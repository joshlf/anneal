/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Trusted
import MiniRustSpec.Interp
import MiniRustSpec.Correspondence.Pointers

/-!
# Episode 1 MiniRust Authority: Cross-Frame References, Pointer Arithmetic, & 4-Way Panic Unwinding (`MiniRustSpec.CrossFrameRefAndPanicMR`)

Operational correspondence between MiniRust `d821c6e3` (`MiniRustSpec.Interp` over both
`BasicMemory<x86_64>` `Mach` and `TreeBorrowsMemory<x86_64>` `MachTB`) and Anneal's
unmodified trusted MIR semantics (`Trusted.Rustc.V2026_06_01.MirSemantics`) for:

1. **Cross-frame `&mut T` / `&T` calls (`RetagKind.fnEntry` / `Validate(_, true)` protectors)
   and callee raw-pointer arithmetic** (`.as_mut_ptr` / `.cast`, in-bounds `BinOp.offset`,
   wrapping pointer offset round-trips, OOB-without-deref wrapping offset vs. OOB in-bounds
   offset UB, post-return caller write after protector release, Tree Borrows foreign-write
   protector UB, `Frozen` `&T` write UB, and callee dead-local use-after-return UB).
2. **`TerminatorKind.assert`, `TerminatorKind.unreachable`, panic initiation, 4-way
   `UnwindAction.{continue_, cleanup, terminate, unreachable}`, `TerminatorKind.{unwindResume,
   unwindTerminate}`, multi-frame LIFO protector release with partial `&mut` writeback
   preservation, and the root-frame `Memory.rootUnwindCeiling` boundary**.

Root isolation: imports strictly `Lean`, `Trusted`, `MiniRustSpec.Interp`, and
`MiniRustSpec.Correspondence.Pointers` (zero `Miri.*`, `LeanMiriSpec.*`, or `Anneal.*`).
-/

namespace MiniRustSpec.CrossFrameRefAndPanicMR

set_option Elab.async false

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.Correspondence

/-! ## §0. Frozen Observation Interface & Kernel Helpers -/

/-- Frozen cross-authority observation domain for Episode 1 scenarios (constructor order
shared identically with `LmCrossFramePanicObs` and `CrossFramePanicObs`). -/
inductive MrCrossFramePanicObs : Type where
  /-- Normal return carrying `(retVal, callerReferentVal)`. -/
  | okVal (retVal : Nat) (referentVal : Nat)
  /-- Normal return recovered via outer catch harness after cleanup-block mutations. -/
  | okCleanupRecovered (retVal : Nat) (referentVal : Nat)
  /-- Unwound / panicked exit with preserved caller referent value. -/
  | unwound (referentVal : Nat)
  /-- Deterministic process abort (`unwindTerminate`, `UnwindAction.terminate`, `IntrinsicOp.Abort`). -/
  | abort
  /-- Undefined behavior fault. -/
  | ub
  /-- MiniRust well-formedness specification panic. -/
  | specPanic
  /-- Fail-closed out-of-range or unsupported case. -/
  | invalidOrUnsupported
  deriving DecidableEq, Repr

/-- Number of canonical cross-frame reference & panic-unwind scenarios (`0..27`, 56 mode cells). -/
def mrCanonicalCaseCount : Nat := 28

/-- Close an equality goal via kernel definitional reduction (`Eq.refl`, zero `Lean.ofReduceBool`). -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq?
    | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-- Inversion of a successful `Interp` bind. -/
theorem interp_bind_ok {α β : Type} {x : Interp α} {f : α → Interp β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Inversion of a successful `pure`. -/
theorem interp_pure_ok {α : Type} {x y : α} (h : (pure x : Interp α) = .ok y) : x = y := by
  cases h; rfl

/-! ## §1. MiniRust AST, Types, & Polymorphic Execution Harness (`Mach` & `MachTB`) -/

@[reducible] def fnId (n : Nat) : FnName := ⟨⟨n⟩⟩
@[reducible] def bbId (n : Nat) : BbName := ⟨⟨n⟩⟩
@[reducible] def locId (n : Nat) : LocalName := ⟨⟨n⟩⟩

@[reducible] def u32IntTy : IntType := ⟨.Unsigned, ⟨4⟩⟩
@[reducible] def isizeIntTy : IntType := ⟨.Signed, ⟨8⟩⟩
@[reducible] def u32Ty : «Type» := .Int u32IntTy
@[reducible] def isizeTy : «Type» := .Int isizeIntTy
@[reducible] def arr2U32Ty : «Type» := .Array u32Ty 2
@[reducible] def rawThinTy : «Type» := .Ptr (.Raw .None)
@[reducible] def fnPtrTy : «Type» := .Ptr .FnPtr

@[reducible] def u32Pointee : PointeeInfo :=
  { layout := .Sized ⟨4⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Sized [],
    freeze := true, unpin := true }

@[reducible] def arr2U32Pointee : PointeeInfo :=
  { layout := .Sized ⟨8⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Sized [],
    freeze := true, unpin := true }

@[reducible] def mutRefU32PtrTy : PtrType := .Ref .Mutable u32Pointee
@[reducible] def shrRefU32PtrTy : PtrType := .Ref .Immutable u32Pointee
@[reducible] def mutRefArr2PtrTy : PtrType := .Ref .Mutable arr2U32Pointee

@[reducible] def mutRefU32Ty : «Type» := .Ptr mutRefU32PtrTy
@[reducible] def shrRefU32Ty : «Type» := .Ptr shrRefU32PtrTy
@[reducible] def mutRefArr2Ty : «Type» := .Ptr mutRefArr2PtrTy

@[reducible] def cU32 (n : Int) : ValueExpr := .Constant (.Int n) u32Ty
@[reducible] def cIsize (n : Int) : ValueExpr := .Constant (.Int n) isizeTy
@[reducible] def cNullRaw : ValueExpr := .Constant (.PointerWithoutProvenance 0) rawThinTy
@[reducible] def cFn (n : Nat) : ValueExpr := .Constant (.FnPointer (fnId n)) fnPtrTy
@[reducible] def unitPlaceExpr : PlaceExpr :=
  .Deref (.Constant (.PointerWithoutProvenance 1) rawThinTy) unitType

@[reducible] def exitTerm : Terminator := .Intrinsic .Exit [] unitPlaceExpr none
@[reducible] def abortTerm : Terminator := .Intrinsic .Abort [] unitPlaceExpr none

@[reducible] def mkFn (locals : List (LocalName × «Type»)) (args : List LocalName)
    (ret : LocalName) (blocks : List (BbName × BasicBlock))
    (start : BbName := bbId 0) : Function :=
  { locals := ⟨locals⟩, args, ret, calling_convention := .Rust,
    blocks := ⟨blocks⟩, start, implicit_writes := true }

@[reducible] def mkProg (fns : List (FnName × Function)) (start : FnName := fnId 0) : Program :=
  { functions := ⟨fns⟩, start, globals := ⟨[]⟩, traits := ⟨[]⟩, vtables := ⟨[]⟩ }

/-- Allocate a zero-sized `.Function` allocation for each function in `fns`, recording its
pointer in `fn_ptrs` polymorphically across `BasicMemory` and `TreeBorrowsMemory`. -/
def allocFnPtrsM {M : Type} [Memory M] [MemoryOps M]
    (cm : ConcurrentMemory M) :
    List (FnName × Function) →
    Interp (List (FnName × ThinPointer (Memory.Provenance M)) × ConcurrentMemory M)
  | [] => pure ([], cm)
  | (name, _) :: rest => do
    let (ptr, cm1) ← ConcurrentMemory.allocate cm .Function ⟨0⟩ ⟨1⟩
    let (ptrs, cm2) ← allocFnPtrsM cm1 rest
    pure ((name, ptr) :: ptrs, cm2)

/-- Boot a single-thread polymorphic `Machine M` (`Mach` or `MachTB`) from a `Program`,
allocating all function pointers and entering `prog.start` at `.BottomOfStack`. -/
def bootProgramM {M : Type} [Memory M] [MemoryOps M]
    (params : Memory.Params M) (prog : Program) : Interp (Machine M) := do
  let cm0 := ConcurrentMemory.new (M := M) params
  let (fnPtrs, cm1) ← allocFnPtrsM cm0 prog.functions.entries
  let startFn ← mapIndex prog.functions prog.start "prog.functions[prog.start]"
  let m0 : Machine M := {
    prog := prog
    mem := cm1
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [], state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨fnPtrs⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩
  }
  let (startFrame, m1) ← createFrameM m0 startFn .BottomOfStack .Rust u32Ty []
  let (_, m2) ← mutateCurStackM m1 (fun _ => pure ((), [startFrame]))
  pure m2

/-- Step a polymorphic `Machine M` up to `fuel` steps, returning either `.error (stop, mBefore)`
at the stopping state or `.ok mFuel` if fuel runs out. -/
def runToStopM {M : Type} [Memory M] [MemoryOps M] :
    Nat → Machine M → Except (Stop × Machine M) (Machine M)
  | 0, m => .ok m
  | fuel + 1, m =>
    match stepM m with
    | .ok m' => runToStopM fuel m'
    | .error s => .error (s, m)

/-- Read a `u32` local from the active root frame of `m` via `evalPlaceM` + `placeLoadM`. -/
def readLocalU32M {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (loc : LocalName) :
    Option Nat :=
  match evalPlaceM m (.Local loc) with
  | .ok ((place, ty), m1) =>
    match placeLoadM m1 place ty with
    | .ok (.Int i, _) => if 0 ≤ i then some i.toNat else none
    | _ => none
  | .error _ => none

/-- Run `prog` polymorphically on `Machine M` (`BM` or `TBM`) and extract `MrCrossFramePanicObs`.
Root programs store `(obsKind, retVal, referentVal)` in locals `(0, 1, 2)` before `Intrinsic.Exit`
(`obsKind = 0 => okVal`, `1 => okCleanupRecovered`, `2 => unwound`). -/
def runProgramObsM {M : Type} [Memory M] [MemoryOps M]
    (params : Memory.Params M) (prog : Program) (fuel : Nat := 120) : MrCrossFramePanicObs :=
  match bootProgramM (M := M) params prog with
  | .error (.ub _) => .ub
  | .error .abort => .abort
  | .error (.specPanic _) => .specPanic
  | .error _ => .invalidOrUnsupported
  | .ok m0 =>
    match runToStopM fuel m0 with
    | .error (.machineStop, mFinal) =>
      match readLocalU32M mFinal (locId 0), readLocalU32M mFinal (locId 1),
            readLocalU32M mFinal (locId 2) with
      | some 0, some retV, some refV => .okVal retV refV
      | some 1, some retV, some refV => .okCleanupRecovered retV refV
      | some 2, _, some refV => .unwound refV
      | _, _, _ => .invalidOrUnsupported
    | .error (.ub _, _) => .ub
    | .error (.abort, _) => .abort
    | .error (.specPanic _, _) => .specPanic
    | .error (_, _) => .invalidOrUnsupported
    | .ok _ => .invalidOrUnsupported

/-! ## §2. Universal Polymorphic MiniRust Laws (`Mach` & `MachTB`) & `MachTB.wfLive` -/

section MiniRustUniversalLaws

/-- `allocFnPtrsM` on `TBM` preserves `TreeBorrowsMemory.wfLive`. -/
theorem allocFnPtrsM_tb_wfLive :
    ∀ (fns : List (FnName × Function)) {cm cm' : ConcurrentMemory TBM}
      {ptrs : List (FnName × ThinPointer TreeBorrowsProvenance)},
      TreeBorrowsMemory.wfLive cm.memory →
      allocFnPtrsM cm fns = .ok (ptrs, cm') →
      TreeBorrowsMemory.wfLive cm'.memory
  | [], _, _, _, hwf, h => by
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | (_, _) :: rest, cm, cm', ptrs, hwf, h => by
    unfold allocFnPtrsM at h
    obtain ⟨⟨_, cm1⟩, hal, h⟩ := interp_bind_ok h
    obtain ⟨⟨_, cm2⟩, hrec, h⟩ := interp_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    have hwf1 : TreeBorrowsMemory.wfLive cm1.memory := by
      unfold ConcurrentMemory.allocate MemoryOps.allocate instMemoryOpsTBM at hal
      obtain ⟨⟨_, tbm1⟩, hta, h1⟩ := interp_bind_ok hal
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h1)
      exact TreeBorrowsMemory.allocate_wfLive hwf hta
    exact allocFnPtrsM_tb_wfLive rest hwf1 hrec

/-- Booting any MiniRust `Program` into `MachTB` via `bootProgramM` satisfies `MachTB.wfLive`. -/
theorem bootProgramM_tb_wfLive (params : TreeBorrowsParams) (prog : Program) (m : MachTB)
    (h : bootProgramM (M := TBM) params prog = .ok m) : MachTB.wfLive m := by
  unfold bootProgramM at h
  obtain ⟨⟨_, cm1⟩, hfn, h⟩ := interp_bind_ok h
  obtain ⟨startFn, _, h⟩ := interp_bind_ok h
  obtain ⟨⟨startFr, m1⟩, hcr, h⟩ := interp_bind_ok h
  obtain ⟨⟨_, m2⟩, hmut, h⟩ := interp_bind_ok h
  obtain rfl := interp_pure_ok h
  have hwf0 : TreeBorrowsMemory.wfLive (ConcurrentMemory.new (M := TBM) params).memory :=
    TreeBorrowsMemory.new_wfLive params
  have hwf1 : TreeBorrowsMemory.wfLive cm1.memory := allocFnPtrsM_tb_wfLive _ hwf0 hfn
  -- `createFrameM` preserves `MachTB.wfLive` (via `storageLiveM_tb_wfLive`, zero args).
  have hwfM1 : MachTB.wfLive m1 := by
    unfold createFrameM at hcr
    obtain ⟨⟨fr1, cm2⟩, hsl, hcr⟩ := interp_bind_ok hcr
    obtain ⟨⟨fr2, cm3⟩, hal, hcr⟩ := interp_bind_ok hcr
    have hwf2 : TreeBorrowsMemory.wfLive cm2.memory := storageLiveM_tb_wfLive hwf1 hsl
    have hAllocArgs : ∀ (args : List LocalName) (fr0 fr' : StackFrame TBM)
        (cm0 cm' : ConcurrentMemory TBM),
        TreeBorrowsMemory.wfLive cm0.memory →
        allocFrameArgsM fr0 cm0 args = .ok (fr', cm') →
        TreeBorrowsMemory.wfLive cm'.memory := by
      intro args
      induction args with
      | nil =>
        intro fr0 fr' cm0 cm' hwf ha
        obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok ha)
        exact hwf
      | cons l rest ih =>
        intro fr0 fr' cm0 cm' hwf ha
        unfold allocFrameArgsM at ha
        obtain ⟨⟨fr1, cm1⟩, hsl1, ha⟩ := interp_bind_ok ha
        exact ih fr1 fr' cm1 cm' (storageLiveM_tb_wfLive hwf hsl1) ha
    have hwf3 : TreeBorrowsMemory.wfLive cm3.memory := hAllocArgs _ _ _ _ _ hwf2 hal
    dsimp only at hcr
    split at hcr
    · cases hcr
    · obtain ⟨_, _, hcr⟩ := interp_bind_ok hcr
      obtain ⟨_, _, hcr⟩ := interp_bind_ok hcr
      split at hcr
      · cases hcr
      · split at hcr
        · cases hcr
        · rename_i hLenEq
          have hNil : startFn.args = [] := by
            cases hA : startFn.args with
            | nil => rfl
            | cons _ _ => simp [hA] at hLenEq
          obtain ⟨m3, hinit, hcr⟩ := interp_bind_ok hcr
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hcr)
          rw [hNil] at hinit
          obtain rfl := interp_pure_ok hinit
          exact hwf3
  -- `mutateCurStackM` does not modify `mem`.
  unfold mutateCurStackM at hmut
  obtain ⟨_, _, hmut⟩ := interp_bind_ok hmut
  obtain ⟨_, hpure, hmut⟩ := interp_bind_ok hmut
  obtain ⟨_, _, hmut⟩ := interp_bind_ok hmut
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hmut)
  exact hwfM1

/-- Running `runToStopM` from any `MachTB.wfLive` state preserves `MachTB.wfLive` at both
stopping states and fuel-exhausted states. -/
theorem runToStopM_tb_wfLive :
    ∀ (fuel : Nat) {m : MachTB}, MachTB.wfLive m →
      match runToStopM fuel m with
      | .ok mEnd => MachTB.wfLive mEnd
      | .error (_, mStop) => MachTB.wfLive mStop
  | 0, _, hwf => hwf
  | fuel + 1, m, hwf => by
    unfold runToStopM
    cases hStep : stepM m with
    | error _ => exact hwf
    | ok m' => exact runToStopM_tb_wfLive fuel (stepTB_wfLive hwf hStep)

/-- **Universal wrapping `BinOp::PtrOffset { inbounds: false }`**: never fails on any thin
pointer and integer offset across EVERY memory model `M` (`Mach` and `MachTB`), preserving
provenance and type while wrapping the address modulo `2^64`. -/
theorem evalPtrOffsetM_wrapping_eq {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (lTy rTy : «Type») (offset : Int) :
    evalPtrOffsetM m false (.Ptr ⟨ptr, none⟩, lTy) (.Int offset, rTy) =
      .ok (.Ptr (ThinPointer.widen (ptrOffsetWrappingM ptr offset) none), lTy) := rfl

/-- **Universal in-bounds `BinOp::PtrOffset { inbounds: true }`**: delegates directly to
`ptrOffsetInboundsM` across EVERY memory model `M`, preserving provenance and type on success
and propagating `Stop.ub` when out of bounds. -/
theorem evalPtrOffsetM_inbounds_eq {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (lTy rTy : «Type») (offset : Int) :
    evalPtrOffsetM m true (.Ptr ⟨ptr, none⟩, lTy) (.Int offset, rTy) =
      (do
        let p' ← ptrOffsetInboundsM m ptr offset
        pure (.Ptr (ThinPointer.widen p' none), lTy)) := rfl

/-- **Universal wrapping pointer offset `+delta` / `-delta` round-trip** across EVERY
provenance type: for any valid 64-bit address (`0 ≤ ptr.addr < 2^64`) and arbitrary integer
offset `delta`, wrapping by `+delta` and then `-delta` restores the EXACT original pointer
(both address and provenance). -/
theorem ptrOffsetWrappingM_roundtrip {Provenance : Type} (ptr : ThinPointer Provenance)
    (delta : Int) (hLo : 0 ≤ ptr.addr) (hHi : ptr.addr < (2 : Int) ^ 64) :
    ptrOffsetWrappingM (ptrOffsetWrappingM ptr delta) (-delta) = ptr := by
  cases ptr with
  | mk addr prov =>
    dsimp only at hLo hHi
    unfold ptrOffsetWrappingM ThinPointer.wrapping_offsetM bringInBounds
    dsimp only [Size.bits, x86_64.PTR_SIZE]
    have hMod : ((addr + delta) % (2 : Int) ^ 64 + -delta) % (2 : Int) ^ 64 = addr := by
      have h1 : ((addr + delta) % (2 : Int) ^ 64 + -delta) % (2 : Int) ^ 64 =
          ((addr + delta) + -delta) % (2 : Int) ^ 64 := by
        rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
      rw [h1, Int.add_neg_cancel_right, Int.emod_eq_of_lt hLo hHi]
    congr 1

/-- **Universal `Terminator::Unreachable` UB** across EVERY memory model `M` (`Mach` & `MachTB`). -/
theorem evalTerminatorM_unreachable_ub {M : Type} [Memory M] [MemoryOps M] (m : Machine M) :
    evalTerminatorM m .Unreachable = .error (.ub "reached unreachable code") := rfl

/-- **Universal `Terminator::Switch` assert-branching law** across EVERY memory model `M`:
branching on `1` (pass) jumps to `passBb`, while branching on `0` (fail) jumps to `failBb`. -/
theorem evalTerminatorM_switch_assert {M : Type} [Memory M] [MemoryOps M] (m m1 : Machine M)
    (condExpr : ValueExpr) (condTy : «Type») (b : Bool) (passBb failBb : BbName)
    (hVal : evalValueM m condExpr = .ok ((.Int (if b then 1 else 0), condTy), m1)) :
    evalTerminatorM m (.Switch condExpr ⟨[(1, passBb)]⟩ failBb) =
      jumpToBlockM m1 (if b then passBb else failBb) := by
  unfold evalTerminatorM
  dsimp only
  rw [hVal]
  cases b <;> rfl

/-- **Universal `Terminator::Intrinsic .Abort` law** across EVERY memory model `M`
(`Mach` & `MachTB`): deterministically terminates with `.error .abort`. -/
theorem evalTerminatorM_abort {M : Type} [Memory M] [MemoryOps M] (m : Machine M) :
    evalTerminatorM m abortTerm = .error .abort := by
  unfold evalTerminatorM abortTerm unitPlaceExpr evalPlaceM evalValueM evalArgsM evalIntrinsicM abort
  rfl

/-- **Universal `Terminator::ResumeUnwind` 3-way dispatch law** across EVERY memory model `M`
(`Mach` & `MachTB`): after local teardown (`deallocAllM`) and protector release
(`ConcurrentMemory.end_call`), `.BackToCaller _ (some ubBb) _` jumps to `ubBb`,
`.BackToCaller _ none _` faults with UB (`.unreachable` unwind edge), and `.BottomOfStack`
faults with UB (`"the function at the bottom of the stack must not unwind"`). -/
theorem evalResumeUnwindM_dispatch {M : Type} [Memory M] [MemoryOps M]
    (m : Machine M) (t : Thread M) (fr fr1 : StackFrame M)
    (threads' : List (Thread M)) (cm1 cm2 : ConcurrentMemory M)
    (hTid : activeThreadM m = .ok t) (hLast : t.stack.getLast? = some fr)
    (hSet : listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop" = .ok threads')
    (hDealloc : deallocAllM fr.locals.entries.length fr m.mem = .ok (fr1, cm1))
    (hEnd : ConcurrentMemory.end_call cm1 fr1.extra = .ok cm2) :
    (∀ nb ubBb rp, fr1.stack_pop_action = .BackToCaller nb (some ubBb) rp →
      evalResumeUnwindM m = jumpToBlockM { { m with threads := threads' } with mem := cm2 } ubBb) ∧
    (∀ nb rp, fr1.stack_pop_action = .BackToCaller nb none rp →
      evalResumeUnwindM m =
        .error (.ub "unwinding from a function where the caller did not specify an unwind_block")) ∧
    (fr1.stack_pop_action = .BottomOfStack →
      evalResumeUnwindM m =
        .error (.ub "the function at the bottom of the stack must not unwind")) := by
  refine ⟨?_, ?_, ?_⟩
  · intro nb ubBb rp hAct
    unfold evalResumeUnwindM
    simp only [hTid, hLast, hSet, hDealloc, hEnd, hAct, pure, Except.pure, bind, Except.bind]
  · intro nb rp hAct
    unfold evalResumeUnwindM
    simp only [hTid, hLast, hSet, hDealloc, hEnd, hAct, pure, Except.pure, bind, Except.bind, ub]
  · intro hAct
    unfold evalResumeUnwindM
    simp only [hTid, hLast, hSet, hDealloc, hEnd, hAct, pure, Except.pure, bind, Except.bind, ub]

/-- **Universal Tree Borrows `FnEntry` strong-protector foreign-write UB & post-release
permission law** on `MiniRustSpec.Interp.Node`:
1. A foreign write to a strongly protected `Unique` / `Frozen true` / `Reserved true _` child
   node faults with UB (`Tree Borrows: foreign write of protected ...`).
2. Once `end_call` / protector release changes `Protected.Strong` to `Protected.No` and
   unprotects the permission, a foreign write through the parent succeeds cleanly (disabling
   the child without UB).
3. A local write through a `Frozen` node faults with `"Tree Borrows: local write of Frozen reference"`. -/
theorem tbm_node_protector_and_frozen_laws :
    (Node.access ⟨[⟨[], [.Prot (.Reserved true false)], .Strong⟩], [.Unprot .Unique], .No⟩
        (some []) .Write ⟨0⟩ ⟨1⟩ =
      .error (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read") ∧
      Node.access ⟨[⟨[], [.Unprot .Reserved], .No⟩], [.Unprot .Unique], .No⟩
        (some []) .Write ⟨0⟩ ⟨1⟩ =
      .ok ⟨[⟨[], [.Unprot .Disabled], .No⟩], [.Unprot .Unique], .No⟩) ∧
    (Node.access ⟨[⟨[], [.Prot .Unique], .Strong⟩], [.Unprot .Unique], .No⟩
        (some []) .Write ⟨0⟩ ⟨1⟩ =
      .error (.ub "Tree Borrows: foreign read of protected Unique reference") ∧
      Node.access ⟨[⟨[], [.Unprot .Unique], .No⟩], [.Unprot .Unique], .No⟩
        (some []) .Write ⟨0⟩ ⟨1⟩ =
      .ok ⟨[⟨[], [.Unprot .Disabled], .No⟩], [.Unprot .Unique], .No⟩) ∧
    (Node.access ⟨[⟨[], [.Prot (.Frozen true)], .Strong⟩], [.Unprot .Unique], .No⟩
        (some [0]) .Write ⟨0⟩ ⟨1⟩ =
      .error (.ub "Tree Borrows: local write to protected Frozen reference")) := by
  refine ⟨⟨by kernel_rfl, by kernel_rfl⟩, ⟨by kernel_rfl, by kernel_rfl⟩, by kernel_rfl⟩

end MiniRustUniversalLaws

/-! ## §3. Universal Operational Laws over Unmodified `Trusted.Rustc.V2026_06_01.MirSemantics` -/

section TrustedUniversalLaws

open Trusted.Rustc.V2026_06_01.Layout (LayoutTable)
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Sequence

abbrev TrustedMem := Trusted.Rustc.V2026_06_01.MirSemantics.Memory

private theorem nat_ble_false {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hb : Nat.ble a b with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true hb) (by omega)

private theorem nat_ble_true {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := by
  cases hb : Nat.ble a b with
  | true => rfl
  | false => exact absurd (Nat.ble_eq.mpr h) (by simp [hb])

private theorem nat_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem wrapScalarBits_eq_mod (val m : Nat) :
    wrapScalarBits val m = val % m := by
  unfold wrapScalarBits
  cases hb : Nat.ble m val with
  | true => rfl
  | false =>
    rcases Nat.lt_or_ge val m with hlt | hle
    · exact (Nat.mod_eq_of_lt hlt).symm
    · have htr : Nat.ble m val = true := nat_ble_true hle
      rw [htr] at hb; cases hb

/-- **Trusted `TerminatorKind.unreachable` UB**: matches MiniRust `evalTerminatorM_unreachable_ub`. -/
theorem trusted_evalTerminator_unreachable_ub (s : MachineState) (span : String)
    (cb : Option CapturedMir) :
    evalTerminator s { kind := .unreachable, span := span } cb =
      MirStepNode.fail .ub := rfl

/-- **Trusted `TerminatorKind.unwindTerminate` abort**: matches MiniRust `evalTerminatorM_abort`. -/
theorem trusted_evalTerminator_unwindTerminate_abort (s : MachineState) (span : String)
    (cb : Option CapturedMir) :
    evalTerminator s { kind := .unwindTerminate, span := span } cb =
      MirStepNode.retOutcome .abort := rfl

/-- **Trusted `TerminatorKind.assert` pass law**: when `cond` evaluates to `expectedBit`,
`evalTerminator` jumps cleanly to `(target, 0)` preserving `s.memory`. -/
theorem trusted_evalTerminator_assert_pass (s : MachineState) (cond : Operand) (expected : Bool)
    (target : BasicBlockIdx) (unwind : UnwindAction) (span : String) (cb : Option CapturedMir)
    (sc : ScalarInt) (locals' : List LocalSlot)
    (hCond : evalOperandWithBodyCast s.frame.locals cond s.memory.borrows s.memory.globals
      (match cb with | .some b => b.layouts | .none => emptyLayoutTable)
      s.memory.callerLocals (bodyLocalDeclsOf cb) s.memory.callStack = .ok (.scalar sc) locals')
    (hMatch : sc.bits = (if expected then 1 else 0)) :
    evalTerminator s
        { kind := .assert cond expected target unwind, span := span } cb =
      MirStepNode.step { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } } := by
  cases cb <;> cases expected <;>
    (unfold Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator
     dsimp only at hCond hMatch ⊢
     rw [hCond]
     dsimp only
     simp [hMatch])

/-- **Trusted `TerminatorKind.assert` fail law**: when `cond` evaluates to `sc.bits ≠ expectedBit`,
`evalTerminator` dispatches `applyUnwindAction s locals' s.memory unwind`. -/
theorem trusted_evalTerminator_assert_fail (s : MachineState) (cond : Operand) (expected : Bool)
    (target : BasicBlockIdx) (unwind : UnwindAction) (span : String) (cb : Option CapturedMir)
    (sc : ScalarInt) (locals' : List LocalSlot)
    (hCond : evalOperandWithBodyCast s.frame.locals cond s.memory.borrows s.memory.globals
      (match cb with | .some b => b.layouts | .none => emptyLayoutTable)
      s.memory.callerLocals (bodyLocalDeclsOf cb) s.memory.callStack = .ok (.scalar sc) locals')
    (hMismatch : sc.bits ≠ (if expected then 1 else 0)) :
    evalTerminator s
        { kind := .assert cond expected target unwind, span := span } cb =
      match applyUnwindAction s locals' s.memory unwind with
      | .running nextState => MirStepNode.step nextState
      | .halted out => MirStepNode.retOutcome out
      | .faulted fk => MirStepNode.fail fk := by
  cases cb <;> cases expected <;>
    (unfold Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator
     dsimp only at hCond hMismatch ⊢
     rw [hCond]
     dsimp only
     rw [nat_beq_false (by simpa using hMismatch)]
     rfl)

/-- **Trusted 4-way `applyUnwindAction` exact characterization**: covers `.cleanup`, `.continue_`,
`.terminate`, and `.unreachable`. -/
theorem trusted_applyUnwindAction_four_way (s : MachineState) (localsAfter : List LocalSlot)
    (memAfter : TrustedMem) (cleanupBb : BasicBlockIdx) :
    applyUnwindAction s localsAfter memAfter (.cleanup cleanupBb) =
      .running { frame := { s.frame with blockIdx := cleanupBb, stmtIdx := 0, locals := localsAfter },
                 memory := memAfter } ∧
    applyUnwindAction s localsAfter memAfter .continue_ =
      unwindFromCallStack memAfter.callStack memAfter ∧
    applyUnwindAction s localsAfter memAfter .terminate = .halted .abort ∧
    applyUnwindAction s localsAfter memAfter .unreachable = .faulted .ub :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Closed-form memory after popping `conts` `.continue_` frames in LIFO order. -/
def unwindContinuePopMem :
    List SavedCallerFrame → List SavedCallerFrame → TrustedMem → TrustedMem
  | [], _, mem => mem
  | caller :: rest, tail, mem =>
    unwindContinuePopMem rest tail
      { mem with
        callStack := rest ++ tail
        activeCallee := .some caller.callerBody
        activeProtectors := restoreCallerProtectors caller }

theorem unwindContinuePopMem_rootUnwindCeiling :
    ∀ (conts tail : List SavedCallerFrame) (mem : TrustedMem),
      (unwindContinuePopMem conts tail mem).rootUnwindCeiling = mem.rootUnwindCeiling
  | [], _, _ => rfl
  | _ :: rest, tail, mem => by
    unfold unwindContinuePopMem
    exact unwindContinuePopMem_rootUnwindCeiling rest tail _

/-- **Trusted multi-frame `.continue_` LIFO unwind chain**: pops every `.continue_` frame
restoring each caller's protectors in LIFO order before dispatching `tail`. -/
theorem trusted_unwindFromCallStack_continue_chain :
    ∀ (conts tail : List SavedCallerFrame) (mem : TrustedMem),
      (∀ c ∈ conts, c.returnUnwind = .continue_) →
      unwindFromCallStack (conts ++ tail) mem =
        unwindFromCallStack tail (unwindContinuePopMem conts tail mem)
  | [], _, _, _ => rfl
  | c :: cs, tail, mem, hCont => by
    have hc : c.returnUnwind = .continue_ := hCont c (List.mem_cons_self ..)
    have hcs : ∀ x ∈ cs, x.returnUnwind = .continue_ :=
      fun x hx => hCont x (List.mem_cons_of_mem c hx)
    simp only [List.cons_append, unwindFromCallStack, hc, unwindContinuePopMem]
    exact trusted_unwindFromCallStack_continue_chain cs tail _ hcs

/-- **Exact root-frame unwind boundary characterization (`Memory.rootUnwindCeiling`)**:
- `rootUnwindCeiling = true` -> Trusted halts with `.halted .panic` (diverges from MiniRust's
  `BottomOfStack` UB unless wrapped in an outer catch harness).
- `rootUnwindCeiling = false` -> Trusted faults with `.faulted .ub` (agrees identically with
  MiniRust's `BottomOfStack` UB). -/
theorem trusted_unwindFromCallStack_root_ceiling_iff (mem : TrustedMem) :
    (mem.rootUnwindCeiling = true → unwindFromCallStack [] mem = .halted .panic) ∧
    (mem.rootUnwindCeiling = false → unwindFromCallStack [] mem = .faulted .ub) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold unwindFromCallStack; rw [h]
  · unfold unwindFromCallStack; rw [h]

/-- **Trusted `evalBinOpOffset` out-of-bounds UB**:
1. Positive non-zero offset pushing `ptrVal.offsetBytes + n * stride > bound` returns `.none` (UB).
2. Negative offset (`-1`) from `offsetBytes = 0` with `0 < stride < 2^63` returns `.none` (UB). -/
theorem trusted_evalBinOpOffset_oob_none (p : ProvenancePtr) (stride bound : Nat) :
    (∀ (n : Nat), n < 2 ^ 63 → stride < 2 ^ 63 →
      0 < n * stride → n * stride < 2 ^ 63 → bound < 2 ^ 63 →
      bound < p.offsetBytes + n * stride →
      evalBinOpOffset p 8 ⟨n, 8⟩ stride (some bound) 8 = .none) ∧
    (p.offsetBytes = 0 → 0 < stride → stride < 2 ^ 63 →
      evalBinOpOffset p 8 ⟨2 ^ 64 - 1, 8⟩ stride (some bound) 8 = .none) := by
  have hMod : scalarModulus 8 = 2 ^ 64 := rfl
  have hHalf : signedHalfModulus 8 = 2 ^ 63 := rfl
  refine ⟨?_, ?_⟩
  · intro n hn _ hMulPos hMul hBnd hGt
    have hWrap : wrapScalarBits n (scalarModulus 8) = n := by
      rw [wrapScalarBits_eq_mod, hMod, Nat.mod_eq_of_lt (by omega)]
    have hNeg : isSignedNegative n 8 = false := by
      unfold isSignedNegative
      dsimp only
      rw [hMod, wrapScalarBits_eq_mod, Nat.mod_eq_of_lt (by omega)]
      exact nat_ble_false (by omega)
    have hDeltaLt : Nat.ble (signedHalfModulus 8) (Nat.mul n stride) = false := by
      rw [hHalf]; exact nat_ble_false (by change n * stride < 2 ^ 63; omega)
    unfold evalBinOpOffset
    simp only [Nat.beq_refl, Bool.and_self, hWrap, hNeg, hDeltaLt]
    cases hCand : Nat.ble (signedHalfModulus 8) (Nat.add p.offsetBytes (Nat.mul n stride)) with
    | true => rfl
    | false =>
      have hGtBle : (p.offsetBytes.add (n.mul stride)).ble bound = false :=
        nat_ble_false (by change bound < p.offsetBytes + n * stride; omega)
      have hNe : (p.offsetBytes.add (n.mul stride)).beq p.offsetBytes = false :=
        nat_beq_false (by change p.offsetBytes + n * stride ≠ p.offsetBytes; omega)
      dsimp only
      rw [hNe, hGtBle]
      simp
  · intro hOff hPos _
    have hWrap : wrapScalarBits (2 ^ 64 - 1) (scalarModulus 8) = 2 ^ 64 - 1 := by decide
    have hNeg : isSignedNegative (2 ^ 64 - 1) 8 = true := by decide
    have hSub : Nat.sub (scalarModulus 8) (2 ^ 64 - 1) = 1 := by decide
    have hMul : Nat.mul 1 stride = stride := Nat.one_mul stride
    have hBle0 : Nat.ble stride 0 = false := nat_ble_false hPos
    unfold evalBinOpOffset
    simp only [Nat.beq_refl, Bool.and_self, hWrap, hNeg, hSub, hMul, hOff, hBle0, Bool.and_false]

/-- **Trusted `evalArithOffset` wrapping `+k` / `-k` round-trip** (matching MiniRust
`ptrOffsetWrappingM_roundtrip`): for any pointer with `offsetBytes < 2^64` and `0 < k < 2^63`,
wrapping forward by `+k` and backward by `-k` recovers the exact original `ProvenancePtr`. -/
theorem trusted_evalArithOffset_roundtrip (p : ProvenancePtr) (k stride : Nat)
    (hOff : p.offsetBytes < 2 ^ 64) (hk : 0 < k) (hkLo : k < 2 ^ 63) :
    ∃ p1, evalArithOffset p 8 ⟨k, 8⟩ stride = .some p1 ∧
      evalArithOffset p1 8 ⟨2 ^ 64 - k, 8⟩ stride = .some p := by
  have hMod : scalarModulus 8 = 2 ^ 64 := rfl
  have hWrapPos : wrapScalarBits k (scalarModulus 8) = k := by
    rw [wrapScalarBits_eq_mod, hMod, Nat.mod_eq_of_lt (by omega)]
  have hNotNeg : isSignedNegative k 8 = false := by
    unfold isSignedNegative; dsimp only
    rw [hMod, wrapScalarBits_eq_mod, Nat.mod_eq_of_lt (by omega)]
    exact nat_ble_false (by omega)
  have hWrapNeg : wrapScalarBits (2 ^ 64 - k) (scalarModulus 8) = 2 ^ 64 - k := by
    rw [wrapScalarBits_eq_mod, hMod, Nat.mod_eq_of_lt (by omega)]
  have hIsNeg : isSignedNegative (2 ^ 64 - k) 8 = true := by
    unfold isSignedNegative; dsimp only
    rw [hMod, wrapScalarBits_eq_mod, Nat.mod_eq_of_lt (by omega)]
    exact nat_ble_true (by change 2 ^ 63 ≤ 2 ^ 64 - k; omega)
  have hMag : Nat.sub (scalarModulus 8) (2 ^ 64 - k) = k := by
    rw [hMod]; change 2 ^ 64 - (2 ^ 64 - k) = k; omega
  refine ⟨{ p with offsetBytes := (p.offsetBytes + k * stride) % 2 ^ 64 }, ?_, ?_⟩
  · unfold evalArithOffset
    dsimp only
    simp only [Nat.beq_refl, Bool.and_self, hWrapPos, hNotNeg]
    rw [wrapScalarBits_eq_mod, hMod]
    rfl
  · unfold evalArithOffset
    dsimp only
    simp only [Nat.beq_refl, Bool.and_self, hWrapNeg, hIsNeg, hMag]
    rw [wrapScalarBits_eq_mod, wrapScalarBits_eq_mod, hMod]
    apply congrArg Option.some
    cases p with
    | mk aid off =>
      dsimp only at hOff ⊢
      congr 1
      change ((off + k * stride) % 2 ^ 64 + (2 ^ 64 - k * stride % 2 ^ 64)) % 2 ^ 64 = off
      have hDlt : k * stride % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
      have hEq : (off + k * stride) % 2 ^ 64 = (off + k * stride % 2 ^ 64) % 2 ^ 64 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hOff]
      rw [hEq]
      by_cases hSum : off + k * stride % 2 ^ 64 < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hSum]
        have : off + k * stride % 2 ^ 64 + (2 ^ 64 - k * stride % 2 ^ 64) = off + 2 ^ 64 := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hOff]
      · have hSum2 : off + k * stride % 2 ^ 64 - 2 ^ 64 < 2 ^ 64 := by omega
        have hMod2 : (off + k * stride % 2 ^ 64) % 2 ^ 64 = off + k * stride % 2 ^ 64 - 2 ^ 64 := by
          have hSplit : off + k * stride % 2 ^ 64 = (off + k * stride % 2 ^ 64 - 2 ^ 64) + 2 ^ 64 := by omega
          conv => lhs; rw [hSplit]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hSum2]
        rw [hMod2]
        have : off + k * stride % 2 ^ 64 - 2 ^ 64 + (2 ^ 64 - k * stride % 2 ^ 64) = off := by omega
        rw [this, Nat.mod_eq_of_lt hOff]

/-- **Trusted `evalFnEntryRetag` activation & `restoreCallerProtectors` release law**:
`restoreCallerProtectors` restores exactly the caller's saved protectors (`callerProtector`
consed onto `calleeProtectors`), releasing any fresh callee protector `pid` absent from the
caller's saved protector list. -/
theorem trusted_restoreCallerProtectors_releases (caller : SavedCallerFrame) (e : BorrowEntry)
    (pid : Nat) (hProt : e.protector = some pid)
    (hAbsent : pid ∉ restoreCallerProtectors caller) :
    isBorrowProtected (restoreCallerProtectors caller) e = false := by
  unfold isBorrowProtected
  rw [hProt]
  have aux : ∀ (xs : List Nat), pid ∉ xs → natListContainsBool xs pid = false := by
    intro xs hNot
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      unfold natListContainsBool
      have hNe : x ≠ pid := fun h => hNot (h ▸ List.mem_cons_self ..)
      have hBeq : Nat.beq x pid = false := nat_beq_false hNe
      rw [hBeq]
      exact ih (fun hm => hNot (List.mem_cons_of_mem x hm))
  exact aux (restoreCallerProtectors caller) hAbsent

end TrustedUniversalLaws

/-! ## §4. Canonical 28-Scenario MiniRust Program Suite (`0..27`) on `Mach` & `MachTB` -/

section CanonicalMrPrograms

/-! ### Helper builders for clean, compact MiniRust functions -/

/-- Standard start-frame prologue writing `(obsKind, retVal, refVal)` to locals `(0, 1, 2)`
and terminating with `IntrinsicOp.Exit`. -/
def finishStmts (kindVal : Int) (retExpr refExpr : ValueExpr) : List Statement :=
  [.StorageLive (locId 1),
   .StorageLive (locId 2),
   .Assign (.Local (locId 0)) (cU32 kindVal),
   .Assign (.Local (locId 1)) retExpr,
   .Assign (.Local (locId 2)) refExpr]

/-- Encode two `u32` elements `(e0, e1)` as `e0 * 1000 + e1` in MiniRust arithmetic. -/
def packPairExpr (e0 e1 : ValueExpr) : ValueExpr :=
  .BinOp (.Int .Add) (.BinOp (.Int .Mul) e0 (cU32 1000)) e1

/-- Transmute any thin reference/pointer value expression to a thin raw pointer (`*mut T` / `*const T`). -/
def asRawPtr (e : ValueExpr) : ValueExpr :=
  .UnOp (.Cast (.Transmute rawThinTy)) e

/-- Pointer offset expression (`inbounds = true` for `BinOp.offset`, `false` for `wrapping_offset`). -/
def ptrOff (inbounds : Bool) (p : ValueExpr) (byteDelta : Int) : ValueExpr :=
  .BinOp (.PtrOffset inbounds) p (cIsize byteDelta)

/-- **Case 0 (`ref_mut_u32_call_writeback`)**:
Caller passes `&mut x` (`x = 10`) to callee; callee activates `FnEntry` protector
(`Validate(_, true)`), writes `*r = 42`, returns `42`; caller reads updated `x = 42`. -/
def mrProg0 : Program :=
  let callee := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 42),
      .Assign (.Local (locId 0)) (cU32 42)
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 10)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 1 (`ref_shared_u32_call_read`)**:
Caller passes `&x` (`x = 77`) to callee; callee activates `FnEntry` shared protector,
reads `*r = 77`, returns `77`; caller observes `x = 77`. -/
def mrProg1 : Program :=
  let callee := mkFn [(locId 0, u32Ty), (locId 1, shrRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Local (locId 0)) (.Load (.Deref (.Load (.Local (locId 1))) u32Ty))
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 77)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) shrRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 2 (`ref_mut_post_return_caller_write`)**:
Callee activates `FnEntry` protector on `&mut x`, writes `25`, returns (releasing protector);
caller then performs a direct/parent write `x = 99` and returns `(99, 99)`. -/
def mrProg2 : Program :=
  let callee := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 25),
      .Assign (.Local (locId 0)) (cU32 25)
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 10)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨[
      .Assign (.Local (locId 3)) (cU32 99)
    ] ++ finishStmts 0 (.Load (.Local (locId 3))) (.Load (.Local (locId 3))),
      exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 3 (`ref_mut_array_cast_offset_inbounds`)**:
Caller passes `&mut [u32; 2] = [10, 20]` to callee; callee activates `FnEntry` protector,
casts to `*mut u32`, computes in-bounds `PtrOffset(+4)`, writes `88` to element `1`, returns `88`;
caller observes `(88, 10088)`. -/
def mrProg3 : Program :=
  let callee := mkFn
    [(locId 0, u32Ty), (locId 1, mutRefArr2Ty), (locId 2, rawThinTy)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2),
      .Assign (.Local (locId 2)) (ptrOff true (asRawPtr (.Load (.Local (locId 1)))) 4),
      .Assign (.Deref (.Load (.Local (locId 2))) u32Ty) (cU32 88),
      .Assign (.Local (locId 0)) (cU32 88)
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, arr2U32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (.Tuple [cU32 10, cU32 20] arr2U32Ty)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefArr2PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4)))
       (packPairExpr (.Load (.Index (.Local (locId 3)) (cIsize 0)))
                     (.Load (.Index (.Local (locId 3)) (cIsize 1)))),
       exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 4 (`ref_mut_array_offset_pos_neg_roundtrip`)**:
Callee receives `&mut [u32; 2] = [11, 22]`, casts to `*mut u32`, computes `p1 = p.offset(+4)`,
writes `33`, computes `p0 = p1.offset(-4)`, writes `44`, returns `44`; caller observes `(44, 44033)`. -/
def mrProg4 : Program :=
  let callee := mkFn
    [(locId 0, u32Ty), (locId 1, mutRefArr2Ty), (locId 2, rawThinTy), (locId 3, rawThinTy)]
    [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2),
      .StorageLive (locId 3),
      .Assign (.Local (locId 2)) (ptrOff true (asRawPtr (.Load (.Local (locId 1)))) 4),
      .Assign (.Deref (.Load (.Local (locId 2))) u32Ty) (cU32 33),
      .Assign (.Local (locId 3)) (ptrOff true (.Load (.Local (locId 2))) (-4)),
      .Assign (.Deref (.Load (.Local (locId 3))) u32Ty) (cU32 44),
      .Assign (.Local (locId 0)) (cU32 44)
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, arr2U32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (.Tuple [cU32 11, cU32 22] arr2U32Ty)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefArr2PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4)))
       (packPairExpr (.Load (.Index (.Local (locId 3)) (cIsize 0)))
                     (.Load (.Index (.Local (locId 3)) (cIsize 1)))),
       exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 5 (`ref_mut_wrapping_offset_roundtrip`)**:
Callee receives `&mut [u32; 2] = [5, 6]`, uses wrapping `PtrOffset(false)` `+4` (write `55`)
then `-4` (write `66`), returns `66`; caller observes `(66, 66055)`. -/
def mrProg5 : Program :=
  let callee := mkFn
    [(locId 0, u32Ty), (locId 1, mutRefArr2Ty), (locId 2, rawThinTy), (locId 3, rawThinTy)]
    [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2),
      .StorageLive (locId 3),
      .Assign (.Local (locId 2)) (ptrOff false (asRawPtr (.Load (.Local (locId 1)))) 4),
      .Assign (.Deref (.Load (.Local (locId 2))) u32Ty) (cU32 55),
      .Assign (.Local (locId 3)) (ptrOff false (.Load (.Local (locId 2))) (-4)),
      .Assign (.Deref (.Load (.Local (locId 3))) u32Ty) (cU32 66),
      .Assign (.Local (locId 0)) (cU32 66)
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, arr2U32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (.Tuple [cU32 5, cU32 6] arr2U32Ty)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefArr2PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4)))
       (packPairExpr (.Load (.Index (.Local (locId 3)) (cIsize 0)))
                     (.Load (.Index (.Local (locId 3)) (cIsize 1)))),
       exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 6 (`ref_mut_wrapping_offset_oob_no_deref_ok`)**:
Callee receives `&mut u32` (`x = 12`), computes wrapping offset `+400` (OOB, NO deref!),
then wraps back `-400`, writes `34`, returns `34`; caller observes `(34, 34)`. -/
def mrProg6 : Program :=
  let callee := mkFn
    [(locId 0, u32Ty), (locId 1, mutRefU32Ty), (locId 2, rawThinTy), (locId 3, rawThinTy)]
    [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2),
      .StorageLive (locId 3),
      .Assign (.Local (locId 2)) (ptrOff false (asRawPtr (.Load (.Local (locId 1)))) 400),
      .Assign (.Local (locId 3)) (ptrOff false (.Load (.Local (locId 2))) (-400)),
      .Assign (.Deref (.Load (.Local (locId 3))) u32Ty) (cU32 34),
      .Assign (.Local (locId 0)) (cU32 34)
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 12)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 7 (`ref_mut_two_level_nested_reborrow_call`)**:
Outer passes `&mut x` (`x = 1`) to mid (`FnEntry` `p1`), mid reborrows `&mut *r` to inner
(`FnEntry` `p2`); inner writes `7` and returns (releasing `p2`); mid writes `10` through `p1`
and returns (releasing `p1`); outer writes `20` and returns `(20, 20)`. -/
def mrProg7 : Program :=
  let inner := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 7),
      .Assign (.Local (locId 0)) (cU32 7)
    ], .Return, .Regular⟩)]
  let mid := mkFn
    [(locId 0, u32Ty), (locId 1, mutRefU32Ty), (locId 2, u32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2)
    ], .Call (cFn 2) .Rust
         [.ByValue (.AddrOf (.Deref (.Load (.Local (locId 1))) u32Ty) mutRefU32PtrTy)]
         (.Local (locId 2)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨[
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty)
        (.BinOp (.Int .Add) (.Load (.Local (locId 2))) (cU32 3)),
      .Assign (.Local (locId 0)) (.Load (.Deref (.Load (.Local (locId 1))) u32Ty))
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 1)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨[
      .Assign (.Local (locId 3)) (.BinOp (.Int .Add) (.Load (.Local (locId 4))) (cU32 10))
    ] ++ finishStmts 0 (.Load (.Local (locId 3))) (.Load (.Local (locId 3))),
      exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, mid), (fnId 2, inner)]

/-- **Case 8 (`ub_foreign_write_under_active_fnEntry_protector`) [MODE-SENSITIVE #1]**:
Caller passes `(parentRawPtr, &mut x)` to callee; callee activates `FnEntry` strong protector
on `&mut x`, then writes `77` through `parentRawPtr` (conflicting foreign write!).
`BasicMemory` succeeds with `.okVal 77 77`; `TreeBorrowsMemory` rejects with `.ub`. -/
def mrProg8 : Program :=
  let callee := mkFn
    [(locId 0, u32Ty), (locId 1, mutRefU32Ty), (locId 2, rawThinTy)]
    [locId 1, locId 2] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 2))) u32Ty) (cU32 77),
      .Assign (.Local (locId 0)) (cU32 77)
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty),
     (locId 4, rawThinTy), (locId 5, u32Ty)] [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .StorageLive (locId 5),
      .Assign (.Local (locId 3)) (cU32 10),
      .Assign (.Local (locId 4)) (.AddrOf (.Local (locId 3)) (.Raw .None))
    ], .Call (cFn 1) .Rust
         [.ByValue (.AddrOf (.Deref (.Load (.Local (locId 4))) u32Ty) mutRefU32PtrTy),
          .ByValue (.Load (.Local (locId 4)))]
         (.Local (locId 5)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 5))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 9 (`ub_write_through_frozen_shared_ref_ptr`) [MODE-SENSITIVE #2]**:
Caller passes `&x` (`x = 10`) to callee; callee activates `FnEntry` shared protector (`Frozen`),
casts `&x` to `*mut u32`, and writes `99` through that `Frozen` tag!
`BasicMemory` succeeds with `.okVal 99 99`; `TreeBorrowsMemory` rejects with `.ub`. -/
def mrProg9 : Program :=
  let callee := mkFn
    [(locId 0, u32Ty), (locId 1, shrRefU32Ty), (locId 2, rawThinTy)]
    [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2),
      .Assign (.Local (locId 2)) (asRawPtr (.Load (.Local (locId 1)))),
      .Assign (.Deref (.Load (.Local (locId 2))) u32Ty) (cU32 99),
      .Assign (.Local (locId 0)) (cU32 99)
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 10)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) shrRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 10 (`ub_callee_returns_dangling_local_ptr_uar`)**:
Callee returns `&raw const y` to its own stack local `y = 55`; `evalReturnM` deallocates `y`;
caller dereferences the returned dangling pointer -> UAR `.ub` in BOTH modes. -/
def mrProg10 : Program :=
  let callee := mkFn [(locId 0, rawThinTy), (locId 1, u32Ty)] [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 1),
      .Assign (.Local (locId 1)) (cU32 55),
      .Assign (.Local (locId 0)) (.AddrOf (.Local (locId 1)) (.Raw .None))
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, rawThinTy), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4)
    ], .Call (cFn 1) .Rust [] (.Local (locId 3)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨[
      .Assign (.Local (locId 4)) (.Load (.Deref (.Load (.Local (locId 3))) u32Ty))
    ] ++ finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 4))),
      exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 11 (`ub_inbounds_offset_past_end`)**:
Callee receives `&mut [u32; 2]` (8 bytes), casts to `*mut u32`, executes in-bounds `PtrOffset(+12)`
(past end, without dereferencing) -> `.ub` in BOTH modes. -/
def mrProg11 : Program :=
  let callee := mkFn
    [(locId 0, u32Ty), (locId 1, mutRefArr2Ty), (locId 2, rawThinTy)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2),
      .Assign (.Local (locId 2)) (ptrOff true (asRawPtr (.Load (.Local (locId 1)))) 12),
      .Assign (.Local (locId 0)) (cU32 0)
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, arr2U32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (.Tuple [cU32 10, cU32 20] arr2U32Ty)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefArr2PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (cU32 0), exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 12 (`ub_inbounds_offset_before_start`)**:
Callee receives `&mut [u32; 2]`, casts to `*mut u32`, executes in-bounds `PtrOffset(-4)`
(before start of allocation) -> `.ub` in BOTH modes. -/
def mrProg12 : Program :=
  let callee := mkFn
    [(locId 0, u32Ty), (locId 1, mutRefArr2Ty), (locId 2, rawThinTy)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2),
      .Assign (.Local (locId 2)) (ptrOff true (asRawPtr (.Load (.Local (locId 1)))) (-4)),
      .Assign (.Local (locId 0)) (cU32 0)
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, arr2U32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (.Tuple [cU32 10, cU32 20] arr2U32Ty)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefArr2PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (cU32 0), exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 13 (`ub_wrapping_offset_oob_then_deref`)**:
Callee computes valid wrapping offset `+400` and then dereferences it -> `.ub` in BOTH modes. -/
def mrProg13 : Program :=
  let callee := mkFn
    [(locId 0, u32Ty), (locId 1, mutRefU32Ty), (locId 2, rawThinTy)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2),
      .Assign (.Local (locId 2)) (ptrOff false (asRawPtr (.Load (.Local (locId 1)))) 400),
      .Assign (.Local (locId 0)) (.Load (.Deref (.Load (.Local (locId 2))) u32Ty))
    ], .Return, .Regular⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 12)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 14 (`assert_pass_expected_true`)**: `assert(1 == 1)` passes -> `.okVal 101 101`. -/
def mrProg14 : Program :=
  let main := mkFn [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty)] [] (locId 0)
    [(bbId 0, ⟨[], .Switch (cU32 1) ⟨[(1, bbId 1)]⟩ (bbId 2), .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (cU32 101) (cU32 101), exitTerm, .Regular⟩),
     (bbId 2, ⟨[], abortTerm, .Terminate⟩)]
  mkProg [(fnId 0, main)]

/-- **Case 15 (`assert_pass_expected_false`)**: `assert(0 == 0)` passes -> `.okVal 102 102`. -/
def mrProg15 : Program :=
  let main := mkFn [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty)] [] (locId 0)
    [(bbId 0, ⟨[], .Switch (cU32 0) ⟨[(0, bbId 1)]⟩ (bbId 2), .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (cU32 102) (cU32 102), exitTerm, .Regular⟩),
     (bbId 2, ⟨[], abortTerm, .Terminate⟩)]
  mkProg [(fnId 0, main)]

/-- **Case 16 (`unreachable_immediate_ub`)**: `Terminator.Unreachable` -> `.ub`. -/
def mrProg16 : Program :=
  let main := mkFn [(locId 0, u32Ty)] [] (locId 0)
    [(bbId 0, ⟨[], .Unreachable, .Regular⟩)]
  mkProg [(fnId 0, main)]

/-- **Case 17 (`assert_fail_cleanup_mutate_unwindResume`)**:
Subject writes `*r = 15`, fails `assert(0 == 1, unwind: .cleanup bb_clean)`, runs cleanup
mutation `*r = 115`, executes `ResumeUnwind`; outer catch harness observes `.unwound 115`. -/
def mrProg17 : Program :=
  let subject := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 15)
    ], .Switch (cU32 0) ⟨[(1, bbId 1)]⟩ (bbId 2), .Regular⟩),
     (bbId 1, ⟨[.Assign (.Local (locId 0)) (cU32 15)], .Return, .Regular⟩),
     (bbId 2, ⟨[], .StartUnwind cNullRaw (bbId 3), .Regular⟩),
     (bbId 3, ⟨[
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 115)
    ], .ResumeUnwind, .Cleanup⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 10)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) (some (bbId 2)), .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩),
     (bbId 2, ⟨[], .StopUnwind (bbId 3), .Catch⟩),
     (bbId 3, ⟨finishStmts 2 (cU32 0) (.Load (.Local (locId 3))), exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, subject)]

/-- **Case 18 (`assert_fail_cleanup_mutate_unwindTerminate`)**:
Subject fails `assert(1 == 0, unwind: .cleanup bb_clean)`, runs cleanup mutation, then executes
`unwindTerminate` (`IntrinsicOp.Abort`) -> `.abort`. -/
def mrProg18 : Program :=
  let subject := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true
    ], .Switch (cU32 1) ⟨[(0, bbId 1)]⟩ (bbId 2), .Regular⟩),
     (bbId 1, ⟨[.Assign (.Local (locId 0)) (cU32 10)], .Return, .Regular⟩),
     (bbId 2, ⟨[], .StartUnwind cNullRaw (bbId 3), .Regular⟩),
     (bbId 3, ⟨[
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 116)
    ], abortTerm, .Terminate⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 10)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) (some (bbId 2)), .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩),
     (bbId 2, ⟨[], .StopUnwind (bbId 3), .Catch⟩),
     (bbId 3, ⟨finishStmts 2 (cU32 0) (.Load (.Local (locId 3))), exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, subject)]

/-- **Case 19 (`assert_fail_unwind_terminate`)**:
Failing `assert(0 == 1, unwind: .terminate)` -> deterministic `.abort`. -/
def mrProg19 : Program :=
  let main := mkFn [(locId 0, u32Ty)] [] (locId 0)
    [(bbId 0, ⟨[], .Switch (cU32 0) ⟨[(1, bbId 1)]⟩ (bbId 2), .Regular⟩),
     (bbId 1, ⟨[], exitTerm, .Regular⟩),
     (bbId 2, ⟨[], abortTerm, .Terminate⟩)]
  mkProg [(fnId 0, main)]

/-- **Case 20 (`assert_fail_unwind_unreachable`)**:
Failing `assert(0 == 1, unwind: .unreachable)` -> `.ub`. -/
def mrProg20 : Program :=
  let main := mkFn [(locId 0, u32Ty)] [] (locId 0)
    [(bbId 0, ⟨[], .Switch (cU32 0) ⟨[(1, bbId 1)]⟩ (bbId 2), .Regular⟩),
     (bbId 1, ⟨[], exitTerm, .Regular⟩),
     (bbId 2, ⟨[], .Unreachable, .Cleanup⟩)]
  mkProg [(fnId 0, main)]

/-- **Case 21 (`callee_panic_partial_writeback_cleanup_release_protector_resume`)**:
Caller allocates `x = 10`, passes `&mut x` to panicking callee (`unwind: .cleanup bb_clean`).
Callee activates `FnEntry` protector, writes partial update `*r = 55`, panics (`StartUnwind`
-> `ResumeUnwind`), releasing its `FnEntry` protector (`end_call`). Caller's cleanup block
reads preserved `x == 55`, performs a direct parent write `x = x + 10 = 65` (which would UB on
`MachTB` if callee's protector were still active!), and executes `ResumeUnwind`; outer catch
harness catches and returns `.okCleanupRecovered 65 65`. -/
def mrProg21 : Program :=
  let callee := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 55)
    ], .Switch (cU32 0) ⟨[(1, bbId 1)]⟩ (bbId 2), .Regular⟩),
     (bbId 1, ⟨[.Assign (.Local (locId 0)) (cU32 55)], .Return, .Regular⟩),
     (bbId 2, ⟨[], .StartUnwind cNullRaw (bbId 3), .Regular⟩),
     (bbId 3, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let caller := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty), (locId 2, u32Ty)]
    [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2)
    ], .Call (cFn 2) .Rust
         [.ByValue (.AddrOf (.Deref (.Load (.Local (locId 1))) u32Ty) mutRefU32PtrTy)]
         (.Local (locId 2)) (some (bbId 1)) (some (bbId 2)), .Regular⟩),
     (bbId 1, ⟨[.Assign (.Local (locId 0)) (.Load (.Local (locId 2)))], .Return, .Regular⟩),
     (bbId 2, ⟨[
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty)
        (.BinOp (.Int .Add) (.Load (.Deref (.Load (.Local (locId 1))) u32Ty)) (cU32 10))
    ], .ResumeUnwind, .Cleanup⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 10)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) (some (bbId 2)), .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩),
     (bbId 2, ⟨[], .StopUnwind (bbId 3), .Catch⟩),
     (bbId 3, ⟨finishStmts 1 (.Load (.Local (locId 3))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, caller), (fnId 2, callee)]

/-- **Case 22 (`callee_panic_partial_writeback_cleanup_terminate`)**:
Same as Case 21, except caller's cleanup block mutates `x = 66` and terminates with
`unwindTerminate` (`IntrinsicOp.Abort`) -> `.abort`. -/
def mrProg22 : Program :=
  let callee := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 55)
    ], .StartUnwind cNullRaw (bbId 1), .Regular⟩),
     (bbId 1, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let caller := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty), (locId 2, u32Ty)]
    [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2)
    ], .Call (cFn 2) .Rust
         [.ByValue (.AddrOf (.Deref (.Load (.Local (locId 1))) u32Ty) mutRefU32PtrTy)]
         (.Local (locId 2)) (some (bbId 1)) (some (bbId 2)), .Regular⟩),
     (bbId 1, ⟨[.Assign (.Local (locId 0)) (.Load (.Local (locId 2)))], .Return, .Regular⟩),
     (bbId 2, ⟨[
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 66)
    ], abortTerm, .Terminate⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 10)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) (some (bbId 2)), .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩),
     (bbId 2, ⟨[], .StopUnwind (bbId 3), .Catch⟩),
     (bbId 3, ⟨finishStmts 1 (.Load (.Local (locId 3))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, caller), (fnId 2, callee)]

/-- **Case 23 (`multiframe_2hop_continue_lifo_protector_release_cleanup`)**:
3-frame stack `outer -> mid -> leaf`: `mid` activates `FnEntry` protector `p1`, writes `2`,
calls `leaf` with `.continue_` (`bb_resume`); `leaf` activates `FnEntry` protector `p2`, writes
partial update `3`, panics; `leaf` pops (releasing `p2`), `mid` runs `ResumeUnwind` (releasing
`p1` in strict LIFO order), `outer` catches in `bb_clean`, reads preserved `3`, performs direct
parent write `x = x * 100 = 300`, and returns `.okCleanupRecovered 300 300`. -/
def mrProg23 : Program :=
  let leaf := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 3)
    ], .StartUnwind cNullRaw (bbId 1), .Regular⟩),
     (bbId 1, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let mid := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty), (locId 2, u32Ty)]
    [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 2),
      .StorageLive (locId 2)
    ], .Call (cFn 3) .Rust
         [.ByValue (.AddrOf (.Deref (.Load (.Local (locId 1))) u32Ty) mutRefU32PtrTy)]
         (.Local (locId 2)) (some (bbId 1)) (some (bbId 2)), .Regular⟩),
     (bbId 1, ⟨[.Assign (.Local (locId 0)) (.Load (.Local (locId 2)))], .Return, .Regular⟩),
     (bbId 2, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let outer := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty), (locId 2, u32Ty)]
    [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .StorageLive (locId 2)
    ], .Call (cFn 2) .Rust
         [.ByValue (.AddrOf (.Deref (.Load (.Local (locId 1))) u32Ty) mutRefU32PtrTy)]
         (.Local (locId 2)) (some (bbId 1)) (some (bbId 2)), .Regular⟩),
     (bbId 1, ⟨[.Assign (.Local (locId 0)) (.Load (.Local (locId 2)))], .Return, .Regular⟩),
     (bbId 2, ⟨[
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty)
        (.BinOp (.Int .Mul) (.Load (.Deref (.Load (.Local (locId 1))) u32Ty)) (cU32 100))
    ], .ResumeUnwind, .Cleanup⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 1)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) (some (bbId 2)), .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩),
     (bbId 2, ⟨[], .StopUnwind (bbId 3), .Catch⟩),
     (bbId 3, ⟨finishStmts 1 (.Load (.Local (locId 3))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, outer), (fnId 2, mid), (fnId 3, leaf)]

/-- **Case 24 (`callee_panic_call_unwind_terminate`)**:
Caller calls panicking callee with `unwind: .terminate` (callee holds `FnEntry` protector and
writes `44` before panicking) -> `.abort`. -/
def mrProg24 : Program :=
  let callee := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 44)
    ], .StartUnwind cNullRaw (bbId 1), .Regular⟩),
     (bbId 1, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 10)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) (some (bbId 2)), .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩),
     (bbId 2, ⟨[], abortTerm, .Terminate⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 25 (`callee_panic_call_unwind_unreachable`)**:
Caller calls panicking callee with `unwind_block := none` (`UnwindAction.unreachable`) -> `.ub`. -/
def mrProg25 : Program :=
  let callee := mkFn [(locId 0, u32Ty), (locId 1, mutRefU32Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (.Local (locId 1)) true,
      .Assign (.Deref (.Load (.Local (locId 1))) u32Ty) (cU32 44)
    ], .StartUnwind cNullRaw (bbId 1), .Regular⟩),
     (bbId 1, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let main := mkFn
    [(locId 0, u32Ty), (locId 1, u32Ty), (locId 2, u32Ty), (locId 3, u32Ty), (locId 4, u32Ty)]
    [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 3),
      .StorageLive (locId 4),
      .Assign (.Local (locId 3)) (cU32 10)
    ], .Call (cFn 1) .Rust [.ByValue (.AddrOf (.Local (locId 3)) mutRefU32PtrTy)]
         (.Local (locId 4)) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨finishStmts 0 (.Load (.Local (locId 4))) (.Load (.Local (locId 3))),
               exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

/-- **Case 26 (`root_unwind_cleared_ceiling_ub_agreement`)** &
**Case 27 (`root_unwind_intact_ceiling_divergence`)**:
Bare root frame (`BottomOfStack`, no outer catch harness) writes `77` and executes
`StartUnwind` -> `ResumeUnwind`: MiniRust faults with `BottomOfStack` `.ub` in BOTH modes
(agrees with Trusted when `rootUnwindCeiling = false` [Case 26], diverges from Trusted `.panic`
when `rootUnwindCeiling = true` [Case 27]). -/
def mrProgRootUnwind : Program :=
  let main := mkFn [(locId 0, u32Ty), (locId 1, u32Ty)] [] (locId 0)
    [(bbId 0, ⟨[
      .StorageLive (locId 1),
      .Assign (.Local (locId 1)) (cU32 77)
    ], .StartUnwind cNullRaw (bbId 1), .Regular⟩),
     (bbId 1, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  mkProg [(fnId 0, main)]

/-- Dispatch table of the 28 canonical MiniRust programs (`none` for `idx ≥ 28`). -/
def mrCanonicalProg? : Nat → Option Program
  | 0 => some mrProg0
  | 1 => some mrProg1
  | 2 => some mrProg2
  | 3 => some mrProg3
  | 4 => some mrProg4
  | 5 => some mrProg5
  | 6 => some mrProg6
  | 7 => some mrProg7
  | 8 => some mrProg8
  | 9 => some mrProg9
  | 10 => some mrProg10
  | 11 => some mrProg11
  | 12 => some mrProg12
  | 13 => some mrProg13
  | 14 => some mrProg14
  | 15 => some mrProg15
  | 16 => some mrProg16
  | 17 => some mrProg17
  | 18 => some mrProg18
  | 19 => some mrProg19
  | 20 => some mrProg20
  | 21 => some mrProg21
  | 22 => some mrProg22
  | 23 => some mrProg23
  | 24 => some mrProg24
  | 25 => some mrProg25
  | 26 => some mrProgRootUnwind
  | 27 => some mrProgRootUnwind
  | _ => none

/-- Real MiniRust observer: `tb = false` runs on `Mach` (`BasicMemory<x86_64>`),
`tb = true` runs on `MachTB` (`TreeBorrowsMemory<x86_64>` with `implicit_writes = true`).
Fail-closed `.invalidOrUnsupported` for all `idx ≥ 28`. -/
def mrCrossFramePanicObserve (tb : Bool) (idx : Nat) : MrCrossFramePanicObs :=
  match mrCanonicalProg? idx with
  | none => .invalidOrUnsupported
  | some prog =>
    if tb then runProgramObsM (M := TBM) ({ implicit_writes := true } : TreeBorrowsParams) prog 120
    else runProgramObsM (M := BM) () prog 120

/-- Frozen expected MiniRust table for `tb = false` (`Mach`). -/
def mrExpectedBasicList : List MrCrossFramePanicObs :=
  [.okVal 42 42,
   .okVal 77 77,
   .okVal 99 99,
   .okVal 88 10088,
   .okVal 44 44033,
   .okVal 66 66055,
   .okVal 34 34,
   .okVal 20 20,
   .okVal 77 77,
   .okVal 99 99,
   .ub,
   .ub,
   .ub,
   .ub,
   .okVal 101 101,
   .okVal 102 102,
   .ub,
   .unwound 115,
   .abort,
   .abort,
   .ub,
   .okCleanupRecovered 65 65,
   .abort,
   .okCleanupRecovered 300 300,
   .abort,
   .ub,
   .ub,
   .ub]

/-- Frozen expected MiniRust table for `tb = true` (`MachTB`). -/
def mrExpectedTbList : List MrCrossFramePanicObs :=
  [.okVal 42 42,
   .okVal 77 77,
   .okVal 99 99,
   .okVal 88 10088,
   .okVal 44 44033,
   .okVal 66 66055,
   .okVal 34 34,
   .okVal 20 20,
   .ub,
   .ub,
   .ub,
   .ub,
   .ub,
   .ub,
   .okVal 101 101,
   .okVal 102 102,
   .ub,
   .unwound 115,
   .abort,
   .abort,
   .ub,
   .okCleanupRecovered 65 65,
   .abort,
   .okCleanupRecovered 300 300,
   .abort,
   .ub,
   .ub,
   .ub]

/-- **Kernel-checked 56-cell MiniRust execution table (`28 scenarios × 2 memory modes`)**:
every cell is executed on real `Mach` (`BasicMemory<x86_64>`) and `MachTB`
(`TreeBorrowsMemory<x86_64>`) via `stepM`, verified purely by kernel reduction (zero `native_decide`). -/
theorem mrCrossFramePanicObserve_table :
    (List.range mrCanonicalCaseCount).map (mrCrossFramePanicObserve false) = mrExpectedBasicList ∧
    (List.range mrCanonicalCaseCount).map (mrCrossFramePanicObserve true) = mrExpectedTbList := by
  constructor <;> kernel_rfl

/-- Out-of-range scenarios are fail-closed `.invalidOrUnsupported` in both modes. -/
theorem mrCrossFramePanicObserve_out_of_range (tb : Bool) (idx : Nat)
    (h : mrCanonicalCaseCount ≤ idx) :
    mrCrossFramePanicObserve tb idx = .invalidOrUnsupported := by
  unfold mrCanonicalCaseCount at h
  have hNone : mrCanonicalProg? idx = none := by
    unfold mrCanonicalProg?
    split <;> first | rfl | omega
  unfold mrCrossFramePanicObserve
  rw [hNone]

/-- Exact Tree Borrows mode-sensitivity predicate: Cases `8` (foreign write under active
`FnEntry` strong protector) and `9` (write through `Frozen` `&T`-derived raw pointer) flip
between `Mach` and `MachTB`. -/
def mrCaseModeSensitive : Nat → Bool
  | 8 | 9 => true
  | _ => false

private theorem list_getElem_eq_of_map {α : Type} {f : Nat → α} {xs : List α} {n : Nat}
    (h : (List.range n).map f = xs) (i : Nat) (hi : i < n) : f i = xs[i]?.getD (f i) := by
  have h' := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at h'
  rw [← h']
  rfl

/-- **Exact MiniRust Tree Borrows mode-sensitivity `↔` theorem**:
`Mach` and `MachTB` disagree on `idx < 28` if and only if `idx = 8` or `idx = 9`. -/
theorem mrCrossFramePanicObserve_mode_sensitivity :
    mrCrossFramePanicObserve false 8 = .okVal 77 77 ∧
    mrCrossFramePanicObserve true 8 = .ub ∧
    mrCrossFramePanicObserve false 9 = .okVal 99 99 ∧
    mrCrossFramePanicObserve true 9 = .ub ∧
    (∀ idx, idx < mrCanonicalCaseCount →
      (mrCrossFramePanicObserve false idx ≠ mrCrossFramePanicObserve true idx ↔
        mrCaseModeSensitive idx = true)) := by
  have hB := mrCrossFramePanicObserve_table.1
  have hT := mrCrossFramePanicObserve_table.2
  have hAll : ((List.range mrCanonicalCaseCount).all fun idx =>
      decide ((mrExpectedBasicList[idx]? ≠ mrExpectedTbList[idx]?) ↔
        mrCaseModeSensitive idx = true)) = true := by decide
  have cellB : ∀ idx, idx < mrCanonicalCaseCount →
      some (mrCrossFramePanicObserve false idx) = mrExpectedBasicList[idx]? := by
    intro idx hi
    have h' := congrArg (fun l => l[idx]?) hB
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have cellT : ∀ idx, idx < mrCanonicalCaseCount →
      some (mrCrossFramePanicObserve true idx) = mrExpectedTbList[idx]? := by
    intro idx hi
    have h' := congrArg (fun l => l[idx]?) hT
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  refine ⟨Option.some.inj (cellB 8 (by decide)), Option.some.inj (cellT 8 (by decide)),
    Option.some.inj (cellB 9 (by decide)), Option.some.inj (cellT 9 (by decide)), ?_⟩
  intro idx hi
  have hIff := of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hi))
  rw [← cellB idx hi, ← cellT idx hi] at hIff
  simpa [Option.some.injEq] using hIff

/-- **`MachTB.wfLive` preservation across ALL 28 canonical scenarios**: every booted and
executed `MachTB` scenario preserves the live-allocation Tree Borrows invariant. -/
theorem mrCanonicalProg_tb_wfLive (idx : Nat) (prog : Program) (m0 : MachTB)
    (_hProg : mrCanonicalProg? idx = some prog)
    (hBoot : bootProgramM (M := TBM) ({ implicit_writes := true } : TreeBorrowsParams) prog = .ok m0)
    (fuel : Nat) :
    match runToStopM fuel m0 with
    | .ok mEnd => MachTB.wfLive mEnd
    | .error (_, mStop) => MachTB.wfLive mStop :=
  runToStopM_tb_wfLive fuel
    (bootProgramM_tb_wfLive ({ implicit_writes := true } : TreeBorrowsParams) prog m0 hBoot)

/-- Exact UB-message witnesses on `MachTB` confirming the *genuine* root cause of Cases `8`,
`9`, `10`, `11`, `12`, `16`, `25`, `27` (not accidental harness errors!). -/
def runStopMsgTB (prog : Program) (fuel : Nat := 120) : Option String :=
  match bootProgramM (M := TBM) ({ implicit_writes := true } : TreeBorrowsParams) prog with
  | .ok m0 =>
    match runToStopM fuel m0 with
    | .error (.ub msg, _) => some msg
    | _ => none
  | .error _ => none

theorem mr_tb_exact_ub_diagnostics :
    runStopMsgTB mrProg8 =
      some "Tree Borrows: foreign read of protected Unique reference" ∧
    runStopMsgTB mrProg9 =
      some "Tree Borrows: local write of Frozen reference" ∧
    runStopMsgTB mrProg10 =
      some "dereferencing pointer to dead allocation" ∧
    runStopMsgTB mrProg11 =
      some "dereferencing pointer outside the bounds of its allocation" ∧
    runStopMsgTB mrProg12 =
      some "dereferencing pointer outside the bounds of its allocation" ∧
    runStopMsgTB mrProg16 =
      some "reached unreachable code" ∧
    runStopMsgTB mrProg25 =
      some "unwinding from a function where the caller did not specify an unwind_block" ∧
    runStopMsgTB mrProgRootUnwind =
      some "the function at the bottom of the stack must not unwind" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

end CanonicalMrPrograms

/-! ## §5. Episode 1 MiniRust Capstone & Silent Axiom / Import-Isolation Audit -/

/-- **Episode 1 MiniRust Cross-Frame Reference & Panic-Unwind Capstone.** -/
theorem ep1_minirust_cross_frame_panic_capstone :
    (type_of% @bootProgramM_tb_wfLive) ∧
    (type_of% @runToStopM_tb_wfLive) ∧
    (type_of% @evalPtrOffsetM_wrapping_eq) ∧
    (type_of% @evalPtrOffsetM_inbounds_eq) ∧
    (type_of% @ptrOffsetWrappingM_roundtrip) ∧
    (type_of% @evalTerminatorM_unreachable_ub) ∧
    (type_of% @evalTerminatorM_switch_assert) ∧
    (type_of% @evalTerminatorM_abort) ∧
    (type_of% @evalResumeUnwindM_dispatch) ∧
    (type_of% @tbm_node_protector_and_frozen_laws) ∧
    (type_of% @trusted_evalTerminator_unreachable_ub) ∧
    (type_of% @trusted_evalTerminator_unwindTerminate_abort) ∧
    (type_of% @trusted_evalTerminator_assert_pass) ∧
    (type_of% @trusted_evalTerminator_assert_fail) ∧
    (type_of% @trusted_applyUnwindAction_four_way) ∧
    (type_of% @trusted_unwindFromCallStack_continue_chain) ∧
    (type_of% @trusted_unwindFromCallStack_root_ceiling_iff) ∧
    (type_of% @trusted_evalBinOpOffset_oob_none) ∧
    (type_of% @trusted_evalArithOffset_roundtrip) ∧
    (type_of% @trusted_restoreCallerProtectors_releases) ∧
    (type_of% @mrCrossFramePanicObserve_table) ∧
    (type_of% @mrCrossFramePanicObserve_out_of_range) ∧
    (type_of% @mrCrossFramePanicObserve_mode_sensitivity) ∧
    (type_of% @mrCanonicalProg_tb_wfLive) ∧
    (type_of% @mr_tb_exact_ub_diagnostics) :=
  ⟨@bootProgramM_tb_wfLive, @runToStopM_tb_wfLive, @evalPtrOffsetM_wrapping_eq,
   @evalPtrOffsetM_inbounds_eq, @ptrOffsetWrappingM_roundtrip, @evalTerminatorM_unreachable_ub,
   @evalTerminatorM_switch_assert, @evalTerminatorM_abort, @evalResumeUnwindM_dispatch,
   @tbm_node_protector_and_frozen_laws, @trusted_evalTerminator_unreachable_ub,
   @trusted_evalTerminator_unwindTerminate_abort, @trusted_evalTerminator_assert_pass,
   @trusted_evalTerminator_assert_fail, @trusted_applyUnwindAction_four_way,
   @trusted_unwindFromCallStack_continue_chain, @trusted_unwindFromCallStack_root_ceiling_iff,
   @trusted_evalBinOpOffset_oob_none, @trusted_evalArithOffset_roundtrip,
   @trusted_restoreCallerProtectors_releases, @mrCrossFramePanicObserve_table,
   @mrCrossFramePanicObserve_out_of_range, @mrCrossFramePanicObserve_mode_sensitivity,
   @mrCanonicalProg_tb_wfLive, @mr_tb_exact_ub_diagnostics⟩

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Miri).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName ||
        (`Anneal).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported by MiniRustSpec.CrossFrameRefAndPanicMR"
  let ns := `MiniRustSpec.CrossFrameRefAndPanicMR
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on forbidden axiom {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    if ns.isPrefixOf c && !c.isInternal then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 25 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAudit

end MiniRustSpec.CrossFrameRefAndPanicMR
