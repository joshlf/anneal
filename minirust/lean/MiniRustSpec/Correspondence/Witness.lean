/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Run

/-!
# Non-vacuity witnesses

The correspondence theorems are implications whose hypotheses (`inFragment`,
`translateFn`, `StateRel`, and Anneal reachability facts) could in principle
be unsatisfiable. This module discharges them for concrete programs, and
checks the conclusions against *independent* executions of the MiniRust
interpretation, all by kernel computation (`decide`/`rfl`, no
`native_decide`):

* `sumTo`: the MIR of a `u32` loop computing `n + (n-1) + .. + 1`, with
  `switchInt`, wrapping `Add`/`Sub`, constants, and `Goto`. For `n = 3`:
  - `sumTo_anneal_ret`: Anneal's semantics returns `6` (computed);
  - `sumTo_rel`: the initial states are related;
  - `sumTo_minirust_ret`: hence (by `run_ret`) MiniRust performs a return that
    writes the bytes of `6u32` into the caller's return place;
  - `sumTo_minirust_direct`: running the MiniRust interpretation directly
    (16 steps) produces exactly that return place, so the theorem's
    conclusion agrees with an independent computation.
  - `sumTo_init_step`: the init block that `minimize` prepends steps into the
    related initial machine.
* `retUninit`: the MIR of a function returning an uninitialized `_0`.
  Anneal's semantics faults with UB (`retUninit_anneal_ub`), hence MiniRust
  raises UB (`retUninit_minirust_ub` via `run_ub`, and
  `retUninit_minirust_ub_from_start` via `run_ub_from_start`), which a direct
  computation confirms (`retUninit_minirust_direct`).
* `negMention`: the MIR of a function exercising `PlaceMention(_0)` (while `_0`
  is still uninitialized), wrapping `UnaryOp(Neg)` (`_0 = -_1`), and an
  `Unreachable` branch when `_1 == 0`:
  - for `_1 = 5`: returns `2^32 - 5 = 4294967291` (`negMention5_minirust_ret_from_start`,
    verified against `negMention5_minirust_direct`);
  - for `_1 = 0`: computes `-0 = 0` and takes the `Unreachable` terminator,
    raising UB (`negMention0_minirust_ub_from_start`, verified against
    `negMention0_minirust_direct`).
* `signedEdge`: the MIR of a signed `i8` function exercising two's-complement
  sign-bit decoding (`intFromBits`), `i8::MIN` (`-128i8`, bits `128`) wrapping
  negation (`-(-128i8) = -128i8`), negative `switchInt` branch keys (`-128`,
  `-1`), signed underflow wrapping (`-128i8 + (-1i8) = 127i8`), signed
  negative-by-negative `Mul` (`(-1i8) * (-2i8) = 2i8`), and end-to-end
  `MirNoUBTree` safety transfer (`signedEdgeMin_minirust_noUB`).
* `castBitNot`: mixed-width (`i8` and `u32`) `UnaryOp(Not)` (`BitNot`) and
  signed-widening / unsigned-narrowing `Cast(IntToInt)`.
* `spinLoop`: diverging UB-free loop exercising `mirCall_diverges_steps_ok` and
  lockstep `mirCall_diverges_rel` (`StateRel` + `Reaches` preserved for all `n`).
* `divRemI8` and `remOnlyI8`: signed `i8` truncating-toward-zero `Div` and `Rem`
  (`-7 / 3 = -2`, `-7 % 3 = -1`, `i8::MIN / 1 = -128`) plus all four division
  and remainder UB conditions (`x / 0`, `i8::MIN / -1`, `x % 0`, `i8::MIN % -1`)
  and converse `mirCall_steps_error`.
* `uncheckedArithI8`: signed `i8` `MulUnchecked`, `SubUnchecked`, and
  `AddUnchecked` both succeeding at the `i8::MIN` boundary (`64 * -2 = -128`,
  `-128 - (-2) = -126`, `-126 + 127 = 1`) and triggering each operator's
  signed overflow UB (`mirCall_ub`, `mirCall_outcome`, and direct checks of
  MiniRust's `throw_ub!` messages).
* `branchSpinLoop`: diverging conditional `while x != 0 {}` loop emitting a
  visible `.emit` branch event on every iteration (`treeSafe_of_step_inv`,
  `noRet_of_step_inv`, and `mirCall_diverges_rel`).
* `shiftI8` and `shlUncheckedI8`: signed `i8` `Shr`, `Shl`, `ShrUnchecked`, and
  `ShlUnchecked` including negative shift counts wrapped via `.rem_euclid(8)` and
  all four unchecked-shift UB paths (`s >= bits` and `s < 0`).
* `bitwiseI8` (plus `countOnes_neg86_i8` / `countOnes_neg1_i8`): signed `i8`
  two's-complement `BitAnd`, `BitOr`, and `BitXor` on negative operands
  (including cancellation of infinite leading two's-complement `1` bits under
  `BitXor`), alongside ground-truth checks of `IntUnOp::CountOnes` returning
  `u32` on negative `i8` inputs.
* `heteroShiftSwitch`: mixed-type `(i8, u32)` wrapping `Shr` / `Shl` with shift
  counts `258u32, 257u32 >= 256`, constant-discriminant `SwitchInt` on `-1i8`,
  and heterogeneous `(i8, i32)` `ShrUnchecked` / `ShlUnchecked` both succeeding
  at `k = 3i32` and faulting with UB at `k = 8i32` (`8 >= i8::BITS` even though
  `8 < i32::BITS`) and `k = -1i32` (`-1 < 0`).
* `uninitOperandUb` (plus `divExact_ok_i8`, `divExact_rem_ub_i8`,
  `divExact_zero_ub_i8`, `divExact_min_neg1_ub_i8`): reading an uninitialized
  local (`copy _0` while `_0` is `.uninit`) inside a `BinaryOp` operand, a
  `UnaryOp` operand, and a `SwitchInt` scrutinee (`mirCall_ub`,
  `mirCall_steps_error`, and direct checks of MiniRust's `"load at type but the
  data in memory violates the language invariant"` UB), alongside ground-truth
  checks of all four `IntBinOp::DivExact` outcomes.
* `tempMove`, `crossBlockMove`, `loopTempMove`, `storageLiveArgRet`,
  `diamondMoveJoin`, `tupleAggCastMove`, `deadRead`, `deadAssign`,
  `deadDeinit`, `deadPlaceMention`, `moveReuse`, `crossBlockMoveReuse`,
  `loopBackEdgeReuse`, `projAssignMoveReuse`, `projFieldMoveReuse`,
  `sameRvalueMoveReuse`, `moveRetPlace`, `diamondHalfMoveReuse`,
  `unmarkedTempAssign`, `storageDeadRet`, `storageDeadArg`,
  `storageDeadArgReadAfter`, and `projectedDeinit` (MR-1.3): temporaries with
  `StorageLive`/`StorageDead` (including `StorageLive` on `_0` and argument
  locals), root and projected `move` across `Use`, `UnaryOp`, `BinaryOp`,
  `Cast(IntToInt)`, `Aggregate(Tuple, ..)`, and `SwitchInt` in straight-line,
  branching, diamond join, and cyclic loop CFGs (with multi-pass back-edge
  `movedAtEntry` fixpoint convergence), `Deinit`, multi-local `initBlock`
  allocation of heterogeneous temporaries, first-fit address reuse, dead-local
  UB across reads, `Assign`, `Deinit`, and projected `PlaceMention`, and
  concrete semantic counterexamples showing why `movesOk` (including
  intra-rvalue, projected sibling-field, `Return`, diamond merge, and
  back-edge checks), `mentionsOk`, `storageDeadOk` (for both `_0` and
  arguments), and projection-free `Deinit` are each necessary for soundness.
  Their direct MiniRust runs allocate, so they are checked by `decide +kernel`
  (kernel evaluation; still no `native_decide`).
* `checkedArithI8`, `checkedTupleU32`, `uninitTupleField0`, and
  `uninitTupleField1`: checked integer arithmetic (`AddWithOverflow`,
  `SubWithOverflow`, `MulWithOverflow`), `(Int, bool)` 2-tuple locals and
  return places (including `IntType::with_overflow` trailing `Uninit` padding
  bytes on `(u32, bool)`), `Rvalue::Aggregate(Tuple, ..)` (`ValueExpr::Tuple`),
  and `.0` / `.1` field projections (`PlaceExpr::Field`) across no-overflow and
  overflow boundary inputs (`INT_MAX + 1`, `INT_MIN - 1`, `UINT_MAX + 1`,
  `0 - 1`, and signed/unsigned multiplication overflow), plus UB on reading
  `.0` or `.1` from an uninitialized tuple local.
* `callerMain`/`calleePair`, `projDestCaller`/`negI8Callee`/`flipBoolCallee`,
  `chainEntry`/`chainMid`/`chainLeaf`, `callArgUbCaller`,
  `calleeDivZeroCaller`/`divTenI8Callee`, `callSpinCaller`/`idU32Callee`,
  `callMoveReuse`, `callDestArgAlias`, `callProjMoveReuse`,
  `stmtMoveThenCallArg`, and `recCycleA`/`recCycleB` (MR-4.1): multi-function
  `translateProg` and `progInFragment` programs exercising `Terminator::Call`
  (`ByValue` and `InPlace` argument passing, `Constant::FnPointer`,
  `fn_from_ptr`, `check_abi_compatibility`, `create_frame`, multi-step
  `Call + initBlock` entry, and `UnwindAction::{Continue, Unreachable,
  Terminate}`), multi-frame `Terminator::Return` (`StackPopAction::BackToCaller`
  into root locals and projected `.0` / `.1` tuple fields), 3-deep nested call
  stacks returning `Ordering`, call-argument, post-call `move` reuse, and
  callee-body UB propagation, diverging multi-function call loops
  (`mirCallWithCallees_diverges_rel`), soundness counterexamples for
  return-place aliasing, projected `move` call arguments, pre-call `move` reuse,
  and cyclic call graphs, plus ground-truth unit checks of the `MR-4.1`
  `Interp` definitions.
-/

namespace MiniRustSpec.Correspondence.Witness

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

/-! ## MIR building blocks -/

def u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def u32Decl : LocalDecl := { mutability := .mut, ty := u32Ty, debugName := none }
def mkStmt (k : StatementKind) : MirAst.Statement := { kind := k, span := "witness" }
def mkTerm (k : TerminatorKind) : MirAst.Terminator := { kind := k, span := "witness" }
def local_ (i : Nat) : Place := { local_ := i, projection := [] }
def constU32 (n : Nat) : Operand := .constant { ty := u32Ty, val := .scalar (.int ⟨n, 4⟩) }

def u32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbi (nargs : Nat) : FnAbi :=
  { args := List.replicate nargs { layout := u32Layout, mode := .direct },
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-! ## `sum_to` -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn sum_to(mut n: u32) -> u32 {
    let mut acc = 0;            // bb0: _0 = const 0_u32; goto -> bb1
    while n != 0 {              // bb1: switchInt(copy _1) -> [0: bb3, otherwise: bb2]
        acc = acc.wrapping_add(n); // bb2: _0 = Add(copy _0, copy _1)
        n = n.wrapping_sub(1);     //      _1 = Sub(copy _1, const 1_u32); goto -> bb1
    }
    acc                         // bb3: return
}
```
(with `acc` living in the return place). -/
def sumTo : CapturedMir where
  defPath := "witness::sum_to"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 0)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 3)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 0)) (.copy (local_ 1)))),
        mkStmt (.assign (local_ 1) (.binaryOp .sub (.copy (local_ 1)) (constU32 1)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem sumTo_inFragment : inFragment sumTo = true := by decide

def u32 : Gen.IntType := ⟨.Unsigned, ⟨4⟩⟩

/-- The MiniRust function `minimize` produces for `sumTo`, spelled out. -/
def sumToFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 0) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[], .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 3)]⟩ (bbName 2),
      .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0))) (.Load (.Local (localName 1)))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 1))) (.Constant (.Int 1) (.Int u32)))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 3, ⟨[], .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem sumTo_translate : translateFn sumTo = some sumToFn := rfl

/-! ## The surrounding MiniRust machine -/

/-- The caller's return place: allocation `0`, at address `64`. -/
def retPtr : Ptr := { addr := 64, provenance := some (⟨0⟩, ()) }

def retAlloc : Gen.Allocation :=
  { data := List.replicate 4 .Uninit, addr := 64, align := ⟨4⟩, kind := .Stack, live := true,
    extra := () }

/-- A caller that holds its return place in its own `_0`. Execution after the
return (in the caller) is outside the correspondence, so its body is empty. -/
def callerFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true

def callerFrame : Frame :=
  { func := callerFn, locals := ⟨[(localName 0, retPtr)]⟩, stack_pop_action := .BottomOfStack,
    next_block := bbName 0, next_stmt := 0, extra := () }

/-- The callee's locals live at addresses `128` (`_0`) and `256` (`_1`). -/
def ctx0 : Ctx :=
  { caller := callerFrame, payloads := [], base := [retAlloc], addrs := [128, 256],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

def emptyProg : Gen.Program :=
  { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩, traits := ⟨[]⟩, vtables := ⟨[]⟩ }

/-- A MiniRust machine running `fn` under caller context `ctx` with Anneal
locals `locals` at the given callee program counter. -/
def machineWithCtx (ctx : Ctx) (body : CapturedMir) (fn : Gen.Function) (locals : List LocalSlot)
    (blk : Gen.BbName) : Mach :=
  { prog := emptyProg,
    mem := { memory := { allocations := ctx.base ++
                           localAllocs ctx (body.localDecls.take (body.argCount + 1)) locals,
                         _phantom := {} },
             accesses := [] },
    intptrcast := ⟨⟨[]⟩⟩,
    threads := [thread1 ctx [ctx.caller,
      { calleeFrame fn ctx (body.argCount + 1) 0 0 with next_block := blk }]],
    active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [], global_ptrs := ⟨[]⟩,
    fn_ptrs := ⟨[]⟩, vtable_ptrs := ⟨[]⟩, stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

def machine : CapturedMir → Gen.Function → List LocalSlot → Gen.BbName → Mach :=
  machineWithCtx ctx0

theorem ctx0_ok1 {body : CapturedMir} (h : body.localDecls = [u32Decl]) : CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | _ + 1, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem ctx0_ok2 {body : CapturedMir} (h : body.localDecls = [u32Decl, u32Decl]) : CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-! ## `sum_to(3)` -/

def sumToS0 : MachineState := initMachineState sumTo [.scalar ⟨3, 4⟩]

/-- MiniRust at the start of MIR block `bb0`. -/
def sumToM0 : Mach := machine sumTo sumToFn sumToS0.frame.locals (bbName 0)

/-- MiniRust at the `minimize` init block (the function's `start`). -/
def sumToMInit : Mach := machine sumTo sumToFn sumToS0.frame.locals sumToFn.start

theorem sumTo_init_step : Interp.step sumToMInit = .ok sumToM0 := rfl

/-- `minimize`'s init block (here only `Goto(bb0)`) runs from the entry
relation into the relation at `bb0` (`step_start`). -/
theorem sumTo_rel : StateRel sumTo sumToFn ctx0 sumToS0 sumToM0 := by
  obtain ⟨m0, hm0, hrel⟩ := step_start sumTo_inFragment sumTo_translate
    (initMachineState_startRel sumTo_inFragment ctx0 (ctx0_ok2 rfl) [.scalar ⟨3, 4⟩] (by decide)
      sumToMInit rfl rfl rfl)
  have h : Interp.steps (initLen sumTo) sumToMInit = .ok sumToM0 := rfl
  rw [h] at hm0
  cases hm0
  exact hrel

/-- The branch observations of `sum_to(3)`: the scrutinee of each
`switchInt`. -/
def sumToTrace : List (Event MirEffect) :=
  [3, 2, 1, 0].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

/-- Anneal's semantics of `sum_to(3)` returns `6` (computed by the kernel). -/
theorem sumTo_anneal_ret :
    ReachesRet (mirTree sumTo sumToS0) sumToTrace (.normal (.scalar ⟨6, 4⟩, sumToS0.memory)) :=
  runA_sound sumTo 20 _ _ _ rfl

/-- Anneal's interaction tree for `sum_to(3)` is UB-free (`MirNoUBTree`). -/
theorem sumTo_noUB : MirNoUBTree (mirCallTree sumTo [.scalar ⟨3, 4⟩]) :=
  runA_noUB sumTo 20 _ _ _ rfl

/-- Therefore MiniRust, started from the related machine, performs a return
whose return place holds the little-endian bytes of `6u32`. -/
theorem sumTo_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n sumToM0 = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    run_ret sumTo_inFragment sumTo_translate ctx0 sumToS0 sumToM0 sumTo_rel sumTo_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [sumTo] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- The same return, computed directly by running the MiniRust interpretation
for 16 steps (one per Anneal step). -/
theorem sumTo_minirust_direct :
    (Interp.steps 16 sumToM0).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1]) := rfl

/-- Whole-execution return starting at `f.start` (including `minimize`'s
init block), directly via `mirCall_ret` without any phantom `bb0` machine. -/
theorem sumTo_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n sumToMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret sumTo_inFragment sumTo_translate ctx0 (ctx0_ok2 rfl) [.scalar ⟨3, 4⟩]
      (by decide) sumToMInit rfl rfl rfl sumTo_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [sumTo] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- Direct 17-step run from `f.start` (init block + 16 MIR steps). -/
theorem sumTo_minirust_direct_from_start :
    (Interp.steps 17 sumToMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1]) := rfl

/-! ## Returning an uninitialized `_0` -/

/-- MIR of a function whose only block returns without writing `_0`. -/
def retUninit : CapturedMir where
  defPath := "witness::ret_uninit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl]
  basicBlocks := [{ statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem retUninit_inFragment : inFragment retUninit = true := by decide

def retUninitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[(bbName 0, ⟨[], .Return, .Regular⟩), (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem retUninit_translate : translateFn retUninit = some retUninitFn := rfl

def retUninitS0 : MachineState := initMachineState retUninit []

def retUninitM0 : Mach := machine retUninit retUninitFn retUninitS0.frame.locals (bbName 0)

def retUninitMInit : Mach := machine retUninit retUninitFn retUninitS0.frame.locals retUninitFn.start

theorem retUninit_rel : StateRel retUninit retUninitFn ctx0 retUninitS0 retUninitM0 := by
  obtain ⟨m0, hm0, hrel⟩ := step_start retUninit_inFragment retUninit_translate
    (initMachineState_startRel retUninit_inFragment ctx0 (ctx0_ok1 rfl) [] (by decide)
      retUninitMInit rfl rfl rfl)
  have h : Interp.steps (initLen retUninit) retUninitMInit = .ok retUninitM0 := rfl
  rw [h] at hm0
  cases hm0
  exact hrel

/-- Anneal's semantics of `ret_uninit()` faults (computed by the kernel). -/
theorem retUninit_anneal_ub : ∃ tr u, Reaches (mirTree retUninit retUninitS0) tr u ∧ FaultNow u :=
  faultsA_sound retUninit 1 _ (by decide)

/-- Therefore MiniRust raises UB. -/
theorem retUninit_minirust_ub : ∃ (n : Nat) (msg : String), Interp.steps n retUninitM0 = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := retUninit_anneal_ub
  exact run_ub retUninit_inFragment retUninit_translate ctx0 retUninitS0 retUninitM0 retUninit_rel hr hf

/-- Direct computation: MiniRust's first step is UB. -/
theorem retUninit_minirust_direct :
    ∃ msg, Interp.step retUninitM0 = .error (.ub msg) :=
  ⟨_, rfl⟩

/-- Whole-execution UB starting at `f.start` (including `minimize`'s init
block), directly via `mirCall_ub`. -/
theorem retUninit_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n retUninitMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := retUninit_anneal_ub
  exact mirCall_ub retUninit_inFragment retUninit_translate ctx0 (ctx0_ok1 rfl) []
    (by decide) retUninitMInit rfl rfl rfl hr hf

/-! ## `PlaceMention`, `UnaryOp(Neg)`, and `Unreachable` -/

/-- MIR of a function exercising `PlaceMention(_0)` (while `_0` is still
uninitialized), wrapping integer negation `_0 = Neg(copy _1)`, and an
`Unreachable` terminator on the `_1 == 0` branch. -/
def negMention : CapturedMir where
  defPath := "witness::neg_mention"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.placeMention (local_ 0)),
        mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1))))],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false },
    { statements := [], terminator := mkTerm .unreachable, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem negMention_inFragment : inFragment negMention = true := by decide

def negMentionFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .PlaceMention (.Local (localName 0)),
      .Assign (.Local (localName 0)) (.UnOp (.Int .Neg) (.Load (.Local (localName 1))))],
      .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[], .Return, .Regular⟩),
    (bbName 2, ⟨[], .Unreachable, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem negMention_translate : translateFn negMention = some negMentionFn := rfl

def negMention5S0 : MachineState := initMachineState negMention [.scalar ⟨5, 4⟩]
def negMention5MInit : Mach := machine negMention negMentionFn negMention5S0.frame.locals negMentionFn.start

theorem negMention5_startRel :
    StartRel negMention negMentionFn ctx0 negMention5S0 negMention5MInit :=
  initMachineState_startRel negMention_inFragment ctx0 (ctx0_ok2 rfl) [.scalar ⟨5, 4⟩]
    (by decide) negMention5MInit rfl rfl rfl

def negMention5Trace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 5))), PUnit.unit⟩]

theorem negMention5_anneal_ret :
    ReachesRet (mirTree negMention negMention5S0) negMention5Trace
      (.normal (.scalar ⟨4294967291, 4⟩, negMention5S0.memory)) :=
  runA_sound negMention 10 _ _ _ rfl

theorem negMention5_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n negMention5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 4294967291 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    run_ret_from_start negMention_inFragment negMention_translate ctx0 negMention5S0
      negMention5MInit negMention5_startRel negMention5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [negMention] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem negMention5_minirust_direct :
    (Interp.steps 5 negMention5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 4294967291 }, [1]) := rfl

def negMention0S0 : MachineState := initMachineState negMention [.scalar ⟨0, 4⟩]
def negMention0MInit : Mach := machine negMention negMentionFn negMention0S0.frame.locals negMentionFn.start

theorem negMention0_startRel :
    StartRel negMention negMentionFn ctx0 negMention0S0 negMention0MInit :=
  initMachineState_startRel negMention_inFragment ctx0 (ctx0_ok2 rfl) [.scalar ⟨0, 4⟩]
    (by decide) negMention0MInit rfl rfl rfl

theorem negMention0_anneal_ub :
    ∃ tr u, Reaches (mirTree negMention negMention0S0) tr u ∧ FaultNow u :=
  faultsA_sound negMention 10 _ (by decide)

theorem negMention0_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n negMention0MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := negMention0_anneal_ub
  exact run_ub_from_start negMention_inFragment negMention_translate ctx0 negMention0S0
    negMention0MInit negMention0_startRel hr hf

theorem negMention0_minirust_direct :
    ∃ msg, Interp.steps 5 negMention0MInit = .error (.ub msg) :=
  ⟨_, rfl⟩

/-! ## Signed two's-complement corner cases (`i8::MIN`, negative `switchInt`, `MirNoUBTree`) -/

def i8Ty : Ty := { kind := .int .i8, layoutIdx := 0 }
def i8Decl : LocalDecl := { mutability := .mut, ty := i8Ty, debugName := none }
def i8 : Gen.IntType := ⟨.Signed, ⟨1⟩⟩
def constI8 (bits : Nat) : Operand := .constant { ty := i8Ty, val := .scalar (.int ⟨bits, 1⟩) }

def i8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiI8 (nargs : Nat) : FnAbi :=
  { args := List.replicate nargs { layout := i8Layout, mode := .direct },
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

def retAllocI8 : Gen.Allocation :=
  { data := [.Uninit], addr := 64, align := ⟨1⟩, kind := .Stack, live := true, extra := () }

def callerFnI8 : Gen.Function where
  locals := ⟨[(localName 0, .Int i8)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true

def callerFrameI8 : Frame :=
  { func := callerFnI8, locals := ⟨[(localName 0, retPtr)]⟩, stack_pop_action := .BottomOfStack,
    next_block := bbName 0, next_stmt := 0, extra := () }

def ctxI8 : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8], addrs := [128, 256],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxI8_ok2 {body : CapturedMir} (h : body.localDecls = [i8Decl, i8Decl]) :
    CtxOk body ctxI8 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn signed_edge(x: i8) -> i8 {
    let y = x.wrapping_neg(); // bb0: _0 = Neg(copy _1); switchInt(copy _0) -> [-128i8: bb1, -1i8: bb2, _: bb3]
    match y {
        -128 => y.wrapping_add(-1), // bb1: _0 = Add(copy _0, const -1i8); return  (-> 127i8)
        -1   => y.wrapping_mul(-2), // bb2: _0 = Mul(copy _0, const -2i8); return  (-> 2i8)
        _    => y,                  // bb3: return
    }
}
```
where `-128i8` has bit pattern `128`, `-1i8` has bit pattern `255`, and `-2i8`
has bit pattern `254`. -/
def signedEdge : CapturedMir where
  defPath := "witness::signed_edge"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1))))],
      terminator := mkTerm (.switchInt (.copy (local_ 0))
        { branches := [(128, 1), (255, 2)], otherwise := 3 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 0)) (constI8 255)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .mul (.copy (local_ 0)) (constI8 254)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem signedEdge_inFragment : inFragment signedEdge = true := by decide

def signedEdgeFn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0)) (.UnOp (.Int .Neg) (.Load (.Local (localName 1))))],
      .Switch (.Load (.Local (localName 0))) ⟨[(-128, bbName 1), (-1, bbName 2)]⟩ (bbName 3),
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0))) (.Constant (.Int (-1)) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Mul) (.Load (.Local (localName 0))) (.Constant (.Int (-2)) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem signedEdge_translate : translateFn signedEdge = some signedEdgeFn := rfl

/-- Input `x = -128i8` (`i8::MIN`, bits `128`): `-(-128i8)` overflows signed
`i8` and wraps back to `-128i8`, takes the `-128` `switchInt` arm, and
`-128i8 + (-1i8)` underflows signed `i8` and wraps to `127i8` (`i8::MAX`). -/
def signedEdgeMinS0 : MachineState := initMachineState signedEdge [.scalar ⟨128, 1⟩]
def signedEdgeMinMInit : Mach :=
  machineWithCtx ctxI8 signedEdge signedEdgeFn signedEdgeMinS0.frame.locals signedEdgeFn.start

def signedEdgeMinTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 128))), PUnit.unit⟩]

theorem signedEdgeMin_anneal_ret :
    ReachesRet (mirCallTree signedEdge [.scalar ⟨128, 1⟩]) signedEdgeMinTrace
      (.normal (.scalar ⟨127, 1⟩, signedEdgeMinS0.memory)) :=
  runA_sound signedEdge 10 _ _ _ rfl

theorem signedEdgeMin_noUB : MirNoUBTree (mirCallTree signedEdge [.scalar ⟨128, 1⟩]) :=
  runA_noUB signedEdge 10 _ _ _ rfl

theorem signedEdgeMin_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n signedEdgeMinMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 127 } ∧
      m'.threads = [thread1 ctxI8 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret signedEdge_inFragment signedEdge_translate ctxI8 (ctxI8_ok2 rfl)
      [.scalar ⟨128, 1⟩] (by decide) signedEdgeMinMInit rfl rfl rfl signedEdgeMin_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [signedEdge] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- End-to-end `MirNoUBTree` safety transfer: any error within `n` MiniRust
steps from `f.start` occurs strictly after `k < n` steps at which MiniRust has
already completed the callee's return (`ReturnRel`). -/
theorem signedEdgeMin_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n signedEdgeMinMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k signedEdgeMinMInit = .ok mRet ∧
      ReturnRel signedEdge ctxI8 s' v mRet ∧
      ReachesRet (mirCallTree signedEdge [.scalar ⟨128, 1⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB signedEdge_inFragment signedEdge_translate ctxI8 (ctxI8_ok2 rfl)
    [.scalar ⟨128, 1⟩] (by decide) signedEdgeMinMInit rfl rfl rfl signedEdgeMin_noUB herr

theorem signedEdgeMin_minirust_direct :
    (Interp.steps 5 signedEdgeMinMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 127 }, [1]) := rfl

/-- Input `x = 1i8` (bits `1`): `-(1i8) = -1i8` (bits `255`), takes the `-1`
`switchInt` arm, and `(-1i8) * (-2i8) = 2i8` (bits `2`). -/
def signedEdgeOneS0 : MachineState := initMachineState signedEdge [.scalar ⟨1, 1⟩]
def signedEdgeOneMInit : Mach :=
  machineWithCtx ctxI8 signedEdge signedEdgeFn signedEdgeOneS0.frame.locals signedEdgeFn.start

def signedEdgeOneTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 255))), PUnit.unit⟩]

theorem signedEdgeOne_anneal_ret :
    ReachesRet (mirCallTree signedEdge [.scalar ⟨1, 1⟩]) signedEdgeOneTrace
      (.normal (.scalar ⟨2, 1⟩, signedEdgeOneS0.memory)) :=
  runA_sound signedEdge 10 _ _ _ rfl

theorem signedEdgeOne_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n signedEdgeOneMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 2 } ∧
      m'.threads = [thread1 ctxI8 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret signedEdge_inFragment signedEdge_translate ctxI8 (ctxI8_ok2 rfl)
      [.scalar ⟨1, 1⟩] (by decide) signedEdgeOneMInit rfl rfl rfl signedEdgeOne_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [signedEdge] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem signedEdgeOne_minirust_direct :
    (Interp.steps 5 signedEdgeOneMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 2 }, [1]) := rfl

/-! ## Cross-width `Cast(IntToInt)` (sign-extension & truncation) and `UnaryOp(Not)` (`BitNot`) -/

def fnAbiI8ToU32 : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctx0_ok_u32_i8 {body : CapturedMir} (h : body.localDecls = [u32Decl, i8Decl]) :
    CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn cast_bitnot(mut x: i8) -> u32 {
    x = !x;                  // bb0: _1 = Not(copy _1)
    let w = x as u32;        //      _0 = Cast(IntToInt, copy _1, u32)
    match x {                //      switchInt(copy _1) -> [-5i8: bb1, otherwise: bb2]
        -5 => {
            let _t = w as i8; // bb1: _1 = Cast(IntToInt, copy _0, i8)
            !w                //      _0 = Not(copy _0); return
        }
        _ => unreachable!(), // bb2: unreachable
    }
}
```
For `x = 4i8` (bits `4`), `!4i8 = -5i8` (bits `251`), sign-extending `-5i8 as u32`
yields `4294967291u32` (`0xFFFFFFFB`), narrowing `4294967291u32 as i8` truncates
back to `-5i8` (bits `251`), and `!4294967291u32 = 4u32`. -/
def castBitNot : CapturedMir where
  defPath := "witness::cast_bitnot"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.unaryOp .not (.copy (local_ 1)))),
        mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 1)) u32Ty))],
      terminator := mkTerm (.switchInt (.copy (local_ 1))
        { branches := [(251, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.cast .intToInt (.copy (local_ 0)) i8Ty)),
        mkStmt (.assign (local_ 0) (.unaryOp .not (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [], terminator := mkTerm .unreachable, isCleanup := false }]
  fnAbi := fnAbiI8ToU32
  layouts := emptyLayoutTable
  allocations := []

theorem castBitNot_inFragment : inFragment castBitNot = true := by decide

def castBitNotFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int i8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1)) (.UnOp (.Int .BitNot) (.Load (.Local (localName 1)))),
      .Assign (.Local (localName 0)) (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 1))))],
      .Switch (.Load (.Local (localName 1))) ⟨[(-5, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 1)) (.UnOp (.Cast (.IntToInt i8)) (.Load (.Local (localName 0)))),
      .Assign (.Local (localName 0)) (.UnOp (.Int .BitNot) (.Load (.Local (localName 0))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Unreachable, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem castBitNot_translate : translateFn castBitNot = some castBitNotFn := rfl

def castBitNot4S0 : MachineState := initMachineState castBitNot [.scalar ⟨4, 1⟩]
def castBitNot4MInit : Mach :=
  machine castBitNot castBitNotFn castBitNot4S0.frame.locals castBitNotFn.start

def castBitNot4Trace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 251))), PUnit.unit⟩]

theorem castBitNot4_anneal_ret :
    ReachesRet (mirCallTree castBitNot [.scalar ⟨4, 1⟩]) castBitNot4Trace
      (.normal (.scalar ⟨4, 4⟩, castBitNot4S0.memory)) :=
  runA_sound castBitNot 10 _ _ _ rfl

theorem castBitNot4_noUB : MirNoUBTree (mirCallTree castBitNot [.scalar ⟨4, 1⟩]) :=
  runA_noUB castBitNot 10 _ _ _ rfl

theorem castBitNot4_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n castBitNot4MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 4 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret castBitNot_inFragment castBitNot_translate ctx0 (ctx0_ok_u32_i8 rfl)
      [.scalar ⟨4, 1⟩] (by decide) castBitNot4MInit rfl rfl rfl castBitNot4_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [castBitNot] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem castBitNot4_minirust_direct :
    (Interp.steps 7 castBitNot4MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 4 }, [1]) := rfl

/-! ## Diverging UB-free loop (`spinLoop`) -/

/-- MIR of a diverging loop `fn spin_loop() -> u32 { loop {} }`. -/
def spinLoop : CapturedMir where
  defPath := "witness::spin_loop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl]
  basicBlocks := [{ statements := [], terminator := mkTerm (.goto 0), isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem spinLoop_inFragment : inFragment spinLoop = true := by decide

def spinLoopFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[(bbName 0, ⟨[], .Goto (bbName 0), .Regular⟩),
              (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem spinLoop_translate : translateFn spinLoop = some spinLoopFn := rfl

def spinLoopS0 : MachineState := initMachineState spinLoop []
def spinLoopMInit : Mach := machine spinLoop spinLoopFn spinLoopS0.frame.locals spinLoopFn.start

theorem spinLoop_step_self :
    ∀ s, s = spinLoopS0 → ∃ s', stepMirFn spinLoop s = .tau (.running s') ∧ s' = spinLoopS0 := by
  rintro s rfl
  exact ⟨spinLoopS0, rfl, rfl⟩

/-- `spinLoop` is UB-free across its infinite interaction tree. -/
theorem spinLoop_noUB : MirNoUBTree (mirCallTree spinLoop []) :=
  treeSafe_of_tau_inv spinLoop_step_self rfl

/-- `spinLoop` never reaches a return outcome. -/
theorem spinLoop_diverges (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet (mirCallTree spinLoop []) tr o :=
  noRet_of_tau_inv spinLoop_step_self rfl tr o

/-- Therefore MiniRust started at `f.start` succeeds for every step count `n : Nat`. -/
theorem spinLoop_minirust_steps_ok (n : Nat) :
    ∃ m', Interp.steps n spinLoopMInit = .ok m' :=
  mirCall_diverges_steps_ok spinLoop_inFragment spinLoop_translate ctx0 (ctx0_ok1 rfl) []
    (by decide) spinLoopMInit rfl rfl rfl spinLoop_noUB spinLoop_diverges n

/-- Stronger lockstep divergence witness via `mirCall_diverges_rel`: for every
`n : Nat`, `initLen spinLoop + n` MiniRust steps from `f.start` stay in `StateRel` with an
Anneal state reachable via `Reaches (mirCallTree spinLoop [])`. -/
theorem spinLoop_minirust_diverges_rel (n : Nat) :
    ∃ s' m' tr, Interp.steps (initLen spinLoop + n) spinLoopMInit = .ok m' ∧
      StateRel spinLoop spinLoopFn ctx0 s' m' ∧
      Reaches (mirCallTree spinLoop []) tr (mirTree spinLoop s') :=
  mirCall_diverges_rel spinLoop_inFragment spinLoop_translate ctx0 (ctx0_ok1 rfl) []
    (by decide) spinLoopMInit rfl rfl rfl spinLoop_noUB spinLoop_diverges n

/-! ## Signed `Div` and `Rem` (truncation toward zero and all 4 UB conditions) -/

def ctxI8_3 : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8], addrs := [128, 256, 384],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxI8_ok3 {body : CapturedMir} (h : body.localDecls = [i8Decl, i8Decl, i8Decl]) :
    CtxOk body ctxI8_3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn div_rem_i8(mut a: i8, b: i8) -> i8 {
    let q = a / b;   // bb0: _0 = Div(copy _1, copy _2)
    a = a % b;       //      _1 = Rem(copy _1, copy _2)
    match q {        //      switchInt(copy _0) -> [-2i8: bb1, otherwise: bb2]
        -2 => a,     // bb1: _0 = Use(copy _1); return
        _  => q,     // bb2: return
    }
}
```
where `-2i8` has bit pattern `254`. -/
def divRemI8 : CapturedMir where
  defPath := "witness::div_rem_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .div (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 1) (.binaryOp .rem (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm (.switchInt (.copy (local_ 0))
        { branches := [(254, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem divRemI8_inFragment : inFragment divRemI8 = true := by decide

def divRemI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Div) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Rem) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Switch (.Load (.Local (localName 0))) ⟨[(-2, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem divRemI8_translate : translateFn divRemI8 = some divRemI8Fn := rfl

/-- Input `(-7i8, 3i8)` (bits `249`, `3`): truncating division gives `-7 / 3 = -2`
(bits `254`, taking `bb1`), and truncating remainder gives `-7 % 3 = -1`
(bits `255`), returned in `_0`. -/
def divRemNeg7S0 : MachineState := initMachineState divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨3, 1⟩]
def divRemNeg7MInit : Mach :=
  machineWithCtx ctxI8_3 divRemI8 divRemI8Fn divRemNeg7S0.frame.locals divRemI8Fn.start

def divRemNeg7Trace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 254))), PUnit.unit⟩]

theorem divRemNeg7_anneal_ret :
    ReachesRet (mirCallTree divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨3, 1⟩]) divRemNeg7Trace
      (.normal (.scalar ⟨255, 1⟩, divRemNeg7S0.memory)) :=
  runA_sound divRemI8 10 _ _ _ rfl

theorem divRemNeg7_noUB : MirNoUBTree (mirCallTree divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨3, 1⟩]) :=
  runA_noUB divRemI8 10 _ _ _ rfl

theorem divRemNeg7_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n divRemNeg7MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 255 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret divRemI8_inFragment divRemI8_translate ctxI8_3 (ctxI8_ok3 rfl)
      [.scalar ⟨249, 1⟩, .scalar ⟨3, 1⟩] (by decide) divRemNeg7MInit rfl rfl rfl divRemNeg7_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [divRemI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem divRemNeg7_minirust_direct :
    (Interp.steps 6 divRemNeg7MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 255 }, [1]) := rfl

/-- Non-UB signed boundary `(-128i8, 1i8)` (`i8::MIN / 1 = -128i8`, bits `128`). -/
def divRemMinOneS0 : MachineState := initMachineState divRemI8 [.scalar ⟨128, 1⟩, .scalar ⟨1, 1⟩]
def divRemMinOneMInit : Mach :=
  machineWithCtx ctxI8_3 divRemI8 divRemI8Fn divRemMinOneS0.frame.locals divRemI8Fn.start

def divRemMinOneTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 128))), PUnit.unit⟩]

theorem divRemMinOne_anneal_ret :
    ReachesRet (mirCallTree divRemI8 [.scalar ⟨128, 1⟩, .scalar ⟨1, 1⟩]) divRemMinOneTrace
      (.normal (.scalar ⟨128, 1⟩, divRemMinOneS0.memory)) :=
  runA_sound divRemI8 10 _ _ _ rfl

theorem divRemMinOne_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n divRemMinOneMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 128 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret divRemI8_inFragment divRemI8_translate ctxI8_3 (ctxI8_ok3 rfl)
      [.scalar ⟨128, 1⟩, .scalar ⟨1, 1⟩] (by decide) divRemMinOneMInit rfl rfl rfl divRemMinOne_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [divRemI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem divRemMinOne_minirust_direct :
    (Interp.steps 5 divRemMinOneMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 128 }, [1]) := rfl

/-- Division-by-zero UB (`-7i8 / 0i8`) via `mirCall_ub`, `mirCall_steps_error`,
and direct check of MiniRust's `"division by zero"` message. -/
def divByZeroS0 : MachineState := initMachineState divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]
def divByZeroMInit : Mach :=
  machineWithCtx ctxI8_3 divRemI8 divRemI8Fn divByZeroS0.frame.locals divRemI8Fn.start

theorem divByZero_anneal_ub :
    ∃ tr u, Reaches (mirCallTree divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound divRemI8 5 _ (by decide)

theorem divByZero_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n divByZeroMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := divByZero_anneal_ub
  exact mirCall_ub divRemI8_inFragment divRemI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩] (by decide) divByZeroMInit rfl rfl rfl hr hf

theorem divByZero_minirust_direct :
    Interp.steps 2 divByZeroMInit = .error (.ub "division by zero") := rfl

/-- Converse `mirCall_steps_error` witness: MiniRust's 2-step error on
`divByZeroMInit` implies Anneal `mirCallTree` reaches `FaultNow` (or already
returned, which is ruled out on `divByZero`). -/
theorem divByZero_converse_error :
    (∃ msg, Stop.ub "division by zero" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 2 ∧ Interp.steps k divByZeroMInit = .ok mRet ∧
      ReturnRel divRemI8 ctxI8_3 s' v mRet ∧
      ReachesRet (mirCallTree divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error divRemI8_inFragment divRemI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩] (by decide) divByZeroMInit rfl rfl rfl
    divByZero_minirust_direct

/-- Signed division overflow UB (`i8::MIN / -1`, bits `128` and `255`). -/
def divMinNeg1S0 : MachineState := initMachineState divRemI8 [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩]
def divMinNeg1MInit : Mach :=
  machineWithCtx ctxI8_3 divRemI8 divRemI8Fn divMinNeg1S0.frame.locals divRemI8Fn.start

theorem divMinNeg1_anneal_ub :
    ∃ tr u, Reaches (mirCallTree divRemI8 [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound divRemI8 5 _ (by decide)

theorem divMinNeg1_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n divMinNeg1MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := divMinNeg1_anneal_ub
  exact mirCall_ub divRemI8_inFragment divRemI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩] (by decide) divMinNeg1MInit rfl rfl rfl hr hf

theorem divMinNeg1_minirust_direct :
    Interp.steps 2 divMinNeg1MInit = .error (.ub "overflow in division") := rfl

/-- Standalone `Rem` body (`_0 = Rem(copy _1, copy _2); return`) so `Rem`'s own
zero-divisor and `i8::MIN % -1` UB branches execute without `Div` faulting first. -/
def remOnlyI8 : CapturedMir where
  defPath := "witness::rem_only_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .rem (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem remOnlyI8_inFragment : inFragment remOnlyI8 = true := by decide

def remOnlyI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Rem) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem remOnlyI8_translate : translateFn remOnlyI8 = some remOnlyI8Fn := rfl

def remByZeroS0 : MachineState := initMachineState remOnlyI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]
def remByZeroMInit : Mach :=
  machineWithCtx ctxI8_3 remOnlyI8 remOnlyI8Fn remByZeroS0.frame.locals remOnlyI8Fn.start

theorem remByZero_anneal_ub :
    ∃ tr u, Reaches (mirCallTree remOnlyI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound remOnlyI8 5 _ (by decide)

theorem remByZero_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n remByZeroMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := remByZero_anneal_ub
  exact mirCall_ub remOnlyI8_inFragment remOnlyI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩] (by decide) remByZeroMInit rfl rfl rfl hr hf

theorem remByZero_minirust_direct :
    Interp.steps 2 remByZeroMInit = .error (.ub "modulus of remainder is zero") := rfl

def remMinNeg1S0 : MachineState := initMachineState remOnlyI8 [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩]
def remMinNeg1MInit : Mach :=
  machineWithCtx ctxI8_3 remOnlyI8 remOnlyI8Fn remMinNeg1S0.frame.locals remOnlyI8Fn.start

theorem remMinNeg1_anneal_ub :
    ∃ tr u, Reaches (mirCallTree remOnlyI8 [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound remOnlyI8 5 _ (by decide)

theorem remMinNeg1_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n remMinNeg1MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := remMinNeg1_anneal_ub
  exact mirCall_ub remOnlyI8_inFragment remOnlyI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩] (by decide) remMinNeg1MInit rfl rfl rfl hr hf

theorem remMinNeg1_minirust_direct :
    Interp.steps 2 remMinNeg1MInit = .error (.ub "overflow in remainder") := rfl

/-! ## Unchecked arithmetic (`MulUnchecked`, `SubUnchecked`, `AddUnchecked`) -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
unsafe fn unchecked_arith_i8(a: i8, b: i8) -> i8 {
    let p = a.unchecked_mul(b);   // bb0: _0 = MulUnchecked(copy _1, copy _2)
    let d = p.unchecked_sub(b);   //      _0 = SubUnchecked(copy _0, copy _2)
    d.unchecked_add(127)          //      _0 = AddUnchecked(copy _0, const 127i8); return
}
```
Exercises all three unchecked operators both succeeding at the `i8::MIN`
boundary and faulting with UB on signed overflow. -/
def uncheckedArithI8 : CapturedMir where
  defPath := "witness::unchecked_arith_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .mulUnchecked (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.binaryOp .subUnchecked (.copy (local_ 0)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.binaryOp .addUnchecked (.copy (local_ 0)) (constI8 127)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem uncheckedArithI8_inFragment : inFragment uncheckedArithI8 = true := by decide

def uncheckedArithI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .MulUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .SubUnchecked) (.Load (.Local (localName 0))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .AddUnchecked) (.Load (.Local (localName 0))) (.Constant (.Int 127) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uncheckedArithI8_translate : translateFn uncheckedArithI8 = some uncheckedArithI8Fn := rfl

/-- Boundary success `(64i8, -2i8)` (bits `64`, `254`):
`64 * -2 = -128` (`i8::MIN`), `-128 - (-2) = -126`, `-126 + 127 = 1`. -/
def uncheckedOkS0 : MachineState := initMachineState uncheckedArithI8 [.scalar ⟨64, 1⟩, .scalar ⟨254, 1⟩]
def uncheckedOkMInit : Mach :=
  machineWithCtx ctxI8_3 uncheckedArithI8 uncheckedArithI8Fn uncheckedOkS0.frame.locals uncheckedArithI8Fn.start

theorem uncheckedOk_anneal_ret :
    ReachesRet (mirCallTree uncheckedArithI8 [.scalar ⟨64, 1⟩, .scalar ⟨254, 1⟩]) []
      (.normal (.scalar ⟨1, 1⟩, uncheckedOkS0.memory)) :=
  runA_sound uncheckedArithI8 10 _ _ _ rfl

theorem uncheckedOk_noUB :
    MirNoUBTree (mirCallTree uncheckedArithI8 [.scalar ⟨64, 1⟩, .scalar ⟨254, 1⟩]) :=
  runA_noUB uncheckedArithI8 10 _ _ _ rfl

theorem uncheckedOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n uncheckedOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 1 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret uncheckedArithI8_inFragment uncheckedArithI8_translate ctxI8_3 (ctxI8_ok3 rfl)
      [.scalar ⟨64, 1⟩, .scalar ⟨254, 1⟩] (by decide) uncheckedOkMInit rfl rfl rfl uncheckedOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [uncheckedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem uncheckedOk_minirust_direct :
    (Interp.steps 5 uncheckedOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 1 }, [1]) := rfl

/-- `MulUnchecked` overflow `(-64i8, -2i8)` (`+128` overflows `i8`). -/
def uncheckedMulUbS0 : MachineState := initMachineState uncheckedArithI8 [.scalar ⟨192, 1⟩, .scalar ⟨254, 1⟩]
def uncheckedMulUbMInit : Mach :=
  machineWithCtx ctxI8_3 uncheckedArithI8 uncheckedArithI8Fn uncheckedMulUbS0.frame.locals uncheckedArithI8Fn.start

theorem uncheckedMulUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨192, 1⟩, .scalar ⟨254, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uncheckedArithI8 5 _ (by decide)

theorem uncheckedMulUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uncheckedMulUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uncheckedMulUb_anneal_ub
  exact mirCall_ub uncheckedArithI8_inFragment uncheckedArithI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨192, 1⟩, .scalar ⟨254, 1⟩] (by decide) uncheckedMulUbMInit rfl rfl rfl hr hf

theorem uncheckedMulUb_minirust_direct :
    Interp.steps 2 uncheckedMulUbMInit = .error (.ub "overflow in unchecked mul") := rfl

/-- `SubUnchecked` overflow `(-64i8, 2i8)` (`-64 * 2 = -128` succeeds, then
`-128 - 2 = -130` overflows `i8`). -/
def uncheckedSubUbS0 : MachineState := initMachineState uncheckedArithI8 [.scalar ⟨192, 1⟩, .scalar ⟨2, 1⟩]
def uncheckedSubUbMInit : Mach :=
  machineWithCtx ctxI8_3 uncheckedArithI8 uncheckedArithI8Fn uncheckedSubUbS0.frame.locals uncheckedArithI8Fn.start

theorem uncheckedSubUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨192, 1⟩, .scalar ⟨2, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uncheckedArithI8 5 _ (by decide)

theorem uncheckedSubUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uncheckedSubUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uncheckedSubUb_anneal_ub
  exact mirCall_ub uncheckedArithI8_inFragment uncheckedArithI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨192, 1⟩, .scalar ⟨2, 1⟩] (by decide) uncheckedSubUbMInit rfl rfl rfl hr hf

theorem uncheckedSubUb_minirust_direct :
    Interp.steps 3 uncheckedSubUbMInit = .error (.ub "overflow in unchecked sub") := rfl

/-- `AddUnchecked` overflow `(10i8, 2i8)` (`10 * 2 = 20`, `20 - 2 = 18`, then
`18 + 127 = 145` overflows `i8`), plus a witness of `mirCall_outcome`. -/
def uncheckedAddUbS0 : MachineState := initMachineState uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]
def uncheckedAddUbMInit : Mach :=
  machineWithCtx ctxI8_3 uncheckedArithI8 uncheckedArithI8Fn uncheckedAddUbS0.frame.locals uncheckedArithI8Fn.start

theorem uncheckedAddUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uncheckedArithI8 5 _ (by decide)

theorem uncheckedAddUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uncheckedAddUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uncheckedAddUb_anneal_ub
  exact mirCall_ub uncheckedArithI8_inFragment uncheckedArithI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩] (by decide) uncheckedAddUbMInit rfl rfl rfl hr hf

theorem uncheckedAddUb_minirust_direct :
    Interp.steps 4 uncheckedAddUbMInit = .error (.ub "overflow in unchecked add") := rfl

theorem uncheckedAddUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen uncheckedArithI8 + n) uncheckedAddUbMInit = .ok m' ∧
      StateRel uncheckedArithI8 uncheckedArithI8Fn ctxI8_3 s' m' ∧
      Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]) tr
        (mirTree uncheckedArithI8 s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen uncheckedArithI8 + n ∧
      Interp.steps k uncheckedAddUbMInit = .ok mRet ∧
      ReturnRel uncheckedArithI8 ctxI8_3 s' v mRet ∧
      ReachesRet (mirCallTree uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen uncheckedArithI8 + n) uncheckedAddUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome uncheckedArithI8_inFragment uncheckedArithI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩] (by decide) uncheckedAddUbMInit rfl rfl rfl n

/-! ## Observable-step diverging loop (`branchSpinLoop`) -/

/-- MIR (`Runtime(PostCleanup)`) of a conditional loop
```rust
fn branch_spin_loop(x: u32) -> u32 {
    while x != 0 {}
    x
}
```
Unlike `spinLoop`, every iteration executes a `switchInt` terminator and
emits a visible `.emit` branch event in Anneal's interaction tree, exercising
`treeSafe_of_step_inv` and `noRet_of_step_inv`. -/
def branchSpinLoop : CapturedMir where
  defPath := "witness::branch_spin_loop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1))
        { branches := [(0, 1)], otherwise := 0 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem branchSpinLoop_inFragment : inFragment branchSpinLoop = true := by decide

def branchSpinLoopFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 1)]⟩ (bbName 0), .Regular⟩),
    (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 2
  implicit_writes := true

theorem branchSpinLoop_translate : translateFn branchSpinLoop = some branchSpinLoopFn := rfl

def branchSpinLoop1S0 : MachineState := initMachineState branchSpinLoop [.scalar ⟨1, 4⟩]
def branchSpinLoop1MInit : Mach :=
  machine branchSpinLoop branchSpinLoopFn branchSpinLoop1S0.frame.locals branchSpinLoopFn.start

theorem branchSpinLoop1_step_self :
    ∀ s, s = branchSpinLoop1S0 → SafeContinue branchSpinLoop (· = branchSpinLoop1S0) s := by
  rintro s rfl
  exact Or.inr ⟨.event 1, _, branchSpinLoop1S0, rfl, rfl, rfl⟩

/-- `branchSpinLoop(1)` is UB-free across its infinite interaction tree, even
though every iteration emits a visible `.emit (.event 1)` branch observation. -/
theorem branchSpinLoop1_noUB : MirNoUBTree (mirCallTree branchSpinLoop [.scalar ⟨1, 4⟩]) :=
  treeSafe_of_step_inv branchSpinLoop1_step_self rfl

/-- `branchSpinLoop(1)` never reaches a return outcome along any trace. -/
theorem branchSpinLoop1_diverges (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet (mirCallTree branchSpinLoop [.scalar ⟨1, 4⟩]) tr o :=
  noRet_of_step_inv branchSpinLoop1_step_self rfl tr o

/-- Therefore MiniRust started at `f.start` steps forever in `StateRel` with an
Anneal state reachable via `Reaches` along the growing branch-observation trace. -/
theorem branchSpinLoop1_minirust_diverges_rel (n : Nat) :
    ∃ s' m' tr, Interp.steps (initLen branchSpinLoop + n) branchSpinLoop1MInit = .ok m' ∧
      StateRel branchSpinLoop branchSpinLoopFn ctx0 s' m' ∧
      Reaches (mirCallTree branchSpinLoop [.scalar ⟨1, 4⟩]) tr (mirTree branchSpinLoop s') :=
  mirCall_diverges_rel branchSpinLoop_inFragment branchSpinLoop_translate ctx0 (ctx0_ok2 rfl)
    [.scalar ⟨1, 4⟩] (by decide) branchSpinLoop1MInit rfl rfl rfl
    branchSpinLoop1_noUB branchSpinLoop1_diverges n

/-! ## Wrapping and unchecked shifts (`Shl`, `Shr`, `ShlUnchecked`, `ShrUnchecked`) -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn shift_i8(mut a: i8, s: i8) -> i8 {
    a = a >> -6i8;              // bb0: _1 = Shr(copy _1, const -6i8)   -- (-6).rem_euclid(8) = 2
    a = a << -7i8;              //      _1 = Shl(copy _1, const -7i8)   -- (-7).rem_euclid(8) = 1
    a = unchecked_shr(a, s);    //      _1 = ShrUnchecked(copy _1, copy _2)
    unchecked_shl(a, s)         //      _0 = ShlUnchecked(copy _1, copy _2); return
}
```
where `-6i8` has bit pattern `250` and `-7i8` has bit pattern `249`. -/
def shiftI8 : CapturedMir where
  defPath := "witness::shift_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [{
    statements := [
      mkStmt (.assign (local_ 1) (.binaryOp .shr (.copy (local_ 1)) (constI8 250))),
      mkStmt (.assign (local_ 1) (.binaryOp .shl (.copy (local_ 1)) (constI8 249))),
      mkStmt (.assign (local_ 1) (.binaryOp .shrUnchecked (.copy (local_ 1)) (.copy (local_ 2)))),
      mkStmt (.assign (local_ 0) (.binaryOp .shlUnchecked (.copy (local_ 1)) (.copy (local_ 2))))],
    terminator := mkTerm .return_,
    isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem shiftI8_inFragment : inFragment shiftI8 = true := by decide

def shiftI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int (-6)) (.Int i8))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Shl) (.Load (.Local (localName 1))) (.Constant (.Int (-7)) (.Int i8))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .ShrUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .ShlUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem shiftI8_translate : translateFn shiftI8 = some shiftI8Fn := rfl

/-- Input `(-64i8, 3i8)` (bits `192`, `3`):
`-64i8 >> -6i8 = -64i8 >> 2 = -16i8` (bits `240`),
`-16i8 << -7i8 = -16i8 << 1 = -32i8` (bits `224`),
`unchecked_shr(-32i8, 3i8) = -4i8` (bits `252`),
`unchecked_shl(-4i8, 3i8) = -32i8` (bits `224`). -/
def shiftOkS0 : MachineState := initMachineState shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨3, 1⟩]
def shiftOkMInit : Mach :=
  machineWithCtx ctxI8_3 shiftI8 shiftI8Fn shiftOkS0.frame.locals shiftI8Fn.start

theorem shiftOk_anneal_ret :
    ReachesRet (mirCallTree shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨3, 1⟩]) []
      (.normal (.scalar ⟨224, 1⟩, shiftOkS0.memory)) :=
  runA_sound shiftI8 10 _ _ _ rfl

theorem shiftOk_noUB :
    MirNoUBTree (mirCallTree shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨3, 1⟩]) :=
  runA_noUB shiftI8 10 _ _ _ rfl

theorem shiftOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n shiftOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 224 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret shiftI8_inFragment shiftI8_translate ctxI8_3 (ctxI8_ok3 rfl)
      [.scalar ⟨192, 1⟩, .scalar ⟨3, 1⟩] (by decide) shiftOkMInit rfl rfl rfl shiftOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [shiftI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem shiftOk_minirust_direct :
    (Interp.steps 6 shiftOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 224 }, [1]) := rfl

/-- `ShrUnchecked` UB when `s = 8i8` (`s >= bits`). -/
def shrUncheckedGe8UbS0 : MachineState := initMachineState shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨8, 1⟩]
def shrUncheckedGe8UbMInit : Mach :=
  machineWithCtx ctxI8_3 shiftI8 shiftI8Fn shrUncheckedGe8UbS0.frame.locals shiftI8Fn.start

theorem shrUncheckedGe8Ub_anneal_ub :
    ∃ tr u, Reaches (mirCallTree shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨8, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound shiftI8 6 _ (by decide)

theorem shrUncheckedGe8Ub_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n shrUncheckedGe8UbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := shrUncheckedGe8Ub_anneal_ub
  exact mirCall_ub shiftI8_inFragment shiftI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨192, 1⟩, .scalar ⟨8, 1⟩] (by decide) shrUncheckedGe8UbMInit rfl rfl rfl hr hf

theorem shrUncheckedGe8Ub_minirust_direct :
    Interp.steps 4 shrUncheckedGe8UbMInit = .error (.ub "overflow in unchecked shift") := rfl

/-- `ShrUnchecked` UB when `s = -1i8` (bits `255`, `s < 0`). -/
def shrUncheckedNegUbS0 : MachineState := initMachineState shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨255, 1⟩]
def shrUncheckedNegUbMInit : Mach :=
  machineWithCtx ctxI8_3 shiftI8 shiftI8Fn shrUncheckedNegUbS0.frame.locals shiftI8Fn.start

theorem shrUncheckedNegUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨255, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound shiftI8 6 _ (by decide)

theorem shrUncheckedNegUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n shrUncheckedNegUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := shrUncheckedNegUb_anneal_ub
  exact mirCall_ub shiftI8_inFragment shiftI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨192, 1⟩, .scalar ⟨255, 1⟩] (by decide) shrUncheckedNegUbMInit rfl rfl rfl hr hf

theorem shrUncheckedNegUb_minirust_direct :
    Interp.steps 4 shrUncheckedNegUbMInit = .error (.ub "overflow in unchecked shift") := rfl

/-- Standalone `ShlUnchecked` body `fn shl_unchecked_i8(a: i8, s: i8) -> i8 { unchecked_shl(a, s) }`
to witness both `s >= 8` and `s < 0` UB on `ShlUnchecked`. -/
def shlUncheckedI8 : CapturedMir where
  defPath := "witness::shl_unchecked_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [{
    statements := [
      mkStmt (.assign (local_ 0) (.binaryOp .shlUnchecked (.copy (local_ 1)) (.copy (local_ 2))))],
    terminator := mkTerm .return_,
    isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem shlUncheckedI8_inFragment : inFragment shlUncheckedI8 = true := by decide

def shlUncheckedI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .ShlUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem shlUncheckedI8_translate : translateFn shlUncheckedI8 = some shlUncheckedI8Fn := rfl

def shlUncheckedGe8UbS0 : MachineState := initMachineState shlUncheckedI8 [.scalar ⟨1, 1⟩, .scalar ⟨8, 1⟩]
def shlUncheckedGe8UbMInit : Mach :=
  machineWithCtx ctxI8_3 shlUncheckedI8 shlUncheckedI8Fn shlUncheckedGe8UbS0.frame.locals shlUncheckedI8Fn.start

theorem shlUncheckedGe8Ub_anneal_ub :
    ∃ tr u, Reaches (mirCallTree shlUncheckedI8 [.scalar ⟨1, 1⟩, .scalar ⟨8, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound shlUncheckedI8 5 _ (by decide)

theorem shlUncheckedGe8Ub_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n shlUncheckedGe8UbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := shlUncheckedGe8Ub_anneal_ub
  exact mirCall_ub shlUncheckedI8_inFragment shlUncheckedI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨1, 1⟩, .scalar ⟨8, 1⟩] (by decide) shlUncheckedGe8UbMInit rfl rfl rfl hr hf

theorem shlUncheckedGe8Ub_minirust_direct :
    Interp.steps 2 shlUncheckedGe8UbMInit = .error (.ub "overflow in unchecked shift") := rfl

def shlUncheckedNegUbS0 : MachineState := initMachineState shlUncheckedI8 [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩]
def shlUncheckedNegUbMInit : Mach :=
  machineWithCtx ctxI8_3 shlUncheckedI8 shlUncheckedI8Fn shlUncheckedNegUbS0.frame.locals shlUncheckedI8Fn.start

theorem shlUncheckedNegUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree shlUncheckedI8 [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound shlUncheckedI8 5 _ (by decide)

theorem shlUncheckedNegUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n shlUncheckedNegUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := shlUncheckedNegUb_anneal_ub
  exact mirCall_ub shlUncheckedI8_inFragment shlUncheckedI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩] (by decide) shlUncheckedNegUbMInit rfl rfl rfl hr hf

theorem shlUncheckedNegUb_minirust_direct :
    Interp.steps 2 shlUncheckedNegUbMInit = .error (.ub "overflow in unchecked shift") := rfl

/-! ## Signed two's-complement bitwise operators (`BitAnd`, `BitOr`, `BitXor`) and `CountOnes` -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn bitwise_i8(mut a: i8, b: i8) -> i8 {
    a = a & b;        // bb0: _1 = BitAnd(copy _1, copy _2)
    a = a | -123i8;   //      _1 = BitOr(copy _1, const -123i8)
    a ^ -59i8         //      _0 = BitXor(copy _1, const -59i8); return
}
```
where `-123i8` has bit pattern `133` (`0x85`) and `-59i8` has bit pattern `197`
(`0xC5`). -/
def bitwiseI8 : CapturedMir where
  defPath := "witness::bitwise_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [{
    statements := [
      mkStmt (.assign (local_ 1) (.binaryOp .bitAnd (.copy (local_ 1)) (.copy (local_ 2)))),
      mkStmt (.assign (local_ 1) (.binaryOp .bitOr (.copy (local_ 1)) (constI8 133))),
      mkStmt (.assign (local_ 0) (.binaryOp .bitXor (.copy (local_ 1)) (constI8 197)))],
    terminator := mkTerm .return_,
    isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem bitwiseI8_inFragment : inFragment bitwiseI8 = true := by decide

def bitwiseI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Int .BitAnd) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .BitOr) (.Load (.Local (localName 1))) (.Constant (.Int (-123)) (.Int i8))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .BitXor) (.Load (.Local (localName 1))) (.Constant (.Int (-59)) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem bitwiseI8_translate : translateFn bitwiseI8 = some bitwiseI8Fn := rfl

/-- Input `(-86i8, -15i8)` (bits `170 = 0xAA`, `241 = 0xF1`):
`(-86i8) & (-15i8) = -96i8` (bits `160 = 0xA0`),
`(-96i8) | (-123i8) = -91i8` (bits `165 = 0xA5`),
`(-91i8) ^ (-59i8) = 96i8` (bits `96 = 0x60`, cancelling the infinite leading
two's-complement `1` bits of both negative `libspecr::Int` operands). -/
def bitwiseNegS0 : MachineState := initMachineState bitwiseI8 [.scalar ⟨170, 1⟩, .scalar ⟨241, 1⟩]
def bitwiseNegMInit : Mach :=
  machineWithCtx ctxI8_3 bitwiseI8 bitwiseI8Fn bitwiseNegS0.frame.locals bitwiseI8Fn.start

theorem bitwiseNeg_anneal_ret :
    ReachesRet (mirCallTree bitwiseI8 [.scalar ⟨170, 1⟩, .scalar ⟨241, 1⟩]) []
      (.normal (.scalar ⟨96, 1⟩, bitwiseNegS0.memory)) :=
  runA_sound bitwiseI8 10 _ _ _ rfl

theorem bitwiseNeg_noUB :
    MirNoUBTree (mirCallTree bitwiseI8 [.scalar ⟨170, 1⟩, .scalar ⟨241, 1⟩]) :=
  runA_noUB bitwiseI8 10 _ _ _ rfl

theorem bitwiseNeg_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n bitwiseNegMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 96 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret bitwiseI8_inFragment bitwiseI8_translate ctxI8_3 (ctxI8_ok3 rfl)
      [.scalar ⟨170, 1⟩, .scalar ⟨241, 1⟩] (by decide) bitwiseNegMInit rfl rfl rfl bitwiseNeg_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [bitwiseI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem bitwiseNeg_minirust_direct :
    (Interp.steps 5 bitwiseNegMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 96 }, [1]) := rfl

/-- Direct ground-truth checks of `IntUnOp::CountOnes` (`eval_count_ones`):
`-86i8` (`0b1010_1010` modulo `2^8`) has `4` ones and `-1i8` (`0b1111_1111`
modulo `2^8`) has `8` ones, both returning `u32`. -/
theorem countOnes_neg86_i8 :
    evalUnOp (.Int .CountOnes) (.Int (-86), .Int i8) = .ok (.Int 4, .Int u32) := rfl

theorem countOnes_neg1_i8 :
    evalUnOp (.Int .CountOnes) (.Int (-1), .Int i8) = .ok (.Int 8, .Int u32) := rfl

/-! ## Heterogeneous shifts (`(i8, u32)`, `(i8, i32)`) and constant-discriminant `SwitchInt` -/

def i32Ty : Ty := { kind := .int .i32, layoutIdx := 0 }
def i32Decl : LocalDecl := { mutability := .mut, ty := i32Ty, debugName := none }
def i32 : Gen.IntType := ⟨.Signed, ⟨4⟩⟩

def i32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiHeteroShift : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct },
             { layout := i32Layout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_hetero {body : CapturedMir}
    (h : body.localDecls = [i8Decl, i8Decl, i32Decl]) : CtxOk body ctxI8_3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn hetero_shift_switch(mut x: i8, k: i32) -> i8 {
    x = x >> 258u32;                // bb0: _1 = Shr(copy _1, const 258u32)   -- (i8, u32)
    x = x << 257u32;                //      _1 = Shl(copy _1, const 257u32)   -- (i8, u32)
    match -1i8 {                    //      switchInt(const -1i8) -> [-1i8: bb1, otherwise: bb2]
        -1 => {
            x = unchecked_shr(x, k); // bb1: _1 = ShrUnchecked(copy _1, copy _2) -- (i8, i32)
            unchecked_shl(x, k)      //      _0 = ShlUnchecked(copy _1, copy _2); return
        }
        _ => unreachable!(),        // bb2: unreachable
    }
}
```
exercising unequal `(lhs, rhs)` shift operand types (`(i8, u32)` and `(i8, i32)`)
together with a constant-operand signed `SwitchInt` scrutinee. -/
def heteroShiftSwitch : CapturedMir where
  defPath := "witness::hetero_shift_switch"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.binaryOp .shr (.copy (local_ 1)) (constU32 258))),
        mkStmt (.assign (local_ 1) (.binaryOp .shl (.copy (local_ 1)) (constU32 257)))],
      terminator := mkTerm (.switchInt (constI8 255)
        { branches := [(255, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.binaryOp .shrUnchecked (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.binaryOp .shlUnchecked (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [], terminator := mkTerm .unreachable, isCleanup := false }]
  fnAbi := fnAbiHeteroShift
  layouts := emptyLayoutTable
  allocations := []

theorem heteroShiftSwitch_inFragment : inFragment heteroShiftSwitch = true := by decide

def heteroShiftSwitchFn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int 258) (.Int u32))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Shl) (.Load (.Local (localName 1))) (.Constant (.Int 257) (.Int u32)))],
      .Switch (.Constant (.Int (-1)) (.Int i8)) ⟨[(-1, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Int .ShrUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .ShlUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Unreachable, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem heteroShiftSwitch_translate : translateFn heteroShiftSwitch = some heteroShiftSwitchFn := rfl

/-- Input `(-64i8, 3i32)` (bits `192`, `3`):
`-64i8 >> 258u32 = -64i8 >> 2 = -16i8` (bits `240`, with `258 >= 256`),
`-16i8 << 257u32 = -16i8 << 1 = -32i8` (bits `224`, with `257 >= 256`),
`switchInt(const -1i8)` takes the `-1` arm to `bb1`,
`unchecked_shr(-32i8, 3i32) = -4i8` (bits `252`), and
`unchecked_shl(-4i8, 3i32) = -32i8` (bits `224`). -/
def heteroShiftOkS0 : MachineState :=
  initMachineState heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨3, 4⟩]
def heteroShiftOkMInit : Mach :=
  machineWithCtx ctxI8_3 heteroShiftSwitch heteroShiftSwitchFn
    heteroShiftOkS0.frame.locals heteroShiftSwitchFn.start

def heteroShiftOkTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 255))), PUnit.unit⟩]

theorem heteroShiftOk_anneal_ret :
    ReachesRet (mirCallTree heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨3, 4⟩])
      heteroShiftOkTrace (.normal (.scalar ⟨224, 1⟩, heteroShiftOkS0.memory)) :=
  runA_sound heteroShiftSwitch 10 _ _ _ rfl

theorem heteroShiftOk_noUB :
    MirNoUBTree (mirCallTree heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨3, 4⟩]) :=
  runA_noUB heteroShiftSwitch 10 _ _ _ rfl

theorem heteroShiftOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n heteroShiftOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 224 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret heteroShiftSwitch_inFragment heteroShiftSwitch_translate ctxI8_3
      (ctxI8_ok_hetero rfl) [.scalar ⟨192, 1⟩, .scalar ⟨3, 4⟩] (by decide)
      heteroShiftOkMInit rfl rfl rfl heteroShiftOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [heteroShiftSwitch] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem heteroShiftOk_minirust_direct :
    (Interp.steps 7 heteroShiftOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 224 }, [1]) := rfl

/-- Heterogeneous `ShrUnchecked(i8, i32)` UB when `k = 8i32`: `8 < 32 = i32::BITS`
(in bounds for the RHS type `i32`), but `8 >= 8 = i8::BITS` (out of bounds for
the LHS type `i8`). -/
def heteroShrGe8UbS0 : MachineState :=
  initMachineState heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨8, 4⟩]
def heteroShrGe8UbMInit : Mach :=
  machineWithCtx ctxI8_3 heteroShiftSwitch heteroShiftSwitchFn
    heteroShrGe8UbS0.frame.locals heteroShiftSwitchFn.start

theorem heteroShrGe8Ub_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨8, 4⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound heteroShiftSwitch 8 _ (by decide)

theorem heteroShrGe8Ub_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n heteroShrGe8UbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := heteroShrGe8Ub_anneal_ub
  exact mirCall_ub heteroShiftSwitch_inFragment heteroShiftSwitch_translate ctxI8_3
    (ctxI8_ok_hetero rfl) [.scalar ⟨192, 1⟩, .scalar ⟨8, 4⟩] (by decide)
    heteroShrGe8UbMInit rfl rfl rfl hr hf

theorem heteroShrGe8Ub_minirust_direct :
    Interp.steps 5 heteroShrGe8UbMInit = .error (.ub "overflow in unchecked shift") := rfl

/-- Heterogeneous `ShrUnchecked(i8, i32)` UB when `k = -1i32` (bits `4294967295`
in 32-bit `i32`, negative `< 0`). -/
def heteroShrNegUbS0 : MachineState :=
  initMachineState heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨4294967295, 4⟩]
def heteroShrNegUbMInit : Mach :=
  machineWithCtx ctxI8_3 heteroShiftSwitch heteroShiftSwitchFn
    heteroShrNegUbS0.frame.locals heteroShiftSwitchFn.start

theorem heteroShrNegUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨4294967295, 4⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound heteroShiftSwitch 8 _ (by decide)

theorem heteroShrNegUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n heteroShrNegUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := heteroShrNegUb_anneal_ub
  exact mirCall_ub heteroShiftSwitch_inFragment heteroShiftSwitch_translate ctxI8_3
    (ctxI8_ok_hetero rfl) [.scalar ⟨192, 1⟩, .scalar ⟨4294967295, 4⟩] (by decide)
    heteroShrNegUbMInit rfl rfl rfl hr hf

theorem heteroShrNegUb_minirust_direct :
    Interp.steps 5 heteroShrNegUbMInit = .error (.ub "overflow in unchecked shift") := rfl

/-! ## Uninitialized-operand UB (`BinaryOp`, `UnaryOp`, `SwitchInt`) and `IntBinOp::DivExact` -/

/-- Direct ground-truth checks of `IntBinOp::DivExact` (`spec/lang/step/operators.md`)
across all four outcomes on `i8`:
* exact division `-6i8 / 3i8 = -2i8`,
* non-zero remainder UB on `-7i8 / 3i8`,
* division by zero UB on `-6i8 / 0i8`, and
* signed overflow UB on `i8::MIN / -1i8 = -128 / -1`. -/
theorem divExact_ok_i8 :
    evalBinOp (.Int .DivExact) (.Int (-6), .Int i8) (.Int 3, .Int i8) =
      .ok (.Int (-2), .Int i8) := rfl

theorem divExact_rem_ub_i8 :
    evalBinOp (.Int .DivExact) (.Int (-7), .Int i8) (.Int 3, .Int i8) =
      .error (.ub "non-zero remainder in exact division") := rfl

theorem divExact_zero_ub_i8 :
    evalBinOp (.Int .DivExact) (.Int (-6), .Int i8) (.Int 0, .Int i8) =
      .error (.ub "division by zero") := rfl

theorem divExact_min_neg1_ub_i8 :
    evalBinOp (.Int .DivExact) (.Int (-128), .Int i8) (.Int (-1), .Int i8) =
      .error (.ub "overflow in division") := rfl

/-- MIR (`Runtime(PostCleanup)`) of a function that reads an uninitialized local
(`copy _0` before `_0` has been written) in three different positions depending
on `x`:
* `x == 0` (`bb1`): `_0 = Add(copy _0, copy _1)` (uninitialized operand in `BinaryOp`),
* `x == 1` (`bb2`): `_0 = Neg(copy _0)` (uninitialized operand in `UnaryOp`),
* otherwise (`bb3`): `switchInt(copy _0)` (uninitialized scrutinee in `SwitchInt`). -/
def uninitOperandUb : CapturedMir where
  defPath := "witness::uninit_operand_ub"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1))
        { branches := [(0, 1), (1, 2)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 0)) (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 0))
        { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem uninitOperandUb_inFragment : inFragment uninitOperandUb = true := by decide

def uninitOperandUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[],
      .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 1), (1, bbName 2)]⟩ (bbName 3),
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0))) (.Load (.Local (localName 1))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0)) (.UnOp (.Int .Neg) (.Load (.Local (localName 0))))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[],
      .Switch (.Load (.Local (localName 0))) ⟨[(0, bbName 1)]⟩ (bbName 2),
      .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem uninitOperandUb_translate : translateFn uninitOperandUb = some uninitOperandUbFn := rfl

/-- `x = 0i8`: `bb1` reads uninitialized `_0` in `BinaryOp(Add, copy _0, copy _1)`. -/
def uninitBinOpUbS0 : MachineState := initMachineState uninitOperandUb [.scalar ⟨0, 1⟩]
def uninitBinOpUbMInit : Mach :=
  machineWithCtx ctxI8 uninitOperandUb uninitOperandUbFn
    uninitBinOpUbS0.frame.locals uninitOperandUbFn.start

theorem uninitBinOpUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitOperandUb [.scalar ⟨0, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitOperandUb 6 _ (by decide)

theorem uninitBinOpUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBinOpUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBinOpUb_anneal_ub
  exact mirCall_ub uninitOperandUb_inFragment uninitOperandUb_translate ctxI8 (ctxI8_ok2 rfl)
    [.scalar ⟨0, 1⟩] (by decide) uninitBinOpUbMInit rfl rfl rfl hr hf

theorem uninitBinOpUb_minirust_direct :
    Interp.steps 3 uninitBinOpUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- `x = 1i8`: `bb2` reads uninitialized `_0` in `UnaryOp(Neg, copy _0)`. -/
def uninitUnOpUbS0 : MachineState := initMachineState uninitOperandUb [.scalar ⟨1, 1⟩]
def uninitUnOpUbMInit : Mach :=
  machineWithCtx ctxI8 uninitOperandUb uninitOperandUbFn
    uninitUnOpUbS0.frame.locals uninitOperandUbFn.start

theorem uninitUnOpUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitOperandUb [.scalar ⟨1, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitOperandUb 6 _ (by decide)

theorem uninitUnOpUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitUnOpUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitUnOpUb_anneal_ub
  exact mirCall_ub uninitOperandUb_inFragment uninitOperandUb_translate ctxI8 (ctxI8_ok2 rfl)
    [.scalar ⟨1, 1⟩] (by decide) uninitUnOpUbMInit rfl rfl rfl hr hf

theorem uninitUnOpUb_minirust_direct :
    Interp.steps 3 uninitUnOpUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- `x = 2i8`: `bb3` reads uninitialized `_0` as the scrutinee of `SwitchInt(copy _0)`. -/
def uninitSwitchUbS0 : MachineState := initMachineState uninitOperandUb [.scalar ⟨2, 1⟩]
def uninitSwitchUbMInit : Mach :=
  machineWithCtx ctxI8 uninitOperandUb uninitOperandUbFn
    uninitSwitchUbS0.frame.locals uninitOperandUbFn.start

theorem uninitSwitchUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitOperandUb [.scalar ⟨2, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitOperandUb 6 _ (by decide)

theorem uninitSwitchUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitSwitchUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitSwitchUb_anneal_ub
  exact mirCall_ub uninitOperandUb_inFragment uninitOperandUb_translate ctxI8 (ctxI8_ok2 rfl)
    [.scalar ⟨2, 1⟩] (by decide) uninitSwitchUbMInit rfl rfl rfl hr hf

theorem uninitSwitchUb_minirust_direct :
    Interp.steps 3 uninitSwitchUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

theorem uninitSwitchUb_converse_error :
    (∃ msg, Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree uninitOperandUb [.scalar ⟨2, 1⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 3 ∧ Interp.steps k uninitSwitchUbMInit = .ok mRet ∧
      ReturnRel uninitOperandUb ctxI8 s' v mRet ∧
      ReachesRet (mirCallTree uninitOperandUb [.scalar ⟨2, 1⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error uninitOperandUb_inFragment uninitOperandUb_translate ctxI8 (ctxI8_ok2 rfl)
    [.scalar ⟨2, 1⟩] (by decide) uninitSwitchUbMInit rfl rfl rfl uninitSwitchUb_minirust_direct

/-! ## Booleans: comparisons, `!`, `switchInt` on `bool`, and `bool` returns -/

def boolTy : Ty := { kind := .bool, layoutIdx := 0 }
def boolDecl : LocalDecl := { mutability := .mut, ty := boolTy, debugName := none }
def constBool (b : Bool) : Operand :=
  .constant { ty := boolTy, val := .scalar (.int ⟨if b then 1 else 0, 1⟩) }
def u8TyW : Ty := { kind := .uint .u8, layoutIdx := 0 }
def u8Decl : LocalDecl := { mutability := .mut, ty := u8TyW, debugName := none }
def constU8 (n : Nat) : Operand := .constant { ty := u8TyW, val := .scalar (.int ⟨n, 1⟩) }
def u8 : Gen.IntType := ⟨.Unsigned, ⟨1⟩⟩

/-- The layout of `bool` (one byte, alignment one); like the other ABI
layouts in this module, the fragment never reads it. -/
def boolLayout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiCmpNot : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct }, { layout := i8Layout, mode := .direct },
      { layout := boolLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- The callee's locals live at addresses `128`, `256`, `384`, and `512`. -/
def ctxI8_4 : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8], addrs := [128, 256, 384, 512],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxI8_ok_cmpNot {body : CapturedMir}
    (h : body.localDecls = [i8Decl, i8Decl, i8Decl, boolDecl]) : CtxOk body ctxI8_4 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | 3, hd => simp at hd; subst hd; decide
    | _ + 4, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn cmp_not_switch(x: i8, y: i8, mut b: bool) -> i8 {
    b = x < y;               // bb0: _3 = Lt(copy _1, copy _2)
    b = !b;                  //      _3 = Not(copy _3)
    if b { return y; }       //      switchInt(copy _3) -> [0: bb1, otherwise: bb3]
    b = x == -1;             // bb1: _3 = Eq(copy _1, const -1_i8)
    b = b > false;           //      _3 = Gt(copy _3, const false)
    if b { x } else { y }    //      switchInt(copy _3) -> [0: bb3, otherwise: bb2]
}                            // bb2: _0 = copy _1; return    bb3: _0 = copy _2; return
```
For `(x, y) = (-1, 1)` the signed comparison `-1 < 1` holds, so `!b` is
`false`, the first switch takes `bb1`, `-1 == -1` and `true > false` hold, and
the function returns `x = -1` (bits `255`). Comparing the bit patterns
unsigned (`255 < 1`) would instead return `y`. -/
def cmpNotSwitch : CapturedMir where
  defPath := "witness::cmp_not_switch"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [i8Decl, i8Decl, i8Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .lt (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 3) (.unaryOp .not (.copy (local_ 3))))],
      terminator := mkTerm (.switchInt (.copy (local_ 3)) { branches := [(0, 1)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .eq (.copy (local_ 1)) (constI8 255))),
        mkStmt (.assign (local_ 3) (.binaryOp .gt (.copy (local_ 3)) (constBool false)))],
      terminator := mkTerm (.switchInt (.copy (local_ 3)) { branches := [(0, 3)], otherwise := 2 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCmpNot
  layouts := emptyLayoutTable
  allocations := []

theorem cmpNotSwitch_inFragment : inFragment cmpNotSwitch = true := by decide

/-- The MiniRust function `minimize` produces for `cmpNotSwitch`, spelled out:
the comparisons are `BinOp::Rel`, `!b` is `build::not` (a transmute of
`1u8 - transmute::<u8>(b)` back to `bool`), and each `switchInt` on `b`
switches on `transmute::<u8>(b)`. -/
def cmpNotSwitchFn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, .Bool)]⟩
  args := [localName 1, localName 2, localName 3]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.Rel .Lt) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 3))
        (.UnOp (.Cast (.Transmute .Bool))
          (.BinOp (.Int .Sub) (.Constant (.Int 1) (.Int u8))
            (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 3))))))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 3))))
        ⟨[(0, bbName 1)]⟩ (bbName 3), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.Rel .Eq) (.Load (.Local (localName 1))) (.Constant (.Int (-1)) (.Int i8))),
      .Assign (.Local (localName 3))
        (.BinOp (.Rel .Gt) (.Load (.Local (localName 3))) (.Constant (.Bool false) .Bool))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 3))))
        ⟨[(0, bbName 3)]⟩ (bbName 2), .Regular⟩),
    (bbName 2, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 1)))], .Return, .Regular⟩),
    (bbName 3, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 2)))], .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem cmpNotSwitch_translate : translateFn cmpNotSwitch = some cmpNotSwitchFn := rfl

/-- Input `(x, y, b) = (-1i8, 1i8, false)` (bits `255`, `1`, `0`). -/
def cmpNotNeg1Args : List Value := [.scalar ⟨255, 1⟩, .scalar ⟨1, 1⟩, .scalar ⟨0, 1⟩]
def cmpNotNeg1S0 : MachineState := initMachineState cmpNotSwitch cmpNotNeg1Args
def cmpNotNeg1MInit : Mach :=
  machineWithCtx ctxI8_4 cmpNotSwitch cmpNotSwitchFn cmpNotNeg1S0.frame.locals cmpNotSwitchFn.start

/-- The branch observations: the first `switchInt` sees `!(x < y) = false`
(`0`) and the second sees `(x == -1) > false = true` (`1`). -/
def cmpNotNeg1Trace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩, ⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]

/-- Anneal's semantics returns `x = -1i8` (bits `255`), computed by the
kernel. -/
theorem cmpNotNeg1_anneal_ret :
    ReachesRet (mirCallTree cmpNotSwitch cmpNotNeg1Args) cmpNotNeg1Trace
      (.normal (.scalar ⟨255, 1⟩, cmpNotNeg1S0.memory)) :=
  runA_sound cmpNotSwitch 20 _ _ _ rfl

theorem cmpNotNeg1_noUB : MirNoUBTree (mirCallTree cmpNotSwitch cmpNotNeg1Args) :=
  runA_noUB cmpNotSwitch 20 _ _ _ rfl

/-- Therefore (by `mirCall_ret`) MiniRust, started at `minimize`'s entry
block, returns the bytes of `-1i8` to the caller. -/
theorem cmpNotNeg1_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpNotNeg1MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 255 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpNotSwitch_inFragment cmpNotSwitch_translate ctxI8_4 (ctxI8_ok_cmpNot rfl)
      cmpNotNeg1Args (by decide) cmpNotNeg1MInit rfl rfl rfl cmpNotNeg1_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpNotSwitch] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
/-- The same return, computed directly: 9 MiniRust steps (the entry block,
three steps per block for `bb0` and `bb1`, and two for `bb2`). -/
theorem cmpNotNeg1_minirust_direct :
    (Interp.steps 9 cmpNotNeg1MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 255 }, [1]) := rfl

/-- Input `(x, y, b) = (3i8, 2i8, true)`: `3 < 2` fails, so `!b` is `true` and
the first switch returns `y = 2i8` from `bb3`. -/
def cmpNot3Args : List Value := [.scalar ⟨3, 1⟩, .scalar ⟨2, 1⟩, .scalar ⟨1, 1⟩]
def cmpNot3S0 : MachineState := initMachineState cmpNotSwitch cmpNot3Args
def cmpNot3MInit : Mach :=
  machineWithCtx ctxI8_4 cmpNotSwitch cmpNotSwitchFn cmpNot3S0.frame.locals cmpNotSwitchFn.start

theorem cmpNot3_anneal_ret :
    ReachesRet (mirCallTree cmpNotSwitch cmpNot3Args) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨2, 1⟩, cmpNot3S0.memory)) :=
  runA_sound cmpNotSwitch 20 _ _ _ rfl

theorem cmpNot3_noUB : MirNoUBTree (mirCallTree cmpNotSwitch cmpNot3Args) :=
  runA_noUB cmpNotSwitch 20 _ _ _ rfl

theorem cmpNot3_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpNot3MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 2 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpNotSwitch_inFragment cmpNotSwitch_translate ctxI8_4 (ctxI8_ok_cmpNot rfl)
      cmpNot3Args (by decide) cmpNot3MInit rfl rfl rfl cmpNot3_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpNotSwitch] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem cmpNot3_minirust_direct :
    (Interp.steps 6 cmpNot3MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 2 }, [1]) := rfl

/-! ### Returning a `bool` -/

def fnAbiU8ToBool : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct }, { layout := i8Layout, mode := .direct }],
    ret := { layout := boolLayout, mode := .direct }, conv := .rust, canUnwind := false }

def ctxBool : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8], addrs := [128, 256, 384],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxBool_ok {body : CapturedMir} (h : body.localDecls = [boolDecl, u8Decl, u8Decl]) :
    CtxOk body ctxBool where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn le_ne_ge(x: u8, y: u8) -> bool {
    if x <= y { x != y }      // bb0: _0 = Le(copy _1, copy _2);
                              //      switchInt(copy _0) -> [0: bb2, otherwise: bb1]
                              // bb1: _0 = Ne(copy _1, copy _2); return
    else { x >= 200 }         // bb2: _0 = Ge(copy _1, const 200_u8); return
}
```
whose return place `_0` is a `bool` that also serves as the switch scrutinee,
so the return path loads and stores the result at `Type::Bool`. -/
def leNeGe : CapturedMir where
  defPath := "witness::le_ne_ge"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [boolDecl, u8Decl, u8Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .le (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm (.switchInt (.copy (local_ 0)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .ne (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .ge (.copy (local_ 1)) (constU8 200)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU8ToBool
  layouts := emptyLayoutTable
  allocations := []

theorem leNeGe_inFragment : inFragment leNeGe = true := by decide

def leNeGeFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool), (localName 1, .Int u8), (localName 2, .Int u8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Rel .Le) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 0))))
        ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Rel .Ne) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Rel .Ge) (.Load (.Local (localName 1))) (.Constant (.Int 200) (.Int u8)))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem leNeGe_translate : translateFn leNeGe = some leNeGeFn := rfl

/-- Input `(250u8, 7u8)`: `250 <= 7` fails, and `250 >= 200` returns `true`
(byte `1`). -/
def leNeGe250Args : List Value := [.scalar ⟨250, 1⟩, .scalar ⟨7, 1⟩]
def leNeGe250S0 : MachineState := initMachineState leNeGe leNeGe250Args
def leNeGe250MInit : Mach :=
  machineWithCtx ctxBool leNeGe leNeGeFn leNeGe250S0.frame.locals leNeGeFn.start

theorem leNeGe250_anneal_ret :
    ReachesRet (mirCallTree leNeGe leNeGe250Args) [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, leNeGe250S0.memory)) :=
  runA_sound leNeGe 10 _ _ _ rfl

theorem leNeGe250_noUB : MirNoUBTree (mirCallTree leNeGe leNeGe250Args) :=
  runA_noUB leNeGe 10 _ _ _ rfl

theorem leNeGe250_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n leNeGe250MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 1 } ∧
      m'.threads = [thread1 ctxBool [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret leNeGe_inFragment leNeGe_translate ctxBool (ctxBool_ok rfl)
      leNeGe250Args (by decide) leNeGe250MInit rfl rfl rfl leNeGe250_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [leNeGe] at hd; subst hd
  simp [retPtr, ctxBool] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxBool] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem leNeGe250_minirust_direct :
    (Interp.steps 5 leNeGe250MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 1 }, [1]) := rfl

/-- Input `(5u8, 5u8)`: `5 <= 5` holds, and `5 != 5` returns `false`
(byte `0`). -/
def leNeGe5Args : List Value := [.scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩]
def leNeGe5S0 : MachineState := initMachineState leNeGe leNeGe5Args
def leNeGe5MInit : Mach :=
  machineWithCtx ctxBool leNeGe leNeGeFn leNeGe5S0.frame.locals leNeGeFn.start

theorem leNeGe5_anneal_ret :
    ReachesRet (mirCallTree leNeGe leNeGe5Args) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 1⟩, leNeGe5S0.memory)) :=
  runA_sound leNeGe 10 _ _ _ rfl

theorem leNeGe5_noUB : MirNoUBTree (mirCallTree leNeGe leNeGe5Args) :=
  runA_noUB leNeGe 10 _ _ _ rfl

theorem leNeGe5_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n leNeGe5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 0 } ∧
      m'.threads = [thread1 ctxBool [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret leNeGe_inFragment leNeGe_translate ctxBool (ctxBool_ok rfl)
      leNeGe5Args (by decide) leNeGe5MInit rfl rfl rfl leNeGe5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [leNeGe] at hd; subst hd
  simp [retPtr, ctxBool] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxBool] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem leNeGe5_minirust_direct :
    (Interp.steps 5 leNeGe5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 0 }, [1]) := rfl

/-! ### `bool`-to-integer cast (`CastKind::IntToInt` on `Type::Bool`) -/

def fnAbiBoolToI8 : FnAbi :=
  { args := [{ layout := boolLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_boolCast {body : CapturedMir} (h : body.localDecls = [i8Decl, boolDecl]) :
    CtxOk body ctxI8 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn bool_cast_i8(mut b: bool) -> i8 {
    b = !(b == false);         // bb0: _1 = Eq(copy _1, const false); _1 = Not(copy _1);
                               //      switchInt(copy _1) -> [0: bb2, otherwise: bb1]
    if b { b as i8 }           // bb1: _0 = Cast(IntToInt, copy _1, i8); return
    else { b as i8 }           // bb2: _0 = Cast(IntToInt, copy _1, i8); return
}
```
exercising `Cast(CastKind::IntToInt)` on `Type::Bool` (which `minimize` lowers
by transmuting the `bool` to `u8` and then applying `CastOp::IntToInt`). -/
def boolCastI8 : CapturedMir where
  defPath := "witness::bool_cast_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.binaryOp .eq (.copy (local_ 1)) (constBool false))),
        mkStmt (.assign (local_ 1) (.unaryOp .not (.copy (local_ 1))))],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 1)) i8Ty))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 1)) i8Ty))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiBoolToI8
  layouts := emptyLayoutTable
  allocations := []

theorem boolCastI8_inFragment : inFragment boolCastI8 = true := by decide

def boolCastI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Bool)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Rel .Eq) (.Load (.Local (localName 1))) (.Constant (.Bool false) .Bool)),
      .Assign (.Local (localName 1))
        (.UnOp (.Cast (.Transmute .Bool))
          (.BinOp (.Int .Sub) (.Constant (.Int 1) (.Int u8))
            (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1))))))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1))))
        ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt i8))
          (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1)))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt i8))
          (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1)))))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem boolCastI8_translate : translateFn boolCastI8 = some boolCastI8Fn := rfl

/-- An invalid `bool` bit pattern (`2 >= 2`) is rejected by `argsOk`. -/
theorem boolCastInvalidArg_rejected : argsOk boolCastI8 [.scalar ⟨2, 1⟩] = false := rfl

/-- Input `b = true` (byte `1`): `!(true == false) = true`, casts `true as i8 = 1i8`. -/
def boolCastTrueArgs : List Value := [.scalar ⟨1, 1⟩]
def boolCastTrueS0 : MachineState := initMachineState boolCastI8 boolCastTrueArgs
def boolCastTrueMInit : Mach :=
  machineWithCtx ctxI8 boolCastI8 boolCastI8Fn boolCastTrueS0.frame.locals boolCastI8Fn.start

theorem boolCastTrue_anneal_ret :
    ReachesRet (mirCallTree boolCastI8 boolCastTrueArgs) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, boolCastTrueS0.memory)) :=
  runA_sound boolCastI8 15 _ _ _ rfl

theorem boolCastTrue_noUB : MirNoUBTree (mirCallTree boolCastI8 boolCastTrueArgs) :=
  runA_noUB boolCastI8 15 _ _ _ rfl

theorem boolCastTrue_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n boolCastTrueMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 1 } ∧
      m'.threads = [thread1 ctxI8 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret boolCastI8_inFragment boolCastI8_translate ctxI8 (ctxI8_ok_boolCast rfl)
      boolCastTrueArgs (by decide) boolCastTrueMInit rfl rfl rfl boolCastTrue_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [boolCastI8] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem boolCastTrue_minirust_direct :
    (Interp.steps 6 boolCastTrueMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 1 }, [1]) := rfl

/-- Input `b = false` (byte `0`): `!(false == false) = false`, casts `false as i8 = 0i8`. -/
def boolCastFalseArgs : List Value := [.scalar ⟨0, 1⟩]
def boolCastFalseS0 : MachineState := initMachineState boolCastI8 boolCastFalseArgs
def boolCastFalseMInit : Mach :=
  machineWithCtx ctxI8 boolCastI8 boolCastI8Fn boolCastFalseS0.frame.locals boolCastI8Fn.start

theorem boolCastFalse_anneal_ret :
    ReachesRet (mirCallTree boolCastI8 boolCastFalseArgs) [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 1⟩, boolCastFalseS0.memory)) :=
  runA_sound boolCastI8 15 _ _ _ rfl

theorem boolCastFalse_noUB : MirNoUBTree (mirCallTree boolCastI8 boolCastFalseArgs) :=
  runA_noUB boolCastI8 15 _ _ _ rfl

theorem boolCastFalse_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n boolCastFalseMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 0 } ∧
      m'.threads = [thread1 ctxI8 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret boolCastI8_inFragment boolCastI8_translate ctxI8 (ctxI8_ok_boolCast rfl)
      boolCastFalseArgs (by decide) boolCastFalseMInit rfl rfl rfl boolCastFalse_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [boolCastI8] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem boolCastFalse_minirust_direct :
    (Interp.steps 6 boolCastFalseMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 0 }, [1]) := rfl

/-! ### Reading an uninitialized `bool` -/

def fnAbiToBool : FnAbi :=
  { args := [], ret := { layout := boolLayout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR of `fn uninit_bool() -> bool` whose only block switches on the
uninitialized return place `_0`: both semantics raise UB at the load. -/
def uninitBool : CapturedMir where
  defPath := "witness::uninit_bool"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 0)) { branches := [(0, 1)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.unaryOp .not (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToBool
  layouts := emptyLayoutTable
  allocations := []

theorem uninitBool_inFragment : inFragment uninitBool = true := by decide

def uninitBoolFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 0))))
      ⟨[(0, bbName 1)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute .Bool))
          (.BinOp (.Int .Sub) (.Constant (.Int 1) (.Int u8))
            (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 0))))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 2
  implicit_writes := true

theorem uninitBool_translate : translateFn uninitBool = some uninitBoolFn := rfl

def uninitBoolS0 : MachineState := initMachineState uninitBool []
def uninitBoolMInit : Mach :=
  machineWithCtx ctxBool uninitBool uninitBoolFn uninitBoolS0.frame.locals uninitBoolFn.start

theorem ctxBool_ok1 {body : CapturedMir} (h : body.localDecls = [boolDecl]) : CtxOk body ctxBool where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | _ + 1, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem uninitBool_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitBool []) tr u ∧ FaultNow u :=
  faultsA_sound uninitBool 3 _ (by decide)

theorem uninitBool_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBoolMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBool_anneal_ub
  exact mirCall_ub uninitBool_inFragment uninitBool_translate ctxBool (ctxBool_ok1 rfl) []
    (by decide) uninitBoolMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitBool_minirust_direct :
    Interp.steps 2 uninitBoolMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- MIR of `fn uninit_bool_not() -> bool` whose entry block negates the
uninitialized return place `_0` (`_0 = !copy _0` via `build::not`), faulting
at the load of `_0` before the `u8` transmute. -/
def uninitBoolNot : CapturedMir where
  defPath := "witness::uninit_bool_not"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.unaryOp .not (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToBool
  layouts := emptyLayoutTable
  allocations := []

theorem uninitBoolNot_inFragment : inFragment uninitBoolNot = true := by decide

def uninitBoolNotFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute .Bool))
          (.BinOp (.Int .Sub) (.Constant (.Int 1) (.Int u8))
            (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 0))))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitBoolNot_translate : translateFn uninitBoolNot = some uninitBoolNotFn := rfl

def uninitBoolNotS0 : MachineState := initMachineState uninitBoolNot []
def uninitBoolNotMInit : Mach :=
  machineWithCtx ctxBool uninitBoolNot uninitBoolNotFn uninitBoolNotS0.frame.locals uninitBoolNotFn.start

theorem uninitBoolNot_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitBoolNot []) tr u ∧ FaultNow u :=
  faultsA_sound uninitBoolNot 3 _ (by decide)

theorem uninitBoolNot_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBoolNotMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBoolNot_anneal_ub
  exact mirCall_ub uninitBoolNot_inFragment uninitBoolNot_translate ctxBool (ctxBool_ok1 rfl) []
    (by decide) uninitBoolNotMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitBoolNot_minirust_direct :
    Interp.steps 2 uninitBoolNotMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- MIR of `fn uninit_bool_rel() -> bool` whose entry block compares the
uninitialized return place `_0` (`_0 = Eq(copy _0, const true)`), faulting at
the load of `_0` in `BinOp::Rel`. -/
def uninitBoolRel : CapturedMir where
  defPath := "witness::uninit_bool_rel"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .eq (.copy (local_ 0)) (constBool true)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToBool
  layouts := emptyLayoutTable
  allocations := []

theorem uninitBoolRel_inFragment : inFragment uninitBoolRel = true := by decide

def uninitBoolRelFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Rel .Eq) (.Load (.Local (localName 0))) (.Constant (.Bool true) .Bool))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitBoolRel_translate : translateFn uninitBoolRel = some uninitBoolRelFn := rfl

def uninitBoolRelS0 : MachineState := initMachineState uninitBoolRel []
def uninitBoolRelMInit : Mach :=
  machineWithCtx ctxBool uninitBoolRel uninitBoolRelFn uninitBoolRelS0.frame.locals uninitBoolRelFn.start

theorem uninitBoolRel_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitBoolRel []) tr u ∧ FaultNow u :=
  faultsA_sound uninitBoolRel 3 _ (by decide)

theorem uninitBoolRel_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBoolRelMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBoolRel_anneal_ub
  exact mirCall_ub uninitBoolRel_inFragment uninitBoolRel_translate ctxBool (ctxBool_ok1 rfl) []
    (by decide) uninitBoolRelMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitBoolRel_minirust_direct :
    Interp.steps 2 uninitBoolRelMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-! ## Three-way comparison `Cmp` and `core::cmp::Ordering` -/

def orderingTyW : Ty := { kind := .adt "core::cmp::Ordering" [], layoutIdx := 0 }
def orderingDecl : LocalDecl := { mutability := .mut, ty := orderingTyW, debugName := none }

/-- The ABI of `cmp_sel`. Like the other ABI layouts in this module, the
return layout is never read by the fragment, so the one-byte `i8Layout`
stands in for `Ordering`'s one-byte layout. -/
def fnAbiCmpSel : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct }, { layout := i8Layout, mode := .direct },
      { layout := boolLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_cmpSel {body : CapturedMir}
    (h : body.localDecls = [orderingDecl, i8Decl, i8Decl, boolDecl]) : CtxOk body ctxI8_4 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | 3, hd => simp at hd; subst hd; decide
    | _ + 4, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`, with `Ord::cmp` inlined to `BinOp::Cmp`) of
```rust
fn cmp_sel(x: i8, y: i8, b: bool) -> Ordering {
    if b { x.cmp(&y) }       // bb0: switchInt(copy _3) -> [0: bb2, otherwise: bb1]
                             // bb1: _0 = Cmp(copy _1, copy _2); return
    else { true.cmp(&b) }    // bb2: _0 = Cmp(const true, copy _3); return
}
```
whose `Ordering` return place receives a three-way comparison of two signed
integers or of two `bool`s. `minimize` turns each `Cmp` into a transmute of
MiniRust's `i8` comparison result to `orderingTy` (`translateCmp`), and the
return path loads and stores the result at `orderingTy`. -/
def cmpSel : CapturedMir where
  defPath := "witness::cmp_sel"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [orderingDecl, i8Decl, i8Decl, boolDecl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 3)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .cmp (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .cmp (constBool true) (.copy (local_ 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCmpSel
  layouts := emptyLayoutTable
  allocations := []

theorem cmpSel_inFragment : inFragment cmpSel = true := by decide

/-- The MiniRust function `minimize` produces for `cmpSel`, spelled out: the
return place has type `orderingTy`, each `Cmp` is
`transmute::<orderingTy>(BinOp::Rel(RelOp::Cmp, ..))`, and the `switchInt` on
`b` switches on `transmute::<u8>(b)`. -/
def cmpSelFn : Gen.Function where
  locals := ⟨[(localName 0, orderingTy), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, .Bool)]⟩
  args := [localName 1, localName 2, localName 3]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 3))))
      ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute orderingTy))
          (.BinOp (.Rel .Cmp) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute orderingTy))
          (.BinOp (.Rel .Cmp) (.Constant (.Bool true) .Bool) (.Load (.Local (localName 3)))))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem cmpSel_translate : translateFn cmpSel = some cmpSelFn := rfl

/-- Input `(x, y, b) = (-1, 1, true)`: `(-1).cmp(&1)` is `Less`, whose tag is
the `i8` `-1` (byte `255`). Comparing the bit patterns unsigned (`255 > 1`)
would give `Greater` instead. -/
def cmpSelLessArgs : List Value := [.scalar ⟨255, 1⟩, .scalar ⟨1, 1⟩, .scalar ⟨1, 1⟩]
def cmpSelLessS0 : MachineState := initMachineState cmpSel cmpSelLessArgs
def cmpSelLessMInit : Mach :=
  machineWithCtx ctxI8_4 cmpSel cmpSelFn cmpSelLessS0.frame.locals cmpSelFn.start

theorem cmpSelLess_anneal_ret :
    ReachesRet (mirCallTree cmpSel cmpSelLessArgs) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨255, 1⟩, cmpSelLessS0.memory)) :=
  runA_sound cmpSel 10 _ _ _ rfl

theorem cmpSelLess_noUB : MirNoUBTree (mirCallTree cmpSel cmpSelLessArgs) :=
  runA_noUB cmpSel 10 _ _ _ rfl

theorem cmpSelLess_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpSelLessMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 255 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpSel_inFragment cmpSel_translate ctxI8_4 (ctxI8_ok_cmpSel rfl)
      cmpSelLessArgs (by decide) cmpSelLessMInit rfl rfl rfl cmpSelLess_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpSel] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem cmpSelLess_minirust_direct :
    (Interp.steps 4 cmpSelLessMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 255 }, [1]) := rfl

/-- Input `(7, 7, true)`: `7.cmp(&7)` is `Equal` (byte `0`). -/
def cmpSelEqualArgs : List Value := [.scalar ⟨7, 1⟩, .scalar ⟨7, 1⟩, .scalar ⟨1, 1⟩]
def cmpSelEqualS0 : MachineState := initMachineState cmpSel cmpSelEqualArgs
def cmpSelEqualMInit : Mach :=
  machineWithCtx ctxI8_4 cmpSel cmpSelFn cmpSelEqualS0.frame.locals cmpSelFn.start

theorem cmpSelEqual_anneal_ret :
    ReachesRet (mirCallTree cmpSel cmpSelEqualArgs) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 1⟩, cmpSelEqualS0.memory)) :=
  runA_sound cmpSel 10 _ _ _ rfl

theorem cmpSelEqual_noUB : MirNoUBTree (mirCallTree cmpSel cmpSelEqualArgs) :=
  runA_noUB cmpSel 10 _ _ _ rfl

theorem cmpSelEqual_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpSelEqualMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 0 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpSel_inFragment cmpSel_translate ctxI8_4 (ctxI8_ok_cmpSel rfl)
      cmpSelEqualArgs (by decide) cmpSelEqualMInit rfl rfl rfl cmpSelEqual_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpSel] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem cmpSelEqual_minirust_direct :
    (Interp.steps 4 cmpSelEqualMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 0 }, [1]) := rfl

/-- Input `(0, 0, false)`: `true.cmp(&false)` is `Greater` (byte `1`). -/
def cmpSelGreaterArgs : List Value := [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩]
def cmpSelGreaterS0 : MachineState := initMachineState cmpSel cmpSelGreaterArgs
def cmpSelGreaterMInit : Mach :=
  machineWithCtx ctxI8_4 cmpSel cmpSelFn cmpSelGreaterS0.frame.locals cmpSelFn.start

theorem cmpSelGreater_anneal_ret :
    ReachesRet (mirCallTree cmpSel cmpSelGreaterArgs) [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, cmpSelGreaterS0.memory)) :=
  runA_sound cmpSel 10 _ _ _ rfl

theorem cmpSelGreater_noUB : MirNoUBTree (mirCallTree cmpSel cmpSelGreaterArgs) :=
  runA_noUB cmpSel 10 _ _ _ rfl

theorem cmpSelGreater_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpSelGreaterMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 1 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpSel_inFragment cmpSel_translate ctxI8_4 (ctxI8_ok_cmpSel rfl)
      cmpSelGreaterArgs (by decide) cmpSelGreaterMInit rfl rfl rfl cmpSelGreater_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpSel] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem cmpSelGreater_minirust_direct :
    (Interp.steps 4 cmpSelGreaterMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 1 }, [1]) := rfl

/-! ### Returning an uninitialized `Ordering` -/

def fnAbiToOrdering : FnAbi :=
  { args := [], ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR of `fn uninit_ordering() -> Ordering` that returns without writing its
return place: both semantics raise UB when the return reads `_0` (MiniRust
decodes the `Uninit` byte at `orderingTy` and finds no tag). -/
def uninitOrdering : CapturedMir where
  defPath := "witness::uninit_ordering"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [orderingDecl]
  basicBlocks := [{ statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToOrdering
  layouts := emptyLayoutTable
  allocations := []

theorem uninitOrdering_inFragment : inFragment uninitOrdering = true := by decide

def uninitOrderingFn : Gen.Function where
  locals := ⟨[(localName 0, orderingTy)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[(bbName 0, ⟨[], .Return, .Regular⟩), (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitOrdering_translate : translateFn uninitOrdering = some uninitOrderingFn := rfl

theorem ctxBool_ok_ordering {body : CapturedMir} (h : body.localDecls = [orderingDecl]) :
    CtxOk body ctxBool where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | _ + 1, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

def uninitOrderingS0 : MachineState := initMachineState uninitOrdering []
def uninitOrderingMInit : Mach :=
  machineWithCtx ctxBool uninitOrdering uninitOrderingFn uninitOrderingS0.frame.locals
    uninitOrderingFn.start

theorem uninitOrdering_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitOrdering []) tr u ∧ FaultNow u :=
  faultsA_sound uninitOrdering 3 _ (by decide)

theorem uninitOrdering_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitOrderingMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitOrdering_anneal_ub
  exact mirCall_ub uninitOrdering_inFragment uninitOrdering_translate ctxBool
    (ctxBool_ok_ordering rfl) [] (by decide) uninitOrderingMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitOrdering_minirust_direct :
    Interp.steps 2 uninitOrderingMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-! ### `bool` bitwise `BitAnd`/`BitOr`/`BitXor`, unsigned `u8` `Cmp`, and `Ordering` `Use` -/

theorem ctxI8_ok_boolBitOrdUse {body : CapturedMir}
    (h : body.localDecls = [orderingDecl, boolDecl, u8Decl, orderingDecl]) : CtxOk body ctxI8_4 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | 3, hd => simp at hd; subst hd; decide
    | _ + 4, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn bool_bit_ord_use(mut a: bool, x: u8, ord_in: Ordering) -> Ordering {
    // bb0: PlaceMention(_0) (while _0: Ordering is still uninitialized);
    a = ((a & true) | false) ^ true; //      _1 = BitAnd(copy _1, const true);
                                     //      _1 = BitOr(copy _1, const false);
                                     //      _1 = BitXor(copy _1, const true);
                                     //      switchInt(copy _1) -> [0: bb2, otherwise: bb1]
    if a { x.cmp(&1u8) }             // bb1: _0 = Cmp(copy _2, const 1u8); return
    else { ord_in }                  // bb2: _0 = Use(copy _3); return
}
```
exercising `PlaceMention(_0)` on an uninitialized `Ordering` local,
`build::bool_and`, `build::bool_or`, and `build::bool_xor` (`boolBitOp`),
unsigned `u8` three-way `Cmp` (`255u8.cmp(&1u8) = Greater`, whereas signed
`-1i8.cmp(&1i8) = Less` in `cmpSel`), and `Use(copy _3)` on an `Ordering`
local. -/
def boolBitOrdUse : CapturedMir where
  defPath := "witness::bool_bit_ord_use"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [orderingDecl, boolDecl, u8Decl, orderingDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.placeMention (local_ 0)),
        mkStmt (.assign (local_ 1) (.binaryOp .bitAnd (.copy (local_ 1)) (constBool true))),
        mkStmt (.assign (local_ 1) (.binaryOp .bitOr (.copy (local_ 1)) (constBool false))),
        mkStmt (.assign (local_ 1) (.binaryOp .bitXor (.copy (local_ 1)) (constBool true)))],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .cmp (.copy (local_ 2)) (constU8 1)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCmpSel
  layouts := emptyLayoutTable
  allocations := []

theorem boolBitOrdUse_inFragment : inFragment boolBitOrdUse = true := by decide

def boolBitOrdUseFn : Gen.Function where
  locals := ⟨[(localName 0, orderingTy), (localName 1, .Bool), (localName 2, .Int u8),
    (localName 3, orderingTy)]⟩
  args := [localName 1, localName 2, localName 3]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .PlaceMention (.Local (localName 0)),
      .Assign (.Local (localName 1))
        (boolBitOp .BitAnd (.Load (.Local (localName 1))) (.Constant (.Bool true) .Bool)),
      .Assign (.Local (localName 1))
        (boolBitOp .BitOr (.Load (.Local (localName 1))) (.Constant (.Bool false) .Bool)),
      .Assign (.Local (localName 1))
        (boolBitOp .BitXor (.Load (.Local (localName 1))) (.Constant (.Bool true) .Bool))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1))))
        ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (translateCmp (.Load (.Local (localName 2))) (.Constant (.Int 1) (.Int u8)))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 3)))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem boolBitOrdUse_translate : translateFn boolBitOrdUse = some boolBitOrdUseFn := rfl

/-- Invalid `Ordering` tag bytes (`2` and `128`, i.e. `-128i8`) are rejected by
`argsOk`. -/
theorem boolBitOrdInvalidTag_rejected :
    argsOk boolBitOrdUse [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩, .scalar ⟨2, 1⟩] = false ∧
      argsOk boolBitOrdUse [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩, .scalar ⟨128, 1⟩] = false :=
  ⟨rfl, rfl⟩

/-- Input `(false, 255u8, Equal)`: `((false & true) | false) ^ true = true`,
takes `bb1`, and unsigned `255u8.cmp(&1u8)` returns `Greater` (byte `1`). -/
def boolBitOrdUseCmpArgs : List Value := [.scalar ⟨0, 1⟩, .scalar ⟨255, 1⟩, .scalar ⟨0, 1⟩]
def boolBitOrdUseCmpS0 : MachineState := initMachineState boolBitOrdUse boolBitOrdUseCmpArgs
def boolBitOrdUseCmpMInit : Mach :=
  machineWithCtx ctxI8_4 boolBitOrdUse boolBitOrdUseFn boolBitOrdUseCmpS0.frame.locals
    boolBitOrdUseFn.start

theorem boolBitOrdUseCmp_anneal_ret :
    ReachesRet (mirCallTree boolBitOrdUse boolBitOrdUseCmpArgs)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, boolBitOrdUseCmpS0.memory)) :=
  runA_sound boolBitOrdUse 15 _ _ _ rfl

theorem boolBitOrdUseCmp_noUB : MirNoUBTree (mirCallTree boolBitOrdUse boolBitOrdUseCmpArgs) :=
  runA_noUB boolBitOrdUse 15 _ _ _ rfl

theorem boolBitOrdUseCmp_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n boolBitOrdUseCmpMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 1 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret boolBitOrdUse_inFragment boolBitOrdUse_translate ctxI8_4
      (ctxI8_ok_boolBitOrdUse rfl) boolBitOrdUseCmpArgs (by decide) boolBitOrdUseCmpMInit
      rfl rfl rfl boolBitOrdUseCmp_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [boolBitOrdUse] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem boolBitOrdUseCmp_minirust_direct :
    (Interp.steps 8 boolBitOrdUseCmpMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 1 }, [1]) := rfl

/-- Input `(true, 255u8, Less)`: `((true & true) | false) ^ true = false`,
takes `bb2`, and `_0 = Use(copy _3)` returns `Less` (byte `255`). -/
def boolBitOrdUseCopyArgs : List Value := [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩, .scalar ⟨255, 1⟩]
def boolBitOrdUseCopyS0 : MachineState := initMachineState boolBitOrdUse boolBitOrdUseCopyArgs
def boolBitOrdUseCopyMInit : Mach :=
  machineWithCtx ctxI8_4 boolBitOrdUse boolBitOrdUseFn boolBitOrdUseCopyS0.frame.locals
    boolBitOrdUseFn.start

theorem boolBitOrdUseCopy_anneal_ret :
    ReachesRet (mirCallTree boolBitOrdUse boolBitOrdUseCopyArgs)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨255, 1⟩, boolBitOrdUseCopyS0.memory)) :=
  runA_sound boolBitOrdUse 15 _ _ _ rfl

theorem boolBitOrdUseCopy_noUB : MirNoUBTree (mirCallTree boolBitOrdUse boolBitOrdUseCopyArgs) :=
  runA_noUB boolBitOrdUse 15 _ _ _ rfl

theorem boolBitOrdUseCopy_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n boolBitOrdUseCopyMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 255 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret boolBitOrdUse_inFragment boolBitOrdUse_translate ctxI8_4
      (ctxI8_ok_boolBitOrdUse rfl) boolBitOrdUseCopyArgs (by decide) boolBitOrdUseCopyMInit
      rfl rfl rfl boolBitOrdUseCopy_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [boolBitOrdUse] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem boolBitOrdUseCopy_minirust_direct :
    (Interp.steps 8 boolBitOrdUseCopyMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 255 }, [1]) := rfl

/-- MIR of `fn uninit_bool_bitand() -> bool` whose entry block applies
`BitAnd(copy _0, const true)` (`build::bool_and`) to the uninitialized return
place `_0`, faulting at the load of `_0`. -/
def uninitBoolBitAnd : CapturedMir where
  defPath := "witness::uninit_bool_bitand"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .bitAnd (.copy (local_ 0)) (constBool true)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToBool
  layouts := emptyLayoutTable
  allocations := []

theorem uninitBoolBitAnd_inFragment : inFragment uninitBoolBitAnd = true := by decide

def uninitBoolBitAndFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (boolBitOp .BitAnd (.Load (.Local (localName 0))) (.Constant (.Bool true) .Bool))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitBoolBitAnd_translate : translateFn uninitBoolBitAnd = some uninitBoolBitAndFn := rfl

def uninitBoolBitAndS0 : MachineState := initMachineState uninitBoolBitAnd []
def uninitBoolBitAndMInit : Mach :=
  machineWithCtx ctxBool uninitBoolBitAnd uninitBoolBitAndFn uninitBoolBitAndS0.frame.locals
    uninitBoolBitAndFn.start

theorem uninitBoolBitAnd_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitBoolBitAnd []) tr u ∧ FaultNow u :=
  faultsA_sound uninitBoolBitAnd 3 _ (by decide)

theorem uninitBoolBitAnd_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBoolBitAndMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBoolBitAnd_anneal_ub
  exact mirCall_ub uninitBoolBitAnd_inFragment uninitBoolBitAnd_translate ctxBool (ctxBool_ok1 rfl) []
    (by decide) uninitBoolBitAndMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitBoolBitAnd_minirust_direct :
    Interp.steps 2 uninitBoolBitAndMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- MIR of `fn uninit_bool_bitor_rhs() -> bool` whose entry block applies
`BitOr(const true, copy _0)` (`build::bool_or`) to an initialized LHS `true`
and the uninitialized return place `_0` on the RHS, confirming that MIR
`BinaryOp(BitOr)` on `bool` does not short-circuit and faults when loading the
uninitialized RHS operand `_0`. -/
def uninitBoolBitOrRhs : CapturedMir where
  defPath := "witness::uninit_bool_bitor_rhs"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .bitOr (constBool true) (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToBool
  layouts := emptyLayoutTable
  allocations := []

theorem uninitBoolBitOrRhs_inFragment : inFragment uninitBoolBitOrRhs = true := by decide

def uninitBoolBitOrRhsFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (boolBitOp .BitOr (.Constant (.Bool true) .Bool) (.Load (.Local (localName 0))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitBoolBitOrRhs_translate : translateFn uninitBoolBitOrRhs = some uninitBoolBitOrRhsFn := rfl

def uninitBoolBitOrRhsS0 : MachineState := initMachineState uninitBoolBitOrRhs []
def uninitBoolBitOrRhsMInit : Mach :=
  machineWithCtx ctxBool uninitBoolBitOrRhs uninitBoolBitOrRhsFn uninitBoolBitOrRhsS0.frame.locals
    uninitBoolBitOrRhsFn.start

theorem uninitBoolBitOrRhs_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitBoolBitOrRhs []) tr u ∧ FaultNow u :=
  faultsA_sound uninitBoolBitOrRhs 3 _ (by decide)

theorem uninitBoolBitOrRhs_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBoolBitOrRhsMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBoolBitOrRhs_anneal_ub
  exact mirCall_ub uninitBoolBitOrRhs_inFragment uninitBoolBitOrRhs_translate ctxBool (ctxBool_ok1 rfl) []
    (by decide) uninitBoolBitOrRhsMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitBoolBitOrRhs_minirust_direct :
    Interp.steps 2 uninitBoolBitOrRhsMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-! ### Ground truth for the interpreted operators

Direct evaluations of the transcribed MiniRust operators, independent of the
correspondence. -/

/-- `BinOp::Rel` compares signed integers by value: `-1i8 < 1i8`. -/
theorem relLt_signed : evalBinOp (.Rel .Lt) (.Int (-1), .Int i8) (.Int 1, .Int i8) =
    .ok (.Bool true, .Bool) := rfl

/-- `BinOp::Rel` compares unsigned integers by value: `255u8 > 1u8`. -/
theorem relGt_unsigned : evalBinOp (.Rel .Gt) (.Int 255, .Int u8) (.Int 1, .Int u8) =
    .ok (.Bool true, .Bool) := rfl

/-- `RelOp::Cmp` returns an `i8`: `-1` for `-1i8 < 1i8`, `1` for
`255u8 > 1u8`, and `0` for equal `bool`s. -/
theorem relCmp_signed : evalBinOp (.Rel .Cmp) (.Int (-1), .Int i8) (.Int 1, .Int i8) =
    .ok (.Int (-1), .Int IntType.I8) := rfl
theorem relCmp_unsigned : evalBinOp (.Rel .Cmp) (.Int 255, .Int u8) (.Int 1, .Int u8) =
    .ok (.Int 1, .Int IntType.I8) := rfl
theorem relCmp_bool : evalBinOp (.Rel .Cmp) (.Bool true, .Bool) (.Bool true, .Bool) =
    .ok (.Int 0, .Int IntType.I8) := rfl

/-- `bool`s compare with `false < true`, and `Le`/`Ge`/`Ne` are the negations
of `Gt`/`Lt`/`Eq`. -/
theorem relLt_bool : evalBinOp (.Rel .Lt) (.Bool false, .Bool) (.Bool true, .Bool) =
    .ok (.Bool true, .Bool) := rfl
theorem relGt_bool : evalBinOp (.Rel .Gt) (.Bool true, .Bool) (.Bool false, .Bool) =
    .ok (.Bool true, .Bool) := rfl
theorem relLe_bool : evalBinOp (.Rel .Le) (.Bool true, .Bool) (.Bool false, .Bool) =
    .ok (.Bool false, .Bool) := rfl
theorem relGe_bool : evalBinOp (.Rel .Ge) (.Bool false, .Bool) (.Bool false, .Bool) =
    .ok (.Bool true, .Bool) := rfl
theorem relEq_bool : evalBinOp (.Rel .Eq) (.Bool false, .Bool) (.Bool false, .Bool) =
    .ok (.Bool true, .Bool) := rfl
theorem relNe_bool : evalBinOp (.Rel .Ne) (.Bool false, .Bool) (.Bool true, .Bool) =
    .ok (.Bool true, .Bool) := rfl
theorem relGe_eq : evalBinOp (.Rel .Ge) (.Int 7, .Int u8) (.Int 7, .Int u8) =
    .ok (.Bool true, .Bool) := rfl
theorem relNe_eq : evalBinOp (.Rel .Ne) (.Int 7, .Int u8) (.Int 7, .Int u8) =
    .ok (.Bool false, .Bool) := rfl

/-- A comparison of mismatched values is a spec panic (an ill-formed program),
not UB. -/
theorem rel_mismatch : evalBinOp (.Rel .Eq) (.Int 1, .Int i8) (.Bool true, .Bool) =
    .error (.specPanic "relational operator on incomparable type or value-type mismatch") := rfl

/-- `CastOp::Transmute` goes through the bytes: `true` becomes `1u8`, `1u8`
becomes `true`, the byte `2` is not a valid `bool`, and transmuting between
types of different sizes is UB. -/
theorem transmute_bool_u8 : evalCastOp (.Transmute (.Int u8)) (.Bool true, .Bool) =
    .ok (.Int 1, .Int u8) := rfl
theorem transmute_u8_bool : evalCastOp (.Transmute .Bool) (.Int 1, .Int u8) =
    .ok (.Bool true, .Bool) := rfl
theorem transmute_u8_bool_invalid : evalCastOp (.Transmute .Bool) (.Int 2, .Int u8) =
    .error (.ub "transmuted value is not valid at new type") := rfl
theorem transmute_size_mismatch :
    evalCastOp (.Transmute .Bool) (.Int 1, .Int ⟨.Unsigned, ⟨2⟩⟩) =
      .error (.ub "transmute between types of different size") := rfl

/-- `Type::Bool` decodes only the bytes `0` and `1`. -/
theorem decode_bool_invalid :
    Type.decode .Bool [.Init 2 none] = .ok none ∧ Type.decode .Bool [.Uninit] = .ok none ∧
      Type.decode .Bool [.Init 1 none] = .ok (some (.Bool true)) := ⟨rfl, rfl, rfl⟩

/-- `UnOp::Int` on a `bool` is a spec panic: MiniRust has no Boolean `!`. -/
theorem bitNot_bool_panics : evalUnOp (.Int .BitNot) (.Bool true, .Bool) =
    .error (.specPanic "non-integer input to integer operation") := rfl

/-- `core::cmp::Ordering`'s discriminator accepts exactly the tags `0`, `1`,
and `255` (the `i8`s `0`, `1`, `-1`) among all one-byte patterns. -/
theorem ordering_validTags : (List.range 256).filter (validBits orderingTy) = [0, 1, 255] := by
  decide +kernel

/-- `Type::decode` at `orderingTy` walks the discriminator: the byte `255` is
the tag `-1` of `Less`, while `2` and `128` (the `i8` `-128`) fall into the
`Invalid` fallback and an `Uninit` byte has no tag. -/
theorem decode_ordering_less :
    Type.decode orderingTy [.Init 255 none] = .ok (some (.Variant (-1) (.Tuple []))) := rfl
theorem decode_ordering_invalid :
    Type.decode orderingTy [.Init 2 none] = .ok none ∧
      Type.decode orderingTy [.Init 128 none] = .ok none ∧
      Type.decode orderingTy [.Uninit] = .ok none := ⟨rfl, rfl, rfl⟩

/-- `Type::encode` at `orderingTy` encodes the variant's empty tuple as one
`Uninit` byte and then writes the tag over it (`encode_discriminant`). -/
theorem encode_ordering_greater :
    Type.encode orderingTy (.Variant 1 (.Tuple [])) = .ok [.Init 1 none] := rfl

/-- `check_value` rejects a discriminant without a variant as UB. -/
theorem checkValue_variant_invalid :
    checkValue (.Variant 2 (.Tuple [])) orderingTy =
      .error (.ub "Value::Variant: invalid discrimant") := rfl

/-- `translateCmp`'s transmute: the `i8` `-1` becomes `Less`, while the `i8`
`2` (which `RelOp::Cmp` never returns) is not a valid `Ordering`. -/
theorem transmute_i8_ordering :
    transmute (.Int (-1)) (.Int IntType.I8) orderingTy = .ok (.Variant (-1) (.Tuple [])) := rfl
theorem transmute_i8_ordering_invalid :
    transmute (.Int 2) (.Int IntType.I8) orderingTy =
      .error (.ub "transmuted value is not valid at new type") := rfl

/-- A padded tuple `(i8, bool)` with the `bool` at offset 2 and alignment 2:
`head_size_and_align` rounds the head size 3 up to 4, `Type::encode` makes
both padding bytes `Uninit`, `Type::decode` ignores them, and `check_value`
rejects a value with the wrong number of fields as UB. -/
def paddedPairTy : Gen.Type := .Tuple [(⟨0⟩, .Int IntType.I8), (⟨2⟩, .Bool)] ⟨⟨3⟩, ⟨2⟩, none⟩ none
theorem layout_paddedPair : Type.layout paddedPairTy = .ok (.Sized ⟨4⟩ ⟨2⟩) := rfl
theorem encode_paddedPair :
    Type.encode paddedPairTy (.Tuple [.Int (-2), .Bool true]) =
      .ok [.Init 254 none, .Uninit, .Init 1 none, .Uninit] := rfl
set_option maxRecDepth 8192 in
theorem decode_paddedPair :
    Type.decode paddedPairTy [.Init 254 none, .Init 7 none, .Init 1 none, .Uninit] =
      .ok (some (.Tuple [.Int (-2), .Bool true])) := rfl
theorem checkValue_tuple_arity :
    checkValue (.Tuple [.Int (-2)]) paddedPairTy =
      .error (.ub "Value::Tuple: invalid number of fields") := rfl

set_option maxRecDepth 8192 in
/-- `decodeDiscriminant` threads the `FnMut` accessor state `s` and evaluates
the `fallback` continuation only when no child branch matches: here a child
branch matches `(-1, 0)` at offset `0`, so the fallback (which would read
out-of-bounds offset `99`) is never invoked and the visited-offset log is
`[0]`. -/
theorem decodeDiscriminant_short_circuits :
    decodeDiscriminant
      (fun (s : List Nat) o sz => do
        let chunk ← subsliceWithLength ([.Init 255 none] : List Byte) o.bytes sz.bytes
        pure (chunk, s ++ [o.bytes]))
      (.Branch ⟨0⟩ IntType.I8
        (.Branch ⟨99⟩ IntType.I8 .Invalid ⟨[]⟩)
        ⟨[((-1, 0), .Known (-1))]⟩)
      [] = .ok (some (-1), [0]) := rfl

/-- Unsized `Type::Slice`, `Type::TraitObject`, and unsized `Type::Tuple`:
`Type.layout` returns `LayoutStrategy::Slice`, `LayoutStrategy::TraitObject`,
or `LayoutStrategy::Tuple`, and `LayoutStrategy.expect_size`,
`LayoutStrategy.expect_align`, `evalCastOp (.Transmute ...)`, `Type.decode`,
`Type.encode`, and `checkValue` raise the exact upstream `specPanic`s from
`spec/lang/types.md` and `spec/lang/representation.md`. -/
theorem layout_slice :
    Type.layout (.Slice .Bool) = .ok (.Slice ⟨1⟩ ⟨1⟩) := rfl
theorem layout_traitObject :
    Type.layout (.TraitObject ⟨⟨0⟩⟩) = .ok (.TraitObject ⟨⟨0⟩⟩) := rfl
theorem layout_unsizedTuple :
    Type.layout (.Tuple [] ⟨⟨1⟩, ⟨1⟩, none⟩ (some (.Slice .Bool))) =
      .ok (.Tuple ⟨⟨1⟩, ⟨1⟩, none⟩ (.Slice ⟨1⟩ ⟨1⟩)) := rfl
theorem expectSize_unsized_panics :
    LayoutStrategy.expect_size (.Slice ⟨1⟩ ⟨1⟩) "WF" =
      .error (.specPanic "expect_size called on unsized type: WF") := by
  simp [LayoutStrategy.expect_size, specPanic]
theorem expectAlign_traitObject_panics :
    LayoutStrategy.expect_align (.TraitObject ⟨⟨0⟩⟩) "WF" =
      .error (.specPanic "expect_align called on unsized type: WF") := by
  simp [LayoutStrategy.expect_align, specPanic]
theorem transmute_unsized_panics :
    evalCastOp (.Transmute .Bool) (.Tuple [], .Slice .Bool) =
      .error (.specPanic "expect_size called on unsized type: WF ensures transmutes are sized") := by
  simp [evalCastOp, Type.layout, LayoutStrategy.expect_size, LayoutStrategy.expect_align, specPanic]
theorem decode_unsized_panics :
    Type.decode (.Slice .Bool) [] =
      .error (.specPanic "decode of Type::Slice") := rfl
theorem encode_unsized_panics :
    Type.encode (.TraitObject ⟨⟨0⟩⟩) (.Tuple []) =
      .error (.specPanic "encode of Type::TraitObject") := rfl
theorem checkValue_unsized_panics :
    checkValue (.Tuple []) (.Slice .Bool) =
      .error (.specPanic "Value: slices cannot be represented as values") := rfl

/-- `Type::Union` with two 1-byte chunks at offsets `0` and `2` and padding at
offsets `1` and `3`: `Type::decode` extracts each chunk's raw `AbstractByte`s
(including `Uninit`) and ignores gap bytes outside `chunks`, `Type::encode`
restores each chunk at its offset and fills gap bytes with `Uninit`, and
`checkValue` rejects a wrong number of chunks or a chunk of wrong byte length
as UB. -/
def unionPaddedTy : Gen.Type :=
  .Union [(⟨0⟩, .Int IntType.I8), (⟨2⟩, .Bool)] [(⟨0⟩, ⟨1⟩), (⟨2⟩, ⟨1⟩)] ⟨4⟩ ⟨2⟩
theorem layout_union : Type.layout unionPaddedTy = .ok (.Sized ⟨4⟩ ⟨2⟩) := rfl
theorem decode_union :
    Type.decode unionPaddedTy [.Init 254 none, .Init 7 none, .Uninit, .Init 9 none] =
      .ok (some (.Union [[.Init 254 none], [.Uninit]])) := rfl
theorem encode_union :
    Type.encode unionPaddedTy (.Union [[.Init 254 none], [.Uninit]]) =
      .ok [.Init 254 none, .Uninit, .Uninit, .Uninit] := rfl
theorem checkValue_union_chunk_size :
    checkValue (.Union [[.Init 254 none]]) unionPaddedTy =
      .error (.ub "Value::Union: invalid chunk size") := rfl
theorem checkValue_union_chunk_data :
    checkValue (.Union [[.Init 254 none], [.Init 1 none, .Init 2 none]]) unionPaddedTy =
      .error (.ub "Value::Union: invalid chunk data") := rfl

set_option maxRecDepth 8192 in
/-- `CastOp::Transmute` between `unionPaddedTy` and `paddedPairTy` (both of size
`4` and alignment `2`, with active fields/chunks at offsets `0` and `2` and
padding/gaps at offsets `1` and `3`): transmuting a union with valid `i8` and
`bool` chunk bytes produces the corresponding tuple (and vice versa), whereas
transmuting a union whose second chunk at offset `2` is `Uninit` raises UB
because `paddedPairTy`'s `bool` field at offset `2` fails `Type::decode`. -/
theorem transmute_union_paddedPair :
    evalCastOp (.Transmute paddedPairTy) (.Union [[.Init 254 none], [.Init 1 none]], unionPaddedTy) =
      .ok (.Tuple [.Int (-2), .Bool true], paddedPairTy) := rfl
set_option maxRecDepth 8192 in
theorem transmute_paddedPair_union :
    evalCastOp (.Transmute unionPaddedTy) (.Tuple [.Int (-2), .Bool true], paddedPairTy) =
      .ok (.Union [[.Init 254 none], [.Init 1 none]], unionPaddedTy) := rfl
set_option maxRecDepth 8192 in
theorem transmute_union_paddedPair_uninit_ub :
    evalCastOp (.Transmute paddedPairTy) (.Union [[.Init 254 none], [.Uninit]], unionPaddedTy) =
      .error (.ub "transmuted value is not valid at new type") := rfl

/-! ## Checked integer arithmetic (`AddWithOverflow`, `SubWithOverflow`, `MulWithOverflow`) and `(Int, bool)` 2-tuples -/

def i8BoolTupleTyW : Ty := { kind := .tuple [.int .i8, .bool], layoutIdx := 0 }
def i8BoolTupleDecl : LocalDecl := { mutability := .mut, ty := i8BoolTupleTyW, debugName := none }
def u32BoolTupleTyW : Ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := 0 }
def u32BoolTupleDecl : LocalDecl := { mutability := .mut, ty := u32BoolTupleTyW, debugName := none }

def field0I8 (i : Nat) : Place := { local_ := i, projection := [.field 0 i8Ty] }
def field0U32 (i : Nat) : Place := { local_ := i, projection := [.field 0 u32Ty] }
def field1 (i : Nat) : Place := { local_ := i, projection := [.field 1 boolTy] }

/-- The callee's 5 locals live at addresses `128`, `256`, `384`, `512`, and `640`. -/
def ctxI8_5 : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8],
    addrs := [128, 256, 384, 512, 640],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxI8_ok_checkedArith {body : CapturedMir}
    (h : body.localDecls = [i8Decl, i8Decl, i8Decl, i8BoolTupleDecl, boolDecl]) :
    CtxOk body ctxI8_5 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | 3, hd => simp at hd; subst hd; decide
    | 4, hd => simp at hd; subst hd; decide
    | _ + 5, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

def fnAbiCheckedArithI8 : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct }, { layout := i8Layout, mode := .direct },
      { layout := i8Layout, mode := .direct }, { layout := boolLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn checked_arith_i8(x: i8, y: i8, mut t: (i8, bool), mut ov: bool) -> i8 {
    t = AddWithOverflow(x, y);                     // bb0: _3 = AddWithOverflow(copy _1, copy _2)
    ov = t.1;                                      //      _4 = Use(copy (_3.1))
    if ov {                                        //      switchInt(copy _4) -> [0: bb1, otherwise: bb3]
        return t.0;                                // bb3: _0 = Use(copy (_3.0)); return
    }
    t = SubWithOverflow(t.0, 1i8);                 // bb1: _3 = SubWithOverflow(copy (_3.0), const 1i8)
    if t.1 {                                       //      switchInt(copy (_3.1)) -> [0: bb2, otherwise: bb3]
        return t.0;
    }
    t = MulWithOverflow(t.0, 2i8);                 // bb2: _3 = MulWithOverflow(copy (_3.0), const 2i8)
    if t.1 {                                       //      switchInt(copy (_3.1)) -> [0: bb3, otherwise: bb4]
        return -t.0;                               // bb4: _0 = Neg(copy (_3.0)); return
    }
    t.0                                            // bb3: _0 = Use(copy (_3.0)); return
}
```
Exercises `AddWithOverflow`, `SubWithOverflow`, and `MulWithOverflow` on signed
`i8`, field projections `_3.0` and `_3.1` in `Rvalue::Use`, `Rvalue::BinaryOp`,
`Rvalue::UnaryOp`, and `TerminatorKind::SwitchInt`, both without overflow and
on `INT_MAX + 1`, `INT_MIN - 1`, and signed multiplication overflow. -/
def checkedArithI8 : CapturedMir where
  defPath := "witness::checked_arith_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 4
  localDecls := [i8Decl, i8Decl, i8Decl, i8BoolTupleDecl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 4) (.use (.copy (field1 3))))],
      terminator := mkTerm (.switchInt (.copy (local_ 4)) { branches := [(0, 1)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .subWithOverflow (.copy (field0I8 3)) (constI8 1)))],
      terminator := mkTerm (.switchInt (.copy (field1 3)) { branches := [(0, 2)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .mulWithOverflow (.copy (field0I8 3)) (constI8 2)))],
      terminator := mkTerm (.switchInt (.copy (field1 3)) { branches := [(0, 3)], otherwise := 4 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (field0I8 3))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy (field0I8 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCheckedArithI8
  layouts := emptyLayoutTable
  allocations := []

theorem checkedArithI8_inFragment : inFragment checkedArithI8 = true := by decide

def checkedArithI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, intBoolTupleTy i8), (localName 4, .Bool)]⟩
  args := [localName 1, localName 2, localName 3, localName 4]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.IntWithOverflow .Add) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 4))
        (.Load (.Field (.Local (localName 3)) 1))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 4))))
        ⟨[(0, bbName 1)]⟩ (bbName 3), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.IntWithOverflow .Sub)
          (.Load (.Field (.Local (localName 3)) 0))
          (.Constant (.Int 1) (.Int i8)))],
      .Switch
        (.UnOp (.Cast (.Transmute (.Int u8)))
          (.Load (.Field (.Local (localName 3)) 1)))
        ⟨[(0, bbName 2)]⟩ (bbName 3), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.IntWithOverflow .Mul)
          (.Load (.Field (.Local (localName 3)) 0))
          (.Constant (.Int 2) (.Int i8)))],
      .Switch
        (.UnOp (.Cast (.Transmute (.Int u8)))
          (.Load (.Field (.Local (localName 3)) 1)))
        ⟨[(0, bbName 3)]⟩ (bbName 4), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0))
        (.Load (.Field (.Local (localName 3)) 0))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Int .Neg)
          (.Load (.Field (.Local (localName 3)) 0)))],
      .Return, .Regular⟩),
    (bbName 5, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 5
  implicit_writes := true

theorem checkedArithI8_translate : translateFn checkedArithI8 = some checkedArithI8Fn := rfl

/-- An invalid `bool` bit pattern (`2 >= 2`) in field 1 of a `(i8, bool)` tuple
argument is rejected by `argsOk`. -/
theorem checkedArithInvalidTupleArg_rejected :
    argsOk checkedArithI8
      [.scalar ⟨30, 1⟩, .scalar ⟨20, 1⟩, .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨2, 1⟩], .scalar ⟨0, 1⟩] =
      false := rfl

/-- No-overflow input `(30i8, 20i8)`:
`30 + 20 = (50, false)`, `50 - 1 = (49, false)`, `49 * 2 = (98, false) -> 98i8`. -/
def checkedArithOkArgs : List Value :=
  [.scalar ⟨30, 1⟩, .scalar ⟨20, 1⟩, .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩], .scalar ⟨0, 1⟩]
def checkedArithOkS0 : MachineState := initMachineState checkedArithI8 checkedArithOkArgs
def checkedArithOkMInit : Mach :=
  machineWithCtx ctxI8_5 checkedArithI8 checkedArithI8Fn checkedArithOkS0.frame.locals
    checkedArithI8Fn.start

def checkedArithOkTrace : List (Event MirEffect) :=
  [0, 0, 0].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

theorem checkedArithOk_anneal_ret :
    ReachesRet (mirCallTree checkedArithI8 checkedArithOkArgs) checkedArithOkTrace
      (.normal (.scalar ⟨98, 1⟩, checkedArithOkS0.memory)) :=
  runA_sound checkedArithI8 20 _ _ _ rfl

theorem checkedArithOk_noUB : MirNoUBTree (mirCallTree checkedArithI8 checkedArithOkArgs) :=
  runA_noUB checkedArithI8 20 _ _ _ rfl

theorem checkedArithOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedArithOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 98 } ∧
      m'.threads = [thread1 ctxI8_5 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedArithI8_inFragment checkedArithI8_translate ctxI8_5
      (ctxI8_ok_checkedArith rfl) checkedArithOkArgs (by decide) checkedArithOkMInit
      rfl rfl rfl checkedArithOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_5] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_5] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedArithOk_minirust_direct :
    (Interp.steps 10 checkedArithOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 98 }, [1]) := rfl

/-- Signed addition overflow (`INT_MAX + 1`): `(127i8, 1i8)` computes
`AddWithOverflow(127i8, 1i8) = (-128i8, true)` (bits `128`, flag `1`),
branches on `_4 = _3.1 = true` to `bb3`, and returns `_3.0 = -128i8`. -/
def checkedArithAddOvArgs : List Value :=
  [.scalar ⟨127, 1⟩, .scalar ⟨1, 1⟩, .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩], .scalar ⟨0, 1⟩]
def checkedArithAddOvS0 : MachineState := initMachineState checkedArithI8 checkedArithAddOvArgs
def checkedArithAddOvMInit : Mach :=
  machineWithCtx ctxI8_5 checkedArithI8 checkedArithI8Fn checkedArithAddOvS0.frame.locals
    checkedArithI8Fn.start

theorem checkedArithAddOv_anneal_ret :
    ReachesRet (mirCallTree checkedArithI8 checkedArithAddOvArgs)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨128, 1⟩, checkedArithAddOvS0.memory)) :=
  runA_sound checkedArithI8 20 _ _ _ rfl

theorem checkedArithAddOv_noUB : MirNoUBTree (mirCallTree checkedArithI8 checkedArithAddOvArgs) :=
  runA_noUB checkedArithI8 20 _ _ _ rfl

theorem checkedArithAddOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedArithAddOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 128 } ∧
      m'.threads = [thread1 ctxI8_5 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedArithI8_inFragment checkedArithI8_translate ctxI8_5
      (ctxI8_ok_checkedArith rfl) checkedArithAddOvArgs (by decide) checkedArithAddOvMInit
      rfl rfl rfl checkedArithAddOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_5] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_5] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedArithAddOv_minirust_direct :
    (Interp.steps 6 checkedArithAddOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 128 }, [1]) := rfl

/-- Signed subtraction underflow (`INT_MIN - 1`): `(-128i8, 0i8)` (bits `128, 0`)
computes `AddWithOverflow(-128i8, 0i8) = (-128i8, false)`, then in `bb1`
`SubWithOverflow(-128i8, 1i8) = (127i8, true)` (bits `127`, flag `1`),
branches on `_3.1 = true` to `bb3`, and returns `_3.0 = 127i8`. -/
def checkedArithSubOvArgs : List Value :=
  [.scalar ⟨128, 1⟩, .scalar ⟨0, 1⟩, .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩], .scalar ⟨0, 1⟩]
def checkedArithSubOvS0 : MachineState := initMachineState checkedArithI8 checkedArithSubOvArgs
def checkedArithSubOvMInit : Mach :=
  machineWithCtx ctxI8_5 checkedArithI8 checkedArithI8Fn checkedArithSubOvS0.frame.locals
    checkedArithI8Fn.start

def checkedArithSubOvTrace : List (Event MirEffect) :=
  [0, 1].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

theorem checkedArithSubOv_anneal_ret :
    ReachesRet (mirCallTree checkedArithI8 checkedArithSubOvArgs) checkedArithSubOvTrace
      (.normal (.scalar ⟨127, 1⟩, checkedArithSubOvS0.memory)) :=
  runA_sound checkedArithI8 20 _ _ _ rfl

theorem checkedArithSubOv_noUB : MirNoUBTree (mirCallTree checkedArithI8 checkedArithSubOvArgs) :=
  runA_noUB checkedArithI8 20 _ _ _ rfl

theorem checkedArithSubOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedArithSubOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 127 } ∧
      m'.threads = [thread1 ctxI8_5 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedArithI8_inFragment checkedArithI8_translate ctxI8_5
      (ctxI8_ok_checkedArith rfl) checkedArithSubOvArgs (by decide) checkedArithSubOvMInit
      rfl rfl rfl checkedArithSubOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_5] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_5] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedArithSubOv_minirust_direct :
    (Interp.steps 8 checkedArithSubOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 127 }, [1]) := rfl

/-- Signed multiplication overflow: `(65i8, 0i8)` computes `65 + 0 = (65, false)`,
`65 - 1 = (64, false)`, and `MulWithOverflow(64i8, 2i8) = (-128i8, true)`
(since `64 * 2 = 128` overflows `i8` and wraps to `-128i8`, bits `128`),
branches to `bb4`, and returns `-(-128i8) = -128i8` (bits `128`). -/
def checkedArithMulOvArgs : List Value :=
  [.scalar ⟨65, 1⟩, .scalar ⟨0, 1⟩, .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩], .scalar ⟨0, 1⟩]
def checkedArithMulOvS0 : MachineState := initMachineState checkedArithI8 checkedArithMulOvArgs
def checkedArithMulOvMInit : Mach :=
  machineWithCtx ctxI8_5 checkedArithI8 checkedArithI8Fn checkedArithMulOvS0.frame.locals
    checkedArithI8Fn.start

def checkedArithMulOvTrace : List (Event MirEffect) :=
  [0, 0, 1].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

theorem checkedArithMulOv_anneal_ret :
    ReachesRet (mirCallTree checkedArithI8 checkedArithMulOvArgs) checkedArithMulOvTrace
      (.normal (.scalar ⟨128, 1⟩, checkedArithMulOvS0.memory)) :=
  runA_sound checkedArithI8 20 _ _ _ rfl

theorem checkedArithMulOv_noUB : MirNoUBTree (mirCallTree checkedArithI8 checkedArithMulOvArgs) :=
  runA_noUB checkedArithI8 20 _ _ _ rfl

theorem checkedArithMulOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedArithMulOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 128 } ∧
      m'.threads = [thread1 ctxI8_5 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedArithI8_inFragment checkedArithI8_translate ctxI8_5
      (ctxI8_ok_checkedArith rfl) checkedArithMulOvArgs (by decide) checkedArithMulOvMInit
      rfl rfl rfl checkedArithMulOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_5] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_5] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedArithMulOv_minirust_direct :
    (Interp.steps 10 checkedArithMulOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 128 }, [1]) := rfl

/-! ### Padded `(u32, bool)` 2-tuples, `Aggregate(Tuple)`, `UINT_MAX + 1`, `0 - 1`, and `u32` multiplication overflow -/

/-- Caller return allocation for `(u32, bool)`: size `8` bytes, alignment `4`. -/
def retAllocTupleU32 : Gen.Allocation :=
  { data := List.replicate 8 .Uninit, addr := 64, align := ⟨4⟩, kind := .Stack, live := true,
    extra := () }

def callerFnTupleU32 : Gen.Function where
  locals := ⟨[(localName 0, intBoolTupleTy u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true

def callerFrameTupleU32 : Frame :=
  { func := callerFnTupleU32, locals := ⟨[(localName 0, retPtr)]⟩, stack_pop_action := .BottomOfStack,
    next_block := bbName 0, next_stmt := 0, extra := () }

def ctxTupleU32 : Ctx :=
  { caller := callerFrameTupleU32, payloads := [], base := [retAllocTupleU32],
    addrs := [128, 256, 384],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxTupleU32_ok {body : CapturedMir}
    (h : body.localDecls = [u32BoolTupleDecl, u32Decl, u32Decl]) :
    CtxOk body ctxTupleU32 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocTupleU32, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn checked_tuple_u32(x: u32, y: u32) -> (u32, bool) {
    // bb0: PlaceMention(_0), PlaceMention(_0.0), PlaceMention(_0.1) (while _0: (u32, bool) is uninit)
    let mut t: (u32, bool) = SubWithOverflow(x, y); // _0 = SubWithOverflow(copy _1, copy _2)
    if t.1 {                                        // switchInt(copy (_0.1)) -> [0: bb1, otherwise: bb2]
        return AddWithOverflow(t.0, 1u32);          // bb2: _0 = AddWithOverflow(copy (_0.0), const 1u32); return
    }
    t = MulWithOverflow(t.0, y);                    // bb1: _0 = MulWithOverflow(copy (_0.0), copy _2)
    (t.0, t.1)                                      //      _0 = Aggregate(Tuple, [copy (_0.0), copy (_0.1)]); return
}
```
Exercises:
* `PlaceMention(_0)`, `PlaceMention(_0.0)`, and `PlaceMention(_0.1)` on the uninitialized `(u32, bool)` return place `_0`;
* unsigned `0u32 - 1u32 = (u32::MAX, true)` underflow followed by `u32::MAX + 1u32 = (0u32, true)` overflow;
* unsigned `65536u32 * 65536u32 = (0u32, true)` multiplication overflow;
* `Rvalue::Aggregate(AggregateKind::Tuple, [copy (_0.0), copy (_0.1)])` (`ValueExpr::Tuple`);
* returning a padded `(u32, bool)` tuple in `_0` (writing 4-byte `u32` at offset `0`, 1-byte `bool` at offset `4`, and 3 trailing `AbstractByte::Uninit` padding bytes at offsets `5..8`). -/
def checkedTupleU32 : CapturedMir where
  defPath := "witness::checked_tuple_u32"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32BoolTupleDecl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.placeMention (local_ 0)),
        mkStmt (.placeMention (field0U32 0)),
        mkStmt (.placeMention (field1 0)),
        mkStmt (.assign (local_ 0) (.binaryOp .subWithOverflow (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm (.switchInt (.copy (field1 0)) { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .mulWithOverflow (.copy (field0U32 0)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.aggregate .tuple [.copy (field0U32 0), .copy (field1 0)]))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .addWithOverflow (.copy (field0U32 0)) (constU32 1)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem checkedTupleU32_inFragment : inFragment checkedTupleU32 = true := by decide

def checkedTupleU32Fn : Gen.Function where
  locals := ⟨[(localName 0, intBoolTupleTy u32), (localName 1, .Int u32), (localName 2, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .PlaceMention (.Local (localName 0)),
      .PlaceMention (.Field (.Local (localName 0)) 0),
      .PlaceMention (.Field (.Local (localName 0)) 1),
      .Assign (.Local (localName 0))
        (.BinOp (.IntWithOverflow .Sub) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Switch
        (.UnOp (.Cast (.Transmute (.Int u8)))
          (.Load (.Field (.Local (localName 0)) 1)))
        ⟨[(0, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.IntWithOverflow .Mul)
          (.Load (.Field (.Local (localName 0)) 0))
          (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.Tuple [
          .Load (.Field (.Local (localName 0)) 0),
          .Load (.Field (.Local (localName 0)) 1)]
          (intBoolTupleTy u32))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.IntWithOverflow .Add)
          (.Load (.Field (.Local (localName 0)) 0))
          (.Constant (.Int 1) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem checkedTupleU32_translate : translateFn checkedTupleU32 = some checkedTupleU32Fn := rfl

/-- Unsigned underflow `0u32 - 1u32 = (4294967295u32, true)` followed by
`UINT_MAX + 1` (`4294967295u32 + 1u32 = (0u32, true)`), returning `(0u32, true)`
encoded as `tupleBytes u32 0 1` (with 3 trailing `Uninit` padding bytes). -/
def checkedTupleUnderAddOvArgs : List Value := [.scalar ⟨0, 4⟩, .scalar ⟨1, 4⟩]
def checkedTupleUnderAddOvS0 : MachineState :=
  initMachineState checkedTupleU32 checkedTupleUnderAddOvArgs
def checkedTupleUnderAddOvMInit : Mach :=
  machineWithCtx ctxTupleU32 checkedTupleU32 checkedTupleU32Fn
    checkedTupleUnderAddOvS0.frame.locals checkedTupleU32Fn.start

theorem checkedTupleUnderAddOv_anneal_ret :
    ReachesRet (mirCallTree checkedTupleU32 checkedTupleUnderAddOvArgs)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.aggregate 0 [.scalar ⟨0, 4⟩, .scalar ⟨1, 1⟩], checkedTupleUnderAddOvS0.memory)) :=
  runA_sound checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleUnderAddOv_noUB :
    MirNoUBTree (mirCallTree checkedTupleU32 checkedTupleUnderAddOvArgs) :=
  runA_noUB checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleUnderAddOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedTupleUnderAddOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocTupleU32 with data := tupleBytes u32 0 1 } ∧
      m'.threads = [thread1 ctxTupleU32 [{ callerFrameTupleU32 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedTupleU32_inFragment checkedTupleU32_translate ctxTupleU32
      (ctxTupleU32_ok rfl) checkedTupleUnderAddOvArgs (by decide) checkedTupleUnderAddOvMInit
      rfl rfl rfl checkedTupleUnderAddOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedTupleU32] at hd; subst hd
  simp [retPtr, ctxTupleU32] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxTupleU32] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedTupleUnderAddOv_minirust_direct :
    (Interp.steps 8 checkedTupleUnderAddOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocTupleU32 with data := tupleBytes u32 0 1 }, [1]) := rfl

/-- Unsigned multiplication overflow `(131072u32, 65536u32)`:
`131072u32 - 65536u32 = (65536u32, false)`, then
`MulWithOverflow(65536u32, 65536u32) = (0u32, true)` (`2^16 * 2^16 = 2^32`),
repackaged via `Aggregate(Tuple, [copy (_0.0), copy (_0.1)])` and returned. -/
def checkedTupleMulOvArgs : List Value := [.scalar ⟨131072, 4⟩, .scalar ⟨65536, 4⟩]
def checkedTupleMulOvS0 : MachineState :=
  initMachineState checkedTupleU32 checkedTupleMulOvArgs
def checkedTupleMulOvMInit : Mach :=
  machineWithCtx ctxTupleU32 checkedTupleU32 checkedTupleU32Fn
    checkedTupleMulOvS0.frame.locals checkedTupleU32Fn.start

theorem checkedTupleMulOv_anneal_ret :
    ReachesRet (mirCallTree checkedTupleU32 checkedTupleMulOvArgs)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.aggregate 0 [.scalar ⟨0, 4⟩, .scalar ⟨1, 1⟩], checkedTupleMulOvS0.memory)) :=
  runA_sound checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleMulOv_noUB :
    MirNoUBTree (mirCallTree checkedTupleU32 checkedTupleMulOvArgs) :=
  runA_noUB checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleMulOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedTupleMulOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocTupleU32 with data := tupleBytes u32 0 1 } ∧
      m'.threads = [thread1 ctxTupleU32 [{ callerFrameTupleU32 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedTupleU32_inFragment checkedTupleU32_translate ctxTupleU32
      (ctxTupleU32_ok rfl) checkedTupleMulOvArgs (by decide) checkedTupleMulOvMInit
      rfl rfl rfl checkedTupleMulOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedTupleU32] at hd; subst hd
  simp [retPtr, ctxTupleU32] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxTupleU32] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedTupleMulOv_minirust_direct :
    (Interp.steps 9 checkedTupleMulOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocTupleU32 with data := tupleBytes u32 0 1 }, [1]) := rfl

/-- No-overflow input `(10u32, 3u32)`: `10 - 3 = (7, false)`, `7 * 3 = (21, false)`,
repackaged via `Aggregate(Tuple)` and returned as `tupleBytes u32 21 0`. -/
def checkedTupleOkArgs : List Value := [.scalar ⟨10, 4⟩, .scalar ⟨3, 4⟩]
def checkedTupleOkS0 : MachineState :=
  initMachineState checkedTupleU32 checkedTupleOkArgs
def checkedTupleOkMInit : Mach :=
  machineWithCtx ctxTupleU32 checkedTupleU32 checkedTupleU32Fn
    checkedTupleOkS0.frame.locals checkedTupleU32Fn.start

theorem checkedTupleOk_anneal_ret :
    ReachesRet (mirCallTree checkedTupleU32 checkedTupleOkArgs)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.aggregate 0 [.scalar ⟨21, 4⟩, .scalar ⟨0, 1⟩], checkedTupleOkS0.memory)) :=
  runA_sound checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleOk_noUB :
    MirNoUBTree (mirCallTree checkedTupleU32 checkedTupleOkArgs) :=
  runA_noUB checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedTupleOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocTupleU32 with data := tupleBytes u32 21 0 } ∧
      m'.threads = [thread1 ctxTupleU32 [{ callerFrameTupleU32 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedTupleU32_inFragment checkedTupleU32_translate ctxTupleU32
      (ctxTupleU32_ok rfl) checkedTupleOkArgs (by decide) checkedTupleOkMInit
      rfl rfl rfl checkedTupleOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedTupleU32] at hd; subst hd
  simp [retPtr, ctxTupleU32] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxTupleU32] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedTupleOk_minirust_direct :
    (Interp.steps 9 checkedTupleOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocTupleU32 with data := tupleBytes u32 21 0 }, [1]) := rfl

/-! ### Reading `.0` or `.1` from an uninitialized `(u32, bool)` tuple local -/

theorem ctxTupleU32_ok1 {body : CapturedMir}
    (h : body.localDecls = [u32BoolTupleDecl]) : CtxOk body ctxTupleU32 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | _ + 1, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocTupleU32, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR of `fn uninit_tuple_field0() -> (u32, bool)` whose entry block reads
`_0.0` from the uninitialized `(u32, bool)` return place `_0`
(`_0 = AddWithOverflow(copy (_0.0), const 1u32)`), raising UB in both Anneal and
MiniRust. -/
def uninitTupleField0 : CapturedMir where
  defPath := "witness::uninit_tuple_field0"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .addWithOverflow (.copy (field0U32 0)) (constU32 1)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem uninitTupleField0_inFragment : inFragment uninitTupleField0 = true := by decide

def uninitTupleField0Fn : Gen.Function where
  locals := ⟨[(localName 0, intBoolTupleTy u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.IntWithOverflow .Add)
          (.Load (.Field (.Local (localName 0)) 0))
          (.Constant (.Int 1) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitTupleField0_translate : translateFn uninitTupleField0 = some uninitTupleField0Fn := rfl

def uninitTupleField0S0 : MachineState := initMachineState uninitTupleField0 []
def uninitTupleField0MInit : Mach :=
  machineWithCtx ctxTupleU32 uninitTupleField0 uninitTupleField0Fn
    uninitTupleField0S0.frame.locals uninitTupleField0Fn.start

theorem uninitTupleField0_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitTupleField0 []) tr u ∧ FaultNow u :=
  faultsA_sound uninitTupleField0 3 _ (by decide)

theorem uninitTupleField0_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitTupleField0MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitTupleField0_anneal_ub
  exact mirCall_ub uninitTupleField0_inFragment uninitTupleField0_translate ctxTupleU32
    (ctxTupleU32_ok1 rfl) [] (by decide) uninitTupleField0MInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitTupleField0_minirust_direct :
    Interp.steps 2 uninitTupleField0MInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

theorem uninitTupleField0_converse_error :
    (∃ msg, Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree uninitTupleField0 []) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 2 ∧ Interp.steps k uninitTupleField0MInit = .ok mRet ∧
      ReturnRel uninitTupleField0 ctxTupleU32 s' v mRet ∧
      ReachesRet (mirCallTree uninitTupleField0 []) tr (.normal (v, mem))) :=
  mirCall_steps_error uninitTupleField0_inFragment uninitTupleField0_translate ctxTupleU32
    (ctxTupleU32_ok1 rfl) [] (by decide) uninitTupleField0MInit rfl rfl rfl
    uninitTupleField0_minirust_direct

/-- MIR of `fn uninit_tuple_field1() -> (u32, bool)` whose entry block switches
on `_0.1` (at offset `4`) from the uninitialized `(u32, bool)` return place
`_0`, raising UB in both Anneal and MiniRust. -/
def uninitTupleField1 : CapturedMir where
  defPath := "witness::uninit_tuple_field1"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32BoolTupleDecl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (field1 0)) { branches := [(0, 1)], otherwise := 1 }),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem uninitTupleField1_inFragment : inFragment uninitTupleField1 = true := by decide

def uninitTupleField1Fn : Gen.Function where
  locals := ⟨[(localName 0, intBoolTupleTy u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[],
      .Switch
        (.UnOp (.Cast (.Transmute (.Int u8)))
          (.Load (.Field (.Local (localName 0)) 1)))
        ⟨[(0, bbName 1)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[], .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 2
  implicit_writes := true

theorem uninitTupleField1_translate : translateFn uninitTupleField1 = some uninitTupleField1Fn := rfl

def uninitTupleField1S0 : MachineState := initMachineState uninitTupleField1 []
def uninitTupleField1MInit : Mach :=
  machineWithCtx ctxTupleU32 uninitTupleField1 uninitTupleField1Fn
    uninitTupleField1S0.frame.locals uninitTupleField1Fn.start

theorem uninitTupleField1_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitTupleField1 []) tr u ∧ FaultNow u :=
  faultsA_sound uninitTupleField1 3 _ (by decide)

theorem uninitTupleField1_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitTupleField1MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitTupleField1_anneal_ub
  exact mirCall_ub uninitTupleField1_inFragment uninitTupleField1_translate ctxTupleU32
    (ctxTupleU32_ok1 rfl) [] (by decide) uninitTupleField1MInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitTupleField1_minirust_direct :
    Interp.steps 2 uninitTupleField1MInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

theorem uninitTupleField1_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen uninitTupleField1 + n) uninitTupleField1MInit = .ok m' ∧
      StateRel uninitTupleField1 uninitTupleField1Fn ctxTupleU32 s' m' ∧
      Reaches (mirCallTree uninitTupleField1 []) tr
        (mirTree uninitTupleField1 s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen uninitTupleField1 + n ∧
      Interp.steps k uninitTupleField1MInit = .ok mRet ∧
      ReturnRel uninitTupleField1 ctxTupleU32 s' v mRet ∧
      ReachesRet (mirCallTree uninitTupleField1 []) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen uninitTupleField1 + n) uninitTupleField1MInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree uninitTupleField1 []) tr u ∧ FaultNow u) :=
  mirCall_outcome uninitTupleField1_inFragment uninitTupleField1_translate ctxTupleU32
    (ctxTupleU32_ok1 rfl) [] (by decide) uninitTupleField1MInit rfl rfl rfl n

/-! ### Ground truth for `IntType::with_overflow`, `BinOpIntWithOverflow`, `ValueExpr::Tuple`, and `PlaceExpr::Field` -/

/-- `IntType::with_overflow` layout on `i8` (size `2`, align `1`, no trailing
padding) and on `u32` (size `8`, align `4`, field `0` at offset `0`, field `1`
at offset `4`, and `3` trailing `AbstractByte::Uninit` padding bytes). -/
theorem withOverflow_i8_layout :
    IntType.with_overflow i8 = .ok (intBoolTupleTy i8) ∧
      Type.layout (intBoolTupleTy i8) = .ok (.Sized ⟨2⟩ ⟨1⟩) := ⟨rfl, rfl⟩

theorem withOverflow_u32_layout :
    IntType.with_overflow u32 = .ok (intBoolTupleTy u32) ∧
      Type.layout (intBoolTupleTy u32) = .ok (.Sized ⟨8⟩ ⟨4⟩) ∧
      Type.encode (intBoolTupleTy u32) (.Tuple [.Int 0x01020304, .Bool true]) =
        .ok [.Init 4 none, .Init 3 none, .Init 2 none, .Init 1 none,
             .Init 1 none, .Uninit, .Uninit, .Uninit] := ⟨rfl, rfl, rfl⟩

/-- `TupleHeadLayout::full_size_and_align` and `LayoutStrategy::compute_size_and_align`
handle both `Sized` (`tail = none`) and `Unsized` (`Slice` / `TraitObject`) layouts. -/
theorem tupleHeadLayout_full_sized_and_slice :
    TupleHeadLayout.full_size_and_align ⟨⟨5⟩, ⟨4⟩, none⟩ ⟨0⟩ ⟨1⟩ = (⟨8⟩, ⟨4⟩) ∧
      TupleHeadLayout.full_size_and_align ⟨⟨5⟩, ⟨4⟩, some ⟨2⟩⟩ ⟨6⟩ ⟨2⟩ = (⟨12⟩, ⟨4⟩) ∧
      LayoutStrategy.compute_size_and_align (vtableLookup checkedTupleOkMInit)
        (.Slice ⟨2⟩ ⟨2⟩) (some (.ElementCount 3)) = .ok (⟨6⟩, ⟨2⟩) := ⟨rfl, rfl, rfl⟩

/-- `TupleHeadLayout::{capped_tail_align, tail_offset}` when `packed_align`
genuinely caps `tail_align` (`min 4 1 = 1`, placing the tail at offset `5`
instead of `8`), and `LayoutStrategy::compute_size_and_align` on `Tuple`,
`TraitObject`, mismatched pointer metadata (`specPanic`), and negative slice
count (`specPanic`). -/
theorem cappedTailAlign_and_computeSizeAndAlign_all_branches :
    TupleHeadLayout.capped_tail_align ⟨⟨5⟩, ⟨1⟩, some ⟨1⟩⟩ ⟨4⟩ = ⟨1⟩ ∧
    TupleHeadLayout.tail_offset ⟨⟨5⟩, ⟨1⟩, some ⟨1⟩⟩ ⟨4⟩ = ⟨5⟩ ∧
    TupleHeadLayout.tail_offset ⟨⟨5⟩, ⟨1⟩, none⟩ ⟨4⟩ = ⟨8⟩ ∧
    LayoutStrategy.compute_size_and_align (vtableLookup checkedTupleOkMInit)
      (.Tuple ⟨⟨5⟩, ⟨4⟩, none⟩ (.Slice ⟨2⟩ ⟨2⟩)) (some (.ElementCount 3)) =
      .ok (⟨12⟩, ⟨4⟩) ∧
    LayoutStrategy.compute_size_and_align
      (fun _ => .ok { trait_name := ⟨⟨0⟩⟩, size := ⟨24⟩, align := ⟨8⟩, cells := [], methods := ⟨[]⟩ })
      (.TraitObject ⟨⟨0⟩⟩)
      (some (.VTablePointer { addr := 64, provenance := none })) =
      .ok (⟨24⟩, ⟨8⟩) ∧
    LayoutStrategy.compute_size_and_align (vtableLookup checkedTupleOkMInit)
      (.Sized ⟨4⟩ ⟨4⟩) (some (.ElementCount 1)) =
      .error (.specPanic "pointer meta data does not match type") ∧
    LayoutStrategy.compute_size_and_align (vtableLookup checkedTupleOkMInit)
      (.Slice ⟨2⟩ ⟨2⟩) (some (.ElementCount (-1))) =
      .error (.specPanic "Size::from_bytes(count * elem_size.bytes()).unwrap()") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Direct ground-truth evaluations of `evalBinOp (.IntWithOverflow ..)` on
`INT_MAX + 1`, `INT_MIN - 1`, `UINT_MAX + 1`, `0 - 1`, and signed/unsigned
multiplication overflow. -/
theorem evalBinOp_addWithOverflow_i8_max :
    evalBinOp (.IntWithOverflow .Add) (.Int 127, .Int i8) (.Int 1, .Int i8) =
      .ok (.Tuple [.Int (-128), .Bool true], intBoolTupleTy i8) := rfl

theorem evalBinOp_subWithOverflow_i8_min :
    evalBinOp (.IntWithOverflow .Sub) (.Int (-128), .Int i8) (.Int 1, .Int i8) =
      .ok (.Tuple [.Int 127, .Bool true], intBoolTupleTy i8) := rfl

theorem evalBinOp_addWithOverflow_u32_max :
    evalBinOp (.IntWithOverflow .Add) (.Int 4294967295, .Int u32) (.Int 1, .Int u32) =
      .ok (.Tuple [.Int 0, .Bool true], intBoolTupleTy u32) := rfl

theorem evalBinOp_subWithOverflow_u32_zero :
    evalBinOp (.IntWithOverflow .Sub) (.Int 0, .Int u32) (.Int 1, .Int u32) =
      .ok (.Tuple [.Int 4294967295, .Bool true], intBoolTupleTy u32) := rfl

theorem evalBinOp_mulWithOverflow_i8_min :
    evalBinOp (.IntWithOverflow .Mul) (.Int (-128), .Int i8) (.Int (-1), .Int i8) =
      .ok (.Tuple [.Int (-128), .Bool true], intBoolTupleTy i8) := rfl

theorem evalBinOp_mulWithOverflow_u32 :
    evalBinOp (.IntWithOverflow .Mul) (.Int 65536, .Int u32) (.Int 65536, .Int u32) =
      .ok (.Tuple [.Int 0, .Bool true], intBoolTupleTy u32) := rfl

/-- `ptrOffsetInbounds` offsets a valid pointer within its live allocation and
rejects out-of-bounds or negative offsets with UB, and `evalValue` / `evalPlace`
evaluate `ValueExpr::Tuple` and `PlaceExpr::Field` on `(u32, bool)`. -/
theorem ptrOffsetInbounds_ok_and_oob :
    ptrOffsetInbounds checkedTupleOkMInit
      { addr := 384, provenance := some (⟨3⟩, ()) } 4 =
      .ok { addr := 388, provenance := some (⟨3⟩, ()) } ∧
    ptrOffsetInbounds checkedTupleOkMInit
      { addr := 384, provenance := some (⟨3⟩, ()) } 9 =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    ptrOffsetInbounds checkedTupleOkMInit
      { addr := 384, provenance := some (⟨3⟩, ()) } (-1) =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") := ⟨rfl, rfl, rfl⟩

theorem evalValue_tuple_and_evalPlace_field :
    evalValue checkedTupleOkMInit
      (.Tuple [.Constant (.Int 42) (.Int u32), .Constant (.Bool true) .Bool]
        (intBoolTupleTy u32)) =
      .ok ((.Tuple [.Int 42, .Bool true], intBoolTupleTy u32), checkedTupleOkMInit) ∧
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 0)) 0) =
      .ok ({ ptr := { thin_pointer := { addr := 128, provenance := some (⟨1⟩, ()) }, metadata := none },
             aligned := true }, .Int u32) ∧
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 0)) 1) =
      .ok ({ ptr := { thin_pointer := { addr := 132, provenance := some (⟨1⟩, ()) }, metadata := none },
             aligned := true }, .Bool) := ⟨rfl, rfl, rfl⟩

/-- `evalBinOp (.IntWithOverflow ..)` on a non-integer operand and `evalPlace (.Field ..)`
on an out-of-range field index, a missing unsized tail, or a non-projectable
type raise the exact upstream `specPanic`s from `spec/lang/step/{operators,expressions}.md`. -/
theorem evalBinOp_intWithOverflow_nonInt_panics :
    evalBinOp (.IntWithOverflow .Add) (.Bool true, .Bool) (.Bool false, .Bool) =
      .error (.specPanic "non-integer input to integer operation") := rfl

theorem evalPlace_field_panics :
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 0)) 2) =
      .error (.specPanic "field projection to non-existing unsized tail") ∧
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 0)) 3) =
      .error (.specPanic "field projection to invalid field") ∧
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 0)) (-1)) =
      .error (.specPanic "field projection to invalid field") ∧
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 1)) 0) =
      .error (.specPanic "field projection on non-projectable type") := ⟨rfl, rfl, rfl, rfl⟩

/-- `IntType::with_overflow` and `evalBinOp (.IntWithOverflow ..)` across the
remaining integer widths (`u8`, `i16`, `u16`, `i32`, `i64`/`isize`,
`u64`/`usize`, `i128`, `u128`), including 16-byte `(i64, bool)` (`7` trailing
padding bytes) and 32-byte `(u128, bool)` (`15` trailing padding bytes). -/
def i16W : Gen.IntType := ⟨.Signed, ⟨2⟩⟩
def u16W : Gen.IntType := ⟨.Unsigned, ⟨2⟩⟩
def i32W : Gen.IntType := ⟨.Signed, ⟨4⟩⟩
def i64W : Gen.IntType := ⟨.Signed, ⟨8⟩⟩
def u64W : Gen.IntType := ⟨.Unsigned, ⟨8⟩⟩
def i128W : Gen.IntType := ⟨.Signed, ⟨16⟩⟩
def u128W : Gen.IntType := ⟨.Unsigned, ⟨16⟩⟩

theorem evalBinOp_withOverflow_all_widths :
    Type.layout (intBoolTupleTy i64W) = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    Type.layout (intBoolTupleTy u128W) = .ok (.Sized ⟨32⟩ ⟨16⟩) ∧
    evalBinOp (.IntWithOverflow .Add) (.Int 255, .Int u8Ty) (.Int 1, .Int u8Ty) =
      .ok (.Tuple [.Int 0, .Bool true], intBoolTupleTy u8Ty) ∧
    evalBinOp (.IntWithOverflow .Sub) (.Int (-32768), .Int i16W) (.Int 1, .Int i16W) =
      .ok (.Tuple [.Int 32767, .Bool true], intBoolTupleTy i16W) ∧
    evalBinOp (.IntWithOverflow .Add) (.Int 65535, .Int u16W) (.Int 1, .Int u16W) =
      .ok (.Tuple [.Int 0, .Bool true], intBoolTupleTy u16W) ∧
    evalBinOp (.IntWithOverflow .Add) (.Int 2147483647, .Int i32W) (.Int 1, .Int i32W) =
      .ok (.Tuple [.Int (-2147483648), .Bool true], intBoolTupleTy i32W) ∧
    evalBinOp (.IntWithOverflow .Sub)
      (.Int (-9223372036854775808), .Int i64W) (.Int 1, .Int i64W) =
      .ok (.Tuple [.Int 9223372036854775807, .Bool true], intBoolTupleTy i64W) ∧
    evalBinOp (.IntWithOverflow .Add)
      (.Int 18446744073709551615, .Int u64W) (.Int 1, .Int u64W) =
      .ok (.Tuple [.Int 0, .Bool true], intBoolTupleTy u64W) ∧
    evalBinOp (.IntWithOverflow .Sub)
      (.Int (-(2 ^ 127)), .Int i128W) (.Int 1, .Int i128W) =
      .ok (.Tuple [.Int (2 ^ 127 - 1), .Bool true], intBoolTupleTy i128W) ∧
    evalBinOp (.IntWithOverflow .Sub)
      (.Int 0, .Int u128W) (.Int 1, .Int u128W) =
      .ok (.Tuple [.Int (2 ^ 128 - 1), .Bool true], intBoolTupleTy u128W) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `evalPlace (.Field ..)` on `Type::Union` (`unionPaddedTy`, projecting field
`0` at offset `0` with type `.Int i8` and field `1` at offset `2` with type
`.Bool`) and the `offset <= self.compute_size(...)` assertion `specPanic` when a
malformed tuple's field offset (`16`) exceeds the tuple's head size (`8`). -/
def unionFieldTestMach : Mach :=
  machineWithCtx ctxTupleU32 checkedTupleU32
    { checkedTupleU32Fn with
      locals := ⟨[(localName 0, unionPaddedTy),
                  (localName 1, .Tuple [(⟨16⟩, .Int u32)] ⟨⟨8⟩, ⟨4⟩, none⟩ none)]⟩ }
    checkedTupleOkS0.frame.locals (bbName 0)

theorem evalPlace_field_union_and_offset_panic :
    evalPlace unionFieldTestMach (.Field (.Local (localName 0)) 0) =
      .ok ({ ptr := { thin_pointer := { addr := 128, provenance := some (⟨1⟩, ()) }, metadata := none },
             aligned := true }, .Int i8) ∧
    evalPlace unionFieldTestMach (.Field (.Local (localName 0)) 1) =
      .ok ({ ptr := { thin_pointer := { addr := 130, provenance := some (⟨1⟩, ()) }, metadata := none },
             aligned := true }, .Bool) ∧
    evalPlace unionFieldTestMach (.Field (.Local (localName 1)) 0) =
      .error (.specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)") :=
  ⟨rfl, rfl, rfl⟩


/-! ## Temporaries, storage markers, `move`, `Deinit`, and the init block

MR-1.3 bodies with temporaries beyond the arguments. `tempMove` exercises
`StorageLive`/`StorageDead` of `u32` and `bool` temporaries, a root `move` in
a `BinaryOp` operand, in a `Use`, and in a `switchInt` discriminant (Anneal
de-initializes the moved-from local; MiniRust's `move` is a plain load, which
`StaleOk` reconciles), `Deinit` of a moved-from local, and a temporary without
storage markers that `minimize`'s init block allocates (`_4`, never
mentioned). Its first-fit stack addresses (`allocCandidate`) show `StorageLive`
reusing the address that `StorageDead` released. `deadRead` reads a local
after `StorageDead` (UB in both models), and `moveReuse` is a body that
`movesOk` rejects because it reads a local after moving out of it. -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn temp_move(x: u32) -> u32 {
    let y = (x + 1) * 2;
    if y == 8 { 100 } else { y }
}
```
with the temporaries spelled out:
```text
bb0: StorageLive(_2); _2 = Add(copy _1, const 1_u32);
     StorageLive(_3); _3 = Mul(move _2, const 2_u32); StorageDead(_2);
     _0 = move _3; Deinit(_3); StorageDead(_3);
     StorageLive(_5); _5 = Eq(copy _0, const 8_u32);
     switchInt(move _5) -> [0: bb1, otherwise: bb2]
bb1: StorageDead(_5); return
bb2: StorageDead(_5); _0 = const 100_u32; return
```
`_4: u32` has no storage markers and no uses. -/
def tempMove : CapturedMir where
  defPath := "witness::temp_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl, u32Decl, u32Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.binaryOp .add (.copy (local_ 1)) (constU32 1))),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.binaryOp .mul (.move (local_ 2)) (constU32 2))),
        mkStmt (.storageDead 2),
        mkStmt (.assign (local_ 0) (.use (.move (local_ 3)))),
        mkStmt (.deinit (local_ 3)),
        mkStmt (.storageDead 3),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.binaryOp .eq (.copy (local_ 0)) (constU32 8)))],
      terminator := mkTerm (.switchInt (.move (local_ 5)) { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [mkStmt (.storageDead 5)], terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.storageDead 5), mkStmt (.assign (local_ 0) (.use (constU32 100)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem tempMove_inFragment : inFragment tempMove = true := by decide

/-- `_4` is the only temporary without storage markers. -/
theorem tempMove_alwaysLive : alwaysStorageLiveLocals tempMove = [4] := by decide

/-- The MiniRust function `minimize` produces for `tempMove`, spelled out:
`move` operands translate like `copy` operands (`Load`), and the init block
`bb3` allocates `_4`. -/
def tempMoveFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, .Int u32), (localName 4, .Int u32), (localName 5, .Bool)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Add) (.Load (.Local (localName 1))) (.Constant (.Int 1) (.Int u32))),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Mul) (.Load (.Local (localName 2))) (.Constant (.Int 2) (.Int u32))),
      .StorageDead (localName 2),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 3))),
      .Deinit (.Local (localName 3)),
      .StorageDead (localName 3),
      .StorageLive (localName 5),
      .Assign (.Local (localName 5))
        (.BinOp (.Rel .Eq) (.Load (.Local (localName 0))) (.Constant (.Int 8) (.Int u32)))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 5))))
        ⟨[(0, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[.StorageDead (localName 5)], .Return, .Regular⟩),
    (bbName 2, ⟨[.StorageDead (localName 5),
      .Assign (.Local (localName 0)) (.Constant (.Int 100) (.Int u32))], .Return, .Regular⟩),
    (bbName 3, ⟨[.StorageLive (localName 4)], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem tempMove_translate : translateFn tempMove = some tempMoveFn := rfl

theorem ctx0_ok_tempMove : CtxOk tempMove ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [tempMove] at hd; subst hd; decide
    | 1, _, hd => simp [tempMove] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [tempMove] at hi
  ret := by
    intro d hd
    simp [tempMove] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-! ### `temp_move(3)`: `y == 8`, returns `100` -/

def tempMove3S0 : MachineState := initMachineState tempMove [.scalar ⟨3, 4⟩]
def tempMove3MInit : Mach := machine tempMove tempMoveFn tempMove3S0.frame.locals tempMoveFn.start

/-- The init block takes two MiniRust steps: `StorageLive(_4)` and
`Goto(bb0)`. -/
theorem tempMove_initLen : initLen tempMove = 2 := by decide

def tempMove3Trace : List (Event MirEffect) := [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]

theorem tempMove3_anneal_ret :
    ReachesRet (mirTree tempMove tempMove3S0) tempMove3Trace
      (.normal (.scalar ⟨100, 4⟩, tempMove3S0.memory)) :=
  runA_sound tempMove 30 _ _ _ rfl

theorem tempMove3_noUB : MirNoUBTree (mirCallTree tempMove [.scalar ⟨3, 4⟩]) :=
  runA_noUB tempMove 30 _ _ _ rfl

theorem tempMove3_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n tempMove3MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 100 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret tempMove_inFragment tempMove_translate ctx0 ctx0_ok_tempMove [.scalar ⟨3, 4⟩]
      (by decide) tempMove3MInit rfl rfl rfl tempMove3_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [tempMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- The same return, computed directly (16 MiniRust steps: the two init-block
steps and one per Anneal step). Every callee allocation is dead afterwards,
including the init block's `_4`; the first-fit addresses show `_4` at
`2^32`, `_2` at `2 * 2^32`, `_3` at `3 * 2^32`, and `_5` reusing `2 * 2^32`
after `StorageDead(_2)`. -/
theorem tempMove3_minirust_direct :
    (Interp.steps 16 tempMove3MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live), m.mem.memory.allocations.map (·.addr))) =
      some (some { retAlloc with data := scalarBytes u32 100 }, [1],
        [true, false, false, false, false, false, false],
        [64, 128, 256, 2 ^ 32, 2 * 2 ^ 32, 3 * 2 ^ 32, 2 * 2 ^ 32]) := by
  decide +kernel

/-! ### `temp_move(2)`: `y == 6`, returns `6` -/

def tempMove2S0 : MachineState := initMachineState tempMove [.scalar ⟨2, 4⟩]
def tempMove2MInit : Mach := machine tempMove tempMoveFn tempMove2S0.frame.locals tempMoveFn.start

def tempMove2Trace : List (Event MirEffect) := [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]

theorem tempMove2_anneal_ret :
    ReachesRet (mirTree tempMove tempMove2S0) tempMove2Trace
      (.normal (.scalar ⟨6, 4⟩, tempMove2S0.memory)) :=
  runA_sound tempMove 30 _ _ _ rfl

theorem tempMove2_noUB : MirNoUBTree (mirCallTree tempMove [.scalar ⟨2, 4⟩]) :=
  runA_noUB tempMove 30 _ _ _ rfl

theorem tempMove3_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen tempMove + n) tempMove3MInit = .ok m' ∧
      StateRel tempMove tempMoveFn ctx0 s' m' ∧
      Reaches (mirCallTree tempMove [.scalar ⟨3, 4⟩]) tr (mirTree tempMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen tempMove + n ∧
      Interp.steps k tempMove3MInit = .ok mRet ∧
      ReturnRel tempMove ctx0 s' v mRet ∧
      ReachesRet (mirCallTree tempMove [.scalar ⟨3, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress tempMove_inFragment tempMove_translate ctx0 ctx0_ok_tempMove [.scalar ⟨3, 4⟩]
    (by decide) tempMove3MInit rfl rfl rfl tempMove3_noUB n

theorem tempMove2_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n tempMove2MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret tempMove_inFragment tempMove_translate ctx0 ctx0_ok_tempMove [.scalar ⟨2, 4⟩]
      (by decide) tempMove2MInit rfl rfl rfl tempMove2_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [tempMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem tempMove2_minirust_direct :
    (Interp.steps 15 tempMove2MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live))) =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1],
        [true, false, false, false, false, false, false]) := by
  decide +kernel

/-! ### Reading a local after `StorageDead` -/

/-- MIR of `StorageLive(_1); _1 = const 5_u32; StorageDead(_1); _0 = copy _1;
return`, which reads the dead temporary `_1`. -/
def deadRead : CapturedMir where
  defPath := "witness::dead_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (constU32 5))),
        mkStmt (.storageDead 1),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem deadRead_inFragment : inFragment deadRead = true := by decide

def deadReadFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .Assign (.Local (localName 1)) (.Constant (.Int 5) (.Int u32)),
      .StorageDead (localName 1),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deadRead_translate : translateFn deadRead = some deadReadFn := rfl

def deadReadS0 : MachineState := initMachineState deadRead []
def deadReadMInit : Mach := machine deadRead deadReadFn deadReadS0.frame.locals deadReadFn.start

theorem deadRead_anneal_ub : ∃ tr u, Reaches (mirTree deadRead deadReadS0) tr u ∧ FaultNow u :=
  faultsA_sound deadRead 10 _ (by decide)

theorem deadRead_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n deadReadMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := deadRead_anneal_ub
  exact mirCall_ub deadRead_inFragment deadRead_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadReadMInit rfl rfl rfl hr hf

/-- Direct computation: the fifth MiniRust step (the init block's `Goto`, then
three statements) raises the UB of loading a dead local. -/
theorem deadRead_minirust_direct :
    (match Interp.steps 5 deadReadMInit with
      | .error (.ub msg) => some msg
      | _ => none) = some "access to a dead local" := by
  decide +kernel

theorem deadRead_steps5_ub :
    Interp.steps 5 deadReadMInit = .error (.ub "access to a dead local") := by
  have h := deadRead_minirust_direct
  revert h
  cases Interp.steps 5 deadReadMInit with
  | ok _ => simp
  | error e => cases e <;> simp

theorem deadRead_converse_error :
    (∃ msg, Stop.ub "access to a dead local" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree deadRead []) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 5 ∧ Interp.steps k deadReadMInit = .ok mRet ∧
      ReturnRel deadRead ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadRead []) tr (.normal (v, mem))) :=
  mirCall_steps_error deadRead_inFragment deadRead_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadReadMInit rfl rfl rfl deadRead_steps5_ub

theorem deadRead_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen deadRead + n) deadReadMInit = .ok m' ∧
      StateRel deadRead deadReadFn ctx0 s' m' ∧
      Reaches (mirCallTree deadRead []) tr (mirTree deadRead s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen deadRead + n ∧
      Interp.steps k deadReadMInit = .ok mRet ∧
      ReturnRel deadRead ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadRead []) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen deadRead + n) deadReadMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree deadRead []) tr u ∧ FaultNow u) :=
  mirCall_outcome deadRead_inFragment deadRead_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadReadMInit rfl rfl rfl n

/-! ### A body that `movesOk` rejects -/

/-- MIR of `StorageLive(_2); _2 = copy _1; _0 = move _2; _0 = copy _2;
StorageDead(_2); return` for `fn(u32) -> u32`: Anneal de-initializes `_2` at
the `move` (so the second read is UB), while MiniRust's `move` is a plain load
(so the second read succeeds). `movesOk` rejects the body, so the
correspondence theorem claims nothing about it. -/
def moveReuse : CapturedMir where
  defPath := "witness::move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 0) (.use (.move (local_ 2)))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 2)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem moveReuse_movesOk : movesOk moveReuse = false := by decide

theorem moveReuse_not_inFragment : inFragment moveReuse = false := by decide

/-- The two models indeed disagree on `moveReuse(7)`: Anneal faults, while
MiniRust's run of the translated body returns `7`. -/
def moveReuseFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.Load (.Local (localName 1))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 2))),
      .StorageDead (localName 2)], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem moveReuse_translate : translateFn moveReuse = some moveReuseFn := rfl

def moveReuse7S0 : MachineState := initMachineState moveReuse [.scalar ⟨7, 4⟩]

theorem moveReuse7_anneal_ub :
    ∃ tr u, Reaches (mirTree moveReuse moveReuse7S0) tr u ∧ FaultNow u :=
  faultsA_sound moveReuse 10 _ (by decide)

theorem moveReuse7_minirust_direct :
    (Interp.steps 7 (machine moveReuse moveReuseFn moveReuse7S0.frame.locals
        moveReuseFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 7 }, [1]) := by
  decide +kernel

/-! ### Cross-block moves, argument moves, projected tuple moves, live re-allocation, and idempotent `StorageDead`

`crossBlockMove` exercises the CFG-aware `movesOk` dataflow analysis across
`Goto` and `SwitchInt` edges:
* moving the incoming function argument `_1` in `bb0`
  (`_2 = AddWithOverflow(move _1, const 10_u32)`), which a block-insensitive
  `movedLocals` check would reject;
* projected tuple moves `move (_2.0)` (in `Use`) and `move (_2.1)` (as a `bool`
  `SwitchInt` discriminant), which leave `_2: (u32, bool)` initialized in both
  models (`opMoved (.move ⟨2, [.field ..]⟩) = none`);
* carrying live temporaries `_2` and `_3` initialized in `bb0` across
  `Goto(bb1)` and `SwitchInt -> [0: bb2, otherwise: bb3]` before moving `_3` in
  `bb1` and `bb2`;
* calling `StorageLive(_1)` and `StorageLive(_3)` on already-live locals without
  an intervening `StorageDead`, exercising `StackFrame::storage_live`'s initial
  `self.storage_dead(mem, local)?` deallocation and clearing their moved marks;
* `Deinit(_2)` on a `(u32, bool)` 2-tuple local;
* idempotent `StorageDead(_2)` on an already-dead local
  (`if let Some(ptr) = self.locals.remove(local)`). -/
def crossBlockMove : CapturedMir where
  defPath := "witness::cross_block_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32BoolTupleDecl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.binaryOp .addWithOverflow (.move (local_ 1)) (constU32 10))),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.use (.move (field0U32 2))))],
      terminator := mkTerm (.goto 1),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (.move (local_ 3)))),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.binaryOp .add (.move (local_ 1)) (constU32 5)))],
      terminator := mkTerm (.switchInt (.move (field1 2)) { branches := [(0, 2)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.deinit (local_ 2)),
        mkStmt (.storageDead 2),
        mkStmt (.storageDead 2),
        mkStmt (.assign (local_ 0) (.use (.move (local_ 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_,
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 2),
        mkStmt (.storageDead 3),
        mkStmt (.assign (local_ 0) (.use (constU32 0)))],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem crossBlockMove_inFragment : inFragment crossBlockMove = true := by decide

/-- Forward CFG dataflow `movedAtEntry` for `crossBlockMove`: `bb0` starts with
`[]`, while `bb1`, `bb2`, and `bb3` have `[1]` moved out on entry (`_3` is
initialized in `bb0`, moved in `bb1`, and re-allocated/initialized in `bb1`
before reaching `bb2`). -/
theorem crossBlockMove_movedAtEntry :
    [0, 1, 2, 3].map (movedAtEntry crossBlockMove) = [[], [1], [1], [1]] := by decide

def crossBlockMoveFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, intBoolTupleTy u32), (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2))
        (.BinOp (.IntWithOverflow .Add) (.Load (.Local (localName 1))) (.Constant (.Int 10) (.Int u32))),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3)) (.Load (.Field (.Local (localName 2)) 0))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .StorageLive (localName 1),
      .Assign (.Local (localName 1)) (.Load (.Local (localName 3))),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Add) (.Load (.Local (localName 1))) (.Constant (.Int 5) (.Int u32)))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Field (.Local (localName 2)) 1)))
        ⟨[(0, bbName 2)]⟩ (bbName 3), .Regular⟩),
    (bbName 2, ⟨[
      .Deinit (.Local (localName 2)),
      .StorageDead (localName 2),
      .StorageDead (localName 2),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 3))),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 3, ⟨[
      .StorageDead (localName 2),
      .StorageDead (localName 3),
      .Assign (.Local (localName 0)) (.Constant (.Int 0) (.Int u32))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem crossBlockMove_translate : translateFn crossBlockMove = some crossBlockMoveFn := rfl

theorem ctx0_ok_crossBlockMove : CtxOk crossBlockMove ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [crossBlockMove] at hd; subst hd; decide
    | 1, _, hd => simp [crossBlockMove] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [crossBlockMove] at hi
  ret := by
    intro d hd
    simp [crossBlockMove] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def crossBlockMove20S0 : MachineState := initMachineState crossBlockMove [.scalar ⟨20, 4⟩]
def crossBlockMove20MInit : Mach :=
  machine crossBlockMove crossBlockMoveFn crossBlockMove20S0.frame.locals crossBlockMoveFn.start

theorem crossBlockMove20_anneal_ret :
    ReachesRet (mirTree crossBlockMove crossBlockMove20S0)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨35, 4⟩, crossBlockMove20S0.memory)) :=
  runA_sound crossBlockMove 30 _ _ _ rfl

theorem crossBlockMove20_noUB : MirNoUBTree (mirCallTree crossBlockMove [.scalar ⟨20, 4⟩]) :=
  runA_noUB crossBlockMove 30 _ _ _ rfl

theorem crossBlockMove20_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen crossBlockMove + n) crossBlockMove20MInit = .ok m' ∧
      StateRel crossBlockMove crossBlockMoveFn ctx0 s' m' ∧
      Reaches (mirCallTree crossBlockMove [.scalar ⟨20, 4⟩]) tr (mirTree crossBlockMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen crossBlockMove + n ∧
      Interp.steps k crossBlockMove20MInit = .ok mRet ∧
      ReturnRel crossBlockMove ctx0 s' v mRet ∧
      ReachesRet (mirCallTree crossBlockMove [.scalar ⟨20, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress crossBlockMove_inFragment crossBlockMove_translate ctx0 ctx0_ok_crossBlockMove
    [.scalar ⟨20, 4⟩] (by decide) crossBlockMove20MInit rfl rfl rfl crossBlockMove20_noUB n

theorem crossBlockMove20_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n crossBlockMove20MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 35 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret crossBlockMove_inFragment crossBlockMove_translate ctx0 ctx0_ok_crossBlockMove
      [.scalar ⟨20, 4⟩] (by decide) crossBlockMove20MInit rfl rfl rfl crossBlockMove20_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [crossBlockMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem crossBlockMove20_minirust_direct :
    (Interp.steps 17 crossBlockMove20MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live))) =
      some (some { retAlloc with data := scalarBytes u32 35 }, [1],
        [true, false, false, false, false, false, false]) := by
  decide +kernel

def crossBlockMoveOvS0 : MachineState :=
  initMachineState crossBlockMove [.scalar ⟨4294967290, 4⟩]
def crossBlockMoveOvMInit : Mach :=
  machine crossBlockMove crossBlockMoveFn crossBlockMoveOvS0.frame.locals crossBlockMoveFn.start

theorem crossBlockMoveOv_anneal_ret :
    ReachesRet (mirTree crossBlockMove crossBlockMoveOvS0)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 4⟩, crossBlockMoveOvS0.memory)) :=
  runA_sound crossBlockMove 30 _ _ _ rfl

theorem crossBlockMoveOv_noUB :
    MirNoUBTree (mirCallTree crossBlockMove [.scalar ⟨4294967290, 4⟩]) :=
  runA_noUB crossBlockMove 30 _ _ _ rfl

theorem crossBlockMoveOv_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen crossBlockMove + n) crossBlockMoveOvMInit = .ok m' ∧
      StateRel crossBlockMove crossBlockMoveFn ctx0 s' m' ∧
      Reaches (mirCallTree crossBlockMove [.scalar ⟨4294967290, 4⟩]) tr (mirTree crossBlockMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen crossBlockMove + n ∧
      Interp.steps k crossBlockMoveOvMInit = .ok mRet ∧
      ReturnRel crossBlockMove ctx0 s' v mRet ∧
      ReachesRet (mirCallTree crossBlockMove [.scalar ⟨4294967290, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress crossBlockMove_inFragment crossBlockMove_translate ctx0 ctx0_ok_crossBlockMove
    [.scalar ⟨4294967290, 4⟩] (by decide) crossBlockMoveOvMInit rfl rfl rfl crossBlockMoveOv_noUB n

theorem crossBlockMoveOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n crossBlockMoveOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 0 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret crossBlockMove_inFragment crossBlockMove_translate ctx0 ctx0_ok_crossBlockMove
      [.scalar ⟨4294967290, 4⟩] (by decide) crossBlockMoveOvMInit rfl rfl rfl
      crossBlockMoveOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [crossBlockMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem crossBlockMoveOv_minirust_direct :
    (Interp.steps 15 crossBlockMoveOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live))) =
      some (some { retAlloc with data := scalarBytes u32 0 }, [1],
        [true, false, false, false, false, false, false]) := by
  decide +kernel

/-! ### Cross-block move-reuse rejected by `movesOk` -/

/-- A 2-block body that moves `_1` in `bb0` (`_0 = move _1; goto bb1`) and reads
`_1` in `bb1` (`_0 = copy _1; return`): `movedAtEntry` propagates `1` across the
`bb0 → bb1` edge and `movesOk` rejects the body. -/
def crossBlockMoveReuse : CapturedMir where
  defPath := "witness::cross_block_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (.move (local_ 1))))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem crossBlockMoveReuse_movesOk :
    movedAtEntry crossBlockMoveReuse 1 = [1] ∧ movesOk crossBlockMoveReuse = false ∧
    inFragment crossBlockMoveReuse = false := by decide

/-! ### A body that `mentionsOk` rejects (`alwaysStorageLiveLocals` gap) -/

/-- MIR of `_1 = const 9_u32; _0 = copy _1; return` for `fn() -> u32` where the
temporary `_1: u32` has no `StorageLive` or `StorageDead` marker in the body
(`alwaysStorageLiveLocals = [1]`): `minimize`'s `initBlock` emits
`StorageLive(_1)` so MiniRust returns `9`, whereas Anneal's `initMachineState`
starts `_1` in `.dead` and faults with UB on `_1 = const 9_u32`. `mentionsOk`
rejects this body. -/
def unmarkedTempAssign : CapturedMir where
  defPath := "witness::unmarked_temp_assign"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.use (constU32 9))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem unmarkedTempAssign_rejected :
    alwaysStorageLiveLocals unmarkedTempAssign = [1] ∧
    mentionsOk unmarkedTempAssign = false ∧
    inFragment unmarkedTempAssign = false := by decide

def unmarkedTempAssignFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1)) (.Constant (.Int 9) (.Int u32)),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[.StorageLive (localName 1)], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem unmarkedTempAssign_translate :
    translateFn unmarkedTempAssign = some unmarkedTempAssignFn := rfl

def unmarkedTempAssignS0 : MachineState := initMachineState unmarkedTempAssign []

theorem unmarkedTempAssign_anneal_ub :
    ∃ tr u, Reaches (mirTree unmarkedTempAssign unmarkedTempAssignS0) tr u ∧ FaultNow u :=
  faultsA_sound unmarkedTempAssign 10 _ (by decide)

theorem unmarkedTempAssign_minirust_direct :
    (Interp.steps 5 (machine unmarkedTempAssign unmarkedTempAssignFn
        unmarkedTempAssignS0.frame.locals unmarkedTempAssignFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

/-! ### Direct ground-truth checks for `BM.allocate`, `BM.deallocate`, and
`Statement::Deinit` UB paths -/

/-- `BM.allocate` raises `"asking for a too large allocation"` when
`!x86_64.valid_size(size)` (`size.bytes >= 2^63` or `size.bytes < 0`), and
`BM.deallocate` raises each of the six upstream UB diagnostics from
`spec/mem/basic.md` (provenance `None`, double-free of a dead allocation,
non-zero offset from `alloc.addr`, wrong `AllocationKind` formatting both the
allocation's kind and the requested operation kind across all five
`AllocationKind` variants `Stack`, `Heap`, `Global`, `Function`, and `VTable`,
wrong `Size`, and wrong `Align`). -/
theorem bm_allocate_and_deallocate_ub_cases :
    BM.allocate { tempMove3MInit.mem.memory with allocations := [] } .Stack ⟨2 ^ 63⟩ ⟨1⟩ =
      .error (.ub "asking for a too large allocation") ∧
    BM.deallocate tempMove3MInit.mem.memory { addr := 64, provenance := none } .Stack ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating invalid pointer") ∧
    BM.deallocate
      { tempMove3MInit.mem.memory with allocations := [{ retAlloc with live := false }] }
      { addr := 64, provenance := some (⟨0⟩, ()) } .Stack ⟨4⟩ ⟨4⟩ =
      .error (.ub "double-free") ∧
    BM.deallocate tempMove3MInit.mem.memory
      { addr := 65, provenance := some (⟨0⟩, ()) } .Stack ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating with pointer not to the beginning of its allocation") ∧
    BM.deallocate tempMove3MInit.mem.memory
      { addr := 64, provenance := some (⟨0⟩, ()) } .Heap ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating Stack memory with Heap deallocation operation") ∧
    BM.deallocate
      { tempMove3MInit.mem.memory with allocations := [{ retAlloc with kind := .Global }] }
      { addr := 64, provenance := some (⟨0⟩, ()) } .Function ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating Global memory with Function deallocation operation") ∧
    BM.deallocate
      { tempMove3MInit.mem.memory with allocations := [{ retAlloc with kind := .VTable }] }
      { addr := 64, provenance := some (⟨0⟩, ()) } .Stack ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating VTable memory with Stack deallocation operation") ∧
    BM.deallocate tempMove3MInit.mem.memory
      { addr := 64, provenance := some (⟨0⟩, ()) } .Stack ⟨8⟩ ⟨4⟩ =
      .error (.ub "deallocating with incorrect size information") ∧
    BM.deallocate tempMove3MInit.mem.memory
      { addr := 64, provenance := some (⟨0⟩, ()) } .Stack ⟨4⟩ ⟨8⟩ =
      .error (.ub "deallocating with incorrect alignment information") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `evalStatement` for `Statement::Deinit` replaces the bytes of a live local
with `AbstractByte.Uninit`, raises `"access to a dead local"` on a dead local,
and raises `"dereferencing pointer outside the bounds of its allocation"` when
`CM.deinit` stores `size` bytes at an out-of-bounds offset in the local's
allocation (while `CM.deinit` with non-unit alignment raises `"store to a
misaligned pointer"`). -/
def misalignedLocalMach : Mach :=
  { tempMove3MInit with
    threads := [thread1 ctx0 [callerFrame,
      { calleeFrameL tempMoveFn ctx0
          ⟨[(localName 0, localPtr ctx0 0),
            (localName 1, { addr := 257, provenance := some (⟨2⟩, ()) })]⟩ 0 0 with
        next_block := tempMoveFn.start }]] }

theorem evalStatement_deinit_ok_dead_and_misaligned :
    (evalStatement tempMove3MInit (.Deinit (.Local (localName 1)))).toOption.bind
        (fun m => m.mem.memory.allocations[2]?.map (·.data)) =
      some [.Uninit, .Uninit, .Uninit, .Uninit] ∧
    evalStatement tempMove3MInit (.Deinit (.Local (localName 2))) =
      .error (.ub "access to a dead local") ∧
    evalStatement misalignedLocalMach (.Deinit (.Local (localName 1))) =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    CM.deinit tempMove3MInit.mem { addr := 257, provenance := some (⟨2⟩, ()) } ⟨4⟩ ⟨4⟩ =
      .error (.ub "store to a misaligned pointer") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Cyclic loop CFG with multi-pass `movesOk` and multi-local `initBlock`

`loopTempMove` computes `n + (n - 1) + .. + 1` in a 4-block cyclic CFG (`bb0`
entry, `bb1` loop header, `bb2` loop body with back-edge `Goto(bb1)`, `bb3`
exit), exercising:
* two heterogeneous unmarked temporaries `_4: u32` and `_5: i8`
  (`alwaysStorageLiveLocals = [4, 5]`, `initLen = 3`);
* multi-pass fixpoint convergence of `iterMovedEntries`: `bb2` moves out of
  `_2` before jumping back to `bb1` (leaving `_2` live across the back-edge),
  Pass 1 adds `2` to `bb1`'s entry set, Pass 2 propagates `2` forward from
  `bb1` into `bb2` and `bb3`, and `StorageLive(_2)` in `bb2` (re-allocating
  already-live `_2`) / idempotent `StorageDead(_2)` in `bb3` clear the mark;
* per-iteration `StorageLive(_3)`, `SwitchInt(move _3)`, `Deinit(_3)`, and
  `StorageDead(_3)` on the `bool` loop-condition temporary `_3`;
* loop-carried root moves `move _0` and `move _1` re-initialized in `bb2`. -/
def loopTempMove : CapturedMir where
  defPath := "witness::loop_temp_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl, boolDecl, u32Decl, i8Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 0)))],
      terminator := mkTerm (.goto 1),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.binaryOp .gt (.copy (local_ 1)) (constU32 0)))],
      terminator := mkTerm (.switchInt (.move (local_ 3)) { branches := [(0, 3)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.deinit (local_ 3)),
        mkStmt (.storageDead 3),
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.binaryOp .add (.move (local_ 0)) (.copy (local_ 1)))),
        mkStmt (.assign (local_ 0) (.use (.move (local_ 2)))),
        mkStmt (.assign (local_ 1) (.binaryOp .sub (.move (local_ 1)) (constU32 1)))],
      terminator := mkTerm (.goto 1),
      isCleanup := false },
    { statements := [
        mkStmt (.deinit (local_ 3)),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem loopTempMove_inFragment : inFragment loopTempMove = true := by decide

theorem loopTempMove_alwaysLive : alwaysStorageLiveLocals loopTempMove = [4, 5] := by decide

theorem loopTempMove_initLen : initLen loopTempMove = 3 := by decide

/-- Pass 1 of `iterMovedEntries` records `2` at `bb1` from the back-edge
`bb2 → bb1` (`[[], [2], [3], [3]]`), and Pass 2 propagates `2` from `bb1` into
`bb2` and `bb3` (`[[], [2], [2, 3], [2, 3]]`), where it stabilizes. -/
theorem loopTempMove_movedAtEntry_multiPass :
    iterMovedEntries 1 loopTempMove.basicBlocks [] = [[], [2], [3], [3]] ∧
    iterMovedEntries 2 loopTempMove.basicBlocks [] = [[], [2], [2, 3], [2, 3]] ∧
    [0, 1, 2, 3].map (movedAtEntry loopTempMove) = [[], [2], [2, 3], [2, 3]] := by decide

def loopTempMoveFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, .Bool), (localName 4, .Int u32), (localName 5, .Int i8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 0) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.Rel .Gt) (.Load (.Local (localName 1))) (.Constant (.Int 0) (.Int u32)))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 3))))
        ⟨[(0, bbName 3)]⟩ (bbName 2), .Regular⟩),
    (bbName 2, ⟨[
      .Deinit (.Local (localName 3)),
      .StorageDead (localName 3),
      .StorageLive (localName 2),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0))) (.Load (.Local (localName 1)))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 1))) (.Constant (.Int 1) (.Int u32)))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 3, ⟨[
      .Deinit (.Local (localName 3)),
      .StorageDead (localName 3),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[.StorageLive (localName 4), .StorageLive (localName 5)],
      .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem loopTempMove_translate : translateFn loopTempMove = some loopTempMoveFn := rfl

theorem ctx0_ok_loopTempMove : CtxOk loopTempMove ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [loopTempMove] at hd; subst hd; decide
    | 1, _, hd => simp [loopTempMove] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [loopTempMove] at hi
  ret := by
    intro d hd
    simp [loopTempMove] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def loopTempMove3S0 : MachineState := initMachineState loopTempMove [.scalar ⟨3, 4⟩]
def loopTempMove3MInit : Mach :=
  machine loopTempMove loopTempMoveFn loopTempMove3S0.frame.locals loopTempMoveFn.start

def loopTempMove3Trace : List (Event MirEffect) :=
  [1, 1, 1, 0].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

theorem loopTempMove3_anneal_ret :
    ReachesRet (mirTree loopTempMove loopTempMove3S0) loopTempMove3Trace
      (.normal (.scalar ⟨6, 4⟩, loopTempMove3S0.memory)) :=
  runA_sound loopTempMove 50 _ _ _ rfl

theorem loopTempMove3_noUB : MirNoUBTree (mirCallTree loopTempMove [.scalar ⟨3, 4⟩]) :=
  runA_noUB loopTempMove 50 _ _ _ rfl

theorem loopTempMove3_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen loopTempMove + n) loopTempMove3MInit = .ok m' ∧
      StateRel loopTempMove loopTempMoveFn ctx0 s' m' ∧
      Reaches (mirCallTree loopTempMove [.scalar ⟨3, 4⟩]) tr (mirTree loopTempMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen loopTempMove + n ∧
      Interp.steps k loopTempMove3MInit = .ok mRet ∧
      ReturnRel loopTempMove ctx0 s' v mRet ∧
      ReachesRet (mirCallTree loopTempMove [.scalar ⟨3, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress loopTempMove_inFragment loopTempMove_translate ctx0 ctx0_ok_loopTempMove
    [.scalar ⟨3, 4⟩] (by decide) loopTempMove3MInit rfl rfl rfl loopTempMove3_noUB n

theorem loopTempMove3_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n loopTempMove3MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret loopTempMove_inFragment loopTempMove_translate ctx0 ctx0_ok_loopTempMove
      [.scalar ⟨3, 4⟩] (by decide) loopTempMove3MInit rfl rfl rfl loopTempMove3_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [loopTempMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem loopTempMove3_minirust_direct :
    (Interp.steps 42 loopTempMove3MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.all (fun a => a.addr == 64 || !a.live))) =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1], true) := by
  decide +kernel

def loopTempMove0S0 : MachineState := initMachineState loopTempMove [.scalar ⟨0, 4⟩]
def loopTempMove0MInit : Mach :=
  machine loopTempMove loopTempMoveFn loopTempMove0S0.frame.locals loopTempMoveFn.start

theorem loopTempMove0_anneal_ret :
    ReachesRet (mirTree loopTempMove loopTempMove0S0)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 4⟩, loopTempMove0S0.memory)) :=
  runA_sound loopTempMove 20 _ _ _ rfl

theorem loopTempMove0_noUB : MirNoUBTree (mirCallTree loopTempMove [.scalar ⟨0, 4⟩]) :=
  runA_noUB loopTempMove 20 _ _ _ rfl

theorem loopTempMove0_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen loopTempMove + n) loopTempMove0MInit = .ok m' ∧
      StateRel loopTempMove loopTempMoveFn ctx0 s' m' ∧
      Reaches (mirCallTree loopTempMove [.scalar ⟨0, 4⟩]) tr (mirTree loopTempMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen loopTempMove + n ∧
      Interp.steps k loopTempMove0MInit = .ok mRet ∧
      ReturnRel loopTempMove ctx0 s' v mRet ∧
      ReachesRet (mirCallTree loopTempMove [.scalar ⟨0, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress loopTempMove_inFragment loopTempMove_translate ctx0 ctx0_ok_loopTempMove
    [.scalar ⟨0, 4⟩] (by decide) loopTempMove0MInit rfl rfl rfl loopTempMove0_noUB n

theorem loopTempMove0_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n loopTempMove0MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 0 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret loopTempMove_inFragment loopTempMove_translate ctx0 ctx0_ok_loopTempMove
      [.scalar ⟨0, 4⟩] (by decide) loopTempMove0MInit rfl rfl rfl loopTempMove0_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [loopTempMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem loopTempMove0_minirust_direct :
    (Interp.steps 12 loopTempMove0MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live))) =
      some (some { retAlloc with data := scalarBytes u32 0 }, [1],
        [true, false, false, false, false, false]) := by
  decide +kernel

/-! ### Cyclic back-edge move-reuse separating multi-pass from 1-pass -/

/-- `bb0` initializes `_2 = 99`, `bb1` branches to `bb2` or `bb3`, `bb2` moves
`_2` and loops back to `bb1`, and `bb3` reads `copy _2`: a single forward pass
leaves `bb3`'s entry set empty (`[]`), whereas Pass 2 propagates `2` along
`bb2 → bb1 → bb3` and `movesOk` rejects the body. On `_1 = 1`, Anneal faults
with UB in `bb3` while MiniRust returns `99`. -/
def loopBackEdgeReuse : CapturedMir where
  defPath := "witness::loop_back_edge_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (constU32 99)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 3)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.move (local_ 2)))),
        mkStmt (.assign (local_ 1) (.use (constU32 0)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 2)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem loopBackEdgeReuse_movesOk :
    (iterMovedEntries 1 loopBackEdgeReuse.basicBlocks []).getD 3 [] = [] ∧
    movedAtEntry loopBackEdgeReuse 3 = [2] ∧
    movesOk loopBackEdgeReuse = false ∧
    inFragment loopBackEdgeReuse = false := by decide

def loopBackEdgeReuseFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.Constant (.Int 99) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[],
      .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 3)]⟩ (bbName 2), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 1)) (.Constant (.Int 0) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 2))),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem loopBackEdgeReuse_translate :
    translateFn loopBackEdgeReuse = some loopBackEdgeReuseFn := rfl

def loopBackEdgeReuse1S0 : MachineState := initMachineState loopBackEdgeReuse [.scalar ⟨1, 4⟩]

theorem loopBackEdgeReuse1_anneal_ub :
    ∃ tr u, Reaches (mirTree loopBackEdgeReuse loopBackEdgeReuse1S0) tr u ∧ FaultNow u :=
  faultsA_sound loopBackEdgeReuse 20 _ (by decide)

theorem loopBackEdgeReuse1_minirust_direct :
    (Interp.steps 12 (machine loopBackEdgeReuse loopBackEdgeReuseFn
        loopBackEdgeReuse1S0.frame.locals loopBackEdgeReuseFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) := by
  decide +kernel

/-! ### Dead-local UB for `Assign`, `Deinit`, and projected `PlaceMention` -/

/-- Assigning to `_1` after `StorageDead(_1)` raises UB in both models. -/
def deadAssign : CapturedMir where
  defPath := "witness::dead_assign"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.storageDead 1),
        mkStmt (.assign (local_ 1) (.use (constU32 5)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem deadAssign_inFragment : inFragment deadAssign = true := by decide

def deadAssignFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .StorageDead (localName 1),
      .Assign (.Local (localName 1)) (.Constant (.Int 5) (.Int u32))], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deadAssign_translate : translateFn deadAssign = some deadAssignFn := rfl

def deadAssignS0 : MachineState := initMachineState deadAssign []
def deadAssignMInit : Mach := machine deadAssign deadAssignFn deadAssignS0.frame.locals deadAssignFn.start

theorem deadAssign_anneal_ub : ∃ tr u, Reaches (mirTree deadAssign deadAssignS0) tr u ∧ FaultNow u :=
  faultsA_sound deadAssign 10 _ (by decide)

theorem deadAssign_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n deadAssignMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := deadAssign_anneal_ub
  exact mirCall_ub deadAssign_inFragment deadAssign_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadAssignMInit rfl rfl rfl hr hf

theorem deadAssign_minirust_direct :
    (match Interp.steps 4 deadAssignMInit with
      | .error (.ub msg) => some msg
      | _ => none) = some "access to a dead local" := by
  decide +kernel

theorem deadAssign_steps4_ub :
    Interp.steps 4 deadAssignMInit = .error (.ub "access to a dead local") := by
  have h := deadAssign_minirust_direct
  revert h
  cases Interp.steps 4 deadAssignMInit with
  | ok _ => simp
  | error e => cases e <;> simp

theorem deadAssign_converse_error :
    (∃ msg, Stop.ub "access to a dead local" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree deadAssign []) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 4 ∧ Interp.steps k deadAssignMInit = .ok mRet ∧
      ReturnRel deadAssign ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadAssign []) tr (.normal (v, mem))) :=
  mirCall_steps_error deadAssign_inFragment deadAssign_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadAssignMInit rfl rfl rfl deadAssign_steps4_ub

theorem deadAssign_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen deadAssign + n) deadAssignMInit = .ok m' ∧
      StateRel deadAssign deadAssignFn ctx0 s' m' ∧
      Reaches (mirCallTree deadAssign []) tr (mirTree deadAssign s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen deadAssign + n ∧
      Interp.steps k deadAssignMInit = .ok mRet ∧
      ReturnRel deadAssign ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadAssign []) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen deadAssign + n) deadAssignMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree deadAssign []) tr u ∧ FaultNow u) :=
  mirCall_outcome deadAssign_inFragment deadAssign_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadAssignMInit rfl rfl rfl n

/-- `Deinit(_1)` after `StorageDead(_1)` raises UB in both models. -/
def deadDeinit : CapturedMir where
  defPath := "witness::dead_deinit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (constU32 5))),
        mkStmt (.storageDead 1),
        mkStmt (.deinit (local_ 1))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem deadDeinit_inFragment : inFragment deadDeinit = true := by decide

def deadDeinitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .Assign (.Local (localName 1)) (.Constant (.Int 5) (.Int u32)),
      .StorageDead (localName 1),
      .Deinit (.Local (localName 1))], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deadDeinit_translate : translateFn deadDeinit = some deadDeinitFn := rfl

def deadDeinitS0 : MachineState := initMachineState deadDeinit []
def deadDeinitMInit : Mach := machine deadDeinit deadDeinitFn deadDeinitS0.frame.locals deadDeinitFn.start

theorem deadDeinit_anneal_ub : ∃ tr u, Reaches (mirTree deadDeinit deadDeinitS0) tr u ∧ FaultNow u :=
  faultsA_sound deadDeinit 10 _ (by decide)

theorem deadDeinit_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n deadDeinitMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := deadDeinit_anneal_ub
  exact mirCall_ub deadDeinit_inFragment deadDeinit_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadDeinitMInit rfl rfl rfl hr hf

theorem deadDeinit_minirust_direct :
    (match Interp.steps 5 deadDeinitMInit with
      | .error (.ub msg) => some msg
      | _ => none) = some "access to a dead local" := by
  decide +kernel

theorem deadDeinit_steps5_ub :
    Interp.steps 5 deadDeinitMInit = .error (.ub "access to a dead local") := by
  have h := deadDeinit_minirust_direct
  revert h
  cases Interp.steps 5 deadDeinitMInit with
  | ok _ => simp
  | error e => cases e <;> simp

theorem deadDeinit_converse_error :
    (∃ msg, Stop.ub "access to a dead local" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree deadDeinit []) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 5 ∧ Interp.steps k deadDeinitMInit = .ok mRet ∧
      ReturnRel deadDeinit ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadDeinit []) tr (.normal (v, mem))) :=
  mirCall_steps_error deadDeinit_inFragment deadDeinit_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadDeinitMInit rfl rfl rfl deadDeinit_steps5_ub

theorem deadDeinit_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen deadDeinit + n) deadDeinitMInit = .ok m' ∧
      StateRel deadDeinit deadDeinitFn ctx0 s' m' ∧
      Reaches (mirCallTree deadDeinit []) tr (mirTree deadDeinit s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen deadDeinit + n ∧
      Interp.steps k deadDeinitMInit = .ok mRet ∧
      ReturnRel deadDeinit ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadDeinit []) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen deadDeinit + n) deadDeinitMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree deadDeinit []) tr u ∧ FaultNow u) :=
  mirCall_outcome deadDeinit_inFragment deadDeinit_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadDeinitMInit rfl rfl rfl n

/-- Projected `PlaceMention(_1.0)` on `_1: (u32, bool)` after `StorageDead(_1)`
raises UB in both models. -/
theorem ctx0_ok_u32_tuple {body : CapturedMir}
    (h : body.localDecls = [u32Decl, u32BoolTupleDecl]) : CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def deadPlaceMention : CapturedMir where
  defPath := "witness::dead_place_mention"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.storageDead 1),
        mkStmt (.placeMention (field0U32 1))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem deadPlaceMention_inFragment : inFragment deadPlaceMention = true := by decide

def deadPlaceMentionFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, intBoolTupleTy u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .StorageDead (localName 1),
      .PlaceMention (.Field (.Local (localName 1)) 0)], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deadPlaceMention_translate :
    translateFn deadPlaceMention = some deadPlaceMentionFn := rfl

def deadPlaceMentionS0 : MachineState := initMachineState deadPlaceMention []
def deadPlaceMentionMInit : Mach :=
  machine deadPlaceMention deadPlaceMentionFn deadPlaceMentionS0.frame.locals
    deadPlaceMentionFn.start

theorem deadPlaceMention_anneal_ub :
    ∃ tr u, Reaches (mirTree deadPlaceMention deadPlaceMentionS0) tr u ∧ FaultNow u :=
  faultsA_sound deadPlaceMention 10 _ (by decide)

theorem deadPlaceMention_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n deadPlaceMentionMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := deadPlaceMention_anneal_ub
  exact mirCall_ub deadPlaceMention_inFragment deadPlaceMention_translate ctx0
    (ctx0_ok_u32_tuple rfl) [] (by decide) deadPlaceMentionMInit rfl rfl rfl hr hf

theorem deadPlaceMention_minirust_direct :
    (match Interp.steps 4 deadPlaceMentionMInit with
      | .error (.ub msg) => some msg
      | _ => none) = some "access to a dead local" := by
  decide +kernel

theorem deadPlaceMention_steps4_ub :
    Interp.steps 4 deadPlaceMentionMInit = .error (.ub "access to a dead local") := by
  have h := deadPlaceMention_minirust_direct
  revert h
  cases Interp.steps 4 deadPlaceMentionMInit with
  | ok _ => simp
  | error e => cases e <;> simp

theorem deadPlaceMention_converse_error :
    (∃ msg, Stop.ub "access to a dead local" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree deadPlaceMention []) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 4 ∧ Interp.steps k deadPlaceMentionMInit = .ok mRet ∧
      ReturnRel deadPlaceMention ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadPlaceMention []) tr (.normal (v, mem))) :=
  mirCall_steps_error deadPlaceMention_inFragment deadPlaceMention_translate ctx0
    (ctx0_ok_u32_tuple rfl) [] (by decide) deadPlaceMentionMInit rfl rfl rfl
    deadPlaceMention_steps4_ub

theorem deadPlaceMention_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen deadPlaceMention + n) deadPlaceMentionMInit = .ok m' ∧
      StateRel deadPlaceMention deadPlaceMentionFn ctx0 s' m' ∧
      Reaches (mirCallTree deadPlaceMention []) tr (mirTree deadPlaceMention s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen deadPlaceMention + n ∧
      Interp.steps k deadPlaceMentionMInit = .ok mRet ∧
      ReturnRel deadPlaceMention ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadPlaceMention []) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen deadPlaceMention + n) deadPlaceMentionMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree deadPlaceMention []) tr u ∧ FaultNow u) :=
  mirCall_outcome deadPlaceMention_inFragment deadPlaceMention_translate ctx0
    (ctx0_ok_u32_tuple rfl) [] (by decide) deadPlaceMentionMInit rfl rfl rfl n

/-! ### Boundary counterexamples (`storageDeadOk`, `Deinit`, `stmtMoved`,
`readsOk`, `termReadsOk`) -/

/-- `StorageDead(_0); return` is ill-formed in MiniRust (`storageDeadOk` fails):
Anneal faults with `.ub` on returning a dead `_0`, whereas MiniRust's
`evalReturn` indexes `frame.locals[frame.func.ret]` and hits `Stop.specPanic`.
-/
def storageDeadRet : CapturedMir where
  defPath := "witness::storage_dead_ret"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageDead 0)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem storageDeadRet_rejected :
    storageDeadOk storageDeadRet = false ∧ inFragment storageDeadRet = false := by decide

def storageDeadRetFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.StorageDead (localName 0)], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem storageDeadRet_translate :
    translateFn storageDeadRet = some storageDeadRetFn := rfl

def storageDeadRetS0 : MachineState := initMachineState storageDeadRet []

theorem storageDeadRet_anneal_ub :
    ∃ tr u, Reaches (mirTree storageDeadRet storageDeadRetS0) tr u ∧ FaultNow u :=
  faultsA_sound storageDeadRet 5 _ (by decide)

theorem storageDeadRet_minirust_panics :
    (match Interp.steps 3 (machine storageDeadRet storageDeadRetFn storageDeadRetS0.frame.locals
        storageDeadRetFn.start) with
      | .error (.specPanic msg) => some msg
      | _ => none) =
      some "map index: missing key (frame.locals[frame.func.ret])" := by
  decide +kernel

/-- `Deinit(_1.0); _0 = copy (_1.0); return` on `_1: (u32, bool)` is rejected by
`statementOk`: Anneal's projected `Deinit` checks `_1.0` and leaves `_1`
initialized (returning `42`), whereas MiniRust overwrites `_1.0` with `Uninit`
bytes so the subsequent load raises UB. -/
def projectedDeinit : CapturedMir where
  defPath := "witness::projected_deinit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.deinit (field0U32 1)),
        mkStmt (.assign (local_ 0) (.use (.copy (field0U32 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem projectedDeinit_rejected :
    statementOk projectedDeinit.localDecls (mkStmt (.deinit (field0U32 1))) = false ∧
    inFragment projectedDeinit = false := by decide

def projectedDeinitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, intBoolTupleTy u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Deinit (.Field (.Local (localName 1)) 0),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 0))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem projectedDeinit_translate :
    translateFn projectedDeinit = some projectedDeinitFn := rfl

def projectedDeinitArgs : List Value := [.aggregate 0 [.scalar ⟨42, 4⟩, .scalar ⟨1, 1⟩]]
def projectedDeinitS0 : MachineState := initMachineState projectedDeinit projectedDeinitArgs

theorem projectedDeinit_anneal_ret :
    ReachesRet (mirTree projectedDeinit projectedDeinitS0) []
      (.normal (.scalar ⟨42, 4⟩, projectedDeinitS0.memory)) :=
  runA_sound projectedDeinit 10 _ _ _ rfl

theorem projectedDeinit_minirust_ub :
    (match Interp.steps 3 (machine projectedDeinit projectedDeinitFn projectedDeinitS0.frame.locals
        projectedDeinitFn.start) with
      | .error (.ub msg) => some msg
      | _ => none) =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- `_2.0 = Use(move _1); _0 = Use(copy _1); return`: `stmtMoved` tracks operand
moves on projected assignments without clearing `_2`, so `movesOk` rejects the
subsequent read of `_1` even when inspected standalone. -/
def projAssignMoveReuse : CapturedMir where
  defPath := "witness::proj_assign_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (field0U32 2) (.use (.move (local_ 1)))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem projAssignMoveReuse_movesOk :
    movesOk projAssignMoveReuse = false ∧ inFragment projAssignMoveReuse = false := by decide

/-- `_0 = BinaryOp(Add, move _1, copy _1); return` for `fn(u32) -> u32`:
`readsOk` threads `moveOut` left-to-right across the operands of a single
rvalue (`readsOk (moveOut mo op) ops`), so moving `_1` in the first operand and
reading `_1` in the second operand of the same statement is rejected by
`movesOk`. On input `5`, Anneal faults with `.ub` on the second operand
`copy _1`, whereas MiniRust loads `_1` twice and returns `10`. -/
def sameRvalueMoveReuse : CapturedMir where
  defPath := "witness::same_rvalue_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.move (local_ 1)) (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem sameRvalueMoveReuse_movesOk :
    readsOk [] (rvOperands (.binaryOp .add (.move (local_ 1)) (.copy (local_ 1)))) = false ∧
    movesOk sameRvalueMoveReuse = false ∧
    inFragment sameRvalueMoveReuse = false := by decide

def sameRvalueMoveReuseFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 1))) (.Load (.Local (localName 1))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem sameRvalueMoveReuse_translate :
    translateFn sameRvalueMoveReuse = some sameRvalueMoveReuseFn := rfl

def sameRvalueMoveReuse5S0 : MachineState := initMachineState sameRvalueMoveReuse [.scalar ⟨5, 4⟩]

theorem sameRvalueMoveReuse5_anneal_ub :
    ∃ tr u, Reaches (mirTree sameRvalueMoveReuse sameRvalueMoveReuse5S0) tr u ∧ FaultNow u :=
  faultsA_sound sameRvalueMoveReuse 5 _ (by decide)

theorem sameRvalueMoveReuse5_minirust_direct :
    (Interp.steps 3 (machine sameRvalueMoveReuse sameRvalueMoveReuseFn
        sameRvalueMoveReuse5S0.frame.locals sameRvalueMoveReuseFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 10 }, [1]) := by
  decide +kernel

/-- `_0 = const 10_u32; StorageLive(_1); _1 = Use(move _0); StorageDead(_1);`
`return` for `fn() -> u32`: every statement satisfies `stmtReadsOk`, but
`termReadsOk` on `.return_` requires `!mo.contains 0` because `Return` reads the
return place `_0`. Anneal de-initializes `_0` at `move _0` and faults with `.ub`
at `return`, whereas MiniRust's `evalReturn` loads the still-present bytes of
`_0` and returns `10`. -/
def moveRetPlace : CapturedMir where
  defPath := "witness::move_ret_place"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.use (constU32 10))),
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (.move (local_ 0)))),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem moveRetPlace_movesOk :
    termReadsOk [0] (mkTerm .return_) = false ∧
    movesOk moveRetPlace = false ∧
    inFragment moveRetPlace = false := by decide

def moveRetPlaceFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0)) (.Constant (.Int 10) (.Int u32)),
      .StorageLive (localName 1),
      .Assign (.Local (localName 1)) (.Load (.Local (localName 0))),
      .StorageDead (localName 1)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem moveRetPlace_translate : translateFn moveRetPlace = some moveRetPlaceFn := rfl

def moveRetPlaceS0 : MachineState := initMachineState moveRetPlace []

theorem moveRetPlace_anneal_ub :
    ∃ tr u, Reaches (mirTree moveRetPlace moveRetPlaceS0) tr u ∧ FaultNow u :=
  faultsA_sound moveRetPlace 10 _ (by decide)

theorem moveRetPlace_minirust_direct :
    (Interp.steps 6 (machine moveRetPlace moveRetPlaceFn
        moveRetPlaceS0.frame.locals moveRetPlaceFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 10 }, [1]) := by
  decide +kernel

/-! ### `StorageLive` on argument and return locals, `StorageDead` on an
argument, and CFG diamond merges -/

/-- `fn(x: u32) -> u32` exercising `StorageLive(_1)` on an argument local and
`StorageLive(_0)` on the return place (both permitted by MiniRust's
well-formedness check in `spec/lang/well-formed.md` and by `statementOk`).
`StorageLive(_1)` and `StorageLive(_0)` deallocate the caller-range (`< 2^32`)
initial allocations at `256` and `128`, re-allocate fresh `Uninit` stack
allocations at `2 * 2^32` and `3 * 2^32`, clear `1` from `mo` (`stmtMoved`),
and allow `Return` to copy `_0` from its re-allocated `3 * 2^32` slot and tear
down the shuffled `locals` map. -/
def storageLiveArgRet : CapturedMir where
  defPath := "witness::storage_live_arg_ret"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (.move (local_ 1)))),
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.binaryOp .add (.copy (local_ 2)) (constU32 10))),
        mkStmt (.storageLive 0),
        mkStmt (.assign (local_ 0) (.binaryOp .mul (.move (local_ 1)) (constU32 2))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem storageLiveArgRet_inFragment : inFragment storageLiveArgRet = true := by decide

def storageLiveArgRetFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.Load (.Local (localName 1))),
      .StorageLive (localName 1),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Add) (.Load (.Local (localName 2))) (.Constant (.Int 10) (.Int u32))),
      .StorageLive (localName 0),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Mul) (.Load (.Local (localName 1))) (.Constant (.Int 2) (.Int u32))),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem storageLiveArgRet_translate :
    translateFn storageLiveArgRet = some storageLiveArgRetFn := rfl

theorem ctx0_ok_u32_3 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, u32Decl, u32Decl]) : CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def storageLiveArgRet5S0 : MachineState :=
  initMachineState storageLiveArgRet [.scalar ⟨5, 4⟩]
def storageLiveArgRet5MInit : Mach :=
  machine storageLiveArgRet storageLiveArgRetFn
    storageLiveArgRet5S0.frame.locals storageLiveArgRetFn.start

theorem storageLiveArgRet5_anneal_ret :
    ReachesRet (mirTree storageLiveArgRet storageLiveArgRet5S0) []
      (.normal (.scalar ⟨30, 4⟩, storageLiveArgRet5S0.memory)) :=
  runA_sound storageLiveArgRet 20 _ _ _ rfl

theorem storageLiveArgRet5_noUB :
    MirNoUBTree (mirCallTree storageLiveArgRet [.scalar ⟨5, 4⟩]) :=
  runA_noUB storageLiveArgRet 20 _ _ _ rfl

theorem storageLiveArgRet5_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen storageLiveArgRet + n) storageLiveArgRet5MInit = .ok m' ∧
      StateRel storageLiveArgRet storageLiveArgRetFn ctx0 s' m' ∧
      Reaches (mirCallTree storageLiveArgRet [.scalar ⟨5, 4⟩]) tr
        (mirTree storageLiveArgRet s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen storageLiveArgRet + n ∧
      Interp.steps k storageLiveArgRet5MInit = .ok mRet ∧
      ReturnRel storageLiveArgRet ctx0 s' v mRet ∧
      ReachesRet (mirCallTree storageLiveArgRet [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress storageLiveArgRet_inFragment storageLiveArgRet_translate ctx0
    (ctx0_ok_u32_3 rfl) [.scalar ⟨5, 4⟩] (by decide) storageLiveArgRet5MInit
    rfl rfl rfl storageLiveArgRet5_noUB n

theorem storageLiveArgRet5_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n storageLiveArgRet5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 30 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret storageLiveArgRet_inFragment storageLiveArgRet_translate ctx0
      (ctx0_ok_u32_3 rfl) [.scalar ⟨5, 4⟩] (by decide) storageLiveArgRet5MInit
      rfl rfl rfl storageLiveArgRet5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [storageLiveArgRet] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem storageLiveArgRet5_minirust_direct :
    (Interp.steps 9 storageLiveArgRet5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live), m.mem.memory.allocations.map (·.addr))) =
      some (some { retAlloc with data := scalarBytes u32 30 }, [1],
        [true, false, false, false, false, false],
        [64, 128, 256, 2 ^ 32, 2 * 2 ^ 32, 3 * 2 ^ 32]) := by
  decide +kernel

/-- `_0 = Use(copy _1); StorageDead(_1); return` for `fn(u32) -> u32`:
`statementOk` accepts `StorageDead(_1)` because `_1` is an in-range local, while
`storageDeadOk` rejects it at the exact upper boundary `i = argCount` (`1 ≤ 1`),
matching MiniRust's well-formedness rejection of `StorageDead` on `func.args`.
-/
def storageDeadArg : CapturedMir where
  defPath := "witness::storage_dead_arg"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem storageDeadArg_rejected :
    statementOk storageDeadArg.localDecls (mkStmt (.storageDead 1)) = true ∧
    storageDeadOk storageDeadArg = false ∧
    inFragment storageDeadArg = false := by decide

def storageDeadArgFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1))),
      .StorageDead (localName 1)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem storageDeadArg_translate :
    translateFn storageDeadArg = some storageDeadArgFn := rfl

def storageDeadArg5S0 : MachineState :=
  initMachineState storageDeadArg [.scalar ⟨5, 4⟩]

theorem storageDeadArg5_anneal_ret :
    ReachesRet (mirTree storageDeadArg storageDeadArg5S0) []
      (.normal (.scalar ⟨5, 4⟩, storageDeadArg5S0.memory)) :=
  runA_sound storageDeadArg 10 _ _ _ rfl

theorem storageDeadArg5_minirust_direct :
    (Interp.steps 4 (machine storageDeadArg storageDeadArgFn
        storageDeadArg5S0.frame.locals storageDeadArgFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live))) =
      some (some { retAlloc with data := scalarBytes u32 5 }, [1],
        [true, false, false]) := by
  decide +kernel

/-- `StorageDead(_1); _0 = Use(copy _1); return` for `fn(u32) -> u32`:
rejected by `storageDeadOk = false` (`1 ≤ argCount`), and reading `_1` after
`StorageDead(_1)` faults with UB in both Anneal (`storageDeadArgReadAfter5_anneal_ub`)
and MiniRust (`storageDeadArgReadAfter5_minirust_ub`, raising
`"access to a dead local"`). -/
def storageDeadArgReadAfter : CapturedMir where
  defPath := "witness::storage_dead_arg_read_after"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageDead 1),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem storageDeadArgReadAfter_rejected :
    storageDeadOk storageDeadArgReadAfter = false ∧
    inFragment storageDeadArgReadAfter = false := by decide

def storageDeadArgReadAfterFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageDead (localName 1),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem storageDeadArgReadAfter_translate :
    translateFn storageDeadArgReadAfter = some storageDeadArgReadAfterFn := rfl

def storageDeadArgReadAfter5S0 : MachineState :=
  initMachineState storageDeadArgReadAfter [.scalar ⟨5, 4⟩]

theorem storageDeadArgReadAfter5_anneal_ub :
    ∃ tr u, Reaches (mirTree storageDeadArgReadAfter storageDeadArgReadAfter5S0) tr u ∧
      FaultNow u :=
  faultsA_sound storageDeadArgReadAfter 10 _ (by decide)

theorem storageDeadArgReadAfter5_minirust_ub :
    (match Interp.steps 3 (machine storageDeadArgReadAfter storageDeadArgReadAfterFn
        storageDeadArgReadAfter5S0.frame.locals storageDeadArgReadAfterFn.start) with
      | .error (.ub msg) => some msg
      | _ => none) = some "access to a dead local" := by
  decide +kernel

/-- Caller context placing `_0`, `_1`, and `_2` at distinct non-zero addresses
`128`, `256`, and `384` below `2^32` for two-argument `(bool, u32) -> u32`
diamond witnesses. -/
def ctx0_2 : Ctx := { ctx0 with addrs := [128, 256, 384] }

theorem ctx0_2_ok_bool_u32 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, boolDecl, u32Decl, u32Decl]) : CtxOk body ctx0_2 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | 3, hd => simp at hd; subst hd; decide
    | _ + 4, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- A 4-block diamond CFG `fn(flag: bool, x: u32) -> u32` accepted by
`inFragment = true`: `bb0` branches via `SwitchInt(move _1)` to `bb1` (which
moves `_2` into `_3 = move _2 + 1` and re-initializes `_2 = 10`, leaving
outgoing set `[1]`) and `bb2` (which moves `_2` into `_3 = move _2 * 2` without
re-initializing `_2`, leaving outgoing set `[2, 1]`). At the merge block `bb3`,
`movedAtEntry` converges to `[1, 2]`, and `bb3` safely returns `move _3`
without reading `_2`. -/
def diamondMoveJoin : CapturedMir where
  defPath := "witness::diamond_move_join"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, boolDecl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 3)],
      terminator := mkTerm (.switchInt (.move (local_ 1))
        { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .add (.move (local_ 2)) (constU32 1))),
        mkStmt (.assign (local_ 2) (.use (constU32 10)))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .mul (.move (local_ 2)) (constU32 2)))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.move (local_ 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem diamondMoveJoin_inFragment : inFragment diamondMoveJoin = true := by decide

theorem diamondMoveJoin_movedAtEntry :
    [0, 1, 2, 3].map (movedAtEntry diamondMoveJoin) = [[], [1], [1], [1, 2]] := by decide

def diamondMoveJoinFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Bool),
    (localName 2, .Int u32), (localName 3, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.StorageLive (localName 3)],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1))))
        ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Add) (.Load (.Local (localName 2))) (.Constant (.Int 1) (.Int u32))),
      .Assign (.Local (localName 2)) (.Constant (.Int 10) (.Int u32))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Mul) (.Load (.Local (localName 2))) (.Constant (.Int 2) (.Int u32)))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 3))),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem diamondMoveJoin_translate :
    translateFn diamondMoveJoin = some diamondMoveJoinFn := rfl

def diamondMoveJoinTrueArgs : List Value := [.scalar ⟨1, 1⟩, .scalar ⟨7, 4⟩]
def diamondMoveJoinTrueS0 : MachineState :=
  initMachineState diamondMoveJoin diamondMoveJoinTrueArgs
def diamondMoveJoinTrueMInit : Mach :=
  machineWithCtx ctx0_2 diamondMoveJoin diamondMoveJoinFn
    diamondMoveJoinTrueS0.frame.locals diamondMoveJoinFn.start

theorem diamondMoveJoinTrue_anneal_ret :
    ReachesRet (mirTree diamondMoveJoin diamondMoveJoinTrueS0)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨8, 4⟩, diamondMoveJoinTrueS0.memory)) :=
  runA_sound diamondMoveJoin 20 _ _ _ rfl

theorem diamondMoveJoinTrue_noUB :
    MirNoUBTree (mirCallTree diamondMoveJoin diamondMoveJoinTrueArgs) :=
  runA_noUB diamondMoveJoin 20 _ _ _ rfl

theorem diamondMoveJoinTrue_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen diamondMoveJoin + n) diamondMoveJoinTrueMInit = .ok m' ∧
      StateRel diamondMoveJoin diamondMoveJoinFn ctx0_2 s' m' ∧
      Reaches (mirCallTree diamondMoveJoin diamondMoveJoinTrueArgs) tr
        (mirTree diamondMoveJoin s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen diamondMoveJoin + n ∧
      Interp.steps k diamondMoveJoinTrueMInit = .ok mRet ∧
      ReturnRel diamondMoveJoin ctx0_2 s' v mRet ∧
      ReachesRet (mirCallTree diamondMoveJoin diamondMoveJoinTrueArgs) tr
        (.normal (v, mem))) :=
  mirCall_progress diamondMoveJoin_inFragment diamondMoveJoin_translate ctx0_2
    (ctx0_2_ok_bool_u32 rfl) diamondMoveJoinTrueArgs (by decide)
    diamondMoveJoinTrueMInit rfl rfl rfl diamondMoveJoinTrue_noUB n

theorem diamondMoveJoinTrue_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n diamondMoveJoinTrueMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 8 } ∧
      m'.threads = [thread1 ctx0_2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret diamondMoveJoin_inFragment diamondMoveJoin_translate ctx0_2
      (ctx0_2_ok_bool_u32 rfl) diamondMoveJoinTrueArgs (by decide)
      diamondMoveJoinTrueMInit rfl rfl rfl diamondMoveJoinTrue_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [diamondMoveJoin] at hd; subst hd
  simp [retPtr, ctx0_2, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0_2, ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem diamondMoveJoinTrue_minirust_direct :
    (Interp.steps 9 diamondMoveJoinTrueMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 8 }, [1]) := by
  decide +kernel

def diamondMoveJoinFalseArgs : List Value := [.scalar ⟨0, 1⟩, .scalar ⟨7, 4⟩]
def diamondMoveJoinFalseS0 : MachineState :=
  initMachineState diamondMoveJoin diamondMoveJoinFalseArgs
def diamondMoveJoinFalseMInit : Mach :=
  machineWithCtx ctx0_2 diamondMoveJoin diamondMoveJoinFn
    diamondMoveJoinFalseS0.frame.locals diamondMoveJoinFn.start

theorem diamondMoveJoinFalse_anneal_ret :
    ReachesRet (mirTree diamondMoveJoin diamondMoveJoinFalseS0)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨14, 4⟩, diamondMoveJoinFalseS0.memory)) :=
  runA_sound diamondMoveJoin 20 _ _ _ rfl

theorem diamondMoveJoinFalse_noUB :
    MirNoUBTree (mirCallTree diamondMoveJoin diamondMoveJoinFalseArgs) :=
  runA_noUB diamondMoveJoin 20 _ _ _ rfl

theorem diamondMoveJoinFalse_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen diamondMoveJoin + n) diamondMoveJoinFalseMInit = .ok m' ∧
      StateRel diamondMoveJoin diamondMoveJoinFn ctx0_2 s' m' ∧
      Reaches (mirCallTree diamondMoveJoin diamondMoveJoinFalseArgs) tr
        (mirTree diamondMoveJoin s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen diamondMoveJoin + n ∧
      Interp.steps k diamondMoveJoinFalseMInit = .ok mRet ∧
      ReturnRel diamondMoveJoin ctx0_2 s' v mRet ∧
      ReachesRet (mirCallTree diamondMoveJoin diamondMoveJoinFalseArgs) tr
        (.normal (v, mem))) :=
  mirCall_progress diamondMoveJoin_inFragment diamondMoveJoin_translate ctx0_2
    (ctx0_2_ok_bool_u32 rfl) diamondMoveJoinFalseArgs (by decide)
    diamondMoveJoinFalseMInit rfl rfl rfl diamondMoveJoinFalse_noUB n

theorem diamondMoveJoinFalse_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n diamondMoveJoinFalseMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 14 } ∧
      m'.threads = [thread1 ctx0_2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret diamondMoveJoin_inFragment diamondMoveJoin_translate ctx0_2
      (ctx0_2_ok_bool_u32 rfl) diamondMoveJoinFalseArgs (by decide)
      diamondMoveJoinFalseMInit rfl rfl rfl diamondMoveJoinFalse_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [diamondMoveJoin] at hd; subst hd
  simp [retPtr, ctx0_2, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0_2, ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem diamondMoveJoinFalse_minirust_direct :
    (Interp.steps 8 diamondMoveJoinFalseMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 14 }, [1]) := by
  decide +kernel

/-- A 4-block diamond CFG where only `bb2` moves out of `_2` while `bb1` leaves
`_2` intact, and the merge block `bb3` reads `copy _2`: `movedAtEntry` unions
`[]` and `[2]` to `[2]` at `bb3`, so `movesOk` rejects the body. On
`(false, 7)`, Anneal faults with `.ub` at `copy _2` in `bb3`, whereas MiniRust
loads the stale `7` and returns `14`. -/
def diamondHalfMoveReuse : CapturedMir where
  defPath := "witness::diamond_half_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, boolDecl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 3)],
      terminator := mkTerm (.switchInt (.copy (local_ 1))
        { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 3) (.use (constU32 1)))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 3) (.use (.move (local_ 2))))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.move (local_ 3)) (.copy (local_ 2)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem diamondHalfMoveReuse_movesOk :
    [0, 1, 2, 3].map (movedAtEntry diamondHalfMoveReuse) = [[], [], [], [2]] ∧
    movesOk diamondHalfMoveReuse = false ∧
    inFragment diamondHalfMoveReuse = false := by decide

def diamondHalfMoveReuseFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Bool),
    (localName 2, .Int u32), (localName 3, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.StorageLive (localName 3)],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1))))
        ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[.Assign (.Local (localName 3)) (.Constant (.Int 1) (.Int u32))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 2, ⟨[.Assign (.Local (localName 3)) (.Load (.Local (localName 2)))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 3))) (.Load (.Local (localName 2)))),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem diamondHalfMoveReuse_translate :
    translateFn diamondHalfMoveReuse = some diamondHalfMoveReuseFn := rfl

def diamondHalfMoveReuseFalseS0 : MachineState :=
  initMachineState diamondHalfMoveReuse [.scalar ⟨0, 1⟩, .scalar ⟨7, 4⟩]

theorem diamondHalfMoveReuseFalse_anneal_ub :
    ∃ tr u, Reaches (mirTree diamondHalfMoveReuse diamondHalfMoveReuseFalseS0) tr u ∧
      FaultNow u :=
  faultsA_sound diamondHalfMoveReuse 15 _ (by decide)

theorem diamondHalfMoveReuseFalse_minirust_direct :
    (Interp.steps 8 (machineWithCtx ctx0_2 diamondHalfMoveReuse diamondHalfMoveReuseFn
        diamondHalfMoveReuseFalseS0.frame.locals diamondHalfMoveReuseFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 14 }, [1]) := by
  decide +kernel

/-- Caller context for `tupleAggCastMove` and `projFieldMoveReuse`. -/
def ctx0_tupleAggCastMove : Ctx :=
  { ctx0 with addrs := [128, 256, 384, 512, 640, 768] }

theorem ctx0_ok_tupleAggCastMove {body : CapturedMir}
    (h : body.localDecls = [u32Decl, i8Decl, i8Decl, u32Decl, boolDecl, u32BoolTupleDecl]) :
    CtxOk body ctx0_tupleAggCastMove where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | 3, hd => simp at hd; subst hd; decide
    | 4, hd => simp at hd; subst hd; decide
    | 5, hd => simp at hd; subst hd; decide
    | _ + 6, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- `tupleAggCastMove`: `fn(x: i8) -> u32` exercising `Operand::Move` across
`Rvalue::UnaryOp(Neg, move _1)` on `i8`, `Rvalue::Cast(IntToInt, move _2, u32)`
from `i8` to `u32`, `Rvalue::UnaryOp(Not, move _4)` on `bool` (self-assign
move), `Rvalue::Aggregate(Tuple, [move _3, move _4])` constructing a `(u32, bool)`
tuple from two moved operands, and `Rvalue::Use(move (_5.0))` projected field
move followed by `StorageDead(_5)`. -/
def tupleAggCastMove : CapturedMir where
  defPath := "witness::tuple_agg_cast_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, i8Decl, i8Decl, u32Decl, boolDecl, u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.unaryOp .neg (.move (local_ 1)))),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.cast .intToInt (.move (local_ 2)) u32Ty)),
        mkStmt (.storageDead 2),
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.binaryOp .gt (.copy (local_ 3)) (constU32 0))),
        mkStmt (.assign (local_ 4) (.unaryOp .not (.move (local_ 4)))),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.aggregate .tuple [.move (local_ 3), .move (local_ 4)])),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 4),
        mkStmt (.assign (local_ 0) (.use (.move (field0U32 5)))),
        mkStmt (.storageDead 5)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem tupleAggCastMove_inFragment : inFragment tupleAggCastMove = true := by decide

/-- `CtxOk.addrs` constrains only `_0` and the arguments (`i ≤ body.argCount`),
so unaligned (`257`) or `≥ 2^32` (`2^40`) trailing entries in `ctx.addrs` at
temporary indices `i > argCount` remain valid caller contexts. -/
theorem ctx0_ok_trailing_temp_addrs :
    CtxOk tupleAggCastMove { ctx0 with addrs := [128, 256, 257, 2 ^ 40] } where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [tupleAggCastMove] at hd; subst hd; decide
    | 1, _, hd => simp [tupleAggCastMove] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [tupleAggCastMove] at hi
  ret := by
    intro d hd; simp [tupleAggCastMove] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def tupleAggCastMoveFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, .Int u32), (localName 4, .Bool), (localName 5, intBoolTupleTy u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.UnOp (.Int .Neg) (.Load (.Local (localName 1)))),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 2)))),
      .StorageDead (localName 2),
      .StorageLive (localName 4),
      .Assign (.Local (localName 4))
        (.BinOp (.Rel .Gt) (.Load (.Local (localName 3))) (.Constant (.Int 0) (.Int u32))),
      .Assign (.Local (localName 4)) (boolNot (.Load (.Local (localName 4)))),
      .StorageLive (localName 5),
      .Assign (.Local (localName 5))
        (.Tuple [.Load (.Local (localName 3)), .Load (.Local (localName 4))]
          (intBoolTupleTy u32)),
      .StorageDead (localName 3),
      .StorageDead (localName 4),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 5)) 0)),
      .StorageDead (localName 5)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem tupleAggCastMove_translate :
    translateFn tupleAggCastMove = some tupleAggCastMoveFn := rfl

def tupleAggCastMoveNeg5Args : List Value := [.scalar ⟨251, 1⟩]
def tupleAggCastMoveNeg5S0 : MachineState :=
  initMachineState tupleAggCastMove tupleAggCastMoveNeg5Args
def tupleAggCastMoveNeg5MInit : Mach :=
  machineWithCtx ctx0_tupleAggCastMove tupleAggCastMove tupleAggCastMoveFn
    tupleAggCastMoveNeg5S0.frame.locals tupleAggCastMoveFn.start

theorem tupleAggCastMoveNeg5_anneal_ret :
    ReachesRet (mirTree tupleAggCastMove tupleAggCastMoveNeg5S0) []
      (.normal (.scalar ⟨5, 4⟩, tupleAggCastMoveNeg5S0.memory)) :=
  runA_sound tupleAggCastMove 25 _ _ _ rfl

theorem tupleAggCastMoveNeg5_noUB :
    MirNoUBTree (mirCallTree tupleAggCastMove tupleAggCastMoveNeg5Args) :=
  runA_noUB tupleAggCastMove 25 _ _ _ rfl

theorem tupleAggCastMoveNeg5_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen tupleAggCastMove + n) tupleAggCastMoveNeg5MInit = .ok m' ∧
      StateRel tupleAggCastMove tupleAggCastMoveFn ctx0_tupleAggCastMove s' m' ∧
      Reaches (mirCallTree tupleAggCastMove tupleAggCastMoveNeg5Args) tr
        (mirTree tupleAggCastMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen tupleAggCastMove + n ∧
      Interp.steps k tupleAggCastMoveNeg5MInit = .ok mRet ∧
      ReturnRel tupleAggCastMove ctx0_tupleAggCastMove s' v mRet ∧
      ReachesRet (mirCallTree tupleAggCastMove tupleAggCastMoveNeg5Args) tr
        (.normal (v, mem))) :=
  mirCall_progress tupleAggCastMove_inFragment tupleAggCastMove_translate ctx0_tupleAggCastMove
    (ctx0_ok_tupleAggCastMove rfl) tupleAggCastMoveNeg5Args (by decide)
    tupleAggCastMoveNeg5MInit rfl rfl rfl tupleAggCastMoveNeg5_noUB n

theorem tupleAggCastMoveNeg5_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n tupleAggCastMoveNeg5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 5 } ∧
      m'.threads = [thread1 ctx0_tupleAggCastMove
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret tupleAggCastMove_inFragment tupleAggCastMove_translate ctx0_tupleAggCastMove
      (ctx0_ok_tupleAggCastMove rfl) tupleAggCastMoveNeg5Args (by decide)
      tupleAggCastMoveNeg5MInit rfl rfl rfl tupleAggCastMoveNeg5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [tupleAggCastMove] at hd; subst hd
  simp [retPtr, ctx0_tupleAggCastMove, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0_tupleAggCastMove, ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem tupleAggCastMoveNeg5_minirust_direct :
    (Interp.steps 16 tupleAggCastMoveNeg5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?,
          m.mem.memory.allocations.map (·.live),
          m.mem.memory.allocations.map (·.addr),
          m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 5 },
        [true, false, false, false, false, false, false],
        [64, 128, 256, 2 ^ 32, 2 * 2 ^ 32, 2 ^ 32, 3 * 2 ^ 32],
        [1]) := by
  decide +kernel

/-- Projected field read after root tuple move (`projFieldMoveReuse`):
moving out of the root tuple `_3` (`_4 = Use(move _3)`) deinitializes `_3` in
Anneal's `evalOperand` (`s.frame.locals[3] := .uninit`), so subsequently
reading the projected field `_3.0` (`_0 = Use(copy (_3.0))`) faults with `.ub`
in Anneal while succeeding in MiniRust (which translates `move _3` to
`Load(Local(_3))` without deinitializing `_3`). `movesOk` rejects
`projFieldMoveReuse` because `opMoved (.move (local_ 3)) = some 3` marks local
`3` moved out and `opRead (.copy (field0U32 3)) = some 3` detects the projected
read of `3`. -/
def projFieldMoveReuse : CapturedMir where
  defPath := "witness::proj_field_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, boolDecl, u32BoolTupleDecl, u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.aggregate .tuple [.move (local_ 1), .move (local_ 2)])),
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.use (.move (local_ 3)))),
        mkStmt (.assign (local_ 0) (.use (.copy (field0U32 3)))),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem projFieldMoveReuse_movesOk :
    movesOk projFieldMoveReuse = false ∧
    inFragment projFieldMoveReuse = false := by decide

def projFieldMoveReuseFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Bool),
    (localName 3, intBoolTupleTy u32), (localName 4, intBoolTupleTy u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.Tuple [.Load (.Local (localName 1)), .Load (.Local (localName 2))]
          (intBoolTupleTy u32)),
      .StorageLive (localName 4),
      .Assign (.Local (localName 4)) (.Load (.Local (localName 3))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 3)) 0)),
      .StorageDead (localName 4),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem projFieldMoveReuse_translate :
    translateFn projFieldMoveReuse = some projFieldMoveReuseFn := rfl

def projFieldMoveReuseS0 : MachineState :=
  initMachineState projFieldMoveReuse [.scalar ⟨11, 4⟩, .scalar ⟨1, 1⟩]

theorem projFieldMoveReuse_anneal_ub :
    ∃ tr u, Reaches (mirTree projFieldMoveReuse projFieldMoveReuseS0) tr u ∧
      FaultNow u :=
  faultsA_sound projFieldMoveReuse 15 _ (by decide)

theorem projFieldMoveReuse_minirust_direct :
    (Interp.steps 9 (machineWithCtx ctx0_tupleAggCastMove projFieldMoveReuse projFieldMoveReuseFn
        projFieldMoveReuseS0.frame.locals projFieldMoveReuseFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 11 }, [1]) := by
  decide +kernel

/-! ## `ord_bool_cast_temp_move`: `Ordering` temporaries & moved-`bool` cast -/

/-- `ordBoolCastTempMove`: `fn(a: i8, b: i8, flag: bool) -> Ordering` exercising
`Rvalue::Cast(IntToInt, move _3, u32)` from a moved `bool` parameter (`boolToU8`
followed by `IntToInt`), `SwitchInt(move _4)` on the cast temporary, explicit
`StorageLive(_5)` / `BinaryOp(Cmp, move _, move _)` / `Use(move _5)` /
`Deinit(_5)` / `StorageDead(_5)` on a `core::cmp::Ordering` (`Type::Enum`)
temporary local reusing `_4`'s freed `2^32` address, and `ctxI8_4` directly
(`addrs` of length `4 = argCount + 1` with `6` total `localDecls`). -/
def ordBoolCastTempMove : CapturedMir where
  defPath := "witness::ord_bool_cast_temp_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [orderingDecl, i8Decl, i8Decl, boolDecl, u32Decl, orderingDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.cast .intToInt (.move (local_ 3)) u32Ty))],
      terminator := mkTerm (.switchInt (.move (local_ 4))
        { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 4),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.binaryOp .cmp (.move (local_ 1)) (.move (local_ 2))))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 4),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.binaryOp .cmp (.move (local_ 2)) (.move (local_ 1))))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.move (local_ 5)))),
        mkStmt (.deinit (local_ 5)),
        mkStmt (.storageDead 5)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbiCmpSel
  layouts := emptyLayoutTable
  allocations := []

theorem ctxI8_ok_ordBoolCastTempMove : CtxOk ordBoolCastTempMove ctxI8_4 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [ordBoolCastTempMove] at hd; subst hd; decide
    | 1, _, hd => simp [ordBoolCastTempMove] at hd; subst hd; decide
    | 2, _, hd => simp [ordBoolCastTempMove] at hd; subst hd; decide
    | 3, _, hd => simp [ordBoolCastTempMove] at hd; subst hd; decide
    | _ + 4, hi, _ => simp [ordBoolCastTempMove] at hi
  ret := by
    intro d hd; simp [ordBoolCastTempMove] at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem ordBoolCastTempMove_inFragment : inFragment ordBoolCastTempMove = true := by decide

theorem ordBoolCastTempMove_movedAtEntry :
    [0, 1, 2, 3].map (movedAtEntry ordBoolCastTempMove) =
      [[], [3, 4], [3, 4], [3, 1, 2]] := by decide

/-- Concrete Park-induction witness for `movesOk_of_preFixedPoint` using a
strictly over-approximating inductive pre-fixed point `[[5], [3, 4, 5],
[3, 4, 5], [1, 2, 3]]` (which marks `_5` moved out on entry to `bb0`, unlike
the least fixed point `movedAtEntry`). -/
theorem ordBoolCastTempMove_movesOk_by_preFixedPoint :
    movesOk ordBoolCastTempMove = true := by
  let cert : List (List Nat) := [[5], [3, 4, 5], [3, 4, 5], [1, 2, 3]]
  apply movesOk_of_preFixedPoint (by decide) (by decide) cert
  · intro src dst bb hbb hdst htgt j hj
    have hsrc : src < 4 := by
      have := (List.getElem?_eq_some_iff.mp hbb).1
      simpa [ordBoolCastTempMove] using this
    have hdst' : dst < 4 := by simpa [ordBoolCastTempMove] using hdst
    revert bb hbb htgt j hj
    rcases (by omega : src = 0 ∨ src = 1 ∨ src = 2 ∨ src = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : dst = 0 ∨ dst = 1 ∨ dst = 2 ∨ dst = 3) with rfl | rfl | rfl | rfl <;>
    (intro bb hbb; simp [ordBoolCastTempMove] at hbb; subst hbb; decide)
  · intro blk bb hbb
    have hblk : blk < 4 := by
      have := (List.getElem?_eq_some_iff.mp hbb).1
      simpa [ordBoolCastTempMove] using this
    revert bb hbb
    rcases (by omega : blk = 0 ∨ blk = 1 ∨ blk = 2 ∨ blk = 3) with rfl | rfl | rfl | rfl <;>
    (intro bb hbb; simp [ordBoolCastTempMove] at hbb; subst hbb; decide)

def ordBoolCastTempMoveFn : Gen.Function where
  locals := ⟨[(localName 0, orderingTy), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, .Bool), (localName 4, .Int u32), (localName 5, orderingTy)]⟩
  args := [localName 1, localName 2, localName 3]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 4),
      .Assign (.Local (localName 4))
        (.UnOp (.Cast (.IntToInt u32)) (boolToU8 (.Load (.Local (localName 3)))))],
      .Switch (.Load (.Local (localName 4))) ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .StorageDead (localName 4),
      .StorageLive (localName 5),
      .Assign (.Local (localName 5))
        (translateCmp (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 2, ⟨[
      .StorageDead (localName 4),
      .StorageLive (localName 5),
      .Assign (.Local (localName 5))
        (translateCmp (.Load (.Local (localName 2))) (.Load (.Local (localName 1))))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 5))),
      .Deinit (.Local (localName 5)),
      .StorageDead (localName 5)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem ordBoolCastTempMove_translate :
    translateFn ordBoolCastTempMove = some ordBoolCastTempMoveFn := rfl

def ordBoolCastTempMoveTrueArgs : List Value :=
  [.scalar ⟨251, 1⟩, .scalar ⟨3, 1⟩, .scalar ⟨1, 1⟩]
def ordBoolCastTempMoveTrueS0 : MachineState :=
  initMachineState ordBoolCastTempMove ordBoolCastTempMoveTrueArgs
def ordBoolCastTempMoveTrueMInit : Mach :=
  machineWithCtx ctxI8_4 ordBoolCastTempMove ordBoolCastTempMoveFn
    ordBoolCastTempMoveTrueS0.frame.locals ordBoolCastTempMoveFn.start

theorem ordBoolCastTempMoveTrue_anneal_ret :
    ReachesRet (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveTrueArgs)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨255, 1⟩, ordBoolCastTempMoveTrueS0.memory)) :=
  runA_sound ordBoolCastTempMove 20 _ _ _ rfl

theorem ordBoolCastTempMoveTrue_noUB :
    MirNoUBTree (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveTrueArgs) :=
  runA_noUB ordBoolCastTempMove 20 _ _ _ rfl

theorem ordBoolCastTempMoveTrue_progress (n : Nat) :
    (∃ s' m' tr,
      Interp.steps (initLen ordBoolCastTempMove + n) ordBoolCastTempMoveTrueMInit = .ok m' ∧
      StateRel ordBoolCastTempMove ordBoolCastTempMoveFn ctxI8_4 s' m' ∧
      Reaches (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveTrueArgs) tr
        (mirTree ordBoolCastTempMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen ordBoolCastTempMove + n ∧
      Interp.steps k ordBoolCastTempMoveTrueMInit = .ok mRet ∧
      ReturnRel ordBoolCastTempMove ctxI8_4 s' v mRet ∧
      ReachesRet (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveTrueArgs) tr
        (.normal (v, mem))) :=
  mirCall_progress ordBoolCastTempMove_inFragment ordBoolCastTempMove_translate ctxI8_4
    ctxI8_ok_ordBoolCastTempMove ordBoolCastTempMoveTrueArgs (by decide)
    ordBoolCastTempMoveTrueMInit rfl rfl rfl ordBoolCastTempMoveTrue_noUB n

theorem ordBoolCastTempMoveTrue_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n ordBoolCastTempMoveTrueMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 255 } ∧
      m'.threads = [thread1 ctxI8_4
        [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret ordBoolCastTempMove_inFragment ordBoolCastTempMove_translate ctxI8_4
      ctxI8_ok_ordBoolCastTempMove ordBoolCastTempMoveTrueArgs (by decide)
      ordBoolCastTempMoveTrueMInit rfl rfl rfl ordBoolCastTempMoveTrue_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [ordBoolCastTempMove] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem ordBoolCastTempMoveTrue_minirust_direct :
    (Interp.steps 12 ordBoolCastTempMoveTrueMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?,
          m.mem.memory.allocations.map (·.live),
          m.mem.memory.allocations.map (·.addr),
          m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 255 },
        [true, false, false, false, false, false, false],
        [64, 128, 256, 384, 512, 2 ^ 32, 2 ^ 32],
        [1]) := by
  decide +kernel

def ordBoolCastTempMoveFalseArgs : List Value :=
  [.scalar ⟨251, 1⟩, .scalar ⟨3, 1⟩, .scalar ⟨0, 1⟩]
def ordBoolCastTempMoveFalseS0 : MachineState :=
  initMachineState ordBoolCastTempMove ordBoolCastTempMoveFalseArgs
def ordBoolCastTempMoveFalseMInit : Mach :=
  machineWithCtx ctxI8_4 ordBoolCastTempMove ordBoolCastTempMoveFn
    ordBoolCastTempMoveFalseS0.frame.locals ordBoolCastTempMoveFn.start

theorem ordBoolCastTempMoveFalse_anneal_ret :
    ReachesRet (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveFalseArgs)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, ordBoolCastTempMoveFalseS0.memory)) :=
  runA_sound ordBoolCastTempMove 20 _ _ _ rfl

theorem ordBoolCastTempMoveFalse_noUB :
    MirNoUBTree (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveFalseArgs) :=
  runA_noUB ordBoolCastTempMove 20 _ _ _ rfl

theorem ordBoolCastTempMoveFalse_progress (n : Nat) :
    (∃ s' m' tr,
      Interp.steps (initLen ordBoolCastTempMove + n) ordBoolCastTempMoveFalseMInit = .ok m' ∧
      StateRel ordBoolCastTempMove ordBoolCastTempMoveFn ctxI8_4 s' m' ∧
      Reaches (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveFalseArgs) tr
        (mirTree ordBoolCastTempMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen ordBoolCastTempMove + n ∧
      Interp.steps k ordBoolCastTempMoveFalseMInit = .ok mRet ∧
      ReturnRel ordBoolCastTempMove ctxI8_4 s' v mRet ∧
      ReachesRet (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveFalseArgs) tr
        (.normal (v, mem))) :=
  mirCall_progress ordBoolCastTempMove_inFragment ordBoolCastTempMove_translate ctxI8_4
    ctxI8_ok_ordBoolCastTempMove ordBoolCastTempMoveFalseArgs (by decide)
    ordBoolCastTempMoveFalseMInit rfl rfl rfl ordBoolCastTempMoveFalse_noUB n

theorem ordBoolCastTempMoveFalse_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n ordBoolCastTempMoveFalseMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 1 } ∧
      m'.threads = [thread1 ctxI8_4
        [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret ordBoolCastTempMove_inFragment ordBoolCastTempMove_translate ctxI8_4
      ctxI8_ok_ordBoolCastTempMove ordBoolCastTempMoveFalseArgs (by decide)
      ordBoolCastTempMoveFalseMInit rfl rfl rfl ordBoolCastTempMoveFalse_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [ordBoolCastTempMove] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem ordBoolCastTempMoveFalse_minirust_direct :
    (Interp.steps 12 ordBoolCastTempMoveFalseMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?,
          m.mem.memory.allocations.map (·.live),
          m.mem.memory.allocations.map (·.addr),
          m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 1 },
        [true, false, false, false, false, false, false],
        [64, 128, 256, 384, 512, 2 ^ 32, 2 ^ 32],
        [1]) := by
  decide +kernel

/-! ## Multi-function `Terminator::Call` & `Return` stack witnesses (`MR-4.1`) -/

/-- Extract `some msg` when an `Interp` computation stops with `.error (.ub msg)`. -/
def ubMsg? {α : Type} : Interp α → Option String
  | .error (.ub msg) => some msg
  | _ => none

private theorem eq_error_ub_of_ubMsg? {α : Type} {x : Interp α} {msg : String}
    (h : ubMsg? x = some msg) : x = .error (.ub msg) := by
  cases x with
  | ok _ => simp [ubMsg?] at h
  | error e =>
    cases e <;> simp [ubMsg?] at h ⊢
    exact h

/-- Direct-call function-item constant operand (`TyKind.fnDef dp []` with
`MirConstVal.zeroSized`), recognized by both `Translate.extractFnDefPath` and
`MirSemantics.extractCalleeDefPath?`. -/
def fnDefOp (dp : String) : Operand :=
  .constant { ty := { kind := .fnDef dp [], layoutIdx := 0 }, val := .zeroSized }

/-- Root caller context with `retA` at allocation index `0` (address `64`) and
`fnAllocs nFns` (`AllocationKind::Function` allocations at addresses `16 + k`
for `0 ≤ k < nFns`) at indices `1 .. nFns`, plus root locals at `addrs`. -/
def ctxWithFns (caller : Frame) (retA : Gen.Allocation) (nFns : Nat)
    (addrs : List Int) : Ctx :=
  { caller := caller, payloads := [], base := retA :: fnAllocs nFns,
    addrs := addrs, nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

/-- Multi-function MiniRust machine running `fEntry` from `prog` under caller
context `rootCtx` with `fnPtrMap 1 nFns` and initial Anneal locals `locals` at
`blk`. -/
def multiMachineWithCtx (rootCtx : Ctx) (prog : Gen.Program) (nFns : Nat)
    (entry : CapturedMir) (fEntry : Gen.Function) (locals : List LocalSlot)
    (blk : Gen.BbName) : Mach :=
  { prog := prog,
    mem := { memory := { allocations := rootCtx.base ++
                           localAllocs rootCtx
                             (entry.localDecls.take (entry.argCount + 1)) locals,
                         _phantom := {} },
             accesses := [] },
    intptrcast := ⟨⟨[]⟩⟩,
    threads := [thread1 rootCtx [rootCtx.caller,
      { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := blk }]],
    active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [], global_ptrs := ⟨[]⟩,
    fn_ptrs := fnPtrMap 1 nFns, vtable_ptrs := ⟨[]⟩, stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

/-! ### `callerMain` invoking `calleePair` (`ByValue` + `InPlace` args & `Call + initBlock`) -/

def tupleU32Layout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiCalleePair : FnAbi :=
  { args := [{ layout := u32Layout, mode := .direct },
      { layout := tupleU32Layout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn callee_pair(a: u32, pair: (u32, bool)) -> u32 {
    // unmarked _4: i8 allocated by callee initBlock (initLen = 2)
    let mut k: u32;             // bb0: StorageLive(_3); _3 = const 7_u32
    if pair.1 {                 //      switchInt(copy (_2.1)) -> [0: bb1, otherwise: bb2]
        a.wrapping_sub(k)       // bb2: _0 = Sub(copy _1, move _3); Deinit(_3); StorageDead(_3); return
    } else {
        pair.0.wrapping_add(k)  // bb1: _0 = Add(copy (_2.0), move _3); Deinit(_3); StorageDead(_3); return
    }
}
```
Having both an unmentioned unmarked local (`_4 : i8`, allocated in `calleePair`'s
`initBlock`, so `initLen calleePair = 2`) and a `StorageLive` local (`_3 : u32`)
makes entering `calleePair` take `3` MiniRust steps (`Terminator::Call` plus
`StorageLive(_4)` plus `Goto(bb0)`) for one Anneal `.tau` call step. -/
def calleePair : CapturedMir where
  defPath := "witness::callee_pair"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32BoolTupleDecl, u32Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.use (constU32 7)))],
      terminator := mkTerm (.switchInt (.copy (field1 2)) { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (field0U32 2)) (.move (local_ 3)))),
        mkStmt (.deinit (local_ 3)),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 1)) (.move (local_ 3)))),
        mkStmt (.deinit (local_ 3)),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCalleePair
  layouts := emptyLayoutTable
  allocations := []

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn caller_main(x: u32, y: u32) -> u32 {
    let pair = AddWithOverflow(x, y);   // bb0: StorageLive(_3); StorageLive(_4); _3 = AddWithOverflow(copy _1, copy _2)
    let r = callee_pair(x, move pair);  //      _4 = Call(callee_pair, [copy _1, move _3]) -> [return: bb1, unwind: continue]
    r.wrapping_add(x)                   // bb1: _0 = Add(move _4, copy _1); StorageDead(_4); StorageDead(_3); return
}
```
Passes `_1` by value (`ArgumentExpr::ByValue`, leaving `_1` live for `bb1`) and
`_3 : (u32, bool)` in place (`ArgumentExpr::InPlace`, deinitializing `_3` to
`Uninit` bytes in MiniRust memory before entering `calleePair`). -/
def callerMain : CapturedMir where
  defPath := "witness::caller_main"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32Decl, u32BoolTupleDecl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 3) (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm (.call (fnDefOp "witness::callee_pair")
        [.copy (local_ 1), .move (local_ 3)] (local_ 4) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.move (local_ 4)) (.copy (local_ 1)))),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem callerCallee_inFragment : progInFragment callerMain [calleePair] = true := by decide

theorem calleePair_initLen : initLen calleePair = 2 := rfl

def callerMainFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, intBoolTupleTy u32), (localName 4, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3),
      .StorageLive (localName 4),
      .Assign (.Local (localName 3))
        (.BinOp (.IntWithOverflow .Add) (.Load (.Local (localName 1)))
          (.Load (.Local (localName 2))))],
      .Call (fnPtrExpr (fnName 1)) .Rust
        [.ByValue (.Load (.Local (localName 1))), .InPlace (.Local (localName 3))]
        (.Local (localName 4)) (some (bbName 1)) (some (bbName 3)), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 4))) (.Load (.Local (localName 1)))),
      .StorageDead (localName 4),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩),
    (bbName 3, ⟨[], .ResumeUnwind, .Cleanup⟩)]⟩
  start := bbName 2
  implicit_writes := true

def calleePairFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, intBoolTupleTy u32), (localName 3, .Int u32), (localName 4, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3),
      .Assign (.Local (localName 3)) (.Constant (.Int 7) (.Int u32))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Field (.Local (localName 2)) 1)))
        ⟨[(0, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Field (.Local (localName 2)) 0))
          (.Load (.Local (localName 3)))),
      .Deinit (.Local (localName 3)),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 1))) (.Load (.Local (localName 3)))),
      .Deinit (.Local (localName 3)),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 3, ⟨[.StorageLive (localName 4)], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

def callerCalleeProg : Gen.Program where
  functions := ⟨[(fnName 0, callerMainFn), (fnName 1, calleePairFn), (fnName 2, mkStartFn 0)]⟩
  start := fnName 2
  globals := ⟨[]⟩
  vtables := ⟨[]⟩
  traits := ⟨[]⟩

theorem callerCallee_translate :
    translateProg callerMain [calleePair] = some callerCalleeProg := rfl

theorem callerMain_translateInProg :
    translateFnInProg (fnNameMap callerMain [calleePair]) callerMain = some callerMainFn := rfl

def ctxCallerMain : Ctx :=
  ctxWithFns callerFrame retAlloc 2 [128, 256, 384]

theorem ctxCallerMain_ok : CtxOk callerMain ctxCallerMain where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [callerMain] at hd; subst hd; decide
    | 1, _, hd => simp [callerMain] at hd; subst hd; decide
    | 2, _, hd => simp [callerMain] at hd; subst hd; decide
    | _ + 3, hi, _ => simp [callerMain] at hi
  ret := by
    intro d hd; simp [callerMain] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- Non-overflow call `(20u32, 5u32)`: `AddWithOverflow(20, 5) = (25, false)`,
`calleePair(20, (25, false)) = 25 + 7 = 32`, and `callerMain` returns
`32 + 20 = 52u32`. -/
def callerCallee20Args : List Value := [.scalar ⟨20, 4⟩, .scalar ⟨5, 4⟩]
def callerCallee20S0 : MachineState :=
  initMachineStateWithCallees callerMain callerCallee20Args [calleePair]
def callerCallee20MInit : Mach :=
  multiMachineWithCtx ctxCallerMain callerCalleeProg 2 callerMain callerMainFn
    callerCallee20S0.frame.locals callerMainFn.start

theorem callerCallee20_anneal_ret :
    ReachesRet (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair])
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨52, 4⟩,
        { callerCallee20S0.memory with activeCallee := some callerMain })) :=
  runA_sound callerMain 25 _ _ _ rfl

theorem callerCallee20_noUB :
    MirNoUBTree (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) :=
  runA_noUB callerMain 25 _ _ _ rfl

theorem callerCallee20_progress (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps (initLen callerMain + n) callerCallee20MInit = .ok m0 ∧
      Interp.steps (initLen callerMain + n + d) callerCallee20MInit = .ok m' ∧
      MultiStateRel callerMain [calleePair] callerCalleeProg ctxCallerMain s' m' ∧
      Reaches (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (mirTree callerMain s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen callerMain + n ∧
      Interp.steps k callerCallee20MInit = .ok mRet ∧
      ReturnRel callerMain ctxCallerMain s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (.normal (v, mem))) :=
  mirCallWithCallees_progress callerCallee_inFragment callerCallee_translate
    callerMain_translateInProg ctxCallerMain ctxCallerMain_ok callerCallee20Args (by decide)
    callerCallee20MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callerCallee20_noUB n

theorem callerCallee20_progress_any (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps n callerCallee20MInit = .ok m0 ∧
      Interp.steps (n + d) callerCallee20MInit = .ok m' ∧
      MultiStateRel callerMain [calleePair] callerCalleeProg ctxCallerMain s' m' ∧
      Reaches (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (mirTree callerMain s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧
      Interp.steps k callerCallee20MInit = .ok mRet ∧
      ReturnRel callerMain ctxCallerMain s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (.normal (v, mem))) :=
  mirCallWithCallees_progress_any callerCallee_inFragment callerCallee_translate
    callerMain_translateInProg ctxCallerMain ctxCallerMain_ok callerCallee20Args (by decide)
    callerCallee20MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callerCallee20_noUB n

theorem callerCallee20_outcome_any (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps n callerCallee20MInit = .ok m0 ∧
      Interp.steps (n + d) callerCallee20MInit = .ok m' ∧
      MultiStateRel callerMain [calleePair] callerCalleeProg ctxCallerMain s' m' ∧
      Reaches (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (mirTree callerMain s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧
      Interp.steps k callerCallee20MInit = .ok mRet ∧
      ReturnRel callerMain ctxCallerMain s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (.normal (v, mem))) ∨
    (∃ msg, Interp.steps n callerCallee20MInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr u ∧
        FaultNow u) :=
  mirCallWithCallees_outcome_any callerCallee_inFragment callerCallee_translate
    callerMain_translateInProg ctxCallerMain ctxCallerMain_ok callerCallee20Args (by decide)
    callerCallee20MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl n

theorem callerCallee20_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n callerCallee20MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 52 } ∧
      m'.threads = [thread1 ctxCallerMain
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret callerCallee_inFragment callerCallee_translate
      callerMain_translateInProg ctxCallerMain ctxCallerMain_ok callerCallee20Args (by decide)
      callerCallee20MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      callerCallee20_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [callerMain] at hd; subst hd
  simp [retPtr, ctxCallerMain, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallerMain, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- Mid-call snapshot right after `Terminator::Call` (step `5`, before
`calleePair`'s 2-step `initBlock` completes): the thread stack has depth `3`
(`[callerFrame, callerMainFn, calleePairFn]`), and `callerMain`'s moved tuple
local `_3` (allocation `6`) has been deinitialized to 8 `Uninit` bytes by
`ArgumentExpr::InPlace`. -/
theorem callerCallee20_midCall_step5 :
    (Interp.steps 5 callerCallee20MInit).toOption.map
        (fun m => (m.threads.map (·.stack.length),
          (m.mem.memory.allocations[6]?).map (·.data))) =
      some ([3], some (List.replicate 8 .Uninit)) := by
  decide +kernel

theorem callerCallee20_minirust_direct :
    (Interp.steps 18 callerCallee20MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 52 }, [1]) := by
  decide +kernel

/-- Overflow call `(u32::MAX, 5u32)`: `AddWithOverflow(4294967295, 5) = (4, true)`,
`calleePair` takes `bb2` (`4294967295 - 7 = 4294967288`), and `callerMain`
returns `4294967288.wrapping_add(4294967295) = 4294967287u32`. -/
def callerCalleeOvArgs : List Value := [.scalar ⟨4294967295, 4⟩, .scalar ⟨5, 4⟩]
def callerCalleeOvS0 : MachineState :=
  initMachineStateWithCallees callerMain callerCalleeOvArgs [calleePair]
def callerCalleeOvMInit : Mach :=
  multiMachineWithCtx ctxCallerMain callerCalleeProg 2 callerMain callerMainFn
    callerCalleeOvS0.frame.locals callerMainFn.start

theorem callerCalleeOv_anneal_ret :
    ReachesRet (mirCallTreeWithCallees callerMain callerCalleeOvArgs [calleePair])
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨4294967287, 4⟩,
        { callerCalleeOvS0.memory with activeCallee := some callerMain })) :=
  runA_sound callerMain 25 _ _ _ rfl

theorem callerCalleeOv_noUB :
    MirNoUBTree (mirCallTreeWithCallees callerMain callerCalleeOvArgs [calleePair]) :=
  runA_noUB callerMain 25 _ _ _ rfl

theorem callerCalleeOv_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n callerCalleeOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? =
        some { retAlloc with data := scalarBytes u32 4294967287 } ∧
      m'.threads = [thread1 ctxCallerMain
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret callerCallee_inFragment callerCallee_translate
      callerMain_translateInProg ctxCallerMain ctxCallerMain_ok callerCalleeOvArgs (by decide)
      callerCalleeOvMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      callerCalleeOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [callerMain] at hd; subst hd
  simp [retPtr, ctxCallerMain, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallerMain, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem callerCalleeOv_minirust_direct :
    (Interp.steps 18 callerCalleeOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 4294967287 }, [1]) := by
  decide +kernel

/-! ### Projected tuple-field call destinations & sequential multi-call reuse -/

def fnAbiBool1 : FnAbi :=
  { args := [{ layout := boolLayout, mode := .direct }],
    ret := { layout := boolLayout, mode := .direct }, conv := .rust, canUnwind := false }

def negI8Callee : CapturedMir where
  defPath := "witness::neg_i8_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

def flipBoolCallee : CapturedMir where
  defPath := "witness::flip_bool_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [boolDecl, boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.unaryOp .not (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiBool1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller writing sequential call results into projected fields `_0.0`
(`CallerDestRel.field0`, `UnwindAction.unreachable`, preserving `_0.1`) and
`_0.1` (`CallerDestRel.field1`, `UnwindAction.terminate`, preserving `_0.0`) of
an initialized `(i8, bool)` return local `_0`. -/
def projDestCaller : CapturedMir where
  defPath := "witness::proj_dest_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8BoolTupleDecl, i8Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .addWithOverflow (.copy (local_ 1)) (constI8 1)))],
      terminator := mkTerm (.call (fnDefOp "witness::neg_i8_callee")
        [.copy (local_ 1)] (field0I8 0) (some 1) .unreachable),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (.copy (field1 0))))],
      terminator := mkTerm (.call (fnDefOp "witness::flip_bool_callee")
        [.copy (local_ 2)] (field1 0) (some 2) .terminate),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem projDestCaller_inFragment :
    progInFragment projDestCaller [negI8Callee, flipBoolCallee] = true := by decide

def retAllocTupleI8 : Gen.Allocation :=
  { data := List.replicate 2 .Uninit, addr := 64, align := ⟨1⟩, kind := .Stack, live := true,
    extra := () }

def callerFnTupleI8 : Gen.Function where
  locals := ⟨[(localName 0, intBoolTupleTy i8)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true

def callerFrameTupleI8 : Frame :=
  { func := callerFnTupleI8, locals := ⟨[(localName 0, retPtr)]⟩,
    stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }

def ctxProjDest : Ctx :=
  ctxWithFns callerFrameTupleI8 retAllocTupleI8 3 [128, 256]

theorem ctxProjDest_ok : CtxOk projDestCaller ctxProjDest where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [projDestCaller] at hd; subst hd; decide
    | 1, _, hd => simp [projDestCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [projDestCaller] at hi
  ret := by
    intro d hd; simp [projDestCaller] at hd; subst hd
    exact ⟨0, retAllocTupleI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

def projDestProg : Gen.Program :=
  (translateProg projDestCaller [negI8Callee, flipBoolCallee]).getD emptyProg

def projDestCallerFn : Gen.Function :=
  (translateFnInProg (fnNameMap projDestCaller [negI8Callee, flipBoolCallee])
    projDestCaller).getD callerFnTupleI8

theorem projDest_translate :
    translateProg projDestCaller [negI8Callee, flipBoolCallee] = some projDestProg := rfl

theorem projDestCaller_translateInProg :
    translateFnInProg (fnNameMap projDestCaller [negI8Callee, flipBoolCallee]) projDestCaller =
      some projDestCallerFn := rfl

/-- Input `127i8`: `AddWithOverflow(127i8, 1i8) = (-128i8, true)`,
`negI8Callee(127i8)` overwrites `_0.0` with `-127i8` (bits `129`) while leaving
`_0.1 = true`, and `flipBoolCallee(true)` overwrites `_0.1` with `false` while
leaving `_0.0 = -127i8`. -/
def projDest127Args : List Value := [.scalar ⟨127, 1⟩]
def projDest127S0 : MachineState :=
  initMachineStateWithCallees projDestCaller projDest127Args [negI8Callee, flipBoolCallee]
def projDest127MInit : Mach :=
  multiMachineWithCtx ctxProjDest projDestProg 3 projDestCaller projDestCallerFn
    projDest127S0.frame.locals projDestCallerFn.start

theorem projDest127_anneal_ret :
    ReachesRet
      (mirCallTreeWithCallees projDestCaller projDest127Args [negI8Callee, flipBoolCallee]) []
      (.normal (.aggregate 0 [.scalar ⟨129, 1⟩, .scalar ⟨0, 1⟩],
        { projDest127S0.memory with activeCallee := some projDestCaller })) :=
  runA_sound projDestCaller 25 _ _ _ rfl

theorem projDest127_noUB :
    MirNoUBTree
      (mirCallTreeWithCallees projDestCaller projDest127Args [negI8Callee, flipBoolCallee]) :=
  runA_noUB projDestCaller 25 _ _ _ rfl

theorem projDest127_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n projDest127MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? =
        some { retAllocTupleI8 with data := scalarBytes i8 129 ++ scalarBytes u8 0 } ∧
      m'.threads = [thread1 ctxProjDest
        [{ callerFrameTupleI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret projDestCaller_inFragment projDest_translate
      projDestCaller_translateInProg ctxProjDest ctxProjDest_ok projDest127Args (by decide)
      projDest127MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      projDest127_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [projDestCaller] at hd; subst hd
  simp [retPtr, ctxProjDest, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxProjDest, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem projDest127_minirust_direct :
    (Interp.steps 13 projDest127MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocTupleI8 with data := scalarBytes i8 129 ++ scalarBytes u8 0 },
        [1]) := by
  decide +kernel

/-! ### 3-deep nested call stack & `Ordering` enum ABI (`chainEntry -> chainMid -> chainLeaf`) -/

def chainLeaf : CapturedMir where
  defPath := "witness::chain_leaf"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [orderingDecl, i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .cmp (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

def chainMid : CapturedMir where
  defPath := "witness::chain_mid"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [orderingDecl, i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.unaryOp .neg (.copy (local_ 1))))],
      terminator := mkTerm (.call (fnDefOp "witness::chain_leaf")
        [.copy (local_ 1), .move (local_ 2)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

def chainEntry : CapturedMir where
  defPath := "witness::chain_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [orderingDecl, i8Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::chain_mid")
        [.move (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem chain3_inFragment :
    progInFragment chainEntry [chainMid, chainLeaf] = true := by decide

theorem chain3_maxStackLocals :
    maxStackLocals chainEntry [chainMid, chainLeaf] = some 8 := rfl

def ctxChainEntry : Ctx :=
  ctxWithFns callerFrameI8 retAllocI8 3 [128, 256]

theorem ctxChainEntry_ok : CtxOk chainEntry ctxChainEntry where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [chainEntry] at hd; subst hd; decide
    | 1, _, hd => simp [chainEntry] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [chainEntry] at hi
  ret := by
    intro d hd; simp [chainEntry] at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

def chain3Prog : Gen.Program :=
  (translateProg chainEntry [chainMid, chainLeaf]).getD emptyProg

def chainEntryFn : Gen.Function :=
  (translateFnInProg (fnNameMap chainEntry [chainMid, chainLeaf]) chainEntry).getD callerFn

theorem chain3_translate :
    translateProg chainEntry [chainMid, chainLeaf] = some chain3Prog := rfl

theorem chainEntry_translateInProg :
    translateFnInProg (fnNameMap chainEntry [chainMid, chainLeaf]) chainEntry =
      some chainEntryFn := rfl

/-- Input `-5i8` (bits `251`): `chainEntry(-5)` calls `chainMid(-5)`, which
computes `-(-5) = 5` and calls `chainLeaf(-5, 5)`, returning `Ordering::Less`
(`-1i8`, byte `255`) back through all three frames. -/
def chainNeg5Args : List Value := [.scalar ⟨251, 1⟩]
def chainNeg5S0 : MachineState :=
  initMachineStateWithCallees chainEntry chainNeg5Args [chainMid, chainLeaf]
def chainNeg5MInit : Mach :=
  multiMachineWithCtx ctxChainEntry chain3Prog 3 chainEntry chainEntryFn
    chainNeg5S0.frame.locals chainEntryFn.start

theorem chainNeg5_anneal_ret :
    ReachesRet (mirCallTreeWithCallees chainEntry chainNeg5Args [chainMid, chainLeaf]) []
      (.normal (.scalar ⟨255, 1⟩,
        { chainNeg5S0.memory with activeCallee := some chainEntry })) :=
  runA_sound chainEntry 25 _ _ _ rfl

theorem chainNeg5_noUB :
    MirNoUBTree (mirCallTreeWithCallees chainEntry chainNeg5Args [chainMid, chainLeaf]) :=
  runA_noUB chainEntry 25 _ _ _ rfl

theorem chainNeg5_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n chainNeg5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 255 } ∧
      m'.threads = [thread1 ctxChainEntry
        [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret chain3_inFragment chain3_translate
      chainEntry_translateInProg ctxChainEntry ctxChainEntry_ok chainNeg5Args (by decide)
      chainNeg5MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      chainNeg5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [chainEntry] at hd; subst hd
  simp [retPtr, ctxChainEntry, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxChainEntry, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- At step `7`, all three translated functions (`chainEntryFn`, `chainMidFn`,
and `chainLeafFn`) are live on the MiniRust call stack above `callerFrameI8`
(stack depth `4`). -/
theorem chainNeg5_depth4_step7 :
    (Interp.steps 7 chainNeg5MInit).toOption.map (fun m => m.threads.map (·.stack.length)) =
      some [4] := by
  decide +kernel

theorem chainNeg5_minirust_direct :
    (Interp.steps 11 chainNeg5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 255 }, [1]) := by
  decide +kernel

/-! ### Multi-frame UB propagation (call-argument UB and callee-body UB) -/

def idU32Callee : CapturedMir where
  defPath := "witness::id_u32_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller passing an uninitialized local `copy _1` as a call argument to
`idU32Callee`: both semantics raise UB during argument evaluation before
entering `idU32Callee`. -/
def callArgUbCaller : CapturedMir where
  defPath := "witness::call_arg_ub_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 1)],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem callArgUb_inFragment :
    progInFragment callArgUbCaller [idU32Callee] = true := by decide

def ctxCallArgUb : Ctx :=
  ctxWithFns callerFrame retAlloc 2 [128]

theorem ctxCallArgUb_ok : CtxOk callArgUbCaller ctxCallArgUb where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [callArgUbCaller] at hd; subst hd; decide
    | _ + 1, hi, _ => simp [callArgUbCaller] at hi
  ret := by
    intro d hd; simp [callArgUbCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def callArgUbProg : Gen.Program :=
  (translateProg callArgUbCaller [idU32Callee]).getD emptyProg

def callArgUbCallerFn : Gen.Function :=
  (translateFnInProg (fnNameMap callArgUbCaller [idU32Callee]) callArgUbCaller).getD callerFn

theorem callArgUb_translate :
    translateProg callArgUbCaller [idU32Callee] = some callArgUbProg := rfl

theorem callArgUbCaller_translateInProg :
    translateFnInProg (fnNameMap callArgUbCaller [idU32Callee]) callArgUbCaller =
      some callArgUbCallerFn := rfl

def callArgUbS0 : MachineState :=
  initMachineStateWithCallees callArgUbCaller [] [idU32Callee]
def callArgUbMInit : Mach :=
  multiMachineWithCtx ctxCallArgUb callArgUbProg 2 callArgUbCaller callArgUbCallerFn
    callArgUbS0.frame.locals callArgUbCallerFn.start

theorem callArgUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr u ∧ FaultNow u :=
  faultsA_sound callArgUbCaller 5 _ (by decide)

theorem callArgUb_minirust_ub :
    ∃ (n : Nat) (msg : String), Interp.steps n callArgUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := callArgUb_anneal_ub
  exact mirCallWithCallees_ub callArgUb_inFragment callArgUb_translate
    callArgUbCaller_translateInProg ctxCallArgUb ctxCallArgUb_ok [] (by decide)
    callArgUbMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf

theorem callArgUb_minirust_direct :
    Interp.steps 3 callArgUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

theorem callArgUb_converse_error :
    (∃ msg,
      Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr u ∧
        FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 3 ∧ Interp.steps k callArgUbMInit = .ok mRet ∧
      ReturnRel callArgUbCaller ctxCallArgUb s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr
        (.normal (v, mem))) :=
  mirCallWithCallees_steps_error callArgUb_inFragment callArgUb_translate
    callArgUbCaller_translateInProg ctxCallArgUb ctxCallArgUb_ok [] (by decide)
    callArgUbMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callArgUb_minirust_direct

theorem callArgUb_outcome :
    (∃ d s' m0 m' tr, Interp.steps (initLen callArgUbCaller + 1) callArgUbMInit = .ok m0 ∧
      Interp.steps (initLen callArgUbCaller + 1 + d) callArgUbMInit = .ok m' ∧
      MultiStateRel callArgUbCaller [idU32Callee] callArgUbProg ctxCallArgUb s' m' ∧
      Reaches (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr
        (mirTree callArgUbCaller s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen callArgUbCaller + 1 ∧
      Interp.steps k callArgUbMInit = .ok mRet ∧
      ReturnRel callArgUbCaller ctxCallArgUb s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr
        (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen callArgUbCaller + 1) callArgUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr u ∧
        FaultNow u) :=
  mirCallWithCallees_outcome callArgUb_inFragment callArgUb_translate
    callArgUbCaller_translateInProg ctxCallArgUb ctxCallArgUb_ok [] (by decide)
    callArgUbMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl 1

/-- Callee faulting with division-by-zero inside a pushed stack frame. -/
def divTenI8Callee : CapturedMir where
  defPath := "witness::div_ten_i8_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .div (constI8 10) (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

def calleeDivZeroCaller : CapturedMir where
  defPath := "witness::callee_div_zero_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::div_ten_i8_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem calleeDivZero_inFragment :
    progInFragment calleeDivZeroCaller [divTenI8Callee] = true := by decide

def ctxCalleeDivZero : Ctx :=
  ctxWithFns callerFrameI8 retAllocI8 2 [128, 256]

theorem ctxCalleeDivZero_ok : CtxOk calleeDivZeroCaller ctxCalleeDivZero where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [calleeDivZeroCaller] at hd; subst hd; decide
    | 1, _, hd => simp [calleeDivZeroCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [calleeDivZeroCaller] at hi
  ret := by
    intro d hd; simp [calleeDivZeroCaller] at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

def calleeDivZeroProg : Gen.Program :=
  (translateProg calleeDivZeroCaller [divTenI8Callee]).getD emptyProg

def calleeDivZeroCallerFn : Gen.Function :=
  (translateFnInProg (fnNameMap calleeDivZeroCaller [divTenI8Callee])
    calleeDivZeroCaller).getD callerFn

theorem calleeDivZero_translate :
    translateProg calleeDivZeroCaller [divTenI8Callee] = some calleeDivZeroProg := rfl

theorem calleeDivZeroCaller_translateInProg :
    translateFnInProg (fnNameMap calleeDivZeroCaller [divTenI8Callee]) calleeDivZeroCaller =
      some calleeDivZeroCallerFn := rfl

def calleeDivZeroArgs : List Value := [.scalar ⟨0, 1⟩]
def calleeDivZeroS0 : MachineState :=
  initMachineStateWithCallees calleeDivZeroCaller calleeDivZeroArgs [divTenI8Callee]
def calleeDivZeroMInit : Mach :=
  multiMachineWithCtx ctxCalleeDivZero calleeDivZeroProg 2 calleeDivZeroCaller
    calleeDivZeroCallerFn calleeDivZeroS0.frame.locals calleeDivZeroCallerFn.start

theorem calleeDivZero_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees calleeDivZeroCaller calleeDivZeroArgs [divTenI8Callee]) tr u ∧
      FaultNow u :=
  faultsA_sound calleeDivZeroCaller 10 _ (by decide)

theorem calleeDivZero_minirust_ub :
    ∃ (n : Nat) (msg : String), Interp.steps n calleeDivZeroMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := calleeDivZero_anneal_ub
  exact mirCallWithCallees_ub calleeDivZero_inFragment calleeDivZero_translate
    calleeDivZeroCaller_translateInProg ctxCalleeDivZero ctxCalleeDivZero_ok calleeDivZeroArgs
    (by decide) calleeDivZeroMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf

theorem calleeDivZero_minirust_direct :
    Interp.steps 4 calleeDivZeroMInit = .error (.ub "division by zero") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

theorem calleeDivZero_converse_error :
    (∃ msg, Stop.ub "division by zero" = .ub msg ∧
      ∃ tr u, Reaches
        (mirCallTreeWithCallees calleeDivZeroCaller calleeDivZeroArgs [divTenI8Callee]) tr u ∧
        FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 4 ∧ Interp.steps k calleeDivZeroMInit = .ok mRet ∧
      ReturnRel calleeDivZeroCaller ctxCalleeDivZero s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees calleeDivZeroCaller calleeDivZeroArgs [divTenI8Callee])
        tr (.normal (v, mem))) :=
  mirCallWithCallees_steps_error calleeDivZero_inFragment calleeDivZero_translate
    calleeDivZeroCaller_translateInProg ctxCalleeDivZero ctxCalleeDivZero_ok calleeDivZeroArgs
    (by decide) calleeDivZeroMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    calleeDivZero_minirust_direct

/-! ### Diverging multi-function call loop (`callSpinCaller` calling `idU32Callee`) -/

/-- Diverging caller `StorageLive(_2); loop { _2 = copy _1; _1 = id_u32_callee(move _2); }`:
the static call graph `callSpinCaller -> idU32Callee` is acyclic, and each
iteration pushes and pops `idU32Callee` cleanly without unbounded stack growth. -/
def callSpinCaller : CapturedMir where
  defPath := "witness::call_spin_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2)],
      terminator := mkTerm (.goto 1),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2) (.use (.copy (local_ 1))))],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.move (local_ 2)] (local_ 1) (some 1) .continue_),
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callSpin_inFragment :
    progInFragment callSpinCaller [idU32Callee] = true := by decide

def ctxCallSpin : Ctx :=
  ctxWithFns callerFrame retAlloc 2 [128, 256]

theorem ctxCallSpin_ok : CtxOk callSpinCaller ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [callSpinCaller] at hd; subst hd; decide
    | 1, _, hd => simp [callSpinCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [callSpinCaller] at hi
  ret := by
    intro d hd; simp [callSpinCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def callSpinProg : Gen.Program :=
  (translateProg callSpinCaller [idU32Callee]).getD emptyProg

def callSpinCallerFn : Gen.Function :=
  (translateFnInProg (fnNameMap callSpinCaller [idU32Callee]) callSpinCaller).getD callerFn

theorem callSpin_translate :
    translateProg callSpinCaller [idU32Callee] = some callSpinProg := rfl

theorem callSpinCaller_translateInProg :
    translateFnInProg (fnNameMap callSpinCaller [idU32Callee]) callSpinCaller =
      some callSpinCallerFn := rfl

def callSpinArgs : List Value := [.scalar ⟨0, 4⟩]
def callSpinS0 : MachineState :=
  initMachineStateWithCallees callSpinCaller callSpinArgs [idU32Callee]

private def nextSpinState (s : MachineState) : MachineState :=
  match stepMirFn callSpinCaller s with
  | .tau (.running s') => s'
  | _ => s

private def callSpinS1 : MachineState := nextSpinState callSpinS0
private def callSpinS2 : MachineState := nextSpinState callSpinS1
private def callSpinS3 : MachineState := nextSpinState callSpinS2
private def callSpinS4 : MachineState := nextSpinState callSpinS3
private def callSpinS5 : MachineState := nextSpinState callSpinS4
private def callSpinS6 : MachineState := nextSpinState callSpinS5
private def callSpinS7 : MachineState := nextSpinState callSpinS6

/-- Eight-state silent-step invariant for `callSpinCaller`:
`S0 -> S1 -> S2 -> S3` on entry (`activeCallee = none`), entering the 4-state
call/return cycle `S4 -> S5 -> S6 -> S7 -> S4`. -/
def CallSpinInv (s : MachineState) : Prop :=
  s = callSpinS0 ∨ s = callSpinS1 ∨ s = callSpinS2 ∨ s = callSpinS3 ∨
  s = callSpinS4 ∨ s = callSpinS5 ∨ s = callSpinS6 ∨ s = callSpinS7

private theorem callSpin_step (s : MachineState) (h : CallSpinInv s) :
    ∃ s', stepMirFn callSpinCaller s = .tau (.running s') ∧ CallSpinInv s' := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨callSpinS1, rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨callSpinS2, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨callSpinS3, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · exact ⟨callSpinS4, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  · exact ⟨callSpinS5, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  · exact ⟨callSpinS6, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
  · exact ⟨callSpinS7, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))⟩
  · exact ⟨callSpinS4, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩

def callSpinMInit : Mach :=
  multiMachineWithCtx ctxCallSpin callSpinProg 2 callSpinCaller callSpinCallerFn
    callSpinS0.frame.locals callSpinCallerFn.start

theorem callSpin_noUB :
    MirNoUBTree (mirCallTreeWithCallees callSpinCaller callSpinArgs [idU32Callee]) :=
  treeSafe_of_tau_inv callSpin_step (Or.inl rfl)

theorem callSpin_noRet (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet (mirCallTreeWithCallees callSpinCaller callSpinArgs [idU32Callee]) tr o :=
  noRet_of_tau_inv callSpin_step (Or.inl rfl) tr o

theorem callSpin_minirust_diverges (n : Nat) :
    ∃ m', Interp.steps n callSpinMInit = .ok m' :=
  mirCallWithCallees_diverges_steps_ok callSpin_inFragment callSpin_translate
    callSpinCaller_translateInProg ctxCallSpin ctxCallSpin_ok callSpinArgs (by decide)
    callSpinMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callSpin_noUB callSpin_noRet n

theorem callSpin_minirust_diverges_rel (n : Nat) :
    ∃ d s' m0 m' tr, Interp.steps (initLen callSpinCaller + n) callSpinMInit = .ok m0 ∧
      Interp.steps (initLen callSpinCaller + n + d) callSpinMInit = .ok m' ∧
      MultiStateRel callSpinCaller [idU32Callee] callSpinProg ctxCallSpin s' m' ∧
      Reaches (mirCallTreeWithCallees callSpinCaller callSpinArgs [idU32Callee]) tr
        (mirTree callSpinCaller s') :=
  mirCallWithCallees_diverges_rel callSpin_inFragment callSpin_translate
    callSpinCaller_translateInProg ctxCallSpin ctxCallSpin_ok callSpinArgs (by decide)
    callSpinMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callSpin_noUB callSpin_noRet n

/-! ### Soundness-boundary counterexamples (`progInFragment = false`) -/

/-- Counterexample 1 (`_1 = idU32Callee(copy _1)`): return place `_1` aliases
argument `copy _1`. Anneal evaluates `copy _1` before writing `_1` on return and
succeeds, whereas MiniRust's `Terminator::Call` runs
`prepare_for_inplace_passing(_1)` (writing `Uninit`) BEFORE `eval_argument`
loads `_1`, faulting with UB! `callTerminatorOk` rightly rejects this. -/
def callDestArgAlias : CapturedMir where
  defPath := "witness::call_dest_arg_alias"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (local_ 1)] (local_ 1) (some 1) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callDestArgAlias_movesOk : movesOk callDestArgAlias = false := by decide

theorem callDestArgAlias_rejected :
    progInFragment callDestArgAlias [idU32Callee] = false := by decide

def callDestArgAliasProg : Gen.Program :=
  (translateProg callDestArgAlias [idU32Callee]).getD emptyProg

def callDestArgAliasFn : Gen.Function :=
  (translateFnInProg (fnNameMap callDestArgAlias [idU32Callee]) callDestArgAlias).getD callerFn

theorem callDestArgAlias_translate :
    translateProg callDestArgAlias [idU32Callee] = some callDestArgAliasProg := rfl

def callDestArgAliasS0 : MachineState :=
  initMachineStateWithCallees callDestArgAlias [.scalar ⟨7, 4⟩] [idU32Callee]
def callDestArgAliasMInit : Mach :=
  multiMachineWithCtx ctxCallerMain callDestArgAliasProg 2 callDestArgAlias callDestArgAliasFn
    callDestArgAliasS0.frame.locals callDestArgAliasFn.start

theorem callDestArgAlias_anneal_ret :
    ReachesRet (mirCallTreeWithCallees callDestArgAlias [.scalar ⟨7, 4⟩] [idU32Callee]) []
      (.normal (.scalar ⟨7, 4⟩,
        { callDestArgAliasS0.memory with activeCallee := some callDestArgAlias })) :=
  runA_sound callDestArgAlias 10 _ _ _ rfl

theorem callDestArgAlias_minirust_ub :
    Interp.steps 2 callDestArgAliasMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

/-- Counterexample 2 (`_2 = idU32Callee(move (_1.0)); _0 = copy (_1.0)`):
projected `move (_1.0)` in a call argument leaves `_1` intact in Anneal's
`evalOperand` (which only deinitializes root moves), whereas MiniRust translates
`Operand::Move(_1.0)` to `ArgumentExpr::InPlace (.Field (.Local _1) 0)` and
deinitializes `_1.0`, faulting when `bb1` reads `copy (_1.0)`! `callArgOk`
rightly restricts `Operand::Move` call arguments to root locals. -/
def callProjMoveReuse : CapturedMir where
  defPath := "witness::call_proj_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32BoolTupleDecl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2)],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.move (field0U32 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (field0U32 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callProjMoveReuse_rejected :
    progInFragment callProjMoveReuse [idU32Callee] = false := by decide

def callProjMoveReuseProg : Gen.Program :=
  (translateProg callProjMoveReuse [idU32Callee]).getD emptyProg

def callProjMoveReuseFn : Gen.Function :=
  (translateFnInProg (fnNameMap callProjMoveReuse [idU32Callee]) callProjMoveReuse).getD callerFn

theorem callProjMoveReuse_translate :
    translateProg callProjMoveReuse [idU32Callee] = some callProjMoveReuseProg := rfl

def callProjMoveReuseArgs : List Value := [.aggregate 0 [.scalar ⟨9, 4⟩, .scalar ⟨1, 1⟩]]
def callProjMoveReuseS0 : MachineState :=
  initMachineStateWithCallees callProjMoveReuse callProjMoveReuseArgs [idU32Callee]
def callProjMoveReuseMInit : Mach :=
  multiMachineWithCtx ctxCallerMain callProjMoveReuseProg 2 callProjMoveReuse
    callProjMoveReuseFn callProjMoveReuseS0.frame.locals callProjMoveReuseFn.start

theorem callProjMoveReuse_anneal_ret :
    ReachesRet
      (mirCallTreeWithCallees callProjMoveReuse callProjMoveReuseArgs [idU32Callee]) []
      (.normal (.scalar ⟨9, 4⟩,
        { callProjMoveReuseS0.memory with activeCallee := some callProjMoveReuse })) :=
  runA_sound callProjMoveReuse 10 _ _ _ rfl

theorem callProjMoveReuse_minirust_ub :
    Interp.steps 7 callProjMoveReuseMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

/-- Post-call root-`move` reuse (`StorageLive(_2); _2 = idU32Callee(move _1);
_0 = copy _1`): because `ArgumentExpr::InPlace` writes `Uninit` to `_1` in
MiniRust just as `evalOperand` sets `_1` to `.uninit` in Anneal (`_1` is not
stale!), `callMoveReuse` is IN `progInFragment`, and BOTH forward UB transfer
(`mirCallWithCallees_ub`) and converse error soundness
(`mirCallWithCallees_steps_error`) apply on `bb1`'s `copy _1`. -/
def callMoveReuse : CapturedMir where
  defPath := "witness::call_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2)],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.move (local_ 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callMoveReuse_inFragment :
    progInFragment callMoveReuse [idU32Callee] = true := by decide

theorem callMoveReuse_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees callMoveReuse [.scalar ⟨7, 4⟩] [idU32Callee]) tr u ∧ FaultNow u :=
  faultsA_sound callMoveReuse 10 _ (by decide)

def callMoveReuseProg : Gen.Program :=
  (translateProg callMoveReuse [idU32Callee]).getD emptyProg
def callMoveReuseFn : Gen.Function :=
  (translateFnInProg (fnNameMap callMoveReuse [idU32Callee]) callMoveReuse).getD callerFn
theorem callMoveReuse_translate :
    translateProg callMoveReuse [idU32Callee] = some callMoveReuseProg := rfl
theorem callMoveReuse_translateInProg :
    translateFnInProg (fnNameMap callMoveReuse [idU32Callee]) callMoveReuse =
      some callMoveReuseFn := rfl
def callMoveReuseMInit : Mach :=
  multiMachineWithCtx ctxCallSpin callMoveReuseProg 2 callMoveReuse callMoveReuseFn
    (initMachineStateWithCallees callMoveReuse [.scalar ⟨7, 4⟩] [idU32Callee]).frame.locals
    callMoveReuseFn.start

theorem ctxCallMoveReuse_ok : CtxOk callMoveReuse ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [callMoveReuse] at hd; subst hd; decide
    | 1, _, hd => simp [callMoveReuse] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [callMoveReuse] at hi
  ret := by
    intro d hd; simp [callMoveReuse] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem callMoveReuse_minirust_ub :
    ∃ (n : Nat) (msg : String), Interp.steps n callMoveReuseMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := callMoveReuse_anneal_ub
  exact mirCallWithCallees_ub callMoveReuse_inFragment callMoveReuse_translate
    callMoveReuse_translateInProg ctxCallSpin ctxCallMoveReuse_ok
    [.scalar ⟨7, 4⟩] (by decide) callMoveReuseMInit
    (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf

theorem callMoveReuse_minirust_direct :
    Interp.steps 7 callMoveReuseMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

theorem callMoveReuse_converse_error :
    (∃ msg,
      Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u,
        Reaches (mirCallTreeWithCallees callMoveReuse [.scalar ⟨7, 4⟩] [idU32Callee]) tr u ∧
          FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 7 ∧ Interp.steps k callMoveReuseMInit = .ok mRet ∧
      ReturnRel callMoveReuse ctxCallSpin s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callMoveReuse [.scalar ⟨7, 4⟩] [idU32Callee]) tr
        (.normal (v, mem))) :=
  mirCallWithCallees_steps_error callMoveReuse_inFragment callMoveReuse_translate
    callMoveReuse_translateInProg ctxCallSpin ctxCallMoveReuse_ok
    [.scalar ⟨7, 4⟩] (by decide) callMoveReuseMInit
    (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callMoveReuse_minirust_direct

/-- Root-destination call re-initialization (`StorageLive(_2); _2 = move _1;
_1 = idU32Callee(copy _2); _0 = copy _1; StorageDead(_2); Return`): `_1` is
moved out by `_2 = move _1` (entering `mo`), then completely overwritten by the
root destination of `_1 = idU32Callee(copy _2)` (`termMoved` clears `_1` from
`mo`, and `termReadsOk` allows `_1 ∈ mo` on root destinations `⟨dst, []⟩`). -/
def moveReinitByCall : CapturedMir where
  defPath := "witness::move_reinit_by_call"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (.move (local_ 1))))],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (local_ 2)] (local_ 1) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem moveReinitByCall_inFragment :
    progInFragment moveReinitByCall [idU32Callee] = true := by decide

def moveReinitByCallProg : Gen.Program :=
  (translateProg moveReinitByCall [idU32Callee]).getD emptyProg
def moveReinitByCallFn : Gen.Function :=
  (translateFnInProg (fnNameMap moveReinitByCall [idU32Callee]) moveReinitByCall).getD callerFn
theorem moveReinitByCall_translate :
    translateProg moveReinitByCall [idU32Callee] = some moveReinitByCallProg := rfl
theorem moveReinitByCall_translateInProg :
    translateFnInProg (fnNameMap moveReinitByCall [idU32Callee]) moveReinitByCall =
      some moveReinitByCallFn := rfl

def moveReinitByCallS0 : MachineState :=
  initMachineStateWithCallees moveReinitByCall [.scalar ⟨55, 4⟩] [idU32Callee]
def moveReinitByCallMInit : Mach :=
  multiMachineWithCtx ctxCallSpin moveReinitByCallProg 2 moveReinitByCall moveReinitByCallFn
    moveReinitByCallS0.frame.locals moveReinitByCallFn.start

theorem ctxMoveReinitByCall_ok : CtxOk moveReinitByCall ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [moveReinitByCall] at hd; subst hd; decide
    | 1, _, hd => simp [moveReinitByCall] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [moveReinitByCall] at hi
  ret := by
    intro d hd; simp [moveReinitByCall] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem moveReinitByCall_anneal_ret :
    ReachesRet (mirCallTreeWithCallees moveReinitByCall [.scalar ⟨55, 4⟩] [idU32Callee]) []
      (.normal (.scalar ⟨55, 4⟩,
        { moveReinitByCallS0.memory with activeCallee := some moveReinitByCall })) :=
  runA_sound moveReinitByCall 20 _ _ _ rfl

theorem moveReinitByCall_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n moveReinitByCallMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 55 } ∧
      m'.threads = [thread1 ctxCallSpin
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret moveReinitByCall_inFragment moveReinitByCall_translate
      moveReinitByCall_translateInProg ctxCallSpin ctxMoveReinitByCall_ok
      [.scalar ⟨55, 4⟩] (by decide) moveReinitByCallMInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      moveReinitByCall_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [moveReinitByCall] at hd; subst hd
  simp [retPtr, ctxCallSpin, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallSpin, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem moveReinitByCall_minirust_direct :
    (Interp.steps 10 moveReinitByCallMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 55 }, [1]) := by
  decide +kernel

/-- Branch-correlated `Call` `move` across a CFG join:
```rust
fn cond_call_move_join(flag: u32, x: u32) -> u32 {
    let y = if flag != 0 { id_u32_callee(move x) } else { 0 };
    if flag != 0 { y } else { x }
}
```
On `bb1` (`flag != 0`), `move _2` is lowered via `ArgumentExpr::InPlace` (writing
`Uninit` in MiniRust too, so `_2` is not stale!), allowing `bb5` (`flag == 0`)
after the join block `bb3` to read `copy _2` cleanly in `progInFragment`. -/
def condCallMoveJoin : CapturedMir where
  defPath := "witness::cond_call_move_join"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 3)],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.move (local_ 2)] (local_ 3) (some 3) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 3) (.use (constU32 0)))],
      terminator := mkTerm (.goto 3), isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 5)], otherwise := 4 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 2)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem condCallMoveJoin_inFragment :
    progInFragment condCallMoveJoin [idU32Callee] = true := by decide

def condCallMoveJoinProg : Gen.Program :=
  (translateProg condCallMoveJoin [idU32Callee]).getD emptyProg
def condCallMoveJoinFn : Gen.Function :=
  (translateFnInProg (fnNameMap condCallMoveJoin [idU32Callee]) condCallMoveJoin).getD callerFn
theorem condCallMoveJoin_translate :
    translateProg condCallMoveJoin [idU32Callee] = some condCallMoveJoinProg := rfl
theorem condCallMoveJoin_translateInProg :
    translateFnInProg (fnNameMap condCallMoveJoin [idU32Callee]) condCallMoveJoin =
      some condCallMoveJoinFn := rfl

theorem ctxCondCallMoveJoin_ok : CtxOk condCallMoveJoin ctxCallerMain where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [condCallMoveJoin] at hd; subst hd; decide
    | 1, _, hd => simp [condCallMoveJoin] at hd; subst hd; decide
    | 2, _, hd => simp [condCallMoveJoin] at hd; subst hd; decide
    | _ + 3, hi, _ => simp [condCallMoveJoin] at hi
  ret := by
    intro d hd; simp [condCallMoveJoin] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def condCallMoveJoin1Args : List Value := [.scalar ⟨1, 4⟩, .scalar ⟨42, 4⟩]
def condCallMoveJoin1S0 : MachineState :=
  initMachineStateWithCallees condCallMoveJoin condCallMoveJoin1Args [idU32Callee]
def condCallMoveJoin1MInit : Mach :=
  multiMachineWithCtx ctxCallerMain condCallMoveJoinProg 2 condCallMoveJoin condCallMoveJoinFn
    condCallMoveJoin1S0.frame.locals condCallMoveJoinFn.start

theorem condCallMoveJoin1_anneal_ret :
    ReachesRet (mirCallTreeWithCallees condCallMoveJoin condCallMoveJoin1Args [idU32Callee])
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩,
        ⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨42, 4⟩,
        { condCallMoveJoin1S0.memory with activeCallee := some condCallMoveJoin })) :=
  runA_sound condCallMoveJoin 25 _ _ _ rfl

theorem condCallMoveJoin1_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n condCallMoveJoin1MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads = [thread1 ctxCallerMain
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret condCallMoveJoin_inFragment condCallMoveJoin_translate
      condCallMoveJoin_translateInProg ctxCallerMain ctxCondCallMoveJoin_ok
      condCallMoveJoin1Args (by decide) condCallMoveJoin1MInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      condCallMoveJoin1_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [condCallMoveJoin] at hd; subst hd
  simp [retPtr, ctxCallerMain, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallerMain, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

def condCallMoveJoin0Args : List Value := [.scalar ⟨0, 4⟩, .scalar ⟨99, 4⟩]
def condCallMoveJoin0S0 : MachineState :=
  initMachineStateWithCallees condCallMoveJoin condCallMoveJoin0Args [idU32Callee]
def condCallMoveJoin0MInit : Mach :=
  multiMachineWithCtx ctxCallerMain condCallMoveJoinProg 2 condCallMoveJoin condCallMoveJoinFn
    condCallMoveJoin0S0.frame.locals condCallMoveJoinFn.start

theorem condCallMoveJoin0_anneal_ret :
    ReachesRet (mirCallTreeWithCallees condCallMoveJoin condCallMoveJoin0Args [idU32Callee])
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩,
        ⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨99, 4⟩, condCallMoveJoin0S0.memory)) :=
  runA_sound condCallMoveJoin 25 _ _ _ rfl

theorem condCallMoveJoin0_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n condCallMoveJoin0MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 99 } ∧
      m'.threads = [thread1 ctxCallerMain
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret condCallMoveJoin_inFragment condCallMoveJoin_translate
      condCallMoveJoin_translateInProg ctxCallerMain ctxCondCallMoveJoin_ok
      condCallMoveJoin0Args (by decide) condCallMoveJoin0MInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      condCallMoveJoin0_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [condCallMoveJoin] at hd; subst hd
  simp [retPtr, ctxCallerMain, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallerMain, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem condCallMoveJoin_minirust_direct :
    (Interp.steps 11 condCallMoveJoin1MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (Interp.steps 9 condCallMoveJoin0MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) :=
  ⟨by decide +kernel, by decide +kernel⟩


/-- Counterexample 3 (`StorageLive(_2); _2 = move _1; _0 = idU32Callee(copy _1)`):
passing a local that was moved out in an earlier statement (leaving stale bytes
in MiniRust!) as a call argument is rejected by `termReadsOk` / `movesOk` (and
`progInFragment`). -/
def stmtMoveThenCallArg : CapturedMir where
  defPath := "witness::stmt_move_then_call_arg"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (.move (local_ 1))))],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem stmtMoveThenCallArg_movesOk : movesOk stmtMoveThenCallArg = false := by decide

theorem stmtMoveThenCallArg_rejected :
    progInFragment stmtMoveThenCallArg [idU32Callee] = false := by decide

/-- Counterexample 4: mutual recursion `recCycleA -> recCycleB -> recCycleA` is
rejected by `maxStackLocals = none` (`progInFragment = false`). -/
def recCycleA : CapturedMir where
  defPath := "witness::rec_cycle_a"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::rec_cycle_b")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

def recCycleB : CapturedMir where
  defPath := "witness::rec_cycle_b"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::rec_cycle_a")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem recCycle_maxStackLocals :
    maxStackLocals recCycleA [recCycleB, recCycleA] = none := rfl

theorem recCycle_rejected :
    progInFragment recCycleA [recCycleB, recCycleA] = false := by decide

/-! ### Ground-truth `Interp` unit checks for `MR-4.1` spec items -/

/-- `Type.layout` on `Ptr` (thin `FnPtr`, thin sized `Ref`, wide `Slice` `Ref`,
and `Raw (.VTablePointer _)`) and `Array` (`[u32; 3]`, `3 * 4 = 12` bytes, align `4`). -/
def sizedU32Pointee : Gen.PointeeInfo :=
  { layout := .Sized ⟨4⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Sized [],
    freeze := true, unpin := true }

def sliceU32Pointee : Gen.PointeeInfo :=
  { layout := .Slice ⟨4⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Slice [],
    freeze := true, unpin := true }

theorem layout_ptr_and_array_mr41 :
    Type.layout (.Ptr .FnPtr) = .ok (.Sized ⟨8⟩ ⟨8⟩) ∧
    Type.layout (.Ptr (.Ref .Immutable sizedU32Pointee)) = .ok (.Sized ⟨8⟩ ⟨8⟩) ∧
    Type.layout (.Ptr (.Ref .Immutable sliceU32Pointee)) = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    Type.layout (.Ptr (.Raw (.VTablePointer ⟨⟨0⟩⟩))) = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    Type.layout (.Array (.Int u32) 3) = .ok (.Sized ⟨12⟩ ⟨4⟩) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `evalConstant` on `FnPointer`, `GlobalPointer` (with offset),
`VTablePointer`, and `PointerWithoutProvenance`, plus `fnFromPtr` on valid thin
function pointers, wide pointers (UB), unmapped thin pointers (UB), and
non-pointer values (UB). -/
def constTestMach : Mach :=
  { callerCallee20MInit with
    prog := { callerCalleeProg with
              globals := ⟨[(⟨⟨0⟩⟩, { bytes := [some 1, some 2], relocations := [], align := ⟨2⟩ })]⟩ },
    global_ptrs := ⟨[(⟨⟨0⟩⟩, { addr := 32, provenance := some (⟨99⟩, ()) })]⟩,
    vtable_ptrs := ⟨[(⟨⟨0⟩⟩, { addr := 48, provenance := some (⟨98⟩, ()) })]⟩ }

theorem evalConstant_and_fnFromPtr_mr41 :
    evalConstant constTestMach (.FnPointer (fnName 1)) =
      .ok (.Ptr ⟨fnPtrAt 1 1, none⟩) ∧
    evalConstant constTestMach (.GlobalPointer ⟨⟨⟨0⟩⟩, ⟨1⟩⟩) =
      .ok (.Ptr ⟨{ addr := 33, provenance := some (⟨99⟩, ()) }, none⟩) ∧
    evalConstant constTestMach (.VTablePointer ⟨⟨0⟩⟩) =
      .ok (.Ptr ⟨{ addr := 48, provenance := some (⟨98⟩, ()) }, none⟩) ∧
    evalConstant constTestMach (.PointerWithoutProvenance 4096) =
      .ok (.Ptr ⟨{ addr := 4096, provenance := none }, none⟩) ∧
    fnFromPtr constTestMach (.Ptr ⟨fnPtrAt 1 1, none⟩) = .ok calleePairFn ∧
    fnFromPtr constTestMach (.Ptr ⟨fnPtrAt 1 1, some (.ElementCount 2)⟩) =
      .error (.ub "invalid pointer for function lookup") ∧
    fnFromPtr constTestMach (.Ptr ⟨{ addr := 999, provenance := none }, none⟩) =
      .error (.ub "invalid pointer for function lookup") ∧
    fnFromPtr constTestMach (.Int 0) =
      .error (.ub "trying to look up a function based on a non-pointer value") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `checkAbiCompatibility` across `Int`, `Bool`, `Ptr`, `Tuple` (including
unsized tuple `specPanic`), `Array`, `Union`, and `Enum` (`orderingTy`
`Branch` `Discriminator`, variant mismatch, and tagger mismatch). -/
def sampleUnionA : Gen.Type :=
  .Union [(⟨0⟩, .Int u32), (⟨0⟩, .Bool)] [(⟨0⟩, ⟨4⟩)] ⟨4⟩ ⟨4⟩

def sampleUnionBadChunks : Gen.Type :=
  .Union [(⟨0⟩, .Int u32), (⟨0⟩, .Bool)] [(⟨0⟩, ⟨2⟩)] ⟨4⟩ ⟨4⟩

def orderingBadTagger : Gen.Type :=
  match orderingTy with
  | .Enum ⟨(-1, v) :: rest⟩ dTy discr sz al =>
    .Enum ⟨(-1, { v with tagger := ⟨[(⟨0⟩, (u8, 42))]⟩ }) :: rest⟩ dTy discr sz al
  | t => t

theorem checkAbiCompatibility_all_variants_mr41 :
    checkAbiCompatibility (.Int u32) (.Int u32) = .ok true ∧
    checkAbiCompatibility (.Int u32) (.Int i8) = .ok false ∧
    checkAbiCompatibility .Bool .Bool = .ok true ∧
    checkAbiCompatibility (.Ptr .FnPtr) (.Ptr (.Raw .None)) = .ok true ∧
    checkAbiCompatibility (.Ptr .FnPtr) (.Ptr (.Raw .ElementCount)) = .ok false ∧
    checkAbiCompatibility (intBoolTupleTy u32) (intBoolTupleTy u32) = .ok true ∧
    checkAbiCompatibility (intBoolTupleTy u32) (intBoolTupleTy i8) = .ok false ∧
    checkAbiCompatibility (.Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ (some (.Array (.Int u8) 0))) unitTy =
      .error (.specPanic "wf ensures all arugments are sized") ∧
    checkAbiCompatibility (.Array (.Int u32) 4) (.Array (.Int u32) 4) = .ok true ∧
    checkAbiCompatibility (.Array (.Int u32) 4) (.Array (.Int u32) 5) = .ok false ∧
    checkAbiCompatibility sampleUnionA sampleUnionA = .ok true ∧
    checkAbiCompatibility sampleUnionA sampleUnionBadChunks = .ok false ∧
    checkAbiCompatibility orderingTy orderingTy = .ok true ∧
    checkAbiCompatibility orderingTy orderingBadTagger = .ok false ∧
    checkAbiCompatibility orderingTy .Bool = .ok false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `createFrame` ABI-violation UB paths (calling convention mismatch, return
type mismatch, argument count mismatch, and argument type mismatch). -/
theorem createFrame_ub_mr41 :
    createFrame callerCallee20MInit calleePairFn
      (.BackToCaller (some (bbName 1)) none retPtr) .C (.Int u32) [] =
      .error (.ub "call ABI violation: calling conventions are not the same") ∧
    createFrame callerCallee20MInit calleePairFn
      (.BackToCaller (some (bbName 1)) none retPtr) .Rust .Bool [] =
      .error (.ub "call ABI violation: return types are not compatible") ∧
    createFrame callerCallee20MInit calleePairFn
      (.BackToCaller (some (bbName 1)) none retPtr) .Rust (.Int u32) [] =
      .error (.ub "call ABI violation: number of arguments does not agree") ∧
    createFrame callerCallee20MInit calleePairFn
      (.BackToCaller (some (bbName 1)) none retPtr) .Rust (.Int u32)
      [(.Bool true, .Bool), (.Bool false, .Bool)] =
      .error (.ub "call ABI violation: argument types are not compatible") :=
  ⟨eq_error_ub_of_ubMsg? (by decide +kernel),
   eq_error_ub_of_ubMsg? (by decide +kernel),
   eq_error_ub_of_ubMsg? (by decide +kernel),
   eq_error_ub_of_ubMsg? (by decide +kernel)⟩

def retNoNextBlockMach : Mach :=
  let m := multiMachineWithCtx
    { ctxWithFns callerFrame retAlloc 1 [128, 256] with nextBlock := bbName 7 }
    emptyProg 1 idU32Callee
    ((translateFn idU32Callee).getD callerFn)
    [.init (.scalar ⟨11, 4⟩), .init (.scalar ⟨11, 4⟩)]
    (bbName 0)
  let t0 := m.threads[0]?.getD (thread1 ctx0 [])
  let fTop := (t0.stack.getLast?.getD callerFrame)
  { m with threads := [{ t0 with stack := [callerFrame,
      { fTop with next_stmt := 1, stack_pop_action := .BackToCaller none none retPtr }] }] }

def retBottomOfStackMach : Mach :=
  let m := multiMachineWithCtx
    (ctxWithFns callerFrame retAlloc 1 [128, 256])
    emptyProg 1 idU32Callee
    ((translateFn idU32Callee).getD callerFn)
    [.init (.scalar ⟨11, 4⟩), .init (.scalar ⟨11, 4⟩)]
    (bbName 0)
  let t0 := m.threads[0]?.getD (thread1 ctx0 [])
  let fTop := (t0.stack.getLast?.getD callerFrame)
  { m with threads := [{ t0 with stack := [
      { fTop with next_stmt := 1, stack_pop_action := .BottomOfStack }] }] }

/-- `evalReturn` UB paths (`next_block = none` and `BottomOfStack` on thread `0`). -/
theorem evalReturn_missingNextBlock_and_bottomOfStack_ub :
    evalReturn retNoNextBlockMach =
      .error (.ub "return from a function where caller did not specify next block") ∧
    evalReturn retBottomOfStackMach =
      .error (.ub "the start function must not return") :=
  ⟨eq_error_ub_of_ubMsg? (by decide +kernel),
   eq_error_ub_of_ubMsg? (by decide +kernel)⟩

/-! ### Pass `B3` hardening witnesses: `CallConv.c` (`extern "C"`), unsupported-ABI rejection,
dead / uninitialized-tuple return-place counterexamples, and diamond call DAG -/

/-- `extern "C"` single-parameter `u32 -> u32` ABI (`Layout.CallConv.c`). -/
def fnAbiC1 : FnAbi :=
  { (fnAbi 1) with conv := .c }

/-- `extern "C"` callee `cAbiCallee(x: u32) -> u32 { x + 10 }`: exercises
`translateCallConv .c = some .C` in both `translateFn` and `translateFnInProg`. -/
def cAbiCallee : CapturedMir where
  defPath := "witness::c_abi_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 1)) (constU32 10)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiC1
  layouts := emptyLayoutTable
  allocations := []

/-- Rust-ABI caller invoking `extern "C"` `cAbiCallee` (`CallingConvention.C` on
the `Terminator::Call` edge while the caller itself has `CallingConvention.Rust`). -/
def cAbiCaller : CapturedMir where
  defPath := "witness::c_abi_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::c_abi_callee")
        [.move (local_ 1)] (local_ 0) (some 1) .unreachable),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem cAbiCallee_conv :
    (translateFn cAbiCallee).map (·.calling_convention) = some .C ∧
    (translateFnInProg (fnNameMap cAbiCaller [cAbiCallee]) cAbiCallee).map
      (·.calling_convention) = some .C ∧
    (translateFnInProg (fnNameMap cAbiCaller [cAbiCallee]) cAbiCaller).map
      (·.calling_convention) = some .Rust :=
  ⟨rfl, rfl, rfl⟩

theorem cAbi_inFragment :
    progInFragment cAbiCaller [cAbiCallee] = true := by decide

def cAbiProg : Gen.Program :=
  (translateProg cAbiCaller [cAbiCallee]).getD emptyProg
def cAbiCallerFn : Gen.Function :=
  (translateFnInProg (fnNameMap cAbiCaller [cAbiCallee]) cAbiCaller).getD callerFn
theorem cAbi_translate :
    translateProg cAbiCaller [cAbiCallee] = some cAbiProg := rfl
theorem cAbiCaller_translateInProg :
    translateFnInProg (fnNameMap cAbiCaller [cAbiCallee]) cAbiCaller = some cAbiCallerFn := rfl

theorem ctxCAbiCaller_ok : CtxOk cAbiCaller ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [cAbiCaller] at hd; subst hd; decide
    | 1, _, hd => simp [cAbiCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [cAbiCaller] at hi
  ret := by
    intro d hd; simp [cAbiCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def cAbi32Args : List Value := [.scalar ⟨32, 4⟩]
def cAbi32S0 : MachineState :=
  initMachineStateWithCallees cAbiCaller cAbi32Args [cAbiCallee]
def cAbi32MInit : Mach :=
  multiMachineWithCtx ctxCallSpin cAbiProg 2 cAbiCaller cAbiCallerFn
    cAbi32S0.frame.locals cAbiCallerFn.start

theorem cAbi32_anneal_ret :
    ReachesRet (mirCallTreeWithCallees cAbiCaller cAbi32Args [cAbiCallee]) []
      (.normal (.scalar ⟨42, 4⟩,
        { cAbi32S0.memory with activeCallee := some cAbiCaller })) :=
  runA_sound cAbiCaller 20 _ _ _ rfl

theorem cAbi32_noUB :
    MirNoUBTree (mirCallTreeWithCallees cAbiCaller cAbi32Args [cAbiCallee]) :=
  runA_noUB cAbiCaller 20 _ _ _ rfl

theorem cAbi32_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cAbi32MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads = [thread1 ctxCallSpin
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret cAbi_inFragment cAbi_translate
      cAbiCaller_translateInProg ctxCallSpin ctxCAbiCaller_ok
      cAbi32Args (by decide) cAbi32MInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      cAbi32_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cAbiCaller] at hd; subst hd
  simp [retPtr, ctxCallSpin, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallSpin, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem cAbi32_minirust_direct :
    (Interp.steps 6 cAbi32MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) := by
  decide +kernel

/-- Rejection of unsupported calling conventions (`Layout.CallConv.rustIntrinsic`
and `Layout.CallConv.other "sysv64"`): `translateCallConv = none`, so both
single-function (`translateFn`, `inFragment`) and multi-function
(`callTerminatorOk`, `translateProg`, `progInFragment`) checks reject them. -/
def badCallConvCallee : CapturedMir :=
  { idU32Callee with
    defPath := "witness::bad_call_conv_callee",
    fnAbi := { (fnAbi 1) with conv := .rustIntrinsic } }

def badCallConvSysvBody : CapturedMir :=
  { idU32Callee with
    defPath := "witness::bad_sysv_body",
    fnAbi := { (fnAbi 1) with conv := .other "sysv64" } }

def badCallConvCaller : CapturedMir where
  defPath := "witness::bad_call_conv_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::bad_call_conv_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem badCallConv_rejected :
    translateCallConv .rustIntrinsic = none ∧
    translateCallConv (.other "sysv64") = none ∧
    translateFn badCallConvCallee = none ∧
    inFragment badCallConvCallee = false ∧
    translateFn badCallConvSysvBody = none ∧
    inFragment badCallConvSysvBody = false ∧
    callTerminatorOk [badCallConvCallee] badCallConvCaller 0
      (mkTerm (.call (fnDefOp "witness::bad_call_conv_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_)) = false ∧
    progInFragment badCallConvCaller [badCallConvCallee] = false ∧
    translateProg badCallConvCaller [badCallConvCallee] = none :=
  ⟨rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, rfl⟩

/-- Counterexample 5 (`StorageLive(_2); StorageDead(_2); _2 = idU32Callee(copy _1)`):
calling into a dead return place `_2`. In MiniRust, `Terminator::Call` evaluates
the return place `_2` and runs `prepare_for_inplace_passing` BEFORE argument
evaluation or callee entry, faulting on step 4 (after `initBlock` `Goto(bb0)`,
`StorageLive(_2)`, and `StorageDead(_2)`) with `"access to a dead local"`
before `idU32Callee` is ever entered. `callDestOk` requires `lv.contains dst`
and rejects this caller. -/
def deadCallDestCaller : CapturedMir where
  defPath := "witness::dead_call_dest_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2), mkStmt (.storageDead 2)],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (local_ 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 0)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem deadCallDest_rejected :
    callDestOk deadCallDestCaller.localDecls (mustLiveBefore deadCallDestCaller 0 2)
      (tupleInitBefore deadCallDestCaller 0 2) u32Decl (local_ 2) = false ∧
    progInFragment deadCallDestCaller [idU32Callee] = false := by
  decide

def deadCallDestProg : Gen.Program :=
  (translateProg deadCallDestCaller [idU32Callee]).getD emptyProg
def deadCallDestFn : Gen.Function :=
  (translateFnInProg (fnNameMap deadCallDestCaller [idU32Callee]) deadCallDestCaller).getD callerFn
theorem deadCallDest_translate :
    translateProg deadCallDestCaller [idU32Callee] = some deadCallDestProg := rfl

def deadCallDestS0 : MachineState :=
  initMachineStateWithCallees deadCallDestCaller [.scalar ⟨7, 4⟩] [idU32Callee]
def deadCallDestMInit : Mach :=
  multiMachineWithCtx ctxCallSpin deadCallDestProg 2 deadCallDestCaller deadCallDestFn
    deadCallDestS0.frame.locals deadCallDestFn.start

theorem deadCallDest_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees deadCallDestCaller [.scalar ⟨7, 4⟩] [idU32Callee]) tr u ∧
      FaultNow u :=
  faultsA_sound deadCallDestCaller 10 _ (by decide)

theorem deadCallDest_minirust_ub_before_callee :
    Interp.steps 4 deadCallDestMInit =
      .error (.ub "access to a dead local") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

/-- Counterexample 6 (`StorageLive(_2); _2.0 = negI8Callee(copy _1); _0 = copy (_2.0);
StorageDead(_2); Return` where `_2 : (i8, bool)` is live but uninitialized):
when `negI8Callee(5i8)` returns `-5i8`, Anneal's `writePlaceValue` faults with UB
because projected field assignment into `.uninit` local `_2` is forbidden in
Anneal's value-slot model (`uninitProjCallDest_anneal_ub`), whereas MiniRust's
byte-level stack allocation writes `[-5i8]` to byte `0` of `_2` and returns
`-5i8` (`251`) cleanly (`uninitProjCallDest_minirust_ret`)! Thus `ti.contains dst`
(`tupleInitOk`) in `callDestOk` is strictly required for forward UB soundness. -/
def uninitProjCallDestCaller : CapturedMir where
  defPath := "witness::uninit_proj_call_dest_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl, i8BoolTupleDecl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2)],
      terminator := mkTerm (.call (fnDefOp "witness::neg_i8_callee")
        [.copy (local_ 1)] (field0I8 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (field0I8 2)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem uninitProjCallDest_rejected :
    (mustLiveBefore uninitProjCallDestCaller 0 1).contains 2 = true ∧
    (tupleInitBefore uninitProjCallDestCaller 0 1).contains 2 = false ∧
    callDestOk uninitProjCallDestCaller.localDecls (mustLiveBefore uninitProjCallDestCaller 0 1)
      (tupleInitBefore uninitProjCallDestCaller 0 1) i8Decl (field0I8 2) = false ∧
    progInFragment uninitProjCallDestCaller [negI8Callee] = false := by
  decide

def uninitProjCallDestProg : Gen.Program :=
  (translateProg uninitProjCallDestCaller [negI8Callee]).getD emptyProg
def uninitProjCallDestFn : Gen.Function :=
  (translateFnInProg (fnNameMap uninitProjCallDestCaller [negI8Callee])
    uninitProjCallDestCaller).getD callerFnI8
theorem uninitProjCallDest_translate :
    translateProg uninitProjCallDestCaller [negI8Callee] = some uninitProjCallDestProg := rfl

def uninitProjCallDestS0 : MachineState :=
  initMachineStateWithCallees uninitProjCallDestCaller [.scalar ⟨5, 1⟩] [negI8Callee]
def uninitProjCallDestMInit : Mach :=
  multiMachineWithCtx ctxCalleeDivZero uninitProjCallDestProg 2 uninitProjCallDestCaller
    uninitProjCallDestFn uninitProjCallDestS0.frame.locals uninitProjCallDestFn.start

theorem uninitProjCallDest_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees uninitProjCallDestCaller [.scalar ⟨5, 1⟩] [negI8Callee]) tr u ∧
      FaultNow u :=
  faultsA_sound uninitProjCallDestCaller 15 _ (by decide)

theorem uninitProjCallDest_minirust_ret :
    (Interp.steps 9 uninitProjCallDestMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 251 }, [1]) := by
  decide +kernel

/-- Diamond call-graph DAG (`diamondCallEntry -> diamondMidA -> cAbiCallee` and
`diamondCallEntry -> diamondMidB -> cAbiCallee`) mixing `.Rust` (`diamondCallEntry`,
`diamondMidA`) and `.C` (`diamondMidB`, `cAbiCallee`) calling conventions across
shared leaf `cAbiCallee`. -/
def diamondMidA : CapturedMir where
  defPath := "witness::diamond_mid_a"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::c_abi_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

def diamondMidB : CapturedMir where
  defPath := "witness::diamond_mid_b"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.binaryOp .add (.copy (local_ 1)) (constU32 1)))],
      terminator := mkTerm (.call (fnDefOp "witness::c_abi_callee")
        [.move (local_ 2)] (local_ 0) (some 1) .terminate),
      isCleanup := false },
    { statements := [mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiC1
  layouts := emptyLayoutTable
  allocations := []

def diamondCallEntry : CapturedMir where
  defPath := "witness::diamond_call_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2), mkStmt (.storageLive 3)],
      terminator := mkTerm (.call (fnDefOp "witness::diamond_mid_a")
        [.copy (local_ 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::diamond_mid_b")
        [.move (local_ 1)] (local_ 3) (some 2) .unreachable),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.move (local_ 2)) (.move (local_ 3)))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem diamondCall_inFragment :
    progInFragment diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee] = true := by
  decide

theorem diamondCall_maxStackLocals :
    maxStackLocals diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee] = some 9 := rfl

def ctxDiamondCall : Ctx :=
  ctxWithFns callerFrame retAlloc 4 [128, 256]

theorem ctxDiamondCall_ok : CtxOk diamondCallEntry ctxDiamondCall where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [diamondCallEntry] at hd; subst hd; decide
    | 1, _, hd => simp [diamondCallEntry] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [diamondCallEntry] at hi
  ret := by
    intro d hd; simp [diamondCallEntry] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def diamondCallProg : Gen.Program :=
  (translateProg diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee]).getD emptyProg
def diamondCallEntryFn : Gen.Function :=
  (translateFnInProg (fnNameMap diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee])
    diamondCallEntry).getD callerFn
theorem diamondCall_translate :
    translateProg diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee] =
      some diamondCallProg := rfl
theorem diamondCallEntry_translateInProg :
    translateFnInProg (fnNameMap diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee])
      diamondCallEntry = some diamondCallEntryFn := rfl

def diamondCall5Args : List Value := [.scalar ⟨5, 4⟩]
def diamondCall5S0 : MachineState :=
  initMachineStateWithCallees diamondCallEntry diamondCall5Args
    [diamondMidA, diamondMidB, cAbiCallee]
def diamondCall5MInit : Mach :=
  multiMachineWithCtx ctxDiamondCall diamondCallProg 4 diamondCallEntry diamondCallEntryFn
    diamondCall5S0.frame.locals diamondCallEntryFn.start

theorem diamondCall5_anneal_ret :
    ReachesRet
      (mirCallTreeWithCallees diamondCallEntry diamondCall5Args
        [diamondMidA, diamondMidB, cAbiCallee]) []
      (.normal (.scalar ⟨31, 4⟩,
        { diamondCall5S0.memory with activeCallee := some diamondCallEntry })) :=
  runA_sound diamondCallEntry 35 _ _ _ rfl

theorem diamondCall5_noUB :
    MirNoUBTree
      (mirCallTreeWithCallees diamondCallEntry diamondCall5Args
        [diamondMidA, diamondMidB, cAbiCallee]) :=
  runA_noUB diamondCallEntry 35 _ _ _ rfl

theorem diamondCall5_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n diamondCall5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 31 } ∧
      m'.threads = [thread1 ctxDiamondCall
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret diamondCall_inFragment diamondCall_translate
      diamondCallEntry_translateInProg ctxDiamondCall ctxDiamondCall_ok
      diamondCall5Args (by decide) diamondCall5MInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      diamondCall5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [diamondCallEntry] at hd; subst hd
  simp [retPtr, ctxDiamondCall, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxDiamondCall, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem diamondCall5_minirust_direct :
    (Interp.steps 24 diamondCall5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 31 }, [1]) := by
  decide +kernel

end MiniRustSpec.Correspondence.Witness
