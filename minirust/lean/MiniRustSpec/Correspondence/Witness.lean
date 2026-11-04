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
    mem := { memory := { allocations := ctx.base ++ localAllocs ctx body.localDecls locals,
                         _phantom := {} },
             accesses := [] },
    intptrcast := ⟨⟨[]⟩⟩,
    threads := [thread1 ctx [ctx.caller,
      { calleeFrame fn ctx body.localDecls.length 0 0 with next_block := blk }]],
    active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [], global_ptrs := ⟨[]⟩,
    fn_ptrs := ⟨[]⟩, vtable_ptrs := ⟨[]⟩, stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

def machine : CapturedMir → Gen.Function → List LocalSlot → Gen.BbName → Mach :=
  machineWithCtx ctx0

theorem ctx0_ok1 {body : CapturedMir} (h : body.localDecls = [u32Decl]) : CtxOk body ctx0 where
  addrs := by
    intro i d hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | _ + 1, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem ctx0_ok2 {body : CapturedMir} (h : body.localDecls = [u32Decl, u32Decl]) : CtxOk body ctx0 where
  addrs := by
    intro i d hd; rw [h] at hd
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

theorem sumTo_rel : StateRel sumTo sumToFn ctx0 sumToS0 sumToM0 where
  threads := rfl
  active := rfl
  allocs := rfl
  blk := by decide
  stmt := by intro bb hbb; simp [sumToS0, initMachineState] at hbb ⊢
  nlocals := by decide
  slots := by
    intro i d slot hd hs
    have hloc : sumToS0.frame.locals = [.uninit, .init (.scalar ⟨3, 4⟩)] := rfl
    rw [hloc] at hs
    match i, hd, hs with
    | 0, hd, hs => simp [sumTo] at hd; subst hd; simp at hs; subst hs; trivial
    | 1, hd, hs =>
      simp [sumTo] at hd; subst hd
      simp at hs; subst hs
      exact ⟨rfl, by decide⟩
    | _ + 2, hd, _ => simp [sumTo] at hd
  addrs := by
    intro i d hd
    match i, hd with
    | 0, hd => simp [sumTo] at hd; subst hd; decide
    | 1, hd => simp [sumTo] at hd; subst hd; decide
    | _ + 2, hd => simp [sumTo] at hd
  ret := by
    intro d hd
    simp [sumTo] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩
  borrows := rfl
  callStack := rfl
  activeCallee := rfl
  protectors := rfl
  callerLocals := rfl

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [sumTo] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  have hbits : bits = 6 := by
    simp [itOf, intTypeOf, intTyBytes, u32Decl, u32Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctx0, itOf, intTypeOf, intTyBytes, u32Decl, u32Ty, u32]

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [sumTo] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  have hbits : bits = 6 := by
    simp [itOf, intTypeOf, intTyBytes, u32Decl, u32Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctx0, itOf, intTypeOf, intTyBytes, u32Decl, u32Ty, u32]

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

theorem retUninit_rel : StateRel retUninit retUninitFn ctx0 retUninitS0 retUninitM0 where
  threads := rfl
  active := rfl
  allocs := rfl
  blk := by decide
  stmt := by intro bb hbb; simp [retUninitS0, initMachineState] at hbb ⊢
  nlocals := by decide
  slots := by
    intro i d slot hd hs
    have hloc : retUninitS0.frame.locals = [.uninit] := rfl
    rw [hloc] at hs
    match i, hd, hs with
    | 0, hd, hs =>
      simp [retUninit] at hd; subst hd
      simp at hs; subst hs; trivial
    | _ + 1, hd, _ => simp [retUninit] at hd
  addrs := by
    intro i d hd
    match i, hd with
    | 0, hd => simp [retUninit] at hd; subst hd; decide
    | _ + 1, hd => simp [retUninit] at hd
  ret := by
    intro d hd
    simp [retUninit] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩
  borrows := rfl
  callStack := rfl
  activeCallee := rfl
  protectors := rfl
  callerLocals := rfl

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

def retUninitMInit : Mach := machine retUninit retUninitFn retUninitS0.frame.locals retUninitFn.start

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [negMention] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  have hbits : bits = 4294967291 := by
    simp [itOf, intTypeOf, intTyBytes, u32Decl, u32Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctx0, itOf, intTypeOf, intTyBytes, u32Decl, u32Ty, u32]

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
  addrs := by
    intro i d hd; rw [h] at hd
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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [signedEdge] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  have hbits : bits = 127 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [signedEdge] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  have hbits : bits = 2 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  addrs := by
    intro i d hd; rw [h] at hd
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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [castBitNot] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  have hbits : bits = 4 := by
    simp [itOf, intTypeOf, intTyBytes, u32Decl, u32Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctx0, itOf, intTypeOf, intTyBytes, u32Decl, u32Ty, u32]

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
`n : Nat`, `n + 1` MiniRust steps from `f.start` stay in `StateRel` with an
Anneal state reachable via `Reaches (mirCallTree spinLoop [])`. -/
theorem spinLoop_minirust_diverges_rel (n : Nat) :
    ∃ s' m' tr, Interp.steps (n + 1) spinLoopMInit = .ok m' ∧
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
  addrs := by
    intro i d hd; rw [h] at hd
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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [divRemI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  have hbits : bits = 255 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_3, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [divRemI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  have hbits : bits = 128 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_3, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [uncheckedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  have hbits : bits = 1 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_3, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
    (∃ s' m' tr, Interp.steps (n + 1) uncheckedAddUbMInit = .ok m' ∧
      StateRel uncheckedArithI8 uncheckedArithI8Fn ctxI8_3 s' m' ∧
      Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]) tr
        (mirTree uncheckedArithI8 s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n + 1 ∧ Interp.steps k uncheckedAddUbMInit = .ok mRet ∧
      ReturnRel uncheckedArithI8 ctxI8_3 s' v mRet ∧
      ReachesRet (mirCallTree uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (n + 1) uncheckedAddUbMInit = .error (.ub msg) ∧
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
    ∃ s' m' tr, Interp.steps (n + 1) branchSpinLoop1MInit = .ok m' ∧
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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [shiftI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  have hbits : bits = 224 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_3, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [bitwiseI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  have hbits : bits = 96 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_3, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  addrs := by
    intro i d hd; rw [h] at hd
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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [heteroShiftSwitch] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  have hbits : bits = 224 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_3, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  addrs := by
    intro i d hd; rw [h] at hd
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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [cmpNotSwitch] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  have hbits : bits = 255 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_4, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [cmpNotSwitch] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  have hbits : bits = 2 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_4, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  addrs := by
    intro i d hd; rw [h] at hd
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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [leNeGe] at hd; subst hd
  simp [retPtr, ctxBool] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxBool] at hr; subst hr
  have hbits : bits = 1 := by
    simp [itOf, intTypeOf, intTyBytes, boolDecl, boolTy] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxBool, itOf, intTypeOf, intTyBytes, boolDecl, boolTy, u8]

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [leNeGe] at hd; subst hd
  simp [retPtr, ctxBool] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxBool] at hr; subst hr
  have hbits : bits = 0 := by
    simp [itOf, intTypeOf, intTyBytes, boolDecl, boolTy] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxBool, itOf, intTypeOf, intTyBytes, boolDecl, boolTy, u8]

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
  addrs := by
    intro i d hd; rw [h] at hd
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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [boolCastI8] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  have hbits : bits = 1 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [boolCastI8] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  have hbits : bits = 0 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

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
  addrs := by
    intro i d hd; rw [h] at hd
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
  addrs := by
    intro i d hd; rw [h] at hd
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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [cmpSel] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  have hbits : bits = 255 := by
    simp [itOf, intTypeOf, intTyBytes, orderingDecl, orderingTyW] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_4, itOf, intTypeOf, intTyBytes, orderingDecl, orderingTyW, u8]

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [cmpSel] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  have hbits : bits = 0 := by
    simp [itOf, intTypeOf, intTyBytes, orderingDecl, orderingTyW] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_4, itOf, intTypeOf, intTyBytes, orderingDecl, orderingTyW, u8]

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
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [cmpSel] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  have hbits : bits = 1 := by
    simp [itOf, intTypeOf, intTyBytes, orderingDecl, orderingTyW] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_4, itOf, intTypeOf, intTyBytes, orderingDecl, orderingTyW, u8]

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
  addrs := by
    intro i d hd; rw [h] at hd
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

end MiniRustSpec.Correspondence.Witness
