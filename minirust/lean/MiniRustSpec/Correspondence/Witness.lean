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

/-- A MiniRust machine running `fn` with Anneal locals `locals` at the given
callee program counter. -/
def machine (body : CapturedMir) (fn : Gen.Function) (locals : List LocalSlot) (blk : Gen.BbName) :
    Mach :=
  { prog := emptyProg,
    mem := { memory := { allocations := ctx0.base ++ localAllocs ctx0 body.localDecls locals,
                         _phantom := {} },
             accesses := [] },
    intptrcast := ⟨⟨[]⟩⟩,
    threads := [thread1 ctx0 [ctx0.caller,
      { calleeFrame fn ctx0 body.localDecls.length 0 0 with next_block := blk }]],
    active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [], global_ptrs := ⟨[]⟩,
    fn_ptrs := ⟨[]⟩, vtable_ptrs := ⟨[]⟩, stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

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
init block), via `run_ret_from_start`. -/
theorem sumTo_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n sumToMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    run_ret_from_start sumTo_inFragment sumTo_translate ctx0 sumToS0 sumToM0 sumToMInit
      sumTo_rel rfl rfl ⟨rfl, rfl, rfl⟩ sumTo_anneal_ret
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
block), via `run_ub_from_start`. -/
theorem retUninit_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n retUninitMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := retUninit_anneal_ub
  exact run_ub_from_start retUninit_inFragment retUninit_translate ctx0 retUninitS0
    retUninitM0 retUninitMInit retUninit_rel rfl rfl ⟨rfl, rfl, rfl⟩ hr hf

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
def negMention5M0 : Mach := machine negMention negMentionFn negMention5S0.frame.locals (bbName 0)
def negMention5MInit : Mach := machine negMention negMentionFn negMention5S0.frame.locals negMentionFn.start

theorem negMention5_rel : StateRel negMention negMentionFn ctx0 negMention5S0 negMention5M0 where
  threads := rfl
  active := rfl
  allocs := rfl
  blk := by decide
  stmt := by intro bb hbb; simp [negMention5S0, initMachineState] at hbb ⊢
  nlocals := by decide
  slots := by
    intro i d slot hd hs
    have hloc : negMention5S0.frame.locals = [.uninit, .init (.scalar ⟨5, 4⟩)] := rfl
    rw [hloc] at hs
    match i, hd, hs with
    | 0, hd, hs => simp [negMention] at hd; subst hd; simp at hs; subst hs; trivial
    | 1, hd, hs =>
      simp [negMention] at hd; subst hd
      simp at hs; subst hs
      exact ⟨rfl, by decide⟩
    | _ + 2, hd, _ => simp [negMention] at hd
  addrs := by
    intro i d hd
    match i, hd with
    | 0, hd => simp [negMention] at hd; subst hd; decide
    | 1, hd => simp [negMention] at hd; subst hd; decide
    | _ + 2, hd => simp [negMention] at hd
  ret := by
    intro d hd
    simp [negMention] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩
  borrows := rfl
  callStack := rfl
  activeCallee := rfl
  protectors := rfl
  callerLocals := rfl

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
      negMention5M0 negMention5MInit negMention5_rel rfl rfl ⟨rfl, rfl, rfl⟩ negMention5_anneal_ret
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
def negMention0M0 : Mach := machine negMention negMentionFn negMention0S0.frame.locals (bbName 0)
def negMention0MInit : Mach := machine negMention negMentionFn negMention0S0.frame.locals negMentionFn.start

theorem negMention0_rel : StateRel negMention negMentionFn ctx0 negMention0S0 negMention0M0 where
  threads := rfl
  active := rfl
  allocs := rfl
  blk := by decide
  stmt := by intro bb hbb; simp [negMention0S0, initMachineState] at hbb ⊢
  nlocals := by decide
  slots := by
    intro i d slot hd hs
    have hloc : negMention0S0.frame.locals = [.uninit, .init (.scalar ⟨0, 4⟩)] := rfl
    rw [hloc] at hs
    match i, hd, hs with
    | 0, hd, hs => simp [negMention] at hd; subst hd; simp at hs; subst hs; trivial
    | 1, hd, hs =>
      simp [negMention] at hd; subst hd
      simp at hs; subst hs
      exact ⟨rfl, by decide⟩
    | _ + 2, hd, _ => simp [negMention] at hd
  addrs := by
    intro i d hd
    match i, hd with
    | 0, hd => simp [negMention] at hd; subst hd; decide
    | 1, hd => simp [negMention] at hd; subst hd; decide
    | _ + 2, hd => simp [negMention] at hd
  ret := by
    intro d hd
    simp [negMention] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩
  borrows := rfl
  callStack := rfl
  activeCallee := rfl
  protectors := rfl
  callerLocals := rfl

theorem negMention0_anneal_ub :
    ∃ tr u, Reaches (mirTree negMention negMention0S0) tr u ∧ FaultNow u :=
  faultsA_sound negMention 10 _ (by decide)

theorem negMention0_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n negMention0MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := negMention0_anneal_ub
  exact run_ub_from_start negMention_inFragment negMention_translate ctx0 negMention0S0
    negMention0M0 negMention0MInit negMention0_rel rfl rfl ⟨rfl, rfl, rfl⟩ hr hf

theorem negMention0_minirust_direct :
    ∃ msg, Interp.steps 5 negMention0MInit = .error (.ub msg) :=
  ⟨_, rfl⟩

end MiniRustSpec.Correspondence.Witness
