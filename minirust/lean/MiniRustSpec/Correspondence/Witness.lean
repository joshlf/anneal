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

end MiniRustSpec.Correspondence.Witness
