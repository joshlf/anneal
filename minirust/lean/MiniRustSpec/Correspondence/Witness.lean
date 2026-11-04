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
* `arrayOpsI8`, `arraySignedIdxI8`, and `zeroArrayI8`: fixed-size homogeneous
  arrays (`Type::Array` / `TyKind.array`), `AggregateKind.array`,
  `Rvalue.repeat`, `Rvalue.len`, whole-array `Use(Copy)`, and
  `ProjectionElem.index` / `ProjectionElem.constantIndex` (`fromEnd = false`
  and `fromEnd = true`) for both reads and in-place element writes preserving
  sibling elements, plus out-of-bounds (`idx >= count`), negative signed index
  (`idx < 0`), and zero-length array (`[i8; 0]`) construction, `Len`, and
  indexing UB, with a byte-level check that the in-place writes leave the
  sibling bytes of MiniRust's array allocation intact
  (`arrayOpsOk_minirust_inplace_bytes`).
* `arrayUninitIdxI8`: an index local that is still uninitialized (`_1[_0]`
  before `_0` is written) raises UB on both sides; MiniRust's `Load` of the
  index operand fails the validity invariant before the bounds check.
* `arrayU32Idx`: a multi-byte element type (`[u32; 3]`), so that the byte
  offset `index * elem_size` of `PlaceExpr::Index` is exercised with
  `elem_size = 4` (all other array witnesses use 1-byte `i8` elements, for
  which the offset equals the index): an in-place write at index `2` lands at
  byte offset `8` and leaves the first two elements intact, and index `3`
  raises out-of-bounds UB on both sides.
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

@[simp] theorem arrayTypeOf_int (it : IntTy) (l : Nat) :
    arrayTypeOf { kind := .int it, layoutIdx := l } = none := rfl

@[simp] theorem arrayTypeOf_uint (ut : UintTy) (l : Nat) :
    arrayTypeOf { kind := .uint ut, layoutIdx := l } = none := rfl

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

/-! ## Homogeneous arrays (`Type::Array`), `Repeat`, `Len`, and `Index`/`ConstantIndex` projections -/

def usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
def usizeDecl : LocalDecl := { mutability := .mut, ty := usizeTy, debugName := none }
def constUsize (n : Nat) : Operand := .constant { ty := usizeTy, val := .scalar (.int ⟨n, 8⟩) }

def arrI8_3Ty : Ty := { kind := .array (.int .i8) 3, layoutIdx := 0 }
def arrI8_3Decl : LocalDecl := { mutability := .mut, ty := arrI8_3Ty, debugName := none }

def arrI8_2Ty : Ty := { kind := .array (.int .i8) 2, layoutIdx := 0 }
def arrI8_2Decl : LocalDecl := { mutability := .mut, ty := arrI8_2Ty, debugName := none }

def arrI8_0Ty : Ty := { kind := .array (.int .i8) 0, layoutIdx := 0 }
def arrI8_0Decl : LocalDecl := { mutability := .mut, ty := arrI8_0Ty, debugName := none }

def usizeLayout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def arrI8_3Layout : TypeLayout :=
  { size := { bytes := 3 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def arrI8_2Layout : TypeLayout :=
  { size := { bytes := 2 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def arrI8_0Layout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiArrayOps : FnAbi :=
  { args := [{ layout := arrI8_3Layout, mode := .direct },
             { layout := arrI8_3Layout, mode := .direct },
             { layout := i8Layout, mode := .direct },
             { layout := usizeLayout, mode := .direct },
             { layout := usizeLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

def ctxI8_6 : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8],
    addrs := [128, 256, 384, 512, 640, 768],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxI8_ok_arrayOps {body : CapturedMir}
    (h : body.localDecls = [i8Decl, arrI8_3Decl, arrI8_3Decl, i8Decl, usizeDecl, usizeDecl]) :
    CtxOk body ctxI8_6 where
  addrs := by
    intro i d hd; rw [h] at hd
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
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

def placeIdx (i idxLocal : Nat) : Place :=
  { local_ := i, projection := [.index idxLocal] }

def placeConstIdx (i offset minLen : Nat) (fromEnd : Bool) : Place :=
  { local_ := i, projection := [.constantIndex offset minLen fromEnd] }

/-- MIR (`Runtime(PostCleanup)`) of a function exercising homogeneous `[i8; 3]`
arrays across all six `MR-2.1` constructs:
1. `_1 = [copy _3, 10i8, 20i8]` (`Rvalue.aggregate (.array i8Ty)`),
2. `_2 = [5i8; 3]` (`Rvalue.repeat`),
3. `_2 = copy _1` (whole-array `Rvalue.use (.copy _1)`),
4. `_2[_4] = Add(copy _2[_4], 7i8)` (`ProjectionElem.index` read and in-place write),
5. `_2[-1 of 3] = Sub(copy _2[-1 of 3], copy _2[0 of 3])`
   (`ProjectionElem.constantIndex` with `fromEnd = true` and `fromEnd = false`,
   both read and in-place write),
6. `_5 = Len(_2)` (`Rvalue.len`), cast to `i8`, and summed with all three
   elements `_2[_4]`, `_2[-1 of 3]`, and `_2[0 of 3]` to verify that in-place
   indexed writes preserve sibling elements. -/
def arrayOpsI8 : CapturedMir where
  defPath := "witness::array_ops_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 5
  localDecls := [i8Decl, arrI8_3Decl, arrI8_3Decl, i8Decl, usizeDecl, usizeDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1)
          (.aggregate (.array i8Ty) [.copy (local_ 3), constI8 10, constI8 20])),
        mkStmt (.assign (local_ 2) (.repeat (constI8 5) 3)),
        mkStmt (.assign (local_ 2) (.use (.copy (local_ 1)))),
        mkStmt (.assign (placeIdx 2 4)
          (.binaryOp .add (.copy (placeIdx 2 4)) (constI8 7))),
        mkStmt (.assign (placeConstIdx 2 1 3 true)
          (.binaryOp .sub (.copy (placeConstIdx 2 1 3 true)) (.copy (placeConstIdx 2 0 3 false)))),
        mkStmt (.assign (local_ 5) (.len (local_ 2))),
        mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 5)) i8Ty)),
        mkStmt (.assign (local_ 0)
          (.binaryOp .add (.copy (local_ 0)) (.copy (placeIdx 2 4)))),
        mkStmt (.assign (local_ 0)
          (.binaryOp .add (.copy (local_ 0)) (.copy (placeConstIdx 2 1 3 true)))),
        mkStmt (.assign (local_ 0)
          (.binaryOp .add (.copy (local_ 0)) (.copy (placeConstIdx 2 0 3 false))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArrayOps
  layouts := emptyLayoutTable
  allocations := []

theorem arrayOpsI8_inFragment : inFragment arrayOpsI8 = true := by decide

def arrayOpsI8Fn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int i8),
    (localName 1, .Array (.Int i8) 3),
    (localName 2, .Array (.Int i8) 3),
    (localName 3, .Int i8),
    (localName 4, .Int usizeIt),
    (localName 5, .Int usizeIt)]⟩
  args := [localName 1, localName 2, localName 3, localName 4, localName 5]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Local (localName 3)),
          .Constant (.Int 10) (.Int i8),
          .Constant (.Int 20) (.Int i8)] (.Array (.Int i8) 3)),
      .Assign (.Local (localName 2))
        (.Tuple [
          .Constant (.Int 5) (.Int i8),
          .Constant (.Int 5) (.Int i8),
          .Constant (.Int 5) (.Int i8)] (.Array (.Int i8) 3)),
      .Assign (.Local (localName 2)) (.Load (.Local (localName 1))),
      .Assign (.Index (.Local (localName 2)) (.Load (.Local (localName 4))))
        (.BinOp (.Int .Add)
          (.Load (.Index (.Local (localName 2)) (.Load (.Local (localName 4)))))
          (.Constant (.Int 7) (.Int i8))),
      .Assign (.Index (.Local (localName 2)) (.Constant (.Int 2) (.Int usizeIt)))
        (.BinOp (.Int .Sub)
          (.Load (.Index (.Local (localName 2)) (.Constant (.Int 2) (.Int usizeIt))))
          (.Load (.Index (.Local (localName 2)) (.Constant (.Int 0) (.Int usizeIt))))),
      .Assign (.Local (localName 5)) (.Constant (.Int 3) (.Int usizeIt)),
      .Assign (.Local (localName 0)) (.UnOp (.Cast (.IntToInt i8)) (.Load (.Local (localName 5)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add)
          (.Load (.Local (localName 0)))
          (.Load (.Index (.Local (localName 2)) (.Load (.Local (localName 4)))))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add)
          (.Load (.Local (localName 0)))
          (.Load (.Index (.Local (localName 2)) (.Constant (.Int 2) (.Int usizeIt))))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add)
          (.Load (.Local (localName 0)))
          (.Load (.Index (.Local (localName 2)) (.Constant (.Int 0) (.Int usizeIt)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arrayOpsI8_translate : translateFn arrayOpsI8 = some arrayOpsI8Fn := rfl

def initArrI8_3 : Value := .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩]

def arrayOpsOkArgs : List Value :=
  [initArrI8_3, initArrI8_3, .scalar ⟨3, 1⟩, .scalar ⟨1, 8⟩, .scalar ⟨0, 8⟩]

/-- Input `_3 = 3i8`, `_4 = 1usize`:
* `_1 = [3, 10, 20]`, `_2 = [5, 5, 5]`, then `_2 = copy _1 = [3, 10, 20]`;
* `_2[1] = _2[1] + 7 = 17`, so `_2 = [3, 17, 20]`;
* `_2[2] = _2[2] - _2[0] = 20 - 3 = 17`, so `_2 = [3, 17, 17]`;
* `_5 = Len(_2) = 3usize`, and `_0 = 3 + 17 + 17 + 3 = 40i8`. -/
def arrayOpsOkS0 : MachineState := initMachineState arrayOpsI8 arrayOpsOkArgs
def arrayOpsOkMInit : Mach :=
  machineWithCtx ctxI8_6 arrayOpsI8 arrayOpsI8Fn arrayOpsOkS0.frame.locals arrayOpsI8Fn.start

theorem arrayOpsOk_anneal_ret :
    ReachesRet (mirCallTree arrayOpsI8 arrayOpsOkArgs) []
      (.normal (.scalar ⟨40, 1⟩, arrayOpsOkS0.memory)) :=
  runA_sound arrayOpsI8 16 _ _ _ rfl

theorem arrayOpsOk_noUB :
    MirNoUBTree (mirCallTree arrayOpsI8 arrayOpsOkArgs) :=
  runA_noUB arrayOpsI8 16 _ _ _ rfl

theorem arrayOpsOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n arrayOpsOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 40 } ∧
      m'.threads = [thread1 ctxI8_6 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret arrayOpsI8_inFragment arrayOpsI8_translate ctxI8_6
      (ctxI8_ok_arrayOps rfl) arrayOpsOkArgs (by decide)
      arrayOpsOkMInit rfl rfl rfl arrayOpsOk_anneal_ret
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [arrayOpsI8] at hd; subst hd
  simp [retPtr, ctxI8_6] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_6] at hr; subst hr
  have hbits : bits = 40 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_6, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

theorem arrayOpsOk_minirust_direct :
    (Interp.steps 12 arrayOpsOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 40 }, [1]) := rfl

/-- Byte-level view of the in-place element writes of `arrayOpsI8` on the
input of `arrayOpsOkArgs`. MiniRust's allocation `3` is `_2`'s (after the
caller's return allocation and those of `_0` and `_1`). After step `4`
(`_2 = copy _1`) it holds the bytes of `[3, 10, 20]`; step `5`
(`_2[_4] = _2[_4] + 7`) rewrites only the byte at offset `1`, giving
`[3, 17, 20]`; step `6` (`_2[-1 of 3] = _2[-1 of 3] - _2[0 of 3]`) rewrites
only the byte at offset `2`, giving `[3, 17, 17]`. Each store leaves the
sibling bytes before and after the written element unchanged. -/
theorem arrayOpsOk_minirust_inplace_bytes :
    [4, 5, 6].map (fun k => (Interp.steps k arrayOpsOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[3]?).map (·.data))) =
      [some (some (scalarBytes i8 3 ++ scalarBytes i8 10 ++ scalarBytes i8 20)),
       some (some (scalarBytes i8 3 ++ scalarBytes i8 17 ++ scalarBytes i8 20)),
       some (some (scalarBytes i8 3 ++ scalarBytes i8 17 ++ scalarBytes i8 17))] := rfl

/-- Out-of-bounds `Index` (`_4 = 3usize >= 3`) on `arrayOpsI8`: raises UB on
`_2[_4]`. -/
def arrayOpsOobArgs : List Value :=
  [initArrI8_3, initArrI8_3, .scalar ⟨3, 1⟩, .scalar ⟨3, 8⟩, .scalar ⟨0, 8⟩]

def arrayOpsOobS0 : MachineState := initMachineState arrayOpsI8 arrayOpsOobArgs
def arrayOpsOobMInit : Mach :=
  machineWithCtx ctxI8_6 arrayOpsI8 arrayOpsI8Fn arrayOpsOobS0.frame.locals arrayOpsI8Fn.start

theorem arrayOpsOob_anneal_ub :
    ∃ tr u, Reaches (mirCallTree arrayOpsI8 arrayOpsOobArgs) tr u ∧ FaultNow u :=
  faultsA_sound arrayOpsI8 8 _ (by decide)

theorem arrayOpsOob_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayOpsOobMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayOpsOob_anneal_ub
  exact mirCall_ub arrayOpsI8_inFragment arrayOpsI8_translate ctxI8_6
    (ctxI8_ok_arrayOps rfl) arrayOpsOobArgs (by decide)
    arrayOpsOobMInit rfl rfl rfl hr hf

theorem arrayOpsOob_minirust_direct :
    Interp.steps 5 arrayOpsOobMInit = .error (.ub "access to out-of-bounds index") := rfl

theorem arrayOpsOob_converse_error :
    (∃ msg, Stop.ub "access to out-of-bounds index" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree arrayOpsI8 arrayOpsOobArgs) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 5 ∧ Interp.steps k arrayOpsOobMInit = .ok mRet ∧
      ReturnRel arrayOpsI8 ctxI8_6 s' v mRet ∧
      ReachesRet (mirCallTree arrayOpsI8 arrayOpsOobArgs) tr (.normal (v, mem))) :=
  mirCall_steps_error arrayOpsI8_inFragment arrayOpsI8_translate ctxI8_6
    (ctxI8_ok_arrayOps rfl) arrayOpsOobArgs (by decide)
    arrayOpsOobMInit rfl rfl rfl arrayOpsOob_minirust_direct

/-! ## Signed index local (`i8`), negative index UB (`idx < 0`), and in-place write UB -/

def fnAbiArraySignedIdx : FnAbi :=
  { args := [{ layout := arrI8_2Layout, mode := .direct },
             { layout := i8Layout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_arraySignedIdx {body : CapturedMir}
    (h : body.localDecls = [i8Decl, arrI8_2Decl, i8Decl]) : CtxOk body ctxI8_3 where
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

/-- MIR (`Runtime(PostCleanup)`) of a function that indexes `[i8; 2]` with a
signed `i8` index local `_2` in both an in-place write `_1[_2] = const 99i8`
and a read `_0 = copy _1[_2]`. -/
def arraySignedIdxI8 : CapturedMir where
  defPath := "witness::array_signed_idx_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, arrI8_2Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (placeIdx 1 2) (.use (constI8 99))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeIdx 1 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArraySignedIdx
  layouts := emptyLayoutTable
  allocations := []

theorem arraySignedIdxI8_inFragment : inFragment arraySignedIdxI8 = true := by decide

def arraySignedIdxI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Array (.Int i8) 2), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Index (.Local (localName 1)) (.Load (.Local (localName 2))))
        (.Constant (.Int 99) (.Int i8)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arraySignedIdxI8_translate : translateFn arraySignedIdxI8 = some arraySignedIdxI8Fn := rfl

def initArrI8_2 : Value := .aggregate 0 [.scalar ⟨11, 1⟩, .scalar ⟨22, 1⟩]

/-- Signed index `_2 = 1i8`: writes `_1[1] = 99i8` and returns `99i8`. -/
def arraySignedIdxOkS0 : MachineState :=
  initMachineState arraySignedIdxI8 [initArrI8_2, .scalar ⟨1, 1⟩]
def arraySignedIdxOkMInit : Mach :=
  machineWithCtx ctxI8_3 arraySignedIdxI8 arraySignedIdxI8Fn
    arraySignedIdxOkS0.frame.locals arraySignedIdxI8Fn.start

theorem arraySignedIdxOk_anneal_ret :
    ReachesRet (mirCallTree arraySignedIdxI8 [initArrI8_2, .scalar ⟨1, 1⟩]) []
      (.normal (.scalar ⟨99, 1⟩, arraySignedIdxOkS0.memory)) :=
  runA_sound arraySignedIdxI8 8 _ _ _ rfl

theorem arraySignedIdxOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n arraySignedIdxOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 99 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret arraySignedIdxI8_inFragment arraySignedIdxI8_translate ctxI8_3
      (ctxI8_ok_arraySignedIdx rfl) [initArrI8_2, .scalar ⟨1, 1⟩] (by decide)
      arraySignedIdxOkMInit rfl rfl rfl arraySignedIdxOk_anneal_ret
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [arraySignedIdxI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  have hbits : bits = 99 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_3, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

theorem arraySignedIdxOk_minirust_direct :
    (Interp.steps 4 arraySignedIdxOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 99 }, [1]) := rfl

/-- Negative signed index `_2 = -1i8` (bits `255` in `i8`): raises UB on the
in-place element write `_1[_2] = 99i8`. -/
def arraySignedNegUbS0 : MachineState :=
  initMachineState arraySignedIdxI8 [initArrI8_2, .scalar ⟨255, 1⟩]
def arraySignedNegUbMInit : Mach :=
  machineWithCtx ctxI8_3 arraySignedIdxI8 arraySignedIdxI8Fn
    arraySignedNegUbS0.frame.locals arraySignedIdxI8Fn.start

theorem arraySignedNegUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arraySignedIdxI8 [initArrI8_2, .scalar ⟨255, 1⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arraySignedIdxI8 6 _ (by decide)

theorem arraySignedNegUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arraySignedNegUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arraySignedNegUb_anneal_ub
  exact mirCall_ub arraySignedIdxI8_inFragment arraySignedIdxI8_translate ctxI8_3
    (ctxI8_ok_arraySignedIdx rfl) [initArrI8_2, .scalar ⟨255, 1⟩] (by decide)
    arraySignedNegUbMInit rfl rfl rfl hr hf

theorem arraySignedNegUb_minirust_direct :
    Interp.steps 2 arraySignedNegUbMInit = .error (.ub "access to out-of-bounds index") := rfl

/-- Out-of-bounds positive signed index `_2 = 2i8` (`2 >= 2`): raises UB on the
in-place element write `_1[_2] = 99i8`. -/
def arraySignedOobUbS0 : MachineState :=
  initMachineState arraySignedIdxI8 [initArrI8_2, .scalar ⟨2, 1⟩]
def arraySignedOobUbMInit : Mach :=
  machineWithCtx ctxI8_3 arraySignedIdxI8 arraySignedIdxI8Fn
    arraySignedOobUbS0.frame.locals arraySignedIdxI8Fn.start

theorem arraySignedOobUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arraySignedIdxI8 [initArrI8_2, .scalar ⟨2, 1⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arraySignedIdxI8 6 _ (by decide)

theorem arraySignedOobUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arraySignedOobUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arraySignedOobUb_anneal_ub
  exact mirCall_ub arraySignedIdxI8_inFragment arraySignedIdxI8_translate ctxI8_3
    (ctxI8_ok_arraySignedIdx rfl) [initArrI8_2, .scalar ⟨2, 1⟩] (by decide)
    arraySignedOobUbMInit rfl rfl rfl hr hf

theorem arraySignedOobUb_minirust_direct :
    Interp.steps 2 arraySignedOobUbMInit = .error (.ub "access to out-of-bounds index") := rfl

/-! ## Zero-length array `[i8; 0]` construction, `Len`, and out-of-bounds indexing at `0` -/

def fnAbiZeroArray : FnAbi :=
  { args := [{ layout := arrI8_0Layout, mode := .direct },
             { layout := usizeLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_zeroArray {body : CapturedMir}
    (h : body.localDecls = [i8Decl, arrI8_0Decl, usizeDecl]) : CtxOk body ctxI8_3 where
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

/-- MIR (`Runtime(PostCleanup)`) of a function exercising a zero-length array
`[i8; 0]` (`_1`):
* in `bb0`, constructs `_1 = []` via `Rvalue.aggregate (.array i8Ty) []` and
  copies `_1 = copy _1` via `Rvalue.use (.copy _1)`, then switches on `_2`;
* when `_2 == 0` (`bb1`), constructs `_1 = [5i8; 0]` via
  `Rvalue.repeat (constI8 5) 0`, computes `_2 = Len(_1)` (`= 0usize`), casts to
  `0i8`, and returns;
* when `_2 != 0` (`bb2`), sets `_2 = 0usize` and attempts to read `_1[_2]` at
  index `0`, raising out-of-bounds UB (`0 >= 0`). -/
def zeroArrayI8 : CapturedMir where
  defPath := "witness::zero_array_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, arrI8_0Decl, usizeDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.array i8Ty) [])),
        mkStmt (.assign (local_ 1) (.use (.copy (local_ 1))))],
      terminator := mkTerm (.switchInt (.copy (local_ 2))
        { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.repeat (constI8 5) 0)),
        mkStmt (.assign (local_ 2) (.len (local_ 1))),
        mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 2)) i8Ty))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2) (.use (constUsize 0))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeIdx 1 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiZeroArray
  layouts := emptyLayoutTable
  allocations := []

theorem zeroArrayI8_inFragment : inFragment zeroArrayI8 = true := by decide

def zeroArrayI8Fn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int i8),
    (localName 1, .Array (.Int i8) 0),
    (localName 2, .Int usizeIt)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1)) (.Tuple [] (.Array (.Int i8) 0)),
      .Assign (.Local (localName 1)) (.Load (.Local (localName 1)))],
      .Switch (.Load (.Local (localName 2))) ⟨[(0, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 1)) (.Tuple [] (.Array (.Int i8) 0)),
      .Assign (.Local (localName 2)) (.Constant (.Int 0) (.Int usizeIt)),
      .Assign (.Local (localName 0)) (.UnOp (.Cast (.IntToInt i8)) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 2)) (.Constant (.Int 0) (.Int usizeIt)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2)))))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem zeroArrayI8_translate : translateFn zeroArrayI8 = some zeroArrayI8Fn := rfl

def initArrI8_0 : Value := .aggregate 0 []

/-- `_2 = 0usize`: constructs `[i8; 0]`, repeats `[5i8; 0]`, reads `Len(_1) = 0`,
and returns `0i8`. -/
def zeroArrayOkS0 : MachineState :=
  initMachineState zeroArrayI8 [initArrI8_0, .scalar ⟨0, 8⟩]
def zeroArrayOkMInit : Mach :=
  machineWithCtx ctxI8_3 zeroArrayI8 zeroArrayI8Fn
    zeroArrayOkS0.frame.locals zeroArrayI8Fn.start

def zeroArrayOkTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]

theorem zeroArrayOk_anneal_ret :
    ReachesRet (mirCallTree zeroArrayI8 [initArrI8_0, .scalar ⟨0, 8⟩])
      zeroArrayOkTrace (.normal (.scalar ⟨0, 1⟩, zeroArrayOkS0.memory)) :=
  runA_sound zeroArrayI8 12 _ _ _ rfl

theorem zeroArrayOk_noUB :
    MirNoUBTree (mirCallTree zeroArrayI8 [initArrI8_0, .scalar ⟨0, 8⟩]) :=
  runA_noUB zeroArrayI8 12 _ _ _ rfl

theorem zeroArrayOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n zeroArrayOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 0 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret zeroArrayI8_inFragment zeroArrayI8_translate ctxI8_3
      (ctxI8_ok_zeroArray rfl) [initArrI8_0, .scalar ⟨0, 8⟩] (by decide)
      zeroArrayOkMInit rfl rfl rfl zeroArrayOk_anneal_ret
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [zeroArrayI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  have hbits : bits = 0 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_3, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

theorem zeroArrayOk_minirust_direct :
    (Interp.steps 8 zeroArrayOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 0 }, [1]) := rfl

/-- `_2 = 1usize`: takes `bb2` and indexes `[i8; 0]` at `0usize`, raising
out-of-bounds UB (`0 >= 0`). -/
def zeroArrayIdxUbS0 : MachineState :=
  initMachineState zeroArrayI8 [initArrI8_0, .scalar ⟨1, 8⟩]
def zeroArrayIdxUbMInit : Mach :=
  machineWithCtx ctxI8_3 zeroArrayI8 zeroArrayI8Fn
    zeroArrayIdxUbS0.frame.locals zeroArrayI8Fn.start

theorem zeroArrayIdxUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree zeroArrayI8 [initArrI8_0, .scalar ⟨1, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound zeroArrayI8 10 _ (by decide)

theorem zeroArrayIdxUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n zeroArrayIdxUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := zeroArrayIdxUb_anneal_ub
  exact mirCall_ub zeroArrayI8_inFragment zeroArrayI8_translate ctxI8_3
    (ctxI8_ok_zeroArray rfl) [initArrI8_0, .scalar ⟨1, 8⟩] (by decide)
    zeroArrayIdxUbMInit rfl rfl rfl hr hf

theorem zeroArrayIdxUb_minirust_direct :
    Interp.steps 6 zeroArrayIdxUbMInit = .error (.ub "access to out-of-bounds index") := rfl

/-! ## Uninitialized index local (`_1[_0]` while `_0` is still `.uninit`) -/

def fnAbiArrayUninitIdx : FnAbi :=
  { args := [{ layout := arrI8_2Layout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_arrayUninitIdx {body : CapturedMir}
    (h : body.localDecls = [i8Decl, arrI8_2Decl]) : CtxOk body ctxI8 where
  addrs := by
    intro i d hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of a function that indexes `[i8; 2]` with the
return place `_0` as the index local before `_0` is ever written: first in the
in-place element write `_1[_0] = const 7_i8`, then in the read
`_0 = copy _1[_0]`. MiniRust evaluates the destination place first, so the
`Load` of the index operand `_0` fails the validity invariant before the
bounds check or the store happen; Anneal's projection finds `_0` `.uninit`
and faults. -/
def arrayUninitIdxI8 : CapturedMir where
  defPath := "witness::array_uninit_idx_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, arrI8_2Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (placeIdx 1 0) (.use (constI8 7))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeIdx 1 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArrayUninitIdx
  layouts := emptyLayoutTable
  allocations := []

theorem arrayUninitIdxI8_inFragment : inFragment arrayUninitIdxI8 = true := by decide

def arrayUninitIdxI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Array (.Int i8) 2)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Index (.Local (localName 1)) (.Load (.Local (localName 0))))
        (.Constant (.Int 7) (.Int i8)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Local (localName 1)) (.Load (.Local (localName 0)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arrayUninitIdxI8_translate :
    translateFn arrayUninitIdxI8 = some arrayUninitIdxI8Fn := rfl

def arrayUninitIdxS0 : MachineState := initMachineState arrayUninitIdxI8 [initArrI8_2]
def arrayUninitIdxMInit : Mach :=
  machineWithCtx ctxI8 arrayUninitIdxI8 arrayUninitIdxI8Fn
    arrayUninitIdxS0.frame.locals arrayUninitIdxI8Fn.start

theorem arrayUninitIdx_anneal_ub :
    ∃ tr u, Reaches (mirCallTree arrayUninitIdxI8 [initArrI8_2]) tr u ∧ FaultNow u :=
  faultsA_sound arrayUninitIdxI8 6 _ (by decide)

theorem arrayUninitIdx_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayUninitIdxMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayUninitIdx_anneal_ub
  exact mirCall_ub arrayUninitIdxI8_inFragment arrayUninitIdxI8_translate ctxI8
    (ctxI8_ok_arrayUninitIdx rfl) [initArrI8_2] (by decide)
    arrayUninitIdxMInit rfl rfl rfl hr hf

/-- The UB is the failed `Load` of the uninitialized index operand, not the
bounds check (`"access to out-of-bounds index"`). -/
theorem arrayUninitIdx_minirust_direct :
    Interp.steps 2 arrayUninitIdxMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-! ## Multi-byte elements (`[u32; 3]`): byte offset `index * elem_size` -/

def arrU32_3Ty : Ty := { kind := .array (.uint .u32) 3, layoutIdx := 0 }
def arrU32_3Decl : LocalDecl := { mutability := .mut, ty := arrU32_3Ty, debugName := none }

def arrU32_3Layout : TypeLayout :=
  { size := { bytes := 12 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiArrayU32Idx : FnAbi :=
  { args := [{ layout := arrU32_3Layout, mode := .direct },
             { layout := usizeLayout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- The callee's locals live at addresses `128` (`_0`), `256` (`_1`, twelve
bytes), and `384` (`_2`). -/
def ctxU32_3 : Ctx := { ctx0 with addrs := [128, 256, 384] }

theorem ctxU32_ok_arrayU32Idx {body : CapturedMir}
    (h : body.localDecls = [u32Decl, arrU32_3Decl, usizeDecl]) : CtxOk body ctxU32_3 where
  addrs := by
    intro i d hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of a function that writes
`const 0x04030201_u32` into `_1[_2]` of a `[u32; 3]` argument and returns
`_1[_2] + _1[0 of 3]`. -/
def arrayU32Idx : CapturedMir where
  defPath := "witness::array_u32_idx"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, arrU32_3Decl, usizeDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (placeIdx 1 2) (.use (constU32 0x04030201))),
        mkStmt (.assign (local_ 0)
          (.binaryOp .add (.copy (placeIdx 1 2)) (.copy (placeConstIdx 1 0 3 false))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArrayU32Idx
  layouts := emptyLayoutTable
  allocations := []

theorem arrayU32Idx_inFragment : inFragment arrayU32Idx = true := by decide

def arrayU32IdxFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Array (.Int u32) 3),
    (localName 2, .Int usizeIt)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Index (.Local (localName 1)) (.Load (.Local (localName 2))))
        (.Constant (.Int 0x04030201) (.Int u32)),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add)
          (.Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2)))))
          (.Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arrayU32Idx_translate : translateFn arrayU32Idx = some arrayU32IdxFn := rfl

def initArrU32_3 : Value := .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩]

/-- Index `_2 = 2usize`: `_1 = [10, 20, 0x04030201]`, returning
`0x04030201 + 10 = 0x0403020b`. -/
def arrayU32IdxOkS0 : MachineState :=
  initMachineState arrayU32Idx [initArrU32_3, .scalar ⟨2, 8⟩]
def arrayU32IdxOkMInit : Mach :=
  machineWithCtx ctxU32_3 arrayU32Idx arrayU32IdxFn arrayU32IdxOkS0.frame.locals
    arrayU32IdxFn.start

theorem arrayU32IdxOk_anneal_ret :
    ReachesRet (mirCallTree arrayU32Idx [initArrU32_3, .scalar ⟨2, 8⟩]) []
      (.normal (.scalar ⟨0x0403020b, 4⟩, arrayU32IdxOkS0.memory)) :=
  runA_sound arrayU32Idx 8 _ _ _ rfl

theorem arrayU32IdxOk_noUB :
    MirNoUBTree (mirCallTree arrayU32Idx [initArrU32_3, .scalar ⟨2, 8⟩]) :=
  runA_noUB arrayU32Idx 8 _ _ _ rfl

theorem arrayU32IdxOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n arrayU32IdxOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 0x0403020b } ∧
      m'.threads = [thread1 ctxU32_3 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret arrayU32Idx_inFragment arrayU32Idx_translate ctxU32_3
      (ctxU32_ok_arrayU32Idx rfl) [initArrU32_3, .scalar ⟨2, 8⟩] (by decide)
      arrayU32IdxOkMInit rfl rfl rfl arrayU32IdxOk_anneal_ret
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [arrayU32Idx] at hd; subst hd
  simp [retPtr, ctxU32_3, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxU32_3, ctx0] at hr; subst hr
  have hbits : bits = 0x0403020b := by
    simp [itOf, intTypeOf, intTyBytes, u32Decl, u32Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxU32_3, ctx0, itOf, intTypeOf, intTyBytes, u32Decl, u32Ty, u32]

theorem arrayU32IdxOk_minirust_direct :
    (Interp.steps 4 arrayU32IdxOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 0x0403020b }, [1]) := rfl

/-- Byte-level view of the in-place write: MiniRust's allocation `2` is `_1`'s
(after the caller's return allocation and `_0`'s). Before step `2` it holds
the little-endian bytes of `[10, 20, 30]`; step `2` (`_1[_2] = 0x04030201`
with `_2 = 2`) rewrites exactly bytes `8..12` (`2 * size_of::<u32>()`) to
`01 02 03 04`, leaving bytes `0..8` (elements `0` and `1`) unchanged. -/
theorem arrayU32IdxOk_minirust_inplace_bytes :
    [1, 2].map (fun k => (Interp.steps k arrayU32IdxOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[2]?).map (·.data))) =
      [some (some (scalarBytes u32 10 ++ scalarBytes u32 20 ++ scalarBytes u32 30)),
       some (some (scalarBytes u32 10 ++ scalarBytes u32 20 ++
         [.Init 1 none, .Init 2 none, .Init 3 none, .Init 4 none]))] := rfl

/-- Index `_2 = 3usize` (`3 >= 3`): out-of-bounds UB on the in-place write. -/
def arrayU32IdxOobS0 : MachineState :=
  initMachineState arrayU32Idx [initArrU32_3, .scalar ⟨3, 8⟩]
def arrayU32IdxOobMInit : Mach :=
  machineWithCtx ctxU32_3 arrayU32Idx arrayU32IdxFn arrayU32IdxOobS0.frame.locals
    arrayU32IdxFn.start

theorem arrayU32IdxOob_anneal_ub :
    ∃ tr u, Reaches (mirCallTree arrayU32Idx [initArrU32_3, .scalar ⟨3, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayU32Idx 6 _ (by decide)

theorem arrayU32IdxOob_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayU32IdxOobMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayU32IdxOob_anneal_ub
  exact mirCall_ub arrayU32Idx_inFragment arrayU32Idx_translate ctxU32_3
    (ctxU32_ok_arrayU32Idx rfl) [initArrU32_3, .scalar ⟨3, 8⟩] (by decide)
    arrayU32IdxOobMInit rfl rfl rfl hr hf

theorem arrayU32IdxOob_minirust_direct :
    Interp.steps 2 arrayU32IdxOobMInit = .error (.ub "access to out-of-bounds index") := rfl

/-! ## Out-of-bounds `ConstantIndex` (`fromEnd = false, offset >= count`), `PlaceMention` on an array local, and `Interp` representation checks -/

/-- MIR (`Runtime(PostCleanup)`) of a function that executes `PlaceMention(_1)`
on a `[i8; 2]` array local and then attempts to read `_1[2 of 2]`
(`ProjectionElem.constantIndex 2 2 false`, where `fromEnd = false` and
`offset = 2 >= 2`), raising out-of-bounds UB in both Anneal and MiniRust. -/
def arrayConstIdxOobI8 : CapturedMir where
  defPath := "witness::array_const_idx_oob_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, arrI8_2Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.placeMention (local_ 1)),
        mkStmt (.assign (local_ 0) (.use (.copy (placeConstIdx 1 2 2 false))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArrayUninitIdx
  layouts := emptyLayoutTable
  allocations := []

theorem arrayConstIdxOobI8_inFragment : inFragment arrayConstIdxOobI8 = true := by decide

def arrayConstIdxOobI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Array (.Int i8) 2)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .PlaceMention (.Local (localName 1)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Local (localName 1)) (.Constant (.Int 2) (.Int usizeIt))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arrayConstIdxOobI8_translate :
    translateFn arrayConstIdxOobI8 = some arrayConstIdxOobI8Fn := rfl

def arrayConstIdxOobS0 : MachineState := initMachineState arrayConstIdxOobI8 [initArrI8_2]
def arrayConstIdxOobMInit : Mach :=
  machineWithCtx ctxI8 arrayConstIdxOobI8 arrayConstIdxOobI8Fn
    arrayConstIdxOobS0.frame.locals arrayConstIdxOobI8Fn.start

theorem arrayConstIdxOob_anneal_ub :
    ∃ tr u, Reaches (mirCallTree arrayConstIdxOobI8 [initArrI8_2]) tr u ∧ FaultNow u :=
  faultsA_sound arrayConstIdxOobI8 6 _ (by decide)

theorem arrayConstIdxOob_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayConstIdxOobMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayConstIdxOob_anneal_ub
  exact mirCall_ub arrayConstIdxOobI8_inFragment arrayConstIdxOobI8_translate ctxI8
    (ctxI8_ok_arrayUninitIdx rfl) [initArrI8_2] (by decide)
    arrayConstIdxOobMInit rfl rfl rfl hr hf

theorem arrayConstIdxOob_minirust_direct :
    Interp.steps 3 arrayConstIdxOobMInit = .error (.ub "access to out-of-bounds index") := rfl

/-- `Size::ZERO * -1 = Size::ZERO` (`Size::from_bytes(0 * -1).unwrap()`), whereas
multiplying a non-zero `Size` by `-1` panics with a negative byte count. -/
theorem sizeMulInt_zero_neg :
    Size.mulInt ⟨0⟩ (-1) = .ok ⟨0⟩ ∧
    Size.mulInt ⟨1⟩ (-1) = .error (.specPanic "Size * Int: negative byte count") :=
  ⟨rfl, rfl⟩

/-- `Type.encode` on `Type::Array` checks `assert_eq!(values.len(), count)`
before encoding elements or computing `elem.layout()` (so an empty 0-length
array succeeds without querying `elem.layout()`), and `Type.decode` on
`Type::Array` short-circuits left-to-right via `tryMapM` on the first `.Uninit`
element chunk. -/
theorem array_encode_decode_edge_cases :
    Type.encode (.Array (.Slice (.Int i8)) 2) (.Tuple []) =
      .error (.specPanic "encode: Type::Array length mismatch") ∧
    Type.encode (.Array (.Slice (.Int i8)) 0) (.Tuple []) = .ok [] ∧
    Type.decode (.Array (.Int i8) 2) [.Uninit, .Init 5 none] = .ok none ∧
    (tryMapM (fun x : Nat =>
      if x = 0 then (.ok none : Interp (Option Val))
      else .error (.specPanic "unreachable")) [0, 1] : Interp (Option (List Val))) =
      .ok none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Projected array operands across `SwitchInt`/`Repeat`/`Aggregate`/`UnaryOp`/`Cast`, faulting array rvalues, and faulting in-place write RHS -/

def fnAbiArrayCompose : FnAbi :=
  { args := [{ layout := arrI8_2Layout, mode := .direct },
             { layout := usizeLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_arrayCompose {body : CapturedMir}
    (h : body.localDecls = [i8Decl, arrI8_2Decl, usizeDecl]) : CtxOk body ctxI8_3 where
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

/-- MIR (`Runtime(PostCleanup)`) of a function exercising projected array
element operands (`copy _1[proj]`) across `SwitchInt`, `Repeat`,
`Aggregate(Array)`, `UnaryOp(Neg)`, and `Cast(IntToInt)`, as well as the UB
branches of `evalStatement_assign_array` (`Aggregate` and `Repeat` with a
faulting operand) and `evalStatement_assign_index` (in-place indexed write with
a faulting RHS, and when both destination projection and RHS fault):
* `bb0`: `SwitchInt(copy _1[_2])` branches on `10 -> bb1`, `20 -> bb2`,
  `30 -> bb3`, `40 -> bb4`, `otherwise -> bb5` (and faults in `bb0` if `_2 >= 2`);
* `bb1`: `_1 = Repeat(copy _1[_2], 2)`,
  `_1 = Aggregate(Array(i8), [copy _1[0 of 2], const 20i8])`,
  `_1[_2] = UnaryOp(Neg, copy _1[-1 of 2])`,
  `_0 = Cast(IntToInt, copy _1[0 of 2], i8Ty)`, then `Return`;
* `bb2`: `_1 = Aggregate(Array(i8), [copy _1[0 of 2], copy _0])` (faults on
  uninitialized `_0` in element `1`);
* `bb3`: `_1 = Repeat(copy _1[2 of 2], 2)` (faults on out-of-bounds
  `ConstantIndex` `2 >= 2`);
* `bb4`: `_1[0 of 2] = BinaryOp(Div, copy _1[0 of 2], const 0i8)` (valid
  destination index `0`, faulting RHS division by zero);
* `bb5`: `_1[2 of 2] = BinaryOp(Div, copy _1[0 of 2], const 0i8)` (both
  destination projection `2 >= 2` and RHS division by zero fault). -/
def arrayComposeI8 : CapturedMir where
  defPath := "witness::array_compose_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, arrI8_2Decl, usizeDecl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (placeIdx 1 2))
        { branches := [(10, 1), (20, 2), (30, 3), (40, 4)], otherwise := 5 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.repeat (.copy (placeIdx 1 2)) 2)),
        mkStmt (.assign (local_ 1)
          (.aggregate (.array i8Ty) [.copy (placeConstIdx 1 0 2 false), constI8 20])),
        mkStmt (.assign (placeIdx 1 2)
          (.unaryOp .neg (.copy (placeConstIdx 1 1 2 true)))),
        mkStmt (.assign (local_ 0)
          (.cast .intToInt (.copy (placeConstIdx 1 0 2 false)) i8Ty))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1)
          (.aggregate (.array i8Ty) [.copy (placeConstIdx 1 0 2 false), .copy (local_ 0)]))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.repeat (.copy (placeConstIdx 1 2 2 false)) 2))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (placeConstIdx 1 0 2 false)
          (.binaryOp .div (.copy (placeConstIdx 1 0 2 false)) (constI8 0)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (placeConstIdx 1 2 2 false)
          (.binaryOp .div (.copy (placeConstIdx 1 0 2 false)) (constI8 0)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArrayCompose
  layouts := emptyLayoutTable
  allocations := []

theorem arrayComposeI8_inFragment : inFragment arrayComposeI8 = true := by decide

def arrayComposeI8Fn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int i8),
    (localName 1, .Array (.Int i8) 2),
    (localName 2, .Int usizeIt)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[],
      .Switch (.Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2)))))
        ⟨[(10, bbName 1), (20, bbName 2), (30, bbName 3), (40, bbName 4)]⟩ (bbName 5),
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2)))),
          .Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2))))]
          (.Array (.Int i8) 2)),
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))),
          .Constant (.Int 20) (.Int i8)] (.Array (.Int i8) 2)),
      .Assign (.Index (.Local (localName 1)) (.Load (.Local (localName 2))))
        (.UnOp (.Int .Neg)
          (.Load (.Index (.Local (localName 1)) (.Constant (.Int 1) (.Int usizeIt))))),
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt i8))
          (.Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt)))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))),
          .Load (.Local (localName 0))] (.Array (.Int i8) 2))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Index (.Local (localName 1)) (.Constant (.Int 2) (.Int usizeIt))),
          .Load (.Index (.Local (localName 1)) (.Constant (.Int 2) (.Int usizeIt)))]
          (.Array (.Int i8) 2))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[
      .Assign (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt)))
        (.BinOp (.Int .Div)
          (.Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))))
          (.Constant (.Int 0) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 5, ⟨[
      .Assign (.Index (.Local (localName 1)) (.Constant (.Int 2) (.Int usizeIt)))
        (.BinOp (.Int .Div)
          (.Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))))
          (.Constant (.Int 0) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 6, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 6
  implicit_writes := true

theorem arrayComposeI8_translate : translateFn arrayComposeI8 = some arrayComposeI8Fn := rfl

def initArrCompose10_20 : Value := .aggregate 0 [.scalar ⟨10, 1⟩, .scalar ⟨20, 1⟩]

/-- `_1 = [10i8, 20i8]`, `_2 = 0usize`: switches on `_1[0] = 10` to `bb1`,
repeats `_1[0]` into `[10, 10]`, rebuilds `[10, 20]`, negates `_1[-1 of 2] = 20`
into `_1[0] = -20i8` (bits `236`), casts `_1[0]` to `i8`, and returns `-20i8`. -/
def arrayComposeOkS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose10_20, .scalar ⟨0, 8⟩]
def arrayComposeOkMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeOkS0.frame.locals arrayComposeI8Fn.start

def arrayComposeOkTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 10))), PUnit.unit⟩]

theorem arrayComposeOk_anneal_ret :
    ReachesRet (mirCallTree arrayComposeI8 [initArrCompose10_20, .scalar ⟨0, 8⟩])
      arrayComposeOkTrace (.normal (.scalar ⟨236, 1⟩, arrayComposeOkS0.memory)) :=
  runA_sound arrayComposeI8 12 _ _ _ rfl

theorem arrayComposeOk_noUB :
    MirNoUBTree (mirCallTree arrayComposeI8 [initArrCompose10_20, .scalar ⟨0, 8⟩]) :=
  runA_noUB arrayComposeI8 12 _ _ _ rfl

theorem arrayComposeOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n arrayComposeOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 236 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
      (ctxI8_ok_arrayCompose rfl) [initArrCompose10_20, .scalar ⟨0, 8⟩] (by decide)
      arrayComposeOkMInit rfl rfl rfl arrayComposeOk_anneal_ret
  obtain ⟨bits, r, a, d, hd, hv, hp, hr, hthr, hallocs⟩ := hret
  simp [arrayComposeI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  have hbits : bits = 236 := by
    simp [itOf, intTypeOf, intTyBytes, i8Decl, i8Ty] at hv; omega
  subst hbits
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]
  simp [ctxI8_3, itOf, intTypeOf, intTyBytes, i8Decl, i8Ty, i8]

theorem arrayComposeOk_minirust_direct :
    (Interp.steps 7 arrayComposeOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 236 }, [1]) := rfl

/-- `_1 = [10i8, 20i8]`, `_2 = 1usize`: switches on `_1[1] = 20` to `bb2` and
faults when `Aggregate(Array)` evaluates its second operand `copy _0` while `_0`
is `.uninit` (`evalStatement_assign_array` UB branch). -/
def arrayComposeAggUbS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose10_20, .scalar ⟨1, 8⟩]
def arrayComposeAggUbMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeAggUbS0.frame.locals arrayComposeI8Fn.start

theorem arrayComposeAggUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arrayComposeI8 [initArrCompose10_20, .scalar ⟨1, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayComposeI8 8 _ (by decide)

theorem arrayComposeAggUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayComposeAggUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayComposeAggUb_anneal_ub
  exact mirCall_ub arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
    (ctxI8_ok_arrayCompose rfl) [initArrCompose10_20, .scalar ⟨1, 8⟩] (by decide)
    arrayComposeAggUbMInit rfl rfl rfl hr hf

theorem arrayComposeAggUb_minirust_direct :
    Interp.steps 3 arrayComposeAggUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- `_1 = [30i8, 20i8]`, `_2 = 0usize`: switches on `_1[0] = 30` to `bb3` and
faults when `Repeat(copy _1[2 of 2], 2)` evaluates its out-of-bounds
`ConstantIndex` operand (`evalStatement_assign_array` UB branch). -/
def initArrCompose30_20 : Value := .aggregate 0 [.scalar ⟨30, 1⟩, .scalar ⟨20, 1⟩]

def arrayComposeRepeatUbS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose30_20, .scalar ⟨0, 8⟩]
def arrayComposeRepeatUbMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeRepeatUbS0.frame.locals arrayComposeI8Fn.start

theorem arrayComposeRepeatUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arrayComposeI8 [initArrCompose30_20, .scalar ⟨0, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayComposeI8 8 _ (by decide)

theorem arrayComposeRepeatUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayComposeRepeatUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayComposeRepeatUb_anneal_ub
  exact mirCall_ub arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
    (ctxI8_ok_arrayCompose rfl) [initArrCompose30_20, .scalar ⟨0, 8⟩] (by decide)
    arrayComposeRepeatUbMInit rfl rfl rfl hr hf

theorem arrayComposeRepeatUb_minirust_direct :
    Interp.steps 3 arrayComposeRepeatUbMInit =
      .error (.ub "access to out-of-bounds index") := rfl

/-- `_1 = [40i8, 20i8]`, `_2 = 0usize`: switches on `_1[0] = 40` to `bb4` and
faults on the RHS division by zero in `_1[0 of 2] = Div(copy _1[0 of 2], 0i8)`
while the destination projection `_1[0 of 2]` is in-bounds (`projIdx = some 0`,
`rvBits = none` in `evalStatement_assign_index`). -/
def initArrCompose40_20 : Value := .aggregate 0 [.scalar ⟨40, 1⟩, .scalar ⟨20, 1⟩]

def arrayComposeRhsUbS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose40_20, .scalar ⟨0, 8⟩]
def arrayComposeRhsUbMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeRhsUbS0.frame.locals arrayComposeI8Fn.start

theorem arrayComposeRhsUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arrayComposeI8 [initArrCompose40_20, .scalar ⟨0, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayComposeI8 8 _ (by decide)

theorem arrayComposeRhsUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayComposeRhsUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayComposeRhsUb_anneal_ub
  exact mirCall_ub arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
    (ctxI8_ok_arrayCompose rfl) [initArrCompose40_20, .scalar ⟨0, 8⟩] (by decide)
    arrayComposeRhsUbMInit rfl rfl rfl hr hf

theorem arrayComposeRhsUb_minirust_direct :
    Interp.steps 3 arrayComposeRhsUbMInit = .error (.ub "division by zero") := rfl

/-- `_1 = [50i8, 20i8]`, `_2 = 0usize`: takes `otherwise` (`bb5`) where both the
destination projection `_1[2 of 2]` (`2 >= 2`) and the RHS `Div(..., 0i8)` fault
(`projIdx = none` and `rvBits = none`). Anneal faults on `evalRvalue` first and
MiniRust faults on `eval_place(destination)` first, so both raise UB. -/
def initArrCompose50_20 : Value := .aggregate 0 [.scalar ⟨50, 1⟩, .scalar ⟨20, 1⟩]

def arrayComposeBothUbS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose50_20, .scalar ⟨0, 8⟩]
def arrayComposeBothUbMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeBothUbS0.frame.locals arrayComposeI8Fn.start

theorem arrayComposeBothUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arrayComposeI8 [initArrCompose50_20, .scalar ⟨0, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayComposeI8 8 _ (by decide)

theorem arrayComposeBothUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayComposeBothUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayComposeBothUb_anneal_ub
  exact mirCall_ub arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
    (ctxI8_ok_arrayCompose rfl) [initArrCompose50_20, .scalar ⟨0, 8⟩] (by decide)
    arrayComposeBothUbMInit rfl rfl rfl hr hf

theorem arrayComposeBothUb_minirust_direct :
    Interp.steps 3 arrayComposeBothUbMInit =
      .error (.ub "access to out-of-bounds index") := rfl

/-- `_1 = [10i8, 20i8]`, `_2 = 2usize`: faults in `bb0` when `SwitchInt`
evaluates its out-of-bounds projected discriminant `copy _1[_2]` (`2 >= 2`). -/
def arrayComposeSwitchOobUbS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose10_20, .scalar ⟨2, 8⟩]
def arrayComposeSwitchOobUbMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeSwitchOobUbS0.frame.locals arrayComposeI8Fn.start

theorem arrayComposeSwitchOobUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arrayComposeI8 [initArrCompose10_20, .scalar ⟨2, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayComposeI8 6 _ (by decide)

theorem arrayComposeSwitchOobUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayComposeSwitchOobUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayComposeSwitchOobUb_anneal_ub
  exact mirCall_ub arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
    (ctxI8_ok_arrayCompose rfl) [initArrCompose10_20, .scalar ⟨2, 8⟩] (by decide)
    arrayComposeSwitchOobUbMInit rfl rfl rfl hr hf

theorem arrayComposeSwitchOobUb_minirust_direct :
    Interp.steps 2 arrayComposeSwitchOobUbMInit =
      .error (.ub "access to out-of-bounds index") := rfl

end MiniRustSpec.Correspondence.Witness
