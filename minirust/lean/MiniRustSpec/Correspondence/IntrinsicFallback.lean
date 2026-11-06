/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Witness

/-!
# Intrinsic calls resolved to MIR fallback bodies

Anneal resolves a `TerminatorKind::Call` through `callees` by the callee's
`DefPath` (`MirSemantics.findCallee?`), whatever that path names. A call to an
intrinsic whose MIR body is available in `callees` (a fallback body) is
therefore an ordinary direct call, and the `MR-4.1` multi-function results
(`progInFragment`, `translateProg`, and `mirCallWithCallees_ret` in
`Correspondence/Run.lean`) apply to it unchanged. This module checks that claim
for seven intrinsics and for two `u32` library methods, `wrapping_shl` and
`wrapping_shr`. Each callee body is a hand-written algorithm for its
operation, expressed in the fragment's MIR; none is captured or quoted from
`core`:

| Operation | Callee `DefPath` | Algorithm |
| :--- | :--- | :--- |
| `ctlz::<u8>` | `core::intrinsics::ctlz` | binary search (`switchInt`) |
| `cttz::<u8>` | `core::intrinsics::cttz` | shift loop (back edge) |
| `bswap::<u32>` | `core::intrinsics::bswap` | shifts and masks |
| `bitreverse::<u8>` | `core::intrinsics::bitreverse` | nibble/pair/bit swaps |
| `saturating_add::<u8>` | `core::intrinsics::saturating_add` | `AddWithOverflow` |
| `saturating_sub::<i8>` | `core::intrinsics::saturating_sub` | `SubWithOverflow`, `Lt` |
| `u32::wrapping_shl` | `core::num::<impl u32>::wrapping_shl` | `rhs & 31`, `Shl` |
| `u32::wrapping_shr` | `core::num::<impl u32>::wrapping_shr` | `rhs & 31`, `Shr` |
| `black_box::<u32>` | `core::intrinsics::black_box` | identity |

Every callee has the Rust calling convention (`CallConv.rust`): the fragment
requires a convention that `translateCallConv` accepts, and it rejects
`CallConv.rustIntrinsic`. Since `findCallee?` compares `DefPath`s only, each
program contains a single monomorphic instance of its callee; the generic
arguments recorded in the call's `FnDef` type document that instance but are
never consulted.

This is a statement about Anneal's capture model and about `translateProg`,
not about upstream `minimize`. `minimize`'s `translate_call`
(`tooling/minimize/src/bb.rs`) resolves a call to
`core::intrinsics::{ctlz, cttz, bswap, bitreverse, saturating_add,
saturating_sub, black_box}` to `InstanceKind::Intrinsic` and hands it to
`translate_rs_intrinsic`, whose catch-all arm is a `span_bug!` ("unsupported
Rust intrinsic") for all seven. `translateProg` instead lowers such a call
like any other direct call, to a `Terminator::Call` of the callee's function
pointer, which is what `minimize` does for the ordinary library functions
`wrapping_shl` and `wrapping_shr`. For the seven intrinsics, the witnesses
below therefore relate Anneal to the MiniRust program that calls the fallback
body, the program a backend without a native lowering runs, and not to any
output of `minimize`.

For each operation, a caller entry calls the callee once and returns its
result, and the module proves:

* `progInFragment caller [callee] = true` (`fb*_inFragment`), and the
  translated program and entry function spelled out (`fb*_translate`,
  `fb*Caller_translateInProg`);
* functional correctness against a pure Lean reference (`fb*Spec`): Anneal's
  `mirCallTreeWithCallees caller args [callee]` returns the specified scalar,
  and no execution prefix reaches UB (`fbReturns`). The `fb*_check` theorems
  evaluate `runA` in the kernel (`decide +kernel`, never `native_decide`), and
  `fbRunsTo_sound` turns each check into `runA_sound` and `runA_noUB` facts.
  The checks are exhaustive over all 256 inputs for the unary `u8` operations
  (`ctlz`, `cttz`, `bitreverse`); for the binary saturating operations they
  cover full 256-input rows (one for `saturating_add`; one row and two columns
  for `saturating_sub`) plus a 144-pair grid of boundary values; for the
  shifts, all shift amounts `s < 64` for one value plus sampled pairs; and for
  `bswap`, sampled `u32` inputs. For `black_box`, the kernel reduces `runA`
  with a variable argument (`fbBlackBox_runA`), which covers every `u32` input;
* MiniRust correspondence: by `mirCallWithCallees_ret`, the translated MiniRust
  program, started at the translated entry, returns the bytes of the specified
  result into the caller's return place for every checked input
  (`fb*_minirust_*`); and one direct kernel run of `Interp.steps` per
  operation (`fb*_minirust_direct`) agrees with that conclusion.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence.Witness

/-! ## Shared building blocks -/

/-- An `i32` constant. The fallback bodies use `i32` shift amounts, the type
Rust gives an unsuffixed integer literal on the right of `<<` or `>>`. -/
def fbConstI32 (n : Nat) : Operand := .constant { ty := i32Ty, val := .scalar (.int ⟨n, 4⟩) }

def fbU8BoolTupleTy : Ty := { kind := .tuple [.uint .u8, .bool], layoutIdx := 0 }
def fbU8BoolTupleDecl : LocalDecl :=
  { mutability := .mut, ty := fbU8BoolTupleTy, debugName := none }
def fbField0U8 (i : Nat) : Place := { local_ := i, projection := [.field 0 u8TyW] }

/-- A Rust-ABI `FnAbi` passing every argument directly. Like the other ABI
layouts in `Witness`, the fragment never reads the layouts; `i8Layout` stands
for every one-byte primitive. -/
def fbAbi (args : List TypeLayout) (ret : TypeLayout) : FnAbi :=
  { args := args.map fun l => { layout := l, mode := .direct },
    ret := { layout := ret, mode := .direct }, conv := .rust, canUnwind := false }

/-- Direct-call operand for the monomorphic instance `dp::<tys>`
(`TyKind.fnDef dp tys` with `MirConstVal.zeroSized`). -/
def fbFnOp (dp : String) (tys : List RigidTy) : Operand :=
  .constant { ty := { kind := .fnDef dp tys, layoutIdx := 0 }, val := .zeroSized }

/-- MIR (`Runtime(PostCleanup)`) of a caller `dp` with locals `decls`
(`_0` the return place, `_1 .. _k` the parameters) that returns
`calleeDp::<tys>(_1, .., _k)`:
```text
bb0: _0 = calleeDp::<tys>(copy _1, .., copy _k) -> [return: bb1, unwind unreachable]
bb1: return
```
No fallback body below can unwind, so the `UnwindAction::Unreachable` edge is
never taken. -/
def fbCaller (dp calleeDp : String) (tys : List RigidTy) (decls : List LocalDecl)
    (abi : FnAbi) : CapturedMir where
  defPath := dp
  phase := .runtimePostCleanup
  role := .subject
  argCount := decls.length - 1
  localDecls := decls
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fbFnOp calleeDp tys)
        ((List.range (decls.length - 1)).map fun i => .copy (local_ (i + 1)))
        (local_ 0) (some 1) .unreachable),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := abi
  layouts := emptyLayoutTable
  allocations := []

/-- The MiniRust function that `translateFnInProg` produces for an `fbCaller`
body whose locals translate to `locals`: the call passes every parameter
`ArgumentExpr::ByValue` to `fnName 1`, `bbName 2` is `minimize`'s init block
(no temporaries), and `bbName 3` is the synthesized cleanup block of the
`Unreachable` unwind edge. -/
def fbCallerFn (locals : List Gen.Type) : Gen.Function where
  locals := ⟨(List.range locals.length).zip locals |>.map fun (i, t) => (localName i, t)⟩
  args := (List.range (locals.length - 1)).map fun k => localName (k + 1)
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Call (fnPtrExpr (fnName 1)) .Rust
      ((List.range (locals.length - 1)).map fun k => .ByValue (.Load (.Local (localName (k + 1)))))
      (.Local (localName 0)) (some (bbName 1)) (some (bbName 3)), .Regular⟩),
    (bbName 1, ⟨[], .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩),
    (bbName 3, ⟨[], .Unreachable, .Cleanup⟩)]⟩
  start := bbName 2
  implicit_writes := true

/-- The translated program of an entry and a single callee: `fnName 0` is the
entry, `fnName 1` the callee, and `fnName 2` `minimize`'s start wrapper. -/
def fbProg (callerFn calleeFn : Gen.Function) : Gen.Program where
  functions := ⟨[(fnName 0, callerFn), (fnName 1, calleeFn), (fnName 2, mkStartFn 0)]⟩
  start := fnName 2
  globals := ⟨[]⟩
  vtables := ⟨[]⟩
  traits := ⟨[]⟩

/-- An external caller holding a `u8` return place in its own `_0`. -/
def fbCallerFnU8 : Gen.Function where
  locals := ⟨[(localName 0, .Int u8)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true

def fbCallerFrameU8 : Frame :=
  { func := fbCallerFnU8, locals := ⟨[(localName 0, retPtr)]⟩, stack_pop_action := .BottomOfStack,
    next_block := bbName 0, next_stmt := 0, extra := () }

/-- Where the external caller allocated the entry's `_0 .. _argCount`. -/
def fbAddrs : List Int := [128, 256, 384]

/-- Root contexts for entries returning `u32` (return place `retAlloc`),
`u8`, and `i8` (both with the one-byte return place `retAllocI8`). -/
def fbCtxU32 : Ctx := ctxWithFns callerFrame retAlloc 2 fbAddrs
def fbCtxU8 : Ctx := ctxWithFns fbCallerFrameU8 retAllocI8 2 fbAddrs
def fbCtxI8 : Ctx := ctxWithFns callerFrameI8 retAllocI8 2 fbAddrs

theorem fbCtxU32_ok_u8 {body : CapturedMir} (h : body.localDecls = [u32Decl, u8Decl]) :
    CtxOk body fbCtxU32 where
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

theorem fbCtxU32_ok_u32 {body : CapturedMir} (h : body.localDecls = [u32Decl, u32Decl]) :
    CtxOk body fbCtxU32 where
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

theorem fbCtxU32_ok_u32u32 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, u32Decl, u32Decl]) : CtxOk body fbCtxU32 where
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

theorem fbCtxU8_ok_u8 {body : CapturedMir} (h : body.localDecls = [u8Decl, u8Decl]) :
    CtxOk body fbCtxU8 where
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

theorem fbCtxU8_ok_u8u8 {body : CapturedMir} (h : body.localDecls = [u8Decl, u8Decl, u8Decl]) :
    CtxOk body fbCtxU8 where
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

theorem fbCtxI8_ok_i8i8 {body : CapturedMir} (h : body.localDecls = [i8Decl, i8Decl, i8Decl]) :
    CtxOk body fbCtxI8 where
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

/-- The MiniRust machine that runs the translated `entry` (with `callee` as
`fnName 1`) on `args` from its start block under root context `ctx`. -/
def fbMInit (ctx : Ctx) (prog : Gen.Program) (entry callee : CapturedMir) (fEntry : Gen.Function)
    (args : List Value) : Mach :=
  multiMachineWithCtx ctx prog 2 entry fEntry
    (initMachineStateWithCallees entry args [callee]).frame.locals fEntry.start

/-- The branch observation that `switchInt` emits for scrutinee bits `t`. -/
def fbEv (t : Nat) : Event MirEffect := ⟨.inr (.inl (.emit (.event t))), PUnit.unit⟩

/-! ### From kernel-evaluated runs to Anneal and MiniRust facts -/

/-- Anneal's multi-function semantics of `entry` applied to `args`, resolving
calls through `callees`, returns the scalar `⟨bits, size⟩` along some trace of
branch observations, and no execution prefix reaches UB. -/
def fbReturns (entry : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (bits size : Nat) : Prop :=
  (∃ tr mem, ReachesRet (mirCallTreeWithCallees entry args callees) tr
    (.normal (.scalar ⟨bits, size⟩, mem))) ∧
  MirNoUBTree (mirCallTreeWithCallees entry args callees)

/-- A kernel-evaluable test that `args` are well typed for `entry` (`argsOk`)
and that `runA`, which runs Anneal's step function for at most `fuel` steps,
returns the scalar `⟨bits, size⟩` from `entry` applied to `args` with
`callees`. -/
def fbRunsTo (entry : CapturedMir) (callees : List CapturedMir) (fuel : Nat) (args : List Value)
    (bits size : Nat) : Bool :=
  argsOk entry args &&
  match runA entry fuel (initMachineStateWithCallees entry args callees) with
  | some (_, .normal (.scalar sc, _)) => sc.bits == bits && sc.sizeBytes == size
  | _ => false

/-- A passing `fbRunsTo` check yields `argsOk` and, by `runA_sound` and
`runA_noUB`, `fbReturns`. -/
theorem fbRunsTo_sound {entry : CapturedMir} {callees : List CapturedMir} {fuel : Nat}
    {args : List Value} {bits size : Nat} (h : fbRunsTo entry callees fuel args bits size = true) :
    argsOk entry args = true ∧ fbReturns entry callees args bits size := by
  unfold fbRunsTo at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hargs, h⟩ := h
  refine ⟨hargs, ?_⟩
  split at h
  · rename_i tr sc mem hrun
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
    obtain ⟨hb, hs⟩ := h
    have hsc : sc = ⟨bits, size⟩ := by cases sc; simp_all
    subst hsc
    exact ⟨⟨tr, mem, runA_sound entry fuel _ _ _ hrun⟩, runA_noUB entry fuel _ _ _ hrun⟩
  · exact absurd h Bool.false_ne_true

theorem fb_forall_lt_of_all {p : Nat → Bool} {n : Nat} (h : (List.range n).all p = true)
    (a : Nat) (ha : a < n) : p a = true :=
  List.all_eq_true.mp h a (List.mem_range.mpr ha)

theorem fb_forall_mem_of_all {α : Type} {p : α → Bool} {xs : List α} (h : xs.all p = true)
    (a : α) (ha : a ∈ xs) : p a = true :=
  List.all_eq_true.mp h a ha

/-- After finitely many steps from `m`, MiniRust reaches a machine whose
allocation `0` is `retA` holding `bytes` and whose only thread holds just
`caller`, resumed at `bbName 7`. For `m` running a translated entry under
`ctxWithFns caller retA 2 addrs`, this is the entry's root return into the
caller's return place. -/
def fbMiniRustRet (m : Mach) (caller : Frame) (retA : Gen.Allocation) (addrs : List Int)
    (bytes : List Byte) : Prop :=
  ∃ (n : Nat) (m' : Mach), Interp.steps n m = .ok m' ∧
    m'.mem.memory.allocations[0]? = some { retA with data := bytes } ∧
    m'.threads = [thread1 (ctxWithFns caller retA 2 addrs)
      [{ caller with next_block := bbName 7, next_stmt := 0 }]]

/-- `ReturnRel` under a `ctxWithFns` root context pins the caller's return
place (allocation `0`) and the remaining caller frame. -/
theorem fb_returnRel_alloc {entry : CapturedMir} {d : LocalDecl} {caller : Frame}
    {retA : Gen.Allocation} {nFns : Nat} {addrs : List Int} {s : MachineState} {v : Value}
    {m : Mach} (hd : entry.localDecls[0]? = some d)
    (h : ReturnRel entry (ctxWithFns caller retA nFns addrs) s v m) :
    m.mem.memory.allocations[0]? = some { retA with data := declSlotData d (.init v) } ∧
    m.threads = [thread1 (ctxWithFns caller retA nFns addrs)
      [{ caller with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨r, a, d', R, hd', _hv, hp, hr, hthr, hallocs, _hR⟩ := h
  rw [hd] at hd'
  cases hd'
  simp [retPtr, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxWithFns] at hr
  subst hr
  exact ⟨by rw [hallocs]; rfl, hthr⟩

/-- The `callerCallee20_minirust_ret` pattern for an entry with one callee: an
Anneal return of `v` (`ReachesRet`) becomes, by `mirCallWithCallees_ret`, a
MiniRust return of `v`'s bytes into the caller's return place. -/
theorem fb_minirust_ret {entry callee : CapturedMir} {prog : Gen.Program} {fEntry : Gen.Function}
    {caller : Frame} {retA : Gen.Allocation} {addrs : List Int} {d : LocalDecl}
    (hfrag : progInFragment entry [callee] = true)
    (hprog : translateProg entry [callee] = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry [callee]) entry = some fEntry)
    (hctx : CtxOk entry (ctxWithFns caller retA 2 addrs))
    (hd : entry.localDecls[0]? = some d)
    {args : List Value} (hargs : argsOk entry args = true)
    {tr : List (Event MirEffect)} {v : Value} {mem : MirSemantics.Memory}
    (hret : ReachesRet (mirCallTreeWithCallees entry args [callee]) tr (.normal (v, mem))) :
    fbMiniRustRet (fbMInit (ctxWithFns caller retA 2 addrs) prog entry callee fEntry args)
      caller retA addrs (declSlotData d (.init v)) := by
  obtain ⟨n, s', m', hsteps, hrel⟩ :=
    mirCallWithCallees_ret hfrag hprog hfEntry _ hctx args hargs
      (fbMInit (ctxWithFns caller retA 2 addrs) prog entry callee fEntry args)
      (progEnvOk_fnPtrMap (baseOff := 1) (n := 2) rfl rfl (Nat.le_refl 2)) rfl rfl rfl hret
  exact ⟨n, m', hsteps, fb_returnRel_alloc hd hrel⟩

/-- A passing `fbRunsTo` check, transferred to MiniRust by `fb_minirust_ret`. -/
theorem fb_minirust_of_runsTo {entry callee : CapturedMir} {prog : Gen.Program}
    {fEntry : Gen.Function} {caller : Frame} {retA : Gen.Allocation} {addrs : List Int}
    {d : LocalDecl}
    (hfrag : progInFragment entry [callee] = true)
    (hprog : translateProg entry [callee] = some prog)
    (hfEntry : translateFnInProg (fnNameMap entry [callee]) entry = some fEntry)
    (hctx : CtxOk entry (ctxWithFns caller retA 2 addrs))
    (hd : entry.localDecls[0]? = some d)
    {fuel : Nat} {args : List Value} {bits size : Nat}
    (h : fbRunsTo entry [callee] fuel args bits size = true) :
    fbMiniRustRet (fbMInit (ctxWithFns caller retA 2 addrs) prog entry callee fEntry args)
      caller retA addrs (declSlotData d (.init (.scalar ⟨bits, size⟩))) := by
  obtain ⟨hargs, ⟨tr, mem, hret⟩, _⟩ := fbRunsTo_sound h
  exact fb_minirust_ret hfrag hprog hfEntry hctx hd hargs hret

/-! ## `ctlz::<u8>` -/

/-- `ctlz::<u8>` (`core::intrinsics::ctlz`), the number of leading zero bits
of `x` as a `u32`. The fallback body binary-searches for the highest set bit:
```rust
fn ctlz(mut x: u8) -> u32 {
    let mut n: u32 = 8;
    let mut y = x >> 4;
    if y != 0 { n -= 4; x = y; }
    y = x >> 2;
    if y != 0 { n -= 2; x = y; }
    y = x >> 1;
    if y != 0 { return n - 2; }
    n - x as u32
}
```
Its MIR keeps `n` in the return place `_0` and `y` in `_2`, and switches on
`y` directly:
```text
bb0: StorageLive(_2); _0 = const 8_u32; _2 = Shr(copy _1, const 4_i32);
     switchInt(copy _2) -> [0: bb2, otherwise: bb1]
bb1: _0 = Sub(copy _0, const 4_u32); _1 = copy _2; goto -> bb2
bb2: _2 = Shr(copy _1, const 2_i32); switchInt(copy _2) -> [0: bb4, otherwise: bb3]
bb3: _0 = Sub(copy _0, const 2_u32); _1 = copy _2; goto -> bb4
bb4: _2 = Shr(copy _1, const 1_i32); switchInt(copy _2) -> [0: bb6, otherwise: bb5]
bb5: StorageDead(_2); _0 = Sub(copy _0, const 2_u32); return
bb6: StorageDead(_2); StorageLive(_3); _3 = copy _1 as u32 (IntToInt);
     _0 = Sub(copy _0, move _3); StorageDead(_3); return
``` -/
def fbCtlzCallee : CapturedMir where
  defPath := "core::intrinsics::ctlz"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u8Decl, u8Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 0) (.use (constU32 8))),
        mkStmt (.assign (local_ 2) (.binaryOp .shr (.copy (local_ 1)) (fbConstI32 4)))],
      terminator := mkTerm (.switchInt (.copy (local_ 2)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 0)) (constU32 4))),
        mkStmt (.assign (local_ 1) (.use (.copy (local_ 2))))],
      terminator := mkTerm (.goto 2), isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2) (.binaryOp .shr (.copy (local_ 1)) (fbConstI32 2)))],
      terminator := mkTerm (.switchInt (.copy (local_ 2)) { branches := [(0, 4)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 0)) (constU32 2))),
        mkStmt (.assign (local_ 1) (.use (.copy (local_ 2))))],
      terminator := mkTerm (.goto 4), isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2) (.binaryOp .shr (.copy (local_ 1)) (fbConstI32 1)))],
      terminator := mkTerm (.switchInt (.copy (local_ 2)) { branches := [(0, 6)], otherwise := 5 }),
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 2),
        mkStmt (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 0)) (constU32 2)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.storageDead 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.cast .intToInt (.copy (local_ 1)) u32Ty)),
        mkStmt (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 0)) (.move (local_ 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fbAbi [i8Layout] u32Layout
  layouts := emptyLayoutTable
  allocations := []

/-- `fn ctlz_caller(x: u8) -> u32 { core::intrinsics::ctlz(x) }`. -/
def fbCtlzCaller : CapturedMir :=
  fbCaller "fallback::ctlz_caller" "core::intrinsics::ctlz" [.uint .u8] [u32Decl, u8Decl]
    (fbAbi [i8Layout] u32Layout)

theorem fbCtlz_inFragment : progInFragment fbCtlzCaller [fbCtlzCallee] = true := by decide

def fbCtlzCalleeFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u8), (localName 2, .Int u8),
    (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 0)) (.Constant (.Int 8) (.Int u32)),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int 4) (.Int i32)))],
      .Switch (.Load (.Local (localName 2))) ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 0))) (.Constant (.Int 4) (.Int u32))),
      .Assign (.Local (localName 1)) (.Load (.Local (localName 2)))],
      .Goto (bbName 2), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int 2) (.Int i32)))],
      .Switch (.Load (.Local (localName 2))) ⟨[(0, bbName 4)]⟩ (bbName 3), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 0))) (.Constant (.Int 2) (.Int u32))),
      .Assign (.Local (localName 1)) (.Load (.Local (localName 2)))],
      .Goto (bbName 4), .Regular⟩),
    (bbName 4, ⟨[
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int 1) (.Int i32)))],
      .Switch (.Load (.Local (localName 2))) ⟨[(0, bbName 6)]⟩ (bbName 5), .Regular⟩),
    (bbName 5, ⟨[
      .StorageDead (localName 2),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 0))) (.Constant (.Int 2) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 6, ⟨[
      .StorageDead (localName 2),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3)) (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 1)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 0))) (.Load (.Local (localName 3)))),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 7, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 7
  implicit_writes := true

def fbCtlzCallerFn : Gen.Function := fbCallerFn [.Int u32, .Int u8]
def fbCtlzProg : Gen.Program := fbProg fbCtlzCallerFn fbCtlzCalleeFn

theorem fbCtlz_translate : translateProg fbCtlzCaller [fbCtlzCallee] = some fbCtlzProg := rfl

theorem fbCtlzCaller_translateInProg :
    translateFnInProg (fnNameMap fbCtlzCaller [fbCtlzCallee]) fbCtlzCaller =
      some fbCtlzCallerFn := rfl

/-- Leading zero bits of the 8-bit value `a`: the position, counting down from
bit `7`, of its highest set bit, or `8` when `a = 0`. -/
def fbCtlzSpec (a : Nat) : Nat := ((List.range 8).find? (fun i => a.testBit (7 - i))).getD 8

def fbCtlzMInit (a : Nat) : Mach :=
  fbMInit fbCtxU32 fbCtlzProg fbCtlzCaller fbCtlzCallee fbCtlzCallerFn [.scalar ⟨a, 1⟩]

theorem fbCtlz_check : (List.range 256).all (fun a =>
    fbRunsTo fbCtlzCaller [fbCtlzCallee] 30 [.scalar ⟨a, 1⟩] (fbCtlzSpec a) 4) = true := by
  decide +kernel

/-- Exhaustive: for every `u8` input, Anneal returns `fbCtlzSpec a` without
UB. -/
theorem fbCtlz_anneal_all (a : Nat) (ha : a < 256) :
    fbReturns fbCtlzCaller [fbCtlzCallee] [.scalar ⟨a, 1⟩] (fbCtlzSpec a) 4 :=
  (fbRunsTo_sound (fb_forall_lt_of_all fbCtlz_check a ha)).2

/-- Exhaustive: for every `u8` input, MiniRust returns the bytes of
`fbCtlzSpec a`. -/
theorem fbCtlz_minirust_all (a : Nat) (ha : a < 256) :
    fbMiniRustRet (fbCtlzMInit a) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbCtlzSpec a)) :=
  fb_minirust_of_runsTo (d := u32Decl) fbCtlz_inFragment fbCtlz_translate
    fbCtlzCaller_translateInProg (fbCtxU32_ok_u8 rfl) rfl (fb_forall_lt_of_all fbCtlz_check a ha)

/-- `ctlz(0x80u8) = 0`: every probe finds a set bit, so the branch
observations are `y = 8`, `2`, and `1`. -/
theorem fbCtlz128_anneal_ret :
    ReachesRet (mirCallTreeWithCallees fbCtlzCaller [.scalar ⟨128, 1⟩] [fbCtlzCallee])
      [fbEv 8, fbEv 2, fbEv 1]
      (.normal (.scalar ⟨fbCtlzSpec 128, 4⟩,
        { (initMachineStateWithCallees fbCtlzCaller [.scalar ⟨128, 1⟩] [fbCtlzCallee]).memory with
          activeCallee := some fbCtlzCaller })) :=
  runA_sound fbCtlzCaller 30 _ _ _ rfl

theorem fbCtlz128_noUB :
    MirNoUBTree (mirCallTreeWithCallees fbCtlzCaller [.scalar ⟨128, 1⟩] [fbCtlzCallee]) :=
  runA_noUB fbCtlzCaller 30 _ _ _ rfl

theorem fbCtlz128_minirust_ret :
    fbMiniRustRet (fbCtlzMInit 128) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbCtlzSpec 128)) :=
  fb_minirust_ret (d := u32Decl) fbCtlz_inFragment fbCtlz_translate fbCtlzCaller_translateInProg
    (fbCtxU32_ok_u8 rfl) rfl (by decide) fbCtlz128_anneal_ret

theorem fbCtlz128_minirust_direct :
    (Interp.steps 21 (fbCtlzMInit 128)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 0 }, [1]) := by
  decide +kernel

/-! ## `cttz::<u8>` -/

/-- `cttz::<u8>` (`core::intrinsics::cttz`), the number of trailing zero bits
of `x` as a `u32`. The fallback body shifts `x` right until its lowest bit is
set, after handling `x == 0` separately:
```rust
fn cttz(mut x: u8) -> u32 {
    if x == 0 { return 8; }
    let mut n: u32 = 0;
    while x & 1 == 0 { x >>= 1; n += 1; }
    n
}
```
Its MIR keeps `n` in `_0`, and its loop (`bb2`, `bb3`) runs once per trailing
zero, up to 7 times:
```text
bb0: switchInt(copy _1) -> [0: bb4, otherwise: bb1]
bb1: StorageLive(_2); _0 = const 0_u32; goto -> bb2
bb2: _2 = BitAnd(copy _1, const 1_u8); switchInt(copy _2) -> [0: bb3, otherwise: bb5]
bb3: _1 = Shr(copy _1, const 1_i32); _0 = Add(copy _0, const 1_u32); goto -> bb2
bb4: _0 = const 8_u32; return
bb5: StorageDead(_2); return
``` -/
def fbCttzCallee : CapturedMir where
  defPath := "core::intrinsics::cttz"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u8Decl, u8Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 4)], otherwise := 1 }),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 0) (.use (constU32 0)))],
      terminator := mkTerm (.goto 2), isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2) (.binaryOp .bitAnd (.copy (local_ 1)) (constU8 1)))],
      terminator := mkTerm (.switchInt (.copy (local_ 2)) { branches := [(0, 3)], otherwise := 5 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.binaryOp .shr (.copy (local_ 1)) (fbConstI32 1))),
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 0)) (constU32 1)))],
      terminator := mkTerm (.goto 2), isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 8)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fbAbi [i8Layout] u32Layout
  layouts := emptyLayoutTable
  allocations := []

/-- `fn cttz_caller(x: u8) -> u32 { core::intrinsics::cttz(x) }`. -/
def fbCttzCaller : CapturedMir :=
  fbCaller "fallback::cttz_caller" "core::intrinsics::cttz" [.uint .u8] [u32Decl, u8Decl]
    (fbAbi [i8Layout] u32Layout)

theorem fbCttz_inFragment : progInFragment fbCttzCaller [fbCttzCallee] = true := by decide

def fbCttzCalleeFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u8), (localName 2, .Int u8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 4)]⟩ (bbName 1),
      .Regular⟩),
    (bbName 1, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 0)) (.Constant (.Int 0) (.Int u32))],
      .Goto (bbName 2), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 2))
        (.BinOp (.Int .BitAnd) (.Load (.Local (localName 1))) (.Constant (.Int 1) (.Int u8)))],
      .Switch (.Load (.Local (localName 2))) ⟨[(0, bbName 3)]⟩ (bbName 5), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int 1) (.Int i32))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0))) (.Constant (.Int 1) (.Int u32)))],
      .Goto (bbName 2), .Regular⟩),
    (bbName 4, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 8) (.Int u32))], .Return,
      .Regular⟩),
    (bbName 5, ⟨[.StorageDead (localName 2)], .Return, .Regular⟩),
    (bbName 6, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 6
  implicit_writes := true

def fbCttzCallerFn : Gen.Function := fbCallerFn [.Int u32, .Int u8]
def fbCttzProg : Gen.Program := fbProg fbCttzCallerFn fbCttzCalleeFn

theorem fbCttz_translate : translateProg fbCttzCaller [fbCttzCallee] = some fbCttzProg := rfl

theorem fbCttzCaller_translateInProg :
    translateFnInProg (fnNameMap fbCttzCaller [fbCttzCallee]) fbCttzCaller =
      some fbCttzCallerFn := rfl

/-- Trailing zero bits of the 8-bit value `a`: the position of its lowest set
bit, or `8` when `a = 0`. -/
def fbCttzSpec (a : Nat) : Nat := ((List.range 8).find? (fun i => a.testBit i)).getD 8

def fbCttzMInit (a : Nat) : Mach :=
  fbMInit fbCtxU32 fbCttzProg fbCttzCaller fbCttzCallee fbCttzCallerFn [.scalar ⟨a, 1⟩]

theorem fbCttz_check : (List.range 256).all (fun a =>
    fbRunsTo fbCttzCaller [fbCttzCallee] 60 [.scalar ⟨a, 1⟩] (fbCttzSpec a) 4) = true := by
  decide +kernel

/-- Exhaustive: for every `u8` input, Anneal returns `fbCttzSpec a` without
UB. -/
theorem fbCttz_anneal_all (a : Nat) (ha : a < 256) :
    fbReturns fbCttzCaller [fbCttzCallee] [.scalar ⟨a, 1⟩] (fbCttzSpec a) 4 :=
  (fbRunsTo_sound (fb_forall_lt_of_all fbCttz_check a ha)).2

/-- Exhaustive: for every `u8` input, MiniRust returns the bytes of
`fbCttzSpec a`. -/
theorem fbCttz_minirust_all (a : Nat) (ha : a < 256) :
    fbMiniRustRet (fbCttzMInit a) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbCttzSpec a)) :=
  fb_minirust_of_runsTo (d := u32Decl) fbCttz_inFragment fbCttz_translate
    fbCttzCaller_translateInProg (fbCtxU32_ok_u8 rfl) rfl (fb_forall_lt_of_all fbCttz_check a ha)

/-- `cttz(12u8) = 2` (`12 = 0b1100`): the branch observations are the
scrutinee `x = 12` of `bb0`, then `x & 1 = 0`, `0`, and `1` for the three
loop tests. -/
theorem fbCttz12_anneal_ret :
    ReachesRet (mirCallTreeWithCallees fbCttzCaller [.scalar ⟨12, 1⟩] [fbCttzCallee])
      [fbEv 12, fbEv 0, fbEv 0, fbEv 1]
      (.normal (.scalar ⟨fbCttzSpec 12, 4⟩,
        { (initMachineStateWithCallees fbCttzCaller [.scalar ⟨12, 1⟩] [fbCttzCallee]).memory with
          activeCallee := some fbCttzCaller })) :=
  runA_sound fbCttzCaller 60 _ _ _ rfl

theorem fbCttz12_noUB :
    MirNoUBTree (mirCallTreeWithCallees fbCttzCaller [.scalar ⟨12, 1⟩] [fbCttzCallee]) :=
  runA_noUB fbCttzCaller 60 _ _ _ rfl

theorem fbCttz12_minirust_ret :
    fbMiniRustRet (fbCttzMInit 12) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbCttzSpec 12)) :=
  fb_minirust_ret (d := u32Decl) fbCttz_inFragment fbCttz_translate fbCttzCaller_translateInProg
    (fbCtxU32_ok_u8 rfl) rfl (by decide) fbCttz12_anneal_ret

theorem fbCttz12_minirust_direct :
    (Interp.steps 22 (fbCttzMInit 12)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 2 }, [1]) := by
  decide +kernel

/-! ## `bswap::<u32>` -/

/-- `bswap::<u32>` (`core::intrinsics::bswap`), which reverses the byte order
of `x`. The fallback body moves each byte with shifts and masks:
```rust
fn bswap(x: u32) -> u32 {
    (x << 24) | ((x & 0xff00) << 8) | ((x >> 8) & 0xff00) | (x >> 24)
}
```
Its MIR accumulates the result in `_2`, uses `_3` for each shifted byte, and
relies on the wrapping semantics of `Shl` to drop the high bytes of `x << 24`:
```text
bb0: StorageLive(_2); StorageLive(_3);
     _2 = Shl(copy _1, const 24_i32);
     _3 = BitAnd(copy _1, const 65280_u32); _3 = Shl(copy _3, const 8_i32);
     _2 = BitOr(copy _2, copy _3);
     _3 = Shr(copy _1, const 8_i32); _3 = BitAnd(copy _3, const 65280_u32);
     _2 = BitOr(copy _2, copy _3);
     _3 = Shr(copy _1, const 24_i32); _0 = BitOr(move _2, move _3);
     StorageDead(_3); StorageDead(_2); return
``` -/
def fbBswapCallee : CapturedMir where
  defPath := "core::intrinsics::bswap"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 2) (.binaryOp .shl (.copy (local_ 1)) (fbConstI32 24))),
        mkStmt (.assign (local_ 3) (.binaryOp .bitAnd (.copy (local_ 1)) (constU32 65280))),
        mkStmt (.assign (local_ 3) (.binaryOp .shl (.copy (local_ 3)) (fbConstI32 8))),
        mkStmt (.assign (local_ 2) (.binaryOp .bitOr (.copy (local_ 2)) (.copy (local_ 3)))),
        mkStmt (.assign (local_ 3) (.binaryOp .shr (.copy (local_ 1)) (fbConstI32 8))),
        mkStmt (.assign (local_ 3) (.binaryOp .bitAnd (.copy (local_ 3)) (constU32 65280))),
        mkStmt (.assign (local_ 2) (.binaryOp .bitOr (.copy (local_ 2)) (.copy (local_ 3)))),
        mkStmt (.assign (local_ 3) (.binaryOp .shr (.copy (local_ 1)) (fbConstI32 24))),
        mkStmt (.assign (local_ 0) (.binaryOp .bitOr (.move (local_ 2)) (.move (local_ 3)))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fbAbi [u32Layout] u32Layout
  layouts := emptyLayoutTable
  allocations := []

/-- `fn bswap_caller(x: u32) -> u32 { core::intrinsics::bswap(x) }`. -/
def fbBswapCaller : CapturedMir :=
  fbCaller "fallback::bswap_caller" "core::intrinsics::bswap" [.uint .u32] [u32Decl, u32Decl]
    (fbAbi [u32Layout] u32Layout)

theorem fbBswap_inFragment : progInFragment fbBswapCaller [fbBswapCallee] = true := by decide

def fbBswapCalleeFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Shl) (.Load (.Local (localName 1))) (.Constant (.Int 24) (.Int i32))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .BitAnd) (.Load (.Local (localName 1))) (.Constant (.Int 65280) (.Int u32))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Shl) (.Load (.Local (localName 3))) (.Constant (.Int 8) (.Int i32))),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .BitOr) (.Load (.Local (localName 2))) (.Load (.Local (localName 3)))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int 8) (.Int i32))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .BitAnd) (.Load (.Local (localName 3))) (.Constant (.Int 65280) (.Int u32))),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .BitOr) (.Load (.Local (localName 2))) (.Load (.Local (localName 3)))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int 24) (.Int i32))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .BitOr) (.Load (.Local (localName 2))) (.Load (.Local (localName 3)))),
      .StorageDead (localName 3),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def fbBswapCallerFn : Gen.Function := fbCallerFn [.Int u32, .Int u32]
def fbBswapProg : Gen.Program := fbProg fbBswapCallerFn fbBswapCalleeFn

theorem fbBswap_translate : translateProg fbBswapCaller [fbBswapCallee] = some fbBswapProg := rfl

theorem fbBswapCaller_translateInProg :
    translateFnInProg (fnNameMap fbBswapCaller [fbBswapCallee]) fbBswapCaller =
      some fbBswapCallerFn := rfl

/-- Byte swap of the 32-bit value `a`: the value whose bytes, from most to
least significant, are the bytes `a / 256 ^ i % 256` of `a` for
`i = 0, 1, 2, 3`. -/
def fbBswapSpec (a : Nat) : Nat :=
  (List.range 4).foldl (fun acc i => acc * 256 + a / 256 ^ i % 256) 0

/-- Sampled `u32` inputs: `0`, `1`, a low byte, a second byte, the sign bit,
`u32::MAX`, and `0x12345678`. -/
def fbU32Samples : List Nat := [0, 1, 255, 65280, 2147483648, 4294967295, 305419896]

def fbBswapMInit (a : Nat) : Mach :=
  fbMInit fbCtxU32 fbBswapProg fbBswapCaller fbBswapCallee fbBswapCallerFn [.scalar ⟨a, 4⟩]

theorem fbBswap_check : fbU32Samples.all (fun a =>
    fbRunsTo fbBswapCaller [fbBswapCallee] 20 [.scalar ⟨a, 4⟩] (fbBswapSpec a) 4) = true := by
  decide +kernel

theorem fbBswap_anneal_samples (a : Nat) (ha : a ∈ fbU32Samples) :
    fbReturns fbBswapCaller [fbBswapCallee] [.scalar ⟨a, 4⟩] (fbBswapSpec a) 4 :=
  (fbRunsTo_sound (fb_forall_mem_of_all fbBswap_check a ha)).2

theorem fbBswap_minirust_samples (a : Nat) (ha : a ∈ fbU32Samples) :
    fbMiniRustRet (fbBswapMInit a) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbBswapSpec a)) :=
  fb_minirust_of_runsTo (d := u32Decl) fbBswap_inFragment fbBswap_translate
    fbBswapCaller_translateInProg (fbCtxU32_ok_u32 rfl) rfl
    (fb_forall_mem_of_all fbBswap_check a ha)

/-- `bswap(0x12345678u32) = 0x78563412` (`2018915346`); the straight-line
body emits no branch observations. -/
theorem fbBswapMid_anneal_ret :
    ReachesRet (mirCallTreeWithCallees fbBswapCaller [.scalar ⟨305419896, 4⟩] [fbBswapCallee]) []
      (.normal (.scalar ⟨fbBswapSpec 305419896, 4⟩,
        { (initMachineStateWithCallees fbBswapCaller [.scalar ⟨305419896, 4⟩]
            [fbBswapCallee]).memory with
          activeCallee := some fbBswapCaller })) :=
  runA_sound fbBswapCaller 20 _ _ _ rfl

theorem fbBswapMid_noUB :
    MirNoUBTree (mirCallTreeWithCallees fbBswapCaller [.scalar ⟨305419896, 4⟩] [fbBswapCallee]) :=
  runA_noUB fbBswapCaller 20 _ _ _ rfl

theorem fbBswapMid_minirust_ret :
    fbMiniRustRet (fbBswapMInit 305419896) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbBswapSpec 305419896)) :=
  fb_minirust_ret (d := u32Decl) fbBswap_inFragment fbBswap_translate
    fbBswapCaller_translateInProg (fbCtxU32_ok_u32 rfl) rfl (by decide) fbBswapMid_anneal_ret

theorem fbBswapMid_minirust_direct :
    (Interp.steps 18 (fbBswapMInit 305419896)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 2018915346 }, [1]) := by
  decide +kernel

/-! ## `bitreverse::<u8>` -/

/-- `bitreverse::<u8>` (`core::intrinsics::bitreverse`), which reverses the
bit order of `x`. The fallback body swaps nibbles, then bit pairs, then
adjacent bits:
```rust
fn bitreverse(mut x: u8) -> u8 {
    x = (x >> 4) | (x << 4);
    x = ((x & 0xcc) >> 2) | ((x & 0x33) << 2);
    ((x & 0xaa) >> 1) | ((x & 0x55) << 1)
}
```
Its MIR reuses the parameter `_1` for `x` and the temporaries `_2` and `_3`
for the two halves of each swap; `Shl` on `u8` discards the bits shifted past
bit `7`:
```text
bb0: StorageLive(_2); StorageLive(_3);
     _2 = Shr(copy _1, const 4_i32); _3 = Shl(copy _1, const 4_i32);
     _1 = BitOr(copy _2, copy _3);
     _2 = BitAnd(copy _1, const 204_u8); _2 = Shr(copy _2, const 2_i32);
     _3 = BitAnd(copy _1, const 51_u8); _3 = Shl(copy _3, const 2_i32);
     _1 = BitOr(copy _2, copy _3);
     _2 = BitAnd(copy _1, const 170_u8); _2 = Shr(copy _2, const 1_i32);
     _3 = BitAnd(copy _1, const 85_u8); _3 = Shl(copy _3, const 1_i32);
     _0 = BitOr(move _2, move _3); StorageDead(_3); StorageDead(_2); return
``` -/
def fbBitrevCallee : CapturedMir where
  defPath := "core::intrinsics::bitreverse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u8Decl, u8Decl, u8Decl, u8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 2) (.binaryOp .shr (.copy (local_ 1)) (fbConstI32 4))),
        mkStmt (.assign (local_ 3) (.binaryOp .shl (.copy (local_ 1)) (fbConstI32 4))),
        mkStmt (.assign (local_ 1) (.binaryOp .bitOr (.copy (local_ 2)) (.copy (local_ 3)))),
        mkStmt (.assign (local_ 2) (.binaryOp .bitAnd (.copy (local_ 1)) (constU8 204))),
        mkStmt (.assign (local_ 2) (.binaryOp .shr (.copy (local_ 2)) (fbConstI32 2))),
        mkStmt (.assign (local_ 3) (.binaryOp .bitAnd (.copy (local_ 1)) (constU8 51))),
        mkStmt (.assign (local_ 3) (.binaryOp .shl (.copy (local_ 3)) (fbConstI32 2))),
        mkStmt (.assign (local_ 1) (.binaryOp .bitOr (.copy (local_ 2)) (.copy (local_ 3)))),
        mkStmt (.assign (local_ 2) (.binaryOp .bitAnd (.copy (local_ 1)) (constU8 170))),
        mkStmt (.assign (local_ 2) (.binaryOp .shr (.copy (local_ 2)) (fbConstI32 1))),
        mkStmt (.assign (local_ 3) (.binaryOp .bitAnd (.copy (local_ 1)) (constU8 85))),
        mkStmt (.assign (local_ 3) (.binaryOp .shl (.copy (local_ 3)) (fbConstI32 1))),
        mkStmt (.assign (local_ 0) (.binaryOp .bitOr (.move (local_ 2)) (.move (local_ 3)))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fbAbi [i8Layout] i8Layout
  layouts := emptyLayoutTable
  allocations := []

/-- `fn bitreverse_caller(x: u8) -> u8 { core::intrinsics::bitreverse(x) }`. -/
def fbBitrevCaller : CapturedMir :=
  fbCaller "fallback::bitreverse_caller" "core::intrinsics::bitreverse" [.uint .u8]
    [u8Decl, u8Decl] (fbAbi [i8Layout] i8Layout)

theorem fbBitrev_inFragment : progInFragment fbBitrevCaller [fbBitrevCallee] = true := by decide

def fbBitrevCalleeFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u8), (localName 1, .Int u8), (localName 2, .Int u8),
    (localName 3, .Int u8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int 4) (.Int i32))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Shl) (.Load (.Local (localName 1))) (.Constant (.Int 4) (.Int i32))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .BitOr) (.Load (.Local (localName 2))) (.Load (.Local (localName 3)))),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .BitAnd) (.Load (.Local (localName 1))) (.Constant (.Int 204) (.Int u8))),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 2))) (.Constant (.Int 2) (.Int i32))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .BitAnd) (.Load (.Local (localName 1))) (.Constant (.Int 51) (.Int u8))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Shl) (.Load (.Local (localName 3))) (.Constant (.Int 2) (.Int i32))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .BitOr) (.Load (.Local (localName 2))) (.Load (.Local (localName 3)))),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .BitAnd) (.Load (.Local (localName 1))) (.Constant (.Int 170) (.Int u8))),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 2))) (.Constant (.Int 1) (.Int i32))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .BitAnd) (.Load (.Local (localName 1))) (.Constant (.Int 85) (.Int u8))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Shl) (.Load (.Local (localName 3))) (.Constant (.Int 1) (.Int i32))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .BitOr) (.Load (.Local (localName 2))) (.Load (.Local (localName 3)))),
      .StorageDead (localName 3),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def fbBitrevCallerFn : Gen.Function := fbCallerFn [.Int u8, .Int u8]
def fbBitrevProg : Gen.Program := fbProg fbBitrevCallerFn fbBitrevCalleeFn

theorem fbBitrev_translate :
    translateProg fbBitrevCaller [fbBitrevCallee] = some fbBitrevProg := rfl

theorem fbBitrevCaller_translateInProg :
    translateFnInProg (fnNameMap fbBitrevCaller [fbBitrevCallee]) fbBitrevCaller =
      some fbBitrevCallerFn := rfl

/-- Bit reversal of the 8-bit value `a`: bit `i` of `a` becomes bit `7 - i` of
the result. -/
def fbBitrevSpec (a : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc * 2 + (if a.testBit i then 1 else 0)) 0

def fbBitrevMInit (a : Nat) : Mach :=
  fbMInit fbCtxU8 fbBitrevProg fbBitrevCaller fbBitrevCallee fbBitrevCallerFn [.scalar ⟨a, 1⟩]

theorem fbBitrev_check : (List.range 256).all (fun a =>
    fbRunsTo fbBitrevCaller [fbBitrevCallee] 30 [.scalar ⟨a, 1⟩] (fbBitrevSpec a) 1) = true := by
  decide +kernel

/-- Exhaustive: for every `u8` input, Anneal returns `fbBitrevSpec a` without
UB. -/
theorem fbBitrev_anneal_all (a : Nat) (ha : a < 256) :
    fbReturns fbBitrevCaller [fbBitrevCallee] [.scalar ⟨a, 1⟩] (fbBitrevSpec a) 1 :=
  (fbRunsTo_sound (fb_forall_lt_of_all fbBitrev_check a ha)).2

/-- Exhaustive: for every `u8` input, MiniRust returns the byte
`fbBitrevSpec a`. -/
theorem fbBitrev_minirust_all (a : Nat) (ha : a < 256) :
    fbMiniRustRet (fbBitrevMInit a) fbCallerFrameU8 retAllocI8 fbAddrs
      (scalarBytes u8 (fbBitrevSpec a)) :=
  fb_minirust_of_runsTo (d := u8Decl) fbBitrev_inFragment fbBitrev_translate
    fbBitrevCaller_translateInProg (fbCtxU8_ok_u8 rfl) rfl
    (fb_forall_lt_of_all fbBitrev_check a ha)

/-- `bitreverse(0x35u8) = 0xac` (`0b0011_0101` reversed is `0b1010_1100`). -/
theorem fbBitrev35_anneal_ret :
    ReachesRet (mirCallTreeWithCallees fbBitrevCaller [.scalar ⟨53, 1⟩] [fbBitrevCallee]) []
      (.normal (.scalar ⟨fbBitrevSpec 53, 1⟩,
        { (initMachineStateWithCallees fbBitrevCaller [.scalar ⟨53, 1⟩]
            [fbBitrevCallee]).memory with
          activeCallee := some fbBitrevCaller })) :=
  runA_sound fbBitrevCaller 30 _ _ _ rfl

theorem fbBitrev35_noUB :
    MirNoUBTree (mirCallTreeWithCallees fbBitrevCaller [.scalar ⟨53, 1⟩] [fbBitrevCallee]) :=
  runA_noUB fbBitrevCaller 30 _ _ _ rfl

theorem fbBitrev35_minirust_ret :
    fbMiniRustRet (fbBitrevMInit 53) fbCallerFrameU8 retAllocI8 fbAddrs
      (scalarBytes u8 (fbBitrevSpec 53)) :=
  fb_minirust_ret (d := u8Decl) fbBitrev_inFragment fbBitrev_translate
    fbBitrevCaller_translateInProg (fbCtxU8_ok_u8 rfl) rfl (by decide) fbBitrev35_anneal_ret

theorem fbBitrev35_minirust_direct :
    (Interp.steps 22 (fbBitrevMInit 53)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 172 }, [1]) := by
  decide +kernel

/-! ## Binary saturating operations -/

/-- Boundary values for the binary checks. As `u8` they include `0`, `1`, both
sides of `127`/`128`, and `u8::MAX`; as `i8` bit patterns they include `0`,
`1`, `i8::MAX` (`127`), `i8::MIN` (`128`), `-127` (`129`), `-2` (`254`), and
`-1` (`255`). -/
def fbU8Edges : List Nat := [0, 1, 2, 63, 64, 127, 128, 129, 191, 192, 254, 255]

/-! ### `saturating_add::<u8>` -/

/-- `saturating_add::<u8>` (`core::intrinsics::saturating_add`), `a + b`
clamped to `u8::MAX`. The fallback body selects `u8::MAX` when the checked
addition overflows:
```rust
fn saturating_add(a: u8, b: u8) -> u8 {
    let (r, overflow) = a.overflowing_add(b);
    if overflow { u8::MAX } else { r }
}
```
Its MIR holds `a.overflowing_add(b)` in the `(u8, bool)` temporary `_3` and
switches on the overflow flag `_3.1`:
```text
bb0: StorageLive(_3); _3 = AddWithOverflow(copy _1, copy _2);
     switchInt(copy (_3.1)) -> [0: bb1, otherwise: bb2]
bb1: _0 = copy (_3.0); StorageDead(_3); return
bb2: StorageDead(_3); _0 = const 255_u8; return
``` -/
def fbSatAddCallee : CapturedMir where
  defPath := "core::intrinsics::saturating_add"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u8Decl, u8Decl, u8Decl, fbU8BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3)
          (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm (.switchInt (.copy (field1 3)) { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (fbField0U8 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.storageDead 3),
        mkStmt (.assign (local_ 0) (.use (constU8 255)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fbAbi [i8Layout, i8Layout] i8Layout
  layouts := emptyLayoutTable
  allocations := []

/-- `fn saturating_add_caller(a: u8, b: u8) -> u8 { saturating_add(a, b) }`. -/
def fbSatAddCaller : CapturedMir :=
  fbCaller "fallback::saturating_add_caller" "core::intrinsics::saturating_add" [.uint .u8]
    [u8Decl, u8Decl, u8Decl] (fbAbi [i8Layout, i8Layout] i8Layout)

theorem fbSatAdd_inFragment : progInFragment fbSatAddCaller [fbSatAddCallee] = true := by decide

def fbSatAddCalleeFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u8), (localName 1, .Int u8), (localName 2, .Int u8),
    (localName 3, intBoolTupleTy u8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.IntWithOverflow .Add) (.Load (.Local (localName 1)))
          (.Load (.Local (localName 2))))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Field (.Local (localName 3)) 1)))
        ⟨[(0, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 3)) 0)),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .StorageDead (localName 3),
      .Assign (.Local (localName 0)) (.Constant (.Int 255) (.Int u8))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

def fbSatAddCallerFn : Gen.Function := fbCallerFn [.Int u8, .Int u8, .Int u8]
def fbSatAddProg : Gen.Program := fbProg fbSatAddCallerFn fbSatAddCalleeFn

theorem fbSatAdd_translate :
    translateProg fbSatAddCaller [fbSatAddCallee] = some fbSatAddProg := rfl

theorem fbSatAddCaller_translateInProg :
    translateFnInProg (fnNameMap fbSatAddCaller [fbSatAddCallee]) fbSatAddCaller =
      some fbSatAddCallerFn := rfl

/-- Saturating `u8` addition: `a + b` clamped to `255`. -/
def fbSatAddSpec (a b : Nat) : Nat := min (a + b) 255

def fbSatAddMInit (a b : Nat) : Mach :=
  fbMInit fbCtxU8 fbSatAddProg fbSatAddCaller fbSatAddCallee fbSatAddCallerFn
    [.scalar ⟨a, 1⟩, .scalar ⟨b, 1⟩]

/-- All `a` with `b = 128`: `a + 128` saturates exactly when `a ≥ 128`. -/
theorem fbSatAdd_checkRow : (List.range 256).all (fun a =>
    fbRunsTo fbSatAddCaller [fbSatAddCallee] 20 [.scalar ⟨a, 1⟩, .scalar ⟨128, 1⟩]
      (fbSatAddSpec a 128) 1) = true := by
  decide +kernel

theorem fbSatAdd_checkGrid : fbU8Edges.all (fun a => fbU8Edges.all (fun b =>
    fbRunsTo fbSatAddCaller [fbSatAddCallee] 20 [.scalar ⟨a, 1⟩, .scalar ⟨b, 1⟩]
      (fbSatAddSpec a b) 1)) = true := by
  decide +kernel

theorem fbSatAdd_anneal_row (a : Nat) (ha : a < 256) :
    fbReturns fbSatAddCaller [fbSatAddCallee] [.scalar ⟨a, 1⟩, .scalar ⟨128, 1⟩]
      (fbSatAddSpec a 128) 1 :=
  (fbRunsTo_sound (fb_forall_lt_of_all fbSatAdd_checkRow a ha)).2

theorem fbSatAdd_anneal_grid (a b : Nat) (ha : a ∈ fbU8Edges) (hb : b ∈ fbU8Edges) :
    fbReturns fbSatAddCaller [fbSatAddCallee] [.scalar ⟨a, 1⟩, .scalar ⟨b, 1⟩]
      (fbSatAddSpec a b) 1 :=
  (fbRunsTo_sound
    (fb_forall_mem_of_all (fb_forall_mem_of_all fbSatAdd_checkGrid a ha) b hb)).2

theorem fbSatAdd_minirust_row (a : Nat) (ha : a < 256) :
    fbMiniRustRet (fbSatAddMInit a 128) fbCallerFrameU8 retAllocI8 fbAddrs
      (scalarBytes u8 (fbSatAddSpec a 128)) :=
  fb_minirust_of_runsTo (d := u8Decl) fbSatAdd_inFragment fbSatAdd_translate
    fbSatAddCaller_translateInProg (fbCtxU8_ok_u8u8 rfl) rfl
    (fb_forall_lt_of_all fbSatAdd_checkRow a ha)

theorem fbSatAdd_minirust_grid (a b : Nat) (ha : a ∈ fbU8Edges) (hb : b ∈ fbU8Edges) :
    fbMiniRustRet (fbSatAddMInit a b) fbCallerFrameU8 retAllocI8 fbAddrs
      (scalarBytes u8 (fbSatAddSpec a b)) :=
  fb_minirust_of_runsTo (d := u8Decl) fbSatAdd_inFragment fbSatAdd_translate
    fbSatAddCaller_translateInProg (fbCtxU8_ok_u8u8 rfl) rfl
    (fb_forall_mem_of_all (fb_forall_mem_of_all fbSatAdd_checkGrid a ha) b hb)

/-- `saturating_add(200u8, 100u8) = 255`: the addition overflows, so the only
branch observation is the overflow flag `1`. -/
theorem fbSatAddOv_anneal_ret :
    ReachesRet (mirCallTreeWithCallees fbSatAddCaller [.scalar ⟨200, 1⟩, .scalar ⟨100, 1⟩]
        [fbSatAddCallee]) [fbEv 1]
      (.normal (.scalar ⟨fbSatAddSpec 200 100, 1⟩,
        { (initMachineStateWithCallees fbSatAddCaller [.scalar ⟨200, 1⟩, .scalar ⟨100, 1⟩]
            [fbSatAddCallee]).memory with
          activeCallee := some fbSatAddCaller })) :=
  runA_sound fbSatAddCaller 20 _ _ _ rfl

theorem fbSatAddOv_noUB :
    MirNoUBTree (mirCallTreeWithCallees fbSatAddCaller [.scalar ⟨200, 1⟩, .scalar ⟨100, 1⟩]
      [fbSatAddCallee]) :=
  runA_noUB fbSatAddCaller 20 _ _ _ rfl

theorem fbSatAddOv_minirust_ret :
    fbMiniRustRet (fbSatAddMInit 200 100) fbCallerFrameU8 retAllocI8 fbAddrs
      (scalarBytes u8 (fbSatAddSpec 200 100)) :=
  fb_minirust_ret (d := u8Decl) fbSatAdd_inFragment fbSatAdd_translate
    fbSatAddCaller_translateInProg (fbCtxU8_ok_u8u8 rfl) rfl (by decide) fbSatAddOv_anneal_ret

theorem fbSatAddOv_minirust_direct :
    (Interp.steps 10 (fbSatAddMInit 200 100)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 255 }, [1]) := by
  decide +kernel

/-! ### `saturating_sub::<i8>` -/

/-- `saturating_sub::<i8>` (`core::intrinsics::saturating_sub`), `a - b`
clamped to `i8::MIN ..= i8::MAX`. The fallback body uses the sign of `b` to
pick the bound when the checked subtraction overflows:
```rust
fn saturating_sub(a: i8, b: i8) -> i8 {
    let (r, overflow) = a.overflowing_sub(b);
    if !overflow { r } else if b < 0 { i8::MAX } else { i8::MIN }
}
```
Its MIR holds `a.overflowing_sub(b)` in the `(i8, bool)` temporary `_3` and
the comparison `b < 0` in the `bool` temporary `_4`:
```text
bb0: StorageLive(_3); _3 = SubWithOverflow(copy _1, copy _2);
     switchInt(copy (_3.1)) -> [0: bb1, otherwise: bb2]
bb1: _0 = copy (_3.0); StorageDead(_3); return
bb2: StorageDead(_3); StorageLive(_4); _4 = Lt(copy _2, const 0_i8);
     switchInt(copy _4) -> [0: bb4, otherwise: bb3]
bb3: StorageDead(_4); _0 = const 127_i8; return
bb4: StorageDead(_4); _0 = const -128_i8; return
``` -/
def fbSatSubCallee : CapturedMir where
  defPath := "core::intrinsics::saturating_sub"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl, i8BoolTupleDecl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3)
          (.binaryOp .subWithOverflow (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm (.switchInt (.copy (field1 3)) { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (field0I8 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.storageDead 3),
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.binaryOp .lt (.copy (local_ 2)) (constI8 0)))],
      terminator := mkTerm (.switchInt (.copy (local_ 4)) { branches := [(0, 4)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 4),
        mkStmt (.assign (local_ 0) (.use (constI8 127)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.storageDead 4),
        mkStmt (.assign (local_ 0) (.use (constI8 128)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fbAbi [i8Layout, i8Layout] i8Layout
  layouts := emptyLayoutTable
  allocations := []

/-- `fn saturating_sub_caller(a: i8, b: i8) -> i8 { saturating_sub(a, b) }`. -/
def fbSatSubCaller : CapturedMir :=
  fbCaller "fallback::saturating_sub_caller" "core::intrinsics::saturating_sub" [.int .i8]
    [i8Decl, i8Decl, i8Decl] (fbAbi [i8Layout, i8Layout] i8Layout)

theorem fbSatSub_inFragment : progInFragment fbSatSubCaller [fbSatSubCallee] = true := by decide

def fbSatSubCalleeFn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, intBoolTupleTy i8), (localName 4, .Bool)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.IntWithOverflow .Sub) (.Load (.Local (localName 1)))
          (.Load (.Local (localName 2))))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Field (.Local (localName 3)) 1)))
        ⟨[(0, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 3)) 0)),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .StorageDead (localName 3),
      .StorageLive (localName 4),
      .Assign (.Local (localName 4))
        (.BinOp (.Rel .Lt) (.Load (.Local (localName 2))) (.Constant (.Int 0) (.Int i8)))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 4))))
        ⟨[(0, bbName 4)]⟩ (bbName 3), .Regular⟩),
    (bbName 3, ⟨[
      .StorageDead (localName 4),
      .Assign (.Local (localName 0)) (.Constant (.Int 127) (.Int i8))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[
      .StorageDead (localName 4),
      .Assign (.Local (localName 0)) (.Constant (.Int (-128)) (.Int i8))],
      .Return, .Regular⟩),
    (bbName 5, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 5
  implicit_writes := true

def fbSatSubCallerFn : Gen.Function := fbCallerFn [.Int i8, .Int i8, .Int i8]
def fbSatSubProg : Gen.Program := fbProg fbSatSubCallerFn fbSatSubCalleeFn

theorem fbSatSub_translate :
    translateProg fbSatSubCaller [fbSatSubCallee] = some fbSatSubProg := rfl

theorem fbSatSubCaller_translateInProg :
    translateFnInProg (fnNameMap fbSatSubCaller [fbSatSubCallee]) fbSatSubCaller =
      some fbSatSubCallerFn := rfl

/-- The `i8` value of bit pattern `bits < 256` (two's complement). -/
def fbI8Val (bits : Nat) : Int := if bits < 128 then bits else (bits : Int) - 256

/-- The bit pattern of the `i8` value `v`. -/
def fbI8Bits (v : Int) : Nat := (v % 256).toNat

/-- Saturating `i8` subtraction on bit patterns: the difference of the two
`i8` values, clamped to `-128 ..= 127`. -/
def fbSatSubSpec (a b : Nat) : Nat :=
  fbI8Bits (max (-128) (min 127 (fbI8Val a - fbI8Val b)))

def fbSatSubMInit (a b : Nat) : Mach :=
  fbMInit fbCtxI8 fbSatSubProg fbSatSubCaller fbSatSubCallee fbSatSubCallerFn
    [.scalar ⟨a, 1⟩, .scalar ⟨b, 1⟩]

/-- All `a` with `b = i8::MIN` (bits `128`): `a - (-128)` saturates to
`i8::MAX` exactly when `a ≥ 0`. -/
theorem fbSatSub_checkRow : (List.range 256).all (fun a =>
    fbRunsTo fbSatSubCaller [fbSatSubCallee] 20 [.scalar ⟨a, 1⟩, .scalar ⟨128, 1⟩]
      (fbSatSubSpec a 128) 1) = true := by
  decide +kernel

/-- All `b` with `a = i8::MAX` (bits `127`) or `a = i8::MIN` (bits `128`):
`127 - b` saturates to `i8::MAX` exactly when `b < 0`, and `-128 - b`
saturates to `i8::MIN` exactly when `b > 0`, so these columns exercise both
outcomes of the `b < 0` test for every `b`. -/
theorem fbSatSub_checkCols : [127, 128].all (fun a => (List.range 256).all (fun b =>
    fbRunsTo fbSatSubCaller [fbSatSubCallee] 20 [.scalar ⟨a, 1⟩, .scalar ⟨b, 1⟩]
      (fbSatSubSpec a b) 1)) = true := by
  decide +kernel

theorem fbSatSub_checkGrid : fbU8Edges.all (fun a => fbU8Edges.all (fun b =>
    fbRunsTo fbSatSubCaller [fbSatSubCallee] 20 [.scalar ⟨a, 1⟩, .scalar ⟨b, 1⟩]
      (fbSatSubSpec a b) 1)) = true := by
  decide +kernel

theorem fbSatSub_anneal_row (a : Nat) (ha : a < 256) :
    fbReturns fbSatSubCaller [fbSatSubCallee] [.scalar ⟨a, 1⟩, .scalar ⟨128, 1⟩]
      (fbSatSubSpec a 128) 1 :=
  (fbRunsTo_sound (fb_forall_lt_of_all fbSatSub_checkRow a ha)).2

theorem fbSatSub_anneal_cols (a b : Nat) (ha : a ∈ [127, 128]) (hb : b < 256) :
    fbReturns fbSatSubCaller [fbSatSubCallee] [.scalar ⟨a, 1⟩, .scalar ⟨b, 1⟩]
      (fbSatSubSpec a b) 1 :=
  (fbRunsTo_sound
    (fb_forall_lt_of_all (fb_forall_mem_of_all fbSatSub_checkCols a ha) b hb)).2

theorem fbSatSub_anneal_grid (a b : Nat) (ha : a ∈ fbU8Edges) (hb : b ∈ fbU8Edges) :
    fbReturns fbSatSubCaller [fbSatSubCallee] [.scalar ⟨a, 1⟩, .scalar ⟨b, 1⟩]
      (fbSatSubSpec a b) 1 :=
  (fbRunsTo_sound
    (fb_forall_mem_of_all (fb_forall_mem_of_all fbSatSub_checkGrid a ha) b hb)).2

theorem fbSatSub_minirust_row (a : Nat) (ha : a < 256) :
    fbMiniRustRet (fbSatSubMInit a 128) callerFrameI8 retAllocI8 fbAddrs
      (scalarBytes i8 (fbSatSubSpec a 128)) :=
  fb_minirust_of_runsTo (d := i8Decl) fbSatSub_inFragment fbSatSub_translate
    fbSatSubCaller_translateInProg (fbCtxI8_ok_i8i8 rfl) rfl
    (fb_forall_lt_of_all fbSatSub_checkRow a ha)

theorem fbSatSub_minirust_cols (a b : Nat) (ha : a ∈ [127, 128]) (hb : b < 256) :
    fbMiniRustRet (fbSatSubMInit a b) callerFrameI8 retAllocI8 fbAddrs
      (scalarBytes i8 (fbSatSubSpec a b)) :=
  fb_minirust_of_runsTo (d := i8Decl) fbSatSub_inFragment fbSatSub_translate
    fbSatSubCaller_translateInProg (fbCtxI8_ok_i8i8 rfl) rfl
    (fb_forall_lt_of_all (fb_forall_mem_of_all fbSatSub_checkCols a ha) b hb)

theorem fbSatSub_minirust_grid (a b : Nat) (ha : a ∈ fbU8Edges) (hb : b ∈ fbU8Edges) :
    fbMiniRustRet (fbSatSubMInit a b) callerFrameI8 retAllocI8 fbAddrs
      (scalarBytes i8 (fbSatSubSpec a b)) :=
  fb_minirust_of_runsTo (d := i8Decl) fbSatSub_inFragment fbSatSub_translate
    fbSatSubCaller_translateInProg (fbCtxI8_ok_i8i8 rfl) rfl
    (fb_forall_mem_of_all (fb_forall_mem_of_all fbSatSub_checkGrid a ha) b hb)

/-- `saturating_sub(i8::MIN, 1) = i8::MIN` (bits `128`): the subtraction
overflows (observation `1`) and `1 < 0` fails (observation `0`). -/
theorem fbSatSubMin_anneal_ret :
    ReachesRet (mirCallTreeWithCallees fbSatSubCaller [.scalar ⟨128, 1⟩, .scalar ⟨1, 1⟩]
        [fbSatSubCallee]) [fbEv 1, fbEv 0]
      (.normal (.scalar ⟨fbSatSubSpec 128 1, 1⟩,
        { (initMachineStateWithCallees fbSatSubCaller [.scalar ⟨128, 1⟩, .scalar ⟨1, 1⟩]
            [fbSatSubCallee]).memory with
          activeCallee := some fbSatSubCaller })) :=
  runA_sound fbSatSubCaller 20 _ _ _ rfl

theorem fbSatSubMin_noUB :
    MirNoUBTree (mirCallTreeWithCallees fbSatSubCaller [.scalar ⟨128, 1⟩, .scalar ⟨1, 1⟩]
      [fbSatSubCallee]) :=
  runA_noUB fbSatSubCaller 20 _ _ _ rfl

theorem fbSatSubMin_minirust_ret :
    fbMiniRustRet (fbSatSubMInit 128 1) callerFrameI8 retAllocI8 fbAddrs
      (scalarBytes i8 (fbSatSubSpec 128 1)) :=
  fb_minirust_ret (d := i8Decl) fbSatSub_inFragment fbSatSub_translate
    fbSatSubCaller_translateInProg (fbCtxI8_ok_i8i8 rfl) rfl (by decide) fbSatSubMin_anneal_ret

theorem fbSatSubMin_minirust_direct :
    (Interp.steps 14 (fbSatSubMInit 128 1)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 128 }, [1]) := by
  decide +kernel

/-! ## `u32::wrapping_shl` and `u32::wrapping_shr` -/

/-- `u32::wrapping_shl` or `u32::wrapping_shr` (library methods on `u32`),
which shift `x` by `rhs` modulo the bit width. The body masks the shift amount
and then shifts with `op` (`Shl` or `Shr`):
```rust
fn wrapping_shl(x: u32, rhs: u32) -> u32 { x << (rhs & (u32::BITS - 1)) }
fn wrapping_shr(x: u32, rhs: u32) -> u32 { x >> (rhs & (u32::BITS - 1)) }
```
```text
bb0: StorageLive(_3); _3 = BitAnd(copy _2, const 31_u32);
     _0 = op(copy _1, move _3); StorageDead(_3); return
```
The masked amount is below 32, so the shift never reaches the bit width. -/
def fbShiftCallee (dp : String) (op : BinOp) : CapturedMir where
  defPath := dp
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.binaryOp .bitAnd (.copy (local_ 2)) (constU32 31))),
        mkStmt (.assign (local_ 0) (.binaryOp op (.copy (local_ 1)) (.move (local_ 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fbAbi [u32Layout, u32Layout] u32Layout
  layouts := emptyLayoutTable
  allocations := []

def fbShlCallee : CapturedMir := fbShiftCallee "core::num::<impl u32>::wrapping_shl" .shl
def fbShrCallee : CapturedMir := fbShiftCallee "core::num::<impl u32>::wrapping_shr" .shr

/-- `fn wrapping_shl_caller(x: u32, s: u32) -> u32 { x.wrapping_shl(s) }`. -/
def fbShlCaller : CapturedMir :=
  fbCaller "fallback::wrapping_shl_caller" "core::num::<impl u32>::wrapping_shl" []
    [u32Decl, u32Decl, u32Decl] (fbAbi [u32Layout, u32Layout] u32Layout)

/-- `fn wrapping_shr_caller(x: u32, s: u32) -> u32 { x.wrapping_shr(s) }`. -/
def fbShrCaller : CapturedMir :=
  fbCaller "fallback::wrapping_shr_caller" "core::num::<impl u32>::wrapping_shr" []
    [u32Decl, u32Decl, u32Decl] (fbAbi [u32Layout, u32Layout] u32Layout)

theorem fbShl_inFragment : progInFragment fbShlCaller [fbShlCallee] = true := by decide
theorem fbShr_inFragment : progInFragment fbShrCaller [fbShrCallee] = true := by decide

/-- The translation of `fbShiftCallee dp op` when `op` translates to the
MiniRust integer operator `iop`. -/
def fbShiftCalleeFn (iop : Gen.IntBinOp) : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .BitAnd) (.Load (.Local (localName 2))) (.Constant (.Int 31) (.Int u32))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int iop) (.Load (.Local (localName 1))) (.Load (.Local (localName 3)))),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def fbShiftCallerFn : Gen.Function := fbCallerFn [.Int u32, .Int u32, .Int u32]
def fbShlProg : Gen.Program := fbProg fbShiftCallerFn (fbShiftCalleeFn .Shl)
def fbShrProg : Gen.Program := fbProg fbShiftCallerFn (fbShiftCalleeFn .Shr)

theorem fbShl_translate : translateProg fbShlCaller [fbShlCallee] = some fbShlProg := rfl
theorem fbShr_translate : translateProg fbShrCaller [fbShrCallee] = some fbShrProg := rfl

theorem fbShlCaller_translateInProg :
    translateFnInProg (fnNameMap fbShlCaller [fbShlCallee]) fbShlCaller = some fbShiftCallerFn :=
  rfl

theorem fbShrCaller_translateInProg :
    translateFnInProg (fnNameMap fbShrCaller [fbShrCallee]) fbShrCaller = some fbShiftCallerFn :=
  rfl

/-- `x.wrapping_shl(s)` on `u32`: `x * 2 ^ (s % 32)` reduced modulo `2 ^ 32`. -/
def fbShlSpec (x s : Nat) : Nat := x * 2 ^ (s % 32) % 2 ^ 32

/-- `x.wrapping_shr(s)` on `u32`: `x / 2 ^ (s % 32)`. -/
def fbShrSpec (x s : Nat) : Nat := x / 2 ^ (s % 32)

/-- The value shifted by every amount `s < 64` in the row checks:
`0xdeadbeef`, which has set bits at both ends. -/
def fbShiftX : Nat := 3735928559

/-- Sampled `(x, s)` pairs: a zero value, shifts by `0` and `31`, the masked
amounts `32` and `u32::MAX`, a sign-bit value, and `u32::MAX`. -/
def fbShiftSamples : List (Nat × Nat) :=
  [(0, 7), (1, 0), (1, 31), (1, 32), (2147483648, 1), (4294967295, 4), (305419896, 4294967295)]

def fbShlMInit (x s : Nat) : Mach :=
  fbMInit fbCtxU32 fbShlProg fbShlCaller fbShlCallee fbShiftCallerFn
    [.scalar ⟨x, 4⟩, .scalar ⟨s, 4⟩]

def fbShrMInit (x s : Nat) : Mach :=
  fbMInit fbCtxU32 fbShrProg fbShrCaller fbShrCallee fbShiftCallerFn
    [.scalar ⟨x, 4⟩, .scalar ⟨s, 4⟩]

theorem fbShl_checkRow : (List.range 64).all (fun s =>
    fbRunsTo fbShlCaller [fbShlCallee] 20 [.scalar ⟨fbShiftX, 4⟩, .scalar ⟨s, 4⟩]
      (fbShlSpec fbShiftX s) 4) = true := by
  decide +kernel

theorem fbShl_checkSamples : fbShiftSamples.all (fun p =>
    fbRunsTo fbShlCaller [fbShlCallee] 20 [.scalar ⟨p.1, 4⟩, .scalar ⟨p.2, 4⟩]
      (fbShlSpec p.1 p.2) 4) = true := by
  decide +kernel

theorem fbShr_checkRow : (List.range 64).all (fun s =>
    fbRunsTo fbShrCaller [fbShrCallee] 20 [.scalar ⟨fbShiftX, 4⟩, .scalar ⟨s, 4⟩]
      (fbShrSpec fbShiftX s) 4) = true := by
  decide +kernel

theorem fbShr_checkSamples : fbShiftSamples.all (fun p =>
    fbRunsTo fbShrCaller [fbShrCallee] 20 [.scalar ⟨p.1, 4⟩, .scalar ⟨p.2, 4⟩]
      (fbShrSpec p.1 p.2) 4) = true := by
  decide +kernel

theorem fbShl_anneal_row (s : Nat) (hs : s < 64) :
    fbReturns fbShlCaller [fbShlCallee] [.scalar ⟨fbShiftX, 4⟩, .scalar ⟨s, 4⟩]
      (fbShlSpec fbShiftX s) 4 :=
  (fbRunsTo_sound (fb_forall_lt_of_all fbShl_checkRow s hs)).2

theorem fbShl_anneal_samples (p : Nat × Nat) (hp : p ∈ fbShiftSamples) :
    fbReturns fbShlCaller [fbShlCallee] [.scalar ⟨p.1, 4⟩, .scalar ⟨p.2, 4⟩]
      (fbShlSpec p.1 p.2) 4 :=
  (fbRunsTo_sound (fb_forall_mem_of_all fbShl_checkSamples p hp)).2

theorem fbShr_anneal_row (s : Nat) (hs : s < 64) :
    fbReturns fbShrCaller [fbShrCallee] [.scalar ⟨fbShiftX, 4⟩, .scalar ⟨s, 4⟩]
      (fbShrSpec fbShiftX s) 4 :=
  (fbRunsTo_sound (fb_forall_lt_of_all fbShr_checkRow s hs)).2

theorem fbShr_anneal_samples (p : Nat × Nat) (hp : p ∈ fbShiftSamples) :
    fbReturns fbShrCaller [fbShrCallee] [.scalar ⟨p.1, 4⟩, .scalar ⟨p.2, 4⟩]
      (fbShrSpec p.1 p.2) 4 :=
  (fbRunsTo_sound (fb_forall_mem_of_all fbShr_checkSamples p hp)).2

theorem fbShl_minirust_row (s : Nat) (hs : s < 64) :
    fbMiniRustRet (fbShlMInit fbShiftX s) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbShlSpec fbShiftX s)) :=
  fb_minirust_of_runsTo (d := u32Decl) fbShl_inFragment fbShl_translate
    fbShlCaller_translateInProg (fbCtxU32_ok_u32u32 rfl) rfl
    (fb_forall_lt_of_all fbShl_checkRow s hs)

theorem fbShl_minirust_samples (p : Nat × Nat) (hp : p ∈ fbShiftSamples) :
    fbMiniRustRet (fbShlMInit p.1 p.2) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbShlSpec p.1 p.2)) :=
  fb_minirust_of_runsTo (d := u32Decl) fbShl_inFragment fbShl_translate
    fbShlCaller_translateInProg (fbCtxU32_ok_u32u32 rfl) rfl
    (fb_forall_mem_of_all fbShl_checkSamples p hp)

theorem fbShr_minirust_row (s : Nat) (hs : s < 64) :
    fbMiniRustRet (fbShrMInit fbShiftX s) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbShrSpec fbShiftX s)) :=
  fb_minirust_of_runsTo (d := u32Decl) fbShr_inFragment fbShr_translate
    fbShrCaller_translateInProg (fbCtxU32_ok_u32u32 rfl) rfl
    (fb_forall_lt_of_all fbShr_checkRow s hs)

theorem fbShr_minirust_samples (p : Nat × Nat) (hp : p ∈ fbShiftSamples) :
    fbMiniRustRet (fbShrMInit p.1 p.2) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbShrSpec p.1 p.2)) :=
  fb_minirust_of_runsTo (d := u32Decl) fbShr_inFragment fbShr_translate
    fbShrCaller_translateInProg (fbCtxU32_ok_u32u32 rfl) rfl
    (fb_forall_mem_of_all fbShr_checkSamples p hp)

/-- `1u32.wrapping_shl(33) = 2`: the amount `33` is masked to `1`. -/
theorem fbShl33_anneal_ret :
    ReachesRet (mirCallTreeWithCallees fbShlCaller [.scalar ⟨1, 4⟩, .scalar ⟨33, 4⟩] [fbShlCallee])
      [] (.normal (.scalar ⟨fbShlSpec 1 33, 4⟩,
        { (initMachineStateWithCallees fbShlCaller [.scalar ⟨1, 4⟩, .scalar ⟨33, 4⟩]
            [fbShlCallee]).memory with
          activeCallee := some fbShlCaller })) :=
  runA_sound fbShlCaller 20 _ _ _ rfl

theorem fbShl33_noUB :
    MirNoUBTree (mirCallTreeWithCallees fbShlCaller [.scalar ⟨1, 4⟩, .scalar ⟨33, 4⟩]
      [fbShlCallee]) :=
  runA_noUB fbShlCaller 20 _ _ _ rfl

theorem fbShl33_minirust_ret :
    fbMiniRustRet (fbShlMInit 1 33) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbShlSpec 1 33)) :=
  fb_minirust_ret (d := u32Decl) fbShl_inFragment fbShl_translate fbShlCaller_translateInProg
    (fbCtxU32_ok_u32u32 rfl) rfl (by decide) fbShl33_anneal_ret

theorem fbShl33_minirust_direct :
    (Interp.steps 9 (fbShlMInit 1 33)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 2 }, [1]) := by
  decide +kernel

/-- `0x8000_0000u32.wrapping_shr(63) = 1`: the amount `63` is masked to
`31`. -/
theorem fbShr63_anneal_ret :
    ReachesRet (mirCallTreeWithCallees fbShrCaller [.scalar ⟨2147483648, 4⟩, .scalar ⟨63, 4⟩]
        [fbShrCallee])
      [] (.normal (.scalar ⟨fbShrSpec 2147483648 63, 4⟩,
        { (initMachineStateWithCallees fbShrCaller [.scalar ⟨2147483648, 4⟩, .scalar ⟨63, 4⟩]
            [fbShrCallee]).memory with
          activeCallee := some fbShrCaller })) :=
  runA_sound fbShrCaller 20 _ _ _ rfl

theorem fbShr63_noUB :
    MirNoUBTree (mirCallTreeWithCallees fbShrCaller [.scalar ⟨2147483648, 4⟩, .scalar ⟨63, 4⟩]
      [fbShrCallee]) :=
  runA_noUB fbShrCaller 20 _ _ _ rfl

theorem fbShr63_minirust_ret :
    fbMiniRustRet (fbShrMInit 2147483648 63) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbShrSpec 2147483648 63)) :=
  fb_minirust_ret (d := u32Decl) fbShr_inFragment fbShr_translate fbShrCaller_translateInProg
    (fbCtxU32_ok_u32u32 rfl) rfl (by decide) fbShr63_anneal_ret

theorem fbShr63_minirust_direct :
    (Interp.steps 9 (fbShrMInit 2147483648 63)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 1 }, [1]) := by
  decide +kernel


/-! ## Completeness Audit: Statement Lowering vs Fallback

The `core::intrinsics::unchecked_add`, `unchecked_sub`, `unchecked_mul`,
`unchecked_shl`, and `unchecked_shr` intrinsics, along with `wrapping_add`,
`wrapping_sub`, and `wrapping_mul`, are handled by `rustc`'s intrinsic lowering
pass during MIR building (`rustc_mir_build`). They become `Rvalue::BinaryOp`
statements (`BinOp.*Unchecked` or ordinary `BinOp.add`/`sub`/`mul`) in the MIR,
so they do not appear as `TerminatorKind::Call` to `core::intrinsics::*` in
`Runtime(PostCleanup)` MIR. Consequently, they do not require
`ExternalCallHandler` implementations or `callees` fallback bodies.
`Translate.lean` translates `BinOp.addUnchecked` directly to MiniRust's
`IntBinOp::AddUnchecked` (`translateRvalue`).
-/

/-! ## `black_box::<u32>` -/

/-- `black_box::<u32>` (`core::intrinsics::black_box`), an identity function
that only restrains compiler optimizations. Neither semantics models an
optimizer, so the fallback body returns its argument:
```rust
fn black_box(dummy: u32) -> u32 { dummy }
```
```text
bb0: _0 = copy _1; return
``` -/
def fbBlackBoxCallee : CapturedMir where
  defPath := "core::intrinsics::black_box"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fbAbi [u32Layout] u32Layout
  layouts := emptyLayoutTable
  allocations := []

/-- `fn black_box_caller(x: u32) -> u32 { core::intrinsics::black_box(x) }`. -/
def fbBlackBoxCaller : CapturedMir :=
  fbCaller "fallback::black_box_caller" "core::intrinsics::black_box" [.uint .u32]
    [u32Decl, u32Decl] (fbAbi [u32Layout] u32Layout)

theorem fbBlackBox_inFragment : progInFragment fbBlackBoxCaller [fbBlackBoxCallee] = true := by
  decide

def fbBlackBoxCalleeFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 1)))], .Return,
      .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def fbBlackBoxCallerFn : Gen.Function := fbCallerFn [.Int u32, .Int u32]
def fbBlackBoxProg : Gen.Program := fbProg fbBlackBoxCallerFn fbBlackBoxCalleeFn

theorem fbBlackBox_translate :
    translateProg fbBlackBoxCaller [fbBlackBoxCallee] = some fbBlackBoxProg := rfl

theorem fbBlackBoxCaller_translateInProg :
    translateFnInProg (fnNameMap fbBlackBoxCaller [fbBlackBoxCallee]) fbBlackBoxCaller =
      some fbBlackBoxCallerFn := rfl

/-- `black_box` on `u32`: the identity. -/
def fbBlackBoxSpec (x : Nat) : Nat := x

def fbBlackBoxMInit (a : Nat) : Mach :=
  fbMInit fbCtxU32 fbBlackBoxProg fbBlackBoxCaller fbBlackBoxCallee fbBlackBoxCallerFn
    [.scalar ⟨a, 4⟩]

/-- Symbolic in `a`: no step of this run inspects the argument's bits (the
call copies the argument, the callee copies it into `_0`, and both returns move
it), so the kernel reduces `runA` with `a` a variable. -/
theorem fbBlackBox_runA (a : Nat) :
    runA fbBlackBoxCaller 10
        (initMachineStateWithCallees fbBlackBoxCaller [.scalar ⟨a, 4⟩] [fbBlackBoxCallee]) =
      some ([], .normal (.scalar ⟨fbBlackBoxSpec a, 4⟩,
        { (initMachineStateWithCallees fbBlackBoxCaller [.scalar ⟨a, 4⟩]
            [fbBlackBoxCallee]).memory with
          activeCallee := some fbBlackBoxCaller })) := rfl

theorem fbBlackBox_argsOk (a : Nat) (ha : a < 2 ^ 32) :
    argsOk fbBlackBoxCaller [.scalar ⟨a, 4⟩] = true := by
  simp [argsOk, argsOkAux, argOk, validBits, fbBlackBoxCaller, fbCaller, tyOf, tyBytes, itOf,
    scalarTypeOf, isBoolTy, isOrderingTy, intBoolTupleOf, intTypeOf, intTyBytes, u32Decl, u32Ty]
  omega

/-- Exhaustive (symbolic): for every argument bit pattern `a`, Anneal returns
`a` without UB. -/
theorem fbBlackBox_anneal_all (a : Nat) :
    fbReturns fbBlackBoxCaller [fbBlackBoxCallee] [.scalar ⟨a, 4⟩] (fbBlackBoxSpec a) 4 :=
  ⟨⟨_, _, runA_sound fbBlackBoxCaller 10 _ _ _ (fbBlackBox_runA a)⟩,
    runA_noUB fbBlackBoxCaller 10 _ _ _ (fbBlackBox_runA a)⟩

/-- Exhaustive (symbolic): for every `u32` input, MiniRust returns the bytes
of `a`. -/
theorem fbBlackBox_minirust_all (a : Nat) (ha : a < 2 ^ 32) :
    fbMiniRustRet (fbBlackBoxMInit a) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbBlackBoxSpec a)) :=
  fb_minirust_ret (d := u32Decl) fbBlackBox_inFragment fbBlackBox_translate
    fbBlackBoxCaller_translateInProg (fbCtxU32_ok_u32 rfl) rfl (fbBlackBox_argsOk a ha)
    (runA_sound fbBlackBoxCaller 10 _ _ _ (fbBlackBox_runA a))

/-- `black_box(0x12345678u32) = 0x12345678`. -/
theorem fbBlackBoxMid_anneal_ret :
    ReachesRet (mirCallTreeWithCallees fbBlackBoxCaller [.scalar ⟨305419896, 4⟩]
        [fbBlackBoxCallee]) []
      (.normal (.scalar ⟨fbBlackBoxSpec 305419896, 4⟩,
        { (initMachineStateWithCallees fbBlackBoxCaller [.scalar ⟨305419896, 4⟩]
            [fbBlackBoxCallee]).memory with
          activeCallee := some fbBlackBoxCaller })) :=
  runA_sound fbBlackBoxCaller 10 _ _ _ rfl

theorem fbBlackBoxMid_noUB :
    MirNoUBTree (mirCallTreeWithCallees fbBlackBoxCaller [.scalar ⟨305419896, 4⟩]
      [fbBlackBoxCallee]) :=
  runA_noUB fbBlackBoxCaller 10 _ _ _ rfl

theorem fbBlackBoxMid_minirust_ret :
    fbMiniRustRet (fbBlackBoxMInit 305419896) callerFrame retAlloc fbAddrs
      (scalarBytes u32 (fbBlackBoxSpec 305419896)) :=
  fb_minirust_ret (d := u32Decl) fbBlackBox_inFragment fbBlackBox_translate
    fbBlackBoxCaller_translateInProg (fbCtxU32_ok_u32 rfl) rfl (by decide)
    fbBlackBoxMid_anneal_ret

theorem fbBlackBoxMid_minirust_direct :
    (Interp.steps 6 (fbBlackBoxMInit 305419896)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 305419896 }, [1]) := by
  decide +kernel

end MiniRustSpec.Correspondence
