/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Witness
import MiniRustSpec.Correspondence.Pointers

/-!
# Raw pointer witnesses (MR-3.1)

Concrete MIR bodies with raw pointers (`*const T`, `*mut T`), each run to
completion in Anneal's semantics (`runA_sound`, `faultsA_sound`) and, after
`minimize`'s translation (`translateFn`), in the MiniRust interpretation
(`Interp.steps`), both by kernel computation (`rfl`, `decide`, `decide +kernel`;
no `native_decide`). Reference, reborrowing, two-phase borrow, `Retag`,
`CastKind.transmute`, and Tree Borrows witnesses live in
`MiniRustSpec.Correspondence.RefWitness`.

`ptrRoundTrip`, `arrayParamPtr`, `fieldPtr`, `nestedFieldPtr`, `ptrCountdown`,
`constBorrowLoop`, `repointPtr`, `ptrSpinLoop`, `uninitPtrReadUb`,
`uninitPtrWriteUb`, `deadPtrReadUb`, `uninitPtrOffsetUb`, `derefWriteRhsUb`,
`derefIdxWriteRhsUb`, and `derefFieldWriteRhsUb` lie in the correspondence
fragment (`*_inFragment`), so the end-to-end correspondence theorems
(`mirCall_ret`, `mirCall_ub`, `mirCall_noUB`, `mirCall_progress_N`,
`mirCall_steps_error`, `mirCall_outcome_N`, `mirCall_diverges_steps_ok`,
`mirCall_diverges_rel_N`) apply to them directly. `arrayElemPtr` (borrowing a
non-parameter `[u32; 2]` temporary), `dangling`, and every divergent witness
below lie outside the fragment (`*_notInFragment`).

**Agreement.** Both semantics return the same value (or diverge in lockstep) for

* `ptrRoundTrip`: `&raw mut x`, a read and a write through the pointer, a
  `PtrToPtr` cast to `*const u32`, and a read through the cast pointer;
* `arrayParamPtr`: two disjoint `&raw mut` borrows (`&raw mut a[-2 of 2]`,
  that is `a[0]`, and `&raw mut a[-1 of 2]`, that is `a[1]`; `fromEnd = true`)
  on a `[u32; 2]` parameter `a`, `Offset(p, 0)`, `move` of a pointer
  temporary, `StorageDead` and `Deinit` on pointer temporaries, `copy (*p)` and
  `move (*p)`, and writes through both `*mut` pointers confirming neither
  disables the other's borrow tag;
* `arrayElemPtr`: `&raw mut a[1]` (`ConstantIndex`) on a `[u32; 2]` temporary,
  read and written through the pointer;
* `fieldPtr`: `&raw mut s.1` on the padded struct `Padded(u8, u32, u16)` (field
  at byte offset `4`), read and written through the pointer;
* `nestedFieldPtr`: two disjoint `&raw mut` borrows (`&raw mut t.0.1` at a
  two-step nested field chain `[.field 0 .., .field 1 ..]` at byte offset `4`
  with pointee type `u32`, and `&raw mut t.1` at byte offset `8` with pointee
  type `u16`) on a nested padded tuple parameter `t: ((u8, u32), u16, ())`,
  reading and writing through both `*mut u32` and `*mut u16` pointers without
  disabling either borrow tag and preserving `.Uninit` padding bytes;
* `ptrCountdown`: a loop over four blocks that counts `x` down to `0` through
  `&raw mut x`, reading `*p` before each `switchInt` and writing `*p` in the
  loop body, then reads `x` directly; the correspondence carries the `Active`
  borrow out of the entry block across `Goto` and `SwitchInt` edges
  (`BorrowsOk.jump`);
* `constBorrowLoop`: a fresh `&raw const x` in every iteration of a loop, read
  through and then killed by `StorageDead`, so Anneal's borrow table grows by
  one `Frozen` entry per iteration while the pointer temporary is re-allocated
  in MiniRust;
* `repointPtr`: `&raw mut a[0 of 2]` and `&raw mut a[1 of 2]` (`fromEnd =
  false`) on a `[u32; 2]` parameter, a read through a copy of the first
  pointer, then the same initialized pointer local overwritten with the second
  pointer and written through, which reaches `a[1]`;
* `ptrSpinLoop`: a diverging UB-free loop that takes `_2 = &raw mut _1` in
  `bb0` and repeatedly executes `PlaceMention(_2)`, self-assignment
  `_2 = Offset(copy _2, const 0_usize)`, `_0 = copy (*_2)`, and
  `(*_2) = copy _0` in `bb1`, staying in lockstep `StateRelN` + `Reaches`
  for every step count `1 + n` (`mirCall_diverges_steps_ok`,
  `mirCall_diverges_rel_N`);

and both raise UB for `uninitPtrReadUb` (reading through an uninitialized
pointer temporary), `uninitPtrWriteUb` (writing through an uninitialized `*mut`
pointer temporary), `deadPtrReadUb` (reading through a pointer temporary after
its `StorageDead`), `uninitPtrOffsetUb` (`Offset(copy _p, 0)` on an
uninitialized pointer temporary), `derefWriteRhsUb`, `derefIdxWriteRhsUb`, and
`derefFieldWriteRhsUb` (writing an uninitialized rvalue operand through a valid
`*mut` pointer to an integer local, to a `ConstantIndex` array element, or to a
`TupleSpec` scalar field chain), and `dangling` (a read through a pointer to a
temporary after its `StorageDead`).

and `offsetDeref` (outside `inFragment` because `&raw const (_2[0 of 2])`
borrows an array element subplace and `k ≠ 0` uses a non-zero `Offset`, yet
Anneal's stride-scaled `BinOp::Offset` and subobject byte-offset dereference
match MiniRust: `offsetDeref 0` returns `a[0] = 5`, `offsetDeref 1` returns
`a[1] = 7`, and `offsetDeref 2`, `offsetDeref 3`, and `offsetDeref usizeMax`
raise UB).

**Out-of-fragment alignment and address-exposure agreement.**

* `misaligned`: reading a `u32` through a pointer one byte into a `u32` raises UB
  in both MiniRust and Anneal (`checkTargetPlaceAlign`);
* `exposeTwice`: two `&raw const x` expose the same canonical stack address and
  return `0` in both MiniRust and Anneal (`ptrAddress?`), while recording
  `exposedAllocIds = [2, 1]`. `minimize` translates `PointerExposeProvenance`
  into an intrinsic call terminator after splitting the block, which `translateFn`
  leaves to `translateFnWithIntrinsics` (`exposeTwice_translate`); `exposeTwiceFn`
  spells out that translation.

**Divergence, Anneal stricter.** Anneal raises UB where MiniRust's
`BasicMemory`, which has no aliasing model, returns a value:

* `directWrite`: a direct write to `x` disables the Tree Borrows entry of an
  earlier `&raw mut x`, so reading through the pointer afterwards is UB in
  Anneal;
* `frozenWrite`: writing through a `&raw const x` pointer cast to `*mut u32` is
  UB in Anneal.

Finally, a few ground-truth checks of the interpretation's pointer primitives:
dereferencing a pointer without provenance, wrapping pointer arithmetic, and
the bounds of `Value::Ptr`.
-/

namespace MiniRustSpec.Correspondence.PointerWitness

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

/-! ## MIR building blocks -/

def ptrMutU32Ty : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
def ptrMutU16Ty : Ty := { kind := .rawPtr .mut (.uint .u16), layoutIdx := 0 }
def ptrConstU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
def ptrConstU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
def ptrMutU32Decl : LocalDecl := { mutability := .mut, ty := ptrMutU32Ty, debugName := none }
def ptrMutU16Decl : LocalDecl := { mutability := .mut, ty := ptrMutU16Ty, debugName := none }
def ptrConstU32Decl : LocalDecl := { mutability := .mut, ty := ptrConstU32Ty, debugName := none }
def ptrConstU8Decl : LocalDecl := { mutability := .mut, ty := ptrConstU8Ty, debugName := none }
def arrU32_2Ty : Ty := { kind := .array (.uint .u32) 2, layoutIdx := 0 }
def arrU32_2Decl : LocalDecl := { mutability := .mut, ty := arrU32_2Ty, debugName := none }

/-- The place `*_i`. -/
def derefPlace (i : Nat) : Place := { local_ := i, projection := [.deref] }

/-- A body with one `u32` argument `_1` returning `u32` in `_0`, whose only
block runs `stmts` and returns. -/
def ptrBody (name : String) (decls : List LocalDecl) (stmts : List StatementKind) :
    CapturedMir where
  defPath := name
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := decls
  basicBlocks :=
    [{ statements := stmts.map mkStmt, terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- The MiniRust machine running `minimize`'s translation of `body` from its
start, with the Anneal arguments `args`, under `ctx0`. -/
def startMachine (body : CapturedMir) (args : List Value) : Option Mach :=
  (translateFn body).map (fun f => machine body f (initMachineState body args).frame.locals f.start)

/-- The return place and the stack depths after `n` MiniRust steps from
`startMachine body args`, if those steps succeed. -/
def retAfter (body : CapturedMir) (args : List Value) (n : Nat) :
    Option (Option Gen.Allocation × List Nat) :=
  (startMachine body args).bind fun m =>
    (Interp.steps n m).toOption.map
      (fun m' => (m'.mem.memory.allocations[0]?, m'.threads.map (·.stack.length)))

/-- The UB message of the `n`-th MiniRust step from `startMachine body args`, if
it raises UB. -/
def ubAfter (body : CapturedMir) (args : List Value) (n : Nat) : Option String :=
  (startMachine body args).bind fun m =>
    match Interp.steps n m with
    | .error (.ub msg) => some msg
    | _ => none

/-! ## `&raw mut x`, `*p`, and `PtrToPtr` -/

/-- MIR of
```rust
fn ptr_round_trip(mut x: u32) -> u32 {
    let p = &raw mut x;               // _2 = &raw mut _1
    let t = unsafe { *p };            // _3 = copy (*_2)
    unsafe { *p = t + 1 };            // (*_2) = Add(copy _3, const 1_u32)
    let q = p as *const u32;          // _4 = copy _2 as *const u32 (PtrToPtr)
    unsafe { *q }                     // _0 = copy (*_4)
}
```
-/
def ptrRoundTrip : CapturedMir :=
  ptrBody "witness::ptr_round_trip" [u32Decl, u32Decl, ptrMutU32Decl, u32Decl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4,
     .assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (local_ 3) (.use (.copy (derefPlace 2))),
     .assign (derefPlace 2) (.binaryOp .add (.copy (local_ 3)) (constU32 1)),
     .assign (local_ 4) (.cast .ptrToPtr (.copy (local_ 2)) ptrConstU32Ty),
     .assign (local_ 0) (.use (.copy (derefPlace 4)))]

/-- `ptrRoundTrip` lies in the correspondence fragment: `_1` is a parameter
borrowed only by `&raw mut _1`, never written directly, and every pointer
statement is one that `statementOk` admits. -/
theorem ptrRoundTrip_inFragment : inFragment ptrRoundTrip = true := by decide

/-- The MiniRust function `minimize` produces for `ptrRoundTrip`: `&raw mut _1`
becomes `AddrOf` at the thin raw pointer type, `*_2` becomes
`Deref(Load(_2), u32)`, and the `PtrToPtr` cast between thin raw pointers is
its operand. -/
def ptrRoundTripFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, thinRawPtrTy),
    (localName 3, .Int u32), (localName 4, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3), .StorageLive (localName 4),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
      .Assign (.Local (localName 3)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 3))) (.Constant (.Int 1) (.Int u32))),
      .Assign (.Local (localName 4)) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem ptrRoundTrip_translate : translateFn ptrRoundTrip = some ptrRoundTripFn := rfl

def ptrRoundTripS0 : MachineState := initMachineState ptrRoundTrip [.scalar ⟨5, 4⟩]

/-- Anneal returns `6`; its memory afterwards records the `Active` Tree Borrows
entry with tag `1` that `&raw mut _1` pushed. -/
theorem ptrRoundTrip_anneal_ret :
    ReachesRet (mirTree ptrRoundTrip ptrRoundTripS0) []
      (.normal (.scalar ⟨6, 4⟩,
        { ptrRoundTripS0.memory with borrows := [rawPtrEntry 1 .mut (local_ 1)], nextTag := 2 })) :=
  runA_sound ptrRoundTrip 30 _ _ _ rfl

theorem ptrRoundTrip_noUB :
    MirNoUBTree (mirCallTree ptrRoundTrip [.scalar ⟨5, 4⟩]) :=
  runA_noUB ptrRoundTrip 30 _ _ _ rfl

/-- MiniRust returns `6` too, after ten steps (the init block's `Goto`, nine
statements, and `Return`). -/
theorem ptrRoundTrip_minirust_direct :
    retAfter ptrRoundTrip [.scalar ⟨5, 4⟩] 10 =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1]) := by
  decide +kernel

theorem ptrRoundTrip_ctxOk : CtxOk ptrRoundTrip ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    match i, hd, hi1 with
    | 0, hd, _ =>
      simp [ptrRoundTrip, ptrBody] at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 1, hd, _ =>
      simp [ptrRoundTrip, ptrBody] at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd; simp [ptrRoundTrip, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

/-- MiniRust at `minimize`'s init block (the function's `start`). -/
def ptrRoundTripMInit : Mach :=
  machine ptrRoundTrip ptrRoundTripFn ptrRoundTripS0.frame.locals ptrRoundTripFn.start

/-- MiniRust returns `6` as well, now derived from Anneal's return
(`ptrRoundTrip_anneal_ret`) by the correspondence theorem (`mirCall_ret`), which
covers `&raw mut`, the read and the write through the pointer, and the
`PtrToPtr` copy. -/
theorem ptrRoundTrip_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n ptrRoundTripMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret ptrRoundTrip_inFragment ptrRoundTrip_translate ctx0 ptrRoundTrip_ctxOk
      [.scalar ⟨5, 4⟩] (by decide) ptrRoundTripMInit rfl rfl rfl ptrRoundTrip_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [ptrRoundTrip, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem ptrRoundTrip_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n ptrRoundTripMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k ptrRoundTripMInit = .ok mRet ∧
      ReturnRel ptrRoundTrip ctx0 s' v mRet ∧
      ReachesRet (mirCallTree ptrRoundTrip [.scalar ⟨5, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB ptrRoundTrip_inFragment ptrRoundTrip_translate ctx0 ptrRoundTrip_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) ptrRoundTripMInit rfl rfl rfl ptrRoundTrip_noUB herr

theorem ptrRoundTrip_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) ptrRoundTripMInit = .ok m' ∧
      StateRelN ptrRoundTrip ptrRoundTripFn ctx0 s' m' ∧
      Reaches (mirCallTree ptrRoundTrip [.scalar ⟨5, 4⟩]) tr (mirTree ptrRoundTrip s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k ptrRoundTripMInit = .ok mRet ∧
      ReturnRel ptrRoundTrip ctx0 s' v mRet ∧
      ReachesRet (mirCallTree ptrRoundTrip [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N ptrRoundTrip_inFragment ptrRoundTrip_translate ctx0 ptrRoundTrip_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) ptrRoundTripMInit rfl rfl rfl ptrRoundTrip_noUB n

/-! ## `&raw mut a[-2]` and `&raw mut a[-1]` on an array parameter -/

def arrU32_2Layout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiArrU32_2Arg : FnAbi :=
  { args := [{ layout := arrU32_2Layout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR of a function taking `mut a: [u32; 2]` and exercising:
* two disjoint `&raw mut` borrows on `_1` in `bb0`:
  `_2 = &raw mut _1[-2 of 2]` (`fromEnd = true`, `offset = 2`, `minLen = 2`,
  resolving to index `2 - 2 = 0` at byte offset `0`) and
  `_3 = &raw mut _1[-1 of 2]` (`fromEnd = true`, `offset = 1`, `minLen = 2`,
  resolving to index `2 - 1 = 1` at byte offset `4`);
* `Offset(copy _3, const 0_usize)` (`zeroOffsetConstOk`);
* `move _2` of a pointer temporary;
* `StorageDead(_2)` and `Deinit(_3)` on pointer temporaries;
* `copy (*_5)` and `move (*_4)`;
* dereference writes through both `*mut` pointers (`(*_5) = ...` and
  `(*_4) = ...`), confirming that writing through either of the borrow tags `1`
  (`_2`, copied to `_5`) and `2` (`_3`, offset to `_4`) disables neither. -/
def arrayParamPtr : CapturedMir :=
  { ptrBody "witness::array_param_ptr"
      [u32Decl, arrU32_2Decl, ptrMutU32Decl, ptrMutU32Decl, ptrMutU32Decl,
       ptrMutU32Decl, u32Decl, u32Decl, u32Decl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
       .storageLive 6, .storageLive 7, .storageLive 8,
       .assign (local_ 2) (.rawPtr .mut (placeConstIdx 1 2 2 true)),
       .assign (local_ 3) (.rawPtr .mut (placeConstIdx 1 1 2 true)),
       .assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (constUsize 0)),
       .assign (local_ 5) (.use (.move (local_ 2))),
       .storageDead 2,
       .deinit (local_ 3),
       .assign (local_ 6) (.use (.copy (derefPlace 5))),
       .assign (local_ 7) (.use (.move (derefPlace 4))),
       .assign (derefPlace 5) (.binaryOp .add (.copy (local_ 6)) (.copy (local_ 7))),
       .assign (local_ 8) (.use (.copy (derefPlace 5))),
       .assign (derefPlace 4) (.binaryOp .add (.copy (local_ 8)) (.copy (local_ 7))),
       .assign (local_ 0) (.use (.copy (derefPlace 4)))] with
    fnAbi := fnAbiArrU32_2Arg }

theorem arrayParamPtr_inFragment : inFragment arrayParamPtr = true := by decide

def arrayParamPtrFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Array (.Int u32) 2),
    (localName 2, thinRawPtrTy), (localName 3, thinRawPtrTy),
    (localName 4, thinRawPtrTy), (localName 5, thinRawPtrTy),
    (localName 6, .Int u32), (localName 7, .Int u32), (localName 8, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .StorageLive (localName 6), .StorageLive (localName 7), .StorageLive (localName 8),
      .Assign (.Local (localName 2))
        (.AddrOf (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))) (.Raw .None)),
      .Assign (.Local (localName 3))
        (.AddrOf (.Index (.Local (localName 1)) (.Constant (.Int 1) (.Int usizeIt))) (.Raw .None)),
      .Assign (.Local (localName 4))
        (.BinOp (.PtrOffset true) (.Load (.Local (localName 3)))
          (.BinOp (.Int .MulUnchecked) (.Constant (.Int 0) (.Int usizeIt))
            (.Constant (.Int 4) (.Int usizeIt)))),
      .Assign (.Local (localName 5)) (.Load (.Local (localName 2))),
      .StorageDead (localName 2),
      .Deinit (.Local (localName 3)),
      .Assign (.Local (localName 6)) (.Load (.Deref (.Load (.Local (localName 5))) (.Int u32))),
      .Assign (.Local (localName 7)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 5))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 6))) (.Load (.Local (localName 7)))),
      .Assign (.Local (localName 8)) (.Load (.Deref (.Load (.Local (localName 5))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 4))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 8))) (.Load (.Local (localName 7)))),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arrayParamPtr_translate : translateFn arrayParamPtr = some arrayParamPtrFn := rfl

def initArrU32_2 : Value := .aggregate 0 [.scalar ⟨5, 4⟩, .scalar ⟨7, 4⟩]

def arrayParamPtrS0 : MachineState := initMachineState arrayParamPtr [initArrU32_2]

theorem arrayParamPtr_anneal_ret :
    ReachesRet (mirTree arrayParamPtr arrayParamPtrS0) []
      (.normal (.scalar ⟨19, 4⟩,
        { arrayParamPtrS0.memory with
          borrows := [rawPtrEntry 2 .mut (placeConstIdx 1 1 2 true),
                      rawPtrEntry 1 .mut (placeConstIdx 1 2 2 true)],
          nextTag := 3 })) :=
  runA_sound arrayParamPtr 40 _ _ _ rfl

theorem arrayParamPtr_noUB :
    MirNoUBTree (mirCallTree arrayParamPtr [initArrU32_2]) :=
  runA_noUB arrayParamPtr 40 _ _ _ rfl

theorem arrayParamPtr_ctxOk : CtxOk arrayParamPtr ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : arrayParamPtr.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [arrayParamPtr, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [arrayParamPtr, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : arrayParamPtr.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [arrayParamPtr, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def arrayParamPtrMInit : Mach :=
  machine arrayParamPtr arrayParamPtrFn arrayParamPtrS0.frame.locals arrayParamPtrFn.start

theorem arrayParamPtr_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n arrayParamPtrMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 19 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret arrayParamPtr_inFragment arrayParamPtr_translate ctx0 arrayParamPtr_ctxOk
      [initArrU32_2] (by decide) arrayParamPtrMInit rfl rfl rfl arrayParamPtr_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [arrayParamPtr, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem arrayParamPtr_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n arrayParamPtrMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k arrayParamPtrMInit = .ok mRet ∧
      ReturnRel arrayParamPtr ctx0 s' v mRet ∧
      ReachesRet (mirCallTree arrayParamPtr [initArrU32_2]) tr (.normal (v, mem)) :=
  mirCall_noUB arrayParamPtr_inFragment arrayParamPtr_translate ctx0 arrayParamPtr_ctxOk
    [initArrU32_2] (by decide) arrayParamPtrMInit rfl rfl rfl arrayParamPtr_noUB herr

theorem arrayParamPtr_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) arrayParamPtrMInit = .ok m' ∧
      StateRelN arrayParamPtr arrayParamPtrFn ctx0 s' m' ∧
      Reaches (mirCallTree arrayParamPtr [initArrU32_2]) tr (mirTree arrayParamPtr s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k arrayParamPtrMInit = .ok mRet ∧
      ReturnRel arrayParamPtr ctx0 s' v mRet ∧
      ReachesRet (mirCallTree arrayParamPtr [initArrU32_2]) tr (.normal (v, mem))) :=
  mirCall_progress_N arrayParamPtr_inFragment arrayParamPtr_translate ctx0 arrayParamPtr_ctxOk
    [initArrU32_2] (by decide) arrayParamPtrMInit rfl rfl rfl arrayParamPtr_noUB n

theorem arrayParamPtr_minirust_direct :
    retAfter arrayParamPtr [initArrU32_2] 21 =
      some (some { retAlloc with data := scalarBytes u32 19 }, [1]) := by
  decide +kernel

/-! ## `&raw mut a[1]` on an array temporary (outside fragment) -/

/-- MIR of
```rust
fn array_elem_ptr(x: u32) -> u32 {
    let mut a = [x, 7];               // _2 = [copy _1, const 7_u32]
    let p = &raw mut a[1];            // _3 = &raw mut _2[1 of 2]
    let t = unsafe { *p };            // _4 = copy (*_3)
    unsafe { *p = t + x };            // (*_3) = Add(copy _4, copy _1)
    a[1]                              // _0 = copy _2[1 of 2]
}
```
-/
def arrayElemPtr : CapturedMir :=
  ptrBody "witness::array_elem_ptr" [u32Decl, u32Decl, arrU32_2Decl, ptrMutU32Decl, u32Decl]
    [.storageLive 2, .assign (local_ 2) (.aggregate (.array u32Ty) [.copy (local_ 1), constU32 7]),
     .storageLive 3, .assign (local_ 3) (.rawPtr .mut (placeConstIdx 2 1 2 false)),
     .storageLive 4, .assign (local_ 4) (.use (.copy (derefPlace 3))),
     .assign (derefPlace 3) (.binaryOp .add (.copy (local_ 4)) (.copy (local_ 1))),
     .assign (local_ 0) (.use (.copy (placeConstIdx 2 1 2 false)))]

/-- `arrayElemPtr` borrows the non-parameter array temporary `_2`, so it lies
outside the fragment (`ptrTargetSpec` requires `1 ≤ k ≤ argCount`). -/
theorem arrayElemPtr_notInFragment : inFragment arrayElemPtr = false := by decide +kernel

theorem arrayElemPtr_anneal_ret :
    ∃ mem, ReachesRet (mirTree arrayElemPtr (initMachineState arrayElemPtr [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨12, 4⟩, mem)) :=
  ⟨_, runA_sound arrayElemPtr 30 _ _ _ rfl⟩

theorem arrayElemPtr_minirust_direct :
    retAfter arrayElemPtr [.scalar ⟨5, 4⟩] 10 =
      some (some { retAlloc with data := scalarBytes u32 12 }, [1]) := by
  decide +kernel

/-! ## `&raw mut s.1` on a padded struct -/

def fnAbiPaddedArg : FnAbi :=
  { args := [{ layout := paddedStructLayout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR of
```rust
fn field_ptr(mut s: Padded) -> u32 {
    let p = &raw mut s.1;             // _2 = &raw mut (_1.1: u32)
    let t = unsafe { *p };            // _3 = copy (*_2)
    unsafe { *p = t + 1 };            // (*_2) = Add(copy _3, const 1_u32)
    s.1                               // _0 = copy (_1.1: u32)
}
```
for `struct Padded(u8, u32, u16)`, whose field `1` sits at byte offset `4`. -/
def fieldPtr : CapturedMir :=
  { ptrBody "witness::field_ptr" [u32Decl, paddedStructDecl, ptrMutU32Decl, u32Decl]
      [.storageLive 2, .assign (local_ 2) (.rawPtr .mut (placeField 1 [(1, u32Ty)])),
       .storageLive 3, .assign (local_ 3) (.use (.copy (derefPlace 2))),
       .assign (derefPlace 2) (.binaryOp .add (.copy (local_ 3)) (constU32 1)),
       .assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)])))] with
    fnAbi := fnAbiPaddedArg, layouts := paddedLayouts }

/-- `fieldPtr` lies in the correspondence fragment. -/
theorem fieldPtr_inFragment : inFragment fieldPtr = true := by decide

def fieldPtrFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, paddedMiniRustTy),
    (localName 2, thinRawPtrTy), (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.AddrOf (.Field (.Local (localName 1)) 1) (.Raw .None)),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 3))) (.Constant (.Int 1) (.Int u32))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem fieldPtr_translate : translateFn fieldPtr = some fieldPtrFn := rfl

def fieldPtrS0 : MachineState := initMachineState fieldPtr [initPaddedStruct]

theorem fieldPtr_anneal_ret :
    ReachesRet (mirTree fieldPtr fieldPtrS0) []
      (.normal (.scalar ⟨100, 4⟩,
        { fieldPtrS0.memory with
          borrows := [rawPtrEntry 1 .mut (placeField 1 [(1, u32Ty)])], nextTag := 2 })) :=
  runA_sound fieldPtr 30 _ _ _ rfl

theorem fieldPtr_noUB :
    MirNoUBTree (mirCallTree fieldPtr [initPaddedStruct]) :=
  runA_noUB fieldPtr 30 _ _ _ rfl

theorem fieldPtr_ctxOk : CtxOk fieldPtr ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : fieldPtr.layouts = paddedLayouts := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [fieldPtr, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [fieldPtr, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : fieldPtr.layouts = paddedLayouts := rfl
    rw [hlay]
    simp [fieldPtr, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def fieldPtrMInit : Mach :=
  machine fieldPtr fieldPtrFn fieldPtrS0.frame.locals fieldPtrFn.start

theorem fieldPtr_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n fieldPtrMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 100 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret fieldPtr_inFragment fieldPtr_translate ctx0 fieldPtr_ctxOk
      [initPaddedStruct] (by decide) fieldPtrMInit rfl rfl rfl fieldPtr_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [fieldPtr, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem fieldPtr_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n fieldPtrMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k fieldPtrMInit = .ok mRet ∧
      ReturnRel fieldPtr ctx0 s' v mRet ∧
      ReachesRet (mirCallTree fieldPtr [initPaddedStruct]) tr (.normal (v, mem)) :=
  mirCall_noUB fieldPtr_inFragment fieldPtr_translate ctx0 fieldPtr_ctxOk
    [initPaddedStruct] (by decide) fieldPtrMInit rfl rfl rfl fieldPtr_noUB herr

theorem fieldPtr_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) fieldPtrMInit = .ok m' ∧
      StateRelN fieldPtr fieldPtrFn ctx0 s' m' ∧
      Reaches (mirCallTree fieldPtr [initPaddedStruct]) tr (mirTree fieldPtr s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k fieldPtrMInit = .ok mRet ∧
      ReturnRel fieldPtr ctx0 s' v mRet ∧
      ReachesRet (mirCallTree fieldPtr [initPaddedStruct]) tr (.normal (v, mem))) :=
  mirCall_progress_N fieldPtr_inFragment fieldPtr_translate ctx0 fieldPtr_ctxOk
    [initPaddedStruct] (by decide) fieldPtrMInit rfl rfl rfl fieldPtr_noUB n

theorem fieldPtr_minirust_direct :
    retAfter fieldPtr [initPaddedStruct] 8 =
      some (some { retAlloc with data := scalarBytes u32 100 }, [1]) := by
  decide +kernel

/-! ## Disjoint `&raw mut t.0.1` and `&raw mut t.1` on a nested padded tuple -/

def fnAbiOuterTupleArg : FnAbi :=
  { args := [{ layout := outerTupleLayout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR of
```rust
fn nested_field_ptr(mut t: ((u8, u32), u16, ())) -> u32 {
    let p = &raw mut (t.0).1;         // _2 = &raw mut ((_1.0: (u8, u32)).1: u32)
    let q = &raw mut t.1;             // _3 = &raw mut (_1.1: u16)
    let a = unsafe { *p };            // _4 = copy (*_2)
    let b = unsafe { *q };            // _5 = copy (*_3)
    unsafe { *p = a + 20 };           // (*_2) = Add(copy _4, const 20_u32)
    unsafe { *q = b + 5 };            // (*_3) = Add(copy _5, const 5_u16)
    let a2 = unsafe { *p };           // _4 = copy (*_2)
    let b2 = unsafe { *q };           // _5 = copy (*_3)
    (b2 as u32) + a2 + (t.0).1        // _0 = Cast(IntToInt, copy _5, u32);
                                      // _0 = Add(copy _0, copy _4);
                                      // _0 = Add(copy _0, copy (_1.0.1: u32))
}
```
exercising a two-step nested field borrow (`[field 0, field 1]` at byte offset
`4`, pointee `u32`) alongside a disjoint field borrow (`[field 1]` at byte
offset `8`, pointee `u16`) on the same nested padded tuple parameter
`_1 : ((u8, u32), u16, ())`, writing through both `*mut` pointers without
disabling either borrow tag, reading back through both pointers and directly
from `_1.0.1`, and preserving `AbstractByte.Uninit` padding at `1..4` and
`10..12`. -/
def nestedFieldPtr : CapturedMir :=
  { ptrBody "witness::nested_field_ptr"
      [u32Decl, outerTupleDecl, ptrMutU32Decl, ptrMutU16Decl, u32Decl, u16Decl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
       .assign (local_ 2) (.rawPtr .mut (placeField 1 [(0, innerTupleTy), (1, u32Ty)])),
       .assign (local_ 3) (.rawPtr .mut (placeField 1 [(1, u16Ty)])),
       .assign (local_ 4) (.use (.copy (derefPlace 2))),
       .assign (local_ 5) (.use (.copy (derefPlace 3))),
       .assign (derefPlace 2) (.binaryOp .add (.copy (local_ 4)) (constU32 20)),
       .assign (derefPlace 3) (.binaryOp .add (.copy (local_ 5)) (constU16 5)),
       .assign (local_ 4) (.use (.copy (derefPlace 2))),
       .assign (local_ 5) (.use (.copy (derefPlace 3))),
       .assign (local_ 0) (.cast .intToInt (.copy (local_ 5)) u32Ty),
       .assign (local_ 0) (.binaryOp .add (.copy (local_ 0)) (.copy (local_ 4))),
       .assign (local_ 0)
         (.binaryOp .add (.copy (local_ 0))
           (.copy (placeField 1 [(0, innerTupleTy), (1, u32Ty)])))] with
    fnAbi := fnAbiOuterTupleArg, layouts := nestedLayouts }

theorem nestedFieldPtr_inFragment : inFragment nestedFieldPtr = true := by decide

def nestedFieldPtrFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, outerMiniRustTy),
    (localName 2, thinRawPtrTy), (localName 3, thinRawPtrTy),
    (localName 4, .Int u32), (localName 5, .Int u16)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .Assign (.Local (localName 2))
        (.AddrOf (.Field (.Field (.Local (localName 1)) 0) 1) (.Raw .None)),
      .Assign (.Local (localName 3))
        (.AddrOf (.Field (.Local (localName 1)) 1) (.Raw .None)),
      .Assign (.Local (localName 4))
        (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Local (localName 5))
        (.Load (.Deref (.Load (.Local (localName 3))) (.Int u16))),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 4))) (.Constant (.Int 20) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 3))) (.Int u16))
        (.BinOp (.Int .Add) (.Load (.Local (localName 5))) (.Constant (.Int 5) (.Int u16))),
      .Assign (.Local (localName 4))
        (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Local (localName 5))
        (.Load (.Deref (.Load (.Local (localName 3))) (.Int u16))),
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 5)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0))) (.Load (.Local (localName 4)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0)))
          (.Load (.Field (.Field (.Local (localName 1)) 0) 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem nestedFieldPtr_translate : translateFn nestedFieldPtr = some nestedFieldPtrFn := rfl

def nestedFieldPtrS0 : MachineState := initMachineState nestedFieldPtr [initOuterTuple]

/-- On `initOuterTuple = ((1u8, 2u32), 10u16, ())`, writing `2 + 20 = 22u32`
through `&raw mut (_1.0.1)` and `10 + 5 = 15u16` through `&raw mut (_1.1)`
yields `15 + 22 + 22 = 59u32`, while both `Active` borrow entries remain in the
borrow table. -/
theorem nestedFieldPtr_anneal_ret :
    ReachesRet (mirTree nestedFieldPtr nestedFieldPtrS0) []
      (.normal (.scalar ⟨59, 4⟩,
        { nestedFieldPtrS0.memory with
          borrows := [rawPtrEntry 2 .mut (placeField 1 [(1, u16Ty)]),
                      rawPtrEntry 1 .mut (placeField 1 [(0, innerTupleTy), (1, u32Ty)])],
          nextTag := 3 })) :=
  runA_sound nestedFieldPtr 40 _ _ _ rfl

theorem nestedFieldPtr_noUB :
    MirNoUBTree (mirCallTree nestedFieldPtr [initOuterTuple]) :=
  runA_noUB nestedFieldPtr 40 _ _ _ rfl

theorem nestedFieldPtr_ctxOk : CtxOk nestedFieldPtr ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : nestedFieldPtr.layouts = nestedLayouts := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [nestedFieldPtr, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [nestedFieldPtr, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : nestedFieldPtr.layouts = nestedLayouts := rfl
    rw [hlay]
    simp [nestedFieldPtr, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def nestedFieldPtrMInit : Mach :=
  machine nestedFieldPtr nestedFieldPtrFn nestedFieldPtrS0.frame.locals nestedFieldPtrFn.start

theorem nestedFieldPtr_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n nestedFieldPtrMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 59 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret nestedFieldPtr_inFragment nestedFieldPtr_translate ctx0 nestedFieldPtr_ctxOk
      [initOuterTuple] (by decide) nestedFieldPtrMInit rfl rfl rfl nestedFieldPtr_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [nestedFieldPtr, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem nestedFieldPtr_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n nestedFieldPtrMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k nestedFieldPtrMInit = .ok mRet ∧
      ReturnRel nestedFieldPtr ctx0 s' v mRet ∧
      ReachesRet (mirCallTree nestedFieldPtr [initOuterTuple]) tr (.normal (v, mem)) :=
  mirCall_noUB nestedFieldPtr_inFragment nestedFieldPtr_translate ctx0 nestedFieldPtr_ctxOk
    [initOuterTuple] (by decide) nestedFieldPtrMInit rfl rfl rfl nestedFieldPtr_noUB herr

theorem nestedFieldPtr_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) nestedFieldPtrMInit = .ok m' ∧
      StateRelN nestedFieldPtr nestedFieldPtrFn ctx0 s' m' ∧
      Reaches (mirCallTree nestedFieldPtr [initOuterTuple]) tr (mirTree nestedFieldPtr s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k nestedFieldPtrMInit = .ok mRet ∧
      ReturnRel nestedFieldPtr ctx0 s' v mRet ∧
      ReachesRet (mirCallTree nestedFieldPtr [initOuterTuple]) tr (.normal (v, mem))) :=
  mirCall_progress_N nestedFieldPtr_inFragment nestedFieldPtr_translate ctx0 nestedFieldPtr_ctxOk
    [initOuterTuple] (by decide) nestedFieldPtrMInit rfl rfl rfl nestedFieldPtr_noUB n

theorem nestedFieldPtr_minirust_direct :
    retAfter nestedFieldPtr [initOuterTuple] 17 =
      some (some { retAlloc with data := scalarBytes u32 59 }, [1]) := by
  decide +kernel

/-- After the two dereference writes in `nestedFieldPtr` (step 11: the init
block's `Goto` plus ten statements of `bb0`), allocation `2` (`_1` in MiniRust)
holds `1u8` at byte `0`, `.Uninit` inner padding at `1..4`, `22u32` at `4..8`,
`15u16` at `8..10`, and `.Uninit` trailing padding at `10..12`. -/
theorem nestedFieldPtr_minirust_padding_bytes :
    ((Interp.steps 11 nestedFieldPtrMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[2]?).map (·.data))) =
      some [.Init 1 none, .Uninit, .Uninit, .Uninit,
            .Init 22 none, .Init 0 none, .Init 0 none, .Init 0 none,
            .Init 15 none, .Init 0 none, .Uninit, .Uninit] := by
  decide +kernel

/-! ## A loop through a `*mut` pointer -/

/-- MIR of
```rust
fn ptr_countdown(mut x: u32) -> u32 {
    let p = &raw mut x;           // bb0: _2 = &raw mut _1; _4 = const 0_u32; goto -> bb1
    let mut steps = 0;
    while unsafe { *p } != 0 {    // bb1: _3 = copy (*_2); switchInt(copy _3) -> [0: bb3, otherwise: bb2]
        unsafe { *p = *p - 1 };   // bb2: (*_2) = Sub(copy _3, const 1_u32);
        steps += 1;               //      _4 = Add(copy _4, const 1_u32); goto -> bb1
    }
    steps + x                     // bb3: _0 = Add(copy _4, copy _1); return
}
```
The `&raw mut` borrow is taken in `bb0`, which no edge enters, and stays
`Active` while the loop reads and writes through it in `bb1` and `bb2`; `bb3`
then reads the borrowed parameter `_1` directly, which the writes through the
pointer have counted down to `0`. -/
def ptrCountdown : CapturedMir where
  defPath := "witness::ptr_countdown"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, ptrMutU32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2), mkStmt (.storageLive 3), mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 4) (.use (constU32 0)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [mkStmt (.assign (local_ 3) (.use (.copy (derefPlace 2))))],
      terminator := mkTerm (.switchInt (.copy (local_ 3)) { branches := [(0, 3)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (derefPlace 2) (.binaryOp .sub (.copy (local_ 3)) (constU32 1))),
        mkStmt (.assign (local_ 4) (.binaryOp .add (.copy (local_ 4)) (constU32 1)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 4)) (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem ptrCountdown_inFragment : inFragment ptrCountdown = true := by decide

def ptrCountdownFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, thinRawPtrTy),
    (localName 3, .Int u32), (localName 4, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3), .StorageLive (localName 4),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
      .Assign (.Local (localName 4)) (.Constant (.Int 0) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 3)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32)))],
      .Switch (.Load (.Local (localName 3))) ⟨[(0, bbName 3)]⟩ (bbName 2), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 3))) (.Constant (.Int 1) (.Int u32))),
      .Assign (.Local (localName 4))
        (.BinOp (.Int .Add) (.Load (.Local (localName 4))) (.Constant (.Int 1) (.Int u32)))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 4))) (.Load (.Local (localName 1))))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem ptrCountdown_translate : translateFn ptrCountdown = some ptrCountdownFn := rfl

def ptrCountdownS0 : MachineState := initMachineState ptrCountdown [.scalar ⟨3, 4⟩]

/-- The branch observations of `ptr_countdown(3)`: the value read through the
pointer before each `switchInt`. -/
def ptrCountdownTrace : List (Event MirEffect) :=
  [3, 2, 1, 0].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

/-- Anneal returns `3` (three iterations, and `x` is `0` afterwards); its borrow
table still holds the `Active` entry of `&raw mut _1`. -/
theorem ptrCountdown_anneal_ret :
    ReachesRet (mirTree ptrCountdown ptrCountdownS0) ptrCountdownTrace
      (.normal (.scalar ⟨3, 4⟩,
        { ptrCountdownS0.memory with borrows := [rawPtrEntry 1 .mut (local_ 1)], nextTag := 2 })) :=
  runA_sound ptrCountdown 40 _ _ _ rfl

theorem ptrCountdown_noUB : MirNoUBTree (mirCallTree ptrCountdown [.scalar ⟨3, 4⟩]) :=
  runA_noUB ptrCountdown 40 _ _ _ rfl

theorem ptrCountdown_ctxOk : CtxOk ptrCountdown ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : ptrCountdown.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [ptrCountdown] at hd; subst hd; decide
    | 1, hd, _ => simp [ptrCountdown] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : ptrCountdown.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [ptrCountdown] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MiniRust at `minimize`'s init block (the function's `start`). -/
def ptrCountdownMInit : Mach :=
  machine ptrCountdown ptrCountdownFn ptrCountdownS0.frame.locals ptrCountdownFn.start

/-- MiniRust returns `3` as well, derived from Anneal's return by the
correspondence theorem (`mirCall_ret`) through every iteration of the loop. -/
theorem ptrCountdown_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n ptrCountdownMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 3 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret ptrCountdown_inFragment ptrCountdown_translate ctx0 ptrCountdown_ctxOk
      [.scalar ⟨3, 4⟩] (by decide) ptrCountdownMInit rfl rfl rfl ptrCountdown_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [ptrCountdown] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem ptrCountdown_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n ptrCountdownMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k ptrCountdownMInit = .ok mRet ∧
      ReturnRel ptrCountdown ctx0 s' v mRet ∧
      ReachesRet (mirCallTree ptrCountdown [.scalar ⟨3, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB ptrCountdown_inFragment ptrCountdown_translate ctx0 ptrCountdown_ctxOk
    [.scalar ⟨3, 4⟩] (by decide) ptrCountdownMInit rfl rfl rfl ptrCountdown_noUB herr

theorem ptrCountdown_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) ptrCountdownMInit = .ok m' ∧
      StateRelN ptrCountdown ptrCountdownFn ctx0 s' m' ∧
      Reaches (mirCallTree ptrCountdown [.scalar ⟨3, 4⟩]) tr (mirTree ptrCountdown s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k ptrCountdownMInit = .ok mRet ∧
      ReturnRel ptrCountdown ctx0 s' v mRet ∧
      ReachesRet (mirCallTree ptrCountdown [.scalar ⟨3, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N ptrCountdown_inFragment ptrCountdown_translate ctx0 ptrCountdown_ctxOk
    [.scalar ⟨3, 4⟩] (by decide) ptrCountdownMInit rfl rfl rfl ptrCountdown_noUB n

/-- MiniRust's return, computed directly: 26 steps (the init block's `Goto`,
six steps of `bb0`, four visits of `bb1`, three of `bb2`, and `bb3`). -/
theorem ptrCountdown_minirust_direct :
    retAfter ptrCountdown [.scalar ⟨3, 4⟩] 26 =
      some (some { retAlloc with data := scalarBytes u32 3 }, [1]) := by
  decide +kernel

/-! ## `&raw const` in a loop -/

/-- MIR of
```rust
fn const_borrow_loop(x: u32) -> u32 {
    let mut acc = 0;              // bb0: _3 = const 0_u32; _4 = const 3_u32; goto -> bb1
    let mut n = 3;
    while n != 0 {                // bb1: switchInt(copy _4) -> [0: bb3, otherwise: bb2]
        let p = &raw const x;     // bb2: StorageLive(_2); _2 = &raw const _1;
        acc += unsafe { *p };     //      _5 = copy (*_2); StorageDead(_2);
        n -= 1;                   //      _3 = Add(copy _3, copy _5); _4 = Sub(copy _4, const 1_u32);
    }                             //      goto -> bb1
    acc                           // bb3: _0 = copy _3; return
}
```
Each iteration takes a fresh `&raw const` borrow of the parameter `_1` outside
the entry block (allowed because `_1` has no `&raw mut` borrow), reads through
it, and ends the pointer temporary's storage, so Anneal's borrow table
accumulates one `Frozen` entry per iteration while MiniRust re-allocates the
pointer temporary each time. -/
def constBorrowLoop : CapturedMir where
  defPath := "witness::const_borrow_loop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, ptrConstU32Decl, u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 3), mkStmt (.storageLive 4), mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 3) (.use (constU32 0))),
        mkStmt (.assign (local_ 4) (.use (constU32 3)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 4)) { branches := [(0, 3)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 5) (.use (.copy (derefPlace 2)))),
        mkStmt (.storageDead 2),
        mkStmt (.assign (local_ 3) (.binaryOp .add (.copy (local_ 3)) (.copy (local_ 5)))),
        mkStmt (.assign (local_ 4) (.binaryOp .sub (.copy (local_ 4)) (constU32 1)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem constBorrowLoop_inFragment : inFragment constBorrowLoop = true := by decide

def constBorrowLoopFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, thinRawPtrTy),
    (localName 3, .Int u32), (localName 4, .Int u32), (localName 5, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3), .StorageLive (localName 4), .StorageLive (localName 5),
      .Assign (.Local (localName 3)) (.Constant (.Int 0) (.Int u32)),
      .Assign (.Local (localName 4)) (.Constant (.Int 3) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[], .Switch (.Load (.Local (localName 4))) ⟨[(0, bbName 3)]⟩ (bbName 2),
      .Regular⟩),
    (bbName 2, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
      .Assign (.Local (localName 5)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .StorageDead (localName 2),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Add) (.Load (.Local (localName 3))) (.Load (.Local (localName 5)))),
      .Assign (.Local (localName 4))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 4))) (.Constant (.Int 1) (.Int u32)))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 3, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 3)))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem constBorrowLoop_translate : translateFn constBorrowLoop = some constBorrowLoopFn := rfl

def constBorrowLoopS0 : MachineState := initMachineState constBorrowLoop [.scalar ⟨5, 4⟩]

/-- The branch observations of `const_borrow_loop(5)`: the loop counter at each
`switchInt`. -/
def constBorrowLoopTrace : List (Event MirEffect) :=
  [3, 2, 1, 0].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

/-- Anneal returns `15`; its borrow table holds the three `Frozen` entries, with
the tags `1`, `2`, and `3`, of the three iterations' `&raw const _1`. -/
theorem constBorrowLoop_anneal_ret :
    ReachesRet (mirTree constBorrowLoop constBorrowLoopS0) constBorrowLoopTrace
      (.normal (.scalar ⟨15, 4⟩,
        { constBorrowLoopS0.memory with
          borrows := [rawPtrEntry 3 .not (local_ 1), rawPtrEntry 2 .not (local_ 1),
                      rawPtrEntry 1 .not (local_ 1)],
          nextTag := 4 })) :=
  runA_sound constBorrowLoop 50 _ _ _ rfl

theorem constBorrowLoop_noUB : MirNoUBTree (mirCallTree constBorrowLoop [.scalar ⟨5, 4⟩]) :=
  runA_noUB constBorrowLoop 50 _ _ _ rfl

theorem constBorrowLoop_ctxOk : CtxOk constBorrowLoop ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : constBorrowLoop.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [constBorrowLoop] at hd; subst hd; decide
    | 1, hd, _ => simp [constBorrowLoop] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : constBorrowLoop.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [constBorrowLoop] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MiniRust at `minimize`'s init block (the function's `start`). -/
def constBorrowLoopMInit : Mach :=
  machine constBorrowLoop constBorrowLoopFn constBorrowLoopS0.frame.locals constBorrowLoopFn.start

/-- MiniRust returns `15` as well, derived from Anneal's return by the
correspondence theorem (`mirCall_ret`). -/
theorem constBorrowLoop_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n constBorrowLoopMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 15 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret constBorrowLoop_inFragment constBorrowLoop_translate ctx0 constBorrowLoop_ctxOk
      [.scalar ⟨5, 4⟩] (by decide) constBorrowLoopMInit rfl rfl rfl constBorrowLoop_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [constBorrowLoop] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem constBorrowLoop_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n constBorrowLoopMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k constBorrowLoopMInit = .ok mRet ∧
      ReturnRel constBorrowLoop ctx0 s' v mRet ∧
      ReachesRet (mirCallTree constBorrowLoop [.scalar ⟨5, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB constBorrowLoop_inFragment constBorrowLoop_translate ctx0 constBorrowLoop_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) constBorrowLoopMInit rfl rfl rfl constBorrowLoop_noUB herr

theorem constBorrowLoop_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) constBorrowLoopMInit = .ok m' ∧
      StateRelN constBorrowLoop constBorrowLoopFn ctx0 s' m' ∧
      Reaches (mirCallTree constBorrowLoop [.scalar ⟨5, 4⟩]) tr (mirTree constBorrowLoop s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k constBorrowLoopMInit = .ok mRet ∧
      ReturnRel constBorrowLoop ctx0 s' v mRet ∧
      ReachesRet (mirCallTree constBorrowLoop [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N constBorrowLoop_inFragment constBorrowLoop_translate ctx0
    constBorrowLoop_ctxOk [.scalar ⟨5, 4⟩] (by decide) constBorrowLoopMInit rfl rfl rfl
    constBorrowLoop_noUB n

/-- MiniRust's return, computed directly: 34 steps (the init block's `Goto`,
six steps of `bb0`, four visits of `bb1`, three of `bb2`, and `bb3`). -/
theorem constBorrowLoop_minirust_direct :
    retAfter constBorrowLoop [.scalar ⟨5, 4⟩] 34 =
      some (some { retAlloc with data := scalarBytes u32 15 }, [1]) := by
  decide +kernel

/-! ## Re-pointing an initialized pointer local -/

/-- MIR of
```rust
fn repoint_ptr(mut a: [u32; 2]) -> u32 {
    let p = &raw mut a[0];        // _2 = &raw mut _1[0 of 2]
    let q = &raw mut a[1];        // _3 = &raw mut _1[1 of 2]
    let mut r = p;                // _4 = copy _2
    let x = unsafe { *r };        // _5 = copy (*_4)
    r = q;                        // _4 = copy _3
    unsafe { *r = x + 100 };      // (*_4) = Add(copy _5, const 100_u32)
    a[1]                          // _0 = copy _1[1 of 2]
}
```
borrowing `ConstantIndex` elements counted from the start (`fromEnd = false`),
overwriting the initialized pointer local `_4`, which holds the tag of `_2`,
with the tag of `_3`, and writing through the re-pointed local, which must
reach `a[1]` and not `a[0]`. -/
def repointPtr : CapturedMir :=
  { ptrBody "witness::repoint_ptr"
      [u32Decl, arrU32_2Decl, ptrMutU32Decl, ptrMutU32Decl, ptrMutU32Decl, u32Decl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
       .assign (local_ 2) (.rawPtr .mut (placeConstIdx 1 0 2 false)),
       .assign (local_ 3) (.rawPtr .mut (placeConstIdx 1 1 2 false)),
       .assign (local_ 4) (.use (.copy (local_ 2))),
       .assign (local_ 5) (.use (.copy (derefPlace 4))),
       .assign (local_ 4) (.use (.copy (local_ 3))),
       .assign (derefPlace 4) (.binaryOp .add (.copy (local_ 5)) (constU32 100)),
       .assign (local_ 0) (.use (.copy (placeConstIdx 1 1 2 false)))] with
    fnAbi := fnAbiArrU32_2Arg }

theorem repointPtr_inFragment : inFragment repointPtr = true := by decide

def repointPtrFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Array (.Int u32) 2),
    (localName 2, thinRawPtrTy), (localName 3, thinRawPtrTy), (localName 4, thinRawPtrTy),
    (localName 5, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .Assign (.Local (localName 2))
        (.AddrOf (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))) (.Raw .None)),
      .Assign (.Local (localName 3))
        (.AddrOf (.Index (.Local (localName 1)) (.Constant (.Int 1) (.Int usizeIt))) (.Raw .None)),
      .Assign (.Local (localName 4)) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 5)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32))),
      .Assign (.Local (localName 4)) (.Load (.Local (localName 3))),
      .Assign (.Deref (.Load (.Local (localName 4))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 5))) (.Constant (.Int 100) (.Int u32))),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Local (localName 1)) (.Constant (.Int 1) (.Int usizeIt))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem repointPtr_translate : translateFn repointPtr = some repointPtrFn := rfl

def repointPtrS0 : MachineState := initMachineState repointPtr [initArrU32_2]

/-- On `a = [5, 7]`, Anneal reads `5` through tag `1` and writes `105` through
tag `2`, so `a[1]` is `105`; both `Active` entries remain in the borrow table. -/
theorem repointPtr_anneal_ret :
    ReachesRet (mirTree repointPtr repointPtrS0) []
      (.normal (.scalar ⟨105, 4⟩,
        { repointPtrS0.memory with
          borrows := [rawPtrEntry 2 .mut (placeConstIdx 1 1 2 false),
                      rawPtrEntry 1 .mut (placeConstIdx 1 0 2 false)],
          nextTag := 3 })) :=
  runA_sound repointPtr 30 _ _ _ rfl

theorem repointPtr_noUB : MirNoUBTree (mirCallTree repointPtr [initArrU32_2]) :=
  runA_noUB repointPtr 30 _ _ _ rfl

theorem repointPtr_ctxOk : CtxOk repointPtr ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : repointPtr.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [repointPtr, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [repointPtr, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : repointPtr.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [repointPtr, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MiniRust at `minimize`'s init block (the function's `start`). -/
def repointPtrMInit : Mach :=
  machine repointPtr repointPtrFn repointPtrS0.frame.locals repointPtrFn.start

/-- MiniRust returns `105` as well, derived from Anneal's return by the
correspondence theorem (`mirCall_ret`). -/
theorem repointPtr_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n repointPtrMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 105 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret repointPtr_inFragment repointPtr_translate ctx0 repointPtr_ctxOk
      [initArrU32_2] (by decide) repointPtrMInit rfl rfl rfl repointPtr_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [repointPtr, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem repointPtr_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n repointPtrMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k repointPtrMInit = .ok mRet ∧
      ReturnRel repointPtr ctx0 s' v mRet ∧
      ReachesRet (mirCallTree repointPtr [initArrU32_2]) tr (.normal (v, mem)) :=
  mirCall_noUB repointPtr_inFragment repointPtr_translate ctx0 repointPtr_ctxOk
    [initArrU32_2] (by decide) repointPtrMInit rfl rfl rfl repointPtr_noUB herr

theorem repointPtr_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) repointPtrMInit = .ok m' ∧
      StateRelN repointPtr repointPtrFn ctx0 s' m' ∧
      Reaches (mirCallTree repointPtr [initArrU32_2]) tr (mirTree repointPtr s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k repointPtrMInit = .ok mRet ∧
      ReturnRel repointPtr ctx0 s' v mRet ∧
      ReachesRet (mirCallTree repointPtr [initArrU32_2]) tr (.normal (v, mem))) :=
  mirCall_progress_N repointPtr_inFragment repointPtr_translate ctx0 repointPtr_ctxOk
    [initArrU32_2] (by decide) repointPtrMInit rfl rfl rfl repointPtr_noUB n

/-- MiniRust's return, computed directly: 13 steps (the init block's `Goto`,
eleven statements, and `Return`). -/
theorem repointPtr_minirust_direct :
    retAfter repointPtr [initArrU32_2] 13 =
      some (some { retAlloc with data := scalarBytes u32 105 }, [1]) := by
  decide +kernel

/-! ## Diverging UB-free raw-pointer loop (`ptrSpinLoop`) -/

/-- MIR of a diverging raw-pointer loop:
```rust
fn ptr_spin_loop(mut x: u32) -> u32 {
    let mut p = &raw mut x;           // bb0: StorageLive(_2); _2 = &raw mut _1
    let mut acc = unsafe { *p };      //      _0 = copy (*_2); goto -> bb1
    loop {                            // bb1: PlaceMention(_2)
        p = unsafe { p.offset(0) };   //      _2 = Offset(copy _2, const 0_usize)
        acc = unsafe { *p };          //      _0 = copy (*_2)
        unsafe { *p = acc };          //      (*_2) = copy _0; goto -> bb1
    }
}
```
Exercises:
- `PlaceMention(_2)` on an initialized raw-pointer local;
- self-assignment `_2 = Offset(copy _2, const 0_usize)` where a pointer local
  is updated in place from itself;
- repeated dereference reads `_0 = copy (*_2)` and dereference writes
  `(*_2) = copy _0` across an infinite loop; and
- the non-scalar / raw-pointer diverging correspondence theorems
  `mirCall_diverges_steps_ok` and `mirCall_diverges_rel_N` (`StateRelN`). -/
def ptrSpinLoop : CapturedMir where
  defPath := "witness::ptr_spin_loop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, ptrMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefPlace 2))))],
      terminator := mkTerm (.goto 1),
      isCleanup := false },
    { statements := [
        mkStmt (.placeMention (local_ 2)),
        mkStmt (.assign (local_ 2) (.binaryOp .offset (.copy (local_ 2)) (constUsize 0))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefPlace 2)))),
        mkStmt (.assign (derefPlace 2) (.use (.copy (local_ 0))))],
      terminator := mkTerm (.goto 1),
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem ptrSpinLoop_inFragment : inFragment ptrSpinLoop = true := by decide

def ptrSpinLoopFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32)))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .PlaceMention (.Local (localName 2)),
      .Assign (.Local (localName 2))
        (.BinOp (.PtrOffset true) (.Load (.Local (localName 2)))
          (.BinOp (.Int .MulUnchecked) (.Constant (.Int 0) (.Int usizeIt))
            (.Constant (.Int 4) (.Int usizeIt)))),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32)) (.Load (.Local (localName 0)))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 2
  implicit_writes := true

theorem ptrSpinLoop_translate : translateFn ptrSpinLoop = some ptrSpinLoopFn := rfl

def ptrSpinLoopS0 : MachineState := initMachineState ptrSpinLoop [.scalar ⟨5, 4⟩]

/-- Advance `s` by `k` silent `.tau` steps of `ptrSpinLoop`. -/
def stepPtrSpinN : Nat → MachineState → MachineState
  | 0, s => s
  | k + 1, s =>
    match stepMirFn ptrSpinLoop s with
    | .tau (.running s') => stepPtrSpinN k s'
    | _ => s

/-- The 9 reachable Anneal states of `ptrSpinLoop` (4 in `bb0` and 5 cycling in `bb1`). -/
def PtrSpinInv (s : MachineState) : Prop :=
  s = stepPtrSpinN 0 ptrSpinLoopS0 ∨
  s = stepPtrSpinN 1 ptrSpinLoopS0 ∨
  s = stepPtrSpinN 2 ptrSpinLoopS0 ∨
  s = stepPtrSpinN 3 ptrSpinLoopS0 ∨
  s = stepPtrSpinN 4 ptrSpinLoopS0 ∨
  s = stepPtrSpinN 5 ptrSpinLoopS0 ∨
  s = stepPtrSpinN 6 ptrSpinLoopS0 ∨
  s = stepPtrSpinN 7 ptrSpinLoopS0 ∨
  s = stepPtrSpinN 8 ptrSpinLoopS0

theorem ptrSpinLoop_step_inv :
    ∀ s, PtrSpinInv s → ∃ s', stepMirFn ptrSpinLoop s = .tau (.running s') ∧ PtrSpinInv s' := by
  intro s hinv
  rcases hinv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨stepPtrSpinN 1 ptrSpinLoopS0, rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨stepPtrSpinN 2 ptrSpinLoopS0, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨stepPtrSpinN 3 ptrSpinLoopS0, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · exact ⟨stepPtrSpinN 4 ptrSpinLoopS0, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  · exact ⟨stepPtrSpinN 5 ptrSpinLoopS0, rfl,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  · exact ⟨stepPtrSpinN 6 ptrSpinLoopS0, rfl,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
  · exact ⟨stepPtrSpinN 7 ptrSpinLoopS0, rfl,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))⟩
  · exact ⟨stepPtrSpinN 8 ptrSpinLoopS0, rfl,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))⟩
  · exact ⟨stepPtrSpinN 4 ptrSpinLoopS0, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩

/-- `ptrSpinLoop(5)` is UB-free across its infinite interaction tree. -/
theorem ptrSpinLoop_noUB : MirNoUBTree (mirCallTree ptrSpinLoop [.scalar ⟨5, 4⟩]) :=
  treeSafe_of_tau_inv ptrSpinLoop_step_inv (Or.inl rfl)

/-- `ptrSpinLoop(5)` never reaches a return outcome. -/
theorem ptrSpinLoop_diverges (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet (mirCallTree ptrSpinLoop [.scalar ⟨5, 4⟩]) tr o :=
  noRet_of_tau_inv ptrSpinLoop_step_inv (Or.inl rfl) tr o

theorem ptrSpinLoop_ctxOk : CtxOk ptrSpinLoop ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : ptrSpinLoop.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [ptrSpinLoop] at hd; subst hd; decide
    | 1, hd, _ => simp [ptrSpinLoop] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : ptrSpinLoop.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [ptrSpinLoop] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def ptrSpinLoopMInit : Mach :=
  machine ptrSpinLoop ptrSpinLoopFn ptrSpinLoopS0.frame.locals ptrSpinLoopFn.start

/-- MiniRust started at `ptrSpinLoopFn.start` succeeds for every step count `n : Nat`. -/
theorem ptrSpinLoop_minirust_steps_ok (n : Nat) :
    ∃ m', Interp.steps n ptrSpinLoopMInit = .ok m' :=
  mirCall_diverges_steps_ok ptrSpinLoop_inFragment ptrSpinLoop_translate ctx0 ptrSpinLoop_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) ptrSpinLoopMInit rfl rfl rfl ptrSpinLoop_noUB ptrSpinLoop_diverges n

/-- Stronger lockstep divergence witness via `mirCall_diverges_rel_N`: for every
`n : Nat`, `1 + n` MiniRust steps from `ptrSpinLoopFn.start` stay in `StateRelN`
with an Anneal state reachable via `Reaches (mirCallTree ptrSpinLoop [5])`. -/
theorem ptrSpinLoop_minirust_diverges_rel (n : Nat) :
    ∃ s' m' tr, Interp.steps (1 + n) ptrSpinLoopMInit = .ok m' ∧
      StateRelN ptrSpinLoop ptrSpinLoopFn ctx0 s' m' ∧
      Reaches (mirCallTree ptrSpinLoop [.scalar ⟨5, 4⟩]) tr (mirTree ptrSpinLoop s') :=
  mirCall_diverges_rel_N ptrSpinLoop_inFragment ptrSpinLoop_translate ctx0 ptrSpinLoop_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) ptrSpinLoopMInit rfl rfl rfl ptrSpinLoop_noUB ptrSpinLoop_diverges n

/-- MiniRust, run directly rather than through the correspondence: after
`1 + 4 + 4 * 5 = 25` steps (the init block's `Goto`, `bb0`, and four iterations
of `bb1`), the callee is still running (the stack holds the caller and the
callee) and `x` (allocation `2`) still holds `5`, which every iteration reads
through the pointer and writes back. -/
theorem ptrSpinLoop_minirust_direct :
    (Interp.steps 25 ptrSpinLoopMInit).toOption.map
        (fun m => (m.threads.map (·.stack.length), (m.mem.memory.allocations[2]?).map (·.data))) =
      some ([2], some (scalarBytes u32 5)) := by
  decide +kernel

/-! ## Uninitialized pointer dereference UB (in fragment) -/

/-- Reading through an uninitialized `*const u32` pointer temporary `_2`:
```text
StorageLive(_2); _0 = copy (*_2); return
```
-/
def uninitPtrReadUb : CapturedMir :=
  ptrBody "witness::uninit_ptr_read_ub" [u32Decl, u32Decl, ptrConstU32Decl]
    [.storageLive 2,
     .assign (local_ 0) (.use (.copy (derefPlace 2)))]

theorem uninitPtrReadUb_inFragment : inFragment uninitPtrReadUb = true := by decide

def uninitPtrReadUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitPtrReadUb_translate : translateFn uninitPtrReadUb = some uninitPtrReadUbFn := rfl

def uninitPtrReadUbS0 : MachineState := initMachineState uninitPtrReadUb [.scalar ⟨5, 4⟩]
def uninitPtrReadUbMInit : Mach :=
  machine uninitPtrReadUb uninitPtrReadUbFn uninitPtrReadUbS0.frame.locals uninitPtrReadUbFn.start

theorem uninitPtrReadUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitPtrReadUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitPtrReadUb 10 _ (by decide)

theorem uninitPtrReadUb_ctxOk : CtxOk uninitPtrReadUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : uninitPtrReadUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [uninitPtrReadUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [uninitPtrReadUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : uninitPtrReadUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [uninitPtrReadUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem uninitPtrReadUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitPtrReadUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitPtrReadUb_anneal_ub
  exact mirCall_ub uninitPtrReadUb_inFragment uninitPtrReadUb_translate ctx0 uninitPtrReadUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitPtrReadUbMInit rfl rfl rfl hr hf

theorem uninitPtrReadUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n uninitPtrReadUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree uninitPtrReadUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k uninitPtrReadUbMInit = .ok mRet ∧
      ReturnRel uninitPtrReadUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree uninitPtrReadUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error uninitPtrReadUb_inFragment uninitPtrReadUb_translate ctx0 uninitPtrReadUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitPtrReadUbMInit rfl rfl rfl herr

theorem uninitPtrReadUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) uninitPtrReadUbMInit = .ok m' ∧
      StateRelN uninitPtrReadUb uninitPtrReadUbFn ctx0 s' m' ∧
      Reaches (mirCallTree uninitPtrReadUb [.scalar ⟨5, 4⟩]) tr (mirTree uninitPtrReadUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k uninitPtrReadUbMInit = .ok mRet ∧
      ReturnRel uninitPtrReadUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree uninitPtrReadUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) uninitPtrReadUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree uninitPtrReadUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N uninitPtrReadUb_inFragment uninitPtrReadUb_translate ctx0 uninitPtrReadUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitPtrReadUbMInit rfl rfl rfl n

theorem uninitPtrReadUb_minirust_direct :
    ubAfter uninitPtrReadUb [.scalar ⟨5, 4⟩] 3 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- Writing through an uninitialized `*mut u32` pointer temporary `_2`:
```text
StorageLive(_2); (*_2) = copy _1; _0 = copy _1; return
```
-/
def uninitPtrWriteUb : CapturedMir :=
  ptrBody "witness::uninit_ptr_write_ub" [u32Decl, u32Decl, ptrMutU32Decl]
    [.storageLive 2,
     .assign (derefPlace 2) (.use (.copy (local_ 1))),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem uninitPtrWriteUb_inFragment : inFragment uninitPtrWriteUb = true := by decide

def uninitPtrWriteUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32)) (.Load (.Local (localName 1))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitPtrWriteUb_translate : translateFn uninitPtrWriteUb = some uninitPtrWriteUbFn := rfl

def uninitPtrWriteUbS0 : MachineState := initMachineState uninitPtrWriteUb [.scalar ⟨5, 4⟩]
def uninitPtrWriteUbMInit : Mach :=
  machine uninitPtrWriteUb uninitPtrWriteUbFn uninitPtrWriteUbS0.frame.locals uninitPtrWriteUbFn.start

theorem uninitPtrWriteUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitPtrWriteUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitPtrWriteUb 10 _ (by decide)

theorem uninitPtrWriteUb_ctxOk : CtxOk uninitPtrWriteUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : uninitPtrWriteUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [uninitPtrWriteUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [uninitPtrWriteUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : uninitPtrWriteUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [uninitPtrWriteUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem uninitPtrWriteUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitPtrWriteUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitPtrWriteUb_anneal_ub
  exact mirCall_ub uninitPtrWriteUb_inFragment uninitPtrWriteUb_translate ctx0 uninitPtrWriteUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitPtrWriteUbMInit rfl rfl rfl hr hf

theorem uninitPtrWriteUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n uninitPtrWriteUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree uninitPtrWriteUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k uninitPtrWriteUbMInit = .ok mRet ∧
      ReturnRel uninitPtrWriteUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree uninitPtrWriteUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error uninitPtrWriteUb_inFragment uninitPtrWriteUb_translate ctx0 uninitPtrWriteUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitPtrWriteUbMInit rfl rfl rfl herr

theorem uninitPtrWriteUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) uninitPtrWriteUbMInit = .ok m' ∧
      StateRelN uninitPtrWriteUb uninitPtrWriteUbFn ctx0 s' m' ∧
      Reaches (mirCallTree uninitPtrWriteUb [.scalar ⟨5, 4⟩]) tr (mirTree uninitPtrWriteUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k uninitPtrWriteUbMInit = .ok mRet ∧
      ReturnRel uninitPtrWriteUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree uninitPtrWriteUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) uninitPtrWriteUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree uninitPtrWriteUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N uninitPtrWriteUb_inFragment uninitPtrWriteUb_translate ctx0 uninitPtrWriteUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitPtrWriteUbMInit rfl rfl rfl n

theorem uninitPtrWriteUb_minirust_direct :
    ubAfter uninitPtrWriteUb [.scalar ⟨5, 4⟩] 3 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- Reading through a pointer temporary `_2` after its `StorageDead`:
```text
StorageLive(_2); _2 = &raw const _1; StorageDead(_2); _0 = copy (*_2); return
```
Unlike `dangling` (where the borrowed target temporary had `StorageDead`), here
the target `_1` is a live parameter and the pointer temporary `_2` itself had
`StorageDead`, so the body lies in the fragment and exercises the `.dead`
pointer-slot branch of `evalPtrLoad` / `evalPlace_deref`. -/
def deadPtrReadUb : CapturedMir :=
  ptrBody "witness::dead_ptr_read_ub" [u32Decl, u32Decl, ptrConstU32Decl]
    [.storageLive 2,
     .assign (local_ 2) (.rawPtr .not (local_ 1)),
     .storageDead 2,
     .assign (local_ 0) (.use (.copy (derefPlace 2)))]

theorem deadPtrReadUb_inFragment : inFragment deadPtrReadUb = true := by decide

def deadPtrReadUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
      .StorageDead (localName 2),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deadPtrReadUb_translate : translateFn deadPtrReadUb = some deadPtrReadUbFn := rfl

def deadPtrReadUbS0 : MachineState := initMachineState deadPtrReadUb [.scalar ⟨5, 4⟩]
def deadPtrReadUbMInit : Mach :=
  machine deadPtrReadUb deadPtrReadUbFn deadPtrReadUbS0.frame.locals deadPtrReadUbFn.start

theorem deadPtrReadUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree deadPtrReadUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound deadPtrReadUb 10 _ (by decide)

theorem deadPtrReadUb_ctxOk : CtxOk deadPtrReadUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : deadPtrReadUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [deadPtrReadUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [deadPtrReadUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : deadPtrReadUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [deadPtrReadUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem deadPtrReadUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n deadPtrReadUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := deadPtrReadUb_anneal_ub
  exact mirCall_ub deadPtrReadUb_inFragment deadPtrReadUb_translate ctx0 deadPtrReadUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) deadPtrReadUbMInit rfl rfl rfl hr hf

theorem deadPtrReadUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n deadPtrReadUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree deadPtrReadUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k deadPtrReadUbMInit = .ok mRet ∧
      ReturnRel deadPtrReadUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadPtrReadUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error deadPtrReadUb_inFragment deadPtrReadUb_translate ctx0 deadPtrReadUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) deadPtrReadUbMInit rfl rfl rfl herr

theorem deadPtrReadUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) deadPtrReadUbMInit = .ok m' ∧
      StateRelN deadPtrReadUb deadPtrReadUbFn ctx0 s' m' ∧
      Reaches (mirCallTree deadPtrReadUb [.scalar ⟨5, 4⟩]) tr (mirTree deadPtrReadUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k deadPtrReadUbMInit = .ok mRet ∧
      ReturnRel deadPtrReadUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadPtrReadUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) deadPtrReadUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree deadPtrReadUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N deadPtrReadUb_inFragment deadPtrReadUb_translate ctx0 deadPtrReadUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) deadPtrReadUbMInit rfl rfl rfl n

theorem deadPtrReadUb_minirust_direct :
    ubAfter deadPtrReadUb [.scalar ⟨5, 4⟩] 5 =
      some "access to a dead local" := by
  decide +kernel

/-- Zero-offset pointer arithmetic `Offset(copy _2, const 0_usize)` on an
uninitialized pointer temporary `_2`:
```text
StorageLive(_2); StorageLive(_3); _3 = Offset(copy _2, const 0_usize); _0 = copy _1; return
```
exercising the `.uninit` UB branch of `evalStatement_assign_ptrRvalue_mr`. -/
def uninitPtrOffsetUb : CapturedMir :=
  ptrBody "witness::uninit_ptr_offset_ub" [u32Decl, u32Decl, ptrConstU32Decl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 3) (.binaryOp .offset (.copy (local_ 2)) (constUsize 0)),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem uninitPtrOffsetUb_inFragment : inFragment uninitPtrOffsetUb = true := by decide

def uninitPtrOffsetUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, thinRawPtrTy), (localName 3, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.PtrOffset true) (.Load (.Local (localName 2)))
          (.BinOp (.Int .MulUnchecked) (.Constant (.Int 0) (.Int usizeIt))
            (.Constant (.Int 4) (.Int usizeIt)))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitPtrOffsetUb_translate : translateFn uninitPtrOffsetUb = some uninitPtrOffsetUbFn := rfl

def uninitPtrOffsetUbS0 : MachineState := initMachineState uninitPtrOffsetUb [.scalar ⟨5, 4⟩]
def uninitPtrOffsetUbMInit : Mach :=
  machine uninitPtrOffsetUb uninitPtrOffsetUbFn uninitPtrOffsetUbS0.frame.locals uninitPtrOffsetUbFn.start

theorem uninitPtrOffsetUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitPtrOffsetUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitPtrOffsetUb 10 _ (by decide)

theorem uninitPtrOffsetUb_ctxOk : CtxOk uninitPtrOffsetUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : uninitPtrOffsetUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [uninitPtrOffsetUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [uninitPtrOffsetUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : uninitPtrOffsetUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [uninitPtrOffsetUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem uninitPtrOffsetUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitPtrOffsetUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitPtrOffsetUb_anneal_ub
  exact mirCall_ub uninitPtrOffsetUb_inFragment uninitPtrOffsetUb_translate ctx0 uninitPtrOffsetUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitPtrOffsetUbMInit rfl rfl rfl hr hf

theorem uninitPtrOffsetUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n uninitPtrOffsetUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree uninitPtrOffsetUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k uninitPtrOffsetUbMInit = .ok mRet ∧
      ReturnRel uninitPtrOffsetUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree uninitPtrOffsetUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error uninitPtrOffsetUb_inFragment uninitPtrOffsetUb_translate ctx0 uninitPtrOffsetUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitPtrOffsetUbMInit rfl rfl rfl herr

theorem uninitPtrOffsetUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) uninitPtrOffsetUbMInit = .ok m' ∧
      StateRelN uninitPtrOffsetUb uninitPtrOffsetUbFn ctx0 s' m' ∧
      Reaches (mirCallTree uninitPtrOffsetUb [.scalar ⟨5, 4⟩]) tr (mirTree uninitPtrOffsetUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k uninitPtrOffsetUbMInit = .ok mRet ∧
      ReturnRel uninitPtrOffsetUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree uninitPtrOffsetUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) uninitPtrOffsetUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree uninitPtrOffsetUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N uninitPtrOffsetUb_inFragment uninitPtrOffsetUb_translate ctx0 uninitPtrOffsetUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitPtrOffsetUbMInit rfl rfl rfl n

theorem uninitPtrOffsetUb_minirust_direct :
    ubAfter uninitPtrOffsetUb [.scalar ⟨5, 4⟩] 4 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- Writing an uninitialized rvalue operand `copy _3` through a valid `*mut u32`
pointer `_2`:
```text
StorageLive(_2); StorageLive(_3); _2 = &raw mut _1; (*_2) = copy _3; _0 = copy _1; return
```
exercising the `res = none` branch of `derefWrite_target` where `evalPlace` on
`(*_2)` succeeds and `evalValue` / `evalRvalue` subsequently faults on `copy _3`. -/
def derefWriteRhsUb : CapturedMir :=
  ptrBody "witness::deref_write_rhs_ub" [u32Decl, u32Decl, ptrMutU32Decl, u32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (derefPlace 2) (.use (.copy (local_ 3))),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem derefWriteRhsUb_inFragment : inFragment derefWriteRhsUb = true := by decide

def derefWriteRhsUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, thinRawPtrTy), (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32)) (.Load (.Local (localName 3))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem derefWriteRhsUb_translate : translateFn derefWriteRhsUb = some derefWriteRhsUbFn := rfl

def derefWriteRhsUbS0 : MachineState := initMachineState derefWriteRhsUb [.scalar ⟨5, 4⟩]
def derefWriteRhsUbMInit : Mach :=
  machine derefWriteRhsUb derefWriteRhsUbFn derefWriteRhsUbS0.frame.locals derefWriteRhsUbFn.start

theorem derefWriteRhsUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree derefWriteRhsUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound derefWriteRhsUb 10 _ (by decide)

theorem derefWriteRhsUb_ctxOk : CtxOk derefWriteRhsUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : derefWriteRhsUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [derefWriteRhsUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [derefWriteRhsUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : derefWriteRhsUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [derefWriteRhsUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem derefWriteRhsUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n derefWriteRhsUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := derefWriteRhsUb_anneal_ub
  exact mirCall_ub derefWriteRhsUb_inFragment derefWriteRhsUb_translate ctx0 derefWriteRhsUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) derefWriteRhsUbMInit rfl rfl rfl hr hf

theorem derefWriteRhsUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n derefWriteRhsUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree derefWriteRhsUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k derefWriteRhsUbMInit = .ok mRet ∧
      ReturnRel derefWriteRhsUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree derefWriteRhsUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error derefWriteRhsUb_inFragment derefWriteRhsUb_translate ctx0 derefWriteRhsUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) derefWriteRhsUbMInit rfl rfl rfl herr

theorem derefWriteRhsUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) derefWriteRhsUbMInit = .ok m' ∧
      StateRelN derefWriteRhsUb derefWriteRhsUbFn ctx0 s' m' ∧
      Reaches (mirCallTree derefWriteRhsUb [.scalar ⟨5, 4⟩]) tr (mirTree derefWriteRhsUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k derefWriteRhsUbMInit = .ok mRet ∧
      ReturnRel derefWriteRhsUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree derefWriteRhsUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) derefWriteRhsUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree derefWriteRhsUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N derefWriteRhsUb_inFragment derefWriteRhsUb_translate ctx0 derefWriteRhsUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) derefWriteRhsUbMInit rfl rfl rfl n

theorem derefWriteRhsUb_minirust_direct :
    ubAfter derefWriteRhsUb [.scalar ⟨5, 4⟩] 5 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- Writing an uninitialized rvalue through a valid `*mut` pointer to the
`ConstantIndex` element `_1[1 of 2]` of an array parameter:
```text
StorageLive(_2); StorageLive(_3); _2 = &raw mut _1[1 of 2]; (*_2) = copy _3;
_0 = copy _1[0 of 2]; return
```
Unlike `derefWriteRhsUb`, whose pointer targets a whole integer local, the
write targets a projected place, so both semantics fault on the rvalue in the
`ConstantIndex` branch of `derefWrite_target`. -/
def derefIdxWriteRhsUb : CapturedMir :=
  { ptrBody "witness::deref_idx_write_rhs_ub" [u32Decl, arrU32_2Decl, ptrMutU32Decl, u32Decl]
      [.storageLive 2, .storageLive 3,
       .assign (local_ 2) (.rawPtr .mut (placeConstIdx 1 1 2 false)),
       .assign (derefPlace 2) (.use (.copy (local_ 3))),
       .assign (local_ 0) (.use (.copy (placeConstIdx 1 0 2 false)))] with
    fnAbi := fnAbiArrU32_2Arg }

theorem derefIdxWriteRhsUb_inFragment : inFragment derefIdxWriteRhsUb = true := by decide

def derefIdxWriteRhsUbFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Array (.Int u32) 2),
    (localName 2, thinRawPtrTy), (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .Assign (.Local (localName 2))
        (.AddrOf (.Index (.Local (localName 1)) (.Constant (.Int 1) (.Int usizeIt))) (.Raw .None)),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32)) (.Load (.Local (localName 3))),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem derefIdxWriteRhsUb_translate :
    translateFn derefIdxWriteRhsUb = some derefIdxWriteRhsUbFn := rfl

def derefIdxWriteRhsUbS0 : MachineState := initMachineState derefIdxWriteRhsUb [initArrU32_2]
def derefIdxWriteRhsUbMInit : Mach :=
  machine derefIdxWriteRhsUb derefIdxWriteRhsUbFn derefIdxWriteRhsUbS0.frame.locals
    derefIdxWriteRhsUbFn.start

theorem derefIdxWriteRhsUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree derefIdxWriteRhsUb [initArrU32_2]) tr u ∧ FaultNow u :=
  faultsA_sound derefIdxWriteRhsUb 10 _ (by decide)

theorem derefIdxWriteRhsUb_ctxOk : CtxOk derefIdxWriteRhsUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : derefIdxWriteRhsUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [derefIdxWriteRhsUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [derefIdxWriteRhsUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : derefIdxWriteRhsUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [derefIdxWriteRhsUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem derefIdxWriteRhsUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n derefIdxWriteRhsUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := derefIdxWriteRhsUb_anneal_ub
  exact mirCall_ub derefIdxWriteRhsUb_inFragment derefIdxWriteRhsUb_translate ctx0
    derefIdxWriteRhsUb_ctxOk [initArrU32_2] (by decide) derefIdxWriteRhsUbMInit rfl rfl rfl hr hf

theorem derefIdxWriteRhsUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n derefIdxWriteRhsUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree derefIdxWriteRhsUb [initArrU32_2]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k derefIdxWriteRhsUbMInit = .ok mRet ∧
      ReturnRel derefIdxWriteRhsUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree derefIdxWriteRhsUb [initArrU32_2]) tr (.normal (v, mem))) :=
  mirCall_steps_error derefIdxWriteRhsUb_inFragment derefIdxWriteRhsUb_translate ctx0
    derefIdxWriteRhsUb_ctxOk [initArrU32_2] (by decide) derefIdxWriteRhsUbMInit rfl rfl rfl herr

theorem derefIdxWriteRhsUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) derefIdxWriteRhsUbMInit = .ok m' ∧
      StateRelN derefIdxWriteRhsUb derefIdxWriteRhsUbFn ctx0 s' m' ∧
      Reaches (mirCallTree derefIdxWriteRhsUb [initArrU32_2]) tr (mirTree derefIdxWriteRhsUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k derefIdxWriteRhsUbMInit = .ok mRet ∧
      ReturnRel derefIdxWriteRhsUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree derefIdxWriteRhsUb [initArrU32_2]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) derefIdxWriteRhsUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree derefIdxWriteRhsUb [initArrU32_2]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N derefIdxWriteRhsUb_inFragment derefIdxWriteRhsUb_translate ctx0
    derefIdxWriteRhsUb_ctxOk [initArrU32_2] (by decide) derefIdxWriteRhsUbMInit rfl rfl rfl n

theorem derefIdxWriteRhsUb_minirust_direct :
    ubAfter derefIdxWriteRhsUb [initArrU32_2] 5 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- Writing an uninitialized rvalue through a valid `*mut` pointer to the
scalar field `_1.1: u32` of a `TupleSpec` struct parameter (`Padded`):
```text
StorageLive(_2); StorageLive(_3); _2 = &raw mut (_1.1: u32); (*_2) = copy _3;
_0 = copy (_1.1: u32); return
```
Completes the 3-way target case split of `derefWrite_target` alongside
`derefWriteRhsUb` (whole integer local) and `derefIdxWriteRhsUb` (`ConstantIndex`
array element): both semantics fault on the uninitialized RHS in the
`TupleSpec` field-chain branch of `derefWrite_target`. -/
def derefFieldWriteRhsUb : CapturedMir :=
  { ptrBody "witness::deref_field_write_rhs_ub"
      [u32Decl, paddedStructDecl, ptrMutU32Decl, u32Decl]
      [.storageLive 2, .storageLive 3,
       .assign (local_ 2) (.rawPtr .mut (placeField 1 [(1, u32Ty)])),
       .assign (derefPlace 2) (.use (.copy (local_ 3))),
       .assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)])))] with
    fnAbi := fnAbiPaddedArg, layouts := paddedLayouts }

theorem derefFieldWriteRhsUb_inFragment : inFragment derefFieldWriteRhsUb = true := by decide

def derefFieldWriteRhsUbFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, paddedMiniRustTy),
    (localName 2, thinRawPtrTy), (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .Assign (.Local (localName 2)) (.AddrOf (.Field (.Local (localName 1)) 1) (.Raw .None)),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32)) (.Load (.Local (localName 3))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem derefFieldWriteRhsUb_translate :
    translateFn derefFieldWriteRhsUb = some derefFieldWriteRhsUbFn := rfl

def derefFieldWriteRhsUbS0 : MachineState :=
  initMachineState derefFieldWriteRhsUb [initPaddedStruct]
def derefFieldWriteRhsUbMInit : Mach :=
  machine derefFieldWriteRhsUb derefFieldWriteRhsUbFn derefFieldWriteRhsUbS0.frame.locals
    derefFieldWriteRhsUbFn.start

theorem derefFieldWriteRhsUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree derefFieldWriteRhsUb [initPaddedStruct]) tr u ∧ FaultNow u :=
  faultsA_sound derefFieldWriteRhsUb 10 _ (by decide)

theorem derefFieldWriteRhsUb_ctxOk : CtxOk derefFieldWriteRhsUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : derefFieldWriteRhsUb.layouts = paddedLayouts := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [derefFieldWriteRhsUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [derefFieldWriteRhsUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : derefFieldWriteRhsUb.layouts = paddedLayouts := rfl
    rw [hlay]
    simp [derefFieldWriteRhsUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem derefFieldWriteRhsUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n derefFieldWriteRhsUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := derefFieldWriteRhsUb_anneal_ub
  exact mirCall_ub derefFieldWriteRhsUb_inFragment derefFieldWriteRhsUb_translate ctx0
    derefFieldWriteRhsUb_ctxOk [initPaddedStruct] (by decide) derefFieldWriteRhsUbMInit rfl rfl rfl
    hr hf

theorem derefFieldWriteRhsUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n derefFieldWriteRhsUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree derefFieldWriteRhsUb [initPaddedStruct]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k derefFieldWriteRhsUbMInit = .ok mRet ∧
      ReturnRel derefFieldWriteRhsUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree derefFieldWriteRhsUb [initPaddedStruct]) tr (.normal (v, mem))) :=
  mirCall_steps_error derefFieldWriteRhsUb_inFragment derefFieldWriteRhsUb_translate ctx0
    derefFieldWriteRhsUb_ctxOk [initPaddedStruct] (by decide) derefFieldWriteRhsUbMInit rfl rfl rfl
    herr

theorem derefFieldWriteRhsUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) derefFieldWriteRhsUbMInit = .ok m' ∧
      StateRelN derefFieldWriteRhsUb derefFieldWriteRhsUbFn ctx0 s' m' ∧
      Reaches (mirCallTree derefFieldWriteRhsUb [initPaddedStruct]) tr
        (mirTree derefFieldWriteRhsUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k derefFieldWriteRhsUbMInit = .ok mRet ∧
      ReturnRel derefFieldWriteRhsUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree derefFieldWriteRhsUb [initPaddedStruct]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) derefFieldWriteRhsUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree derefFieldWriteRhsUb [initPaddedStruct]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N derefFieldWriteRhsUb_inFragment derefFieldWriteRhsUb_translate ctx0
    derefFieldWriteRhsUb_ctxOk [initPaddedStruct] (by decide) derefFieldWriteRhsUbMInit rfl rfl rfl
    n

theorem derefFieldWriteRhsUb_minirust_direct :
    ubAfter derefFieldWriteRhsUb [initPaddedStruct] 5 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-! ## Dangling pointers -/

/-- MIR of a read through a pointer to a temporary after its `StorageDead`:
```text
StorageLive(_2); _2 = copy _1; StorageLive(_3); _3 = &raw const _2;
StorageDead(_2); _0 = copy (*_3); return
```
-/
def dangling : CapturedMir :=
  ptrBody "witness::dangling" [u32Decl, u32Decl, u32Decl, ptrConstU32Decl]
    [.storageLive 2, .assign (local_ 2) (.use (.copy (local_ 1))),
     .storageLive 3, .assign (local_ 3) (.rawPtr .not (local_ 2)),
     .storageDead 2,
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem dangling_notInFragment : inFragment dangling = false := by decide +kernel

theorem dangling_anneal_ub :
    ∃ tr u, Reaches (mirTree dangling (initMachineState dangling [.scalar ⟨5, 4⟩])) tr u ∧
      FaultNow u :=
  faultsA_sound dangling 30 _ (by decide)

theorem dangling_minirust_direct :
    ubAfter dangling [.scalar ⟨5, 4⟩] 7 = some "dereferencing pointer to dead allocation" := by
  decide +kernel

/-! ## Dereferencing offset pointers: Anneal reads the original target -/

/-- `usize::MAX`. -/
def usizeMax : Nat := 18446744073709551615

/-- MIR of
```rust
fn offset_deref(x: u32) -> u32 {
    let a = [x, 7];                   // _2 = [copy _1, const 7_u32]
    let p = &raw const a[0];          // _3 = &raw const _2[0 of 2]
    let q = unsafe { p.offset(k) };   // _4 = Offset(copy _3, const k_usize)
    unsafe { *q }                     // _0 = copy (*_4)
}
```
-/
def offsetDeref (k : Nat) : CapturedMir :=
  ptrBody "witness::offset_deref" [u32Decl, u32Decl, arrU32_2Decl, ptrConstU32Decl, ptrConstU32Decl]
    [.storageLive 2, .assign (local_ 2) (.aggregate (.array u32Ty) [.copy (local_ 1), constU32 7]),
     .storageLive 3, .assign (local_ 3) (.rawPtr .not (placeConstIdx 2 0 2 false)),
     .storageLive 4, .assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (constUsize k)),
     .assign (local_ 0) (.use (.copy (derefPlace 4)))]

/-- The MiniRust function `minimize` produces for `offsetDeref k`: `Offset`
counts in units of the pointee, so it becomes an in-bounds `PtrOffset` by the
byte count `k * 4`, computed by `MulUnchecked`. -/
def offsetDerefFn (k : Nat) : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Array (.Int u32) 2),
    (localName 3, thinRawPtrTy), (localName 4, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2))
        (.Tuple [.Load (.Local (localName 1)), .Constant (.Int 7) (.Int u32)] (.Array (.Int u32) 2)),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.AddrOf (.Index (.Local (localName 2)) (.Constant (.Int 0) (.Int usizeIt))) (.Raw .None)),
      .StorageLive (localName 4),
      .Assign (.Local (localName 4))
        (.BinOp (.PtrOffset true) (.Load (.Local (localName 3)))
          (.BinOp (.Int .MulUnchecked) (.Constant (.Int k) (.Int usizeIt))
            (.Constant (.Int 4) (.Int usizeIt)))),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem offsetDeref1_translate : translateFn (offsetDeref 1) = some (offsetDerefFn 1) := rfl
theorem offsetDeref2_translate : translateFn (offsetDeref 2) = some (offsetDerefFn 2) := rfl
theorem offsetDeref3_translate : translateFn (offsetDeref 3) = some (offsetDerefFn 3) := rfl
theorem offsetDerefMax_translate :
    translateFn (offsetDeref usizeMax) = some (offsetDerefFn usizeMax) := rfl

/-- `offsetDeref` is outside `inFragment` (`&raw const (_2[0 of 2])` borrows an
indexed array subplace, and `k ≠ 0` uses a non-zero `BinOp::Offset`). -/
theorem offsetDeref_notInFragment :
    ∀ k ∈ [0, 1, 2, 3, usizeMax], inFragment (offsetDeref k) = false := by decide +kernel

/-- Anneal's stride-scaled `BinOp::Offset` and array byte-offset dereference
return `a[0] = 5` for `k = 0` and `a[1] = 7` for `k = 1`, matching MiniRust. -/
theorem offsetDeref_anneal_ret :
    (∃ mem, ReachesRet (mirTree (offsetDeref 0) (initMachineState (offsetDeref 0) [.scalar ⟨5, 4⟩]))
      [] (.normal (.scalar ⟨5, 4⟩, mem))) ∧
    (∃ mem, ReachesRet (mirTree (offsetDeref 1) (initMachineState (offsetDeref 1) [.scalar ⟨5, 4⟩]))
      [] (.normal (.scalar ⟨7, 4⟩, mem))) :=
  ⟨⟨_, runA_sound (offsetDeref 0) 30 _ _ _ rfl⟩,
   ⟨_, runA_sound (offsetDeref 1) 30 _ _ _ rfl⟩⟩

/-- For `k ∈ {2, 3, usize::MAX}`, Anneal faults with UB (reading through
one-past-the-end `p.offset(2)`, out-of-bounds `p.offset(3)`, and overflowing
`p.offset(usize::MAX)`), matching MiniRust. -/
theorem offsetDeref_anneal_ub (k : Nat) (hk : k ∈ [2, 3, usizeMax]) :
    ∃ tr u,
      Reaches (mirTree (offsetDeref k) (initMachineState (offsetDeref k) [.scalar ⟨5, 4⟩])) tr u ∧
      FaultNow u := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact faultsA_sound (offsetDeref 2) 30 _ rfl
  · exact faultsA_sound (offsetDeref 3) 30 _ rfl
  · exact faultsA_sound (offsetDeref usizeMax) 30 _ rfl

/-- MiniRust reads `a[1] = 7` through `p.offset(1)`. -/
theorem offsetDeref1_minirust_direct :
    retAfter (offsetDeref 1) [.scalar ⟨5, 4⟩] 9 =
      some (some { retAlloc with data := scalarBytes u32 7 }, [1]) := by
  decide +kernel

/-- `p.offset(2)` is the one-past-the-end pointer of `a`, which MiniRust lets
the program compute (step 7) but not read through (step 8). -/
theorem offsetDeref2_minirust_direct :
    (startMachine (offsetDeref 2) [.scalar ⟨5, 4⟩]).bind (fun m => (Interp.steps 7 m).toOption.map
        (fun _ => ())) = some () ∧
      ubAfter (offsetDeref 2) [.scalar ⟨5, 4⟩] 8 =
        some "dereferencing pointer outside the bounds of its allocation" := by
  constructor <;> decide +kernel

/-- `p.offset(3)` leaves the allocation: UB at the offset itself (step 7). -/
theorem offsetDeref3_minirust_direct :
    ubAfter (offsetDeref 3) [.scalar ⟨5, 4⟩] 7 =
      some "dereferencing pointer outside the bounds of its allocation" := by
  decide +kernel

/-- `p.offset(usize::MAX)`: the byte count `usize::MAX * 4` overflows `usize`
(step 7). -/
theorem offsetDerefMax_minirust_direct :
    ubAfter (offsetDeref usizeMax) [.scalar ⟨5, 4⟩] 7 = some "overflow in unchecked mul" := by
  decide +kernel

/-! ## Misaligned dereference -/

/-- MIR of
```rust
fn misaligned(x: u32) -> u32 {
    let p = &raw const x;             // _2 = &raw const _1
    let b = p as *const u8;           // _3 = copy _2 as *const u8 (PtrToPtr)
    let c = unsafe { b.offset(1) };   // _4 = Offset(copy _3, const 1_usize)
    let q = c as *const u32;          // _5 = copy _4 as *const u32 (PtrToPtr)
    unsafe { *q }                     // _0 = copy (*_5)
}
```
-/
def misaligned : CapturedMir :=
  ptrBody "witness::misaligned"
    [u32Decl, u32Decl, ptrConstU32Decl, ptrConstU8Decl, ptrConstU8Decl, ptrConstU32Decl]
    [.storageLive 2, .assign (local_ 2) (.rawPtr .not (local_ 1)),
     .storageLive 3, .assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) ptrConstU8Ty),
     .storageLive 4, .assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (constUsize 1)),
     .storageLive 5, .assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) ptrConstU32Ty),
     .assign (local_ 0) (.use (.copy (derefPlace 5)))]

theorem misaligned_notInFragment : inFragment misaligned = false := by decide +kernel

/-- Anneal raises UB: `*q` has `offsetBytes = 1`, which fails `u32` alignment
(`checkTargetPlaceAlign`), matching MiniRust (`misaligned_minirust_direct`;
bundled across Anneal, `BasicMemory`, and `TreeBorrowsMemory` in
`misaligned_three_way_ub_agreement` in `RefWitness.lean`). -/
theorem misaligned_anneal_ub :
    ∃ tr u, Reaches (mirTree misaligned (initMachineState misaligned [.scalar ⟨5, 4⟩])) tr u ∧
      FaultNow u :=
  faultsA_sound misaligned 30 _ (by decide)

/-- MiniRust raises UB: the place `*q` is based on a pointer that is not
aligned for `u32`. -/
theorem misaligned_minirust_direct :
    ubAfter misaligned [.scalar ⟨5, 4⟩] 10 =
      some "loading from a place based on a misaligned pointer" := by
  decide +kernel

/-! ## Exposed addresses -/

/-- MIR of
```rust
fn expose_twice(x: u32) -> u32 {
    let p1 = &raw const x;            // _2 = &raw const _1
    let p2 = &raw const x;            // _3 = &raw const _1
    let e1 = p1.expose_provenance();  // _4 = copy _2 as usize (PointerExposeProvenance)
    let e2 = p2.expose_provenance();  // _5 = copy _3 as usize (PointerExposeProvenance)
    (e2 - e1) as u32                  // _6 = Sub(copy _5, copy _4); _0 = copy _6 as u32
}
```
-/
def exposeTwice : CapturedMir :=
  ptrBody "witness::expose_twice"
    [u32Decl, u32Decl, ptrConstU32Decl, ptrConstU32Decl, usizeDecl, usizeDecl, usizeDecl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6,
     .assign (local_ 2) (.rawPtr .not (local_ 1)),
     .assign (local_ 3) (.rawPtr .not (local_ 1)),
     .assign (local_ 4) (.cast .pointerExposeProvenance (.copy (local_ 2)) usizeTy),
     .assign (local_ 5) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy),
     .assign (local_ 6) (.binaryOp .sub (.copy (local_ 5)) (.copy (local_ 4))),
     .assign (local_ 0) (.cast .intToInt (.copy (local_ 6)) u32Ty)]

/-- `translateFn` does not translate `PointerExposeProvenance`. -/
theorem exposeTwice_translate : (translateFn exposeTwice).isNone = true := by decide +kernel

theorem exposeTwice_notInFragment : inFragment exposeTwice = false := by decide +kernel

set_option maxRecDepth 200000 in
/-- Anneal returns `0`: both `p1` (tag `1`) and `p2` (tag `2`) borrow `_1` at
offset `0`, so `PointerExposeProvenance` exposes the same canonical stack
address `(stackLocalAddrPageBase 8 + 1) * 65536` while recording `exposedAllocIds = [2, 1]`. -/
theorem exposeTwice_anneal_ret :
    ReachesRet (mirTree exposeTwice (initMachineState exposeTwice [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨0, 4⟩,
        { (initMachineState exposeTwice [.scalar ⟨5, 4⟩]).memory with
          borrows := [rawPtrEntry 2 .not (local_ 1), rawPtrEntry 1 .not (local_ 1)],
          exposedAllocIds := [2, 1],
          nextTag := 3 })) :=
  runA_sound exposeTwice 30 _ _ _ rfl

/-- `minimize`'s translation of `exposeTwice`: each `PointerExposeProvenance`
cast ends its block with a `PointerExposeProvenance` intrinsic call whose
continuation is a fresh block (`bb2`, `bb3`, after the init block `bb1`)
holding the rest of the statements. -/
def exposeTwiceFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, thinRawPtrTy),
    (localName 3, thinRawPtrTy), (localName 4, .Int usizeIt), (localName 5, .Int usizeIt),
    (localName 6, .Int usizeIt)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5), .StorageLive (localName 6),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 1)) (.Raw .None))],
      .Intrinsic .PointerExposeProvenance [.Load (.Local (localName 2))] (.Local (localName 4))
        (some (bbName 2)), .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩),
    (bbName 2, ⟨[], .Intrinsic .PointerExposeProvenance [.Load (.Local (localName 3))]
        (.Local (localName 5)) (some (bbName 3)), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 6))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 5))) (.Load (.Local (localName 4)))),
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 6))))],
      .Return, .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

/-- MiniRust returns `0`: both pointers have the address of `x`. -/
theorem exposeTwice_minirust_direct :
    (Interp.steps 13 (machine exposeTwice exposeTwiceFn
        (initMachineState exposeTwice [.scalar ⟨5, 4⟩]).frame.locals exposeTwiceFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 0 }, [1]) := by
  decide +kernel

/-! ## Aliasing: Anneal's Tree Borrows entries -/

/-- MIR of
```text
StorageLive(_2); _2 = &raw mut _1; _1 = const 9_u32; _0 = copy (*_2); return
```
-/
def directWrite : CapturedMir :=
  ptrBody "witness::direct_write" [u32Decl, u32Decl, ptrMutU32Decl]
    [.storageLive 2, .assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (local_ 1) (.use (constU32 9)),
     .assign (local_ 0) (.use (.copy (derefPlace 2)))]

theorem directWrite_notInFragment : inFragment directWrite = false := by decide +kernel

/-- Anneal: the direct write to `_1` disables the entry of `_2`, so the read
through `_2` is UB. -/
theorem directWrite_anneal_ub :
    ∃ tr u, Reaches (mirTree directWrite (initMachineState directWrite [.scalar ⟨5, 4⟩])) tr u ∧
      FaultNow u :=
  faultsA_sound directWrite 30 _ (by decide)

/-- MiniRust reads `9`. -/
theorem directWrite_minirust_direct :
    retAfter directWrite [.scalar ⟨5, 4⟩] 6 =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

/-- MIR of
```text
StorageLive(_2); _2 = &raw const _1; StorageLive(_3); _3 = copy _2 as *mut u32;
(*_3) = const 9_u32; _0 = copy _1; return
```
-/
def frozenWrite : CapturedMir :=
  ptrBody "witness::frozen_write" [u32Decl, u32Decl, ptrConstU32Decl, ptrMutU32Decl]
    [.storageLive 2, .assign (local_ 2) (.rawPtr .not (local_ 1)),
     .storageLive 3, .assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) ptrMutU32Ty),
     .assign (derefPlace 3) (.use (constU32 9)),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem frozenWrite_notInFragment : inFragment frozenWrite = false := by decide +kernel

/-- Anneal: the write through the `Frozen` entry of `&raw const _1` is UB. -/
theorem frozenWrite_anneal_ub :
    ∃ tr u, Reaches (mirTree frozenWrite (initMachineState frozenWrite [.scalar ⟨5, 4⟩])) tr u ∧
      FaultNow u :=
  faultsA_sound frozenWrite 30 _ (by decide)

/-- MiniRust stores `9` into `x` and returns it. -/
theorem frozenWrite_minirust_direct :
    retAfter frozenWrite [.scalar ⟨5, 4⟩] 8 =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

/-! ## Ground truth for the pointer primitives -/

/-- Accessing memory through a pointer without provenance (for instance the
null pointer) is UB, unless the access is zero-sized. -/
theorem checkPtr_null (mem : BM) :
    BM.check_ptr mem { addr := 0, provenance := none } ⟨4⟩ =
        .error (.ub "dereferencing pointer without provenance") ∧
      BM.check_ptr mem { addr := 0, provenance := none } ⟨0⟩ = .ok none :=
  ⟨rfl, rfl⟩

/-- `PtrOffset { inbounds: false }` wraps around the address space and keeps
the provenance. -/
theorem ptrOffsetWrapping_wraps (prov : Option Prov) :
    ptrOffsetWrapping { addr := 5, provenance := prov } (-10) =
      { addr := 18446744073709551611, provenance := prov } := by
  simp [ptrOffsetWrapping, ThinPointer.wrapping_offset, bringInBounds, two_pow_ptrBits]

/-- The thin pointer value `⟨addr, prov⟩`. -/
def thinPtrVal (addr : Int) (prov : Option Prov) : Val :=
  .Ptr { thin_pointer := { addr := addr, provenance := prov }, metadata := none }

/-- `Value::Ptr` at a thin raw pointer type accepts exactly the addresses in
`[0, 2^64)` (`checkValue_thinRawPtr`, `checkValue_thinRawPtr_oob`). -/
theorem checkValue_thinRawPtr_bounds (prov : Option Prov) :
    checkValue (thinPtrVal 18446744073709551615 prov) thinRawPtrTy = .ok () ∧
      checkValue (thinPtrVal 18446744073709551616 prov) thinRawPtrTy =
        .error (.ub "Value::Ptr: pointer out-of-bounds") ∧
      checkValue (thinPtrVal (-1) prov) thinRawPtrTy =
        .error (.ub "Value::Ptr: pointer out-of-bounds") :=
  ⟨checkValue_thinRawPtr 18446744073709551615 (by decide) prov,
   checkValue_thinRawPtr_oob _ (by decide) prov,
   checkValue_thinRawPtr_oob _ (by decide) prov⟩

end MiniRustSpec.Correspondence.PointerWitness
