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

Concrete MIR bodies with raw pointers, each run to completion in Anneal's
semantics (`runA_sound`, `faultsA_sound`) and, after `minimize`'s translation
(`translateFn`), in the MiniRust interpretation (`Interp.steps`), both by kernel
computation (`rfl`, `decide`, `decide +kernel`; no `native_decide`). The
correspondence fragment (`inFragment`) does not admit raw pointers yet
(`ptrRoundTrip_notInFragment`), so these are independent executions of the two
semantics rather than instances of `step_correspondence`.

**Agreement.** Both semantics return the same value for

* `ptrRoundTrip`: `&raw mut x`, a read and a write through the pointer, a
  `PtrToPtr` cast to `*const u32`, and a read through the cast pointer;
* `arrayElemPtr`: `&raw mut a[1]` (`ConstantIndex`) on a `[u32; 2]` temporary,
  read and written through the pointer;
* `fieldPtr`: `&raw mut s.1` on the padded struct `Padded(u8, u32, u16)` (field
  at byte offset `4`), read and written through the pointer;

and both raise UB for `dangling`, a read through a pointer to a temporary after
its `StorageDead`.

**Divergence, Anneal unsound.** Anneal returns a value where MiniRust, the
ground truth, returns a different value or raises UB:

* `offsetDeref 1`: `*a[0..].offset(1)` reads `a[1]` in MiniRust and `a[0]` in
  Anneal, whose dereference ignores the pointer's offset;
* `offsetDeref 2`: the one-past-the-end pointer may be computed, but reading
  through it is UB in MiniRust;
* `offsetDeref 3`: computing a pointer beyond one-past-the-end is UB in
  MiniRust (`ptr_offset_inbounds`);
* `offsetDeref usizeMax`: the byte count `usize::MAX * 4` overflows, which is UB
  in MiniRust (`MulUnchecked`);
* `misaligned`: reading a `u32` through a pointer one byte into a `u32` is UB in
  MiniRust;
* `exposeTwice`: two `&raw const x` expose the same address in MiniRust, but
  addresses `65536` apart in Anneal, whose exposed address encodes the borrow
  tag. `minimize` translates `PointerExposeProvenance` into an intrinsic call
  terminator after splitting the block, which `translateFn` does not do yet
  (`exposeTwice_translate`); `exposeTwiceFn` spells out that translation.

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
def ptrConstU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
def ptrConstU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
def ptrMutU32Decl : LocalDecl := { mutability := .mut, ty := ptrMutU32Ty, debugName := none }
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

/-- The correspondence fragment does not admit raw pointers yet. -/
theorem ptrRoundTrip_notInFragment : inFragment ptrRoundTrip = false := by decide

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

/-- MiniRust returns `6` too, after ten steps (the init block's `Goto`, nine
statements, and `Return`). -/
theorem ptrRoundTrip_minirust_direct :
    retAfter ptrRoundTrip [.scalar ⟨5, 4⟩] 10 =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1]) := by
  decide +kernel

/-! ## `&raw mut a[1]` on an array -/

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

theorem fieldPtr_anneal_ret :
    ∃ mem, ReachesRet (mirTree fieldPtr (initMachineState fieldPtr [initPaddedStruct])) []
      (.normal (.scalar ⟨100, 4⟩, mem)) :=
  ⟨_, runA_sound fieldPtr 30 _ _ _ rfl⟩

theorem fieldPtr_minirust_direct :
    retAfter fieldPtr [initPaddedStruct] 8 =
      some (some { retAlloc with data := scalarBytes u32 100 }, [1]) := by
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

/-- Anneal returns `a[0] = x` for every offset `k ∈ {0, 1, 2, 3, usize::MAX}`:
`Offset` adds the raw count to the pointer's `offsetBytes`, and the
dereference reads the borrow entry's place `_2[0 of 2]` regardless. -/
theorem offsetDeref_anneal_ret (k : Nat) (hk : k ∈ [0, 1, 2, 3, usizeMax]) :
    ∃ mem, ReachesRet (mirTree (offsetDeref k) (initMachineState (offsetDeref k) [.scalar ⟨5, 4⟩]))
      [] (.normal (.scalar ⟨5, 4⟩, mem)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, runA_sound (offsetDeref 0) 30 _ _ _ rfl⟩
  · exact ⟨_, runA_sound (offsetDeref 1) 30 _ _ _ rfl⟩
  · exact ⟨_, runA_sound (offsetDeref 2) 30 _ _ _ rfl⟩
  · exact ⟨_, runA_sound (offsetDeref 3) 30 _ _ _ rfl⟩
  · exact ⟨_, runA_sound (offsetDeref usizeMax) 30 _ _ _ rfl⟩

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

/-- Anneal returns `x`. -/
theorem misaligned_anneal_ret :
    ∃ mem, ReachesRet (mirTree misaligned (initMachineState misaligned [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨5, 4⟩, mem)) :=
  ⟨_, runA_sound misaligned 30 _ _ _ rfl⟩

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

set_option maxRecDepth 200000 in
/-- Anneal returns `65536`: the two pointers carry the borrow tags `1` and `2`,
and `PointerExposeProvenance` returns `tag * 65536 + offsetBytes`. -/
theorem exposeTwice_anneal_ret :
    ReachesRet (mirTree exposeTwice (initMachineState exposeTwice [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨65536, 4⟩,
        { (initMachineState exposeTwice [.scalar ⟨5, 4⟩]).memory with
          borrows := [rawPtrEntry 2 .not (local_ 1), rawPtrEntry 1 .not (local_ 1)],
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
