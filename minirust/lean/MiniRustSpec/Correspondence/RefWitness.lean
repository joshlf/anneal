/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.PointerWitness

/-!
# Reference, reborrowing, transmute, and Tree Borrows witnesses (MR-3.2)

Concrete MIR bodies and ground-truth execution witnesses exercising safe
references (`&T`, `&mut T`), two-phase mutable borrows (`BorrowKind.mut true`),
multi-step reborrowing chains, `StatementKind.retag` (`Statement.Validate`),
cross-kind pointer/reference `CastKind.transmute`, safe-pointer validity checks,
RFC 2582 raw place addressing (`Rvalue.rawPtr`), provenance-faithful scalar-to-pointer
transmute byte decoding (`decodeScalarBytes`), and Tree Borrows permissions
(`ReborrowSettings` and `TreeBorrowsMemory`) across
three semantics:

1. **Anneal's MIR semantics** (`runA_sound`, `faultsA_sound`),
2. **MiniRust `Machine<BasicMemory<x86_64>>` (`Mach`)** (`retAfter`, `ubAfter`,
   plus symbolic correspondence via `mirCall_ret` / `mirCall_ub`), and
3. **MiniRust `Machine<TreeBorrowsMemory<x86_64>>` (`MachTB`)** (`retAfterTB`,
   `ubAfterTB`, executing `stepTB` / `stepsTB` directly on `translateFn` output).
-/

namespace MiniRustSpec.Correspondence.RefWitness

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

/-! ## MR-3.2: References, Reborrowing, Safe-Pointer Checks, and Tree Borrows Permissions -/

def refSharedU32Ty : Ty := { kind := .ref .not (.uint .u32), layoutIdx := 0 }
def refMutU32Ty : Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }
def refSharedU16Ty : Ty := { kind := .ref .not (.uint .u16), layoutIdx := 0 }
def refSharedU32Decl : LocalDecl := { mutability := .mut, ty := refSharedU32Ty, debugName := none }
def refMutU32Decl : LocalDecl := { mutability := .mut, ty := refMutU32Ty, debugName := none }
def refSharedU16Decl : LocalDecl := { mutability := .mut, ty := refSharedU16Ty, debugName := none }

/-- Lift a `BasicMemory` provenance `(id, ())` to its root `TreeBorrowsProvenance` `(id, [])`. -/
def liftProvTB (p : Prov) : Gen.TreeBorrowsProvenance := (p.1, [])

/-- Lift an `AbstractByte` from `BasicMemory` provenance to `TreeBorrowsProvenance`. -/
def liftByteTB : Byte → Gen.AbstractByte Gen.TreeBorrowsProvenance
  | .Uninit => .Uninit
  | .Init b pf =>
    .Init b (pf.map fun f => { provenance := liftProvTB f.provenance, position := f.position })

/-- Lift a `BasicMemory` allocation to a `TreeBorrowsMemory` allocation with a fresh
unprotected `Unique` root node (`TreeBorrowsMemory::allocate`, `spec/mem/tree_borrows/memory.md`). -/
def liftAllocTB (a : Gen.Allocation) :
    Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
  { data := a.data.map liftByteTB
    addr := a.addr
    align := a.align
    kind := a.kind
    live := a.live
    extra := { root := { children := []
                         permissions := List.replicate a.data.length (.Unprot .Unique)
                         «protected» := .No } } }

/-- Lift a `BasicMemory` thin pointer to a `TreeBorrowsMemory` thin pointer. -/
def liftThinPtrTB (p : Ptr) : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
  { addr := p.addr, provenance := p.provenance.map liftProvTB }

/-- Lift a `StackPopAction` from `BM` to `TBM`. -/
def liftStackPopActionTB : Gen.StackPopAction BM → Gen.StackPopAction TBM
  | .BottomOfStack => .BottomOfStack
  | .BackToCaller nb ub ptr => .BackToCaller nb ub (liftThinPtrTB ptr)

/-- Lift a `StackFrame` from `BM` to `TBM` with empty `TreeBorrowsFrameExtra` (`new_call`). -/
def liftFrameTB (fr : Frame) : Gen.StackFrame TBM :=
  { func := fr.func
    locals := ⟨fr.locals.entries.map fun (k, p) => (k, liftThinPtrTB p)⟩
    stack_pop_action := liftStackPopActionTB fr.stack_pop_action
    next_block := fr.next_block
    next_stmt := fr.next_stmt
    extra := TreeBorrowsMemory.new_call }

/-- Lift a `Thread` from `BM` to `TBM`. -/
def liftThreadTB (th : Gen.Thread BM) : Gen.Thread TBM :=
  { stack := th.stack.map liftFrameTB
    state := th.state
    unwind_payloads := th.unwind_payloads.map liftThinPtrTB }

/-- Lift a `BasicMemory` `Mach` state at function entry to `MachTB`
(`Machine<TreeBorrowsMemory<x86_64>>` with `implicit_writes = true`). -/
def liftMachToTB (m : Mach) : MachTB :=
  { prog := m.prog
    mem := { memory := { params := ⟨true⟩
                         mem := { allocations := m.mem.memory.allocations.map liftAllocTB
                                  _phantom := {} } }
             accesses := m.mem.accesses }
    intptrcast := ⟨⟨m.intptrcast.exposed.elems.map liftProvTB⟩⟩
    threads := m.threads.map liftThreadTB
    active_thread := m.active_thread
    synchronized_threads := m.synchronized_threads
    locks := m.locks
    global_ptrs := ⟨m.global_ptrs.entries.map fun (k, p) => (k, liftThinPtrTB p)⟩
    fn_ptrs := ⟨m.fn_ptrs.entries.map fun (k, p) => (k, liftThinPtrTB p)⟩
    vtable_ptrs := ⟨m.vtable_ptrs.entries.map fun (k, p) => (k, liftThinPtrTB p)⟩
    stdout := m.stdout
    stderr := m.stderr }

/-- The `MachTB` machine running `minimize`'s translation of `body` from its
start, with the Anneal arguments `args`, under `ctx0` and `TreeBorrowsMemory`. -/
def startMachineTB (body : CapturedMir) (args : List Value) : Option MachTB :=
  (startMachine body args).map liftMachToTB

/-- Lossless decidable representation of `AbstractByte TreeBorrowsProvenance` preserving
initialization, byte value, and `(alloc_id, path, position)` provenance. -/
inductive TBByteOutcome : Type where
  | uninit
  | initNoProv (val : UInt8)
  | initProv (val : UInt8) (allocId : Int) (path : List Int) (pos : Int)
deriving DecidableEq

/-- Project an `AbstractByte TreeBorrowsProvenance` losslessly to `TBByteOutcome`. -/
def projByteTB : Gen.AbstractByte Gen.TreeBorrowsProvenance → TBByteOutcome
  | .Uninit => .uninit
  | .Init b none => .initNoProv b
  | .Init b (some f) => .initProv b f.provenance.1._0 f.provenance.2 f.position

/-- Decidable caller-return snapshot after running `MachTB`. -/
structure TBRetOutcome : Type where
  retAlloc : Option (Bool × List TBByteOutcome)
  stackDepths : List Nat
deriving DecidableEq

/-- Caller return allocation `(live, data)` and stack depths after `n`
`TreeBorrowsMemory` machine steps (`stepsTB`) from `startMachineTB body args`. -/
def retAfterTB (body : CapturedMir) (args : List Value) (n : Nat) :
    Option TBRetOutcome :=
  (startMachineTB body args).bind fun m =>
    (Interp.stepsTB n m).toOption.map
      (fun m' =>
        { retAlloc := m'.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
          stackDepths := m'.threads.map (·.stack.length) })

/-- Expected `retAfterTB` outcome when the callee returns scalar `u32` value `v`
into `retAlloc` and pops back to the single caller frame. -/
def tbRetU32 (v : Nat) : Option TBRetOutcome :=
  some { retAlloc := some (true, (scalarBytes u32 v).map (projByteTB ∘ liftByteTB))
         stackDepths := [1] }

/-- The UB message of the `n`-th `TreeBorrowsMemory` machine step (`stepsTB`)
from `startMachineTB body args`, if it raises UB. -/
def ubAfterTB (body : CapturedMir) (args : List Value) (n : Nat) : Option String :=
  (startMachineTB body args).bind fun m =>
    match Interp.stepsTB n m with
    | .error (.ub msg) => some msg
    | _ => none

/-- MIR of shared reference creation, `copy`, `move`, and dereference read:
```rust
fn ref_shared_read(x: u32) -> u32 {
    let r1 = &x;        // _2 = &_1
    let r2 = r1;        // _3 = copy _2
    let r3 = r2;        // _4 = move _3
    *r3                 // _0 = copy (*_4)
}
```
-/
def refSharedRead : CapturedMir :=
  ptrBody "witness::ref_shared_read"
    [u32Decl, u32Decl, refSharedU32Decl, refSharedU32Decl, refSharedU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4,
     .assign (local_ 2) (.ref .shared (local_ 1)),
     .assign (local_ 3) (.use (.copy (local_ 2))),
     .assign (local_ 4) (.use (.move (local_ 3))),
     .assign (local_ 0) (.use (.copy (derefPlace 4)))]

theorem refSharedRead_inFragment : inFragment refSharedRead = true := by decide

def refSharedReadFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .not u32), (localName 3, refTy .not u32), (localName 4, refTy .not u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3), .StorageLive (localName 4),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .not u32)),
      .Assign (.Local (localName 3)) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 4)) (.Load (.Local (localName 3))),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem refSharedRead_translate : translateFn refSharedRead = some refSharedReadFn := rfl

def refSharedReadS0 : MachineState := initMachineState refSharedRead [.scalar ⟨5, 4⟩]
def refSharedReadMInit : Mach :=
  machine refSharedRead refSharedReadFn refSharedReadS0.frame.locals refSharedReadFn.start

theorem refSharedRead_anneal_ret :
    ReachesRet (mirTree refSharedRead refSharedReadS0) []
      (.normal (.scalar ⟨5, 4⟩,
        { refSharedReadS0.memory with borrows := [rawPtrEntry 1 .not (local_ 1)], nextTag := 2 })) :=
  runA_sound refSharedRead 30 _ _ _ rfl

theorem refSharedRead_noUB :
    MirNoUBTree (mirCallTree refSharedRead [.scalar ⟨5, 4⟩]) :=
  runA_noUB refSharedRead 30 _ _ _ rfl

theorem refSharedRead_minirust_direct :
    retAfter refSharedRead [.scalar ⟨5, 4⟩] 9 =
      some (some { retAlloc with data := scalarBytes u32 5 }, [1]) := by
  decide +kernel

theorem refSharedRead_ctxOk : CtxOk refSharedRead ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : refSharedRead.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [refSharedRead, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [refSharedRead, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : refSharedRead.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [refSharedRead, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem refSharedRead_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n refSharedReadMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 5 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret refSharedRead_inFragment refSharedRead_translate ctx0 refSharedRead_ctxOk
      [.scalar ⟨5, 4⟩] (by decide) refSharedReadMInit rfl rfl rfl refSharedRead_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [refSharedRead, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem refSharedRead_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n refSharedReadMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k refSharedReadMInit = .ok mRet ∧
      ReturnRel refSharedRead ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refSharedRead [.scalar ⟨5, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB refSharedRead_inFragment refSharedRead_translate ctx0 refSharedRead_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) refSharedReadMInit rfl rfl rfl refSharedRead_noUB herr

theorem refSharedRead_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) refSharedReadMInit = .ok m' ∧
      StateRelN refSharedRead refSharedReadFn ctx0 s' m' ∧
      Reaches (mirCallTree refSharedRead [.scalar ⟨5, 4⟩]) tr (mirTree refSharedRead s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k refSharedReadMInit = .ok mRet ∧
      ReturnRel refSharedRead ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refSharedRead [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N refSharedRead_inFragment refSharedRead_translate ctx0 refSharedRead_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) refSharedReadMInit rfl rfl rfl refSharedRead_noUB n

/-- MIR of `&mut x`, deref read/write, shared reborrow `&*r`, raw reborrow `&raw const *s`,
and deref read:
```rust
fn ref_mut_round_trip(mut x: u32) -> u32 {
    let r = &mut x;           // _2 = &mut _1
    let t = *r;               // _3 = copy (*_2)
    *r = t + 1;               // (*_2) = Add(copy _3, const 1_u32)
    let s = &*r;              // _4 = &(*_2)
    let p = &raw const *s;    // _5 = &raw const (*_4)
    unsafe { *p }             // _0 = copy (*_5)
}
```
-/
def refMutRoundTrip : CapturedMir :=
  ptrBody "witness::ref_mut_round_trip"
    [u32Decl, u32Decl, refMutU32Decl, u32Decl, refSharedU32Decl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.use (.copy (derefPlace 2))),
     .assign (derefPlace 2) (.binaryOp .add (.copy (local_ 3)) (constU32 1)),
     .assign (local_ 4) (.ref .shared (derefPlace 2)),
     .assign (local_ 5) (.rawPtr .not (derefPlace 4)),
     .assign (local_ 0) (.use (.copy (derefPlace 5)))]

theorem refMutRoundTrip_inFragment : inFragment refMutRoundTrip = true := by decide

def refMutRoundTripFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, .Int u32),
    (localName 4, refTy .not u32), (localName 5, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Local (localName 3)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 3))) (.Constant (.Int 1) (.Int u32))),
      .Assign (.Local (localName 4))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Local (localName 5))
        (.AddrOf (.Deref (.Load (.Local (localName 4))) (.Int u32)) (.Raw .None)),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 5))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem refMutRoundTrip_translate : translateFn refMutRoundTrip = some refMutRoundTripFn := rfl

def refMutRoundTripS0 : MachineState := initMachineState refMutRoundTrip [.scalar ⟨5, 4⟩]
def refMutRoundTripMInit : Mach :=
  machine refMutRoundTrip refMutRoundTripFn refMutRoundTripS0.frame.locals refMutRoundTripFn.start

theorem refMutRoundTrip_anneal_ret :
    ReachesRet (mirTree refMutRoundTrip refMutRoundTripS0) []
      (.normal (.scalar ⟨6, 4⟩,
        { refMutRoundTripS0.memory with
          borrows := [{ rawPtrEntry 2 .not (local_ 1) with parentTag := some 1 },
                      rawPtrEntry 1 .mut (local_ 1)],
          nextTag := 3 })) :=
  runA_sound refMutRoundTrip 30 _ _ _ rfl

theorem refMutRoundTrip_noUB :
    MirNoUBTree (mirCallTree refMutRoundTrip [.scalar ⟨5, 4⟩]) :=
  runA_noUB refMutRoundTrip 30 _ _ _ rfl

theorem refMutRoundTrip_minirust_direct :
    retAfter refMutRoundTrip [.scalar ⟨5, 4⟩] 12 =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1]) := by
  decide +kernel

theorem refMutRoundTrip_ctxOk : CtxOk refMutRoundTrip ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : refMutRoundTrip.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [refMutRoundTrip, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [refMutRoundTrip, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : refMutRoundTrip.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [refMutRoundTrip, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem refMutRoundTrip_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n refMutRoundTripMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret refMutRoundTrip_inFragment refMutRoundTrip_translate ctx0 refMutRoundTrip_ctxOk
      [.scalar ⟨5, 4⟩] (by decide) refMutRoundTripMInit rfl rfl rfl refMutRoundTrip_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [refMutRoundTrip, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem refMutRoundTrip_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n refMutRoundTripMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k refMutRoundTripMInit = .ok mRet ∧
      ReturnRel refMutRoundTrip ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refMutRoundTrip [.scalar ⟨5, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB refMutRoundTrip_inFragment refMutRoundTrip_translate ctx0 refMutRoundTrip_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) refMutRoundTripMInit rfl rfl rfl refMutRoundTrip_noUB herr

theorem refMutRoundTrip_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) refMutRoundTripMInit = .ok m' ∧
      StateRelN refMutRoundTrip refMutRoundTripFn ctx0 s' m' ∧
      Reaches (mirCallTree refMutRoundTrip [.scalar ⟨5, 4⟩]) tr (mirTree refMutRoundTrip s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k refMutRoundTripMInit = .ok mRet ∧
      ReturnRel refMutRoundTrip ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refMutRoundTrip [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N refMutRoundTrip_inFragment refMutRoundTrip_translate ctx0 refMutRoundTrip_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) refMutRoundTripMInit rfl rfl rfl refMutRoundTrip_noUB n

/-- Disjoint `&mut` borrows on an array parameter `[u32; 2]` (`a = [5, 7]`),
writes through both mutable references (`15`, `27`), and a five-step reborrowing
chain (`&mut -> &mut -> & -> & -> *const` and `&mut -> *mut`) returning `42`. -/
def refArrayReborrowChain : CapturedMir :=
  { ptrBody "witness::ref_array_reborrow_chain"
      [u32Decl, arrU32_2Decl,
       refMutU32Decl, refMutU32Decl, refMutU32Decl, refSharedU32Decl, refSharedU32Decl,
       ptrMutU32Decl, ptrConstU32Decl, u32Decl, u32Decl, u32Decl, u32Decl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6,
       .storageLive 7, .storageLive 8, .storageLive 9, .storageLive 10,
       .storageLive 11, .storageLive 12,
       .assign (local_ 2) (.ref (.mut false) (placeConstIdx 1 0 2 false)),
       .assign (local_ 3) (.ref (.mut false) (placeConstIdx 1 1 2 false)),
       .assign (local_ 9) (.use (.copy (derefPlace 2))),
       .assign (local_ 10) (.use (.copy (derefPlace 3))),
       .assign (derefPlace 2) (.binaryOp .add (.copy (local_ 9)) (constU32 10)),
       .assign (derefPlace 3) (.binaryOp .add (.copy (local_ 10)) (constU32 20)),
       .assign (local_ 4) (.ref (.mut false) (derefPlace 2)),
       .assign (local_ 5) (.ref .shared (derefPlace 4)),
       .assign (local_ 6) (.ref .shared (derefPlace 5)),
       .assign (local_ 7) (.rawPtr .mut (derefPlace 3)),
       .assign (local_ 8) (.rawPtr .not (derefPlace 6)),
       .assign (local_ 11) (.use (.copy (derefPlace 8))),
       .assign (local_ 12) (.use (.copy (derefPlace 7))),
       .assign (local_ 0) (.binaryOp .add (.copy (local_ 11)) (.copy (local_ 12)))] with
    fnAbi := fnAbiArrU32_2Arg }

theorem refArrayReborrowChain_inFragment : inFragment refArrayReborrowChain = true := by decide

def refArrayReborrowChainFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Array (.Int u32) 2),
    (localName 2, refTy .mut u32), (localName 3, refTy .mut u32),
    (localName 4, refTy .mut u32), (localName 5, refTy .not u32),
    (localName 6, refTy .not u32), (localName 7, thinRawPtrTy),
    (localName 8, thinRawPtrTy), (localName 9, .Int u32),
    (localName 10, .Int u32), (localName 11, .Int u32), (localName 12, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3), .StorageLive (localName 4),
      .StorageLive (localName 5), .StorageLive (localName 6), .StorageLive (localName 7),
      .StorageLive (localName 8), .StorageLive (localName 9), .StorageLive (localName 10),
      .StorageLive (localName 11), .StorageLive (localName 12),
      .Assign (.Local (localName 2))
        (.AddrOf (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt)))
          (refPtrType .mut u32)),
      .Assign (.Local (localName 3))
        (.AddrOf (.Index (.Local (localName 1)) (.Constant (.Int 1) (.Int usizeIt)))
          (refPtrType .mut u32)),
      .Assign (.Local (localName 9)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Local (localName 10)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 9))) (.Constant (.Int 10) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 3))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 10))) (.Constant (.Int 20) (.Int u32))),
      .Assign (.Local (localName 4))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .mut u32)),
      .Assign (.Local (localName 5))
        (.AddrOf (.Deref (.Load (.Local (localName 4))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Local (localName 6))
        (.AddrOf (.Deref (.Load (.Local (localName 5))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Local (localName 7))
        (.AddrOf (.Deref (.Load (.Local (localName 3))) (.Int u32)) (.Raw .None)),
      .Assign (.Local (localName 8))
        (.AddrOf (.Deref (.Load (.Local (localName 6))) (.Int u32)) (.Raw .None)),
      .Assign (.Local (localName 11)) (.Load (.Deref (.Load (.Local (localName 8))) (.Int u32))),
      .Assign (.Local (localName 12)) (.Load (.Deref (.Load (.Local (localName 7))) (.Int u32))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 11))) (.Load (.Local (localName 12))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem refArrayReborrowChain_translate :
    translateFn refArrayReborrowChain = some refArrayReborrowChainFn := rfl

def refArrayReborrowChainS0 : MachineState :=
  initMachineState refArrayReborrowChain [initArrU32_2]
def refArrayReborrowChainMInit : Mach :=
  machine refArrayReborrowChain refArrayReborrowChainFn
    refArrayReborrowChainS0.frame.locals refArrayReborrowChainFn.start

theorem refArrayReborrowChain_anneal_ret :
    ReachesRet (mirTree refArrayReborrowChain refArrayReborrowChainS0) []
      (.normal (.scalar ⟨42, 4⟩,
        { refArrayReborrowChainS0.memory with
          borrows := [{ rawPtrEntry 5 .not (placeConstIdx 1 0 2 false) with parentTag := some 4 },
                      { rawPtrEntry 4 .not (placeConstIdx 1 0 2 false) with parentTag := some 3 },
                      { rawPtrEntry 3 .mut (placeConstIdx 1 0 2 false) with
                          perm := .reserved, parentTag := some 1 },
                      rawPtrEntry 2 .mut (placeConstIdx 1 1 2 false),
                      rawPtrEntry 1 .mut (placeConstIdx 1 0 2 false)],
          nextTag := 6 })) :=
  runA_sound refArrayReborrowChain 60 _ _ _ rfl

theorem refArrayReborrowChain_noUB :
    MirNoUBTree (mirCallTree refArrayReborrowChain [initArrU32_2]) :=
  runA_noUB refArrayReborrowChain 60 _ _ _ rfl

theorem refArrayReborrowChain_minirust_direct :
    retAfter refArrayReborrowChain [initArrU32_2] 27 =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) := by
  decide +kernel

theorem refArrayReborrowChain_ctxOk : CtxOk refArrayReborrowChain ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : refArrayReborrowChain.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [refArrayReborrowChain, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [refArrayReborrowChain, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : refArrayReborrowChain.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [refArrayReborrowChain, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem refArrayReborrowChain_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n refArrayReborrowChainMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret refArrayReborrowChain_inFragment refArrayReborrowChain_translate ctx0
      refArrayReborrowChain_ctxOk [initArrU32_2] (by decide) refArrayReborrowChainMInit
      rfl rfl rfl refArrayReborrowChain_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [refArrayReborrowChain, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem refArrayReborrowChain_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n refArrayReborrowChainMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k refArrayReborrowChainMInit = .ok mRet ∧
      ReturnRel refArrayReborrowChain ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refArrayReborrowChain [initArrU32_2]) tr (.normal (v, mem)) :=
  mirCall_noUB refArrayReborrowChain_inFragment refArrayReborrowChain_translate ctx0
    refArrayReborrowChain_ctxOk [initArrU32_2] (by decide) refArrayReborrowChainMInit
    rfl rfl rfl refArrayReborrowChain_noUB herr

theorem refArrayReborrowChain_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) refArrayReborrowChainMInit = .ok m' ∧
      StateRelN refArrayReborrowChain refArrayReborrowChainFn ctx0 s' m' ∧
      Reaches (mirCallTree refArrayReborrowChain [initArrU32_2]) tr
        (mirTree refArrayReborrowChain s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k refArrayReborrowChainMInit = .ok mRet ∧
      ReturnRel refArrayReborrowChain ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refArrayReborrowChain [initArrU32_2]) tr (.normal (v, mem))) :=
  mirCall_progress_N refArrayReborrowChain_inFragment refArrayReborrowChain_translate ctx0
    refArrayReborrowChain_ctxOk [initArrU32_2] (by decide) refArrayReborrowChainMInit
    rfl rfl rfl refArrayReborrowChain_noUB n

/-- Disjoint `&mut s.1` (`&mut u32` at byte offset `4`) and `&s.2` (`&u16` at
byte offset `8`) on `Padded(u8, u32, u16)` (`initPaddedStruct = (7, 99, 1541)`),
deref write through `&mut s.1`, shared reborrows of both references, and
preserved `.Uninit` padding bytes (`100 + 1541 = 1641`). -/
def refPaddedStructReborrow : CapturedMir :=
  { ptrBody "witness::ref_padded_struct_reborrow"
      [u32Decl, paddedStructDecl, refMutU32Decl, refSharedU16Decl,
       refSharedU32Decl, refSharedU16Decl, u32Decl, u32Decl, u16Decl, u32Decl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
       .storageLive 6, .storageLive 7, .storageLive 8, .storageLive 9,
       .assign (local_ 2) (.ref (.mut false) (placeField 1 [(1, u32Ty)])),
       .assign (local_ 3) (.ref .shared (placeField 1 [(2, u16Ty)])),
       .assign (local_ 6) (.use (.copy (derefPlace 2))),
       .assign (derefPlace 2) (.binaryOp .add (.copy (local_ 6)) (constU32 1)),
       .assign (local_ 4) (.ref .shared (derefPlace 2)),
       .assign (local_ 5) (.ref .shared (derefPlace 3)),
       .assign (local_ 7) (.use (.copy (derefPlace 4))),
       .assign (local_ 8) (.use (.copy (derefPlace 5))),
       .assign (local_ 9) (.cast .intToInt (.copy (local_ 8)) u32Ty),
       .assign (local_ 0) (.binaryOp .add (.copy (local_ 7)) (.copy (local_ 9)))] with
    fnAbi := fnAbiPaddedArg, layouts := paddedLayouts }

theorem refPaddedStructReborrow_inFragment : inFragment refPaddedStructReborrow = true := by decide

def refPaddedStructReborrowFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, paddedMiniRustTy),
    (localName 2, refTy .mut u32), (localName 3, refTy .not u16),
    (localName 4, refTy .not u32), (localName 5, refTy .not u16),
    (localName 6, .Int u32), (localName 7, .Int u32),
    (localName 8, .Int u16), (localName 9, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .StorageLive (localName 6), .StorageLive (localName 7),
      .StorageLive (localName 8), .StorageLive (localName 9),
      .Assign (.Local (localName 2)) (.AddrOf (.Field (.Local (localName 1)) 1) (refPtrType .mut u32)),
      .Assign (.Local (localName 3)) (.AddrOf (.Field (.Local (localName 1)) 2) (refPtrType .not u16)),
      .Assign (.Local (localName 6)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 6))) (.Constant (.Int 1) (.Int u32))),
      .Assign (.Local (localName 4))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Local (localName 5))
        (.AddrOf (.Deref (.Load (.Local (localName 3))) (.Int u16)) (refPtrType .not u16)),
      .Assign (.Local (localName 7)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32))),
      .Assign (.Local (localName 8)) (.Load (.Deref (.Load (.Local (localName 5))) (.Int u16))),
      .Assign (.Local (localName 9)) (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 8)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 7))) (.Load (.Local (localName 9))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem refPaddedStructReborrow_translate :
    translateFn refPaddedStructReborrow = some refPaddedStructReborrowFn := rfl

def refPaddedStructReborrowS0 : MachineState :=
  initMachineState refPaddedStructReborrow [initPaddedStruct]
def refPaddedStructReborrowMInit : Mach :=
  machine refPaddedStructReborrow refPaddedStructReborrowFn
    refPaddedStructReborrowS0.frame.locals refPaddedStructReborrowFn.start

theorem refPaddedStructReborrow_anneal_ret :
    ReachesRet (mirTree refPaddedStructReborrow refPaddedStructReborrowS0) []
      (.normal (.scalar ⟨1641, 4⟩,
        { refPaddedStructReborrowS0.memory with
          borrows := [{ rawPtrEntry 4 .not (placeField 1 [(2, u16Ty)]) with parentTag := some 2 },
                      { rawPtrEntry 3 .not (placeField 1 [(1, u32Ty)]) with parentTag := some 1 },
                      rawPtrEntry 2 .not (placeField 1 [(2, u16Ty)]),
                      rawPtrEntry 1 .mut (placeField 1 [(1, u32Ty)])],
          nextTag := 5 })) :=
  runA_sound refPaddedStructReborrow 50 _ _ _ rfl

theorem refPaddedStructReborrow_noUB :
    MirNoUBTree (mirCallTree refPaddedStructReborrow [initPaddedStruct]) :=
  runA_noUB refPaddedStructReborrow 50 _ _ _ rfl

theorem refPaddedStructReborrow_minirust_direct :
    retAfter refPaddedStructReborrow [initPaddedStruct] 20 =
      some (some { retAlloc with data := scalarBytes u32 1641 }, [1]) := by
  decide +kernel

theorem refPaddedStructReborrow_ctxOk : CtxOk refPaddedStructReborrow ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : refPaddedStructReborrow.layouts = paddedLayouts := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [refPaddedStructReborrow, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [refPaddedStructReborrow, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : refPaddedStructReborrow.layouts = paddedLayouts := rfl
    rw [hlay]
    simp [refPaddedStructReborrow, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem refPaddedStructReborrow_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n refPaddedStructReborrowMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 1641 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret refPaddedStructReborrow_inFragment refPaddedStructReborrow_translate ctx0
      refPaddedStructReborrow_ctxOk [initPaddedStruct] (by decide) refPaddedStructReborrowMInit
      rfl rfl rfl refPaddedStructReborrow_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [refPaddedStructReborrow, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem refPaddedStructReborrow_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n refPaddedStructReborrowMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k refPaddedStructReborrowMInit = .ok mRet ∧
      ReturnRel refPaddedStructReborrow ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refPaddedStructReborrow [initPaddedStruct]) tr (.normal (v, mem)) :=
  mirCall_noUB refPaddedStructReborrow_inFragment refPaddedStructReborrow_translate ctx0
    refPaddedStructReborrow_ctxOk [initPaddedStruct] (by decide) refPaddedStructReborrowMInit
    rfl rfl rfl refPaddedStructReborrow_noUB herr

theorem refPaddedStructReborrow_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) refPaddedStructReborrowMInit = .ok m' ∧
      StateRelN refPaddedStructReborrow refPaddedStructReborrowFn ctx0 s' m' ∧
      Reaches (mirCallTree refPaddedStructReborrow [initPaddedStruct]) tr
        (mirTree refPaddedStructReborrow s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k refPaddedStructReborrowMInit = .ok mRet ∧
      ReturnRel refPaddedStructReborrow ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refPaddedStructReborrow [initPaddedStruct]) tr (.normal (v, mem))) :=
  mirCall_progress_N refPaddedStructReborrow_inFragment refPaddedStructReborrow_translate ctx0
    refPaddedStructReborrow_ctxOk [initPaddedStruct] (by decide) refPaddedStructReborrowMInit
    rfl rfl rfl refPaddedStructReborrow_noUB n

/-- Mutable reborrow via `Rvalue.copyForDeref` followed by a dereference write
through the child `&mut u32` reference (`(*_4) = Add(copy _5, const 10_u32)`),
which runs `invalidateDerefWriteBorrows` and transitions the parent borrow tag
(`tag = 1`) to `TreeBorrowPerm.disabled` while keeping the child tag (`tag = 2`)
`.active`, then takes a shared reborrow `&(*_4)`, reads via `CopyForDeref`, and
runs `StorageDead` on all reference temporaries (`15` for `x = 5`). -/
def refMutReborrowWrite : CapturedMir :=
  ptrBody "witness::ref_mut_reborrow_write"
    [u32Decl, u32Decl, refMutU32Decl, refMutU32Decl, refMutU32Decl, u32Decl, refSharedU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.copyForDeref (local_ 2)),
     .assign (local_ 4) (.ref (.mut false) (derefPlace 3)),
     .assign (local_ 5) (.copyForDeref (derefPlace 4)),
     .assign (derefPlace 4) (.binaryOp .add (.copy (local_ 5)) (constU32 10)),
     .assign (local_ 6) (.ref .shared (derefPlace 4)),
     .assign (local_ 0) (.copyForDeref (derefPlace 6)),
     .storageDead 6, .storageDead 4, .storageDead 3, .storageDead 2]

theorem refMutReborrowWrite_inFragment : inFragment refMutReborrowWrite = true := by decide

def refMutReborrowWriteFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, refTy .mut u32),
    (localName 4, refTy .mut u32), (localName 5, .Int u32),
    (localName 6, refTy .not u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .StorageLive (localName 6),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Local (localName 3)) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 4))
        (.AddrOf (.Deref (.Load (.Local (localName 3))) (.Int u32)) (refPtrType .mut u32)),
      .Assign (.Local (localName 5)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 4))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 5))) (.Constant (.Int 10) (.Int u32))),
      .Assign (.Local (localName 6))
        (.AddrOf (.Deref (.Load (.Local (localName 4))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 6))) (.Int u32))),
      .StorageDead (localName 6), .StorageDead (localName 4),
      .StorageDead (localName 3), .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem refMutReborrowWrite_translate :
    translateFn refMutReborrowWrite = some refMutReborrowWriteFn := rfl

def refMutReborrowWriteS0 : MachineState :=
  initMachineState refMutReborrowWrite [.scalar ⟨5, 4⟩]
def refMutReborrowWriteMInit : Mach :=
  machine refMutReborrowWrite refMutReborrowWriteFn
    refMutReborrowWriteS0.frame.locals refMutReborrowWriteFn.start

theorem refMutReborrowWrite_anneal_ret :
    ReachesRet (mirTree refMutReborrowWrite refMutReborrowWriteS0) []
      (.normal (.scalar ⟨15, 4⟩,
        { refMutReborrowWriteS0.memory with
          borrows := [{ rawPtrEntry 3 .not (local_ 1) with parentTag := some 2 },
                      { rawPtrEntry 2 .mut (local_ 1) with parentTag := some 1 },
                      rawPtrEntry 1 .mut (local_ 1)],
          nextTag := 4 })) :=
  runA_sound refMutReborrowWrite 40 _ _ _ rfl

theorem refMutReborrowWrite_noUB :
    MirNoUBTree (mirCallTree refMutReborrowWrite [.scalar ⟨5, 4⟩]) :=
  runA_noUB refMutReborrowWrite 40 _ _ _ rfl

theorem refMutReborrowWrite_minirust_direct :
    retAfter refMutReborrowWrite [.scalar ⟨5, 4⟩] 18 =
      some (some { retAlloc with data := scalarBytes u32 15 }, [1]) := by
  decide +kernel

theorem refMutReborrowWrite_ctxOk : CtxOk refMutReborrowWrite ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : refMutReborrowWrite.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [refMutReborrowWrite, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [refMutReborrowWrite, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : refMutReborrowWrite.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [refMutReborrowWrite, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem refMutReborrowWrite_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n refMutReborrowWriteMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 15 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret refMutReborrowWrite_inFragment refMutReborrowWrite_translate ctx0
      refMutReborrowWrite_ctxOk [.scalar ⟨5, 4⟩] (by decide) refMutReborrowWriteMInit
      rfl rfl rfl refMutReborrowWrite_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [refMutReborrowWrite, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem refMutReborrowWrite_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n refMutReborrowWriteMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k refMutReborrowWriteMInit = .ok mRet ∧
      ReturnRel refMutReborrowWrite ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refMutReborrowWrite [.scalar ⟨5, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB refMutReborrowWrite_inFragment refMutReborrowWrite_translate ctx0
    refMutReborrowWrite_ctxOk [.scalar ⟨5, 4⟩] (by decide) refMutReborrowWriteMInit
    rfl rfl rfl refMutReborrowWrite_noUB herr

theorem refMutReborrowWrite_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) refMutReborrowWriteMInit = .ok m' ∧
      StateRelN refMutReborrowWrite refMutReborrowWriteFn ctx0 s' m' ∧
      Reaches (mirCallTree refMutReborrowWrite [.scalar ⟨5, 4⟩]) tr
        (mirTree refMutReborrowWrite s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k refMutReborrowWriteMInit = .ok mRet ∧
      ReturnRel refMutReborrowWrite ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refMutReborrowWrite [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N refMutReborrowWrite_inFragment refMutReborrowWrite_translate ctx0
    refMutReborrowWrite_ctxOk [.scalar ⟨5, 4⟩] (by decide) refMutReborrowWriteMInit
    rfl rfl rfl refMutReborrowWrite_noUB n

/-- Interleaved mutable reborrows and dereference writes on disjoint array
elements `a[0]` and `a[1]` of `[u32; 2]` (`a = [5, 7]`): writing `(*_4) = 15`
disables parent `_2` (`tag = 1`) on `a[0]` while `targetsDefinitelyDisjoint`
keeps sibling reborrow `_5` (`tag = 4`) `.live` on `a[1]`, and writing
`(*_5) = 27` disables parent `_3` (`tag = 2`) on `a[1]` while keeping `_4`
(`tag = 3`) `.live` on `a[0]`, returning `15 + 27 = 42`. -/
def refDisjointReborrowWrite : CapturedMir :=
  { ptrBody "witness::ref_disjoint_reborrow_write"
      [u32Decl, arrU32_2Decl, refMutU32Decl, refMutU32Decl, refMutU32Decl,
       refMutU32Decl, u32Decl, u32Decl, u32Decl, u32Decl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
       .storageLive 6, .storageLive 7, .storageLive 8, .storageLive 9,
       .assign (local_ 2) (.ref (.mut false) (placeConstIdx 1 0 2 false)),
       .assign (local_ 3) (.ref (.mut false) (placeConstIdx 1 1 2 false)),
       .assign (local_ 4) (.ref (.mut false) (derefPlace 2)),
       .assign (local_ 5) (.ref (.mut false) (derefPlace 3)),
       .assign (local_ 6) (.copyForDeref (derefPlace 4)),
       .assign (derefPlace 4) (.binaryOp .add (.copy (local_ 6)) (constU32 10)),
       .assign (local_ 7) (.copyForDeref (derefPlace 5)),
       .assign (derefPlace 5) (.binaryOp .add (.copy (local_ 7)) (constU32 20)),
       .assign (local_ 8) (.copyForDeref (derefPlace 4)),
       .assign (local_ 9) (.copyForDeref (derefPlace 5)),
       .assign (local_ 0) (.binaryOp .add (.copy (local_ 8)) (.copy (local_ 9)))] with
    fnAbi := fnAbiArrU32_2Arg }

theorem refDisjointReborrowWrite_inFragment : inFragment refDisjointReborrowWrite = true := by
  decide

def refDisjointReborrowWriteFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Array (.Int u32) 2),
    (localName 2, refTy .mut u32), (localName 3, refTy .mut u32),
    (localName 4, refTy .mut u32), (localName 5, refTy .mut u32),
    (localName 6, .Int u32), (localName 7, .Int u32),
    (localName 8, .Int u32), (localName 9, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .StorageLive (localName 6), .StorageLive (localName 7),
      .StorageLive (localName 8), .StorageLive (localName 9),
      .Assign (.Local (localName 2))
        (.AddrOf (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt)))
          (refPtrType .mut u32)),
      .Assign (.Local (localName 3))
        (.AddrOf (.Index (.Local (localName 1)) (.Constant (.Int 1) (.Int usizeIt)))
          (refPtrType .mut u32)),
      .Assign (.Local (localName 4))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .mut u32)),
      .Assign (.Local (localName 5))
        (.AddrOf (.Deref (.Load (.Local (localName 3))) (.Int u32)) (refPtrType .mut u32)),
      .Assign (.Local (localName 6)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 4))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 6))) (.Constant (.Int 10) (.Int u32))),
      .Assign (.Local (localName 7)) (.Load (.Deref (.Load (.Local (localName 5))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 5))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 7))) (.Constant (.Int 20) (.Int u32))),
      .Assign (.Local (localName 8)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32))),
      .Assign (.Local (localName 9)) (.Load (.Deref (.Load (.Local (localName 5))) (.Int u32))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 8))) (.Load (.Local (localName 9))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem refDisjointReborrowWrite_translate :
    translateFn refDisjointReborrowWrite = some refDisjointReborrowWriteFn := rfl

def refDisjointReborrowWriteS0 : MachineState :=
  initMachineState refDisjointReborrowWrite [initArrU32_2]
def refDisjointReborrowWriteMInit : Mach :=
  machine refDisjointReborrowWrite refDisjointReborrowWriteFn
    refDisjointReborrowWriteS0.frame.locals refDisjointReborrowWriteFn.start

theorem refDisjointReborrowWrite_anneal_ret :
    ReachesRet (mirTree refDisjointReborrowWrite refDisjointReborrowWriteS0) []
      (.normal (.scalar ⟨42, 4⟩,
        { refDisjointReborrowWriteS0.memory with
          borrows := [{ rawPtrEntry 4 .mut (placeConstIdx 1 1 2 false) with parentTag := some 2 },
                      { rawPtrEntry 3 .mut (placeConstIdx 1 0 2 false) with parentTag := some 1 },
                      rawPtrEntry 2 .mut (placeConstIdx 1 1 2 false),
                      rawPtrEntry 1 .mut (placeConstIdx 1 0 2 false)],
          nextTag := 5 })) :=
  runA_sound refDisjointReborrowWrite 50 _ _ _ rfl

theorem refDisjointReborrowWrite_noUB :
    MirNoUBTree (mirCallTree refDisjointReborrowWrite [initArrU32_2]) :=
  runA_noUB refDisjointReborrowWrite 50 _ _ _ rfl

theorem refDisjointReborrowWrite_minirust_direct :
    retAfter refDisjointReborrowWrite [initArrU32_2] 21 =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) := by
  decide +kernel

theorem refDisjointReborrowWrite_ctxOk : CtxOk refDisjointReborrowWrite ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : refDisjointReborrowWrite.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [refDisjointReborrowWrite, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [refDisjointReborrowWrite, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : refDisjointReborrowWrite.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [refDisjointReborrowWrite, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem refDisjointReborrowWrite_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n refDisjointReborrowWriteMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret refDisjointReborrowWrite_inFragment refDisjointReborrowWrite_translate ctx0
      refDisjointReborrowWrite_ctxOk [initArrU32_2] (by decide) refDisjointReborrowWriteMInit
      rfl rfl rfl refDisjointReborrowWrite_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [refDisjointReborrowWrite, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem refDisjointReborrowWrite_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n refDisjointReborrowWriteMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k refDisjointReborrowWriteMInit = .ok mRet ∧
      ReturnRel refDisjointReborrowWrite ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refDisjointReborrowWrite [initArrU32_2]) tr (.normal (v, mem)) :=
  mirCall_noUB refDisjointReborrowWrite_inFragment refDisjointReborrowWrite_translate ctx0
    refDisjointReborrowWrite_ctxOk [initArrU32_2] (by decide) refDisjointReborrowWriteMInit
    rfl rfl rfl refDisjointReborrowWrite_noUB herr

theorem refDisjointReborrowWrite_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) refDisjointReborrowWriteMInit = .ok m' ∧
      StateRelN refDisjointReborrowWrite refDisjointReborrowWriteFn ctx0 s' m' ∧
      Reaches (mirCallTree refDisjointReborrowWrite [initArrU32_2]) tr
        (mirTree refDisjointReborrowWrite s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k refDisjointReborrowWriteMInit = .ok mRet ∧
      ReturnRel refDisjointReborrowWrite ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refDisjointReborrowWrite [initArrU32_2]) tr (.normal (v, mem))) :=
  mirCall_progress_N refDisjointReborrowWrite_inFragment refDisjointReborrowWrite_translate ctx0
    refDisjointReborrowWrite_ctxOk [initArrU32_2] (by decide) refDisjointReborrowWriteMInit
    rfl rfl rfl refDisjointReborrowWrite_noUB n

/-- Cyclic 5-block CFG taking sequential NLL shared (`_3 = &_1` in `bb1`) and
mutable (`_5 = &mut _1` in `bb2`, carried live across `Goto -> bb3`, reborrowed
`_6 = &mut (*_5)`, and mutated `(*_6) = (*_6) - 1` in `bb3`) borrows of `_1`
across loop iterations, then reading `copy _1` directly on loop exit (`bb4`);
returns `(3 + 2 + 1) + 0 = 6` on `x = 3`. -/
def refLoopCountdown : CapturedMir where
  defPath := "witness::ref_loop_countdown"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl, refSharedU32Decl, u32Decl,
    refMutU32Decl, refMutU32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2), mkStmt (.storageLive 4), mkStmt (.storageLive 7),
        mkStmt (.assign (local_ 2) (.use (constU32 0)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.ref .shared (local_ 1))),
        mkStmt (.assign (local_ 4) (.copyForDeref (derefPlace 3))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm (.switchInt (.copy (local_ 4)) { branches := [(0, 4)], otherwise := 2 }),
      isCleanup := false },
    { statements := [mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.ref (.mut false) (local_ 1)))],
      terminator := mkTerm (.goto 3), isCleanup := false },
    { statements := [mkStmt (.storageLive 6),
        mkStmt (.assign (local_ 6) (.ref (.mut false) (derefPlace 5))),
        mkStmt (.assign (local_ 7) (.use (.copy (derefPlace 6)))),
        mkStmt (.assign (local_ 2) (.binaryOp .add (.copy (local_ 2)) (.copy (local_ 7)))),
        mkStmt (.assign (derefPlace 6) (.binaryOp .sub (.copy (local_ 7)) (constU32 1))),
        mkStmt (.storageDead 6),
        mkStmt (.storageDead 5)],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 2)) (.copy (local_ 1)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem refLoopCountdown_inFragment : inFragment refLoopCountdown = true := by decide

/-- At `bb3` of `refLoopCountdown`, forward CFG borrow dataflow (`ptrEnvAtEntry`)
propagates the live `&mut _1` borrow `_5` across `bb2 -> bb3` inside the loop. -/
theorem refLoopCountdown_ptrEnvAtEntry_bb3 :
    (ptrEnvAtEntry refLoopCountdown 3)[5]? =
      some (.live (some (1, [])) [5] false true) := by
  decide

def refLoopCountdownFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, refTy .not u32), (localName 4, .Int u32),
    (localName 5, refTy .mut u32), (localName 6, refTy .mut u32),
    (localName 7, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 4), .StorageLive (localName 7),
      .Assign (.Local (localName 2)) (.Constant (.Int 0) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .StorageLive (localName 3),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 1)) (refPtrType .not u32)),
      .Assign (.Local (localName 4)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32))),
      .StorageDead (localName 3)],
      .Switch (.Load (.Local (localName 4))) ⟨[(0, bbName 4)]⟩ (bbName 2), .Regular⟩),
    (bbName 2, ⟨[
      .StorageLive (localName 5),
      .Assign (.Local (localName 5)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 3, ⟨[
      .StorageLive (localName 6),
      .Assign (.Local (localName 6))
        (.AddrOf (.Deref (.Load (.Local (localName 5))) (.Int u32)) (refPtrType .mut u32)),
      .Assign (.Local (localName 7)) (.Load (.Deref (.Load (.Local (localName 6))) (.Int u32))),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Add) (.Load (.Local (localName 2))) (.Load (.Local (localName 7)))),
      .Assign (.Deref (.Load (.Local (localName 6))) (.Int u32))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 7))) (.Constant (.Int 1) (.Int u32))),
      .StorageDead (localName 6),
      .StorageDead (localName 5)],
      .Goto (bbName 1), .Regular⟩),
    (bbName 4, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 2))) (.Load (.Local (localName 1)))),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 5, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 5
  implicit_writes := true

theorem refLoopCountdown_translate :
    translateFn refLoopCountdown = some refLoopCountdownFn := rfl

def refLoopCountdownS0 : MachineState := initMachineState refLoopCountdown [.scalar ⟨3, 4⟩]
def refLoopCountdownMInit : Mach :=
  machine refLoopCountdown refLoopCountdownFn
    refLoopCountdownS0.frame.locals refLoopCountdownFn.start

theorem refLoopCountdown_anneal_ret :
    ReachesRet (mirTree refLoopCountdown refLoopCountdownS0) constBorrowLoopTrace
      (.normal (.scalar ⟨6, 4⟩,
        { refLoopCountdownS0.memory with
          borrows := [rawPtrEntry 10 .not (local_ 1),
                      { rawPtrEntry 9 .mut (local_ 1) with perm := .frozen, parentTag := some 8 },
                      { rawPtrEntry 8 .mut (local_ 1) with perm := .frozen },
                      { rawPtrEntry 7 .not (local_ 1) with perm := .disabled },
                      { rawPtrEntry 6 .mut (local_ 1) with perm := .disabled, parentTag := some 5 },
                      { rawPtrEntry 5 .mut (local_ 1) with perm := .disabled },
                      { rawPtrEntry 4 .not (local_ 1) with perm := .disabled },
                      { rawPtrEntry 3 .mut (local_ 1) with perm := .disabled, parentTag := some 2 },
                      { rawPtrEntry 2 .mut (local_ 1) with perm := .disabled },
                      { rawPtrEntry 1 .not (local_ 1) with perm := .disabled }],
          nextTag := 11 })) :=
  runA_sound refLoopCountdown 100 _ _ _ rfl

theorem refLoopCountdown_noUB :
    MirNoUBTree (mirCallTree refLoopCountdown [.scalar ⟨3, 4⟩]) :=
  runA_noUB refLoopCountdown 100 _ _ _ rfl

theorem refLoopCountdown_minirust_direct :
    retAfter refLoopCountdown [.scalar ⟨3, 4⟩] 62 =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1]) := by
  decide +kernel

theorem refLoopCountdown_ctxOk : CtxOk refLoopCountdown ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : refLoopCountdown.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [refLoopCountdown] at hd; subst hd; decide
    | 1, hd, _ => simp [refLoopCountdown] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : refLoopCountdown.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [refLoopCountdown] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem refLoopCountdown_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n refLoopCountdownMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret refLoopCountdown_inFragment refLoopCountdown_translate ctx0
      refLoopCountdown_ctxOk [.scalar ⟨3, 4⟩] (by decide) refLoopCountdownMInit
      rfl rfl rfl refLoopCountdown_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [refLoopCountdown] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem refLoopCountdown_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n refLoopCountdownMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k refLoopCountdownMInit = .ok mRet ∧
      ReturnRel refLoopCountdown ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refLoopCountdown [.scalar ⟨3, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB refLoopCountdown_inFragment refLoopCountdown_translate ctx0
    refLoopCountdown_ctxOk [.scalar ⟨3, 4⟩] (by decide) refLoopCountdownMInit
    rfl rfl rfl refLoopCountdown_noUB herr

theorem refLoopCountdown_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) refLoopCountdownMInit = .ok m' ∧
      StateRelN refLoopCountdown refLoopCountdownFn ctx0 s' m' ∧
      Reaches (mirCallTree refLoopCountdown [.scalar ⟨3, 4⟩]) tr
        (mirTree refLoopCountdown s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k refLoopCountdownMInit = .ok mRet ∧
      ReturnRel refLoopCountdown ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refLoopCountdown [.scalar ⟨3, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N refLoopCountdown_inFragment refLoopCountdown_translate ctx0
    refLoopCountdown_ctxOk [.scalar ⟨3, 4⟩] (by decide) refLoopCountdownMInit
    rfl rfl rfl refLoopCountdown_noUB n

/-! ### In-fragment reference UB witnesses -/

/-- Reading `copy (*_2)` through an uninitialized `&u32` temporary `_2` is in
the fragment and raises UB in both semantics. -/
def uninitRefReadUb : CapturedMir :=
  ptrBody "witness::uninit_ref_read_ub" [u32Decl, u32Decl, refSharedU32Decl]
    [.storageLive 2, .assign (local_ 0) (.use (.copy (derefPlace 2)))]

theorem uninitRefReadUb_inFragment : inFragment uninitRefReadUb = true := by decide

def uninitRefReadUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, refTy .not u32)]⟩
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

theorem uninitRefReadUb_translate : translateFn uninitRefReadUb = some uninitRefReadUbFn := rfl

def uninitRefReadUbS0 : MachineState := initMachineState uninitRefReadUb [.scalar ⟨5, 4⟩]
def uninitRefReadUbMInit : Mach :=
  machine uninitRefReadUb uninitRefReadUbFn uninitRefReadUbS0.frame.locals uninitRefReadUbFn.start

theorem uninitRefReadUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitRefReadUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitRefReadUb 10 _ (by decide)

theorem uninitRefReadUb_ctxOk : CtxOk uninitRefReadUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : uninitRefReadUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [uninitRefReadUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [uninitRefReadUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : uninitRefReadUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [uninitRefReadUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem uninitRefReadUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitRefReadUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitRefReadUb_anneal_ub
  exact mirCall_ub uninitRefReadUb_inFragment uninitRefReadUb_translate ctx0 uninitRefReadUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitRefReadUbMInit rfl rfl rfl hr hf

theorem uninitRefReadUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n uninitRefReadUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree uninitRefReadUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k uninitRefReadUbMInit = .ok mRet ∧
      ReturnRel uninitRefReadUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree uninitRefReadUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error uninitRefReadUb_inFragment uninitRefReadUb_translate ctx0 uninitRefReadUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitRefReadUbMInit rfl rfl rfl herr

theorem uninitRefReadUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) uninitRefReadUbMInit = .ok m' ∧
      StateRelN uninitRefReadUb uninitRefReadUbFn ctx0 s' m' ∧
      Reaches (mirCallTree uninitRefReadUb [.scalar ⟨5, 4⟩]) tr (mirTree uninitRefReadUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k uninitRefReadUbMInit = .ok mRet ∧
      ReturnRel uninitRefReadUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree uninitRefReadUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) uninitRefReadUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree uninitRefReadUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N uninitRefReadUb_inFragment uninitRefReadUb_translate ctx0 uninitRefReadUb_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) uninitRefReadUbMInit rfl rfl rfl n

theorem uninitRefReadUb_minirust_direct :
    ubAfter uninitRefReadUb [.scalar ⟨5, 4⟩] 3 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- Reborrowing `&(*_2)` from an uninitialized `&u32` temporary `_2` is in the
fragment and raises UB in both semantics. -/
def uninitRefReborrowUb : CapturedMir :=
  ptrBody "witness::uninit_ref_reborrow_ub" [u32Decl, u32Decl, refSharedU32Decl, refSharedU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 3) (.ref .shared (derefPlace 2)),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem uninitRefReborrowUb_inFragment : inFragment uninitRefReborrowUb = true := by decide

def uninitRefReborrowUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .not u32), (localName 3, refTy .not u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitRefReborrowUb_translate :
    translateFn uninitRefReborrowUb = some uninitRefReborrowUbFn := rfl

def uninitRefReborrowUbS0 : MachineState := initMachineState uninitRefReborrowUb [.scalar ⟨5, 4⟩]
def uninitRefReborrowUbMInit : Mach :=
  machine uninitRefReborrowUb uninitRefReborrowUbFn
    uninitRefReborrowUbS0.frame.locals uninitRefReborrowUbFn.start

theorem uninitRefReborrowUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitRefReborrowUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitRefReborrowUb 10 _ (by decide)

theorem uninitRefReborrowUb_ctxOk : CtxOk uninitRefReborrowUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : uninitRefReborrowUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [uninitRefReborrowUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [uninitRefReborrowUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : uninitRefReborrowUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [uninitRefReborrowUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem uninitRefReborrowUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitRefReborrowUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitRefReborrowUb_anneal_ub
  exact mirCall_ub uninitRefReborrowUb_inFragment uninitRefReborrowUb_translate ctx0
    uninitRefReborrowUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) uninitRefReborrowUbMInit rfl rfl rfl hr hf

theorem uninitRefReborrowUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n uninitRefReborrowUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree uninitRefReborrowUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k uninitRefReborrowUbMInit = .ok mRet ∧
      ReturnRel uninitRefReborrowUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree uninitRefReborrowUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error uninitRefReborrowUb_inFragment uninitRefReborrowUb_translate ctx0
    uninitRefReborrowUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) uninitRefReborrowUbMInit rfl rfl rfl herr

theorem uninitRefReborrowUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) uninitRefReborrowUbMInit = .ok m' ∧
      StateRelN uninitRefReborrowUb uninitRefReborrowUbFn ctx0 s' m' ∧
      Reaches (mirCallTree uninitRefReborrowUb [.scalar ⟨5, 4⟩]) tr
        (mirTree uninitRefReborrowUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k uninitRefReborrowUbMInit = .ok mRet ∧
      ReturnRel uninitRefReborrowUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree uninitRefReborrowUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) uninitRefReborrowUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree uninitRefReborrowUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N uninitRefReborrowUb_inFragment uninitRefReborrowUb_translate ctx0
    uninitRefReborrowUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) uninitRefReborrowUbMInit rfl rfl rfl n

theorem uninitRefReborrowUb_minirust_direct :
    ubAfter uninitRefReborrowUb [.scalar ⟨5, 4⟩] 4 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- Mutable reborrow `&mut (*_2)` followed by a dereference write whose RHS
divides by zero (`(*_3) = Div(copy _4, const 0_u32)`) is in the fragment and
raises UB in lockstep in both semantics (`mirCall_ub`, `mirCall_steps_error`,
`mirCall_outcome_N`). -/
def refMutDivZeroUb : CapturedMir :=
  ptrBody "witness::ref_mut_div_zero_ub"
    [u32Decl, u32Decl, refMutU32Decl, refMutU32Decl, u32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.ref (.mut false) (derefPlace 2)),
     .assign (local_ 4) (.copyForDeref (derefPlace 3)),
     .assign (derefPlace 3) (.binaryOp .div (.copy (local_ 4)) (constU32 0)),
     .assign (local_ 0) (.copyForDeref (derefPlace 3))]

theorem refMutDivZeroUb_inFragment : inFragment refMutDivZeroUb = true := by decide

def refMutDivZeroUbFn : Gen.Function where
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
      .Assign (.Local (localName 4)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 3))) (.Int u32))
        (.BinOp (.Int .Div) (.Load (.Local (localName 4))) (.Constant (.Int 0) (.Int u32))),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem refMutDivZeroUb_translate :
    translateFn refMutDivZeroUb = some refMutDivZeroUbFn := rfl

def refMutDivZeroUbS0 : MachineState := initMachineState refMutDivZeroUb [.scalar ⟨5, 4⟩]
def refMutDivZeroUbMInit : Mach :=
  machine refMutDivZeroUb refMutDivZeroUbFn
    refMutDivZeroUbS0.frame.locals refMutDivZeroUbFn.start

theorem refMutDivZeroUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree refMutDivZeroUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound refMutDivZeroUb 15 _ (by decide)

theorem refMutDivZeroUb_ctxOk : CtxOk refMutDivZeroUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : refMutDivZeroUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [refMutDivZeroUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [refMutDivZeroUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : refMutDivZeroUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [refMutDivZeroUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem refMutDivZeroUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n refMutDivZeroUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := refMutDivZeroUb_anneal_ub
  exact mirCall_ub refMutDivZeroUb_inFragment refMutDivZeroUb_translate ctx0
    refMutDivZeroUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) refMutDivZeroUbMInit rfl rfl rfl hr hf

theorem refMutDivZeroUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n refMutDivZeroUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree refMutDivZeroUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k refMutDivZeroUbMInit = .ok mRet ∧
      ReturnRel refMutDivZeroUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refMutDivZeroUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error refMutDivZeroUb_inFragment refMutDivZeroUb_translate ctx0
    refMutDivZeroUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) refMutDivZeroUbMInit rfl rfl rfl herr

theorem refMutDivZeroUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) refMutDivZeroUbMInit = .ok m' ∧
      StateRelN refMutDivZeroUb refMutDivZeroUbFn ctx0 s' m' ∧
      Reaches (mirCallTree refMutDivZeroUb [.scalar ⟨5, 4⟩]) tr
        (mirTree refMutDivZeroUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k refMutDivZeroUbMInit = .ok mRet ∧
      ReturnRel refMutDivZeroUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refMutDivZeroUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) refMutDivZeroUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree refMutDivZeroUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N refMutDivZeroUb_inFragment refMutDivZeroUb_translate ctx0
    refMutDivZeroUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) refMutDivZeroUbMInit rfl rfl rfl n

theorem refMutDivZeroUb_minirust_direct :
    ubAfter refMutDivZeroUb [.scalar ⟨5, 4⟩] 8 =
      some "division by zero" := by
  decide +kernel

/-! ### Safe-pointer validity (`PtrType::Ref` vs `PtrType::Raw`) -/

/-- Creating an unused `&u32` reference from a misaligned `*const u32`
(`_6 = &(*_5); _0 = copy _1; return`): unlike a raw borrow `&raw const (*_5)`,
forming `&*q` checks safe-pointer alignment and raises UB in both MiniRust
(`"Value::Ptr: unaligned safe pointer"`) and Anneal (`resolveRefDerefTarget?`;
see `misalignedRef_three_way_ub_agreement` below). -/
def misalignedRef : CapturedMir :=
  ptrBody "witness::misaligned_ref"
    [u32Decl, u32Decl, ptrConstU32Decl, ptrConstU8Decl, ptrConstU8Decl,
     ptrConstU32Decl, refSharedU32Decl]
    [.storageLive 2, .assign (local_ 2) (.rawPtr .not (local_ 1)),
     .storageLive 3, .assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) ptrConstU8Ty),
     .storageLive 4, .assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (constUsize 1)),
     .storageLive 5, .assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) ptrConstU32Ty),
     .storageLive 6, .assign (local_ 6) (.ref .shared (derefPlace 5)),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem misalignedRef_notInFragment : inFragment misalignedRef = false := by decide +kernel

theorem misalignedRef_anneal_ub :
    ∃ tr u, Reaches (mirTree misalignedRef (initMachineState misalignedRef [.scalar ⟨5, 4⟩])) tr u ∧
      FaultNow u :=
  faultsA_sound misalignedRef 30 _ (by decide)

theorem misalignedRef_minirust_direct :
    ubAfter misalignedRef [.scalar ⟨5, 4⟩] 11 = some "Value::Ptr: unaligned safe pointer" := by
  decide +kernel

/-- Copying a dangling `&u32` (`_3 = &_2; StorageDead(_2); _4 = copy _3`)
without ever dereferencing `*_3`: unlike a dangling `*const u32`, loading a
`&u32` value runs `checkPtr`'s dereferenceability check and raises
`"Value::Ptr: non-dereferenceable safe pointer"` in MiniRust, whereas Anneal
copies the `(tag, offset)` pair without retagging or dereferencing and returns `x`. -/
def danglingRef : CapturedMir :=
  ptrBody "witness::dangling_ref"
    [u32Decl, u32Decl, u32Decl, refSharedU32Decl, refSharedU32Decl]
    [.storageLive 2, .assign (local_ 2) (.use (.copy (local_ 1))),
     .storageLive 3, .assign (local_ 3) (.ref .shared (local_ 2)),
     .storageDead 2,
     .storageLive 4, .assign (local_ 4) (.use (.copy (local_ 3))),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem danglingRef_notInFragment : inFragment danglingRef = false := by decide +kernel

theorem danglingRef_anneal_ret :
    ∃ mem, ReachesRet (mirTree danglingRef (initMachineState danglingRef [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨5, 4⟩, mem)) :=
  ⟨_, runA_sound danglingRef 30 _ _ _ rfl⟩

theorem danglingRef_minirust_direct :
    ubAfter danglingRef [.scalar ⟨5, 4⟩] 8 =
      some "Value::Ptr: non-dereferenceable safe pointer" := by
  decide +kernel

/-- Ground-truth `checkValue` checks on `PtrType.Ref`: null address, unaligned
address, uninhabited pointee, and non-dereferenceable provenance each raise the
exact MiniRust `Value::Ptr` UB diagnostic. -/
theorem checkValue_refTy_safe_ptr_ub (prov : Option Prov) :
    checkValue (thinPtrVal 0 prov) (refTy .not u32) =
        .error (.ub "Value::Ptr: null safe pointer") ∧
      checkValue (thinPtrVal 2 prov) (refTy .not u32) =
        .error (.ub "Value::Ptr: unaligned safe pointer") ∧
      checkValue (thinPtrVal 4 prov)
          (.Ptr (.Ref .Immutable { intPointeeInfo u32 with inhabited := false })) =
        .error (.ub "Value::Ptr: safe pointer to uninhabited type") ∧
      checkValue (thinPtrVal 4 (some (⟨0⟩, ()))) (refTy .not u32) (some refSharedReadMInit) =
        .error (.ub "Value::Ptr: non-dereferenceable safe pointer") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Two-phase borrows and Tree Borrows permission checks -/

/-- In-fragment two-phase mutable borrow (`BorrowKind.mut true`) with a foreign
shared read during reservation followed by activation on dereference write:
```rust
fn ref_two_phase_borrow_round_trip(mut x: u32) -> u32 {
    let r = &two_phase mut x; // _2 = &two_phase mut _1 (tag 1: Reserved)
    let s = &x;               // _3 = &_1               (tag 2: Frozen; tag 1 stays Reserved)
    let t = *s;               // _4 = copy (*_3)        (foreign read while tag 1 is Reserved)
    *r = t + 37;              // (*_2) = _4 + 37        (activates tag 1: Reserved -> Active, disables tag 2)
    *r                        // _0 = copy (*_2)        (returns 42 on input 5)
}
```
-/
def refTwoPhaseBorrowRoundTrip : CapturedMir :=
  ptrBody "witness::ref_two_phase_borrow_round_trip"
    [u32Decl, u32Decl, refMutU32Decl, refSharedU32Decl, u32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4,
     .assign (local_ 2) (.ref (.mut true) (local_ 1)),
     .assign (local_ 3) (.ref .shared (local_ 1)),
     .assign (local_ 4) (.use (.copy (derefPlace 3))),
     .assign (derefPlace 2) (.binaryOp .add (.copy (local_ 4)) (constU32 37)),
     .assign (local_ 0) (.use (.copy (derefPlace 2)))]

theorem refTwoPhaseBorrowRoundTrip_inFragment :
    inFragment refTwoPhaseBorrowRoundTrip = true := by decide

def refTwoPhaseBorrowRoundTripFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, refTy .not u32),
    (localName 4, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3), .StorageLive (localName 4),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 1)) (refPtrType .not u32)),
      .Assign (.Local (localName 4)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 4))) (.Constant (.Int 37) (.Int u32))),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem refTwoPhaseBorrowRoundTrip_translate :
    translateFn refTwoPhaseBorrowRoundTrip = some refTwoPhaseBorrowRoundTripFn := rfl

def refTwoPhaseBorrowRoundTripS0 : MachineState :=
  initMachineState refTwoPhaseBorrowRoundTrip [.scalar ⟨5, 4⟩]
def refTwoPhaseBorrowRoundTripMInit : Mach :=
  machine refTwoPhaseBorrowRoundTrip refTwoPhaseBorrowRoundTripFn
    refTwoPhaseBorrowRoundTripS0.frame.locals refTwoPhaseBorrowRoundTripFn.start

theorem refTwoPhaseBorrowRoundTrip_anneal_ret :
    ReachesRet (mirTree refTwoPhaseBorrowRoundTrip refTwoPhaseBorrowRoundTripS0) []
      (.normal (.scalar ⟨42, 4⟩,
        { refTwoPhaseBorrowRoundTripS0.memory with
          borrows := [{ rawPtrEntry 2 .not (local_ 1) with perm := .disabled },
                      rawPtrEntry 1 .mut (local_ 1)],
          nextTag := 3 })) :=
  runA_sound refTwoPhaseBorrowRoundTrip 30 _ _ _ rfl

theorem refTwoPhaseBorrowRoundTrip_noUB :
    MirNoUBTree (mirCallTree refTwoPhaseBorrowRoundTrip [.scalar ⟨5, 4⟩]) :=
  runA_noUB refTwoPhaseBorrowRoundTrip 30 _ _ _ rfl

theorem refTwoPhaseBorrowRoundTrip_minirust_direct :
    retAfter refTwoPhaseBorrowRoundTrip [.scalar ⟨5, 4⟩] 10 =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) := by
  decide +kernel

theorem refTwoPhaseBorrowRoundTrip_ctxOk : CtxOk refTwoPhaseBorrowRoundTrip ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : refTwoPhaseBorrowRoundTrip.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [refTwoPhaseBorrowRoundTrip, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [refTwoPhaseBorrowRoundTrip, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : refTwoPhaseBorrowRoundTrip.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [refTwoPhaseBorrowRoundTrip, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem refTwoPhaseBorrowRoundTrip_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n refTwoPhaseBorrowRoundTripMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret refTwoPhaseBorrowRoundTrip_inFragment refTwoPhaseBorrowRoundTrip_translate ctx0
      refTwoPhaseBorrowRoundTrip_ctxOk [.scalar ⟨5, 4⟩] (by decide) refTwoPhaseBorrowRoundTripMInit
      rfl rfl rfl refTwoPhaseBorrowRoundTrip_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [refTwoPhaseBorrowRoundTrip, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem refTwoPhaseBorrowRoundTrip_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n refTwoPhaseBorrowRoundTripMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k refTwoPhaseBorrowRoundTripMInit = .ok mRet ∧
      ReturnRel refTwoPhaseBorrowRoundTrip ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refTwoPhaseBorrowRoundTrip [.scalar ⟨5, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB refTwoPhaseBorrowRoundTrip_inFragment refTwoPhaseBorrowRoundTrip_translate ctx0
    refTwoPhaseBorrowRoundTrip_ctxOk [.scalar ⟨5, 4⟩] (by decide) refTwoPhaseBorrowRoundTripMInit
    rfl rfl rfl refTwoPhaseBorrowRoundTrip_noUB herr

theorem refTwoPhaseBorrowRoundTrip_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) refTwoPhaseBorrowRoundTripMInit = .ok m' ∧
      StateRelN refTwoPhaseBorrowRoundTrip refTwoPhaseBorrowRoundTripFn ctx0 s' m' ∧
      Reaches (mirCallTree refTwoPhaseBorrowRoundTrip [.scalar ⟨5, 4⟩]) tr
        (mirTree refTwoPhaseBorrowRoundTrip s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k refTwoPhaseBorrowRoundTripMInit = .ok mRet ∧
      ReturnRel refTwoPhaseBorrowRoundTrip ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refTwoPhaseBorrowRoundTrip [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N refTwoPhaseBorrowRoundTrip_inFragment refTwoPhaseBorrowRoundTrip_translate ctx0
    refTwoPhaseBorrowRoundTrip_ctxOk [.scalar ⟨5, 4⟩] (by decide) refTwoPhaseBorrowRoundTripMInit
    rfl rfl rfl refTwoPhaseBorrowRoundTrip_noUB n

/-- Foreign dereference write while a two-phase mutable borrow is `Reserved`
(`_2 = &two_phase mut _1; _3 = &mut _1; (*_3) = 99; _0 = copy (*_2)`):
`ptrAliasingOk`'s `stepDerefWrite` marks `_2` `.disabled` after `(*_3) = 99`,
so `inFragment` rejects the subsequent `copy (*_2)`. Anneal disables tag `1`
(`.reserved -> .disabled`) on the foreign dereference write through tag `2` and
faults when reading `*_2`, while MiniRust's `BasicMemory` returns `99`. -/
def twoPhaseForeignWriteDiscrepancy : CapturedMir :=
  ptrBody "witness::two_phase_foreign_write_discrepancy"
    [u32Decl, u32Decl, refMutU32Decl, refMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.ref (.mut true) (local_ 1)),
     .assign (local_ 3) (.ref (.mut false) (local_ 1)),
     .assign (derefPlace 3) (.use (constU32 99)),
     .assign (local_ 0) (.use (.copy (derefPlace 2)))]

theorem twoPhaseForeignWriteDiscrepancy_translate :
    (translateFn twoPhaseForeignWriteDiscrepancy).isSome = true := by decide +kernel

theorem twoPhaseForeignWriteDiscrepancy_notInFragment :
    inFragment twoPhaseForeignWriteDiscrepancy = false := by decide +kernel

theorem twoPhaseForeignWriteDiscrepancy_anneal_ub :
    ∃ tr u, Reaches (mirTree twoPhaseForeignWriteDiscrepancy
      (initMachineState twoPhaseForeignWriteDiscrepancy [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound twoPhaseForeignWriteDiscrepancy 30 _ (by decide)

theorem twoPhaseForeignWriteDiscrepancy_minirust_direct :
    retAfter twoPhaseForeignWriteDiscrepancy [.scalar ⟨5, 4⟩] 8 =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) := by
  decide +kernel

/-- Direct write to a local with an unprotected `Freeze` two-phase borrow
(`_2 = &two_phase mut _1; _1 = 99; _0 = copy (*_2)`):
`inFragment` rejects this body because `stmtPreservesAddrTaken` forbids direct
writes to address-taken locals. Under the merged `LM-3.3` `Trusted` semantics
the former Anneal/Tree Borrows gap is closed: `&two_phase mut _1` records
`.reservedFrz false` (`TreeBorrowPerm.reserved`), and `updateBorrowPerm` with
`writerTag = .none` (the direct write `_1 = 99`) disables an unprotected
`.reservedFrz false` entry, so reading `*_2` raises UB in Anneal
(`twoPhaseDirectWriteTreeBorrowsGap_anneal_ub`), agreeing with ground-truth
`TreeBorrowsMemory` (`Permission.foreign_write_unprot_reserved_iff.1`,
`treeBorrowsDirectWriteDisablesUnprotReserved`, and
`twoPhaseDirectWriteTreeBorrowsGap_tb_direct`), which transitions unprotected
`Freeze` `Reserved -> Disabled` on foreign writes. Only MiniRust's `BasicMemory`
(no aliasing model) returns `99`. -/
def twoPhaseDirectWriteTreeBorrowsGap : CapturedMir :=
  ptrBody "witness::two_phase_direct_write_tree_borrows_gap"
    [u32Decl, u32Decl, refMutU32Decl]
    [.storageLive 2,
     .assign (local_ 2) (.ref (.mut true) (local_ 1)),
     .assign (local_ 1) (.use (constU32 99)),
     .assign (local_ 0) (.use (.copy (derefPlace 2)))]

theorem twoPhaseDirectWriteTreeBorrowsGap_translate :
    (translateFn twoPhaseDirectWriteTreeBorrowsGap).isSome = true := by decide +kernel

theorem twoPhaseDirectWriteTreeBorrowsGap_notInFragment :
    inFragment twoPhaseDirectWriteTreeBorrowsGap = false := by decide +kernel

theorem twoPhaseDirectWriteTreeBorrowsGap_anneal_ub :
    ∃ tr u, Reaches (mirTree twoPhaseDirectWriteTreeBorrowsGap
      (initMachineState twoPhaseDirectWriteTreeBorrowsGap [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound twoPhaseDirectWriteTreeBorrowsGap 20 _ (by decide)

theorem twoPhaseDirectWriteTreeBorrowsGap_minirust_direct :
    retAfter twoPhaseDirectWriteTreeBorrowsGap [.scalar ⟨5, 4⟩] 6 =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) := by
  decide +kernel

/-- Mutably reborrowing `&mut (*_2)` from a `Frozen` shared reference `_2 = &_1`:
Anneal faults on the reborrow permission check (a `.frozen` parent entry rejects a
`.mut` borrow kind), while MiniRust's `BasicMemory` returns `5`. -/
def frozenRefMutReborrow : CapturedMir :=
  ptrBody "witness::frozen_ref_mut_reborrow" [u32Decl, u32Decl, refSharedU32Decl, refMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.ref .shared (local_ 1)),
     .assign (local_ 3) (.ref (.mut false) (derefPlace 2)),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem frozenRefMutReborrow_notInFragment :
    inFragment frozenRefMutReborrow = false := by decide +kernel

theorem frozenRefMutReborrow_anneal_ub :
    ∃ tr u, Reaches (mirTree frozenRefMutReborrow
      (initMachineState frozenRefMutReborrow [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound frozenRefMutReborrow 30 _ (by decide)

theorem frozenRefMutReborrow_minirust_direct :
    retAfter frozenRefMutReborrow [.scalar ⟨5, 4⟩] 7 =
      some (some { retAlloc with data := scalarBytes u32 5 }, [1]) := by
  decide +kernel

/-- Reborrowing `&(*_2)` from a reference disabled by a direct write `_1 = 9`:
Anneal faults (`parentEntry.perm != .disabled`), while MiniRust's `BasicMemory`
returns `9`. -/
def disabledRefReborrow : CapturedMir :=
  ptrBody "witness::disabled_ref_reborrow" [u32Decl, u32Decl, refMutU32Decl, refSharedU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 1) (.use (constU32 9)),
     .assign (local_ 3) (.ref .shared (derefPlace 2)),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem disabledRefReborrow_notInFragment :
    inFragment disabledRefReborrow = false := by decide +kernel

theorem disabledRefReborrow_anneal_ub :
    ∃ tr u, Reaches (mirTree disabledRefReborrow
      (initMachineState disabledRefReborrow [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound disabledRefReborrow 30 _ (by decide)

theorem disabledRefReborrow_minirust_direct :
    retAfter disabledRefReborrow [.scalar ⟨5, 4⟩] 8 =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

/-- Parent reuse after a child write: in
`_2 = &mut _1; _3 = &mut (*_2); (*_3) = 9; _0 = copy (*_2)`, the reborrow `_3`
(tag `2`) is a Tree Borrows child of `_2` (tag `1`, `parentTag`, unstable
`b076d6a3`), so writing through `_3` is a local write for `_2` and the later read
through `_2` succeeds (freezing the child) and returns `9`, as in Tree Borrows
and `BasicMemory`. (Before `b076d6a3`, Anneal's flat borrow list disabled the
parent and faulted here.) Because `stepReborrow` tracks Tree Borrows ancestor
sets (`i :: pPeers`) in `ptrAliasingOk`, `stepDerefWrite` preserves ancestor `_2`
after `(*_3) = 9` and admits `childReborrowWriteDisablesParent` in `inFragment`. -/
def childReborrowWriteDisablesParent : CapturedMir :=
  ptrBody "witness::child_reborrow_write_disables_parent"
    [u32Decl, u32Decl, refMutU32Decl, refMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.ref (.mut false) (derefPlace 2)),
     .assign (derefPlace 3) (.use (constU32 9)),
     .assign (local_ 0) (.use (.copy (derefPlace 2)))]

theorem childReborrowWriteDisablesParent_inFragment :
    inFragment childReborrowWriteDisablesParent = true := by decide +kernel

theorem childReborrowWriteDisablesParent_anneal_ret :
    ReachesRet (mirTree childReborrowWriteDisablesParent
      (initMachineState childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨9, 4⟩,
        { (initMachineState childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩]).memory with
          borrows := [{ rawPtrEntry 2 .mut (local_ 1) with perm := .frozen, parentTag := some 1 },
                      rawPtrEntry 1 .mut (local_ 1)],
          nextTag := 3 })) :=
  runA_sound childReborrowWriteDisablesParent 30 _ _ _ rfl

theorem childReborrowWriteDisablesParent_minirust_direct :
    retAfter childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩] 8 =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

/-! Since `childReborrowWriteDisablesParent` is now in-fragment (ancestor-tracking
`stepReborrow` keeps parent `_2` `.live` across the child write `(*_3) = 9`), the
generic simulation theorems `mirCall_ret` / `mirCall_noUB` transport Anneal's
return of `9` (a write through the `.reserved` child `_3`, which activates it and
is a local write for its `.active` parent `_2`, followed by a parent read that
freezes the child) to MiniRust's `Interp.steps`, symbolically rather than by
direct evaluation. -/

def childReborrowWriteDisablesParentFn : Gen.Function where
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
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .mut u32)),
      .Assign (.Deref (.Load (.Local (localName 3))) (.Int u32)) (.Constant (.Int 9) (.Int u32)),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem childReborrowWriteDisablesParent_translate :
    translateFn childReborrowWriteDisablesParent = some childReborrowWriteDisablesParentFn := rfl

def childReborrowWriteDisablesParentS0 : MachineState :=
  initMachineState childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩]
def childReborrowWriteDisablesParentMInit : Mach :=
  machine childReborrowWriteDisablesParent childReborrowWriteDisablesParentFn
    childReborrowWriteDisablesParentS0.frame.locals childReborrowWriteDisablesParentFn.start

theorem childReborrowWriteDisablesParent_noUB :
    MirNoUBTree (mirCallTree childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩]) :=
  runA_noUB childReborrowWriteDisablesParent 30 _ _ _ rfl

theorem childReborrowWriteDisablesParent_ctxOk : CtxOk childReborrowWriteDisablesParent ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : childReborrowWriteDisablesParent.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [childReborrowWriteDisablesParent, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [childReborrowWriteDisablesParent, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : childReborrowWriteDisablesParent.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [childReborrowWriteDisablesParent, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem childReborrowWriteDisablesParent_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n childReborrowWriteDisablesParentMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 9 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret childReborrowWriteDisablesParent_inFragment
      childReborrowWriteDisablesParent_translate ctx0 childReborrowWriteDisablesParent_ctxOk
      [.scalar ⟨5, 4⟩] (by decide) childReborrowWriteDisablesParentMInit
      rfl rfl rfl childReborrowWriteDisablesParent_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [childReborrowWriteDisablesParent, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem childReborrowWriteDisablesParent_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n childReborrowWriteDisablesParentMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k childReborrowWriteDisablesParentMInit = .ok mRet ∧
      ReturnRel childReborrowWriteDisablesParent ctx0 s' v mRet ∧
      ReachesRet (mirCallTree childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩]) tr
        (.normal (v, mem)) :=
  mirCall_noUB childReborrowWriteDisablesParent_inFragment
    childReborrowWriteDisablesParent_translate ctx0 childReborrowWriteDisablesParent_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) childReborrowWriteDisablesParentMInit
    rfl rfl rfl childReborrowWriteDisablesParent_noUB herr

theorem childReborrowWriteDisablesParent_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) childReborrowWriteDisablesParentMInit = .ok m' ∧
      StateRelN childReborrowWriteDisablesParent childReborrowWriteDisablesParentFn ctx0 s' m' ∧
      Reaches (mirCallTree childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩]) tr
        (mirTree childReborrowWriteDisablesParent s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k childReborrowWriteDisablesParentMInit = .ok mRet ∧
      ReturnRel childReborrowWriteDisablesParent ctx0 s' v mRet ∧
      ReachesRet (mirCallTree childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩]) tr
        (.normal (v, mem))) :=
  mirCall_progress_N childReborrowWriteDisablesParent_inFragment
    childReborrowWriteDisablesParent_translate ctx0 childReborrowWriteDisablesParent_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) childReborrowWriteDisablesParentMInit
    rfl rfl rfl childReborrowWriteDisablesParent_noUB n

/-! ### Ground truth for Tree Borrows `ReborrowSettings.new` -/

def sampleTbPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
  { thin_pointer := { addr := 64, provenance := none }, metadata := none }

def panicVtableLookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable :=
  fun _ => Interp.unsupported "no vtable in sized witness"

/-- Concrete instantiations of `ReborrowSettings.new` (`spec/mem/tree_borrows/reborrow_settings.md`)
across shared references (`Frozen` vs `Cell` inside `UnsafeCell`), mutable
references (`Reserved` unprotected vs `Prot (Reserved false false)` without
implicit writes vs `Prot Unique` on function entry with implicit writes),
`Box<u32>` (`Protected.Weak`), `!Unpin` mutable references (`none`), and raw
pointers (`none`). -/
theorem reborrowSettings_u32_examples :
    ReborrowSettings.new panicVtableLookup sampleTbPtr (refPtrType .not u32)
        false ⟨true⟩ true =
      .ok (some { inside := List.replicate 4 (.Unprot .Frozen)
                  outside := .Unprot .Frozen
                  «protected» := .No }) ∧
    ReborrowSettings.new panicVtableLookup sampleTbPtr
        (.Ref .Immutable { intPointeeInfo u32 with
          unsafe_cells := .Sized [(⟨0⟩, ⟨4⟩)], freeze := false })
        false ⟨true⟩ true =
      .ok (some { inside := List.replicate 4 (.Unprot .Cell)
                  outside := .Unprot .Cell
                  «protected» := .No }) ∧
    ReborrowSettings.new panicVtableLookup sampleTbPtr (refPtrType .mut u32)
        false ⟨true⟩ true =
      .ok (some { inside := List.replicate 4 (.Unprot .Reserved)
                  outside := .Unprot .Reserved
                  «protected» := .No }) ∧
    ReborrowSettings.new panicVtableLookup sampleTbPtr (refPtrType .mut u32)
        true ⟨true⟩ false =
      .ok (some { inside := List.replicate 4 (.Prot (.Reserved false false))
                  outside := .Prot (.Reserved false false)
                  «protected» := .Strong }) ∧
    ReborrowSettings.new panicVtableLookup sampleTbPtr (refPtrType .mut u32)
        true ⟨true⟩ true =
      .ok (some { inside := List.replicate 4 (.Prot .Unique)
                  outside := .Prot (.Reserved false false)
                  «protected» := .Strong }) ∧
    ReborrowSettings.new panicVtableLookup sampleTbPtr (.Box (intPointeeInfo u32))
        true ⟨true⟩ true =
      .ok (some { inside := List.replicate 4 (.Prot .Unique)
                  outside := .Prot (.Reserved false false)
                  «protected» := .Weak }) ∧
    ReborrowSettings.new panicVtableLookup sampleTbPtr
        (.Ref .Mutable { intPointeeInfo u32 with unpin := false })
        false ⟨true⟩ true =
      .ok none ∧
    ReborrowSettings.new panicVtableLookup sampleTbPtr (.Raw .None)
        true ⟨true⟩ true =
      .ok none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Ground truth for `CastOp::Transmute` to `&T` / `&mut T` and `Statement::Validate` -/

/-- `CastOp::Transmute` and `evalValue` `.UnOp (.Cast (.Transmute ...))` to
`refTy` thread `some m` into `checkValue`, accepting a live aligned pointer and
raising exact safe-pointer UB diagnostics for provenance-free (`PointerWithoutProvenance`),
out-of-bounds/non-dereferenceable, null, and unaligned pointers. -/
theorem transmute_refTy_machine_checks :
    evalCastOp (.Transmute (refTy .mut u32))
        (thinPtrVal 256 (some (⟨2⟩, ())), thinRawPtrTy) (some refSharedReadMInit) =
      .ok (thinPtrVal 256 (some (⟨2⟩, ())), refTy .mut u32) ∧
    evalValue refSharedReadMInit
        (.UnOp (.Cast (.Transmute (refTy .not u32)))
          (.Constant (.PointerWithoutProvenance 256) thinRawPtrTy)) =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    evalCastOp (.Transmute (refTy .not u32))
        (thinPtrVal 4 (some (⟨0⟩, ())), thinRawPtrTy) (some refSharedReadMInit) =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    evalCastOp (.Transmute (refTy .not u32))
        (thinPtrVal 0 (some (⟨2⟩, ())), thinRawPtrTy) (some refSharedReadMInit) =
      .error (.ub "Value::Ptr: null safe pointer") ∧
    evalCastOp (.Transmute (refTy .not u32))
        (thinPtrVal 258 (some (⟨2⟩, ())), thinRawPtrTy) (some refSharedReadMInit) =
      .error (.ub "Value::Ptr: unaligned safe pointer") :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Helper running `Statement::Validate { place, fn_entry }` after `n` steps from
`startMachine body args`, returning `Sum.inl ()` on `.ok` or `Sum.inr msg` on
`Stop.ub msg`. -/
def validateAfter (body : CapturedMir) (args : List Value) (n : Nat)
    (place : Gen.PlaceExpr) (fnEntry : Bool) : Option (Unit ⊕ String) :=
  (startMachine body args).bind fun m =>
    (Interp.steps n m).toOption.bind fun m' =>
      match evalStatement m' (.Validate place fnEntry) with
      | .ok _ => some (.inl ())
      | .error (.ub msg) => some (.inr msg)
      | .error _ => none

/-- `Statement::Validate` (`Machine::retag_val`) succeeds on an initialized live
`&u32` local (`fn_entry = true` and `fn_entry = false`), raises language-invariant
UB on an uninitialized `&u32` local, raises `"Value::Ptr: non-dereferenceable safe pointer"`
on a dangling `&u32` local after `StorageDead` of its referent, and traverses
aggregate `Type::Array` reference elements in `retagVal`. -/
theorem validate_refTy_machine_checks :
    validateAfter refSharedRead [.scalar ⟨5, 4⟩] 5 (.Local (localName 2)) true =
      some (.inl ()) ∧
    validateAfter refSharedRead [.scalar ⟨5, 4⟩] 5 (.Local (localName 2)) false =
      some (.inl ()) ∧
    validateAfter refSharedRead [.scalar ⟨5, 4⟩] 5 (.Local (localName 3)) false =
      some (.inr "load at type but the data in memory violates the language invariant") ∧
    validateAfter danglingRef [.scalar ⟨5, 4⟩] 6 (.Local (localName 3)) false =
      some (.inr "Value::Ptr: non-dereferenceable safe pointer") ∧
    retagVal refSharedReadMInit true
        (.Tuple [thinPtrVal 256 (some (⟨2⟩, ()))]) (.Array (refTy .not u32) 1) =
      .ok (.Tuple [thinPtrVal 256 (some (⟨2⟩, ()))]) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by
    unfold retagVal
    dsimp [List.mapM, List.mapM.loop, thinPtrVal, refTy]
    unfold retagVal
    rfl⟩

/-- `retagTupleFields` (`Machine::retag_val` on `Type::Tuple`) traverses matching
tuple fields and raises `Stop.specPanic "List::zip: lists have different lengths"`
when `Value::Tuple` and `Type::Tuple` have unequal field counts (matching
`libspecr::List::zip`). -/
theorem retagTupleFields_machine_checks :
    retagVal refSharedReadMInit false
        (.Tuple [thinPtrVal 256 (some (⟨2⟩, ())), .Int 9])
        (.Tuple [(⟨0⟩, refTy .not u32), (⟨8⟩, .Int u32)] ⟨⟨16⟩, ⟨8⟩, none⟩ none) =
      .ok (.Tuple [thinPtrVal 256 (some (⟨2⟩, ())), .Int 9]) ∧
    retagVal refSharedReadMInit false
        (.Tuple [.Int 1, .Int 2])
        (.Tuple [(⟨0⟩, .Int u32)] ⟨⟨4⟩, ⟨4⟩, none⟩ none) =
      .error (.specPanic "List::zip: lists have different lengths") ∧
    retagVal refSharedReadMInit false
        (.Tuple [])
        (.Tuple [(⟨0⟩, .Int u32)] ⟨⟨4⟩, ⟨4⟩, none⟩ none) =
      .error (.specPanic "List::zip: lists have different lengths") :=
  ⟨by
    unfold retagVal retagTupleFields
    dsimp [thinPtrVal, refTy]
    unfold retagVal retagTupleFields
    dsimp
    unfold retagVal retagTupleFields
    rfl,
   by
    unfold retagVal retagTupleFields
    dsimp
    unfold retagVal retagTupleFields
    rfl,
   by
    unfold retagVal retagTupleFields
    rfl⟩

/-! ### End-to-end `StatementKind.retag` -> `Statement.Validate` correspondence and Tree Borrows protector discrepancies -/

/-- Cross-kind `&mut -> *mut -> &mut -> &` reborrow chain with `StatementKind::Retag`
(`.default`, `.raw`, `.twoPhase`) lowered to `Statement::Validate { place, fn_entry: false }`,
plus a dereference write `(*_4) = _5 + 7` disabling ancestor tags `1` and `2`
while keeping `_4` (tag `3`) active for subsequent `Retag([twoPhase], _4)` and
shared reborrow `_6 = &(*_4)`: returns `5 + 7 = 12` in lockstep. -/
def retagRefReborrowChain : CapturedMir :=
  ptrBody "witness::retag_ref_reborrow_chain"
    [u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, refMutU32Decl, u32Decl, refSharedU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .retag .default (local_ 2),
     .assign (local_ 3) (.rawPtr .mut (derefPlace 2)),
     .retag .raw (local_ 3),
     .assign (local_ 4) (.ref (.mut false) (derefPlace 3)),
     .retag .default (local_ 4),
     .assign (local_ 5) (.copyForDeref (derefPlace 4)),
     .assign (derefPlace 4) (.binaryOp .add (.copy (local_ 5)) (constU32 7)),
     .retag .twoPhase (local_ 4),
     .assign (local_ 6) (.ref .shared (derefPlace 4)),
     .retag .default (local_ 6),
     .assign (local_ 0) (.use (.copy (derefPlace 6)))]

theorem retagRefReborrowChain_inFragment : inFragment retagRefReborrowChain = true := by decide

def retagRefReborrowChainFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, thinRawPtrTy),
    (localName 4, refTy .mut u32), (localName 5, .Int u32),
    (localName 6, refTy .not u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .StorageLive (localName 6),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Validate (.Local (localName 2)) false,
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (.Raw .None)),
      .Validate (.Local (localName 3)) false,
      .Assign (.Local (localName 4))
        (.AddrOf (.Deref (.Load (.Local (localName 3))) (.Int u32)) (refPtrType .mut u32)),
      .Validate (.Local (localName 4)) false,
      .Assign (.Local (localName 5)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 4))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 5))) (.Constant (.Int 7) (.Int u32))),
      .Validate (.Local (localName 4)) false,
      .Assign (.Local (localName 6))
        (.AddrOf (.Deref (.Load (.Local (localName 4))) (.Int u32)) (refPtrType .not u32)),
      .Validate (.Local (localName 6)) false,
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 6))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem retagRefReborrowChain_translate :
    translateFn retagRefReborrowChain = some retagRefReborrowChainFn := rfl

def retagRefReborrowChainS0 : MachineState :=
  initMachineState retagRefReborrowChain [.scalar ⟨5, 4⟩]
def retagRefReborrowChainMInit : Mach :=
  machine retagRefReborrowChain retagRefReborrowChainFn
    retagRefReborrowChainS0.frame.locals retagRefReborrowChainFn.start

theorem retagRefReborrowChain_anneal_ret :
    ReachesRet (mirTree retagRefReborrowChain retagRefReborrowChainS0) []
      (.normal (.scalar ⟨12, 4⟩,
        { retagRefReborrowChainS0.memory with
          borrows := [{ rawPtrEntry 7 .not (local_ 1) with parentTag := some 6 },
                      { rawPtrEntry 6 .not (local_ 1) with parentTag := some 5 },
                      { rawPtrEntry 5 .mut (local_ 1) with
                        perm := .reservedFrz false, parentTag := some 4 },
                      { rawPtrEntry 4 .mut (local_ 1) with parentTag := some 3 },
                      { rawPtrEntry 3 .mut (local_ 1) with parentTag := some 2 },
                      { rawPtrEntry 2 .mut (local_ 1) with parentTag := some 1 },
                      rawPtrEntry 1 .mut (local_ 1)],
          nextTag := 8 })) :=
  runA_sound retagRefReborrowChain 40 _ _ _ rfl

theorem retagRefReborrowChain_noUB :
    MirNoUBTree (mirCallTree retagRefReborrowChain [.scalar ⟨5, 4⟩]) :=
  runA_noUB retagRefReborrowChain 40 _ _ _ rfl

theorem retagRefReborrowChain_minirust_direct :
    retAfter retagRefReborrowChain [.scalar ⟨5, 4⟩] 19 =
      some (some { retAlloc with data := scalarBytes u32 12 }, [1]) := by
  decide +kernel

theorem retagRefReborrowChain_ctxOk : CtxOk retagRefReborrowChain ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : retagRefReborrowChain.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [retagRefReborrowChain, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [retagRefReborrowChain, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : retagRefReborrowChain.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [retagRefReborrowChain, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem retagRefReborrowChain_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n retagRefReborrowChainMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 12 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret retagRefReborrowChain_inFragment retagRefReborrowChain_translate ctx0
      retagRefReborrowChain_ctxOk [.scalar ⟨5, 4⟩] (by decide) retagRefReborrowChainMInit
      rfl rfl rfl retagRefReborrowChain_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [retagRefReborrowChain, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem retagRefReborrowChain_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n retagRefReborrowChainMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k retagRefReborrowChainMInit = .ok mRet ∧
      ReturnRel retagRefReborrowChain ctx0 s' v mRet ∧
      ReachesRet (mirCallTree retagRefReborrowChain [.scalar ⟨5, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB retagRefReborrowChain_inFragment retagRefReborrowChain_translate ctx0
    retagRefReborrowChain_ctxOk [.scalar ⟨5, 4⟩] (by decide) retagRefReborrowChainMInit
    rfl rfl rfl retagRefReborrowChain_noUB herr

theorem retagRefReborrowChain_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) retagRefReborrowChainMInit = .ok m' ∧
      StateRelN retagRefReborrowChain retagRefReborrowChainFn ctx0 s' m' ∧
      Reaches (mirCallTree retagRefReborrowChain [.scalar ⟨5, 4⟩]) tr
        (mirTree retagRefReborrowChain s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k retagRefReborrowChainMInit = .ok mRet ∧
      ReturnRel retagRefReborrowChain ctx0 s' v mRet ∧
      ReachesRet (mirCallTree retagRefReborrowChain [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N retagRefReborrowChain_inFragment retagRefReborrowChain_translate ctx0
    retagRefReborrowChain_ctxOk [.scalar ⟨5, 4⟩] (by decide) retagRefReborrowChainMInit
    rfl rfl rfl retagRefReborrowChain_noUB n

/-- `Retag([default], _2)` on an uninitialized `&u32` temporary `_2` is in the
fragment (`env[2] = .empty ≠ .disabled`) and raises UB in lockstep in both
semantics (`mirCall_ub`, `mirCall_steps_error`, `mirCall_outcome_N`). -/
def retagUninitRefUb : CapturedMir :=
  ptrBody "witness::retag_uninit_ref_ub" [u32Decl, u32Decl, refSharedU32Decl]
    [.storageLive 2,
     .retag .default (local_ 2),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem retagUninitRefUb_inFragment : inFragment retagUninitRefUb = true := by decide

def retagUninitRefUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, refTy .not u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Validate (.Local (localName 2)) false,
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem retagUninitRefUb_translate :
    translateFn retagUninitRefUb = some retagUninitRefUbFn := rfl

def retagUninitRefUbS0 : MachineState := initMachineState retagUninitRefUb [.scalar ⟨5, 4⟩]
def retagUninitRefUbMInit : Mach :=
  machine retagUninitRefUb retagUninitRefUbFn
    retagUninitRefUbS0.frame.locals retagUninitRefUbFn.start

theorem retagUninitRefUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree retagUninitRefUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound retagUninitRefUb 10 _ (by decide)

theorem retagUninitRefUb_ctxOk : CtxOk retagUninitRefUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : retagUninitRefUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [retagUninitRefUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [retagUninitRefUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : retagUninitRefUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [retagUninitRefUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem retagUninitRefUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n retagUninitRefUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := retagUninitRefUb_anneal_ub
  exact mirCall_ub retagUninitRefUb_inFragment retagUninitRefUb_translate ctx0
    retagUninitRefUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) retagUninitRefUbMInit rfl rfl rfl hr hf

theorem retagUninitRefUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n retagUninitRefUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree retagUninitRefUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k retagUninitRefUbMInit = .ok mRet ∧
      ReturnRel retagUninitRefUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree retagUninitRefUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error retagUninitRefUb_inFragment retagUninitRefUb_translate ctx0
    retagUninitRefUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) retagUninitRefUbMInit rfl rfl rfl herr

theorem retagUninitRefUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) retagUninitRefUbMInit = .ok m' ∧
      StateRelN retagUninitRefUb retagUninitRefUbFn ctx0 s' m' ∧
      Reaches (mirCallTree retagUninitRefUb [.scalar ⟨5, 4⟩]) tr
        (mirTree retagUninitRefUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k retagUninitRefUbMInit = .ok mRet ∧
      ReturnRel retagUninitRefUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree retagUninitRefUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) retagUninitRefUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree retagUninitRefUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N retagUninitRefUb_inFragment retagUninitRefUb_translate ctx0
    retagUninitRefUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) retagUninitRefUbMInit rfl rfl rfl n

theorem retagUninitRefUb_minirust_direct :
    ubAfter retagUninitRefUb [.scalar ⟨5, 4⟩] 3 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- Function-entry Tree Borrows protector discrepancy (`Retag([fn entry], _2)`):
`translateFn` lowers `RetagKind::FnEntry` to `Statement::Validate { place: _2, fn_entry: true }`,
while `statementOk` excludes `.fnEntry` from `inFragment`. In Anneal,
`Retag([fn entry], _2)` attaches a live Tree Borrows protector to `_2`
(`attachBorrowProtector` + `activeProtectors`), so a subsequent direct write
`_1 = 9` faults *immediately* at `_1 = 9` (`hasProtectedWriteConflict = true`)
even though `_2` is never dereferenced again, whereas MiniRust's `BasicMemory`
returns `9`. -/
def retagFnEntryProtectorWrite : CapturedMir :=
  ptrBody "witness::retag_fn_entry_protector_write" [u32Decl, u32Decl, refMutU32Decl]
    [.storageLive 2,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .retag .fnEntry (local_ 2),
     .assign (local_ 1) (.use (constU32 9)),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem retagFnEntryProtectorWrite_translate :
    (translateFn retagFnEntryProtectorWrite).isSome = true := by decide +kernel

theorem retagFnEntryProtectorWrite_notInFragment :
    inFragment retagFnEntryProtectorWrite = false := by decide +kernel

theorem retagFnEntryProtectorWrite_anneal_ub :
    ∃ tr u, Reaches (mirTree retagFnEntryProtectorWrite
      (initMachineState retagFnEntryProtectorWrite [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound retagFnEntryProtectorWrite 20 _ (by decide)

theorem retagFnEntryProtectorWrite_minirust_direct :
    retAfter retagFnEntryProtectorWrite [.scalar ⟨5, 4⟩] 7 =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

/-- Retagging a parent after a child write
(`_2 = &mut _1; _3 = &mut (*_2); (*_3) = 9; Retag([default], _2)`): since
unstable `b076d6a3`, Anneal links `_3` to its parent `_2` (`parentTag`), the
child write keeps `_2` active (and `stepReborrow` / `stepDerefWrite` preserve
ancestor `_2` in `inFragment`), and Anneal returns `9` like MiniRust's
`BasicMemory` and `MachTB` (before `b076d6a3`, Anneal's flat borrow list
disabled `_2` and faulted at the `Retag`). -/
def retagDisabledRefDiscrepancy : CapturedMir :=
  ptrBody "witness::retag_disabled_ref_discrepancy"
    [u32Decl, u32Decl, refMutU32Decl, refMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.ref (.mut false) (derefPlace 2)),
     .assign (derefPlace 3) (.use (constU32 9)),
     .retag .default (local_ 2),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem retagDisabledRefDiscrepancy_translate :
    (translateFn retagDisabledRefDiscrepancy).isSome = true := by decide +kernel

theorem retagDisabledRefDiscrepancy_inFragment :
    inFragment retagDisabledRefDiscrepancy = true := by decide +kernel

theorem retagDisabledRefDiscrepancy_anneal_ret :
    ReachesRet (mirTree retagDisabledRefDiscrepancy
      (initMachineState retagDisabledRefDiscrepancy [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨9, 4⟩,
        { (initMachineState retagDisabledRefDiscrepancy [.scalar ⟨5, 4⟩]).memory with
          borrows := [{ rawPtrEntry 3 .mut (local_ 1) with
                        perm := .reservedFrz false, parentTag := some 1 },
                      { rawPtrEntry 2 .mut (local_ 1) with
                        perm := .frozen, parentTag := some 1 },
                      rawPtrEntry 1 .mut (local_ 1)],
          nextTag := 4 })) :=
  runA_sound retagDisabledRefDiscrepancy 25 _ _ _ rfl

theorem retagDisabledRefDiscrepancy_minirust_direct :
    retAfter retagDisabledRefDiscrepancy [.scalar ⟨5, 4⟩] 9 =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

/-! `retagDisabledRefDiscrepancy` is likewise in-fragment now, so `mirCall_ret` /
`mirCall_noUB` transport Anneal's return of `9` (a write through the `.reserved`
child `_3`, local for its `.active` parent `_2`, then `Retag([default], _2)`
lowered to `Statement::Validate`) to MiniRust's `Interp.steps`. -/

def retagDisabledRefDiscrepancyFn : Gen.Function where
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
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .mut u32)),
      .Assign (.Deref (.Load (.Local (localName 3))) (.Int u32)) (.Constant (.Int 9) (.Int u32)),
      .Validate (.Local (localName 2)) false,
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem retagDisabledRefDiscrepancy_translate_eq :
    translateFn retagDisabledRefDiscrepancy = some retagDisabledRefDiscrepancyFn := rfl

def retagDisabledRefDiscrepancyS0 : MachineState :=
  initMachineState retagDisabledRefDiscrepancy [.scalar ⟨5, 4⟩]
def retagDisabledRefDiscrepancyMInit : Mach :=
  machine retagDisabledRefDiscrepancy retagDisabledRefDiscrepancyFn
    retagDisabledRefDiscrepancyS0.frame.locals retagDisabledRefDiscrepancyFn.start

theorem retagDisabledRefDiscrepancy_noUB :
    MirNoUBTree (mirCallTree retagDisabledRefDiscrepancy [.scalar ⟨5, 4⟩]) :=
  runA_noUB retagDisabledRefDiscrepancy 25 _ _ _ rfl

theorem retagDisabledRefDiscrepancy_ctxOk : CtxOk retagDisabledRefDiscrepancy ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : retagDisabledRefDiscrepancy.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [retagDisabledRefDiscrepancy, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [retagDisabledRefDiscrepancy, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : retagDisabledRefDiscrepancy.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [retagDisabledRefDiscrepancy, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem retagDisabledRefDiscrepancy_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n retagDisabledRefDiscrepancyMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 9 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret retagDisabledRefDiscrepancy_inFragment
      retagDisabledRefDiscrepancy_translate_eq ctx0 retagDisabledRefDiscrepancy_ctxOk
      [.scalar ⟨5, 4⟩] (by decide) retagDisabledRefDiscrepancyMInit
      rfl rfl rfl retagDisabledRefDiscrepancy_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [retagDisabledRefDiscrepancy, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem retagDisabledRefDiscrepancy_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n retagDisabledRefDiscrepancyMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k retagDisabledRefDiscrepancyMInit = .ok mRet ∧
      ReturnRel retagDisabledRefDiscrepancy ctx0 s' v mRet ∧
      ReachesRet (mirCallTree retagDisabledRefDiscrepancy [.scalar ⟨5, 4⟩]) tr
        (.normal (v, mem)) :=
  mirCall_noUB retagDisabledRefDiscrepancy_inFragment
    retagDisabledRefDiscrepancy_translate_eq ctx0 retagDisabledRefDiscrepancy_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) retagDisabledRefDiscrepancyMInit
    rfl rfl rfl retagDisabledRefDiscrepancy_noUB herr

theorem retagDisabledRefDiscrepancy_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) retagDisabledRefDiscrepancyMInit = .ok m' ∧
      StateRelN retagDisabledRefDiscrepancy retagDisabledRefDiscrepancyFn ctx0 s' m' ∧
      Reaches (mirCallTree retagDisabledRefDiscrepancy [.scalar ⟨5, 4⟩]) tr
        (mirTree retagDisabledRefDiscrepancy s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k retagDisabledRefDiscrepancyMInit = .ok mRet ∧
      ReturnRel retagDisabledRefDiscrepancy ctx0 s' v mRet ∧
      ReachesRet (mirCallTree retagDisabledRefDiscrepancy [.scalar ⟨5, 4⟩]) tr
        (.normal (v, mem))) :=
  mirCall_progress_N retagDisabledRefDiscrepancy_inFragment
    retagDisabledRefDiscrepancy_translate_eq ctx0 retagDisabledRefDiscrepancy_ctxOk
    [.scalar ⟨5, 4⟩] (by decide) retagDisabledRefDiscrepancyMInit
    rfl rfl rfl retagDisabledRefDiscrepancy_noUB n

/-- Scalar `Retag([default], _1)` on `u32` parameter `_1`:
`translateFn` lowers `Retag` to `Statement::Validate`, while `statementOk`
restricts `Retag` to pointer/reference locals (`isDeclPtrLocal`). Under the
merged `LM-3.3` `Trusted` `evalStmt` `.retag` dispatch (from `05658250`, kept by
the `9ffc1853` merge; `314c4453`'s `extractDerefPtrVal?` dispatch instead faulted
on scalars), a place whose type is neither `.rawPtr` nor `.ref` holding a
non-pointer scalar value is a no-op, so Anneal returns `5`, now agreeing with
MiniRust's `Machine::retag_val` (`Value::Int` no-op) on both `BasicMemory`
(`retagScalarDiscrepancy_minirust_direct`) and `MachTB`
(`retagScalarDiscrepancy_tb_direct`). -/
def retagScalarDiscrepancy : CapturedMir :=
  ptrBody "witness::retag_scalar_discrepancy" [u32Decl, u32Decl]
    [.retag .default (local_ 1),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem retagScalarDiscrepancy_translate :
    (translateFn retagScalarDiscrepancy).isSome = true := by decide +kernel

theorem retagScalarDiscrepancy_notInFragment :
    inFragment retagScalarDiscrepancy = false := by decide +kernel

theorem retagScalarDiscrepancy_anneal_ret :
    ReachesRet (mirTree retagScalarDiscrepancy
      (initMachineState retagScalarDiscrepancy [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨5, 4⟩,
        (initMachineState retagScalarDiscrepancy [.scalar ⟨5, 4⟩]).memory)) :=
  runA_sound retagScalarDiscrepancy 15 _ _ _ rfl

theorem retagScalarDiscrepancy_minirust_direct :
    retAfter retagScalarDiscrepancy [.scalar ⟨5, 4⟩] 4 =
      some (some { retAlloc with data := scalarBytes u32 5 }, [1]) := by
  decide +kernel

/-! ### End-to-end `CastKind.transmute` pointer/reference correspondence and discrepancies -/

/-- Cross-kind `CastKind::Transmute` chain across `&mut u32`, `*mut u32`, `&u32`,
and `*const u32` (including `Operand.move` out of non-`Copy` `&mut u32`):
```rust
fn ref_raw_transmute_chain(mut x: u32) -> u32 {
    let r: &mut u32 = &mut x;                     // _2 = &mut _1
    let p: *mut u32 = transmute(r);               // _3 = move _2 as *mut u32 (Transmute)
    let t: u32 = unsafe { *p };                   // _4 = copy (*_3)
    unsafe { *p = t + 10 };                       // (*_3) = Add(copy _4, const 10_u32)
    let s: &u32 = unsafe { transmute(p) };        // _5 = copy _3 as &u32 (Transmute)
    let q: *const u32 = unsafe { transmute(s) };  // _6 = copy _5 as *const u32 (Transmute)
    unsafe { *q }                                 // _0 = copy (*_6)
}
```
Returns `5 + 10 = 15` in lockstep. -/
def refRawTransmuteChain : CapturedMir :=
  ptrBody "witness::ref_raw_transmute_chain"
    [u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, u32Decl, refSharedU32Decl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.cast .transmute (.move (local_ 2)) ptrMutU32Ty),
     .assign (local_ 4) (.use (.copy (derefPlace 3))),
     .assign (derefPlace 3) (.binaryOp .add (.copy (local_ 4)) (constU32 10)),
     .assign (local_ 5) (.cast .transmute (.copy (local_ 3)) refSharedU32Ty),
     .assign (local_ 6) (.cast .transmute (.copy (local_ 5)) ptrConstU32Ty),
     .assign (local_ 0) (.use (.copy (derefPlace 6)))]

theorem refRawTransmuteChain_inFragment : inFragment refRawTransmuteChain = true := by decide

def refRawTransmuteChainFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, thinRawPtrTy),
    (localName 4, .Int u32), (localName 5, refTy .not u32),
    (localName 6, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .StorageLive (localName 6),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Local (localName 3))
        (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 4)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 3))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 4))) (.Constant (.Int 10) (.Int u32))),
      .Assign (.Local (localName 5))
        (.UnOp (.Cast (.Transmute (refTy .not u32))) (.Load (.Local (localName 3)))),
      .Assign (.Local (localName 6))
        (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 5)))),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 6))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem refRawTransmuteChain_translate :
    translateFn refRawTransmuteChain = some refRawTransmuteChainFn := rfl

def refRawTransmuteChainS0 : MachineState :=
  initMachineState refRawTransmuteChain [.scalar ⟨5, 4⟩]
def refRawTransmuteChainMInit : Mach :=
  machine refRawTransmuteChain refRawTransmuteChainFn
    refRawTransmuteChainS0.frame.locals refRawTransmuteChainFn.start

theorem refRawTransmuteChain_anneal_ret :
    ReachesRet (mirTree refRawTransmuteChain refRawTransmuteChainS0) []
      (.normal (.scalar ⟨15, 4⟩,
        { refRawTransmuteChainS0.memory with
          borrows := [rawPtrEntry 1 .mut (local_ 1)],
          nextTag := 2 })) :=
  runA_sound refRawTransmuteChain 35 _ _ _ rfl

theorem refRawTransmuteChain_noUB :
    MirNoUBTree (mirCallTree refRawTransmuteChain [.scalar ⟨5, 4⟩]) :=
  runA_noUB refRawTransmuteChain 35 _ _ _ rfl

theorem refRawTransmuteChain_minirust_direct :
    retAfter refRawTransmuteChain [.scalar ⟨5, 4⟩] 14 =
      some (some { retAlloc with data := scalarBytes u32 15 }, [1]) := by
  decide +kernel

theorem refRawTransmuteChain_ctxOk : CtxOk refRawTransmuteChain ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : refRawTransmuteChain.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [refRawTransmuteChain, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [refRawTransmuteChain, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : refRawTransmuteChain.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [refRawTransmuteChain, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem refRawTransmuteChain_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n refRawTransmuteChainMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 15 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret refRawTransmuteChain_inFragment refRawTransmuteChain_translate ctx0
      refRawTransmuteChain_ctxOk [.scalar ⟨5, 4⟩] (by decide) refRawTransmuteChainMInit
      rfl rfl rfl refRawTransmuteChain_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [refRawTransmuteChain, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem refRawTransmuteChain_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n refRawTransmuteChainMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k refRawTransmuteChainMInit = .ok mRet ∧
      ReturnRel refRawTransmuteChain ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refRawTransmuteChain [.scalar ⟨5, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB refRawTransmuteChain_inFragment refRawTransmuteChain_translate ctx0
    refRawTransmuteChain_ctxOk [.scalar ⟨5, 4⟩] (by decide) refRawTransmuteChainMInit
    rfl rfl rfl refRawTransmuteChain_noUB herr

theorem refRawTransmuteChain_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) refRawTransmuteChainMInit = .ok m' ∧
      StateRelN refRawTransmuteChain refRawTransmuteChainFn ctx0 s' m' ∧
      Reaches (mirCallTree refRawTransmuteChain [.scalar ⟨5, 4⟩]) tr
        (mirTree refRawTransmuteChain s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k refRawTransmuteChainMInit = .ok mRet ∧
      ReturnRel refRawTransmuteChain ctx0 s' v mRet ∧
      ReachesRet (mirCallTree refRawTransmuteChain [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N refRawTransmuteChain_inFragment refRawTransmuteChain_translate ctx0
    refRawTransmuteChain_ctxOk [.scalar ⟨5, 4⟩] (by decide) refRawTransmuteChainMInit
    rfl rfl rfl refRawTransmuteChain_noUB n

/-- Transmuting an uninitialized `&u32` temporary `_2` to `*const u32` (`_3`) lies
in the fragment and raises UB in lockstep in both semantics (`mirCall_ub`,
`mirCall_steps_error`, `mirCall_outcome_N`). -/
def transmuteUninitRefUb : CapturedMir :=
  ptrBody "witness::transmute_uninit_ref_ub"
    [u32Decl, u32Decl, refSharedU32Decl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 3) (.cast .transmute (.copy (local_ 2)) ptrConstU32Ty),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem transmuteUninitRefUb_inFragment : inFragment transmuteUninitRefUb = true := by decide

def transmuteUninitRefUbFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .not u32), (localName 3, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem transmuteUninitRefUb_translate :
    translateFn transmuteUninitRefUb = some transmuteUninitRefUbFn := rfl

def transmuteUninitRefUbS0 : MachineState :=
  initMachineState transmuteUninitRefUb [.scalar ⟨5, 4⟩]
def transmuteUninitRefUbMInit : Mach :=
  machine transmuteUninitRefUb transmuteUninitRefUbFn
    transmuteUninitRefUbS0.frame.locals transmuteUninitRefUbFn.start

theorem transmuteUninitRefUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree transmuteUninitRefUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound transmuteUninitRefUb 15 _ (by decide)

theorem transmuteUninitRefUb_ctxOk : CtxOk transmuteUninitRefUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : transmuteUninitRefUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [transmuteUninitRefUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [transmuteUninitRefUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : transmuteUninitRefUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [transmuteUninitRefUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem transmuteUninitRefUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n transmuteUninitRefUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := transmuteUninitRefUb_anneal_ub
  exact mirCall_ub transmuteUninitRefUb_inFragment transmuteUninitRefUb_translate ctx0
    transmuteUninitRefUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) transmuteUninitRefUbMInit rfl rfl rfl hr hf

theorem transmuteUninitRefUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n transmuteUninitRefUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree transmuteUninitRefUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k transmuteUninitRefUbMInit = .ok mRet ∧
      ReturnRel transmuteUninitRefUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree transmuteUninitRefUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error transmuteUninitRefUb_inFragment transmuteUninitRefUb_translate ctx0
    transmuteUninitRefUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) transmuteUninitRefUbMInit rfl rfl rfl herr

theorem transmuteUninitRefUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) transmuteUninitRefUbMInit = .ok m' ∧
      StateRelN transmuteUninitRefUb transmuteUninitRefUbFn ctx0 s' m' ∧
      Reaches (mirCallTree transmuteUninitRefUb [.scalar ⟨5, 4⟩]) tr
        (mirTree transmuteUninitRefUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k transmuteUninitRefUbMInit = .ok mRet ∧
      ReturnRel transmuteUninitRefUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree transmuteUninitRefUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) transmuteUninitRefUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree transmuteUninitRefUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N transmuteUninitRefUb_inFragment transmuteUninitRefUb_translate ctx0
    transmuteUninitRefUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) transmuteUninitRefUbMInit rfl rfl rfl n

theorem transmuteUninitRefUb_minirust_direct :
    ubAfter transmuteUninitRefUb [.scalar ⟨5, 4⟩] 4 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- Transmuting `&u32` (`Frozen`) to `&mut u32` and writing through it
(`_2 = &_1; _3 = copy _2 as &mut u32 (Transmute); (*_3) = 77; _0 = copy _1`):
`ptrRvalueOk` rejects mutability-upgrading transmutes (`srcMutbl = .not`,
`mutbl = .mut`), so `inFragment` is `false`. Anneal faults on the dereference
write because tag `1` has `perm = .frozen`, while MiniRust's `BasicMemory`
returns `77`. -/
def transmuteSharedRefToMutWriteDiscrepancy : CapturedMir :=
  ptrBody "witness::transmute_shared_ref_to_mut_write_discrepancy"
    [u32Decl, u32Decl, refSharedU32Decl, refMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.ref .shared (local_ 1)),
     .assign (local_ 3) (.cast .transmute (.copy (local_ 2)) refMutU32Ty),
     .assign (derefPlace 3) (.use (constU32 77)),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem transmuteSharedRefToMutWriteDiscrepancy_translate :
    (translateFn transmuteSharedRefToMutWriteDiscrepancy).isSome = true := by decide +kernel

theorem transmuteSharedRefToMutWriteDiscrepancy_notInFragment :
    inFragment transmuteSharedRefToMutWriteDiscrepancy = false := by decide +kernel

theorem transmuteSharedRefToMutWriteDiscrepancy_anneal_ub :
    ∃ tr u, Reaches (mirTree transmuteSharedRefToMutWriteDiscrepancy
      (initMachineState transmuteSharedRefToMutWriteDiscrepancy [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound transmuteSharedRefToMutWriteDiscrepancy 25 _ (by decide)

theorem transmuteSharedRefToMutWriteDiscrepancy_minirust_direct :
    retAfter transmuteSharedRefToMutWriteDiscrepancy [.scalar ⟨5, 4⟩] 8 =
      some (some { retAlloc with data := scalarBytes u32 77 }, [1]) := by
  decide +kernel

/-- Transmuting an aligned non-null integer (`4_usize`) to `&u32` without ever
dereferencing it (`_2 = 4_usize; _3 = copy _2 as &u32 (Transmute); _0 = copy _1`):
`ptrRvalueOk` excludes integer-to-pointer transmutes (`notInFragment = true`),
and both Anneal (`decodeValueFromBytes` safe-reference dereferenceability check)
and MiniRust (`CastOp::Transmute` `Value::check`) raise UB immediately
(see `transmuteDanglingIntToRefDiscrepancy_three_way_ub_agreement` below). -/
def transmuteDanglingIntToRefDiscrepancy : CapturedMir :=
  ptrBody "witness::transmute_dangling_int_to_ref_discrepancy"
    [u32Decl, u32Decl, usizeDecl, refSharedU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.use (constUsize 4)),
     .assign (local_ 3) (.cast .transmute (.copy (local_ 2)) refSharedU32Ty),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem transmuteDanglingIntToRefDiscrepancy_translate :
    (translateFn transmuteDanglingIntToRefDiscrepancy).isSome = true := by decide +kernel

theorem transmuteDanglingIntToRefDiscrepancy_notInFragment :
    inFragment transmuteDanglingIntToRefDiscrepancy = false := by decide +kernel

theorem transmuteDanglingIntToRefDiscrepancy_anneal_ub :
    ∃ tr u, Reaches (mirTree transmuteDanglingIntToRefDiscrepancy
      (initMachineState transmuteDanglingIntToRefDiscrepancy [.scalar ⟨5, 4⟩])) tr u ∧
      FaultNow u :=
  faultsA_sound transmuteDanglingIntToRefDiscrepancy 20 _ (by decide)

theorem transmuteDanglingIntToRefDiscrepancy_minirust_ub :
    ubAfter transmuteDanglingIntToRefDiscrepancy [.scalar ⟨5, 4⟩] 5 =
      some "Value::Ptr: non-dereferenceable safe pointer" := by
  decide +kernel

/-! ### Executable ground-truth `TreeBorrowsMemory` trace witnesses (`spec/mem/tree_borrows/*`) -/

/-- Little-endian 4-byte `TreeBorrowsProvenance` payload with low byte `b0`. -/
def tbU32Bytes (b0 : UInt8) : List (Gen.AbstractByte Gen.TreeBorrowsProvenance) :=
  [.Init b0 none, .Init 0 none, .Init 0 none, .Init 0 none]

/-- Decidable projection of a `TreeBorrowsMemory` byte-load result (`Sum.inl` on
`.ok` byte payloads, `Sum.inr msg` on `Stop.ub msg`, `none` otherwise). -/
def tbBytesOutcome (r : Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance))) :
    Option (List (Option UInt8) ⊕ String) :=
  match r with
  | .ok bs => some (.inl (bs.map fun
      | .Uninit => none
      | .Init b _ => some b))
  | .error (.ub msg) => some (.inr msg)
  | .error _ => none

/-- Decidable projection of a unit/state `TreeBorrowsMemory` trace (`Sum.inl ()`
on `.ok`, `Sum.inr msg` on `Stop.ub msg`, `none` otherwise). -/
def tbUnitOutcome {α : Type} (r : Interp α) : Option (Unit ⊕ String) :=
  match r with
  | .ok _ => some (.inl ())
  | .error (.ub msg) => some (.inr msg)
  | .error _ => none

/-- Ground-truth `TreeBorrowsMemory` trace corresponding to
`childReborrowWriteDisablesParent`: allocate a 4-byte stack slot, retag a parent
`&mut u32` (`[0]`, `Reserved`), retag a child `&mut u32` (`[0, 0]`, `Reserved`),
write `9` through the child (`Reserved -> Unique` on both `[0]` and `[0, 0]`),
and read back `9` through the parent (`[0]`), confirming that upstream Tree
Borrows' hierarchical tree preserves the parent after a child write. -/
def tbChildWritePreservesParentTrace :
    Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 5) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
    { thin_pointer := rootThin, metadata := none }
  let (parentPtr, tbm3, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr (refPtrType .mut u32) false true panicVtableLookup
  let (childPtr, tbm4, _frame2) ←
    TreeBorrowsMemory.retag_ptr tbm3 frame1 parentPtr (refPtrType .mut u32) false true panicVtableLookup
  let tbm5 ← TreeBorrowsMemory.store tbm4 childPtr.thin_pointer (tbU32Bytes 9) ⟨4⟩
  let (loaded, _tbm6) ← TreeBorrowsMemory.load tbm5 parentPtr.thin_pointer ⟨4⟩ ⟨4⟩
  pure loaded

theorem treeBorrowsChildWritePreservesParent :
    tbBytesOutcome tbChildWritePreservesParentTrace =
      some (.inl [some 9, some 0, some 0, some 0]) := by
  decide +kernel

/-- Ground-truth `TreeBorrowsMemory` UB traces for writing through an unprotected
`Frozen` shared reference `&u32` and reading through a sibling `&mut u32`
invalidated (`Reserved -> Disabled`) by a foreign write. -/
def tbFrozenWriteTrace : Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 5) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
    { thin_pointer := rootThin, metadata := none }
  let (sharedPtr, tbm3, _frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr (refPtrType .not u32) false true panicVtableLookup
  TreeBorrowsMemory.store tbm3 sharedPtr.thin_pointer (tbU32Bytes 9) ⟨4⟩

def tbSiblingWriteDisablesReadTrace :
    Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 5) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
    { thin_pointer := rootThin, metadata := none }
  let (r1, tbm3, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr (refPtrType .mut u32) false true panicVtableLookup
  let (r2, tbm4, _frame2) ←
    TreeBorrowsMemory.retag_ptr tbm3 frame1 rootPtr (refPtrType .mut u32) false true panicVtableLookup
  let tbm5 ← TreeBorrowsMemory.store tbm4 r2.thin_pointer (tbU32Bytes 99) ⟨4⟩
  let (loaded, _tbm6) ← TreeBorrowsMemory.load tbm5 r1.thin_pointer ⟨4⟩ ⟨4⟩
  pure loaded

theorem treeBorrowsFrozenAndDisabledUb :
    tbUnitOutcome tbFrozenWriteTrace =
      some (.inr "Tree Borrows: local write of Frozen reference") ∧
    tbBytesOutcome tbSiblingWriteDisablesReadTrace =
      some (.inr "Tree Borrows: local read of Disabled reference") :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- Ground-truth `TreeBorrowsMemory` counterpart to `twoPhaseDirectWriteTreeBorrowsGap`:
writing directly through the root allocation tag (`[]`) is a foreign write to an
unprotected `Freeze` `&mut u32` child (`[0]`, `Reserved`), transitioning it to
`Disabled`, so reading through the child afterwards raises
`"Tree Borrows: local read of Disabled reference"`. -/
def tbDirectWriteDisablesUnprotReservedTrace :
    Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 5) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
    { thin_pointer := rootThin, metadata := none }
  let (twoPhasePtr, tbm3, _frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr (refPtrType .mut u32) false true panicVtableLookup
  let tbm4 ← TreeBorrowsMemory.store tbm3 rootThin (tbU32Bytes 99) ⟨4⟩
  let (loaded, _tbm5) ← TreeBorrowsMemory.load tbm4 twoPhasePtr.thin_pointer ⟨4⟩ ⟨4⟩
  pure loaded

theorem treeBorrowsDirectWriteDisablesUnprotReserved :
    tbBytesOutcome tbDirectWriteDisablesUnprotReservedTrace =
      some (.inr "Tree Borrows: local read of Disabled reference") := by
  decide +kernel

/-- Ground-truth `TreeBorrowsMemory` protector lifecycle checks
(`spec/mem/tree_borrows/{state_machine_protected,tree,memory}.md`):
1. A foreign read while a function-entry `&mut u32` (`fn_entry = true`,
   `fn_implicit_writes = false`, `Protected::Strong`, `Prot (Reserved false false)`)
   is protected sets `had_foreign_read = true` and blocks subsequent local writes.
2. Deallocating through a strongly protected `Unique` reference before `end_call`
   raises `"Tree Borrows: deallocating strongly protected allocation"`.
3. Releasing the frame's protectors via `TreeBorrowsMemory.end_call` converts
   `Protected::Strong` to `Protected::No` and allows subsequent deallocation. -/
def tbProtReservedForeignReadThenLocalWriteTrace : Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 5) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
    { thin_pointer := rootThin, metadata := none }
  let (protPtr, tbm3, _frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr (refPtrType .mut u32) true false panicVtableLookup
  let (_loaded, tbm4) ← TreeBorrowsMemory.load tbm3 rootThin ⟨4⟩ ⟨4⟩
  TreeBorrowsMemory.store tbm4 protPtr.thin_pointer (tbU32Bytes 9) ⟨4⟩

def tbDeallocStrongProtectedTrace : Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 5) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
    { thin_pointer := rootThin, metadata := none }
  let (protPtr, tbm3, _frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr (refPtrType .mut u32) true true panicVtableLookup
  TreeBorrowsMemory.deallocate tbm3 protPtr.thin_pointer .Stack ⟨4⟩ ⟨4⟩

def tbEndCallThenDeallocTrace : Interp Unit := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 5) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
    { thin_pointer := rootThin, metadata := none }
  let (protPtr, tbm3, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr (refPtrType .mut u32) true true panicVtableLookup
  let tbm4 ← TreeBorrowsMemory.end_call tbm3 frame1
  let tbm5 ← TreeBorrowsMemory.deallocate tbm4 protPtr.thin_pointer .Stack ⟨4⟩ ⟨4⟩
  TreeBorrowsMemory.leak_check tbm5

theorem treeBorrowsProtectorEndAndDeallocChecks :
    tbUnitOutcome tbProtReservedForeignReadThenLocalWriteTrace =
      some (.inr "Tree Borrows: local write to protected Reserved reference that had a foreign read") ∧
    tbUnitOutcome tbDeallocStrongProtectedTrace =
      some (.inr "Tree Borrows: deallocating strongly protected allocation") ∧
    tbUnitOutcome tbEndCallThenDeallocTrace = some (.inl ()) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### End-to-end polymorphic `Machine<TreeBorrowsMemory<x86_64>>` (`MachTB`) 3-way witnesses -/

/-! #### 1. In-fragment normal-return agreement on `MachTB` -/

theorem refSharedRead_tb_direct :
    retAfterTB refSharedRead [.scalar ⟨5, 4⟩] 9 = tbRetU32 5 := by
  decide +kernel

theorem refMutRoundTrip_tb_direct :
    retAfterTB refMutRoundTrip [.scalar ⟨5, 4⟩] 12 = tbRetU32 6 := by
  decide +kernel

theorem refArrayReborrowChain_tb_direct :
    retAfterTB refArrayReborrowChain [initArrU32_2] 27 = tbRetU32 42 := by
  decide +kernel

theorem refPaddedStructReborrow_tb_direct :
    retAfterTB refPaddedStructReborrow [initPaddedStruct] 20 = tbRetU32 1641 := by
  decide +kernel

theorem refMutReborrowWrite_tb_direct :
    retAfterTB refMutReborrowWrite [.scalar ⟨5, 4⟩] 18 = tbRetU32 15 := by
  decide +kernel

theorem refDisjointReborrowWrite_tb_direct :
    retAfterTB refDisjointReborrowWrite [initArrU32_2] 21 = tbRetU32 42 := by
  decide +kernel

theorem refLoopCountdown_tb_direct :
    retAfterTB refLoopCountdown [.scalar ⟨3, 4⟩] 62 = tbRetU32 6 := by
  decide +kernel

theorem refTwoPhaseBorrowRoundTrip_tb_direct :
    retAfterTB refTwoPhaseBorrowRoundTrip [.scalar ⟨5, 4⟩] 10 = tbRetU32 42 := by
  decide +kernel

theorem retagRefReborrowChain_tb_direct :
    retAfterTB retagRefReborrowChain [.scalar ⟨5, 4⟩] 19 = tbRetU32 12 := by
  decide +kernel

theorem refRawTransmuteChain_tb_direct :
    retAfterTB refRawTransmuteChain [.scalar ⟨5, 4⟩] 14 = tbRetU32 15 := by
  decide +kernel

/-! #### 2. In-fragment UB agreement on `MachTB` -/

theorem uninitRefReadUb_tb_direct :
    ubAfterTB uninitRefReadUb [.scalar ⟨5, 4⟩] 3 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

theorem uninitRefReborrowUb_tb_direct :
    ubAfterTB uninitRefReborrowUb [.scalar ⟨5, 4⟩] 4 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

theorem refMutDivZeroUb_tb_direct :
    ubAfterTB refMutDivZeroUb [.scalar ⟨5, 4⟩] 8 =
      some "division by zero" := by
  decide +kernel

theorem retagUninitRefUb_tb_direct :
    ubAfterTB retagUninitRefUb [.scalar ⟨5, 4⟩] 3 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

theorem transmuteUninitRefUb_tb_direct :
    ubAfterTB transmuteUninitRefUb [.scalar ⟨5, 4⟩] 4 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-! #### 3. Raw pointers (`*const`/`*mut`) vs safe references (`&`/`&mut`) on `MachTB`

In upstream MiniRust, `PtrType::Raw` has `safe_pointee = None`, so
`ReborrowSettings::new` returns `None` and `AddrOf(..., PtrType::Raw)` leaves
the root `[]` (`Unprot Unique`) provenance unchanged instead of allocating a
child Tree Borrows node. Thus `PointerWitness.directWrite` (`&raw mut _1; _1 = 9; *p`)
and `PointerWitness.frozenWrite` (`&raw const _1; p as *mut u32; *q = 9`) both
return `9` on `MachTB` just as on `Mach` (`BasicMemory`), whereas Anneal
allocates a `BorrowEntry` on `Rvalue.rawPtr` and faults. -/

theorem directWrite_tb_direct :
    retAfterTB directWrite [.scalar ⟨5, 4⟩] 6 = tbRetU32 9 := by
  decide +kernel

theorem frozenWrite_tb_direct :
    retAfterTB frozenWrite [.scalar ⟨5, 4⟩] 8 = tbRetU32 9 := by
  decide +kernel

/-! #### 4. Out-of-fragment safe-reference & Tree Borrows 3-way witnesses on `MachTB` -/

theorem misalignedRef_tb_direct :
    ubAfterTB misalignedRef [.scalar ⟨5, 4⟩] 11 =
      some "Value::Ptr: unaligned safe pointer" := by
  decide +kernel

theorem danglingRef_tb_direct :
    ubAfterTB danglingRef [.scalar ⟨5, 4⟩] 8 =
      some "Value::Ptr: non-dereferenceable safe pointer" := by
  decide +kernel

/-- Foreign dereference write invalidates a sibling two-phase borrow in both
Anneal and `MachTB` (`"Tree Borrows: local read of Disabled reference"`),
whereas `BasicMemory` returns `99`. -/
theorem twoPhaseForeignWriteDiscrepancy_tb_direct :
    ubAfterTB twoPhaseForeignWriteDiscrepancy [.scalar ⟨5, 4⟩] 7 =
      some "Tree Borrows: local read of Disabled reference" := by
  decide +kernel

/-- End-to-end translated-MIR ground truth for the direct-write two-phase borrow
witness: `MachTB` transitions unprotected `Freeze` `Reserved` to `Disabled` on
`_1 = 99` and raises `"Tree Borrows: local read of Disabled reference"` at
`_0 = copy (*_2)`, agreeing with Anneal's UB under the `LM-3.3` `updateBorrowPerm`
(`twoPhaseDirectWriteTreeBorrowsGap_anneal_ub`: `writerTag = .none` disables the
unprotected `.reservedFrz false` entry), whereas `BasicMemory` returns `99`. -/
theorem twoPhaseDirectWriteTreeBorrowsGap_tb_direct :
    ubAfterTB twoPhaseDirectWriteTreeBorrowsGap [.scalar ⟨5, 4⟩] 5 =
      some "Tree Borrows: local read of Disabled reference" := by
  decide +kernel

/-- Read-only mutable reborrow `_3 = &mut (*_2)` from shared `_2 = &_1`:
Anneal faults eagerly at `&mut (*_2)` (a `.frozen` parent rejects `.mut`), whereas
`MachTB` creates `_3` lazily in `Reserved` (`init_access = Some(Read)`) and
returns `5` because `_3` is only read and never written. -/
theorem frozenRefMutReborrow_tb_direct :
    retAfterTB frozenRefMutReborrow [.scalar ⟨5, 4⟩] 7 = tbRetU32 5 := by
  decide +kernel

/-- Writing through `_3 = &mut (*_2)` reborrowed from shared `_2 = &_1`
(`_2 = &_1; _3 = &mut (*_2); (*_3) = 9; _0 = copy (*_3)`):
Anneal faults at `&mut (*_2)`, `BasicMemory` returns `9`, and `MachTB` faults
at `(*_3) = 9` because the write propagates as a `Local` `Write` to ancestor
`_2` (`Frozen`), raising `"Tree Borrows: local write of Frozen reference"`. -/
def frozenRefMutReborrowWrite : CapturedMir :=
  ptrBody "witness::frozen_ref_mut_reborrow_write"
    [u32Decl, u32Decl, refSharedU32Decl, refMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.ref .shared (local_ 1)),
     .assign (local_ 3) (.ref (.mut false) (derefPlace 2)),
     .assign (derefPlace 3) (.use (constU32 9)),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem frozenRefMutReborrowWrite_translate :
    (translateFn frozenRefMutReborrowWrite).isSome = true := by decide +kernel

theorem frozenRefMutReborrowWrite_notInFragment :
    inFragment frozenRefMutReborrowWrite = false := by decide +kernel

theorem frozenRefMutReborrowWrite_anneal_ub :
    ∃ tr u, Reaches (mirTree frozenRefMutReborrowWrite
      (initMachineState frozenRefMutReborrowWrite [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound frozenRefMutReborrowWrite 30 _ (by decide)

theorem frozenRefMutReborrowWrite_minirust_direct :
    retAfter frozenRefMutReborrowWrite [.scalar ⟨5, 4⟩] 8 =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

theorem frozenRefMutReborrowWrite_tb_direct :
    ubAfterTB frozenRefMutReborrowWrite [.scalar ⟨5, 4⟩] 6 =
      some "Tree Borrows: local write of Frozen reference" := by
  decide +kernel

/-- Reborrowing `&(*_2)` after `_1 = 9` disabled `_2`: both Anneal and `MachTB`
fault at the reborrow (`init_access = Some(Read)` on `Disabled` `_2`), while
`BasicMemory` returns `9`. -/
theorem disabledRefReborrow_tb_direct :
    ubAfterTB disabledRefReborrow [.scalar ⟨5, 4⟩] 6 =
      some "Tree Borrows: local read of Disabled reference" := by
  decide +kernel

/-- End-to-end translated-MIR witness for hierarchical parent preservation:
in `_2 = &mut _1; _3 = &mut (*_2); (*_3) = 9; _0 = copy (*_2)`, Anneal's flat
`List BorrowEntry` disables parent `_2` and faults, while both `BasicMemory` and
`MachTB` preserve parent `[0]` (`Reserved -> Unique`) across child `[0, 0]`'s
write and return `9`. -/
theorem childReborrowWriteDisablesParent_tb_direct :
    retAfterTB childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩] 8 = tbRetU32 9 := by
  decide +kernel

/-- Direct write `_1 = 9` after `Retag([fn entry], _2)` on `_2 = &mut _1`:
both Anneal and `MachTB` fault immediately at `_1 = 9` (`Prot::Unique` rejects
any foreign access), while `BasicMemory` returns `9`. -/
theorem retagFnEntryProtectorWrite_tb_direct :
    ubAfterTB retagFnEntryProtectorWrite [.scalar ⟨5, 4⟩] 5 =
      some "Tree Borrows: foreign read of protected Unique reference" := by
  decide +kernel

/-- Retagging parent `_2` after child write `(*_3) = 9` in
`retagDisabledRefDiscrepancy`: Anneal's flat list disabled `_2` so Anneal
faults, whereas `MachTB` kept parent `_2` `Unique` and returns `9`. -/
theorem retagDisabledRefDiscrepancy_tb_direct :
    retAfterTB retagDisabledRefDiscrepancy [.scalar ⟨5, 4⟩] 9 = tbRetU32 9 := by
  decide +kernel

/-- Retagging a reference *truly* disabled by a foreign write
(`_2 = &mut _1; _1 = 9; Retag([default], _2); _0 = copy _1`):
both Anneal and `MachTB` fault at `Retag([default], _2)` (`Statement::Validate`
performs `init_access = Some(Read)` on `Disabled` `[0]`), while `BasicMemory`
returns `9`. -/
def retagTrulyDisabledRefUb : CapturedMir :=
  ptrBody "witness::retag_truly_disabled_ref_ub"
    [u32Decl, u32Decl, refMutU32Decl]
    [.storageLive 2,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 1) (.use (constU32 9)),
     .retag .default (local_ 2),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem retagTrulyDisabledRefUb_translate :
    (translateFn retagTrulyDisabledRefUb).isSome = true := by decide +kernel

theorem retagTrulyDisabledRefUb_notInFragment :
    inFragment retagTrulyDisabledRefUb = false := by decide +kernel

theorem retagTrulyDisabledRefUb_anneal_ub :
    ∃ tr u, Reaches (mirTree retagTrulyDisabledRefUb
      (initMachineState retagTrulyDisabledRefUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound retagTrulyDisabledRefUb 20 _ (by decide)

theorem retagTrulyDisabledRefUb_minirust_direct :
    retAfter retagTrulyDisabledRefUb [.scalar ⟨5, 4⟩] 7 =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

theorem retagTrulyDisabledRefUb_tb_direct :
    ubAfterTB retagTrulyDisabledRefUb [.scalar ⟨5, 4⟩] 5 =
      some "Tree Borrows: local read of Disabled reference" := by
  decide +kernel

/-- Function-entry protector on a callee-owned local (`_2 = &_1; Retag([fn entry], _2);
_0 = copy (*_2); return`): Anneal discards the callee frame on `return` without
checking `activeProtectors` against local deallocation (returning `5`), and
`BasicMemory` has no protectors (returning `5`), whereas `MachTB`'s
`evalReturnM` runs `deallocAllM` (`StorageDead(_1)`) *before* `end_call`,
raising `"Tree Borrows: foreign write of protected Frozen reference which had a local read"`
at `Terminator::Return` (step 6). -/
def retagFnEntryLocalDeallocUb : CapturedMir :=
  ptrBody "witness::retag_fn_entry_local_dealloc_ub"
    [u32Decl, u32Decl, refSharedU32Decl]
    [.storageLive 2,
     .assign (local_ 2) (.ref .shared (local_ 1)),
     .retag .fnEntry (local_ 2),
     .assign (local_ 0) (.use (.copy (derefPlace 2)))]

theorem retagFnEntryLocalDeallocUb_translate :
    (translateFn retagFnEntryLocalDeallocUb).isSome = true := by decide +kernel

theorem retagFnEntryLocalDeallocUb_notInFragment :
    inFragment retagFnEntryLocalDeallocUb = false := by decide +kernel

theorem retagFnEntryLocalDeallocUb_anneal_ret :
    ∃ mem, ReachesRet (mirTree retagFnEntryLocalDeallocUb
      (initMachineState retagFnEntryLocalDeallocUb [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨5, 4⟩, mem)) :=
  ⟨_, runA_sound retagFnEntryLocalDeallocUb 20 _ _ _ rfl⟩

theorem retagFnEntryLocalDeallocUb_minirust_direct :
    retAfter retagFnEntryLocalDeallocUb [.scalar ⟨5, 4⟩] 6 =
      some (some { retAlloc with data := scalarBytes u32 5 }, [1]) := by
  decide +kernel

theorem retagFnEntryLocalDeallocUb_tb_direct :
    ubAfterTB retagFnEntryLocalDeallocUb [.scalar ⟨5, 4⟩] 6 =
      some "Tree Borrows: foreign write of protected Frozen reference which had a local read" := by
  decide +kernel

theorem retagScalarDiscrepancy_tb_direct :
    retAfterTB retagScalarDiscrepancy [.scalar ⟨5, 4⟩] 4 = tbRetU32 5 := by
  decide +kernel

theorem transmuteSharedRefToMutWriteDiscrepancy_tb_direct :
    ubAfterTB transmuteSharedRefToMutWriteDiscrepancy [.scalar ⟨5, 4⟩] 6 =
      some "Tree Borrows: local write of Frozen reference" := by
  decide +kernel

theorem transmuteDanglingIntToRefDiscrepancy_tb_direct :
    ubAfterTB transmuteDanglingIntToRefDiscrepancy [.scalar ⟨5, 4⟩] 5 =
      some "Value::Ptr: non-dereferenceable safe pointer" := by
  decide +kernel

/-! #### 5. Three-way lockstep UB agreement on divergences resolved by the places-ptr `Trusted` semantics

Before the places-ptr `Trusted` semantics, Anneal *returned* `5` on `misaligned`,
`misalignedRef`, and `transmuteDanglingIntToRefDiscrepancy` while both MiniRust
machines raised UB. Anneal now faults at the same statement, so these witnesses
are positive lockstep agreements across Anneal, `BasicMemory` (`Mach`), and Tree
Borrows (`MachTB`). -/

/-- `misaligned`: loading a `u32` through a pointer one byte into a `u32` is UB
in Anneal (`checkTargetPlaceAlign`), `Mach`, and `MachTB`. -/
theorem misaligned_three_way_ub_agreement :
    (∃ tr u, Reaches (mirTree misaligned (initMachineState misaligned [.scalar ⟨5, 4⟩])) tr u ∧
      FaultNow u) ∧
    ubAfter misaligned [.scalar ⟨5, 4⟩] 10 =
      some "loading from a place based on a misaligned pointer" ∧
    ubAfterTB misaligned [.scalar ⟨5, 4⟩] 10 =
      some "loading from a place based on a misaligned pointer" :=
  ⟨misaligned_anneal_ub, misaligned_minirust_direct, by decide +kernel⟩

/-- `misalignedRef`: forming `&*q` from a misaligned `*const u32` is UB in Anneal
(`resolveRefDerefTarget?`), `Mach`, and `MachTB`
(`"Value::Ptr: unaligned safe pointer"`). -/
theorem misalignedRef_three_way_ub_agreement :
    (∃ tr u, Reaches (mirTree misalignedRef (initMachineState misalignedRef [.scalar ⟨5, 4⟩]))
      tr u ∧ FaultNow u) ∧
    ubAfter misalignedRef [.scalar ⟨5, 4⟩] 11 = some "Value::Ptr: unaligned safe pointer" ∧
    ubAfterTB misalignedRef [.scalar ⟨5, 4⟩] 11 = some "Value::Ptr: unaligned safe pointer" :=
  ⟨misalignedRef_anneal_ub, misalignedRef_minirust_direct, misalignedRef_tb_direct⟩

/-- `transmuteDanglingIntToRefDiscrepancy`: transmuting `4_usize` to `&u32` is UB
in Anneal (the safe-reference image has no intact provenance), `Mach`, and
`MachTB` (`"Value::Ptr: non-dereferenceable safe pointer"`); the witness name
records the former discrepancy. -/
theorem transmuteDanglingIntToRefDiscrepancy_three_way_ub_agreement :
    (∃ tr u, Reaches (mirTree transmuteDanglingIntToRefDiscrepancy
      (initMachineState transmuteDanglingIntToRefDiscrepancy [.scalar ⟨5, 4⟩])) tr u ∧
      FaultNow u) ∧
    ubAfter transmuteDanglingIntToRefDiscrepancy [.scalar ⟨5, 4⟩] 5 =
      some "Value::Ptr: non-dereferenceable safe pointer" ∧
    ubAfterTB transmuteDanglingIntToRefDiscrepancy [.scalar ⟨5, 4⟩] 5 =
      some "Value::Ptr: non-dereferenceable safe pointer" :=
  ⟨transmuteDanglingIntToRefDiscrepancy_anneal_ub,
    transmuteDanglingIntToRefDiscrepancy_minirust_ub,
    transmuteDanglingIntToRefDiscrepancy_tb_direct⟩

/-! #### 6. RFC 2582 `&raw` place addressing: three-way normal-return agreement

The places-ptr `Trusted` semantics evaluates `Rvalue.rawPtr` by computing the
place address alone: it neither reads the value stored at the place nor checks
the place's alignment, matching MiniRust's `AddrOf(_, PtrType::Raw)` (and Tree
Borrows, where a raw `AddrOf` performs no retag). Both witnesses lie outside the
proved fragment (a misaligned pointer, resp. an address-taken non-argument
local), so these are executable three-way agreements rather than instances of
the simulation theorems. -/

/-- `misalignedRef` with the safe reborrow `&(*_5)` replaced by the raw borrow
`&raw const (*_5)` of the same misaligned `*const u32`: no UB on any machine,
all three return `5`. Together with `misalignedRef_three_way_ub_agreement` this
pins the RFC 2582 distinction: alignment is checked for safe references, never
for raw place addressing. -/
def misalignedRaw : CapturedMir :=
  ptrBody "witness::misaligned_raw"
    [u32Decl, u32Decl, ptrConstU32Decl, ptrConstU8Decl, ptrConstU8Decl,
     ptrConstU32Decl, ptrConstU32Decl]
    [.storageLive 2, .assign (local_ 2) (.rawPtr .not (local_ 1)),
     .storageLive 3, .assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) ptrConstU8Ty),
     .storageLive 4, .assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (constUsize 1)),
     .storageLive 5, .assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) ptrConstU32Ty),
     .storageLive 6, .assign (local_ 6) (.rawPtr .not (derefPlace 5)),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem misalignedRaw_translate : (translateFn misalignedRaw).isSome = true := by decide +kernel

theorem misalignedRaw_notInFragment : inFragment misalignedRaw = false := by decide +kernel

theorem misalignedRaw_anneal_ret :
    ∃ mem, ReachesRet (mirTree misalignedRaw (initMachineState misalignedRaw [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨5, 4⟩, mem)) :=
  ⟨_, runA_sound misalignedRaw 30 _ _ _ rfl⟩

theorem misalignedRaw_three_way_agreement :
    (∃ mem, ReachesRet (mirTree misalignedRaw (initMachineState misalignedRaw [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨5, 4⟩, mem))) ∧
    retAfter misalignedRaw [.scalar ⟨5, 4⟩] 13 =
      some (some { retAlloc with data := scalarBytes u32 5 }, [1]) ∧
    retAfterTB misalignedRaw [.scalar ⟨5, 4⟩] 13 = tbRetU32 5 :=
  ⟨misalignedRaw_anneal_ret, by decide +kernel, by decide +kernel⟩

/-- `&raw mut` of a storage-live but *uninitialized* local
(`_3 = &raw mut _2; *_3 = 7; _0 = Add(copy _2, copy _1)`): taking the raw
address never reads `_2`, the write through `_3` initializes it, and all three
machines return `12`. -/
def rawAddrOfUninit : CapturedMir :=
  ptrBody "witness::raw_addr_of_uninit"
    [u32Decl, u32Decl, u32Decl, ptrMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 3) (.rawPtr .mut (local_ 2)),
     .assign (derefPlace 3) (.use (constU32 7)),
     .assign (local_ 0) (.binaryOp .add (.copy (local_ 2)) (.copy (local_ 1)))]

theorem rawAddrOfUninit_translate : (translateFn rawAddrOfUninit).isSome = true := by
  decide +kernel

theorem rawAddrOfUninit_notInFragment : inFragment rawAddrOfUninit = false := by decide +kernel

theorem rawAddrOfUninit_anneal_ret :
    ∃ mem, ReachesRet (mirTree rawAddrOfUninit
      (initMachineState rawAddrOfUninit [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨12, 4⟩, mem)) :=
  ⟨_, runA_sound rawAddrOfUninit 30 _ _ _ rfl⟩

theorem rawAddrOfUninit_three_way_agreement :
    (∃ mem, ReachesRet (mirTree rawAddrOfUninit
      (initMachineState rawAddrOfUninit [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨12, 4⟩, mem))) ∧
    retAfter rawAddrOfUninit [.scalar ⟨5, 4⟩] 7 =
      some (some { retAlloc with data := scalarBytes u32 12 }, [1]) ∧
    retAfterTB rawAddrOfUninit [.scalar ⟨5, 4⟩] 7 = tbRetU32 12 :=
  ⟨rawAddrOfUninit_anneal_ret, by decide +kernel, by decide +kernel⟩

/-! #### 7. Provenance-faithful scalar-to-pointer transmute byte decoding (`decodeScalarBytes`)

Unlike `transmuteDanglingIntToRefDiscrepancy` (where transmuting `4_usize` to a
safe reference `&u32` immediately faults because `decodeValueFromBytes` checks
`isRef = true` dereferenceability and intact provenance, matching MiniRust's
`Value::check` on `PtrType::Ref`), transmuting the same `4_usize` to a raw
pointer `*const u32` without dereferencing takes the `isRef = false` branch of
`decodeValueFromBytes`, decoding the provenance-less byte sequence via
`decodeScalarBytes` into a provenance-less scalar on Anneal just as MiniRust
decodes `Value::Ptr { addr: 4, provenance: None }` under `PtrType::Raw`
(`safe_pointee = None`). (Dereferencing such a transmuted raw pointer — even
when its address matches a previously exposed live local — faults across all
three semantics; see `transmuteExposedAddrToRawPtrDerefUb_three_way` in
`ProvenanceWitness.lean`.) -/

/-- Transmuting `4_usize` to `*const u32` without dereferencing
(`_2 = 4_usize; _3 = copy _2 as *const u32 (Transmute); _0 = copy _1`):
succeeds across Anneal, `Mach`, and `MachTB` and returns `5`, contrasting
one-for-one with `transmuteDanglingIntToRefDiscrepancy_three_way_ub_agreement`. -/
def transmuteDanglingIntToRawPtrNoDerefOk : CapturedMir :=
  ptrBody "witness::transmute_dangling_int_to_raw_ptr_no_deref_ok"
    [u32Decl, u32Decl, usizeDecl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.use (constUsize 4)),
     .assign (local_ 3) (.cast .transmute (.copy (local_ 2)) ptrConstU32Ty),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem transmuteDanglingIntToRawPtrNoDerefOk_translate :
    (translateFn transmuteDanglingIntToRawPtrNoDerefOk).isSome = true := by decide +kernel

theorem transmuteDanglingIntToRawPtrNoDerefOk_notInFragment :
    inFragment transmuteDanglingIntToRawPtrNoDerefOk = false := by decide +kernel

theorem transmuteDanglingIntToRawPtrNoDerefOk_anneal_ret :
    ∃ mem, ReachesRet (mirTree transmuteDanglingIntToRawPtrNoDerefOk
      (initMachineState transmuteDanglingIntToRawPtrNoDerefOk [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨5, 4⟩, mem)) :=
  ⟨_, runA_sound transmuteDanglingIntToRawPtrNoDerefOk 20 _ _ _ rfl⟩

theorem transmuteDanglingIntToRawPtrNoDerefOk_three_way_agreement :
    (∃ mem, ReachesRet (mirTree transmuteDanglingIntToRawPtrNoDerefOk
      (initMachineState transmuteDanglingIntToRawPtrNoDerefOk [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨5, 4⟩, mem))) ∧
    retAfter transmuteDanglingIntToRawPtrNoDerefOk [.scalar ⟨5, 4⟩] 7 =
      some (some { retAlloc with data := scalarBytes u32 5 }, [1]) ∧
    retAfterTB transmuteDanglingIntToRawPtrNoDerefOk [.scalar ⟨5, 4⟩] 7 = tbRetU32 5 :=
  ⟨transmuteDanglingIntToRawPtrNoDerefOk_anneal_ret, by decide +kernel, by decide +kernel⟩

/-- Reference-typed `Retag([raw], _2)` and `Retag([raw], _3)` (`_2 : &mut u32`,
`_3 : &u32`): exercises `statementOk` / `evalStmt_retag_ref_local` / `Simulation`
on `.retag .raw` applied to reference locals (`retagPerm .raw (.ref ..)` matches
`.default`/`.twoPhase`, allocating child tags `2` and `4` in Anneal while MiniRust
lowers both to `Validate(_, false)`), returning `5 + 7 = 12` across Anneal, `Mach`,
and `MachTB`. -/
def retagRawOnRefLocal : CapturedMir :=
  ptrBody "witness::retag_raw_on_ref_local"
    [u32Decl, u32Decl, refMutU32Decl, refSharedU32Decl, u32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .retag .raw (local_ 2),
     .assign (local_ 4) (.copyForDeref (derefPlace 2)),
     .assign (derefPlace 2) (.binaryOp .add (.copy (local_ 4)) (constU32 7)),
     .assign (local_ 3) (.ref .shared (derefPlace 2)),
     .retag .raw (local_ 3),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem retagRawOnRefLocal_inFragment : inFragment retagRawOnRefLocal = true := by decide

def retagRawOnRefLocalFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, refTy .not u32),
    (localName 4, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Validate (.Local (localName 2)) false,
      .Assign (.Local (localName 4)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 4))) (.Constant (.Int 7) (.Int u32))),
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .not u32)),
      .Validate (.Local (localName 3)) false,
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem retagRawOnRefLocal_translate :
    translateFn retagRawOnRefLocal = some retagRawOnRefLocalFn := rfl

def retagRawOnRefLocalS0 : MachineState :=
  initMachineState retagRawOnRefLocal [.scalar ⟨5, 4⟩]
def retagRawOnRefLocalMInit : Mach :=
  machine retagRawOnRefLocal retagRawOnRefLocalFn
    retagRawOnRefLocalS0.frame.locals retagRawOnRefLocalFn.start

theorem retagRawOnRefLocal_anneal_ret :
    ReachesRet (mirTree retagRawOnRefLocal retagRawOnRefLocalS0) []
      (.normal (.scalar ⟨12, 4⟩,
        { retagRawOnRefLocalS0.memory with
          borrows := [{ rawPtrEntry 4 .not (local_ 1) with parentTag := some 3 },
                      { rawPtrEntry 3 .not (local_ 1) with parentTag := some 2 },
                      { rawPtrEntry 2 .mut (local_ 1) with parentTag := some 1 },
                      rawPtrEntry 1 .mut (local_ 1)],
          nextTag := 5 })) :=
  runA_sound retagRawOnRefLocal 30 _ _ _ rfl

theorem retagRawOnRefLocal_noUB :
    MirNoUBTree (mirCallTree retagRawOnRefLocal [.scalar ⟨5, 4⟩]) :=
  runA_noUB retagRawOnRefLocal 30 _ _ _ rfl

theorem retagRawOnRefLocal_minirust_direct :
    retAfter retagRawOnRefLocal [.scalar ⟨5, 4⟩] 12 =
      some (some { retAlloc with data := scalarBytes u32 12 }, [1]) := by
  decide +kernel

theorem retagRawOnRefLocal_tb_direct :
    retAfterTB retagRawOnRefLocal [.scalar ⟨5, 4⟩] 12 = tbRetU32 12 := by
  decide +kernel

theorem retagRawOnRefLocal_ctxOk : CtxOk retagRawOnRefLocal ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : retagRawOnRefLocal.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [retagRawOnRefLocal, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [retagRawOnRefLocal, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : retagRawOnRefLocal.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [retagRawOnRefLocal, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem retagRawOnRefLocal_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n retagRawOnRefLocalMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 12 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret retagRawOnRefLocal_inFragment retagRawOnRefLocal_translate ctx0
      retagRawOnRefLocal_ctxOk [.scalar ⟨5, 4⟩] (by decide) retagRawOnRefLocalMInit
      rfl rfl rfl retagRawOnRefLocal_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [retagRawOnRefLocal, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem retagRawOnRefLocal_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n retagRawOnRefLocalMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k retagRawOnRefLocalMInit = .ok mRet ∧
      ReturnRel retagRawOnRefLocal ctx0 s' v mRet ∧
      ReachesRet (mirCallTree retagRawOnRefLocal [.scalar ⟨5, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB retagRawOnRefLocal_inFragment retagRawOnRefLocal_translate ctx0
    retagRawOnRefLocal_ctxOk [.scalar ⟨5, 4⟩] (by decide) retagRawOnRefLocalMInit
    rfl rfl rfl retagRawOnRefLocal_noUB herr

theorem retagRawOnRefLocal_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) retagRawOnRefLocalMInit = .ok m' ∧
      StateRelN retagRawOnRefLocal retagRawOnRefLocalFn ctx0 s' m' ∧
      Reaches (mirCallTree retagRawOnRefLocal [.scalar ⟨5, 4⟩]) tr
        (mirTree retagRawOnRefLocal s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k retagRawOnRefLocalMInit = .ok mRet ∧
      ReturnRel retagRawOnRefLocal ctx0 s' v mRet ∧
      ReachesRet (mirCallTree retagRawOnRefLocal [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N retagRawOnRefLocal_inFragment retagRawOnRefLocal_translate ctx0
    retagRawOnRefLocal_ctxOk [.scalar ⟨5, 4⟩] (by decide) retagRawOnRefLocalMInit
    rfl rfl rfl retagRawOnRefLocal_noUB n

end MiniRustSpec.Correspondence.RefWitness
