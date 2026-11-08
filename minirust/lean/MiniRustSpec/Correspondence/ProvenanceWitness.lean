/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.TbWitness
import MiniRustSpec.Correspondence.Provenance

/-!
# Provenance-cast 3-way witnesses and fragment counterexamples (MR-3.3)

Concrete MIR bodies run on Anneal's MIR semantics (`runA_sound`,
`faultsA_sound`), on MiniRust `Machine<BasicMemory<x86_64>>` (`Mach`), and on
MiniRust `Machine<TreeBorrowsMemory<x86_64>>` (`MachTB`), all three through
`translateFnWithIntrinsics`:

1. **Why the provenance-cast fragment needs `provCastFlowOk` and the alias view**
   (`inFragmentWithIntrinsicsA1`, the extended fragment exactly as Pass A1
   defined it). That predicate admitted
   * `exposeTwice` — Anneal returns `65536`, both MiniRust machines `0`
     (`exposeTwice_three_way_divergence`): Anneal's `tag * 65536` encoding of an
     exposed address is observable;
   * `int2ptrForgedTag` — Anneal *returns `5`* while both MiniRust machines
     raise `"dereferencing pointer without provenance"`
     (`int2ptrForgedTag_three_way_divergence`): Anneal decodes any integer into a
     borrow tag, so it is more defined than MiniRust and a forged
     `PointerWithExposedProvenance` operand is unsound to admit;
   * `directWrite` — Anneal UB, `Mach` returns `9`: the `ptrAliasingOk`
     discipline of `inFragment` had been dropped;
   * `exposeSharedRefWriteUb` — Anneal UB, `Mach` returns `88`: `*const u32 →
     usize → *mut u32` launders mutability past `ptrRvalueOk`'s `PtrToPtr` rule.

   The corrected `inFragmentWithIntrinsics` rejects all four
   (`*_notInFragmentWithIntrinsics`) while keeping the agreeing round trips.
2. **The brief's witness suite**, each across all three semantics:
   `int2ptrRoundTripOk_three_way` (in the fragment, `77` everywhere),
   `int2ptrUnexposedUb_three_way` (UB everywhere; outside the fragment because
   its address is forged), `int2ptrAmbiguityUnsupported_three_way` (in the
   fragment: Anneal returns `9`, both MiniRust machines stop with
   `Stop.unsupported` because two adjacent exposed arguments meet at the
   address — the same body returns `9` on both machines when the arguments are
   not adjacent), and `int2ptrDeadAllocUb_three_way` (the cast happens *after*
   `StorageDead`: UB everywhere, `"dereferencing pointer to dead allocation"` on
   both MiniRust machines).
3. **Pass A1's `ProvenanceRel` is not an invariant of A1's fragment**
   (`int2ptrDeadAllocDerefUb_provenanceRel_fails`): after `StorageDead(_2)` in
   `int2ptrDeadAllocDerefUb` (admitted by `inFragmentWithIntrinsicsA1`), the
   exposed provenance's allocation is dead, so no `ProvenanceRel` (which demands
   live exposed allocations) holds; under the corrected fragment the body is
   rejected (`ptrAliasingOk` only lets parameters, which are never deallocated,
   be borrowed).
4. **Out-of-fragment angelic boundary**: `int2ptrAfterStorageDeadTwoExposed`
   stops with `Stop.unsupported` on both MiniRust machines although every
   admissible provenance leads to UB, documenting where the committed
   resolution is incomplete (never unsound).
-/

namespace MiniRustSpec.Correspondence.ProvenanceWitness

set_option Elab.async false

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
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness

/-! ## 1. Pass A1's extended fragment and its counterexamples -/

/-- The extended fragment exactly as Pass A1 defined `inFragmentWithIntrinsics`
(no provenance-cast data flow, no `ptrAliasingOk`), kept to record which
diverging bodies it admitted. -/
def inFragmentWithIntrinsicsA1 (body : CapturedMir) : Bool :=
  body.isRuntimePostCleanup &&
  decide (body.argCount + 1 ≤ body.localDecls.length) &&
  decide (body.localDecls.length < 2 ^ 31) &&
  (body.localDecls[0]? >>= (scalarTypeOf ·.ty)).isSome &&
  body.localDecls.all (localDeclOk body.layouts) &&
  ((body.localDecls.drop 1).take body.argCount).all (fun d => !isPtrTy d.ty) &&
  (body.localDecls.drop (body.argCount + 1)).all
    (fun d => (scalarTypeOf d.ty).isSome || isPtrTy d.ty) &&
  decide (body.basicBlocks ≠ []) &&
  body.basicBlocks.all (fun bb =>
    !bb.isCleanup &&
    bb.statements.all (statementOkWithIntrinsics body.localDecls · body.layouts) &&
    terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator) &&
  storageDeadOk body && movesOk body && mentionsOk body &&
  (translateFnWithIntrinsics body).isSome

/-- The corrected fragment refines Pass A1's. -/
theorem inFragmentWithIntrinsics_imp_A1 {body : CapturedMir}
    (h : inFragmentWithIntrinsics body = true) : inFragmentWithIntrinsicsA1 body = true := by
  simp only [inFragmentWithIntrinsics, inFragmentWithIntrinsicsA1, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨hcore, _⟩, _⟩, htr⟩ := h
  exact ⟨hcore, htr⟩

/-! ### `exposeTwice`: an observed exposed address -/

theorem exposeTwice_inFragmentWithIntrinsicsA1 :
    inFragmentWithIntrinsicsA1 exposeTwice = true := by decide +kernel

theorem exposeTwice_provCastFlowOk_false : provCastFlowOk exposeTwice = false := by
  decide +kernel

theorem exposeTwice_notInFragmentWithIntrinsics :
    inFragmentWithIntrinsics exposeTwice = false := by decide +kernel

theorem exposeTwice_intr_minirust_direct :
    retAfterIntr exposeTwice [.scalar ⟨5, 4⟩] 13 =
      some (some { retAlloc with data := scalarBytes u32 0 }, [1]) := by
  decide +kernel

theorem exposeTwice_intr_tb_direct :
    retAfterIntrTB exposeTwice [.scalar ⟨5, 4⟩] 13 = tbRetU32 0 := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- Anneal returns `65536` (the two borrow tags `1` and `2` encoded as
`tag * 65536`), both MiniRust machines return `0` (one address). -/
theorem exposeTwice_three_way_divergence :
    (∃ mem, ReachesRet (mirTree exposeTwice (initMachineState exposeTwice [.scalar ⟨5, 4⟩])) []
        (.normal (.scalar ⟨65536, 4⟩, mem))) ∧
      retAfterIntr exposeTwice [.scalar ⟨5, 4⟩] 13 =
        some (some { retAlloc with data := scalarBytes u32 0 }, [1]) ∧
      retAfterIntrTB exposeTwice [.scalar ⟨5, 4⟩] 13 = tbRetU32 0 :=
  ⟨⟨_, exposeTwice_anneal_ret⟩, exposeTwice_intr_minirust_direct, exposeTwice_intr_tb_direct⟩

/-! ### `int2ptrForgedTag`: Anneal resurrects provenance from a forged integer -/

/-- MIR of
```rust
fn int2ptr_forged_tag(x: u32) -> u32 {
    let _p = &raw const x;                                   // borrow tag 1
    let q = std::ptr::with_exposed_provenance::<u32>(65536); // 1 * 65536
    unsafe { *q }
}
```
Nothing is exposed, yet Anneal decodes `65536` into borrow tag `1` (the
borrow of `x`) and reads `x`. -/
def int2ptrForgedTag : CapturedMir :=
  ptrBody "witness::int2ptr_forged_tag"
    [u32Decl, u32Decl, ptrConstU32Decl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.rawPtr .not (local_ 1)),
     .assign (local_ 3) (.cast .pointerWithExposedProvenance (constUsize 65536) ptrConstU32Ty),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem int2ptrForgedTag_inFragmentWithIntrinsicsA1 :
    inFragmentWithIntrinsicsA1 int2ptrForgedTag = true := by decide +kernel

theorem int2ptrForgedTag_notInFragmentWithIntrinsics :
    inFragmentWithIntrinsics int2ptrForgedTag = false := by decide +kernel

set_option maxRecDepth 200000 in
theorem int2ptrForgedTag_anneal_ret :
    ∃ mem, ReachesRet (mirTree int2ptrForgedTag
      (initMachineState int2ptrForgedTag [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨5, 4⟩, mem)) :=
  ⟨_, runA_sound int2ptrForgedTag 30 _ _ _ rfl⟩

theorem int2ptrForgedTag_minirust_direct :
    stopAfterIntr int2ptrForgedTag [.scalar ⟨5, 4⟩] 6 =
      some (.ub "dereferencing pointer without provenance") := by
  decide +kernel

theorem int2ptrForgedTag_tb_direct :
    stopAfterIntrTB int2ptrForgedTag [.scalar ⟨5, 4⟩] 6 =
      some (.ub "dereferencing pointer without provenance") := by
  decide +kernel

/-- **Anneal is more defined than MiniRust** on a body Pass A1's fragment
admitted: Anneal returns `5`, both MiniRust machines raise UB. -/
theorem int2ptrForgedTag_three_way_divergence :
    inFragmentWithIntrinsicsA1 int2ptrForgedTag = true ∧
      (∃ mem, ReachesRet (mirTree int2ptrForgedTag
        (initMachineState int2ptrForgedTag [.scalar ⟨5, 4⟩])) []
        (.normal (.scalar ⟨5, 4⟩, mem))) ∧
      stopAfterIntr int2ptrForgedTag [.scalar ⟨5, 4⟩] 6 =
        some (.ub "dereferencing pointer without provenance") ∧
      stopAfterIntrTB int2ptrForgedTag [.scalar ⟨5, 4⟩] 6 =
        some (.ub "dereferencing pointer without provenance") :=
  ⟨int2ptrForgedTag_inFragmentWithIntrinsicsA1, int2ptrForgedTag_anneal_ret,
    int2ptrForgedTag_minirust_direct, int2ptrForgedTag_tb_direct⟩

/-! ### `directWrite` and `exposeSharedRefWriteUb`: dropped borrow discipline -/

theorem directWrite_inFragmentWithIntrinsicsA1 :
    inFragmentWithIntrinsicsA1 directWrite = true := by decide +kernel

theorem directWrite_notInFragmentWithIntrinsics :
    inFragmentWithIntrinsics directWrite = false := by decide +kernel

/-- Pass A1's fragment admitted `directWrite`, on which Anneal raises UB and
`Mach` returns `9`. -/
theorem directWrite_A1_divergence :
    inFragmentWithIntrinsicsA1 directWrite = true ∧
      (∃ tr u, Reaches (mirTree directWrite (initMachineState directWrite [.scalar ⟨5, 4⟩])) tr u ∧
        FaultNow u) ∧
      retAfter directWrite [.scalar ⟨5, 4⟩] 6 =
        some (some { retAlloc with data := scalarBytes u32 9 }, [1]) :=
  ⟨directWrite_inFragmentWithIntrinsicsA1, directWrite_anneal_ub, directWrite_minirust_direct⟩

theorem exposeSharedRefWriteUb_inFragmentWithIntrinsicsA1 :
    inFragmentWithIntrinsicsA1 exposeSharedRefWriteUb = true := by decide +kernel

/-- Pass A1's fragment admitted `exposeSharedRefWriteUb`, on which Anneal raises
UB and `Mach` returns `88`. -/
theorem exposeSharedRefWriteUb_A1_divergence :
    inFragmentWithIntrinsicsA1 exposeSharedRefWriteUb = true ∧
      inFragmentWithIntrinsics exposeSharedRefWriteUb = false ∧
      (∃ tr u, Reaches (mirTree exposeSharedRefWriteUb
        (initMachineState exposeSharedRefWriteUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
      retAfterIntr exposeSharedRefWriteUb [.scalar ⟨5, 4⟩] 12 =
        some (some { retAlloc with data := scalarBytes u32 88 }, [1]) :=
  ⟨exposeSharedRefWriteUb_inFragmentWithIntrinsicsA1,
    exposeSharedRefWriteUb_notInFragmentWithIntrinsics,
    exposeSharedRefWriteUb_anneal_ub, exposeSharedRefWriteUb_minirust_direct⟩

/-! ## 2. The brief's witness suite -/

/-! ### `int2ptrRoundTripOk` -/

set_option maxRecDepth 200000 in
theorem int2ptrRawRoundTripOk_anneal_ret :
    ∃ mem, ReachesRet (mirTree int2ptrRawRoundTripOk
      (initMachineState int2ptrRawRoundTripOk [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨77, 4⟩, mem)) :=
  ⟨_, runA_sound int2ptrRawRoundTripOk 30 _ _ _ rfl⟩

/-- `_2 = &raw mut _1; _3 = expose(_2); _4 = with_exposed(_3); *_4 = 77; *_4`
lies in the corrected fragment and returns `77` on Anneal, `Mach`, and `MachTB`. -/
theorem int2ptrRoundTripOk_three_way :
    inFragmentWithIntrinsics int2ptrRawRoundTripOk = true ∧
      (∃ mem, ReachesRet (mirTree int2ptrRawRoundTripOk
        (initMachineState int2ptrRawRoundTripOk [.scalar ⟨5, 4⟩])) []
        (.normal (.scalar ⟨77, 4⟩, mem))) ∧
      retAfterIntr int2ptrRawRoundTripOk [.scalar ⟨5, 4⟩] 10 =
        some (some { retAlloc with data := scalarBytes u32 77 }, [1]) ∧
      retAfterIntrTB int2ptrRawRoundTripOk [.scalar ⟨5, 4⟩] 10 = tbRetU32 77 :=
  ⟨int2ptrRawRoundTripOk_inFragmentWithIntrinsics, int2ptrRawRoundTripOk_anneal_ret,
    int2ptrRawRoundTripOk_minirust_direct, int2ptrRawRoundTripOk_tb_direct⟩

/-! ### `int2ptrUnexposedUb` -/

theorem int2ptrUnexposedDerefUb_anneal_ub :
    ∃ tr u, Reaches (mirTree int2ptrUnexposedDerefUb
      (initMachineState int2ptrUnexposedDerefUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound int2ptrUnexposedDerefUb 30 _ (by decide)

/-- With nothing exposed, `with_exposed_provenance(256)` predicts `None`
(`int2ptrProvenance_eq_none_iff`, the only admissible choice), so the read is UB
on both MiniRust machines; Anneal faults too (`256 / 65536 = 0` names no
borrow). The address is forged, so the body is outside the fragment. -/
theorem int2ptrUnexposedUb_three_way :
    inFragmentWithIntrinsics int2ptrUnexposedDerefUb = false ∧
      (∃ tr u, Reaches (mirTree int2ptrUnexposedDerefUb
        (initMachineState int2ptrUnexposedDerefUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
      stopAfterIntr int2ptrUnexposedDerefUb [.scalar ⟨5, 4⟩] 6 =
        some (.ub "dereferencing pointer without provenance") ∧
      stopAfterIntrTB int2ptrUnexposedDerefUb [.scalar ⟨5, 4⟩] 6 =
        some (.ub "dereferencing pointer without provenance") :=
  ⟨int2ptrUnexposedDerefUb_notInFragmentWithIntrinsics, int2ptrUnexposedDerefUb_anneal_ub,
    int2ptrUnexposedDerefUb_minirust_direct, int2ptrUnexposedDerefUb_tb_direct⟩

/-! ### `int2ptrAmbiguityUnsupported` -/

/-- Caller context placing two `u32` arguments at adjacent addresses: `_1` at
`[256, 260)` and `_2` at `[260, 264)` (a valid resolution of
`BasicMemory::allocate`'s address choice: aligned, positive, non-overlapping,
distinct). -/
def ctxAdj : Ctx := { ctx0 with addrs := [128, 256, 260] }

/-- MIR of
```rust
fn int2ptr_adjacent_args_ambiguous(x: u32, y: u32) -> u32 {
    let px = &raw const x;                                  // _3
    let py = &raw const y;                                  // _4
    let _ex = px.expose_provenance();                       // _5
    let ey = py.expose_provenance();                        // _6
    let q = std::ptr::with_exposed_provenance::<u32>(ey);   // _7
    unsafe { *q }
}
```
-/
def int2ptrAdjacentArgsAmbiguous : CapturedMir where
  defPath := "witness::int2ptr_adjacent_args_ambiguous"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32Decl, ptrConstU32Decl, ptrConstU32Decl, usizeDecl, usizeDecl,
    ptrConstU32Decl]
  basicBlocks := [{
    statements := ([
      .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6, .storageLive 7,
      .assign (local_ 3) (.rawPtr .not (local_ 1)),
      .assign (local_ 4) (.rawPtr .not (local_ 2)),
      .assign (local_ 5) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy),
      .assign (local_ 6) (.cast .pointerExposeProvenance (.copy (local_ 4)) usizeTy),
      .assign (local_ 7) (.cast .pointerWithExposedProvenance (.copy (local_ 6)) ptrConstU32Ty),
      .assign (local_ 0) (.use (.copy (derefPlace 7)))
    ] : List StatementKind).map mkStmt
    terminator := mkTerm .return_
    isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

/-- Start `Mach` under caller context `ctx` via `translateFnWithIntrinsics`. -/
def startMachineIntrCtx (ctx : Ctx) (body : CapturedMir) (args : List Value) : Option Mach :=
  (translateFnWithIntrinsics body).map
    (fun f => machineWithCtx ctx body f (initMachineState body args).frame.locals f.start)

/-- Stop reason after `n` `Mach` steps under caller context `ctx`. -/
def stopAfterIntrCtx (ctx : Ctx) (body : CapturedMir) (args : List Value) (n : Nat) :
    Option Stop :=
  (startMachineIntrCtx ctx body args).bind fun m =>
    match Interp.steps n m with
    | .error e => some e
    | .ok _ => none

/-- Stop reason after `n` `MachTB` steps under caller context `ctx`. -/
def stopAfterIntrCtxTB (ctx : Ctx) (body : CapturedMir) (args : List Value) (n : Nat) :
    Option Stop :=
  (startMachineIntrCtx ctx body args).bind fun m =>
    match Interp.stepsTB n (liftMachToTB m) with
    | .error e => some e
    | .ok _ => none

/-- Caller return place and stack depths after `n` `Mach` steps under `ctx`. -/
def retAfterIntrCtx (ctx : Ctx) (body : CapturedMir) (args : List Value) (n : Nat) :
    Option (Option Gen.Allocation × List Nat) :=
  (startMachineIntrCtx ctx body args).bind fun m =>
    (Interp.steps n m).toOption.map
      (fun m' => (m'.mem.memory.allocations[0]?, m'.threads.map (·.stack.length)))

/-- Caller return snapshot after `n` `MachTB` steps under `ctx`. -/
def retAfterIntrCtxTB (ctx : Ctx) (body : CapturedMir) (args : List Value) (n : Nat) :
    Option TBRetOutcome :=
  (startMachineIntrCtx ctx body args).bind fun m =>
    (Interp.stepsTB n (liftMachToTB m)).toOption.map
      (fun m' =>
        { retAlloc := m'.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
          stackDepths := m'.threads.map (·.stack.length) })

theorem int2ptrAdjacentArgsAmbiguous_inFragmentWithIntrinsics :
    inFragmentWithIntrinsics int2ptrAdjacentArgsAmbiguous = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem int2ptrAdjacentArgsAmbiguous_anneal_ret :
    ∃ mem, ReachesRet (mirTree int2ptrAdjacentArgsAmbiguous
      (initMachineState int2ptrAdjacentArgsAmbiguous [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩])) []
      (.normal (.scalar ⟨9, 4⟩, mem)) :=
  ⟨_, runA_sound int2ptrAdjacentArgsAmbiguous 40 _ _ _ rfl⟩

theorem int2ptrAdjacentArgsAmbiguous_minirust_direct :
    stopAfterIntrCtx ctxAdj int2ptrAdjacentArgsAmbiguous [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩] 11 =
      some (.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)") := by
  decide +kernel

theorem int2ptrAdjacentArgsAmbiguous_tb_direct :
    stopAfterIntrCtxTB ctxAdj int2ptrAdjacentArgsAmbiguous [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩] 11 =
      some (.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)") := by
  decide +kernel

/-- With the arguments `128` bytes apart (`ctx0_2`), the same body returns `9` on
both MiniRust machines: the ambiguity is exactly the shared boundary `260`
(`int2ptrCandidates_two_boundary`, `int2ptrProvenance_boundary_unsupported`). -/
theorem int2ptrAdjacentArgsAmbiguous_spaced_minirust_direct :
    retAfterIntrCtx ctx0_2 int2ptrAdjacentArgsAmbiguous [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩] 13 =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

theorem int2ptrAdjacentArgsAmbiguous_spaced_tb_direct :
    retAfterIntrCtxTB ctx0_2 int2ptrAdjacentArgsAmbiguous [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]
      13 = tbRetU32 9 := by
  decide +kernel

/-- In the fragment, when two live exposed allocations meet at the reconstructed
address, Anneal returns `9` while both MiniRust machines stop with
`Stop.unsupported` instead of guessing: the angelic choice of `y`'s provenance
would make the read defined, but so would `x`'s for a continuation that first
subtracts `4`, so no committed resolution is exact. -/
theorem int2ptrAmbiguityUnsupported_three_way :
    inFragmentWithIntrinsics int2ptrAdjacentArgsAmbiguous = true ∧
      (∃ mem, ReachesRet (mirTree int2ptrAdjacentArgsAmbiguous
        (initMachineState int2ptrAdjacentArgsAmbiguous [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩])) []
        (.normal (.scalar ⟨9, 4⟩, mem))) ∧
      stopAfterIntrCtx ctxAdj int2ptrAdjacentArgsAmbiguous [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩] 11 =
        some (.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)") ∧
      stopAfterIntrCtxTB ctxAdj int2ptrAdjacentArgsAmbiguous [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩] 11 =
        some (.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)") :=
  ⟨int2ptrAdjacentArgsAmbiguous_inFragmentWithIntrinsics, int2ptrAdjacentArgsAmbiguous_anneal_ret,
    int2ptrAdjacentArgsAmbiguous_minirust_direct, int2ptrAdjacentArgsAmbiguous_tb_direct⟩

/-! ### `int2ptrDeadAllocUb`: the cast after deallocation -/

/-- MIR of
```rust
fn int2ptr_after_storage_dead_ub(_x: u32) -> u32 {
    let a: usize;
    {
        let t = 42u32;                         // _2
        let p = &raw const t;                  // _3
        a = p.expose_provenance();             // _4
    }                                          // StorageDead(_2)
    let q = std::ptr::with_exposed_provenance::<u32>(a);  // _5, after deallocation
    unsafe { *q }
}
```
-/
def int2ptrAfterStorageDeadUb : CapturedMir :=
  ptrBody "witness::int2ptr_after_storage_dead_ub"
    [u32Decl, u32Decl, u32Decl, ptrConstU32Decl, usizeDecl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .assign (local_ 2) (.use (constU32 42)),
     .assign (local_ 3) (.rawPtr .not (local_ 2)),
     .assign (local_ 4) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy),
     .storageDead 2,
     .assign (local_ 5) (.cast .pointerWithExposedProvenance (.copy (local_ 4)) ptrConstU32Ty),
     .assign (local_ 0) (.use (.copy (derefPlace 5)))]

theorem int2ptrAfterStorageDeadUb_translateIntr :
    (translateFnWithIntrinsics int2ptrAfterStorageDeadUb).isSome = true := by decide +kernel

/-- Borrowing a temporary is outside `ptrAliasingOk` (only never-deallocated
parameters may be borrowed), so the body is outside the fragment. -/
theorem int2ptrAfterStorageDeadUb_notInFragmentWithIntrinsics :
    inFragmentWithIntrinsics int2ptrAfterStorageDeadUb = false := by decide +kernel

theorem int2ptrAfterStorageDeadUb_anneal_ub :
    ∃ tr u, Reaches (mirTree int2ptrAfterStorageDeadUb
      (initMachineState int2ptrAfterStorageDeadUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound int2ptrAfterStorageDeadUb 30 _ (by decide)

theorem int2ptrAfterStorageDeadUb_minirust_direct :
    stopAfterIntr int2ptrAfterStorageDeadUb [.scalar ⟨5, 4⟩] 11 =
      some (.ub "dereferencing pointer to dead allocation") := by
  decide +kernel

theorem int2ptrAfterStorageDeadUb_tb_direct :
    stopAfterIntrTB int2ptrAfterStorageDeadUb [.scalar ⟨5, 4⟩] 11 =
      some (.ub "dereferencing pointer to dead allocation") := by
  decide +kernel

/-- Exposing a temporary, deallocating it, and only then reconstructing its
address: the single exposed provenance is predicted (`None` is the only other
admissible choice, and both fault, `int2ptr_checkPtr_ub_forced`), and the read
is UB on Anneal, `Mach`, and `MachTB`. -/
theorem int2ptrDeadAllocUb_three_way :
    (∃ tr u, Reaches (mirTree int2ptrAfterStorageDeadUb
        (initMachineState int2ptrAfterStorageDeadUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
      stopAfterIntr int2ptrAfterStorageDeadUb [.scalar ⟨5, 4⟩] 11 =
        some (.ub "dereferencing pointer to dead allocation") ∧
      stopAfterIntrTB int2ptrAfterStorageDeadUb [.scalar ⟨5, 4⟩] 11 =
        some (.ub "dereferencing pointer to dead allocation") :=
  ⟨int2ptrAfterStorageDeadUb_anneal_ub, int2ptrAfterStorageDeadUb_minirust_direct,
    int2ptrAfterStorageDeadUb_tb_direct⟩

/-! ### Pass A1's remaining witnesses on Anneal -/

theorem int2ptrDeadAllocDerefUb_notInFragmentWithIntrinsics :
    inFragmentWithIntrinsics int2ptrDeadAllocDerefUb = false := by decide +kernel

theorem int2ptrDeadAllocDerefUb_inFragmentWithIntrinsicsA1 :
    inFragmentWithIntrinsicsA1 int2ptrDeadAllocDerefUb = true := by decide +kernel

theorem int2ptrDeadAllocDerefUb_anneal_ub :
    ∃ tr u, Reaches (mirTree int2ptrDeadAllocDerefUb
      (initMachineState int2ptrDeadAllocDerefUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound int2ptrDeadAllocDerefUb 30 _ (by decide)

theorem int2ptrDeadAllocDerefUb_three_way :
    (∃ tr u, Reaches (mirTree int2ptrDeadAllocDerefUb
        (initMachineState int2ptrDeadAllocDerefUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
      stopAfterIntr int2ptrDeadAllocDerefUb [.scalar ⟨5, 4⟩] 11 =
        some (.ub "dereferencing pointer to dead allocation") ∧
      stopAfterIntrTB int2ptrDeadAllocDerefUb [.scalar ⟨5, 4⟩] 11 =
        some (.ub "dereferencing pointer to dead allocation") :=
  ⟨int2ptrDeadAllocDerefUb_anneal_ub, int2ptrDeadAllocDerefUb_minirust_direct,
    int2ptrDeadAllocDerefUb_tb_direct⟩

theorem int2ptrMultiAllocBoundaryUnsupported_notInFragmentWithIntrinsics :
    inFragmentWithIntrinsics int2ptrMultiAllocBoundaryUnsupported = false := by decide +kernel

theorem int2ptrMultiAllocBoundaryUnsupported_anneal_ub :
    ∃ tr u, Reaches (mirTree int2ptrMultiAllocBoundaryUnsupported
      (initMachineState int2ptrMultiAllocBoundaryUnsupported [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound int2ptrMultiAllocBoundaryUnsupported 40 _ (by decide)

/-- Pass A1 never ran this body: the forged address `1024` lies in neither
exposed allocation, so both MiniRust machines stop with `Stop.unsupported`
(not the message A1's docstring cited), while Anneal faults
(`1024 / 65536 = 0` names no borrow). -/
theorem int2ptrMultiAllocBoundaryUnsupported_three_way :
    (∃ tr u, Reaches (mirTree int2ptrMultiAllocBoundaryUnsupported
        (initMachineState int2ptrMultiAllocBoundaryUnsupported [.scalar ⟨5, 4⟩])) tr u ∧
        FaultNow u) ∧
      stopAfterIntr int2ptrMultiAllocBoundaryUnsupported [.scalar ⟨5, 4⟩] 15 =
        some (.unsupported
          "int2ptr: multiple exposed allocations and none contains the address (angelic choice)") ∧
      stopAfterIntrTB int2ptrMultiAllocBoundaryUnsupported [.scalar ⟨5, 4⟩] 15 =
        some (.unsupported
          "int2ptr: multiple exposed allocations and none contains the address (angelic choice)") :=
  ⟨int2ptrMultiAllocBoundaryUnsupported_anneal_ub, by decide +kernel, by decide +kernel⟩

/-! ## 3. Pass A1's `ProvenanceRel` fails on A1's own fragment -/

/-- Every exposed provenance names a live allocation. -/
def exposedAllLive (m : Mach) : Bool :=
  m.intptrcast.exposed.elems.all fun p =>
    decide (0 ≤ p.1._0) &&
      match m.mem.memory.allocations[p.1._0.toNat]? with
      | some a => a.live
      | none => false

theorem exposedAllLive_of_provenanceRel {body : CapturedMir} {ctx : Ctx} {s : MachineState}
    {m : Mach} {tags : List Nat} (h : ProvenanceRel body ctx s m tags) :
    exposedAllLive m = true := by
  unfold exposedAllLive
  rw [List.all_eq_true]
  intro p hp
  have hc : setContains m.intptrcast.exposed p = true := (setContains_iff_mem _ _).mpr hp
  obtain ⟨idx, a, rfl, ha, hlive⟩ := h.exposed_alloc_live hc
  simp [ha, hlive]

/-- After `10` steps of `int2ptrDeadAllocDerefUb` (just past `StorageDead(_2)`),
the exposed provenance of `_2` names a dead allocation. -/
theorem int2ptrDeadAllocDerefUb_exposed_dead :
    ((startMachineIntr int2ptrDeadAllocDerefUb [.scalar ⟨5, 4⟩]).bind
        (fun m => (Interp.steps 10 m).toOption)).map exposedAllLive = some false := by
  decide +kernel

/-- **`ProvenanceRel` is not an invariant of Pass A1's fragment.** The body is in
`inFragmentWithIntrinsicsA1`, its MiniRust run reaches a state (after
`StorageDead(_2)`) at which no `ProvenanceRel` holds for any Anneal state and
tag list. -/
theorem int2ptrDeadAllocDerefUb_provenanceRel_fails :
    inFragmentWithIntrinsicsA1 int2ptrDeadAllocDerefUb = true ∧
      ((startMachineIntr int2ptrDeadAllocDerefUb [.scalar ⟨5, 4⟩]).bind
        (fun m => (Interp.steps 10 m).toOption)).isSome = true ∧
      ∀ m', (startMachineIntr int2ptrDeadAllocDerefUb [.scalar ⟨5, 4⟩]).bind
          (fun m => (Interp.steps 10 m).toOption) = some m' →
        ∀ (ctx : Ctx) (s : MachineState) (tags : List Nat),
          ¬ ProvenanceRel int2ptrDeadAllocDerefUb ctx s m' tags := by
  refine ⟨int2ptrDeadAllocDerefUb_inFragmentWithIntrinsicsA1, by decide +kernel, ?_⟩
  intro m' hm' ctx s tags hrel
  have h1 := exposedAllLive_of_provenanceRel hrel
  have h2 := int2ptrDeadAllocDerefUb_exposed_dead
  rw [hm'] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  rw [h1] at h2
  cases h2

/-! ## 4. Incompleteness at dead exposed allocations (outside the fragment) -/

/-- MIR exposing a parameter `_1` and a temporary `_2`, deallocating `_2`, and
then reconstructing `_2`'s address. -/
def int2ptrAfterStorageDeadTwoExposed : CapturedMir :=
  ptrBody "witness::int2ptr_after_storage_dead_two_exposed"
    [u32Decl, u32Decl, u32Decl, ptrConstU32Decl, ptrConstU32Decl, usizeDecl, usizeDecl,
     ptrConstU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6,
     .storageLive 7,
     .assign (local_ 2) (.use (constU32 42)),
     .assign (local_ 3) (.rawPtr .not (local_ 1)),
     .assign (local_ 4) (.rawPtr .not (local_ 2)),
     .assign (local_ 5) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy),
     .assign (local_ 6) (.cast .pointerExposeProvenance (.copy (local_ 4)) usizeTy),
     .storageDead 2,
     .assign (local_ 7) (.cast .pointerWithExposedProvenance (.copy (local_ 6)) ptrConstU32Ty),
     .assign (local_ 0) (.use (.copy (derefPlace 7)))]

/-- Every admissible provenance (`None`, `_1`'s, or the dead `_2`'s) makes the read
UB, but with two exposed provenances and no live candidate the interpretation
stops with `Stop.unsupported` on both MiniRust machines (sound but incomplete),
while Anneal faults. -/
theorem int2ptrAfterStorageDeadTwoExposed_three_way :
    inFragmentWithIntrinsics int2ptrAfterStorageDeadTwoExposed = false ∧
      (∃ tr u, Reaches (mirTree int2ptrAfterStorageDeadTwoExposed
        (initMachineState int2ptrAfterStorageDeadTwoExposed [.scalar ⟨5, 4⟩])) tr u ∧
        FaultNow u) ∧
      stopAfterIntr int2ptrAfterStorageDeadTwoExposed [.scalar ⟨5, 4⟩] 14 =
        some (.unsupported
          "int2ptr: multiple exposed allocations and none contains the address (angelic choice)") ∧
      stopAfterIntrTB int2ptrAfterStorageDeadTwoExposed [.scalar ⟨5, 4⟩] 14 =
        some (.unsupported
          "int2ptr: multiple exposed allocations and none contains the address (angelic choice)") :=
  ⟨by decide +kernel, faultsA_sound int2ptrAfterStorageDeadTwoExposed 40 _ (by decide),
    by decide +kernel, by decide +kernel⟩

end MiniRustSpec.Correspondence.ProvenanceWitness
