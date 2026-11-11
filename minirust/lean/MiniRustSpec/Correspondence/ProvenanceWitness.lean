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
   * `exposeTwice` — Anneal and both MiniRust machines return `0` under
     canonical stack addresses (`exposeTwice_three_way_divergence`), while
     `provCastFlowOk = false` still conservatively rejects multi-exposure flow;
   * `int2ptrForgedTag` — Anneal and both MiniRust machines raise UB
     (`int2ptrForgedTag_three_way_divergence`) because `exposedAllocIds = []`
     prevents unexposed tag resurrection, while `provCastFlowOk` still rejects
     forged integer constants syntactically;
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
/-- With canonical stack local page addresses (`ptrAddress?`), Anneal and both
MiniRust machines (`Mach` and `MachTB`) return `0` on `exposeTwice` (while
`provCastFlowOk = false` still conservatively rejects `exposeTwice` from
`inFragmentWithIntrinsics`). -/
theorem exposeTwice_three_way_divergence :
    (∃ mem, ReachesRet (mirTree exposeTwice (initMachineState exposeTwice [.scalar ⟨5, 4⟩])) []
        (.normal (.scalar ⟨0, 4⟩, mem))) ∧
      retAfterIntr exposeTwice [.scalar ⟨5, 4⟩] 13 =
        some (some { retAlloc with data := scalarBytes u32 0 }, [1]) ∧
      retAfterIntrTB exposeTwice [.scalar ⟨5, 4⟩] 13 = tbRetU32 0 :=
  ⟨⟨_, exposeTwice_anneal_ret⟩, exposeTwice_intr_minirust_direct, exposeTwice_intr_tb_direct⟩

/-! ### `int2ptrForgedTag`: unexposed integer cast raises UB across all three machines -/

/-- MIR of
```rust
fn int2ptr_forged_tag(x: u32) -> u32 {
    let _p = &raw const x;                                   // borrow tag 1
    let q = std::ptr::with_exposed_provenance::<u32>(65536); // 1 * 65536
    unsafe { *q }
}
```
Nothing is exposed (`exposedAllocIds = []`), so `with_exposed_provenance(65536)`
recovers a provenance-less scalar `65536` and dereferencing `*q` raises UB in
Anneal as well as both MiniRust machines. -/
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

theorem int2ptrForgedTag_anneal_ub :
    ∃ tr u, Reaches (mirTree int2ptrForgedTag
      (initMachineState int2ptrForgedTag [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound int2ptrForgedTag 30 _ (by decide)

theorem int2ptrForgedTag_minirust_direct :
    stopAfterIntr int2ptrForgedTag [.scalar ⟨5, 4⟩] 6 =
      some (.ub "dereferencing pointer without provenance") := by
  decide +kernel

theorem int2ptrForgedTag_tb_direct :
    stopAfterIntrTB int2ptrForgedTag [.scalar ⟨5, 4⟩] 6 =
      some (.ub "dereferencing pointer without provenance") := by
  decide +kernel

/-- With `Memory.exposedAllocIds` enforced by `recoverExposedPtrValue?`, Anneal
and both MiniRust machines (`Mach` and `MachTB`) raise UB on `int2ptrForgedTag`
(while `provCastFlowOk` still excludes forged integer constants from
`inFragmentWithIntrinsics`). -/
theorem int2ptrForgedTag_three_way_divergence :
    inFragmentWithIntrinsicsA1 int2ptrForgedTag = true ∧
      (∃ tr u, Reaches (mirTree int2ptrForgedTag
        (initMachineState int2ptrForgedTag [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
      stopAfterIntr int2ptrForgedTag [.scalar ⟨5, 4⟩] 6 =
        some (.ub "dereferencing pointer without provenance") ∧
      stopAfterIntrTB int2ptrForgedTag [.scalar ⟨5, 4⟩] 6 =
        some (.ub "dereferencing pointer without provenance") :=
  ⟨int2ptrForgedTag_inFragmentWithIntrinsicsA1, int2ptrForgedTag_anneal_ub,
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

/-- Pre-exposure `MachineState` of `int2ptrRawRoundTripOk` right after
`_2 = &raw mut _1`. -/
def int2ptrRawRoundTripOkPreExposeState : MachineState :=
  let s0 := initMachineState int2ptrRawRoundTripOk [.scalar ⟨5, 4⟩]
  { s0 with
    frame := { s0.frame with
      locals := [.uninit, .init (.scalar ⟨5, 4⟩), .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] }
    memory := { s0.memory with
      borrows := [rawPtrEntry 1 .mut (local_ 1)]
      nextTag := 2 } }

/-- Concrete non-vacuity witness instantiating `AnnealExposeRoundTripOk` on
`int2ptrRawRoundTripOk` (`pv = ⟨1, 0⟩`, `fullAddr = (stackLocalAddrPageBase 8 + 1) * 65536`). -/
theorem int2ptrRawRoundTripOk_annealExposeRoundTripOk :
    AnnealExposeRoundTripOk int2ptrRawRoundTripOk int2ptrRawRoundTripOkPreExposeState
      ⟨1, 0⟩ ((MirSemantics.stackLocalAddrPageBase 8 + 1) * 65536) where
  tag_ne_zero := by decide
  addr_lt := by decide
  ptr_addr := by
    intro _ _
    rfl
  recover_eq := by
    intro localsPost hloc
    have h1 : Trusted.Sequence.get? localsPost 1 = some (.init (.scalar ⟨5, 4⟩)) := by
      have hb := hloc (rawPtrEntry 1 .mut (local_ 1)) (.head _)
      simpa [Trusted.Sequence.get?, int2ptrRawRoundTripOkPreExposeState, rawPtrEntry, local_] using hb
    have hbase : (MirSemantics.stackLocalAddrPageBase 8 + 1) * 65536 = 68719542272 := rfl
    rw [hbase]
    unfold MirSemantics.recoverExposedPtrValue? MirSemantics.findBestExposedStackBorrow
      MirSemantics.borrowPlaceByteOffset? MirSemantics.ptrAllocByteBound? lookupBorrow
    simp only [int2ptrRawRoundTripOkPreExposeState, initMachineState,
      MirSemantics.recordExposedAllocId, MirSemantics.isExposedAllocId,
      rawPtrEntry, local_, MirAst.ProvenancePtr.tag, h1]
    rfl

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

/-! ## 5. `inFragmentWithIntrinsics` vs. `singleExposeSiteOk` on `Mach` vs. `MachTB` (Pass A2) -/

theorem int2ptrRawRoundTripOk_singleExposeSiteOk :
    singleExposeSiteOk int2ptrRawRoundTripOk = true := by decide +kernel

theorem exposeSingleRefMutRoundTrip_singleExposeSiteOk :
    singleExposeSiteOk exposeSingleRefMutRoundTrip = true := by decide +kernel

theorem exposeTwoRefMutAngelicUnsupported_singleExposeSiteOk_false :
    singleExposeSiteOk exposeTwoRefMutAngelicUnsupported = false := by decide +kernel

/-- **Three-way `Mach` vs. `MachTB` multi-tag theorem inside `inFragmentWithIntrinsics`.**
`exposeTwoRefMutAngelicUnsupported` satisfies `inFragmentWithIntrinsics = true`
(because creating the second `&mut _1` disables the first, and only the second
exposed address `_7` is passed to `with_exposed_provenance`), and both Anneal
and `Mach` (`BasicMemory`, which deduplicates `(AllocId(1), ())` into a singleton
`exposed` set) return `88`, whereas `MachTB` (`TreeBorrowsMemory`) records two
distinct exposed `TreeBorrowsProvenance` tags `(AllocId(1), [0])` and
`(AllocId(1), [1])` at the same address and stops with `Stop.unsupported`
(`singleExposeSiteOk = false`). -/
theorem exposeTwoRefMutAngelicUnsupported_three_way :
    inFragmentWithIntrinsics exposeTwoRefMutAngelicUnsupported = true ∧
    singleExposeSiteOk exposeTwoRefMutAngelicUnsupported = false ∧
    (∃ mem, ReachesRet (mirTree exposeTwoRefMutAngelicUnsupported
      (initMachineState exposeTwoRefMutAngelicUnsupported [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨88, 4⟩, mem))) ∧
    retAfterIntr exposeTwoRefMutAngelicUnsupported [.scalar ⟨5, 4⟩] 18 =
      some (some { retAlloc with data := scalarBytes u32 88 }, [1]) ∧
    stopAfterIntrTB exposeTwoRefMutAngelicUnsupported [.scalar ⟨5, 4⟩] 15 =
      some (.unsupported
        "int2ptr: several exposed allocations meet at the address (angelic choice)") :=
  ⟨exposeTwoRefMutAngelicUnsupported_inFragmentWithIntrinsics,
   exposeTwoRefMutAngelicUnsupported_singleExposeSiteOk_false,
   exposeTwoRefMutAngelicUnsupported_anneal_ret,
   exposeTwoRefMutAngelicUnsupported_minirust_direct,
   exposeTwoRefMutAngelicUnsupported_tb_direct⟩

/-! ## 6. Real provenance-cast steps rewrite allocation bytes (Pass B3)

Pass A2's step lemmas assumed `m4.mem.memory.allocations = m.mem.memory.allocations`
for the MiniRust post-state `m4` of the intrinsic terminator. At the actual
`PointerExposeProvenance` (after 5 steps) and `PointerWithExposedProvenance`
(after 6 steps) terminators of `int2ptrRawRoundTripOk`, evaluating exactly the
terminator shapes those lemmas mention succeeds and *changes* the allocations
(the destination local receives the address, resp. the reconstructed pointer),
so that hypothesis held at no real step; `ProvenanceRel.expose_step` and
`ProvenanceRel.withExposed_step` (`Simulation.lean`) derive the post-state facts
instead. -/

/-- The `Mach` state of `int2ptrRawRoundTripOk` after `k` steps. -/
def rtState (k : Nat) : Option Mach :=
  (startMachineIntr int2ptrRawRoundTripOk [.scalar ⟨5, 4⟩]).bind
    (fun m => (Interp.steps k m).toOption)

/-- Whether `m` is about to evaluate its block terminator, and that terminator
is a provenance intrinsic of the given kind. -/
def pendingIntrinsic (m : Mach) (op : Gen.IntrinsicOp) : Bool :=
  match curFrame m with
  | .ok fr =>
    match mapIndex fr.func.blocks fr.next_block "" with
    | .ok blk =>
      decide (fr.next_stmt = (blk.statements.length : Int)) &&
        match blk.terminator with
        | .Intrinsic op' _ _ _ => decide (op' = op)
        | _ => false
    | .error _ => false
  | .error _ => false

/-- `int2ptrRawRoundTripOk`'s `PointerExposeProvenance` terminator. -/
def rtExposeTerm : Gen.Terminator :=
  .Intrinsic .PointerExposeProvenance [.Load (.Local (localName 2))] (.Local (localName 3))
    (some (bbName 1))

/-- `int2ptrRawRoundTripOk`'s `PointerWithExposedProvenance` terminator. -/
def rtWithExposedTerm : Gen.Terminator :=
  .Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName 3))] (.Local (localName 4))
    (some (bbName 2))

/-- Whether evaluating terminator `t` at `m` leaves the allocations literally
unchanged (`none` if the evaluation stops). -/
def termKeepsAllocs (t : Gen.Terminator) (m : Mach) : Option Bool :=
  (Interp.evalTerminator m t).toOption.map
    (fun m4 => decide (m4.mem.memory.allocations = m.mem.memory.allocations))

theorem rtState_pending_expose :
    (rtState 5).map (pendingIntrinsic · .PointerExposeProvenance) = some true := by
  decide +kernel

theorem rtState_pending_withExposed :
    (rtState 6).map (pendingIntrinsic · .PointerWithExposedProvenance) = some true := by
  decide +kernel

theorem rtState_expose_changes_allocs :
    (rtState 5).bind (termKeepsAllocs rtExposeTerm) = some false := by
  decide +kernel

theorem rtState_withExposed_changes_allocs :
    (rtState 6).bind (termKeepsAllocs rtWithExposedTerm) = some false := by
  decide +kernel

/-- At the real `PointerExposeProvenance` step, every successful evaluation of
the terminator changes the allocations: Pass A2's hypothesis
`m4.mem.memory.allocations = m.mem.memory.allocations` is unsatisfiable. -/
theorem passA2_hm4_allocs_unsatisfiable_expose :
    ∀ m, rtState 5 = some m → ∀ m4, Interp.evalTerminator m rtExposeTerm = .ok m4 →
      m4.mem.memory.allocations ≠ m.mem.memory.allocations := by
  intro m hm m4 hev heq
  have h := rtState_expose_changes_allocs
  rw [hm] at h
  simp only [Option.bind_some, termKeepsAllocs, hev, Except.toOption, Option.map_some,
    Option.some.injEq, decide_eq_false_iff_not] at h
  exact h heq

/-- At the real `PointerWithExposedProvenance` step, likewise. -/
theorem passA2_hm4_allocs_unsatisfiable_withExposed :
    ∀ m, rtState 6 = some m → ∀ m4, Interp.evalTerminator m rtWithExposedTerm = .ok m4 →
      m4.mem.memory.allocations ≠ m.mem.memory.allocations := by
  intro m hm m4 hev heq
  have h := rtState_withExposed_changes_allocs
  rw [hm] at h
  simp only [Option.bind_some, termKeepsAllocs, hev, Except.toOption, Option.map_some,
    Option.some.injEq, decide_eq_false_iff_not] at h
  exact h heq

/-- The MiniRust sub-evaluations that `ProvenanceRel.expose_step` takes as
hypotheses (`evalPlace` of `_3`, the load of `_2`, the `placeStore` after
exposing, `jumpToBlock`) all succeed at the real `PointerExposeProvenance` step
of `int2ptrRawRoundTripOk`, at `usize` type: unlike Pass A2's hypotheses they are
jointly satisfiable. -/
def exposeSubevalsOk (m : Mach) : Bool :=
  match evalPlace m (.Local (localName 3)) with
  | .ok ((pl, ty), m1) =>
    (match ty with
      | .Int it => decide (it = usizeIt)
      | _ => false) &&
      match evalValue m1 (.Load (.Local (localName 2))) with
      | .ok ((.Ptr ⟨ptr, none⟩, _), m2) =>
        match placeStore { m2 with intptrcast := IntPtrCast.expose m2.intptrcast ptr } pl
            (.Int ptr.addr) (.Int usizeIt) with
        | .ok m3 =>
          match jumpToBlock m3 (bbName 1) with
          | .ok _ => true
          | .error _ => false
        | .error _ => false
      | _ => false
  | .error _ => false

theorem rtState_expose_subevals_ok : (rtState 5).map exposeSubevalsOk = some true := by
  decide +kernel

/-- Executable check that the individual sub-evaluations of
`ProvenanceRel.withExposed_step_synced` (`evalPlace` of `_4`, `evalValue` of
`.Load (.Local (localName 3))` returning `(.Int 256, .Int usizeIt)`, `placeStore` of
the reconstructed pointer `{ addr := 256, provenance := some (⟨2⟩, ()) }`, and
`jumpToBlock`) all succeed at `rtState 6` of `int2ptrRawRoundTripOk`. -/
def withExposedSubevalsOk (m : Mach) : Bool :=
  match evalPlace m (.Local (localName 4)) with
  | .ok ((pl, ty), m1) =>
    (match ty with
      | .Ptr ptrTy => decide (PtrType.meta_kind ptrTy = .None)
      | _ => false) &&
      match evalValue m1 (.Load (.Local (localName 3))) with
      | .ok ((.Int addr, .Int it), m2) =>
        decide (addr = 256 ∧ it = usizeIt) &&
          match IntPtrCast.int2ptr m2 addr with
          | .ok ptr =>
            decide (ptr = { addr := 256, provenance := some (⟨2⟩, ()) }) &&
              match placeStore m2 pl (.Ptr ⟨ptr, none⟩) ty with
              | .ok m3 =>
                match jumpToBlock m3 (bbName 2) with
                | .ok _ => true
                | .error _ => false
              | .error _ => false
          | .error _ => false
      | _ => false
  | .error _ => false

theorem rtState_withExposed_subevals_ok : (rtState 6).map withExposedSubevalsOk = some true := by
  decide +kernel

/-- Concrete 2-step execution witness for `expose_then_withExposed` on
`int2ptrRawRoundTripOk`:
1. At `rtState 5` (immediately before `ExposeProvenance`), `m5.intptrcast.exposed.elems = []`.
2. Executing `rtExposeTerm` (`m5 -> m6`) exposes `targetProv ctx0 1 = (⟨2⟩, ())` and stores
   the target address `256` into `_3` so
   `evalValue m6 (.Load (.Local (localName 3))) = .ok ((.Int 256, .Int usizeIt), m6')`
   with `m6'.mem.memory.allocations = m6.mem.memory.allocations`.
3. Immediately executing `rtWithExposedTerm` (`m6 -> m7`) loads `256` from `_3`, resolves
   `IntPtrCast.int2ptr m6 256 = .ok { addr := 256, provenance := some (⟨2⟩, ()) }`, and stores
   the reconstructed pointer into `_4`. -/
def exposeThenWithExposedSyncedOk (m5 : Mach) : Bool :=
  decide (m5.intptrcast.exposed.elems = []) &&
    match Interp.evalTerminator m5 rtExposeTerm with
    | .ok m6 =>
      decide (m6.intptrcast.exposed.elems = [(⟨2⟩, ())]) &&
        match evalValue m6 (.Load (.Local (localName 3))) with
        | .ok ((.Int addr, .Int it), m6') =>
          decide (addr = 256 ∧ it = usizeIt ∧
            m6'.mem.memory.allocations = m6.mem.memory.allocations) &&
            match Interp.evalTerminator m6 rtWithExposedTerm with
            | .ok m7 =>
              match evalValue m7 (.Load (.Local (localName 4))) with
              | .ok ((.Ptr ⟨ptr, none⟩, _), _) =>
                decide (ptr = { addr := 256, provenance := some (⟨2⟩, ()) })
              | _ => false
            | .error _ => false
        | _ => false
    | .error _ => false

theorem rtState_expose_then_withExposed_synced :
    (rtState 5).map exposeThenWithExposedSyncedOk = some true := by
  decide +kernel

/-- MIR body with a single syntactic `PointerExposeProvenance` statement
(`countExposeStmts = 1`) inside a loop (`bb0 -> bb0`), which `isAcyclicCfg`
rejects. Its loop re-exposes `&raw mut _1`, and creating a raw pointer does not
retag, so on `MachTB` its exposed set stays a singleton however many iterations
run (`exposeLoopSingleSite_tb_exposed_singleton`); the loop that actually
accumulates distinct Tree Borrows tags at one site is `exposeLoopReborrow`. -/
def exposeLoopSingleSite : CapturedMir :=
  { int2ptrRawRoundTripOk with
    defPath := "witness::expose_loop_single_site"
    basicBlocks := [
      { statements := [
          ⟨.storageLive 2, ""⟩,
          ⟨.storageLive 3, ""⟩,
          ⟨.assign (local_ 2) (.rawPtr .mut (local_ 1)), ""⟩,
          ⟨.assign (local_ 3) (.cast .pointerExposeProvenance (.copy (local_ 2)) usizeTy), ""⟩
        ]
        terminator := ⟨.goto 0, ""⟩
        isCleanup := false }
    ] }

/-- `exposeLoopSingleSite` has only 1 syntactic `PointerExposeProvenance` statement,
yet its CFG has a back-edge (`bb0 -> bb0`), so `isAcyclicCfg` and `singleExposeSiteOk`
both reject it (`false`). -/
theorem exposeLoopSingleSite_countExposeStmts_eq_one :
    countExposeStmts exposeLoopSingleSite = 1 := by
  decide +kernel

theorem exposeLoopSingleSite_isAcyclicCfg_false :
    isAcyclicCfg exposeLoopSingleSite = false := by
  decide +kernel

theorem exposeLoopSingleSite_singleExposeSiteOk_false :
    singleExposeSiteOk exposeLoopSingleSite = false := by
  decide +kernel

/-! ## 7. A single exposure site in a loop: Tree Borrows tag accumulation (Pass B4) -/

/-- After 29 `MachTB` steps (several loop iterations) `exposeLoopSingleSite` has
exposed exactly one Tree Borrows provenance. -/
theorem exposeLoopSingleSite_tb_exposed_singleton :
    (startMachineIntrTB exposeLoopSingleSite [.scalar ⟨5, 4⟩]).bind
        (fun m => (Interp.stepsTB 29 m).toOption.map (·.intptrcast.exposed.elems.length)) =
      some 1 := by
  decide +kernel

/-- MIR of
```text
bb0: StorageLive(_2..=_5); goto bb1
bb1: _2 = &mut _1; _3 = &raw mut (*_2); _4 = _3 as usize (PointerExposeProvenance);
     _5 = _4 as *mut u32 (PointerWithExposedProvenance); (*_5) = const 7_u32; goto bb1
```
One exposure site, in a loop: every iteration retags `&mut _1`, so on `MachTB`
the second iteration exposes a second tag of `_1`'s allocation and
`PointerWithExposedProvenance` stops with `Stop.unsupported`, while `Mach`
(`()` provenance, deduplicated) keeps running. The body is in
`inFragmentWithIntrinsics`, and `singleExposeSiteOk` (which demands an acyclic
CFG) rejects it. -/
def exposeLoopReborrow : CapturedMir :=
  { int2ptrRawRoundTripOk with
    defPath := "witness::expose_loop_reborrow"
    localDecls := [u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, usizeDecl, ptrMutU32Decl]
    basicBlocks := [
      { statements := [⟨.storageLive 2, ""⟩, ⟨.storageLive 3, ""⟩, ⟨.storageLive 4, ""⟩,
          ⟨.storageLive 5, ""⟩]
        terminator := ⟨.goto 1, ""⟩
        isCleanup := false },
      { statements := [
          ⟨.assign (local_ 2) (.ref (.mut false) (local_ 1)), ""⟩,
          ⟨.assign (local_ 3) (.rawPtr .mut (derefPlace 2)), ""⟩,
          ⟨.assign (local_ 4) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy), ""⟩,
          ⟨.assign (local_ 5)
            (.cast .pointerWithExposedProvenance (.copy (local_ 4)) ptrMutU32Ty), ""⟩,
          ⟨.assign (derefPlace 5) (.use (constU32 7)), ""⟩]
        terminator := ⟨.goto 1, ""⟩
        isCleanup := false }] }

theorem exposeLoopReborrow_inFragmentWithIntrinsics :
    inFragmentWithIntrinsics exposeLoopReborrow = true := by decide +kernel

theorem exposeLoopReborrow_singleExposeSiteOk_false :
    singleExposeSiteOk exposeLoopReborrow = false := by decide +kernel

theorem exposeLoopReborrow_tb_two_tags :
    (startMachineIntrTB exposeLoopReborrow [.scalar ⟨5, 4⟩]).bind
        (fun m => (Interp.stepsTB 15 m).toOption.map (·.intptrcast.exposed.elems.length)) =
      some 2 := by
  decide +kernel

theorem exposeLoopReborrow_tb_unsupported :
    stopAfterIntrTB exposeLoopReborrow [.scalar ⟨5, 4⟩] 16 =
      some (.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)") := by
  decide +kernel

theorem exposeLoopReborrow_bm_runs :
    stopAfterIntr exposeLoopReborrow [.scalar ⟨5, 4⟩] 40 = none := by
  decide +kernel

/-- Anneal runs 60 steps of the loop without faulting. -/
theorem exposeLoopReborrow_anneal_no_fault_60 :
    faultsA exposeLoopReborrow 60 (initMachineState exposeLoopReborrow [.scalar ⟨5, 4⟩]) = false := by
  decide +kernel

/-! ## 8. Concrete round-trip reconstruction with a non-empty prior exposed set (Pass A4) -/

/-- `int2ptrAdjacentArgsAmbiguous` has two syntactic `PointerExposeProvenance`
statements (`_5 = _3 as usize` and `_6 = _4 as usize`), so `singleExposeSiteOk`
is `false`. -/
theorem int2ptrAdjacentArgsAmbiguous_countExposeStmts_eq_two :
    countExposeStmts int2ptrAdjacentArgsAmbiguous = 2 := by
  decide +kernel

theorem int2ptrAdjacentArgsAmbiguous_singleExposeSiteOk_false :
    singleExposeSiteOk int2ptrAdjacentArgsAmbiguous = false := by
  decide +kernel

/-- Concrete execution check for the 2-step round trip in the presence of a
prior exposure (`ProvenanceRel.expose_then_withExposed_reconstructs` /
`ProvenanceRel.expose_then_withExposed_from_frameOk`) on
`int2ptrAdjacentArgsAmbiguous` under `ctx0_2` (`_1` at `256`, `_2` at `384`):
1. After 9 `Mach` steps (`m9`, immediately after exposing `_3 = &raw const _1`),
   `m9.intptrcast.exposed.elems = [(⟨2⟩, ())]` is already non-empty, and no
   currently exposed live allocation contains `_2`'s address `384`
   (`int2ptrCandidates m9.mem.memory.allocations m9.intptrcast.exposed 384 = []`).
2. Step 10 (`m9 -> m10`, exposing `_4 = &raw const _2` into `_6`) extends
   `m10.intptrcast.exposed.elems` to `[(⟨2⟩, ()), (⟨3⟩, ())]` and stores `384`
   into `_6` (`evalValue m10 (.Load (.Local (localName 6))) = .ok ((.Int 384, .Int usizeIt), _)`),
   with `int2ptrCandidates m10.mem.memory.allocations m10.intptrcast.exposed 384 = [(⟨3⟩, ())]`
   and `IntPtrCast.int2ptr m10 384 = .ok { addr := 384, provenance := some (⟨3⟩, ()) }`.
3. Step 11 (`m10 -> m11`, `_7 = _6 as *const u32`) reconstructs and stores
   `{ addr := 384, provenance := some (⟨3⟩, ()) }` into `_7`. -/
def spacedSecondExposeReconstructsOk (m0 : Mach) : Bool :=
  match Interp.steps 9 m0 with
  | .ok m9 =>
    decide (m9.intptrcast.exposed.elems = [(⟨2⟩, ())]) &&
    decide (int2ptrCandidates m9.mem.memory.allocations m9.intptrcast.exposed 384 = []) &&
    match Interp.step m9 with
    | .ok m10 =>
      decide (m10.intptrcast.exposed.elems = [(⟨2⟩, ()), (⟨3⟩, ())]) &&
      decide (int2ptrCandidates m10.mem.memory.allocations m10.intptrcast.exposed 384 =
        [(⟨3⟩, ())]) &&
      match IntPtrCast.int2ptr m10 384 with
      | .ok ptr0 =>
        decide (ptr0 = { addr := 384, provenance := some (⟨3⟩, ()) }) &&
        match evalValue m10 (.Load (.Local (localName 6))) with
        | .ok ((.Int addr, .Int it), _) =>
          decide (addr = 384 ∧ it = usizeIt) &&
          match Interp.step m10 with
          | .ok m11 =>
            match evalValue m11 (.Load (.Local (localName 7))) with
            | .ok ((.Ptr ⟨ptr, none⟩, _), _) =>
              decide (ptr = { addr := 384, provenance := some (⟨3⟩, ()) })
            | _ => false
          | .error _ => false
        | _ => false
      | .error _ => false
    | .error _ => false
  | .error _ => false

theorem int2ptrAdjacentArgsAmbiguous_spaced_reconstructs_with_prior_exposure :
    (startMachineIntrCtx ctx0_2 int2ptrAdjacentArgsAmbiguous [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]).map
        spacedSecondExposeReconstructsOk =
      some true := by
  decide +kernel

/-! ## 9. `Assume` across reborrowing and provenance casts (MR-4.3 Pass B2) -/

/-- MIR of
```rust
fn assume_reborrow_expose_round_trip(mut x: u32) -> u32 {
    let r1 = &mut x;                                         // _2 = &mut _1
    let r2 = &mut *r1;                                       // _3 = &mut (*_2)
    *r2 = 42;                                                // (*_3) = const 42_u32
    let v = *r2;                                             // _4 = copy (*_3)
    let ok = v == 42;                                        // _5 = Eq(copy _4, const 42_u32)
    core::intrinsics::assume(ok);                            // Intrinsic(Assume(copy _5))
    let addr = (r2 as *mut u32).expose_provenance();         // _6 = PointerExposeProvenance(copy _3)
    let p = core::ptr::with_exposed_provenance_mut::<u32>(addr); // _7 = PointerWithExposedProvenance(copy _6)
    unsafe { *p = 99; *p }                                   // (*_7) = const 99_u32; _0 = copy (*_7)
}
```
Exercises `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume)` interleaved
with two-level `&mut` reborrowing (`_2 = &mut _1; _3 = &mut (*_2)`) and
`PointerExposeProvenance` / `PointerWithExposedProvenance` block splitting in a
single `inFragmentWithIntrinsics` body: `translateStmtOrIntrinsic` splits the
single MIR block into four MiniRust basic blocks (`bb0` ending in
`IntrinsicOp::Assume -> bb1`, `bb1` ending in `PointerExposeProvenance -> bb2`,
`bb2` ending in `PointerWithExposedProvenance -> bb3`, and `bb3` ending in
`Return`). -/
def assumeReborrowExposeRoundTrip : CapturedMir :=
  ptrBody "witness::assume_reborrow_expose_round_trip"
    [u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, u32Decl, boolDecl, usizeDecl, ptrMutU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .storageLive 6, .storageLive 7,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.rawPtr .mut (derefPlace 2)),
     .assign (derefPlace 3) (.use (constU32 42)),
     .assign (local_ 4) (.use (.copy (derefPlace 3))),
     .assign (local_ 5) (.binaryOp .eq (.copy (local_ 4)) (constU32 42)),
     .intrinsic (.assume (.copy (local_ 5))),
     .assign (local_ 6) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy),
     .assign (local_ 7) (.cast .pointerWithExposedProvenance (.copy (local_ 6)) ptrMutU32Ty),
     .assign (derefPlace 7) (.use (constU32 99)),
     .assign (local_ 0) (.use (.copy (derefPlace 7)))]

theorem assumeReborrowExposeRoundTrip_inFragmentWithIntrinsics :
    inFragmentWithIntrinsics assumeReborrowExposeRoundTrip = true := by
  decide +kernel

theorem assumeReborrowExposeRoundTrip_singleExposeSiteOk :
    singleExposeSiteOk assumeReborrowExposeRoundTrip = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem assumeReborrowExposeRoundTrip_anneal_ret :
    ∃ mem, ReachesRet (mirTree assumeReborrowExposeRoundTrip
      (initMachineState assumeReborrowExposeRoundTrip [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨99, 4⟩, mem)) :=
  ⟨_, runA_sound assumeReborrowExposeRoundTrip 35 _ _ _ rfl⟩

theorem assumeReborrowExposeRoundTrip_minirust_direct :
    retAfterIntr assumeReborrowExposeRoundTrip [.scalar ⟨5, 4⟩] 18 =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) := by
  decide +kernel

theorem assumeReborrowExposeRoundTrip_tb_direct :
    retAfterIntrTB assumeReborrowExposeRoundTrip [.scalar ⟨5, 4⟩] 18 = tbRetU32 99 := by
  decide +kernel

theorem assumeReborrowExposeRoundTrip_three_way :
    inFragmentWithIntrinsics assumeReborrowExposeRoundTrip = true ∧
      singleExposeSiteOk assumeReborrowExposeRoundTrip = true ∧
      (∃ mem, ReachesRet (mirTree assumeReborrowExposeRoundTrip
        (initMachineState assumeReborrowExposeRoundTrip [.scalar ⟨5, 4⟩])) []
        (.normal (.scalar ⟨99, 4⟩, mem))) ∧
      retAfterIntr assumeReborrowExposeRoundTrip [.scalar ⟨5, 4⟩] 18 =
        some (some { retAlloc with data := scalarBytes u32 99 }, [1]) ∧
      retAfterIntrTB assumeReborrowExposeRoundTrip [.scalar ⟨5, 4⟩] 18 = tbRetU32 99 :=
  ⟨assumeReborrowExposeRoundTrip_inFragmentWithIntrinsics,
    assumeReborrowExposeRoundTrip_singleExposeSiteOk,
    assumeReborrowExposeRoundTrip_anneal_ret,
    assumeReborrowExposeRoundTrip_minirust_direct,
    assumeReborrowExposeRoundTrip_tb_direct⟩

/-- Companion body in which the `Assume` condition after reborrowing is `false`
(`*r2 == 0` when `*r2 == 42`), raising UB across Anneal, `Mach`, and `MachTB`. -/
def assumeReborrowFalseUb : CapturedMir :=
  ptrBody "witness::assume_reborrow_false_ub"
    [u32Decl, u32Decl, refMutU32Decl, refMutU32Decl, u32Decl, boolDecl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.ref (.mut false) (derefPlace 2)),
     .assign (derefPlace 3) (.use (constU32 42)),
     .assign (local_ 4) (.use (.copy (derefPlace 3))),
     .assign (local_ 5) (.binaryOp .eq (.copy (local_ 4)) (constU32 0)),
     .intrinsic (.assume (.copy (local_ 5))),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem assumeReborrowFalseUb_inFragmentWithIntrinsics :
    inFragmentWithIntrinsics assumeReborrowFalseUb = true := by
  decide +kernel

theorem assumeReborrowFalseUb_anneal_ub :
    ∃ tr u, Reaches (mirTree assumeReborrowFalseUb
      (initMachineState assumeReborrowFalseUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound assumeReborrowFalseUb 25 _ (by decide)

theorem assumeReborrowFalseUb_minirust_direct :
    stopAfterIntr assumeReborrowFalseUb [.scalar ⟨5, 4⟩] 11 =
      some (.ub "`Assume` intrinsic called on condition that is violated") := by
  decide +kernel

theorem assumeReborrowFalseUb_tb_direct :
    stopAfterIntrTB assumeReborrowFalseUb [.scalar ⟨5, 4⟩] 11 =
      some (.ub "`Assume` intrinsic called on condition that is violated") := by
  decide +kernel

theorem assumeReborrowFalseUb_three_way :
    inFragmentWithIntrinsics assumeReborrowFalseUb = true ∧
      (∃ tr u, Reaches (mirTree assumeReborrowFalseUb
        (initMachineState assumeReborrowFalseUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
      stopAfterIntr assumeReborrowFalseUb [.scalar ⟨5, 4⟩] 11 =
        some (.ub "`Assume` intrinsic called on condition that is violated") ∧
      stopAfterIntrTB assumeReborrowFalseUb [.scalar ⟨5, 4⟩] 11 =
        some (.ub "`Assume` intrinsic called on condition that is violated") :=
  ⟨assumeReborrowFalseUb_inFragmentWithIntrinsics,
    assumeReborrowFalseUb_anneal_ub,
    assumeReborrowFalseUb_minirust_direct,
    assumeReborrowFalseUb_tb_direct⟩

/-! ## 10. Multi-frame calls with `&mut` protectors and provenance casts (MR-4.3 Passes B2-A3)

Concrete multi-function `CapturedMir` programs translated via
`translateProgWithIntrinsics` (syntactically checked by `progCrossFrameTranslatable`
and correctly excluded from the sound Anneal–MiniRust correspondence fragment
`progInFragmentWithIntrinsics` because they pass pointers/references across
frames), executed across all three semantics (Anneal `mirCallTreeWithCallees`,
MiniRust `Mach`, and MiniRust `MachTB`). -/

/-- Callee `fn add37_ref_mut(r: &mut u32) -> u32`: validates `r` with
`fn_entry = true` (`Protected::Strong` under Tree Borrows), writes `*r = *r + 37`,
and returns `*r`. -/
def calleeAdd37RefMutMir : CapturedMir where
  defPath := "witness::add37_ref_mut"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, refMutU32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.retag .fnEntry (local_ 1)),
        mkStmt (.assign (local_ 2) (.use (.copy (derefPlace 1)))),
        mkStmt (.assign (derefPlace 1) (.binaryOp .add (.copy (local_ 2)) (constU32 37))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefPlace 1)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller `fn call_ref_mut_protected(mut x: u32) -> u32`: borrows `_2 = &mut _1`,
calls `add37_ref_mut(move _2) -> _3`, and returns `_3 + _1`. -/
def callerRefMutProtectedMir : CapturedMir where
  defPath := "witness::call_ref_mut_protected"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, refMutU32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1)))],
      terminator := mkTerm (.call (fnDefOp "witness::add37_ref_mut")
        [.move (local_ 2)] (local_ 3) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 3)) (.copy (local_ 1)))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Counterexample caller writing `Call`'s return value directly to address-taken
local `_1`: rejected by `termPreservesAddrTaken` and `progInFragmentWithIntrinsics`. -/
def callerRefMutProtectedBadCallDstMir : CapturedMir where
  defPath := "witness::call_ref_mut_protected_bad_dst"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, refMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1)))],
      terminator := mkTerm (.call (fnDefOp "witness::add37_ref_mut")
        [.move (local_ 2)] (local_ 1) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callRefMutProtected_inFragmentWithIntrinsics :
    progCrossFrameTranslatable callerRefMutProtectedMir [calleeAdd37RefMutMir] = true ∧
    progInFragmentWithIntrinsics callerRefMutProtectedMir [calleeAdd37RefMutMir] = false := by
  decide +kernel

theorem callerRefMutProtectedBadCallDst_notInFragmentWithIntrinsics :
    progCrossFrameTranslatable callerRefMutProtectedBadCallDstMir [calleeAdd37RefMutMir] = false ∧
    progInFragmentWithIntrinsics callerRefMutProtectedBadCallDstMir [calleeAdd37RefMutMir] = false := by
  decide +kernel

def calleeAdd37RefMutFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, refTy .mut u32), (localName 2, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Validate (.Local (localName 1)) true,
      .Assign (.Local (localName 2))
        (.Load (.Deref (.Load (.Local (localName 1))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 1))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 2))) (.Constant (.Int 37) (.Int u32))),
      .Assign (.Local (localName 0))
        (.Load (.Deref (.Load (.Local (localName 1))) (.Int u32))),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def callerRefMutProtectedFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .Assign (.Local (localName 2))
        (.AddrOf (.Local (localName 1)) (refPtrType .mut u32))],
      .Call (fnPtrExpr (fnName 1)) .Rust
        [.InPlace (.Local (localName 2))]
        (.Local (localName 3)) (some (bbName 1)) (some (bbName 3)), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 3))) (.Load (.Local (localName 1)))),
      .StorageDead (localName 3),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩),
    (bbName 3, ⟨[], .ResumeUnwind, .Cleanup⟩)]⟩
  start := bbName 2
  implicit_writes := true

def callRefMutProtectedProg : Gen.Program where
  functions := ⟨[(fnName 0, callerRefMutProtectedFn),
    (fnName 1, calleeAdd37RefMutFn),
    (fnName 2, mkStartFn 0)]⟩
  start := fnName 2
  globals := ⟨[]⟩
  vtables := ⟨[]⟩
  traits := ⟨[]⟩

theorem callRefMutProtected_translateProgWithIntrinsics :
    translateProgWithIntrinsics callerRefMutProtectedMir [calleeAdd37RefMutMir] =
      some callRefMutProtectedProg := rfl

def ctxCallRefMut1 : Ctx :=
  ctxWithFns callerFrame retAlloc 2 [128, 256]

def callRefMutProtectedMInit : Mach :=
  multiMachineWithCtx ctxCallRefMut1 callRefMutProtectedProg 2 callerRefMutProtectedMir
    callerRefMutProtectedFn [.uninit, .init (.scalar ⟨5, 4⟩)] callerRefMutProtectedFn.start

def callRefMutProtectedTBInit : MachTB :=
  liftMachToTB callRefMutProtectedMInit

/-- `progInFragment` (used by `multi_step_correspondence`) rejects
`callerRefMutProtectedMir` / `calleeAdd37RefMutMir` because `_1 : &mut u32` is
non-scalar; in Anneal's `MirSemantics`, `Terminators.evalTerminator` saves the
caller's locals on `s.memory.callStack` without rebinding `BorrowEntry.targetLocal`
across frames, so dereferencing `*_1` inside `calleeAdd37RefMutMir` reads the
callee's own `_1` (`Value.ptr`) and faults on `Value.ptr + 37`. -/
theorem callRefMutProtected_anneal_ret :
    progInFragment callerRefMutProtectedMir [calleeAdd37RefMutMir] = false ∧
    (∃ tr u, Reaches
      (mirCallTreeWithCallees callerRefMutProtectedMir [.scalar ⟨5, 4⟩] [calleeAdd37RefMutMir])
      tr u ∧ FaultNow u) :=
  ⟨by decide +kernel, faultsA_sound callerRefMutProtectedMir 25 _ (by decide)⟩

/-- Multi-frame `Call` passing `&mut u32` with function-entry `Validate` (`fn_entry = true`)
succeeds on both `Mach` (`BasicMemory`) and `MachTB` (`TreeBorrowsMemory`),
updating caller local `_1` from `5` to `42`, releasing the callee's strong
protector on `Return`, and returning `42 + 42 = 84`. -/
theorem callRefMutProtectedRoundTrip_mach_and_tb :
    (Interp.steps 17 callRefMutProtectedMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 84 }, [1]) ∧
    (Interp.stepsTB 17 callRefMutProtectedTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 84 := by
  decide +kernel

theorem callRefMutProtectedRoundTrip_three_way :
    progInFragment callerRefMutProtectedMir [calleeAdd37RefMutMir] = false ∧
    progCrossFrameTranslatable callerRefMutProtectedMir [calleeAdd37RefMutMir] = true ∧
    progInFragmentWithIntrinsics callerRefMutProtectedMir [calleeAdd37RefMutMir] = false ∧
    translateProgWithIntrinsics callerRefMutProtectedMir [calleeAdd37RefMutMir] =
      some callRefMutProtectedProg ∧
    (∃ tr u, Reaches
      (mirCallTreeWithCallees callerRefMutProtectedMir [.scalar ⟨5, 4⟩] [calleeAdd37RefMutMir])
      tr u ∧ FaultNow u) ∧
    (Interp.steps 17 callRefMutProtectedMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 84 }, [1]) ∧
    (Interp.stepsTB 17 callRefMutProtectedTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 84 :=
  ⟨callRefMutProtected_anneal_ret.1,
   callRefMutProtected_inFragmentWithIntrinsics.1,
   callRefMutProtected_inFragmentWithIntrinsics.2,
   callRefMutProtected_translateProgWithIntrinsics,
   callRefMutProtected_anneal_ret.2,
   callRefMutProtectedRoundTrip_mach_and_tb.1,
   callRefMutProtectedRoundTrip_mach_and_tb.2⟩

/-- Callee `fn protector_conflict(r: &mut u32, raw: *mut u32) -> u32`:
validates `r` at function entry (`Protected::Strong`), activates `r` via `*r = 10`,
and then writes `*raw = 20` through the aliasing parent raw pointer `raw` while
`r`'s strong function-entry protector is still active. -/
def calleeProtectorConflictMir : CapturedMir where
  defPath := "witness::protector_conflict"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, refMutU32Decl, ptrMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.retag .fnEntry (local_ 1)),
        mkStmt (.assign (derefPlace 1) (.use (constU32 10))),
        mkStmt (.assign (derefPlace 2) (.use (constU32 20))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefPlace 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

/-- Caller `fn call_protector_conflict(mut x: u32) -> u32`: creates `raw = &raw mut _1`,
reborrows `r = &mut *raw`, and calls `protector_conflict(move r, move raw)`. -/
def callerProtectorConflictMir : CapturedMir where
  defPath := "witness::call_protector_conflict"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, ptrMutU32Decl, refMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.ref (.mut false) (derefPlace 2)))],
      terminator := mkTerm (.call (fnDefOp "witness::protector_conflict")
        [.move (local_ 3), .move (local_ 2)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callProtectorConflict_inFragmentWithIntrinsics :
    progCrossFrameTranslatable callerProtectorConflictMir [calleeProtectorConflictMir] = true ∧
    progInFragmentWithIntrinsics callerProtectorConflictMir [calleeProtectorConflictMir] = false := by
  decide +kernel

def calleeProtectorConflictFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, refTy .mut u32),
    (localName 2, thinRawPtrTy)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Validate (.Local (localName 1)) true,
      .Assign (.Deref (.Load (.Local (localName 1))) (.Int u32))
        (.Constant (.Int 10) (.Int u32)),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.Constant (.Int 20) (.Int u32)),
      .Assign (.Local (localName 0))
        (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def callerProtectorConflictFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, thinRawPtrTy), (localName 3, refTy .mut u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .Assign (.Local (localName 2))
        (.AddrOf (.Local (localName 1)) (.Raw .None)),
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .mut u32))],
      .Call (fnPtrExpr (fnName 1)) .Rust
        [.InPlace (.Local (localName 3)), .InPlace (.Local (localName 2))]
        (.Local (localName 0)) (some (bbName 1)) (some (bbName 3)), .Regular⟩),
    (bbName 1, ⟨[
      .StorageDead (localName 3),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩),
    (bbName 3, ⟨[], .ResumeUnwind, .Cleanup⟩)]⟩
  start := bbName 2
  implicit_writes := true

def callProtectorConflictProg : Gen.Program where
  functions := ⟨[(fnName 0, callerProtectorConflictFn),
    (fnName 1, calleeProtectorConflictFn),
    (fnName 2, mkStartFn 0)]⟩
  start := fnName 2
  globals := ⟨[]⟩
  vtables := ⟨[]⟩
  traits := ⟨[]⟩

theorem callProtectorConflict_translateProgWithIntrinsics :
    translateProgWithIntrinsics callerProtectorConflictMir [calleeProtectorConflictMir] =
      some callProtectorConflictProg := rfl

def callProtectorConflictMInit : Mach :=
  multiMachineWithCtx ctxCallRefMut1 callProtectorConflictProg 2 callerProtectorConflictMir
    callerProtectorConflictFn [.uninit, .init (.scalar ⟨5, 4⟩)] callerProtectorConflictFn.start

def callProtectorConflictTBInit : MachTB :=
  liftMachToTB callProtectorConflictMInit

def stopStepsTB (n : Nat) (m : MachTB) : Option Stop :=
  match Interp.stepsTB n m with
  | .error e => some e
  | .ok _ => none

theorem callProtectorConflict_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees callerProtectorConflictMir [.scalar ⟨5, 4⟩] [calleeProtectorConflictMir])
      tr u ∧ FaultNow u :=
  faultsA_sound callerProtectorConflictMir 25 _ (by decide)

/-- On `Mach` (`BasicMemory`, which has no Tree Borrows aliasing model),
`callProtectorConflict` completes normally and returns `20`; on `MachTB`
(`TreeBorrowsMemory`), the write through `raw` while `r`'s function-entry
protector (`PermissionProt::Unique`) is active raises Tree Borrows UB
(`"Tree Borrows: foreign read of protected Unique reference"` in
`PermissionProt::foreign_write`). On Anneal (`mirCallTreeWithCallees`),
`*_1 = 10` resolves `r`'s un-namespaced `targetLocal = 1` against
`callee.frame.locals[1]` (overwriting `r` with `.scalar ⟨10, 4⟩` and disabling
`raw`'s borrow tag via `invalidateDerefWriteBorrows`), faulting on `*_2 = 20`. -/
theorem callRefMutProtectorViolation_mach_vs_tb :
    (Interp.steps 15 callProtectorConflictMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 20 }, [1]) ∧
    stopStepsTB 10 callProtectorConflictTBInit =
      some (.ub "Tree Borrows: foreign read of protected Unique reference") := by
  decide +kernel

theorem callRefMutProtectorViolation_three_way :
    progCrossFrameTranslatable callerProtectorConflictMir [calleeProtectorConflictMir] = true ∧
    progInFragmentWithIntrinsics callerProtectorConflictMir [calleeProtectorConflictMir] = false ∧
    translateProgWithIntrinsics callerProtectorConflictMir [calleeProtectorConflictMir] =
      some callProtectorConflictProg ∧
    (∃ tr u, Reaches
      (mirCallTreeWithCallees callerProtectorConflictMir [.scalar ⟨5, 4⟩] [calleeProtectorConflictMir])
      tr u ∧ FaultNow u) ∧
    (Interp.steps 15 callProtectorConflictMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 20 }, [1]) ∧
    stopStepsTB 10 callProtectorConflictTBInit =
      some (.ub "Tree Borrows: foreign read of protected Unique reference") :=
  ⟨callProtectorConflict_inFragmentWithIntrinsics.1,
   callProtectorConflict_inFragmentWithIntrinsics.2,
   callProtectorConflict_translateProgWithIntrinsics,
   callProtectorConflict_anneal_ub,
   callRefMutProtectorViolation_mach_vs_tb.1,
   callRefMutProtectorViolation_mach_vs_tb.2⟩

/-- Callee `fn expose_ptr_callee(p: *mut u32) -> usize`: exposes `p` via
`CastKind::PointerExposeProvenance` (`IntrinsicOp::PointerExposeProvenance`) and
returns the exposed `usize` address to its caller. -/
def calleeExposePtrMir : CapturedMir where
  defPath := "witness::expose_ptr_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [usizeDecl, ptrMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.cast .pointerExposeProvenance (.copy (local_ 1)) usizeTy))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller `fn call_cross_frame_expose_with_exposed(mut x: u32) -> u32`:
creates `_2 = &mut _1` and `_3 = &raw mut (*_2)`, passes `_3` to
`expose_ptr_callee(move _3) -> _4`, reconstructs `_5 : *mut u32` in the caller
frame via `CastKind::PointerWithExposedProvenance`
(`IntrinsicOp::PointerWithExposedProvenance`), writes `(*_5) = 88`, and returns
`_1` (`88`). -/
def callerCrossFrameExposeMir : CapturedMir where
  defPath := "witness::call_cross_frame_expose_with_exposed"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, usizeDecl, ptrMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.storageLive 4),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
        mkStmt (.assign (local_ 3) (.rawPtr .mut (derefPlace 2)))],
      terminator := mkTerm (.call (fnDefOp "witness::expose_ptr_callee")
        [.move (local_ 3)] (local_ 4) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 5)
          (.cast .pointerWithExposedProvenance (.copy (local_ 4)) ptrMutU32Ty)),
        mkStmt (.assign (derefPlace 5) (.use (constU32 88))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 5),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callCrossFrameExpose_inFragmentWithIntrinsics :
    progCrossFrameTranslatable callerCrossFrameExposeMir [calleeExposePtrMir] = true ∧
    progInFragmentWithIntrinsics callerCrossFrameExposeMir [calleeExposePtrMir] = false := by
  decide +kernel

def calleeExposePtrFn : Gen.Function where
  locals := ⟨[(localName 0, .Int usizeIt), (localName 1, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[],
      .Intrinsic .PointerExposeProvenance [.Load (.Local (localName 1))]
        (.Local (localName 0)) (some (bbName 2)), .Regular⟩),
    (bbName 2, ⟨[], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def callerCrossFrameExposeFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, thinRawPtrTy),
    (localName 4, .Int usizeIt), (localName 5, thinRawPtrTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .StorageLive (localName 4),
      .StorageLive (localName 5),
      .Assign (.Local (localName 2))
        (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (.Raw .None))],
      .Call (fnPtrExpr (fnName 1)) .Rust
        [.InPlace (.Local (localName 3))]
        (.Local (localName 4)) (some (bbName 1)) (some (bbName 3)), .Regular⟩),
    (bbName 1, ⟨[],
      .Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName 4))]
        (.Local (localName 5)) (some (bbName 4)), .Regular⟩),
    (bbName 4, ⟨[
      .Assign (.Deref (.Load (.Local (localName 5))) (.Int u32))
        (.Constant (.Int 88) (.Int u32)),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1))),
      .StorageDead (localName 5),
      .StorageDead (localName 4),
      .StorageDead (localName 3),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩),
    (bbName 3, ⟨[], .ResumeUnwind, .Cleanup⟩)]⟩
  start := bbName 2
  implicit_writes := true

def callCrossFrameExposeProg : Gen.Program where
  functions := ⟨[(fnName 0, callerCrossFrameExposeFn),
    (fnName 1, calleeExposePtrFn),
    (fnName 2, mkStartFn 0)]⟩
  start := fnName 2
  globals := ⟨[]⟩
  vtables := ⟨[]⟩
  traits := ⟨[]⟩

theorem callCrossFrameExpose_translateProgWithIntrinsics :
    translateProgWithIntrinsics callerCrossFrameExposeMir [calleeExposePtrMir] =
      some callCrossFrameExposeProg := rfl

def callCrossFrameExposeMInit : Mach :=
  multiMachineWithCtx ctxCallRefMut1 callCrossFrameExposeProg 2 callerCrossFrameExposeMir
    callerCrossFrameExposeFn [.uninit, .init (.scalar ⟨5, 4⟩)] callerCrossFrameExposeFn.start

def callCrossFrameExposeTBInit : MachTB :=
  liftMachToTB callCrossFrameExposeMInit

theorem callCrossFrameExpose_anneal_ret :
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerCrossFrameExposeMir [.scalar ⟨5, 4⟩] [calleeExposePtrMir])
      tr (.normal (.scalar ⟨88, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerCrossFrameExposeMir [.scalar ⟨5, 4⟩] [calleeExposePtrMir]) :=
  runsToScalar_sound (fuel := 30) (by decide)

/-- Exposing a pointer in a callee frame (`PointerExposeProvenance`) and
reconstructing it in the caller frame (`PointerWithExposedProvenance`) after
`Return` succeeds and returns `88` on Anneal (`mirCallTreeWithCallees`), `Mach`
(`BasicMemory`), and `MachTB` (`TreeBorrowsMemory`). -/
theorem callCrossFrameExposeWithExposed_mach_and_tb :
    (Interp.steps 19 callCrossFrameExposeMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 88 }, [1]) ∧
    (Interp.stepsTB 19 callCrossFrameExposeTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 88 := by
  decide +kernel

theorem callCrossFrameExposeWithExposed_three_way :
    progCrossFrameTranslatable callerCrossFrameExposeMir [calleeExposePtrMir] = true ∧
    progInFragmentWithIntrinsics callerCrossFrameExposeMir [calleeExposePtrMir] = false ∧
    translateProgWithIntrinsics callerCrossFrameExposeMir [calleeExposePtrMir] =
      some callCrossFrameExposeProg ∧
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerCrossFrameExposeMir [.scalar ⟨5, 4⟩] [calleeExposePtrMir])
      tr (.normal (.scalar ⟨88, 4⟩, mem))) ∧
    (Interp.steps 19 callCrossFrameExposeMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 88 }, [1]) ∧
    (Interp.stepsTB 19 callCrossFrameExposeTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 88 :=
  ⟨callCrossFrameExpose_inFragmentWithIntrinsics.1,
   callCrossFrameExpose_inFragmentWithIntrinsics.2,
   callCrossFrameExpose_translateProgWithIntrinsics,
   callCrossFrameExpose_anneal_ret.1,
   callCrossFrameExposeWithExposed_mach_and_tb.1,
   callCrossFrameExposeWithExposed_mach_and_tb.2⟩

/-! ## 11. Pass B3 multi-function fragment counterexamples and sound unified witness (MR-4.3 Pass A3)

1. **`progInFragmentWithIntrinsicsB3`** records the multi-function predicate as
   Pass B3 defined it (omitting `provCastFlowOk`, `ptrAliasingProgOk`,
   `provCastAliasView`, scalar call-boundary checks, and using `isDeclPtrLocal`
   on `.retag .fnEntry`). We prove both `progCrossFrameTranslatable_imp_B3` and
   `progInFragmentWithIntrinsics_imp_B3`, and then witness every independent
   divergence that `progInFragmentWithIntrinsicsB3` admitted:
   * `exposeTwice_B3_divergence`, `int2ptrForgedTag_B3_divergence`,
     `childReborrowWriteDisablesParent_B3_divergence`, and
     `exposeSharedRefWriteUb_B3_divergence` (single-body `callees = []`
     divergences, including `int2ptrForgedTag` where Anneal succeeds and returns
     `5` while `Mach` and `MachTB` raise UB);
   * `callerRawPtrRetagFnEntry_B3_divergence` (`Retag(FnEntry)` on a `*mut u32`
     parameter attaches a strong protector in Anneal, faulting on `StorageDead`
     of an unrelated callee local, while `Mach` and `MachTB` return `7`);
   * `callerRefMutSilentWrongLocal_divergence` (cross-frame `&mut u32` argument
     where Anneal does **not** fault — it succeeds with `MirNoUBTree` and
     **silently returns the wrong scalar `137`** by reading `callee`'s own `_1`
     instead of `caller`'s `_1`, while `Mach` and `MachTB` return `42`);
   * `callerBorrowAcrossScalarCall_divergence` (scalar-only `Call` where both
     bodies individually satisfy `ptrAliasingOk = true`, yet `callee`'s root
     assignment `_1 = _1 + 36` disables `caller`'s active borrow `_2 = &raw mut _1`
     in Anneal's global `borrows` table, faulting after `Return` while `Mach` and
     `MachTB` return `42` — proving `ptrAliasingProgOk` is strictly required over
     per-body `ptrAliasingOk`).
2. **`callerBorrowExposeAndScalarCall_three_way`** provides a positive 2-function
   witness inside the sound unified fragment (`progInFragment = false`,
   `progInFragmentWithIntrinsics = true`), combining `Call`, `&mut`, `&raw mut`,
   `Retag`, `Assume`, `PointerExposeProvenance`, and
   `PointerWithExposedProvenance` with 3-way agreement (`92` + `MirNoUBTree`)
   across Anneal, `Mach`, and `MachTB`. -/

/-- Statement predicate exactly as Pass B3 defined `progStmtOkWithIntrinsics`
(`isDeclPtrLocal` on `.retag .fnEntry`, admitting raw pointer parameters). -/
def progStmtOkWithIntrinsicsB3 (argCount : Nat) (decls : List MirAst.LocalDecl)
    (s : MirAst.Statement) (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Bool :=
  statementOkWithIntrinsics decls s layouts ||
  match s.kind with
  | .retag .fnEntry ⟨i, []⟩ =>
    decide (1 ≤ i ∧ i ≤ argCount) && decide (i < decls.length) && isDeclPtrLocal decls i
  | _ => false

/-- Per-body multi-function predicate exactly as Pass B3 defined
`bodyInProgFragmentWithIntrinsics`. -/
def bodyInProgFragmentWithIntrinsicsB3 (fnMap : FnMap)
    (callees : List MirAst.CapturedMir) (body : MirAst.CapturedMir) : Bool :=
  let addrLocals := bodyAddrTakenLocals body
  body.isRuntimePostCleanup &&
  decide (body.argCount + 1 ≤ body.localDecls.length) &&
  decide (body.localDecls.length < 2 ^ 31) &&
  body.localDecls.all (localDeclOk body.layouts) &&
  decide (body.basicBlocks ≠ []) &&
  (List.range body.basicBlocks.length).all (fun blk =>
    match body.basicBlocks[blk]? with
    | some bb =>
      !bb.isCleanup &&
      bb.statements.all (progStmtOkWithIntrinsicsB3 body.argCount body.localDecls · body.layouts) &&
      bb.statements.all (stmtPreservesAddrTaken addrLocals) &&
      termPreservesAddrTaken addrLocals bb.terminator &&
      terminatorInProgOkWithIntrinsics callees body blk bb.terminator
    | none => true) &&
  addrLocals.all (fun k => decide (1 ≤ k ∧ k ≤ body.argCount)) &&
  storageDeadOk body && movesOk body && mentionsOk body &&
  livenessOk body && tupleInitOk body &&
  (translateFnInProgWithIntrinsics fnMap body).isSome

/-- Multi-function fragment predicate exactly as Pass B3 defined
`progInFragmentWithIntrinsics`. -/
def progInFragmentWithIntrinsicsB3 (entry : MirAst.CapturedMir)
    (callees : List MirAst.CapturedMir) : Bool :=
  let fnMap := fnNameMap entry callees
  ((entry :: callees).map (·.defPath)).Nodup &&
  (entry :: callees).all (bodyInProgFragmentWithIntrinsicsB3 fnMap callees) &&
  (match maxStackLocals entry callees with
   | some bound => decide (bound < 2 ^ 31)
   | none => false) &&
  (translateProgWithIntrinsics entry callees).isSome

private theorem isDeclPtrLocal_of_isRefTy {decls : List MirAst.LocalDecl} {i : Nat}
    {d : MirAst.LocalDecl} (hd : decls[i]? = some d) (href : isRefTy d.ty = true) :
    isDeclPtrLocal decls i = true := by
  unfold isDeclPtrLocal isPtrTy ptrPointeeOf
  unfold isRefTy refPointeeOf at href
  rw [hd]
  dsimp only
  cases hk : d.ty.kind with
  | ref mutbl pointee => rw [hk] at href; exact href
  | _ => simp [hk] at href

theorem progCrossFrameTranslatable_imp_B3 {entry : CapturedMir} {callees : List CapturedMir}
    (h : progCrossFrameTranslatable entry callees = true) :
    progInFragmentWithIntrinsicsB3 entry callees = true := by
  simp only [progCrossFrameTranslatable, progInFragmentWithIntrinsicsB3,
    Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨hnodup, hall⟩, hstack⟩, htr⟩ := h
  refine ⟨⟨⟨hnodup, fun b hb => ?_⟩, hstack⟩, htr⟩
  have hbf := hall b hb
  simp only [bodyCrossFrameTranslatable, bodyInProgFragmentWithIntrinsicsB3,
    Bool.and_eq_true, List.all_eq_true] at hbf ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hbbs⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hbf
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, fun blk hblk => ?_⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩
  have hb0 := hbbs blk hblk
  cases hget : b.basicBlocks[blk]? with
  | none => rfl
  | some bb =>
    simp only [hget, Bool.and_eq_true, List.all_eq_true] at hb0 ⊢
    refine ⟨⟨⟨⟨hb0.1.1.1.1, fun s hs => ?_⟩, hb0.1.1.2⟩, hb0.1.2⟩, hb0.2⟩
    have hs0 := hb0.1.1.1.2 s hs
    simp only [progStmtOkWithIntrinsics, progStmtOkWithIntrinsicsB3, Bool.or_eq_true] at hs0 ⊢
    rcases hs0 with hs1 | hs2
    · exact .inl hs1
    · right
      obtain ⟨kind, span⟩ := s
      cases kind with
      | retag rk pl =>
        cases rk <;> try simp at hs2
        rcases pl with ⟨i, projs⟩
        cases projs with
        | cons _ _ => simp at hs2
        | nil =>
          simp only [Bool.and_eq_true] at hs2 ⊢
          cases hd : b.localDecls[i]? with
          | none => simp [hd] at hs2
          | some d =>
            simp only [hd, decide_eq_true_eq] at hs2 ⊢
            exact ⟨⟨⟨hs2.1.1.1, hs2.1.1.2⟩, hs2.1.2⟩, isDeclPtrLocal_of_isRefTy hd hs2.2⟩
      | _ => simp at hs2

theorem progInFragmentWithIntrinsics_imp_B3 {entry : CapturedMir} {callees : List CapturedMir}
    (h : progInFragmentWithIntrinsics entry callees = true) :
    progInFragmentWithIntrinsicsB3 entry callees = true :=
  progCrossFrameTranslatable_imp_B3 (progInFragmentWithIntrinsics_implies_progCrossFrameTranslatable h)

theorem exposeTwice_B3_divergence :
    progInFragmentWithIntrinsicsB3 exposeTwice [] = true ∧
    progInFragmentWithIntrinsics exposeTwice [] = false ∧
    (∃ mem, ReachesRet (mirTree exposeTwice (initMachineState exposeTwice [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨0, 4⟩, mem))) ∧
    retAfterIntr exposeTwice [.scalar ⟨5, 4⟩] 13 =
      some (some { retAlloc with data := scalarBytes u32 0 }, [1]) ∧
    retAfterIntrTB exposeTwice [.scalar ⟨5, 4⟩] 13 = tbRetU32 0 :=
  ⟨by decide +kernel, by decide +kernel, exposeTwice_three_way_divergence⟩

theorem int2ptrForgedTag_B3_divergence :
    progInFragmentWithIntrinsicsB3 int2ptrForgedTag [] = true ∧
    progInFragmentWithIntrinsics int2ptrForgedTag [] = false ∧
    (∃ tr u, Reaches (mirTree int2ptrForgedTag
      (initMachineState int2ptrForgedTag [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
    stopAfterIntr int2ptrForgedTag [.scalar ⟨5, 4⟩] 6 =
      some (.ub "dereferencing pointer without provenance") ∧
    stopAfterIntrTB int2ptrForgedTag [.scalar ⟨5, 4⟩] 6 =
      some (.ub "dereferencing pointer without provenance") :=
  ⟨by decide +kernel, by decide +kernel,
   int2ptrForgedTag_anneal_ub, int2ptrForgedTag_minirust_direct, int2ptrForgedTag_tb_direct⟩

/-- `childReborrowWriteDisablesParent` under the B3 and unified fragments. Before
unstable `b076d6a3` this was a divergence (Anneal's flat borrow list faulted on
the parent read while `BasicMemory` and Tree Borrows returned `9`); with
parent-linked Tree Borrows entries and ancestor-tracking `stepReborrow`, the
program is accepted by both B3 and `progInFragmentWithIntrinsics`, and all three
semantics return `9`. -/
theorem childReborrowWriteDisablesParent_B3_divergence :
    progInFragmentWithIntrinsicsB3 childReborrowWriteDisablesParent [] = true ∧
    progInFragmentWithIntrinsics childReborrowWriteDisablesParent [] = true ∧
    ReachesRet (mirTree childReborrowWriteDisablesParent
      (initMachineState childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨9, 4⟩,
        { (initMachineState childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩]).memory with
          borrows := [{ rawPtrEntry 2 .mut (local_ 1) with perm := .frozen, parentTag := some 1 },
                      rawPtrEntry 1 .mut (local_ 1)],
          nextTag := 3 })) ∧
    retAfter childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩] 8 =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) ∧
    retAfterTB childReborrowWriteDisablesParent [.scalar ⟨5, 4⟩] 8 = tbRetU32 9 :=
  ⟨by decide +kernel, by decide +kernel,
   childReborrowWriteDisablesParent_anneal_ret,
   childReborrowWriteDisablesParent_minirust_direct,
   childReborrowWriteDisablesParent_tb_direct⟩

theorem exposeSharedRefWriteUb_B3_divergence :
    progInFragmentWithIntrinsicsB3 exposeSharedRefWriteUb [] = true ∧
    progInFragmentWithIntrinsics exposeSharedRefWriteUb [] = false ∧
    (∃ tr u, Reaches (mirTree exposeSharedRefWriteUb
      (initMachineState exposeSharedRefWriteUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
    retAfterIntr exposeSharedRefWriteUb [.scalar ⟨5, 4⟩] 12 =
      some (some { retAlloc with data := scalarBytes u32 88 }, [1]) :=
  ⟨by decide +kernel, by decide +kernel,
   exposeSharedRefWriteUb_anneal_ub, exposeSharedRefWriteUb_minirust_direct⟩

/-- Callee `fn raw_ptr_retag_fn_entry(p: *mut u32) -> u32`: runs
`Retag([fn entry], _1)` on a raw pointer parameter and cycles a fresh scalar
temporary `_2` (`StorageLive(2); _2 = 7; _0 = _2; StorageDead(2)`). -/
def calleeRawPtrRetagFnEntryMir : CapturedMir where
  defPath := "witness::raw_ptr_retag_fn_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, ptrMutU32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.retag .fnEntry (local_ 1)),
        mkStmt (.assign (local_ 2) (.use (constU32 7))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 2)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller `fn caller_raw_ptr_retag_fn_entry(a: u32, mut b: u32) -> u32`:
passes `_3 = &raw mut _2` (`targetLocal = 2`) to `raw_ptr_retag_fn_entry`. In
Anneal, `Retag(FnEntry, _1)` attaches a strong borrow protector to `tag 1`
(`targetLocal = 2`), causing `StorageDead(2)` inside `callee` to fault with UB
without ever dereferencing `p`, whereas `Validate(_1, true)` on `PtrType::Raw`
is a no-op in both `Mach` and `MachTB` (both return `7`). -/
def callerRawPtrRetagFnEntryMir : CapturedMir where
  defPath := "witness::caller_raw_ptr_retag_fn_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32Decl, ptrMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.rawPtr .mut (local_ 2)))],
      terminator := mkTerm (.call (fnDefOp "witness::raw_ptr_retag_fn_entry")
        [.move (local_ 3)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

def ctxCallRawRetag2 : Ctx :=
  ctxWithFns callerFrame retAlloc 2 [128, 192, 256]

def callerRawPtrRetagFnEntryProg : Gen.Program :=
  (translateProgWithIntrinsics callerRawPtrRetagFnEntryMir [calleeRawPtrRetagFnEntryMir]).getD
    callRefMutProtectedProg

def callerRawPtrRetagFnEntryMInit : Mach :=
  match callerRawPtrRetagFnEntryProg.functions.entries[0]? with
  | some (_, callerFn) =>
    multiMachineWithCtx ctxCallRawRetag2 callerRawPtrRetagFnEntryProg 2
      callerRawPtrRetagFnEntryMir callerFn
      [.uninit, .init (.scalar ⟨5, 4⟩), .init (.scalar ⟨9, 4⟩)] callerFn.start
  | none => callRefMutProtectedMInit

def callerRawPtrRetagFnEntryTBInit : MachTB :=
  liftMachToTB callerRawPtrRetagFnEntryMInit

theorem callerRawPtrRetagFnEntry_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees callerRawPtrRetagFnEntryMir [.scalar ⟨5, 4⟩, .scalar ⟨9, 4⟩]
        [calleeRawPtrRetagFnEntryMir])
      tr u ∧ FaultNow u :=
  faultsA_sound callerRawPtrRetagFnEntryMir 25 _ (by decide)

theorem callerRawPtrRetagFnEntry_B3_divergence :
    progInFragmentWithIntrinsicsB3 callerRawPtrRetagFnEntryMir [calleeRawPtrRetagFnEntryMir] = true ∧
    progCrossFrameTranslatable callerRawPtrRetagFnEntryMir [calleeRawPtrRetagFnEntryMir] = false ∧
    progInFragmentWithIntrinsics callerRawPtrRetagFnEntryMir [calleeRawPtrRetagFnEntryMir] = false ∧
    (∃ tr u, Reaches
      (mirCallTreeWithCallees callerRawPtrRetagFnEntryMir [.scalar ⟨5, 4⟩, .scalar ⟨9, 4⟩]
        [calleeRawPtrRetagFnEntryMir])
      tr u ∧ FaultNow u) ∧
    (Interp.steps 13 callerRawPtrRetagFnEntryMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 7 }, [1]) ∧
    (Interp.stepsTB 13 callerRawPtrRetagFnEntryTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
   callerRawPtrRetagFnEntry_anneal_ub, by decide +kernel, by decide +kernel⟩

/-- Callee `fn read_ref_with_local(dummy: u32, r: &mut u32) -> u32`: `_1` is a
scalar `u32` parameter (`dummy = 100`) and `_2` is `r : &mut u32`. When `caller`
borrows its own `_1` (`x = 5`), `r`'s `BorrowEntry` carries un-namespaced
`targetLocal = 1`; dereferencing `*_2` inside `callee` reads `callee.frame.locals[1]`
(`100`) instead of `caller.frame.locals[1]` (`5`), so Anneal succeeds with
`MirNoUBTree` and **silently returns `137` (`100 + 37`)** while `Mach` and
`MachTB` return `42` (`5 + 37`). -/
def calleeReadRefWithLocalMir : CapturedMir where
  defPath := "witness::read_ref_with_local"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, refMutU32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.retag .fnEntry (local_ 2)),
        mkStmt (.assign (local_ 3) (.use (.copy (derefPlace 2)))),
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 3)) (constU32 37))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

def callerRefMutSilentWrongLocalMir : CapturedMir where
  defPath := "witness::call_ref_mut_silent_wrong_local"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, refMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1)))],
      terminator := mkTerm (.call (fnDefOp "witness::read_ref_with_local")
        [constU32 100, .move (local_ 2)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

def callerRefMutSilentWrongLocalProg : Gen.Program :=
  (translateProgWithIntrinsics callerRefMutSilentWrongLocalMir [calleeReadRefWithLocalMir]).getD
    callRefMutProtectedProg

def callerRefMutSilentWrongLocalMInit : Mach :=
  match callerRefMutSilentWrongLocalProg.functions.entries[0]? with
  | some (_, callerFn) =>
    multiMachineWithCtx ctxCallRefMut1 callerRefMutSilentWrongLocalProg 2
      callerRefMutSilentWrongLocalMir callerFn [.uninit, .init (.scalar ⟨5, 4⟩)] callerFn.start
  | none => callRefMutProtectedMInit

def callerRefMutSilentWrongLocalTBInit : MachTB :=
  liftMachToTB callerRefMutSilentWrongLocalMInit

theorem callerRefMutSilentWrongLocal_anneal_137 :
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerRefMutSilentWrongLocalMir [.scalar ⟨5, 4⟩]
        [calleeReadRefWithLocalMir])
      tr (.normal (.scalar ⟨137, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerRefMutSilentWrongLocalMir [.scalar ⟨5, 4⟩]
        [calleeReadRefWithLocalMir]) :=
  runsToScalar_sound (fuel := 25) (by decide)

theorem callerRefMutSilentWrongLocal_divergence :
    progInFragmentWithIntrinsicsB3 callerRefMutSilentWrongLocalMir [calleeReadRefWithLocalMir] = true ∧
    progCrossFrameTranslatable callerRefMutSilentWrongLocalMir [calleeReadRefWithLocalMir] = true ∧
    progInFragmentWithIntrinsics callerRefMutSilentWrongLocalMir [calleeReadRefWithLocalMir] = false ∧
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerRefMutSilentWrongLocalMir [.scalar ⟨5, 4⟩]
        [calleeReadRefWithLocalMir])
      tr (.normal (.scalar ⟨137, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerRefMutSilentWrongLocalMir [.scalar ⟨5, 4⟩]
        [calleeReadRefWithLocalMir]) ∧
    (Interp.steps 13 callerRefMutSilentWrongLocalMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (Interp.stepsTB 13 callerRefMutSilentWrongLocalTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 42 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
   callerRefMutSilentWrongLocal_anneal_137.1,
   callerRefMutSilentWrongLocal_anneal_137.2,
   by decide +kernel, by decide +kernel⟩

/-- Scalar-only callee `fn scalar_assign_local1(mut y: u32) -> u32`: assigns its
own scalar parameter `_1 = _1 + 36` and returns `_1`. In Anneal, `_1 = ...` runs
`invalidateConflictingBorrows mem₁.borrows 1 .none` on the shared `borrows`
table, disabling any active caller borrow with `targetLocal = 1`! -/
def calleeScalarAssignLocal1Mir : CapturedMir where
  defPath := "witness::scalar_assign_local1"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.binaryOp .add (.copy (local_ 1)) (constU32 36))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller `fn caller_borrow_across_scalar_call(mut x: u32) -> u32`: creates
`_2 = &raw mut _1` before a purely scalar call `scalar_assign_local1(1) -> _3`,
then writes `*_2 = _3 + 5` after `Return`. Both bodies individually satisfy
`ptrAliasingOk = true`, yet `ptrAliasingProgOk callerBorrowAcrossScalarCallMir = false`
because `ptrTermStep` disables `_2` across the returning `Call`. -/
def callerBorrowAcrossScalarCallMir : CapturedMir where
  defPath := "witness::caller_borrow_across_scalar_call"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, ptrMutU32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1)))],
      terminator := mkTerm (.call (fnDefOp "witness::scalar_assign_local1")
        [constU32 1] (local_ 3) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (derefPlace 2) (.binaryOp .add (.copy (local_ 3)) (constU32 5))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

def callerBorrowAcrossScalarCallProg : Gen.Program :=
  (translateProgWithIntrinsics callerBorrowAcrossScalarCallMir [calleeScalarAssignLocal1Mir]).getD
    callRefMutProtectedProg

def callerBorrowAcrossScalarCallMInit : Mach :=
  match callerBorrowAcrossScalarCallProg.functions.entries[0]? with
  | some (_, callerFn) =>
    multiMachineWithCtx ctxCallRefMut1 callerBorrowAcrossScalarCallProg 2
      callerBorrowAcrossScalarCallMir callerFn [.uninit, .init (.scalar ⟨5, 4⟩)] callerFn.start
  | none => callRefMutProtectedMInit

def callerBorrowAcrossScalarCallTBInit : MachTB :=
  liftMachToTB callerBorrowAcrossScalarCallMInit

theorem callerBorrowAcrossScalarCall_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees callerBorrowAcrossScalarCallMir [.scalar ⟨5, 4⟩]
        [calleeScalarAssignLocal1Mir])
      tr u ∧ FaultNow u :=
  faultsA_sound callerBorrowAcrossScalarCallMir 25 _ (by decide)

theorem callerBorrowAcrossScalarCall_divergence :
    ptrAliasingOk callerBorrowAcrossScalarCallMir = true ∧
    ptrAliasingOk calleeScalarAssignLocal1Mir = true ∧
    ptrAliasingProgOk callerBorrowAcrossScalarCallMir = false ∧
    progInFragmentWithIntrinsicsB3 callerBorrowAcrossScalarCallMir [calleeScalarAssignLocal1Mir] = true ∧
    progInFragmentWithIntrinsics callerBorrowAcrossScalarCallMir [calleeScalarAssignLocal1Mir] = false ∧
    (∃ tr u, Reaches
      (mirCallTreeWithCallees callerBorrowAcrossScalarCallMir [.scalar ⟨5, 4⟩]
        [calleeScalarAssignLocal1Mir])
      tr u ∧ FaultNow u) ∧
    (Interp.steps 14 callerBorrowAcrossScalarCallMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (Interp.stepsTB 14 callerBorrowAcrossScalarCallTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 42 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel,
   callerBorrowAcrossScalarCall_anneal_ub,
   by decide +kernel, by decide +kernel⟩

/-- Positive sound unified multi-function callee `fn borrow_assume_add(mut y: u32) -> u32`:
uses `Assume(true)`, `&mut _1`, `Retag`, `&raw mut (*_2)`,
`PointerExposeProvenance`, and `PointerWithExposedProvenance` to compute `y + 37`. -/
def calleeBorrowAssumeAddMir : CapturedMir where
  defPath := "witness::borrow_assume_add"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, usizeDecl, ptrMutU32Decl,
    u32Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.storageLive 4),
        mkStmt (.storageLive 5),
        mkStmt (.storageLive 6),
        mkStmt (.storageLive 7),
        mkStmt (.assign (local_ 7) (.use (constBool true))),
        mkStmt (.intrinsic (.assume (.copy (local_ 7)))),
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
        mkStmt (.retag .default (local_ 2)),
        mkStmt (.assign (local_ 3) (.rawPtr .mut (derefPlace 2))),
        mkStmt (.assign (local_ 4) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy)),
        mkStmt (.assign (local_ 5)
          (.cast .pointerWithExposedProvenance (.copy (local_ 4)) ptrMutU32Ty)),
        mkStmt (.assign (local_ 6) (.use (.copy (derefPlace 5)))),
        mkStmt (.assign (derefPlace 5) (.binaryOp .add (.copy (local_ 6)) (constU32 37))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 7),
        mkStmt (.storageDead 6),
        mkStmt (.storageDead 5),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Positive sound unified multi-function caller
`fn call_borrow_expose_and_scalar(mut x: u32) -> u32`: calls
`borrow_assume_add(copy _1) -> _2`, then borrows `&mut _1`, reborrows
`&raw mut (*_3)`, round-trips through `PointerExposeProvenance` and
`PointerWithExposedProvenance`, writes `_2 + 50` (`92`), and returns `_1`. -/
def callerBorrowExposeAndScalarCallMir : CapturedMir where
  defPath := "witness::call_borrow_expose_and_scalar"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, usizeDecl, ptrMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2)],
      terminator := mkTerm (.call (fnDefOp "witness::borrow_assume_add")
        [.copy (local_ 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.storageLive 4),
        mkStmt (.storageLive 5),
        mkStmt (.storageLive 6),
        mkStmt (.assign (local_ 3) (.ref (.mut false) (local_ 1))),
        mkStmt (.retag .default (local_ 3)),
        mkStmt (.assign (local_ 4) (.rawPtr .mut (derefPlace 3))),
        mkStmt (.assign (local_ 5) (.cast .pointerExposeProvenance (.copy (local_ 4)) usizeTy)),
        mkStmt (.assign (local_ 6)
          (.cast .pointerWithExposedProvenance (.copy (local_ 5)) ptrMutU32Ty)),
        mkStmt (.assign (derefPlace 6) (.binaryOp .add (.copy (local_ 2)) (constU32 50))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 6),
        mkStmt (.storageDead 5),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

def callerBorrowExposeAndScalarCallProg : Gen.Program :=
  (translateProgWithIntrinsics callerBorrowExposeAndScalarCallMir [calleeBorrowAssumeAddMir]).getD
    callRefMutProtectedProg

def callerBorrowExposeAndScalarCallMInit : Mach :=
  match callerBorrowExposeAndScalarCallProg.functions.entries[0]? with
  | some (_, callerFn) =>
    multiMachineWithCtx ctxCallRefMut1 callerBorrowExposeAndScalarCallProg 2
      callerBorrowExposeAndScalarCallMir callerFn [.uninit, .init (.scalar ⟨5, 4⟩)] callerFn.start
  | none => callRefMutProtectedMInit

def callerBorrowExposeAndScalarCallTBInit : MachTB :=
  liftMachToTB callerBorrowExposeAndScalarCallMInit

theorem callerBorrowExposeAndScalarCall_anneal_92 :
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerBorrowExposeAndScalarCallMir [.scalar ⟨5, 4⟩]
        [calleeBorrowAssumeAddMir])
      tr (.normal (.scalar ⟨92, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerBorrowExposeAndScalarCallMir [.scalar ⟨5, 4⟩]
        [calleeBorrowAssumeAddMir]) :=
  runsToScalar_sound (fuel := 80) (by decide)

theorem callerBorrowExposeAndScalarCall_three_way :
    progInFragment callerBorrowExposeAndScalarCallMir [calleeBorrowAssumeAddMir] = false ∧
    progInFragmentWithIntrinsics callerBorrowExposeAndScalarCallMir [calleeBorrowAssumeAddMir] = true ∧
    (translateProgWithIntrinsics callerBorrowExposeAndScalarCallMir
      [calleeBorrowAssumeAddMir]).isSome = true ∧
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerBorrowExposeAndScalarCallMir [.scalar ⟨5, 4⟩]
        [calleeBorrowAssumeAddMir])
      tr (.normal (.scalar ⟨92, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerBorrowExposeAndScalarCallMir [.scalar ⟨5, 4⟩]
        [calleeBorrowAssumeAddMir]) ∧
    (Interp.steps 44 callerBorrowExposeAndScalarCallMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 92 }, [1]) ∧
    (Interp.stepsTB 44 callerBorrowExposeAndScalarCallTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 92 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
   callerBorrowExposeAndScalarCall_anneal_92.1,
   callerBorrowExposeAndScalarCall_anneal_92.2,
   by decide +kernel, by decide +kernel⟩

/-! ## 12. Pass A3 critique & multi-function Tree Borrows exposure discipline (MR-4.3 Pass B4)

Pass A3 unified `progInFragmentWithIntrinsics` by checking `provCastFlowOk` and
`ptrAliasingProgOk (provCastAliasView body)` on every function, where
`ptrTermStep` disables all pre-call caller borrows across a returning scalar
`Call`. Because `ptrTermStep` forces a caller that wants to mutate a local `_1`
through a borrow both before and after a scalar `Call` to create a **fresh**
borrow (`&mut _1` + `Retag`) after `Return`, any caller that exposes its
pre-call borrow via `PointerExposeProvenance` and then exposes its post-call
fresh borrow via `PointerExposeProvenance` + `PointerWithExposedProvenance`
satisfies `progInFragmentWithIntrinsics = true` (`provCastFlowOk = true` and
`ptrAliasingProgOk = true`) and succeeds on both Anneal and MiniRust
`BasicMemory` (`Mach`), yet halts with `Stop.unsupported` on MiniRust
`TreeBorrowsMemory` (`MachTB`) because the caller's stack allocation `AllocId(1)`
remains live across the call and accumulates two distinct exposed Tree Borrows
tags `(AllocId(1), path₁)` and `(AllocId(1), path₂)`!

By contrast, when each function in the program satisfies `singleExposeSiteOk`
(`progSingleExposeSiteOk entry callees = true`, as in
`callerBorrowExposeAndScalarCallMir` + `calleeBorrowAssumeAddMir` where the first
exposure is inside the callee and the second is in the caller), the callee's
stack allocation is deallocated on `Return` (`a.live = false`), so `MachTB`'s
live-allocation candidate filter `tbmExposedInBounds` sees only the caller's own
exposed tag and succeeds (`tbRetU32 92`). -/

/-- `callerBorrowExposeAndScalarCallMir` and `calleeBorrowAssumeAddMir` satisfy
the program-level single-expose-site discipline `progSingleExposeSiteOk = true`
(one acyclic exposure site in the callee, whose stack allocation is deallocated
on `Return`, and one acyclic exposure site in the caller). -/
theorem callerBorrowExposeAndScalarCall_progSingleExposeSiteOk :
    progSingleExposeSiteOk callerBorrowExposeAndScalarCallMir [calleeBorrowAssumeAddMir] = true := by
  decide +kernel

/-- Multi-function caller `fn caller_pre_post_call_expose(mut x: u32) -> u32`:
before calling `scalar_assign_local1(1) -> _6`, borrows `_2 = &mut _1`, retags
`_2`, takes `_3 = &raw mut (*_2)`, round-trips through `PointerExposeProvenance`
(`_4`) and `PointerWithExposedProvenance` (`_5`), and writes `*_5 = 10`.
Because `ptrTermStep` disables pre-call borrows across the returning `Call`, the
continuation block `bb1` creates a fresh borrow `_7 = &mut _1`, retags `_7`,
takes `_8 = &raw mut (*_7)`, round-trips through `PointerExposeProvenance`
(`_9`) and `PointerWithExposedProvenance` (`_10`), writes `*_10 = _6 + 5` (`42`),
and returns `_1`. -/
def callerPrePostCallExposeMir : CapturedMir where
  defPath := "witness::caller_pre_post_call_expose"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, usizeDecl, ptrMutU32Decl,
    u32Decl, refMutU32Decl, ptrMutU32Decl, usizeDecl, ptrMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.storageLive 4),
        mkStmt (.storageLive 5),
        mkStmt (.storageLive 6),
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
        mkStmt (.retag .default (local_ 2)),
        mkStmt (.assign (local_ 3) (.rawPtr .mut (derefPlace 2))),
        mkStmt (.assign (local_ 4) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy)),
        mkStmt (.assign (local_ 5)
          (.cast .pointerWithExposedProvenance (.copy (local_ 4)) ptrMutU32Ty)),
        mkStmt (.assign (derefPlace 5) (.use (constU32 10)))],
      terminator := mkTerm (.call (fnDefOp "witness::scalar_assign_local1")
        [constU32 1] (local_ 6) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 7),
        mkStmt (.storageLive 8),
        mkStmt (.storageLive 9),
        mkStmt (.storageLive 10),
        mkStmt (.assign (local_ 7) (.ref (.mut false) (local_ 1))),
        mkStmt (.retag .default (local_ 7)),
        mkStmt (.assign (local_ 8) (.rawPtr .mut (derefPlace 7))),
        mkStmt (.assign (local_ 9) (.cast .pointerExposeProvenance (.copy (local_ 8)) usizeTy)),
        mkStmt (.assign (local_ 10)
          (.cast .pointerWithExposedProvenance (.copy (local_ 9)) ptrMutU32Ty)),
        mkStmt (.assign (derefPlace 10) (.binaryOp .add (.copy (local_ 6)) (constU32 5))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 10),
        mkStmt (.storageDead 9),
        mkStmt (.storageDead 8),
        mkStmt (.storageDead 7),
        mkStmt (.storageDead 6),
        mkStmt (.storageDead 5),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

def callerPrePostCallExposeProg : Gen.Program :=
  (translateProgWithIntrinsics callerPrePostCallExposeMir [calleeScalarAssignLocal1Mir]).getD
    callRefMutProtectedProg

def callerPrePostCallExposeMInit : Mach :=
  match callerPrePostCallExposeProg.functions.entries[0]? with
  | some (_, callerFn) =>
    multiMachineWithCtx ctxCallRefMut1 callerPrePostCallExposeProg 2
      callerPrePostCallExposeMir callerFn [.uninit, .init (.scalar ⟨5, 4⟩)] callerFn.start
  | none => callRefMutProtectedMInit

def callerPrePostCallExposeTBInit : MachTB :=
  liftMachToTB callerPrePostCallExposeMInit

theorem callerPrePostCallExpose_anneal_42 :
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerPrePostCallExposeMir [.scalar ⟨5, 4⟩]
        [calleeScalarAssignLocal1Mir])
      tr (.normal (.scalar ⟨42, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerPrePostCallExposeMir [.scalar ⟨5, 4⟩]
        [calleeScalarAssignLocal1Mir]) :=
  runsToScalar_sound (fuel := 60) (by decide)

/-- Pass B4 multi-function Tree Borrows exposure divergence:
`callerPrePostCallExposeMir` + `calleeScalarAssignLocal1Mir` is accepted by
`progInFragmentWithIntrinsics` (`true`) but rejected by
`progSingleExposeSiteOk` (`false`); Anneal and MiniRust `Mach` (`BasicMemory`)
both succeed and return `42` (`MirNoUBTree`), whereas MiniRust `MachTB`
(`TreeBorrowsMemory`) halts at the post-call `PointerWithExposedProvenance`
with `Stop.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)"`
because the pre-call and post-call `Retag`s expose two distinct tags on the
same live caller stack allocation `AllocId(1)`. -/
theorem callerPrePostCallExpose_three_way_divergence :
    progInFragmentWithIntrinsics callerPrePostCallExposeMir [calleeScalarAssignLocal1Mir] = true ∧
    progSingleExposeSiteOk callerPrePostCallExposeMir [calleeScalarAssignLocal1Mir] = false ∧
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerPrePostCallExposeMir [.scalar ⟨5, 4⟩]
        [calleeScalarAssignLocal1Mir])
      tr (.normal (.scalar ⟨42, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerPrePostCallExposeMir [.scalar ⟨5, 4⟩]
        [calleeScalarAssignLocal1Mir]) ∧
    (Interp.steps 38 callerPrePostCallExposeMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    stopStepsTB 38 callerPrePostCallExposeTBInit =
      some (.unsupported
        "int2ptr: several exposed allocations meet at the address (angelic choice)") :=
  ⟨by decide +kernel, by decide +kernel,
   callerPrePostCallExpose_anneal_42.1,
   callerPrePostCallExpose_anneal_42.2,
   by decide +kernel, by decide +kernel⟩

/-! ## 13. Cyclic loop multi-call callee stack-reuse 3-way witness (MR-4.3 Pass A4)

Whereas §12 showed that exposing twice in the **same** live caller frame
(`callerPrePostCallExposeMir`, rejected by `progSingleExposeSiteOk`) causes
`MachTB` to halt with `Stop.unsupported` due to two live exposed tags on
`AllocId(1)`, `progSingleExposeSiteOk` admits a cyclic `SwitchInt` loop caller
(`isAcyclicCfg = false`, `hasProvCast = false`) that invokes an acyclic exposing
callee (`calleeBorrowAssumeAddMir`, `singleExposeSiteOk = true`) multiple times!

Across two loop iterations (`x = 5 -> 42 -> 79`), both `Mach` (`BM.pickAddr`)
and `MachTB` (`TBM.pickAddr`) allocate the callee's borrowed parameter slot `_1`
at the **exact same first-fit stack address `5 * 2 ^ 32` (`21474836480`)**,
appending two distinct exposed provenances at `5 * 2 ^ 32` to
`m.intptrcast.exposed`. Because the first call's stack allocation is deallocated
on `Return` (`a.live = false`), `int2ptr` filters out the dead first-call
allocation during the second call's `PointerWithExposedProvenance`, uniquely
selecting the second call's live allocation and active Tree Borrows tag and
achieving 3-way agreement (`79` + `MirNoUBTree`) across Anneal, `Mach`, and
`MachTB`. -/

/-- Looping caller `fn loop_call_expose_callee(x: u32) -> u32`:
has a cyclic `SwitchInt` loop (`isAcyclicCfg = false`) calling
`borrow_assume_add` twice (`5 -> 42 -> 79`) using distinct temporary `_4` for
the `Call` destination. -/
def callerLoopCallExposeCalleeMir : CapturedMir where
  defPath := "witness::loop_call_expose_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 2) (.use (constU32 2))),
        mkStmt (.assign (local_ 3) (.use (.copy (local_ 1))))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 2)) { branches := [(0, 4)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2) (.binaryOp .sub (.copy (local_ 2)) (constU32 1))),
        mkStmt (.storageLive 4)],
      terminator := mkTerm (.call (fnDefOp "witness::borrow_assume_add")
        [.copy (local_ 3)] (local_ 4) (some 3) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.use (.copy (local_ 4)))),
        mkStmt (.storageDead 4)],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 3)))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

def callerLoopCallExposeCalleeProg : Gen.Program :=
  (translateProgWithIntrinsics callerLoopCallExposeCalleeMir [calleeBorrowAssumeAddMir]).getD
    callRefMutProtectedProg

def callerLoopCallExposeCalleeMInit : Mach :=
  match callerLoopCallExposeCalleeProg.functions.entries[0]? with
  | some (_, callerFn) =>
    multiMachineWithCtx ctxCallRefMut1 callerLoopCallExposeCalleeProg 2
      callerLoopCallExposeCalleeMir callerFn [.uninit, .init (.scalar ⟨5, 4⟩)] callerFn.start
  | none => callRefMutProtectedMInit

def callerLoopCallExposeCalleeTBInit : MachTB :=
  liftMachToTB callerLoopCallExposeCalleeMInit

theorem callerLoopCallExposeCallee_anneal_79 :
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerLoopCallExposeCalleeMir [.scalar ⟨5, 4⟩]
        [calleeBorrowAssumeAddMir])
      tr (.normal (.scalar ⟨79, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerLoopCallExposeCalleeMir [.scalar ⟨5, 4⟩]
        [calleeBorrowAssumeAddMir]) :=
  runsToScalar_sound (fuel := 120) (by decide)

/-- Positive 3-way cyclic-loop multi-call stack-reuse witness (MR-4.3 Pass A4):
`callerLoopCallExposeCalleeMir` (`isAcyclicCfg = false`) calling
`calleeBorrowAssumeAddMir` satisfies both `progInFragmentWithIntrinsics = true`
and `progSingleExposeSiteOk = true`, returns `79` (`MirNoUBTree`) on Anneal, and
returns `79` in 73 steps on both MiniRust `Mach` (`BasicMemory`) and `MachTB`
(`TreeBorrowsMemory`) while accumulating two distinct exposed provenances at the
exact same reused first-fit callee stack address `5 * 2 ^ 32` (`21474836480`),
both deallocated (`live = false`) on `Return`. -/
theorem callerLoopCallExposeCallee_three_way :
    isAcyclicCfg callerLoopCallExposeCalleeMir = false ∧
    progInFragmentWithIntrinsics callerLoopCallExposeCalleeMir [calleeBorrowAssumeAddMir] = true ∧
    progSingleExposeSiteOk callerLoopCallExposeCalleeMir [calleeBorrowAssumeAddMir] = true ∧
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees callerLoopCallExposeCalleeMir [.scalar ⟨5, 4⟩]
        [calleeBorrowAssumeAddMir])
      tr (.normal (.scalar ⟨79, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees callerLoopCallExposeCalleeMir [.scalar ⟨5, 4⟩]
        [calleeBorrowAssumeAddMir]) ∧
    (Interp.steps 73 callerLoopCallExposeCalleeMInit).toOption.map
        (fun m =>
          (m.mem.memory.allocations[0]?,
           m.threads.map (·.stack.length),
           m.intptrcast.exposed.elems.map (fun (aid, _) =>
             m.mem.memory.allocations[aid.1.toNat]?.map
               (fun a => (Gen.Allocation.addr a, Gen.Allocation.live a))))) =
      some (some { retAlloc with data := scalarBytes u32 79 }, [1],
        [some (21474836480, false), some (21474836480, false)]) ∧
    (Interp.stepsTB 73 callerLoopCallExposeCalleeTBInit).toOption.map
        (fun m =>
          (({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
              stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome),
           m.intptrcast.exposed.elems.map (fun (aid, _) =>
             m.mem.memory.mem.allocations[aid.1.toNat]?.map
               (fun a => (Gen.Allocation.addr a, Gen.Allocation.live a))))) =
      (tbRetU32 79).map (·, [some (21474836480, false), some (21474836480, false)]) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
   callerLoopCallExposeCallee_anneal_79.1,
   callerLoopCallExposeCallee_anneal_79.2,
   by decide +kernel, by decide +kernel⟩

end MiniRustSpec.Correspondence.ProvenanceWitness
