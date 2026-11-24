-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Init.Data.Option.Basic
import Anneal.Firewall
import Anneal.RefFrame.RangedTree
import Anneal.ParametricCore.LoopInv
import Anneal.ParametricCore.StageCut
import Anneal.ParametricCore.ByteSubLens
import Anneal.ParametricCore.ByteRun

universe u v w x y z a b

namespace Anneal.ParametricCore

/-!
# 4-Way Call-Continuation, `RangedTree` Protector Frames, and Modular Unwind Stage Cuts
(`Anneal.ParametricCore.CallStackUnwind`)

This module converges `Anneal.RefFrame.Frame` (`#4167`) and
`Anneal.CallStackUnwind.SpecCut` (`#4177`) onto `Anneal.ParametricCore`,
`Anneal.RefFrame.RangedTree`, and `Anneal.Firewall`, with zero `Trusted.*`
imports, fully computable definitions, and complete kernel-checked proofs:

1. **4-Way Call-Continuation & `RangedTree` Protector Frames (`UnwindAction4`,
   `CallCont4`, `RefFrame`, `ProtectedRefFrame`):**
   - `evalRefFrameExit` commits mixed-mask `ByteRun` slices through
     `ByteSubLens.set` across all 8 `(Option Nat × UnwindAction4)` continuation
     regimes × 2 `(returned, unwound)` exits = 16 exact outcome equations
     (`refFrame_callCont4_matrix_sound`), overwriting prior pointer provenance
     and preserving `.uninitPad` runs verbatim while framing every disjoint
     `ByteSubLens`.
   - `evalProtectedRefFrameExit` runs `Anneal.RefFrame.exitFrameWithProtectors`
     before committing caller continuation on both normal return and panic
     unwind, keeping co-frame protectors active during implicit exit accesses,
     stripping `frameTags` strictly afterward, and failing closed to `.fault`
     on `.MissingTag`, `.AccessFailure` (including `.ProtectedDisabled`), or
     `.InvariantFailure`.
   - `protectedRefFrame_shared_topo3_commutation` lifts
     `Anneal.RefFrame.shared_topo3_ranged_commutation_universal` across
     `exitFrameWithProtectors` and `evalProtectedRefFrameExit`, proving that
     disjoint sibling reads (`src`, tag `1`) and protected writes (`dst`, tag
     `2`) commute to identical `(CallerContOutcome, RangedBorrowTree)` states
     with all frame protectors stripped and `src` framed.
2. **Sub-Lens Modification Framing (`UpdatesOnly`):**
   - `UpdatesOnly allowed m₀ m₁` is the reflexive-transitive closure of
     `ByteSubLens.set` steps confined to `allowed : List (ByteSubLens Addr)`.
   - Proves reflexivity, transitivity, subset monotonicity, single-lens
     containment monotonicity via `ByteSubLens.zoom_set_eq_splice`, integration
     with `copyRangeComp` / `writeRepeatRunsComp`, disjoint-lens framing
     (`updatesOnly_frame_disjoint`), and auxiliary-projection preservation
     (`updatesOnly_preserves_proj`).
3. **Modular `CallSpec`, Multi-Frame `StackFrameState`, & Zero-`Prop`-Argument
   `@[irreducible] CallSpecCut`:**
   - `CallSpec` packages normal/unwind pre/postconditions, `modifies` footprint,
     `frameTags`, and `canNormal` / `canUnwind` flags.
   - `CallSpecCut` takes only `(adapter, spec)` (zero bare `Prop` arguments),
     is sealed `@[irreducible]` after its core lemmas, and interoperates with
     `ParametricCore.StageCut` and `Anneal.Firewall.IndexedCut`.
   - Proves modular call-site WP rules (`callSpecCut_call_normal_cleanup`,
     `callSpecCut_call_normal_continue`, `callSpecCut_call_diverging_unwind`,
     `callSpecCut_unwind_propagate_chain`, `callSpecCut_frame_disjoint`) over
     arbitrary `[MirWpOps]` machines and `StackFrameState`, plus fail-closed
     rejection of diverging normal return (`onRet = none`) and `.unreachable`
     unwind.
4. **Self-Contained Kernel-Checked Canaries:** Positive and negative canaries
   exercising normal return, `.cleanup` recovery without `postRet` leakage,
   `.continue_` multi-frame unwind propagation with protector release,
   `shared_topo3` commutation through `evalProtectedRefFrameExit`,
   `.ProtectedDisabled` UB detection, `.MissingTag` failure, `onRet = none` /
   `.unreachable` fault rejection, and non-disjoint lens refutation.
-/

/-! ## Part I: 4-Way Call-Continuation & `RangedTree` Protector Frames -/

/-- 4-way MIR unwind continuation action matching `TerminatorKind.call` /
`TerminatorKind.assert` unwind edges. -/
inductive UnwindAction4 : Type where
  | cleanup (cleanupBb : Nat)
  | unreachable
  | terminate
  | continue_

/-- 4-way call-terminator continuation descriptor `(onRet, onUnwind)`. -/
structure CallCont4 where
  /-- Normal-return target basic block (`none` for diverging `-> !` calls). -/
  onRet : Option Nat
  /-- Unwind continuation action. -/
  onUnwind : UnwindAction4

/-- Callee exit payload carrying either a normal return `(retVal, mutSlice)` or
a panic unwind carrying the pre-panic partial `&mut` referent slice
`partialMutSlice`. -/
inductive CalleeExit (Val : Type w) (Byte : Type a) where
  | returned (retVal : Val) (mutSlice : List Byte)
  | unwound (partialMutSlice : List Byte)

/-- Caller-side continuation transition across all `(onRet, onUnwind)` regimes. -/
inductive CallerContOutcome (Mem : Type u) (Val : Type w) where
  | jumpNormal (targetBb : Nat) (retVal : Val) (mem : Mem)
  | jumpCleanup (cleanupBb : Nat) (mem : Mem)
  | propagateUnwind (mem : Mem)
  | abortTerminate (mem : Mem)
  | fault

/-- `&mut` borrow writeback frame pairing a `ByteSubLens` with a `CallCont4`
continuation descriptor. -/
structure RefFrame (Addr : Type v) where
  /-- Sub-allocation byte lens for the borrowed `&mut` referent. -/
  refLens : ByteSubLens Addr
  /-- Caller `(onRet, onUnwind)` continuation descriptor. -/
  cont : CallCont4

/-- Computable `RefFrame` exit transition, writing back
mixed-mask `Byte` slices through `ByteSubLens.set` across all 8
`(Option Nat × UnwindAction4)` continuation regimes. Fails closed to `.fault`
on `onRet = none` (`.returned`), `onUnwind = .unreachable` (`.unwound`), or
any rejected `ByteSubLens.set` (zero-length, length mismatch, OOB, unwritable).
-/
def evalRefFrameExit {Mem : Type u} {Addr : Type v} {Byte : Type a}
    {Val : Type w} [ops : ByteStoreOps Mem Addr Byte]
    (rf : RefFrame Addr) (mem : Mem) (exit : CalleeExit Val Byte) :
    CallerContOutcome Mem Val :=
  match exit with
  | .returned retVal mutSlice =>
    match rf.cont.onRet with
    | none => .fault
    | some retBb =>
      match rf.refLens.set mem mutSlice with
      | none => .fault
      | some mem' => .jumpNormal retBb retVal mem'
  | .unwound partialMutSlice =>
    match rf.cont.onUnwind with
    | .unreachable => .fault
    | .cleanup cleanupBb =>
      match rf.refLens.set mem partialMutSlice with
      | none => .fault
      | some mem' => .jumpCleanup cleanupBb mem'
    | .continue_ =>
      match rf.refLens.set mem partialMutSlice with
      | none => .fault
      | some mem' => .propagateUnwind mem'
    | .terminate =>
      match rf.refLens.set mem partialMutSlice with
      | none => .fault
      | some mem' => .abortTerminate mem'

section RefFrameLaws

variable {Mem : Type u} {Addr : Type v} {Byte : Type a} {Val : Type w}
  [ops : ByteStoreOps Mem Addr Byte]

/-- Fail-closed: returning normally into a diverging call site (`onRet = none`)
always yields `.fault`. -/
theorem evalRefFrameExit_fault_of_onRet_none (L : ByteSubLens Addr)
    (uAct : UnwindAction4) (mem : Mem) (retVal : Val) (bs : List Byte) :
    evalRefFrameExit ⟨L, ⟨none, uAct⟩⟩ mem (.returned retVal bs) = .fault :=
  rfl

/-- Fail-closed: unwinding into `onUnwind = .unreachable` always yields
`.fault`. -/
theorem evalRefFrameExit_fault_of_unwind_unreachable (Val : Type w)
    (L : ByteSubLens Addr) (onRet : Option Nat) (mem : Mem) (bs : List Byte) :
    evalRefFrameExit ⟨L, ⟨onRet, .unreachable⟩⟩ mem
      (CalleeExit.unwound (Val := Val) bs) = .fault :=
  rfl

/-- Fail-closed: if `rf.refLens.set mem bs = none`, a normal return yields
`.fault`. -/
theorem evalRefFrameExit_fault_of_set_none_returned (rf : RefFrame Addr)
    (mem : Mem) (retVal : Val) (bs : List Byte)
    (hNone : rf.refLens.set mem bs = none) :
    evalRefFrameExit rf mem (.returned retVal bs) = .fault := by
  unfold evalRefFrameExit
  cases rf.cont.onRet with
  | none => rfl
  | some _ => dsimp only; rw [hNone]

/-- Fail-closed: if `rf.refLens.set mem bs = none`, an unwind exit yields
`.fault`. -/
theorem evalRefFrameExit_fault_of_set_none_unwound (Val : Type w)
    (rf : RefFrame Addr) (mem : Mem) (bs : List Byte)
    (hNone : rf.refLens.set mem bs = none) :
    evalRefFrameExit rf mem (CalleeExit.unwound (Val := Val) bs) = .fault := by
  unfold evalRefFrameExit
  cases rf.cont.onUnwind with
  | unreachable => rfl
  | cleanup _ => dsimp only; rw [hNone]
  | continue_ => dsimp only; rw [hNone]
  | terminate => dsimp only; rw [hNone]

/-- Fail-closed: a zero-length `&mut` lens rejects both normal and unwind
writebacks with `.fault`. -/
theorem evalRefFrameExit_fault_of_len_zero (rf : RefFrame Addr) (mem : Mem)
    (exit : CalleeExit Val Byte) (hZero : rf.refLens.len = 0) :
    evalRefFrameExit rf mem exit = .fault := by
  cases exit with
  | returned rv bs =>
    exact evalRefFrameExit_fault_of_set_none_returned rf mem rv bs
      (ByteSubLens.set_none_of_len_zero mem bs hZero)
  | unwound bs =>
    exact evalRefFrameExit_fault_of_set_none_unwound Val rf mem bs
      (ByteSubLens.set_none_of_len_zero mem bs hZero)

/-- Fail-closed: a writeback slice whose length disagrees with `rf.refLens.len`
yields `.fault`. -/
theorem evalRefFrameExit_fault_of_length_ne (rf : RefFrame Addr) (mem : Mem)
    (exit : CalleeExit Val Byte)
    (hNe : match exit with
      | .returned _ bs => ¬ bs.length = rf.refLens.len
      | .unwound bs => ¬ bs.length = rf.refLens.len) :
    evalRefFrameExit rf mem exit = .fault := by
  cases exit with
  | returned rv bs =>
    exact evalRefFrameExit_fault_of_set_none_returned rf mem rv bs
      (ByteSubLens.set_none_of_length_ne mem hNe)
  | unwound bs =>
    exact evalRefFrameExit_fault_of_set_none_unwound Val rf mem bs
      (ByteSubLens.set_none_of_length_ne mem hNe)

/-- Complete 8-regime `(Option Nat × UnwindAction4)` × 2 `(returned, unwound)`
= 16-equation `RefFrame` continuation matrix over any lawful `ByteStoreOps`
and `ByteRunCodec`, proving exact mixed-mask `flattenByteRuns` writeback
read-back (preserving `.uninitPad` padding and overwriting prior `.initProv`
provenance) and symmetric disjoint `ByteSubLens` framing. -/
theorem refFrame_callCont4_matrix_sound [LawfulByteStoreOps Mem Addr Byte]
    {Prov : Type b} (codec : ByteRunCodec Prov Byte)
    (L : ByteSubLens Addr) (m : Mem) (old : List Byte)
    (retBb cleanupBb : Nat) (retVal : Val)
    (normalRuns partialRuns : List (ByteRun Prov))
    (hGet : L.get m = some old)
    (hNormLen : runsByteLen normalRuns = L.len)
    (hPartLen : runsByteLen partialRuns = L.len) :
    ∃ (mNorm mUnw : Mem),
      L.set m (flattenByteRuns codec normalRuns) = some mNorm ∧
      L.get mNorm = some (flattenByteRuns codec normalRuns) ∧
      L.set m (flattenByteRuns codec partialRuns) = some mUnw ∧
      L.get mUnw = some (flattenByteRuns codec partialRuns) ∧
      (∀ other : ByteSubLens Addr, L.Disjoint Mem other →
        other.get mNorm = other.get m ∧ other.get mUnw = other.get m) ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .cleanup cleanupBb⟩⟩ m
        (.returned retVal (flattenByteRuns codec normalRuns)) =
        .jumpNormal retBb retVal mNorm ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .cleanup cleanupBb⟩⟩ m
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        .jumpCleanup cleanupBb mUnw ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .continue_⟩⟩ m
        (.returned retVal (flattenByteRuns codec normalRuns)) =
        .jumpNormal retBb retVal mNorm ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .continue_⟩⟩ m
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        .propagateUnwind mUnw ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .unreachable⟩⟩ m
        (.returned retVal (flattenByteRuns codec normalRuns)) =
        .jumpNormal retBb retVal mNorm ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .unreachable⟩⟩ m
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) = .fault ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .terminate⟩⟩ m
        (.returned retVal (flattenByteRuns codec normalRuns)) =
        .jumpNormal retBb retVal mNorm ∧
      evalRefFrameExit ⟨L, ⟨some retBb, .terminate⟩⟩ m
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        .abortTerminate mUnw ∧
      evalRefFrameExit ⟨L, ⟨none, .cleanup cleanupBb⟩⟩ m
        (.returned retVal (flattenByteRuns codec normalRuns)) = .fault ∧
      evalRefFrameExit ⟨L, ⟨none, .cleanup cleanupBb⟩⟩ m
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        .jumpCleanup cleanupBb mUnw ∧
      evalRefFrameExit ⟨L, ⟨none, .continue_⟩⟩ m
        (.returned retVal (flattenByteRuns codec normalRuns)) = .fault ∧
      evalRefFrameExit ⟨L, ⟨none, .continue_⟩⟩ m
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        .propagateUnwind mUnw ∧
      evalRefFrameExit ⟨L, ⟨none, .unreachable⟩⟩ m
        (.returned retVal (flattenByteRuns codec normalRuns)) = .fault ∧
      evalRefFrameExit ⟨L, ⟨none, .unreachable⟩⟩ m
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) = .fault ∧
      evalRefFrameExit ⟨L, ⟨none, .terminate⟩⟩ m
        (.returned retVal (flattenByteRuns codec normalRuns)) = .fault ∧
      evalRefFrameExit ⟨L, ⟨none, .terminate⟩⟩ m
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        .abortTerminate mUnw := by
  have hLenN : (flattenByteRuns codec normalRuns).length = L.len :=
    (flattenByteRuns_length codec normalRuns).trans hNormLen
  have hLenP : (flattenByteRuns codec partialRuns).length = L.len :=
    (flattenByteRuns_length codec partialRuns).trans hPartLen
  let ⟨mNorm, hPutN⟩ := ByteSubLens.set_isSome_of_get
    (flattenByteRuns codec normalRuns) hGet hLenN
  let ⟨mUnw, hPutU⟩ := ByteSubLens.set_isSome_of_get
    (flattenByteRuns codec partialRuns) hGet hLenP
  refine ⟨mNorm, mUnw, hPutN, ByteSubLens.get_set hPutN,
    hPutU, ByteSubLens.get_set hPutU, ?_,
    ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_,
    rfl, ?_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · intro other hDisj
    exact ⟨ByteSubLens.get_set_disjoint hDisj hPutN,
      ByteSubLens.get_set_disjoint hDisj hPutU⟩
  · unfold evalRefFrameExit; dsimp only; rw [hPutN]
  · unfold evalRefFrameExit; dsimp only; rw [hPutU]
  · unfold evalRefFrameExit; dsimp only; rw [hPutN]
  · unfold evalRefFrameExit; dsimp only; rw [hPutU]
  · unfold evalRefFrameExit; dsimp only; rw [hPutN]
  · unfold evalRefFrameExit; dsimp only; rw [hPutN]
  · unfold evalRefFrameExit; dsimp only; rw [hPutU]
  · unfold evalRefFrameExit; dsimp only; rw [hPutU]
  · unfold evalRefFrameExit; dsimp only; rw [hPutU]
  · unfold evalRefFrameExit; dsimp only; rw [hPutU]

end RefFrameLaws

/-! ### Direct `Anneal.RefFrame.RangedTree` Protector-Exit Wiring -/

/-- Helper characterizing `Anneal.RefFrame.natListMem` on a `List.filter`
result. -/
theorem natListMem_filter_not_mem (t : Nat) (xs frameTags : List Nat) :
    Anneal.RefFrame.natListMem t
      (xs.filter (fun x => !Anneal.RefFrame.natListMem x frameTags)) =
    (Anneal.RefFrame.natListMem t xs &&
      !Anneal.RefFrame.natListMem t frameTags) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    have hStepMem :
        Anneal.RefFrame.natListMem t (hd :: tl) =
          (Nat.beq t hd || Anneal.RefFrame.natListMem t tl) := rfl
    rw [hStepMem]
    cases hMem : Anneal.RefFrame.natListMem hd frameTags with
    | true =>
      have hFilt :
          (hd :: tl).filter (fun x => !Anneal.RefFrame.natListMem x frameTags) =
            tl.filter (fun x => !Anneal.RefFrame.natListMem x frameTags) := by
        change (match !Anneal.RefFrame.natListMem hd frameTags with
          | true => hd :: tl.filter (fun x => !Anneal.RefFrame.natListMem x frameTags)
          | false => tl.filter (fun x => !Anneal.RefFrame.natListMem x frameTags)) = _
        rw [hMem]
        rfl
      rw [hFilt, ih]
      cases hEq : Nat.beq t hd with
      | false => rfl
      | true =>
        have hT : t = hd := Nat.eq_of_beq_eq_true hEq
        rw [hT, hMem]
        cases Anneal.RefFrame.natListMem hd tl <;> rfl
    | false =>
      have hFilt :
          (hd :: tl).filter (fun x => !Anneal.RefFrame.natListMem x frameTags) =
            hd :: tl.filter (fun x => !Anneal.RefFrame.natListMem x frameTags) := by
        change (match !Anneal.RefFrame.natListMem hd frameTags with
          | true => hd :: tl.filter (fun x => !Anneal.RefFrame.natListMem x frameTags)
          | false => tl.filter (fun x => !Anneal.RefFrame.natListMem x frameTags)) = _
        rw [hMem]
        rfl
      have hMemCons :
          Anneal.RefFrame.natListMem t
              (hd :: tl.filter (fun x => !Anneal.RefFrame.natListMem x frameTags)) =
            (Nat.beq t hd ||
              Anneal.RefFrame.natListMem t
                (tl.filter (fun x => !Anneal.RefFrame.natListMem x frameTags))) := rfl
      rw [hFilt, hMemCons, ih]
      cases hEq : Nat.beq t hd with
      | false => rfl
      | true =>
        have hT : t = hd := Nat.eq_of_beq_eq_true hEq
        rw [hT, hMem]
        rfl

/-- `endCallRemoveProtectors` strips every tag in `frameTags` from
`protectedTags`. -/
theorem endCallRemoveProtectors_strips_frameTags
    (tree : Anneal.RefFrame.RangedBorrowTree) (frameTags : List Nat) (t : Nat)
    (hIn : Anneal.RefFrame.natListMem t frameTags = true) :
    Anneal.RefFrame.natListMem t
      (Anneal.RefFrame.endCallRemoveProtectors tree frameTags).protectedTags =
    false := by
  unfold Anneal.RefFrame.endCallRemoveProtectors
  dsimp only
  rw [natListMem_filter_not_mem t tree.protectedTags frameTags, hIn]
  cases Anneal.RefFrame.natListMem t tree.protectedTags <;> rfl

/-- `endCallRemoveProtectors` preserves protection status for every tag outside
`frameTags`. -/
theorem endCallRemoveProtectors_preserves_other_tags
    (tree : Anneal.RefFrame.RangedBorrowTree) (frameTags : List Nat) (t : Nat)
    (hOut : Anneal.RefFrame.natListMem t frameTags = false) :
    Anneal.RefFrame.natListMem t
      (Anneal.RefFrame.endCallRemoveProtectors tree frameTags).protectedTags =
    Anneal.RefFrame.natListMem t tree.protectedTags := by
  unfold Anneal.RefFrame.endCallRemoveProtectors
  dsimp only
  rw [natListMem_filter_not_mem t tree.protectedTags frameTags, hOut]
  cases Anneal.RefFrame.natListMem t tree.protectedTags <;> rfl

/-- `releaseProtectorKeepProtected` never modifies `tree.protectedTags` (keeping
all co-frame protectors active during implicit exit accesses). -/
theorem releaseProtectorKeepProtected_preserves_protectedTags
    (tree : Anneal.RefFrame.RangedBorrowTree) (calleeTag : Nat) :
    (Anneal.RefFrame.releaseProtectorKeepProtected tree calleeTag).tree.protectedTags =
      tree.protectedTags := by
  unfold Anneal.RefFrame.releaseProtectorKeepProtected
  cases Anneal.RefFrame.findTopoNode calleeTag tree.topology with
  | none => rfl
  | some _ =>
    cases tree.segments with
    | nil => rfl
    | cons _ _ => rfl

private def exitFrameStepFn (a : Anneal.RefFrame.ProtectorReleaseResult)
    (tag : Nat) : Anneal.RefFrame.ProtectorReleaseResult :=
  match a.status with
  | .Released =>
    if !Anneal.RefFrame.natListMem tag a.tree.protectedTags then
      ⟨a.tree, .MissingTag tag⟩
    else
      Anneal.RefFrame.releaseProtectorKeepProtected a.tree tag
  | .MissingTag _ | .AccessFailure _ _ _ _ | .InvariantFailure _ _ _ => a

private theorem exitFrameFold_preserves_protectedTags
    (tags : List Nat) (acc : Anneal.RefFrame.ProtectorReleaseResult) :
    (tags.foldl exitFrameStepFn acc).tree.protectedTags =
      acc.tree.protectedTags := by
  induction tags generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [List.foldl]
    rw [ih]
    unfold exitFrameStepFn
    cases acc.status with
    | Released =>
      cases Anneal.RefFrame.natListMem hd acc.tree.protectedTags with
      | false => rfl
      | true => exact releaseProtectorKeepProtected_preserves_protectedTags acc.tree hd
    | MissingTag _ => rfl
    | AccessFailure _ _ _ _ => rfl
    | InvariantFailure _ _ _ => rfl

/-- When `exitFrameWithProtectors tree frameTags` succeeds (`.Released`), every
tag in `frameTags` is stripped from `protectedTags` and every tag outside
`frameTags` preserves its protection status. -/
theorem exitFrameWithProtectors_released_tags
    {tree tree' : Anneal.RefFrame.RangedBorrowTree} {frameTags : List Nat}
    (hRel : Anneal.RefFrame.exitFrameWithProtectors tree frameTags =
      ⟨tree', .Released⟩) :
    (∀ t : Nat, Anneal.RefFrame.natListMem t frameTags = true →
      Anneal.RefFrame.natListMem t tree'.protectedTags = false) ∧
    (∀ t : Nat, Anneal.RefFrame.natListMem t frameTags = false →
      Anneal.RefFrame.natListMem t tree'.protectedTags =
        Anneal.RefFrame.natListMem t tree.protectedTags) := by
  have hKeep := exitFrameFold_preserves_protectedTags frameTags ⟨tree, .Released⟩
  have hRel' :
      (let relOut := frameTags.foldl exitFrameStepFn ⟨tree, .Released⟩
       match relOut.status with
       | .Released =>
         Anneal.RefFrame.ProtectorReleaseResult.mk
           (Anneal.RefFrame.endCallRemoveProtectors relOut.tree frameTags) .Released
       | .MissingTag _ | .AccessFailure _ _ _ _ | .InvariantFailure _ _ _ =>
         relOut) = ⟨tree', .Released⟩ := hRel
  dsimp only at hRel'
  generalize hFold : frameTags.foldl exitFrameStepFn ⟨tree, .Released⟩ = relOut at hRel' hKeep
  cases relOut with
  | mk relTree relSt =>
    cases relSt with
    | Released =>
      dsimp only at hRel'
      injection hRel' with hTreeEq _
      rw [← hTreeEq]
      refine ⟨fun t hIn =>
        endCallRemoveProtectors_strips_frameTags relTree frameTags t hIn,
        fun t hOut => ?_⟩
      rw [endCallRemoveProtectors_preserves_other_tags relTree frameTags t hOut]
      exact congrArg (fun ps => Anneal.RefFrame.natListMem t ps) hKeep
    | MissingTag _ => cases hRel'
    | AccessFailure _ _ _ _ => cases hRel'
    | InvariantFailure _ _ _ => cases hRel'

private def exitFrameFinish (frameTags : List Nat)
    (relOut : Anneal.RefFrame.ProtectorReleaseResult) :
    Anneal.RefFrame.ProtectorReleaseResult :=
  match relOut.status with
  | .Released =>
    ⟨Anneal.RefFrame.endCallRemoveProtectors relOut.tree frameTags, .Released⟩
  | .MissingTag _ | .AccessFailure _ _ _ _ | .InvariantFailure _ _ _ => relOut

private theorem exitFrameWithProtectors_eq_fold
    (tree : Anneal.RefFrame.RangedBorrowTree) (frameTags : List Nat) :
    Anneal.RefFrame.exitFrameWithProtectors tree frameTags =
      exitFrameFinish frameTags
        (frameTags.foldl exitFrameStepFn ⟨tree, .Released⟩) :=
  rfl

private theorem exitFrameFold_released_all_protected
    (tags : List Nat) (acc : Anneal.RefFrame.ProtectorReleaseResult)
    (hRel : (tags.foldl exitFrameStepFn acc).status = .Released) :
    acc.status = .Released ∧
    ∀ t : Nat, Anneal.RefFrame.natListMem t tags = true →
      Anneal.RefFrame.natListMem t acc.tree.protectedTags = true := by
  induction tags generalizing acc with
  | nil => exact ⟨hRel, fun _ hIn => by cases (hIn : false = true)⟩
  | cons hd tl ih =>
    have h := ih (exitFrameStepFn acc hd) hRel
    cases acc with
    | mk tr st =>
      cases st with
      | MissingTag tg =>
        cases (h.1 : Anneal.RefFrame.ProtectorReleaseStatus.MissingTag tg = .Released)
      | AccessFailure o l tg e =>
        cases (h.1 :
          Anneal.RefFrame.ProtectorReleaseStatus.AccessFailure o l tg e = .Released)
      | InvariantFailure o l tg =>
        cases (h.1 :
          Anneal.RefFrame.ProtectorReleaseStatus.InvariantFailure o l tg = .Released)
      | Released =>
        cases hP : Anneal.RefFrame.natListMem hd tr.protectedTags with
        | false =>
          have hStep : exitFrameStepFn ⟨tr, .Released⟩ hd = ⟨tr, .MissingTag hd⟩ := by
            unfold exitFrameStepFn
            dsimp only
            rw [hP] <;> rfl
          rw [hStep] at h
          cases (h.1 :
            Anneal.RefFrame.ProtectorReleaseStatus.MissingTag hd = .Released)
        | true =>
          have hStep : exitFrameStepFn ⟨tr, .Released⟩ hd =
              Anneal.RefFrame.releaseProtectorKeepProtected tr hd := by
            unfold exitFrameStepFn
            dsimp only
            rw [hP] <;> rfl
          rw [hStep, releaseProtectorKeepProtected_preserves_protectedTags] at h
          refine ⟨rfl, fun t hIn => ?_⟩
          have hCons : Anneal.RefFrame.natListMem t (hd :: tl) =
              (Nat.beq t hd || Anneal.RefFrame.natListMem t tl) := rfl
          rw [hCons] at hIn
          cases hEq : Nat.beq t hd with
          | true =>
            rw [Nat.eq_of_beq_eq_true hEq]
            exact hP
          | false =>
            rw [hEq] at hIn
            exact h.2 t hIn

/-- Fail-closed precondition of a clean frame exit: when
`exitFrameWithProtectors tree frameTags` succeeds (`.Released`), EVERY tag in
`frameTags` was protected in the input `tree`. Contrapositively, a frame that
claims a tag it does not protect can never release cleanly. -/
theorem exitFrameWithProtectors_released_all_protected
    {tree tree' : Anneal.RefFrame.RangedBorrowTree} {frameTags : List Nat}
    (hRel : Anneal.RefFrame.exitFrameWithProtectors tree frameTags =
      ⟨tree', .Released⟩)
    (t : Nat) (hIn : Anneal.RefFrame.natListMem t frameTags = true) :
    Anneal.RefFrame.natListMem t tree.protectedTags = true := by
  have hSt : (Anneal.RefFrame.exitFrameWithProtectors tree frameTags).status =
      .Released := by
    rw [hRel]
  rw [exitFrameWithProtectors_eq_fold] at hSt
  have hFoldRel :
      (frameTags.foldl exitFrameStepFn ⟨tree, .Released⟩).status = .Released := by
    generalize frameTags.foldl exitFrameStepFn ⟨tree, .Released⟩ = relOut at hSt ⊢
    cases relOut with
    | mk relTree relSt =>
      cases relSt with
      | Released => rfl
      | MissingTag tg =>
        cases (hSt : Anneal.RefFrame.ProtectorReleaseStatus.MissingTag tg = .Released)
      | AccessFailure o l tg e =>
        cases (hSt :
          Anneal.RefFrame.ProtectorReleaseStatus.AccessFailure o l tg e = .Released)
      | InvariantFailure o l tg =>
        cases (hSt :
          Anneal.RefFrame.ProtectorReleaseStatus.InvariantFailure o l tg = .Released)
  exact (exitFrameFold_released_all_protected frameTags ⟨tree, .Released⟩
    hFoldRel).2 t hIn

/-- Fail-closed: whenever `exitFrameWithProtectors tree frameTags` does not
release cleanly (`.MissingTag`, `.AccessFailure`, or `.InvariantFailure`), the
returned tree keeps `tree.protectedTags` unchanged. A failed frame exit never
strips a protector, not even partially. -/
theorem exitFrameWithProtectors_not_released_keeps_protectedTags
    (tree : Anneal.RefFrame.RangedBorrowTree) (frameTags : List Nat)
    (hNot : (Anneal.RefFrame.exitFrameWithProtectors tree frameTags).status ≠
      .Released) :
    (Anneal.RefFrame.exitFrameWithProtectors tree frameTags).tree.protectedTags =
      tree.protectedTags := by
  have hKeep := exitFrameFold_preserves_protectedTags frameTags ⟨tree, .Released⟩
  rw [exitFrameWithProtectors_eq_fold] at hNot ⊢
  generalize frameTags.foldl exitFrameStepFn ⟨tree, .Released⟩ = relOut
    at hNot hKeep ⊢
  cases relOut with
  | mk relTree relSt =>
    cases relSt with
    | Released => exact False.elim (hNot rfl)
    | MissingTag _ => exact hKeep
    | AccessFailure _ _ _ _ => exact hKeep
    | InvariantFailure _ _ _ => exact hKeep

private theorem listFilter_true {α : Type} :
    ∀ (xs : List α), xs.filter (fun _ => true) = xs
  | [] => rfl
  | x :: tl => congrArg (List.cons x) (listFilter_true tl)

/-- Empty-protector frame exit (`frameTags = []`): a callee owning no
Tree Borrows protectors releases cleanly and returns the identical
`RangedBorrowTree`. -/
theorem exitFrameWithProtectors_nil (tree : Anneal.RefFrame.RangedBorrowTree) :
    Anneal.RefFrame.exitFrameWithProtectors tree [] = ⟨tree, .Released⟩ := by
  unfold Anneal.RefFrame.exitFrameWithProtectors Anneal.RefFrame.endCallRemoveProtectors
  cases tree with
  | mk topo prot segs =>
    dsimp only [List.foldl]
    have hF : prot.filter (fun t => !Anneal.RefFrame.natListMem t []) = prot :=
      listFilter_true prot
    rw [hF]

/-- Protected `&mut` borrow writeback frame pairing `RefFrame Addr` with the
callee's Tree Borrows protector tags `frameTags : List Nat` on a shared
`Anneal.RefFrame.RangedBorrowTree`. -/
structure ProtectedRefFrame (Addr : Type v) where
  /-- Underlying `&mut` writeback lens and 4-way call continuation. -/
  frame : RefFrame Addr
  /-- Protector tags owned by the exiting call frame. -/
  frameTags : List Nat

/-- Evaluates a protected call-frame exit: runs
`Anneal.RefFrame.exitFrameWithProtectors tree prf.frameTags` FIRST on both
`.returned` and `.unwound` exits; only when protector release returns
`.Released` does it commit `evalRefFrameExit prf.frame mem exit` and return
the stripped `rel.tree`. Any `.MissingTag`, `.AccessFailure` (e.g.
`.ProtectedDisabled`), or `.InvariantFailure` fails closed to `.fault`. -/
def evalProtectedRefFrameExit {Mem : Type u} {Addr : Type v} {Byte : Type a}
    {Val : Type w} [ops : ByteStoreOps Mem Addr Byte]
    (prf : ProtectedRefFrame Addr) (mem : Mem)
    (tree : Anneal.RefFrame.RangedBorrowTree) (exit : CalleeExit Val Byte) :
    CallerContOutcome Mem Val × Anneal.RefFrame.RangedBorrowTree :=
  let rel := Anneal.RefFrame.exitFrameWithProtectors tree prf.frameTags
  match rel.status with
  | .Released => (evalRefFrameExit prf.frame mem exit, rel.tree)
  | .MissingTag _ => (.fault, rel.tree)
  | .AccessFailure _ _ _ _ => (.fault, rel.tree)
  | .InvariantFailure _ _ _ => (.fault, rel.tree)

section ProtectedRefFrameLaws

variable {Mem : Type u} {Addr : Type v} {Byte : Type a} {Val : Type w}
  [ops : ByteStoreOps Mem Addr Byte]

/-- Sound reduction of `evalProtectedRefFrameExit` when protector release
succeeds (`.Released`), certifying that all `prf.frameTags` are stripped from
`tree'.protectedTags`. -/
theorem evalProtectedRefFrameExit_of_released (prf : ProtectedRefFrame Addr)
    (mem : Mem) {tree tree' : Anneal.RefFrame.RangedBorrowTree}
    (exit : CalleeExit Val Byte)
    (hRel : Anneal.RefFrame.exitFrameWithProtectors tree prf.frameTags =
      ⟨tree', .Released⟩) :
    evalProtectedRefFrameExit prf mem tree exit =
      (evalRefFrameExit prf.frame mem exit, tree') ∧
    (∀ t : Nat, Anneal.RefFrame.natListMem t prf.frameTags = true →
      Anneal.RefFrame.natListMem t tree'.protectedTags = false) ∧
    (∀ t : Nat, Anneal.RefFrame.natListMem t prf.frameTags = false →
      Anneal.RefFrame.natListMem t tree'.protectedTags =
        Anneal.RefFrame.natListMem t tree.protectedTags) := by
  have hTags := exitFrameWithProtectors_released_tags hRel
  refine ⟨?_, hTags.1, hTags.2⟩
  unfold evalProtectedRefFrameExit
  dsimp only
  rw [hRel]

/-- Fail-closed: `.MissingTag` from `exitFrameWithProtectors` yields `.fault`.
-/
theorem evalProtectedRefFrameExit_fault_of_missingTag
    (prf : ProtectedRefFrame Addr) (mem : Mem)
    {tree tree' : Anneal.RefFrame.RangedBorrowTree} {tag : Nat}
    (exit : CalleeExit Val Byte)
    (hErr : Anneal.RefFrame.exitFrameWithProtectors tree prf.frameTags =
      ⟨tree', .MissingTag tag⟩) :
    (evalProtectedRefFrameExit prf mem tree exit).1 = .fault := by
  unfold evalProtectedRefFrameExit
  dsimp only
  rw [hErr]

/-- Fail-closed: `.AccessFailure` (such as `.ProtectedDisabled`) from
`exitFrameWithProtectors` yields `.fault`. -/
theorem evalProtectedRefFrameExit_fault_of_accessFailure
    (prf : ProtectedRefFrame Addr) (mem : Mem)
    {tree tree' : Anneal.RefFrame.RangedBorrowTree}
    {off len nodeTag : Nat} {err : Anneal.RefFrame.TbTransitionError}
    (exit : CalleeExit Val Byte)
    (hErr : Anneal.RefFrame.exitFrameWithProtectors tree prf.frameTags =
      ⟨tree', .AccessFailure off len nodeTag err⟩) :
    (evalProtectedRefFrameExit prf mem tree exit).1 = .fault := by
  unfold evalProtectedRefFrameExit
  dsimp only
  rw [hErr]

/-- Fail-closed: `.InvariantFailure` from `exitFrameWithProtectors` yields
`.fault`. -/
theorem evalProtectedRefFrameExit_fault_of_invariantFailure
    (prf : ProtectedRefFrame Addr) (mem : Mem)
    {tree tree' : Anneal.RefFrame.RangedBorrowTree}
    {off len nodeTag : Nat}
    (exit : CalleeExit Val Byte)
    (hErr : Anneal.RefFrame.exitFrameWithProtectors tree prf.frameTags =
      ⟨tree', .InvariantFailure off len nodeTag⟩) :
    (evalProtectedRefFrameExit prf mem tree exit).1 = .fault := by
  unfold evalProtectedRefFrameExit
  dsimp only
  rw [hErr]

/-- Universal fail-closed rule for unprotected frame tags: if ANY tag claimed by
`prf.frameTags` is not in `tree.protectedTags`, `evalProtectedRefFrameExit`
faults on every `(onRet, onUnwind)` regime and every callee exit, and returns a
tree whose `protectedTags` are unchanged (no protector is stripped by a failed
exit). -/
theorem evalProtectedRefFrameExit_fault_of_unprotected_frameTag
    (prf : ProtectedRefFrame Addr) (mem : Mem)
    (tree : Anneal.RefFrame.RangedBorrowTree) (exit : CalleeExit Val Byte)
    {t : Nat}
    (hIn : Anneal.RefFrame.natListMem t prf.frameTags = true)
    (hUnprot : Anneal.RefFrame.natListMem t tree.protectedTags = false) :
    (evalProtectedRefFrameExit prf mem tree exit).1 = .fault ∧
    (evalProtectedRefFrameExit prf mem tree exit).2.protectedTags =
      tree.protectedTags := by
  have hNot :
      (Anneal.RefFrame.exitFrameWithProtectors tree prf.frameTags).status ≠
        .Released := by
    intro hSt
    cases hR : Anneal.RefFrame.exitFrameWithProtectors tree prf.frameTags with
    | mk tr st =>
      rw [hR] at hSt
      have hSt' : st = .Released := hSt
      rw [hSt'] at hR
      have hProt := exitFrameWithProtectors_released_all_protected hR t hIn
      rw [hUnprot] at hProt
      cases hProt
  have hKeep := exitFrameWithProtectors_not_released_keeps_protectedTags
    tree prf.frameTags hNot
  unfold evalProtectedRefFrameExit
  dsimp only
  cases hR : Anneal.RefFrame.exitFrameWithProtectors tree prf.frameTags with
  | mk tr st =>
    rw [hR] at hNot hKeep
    cases st with
    | Released => exact False.elim (hNot rfl)
    | MissingTag _ => exact ⟨rfl, hKeep⟩
    | AccessFailure _ _ _ _ => exact ⟨rfl, hKeep⟩
    | InvariantFailure _ _ _ => exact ⟨rfl, hKeep⟩

/-- Complete 16-equation protected call-frame continuation matrix combining
`refFrame_callCont4_matrix_sound` with `Anneal.RefFrame.exitFrameWithProtectors`
protector stripping. -/
theorem protectedRefFrame_callCont4_matrix_sound
    [LawfulByteStoreOps Mem Addr Byte] {Prov : Type b}
    (codec : ByteRunCodec Prov Byte)
    (L : ByteSubLens Addr) (frameTags : List Nat)
    (m : Mem) (old : List Byte)
    (tree tree' : Anneal.RefFrame.RangedBorrowTree)
    (retBb cleanupBb : Nat) (retVal : Val)
    (normalRuns partialRuns : List (ByteRun Prov))
    (hGet : L.get m = some old)
    (hNormLen : runsByteLen normalRuns = L.len)
    (hPartLen : runsByteLen partialRuns = L.len)
    (hRel : Anneal.RefFrame.exitFrameWithProtectors tree frameTags =
      ⟨tree', .Released⟩) :
    (∀ t : Nat, Anneal.RefFrame.natListMem t frameTags = true →
      Anneal.RefFrame.natListMem t tree'.protectedTags = false) ∧
    ∃ (mNorm mUnw : Mem),
      L.get mNorm = some (flattenByteRuns codec normalRuns) ∧
      L.get mUnw = some (flattenByteRuns codec partialRuns) ∧
      (∀ other : ByteSubLens Addr, L.Disjoint Mem other →
        other.get mNorm = other.get m ∧ other.get mUnw = other.get m) ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨some retBb, .cleanup cleanupBb⟩⟩, frameTags⟩ m tree
        (.returned retVal (flattenByteRuns codec normalRuns)) =
        (.jumpNormal retBb retVal mNorm, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨some retBb, .cleanup cleanupBb⟩⟩, frameTags⟩ m tree
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        (.jumpCleanup cleanupBb mUnw, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨some retBb, .continue_⟩⟩, frameTags⟩ m tree
        (.returned retVal (flattenByteRuns codec normalRuns)) =
        (.jumpNormal retBb retVal mNorm, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨some retBb, .continue_⟩⟩, frameTags⟩ m tree
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        (.propagateUnwind mUnw, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨some retBb, .unreachable⟩⟩, frameTags⟩ m tree
        (.returned retVal (flattenByteRuns codec normalRuns)) =
        (.jumpNormal retBb retVal mNorm, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨some retBb, .unreachable⟩⟩, frameTags⟩ m tree
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) = (.fault, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨some retBb, .terminate⟩⟩, frameTags⟩ m tree
        (.returned retVal (flattenByteRuns codec normalRuns)) =
        (.jumpNormal retBb retVal mNorm, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨some retBb, .terminate⟩⟩, frameTags⟩ m tree
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        (.abortTerminate mUnw, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨none, .cleanup cleanupBb⟩⟩, frameTags⟩ m tree
        (.returned retVal (flattenByteRuns codec normalRuns)) = (.fault, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨none, .cleanup cleanupBb⟩⟩, frameTags⟩ m tree
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        (.jumpCleanup cleanupBb mUnw, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨none, .continue_⟩⟩, frameTags⟩ m tree
        (.returned retVal (flattenByteRuns codec normalRuns)) = (.fault, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨none, .continue_⟩⟩, frameTags⟩ m tree
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        (.propagateUnwind mUnw, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨none, .unreachable⟩⟩, frameTags⟩ m tree
        (.returned retVal (flattenByteRuns codec normalRuns)) = (.fault, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨none, .unreachable⟩⟩, frameTags⟩ m tree
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) = (.fault, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨none, .terminate⟩⟩, frameTags⟩ m tree
        (.returned retVal (flattenByteRuns codec normalRuns)) = (.fault, tree') ∧
      evalProtectedRefFrameExit ⟨⟨L, ⟨none, .terminate⟩⟩, frameTags⟩ m tree
        (CalleeExit.unwound (Val := Val) (flattenByteRuns codec partialRuns)) =
        (.abortTerminate mUnw, tree') := by
  have hTags := exitFrameWithProtectors_released_tags hRel
  let ⟨mNorm, mUnw, _, hGetN, _, hGetU, hFrame,
      e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ :=
    refFrame_callCont4_matrix_sound codec L m old retBb cleanupBb retVal
      normalRuns partialRuns hGet hNormLen hPartLen
  have hWrap : ∀ (cont : CallCont4) (ex : CalleeExit Val Byte),
      evalProtectedRefFrameExit ⟨⟨L, cont⟩, frameTags⟩ m tree ex =
        (evalRefFrameExit ⟨L, cont⟩ m ex, tree') := fun cont ex =>
    (evalProtectedRefFrameExit_of_released ⟨⟨L, cont⟩, frameTags⟩ m ex hRel).1
  refine ⟨hTags.1, mNorm, mUnw, hGetN, hGetU, hFrame, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hWrap, e1]
  · rw [hWrap, e2]
  · rw [hWrap, e3]
  · rw [hWrap, e4]
  · rw [hWrap, e5]
  · rw [hWrap, e6]
  · rw [hWrap, e7]
  · rw [hWrap, e8]
  · rw [hWrap, e9]
  · rw [hWrap, e10]
  · rw [hWrap, e11]
  · rw [hWrap, e12]
  · rw [hWrap, e13]
  · rw [hWrap, e14]
  · rw [hWrap, e15]
  · rw [hWrap, e16]

end ProtectedRefFrameLaws

/-! ### Lifting `Anneal.RefFrame.shared_topo3_ranged_commutation_universal` -/

private def topo3NextDstPerm (p : Anneal.RefFrame.TbPermission) :
    Anneal.RefFrame.TbPermission :=
  match p with
  | .Cell => .Cell
  | .ReservedFrz _ | .ReservedIM | .Unique | .Frozen | .Disabled => .Unique

private theorem topo3_seg08_read_ok (pSrc : Anneal.RefFrame.TbPermission)
    (accSrc protBoth : Bool)
    (hRead : Anneal.RefFrame.permCanLocalRead pSrc = true) :
    Anneal.RefFrame.performSegmentAccess Anneal.RefFrame.topo3
      (if protBoth then [1, 2] else [2])
      ⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨pSrc, accSrc⟩),
              (2, ⟨.Disabled, false⟩)]⟩
      1 .Read .VisitChildrenOfAccessed =
    .ok ⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨pSrc, true⟩),
                (2, ⟨.Disabled, false⟩)]⟩ := by
  cases pSrc with
  | Disabled => cases hRead
  | Cell => cases accSrc <;> cases protBoth <;> rfl
  | ReservedFrz c => cases c <;> cases accSrc <;> cases protBoth <;> rfl
  | ReservedIM => cases accSrc <;> cases protBoth <;> rfl
  | Unique => cases accSrc <;> cases protBoth <;> rfl
  | Frozen => cases accSrc <;> cases protBoth <;> rfl

private theorem topo3_seg816_write_ok (pDst : Anneal.RefFrame.TbPermission)
    (accDst protBoth : Bool)
    (hWrite : Anneal.RefFrame.permCanProtectedLocalWrite pDst = true) :
    Anneal.RefFrame.performSegmentAccess Anneal.RefFrame.topo3
      (if protBoth then [1, 2] else [2])
      ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
              (2, ⟨pDst, accDst⟩)]⟩
      2 .Write .VisitChildrenOfAccessed =
    .ok ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
      (2, ⟨topo3NextDstPerm pDst, true⟩)]⟩ := by
  cases pDst with
  | Frozen | Disabled => cases hWrite
  | ReservedFrz c =>
    cases c with
    | true => cases hWrite
    | false => cases accDst <;> cases protBoth <;> rfl
  | Cell => cases accDst <;> cases protBoth <;> rfl
  | ReservedIM => cases accDst <;> cases protBoth <;> rfl
  | Unique => cases accDst <;> cases protBoth <;> rfl

private theorem topo3_exit_after_accesses (pSrc : Anneal.RefFrame.TbPermission)
    (pDstAfter : Anneal.RefFrame.TbPermission) (protBoth : Bool)
    (hRead : Anneal.RefFrame.permCanLocalRead pSrc = true)
    (hDst : pDstAfter = .Cell ∨ pDstAfter = .Unique) :
    let protTags := if protBoth then [1, 2] else [2]
    let treeAfter : Anneal.RefFrame.RangedBorrowTree :=
      { topology := Anneal.RefFrame.topo3
        protectedTags := protTags
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨pSrc, true⟩),
                   (2, ⟨.Disabled, false⟩)]⟩,
           ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
                   (2, ⟨pDstAfter, true⟩)]⟩] }
    let rel := Anneal.RefFrame.exitFrameWithProtectors treeAfter protTags
    rel.status = .Released ∧ rel.tree.protectedTags = [] := by
  cases hDst with
  | inl hC =>
    subst hC
    cases pSrc with
    | Disabled => cases hRead
    | Cell => cases protBoth <;> exact ⟨rfl, rfl⟩
    | ReservedFrz c => cases c <;> cases protBoth <;> exact ⟨rfl, rfl⟩
    | ReservedIM => cases protBoth <;> exact ⟨rfl, rfl⟩
    | Unique => cases protBoth <;> exact ⟨rfl, rfl⟩
    | Frozen => cases protBoth <;> exact ⟨rfl, rfl⟩
  | inr hU =>
    subst hU
    cases pSrc with
    | Disabled => cases hRead
    | Cell => cases protBoth <;> exact ⟨rfl, rfl⟩
    | ReservedFrz c => cases c <;> cases protBoth <;> exact ⟨rfl, rfl⟩
    | ReservedIM => cases protBoth <;> exact ⟨rfl, rfl⟩
    | Unique => cases protBoth <;> exact ⟨rfl, rfl⟩
    | Frozen => cases protBoth <;> exact ⟨rfl, rfl⟩

/-- Auxiliary lemma: `exitFrameWithProtectors` on the post-access shared
3-node `topo3` tree releases `protTags` (`[1, 2]` or `[2]`) cleanly with
`.Released` and empty `protectedTags = []`. -/
theorem shared_topo3_exitFrame_released
    (pSrc pDst : Anneal.RefFrame.TbPermission) (accSrc accDst protBoth : Bool)
    (hRead : Anneal.RefFrame.permCanLocalRead pSrc = true)
    (hWrite : Anneal.RefFrame.permCanProtectedLocalWrite pDst = true) :
    let protTags := if protBoth then [1, 2] else [2]
    let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags
    let s1 := Anneal.RefFrame.performRangedAccess tree0 0 8 1 .Read .VisitChildrenOfAccessed
    let s12 := Anneal.RefFrame.performRangedAccess s1.tree 8 8 2 .Write .VisitChildrenOfAccessed
    let rel := Anneal.RefFrame.exitFrameWithProtectors s12.tree protTags
    rel.status = .Released ∧ rel.tree.protectedTags = [] := by
  let protTags := if protBoth then [1, 2] else [2]
  have hS08 := topo3_seg08_read_ok pSrc accSrc protBoth hRead
  have hS816 := topo3_seg816_write_ok pDst accDst protBoth hWrite
  have hNextDst : topo3NextDstPerm pDst = .Cell ∨ topo3NextDstPerm pDst = .Unique := by
    cases pDst <;> first | exact Or.inl rfl | exact Or.inr rfl
  let seg08Init : Anneal.RefFrame.RangeSegment :=
    ⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨pSrc, accSrc⟩), (2, ⟨.Disabled, false⟩)]⟩
  let seg08After : Anneal.RefFrame.RangeSegment :=
    ⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨pSrc, true⟩), (2, ⟨.Disabled, false⟩)]⟩
  let seg816Init : Anneal.RefFrame.RangeSegment :=
    ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩), (2, ⟨pDst, accDst⟩)]⟩
  let seg816After : Anneal.RefFrame.RangeSegment :=
    ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
            (2, ⟨topo3NextDstPerm pDst, true⟩)]⟩
  have hStep1 :
      (Anneal.RefFrame.performRangedAccess
        (Anneal.RefFrame.mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags)
        0 8 1 .Read .VisitChildrenOfAccessed).tree =
      { topology := Anneal.RefFrame.topo3
        protectedTags := protTags
        segments := [seg08After, seg816Init] } := by
    unfold Anneal.RefFrame.mkSharedTopo3Tree16 Anneal.RefFrame.performRangedAccess
    change ({ topology := Anneal.RefFrame.topo3
              protectedTags := protTags
              segments :=
                ([seg08Init, seg816Init].foldl
                  (Anneal.RefFrame.stepRangedSegment Anneal.RefFrame.topo3
                    protTags 0 8 1 .Read .VisitChildrenOfAccessed)
                  ([], 0, .Completed)).1 } : Anneal.RefFrame.RangedBorrowTree) = _
    dsimp only [List.foldl, Anneal.RefFrame.stepRangedSegment, seg08Init, seg816Init]
    have hIteF : ∀ {α : Type} {t e : α},
        (if Anneal.RefFrame.rangesDisjoint 0 8 0 8 then t else e) = e := fun {_ _ _} => rfl
    have hIteT : ∀ {α : Type} {t e : α},
        (if Anneal.RefFrame.rangesDisjoint 0 8 8 8 then t else e) = t := fun {_ _ _} => rfl
    rw [hIteF, hS08]
    dsimp only
    rw [hIteT]
    rfl
  have hTree12 :
      (Anneal.RefFrame.performRangedAccess
        (Anneal.RefFrame.performRangedAccess
          (Anneal.RefFrame.mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags)
          0 8 1 .Read .VisitChildrenOfAccessed).tree
        8 8 2 .Write .VisitChildrenOfAccessed).tree =
      { topology := Anneal.RefFrame.topo3
        protectedTags := protTags
        segments := [seg08After, seg816After] } := by
    rw [hStep1]
    unfold Anneal.RefFrame.performRangedAccess
    change ({ topology := Anneal.RefFrame.topo3
              protectedTags := protTags
              segments :=
                ([seg08After, seg816Init].foldl
                  (Anneal.RefFrame.stepRangedSegment Anneal.RefFrame.topo3
                    protTags 8 8 2 .Write .VisitChildrenOfAccessed)
                  ([], 0, .Completed)).1 } : Anneal.RefFrame.RangedBorrowTree) = _
    dsimp only [List.foldl, Anneal.RefFrame.stepRangedSegment, seg08After, seg816Init]
    have hIteT : ∀ {α : Type} {t e : α},
        (if Anneal.RefFrame.rangesDisjoint 8 8 0 8 then t else e) = t := fun {_ _ _} => rfl
    have hIteF : ∀ {α : Type} {t e : α},
        (if Anneal.RefFrame.rangesDisjoint 8 8 8 8 then t else e) = e := fun {_ _ _} => rfl
    rw [hIteT]
    dsimp only
    rw [hIteF, hS816]
    rfl
  dsimp only
  change (Anneal.RefFrame.exitFrameWithProtectors _ protTags).status = .Released ∧
    (Anneal.RefFrame.exitFrameWithProtectors _ protTags).tree.protectedTags = []
  rw [hTree12]
  exact topo3_exit_after_accesses pSrc (topo3NextDstPerm pDst) protBoth hRead hNextDst

/-- Lifted universal commutation across protected call-frame exit: reading `src`
(tag `1`, `[0..8)`) and writing protected `dst` (tag `2`, `[8..16)`) on a shared
3-node `RangedBorrowTree` commute to the identical tree state, release all
`protTags` cleanly via `exitFrameWithProtectors`, and produce identical
`(CallerContOutcome, RangedBorrowTree)` results under `evalProtectedRefFrameExit`
with all `protTags` stripped (`protectedTags = []`). -/
theorem protectedRefFrame_shared_topo3_commutation
    {Mem : Type u} {Addr : Type v} {Byte : Type a} {Val : Type w}
    [ops : ByteStoreOps Mem Addr Byte]
    (pSrc pDst : Anneal.RefFrame.TbPermission) (accSrc accDst protBoth : Bool)
    (hRead : Anneal.RefFrame.permCanLocalRead pSrc = true)
    (hWrite : Anneal.RefFrame.permCanProtectedLocalWrite pDst = true)
    (rf : RefFrame Addr) (mem : Mem) (exit : CalleeExit Val Byte) :
    let protTags := if protBoth then [1, 2] else [2]
    let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags
    let s1 := Anneal.RefFrame.performRangedAccess tree0 0 8 1 .Read .VisitChildrenOfAccessed
    let s12 := Anneal.RefFrame.performRangedAccess s1.tree 8 8 2 .Write .VisitChildrenOfAccessed
    let s2 := Anneal.RefFrame.performRangedAccess tree0 8 8 2 .Write .VisitChildrenOfAccessed
    let s21 := Anneal.RefFrame.performRangedAccess s2.tree 0 8 1 .Read .VisitChildrenOfAccessed
    let out12 := evalProtectedRefFrameExit ⟨rf, protTags⟩ mem s12.tree exit
    let out21 := evalProtectedRefFrameExit ⟨rf, protTags⟩ mem s21.tree exit
    s1.status = .Completed ∧
    s2.status = .Completed ∧
    s12.status = .Completed ∧
    s21.status = .Completed ∧
    s12.tree = s21.tree ∧
    out12 = out21 ∧
    out12.1 = evalRefFrameExit rf mem exit ∧
    out12.2.protectedTags = [] := by
  have hComm := Anneal.RefFrame.shared_topo3_ranged_commutation_universal
    pSrc pDst accSrc accDst protBoth hRead hWrite
  have hRel := shared_topo3_exitFrame_released
    pSrc pDst accSrc accDst protBoth hRead hWrite
  dsimp only at hComm hRel ⊢
  let protTags := if protBoth then [1, 2] else [2]
  let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags
  let s1 := Anneal.RefFrame.performRangedAccess tree0 0 8 1 .Read .VisitChildrenOfAccessed
  let s12 := Anneal.RefFrame.performRangedAccess s1.tree 8 8 2 .Write .VisitChildrenOfAccessed
  let s2 := Anneal.RefFrame.performRangedAccess tree0 8 8 2 .Write .VisitChildrenOfAccessed
  let s21 := Anneal.RefFrame.performRangedAccess s2.tree 0 8 1 .Read .VisitChildrenOfAccessed
  have hTreeEq : s12.tree = s21.tree := hComm.2.2.2.2
  have hOutEq :
      evalProtectedRefFrameExit ⟨rf, protTags⟩ mem s12.tree exit =
        evalProtectedRefFrameExit ⟨rf, protTags⟩ mem s21.tree exit := by
    rw [hTreeEq]
  have hRelEq :
      Anneal.RefFrame.exitFrameWithProtectors s12.tree protTags =
        ⟨(Anneal.RefFrame.exitFrameWithProtectors s12.tree protTags).tree,
         .Released⟩ := by
    cases hR : Anneal.RefFrame.exitFrameWithProtectors s12.tree protTags with
    | mk t st =>
      rw [hR] at hRel
      dsimp only at hRel
      rw [hRel.1]
  have hEval := evalProtectedRefFrameExit_of_released ⟨rf, protTags⟩ mem exit hRelEq
  refine ⟨hComm.1, hComm.2.1, hComm.2.2.1, hComm.2.2.2.1, hTreeEq, hOutEq, ?_, ?_⟩
  · rw [hEval.1]
  · rw [hEval.1]
    exact hRel.2

/-! ## Part II: `UpdatesOnly` Sub-Lens Framing Algebra -/

/-- Multi-step byte-lens modification framing: `m₁` is obtained from `m₀` by
zero or more `ByteSubLens.set` updates confined strictly to lenses in
`allowed : List (ByteSubLens Addr)`. -/
inductive UpdatesOnly {Mem : Type u} {Addr : Type v} {Byte : Type a}
    [ops : ByteStoreOps Mem Addr Byte]
    (allowed : List (ByteSubLens Addr)) : Mem → Mem → Prop where
  | refl (m : Mem) : UpdatesOnly allowed m m
  | step {m₀ m₁ m₂ : Mem} {L : ByteSubLens Addr} {bs : List Byte}
      (hIn : L ∈ allowed)
      (hSet : L.set m₀ bs = some m₁)
      (hRest : UpdatesOnly allowed m₁ m₂) :
      UpdatesOnly allowed m₀ m₂

section UpdatesOnlyLaws

variable {Mem : Type u} {Addr : Type v} {Byte : Type a}
  [ops : ByteStoreOps Mem Addr Byte]

/-- Single-step introduction of `UpdatesOnly` from `L.set m₀ bs = some m₁`. -/
theorem UpdatesOnly.of_set {allowed : List (ByteSubLens Addr)}
    {L : ByteSubLens Addr} {m₀ m₁ : Mem} {bs : List Byte}
    (hIn : L ∈ allowed) (hSet : L.set m₀ bs = some m₁) :
    UpdatesOnly allowed m₀ m₁ :=
  .step hIn hSet (.refl m₁)

/-- Single-lens convenience introduction `UpdatesOnly [L] m₀ m₁`. -/
theorem UpdatesOnly.of_single_set {L : ByteSubLens Addr} {m₀ m₁ : Mem}
    {bs : List Byte} (hSet : L.set m₀ bs = some m₁) :
    UpdatesOnly [L] m₀ m₁ :=
  UpdatesOnly.of_set (List.Mem.head []) hSet

/-- Transitivity of `UpdatesOnly`. -/
theorem UpdatesOnly.trans {allowed : List (ByteSubLens Addr)}
    {m₀ m₁ m₂ : Mem} (h₁ : UpdatesOnly allowed m₀ m₁)
    (h₂ : UpdatesOnly allowed m₁ m₂) :
    UpdatesOnly allowed m₀ m₂ := by
  induction h₁ with
  | refl _ => exact h₂
  | step hIn hSet _ ih => exact .step hIn hSet (ih h₂)

/-- Subset monotonicity: enlarging `allowed` preserves `UpdatesOnly`. -/
theorem UpdatesOnly.mono_subset {allowed₁ allowed₂ : List (ByteSubLens Addr)}
    (hSub : ∀ L : ByteSubLens Addr, L ∈ allowed₁ → L ∈ allowed₂)
    {m₀ m₁ : Mem} (h : UpdatesOnly allowed₁ m₀ m₁) :
    UpdatesOnly allowed₂ m₀ m₁ := by
  induction h with
  | refl m => exact .refl m
  | step hIn hSet _ ih => exact .step (hSub _ hIn) hSet ih

/-- Any `copyRangeComp src dst` transition is confined to `allowed` whenever
`dst ∈ allowed`. -/
theorem UpdatesOnly.of_copyRangeComp {allowed : List (ByteSubLens Addr)}
    {src dst : ByteSubLens Addr} {m₀ m₁ : Mem}
    (hIn : dst ∈ allowed) (hCopy : copyRangeComp src dst m₀ = some m₁) :
    UpdatesOnly allowed m₀ m₁ := by
  unfold copyRangeComp at hCopy
  cases hGuard : (Nat.beq src.len 0 || Nat.beq dst.len 0 || !Nat.beq src.len dst.len) with
  | true => rw [hGuard] at hCopy; cases hCopy
  | false =>
    rw [hGuard] at hCopy
    cases hGet : src.get m₀ with
    | none => rw [hGet] at hCopy; cases hCopy
    | some bs =>
      rw [hGet] at hCopy
      exact UpdatesOnly.of_set hIn hCopy

/-- Any `writeRepeatRunsComp` transition is confined to `allowed` whenever the
target window lens `{ addr := dstAddr, offset := dstOff, len :=
n * runsByteLen runs }` lies in `allowed`. -/
theorem UpdatesOnly.of_writeRepeatRunsComp {Prov : Type b}
    {allowed : List (ByteSubLens Addr)} (codec : ByteRunCodec Prov Byte)
    {dstAddr : Addr} {dstOff n : Nat} {runs : List (ByteRun Prov)}
    {m₀ m₁ : Mem}
    (hIn : ({ addr := dstAddr, offset := dstOff,
              len := n * runsByteLen runs } : ByteSubLens Addr) ∈ allowed)
    (hWr : writeRepeatRunsComp codec dstAddr dstOff n runs m₀ = some m₁) :
    UpdatesOnly allowed m₀ m₁ :=
  UpdatesOnly.of_set hIn hWr

/-- Auxiliary-projection preservation: any store-write-invariant projection
`proj` (e.g. allocation metadata or borrow table stored alongside bytes) is
preserved across every `UpdatesOnly` transition. -/
theorem updatesOnly_preserves_proj {V : Sort y} {proj : Mem → V}
    (hPres : ops.WritePreserves proj) {allowed : List (ByteSubLens Addr)}
    {m₀ m₁ : Mem} (h : UpdatesOnly allowed m₀ m₁) :
    proj m₁ = proj m₀ := by
  induction h with
  | refl _ => rfl
  | step _ hSet _ ih =>
    exact ih.trans (ByteSubLens.set_preserves hPres hSet)

/-- Sub-lens containment write lift: writing through a sub-lens `subL ⊆ bigL`
when `bigL` is readable in `m₀` is an `UpdatesOnly` step on `bigL` (via
`ByteSubLens.zoom_set_eq_splice`). -/
theorem UpdatesOnly.of_contained_set [LawfulByteStoreOps Mem Addr Byte]
    {allowed : List (ByteSubLens Addr)} {subL bigL : ByteSubLens Addr}
    {m₀ m₁ : Mem} {old sub : List Byte}
    (hIn : bigL ∈ allowed)
    (hCont : subL.ContainedIn bigL)
    (hGetBig : bigL.get m₀ = some old)
    (hSetSub : subL.set m₀ sub = some m₁) :
    UpdatesOnly allowed m₀ m₁ := by
  let ⟨hPosSub, hSubLen, _⟩ := ByteSubLens.set_inv hSetSub
  have hZoomEq : bigL.zoom (subL.offset - bigL.offset) subL.len = subL := by
    unfold ByteSubLens.zoom
    cases subL with
    | mk a off len =>
      cases bigL with
      | mk ba boff blen =>
        dsimp only [ByteSubLens.ContainedIn] at hCont
        have hAddr : ba = a := hCont.1.symm
        have hOff : boff + (off - boff) = off := Nat.add_sub_of_le hCont.2.1
        rw [hAddr, hOff]
  have hRelBound : (subL.offset - bigL.offset) + subL.len ≤ bigL.len := by
    have hAdd : bigL.offset + ((subL.offset - bigL.offset) + subL.len) ≤
        bigL.offset + bigL.len := by
      rw [← Nat.add_assoc, Nat.add_sub_of_le hCont.2.1]
      exact hCont.2.2
    exact Nat.le_of_add_le_add_left hAdd
  rw [← hZoomEq, ByteSubLens.zoom_set_eq_splice hGetBig hPosSub hRelBound hSubLen] at hSetSub
  exact UpdatesOnly.of_set hIn hSetSub

/-- Hierarchical sub-lens containment monotonicity for single-lens footprints:
any multi-step update sequence confined to `subL ⊆ bigL` (when `bigL` is
readable at entry) is confined to `[bigL]`. -/
theorem UpdatesOnly.mono_contained_single [LawfulByteStoreOps Mem Addr Byte]
    {subL bigL : ByteSubLens Addr} {m₀ m₁ : Mem} {old : List Byte}
    (hCont : subL.ContainedIn bigL)
    (hGetBig : bigL.get m₀ = some old)
    (hUpd : UpdatesOnly [subL] m₀ m₁) :
    UpdatesOnly [bigL] m₀ m₁ := by
  induction hUpd generalizing old with
  | refl m => exact .refl m
  | @step ma mb mc L bs hIn hSet _ ih =>
    have hEqL : L = subL := by
      cases hIn with
      | head => rfl
      | tail _ hEmpty => cases hEmpty
    rw [hEqL] at hSet
    have hStepBig : UpdatesOnly [bigL] ma mb :=
      UpdatesOnly.of_contained_set (List.Mem.head []) hCont hGetBig hSet
    have hGetMb : ∃ old', bigL.get mb = some old' := by
      have hZoomEq : bigL.zoom (subL.offset - bigL.offset) subL.len = subL := by
        unfold ByteSubLens.zoom
        cases subL with
        | mk a off len =>
          cases bigL with
          | mk ba boff blen =>
            dsimp only [ByteSubLens.ContainedIn] at hCont
            rw [hCont.1.symm, Nat.add_sub_of_le hCont.2.1]
      have hRelBound : (subL.offset - bigL.offset) + subL.len ≤ bigL.len := by
        have hAdd : bigL.offset + ((subL.offset - bigL.offset) + subL.len) ≤
            bigL.offset + bigL.len := by
          rw [← Nat.add_assoc, Nat.add_sub_of_le hCont.2.1]
          exact hCont.2.2
        exact Nat.le_of_add_le_add_left hAdd
      rw [← hZoomEq] at hSet
      exact ⟨listSplice old (subL.offset - bigL.offset) bs,
        ByteSubLens.get_zoom_set hGetBig hRelBound hSet⟩
    let ⟨old', hGet'⟩ := hGetMb
    exact hStepBig.trans (ih hGet')

/-- Disjoint-lens framing theorem for `UpdatesOnly`: if `other` is pairwise
disjoint from every lens `L ∈ allowed`, then `other.get m₁ = other.get m₀`. -/
theorem updatesOnly_frame_disjoint [LawfulByteStoreOps Mem Addr Byte]
    {allowed : List (ByteSubLens Addr)} {other : ByteSubLens Addr}
    {m₀ m₁ : Mem}
    (hDisj : ∀ L : ByteSubLens Addr, L ∈ allowed → L.Disjoint Mem other)
    (hUpd : UpdatesOnly allowed m₀ m₁) :
    other.get m₁ = other.get m₀ := by
  induction hUpd with
  | refl _ => rfl
  | step hIn hSet _ ih =>
    exact ih.trans (ByteSubLens.get_set_disjoint (hDisj _ hIn) hSet)

private theorem contained_zoom_eq {a b : ByteSubLens Addr}
    (hCont : a.ContainedIn b) :
    b.zoom (a.offset - b.offset) a.len = a ∧
    (a.offset - b.offset) + a.len ≤ b.len := by
  refine ⟨?_, ?_⟩
  · unfold ByteSubLens.zoom
    cases a with
    | mk aa aoff alen =>
      cases b with
      | mk ba boff blen =>
        dsimp only [ByteSubLens.ContainedIn] at hCont
        rw [hCont.1.symm, Nat.add_sub_of_le hCont.2.1]
  · have hAdd : b.offset + ((a.offset - b.offset) + a.len) ≤ b.offset + b.len := by
      rw [← Nat.add_assoc, Nat.add_sub_of_le hCont.2.1]
      exact hCont.2.2
    exact Nat.le_of_add_le_add_left hAdd

/-- Lens readability and writability validity after `UpdatesOnly` (parametric
analog of `#4177`'s `lens_valid_after_updatesOnly`): for any positive-length
lens `Q` readable at entry (`Q.get m₀ = some old`), if every `L ∈ allowed` is
either disjoint from `Q`, contained in `Q`, or contains `Q`, then `Q` remains
readable (with exact length `Q.len`) and writable for any slice of length
`Q.len` in `m₁`. -/
theorem lens_valid_after_updatesOnly [LawfulByteStoreOps Mem Addr Byte]
    {allowed : List (ByteSubLens Addr)} {Q : ByteSubLens Addr}
    {m₀ m₁ : Mem} {old : List Byte}
    (hGet : Q.get m₀ = some old)
    (hCompat : ∀ L : ByteSubLens Addr, L ∈ allowed →
      L.Disjoint Mem Q ∨ L.ContainedIn Q ∨ Q.ContainedIn L)
    (hUpd : UpdatesOnly allowed m₀ m₁) :
    ∃ bs₁ : List Byte,
      Q.get m₁ = some bs₁ ∧
      bs₁.length = Q.len ∧
      (∀ newBs : List Byte, newBs.length = Q.len → ∃ m₂, Q.set m₁ newBs = some m₂) := by
  have hQPos : 0 < Q.len := (ByteSubLens.get_inv hGet).1
  have hAux : ∀ {ma mb : Mem} {oldA : List Byte},
      Q.get ma = some oldA → UpdatesOnly allowed ma mb →
      ∃ bs₁ : List Byte, Q.get mb = some bs₁ := by
    intro ma mb oldA hG hU
    induction hU generalizing oldA with
    | refl _ => exact ⟨oldA, hG⟩
    | @step mA mB mC L bs hIn hSet _ ih =>
      cases hCompat L hIn with
      | inl hDisj =>
        have hNext : Q.get mB = some oldA :=
          (ByteSubLens.get_set_disjoint hDisj hSet).trans hG
        exact ih hNext
      | inr hNest =>
        cases hNest with
        | inl hSub =>
          let ⟨hZoom, hBound⟩ := contained_zoom_eq hSub
          rw [← hZoom] at hSet
          exact ih (ByteSubLens.get_zoom_set hG hBound hSet)
        | inr hSup =>
          let ⟨hZoom, hBound⟩ := contained_zoom_eq hSup
          have hGetL : L.get mB = some bs := ByteSubLens.get_set hSet
          have hNext : Q.get mB = some ((bs.drop (Q.offset - L.offset)).take Q.len) := by
            have hZ := ByteSubLens.zoom_get hGetL hQPos hBound
            rw [hZoom] at hZ
            exact hZ
          exact ih hNext
  let ⟨bs₁, hGet₁⟩ := hAux hGet hUpd
  exact ⟨bs₁, hGet₁, ByteSubLens.get_len hGet₁,
    fun newBs hLen => ByteSubLens.set_isSome_of_get newBs hGet₁ hLen⟩

/-- Single-lens validity corollary: if `L` is readable before
`UpdatesOnly [L] m₀ m₁`, it remains readable and writable in `m₁`. -/
theorem lens_valid_after_updatesOnly_self [LawfulByteStoreOps Mem Addr Byte]
    {L : ByteSubLens Addr} {m₀ m₁ : Mem} {old : List Byte}
    (hGet : L.get m₀ = some old) (hUpd : UpdatesOnly [L] m₀ m₁) :
    ∃ bs₁ : List Byte,
      L.get m₁ = some bs₁ ∧
      bs₁.length = L.len ∧
      (∀ newBs : List Byte, newBs.length = L.len → ∃ m₂, L.set m₁ newBs = some m₂) :=
  lens_valid_after_updatesOnly hGet
    (fun L' hIn => by
      cases hIn with
      | head => exact Or.inr (Or.inl (ByteSubLens.containedIn_refl L))
      | tail _ hE => cases hE)
    hUpd

/-- Generalized hierarchical containment monotonicity for multi-lens footprints:
if every `L ∈ allowed` is contained in `bigL` and `bigL` is readable in `m₀`,
then `UpdatesOnly allowed m₀ m₁` collapses into `UpdatesOnly [bigL] m₀ m₁` and
preserves `bigL` readability. -/
theorem UpdatesOnly.mono_contained_list [LawfulByteStoreOps Mem Addr Byte]
    {allowed : List (ByteSubLens Addr)} {bigL : ByteSubLens Addr}
    {m₀ m₁ : Mem} {old : List Byte}
    (hAllSub : ∀ L : ByteSubLens Addr, L ∈ allowed → L.ContainedIn bigL)
    (hGetBig : bigL.get m₀ = some old)
    (hUpd : UpdatesOnly allowed m₀ m₁) :
    UpdatesOnly [bigL] m₀ m₁ ∧ ∃ bs₁ : List Byte, bigL.get m₁ = some bs₁ := by
  induction hUpd generalizing old with
  | refl m => exact ⟨.refl m, old, hGetBig⟩
  | @step ma mb mc L bs hIn hSet _ ih =>
    have hCont := hAllSub L hIn
    have hStepBig : UpdatesOnly [bigL] ma mb :=
      UpdatesOnly.of_contained_set (List.Mem.head []) hCont hGetBig hSet
    let ⟨hZoom, hBound⟩ := contained_zoom_eq hCont
    have hSetZ : (bigL.zoom (L.offset - bigL.offset) L.len).set ma bs = some mb := by
      rw [hZoom]; exact hSet
    have hGetMb := ByteSubLens.get_zoom_set hGetBig hBound hSetZ
    let ⟨hRestBig, bs₁, hGetEnd⟩ := ih hGetMb
    exact ⟨hStepBig.trans hRestBig, bs₁, hGetEnd⟩

/-- Bridge from `ByteRun.copyRepeatedlyComp` into `UpdatesOnly`: if the target
window `dstWin = { addr := dstAddr, offset := dstOff, len := n * src.len }`
lies in `allowed` and is readable in `m₀`, every successful `copyRepeatedlyComp`
execution satisfies `UpdatesOnly allowed m₀ m₁`. -/
theorem UpdatesOnly.of_copyRepeatedlyComp [LawfulByteStoreOps Mem Addr Byte]
    {allowed : List (ByteSubLens Addr)} {src : ByteSubLens Addr}
    {dstAddr : Addr} {dstOff n : Nat} {m₀ m₁ : Mem} {oldWin : List Byte}
    (hIn : ({ addr := dstAddr, offset := dstOff,
              len := n * src.len } : ByteSubLens Addr) ∈ allowed)
    (hWinGet : ({ addr := dstAddr, offset := dstOff,
                  len := n * src.len } : ByteSubLens Addr).get m₀ = some oldWin)
    (hRep : copyRepeatedlyComp src dstAddr dstOff n m₀ = some m₁) :
    UpdatesOnly allowed m₀ m₁ := by
  let dstWin : ByteSubLens Addr :=
    { addr := dstAddr, offset := dstOff, len := n * src.len }
  unfold copyRepeatedlyComp at hRep
  cases hGuard : (Nat.beq n 0 || Nat.beq src.len 0) with
  | true => rw [hGuard] at hRep; cases hRep
  | false =>
    rw [hGuard] at hRep
    have hRec :
        ∀ (j : Nat) (mOut : Mem), j ≤ n →
          @Nat.rec (fun _ => Option Mem) (some m₀)
            (fun i acc =>
              match acc with
              | none => none
              | some mCur =>
                copyRangeComp src
                  { addr := dstAddr, offset := dstOff + i * src.len,
                    len := src.len } mCur) j = some mOut →
          UpdatesOnly allowed m₀ mOut ∧ ∃ curWin, dstWin.get mOut = some curWin := by
      intro j
      induction j with
      | zero =>
        intro mOut _ hEq
        have hM : m₀ = mOut := Option.some.inj hEq
        rw [← hM]
        exact ⟨.refl m₀, oldWin, hWinGet⟩
      | succ k ih =>
        intro mOut hK1Le hStep
        change (match @Nat.rec (fun _ => Option Mem) (some m₀)
            (fun i acc =>
              match acc with
              | none => none
              | some mCur =>
                copyRangeComp src
                  { addr := dstAddr, offset := dstOff + i * src.len,
                    len := src.len } mCur) k with
          | none => none
          | some mCur =>
            copyRangeComp src
              { addr := dstAddr, offset := dstOff + k * src.len,
                len := src.len } mCur) = some mOut at hStep
        cases hPrev : @Nat.rec (fun _ => Option Mem) (some m₀)
            (fun i acc =>
              match acc with
              | none => none
              | some mCur =>
                copyRangeComp src
                  { addr := dstAddr, offset := dstOff + i * src.len,
                    len := src.len } mCur) k with
        | none => rw [hPrev] at hStep; cases hStep
        | some mK =>
          rw [hPrev] at hStep
          let ⟨hUpdK, curWin, hGetK⟩ := ih mK (Nat.le_trans (Nat.le_succ k) hK1Le) hPrev
          let ⟨_, _, bs, _, hSet⟩ := copyRangeComp_inv hStep
          let elemLens : ByteSubLens Addr :=
            { addr := dstAddr, offset := dstOff + k * src.len, len := src.len }
          have hSubBound : k * src.len + src.len ≤ n * src.len := by
            rw [← Nat.succ_mul]
            exact Nat.mul_le_mul_right src.len hK1Le
          have hElemZoom : dstWin.zoom (k * src.len) src.len = elemLens := rfl
          have hCont : elemLens.ContainedIn dstWin := by
            rw [← hElemZoom]
            exact ByteSubLens.zoom_containedIn dstWin hSubBound
          have hUpdStep : UpdatesOnly allowed mK mOut :=
            UpdatesOnly.of_contained_set hIn hCont hGetK hSet
          have hGetOut : dstWin.get mOut =
              some (listSplice curWin (k * src.len) bs) :=
            ByteSubLens.get_zoom_set hGetK hSubBound hSet
          exact ⟨hUpdK.trans hUpdStep, _, hGetOut⟩
    exact (hRec n m₁ (Nat.le_refl n) hRep).1

/-- Predicate that a `ByteRunCopyOp` pipeline consists solely of `.copyRange`
operations whose target lenses lie in `allowed`. -/
def CopyOpsTargetsIn (allowed : List (ByteSubLens Addr))
    (copyOps : List (ByteRunCopyOp Addr)) : Prop :=
  ∀ op : ByteRunCopyOp Addr, op ∈ copyOps →
    ∃ src dst : ByteSubLens Addr, op = .copyRange src dst ∧ dst ∈ allowed

/-- Bridge from `execByteRunCopyOps` into `UpdatesOnly` for `.copyRange`
pipelines. -/
theorem UpdatesOnly.of_execByteRunCopyOps_ranges
    {allowed : List (ByteSubLens Addr)} {copyOps : List (ByteRunCopyOp Addr)}
    {m₀ m₁ : Mem}
    (hTargets : CopyOpsTargetsIn allowed copyOps)
    (hExec : execByteRunCopyOps copyOps m₀ = some m₁) :
    UpdatesOnly allowed m₀ m₁ := by
  induction copyOps generalizing m₀ with
  | nil =>
    have hEq : m₀ = m₁ := Option.some.inj hExec
    rw [← hEq]
    exact .refl m₀
  | cons op rest ih =>
    rw [execByteRunCopyOps_cons] at hExec
    let ⟨src, dst, hOpEq, hIn⟩ := hTargets op (List.Mem.head rest)
    rw [hOpEq] at hExec
    dsimp only [ByteRunCopyOp.exec] at hExec
    cases hStep : copyRangeComp src dst m₀ with
    | none => rw [hStep] at hExec; cases hExec
    | some mMid =>
      rw [hStep] at hExec
      exact (UpdatesOnly.of_copyRangeComp hIn hStep).trans
        (ih (fun op' hM => hTargets op' (List.Mem.tail op hM)) hExec)

/-- Bridge from a sealed `ByteRunCopyCut` directly into `UpdatesOnly` (Episode 2
hook connecting `ByteRun` copy stages to `CallSpecCut`'s modification footprint).
-/
theorem ByteRunCopyCut.to_updatesOnly_ranges {S : Type x} {Out : Type y}
    {Fault : Type z} {step : S → StepOutcome S Out Fault} {memOf : S → Mem}
    {allowed : List (ByteSubLens Addr)} {copyOps : List (ByteRunCopyOp Addr)}
    {fuel : Nat} {s₀ s₁ : S}
    (hTargets : CopyOpsTargetsIn allowed copyOps)
    (hCut : ByteRunCopyCut step memOf copyOps fuel s₀ s₁) :
    UpdatesOnly allowed (memOf s₀) (memOf s₁) :=
  UpdatesOnly.of_execByteRunCopyOps_ranges hTargets (ByteRunCopyCut.exec_eq hCut)

/-- Bridge from Part I (`evalRefFrameExit`) into Part II (`UpdatesOnly`): every
non-faulting outcome of `evalRefFrameExit rf mem exit` yields a post-memory
satisfying `UpdatesOnly [rf.refLens] mem mem'`. -/
theorem evalRefFrameExit_updatesOnly {Val : Type w}
    (rf : RefFrame Addr) (mem : Mem) (exit : CalleeExit Val Byte) :
    match evalRefFrameExit rf mem exit with
    | .jumpNormal _ _ mem' => UpdatesOnly [rf.refLens] mem mem'
    | .jumpCleanup _ mem' => UpdatesOnly [rf.refLens] mem mem'
    | .propagateUnwind mem' => UpdatesOnly [rf.refLens] mem mem'
    | .abortTerminate mem' => UpdatesOnly [rf.refLens] mem mem'
    | .fault => True := by
  unfold evalRefFrameExit
  cases exit with
  | returned retVal mutSlice =>
    cases rf.cont.onRet with
    | none => exact True.intro
    | some retBb =>
      dsimp only
      cases hSet : rf.refLens.set mem mutSlice with
      | none => exact True.intro
      | some mem' => exact UpdatesOnly.of_single_set hSet
  | unwound partialSlice =>
    cases rf.cont.onUnwind with
    | unreachable => exact True.intro
    | cleanup _ =>
      dsimp only
      cases hSet : rf.refLens.set mem partialSlice with
      | none => exact True.intro
      | some mem' => exact UpdatesOnly.of_single_set hSet
    | continue_ =>
      dsimp only
      cases hSet : rf.refLens.set mem partialSlice with
      | none => exact True.intro
      | some mem' => exact UpdatesOnly.of_single_set hSet
    | terminate =>
      dsimp only
      cases hSet : rf.refLens.set mem partialSlice with
      | none => exact True.intro
      | some mem' => exact UpdatesOnly.of_single_set hSet

/-- Bridge from Part I (`evalProtectedRefFrameExit`) into Part II
(`UpdatesOnly`): every non-faulting outcome satisfies
`UpdatesOnly [prf.frame.refLens] mem mem'`. -/
theorem evalProtectedRefFrameExit_updatesOnly {Val : Type w}
    (prf : ProtectedRefFrame Addr) (mem : Mem)
    (tree : Anneal.RefFrame.RangedBorrowTree) (exit : CalleeExit Val Byte) :
    match (evalProtectedRefFrameExit prf mem tree exit).1 with
    | .jumpNormal _ _ mem' => UpdatesOnly [prf.frame.refLens] mem mem'
    | .jumpCleanup _ mem' => UpdatesOnly [prf.frame.refLens] mem mem'
    | .propagateUnwind mem' => UpdatesOnly [prf.frame.refLens] mem mem'
    | .abortTerminate mem' => UpdatesOnly [prf.frame.refLens] mem mem'
    | .fault => True := by
  unfold evalProtectedRefFrameExit
  dsimp only
  cases (Anneal.RefFrame.exitFrameWithProtectors tree prf.frameTags).status with
  | Released => exact evalRefFrameExit_updatesOnly prf.frame mem exit
  | MissingTag _ => exact True.intro
  | AccessFailure _ _ _ _ => exact True.intro
  | InvariantFailure _ _ _ => exact True.intro

end UpdatesOnlyLaws

/-- Computable pairwise separation check for a `Nat`-addressed lens list against
a bystander lens `other` (`rfl` decidable). -/
def allNatLensesSeparatedBool (allowed : List (ByteSubLens Nat))
    (other : ByteSubLens Nat) : Bool :=
  allowed.foldr (fun L acc => ByteSubLens.natLensSeparatedBool L other && acc) true

/-- Soundness of `allNatLensesSeparatedBool`: produces store-level pairwise
disjointness for any lawful `Nat`-addressed `ByteStoreOps`. -/
theorem allDisjoint_of_allNatLensesSeparatedBool {Mem : Type u} {Byte : Type a}
    [ops : ByteStoreOps Mem Nat Byte] [LawfulByteStoreOps Mem Nat Byte]
    {allowed : List (ByteSubLens Nat)} {other : ByteSubLens Nat}
    (h : allNatLensesSeparatedBool allowed other = true) :
    ∀ L : ByteSubLens Nat, L ∈ allowed → L.Disjoint Mem other := by
  induction allowed with
  | nil => intro _ hMem; cases hMem
  | cons hd tl ih =>
    unfold allNatLensesSeparatedBool at h
    dsimp only [List.foldr] at h
    have hHd := ByteSubLens.disjoint_of_separated (Mem := Mem)
      (ByteSubLens.separated_of_natLensSeparatedBool (boolAnd_left h))
    have hTl := ih (boolAnd_right h)
    intro L hMem
    cases hMem with
    | head => exact hHd
    | tail _ hInTl => exact hTl L hInTl

/-! ## Part III: `CallSpec`, `StackFrameState`, & `@[irreducible] CallSpecCut` -/

/-- Callee contract over memory `Mem`, address space `Addr`, return value `Val`,
and `Anneal.RefFrame.RangedBorrowTree` protector state. -/
structure CallSpec (Mem : Type u) (Addr : Type v) (Val : Type w) where
  /-- Entry precondition on `(mem, tree)`. -/
  pre : Mem → Anneal.RefFrame.RangedBorrowTree → Prop
  /-- Normal-return postcondition on `(retVal, mem, treeAfterProtectorRelease)`. -/
  postRet : Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop
  /-- Panic-unwind postcondition on `(mem, treeAfterProtectorRelease)` (strictly
  separate from `postRet` so normal postconditions never leak onto cleanup
  paths). -/
  postUnwind : Mem → Anneal.RefFrame.RangedBorrowTree → Prop
  /-- Process-abort (`UnwindAction.terminate`) postcondition on `(mem, tree)`
  when `canAbort = true` (defaults to `fun _ _ => False`). -/
  postAbort : Mem → Anneal.RefFrame.RangedBorrowTree → Prop := fun _ _ => False
  /-- Allowed modification footprint (`UpdatesOnly`). -/
  modifies : List (ByteSubLens Addr)
  /-- Tree Borrows protector tags released on callee frame exit. -/
  frameTags : List Nat
  /-- Whether normal return is permitted by this contract (`false` for
  diverging `-> !` callees). -/
  canNormal : Bool
  /-- Whether panic unwind is permitted by this contract (`false` for
  no-unwind callees). -/
  canUnwind : Bool
  /-- Whether uncatchable process abort (`.abortTerminate`, e.g. from an inner
  `UnwindAction.terminate` boundary) is permitted by this contract (defaults
  to `false`). -/
  canAbort : Bool := false

/-- Pure-boolean constructor for `CallSpec` over a single `&mut` lens
(convenient bridge for `#4177`-style boolean contracts). -/
def CallSpec.ofBool {Mem : Type u} {Addr : Type v} {Byte : Type a}
    {Val : Type w} [ops : ByteStoreOps Mem Addr Byte]
    (mutLens : ByteSubLens Addr) (frameTags : List Nat)
    (preBool : List Byte → Bool)
    (postRetBool : Val → List Byte → Bool)
    (postUnwindBool : List Byte → Bool)
    (canNormal canUnwind : Bool) : CallSpec Mem Addr Val where
  pre m _ := ∃ bs, mutLens.get m = some bs ∧ preBool bs = true
  postRet rv m _ := ∃ bs, mutLens.get m = some bs ∧ postRetBool rv bs = true
  postUnwind m _ := ∃ bs, mutLens.get m = some bs ∧ postUnwindBool bs = true
  modifies := [mutLens]
  frameTags := frameTags
  canNormal := canNormal
  canUnwind := canUnwind

/-- Classified callee exit carrying the post-callee `(mem, tree)` prior to
frame-exit protector release. -/
inductive FrameExitOutcome (Mem : Type u) (Val : Type w) where
  | returned (retVal : Val) (mem : Mem) (tree : Anneal.RefFrame.RangedBorrowTree)
  | unwound (mem : Mem) (tree : Anneal.RefFrame.RangedBorrowTree)
  | abortTerminate (mem : Mem) (tree : Anneal.RefFrame.RangedBorrowTree)

/-- Adapter connecting an abstract `MirWpOps State Out Fault` machine to a
`CallSpec` entry/exit boundary (`0` `Prop` fields). -/
structure CalleeMachineAdapter (State : Type x) (Out : Type y)
    (Mem : Type u) (Val : Type w) where
  /-- Builds the callee entry state from `(mem, tree)`. -/
  mkEntry : Mem → Anneal.RefFrame.RangedBorrowTree → State
  /-- Classifies a machine terminal output into `Option (FrameExitOutcome)`. -/
  classifyOut : Out → Option (FrameExitOutcome Mem Val)

/-- Caller continuation dispatch outcome after frame-exit protector release. -/
inductive CallCont4Dispatch (Mem : Type u) (Val : Type w) where
  | stepNormal (targetBb : Nat) (retVal : Val) (mem : Mem)
      (tree : Anneal.RefFrame.RangedBorrowTree)
  | stepCleanup (cleanupBb : Nat) (mem : Mem)
      (tree : Anneal.RefFrame.RangedBorrowTree)
  | exitUnwind (mem : Mem) (tree : Anneal.RefFrame.RangedBorrowTree)
  | exitTerminate (mem : Mem) (tree : Anneal.RefFrame.RangedBorrowTree)
  | fault

/-- Evaluates the caller-side continuation of a call exit across all 4
`CallCont4` regimes, failing closed on `onRet = none` (`.returned`),
`onUnwind = .unreachable` (`.unwound`), and non-cleanup landing pad blocks
(`isCleanupBb cleanupBb = false`). -/
def evalCallCont4Dispatch {Mem : Type u} {Val : Type w}
    (isCleanupBb : Nat → Bool) (cont : CallCont4)
    (out : FrameExitOutcome Mem Val) : CallCont4Dispatch Mem Val :=
  match out with
  | .returned retVal m t =>
    match cont.onRet with
    | none => .fault
    | some retBb => .stepNormal retBb retVal m t
  | .unwound m t =>
    match cont.onUnwind with
    | .unreachable => .fault
    | .terminate => .exitTerminate m t
    | .continue_ => .exitUnwind m t
    | .cleanup cleanupBb =>
      if isCleanupBb cleanupBb then
        .stepCleanup cleanupBb m t
      else
        .fault
  | .abortTerminate m t => .exitTerminate m t

/-- Fail-closed: `evalCallCont4Dispatch` rejects `.returned` at a diverging call
site (`onRet = none`). -/
theorem evalCallCont4Dispatch_fault_of_onRet_none {Mem : Type u} {Val : Type w}
    (isCleanupBb : Nat → Bool) (uAct : UnwindAction4) (rv : Val) (m : Mem)
    (t : Anneal.RefFrame.RangedBorrowTree) :
    evalCallCont4Dispatch isCleanupBb ⟨none, uAct⟩ (.returned rv m t) = .fault :=
  rfl

/-- Fail-closed: `evalCallCont4Dispatch` rejects `.unwound` when
`onUnwind = .unreachable`. -/
theorem evalCallCont4Dispatch_fault_of_unreachable {Mem : Type u} (Val : Type w)
    (isCleanupBb : Nat → Bool) (onRet : Option Nat) (m : Mem)
    (t : Anneal.RefFrame.RangedBorrowTree) :
    evalCallCont4Dispatch isCleanupBb ⟨onRet, .unreachable⟩
      (FrameExitOutcome.unwound (Val := Val) m t) = .fault :=
  rfl

/-- Fail-closed: `evalCallCont4Dispatch` rejects `.cleanup cleanupBb` when
`isCleanupBb cleanupBb = false`. -/
theorem evalCallCont4Dispatch_fault_of_non_cleanup {Mem : Type u} (Val : Type w)
    (isCleanupBb : Nat → Bool) (onRet : Option Nat) (cleanupBb : Nat) (m : Mem)
    (t : Anneal.RefFrame.RangedBorrowTree)
    (hFalse : isCleanupBb cleanupBb = false) :
    evalCallCont4Dispatch isCleanupBb ⟨onRet, .cleanup cleanupBb⟩
      (FrameExitOutcome.unwound (Val := Val) m t) = .fault := by
  unfold evalCallCont4Dispatch
  dsimp only
  rw [hFalse]
  rfl

/-- Forgets the `RangedBorrowTree` component of a `CallCont4Dispatch`, giving
the `CallerContOutcome` that `evalRefFrameExit` produces for the same
continuation regime. -/
def CallerContOutcome.ofDispatch {Mem : Type u} {Val : Type w} :
    CallCont4Dispatch Mem Val → CallerContOutcome Mem Val
  | .stepNormal targetBb retVal mem _ => .jumpNormal targetBb retVal mem
  | .stepCleanup cleanupBb mem _ => .jumpCleanup cleanupBb mem
  | .exitUnwind mem _ => .propagateUnwind mem
  | .exitTerminate mem _ => .abortTerminate mem
  | .fault => .fault

/-- Agreement between the two call-continuation evaluators of this module: for
a clean protector release and an accepted `&mut` writeback `L.set mem bs =
some mem'`, the Part I `evalProtectedRefFrameExit` (which commits the writeback
itself) and the Part III `evalCallCont4Dispatch` used by `wpCallSite` (which
receives the post-writeback `(mem', tree')`) select the same continuation on
both `.returned` and `.unwound` exits, across all 8 `(onRet, onUnwind)`
regimes. `evalRefFrameExit` does not validate landing pads, so the `.cleanup`
regime needs `isCleanupBb` to accept the pad. -/
theorem evalProtectedRefFrameExit_eq_dispatch {Mem : Type u} {Addr : Type v}
    {Byte : Type a} {Val : Type w} [ops : ByteStoreOps Mem Addr Byte]
    (L : ByteSubLens Addr) (cont : CallCont4) (frameTags : List Nat)
    (isCleanupBb : Nat → Bool) (mem mem' : Mem)
    {tree tree' : Anneal.RefFrame.RangedBorrowTree}
    (retVal : Val) (bs : List Byte)
    (hRel : Anneal.RefFrame.exitFrameWithProtectors tree frameTags =
      ⟨tree', .Released⟩)
    (hSet : L.set mem bs = some mem')
    (hClean : ∀ cleanupBb : Nat, cont.onUnwind = .cleanup cleanupBb →
      isCleanupBb cleanupBb = true) :
    evalProtectedRefFrameExit ⟨⟨L, cont⟩, frameTags⟩ mem tree
        (.returned retVal bs) =
      (CallerContOutcome.ofDispatch
        (evalCallCont4Dispatch isCleanupBb cont (.returned retVal mem' tree')),
       tree') ∧
    evalProtectedRefFrameExit ⟨⟨L, cont⟩, frameTags⟩ mem tree
        (CalleeExit.unwound (Val := Val) bs) =
      (CallerContOutcome.ofDispatch
        (evalCallCont4Dispatch isCleanupBb cont
          (FrameExitOutcome.unwound (Val := Val) mem' tree')),
       tree') := by
  have hW : ∀ ex : CalleeExit Val Byte,
      evalProtectedRefFrameExit ⟨⟨L, cont⟩, frameTags⟩ mem tree ex =
        (evalRefFrameExit ⟨L, cont⟩ mem ex, tree') := fun ex =>
    (evalProtectedRefFrameExit_of_released ⟨⟨L, cont⟩, frameTags⟩ mem ex hRel).1
  rw [hW, hW]
  cases cont with
  | mk onRet onUnwind =>
    refine ⟨?_, ?_⟩
    · cases onRet with
      | none => rfl
      | some retBb =>
        unfold evalRefFrameExit
        dsimp only
        rw [hSet] <;> rfl
    · cases onUnwind with
      | unreachable => rfl
      | terminate =>
        unfold evalRefFrameExit
        dsimp only
        rw [hSet] <;> rfl
      | continue_ =>
        unfold evalRefFrameExit
        dsimp only
        rw [hSet] <;> rfl
      | cleanup cleanupBb =>
        have hC : isCleanupBb cleanupBb = true := hClean cleanupBb rfl
        unfold evalRefFrameExit evalCallCont4Dispatch
        dsimp only
        rw [hSet, hC] <;> rfl

/-- Saved caller frame on the multi-frame call-stack overlay waiting for a
callee return or unwind. -/
structure SavedCallFrame (FrameCtx : Type z) (Addr : Type v) where
  /-- Caller frame-local context (locals, `defId`, return destination, etc.). -/
  ctx : FrameCtx
  /-- 4-way call continuation at the suspended call site. -/
  cont : CallCont4
  /-- Predicate deciding whether a basic block index is a valid cleanup pad. -/
  isCleanupBb : Nat → Bool
  /-- Sub-lenses permitted to be modified within this caller frame. -/
  callerModifies : List (ByteSubLens Addr)
  /-- Tree Borrows protector tags owned by this caller frame (released when an
  unwind propagates past a `.continue_` edge out of this frame). -/
  callerTags : List Nat

/-- Multi-frame call-stack overlay state pairing the active block index and
frame context with saved callers, abstract memory, and `RangedBorrowTree`. -/
structure StackFrameState (FrameCtx : Type z) (Mem : Type u) (Addr : Type v) where
  blockIdx : Nat
  ctx : FrameCtx
  callers : List (SavedCallFrame FrameCtx Addr)
  mem : Mem
  tree : Anneal.RefFrame.RangedBorrowTree

/-- Multi-frame unwind propagation weakest precondition over `callers`:
- empty stack `[]`: exits the modeled call subtree to `onRootUnwind m t`;
- `.unreachable`: fails closed (`False`);
- `.terminate`: aborts cleanly via `onAbortTerminate m t`;
- `.cleanup cleanupBb`: checks `isCleanupBb cleanupBb = true` (failing closed
  otherwise) and resumes in `StackFrameState ⟨cleanupBb, saved.ctx, rest, m, t⟩`;
- `.continue_`: releases `saved.callerTags` via
  `Anneal.RefFrame.exitFrameWithProtectors t saved.callerTags` (failing closed
  on `.MissingTag` / `.AccessFailure` / `.InvariantFailure`) and continues
  propagating to `rest`. -/
def wpUnwindStack {FrameCtx : Type z} {Mem : Type u} {Addr : Type v}
    (onCleanupFrame : StackFrameState FrameCtx Mem Addr → Prop)
    (onRootUnwind : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onAbortTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop) :
    List (SavedCallFrame FrameCtx Addr) → Mem →
      Anneal.RefFrame.RangedBorrowTree → Prop
  | [], m, t => onRootUnwind m t
  | saved :: rest, m, t =>
    match saved.cont.onUnwind with
    | .unreachable => False
    | .terminate => onAbortTerminate m t
    | .cleanup cleanupBb =>
      if saved.isCleanupBb cleanupBb then
        onCleanupFrame ⟨cleanupBb, saved.ctx, rest, m, t⟩
      else
        False
    | .continue_ =>
      match Anneal.RefFrame.exitFrameWithProtectors t saved.callerTags with
      | ⟨t', .Released⟩ =>
        wpUnwindStack onCleanupFrame onRootUnwind onAbortTerminate rest m t'
      | ⟨_, .MissingTag _⟩ => False
      | ⟨_, .AccessFailure _ _ _ _⟩ => False
      | ⟨_, .InvariantFailure _ _ _⟩ => False

/-- Predicate that a chain of `.continue_` caller frames cleanly releases all
intermediate protector tags sequentially from `t₀` to `tFinal`, accumulating
every stripped tag. -/
def ContinueChainReleases {FrameCtx : Type z} {Addr : Type v} :
    List (SavedCallFrame FrameCtx Addr) →
      Anneal.RefFrame.RangedBorrowTree →
      Anneal.RefFrame.RangedBorrowTree → Prop
  | [], t₀, tFinal => tFinal = t₀
  | saved :: rest, t₀, tFinal =>
    saved.cont.onUnwind = .continue_ ∧
    ∃ tMid : Anneal.RefFrame.RangedBorrowTree,
      Anneal.RefFrame.exitFrameWithProtectors t₀ saved.callerTags =
        ⟨tMid, .Released⟩ ∧
      ContinueChainReleases rest tMid tFinal

/-- Propagates an unwind through a `ContinueChainReleases` prefix of `.continue_`
frames directly to `suffix` at `(m, tFinal)`. -/
theorem wpUnwindStack_append_continue_chain {FrameCtx : Type z} {Mem : Type u}
    {Addr : Type v}
    {onCleanupFrame : StackFrameState FrameCtx Mem Addr → Prop}
    {onRootUnwind : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onAbortTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {prefixFrames suffixFrames : List (SavedCallFrame FrameCtx Addr)}
    {m : Mem} {t₀ tFinal : Anneal.RefFrame.RangedBorrowTree}
    (hChain : ContinueChainReleases prefixFrames t₀ tFinal)
    (hSuffix : wpUnwindStack onCleanupFrame onRootUnwind onAbortTerminate
      suffixFrames m tFinal) :
    wpUnwindStack onCleanupFrame onRootUnwind onAbortTerminate
      (prefixFrames ++ suffixFrames) m t₀ := by
  induction prefixFrames generalizing t₀ with
  | nil =>
    cases hChain
    exact hSuffix
  | cons saved rest ih =>
    let ⟨hCont, tMid, hRel, hRest⟩ := hChain
    dsimp only [List.cons_append, wpUnwindStack]
    rw [hCont, hRel]
    exact ih hRest

/-- Every tag owned by a frame in a `ContinueChainReleases` prefix that is not
re-introduced is stripped in `tFinal.protectedTags` (since
`exitFrameWithProtectors` is strictly tag-shrinking). -/
theorem continueChainReleases_strips_tags {FrameCtx : Type z} {Addr : Type v}
    {prefixFrames : List (SavedCallFrame FrameCtx Addr)}
    {t₀ tFinal : Anneal.RefFrame.RangedBorrowTree}
    (hChain : ContinueChainReleases prefixFrames t₀ tFinal) :
    ∀ (t : Nat),
      (Anneal.RefFrame.natListMem t t₀.protectedTags = false →
        Anneal.RefFrame.natListMem t tFinal.protectedTags = false) ∧
      (∀ fr : SavedCallFrame FrameCtx Addr, fr ∈ prefixFrames →
        Anneal.RefFrame.natListMem t fr.callerTags = true →
        Anneal.RefFrame.natListMem t tFinal.protectedTags = false) := by
  induction prefixFrames generalizing t₀ with
  | nil =>
    cases hChain
    intro t
    exact ⟨fun h => h, fun _ hMem => False.elim (by cases hMem)⟩
  | cons saved rest ih =>
    let ⟨_, tMid, hRel, hRest⟩ := hChain
    have hStepTags := exitFrameWithProtectors_released_tags hRel
    have hIh := ih hRest
    intro t
    refine ⟨?_, ?_⟩
    · intro hAbsent
      have hMidAbsent : Anneal.RefFrame.natListMem t tMid.protectedTags = false := by
        cases hIn : Anneal.RefFrame.natListMem t saved.callerTags with
        | true => exact hStepTags.1 t hIn
        | false => rw [hStepTags.2 t hIn]; exact hAbsent
      exact (hIh t).1 hMidAbsent
    · intro fr hMem hInFr
      cases hMem with
      | head =>
        exact (hIh t).1 (hStepTags.1 t hInFr)
      | tail _ hInRest =>
        exact (hIh t).2 fr hInRest hInFr

/-- Terminal result of propagating a panic unwind through saved caller frames
(`evalUnwindStack`). -/
inductive UnwindStackResult (FrameCtx : Type z) (Mem : Type u) (Addr : Type v) where
  /-- Landed on a validated cleanup pad of a caller frame. -/
  | landed (st : StackFrameState FrameCtx Mem Addr)
  /-- Propagated past every saved frame out of the modeled call subtree. -/
  | rootUnwind (mem : Mem) (tree : Anneal.RefFrame.RangedBorrowTree)
  /-- Hit a `.terminate` unwind edge (process abort). -/
  | abortTerminate (mem : Mem) (tree : Anneal.RefFrame.RangedBorrowTree)
  /-- `.unreachable` edge, invalid cleanup pad, or failed protector release. -/
  | fault

/-- Computable operational unwinder over the saved caller frames: pops frames
while their unwind edge is `.continue_` (releasing each frame's `callerTags`
via `Anneal.RefFrame.exitFrameWithProtectors`), stops on the first `.cleanup`
pad (validated by `isCleanupBb`), `.terminate`, or an empty stack, and faults
on `.unreachable`, an invalid pad, or a failed protector release. -/
def evalUnwindStack {FrameCtx : Type z} {Mem : Type u} {Addr : Type v} :
    List (SavedCallFrame FrameCtx Addr) → Mem →
      Anneal.RefFrame.RangedBorrowTree → UnwindStackResult FrameCtx Mem Addr
  | [], m, t => .rootUnwind m t
  | saved :: rest, m, t =>
    match saved.cont.onUnwind with
    | .unreachable => .fault
    | .terminate => .abortTerminate m t
    | .cleanup cleanupBb =>
      if saved.isCleanupBb cleanupBb then
        .landed ⟨cleanupBb, saved.ctx, rest, m, t⟩
      else
        .fault
    | .continue_ =>
      match Anneal.RefFrame.exitFrameWithProtectors t saved.callerTags with
      | ⟨t', .Released⟩ => evalUnwindStack rest m t'
      | ⟨_, .MissingTag _⟩ => .fault
      | ⟨_, .AccessFailure _ _ _ _⟩ => .fault
      | ⟨_, .InvariantFailure _ _ _⟩ => .fault

/-- Postcondition reading of an `UnwindStackResult` (`.fault ↦ False`). -/
def UnwindStackResult.holds {FrameCtx : Type z} {Mem : Type u} {Addr : Type v}
    (onCleanupFrame : StackFrameState FrameCtx Mem Addr → Prop)
    (onRootUnwind : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onAbortTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop) :
    UnwindStackResult FrameCtx Mem Addr → Prop
  | .landed st => onCleanupFrame st
  | .rootUnwind m t => onRootUnwind m t
  | .abortTerminate m t => onAbortTerminate m t
  | .fault => False

/-- Operational adequacy of `wpUnwindStack`: the weakest precondition holds
exactly when the computable unwinder `evalUnwindStack` produces a result
satisfying the corresponding continuation (and never when it faults). -/
theorem wpUnwindStack_iff_evalUnwindStack {FrameCtx : Type z} {Mem : Type u}
    {Addr : Type v}
    (onCleanupFrame : StackFrameState FrameCtx Mem Addr → Prop)
    (onRootUnwind : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onAbortTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (frames : List (SavedCallFrame FrameCtx Addr)) (m : Mem)
    (t : Anneal.RefFrame.RangedBorrowTree) :
    wpUnwindStack onCleanupFrame onRootUnwind onAbortTerminate frames m t ↔
      (evalUnwindStack frames m t).holds onCleanupFrame onRootUnwind
        onAbortTerminate := by
  induction frames generalizing t with
  | nil => exact Iff.rfl
  | cons saved rest ih =>
    cases hU : saved.cont.onUnwind with
    | unreachable =>
      dsimp only [wpUnwindStack, evalUnwindStack]
      rw [hU]
      exact Iff.rfl
    | terminate =>
      dsimp only [wpUnwindStack, evalUnwindStack]
      rw [hU]
      exact Iff.rfl
    | cleanup cleanupBb =>
      dsimp only [wpUnwindStack, evalUnwindStack]
      rw [hU]
      dsimp only
      cases saved.isCleanupBb cleanupBb with
      | true => exact Iff.rfl
      | false => exact Iff.rfl
    | continue_ =>
      dsimp only [wpUnwindStack, evalUnwindStack]
      rw [hU]
      dsimp only
      cases Anneal.RefFrame.exitFrameWithProtectors t saved.callerTags with
      | mk t' st =>
        cases st with
        | Released => exact ih t'
        | MissingTag _ => exact Iff.rfl
        | AccessFailure _ _ _ _ => exact Iff.rfl
        | InvariantFailure _ _ _ => exact Iff.rfl

/-- Operational chain rule: a `ContinueChainReleases` prefix is transparent to
`evalUnwindStack`, which resumes on the suffix with the released tree. -/
theorem evalUnwindStack_append_continue_chain {FrameCtx : Type z} {Mem : Type u}
    {Addr : Type v}
    {prefixFrames suffixFrames : List (SavedCallFrame FrameCtx Addr)}
    {m : Mem} {t₀ tFinal : Anneal.RefFrame.RangedBorrowTree}
    (hChain : ContinueChainReleases prefixFrames t₀ tFinal) :
    evalUnwindStack (prefixFrames ++ suffixFrames) m t₀ =
      evalUnwindStack suffixFrames m tFinal := by
  induction prefixFrames generalizing t₀ with
  | nil =>
    cases hChain
    rfl
  | cons saved rest ih =>
    let ⟨hCont, tMid, hRel, hRest⟩ := hChain
    dsimp only [List.cons_append, evalUnwindStack]
    rw [hCont]
    dsimp only
    rw [hRel]
    exact ih hRest

/-- Unwind propagation never writes memory: every non-faulting result of
`evalUnwindStack frames m t` carries the input memory `m` unchanged, and a
landing frame is a validated cleanup pad (`isCleanupBb = true`) of one of the
saved frames whose remaining callers are a suffix of `frames`. -/
theorem evalUnwindStack_preserves_mem {FrameCtx : Type z} {Mem : Type u}
    {Addr : Type v} (frames : List (SavedCallFrame FrameCtx Addr)) (m : Mem)
    (t : Anneal.RefFrame.RangedBorrowTree) :
    match evalUnwindStack frames m t with
    | .landed st =>
      st.mem = m ∧
        ∃ saved : SavedCallFrame FrameCtx Addr, saved ∈ frames ∧
          saved.cont.onUnwind = .cleanup st.blockIdx ∧
          saved.isCleanupBb st.blockIdx = true ∧ saved.ctx = st.ctx ∧
          ∃ pre : List (SavedCallFrame FrameCtx Addr),
            frames = pre ++ saved :: st.callers
    | .rootUnwind m' _ => m' = m
    | .abortTerminate m' _ => m' = m
    | .fault => True := by
  induction frames generalizing t with
  | nil => rfl
  | cons saved rest ih =>
    cases hU : saved.cont.onUnwind with
    | unreachable =>
      dsimp only [evalUnwindStack]
      rw [hU]
      trivial
    | terminate =>
      dsimp only [evalUnwindStack]
      rw [hU]
    | cleanup cleanupBb =>
      dsimp only [evalUnwindStack]
      rw [hU]
      dsimp only
      cases hB : saved.isCleanupBb cleanupBb with
      | false => trivial
      | true =>
        exact ⟨rfl, saved, List.Mem.head _, hU, hB, rfl, [], rfl⟩
    | continue_ =>
      dsimp only [evalUnwindStack]
      rw [hU]
      dsimp only
      cases Anneal.RefFrame.exitFrameWithProtectors t saved.callerTags with
      | mk t' st =>
        cases st with
        | MissingTag _ => trivial
        | AccessFailure _ _ _ _ => trivial
        | InvariantFailure _ _ _ => trivial
        | Released =>
          have h := ih t'
          dsimp only
          revert h
          cases evalUnwindStack rest m t' with
          | landed st =>
            intro ⟨hMem, sv, hIn, hEdge, hValid, hCtx, pre, hSplit⟩
            exact ⟨hMem, sv, List.Mem.tail _ hIn, hEdge, hValid, hCtx,
              saved :: pre, by rw [hSplit]; rfl⟩
          | rootUnwind _ _ => exact id
          | abortTerminate _ _ => exact id
          | fault => exact id

/-- Call-site weakest precondition over `[wops : MirWpOps State Out Fault]`:
starting at `adapter.mkEntry m₀ t₀`, the callee terminates without faulting,
its exit releases `frameTags` cleanly via `exitFrameWithProtectors`, and the
resulting `evalCallCont4Dispatch` satisfies the active caller continuation
(`onNormal`, `onCleanup`, `onUnwindExit`, or `onTerminate`). -/
def wpCallSite {State : Type x} {Out : Type y} {Fault : Type z}
    {Mem : Type u} {Val : Type w}
    [wops : MirWpOps State Out Fault]
    (adapter : CalleeMachineAdapter State Out Mem Val)
    (cont : CallCont4) (isCleanupBb : Nat → Bool) (frameTags : List Nat)
    (onNormal : Nat → Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onCleanup : Nat → Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onUnwindExit : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (m₀ : Mem) (t₀ : Anneal.RefFrame.RangedBorrowTree) : Prop :=
  wpOutcome (ops := wops)
    (fun out =>
      match adapter.classifyOut out with
      | none => False
      | some (.returned retVal m₁ t₁) =>
        match Anneal.RefFrame.exitFrameWithProtectors t₁ frameTags with
        | ⟨tRel, .Released⟩ =>
          match evalCallCont4Dispatch isCleanupBb cont
              (.returned retVal m₁ tRel) with
          | .stepNormal retBb rv m' t' => onNormal retBb rv m' t'
          | _ => False
        | _ => False
      | some (.unwound m₁ t₁) =>
        match Anneal.RefFrame.exitFrameWithProtectors t₁ frameTags with
        | ⟨tRel, .Released⟩ =>
          match evalCallCont4Dispatch isCleanupBb cont
              (FrameExitOutcome.unwound (Val := Val) m₁ tRel) with
          | .stepCleanup cleanupBb m' t' => onCleanup cleanupBb m' t'
          | .exitUnwind m' t' => onUnwindExit m' t'
          | .exitTerminate m' t' => onTerminate m' t'
          | _ => False
        | _ => False
      | some (.abortTerminate m₁ t₁) =>
        match evalCallCont4Dispatch isCleanupBb cont
            (FrameExitOutcome.abortTerminate (Val := Val) m₁ t₁) with
        | .exitTerminate m' t' => onTerminate m' t'
        | _ => False)
    (fun _ => False)
    (adapter.mkEntry m₀ t₀)

section CallSpecCutSec

variable {State : Type x} {Out : Type y} {Fault : Type z}
  {Mem : Type u} {Addr : Type v} {Byte : Type a} {Val : Type w}

/-- Unsealed denotation of `CallSpecCut` (`0` bare `Prop` arguments): for every
`(m₀, t₀)` satisfying `spec.pre m₀ t₀`, `wpOutcome` from `adapter.mkEntry m₀ t₀`
forbids faults and certifies that:
- normal returns satisfy `spec.canNormal = true`, `UpdatesOnly spec.modifies
  m₀ m₁`, clean `exitFrameWithProtectors t₁ spec.frameTags = ⟨tRel, .Released⟩`,
  and `spec.postRet retVal m₁ tRel`;
- panic unwinds satisfy `spec.canUnwind = true`, `UpdatesOnly spec.modifies
  m₀ m₁`, clean `exitFrameWithProtectors t₁ spec.frameTags = ⟨tRel, .Released⟩`,
  and `spec.postUnwind m₁ tRel`;
- process aborts (`.abortTerminate`) satisfy `spec.canAbort = true`,
  `UpdatesOnly spec.modifies m₀ m₁`, and `spec.postAbort m₁ t₁` (aborting
  immediately without unwinding or releasing outer protectors). -/
def denoteCallSpecCut [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    (adapter : CalleeMachineAdapter State Out Mem Val)
    (spec : CallSpec Mem Addr Val) : Prop :=
  ∀ (m₀ : Mem) (t₀ : Anneal.RefFrame.RangedBorrowTree),
    spec.pre m₀ t₀ →
    wpOutcome (ops := wops)
      (fun out =>
        match adapter.classifyOut out with
        | none => False
        | some (.returned retVal m₁ t₁) =>
          spec.canNormal = true ∧
          UpdatesOnly spec.modifies m₀ m₁ ∧
          ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
            Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
              ⟨tRel, .Released⟩ ∧
            spec.postRet retVal m₁ tRel
        | some (.unwound m₁ t₁) =>
          spec.canUnwind = true ∧
          UpdatesOnly spec.modifies m₀ m₁ ∧
          ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
            Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
              ⟨tRel, .Released⟩ ∧
            spec.postUnwind m₁ tRel
        | some (.abortTerminate m₁ t₁) =>
          spec.canAbort = true ∧
          UpdatesOnly spec.modifies m₀ m₁ ∧
          spec.postAbort m₁ t₁)
      (fun _ => False)
      (adapter.mkEntry m₀ t₀)

/-- Zero-`Prop`-argument modular call contract barrier (`@[irreducible]` below
after proving its seal, unseal, call-site WP, unwind-chain, framing, and
`StageCut` laws). -/
def CallSpecCut [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    (adapter : CalleeMachineAdapter State Out Mem Val)
    (spec : CallSpec Mem Addr Val) : Prop :=
  denoteCallSpecCut adapter spec

/-- Seals a `denoteCallSpecCut` proof behind `CallSpecCut`. -/
theorem seal_callSpecCut [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    (h : denoteCallSpecCut (wops := wops) (ops := ops) adapter spec) :
    CallSpecCut (wops := wops) (ops := ops) adapter spec :=
  h

/-- Unseals `CallSpecCut` into `denoteCallSpecCut`. -/
theorem open_callSpecCut [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    (h : CallSpecCut (wops := wops) (ops := ops) adapter spec) :
    denoteCallSpecCut (wops := wops) (ops := ops) adapter spec :=
  h

/-- Modular call-site WP rule for `⟨some retBb, .cleanup cleanupBb⟩`:
normal returns jump to `retBb` with `spec.postRet`, `UpdatesOnly`, and stripped
`frameTags`; unwinds jump to `cleanupBb` with `spec.postUnwind`, `UpdatesOnly`,
and stripped `frameTags` (never leaking `spec.postRet` onto cleanup paths). -/
theorem callSpecCut_call_normal_cleanup [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    {isCleanupBb : Nat → Bool} {retBb cleanupBb : Nat}
    {onNormal : Nat → Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onCleanup : Nat → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onUnwindExit : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {m₀ : Mem} {t₀ : Anneal.RefFrame.RangedBorrowTree}
    (hCut : CallSpecCut adapter spec)
    (hPre : spec.pre m₀ t₀)
    (hCleanValid : isCleanupBb cleanupBb = true)
    (hNormal : ∀ (retVal : Val) (m₁ : Mem) (tRel : Anneal.RefFrame.RangedBorrowTree),
      spec.canNormal = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t : Nat, Anneal.RefFrame.natListMem t spec.frameTags = true →
        Anneal.RefFrame.natListMem t tRel.protectedTags = false) →
      spec.postRet retVal m₁ tRel →
      onNormal retBb retVal m₁ tRel)
    (hCleanup : ∀ (m₁ : Mem) (tRel : Anneal.RefFrame.RangedBorrowTree),
      spec.canUnwind = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t : Nat, Anneal.RefFrame.natListMem t spec.frameTags = true →
        Anneal.RefFrame.natListMem t tRel.protectedTags = false) →
      spec.postUnwind m₁ tRel →
      onCleanup cleanupBb m₁ tRel)
    (hAbort : ∀ (m₁ : Mem) (t₁ : Anneal.RefFrame.RangedBorrowTree),
      spec.canAbort = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      spec.postAbort m₁ t₁ →
      onTerminate m₁ t₁) :
    wpCallSite adapter ⟨some retBb, .cleanup cleanupBb⟩ isCleanupBb
      spec.frameTags onNormal onCleanup onUnwindExit onTerminate m₀ t₀ := by
  unfold wpCallSite wpOutcome
  refine wpUntil_mono (ops := wops) (fun _ hf => hf) ?_ (fun _ hf => hf)
    (hCut m₀ t₀ hPre)
  intro out hOut
  cases hCls : adapter.classifyOut out with
  | none => rw [hCls] at hOut; exact False.elim hOut
  | some ex =>
    rw [hCls] at hOut
    cases ex with
    | returned retVal m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanN, hUpd, tRel, hRel, hPost⟩ := hOut
      rw [hRel]
      have hStripped := (exitFrameWithProtectors_released_tags hRel).1
      exact hNormal retVal m₁ tRel hCanN hUpd hStripped hPost
    | unwound m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanU, hUpd, tRel, hRel, hPost⟩ := hOut
      rw [hRel]
      unfold evalCallCont4Dispatch
      dsimp only
      rw [hCleanValid]
      have hStripped := (exitFrameWithProtectors_released_tags hRel).1
      exact hCleanup m₁ tRel hCanU hUpd hStripped hPost
    | abortTerminate m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanA, hUpd, hPost⟩ := hOut
      exact hAbort m₁ t₁ hCanA hUpd hPost

/-- Modular call-site WP rule for `⟨some retBb, .continue_⟩`:
normal returns jump to `retBb` with `spec.postRet`, unwinds exit the
caller frame via `onUnwindExit` with `spec.postUnwind`, `UpdatesOnly`, and
stripped `frameTags`, and callee process aborts route to `onTerminate`. -/
theorem callSpecCut_call_normal_continue [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    {isCleanupBb : Nat → Bool} {retBb : Nat}
    {onNormal : Nat → Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onCleanup : Nat → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onUnwindExit : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {m₀ : Mem} {t₀ : Anneal.RefFrame.RangedBorrowTree}
    (hCut : CallSpecCut adapter spec)
    (hPre : spec.pre m₀ t₀)
    (hNormal : ∀ (retVal : Val) (m₁ : Mem) (tRel : Anneal.RefFrame.RangedBorrowTree),
      spec.canNormal = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t : Nat, Anneal.RefFrame.natListMem t spec.frameTags = true →
        Anneal.RefFrame.natListMem t tRel.protectedTags = false) →
      spec.postRet retVal m₁ tRel →
      onNormal retBb retVal m₁ tRel)
    (hUnwind : ∀ (m₁ : Mem) (tRel : Anneal.RefFrame.RangedBorrowTree),
      spec.canUnwind = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t : Nat, Anneal.RefFrame.natListMem t spec.frameTags = true →
        Anneal.RefFrame.natListMem t tRel.protectedTags = false) →
      spec.postUnwind m₁ tRel →
      onUnwindExit m₁ tRel)
    (hAbort : ∀ (m₁ : Mem) (t₁ : Anneal.RefFrame.RangedBorrowTree),
      spec.canAbort = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      spec.postAbort m₁ t₁ →
      onTerminate m₁ t₁) :
    wpCallSite adapter ⟨some retBb, .continue_⟩ isCleanupBb
      spec.frameTags onNormal onCleanup onUnwindExit onTerminate m₀ t₀ := by
  unfold wpCallSite wpOutcome
  refine wpUntil_mono (ops := wops) (fun _ hf => hf) ?_ (fun _ hf => hf)
    (hCut m₀ t₀ hPre)
  intro out hOut
  cases hCls : adapter.classifyOut out with
  | none => rw [hCls] at hOut; exact False.elim hOut
  | some ex =>
    rw [hCls] at hOut
    cases ex with
    | returned retVal m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanN, hUpd, tRel, hRel, hPost⟩ := hOut
      rw [hRel]
      exact hNormal retVal m₁ tRel hCanN hUpd
        (exitFrameWithProtectors_released_tags hRel).1 hPost
    | unwound m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanU, hUpd, tRel, hRel, hPost⟩ := hOut
      rw [hRel]
      exact hUnwind m₁ tRel hCanU hUpd
        (exitFrameWithProtectors_released_tags hRel).1 hPost
    | abortTerminate m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanA, hUpd, hPost⟩ := hOut
      exact hAbort m₁ t₁ hCanA hUpd hPost

/-- Modular call-site WP rule for `⟨some retBb, .terminate⟩`:
normal returns jump to `retBb` with `spec.postRet`; both callee unwinds (after
protector release) and callee aborts route to `onTerminate`. -/
theorem callSpecCut_call_normal_terminate [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    {isCleanupBb : Nat → Bool} {retBb : Nat}
    {onNormal : Nat → Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onCleanup : Nat → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onUnwindExit : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {m₀ : Mem} {t₀ : Anneal.RefFrame.RangedBorrowTree}
    (hCut : CallSpecCut adapter spec)
    (hPre : spec.pre m₀ t₀)
    (hNormal : ∀ (retVal : Val) (m₁ : Mem) (tRel : Anneal.RefFrame.RangedBorrowTree),
      spec.canNormal = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t : Nat, Anneal.RefFrame.natListMem t spec.frameTags = true →
        Anneal.RefFrame.natListMem t tRel.protectedTags = false) →
      spec.postRet retVal m₁ tRel →
      onNormal retBb retVal m₁ tRel)
    (hUnwindTerm : ∀ (m₁ : Mem) (tRel : Anneal.RefFrame.RangedBorrowTree),
      spec.canUnwind = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t : Nat, Anneal.RefFrame.natListMem t spec.frameTags = true →
        Anneal.RefFrame.natListMem t tRel.protectedTags = false) →
      spec.postUnwind m₁ tRel →
      onTerminate m₁ tRel)
    (hAbort : ∀ (m₁ : Mem) (t₁ : Anneal.RefFrame.RangedBorrowTree),
      spec.canAbort = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      spec.postAbort m₁ t₁ →
      onTerminate m₁ t₁) :
    wpCallSite adapter ⟨some retBb, .terminate⟩ isCleanupBb
      spec.frameTags onNormal onCleanup onUnwindExit onTerminate m₀ t₀ := by
  unfold wpCallSite wpOutcome
  refine wpUntil_mono (ops := wops) (fun _ hf => hf) ?_ (fun _ hf => hf)
    (hCut m₀ t₀ hPre)
  intro out hOut
  cases hCls : adapter.classifyOut out with
  | none => rw [hCls] at hOut; exact False.elim hOut
  | some ex =>
    rw [hCls] at hOut
    cases ex with
    | returned retVal m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanN, hUpd, tRel, hRel, hPost⟩ := hOut
      rw [hRel]
      exact hNormal retVal m₁ tRel hCanN hUpd
        (exitFrameWithProtectors_released_tags hRel).1 hPost
    | unwound m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanU, hUpd, tRel, hRel, hPost⟩ := hOut
      rw [hRel]
      exact hUnwindTerm m₁ tRel hCanU hUpd
        (exitFrameWithProtectors_released_tags hRel).1 hPost
    | abortTerminate m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanA, hUpd, hPost⟩ := hOut
      exact hAbort m₁ t₁ hCanA hUpd hPost

/-- Modular call-site WP rule for no-unwind calls (`spec.canUnwind = false`) at
`⟨some retBb, uAct⟩` (covering `.unreachable`, `.terminate`, `.continue_`, or
`.cleanup` when the callee statically cannot unwind). -/
theorem callSpecCut_call_normal_no_unwind [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    {isCleanupBb : Nat → Bool} {retBb : Nat} {uAct : UnwindAction4}
    {onNormal : Nat → Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onCleanup : Nat → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onUnwindExit : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {m₀ : Mem} {t₀ : Anneal.RefFrame.RangedBorrowTree}
    (hCut : CallSpecCut adapter spec)
    (hPre : spec.pre m₀ t₀)
    (hNoUnw : spec.canUnwind = false)
    (hNormal : ∀ (retVal : Val) (m₁ : Mem) (tRel : Anneal.RefFrame.RangedBorrowTree),
      spec.canNormal = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t : Nat, Anneal.RefFrame.natListMem t spec.frameTags = true →
        Anneal.RefFrame.natListMem t tRel.protectedTags = false) →
      spec.postRet retVal m₁ tRel →
      onNormal retBb retVal m₁ tRel)
    (hAbort : ∀ (m₁ : Mem) (t₁ : Anneal.RefFrame.RangedBorrowTree),
      spec.canAbort = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      spec.postAbort m₁ t₁ →
      onTerminate m₁ t₁) :
    wpCallSite adapter ⟨some retBb, uAct⟩ isCleanupBb
      spec.frameTags onNormal onCleanup onUnwindExit onTerminate m₀ t₀ := by
  unfold wpCallSite wpOutcome
  refine wpUntil_mono (ops := wops) (fun _ hf => hf) ?_ (fun _ hf => hf)
    (hCut m₀ t₀ hPre)
  intro out hOut
  cases hCls : adapter.classifyOut out with
  | none => rw [hCls] at hOut; exact False.elim hOut
  | some ex =>
    rw [hCls] at hOut
    cases ex with
    | returned retVal m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanN, hUpd, tRel, hRel, hPost⟩ := hOut
      rw [hRel]
      exact hNormal retVal m₁ tRel hCanN hUpd
        (exitFrameWithProtectors_released_tags hRel).1 hPost
    | unwound _ _ =>
      rw [hNoUnw] at hOut
      cases hOut.1
    | abortTerminate m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanA, hUpd, hPost⟩ := hOut
      exact hAbort m₁ t₁ hCanA hUpd hPost

/-- Modular call-site WP rule for diverging `-> !` calls (`onRet = none`,
`spec.canNormal = false`): normal return is statically excluded, unwind
paths discharge `.cleanup`, `.continue_`, or `.terminate` cleanly (while
`.unreachable` remains excluded unless `spec.canUnwind = false`), and callee
process aborts route to `onTerminate`. -/
theorem callSpecCut_call_diverging_unwind [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    {isCleanupBb : Nat → Bool} {uAct : UnwindAction4}
    {onNormal : Nat → Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onCleanup : Nat → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onUnwindExit : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {m₀ : Mem} {t₀ : Anneal.RefFrame.RangedBorrowTree}
    (hCut : CallSpecCut adapter spec)
    (hPre : spec.pre m₀ t₀)
    (hDiv : spec.canNormal = false)
    (hUnwind : ∀ (m₁ : Mem) (tRel : Anneal.RefFrame.RangedBorrowTree),
      spec.canUnwind = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t : Nat, Anneal.RefFrame.natListMem t spec.frameTags = true →
        Anneal.RefFrame.natListMem t tRel.protectedTags = false) →
      spec.postUnwind m₁ tRel →
      match uAct with
      | .cleanup cleanupBb =>
        isCleanupBb cleanupBb = true ∧ onCleanup cleanupBb m₁ tRel
      | .continue_ => onUnwindExit m₁ tRel
      | .terminate => onTerminate m₁ tRel
      | .unreachable => False)
    (hAbort : ∀ (m₁ : Mem) (t₁ : Anneal.RefFrame.RangedBorrowTree),
      spec.canAbort = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      spec.postAbort m₁ t₁ →
      onTerminate m₁ t₁) :
    wpCallSite adapter ⟨none, uAct⟩ isCleanupBb
      spec.frameTags onNormal onCleanup onUnwindExit onTerminate m₀ t₀ := by
  unfold wpCallSite wpOutcome
  refine wpUntil_mono (ops := wops) (fun _ hf => hf) ?_ (fun _ hf => hf)
    (hCut m₀ t₀ hPre)
  intro out hOut
  cases hCls : adapter.classifyOut out with
  | none => rw [hCls] at hOut; exact False.elim hOut
  | some ex =>
    rw [hCls] at hOut
    cases ex with
    | returned _ _ _ =>
      rw [hDiv] at hOut
      cases hOut.1
    | unwound m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanU, hUpd, tRel, hRel, hPost⟩ := hOut
      rw [hRel]
      have hU := hUnwind m₁ tRel hCanU hUpd
        (exitFrameWithProtectors_released_tags hRel).1 hPost
      cases uAct with
      | unreachable => exact hU
      | continue_ => exact hU
      | terminate => exact hU
      | cleanup cleanupBb =>
        unfold evalCallCont4Dispatch
        dsimp only
        rw [hU.1]
        exact hU.2
    | abortTerminate m₁ t₁ =>
      dsimp only at hOut ⊢
      let ⟨hCanA, hUpd, hPost⟩ := hOut
      exact hAbort m₁ t₁ hCanA hUpd hPost

/-- Multi-frame unwind propagation chain rule (`StackFrameState`): when a
callee satisfies `CallSpecCut` at a `.continue_` call site and its unwind
propagates across a chain of `.continue_` caller frames (`prefixFrames`)
releasing each frame's `callerTags` sequentially via `exitFrameWithProtectors`
into `suffixFrames`, the combined call site discharges normal return,
multi-frame `wpUnwindStack`, and callee aborts while preserving
`UpdatesOnly spec.modifies m₀ m₁` and stripping all callee + intermediate
caller protector tags. -/
theorem callSpecCut_unwind_propagate_chain {FrameCtx : Type b}
    [wops : MirWpOps State Out Fault] [ops : ByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    {isCleanupBb : Nat → Bool} {retBb : Nat}
    {prefixFrames suffixFrames : List (SavedCallFrame FrameCtx Addr)}
    {onNormal : Nat → Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onCleanup : Nat → Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onCleanupFrame : StackFrameState FrameCtx Mem Addr → Prop}
    {onRootUnwind : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {onAbortTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop}
    {m₀ : Mem} {t₀ : Anneal.RefFrame.RangedBorrowTree}
    (hCut : CallSpecCut adapter spec)
    (hPre : spec.pre m₀ t₀)
    (hNormal : ∀ (retVal : Val) (m₁ : Mem) (tRel : Anneal.RefFrame.RangedBorrowTree),
      spec.canNormal = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t : Nat, Anneal.RefFrame.natListMem t spec.frameTags = true →
        Anneal.RefFrame.natListMem t tRel.protectedTags = false) →
      spec.postRet retVal m₁ tRel →
      onNormal retBb retVal m₁ tRel)
    (hChain : ∀ (m₁ : Mem) (tRel : Anneal.RefFrame.RangedBorrowTree),
      spec.canUnwind = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      (∀ t : Nat, Anneal.RefFrame.natListMem t spec.frameTags = true →
        Anneal.RefFrame.natListMem t tRel.protectedTags = false) →
      spec.postUnwind m₁ tRel →
      ∃ tFinal : Anneal.RefFrame.RangedBorrowTree,
        ContinueChainReleases prefixFrames tRel tFinal ∧
        wpUnwindStack onCleanupFrame onRootUnwind onAbortTerminate
          suffixFrames m₁ tFinal)
    (hAbort : ∀ (m₁ : Mem) (t₁ : Anneal.RefFrame.RangedBorrowTree),
      spec.canAbort = true →
      UpdatesOnly spec.modifies m₀ m₁ →
      spec.postAbort m₁ t₁ →
      onTerminate m₁ t₁) :
    wpCallSite adapter ⟨some retBb, .continue_⟩ isCleanupBb spec.frameTags
      onNormal onCleanup
      (wpUnwindStack onCleanupFrame onRootUnwind onAbortTerminate
        (prefixFrames ++ suffixFrames))
      onTerminate m₀ t₀ :=
  callSpecCut_call_normal_continue hCut hPre hNormal
    (fun m₁ tRel hCanU hUpd hStripped hPost => by
      let ⟨tFinal, hRelChain, hSuf⟩ := hChain m₁ tRel hCanU hUpd hStripped hPost
      exact wpUnwindStack_append_continue_chain hRelChain hSuf)
    hAbort

/-- Disjoint-lens frame rule for `CallSpecCut`: for any bystander lens `other`
pairwise disjoint from `spec.modifies`, every normal return, unwind exit, and
abort exit of the callee preserves `other.get m₁ = other.get m₀`. -/
theorem callSpecCut_frame_disjoint [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte] [LawfulByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    {other : ByteSubLens Addr}
    {m₀ : Mem} {t₀ : Anneal.RefFrame.RangedBorrowTree}
    (hCut : CallSpecCut adapter spec)
    (hPre : spec.pre m₀ t₀)
    (hDisj : ∀ L : ByteSubLens Addr, L ∈ spec.modifies → L.Disjoint Mem other) :
    wpOutcome (ops := wops)
      (fun out =>
        match adapter.classifyOut out with
        | none => False
        | some (.returned retVal m₁ t₁) =>
          spec.canNormal = true ∧
          other.get m₁ = other.get m₀ ∧
          ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
            Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
              ⟨tRel, .Released⟩ ∧
            spec.postRet retVal m₁ tRel
        | some (.unwound m₁ t₁) =>
          spec.canUnwind = true ∧
          other.get m₁ = other.get m₀ ∧
          ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
            Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
              ⟨tRel, .Released⟩ ∧
            spec.postUnwind m₁ tRel
        | some (.abortTerminate m₁ t₁) =>
          spec.canAbort = true ∧
          other.get m₁ = other.get m₀ ∧
          spec.postAbort m₁ t₁)
      (fun _ => False)
      (adapter.mkEntry m₀ t₀) := by
  unfold wpOutcome
  refine wpUntil_mono (ops := wops) (fun _ hf => hf) ?_ (fun _ hf => hf)
    (hCut m₀ t₀ hPre)
  intro out hOut
  cases hCls : adapter.classifyOut out with
  | none => rw [hCls] at hOut; exact False.elim hOut
  | some ex =>
    rw [hCls] at hOut
    cases ex with
    | returned retVal m₁ t₁ =>
      let ⟨hCanN, hUpd, tRel, hRel, hPost⟩ := hOut
      exact ⟨hCanN, updatesOnly_frame_disjoint hDisj hUpd, tRel, hRel, hPost⟩
    | unwound m₁ t₁ =>
      let ⟨hCanU, hUpd, tRel, hRel, hPost⟩ := hOut
      exact ⟨hCanU, updatesOnly_frame_disjoint hDisj hUpd, tRel, hRel, hPost⟩
    | abortTerminate m₁ t₁ =>
      let ⟨hCanA, hUpd, hPost⟩ := hOut
      exact ⟨hCanA, updatesOnly_frame_disjoint hDisj hUpd, hPost⟩

/-- Auxiliary-projection frame rule for `CallSpecCut`: any write-invariant
projection `proj` (such as metadata stored alongside bytes) is preserved on
normal return, unwind, and abort exits. -/
theorem CallSpecCut.frame_preserves_proj {V : Sort b} {proj : Mem → V}
    [wops : MirWpOps State Out Fault] [ops : ByteStoreOps Mem Addr Byte]
    (hPres : ops.WritePreserves proj)
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    {m₀ : Mem} {t₀ : Anneal.RefFrame.RangedBorrowTree}
    (hCut : CallSpecCut adapter spec)
    (hPre : spec.pre m₀ t₀) :
    wpOutcome (ops := wops)
      (fun out =>
        match adapter.classifyOut out with
        | none => False
        | some (.returned retVal m₁ t₁) =>
          spec.canNormal = true ∧ proj m₁ = proj m₀ ∧
          ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
            Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
              ⟨tRel, .Released⟩ ∧
            spec.postRet retVal m₁ tRel
        | some (.unwound m₁ t₁) =>
          spec.canUnwind = true ∧ proj m₁ = proj m₀ ∧
          ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
            Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
              ⟨tRel, .Released⟩ ∧
            spec.postUnwind m₁ tRel
        | some (.abortTerminate m₁ t₁) =>
          spec.canAbort = true ∧ proj m₁ = proj m₀ ∧
          spec.postAbort m₁ t₁)
      (fun _ => False)
      (adapter.mkEntry m₀ t₀) := by
  unfold wpOutcome
  refine wpUntil_mono (ops := wops) (fun _ hf => hf) ?_ (fun _ hf => hf)
    (hCut m₀ t₀ hPre)
  intro out hOut
  cases hCls : adapter.classifyOut out with
  | none => rw [hCls] at hOut; exact False.elim hOut
  | some ex =>
    rw [hCls] at hOut
    cases ex with
    | returned retVal m₁ t₁ =>
      let ⟨hCanN, hUpd, tRel, hRel, hPost⟩ := hOut
      exact ⟨hCanN, updatesOnly_preserves_proj hPres hUpd, tRel, hRel, hPost⟩
    | unwound m₁ t₁ =>
      let ⟨hCanU, hUpd, tRel, hRel, hPost⟩ := hOut
      exact ⟨hCanU, updatesOnly_preserves_proj hPres hUpd, tRel, hRel, hPost⟩
    | abortTerminate m₁ t₁ =>
      let ⟨hCanA, hUpd, hPost⟩ := hOut
      exact ⟨hCanA, updatesOnly_preserves_proj hPres hUpd, hPost⟩

/-- Rule of consequence for `CallSpecCut`: strengthens `pre`, weakens
`postRet` / `postUnwind` / `postAbort`, enlarges `modifies` via
`UpdatesOnly.mono_subset`, and relaxes `canNormal` / `canUnwind` / `canAbort`
for the same `frameTags`. -/
theorem CallSpecCut.weaken [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec₁ spec₂ : CallSpec Mem Addr Val}
    (hTags : spec₂.frameTags = spec₁.frameTags)
    (hPre : ∀ m t, spec₂.pre m t → spec₁.pre m t)
    (hMod : ∀ L, L ∈ spec₁.modifies → L ∈ spec₂.modifies)
    (hCanN : spec₁.canNormal = true → spec₂.canNormal = true)
    (hCanU : spec₁.canUnwind = true → spec₂.canUnwind = true)
    (hCanA : spec₁.canAbort = true → spec₂.canAbort = true)
    (hPostR : ∀ rv m t, spec₁.postRet rv m t → spec₂.postRet rv m t)
    (hPostU : ∀ m t, spec₁.postUnwind m t → spec₂.postUnwind m t)
    (hPostA : ∀ m t, spec₁.postAbort m t → spec₂.postAbort m t)
    (hCut : CallSpecCut adapter spec₁) :
    CallSpecCut adapter spec₂ := by
  intro m₀ t₀ hPre₂
  unfold wpOutcome
  refine wpUntil_mono (ops := wops) (fun _ hf => hf) ?_ (fun _ hf => hf)
    (hCut m₀ t₀ (hPre m₀ t₀ hPre₂))
  intro out hOut
  cases hCls : adapter.classifyOut out with
  | none => rw [hCls] at hOut; exact False.elim hOut
  | some ex =>
    rw [hCls] at hOut
    cases ex with
    | returned retVal m₁ t₁ =>
      let ⟨hN, hUpd, tRel, hRel, hP⟩ := hOut
      refine ⟨hCanN hN, UpdatesOnly.mono_subset hMod hUpd, tRel, ?_, hPostR _ _ _ hP⟩
      rw [hTags]
      exact hRel
    | unwound m₁ t₁ =>
      let ⟨hU, hUpd, tRel, hRel, hP⟩ := hOut
      refine ⟨hCanU hU, UpdatesOnly.mono_subset hMod hUpd, tRel, ?_, hPostU _ _ hP⟩
      rw [hTags]
      exact hRel
    | abortTerminate m₁ t₁ =>
      let ⟨hA, hUpd, hP⟩ := hOut
      exact ⟨hCanA hA, UpdatesOnly.mono_subset hMod hUpd, hPostA _ _ hP⟩

/-- Pointwise step-function congruence for deterministic `CallSpecCut`
(`0 Quot.sound`), enabling `BlockTree`-backed callee proofs to transport
directly to list-backed lookup. -/
theorem CallSpecCut.congr_step [ops : ByteStoreOps Mem Addr Byte]
    {step₁ step₂ : State → StepOutcome State Out Fault}
    {tag₁ tag₂ : State → Option Nat}
    (hEq : ∀ s : State, step₁ s = step₂ s)
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    (hCut : CallSpecCut (wops := MirWpOps.ofDetStep step₁ tag₁) adapter spec) :
    CallSpecCut (wops := MirWpOps.ofDetStep step₂ tag₂) adapter spec := by
  intro m₀ t₀ hPre
  have hAux : ∀ s : State,
      wpUntil (ops := MirWpOps.ofDetStep step₁ tag₁)
        (fun _ => False)
        (fun out =>
          match adapter.classifyOut out with
          | none => False
          | some (.returned retVal m₁ t₁) =>
            spec.canNormal = true ∧
            UpdatesOnly spec.modifies m₀ m₁ ∧
            ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
              Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
                ⟨tRel, .Released⟩ ∧
              spec.postRet retVal m₁ tRel
          | some (.unwound m₁ t₁) =>
            spec.canUnwind = true ∧
            UpdatesOnly spec.modifies m₀ m₁ ∧
            ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
              Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
                ⟨tRel, .Released⟩ ∧
              spec.postUnwind m₁ tRel
          | some (.abortTerminate m₁ t₁) =>
            spec.canAbort = true ∧
            UpdatesOnly spec.modifies m₀ m₁ ∧
            spec.postAbort m₁ t₁)
        (fun _ => False) s →
      wpUntil (ops := MirWpOps.ofDetStep step₂ tag₂)
        (fun _ => False)
        (fun out =>
          match adapter.classifyOut out with
          | none => False
          | some (.returned retVal m₁ t₁) =>
            spec.canNormal = true ∧
            UpdatesOnly spec.modifies m₀ m₁ ∧
            ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
              Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
                ⟨tRel, .Released⟩ ∧
              spec.postRet retVal m₁ tRel
          | some (.unwound m₁ t₁) =>
            spec.canUnwind = true ∧
            UpdatesOnly spec.modifies m₀ m₁ ∧
            ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
              Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
                ⟨tRel, .Released⟩ ∧
              spec.postUnwind m₁ tRel
          | some (.abortTerminate m₁ t₁) =>
            spec.canAbort = true ∧
            UpdatesOnly spec.modifies m₀ m₁ ∧
            spec.postAbort m₁ t₁)
        (fun _ => False) s := by
    intro s hW
    induction hW with
    | here hf => exact False.elim hf
    | step mid hStep _ ih =>
      refine wpUntil_step (ops := MirWpOps.ofDetStep step₂ tag₂) ?_
      change (step₂ _).wp _ _ _
      rw [← hEq]
      exact StepOutcome.wp_mono ih (fun _ ho => ho) (fun _ hf => hf) hStep
  exact hAux (adapter.mkEntry m₀ t₀) (hCut m₀ t₀ hPre)

/-- `0 Quot.sound` pointwise `BlockTree` transport for deterministic
`CallSpecCut`. -/
theorem CallSpecCut.of_validBlockTree {BB : Type b}
    [ops : ByteStoreOps Mem Addr Byte]
    {blocks : List BB} {bt : BlockTree BB} (hValid : ValidBlockTree blocks bt)
    (stepWith : (Nat → Option BB) → State → StepOutcome State Out Fault)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : State),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    {tag : State → Option Nat}
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    (hCut : CallSpecCut
      (wops := MirWpOps.ofDetStep (stepWith bt.lookupForced?) tag) adapter spec) :
    CallSpecCut
      (wops := MirWpOps.ofDetStep (stepWith (listGet? blocks)) tag) adapter spec :=
  CallSpecCut.congr_step
    (fun s => hPointwise _ _ s (fun i =>
      (bt.lookupForced?_eq i).trans (hValid.2 i))) hCut

/-- Lifts a `CallSpecCut` directly into a fuel-free `ParametricCore.StageCut`
over `[wops : MirWpOps State Out Fault]`. -/
theorem CallSpecCut.to_stageCut [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapter : CalleeMachineAdapter State Out Mem Val}
    {spec : CallSpec Mem Addr Val}
    (hCut : CallSpecCut adapter spec) :
    StageCut (ops := wops)
      (fun st => ∃ m₀ t₀, st = adapter.mkEntry m₀ t₀ ∧ spec.pre m₀ t₀)
      (fun _ => False)
      (fun out =>
        match adapter.classifyOut out with
        | none => False
        | some (.returned retVal m₁ t₁) =>
          spec.canNormal = true ∧
          ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
            Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
              ⟨tRel, .Released⟩ ∧
            spec.postRet retVal m₁ tRel
        | some (.unwound m₁ t₁) =>
          spec.canUnwind = true ∧
          ∃ tRel : Anneal.RefFrame.RangedBorrowTree,
            Anneal.RefFrame.exitFrameWithProtectors t₁ spec.frameTags =
              ⟨tRel, .Released⟩ ∧
            spec.postUnwind m₁ tRel
        | some (.abortTerminate m₁ t₁) =>
          spec.canAbort = true ∧
          spec.postAbort m₁ t₁)
      (fun _ => False) :=
  StageCut.intro (ops := wops) (fun _ hEntry => by
    let ⟨m₀, t₀, hEq, hPre⟩ := hEntry
    rw [hEq]
    refine wpUntil_mono (ops := wops) (fun _ hf => hf) ?_ (fun _ hf => hf)
      (hCut m₀ t₀ hPre)
    intro out hOut
    cases hCls : adapter.classifyOut out with
    | none => rw [hCls] at hOut; exact False.elim hOut
    | some ex =>
      rw [hCls] at hOut
      cases ex with
      | returned retVal m₁ t₁ =>
        let ⟨hCanN, _, tRel, hRel, hPost⟩ := hOut
        exact ⟨hCanN, tRel, hRel, hPost⟩
      | unwound m₁ t₁ =>
        let ⟨hCanU, _, tRel, hRel, hPost⟩ := hOut
        exact ⟨hCanU, tRel, hRel, hPost⟩
      | abortTerminate m₁ t₁ =>
        let ⟨hCanA, _, hPost⟩ := hOut
        exact ⟨hCanA, hPost⟩)

/-- Fail-closed: if a deterministic callee terminates immediately with a
normal return `.returned`, `wpCallSite` at a diverging call site
(`onRet = none`) is strictly refutable (`¬ wpCallSite ...`). -/
theorem not_wpCallSite_diverging_of_done_returned
    {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat}
    (adapter : CalleeMachineAdapter State Out Mem Val)
    (uAct : UnwindAction4) (isCleanupBb : Nat → Bool) (frameTags : List Nat)
    (onNormal : Nat → Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onCleanup : Nat → Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onUnwindExit : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (m₀ m₁ : Mem) (t₀ t₁ : Anneal.RefFrame.RangedBorrowTree)
    (out : Out) (rv : Val)
    (hDone : step (adapter.mkEntry m₀ t₀) = .done out)
    (hCls : adapter.classifyOut out = some (.returned rv m₁ t₁)) :
    ¬ wpCallSite (wops := MirWpOps.ofDetStep step tag) adapter
        ⟨none, uAct⟩ isCleanupBb frameTags onNormal onCleanup onUnwindExit
        onTerminate m₀ t₀ := by
  intro hWp
  cases (wpUntil_unfold_iff (ops := MirWpOps.ofDetStep step tag)).mp hWp with
  | inl hFalse => exact hFalse
  | inr hStep =>
    change (step (adapter.mkEntry m₀ t₀)).wp _ _ _ at hStep
    rw [hDone] at hStep
    dsimp only [StepOutcome.wp] at hStep
    rw [hCls] at hStep
    dsimp only at hStep
    cases hRel : Anneal.RefFrame.exitFrameWithProtectors t₁ frameTags with
    | mk tRel st =>
      rw [hRel] at hStep
      cases st with
      | Released => exact hStep
      | MissingTag _ => exact hStep
      | AccessFailure _ _ _ _ => exact hStep
      | InvariantFailure _ _ _ => exact hStep

/-- Fail-closed: if a deterministic callee terminates immediately with an
unwind `.unwound`, `wpCallSite` at an `.unreachable`-unwind call site is
strictly refutable (`¬ wpCallSite ...`). -/
theorem not_wpCallSite_unreachable_of_done_unwound
    {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat}
    (adapter : CalleeMachineAdapter State Out Mem Val)
    (onRet : Option Nat) (isCleanupBb : Nat → Bool) (frameTags : List Nat)
    (onNormal : Nat → Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onCleanup : Nat → Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onUnwindExit : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (m₀ m₁ : Mem) (t₀ t₁ : Anneal.RefFrame.RangedBorrowTree)
    (out : Out)
    (hDone : step (adapter.mkEntry m₀ t₀) = .done out)
    (hCls : adapter.classifyOut out = some (.unwound m₁ t₁)) :
    ¬ wpCallSite (wops := MirWpOps.ofDetStep step tag) adapter
        ⟨onRet, .unreachable⟩ isCleanupBb frameTags onNormal onCleanup
        onUnwindExit onTerminate m₀ t₀ := by
  intro hWp
  cases (wpUntil_unfold_iff (ops := MirWpOps.ofDetStep step tag)).mp hWp with
  | inl hFalse => exact hFalse
  | inr hStep =>
    change (step (adapter.mkEntry m₀ t₀)).wp _ _ _ at hStep
    rw [hDone] at hStep
    dsimp only [StepOutcome.wp] at hStep
    rw [hCls] at hStep
    dsimp only at hStep
    cases hRel : Anneal.RefFrame.exitFrameWithProtectors t₁ frameTags with
    | mk tRel st =>
      rw [hRel] at hStep
      cases st with
      | Released => exact hStep
      | MissingTag _ => exact hStep
      | AccessFailure _ _ _ _ => exact hStep
      | InvariantFailure _ _ _ => exact hStep

/-- Fail-closed: if a deterministic callee terminates immediately with a
process abort `.abortTerminate m₁ t₁` and the caller's `onTerminate` rejects
`(m₁, t₁)`, then `wpCallSite` is strictly refutable (`¬ wpCallSite ...`). -/
theorem not_wpCallSite_of_done_abort_rejected
    {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat}
    (adapter : CalleeMachineAdapter State Out Mem Val)
    (cont : CallCont4) (isCleanupBb : Nat → Bool) (frameTags : List Nat)
    (onNormal : Nat → Val → Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onCleanup : Nat → Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onUnwindExit : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (onTerminate : Mem → Anneal.RefFrame.RangedBorrowTree → Prop)
    (m₀ m₁ : Mem) (t₀ t₁ : Anneal.RefFrame.RangedBorrowTree)
    (out : Out)
    (hDone : step (adapter.mkEntry m₀ t₀) = .done out)
    (hCls : adapter.classifyOut out = some (.abortTerminate m₁ t₁))
    (hReject : ¬ onTerminate m₁ t₁) :
    ¬ wpCallSite (wops := MirWpOps.ofDetStep step tag) adapter
        cont isCleanupBb frameTags onNormal onCleanup onUnwindExit
        onTerminate m₀ t₀ := by
  intro hWp
  cases (wpUntil_unfold_iff (ops := MirWpOps.ofDetStep step tag)).mp hWp with
  | inl hFalse => exact hFalse
  | inr hStep =>
    change (step (adapter.mkEntry m₀ t₀)).wp _ _ _ at hStep
    rw [hDone] at hStep
    dsimp only [StepOutcome.wp] at hStep
    rw [hCls] at hStep
    dsimp only at hStep
    exact hReject hStep

end CallSpecCutSec

attribute [irreducible] CallSpecCut

/-! ### `Anneal.Firewall.IndexedCut` Interop for `CallSpecCut` -/

/-- Indexed call-contract family for `Anneal.Firewall.IndexedCut`: stage `k`
holds the sealed `CallSpecCut` for `specAt k`. -/
def callSpecIndexedCutFamily {State : Type x} {Out : Type y} {Fault : Type z}
    {Mem : Type u} {Addr : Type v} {Byte : Type a} {Val : Type w}
    [wops : MirWpOps State Out Fault] [ops : ByteStoreOps Mem Addr Byte]
    (adapterAt : Nat → CalleeMachineAdapter State Out Mem Val)
    (specAt : Nat → CallSpec Mem Addr Val) (stage : Nat) (_st : Unit) : Prop :=
  CallSpecCut (adapterAt stage) (specAt stage)

/-- Seals a `CallSpecCut` into `Anneal.Firewall.IndexedCut`. -/
theorem CallSpecCut.to_indexedCut {State : Type x} {Out : Type y}
    {Fault : Type z} {Mem : Type u} {Addr : Type v} {Byte : Type a}
    {Val : Type w} [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapterAt : Nat → CalleeMachineAdapter State Out Mem Val}
    {specAt : Nat → CallSpec Mem Addr Val} {stage : Nat}
    (h : CallSpecCut (adapterAt stage) (specAt stage)) :
    Anneal.Firewall.IndexedCut
      (callSpecIndexedCutFamily adapterAt specAt) stage () :=
  Anneal.Firewall.seal_cut h

/-- Connects an outer caller's `CallSpecCut` proof (using an inner callee's
sealed contract) through `Anneal.Firewall.step_cut`. -/
theorem callSpecIndexedCut_step {State : Type x} {Out : Type y}
    {Fault : Type z} {Mem : Type u} {Addr : Type v} {Byte : Type a}
    {Val : Type w} [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapterAt : Nat → CalleeMachineAdapter State Out Mem Val}
    {specAt : Nat → CallSpec Mem Addr Val} {outerStage innerStage : Nat}
    (hOuter : CallSpecCut (adapterAt innerStage) (specAt innerStage) →
      CallSpecCut (adapterAt outerStage) (specAt outerStage))
    (hInner : Anneal.Firewall.IndexedCut
      (callSpecIndexedCutFamily adapterAt specAt) innerStage ()) :
    Anneal.Firewall.IndexedCut
      (callSpecIndexedCutFamily adapterAt specAt) outerStage () :=
  Anneal.Firewall.step_cut hOuter hInner

/-- Discharges a final goal from a `CallSpecCut` `IndexedCut` via
`Anneal.Firewall.finish_cut`. -/
theorem callSpecIndexedCut_finish {State : Type x} {Out : Type y}
    {Fault : Type z} {Mem : Type u} {Addr : Type v} {Byte : Type a}
    {Val : Type w} [wops : MirWpOps State Out Fault]
    [ops : ByteStoreOps Mem Addr Byte]
    {adapterAt : Nat → CalleeMachineAdapter State Out Mem Val}
    {specAt : Nat → CallSpec Mem Addr Val} {stage : Nat} {post : Prop}
    (hDone : CallSpecCut (adapterAt stage) (specAt stage) → post)
    (hCut : Anneal.Firewall.IndexedCut
      (callSpecIndexedCutFamily adapterAt specAt) stage ()) :
    post :=
  Anneal.Firewall.finish_cut hDone hCut

/-! ## Part IV: Self-Contained Kernel-Checked Positive & Negative Canaries -/

/-- Shared 16-byte buffer store (`[0..8)` = `src`, `[8..16)` = `dst`) using
`ByteRunAtom Nat` (with `.initPlain`, `.initProv`, and `.uninitPad`). -/
private abbrev CsuMem := SliceStore (ByteRunAtom Nat)

private def csuSrcLens : ByteSubLens Nat := { addr := 0, offset := 0, len := 8 }
private def csuDstLens : ByteSubLens Nat := { addr := 0, offset := 8, len := 8 }

private def csuInitialBytes : List (ByteRunAtom Nat) :=
  [ .initPlain 0x10, .initPlain 0x11, .initPlain 0x12, .initPlain 0x13,
    .initPlain 0x14, .initPlain 0x15, .initPlain 0x16, .initPlain 0x17,
    .initProv 0xAA 99, .initProv 0xBB 99, .uninitPad, .uninitPad,
    .initPlain 0x00, .initPlain 0x00, .initPlain 0x00, .initPlain 0x00 ]

private def csuInitialMem : CsuMem :=
  { allocs := [{ allocId := 0, bytes := csuInitialBytes, writable := true }] }

/-- Mixed-mask normal writeback runs (4 plain + 2 uninitPad + 2 prov). -/
private def csuNormalRuns : List (ByteRun Nat) :=
  [ .initPlain [0x21, 0x22, 0x23, 0x24],
    .uninitPad 2,
    .initProv [0xF0, 0xF1] 42 ]

/-- Mixed-mask partial unwind writeback runs (2 plain + 6 uninitPad). -/
private def csuPartialRuns : List (ByteRun Nat) :=
  [ .initPlain [0xE1, 0xE2], .uninitPad 6 ]

/-- Canary 1 (Positive): Complete 16-equation protected `RefFrame` continuation
matrix over `SliceStore (ByteRunAtom Nat)` and a protected `topo3`
`RangedBorrowTree`, overwriting prior `.initProv` provenance, preserving
`.uninitPad`, framing `csuSrcLens`, and stripping `[1, 2]` protectors. -/
theorem canary_protectedRefFrame_matrix_and_framing :
    let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2]
    let rel := Anneal.RefFrame.exitFrameWithProtectors tree0 [1, 2]
    rel.status = .Released ∧
    rel.tree.protectedTags = [] ∧
    (∃ mNorm mUnw : CsuMem,
      csuDstLens.get mNorm = some (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns) ∧
      csuDstLens.get mUnw = some (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) ∧
      csuSrcLens.get mNorm = csuSrcLens.get csuInitialMem ∧
      csuSrcLens.get mUnw = csuSrcLens.get csuInitialMem ∧
      evalProtectedRefFrameExit ⟨⟨csuDstLens, ⟨some 10, .cleanup 99⟩⟩, [1, 2]⟩
        csuInitialMem tree0
        (.returned (7 : Nat) (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns)) =
        (.jumpNormal 10 7 mNorm, rel.tree) ∧
      evalProtectedRefFrameExit ⟨⟨csuDstLens, ⟨some 10, .cleanup 99⟩⟩, [1, 2]⟩
        csuInitialMem tree0
        (.unwound (Val := Nat) (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns)) =
        (.jumpCleanup 99 mUnw, rel.tree) ∧
      evalProtectedRefFrameExit ⟨⟨csuDstLens, ⟨none, .continue_⟩⟩, [1, 2]⟩
        csuInitialMem tree0
        (.returned (7 : Nat) (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns)) =
        (.fault, rel.tree) ∧
      evalProtectedRefFrameExit ⟨⟨csuDstLens, ⟨some 10, .unreachable⟩⟩, [1, 2]⟩
        csuInitialMem tree0
        (.unwound (Val := Nat) (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns)) =
        (.fault, rel.tree)) := by
  let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2]
  let rel := Anneal.RefFrame.exitFrameWithProtectors tree0 [1, 2]
  have hRelEq : Anneal.RefFrame.exitFrameWithProtectors tree0 [1, 2] =
      ⟨rel.tree, .Released⟩ := rfl
  have hDisj : csuDstLens.Disjoint CsuMem csuSrcLens :=
    ByteSubLens.disjoint_of_separated
      (ByteSubLens.separated_of_natLensSeparatedBool rfl)
  let ⟨_, mNorm, mUnw, hGetN, hGetU, hFrame,
      e1, e2, _, _, _, e6, _, _, _, _, e11, _, _, _, _, _⟩ :=
    protectedRefFrame_callCont4_matrix_sound (Val := Nat) (ByteRunCodec.id Nat)
      csuDstLens [1, 2] csuInitialMem
      (csuInitialBytes.drop 8 |>.take 8) tree0 rel.tree 10 99 7
      csuNormalRuns csuPartialRuns rfl rfl rfl hRelEq
  have hF := hFrame csuSrcLens hDisj
  exact ⟨rfl, rfl, mNorm, mUnw, hGetN, hGetU, hF.1, hF.2, e1, e2, e11, e6⟩

/-- Canary 2 (Positive): Universal `shared_topo3` commutation lifted through
`evalProtectedRefFrameExit` on `csuInitialMem`. -/
theorem canary_shared_topo3_protected_commutation
    (pSrc pDst : Anneal.RefFrame.TbPermission) (accSrc accDst protBoth : Bool)
    (hRead : Anneal.RefFrame.permCanLocalRead pSrc = true)
    (hWrite : Anneal.RefFrame.permCanProtectedLocalWrite pDst = true) :
    let protTags := if protBoth then [1, 2] else [2]
    let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags
    let s1 := Anneal.RefFrame.performRangedAccess tree0 0 8 1 .Read .VisitChildrenOfAccessed
    let s12 := Anneal.RefFrame.performRangedAccess s1.tree 8 8 2 .Write .VisitChildrenOfAccessed
    let s2 := Anneal.RefFrame.performRangedAccess tree0 8 8 2 .Write .VisitChildrenOfAccessed
    let s21 := Anneal.RefFrame.performRangedAccess s2.tree 0 8 1 .Read .VisitChildrenOfAccessed
    let rf : RefFrame Nat := ⟨csuDstLens, ⟨some 5, .cleanup 8⟩⟩
    let ex : CalleeExit Nat (ByteRunAtom Nat) :=
      .returned 42 (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns)
    evalProtectedRefFrameExit ⟨rf, protTags⟩ csuInitialMem s12.tree ex =
      evalProtectedRefFrameExit ⟨rf, protTags⟩ csuInitialMem s21.tree ex ∧
    (evalProtectedRefFrameExit ⟨rf, protTags⟩ csuInitialMem s12.tree ex).2.protectedTags = [] := by
  have h := protectedRefFrame_shared_topo3_commutation
    pSrc pDst accSrc accDst protBoth hRead hWrite
    ⟨csuDstLens, ⟨some 5, .cleanup 8⟩⟩ csuInitialMem
    (.returned (42 : Nat) (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns))
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- Minimal deterministic callee machine for testing `CallSpecCut`, `.cleanup`
recovery, `.continue_` multi-frame unwind propagation, `IndexedCut`, and
fail-closed negative rejection. -/
private structure CsuCalleeState where
  shouldPanic : Bool
  mem : CsuMem
  tree : Anneal.RefFrame.RangedBorrowTree

private def csuCalleeStep (s : CsuCalleeState) :
    StepOutcome CsuCalleeState (FrameExitOutcome CsuMem Nat) Unit :=
  match s.shouldPanic with
  | true =>
    match csuDstLens.set s.mem (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) with
    | none => .fault ()
    | some m' => .done (.unwound m' s.tree)
  | false =>
    match csuDstLens.set s.mem (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns) with
    | none => .fault ()
    | some m' => .done (.returned 77 m' s.tree)

private def csuAdapter (shouldPanic : Bool) :
    CalleeMachineAdapter CsuCalleeState (FrameExitOutcome CsuMem Nat) CsuMem Nat where
  mkEntry m t := ⟨shouldPanic, m, t⟩
  classifyOut o := some o

private def csuSpec : CallSpec CsuMem Nat Nat where
  pre m t :=
    (∃ bs, csuDstLens.get m = some bs) ∧
    (Anneal.RefFrame.exitFrameWithProtectors t [2]).status = .Released
  postRet rv m t :=
    rv = 77 ∧
    csuDstLens.get m = some (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns) ∧
    Anneal.RefFrame.natListMem 2 t.protectedTags = false
  postUnwind m t :=
    csuDstLens.get m = some (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) ∧
    Anneal.RefFrame.natListMem 2 t.protectedTags = false
  modifies := [csuDstLens]
  frameTags := [2]
  canNormal := true
  canUnwind := true

private theorem csuCallee_cut (shouldPanic : Bool) :
    CallSpecCut
      (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
      (csuAdapter shouldPanic) csuSpec := by
  apply seal_callSpecCut (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
  intro m₀ t₀ hPre
  let ⟨⟨old, hGet⟩, hRelStatus⟩ := hPre
  have hRelEq : Anneal.RefFrame.exitFrameWithProtectors t₀ [2] =
      ⟨(Anneal.RefFrame.exitFrameWithProtectors t₀ [2]).tree, .Released⟩ := by
    cases hR : Anneal.RefFrame.exitFrameWithProtectors t₀ [2] with
    | mk tRel st =>
      rw [hR] at hRelStatus
      dsimp only at hRelStatus
      rw [hRelStatus]
  have hStrip : Anneal.RefFrame.natListMem 2
      (Anneal.RefFrame.exitFrameWithProtectors t₀ [2]).tree.protectedTags = false :=
    (exitFrameWithProtectors_released_tags hRelEq).1 2 rfl
  refine wpUntil_step
    (ops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none)) ?_
  change (csuCalleeStep ⟨shouldPanic, m₀, t₀⟩).wp _ _ _
  unfold csuCalleeStep
  cases shouldPanic with
  | false =>
    dsimp only
    let ⟨m', hSet⟩ := ByteSubLens.set_isSome_of_get
      (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns) hGet rfl
    rw [hSet]
    exact ⟨rfl, UpdatesOnly.of_single_set hSet,
      (Anneal.RefFrame.exitFrameWithProtectors t₀ [2]).tree, hRelEq,
      rfl, ByteSubLens.get_set hSet, hStrip⟩
  | true =>
    dsimp only
    let ⟨m', hSet⟩ := ByteSubLens.set_isSome_of_get
      (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) hGet rfl
    rw [hSet]
    exact ⟨rfl, UpdatesOnly.of_single_set hSet,
      (Anneal.RefFrame.exitFrameWithProtectors t₀ [2]).tree, hRelEq,
      ByteSubLens.get_set hSet, hStrip⟩

/-- Canary 3 (Positive): `CallSpecCut` + `Anneal.Firewall.IndexedCut` +
`.cleanup` landing pad recovery (certifying `postUnwind` without leaking
`postRet`) + `callSpecCut_frame_disjoint` preserving `csuSrcLens`. -/
theorem canary_callSpecCut_cleanup_and_indexedCut (shouldPanic : Bool) :
    let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2]
    let isClean : Nat → Bool := fun bb => Nat.beq bb 99
    wpCallSite (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
      (csuAdapter shouldPanic) ⟨some 10, .cleanup 99⟩ isClean [2]
      (fun bb rv m t => bb = 10 ∧ rv = 77 ∧
        csuDstLens.get m = some (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns) ∧
        csuSrcLens.get m = csuSrcLens.get csuInitialMem ∧
        Anneal.RefFrame.natListMem 2 t.protectedTags = false)
      (fun bb m t => bb = 99 ∧
        csuDstLens.get m = some (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) ∧
        csuSrcLens.get m = csuSrcLens.get csuInitialMem ∧
        Anneal.RefFrame.natListMem 2 t.protectedTags = false)
      (fun _ _ => False) (fun _ _ => False) csuInitialMem tree0 := by
  let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2]
  let isClean : Nat → Bool := fun bb => Nat.beq bb 99
  have hDisj : ∀ L : ByteSubLens Nat, L ∈ csuSpec.modifies →
      L.Disjoint CsuMem csuSrcLens :=
    allDisjoint_of_allNatLensesSeparatedBool rfl
  have hIc : Anneal.Firewall.IndexedCut
      (callSpecIndexedCutFamily
        (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
        (fun _ => csuAdapter shouldPanic) (fun _ => csuSpec)) 0 () :=
    CallSpecCut.to_indexedCut
      (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
      (adapterAt := fun _ => csuAdapter shouldPanic)
      (specAt := fun _ => csuSpec) (stage := 0) (csuCallee_cut shouldPanic)
  have hPre0 : csuSpec.pre csuInitialMem tree0 :=
    ⟨⟨csuInitialBytes.drop 8 |>.take 8, rfl⟩, rfl⟩
  exact callSpecIndexedCut_finish
    (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
    (adapterAt := fun _ => csuAdapter shouldPanic)
    (specAt := fun _ => csuSpec)
    (fun hCut =>
      callSpecCut_call_normal_cleanup
        (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
        hCut hPre0 rfl
        (fun rv m₁ tRel _ hUpd hStrip hPost =>
          ⟨rfl, hPost.1, hPost.2.1,
            updatesOnly_frame_disjoint hDisj hUpd, hStrip 2 rfl⟩)
        (fun m₁ tRel _ hUpd hStrip hPost =>
          ⟨rfl, hPost.1,
            updatesOnly_frame_disjoint hDisj hUpd, hStrip 2 rfl⟩)
        (fun _ _ hA _ _ => by cases hA))
    hIc

/-- Canary 4 (Positive): Multi-frame `.continue_` unwind propagation chain
releasing callee protector `[2]`, propagating across an intermediate
`.continue_` caller frame releasing protector `[1]`, and landing in an outer
`.cleanup 55` `StackFrameState` with `protectedTags = []` and `csuSrcLens`
framed. -/
theorem canary_callSpecCut_multiframe_continue_chain :
    let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2]
    let midFrame : SavedCallFrame Nat Nat :=
      { ctx := 101
        cont := ⟨some 20, .continue_⟩
        isCleanupBb := fun _ => false
        callerModifies := [csuDstLens]
        callerTags := [1] }
    let outerFrame : SavedCallFrame Nat Nat :=
      { ctx := 202
        cont := ⟨some 30, .cleanup 55⟩
        isCleanupBb := fun bb => Nat.beq bb 55
        callerModifies := [csuDstLens]
        callerTags := [] }
    wpCallSite (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
      (csuAdapter true) ⟨some 10, .continue_⟩ (fun _ => false) [2]
      (fun _ _ _ _ => False) (fun _ _ _ => False)
      (wpUnwindStack
        (fun st =>
          st.blockIdx = 55 ∧ st.ctx = 202 ∧ st.callers = [] ∧
          csuDstLens.get st.mem = some (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) ∧
          csuSrcLens.get st.mem = csuSrcLens.get csuInitialMem ∧
          st.tree.protectedTags = [])
        (fun _ _ => False) (fun _ _ => False)
        ([midFrame] ++ [outerFrame]))
      (fun _ _ => False)
      csuInitialMem tree0 := by
  let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2]
  let midFrame : SavedCallFrame Nat Nat :=
    { ctx := 101
      cont := ⟨some 20, .continue_⟩
      isCleanupBb := fun _ => false
      callerModifies := [csuDstLens]
      callerTags := [1] }
  let outerFrame : SavedCallFrame Nat Nat :=
    { ctx := 202
      cont := ⟨some 30, .cleanup 55⟩
      isCleanupBb := fun bb => Nat.beq bb 55
      callerModifies := [csuDstLens]
      callerTags := [] }
  have hDisj : ∀ L : ByteSubLens Nat, L ∈ csuSpec.modifies →
      L.Disjoint CsuMem csuSrcLens :=
    allDisjoint_of_allNatLensesSeparatedBool rfl
  -- Specialize the callee spec to `shouldPanic = true` (`canNormal = false`).
  let panicSpec : CallSpec CsuMem Nat Nat :=
    { pre := fun m t => m = csuInitialMem ∧ t = tree0
      postRet := fun _ _ _ => False
      postUnwind := fun m t =>
        csuDstLens.get m = some (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) ∧
        t = (Anneal.RefFrame.exitFrameWithProtectors tree0 [2]).tree
      modifies := [csuDstLens]
      frameTags := [2]
      canNormal := false
      canUnwind := true }
  have hPanicCut :
      CallSpecCut (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
        (csuAdapter true) panicSpec := by
    apply seal_callSpecCut (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
    intro m₀ t₀ hPre
    rw [hPre.1, hPre.2]
    refine wpUntil_step
      (ops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none)) ?_
    change (csuCalleeStep ⟨true, csuInitialMem, tree0⟩).wp _ _ _
    have hGet0 : csuDstLens.get csuInitialMem =
        some (csuInitialBytes.drop 8 |>.take 8) := rfl
    let ⟨m', hSet⟩ := ByteSubLens.set_isSome_of_get
      (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) hGet0 rfl
    unfold csuCalleeStep
    dsimp only
    rw [hSet]
    exact ⟨rfl, UpdatesOnly.of_single_set hSet,
      (Anneal.RefFrame.exitFrameWithProtectors tree0 [2]).tree, rfl,
      ByteSubLens.get_set hSet, rfl⟩
  exact callSpecCut_unwind_propagate_chain
    (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
    (prefixFrames := [midFrame]) (suffixFrames := [outerFrame])
    hPanicCut ⟨rfl, rfl⟩
    (fun _ _ _ hCanN _ _ _ => by cases hCanN)
    (fun m₁ tRel _ hUpd _ hPost => by
      rw [hPost.2]
      let t1 := (Anneal.RefFrame.exitFrameWithProtectors tree0 [2]).tree
      let t2 := (Anneal.RefFrame.exitFrameWithProtectors t1 [1]).tree
      refine ⟨t2, ⟨rfl, t2, rfl, rfl⟩, ?_⟩
      exact ⟨rfl, rfl, rfl, hPost.1,
        updatesOnly_frame_disjoint hDisj hUpd, rfl⟩)
    (fun _ _ hA _ _ => by cases hA)

/-- Canary 5 (Negative / Fail-Closed):
1. Foreign write on an accessed protected tag raises `.ProtectedDisabled`
   during `performRangedAccess` and during `exitFrameWithProtectors` when
   releasing a conflicting protected sibling, making `evalProtectedRefFrameExit`
   fail closed to `.fault`.
2. Releasing an unprotected tag returns `.MissingTag` and makes
   `evalProtectedRefFrameExit` fail closed to `.fault`.
3. Returning normally into `onRet = none` is strictly refuted by
   `not_wpCallSite_diverging_of_done_returned`.
4. Unwinding into `onUnwind = .unreachable` is strictly refuted by
   `not_wpCallSite_unreachable_of_done_unwound`.
5. Non-disjoint lens `[0..12)` overlaps `csuDstLens = [8..16)` and is rejected
   by `allNatLensesSeparatedBool`. -/
theorem canary_callStackUnwind_fail_closed_negatives :
    let conflictTree : Anneal.RefFrame.RangedBorrowTree :=
      { topology := Anneal.RefFrame.topo3
        protectedTags := [1, 2]
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                   (2, ⟨.Unique, true⟩)]⟩] }
    let missingTagTree : Anneal.RefFrame.RangedBorrowTree :=
      Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1]
    let rf : RefFrame Nat := ⟨csuDstLens, ⟨some 10, .cleanup 99⟩⟩
    let exNorm : CalleeExit Nat (ByteRunAtom Nat) :=
      .returned 1 (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns)
    let exUnw : CalleeExit Nat (ByteRunAtom Nat) :=
      .unwound (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns)
    (Anneal.RefFrame.exitFrameWithProtectors conflictTree [1, 2]).status =
      .AccessFailure 0 8 2 (.ProtectedDisabled .Unique) ∧
    (evalProtectedRefFrameExit ⟨rf, [1, 2]⟩ csuInitialMem conflictTree exNorm).1 =
      .fault ∧
    (evalProtectedRefFrameExit ⟨rf, [1, 2]⟩ csuInitialMem conflictTree exUnw).1 =
      .fault ∧
    (Anneal.RefFrame.exitFrameWithProtectors missingTagTree [1, 2]).status =
      .MissingTag 2 ∧
    (evalProtectedRefFrameExit ⟨rf, [1, 2]⟩ csuInitialMem missingTagTree exNorm).1 =
      .fault ∧
    allNatLensesSeparatedBool [csuDstLens] { addr := 0, offset := 0, len := 12 } =
      false ∧
    (¬ wpCallSite (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
        (csuAdapter false) ⟨none, .continue_⟩ (fun _ => false) [2]
        (fun _ _ _ _ => True) (fun _ _ _ => True)
        (fun _ _ => True) (fun _ _ => True)
        csuInitialMem
        (Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2])) ∧
    (¬ wpCallSite (wops := MirWpOps.ofDetStep csuCalleeStep (fun _ => none))
        (csuAdapter true) ⟨some 10, .unreachable⟩ (fun _ => false) [2]
        (fun _ _ _ _ => True) (fun _ _ _ => True)
        (fun _ _ => True) (fun _ _ => True)
        csuInitialMem
        (Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2])) := by
  let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2]
  have hGet0 : csuDstLens.get csuInitialMem =
      some (csuInitialBytes.drop 8 |>.take 8) := rfl
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · let ⟨m', hSet⟩ := ByteSubLens.set_isSome_of_get
      (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns) hGet0 rfl
    have hDone : csuCalleeStep ⟨false, csuInitialMem, tree0⟩ =
        .done (.returned 77 m' tree0) := by
      unfold csuCalleeStep
      dsimp only
      rw [hSet]
    exact not_wpCallSite_diverging_of_done_returned
      (step := csuCalleeStep) (tag := fun _ => none)
      (csuAdapter false) .continue_ (fun _ => false) [2]
      (fun _ _ _ _ => True) (fun _ _ _ => True)
      (fun _ _ => True) (fun _ _ => True)
      csuInitialMem m' tree0 tree0 (.returned 77 m' tree0) 77 hDone rfl
  · let ⟨m', hSet⟩ := ByteSubLens.set_isSome_of_get
      (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) hGet0 rfl
    have hDone : csuCalleeStep ⟨true, csuInitialMem, tree0⟩ =
        .done (.unwound m' tree0) := by
      unfold csuCalleeStep
      dsimp only
      rw [hSet]
    exact not_wpCallSite_unreachable_of_done_unwound
      (step := csuCalleeStep) (tag := fun _ => none)
      (csuAdapter true) (some 10) (fun _ => false) [2]
      (fun _ _ _ _ => True) (fun _ _ _ => True)
      (fun _ _ => True) (fun _ _ => True)
      csuInitialMem m' tree0 tree0 (.unwound m' tree0) hDone rfl

/-- Co-frame protector ordering canary (Miri frame-exit order): on a single
`[0..8)` segment where sibling tags `1` and `2` are both `(Unique, accessed)`,
1. exiting a frame owning BOTH tags faults with `.ProtectedDisabled`, because
   tag `2` is still protected while tag `1`'s implicit exit write disables it;
2. the same tree with only tag `1` protected and owned releases cleanly, so
   the fault in (1) is caused by the co-frame protector staying active during
   the exit access (stripping protectors first would hide it);
3. the failed exit in (1) strips no protector, and
   `evalProtectedRefFrameExit` on a frame claiming the unprotected tag `2`
   faults while leaving `protectedTags = [1]` unchanged. -/
theorem canary_coframe_protector_active_during_exit_access :
    let mkTree (prot : List Nat) : Anneal.RefFrame.RangedBorrowTree :=
      { topology := Anneal.RefFrame.topo3
        protectedTags := prot
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                   (2, ⟨.Unique, true⟩)]⟩] }
    let rf : RefFrame Nat := ⟨csuDstLens, ⟨some 10, .cleanup 99⟩⟩
    let exNorm : CalleeExit Nat (ByteRunAtom Nat) :=
      .returned 1 (flattenByteRuns (ByteRunCodec.id Nat) csuNormalRuns)
    (Anneal.RefFrame.exitFrameWithProtectors (mkTree [1, 2]) [1, 2]).status =
      .AccessFailure 0 8 2 (.ProtectedDisabled .Unique) ∧
    (Anneal.RefFrame.exitFrameWithProtectors (mkTree [1]) [1]).status =
      .Released ∧
    (Anneal.RefFrame.exitFrameWithProtectors (mkTree [1]) [1]).tree.protectedTags =
      [] ∧
    (Anneal.RefFrame.exitFrameWithProtectors (mkTree [1, 2]) [1, 2]).tree.protectedTags =
      [1, 2] ∧
    (evalProtectedRefFrameExit ⟨rf, [1, 2]⟩ csuInitialMem (mkTree [1]) exNorm).1 =
      .fault ∧
    (evalProtectedRefFrameExit ⟨rf, [1, 2]⟩ csuInitialMem (mkTree [1])
      exNorm).2.protectedTags = [1] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (evalProtectedRefFrameExit_fault_of_unprotected_frameTag
      (t := 2) _ _ _ _ rfl rfl).1
  · exact (evalProtectedRefFrameExit_fault_of_unprotected_frameTag
      (t := 2) _ _ _ _ rfl rfl).2

/-- Canary 6 (Positive + Negative): Callee abort propagation (`canAbort = true`),
`UpdatesOnly` validity (`lens_valid_after_updatesOnly_self`), disjoint framing
across `.abortTerminate`, and fail-closed rejection when `onTerminate` forbids
aborts (`not_wpCallSite_of_done_abort_rejected`). -/
theorem canary_callSpecCut_abort_terminate_and_frame :
    let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2]
    let abortStep : CsuCalleeState →
        StepOutcome CsuCalleeState (FrameExitOutcome CsuMem Nat) Unit := fun s =>
      match csuDstLens.set s.mem (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) with
      | none => .fault ()
      | some m' => .done (.abortTerminate m' s.tree)
    wpCallSite (wops := MirWpOps.ofDetStep abortStep (fun _ => none))
      (csuAdapter true) ⟨some 10, .terminate⟩ (fun _ => false) [2]
      (fun _ _ _ _ => False) (fun _ _ _ => False) (fun _ _ => False)
      (fun m _ =>
        csuDstLens.get m = some (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) ∧
        csuSrcLens.get m = csuSrcLens.get csuInitialMem ∧
        (∃ bs, csuDstLens.get m = some bs ∧ bs.length = 8))
      csuInitialMem tree0 ∧
    (¬ wpCallSite (wops := MirWpOps.ofDetStep abortStep (fun _ => none))
        (csuAdapter true) ⟨some 10, .terminate⟩ (fun _ => false) [2]
        (fun _ _ _ _ => True) (fun _ _ _ => True)
        (fun _ _ => True) (fun _ _ => False)
        csuInitialMem tree0) := by
  let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2]
  let abortStep : CsuCalleeState →
      StepOutcome CsuCalleeState (FrameExitOutcome CsuMem Nat) Unit := fun s =>
    match csuDstLens.set s.mem (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) with
    | none => .fault ()
    | some m' => .done (.abortTerminate m' s.tree)
  let abortSpec : CallSpec CsuMem Nat Nat :=
    { pre := fun m _ => ∃ bs, csuDstLens.get m = some bs
      postRet := fun _ _ _ => False
      postUnwind := fun _ _ => False
      postAbort := fun m _ =>
        csuDstLens.get m = some (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns)
      modifies := [csuDstLens]
      frameTags := [2]
      canNormal := false
      canUnwind := false
      canAbort := true }
  have hDisj : ∀ L : ByteSubLens Nat, L ∈ abortSpec.modifies →
      L.Disjoint CsuMem csuSrcLens :=
    allDisjoint_of_allNatLensesSeparatedBool rfl
  have hGet0 : csuDstLens.get csuInitialMem =
      some (csuInitialBytes.drop 8 |>.take 8) := rfl
  have hAbortCut :
      CallSpecCut (wops := MirWpOps.ofDetStep abortStep (fun _ => none))
        (csuAdapter true) abortSpec := by
    apply seal_callSpecCut (wops := MirWpOps.ofDetStep abortStep (fun _ => none))
    intro m₀ t₀ hPre
    let ⟨old, hGet⟩ := hPre
    refine wpUntil_step (ops := MirWpOps.ofDetStep abortStep (fun _ => none)) ?_
    change (abortStep ⟨true, m₀, t₀⟩).wp _ _ _
    let ⟨m', hSet⟩ := ByteSubLens.set_isSome_of_get
      (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) hGet rfl
    dsimp only [abortStep]
    rw [hSet]
    exact ⟨rfl, UpdatesOnly.of_single_set hSet, ByteSubLens.get_set hSet⟩
  refine ⟨?_, ?_⟩
  · exact callSpecCut_call_normal_terminate
      (wops := MirWpOps.ofDetStep abortStep (fun _ => none))
      hAbortCut ⟨_, hGet0⟩
      (fun _ _ _ hN _ _ _ => by cases hN)
      (fun _ _ hU _ _ _ => by cases hU)
      (fun m₁ _ _ hUpd hPost => by
        let ⟨bs, hG, hLen, _⟩ := lens_valid_after_updatesOnly_self hGet0 hUpd
        exact ⟨hPost, updatesOnly_frame_disjoint hDisj hUpd, bs, hG, hLen⟩)
  · let ⟨m', hSet⟩ := ByteSubLens.set_isSome_of_get
      (flattenByteRuns (ByteRunCodec.id Nat) csuPartialRuns) hGet0 rfl
    have hDone : abortStep ⟨true, csuInitialMem, tree0⟩ =
        .done (.abortTerminate m' tree0) := by
      dsimp only [abortStep]
      rw [hSet]
    exact not_wpCallSite_of_done_abort_rejected
      (step := abortStep) (tag := fun _ => none)
      (csuAdapter true) ⟨some 10, .terminate⟩ (fun _ => false) [2]
      (fun _ _ _ _ => True) (fun _ _ _ => True)
      (fun _ _ => True) (fun _ _ => False)
      csuInitialMem m' tree0 tree0 (.abortTerminate m' tree0) hDone rfl
      (fun hF => hF)

/-- Operational unwinder canary (`evalUnwindStack`) on a 2-frame caller stack
over `tree0` (protected tags `[1, 2]`):
1. a `.continue_` frame owning tag `2` releases it and the unwind lands on the
   validated cleanup pad `7` of the next frame, with memory unchanged and only
   tag `1` still protected;
2. the same stack with an invalid pad (`8`, rejected by `isCleanupBb`) faults;
3. a `.continue_` frame claiming the unprotected tag `3` faults (`.MissingTag`);
4. a lone `.continue_` frame propagates to the root with tag `2` released;
5. a `.unreachable` frame faults and a `.terminate` frame aborts. -/
theorem canary_evalUnwindStack_operational :
    let tree0 := Anneal.RefFrame.mkSharedTopo3Tree16 .Frozen true .Unique true [1, 2]
    let contFrame (tags : List Nat) : SavedCallFrame Unit Nat :=
      { ctx := (), cont := ⟨some 3, .continue_⟩, isCleanupBb := fun _ => false,
        callerModifies := [], callerTags := tags }
    let padFrame (bb : Nat) : SavedCallFrame Unit Nat :=
      { ctx := (), cont := ⟨some 4, .cleanup bb⟩,
        isCleanupBb := fun b => Nat.beq b 7, callerModifies := [], callerTags := [] }
    let edgeFrame (act : UnwindAction4) : SavedCallFrame Unit Nat :=
      { ctx := (), cont := ⟨some 5, act⟩, isCleanupBb := fun _ => true,
        callerModifies := [], callerTags := [] }
    (match evalUnwindStack [contFrame [2], padFrame 7] csuInitialMem tree0 with
      | .landed st =>
        st.blockIdx = 7 ∧ st.callers = [] ∧ st.mem = csuInitialMem ∧
          st.tree.protectedTags = [1]
      | _ => False) ∧
    (match evalUnwindStack [contFrame [2], padFrame 8] csuInitialMem tree0 with
      | .fault => True
      | _ => False) ∧
    (match evalUnwindStack [contFrame [3], padFrame 7] csuInitialMem tree0 with
      | .fault => True
      | _ => False) ∧
    (match evalUnwindStack [contFrame [2]] csuInitialMem tree0 with
      | .rootUnwind m t => m = csuInitialMem ∧ t.protectedTags = [1]
      | _ => False) ∧
    (match evalUnwindStack [edgeFrame .unreachable] csuInitialMem tree0 with
      | .fault => True
      | _ => False) ∧
    (match evalUnwindStack [edgeFrame .terminate] csuInitialMem tree0 with
      | .abortTerminate m t => m = csuInitialMem ∧ t = tree0
      | _ => False) := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, trivial, trivial, ⟨rfl, rfl⟩, trivial, ⟨rfl, rfl⟩⟩

end Anneal.ParametricCore
