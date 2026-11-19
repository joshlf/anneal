/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.ExtTreeMapAllocAndNoWritable
import MiniRustSpec.Correspondence.Pointers

/-!
# `#[rustc_no_writable]` & Static-Access Temporary Retag Correspondence (`MiniRustSpec`)

Cross-model correspondence connecting `Anneal.ExtTreeMapAllocAndNoWritable`
(Parts 2A and 2B) and `Trusted.Rustc.V2026_06_01.MirSemantics` to the
mechanically generated MiniRust Tree Borrows specification (`MiniRustSpec.Gen`,
`MiniRustSpec.Interp`, and `MiniRustSpec.Correspondence.MachTB.wfLive`):

1. **Part 1 (`charon#1619` + `minirust#295`)**:
   - Permission translation `permToMiniRust` from Anneal's `TreeBorrowPerm` +
     `(isProtected, accessed)` onto MiniRust's `Gen.Permission`
     (`PermissionUnprot` / `PermissionProt`). It is a surjection with section
     `permFromMiniRust` (`permToMiniRust_fromMiniRust`), NOT a bijection: its exact
     kernel is `permErasure` (`permToMiniRust_eq_iff_permErasure`, Part 5.3). Also
     the protected-`ReservedIM` exclusion, `PermissionProt.unprotect` vs.
     `protectorEndAccessIsWriteMiniRust?` agreement, and lockstep single-node
     simulation of `stepNodeOnRangeRead` / `stepNodeOnRangeWrite` by
     `Permission.transition`.
   - Universal policy correspondence relating `selectFnEntryPolicy`,
     `MiriRetagPolicyMirror.create`, and `Trusted.fnEntryRetagPerm` to
     MiniRust's `ReborrowSettings.new` across `&T`, `&mut T`, `Box<T>`,
     `!Unpin` skip-retag (`pinned_mutable_or_box_fnEntry_skips_retag`),
     `Protected::Weak` vs. `Protected::Strong`, and zero-sized `&mut ()`.
   - Concrete two-sided `TBM` / `MachTB` (`stepsTB` + `MachTB.wfLive`) + `Trusted`
     (`stepMirFn` + `evalFnEntryRetagWithParamMap`) + `FnEntryBorrowWorld`
     separation between `#[rustc_no_writable]` (`core::mem::forget`-style) and
     standard `&mut` `FnEntry` retags, plus multi-parameter disjoint-range
     frame-exit agreement (`execFrameExit_miri_eq_miniRust_of_disjointFrame`
     and `TreeBorrowsMemory.end_call`).

2. **Part 2 (`charon#1620`)**:
   - General symbolic byte-level equivalence between `StaticTyDesc` /
     `staticFreezeSegments` / `byteInNonZeroUnsafeCell` / `retagStaticPreservedAt`
     / `evalRawMutStaticWriteMiri` and MiniRust's `cellsToFreezeMask` /
     `UnsafeCellStrategy.freeze_mask` / `ReborrowSettings.new` for arbitrary
     disjoint in-bounds `UnsafeCell` layouts in any field declaration order.
   - End-to-end `TBM`, `MachTB` (`stepsTB` + `MachTB.wfLive`), and
     `ExtTreeMapAllocAndNoWritable` correspondence and separation across the
     four canonical static shapes:
     (a) pure `Freeze` (`static S: u32`),
     (b) pure `!Freeze` (`static S: AtomicI32` / `UnsafeCell<u32>`),
     (c) non-ZST mixed composite (`static S: (u8, Padding[3], AtomicI32)`,
         including out-of-offset-order `repr(Rust)` field declarations), and
     (d) zero-sized `UnsafeCell<()>` composite (`static S: (u8, UnsafeCell<()>)`).

3. **Part 3 (Closed Non-Vacuity Canaries)**: zero-hypothesis canary theorems
   exercising positive and negative cases of Parts 1 and 2.

4. **Part 4 (Symbolic Whole-Tree Calculus & Relational Simulation)**:
   - a byte-window calculus for `Node.transitionRange` and a path-indexed
     whole-tree specification of `Node.access` (forward, success inversion, error
     provenance) for borrow trees of ARBITRARY shape and size;
   - `TreeBorrowsMemory.store` / `load` proved equal to `Node.access` on the
     addressed allocation (`tbm_store_eq_node_access`, `tbm_load_eq_node_access`);
   - the whole-tree relational invariant `TreeSimInv` between a flat
     `FnEntryBorrowWorld` and a nested MiniRust borrow tree, and the inductive
     simulation of `execWorldRangeRead` / `execWorldRangeWrite` by `Node.access`
     and by `TreeBorrowsMemory.load` / `store`
     (`tree_read_simulates_node_access`, `tree_write_simulates_node_access`,
     `tbm_load_simulates_execWorldRangeRead`,
     `tbm_store_simulates_execWorldRangeWrite`), with a constructive decidable
     checker (`treeSimInv_of_bool`) and a closed canary.

5. **Part 5 (`#[rustc_no_writable]` Edge Cases on Real `TreeBorrowsMemory`
   Operations)**: the `<[T]>::get_mut` wide-slice pattern, the
   `ReservedFrz { conflicted: true }` lifecycle, a foreign active strong protector
   on overlapping bytes (`TBM` and `MachTB`), read-only allocations, and
   overlapping-range frame-exit order / implicit protector-end access separation
   on `TreeBorrowsMemory.end_call`, each with whole-state `TreeSimInv` lockstep
   against `execFnEntryMutRetagPrunedSourceOrder`, `execWorldRangeRead`,
   `execWorldRangeWrite`, `execFrameExitMiniRust`, and `execFrameExitMiri`; plus
   the envelope of the `stepMirFnWithParamMap` adapter and the kernel of
   `permToMiniRust`.

6. **Part 6 (Symbolic Static-Retag Write Theorem)**: for ANY valid static layout
   (`StaticCellsValid`: any field order, zero-sized `UnsafeCell<()>` anywhere), the
   preserved `#1620` retag on real `TreeBorrowsMemory.retag_ptr` followed by
   `TreeBorrowsMemory.store` at ANY byte window succeeds iff every byte of the
   window lies inside a non-zero-length `UnsafeCell`
   (`tbm_staticPreserved_retag_then_store_iff`), whereas the pre-`#1620` erased raw
   access accepts every in-bounds write; field-order independence and zero-length
   cell irrelevance of MiniRust's `cells_to_freeze_mask`.

7. **Axiom pins**: `#guard_msgs (whitespace := lax) in #print axioms` for EVERY
   public theorem of this file: each uses at most `{propext, Quot.sound}`
   (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).

## Scope of the whole-tree results

- `TreeSimInv` relates the two models on ONE byte window that every Anneal node's
  coarse range overlaps. Outside that regime the coarse-range world
  over-approximates UB
  (`sliceGetMut_world_agreement_and_coarse_range_overapproximation`).
- The access simulations assume that the Anneal ancestor set coincides with the
  MiniRust path-prefix relation (`hloc`) and that Miri's `SkipSelfAndChildren`
  pruning is inactive (`hnoprune`); both are decidable on concrete worlds and are
  discharged in the canaries.
- `FnEntry` retag and frame exit are related at the whole-state level on concrete
  multi-node worlds (Part 5), not yet by a symbolic tree theorem.
- The general MiniRust preservation theorem `stepsTB_wfLive` depends on
  `Classical.choice`, so post-state `MachTB.wfLive` facts are established by the
  constructive checker of Section 0.
-/

namespace MiniRustSpec.NoWritableAndStaticRetag

set_option Elab.async false

open Anneal.ExtTreeMapAllocAndNoWritable
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence

/-! ## Section 0: Constructive `wfLive` Checker, List Helpers, & `TBM` / `MachTB` Builders -/

mutual

/-- Computable boolean verifier for `MiniRustSpec.Correspondence.Node.wf`. -/
def nodeWfBool (sz : Nat) : Gen.Node → Bool
  | ⟨children, permissions, prot⟩ =>
    (permissions.length == sz) &&
    permissions.all (fun p => Permission.matches_protector p prot) &&
    childrenWfBool sz children

/-- Computable boolean verifier for `MiniRustSpec.Correspondence.Node.childrenWf`. -/
def childrenWfBool (sz : Nat) : List Gen.Node → Bool
  | [] => true
  | c :: cs => nodeWfBool sz c && childrenWfBool sz cs

end

/-- Computable boolean verifier for `TreeBorrowsMemory.wfLive`. -/
def tbmWfLiveBool (tbm : Gen.TreeBorrowsMemory Gen.x86_64) : Bool :=
  tbm.mem.allocations.all fun alloc =>
    !alloc.live || nodeWfBool (Allocation.size alloc).bytes alloc.extra.root

/-- Computable boolean verifier for `MachTB.wfLive`. -/
def machTBWfLiveBool (m : MachTB) : Bool :=
  tbmWfLiveBool m.mem.memory

mutual

/-- Constructive soundness of `nodeWfBool` (zero `Classical.choice`). -/
theorem nodeWf_of_bool (sz : Nat) : ∀ n : Gen.Node,
    nodeWfBool sz n = true → Node.wf sz n
  | ⟨children, permissions, prot⟩, h => by
    simp only [nodeWfBool, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    exact ⟨h.1.1, h.1.2, childrenWf_of_bool sz children h.2⟩

/-- Constructive soundness of `childrenWfBool` (zero `Classical.choice`). -/
theorem childrenWf_of_bool (sz : Nat) : ∀ cs : List Gen.Node,
    childrenWfBool sz cs = true → Node.childrenWf sz cs
  | [], _ => trivial
  | c :: cs, h => by
    simp only [childrenWfBool, Bool.and_eq_true] at h
    exact ⟨nodeWf_of_bool sz c h.1, childrenWf_of_bool sz cs h.2⟩

end

/-- Constructive soundness of `tbmWfLiveBool` into `TreeBorrowsMemory.wfLive`. -/
theorem tbm_wfLive_of_bool (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (h : tbmWfLiveBool tbm = true) : TreeBorrowsMemory.wfLive tbm := by
  intro alloc hmem hlive
  unfold tbmWfLiveBool at h
  have ha := List.all_eq_true.mp h alloc hmem
  rw [hlive] at ha
  exact nodeWf_of_bool (Allocation.size alloc).bytes alloc.extra.root ha

/-- Constructive soundness of `machTBWfLiveBool` into `MachTB.wfLive`. -/
theorem machTB_wfLive_of_bool (m : MachTB)
    (h : machTBWfLiveBool m = true) : MachTB.wfLive m :=
  tbm_wfLive_of_bool m.mem.memory h

/-- Combined boolean check that `Interp.stepsTB n m0` succeeds and satisfies
`MachTB.wfLive`. -/
def stepsTBOkAndWfLiveBool (n : Nat) (m0 : MachTB) : Bool :=
  match Interp.stepsTB n m0 with
  | .ok m' => machTBWfLiveBool m'
  | .error _ => false

/-- Constructive lifting of `stepsTBOkAndWfLiveBool` to existential
`Interp.stepsTB n m0 = .ok m' ∧ MachTB.wfLive m'` (zero `Classical.choice`). -/
theorem machTB_steps_ok_and_wfLive_of_bool {n : Nat} {m0 : MachTB}
    (h : stepsTBOkAndWfLiveBool n m0 = true) :
    ∃ m', Interp.stepsTB n m0 = .ok m' ∧ MachTB.wfLive m' := by
  unfold stepsTBOkAndWfLiveBool at h
  cases hs : Interp.stepsTB n m0 with
  | error _ => rw [hs] at h; cases h
  | ok m' =>
    rw [hs] at h
    exact ⟨m', rfl, machTB_wfLive_of_bool m' h⟩

/-- Combined boolean check that a `TBM` trace succeeds and preserves
`TreeBorrowsMemory.wfLive`. -/
def tbmTraceOkAndWfLiveBool (r : Interp (Gen.TreeBorrowsMemory Gen.x86_64)) : Bool :=
  match r with
  | .ok tbm' => tbmWfLiveBool tbm'
  | .error _ => false

/-- Constructive lifting of `tbmTraceOkAndWfLiveBool` to existential
`r = .ok tbm' ∧ TreeBorrowsMemory.wfLive tbm'`. -/
theorem tbm_trace_ok_and_wfLive_of_bool {r : Interp (Gen.TreeBorrowsMemory Gen.x86_64)}
    (h : tbmTraceOkAndWfLiveBool r = true) :
    ∃ tbm', r = .ok tbm' ∧ TreeBorrowsMemory.wfLive tbm' := by
  unfold tbmTraceOkAndWfLiveBool at h
  cases hr : r with
  | error _ => rw [hr] at h; cases h
  | ok tbm' =>
    rw [hr] at h
    exact ⟨tbm', rfl, tbm_wfLive_of_bool tbm' h⟩

private theorem nwsr_mapM_loop_eq_map {α β : Type} (f : α → β) (g : α → Interp β)
    (hg : ∀ a, g a = .ok (f a)) :
    ∀ (xs : List α) (acc : List β),
      List.mapM.loop g xs acc = .ok (acc.reverse ++ xs.map f)
  | [], acc => by simp [List.mapM.loop, pure, Except.pure]
  | x :: xs, acc => by
    simp only [List.mapM.loop, hg x, bind, Except.bind]
    rw [nwsr_mapM_loop_eq_map f g hg xs (f x :: acc)]
    simp [List.reverse_cons, List.append_assoc]

private theorem nwsr_mapM_eq_ok_map {α β : Type} (f : α → β) (g : α → Interp β)
    (hg : ∀ a, g a = .ok (f a)) (xs : List α) :
    xs.mapM g = .ok (xs.map f) := by
  show List.mapM.loop g xs [] = .ok (xs.map f)
  rw [nwsr_mapM_loop_eq_map f g hg xs []]
  simp

private theorem nwsr_map_const_eq_replicate {α β : Type} (b : β) :
    ∀ xs : List α, xs.map (fun _ => b) = List.replicate xs.length b
  | [] => rfl
  | _ :: xs => by
    simp only [List.map_cons, List.length_cons, List.replicate_succ,
      nwsr_map_const_eq_replicate b xs]

private theorem nwsr_protected_yes_strong : Protected.yes .Strong = true := rfl
private theorem nwsr_protected_yes_weak : Protected.yes .Weak = true := rfl
private theorem nwsr_protected_yes_no : Protected.yes .No = false := rfl

private theorem nwsr_mapM_perm_mut_noWrite (info : Gen.PointeeInfo) (mask : List Bool) :
    mask.mapM (fun freeze => ReborrowSettings.perm (.Ref .Mutable info) .Strong false true freeze) =
      .ok (List.replicate mask.length (.Prot (.Reserved false false))) := by
  rw [nwsr_mapM_eq_ok_map (fun _ => Gen.Permission.Prot (.Reserved false false)) _
    (fun b => by cases b <;> rfl) mask, nwsr_map_const_eq_replicate]

private theorem nwsr_mapM_perm_mut_write (info : Gen.PointeeInfo) (mask : List Bool) :
    mask.mapM (fun freeze => ReborrowSettings.perm (.Ref .Mutable info) .Strong true true freeze) =
      .ok (List.replicate mask.length (.Prot .Unique)) := by
  rw [nwsr_mapM_eq_ok_map (fun _ => Gen.Permission.Prot .Unique) _
    (fun b => by cases b <;> rfl) mask, nwsr_map_const_eq_replicate]

private theorem nwsr_mapM_perm_box_noWrite (info : Gen.PointeeInfo) (mask : List Bool) :
    mask.mapM (fun freeze => ReborrowSettings.perm (.Box info) .Weak false true freeze) =
      .ok (List.replicate mask.length (.Prot (.Reserved false false))) := by
  rw [nwsr_mapM_eq_ok_map (fun _ => Gen.Permission.Prot (.Reserved false false)) _
    (fun b => by cases b <;> rfl) mask, nwsr_map_const_eq_replicate]

private theorem nwsr_mapM_perm_box_write (info : Gen.PointeeInfo) (mask : List Bool) :
    mask.mapM (fun freeze => ReborrowSettings.perm (.Box info) .Weak true true freeze) =
      .ok (List.replicate mask.length (.Prot .Unique)) := by
  rw [nwsr_mapM_eq_ok_map (fun _ => Gen.Permission.Prot .Unique) _
    (fun b => by cases b <;> rfl) mask, nwsr_map_const_eq_replicate]

private theorem nwsr_mapM_perm_shared_strong (info : Gen.PointeeInfo) (iw : Bool) (mask : List Bool) :
    mask.mapM (fun freeze => ReborrowSettings.perm (.Ref .Immutable info) .Strong iw true freeze) =
      .ok (mask.map (fun frz => if frz then .Prot (.Frozen false) else .Prot .Cell)) :=
  nwsr_mapM_eq_ok_map (fun frz => if frz then Gen.Permission.Prot (.Frozen false) else .Prot .Cell) _
    (fun b => by cases b <;> rfl) mask

private theorem nwsr_mapM_perm_shared_no (info : Gen.PointeeInfo) (iw : Bool) (mask : List Bool) :
    mask.mapM (fun freeze => ReborrowSettings.perm (.Ref .Immutable info) .No iw true freeze) =
      .ok (mask.map (fun frz => if frz then .Unprot .Frozen else .Unprot .Cell)) :=
  nwsr_mapM_eq_ok_map (fun frz => if frz then Gen.Permission.Unprot .Frozen else .Unprot .Cell) _
    (fun b => by cases b <;> rfl) mask

private theorem nwsr_getElem?_append_left_of_lt {α : Type} {xs ys : List α} {i : Nat}
    (h : i < xs.length) : (xs ++ ys)[i]? = xs[i]? :=
  List.getElem?_append_left h

private theorem nwsr_getElem?_append_right_of_le {α : Type} {xs ys : List α} {i : Nat}
    (h : xs.length ≤ i) : (xs ++ ys)[i]? = ys[i - xs.length]? :=
  List.getElem?_append_right h

private theorem nwsr_getElem?_replicate_lt {α : Type} {n i : Nat} {a : α}
    (h : i < n) : (List.replicate n a)[i]? = some a := by
  rw [List.getElem?_replicate]
  simp only [h, ↓reduceIte]

/-! ### Common MiniRust Type, Byte, and Machine Helpers -/

/-- Unsigned 32-bit MiniRust integer type (`u32`). -/
def u32ItMR : Gen.IntType := ⟨.Unsigned, ⟨4⟩⟩

/-- Signed 32-bit MiniRust integer type (`i32`). -/
def i32ItMR : Gen.IntType := ⟨.Signed, ⟨4⟩⟩

/-- Unsigned 8-bit MiniRust integer type (`u8`). -/
def u8ItMR : Gen.IntType := ⟨.Unsigned, ⟨1⟩⟩

/-- Signed 64-bit pointer-offset MiniRust integer type (`isize` on `x86_64`). -/
def isizeItMR : Gen.IntType := ⟨.Signed, ⟨8⟩⟩

/-- MiniRust `u32` type. -/
def u32TyMR : Gen.Type := .Int u32ItMR

/-- MiniRust `i32` type. -/
def i32TyMR : Gen.Type := .Int i32ItMR

/-- MiniRust `u8` type. -/
def u8TyMR : Gen.Type := .Int u8ItMR

/-- MiniRust `isize` type (`x86_64`). -/
def isizeTyMR : Gen.Type := .Int isizeItMR

/-- MiniRust zero-sized unit tuple type `()`. -/
def unitTyMR : Gen.Type := .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none

/-- MiniRust thin raw pointer type (`*const _` / `*mut _`). -/
def rawPtrTyMR : Gen.Type := .Ptr (.Raw .None)

/-- MiniRust `PointeeInfo` for zero-sized `()`. -/
def zstUnitPointeeInfoMR : Gen.PointeeInfo :=
  { layout := .Sized ⟨0⟩ ⟨1⟩
    inhabited := true
    unsafe_cells := .Sized []
    freeze := true
    unpin := true }

/-- MiniRust `PointeeInfo` for `!Unpin` `u32` (pinned mutable reference target). -/
def pinnedU32PointeeInfoMR : Gen.PointeeInfo :=
  { layout := .Sized ⟨4⟩ ⟨4⟩
    inhabited := true
    unsafe_cells := .Sized []
    freeze := true
    unpin := false }

/-- Little-endian 4-byte `TreeBorrowsProvenance` payload with low byte `b0`. -/
def tbU32Bytes (b0 : UInt8) : List (Gen.AbstractByte Gen.TreeBorrowsProvenance) :=
  [.Init b0 none, .Init 0 none, .Init 0 none, .Init 0 none]

/-- Single-byte `TreeBorrowsProvenance` payload `[.Init b none]`. -/
def tbU8Bytes (b : UInt8) : List (Gen.AbstractByte Gen.TreeBorrowsProvenance) :=
  [.Init b none]

/-- Vtable lookup callback for thin-pointer Tree Borrows calls. -/
def nwsrVtableLookup :
    Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable :=
  fun _ => specPanic "unexpected vtable lookup on thin pointer"

/-- Construct a live `TreeBorrowsMemory` allocation with a fresh unprotected
`.Unique` root node matching `data.length`. -/
def mkRootAllocTB (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (addr : Int) (align : Nat) (kind : Gen.AllocationKind) :
    Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra where
  data := data
  addr := addr
  align := ⟨align⟩
  kind := kind
  live := true
  extra := {
    root := {
      children := []
      permissions := List.replicate data.length (.Unprot .Unique)
      «protected» := .No
    }
  }

/-- Every allocation constructed by `mkRootAllocTB` satisfies `Node.wf`. -/
theorem mkRootAllocTB_wf (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (addr : Int) (align : Nat) (kind : Gen.AllocationKind) :
    Node.wf (Allocation.size (mkRootAllocTB data addr align kind)).bytes
      (mkRootAllocTB data addr align kind).extra.root := by
  refine ⟨List.length_replicate, fun p hp => ?_, trivial⟩
  rw [List.eq_of_mem_replicate hp]
  rfl

/-- Lossless decidable projection of a byte list (data bytes only). -/
def projDataBytesTB (bs : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) :
    List (Option UInt8) :=
  bs.map fun
    | .Uninit => none
    | .Init b _ => some b

/-- Decidable projection of a `TBM` byte-load result (`Sum.inl` on `.ok`,
`Sum.inr msg` on `Stop.ub msg`, `none` on non-UB stop). -/
def tbBytesOutcome (r : Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance))) :
    Option (List (Option UInt8) ⊕ String) :=
  match r with
  | .ok bs => some (.inl (projDataBytesTB bs))
  | .error (.ub msg) => some (.inr msg)
  | .error _ => none

/-- Decidable projection of a `TBM` unit/state trace (`Sum.inl ()` on `.ok`,
`Sum.inr msg` on `Stop.ub msg`, `none` on non-UB stop). -/
def tbUnitOutcome {α : Type} (r : Interp α) : Option (Unit ⊕ String) :=
  match r with
  | .ok _ => some (.inl ())
  | .error (.ub msg) => some (.inr msg)
  | .error _ => none

/-- Decidable caller-return snapshot after `n` `MachTB` steps:
`(retAlloc live, retAlloc data bytes, thread stack depths)`. -/
def machRetSnapshot (m0 : MachTB) (n : Nat) :
    Option (Option (Bool × List (Option UInt8)) × List Nat) :=
  match Interp.stepsTB n m0 with
  | .ok m' =>
    some (m'.mem.memory.mem.allocations[0]?.map (fun a => (a.live, projDataBytesTB a.data)),
      m'.threads.map (·.stack.length))
  | .error _ => none

/-- Decidable allocation data snapshot for allocation index `idx` after `n`
`MachTB` steps. -/
def machAllocSnapshot (m0 : MachTB) (n idx : Nat) :
    Option (Bool × List (Option UInt8)) :=
  match Interp.stepsTB n m0 with
  | .ok m' =>
    m'.mem.memory.mem.allocations[idx]?.map (fun a => (a.live, projDataBytesTB a.data))
  | .error _ => none

/-- Decidable `Stop` outcome after `n` `MachTB` steps (`none` if `.ok`). -/
def machStopOutcome (m0 : MachTB) (n : Nat) : Option Stop :=
  match Interp.stepsTB n m0 with
  | .ok _ => none
  | .error e => some e

/-- Decidable top-frame protector count after `n` `MachTB` steps. -/
def machTopProtectorCount (m0 : MachTB) (n : Nat) : Option Nat :=
  match Interp.stepsTB n m0 with
  | .ok m' =>
    (m'.threads[0]?.bind (fun t => t.stack.getLast?)).map (fun fr => fr.extra.protectors.length)
  | .error _ => none

/-- Sentinel bottom caller function used by `MachTB` execution harnesses so
`Terminator.Return` stores the return value into `allocations[0]` and lands at
`bbName 1`. -/
def nwsrSentinelFn : Gen.Function where
  locals := ⟨[]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Unreachable, .Regular⟩),
    (bbName 1, ⟨[], .Unreachable, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := true

/-- Sentinel caller frame holding `BackToCaller` return control. -/
def nwsrSentinelFrame : Gen.StackFrame TBM where
  func := nwsrSentinelFn
  locals := ⟨[]⟩
  stack_pop_action := .BottomOfStack
  next_block := bbName 0
  next_stmt := 0
  extra := TreeBorrowsMemory.new_call

/-! ## Part 1: Permission & Policy Bijection + `#[rustc_no_writable]` vs. Standard `&mut` `FnEntry` Retags (`charon#1619` + `minirust#295`) -/

/-! ### 1.1 Exact Permission, Protector, Access-Kind, and Single-Node Transition Bijection -/

/-- Map Anneal/Trusted `TreeBorrowPerm` together with `(isProtected, accessed)`
flags to MiniRust `Gen.Permission`.

Returns `none` strictly on `(isProtected = true, perm = .reservedIM)`, capturing
MiniRust's structural invariant that `PermissionProt` has no `ReservedIm`
constructor (`RetagStepErr.protectedReservedIMInvariant`). -/
def permToMiniRust (isProt accessed : Bool) : TreeBorrowPerm → Option Gen.Permission
  | .cell => some (if isProt then .Prot .Cell else .Unprot .Cell)
  | .reservedFrz c => some (if isProt then .Prot (.Reserved accessed c) else .Unprot .Reserved)
  | .reservedIM => if isProt then none else some (.Unprot .ReservedIm)
  | .unique => some (if isProt then .Prot .Unique else .Unprot .Unique)
  | .frozen => some (if isProt then .Prot (.Frozen accessed) else .Unprot .Frozen)
  | .disabled => some (if isProt then .Prot .Disabled else .Unprot .Disabled)

/-- Inverse map from MiniRust `Gen.Permission` back to Anneal
`(TreeBorrowPerm, isProtected, accessed)`. -/
def permFromMiniRust : Gen.Permission → TreeBorrowPerm × Bool × Bool
  | .Unprot .Cell => (.cell, false, true)
  | .Unprot .Reserved => (.reservedFrz false, false, true)
  | .Unprot .ReservedIm => (.reservedIM, false, true)
  | .Unprot .Unique => (.unique, false, true)
  | .Unprot .Frozen => (.frozen, false, true)
  | .Unprot .Disabled => (.disabled, false, true)
  | .Prot .Cell => (.cell, true, false)
  | .Prot (.Reserved hlr hfr) => (.reservedFrz hfr, true, hlr)
  | .Prot .Unique => (.unique, true, true)
  | .Prot (.Frozen hlr) => (.frozen, true, hlr)
  | .Prot .Disabled => (.disabled, true, false)

/-- Map `MiriRetagPolicyMirror.ProtectorKind` option to MiniRust `Gen.Protected`. -/
def protToMiniRust : Option MiriRetagPolicyMirror.ProtectorKind → Gen.Protected
  | none => .No
  | some .strongProtector => .Strong
  | some .weakProtector => .Weak

/-- Map Anneal `isWrite : Bool` option to MiniRust `Option Gen.AccessKind`. -/
def accessIsWriteToMiniRust : Option Bool → Option Gen.AccessKind
  | none => none
  | some false => some .Read
  | some true => some .Write

/-- Map Anneal `isLocal : Bool` to MiniRust `Gen.NodeRelation`. -/
def nodeRelToMiniRust (isLocal : Bool) : Gen.NodeRelation :=
  if isLocal then .Local else .Foreign

/-- `permToMiniRust` is a total left-inverse of `permFromMiniRust` across every
MiniRust `Gen.Permission` state (zero hypotheses, zero axioms). -/
theorem permToMiniRust_fromMiniRust (p : Gen.Permission) :
    let r := permFromMiniRust p
    permToMiniRust r.2.1 r.2.2 r.1 = some p := by
  cases p with
  | Unprot u => cases u <;> rfl
  | Prot pr =>
    cases pr with
    | Cell => rfl
    | Reserved hlr hfr => cases hlr <;> cases hfr <;> rfl
    | Unique => rfl
    | Frozen hlr => cases hlr <;> rfl
    | Disabled => rfl

/-- Protected `.reservedIM` has no MiniRust `PermissionProt` image, matching
`RetagStepErr.protectedReservedIMInvariant`. -/
theorem permToMiniRust_protected_reservedIM_none (acc : Bool) :
    permToMiniRust true acc .reservedIM = none := rfl

/-- On every non-`reservedIM` permission, `permToMiniRust true acc tp` produces
a protected `Gen.Permission` matching both `.Strong` and `.Weak` protectors, and
`permFromMiniRust` recovers `tp` (and `acc` on `.reservedFrz` / `.frozen`). -/
theorem permFromMiniRust_toMiniRust_prot (tp : TreeBorrowPerm) (acc : Bool)
    (hne : tp ≠ .reservedIM) :
    ∃ p : Gen.Permission,
      permToMiniRust true acc tp = some p ∧
      Permission.matches_protector p .Strong = true ∧
      Permission.matches_protector p .Weak = true ∧
      (permFromMiniRust p).1 = tp ∧
      (permFromMiniRust p).2.1 = true ∧
      ((tp = .frozen ∨ ∃ c, tp = .reservedFrz c) → (permFromMiniRust p).2.2 = acc) := by
  cases tp with
  | reservedIM => exact absurd rfl hne
  | cell =>
    exact ⟨.Prot .Cell, rfl, rfl, rfl, rfl, rfl,
      fun h => by rcases h with h | ⟨_, h⟩ <;> cases h⟩
  | reservedFrz c =>
    exact ⟨.Prot (.Reserved acc c), rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | unique =>
    exact ⟨.Prot .Unique, rfl, rfl, rfl, rfl, rfl,
      fun h => by rcases h with h | ⟨_, h⟩ <;> cases h⟩
  | frozen =>
    exact ⟨.Prot (.Frozen acc), rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | disabled =>
    exact ⟨.Prot .Disabled, rfl, rfl, rfl, rfl, rfl,
      fun h => by rcases h with h | ⟨_, h⟩ <;> cases h⟩

/-- **Protector-end access correspondence (`protectorEndAccessIsWriteMiniRust?` ↔
`PermissionProt.unprotect`)**: for every non-`reservedIM` `TreeTagNode` `n`,
MiniRust's `PermissionProt.unprotect` on `n`'s protected permission image emits
the exact `Option Gen.AccessKind` predicted by `protectorEndAccessIsWriteMiniRust? n`
and drops the permission to the corresponding unprotected state. In particular,
an accessed `.reservedFrz c` (`#[rustc_no_writable]` `&mut` with no write) emits
`some .Read` rather than `some .Write`, whereas `.unique` (standard `&mut`) emits
`some .Write`. -/
theorem protectorEndAccessMiniRust_eq_unprotect (n : TreeTagNode)
    (hnoIM : n.perm ≠ .reservedIM) :
    ∃ pProt : Gen.PermissionProt,
      permToMiniRust true n.accessed n.perm = some (.Prot pProt) ∧
      (PermissionProt.unprotect pProt).2 =
        accessIsWriteToMiniRust (protectorEndAccessIsWriteMiniRust? n) ∧
      permToMiniRust false n.accessed n.perm =
        some (.Unprot (PermissionProt.unprotect pProt).1) := by
  cases hp : n.perm with
  | reservedIM => exact absurd hp hnoIM
  | cell => exact ⟨.Cell, rfl, by simp [protectorEndAccessIsWriteMiniRust?, hp, accessIsWriteToMiniRust, PermissionProt.unprotect], rfl⟩
  | unique => exact ⟨.Unique, rfl, by simp [protectorEndAccessIsWriteMiniRust?, hp, accessIsWriteToMiniRust, PermissionProt.unprotect], rfl⟩
  | disabled => exact ⟨.Disabled, rfl, by simp [protectorEndAccessIsWriteMiniRust?, hp, accessIsWriteToMiniRust, PermissionProt.unprotect], rfl⟩
  | frozen =>
    cases ha : n.accessed <;>
      exact ⟨.Frozen _, rfl,
        by simp [protectorEndAccessIsWriteMiniRust?, hp, ha, accessIsWriteToMiniRust, PermissionProt.unprotect], rfl⟩
  | reservedFrz c =>
    cases ha : n.accessed <;>
      exact ⟨.Reserved _ c, rfl,
        by simp [protectorEndAccessIsWriteMiniRust?, hp, ha, accessIsWriteToMiniRust, PermissionProt.unprotect], rfl⟩

/-- Combined Miri + MiniRust protector-end access agreement on every reachable
protected node (`perm ≠ .disabled`, `perm ≠ .reservedIM`, `perm = .unique →
accessed = true`). -/
theorem protectorEndAccess_miri_eq_miniRust_and_unprotect (n : TreeTagNode)
    (hdis : n.perm ≠ .disabled) (hnoIM : n.perm ≠ .reservedIM)
    (huniq : n.perm = .unique → n.accessed = true) :
    ∃ pProt : Gen.PermissionProt,
      permToMiniRust true n.accessed n.perm = some (.Prot pProt) ∧
      (PermissionProt.unprotect pProt).2 =
        accessIsWriteToMiniRust (protectorEndAccessIsWrite? n) ∧
      protectorEndAccessIsWrite? n = protectorEndAccessIsWriteMiniRust? n := by
  have heq := protectorEndAccess_miri_eq_miniRust n hdis huniq
  rcases protectorEndAccessMiniRust_eq_unprotect n hnoIM with ⟨pProt, hp, hunp, _⟩
  exact ⟨pProt, hp, by rw [heq]; exact hunp, heq⟩

/-- **Lockstep single-node READ simulation** between `stepNodeOnRangeRead`
(`Anneal.ExtTreeMapAllocAndNoWritable`) and `Permission.transition _ .Read _`
(`MiniRustSpec.Interp`) across all protected and unprotected states in the
reachable MiniRust envelope (`isProtected → perm ≠ .reservedIM` and
`isProtected ∧ perm = .unique → accessed = true`). -/
theorem stepNodeOnRangeRead_simulates_permission_transition
    (activeProtectors : List Nat) (isLocal : Bool) (off len : Nat) (n : TreeTagNode)
    (hov : rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hnoProtIM : n.isProtected activeProtectors = true → n.perm ≠ .reservedIM)
    (hprotUniqAcc : n.isProtected activeProtectors = true → n.perm = .unique → n.accessed = true) :
    ∃ p : Gen.Permission,
      permToMiniRust (n.isProtected activeProtectors) n.accessed n.perm = some p ∧
      (∀ n', stepNodeOnRangeRead activeProtectors isLocal off len n = .ok n' →
        ∃ p', Permission.transition p .Read (nodeRelToMiniRust isLocal) = .ok p' ∧
          permToMiniRust (n.isProtected activeProtectors) n'.accessed n'.perm = some p') ∧
      (∀ e, stepNodeOnRangeRead activeProtectors isLocal off len n = .error e →
        ∃ msg, Permission.transition p .Read (nodeRelToMiniRust isLocal) = .error (.ub msg)) := by
  rcases n with ⟨tag, par, perm, rOff, rLen, prot, acc⟩
  dsimp only at hov hnoProtIM hprotUniqAcc ⊢
  generalize hprot : (TreeTagNode.mk tag par perm rOff rLen prot acc).isProtected activeProtectors = isP
  rw [hprot] at hnoProtIM hprotUniqAcc
  cases isP with
  | false =>
    cases isLocal <;> cases perm <;>
    · refine ⟨_, rfl, ?_, ?_⟩
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at hok
        cases hok <;> exact ⟨_, rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at herr
        cases herr <;> exact ⟨_, rfl⟩
  | true =>
    cases perm with
    | reservedIM => exact absurd rfl (hnoProtIM rfl)
    | unique =>
      have hacc : acc = true := hprotUniqAcc rfl rfl
      subst hacc
      cases isLocal <;> refine ⟨.Prot .Unique, rfl, ?_, ?_⟩
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at hok
        cases hok
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at herr
        exact ⟨"Tree Borrows: foreign read of protected Unique reference", rfl⟩
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot .Unique, rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
    | cell =>
      cases isLocal <;> refine ⟨.Prot .Cell, rfl, ?_, ?_⟩
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot .Cell, rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot .Cell, rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
    | frozen =>
      cases isLocal <;> refine ⟨.Prot (.Frozen acc), rfl, ?_, ?_⟩
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot (.Frozen acc), rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot (.Frozen true), rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
    | reservedFrz c =>
      cases isLocal <;> refine ⟨.Prot (.Reserved acc c), rfl, ?_, ?_⟩
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot (.Reserved acc true), rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at herr
        cases herr
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot (.Reserved true c), rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
    | disabled =>
      cases isLocal <;> refine ⟨.Prot .Disabled, rfl, ?_, ?_⟩
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot .Disabled, rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
      · intro n' hok
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        cases hok
      · intro e herr
        simp only [stepNodeOnRangeRead, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        exact ⟨"Tree Borrows: local read of protected Disabled reference", rfl⟩

/-- **Lockstep single-node WRITE simulation** between `stepNodeOnRangeWrite`
(`Anneal.ExtTreeMapAllocAndNoWritable`) and `Permission.transition _ .Write _`
(`MiniRustSpec.Interp`) across all protected and unprotected states in the
reachable MiniRust envelope. -/
theorem stepNodeOnRangeWrite_simulates_permission_transition
    (activeProtectors : List Nat) (isLocal : Bool) (off len : Nat) (n : TreeTagNode)
    (hov : rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hnoProtIM : n.isProtected activeProtectors = true → n.perm ≠ .reservedIM)
    (hprotUniqAcc : n.isProtected activeProtectors = true → n.perm = .unique → n.accessed = true) :
    ∃ p : Gen.Permission,
      permToMiniRust (n.isProtected activeProtectors) n.accessed n.perm = some p ∧
      (∀ n', stepNodeOnRangeWrite activeProtectors isLocal off len n = .ok n' →
        ∃ p', Permission.transition p .Write (nodeRelToMiniRust isLocal) = .ok p' ∧
          permToMiniRust (n.isProtected activeProtectors) n'.accessed n'.perm = some p') ∧
      (∀ e, stepNodeOnRangeWrite activeProtectors isLocal off len n = .error e →
        ∃ msg, Permission.transition p .Write (nodeRelToMiniRust isLocal) = .error (.ub msg)) := by
  rcases n with ⟨tag, par, perm, rOff, rLen, prot, acc⟩
  dsimp only at hov hnoProtIM hprotUniqAcc ⊢
  generalize hprot : (TreeTagNode.mk tag par perm rOff rLen prot acc).isProtected activeProtectors = isP
  rw [hprot] at hnoProtIM hprotUniqAcc
  cases isP with
  | false =>
    cases perm with
    | reservedFrz c =>
      cases isLocal <;> cases c <;>
      · refine ⟨.Unprot .Reserved, rfl, ?_, ?_⟩
        · intro n' hok
          simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            hprot] at hok
          cases hok <;> exact ⟨_, rfl, rfl⟩
        · intro e herr
          simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            hprot] at herr
          cases herr <;> exact ⟨_, rfl⟩
    | cell | reservedIM | unique | frozen | disabled =>
      cases isLocal <;>
      · refine ⟨_, rfl, ?_, ?_⟩
        · intro n' hok
          simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            hprot] at hok
          cases hok <;> exact ⟨_, rfl, rfl⟩
        · intro e herr
          simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            hprot] at herr
          cases herr <;> exact ⟨_, rfl⟩
  | true =>
    cases perm with
    | reservedIM => exact absurd rfl (hnoProtIM rfl)
    | unique =>
      have hacc : acc = true := hprotUniqAcc rfl rfl
      subst hacc
      cases isLocal <;> refine ⟨.Prot .Unique, rfl, ?_, ?_⟩
      · intro n' hok
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at hok
        cases hok
      · intro e herr
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at herr
        exact ⟨_, rfl⟩
      · intro n' hok
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot .Unique, rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
    | cell =>
      cases isLocal <;> refine ⟨.Prot .Cell, rfl, ?_, ?_⟩
      · intro n' hok
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot .Cell, rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
      · intro n' hok
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot .Cell, rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
    | frozen =>
      cases isLocal <;> cases acc <;> refine ⟨.Prot (.Frozen _), rfl, ?_, ?_⟩
      · intro n' hok
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot .Disabled, rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at herr
        cases herr
      · intro n' hok
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at hok
        cases hok
      · intro e herr
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hprot] at herr
        exact ⟨_, rfl⟩
      · intro n' hok
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        cases hok
      · intro e herr
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        exact ⟨_, rfl⟩
      · intro n' hok
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        cases hok
      · intro e herr
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        exact ⟨_, rfl⟩
    | reservedFrz c =>
      cases isLocal with
      | false =>
        cases acc <;> cases c <;>
        · refine ⟨.Prot (.Reserved _ _), rfl, ?_, ?_⟩
          · intro n' hok
            simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              hprot] at hok
            cases hok <;> exact ⟨_, rfl, rfl⟩
          · intro e herr
            simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              hprot] at herr
            cases herr <;> exact ⟨_, rfl⟩
      | true =>
        cases c with
        | false =>
          cases acc <;>
          · refine ⟨.Prot (.Reserved _ false), rfl, ?_, ?_⟩
            · intro n' hok
              simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
              cases hok <;> exact ⟨_, rfl, rfl⟩
            · intro e herr
              simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
              cases herr <;> exact ⟨_, rfl⟩
        | true =>
          cases acc <;>
          · refine ⟨.Prot (.Reserved _ true), rfl, ?_, ?_⟩
            · intro n' hok
              simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                hprot] at hok
              cases hok <;> exact ⟨_, rfl, rfl⟩
            · intro e herr
              simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                hprot] at herr
              cases herr <;> exact ⟨_, rfl⟩
    | disabled =>
      cases isLocal <;> refine ⟨.Prot .Disabled, rfl, ?_, ?_⟩
      · intro n' hok
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        injection hok with hEq; subst hEq
        exact ⟨.Prot .Disabled, rfl, rfl⟩
      · intro e herr
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        cases herr
      · intro n' hok
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        cases hok
      · intro e herr
        simp only [stepNodeOnRangeWrite, hov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at herr
        exact ⟨_, rfl⟩

/-! ### 1.2 Policy & `ReborrowSettings.new` Correspondence (`selectFnEntryPolicy`, `MiriRetagPolicyMirror.create`, `Trusted.fnEntryRetagPerm` ↔ `ReborrowSettings.new`) -/

/-- Construct MiniRust `Gen.PointeeInfo` from Anneal `ParamTypeFacts` and sized
layout/cell metadata. -/
def pointeeInfoOfFacts (facts : ParamTypeFacts) (size align : Nat)
    (cells : List (Gen.Offset × LibSpecr.Size)) : Gen.PointeeInfo where
  layout := .Sized ⟨size⟩ ⟨align⟩
  inhabited := true
  unsafe_cells := .Sized cells
  freeze := facts.isFreeze
  unpin := facts.isUnpin && facts.isUnsafeUnpin

/-- Map Anneal `RefParamKind` + `PointeeInfo` to MiniRust `Gen.PtrType`. -/
def ptrTypeOfParamKind (kind : RefParamKind) (info : Gen.PointeeInfo) : Gen.PtrType :=
  match kind with
  | .shared => .Ref .Immutable info
  | .mutable => .Ref .Mutable info
  | .box => .Box info

/-- **`!Unpin` `&mut` and `Box` skip-retag correspondence**: connects
`pinned_mutable_or_box_fnEntry_skips_retag` directly to MiniRust's
`ReborrowSettings.new = .ok none` and proves `TreeBorrowsMemory.retag_ptr` is
the exact identity (no new borrow-tree node, no protector pushed). -/
theorem reborrowSettings_pinned_mut_box_skip
    (facts : ParamTypeFacts) (attrs : ParamRetagAttrs)
    (hnotUnpin : (facts.isUnpin && facts.isUnsafeUnpin) = false)
    (size align : Nat) (cells : List (Gen.Offset × LibSpecr.Size))
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (frameExtra : Gen.TreeBorrowsFrameExtra)
    (ptr : Gen.Pointer Gen.TreeBorrowsProvenance)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable) :
    let info := pointeeInfoOfFacts facts size align cells
    selectFnEntryPolicy facts .mutable attrs = .skipRetag ∧
    selectFnEntryPolicy facts .box attrs = .skipRetag ∧
    MiriRetagPolicyMirror.create facts .mutable .fnEntry attrs = none ∧
    MiriRetagPolicyMirror.create facts .box .fnEntry attrs = none ∧
    ReborrowSettings.new lookup ptr (ptrTypeOfParamKind .mutable info) true
      ⟨attrs.implicitWrites⟩ (!attrs.rustcNoWritable) = .ok none ∧
    ReborrowSettings.new lookup ptr (ptrTypeOfParamKind .box info) true
      ⟨attrs.implicitWrites⟩ (!attrs.rustcNoWritable) = .ok none ∧
    TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind .mutable info) true
      (!attrs.rustcNoWritable) lookup = .ok (ptr, tbm, frameExtra) ∧
    TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind .box info) true
      (!attrs.rustcNoWritable) lookup = .ok (ptr, tbm, frameExtra) := by
  rcases pinned_mutable_or_box_fnEntry_skips_retag facts attrs hnotUnpin with ⟨hm, hb⟩
  have hcm : MiriRetagPolicyMirror.create facts .mutable .fnEntry attrs = none := by
    simp [MiriRetagPolicyMirror.create, hnotUnpin]
  have hcb : MiriRetagPolicyMirror.create facts .box .fnEntry attrs = none := by
    simp [MiriRetagPolicyMirror.create, hnotUnpin]
  have hrm : ∀ params : Gen.TreeBorrowsParams,
      ReborrowSettings.new lookup ptr (ptrTypeOfParamKind .mutable (pointeeInfoOfFacts facts size align cells))
        true params (!attrs.rustcNoWritable) = .ok none := by
    intro params
    simp [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts, PtrType.safe_pointee,
      hnotUnpin, pure, Except.pure]
  have hrb : ∀ params : Gen.TreeBorrowsParams,
      ReborrowSettings.new lookup ptr (ptrTypeOfParamKind .box (pointeeInfoOfFacts facts size align cells))
        true params (!attrs.rustcNoWritable) = .ok none := by
    intro params
    simp [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts, PtrType.safe_pointee,
      hnotUnpin, pure, Except.pure]
  refine ⟨hm, hb, hcm, hcb, hrm ⟨attrs.implicitWrites⟩, hrb ⟨attrs.implicitWrites⟩, ?_, ?_⟩
  · unfold TreeBorrowsMemory.retag_ptr
    rw [hrm tbm.params]
    rfl
  · unfold TreeBorrowsMemory.retag_ptr
    rw [hrb tbm.params]
    rfl

/-- **Universal `&mut` / `Box` `FnEntry` policy correspondence**: for EVERY
`facts`, `kind ∈ {.mutable, .box}`, `attrs`, and valid `cellsToFreezeMask`
output `mask`, MiniRust's `ReborrowSettings.new` agrees exactly with
`selectFnEntryPolicy`, `MiriRetagPolicyMirror.create`, and (under
`rustcNoWritable`) `Trusted.Rustc.V2026_06_01.MirSemantics.fnEntryRetagPerm`:
- `.skipRetag` → `ReborrowSettings.new = .ok none` (`!Unpin`);
- `.writableChildWrite` → `inside = replicate mask.length (.Prot .Unique)`
  (`init_access = some .Write`), `outside = .Prot (.Reserved false false)`,
  protector `.Weak` for `Box` and `.Strong` for `&mut`;
- `.rustcNoWritable` → `inside = replicate mask.length (.Prot (.Reserved false false))`
  (`init_access = some .Read`, matching `fnEntryRetagPerm .mut pointee`),
  `outside = .Prot (.Reserved false false)`, protector `.Weak` for `Box` and
  `.Strong` for `&mut`. -/
theorem reborrowSettings_fnEntry_mutOrBox_eq_policy
    {Provenance : Type}
    (lookup : Gen.ThinPointer Provenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Provenance)
    (facts : ParamTypeFacts) (kind : RefParamKind) (attrs : ParamRetagAttrs)
    (hkind : kind ≠ .shared)
    (size align : Nat) (cells : List (Gen.Offset × LibSpecr.Size)) (mask : List Bool)
    (hmask : cellsToFreezeMask cells ⟨size⟩ = .ok mask) :
    let info := pointeeInfoOfFacts facts size align cells
    let expectedProt : Gen.Protected := if kind = .box then .Weak else .Strong
    ReborrowSettings.new lookup ptr (ptrTypeOfParamKind kind info) true
      ⟨attrs.implicitWrites⟩ (!attrs.rustcNoWritable) =
      match selectFnEntryPolicy facts kind attrs with
      | .skipRetag => .ok none
      | .writableChildWrite =>
        .ok (some {
          inside := List.replicate mask.length (.Prot .Unique)
          outside := .Prot (.Reserved false false)
          «protected» := expectedProt
        })
      | .rustcNoWritable =>
        .ok (some {
          inside := List.replicate mask.length (.Prot (.Reserved false false))
          outside := .Prot (.Reserved false false)
          «protected» := expectedProt
        }) := by
  rcases facts with ⟨u, uu, frz⟩
  rcases attrs with ⟨iw, rnw⟩
  cases kind with
  | shared => exact absurd rfl hkind
  | mutable =>
    cases hu : (u && uu) with
    | false =>
      simp [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts, PtrType.safe_pointee,
        selectFnEntryPolicy, hu, pure, Except.pure]
    | true =>
      cases iw <;> cases rnw
      · -- iw = false, rnw = false -> rustcNoWritable
        simp only [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts,
          PtrType.safe_pointee, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          nwsr_protected_yes_strong, Bool.and_false, Bool.false_and,
          UnsafeCellStrategy.freeze_mask, hmask, bind, Except.bind,
          nwsr_mapM_perm_mut_noWrite, selectFnEntryPolicy, pure, Except.pure]
        cases frz <;> rfl
      · -- iw = false, rnw = true -> rustcNoWritable
        simp only [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts,
          PtrType.safe_pointee, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          nwsr_protected_yes_strong, Bool.and_false,
          UnsafeCellStrategy.freeze_mask, hmask, bind, Except.bind,
          nwsr_mapM_perm_mut_noWrite, selectFnEntryPolicy, pure, Except.pure]
        cases frz <;> rfl
      · -- iw = true, rnw = false -> writableChildWrite
        simp only [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts,
          PtrType.safe_pointee, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          nwsr_protected_yes_strong, Bool.not_false, Bool.and_true,
          UnsafeCellStrategy.freeze_mask, hmask, bind, Except.bind,
          nwsr_mapM_perm_mut_write, selectFnEntryPolicy, pure, Except.pure]
        cases frz <;> rfl
      · -- iw = true, rnw = true -> rustcNoWritable
        simp only [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts,
          PtrType.safe_pointee, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          nwsr_protected_yes_strong, Bool.and_false,
          UnsafeCellStrategy.freeze_mask, hmask, bind, Except.bind,
          nwsr_mapM_perm_mut_noWrite, selectFnEntryPolicy, pure, Except.pure]
        cases frz <;> rfl
  | box =>
    cases hu : (u && uu) with
    | false =>
      simp [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts, PtrType.safe_pointee,
        selectFnEntryPolicy, hu, pure, Except.pure]
    | true =>
      cases iw <;> cases rnw
      · simp only [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts,
          PtrType.safe_pointee, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          nwsr_protected_yes_weak, Bool.and_false, Bool.false_and,
          UnsafeCellStrategy.freeze_mask, hmask, bind, Except.bind,
          nwsr_mapM_perm_box_noWrite, selectFnEntryPolicy, pure, Except.pure]
        cases frz <;> rfl
      · simp only [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts,
          PtrType.safe_pointee, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          nwsr_protected_yes_weak, Bool.and_false,
          UnsafeCellStrategy.freeze_mask, hmask, bind, Except.bind,
          nwsr_mapM_perm_box_noWrite, selectFnEntryPolicy, pure, Except.pure]
        cases frz <;> rfl
      · simp only [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts,
          PtrType.safe_pointee, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          nwsr_protected_yes_weak, Bool.not_false, Bool.and_true,
          UnsafeCellStrategy.freeze_mask, hmask, bind, Except.bind,
          nwsr_mapM_perm_box_write, selectFnEntryPolicy, pure, Except.pure]
        cases frz <;> rfl
      · simp only [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts,
          PtrType.safe_pointee, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          nwsr_protected_yes_weak, Bool.and_false,
          UnsafeCellStrategy.freeze_mask, hmask, bind, Except.bind,
          nwsr_mapM_perm_box_noWrite, selectFnEntryPolicy, pure, Except.pure]
        cases frz <;> rfl

/-- Shared `&T` `FnEntry` correspondence: `ReborrowSettings.new` always mints
`Protected::Strong` with `.Prot (.Frozen false)` on frozen bytes and `.Prot .Cell`
on `UnsafeCell` bytes, matching `fnEntry_shared_childPerms_outside_mut_models`
and `Trusted.fnEntryRetagPerm .not`. -/
theorem reborrowSettings_fnEntry_shared_eq_create
    {Provenance : Type}
    (lookup : Gen.ThinPointer Provenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Provenance)
    (facts : ParamTypeFacts) (attrs : ParamRetagAttrs)
    (size align : Nat) (cells : List (Gen.Offset × LibSpecr.Size)) (mask : List Bool)
    (hmask : cellsToFreezeMask cells ⟨size⟩ = .ok mask) :
    let info := pointeeInfoOfFacts facts size align cells
    ReborrowSettings.new lookup ptr (ptrTypeOfParamKind .shared info) true
      ⟨attrs.implicitWrites⟩ (!attrs.rustcNoWritable) =
      .ok (some {
        inside := mask.map (fun frz => if frz then .Prot (.Frozen false) else .Prot .Cell)
        outside := if facts.isFreeze then .Prot (.Frozen false) else .Prot .Cell
        «protected» := .Strong
      }) ∧
    (MiriRetagPolicyMirror.create facts .shared .fnEntry attrs).map
        (fun p => (p.freezePermission, p.nonfreezePermission, p.outsidePermission, p.protector)) =
      some (.frozen, .cell, if facts.isFreeze then .frozen else .cell, some .strongProtector) := by
  have hshared := (fnEntry_shared_childPerms_outside_mut_models facts attrs).2
  refine ⟨?_, hshared⟩
  simp only [ReborrowSettings.new, ptrTypeOfParamKind, pointeeInfoOfFacts, PtrType.safe_pointee,
    Bool.false_eq_true, ↓reduceIte, UnsafeCellStrategy.freeze_mask, hmask, bind, Except.bind,
    nwsr_mapM_perm_shared_strong]
  cases facts.isFreeze <;> rfl

/-- Exact `Trusted.fnEntryRetagPerm` and `retagPerm .fnEntry` alignment under
`#[rustc_no_writable]`: MiniRust's inside permission `.Prot (.Reserved false false)`
maps back to `fnEntryRetagPerm .mut pointee = retagPerm .fnEntry .mut pointee =
.reservedFrz false` with initial access `some .Read` (no implicit write). -/
theorem trusted_fnEntryRetagPerm_aligns_with_miniRust_noWritable (pointee : RigidTy) :
    retagPerm .fnEntry .mut pointee = fnEntryRetagPerm .mut pointee ∧
    fnEntryRetagPerm .mut pointee = .reservedFrz false ∧
    permToMiniRust true false (fnEntryRetagPerm .mut pointee) =
      some (.Prot (.Reserved false false)) ∧
    Permission.init_access (.Prot (.Reserved false false)) = some .Read ∧
    Permission.init_access (.Prot .Unique) = some .Write :=
  ⟨retagPerm_fnEntry_eq_fnEntryRetagPerm .mut pointee,
   fnEntryRetagPerm_mut_eq_reservedFrz pointee,
   rfl, rfl, rfl⟩

/-- **`Box<T>` weak protector vs. `&mut T` strong protector**: for every `Unpin`
pointee and both implicit-write settings, `Box<T>` gets `Protected::Weak` (which
never blocks `Node.contains_strong_protector_preventing_deallocation`) while
`&mut T` gets `Protected::Strong` (which blocks deallocation for both `.Unique`
and locally-read `.Reserved true _`). -/
theorem box_weak_vs_mut_strong_dealloc_law (sz : Nat) (hsz : 0 < sz) (hfr : Bool) :
    let weakUniq : Gen.Node := ⟨[], List.replicate sz (.Prot .Unique), .Weak⟩
    let weakRes : Gen.Node := ⟨[], List.replicate sz (.Prot (.Reserved true hfr)), .Weak⟩
    let strongUniq : Gen.Node := ⟨[], List.replicate sz (.Prot .Unique), .Strong⟩
    let strongRes : Gen.Node := ⟨[], List.replicate sz (.Prot (.Reserved true hfr)), .Strong⟩
    Node.contains_strong_protector_preventing_deallocation weakUniq = false ∧
    Node.contains_strong_protector_preventing_deallocation weakRes = false ∧
    Node.contains_strong_protector_preventing_deallocation strongUniq = true ∧
    Node.contains_strong_protector_preventing_deallocation strongRes = true := by
  cases sz with
  | zero => exact absurd hsz (Nat.lt_irrefl 0)
  | succ k =>
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp [Node.contains_strong_protector_preventing_deallocation, List.replicate_succ,
        Permission.prevents_deallocation, PermissionProt.prevents_deallocation]
    · simp [Node.contains_strong_protector_preventing_deallocation, List.replicate_succ,
        Permission.prevents_deallocation, PermissionProt.prevents_deallocation]

/-- **Zero-sized `&mut ()` invariance on `TreeBorrowsMemory.retag_ptr`**: for
`zstUnitPointeeInfoMR` (`size = 0`), `ReborrowSettings.new` produces `inside = []`
for BOTH `fnImplicitWrites = true` and `fnImplicitWrites = false`, so
`TreeBorrowsMemory.retag_ptr` computes the exact same result regardless of
`#[rustc_no_writable]`, matching `fnEntryMutRetag_zst_no_write` and
`applyParamFnEntryImplicitWrite_zst_noop`. -/
theorem tbm_retag_zst_implicit_writes_invariance
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (frameExtra : Gen.TreeBorrowsFrameExtra)
    (ptr : Gen.Pointer Gen.TreeBorrowsProvenance)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable) :
    ReborrowSettings.new lookup ptr (.Ref .Mutable zstUnitPointeeInfoMR) true tbm.params true =
      .ok (some { inside := [], outside := .Prot (.Reserved false false), «protected» := .Strong }) ∧
    ReborrowSettings.new lookup ptr (.Ref .Mutable zstUnitPointeeInfoMR) true tbm.params false =
      .ok (some { inside := [], outside := .Prot (.Reserved false false), «protected» := .Strong }) ∧
    TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (.Ref .Mutable zstUnitPointeeInfoMR) true true lookup =
      TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (.Ref .Mutable zstUnitPointeeInfoMR) true false lookup := by
  have h1 : ReborrowSettings.new lookup ptr (.Ref .Mutable zstUnitPointeeInfoMR) true tbm.params true =
      .ok (some { inside := [], outside := .Prot (.Reserved false false), «protected» := .Strong }) := by
    cases h : tbm.params.implicit_writes <;>
      simp [ReborrowSettings.new, zstUnitPointeeInfoMR, PtrType.safe_pointee,
        UnsafeCellStrategy.freeze_mask, cellsToFreezeMask, cellsToFreezeMaskLoop,
        Protected.yes, ReborrowSettings.perm, h, bind, Except.bind, pure, Except.pure, List.mapM,
        List.mapM.loop]
  have h2 : ReborrowSettings.new lookup ptr (.Ref .Mutable zstUnitPointeeInfoMR) true tbm.params false =
      .ok (some { inside := [], outside := .Prot (.Reserved false false), «protected» := .Strong }) := by
    cases h : tbm.params.implicit_writes <;>
      simp [ReborrowSettings.new, zstUnitPointeeInfoMR, PtrType.safe_pointee,
        UnsafeCellStrategy.freeze_mask, cellsToFreezeMask, cellsToFreezeMaskLoop,
        Protected.yes, ReborrowSettings.perm, h, bind, Except.bind, pure, Except.pure, List.mapM,
        List.mapM.loop]
  refine ⟨h1, h2, ?_⟩
  unfold TreeBorrowsMemory.retag_ptr
  rw [h1, h2]

/-! ### 1.3 Two-Sided Separation on `TBM` (`TreeBorrowsMemory`) & `FnEntryBorrowWorld` -/

/-- Build a 4-byte `TBM` state with `root []`, mutable parent `parent [0]`
(`Unprot .Reserved`), and shared sibling `sib [1]` (`Unprot .Frozen`), optionally
initialized with `42u32` (`initBytes = true`) or left uninitialized (`false`). -/
def mkTbmTwoBranchSetup (initBytes : Bool) :
    Interp (Gen.Pointer Gen.TreeBorrowsProvenance × Gen.Pointer Gen.TreeBorrowsProvenance ×
      Gen.Pointer Gen.TreeBorrowsProvenance × Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← if initBytes then TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 42) ⟨4⟩ else pure tbm1
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance := { thin_pointer := rootThin, metadata := none }
  let (parentPtr, tbm3, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr (refPtrType .mut u32ItMR) false true nwsrVtableLookup
  let (sibPtr, tbm4, _) ←
    TreeBorrowsMemory.retag_ptr tbm3 frame1 rootPtr (refPtrType .not u32ItMR) false true nwsrVtableLookup
  pure (rootPtr, parentPtr, sibPtr, tbm4)

/-- `TBM` lifecycle trace under `#[rustc_no_writable]` (`fnImplicitWrites = false`):
1. `FnEntry` retag creates `[0, 0]` (`Prot (.Reserved true false)`), keeping
   sibling `[1]` `Unprot .Frozen`;
2. Reading through sibling `[1]` during the call succeeds (`42`) and latches
   `had_foreign_read = true` (`Prot (.Reserved true true)`);
3. `end_call` (`release_protector`) emits an implicit READ (not WRITE), keeping
   sibling `[1]` `Unprot .Frozen`;
4. Reading through sibling `[1]` AFTER callee exit still succeeds (`42`);
5. Writing `99` through `[0, 0]` AFTER `end_call` unprotects it to `Unprot .Reserved`
   also succeeds, updating the allocation bytes to `99`. -/
def tbmNoWritableFullLifecycleTrace :
    Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance) ×
      List (Gen.AbstractByte Gen.TreeBorrowsProvenance) ×
      Gen.TreeBorrowsMemory Gen.x86_64) := do
  let (_, parentPtr, sibPtr, tbm0) ← mkTbmTwoBranchSetup true
  let frame0 := TreeBorrowsMemory.new_call
  let (childPtr, tbm1, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm0 frame0 parentPtr (refPtrType .mut u32ItMR) true false nwsrVtableLookup
  let (duringBytes, tbm2) ← TreeBorrowsMemory.load tbm1 sibPtr.thin_pointer ⟨4⟩ ⟨4⟩
  let tbm3 ← TreeBorrowsMemory.end_call tbm2 frame1
  let (afterExitBytes, tbm4) ← TreeBorrowsMemory.load tbm3 sibPtr.thin_pointer ⟨4⟩ ⟨4⟩
  let tbm5 ← TreeBorrowsMemory.store tbm4 childPtr.thin_pointer (tbU32Bytes 99) ⟨4⟩
  pure (duringBytes, afterExitBytes, tbm5)

/-- `TBM` trace: under `#[rustc_no_writable]`, after a foreign read latches
`had_foreign_read = true` (`Prot (.Reserved true true)`), a local write through
the protected child BEFORE `end_call` raises UB. -/
def tbmNoWritableConflictedLocalWriteUbTrace : Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let (_, parentPtr, sibPtr, tbm0) ← mkTbmTwoBranchSetup true
  let frame0 := TreeBorrowsMemory.new_call
  let (childPtr, tbm1, _frame1) ←
    TreeBorrowsMemory.retag_ptr tbm0 frame0 parentPtr (refPtrType .mut u32ItMR) true false nwsrVtableLookup
  let (_, tbm2) ← TreeBorrowsMemory.load tbm1 sibPtr.thin_pointer ⟨4⟩ ⟨4⟩
  TreeBorrowsMemory.store tbm2 childPtr.thin_pointer (tbU32Bytes 99) ⟨4⟩

/-- `TBM` trace: under `#[rustc_no_writable]`, a foreign/parent write through
`parent` while the child is strongly protected (`Prot (.Reserved true false)`)
raises Tree Borrows protector UB. -/
def tbmNoWritableParentWriteUbTrace : Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let (_, parentPtr, _, tbm0) ← mkTbmTwoBranchSetup true
  let frame0 := TreeBorrowsMemory.new_call
  let (_, tbm1, _frame1) ←
    TreeBorrowsMemory.retag_ptr tbm0 frame0 parentPtr (refPtrType .mut u32ItMR) true false nwsrVtableLookup
  TreeBorrowsMemory.store tbm1 parentPtr.thin_pointer (tbU32Bytes 99) ⟨4⟩

/-- `TBM` trace: under standard `&mut` (`fnImplicitWrites = true`,
`writableChildWrite`), `FnEntry` retag performs an implicit child write,
permanently disabling sibling `[1]` (`Unprot .Frozen → Unprot .Disabled`) so
even after `end_call` releases the protector, reading `[1]` raises
`"Tree Borrows: local read of Disabled reference"`. -/
def tbmWritableDisablesFrozenSiblingUbTrace :
    Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) := do
  let (_, parentPtr, sibPtr, tbm0) ← mkTbmTwoBranchSetup true
  let frame0 := TreeBorrowsMemory.new_call
  let (_, tbm1, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm0 frame0 parentPtr (refPtrType .mut u32ItMR) true true nwsrVtableLookup
  let tbm2 ← TreeBorrowsMemory.end_call tbm1 frame1
  let (bs, _) ← TreeBorrowsMemory.load tbm2 sibPtr.thin_pointer ⟨4⟩ ⟨4⟩
  pure bs

/-- `TBM` trace: against a **protected** `.Frozen` sibling (held by an outer
frame), standard `&mut` (`fnImplicitWrites = true`) faults immediately at
`FnEntry`, whereas `#[rustc_no_writable]` (`fnImplicitWrites = false`) succeeds
and preserves `TreeBorrowsMemory.wfLive`. -/
def tbmProtectedFrozenSiblingTrace (fnImplicitWrites : Bool) :
    Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let outerFrame := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 42) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance := { thin_pointer := rootThin, metadata := none }
  let (parentPtr, tbm3, outerFrame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 outerFrame rootPtr (refPtrType .mut u32ItMR) false true nwsrVtableLookup
  let (_, tbm4, _outerFrame2) ←
    TreeBorrowsMemory.retag_ptr tbm3 outerFrame1 rootPtr (refPtrType .not u32ItMR) true true nwsrVtableLookup
  let innerFrame := TreeBorrowsMemory.new_call
  let (_, tbm5, innerFrame1) ←
    TreeBorrowsMemory.retag_ptr tbm4 innerFrame parentPtr (refPtrType .mut u32ItMR) true fnImplicitWrites nwsrVtableLookup
  TreeBorrowsMemory.end_call tbm5 innerFrame1

/-- **Two-sided `#[rustc_no_writable]` vs. standard `&mut` `FnEntry` separation
on `TBM` + `FnEntryBorrowWorld`**:
1. `#[rustc_no_writable]` preserves `.Frozen` siblings across BOTH entry and
   exit (`end_call` emits READ), latches `had_foreign_read = true` on foreign
   reads (blocking local child writes while protected, permitting them after
   `end_call`), rejects parent writes while protected, succeeds against a
   protected `.Frozen` sibling, and preserves `TreeBorrowsMemory.wfLive`.
2. Standard `&mut` (`writableChildWrite`) disables `.Frozen` siblings at entry
   and faults immediately at entry against a protected `.Frozen` sibling.
3. Directly mirrors `rustcNoWritable_preserves_uninit_and_frozen_sibling`,
   `rustcNoWritable_foreignRead_latches_conflicted`,
   `rustcNoWritable_parentWrite_faults_on_protected_child`, and
   `sourceOrder_rustcNoWritable_preserves_all_frozen_nodes`. -/
theorem tbm_rustcNoWritable_vs_writable_full_lifecycle :
    (tbBytesOutcome (tbmNoWritableFullLifecycleTrace.map (·.1)) =
      some (.inl [some 42, some 0, some 0, some 0])) ∧
    (tbBytesOutcome (tbmNoWritableFullLifecycleTrace.map (·.2.1)) =
      some (.inl [some 42, some 0, some 0, some 0])) ∧
    (∃ tbmFinal, tbmNoWritableFullLifecycleTrace.map (·.2.2) = .ok tbmFinal ∧
      TreeBorrowsMemory.wfLive tbmFinal) ∧
    (tbUnitOutcome tbmNoWritableConflictedLocalWriteUbTrace =
      some (.inr "Tree Borrows: local write to protected Reserved reference that had a foreign read")) ∧
    (tbUnitOutcome tbmNoWritableParentWriteUbTrace =
      some (.inr "Tree Borrows: foreign write of protected Reserved reference which had a local read")) ∧
    (tbBytesOutcome tbmWritableDisablesFrozenSiblingUbTrace =
      some (.inr "Tree Borrows: local read of Disabled reference")) ∧
    (∃ tbmProtOk, tbmProtectedFrozenSiblingTrace false = .ok tbmProtOk ∧
      TreeBorrowsMemory.wfLive tbmProtOk) ∧
    (tbUnitOutcome (tbmProtectedFrozenSiblingTrace true) =
      some (.inr "Tree Borrows: foreign write of protected Frozen reference which had a local read")) ∧
    (∀ w w' pTag off len cTag reqInit,
      execFnEntryMutRetagPrunedSourceOrder w pTag off len .rustcNoWritable reqInit = .ok (w', cTag) →
      ∀ n ∈ w.nodes, n.perm = .frozen →
        ∃ n' ∈ w'.nodes, n'.tag = n.tag ∧ n'.perm = .frozen) := by
  refine ⟨by decide +kernel, by decide +kernel,
    tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel,
    tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
    by decide +kernel, ?_⟩
  intro w w' pTag off len cTag reqInit hok n hn hfrz
  rcases prunedSourceOrder_rustcNoWritable_preserves_all_frozen_nodes
    w w' pTag off len cTag reqInit hok n hn hfrz with ⟨n', hn'm, htag, _, hperm, _⟩
  exact ⟨n', hn'm, htag, hperm⟩

/-- `TBM` trace on an **uninitialized** 4-byte allocation: `#[rustc_no_writable]`
succeeds across `retag_ptr` and `end_call`, leaves all 4 data bytes strictly
`.Uninit`, keeps sibling `[1]` `Unprot .Frozen`, and preserves
`TreeBorrowsMemory.wfLive`. -/
def tbmNoWritableUninitTrace : Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let (_, parentPtr, sibPtr, tbm0) ← mkTbmTwoBranchSetup false
  let frame0 := TreeBorrowsMemory.new_call
  let (_, tbm1, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm0 frame0 parentPtr (refPtrType .mut u32ItMR) true false nwsrVtableLookup
  let tbm2 ← TreeBorrowsMemory.end_call tbm1 frame1
  let (_, tbm3) ← TreeBorrowsMemory.load tbm2 sibPtr.thin_pointer ⟨4⟩ ⟨4⟩
  pure tbm3

/-- Project allocation 0's byte list after `tbmNoWritableUninitTrace`. -/
def tbmNoWritableUninitBytes : Option (List (Option UInt8)) :=
  match tbmNoWritableUninitTrace with
  | .ok tbm => tbm.mem.allocations[0]?.map (fun a => projDataBytesTB a.data)
  | .error _ => none

/-- **Uninitialized pointee & read-only allocation preservation**:
`#[rustc_no_writable]` preserves all four `.Uninit` bytes and sibling `.Frozen`
across both `FnEntry` and `end_call` on `TBM` (with `TreeBorrowsMemory.wfLive`),
while `execFnEntryMutRetagPrunedSourceOrder` and
`execFnEntryMutRetagTraversalOrderDirect` reject `writableChildWrite` on
uninitialized (`requireInit = true`) and read-only allocations. -/
theorem tbm_and_world_noWritable_uninit_and_readOnly_separation :
    tbmNoWritableUninitBytes = some [none, none, none, none] ∧
    (∃ tbm', tbmNoWritableUninitTrace = .ok tbm' ∧ TreeBorrowsMemory.wfLive tbm') ∧
    (let wUninit := mkTwoBranchWorld .unique .frozen none false
     (execFnEntryMutRetagPrunedSourceOrder wUninit 1 0 4 .rustcNoWritable true).isOk = true ∧
     execFnEntryMutRetagPrunedSourceOrder wUninit 1 0 4 .writableChildWrite true =
       .error .uninitializedPointeeWrite ∧
     (execFnEntryMutRetagTraversalOrderDirect wUninit 1 0 4 .rustcNoWritable true).isOk = true ∧
     execFnEntryMutRetagTraversalOrderDirect wUninit 1 0 4 .writableChildWrite true =
       .error .uninitializedPointeeWrite) ∧
    (let wRo := { mkTwoBranchWorld .unique .frozen none true with allocReadOnly := true }
     (execFnEntryMutRetagPrunedSourceOrder wRo 1 0 4 .rustcNoWritable false).isOk = true ∧
     execFnEntryMutRetagPrunedSourceOrder wRo 1 0 4 .writableChildWrite false =
       .error .writeToReadOnlyAlloc) :=
  ⟨by decide +kernel,
   tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
   ⟨by decide +kernel, rfl, by decide +kernel, rfl⟩,
   ⟨by decide +kernel, rfl⟩⟩

/-- `TBM` callee-deallocation trace comparing `Box<u32>` (`Protected::Weak`) vs.
`&mut u32` (`Protected::Strong`) under arbitrary `fnImplicitWrites : Bool`. -/
def tbmCalleeDeallocTrace (isBox fnImplicitWrites : Bool) :
    Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Heap ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 5) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance := { thin_pointer := rootThin, metadata := none }
  let ptrTy : Gen.PtrType :=
    if isBox then .Box (intPointeeInfo u32ItMR) else refPtrType .mut u32ItMR
  let (childPtr, tbm3, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr ptrTy true fnImplicitWrites nwsrVtableLookup
  let tbm4 ← TreeBorrowsMemory.deallocate tbm3 childPtr.thin_pointer .Heap ⟨4⟩ ⟨4⟩
  let tbm5 ← TreeBorrowsMemory.end_call tbm4 frame1
  TreeBorrowsMemory.leak_check tbm5
  pure tbm5

/-- **`Box<u32>` weak protector vs. `&mut u32` strong protector under BOTH
`fnImplicitWrites = true` and `fnImplicitWrites = false`**:
- `Box<u32>` (`Protected::Weak`) permits callee deallocation before `end_call`
  under both standard and `#[rustc_no_writable]` policies, passing `end_call`,
  `leak_check`, and `TreeBorrowsMemory.wfLive`.
- `&mut u32` (`Protected::Strong`) rejects callee deallocation with
  `"Tree Borrows: deallocating strongly protected allocation"` under BOTH
  policies (under `#[rustc_no_writable]`, the initial local read latches
  `had_local_read = true`, so `PermissionProt.prevents_deallocation = true`). -/
theorem tbm_box_weak_vs_mut_strong_dealloc_both_policies :
    (∃ tbm1, tbmCalleeDeallocTrace true true = .ok tbm1 ∧ TreeBorrowsMemory.wfLive tbm1) ∧
    (∃ tbm2, tbmCalleeDeallocTrace true false = .ok tbm2 ∧ TreeBorrowsMemory.wfLive tbm2) ∧
    tbUnitOutcome (tbmCalleeDeallocTrace false true) =
      some (.inr "Tree Borrows: deallocating strongly protected allocation") ∧
    tbUnitOutcome (tbmCalleeDeallocTrace false false) =
      some (.inr "Tree Borrows: deallocating strongly protected allocation") :=
  ⟨tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
   tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel,
   by decide +kernel⟩

/-- `TBM` ZST `&mut ()` `FnEntry` trace against a protected `Frozen` sibling:
produces identical `TreeBorrowsMemory` results for `fnImplicitWrites = true` and
`false`, leaving the protected `Frozen` sibling intact. -/
def tbmZstMutFnEntryTrace (fnImplicitWrites : Bool) :
    Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let outerFrame := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 17) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance := { thin_pointer := rootThin, metadata := none }
  let (_, tbm3, _) ←
    TreeBorrowsMemory.retag_ptr tbm2 outerFrame rootPtr (refPtrType .not u32ItMR) true true nwsrVtableLookup
  let innerFrame := TreeBorrowsMemory.new_call
  let (_, tbm4, innerFrame1) ←
    TreeBorrowsMemory.retag_ptr tbm3 innerFrame rootPtr (.Ref .Mutable zstUnitPointeeInfoMR)
      true fnImplicitWrites nwsrVtableLookup
  TreeBorrowsMemory.end_call tbm4 innerFrame1

/-- Concrete ZST `&mut ()` invariance on `TBM` (both policies succeed identically
against a strongly protected `Frozen` sibling and preserve
`TreeBorrowsMemory.wfLive`). -/
theorem tbm_zst_mut_ref_both_policies_and_frozen_sibling :
    (∃ tbm1, tbmZstMutFnEntryTrace true = .ok tbm1 ∧ TreeBorrowsMemory.wfLive tbm1) ∧
    (∃ tbm2, tbmZstMutFnEntryTrace false = .ok tbm2 ∧ TreeBorrowsMemory.wfLive tbm2) ∧
    (tbmZstMutFnEntryTrace true = tbmZstMutFnEntryTrace false) := by
  refine ⟨tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
    tbm_trace_ok_and_wfLive_of_bool (by decide +kernel), ?_⟩
  unfold tbmZstMutFnEntryTrace
  simp only [tbm_retag_zst_implicit_writes_invariance]

/-- Multi-parameter disjoint-range `TBM` setup on an 8-byte `(u32, u32)`
allocation:
- Half 0 (`[0, 4)`): frozen sibling `sib0` (`[0]`) + standard `&mut u32` `p0`
  (`fnImplicitWrites = true`, `[1]`, `Prot .Unique`, disables `sib0`),
- Half 1 (`[4, 8)`): frozen sibling `sib1` (`[2]`) + `#[rustc_no_writable]`
  `&mut u32` `p1` (`fnImplicitWrites = false`, `[3]`, `Prot (.Reserved true false)`,
  preserves `sib1`),
releasing protectors in forward `[p0, p1]` (`reverseOrder = false`) or reversed
`[p1, p0]` (`reverseOrder = true`) order via `TreeBorrowsMemory.end_call`. -/
def tbmDisjointTwoParamExitTrace (reverseOrder : Bool) :
    Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance) ×
      Gen.TreeBorrowsMemory Gen.x86_64 ×
      Gen.Pointer Gen.TreeBorrowsProvenance) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨8⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 11 ++ tbU32Bytes 22) ⟨4⟩
  let half0Ptr : Gen.Pointer Gen.TreeBorrowsProvenance := { thin_pointer := rootThin, metadata := none }
  let half1Thin : Gen.ThinPointer Gen.TreeBorrowsProvenance := { rootThin with addr := rootThin.addr + 4 }
  let half1Ptr : Gen.Pointer Gen.TreeBorrowsProvenance := { thin_pointer := half1Thin, metadata := none }
  let (sib0, tbm3, _) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 half0Ptr (refPtrType .not u32ItMR) false true nwsrVtableLookup
  let (_, tbm4, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm3 frame0 half0Ptr (refPtrType .mut u32ItMR) true true nwsrVtableLookup
  let (sib1, tbm5, _) ←
    TreeBorrowsMemory.retag_ptr tbm4 frame0 half1Ptr (refPtrType .not u32ItMR) false true nwsrVtableLookup
  let (_, tbm6, frame2) ←
    TreeBorrowsMemory.retag_ptr tbm5 frame1 half1Ptr (refPtrType .mut u32ItMR) true false nwsrVtableLookup
  let exitFrame : Gen.TreeBorrowsFrameExtra :=
    if reverseOrder then { protectors := frame2.protectors.reverse } else frame2
  let tbm7 ← TreeBorrowsMemory.end_call tbm6 exitFrame
  let (sib1Bytes, tbm8) ← TreeBorrowsMemory.load tbm7 sib1.thin_pointer ⟨4⟩ ⟨4⟩
  pure (sib1Bytes, tbm8, sib0)

/-- Reading half-0's frozen sibling `sib0` after `tbmDisjointTwoParamExitTrace`
raises UB because half 0 used `writableChildWrite`. -/
def tbmDisjointHalf0SibReadUb (reverseOrder : Bool) :
    Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) := do
  let (_, tbm8, sib0) ← tbmDisjointTwoParamExitTrace reverseOrder
  let (bs, _) ← TreeBorrowsMemory.load tbm8 sib0.thin_pointer ⟨4⟩ ⟨4⟩
  pure bs

/-- Matching 2-parameter disjoint-range `FnEntryBorrowWorld` (`[0, 4)` `.unique`
under protector `10`, `[4, 8)` `.reservedFrz false` under protector `11`, with
disjoint frozen siblings `2` on `[0, 4)` and `4` on `[4, 8)`). -/
def disjointTwoParamWorld : FnEntryBorrowWorld where
  nodes := [
    ⟨0, none, .unique, 0, 8, none, true⟩,
    ⟨1, some 0, .unique, 0, 4, some 10, true⟩,
    ⟨2, some 0, .frozen, 0, 4, none, true⟩,
    ⟨3, some 0, .reservedFrz false, 4, 4, some 11, true⟩,
    ⟨4, some 0, .frozen, 4, 4, none, true⟩
  ]
  activeProtectors := [10, 11]
  nextTag := 5
  nextProtector := 12

/-- **Multi-parameter disjoint-range frame-exit correspondence**:
1. `execFrameExit_miri_eq_miniRust_of_disjointFrame` proves
   `execFrameExitMiniRust disjointTwoParamWorld [(1, 10), (3, 11)] =
    execFrameExitMiri disjointTwoParamWorld [(1, 10), (3, 11)]`, disabling
   half-0's frozen sibling `2` while preserving half-1's frozen sibling `4`!
2. On `TBM`, `TreeBorrowsMemory.end_call` over forward `[p0, p1]` and reversed
   `[p1, p0]` protector orders both preserve `TreeBorrowsMemory.wfLive`, return
   identical half-1 bytes `22` through `sib1`, and disable half-0's `sib0` with
   `"Tree Borrows: local read of Disabled reference"`. -/
theorem disjoint_two_param_frame_exit_miri_miniRust_and_tbm :
    (execFrameExitMiniRust disjointTwoParamWorld [(1, 10), (3, 11)] =
      execFrameExitMiri disjointTwoParamWorld [(1, 10), (3, 11)]) ∧
    (match execFrameExitMiniRust disjointTwoParamWorld [(1, 10), (3, 11)] with
     | .ok w' =>
       (findNode? w'.nodes 2).map (·.perm) = some .disabled ∧
       (findNode? w'.nodes 4).map (·.perm) = some .frozen ∧
       w'.activeProtectors = []
     | .error _ => False) ∧
    (tbBytesOutcome ((tbmDisjointTwoParamExitTrace false).map (·.1)) =
      some (.inl [some 22, some 0, some 0, some 0])) ∧
    (tbBytesOutcome ((tbmDisjointTwoParamExitTrace true).map (·.1)) =
      some (.inl [some 22, some 0, some 0, some 0])) ∧
    (∃ tbmF, (tbmDisjointTwoParamExitTrace false).map (·.2.1) = .ok tbmF ∧
      TreeBorrowsMemory.wfLive tbmF) ∧
    (∃ tbmR, (tbmDisjointTwoParamExitTrace true).map (·.2.1) = .ok tbmR ∧
      TreeBorrowsMemory.wfLive tbmR) ∧
    (tbBytesOutcome (tbmDisjointHalf0SibReadUb false) =
      some (.inr "Tree Borrows: local read of Disabled reference")) ∧
    (tbBytesOutcome (tbmDisjointHalf0SibReadUb true) =
      some (.inr "Tree Borrows: local read of Disabled reference")) := by
  have hagree : execFrameExitMiniRust disjointTwoParamWorld [(1, 10), (3, 11)] =
      execFrameExitMiri disjointTwoParamWorld [(1, 10), (3, 11)] := by
    apply execFrameExit_miri_eq_miniRust_of_disjointFrame
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons (fun _ h => by cases h) List.Pairwise.nil)
      intro e2 he2 n2 hn2 htag2 m hm hprot
      simp only [List.mem_singleton] at he2
      subst he2
      rcases List.mem_cons.mp hn2 with rfl | hn2
      · cases htag2
      · rcases List.mem_cons.mp hn2 with rfl | hn2
        · cases htag2
        · rcases List.mem_cons.mp hn2 with rfl | hn2
          · cases htag2
          · rcases List.mem_cons.mp hn2 with rfl | hn2
            · rcases List.mem_cons.mp hm with rfl | hm
              · cases hprot
              · rcases List.mem_cons.mp hm with rfl | hm
                · rfl
                · rcases List.mem_cons.mp hm with rfl | hm
                  · cases hprot
                  · rcases List.mem_cons.mp hm with rfl | hm
                    · cases hprot
                    · rcases List.mem_cons.mp hm with rfl | hm
                      · cases hprot
                      · cases hm
            · rcases List.mem_cons.mp hn2 with rfl | hn2
              · cases htag2
              · cases hn2
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons (fun _ h => by cases h) List.Pairwise.nil)
      intro e2 he2 n1 hn1 htag1 n2 hn2 htag2
      simp only [List.mem_singleton] at he2
      subst he2
      rcases List.mem_cons.mp hn1 with rfl | hn1
      · cases htag1
      · rcases List.mem_cons.mp hn1 with rfl | hn1
        · rcases List.mem_cons.mp hn2 with rfl | hn2
          · cases htag2
          · rcases List.mem_cons.mp hn2 with rfl | hn2
            · cases htag2
            · rcases List.mem_cons.mp hn2 with rfl | hn2
              · cases htag2
              · rcases List.mem_cons.mp hn2 with rfl | hn2
                · rfl
                · rcases List.mem_cons.mp hn2 with rfl | hn2
                  · cases htag2
                  · cases hn2
        · rcases List.mem_cons.mp hn1 with rfl | hn1
          · cases htag1
          · rcases List.mem_cons.mp hn1 with rfl | hn1
            · cases htag1
            · rcases List.mem_cons.mp hn1 with rfl | hn1
              · cases htag1
              · cases hn1
    · intro e he n hn htag
      rcases List.mem_cons.mp he with rfl | he
      · rcases List.mem_cons.mp hn with rfl | hn
        · cases htag
        · rcases List.mem_cons.mp hn with rfl | hn
          · exact ⟨fun h => (by cases h), fun _ => rfl⟩
          · rcases List.mem_cons.mp hn with rfl | hn
            · cases htag
            · rcases List.mem_cons.mp hn with rfl | hn
              · cases htag
              · rcases List.mem_cons.mp hn with rfl | hn
                · cases htag
                · cases hn
      · simp only [List.mem_singleton] at he
        subst he
        rcases List.mem_cons.mp hn with rfl | hn
        · cases htag
        · rcases List.mem_cons.mp hn with rfl | hn
          · cases htag
          · rcases List.mem_cons.mp hn with rfl | hn
            · cases htag
            · rcases List.mem_cons.mp hn with rfl | hn
              · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
              · rcases List.mem_cons.mp hn with rfl | hn
                · cases htag
                · cases hn
  exact ⟨hagree, ⟨rfl, rfl, rfl⟩,
    by decide +kernel, by decide +kernel,
    tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
    tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
    by decide +kernel, by decide +kernel⟩

/-! ### 1.4 End-to-End `MachTB` (`stepsTB` + `MachTB.wfLive`) & `Trusted` (`stepMirFn`) Witnesses -/

/-- `core::mem::forget`-style MiniRust callee taking `_1 : &mut T` (whose
`PointeeInfo` is `mutPointee`) and executing `Validate(_1, fn_entry = true)`
under `Function.implicit_writes := fnImplicitWrites`, then returning `()`. -/
def forgetStyleCalleeFn (mutPointee : Gen.PointeeInfo) (fnImplicitWrites : Bool) :
    Gen.Function where
  locals := ⟨[
    (localName 0, unitTyMR),
    (localName 1, .Ptr (.Ref .Mutable mutPointee))]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Validate (.Local (localName 1)) true,
      .Assign (.Local (localName 0)) (.Tuple [] unitTyMR)],
      .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := fnImplicitWrites

/-- Caller function creating `_1 = 42u32`, `_2 = &mut _1`, sibling `_3 = &_1`,
calling `fnName 1` (`forgetStyleCalleeFn`) with `_2`, and then reading `*_3`
after `fnName 1` returns (`end_call` + `release_protector`). -/
def forgetStyleCallerFn (mutPointee : Gen.PointeeInfo) : Gen.Function where
  locals := ⟨[
    (localName 0, u32TyMR),
    (localName 1, u32TyMR),
    (localName 2, .Ptr (.Ref .Mutable mutPointee)),
    (localName 3, refTy .not u32ItMR),
    (localName 4, unitTyMR)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .StorageLive (localName 4),
      .Assign (.Local (localName 1)) (.Constant (.Int 42) u32TyMR),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Ref .Mutable mutPointee)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 1)) (refPtrType .not u32ItMR))],
      .Call (.Constant (.FnPointer (fnName 1)) (.Ptr .FnPtr)) .Rust
        [.ByValue (.Load (.Local (localName 2)))] (.Local (localName 4))
        (some (bbName 1)) none,
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 3))) u32TyMR))],
      .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := true

/-- Build initial two-function `MachTB` state for `forgetStyleCallerFn` calling
`forgetStyleCalleeFn mutPointee fnImplicitWrites`. -/
def mkForgetStyleMachTB (mutPointee : Gen.PointeeInfo) (fnImplicitWrites : Bool) : MachTB :=
  let callerFn := forgetStyleCallerFn mutPointee
  let calleeFn := forgetStyleCalleeFn mutPointee fnImplicitWrites
  let prog : Gen.Program := {
    functions := ⟨[(fnName 0, callerFn), (fnName 1, calleeFn)]⟩
    start := fnName 0
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩
  }
  let retAlloc := mkRootAllocTB (List.replicate 4 .Uninit) 128 4 .Stack
  let fnAlloc := mkRootAllocTB [.Uninit] 64 1 .Function
  let loc0Alloc := mkRootAllocTB (List.replicate 4 .Uninit) 512 4 .Stack
  let mainFrame : Gen.StackFrame TBM := {
    func := callerFn
    locals := ⟨[(localName 0, { addr := 512, provenance := some (⟨2⟩, []) })]⟩
    stack_pop_action := .BackToCaller (some (bbName 1)) none
      { addr := 128, provenance := some (⟨0⟩, []) }
    next_block := bbName 0
    next_stmt := 0
    extra := TreeBorrowsMemory.new_call
  }
  { prog := prog
    mem := {
      memory := {
        params := ⟨true⟩
        mem := { allocations := [retAlloc, fnAlloc, loc0Alloc], _phantom := ⟨⟩ }
      }
      accesses := []
    }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [nwsrSentinelFrame, mainFrame], state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[(fnName 1, { addr := 64, provenance := some (⟨1⟩, []) })]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- **End-to-end two-function `MachTB` witness (`core::mem::forget`-style
`#[rustc_no_writable]` vs. standard `&mut u32` `FnEntry`)**:
- With `callee.implicit_writes = false` (`#[rustc_no_writable]`): `stepsTB 13`
  completes cleanly, returning `42u32` via caller's sibling `&u32` after callee
  `Validate(_1, fn_entry = true)` AND `Return` (`end_call` / `release_protector`),
  preserving `MachTB.wfLive`.
- With `callee.implicit_writes = true` (standard `&mut u32`): `Validate(_1, true)`
  performs the implicit child write and disables caller's sibling `&u32`, so
  step 12 raises `Stop.ub "Tree Borrows: local read of Disabled reference"`. -/
theorem machTB_forgetStyle_noWritable_vs_writable_e2e :
    let mNoWr := mkForgetStyleMachTB (intPointeeInfo u32ItMR) false
    let mWr := mkForgetStyleMachTB (intPointeeInfo u32ItMR) true
    machRetSnapshot mNoWr 13 = some (some (true, [some 42, some 0, some 0, some 0]), [1]) ∧
    (∃ m', Interp.stepsTB 13 mNoWr = .ok m' ∧ MachTB.wfLive m') ∧
    machStopOutcome mWr 12 = some (.ub "Tree Borrows: local read of Disabled reference") :=
  ⟨by decide +kernel,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel⟩

/-- **End-to-end `MachTB` `!Unpin` `&mut` skip-retag witness**: even when the
callee has `implicit_writes = true`, a `!Unpin` `&mut` parameter
(`pinnedU32PointeeInfoMR`, `unpin = false`) skips retagging at `Validate(_1, true)`
(adding `0` protectors to the callee frame at step 9), preserves caller's sibling
`&u32`, returns `42u32` at step 13, and preserves `MachTB.wfLive`. -/
theorem machTB_pinned_mut_skips_retag_e2e :
    let mPinned := mkForgetStyleMachTB pinnedU32PointeeInfoMR true
    machTopProtectorCount mPinned 9 = some 0 ∧
    machRetSnapshot mPinned 13 = some (some (true, [some 42, some 0, some 0, some 0]), [1]) ∧
    (∃ m', Interp.stepsTB 13 mPinned = .ok m' ∧ MachTB.wfLive m') :=
  ⟨by decide +kernel,
   by decide +kernel,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel)⟩

/-- Caller function leaving `_1 : u32` **uninitialized**, taking `_2 = &mut _1`
and sibling `_3 = &_1`, calling `forgetStyleCalleeFn`, and then validating `_3`
(`Validate _3 false`, which reborrows `_3` without loading `_1`'s uninit bytes). -/
def forgetStyleUninitCallerFn : Gen.Function where
  locals := ⟨[
    (localName 0, u32TyMR),
    (localName 1, u32TyMR),
    (localName 2, refTy .mut u32ItMR),
    (localName 3, refTy .not u32ItMR),
    (localName 4, unitTyMR)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .StorageLive (localName 4),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32ItMR)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 1)) (refPtrType .not u32ItMR))],
      .Call (.Constant (.FnPointer (fnName 1)) (.Ptr .FnPtr)) .Rust
        [.ByValue (.Load (.Local (localName 2)))] (.Local (localName 4))
        (some (bbName 1)) none,
      .Regular⟩),
    (bbName 1, ⟨[
      .Validate (.Local (localName 3)) false,
      .Assign (.Local (localName 0)) (.Constant (.Int 1) u32TyMR)],
      .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := true

/-- Build initial `MachTB` state for `forgetStyleUninitCallerFn`. -/
def mkForgetStyleUninitMachTB (fnImplicitWrites : Bool) : MachTB :=
  let calleeFn := forgetStyleCalleeFn (intPointeeInfo u32ItMR) fnImplicitWrites
  let prog : Gen.Program := {
    functions := ⟨[(fnName 0, forgetStyleUninitCallerFn), (fnName 1, calleeFn)]⟩
    start := fnName 0
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩
  }
  let retAlloc := mkRootAllocTB (List.replicate 4 .Uninit) 128 4 .Stack
  let fnAlloc := mkRootAllocTB [.Uninit] 64 1 .Function
  let loc0Alloc := mkRootAllocTB (List.replicate 4 .Uninit) 512 4 .Stack
  let mainFrame : Gen.StackFrame TBM := {
    func := forgetStyleUninitCallerFn
    locals := ⟨[(localName 0, { addr := 512, provenance := some (⟨2⟩, []) })]⟩
    stack_pop_action := .BackToCaller (some (bbName 1)) none
      { addr := 128, provenance := some (⟨0⟩, []) }
    next_block := bbName 0
    next_stmt := 0
    extra := TreeBorrowsMemory.new_call
  }
  { prog := prog
    mem := {
      memory := {
        params := ⟨true⟩
        mem := { allocations := [retAlloc, fnAlloc, loc0Alloc], _phantom := ⟨⟩ }
      }
      accesses := []
    }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [nwsrSentinelFrame, mainFrame], state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[(fnName 1, { addr := 64, provenance := some (⟨1⟩, []) })]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- **End-to-end `MachTB` uninitialized-pointee preservation witness**:
under `#[rustc_no_writable]` (`implicit_writes = false`), caller local `_1`
(`allocations[3]`) remains live and strictly uninitialized (`[none, none, none,
none]`) after callee `Validate` + `Return` and caller `Validate(_3, false)`
(step 12), and the program returns `1u32` at step 13 with `MachTB.wfLive`
preserved; under `implicit_writes = true`, caller's `Validate(_3, false)` at
step 11 faults with `"Tree Borrows: local read of Disabled reference"`. -/
theorem machTB_forgetStyle_uninit_pointee_e2e :
    let mNoWr := mkForgetStyleUninitMachTB false
    let mWr := mkForgetStyleUninitMachTB true
    machAllocSnapshot mNoWr 12 3 = some (true, [none, none, none, none]) ∧
    machRetSnapshot mNoWr 13 = some (some (true, [some 1, some 0, some 0, some 0]), [1]) ∧
    (∃ m', Interp.stepsTB 13 mNoWr = .ok m' ∧ MachTB.wfLive m') ∧
    machStopOutcome mWr 11 = some (.ub "Tree Borrows: local read of Disabled reference") :=
  ⟨by decide +kernel,
   by decide +kernel,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel⟩

/-- Callee mode for the `#[rustc_no_writable]` conflict-latch & parent-write
`MachTB` suite (`0` = foreign read + clean return, `1` = foreign read then
conflicted local write UB, `2` = foreign/parent write UB while protected). -/
inductive NoWritableCalleeMode where
  | foreignReadThenReturn
  | foreignReadThenLocalWrite
  | parentWriteWhileProtected
  deriving DecidableEq

/-- `#[rustc_no_writable]` callee receiving `_1 : &mut u32`, sibling `_2 : &u32`,
and raw parent `_3 : *mut u32`. -/
def noWritableConflictCalleeFn (mode : NoWritableCalleeMode) : Gen.Function where
  locals := ⟨[
    (localName 0, u32TyMR),
    (localName 1, refTy .mut u32ItMR),
    (localName 2, refTy .not u32ItMR),
    (localName 3, rawPtrTyMR)]⟩
  args := [localName 1, localName 2, localName 3]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨
      match mode with
      | .foreignReadThenReturn =>
        [.Validate (.Local (localName 1)) true,
         .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) u32TyMR))]
      | .foreignReadThenLocalWrite =>
        [.Validate (.Local (localName 1)) true,
         .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) u32TyMR)),
         .Assign (.Deref (.Load (.Local (localName 1))) u32TyMR) (.Constant (.Int 99) u32TyMR)]
      | .parentWriteWhileProtected =>
        [.Validate (.Local (localName 1)) true,
         .Assign (.Deref (.Load (.Local (localName 3))) u32TyMR) (.Constant (.Int 99) u32TyMR),
         .Assign (.Local (localName 0)) (.Constant (.Int 0) u32TyMR)],
      .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := false

/-- Caller passing `_2 : &mut u32`, `_3 : &u32`, and `_4 : *mut u32` to
`noWritableConflictCalleeFn`, then reading `*_3`, writing `*_2 = 99`, and
returning `*_2` after callee exit. -/
def noWritableConflictCallerFn : Gen.Function where
  locals := ⟨[
    (localName 0, u32TyMR),
    (localName 1, u32TyMR),
    (localName 2, refTy .mut u32ItMR),
    (localName 3, refTy .not u32ItMR),
    (localName 4, rawPtrTyMR),
    (localName 5, u32TyMR)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .StorageLive (localName 4),
      .StorageLive (localName 5),
      .Assign (.Local (localName 1)) (.Constant (.Int 42) u32TyMR),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32ItMR)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 1)) (refPtrType .not u32ItMR)),
      .Assign (.Local (localName 4)) (.AddrOf (.Local (localName 1)) (.Raw .None))],
      .Call (.Constant (.FnPointer (fnName 1)) (.Ptr .FnPtr)) .Rust
        [.ByValue (.Load (.Local (localName 2))),
         .ByValue (.Load (.Local (localName 3))),
         .ByValue (.Load (.Local (localName 4)))]
        (.Local (localName 5)) (some (bbName 1)) none,
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 3))) u32TyMR)),
      .Assign (.Deref (.Load (.Local (localName 2))) u32TyMR) (.Constant (.Int 99) u32TyMR),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) u32TyMR))],
      .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := true

/-- Build initial `MachTB` state for `noWritableConflictCallerFn` +
`noWritableConflictCalleeFn mode`. -/
def mkNoWritableConflictMachTB (mode : NoWritableCalleeMode) : MachTB :=
  let calleeFn := noWritableConflictCalleeFn mode
  let prog : Gen.Program := {
    functions := ⟨[(fnName 0, noWritableConflictCallerFn), (fnName 1, calleeFn)]⟩
    start := fnName 0
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩
  }
  let retAlloc := mkRootAllocTB (List.replicate 4 .Uninit) 128 4 .Stack
  let fnAlloc := mkRootAllocTB [.Uninit] 64 1 .Function
  let loc0Alloc := mkRootAllocTB (List.replicate 4 .Uninit) 512 4 .Stack
  let mainFrame : Gen.StackFrame TBM := {
    func := noWritableConflictCallerFn
    locals := ⟨[(localName 0, { addr := 512, provenance := some (⟨2⟩, []) })]⟩
    stack_pop_action := .BackToCaller (some (bbName 1)) none
      { addr := 128, provenance := some (⟨0⟩, []) }
    next_block := bbName 0
    next_stmt := 0
    extra := TreeBorrowsMemory.new_call
  }
  { prog := prog
    mem := {
      memory := {
        params := ⟨true⟩
        mem := { allocations := [retAlloc, fnAlloc, loc0Alloc], _phantom := ⟨⟩ }
      }
      accesses := []
    }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [nwsrSentinelFrame, mainFrame], state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[(fnName 1, { addr := 64, provenance := some (⟨1⟩, []) })]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- **End-to-end `MachTB` conflict-latch & protector-UB witness under
`#[rustc_no_writable]`**:
1. Foreign read (`*_2`) latches `had_foreign_read = true`, yet returning without
   writing succeeds (`end_call` emits READ, caller still reads `*_3 = 42`, then
   writes `*_2 = 99` after unprotection, returning `99` with `MachTB.wfLive`).
2. Writing through the protected `&mut u32` AFTER the foreign read raises
   `"Tree Borrows: local write to protected Reserved reference that had a foreign read"`.
3. Writing through the raw parent `*mut u32` while `&mut u32` is protected raises
   `"Tree Borrows: foreign write of protected Reserved reference which had a local read"`. -/
theorem machTB_noWritable_conflicted_latch_and_parent_write_e2e :
    let mRet := mkNoWritableConflictMachTB .foreignReadThenReturn
    let mLocWr := mkNoWritableConflictMachTB .foreignReadThenLocalWrite
    let mParWr := mkNoWritableConflictMachTB .parentWriteWhileProtected
    machRetSnapshot mRet 17 = some (some (true, [some 99, some 0, some 0, some 0]), [1]) ∧
    (∃ m', Interp.stepsTB 17 mRet = .ok m' ∧ MachTB.wfLive m') ∧
    machStopOutcome mLocWr 13 =
      some (.ub "Tree Borrows: local write to protected Reserved reference that had a foreign read") ∧
    machStopOutcome mParWr 12 =
      some (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read") :=
  ⟨by decide +kernel,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel,
   by decide +kernel⟩

/-! #### `Trusted` (`stepMirFn` + `evalFnEntryRetagWithParamMap`) Companion Witness -/

/-- Decidable outcome of stepping a `Trusted` MIR body with `FnParamRetagMap`. -/
inductive MirParamRunOutcome where
  | retScalar (bits sizeBytes : Nat)
  | ub
  | other
  deriving DecidableEq, Repr

/-- Single MIR step delegating `StatementKind.retag .fnEntry` (across both root
and active callee frames) to `evalFnEntryRetagWithParamMap` and all other
statements/terminators directly to
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`. -/
def stepMirFnWithParamMap (paramMap : FnParamRetagMap) (body : CapturedMir)
    (s : MachineState) : MirStepNode :=
  let activeBody := s.memory.activeCallee.getD body
  match activeBody.phase with
  | .other _ => stepMirFn body s
  | _ =>
    match Trusted.Sequence.get? activeBody.basicBlocks s.frame.blockIdx with
    | some bb =>
      match Trusted.Sequence.get? bb.statements s.frame.stmtIdx with
      | some ⟨.retag .fnEntry place, span⟩ =>
        evalFnEntryRetagWithParamMap paramMap s place span activeBody.localDecls activeBody.layouts
      | _ => stepMirFn body s
    | none => stepMirFn body s

/-- Under an all-`rustcNoWritable` map, `stepMirFnWithParamMap` equals
`Trusted` `stepMirFn` unconditionally across both root and callee frames! -/
theorem stepMirFnWithParamMap_rustcNoWritable_eq_stepMirFn
    (body : CapturedMir) (s : MachineState) :
    stepMirFnWithParamMap (FnParamRetagMap.empty .rustcNoWritable) body s =
      stepMirFn body s := by
  unfold stepMirFnWithParamMap stepMirFn
  dsimp only
  cases (s.memory.activeCallee.getD body).phase with
  | other _ => rfl
  | runtimePostCleanup | runtimeOptimized =>
    cases hbb : Trusted.Sequence.get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => rfl
    | some bb =>
      simp only
      cases hst : Trusted.Sequence.get? bb.statements s.frame.stmtIdx with
      | none => rfl
      | some stmt =>
        rcases stmt with ⟨kind, span⟩
        cases kind with
        | retag rk place =>
          cases rk with
          | fnEntry =>
            exact evalFnEntryRetagWithParamMap_rustcNoWritable_eq_evalStmt
              (FnParamRetagMap.empty .rustcNoWritable) s place span
              (s.memory.activeCallee.getD body).localDecls (s.memory.activeCallee.getD body).layouts rfl
          | default | twoPhase | raw => rfl
        | nop | coverage | constEvalCounter | backwardIncompatibleDropHint _
        | placeMention _ | storageLive _ | storageDead _ | deinit _
        | intrinsic _ | setDiscriminant _ _ | assign _ _ => rfl

/-- Fuel-bounded execution of `stepMirFnWithParamMap`. -/
def runMirWithParamMap (paramMap : FnParamRetagMap) (body : CapturedMir) :
    Nat → MachineState → MirParamRunOutcome
  | 0, _ => .other
  | fuel + 1, s =>
    match stepMirFnWithParamMap paramMap body s with
    | .tau (.running s') => runMirWithParamMap paramMap body fuel s'
    | .ret (.normal (.scalar sc, _)) => .retScalar sc.bits sc.sizeBytes
    | .vis (.inl (.fail .ub)) _ => .ub
    | _ => .other

/-- Fuel-bounded execution of raw `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`. -/
def runMirDirect (body : CapturedMir) : Nat → MachineState → MirParamRunOutcome
  | 0, _ => .other
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => runMirDirect body fuel s'
    | .ret (.normal (.scalar sc, _)) => .retScalar sc.bits sc.sizeBytes
    | .vis (.inl (.fail .ub)) _ => .ub
    | _ => .other

private def nwsrMirU32Ty : Trusted.Rustc.V2026_06_01.MirAst.Ty := { kind := .uint .u32, layoutIdx := 0 }
private def nwsrMirUnitTy : Trusted.Rustc.V2026_06_01.MirAst.Ty := { kind := .tuple [], layoutIdx := 0 }
private def nwsrMirRefMutU32Ty : Trusted.Rustc.V2026_06_01.MirAst.Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }
private def nwsrMirRefSharedU32Ty : Trusted.Rustc.V2026_06_01.MirAst.Ty := { kind := .ref .not (.uint .u32), layoutIdx := 0 }

private def nwsrMirU32Layout : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def nwsrMirUnitLayout : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def nwsrMirPtrLayout : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def nwsrMirFnAbi1 : Trusted.Rustc.V2026_06_01.Layout.FnAbi :=
  { args := [{ layout := nwsrMirU32Layout, mode := .direct }],
    ret := { layout := nwsrMirU32Layout, mode := .direct }, conv := .rust, canUnwind := false }

private def nwsrMirCalleeAbi : Trusted.Rustc.V2026_06_01.Layout.FnAbi :=
  { args := [{ layout := nwsrMirPtrLayout, mode := .direct }],
    ret := { layout := nwsrMirUnitLayout, mode := .ignore }, conv := .rust, canUnwind := false }

/-- `Trusted` `CapturedMir` callee body mirroring `forgetStyleCalleeFn`:
takes `_1 : &mut u32`, executes `Retag([fn entry], _1)`, sets `_0 = ()`, and
returns (releasing the callee frame's protector via `restoreCallerProtectors`). -/
def forgetLikeCalleeMirBody : CapturedMir where
  defPath := "no_writable_correspondence::forget_like_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := nwsrMirUnitTy, debugName := none },
    { mutability := .mut, ty := nwsrMirRefMutU32Ty, debugName := none }
  ]
  basicBlocks := [{
    statements := ([
      .retag .fnEntry { local_ := 1, projection := [] },
      .assign { local_ := 0, projection := [] } (.aggregate .tuple [])
    ] : List StatementKind).map (fun k => { kind := k, span := "witness" })
    terminator := { kind := .return_, span := "witness" }
    isCleanup := false
  }]
  fnAbi := nwsrMirCalleeAbi
  layouts := emptyLayoutTable
  allocations := []

/-- `Trusted` `CapturedMir` caller body mirroring `forgetStyleCallerFn`:
`_2 = &mut _1; _3 = &_1; forget_like_callee(move _2); _0 = copy (*_3); return`. -/
def forgetLikeMirBody : CapturedMir where
  defPath := "no_writable_correspondence::forget_like_mut_ref"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := nwsrMirU32Ty, debugName := none },
    { mutability := .mut, ty := nwsrMirU32Ty, debugName := none },
    { mutability := .mut, ty := nwsrMirRefMutU32Ty, debugName := none },
    { mutability := .mut, ty := nwsrMirRefSharedU32Ty, debugName := none },
    { mutability := .mut, ty := nwsrMirUnitTy, debugName := none }
  ]
  basicBlocks := [
    {
      statements := ([
        .storageLive 2,
        .storageLive 3,
        .storageLive 4,
        .assign { local_ := 2, projection := [] } (.ref (.mut false) { local_ := 1, projection := [] }),
        .assign { local_ := 3, projection := [] } (.ref .shared { local_ := 1, projection := [] })
      ] : List StatementKind).map (fun k => { kind := k, span := "witness" })
      terminator := {
        kind := .call
          (.constant {
            ty := { kind := .fnDef "no_writable_correspondence::forget_like_callee" [], layoutIdx := 0 },
            val := .zeroSized
          })
          [.move { local_ := 2, projection := [] }]
          { local_ := 4, projection := [] }
          (some 1)
          .continue_
        span := "witness"
      }
      isCleanup := false
    },
    {
      statements := ([
        .assign { local_ := 0, projection := [] } (.use (.copy { local_ := 3, projection := [.deref] }))
      ] : List StatementKind).map (fun k => { kind := k, span := "witness" })
      terminator := { kind := .return_, span := "witness" }
      isCleanup := false
    }
  ]
  fnAbi := nwsrMirFnAbi1
  layouts := emptyLayoutTable
  allocations := []

/-- **End-to-end `Trusted` (`stepMirFn` + `evalFnEntryRetagWithParamMap`)
two-function caller/callee witness matching
`machTB_forgetStyle_noWritable_vs_writable_e2e`**:
- Under `#[rustc_no_writable]` (identical to raw `stepMirFn`), callee
  `Retag([fn entry], _1)` mints `.reservedFrz false`, pushes/pops its callee
  protector cleanly across return, preserves caller sibling `_3 : &u32`, and
  returns `42u32`.
- Under standard `&mut` (`writableChildWrite`), `applyParamFnEntryImplicitWrite`
  invalidates caller sibling `_3 : &u32` so reading `*_3` after return faults
  with `.ub`. -/
theorem trusted_stepMirFn_forgetStyle_noWritable_vs_writable :
    let s0 := initMachineStateWithCallees forgetLikeMirBody [.scalar ⟨42, 4⟩] [forgetLikeCalleeMirBody]
    runMirDirect forgetLikeMirBody 12 s0 = .retScalar 42 4 ∧
    runMirWithParamMap (FnParamRetagMap.empty .rustcNoWritable) forgetLikeMirBody 12 s0 =
      .retScalar 42 4 ∧
    runMirWithParamMap (FnParamRetagMap.empty .writableChildWrite) forgetLikeMirBody 12 s0 = .ub :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## Part 2: Static-Access Temporary Retag Correspondence (`Freeze` vs. `!Freeze` `UnsafeCell` / `AtomicI32` & Zero-Sized `UnsafeCell<()>`, `charon#1620`) -/

/-! ### 2.1 General Symbolic Bridge (`StaticTyDesc` ↔ `cellsToFreezeMask` ↔ `ReborrowSettings.new`) -/

/-- Convert a `StaticTyDesc`'s memory-ordered non-zero `UnsafeCell` intervals to
MiniRust `List (Gen.Offset × LibSpecr.Size)`. -/
def staticCellsMR (desc : StaticTyDesc) : List (Gen.Offset × LibSpecr.Size) :=
  (sortCellsByOffset (collectNonZeroUnsafeCells 0 desc)).map (fun c => (⟨c.1⟩, ⟨c.2⟩))

/-- Convert a `StaticTyDesc` to MiniRust `Gen.PointeeInfo` (with `unsafe_cells`
sorted into memory order and `freeze := desc.isSyntacticFreeze`). -/
def staticPointeeInfoMR (desc : StaticTyDesc) (align : Nat := 1) : Gen.PointeeInfo where
  layout := .Sized ⟨desc.totalByteSize⟩ ⟨align⟩
  inhabited := true
  unsafe_cells := .Sized (staticCellsMR desc)
  freeze := desc.isSyntacticFreeze
  unpin := true

/-- Disjointness, memory-ordering, and bounds predicate for a list of
`UnsafeCell` intervals `(offset, len)` starting at or after `cursor` inside
`[0, total)`. -/
def CellsDisjointInBounds (cursor total : Nat) : List (Nat × Nat) → Prop
  | [] => cursor ≤ total
  | (off, len) :: rest =>
    cursor ≤ off ∧ off + len ≤ total ∧ CellsDisjointInBounds (off + len) total rest

private theorem nwsr_cellsDisjoint_mem_ge (total : Nat) :
    ∀ (k : Nat) (xs : List (Nat × Nat)),
      CellsDisjointInBounds k total xs → ∀ d ∈ xs, k ≤ d.1
  | _, [], _, _, hd => by cases hd
  | k, (yo, yl) :: ys, ⟨hky, _, hys⟩, d, hd => by
    cases hd with
    | head => exact hky
    | tail _ hdy =>
      exact Nat.le_trans hky (Nat.le_trans (Nat.le_add_right yo yl)
        (nwsr_cellsDisjoint_mem_ge total (yo + yl) ys hys d hdy))

/-- Exact byte-level loop invariant for MiniRust's `cellsToFreezeMaskLoop` over
any disjoint, memory-ordered, in-bounds `UnsafeCell` list. -/
theorem cellsToFreezeMaskLoop_disjoint_spec (total : Nat) :
    ∀ (cells : List (Nat × Nat)) (curOff curLen : Nat) (acc : List Bool),
      curOff + curLen ≤ total →
      acc.length = curOff →
      CellsDisjointInBounds (curOff + curLen) total cells →
      ∃ out : List Bool,
        cellsToFreezeMaskLoop (⟨curOff⟩, ⟨curLen⟩)
          (cells.map (fun c => (⟨c.1⟩, ⟨c.2⟩)) ++ [(⟨total⟩, ⟨0⟩)]) acc = .ok out ∧
        out.length = total ∧
        (∀ b < curOff, out[b]? = acc[b]?) ∧
        (∀ b, curOff ≤ b → b < curOff + curLen → out[b]? = some false) ∧
        (∀ b, curOff + curLen ≤ b → b < total →
          (out[b]? = some true ↔ ∀ c ∈ cells, ¬ (c.1 ≤ b ∧ b < c.1 + c.2)) ∧
          (out[b]? = some false ↔ ∃ c ∈ cells, c.1 ≤ b ∧ b < c.1 + c.2)) := by
  intro cells
  induction cells with
  | nil =>
    intro curOff curLen acc hle haccLen _
    have hnn : ¬ ((total : Int) - ((curOff + curLen : Nat) : Int) < 0) := by omega
    have htoNat : ((total : Int) - ((curOff + curLen : Nat) : Int)).toNat =
        total - (curOff + curLen) := by omega
    let acc1 := acc ++ List.replicate curLen false ++ List.replicate (total - (curOff + curLen)) true
    have hstep : cellsToFreezeMaskLoop (⟨curOff⟩, ⟨curLen⟩)
        ([].map (fun c : Nat × Nat => (⟨c.1⟩, ⟨c.2⟩)) ++ [(⟨total⟩, ⟨0⟩)]) acc = .ok acc1 := by
      simp only [List.map_nil, List.nil_append, cellsToFreezeMaskLoop, hnn, ↓reduceIte, htoNat,
        pure, Except.pure, acc1]
    have hlen1 : acc1.length = total := by
      simp only [acc1, List.length_append, List.length_replicate, haccLen]
      omega
    refine ⟨acc1, hstep, hlen1, ?_, ?_, ?_⟩
    · intro b hb
      have h1 : b < (acc ++ List.replicate curLen false).length := by
        simp only [List.length_append, List.length_replicate, haccLen]; omega
      rw [nwsr_getElem?_append_left_of_lt h1, nwsr_getElem?_append_left_of_lt (by omega)]
    · intro b hlo hhi
      have h1 : b < (acc ++ List.replicate curLen false).length := by
        simp only [List.length_append, List.length_replicate, haccLen]; omega
      rw [nwsr_getElem?_append_left_of_lt h1, nwsr_getElem?_append_right_of_le (by omega)]
      exact nwsr_getElem?_replicate_lt (by omega)
    · intro b hlo hhi
      have h1 : (acc ++ List.replicate curLen false).length ≤ b := by
        simp only [List.length_append, List.length_replicate, haccLen]; omega
      have hval : acc1[b]? = some true := by
        rw [nwsr_getElem?_append_right_of_le h1]
        exact nwsr_getElem?_replicate_lt (by
          simp only [List.length_append, List.length_replicate, haccLen]; omega)
      rw [hval]
      refine ⟨⟨fun _ c hc => (by cases hc), fun _ => rfl⟩,
        ⟨fun h => (by cases h), fun ⟨c, hc, _⟩ => (by cases hc)⟩⟩
  | cons hd rest ih =>
    intro curOff curLen acc _ haccLen hdisj
    rcases hd with ⟨off, len⟩
    rcases hdisj with ⟨hcurLeOff, hoffLenLe, hrestDisj⟩
    have hnn : ¬ ((off : Int) - ((curOff + curLen : Nat) : Int) < 0) := by omega
    have htoNat : ((off : Int) - ((curOff + curLen : Nat) : Int)).toNat =
        off - (curOff + curLen) := by omega
    let acc1 := acc ++ List.replicate curLen false ++ List.replicate (off - (curOff + curLen)) true
    have hacc1Len : acc1.length = off := by
      simp only [acc1, List.length_append, List.length_replicate, haccLen]
      omega
    rcases ih off len acc1 hoffLenLe hacc1Len hrestDisj with
      ⟨out, houtEq, houtLen, houtPref, houtCell, houtRest⟩
    have hstep : cellsToFreezeMaskLoop (⟨curOff⟩, ⟨curLen⟩)
        (((off, len) :: rest).map (fun c : Nat × Nat => (⟨c.1⟩, ⟨c.2⟩)) ++ [(⟨total⟩, ⟨0⟩)]) acc =
        .ok out := by
      simp only [List.map_cons, List.cons_append, cellsToFreezeMaskLoop, hnn, ↓reduceIte, htoNat]
      exact houtEq
    refine ⟨out, hstep, houtLen, ?_, ?_, ?_⟩
    · intro b hb
      rw [houtPref b (by omega)]
      have h1 : b < (acc ++ List.replicate curLen false).length := by
        simp only [List.length_append, List.length_replicate, haccLen]; omega
      rw [nwsr_getElem?_append_left_of_lt h1, nwsr_getElem?_append_left_of_lt (by omega)]
    · intro b hlo hhi
      rw [houtPref b (by omega)]
      have h1 : b < (acc ++ List.replicate curLen false).length := by
        simp only [List.length_append, List.length_replicate, haccLen]; omega
      rw [nwsr_getElem?_append_left_of_lt h1, nwsr_getElem?_append_right_of_le (by omega)]
      exact nwsr_getElem?_replicate_lt (by omega)
    · intro b hlo hhi
      by_cases hbo : b < off
      · have hval : out[b]? = some true := by
          rw [houtPref b hbo]
          have h1 : (acc ++ List.replicate curLen false).length ≤ b := by
            simp only [List.length_append, List.length_replicate, haccLen]; omega
          rw [nwsr_getElem?_append_right_of_le h1]
          exact nwsr_getElem?_replicate_lt (by
            simp only [List.length_append, List.length_replicate, haccLen]; omega)
        have hnone : ∀ c ∈ (off, len) :: rest, ¬ (c.1 ≤ b ∧ b < c.1 + c.2) := by
          intro c hc
          cases hc with
          | head => omega
          | tail _ hcr =>
            have hge := nwsr_cellsDisjoint_mem_ge total (off + len) rest hrestDisj c hcr
            omega
        rw [hval]
        refine ⟨⟨fun _ => hnone, fun _ => rfl⟩,
          ⟨fun h => (by cases h), fun ⟨c, hc, hcb⟩ => absurd hcb (hnone c hc)⟩⟩
      · by_cases hbl : b < off + len
        · have hval : out[b]? = some false := houtCell b (by omega) hbl
          rw [hval]
          refine ⟨⟨fun h => (by cases h), fun hall =>
            absurd ⟨by omega, hbl⟩ (hall (off, len) (List.mem_cons_self ..))⟩,
            ⟨fun _ => ⟨(off, len), List.mem_cons_self .., by omega, hbl⟩, fun _ => rfl⟩⟩
        · rcases houtRest b (by omega) hhi with ⟨hT, hF⟩
          refine ⟨?_, ?_⟩
          · rw [hT]
            constructor
            · intro h c hc
              cases hc with
              | head => omega
              | tail _ hcr => exact h c hcr
            · intro h c hc
              exact h c (List.mem_cons_of_mem _ hc)
          · rw [hF]
            constructor
            · rintro ⟨c, hc, hcb⟩
              exact ⟨c, List.mem_cons_of_mem _ hc, hcb⟩
            · rintro ⟨c, hc, hcb⟩
              cases hc with
              | head => omega
              | tail _ hcr => exact ⟨c, hcr, hcb⟩

/-- **General byte-level `cellsToFreezeMask` ↔ `staticFreezeSegments` /
`byteInNonZeroUnsafeCell` equivalence**: for EVERY `desc : StaticTyDesc` (in any
field declaration order, with arbitrary nesting) whose sorted non-zero
`UnsafeCell` intervals are disjoint and in bounds:
1. MiniRust's `cellsToFreezeMask (staticCellsMR desc) ⟨desc.totalByteSize⟩`
   succeeds with a mask of length `desc.totalByteSize`;
2. Byte `b` is frozen (`mask[b]? = some true`) iff `byteInNonZeroUnsafeCell desc b = false`
   iff `b` lies in a `.freeze` segment of `staticFreezeSegments desc`;
3. Byte `b` is unfrozen (`mask[b]? = some false`) iff `byteInNonZeroUnsafeCell desc b = true`. -/
theorem cellsToFreezeMask_staticCellsMR_iff (desc : StaticTyDesc)
    (hdisj : CellsDisjointInBounds 0 desc.totalByteSize
      (sortCellsByOffset (collectNonZeroUnsafeCells 0 desc))) :
    ∃ mask : List Bool,
      cellsToFreezeMask (staticCellsMR desc) ⟨desc.totalByteSize⟩ = .ok mask ∧
      mask.length = desc.totalByteSize ∧
      (∀ b < desc.totalByteSize,
        (mask[b]? = some true ↔ byteInNonZeroUnsafeCell desc b = false) ∧
        (mask[b]? = some false ↔ byteInNonZeroUnsafeCell desc b = true) ∧
        (mask[b]? = some true ↔
          ∃ s ∈ (staticFreezeSegments desc).2, s.kind = .freeze ∧ s.offset ≤ b ∧ b < s.offset + s.len)) := by
  rcases cellsToFreezeMaskLoop_disjoint_spec desc.totalByteSize
      (sortCellsByOffset (collectNonZeroUnsafeCells 0 desc)) 0 0 []
      (Nat.zero_le _) rfl hdisj with
    ⟨mask, hloop, hlen, _, _, hbytes⟩
  have hcm : cellsToFreezeMask (staticCellsMR desc) ⟨desc.totalByteSize⟩ = .ok mask := by
    unfold cellsToFreezeMask staticCellsMR
    rw [hloop]
    simp only [bind, Except.bind, hlen, ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure]
  refine ⟨mask, hcm, hlen, fun b hb => ?_⟩
  rcases hbytes b (Nat.zero_le b) hb with ⟨hT, hF⟩
  have hbyteFalse : byteInNonZeroUnsafeCell desc b = false ↔
      ∀ c ∈ sortCellsByOffset (collectNonZeroUnsafeCells 0 desc), ¬ (c.1 ≤ b ∧ b < c.1 + c.2) := by
    unfold byteInNonZeroUnsafeCell
    rw [List.any_eq_false]
    constructor
    · intro h c hc hcb
      have h0 := h c ((mem_sortCellsByOffset c _).1 hc)
      simp [hcb.1, hcb.2] at h0
    · intro h c hc
      have h0 := h c ((mem_sortCellsByOffset c _).2 hc)
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact h0
  have hbyteTrue : byteInNonZeroUnsafeCell desc b = true ↔
      ∃ c ∈ sortCellsByOffset (collectNonZeroUnsafeCells 0 desc), c.1 ≤ b ∧ b < c.1 + c.2 := by
    unfold byteInNonZeroUnsafeCell
    rw [List.any_eq_true]
    constructor
    · rintro ⟨c, hc, hcond⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨c, (mem_sortCellsByOffset c _).2 hc, hcond⟩
    · rintro ⟨c, hc, hcond⟩
      exact ⟨c, (mem_sortCellsByOffset c _).1 hc, by simp [hcond.1, hcond.2]⟩
  have hTiff : mask[b]? = some true ↔ byteInNonZeroUnsafeCell desc b = false :=
    hT.trans hbyteFalse.symm
  have hFiff : mask[b]? = some false ↔ byteInNonZeroUnsafeCell desc b = true :=
    hF.trans hbyteTrue.symm
  exact ⟨hTiff, hFiff, hTiff.trans (staticFreezeSegments_freeze_byte_iff desc b hb).symm⟩

/-- **General preserved-retag correspondence on MiniRust `ReborrowSettings.new`**:
for EVERY `desc : StaticTyDesc` with disjoint in-bounds `UnsafeCell`s, the
preserved `#1620` shared temporary retag `&S` (`PtrType.Ref .Immutable
(staticPointeeInfoMR desc align)`, `fnEntry = false`) succeeds in MiniRust with
per-byte permissions `s.inside`:
- `s.inside[b]? = some (.Unprot .Frozen)` iff `byteInNonZeroUnsafeCell desc b = false`
  (where `Permission.transition (.Unprot .Frozen) .Write .Local` raises
  `"Tree Borrows: local write of Frozen reference"`),
- `s.inside[b]? = some (.Unprot .Cell)` iff `byteInNonZeroUnsafeCell desc b = true`
  (where `Permission.transition (.Unprot .Cell) .Write .Local = .ok (.Unprot .Cell)`).
- Composed with `static_preserved_write_ok_iff_all_bytes_in_unsafeCell`, whenever
  `staticAllocMutability desc = .mut`, an in-bounds write `[off, off + len)` is
  accepted by `evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag) off len`
  **iff** EVERY byte in `[off, off + len)` receives `.Unprot .Cell` in MiniRust! -/
theorem reborrowSettings_staticPreserved_correspondence
    {Provenance : Type}
    (lookup : Gen.ThinPointer Provenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Provenance)
    (desc : StaticTyDesc) (align : Nat) (params : Gen.TreeBorrowsParams) (fnIw : Bool)
    (hdisj : CellsDisjointInBounds 0 desc.totalByteSize
      (sortCellsByOffset (collectNonZeroUnsafeCells 0 desc))) :
    ∃ s : Gen.ReborrowSettings,
      ReborrowSettings.new lookup ptr (.Ref .Immutable (staticPointeeInfoMR desc align))
        false params fnIw = .ok (some s) ∧
      s.«protected» = .No ∧
      s.inside.length = desc.totalByteSize ∧
      s.outside = (if desc.isSyntacticFreeze then .Unprot .Frozen else .Unprot .Cell) ∧
      (∀ b < desc.totalByteSize,
        (s.inside[b]? = some (.Unprot .Frozen) ↔ byteInNonZeroUnsafeCell desc b = false) ∧
        (s.inside[b]? = some (.Unprot .Cell) ↔ byteInNonZeroUnsafeCell desc b = true)) ∧
      (staticAllocMutability desc = .mut →
        ∀ rootTag tmpTag off len, off + len ≤ desc.totalByteSize →
          (evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag) off len = .ok ↔
            ∀ b, off ≤ b → b < off + len → s.inside[b]? = some (.Unprot .Cell))) := by
  rcases cellsToFreezeMask_staticCellsMR_iff desc hdisj with ⟨mask, hmask, hlen, hbytes⟩
  let toPerm : Bool → Gen.Permission := fun frz => if frz then .Unprot .Frozen else .Unprot .Cell
  let s : Gen.ReborrowSettings := {
    inside := mask.map toPerm
    outside := if desc.isSyntacticFreeze then .Unprot .Frozen else .Unprot .Cell
    «protected» := .No
  }
  have hnew : ReborrowSettings.new lookup ptr (.Ref .Immutable (staticPointeeInfoMR desc align))
      false params fnIw = .ok (some s) := by
    simp only [ReborrowSettings.new, staticPointeeInfoMR, PtrType.safe_pointee,
      Bool.false_eq_true, ↓reduceIte, nwsr_protected_yes_no, Bool.false_and,
      UnsafeCellStrategy.freeze_mask, hmask, bind, Except.bind, nwsr_mapM_perm_shared_no,
      s, toPerm]
    cases desc.isSyntacticFreeze <;> rfl
  have hinsideLen : s.inside.length = desc.totalByteSize := by
    simp only [s, List.length_map, hlen]
  have hbytePerms : ∀ b < desc.totalByteSize,
      (s.inside[b]? = some (.Unprot .Frozen) ↔ byteInNonZeroUnsafeCell desc b = false) ∧
      (s.inside[b]? = some (.Unprot .Cell) ↔ byteInNonZeroUnsafeCell desc b = true) := by
    intro b hb
    rcases hbytes b hb with ⟨hT, hF, _⟩
    have hget : s.inside[b]? = (mask[b]?).map toPerm := by
      simp only [s, List.getElem?_map]
    rw [hget]
    cases hm : mask[b]? with
    | none =>
      have hlt : b < mask.length := by rw [hlen]; exact hb
      have hsome := List.getElem?_eq_getElem hlt
      rw [hm] at hsome
      cases hsome
    | some bit =>
      cases bit with
      | true =>
        simp only [Option.map_some, toPerm, ↓reduceIte]
        have hbf : byteInNonZeroUnsafeCell desc b = false := hT.mp hm
        refine ⟨⟨fun _ => hbf, fun _ => trivial⟩, ⟨fun h => (by cases h), fun h => by rw [hbf] at h; cases h⟩⟩
      | false =>
        simp only [Option.map_some, toPerm, Bool.false_eq_true, ↓reduceIte]
        have hbt : byteInNonZeroUnsafeCell desc b = true := hF.mp hm
        refine ⟨⟨fun h => (by cases h), fun h => by rw [hbt] at h; cases h⟩, ⟨fun _ => hbt, fun _ => trivial⟩⟩
  refine ⟨s, hnew, rfl, hinsideLen, rfl, hbytePerms, ?_⟩
  intro hmut rootTag tmpTag off len hin
  have hokIff := (static_preserved_write_ok_iff_all_bytes_in_unsafeCell desc rootTag tmpTag off len hin hmut).1
  rw [hokIff]
  constructor
  · intro hall b hlo hhi
    exact (hbytePerms b (by omega)).2.mpr (hall b hlo hhi)
  · intro hall b hlo hhi
    exact (hbytePerms b (by omega)).2.mp (hall b hlo hhi)

/-- Pre-`#1620` erased raw address-of (`&raw const S`, `PtrType.Raw .None`)
skips retagging in MiniRust (`ReborrowSettings.new = .ok none`,
`TreeBorrowsMemory.retag_ptr` is the identity), retaining root `.Unprot .Unique`
permissions across all bytes and matching `retagStaticErasedAt`. -/
theorem tbm_staticErased_raw_is_noop
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (frameExtra : Gen.TreeBorrowsFrameExtra)
    (ptr : Gen.Pointer Gen.TreeBorrowsProvenance) (fnEntry fnIw : Bool)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable) :
    ReborrowSettings.new lookup ptr (.Raw .None) fnEntry tbm.params fnIw = .ok none ∧
    TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (.Raw .None) fnEntry fnIw lookup =
      .ok (ptr, tbm, frameExtra) := by
  refine ⟨rfl, ?_⟩
  unfold TreeBorrowsMemory.retag_ptr
  rfl

/-! ### 2.2 All Four Canonical Static Shapes on `TBM`, `MachTB` (`stepsTB` + `MachTB.wfLive`), & `ExtTreeMapAllocAndNoWritable` -/

/-- Shape (a): Pure `Freeze` static (`static S: u32`). -/
def staticShapeADesc : StaticTyDesc := .freezeScalar 4

/-- Shape (b): Pure `!Freeze` static (`static S: AtomicI32` / `UnsafeCell<u32>`). -/
def staticShapeBDesc : StaticTyDesc := .unsafeCell 4

/-- Shape (c) in memory order: non-ZST mixed composite static
`static S: (u8, Padding[3], AtomicI32)`. -/
def staticShapeCDesc : StaticTyDesc :=
  .composite 8 [(0, .freezeScalar 1), (1, .padding 3), (4, .unsafeCell 4)]

/-- Shape (c) in out-of-offset-order `repr(Rust)` field declaration order:
`[(4, AtomicI32), (0, u8), (1, Padding[3])]`. -/
def staticShapeCOutOfOrderDesc : StaticTyDesc :=
  .composite 8 [(4, .unsafeCell 4), (0, .freezeScalar 1), (1, .padding 3)]

/-- Shape (d): Zero-sized `UnsafeCell<()>` composite static
`static S: (u8, UnsafeCell<()>)`. -/
def staticShapeDDesc : StaticTyDesc :=
  .composite 1 [(0, .freezeScalar 1), (1, .unsafeCell 0)]

/-- MiniRust `Gen.Type` for Shape (c) `(u8, Padding[3], AtomicI32)` (`size = 8`, `align = 4`). -/
def staticShapeCTyMR : Gen.Type :=
  .Tuple [(⟨0⟩, u8TyMR), (⟨4⟩, i32TyMR)] ⟨⟨8⟩, ⟨4⟩, none⟩ none

/-- MiniRust `Gen.Type` for Shape (d) `(u8, UnsafeCell<()>)` (`size = 1`, `align = 1`). -/
def staticShapeDTyMR : Gen.Type :=
  .Tuple [(⟨0⟩, u8TyMR), (⟨1⟩, unitTyMR)] ⟨⟨1⟩, ⟨1⟩, none⟩ none

/-- Direct `TBM` static-access trace: allocates a `.Global` allocation of size
`desc.totalByteSize`, initializes it with `initBytes`, optionally performs the
preserved `#1620` shared retag (`preserved = true`) or pre-`#1620` raw erasure
(`preserved = false`), and stores `writeBytes` at `writeOff`. -/
def tbmStaticWriteTrace (desc : StaticTyDesc) (align : Nat)
    (initBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (preserved : Bool) (writeOff : Int)
    (writeBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (writeAlign : Nat) :
    Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Global ⟨desc.totalByteSize⟩ ⟨align⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin initBytes ⟨align⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance := { thin_pointer := rootThin, metadata := none }
  let ptrTy : Gen.PtrType :=
    if preserved then .Ref .Immutable (staticPointeeInfoMR desc align) else .Raw .None
  let (retaggedPtr, tbm3, _) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr ptrTy false true nwsrVtableLookup
  let writeThin : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
    { retaggedPtr.thin_pointer with addr := retaggedPtr.thin_pointer.addr + writeOff }
  TreeBorrowsMemory.store tbm3 writeThin writeBytes ⟨writeAlign⟩

/-- Reusable `MachTB` static-access program exercising `GlobalPointer` into a
`.Global` allocation under either preserved `#1620` (`let _tmp = &S; &raw const *_tmp`)
or pre-`#1620` erased (`&raw const S`), followed by writing `writeVal : writeTy`
at byte offset `writeOff` and returning `1u32`. -/
def mkStaticAccessMachTB (desc : StaticTyDesc) (sTy : Gen.Type) (align : Nat)
    (initBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (preserved : Bool) (writeOff : Int) (writeTy : Gen.Type) (writeVal : Int) : MachTB :=
  let info := staticPointeeInfoMR desc align
  let globalReloc : Gen.Relocation := { name := ⟨⟨0⟩⟩, offset := ⟨0⟩ }
  let globalPtrExpr : Gen.ValueExpr := .Constant (.GlobalPointer globalReloc) rawPtrTyMR
  let ptrTy1 : Gen.PtrType := if preserved then .Ref .Immutable info else .Raw .None
  let local1Ty : Gen.Type := .Ptr ptrTy1
  let rawBaseExpr : Gen.ValueExpr :=
    if preserved then .AddrOf (.Deref (.Load (.Local (localName 1))) sTy) (.Raw .None)
    else .Load (.Local (localName 1))
  let mainFn : Gen.Function := {
    locals := ⟨[
      (localName 0, u32TyMR),
      (localName 1, local1Ty),
      (localName 2, rawPtrTyMR)]⟩
    args := []
    ret := localName 0
    calling_convention := .Rust
    blocks := ⟨[
      (bbName 0, ⟨[
        .StorageLive (localName 1),
        .StorageLive (localName 2),
        .Assign (.Local (localName 1)) (.AddrOf (.Deref globalPtrExpr sTy) ptrTy1),
        .Assign (.Local (localName 2))
          (.BinOp (.PtrOffset true) rawBaseExpr (.Constant (.Int writeOff) isizeTyMR)),
        .Assign (.Deref (.Load (.Local (localName 2))) writeTy) (.Constant (.Int writeVal) writeTy),
        .Assign (.Local (localName 0)) (.Constant (.Int 1) u32TyMR)],
        .Return, .Regular⟩)]⟩
    start := bbName 0
    implicit_writes := true
  }
  let prog : Gen.Program := {
    functions := ⟨[(fnName 0, mainFn)]⟩
    start := fnName 0
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩
  }
  let retAlloc := mkRootAllocTB (List.replicate 4 .Uninit) 128 4 .Stack
  let globalAlloc := mkRootAllocTB initBytes 256 align .Global
  let loc0Alloc := mkRootAllocTB (List.replicate 4 .Uninit) 512 4 .Stack
  let mainFrame : Gen.StackFrame TBM := {
    func := mainFn
    locals := ⟨[(localName 0, { addr := 512, provenance := some (⟨2⟩, []) })]⟩
    stack_pop_action := .BackToCaller (some (bbName 1)) none
      { addr := 128, provenance := some (⟨0⟩, []) }
    next_block := bbName 0
    next_stmt := 0
    extra := TreeBorrowsMemory.new_call
  }
  { prog := prog
    mem := {
      memory := {
        params := ⟨true⟩
        mem := { allocations := [retAlloc, globalAlloc, loc0Alloc], _phantom := ⟨⟩ }
      }
      accesses := []
    }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [nwsrSentinelFrame, mainFrame], state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[(⟨⟨0⟩⟩, { addr := 256, provenance := some (⟨1⟩, []) })]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- **Shape (a) — Pure `Freeze` static (`static S: u32`) correspondence**:
- `isSyntacticFreeze = true`, `staticAllocMutability = .not`,
  `staticFreezeSegments = (4, [⟨0, 4, .freeze⟩])`;
- Preserved `#1620` temporary retag creates `.Unprot .Frozen` across all 4 bytes
  so mutation via `.cast_mut()` faults with
  `"Tree Borrows: local write of Frozen reference"` on BOTH `TBM` and `MachTB`
  (matching `static_pureFreeze_preserved_ub_vs_erased_unsound`);
- Pre-`#1620` erased `&raw const S` retains root `.Unprot .Unique`, so writing
  `99` succeeds on `TBM` and `MachTB` (updating the global allocation to `99`
  with `MachTB.wfLive` preserved; Miri's read-only allocation check catches pure
  `Freeze` statics at the mutability layer via
  `static_pureFreeze_erased_write_caught_by_readOnly_alloc`). -/
theorem staticShapeA_pureFreeze_correspondence :
    let mPres := mkStaticAccessMachTB staticShapeADesc u32TyMR 4 (tbU32Bytes 7) true 0 u32TyMR 99
    let mEras := mkStaticAccessMachTB staticShapeADesc u32TyMR 4 (tbU32Bytes 7) false 0 u32TyMR 99
    staticShapeADesc.isSyntacticFreeze = true ∧
    staticAllocMutability staticShapeADesc = .not ∧
    staticFreezeSegments staticShapeADesc = (4, [⟨0, 4, .freeze⟩]) ∧
    evalRawMutStaticWriteTB (retagStaticPreservedAt staticShapeADesc 1 2) 0 1 = .ub ∧
    evalRawMutStaticWriteTB (retagStaticErasedAt staticShapeADesc 1) 0 1 = .ok ∧
    evalRawMutStaticWriteMiri staticShapeADesc (retagStaticErasedAt staticShapeADesc 1) 0 1 = .readOnlyAlloc ∧
    tbUnitOutcome (tbmStaticWriteTrace staticShapeADesc 4 (tbU32Bytes 7) true 0 (tbU32Bytes 99) 4) =
      some (.inr "Tree Borrows: local write of Frozen reference") ∧
    (∃ tbmE, tbmStaticWriteTrace staticShapeADesc 4 (tbU32Bytes 7) false 0 (tbU32Bytes 99) 4 = .ok tbmE ∧
      TreeBorrowsMemory.wfLive tbmE) ∧
    machStopOutcome mPres 5 = some (.ub "Tree Borrows: local write of Frozen reference") ∧
    machRetSnapshot mEras 7 = some (some (true, [some 1, some 0, some 0, some 0]), [1]) ∧
    machAllocSnapshot mEras 7 1 = some (true, [some 99, some 0, some 0, some 0]) ∧
    (∃ m', Interp.stepsTB 7 mEras = .ok m' ∧ MachTB.wfLive m') :=
  ⟨rfl, rfl, rfl,
   (static_pureFreeze_preserved_ub_vs_erased_unsound 4 1 2 0 (by decide) (by decide)).1,
   (static_pureFreeze_preserved_ub_vs_erased_unsound 4 1 2 0 (by decide) (by decide)).2,
   (static_pureFreeze_erased_write_caught_by_readOnly_alloc 4 1 0).2,
   by decide +kernel,
   tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel,
   by decide +kernel,
   by decide +kernel,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel)⟩

/-- `MachTB` witness for Shape (b) (`static S: AtomicI32` / `UnsafeCell<u32>`)
executing **repeated** interior-mutable writes (`11` then `77`) through the
preserved `#1620` retagged pointer and loading back `77` into `_0`. -/
def staticShapeBRepeatedWriteMachTB : MachTB :=
  let info := staticPointeeInfoMR staticShapeBDesc 4
  let globalReloc : Gen.Relocation := { name := ⟨⟨0⟩⟩, offset := ⟨0⟩ }
  let globalPtrExpr : Gen.ValueExpr := .Constant (.GlobalPointer globalReloc) rawPtrTyMR
  let mainFn : Gen.Function := {
    locals := ⟨[
      (localName 0, u32TyMR),
      (localName 1, .Ptr (.Ref .Immutable info)),
      (localName 2, rawPtrTyMR)]⟩
    args := []
    ret := localName 0
    calling_convention := .Rust
    blocks := ⟨[
      (bbName 0, ⟨[
        .StorageLive (localName 1),
        .StorageLive (localName 2),
        .Assign (.Local (localName 1)) (.AddrOf (.Deref globalPtrExpr u32TyMR) (.Ref .Immutable info)),
        .Assign (.Local (localName 2))
          (.AddrOf (.Deref (.Load (.Local (localName 1))) u32TyMR) (.Raw .None)),
        .Assign (.Deref (.Load (.Local (localName 2))) u32TyMR) (.Constant (.Int 11) u32TyMR),
        .Assign (.Deref (.Load (.Local (localName 2))) u32TyMR) (.Constant (.Int 77) u32TyMR),
        .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) u32TyMR))],
        .Return, .Regular⟩)]⟩
    start := bbName 0
    implicit_writes := true
  }
  let prog : Gen.Program := {
    functions := ⟨[(fnName 0, mainFn)]⟩
    start := fnName 0
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩
  }
  let retAlloc := mkRootAllocTB (List.replicate 4 .Uninit) 128 4 .Stack
  let globalAlloc := mkRootAllocTB (tbU32Bytes 5) 256 4 .Global
  let loc0Alloc := mkRootAllocTB (List.replicate 4 .Uninit) 512 4 .Stack
  let mainFrame : Gen.StackFrame TBM := {
    func := mainFn
    locals := ⟨[(localName 0, { addr := 512, provenance := some (⟨2⟩, []) })]⟩
    stack_pop_action := .BackToCaller (some (bbName 1)) none
      { addr := 128, provenance := some (⟨0⟩, []) }
    next_block := bbName 0
    next_stmt := 0
    extra := TreeBorrowsMemory.new_call
  }
  { prog := prog
    mem := {
      memory := {
        params := ⟨true⟩
        mem := { allocations := [retAlloc, globalAlloc, loc0Alloc], _phantom := ⟨⟩ }
      }
      accesses := []
    }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [nwsrSentinelFrame, mainFrame], state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[(⟨⟨0⟩⟩, { addr := 256, provenance := some (⟨1⟩, []) })]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- `TBM` repeated interior-mutable write trace on Shape (b) (`11` then `77`). -/
def tbmShapeBRepeatedWriteTrace :
    Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance) × Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Global ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 5) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance := { thin_pointer := rootThin, metadata := none }
  let (cellPtr, tbm3, _) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr
      (.Ref .Immutable (staticPointeeInfoMR staticShapeBDesc 4)) false true nwsrVtableLookup
  let tbm4 ← TreeBorrowsMemory.store tbm3 cellPtr.thin_pointer (tbU32Bytes 11) ⟨4⟩
  let tbm5 ← TreeBorrowsMemory.store tbm4 cellPtr.thin_pointer (tbU32Bytes 77) ⟨4⟩
  let (loaded, tbm6) ← TreeBorrowsMemory.load tbm5 cellPtr.thin_pointer ⟨4⟩ ⟨4⟩
  pure (loaded, tbm6)

/-- **Shape (b) — Pure `!Freeze` static (`static S: AtomicI32` /
`UnsafeCell<u32>`) correspondence**:
- `isSyntacticFreeze = false`, `staticAllocMutability = .mut`,
  `staticFreezeSegments = (4, [⟨0, 4, .unsafeCell⟩])`;
- Preserved `#1620` temporary retag creates `.Unprot .Cell` across all 4 bytes,
  permitting repeated interior-mutable writes (`11` then `77`) and readback of
  `77` on BOTH `TBM` and `MachTB` (with `TreeBorrowsMemory.wfLive` and
  `MachTB.wfLive` preserved), matching `static_pureUnsafeCell_preserved_write_ok`. -/
theorem staticShapeB_pureUnsafeCell_correspondence :
    staticShapeBDesc.isSyntacticFreeze = false ∧
    staticAllocMutability staticShapeBDesc = .mut ∧
    staticFreezeSegments staticShapeBDesc = (4, [⟨0, 4, .unsafeCell⟩]) ∧
    evalRawMutStaticWriteMiri staticShapeBDesc (retagStaticPreservedAt staticShapeBDesc 1 2) 0 1 = .ok ∧
    tbBytesOutcome (tbmShapeBRepeatedWriteTrace.map (·.1)) =
      some (.inl [some 77, some 0, some 0, some 0]) ∧
    (∃ tbm', tbmShapeBRepeatedWriteTrace.map (·.2) = .ok tbm' ∧ TreeBorrowsMemory.wfLive tbm') ∧
    machRetSnapshot staticShapeBRepeatedWriteMachTB 8 =
      some (some (true, [some 77, some 0, some 0, some 0]), [1]) ∧
    machAllocSnapshot staticShapeBRepeatedWriteMachTB 8 1 =
      some (true, [some 77, some 0, some 0, some 0]) ∧
    (∃ m', Interp.stepsTB 8 staticShapeBRepeatedWriteMachTB = .ok m' ∧ MachTB.wfLive m') :=
  ⟨rfl, rfl, rfl,
   (static_pureUnsafeCell_preserved_write_ok 4 1 2 0 (by decide) (by decide)).2,
   by decide +kernel,
   tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel,
   by decide +kernel,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel)⟩

/-- Initial 8-byte payload for Shape (c) `(u8=3, Padding[3]=Uninit, AtomicI32=10)`. -/
def staticShapeCInitBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance) :=
  [.Init 3 none, .Uninit, .Uninit, .Uninit, .Init 10 none, .Init 0 none, .Init 0 none, .Init 0 none]

/-- **Shape (c) — Non-ZST mixed composite static (`static S: (u8, Padding[3],
AtomicI32)`, including out-of-offset-order `repr(Rust)` field declarations)
correspondence**:
1. Both memory-order (`staticShapeCDesc`) and out-of-offset-order
   (`staticShapeCOutOfOrderDesc`) declarations have `isSyntacticFreeze = false`,
   `staticAllocMutability = .mut`, identical segments
   `[⟨0, 4, .freeze⟩, ⟨4, 4, .unsafeCell⟩]`, identical `staticCellsMR = [(⟨4⟩, ⟨4⟩)]`,
   and identical `staticPointeeInfoMR`!
2. Preserved `#1620` retag freezes bytes `0` (`u8`) and `1..3` (padding) while
   keeping bytes `4..7` (`AtomicI32`) `.Unprot .Cell`:
   - Mutating `AtomicI32` (offset `4`, value `55`) **SUCCEEDS** on `TBM` and
     `MachTB` (`MachTB.wfLive` preserved, bytes `[4..7]` updated to `55`),
   - Mutating `u8` (offset `0`) and mutating padding (offset `1`) both **FAULT**
     with `"Tree Borrows: local write of Frozen reference"` on `TBM` and `MachTB`!
3. Pre-`#1620` erased `&raw const S` **UNSOUNDLY SUCCEEDS** when mutating `u8`
   (offset `0`) or padding (offset `1`) on `TBM` and `MachTB` (and even Miri's
   allocation-mutability check accepts it because `staticAllocMutability = .mut`),
   matching `static_mixed_miri_separation` and `static_mixed_miri_unsafeCell_write_ok`! -/
theorem staticShapeC_mixedComposite_correspondence :
    let mPresCell :=
      mkStaticAccessMachTB staticShapeCOutOfOrderDesc staticShapeCTyMR 4 staticShapeCInitBytes
        true 4 i32TyMR 55
    let mPresU8 :=
      mkStaticAccessMachTB staticShapeCOutOfOrderDesc staticShapeCTyMR 4 staticShapeCInitBytes
        true 0 u8TyMR 9
    let mPresPad :=
      mkStaticAccessMachTB staticShapeCOutOfOrderDesc staticShapeCTyMR 4 staticShapeCInitBytes
        true 1 u8TyMR 9
    let mErasU8 :=
      mkStaticAccessMachTB staticShapeCOutOfOrderDesc staticShapeCTyMR 4 staticShapeCInitBytes
        false 0 u8TyMR 9
    let mErasPad :=
      mkStaticAccessMachTB staticShapeCOutOfOrderDesc staticShapeCTyMR 4 staticShapeCInitBytes
        false 1 u8TyMR 9
    staticShapeCDesc.isSyntacticFreeze = false ∧
    staticShapeCOutOfOrderDesc.isSyntacticFreeze = false ∧
    staticAllocMutability staticShapeCOutOfOrderDesc = .mut ∧
    staticFreezeSegments staticShapeCOutOfOrderDesc = (8, [⟨0, 4, .freeze⟩, ⟨4, 4, .unsafeCell⟩]) ∧
    staticFreezeSegments staticShapeCDesc = staticFreezeSegments staticShapeCOutOfOrderDesc ∧
    staticPointeeInfoMR staticShapeCDesc 4 = staticPointeeInfoMR staticShapeCOutOfOrderDesc 4 ∧
    evalRawMutStaticWriteMiri staticShapeCOutOfOrderDesc
      (retagStaticPreservedAt staticShapeCOutOfOrderDesc 1 2) 4 4 = .ok ∧
    evalRawMutStaticWriteMiri staticShapeCOutOfOrderDesc
      (retagStaticPreservedAt staticShapeCOutOfOrderDesc 1 2) 0 1 = .ub ∧
    evalRawMutStaticWriteMiri staticShapeCOutOfOrderDesc
      (retagStaticPreservedAt staticShapeCOutOfOrderDesc 1 2) 1 1 = .ub ∧
    evalRawMutStaticWriteMiri staticShapeCOutOfOrderDesc
      (retagStaticErasedAt staticShapeCOutOfOrderDesc 1) 0 1 = .ok ∧
    evalRawMutStaticWriteMiri staticShapeCOutOfOrderDesc
      (retagStaticErasedAt staticShapeCOutOfOrderDesc 1) 1 1 = .ok ∧
    (∃ tbmC, tbmStaticWriteTrace staticShapeCOutOfOrderDesc 4 staticShapeCInitBytes
      true 4 (tbU32Bytes 55) 4 = .ok tbmC ∧ TreeBorrowsMemory.wfLive tbmC) ∧
    tbUnitOutcome (tbmStaticWriteTrace staticShapeCOutOfOrderDesc 4 staticShapeCInitBytes
      true 0 (tbU8Bytes 9) 1) = some (.inr "Tree Borrows: local write of Frozen reference") ∧
    tbUnitOutcome (tbmStaticWriteTrace staticShapeCOutOfOrderDesc 4 staticShapeCInitBytes
      true 1 (tbU8Bytes 9) 1) = some (.inr "Tree Borrows: local write of Frozen reference") ∧
    (∃ tbmEU, tbmStaticWriteTrace staticShapeCOutOfOrderDesc 4 staticShapeCInitBytes
      false 0 (tbU8Bytes 9) 1 = .ok tbmEU ∧ TreeBorrowsMemory.wfLive tbmEU) ∧
    (∃ tbmEP, tbmStaticWriteTrace staticShapeCOutOfOrderDesc 4 staticShapeCInitBytes
      false 1 (tbU8Bytes 9) 1 = .ok tbmEP ∧ TreeBorrowsMemory.wfLive tbmEP) ∧
    machRetSnapshot mPresCell 7 = some (some (true, [some 1, some 0, some 0, some 0]), [1]) ∧
    machAllocSnapshot mPresCell 7 1 =
      some (true, [some 3, none, none, none, some 55, some 0, some 0, some 0]) ∧
    (∃ m', Interp.stepsTB 7 mPresCell = .ok m' ∧ MachTB.wfLive m') ∧
    machStopOutcome mPresU8 5 = some (.ub "Tree Borrows: local write of Frozen reference") ∧
    machStopOutcome mPresPad 5 = some (.ub "Tree Borrows: local write of Frozen reference") ∧
    machAllocSnapshot mErasU8 7 1 =
      some (true, [some 9, none, none, none, some 10, some 0, some 0, some 0]) ∧
    (∃ m', Interp.stepsTB 7 mErasU8 = .ok m' ∧ MachTB.wfLive m') ∧
    machAllocSnapshot mErasPad 7 1 =
      some (true, [some 3, some 9, none, none, some 10, some 0, some 0, some 0]) ∧
    (∃ m', Interp.stepsTB 7 mErasPad = .ok m' ∧ MachTB.wfLive m') :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel, by decide +kernel,
   tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
   tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel, by decide +kernel,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel, by decide +kernel,
   by decide +kernel, machTB_steps_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel, machTB_steps_ok_and_wfLive_of_bool (by decide +kernel)⟩

/-- **Shape (d) — Zero-sized `UnsafeCell<()>` composite static (`static S: (u8,
UnsafeCell<()>)`) correspondence**:
- `FreezeVisitor` emits zero `.unsafeCell` segments (`[⟨0, 1, .freeze⟩]`),
  `staticCellsMR = []`, yet syntactic `isSyntacticFreeze = false` sets
  `staticAllocMutability = .mut` (`intern.rs:225`) and `PointeeInfo.freeze = false`
  (outside permission `.Unprot .Cell`, inside byte `0` `.Unprot .Frozen`);
- Preserved `#1620` temporary retag catches mutation of the `u8` field as
  `"Tree Borrows: local write of Frozen reference"` on BOTH `TBM` and `MachTB`
  (matching `static_zstUnsafeCell_composite_miri_separation`), whereas
  pre-`#1620` erased `&raw const S` unsoundly succeeds on `TBM`, `MachTB`
  (overwriting byte `0` from `3` to `9` with `MachTB.wfLive` preserved), and
  Miri! -/
theorem staticShapeD_zstUnsafeCellComposite_correspondence :
    let mPres := mkStaticAccessMachTB staticShapeDDesc staticShapeDTyMR 1 (tbU8Bytes 3) true 0 u8TyMR 9
    let mEras := mkStaticAccessMachTB staticShapeDDesc staticShapeDTyMR 1 (tbU8Bytes 3) false 0 u8TyMR 9
    staticShapeDDesc.isSyntacticFreeze = false ∧
    staticAllocMutability staticShapeDDesc = .mut ∧
    staticFreezeSegments staticShapeDDesc = (1, [⟨0, 1, .freeze⟩]) ∧
    staticCellsMR staticShapeDDesc = [] ∧
    (staticPointeeInfoMR staticShapeDDesc 1).freeze = false ∧
    evalRawMutStaticWriteMiri staticShapeDDesc (retagStaticPreservedAt staticShapeDDesc 1 2) 0 1 = .ub ∧
    evalRawMutStaticWriteMiri staticShapeDDesc (retagStaticErasedAt staticShapeDDesc 1) 0 1 = .ok ∧
    tbUnitOutcome (tbmStaticWriteTrace staticShapeDDesc 1 (tbU8Bytes 3) true 0 (tbU8Bytes 9) 1) =
      some (.inr "Tree Borrows: local write of Frozen reference") ∧
    (∃ tbmE, tbmStaticWriteTrace staticShapeDDesc 1 (tbU8Bytes 3) false 0 (tbU8Bytes 9) 1 = .ok tbmE ∧
      TreeBorrowsMemory.wfLive tbmE) ∧
    machStopOutcome mPres 5 = some (.ub "Tree Borrows: local write of Frozen reference") ∧
    machRetSnapshot mEras 7 = some (some (true, [some 1, some 0, some 0, some 0]), [1]) ∧
    machAllocSnapshot mEras 7 1 = some (true, [some 9]) ∧
    (∃ m', Interp.stepsTB 7 mEras = .ok m' ∧ MachTB.wfLive m') :=
  ⟨rfl, rfl, rfl, rfl, rfl,
   (static_zstUnsafeCell_composite_miri_separation 1 1 2 0 (by decide) (by decide)).2.2.2.1,
   (static_zstUnsafeCell_composite_miri_separation 1 1 2 0 (by decide) (by decide)).2.2.2.2,
   by decide +kernel,
   tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel,
   by decide +kernel,
   by decide +kernel,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel)⟩

/-! ## Part 3: Closed Non-Vacuity Canaries -/

/-- Closed non-vacuity canary for Part 1A (zero hypotheses): exercises policy
selection, `ReborrowSettings.new`, `permToMiniRust`, `protectorEndAccess`,
`TBM` lifecycle, `MachTB` two-function `#[rustc_no_writable]` vs. standard `&mut`
separation, uninitialized pointee preservation, conflict latch, parent-write UB,
and `Trusted` `stepMirFn` alignment. -/
theorem canary_part1_noWritable_positive_and_negative :
    (permToMiniRust true false (fnEntryRetagPerm .mut (.uint .u32)) =
      some (.Prot (.Reserved false false))) ∧
    ((PermissionProt.unprotect (.Reserved true true)).2 = some .Read) ∧
    ((PermissionProt.unprotect .Unique).2 = some .Write) ∧
    (machRetSnapshot (mkForgetStyleMachTB (intPointeeInfo u32ItMR) false) 13 =
      some (some (true, [some 42, some 0, some 0, some 0]), [1])) ∧
    (machStopOutcome (mkForgetStyleMachTB (intPointeeInfo u32ItMR) true) 12 =
      some (.ub "Tree Borrows: local read of Disabled reference")) ∧
    (machAllocSnapshot (mkForgetStyleUninitMachTB false) 12 3 =
      some (true, [none, none, none, none])) ∧
    (machStopOutcome (mkNoWritableConflictMachTB .foreignReadThenLocalWrite) 13 =
      some (.ub "Tree Borrows: local write to protected Reserved reference that had a foreign read")) ∧
    (machStopOutcome (mkNoWritableConflictMachTB .parentWriteWhileProtected) 12 =
      some (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read")) ∧
    (runMirDirect forgetLikeMirBody 12
        (initMachineStateWithCallees forgetLikeMirBody [.scalar ⟨42, 4⟩] [forgetLikeCalleeMirBody]) =
      .retScalar 42 4) ∧
    (runMirWithParamMap (FnParamRetagMap.empty .writableChildWrite) forgetLikeMirBody 12
        (initMachineStateWithCallees forgetLikeMirBody [.scalar ⟨42, 4⟩] [forgetLikeCalleeMirBody]) = .ub) :=
  ⟨rfl, rfl, rfl,
   machTB_forgetStyle_noWritable_vs_writable_e2e.1,
   machTB_forgetStyle_noWritable_vs_writable_e2e.2.2,
   machTB_forgetStyle_uninit_pointee_e2e.1,
   machTB_noWritable_conflicted_latch_and_parent_write_e2e.2.2.1,
   machTB_noWritable_conflicted_latch_and_parent_write_e2e.2.2.2,
   trusted_stepMirFn_forgetStyle_noWritable_vs_writable.1,
   trusted_stepMirFn_forgetStyle_noWritable_vs_writable.2.2⟩

/-- Closed non-vacuity canary for Part 1B (zero hypotheses): exercises `!Unpin`
skip-retag on `MachTB`, `Box<u32>` weak vs. `&mut u32` strong deallocation under
both policies, ZST `&mut ()` invariance, and multi-parameter disjoint-range
frame exit across `execFrameExitMiniRust`, `execFrameExitMiri`, and `TBM`. -/
theorem canary_part1_pinned_box_zst_and_disjoint_exit :
    (machTopProtectorCount (mkForgetStyleMachTB pinnedU32PointeeInfoMR true) 9 = some 0) ∧
    (machRetSnapshot (mkForgetStyleMachTB pinnedU32PointeeInfoMR true) 13 =
      some (some (true, [some 42, some 0, some 0, some 0]), [1])) ∧
    (tbUnitOutcome (tbmCalleeDeallocTrace true false) = some (.inl ())) ∧
    (tbUnitOutcome (tbmCalleeDeallocTrace false false) =
      some (.inr "Tree Borrows: deallocating strongly protected allocation")) ∧
    (tbmZstMutFnEntryTrace true = tbmZstMutFnEntryTrace false) ∧
    (execFrameExitMiniRust disjointTwoParamWorld [(1, 10), (3, 11)] =
      execFrameExitMiri disjointTwoParamWorld [(1, 10), (3, 11)]) ∧
    (tbBytesOutcome ((tbmDisjointTwoParamExitTrace true).map (·.1)) =
      some (.inl [some 22, some 0, some 0, some 0])) ∧
    (tbBytesOutcome (tbmDisjointHalf0SibReadUb true) =
      some (.inr "Tree Borrows: local read of Disabled reference")) :=
  ⟨machTB_pinned_mut_skips_retag_e2e.1,
   machTB_pinned_mut_skips_retag_e2e.2.1,
   by decide +kernel,
   tbm_box_weak_vs_mut_strong_dealloc_both_policies.2.2.2,
   tbm_zst_mut_ref_both_policies_and_frozen_sibling.2.2,
   disjoint_two_param_frame_exit_miri_miniRust_and_tbm.1,
   disjoint_two_param_frame_exit_miri_miniRust_and_tbm.2.2.2.1,
   disjoint_two_param_frame_exit_miri_miniRust_and_tbm.2.2.2.2.2.2.2⟩

/-- Closed non-vacuity canary for Part 2 (zero hypotheses): instantiates the
general symbolic bridge `reborrowSettings_staticPreserved_correspondence` on
mixed composite Shape (c) AND verifies all four canonical static shapes (a)–(d)
on `MachTB` (both positive `ok` + `MachTB.wfLive` and negative `Frozen` write UB). -/
theorem canary_part2_all_four_static_shapes :
    (∃ s : Gen.ReborrowSettings,
      ReborrowSettings.new nwsrVtableLookup
        { thin_pointer := { addr := 256, provenance := some (⟨1⟩, []) }, metadata := none }
        (.Ref .Immutable (staticPointeeInfoMR staticShapeCOutOfOrderDesc 4)) false ⟨true⟩ true =
        .ok (some s) ∧
      s.inside[0]? = some (.Unprot .Frozen) ∧
      s.inside[1]? = some (.Unprot .Frozen) ∧
      s.inside[4]? = some (.Unprot .Cell) ∧
      s.inside[7]? = some (.Unprot .Cell)) ∧
    (machStopOutcome
      (mkStaticAccessMachTB staticShapeADesc u32TyMR 4 (tbU32Bytes 7) true 0 u32TyMR 99) 5 =
      some (.ub "Tree Borrows: local write of Frozen reference")) ∧
    (machRetSnapshot staticShapeBRepeatedWriteMachTB 8 =
      some (some (true, [some 77, some 0, some 0, some 0]), [1])) ∧
    (machAllocSnapshot
      (mkStaticAccessMachTB staticShapeCOutOfOrderDesc staticShapeCTyMR 4 staticShapeCInitBytes
        true 4 i32TyMR 55) 7 1 =
      some (true, [some 3, none, none, none, some 55, some 0, some 0, some 0])) ∧
    (machStopOutcome
      (mkStaticAccessMachTB staticShapeCOutOfOrderDesc staticShapeCTyMR 4 staticShapeCInitBytes
        true 0 u8TyMR 9) 5 =
      some (.ub "Tree Borrows: local write of Frozen reference")) ∧
    (machStopOutcome
      (mkStaticAccessMachTB staticShapeCOutOfOrderDesc staticShapeCTyMR 4 staticShapeCInitBytes
        true 1 u8TyMR 9) 5 =
      some (.ub "Tree Borrows: local write of Frozen reference")) ∧
    (machStopOutcome
      (mkStaticAccessMachTB staticShapeDDesc staticShapeDTyMR 1 (tbU8Bytes 3) true 0 u8TyMR 9) 5 =
      some (.ub "Tree Borrows: local write of Frozen reference")) ∧
    (machAllocSnapshot
      (mkStaticAccessMachTB staticShapeDDesc staticShapeDTyMR 1 (tbU8Bytes 3) false 0 u8TyMR 9) 7 1 =
      some (true, [some 9])) := by
  have hdisjC : CellsDisjointInBounds 0 staticShapeCOutOfOrderDesc.totalByteSize
      (sortCellsByOffset (collectNonZeroUnsafeCells 0 staticShapeCOutOfOrderDesc)) :=
    ⟨by decide, by decide, by unfold CellsDisjointInBounds; decide⟩
  rcases reborrowSettings_staticPreserved_correspondence nwsrVtableLookup
      { thin_pointer := { addr := 256, provenance := some (⟨1⟩, []) }, metadata := none }
      staticShapeCOutOfOrderDesc 4 ⟨true⟩ true hdisjC with
    ⟨s, hsNew, _, _, _, hbytePerms, _⟩
  refine ⟨⟨s, hsNew,
    (hbytePerms 0 (by decide)).1.mpr rfl,
    (hbytePerms 1 (by decide)).1.mpr rfl,
    (hbytePerms 4 (by decide)).2.mpr rfl,
    (hbytePerms 7 (by decide)).2.mpr rfl⟩,
    staticShapeA_pureFreeze_correspondence.2.2.2.2.2.2.2.2.1,
    staticShapeB_pureUnsafeCell_correspondence.2.2.2.2.2.2.1,
    staticShapeC_mixedComposite_correspondence.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    staticShapeC_mixedComposite_correspondence.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    staticShapeC_mixedComposite_correspondence.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    staticShapeD_zstUnsafeCellComposite_correspondence.2.2.2.2.2.2.2.2.2.1,
    staticShapeD_zstUnsafeCellComposite_correspondence.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-! ## Part 4: Symbolic Whole-Tree Calculus & Relational Simulation (`Node.access`, `TreeBorrowsMemory.load` / `store`) -/

/-! ### 4.1 `Permission.transition` Error Classification & `Node.transitionRange` Byte-Window Calculus -/

private theorem nwsr_bind_ok {α β : Type} {m : Interp α} {f : α → Interp β} {y : β}
    (h : (m >>= f) = .ok y) : ∃ x, m = .ok x ∧ f x = .ok y := by
  cases m with
  | error _ => cases h
  | ok x => exact ⟨x, rfl, h⟩

private theorem nwsr_bind_err {α β : Type} {m : Interp α} {f : α → Interp β} {e : Stop}
    (h : (m >>= f) = .error e) : m = .error e ∨ ∃ x, m = .ok x ∧ f x = .error e := by
  cases m with
  | error _ => cases h; exact .inl rfl
  | ok x => exact .inr ⟨x, rfl, h⟩

/-- Every `Permission.transition` failure is Tree Borrows undefined behavior
(`Stop.ub`), never a spec panic, abort, or unsupported stop. -/
theorem permission_transition_error_is_ub (p : Gen.Permission) (k : Gen.AccessKind)
    (r : Gen.NodeRelation) (e : Stop) (h : Permission.transition p k r = .error e) :
    ∃ msg, e = .ub msg := by
  cases p with
  | Unprot u =>
    cases r <;> cases k <;> cases u <;> cases h <;> exact ⟨_, rfl⟩
  | Prot q =>
    cases r <;> cases k <;> cases q <;>
      first
        | (cases h <;> exact ⟨_, rfl⟩)
        | (rename_i a; cases a <;> cases h <;> exact ⟨_, rfl⟩)
        | (rename_i a b; cases a <;> cases b <;> cases h <;> exact ⟨_, rfl⟩)

private theorem nwsr_listMutateAt_natCast {T O : Type} (xs : List T) (i : Nat) (what : String)
    (f : T → Interp (O × T)) (x : T) (hx : xs[i]? = some x) :
    listMutateAt xs (Int.ofNat i) what f = (f x >>= fun r => pure (r.1, xs.set i r.2)) := by
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hx).1
  have hnn : (0 : Int) ≤ Int.ofNat i := Int.natCast_nonneg i
  have htn : (Int.ofNat i).toNat = i := rfl
  unfold listMutateAt listIndex listSet
  simp only [hnn, htn, hx, hlt, and_self, ↓reduceIte, bind, Except.bind, pure, Except.pure]

private theorem nwsr_transitionRange_succ (nr : Gen.NodeRelation) (k : Gen.AccessKind)
    (off rem : Nat) (perms : List Gen.Permission) (x : Gen.Permission)
    (hx : perms[off]? = some x) :
    Node.transitionRange nr k off (rem + 1) perms =
      (Permission.transition x k nr >>= fun p' =>
        Node.transitionRange nr k (off + 1) rem (perms.set off p')) := by
  rw [Node.transitionRange, nwsr_listMutateAt_natCast _ _ _ _ x hx]
  cases Permission.transition x k nr <;> rfl

private theorem nwsr_transitionRange_succ_none (nr : Gen.NodeRelation) (k : Gen.AccessKind)
    (off rem : Nat) (perms : List Gen.Permission) (hx : perms[off]? = none) :
    ∃ msg, Node.transitionRange nr k off (rem + 1) perms = .error (.specPanic msg) := by
  have hnn : (0 : Int) ≤ Int.ofNat off := Int.natCast_nonneg off
  have htn : (Int.ofNat off).toNat = off := rfl
  rw [Node.transitionRange]
  unfold listMutateAt listIndex
  simp only [hnn, htn, hx, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- **Forward byte-window specification of `Node.transitionRange`**: whenever every
byte of `[off, off + rem)` holds a permission whose `Permission.transition`
succeeds, the range loop succeeds, preserves the list length, leaves every byte
outside the window untouched, and replaces every byte inside the window by its
`Permission.transition` image. -/
theorem transitionRange_ok_of_pointwise (nr : Gen.NodeRelation) (k : Gen.AccessKind) :
    ∀ (rem off : Nat) (perms : List Gen.Permission),
      (∀ b, off ≤ b → b < off + rem →
        ∃ p p', perms[b]? = some p ∧ Permission.transition p k nr = .ok p') →
      ∃ perms', Node.transitionRange nr k off rem perms = .ok perms' ∧
        perms'.length = perms.length ∧
        (∀ b, b < off ∨ off + rem ≤ b → perms'[b]? = perms[b]?) ∧
        (∀ b, off ≤ b → b < off + rem → ∀ p, perms[b]? = some p →
          ∃ p', Permission.transition p k nr = .ok p' ∧ perms'[b]? = some p')
  | 0, off, perms, _ =>
    ⟨perms, by rw [Node.transitionRange]; rfl, rfl, fun _ _ => rfl,
      fun b h1 h2 => absurd h2 (by omega)⟩
  | rem + 1, off, perms, h => by
    obtain ⟨p, p', hp, htr⟩ := h off (Nat.le_refl _) (by omega)
    have hlt : off < perms.length := (List.getElem?_eq_some_iff.mp hp).1
    have hrest : ∀ b, off + 1 ≤ b → b < off + 1 + rem →
        ∃ q q', (perms.set off p')[b]? = some q ∧ Permission.transition q k nr = .ok q' := by
      intro b h1 h2
      obtain ⟨q, q', hq, hqt⟩ := h b (by omega) (by omega)
      exact ⟨q, q', by rw [List.getElem?_set_ne (by omega)]; exact hq, hqt⟩
    obtain ⟨perms', hrun, hlen, hout, hin⟩ :=
      transitionRange_ok_of_pointwise nr k rem (off + 1) (perms.set off p') hrest
    refine ⟨perms', ?_, ?_, ?_, ?_⟩
    · rw [nwsr_transitionRange_succ nr k off rem perms p hp, htr]; exact hrun
    · rw [hlen, List.length_set]
    · intro b hb
      rw [hout b (by omega), List.getElem?_set_ne (by omega)]
    · intro b h1 h2 q hq
      by_cases hb : b = off
      · rw [hb] at hq ⊢
        rw [hp] at hq
        cases hq
        refine ⟨p', htr, ?_⟩
        rw [hout off (by omega), List.getElem?_set_self hlt]
      · have hq' : (perms.set off p')[b]? = some q := by
          rw [List.getElem?_set_ne (by omega)]; exact hq
        exact hin b (by omega) (by omega) q hq'

/-- **Success inversion of `Node.transitionRange`**: a successful range loop
visited an in-bounds permission with a successful `Permission.transition` at
every byte of `[off, off + rem)`. -/
theorem transitionRange_ok_inv (nr : Gen.NodeRelation) (k : Gen.AccessKind) :
    ∀ (rem off : Nat) (perms perms' : List Gen.Permission),
      Node.transitionRange nr k off rem perms = .ok perms' →
      ∀ b, off ≤ b → b < off + rem →
        ∃ p p', perms[b]? = some p ∧ Permission.transition p k nr = .ok p'
  | 0, _, _, _, _, _, _, h2 => absurd h2 (by omega)
  | rem + 1, off, perms, perms', h, b, h1, h2 => by
    cases hx : perms[off]? with
    | none =>
      obtain ⟨msg, herr⟩ := nwsr_transitionRange_succ_none nr k off rem perms hx
      rw [herr] at h
      cases h
    | some x =>
      rw [nwsr_transitionRange_succ nr k off rem perms x hx] at h
      obtain ⟨p', htr, h⟩ := nwsr_bind_ok h
      by_cases hb : b = off
      · exact ⟨x, p', by rw [hb]; exact hx, htr⟩
      · obtain ⟨q, q', hq, hqt⟩ :=
          transitionRange_ok_inv nr k rem (off + 1) _ perms' h b (by omega) (by omega)
        exact ⟨q, q', by rw [List.getElem?_set_ne (by omega)] at hq; exact hq, hqt⟩

/-- **Error provenance of `Node.transitionRange`**: an in-bounds range loop can
only fail because `Permission.transition` failed (with the very same `Stop`) on
the ORIGINAL permission of some byte of `[off, off + rem)`. -/
theorem transitionRange_error_inv (nr : Gen.NodeRelation) (k : Gen.AccessKind) :
    ∀ (rem off : Nat) (perms : List Gen.Permission) (e : Stop),
      off + rem ≤ perms.length →
      Node.transitionRange nr k off rem perms = .error e →
      ∃ b p, off ≤ b ∧ b < off + rem ∧ perms[b]? = some p ∧
        Permission.transition p k nr = .error e
  | 0, _, _, _, _, h => by rw [Node.transitionRange] at h; cases h
  | rem + 1, off, perms, e, hle, h => by
    have hlt : off < perms.length := by omega
    have hx : perms[off]? = some perms[off] := List.getElem?_eq_getElem hlt
    rw [nwsr_transitionRange_succ nr k off rem perms _ hx] at h
    rcases nwsr_bind_err h with htr | ⟨p', _, h⟩
    · exact ⟨off, _, Nat.le_refl _, by omega, hx, htr⟩
    · obtain ⟨b, q, h1, h2, hq, hqt⟩ :=
        transitionRange_error_inv nr k rem (off + 1) _ e (by rw [List.length_set]; omega) h
      exact ⟨b, q, by omega, by omega,
        by rw [List.getElem?_set_ne (by omega)] at hq; exact hq, hqt⟩

/-- Every in-bounds `Node.transitionRange` failure is Tree Borrows UB. -/
theorem transitionRange_error_is_ub (nr : Gen.NodeRelation) (k : Gen.AccessKind)
    (rem off : Nat) (perms : List Gen.Permission) (e : Stop)
    (hle : off + rem ≤ perms.length)
    (h : Node.transitionRange nr k off rem perms = .error e) : ∃ msg, e = .ub msg := by
  obtain ⟨_, p, _, _, _, htr⟩ := transitionRange_error_inv nr k rem off perms e hle h
  exact permission_transition_error_is_ub p k nr e htr

/-- A range loop over a window of transition-stable permissions is the identity. -/
theorem transitionRange_stable_eq (nr : Gen.NodeRelation) (k : Gen.AccessKind)
    (rem off : Nat) (perms : List Gen.Permission)
    (h : ∀ b, off ≤ b → b < off + rem →
      ∃ p, perms[b]? = some p ∧ Permission.transition p k nr = .ok p) :
    Node.transitionRange nr k off rem perms = .ok perms := by
  obtain ⟨perms', hrun, _, hout, hin⟩ := transitionRange_ok_of_pointwise nr k rem off perms
    (fun b h1 h2 => let ⟨p, hp, ht⟩ := h b h1 h2; ⟨p, p, hp, ht⟩)
  have heq : perms' = perms := by
    apply List.ext_getElem?
    intro b
    by_cases h1 : off ≤ b
    · by_cases h2 : b < off + rem
      · obtain ⟨p, hp, ht⟩ := h b h1 h2
        obtain ⟨p', ht', hp'⟩ := hin b h1 h2 p hp
        rw [ht] at ht'
        cases ht'
        rw [hp', hp]
      · exact hout b (Or.inr (by omega))
    · exact hout b (Or.inl (by omega))
  rw [hrun, heq]

/-! ### 4.2 Path-Indexed Whole-Tree Specification of `Node.access` -/

/-- Subtree of a MiniRust borrow tree at a relative `Path` (child indices). -/
def nodeAt : Gen.Node → Gen.Path → Option Gen.Node
  | n, [] => some n
  | n, i :: rest =>
    if 0 ≤ i then
      match n.children[i.toNat]? with
      | some c => nodeAt c rest
      | none => none
    else none

/-- The sub-path handed to child `cid` by `Node::access` / `Node::release_protector`
(`path.and_then(|p| p.split_first())` filtered by `head == child_id`). -/
def subPathAt (path : Option Gen.Path) (cid : Int) : Option Gen.Path :=
  match path with
  | some (h :: tl) => if h == cid then some tl else none
  | _ => none

/-- Whether the node at relative path `q` lies on the access path `path`
(i.e. receives `NodeRelation::Local`). -/
def locOf : Option Gen.Path → Gen.Path → Bool
  | path, [] => path.isSome
  | path, i :: rest => locOf (subPathAt path i) rest

/-- `NodeRelation` received by the node at relative path `q` under access path `path`. -/
def locRel (path : Option Gen.Path) (q : Gen.Path) : Gen.NodeRelation :=
  if locOf path q then .Local else .Foreign

theorem locOf_none (q : Gen.Path) : locOf none q = false := by
  induction q with
  | nil => rfl
  | cons i rest ih => exact ih

/-- A node is `Local` exactly when its path is a prefix of the accessed path. -/
theorem locOf_some_eq_isPrefixOf : ∀ (q t : Gen.Path), locOf (some t) q = q.isPrefixOf t
  | [], t => by cases t <;> rfl
  | _ :: rest, [] => locOf_none rest
  | i :: rest, h :: tl => by
    show locOf (if h == i then some tl else none) rest = (i == h && rest.isPrefixOf tl)
    by_cases hh : h = i
    · subst hh
      have hb : (h == h) = true := decide_eq_true rfl
      rw [hb]
      exact locOf_some_eq_isPrefixOf rest tl
    · have h1 : (h == i) = false := beq_false_of_ne hh
      have h2 : (i == h) = false := beq_false_of_ne (fun e => hh e.symm)
      rw [h1, h2]
      exact locOf_none rest

private theorem nwsr_nodeAt_cons_some (cs : List Gen.Node) (ps : List Gen.Permission)
    (pr : Gen.Protected) (i : Int) (rest : Gen.Path) (c : Gen.Node)
    (hi : 0 ≤ i) (hc : cs[i.toNat]? = some c) :
    nodeAt ⟨cs, ps, pr⟩ (i :: rest) = nodeAt c rest := by
  simp only [nodeAt, hi, ↓reduceIte, hc]

private theorem nwsr_nodeAt_cons_none (cs : List Gen.Node) (ps : List Gen.Permission)
    (pr : Gen.Protected) (i : Int) (rest : Gen.Path)
    (hi : 0 ≤ i) (hc : cs[i.toNat]? = none) :
    nodeAt ⟨cs, ps, pr⟩ (i :: rest) = none := by
  simp only [nodeAt, hi, ↓reduceIte, hc]

private theorem nwsr_nodeAt_cons_neg (cs : List Gen.Node) (ps : List Gen.Permission)
    (pr : Gen.Protected) (i : Int) (rest : Gen.Path) (hi : ¬ 0 ≤ i) :
    nodeAt ⟨cs, ps, pr⟩ (i :: rest) = none := by
  simp only [nodeAt, hi, ↓reduceIte]

private theorem nwsr_access_eq (cs : List Gen.Node) (ps : List Gen.Permission)
    (pr : Gen.Protected) (path : Option Gen.Path) (k : Gen.AccessKind) (off len : Nat) :
    Node.access ⟨cs, ps, pr⟩ path k ⟨off⟩ ⟨len⟩ =
      (Node.transitionRange (locRel path []) k off len ps >>= fun ps' =>
        Node.accessChildren 0 path k ⟨off⟩ ⟨len⟩ cs >>= fun cs' => pure ⟨cs', ps', pr⟩) := by
  rw [Node.access]
  show (Node.transition ⟨cs, ps, pr⟩ (if path.isSome then .Local else .Foreign) k ⟨off⟩ ⟨len⟩ >>= _) = _
  unfold Node.transition locRel locOf
  cases Node.transitionRange (if path.isSome = true then Gen.NodeRelation.Local else .Foreign)
    k off len ps <;> rfl

private theorem nwsr_accessChildren_cons (cid : Int) (path : Option Gen.Path)
    (k : Gen.AccessKind) (o : Gen.Offset) (s : LibSpecr.Size) (c : Gen.Node)
    (rest : List Gen.Node) :
    Node.accessChildren cid path k o s (c :: rest) =
      (Node.access c (subPathAt path cid) k o s >>= fun c' =>
        Node.accessChildren (cid + 1) path k o s rest >>= fun rest' => pure (c' :: rest')) := by
  rcases path with _ | (_ | ⟨h, tl⟩) <;> rw [Node.accessChildren] <;>
    first
      | rfl
      | (intro _ _ hh; cases hh)

/-- Post-state relation of a successful `Node.access`: the tree shape is
unchanged, every node keeps its `protected` flag, and the permissions of the node
at relative path `q` are exactly the `Node.transitionRange` image under its
`locRel path q` relation. -/
def AccessPost (k : Gen.AccessKind) (off len : Nat) (path : Option Gen.Path)
    (n n' : Gen.Node) : Prop :=
  ∀ q,
    (∀ m, nodeAt n q = some m →
      ∃ m', nodeAt n' q = some m' ∧ m'.«protected» = m.«protected» ∧
        Node.transitionRange (locRel path q) k off len m.permissions = .ok m'.permissions) ∧
    (nodeAt n q = none → nodeAt n' q = none)

mutual

/-- **Whole-tree forward specification of `Node.access`**: if the byte-window
transition succeeds at EVERY node of the tree (under its path-determined
`Local` / `Foreign` relation), then `Node.access` succeeds and the result is
described node-by-node by `AccessPost`. -/
theorem node_access_ok_of_pointwise (k : Gen.AccessKind) (off len : Nat) :
    ∀ (n : Gen.Node) (path : Option Gen.Path),
      (∀ q m, nodeAt n q = some m →
        ∃ ps', Node.transitionRange (locRel path q) k off len m.permissions = .ok ps') →
      ∃ n', Node.access n path k ⟨off⟩ ⟨len⟩ = .ok n' ∧ AccessPost k off len path n n'
  | ⟨cs, ps, pr⟩, path, h => by
    obtain ⟨ps', hps⟩ := h [] ⟨cs, ps, pr⟩ rfl
    have hch : ∀ (j : Nat) (c : Gen.Node), cs[j]? = some c → ∀ q m, nodeAt c q = some m →
        ∃ ps', Node.transitionRange (locRel (subPathAt path ((0 : Int) + (j : Int))) q)
          k off len m.permissions = .ok ps' := by
      intro j c hc q m hm
      have hj : (0 : Int) ≤ (j : Int) := Int.natCast_nonneg j
      have hjn : ((j : Int)).toNat = j := rfl
      have hm' : nodeAt ⟨cs, ps, pr⟩ ((j : Int) :: q) = some m := by
        rw [nwsr_nodeAt_cons_some cs ps pr (j : Int) q c hj (by rw [hjn]; exact hc)]
        exact hm
      have := h ((j : Int) :: q) m hm'
      rw [Int.zero_add]
      exact this
    obtain ⟨cs', hcs, hlen, hpost⟩ :=
      node_accessChildren_ok_of_pointwise k off len cs 0 path hch
    refine ⟨⟨cs', ps', pr⟩, ?_, ?_⟩
    · rw [nwsr_access_eq, hps]
      show (Node.accessChildren 0 path k ⟨off⟩ ⟨len⟩ cs >>= _) = _
      rw [hcs]
      rfl
    · intro q
      cases q with
      | nil =>
        refine ⟨fun m hm => ?_, fun hn => by cases hn⟩
        cases hm
        exact ⟨⟨cs', ps', pr⟩, rfl, rfl, hps⟩
      | cons i rest =>
        by_cases hi : 0 ≤ i
        · have hie : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg hi
          cases hc : cs[i.toNat]? with
          | none =>
            have hc' : cs'[i.toNat]? = none := by
              rw [List.getElem?_eq_none_iff] at hc ⊢
              omega
            refine ⟨fun m hm => ?_, fun _ => ?_⟩
            · rw [nwsr_nodeAt_cons_none cs ps pr i rest hi hc] at hm
              cases hm
            · exact nwsr_nodeAt_cons_none cs' ps' pr i rest hi hc'
          | some c =>
            obtain ⟨c', hc', hp⟩ := hpost i.toNat c hc
            rw [Int.zero_add, hie] at hp
            have hq := hp rest
            refine ⟨fun m hm => ?_, fun hn => ?_⟩
            · rw [nwsr_nodeAt_cons_some cs ps pr i rest c hi hc] at hm
              obtain ⟨m', hm', hprot, htr⟩ := hq.1 m hm
              exact ⟨m', by rw [nwsr_nodeAt_cons_some cs' ps' pr i rest c' hi hc']; exact hm',
                hprot, htr⟩
            · rw [nwsr_nodeAt_cons_some cs ps pr i rest c hi hc] at hn
              rw [nwsr_nodeAt_cons_some cs' ps' pr i rest c' hi hc']
              exact hq.2 hn
        · refine ⟨fun m hm => ?_, fun _ => ?_⟩
          · rw [nwsr_nodeAt_cons_neg cs ps pr i rest hi] at hm
            cases hm
          · exact nwsr_nodeAt_cons_neg cs' ps' pr i rest hi

/-- Child-list companion of `node_access_ok_of_pointwise`. -/
theorem node_accessChildren_ok_of_pointwise (k : Gen.AccessKind) (off len : Nat) :
    ∀ (cs : List Gen.Node) (cid : Int) (path : Option Gen.Path),
      (∀ (j : Nat) (c : Gen.Node), cs[j]? = some c → ∀ q m, nodeAt c q = some m →
        ∃ ps', Node.transitionRange (locRel (subPathAt path (cid + (j : Int))) q)
          k off len m.permissions = .ok ps') →
      ∃ cs', Node.accessChildren cid path k ⟨off⟩ ⟨len⟩ cs = .ok cs' ∧
        cs'.length = cs.length ∧
        ∀ (j : Nat) (c : Gen.Node), cs[j]? = some c →
          ∃ c', cs'[j]? = some c' ∧
            AccessPost k off len (subPathAt path (cid + (j : Int))) c c'
  | [], cid, path, _ =>
    ⟨[], by rw [Node.accessChildren]; rfl, rfl, fun j c hc => by simp at hc⟩
  | c :: rest, cid, path, h => by
    have e0 : cid + ((0 : Nat) : Int) = cid := by omega
    obtain ⟨c', hc', hpost⟩ := node_access_ok_of_pointwise k off len c (subPathAt path cid) (by
      intro q m hm
      have := h 0 c rfl q m hm
      rw [e0] at this
      exact this)
    obtain ⟨rest', hrest, hlen, hpostR⟩ :=
      node_accessChildren_ok_of_pointwise k off len rest (cid + 1) path (by
        intro j d hd q m hm
        have := h (j + 1) d (by rw [List.getElem?_cons_succ]; exact hd) q m hm
        have e1 : cid + ((j + 1 : Nat) : Int) = cid + 1 + (j : Int) := by omega
        rw [e1] at this
        exact this)
    refine ⟨c' :: rest', ?_, by rw [List.length_cons, List.length_cons, hlen], ?_⟩
    · rw [nwsr_accessChildren_cons, hc']
      show (Node.accessChildren (cid + 1) path k ⟨off⟩ ⟨len⟩ rest >>= _) = _
      rw [hrest]
      rfl
    · intro j d hd
      cases j with
      | zero =>
        rw [List.getElem?_cons_zero] at hd
        cases hd
        exact ⟨c', rfl, by rw [e0]; exact hpost⟩
      | succ j =>
        rw [List.getElem?_cons_succ] at hd
        obtain ⟨d', hd', hp⟩ := hpostR j d hd
        have e1 : cid + ((j + 1 : Nat) : Int) = cid + 1 + (j : Int) := by omega
        exact ⟨d', by rw [List.getElem?_cons_succ]; exact hd', by rw [e1]; exact hp⟩

end

mutual

/-- **Whole-tree success inversion of `Node.access`**: a successful access
performed a successful byte-window transition at EVERY node of the tree. -/
theorem node_access_ok_inv (k : Gen.AccessKind) (off len : Nat) :
    ∀ (n n' : Gen.Node) (path : Option Gen.Path),
      Node.access n path k ⟨off⟩ ⟨len⟩ = .ok n' →
      ∀ q m, nodeAt n q = some m →
        ∃ ps', Node.transitionRange (locRel path q) k off len m.permissions = .ok ps'
  | ⟨cs, ps, pr⟩, n', path, h, q, m, hm => by
    rw [nwsr_access_eq] at h
    obtain ⟨ps', hps, h⟩ := nwsr_bind_ok h
    obtain ⟨cs', hcs, _⟩ := nwsr_bind_ok h
    cases q with
    | nil =>
      cases hm
      exact ⟨ps', hps⟩
    | cons i rest =>
      by_cases hi : 0 ≤ i
      · cases hc : cs[i.toNat]? with
        | none =>
          rw [nwsr_nodeAt_cons_none cs ps pr i rest hi hc] at hm
          cases hm
        | some c =>
          rw [nwsr_nodeAt_cons_some cs ps pr i rest c hi hc] at hm
          have := node_accessChildren_ok_inv k off len cs cs' 0 path hcs i.toNat c hc rest m hm
          rw [Int.zero_add, Int.toNat_of_nonneg hi] at this
          exact this
      · rw [nwsr_nodeAt_cons_neg cs ps pr i rest hi] at hm
        cases hm

/-- Child-list companion of `node_access_ok_inv`. -/
theorem node_accessChildren_ok_inv (k : Gen.AccessKind) (off len : Nat) :
    ∀ (cs cs' : List Gen.Node) (cid : Int) (path : Option Gen.Path),
      Node.accessChildren cid path k ⟨off⟩ ⟨len⟩ cs = .ok cs' →
      ∀ (j : Nat) (c : Gen.Node), cs[j]? = some c → ∀ q m, nodeAt c q = some m →
        ∃ ps', Node.transitionRange (locRel (subPathAt path (cid + (j : Int))) q)
          k off len m.permissions = .ok ps'
  | [], _, _, _, _, j, c, hc, _, _, _ => by simp at hc
  | c0 :: rest, cs', cid, path, h, j, c, hc, q, m, hm => by
    rw [nwsr_accessChildren_cons] at h
    obtain ⟨c0', h0, h⟩ := nwsr_bind_ok h
    obtain ⟨rest', hr, _⟩ := nwsr_bind_ok h
    cases j with
    | zero =>
      rw [List.getElem?_cons_zero] at hc
      cases hc
      have := node_access_ok_inv k off len c0 c0' (subPathAt path cid) h0 q m hm
      have e0 : cid + ((0 : Nat) : Int) = cid := by omega
      rw [e0]
      exact this
    | succ j =>
      rw [List.getElem?_cons_succ] at hc
      have := node_accessChildren_ok_inv k off len rest rest' (cid + 1) path hr j c hc q m hm
      have e1 : cid + ((j + 1 : Nat) : Int) = cid + 1 + (j : Int) := by omega
      rw [e1]
      exact this

end

mutual

/-- **Whole-tree error provenance of `Node.access`**: a failing access failed
with the very same `Stop` in the byte-window transition of some node of the tree. -/
theorem node_access_error_inv (k : Gen.AccessKind) (off len : Nat) :
    ∀ (n : Gen.Node) (path : Option Gen.Path) (e : Stop),
      Node.access n path k ⟨off⟩ ⟨len⟩ = .error e →
      ∃ q m, nodeAt n q = some m ∧
        Node.transitionRange (locRel path q) k off len m.permissions = .error e
  | ⟨cs, ps, pr⟩, path, e, h => by
    rw [nwsr_access_eq] at h
    rcases nwsr_bind_err h with hps | ⟨ps', _, h⟩
    · exact ⟨[], ⟨cs, ps, pr⟩, rfl, hps⟩
    · rcases nwsr_bind_err h with hcs | ⟨cs', _, h⟩
      · obtain ⟨j, c, hc, q, m, hm, herr⟩ :=
          node_accessChildren_error_inv k off len cs 0 path e hcs
        have hj : (0 : Int) ≤ (j : Int) := Int.natCast_nonneg j
        have hjn : ((j : Int)).toNat = j := rfl
        refine ⟨(j : Int) :: q, m, ?_, ?_⟩
        · rw [nwsr_nodeAt_cons_some cs ps pr (j : Int) q c hj (by rw [hjn]; exact hc)]
          exact hm
        · rw [Int.zero_add] at herr
          exact herr
      · cases h

/-- Child-list companion of `node_access_error_inv`. -/
theorem node_accessChildren_error_inv (k : Gen.AccessKind) (off len : Nat) :
    ∀ (cs : List Gen.Node) (cid : Int) (path : Option Gen.Path) (e : Stop),
      Node.accessChildren cid path k ⟨off⟩ ⟨len⟩ cs = .error e →
      ∃ (j : Nat) (c : Gen.Node), cs[j]? = some c ∧ ∃ q m, nodeAt c q = some m ∧
        Node.transitionRange (locRel (subPathAt path (cid + (j : Int))) q)
          k off len m.permissions = .error e
  | [], _, _, _, h => by rw [Node.accessChildren] at h; cases h
  | c0 :: rest, cid, path, e, h => by
    rw [nwsr_accessChildren_cons] at h
    rcases nwsr_bind_err h with h0 | ⟨c0', _, h⟩
    · obtain ⟨q, m, hm, herr⟩ := node_access_error_inv k off len c0 (subPathAt path cid) e h0
      have e0 : cid + ((0 : Nat) : Int) = cid := by omega
      exact ⟨0, c0, rfl, q, m, hm, by rw [e0]; exact herr⟩
    · rcases nwsr_bind_err h with hr | ⟨_, _, h⟩
      · obtain ⟨j, c, hc, q, m, hm, herr⟩ :=
          node_accessChildren_error_inv k off len rest (cid + 1) path e hr
        have e1 : cid + ((j + 1 : Nat) : Int) = cid + 1 + (j : Int) := by omega
        exact ⟨j + 1, c, by rw [List.getElem?_cons_succ]; exact hc, q, m, hm,
          by rw [e1]; exact herr⟩
      · cases h

end

/-! ### 4.3 Whole-Tree Relational Simulation: `execWorldRangeRead` / `execWorldRangeWrite` ↔ `Node.access` -/

/-- Byte-window relation between an Anneal coarse-range `TreeTagNode` and a
MiniRust per-byte borrow-tree `Gen.Node`: the protector flags agree, and every
byte of the window `[off, off + len)` carries the `permToMiniRust` image of the
Anneal node's `(isProtected, accessed, perm)` state. -/
def NodeWindowRel (ap : List Nat) (off len : Nat) (n : TreeTagNode) (m : Gen.Node) : Prop :=
  Protected.yes m.«protected» = n.isProtected ap ∧
  ∃ p, permToMiniRust (n.isProtected ap) n.accessed n.perm = some p ∧
    ∀ b, off ≤ b → b < off + len → m.permissions[b]? = some p

/-- **Whole-tree relational invariant** between an Anneal `FnEntryBorrowWorld`
(flat tag-indexed node list with parent links) and a MiniRust borrow tree `t`
(nested children, per-byte permissions) on the byte window `[off, off + len)`,
through a tag-to-path embedding `emb`:
- `nodes`: every Anneal node is represented by the MiniRust node at `emb tag`;
- `surj`: every MiniRust node represents some Anneal node (no hidden nodes);
- `overlap`: every Anneal node's coarse range overlaps the window (so the
  coarse-range step is exact on the window);
- `noProtIM` / `protUniqAcc`: the reachable MiniRust envelope (`PermissionProt`
  has no `ReservedIm`; a protected `Unique` has been locally accessed). -/
structure TreeSimInv (off len : Nat) (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld)
    (t : Gen.Node) : Prop where
  nodes : ∀ n ∈ w.nodes, ∃ m, nodeAt t (emb n.tag) = some m ∧
    NodeWindowRel w.activeProtectors off len n m
  surj : ∀ q m, nodeAt t q = some m → ∃ n ∈ w.nodes, emb n.tag = q
  overlap : ∀ n ∈ w.nodes, rangesOverlap off len n.rangeOffset n.rangeLen = true
  noProtIM : ∀ n ∈ w.nodes, n.isProtected w.activeProtectors = true → n.perm ≠ .reservedIM
  protUniqAcc : ∀ n ∈ w.nodes, n.isProtected w.activeProtectors = true →
    n.perm = .unique → n.accessed = true

private theorem nwsr_stepRead_meta (ap : List Nat) (isLocal : Bool) (off len : Nat)
    (n n' : TreeTagNode) (h : stepNodeOnRangeRead ap isLocal off len n = .ok n') :
    n'.tag = n.tag ∧ n'.protector = n.protector ∧ n'.rangeOffset = n.rangeOffset ∧
    n'.rangeLen = n.rangeLen ∧ (n'.perm = .reservedIM → n.perm = .reservedIM) ∧
    ((n.isProtected ap = true → n.perm = .unique → n.accessed = true) →
      n'.isProtected ap = true → n'.perm = .unique → n'.accessed = true) := by
  unfold stepNodeOnRangeRead at h
  repeat' split at h
  all_goals
    cases h <;>
      exact ⟨rfl, rfl, rfl, rfl,
        by first | exact id | (intro hh; cases hh),
        by first
          | exact (fun _ _ _ => rfl)
          | exact (fun henv => henv)
          | (intro _ _ hu; cases hu)⟩

private theorem nwsr_stepWrite_meta (ap : List Nat) (isLocal : Bool) (off len : Nat)
    (n n' : TreeTagNode) (h : stepNodeOnRangeWrite ap isLocal off len n = .ok n') :
    n'.tag = n.tag ∧ n'.protector = n.protector ∧ n'.rangeOffset = n.rangeOffset ∧
    n'.rangeLen = n.rangeLen ∧ (n'.perm = .reservedIM → n.perm = .reservedIM) ∧
    ((n.isProtected ap = true → n.perm = .unique → n.accessed = true) →
      n'.isProtected ap = true → n'.perm = .unique → n'.accessed = true) := by
  unfold stepNodeOnRangeWrite at h
  repeat' split at h
  all_goals
    cases h <;>
      exact ⟨rfl, rfl, rfl, rfl,
        by first | exact id | (intro hh; cases hh),
        by first
          | exact (fun _ _ _ => rfl)
          | exact (fun henv => henv)
          | (intro _ _ hu; cases hu)⟩

/-- Per-node lockstep interface between an Anneal node step and MiniRust
`Permission.transition` used by the whole-tree simulation. -/
private def NodeStepSim (ap : List Nat) (k : Gen.AccessKind)
    (step : Bool → TreeTagNode → Except RetagStepErr TreeTagNode) (n : TreeTagNode) : Prop :=
  ∀ isLocal, ∃ p,
    permToMiniRust (n.isProtected ap) n.accessed n.perm = some p ∧
    (∀ n', step isLocal n = .ok n' →
      n'.tag = n.tag ∧ n'.isProtected ap = n.isProtected ap ∧
      n'.rangeOffset = n.rangeOffset ∧ n'.rangeLen = n.rangeLen ∧
      (n'.isProtected ap = true → n'.perm ≠ .reservedIM) ∧
      (n'.isProtected ap = true → n'.perm = .unique → n'.accessed = true) ∧
      ∃ p', Permission.transition p k (nodeRelToMiniRust isLocal) = .ok p' ∧
        permToMiniRust (n.isProtected ap) n'.accessed n'.perm = some p') ∧
    (∀ e, step isLocal n = .error e →
      ∃ msg, Permission.transition p k (nodeRelToMiniRust isLocal) = .error (.ub msg))

private theorem nwsr_stepRead_sim (ap : List Nat) (off len : Nat) (n : TreeTagNode)
    (hov : rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hIM : n.isProtected ap = true → n.perm ≠ .reservedIM)
    (hUA : n.isProtected ap = true → n.perm = .unique → n.accessed = true) :
    NodeStepSim ap .Read (fun isLoc m => stepNodeOnRangeRead ap isLoc off len m) n := by
  intro isLocal
  obtain ⟨p, hp, hok, herr⟩ :=
    stepNodeOnRangeRead_simulates_permission_transition ap isLocal off len n hov hIM hUA
  refine ⟨p, hp, fun n' hn' => ?_, herr⟩
  obtain ⟨htag, hprot, hro, hrl, hIM', hUA'⟩ := nwsr_stepRead_meta ap isLocal off len n n' hn'
  have hpe : n'.isProtected ap = n.isProtected ap := by
    unfold TreeTagNode.isProtected
    rw [hprot]
  exact ⟨htag, hpe, hro, hrl, fun hp' him => hIM (hpe ▸ hp') (hIM' him), hUA' hUA, hok n' hn'⟩

private theorem nwsr_stepWrite_sim (ap : List Nat) (off len : Nat) (n : TreeTagNode)
    (hov : rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hIM : n.isProtected ap = true → n.perm ≠ .reservedIM)
    (hUA : n.isProtected ap = true → n.perm = .unique → n.accessed = true) :
    NodeStepSim ap .Write (fun isLoc m => stepNodeOnRangeWrite ap isLoc off len m) n := by
  intro isLocal
  obtain ⟨p, hp, hok, herr⟩ :=
    stepNodeOnRangeWrite_simulates_permission_transition ap isLocal off len n hov hIM hUA
  refine ⟨p, hp, fun n' hn' => ?_, herr⟩
  obtain ⟨htag, hprot, hro, hrl, hIM', hUA'⟩ := nwsr_stepWrite_meta ap isLocal off len n n' hn'
  have hpe : n'.isProtected ap = n.isProtected ap := by
    unfold TreeTagNode.isProtected
    rw [hprot]
  exact ⟨htag, hpe, hro, hrl, fun hp' him => hIM (hpe ▸ hp') (hIM' him), hUA' hUA, hok n' hn'⟩

private theorem nwsr_listRel_of_forall {α β : Type} {R : α → β → Prop} :
    ∀ (xs : List α), (∀ x ∈ xs, ∃ y, R x y) → ∃ ys, ListRel R xs ys
  | [], _ => ⟨[], .nil⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x (List.mem_cons_self ..)
    obtain ⟨ys, hys⟩ := nwsr_listRel_of_forall xs (fun z hz => h z (List.mem_cons_of_mem _ hz))
    exact ⟨y :: ys, .cons hy hys⟩

private theorem nwsr_tree_sim_core
    (k : Gen.AccessKind) (isWrite : Bool)
    (step : Bool → TreeTagNode → Except RetagStepErr TreeTagNode)
    (off len : Nat) (hlen : 0 < len) (emb : Nat → Gen.Path)
    (w : FnEntryBorrowWorld) (t : Gen.Node) (tag : Nat)
    (hinv : TreeSimInv off len emb w t)
    (hstep : ∀ n ∈ w.nodes, NodeStepSim w.activeProtectors k step n)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = locOf (some (emb tag)) (emb n.tag))
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) isWrite off len n = false) :
    (∀ nodes', ListRel (PrunedStepRel w tag isWrite off len step) w.nodes nodes' →
      ∃ t', Node.access t (some (emb tag)) k ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInv off len emb { w with nodes := nodes' } t') ∧
    ((∀ nodes', ¬ ListRel (PrunedStepRel w tag isWrite off len step) w.nodes nodes') →
      ∃ msg, Node.access t (some (emb tag)) k ⟨off⟩ ⟨len⟩ = .error (.ub msg)) := by
  -- Locality bridge: `PrunedStepRel` is exactly the path-determined step.
  have hpr : ∀ n ∈ w.nodes, ∀ n', PrunedStepRel w tag isWrite off len step n n' →
      step (locOf (some (emb tag)) (emb n.tag)) n = .ok n' := by
    intro n hn n' hrel
    rcases hrel with ⟨hc, hs⟩ | ⟨_, hp, _⟩ | ⟨hc, _, hs⟩
    · rw [← hloc n hn, hc]; exact hs
    · rw [hnoprune n hn] at hp; cases hp
    · rw [← hloc n hn, hc]; exact hs
  have hrp : ∀ n ∈ w.nodes, ∀ n', step (locOf (some (emb tag)) (emb n.tag)) n = .ok n' →
      PrunedStepRel w tag isWrite off len step n n' := by
    intro n hn n' hs
    cases hl : locOf (some (emb tag)) (emb n.tag) with
    | true => rw [hl] at hs; exact Or.inl ⟨by rw [hloc n hn, hl], hs⟩
    | false =>
      rw [hl] at hs
      exact Or.inr (Or.inr ⟨by rw [hloc n hn, hl], hnoprune n hn, hs⟩)
  -- Every MiniRust node is the image of an Anneal node carrying the window relation.
  have hmr : ∀ q m, nodeAt t q = some m → ∃ n ∈ w.nodes, emb n.tag = q ∧
      NodeWindowRel w.activeProtectors off len n m := by
    intro q m hq
    obtain ⟨n, hn, hemb⟩ := hinv.surj q m hq
    obtain ⟨m', hm', hrel⟩ := hinv.nodes n hn
    rw [hemb, hq] at hm'
    cases hm'
    exact ⟨n, hn, hemb, hrel⟩
  have hrelNode : ∀ (isLocal : Bool), nodeRelToMiniRust isLocal =
      (if isLocal then Gen.NodeRelation.Local else .Foreign) := fun _ => rfl
  constructor
  · intro nodes' hrel
    have hpoint : ∀ q m, nodeAt t q = some m →
        ∃ ps', Node.transitionRange (locRel (some (emb tag)) q) k off len m.permissions =
          .ok ps' := by
      intro q m hq
      obtain ⟨n, hn, hemb, _, p, hp, hwin⟩ := hmr q m hq
      obtain ⟨n', _, hnn'⟩ := hrel.exists_of_mem_left hn
      have hs := hpr n hn n' hnn'
      obtain ⟨p0, hp0, hok, _⟩ := hstep n hn (locOf (some (emb tag)) (emb n.tag))
      rw [hp] at hp0
      cases hp0
      obtain ⟨_, _, _, _, _, _, p', htr, _⟩ := hok n' hs
      rw [hemb] at htr
      obtain ⟨ps', hrun, _⟩ := transitionRange_ok_of_pointwise
        (locRel (some (emb tag)) q) k len off m.permissions
        (fun b h1 h2 => ⟨p, p', hwin b h1 h2, htr⟩)
      exact ⟨ps', hrun⟩
    obtain ⟨t', hacc, hpost⟩ :=
      node_access_ok_of_pointwise k off len t (some (emb tag)) hpoint
    refine ⟨t', hacc, ?_⟩
    -- Per-node post-state facts.
    have hnode : ∀ n' ∈ nodes', ∃ n ∈ w.nodes, n'.tag = n.tag ∧
        n'.rangeOffset = n.rangeOffset ∧ n'.rangeLen = n.rangeLen ∧
        (n'.isProtected w.activeProtectors = true → n'.perm ≠ .reservedIM) ∧
        (n'.isProtected w.activeProtectors = true → n'.perm = .unique → n'.accessed = true) ∧
        ∃ m', nodeAt t' (emb n'.tag) = some m' ∧
          NodeWindowRel w.activeProtectors off len n' m' := by
      intro n' hn'
      obtain ⟨n, hn, hnn'⟩ := hrel.exists_of_mem_right hn'
      have hs := hpr n hn n' hnn'
      obtain ⟨m, hm, hprotm, p, hp, hwin⟩ := hinv.nodes n hn
      obtain ⟨p0, hp0, hok, _⟩ := hstep n hn (locOf (some (emb tag)) (emb n.tag))
      rw [hp] at hp0
      cases hp0
      obtain ⟨htag, hpe, hro, hrl, hIM, hUA, p', htr, hp'⟩ := hok n' hs
      obtain ⟨m', hm', hprot', hrun⟩ := (hpost (emb n.tag)).1 m hm
      refine ⟨n, hn, htag, hro, hrl, hIM, hUA, m', by rw [htag]; exact hm', ?_, p', ?_, ?_⟩
      · rw [hprot', hprotm, hpe]
      · rw [hpe]; exact hp'
      · intro b h1 h2
        obtain ⟨ps', hrun', _, _, hin⟩ := transitionRange_ok_of_pointwise
          (locRel (some (emb tag)) (emb n.tag)) k len off m.permissions
          (fun b h1 h2 => ⟨p, p', hwin b h1 h2, htr⟩)
        rw [hrun] at hrun'
        cases hrun'
        obtain ⟨p'', htr'', hget⟩ := hin b h1 h2 p (hwin b h1 h2)
        have htr2 : Permission.transition p k (locRel (some (emb tag)) (emb n.tag)) =
            .ok p' := htr
        rw [htr2] at htr''
        cases htr''
        exact hget
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n' hn'
      obtain ⟨_, _, _, _, _, _, _, m', hm', hrel'⟩ := hnode n' hn'
      exact ⟨m', hm', hrel'⟩
    · intro q m' hq'
      cases hq : nodeAt t q with
      | none =>
        rw [(hpost q).2 hq] at hq'
        cases hq'
      | some m =>
        obtain ⟨n, hn, hemb⟩ := hinv.surj q m hq
        obtain ⟨n', hn', hnn'⟩ := hrel.exists_of_mem_left hn
        have hs := hpr n hn n' hnn'
        obtain ⟨_, _, hok, _⟩ := hstep n hn (locOf (some (emb tag)) (emb n.tag))
        obtain ⟨htag, _⟩ := hok n' hs
        exact ⟨n', hn', by rw [htag]; exact hemb⟩
    · intro n' hn'
      obtain ⟨n, hn, _, hro, hrl, _⟩ := hnode n' hn'
      rw [hro, hrl]
      exact hinv.overlap n hn
    · intro n' hn'
      obtain ⟨_, _, _, _, _, hIM, _⟩ := hnode n' hn'
      exact hIM
    · intro n' hn'
      obtain ⟨_, _, _, _, _, _, hUA, _⟩ := hnode n' hn'
      exact hUA
  · intro hno
    cases hacc : Node.access t (some (emb tag)) k ⟨off⟩ ⟨len⟩ with
    | ok t' =>
      exfalso
      have hall : ∀ n ∈ w.nodes, ∃ n', PrunedStepRel w tag isWrite off len step n n' := by
        intro n hn
        obtain ⟨m, hm, _, p, hp, hwin⟩ := hinv.nodes n hn
        obtain ⟨ps', hrun⟩ := node_access_ok_inv k off len t t' (some (emb tag)) hacc
          (emb n.tag) m hm
        obtain ⟨q0, q0', hq0, htr0⟩ := transitionRange_ok_inv
          (locRel (some (emb tag)) (emb n.tag)) k len off m.permissions ps' hrun off
          (Nat.le_refl _) (by omega)
        rw [hwin off (Nat.le_refl _) (by omega)] at hq0
        cases hq0
        obtain ⟨p0, hp0, _, herr⟩ := hstep n hn (locOf (some (emb tag)) (emb n.tag))
        rw [hp] at hp0
        cases hp0
        cases hs : step (locOf (some (emb tag)) (emb n.tag)) n with
        | ok n' => exact ⟨n', hrp n hn n' hs⟩
        | error e =>
          obtain ⟨msg, hmsg⟩ := herr e hs
          rw [hrelNode] at hmsg
          have htr0' : Permission.transition p k
              (if locOf (some (emb tag)) (emb n.tag) then Gen.NodeRelation.Local else .Foreign) =
              .ok q0' := htr0
          rw [htr0'] at hmsg
          cases hmsg
      obtain ⟨nodes', hrel⟩ := nwsr_listRel_of_forall w.nodes hall
      exact hno nodes' hrel
    | error e =>
      obtain ⟨q, m, hq, herr⟩ := node_access_error_inv k off len t (some (emb tag)) e hacc
      obtain ⟨n, _, _, _, p, _, hwin⟩ := hmr q m hq
      have hlast := hwin (off + len - 1) (by omega) (by omega)
      have hlt : off + len - 1 < m.permissions.length :=
        (List.getElem?_eq_some_iff.mp hlast).1
      obtain ⟨msg, hmsg⟩ := transitionRange_error_is_ub (locRel (some (emb tag)) q) k len off
        m.permissions e (by omega) herr
      exact ⟨msg, by rw [hmsg]⟩

/-- **Whole-tree relational READ simulation** (`execWorldRangeRead` ↔ MiniRust
`Node.access … AccessKind::Read`, the tree access performed by
`TreeBorrowsMemory.load`): for EVERY borrow world `w` and MiniRust borrow tree `t`
of ANY shape and size related by `TreeSimInv` on the non-empty byte window
`[off, off + len)`, whenever the Anneal ancestor set of `tag` coincides with the
MiniRust path-prefix relation (`hloc`) and Miri's `SkipSelfAndChildren` pruning is
inactive (`hnoprune`, the hypothesis of
`execFnEntryMutRetagPrunedSourceOrder_eq_sourceOrder_of_noSkippedForeignSubtree`):
1. every successful Anneal read is matched by a successful MiniRust tree access
   whose result is again `TreeSimInv`-related (the invariant is inductive);
2. every Anneal read error is Tree Borrows UB in MiniRust;
3. conversely every successful MiniRust access is matched by a successful Anneal
   read into a `TreeSimInv`-related world. -/
theorem tree_read_simulates_node_access
    (off len : Nat) (hlen : 0 < len) (emb : Nat → Gen.Path)
    (w : FnEntryBorrowWorld) (t : Gen.Node) (tag : Nat)
    (hinv : TreeSimInv off len emb w t)
    (htag : ∃ n, findNode? w.nodes tag = some n)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = locOf (some (emb tag)) (emb n.tag))
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) false off len n = false) :
    (∀ w', execWorldRangeRead w tag off len = .ok w' →
      ∃ t', Node.access t (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInv off len emb w' t') ∧
    (∀ e, execWorldRangeRead w tag off len = .error e →
      ∃ msg, Node.access t (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ = .error (.ub msg)) ∧
    (∀ t', Node.access t (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ = .ok t' →
      ∃ w', execWorldRangeRead w tag off len = .ok w' ∧ TreeSimInv off len emb w' t') := by
  have hne : len ≠ 0 := by omega
  obtain ⟨hfwd, hbwd⟩ := nwsr_tree_sim_core .Read false
    (fun isLoc m => stepNodeOnRangeRead w.activeProtectors isLoc off len m)
    off len hlen emb w t tag hinv
    (fun n hn => nwsr_stepRead_sim w.activeProtectors off len n (hinv.overlap n hn)
      (hinv.noProtIM n hn) (hinv.protUniqAcc n hn))
    hloc hnoprune
  have h1 : ∀ w', execWorldRangeRead w tag off len = .ok w' →
      ∃ t', Node.access t (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInv off len emb w' t' := by
    intro w' hok
    obtain ⟨_, nodes', hw', hrel⟩ := (execWorldRangeRead_ok_iff w w' tag off len hne).mp hok
    rw [hw']
    exact hfwd nodes' hrel
  have h2 : ∀ e, execWorldRangeRead w tag off len = .error e →
      ∃ msg, Node.access t (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ = .error (.ub msg) := by
    intro e herr
    apply hbwd
    intro nodes' hrel
    have hok := (execWorldRangeRead_ok_iff w { w with nodes := nodes' } tag off len hne).mpr
      ⟨htag, nodes', rfl, hrel⟩
    rw [herr] at hok
    cases hok
  refine ⟨h1, h2, ?_⟩
  intro t' hacc
  cases hr : execWorldRangeRead w tag off len with
  | ok w' =>
    obtain ⟨t'', hacc'', hinv'⟩ := h1 w' hr
    rw [hacc] at hacc''
    cases hacc''
    exact ⟨w', rfl, hinv'⟩
  | error e =>
    obtain ⟨msg, hmsg⟩ := h2 e hr
    rw [hacc] at hmsg
    cases hmsg

/-- **Whole-tree relational WRITE simulation** (`execWorldRangeWrite` ↔ MiniRust
`Node.access … AccessKind::Write`, the tree access performed by
`TreeBorrowsMemory.store`): the write counterpart of
`tree_read_simulates_node_access` on any mutable allocation
(`w.allocReadOnly = false`; MiniRust has no read-only allocation check). -/
theorem tree_write_simulates_node_access
    (off len : Nat) (hlen : 0 < len) (emb : Nat → Gen.Path)
    (w : FnEntryBorrowWorld) (t : Gen.Node) (tag : Nat)
    (hinv : TreeSimInv off len emb w t)
    (hro : w.allocReadOnly = false)
    (htag : ∃ n, findNode? w.nodes tag = some n)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = locOf (some (emb tag)) (emb n.tag))
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) true off len n = false) :
    (∀ w', execWorldRangeWrite w tag off len = .ok w' →
      ∃ t', Node.access t (some (emb tag)) .Write ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInv off len emb w' t') ∧
    (∀ e, execWorldRangeWrite w tag off len = .error e →
      ∃ msg, Node.access t (some (emb tag)) .Write ⟨off⟩ ⟨len⟩ = .error (.ub msg)) ∧
    (∀ t', Node.access t (some (emb tag)) .Write ⟨off⟩ ⟨len⟩ = .ok t' →
      ∃ w', execWorldRangeWrite w tag off len = .ok w' ∧ TreeSimInv off len emb w' t') := by
  have hne : len ≠ 0 := by omega
  obtain ⟨hfwd, hbwd⟩ := nwsr_tree_sim_core .Write true
    (fun isLoc m => stepNodeOnRangeWrite w.activeProtectors isLoc off len m)
    off len hlen emb w t tag hinv
    (fun n hn => nwsr_stepWrite_sim w.activeProtectors off len n (hinv.overlap n hn)
      (hinv.noProtIM n hn) (hinv.protUniqAcc n hn))
    hloc hnoprune
  have h1 : ∀ w', execWorldRangeWrite w tag off len = .ok w' →
      ∃ t', Node.access t (some (emb tag)) .Write ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInv off len emb w' t' := by
    intro w' hok
    obtain ⟨_, _, nodes', hw', hrel⟩ := (execWorldRangeWrite_ok_iff w w' tag off len hne).mp hok
    rw [hw']
    exact hfwd nodes' hrel
  have h2 : ∀ e, execWorldRangeWrite w tag off len = .error e →
      ∃ msg, Node.access t (some (emb tag)) .Write ⟨off⟩ ⟨len⟩ = .error (.ub msg) := by
    intro e herr
    apply hbwd
    intro nodes' hrel
    have hok := (execWorldRangeWrite_ok_iff w { w with nodes := nodes' } tag off len hne).mpr
      ⟨hro, htag, nodes', rfl, hrel⟩
    rw [herr] at hok
    cases hok
  refine ⟨h1, h2, ?_⟩
  intro t' hacc
  cases hr : execWorldRangeWrite w tag off len with
  | ok w' =>
    obtain ⟨t'', hacc'', hinv'⟩ := h1 w' hr
    rw [hacc] at hacc''
    cases hacc''
    exact ⟨w', rfl, hinv'⟩
  | error e =>
    obtain ⟨msg, hmsg⟩ := h2 e hr
    rw [hacc] at hmsg
    cases hmsg

/-! ### 4.4 `TreeBorrowsMemory.store` / `load` as `Node.access` & Two-Node Tree Equations -/

private theorem nwsr_check_ptr_ok
    (mem : Gen.BasicMemory Gen.x86_64 Gen.Path Gen.TreeBorrowsAllocationExtra)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (id : Nat) (path : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (off len : Nat)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, path))
    (halloc : mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (hoff : ptr.addr - alloc.addr = (off : Int)) (hb : off + len ≤ alloc.data.length)
    (hlen : len ≠ 0) :
    BasicMemory.check_ptr mem ptr ⟨len⟩ = .ok (some (⟨(id : Int)⟩, path, ⟨off⟩)) := by
  have hnn : (0 : Int) ≤ (id : Int) := Int.natCast_nonneg id
  have htn : ((id : Int)).toNat = id := rfl
  have hc : ¬ ((off : Int) < 0 ∨ (off : Int) + (len : Int) > (alloc.data.length : Int)) := by
    omega
  have hto : ((off : Int)).toNat = off := rfl
  unfold BasicMemory.check_ptr listIndex
  simp only [hlen, ↓reduceIte, hprov, hnn, htn, halloc, hlive, Bool.not_true, Bool.false_eq_true,
    hoff, Allocation.size, hc, hto, bind, Except.bind, pure, Except.pure]

/-- **`TreeBorrowsMemory.store` is the tree access `Node.access … Write`**: for
every Tree Borrows memory, live allocation `alloc` at index `id`, and aligned
non-empty in-bounds store through provenance `(id, path)`, `TreeBorrowsMemory.store`
succeeds or fails EXACTLY as `Node.access alloc.extra.root (some path) Write` does
on the stored byte window (and then splices the bytes into the allocation). -/
theorem tbm_store_eq_node_access (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (align : LibSpecr.Align)
    (id : Nat) (path : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (off : Nat)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, path))
    (halloc : tbm.mem.allocations[id]? = some alloc)
    (hlive : alloc.live = true)
    (haligned : Align.is_aligned align ptr.addr = true)
    (hoff : ptr.addr - alloc.addr = (off : Int))
    (hlen : bytes.length ≠ 0)
    (hbound : off + bytes.length ≤ alloc.data.length) :
    TreeBorrowsMemory.store tbm ptr bytes align =
      (Node.access alloc.extra.root (some path) .Write ⟨off⟩ ⟨bytes.length⟩ >>= fun root' =>
        pure { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id
          { alloc with
            data := alloc.data.take off ++ bytes ++ alloc.data.drop (off + bytes.length),
            extra := { root := root' } }) } }) := by
  have hnn : (0 : Int) ≤ (id : Int) := Int.natCast_nonneg id
  have htn : ((id : Int)).toNat = id := rfl
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  have hcheck := nwsr_check_ptr_ok tbm.mem ptr id path alloc off bytes.length hprov halloc hlive
    hoff hbound hlen
  have hto : ((off : Int)).toNat = off := rfl
  have hw : (0 : Int) ≤ (off : Int) ∧
      (off : Int) + (bytes.length : Int) ≤ (alloc.data.length : Int) :=
    ⟨by omega, by omega⟩
  unfold TreeBorrowsMemory.store BasicMemory.store
  simp only [haligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcheck, bind, Except.bind,
    listIndex, hnn, htn, halloc, pure, Except.pure]
  cases Node.access alloc.extra.root (some path) .Write ⟨off⟩ ⟨bytes.length⟩ with
  | error e => rfl
  | ok root' =>
    simp only [writeSubsliceAtIndex, hw, and_self, ↓reduceIte, hto, listSet, hnn, htn, hidlt,
      pure, Except.pure]

/-- **`TreeBorrowsMemory.load` is the tree access `Node.access … Read`**: the
read counterpart of `tbm_store_eq_node_access`. -/
theorem tbm_load_eq_node_access (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (len : Nat) (align : LibSpecr.Align)
    (id : Nat) (path : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (off : Nat)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, path))
    (halloc : tbm.mem.allocations[id]? = some alloc)
    (hlive : alloc.live = true)
    (haligned : Align.is_aligned align ptr.addr = true)
    (hoff : ptr.addr - alloc.addr = (off : Int))
    (hlen : len ≠ 0)
    (hbound : off + len ≤ alloc.data.length) :
    TreeBorrowsMemory.load tbm ptr ⟨len⟩ align =
      (Node.access alloc.extra.root (some path) .Read ⟨off⟩ ⟨len⟩ >>= fun root' =>
        pure ((alloc.data.drop off).take len,
          { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id
            { alloc with extra := { root := root' } }) } })) := by
  have hnn : (0 : Int) ≤ (id : Int) := Int.natCast_nonneg id
  have htn : ((id : Int)).toNat = id := rfl
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  have hcheck := nwsr_check_ptr_ok tbm.mem ptr id path alloc off len hprov halloc hlive
    hoff hbound hlen
  have hto : ((off : Int)).toNat = off := rfl
  have htl : ((len : Int)).toNat = len := rfl
  have hw : (0 : Int) ≤ (off : Int) ∧ (0 : Int) ≤ (len : Int) ∧
      (off : Int) + (len : Int) ≤ (alloc.data.length : Int) :=
    ⟨by omega, by omega, by omega⟩
  unfold TreeBorrowsMemory.load BasicMemory.load
  simp only [haligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcheck, bind, Except.bind,
    listIndex, hnn, htn, halloc, pure, Except.pure]
  cases Node.access alloc.extra.root (some path) .Read ⟨off⟩ ⟨len⟩ with
  | error e => rfl
  | ok root' =>
    simp only [subsliceWithLength, hw, and_self, ↓reduceIte, hto, htl, listSet, hnn, htn, hidlt,
      pure, Except.pure]

/-- **Two-node tree equation**: on a root with a single leaf child `[0]`, an
access through the child is the root's `Local` window transition followed by the
child's `Local` window transition. -/
theorem node_access_rootChild_eq (k : Gen.AccessKind) (o len : Nat)
    (rootPerms inside : List Gen.Permission) (rp cp : Gen.Protected) :
    Node.access ⟨[⟨[], inside, cp⟩], rootPerms, rp⟩ (some [0]) k ⟨o⟩ ⟨len⟩ =
      (Node.transitionRange .Local k o len rootPerms >>= fun rps =>
        Node.transitionRange .Local k o len inside >>= fun ips =>
          pure ⟨[⟨[], ips, cp⟩], rps, rp⟩) := by
  have hsub : subPathAt (some [(0 : Int)]) 0 = some [] := rfl
  rw [nwsr_access_eq, nwsr_accessChildren_cons, hsub, nwsr_access_eq,
    Node.accessChildren, Node.accessChildren]
  have h1 : locRel (some [(0 : Int)]) [] = .Local := rfl
  have h2 : locRel (some ([] : Gen.Path)) [] = .Local := rfl
  rw [h1, h2]
  cases Node.transitionRange .Local k o len rootPerms <;>
    cases Node.transitionRange .Local k o len inside <;> rfl

/-- **Single-node tree equation**: an access through the root of a childless tree
is the root's `Local` window transition. -/
theorem node_access_rootOnly_eq (k : Gen.AccessKind) (o len : Nat)
    (rootPerms : List Gen.Permission) (rp : Gen.Protected) :
    Node.access ⟨[], rootPerms, rp⟩ (some []) k ⟨o⟩ ⟨len⟩ =
      (Node.transitionRange .Local k o len rootPerms >>= fun rps => pure ⟨[], rps, rp⟩) := by
  rw [nwsr_access_eq, Node.accessChildren]
  have h2 : locRel (some ([] : Gen.Path)) [] = .Local := rfl
  rw [h2]
  cases Node.transitionRange .Local k o len rootPerms <;> rfl

/-! ### 4.5 Tree-Simulation Lifted to `TreeBorrowsMemory.store` / `load`, Decidable Relation Checker, & Canaries -/

/-- **`TreeBorrowsMemory.store` simulates `execWorldRangeWrite` on whole borrow
trees**: for every Tree Borrows memory whose allocation `id` carries a borrow tree
`TreeSimInv`-related to the world `w` on the stored window, an aligned in-bounds
store through `emb tag` succeeds iff `execWorldRangeWrite w tag` does, the updated
allocation is again `TreeSimInv`-related, and every Anneal error is MiniRust UB. -/
theorem tbm_store_simulates_execWorldRangeWrite
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (align : LibSpecr.Align)
    (id : Nat) (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (off : Nat)
    (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld) (tag : Nat)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, emb tag))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (haligned : Align.is_aligned align ptr.addr = true)
    (hoff : ptr.addr - alloc.addr = (off : Int))
    (hlen : bytes.length ≠ 0) (hbound : off + bytes.length ≤ alloc.data.length)
    (hinv : TreeSimInv off bytes.length emb w alloc.extra.root)
    (hro : w.allocReadOnly = false)
    (htag : ∃ n, findNode? w.nodes tag = some n)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = locOf (some (emb tag)) (emb n.tag))
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) true off bytes.length n = false) :
    (∀ w', execWorldRangeWrite w tag off bytes.length = .ok w' →
      ∃ tbm' alloc', TreeBorrowsMemory.store tbm ptr bytes align = .ok tbm' ∧
        tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
        TreeSimInv off bytes.length emb w' alloc'.extra.root) ∧
    (∀ e, execWorldRangeWrite w tag off bytes.length = .error e →
      ∃ msg, TreeBorrowsMemory.store tbm ptr bytes align = .error (.ub msg)) ∧
    (∀ tbm', TreeBorrowsMemory.store tbm ptr bytes align = .ok tbm' →
      ∃ w', execWorldRangeWrite w tag off bytes.length = .ok w') := by
  obtain ⟨h1, h2, h3⟩ := tree_write_simulates_node_access off bytes.length
    (Nat.pos_of_ne_zero hlen) emb w alloc.extra.root tag hinv hro htag hloc hnoprune
  have heq := tbm_store_eq_node_access tbm ptr bytes align id (emb tag) alloc off hprov halloc
    hlive haligned hoff hlen hbound
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  refine ⟨?_, ?_, ?_⟩
  · intro w' hok
    obtain ⟨t', hacc, hinv'⟩ := h1 w' hok
    rw [heq, hacc]
    exact ⟨_, _, rfl, List.getElem?_set_self hidlt, hlive, hinv'⟩
  · intro e herr
    obtain ⟨msg, hmsg⟩ := h2 e herr
    exact ⟨msg, by rw [heq, hmsg]; rfl⟩
  · intro tbm' hok
    rw [heq] at hok
    cases hacc : Node.access alloc.extra.root (some (emb tag)) .Write ⟨off⟩ ⟨bytes.length⟩ with
    | ok t' =>
      obtain ⟨w', hw', _⟩ := h3 t' hacc
      exact ⟨w', hw'⟩
    | error e =>
      rw [hacc] at hok
      cases hok

/-- **`TreeBorrowsMemory.load` simulates `execWorldRangeRead` on whole borrow
trees**: the read counterpart of `tbm_store_simulates_execWorldRangeWrite`. -/
theorem tbm_load_simulates_execWorldRangeRead
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (len : Nat) (align : LibSpecr.Align)
    (id : Nat) (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (off : Nat)
    (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld) (tag : Nat)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, emb tag))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (haligned : Align.is_aligned align ptr.addr = true)
    (hoff : ptr.addr - alloc.addr = (off : Int))
    (hlen : len ≠ 0) (hbound : off + len ≤ alloc.data.length)
    (hinv : TreeSimInv off len emb w alloc.extra.root)
    (htag : ∃ n, findNode? w.nodes tag = some n)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = locOf (some (emb tag)) (emb n.tag))
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) false off len n = false) :
    (∀ w', execWorldRangeRead w tag off len = .ok w' →
      ∃ tbm' alloc', TreeBorrowsMemory.load tbm ptr ⟨len⟩ align =
          .ok ((alloc.data.drop off).take len, tbm') ∧
        tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
        TreeSimInv off len emb w' alloc'.extra.root) ∧
    (∀ e, execWorldRangeRead w tag off len = .error e →
      ∃ msg, TreeBorrowsMemory.load tbm ptr ⟨len⟩ align = .error (.ub msg)) ∧
    (∀ r, TreeBorrowsMemory.load tbm ptr ⟨len⟩ align = .ok r →
      ∃ w', execWorldRangeRead w tag off len = .ok w') := by
  obtain ⟨h1, h2, h3⟩ := tree_read_simulates_node_access off len
    (Nat.pos_of_ne_zero hlen) emb w alloc.extra.root tag hinv htag hloc hnoprune
  have heq := tbm_load_eq_node_access tbm ptr len align id (emb tag) alloc off hprov halloc
    hlive haligned hoff hlen hbound
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  refine ⟨?_, ?_, ?_⟩
  · intro w' hok
    obtain ⟨t', hacc, hinv'⟩ := h1 w' hok
    rw [heq, hacc]
    exact ⟨_, _, rfl, List.getElem?_set_self hidlt, hlive, hinv'⟩
  · intro e herr
    obtain ⟨msg, hmsg⟩ := h2 e herr
    exact ⟨msg, by rw [heq, hmsg]; rfl⟩
  · intro r hok
    rw [heq] at hok
    cases hacc : Node.access alloc.extra.root (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ with
    | ok t' =>
      obtain ⟨w', hw', _⟩ := h3 t' hacc
      exact ⟨w', hw'⟩
    | error e =>
      rw [hacc] at hok
      cases hok

mutual

/-- All relative paths of a MiniRust borrow tree (pre-order). -/
def nodePaths : Gen.Node → List Gen.Path
  | ⟨cs, _, _⟩ => [] :: childrenPaths 0 cs

/-- All relative paths below a child list whose first child has index `cid`. -/
def childrenPaths (cid : Nat) : List Gen.Node → List Gen.Path
  | [] => []
  | c :: rest => (nodePaths c).map ((cid : Int) :: ·) ++ childrenPaths (cid + 1) rest

end

mutual

/-- `nodePaths` enumerates every path at which `nodeAt` finds a node. -/
theorem nodeAt_mem_nodePaths :
    ∀ (n : Gen.Node) (q : Gen.Path) (m : Gen.Node), nodeAt n q = some m → q ∈ nodePaths n
  | ⟨_, _, _⟩, [], _, _ => by
    rw [nodePaths]
    exact List.mem_cons_self ..
  | ⟨cs, ps, pr⟩, i :: rest, m, h => by
    rw [nodePaths]
    by_cases hi : 0 ≤ i
    · cases hc : cs[i.toNat]? with
      | none =>
        rw [nwsr_nodeAt_cons_none cs ps pr i rest hi hc] at h
        cases h
      | some c =>
        rw [nwsr_nodeAt_cons_some cs ps pr i rest c hi hc] at h
        have hmem := nodeAt_mem_childrenPaths cs 0 i.toNat c hc rest m h
        rw [Nat.zero_add, Int.toNat_of_nonneg hi] at hmem
        exact List.mem_cons_of_mem _ hmem
    · rw [nwsr_nodeAt_cons_neg cs ps pr i rest hi] at h
      cases h

/-- Child-list companion of `nodeAt_mem_nodePaths`. -/
theorem nodeAt_mem_childrenPaths :
    ∀ (cs : List Gen.Node) (cid j : Nat) (c : Gen.Node), cs[j]? = some c →
      ∀ (rest : Gen.Path) (m : Gen.Node), nodeAt c rest = some m →
        (((cid + j : Nat) : Int) :: rest) ∈ childrenPaths cid cs
  | [], _, _, _, hc, _, _, _ => by simp at hc
  | c0 :: cs, cid, 0, c, hc, rest, m, h => by
    rw [List.getElem?_cons_zero] at hc
    cases hc
    rw [childrenPaths]
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨rest, nodeAt_mem_nodePaths c0 rest m h, rfl⟩)
  | _ :: cs, cid, j + 1, c, hc, rest, m, h => by
    rw [List.getElem?_cons_succ] at hc
    rw [childrenPaths]
    have hmem := nodeAt_mem_childrenPaths cs (cid + 1) j c hc rest m h
    have e : cid + 1 + j = cid + (j + 1) := by omega
    rw [e] at hmem
    exact List.mem_append_right _ hmem

end

/-- Computable checker for `NodeWindowRel`. -/
def nodeWindowRelBool (ap : List Nat) (off len : Nat) (n : TreeTagNode) (m : Gen.Node) : Bool :=
  decide (Protected.yes m.«protected» = n.isProtected ap) &&
  match permToMiniRust (n.isProtected ap) n.accessed n.perm with
  | some p => (List.range len).all (fun i => decide (m.permissions[off + i]? = some p))
  | none => false

theorem nodeWindowRel_of_bool (ap : List Nat) (off len : Nat) (n : TreeTagNode) (m : Gen.Node)
    (h : nodeWindowRelBool ap off len n m = true) : NodeWindowRel ap off len n m := by
  unfold nodeWindowRelBool at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨of_decide_eq_true h1, ?_⟩
  cases hp : permToMiniRust (n.isProtected ap) n.accessed n.perm with
  | none =>
    rw [hp] at h2
    cases h2
  | some p =>
    rw [hp] at h2
    refine ⟨p, rfl, fun b hb1 hb2 => ?_⟩
    have hall := List.all_eq_true.mp h2 (b - off) (List.mem_range.mpr (by omega))
    have hget := of_decide_eq_true hall
    have e : off + (b - off) = b := by omega
    rw [e] at hget
    exact hget

/-- Computable checker for `TreeSimInv`. -/
def treeSimInvBool (off len : Nat) (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld)
    (t : Gen.Node) : Bool :=
  w.nodes.all (fun n =>
    (match nodeAt t (emb n.tag) with
      | some m => nodeWindowRelBool w.activeProtectors off len n m
      | none => false) &&
    rangesOverlap off len n.rangeOffset n.rangeLen &&
    (!n.isProtected w.activeProtectors ||
      (decide (n.perm ≠ .reservedIM) && (decide (n.perm ≠ .unique) || n.accessed)))) &&
  (nodePaths t).all (fun q => w.nodes.any (fun n => decide (emb n.tag = q)))

/-- Constructive soundness of `treeSimInvBool` (zero `Classical.choice`). -/
theorem treeSimInv_of_bool (off len : Nat) (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld)
    (t : Gen.Node) (h : treeSimInvBool off len emb w t = true) :
    TreeSimInv off len emb w t := by
  unfold treeSimInvBool at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨hn, hs⟩ := h
  have hn' : ∀ n ∈ w.nodes,
      ((match nodeAt t (emb n.tag) with
        | some m => nodeWindowRelBool w.activeProtectors off len n m
        | none => false) = true ∧
       rangesOverlap off len n.rangeOffset n.rangeLen = true) ∧
      (!n.isProtected w.activeProtectors ||
        (decide (n.perm ≠ .reservedIM) && (decide (n.perm ≠ .unique) || n.accessed))) = true := by
    intro n hm
    have h0 := hn n hm
    rw [Bool.and_eq_true, Bool.and_eq_true] at h0
    exact h0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hm
    have h1 := (hn' n hm).1.1
    cases hq : nodeAt t (emb n.tag) with
    | none =>
      rw [hq] at h1
      cases h1
    | some m =>
      rw [hq] at h1
      exact ⟨m, rfl, nodeWindowRel_of_bool _ _ _ _ _ h1⟩
  · intro q m hq
    have h1 := hs q (nodeAt_mem_nodePaths t q m hq)
    rw [List.any_eq_true] at h1
    obtain ⟨n, hm, hd⟩ := h1
    exact ⟨n, hm, of_decide_eq_true hd⟩
  · intro n hm
    exact (hn' n hm).1.2
  · intro n hm hp
    have h3 := (hn' n hm).2
    rw [hp] at h3
    have h4 : (decide (n.perm ≠ .reservedIM) && (decide (n.perm ≠ .unique) || n.accessed)) =
        true := h3
    rw [Bool.and_eq_true] at h4
    exact of_decide_eq_true h4.1
  · intro n hm hp hu
    have h3 := (hn' n hm).2
    rw [hp] at h3
    have h4 : (decide (n.perm ≠ .reservedIM) && (decide (n.perm ≠ .unique) || n.accessed)) =
        true := h3
    rw [Bool.and_eq_true, Bool.or_eq_true] at h4
    rcases h4.2 with h5 | h5
    · exact absurd hu (of_decide_eq_true h5)
    · exact h5

/-- Borrow tree of allocation `idx` of a `TreeBorrowsMemory`. -/
def tbmRootOf (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (idx : Nat) : Option Gen.Node :=
  tbm.mem.allocations[idx]?.map (·.extra.root)

/-- Decidable relational check between an Anneal world result and a MiniRust
`TreeBorrowsMemory` result: both succeed and allocation `0`'s borrow tree is
`TreeSimInv`-related to the world on the window `[off, off + len)`. -/
def tbmWorldRelBool (off len : Nat) (emb : Nat → Gen.Path)
    (rw : Except RetagStepErr FnEntryBorrowWorld)
    (rt : Interp (Gen.TreeBorrowsMemory Gen.x86_64)) : Bool :=
  match rw, rt with
  | .ok w, .ok tbm =>
    match tbmRootOf tbm 0 with
    | some t => treeSimInvBool off len emb w t
    | none => false
  | _, _ => false

/-- Constructive soundness of `tbmWorldRelBool`. -/
theorem tbmWorldRel_of_bool {off len : Nat} {emb : Nat → Gen.Path}
    {rw : Except RetagStepErr FnEntryBorrowWorld}
    {rt : Interp (Gen.TreeBorrowsMemory Gen.x86_64)}
    (h : tbmWorldRelBool off len emb rw rt = true) :
    ∃ w tbm t, rw = .ok w ∧ rt = .ok tbm ∧ tbmRootOf tbm 0 = some t ∧
      TreeSimInv off len emb w t := by
  unfold tbmWorldRelBool at h
  cases rw with
  | error _ => cases h
  | ok w =>
    cases rt with
    | error _ => cases h
    | ok tbm =>
      have h' : (match tbmRootOf tbm 0 with
          | some t => treeSimInvBool off len emb w t
          | none => false) = true := h
      cases hr : tbmRootOf tbm 0 with
      | none =>
        rw [hr] at h'
        cases h'
      | some t =>
        rw [hr] at h'
        exact ⟨w, tbm, t, rfl, rfl, hr, treeSimInv_of_bool off len emb w t h'⟩

/-- Canonical tag-to-path embedding for the two-branch world `mkTwoBranchWorld`
(root `0 ↦ []`, parent `1 ↦ [0]`, sibling `2 ↦ [1]`) extended by a fresh child
`3 ↦ [0, 0]` of the parent. -/
def twoBranchEmb : Nat → Gen.Path
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [0, 0]
  | _ => [7]

/-- MiniRust borrow tree mirroring `mkTwoBranchWorld .unique siblingPerm`: root
`[]` and parent `[0]` are `.Unprot .Unique`; sibling `[1]` carries `sibPerm`. -/
def twoBranchTreeMR (sibPerm : Gen.Permission) : Gen.Node :=
  ⟨[⟨[], List.replicate 4 (.Unprot .Unique), .No⟩, ⟨[], List.replicate 4 sibPerm, .No⟩],
    List.replicate 4 (.Unprot .Unique), .No⟩

private theorem nwsr_exists_ok_of_isOk {ε α : Type} {r : Except ε α} (h : r.isOk = true) :
    ∃ a, r = .ok a := by
  cases r with
  | ok a => exact ⟨a, rfl⟩
  | error _ => cases h

/-- **Closed non-vacuity canary for the whole-tree simulation**: on the concrete
3-node two-branch world / MiniRust tree pair (related by the decidable
`treeSimInvBool`), the symbolic theorems fire with every hypothesis discharged:
1. a READ through the `.frozen` sibling succeeds on both sides and the results are
   again `TreeSimInv`-related (the parent `1` freezes: `.frozen` ↔ `.Unprot .Frozen`);
2. a WRITE through the `.frozen` sibling fails on the Anneal side and is Tree
   Borrows UB on the MiniRust side;
3. a WRITE through the parent succeeds on both sides, disabling the sibling in a
   `TreeSimInv`-related pair of post-states. -/
theorem canary_tree_simulation_twoBranch :
    (∃ w' t', execWorldRangeRead (mkTwoBranchWorld .unique .frozen) 2 0 4 = .ok w' ∧
      Node.access (twoBranchTreeMR (.Unprot .Frozen)) (some [1]) .Read ⟨0⟩ ⟨4⟩ = .ok t' ∧
      TreeSimInv 0 4 twoBranchEmb w' t' ∧
      (findNode? w'.nodes 1).map (·.perm) = some .frozen ∧
      (nodeAt t' [0]).map (·.permissions) = some (List.replicate 4 (.Unprot .Frozen))) ∧
    (execWorldRangeWrite (mkTwoBranchWorld .unique .frozen) 2 0 4 =
        .error (.ancestorWriteForbidden 2) ∧
      ∃ msg, Node.access (twoBranchTreeMR (.Unprot .Frozen)) (some [1]) .Write ⟨0⟩ ⟨4⟩ =
        .error (.ub msg)) ∧
    (∃ w' t', execWorldRangeWrite (mkTwoBranchWorld .unique .frozen) 1 0 4 = .ok w' ∧
      Node.access (twoBranchTreeMR (.Unprot .Frozen)) (some [0]) .Write ⟨0⟩ ⟨4⟩ = .ok t' ∧
      TreeSimInv 0 4 twoBranchEmb w' t' ∧
      (findNode? w'.nodes 2).map (·.perm) = some .disabled ∧
      (nodeAt t' [1]).map (·.permissions) = some (List.replicate 4 (.Unprot .Disabled))) := by
  have hinv : TreeSimInv 0 4 twoBranchEmb (mkTwoBranchWorld .unique .frozen)
      (twoBranchTreeMR (.Unprot .Frozen)) :=
    treeSimInv_of_bool _ _ _ _ _ (by decide +kernel)
  obtain ⟨hr1, _, _⟩ := tree_read_simulates_node_access 0 4 (by decide) twoBranchEmb
    (mkTwoBranchWorld .unique .frozen) (twoBranchTreeMR (.Unprot .Frozen)) 2 hinv
    ⟨_, rfl⟩ (by decide +kernel) (by decide +kernel)
  obtain ⟨_, hw2, _⟩ := tree_write_simulates_node_access 0 4 (by decide) twoBranchEmb
    (mkTwoBranchWorld .unique .frozen) (twoBranchTreeMR (.Unprot .Frozen)) 2 hinv rfl
    ⟨_, rfl⟩ (by decide +kernel) (by decide +kernel)
  obtain ⟨hw1, _, _⟩ := tree_write_simulates_node_access 0 4 (by decide) twoBranchEmb
    (mkTwoBranchWorld .unique .frozen) (twoBranchTreeMR (.Unprot .Frozen)) 1 hinv rfl
    ⟨_, rfl⟩ (by decide +kernel) (by decide +kernel)
  refine ⟨?_, ⟨rfl, hw2 _ rfl⟩, ?_⟩
  · obtain ⟨w', hw'⟩ := nwsr_exists_ok_of_isOk
      (r := execWorldRangeRead (mkTwoBranchWorld .unique .frozen) 2 0 4) (by decide +kernel)
    obtain ⟨t', hacc, hinv'⟩ := hr1 w' hw'
    have hd1 : (execWorldRangeRead (mkTwoBranchWorld .unique .frozen) 2 0 4).toOption.map
        (fun w => (findNode? w.nodes 1).map (·.perm)) = some (some .frozen) := by
      decide +kernel
    have hd2 : (Node.access (twoBranchTreeMR (.Unprot .Frozen)) (some [1]) .Read
        ⟨0⟩ ⟨4⟩).toOption.map (fun t => (nodeAt t [0]).map (·.permissions)) =
        some (some (List.replicate 4 (.Unprot .Frozen))) := by
      decide +kernel
    have hacc' : Node.access (twoBranchTreeMR (.Unprot .Frozen)) (some [1]) .Read ⟨0⟩ ⟨4⟩ =
        .ok t' := hacc
    rw [hw'] at hd1
    rw [hacc'] at hd2
    exact ⟨w', t', hw', hacc', hinv', Option.some.inj hd1, Option.some.inj hd2⟩
  · obtain ⟨w', hw'⟩ := nwsr_exists_ok_of_isOk
      (r := execWorldRangeWrite (mkTwoBranchWorld .unique .frozen) 1 0 4) (by decide +kernel)
    obtain ⟨t', hacc, hinv'⟩ := hw1 w' hw'
    have hd1 : (execWorldRangeWrite (mkTwoBranchWorld .unique .frozen) 1 0 4).toOption.map
        (fun w => (findNode? w.nodes 2).map (·.perm)) = some (some .disabled) := by
      decide +kernel
    have hd2 : (Node.access (twoBranchTreeMR (.Unprot .Frozen)) (some [0]) .Write
        ⟨0⟩ ⟨4⟩).toOption.map (fun t => (nodeAt t [1]).map (·.permissions)) =
        some (some (List.replicate 4 (.Unprot .Disabled))) := by
      decide +kernel
    have hacc' : Node.access (twoBranchTreeMR (.Unprot .Frozen)) (some [0]) .Write ⟨0⟩ ⟨4⟩ =
        .ok t' := hacc
    rw [hw'] at hd1
    rw [hacc'] at hd2
    exact ⟨w', t', hw', hacc', hinv', Option.some.inj hd1, Option.some.inj hd2⟩

/-! ## Part 5: `#[rustc_no_writable]` Edge Cases on Real `TreeBorrowsMemory` Operations (`charon#1619` + `minirust#295`) -/

/-! ### 5.1 Edge-Case Separations & Whole-State Relational Lockstep -/

/-- MiniRust `PointeeInfo` for the slice `[u32]` (element size `4`, `Freeze`, `Unpin`). -/
def sliceU32PointeeInfoMR : Gen.PointeeInfo :=
  { layout := .Slice ⟨4⟩ ⟨4⟩
    inhabited := true
    unsafe_cells := .Slice []
    freeze := true
    unpin := true }

/-- `<[u32]>::get_mut`-style `TBM` trace on a 2-element slice `[11u32, 22u32]`:
the caller holds `self : &mut [u32]` (wide pointer, `ElementCount 2`) and a
`.Frozen` sibling `&[u32]` over the SAME slice; the callee retags `self` at
`FnEntry` (`fnImplicitWrites`), sub-borrows element `1` (`&mut self[1]`,
bytes `[4, 8)`), optionally writes `99` through the sub-borrow, and returns
(`end_call`). After the call the caller reads element `readElem` through the
`.Frozen` sibling. -/
def tbmSliceGetMutTrace (fnImplicitWrites calleeWritesElem1 : Bool) (readElem : Nat) :
    Interp (List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨8⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 11 ++ tbU32Bytes 22) ⟨4⟩
  let slicePtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
    { thin_pointer := rootThin, metadata := some (.ElementCount 2) }
  let (parentPtr, tbm3, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 slicePtr (.Ref .Mutable sliceU32PointeeInfoMR)
      false true nwsrVtableLookup
  let (sibPtr, tbm4, _) ←
    TreeBorrowsMemory.retag_ptr tbm3 frame1 slicePtr (.Ref .Immutable sliceU32PointeeInfoMR)
      false true nwsrVtableLookup
  let calleeFrame := TreeBorrowsMemory.new_call
  let (selfPtr, tbm5, calleeFrame1) ←
    TreeBorrowsMemory.retag_ptr tbm4 calleeFrame parentPtr (.Ref .Mutable sliceU32PointeeInfoMR)
      true fnImplicitWrites nwsrVtableLookup
  let elem1Thin : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
    { selfPtr.thin_pointer with addr := selfPtr.thin_pointer.addr + 4 }
  let (elemPtr, tbm6, calleeFrame2) ←
    TreeBorrowsMemory.retag_ptr tbm5 calleeFrame1 { thin_pointer := elem1Thin, metadata := none }
      (refPtrType .mut u32ItMR) false fnImplicitWrites nwsrVtableLookup
  let tbm7 ←
    if calleeWritesElem1 then TreeBorrowsMemory.store tbm6 elemPtr.thin_pointer (tbU32Bytes 99) ⟨4⟩
    else pure tbm6
  let tbm8 ← TreeBorrowsMemory.end_call tbm7 calleeFrame2
  let sibElemThin : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
    { sibPtr.thin_pointer with addr := sibPtr.thin_pointer.addr + 4 * (readElem : Int) }
  let (bs, tbm9) ← TreeBorrowsMemory.load tbm8 sibElemThin ⟨4⟩ ⟨4⟩
  let _ := tbm9
  pure bs

/-- Coarse-range Anneal world for the `get_mut` slice pattern: root `0`, caller
`&mut [u32]` `1`, and `.frozen` sibling `2`, each covering the whole slice `[0, 8)`. -/
def sliceGetMutWorld : FnEntryBorrowWorld where
  nodes := [
    ⟨0, none, .unique, 0, 8, none, true⟩,
    ⟨1, some 0, .reservedFrz false, 0, 8, none, true⟩,
    ⟨2, some 0, .frozen, 0, 8, none, true⟩
  ]
  activeProtectors := []
  nextTag := 3
  nextProtector := 10

/-- Anneal counterpart of `tbmSliceGetMutTrace`: `FnEntry` retag of the whole slice
`[0, 8)` through `1` under `policy`, optional callee write of element `1`
(`[4, 8)`) through the fresh child `3`, MiniRust-order frame exit, and a caller
read of element `readElem` through the `.frozen` sibling `2`. -/
def sliceGetMutWorldTrace (policy : FnEntryRetagPolicy) (calleeWritesElem1 : Bool)
    (readElem : Nat) : Except RetagStepErr FnEntryBorrowWorld := do
  let (w1, cTag) ← execFnEntryMutRetagPrunedSourceOrder sliceGetMutWorld 1 0 8 policy false
  let w2 ← if calleeWritesElem1 then execWorldRangeWrite w1 cTag 4 4 else pure w1
  let w3 ← execFrameExitMiniRust w2 [(cTag, 10)]
  execWorldRangeRead w3 2 (4 * readElem) 4

/-- Decidable error projection of an Anneal world trace. -/
def worldErr? {α : Type} (r : Except RetagStepErr α) : Option RetagStepErr :=
  match r with
  | .ok _ => none
  | .error e => some e

/-- `TBM` state with a single live 8-byte allocation at address `256` carrying an
explicitly given borrow tree `root` (used to run the real `TreeBorrowsMemory`
operations on borrow-tree states that mirror hand-built `FnEntryBorrowWorld`s). -/
def mkTbmWithTree (root : Gen.Node) : Gen.TreeBorrowsMemory Gen.x86_64 :=
  { params := ⟨true⟩
    mem := {
      allocations := [{
        data := tbU32Bytes 1 ++ tbU32Bytes 2
        addr := 256
        align := ⟨4⟩
        kind := .Stack
        live := true
        extra := { root := root } }]
      _phantom := ⟨⟩ } }

/-- Thin pointer into `mkTbmWithTree`'s allocation with borrow-tree path `path`. -/
def tbmTreePtr (path : Gen.Path) : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
  { addr := 256, provenance := some (⟨0⟩, path) }

/-- Tag-to-path embedding shared by the frame-exit separation worlds
(`0 ↦ []`, `1 ↦ [0]`, `2 ↦ [0, 0]` for the nested world; see `exitImplicitEmb`
for the sibling world). -/
def exitOrderEmb : Nat → Gen.Path
  | 0 => []
  | 1 => [0]
  | 2 => [0, 0]
  | _ => [7]

/-- World of `execFrameExit_miri_vs_sequential_separation`: root `0`; protected
accessed CONFLICTED `.reservedFrz true` node `1` (protector `8`); its protected
accessed `.unique` child `2` (protector `7`); all on `[0, 8)`. -/
def exitOrderWorld : FnEntryBorrowWorld where
  nodes := [
    ⟨2, some 1, .unique, 0, 8, some 7, true⟩,
    ⟨1, some 0, .reservedFrz true, 0, 8, some 8, true⟩,
    ⟨0, none, .unique, 0, 8, none, true⟩
  ]
  activeProtectors := [7, 8]
  nextTag := 3
  nextProtector := 9

/-- MiniRust borrow tree mirroring `exitOrderWorld`: root `[]`
(`.Unprot .Unique`), strongly protected `[0]` (`.Prot (.Reserved true true)`),
and its strongly protected child `[0, 0]` (`.Prot .Unique`). -/
def exitOrderTreeMR : Gen.Node :=
  ⟨[⟨[⟨[], List.replicate 8 (.Prot .Unique), .Strong⟩],
      List.replicate 8 (.Prot (.Reserved true true)), .Strong⟩],
    List.replicate 8 (.Unprot .Unique), .No⟩

/-- Tag-to-path embedding of `exitImplicitWorld` (`0 ↦ []`, `1 ↦ [0]`,
`2 ↦ [1]`, `3 ↦ [0, 0]`). -/
def exitImplicitEmb : Nat → Gen.Path
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [0, 0]
  | _ => [7]

/-- World of `execReleaseProtector_implicitAccess_separation`: root `0`;
protected accessed `.unique` node `1` (protector `7`); its `.reservedFrz` sibling
`2` (protected by the still-active protector `sibProt` when given); and `1`'s own
unprotected `.reservedFrz` child `3`; all on `[0, 8)`. -/
def exitImplicitWorld (sibProt : Option Nat) : FnEntryBorrowWorld where
  nodes := [
    ⟨3, some 1, .reservedFrz false, 0, 8, none, true⟩,
    ⟨2, some 0, .reservedFrz false, 0, 8, sibProt, true⟩,
    ⟨1, some 0, .unique, 0, 8, some 7, true⟩,
    ⟨0, none, .unique, 0, 8, none, true⟩
  ]
  activeProtectors := match sibProt with | some p => [7, p] | none => [7]
  nextTag := 4
  nextProtector := 8

/-- MiniRust borrow tree mirroring `exitImplicitWorld`. -/
def exitImplicitTreeMR (sibProtected : Bool) : Gen.Node :=
  ⟨[⟨[⟨[], List.replicate 8 (.Unprot .Reserved), .No⟩],
      List.replicate 8 (.Prot .Unique), .Strong⟩,
    ⟨[], List.replicate 8
        (if sibProtected then .Prot (.Reserved true false) else .Unprot .Reserved),
      if sibProtected then .Strong else .No⟩],
    List.replicate 8 (.Unprot .Unique), .No⟩

/-- Anneal world after `stage` steps of the `#[rustc_no_writable]` conflict
lifecycle on the two-branch world (parent `1` `.reservedFrz false`, `.frozen`
sibling `2`): `0` initial; `1` after the `FnEntry` retag through `1` (child `3`);
`2` after a foreign read through sibling `2`; `3` after the MiniRust-order frame
exit; `4` after a write through the unprotected child `3`. -/
def noWritableLifecycleWorldAt : Nat → Except RetagStepErr FnEntryBorrowWorld
  | 0 => .ok (mkTwoBranchWorld (.reservedFrz false) .frozen)
  | 1 =>
    (execFnEntryMutRetagPrunedSourceOrder (mkTwoBranchWorld (.reservedFrz false) .frozen)
      1 0 4 .rustcNoWritable false).map (·.1)
  | 2 => noWritableLifecycleWorldAt 1 >>= fun w => execWorldRangeRead w 2 0 4
  | 3 => noWritableLifecycleWorldAt 2 >>= fun w => execFrameExitMiniRust w [(3, 10)]
  | _ + 4 => noWritableLifecycleWorldAt 3 >>= fun w => execWorldRangeWrite w 3 0 4

/-- MiniRust `TBM` state after `stage` steps of the same lifecycle on real
`TreeBorrowsMemory` operations (`retag_ptr`, `load`, `end_call`, `store`). -/
def noWritableLifecycleTbmAt (stage : Nat) : Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let (_, parentPtr, sibPtr, tbm0) ← mkTbmTwoBranchSetup true
  match stage with
  | 0 => pure tbm0
  | stage + 1 =>
    let (childPtr, tbm1, frame1) ←
      TreeBorrowsMemory.retag_ptr tbm0 TreeBorrowsMemory.new_call parentPtr
        (refPtrType .mut u32ItMR) true false nwsrVtableLookup
    match stage with
    | 0 => pure tbm1
    | stage + 1 =>
      let (_, tbm2) ← TreeBorrowsMemory.load tbm1 sibPtr.thin_pointer ⟨4⟩ ⟨4⟩
      match stage with
      | 0 => pure tbm2
      | stage + 1 =>
        let tbm3 ← TreeBorrowsMemory.end_call tbm2 frame1
        match stage with
        | 0 => pure tbm3
        | _ + 1 => TreeBorrowsMemory.store tbm3 childPtr.thin_pointer (tbU32Bytes 99) ⟨4⟩

/-- Anneal world after `stage` steps of the standard `&mut` (`writableChildWrite`)
lifecycle: `1` after the `FnEntry` retag (implicit child write), `2` after the
MiniRust-order frame exit (implicit protector-end WRITE). -/
def writableLifecycleWorldAt : Nat → Except RetagStepErr FnEntryBorrowWorld
  | 0 => .ok (mkTwoBranchWorld (.reservedFrz false) .frozen)
  | 1 =>
    (execFnEntryMutRetagPrunedSourceOrder (mkTwoBranchWorld (.reservedFrz false) .frozen)
      1 0 4 .writableChildWrite false).map (·.1)
  | _ + 2 => writableLifecycleWorldAt 1 >>= fun w => execFrameExitMiniRust w [(3, 10)]

/-- MiniRust `TBM` state after `stage` steps of the standard `&mut` lifecycle. -/
def writableLifecycleTbmAt (stage : Nat) : Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let (_, parentPtr, _, tbm0) ← mkTbmTwoBranchSetup true
  match stage with
  | 0 => pure tbm0
  | stage + 1 =>
    let (_, tbm1, frame1) ←
      TreeBorrowsMemory.retag_ptr tbm0 TreeBorrowsMemory.new_call parentPtr
        (refPtrType .mut u32ItMR) true true nwsrVtableLookup
    match stage with
    | 0 => pure tbm1
    | _ + 1 => TreeBorrowsMemory.end_call tbm1 frame1

/-- Anneal world after `stage` steps of an `FnEntry` retag against a strongly
PROTECTED `.frozen` sibling (protector `5`, held by an outer frame): `0` initial;
`1` after the retag through `1` under `policy`; `2` after the frame exit. -/
def protectedSiblingWorldAt (policy : FnEntryRetagPolicy) :
    Nat → Except RetagStepErr FnEntryBorrowWorld
  | 0 => .ok (mkTwoBranchWorld (.reservedFrz false) .frozen (some 5))
  | 1 =>
    (execFnEntryMutRetagPrunedSourceOrder
      (mkTwoBranchWorld (.reservedFrz false) .frozen (some 5)) 1 0 4 policy false).map (·.1)
  | _ + 2 => protectedSiblingWorldAt policy 1 >>= fun w => execFrameExitMiniRust w [(3, 10)]

/-- MiniRust `TBM` state after `stage` steps of the same scenario: the sibling is
a `Protected::Strong` shared `FnEntry` retag held by an outer frame
(`.Prot (.Frozen true)`), and the inner `&mut u32` `FnEntry` retag uses
`fnImplicitWrites`. -/
def protectedSiblingTbmAt (fnImplicitWrites : Bool) (stage : Nat) :
    Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let outerFrame := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Stack ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 42) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance := { thin_pointer := rootThin, metadata := none }
  let (parentPtr, tbm3, outerFrame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 outerFrame rootPtr (refPtrType .mut u32ItMR) false true nwsrVtableLookup
  let (_, tbm4, _) ←
    TreeBorrowsMemory.retag_ptr tbm3 outerFrame1 rootPtr (refPtrType .not u32ItMR) true true nwsrVtableLookup
  match stage with
  | 0 => pure tbm4
  | stage + 1 =>
    let (_, tbm5, innerFrame1) ←
      TreeBorrowsMemory.retag_ptr tbm4 TreeBorrowsMemory.new_call parentPtr
        (refPtrType .mut u32ItMR) true fnImplicitWrites nwsrVtableLookup
    match stage with
    | 0 => pure tbm5
    | _ + 1 => TreeBorrowsMemory.end_call tbm5 innerFrame1

/-- Read-only mirror of the two-branch world (`allocReadOnly := true`). -/
def readOnlyTwoBranchWorld : FnEntryBorrowWorld :=
  { mkTwoBranchWorld (.reservedFrz false) .frozen with allocReadOnly := true }

/-- `TBM` trace: standard `&mut u32` `FnEntry` retag (implicit child write) into a
`.Global` allocation followed by `end_call`. MiniRust's `TreeBorrowsMemory` carries
no allocation mutability, so the implicit write is accepted. -/
def tbmGlobalWritableFnEntryTrace : Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Global ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 42) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance := { thin_pointer := rootThin, metadata := none }
  let (_, tbm3, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 TreeBorrowsMemory.new_call rootPtr
      (refPtrType .mut u32ItMR) true true nwsrVtableLookup
  TreeBorrowsMemory.end_call tbm3 frame1

/-- Generic two-function `MachTB` harness: `callerFn` (`fnName 0`, entered at
`bbName 0` with return slot `allocations[0]`) calling `calleeFn` (`fnName 1`). -/
def mkTwoFnMachTB (callerFn calleeFn : Gen.Function) : MachTB :=
  let prog : Gen.Program := {
    functions := ⟨[(fnName 0, callerFn), (fnName 1, calleeFn)]⟩
    start := fnName 0
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩
  }
  let retAlloc := mkRootAllocTB (List.replicate 4 .Uninit) 128 4 .Stack
  let fnAlloc := mkRootAllocTB [.Uninit] 64 1 .Function
  let loc0Alloc := mkRootAllocTB (List.replicate 4 .Uninit) 512 4 .Stack
  let mainFrame : Gen.StackFrame TBM := {
    func := callerFn
    locals := ⟨[(localName 0, { addr := 512, provenance := some (⟨2⟩, []) })]⟩
    stack_pop_action := .BackToCaller (some (bbName 1)) none
      { addr := 128, provenance := some (⟨0⟩, []) }
    next_block := bbName 0
    next_stmt := 0
    extra := TreeBorrowsMemory.new_call
  }
  { prog := prog
    mem := {
      memory := {
        params := ⟨true⟩
        mem := { allocations := [retAlloc, fnAlloc, loc0Alloc], _phantom := ⟨⟩ }
      }
      accesses := []
    }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [nwsrSentinelFrame, mainFrame], state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[(fnName 1, { addr := 64, provenance := some (⟨1⟩, []) })]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- Callee taking `_1 : &mut u32` and a `.Frozen` sibling `_2 : &u32` to the SAME
place. It first retags `_2` at `FnEntry` (`Protected::Strong` `.Frozen`), then
retags `_1` at `FnEntry` under `Function.implicit_writes := fnImplicitWrites`,
reads `*_2`, and returns it. -/
def protectedSiblingCalleeFn (fnImplicitWrites : Bool) : Gen.Function where
  locals := ⟨[
    (localName 0, u32TyMR),
    (localName 1, refTy .mut u32ItMR),
    (localName 2, refTy .not u32ItMR)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Validate (.Local (localName 2)) true,
      .Validate (.Local (localName 1)) true,
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 2))) u32TyMR))],
      .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := fnImplicitWrites

/-- Caller creating `_1 = 42u32`, `_2 = &mut _1`, `_3 = &_1`, calling
`protectedSiblingCalleeFn` with `(_2, _3)`, and returning the callee's result. -/
def protectedSiblingCallerFn : Gen.Function where
  locals := ⟨[
    (localName 0, u32TyMR),
    (localName 1, u32TyMR),
    (localName 2, refTy .mut u32ItMR),
    (localName 3, refTy .not u32ItMR),
    (localName 4, u32TyMR)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .StorageLive (localName 4),
      .Assign (.Local (localName 1)) (.Constant (.Int 42) u32TyMR),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32ItMR)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 1)) (refPtrType .not u32ItMR))],
      .Call (.Constant (.FnPointer (fnName 1)) (.Ptr .FnPtr)) .Rust
        [.ByValue (.Load (.Local (localName 2))),
         .ByValue (.Load (.Local (localName 3)))]
        (.Local (localName 4)) (some (bbName 1)) none,
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 4)))],
      .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := true

/-- **`<[T]>::get_mut` slice pattern on real `TreeBorrowsMemory` (wide `&mut [u32]`,
`ElementCount 2`)**: a `.Frozen` sibling `&[u32]` over the SAME slice
1. survives BOTH the `#[rustc_no_writable]` callee entry AND `end_call` on every
   element the callee did not write: after the callee sub-borrows and writes only
   element `1`, the sibling still reads element `0` (`11`), while element `1` is
   (byte-precisely) `Disabled`;
2. survives on the WHOLE slice when the callee returns without writing;
3. whereas the standard `&mut [T]` `FnEntry` (implicit write) disables the sibling
   across the ENTIRE slice at entry, even when the callee never writes. -/
theorem tbm_sliceGetMut_noWritable_vs_writable :
    tbBytesOutcome (tbmSliceGetMutTrace false true 0) =
      some (.inl [some 11, some 0, some 0, some 0]) ∧
    tbBytesOutcome (tbmSliceGetMutTrace false true 1) =
      some (.inr "Tree Borrows: local read of Disabled reference") ∧
    tbBytesOutcome (tbmSliceGetMutTrace false false 0) =
      some (.inl [some 11, some 0, some 0, some 0]) ∧
    tbBytesOutcome (tbmSliceGetMutTrace false false 1) =
      some (.inl [some 22, some 0, some 0, some 0]) ∧
    tbBytesOutcome (tbmSliceGetMutTrace true false 0) =
      some (.inr "Tree Borrows: local read of Disabled reference") ∧
    tbBytesOutcome (tbmSliceGetMutTrace true false 1) =
      some (.inr "Tree Borrows: local read of Disabled reference") ∧
    tbBytesOutcome (tbmSliceGetMutTrace true true 0) =
      some (.inr "Tree Borrows: local read of Disabled reference") :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Anneal coarse-range world vs. MiniRust per-byte permissions on the
`get_mut` slice pattern**: `sliceGetMutWorldTrace` agrees with
`tbmSliceGetMutTrace` whenever the callee does not write
(`#[rustc_no_writable]`: sibling survives; standard `&mut`: sibling disabled) and
on the written element. But a `TreeTagNode` carries ONE permission for its whole
range, so the callee's write of element `1` disables the entire coarse sibling
`[0, 8)`: the Anneal world reports `.disabledParentTag 2` for the sibling's read of
the UNWRITTEN element `0`, which real per-byte `TreeBorrowsMemory` accepts
(`11`). The coarse-range world therefore OVER-approximates UB on sub-range writes
— exactly the case excluded by `TreeSimInv.overlap` / the byte window of
`tree_write_simulates_node_access`. -/
theorem sliceGetMut_world_agreement_and_coarse_range_overapproximation :
    worldErr? (sliceGetMutWorldTrace .rustcNoWritable false 0) = none ∧
    worldErr? (sliceGetMutWorldTrace .rustcNoWritable false 1) = none ∧
    worldErr? (sliceGetMutWorldTrace .writableChildWrite false 0) = some (.disabledParentTag 2) ∧
    worldErr? (sliceGetMutWorldTrace .writableChildWrite false 1) = some (.disabledParentTag 2) ∧
    worldErr? (sliceGetMutWorldTrace .rustcNoWritable true 1) = some (.disabledParentTag 2) ∧
    (worldErr? (sliceGetMutWorldTrace .rustcNoWritable true 0) = some (.disabledParentTag 2) ∧
      tbBytesOutcome (tbmSliceGetMutTrace false true 0) =
        some (.inl [some 11, some 0, some 0, some 0])) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Overlapping-range multi-parameter frame exit: order separation on real
`TreeBorrowsMemory.end_call`** (the world of
`execFrameExit_miri_vs_sequential_separation`, hand-built on both sides because
it is unreachable upstream): with frame order `[1, 2]`,
1. MiniRust's sequential `end_call` SUCCEEDS and its post-state is
   `TreeSimInv`-related to `execFrameExitMiniRust`'s (node `1` becomes `.unique` /
   `.Unprot .Unique` through child `2`'s implicit WRITE);
2. the pinned-Miri order (all protector-end accesses before any pop) is UB
   (`.conflictedProtectedChildWrite 1`);
3. `end_call` itself is order-sensitive: releasing in the reversed order `[2, 1]`
   is UB on real `TreeBorrowsMemory.end_call` and in BOTH Anneal exit models. -/
theorem tbm_endCall_overlapping_frame_order_separation :
    TreeSimInv 0 8 exitOrderEmb exitOrderWorld exitOrderTreeMR ∧
    (∃ w tbm t, execFrameExitMiniRust exitOrderWorld [(1, 8), (2, 7)] = .ok w ∧
      TreeBorrowsMemory.end_call (mkTbmWithTree exitOrderTreeMR)
        ⟨[(⟨0⟩, [0]), (⟨0⟩, [0, 0])]⟩ = .ok tbm ∧
      tbmRootOf tbm 0 = some t ∧ TreeSimInv 0 8 exitOrderEmb w t) ∧
    ((execFrameExitMiniRust exitOrderWorld [(1, 8), (2, 7)]).toOption.map
        (fun w => ((findNode? w.nodes 1).map (·.perm), w.activeProtectors)) =
      some (some .unique, [])) ∧
    worldErr? (execFrameExitMiri exitOrderWorld [(1, 8), (2, 7)]) =
      some (.conflictedProtectedChildWrite 1) ∧
    worldErr? (execFrameExitMiniRust exitOrderWorld [(2, 7), (1, 8)]) =
      some (.conflictedProtectedChildWrite 1) ∧
    worldErr? (execFrameExitMiri exitOrderWorld [(2, 7), (1, 8)]) =
      some (.conflictedProtectedChildWrite 1) ∧
    tbUnitOutcome (TreeBorrowsMemory.end_call (mkTbmWithTree exitOrderTreeMR)
        ⟨[(⟨0⟩, [0, 0]), (⟨0⟩, [0])]⟩) =
      some (.inr "Tree Borrows: local write to protected Reserved reference that had a foreign read") :=
  ⟨treeSimInv_of_bool _ _ _ _ _ (by decide +kernel),
   tbmWorldRel_of_bool (by decide +kernel),
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel⟩

/-- **Implicit protector-end access separation on real
`TreeBorrowsMemory.end_call`** (the world of
`execReleaseProtector_implicitAccess_separation`):
1. releasing the protected `.unique` / `.Prot .Unique` node `1` performs an
   implicit WRITE: its `.reservedFrz` sibling `2` is disabled while `1`'s own child
   `3` is untouched (`SkipChildrenOfAccessed` / `Node::release_protector` returns at
   the protected node), in `TreeSimInv`-related post-states, identically for the
   Miri and MiniRust exit orders;
2. an explicit `TreeBorrowsMemory.store` through `1` ALSO disables child `3`
   (again `TreeSimInv`-related to `execWorldRangeWrite`), so the release is
   observably different from an ordinary write;
3. if sibling `2` is protected by a still-active strong protector, the release is
   UB on both sides. -/
theorem tbm_endCall_implicit_protectorEnd_access_separation :
    TreeSimInv 0 8 exitImplicitEmb (exitImplicitWorld none) (exitImplicitTreeMR false) ∧
    (∃ w tbm t, execFrameExitMiniRust (exitImplicitWorld none) [(1, 7)] = .ok w ∧
      TreeBorrowsMemory.end_call (mkTbmWithTree (exitImplicitTreeMR false))
        ⟨[(⟨0⟩, [0])]⟩ = .ok tbm ∧
      tbmRootOf tbm 0 = some t ∧ TreeSimInv 0 8 exitImplicitEmb w t) ∧
    ((execFrameExitMiniRust (exitImplicitWorld none) [(1, 7)]).toOption.map
        (fun w => ((findNode? w.nodes 2).map (·.perm), (findNode? w.nodes 3).map (·.perm))) =
      some (some .disabled, some (.reservedFrz false))) ∧
    execFrameExitMiniRust (exitImplicitWorld none) [(1, 7)] =
      execFrameExitMiri (exitImplicitWorld none) [(1, 7)] ∧
    (∃ w tbm t, execWorldRangeWrite (exitImplicitWorld none) 1 0 8 = .ok w ∧
      TreeBorrowsMemory.store (mkTbmWithTree (exitImplicitTreeMR false)) (tbmTreePtr [0])
        (tbU32Bytes 5 ++ tbU32Bytes 6) ⟨4⟩ = .ok tbm ∧
      tbmRootOf tbm 0 = some t ∧ TreeSimInv 0 8 exitImplicitEmb w t) ∧
    ((execWorldRangeWrite (exitImplicitWorld none) 1 0 8).toOption.map
        (fun w => ((findNode? w.nodes 2).map (·.perm), (findNode? w.nodes 3).map (·.perm))) =
      some (some .disabled, some .disabled)) ∧
    TreeSimInv 0 8 exitImplicitEmb (exitImplicitWorld (some 5)) (exitImplicitTreeMR true) ∧
    worldErr? (execFrameExitMiniRust (exitImplicitWorld (some 5)) [(1, 7)]) =
      some (.protectedForeignConflict 2) ∧
    tbUnitOutcome (TreeBorrowsMemory.end_call (mkTbmWithTree (exitImplicitTreeMR true))
        ⟨[(⟨0⟩, [0])]⟩) =
      some (.inr "Tree Borrows: foreign write of protected Reserved reference which had a local read") :=
  ⟨treeSimInv_of_bool _ _ _ _ _ (by decide +kernel),
   tbmWorldRel_of_bool (by decide +kernel),
   by decide +kernel,
   execFrameExit_miri_eq_miniRust_singleton (exitImplicitWorld none) 1 7
     ⟨1, some 0, .unique, 0, 8, some 7, true⟩ rfl (by decide) (fun _ => rfl),
   tbmWorldRel_of_bool (by decide +kernel),
   by decide +kernel,
   treeSimInv_of_bool _ _ _ _ _ (by decide +kernel),
   by decide +kernel, by decide +kernel⟩

/-- **Whole-state relational lockstep of the `ReservedFrz { conflicted: true }`
lifecycle under `#[rustc_no_writable]`**: at EVERY stage — initial state, after
the `FnEntry` retag (`execFnEntryMutRetagPrunedSourceOrder` ↔
`TreeBorrowsMemory.retag_ptr`), after the foreign read that latches the conflict
(`execWorldRangeRead` ↔ `TreeBorrowsMemory.load`), after the frame exit
(`execFrameExitMiniRust` ↔ `TreeBorrowsMemory.end_call`), and after the
post-exit child write (`execWorldRangeWrite` ↔ `TreeBorrowsMemory.store`) — the
Anneal world and the borrow tree of the real MiniRust memory are
`TreeSimInv`-related across ALL nodes. In particular:
- during the call the protected child is conflicted on both sides
  (`.reservedFrz true` ↔ `.Prot (.Reserved true true)`) and a local child write
  faults on both sides;
- after `end_call` (implicit READ) the child is unprotected (`.Unprot .Reserved`);
- the subsequent child write activates it (`.unique` ↔ `.Unprot .Unique`) and
  disables the sibling. -/
theorem noWritable_conflicted_lifecycle_relational_lockstep :
    (∀ stage, stage ≤ 4 → ∃ w tbm t, noWritableLifecycleWorldAt stage = .ok w ∧
      noWritableLifecycleTbmAt stage = .ok tbm ∧ tbmRootOf tbm 0 = some t ∧
      TreeSimInv 0 4 twoBranchEmb w t) ∧
    ((noWritableLifecycleWorldAt 2).toOption.map (fun w => (findNode? w.nodes 3).map
        (fun n => (n.perm, n.isProtected w.activeProtectors))) =
      some (some (.reservedFrz true, true))) ∧
    ((noWritableLifecycleTbmAt 2).toOption.bind (fun tbm => (tbmRootOf tbm 0).bind
        (fun t => (nodeAt t [0, 0]).map (·.permissions))) =
      some (List.replicate 4 (.Prot (.Reserved true true)))) ∧
    worldErr? (noWritableLifecycleWorldAt 2 >>= fun w => execWorldRangeWrite w 3 0 4) =
      some (.conflictedProtectedChildWrite 3) ∧
    tbUnitOutcome tbmNoWritableConflictedLocalWriteUbTrace =
      some (.inr "Tree Borrows: local write to protected Reserved reference that had a foreign read") ∧
    ((noWritableLifecycleWorldAt 3).toOption.map (fun w => (findNode? w.nodes 3).map
        (fun n => (n.perm, n.isProtected w.activeProtectors))) =
      some (some (.reservedFrz true, false))) ∧
    ((noWritableLifecycleTbmAt 3).toOption.bind (fun tbm => (tbmRootOf tbm 0).bind
        (fun t => (nodeAt t [0, 0]).map (·.permissions))) =
      some (List.replicate 4 (.Unprot .Reserved))) ∧
    ((noWritableLifecycleWorldAt 4).toOption.map (fun w =>
        ((findNode? w.nodes 3).map (·.perm), (findNode? w.nodes 2).map (·.perm))) =
      some (some .unique, some .disabled)) ∧
    ((noWritableLifecycleTbmAt 4).toOption.bind (fun tbm => (tbmRootOf tbm 0).bind
        (fun t => (nodeAt t [0, 0]).map (·.permissions))) =
      some (List.replicate 4 (.Unprot .Unique))) := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro stage hstage
  match stage, hstage with
  | 0, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | 1, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | 2, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | 3, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | 4, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | n + 5, h => exact absurd h (by omega)

/-- **Whole-state relational lockstep of the standard `&mut` (`writableChildWrite`)
lifecycle**: the `FnEntry` retag with its implicit child write
(`execFnEntryMutRetagPrunedSourceOrder … .writableChildWrite` ↔
`TreeBorrowsMemory.retag_ptr … fnImplicitWrites := true`) and the frame exit with
its implicit protector-end WRITE keep the Anneal world and the real MiniRust
borrow tree `TreeSimInv`-related; the `.frozen` sibling is disabled at entry on
both sides, and its read after the call is an error on both sides. -/
theorem writable_lifecycle_relational_lockstep :
    (∀ stage, stage ≤ 2 → ∃ w tbm t, writableLifecycleWorldAt stage = .ok w ∧
      writableLifecycleTbmAt stage = .ok tbm ∧ tbmRootOf tbm 0 = some t ∧
      TreeSimInv 0 4 twoBranchEmb w t) ∧
    ((writableLifecycleWorldAt 1).toOption.map (fun w =>
        ((findNode? w.nodes 3).map (·.perm), (findNode? w.nodes 2).map (·.perm))) =
      some (some .unique, some .disabled)) ∧
    worldErr? (writableLifecycleWorldAt 2 >>= fun w => execWorldRangeRead w 2 0 4) =
      some (.disabledParentTag 2) ∧
    tbBytesOutcome tbmWritableDisablesFrozenSiblingUbTrace =
      some (.inr "Tree Borrows: local read of Disabled reference") := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro stage hstage
  match stage, hstage with
  | 0, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | 1, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | 2, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | n + 3, h => exact absurd h (by omega)

/-- **Foreign active strong protector on overlapping bytes (whole-state relational
lockstep)**: against a `Protected::Strong` `.frozen` / `.Prot (.Frozen true)`
sibling held by an outer frame,
1. `#[rustc_no_writable]` succeeds at `FnEntry` AND at frame exit without ever
   triggering foreign-write protector UB, with `TreeSimInv`-related states at every
   stage;
2. standard `&mut` (`writableChildWrite`) faults AT the `FnEntry` reborrow on both
   sides (`.protectedForeignConflict 2` ↔
   `"Tree Borrows: foreign write of protected Frozen reference which had a local read"`). -/
theorem protectedSibling_noWritable_vs_writable_relational_lockstep :
    (∀ stage, stage ≤ 2 → ∃ w tbm t, protectedSiblingWorldAt .rustcNoWritable stage = .ok w ∧
      protectedSiblingTbmAt false stage = .ok tbm ∧ tbmRootOf tbm 0 = some t ∧
      TreeSimInv 0 4 twoBranchEmb w t) ∧
    (∃ w tbm t, protectedSiblingWorldAt .writableChildWrite 0 = .ok w ∧
      protectedSiblingTbmAt true 0 = .ok tbm ∧ tbmRootOf tbm 0 = some t ∧
      TreeSimInv 0 4 twoBranchEmb w t) ∧
    worldErr? (protectedSiblingWorldAt .writableChildWrite 1) =
      some (.protectedForeignConflict 2) ∧
    tbUnitOutcome (protectedSiblingTbmAt true 1) =
      some (.inr "Tree Borrows: foreign write of protected Frozen reference which had a local read") := by
  refine ⟨?_, tbmWorldRel_of_bool (by decide +kernel), by decide +kernel, by decide +kernel⟩
  intro stage hstage
  match stage, hstage with
  | 0, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | 1, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | 2, _ => exact tbmWorldRel_of_bool (by decide +kernel)
  | n + 3, h => exact absurd h (by omega)

/-- **Read-only allocation: `writableChildWrite` vs. `#[rustc_no_writable]` on
entry AND exit**: on a read-only allocation (`allocReadOnly := true`),
1. the standard `&mut` `FnEntry` retag is rejected with `.writeToReadOnlyAlloc`
   before any tree access by both the pruned source-order and the direct
   traversal-order models;
2. the `#[rustc_no_writable]` retag succeeds, and the frame exit of the (never
   written) protected child succeeds under BOTH the MiniRust and the pinned-Miri
   exit (implicit READ), preserving the `.frozen` sibling and popping the protector;
   the sibling remains readable;
3. an explicit write through the child during the call is still rejected
   (`.writeToReadOnlyAlloc`);
4. MiniRust's `TreeBorrowsMemory` carries no allocation mutability: the same
   standard `&mut` `FnEntry` retag into a `.Global` allocation is ACCEPTED on
   `TreeBorrowsMemory.retag_ptr` + `end_call`, so the read-only rejection is a
   Miri / rustc-interning check outside the MiniRust Tree Borrows memory. -/
theorem readOnlyAlloc_noWritable_entry_and_exit_vs_writable :
    worldErr? (execFnEntryMutRetagPrunedSourceOrder readOnlyTwoBranchWorld 1 0 4
      .writableChildWrite false) = some .writeToReadOnlyAlloc ∧
    worldErr? (execFnEntryMutRetagTraversalOrderDirect readOnlyTwoBranchWorld 1 0 4
      .writableChildWrite false) = some .writeToReadOnlyAlloc ∧
    worldErr? (execFnEntryMutRetagPrunedSourceOrder readOnlyTwoBranchWorld 1 0 4
      .rustcNoWritable false >>= fun r => execFrameExitMiniRust r.1 [(r.2, 10)]) = none ∧
    worldErr? (execFnEntryMutRetagPrunedSourceOrder readOnlyTwoBranchWorld 1 0 4
      .rustcNoWritable false >>= fun r => execFrameExitMiri r.1 [(r.2, 10)]) = none ∧
    worldErr? (execFnEntryMutRetagTraversalOrderDirect readOnlyTwoBranchWorld 1 0 4
      .rustcNoWritable false >>= fun r => execFrameExitMiniRust r.1 [(r.2, 10)]) = none ∧
    ((execFnEntryMutRetagPrunedSourceOrder readOnlyTwoBranchWorld 1 0 4
        .rustcNoWritable false >>= fun r => execFrameExitMiniRust r.1 [(r.2, 10)]).toOption.map
        (fun w => ((findNode? w.nodes 2).map (·.perm), (findNode? w.nodes 3).map (·.perm),
          w.activeProtectors, w.allocReadOnly)) =
      some (some .frozen, some (.reservedFrz false), [], true)) ∧
    worldErr? (execFnEntryMutRetagPrunedSourceOrder readOnlyTwoBranchWorld 1 0 4
      .rustcNoWritable false >>= fun r => execFrameExitMiniRust r.1 [(r.2, 10)] >>=
        fun w => execWorldRangeRead w 2 0 4) = none ∧
    worldErr? (execFnEntryMutRetagPrunedSourceOrder readOnlyTwoBranchWorld 1 0 4
      .rustcNoWritable false >>= fun r => execWorldRangeWrite r.1 r.2 0 4) =
      some .writeToReadOnlyAlloc ∧
    (∃ tbm, tbmGlobalWritableFnEntryTrace = .ok tbm ∧ TreeBorrowsMemory.wfLive tbm) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   tbm_trace_ok_and_wfLive_of_bool (by decide +kernel)⟩

/-! ### 5.2 Initial-State `MachTB.wfLive` of Every Execution Harness & Protected-Sibling `MachTB` Witness -/

/-- Any machine whose allocations are all built by `mkRootAllocTB` satisfies
`MachTB.wfLive`. -/
theorem machTB_wfLive_of_rootAllocs (m : MachTB)
    (h : ∀ alloc ∈ m.mem.memory.mem.allocations,
      ∃ data addr align kind, alloc = mkRootAllocTB data addr align kind) :
    MachTB.wfLive m := by
  intro alloc hmem _
  obtain ⟨data, addr, align, kind, rfl⟩ := h alloc hmem
  exact mkRootAllocTB_wf data addr align kind

private theorem nwsr_three_rootAllocs
    (d1 d2 d3 : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (a1 a2 a3 : Int)
    (l1 l2 l3 : Nat) (k1 k2 k3 : Gen.AllocationKind) :
    ∀ alloc ∈ [mkRootAllocTB d1 a1 l1 k1, mkRootAllocTB d2 a2 l2 k2, mkRootAllocTB d3 a3 l3 k3],
      ∃ data addr align kind, alloc = mkRootAllocTB data addr align kind := by
  intro alloc hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact ⟨_, _, _, _, rfl⟩
  · rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨_, _, _, _, rfl⟩
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨_, _, _, _, rfl⟩
      · cases hmem

/-- **Every execution harness of this file starts in a `MachTB.wfLive` machine** —
symbolically for all `#[rustc_no_writable]` / standard `&mut` / `!Unpin` variants,
all callee modes, all caller / callee functions of `mkTwoFnMachTB`, and ALL static
layouts, contents, write offsets, and write types of `mkStaticAccessMachTB`. The
post-state `MachTB.wfLive` facts of the witnesses are established by the
constructive checker `machTB_steps_ok_and_wfLive_of_bool`, because the general
preservation theorem `stepsTB_wfLive` depends on `Classical.choice`. -/
theorem machTB_harnesses_initial_wfLive :
    (∀ (mutPointee : Gen.PointeeInfo) (fnIw : Bool),
      MachTB.wfLive (mkForgetStyleMachTB mutPointee fnIw)) ∧
    (∀ (fnIw : Bool), MachTB.wfLive (mkForgetStyleUninitMachTB fnIw)) ∧
    (∀ (mode : NoWritableCalleeMode), MachTB.wfLive (mkNoWritableConflictMachTB mode)) ∧
    (∀ (callerFn calleeFn : Gen.Function), MachTB.wfLive (mkTwoFnMachTB callerFn calleeFn)) ∧
    (∀ (desc : StaticTyDesc) (sTy : Gen.Type) (align : Nat)
        (initBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (preserved : Bool)
        (writeOff : Int) (writeTy : Gen.Type) (writeVal : Int),
      MachTB.wfLive (mkStaticAccessMachTB desc sTy align initBytes preserved writeOff
        writeTy writeVal)) ∧
    MachTB.wfLive staticShapeBRepeatedWriteMachTB :=
  ⟨fun _ _ => machTB_wfLive_of_rootAllocs _ (nwsr_three_rootAllocs _ _ _ _ _ _ _ _ _ _ _ _),
   fun _ => machTB_wfLive_of_rootAllocs _ (nwsr_three_rootAllocs _ _ _ _ _ _ _ _ _ _ _ _),
   fun _ => machTB_wfLive_of_rootAllocs _ (nwsr_three_rootAllocs _ _ _ _ _ _ _ _ _ _ _ _),
   fun _ _ => machTB_wfLive_of_rootAllocs _ (nwsr_three_rootAllocs _ _ _ _ _ _ _ _ _ _ _ _),
   fun _ _ _ _ _ _ _ _ =>
     machTB_wfLive_of_rootAllocs _ (nwsr_three_rootAllocs _ _ _ _ _ _ _ _ _ _ _ _),
   machTB_wfLive_of_rootAllocs _ (nwsr_three_rootAllocs _ _ _ _ _ _ _ _ _ _ _ _)⟩

/-- **End-to-end `MachTB` witness: foreign active strong protector on overlapping
bytes** (two-parameter callee `f(x: &mut u32, y: &u32)` whose parameters alias):
- under `#[rustc_no_writable]` (`callee.implicit_writes = false`), both `FnEntry`
  retags succeed (2 protectors on the callee frame), the callee reads `*y = 42`,
  returns (releasing both protectors), and the program returns `42`, starting and
  ending in `MachTB.wfLive` machines;
- under standard `&mut` (`implicit_writes = true`), the `&mut` `FnEntry` retag's
  implicit write hits the strongly protected `.Frozen` parameter `y` and faults AT
  the reborrow (step 10) with
  `"Tree Borrows: foreign write of protected Frozen reference which had a local read"`. -/
theorem machTB_protectedSibling_noWritable_vs_writable_e2e :
    let mNoWr := mkTwoFnMachTB protectedSiblingCallerFn (protectedSiblingCalleeFn false)
    let mWr := mkTwoFnMachTB protectedSiblingCallerFn (protectedSiblingCalleeFn true)
    machTopProtectorCount mNoWr 10 = some 2 ∧
    machRetSnapshot mNoWr 14 = some (some (true, [some 42, some 0, some 0, some 0]), [1]) ∧
    MachTB.wfLive mNoWr ∧
    (∃ m', Interp.stepsTB 14 mNoWr = .ok m' ∧ MachTB.wfLive m') ∧
    machTopProtectorCount mWr 9 = some 1 ∧
    machStopOutcome mWr 10 =
      some (.ub "Tree Borrows: foreign write of protected Frozen reference which had a local read") :=
  ⟨by decide +kernel, by decide +kernel,
   machTB_harnesses_initial_wfLive.2.2.2.1 _ _,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel, by decide +kernel⟩

/-! ### 5.3 Faithful-Erasure Audits: `stepMirFnWithParamMap` Envelope & `permToMiniRust` Kernel -/

/-- **Envelope of the `stepMirFnWithParamMap` adapter**: for EVERY parameter map,
the adapter coincides with the real `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`
on every machine state whose current statement is not a `Retag([fn entry])` of a
parameter mapped to a non-`rustcNoWritable` policy. It can therefore differ from
`stepMirFn` ONLY at such `FnEntry` retags, where it delegates to
`evalFnEntryRetagWithParamMap`. (`stepMirFn` itself only implements the
no-implicit-write `FnEntry` retag, `fnEntryRetagPerm .mut = .reservedFrz false`, so
the `writableChildWrite` side of the `Trusted` separation necessarily runs through
this adapter.) -/
theorem stepMirFnWithParamMap_eq_stepMirFn_of_rustcNoWritable_at_pc
    (paramMap : FnParamRetagMap) (body : CapturedMir) (s : MachineState)
    (h : ∀ bb place span,
      Trusted.Sequence.get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx =
        some bb →
      Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
        some ⟨.retag .fnEntry place, span⟩ →
      paramMap.policyFor place.local_ = .rustcNoWritable) :
    stepMirFnWithParamMap paramMap body s = stepMirFn body s := by
  unfold stepMirFnWithParamMap stepMirFn
  dsimp only
  cases (s.memory.activeCallee.getD body).phase with
  | other _ => rfl
  | runtimePostCleanup | runtimeOptimized =>
    cases hbb : Trusted.Sequence.get? (s.memory.activeCallee.getD body).basicBlocks
        s.frame.blockIdx with
    | none => rfl
    | some bb =>
      simp only
      cases hst : Trusted.Sequence.get? bb.statements s.frame.stmtIdx with
      | none => rfl
      | some stmt =>
        rcases stmt with ⟨kind, span⟩
        cases kind with
        | retag rk place =>
          cases rk with
          | fnEntry =>
            exact evalFnEntryRetagWithParamMap_rustcNoWritable_eq_evalStmt paramMap s place span
              (s.memory.activeCallee.getD body).localDecls
              (s.memory.activeCallee.getD body).layouts (h bb place span hbb hst)
          | default | twoPhase | raw => rfl
        | nop | coverage | constEvalCounter | backwardIncompatibleDropHint _
        | placeMention _ | storageLive _ | storageDead _ | deinit _
        | intrinsic _ | setDiscriminant _ _ | assign _ _ => rfl

/-- The information about an Anneal `(isProtected, accessed, perm)` state that
`permToMiniRust` retains: the `conflicted` flag of an UNPROTECTED `.reservedFrz`
and the `accessed` flag outside protected `.reservedFrz` / `.frozen` are erased
(MiniRust's `PermissionUnprot::Reserved` has no conflict bit and only
`PermissionProt::{Reserved, Frozen}` track `had_local_read`). -/
def permErasure (isProt accessed : Bool) : TreeBorrowPerm → TreeBorrowPerm × Bool
  | .reservedFrz c => if isProt then (.reservedFrz c, accessed) else (.reservedFrz false, true)
  | .frozen => (.frozen, if isProt then accessed else true)
  | tp => (tp, true)

/-- **Exact kernel of `permToMiniRust`**: `permToMiniRust` is a surjection onto
`Gen.Permission` (`permToMiniRust_fromMiniRust`) but NOT a bijection — two Anneal
states of the same protection status have the same MiniRust image exactly when
they agree up to `permErasure`. -/
theorem permToMiniRust_eq_iff_permErasure (b a a' : Bool) (tp tp' : TreeBorrowPerm) :
    permToMiniRust b a tp = permToMiniRust b a' tp' ↔
      permErasure b a tp = permErasure b a' tp' := by
  cases b <;> cases a <;> cases a' <;> cases tp <;> cases tp' <;>
    first
      | decide
      | (rename_i c; cases c <;> decide)
      | (rename_i c c'; cases c <;> cases c' <;> decide)

/-- `permToMiniRust` identifies distinct Anneal states: an unprotected conflicted
and an unprotected unconflicted `.reservedFrz` share the image
`.Unprot .Reserved`, so `permFromMiniRust ∘ permToMiniRust` is not the identity. -/
theorem permToMiniRust_not_injective :
    permToMiniRust false true (.reservedFrz true) =
      permToMiniRust false false (.reservedFrz false) ∧
    (permFromMiniRust (.Unprot .Reserved)).1 = .reservedFrz false ∧
    (TreeBorrowPerm.reservedFrz true ≠ TreeBorrowPerm.reservedFrz false) :=
  ⟨rfl, rfl, by decide⟩

/-! ## Part 6: Symbolic Static-Retag Write Theorem on `TreeBorrowsMemory.retag_ptr` + `TreeBorrowsMemory.store` (`charon#1620`) -/

/-! ### 6.1 Symbolic Retag + Store on Arbitrary Static Layouts -/

/-- Symbolic single-allocation `TreeBorrowsMemory` state holding one live `.Global`
static allocation with arbitrary contents `data` at base address `addr`. -/
def staticTbm (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int)
    (align : Nat) : Gen.TreeBorrowsMemory Gen.x86_64 :=
  { params := ⟨true⟩
    mem := { allocations := [mkRootAllocTB data addr align .Global], _phantom := ⟨⟩ } }

/-- `staticTbm` after the preserved `#1620` shared temporary retag: the root keeps
`.Unprot .Unique` on every byte and gains one unprotected child `[0]` carrying the
per-byte `inside` permissions. -/
def staticTbmRetagged (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int)
    (align : Nat) (inside : List Gen.Permission) : Gen.TreeBorrowsMemory Gen.x86_64 :=
  { params := ⟨true⟩
    mem := {
      allocations := [{ mkRootAllocTB data addr align .Global with
        extra := { root := ⟨[⟨[], inside, .No⟩],
          List.replicate data.length (.Unprot .Unique), .No⟩ } }]
      _phantom := ⟨⟩ } }

private theorem nwsr_listMutateAt_zero_singleton {T O : Type} (x : T) (what : String)
    (f : T → Interp (O × T)) :
    listMutateAt [x] 0 what f = (f x >>= fun r => pure (r.1, [r.2])) :=
  nwsr_listMutateAt_natCast [x] 0 what f x rfl

private theorem nwsr_static_childPerms (outside : Gen.Permission) (inside : List Gen.Permission)
    (n : Nat) (h : inside.length = n) :
    (if inside.length > 0 then
        writeSubsliceAtIndex (List.replicate n outside) ((0 : Nat) : Int) inside
      else (pure (List.replicate n outside) : Interp (List Gen.Permission))) = .ok inside := by
  subst h
  by_cases hpos : inside.length > 0
  · have hw : (0 : Int) ≤ ((0 : Nat) : Int) ∧
        ((0 : Nat) : Int) + (inside.length : Int) ≤
          ((List.replicate inside.length outside).length : Int) := by
      rw [List.length_replicate]
      exact ⟨by omega, by omega⟩
    unfold writeSubsliceAtIndex
    simp only [hpos, hw, and_self, ↓reduceIte]
    show Except.ok (List.take 0 _ ++ inside ++ List.drop (0 + inside.length) _) = _
    rw [List.take_zero, List.nil_append, Nat.zero_add,
      List.drop_eq_nil_of_le (by rw [List.length_replicate]; exact Nat.le_refl _),
      List.append_nil]
  · have h0 : inside = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0
    rfl

private theorem nwsr_static_initAccess (n : Nat) (inside : List Gen.Permission)
    (hperm : ∀ p ∈ inside, p = .Unprot .Frozen ∨ p = .Unprot .Cell) :
    ∀ (rest : List Gen.Permission) (idx : Nat), inside.length = n → inside.drop idx = rest →
      TreeBorrowsMemory.reborrowInitAccess [0] ⟨0⟩ idx rest
        ⟨[⟨[], inside, .No⟩], List.replicate n (.Unprot .Unique), .No⟩ =
      .ok ⟨[⟨[], inside, .No⟩], List.replicate n (.Unprot .Unique), .No⟩
  | [], _, _, _ => rfl
  | perm :: rest, idx, hlen, hdrop => by
    have hidx : idx < inside.length := by
      rcases Nat.lt_or_ge idx inside.length with h | h
      · exact h
      · rw [List.drop_eq_nil_of_le h] at hdrop
        cases hdrop
    have hget : inside[idx]? = some perm := by
      have h0 : (inside.drop idx)[0]? = some perm := by rw [hdrop]; rfl
      rw [List.getElem?_drop] at h0
      exact h0
    have hnext : inside.drop (idx + 1) = rest := by
      have h1 : (inside.drop idx).drop 1 = rest := by rw [hdrop]; rfl
      rw [List.drop_drop] at h1
      exact h1
    rcases hperm perm (List.mem_of_getElem? hget) with rfl | rfl
    · have hacc : Node.access
          ⟨[⟨[], inside, .No⟩], List.replicate n (.Unprot .Unique), .No⟩ (some [0]) .Read
          (Size.add ⟨0⟩ ⟨idx⟩) ⟨1⟩ =
          .ok ⟨[⟨[], inside, .No⟩], List.replicate n (.Unprot .Unique), .No⟩ := by
        show Node.access _ (some [0]) .Read ⟨0 + idx⟩ ⟨1⟩ = _
        rw [node_access_rootChild_eq,
          transitionRange_stable_eq .Local .Read 1 (0 + idx)
            (List.replicate n (.Unprot .Unique)) (by
              intro b h1 h2
              have hb : b = idx := by omega
              rw [hb]
              exact ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩),
          transitionRange_stable_eq .Local .Read 1 (0 + idx) inside (by
              intro b h1 h2
              have hb : b = idx := by omega
              rw [hb]
              exact ⟨_, hget, rfl⟩)]
        rfl
      show (Node.access ⟨[⟨[], inside, .No⟩], List.replicate n (.Unprot .Unique), .No⟩
          (some [0]) .Read (Size.add ⟨0⟩ ⟨idx⟩) ⟨1⟩ >>= fun root' =>
          TreeBorrowsMemory.reborrowInitAccess [0] ⟨0⟩ (idx + 1) rest root') = _
      rw [hacc]
      exact nwsr_static_initAccess n inside hperm rest (idx + 1) hlen hnext
    · exact nwsr_static_initAccess n inside hperm rest (idx + 1) hlen hnext

private theorem nwsr_static_reborrow (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (addr : Int) (align : Nat) (s : Gen.ReborrowSettings) (fe : Gen.TreeBorrowsFrameExtra)
    (hprot : s.«protected» = .No) (hlen : s.inside.length = data.length)
    (hperm : ∀ p ∈ s.inside, p = .Unprot .Frozen ∨ p = .Unprot .Cell) :
    TreeBorrowsMemory.reborrow (staticTbm data addr align)
        { addr := addr, provenance := some (⟨0⟩, []) } s fe =
      .ok ({ addr := addr, provenance := some (⟨0⟩, [0]) },
        staticTbmRetagged data addr align s.inside, fe) := by
  have hcheck : ∃ r, BasicMemory.check_ptr (staticTbm data addr align).mem
      { addr := addr, provenance := some (⟨0⟩, []) } ⟨s.inside.length⟩ = .ok r := by
    by_cases h0 : s.inside.length = 0
    · refine ⟨none, ?_⟩
      unfold BasicMemory.check_ptr
      simp only [h0, ↓reduceIte]
      rfl
    · exact ⟨_, nwsr_check_ptr_ok _ _ 0 [] (mkRootAllocTB data addr align .Global) 0
        s.inside.length rfl rfl rfl (by show addr - addr = ((0 : Nat) : Int); omega)
        (by show 0 + s.inside.length ≤ data.length; omega) h0⟩
  obtain ⟨r, hr⟩ := hcheck
  have hall : (s.inside.all fun x => Permission.matches_protector x .No) = true := by
    rw [List.all_eq_true]
    intro p hp
    rcases hperm p hp with rfl | rfl <;> rfl
  have hsz : Size.from_bytes (addr - addr) = some ⟨0⟩ := by
    rw [Int.sub_self]
    rfl
  have hperms := nwsr_static_childPerms s.outside s.inside data.length hlen
  have hinit := nwsr_static_initAccess data.length s.inside hperm s.inside 0 hlen rfl
  unfold TreeBorrowsMemory.reborrow
  simp only [hr, bind, Except.bind]
  simp only [staticTbm, staticTbmRetagged, nwsr_listMutateAt_zero_singleton, mkRootAllocTB, hsz,
    pure, Except.pure, Allocation.size, bind, Except.bind, hprot]
  by_cases hpos : s.inside.length > 0
  · have hws : writeSubsliceAtIndex (List.replicate data.length s.outside) ((0 : Nat) : Int)
        s.inside = .ok s.inside := by
      have h1 := hperms
      simp only [hpos, ↓reduceIte] at h1
      exact h1
    have hinit' : TreeBorrowsMemory.reborrowInitAccess [((0 : Nat) : Int)] ⟨0⟩ 0 s.inside
        ⟨[⟨[], s.inside, .No⟩], List.replicate data.length (.Unprot .Unique), .No⟩ =
        .ok ⟨[⟨[], s.inside, .No⟩], List.replicate data.length (.Unprot .Unique), .No⟩ := hinit
    simp only [hpos, ↓reduceIte, hws, hall, Bool.not_true, Bool.false_eq_true, Node.add_node,
      Node.access_node, bind, Except.bind, pure, Except.pure, List.nil_append, List.length_nil,
      hinit']
    rfl
  · have hd0 : data.length = 0 := by omega
    have hin0 : s.inside = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [↓reduceIte, hd0, hin0, List.replicate_zero, List.all_nil, Bool.not_true,
      Bool.false_eq_true, Node.add_node, Node.access_node, bind, Except.bind, pure, Except.pure,
      List.nil_append, List.length_nil]
    rfl

/-- **Preserved `#1620` static retag on real `TreeBorrowsMemory.retag_ptr`
(symbolic in the layout)**: for EVERY `desc : StaticTyDesc` with disjoint
in-bounds `UnsafeCell`s, every static contents `data`, base address, and
alignment, the shared temporary retag `&S` of the root pointer succeeds on
`TreeBorrowsMemory.retag_ptr` → `TreeBorrowsMemory.reborrow`, mints the child tag
`[0]` (no protector pushed), and produces exactly `staticTbmRetagged` whose
per-byte child permissions `inside` are `.Unprot .Frozen` outside and
`.Unprot .Cell` inside non-zero-length `UnsafeCell`s. -/
theorem tbm_staticPreserved_retag_ptr (desc : StaticTyDesc) (align : Nat)
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable) (fnIw : Bool)
    (hdisj : CellsDisjointInBounds 0 desc.totalByteSize
      (sortCellsByOffset (collectNonZeroUnsafeCells 0 desc)))
    (hdata : data.length = desc.totalByteSize) :
    ∃ inside : List Gen.Permission,
      inside.length = desc.totalByteSize ∧
      (∀ b < desc.totalByteSize,
        (inside[b]? = some (.Unprot .Frozen) ↔ byteInNonZeroUnsafeCell desc b = false) ∧
        (inside[b]? = some (.Unprot .Cell) ↔ byteInNonZeroUnsafeCell desc b = true)) ∧
      TreeBorrowsMemory.retag_ptr (staticTbm data addr align) TreeBorrowsMemory.new_call
          { thin_pointer := { addr := addr, provenance := some (⟨0⟩, []) }, metadata := none }
          (.Ref .Immutable (staticPointeeInfoMR desc align)) false fnIw lookup =
        .ok ({ thin_pointer := { addr := addr, provenance := some (⟨0⟩, [0]) }, metadata := none },
          staticTbmRetagged data addr align inside, TreeBorrowsMemory.new_call) := by
  obtain ⟨s, hnew, hprot, hlen, _, hbytes, _⟩ :=
    reborrowSettings_staticPreserved_correspondence lookup
      { thin_pointer := { addr := addr, provenance := some (⟨0⟩, []) }, metadata := none }
      desc align (staticTbm data addr align).params fnIw hdisj
  have hperm : ∀ p ∈ s.inside, p = .Unprot .Frozen ∨ p = .Unprot .Cell := by
    intro p hp
    obtain ⟨b, hget⟩ := List.mem_iff_getElem?.mp hp
    have hb : b < s.inside.length := (List.getElem?_eq_some_iff.mp hget).1
    cases hc : byteInNonZeroUnsafeCell desc b with
    | false =>
      have h1 := (hbytes b (by omega)).1.mpr hc
      rw [hget] at h1
      cases h1
      exact Or.inl rfl
    | true =>
      have h1 := (hbytes b (by omega)).2.mpr hc
      rw [hget] at h1
      cases h1
      exact Or.inr rfl
  refine ⟨s.inside, hlen, hbytes, ?_⟩
  unfold TreeBorrowsMemory.retag_ptr
  simp only [hnew, bind, Except.bind,
    nwsr_static_reborrow data addr align s TreeBorrowsMemory.new_call hprot
      (hlen.trans hdata.symm) hperm]
  rfl

/-- **Symbolic byte-offset write theorem on real `TreeBorrowsMemory.store`**: on
the post-retag state `staticTbmRetagged` of ANY static layout, an aligned
non-empty in-bounds store of `wBytes` at byte offset `wOff` through the preserved
`#1620` tag `[0]` succeeds **iff every byte of `[wOff, wOff + wBytes.length)` lies
inside a non-zero-length `UnsafeCell`**, and otherwise raises exactly
`"Tree Borrows: local write of Frozen reference"`. -/
theorem tbm_staticRetagged_store_ok_iff_all_bytes_in_unsafeCell
    (desc : StaticTyDesc) (align : Nat)
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int)
    (inside : List Gen.Permission)
    (hlen : inside.length = desc.totalByteSize) (hdata : data.length = desc.totalByteSize)
    (hbytes : ∀ b < desc.totalByteSize,
      (inside[b]? = some (.Unprot .Frozen) ↔ byteInNonZeroUnsafeCell desc b = false) ∧
      (inside[b]? = some (.Unprot .Cell) ↔ byteInNonZeroUnsafeCell desc b = true))
    (wOff : Nat) (wBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (wAlign : Nat)
    (hwlen : wBytes.length ≠ 0) (hin : wOff + wBytes.length ≤ desc.totalByteSize)
    (haligned : Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) = true) :
    ((∃ tbm2, TreeBorrowsMemory.store (staticTbmRetagged data addr align inside)
        { addr := addr + (wOff : Int), provenance := some (⟨0⟩, [0]) } wBytes ⟨wAlign⟩ = .ok tbm2) ↔
      ∀ b, wOff ≤ b → b < wOff + wBytes.length → byteInNonZeroUnsafeCell desc b = true) ∧
    ((∃ b, wOff ≤ b ∧ b < wOff + wBytes.length ∧ byteInNonZeroUnsafeCell desc b = false) →
      TreeBorrowsMemory.store (staticTbmRetagged data addr align inside)
        { addr := addr + (wOff : Int), provenance := some (⟨0⟩, [0]) } wBytes ⟨wAlign⟩ =
        .error (.ub "Tree Borrows: local write of Frozen reference")) := by
  have hstore := tbm_store_eq_node_access (staticTbmRetagged data addr align inside)
    { addr := addr + (wOff : Int), provenance := some (⟨0⟩, [0]) } wBytes ⟨wAlign⟩ 0 [0]
    { mkRootAllocTB data addr align .Global with
      extra := { root := ⟨[⟨[], inside, .No⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩ } }
    wOff rfl rfl rfl haligned
    (by show addr + (wOff : Int) - addr = (wOff : Int); omega) hwlen
    (by show wOff + wBytes.length ≤ data.length; omega)
  have hacc : Node.access
      (⟨[⟨[], inside, .No⟩], List.replicate data.length (.Unprot .Unique), .No⟩ : Gen.Node)
      (some [0]) .Write ⟨wOff⟩ ⟨wBytes.length⟩ = _ :=
    node_access_rootChild_eq .Write wOff wBytes.length
      (List.replicate data.length (.Unprot .Unique)) inside .No .No
  have hroot : Node.transitionRange .Local .Write wOff wBytes.length
      (List.replicate data.length (.Unprot .Unique)) =
      .ok (List.replicate data.length (.Unprot .Unique)) :=
    transitionRange_stable_eq .Local .Write wBytes.length wOff _ (fun b _ h2 =>
      ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
  have hcell : ∀ b, wOff ≤ b → b < wOff + wBytes.length →
      byteInNonZeroUnsafeCell desc b = true → inside[b]? = some (.Unprot .Cell) :=
    fun b _ h2 hc => (hbytes b (by omega)).2.mpr hc
  have hfrz : ∀ b, wOff ≤ b → b < wOff + wBytes.length →
      byteInNonZeroUnsafeCell desc b = false → inside[b]? = some (.Unprot .Frozen) :=
    fun b _ h2 hc => (hbytes b (by omega)).1.mpr hc
  dsimp only at hstore
  rw [hstore, hacc, hroot]
  cases hc : Node.transitionRange .Local .Write wOff wBytes.length inside with
  | ok ips =>
    have hallCell : ∀ b, wOff ≤ b → b < wOff + wBytes.length →
        byteInNonZeroUnsafeCell desc b = true := by
      intro b h1 h2
      obtain ⟨p, p', hp, htr⟩ := transitionRange_ok_inv .Local .Write wBytes.length wOff
        inside ips hc b h1 h2
      cases hbv : byteInNonZeroUnsafeCell desc b with
      | true => rfl
      | false =>
        rw [hfrz b h1 h2 hbv] at hp
        cases hp
        cases htr
    refine ⟨⟨fun _ => hallCell, fun _ => ⟨_, rfl⟩⟩, ?_⟩
    rintro ⟨b, h1, h2, hbv⟩
    rw [hallCell b h1 h2] at hbv
    cases hbv
  | error e =>
    refine ⟨⟨(fun ⟨_, h⟩ => by cases h), fun hall => ?_⟩, ?_⟩
    · have hst := transitionRange_stable_eq .Local .Write wBytes.length wOff inside
        (fun b h1 h2 => ⟨_, hcell b h1 h2 (hall b h1 h2), rfl⟩)
      rw [hst] at hc
      cases hc
    · intro _
      obtain ⟨b, p, h1, h2, hp, htr⟩ := transitionRange_error_inv .Local .Write wBytes.length
        wOff inside e (by rw [hlen]; exact hin) hc
      cases hbv : byteInNonZeroUnsafeCell desc b with
      | true =>
        rw [hcell b h1 h2 hbv] at hp
        cases hp
        cases htr
      | false =>
        rw [hfrz b h1 h2 hbv] at hp
        cases hp
        cases htr
        rfl

/-- **Pre-`#1620` erased raw static access on real `TreeBorrowsMemory.store`**:
through the un-retagged root tag `[]` (`&raw const S`, `tbm_staticErased_raw_is_noop`),
EVERY aligned non-empty in-bounds store succeeds, regardless of `Freeze` fields
or padding. -/
theorem tbm_staticErased_store_always_ok
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int) (align : Nat)
    (wOff : Nat) (wBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (wAlign : Nat)
    (hwlen : wBytes.length ≠ 0) (hin : wOff + wBytes.length ≤ data.length)
    (haligned : Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) = true) :
    ∃ tbmE, TreeBorrowsMemory.store (staticTbm data addr align)
      { addr := addr + (wOff : Int), provenance := some (⟨0⟩, []) } wBytes ⟨wAlign⟩ = .ok tbmE := by
  have hstore := tbm_store_eq_node_access (staticTbm data addr align)
    { addr := addr + (wOff : Int), provenance := some (⟨0⟩, []) } wBytes ⟨wAlign⟩ 0 []
    (mkRootAllocTB data addr align .Global) wOff rfl rfl rfl haligned
    (by show addr + (wOff : Int) - addr = (wOff : Int); omega) hwlen hin
  have hacc : Node.access
      (⟨[], List.replicate data.length (.Unprot .Unique), .No⟩ : Gen.Node)
      (some []) .Write ⟨wOff⟩ ⟨wBytes.length⟩ = _ :=
    node_access_rootOnly_eq .Write wOff wBytes.length
      (List.replicate data.length (.Unprot .Unique)) .No
  have hroot : Node.transitionRange .Local .Write wOff wBytes.length
      (List.replicate data.length (.Unprot .Unique)) =
      .ok (List.replicate data.length (.Unprot .Unique)) :=
    transitionRange_stable_eq .Local .Write wBytes.length wOff _ (fun b _ h2 =>
      ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
  have hacc' : Node.access (mkRootAllocTB data addr align .Global).extra.root
      (some []) .Write ⟨wOff⟩ ⟨wBytes.length⟩ = _ := hacc
  rw [hstore, hacc', hroot]
  exact ⟨_, rfl⟩

/-- Miri-model counterpart of `tbm_staticErased_store_always_ok`: on every
mutable static (`!isSyntacticFreeze`), the pre-`#1620` erased raw write is
accepted at EVERY in-bounds byte range. -/
theorem static_erased_write_ok_of_mut (desc : StaticTyDesc) (rootTag off len : Nat)
    (hmut : staticAllocMutability desc = .mut) (hin : off + len ≤ desc.totalByteSize) :
    evalRawMutStaticWriteMiri desc (retagStaticErasedAt desc rootTag) off len = .ok := by
  have hm : (staticAllocMutability desc == AllocMutability.not) = false := by rw [hmut]; rfl
  have hb : ¬ (off + len > (retagStaticErasedAt desc rootTag).totalSize) := by
    show ¬ (off + len > desc.totalByteSize)
    omega
  unfold evalRawMutStaticWriteMiri evalRawMutStaticWriteTB
  cases hl : (len == 0) with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, hm, hb]
    unfold retagStaticErasedAt
    cases (desc.totalByteSize == 0) <;> simp
    all_goals
      intro x x1 _ _ h1 _
      rw [h1]

/-! ### 6.2 Field-Order Independence, Zero-Sized `UnsafeCell<()>` Cells, and Layout Validity -/

private theorem nwsr_cellsDisjoint_mono (total : Nat) :
    ∀ (xs : List (Nat × Nat)) (k k' : Nat), k ≤ k' →
      CellsDisjointInBounds k' total xs → CellsDisjointInBounds k total xs
  | [], _, _, hk, h => Nat.le_trans hk h
  | (_, _) :: _, _, _, hk, ⟨h1, h2, h3⟩ => ⟨Nat.le_trans hk h1, h2, h3⟩

private theorem nwsr_insertCell_disjoint (total cO cL : Nat) (hc2 : cL ≠ 0)
    (hcb : cO + cL ≤ total) :
    ∀ (xs : List (Nat × Nat)) (k : Nat), k ≤ cO →
      (∀ d ∈ xs, d.2 ≠ 0 ∧ (cO + cL ≤ d.1 ∨ d.1 + d.2 ≤ cO)) →
      CellsDisjointInBounds k total xs →
      CellsDisjointInBounds k total (insertCellByOffset (cO, cL) xs)
  | [], _, hk, _, _ => ⟨hk, hcb, hcb⟩
  | (dO, dL) :: rest, k, hk, hd, ⟨hkd, hdb, hrest⟩ => by
    have hdnz : dL ≠ 0 := (hd (dO, dL) (List.mem_cons_self ..)).1
    have hdisj : cO + cL ≤ dO ∨ dO + dL ≤ cO := (hd (dO, dL) (List.mem_cons_self ..)).2
    by_cases hle : cO ≤ dO
    · have hins : insertCellByOffset (cO, cL) ((dO, dL) :: rest) =
          (cO, cL) :: (dO, dL) :: rest := by
        simp only [insertCellByOffset, hle, ↓reduceIte]
      rw [hins]
      have hcd : cO + cL ≤ dO := by
        rcases hdisj with h | h
        · exact h
        · exact absurd (Nat.le_trans h hle) (by omega)
      exact ⟨hk, hcb, hcd, hdb, hrest⟩
    · have hins : insertCellByOffset (cO, cL) ((dO, dL) :: rest) =
          (dO, dL) :: insertCellByOffset (cO, cL) rest := by
        simp only [insertCellByOffset, hle, ↓reduceIte]
      rw [hins]
      have hdc : dO + dL ≤ cO := by
        rcases hdisj with h | h
        · exact absurd (Nat.le_trans (Nat.le_add_right cO cL) h) hle
        · exact h
      exact ⟨hkd, hdb, nwsr_insertCell_disjoint total cO cL hc2 hcb rest (dO + dL) hdc
        (fun d hm => hd d (List.mem_cons_of_mem _ hm)) hrest⟩

/-- **Field-order independence of the MiniRust `UnsafeCell` list**: sorting ANY
list of non-zero-length, in-bounds, pairwise-disjoint `UnsafeCell` intervals
(declared in arbitrary, e.g. reverse-offset, `repr(Rust)` order) by offset yields
a list accepted by MiniRust's `cells_to_freeze_mask` (`CellsDisjointInBounds`). -/
theorem cellsDisjointInBounds_sort_of_pairwise (total : Nat) :
    ∀ (cs : List (Nat × Nat)),
      (∀ c ∈ cs, c.2 ≠ 0 ∧ c.1 + c.2 ≤ total) →
      cs.Pairwise (fun a b => a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1) →
      CellsDisjointInBounds 0 total (sortCellsByOffset cs)
  | [], _, _ => Nat.zero_le _
  | (cO, cL) :: rest, hall, hpw => by
    rw [List.pairwise_cons] at hpw
    obtain ⟨hhead, htail⟩ := hpw
    have hnz : cL ≠ 0 := (hall (cO, cL) (List.mem_cons_self ..)).1
    have hb : cO + cL ≤ total := (hall (cO, cL) (List.mem_cons_self ..)).2
    have ih := cellsDisjointInBounds_sort_of_pairwise total rest
      (fun c hm => hall c (List.mem_cons_of_mem _ hm)) htail
    show CellsDisjointInBounds 0 total (insertCellByOffset (cO, cL) (sortCellsByOffset rest))
    exact nwsr_insertCell_disjoint total cO cL hnz hb (sortCellsByOffset rest) 0 (Nat.zero_le _)
      (fun d hm =>
        have hm' : d ∈ rest := (mem_sortCellsByOffset d rest).mp hm
        ⟨(hall d (List.mem_cons_of_mem _ hm')).1, hhead d hm'⟩) ih

mutual

/-- `collectNonZeroUnsafeCells` only ever emits non-zero-length intervals
(zero-sized `UnsafeCell<()>` fields are dropped at every nesting depth). -/
theorem collectNonZeroUnsafeCells_nonzero :
    ∀ (base : Nat) (d : StaticTyDesc), ∀ c ∈ collectNonZeroUnsafeCells base d, c.2 ≠ 0
  | _, .freezeScalar _, c, h => by
    rw [collectNonZeroUnsafeCells] at h
    cases h
  | _, .padding _, c, h => by
    rw [collectNonZeroUnsafeCells] at h
    cases h
  | base, .unsafeCell len, c, h => by
    rw [collectNonZeroUnsafeCells] at h
    cases hl : (len == 0) with
    | true =>
      rw [hl] at h
      cases h
    | false =>
      rw [hl] at h
      have hc : c = (base, len) := List.mem_singleton.mp h
      rw [hc]
      intro h0
      have h0' : len = 0 := h0
      rw [h0'] at hl
      cases hl
  | base, .composite _ fields, c, h => by
    rw [collectNonZeroUnsafeCells] at h
    exact collectFieldsNonZeroUnsafeCells_nonzero base fields c h

/-- Field-list companion of `collectNonZeroUnsafeCells_nonzero`. -/
theorem collectFieldsNonZeroUnsafeCells_nonzero :
    ∀ (base : Nat) (fs : List (Nat × StaticTyDesc)),
      ∀ c ∈ collectFieldsNonZeroUnsafeCells base fs, c.2 ≠ 0
  | _, [], c, h => by
    rw [collectFieldsNonZeroUnsafeCells] at h
    cases h
  | base, (off, d) :: rest, c, h => by
    rw [collectFieldsNonZeroUnsafeCells] at h
    rcases List.mem_append.mp h with h | h
    · exact collectNonZeroUnsafeCells_nonzero (base + off) d c h
    · exact collectFieldsNonZeroUnsafeCells_nonzero base rest c h

end

/-- **Order-independent static layout validity**: the non-zero-length
`UnsafeCell` intervals of `desc`, in DECLARATION order (any field order, any
nesting), are in bounds and pairwise disjoint. Zero-sized `UnsafeCell<()>` fields
are unconstrained and may sit at any interior, leading, or trailing offset. -/
def StaticCellsValid (desc : StaticTyDesc) : Prop :=
  (∀ c ∈ collectNonZeroUnsafeCells 0 desc, c.1 + c.2 ≤ desc.totalByteSize) ∧
  (collectNonZeroUnsafeCells 0 desc).Pairwise (fun a b => a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1)

instance (desc : StaticTyDesc) : Decidable (StaticCellsValid desc) := by
  unfold StaticCellsValid
  exact inferInstance

/-- Every valid static layout (in ANY field declaration order, with zero-sized
`UnsafeCell<()>` fields anywhere) translates to a MiniRust `UnsafeCell` list
accepted by `cells_to_freeze_mask`. -/
theorem staticCellsValid_disjointInBounds (desc : StaticTyDesc) (h : StaticCellsValid desc) :
    CellsDisjointInBounds 0 desc.totalByteSize
      (sortCellsByOffset (collectNonZeroUnsafeCells 0 desc)) :=
  cellsDisjointInBounds_sort_of_pairwise _ _
    (fun c hc => ⟨collectNonZeroUnsafeCells_nonzero 0 desc c hc, h.1 c hc⟩) h.2

private theorem nwsr_cellsDisjoint_filter (total : Nat) :
    ∀ (xs : List (Nat × Nat)) (k : Nat), CellsDisjointInBounds k total xs →
      CellsDisjointInBounds k total (xs.filter (fun c => c.2 != 0))
  | [], _, h => h
  | (o, l) :: rest, k, ⟨h1, h2, h3⟩ => by
    have ih := nwsr_cellsDisjoint_filter total rest (o + l) h3
    cases hl : (l != 0) with
    | false =>
      have hf : ((o, l) :: rest).filter (fun c => c.2 != 0) =
          rest.filter (fun c => c.2 != 0) := by
        rw [List.filter_cons]
        simp only [hl, Bool.false_eq_true, ↓reduceIte]
      rw [hf]
      exact nwsr_cellsDisjoint_mono total _ k (o + l) (Nat.le_trans h1 (Nat.le_add_right o l)) ih
    | true =>
      have hf : ((o, l) :: rest).filter (fun c => c.2 != 0) =
          (o, l) :: rest.filter (fun c => c.2 != 0) := by
        rw [List.filter_cons]
        simp only [hl, ↓reduceIte]
      rw [hf]
      exact ⟨h1, h2, ih⟩

private theorem nwsr_cellsToFreezeMask_of_spec (total : Nat) (cells : List (Nat × Nat))
    (hdisj : CellsDisjointInBounds 0 total cells) :
    ∃ mask, cellsToFreezeMask (cells.map (fun c => (⟨c.1⟩, ⟨c.2⟩))) ⟨total⟩ = .ok mask ∧
      mask.length = total ∧
      ∀ b < total, (mask[b]? = some true ↔ ∀ c ∈ cells, ¬ (c.1 ≤ b ∧ b < c.1 + c.2)) := by
  rcases cellsToFreezeMaskLoop_disjoint_spec total cells 0 0 [] (Nat.zero_le _) rfl hdisj with
    ⟨mask, hloop, hlen, _, _, hbytes⟩
  refine ⟨mask, ?_, hlen, fun b hb => (hbytes b (Nat.zero_le b) hb).1⟩
  unfold cellsToFreezeMask
  rw [hloop]
  simp only [bind, Except.bind, hlen, ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure]

/-- **Zero-sized `UnsafeCell<()>` cells are irrelevant to MiniRust's freeze mask**:
on every disjoint, memory-ordered, in-bounds cell list — where zero-length cells
may sit at ANY gap position (leading, interior, or trailing) — MiniRust's
`cells_to_freeze_mask` computes exactly the mask of the list with all zero-length
cells removed. So dropping `UnsafeCell<()>` fields (`collectNonZeroUnsafeCells`,
mirroring `FreezeVisitor`) is a faithful erasure on the MiniRust side. -/
theorem cellsToFreezeMask_ignores_zeroLength_cells (total : Nat) (cells : List (Nat × Nat))
    (hdisj : CellsDisjointInBounds 0 total cells) :
    cellsToFreezeMask (cells.map (fun c => (⟨c.1⟩, ⟨c.2⟩))) ⟨total⟩ =
      cellsToFreezeMask ((cells.filter (fun c => c.2 != 0)).map (fun c => (⟨c.1⟩, ⟨c.2⟩)))
        ⟨total⟩ := by
  obtain ⟨m1, h1, hl1, hs1⟩ := nwsr_cellsToFreezeMask_of_spec total cells hdisj
  obtain ⟨m2, h2, hl2, hs2⟩ := nwsr_cellsToFreezeMask_of_spec total
    (cells.filter (fun c => c.2 != 0)) (nwsr_cellsDisjoint_filter total cells 0 hdisj)
  rw [h1, h2]
  have hiff : ∀ b, (∀ c ∈ cells, ¬ (c.1 ≤ b ∧ b < c.1 + c.2)) ↔
      (∀ c ∈ cells.filter (fun c => c.2 != 0), ¬ (c.1 ≤ b ∧ b < c.1 + c.2)) := by
    intro b
    constructor
    · intro h c hc
      exact h c (List.mem_filter.mp hc).1
    · intro h c hc hin
      cases hz : (c.2 != 0) with
      | true => exact h c (List.mem_filter.mpr ⟨hc, hz⟩) hin
      | false =>
        have hz0 : c.2 = 0 := by
          cases hc2 : c.2 with
          | zero => rfl
          | succ n => rw [hc2] at hz; cases hz
        rw [hz0] at hin
        exact absurd hin.2 (by omega)
  have heq : m1 = m2 := by
    apply List.ext_getElem?
    intro b
    by_cases hb : b < total
    · have hb1 : b < m1.length := by rw [hl1]; exact hb
      have hb2 : b < m2.length := by rw [hl2]; exact hb
      have e1 : m1[b]? = some m1[b] := List.getElem?_eq_getElem hb1
      have e2 : m2[b]? = some m2[b] := List.getElem?_eq_getElem hb2
      rw [e1, e2]
      cases hv1 : m1[b] with
      | true =>
        have hP := (hs1 b hb).mp (by rw [e1, hv1])
        have hm2 := (hs2 b hb).mpr ((hiff b).mp hP)
        rw [e2] at hm2
        exact hm2.symm
      | false =>
        cases hv2 : m2[b] with
        | false => rfl
        | true =>
          have hP := (hs2 b hb).mp (by rw [e2, hv2])
          have hm1 := (hs1 b hb).mpr ((hiff b).mpr hP)
          rw [e1, hv1] at hm1
          cases hm1
    · rw [List.getElem?_eq_none (by rw [hl1]; omega), List.getElem?_eq_none (by rw [hl2]; omega)]
  rw [heq]

/-- **Why the zero-length filter is REQUIRED**: MiniRust's `cells_to_freeze_mask`
panics on a zero-sized `UnsafeCell<()>` cell listed after a non-zero cell that
covers its offset (e.g. `(AtomicI32 @ 0, UnsafeCell<()> @ 2)` or the same-offset
declaration order `(AtomicI32 @ 0, UnsafeCell<()> @ 0)`), whereas the same cells
with the zero-sized cell first, or with it filtered out (`staticCellsMR`), yield
the all-`UnsafeCell` mask — matching `FreezeVisitor`, which skips zero-byte cells. -/
theorem cellsToFreezeMask_zeroLength_cell_inside_cell_panics :
    cellsToFreezeMask [(⟨0⟩, ⟨4⟩), (⟨2⟩, ⟨0⟩)] ⟨4⟩ =
      .error (.specPanic "cells_to_freeze_mask: overlapping or out-of-order UnsafeCell ranges") ∧
    cellsToFreezeMask [(⟨0⟩, ⟨4⟩), (⟨0⟩, ⟨0⟩)] ⟨4⟩ =
      .error (.specPanic "cells_to_freeze_mask: overlapping or out-of-order UnsafeCell ranges") ∧
    cellsToFreezeMask [(⟨0⟩, ⟨0⟩), (⟨0⟩, ⟨4⟩)] ⟨4⟩ = .ok [false, false, false, false] ∧
    cellsToFreezeMask [(⟨0⟩, ⟨4⟩)] ⟨4⟩ = .ok [false, false, false, false] ∧
    cellsToFreezeMask (staticCellsMR (.composite 4 [(0, .unsafeCell 4), (2, .unsafeCell 0)]))
      ⟨4⟩ = .ok [false, false, false, false] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `staticTbm` satisfies `TreeBorrowsMemory.wfLive`. -/
theorem staticTbm_wfLive (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (addr : Int) (align : Nat) : TreeBorrowsMemory.wfLive (staticTbm data addr align) := by
  intro alloc hmem _
  have halloc : alloc = mkRootAllocTB data addr align .Global := List.mem_singleton.mp hmem
  rw [halloc]
  exact mkRootAllocTB_wf data addr align .Global

/-- **End-to-end symbolic static-retag write theorem on real
`TreeBorrowsMemory.retag_ptr` (`reborrow`) + `TreeBorrowsMemory.store`
(`charon#1620`)**: for ANY valid static layout `desc` (`StaticCellsValid`: any
field declaration order, zero-sized `UnsafeCell<()>` fields anywhere), any static
contents, base address, alignment, and any aligned non-empty in-bounds write
window `[wOff, wOff + wBytes.length)`:
1. the preserved shared temporary retag `&S` succeeds, minting tag `[0]` with
   `TreeBorrowsMemory.wfLive` preserved (via the general `retag_ptr_wfLive`);
2. the store through the preserved tag succeeds (again `wfLive`, via the general
   `store_wfLive`) **iff every byte of the window lies inside a non-zero-length
   `UnsafeCell`**, and otherwise raises exactly
   `"Tree Borrows: local write of Frozen reference"`;
3. on mutable statics this is exactly Miri's verdict
   (`evalRawMutStaticWriteMiri` on `retagStaticPreservedAt`,
   `static_preserved_write_ok_iff_all_bytes_in_unsafeCell`);
4. whereas the pre-`#1620` erased raw access (root tag `[]`) accepts the SAME
   write unconditionally on `TreeBorrowsMemory.store`, and Miri accepts it on
   every mutable static (`!isSyntacticFreeze`) regardless of `Freeze` fields or
   padding. -/
theorem tbm_staticPreserved_retag_then_store_iff
    (desc : StaticTyDesc) (hvalid : StaticCellsValid desc) (align : Nat)
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (hdata : data.length = desc.totalByteSize) (addr : Int)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable) (fnIw : Bool)
    (wOff : Nat) (wBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (wAlign : Nat)
    (hwlen : wBytes.length ≠ 0) (hin : wOff + wBytes.length ≤ desc.totalByteSize)
    (haligned : Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) = true) :
    ∃ tbm1,
      TreeBorrowsMemory.retag_ptr (staticTbm data addr align) TreeBorrowsMemory.new_call
          { thin_pointer := { addr := addr, provenance := some (⟨0⟩, []) }, metadata := none }
          (.Ref .Immutable (staticPointeeInfoMR desc align)) false fnIw lookup =
        .ok ({ thin_pointer := { addr := addr, provenance := some (⟨0⟩, [0]) }, metadata := none },
          tbm1, TreeBorrowsMemory.new_call) ∧
      TreeBorrowsMemory.wfLive tbm1 ∧
      ((∃ tbm2, TreeBorrowsMemory.store tbm1
          { addr := addr + (wOff : Int), provenance := some (⟨0⟩, [0]) } wBytes ⟨wAlign⟩ = .ok tbm2 ∧
          TreeBorrowsMemory.wfLive tbm2) ↔
        ∀ b, wOff ≤ b → b < wOff + wBytes.length → byteInNonZeroUnsafeCell desc b = true) ∧
      ((∃ b, wOff ≤ b ∧ b < wOff + wBytes.length ∧ byteInNonZeroUnsafeCell desc b = false) →
        TreeBorrowsMemory.store tbm1
          { addr := addr + (wOff : Int), provenance := some (⟨0⟩, [0]) } wBytes ⟨wAlign⟩ =
          .error (.ub "Tree Borrows: local write of Frozen reference")) ∧
      (staticAllocMutability desc = .mut → ∀ rootTag tmpTag,
        ((∃ tbm2, TreeBorrowsMemory.store tbm1
            { addr := addr + (wOff : Int), provenance := some (⟨0⟩, [0]) } wBytes ⟨wAlign⟩ =
            .ok tbm2) ↔
          evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag)
            wOff wBytes.length = .ok)) ∧
      (∃ tbmE, TreeBorrowsMemory.store (staticTbm data addr align)
        { addr := addr + (wOff : Int), provenance := some (⟨0⟩, []) } wBytes ⟨wAlign⟩ = .ok tbmE) ∧
      (staticAllocMutability desc = .mut → ∀ rootTag,
        evalRawMutStaticWriteMiri desc (retagStaticErasedAt desc rootTag) wOff wBytes.length =
          .ok) := by
  have hdisj := staticCellsValid_disjointInBounds desc hvalid
  obtain ⟨inside, hlen, hbytes, hretag⟩ :=
    tbm_staticPreserved_retag_ptr desc align data addr lookup fnIw hdisj hdata
  obtain ⟨hiff, hub⟩ := tbm_staticRetagged_store_ok_iff_all_bytes_in_unsafeCell desc align data
    addr inside hlen hdata hbytes wOff wBytes wAlign hwlen hin haligned
  have hwf1 : TreeBorrowsMemory.wfLive (staticTbmRetagged data addr align inside) :=
    TreeBorrowsMemory.retag_ptr_wfLive (staticTbm_wfLive data addr align) hretag
  refine ⟨staticTbmRetagged data addr align inside, hretag, hwf1, ⟨?_, ?_⟩, hub, ?_,
    tbm_staticErased_store_always_ok data addr align wOff wBytes wAlign hwlen
      (by rw [hdata]; exact hin) haligned,
    fun hmut rootTag => static_erased_write_ok_of_mut desc rootTag wOff wBytes.length hmut hin⟩
  · rintro ⟨tbm2, hst, _⟩
    exact hiff.mp ⟨tbm2, hst⟩
  · intro hall
    obtain ⟨tbm2, hst⟩ := hiff.mpr hall
    exact ⟨tbm2, hst, TreeBorrowsMemory.store_wfLive hwf1 hst⟩
  · intro hmut rootTag tmpTag
    rw [(static_preserved_write_ok_iff_all_bytes_in_unsafeCell desc rootTag tmpTag wOff
      wBytes.length hin hmut).1]
    exact hiff

/-! ### 6.3 Zero-Sized `UnsafeCell<()>` at Leading / Interior / Trailing Offsets & Reverse-Offset Declarations -/

/-- Shape (e): `static S: (UnsafeCell<()>, u8, Padding[3], AtomicI32)` with a
LEADING zero-sized `UnsafeCell<()>` at offset `0` (sharing its offset with `u8`). -/
def staticShapeEDesc : StaticTyDesc :=
  .composite 8 [(0, .unsafeCell 0), (0, .freezeScalar 1), (1, .padding 3), (4, .unsafeCell 4)]

/-- Shape (e) declared in REVERSE offset order with additional zero-sized
`UnsafeCell<()>` fields at the trailing offset `8`, at the `AtomicI32`'s own
offset `4` (declared AFTER it — the order on which an unfiltered MiniRust cell
list panics, `cellsToFreezeMask_zeroLength_cell_inside_cell_panics`), and at the
interior padding offset `2`. -/
def staticShapeEReverseDesc : StaticTyDesc :=
  .composite 8 [(8, .unsafeCell 0), (4, .unsafeCell 4), (4, .unsafeCell 0), (2, .unsafeCell 0),
    (1, .padding 3), (0, .freezeScalar 1), (0, .unsafeCell 0)]

/-- MiniRust `Gen.Type` for Shape (e) `((), u8, i32)` (`size = 8`, `align = 4`). -/
def staticShapeETyMR : Gen.Type :=
  .Tuple [(⟨0⟩, unitTyMR), (⟨0⟩, u8TyMR), (⟨4⟩, i32TyMR)] ⟨⟨8⟩, ⟨4⟩, none⟩ none

private theorem nwsr_forall_window_of_all (P : Nat → Bool) (off len : Nat)
    (h : (List.range len).all (fun i => P (off + i)) = true) :
    ∀ b, off ≤ b → b < off + len → P b = true := by
  intro b h1 h2
  have h3 := List.all_eq_true.mp h (b - off) (List.mem_range.mpr (by omega))
  have e : off + (b - off) = b := by omega
  rw [e] at h3
  exact h3

/-- **Shape (e) — mixed `(UnsafeCell<()>, u8, AtomicI32)` with zero-sized
`UnsafeCell<()>` at leading, interior, same-offset, and trailing positions, in
forward and reverse-offset declaration orders**:
1. both declarations are `StaticCellsValid`, syntactically `!Freeze`
   (`staticAllocMutability = .mut`), and translate to the SAME MiniRust cell list
   `[(4, 4)]`, the same `PointeeInfo` as Shape (c), and the same `FreezeVisitor`
   segments `[⟨0, 4, .freeze⟩, ⟨4, 4, .unsafeCell⟩]`;
2. Miri model: the preserved `#1620` retag accepts the `AtomicI32` write, rejects
   the `u8` write (even though a zero-sized `UnsafeCell<()>` sits at the same
   offset `0`) and a write straddling padding and the cell (`[3, 5)`), while the
   erased raw access accepts the `u8` write;
3. `MachTB`: the preserved program writes `55` into the `AtomicI32`, faults with
   `"Tree Borrows: local write of Frozen reference"` on the `u8`, and the erased
   program overwrites the `u8`. -/
theorem staticShapeE_zstUnsafeCell_any_offset_correspondence :
    let mPresCell := mkStaticAccessMachTB staticShapeEReverseDesc staticShapeETyMR 4
      staticShapeCInitBytes true 4 i32TyMR 55
    let mPresU8 := mkStaticAccessMachTB staticShapeEReverseDesc staticShapeETyMR 4
      staticShapeCInitBytes true 0 u8TyMR 9
    let mErasU8 := mkStaticAccessMachTB staticShapeEReverseDesc staticShapeETyMR 4
      staticShapeCInitBytes false 0 u8TyMR 9
    StaticCellsValid staticShapeEDesc ∧
    StaticCellsValid staticShapeEReverseDesc ∧
    staticShapeEDesc.isSyntacticFreeze = false ∧
    staticAllocMutability staticShapeEReverseDesc = .mut ∧
    staticCellsMR staticShapeEDesc = [(⟨4⟩, ⟨4⟩)] ∧
    staticCellsMR staticShapeEReverseDesc = [(⟨4⟩, ⟨4⟩)] ∧
    staticPointeeInfoMR staticShapeEReverseDesc 4 = staticPointeeInfoMR staticShapeCDesc 4 ∧
    staticFreezeSegments staticShapeEDesc = (8, [⟨0, 4, .freeze⟩, ⟨4, 4, .unsafeCell⟩]) ∧
    staticFreezeSegments staticShapeEReverseDesc = staticFreezeSegments staticShapeEDesc ∧
    evalRawMutStaticWriteMiri staticShapeEReverseDesc
      (retagStaticPreservedAt staticShapeEReverseDesc 1 2) 4 4 = .ok ∧
    evalRawMutStaticWriteMiri staticShapeEReverseDesc
      (retagStaticPreservedAt staticShapeEReverseDesc 1 2) 0 1 = .ub ∧
    evalRawMutStaticWriteMiri staticShapeEReverseDesc
      (retagStaticPreservedAt staticShapeEReverseDesc 1 2) 3 2 = .ub ∧
    evalRawMutStaticWriteMiri staticShapeEReverseDesc
      (retagStaticErasedAt staticShapeEReverseDesc 1) 0 1 = .ok ∧
    machRetSnapshot mPresCell 7 = some (some (true, [some 1, some 0, some 0, some 0]), [1]) ∧
    machAllocSnapshot mPresCell 7 1 =
      some (true, [some 3, none, none, none, some 55, some 0, some 0, some 0]) ∧
    machStopOutcome mPresU8 5 = some (.ub "Tree Borrows: local write of Frozen reference") ∧
    machAllocSnapshot mErasU8 7 1 =
      some (true, [some 9, none, none, none, some 10, some 0, some 0, some 0]) :=
  ⟨by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Closed non-vacuity canary for the symbolic static-write theorems**
(zero hypotheses): instantiating `tbm_staticPreserved_retag_ptr` and
`tbm_staticRetagged_store_ok_iff_all_bytes_in_unsafeCell` on the reverse-offset,
zero-sized-cell-laden Shape (e) yields, on real `TreeBorrowsMemory.retag_ptr` and
`TreeBorrowsMemory.store`:
- the `AtomicI32` window `[4, 8)` is writable through the preserved tag;
- the straddling window `[3, 5)` (padding + cell) and the `u8` window `[0, 1)`
  raise `"Tree Borrows: local write of Frozen reference"`;
- the erased root tag accepts the `u8` write. -/
theorem canary_part2_symbolic_static_write :
    ∃ inside,
      TreeBorrowsMemory.retag_ptr (staticTbm staticShapeCInitBytes 256 4)
          TreeBorrowsMemory.new_call
          { thin_pointer := { addr := 256, provenance := some (⟨0⟩, []) }, metadata := none }
          (.Ref .Immutable (staticPointeeInfoMR staticShapeEReverseDesc 4)) false true
          nwsrVtableLookup =
        .ok ({ thin_pointer := { addr := 256, provenance := some (⟨0⟩, [0]) }, metadata := none },
          staticTbmRetagged staticShapeCInitBytes 256 4 inside, TreeBorrowsMemory.new_call) ∧
      (∃ tbm2, TreeBorrowsMemory.store (staticTbmRetagged staticShapeCInitBytes 256 4 inside)
          { addr := 256 + ((4 : Nat) : Int), provenance := some (⟨0⟩, [0]) } (tbU32Bytes 55) ⟨4⟩ =
          .ok tbm2) ∧
      TreeBorrowsMemory.store (staticTbmRetagged staticShapeCInitBytes 256 4 inside)
          { addr := 256 + ((3 : Nat) : Int), provenance := some (⟨0⟩, [0]) }
          (tbU8Bytes 9 ++ tbU8Bytes 9) ⟨1⟩ =
        .error (.ub "Tree Borrows: local write of Frozen reference") ∧
      TreeBorrowsMemory.store (staticTbmRetagged staticShapeCInitBytes 256 4 inside)
          { addr := 256 + ((0 : Nat) : Int), provenance := some (⟨0⟩, [0]) } (tbU8Bytes 9) ⟨1⟩ =
        .error (.ub "Tree Borrows: local write of Frozen reference") ∧
      (∃ tbmE, TreeBorrowsMemory.store (staticTbm staticShapeCInitBytes 256 4)
          { addr := 256 + ((0 : Nat) : Int), provenance := some (⟨0⟩, []) } (tbU8Bytes 9) ⟨1⟩ =
          .ok tbmE) := by
  have hvalid : StaticCellsValid staticShapeEReverseDesc := by decide
  obtain ⟨inside, hlen, hbytes, hretag⟩ :=
    tbm_staticPreserved_retag_ptr staticShapeEReverseDesc 4 staticShapeCInitBytes 256
      nwsrVtableLookup true (staticCellsValid_disjointInBounds _ hvalid) rfl
  refine ⟨inside, hretag, ?_, ?_, ?_, ?_⟩
  · exact (tbm_staticRetagged_store_ok_iff_all_bytes_in_unsafeCell staticShapeEReverseDesc 4
      staticShapeCInitBytes 256 inside hlen rfl hbytes 4 (tbU32Bytes 55) 4 (by decide)
      (by decide) (by decide)).1.mpr
      (nwsr_forall_window_of_all (byteInNonZeroUnsafeCell staticShapeEReverseDesc) 4 4
        (by decide +kernel))
  · exact (tbm_staticRetagged_store_ok_iff_all_bytes_in_unsafeCell staticShapeEReverseDesc 4
      staticShapeCInitBytes 256 inside hlen rfl hbytes 3 (tbU8Bytes 9 ++ tbU8Bytes 9) 1
      (by decide) (by decide) (by decide)).2 ⟨3, Nat.le_refl _, by decide, by decide +kernel⟩
  · exact (tbm_staticRetagged_store_ok_iff_all_bytes_in_unsafeCell staticShapeEReverseDesc 4
      staticShapeCInitBytes 256 inside hlen rfl hbytes 0 (tbU8Bytes 9) 1 (by decide)
      (by decide) (by decide)).2 ⟨0, Nat.le_refl _, by decide, by decide +kernel⟩
  · exact tbm_staticErased_store_always_ok staticShapeCInitBytes 256 4 0 (tbU8Bytes 9) 1
      (by decide) (by decide) (by decide)

/-! ## Part 7: `#guard_msgs in #print axioms` Pins for Every Public Theorem -/

section AxiomGuards

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.nodeWf_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.nodeWf_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.childrenWf_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.childrenWf_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_wfLive_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_wfLive_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_wfLive_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_wfLive_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_steps_ok_and_wfLive_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_steps_ok_and_wfLive_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_trace_ok_and_wfLive_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_trace_ok_and_wfLive_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.mkRootAllocTB_wf' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.mkRootAllocTB_wf

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.permToMiniRust_fromMiniRust' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.permToMiniRust_fromMiniRust

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.permToMiniRust_protected_reservedIM_none' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.permToMiniRust_protected_reservedIM_none

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.permFromMiniRust_toMiniRust_prot' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.permFromMiniRust_toMiniRust_prot

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.protectorEndAccessMiniRust_eq_unprotect' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.protectorEndAccessMiniRust_eq_unprotect

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.protectorEndAccess_miri_eq_miniRust_and_unprotect' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.protectorEndAccess_miri_eq_miniRust_and_unprotect

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.stepNodeOnRangeRead_simulates_permission_transition' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.stepNodeOnRangeRead_simulates_permission_transition

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.stepNodeOnRangeWrite_simulates_permission_transition' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.stepNodeOnRangeWrite_simulates_permission_transition

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.reborrowSettings_pinned_mut_box_skip' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.reborrowSettings_pinned_mut_box_skip

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.reborrowSettings_fnEntry_mutOrBox_eq_policy' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.reborrowSettings_fnEntry_mutOrBox_eq_policy

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.reborrowSettings_fnEntry_shared_eq_create' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.reborrowSettings_fnEntry_shared_eq_create

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.trusted_fnEntryRetagPerm_aligns_with_miniRust_noWritable' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.trusted_fnEntryRetagPerm_aligns_with_miniRust_noWritable

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.box_weak_vs_mut_strong_dealloc_law' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.box_weak_vs_mut_strong_dealloc_law

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_zst_implicit_writes_invariance' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_zst_implicit_writes_invariance

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_rustcNoWritable_vs_writable_full_lifecycle' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_rustcNoWritable_vs_writable_full_lifecycle

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_and_world_noWritable_uninit_and_readOnly_separation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_and_world_noWritable_uninit_and_readOnly_separation

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_box_weak_vs_mut_strong_dealloc_both_policies' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_box_weak_vs_mut_strong_dealloc_both_policies

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_zst_mut_ref_both_policies_and_frozen_sibling' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_zst_mut_ref_both_policies_and_frozen_sibling

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.disjoint_two_param_frame_exit_miri_miniRust_and_tbm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.disjoint_two_param_frame_exit_miri_miniRust_and_tbm

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_forgetStyle_noWritable_vs_writable_e2e' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_forgetStyle_noWritable_vs_writable_e2e

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_pinned_mut_skips_retag_e2e' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_pinned_mut_skips_retag_e2e

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_forgetStyle_uninit_pointee_e2e' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_forgetStyle_uninit_pointee_e2e

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_noWritable_conflicted_latch_and_parent_write_e2e' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_noWritable_conflicted_latch_and_parent_write_e2e

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.stepMirFnWithParamMap_rustcNoWritable_eq_stepMirFn' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.stepMirFnWithParamMap_rustcNoWritable_eq_stepMirFn

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.trusted_stepMirFn_forgetStyle_noWritable_vs_writable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.trusted_stepMirFn_forgetStyle_noWritable_vs_writable

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.cellsToFreezeMaskLoop_disjoint_spec' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.cellsToFreezeMaskLoop_disjoint_spec

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.cellsToFreezeMask_staticCellsMR_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.cellsToFreezeMask_staticCellsMR_iff

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.reborrowSettings_staticPreserved_correspondence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.reborrowSettings_staticPreserved_correspondence

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_staticErased_raw_is_noop' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_staticErased_raw_is_noop

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.staticShapeA_pureFreeze_correspondence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.staticShapeA_pureFreeze_correspondence

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.staticShapeB_pureUnsafeCell_correspondence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.staticShapeB_pureUnsafeCell_correspondence

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.staticShapeC_mixedComposite_correspondence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.staticShapeC_mixedComposite_correspondence

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.staticShapeD_zstUnsafeCellComposite_correspondence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.staticShapeD_zstUnsafeCellComposite_correspondence

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_part1_noWritable_positive_and_negative' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_part1_noWritable_positive_and_negative

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_part1_pinned_box_zst_and_disjoint_exit' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_part1_pinned_box_zst_and_disjoint_exit

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_part2_all_four_static_shapes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_part2_all_four_static_shapes

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.permission_transition_error_is_ub' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.permission_transition_error_is_ub

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.transitionRange_ok_of_pointwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.transitionRange_ok_of_pointwise

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.transitionRange_ok_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.transitionRange_ok_inv

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.transitionRange_error_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.transitionRange_error_inv

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.transitionRange_error_is_ub' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.transitionRange_error_is_ub

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.transitionRange_stable_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.transitionRange_stable_eq

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.locOf_none' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.locOf_none

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.locOf_some_eq_isPrefixOf' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.locOf_some_eq_isPrefixOf

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_ok_of_pointwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_ok_of_pointwise

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_accessChildren_ok_of_pointwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_accessChildren_ok_of_pointwise

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_ok_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_ok_inv

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_accessChildren_ok_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_accessChildren_ok_inv

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_error_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_error_inv

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_accessChildren_error_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_accessChildren_error_inv

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tree_read_simulates_node_access' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tree_read_simulates_node_access

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tree_write_simulates_node_access' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tree_write_simulates_node_access

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_store_eq_node_access' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_store_eq_node_access

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_load_eq_node_access' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_load_eq_node_access

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_rootChild_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_rootChild_eq

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_rootOnly_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_rootOnly_eq

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_store_simulates_execWorldRangeWrite' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_store_simulates_execWorldRangeWrite

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_load_simulates_execWorldRangeRead' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_load_simulates_execWorldRangeRead

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.nodeAt_mem_nodePaths' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.nodeAt_mem_nodePaths

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.nodeAt_mem_childrenPaths' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.nodeAt_mem_childrenPaths

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.nodeWindowRel_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.nodeWindowRel_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.treeSimInv_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.treeSimInv_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbmWorldRel_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbmWorldRel_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_tree_simulation_twoBranch' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_tree_simulation_twoBranch

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_sliceGetMut_noWritable_vs_writable' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_sliceGetMut_noWritable_vs_writable

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.sliceGetMut_world_agreement_and_coarse_range_overapproximation' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.sliceGetMut_world_agreement_and_coarse_range_overapproximation

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_endCall_overlapping_frame_order_separation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_endCall_overlapping_frame_order_separation

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_endCall_implicit_protectorEnd_access_separation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_endCall_implicit_protectorEnd_access_separation

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.noWritable_conflicted_lifecycle_relational_lockstep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.noWritable_conflicted_lifecycle_relational_lockstep

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.writable_lifecycle_relational_lockstep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.writable_lifecycle_relational_lockstep

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.protectedSibling_noWritable_vs_writable_relational_lockstep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.protectedSibling_noWritable_vs_writable_relational_lockstep

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.readOnlyAlloc_noWritable_entry_and_exit_vs_writable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.readOnlyAlloc_noWritable_entry_and_exit_vs_writable

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_wfLive_of_rootAllocs' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_wfLive_of_rootAllocs

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_harnesses_initial_wfLive' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_harnesses_initial_wfLive

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_protectedSibling_noWritable_vs_writable_e2e' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_protectedSibling_noWritable_vs_writable_e2e

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.stepMirFnWithParamMap_eq_stepMirFn_of_rustcNoWritable_at_pc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.stepMirFnWithParamMap_eq_stepMirFn_of_rustcNoWritable_at_pc

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.permToMiniRust_eq_iff_permErasure' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.permToMiniRust_eq_iff_permErasure

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.permToMiniRust_not_injective' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.permToMiniRust_not_injective

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_staticPreserved_retag_ptr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_staticPreserved_retag_ptr

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_staticRetagged_store_ok_iff_all_bytes_in_unsafeCell' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_staticRetagged_store_ok_iff_all_bytes_in_unsafeCell

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_staticErased_store_always_ok' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_staticErased_store_always_ok

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.static_erased_write_ok_of_mut' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.static_erased_write_ok_of_mut

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.cellsDisjointInBounds_sort_of_pairwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.cellsDisjointInBounds_sort_of_pairwise

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.collectNonZeroUnsafeCells_nonzero' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.collectNonZeroUnsafeCells_nonzero

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.collectFieldsNonZeroUnsafeCells_nonzero' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.collectFieldsNonZeroUnsafeCells_nonzero

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.staticCellsValid_disjointInBounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.staticCellsValid_disjointInBounds

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.cellsToFreezeMask_ignores_zeroLength_cells' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.cellsToFreezeMask_ignores_zeroLength_cells

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.cellsToFreezeMask_zeroLength_cell_inside_cell_panics' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.cellsToFreezeMask_zeroLength_cell_inside_cell_panics

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.staticTbm_wfLive' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.staticTbm_wfLive

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_staticPreserved_retag_then_store_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_staticPreserved_retag_then_store_iff

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.staticShapeE_zstUnsafeCell_any_offset_correspondence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.staticShapeE_zstUnsafeCell_any_offset_correspondence

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_part2_symbolic_static_write' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_part2_symbolic_static_write

end AxiomGuards

end MiniRustSpec.NoWritableAndStaticRetag
