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
     `MiriRetagPolicyMirror.create`, `protToMiniRust`, and `Trusted.fnEntryRetagPerm`
     to MiniRust's `ReborrowSettings.new` across `&T`, `&mut T`, `Box<T>`,
     `!Unpin` skip-retag (`pinned_mutable_or_box_fnEntry_skips_retag`),
     `Protected::Weak` vs. `Protected::Strong`, and zero-sized `&mut ()`
     (`reborrowSettings_prot_eq_protToMiniRust`).
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

4. **Part 4 (Symbolic Whole-Tree Calculus, Relational Simulation, Deallocation,
   & Per-Byte Sub-Slice Refinement)**:
   - **4.1–4.5**: byte-window calculus for `Node.transitionRange`, path-indexed
     whole-tree specification of `Node.access`, `TreeBorrowsMemory.load` / `store`
     equations, and single-window whole-tree simulation (`TreeSimInv`,
     `tbm_load_simulates_execWorldRangeRead`,
     `tbm_store_simulates_execWorldRangeWrite`).
   - **4.6–4.7**: path-indexed specifications for `Node.access_node`,
     `Node.add_node`, `reborrowInitAccess`, and `TreeBorrowsMemory.reborrow`,
     lifting to **symbolic whole-tree `TreeSimInv` lockstep simulation of
     `TreeBorrowsMemory.retag_ptr`** across `#[rustc_no_writable]` & standard
     `&mut T`, `Box<T>` (`Protected::Weak`), `&T`, and ZST `&mut ()` against
     both `execFnEntryMutRetagPrunedSourceOrder` and
     `execFnEntryMutRetagTraversalOrderDirect` (plus closed canary).
   - **4.8**: path-indexed specification of `Node.release_protector`, choice-free
     `tbm_release_protector_wfLive_choiceFree` / `tbm_end_call_wfLive_choiceFree`,
     dead-allocation short-circuit, and **symbolic whole-tree `TreeSimInv`
     lockstep simulation of single- and multi-entry `TreeBorrowsMemory.end_call`**
     against `execFrameExitMiniRust` on borrow trees of ARBITRARY depth
     (`tbm_end_call_simulates_execFrameExitMiniRust_of_pruneInert`, under the
     step-indexed `FrameExitPruneInert`; the shallow-tree
     `NoNestedForeignAncestors` statement is a corollary), plus closed
     multi-entry and deep-tree canaries.
   - **4.9**: **symbolic whole-tree `TreeBorrowsMemory.deallocate`**:
     `permission_prevents_deallocation_iff_foreign_write_err`,
     `contains_strong_protector_iff`, the one-directional
     `tbm_deallocate_strong_protector_ub` (a `Protected::Strong` node with a byte
     that `prevents_deallocation` forces UB, under either retag policy) and
     `tbm_deallocate_weak_box_ok_iff`, and the **exact criterion for ALL
     protector kinds** `tbm_deallocate_ok_iff_pointwise` /
     `tbm_deallocate_ok_iff_full`: deallocation succeeds iff the pre-checks pass
     and the decidable per-byte table `permAllowsDealloc` holds at every byte of
     every node — so a strong protector on never-accessed or `Cell` bytes does
     NOT block deallocation (`tbm_deallocate_precheck_ub` classifies the
     pre-check failures, including `"double-free"`).
   - **4.10**: **byte-local frame & commutativity laws**
     (`node_access_frame_outside`, `node_access_comm_of_disjoint`,
     `node_release_protector_frame_outside`), the frozen-reader laws
     (`node_access_foreign_write_kills_frozen_reader`,
     `node_access_foreign_read_preserves_frozen_reader`) and their lift to the
     real `TreeBorrowsMemory.retag_ptr` on arbitrary trees
     (`tbm_retag_ptr_fnEntry_frozen_reader_noWritable_vs_writable`: the standard
     `FnEntry` implicit write disables every foreign `.Frozen` reader on the
     WHOLE retagged range at entry, `#[rustc_no_writable]` leaves it intact),
     **symbolic
     `<[T]>::get_mut` and `split_at_mut` disjoint sub-slice soundness** on real
     `TreeBorrowsMemory` for arbitrary slice lengths `N` and disjoint windows
     (`tbm_slice_disjoint_getMut_sound`: two sub-slices reborrowed from the
     allocation root, and a `#[rustc_no_writable]` outer `&mut [T]` written on
     one sub-range), and **multi-window per-byte refinement `TreeSimInvMulti`**
     removing the single-window restriction of `TreeSimInv` for `load` / `store`
     on disjoint sub-slice trees (`tbm_load_simulates_execWorldRangeRead_multi`,
     `tbm_store_simulates_execWorldRangeWrite_multi`,
     `treeSimInvMulti_preserved_on_disjoint_window`, and closed canary proving
     `¬ TreeSimInv` while `TreeSimInvMulti` holds and steps in lockstep on both
     disjoint sub-slices).

5. **Part 5 (`#[rustc_no_writable]` Edge Cases & `MachTB` Witnesses)**: the
   `<[T]>::get_mut` wide-slice pattern, the NESTED two-sub-slice `split_at_mut`
   witness below a `#[rustc_no_writable]` vs. standard outer `&mut [u8]`
   (`tbm_nestedSplitAtMut_noWritable_vs_writable`, a closed witness on an 8-byte
   slice), the `ReservedFrz { conflicted: true }` lifecycle, a foreign active
   strong protector on overlapping bytes (`TBM` and `MachTB`), read-only
   allocations, overlapping-range frame-exit order / implicit protector-end
   access separation on `TreeBorrowsMemory.end_call`, end-to-end `MachTB` witness
   for `Box<u32>` `Protected::Weak` vs. `&mut u32` / `&u32` `Protected::Strong`
   `IntrinsicOp.Deallocate` (`machTB_box_weak_vs_mut_strong_dealloc_e2e`), the
   fuel-universal alignment of the `stepMirFnWithParamMap` adapter with the
   trusted `stepMirFn` (`runMirWithParamMap_eq_runMirDirect_of_rustcNoWritable`,
   `trusted_stepMirFn_forgetStyle_separation_all_fuel`), and the kernel of
   `permToMiniRust`.

6. **Part 6 (Full-Domain Symbolic Static-Retag Theorem & Choice-Free Symbolic
   `MachTB.wfLive` Preservation)**:
   - **6.1–6.3**: symbolic retag + store on arbitrary `StaticCellsValid` layouts
     (any field order, zero-sized `UnsafeCell<()>` at any offset), field-order
     independence and zero-length cell irrelevance of `cells_to_freeze_mask`.
   - **6.4**: **full-domain two-way `iff` for ALIGNED write pointers**
     (`tbm_staticPreserved_retag_then_store_full_iff`), removing the `wLen ≠ 0`,
     in-bounds, and `.mut` side conditions (zero-length stores, out-of-bounds
     `wOff + wBytes.length > desc.totalByteSize`, syntactic `Freeze` `.not` vs.
     `.mut` statics, and erased raw access); the **alignment boundary**
     (`tbm_store_misaligned_ub`,
     `tbm_staticPreserved_retag_then_store_iff_aligned_and_miri`: MiniRust
     rejects a misaligned store first, even of zero bytes, where the Anneal
     models answer `.ok`); plus **choice-free symbolic `MachTB.wfLive`
     preservation** (`evalIntrinsicM_tb_wfLive_choiceFree`,
     `evalReturnM_tb_wfLive_choiceFree`, `evalTerminatorM_tb_wfLive_choiceFree`,
     `stepTB_wfLive_choiceFree`, `stepsTB_wfLive_choiceFree`,
     `machTB_staticAccess_steps_wfLive`, `machTB_harnesses_steps_wfLive`, and
     closed canaries).

7. **Axiom pins**: `#guard_msgs (whitespace := lax) in #print axioms` for EVERY
   public theorem of this file: each uses at most `{propext, Quot.sound}`
   (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).

## Scope of the whole-tree results

- Single-window `TreeSimInv` (Sections 4.3–4.8) relates the two models on one
  byte window overlapped by every Anneal node's coarse range; the retag and
  frame-exit simulations are stated for that window and one allocation.
  Multi-window `TreeSimInvMulti` and the byte-local frame laws (Section 4.10)
  lift the restriction for `load` / `store` on disjoint sub-slice trees
  (`<[T]>::get_mut` / `split_at_mut`), where `TreeSimInv` itself cannot hold;
  the NESTED sub-slice retag / frame-exit scenario is covered by the frame
  laws, the symbolic sibling-reader theorem, and the closed witness of Part 5,
  not by a symbolic `TreeSimInvMulti` retag / frame-exit theorem.
- The access, retag, and frame-exit simulations assume that the Anneal ancestor
  set coincides with the MiniRust path-prefix relation (`hloc`) and that pinned
  Miri's `SkipSelfAndChildren` pruning is INERT: every node the Anneal model
  skips is unchanged by the foreign step it skips (`foreignStepInert`,
  `FrameExitPruneInert`). Pruning may be active and borrow trees may be
  arbitrarily deep (`canary_pruneInert_deepTree_load_and_retag`), and inertness
  cannot be dropped (`pruneInert_necessary_separation`); both hypotheses are
  decidable on concrete worlds and discharged in the canaries.
- The `Trusted` connection is a run-level statement: the parameter-map adapter
  coincides with the trusted `stepMirFn` at every fuel under an
  all-`rustcNoWritable` map; the `writableChildWrite` side runs through the
  Anneal-side adapter, and the `MachTB` and `Trusted` runs of the witness
  program are related by their observable outcomes, not by a step simulation.
- Symbolic `MachTB.wfLive` preservation across arbitrary `stepsTB n` executions
  is proved choice-free in Section 6.4 (`stepsTB_wfLive_choiceFree`,
  `machTB_staticAccess_steps_wfLive`, `machTB_harnesses_steps_wfLive`): it is a
  preservation result for non-faulting runs; that the canonical static shapes
  do run to completion is established by the closed `MachTB` witnesses of
  Parts 2 and 6.
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

/-- **Protector-kind correspondence (`protToMiniRust`)**: across EVERY
`RefParamKind` (`&T`, `&mut T`, `Box<T>`), every `ParamTypeFacts` (including
`!Unpin` skip-retag), and every `ParamRetagAttrs`, the protector minted by
MiniRust's `ReborrowSettings.new` coincides with `protToMiniRust` applied to
`MiriRetagPolicyMirror.create`'s protector (`Strong`, `Weak`, or skipped). -/
theorem reborrowSettings_prot_eq_protToMiniRust
    {Provenance : Type}
    (lookup : Gen.ThinPointer Provenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Provenance)
    (facts : ParamTypeFacts) (kind : RefParamKind) (attrs : ParamRetagAttrs)
    (size align : Nat) (cells : List (Gen.Offset × LibSpecr.Size)) (mask : List Bool)
    (hmask : cellsToFreezeMask cells ⟨size⟩ = .ok mask) :
    let info := pointeeInfoOfFacts facts size align cells
    (ReborrowSettings.new lookup ptr (ptrTypeOfParamKind kind info) true
        ⟨attrs.implicitWrites⟩ (!attrs.rustcNoWritable)).map
      (fun opt => opt.map (·.«protected»)) =
    .ok ((MiriRetagPolicyMirror.create facts kind .fnEntry attrs).map
      (fun p => protToMiniRust p.protector)) := by
  cases kind with
  | shared =>
    dsimp only
    have hsh := reborrowSettings_fnEntry_shared_eq_create lookup ptr facts attrs size align cells
      mask hmask
    rw [hsh.1]
    simp [Except.map, MiriRetagPolicyMirror.create, protToMiniRust]
  | mutable =>
    dsimp only
    have hmb := reborrowSettings_fnEntry_mutOrBox_eq_policy lookup ptr facts .mutable attrs
      (by decide) size align cells mask hmask
    rw [hmb]
    rcases facts with ⟨u, uu, frz⟩
    rcases attrs with ⟨iw, rnw⟩
    cases hu : (u && uu) with
    | false =>
      simp [Except.map, selectFnEntryPolicy, MiriRetagPolicyMirror.create, hu]
    | true =>
      cases iw <;> cases rnw <;>
        simp [Except.map, selectFnEntryPolicy, MiriRetagPolicyMirror.create, protToMiniRust, hu]
  | box =>
    dsimp only
    have hmb := reborrowSettings_fnEntry_mutOrBox_eq_policy lookup ptr facts .box attrs
      (by decide) size align cells mask hmask
    rw [hmb]
    rcases facts with ⟨u, uu, frz⟩
    rcases attrs with ⟨iw, rnw⟩
    cases hu : (u && uu) with
    | false =>
      simp [Except.map, selectFnEntryPolicy, MiriRetagPolicyMirror.create, hu]
    | true =>
      cases iw <;> cases rnw <;>
        simp [Except.map, selectFnEntryPolicy, MiriRetagPolicyMirror.create, protToMiniRust, hu]


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

/-- Under an all-`rustcNoWritable` map, `stepMirFnWithParamMap` equals `Trusted`
`stepMirFn` unconditionally across both root and callee frames (the
`FnParamRetagMap.empty .rustcNoWritable` instance of
`stepMirFnWithParamMap_eq_stepMirFn_of_rustcNoWritable_at_pc`). -/
theorem stepMirFnWithParamMap_rustcNoWritable_eq_stepMirFn
    (body : CapturedMir) (s : MachineState) :
    stepMirFnWithParamMap (FnParamRetagMap.empty .rustcNoWritable) body s =
      stepMirFn body s :=
  stepMirFnWithParamMap_eq_stepMirFn_of_rustcNoWritable_at_pc _ body s (fun _ _ _ _ _ => rfl)

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
  with `.ub`. This side is a run of the Anneal-side adapter
  `stepMirFnWithParamMap`, NOT of the trusted `stepMirFn`, which never reports
  UB on this program (`trusted_stepMirFn_forgetStyle_separation_all_fuel`). -/
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

/-- Whether the FOREIGN step of an access of kind `isWrite` on `[off, off + len)`
leaves the Anneal node `n` unchanged. On a node skipped by pinned Miri's
`SkipSelfAndChildren` pruning (`isPrunedForeignNode`) this is exactly the
condition under which the pruned Anneal model and the unpruned MiniRust tree
access agree, so the whole-tree simulations assume it for PRUNED nodes only
("pruning is inert"); it holds vacuously when no node is pruned. -/
def foreignStepInert (ap : List Nat) (isWrite : Bool) (off len : Nat) (n : TreeTagNode) : Bool :=
  match stepNodeOnRangeAccess ap isWrite false off len n with
  | .ok n' => decide (n' = n)
  | .error _ => false

private theorem nwsr_foreignStepInert_read {ap : List Nat} {off len : Nat} {n : TreeTagNode}
    (h : foreignStepInert ap false off len n = true) :
    stepNodeOnRangeRead ap false off len n = .ok n := by
  unfold foreignStepInert stepNodeOnRangeAccess at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hs : stepNodeOnRangeRead ap false off len n with
  | error e => rw [hs] at h; cases h
  | ok n' => rw [hs] at h; rw [of_decide_eq_true h]

private theorem nwsr_foreignStepInert_write {ap : List Nat} {off len : Nat} {n : TreeTagNode}
    (h : foreignStepInert ap true off len n = true) :
    stepNodeOnRangeWrite ap false off len n = .ok n := by
  unfold foreignStepInert stepNodeOnRangeAccess at h
  simp only [↓reduceIte] at h
  cases hs : stepNodeOnRangeWrite ap false off len n with
  | error e => rw [hs] at h; cases h
  | ok n' => rw [hs] at h; rw [of_decide_eq_true h]

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
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) isWrite off len n = true →
      step false n = .ok n) :
    (∀ nodes', ListRel (PrunedStepRel w tag isWrite off len step) w.nodes nodes' →
      ∃ t', Node.access t (some (emb tag)) k ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInv off len emb { w with nodes := nodes' } t') ∧
    ((∀ nodes', ¬ ListRel (PrunedStepRel w tag isWrite off len step) w.nodes nodes') →
      ∃ msg, Node.access t (some (emb tag)) k ⟨off⟩ ⟨len⟩ = .error (.ub msg)) := by
  -- Locality bridge: `PrunedStepRel` is exactly the path-determined step.
  have hpr : ∀ n ∈ w.nodes, ∀ n', PrunedStepRel w tag isWrite off len step n n' →
      step (locOf (some (emb tag)) (emb n.tag)) n = .ok n' := by
    intro n hn n' hrel
    rcases hrel with ⟨hc, hs⟩ | ⟨hc, hp, hEq⟩ | ⟨hc, _, hs⟩
    · rw [← hloc n hn, hc]; exact hs
    · rw [← hloc n hn, hc, hEq]; exact hnoprune n hn hp
    · rw [← hloc n hn, hc]; exact hs
  have hrp : ∀ n ∈ w.nodes, ∀ n', step (locOf (some (emb tag)) (emb n.tag)) n = .ok n' →
      PrunedStepRel w tag isWrite off len step n n' := by
    intro n hn n' hs
    cases hl : locOf (some (emb tag)) (emb n.tag) with
    | true => rw [hl] at hs; exact Or.inl ⟨by rw [hloc n hn, hl], hs⟩
    | false =>
      rw [hl] at hs
      cases hp : isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) isWrite off len n with
      | false => exact Or.inr (Or.inr ⟨by rw [hloc n hn, hl], hp, hs⟩)
      | true =>
        rw [hnoprune n hn hp] at hs
        cases hs
        exact Or.inr (Or.inl ⟨by rw [hloc n hn, hl], hp, rfl⟩)
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
inert (`hnoprune`: every pruned node is unchanged by the foreign step it skips,
`foreignStepInert`; this holds in particular whenever no node is pruned, the
hypothesis of
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
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) false off len n = true →
      foreignStepInert w.activeProtectors false off len n = true) :
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
    hloc (fun n hn hp => nwsr_foreignStepInert_read (hnoprune n hn hp))
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
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) true off len n = true →
      foreignStepInert w.activeProtectors true off len n = true) :
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
    hloc (fun n hn hp => nwsr_foreignStepInert_write (hnoprune n hn hp))
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
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) true off bytes.length n = true →
      foreignStepInert w.activeProtectors true off bytes.length n = true) :
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
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) false off len n = true →
      foreignStepInert w.activeProtectors false off len n = true) :
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

/-! #### Whole-Tree Retag Helpers -/

private theorem a1_listMutateAt_natCast {T O : Type} (xs : List T) (i : Nat) (what : String)
    (f : T → Interp (O × T)) (x : T) (hx : xs[i]? = some x) :
    listMutateAt xs (i : Int) what f = (f x >>= fun r => pure (r.1, xs.set i r.2)) := by
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hx).1
  have hnn : (0 : Int) ≤ (i : Int) := Int.natCast_nonneg i
  have htn : ((i : Int)).toNat = i := rfl
  unfold listMutateAt listIndex listSet
  simp only [hnn, htn, hx, hlt, and_self, ↓reduceIte, bind, Except.bind, pure, Except.pure]

/-! ### 4.6 Path-Indexed Whole-Tree Calculus for `Node.access_node`, `Node.add_node`, & `reborrowInitAccess` -/

private theorem a1_int_beq_self (i : Int) : (i == i) = true := by
  simp [BEq.beq]

private theorem a1_int_beq_iff (a b : Int) : (a == b) = true ↔ a = b := by
  simp [BEq.beq]

private theorem a1_isPrefixOf_append_right :
    ∀ (p suf : Gen.Path), p.isPrefixOf (p ++ suf) = true
  | [], _ => rfl
  | a :: rest, suf => by
    simp only [List.cons_append, List.isPrefixOf, a1_int_beq_self, Bool.true_and]
    exact a1_isPrefixOf_append_right rest suf

private theorem a1_isPrefixOf_eq_append :
    ∀ (p q : Gen.Path), p.isPrefixOf q = true → ∃ suf, q = p ++ suf
  | [], q, _ => ⟨q, rfl⟩
  | _ :: _, [], h => by cases h
  | a :: ps, b :: qs, h => by
    simp only [List.isPrefixOf, Bool.and_eq_true, a1_int_beq_iff] at h
    obtain ⟨rfl, hrest⟩ := h
    obtain ⟨suf, rfl⟩ := a1_isPrefixOf_eq_append ps qs hrest
    exact ⟨suf, rfl⟩

private theorem a1_isPrefixOf_append_singleton_iff :
    ∀ (p q : Gen.Path) (k : Int),
      q.isPrefixOf (p ++ [k]) = true ↔ q.isPrefixOf p = true ∨ q = p ++ [k]
  | [], [], _ => by simp [List.isPrefixOf]
  | [], a :: [], k => by simp [List.isPrefixOf]
  | [], _ :: _ :: _, _ => by simp [List.isPrefixOf]
  | _ :: _, [], _ => by simp [List.isPrefixOf]
  | h :: tl, a :: rest, k => by
    simp only [List.cons_append, List.isPrefixOf, Bool.and_eq_true, a1_int_beq_iff, List.cons.injEq]
    constructor
    · rintro ⟨rfl, hr⟩
      rcases (a1_isPrefixOf_append_singleton_iff tl rest k).mp hr with h1 | rfl
      · exact Or.inl ⟨rfl, h1⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, h1⟩ | ⟨rfl, rfl⟩)
      · exact ⟨rfl, (a1_isPrefixOf_append_singleton_iff tl rest k).mpr (Or.inl h1)⟩
      · exact ⟨rfl, (a1_isPrefixOf_append_singleton_iff tl (tl ++ [k]) k).mpr (Or.inr rfl)⟩

private theorem a1_nodeAt_append :
    ∀ (p : Gen.Path) (n : Gen.Node) (suf : Gen.Path),
      nodeAt n (p ++ suf) = (nodeAt n p).bind (fun m => nodeAt m suf)
  | [], _, _ => rfl
  | i :: rest, ⟨cs, ps, pr⟩, suf => by
    rcases Decidable.em (0 ≤ i) with hi | hi
    · cases hc : cs[i.toNat]? with
      | none =>
        rw [List.cons_append, nwsr_nodeAt_cons_none cs ps pr i (rest ++ suf) hi hc,
          nwsr_nodeAt_cons_none cs ps pr i rest hi hc]
        rfl
      | some c =>
        rw [List.cons_append, nwsr_nodeAt_cons_some cs ps pr i (rest ++ suf) c hi hc,
          nwsr_nodeAt_cons_some cs ps pr i rest c hi hc]
        exact a1_nodeAt_append rest c suf
    · rw [List.cons_append, nwsr_nodeAt_cons_neg cs ps pr i (rest ++ suf) hi,
        nwsr_nodeAt_cons_neg cs ps pr i rest hi]
      rfl

/-- **Automatic locality invariance under fresh child insertion**: appending a
fresh child index `p.children.length` to `parentPath` yields a `childPath` whose
`locOf (some childPath)` agrees with `locOf (some parentPath)` on EVERY
pre-existing node path `q` in the tree. -/
theorem locOf_childPath_eq_parentPath (t : Gen.Node) (parentPath q : Gen.Path)
    (p m : Gen.Node) (hp : nodeAt t parentPath = some p) (hm : nodeAt t q = some m) :
    locOf (some (parentPath ++ [(p.children.length : Int)])) q = locOf (some parentPath) q := by
  rw [locOf_some_eq_isPrefixOf, locOf_some_eq_isPrefixOf]
  cases hq : q.isPrefixOf parentPath with
  | true =>
    exact (a1_isPrefixOf_append_singleton_iff parentPath q (p.children.length : Int)).mpr
      (Or.inl hq)
  | false =>
    cases hqc : q.isPrefixOf (parentPath ++ [(p.children.length : Int)]) with
    | false => rfl
    | true =>
      exfalso
      rcases (a1_isPrefixOf_append_singleton_iff parentPath q (p.children.length : Int)).mp hqc with
        h1 | rfl
      · rw [h1] at hq; cases hq
      · rw [a1_nodeAt_append, hp] at hm
        have hnn : (0 : Int) ≤ (p.children.length : Int) := Int.natCast_nonneg _
        have hnone : p.children[((p.children.length : Int)).toNat]? = none :=
          List.getElem?_eq_none (Nat.le_refl _)
        have hna : nodeAt p [(p.children.length : Int)] = none := by
          cases p with
          | mk cs ps pr => exact nwsr_nodeAt_cons_none cs ps pr (cs.length : Int) [] hnn hnone
        simp only [Option.bind_some, hna] at hm
        cases hm

/-- **Whole-tree path-indexed specification of `Node.access_node`**. -/
theorem node_access_node_spec {O : Type} (f : Gen.Node → Interp (O × Gen.Node)) :
    ∀ (path : Gen.Path) (root target target' : Gen.Node) (out : O),
      nodeAt root path = some target →
      f target = .ok (out, target') →
      ∃ root', Node.access_node f path root = .ok (out, root') ∧
        (∀ suf, nodeAt root' (path ++ suf) = nodeAt target' suf) ∧
        (∀ q, path.isPrefixOf q = false →
          (nodeAt root q = none → nodeAt root' q = none) ∧
          (∀ m, nodeAt root q = some m →
            ∃ m', nodeAt root' q = some m' ∧
              m'.permissions = m.permissions ∧ m'.«protected» = m.«protected» ∧
              (q.isPrefixOf path = false → m' = m)))
  | [], root, target, target', out, hna, hf => by
    cases hna
    refine ⟨target', hf, fun _ => rfl, fun q hpre => ?_⟩
    cases hpre
  | i :: rest, ⟨cs, ps, pr⟩, target, target', out, hna, hf => by
    rcases Decidable.em (0 ≤ i) with hi | hi
    · cases hc : cs[i.toNat]? with
      | none =>
        rw [nwsr_nodeAt_cons_none cs ps pr i rest hi hc] at hna
        cases hna
      | some c =>
        rw [nwsr_nodeAt_cons_some cs ps pr i rest c hi hc] at hna
        obtain ⟨c', hc', hsuf, hother⟩ :=
          node_access_node_spec f rest c target target' out hna hf
        have hlt : i.toNat < cs.length := (List.getElem?_eq_some_iff.mp hc).1
        have hnotLeaf : Node.is_leaf ⟨cs, ps, pr⟩ = false := by
          unfold Node.is_leaf
          cases cs with
          | nil => simp at hlt
          | cons _ _ => rfl
        have hiof : (i.toNat : Int) = i := Int.toNat_of_nonneg hi
        have hmut : listMutateAt cs i "Node::access_node" (Node.access_node f rest) =
            .ok (out, cs.set i.toNat c') := by
          rw [← hiof, a1_listMutateAt_natCast cs i.toNat "Node::access_node"
            (Node.access_node f rest) c hc, hc']
          rfl
        refine ⟨⟨cs.set i.toNat c', ps, pr⟩, ?_, ?_, ?_⟩
        · unfold Node.access_node
          simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hmut, bind, Except.bind,
            pure, Except.pure]
        · intro suf
          rw [List.cons_append, nwsr_nodeAt_cons_some (cs.set i.toNat c') ps pr i (rest ++ suf) c'
            hi (List.getElem?_set_self hlt)]
          exact hsuf suf
        · intro q hpre
          cases q with
          | nil =>
            refine ⟨fun hn => (by cases hn), fun m hm => ?_⟩
            cases hm
            refine ⟨⟨cs.set i.toNat c', ps, pr⟩, rfl, rfl, rfl, fun hqp => (by cases hqp)⟩
          | cons j qrest =>
            rcases Decidable.em (i = j) with hji | hji
            · subst hji
              have hrpre : rest.isPrefixOf qrest = false := by
                simp only [List.isPrefixOf, a1_int_beq_self, Bool.true_and] at hpre
                exact hpre
              have hr := hother qrest hrpre
              refine ⟨fun hn => ?_, fun m hm => ?_⟩
              · rw [nwsr_nodeAt_cons_some cs ps pr i qrest c hi hc] at hn
                rw [nwsr_nodeAt_cons_some (cs.set i.toNat c') ps pr i qrest c' hi
                  (List.getElem?_set_self hlt)]
                exact hr.1 hn
              · rw [nwsr_nodeAt_cons_some cs ps pr i qrest c hi hc] at hm
                obtain ⟨m', hm', hp1, hp2, hdisj⟩ := hr.2 m hm
                refine ⟨m', ?_, hp1, hp2, fun hqp => ?_⟩
                · rw [nwsr_nodeAt_cons_some (cs.set i.toNat c') ps pr i qrest c' hi
                    (List.getElem?_set_self hlt)]
                  exact hm'
                · simp only [List.isPrefixOf, a1_int_beq_self, Bool.true_and] at hqp
                  exact hdisj hqp
            · have hsame : nodeAt ⟨cs.set i.toNat c', ps, pr⟩ (j :: qrest) =
                  nodeAt ⟨cs, ps, pr⟩ (j :: qrest) := by
                rcases Decidable.em (0 ≤ j) with hj | hj
                · have hneNat : i.toNat ≠ j.toNat := by
                    intro h; apply hji
                    have h1 : (i.toNat : Int) = i := Int.toNat_of_nonneg hi
                    have h2 : (j.toNat : Int) = j := Int.toNat_of_nonneg hj
                    rw [h] at h1
                    exact h1.symm.trans h2
                  simp only [nodeAt, hj, ↓reduceIte, List.getElem?_set_ne hneNat]
                · simp only [nodeAt, hj, ↓reduceIte]
              rw [hsame]
              exact ⟨id, fun m hm => ⟨m, hm, rfl, rfl, fun _ => rfl⟩⟩
    · rw [nwsr_nodeAt_cons_neg cs ps pr i rest hi] at hna
      cases hna

/-- **Whole-tree specification of `Node.add_node`**. -/
theorem node_add_node_spec (root p child : Gen.Node) (parentPath : Gen.Path)
    (hp : nodeAt root parentPath = some p) (hleaf : child.children = []) :
    let childPath := parentPath ++ [(p.children.length : Int)]
    ∃ root', Node.add_node root parentPath child = .ok (childPath, root') ∧
      nodeAt root' childPath = some child ∧
      (∀ q m, nodeAt root q = some m →
        ∃ m', nodeAt root' q = some m' ∧
          m'.permissions = m.permissions ∧ m'.«protected» = m.«protected») ∧
      (∀ q m', nodeAt root' q = some m' →
        (q = childPath ∧ m' = child) ∨
        ∃ m, nodeAt root q = some m ∧
          m'.permissions = m.permissions ∧ m'.«protected» = m.«protected») := by
  let childIdx : Int := (p.children.length : Int)
  let childPath : Gen.Path := parentPath ++ [childIdx]
  let p' : Gen.Node := { p with children := p.children ++ [child] }
  obtain ⟨root', hacc, hsuf, hother⟩ :=
    node_access_node_spec
      (fun node => pure ((node.children.length : Int), { node with children := node.children ++ [child] }))
      parentPath root p p' childIdx hp rfl
  have hadd : Node.add_node root parentPath child = .ok (childPath, root') := by
    unfold Node.add_node
    rw [hacc]
    rfl
  have hchildAt : nodeAt root' childPath = some child := by
    show nodeAt root' (parentPath ++ [childIdx]) = some child
    rw [hsuf [childIdx]]
    have hnn : (0 : Int) ≤ childIdx := Int.natCast_nonneg _
    have hget : (p.children ++ [child])[childIdx.toNat]? = some child := by
      have ht : childIdx.toNat = p.children.length := rfl
      rw [ht, List.getElem?_append_right (Nat.le_refl _)]
      simp
    cases p with
    | mk cs ps pr => exact nwsr_nodeAt_cons_some (cs ++ [child]) ps pr childIdx [] child hnn hget
  refine ⟨root', hadd, hchildAt, ?_, ?_⟩
  · intro q m hq
    cases hpre : parentPath.isPrefixOf q with
    | false =>
      obtain ⟨m', hm', hp1, hp2, _⟩ := (hother q hpre).2 m hq
      exact ⟨m', hm', hp1, hp2⟩
    | true =>
      obtain ⟨suf, rfl⟩ := a1_isPrefixOf_eq_append parentPath q hpre
      rw [a1_nodeAt_append, hp] at hq
      simp only [Option.bind_some] at hq
      rw [hsuf suf]
      cases suf with
      | nil =>
        cases hq
        exact ⟨p', rfl, rfl, rfl⟩
      | cons j s =>
        rcases Decidable.em (0 ≤ j) with hj | hj
        · cases hcj : p.children[j.toNat]? with
          | none =>
            cases p with
            | mk cs ps pr =>
              rw [nwsr_nodeAt_cons_none cs ps pr j s hj hcj] at hq
              cases hq
          | some c =>
            have hlt : j.toNat < p.children.length := (List.getElem?_eq_some_iff.mp hcj).1
            have hcj' : (p.children ++ [child])[j.toNat]? = some c := by
              rw [List.getElem?_append_left hlt]; exact hcj
            cases p with
            | mk cs ps pr =>
              rw [nwsr_nodeAt_cons_some cs ps pr j s c hj hcj] at hq
              rw [nwsr_nodeAt_cons_some (cs ++ [child]) ps pr j s c hj hcj', hq]
              exact ⟨m, rfl, rfl, rfl⟩
        · cases p with
          | mk cs ps pr =>
            rw [nwsr_nodeAt_cons_neg cs ps pr j s hj] at hq
            cases hq
  · intro q m' hq'
    cases hpre : parentPath.isPrefixOf q with
    | false =>
      cases hq : nodeAt root q with
      | none =>
        rw [(hother q hpre).1 hq] at hq'
        cases hq'
      | some m =>
        obtain ⟨m'', hm'', hp1, hp2, _⟩ := (hother q hpre).2 m hq
        rw [hm''] at hq'
        cases hq'
        exact Or.inr ⟨m, rfl, hp1, hp2⟩
    | true =>
      obtain ⟨suf, rfl⟩ := a1_isPrefixOf_eq_append parentPath q hpre
      rw [hsuf suf] at hq'
      cases suf with
      | nil =>
        cases hq'
        exact Or.inr ⟨p, by rw [List.append_nil]; exact hp, rfl, rfl⟩
      | cons j s =>
        rcases Decidable.em (0 ≤ j) with hj | hj
        · rcases Decidable.em (j.toNat < p.children.length) with hlt | hlt
          · have hcj' : (p.children ++ [child])[j.toNat]? = p.children[j.toNat]? :=
              List.getElem?_append_left hlt
            cases hcj : p.children[j.toNat]? with
            | none =>
              rw [List.getElem?_eq_none_iff] at hcj
              exfalso; omega
            | some c =>
              rw [hcj] at hcj'
              have hq : nodeAt root (parentPath ++ j :: s) = some m' := by
                rw [a1_nodeAt_append, hp]
                simp only [Option.bind_some]
                cases p with
                | mk cs ps pr =>
                  rw [nwsr_nodeAt_cons_some cs ps pr j s c hj hcj]
                  rw [nwsr_nodeAt_cons_some (cs ++ [child]) ps pr j s c hj hcj'] at hq'
                  exact hq'
              exact Or.inr ⟨m', hq, rfl, rfl⟩
          · rcases Decidable.em (j.toNat = p.children.length) with heq | heq
            · have hji : j = childIdx := by
                have h1 : ((j.toNat : Nat) : Int) = j := Int.toNat_of_nonneg hj
                rw [heq] at h1
                exact h1.symm
              have hcj' : (p.children ++ [child])[j.toNat]? = some child := by
                rw [heq, List.getElem?_append_right (Nat.le_refl _)]
                simp
              cases p with
              | mk cs ps pr =>
                rw [nwsr_nodeAt_cons_some (cs ++ [child]) ps pr j s child hj hcj'] at hq'
                cases s with
                | nil =>
                  cases hq'
                  exact Or.inl ⟨by rw [hji], rfl⟩
                | cons k s' =>
                  cases child with
                  | mk ccs cps cpr =>
                    simp only at hleaf
                    subst hleaf
                    rcases Decidable.em (0 ≤ k) with hk | hk
                    · rw [nwsr_nodeAt_cons_none [] cps cpr k s' hk (by simp)] at hq'
                      cases hq'
                    · rw [nwsr_nodeAt_cons_neg [] cps cpr k s' hk] at hq'
                      cases hq'
            · have hgt : (p.children ++ [child]).length ≤ j.toNat := by
                rw [List.length_append, List.length_singleton]; omega
              have hnone : (p.children ++ [child])[j.toNat]? = none := List.getElem?_eq_none hgt
              cases p with
              | mk cs ps pr =>
                rw [nwsr_nodeAt_cons_none (cs ++ [child]) ps pr j s hj hnone] at hq'
                cases hq'
        · cases p with
          | mk cs ps pr =>
            rw [nwsr_nodeAt_cons_neg (cs ++ [child]) ps pr j s hj] at hq'
            cases hq'

/-- Post-state relation of `TreeBorrowsMemory.reborrowInitAccess`. -/
def InitAccessPost (childPath : Gen.Path) (baseOff : Nat) (perms : List Gen.Permission)
    (n n' : Gen.Node) : Prop :=
  ∀ q,
    (nodeAt n q = none → nodeAt n' q = none) ∧
    (∀ m, nodeAt n q = some m →
      ∃ m', nodeAt n' q = some m' ∧ m'.«protected» = m.«protected» ∧
        m'.permissions.length = m.permissions.length ∧
        (∀ b, b < baseOff ∨ baseOff + perms.length ≤ b → m'.permissions[b]? = m.permissions[b]?) ∧
        (∀ i < perms.length, ∀ pm, perms[i]? = some pm → ∀ p, m.permissions[baseOff + i]? = some p →
          match Permission.init_access pm with
          | none => m'.permissions[baseOff + i]? = some p
          | some k => ∃ p', Permission.transition p k (locRel (some childPath) q) = .ok p' ∧
              m'.permissions[baseOff + i]? = some p'))

/-- Forward whole-tree specification of `TreeBorrowsMemory.reborrowInitAccess`. -/
theorem reborrowInitAccess_ok_of_pointwise (childPath : Gen.Path) (off : Nat) :
    ∀ (perms : List Gen.Permission) (idx : Nat) (root : Gen.Node),
      (∀ q m, nodeAt root q = some m → ∀ i < perms.length, ∀ pm, perms[i]? = some pm →
        ∀ k, Permission.init_access pm = some k →
          ∃ p p', m.permissions[off + idx + i]? = some p ∧
            Permission.transition p k (locRel (some childPath) q) = .ok p') →
      ∃ root', TreeBorrowsMemory.reborrowInitAccess childPath ⟨off⟩ idx perms root = .ok root' ∧
        InitAccessPost childPath (off + idx) perms root root'
  | [], idx, root, _ => by
    refine ⟨root, rfl, fun q => ⟨id, fun m hm => ⟨m, hm, rfl, rfl, fun _ _ => rfl,
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩⟩
  | pm :: rest, idx, root, h => by
    cases hk : Permission.init_access pm with
    | none =>
      have hrest : ∀ q m, nodeAt root q = some m → ∀ i < rest.length, ∀ pm', rest[i]? = some pm' →
          ∀ k, Permission.init_access pm' = some k →
            ∃ p p', m.permissions[off + (idx + 1) + i]? = some p ∧
              Permission.transition p k (locRel (some childPath) q) = .ok p' := by
        intro q m hm i hi pm' hpm' k hk'
        have e : off + (idx + 1) + i = off + idx + (i + 1) := by omega
        rw [e]
        exact h q m hm (i + 1) (by simp; omega) pm' (by rw [List.getElem?_cons_succ]; exact hpm') k hk'
      obtain ⟨root', hrun, hpost⟩ := reborrowInitAccess_ok_of_pointwise childPath off rest (idx + 1)
        root hrest
      refine ⟨root', ?_, ?_⟩
      · rw [TreeBorrowsMemory.reborrowInitAccess, hk]
        exact hrun
      · intro q
        obtain ⟨hnone, hsome⟩ := hpost q
        refine ⟨hnone, fun m hm => ?_⟩
        obtain ⟨m', hm', hprot, hlen, hout, hin⟩ := hsome m hm
        refine ⟨m', hm', hprot, hlen, fun b hb => hout b (by simp at hb; omega), ?_⟩
        intro i hi pm' hpm' p hp
        cases i with
        | zero =>
          rw [List.getElem?_cons_zero] at hpm'
          cases hpm'
          rw [hk]
          exact (hout (off + idx) (Or.inl (by omega))).trans hp
        | succ i =>
          rw [List.getElem?_cons_succ] at hpm'
          have e : off + idx + (i + 1) = off + (idx + 1) + i := by omega
          rw [e] at hp ⊢
          exact hin i (by simp at hi; omega) pm' hpm' p hp
    | some k =>
      have h1point : ∀ q m, nodeAt root q = some m →
          ∃ ps', Node.transitionRange (locRel (some childPath) q) k (off + idx) 1 m.permissions =
            .ok ps' := by
        intro q m hm
        obtain ⟨p, p', hp, htr⟩ := h q m hm 0 (by simp) pm rfl k hk
        obtain ⟨ps', htrR, _⟩ := transitionRange_ok_of_pointwise
          (locRel (some childPath) q) k 1 (off + idx) m.permissions (fun b hb1 hb2 => by
            have hb : b = off + idx := by omega
            rw [hb]
            exact ⟨p, p', hp, htr⟩)
        exact ⟨ps', htrR⟩
      obtain ⟨root1, hacc1, hpost1⟩ :=
        node_access_ok_of_pointwise k (off + idx) 1 root (some childPath) h1point
      have h1detail : ∀ q m, nodeAt root q = some m →
          ∃ m1, nodeAt root1 q = some m1 ∧ m1.«protected» = m.«protected» ∧
            m1.permissions.length = m.permissions.length ∧
            (∀ b, b ≠ off + idx → m1.permissions[b]? = m.permissions[b]?) ∧
            (∀ p, m.permissions[off + idx]? = some p →
              ∃ p', Permission.transition p k (locRel (some childPath) q) = .ok p' ∧
                m1.permissions[off + idx]? = some p') := by
        intro q m hm
        obtain ⟨m1, hm1, hprot1, htr1⟩ := (hpost1 q).1 m hm
        obtain ⟨p0, p0', hp0, htr0⟩ := h q m hm 0 (by simp) pm rfl k hk
        obtain ⟨ps', hrun', hlen', hout', hin'⟩ := transitionRange_ok_of_pointwise
          (locRel (some childPath) q) k 1 (off + idx) m.permissions (fun b hb1 hb2 => by
            have hb : b = off + idx := by omega
            rw [hb]
            exact ⟨p0, p0', hp0, htr0⟩)
        rw [htr1] at hrun'
        cases hrun'
        exact ⟨m1, hm1, hprot1, hlen',
          fun b hb => hout' b (by omega),
          fun p hp => hin' (off + idx) (Nat.le_refl _) (by omega) p hp⟩
      have hrest : ∀ q m1, nodeAt root1 q = some m1 → ∀ i < rest.length, ∀ pm', rest[i]? = some pm' →
          ∀ k', Permission.init_access pm' = some k' →
            ∃ p p', m1.permissions[off + (idx + 1) + i]? = some p ∧
              Permission.transition p k' (locRel (some childPath) q) = .ok p' := by
        intro q m1 hm1 i hi pm' hpm' k' hk'
        cases hqm : nodeAt root q with
        | none => rw [(hpost1 q).2 hqm] at hm1; cases hm1
        | some m =>
          obtain ⟨m1', hm1', _, _, hout1, _⟩ := h1detail q m hqm
          rw [hm1'] at hm1
          cases hm1
          have e : off + (idx + 1) + i = off + idx + (i + 1) := by omega
          rw [hout1 (off + (idx + 1) + i) (by omega), e]
          exact h q m hqm (i + 1) (by simp; omega) pm'
            (by rw [List.getElem?_cons_succ]; exact hpm') k' hk'
      obtain ⟨root', hrun, hpostR⟩ := reborrowInitAccess_ok_of_pointwise childPath off rest (idx + 1)
        root1 hrest
      refine ⟨root', ?_, ?_⟩
      · have hacc1' : Node.access root (some childPath) k (Size.add ⟨off⟩ ⟨idx⟩) ⟨1⟩ = .ok root1 :=
          hacc1
        rw [TreeBorrowsMemory.reborrowInitAccess, hk]
        simp only [bind, Except.bind, hacc1']
        exact hrun
      · intro q
        refine ⟨fun hn => (hpostR q).1 ((hpost1 q).2 hn), fun m hm => ?_⟩
        obtain ⟨m1, hm1, hprot1, hlen1, hout1, hin1⟩ := h1detail q m hm
        obtain ⟨m', hm', hprot', hlen', hout', hin'⟩ := (hpostR q).2 m1 hm1
        refine ⟨m', hm', hprot'.trans hprot1, hlen'.trans hlen1, ?_, ?_⟩
        · intro b hb
          rw [hout' b (by simp at hb; omega), hout1 b (by simp at hb; omega)]
        · intro i hi pm' hpm' p hp
          cases i with
          | zero =>
            rw [List.getElem?_cons_zero] at hpm'
            cases hpm'
            rw [hk]
            obtain ⟨p', htr', hp1⟩ := hin1 p hp
            exact ⟨p', htr', (hout' (off + idx) (Or.inl (by omega))).trans hp1⟩
          | succ i =>
            rw [List.getElem?_cons_succ] at hpm'
            have e : off + idx + (i + 1) = off + (idx + 1) + i := by omega
            rw [e] at hp ⊢
            have hp1 : m1.permissions[off + (idx + 1) + i]? = some p := by
              rw [hout1 (off + (idx + 1) + i) (by omega)]; exact hp
            exact hin' i (by simp at hi; omega) pm' hpm' p hp1

/-- Success inversion of `TreeBorrowsMemory.reborrowInitAccess`. -/
theorem reborrowInitAccess_ok_inv (childPath : Gen.Path) (off : Nat) :
    ∀ (perms : List Gen.Permission) (idx : Nat) (root root' : Gen.Node),
      TreeBorrowsMemory.reborrowInitAccess childPath ⟨off⟩ idx perms root = .ok root' →
      ∀ q m, nodeAt root q = some m → ∀ i < perms.length, ∀ pm, perms[i]? = some pm →
        ∀ k, Permission.init_access pm = some k →
          ∃ p p', m.permissions[off + idx + i]? = some p ∧
            Permission.transition p k (locRel (some childPath) q) = .ok p'
  | [], _, _, _, _, _, _, _, i, hi, _, _, _, _ => absurd hi (Nat.not_lt_zero i)
  | pm0 :: rest, idx, root, root', hrun, q, m, hm, i, hi, pm, hpm, k, hk => by
    rw [TreeBorrowsMemory.reborrowInitAccess] at hrun
    have hstep := hrun
    cases hk0 : Permission.init_access pm0 with
    | none =>
      rw [hk0] at hstep
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at hpm
        cases hpm
        rw [hk0] at hk
        cases hk
      | succ i =>
        rw [List.getElem?_cons_succ] at hpm
        have e : off + idx + (i + 1) = off + (idx + 1) + i := by omega
        rw [e]
        exact reborrowInitAccess_ok_inv childPath off rest (idx + 1) root root' hstep q m hm i
          (by simp at hi; omega) pm hpm k hk
    | some k0 =>
      rw [hk0] at hstep
      obtain ⟨root1, hacc1, hrest⟩ := nwsr_bind_ok hstep
      have hacc1' : Node.access root (some childPath) k0 ⟨off + idx⟩ ⟨1⟩ = .ok root1 := hacc1
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at hpm
        cases hpm
        rw [hk0] at hk
        cases hk
        obtain ⟨ps', htrR⟩ := node_access_ok_inv k (off + idx) 1 root root1 (some childPath)
          hacc1' q m hm
        exact transitionRange_ok_inv (locRel (some childPath) q) k 1 (off + idx) m.permissions
          ps' htrR (off + idx) (Nat.le_refl _) (by omega)
      | succ i =>
        rw [List.getElem?_cons_succ] at hpm
        have hpoint1 := node_access_ok_inv k0 (off + idx) 1 root root1 (some childPath) hacc1'
        obtain ⟨root1', hacc1'', hpost1⟩ :=
          node_access_ok_of_pointwise k0 (off + idx) 1 root (some childPath) hpoint1
        rw [hacc1'] at hacc1''
        cases hacc1''
        obtain ⟨m1, hm1, _, htrR⟩ := (hpost1 q).1 m hm
        obtain ⟨ps', htrR', _, hout1, _⟩ := transitionRange_ok_of_pointwise
          (locRel (some childPath) q) k0 1 (off + idx) m.permissions
          (transitionRange_ok_inv _ _ _ _ _ _ htrR)
        rw [htrR] at htrR'
        cases htrR'
        have e : off + idx + (i + 1) = off + (idx + 1) + i := by omega
        rw [e]
        obtain ⟨p, p', hp1, htr⟩ := reborrowInitAccess_ok_inv childPath off rest (idx + 1) root1
          root' hrest q m1 hm1 i (by simp at hi; omega) pm hpm k hk
        rw [hout1 (off + (idx + 1) + i) (Or.inr (by omega))] at hp1
        exact ⟨p, p', hp1, htr⟩

/-- Error provenance of `TreeBorrowsMemory.reborrowInitAccess`. -/
theorem reborrowInitAccess_error_is_ub (childPath : Gen.Path) (off : Nat) :
    ∀ (perms : List Gen.Permission) (idx : Nat) (root : Gen.Node) (e : Stop),
      (∀ q m, nodeAt root q = some m → off + idx + perms.length ≤ m.permissions.length) →
      TreeBorrowsMemory.reborrowInitAccess childPath ⟨off⟩ idx perms root = .error e →
      ∃ msg, e = .ub msg
  | [], _, _, _, _, h => by cases h
  | pm0 :: rest, idx, root, e, hlen, hrun => by
    rw [TreeBorrowsMemory.reborrowInitAccess] at hrun
    have hstep := hrun
    cases hk0 : Permission.init_access pm0 with
    | none =>
      rw [hk0] at hstep
      exact reborrowInitAccess_error_is_ub childPath off rest (idx + 1) root e
        (fun q m hm => by have := hlen q m hm; simp at this; omega) hstep
    | some k0 =>
      rw [hk0] at hstep
      rcases nwsr_bind_err hstep with haccErr | ⟨root1, hacc1, hrestErr⟩
      · obtain ⟨q, m, hm, herr⟩ := node_access_error_inv k0 (off + idx) 1 root (some childPath) e
          haccErr
        have hl := hlen q m hm
        simp at hl
        exact transitionRange_error_is_ub (locRel (some childPath) q) k0 1 (off + idx)
          m.permissions e (by omega) herr
      · have hacc1' : Node.access root (some childPath) k0 ⟨off + idx⟩ ⟨1⟩ = .ok root1 := hacc1
        have hpoint1 := node_access_ok_inv k0 (off + idx) 1 root root1 (some childPath) hacc1'
        obtain ⟨root1', hacc1'', hpost1⟩ :=
          node_access_ok_of_pointwise k0 (off + idx) 1 root (some childPath) hpoint1
        rw [hacc1'] at hacc1''
        cases hacc1''
        refine reborrowInitAccess_error_is_ub childPath off rest (idx + 1) root1 e ?_ hrestErr
        intro q m1 hm1
        cases hqm : nodeAt root q with
        | none => rw [(hpost1 q).2 hqm] at hm1; cases hm1
        | some m =>
          obtain ⟨m1', hm1', _, htrR⟩ := (hpost1 q).1 m hqm
          rw [hm1'] at hm1
          cases hm1
          obtain ⟨ps', htrR', hlen', _, _⟩ := transitionRange_ok_of_pointwise
            (locRel (some childPath) q) k0 1 (off + idx) m.permissions
            (transitionRange_ok_inv _ _ _ _ _ _ htrR)
          rw [htrR] at htrR'
          cases htrR'
          have hl := hlen q m hqm
          simp at hl
          omega

/-- Initial child permission list built by `TreeBorrowsMemory.reborrow`. -/
def reborrowChildPerms (allocLen off : Nat) (outside : Gen.Permission)
    (inside : List Gen.Permission) : List Gen.Permission :=
  if inside.length > 0 then
    (List.replicate allocLen outside).take off ++ inside ++
      (List.replicate allocLen outside).drop (off + inside.length)
  else
    List.replicate allocLen outside

private theorem a1_reborrowChildPerms_spec (allocLen off : Nat) (outside : Gen.Permission)
    (inside : List Gen.Permission) (hb : off + inside.length ≤ allocLen) :
    (reborrowChildPerms allocLen off outside inside).length = allocLen ∧
    (∀ b, off ≤ b → b < off + inside.length →
      (reborrowChildPerms allocLen off outside inside)[b]? = inside[b - off]?) ∧
    (∀ b, b < allocLen → (b < off ∨ off + inside.length ≤ b) →
      (reborrowChildPerms allocLen off outside inside)[b]? = some outside) ∧
    (∀ p ∈ reborrowChildPerms allocLen off outside inside, p = outside ∨ p ∈ inside) := by
  unfold reborrowChildPerms
  rcases Decidable.em (inside.length > 0) with hpos | hpos
  · simp only [hpos, ↓reduceIte]
    have htakeLen : ((List.replicate allocLen outside).take off).length = off := by
      rw [List.length_take, List.length_replicate]; exact Nat.min_eq_left (by omega)
    have hdropLen : ((List.replicate allocLen outside).drop (off + inside.length)).length =
        allocLen - (off + inside.length) := by
      rw [List.length_drop, List.length_replicate]
    have hlen : (((List.replicate allocLen outside).take off ++ inside) ++
        (List.replicate allocLen outside).drop (off + inside.length)).length = allocLen := by
      rw [List.length_append, List.length_append, htakeLen, hdropLen]; omega
    refine ⟨hlen, ?_, ?_, ?_⟩
    · intro b hb1 hb2
      have h1 : b < ((List.replicate allocLen outside).take off ++ inside).length := by
        rw [List.length_append, htakeLen]; omega
      rw [List.getElem?_append_left h1, List.getElem?_append_right (by rw [htakeLen]; exact hb1),
        htakeLen]
    · intro b hlt hout
      rcases hout with hlo | hhi
      · have h1 : b < ((List.replicate allocLen outside).take off ++ inside).length := by
          rw [List.length_append, htakeLen]; omega
        rw [List.getElem?_append_left h1,
          List.getElem?_append_left (by rw [htakeLen]; exact hlo),
          List.getElem?_take_of_lt hlo, nwsr_getElem?_replicate_lt hlt]
      · have h1 : ((List.replicate allocLen outside).take off ++ inside).length ≤ b := by
          rw [List.length_append, htakeLen]; exact hhi
        rw [List.getElem?_append_right h1, List.length_append, htakeLen,
          List.getElem?_drop, nwsr_getElem?_replicate_lt (by omega)]
    · intro p hp
      rcases List.mem_append.mp hp with hp1 | hp2
      · rcases List.mem_append.mp hp1 with hp1a | hp1b
        · exact Or.inl (List.eq_of_mem_replicate (List.mem_of_mem_take hp1a))
        · exact Or.inr hp1b
      · exact Or.inl (List.eq_of_mem_replicate (List.mem_of_mem_drop hp2))
  · simp only [hpos, ↓reduceIte]
    have h0 : inside.length = 0 := by omega
    refine ⟨List.length_replicate, fun b h1 h2 => absurd h2 (by omega),
      fun b hlt _ => nwsr_getElem?_replicate_lt hlt,
      fun p hp => Or.inl (List.eq_of_mem_replicate hp)⟩

/-- Algebraic equation for `TreeBorrowsMemory.reborrow` on an arbitrary live
borrow tree. -/
theorem tbm_reborrow_eq (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (settings : Gen.ReborrowSettings)
    (frameExtra : Gen.TreeBorrowsFrameExtra)
    (id : Nat) (parentPath : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (pNode : Gen.Node) (off : Nat)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, parentPath))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (hoff : ptr.addr - alloc.addr = (off : Int))
    (hbound : off + settings.inside.length ≤ alloc.data.length)
    (hpNode : nodeAt alloc.extra.root parentPath = some pNode)
    (hmpOut : Permission.matches_protector settings.outside settings.«protected» = true)
    (hmpIn : ∀ p ∈ settings.inside, Permission.matches_protector p settings.«protected» = true) :
    let childPerms := reborrowChildPerms alloc.data.length off settings.outside settings.inside
    let childNode : Gen.Node := ⟨[], childPerms, settings.«protected»⟩
    let childPath : Gen.Path := parentPath ++ [(pNode.children.length : Int)]
    ∃ root1, Node.add_node alloc.extra.root parentPath childNode = .ok (childPath, root1) ∧
      TreeBorrowsMemory.reborrow tbm ptr settings frameExtra =
        (TreeBorrowsMemory.reborrowInitAccess childPath ⟨off⟩ 0 settings.inside root1 >>= fun root2 =>
          pure ({ ptr with provenance := some (⟨(id : Int)⟩, childPath) },
            { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id
              { alloc with extra := { root := root2 } }) } },
            if Protected.yes settings.«protected» then
              { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] }
            else frameExtra)) := by
  let childPerms := reborrowChildPerms alloc.data.length off settings.outside settings.inside
  let childNode : Gen.Node := ⟨[], childPerms, settings.«protected»⟩
  let childPath : Gen.Path := parentPath ++ [(pNode.children.length : Int)]
  obtain ⟨root1, hadd, _, _, _⟩ := node_add_node_spec alloc.extra.root pNode childNode parentPath
    hpNode rfl
  refine ⟨root1, hadd, ?_⟩
  have hcheck : ∃ r, BasicMemory.check_ptr tbm.mem ptr ⟨settings.inside.length⟩ = .ok r := by
    rcases Decidable.em (settings.inside.length = 0) with h0 | h0
    · exact ⟨none, by unfold BasicMemory.check_ptr; simp [h0, pure, Except.pure]⟩
    · exact ⟨_, nwsr_check_ptr_ok tbm.mem ptr id parentPath alloc off settings.inside.length
        hprov halloc hlive hoff hbound h0⟩
  obtain ⟨r, hr⟩ := hcheck
  have hsz : Size.from_bytes (ptr.addr - alloc.addr) = some ⟨off⟩ := by
    rw [hoff]
    have hnn : (0 : Int) ≤ (off : Int) := Int.natCast_nonneg off
    unfold Size.from_bytes
    simp only [hnn, ↓reduceIte]
    rfl
  have hall : (childPerms.all fun x => Permission.matches_protector x settings.«protected») = true := by
    rw [List.all_eq_true]
    intro p hp
    rcases (a1_reborrowChildPerms_spec alloc.data.length off settings.outside settings.inside
      hbound).2.2.2 p hp with rfl | hin
    · exact hmpOut
    · exact hmpIn p hin
  have hadd' : Node.add_node alloc.extra.root parentPath
      { children := [], permissions := childPerms, «protected» := settings.«protected» } =
      .ok (parentPath ++ [(pNode.children.length : Int)], root1) := hadd
  unfold TreeBorrowsMemory.reborrow
  dsimp only
  rw [hr]
  simp only [bind, Except.bind, hprov]
  rw [a1_listMutateAt_natCast _ _ _ _ alloc halloc]
  simp only [hsz, bind, Except.bind, pure, Except.pure]
  rcases Decidable.em (settings.inside.length > 0) with hpos | hpos
  · have hws : writeSubsliceAtIndex (List.replicate (Allocation.size alloc).bytes settings.outside)
        ((off : Nat) : Int) settings.inside = .ok childPerms := by
      unfold childPerms reborrowChildPerms Allocation.size writeSubsliceAtIndex
      have hw : (0 : Int) ≤ (off : Int) ∧
          (off : Int) + (settings.inside.length : Int) ≤
            ((List.replicate alloc.data.length settings.outside).length : Int) := by
        rw [List.length_replicate]; exact ⟨by omega, by omega⟩
      simp only [hpos, hw, and_self, ↓reduceIte]
      rfl
    simp only [hpos, ↓reduceIte, hws, hall, Bool.not_true, Bool.false_eq_true, hadd']
    cases TreeBorrowsMemory.reborrowInitAccess (parentPath ++ [(pNode.children.length : Int)])
      ⟨off⟩ 0 settings.inside root1 <;> rfl
  · have hcpEq : List.replicate (Allocation.size alloc).bytes settings.outside = childPerms := by
      unfold childPerms reborrowChildPerms Allocation.size
      simp only [hpos, ↓reduceIte]
    simp only [hpos, ↓reduceIte, hcpEq, hall, Bool.not_true, Bool.false_eq_true, hadd']
    cases TreeBorrowsMemory.reborrowInitAccess (parentPath ++ [(pNode.children.length : Int)])
      ⟨off⟩ 0 settings.inside root1 <;> rfl

/-! ### 4.7 Symbolic Whole-Tree `TreeSimInv` Simulation for `TreeBorrowsMemory.retag_ptr` -/

/-- Extend a tag-to-path embedding `emb` by mapping a newly minted `newTag` to `newPath`. -/
def extendEmb (emb : Nat → Gen.Path) (newTag : Nat) (newPath : Gen.Path) : Nat → Gen.Path :=
  fun t => if t = newTag then newPath else emb t

private theorem a1_isProtected_cons_ne (n : TreeTagNode) (pid : Nat) (ap : List Nat)
    (hne : n.protector ≠ some pid) :
    n.isProtected (pid :: ap) = n.isProtected ap := by
  unfold TreeTagNode.isProtected
  cases hp : n.protector with
  | none => rfl
  | some q =>
    have hqp : q ≠ pid := fun h => hne (by rw [hp, h])
    simp [hqp.symm]

private theorem a1_rangesOverlap_self {off len : Nat} (hlen : 0 < len) :
    rangesOverlap off len off len = true := by
  unfold rangesOverlap
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩

private theorem a1_cellsToFreezeMask_length {cells : List (Gen.Offset × LibSpecr.Size)}
    {size : Nat} {mask : List Bool} (h : cellsToFreezeMask cells ⟨size⟩ = .ok mask) :
    mask.length = size := by
  unfold cellsToFreezeMask at h
  obtain ⟨res, _, h⟩ := nwsr_bind_ok h
  split at h
  · cases h
  · next hnot =>
    cases h
    exact Decidable.of_not_not hnot


private def A1NodeStepSim (ap : List Nat) (k : Gen.AccessKind)
    (step : Bool → TreeTagNode → Except RetagStepErr TreeTagNode) (n : TreeTagNode) : Prop :=
  ∀ isLocal, ∃ p,
    permToMiniRust (n.isProtected ap) n.accessed n.perm = some p ∧
    (∀ n', step isLocal n = .ok n' →
      n'.tag = n.tag ∧ n'.protector = n.protector ∧ n'.isProtected ap = n.isProtected ap ∧
      n'.rangeOffset = n.rangeOffset ∧ n'.rangeLen = n.rangeLen ∧
      (n'.isProtected ap = true → n'.perm ≠ .reservedIM) ∧
      (n'.isProtected ap = true → n'.perm = .unique → n'.accessed = true) ∧
      ∃ p', Permission.transition p k (nodeRelToMiniRust isLocal) = .ok p' ∧
        permToMiniRust (n.isProtected ap) n'.accessed n'.perm = some p') ∧
    (∀ e, step isLocal n = .error e →
      ∃ msg, Permission.transition p k (nodeRelToMiniRust isLocal) = .error (.ub msg))

private theorem a1_stepRead_sim (ap : List Nat) (off len : Nat) (n : TreeTagNode)
    (hov : rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hIM : n.isProtected ap = true → n.perm ≠ .reservedIM)
    (hUA : n.isProtected ap = true → n.perm = .unique → n.accessed = true) :
    A1NodeStepSim ap .Read (fun isLoc m => stepNodeOnRangeRead ap isLoc off len m) n := by
  intro isLocal
  obtain ⟨p, hp, hok, herr⟩ :=
    stepNodeOnRangeRead_simulates_permission_transition ap isLocal off len n hov hIM hUA
  refine ⟨p, hp, fun n' hn' => ?_, herr⟩
  obtain ⟨htag, hprot, hro, hrl, hIM', hUA'⟩ := nwsr_stepRead_meta ap isLocal off len n n' hn'
  have hpe : n'.isProtected ap = n.isProtected ap := by
    unfold TreeTagNode.isProtected; rw [hprot]
  exact ⟨htag, hprot, hpe, hro, hrl, fun hp' him => hIM (hpe ▸ hp') (hIM' him), hUA' hUA, hok n' hn'⟩

private theorem a1_stepWrite_sim (ap : List Nat) (off len : Nat) (n : TreeTagNode)
    (hov : rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hIM : n.isProtected ap = true → n.perm ≠ .reservedIM)
    (hUA : n.isProtected ap = true → n.perm = .unique → n.accessed = true) :
    A1NodeStepSim ap .Write (fun isLoc m => stepNodeOnRangeWrite ap isLoc off len m) n := by
  intro isLocal
  obtain ⟨p, hp, hok, herr⟩ :=
    stepNodeOnRangeWrite_simulates_permission_transition ap isLocal off len n hov hIM hUA
  refine ⟨p, hp, fun n' hn' => ?_, herr⟩
  obtain ⟨htag, hprot, hro, hrl, hIM', hUA'⟩ := nwsr_stepWrite_meta ap isLocal off len n n' hn'
  have hpe : n'.isProtected ap = n.isProtected ap := by
    unfold TreeTagNode.isProtected; rw [hprot]
  exact ⟨htag, hprot, hpe, hro, hrl, fun hp' him => hIM (hpe ▸ hp') (hIM' him), hUA' hUA, hok n' hn'⟩

private theorem a1_execFnEntryMutRetagPrunedSourceOrder_rustcNoWritable_ok_iff
    (w : FnEntryBorrowWorld) (parentTag off len : Nat) (requireInit : Bool) (hlen : len ≠ 0)
    (res : FnEntryBorrowWorld × Nat) :
    execFnEntryMutRetagPrunedSourceOrder w parentTag off len .rustcNoWritable requireInit = .ok res ↔
      (∃ pn, findNode? w.nodes parentTag = some pn) ∧
      ∃ nodes', res = ({ w with
          nodes := ⟨w.nextTag, some parentTag, .reservedFrz false, off, len, some w.nextProtector, true⟩ :: nodes'
          activeProtectors := w.nextProtector :: w.activeProtectors
          nextTag := w.nextTag + 1
          nextProtector := w.nextProtector + 1 }, w.nextTag) ∧
        ListRel (PrunedStepRel w parentTag false off len
          (fun isLoc m => stepNodeOnRangeRead w.activeProtectors isLoc off len m)) w.nodes nodes' := by
  have hlen0 : (len == 0) = false := beq_false_of_ne hlen
  constructor
  · intro hok
    rcases res with ⟨w', ct⟩
    have hfn : ∃ pn, findNode? w.nodes parentTag = some pn := by
      unfold execFnEntryMutRetagPrunedSourceOrder at hok
      cases hf : findNode? w.nodes parentTag with
      | none => rw [hf] at hok; cases hok
      | some pn => exact ⟨pn, rfl⟩
    obtain ⟨hct, hact, hnt, hnp, hro, hpi, nodes', hnodes, hrel⟩ :=
      execFnEntryMutRetagPrunedSourceOrder_rustcNoWritable_ok_inv w w' parentTag off len ct
        requireInit hlen hok
    refine ⟨hfn, nodes', ?_, hrel⟩
    cases w'
    simp only [FnEntryBorrowWorld.mk.injEq, Prod.mk.injEq] at hct hact hnt hnp hro hpi hnodes ⊢
    exact ⟨⟨hnodes, hact, hnt, hnp, hpi, hro⟩, hct⟩
  · rintro ⟨⟨pn, hfn⟩, nodes', rfl, hrel⟩
    obtain ⟨h1, h2, h3⟩ := prunedPhases_ok_of_listRel w parentTag false off len
      (fun isLoc m => stepNodeOnRangeRead w.activeProtectors isLoc off len m) nodes' hrel
    have h1' : checkAncestorPathM w parentTag
        (stepNodeOnRangeRead w.activeProtectors true off len) = .ok () := h1
    have h2' : checkNodesM (stepNodeOnRangeRead w.activeProtectors false off len)
        (w.nodes.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag &&
          !isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) false off len n)) =
        .ok () := h2
    have h3' : mapNodesM (fun n =>
        if (ancestorPathTags w.nodes parentTag).contains n.tag then
          stepNodeOnRangeRead w.activeProtectors true off len n
        else if isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) false off len n then .ok n
        else stepNodeOnRangeRead w.activeProtectors false off len n) w.nodes = .ok nodes' := h3
    unfold execFnEntryMutRetagPrunedSourceOrder
    simp only [hfn, hlen0, Bool.false_eq_true, ↓reduceIte, h1', h2', h3']

private theorem a1_execFnEntryMutRetagPrunedSourceOrder_writableChildWrite_ok_iff
    (w : FnEntryBorrowWorld) (parentTag off len : Nat) (requireInit : Bool) (hlen : len ≠ 0)
    (res : FnEntryBorrowWorld × Nat) :
    execFnEntryMutRetagPrunedSourceOrder w parentTag off len .writableChildWrite requireInit = .ok res ↔
      w.allocReadOnly = false ∧ (requireInit && !w.pointeeInitialized) = false ∧
      (∃ pn, findNode? w.nodes parentTag = some pn) ∧
      ∃ nodes', res = ({ w with
          nodes := ⟨w.nextTag, some parentTag, .unique, off, len, some w.nextProtector, true⟩ :: nodes'
          activeProtectors := w.nextProtector :: w.activeProtectors
          nextTag := w.nextTag + 1
          nextProtector := w.nextProtector + 1 }, w.nextTag) ∧
        ListRel (PrunedStepRel w parentTag true off len
          (fun isLoc m => stepNodeOnRangeWrite w.activeProtectors isLoc off len m)) w.nodes nodes' := by
  have hlen0 : (len == 0) = false := beq_false_of_ne hlen
  constructor
  · intro hok
    rcases res with ⟨w', ct⟩
    have hfn : ∃ pn, findNode? w.nodes parentTag = some pn := by
      unfold execFnEntryMutRetagPrunedSourceOrder at hok
      cases hf : findNode? w.nodes parentTag with
      | none => rw [hf] at hok; cases hok
      | some pn => exact ⟨pn, rfl⟩
    obtain ⟨hro, hreq, hct, hact, hnt, hnp, nodes', hnodes, hrel⟩ :=
      execFnEntryMutRetagPrunedSourceOrder_writableChildWrite_ok_inv w w' parentTag off len ct
        requireInit hlen hok
    have hmeta : w'.pointeeInitialized = w.pointeeInitialized ∧ w'.allocReadOnly = w.allocReadOnly := by
      unfold execFnEntryMutRetagPrunedSourceOrder at hok
      rcases hfn with ⟨pn, hfn'⟩
      simp only [hfn', hlen0, hro, hreq, Bool.false_eq_true, ↓reduceIte] at hok
      split at hok; · cases hok
      split at hok; · cases hok
      split at hok; · cases hok
      injection hok with hp
      have hw := congrArg Prod.fst hp
      subst hw
      exact ⟨rfl, hro.symm⟩
    refine ⟨hro, hreq, hfn, nodes', ?_, hrel⟩
    cases w'
    simp only [FnEntryBorrowWorld.mk.injEq, Prod.mk.injEq] at hct hact hnt hnp hnodes hmeta ⊢
    exact ⟨⟨hnodes, hact, hnt, hnp, hmeta.1, hmeta.2⟩, hct⟩
  · rintro ⟨hro, hreq, ⟨pn, hfn⟩, nodes', rfl, hrel⟩
    obtain ⟨h1, h2, h3⟩ := prunedPhases_ok_of_listRel w parentTag true off len
      (fun isLoc m => stepNodeOnRangeWrite w.activeProtectors isLoc off len m) nodes' hrel
    have h1' : checkAncestorPathM w parentTag
        (stepNodeOnRangeWrite w.activeProtectors true off len) = .ok () := h1
    have h2' : checkNodesM (stepNodeOnRangeWrite w.activeProtectors false off len)
        (w.nodes.filter (fun n => !(ancestorPathTags w.nodes parentTag).contains n.tag &&
          !isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) true off len n)) =
        .ok () := h2
    have h3' : mapNodesM (fun n =>
        if (ancestorPathTags w.nodes parentTag).contains n.tag then
          stepNodeOnRangeWrite w.activeProtectors true off len n
        else if isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) true off len n then .ok n
        else stepNodeOnRangeWrite w.activeProtectors false off len n) w.nodes = .ok nodes' := h3
    unfold execFnEntryMutRetagPrunedSourceOrder
    simp only [hfn, hlen0, hro, hreq, Bool.false_eq_true, ↓reduceIte, h1', h2', h3']

/-- **Symbolic whole-tree `TreeSimInv` simulation for `TreeBorrowsMemory.retag_ptr`
on `&mut T` / `Box<T>` at `FnEntry`**, for borrow trees of arbitrary depth, every
`Unpin` pointee, and both the `#[rustc_no_writable]` and the standard policy,
whenever Miri's `SkipSelfAndChildren` pruning is inert (`hnoprune`,
`foreignStepInert`). -/
theorem tbm_retag_ptr_fnEntry_mutOrBox_simulates_world
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (frameExtra : Gen.TreeBorrowsFrameExtra)
    (ptr : Gen.Pointer Gen.TreeBorrowsProvenance)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable)
    (facts : ParamTypeFacts) (kind : RefParamKind) (attrs : ParamRetagAttrs)
    (hkind : kind ≠ .shared) (hunpin : (facts.isUnpin && facts.isUnsafeUnpin) = true)
    (htbmParams : tbm.params = ⟨attrs.implicitWrites⟩)
    (id : Nat) (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
    (off len align : Nat) (hlen : 0 < len)
    (cells : List (Gen.Offset × LibSpecr.Size)) (mask : List Bool)
    (hmask : cellsToFreezeMask cells ⟨len⟩ = .ok mask)
    (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld) (parentTag : Nat) (requireInit : Bool)
    (hprov : ptr.thin_pointer.provenance = some (⟨(id : Int)⟩, emb parentTag))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (hoff : ptr.thin_pointer.addr - alloc.addr = (off : Int))
    (hbound : off + len ≤ alloc.data.length)
    (hinv : TreeSimInv off len emb w alloc.extra.root)
    (htag : ∃ pn, findNode? w.nodes parentTag = some pn)
    (hfreshTag : ∀ n ∈ w.nodes, n.tag ≠ w.nextTag)
    (hfreshProt : ∀ n ∈ w.nodes, n.protector ≠ some w.nextProtector)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes parentTag).contains n.tag = locOf (some (emb parentTag)) (emb n.tag))
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag)
        (selectFnEntryPolicy facts kind attrs == .writableChildWrite) off len n = true →
      foreignStepInert w.activeProtectors
        (selectFnEntryPolicy facts kind attrs == .writableChildWrite) off len n = true)
    (hwritableGates : selectFnEntryPolicy facts kind attrs = .writableChildWrite →
      w.allocReadOnly = false ∧ (requireInit && !w.pointeeInitialized) = false) :
    let info := pointeeInfoOfFacts facts len align cells
    let expectedProt : Gen.Protected := if kind = .box then .Weak else .Strong
    let policy := selectFnEntryPolicy facts kind attrs
    ∃ pNode, nodeAt alloc.extra.root (emb parentTag) = some pNode ∧
      let childPath := emb parentTag ++ [(pNode.children.length : Int)]
      let emb' := extendEmb emb w.nextTag childPath
      (∀ w' childTag, execFnEntryMutRetagPrunedSourceOrder w parentTag off len policy requireInit =
          .ok (w', childTag) →
        ∃ tbm' alloc',
          TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info) true
            (!attrs.rustcNoWritable) lookup =
            .ok (ThinPointer.widen { ptr.thin_pointer with provenance := some (⟨(id : Int)⟩, childPath) }
              ptr.metadata, tbm',
              { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] }) ∧
          tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
          (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm') ∧
          (∃ mc, nodeAt alloc'.extra.root childPath = some mc ∧ mc.«protected» = expectedProt) ∧
          TreeSimInv off len emb' w' alloc'.extra.root) ∧
      (∀ e, execFnEntryMutRetagPrunedSourceOrder w parentTag off len policy requireInit = .error e →
        ∃ msg, TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info) true
          (!attrs.rustcNoWritable) lookup = .error (.ub msg)) ∧
      (∀ r, TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info) true
          (!attrs.rustcNoWritable) lookup = .ok r →
        ∃ w' childTag, execFnEntryMutRetagPrunedSourceOrder w parentTag off len policy requireInit =
          .ok (w', childTag) ∧
          r.1 = ThinPointer.widen { ptr.thin_pointer with provenance := some (⟨(id : Int)⟩, childPath) }
            ptr.metadata ∧
          r.2.2 = { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] } ∧
          ∃ alloc', r.2.1.mem.allocations[id]? = some alloc' ∧
            TreeSimInv off len emb' w' alloc'.extra.root) := by
  have hmaskLen : mask.length = len := a1_cellsToFreezeMask_length hmask
  obtain ⟨pn, hpn⟩ := htag
  have hpnMem : pn ∈ w.nodes := (mem_of_findNode?_eq_some hpn).1
  have hpnTag : pn.tag = parentTag := (mem_of_findNode?_eq_some hpn).2
  obtain ⟨pNode, hpNode, _⟩ := hinv.nodes pn hpnMem
  rw [hpnTag] at hpNode
  refine ⟨pNode, hpNode, ?_⟩
  let info := pointeeInfoOfFacts facts len align cells
  let expectedProt : Gen.Protected := if kind = .box then .Weak else .Strong
  have hProtYes : Protected.yes expectedProt = true := by
    dsimp only [expectedProt]; split <;> rfl
  let childPath := emb parentTag ++ [(pNode.children.length : Int)]
  let emb' := extendEmb emb w.nextTag childPath
  have hneLen : len ≠ 0 := by omega
  have hpolNotSkip : selectFnEntryPolicy facts kind attrs ≠ .skipRetag := by
    unfold selectFnEntryPolicy
    cases kind with
    | shared => exact absurd rfl hkind
    | mutable | box =>
      simp only [hunpin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split <;> decide
  have hsettings := reborrowSettings_fnEntry_mutOrBox_eq_policy lookup ptr facts kind attrs hkind
    len align cells mask hmask
  rw [← htbmParams] at hsettings
  have hlocChild : ∀ q m, nodeAt alloc.extra.root q = some m →
      locOf (some childPath) q = locOf (some (emb parentTag)) q :=
    fun q m hm => locOf_childPath_eq_parentPath alloc.extra.root (emb parentTag) q pNode m hpNode hm
  have hlocChildSelf : locOf (some childPath) childPath = true := by
    rw [locOf_some_eq_isPrefixOf]
    have h1 := a1_isPrefixOf_append_right childPath []
    rw [List.append_nil] at h1
    exact h1
  have hcore :
      ∀ (isWrite : Bool) (k : Gen.AccessKind) (pInit pAfter : Gen.Permission)
        (childPerm : TreeBorrowPerm)
        (step : Bool → TreeTagNode → Except RetagStepErr TreeTagNode),
        Permission.init_access pInit = some k →
        Permission.transition pInit k .Local = .ok pAfter →
        Permission.matches_protector pInit expectedProt = true →
        permToMiniRust true true childPerm = some pAfter →
        childPerm ≠ .reservedIM →
        (∀ n ∈ w.nodes, A1NodeStepSim w.activeProtectors k step n) →
        (∀ n ∈ w.nodes,
          isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) isWrite off len n = true →
          step false n = .ok n) →
        ReborrowSettings.new lookup ptr (ptrTypeOfParamKind kind info) true tbm.params
          (!attrs.rustcNoWritable) =
          .ok (some { inside := List.replicate len pInit, outside := .Prot (.Reserved false false), «protected» := expectedProt }) →
        let childNodeW : TreeTagNode :=
          ⟨w.nextTag, some parentTag, childPerm, off, len, some w.nextProtector, true⟩
        (∀ nodes', ListRel (PrunedStepRel w parentTag isWrite off len step) w.nodes nodes' →
          ∃ tbm' alloc',
            TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info) true
              (!attrs.rustcNoWritable) lookup =
              .ok (ThinPointer.widen { ptr.thin_pointer with provenance := some (⟨(id : Int)⟩, childPath) }
                ptr.metadata, tbm',
                { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] }) ∧
            tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
            (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm') ∧
            (∃ mc, nodeAt alloc'.extra.root childPath = some mc ∧ mc.«protected» = expectedProt) ∧
            TreeSimInv off len emb'
              { w with
                nodes := childNodeW :: nodes'
                activeProtectors := w.nextProtector :: w.activeProtectors
                nextTag := w.nextTag + 1
                nextProtector := w.nextProtector + 1 } alloc'.extra.root) ∧
        ((∀ nodes', ¬ ListRel (PrunedStepRel w parentTag isWrite off len step) w.nodes nodes') →
          ∃ msg, TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info) true
            (!attrs.rustcNoWritable) lookup = .error (.ub msg)) := by
    intro isWrite k pInit pAfter childPerm step hinitK hchildTr hmpInit hchildP hchildNoIM hstep hnpr hnew
    let s : Gen.ReborrowSettings :=
      { inside := List.replicate len pInit, outside := .Prot (.Reserved false false),
        «protected» := expectedProt }
    have hmpOut : Permission.matches_protector s.outside s.«protected» = true := by
      simp [s, Permission.matches_protector, hProtYes]
    have hmpIn : ∀ p ∈ s.inside, Permission.matches_protector p s.«protected» = true := by
      intro p hp
      rw [List.eq_of_mem_replicate hp]
      exact hmpInit
    have hsLen : s.inside.length = len := List.length_replicate
    obtain ⟨root1, hadd, hreb⟩ := tbm_reborrow_eq tbm ptr.thin_pointer s frameExtra id
      (emb parentTag) alloc pNode off hprov halloc hlive hoff (by rw [hsLen]; exact hbound)
      hpNode hmpOut hmpIn
    let childPerms := reborrowChildPerms alloc.data.length off s.outside s.inside
    let childNodeMR : Gen.Node := ⟨[], childPerms, expectedProt⟩
    obtain ⟨root1', hadd', hchildAt1, hexist1, hsurj1⟩ :=
      node_add_node_spec alloc.extra.root pNode childNodeMR (emb parentTag) hpNode rfl
    rw [hadd] at hadd'
    cases hadd'
    have hchildPermSpec := a1_reborrowChildPerms_spec alloc.data.length off s.outside s.inside
      (by rw [hsLen]; exact hbound)
    have hretagEq : TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info)
        true (!attrs.rustcNoWritable) lookup =
        (TreeBorrowsMemory.reborrowInitAccess childPath ⟨off⟩ 0 s.inside root1 >>= fun root2 =>
          pure (ThinPointer.widen { ptr.thin_pointer with provenance := some (⟨(id : Int)⟩, childPath) }
              ptr.metadata,
            { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id
              { alloc with extra := { root := root2 } }) } },
            { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] })) := by
      unfold TreeBorrowsMemory.retag_ptr
      rw [hnew]
      dsimp only [s, childPath] at hreb ⊢
      simp only [bind, Except.bind, hreb, hProtYes, ↓reduceIte]
      cases TreeBorrowsMemory.reborrowInitAccess (emb parentTag ++ [(pNode.children.length : Int)])
        ⟨off⟩ 0 (List.replicate len pInit) root1 <;> rfl
    have hpr : ∀ n ∈ w.nodes, ∀ n', PrunedStepRel w parentTag isWrite off len step n n' →
        step (locOf (some (emb parentTag)) (emb n.tag)) n = .ok n' := by
      intro n hn n' hrel
      rcases hrel with ⟨hc, hs⟩ | ⟨hc, hp, hEq⟩ | ⟨hc, _, hs⟩
      · rw [← hloc n hn, hc]; exact hs
      · rw [← hloc n hn, hc, hEq]; exact hnpr n hn hp
      · rw [← hloc n hn, hc]; exact hs
    have hrp : ∀ n ∈ w.nodes, ∀ n', step (locOf (some (emb parentTag)) (emb n.tag)) n = .ok n' →
        PrunedStepRel w parentTag isWrite off len step n n' := by
      intro n hn n' hs
      cases hl : locOf (some (emb parentTag)) (emb n.tag) with
      | true => rw [hl] at hs; exact Or.inl ⟨by rw [hloc n hn, hl], hs⟩
      | false =>
        rw [hl] at hs
        cases hp : isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag) isWrite off
            len n with
        | false => exact Or.inr (Or.inr ⟨by rw [hloc n hn, hl], hp, hs⟩)
        | true =>
          rw [hnpr n hn hp] at hs
          cases hs
          exact Or.inr (Or.inl ⟨by rw [hloc n hn, hl], hp, rfl⟩)
    have hmr : ∀ q m, nodeAt alloc.extra.root q = some m → ∃ n ∈ w.nodes, emb n.tag = q ∧
        NodeWindowRel w.activeProtectors off len n m := by
      intro q m hq
      obtain ⟨n, hn, hemb⟩ := hinv.surj q m hq
      obtain ⟨m', hm', hrel⟩ := hinv.nodes n hn
      rw [hemb, hq] at hm'
      cases hm'
      exact ⟨n, hn, hemb, hrel⟩
    have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
    constructor
    · intro nodes' hrel
      have hpoint : ∀ q m1, nodeAt root1 q = some m1 → ∀ i < s.inside.length, ∀ pm,
          s.inside[i]? = some pm → ∀ k', Permission.init_access pm = some k' →
            ∃ p p', m1.permissions[off + 0 + i]? = some p ∧
              Permission.transition p k' (locRel (some childPath) q) = .ok p' := by
        intro q m1 hm1 i hi pm hpm k' hk'
        have hpmEq : pm = pInit := List.eq_of_mem_replicate (List.mem_of_getElem? hpm)
        rw [hpmEq] at hk'
        rw [hinitK] at hk'
        cases hk'
        rw [Nat.add_zero]
        rcases hsurj1 q m1 hm1 with ⟨rfl, rfl⟩ | ⟨m0, hm0, hps0, _⟩
        · have hget : childPerms[off + i]? = some pInit := by
            rw [hchildPermSpec.2.1 (off + i) (by omega) (by omega)]
            have e : off + i - off = i := by omega
            rw [e]
            exact nwsr_getElem?_replicate_lt (by rw [hsLen] at hi; exact hi)
          have hlocR : locRel (some childPath) childPath = .Local := by
            unfold locRel; rw [hlocChildSelf]; rfl
          rw [hlocR]
          exact ⟨pInit, pAfter, hget, hchildTr⟩
        · obtain ⟨n, hn, hemb, _, p, hp, hwin⟩ := hmr q m0 hm0
          obtain ⟨n', _, hnn'⟩ := hrel.exists_of_mem_left hn
          have hs := hpr n hn n' hnn'
          obtain ⟨p0, hp0, hok, _⟩ := hstep n hn (locOf (some (emb parentTag)) (emb n.tag))
          rw [hp] at hp0
          cases hp0
          obtain ⟨_, _, _, _, _, _, _, p', htr, _⟩ := hok n' hs
          have hlocEq : locRel (some childPath) q = nodeRelToMiniRust (locOf (some (emb parentTag)) (emb n.tag)) := by
            unfold locRel nodeRelToMiniRust
            rw [hlocChild q m0 hm0, hemb]
          rw [hps0, hlocEq]
          exact ⟨p, p', hwin (off + i) (by omega) (by rw [hsLen] at hi; omega), htr⟩
      obtain ⟨root2, hinitRun, hinitPost⟩ :=
        reborrowInitAccess_ok_of_pointwise childPath off s.inside 0 root1 hpoint
      have hretagOk : TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info)
          true (!attrs.rustcNoWritable) lookup =
          .ok (ThinPointer.widen { ptr.thin_pointer with provenance := some (⟨(id : Int)⟩, childPath) }
              ptr.metadata,
            { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id
              { alloc with extra := { root := root2 } }) } },
            { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] }) := by
        rw [hretagEq, hinitRun]
        rfl
      obtain ⟨mc2, hmc2, hmc2Prot, _, _, hmc2In⟩ := (hinitPost childPath).2 childNodeMR hchildAt1
      refine ⟨_, _, hretagOk, List.getElem?_set_self hidlt, hlive,
        fun hwf => TreeBorrowsMemory.retag_ptr_wfLive hwf hretagOk,
        ⟨mc2, hmc2, hmc2Prot⟩, ?_⟩
      let childNodeW : TreeTagNode :=
        ⟨w.nextTag, some parentTag, childPerm, off, len, some w.nextProtector, true⟩
      have hnodeOld : ∀ n' ∈ nodes', ∃ n ∈ w.nodes, n'.tag = n.tag ∧ n'.tag ≠ w.nextTag ∧
          n'.isProtected (w.nextProtector :: w.activeProtectors) = n.isProtected w.activeProtectors ∧
          n'.rangeOffset = n.rangeOffset ∧ n'.rangeLen = n.rangeLen ∧
          (n'.isProtected (w.nextProtector :: w.activeProtectors) = true → n'.perm ≠ .reservedIM) ∧
          (n'.isProtected (w.nextProtector :: w.activeProtectors) = true → n'.perm = .unique →
            n'.accessed = true) ∧
          ∃ m2, nodeAt root2 (emb' n'.tag) = some m2 ∧
            NodeWindowRel (w.nextProtector :: w.activeProtectors) off len n' m2 := by
        intro n' hn'
        obtain ⟨n, hn, hnn'⟩ := hrel.exists_of_mem_right hn'
        have hs := hpr n hn n' hnn'
        obtain ⟨m0, hm0, hprot0, p, hp, hwin0⟩ := hinv.nodes n hn
        obtain ⟨p0, hp0, hok, _⟩ := hstep n hn (locOf (some (emb parentTag)) (emb n.tag))
        rw [hp] at hp0
        cases hp0
        obtain ⟨htagEq, hprotField, hpe, hro, hrl, hIM, hUA, p', htr, hp'⟩ := hok n' hs
        have hprotNew : n'.isProtected (w.nextProtector :: w.activeProtectors) =
            n.isProtected w.activeProtectors := by
          rw [a1_isProtected_cons_ne n' w.nextProtector w.activeProtectors
            (hprotField ▸ hfreshProt n hn)]
          exact hpe
        have htagNe : n'.tag ≠ w.nextTag := htagEq ▸ hfreshTag n hn
        obtain ⟨m1, hm1, hm1Ps, hm1Prot⟩ := hexist1 (emb n.tag) m0 hm0
        obtain ⟨m2, hm2, hm2Prot, _, _, hm2In⟩ := (hinitPost (emb n.tag)).2 m1 hm1
        have hemb'Eq : emb' n'.tag = emb n.tag := by
          unfold emb' extendEmb
          simp only [htagNe, ↓reduceIte]
          exact congrArg emb htagEq
        refine ⟨n, hn, htagEq, htagNe, hprotNew, hro, hrl,
          fun hp'' => hIM (hpe.trans (hprotNew.symm.trans hp'')),
          fun hp'' => hUA (hpe.trans (hprotNew.symm.trans hp'')),
          m2, by rw [hemb'Eq]; exact hm2, ?_, p', by rw [hprotNew]; exact hp', ?_⟩
        · rw [hm2Prot, hm1Prot, hprot0, hprotNew]
        · intro b hb1 hb2
          have hi : b - off < s.inside.length := by rw [hsLen]; omega
          have hpm : s.inside[b - off]? = some pInit := nwsr_getElem?_replicate_lt (by rw [hsLen] at hi; exact hi)
          have hm1Get : m1.permissions[off + 0 + (b - off)]? = some p := by
            rw [hm1Ps, Nat.add_zero]
            have e : off + (b - off) = b := by omega
            rw [e]
            exact hwin0 b hb1 hb2
          have hstepB := hm2In (b - off) hi pInit hpm p hm1Get
          rw [hinitK] at hstepB
          obtain ⟨p'', htr'', hm2Get⟩ := hstepB
          have hlocEq : locRel (some childPath) (emb n.tag) =
              nodeRelToMiniRust (locOf (some (emb parentTag)) (emb n.tag)) := by
            unfold locRel nodeRelToMiniRust
            rw [hlocChild (emb n.tag) m0 hm0]
          rw [hlocEq] at htr''
          rw [htr] at htr''
          cases htr''
          have e : off + 0 + (b - off) = b := by omega
          rw [e] at hm2Get
          exact hm2Get
      have hchildProtW : childNodeW.isProtected (w.nextProtector :: w.activeProtectors) = true := by
        simp [childNodeW, TreeTagNode.isProtected]
      have hemb'Child : emb' childNodeW.tag = childPath := by
        unfold emb' extendEmb childNodeW
        simp
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro n' hn'
        rcases List.mem_cons.mp hn' with rfl | hn''
        · refine ⟨mc2, by rw [hemb'Child]; exact hmc2, ?_, pAfter, by rw [hchildProtW]; exact hchildP, ?_⟩
          · rw [hmc2Prot, hProtYes, hchildProtW]
          · intro b hb1 hb2
            have hi : b - off < s.inside.length := by rw [hsLen]; omega
            have hpm : s.inside[b - off]? = some pInit := nwsr_getElem?_replicate_lt (by rw [hsLen] at hi; exact hi)
            have hget1 : childNodeMR.permissions[off + 0 + (b - off)]? = some pInit := by
              rw [Nat.add_zero]
              have e : off + (b - off) = b := by omega
              rw [e, hchildPermSpec.2.1 b hb1 (by rw [hsLen]; exact hb2)]
              exact hpm
            have hstepB := hmc2In (b - off) hi pInit hpm pInit hget1
            rw [hinitK] at hstepB
            obtain ⟨p'', htr'', hmc2Get⟩ := hstepB
            have hlocR : locRel (some childPath) childPath = .Local := by
              unfold locRel; rw [hlocChildSelf]; rfl
            rw [hlocR, hchildTr] at htr''
            cases htr''
            have e : off + 0 + (b - off) = b := by omega
            rw [e] at hmc2Get
            exact hmc2Get
        · obtain ⟨_, _, _, _, _, _, _, _, _, m2, hm2, hrel2⟩ := hnodeOld n' hn''
          exact ⟨m2, hm2, hrel2⟩
      · intro q m2 hq2
        cases hq1 : nodeAt root1 q with
        | none => rw [(hinitPost q).1 hq1] at hq2; cases hq2
        | some m1 =>
          rcases hsurj1 q m1 hq1 with ⟨rfl, _⟩ | ⟨m0, hm0, _, _⟩
          · exact ⟨childNodeW, List.mem_cons_self .., hemb'Child⟩
          · obtain ⟨n, hn, hemb⟩ := hinv.surj q m0 hm0
            obtain ⟨n', hn', hnn'⟩ := hrel.exists_of_mem_left hn
            have hs := hpr n hn n' hnn'
            obtain ⟨_, _, hok, _⟩ := hstep n hn (locOf (some (emb parentTag)) (emb n.tag))
            obtain ⟨htagEq, _⟩ := hok n' hs
            have hne : n'.tag ≠ w.nextTag := htagEq ▸ hfreshTag n hn
            refine ⟨n', List.mem_cons_of_mem _ hn', ?_⟩
            unfold emb' extendEmb
            simp only [hne, ↓reduceIte]
            rw [htagEq, hemb]
      · intro n' hn'
        rcases List.mem_cons.mp hn' with rfl | hn''
        · exact a1_rangesOverlap_self hlen
        · obtain ⟨n, hn, _, _, _, hro, hrl, _⟩ := hnodeOld n' hn''
          rw [hro, hrl]; exact hinv.overlap n hn
      · intro n' hn' hp''
        rcases List.mem_cons.mp hn' with rfl | hn''
        · exact hchildNoIM
        · obtain ⟨_, _, _, _, _, _, _, hIM, _⟩ := hnodeOld n' hn''
          exact hIM hp''
      · intro n' hn' hp'' hu
        rcases List.mem_cons.mp hn' with rfl | hn''
        · rfl
        · obtain ⟨_, _, _, _, _, _, _, _, hUA, _⟩ := hnodeOld n' hn''
          exact hUA hp'' hu
    · intro hno
      rw [hretagEq]
      cases hrun : TreeBorrowsMemory.reborrowInitAccess childPath ⟨off⟩ 0 s.inside root1 with
      | ok root2 =>
        exfalso
        have hall : ∀ n ∈ w.nodes, ∃ n', PrunedStepRel w parentTag isWrite off len step n n' := by
          intro n hn
          obtain ⟨m0, hm0, _, p, hp, hwin0⟩ := hinv.nodes n hn
          obtain ⟨m1, hm1, hm1Ps, _⟩ := hexist1 (emb n.tag) m0 hm0
          have hpm0 : s.inside[0]? = some pInit := nwsr_getElem?_replicate_lt hlen
          obtain ⟨q0, q0', hq0, htr0⟩ := reborrowInitAccess_ok_inv childPath off s.inside 0 root1
            root2 hrun (emb n.tag) m1 hm1 0 (by rw [hsLen]; exact hlen) pInit hpm0 k hinitK
          rw [hm1Ps, Nat.add_zero, hwin0 off (Nat.le_refl _) (by omega)] at hq0
          cases hq0
          obtain ⟨p0, hp0, _, herr⟩ := hstep n hn (locOf (some (emb parentTag)) (emb n.tag))
          rw [hp] at hp0
          cases hp0
          cases hs : step (locOf (some (emb parentTag)) (emb n.tag)) n with
          | ok n' => exact ⟨n', hrp n hn n' hs⟩
          | error e =>
            obtain ⟨msg, hmsg⟩ := herr e hs
            have hlocEq : locRel (some childPath) (emb n.tag) =
                nodeRelToMiniRust (locOf (some (emb parentTag)) (emb n.tag)) := by
              unfold locRel nodeRelToMiniRust
              rw [hlocChild (emb n.tag) m0 hm0]
            rw [hlocEq] at htr0
            rw [htr0] at hmsg
            cases hmsg
        obtain ⟨nodes', hrel⟩ := nwsr_listRel_of_forall w.nodes hall
        exact hno nodes' hrel
      | error e =>
        have hlenRoot1 : ∀ q m1, nodeAt root1 q = some m1 → off + 0 + s.inside.length ≤ m1.permissions.length := by
          intro q m1 hm1
          rcases hsurj1 q m1 hm1 with ⟨rfl, rfl⟩ | ⟨m0, hm0, hps0, _⟩
          · show off + 0 + s.inside.length ≤ childPerms.length
            rw [hchildPermSpec.1, Nat.add_zero, hsLen]; exact hbound
          · obtain ⟨n, _, _, _, _, _, hwin0⟩ := hmr q m0 hm0
            have hlast := hwin0 (off + len - 1) (by omega) (by omega)
            have hlt : off + len - 1 < m0.permissions.length := (List.getElem?_eq_some_iff.mp hlast).1
            rw [hps0, Nat.add_zero, hsLen]; omega
        obtain ⟨msg, hmsg⟩ := reborrowInitAccess_error_is_ub childPath off s.inside 0 root1 e
          hlenRoot1 hrun
        exact ⟨msg, by rw [hmsg]; rfl⟩
  -- Dispatch on `selectFnEntryPolicy facts kind attrs`.
  dsimp only
  cases hpv : selectFnEntryPolicy facts kind attrs with
  | skipRetag => exact absurd hpv hpolNotSkip
  | rustcNoWritable =>
    have hnew' : ReborrowSettings.new lookup ptr (ptrTypeOfParamKind kind info) true tbm.params
        (!attrs.rustcNoWritable) =
        .ok (some (Gen.ReborrowSettings.mk
          (List.replicate len (.Prot (.Reserved false false)))
          (.Prot (.Reserved false false)) expectedProt)) := by
      have h1 := hsettings
      rw [hpv, hmaskLen] at h1
      exact h1
    have hnpr' : ∀ n ∈ w.nodes, isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag)
        false off len n = true →
        stepNodeOnRangeRead w.activeProtectors false off len n = .ok n := by
      intro n hn hp
      have := hnoprune n hn
      rw [hpv] at this
      exact nwsr_foreignStepInert_read (this hp)
    have hmpInit : Permission.matches_protector (.Prot (.Reserved false false)) expectedProt = true := by
      simp [Permission.matches_protector, hProtYes]
    obtain ⟨hfwd, hbwd⟩ := hcore false .Read (.Prot (.Reserved false false))
      (.Prot (.Reserved true false)) (.reservedFrz false)
      (fun isLoc m => stepNodeOnRangeRead w.activeProtectors isLoc off len m)
      rfl rfl hmpInit rfl (by decide)
      (fun n hn => a1_stepRead_sim w.activeProtectors off len n (hinv.overlap n hn)
        (hinv.noProtIM n hn) (hinv.protUniqAcc n hn))
      hnpr' hnew'
    refine ⟨?_, ?_, ?_⟩
    · intro w' childTag hok
      obtain ⟨_, nodes', hpair, hrel⟩ :=
        (a1_execFnEntryMutRetagPrunedSourceOrder_rustcNoWritable_ok_iff w parentTag off len
          requireInit hneLen (w', childTag)).mp hok
      injection hpair with hw' _
      rw [hw']
      exact hfwd nodes' hrel
    · intro e herr
      apply hbwd
      intro nodes' hrel
      have hok := (a1_execFnEntryMutRetagPrunedSourceOrder_rustcNoWritable_ok_iff w parentTag off len
        requireInit hneLen _).mpr ⟨⟨pn, hpn⟩, nodes', rfl, hrel⟩
      rw [herr] at hok; cases hok
    · intro r hret
      cases he : execFnEntryMutRetagPrunedSourceOrder w parentTag off len .rustcNoWritable requireInit with
      | ok res =>
        rcases res with ⟨w', ct⟩
        obtain ⟨_, nodes', hpair, hrel⟩ :=
          (a1_execFnEntryMutRetagPrunedSourceOrder_rustcNoWritable_ok_iff w parentTag off len
            requireInit hneLen (w', ct)).mp he
        injection hpair with hw' _
        have hfwd' := hfwd nodes' hrel
        rw [← hw'] at hfwd'
        obtain ⟨tbm', alloc', hret', hal', _, _, _, hinv'⟩ := hfwd'
        rw [hret] at hret'
        cases hret'
        exact ⟨w', ct, rfl, rfl, rfl, alloc', hal', hinv'⟩
      | error e =>
        have hno : ∀ nodes', ¬ ListRel (PrunedStepRel w parentTag false off len
            (fun isLoc m => stepNodeOnRangeRead w.activeProtectors isLoc off len m)) w.nodes nodes' := by
          intro nodes' hrel
          have hok := (a1_execFnEntryMutRetagPrunedSourceOrder_rustcNoWritable_ok_iff w parentTag off len
            requireInit hneLen _).mpr ⟨⟨pn, hpn⟩, nodes', rfl, hrel⟩
          rw [he] at hok; cases hok
        obtain ⟨msg, hmsg⟩ := hbwd hno
        rw [hret] at hmsg; cases hmsg
  | writableChildWrite =>
    obtain ⟨hro, hreq⟩ := hwritableGates hpv
    have hnew' : ReborrowSettings.new lookup ptr (ptrTypeOfParamKind kind info) true tbm.params
        (!attrs.rustcNoWritable) =
        .ok (some (Gen.ReborrowSettings.mk
          (List.replicate len (.Prot .Unique))
          (.Prot (.Reserved false false)) expectedProt)) := by
      have h1 := hsettings
      rw [hpv, hmaskLen] at h1
      exact h1
    have hnpr' : ∀ n ∈ w.nodes, isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag)
        true off len n = true →
        stepNodeOnRangeWrite w.activeProtectors false off len n = .ok n := by
      intro n hn hp
      have := hnoprune n hn
      rw [hpv] at this
      exact nwsr_foreignStepInert_write (this hp)
    have hmpInit : Permission.matches_protector (.Prot .Unique) expectedProt = true := by
      simp [Permission.matches_protector, hProtYes]
    obtain ⟨hfwd, hbwd⟩ := hcore true .Write (.Prot .Unique) (.Prot .Unique) .unique
      (fun isLoc m => stepNodeOnRangeWrite w.activeProtectors isLoc off len m)
      rfl rfl hmpInit rfl (by decide)
      (fun n hn => a1_stepWrite_sim w.activeProtectors off len n (hinv.overlap n hn)
        (hinv.noProtIM n hn) (hinv.protUniqAcc n hn))
      hnpr' hnew'
    refine ⟨?_, ?_, ?_⟩
    · intro w' childTag hok
      obtain ⟨_, _, _, nodes', hpair, hrel⟩ :=
        (a1_execFnEntryMutRetagPrunedSourceOrder_writableChildWrite_ok_iff w parentTag off len
          requireInit hneLen (w', childTag)).mp hok
      injection hpair with hw' _
      rw [hw']
      exact hfwd nodes' hrel
    · intro e herr
      apply hbwd
      intro nodes' hrel
      have hok := (a1_execFnEntryMutRetagPrunedSourceOrder_writableChildWrite_ok_iff w parentTag off len
        requireInit hneLen _).mpr ⟨hro, hreq, ⟨pn, hpn⟩, nodes', rfl, hrel⟩
      rw [herr] at hok; cases hok
    · intro r hret
      cases he : execFnEntryMutRetagPrunedSourceOrder w parentTag off len .writableChildWrite requireInit with
      | ok res =>
        rcases res with ⟨w', ct⟩
        obtain ⟨_, _, _, nodes', hpair, hrel⟩ :=
          (a1_execFnEntryMutRetagPrunedSourceOrder_writableChildWrite_ok_iff w parentTag off len
            requireInit hneLen (w', ct)).mp he
        injection hpair with hw' _
        have hfwd' := hfwd nodes' hrel
        rw [← hw'] at hfwd'
        obtain ⟨tbm', alloc', hret', hal', _, _, _, hinv'⟩ := hfwd'
        rw [hret] at hret'
        cases hret'
        exact ⟨w', ct, rfl, rfl, rfl, alloc', hal', hinv'⟩
      | error e =>
        have hno : ∀ nodes', ¬ ListRel (PrunedStepRel w parentTag true off len
            (fun isLoc m => stepNodeOnRangeWrite w.activeProtectors isLoc off len m)) w.nodes nodes' := by
          intro nodes' hrel
          have hok := (a1_execFnEntryMutRetagPrunedSourceOrder_writableChildWrite_ok_iff w parentTag off len
            requireInit hneLen _).mpr ⟨hro, hreq, ⟨pn, hpn⟩, nodes', rfl, hrel⟩
          rw [he] at hok; cases hok
        obtain ⟨msg, hmsg⟩ := hbwd hno
        rw [hret] at hmsg; cases hmsg

/-- **Model 5 (`execFnEntryMutRetagTraversalOrderDirect`) corollary**: on every
rooted borrow tree (`BorrowTreeRootedWF w rootTag`), `TreeBorrowsMemory.retag_ptr`
simulates `execFnEntryMutRetagTraversalOrderDirect` identically to
`execFnEntryMutRetagPrunedSourceOrder`. -/
theorem tbm_retag_ptr_fnEntry_mutOrBox_simulates_traversalOrderDirect
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (frameExtra : Gen.TreeBorrowsFrameExtra)
    (ptr : Gen.Pointer Gen.TreeBorrowsProvenance)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable)
    (facts : ParamTypeFacts) (kind : RefParamKind) (attrs : ParamRetagAttrs)
    (hkind : kind ≠ .shared) (hunpin : (facts.isUnpin && facts.isUnsafeUnpin) = true)
    (htbmParams : tbm.params = ⟨attrs.implicitWrites⟩)
    (id : Nat) (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
    (off len align : Nat) (hlen : 0 < len)
    (cells : List (Gen.Offset × LibSpecr.Size)) (mask : List Bool)
    (hmask : cellsToFreezeMask cells ⟨len⟩ = .ok mask)
    (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld) (rootTag parentTag : Nat) (requireInit : Bool)
    (hrooted : BorrowTreeRootedWF w rootTag)
    (hprov : ptr.thin_pointer.provenance = some (⟨(id : Int)⟩, emb parentTag))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (hoff : ptr.thin_pointer.addr - alloc.addr = (off : Int))
    (hbound : off + len ≤ alloc.data.length)
    (hinv : TreeSimInv off len emb w alloc.extra.root)
    (htag : ∃ pn, findNode? w.nodes parentTag = some pn)
    (hfreshTag : ∀ n ∈ w.nodes, n.tag ≠ w.nextTag)
    (hfreshProt : ∀ n ∈ w.nodes, n.protector ≠ some w.nextProtector)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes parentTag).contains n.tag = locOf (some (emb parentTag)) (emb n.tag))
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes parentTag)
        (selectFnEntryPolicy facts kind attrs == .writableChildWrite) off len n = true →
      foreignStepInert w.activeProtectors
        (selectFnEntryPolicy facts kind attrs == .writableChildWrite) off len n = true)
    (hwritableGates : selectFnEntryPolicy facts kind attrs = .writableChildWrite →
      w.allocReadOnly = false ∧ (requireInit && !w.pointeeInitialized) = false) :
    let info := pointeeInfoOfFacts facts len align cells
    let expectedProt : Gen.Protected := if kind = .box then .Weak else .Strong
    let policy := selectFnEntryPolicy facts kind attrs
    ∃ pNode, nodeAt alloc.extra.root (emb parentTag) = some pNode ∧
      let childPath := emb parentTag ++ [(pNode.children.length : Int)]
      let emb' := extendEmb emb w.nextTag childPath
      (∀ w' childTag, execFnEntryMutRetagTraversalOrderDirect w parentTag off len policy requireInit =
          .ok (w', childTag) →
        ∃ tbm' alloc',
          TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info) true
            (!attrs.rustcNoWritable) lookup =
            .ok (ThinPointer.widen { ptr.thin_pointer with provenance := some (⟨(id : Int)⟩, childPath) }
              ptr.metadata, tbm',
              { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] }) ∧
          tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
          (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm') ∧
          (∃ mc, nodeAt alloc'.extra.root childPath = some mc ∧ mc.«protected» = expectedProt) ∧
          TreeSimInv off len emb' w' alloc'.extra.root) ∧
      (∀ e, execFnEntryMutRetagTraversalOrderDirect w parentTag off len policy requireInit = .error e →
        ∃ msg, TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info) true
          (!attrs.rustcNoWritable) lookup = .error (.ub msg)) ∧
      (∀ r, TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info) true
          (!attrs.rustcNoWritable) lookup = .ok r →
        ∃ w' childTag, execFnEntryMutRetagTraversalOrderDirect w parentTag off len policy requireInit =
          .ok (w', childTag)) := by
  let policy := selectFnEntryPolicy facts kind attrs
  have heqDir := execFnEntryMutRetagTraversalOrderDirect_eq_traversalOrder_of_rootedWF
    hrooted parentTag off len policy requireInit
  have hokIff : ∀ r, execFnEntryMutRetagTraversalOrderDirect w parentTag off len policy requireInit = .ok r ↔
      execFnEntryMutRetagPrunedSourceOrder w parentTag off len policy requireInit = .ok r := by
    intro r
    rw [heqDir]
    exact execFnEntryMutRetagTraversalOrder_ok_iff_prunedSourceOrder_ok _ w parentTag off len
      policy requireInit r
  obtain ⟨pNode, hpNode, h1, h2, h3⟩ := tbm_retag_ptr_fnEntry_mutOrBox_simulates_world
    tbm frameExtra ptr lookup facts kind attrs hkind hunpin htbmParams id alloc off len align hlen
    cells mask hmask emb w parentTag requireInit hprov halloc hlive hoff hbound hinv htag hfreshTag
    hfreshProt hloc hnoprune hwritableGates
  refine ⟨pNode, hpNode, ?_, ?_, ?_⟩
  · intro w' ct hok
    exact h1 w' ct ((hokIff _).mp hok)
  · intro e herr
    cases hp : execFnEntryMutRetagPrunedSourceOrder w parentTag off len policy requireInit with
    | ok r =>
      have hok := (hokIff r).mpr hp
      rw [herr] at hok; cases hok
    | error e0 => exact h2 e0 hp
  · intro r hret
    obtain ⟨w', ct, hok, _⟩ := h3 r hret
    exact ⟨w', ct, (hokIff _).mpr hok⟩

/-- **Symbolic whole-tree `&T` (`Ref .Immutable`) `FnEntry` retag theorem**:
for ANY live borrow tree, ANY `facts`, ANY `cells` with valid `cellsToFreezeMask`
output `mask`, `TreeBorrowsMemory.retag_ptr` for `&T` at `FnEntry` succeeds iff
every pre-existing node succeeds on `.Read` at every frozen byte (`mask[i] = true`),
inserts a `Protected::Strong` child whose frozen bytes are `.Prot (.Frozen true)`
and whose `UnsafeCell` bytes are `.Prot .Cell` (never accessed), leaves all bytes
outside `[off, off + len)` and all `UnsafeCell` bytes untouched on every existing
node, and pushes `(id, childPath)` onto `frameExtra.protectors`. -/
theorem tbm_retag_ptr_fnEntry_shared_wholeTree
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (frameExtra : Gen.TreeBorrowsFrameExtra)
    (ptr : Gen.Pointer Gen.TreeBorrowsProvenance)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable)
    (facts : ParamTypeFacts) (attrs : ParamRetagAttrs)
    (htbmParams : tbm.params = ⟨attrs.implicitWrites⟩)
    (id : Nat) (parentPath : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (pNode : Gen.Node)
    (off len align : Nat)
    (cells : List (Gen.Offset × LibSpecr.Size)) (mask : List Bool)
    (hmask : cellsToFreezeMask cells ⟨len⟩ = .ok mask)
    (hprov : ptr.thin_pointer.provenance = some (⟨(id : Int)⟩, parentPath))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (hoff : ptr.thin_pointer.addr - alloc.addr = (off : Int))
    (hbound : off + len ≤ alloc.data.length)
    (hpNode : nodeAt alloc.extra.root parentPath = some pNode) :
    let info := pointeeInfoOfFacts facts len align cells
    let childPath := parentPath ++ [(pNode.children.length : Int)]
    (∀ q m, nodeAt alloc.extra.root q = some m →
      ∀ i < len, mask[i]? = some true →
        ∃ p p', m.permissions[off + i]? = some p ∧
          Permission.transition p .Read (locRel (some parentPath) q) = .ok p') →
    ∃ tbm' alloc' mc,
      TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind .shared info) true
        (!attrs.rustcNoWritable) lookup =
        .ok (ThinPointer.widen { ptr.thin_pointer with provenance := some (⟨(id : Int)⟩, childPath) }
          ptr.metadata, tbm',
          { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] }) ∧
      tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
      (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm') ∧
      nodeAt alloc'.extra.root childPath = some mc ∧ mc.«protected» = .Strong ∧
      (∀ i < len,
        (mask[i]? = some true → mc.permissions[off + i]? = some (.Prot (.Frozen true))) ∧
        (mask[i]? = some false → mc.permissions[off + i]? = some (.Prot .Cell))) ∧
      (∀ q m, nodeAt alloc.extra.root q = some m →
        ∃ m', nodeAt alloc'.extra.root q = some m' ∧ m'.«protected» = m.«protected» ∧
          (∀ b, b < off ∨ off + len ≤ b → m'.permissions[b]? = m.permissions[b]?) ∧
          (∀ i < len, mask[i]? = some false → m'.permissions[off + i]? = m.permissions[off + i]?)) := by
  dsimp only
  intro hreadOk
  have hmaskLen : mask.length = len := a1_cellsToFreezeMask_length hmask
  let info := pointeeInfoOfFacts facts len align cells
  let childPath := parentPath ++ [(pNode.children.length : Int)]
  let inside := mask.map (fun frz => if frz then Gen.Permission.Prot (.Frozen false) else .Prot .Cell)
  let outside : Gen.Permission := if facts.isFreeze then .Prot (.Frozen false) else .Prot .Cell
  let s : Gen.ReborrowSettings := { inside := inside, outside := outside, «protected» := .Strong }
  have hnew : ReborrowSettings.new lookup ptr (ptrTypeOfParamKind .shared info) true tbm.params
      (!attrs.rustcNoWritable) = .ok (some s) := by
    rw [htbmParams]
    exact (reborrowSettings_fnEntry_shared_eq_create lookup ptr facts attrs len align cells mask hmask).1
  have hsLen : s.inside.length = len := by simp [s, inside, hmaskLen]
  have hmpOut : Permission.matches_protector s.outside s.«protected» = true := by
    dsimp only [s, outside]; cases facts.isFreeze <;> rfl
  have hmpIn : ∀ p ∈ s.inside, Permission.matches_protector p s.«protected» = true := by
    intro p hp
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
    cases b <;> rfl
  obtain ⟨root1, hadd, hreb⟩ := tbm_reborrow_eq tbm ptr.thin_pointer s frameExtra id parentPath
    alloc pNode off hprov halloc hlive hoff (by rw [hsLen]; exact hbound) hpNode hmpOut hmpIn
  let childPerms := reborrowChildPerms alloc.data.length off s.outside s.inside
  let childNodeMR : Gen.Node := ⟨[], childPerms, .Strong⟩
  obtain ⟨root1', hadd', hchildAt1, hexist1, hsurj1⟩ :=
    node_add_node_spec alloc.extra.root pNode childNodeMR parentPath hpNode rfl
  rw [hadd] at hadd'
  cases hadd'
  have hchildPermSpec := a1_reborrowChildPerms_spec alloc.data.length off s.outside s.inside
    (by rw [hsLen]; exact hbound)
  have hlocChildSelf : locRel (some childPath) childPath = .Local := by
    unfold locRel; rw [locOf_some_eq_isPrefixOf]
    have h1 := a1_isPrefixOf_append_right childPath []
    rw [List.append_nil] at h1; rw [h1]; rfl
  have hpoint : ∀ q m1, nodeAt root1 q = some m1 → ∀ i < s.inside.length, ∀ pm,
      s.inside[i]? = some pm → ∀ k', Permission.init_access pm = some k' →
        ∃ p p', m1.permissions[off + 0 + i]? = some p ∧
          Permission.transition p k' (locRel (some childPath) q) = .ok p' := by
    intro q m1 hm1 i hi pm hpm k' hk'
    have hgetMap : s.inside[i]? = (mask[i]?).map (fun frz => if frz then Gen.Permission.Prot (.Frozen false) else .Prot .Cell) :=
      List.getElem?_map
    rw [hgetMap] at hpm
    cases hmi : mask[i]? with
    | none => rw [hmi] at hpm; cases hpm
    | some bit =>
      rw [hmi] at hpm
      cases bit with
      | false =>
        cases hpm
        cases hk'
      | true =>
        cases hpm
        cases hk'
        rw [Nat.add_zero]
        rcases hsurj1 q m1 hm1 with ⟨rfl, rfl⟩ | ⟨m0, hm0, hps0, _⟩
        · have hget : childPerms[off + i]? = some (.Prot (.Frozen false)) := by
            rw [hchildPermSpec.2.1 (off + i) (by omega) (by omega)]
            have e : off + i - off = i := by omega
            rw [e, hgetMap, hmi]; rfl
          rw [hlocChildSelf]
          exact ⟨.Prot (.Frozen false), .Prot (.Frozen true), hget, rfl⟩
        · have hlocEq : locRel (some childPath) q = locRel (some parentPath) q := by
            unfold locRel; rw [locOf_childPath_eq_parentPath alloc.extra.root parentPath q pNode m0 hpNode hm0]
          rw [hps0, hlocEq]
          exact hreadOk q m0 hm0 i (by rw [hsLen] at hi; exact hi) hmi
  obtain ⟨root2, hinitRun, hinitPost⟩ :=
    reborrowInitAccess_ok_of_pointwise childPath off s.inside 0 root1 hpoint
  have hretagOk : TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind .shared info)
      true (!attrs.rustcNoWritable) lookup =
      .ok (ThinPointer.widen { ptr.thin_pointer with provenance := some (⟨(id : Int)⟩, childPath) }
          ptr.metadata,
        { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id
          { alloc with extra := { root := root2 } }) } },
        { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] }) := by
    unfold TreeBorrowsMemory.retag_ptr
    rw [hnew]
    dsimp only [childPath] at hinitRun ⊢
    simp only [bind, Except.bind, hreb, hinitRun]
    rfl
  obtain ⟨mc, hmc, hmcProt, _, _, hmcIn⟩ := (hinitPost childPath).2 childNodeMR hchildAt1
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  refine ⟨_, _, mc, hretagOk, List.getElem?_set_self hidlt, hlive,
    fun hwf => TreeBorrowsMemory.retag_ptr_wfLive hwf hretagOk, hmc, hmcProt, ?_, ?_⟩
  · intro i hi
    have hgetMap : s.inside[i]? = (mask[i]?).map (fun frz => if frz then Gen.Permission.Prot (.Frozen false) else .Prot .Cell) :=
      List.getElem?_map
    constructor
    · intro hmi
      have hpm : s.inside[i]? = some (.Prot (.Frozen false)) := by rw [hgetMap, hmi]; rfl
      have hget1 : childNodeMR.permissions[off + 0 + i]? = some (.Prot (.Frozen false)) := by
        rw [Nat.add_zero, hchildPermSpec.2.1 (off + i) (by omega) (by rw [hsLen]; omega)]
        have e : off + i - off = i := by omega
        rw [e]; exact hpm
      have hst := hmcIn i (by rw [hsLen]; exact hi) (.Prot (.Frozen false)) hpm _ hget1
      obtain ⟨p', htr', hp'⟩ := hst
      rw [hlocChildSelf] at htr'
      cases htr'
      rw [Nat.add_zero] at hp'
      exact hp'
    · intro hmi
      have hpm : s.inside[i]? = some (.Prot .Cell) := by rw [hgetMap, hmi]; rfl
      have hget1 : childNodeMR.permissions[off + 0 + i]? = some (.Prot .Cell) := by
        rw [Nat.add_zero, hchildPermSpec.2.1 (off + i) (by omega) (by rw [hsLen]; omega)]
        have e : off + i - off = i := by omega
        rw [e]; exact hpm
      have hst := hmcIn i (by rw [hsLen]; exact hi) (.Prot .Cell) hpm _ hget1
      rw [Nat.add_zero] at hst
      exact hst
  · intro q m hm
    obtain ⟨m1, hm1, hm1Ps, hm1Prot⟩ := hexist1 q m hm
    obtain ⟨m2, hm2, hm2Prot, _, hm2Out, hm2In⟩ := (hinitPost q).2 m1 hm1
    refine ⟨m2, hm2, hm2Prot.trans hm1Prot, ?_, ?_⟩
    · intro b hb
      rw [hm2Out b (by rw [Nat.add_zero, hsLen]; exact hb), hm1Ps]
    · intro i hi hmi
      have hgetMap : s.inside[i]? = (mask[i]?).map (fun frz => if frz then Gen.Permission.Prot (.Frozen false) else .Prot .Cell) :=
        List.getElem?_map
      have hpm : s.inside[i]? = some (.Prot .Cell) := by rw [hgetMap, hmi]; rfl
      cases hmGet : m.permissions[off + i]? with
      | none =>
        have hlenEq : m2.permissions.length = m.permissions.length := by
          obtain ⟨m2', hm2', _, hl', _, _⟩ := (hinitPost q).2 m1 hm1
          rw [hm2] at hm2'
          cases hm2'
          exact hl'.trans (congrArg List.length hm1Ps)
        rw [List.getElem?_eq_none_iff] at hmGet ⊢
        omega
      | some p =>
        have hst := hm2In i (by rw [hsLen]; exact hi) (.Prot .Cell) hpm p (by rw [Nat.add_zero, hm1Ps]; exact hmGet)
        rw [Nat.add_zero] at hst
        exact hst

/-- **Symbolic whole-tree ZST `&mut ()` / `Box<()>` `FnEntry` retag theorem**:
for ANY live borrow tree, ANY `Unpin` zero-sized pointee (`len = 0`, `cells = []`),
and BOTH `fnImplicitWrites = true` and `false`:
1. `TreeBorrowsMemory.retag_ptr` succeeds identically regardless of
   `#[rustc_no_writable]`, preserves `TreeBorrowsMemory.wfLive`, adds a leaf child
   at `childPath = parentPath ++ [pNode.children.length]` with
   `«protected» = if kind = .box then .Weak else .Strong` and
   `permissions = List.replicate alloc.data.length (.Prot (.Reserved false false))`,
   pushes `(id, childPath)` onto `frameExtra.protectors`, and leaves EVERY
   pre-existing node's permissions and protector flag completely untouched;
2. on `FnEntryBorrowWorld`, both `execFnEntryMutRetagPrunedSourceOrder` and
   `execFnEntryMutRetagTraversalOrderDirect` on `len = 0` likewise leave all
   existing nodes untouched and mint the fresh child node (noting that Anneal
   records `accessed = true` with `rangeLen = 0` so protector-end access is a
   no-op via `len == 0`, while MiniRust keeps `had_local_read = false` on all
   bytes so `PermissionProt.unprotect` returns `none` on every byte). -/
theorem tbm_retag_ptr_fnEntry_zst_wholeTree
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (frameExtra : Gen.TreeBorrowsFrameExtra)
    (ptr : Gen.Pointer Gen.TreeBorrowsProvenance)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable)
    (facts : ParamTypeFacts) (kind : RefParamKind)
    (hkind : kind ≠ .shared) (hunpin : (facts.isUnpin && facts.isUnsafeUnpin) = true)
    (id : Nat) (parentPath : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (pNode : Gen.Node)
    (off align : Nat)
    (hprov : ptr.thin_pointer.provenance = some (⟨(id : Int)⟩, parentPath))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (hoff : ptr.thin_pointer.addr - alloc.addr = (off : Int))
    (hbound : off ≤ alloc.data.length)
    (hpNode : nodeAt alloc.extra.root parentPath = some pNode) :
    let info := pointeeInfoOfFacts facts 0 align []
    let expectedProt : Gen.Protected := if kind = .box then .Weak else .Strong
    let childPath := parentPath ++ [(pNode.children.length : Int)]
    ∃ tbm' alloc' mc,
      (∀ fnIw : Bool,
        TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info) true fnIw lookup =
          .ok (ThinPointer.widen { ptr.thin_pointer with provenance := some (⟨(id : Int)⟩, childPath) }
            ptr.metadata, tbm',
            { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] })) ∧
      tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
      (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm') ∧
      nodeAt alloc'.extra.root childPath = some mc ∧
      mc = ⟨[], List.replicate alloc.data.length (.Prot (.Reserved false false)), expectedProt⟩ ∧
      (∀ q m, nodeAt alloc.extra.root q = some m →
        ∃ m', nodeAt alloc'.extra.root q = some m' ∧
          m'.permissions = m.permissions ∧ m'.«protected» = m.«protected») ∧
      (∀ p ∈ mc.permissions, Permission.unprotect p = .ok (.Unprot .Reserved, none)) ∧
      (∀ (w : FnEntryBorrowWorld) (parentTag : Nat) (pn : TreeTagNode) (policy : FnEntryRetagPolicy)
          (reqInit : Bool),
        policy ≠ .skipRetag → findNode? w.nodes parentTag = some pn →
        execFnEntryMutRetagPrunedSourceOrder w parentTag off 0 policy reqInit =
          execFnEntryMutRetagTraversalOrderDirect w parentTag off 0 policy reqInit ∧
        execFnEntryMutRetagPrunedSourceOrder w parentTag off 0 policy reqInit =
          .ok ({ w with
            nodes := ⟨w.nextTag, some parentTag, .reservedFrz false, off, 0, some w.nextProtector, true⟩ :: w.nodes
            activeProtectors := w.nextProtector :: w.activeProtectors
            nextTag := w.nextTag + 1
            nextProtector := w.nextProtector + 1 }, w.nextTag)) := by
  let info := pointeeInfoOfFacts facts 0 align []
  let expectedProt : Gen.Protected := if kind = .box then .Weak else .Strong
  let childPath := parentPath ++ [(pNode.children.length : Int)]
  let s : Gen.ReborrowSettings :=
    { inside := [], outside := .Prot (.Reserved false false), «protected» := expectedProt }
  have hProtYes : Protected.yes expectedProt = true := by
    dsimp only [expectedProt]; split <;> rfl
  have hmask0 : cellsToFreezeMask [] ⟨0⟩ = .ok [] := rfl
  have hnew : ∀ fnIw : Bool,
      ReborrowSettings.new lookup ptr (ptrTypeOfParamKind kind info) true tbm.params fnIw =
        .ok (some s) := by
    intro fnIw
    have hmb := reborrowSettings_fnEntry_mutOrBox_eq_policy lookup ptr facts kind
      ⟨tbm.params.implicit_writes, !fnIw⟩ hkind 0 align [] [] hmask0
    simp only [Bool.not_not] at hmb
    have hpol : selectFnEntryPolicy facts kind ⟨tbm.params.implicit_writes, !fnIw⟩ ≠ .skipRetag := by
      unfold selectFnEntryPolicy
      cases kind with
      | shared => exact absurd rfl hkind
      | mutable | box =>
        simp only [hunpin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split <;> decide
    cases hp : selectFnEntryPolicy facts kind ⟨tbm.params.implicit_writes, !fnIw⟩ with
    | skipRetag => exact absurd hp hpol
    | rustcNoWritable | writableChildWrite =>
      rw [hp] at hmb
      simpa [s, info, expectedProt] using hmb
  have hmpOut : Permission.matches_protector s.outside s.«protected» = true := by
    simp [s, Permission.matches_protector, hProtYes]
  obtain ⟨root1, hadd, hreb⟩ := tbm_reborrow_eq tbm ptr.thin_pointer s frameExtra id parentPath
    alloc pNode off hprov halloc hlive hoff (by simp [s]; exact hbound) hpNode hmpOut (fun _ hp => by cases hp)
  let childNodeMR : Gen.Node :=
    ⟨[], List.replicate alloc.data.length (.Prot (.Reserved false false)), expectedProt⟩
  obtain ⟨root1', hadd', hchildAt1, hexist1, _⟩ :=
    node_add_node_spec alloc.extra.root pNode childNodeMR parentPath hpNode rfl
  have hcpEq : reborrowChildPerms alloc.data.length off s.outside s.inside =
      List.replicate alloc.data.length (.Prot (.Reserved false false)) := rfl
  rw [hcpEq] at hadd
  rw [hadd] at hadd'
  cases hadd'
  have hretagAll : ∀ fnIw : Bool,
      TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (ptrTypeOfParamKind kind info) true fnIw lookup =
        .ok (ThinPointer.widen { ptr.thin_pointer with provenance := some (⟨(id : Int)⟩, childPath) }
          ptr.metadata,
          { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id
            { alloc with extra := { root := root1 } }) } },
          { protectors := frameExtra.protectors ++ [(⟨(id : Int)⟩, childPath)] }) := by
    intro fnIw
    unfold TreeBorrowsMemory.retag_ptr
    rw [hnew fnIw]
    dsimp only [childPath]
    simp only [bind, Except.bind, hreb, s, TreeBorrowsMemory.reborrowInitAccess, hProtYes,
      ↓reduceIte, pure, Except.pure]
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  refine ⟨_, _, childNodeMR, hretagAll, List.getElem?_set_self hidlt, hlive,
    fun hwf => TreeBorrowsMemory.retag_ptr_wfLive hwf (hretagAll false),
    hchildAt1, rfl, hexist1, ?_, ?_⟩
  · intro p hp
    rw [List.eq_of_mem_replicate hp]
    rfl
  · intro w parentTag pn policy reqInit hpol hfn
    cases policy with
    | skipRetag => exact absurd rfl hpol
    | rustcNoWritable | writableChildWrite =>
      simp [execFnEntryMutRetagPrunedSourceOrder, execFnEntryMutRetagTraversalOrderDirect, hfn]

/-! #### Whole-Tree Protector-Release Helpers -/

private theorem b1_not_in_window {off len b : Nat} (h : ¬(off ≤ b ∧ b < off + len)) :
    b < off ∨ off + len ≤ b :=
  match Nat.lt_or_ge b off with
  | .inl hlt => .inl hlt
  | .inr hge => .inr (Nat.le_of_not_lt fun hlt => h ⟨hge, hlt⟩)

private theorem b1_listMutateAt_ok {T O : Type} {xs xs' : List T} {i : Int} {what : String}
    {f : T → Interp (O × T)} {out : O}
    (h : listMutateAt xs i what f = .ok (out, xs')) :
    ∃ x x', 0 ≤ i ∧ i.toNat < xs.length ∧ xs[i.toNat]? = some x ∧
      f x = .ok (out, x') ∧ xs' = xs.set i.toNat x' := by
  unfold listMutateAt listIndex listSet at h
  obtain ⟨x, hidx, h⟩ := nwsr_bind_ok h
  obtain ⟨⟨o, x'⟩, hfx, h⟩ := nwsr_bind_ok h
  obtain ⟨ys, hset, h⟩ := nwsr_bind_ok h
  cases h
  rcases Decidable.em (0 ≤ i) with hge | hge
  · simp only [hge, ↓reduceIte] at hidx hset
    cases hget : xs[i.toNat]? with
    | none => rw [hget] at hidx; cases hidx
    | some x0 =>
      rw [hget] at hidx
      injection hidx with hx0
      subst hx0
      have hlt : i.toNat < xs.length := (List.getElem?_eq_some_iff.mp hget).1
      simp only [hlt] at hset
      cases hset
      exact ⟨x0, x', hge, hlt, rfl, hfx, rfl⟩
  · simp only [hge, ↓reduceIte] at hidx
    cases hidx

private theorem b1_mem_set_or {α : Type} {xs : List α} {i : Nat} {a b : α}
    (h : b ∈ xs.set i a) : b = a ∨ b ∈ xs := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x rest ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at h
      rcases h with rfl | hm
      · exact .inl rfl
      · exact .inr (List.mem_cons_of_mem _ hm)
    | succ k =>
      simp only [List.set_cons_succ, List.mem_cons] at h
      rcases h with rfl | hm
      · exact .inr (List.mem_cons_self ..)
      · rcases ih hm with rfl | hm'
        · exact .inl rfl
        · exact .inr (List.mem_cons_of_mem _ hm')

private theorem b1_listRel_of_forall {α β : Type} {R : α → β → Prop} :
    ∀ xs : List α, (∀ x ∈ xs, ∃ y, R x y) → ∃ ys, ListRel R xs ys
  | [], _ => ⟨[], ListRel.nil⟩
  | x :: rest, h => by
    obtain ⟨y, hxy⟩ := h x (List.mem_cons_self ..)
    obtain ⟨ys, hys⟩ := b1_listRel_of_forall rest (fun a ha => h a (List.mem_cons_of_mem _ ha))
    exact ⟨y :: ys, ListRel.cons hxy hys⟩

/-! ### 4.8 Symbolic Whole-Tree `Node.release_protector` & Multi-Entry `TreeBorrowsMemory.end_call` Simulation -/

private theorem b1_list_mapM_loop_ok {α β : Type} (f : α → Interp β) :
    ∀ (xs : List α) (acc : List β),
      (∀ x ∈ xs, ∃ y, f x = .ok y) →
      ∃ ys, List.mapM.loop f xs acc = .ok (acc.reverse ++ ys) ∧
        ys.length = xs.length ∧
        ∀ i, (i < xs.length → ∃ x y, xs[i]? = some x ∧ ys[i]? = some y ∧ f x = .ok y)
  | [], acc, _ => ⟨[], by simp [List.mapM.loop, pure, Except.pure], rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | x :: rest, acc, hall => by
    obtain ⟨y, hy⟩ := hall x (List.mem_cons_self ..)
    obtain ⟨ys, hloop, hlen, hget⟩ :=
      b1_list_mapM_loop_ok f rest (y :: acc) (fun a ha => hall a (List.mem_cons_of_mem _ ha))
    refine ⟨y :: ys, ?_, by simp [hlen], ?_⟩
    · simp only [List.mapM.loop, hy, bind, Except.bind]
      rw [hloop]
      simp [List.reverse_cons, List.append_assoc]
    · intro i hi
      cases i with
      | zero => exact ⟨x, y, rfl, rfl, hy⟩
      | succ k =>
        exact hget k (Nat.lt_of_succ_lt_succ hi)

private theorem b1_list_mapM_ok_of_forall {α β : Type} (f : α → Interp β) (xs : List α)
    (hall : ∀ x ∈ xs, ∃ y, f x = .ok y) :
    ∃ ys, xs.mapM f = .ok ys ∧ ys.length = xs.length ∧
      ∀ i < xs.length, ∃ x y, xs[i]? = some x ∧ ys[i]? = some y ∧ f x = .ok y := by
  obtain ⟨ys, hloop, hlen, hget⟩ := b1_list_mapM_loop_ok f xs [] hall
  simp only [List.reverse_nil, List.nil_append] at hloop
  exact ⟨ys, hloop, hlen, hget⟩

private theorem b1_list_mapM_loop_inv {α β : Type} {f : α → Interp β} {P : α → β → Prop}
    (hP : ∀ x y, f x = .ok y → P x y) :
    ∀ (xs : List α) (acc : List β) (out : List β),
      List.mapM.loop f xs acc = .ok out →
      out.length = acc.length + xs.length ∧
      ((∀ y ∈ acc, ∃ x, P x y) →
        ∃ ys, out = acc.reverse ++ ys ∧ ys.length = xs.length ∧
          ∀ y ∈ ys, ∃ x, P x y) := by
  intro xs
  induction xs with
  | nil =>
    intro acc out h
    simp only [List.mapM.loop, pure, Except.pure] at h
    cases h
    refine ⟨by simp, fun _ => ⟨[], by simp, rfl, fun _ h' => by cases h'⟩⟩
  | cons x rest ih =>
    intro acc out h
    simp only [List.mapM.loop, bind, Except.bind] at h
    cases hfx : f x with
    | error e => rw [hfx] at h; cases h
    | ok y =>
      rw [hfx] at h
      obtain ⟨hlen, hbody⟩ := ih (y :: acc) out h
      refine ⟨by simp at hlen ⊢; omega, fun hacc => ?_⟩
      obtain ⟨ys, hout, hylen, hyP⟩ := hbody (fun z hz => by
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact ⟨x, hP x z hfx⟩
        · exact hacc z hz')
      refine ⟨y :: ys, ?_, by simp [hylen], fun z hz => ?_⟩
      · rw [hout]; simp [List.reverse_cons, List.append_assoc]
      · rcases List.mem_cons.mp hz with rfl | hz'
        · exact ⟨x, hP x z hfx⟩
        · exact hyP z hz'

/-- Pointwise forward specification of `Node.releaseProtectorPermissions`. -/
theorem releaseProtectorPermissions_ok_of_pointwise (rel : Gen.NodeRelation) :
    ∀ (accesses : List (Option Gen.AccessKind)) (base : Nat) (perms : List Gen.Permission),
      (∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
        ∃ p p', perms[base + i]? = some p ∧ Permission.transition p k rel = .ok p') →
      ∃ perms', Node.releaseProtectorPermissions rel base accesses perms = .ok perms' ∧
        perms'.length = perms.length ∧
        (∀ b, b < base ∨ base + accesses.length ≤ b → perms'[b]? = perms[b]?) ∧
        (∀ i < accesses.length,
          match accesses[i]? with
          | some none => perms'[base + i]? = perms[base + i]?
          | some (some k) => ∀ p, perms[base + i]? = some p →
              ∃ p', Permission.transition p k rel = .ok p' ∧ perms'[base + i]? = some p'
          | none => True)
  | [], base, perms, _ =>
    ⟨perms, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | none :: rest, base, perms, hpoint => by
    have hrest : ∀ i < rest.length, ∀ k, rest[i]? = some (some k) →
        ∃ p p', perms[(base + 1) + i]? = some p ∧ Permission.transition p k rel = .ok p' := by
      intro i hi k hk
      have h1 := hpoint (i + 1) (Nat.succ_lt_succ hi) k hk
      have e : base + (i + 1) = (base + 1) + i := by omega
      rw [e] at h1
      exact h1
    obtain ⟨perms', hrun, hlen, hout, hin⟩ :=
      releaseProtectorPermissions_ok_of_pointwise rel rest (base + 1) perms hrest
    refine ⟨perms', hrun, hlen, ?_, ?_⟩
    · intro b hb
      apply hout b
      rcases hb with hlo | hhi
      · exact Or.inl (by omega)
      · exact Or.inr (by simp at hhi; omega)
    · intro i hi
      cases i with
      | zero => exact hout base (Or.inl (by omega))
      | succ j =>
        have hstep := hin j (Nat.lt_of_succ_lt_succ hi)
        have e : base + (j + 1) = (base + 1) + j := by omega
        rw [e]
        exact hstep
  | some k :: rest, base, perms, hpoint => by
    obtain ⟨p0, p0', hp0, htr0⟩ := hpoint 0 (Nat.zero_lt_succ _) k rfl
    rw [Nat.add_zero] at hp0
    have hlt : base < perms.length := (List.getElem?_eq_some_iff.mp hp0).1
    have hmut : listMutateAt perms (Int.ofNat base) "Node::release_protector"
        (fun permission => do
          let p' ← Permission.transition permission k rel
          pure ((), p')) = .ok ((), perms.set base p0') := by
      have h1 := a1_listMutateAt_natCast perms base "Node::release_protector"
        (fun permission => do
          let p' ← Permission.transition permission k rel
          pure ((), p')) p0 hp0
      change listMutateAt perms (base : Int) _ _ = _
      rw [h1]
      simp only [htr0, bind, Except.bind, pure, Except.pure]
    have hrest : ∀ i < rest.length, ∀ k', rest[i]? = some (some k') →
        ∃ p p', (perms.set base p0')[(base + 1) + i]? = some p ∧
          Permission.transition p k' rel = .ok p' := by
      intro i hi k' hk'
      have hne : base ≠ (base + 1) + i := by omega
      rw [List.getElem?_set_ne hne]
      have h1 := hpoint (i + 1) (Nat.succ_lt_succ hi) k' hk'
      have e : base + (i + 1) = (base + 1) + i := by omega
      rw [e] at h1
      exact h1
    obtain ⟨perms', hrun, hlen, hout, hin⟩ :=
      releaseProtectorPermissions_ok_of_pointwise rel rest (base + 1) (perms.set base p0') hrest
    refine ⟨perms', ?_, by rw [hlen, List.length_set], ?_, ?_⟩
    · unfold Node.releaseProtectorPermissions
      rw [hmut]
      exact hrun
    · intro b hb
      have hne : base ≠ b := by
        rcases hb with hlo | hhi
        · omega
        · simp at hhi; omega
      have hb' : b < base + 1 ∨ base + 1 + rest.length ≤ b := by
        rcases hb with hlo | hhi
        · exact Or.inl (by omega)
        · exact Or.inr (by simp at hhi; omega)
      rw [hout b hb', List.getElem?_set_ne hne]
    · intro i hi
      cases i with
      | zero =>
        intro p hp
        rw [Nat.add_zero] at hp ⊢
        rw [hp0] at hp
        cases hp
        refine ⟨p0', htr0, ?_⟩
        rw [hout base (Or.inl (by omega)), List.getElem?_set_self hlt]
      | succ j =>
        have hne : base ≠ (base + 1) + j := by omega
        have hstep := hin j (Nat.lt_of_succ_lt_succ hi)
        have e : base + (j + 1) = (base + 1) + j := by omega
        rw [e]
        change match rest[j]? with
          | some none => perms'[(base + 1) + j]? = perms[(base + 1) + j]?
          | some (some k') => ∀ p, perms[(base + 1) + j]? = some p →
              ∃ p', Permission.transition p k' rel = .ok p' ∧ perms'[(base + 1) + j]? = some p'
          | none => True
        cases hget : rest[j]? with
        | none => trivial
        | some opt =>
          rw [hget] at hstep
          cases opt with
          | none =>
            rw [hstep, List.getElem?_set_ne hne]
          | some k' =>
            intro p hp
            exact hstep p (by rw [List.getElem?_set_ne hne]; exact hp)

/-- Pointwise inversion of `Node.releaseProtectorPermissions`. -/
theorem releaseProtectorPermissions_ok_inv (rel : Gen.NodeRelation) :
    ∀ (accesses : List (Option Gen.AccessKind)) (base : Nat) (perms perms' : List Gen.Permission),
      Node.releaseProtectorPermissions rel base accesses perms = .ok perms' →
      perms'.length = perms.length ∧
      (∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
        ∃ p p', perms[base + i]? = some p ∧ Permission.transition p k rel = .ok p')
  | [], base, perms, perms', h => by
    cases h
    exact ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | none :: rest, base, perms, perms', h => by
    obtain ⟨hlen, hinv⟩ := releaseProtectorPermissions_ok_inv rel rest (base + 1) perms perms' h
    refine ⟨hlen, fun i hi k hk => ?_⟩
    cases i with
    | zero => cases hk
    | succ j =>
      have e : base + (j + 1) = (base + 1) + j := by omega
      rw [e]
      exact hinv j (Nat.lt_of_succ_lt_succ hi) k hk
  | some k :: rest, base, perms, perms', h => by
    unfold Node.releaseProtectorPermissions at h
    obtain ⟨⟨_, perms1⟩, hmut, hrest⟩ := nwsr_bind_ok h
    obtain ⟨p0, p0', _, _, hp0, hf0, rfl⟩ := b1_listMutateAt_ok hmut
    have htn : (Int.ofNat base).toNat = base := rfl
    rw [htn] at hp0
    obtain ⟨p0'', htr0, hpure⟩ := nwsr_bind_ok hf0
    cases hpure
    obtain ⟨hlen, hinv⟩ :=
      releaseProtectorPermissions_ok_inv rel rest (base + 1) (perms.set base p0') perms' hrest
    refine ⟨by rw [hlen, List.length_set], fun i hi k' hk' => ?_⟩
    cases i with
    | zero =>
      cases hk'
      rw [Nat.add_zero]
      exact ⟨p0, p0', hp0, htr0⟩
    | succ j =>
      have hne : base ≠ (base + 1) + j := by omega
      have h1 := hinv j (Nat.lt_of_succ_lt_succ hi) k' hk'
      rw [List.getElem?_set_ne hne] at h1
      have e : base + (j + 1) = (base + 1) + j := by omega
      rw [e]
      exact h1

/-- Any error from `Node.releaseProtectorPermissions` on in-bounds accesses is `Stop.ub`. -/
theorem releaseProtectorPermissions_error_is_ub (rel : Gen.NodeRelation) :
    ∀ (accesses : List (Option Gen.AccessKind)) (base : Nat) (perms : List Gen.Permission) (e : Stop),
      base + accesses.length ≤ perms.length →
      Node.releaseProtectorPermissions rel base accesses perms = .error e →
      ∃ msg, e = .ub msg
  | [], _, _, _, _, h => by cases h
  | none :: rest, base, perms, e, hb, h =>
    releaseProtectorPermissions_error_is_ub rel rest (base + 1) perms e (by simp at hb; omega) h
  | some k :: rest, base, perms, e, hb, h => by
    unfold Node.releaseProtectorPermissions at h
    rcases nwsr_bind_err h with hmutErr | ⟨⟨_, perms1⟩, hmutOk, hrestErr⟩
    · have hlt : base < perms.length := by simp at hb; omega
      obtain ⟨p0, hp0⟩ : ∃ p0, perms[base]? = some p0 := ⟨perms[base], List.getElem?_eq_getElem hlt⟩
      have hmutEq : listMutateAt perms (Int.ofNat base) "Node::release_protector"
          (fun permission => do
            let p' ← Permission.transition permission k rel
            pure ((), p')) =
          (Permission.transition p0 k rel >>= fun p' => pure ((), perms.set base p')) := by
        change listMutateAt perms (base : Int) _ _ = _
        rw [a1_listMutateAt_natCast perms base "Node::release_protector" _ p0 hp0]
        cases Permission.transition p0 k rel <;> rfl
      rw [hmutEq] at hmutErr
      cases htr : Permission.transition p0 k rel with
      | ok p' => rw [htr] at hmutErr; cases hmutErr
      | error e' =>
        rw [htr] at hmutErr
        cases hmutErr
        exact permission_transition_error_is_ub p0 k rel e htr
    · obtain ⟨_, _, _, _, _, _, rfl⟩ := b1_listMutateAt_ok hmutOk
      exact releaseProtectorPermissions_error_is_ub rel rest (base + 1) _ e
        (by rw [List.length_set]; simp at hb; omega) hrestErr

/-- Post-state relation at path `q` of `Node.release_protector root targetPath accesses`. -/
def ReleasePost (targetPath : Option Gen.Path) (accesses : List (Option Gen.AccessKind))
    (q : Gen.Path) (m m' : Gen.Node) : Prop :=
  match targetPath with
  | some tp =>
    if tp = q then
      m'.«protected» = .No ∧ m'.permissions = m.permissions
    else if tp.isPrefixOf q = true then
      m' = m
    else
      m'.«protected» = m.«protected» ∧
      m'.permissions.length = m.permissions.length ∧
      (∀ b, accesses.length ≤ b → m'.permissions[b]? = m.permissions[b]?) ∧
      (∀ i < accesses.length,
        match accesses[i]? with
        | some none => m'.permissions[i]? = m.permissions[i]?
        | some (some k) => ∀ p, m.permissions[i]? = some p →
            ∃ p', Permission.transition p k (locRel (some tp) q) = .ok p' ∧ m'.permissions[i]? = some p'
        | none => True)
  | none =>
    m'.«protected» = m.«protected» ∧
    m'.permissions.length = m.permissions.length ∧
    (∀ b, accesses.length ≤ b → m'.permissions[b]? = m.permissions[b]?) ∧
    (∀ i < accesses.length,
      match accesses[i]? with
      | some none => m'.permissions[i]? = m.permissions[i]?
      | some (some k) => ∀ p, m.permissions[i]? = some p →
          ∃ p', Permission.transition p k .Foreign = .ok p' ∧ m'.permissions[i]? = some p'
      | none => True)

private def b1_isTargetOrDesc (targetPath : Option Gen.Path) (q : Gen.Path) : Bool :=
  match targetPath with
  | some tp => tp.isPrefixOf q
  | none => false

private theorem b1_releasePost_step_cons (path : Option Gen.Path) (accesses : List (Option Gen.AccessKind))
    (i : Nat) (rest : Gen.Path) (m m' : Gen.Node) :
    let subPath : Option Gen.Path :=
      match path with
      | some (head :: tail) => if head == (i : Int) then some tail else none
      | _ => none
    ReleasePost subPath accesses rest m m' →
    (path ≠ some []) →
    ReleasePost path accesses ((i : Int) :: rest) m m' := by
  intro subPath hr hneNil
  cases path with
  | none => exact hr
  | some tp =>
    cases tp with
    | nil => exact absurd rfl hneNil
    | cons h tl =>
      have hneEq : (h :: tl) ≠ ((i : Int) :: rest) → True := fun _ => trivial
      rcases Decidable.em (h = (i : Int)) with rfl | hne
      · have hsub : subPath = some tl := by
          dsimp only [subPath]
          rw [a1_int_beq_self]
          rfl
        rw [hsub] at hr
        unfold ReleasePost at hr ⊢
        simp only [List.cons.injEq, true_and, List.isPrefixOf, a1_int_beq_self, Bool.true_and]
        rcases Decidable.em (tl = rest) with rfl | htlne
        · simp only [↓reduceIte] at hr ⊢; exact hr
        · simp only [htlne, ↓reduceIte] at hr ⊢
          cases hpre : tl.isPrefixOf rest with
          | true => simp only [hpre, ↓reduceIte] at hr ⊢; exact hr
          | false =>
            simp only [hpre, Bool.false_eq_true, ↓reduceIte] at hr ⊢
            have hlocEq : locRel (some (↑i :: tl)) (↑i :: rest) = locRel (some tl) rest := by
              unfold locRel
              rw [locOf_some_eq_isPrefixOf, locOf_some_eq_isPrefixOf]
              simp only [List.isPrefixOf, a1_int_beq_self, Bool.true_and]
            rw [hlocEq]
            exact hr
      · have hbeqF : (h == (i : Int)) = false := by
          cases hb : (h == (i : Int)) with
          | false => rfl
          | true => exact absurd ((a1_int_beq_iff h (i : Int)).mp hb) hne
        have hsub : subPath = none := by
          dsimp only [subPath]
          rw [hbeqF]
          rfl
        rw [hsub] at hr
        unfold ReleasePost at hr ⊢
        have hconsNe : h :: tl ≠ (i : Int) :: rest := fun hc => hne (List.cons.inj hc).1
        have hpreF : (h :: tl).isPrefixOf ((i : Int) :: rest) = false := by
          simp only [List.isPrefixOf, hbeqF, Bool.false_and]
        have hbeqF' : ((i : Int) == h) = false := by
          cases hb : ((i : Int) == h) with
          | false => rfl
          | true => exact absurd ((a1_int_beq_iff (i : Int) h).mp hb).symm hne
        have hlocF : locRel (some (h :: tl)) ((i : Int) :: rest) = .Foreign := by
          unfold locRel
          rw [locOf_some_eq_isPrefixOf]
          simp only [List.isPrefixOf, hbeqF', Bool.false_and]
          rfl
        simp only [hconsNe, hpreF, Bool.false_eq_true, ↓reduceIte, hlocF]
        exact hr

private theorem b1_release_protector_mutual (accesses : List (Option Gen.AccessKind)) :
    ∀ (root : Gen.Node) (path : Option Gen.Path),
      (∀ q m, nodeAt root q = some m → b1_isTargetOrDesc path q = false →
        ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
          ∃ p p', m.permissions[i]? = some p ∧
            Permission.transition p k (locRel path q) = .ok p') →
      ∃ root', Node.release_protector root path accesses = .ok root' ∧
        ∀ q, (nodeAt root q = none → nodeAt root' q = none) ∧
          (∀ m, nodeAt root q = some m →
            ∃ m', nodeAt root' q = some m' ∧ ReleasePost path accesses q m m') := by
  refine @Gen.Node.rec
    (motive_1 := fun root =>
      ∀ (path : Option Gen.Path),
        (∀ q m, nodeAt root q = some m → b1_isTargetOrDesc path q = false →
          ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
            ∃ p p', m.permissions[i]? = some p ∧
              Permission.transition p k (locRel path q) = .ok p') →
        ∃ root', Node.release_protector root path accesses = .ok root' ∧
          ∀ q, (nodeAt root q = none → nodeAt root' q = none) ∧
            (∀ m, nodeAt root q = some m →
              ∃ m', nodeAt root' q = some m' ∧ ReleasePost path accesses q m m'))
    (motive_2 := fun cs =>
      ∀ (start : Nat) (path : Option Gen.Path),
        path ≠ some [] →
        (∀ idx c, cs[idx]? = some c →
          ∀ rest m, nodeAt c rest = some m →
            b1_isTargetOrDesc path (((start + idx : Nat) : Int) :: rest) = false →
            ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
              ∃ p p', m.permissions[i]? = some p ∧
                Permission.transition p k (locRel path (((start + idx : Nat) : Int) :: rest)) = .ok p') →
        ∃ cs', Node.releaseProtectorChildren (start : Int) path accesses cs = .ok cs' ∧
          cs'.length = cs.length ∧
          ∀ idx c, cs[idx]? = some c →
            ∃ c', cs'[idx]? = some c' ∧
              ∀ rest, (nodeAt c rest = none → nodeAt c' rest = none) ∧
                (∀ m, nodeAt c rest = some m →
                  ∃ m', nodeAt c' rest = some m' ∧
                    ReleasePost path accesses (((start + idx : Nat) : Int) :: rest) m m'))
    ?nodeCase ?nilCase ?consCase
  case nodeCase =>
    intro cs ps prot ihCs path hpoint
    cases path with
    | some tp =>
      cases tp with
      | nil =>
        refine ⟨⟨cs, ps, .No⟩, rfl, fun q => ?_⟩
        cases q with
        | nil =>
          refine ⟨fun h => (by cases h), fun m hm => ?_⟩
          cases hm
          exact ⟨⟨cs, ps, .No⟩, rfl, by simp [ReleasePost]⟩
        | cons j rest =>
          have hne : ([] : Gen.Path) ≠ j :: rest := fun h => by cases h
          refine ⟨fun h => h, fun m hm => ⟨m, hm, by simp [ReleasePost, hne]⟩⟩
      | cons h tl =>
        have hrootNot : b1_isTargetOrDesc (some (h :: tl)) [] = false := rfl
        have hlocRoot : locRel (some (h :: tl)) [] = .Local := rfl
        have hpRoot : ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
            ∃ p p', ps[0 + i]? = some p ∧ Permission.transition p k .Local = .ok p' := by
          intro i hi k hk
          rw [Nat.zero_add, ← hlocRoot]
          exact hpoint [] ⟨cs, ps, prot⟩ rfl hrootNot i hi k hk
        obtain ⟨ps', hps', hpsLen, hpsOut, hpsIn⟩ :=
          releaseProtectorPermissions_ok_of_pointwise .Local accesses 0 ps hpRoot
        obtain ⟨cs', hcs', hcsLen, hcsAt⟩ := ihCs 0 (some (h :: tl)) (fun hc => by cases hc) (by
          intro idx c hc rest m hm hnd i hi k hk
          rw [Nat.zero_add] at hnd ⊢
          have hna : nodeAt ⟨cs, ps, prot⟩ (((idx : Nat) : Int) :: rest) = some m := by
            rw [nwsr_nodeAt_cons_some cs ps prot (idx : Int) rest c (Int.natCast_nonneg idx) hc]
            exact hm
          exact hpoint (((idx : Nat) : Int) :: rest) m hna hnd i hi k hk)
        refine ⟨⟨cs', ps', prot⟩, ?_, ?_⟩
        · unfold Node.release_protector
          simp only [Option.isSome_some, ↓reduceIte, hps', bind, Except.bind, pure, Except.pure]
          have h0 : ((0 : Nat) : Int) = 0 := rfl
          rw [h0] at hcs'
          rw [hcs']
        · intro q
          cases q with
          | nil =>
            refine ⟨fun hn => (by cases hn), fun m hm => ?_⟩
            cases hm
            have hne : h :: tl ≠ [] := fun hc => by cases hc
            have hpreF : (h :: tl).isPrefixOf [] = false := rfl
            refine ⟨⟨cs', ps', prot⟩, rfl, ?_⟩
            unfold ReleasePost
            simp only [hne, hpreF, Bool.false_eq_true, ↓reduceIte, hlocRoot]
            refine ⟨trivial, hpsLen, fun b hb => hpsOut b (Or.inr (by omega)), fun i hi => ?_⟩
            have hstep := hpsIn i hi
            rw [Nat.zero_add] at hstep
            exact hstep
          | cons j rest =>
            rcases Decidable.em (0 ≤ j) with hj | hj
            · cases hc : cs[j.toNat]? with
              | none =>
                have hnone' : cs'[j.toNat]? = none := by
                  rw [List.getElem?_eq_none_iff] at hc ⊢; omega
                refine ⟨fun _ => nwsr_nodeAt_cons_none cs' ps' prot j rest hj hnone',
                  fun m hm => by rw [nwsr_nodeAt_cons_none cs ps prot j rest hj hc] at hm; cases hm⟩
              | some c =>
                obtain ⟨c', hc', hcrel⟩ := hcsAt j.toNat c hc
                have hjEq : ((0 + j.toNat : Nat) : Int) = j := by
                  rw [Nat.zero_add]; exact Int.toNat_of_nonneg hj
                rw [hjEq] at hcrel
                refine ⟨fun hn => ?_, fun m hm => ?_⟩
                · rw [nwsr_nodeAt_cons_some cs ps prot j rest c hj hc] at hn
                  rw [nwsr_nodeAt_cons_some cs' ps' prot j rest c' hj hc']
                  exact (hcrel rest).1 hn
                · rw [nwsr_nodeAt_cons_some cs ps prot j rest c hj hc] at hm
                  obtain ⟨m', hm', hrel⟩ := (hcrel rest).2 m hm
                  rw [nwsr_nodeAt_cons_some cs' ps' prot j rest c' hj hc']
                  exact ⟨m', hm', hrel⟩
            · refine ⟨fun _ => nwsr_nodeAt_cons_neg cs' ps' prot j rest hj,
                fun m hm => by rw [nwsr_nodeAt_cons_neg cs ps prot j rest hj] at hm; cases hm⟩
    | none =>
      have hpRoot : ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
          ∃ p p', ps[0 + i]? = some p ∧ Permission.transition p k .Foreign = .ok p' := by
        intro i hi k hk
        rw [Nat.zero_add]
        exact hpoint [] ⟨cs, ps, prot⟩ rfl rfl i hi k hk
      obtain ⟨ps', hps', hpsLen, hpsOut, hpsIn⟩ :=
        releaseProtectorPermissions_ok_of_pointwise .Foreign accesses 0 ps hpRoot
      obtain ⟨cs', hcs', hcsLen, hcsAt⟩ := ihCs 0 none (fun hc => by cases hc) (by
        intro idx c hc rest m hm hnd i hi k hk
        rw [Nat.zero_add] at hnd ⊢
        have hna : nodeAt ⟨cs, ps, prot⟩ (((idx : Nat) : Int) :: rest) = some m := by
          rw [nwsr_nodeAt_cons_some cs ps prot (idx : Int) rest c (Int.natCast_nonneg idx) hc]
          exact hm
        exact hpoint (((idx : Nat) : Int) :: rest) m hna hnd i hi k hk)
      refine ⟨⟨cs', ps', prot⟩, ?_, ?_⟩
      · unfold Node.release_protector
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hps', bind, Except.bind, pure, Except.pure]
        have h0 : ((0 : Nat) : Int) = 0 := rfl
        rw [h0] at hcs'
        rw [hcs']
      · intro q
        cases q with
        | nil =>
          refine ⟨fun hn => (by cases hn), fun m hm => ?_⟩
          cases hm
          refine ⟨⟨cs', ps', prot⟩, rfl, ?_⟩
          unfold ReleasePost
          refine ⟨rfl, hpsLen, fun b hb => hpsOut b (Or.inr (by omega)), fun i hi => ?_⟩
          have hstep := hpsIn i hi
          rw [Nat.zero_add] at hstep
          exact hstep
        | cons j rest =>
          rcases Decidable.em (0 ≤ j) with hj | hj
          · cases hc : cs[j.toNat]? with
            | none =>
              have hnone' : cs'[j.toNat]? = none := by
                rw [List.getElem?_eq_none_iff] at hc ⊢; omega
              refine ⟨fun _ => nwsr_nodeAt_cons_none cs' ps' prot j rest hj hnone',
                fun m hm => by rw [nwsr_nodeAt_cons_none cs ps prot j rest hj hc] at hm; cases hm⟩
            | some c =>
              obtain ⟨c', hc', hcrel⟩ := hcsAt j.toNat c hc
              have hjEq : ((0 + j.toNat : Nat) : Int) = j := by
                rw [Nat.zero_add]; exact Int.toNat_of_nonneg hj
              rw [hjEq] at hcrel
              refine ⟨fun hn => ?_, fun m hm => ?_⟩
              · rw [nwsr_nodeAt_cons_some cs ps prot j rest c hj hc] at hn
                rw [nwsr_nodeAt_cons_some cs' ps' prot j rest c' hj hc']
                exact (hcrel rest).1 hn
              · rw [nwsr_nodeAt_cons_some cs ps prot j rest c hj hc] at hm
                obtain ⟨m', hm', hrel⟩ := (hcrel rest).2 m hm
                rw [nwsr_nodeAt_cons_some cs' ps' prot j rest c' hj hc']
                exact ⟨m', hm', hrel⟩
          · refine ⟨fun _ => nwsr_nodeAt_cons_neg cs' ps' prot j rest hj,
              fun m hm => by rw [nwsr_nodeAt_cons_neg cs ps prot j rest hj] at hm; cases hm⟩
  case nilCase =>
    intro start path _ _
    exact ⟨[], rfl, rfl, fun idx c hc => by cases hc⟩
  case consCase =>
    intro hd tl ihHd ihTl start path hneNil hpoint
    let subPath : Option Gen.Path :=
      match path with
      | some (h :: t) => if h == (start : Int) then some t else none
      | _ => none
    have hhd : ∀ q m, nodeAt hd q = some m → b1_isTargetOrDesc subPath q = false →
        ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
          ∃ p p', m.permissions[i]? = some p ∧
            Permission.transition p k (locRel subPath q) = .ok p' := by
      intro q m hm hnd i hi k hk
      have hndParent : b1_isTargetOrDesc path (((start + 0 : Nat) : Int) :: q) = false := by
        rw [Nat.add_zero]
        cases path with
        | none => rfl
        | some tp =>
          cases tp with
          | nil => exact absurd rfl hneNil
          | cons h t =>
            dsimp only [b1_isTargetOrDesc, subPath] at hnd ⊢
            cases hbeq : (h == (start : Int)) with
            | true =>
              simp only [hbeq, ↓reduceIte] at hnd
              simp only [List.isPrefixOf, hbeq, Bool.true_and]
              exact hnd
            | false =>
              simp only [List.isPrefixOf, hbeq, Bool.false_and]
      have hlocEq : locRel path (((start + 0 : Nat) : Int) :: q) = locRel subPath q := by
        rw [Nat.add_zero]
        cases path with
        | none => rfl
        | some tp =>
          cases tp with
          | nil => exact absurd rfl hneNil
          | cons h t =>
            dsimp only [subPath]
            rcases Decidable.em (h = (start : Int)) with rfl | hne
            · simp only [a1_int_beq_self, ↓reduceIte, locRel]
              rw [locOf_some_eq_isPrefixOf, locOf_some_eq_isPrefixOf]
              simp only [List.isPrefixOf, a1_int_beq_self, Bool.true_and]
            · have hbeqF : (h == (start : Int)) = false := by
                cases hb : (h == (start : Int)) with
                | false => rfl
                | true => exact absurd ((a1_int_beq_iff h (start : Int)).mp hb) hne
              have hbeqF' : ((start : Int) == h) = false := by
                cases hb : ((start : Int) == h) with
                | false => rfl
                | true => exact absurd ((a1_int_beq_iff (start : Int) h).mp hb).symm hne
              simp only [hbeqF, Bool.false_eq_true, ↓reduceIte, locRel]
              rw [locOf_some_eq_isPrefixOf]
              simp only [List.isPrefixOf, hbeqF', Bool.false_and]
              rw [locOf_none q]
      rw [← hlocEq]
      exact hpoint 0 hd rfl q m hm hndParent i hi k hk
    obtain ⟨hd', hhd', hhdRel⟩ := ihHd subPath hhd
    have htl : ∀ idx c, tl[idx]? = some c →
        ∀ rest m, nodeAt c rest = some m →
          b1_isTargetOrDesc path ((((start + 1) + idx : Nat) : Int) :: rest) = false →
          ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
            ∃ p p', m.permissions[i]? = some p ∧
              Permission.transition p k (locRel path ((((start + 1) + idx : Nat) : Int) :: rest)) = .ok p' := by
      intro idx c hc rest m hm hnd i hi k hk
      have e : (start + 1) + idx = start + (idx + 1) := by omega
      rw [e] at hnd ⊢
      exact hpoint (idx + 1) c hc rest m hm hnd i hi k hk
    obtain ⟨tl', htl', htlLen, htlRel⟩ := ihTl (start + 1) path hneNil htl
    have haddInt : (start : Int) + 1 = ((start + 1 : Nat) : Int) := by omega
    refine ⟨hd' :: tl', ?_, by simp [htlLen], ?_⟩
    · unfold Node.releaseProtectorChildren
      dsimp only
      cases path with
      | none =>
        dsimp only [subPath] at hhd'
        simp only [hhd', haddInt, htl', bind, Except.bind, pure, Except.pure]
      | some tp =>
        cases tp with
        | nil => exact absurd rfl hneNil
        | cons h t =>
          dsimp only [subPath] at hhd'
          simp only [hhd', haddInt, htl', bind, Except.bind, pure, Except.pure]
    · intro idx c hc
      cases idx with
      | zero =>
        cases hc
        refine ⟨hd', rfl, fun rest => ⟨(hhdRel rest).1, fun m hm => ?_⟩⟩
        obtain ⟨m', hm', hr⟩ := (hhdRel rest).2 m hm
        rw [Nat.add_zero]
        refine ⟨m', hm', b1_releasePost_step_cons path accesses start rest m m' ?_ hneNil⟩
        cases path with
        | none => exact hr
        | some tp =>
          cases tp with
          | nil => exact absurd rfl hneNil
          | cons h t => exact hr
      | succ k =>
        obtain ⟨c', hc', hcr⟩ := htlRel k c hc
        have e : (start + 1) + k = start + (k + 1) := by omega
        rw [e] at hcr
        exact ⟨c', hc', hcr⟩

/-- **Whole-tree forward specification of `Node.release_protector`**: whenever
every non-target, non-descendant node satisfies the pointwise transition condition
on every `some k` entry of `accesses`, `Node.release_protector` succeeds and
transforms every node according to `ReleasePost` (unprotecting `targetPath`,
skipping its strict descendants, and transitioning all ancestors and foreign
non-descendants pointwise). -/
theorem node_release_protector_ok_of_pointwise (root : Gen.Node) (path : Option Gen.Path)
    (accesses : List (Option Gen.AccessKind))
    (hpoint : ∀ q m, nodeAt root q = some m →
      (match path with | some tp => tp.isPrefixOf q | none => false) = false →
      ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
        ∃ p p', m.permissions[i]? = some p ∧
          Permission.transition p k (locRel path q) = .ok p') :
    ∃ root', Node.release_protector root path accesses = .ok root' ∧
      ∀ q, (nodeAt root q = none → nodeAt root' q = none) ∧
        (∀ m, nodeAt root q = some m →
          ∃ m', nodeAt root' q = some m' ∧ ReleasePost path accesses q m m') :=
  b1_release_protector_mutual accesses root path hpoint

private theorem b1_release_protector_inv_mutual (accesses : List (Option Gen.AccessKind)) :
    ∀ (root : Gen.Node) (path : Option Gen.Path) (root' : Gen.Node),
      Node.release_protector root path accesses = .ok root' →
      ∀ q m, nodeAt root q = some m → b1_isTargetOrDesc path q = false →
        ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
          ∃ p p', m.permissions[i]? = some p ∧
            Permission.transition p k (locRel path q) = .ok p' := by
  refine @Gen.Node.rec
    (motive_1 := fun root =>
      ∀ (path : Option Gen.Path) (root' : Gen.Node),
        Node.release_protector root path accesses = .ok root' →
        ∀ q m, nodeAt root q = some m → b1_isTargetOrDesc path q = false →
          ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
            ∃ p p', m.permissions[i]? = some p ∧
              Permission.transition p k (locRel path q) = .ok p')
    (motive_2 := fun cs =>
      ∀ (start : Nat) (path : Option Gen.Path) (cs' : List Gen.Node),
        path ≠ some [] →
        Node.releaseProtectorChildren (start : Int) path accesses cs = .ok cs' →
        ∀ idx c, cs[idx]? = some c →
          ∀ rest m, nodeAt c rest = some m →
            b1_isTargetOrDesc path (((start + idx : Nat) : Int) :: rest) = false →
            ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
              ∃ p p', m.permissions[i]? = some p ∧
                Permission.transition p k (locRel path (((start + idx : Nat) : Int) :: rest)) = .ok p')
    ?nodeCase ?nilCase ?consCase
  case nodeCase =>
    intro cs ps prot ihCs path root' hok q m hm hnd i hi k hk
    cases path with
    | some tp =>
      cases tp with
      | nil => cases hnd
      | cons h tl =>
        unfold Node.release_protector at hok
        simp only [Option.isSome_some, ↓reduceIte] at hok
        obtain ⟨ps', hps', hok⟩ := nwsr_bind_ok hok
        obtain ⟨cs', hcs', hok⟩ := nwsr_bind_ok hok
        cases q with
        | nil =>
          cases hm
          have hinv := (releaseProtectorPermissions_ok_inv .Local accesses 0 ps ps' hps').2 i hi k hk
          rw [Nat.zero_add] at hinv
          exact hinv
        | cons j rest =>
          rcases Decidable.em (0 ≤ j) with hj | hj
          · cases hc : cs[j.toNat]? with
            | none => rw [nwsr_nodeAt_cons_none cs ps prot j rest hj hc] at hm; cases hm
            | some c =>
              rw [nwsr_nodeAt_cons_some cs ps prot j rest c hj hc] at hm
              have hjEq : ((0 + j.toNat : Nat) : Int) = j := by
                rw [Nat.zero_add]; exact Int.toNat_of_nonneg hj
              have hinv := ihCs 0 (some (h :: tl)) cs' (fun hc' => by cases hc') hcs'
                j.toNat c hc rest m hm (by rw [hjEq]; exact hnd) i hi k hk
              rw [hjEq] at hinv
              exact hinv
          · rw [nwsr_nodeAt_cons_neg cs ps prot j rest hj] at hm; cases hm
    | none =>
      unfold Node.release_protector at hok
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hok
      obtain ⟨ps', hps', hok⟩ := nwsr_bind_ok hok
      obtain ⟨cs', hcs', hok⟩ := nwsr_bind_ok hok
      cases q with
      | nil =>
        cases hm
        have hinv := (releaseProtectorPermissions_ok_inv .Foreign accesses 0 ps ps' hps').2 i hi k hk
        rw [Nat.zero_add] at hinv
        exact hinv
      | cons j rest =>
        rcases Decidable.em (0 ≤ j) with hj | hj
        · cases hc : cs[j.toNat]? with
          | none => rw [nwsr_nodeAt_cons_none cs ps prot j rest hj hc] at hm; cases hm
          | some c =>
            rw [nwsr_nodeAt_cons_some cs ps prot j rest c hj hc] at hm
            have hjEq : ((0 + j.toNat : Nat) : Int) = j := by
              rw [Nat.zero_add]; exact Int.toNat_of_nonneg hj
            have hinv := ihCs 0 none cs' (fun hc' => by cases hc') hcs'
              j.toNat c hc rest m hm (by rw [hjEq]; exact hnd) i hi k hk
            rw [hjEq] at hinv
            exact hinv
        · rw [nwsr_nodeAt_cons_neg cs ps prot j rest hj] at hm; cases hm
  case nilCase =>
    intro _ _ _ _ _ idx _ hc
    cases hc
  case consCase =>
    intro hd tl ihHd ihTl start path cs' hneNil hok idx c hc rest m hm hnd i hi k hk
    unfold Node.releaseProtectorChildren at hok
    obtain ⟨hd', hhd', hok⟩ := nwsr_bind_ok hok
    obtain ⟨tl', htl', _⟩ := nwsr_bind_ok hok
    cases idx with
    | zero =>
      cases hc
      rw [Nat.add_zero] at hnd ⊢
      let subPath : Option Gen.Path :=
        match path with
        | some (h :: t) => if h == (start : Int) then some t else none
        | _ => none
      have hndSub : b1_isTargetOrDesc subPath rest = false := by
        cases path with
        | none => rfl
        | some tp =>
          cases tp with
          | nil => exact absurd rfl hneNil
          | cons h t =>
            dsimp only [b1_isTargetOrDesc, subPath] at hnd ⊢
            cases hbeq : (h == (start : Int)) with
            | true =>
              simp only [List.isPrefixOf, hbeq, Bool.true_and] at hnd
              simp only [↓reduceIte]
              exact hnd
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
      have hlocEq : locRel path ((start : Int) :: rest) = locRel subPath rest := by
        cases path with
        | none => rfl
        | some tp =>
          cases tp with
          | nil => exact absurd rfl hneNil
          | cons h t =>
            dsimp only [subPath]
            rcases Decidable.em (h = (start : Int)) with rfl | hne
            · simp only [a1_int_beq_self, ↓reduceIte, locRel]
              rw [locOf_some_eq_isPrefixOf, locOf_some_eq_isPrefixOf]
              simp only [List.isPrefixOf, a1_int_beq_self, Bool.true_and]
            · have hbeqF : (h == (start : Int)) = false := by
                cases hb : (h == (start : Int)) with
                | false => rfl
                | true => exact absurd ((a1_int_beq_iff h (start : Int)).mp hb) hne
              have hbeqF' : ((start : Int) == h) = false := by
                cases hb : ((start : Int) == h) with
                | false => rfl
                | true => exact absurd ((a1_int_beq_iff (start : Int) h).mp hb).symm hne
              simp only [hbeqF, Bool.false_eq_true, ↓reduceIte, locRel]
              rw [locOf_some_eq_isPrefixOf]
              simp only [List.isPrefixOf, hbeqF', Bool.false_and]
              rw [locOf_none rest]
      rw [hlocEq]
      have hhd'' : Node.release_protector hd subPath accesses = .ok hd' := by
        cases path with
        | none => exact hhd'
        | some tp => cases tp with | nil => exact hhd' | cons _ _ => exact hhd'
      exact ihHd subPath hd' hhd'' rest m hm hndSub i hi k hk
    | succ j =>
      have haddInt : (start : Int) + 1 = ((start + 1 : Nat) : Int) := by omega
      rw [haddInt] at htl'
      have e : start + (j + 1) = (start + 1) + j := by omega
      rw [e] at hnd ⊢
      exact ihTl (start + 1) path tl' hneNil htl' j c hc rest m hm hnd i hi k hk

/-- **Whole-tree inversion of `Node.release_protector`**. -/
theorem node_release_protector_ok_inv (root root' : Gen.Node) (path : Option Gen.Path)
    (accesses : List (Option Gen.AccessKind))
    (hok : Node.release_protector root path accesses = .ok root') :
    ∀ q m, nodeAt root q = some m →
      (match path with | some tp => tp.isPrefixOf q | none => false) = false →
      ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
        ∃ p p', m.permissions[i]? = some p ∧
          Permission.transition p k (locRel path q) = .ok p' := by
  intro q m hm hnd
  have hnd' : b1_isTargetOrDesc path q = false := by
    cases path <;> exact hnd
  exact b1_release_protector_inv_mutual accesses root path root' hok q m hm hnd'

private theorem b1_release_protector_err_ub_mutual (accesses : List (Option Gen.AccessKind)) :
    ∀ (root : Gen.Node) (path : Option Gen.Path) (e : Stop),
      (∀ q m, nodeAt root q = some m → accesses.length ≤ m.permissions.length) →
      Node.release_protector root path accesses = .error e →
      ∃ msg, e = .ub msg := by
  refine @Gen.Node.rec
    (motive_1 := fun root =>
      ∀ (path : Option Gen.Path) (e : Stop),
        (∀ q m, nodeAt root q = some m → accesses.length ≤ m.permissions.length) →
        Node.release_protector root path accesses = .error e →
        ∃ msg, e = .ub msg)
    (motive_2 := fun cs =>
      ∀ (start : Int) (path : Option Gen.Path) (e : Stop),
        (∀ (idx : Nat) (c : Gen.Node), cs[idx]? = some c → ∀ rest m, nodeAt c rest = some m →
          accesses.length ≤ m.permissions.length) →
        Node.releaseProtectorChildren start path accesses cs = .error e →
        ∃ msg, e = .ub msg)
    ?nodeCase ?nilCase ?consCase
  case nodeCase =>
    intro cs ps prot ihCs path e hlen herr
    cases path with
    | some tp =>
      cases tp with
      | nil => cases herr
      | cons h tl =>
        unfold Node.release_protector at herr
        simp only [Option.isSome_some, ↓reduceIte] at herr
        rcases nwsr_bind_err herr with hpsErr | ⟨ps', _, hrest⟩
        · exact releaseProtectorPermissions_error_is_ub .Local accesses 0 ps e
            (by rw [Nat.zero_add]; exact hlen [] ⟨cs, ps, prot⟩ rfl) hpsErr
        · rcases nwsr_bind_err hrest with hcsErr | ⟨cs', _, hfin⟩
          · exact ihCs 0 (some (h :: tl)) e (fun idx c hc rest m hm =>
              hlen (((idx : Nat) : Int) :: rest) m (by
                rw [nwsr_nodeAt_cons_some cs ps prot (idx : Int) rest c (Int.natCast_nonneg idx) hc]
                exact hm)) hcsErr
          · cases hfin
    | none =>
      unfold Node.release_protector at herr
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at herr
      rcases nwsr_bind_err herr with hpsErr | ⟨ps', _, hrest⟩
      · exact releaseProtectorPermissions_error_is_ub .Foreign accesses 0 ps e
          (by rw [Nat.zero_add]; exact hlen [] ⟨cs, ps, prot⟩ rfl) hpsErr
      · rcases nwsr_bind_err hrest with hcsErr | ⟨cs', _, hfin⟩
        · exact ihCs 0 none e (fun idx c hc rest m hm =>
            hlen (((idx : Nat) : Int) :: rest) m (by
              rw [nwsr_nodeAt_cons_some cs ps prot (idx : Int) rest c (Int.natCast_nonneg idx) hc]
              exact hm)) hcsErr
        · cases hfin
  case nilCase =>
    intro _ _ _ _ herr; cases herr
  case consCase =>
    intro hd tl ihHd ihTl start path e hlen herr
    unfold Node.releaseProtectorChildren at herr
    rcases nwsr_bind_err herr with hhdErr | ⟨hd', _, hrest⟩
    · exact ihHd _ e (fun rest m hm => hlen 0 hd rfl rest m hm) hhdErr
    · rcases nwsr_bind_err hrest with htlErr | ⟨tl', _, hfin⟩
      · exact ihTl (start + 1) path e (fun idx c hc rest m hm => hlen (idx + 1) c hc rest m hm) htlErr
      · cases hfin

/-- Any error from `Node.release_protector` when `accesses.length` fits in every node's
permission list is `Stop.ub`. -/
theorem node_release_protector_error_is_ub (root : Gen.Node) (path : Option Gen.Path)
    (accesses : List (Option Gen.AccessKind)) (e : Stop)
    (hlen : ∀ q m, nodeAt root q = some m → accesses.length ≤ m.permissions.length)
    (herr : Node.release_protector root path accesses = .error e) :
    ∃ msg, e = .ub msg :=
  b1_release_protector_err_ub_mutual accesses root path e hlen herr

/-! #### Choice-Free `Node.wf` and `TreeBorrowsMemory.wfLive` Preservation for `release_protector` / `end_call` -/

private theorem b1_childrenWf_iff (size : Nat) :
    ∀ cs : List Gen.Node, Node.childrenWf size cs ↔ ∀ c ∈ cs, Node.wf size c
  | [] => ⟨fun _ _ h => (by cases h), fun _ => trivial⟩
  | c :: cs => by
    constructor
    · rintro ⟨hc, hcs⟩ d hd
      rcases List.mem_cons.mp hd with rfl | hmem
      · exact hc
      · exact (b1_childrenWf_iff size cs).mp hcs d hmem
    · intro hall
      exact ⟨hall c (List.mem_cons_self ..),
        (b1_childrenWf_iff size cs).mpr (fun d hd => hall d (List.mem_cons_of_mem _ hd))⟩

private def b1_nodeWfUnprotAt (size : Nat) : Gen.Path → Gen.Node → Prop
  | [], ⟨cs, ps, _⟩ =>
    ps.length = size ∧ (∀ p ∈ ps, Permission.matches_protector p .No = true) ∧
      Node.childrenWf size cs
  | h :: tl, ⟨cs, ps, prot⟩ =>
    ps.length = size ∧ (∀ p ∈ ps, Permission.matches_protector p prot = true) ∧
      ∀ (idx : Nat) (c : Gen.Node), cs[idx]? = some c →
        if (h == (idx : Int)) then b1_nodeWfUnprotAt size tl c else Node.wf size c

private def b1_nodeWfOpt (size : Nat) : Option Gen.Path → Gen.Node → Prop
  | some p, n => b1_nodeWfUnprotAt size p n
  | none, n => Node.wf size n

private theorem b1_access_node_wfUnprotAt {O : Type} (size : Nat)
    (f : Gen.Node → Interp (O × Gen.Node))
    (hf : ∀ u u' o, Node.wf size u → f u = .ok (o, u') →
      u'.permissions.length = size ∧
      (∀ p ∈ u'.permissions, Permission.matches_protector p .No = true) ∧
      Node.childrenWf size u'.children) :
    ∀ (path : Gen.Path) (root root' : Gen.Node) (o : O),
      Node.wf size root →
      Node.access_node f path root = .ok (o, root') →
      b1_nodeWfUnprotAt size path root'
  | [], root, root', o, hwf, hacc => by
    rcases root' with ⟨cs', ps', pr'⟩
    exact hf root ⟨cs', ps', pr'⟩ o hwf hacc
  | h :: tl, ⟨cs, ps, prot⟩, root', o, hwf, hacc => by
    unfold Node.access_node at hacc
    cases hleaf : Node.is_leaf ⟨cs, ps, prot⟩ with
    | true => simp only [hleaf, ↓reduceIte] at hacc; cases hacc
    | false =>
      simp only [hleaf, Bool.false_eq_true, ↓reduceIte] at hacc
      obtain ⟨⟨o', cs'⟩, hmut, hpure⟩ := nwsr_bind_ok hacc
      injection hpure with hp'
      have hoEq : o' = o := congrArg Prod.fst hp'
      have hrEq : { children := cs', permissions := ps, «protected» := prot } = root' := congrArg Prod.snd hp'
      subst hoEq; subst hrEq
      obtain ⟨c, c', hge, hlt, hc, hrec, rfl⟩ := b1_listMutateAt_ok hmut
      have hcw : Node.wf size c := (b1_childrenWf_iff size cs).mp hwf.2.2 c (List.mem_of_getElem? hc)
      have hc'w : b1_nodeWfUnprotAt size tl c' := b1_access_node_wfUnprotAt size f hf tl c c' o' hcw hrec
      refine ⟨hwf.1, hwf.2.1, fun idx d hd => ?_⟩
      rcases Decidable.em (h = (idx : Int)) with rfl | hne
      · have hto : (idx : Int).toNat = idx := rfl
        rw [hto] at hd
        rw [List.getElem?_set_self (by rw [hto] at hlt; exact hlt)] at hd
        cases hd
        rw [a1_int_beq_self]
        exact hc'w
      · have hbeqF : (h == (idx : Int)) = false := by
          cases hb : (h == (idx : Int)) with
          | false => rfl
          | true => exact absurd ((a1_int_beq_iff h (idx : Int)).mp hb) hne
        have hneNat : h.toNat ≠ idx := by
          intro heq
          apply hne
          have h1 : (h.toNat : Int) = h := Int.toNat_of_nonneg hge
          rw [heq] at h1
          exact h1.symm
        rw [List.getElem?_set_ne hneNat] at hd
        rw [hbeqF]
        exact (b1_childrenWf_iff size cs).mp hwf.2.2 d (List.mem_of_getElem? hd)

private theorem b1_release_protector_wf_mutual (size : Nat) (accesses : List (Option Gen.AccessKind)) :
    ∀ (root : Gen.Node) (path : Option Gen.Path) (root' : Gen.Node),
      b1_nodeWfOpt size path root →
      Node.release_protector root path accesses = .ok root' →
      Node.wf size root' := by
  refine @Gen.Node.rec
    (motive_1 := fun root =>
      ∀ (path : Option Gen.Path) (root' : Gen.Node),
        b1_nodeWfOpt size path root →
        Node.release_protector root path accesses = .ok root' →
        Node.wf size root')
    (motive_2 := fun cs =>
      ∀ (start : Nat) (path : Option Gen.Path) (cs' : List Gen.Node),
        path ≠ some [] →
        (∀ (idx : Nat) (c : Gen.Node), cs[idx]? = some c →
          match path with
          | some (h :: tl) => if h == ((start + idx : Nat) : Int) then b1_nodeWfUnprotAt size tl c else Node.wf size c
          | _ => Node.wf size c) →
        Node.releaseProtectorChildren (start : Int) path accesses cs = .ok cs' →
        Node.childrenWf size cs')
    ?nodeCase ?nilCase ?consCase
  case nodeCase =>
    intro cs ps prot ihCs path root' hwf hok
    cases path with
    | some tp =>
      cases tp with
      | nil =>
        cases hok
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | cons h tl =>
        unfold Node.release_protector at hok
        simp only [Option.isSome_some, ↓reduceIte] at hok
        obtain ⟨ps', hps', hok⟩ := nwsr_bind_ok hok
        obtain ⟨cs', hcs', hok⟩ := nwsr_bind_ok hok
        cases hok
        obtain ⟨hpsLen, hpsMp⟩ := Node.releaseProtectorPermissions_wf .Local prot accesses 0 ps ps' hwf.2.1 hps'
        have hcsWf := ihCs 0 (some (h :: tl)) cs' (fun hc => by cases hc) (fun idx c hc => by
          rw [Nat.zero_add]; exact hwf.2.2 idx c hc) hcs'
        exact ⟨hpsLen.trans hwf.1, hpsMp, hcsWf⟩
    | none =>
      unfold Node.release_protector at hok
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hok
      obtain ⟨ps', hps', hok⟩ := nwsr_bind_ok hok
      obtain ⟨cs', hcs', hok⟩ := nwsr_bind_ok hok
      cases hok
      obtain ⟨hpsLen, hpsMp⟩ := Node.releaseProtectorPermissions_wf .Foreign prot accesses 0 ps ps' hwf.2.1 hps'
      have hcsWf := ihCs 0 none cs' (fun hc => by cases hc) (fun idx c hc =>
        (b1_childrenWf_iff size cs).mp hwf.2.2 c (List.mem_of_getElem? hc)) hcs'
      exact ⟨hpsLen.trans hwf.1, hpsMp, hcsWf⟩
  case nilCase =>
    intro _ _ cs' _ _ hok
    cases hok
    trivial
  case consCase =>
    intro hd tl ihHd ihTl start path cs' hneNil hwf hok
    unfold Node.releaseProtectorChildren at hok
    obtain ⟨hd', hhd', hok⟩ := nwsr_bind_ok hok
    obtain ⟨tl', htl', hok⟩ := nwsr_bind_ok hok
    cases hok
    constructor
    · have hhd0 := hwf 0 hd rfl
      rw [Nat.add_zero] at hhd0
      cases path with
      | none => exact ihHd none hd' hhd0 hhd'
      | some tp =>
        cases tp with
        | nil => exact absurd rfl hneNil
        | cons h t =>
          cases hbeq : (h == (start : Int)) with
          | true =>
            simp only [hbeq, ↓reduceIte] at hhd0 hhd'
            exact ihHd (some t) hd' hhd0 hhd'
          | false =>
            simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hhd0 hhd'
            exact ihHd none hd' hhd0 hhd'
    · have haddInt : (start : Int) + 1 = ((start + 1 : Nat) : Int) := by omega
      rw [haddInt] at htl'
      exact ihTl (start + 1) path tl' hneNil (fun idx c hc => by
        have e : (start + 1) + idx = start + (idx + 1) := by omega
        rw [e]
        exact hwf (idx + 1) c hc) htl'

/-- **Choice-free `TreeBorrowsMemory.release_protector` preservation of `wfLive`**
(zero `Classical.choice`, depending only on `{propext, Quot.sound}`). -/
theorem tbm_release_protector_wfLive_choiceFree {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {provenance : Gen.TreeBorrowsProvenance}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.release_protector tbm provenance = .ok tbm') :
    TreeBorrowsMemory.wfLive tbm' := by
  rcases provenance with ⟨allocId, path⟩
  unfold TreeBorrowsMemory.release_protector at h
  obtain ⟨⟨_, allocations'⟩, hpair, h⟩ := nwsr_bind_ok h
  cases h
  obtain ⟨allocation, alloc', _, _, hget, hf, rfl⟩ := b1_listMutateAt_ok hpair
  intro alloc hm' hlive
  rcases b1_mem_set_or hm' with rfl | hm''
  · obtain ⟨⟨protectorAccesses, root1⟩, hacc, hf⟩ := nwsr_bind_ok hf
    cases halloc_live : allocation.live with
    | false =>
      simp only [halloc_live, Bool.not_false, ↓reduceIte] at hf
      cases hf
      simp at hlive
    | true =>
      simp only [halloc_live, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hf
      obtain ⟨root2, hrel, hf⟩ := nwsr_bind_ok hf
      cases hf
      have hroot0 := hwf allocation (List.mem_of_getElem? hget) halloc_live
      have hroot1 : b1_nodeWfOpt (Allocation.size allocation).bytes (some path) root1 := by
        refine b1_access_node_wfUnprotAt (Allocation.size allocation).bytes _
          (fun u u' o hu hfu => ?_) path allocation.extra.root root1 protectorAccesses hroot0 hacc
        rcases u with ⟨uch, uperms, uprot⟩
        cases hy : Protected.yes uprot with
        | false =>
          simp only [hy, Bool.not_false, ↓reduceIte] at hfu; cases hfu
        | true =>
          simp only [hy, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfu
          obtain ⟨pairs, hmap, hpure⟩ := nwsr_bind_ok hfu
          cases hpure
          have hunp : ∀ x y, Permission.unprotect x = .ok y →
              Permission.matches_protector y.1 .No = true := by
            intro x y hx
            cases x with
            | Unprot _ => cases hx
            | Prot _ => cases hx; rfl
          obtain ⟨_, hbody⟩ := b1_list_mapM_loop_inv hunp uperms [] pairs hmap
          obtain ⟨ys, heq, hylen, hyP⟩ := hbody (fun _ h' => by cases h')
          simp only [List.reverse_nil, List.nil_append] at heq
          subst heq
          refine ⟨by rw [List.length_map, hylen, hu.1], fun p hp => ?_, hu.2.2⟩
          obtain ⟨pair, hpm, rfl⟩ := List.mem_map.mp hp
          obtain ⟨_, hmp⟩ := hyP pair hpm
          exact hmp
      exact b1_release_protector_wf_mutual (Allocation.size allocation).bytes protectorAccesses
        root1 (some path) root2 hroot1 hrel
  · exact hwf alloc hm'' hlive

/-- **Choice-free `TreeBorrowsMemory.end_call` preservation of `wfLive`**
(zero `Classical.choice`, depending only on `{propext, Quot.sound}`). -/
theorem tbm_end_call_wfLive_choiceFree {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {extra : Gen.TreeBorrowsFrameExtra}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.end_call tbm extra = .ok tbm') :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.end_call at h
  have key : ∀ (ps : List Gen.TreeBorrowsProvenance)
      (acc out : Gen.TreeBorrowsMemory Gen.x86_64),
      TreeBorrowsMemory.wfLive acc →
      ps.foldlM (fun a prov => TreeBorrowsMemory.release_protector a prov) acc = .ok out →
      TreeBorrowsMemory.wfLive out := by
    intro ps
    induction ps with
    | nil =>
      intro acc out hacc hf
      rw [List.foldlM_nil] at hf
      cases hf
      exact hacc
    | cons prov rest ih =>
      intro acc out hacc hf
      rw [List.foldlM_cons] at hf
      obtain ⟨mid, hr, hf⟩ := nwsr_bind_ok hf
      exact ih mid out (tbm_release_protector_wfLive_choiceFree hacc hr) hf
  exact key extra.protectors tbm tbm' hwf h

/-! #### Algebraic Equations & Dead-Allocation Short-Circuit for `TreeBorrowsMemory.release_protector` -/

/-- Algebraic equation for `TreeBorrowsMemory.release_protector` on a live allocation. -/
theorem tbm_release_protector_eq (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (id : Nat) (path : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
    (target : Gen.Node) (pairs : List (Gen.Permission × Option Gen.AccessKind))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (htarget : nodeAt alloc.extra.root path = some target)
    (hprot : Protected.yes target.«protected» = true)
    (hunprot : target.permissions.mapM Permission.unprotect = .ok pairs) :
    let target' : Gen.Node := { target with permissions := pairs.map Prod.fst }
    let accesses : List (Option Gen.AccessKind) := pairs.map Prod.snd
    ∃ root1,
      Node.access_node (fun node => do
        if !Protected.yes node.«protected» then
          specPanic "assertion failed: node.protected.yes()"
        else do
          let ps ← node.permissions.mapM Permission.unprotect
          pure (ps.map Prod.snd, { node with permissions := ps.map Prod.fst })) path alloc.extra.root =
        .ok (accesses, root1) ∧
      (∀ suf, nodeAt root1 (path ++ suf) = nodeAt target' suf) ∧
      (∀ q, path.isPrefixOf q = false →
        (nodeAt alloc.extra.root q = none → nodeAt root1 q = none) ∧
        (∀ m, nodeAt alloc.extra.root q = some m →
          ∃ m', nodeAt root1 q = some m' ∧
            m'.permissions = m.permissions ∧ m'.«protected» = m.«protected» ∧
            (q.isPrefixOf path = false → m' = m))) ∧
      TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, path) =
        (Node.release_protector root1 (some path) accesses >>= fun root2 =>
          pure { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id { alloc with extra := { root := root2 } }) } }) := by
  let f : Gen.Node → Interp (List (Option Gen.AccessKind) × Gen.Node) := fun node => do
    if !Protected.yes node.«protected» then
      specPanic "assertion failed: node.protected.yes()"
    else do
      let ps ← node.permissions.mapM Permission.unprotect
      pure (ps.map Prod.snd, { node with permissions := ps.map Prod.fst })
  have hf : f target = .ok (pairs.map Prod.snd, { target with permissions := pairs.map Prod.fst }) := by
    dsimp only [f]
    simp only [hprot, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hunprot, bind, Except.bind,
      pure, Except.pure]
  obtain ⟨root1, hacc, hsuf, hother⟩ :=
    node_access_node_spec f path alloc.extra.root target
      { target with permissions := pairs.map Prod.fst } (pairs.map Prod.snd) htarget hf
  refine ⟨root1, hacc, hsuf, hother, ?_⟩
  unfold TreeBorrowsMemory.release_protector
  dsimp only
  rw [a1_listMutateAt_natCast _ _ _ _ alloc halloc]
  have hacc' : Node.access_node (fun node => do
      if !Protected.yes node.«protected» then
        specPanic "assertion failed: node.protected.yes()"
      else do
        let ps ← node.permissions.mapM Permission.unprotect
        let perms := ps.map Prod.fst
        let accesses := ps.map Prod.snd
        pure (accesses, { node with permissions := perms })) path alloc.extra.root =
      .ok (pairs.map Prod.snd, root1) := hacc
  rw [hacc']
  simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  cases Node.release_protector root1 (some path) (pairs.map Prod.snd) <;> rfl

/-- **Dead-allocation `release_protector` short-circuit**: if a protected
allocation (such as a `Box<T>` with `Protected::Weak`) was already deallocated
(`alloc.live = false`), `TreeBorrowsMemory.release_protector` unprotects the
target node's permissions and immediately succeeds without performing any
implicit protector-end tree traversal, preserving `TreeBorrowsMemory.wfLive`. -/
theorem tbm_release_protector_deadAlloc_ok (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (id : Nat) (path : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
    (target : Gen.Node) (pairs : List (Gen.Permission × Option Gen.AccessKind))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hdead : alloc.live = false)
    (htarget : nodeAt alloc.extra.root path = some target)
    (hprot : Protected.yes target.«protected» = true)
    (hunprot : target.permissions.mapM Permission.unprotect = .ok pairs) :
    ∃ tbm' alloc',
      TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, path) = .ok tbm' ∧
      tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = false ∧
      (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm') := by
  let f : Gen.Node → Interp (List (Option Gen.AccessKind) × Gen.Node) := fun node => do
    if !Protected.yes node.«protected» then
      specPanic "assertion failed: node.protected.yes()"
    else do
      let ps ← node.permissions.mapM Permission.unprotect
      pure (ps.map Prod.snd, { node with permissions := ps.map Prod.fst })
  have hf : f target = .ok (pairs.map Prod.snd, { target with permissions := pairs.map Prod.fst }) := by
    dsimp only [f]
    simp only [hprot, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hunprot, bind, Except.bind,
      pure, Except.pure]
  obtain ⟨root1, hacc, _, _⟩ :=
    node_access_node_spec f path alloc.extra.root target
      { target with permissions := pairs.map Prod.fst } (pairs.map Prod.snd) htarget hf
  have hrel : TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, path) =
      .ok { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id { alloc with extra := { root := root1 } }) } } := by
    unfold TreeBorrowsMemory.release_protector
    dsimp only
    rw [a1_listMutateAt_natCast _ _ _ _ alloc halloc]
    have hacc' : Node.access_node (fun node => do
        if !Protected.yes node.«protected» then
          specPanic "assertion failed: node.protected.yes()"
        else do
          let ps ← node.permissions.mapM Permission.unprotect
          let perms := ps.map Prod.fst
          let accesses := ps.map Prod.snd
          pure (accesses, { node with permissions := perms })) path alloc.extra.root =
        .ok (pairs.map Prod.snd, root1) := hacc
    rw [hacc']
    simp only [hdead, Bool.not_false, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  exact ⟨_, _, hrel, List.getElem?_set_self hidlt, hdead,
    fun hwf => tbm_release_protector_wfLive_choiceFree hwf hrel⟩

/-! #### Symbolic Whole-Tree `TreeSimInv` Simulation for `release_protector` & Multi-Entry `end_call` -/

private theorem b1_unprotect_permToMiniRust (n : TreeTagNode) (p : Gen.Permission)
    (hp : permToMiniRust true n.accessed n.perm = some p)
    (hnoIM : n.perm ≠ .reservedIM) (huniq : n.perm = .unique → n.accessed = true) :
    ∃ p',
      Permission.unprotect p =
        .ok (p', (protectorEndAccessIsWriteMiniRust? n).map (fun isW => if isW then .Write else .Read)) ∧
      permToMiniRust false n.accessed n.perm = some p' := by
  rcases n with ⟨tag, par, perm, ro, rl, prot, acc⟩
  cases perm with
  | reservedIM => exact absurd rfl hnoIM
  | unique =>
    have ha : acc = true := huniq rfl
    subst ha
    cases hp
    exact ⟨.Unprot .Unique, rfl, rfl⟩
  | frozen =>
    cases acc <;> (cases hp; exact ⟨.Unprot .Frozen, rfl, rfl⟩)
  | reservedFrz c =>
    cases c <;> cases acc <;> (cases hp; exact ⟨.Unprot .Reserved, rfl, rfl⟩)
  | cell =>
    cases acc <;> (cases hp; exact ⟨.Unprot .Cell, rfl, rfl⟩)
  | disabled =>
    cases acc <;> (cases hp; exact ⟨.Unprot .Disabled, rfl, rfl⟩)

private theorem b1_protectorEnd_self_invariant_miniRust (ap : List Nat) (off len : Nat) (n : TreeTagNode)
    (isWrite : Bool) (hk : protectorEndAccessIsWriteMiniRust? n = some isWrite)
    (huniq : n.perm = .unique → n.accessed = true) :
    stepNodeOnRangeAccess ap isWrite true off len n = .ok n := by
  rcases n with ⟨tag, par, perm, ro, rl, prot, acc⟩
  unfold protectorEndAccessIsWriteMiniRust? at hk
  cases perm with
  | unique =>
    have ha : acc = true := huniq rfl
    subst ha
    cases hk
    unfold stepNodeOnRangeAccess stepNodeOnRangeWrite
    cases rangesOverlap off len ro rl <;> rfl
  | frozen =>
    cases acc with
    | false => cases hk
    | true =>
      cases hk
      unfold stepNodeOnRangeAccess stepNodeOnRangeRead
      cases rangesOverlap off len ro rl <;> rfl
  | reservedFrz c =>
    cases acc with
    | false => cases hk
    | true =>
      cases hk
      unfold stepNodeOnRangeAccess stepNodeOnRangeRead
      cases rangesOverlap off len ro rl <;> rfl
  | reservedIM =>
    cases acc with
    | false => cases hk
    | true =>
      cases hk
      unfold stepNodeOnRangeAccess stepNodeOnRangeRead
      cases rangesOverlap off len ro rl <;> rfl
  | cell => cases hk
  | disabled => cases hk

private theorem b1_isProtected_releaseProtector_self (n : TreeTagNode) (protId : Nat) (ap : List Nat)
    (hp : n.protector = some protId) :
    n.isProtected (ap.filter (· != protId)) = false := by
  unfold TreeTagNode.isProtected
  rw [hp]
  cases h : (ap.filter (· != protId)).any (fun q => q == protId) with
  | false => exact h
  | true =>
    rw [List.any_eq_true] at h
    obtain ⟨q, hmem, hq⟩ := h
    rw [List.mem_filter] at hmem
    have heq : q = protId := eq_of_beq hq
    subst heq
    have hne : (q != q) = false := by simp [bne]
    rw [hne] at hmem
    cases hmem.2

private theorem b1_isProtected_releaseProtector_other (n : TreeTagNode) (protId : Nat) (ap : List Nat)
    (hne : n.protector ≠ some protId) :
    n.isProtected (ap.filter (· != protId)) = n.isProtected ap := by
  unfold TreeTagNode.isProtected
  cases hp : n.protector with
  | none => rfl
  | some q =>
    have hqp : q ≠ protId := fun h => hne (by rw [hp, h])
    have hbne : (q != protId) = true := by simp [bne, hqp]
    cases h1 : (ap.filter (· != protId)).any (fun r => r == q) <;> cases h2 : ap.any (fun r => r == q)
    · exact h1.trans h2.symm
    · exfalso
      rw [List.any_eq_true] at h2
      obtain ⟨r, hr, hrq⟩ := h2
      have hreq : r = q := eq_of_beq hrq
      subst hreq
      have h1' : (ap.filter (· != protId)).any (fun s => s == r) = true :=
        List.any_eq_true.mpr ⟨r, List.mem_filter.mpr ⟨hr, hbne⟩, beq_self_eq_true r⟩
      rw [h1'] at h1; cases h1
    · exfalso
      rw [List.any_eq_true] at h1
      obtain ⟨r, hr, hrq⟩ := h1
      rw [List.mem_filter] at hr
      have h2' : ap.any (fun s => s == q) = true := List.any_eq_true.mpr ⟨r, hr.1, hrq⟩
      rw [h2'] at h2; cases h2
    · exact h1.trans h2.symm

private theorem b1_isPrefixOf_refl : ∀ (p : Gen.Path), p.isPrefixOf p = true
  | [] => rfl
  | h :: tl => by simp only [List.isPrefixOf, a1_int_beq_self, Bool.true_and]; exact b1_isPrefixOf_refl tl

private theorem b1_nodeAt_prefix_eq {p q : Gen.Path} :
    p.isPrefixOf q = true → q.isPrefixOf p = true → p = q := by
  induction p generalizing q with
  | nil => intro _ h2; cases q with | nil => rfl | cons _ _ => cases h2
  | cons a ps ih =>
    intro h1 h2
    cases q with
    | nil => cases h1
    | cons b qs =>
      simp only [List.isPrefixOf, Bool.and_eq_true, a1_int_beq_iff] at h1 h2
      rw [h1.1, ih h1.2 h2.2]

/-- Purely topological no-nested-foreign-ancestors predicate on `nodes` for access
source `srcTag`: every non-ancestor node's strict ancestors already lie on the
access path to `srcTag`. Preserved automatically across all permission-only
steps (`ListRel NodeMetaRel`) and implies zero foreign subtree pruning. This is a
SHALLOW-TREE condition (no node off the access path may have a parent off the
access path, so a released node has no grandchildren); the arbitrary-depth
frame-exit theorem uses `FrameExitPruneInert` instead. -/
def NoNestedForeignAncestors (nodes : List TreeTagNode) (srcTag : Nat) : Prop :=
  ∀ n ∈ nodes, (ancestorPathTags nodes srcTag).contains n.tag = false →
    ∀ t ∈ (ancestorPathTags nodes n.tag).tail,
      (ancestorPathTags nodes srcTag).contains t = true

private theorem b1_noNestedForeignAncestors_imp_not_pruned (nodes : List TreeTagNode)
    (srcTag : Nat) (isWrite : Bool) (off len : Nat)
    (h : NoNestedForeignAncestors nodes srcTag) :
    ∀ n ∈ nodes, isPrunedForeignNode nodes (ancestorPathTags nodes srcTag) isWrite off len n = false := by
  intro n hn
  unfold isPrunedForeignNode
  cases ha : (ancestorPathTags nodes srcTag).contains n.tag with
  | true => simp
  | false =>
    simp only [Bool.not_false, Bool.true_and]
    cases hany : ((ancestorPathTags nodes n.tag).tail.any fun t =>
        !(ancestorPathTags nodes srcTag).contains t &&
          match findNode? nodes t with
          | some a => foreignNodeSkipsSubtree isWrite off len a
          | none => false) with
    | false => exact hany
    | true =>
      rw [List.any_eq_true] at hany
      obtain ⟨t, ht, hcond⟩ := hany
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hc := h n hn ha t ht
      rw [hc] at hcond
      cases hcond.1

/-- Outside-window bytes of node `m` carry protected permissions whose `unprotect`
requests no implicit access (`none`), matching `ReborrowSettings.outside = .Prot (.Reserved false false)`
(and vacuously satisfied when `m.permissions.length = off + len`, e.g., full-allocation windows). -/
def OutsideNoProtectorAccess (off len : Nat) (m : Gen.Node) : Prop :=
  ∀ b p, m.permissions[b]? = some p → (b < off ∨ off + len ≤ b) →
    ∃ p', Permission.unprotect p = .ok (p', none)

private theorem b1_eq_of_mem_of_findNode?_of_nodup :
    ∀ (nodes : List TreeTagNode) (t : Nat) (n pn : TreeTagNode),
      (nodes.map (·.tag)).Nodup →
      n ∈ nodes → n.tag = t → findNode? nodes t = some pn → n = pn
  | [], _, _, _, _, hmem, _, _ => by cases hmem
  | hd :: tl, t, n, pn, hnd, hmem, htag, hfn => by
    rw [List.map_cons, List.nodup_cons] at hnd
    unfold findNode? at hfn
    simp only [List.find?] at hfn
    cases hbeq : (hd.tag == t) with
    | true =>
      have hhdT : hd.tag = t := eq_of_beq hbeq
      simp only [hbeq] at hfn
      cases hfn
      rcases List.mem_cons.mp hmem with rfl | htl
      · rfl
      · exfalso
        apply hnd.1
        rw [hhdT, ← htag]
        exact List.mem_map.mpr ⟨n, htl, rfl⟩
    | false =>
      simp only [hbeq] at hfn
      rcases List.mem_cons.mp hmem with rfl | htl
      · exfalso
        have : (n.tag == t) = true := by rw [htag]; exact beq_self_eq_true t
        rw [this] at hbeq; cases hbeq
      · exact b1_eq_of_mem_of_findNode?_of_nodup tl t n pn hnd.2 htl htag hfn

private theorem b1_listRel_nodeMetaRel_findNode? :
    ∀ {xs ys : List TreeTagNode}, ListRel NodeMetaRel xs ys →
      ∀ t, (findNode? xs t = none → findNode? ys t = none) ∧
        (∀ x, findNode? xs t = some x → ∃ y, findNode? ys t = some y ∧ NodeMetaRel x y)
  | [], [], ListRel.nil, _ => ⟨fun _ => rfl, fun _ h => (by cases h)⟩
  | x :: xs, y :: ys, ListRel.cons hxy hrest, t => by
    unfold findNode?
    simp only [List.find?, hxy.1]
    cases hbeq : (x.tag == t) with
    | true => exact ⟨fun h => (by cases h), fun z hz => by cases hz; exact ⟨y, rfl, hxy⟩⟩
    | false => exact b1_listRel_nodeMetaRel_findNode? hrest t

private theorem b1_listRel_nodeMetaRel_ancestorPathTags_aux :
    ∀ (fuel : Nat) {xs ys : List TreeTagNode}, ListRel NodeMetaRel xs ys →
      ∀ t, ancestorPathTagsAux ys fuel t = ancestorPathTagsAux xs fuel t
  | 0, _, _, _, _ => rfl
  | fuel + 1, xs, ys, hrel, t => by
    unfold ancestorPathTagsAux
    cases hfn : findNode? xs t with
    | none =>
      rw [(b1_listRel_nodeMetaRel_findNode? hrel t).1 hfn]
    | some x =>
      obtain ⟨y, hy, hmeta⟩ := (b1_listRel_nodeMetaRel_findNode? hrel t).2 x hfn
      rw [hy]
      dsimp only
      rw [hmeta.2.1]
      cases x.parentTag with
      | none => rfl
      | some p =>
        dsimp only
        rw [b1_listRel_nodeMetaRel_ancestorPathTags_aux fuel hrel p]

private theorem b1_listRel_nodeMetaRel_ancestorPathTags {xs ys : List TreeTagNode}
    (hrel : ListRel NodeMetaRel xs ys) (t : Nat) :
    ancestorPathTags ys t = ancestorPathTags xs t := by
  have hlen : ys.length = xs.length := by
    have h := ListRel.nodeMetaRel_map_tag_eq hrel
    have h1 := congrArg List.length h
    simp only [List.length_map] at h1
    exact h1
  unfold ancestorPathTags
  rw [hlen]
  exact b1_listRel_nodeMetaRel_ancestorPathTags_aux (xs.length + 1) hrel t

private theorem b1_listRel_nodeMetaRel_isStrictDescendantOf {xs ys : List TreeTagNode}
    (hrel : ListRel NodeMetaRel xs ys) (src : Nat) {x y : TreeTagNode} (hxy : NodeMetaRel x y) :
    isStrictDescendantOf ys src y = isStrictDescendantOf xs src x := by
  unfold isStrictDescendantOf
  rw [hxy.1, b1_listRel_nodeMetaRel_ancestorPathTags hrel x.tag]

/-- **Symbolic single-step whole-tree `TreeSimInv` simulation for
`TreeBorrowsMemory.release_protector` vs `execFrameExitMiniRust w [(protectedTag, protId)]`**:
over ANY `TreeSimInv`-related borrow tree (`0 < len`) with unique node tags, ANY
active protected node `pn` at `(protectedTag, protId)` covering `[off, off + len)`
with passive outside bytes (`OutsideNoProtectorAccess`):
1. if `execFrameExitMiniRust w [(protectedTag, protId)] = .ok w'`, then
   `TreeBorrowsMemory.release_protector tbm (⟨id⟩, emb protectedTag) = .ok tbm'`,
   preserving `alloc'.live = true`, `TreeBorrowsMemory.wfLive` (choice-free!),
   uniform permission-list length, `TreeSimInv off len emb w' alloc'.extra.root`,
   `ListRel NodeMetaRel w.nodes w'.nodes`, AND every other node's outside bytes
   (`OutsideNoProtectorAccess` for all remaining frame entries);
2. if `execFrameExitMiniRust w [(protectedTag, protId)] = .error e`, then
   `TreeBorrowsMemory.release_protector` fails with `.error (.ub msg)`;
3. conversely, whenever `TreeBorrowsMemory.release_protector` succeeds,
   `execFrameExitMiniRust` succeeds with a `TreeSimInv`-related post-state. -/
theorem tbm_release_protector_simulates_execFrameExitMiniRust_step
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (id : Nat) (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
    (off len : Nat) (hlen : 0 < len)
    (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld) (protectedTag protId : Nat) (pn : TreeTagNode)
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (hEqLen : ∀ q m, nodeAt alloc.extra.root q = some m → m.permissions.length = alloc.data.length)
    (hinv : TreeSimInv off len emb w alloc.extra.root)
    (htagsNodup : (w.nodes.map (·.tag)).Nodup)
    (hpn : findNode? w.nodes protectedTag = some pn)
    (hpnProt : pn.protector = some protId)
    (hactProt : w.activeProtectors.contains protId = true)
    (hpnRange : pn.rangeOffset = off ∧ pn.rangeLen = len)
    (hprotUnique : ∀ n ∈ w.nodes, n.tag ≠ protectedTag → n.protector ≠ some protId)
    (hembInj : ∀ n ∈ w.nodes, emb n.tag = emb protectedTag → n.tag = protectedTag)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes protectedTag).contains n.tag =
        locOf (some (emb protectedTag)) (emb n.tag))
    (hdesc : ∀ n ∈ w.nodes,
      isStrictDescendantOf w.nodes protectedTag n =
        ((emb protectedTag).isPrefixOf (emb n.tag) && decide (n.tag ≠ protectedTag)))
    (hpruneInert : ∀ n ∈ w.nodes, ∀ isWrite,
      protectorEndAccessIsWriteMiniRust? pn = some isWrite →
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes protectedTag) isWrite off len n = true →
      stepNodeOnRangeAccess w.activeProtectors isWrite false off len n = .ok n)
    (hOutside : ∀ m, nodeAt alloc.extra.root (emb protectedTag) = some m →
      OutsideNoProtectorAccess off len m) :
    (∀ w', execFrameExitMiniRust w [(protectedTag, protId)] = .ok w' →
      ∃ tbm' alloc',
        TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, emb protectedTag) = .ok tbm' ∧
        tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
        alloc'.data.length = alloc.data.length ∧
        (∀ q m, nodeAt alloc'.extra.root q = some m → m.permissions.length = alloc'.data.length) ∧
        (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm') ∧
        ListRel NodeMetaRel w.nodes w'.nodes ∧
        w'.activeProtectors = w.activeProtectors.filter (· != protId) ∧
        TreeSimInv off len emb w' alloc'.extra.root ∧
        (∀ q m, nodeAt alloc.extra.root q = some m → q ≠ emb protectedTag →
          ∃ m', nodeAt alloc'.extra.root q = some m' ∧
            (∀ b, b < off ∨ off + len ≤ b → m'.permissions[b]? = m.permissions[b]?))) ∧
    (∀ e, execFrameExitMiniRust w [(protectedTag, protId)] = .error e →
      ∃ msg, TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, emb protectedTag) = .error (.ub msg)) ∧
    (∀ tbm', TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, emb protectedTag) = .ok tbm' →
      ∃ w' alloc',
        execFrameExitMiniRust w [(protectedTag, protId)] = .ok w' ∧
        tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
        TreeSimInv off len emb w' alloc'.extra.root) := by
  have hpnMemTag := mem_of_findNode?_eq_some hpn
  have hpnMem : pn ∈ w.nodes := hpnMemTag.1
  have hpnTag : pn.tag = protectedTag := hpnMemTag.2
  have hpnIsProt : pn.isProtected w.activeProtectors = true := by
    unfold TreeTagNode.isProtected; rw [hpnProt]
    exact List.any_eq_true.mpr ⟨protId, List.contains_iff_mem.mp hactProt, beq_self_eq_true protId⟩
  obtain ⟨tNode, htNode, htProt, pPn, hpPn, hwinPn⟩ := hinv.nodes pn hpnMem
  rw [hpnTag] at htNode
  rw [hpnIsProt] at htProt hpPn
  have hnoIMPn : pn.perm ≠ .reservedIM := hinv.noProtIM pn hpnMem hpnIsProt
  have huniqPn : pn.perm = .unique → pn.accessed = true := hinv.protUniqAcc pn hpnMem hpnIsProt
  obtain ⟨pPn', hunpPn, hpPn'⟩ := b1_unprotect_permToMiniRust pn pPn hpPn hnoIMPn huniqPn
  have htOut := hOutside tNode htNode
  have hallUnp : ∀ p ∈ tNode.permissions, ∃ y, Permission.unprotect p = .ok y := by
    intro p hp
    obtain ⟨b, hbLt, hbEq⟩ := List.getElem_of_mem hp
    have hbGet : tNode.permissions[b]? = some p := by rw [List.getElem?_eq_getElem hbLt, hbEq]
    rcases Decidable.em (off ≤ b ∧ b < off + len) with ⟨hb1, hb2⟩ | hout
    · have h1 := hwinPn b hb1 hb2
      rw [hbGet] at h1; cases h1
      exact ⟨_, hunpPn⟩
    · have hout' : b < off ∨ off + len ≤ b := b1_not_in_window hout
      obtain ⟨p', hp'⟩ := htOut b p hbGet hout'
      exact ⟨(p', none), hp'⟩
  obtain ⟨pairs, hpairs, hpairsLen, hpairsGet⟩ :=
    b1_list_mapM_ok_of_forall Permission.unprotect tNode.permissions hallUnp
  let accesses := pairs.map Prod.snd
  let unprotPerms := pairs.map Prod.fst
  have haccLen : accesses.length = tNode.permissions.length := by
    dsimp only [accesses]; rw [List.length_map, hpairsLen]
  have hunpLen : unprotPerms.length = tNode.permissions.length := by
    dsimp only [unprotPerms]; rw [List.length_map, hpairsLen]
  have haccIn : ∀ b, off ≤ b → b < off + len →
      accesses[b]? = some ((protectorEndAccessIsWriteMiniRust? pn).map (fun isW => if isW then .Write else .Read)) ∧
      unprotPerms[b]? = some pPn' := by
    intro b hb1 hb2
    have hbGet := hwinPn b hb1 hb2
    have hbLt : b < tNode.permissions.length := (List.getElem?_eq_some_iff.mp hbGet).1
    obtain ⟨x, y, hx, hy, hfx⟩ := hpairsGet b hbLt
    rw [hbGet] at hx; cases hx
    rw [hunpPn] at hfx; cases hfx
    dsimp only [accesses, unprotPerms]
    rw [List.getElem?_map, List.getElem?_map, hy]
    exact ⟨rfl, rfl⟩
  have haccOut : ∀ b, b < off ∨ off + len ≤ b → b < accesses.length →
      accesses[b]? = some none := by
    intro b hout hblt
    rw [haccLen] at hblt
    obtain ⟨x, y, hx, hy, hfx⟩ := hpairsGet b hblt
    obtain ⟨p', hp'⟩ := htOut b x hx hout
    rw [hp'] at hfx; cases hfx
    dsimp only [accesses]
    rw [List.getElem?_map, hy]
    rfl
  obtain ⟨root1, _, hsuf1, hother1, hrelEq⟩ :=
    tbm_release_protector_eq tbm id (emb protectedTag) alloc tNode pairs halloc hlive htNode htProt hpairs
  have hroot1AtTarget : nodeAt root1 (emb protectedTag) = some { tNode with permissions := unprotPerms } := by
    have h1 := hsuf1 []
    rw [List.append_nil] at h1
    exact h1
  have hroot1Other : ∀ q, q ≠ emb protectedTag →
      (nodeAt alloc.extra.root q = none → nodeAt root1 q = none) ∧
      (∀ m, nodeAt alloc.extra.root q = some m →
        ∃ m1, nodeAt root1 q = some m1 ∧ m1.permissions = m.permissions ∧ m1.«protected» = m.«protected») := by
    intro q hqne
    cases hpre : (emb protectedTag).isPrefixOf q with
    | false =>
      have ho := hother1 q hpre
      exact ⟨ho.1, fun m hm => by obtain ⟨m1, hm1, hp1, hp2, _⟩ := ho.2 m hm; exact ⟨m1, hm1, hp1, hp2⟩⟩
    | true =>
      have hex : ∃ suf, q = emb protectedTag ++ suf ∧ suf ≠ [] := by
        have hprefApp : ∀ (p r : Gen.Path), p.isPrefixOf r = true → ∃ suf, r = p ++ suf := by
          intro p
          induction p with
          | nil => intro r _; exact ⟨r, rfl⟩
          | cons a ps ih =>
            intro r hr
            cases r with
            | nil => cases hr
            | cons b rs =>
              simp only [List.isPrefixOf, Bool.and_eq_true, a1_int_beq_iff] at hr
              obtain ⟨rfl, hrest⟩ := hr
              obtain ⟨suf, rfl⟩ := ih rs hrest
              exact ⟨suf, rfl⟩
        obtain ⟨suf, rfl⟩ := hprefApp (emb protectedTag) q hpre
        refine ⟨suf, rfl, fun hs => hqne (by rw [hs, List.append_nil])⟩
      obtain ⟨suf, rfl, hsufNe⟩ := hex
      have hna0 : ∀ p s (r : Gen.Node), nodeAt r (p ++ s) = (nodeAt r p).bind (fun m => nodeAt m s) := by
        intro p
        induction p with
        | nil => intro _ _; rfl
        | cons a ps ih =>
          intro s ⟨cs, ps', pr⟩
          rcases Decidable.em (0 ≤ a) with ha | ha
          · cases hc : cs[a.toNat]? with
            | none =>
              rw [List.cons_append, nwsr_nodeAt_cons_none cs ps' pr a (ps ++ s) ha hc,
                nwsr_nodeAt_cons_none cs ps' pr a ps ha hc]; rfl
            | some c =>
              rw [List.cons_append, nwsr_nodeAt_cons_some cs ps' pr a (ps ++ s) c ha hc,
                nwsr_nodeAt_cons_some cs ps' pr a ps c ha hc]
              exact ih s c
          · rw [List.cons_append, nwsr_nodeAt_cons_neg cs ps' pr a (ps ++ s) ha,
              nwsr_nodeAt_cons_neg cs ps' pr a ps ha]; rfl
      have hsame : nodeAt root1 (emb protectedTag ++ suf) = nodeAt alloc.extra.root (emb protectedTag ++ suf) := by
        rw [hsuf1 suf, hna0, htNode]
        cases suf with
        | nil => exact absurd rfl hsufNe
        | cons j s =>
          cases tNode with | mk cs ps pr => rfl
      rw [hsame]
      exact ⟨fun h => h, fun m hm => ⟨m, hm, rfl, rfl⟩⟩
  have hroot1EqLen : ∀ q m1, nodeAt root1 q = some m1 → m1.permissions.length = alloc.data.length := by
    intro q m1 hm1
    rcases Decidable.em (q = emb protectedTag) with rfl | hqne
    · rw [hroot1AtTarget] at hm1; cases hm1
      exact hunpLen.trans (hEqLen (emb protectedTag) tNode htNode)
    · cases hm0 : nodeAt alloc.extra.root q with
      | none => rw [(hroot1Other q hqne).1 hm0] at hm1; cases hm1
      | some m0 =>
        obtain ⟨m1', hm1', hps, _⟩ := (hroot1Other q hqne).2 m0 hm0
        rw [hm1'] at hm1; cases hm1
        rw [hps]; exact hEqLen q m0 hm0
  have hmr : ∀ q m, nodeAt alloc.extra.root q = some m → ∃ n ∈ w.nodes, emb n.tag = q ∧
      NodeWindowRel w.activeProtectors off len n m := by
    intro q m hq
    obtain ⟨n, hn, hemb⟩ := hinv.surj q m hq
    obtain ⟨m', hm', hrel⟩ := hinv.nodes n hn
    rw [hemb, hq] at hm'; cases hm'
    exact ⟨n, hn, hemb, hrel⟩
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  have hlenBound : off + len ≤ tNode.permissions.length := by
    have hlast := hwinPn (off + len - 1) (by omega) (by omega)
    have hlt := (List.getElem?_eq_some_iff.mp hlast).1
    omega
  have hpostEqLen : ∀ root2,
      (∀ q, (nodeAt root1 q = none → nodeAt root2 q = none) ∧
        (∀ m1, nodeAt root1 q = some m1 → ∃ m2, nodeAt root2 q = some m2 ∧ ReleasePost (some (emb protectedTag)) accesses q m1 m2)) →
      ∀ q m2, nodeAt root2 q = some m2 → m2.permissions.length = alloc.data.length := by
    intro root2 hpost2 q m2 hm2
    cases hm1 : nodeAt root1 q with
    | none => rw [(hpost2 q).1 hm1] at hm2; cases hm2
    | some m1 =>
      obtain ⟨m2', hm2', hrel⟩ := (hpost2 q).2 m1 hm1
      rw [hm2'] at hm2; cases hm2
      have hl1 := hroot1EqLen q m1 hm1
      unfold ReleasePost at hrel
      rcases Decidable.em (emb protectedTag = q) with rfl | hne
      · simp only [↓reduceIte] at hrel; rw [hrel.2]; exact hl1
      · simp only [hne, ↓reduceIte] at hrel
        cases hpre : (emb protectedTag).isPrefixOf q with
        | true => simp only [hpre, ↓reduceIte] at hrel; rw [hrel]; exact hl1
        | false => simp only [hpre, Bool.false_eq_true, ↓reduceIte] at hrel; exact hrel.2.1.trans hl1
  have hpostOutside : ∀ root2,
      (∀ q, (nodeAt root1 q = none → nodeAt root2 q = none) ∧
        (∀ m1, nodeAt root1 q = some m1 → ∃ m2, nodeAt root2 q = some m2 ∧ ReleasePost (some (emb protectedTag)) accesses q m1 m2)) →
      ∀ q m, nodeAt alloc.extra.root q = some m → q ≠ emb protectedTag →
        ∃ m2, nodeAt root2 q = some m2 ∧
          ∀ b, b < off ∨ off + len ≤ b → m2.permissions[b]? = m.permissions[b]? := by
    intro root2 hpost2 q m hm hqne
    obtain ⟨m1, hm1, hm1Ps, _⟩ := (hroot1Other q hqne).2 m hm
    obtain ⟨m2, hm2, hrel⟩ := (hpost2 q).2 m1 hm1
    refine ⟨m2, hm2, fun b hb => ?_⟩
    unfold ReleasePost at hrel
    have hne' : emb protectedTag ≠ q := hqne.symm
    simp only [hne', ↓reduceIte] at hrel
    cases hpre : (emb protectedTag).isPrefixOf q with
    | true =>
      simp only [hpre, ↓reduceIte] at hrel
      rw [hrel, hm1Ps]
    | false =>
      simp only [hpre, Bool.false_eq_true, ↓reduceIte] at hrel
      rcases Decidable.em (b < accesses.length) with hblt | hbge
      · have hstep := hrel.2.2.2 b hblt
        rw [haccOut b hb hblt] at hstep
        rw [hstep, hm1Ps]
      · rw [hrel.2.2.1 b (by omega), hm1Ps]
  -- Split on `protectorEndAccessIsWriteMiniRust? pn`.
  cases hkind : protectorEndAccessIsWriteMiniRust? pn with
  | none =>
    have hallNone : ∀ i < accesses.length, accesses[i]? = some none := by
      intro i hi
      rcases Decidable.em (off ≤ i ∧ i < off + len) with ⟨hi1, hi2⟩ | hout
      · have h1 := (haccIn i hi1 hi2).1
        rw [hkind] at h1; exact h1
      · exact haccOut i (b1_not_in_window hout) hi
    have hpoint : ∀ q m1, nodeAt root1 q = some m1 →
        (emb protectedTag).isPrefixOf q = false →
        ∀ i < accesses.length, ∀ k, accesses[i]? = some (some k) →
          ∃ p p', m1.permissions[i]? = some p ∧
            Permission.transition p k (locRel (some (emb protectedTag)) q) = .ok p' := by
      intro _ _ _ _ i hi k hk
      rw [hallNone i hi] at hk; cases hk
    obtain ⟨root2, hrel2, hpost2⟩ :=
      node_release_protector_ok_of_pointwise root1 (some (emb protectedTag)) accesses hpoint
    have htbmOk : TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, emb protectedTag) =
        .ok { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id { alloc with extra := { root := root2 } }) } } := by
      rw [hrelEq, hrel2]; rfl
    have hworldOk : execFrameExitMiniRust w [(protectedTag, protId)] = .ok (releaseProtector w protId) := by
      simp [execFrameExitMiniRust, execFrameExitSequential, execProtectorEndAccessFor, hpn, hkind]
    have hinv2 : TreeSimInv off len emb (releaseProtector w protId) root2 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro n hn
        obtain ⟨m0, hm0, hprot0, p, hp, hwin0⟩ := hinv.nodes n hn
        rcases Decidable.em (n.tag = protectedTag) with htagEq | htagNe
        · have hneq : n = pn := b1_eq_of_mem_of_findNode?_of_nodup w.nodes protectedTag n pn htagsNodup hn htagEq hpn
          subst n
          obtain ⟨m2, hm2, hrel⟩ := (hpost2 (emb protectedTag)).2 _ hroot1AtTarget
          unfold ReleasePost at hrel
          simp only [↓reduceIte] at hrel
          have hisP : pn.isProtected (w.activeProtectors.filter (· != protId)) = false :=
            b1_isProtected_releaseProtector_self pn protId w.activeProtectors hpnProt
          refine ⟨m2, by rw [hpnTag]; exact hm2, ?_, pPn', ?_, ?_⟩
          · change Protected.yes m2.«protected» = pn.isProtected (w.activeProtectors.filter (· != protId))
            rw [hrel.1, hisP]; rfl
          · change permToMiniRust (pn.isProtected (w.activeProtectors.filter (· != protId))) pn.accessed pn.perm = some pPn'
            rw [hisP]; exact hpPn'
          · intro b hb1 hb2
            rw [hrel.2]
            exact (haccIn b hb1 hb2).2
        · have hqne : emb n.tag ≠ emb protectedTag := fun h => htagNe (hembInj n hn h)
          obtain ⟨m1, hm1, hm1Ps, hm1Prot⟩ := (hroot1Other (emb n.tag) hqne).2 m0 hm0
          obtain ⟨m2, hm2, hrel⟩ := (hpost2 (emb n.tag)).2 m1 hm1
          have hisP : n.isProtected (w.activeProtectors.filter (· != protId)) = n.isProtected w.activeProtectors :=
            b1_isProtected_releaseProtector_other n protId w.activeProtectors (hprotUnique n hn htagNe)
          unfold ReleasePost at hrel
          have hne' : emb protectedTag ≠ emb n.tag := hqne.symm
          simp only [hne', ↓reduceIte] at hrel
          refine ⟨m2, hm2, ?_, p, ?_, ?_⟩
          · change Protected.yes m2.«protected» = n.isProtected (w.activeProtectors.filter (· != protId))
            rw [hisP]
            cases hpre : (emb protectedTag).isPrefixOf (emb n.tag) with
            | true => simp only [hpre, ↓reduceIte] at hrel; rw [hrel, hm1Prot]; exact hprot0
            | false => simp only [hpre, Bool.false_eq_true, ↓reduceIte] at hrel; rw [hrel.1, hm1Prot]; exact hprot0
          · change permToMiniRust (n.isProtected (w.activeProtectors.filter (· != protId))) n.accessed n.perm = some p
            rw [hisP]; exact hp
          · intro b hb1 hb2
            cases hpre : (emb protectedTag).isPrefixOf (emb n.tag) with
            | true => simp only [hpre, ↓reduceIte] at hrel; rw [hrel, hm1Ps]; exact hwin0 b hb1 hb2
            | false =>
              simp only [hpre, Bool.false_eq_true, ↓reduceIte] at hrel
              have hstep := hrel.2.2.2 b (by rw [haccLen]; omega)
              rw [hallNone b (by rw [haccLen]; omega)] at hstep
              rw [hstep, hm1Ps]; exact hwin0 b hb1 hb2
      · intro q m2 hm2
        cases hm1 : nodeAt root1 q with
        | none => rw [(hpost2 q).1 hm1] at hm2; cases hm2
        | some m1 =>
          rcases Decidable.em (q = emb protectedTag) with rfl | hqne
          · exact ⟨pn, hpnMem, by rw [hpnTag]⟩
          · cases hm0 : nodeAt alloc.extra.root q with
            | none => rw [(hroot1Other q hqne).1 hm0] at hm1; cases hm1
            | some m0 => exact hinv.surj q m0 hm0
      · intro n hn; exact hinv.overlap n hn
      · intro n hn hp'
        rcases Decidable.em (n.tag = protectedTag) with htagEq | htagNe
        · have hneq := b1_eq_of_mem_of_findNode?_of_nodup w.nodes protectedTag n pn htagsNodup hn htagEq hpn
          subst n
          have hisP := b1_isProtected_releaseProtector_self pn protId w.activeProtectors hpnProt
          change pn.isProtected (w.activeProtectors.filter (· != protId)) = true at hp'
          rw [hisP] at hp'; cases hp'
        · have hisP := b1_isProtected_releaseProtector_other n protId w.activeProtectors (hprotUnique n hn htagNe)
          change n.isProtected (w.activeProtectors.filter (· != protId)) = true at hp'
          rw [hisP] at hp'
          exact hinv.noProtIM n hn hp'
      · intro n hn hp' hu
        rcases Decidable.em (n.tag = protectedTag) with htagEq | htagNe
        · have hneq := b1_eq_of_mem_of_findNode?_of_nodup w.nodes protectedTag n pn htagsNodup hn htagEq hpn
          subst n
          have hisP := b1_isProtected_releaseProtector_self pn protId w.activeProtectors hpnProt
          change pn.isProtected (w.activeProtectors.filter (· != protId)) = true at hp'
          rw [hisP] at hp'; cases hp'
        · have hisP := b1_isProtected_releaseProtector_other n protId w.activeProtectors (hprotUnique n hn htagNe)
          change n.isProtected (w.activeProtectors.filter (· != protId)) = true at hp'
          rw [hisP] at hp'
          exact hinv.protUniqAcc n hn hp' hu
    have hmetaRefl : ∀ xs : List TreeTagNode, ListRel NodeMetaRel xs xs := by
      intro xs; induction xs with | nil => exact ListRel.nil | cons x tl ih => exact ListRel.cons (NodeMetaRel.refl x) ih
    refine ⟨?_, ?_, ?_⟩
    · intro w' hw'
      rw [hworldOk] at hw'; cases hw'
      exact ⟨_, _, htbmOk, List.getElem?_set_self hidlt, hlive, rfl,
        hpostEqLen root2 hpost2, fun hwf => tbm_release_protector_wfLive_choiceFree hwf htbmOk,
        hmetaRefl w.nodes, rfl, hinv2, hpostOutside root2 hpost2⟩
    · intro e he
      rw [hworldOk] at he; cases he
    · intro tbm' htbm'
      rw [htbmOk] at htbm'; cases htbm'
      exact ⟨releaseProtector w protId, _, hworldOk, List.getElem?_set_self hidlt, hlive, hinv2⟩
  | some isWrite =>
    let k : Gen.AccessKind := if isWrite then .Write else .Read
    have hneLen : len ≠ 0 := by omega
    have hstepSim : ∀ n ∈ w.nodes, A1NodeStepSim w.activeProtectors k
        (fun isLoc m => stepNodeOnRangeAccess w.activeProtectors isWrite isLoc off len m) n := by
      intro n hn
      cases isWrite with
      | false => exact a1_stepRead_sim w.activeProtectors off len n (hinv.overlap n hn) (hinv.noProtIM n hn) (hinv.protUniqAcc n hn)
      | true => exact a1_stepWrite_sim w.activeProtectors off len n (hinv.overlap n hn) (hinv.noProtIM n hn) (hinv.protUniqAcc n hn)
    have hworldEq : execFrameExitMiniRust w [(protectedTag, protId)] =
        (match execProtectorEndAccess w protectedTag isWrite off len with
        | .error e => .error e
        | .ok w1 => .ok (releaseProtector w1 protId)) := by
      unfold execFrameExitMiniRust execFrameExitSequential execProtectorEndAccessFor
      simp only [hpn, hkind, hpnRange.1, hpnRange.2]
      cases execProtectorEndAccess w protectedTag isWrite off len <;> rfl
    have haccChar : ∀ i < accesses.length,
        accesses[i]? = some (if off ≤ i ∧ i < off + len then some k else none) := by
      intro i hi
      rcases Decidable.em (off ≤ i ∧ i < off + len) with ⟨hi1, hi2⟩ | hout
      · simp only [hi1, hi2, and_self, ↓reduceIte]
        have h1 := (haccIn i hi1 hi2).1
        rw [hkind] at h1; exact h1
      · simp only [hout, ↓reduceIte]
        exact haccOut i (b1_not_in_window hout) hi
    -- Helper relating `ProtectorEndStepRel` on non-descendant nodes to `stepNodeOnRangeAccess`.
    have hrelToStep : ∀ n ∈ w.nodes, ∀ n',
        ProtectorEndStepRel w protectedTag isWrite off len n n' →
        (emb protectedTag).isPrefixOf (emb n.tag) = false →
        stepNodeOnRangeAccess w.activeProtectors isWrite (locOf (some (emb protectedTag)) (emb n.tag)) off len n = .ok n' := by
      intro n hn n' hrel hnotDesc
      have hdescF : isStrictDescendantOf w.nodes protectedTag n = false := by
        rw [hdesc n hn, hnotDesc]; rfl
      rcases hrel with ⟨ha, hs⟩ | ⟨ha, hsk, hEq⟩ | ⟨ha, _, _, hs⟩
      · rw [← hloc n hn, ha]; exact hs
      · subst n'
        rcases hsk with hd | hp
        · rw [hdescF] at hd; cases hd
        · rw [← hloc n hn, ha]
          exact hpruneInert n hn isWrite hkind hp
      · rw [← hloc n hn, ha]; exact hs
    have hstepToRel : ∀ n ∈ w.nodes,
        (∀ n', (emb protectedTag).isPrefixOf (emb n.tag) = false →
          stepNodeOnRangeAccess w.activeProtectors isWrite (locOf (some (emb protectedTag)) (emb n.tag)) off len n = .ok n' →
          ProtectorEndStepRel w protectedTag isWrite off len n n') := by
      intro n hn n' hnotDesc hs
      have hdescF : isStrictDescendantOf w.nodes protectedTag n = false := by
        rw [hdesc n hn, hnotDesc]; rfl
      cases hl : locOf (some (emb protectedTag)) (emb n.tag) with
      | true =>
        rw [hl] at hs
        exact Or.inl ⟨by rw [hloc n hn, hl], hs⟩
      | false =>
        rw [hl] at hs
        cases hp : isPrunedForeignNode w.nodes (ancestorPathTags w.nodes protectedTag) isWrite off len n with
        | true =>
          have hsame := hpruneInert n hn isWrite hkind hp
          rw [hsame] at hs; cases hs
          exact Or.inr (Or.inl ⟨by rw [hloc n hn, hl], Or.inr hp, rfl⟩)
        | false =>
          exact Or.inr (Or.inr ⟨by rw [hloc n hn, hl], hdescF, hp, hs⟩)
    -- Forward proof when `ListRel ProtectorEndStepRel w.nodes nodes'`.
    have hfwd : ∀ nodes', ListRel (ProtectorEndStepRel w protectedTag isWrite off len) w.nodes nodes' →
        ∃ tbm' alloc',
          TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, emb protectedTag) = .ok tbm' ∧
          tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
          alloc'.data.length = alloc.data.length ∧
          (∀ q m, nodeAt alloc'.extra.root q = some m → m.permissions.length = alloc'.data.length) ∧
          (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm') ∧
          ListRel NodeMetaRel w.nodes nodes' ∧
          TreeSimInv off len emb (releaseProtector { w with nodes := nodes' } protId) alloc'.extra.root ∧
          (∀ q m, nodeAt alloc.extra.root q = some m → q ≠ emb protectedTag →
            ∃ m', nodeAt alloc'.extra.root q = some m' ∧
              (∀ b, b < off ∨ off + len ≤ b → m'.permissions[b]? = m.permissions[b]?)) := by
      intro nodes' hrel
      have hpoint : ∀ q m1, nodeAt root1 q = some m1 →
          (emb protectedTag).isPrefixOf q = false →
          ∀ i < accesses.length, ∀ k', accesses[i]? = some (some k') →
            ∃ p p', m1.permissions[i]? = some p ∧
              Permission.transition p k' (locRel (some (emb protectedTag)) q) = .ok p' := by
        intro q m1 hm1 hnotPre i hi k' hk'
        have hqne : q ≠ emb protectedTag := by
          intro h; rw [h, b1_isPrefixOf_refl] at hnotPre; cases hnotPre
        have hci := haccChar i hi
        rw [hk'] at hci
        rcases Decidable.em (off ≤ i ∧ i < off + len) with ⟨hi1, hi2⟩ | hout
        · simp only [hi1, hi2, and_self, ↓reduceIte] at hci
          cases hci
          cases hm0 : nodeAt alloc.extra.root q with
          | none => rw [(hroot1Other q hqne).1 hm0] at hm1; cases hm1
          | some m0 =>
            obtain ⟨m1', hm1', hm1Ps, _⟩ := (hroot1Other q hqne).2 m0 hm0
            rw [hm1'] at hm1; cases hm1
            obtain ⟨n, hn, hemb, _, p, hp, hwin0⟩ := hmr q m0 hm0
            obtain ⟨n', _, hnn'⟩ := hrel.exists_of_mem_left hn
            have hs := hrelToStep n hn n' hnn' (by rw [hemb]; exact hnotPre)
            obtain ⟨p0, hp0, hok, _⟩ := hstepSim n hn (locOf (some (emb protectedTag)) (emb n.tag))
            rw [hp] at hp0; cases hp0
            obtain ⟨_, _, _, _, _, _, _, p', htr, _⟩ := hok n' hs
            have hlocEq : locRel (some (emb protectedTag)) q =
                nodeRelToMiniRust (locOf (some (emb protectedTag)) (emb n.tag)) := by
              unfold locRel nodeRelToMiniRust; rw [hemb]
            rw [hm1Ps, hlocEq]
            exact ⟨p, p', hwin0 i hi1 hi2, htr⟩
        · simp only [hout, ↓reduceIte] at hci; cases hci
      obtain ⟨root2, hrel2, hpost2⟩ :=
        node_release_protector_ok_of_pointwise root1 (some (emb protectedTag)) accesses hpoint
      have htbmOk : TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, emb protectedTag) =
          .ok { tbm with mem := { tbm.mem with allocations := (tbm.mem.allocations.set id { alloc with extra := { root := root2 } }) } } := by
        rw [hrelEq, hrel2]; rfl
      have hmeta : ListRel NodeMetaRel w.nodes nodes' :=
        ListRel.imp (fun _ _ h => ProtectorEndStepRel.nodeMetaRel h) hrel
      have hinv2 : TreeSimInv off len emb (releaseProtector { w with nodes := nodes' } protId) root2 := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro n' hn'
          obtain ⟨n, hn, hnn'⟩ := hrel.exists_of_mem_right hn'
          have hnm := ProtectorEndStepRel.nodeMetaRel hnn'
          obtain ⟨m0, hm0, hprot0, p, hp, hwin0⟩ := hinv.nodes n hn
          rcases Decidable.em (n.tag = protectedTag) with htagEq | htagNe
          · have hneq := b1_eq_of_mem_of_findNode?_of_nodup w.nodes protectedTag n pn htagsNodup hn htagEq hpn
            subst n
            -- On `pn`, `ProtectorEndStepRel` gives `n' = pn` (self-step invariant)!
            have hn'Eq : n' = pn := by
              rcases hnn' with ⟨_, hs⟩ | ⟨_, _, hEq⟩ | ⟨ha, _, _, _⟩
              · rw [b1_protectorEnd_self_invariant_miniRust w.activeProtectors off len pn isWrite hkind huniqPn] at hs
                cases hs; rfl
              · exact hEq
              · have hself : (ancestorPathTags w.nodes protectedTag).contains pn.tag = true := by
                  rw [hloc pn hpnMem, hpnTag, locOf_some_eq_isPrefixOf, b1_isPrefixOf_refl]
                rw [hself] at ha; cases ha
            subst n'
            obtain ⟨m2, hm2, hr2⟩ := (hpost2 (emb protectedTag)).2 _ hroot1AtTarget
            unfold ReleasePost at hr2; simp only [↓reduceIte] at hr2
            have hisP := b1_isProtected_releaseProtector_self pn protId w.activeProtectors hpnProt
            refine ⟨m2, by rw [hpnTag]; exact hm2, ?_, pPn', ?_, ?_⟩
            · change Protected.yes m2.«protected» = pn.isProtected (w.activeProtectors.filter (· != protId))
              rw [hr2.1, hisP]; rfl
            · change permToMiniRust (pn.isProtected (w.activeProtectors.filter (· != protId))) pn.accessed pn.perm = some pPn'
              rw [hisP]; exact hpPn'
            · intro b hb1 hb2; rw [hr2.2]; exact (haccIn b hb1 hb2).2
          · have hqne : emb n.tag ≠ emb protectedTag := fun h => htagNe (hembInj n hn h)
            have hisP : n'.isProtected (w.activeProtectors.filter (· != protId)) = n.isProtected w.activeProtectors := by
              have hprotNe : n'.protector ≠ some protId := by
                rw [hnm.2.2.1]; exact hprotUnique n hn htagNe
              rw [b1_isProtected_releaseProtector_other n' protId w.activeProtectors hprotNe]
              unfold TreeTagNode.isProtected; rw [hnm.2.2.1]
            obtain ⟨m1, hm1, hm1Ps, hm1Prot⟩ := (hroot1Other (emb n.tag) hqne).2 m0 hm0
            obtain ⟨m2, hm2, hr2⟩ := (hpost2 (emb n.tag)).2 m1 hm1
            unfold ReleasePost at hr2
            have hne' : emb protectedTag ≠ emb n.tag := hqne.symm
            simp only [hne', ↓reduceIte] at hr2
            cases hpre : (emb protectedTag).isPrefixOf (emb n.tag) with
            | true =>
              simp only [hpre, ↓reduceIte] at hr2
              have hdescT : isStrictDescendantOf w.nodes protectedTag n = true := by
                rw [hdesc n hn, hpre]; simp [htagNe]
              have hancF : (ancestorPathTags w.nodes protectedTag).contains n.tag = false := by
                rw [hloc n hn, locOf_some_eq_isPrefixOf]
                cases hrev : (emb n.tag).isPrefixOf (emb protectedTag) with
                | false => rfl
                | true =>
                  exfalso
                  exact hqne (b1_nodeAt_prefix_eq hrev hpre)
              have hn'Eq : n' = n := by
                rcases hnn' with ⟨ha, _⟩ | ⟨_, _, hEq⟩ | ⟨_, hd, _, _⟩
                · rw [hancF] at ha; cases ha
                · exact hEq
                · rw [hdescT] at hd; cases hd
              subst n'
              refine ⟨m2, hm2, ?_, p, ?_, ?_⟩
              · change Protected.yes m2.«protected» = n.isProtected (w.activeProtectors.filter (· != protId))
                rw [hr2, hm1Prot, hisP]; exact hprot0
              · change permToMiniRust (n.isProtected (w.activeProtectors.filter (· != protId))) n.accessed n.perm = some p
                rw [hisP]; exact hp
              · intro b hb1 hb2; rw [hr2, hm1Ps]; exact hwin0 b hb1 hb2
            | false =>
              simp only [hpre, Bool.false_eq_true, ↓reduceIte] at hr2
              have hs := hrelToStep n hn n' hnn' hpre
              obtain ⟨p0, hp0, hok, _⟩ := hstepSim n hn (locOf (some (emb protectedTag)) (emb n.tag))
              rw [hp] at hp0; cases hp0
              obtain ⟨htagEq', _, _, _, _, _, _, p', htr, hp'⟩ := hok n' hs
              refine ⟨m2, by rw [htagEq']; exact hm2, ?_, p', ?_, ?_⟩
              · change Protected.yes m2.«protected» = n'.isProtected (w.activeProtectors.filter (· != protId))
                rw [hr2.1, hm1Prot, hisP]; exact hprot0
              · change permToMiniRust (n'.isProtected (w.activeProtectors.filter (· != protId))) n'.accessed n'.perm = some p'
                rw [hisP]; exact hp'
              · intro b hb1 hb2
                have hblt : b < accesses.length := by rw [haccLen]; omega
                have hstepB := hr2.2.2.2 b hblt
                have hci := haccChar b hblt
                simp only [hb1, hb2, and_self, ↓reduceIte] at hci
                rw [hci] at hstepB
                obtain ⟨p'', htr'', hm2Get⟩ := hstepB p (by rw [hm1Ps]; exact hwin0 b hb1 hb2)
                have hlocEq : locRel (some (emb protectedTag)) (emb n.tag) =
                    nodeRelToMiniRust (locOf (some (emb protectedTag)) (emb n.tag)) := rfl
                rw [hlocEq, htr] at htr''
                cases htr''
                exact hm2Get
        · intro q m2 hm2
          cases hm1 : nodeAt root1 q with
          | none => rw [(hpost2 q).1 hm1] at hm2; cases hm2
          | some m1 =>
            rcases Decidable.em (q = emb protectedTag) with rfl | hqne
            · obtain ⟨pn', hpn'Mem, hnn'⟩ := hrel.exists_of_mem_left hpnMem
              have hnm := ProtectorEndStepRel.nodeMetaRel hnn'
              exact ⟨pn', hpn'Mem, by rw [hnm.1, hpnTag]⟩
            · cases hm0 : nodeAt alloc.extra.root q with
              | none => rw [(hroot1Other q hqne).1 hm0] at hm1; cases hm1
              | some m0 =>
                obtain ⟨n, hn, hemb⟩ := hinv.surj q m0 hm0
                obtain ⟨n', hn', hnn'⟩ := hrel.exists_of_mem_left hn
                have hnm := ProtectorEndStepRel.nodeMetaRel hnn'
                exact ⟨n', hn', by rw [hnm.1, hemb]⟩
        · intro n' hn'
          obtain ⟨n, hn, hnn'⟩ := hrel.exists_of_mem_right hn'
          have hnm := ProtectorEndStepRel.nodeMetaRel hnn'
          rw [hnm.2.2.2.1, hnm.2.2.2.2.1]
          exact hinv.overlap n hn
        · intro n' hn' hp'
          obtain ⟨n, hn, hnn'⟩ := hrel.exists_of_mem_right hn'
          have hnm := ProtectorEndStepRel.nodeMetaRel hnn'
          rcases Decidable.em (n.tag = protectedTag) with htagEq | htagNe
          · have hneq := b1_eq_of_mem_of_findNode?_of_nodup w.nodes protectedTag n pn htagsNodup hn htagEq hpn
            subst n
            have hpEq : n'.protector = some protId := hnm.2.2.1.trans hpnProt
            have hisP := b1_isProtected_releaseProtector_self n' protId w.activeProtectors hpEq
            change n'.isProtected (w.activeProtectors.filter (· != protId)) = true at hp'
            rw [hisP] at hp'; cases hp'
          · have hprotNe : n'.protector ≠ some protId := by rw [hnm.2.2.1]; exact hprotUnique n hn htagNe
            have hisP : n'.isProtected (w.activeProtectors.filter (· != protId)) = n'.isProtected w.activeProtectors :=
              b1_isProtected_releaseProtector_other n' protId w.activeProtectors hprotNe
            change n'.isProtected (w.activeProtectors.filter (· != protId)) = true at hp'
            rw [hisP] at hp'
            have hisP0 : n.isProtected w.activeProtectors = true := by
              unfold TreeTagNode.isProtected at hp' ⊢; rw [← hnm.2.2.1]; exact hp'
            cases hpre : (emb protectedTag).isPrefixOf (emb n.tag) with
            | true =>
              have hdescT : isStrictDescendantOf w.nodes protectedTag n = true := by
                rw [hdesc n hn, hpre]; simp [htagNe]
              have hancF : (ancestorPathTags w.nodes protectedTag).contains n.tag = false := by
                rw [hloc n hn, locOf_some_eq_isPrefixOf]
                cases hrev : (emb n.tag).isPrefixOf (emb protectedTag) with
                | false => rfl
                | true =>
                  exfalso
                  exact htagNe (hembInj n hn (b1_nodeAt_prefix_eq hrev hpre))
              rcases hnn' with ⟨ha, _⟩ | ⟨_, _, hEq⟩ | ⟨_, hd, _, _⟩
              · rw [hancF] at ha; cases ha
              · subst n'; exact hinv.noProtIM n hn hisP0
              · rw [hdescT] at hd; cases hd
            | false =>
              have hs := hrelToStep n hn n' hnn' hpre
              obtain ⟨_, _, hok, _⟩ := hstepSim n hn (locOf (some (emb protectedTag)) (emb n.tag))
              obtain ⟨_, _, _, _, _, hIM, _⟩ := hok n' hs
              exact hIM hp'
        · intro n' hn' hp' hu
          obtain ⟨n, hn, hnn'⟩ := hrel.exists_of_mem_right hn'
          have hnm := ProtectorEndStepRel.nodeMetaRel hnn'
          rcases Decidable.em (n.tag = protectedTag) with htagEq | htagNe
          · have hneq := b1_eq_of_mem_of_findNode?_of_nodup w.nodes protectedTag n pn htagsNodup hn htagEq hpn
            subst n
            have hpEq : n'.protector = some protId := hnm.2.2.1.trans hpnProt
            have hisP := b1_isProtected_releaseProtector_self n' protId w.activeProtectors hpEq
            change n'.isProtected (w.activeProtectors.filter (· != protId)) = true at hp'
            rw [hisP] at hp'; cases hp'
          · have hprotNe : n'.protector ≠ some protId := by rw [hnm.2.2.1]; exact hprotUnique n hn htagNe
            have hisP : n'.isProtected (w.activeProtectors.filter (· != protId)) = n'.isProtected w.activeProtectors :=
              b1_isProtected_releaseProtector_other n' protId w.activeProtectors hprotNe
            change n'.isProtected (w.activeProtectors.filter (· != protId)) = true at hp'
            rw [hisP] at hp'
            have hisP0 : n.isProtected w.activeProtectors = true := by
              unfold TreeTagNode.isProtected at hp' ⊢; rw [← hnm.2.2.1]; exact hp'
            cases hpre : (emb protectedTag).isPrefixOf (emb n.tag) with
            | true =>
              have hdescT : isStrictDescendantOf w.nodes protectedTag n = true := by
                rw [hdesc n hn, hpre]; simp [htagNe]
              have hancF : (ancestorPathTags w.nodes protectedTag).contains n.tag = false := by
                rw [hloc n hn, locOf_some_eq_isPrefixOf]
                cases hrev : (emb n.tag).isPrefixOf (emb protectedTag) with
                | false => rfl
                | true =>
                  exfalso
                  exact htagNe (hembInj n hn (b1_nodeAt_prefix_eq hrev hpre))
              rcases hnn' with ⟨ha, _⟩ | ⟨_, _, hEq⟩ | ⟨_, hd, _, _⟩
              · rw [hancF] at ha; cases ha
              · subst n'; exact hinv.protUniqAcc n hn hisP0 hu
              · rw [hdescT] at hd; cases hd
            | false =>
              have hs := hrelToStep n hn n' hnn' hpre
              obtain ⟨_, _, hok, _⟩ := hstepSim n hn (locOf (some (emb protectedTag)) (emb n.tag))
              obtain ⟨_, _, _, _, _, _, hUA, _⟩ := hok n' hs
              exact hUA hp' hu
      exact ⟨_, _, htbmOk, List.getElem?_set_self hidlt, hlive, rfl,
        hpostEqLen root2 hpost2, fun hwf => tbm_release_protector_wfLive_choiceFree hwf htbmOk,
        hmeta, hinv2, hpostOutside root2 hpost2⟩
    -- Backward / error direction.
    have hbwd : (∀ nodes', ¬ ListRel (ProtectorEndStepRel w protectedTag isWrite off len) w.nodes nodes') →
        ∃ msg, TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, emb protectedTag) = .error (.ub msg) := by
      intro hno
      rw [hrelEq]
      cases hrun : Node.release_protector root1 (some (emb protectedTag)) accesses with
      | ok root2 =>
        exfalso
        have hall : ∀ n ∈ w.nodes, ∃ n', ProtectorEndStepRel w protectedTag isWrite off len n n' := by
          intro n hn
          rcases Decidable.em (n.tag = protectedTag) with htagEq | htagNe
          · have hneq := b1_eq_of_mem_of_findNode?_of_nodup w.nodes protectedTag n pn htagsNodup hn htagEq hpn
            subst n
            have hself : (ancestorPathTags w.nodes protectedTag).contains pn.tag = true := by
              rw [hloc pn hpnMem, hpnTag, locOf_some_eq_isPrefixOf, b1_isPrefixOf_refl]
            exact ⟨pn, Or.inl ⟨hself,
              b1_protectorEnd_self_invariant_miniRust w.activeProtectors off len pn isWrite hkind huniqPn⟩⟩
          · cases hpre : (emb protectedTag).isPrefixOf (emb n.tag) with
            | true =>
              have hdescT : isStrictDescendantOf w.nodes protectedTag n = true := by
                rw [hdesc n hn, hpre]; simp [htagNe]
              have hancF : (ancestorPathTags w.nodes protectedTag).contains n.tag = false := by
                rw [hloc n hn, locOf_some_eq_isPrefixOf]
                cases hrev : (emb n.tag).isPrefixOf (emb protectedTag) with
                | false => rfl
                | true =>
                  exfalso
                  exact htagNe (hembInj n hn (b1_nodeAt_prefix_eq hrev hpre))
              exact ⟨n, Or.inr (Or.inl ⟨hancF, Or.inl hdescT, rfl⟩)⟩
            | false =>
              have hqne : emb n.tag ≠ emb protectedTag := fun h => htagNe (hembInj n hn h)
              obtain ⟨m0, hm0, _, p, hp, hwin0⟩ := hinv.nodes n hn
              obtain ⟨m1, hm1, hm1Ps, _⟩ := (hroot1Other (emb n.tag) hqne).2 m0 hm0
              have hoffLt : off < accesses.length := by rw [haccLen]; omega
              have haccOff : accesses[off]? = some (some k) := by
                have hci := haccChar off hoffLt
                have hin : off ≤ off ∧ off < off + len := ⟨Nat.le_refl _, by omega⟩
                simp only [hin, and_self, ↓reduceIte] at hci
                exact hci
              obtain ⟨q0, q0', hq0, htr0⟩ :=
                node_release_protector_ok_inv root1 root2 (some (emb protectedTag)) accesses hrun
                  (emb n.tag) m1 hm1 hpre off hoffLt k haccOff
              rw [hm1Ps, hwin0 off (Nat.le_refl _) (by omega)] at hq0
              cases hq0
              obtain ⟨p0, hp0, _, herr⟩ := hstepSim n hn (locOf (some (emb protectedTag)) (emb n.tag))
              rw [hp] at hp0; cases hp0
              cases hs : stepNodeOnRangeAccess w.activeProtectors isWrite
                  (locOf (some (emb protectedTag)) (emb n.tag)) off len n with
              | ok n' => exact ⟨n', hstepToRel n hn n' hpre hs⟩
              | error e =>
                obtain ⟨msg, hmsg⟩ := herr e hs
                have hlocEq : locRel (some (emb protectedTag)) (emb n.tag) =
                    nodeRelToMiniRust (locOf (some (emb protectedTag)) (emb n.tag)) := rfl
                rw [hlocEq] at htr0
                rw [htr0] at hmsg; cases hmsg
        obtain ⟨nodes', hrel⟩ := b1_listRel_of_forall w.nodes hall
        exact hno nodes' hrel
      | error e =>
        have hlen1 : ∀ q m1, nodeAt root1 q = some m1 → accesses.length ≤ m1.permissions.length := by
          intro q m1 hm1
          rw [hroot1EqLen q m1 hm1, haccLen, hEqLen (emb protectedTag) tNode htNode]
          exact Nat.le_refl _
        obtain ⟨msg, hmsg⟩ := node_release_protector_error_is_ub root1 (some (emb protectedTag)) accesses e hlen1 hrun
        exact ⟨msg, by rw [hmsg]; rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro w' hw'
      rw [hworldEq] at hw'
      cases hpe : execProtectorEndAccess w protectedTag isWrite off len with
      | error _ => rw [hpe] at hw'; cases hw'
      | ok w1 =>
        rw [hpe] at hw'; cases hw'
        obtain ⟨_, nodes', hw1, hrel⟩ := (execProtectorEndAccess_ok_iff w w1 protectedTag isWrite off len hneLen).mp hpe
        subst hw1
        obtain ⟨tbm', alloc', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hfwd nodes' hrel
        exact ⟨tbm', alloc', h1, h2, h3, h4, h5, h6, h7, rfl, h8, h9⟩
    · intro e he
      rw [hworldEq] at he
      cases hpe : execProtectorEndAccess w protectedTag isWrite off len with
      | ok w1 => rw [hpe] at he; cases he
      | error e' =>
        apply hbwd
        intro nodes' hrel
        have hok := (execProtectorEndAccess_ok_iff w { w with nodes := nodes' } protectedTag isWrite off len hneLen).mpr
          ⟨⟨pn, hpn⟩, nodes', rfl, hrel⟩
        rw [hpe] at hok; cases hok
    · intro tbm' htbm'
      cases hw : execFrameExitMiniRust w [(protectedTag, protId)] with
      | ok w' =>
        rw [hworldEq] at hw
        cases hpe : execProtectorEndAccess w protectedTag isWrite off len with
        | error _ => rw [hpe] at hw; cases hw
        | ok w1 =>
          rw [hpe] at hw; cases hw
          obtain ⟨_, nodes', hw1, hrel⟩ := (execProtectorEndAccess_ok_iff w w1 protectedTag isWrite off len hneLen).mp hpe
          subst hw1
          obtain ⟨tbm'', alloc', h1, h2, h3, _, _, _, _, h8, _⟩ := hfwd nodes' hrel
          rw [htbm'] at h1; cases h1
          exact ⟨releaseProtector { w with nodes := nodes' } protId, alloc',
            rfl, h2, h3, h8⟩
      | error e =>
        have hno : ∀ nodes', ¬ ListRel (ProtectorEndStepRel w protectedTag isWrite off len) w.nodes nodes' := by
          intro nodes' hrel
          have hok := (execProtectorEndAccess_ok_iff w { w with nodes := nodes' } protectedTag isWrite off len hneLen).mpr
            ⟨⟨pn, hpn⟩, nodes', rfl, hrel⟩
          rw [hworldEq, hok] at hw; cases hw
        obtain ⟨msg, hmsg⟩ := hbwd hno
        rw [htbm'] at hmsg; cases hmsg

/-- **Step-indexed pruning-inertness of a frame exit** on the window
`[off, off + len)`: at EVERY intermediate world of the sequential (MiniRust-order)
frame exit, each node that pinned Miri's `SkipSelfAndChildren` optimization would
skip during the next protector-end access (`isPrunedForeignNode`) is left
unchanged by the foreign step it skips. This is the exact condition under which
the pruned Anneal model and the unpruned MiniRust `Node::release_protector`
agree; it constrains permissions, NOT the shape or depth of the borrow tree
(strict descendants of the released node are never visited by either model). -/
def FrameExitPruneInert (off len : Nat) : FnEntryBorrowWorld → List (Nat × Nat) → Prop
  | _, [] => True
  | w, (t, p) :: rest =>
    (match findNode? w.nodes t with
      | some pn => ∀ n ∈ w.nodes, ∀ isWrite,
          protectorEndAccessIsWriteMiniRust? pn = some isWrite →
          isPrunedForeignNode w.nodes (ancestorPathTags w.nodes t) isWrite off len n = true →
          stepNodeOnRangeAccess w.activeProtectors isWrite false off len n = .ok n
      | none => True) ∧
    (∀ w1, execFrameExitMiniRust w [(t, p)] = .ok w1 → FrameExitPruneInert off len w1 rest)

/-- Computable checker for `FrameExitPruneInert` (runs the Anneal frame exit). -/
def frameExitPruneInertBool (off len : Nat) : FnEntryBorrowWorld → List (Nat × Nat) → Bool
  | _, [] => true
  | w, (t, p) :: rest =>
    (match findNode? w.nodes t with
      | some pn =>
        match protectorEndAccessIsWriteMiniRust? pn with
        | some isWrite =>
          w.nodes.all fun n =>
            !isPrunedForeignNode w.nodes (ancestorPathTags w.nodes t) isWrite off len n ||
              (match stepNodeOnRangeAccess w.activeProtectors isWrite false off len n with
                | .ok n' => decide (n' = n)
                | .error _ => false)
        | none => true
      | none => true) &&
    (match execFrameExitMiniRust w [(t, p)] with
      | .ok w1 => frameExitPruneInertBool off len w1 rest
      | .error _ => true)

/-- Constructive soundness of `frameExitPruneInertBool`. -/
theorem frameExitPruneInert_of_bool (off len : Nat) :
    ∀ (frame : List (Nat × Nat)) (w : FnEntryBorrowWorld),
      frameExitPruneInertBool off len w frame = true → FrameExitPruneInert off len w frame
  | [], _, _ => trivial
  | (t, p) :: rest, w, h => by
    unfold frameExitPruneInertBool at h
    rw [Bool.and_eq_true] at h
    obtain ⟨hhead, htail⟩ := h
    refine ⟨?_, fun w1 hw1 => ?_⟩
    · cases hfn : findNode? w.nodes t with
      | none => trivial
      | some pn =>
        rw [hfn] at hhead
        intro n hn isWrite hk hpr
        dsimp only at hhead
        rw [hk] at hhead
        have hn' := List.all_eq_true.mp hhead n hn
        rw [hpr] at hn'
        cases hs : stepNodeOnRangeAccess w.activeProtectors isWrite false off len n with
        | error e => rw [hs] at hn'; cases hn'
        | ok n' =>
          rw [hs] at hn'
          have hEq : n' = n := of_decide_eq_true hn'
          rw [hEq]
    · rw [hw1] at htail
      exact frameExitPruneInert_of_bool off len rest w1 htail

/-- The single-entry MiniRust frame exit only changes per-node permission state
(`NodeMetaRel`): tags, parent links, protector ids, and ranges are preserved. -/
theorem execFrameExitMiniRust_singleton_nodeMetaRel (w w1 : FnEntryBorrowWorld) (t p : Nat)
    (h : execFrameExitMiniRust w [(t, p)] = .ok w1) :
    ListRel NodeMetaRel w.nodes w1.nodes := by
  unfold execFrameExitMiniRust execFrameExitSequential at h
  cases hfor : execProtectorEndAccessFor protectorEndAccessIsWriteMiniRust? w t with
  | error e => rw [hfor] at h; cases h
  | ok w' =>
    rw [hfor] at h
    cases h
    exact (execProtectorEndAccessFor_nodeMetaRel hfor : ListRel NodeMetaRel w.nodes w'.nodes)

/-- **`NoNestedForeignAncestors` is a (strictly stronger) special case of
`FrameExitPruneInert`**: the purely topological shallow-tree predicate rules out
every pruned node up front, at every intermediate world. -/
theorem frameExitPruneInert_of_noNestedForeignAncestors (off len : Nat) :
    ∀ (frame : List (Nat × Nat)) (w : FnEntryBorrowWorld),
      (∀ tp ∈ frame, NoNestedForeignAncestors w.nodes tp.1) →
      FrameExitPruneInert off len w frame
  | [], _, _ => trivial
  | (t, p) :: rest, w, h => by
    refine ⟨?_, fun w1 hw1 => ?_⟩
    · cases hfn : findNode? w.nodes t with
      | none => trivial
      | some pn =>
        intro n hn isWrite _ hpr
        have hfalse := b1_noNestedForeignAncestors_imp_not_pruned w.nodes t isWrite off len
          (h (t, p) (List.mem_cons_self ..)) n hn
        rw [hfalse] at hpr
        cases hpr
    · have hmeta := execFrameExitMiniRust_singleton_nodeMetaRel w w1 t p hw1
      refine frameExitPruneInert_of_noNestedForeignAncestors off len rest w1 fun tp htp => ?_
      intro n1 hn1 hnotAnc u hu
      obtain ⟨n0, hn0, hnm⟩ := hmeta.exists_of_mem_right hn1
      rw [b1_listRel_nodeMetaRel_ancestorPathTags hmeta tp.1, hnm.1] at hnotAnc
      rw [b1_listRel_nodeMetaRel_ancestorPathTags hmeta n1.tag, hnm.1] at hu
      rw [b1_listRel_nodeMetaRel_ancestorPathTags hmeta tp.1]
      exact h tp (List.mem_cons_of_mem _ htp) n0 hn0 hnotAnc u hu

/-- **Symbolic multi-entry whole-tree `TreeSimInv` simulation for
`TreeBorrowsMemory.end_call` vs `execFrameExitMiniRust` on borrow trees of
ARBITRARY depth**: for ANY frame `frame : List (Nat × Nat)` of distinct
`(tag, protId)` entries covering `[off, off + len)` (`0 < len`) on ANY
`TreeSimInv`-related borrow tree — released nodes may have arbitrarily deep
descendant subtrees and foreign subtrees may be arbitrarily nested — whose
`SkipSelfAndChildren` pruning is inert along the exit (`FrameExitPruneInert`) and
whose released nodes have passive outside bytes (`OutsideNoProtectorAccess`):
1. `execFrameExitMiniRust w frame = .ok w'` implies
   `TreeBorrowsMemory.end_call tbm ⟨frame.map (fun tp => (⟨id⟩, emb tp.1))⟩ = .ok tbm'`,
   preserving `alloc'.live = true`, `TreeBorrowsMemory.wfLive` (choice-free),
   and `TreeSimInv off len emb w' alloc'.extra.root`;
2. `execFrameExitMiniRust w frame = .error e` implies
   `TreeBorrowsMemory.end_call` fails with `.error (.ub msg)`;
3. conversely, `TreeBorrowsMemory.end_call` succeeding implies `execFrameExitMiniRust`
   succeeds with a `TreeSimInv`-related post-state.

All frame entries share the window `[off, off + len)` and the allocation `id`
(the scope of the single-window `TreeSimInv`). -/
theorem tbm_end_call_simulates_execFrameExitMiniRust_of_pruneInert :
    ∀ (frame : List (Nat × Nat))
      (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
      (id : Nat) (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
      (off len : Nat), 0 < len →
      ∀ (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld),
      tbm.mem.allocations[id]? = some alloc →
      alloc.live = true →
      (∀ q m, nodeAt alloc.extra.root q = some m → m.permissions.length = alloc.data.length) →
      TreeSimInv off len emb w alloc.extra.root →
      (w.nodes.map (·.tag)).Nodup →
      (frame.map Prod.snd).Nodup →
      (∀ tp ∈ frame, ∃ pn, findNode? w.nodes tp.1 = some pn ∧
        pn.protector = some tp.2 ∧ w.activeProtectors.contains tp.2 = true ∧
        pn.rangeOffset = off ∧ pn.rangeLen = len) →
      (∀ tp ∈ frame, ∀ n ∈ w.nodes, n.tag ≠ tp.1 → n.protector ≠ some tp.2) →
      (∀ tp ∈ frame, ∀ n ∈ w.nodes, emb n.tag = emb tp.1 → n.tag = tp.1) →
      (∀ tp ∈ frame, ∀ n ∈ w.nodes,
        (ancestorPathTags w.nodes tp.1).contains n.tag = locOf (some (emb tp.1)) (emb n.tag)) →
      (∀ tp ∈ frame, ∀ n ∈ w.nodes,
        isStrictDescendantOf w.nodes tp.1 n =
          ((emb tp.1).isPrefixOf (emb n.tag) && decide (n.tag ≠ tp.1))) →
      FrameExitPruneInert off len w frame →
      (∀ tp ∈ frame, ∀ m, nodeAt alloc.extra.root (emb tp.1) = some m →
        OutsideNoProtectorAccess off len m) →
      let extra : Gen.TreeBorrowsFrameExtra := ⟨frame.map (fun tp => (⟨(id : Int)⟩, emb tp.1))⟩
      (∀ w', execFrameExitMiniRust w frame = .ok w' →
        ∃ tbm' alloc',
          TreeBorrowsMemory.end_call tbm extra = .ok tbm' ∧
          tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
          (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm') ∧
          TreeSimInv off len emb w' alloc'.extra.root) ∧
      (∀ e, execFrameExitMiniRust w frame = .error e →
        ∃ msg, TreeBorrowsMemory.end_call tbm extra = .error (.ub msg)) ∧
      (∀ tbm', TreeBorrowsMemory.end_call tbm extra = .ok tbm' →
        ∃ w' alloc',
          execFrameExitMiniRust w frame = .ok w' ∧
          tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
          TreeSimInv off len emb w' alloc'.extra.root)
  | [] => by
    intro tbm id alloc off len _ emb w halloc hlive _ hinv _ _ _ _ _ _ _ _ _
    refine ⟨?_, ?_, ?_⟩
    · intro w' hw'
      cases hw'
      exact ⟨tbm, alloc, rfl, halloc, hlive, fun h => h, hinv⟩
    · intro e he; cases he
    · intro tbm' htbm'
      cases htbm'
      exact ⟨w, alloc, rfl, halloc, hlive, hinv⟩
  | (t, p) :: rest => by
    intro tbm id alloc off len hlen emb w halloc hlive hEqLen hinv htagsNodup hframeNodup
      hframeNodes hprotUnique hembInj hloc hdesc hprune hOutside
    rw [List.map_cons, List.nodup_cons] at hframeNodup
    obtain ⟨pn, hpn, hpnProt, hactProt, hpnOff, hpnLen⟩ := hframeNodes (t, p) (List.mem_cons_self ..)
    obtain ⟨hpruneHead, hpruneTail⟩ := hprune
    have hpruneInert : ∀ n ∈ w.nodes, ∀ isWrite,
        protectorEndAccessIsWriteMiniRust? pn = some isWrite →
        isPrunedForeignNode w.nodes (ancestorPathTags w.nodes t) isWrite off len n = true →
        stepNodeOnRangeAccess w.activeProtectors isWrite false off len n = .ok n := by
      rw [hpn] at hpruneHead
      exact hpruneHead
    obtain ⟨hstepOk, hstepErr, hstepBack⟩ :=
      tbm_release_protector_simulates_execFrameExitMiniRust_step
        tbm id alloc off len hlen emb w t p pn halloc hlive hEqLen hinv htagsNodup
        hpn hpnProt hactProt ⟨hpnOff, hpnLen⟩
        (hprotUnique (t, p) (List.mem_cons_self ..))
        (hembInj (t, p) (List.mem_cons_self ..))
        (hloc (t, p) (List.mem_cons_self ..))
        (hdesc (t, p) (List.mem_cons_self ..))
        hpruneInert
        (hOutside (t, p) (List.mem_cons_self ..))
    have hconsWorld : execFrameExitMiniRust w ((t, p) :: rest) =
        (match execFrameExitMiniRust w [(t, p)] with
        | .error e => .error e
        | .ok w1 => execFrameExitMiniRust w1 rest) := by
      cases h : execProtectorEndAccessFor protectorEndAccessIsWriteMiniRust? w t <;>
        simp [execFrameExitMiniRust, execFrameExitSequential, h]
    have hconsTbm :
        TreeBorrowsMemory.end_call tbm ⟨(((t, p) :: rest).map (fun tp => (⟨(id : Int)⟩, emb tp.1)))⟩ =
        (TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, emb t) >>= fun tbm1 =>
          TreeBorrowsMemory.end_call tbm1 ⟨rest.map (fun tp => (⟨(id : Int)⟩, emb tp.1))⟩) := by
      unfold TreeBorrowsMemory.end_call
      simp only [List.map_cons, List.foldlM_cons]
    -- Helper lifting all invariants from `(w, tbm, alloc)` to `(w1, tbm1, alloc1)` for `rest`.
    have hihOfStep : ∀ w1, execFrameExitMiniRust w [(t, p)] = .ok w1 →
        ∃ (tbm1 : Gen.TreeBorrowsMemory Gen.x86_64)
          (alloc1 : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra),
          TreeBorrowsMemory.release_protector tbm (⟨(id : Int)⟩, emb t) = .ok tbm1 ∧
          (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm1) ∧
          (∀ w', execFrameExitMiniRust w1 rest = .ok w' →
            ∃ tbm' alloc',
              TreeBorrowsMemory.end_call tbm1 ⟨rest.map (fun tp => (⟨(id : Int)⟩, emb tp.1))⟩ = .ok tbm' ∧
              tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
              (TreeBorrowsMemory.wfLive tbm1 → TreeBorrowsMemory.wfLive tbm') ∧
              TreeSimInv off len emb w' alloc'.extra.root) ∧
          (∀ e, execFrameExitMiniRust w1 rest = .error e →
            ∃ msg, TreeBorrowsMemory.end_call tbm1 ⟨rest.map (fun tp => (⟨(id : Int)⟩, emb tp.1))⟩ = .error (.ub msg)) ∧
          (∀ tbm', TreeBorrowsMemory.end_call tbm1 ⟨rest.map (fun tp => (⟨(id : Int)⟩, emb tp.1))⟩ = .ok tbm' →
            ∃ w' alloc',
              execFrameExitMiniRust w1 rest = .ok w' ∧
              tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
              TreeSimInv off len emb w' alloc'.extra.root) := by
      intro w1 hw1
      obtain ⟨tbm1, alloc1, hrel1, halloc1, hlive1, _, hEqLen1, hwf1, hmeta1, hact1, hinv1, hout1⟩ :=
        hstepOk w1 hw1
      have htags1 : (w1.nodes.map (·.tag)).Nodup := by
        rw [ListRel.nodeMetaRel_map_tag_eq hmeta1]; exact htagsNodup
      have hfnRest : ∀ tp ∈ rest, ∃ pn1, findNode? w1.nodes tp.1 = some pn1 ∧
          pn1.protector = some tp.2 ∧ w1.activeProtectors.contains tp.2 = true ∧
          pn1.rangeOffset = off ∧ pn1.rangeLen = len := by
        intro tp htp
        obtain ⟨pn0, hpn0, hp0, ha0, ho0, hl0⟩ := hframeNodes tp (List.mem_cons_of_mem _ htp)
        obtain ⟨pn1, hpn1, hnm⟩ := (b1_listRel_nodeMetaRel_findNode? hmeta1 tp.1).2 pn0 hpn0
        have hpNe : tp.2 ≠ p := fun h => hframeNodup.1 (h ▸ List.mem_map.mpr ⟨tp, htp, rfl⟩)
        have hact1' : w1.activeProtectors.contains tp.2 = true := by
          rw [hact1]
          apply List.contains_iff_mem.mpr
          exact List.mem_filter.mpr ⟨List.contains_iff_mem.mp ha0, by simp [bne, hpNe]⟩
        exact ⟨pn1, hpn1, hnm.2.2.1.trans hp0, hact1', hnm.2.2.2.1.trans ho0, hnm.2.2.2.2.1.trans hl0⟩
      have hpu1 : ∀ tp ∈ rest, ∀ n1 ∈ w1.nodes, n1.tag ≠ tp.1 → n1.protector ≠ some tp.2 := by
        intro tp htp n1 hn1 hne
        obtain ⟨n0, hn0, hnm⟩ := hmeta1.exists_of_mem_right hn1
        rw [hnm.2.2.1]
        exact hprotUnique tp (List.mem_cons_of_mem _ htp) n0 hn0 (by rw [← hnm.1]; exact hne)
      have hemb1 : ∀ tp ∈ rest, ∀ n1 ∈ w1.nodes, emb n1.tag = emb tp.1 → n1.tag = tp.1 := by
        intro tp htp n1 hn1 heq
        obtain ⟨n0, hn0, hnm⟩ := hmeta1.exists_of_mem_right hn1
        rw [hnm.1] at heq ⊢
        exact hembInj tp (List.mem_cons_of_mem _ htp) n0 hn0 heq
      have hloc1 : ∀ tp ∈ rest, ∀ n1 ∈ w1.nodes,
          (ancestorPathTags w1.nodes tp.1).contains n1.tag = locOf (some (emb tp.1)) (emb n1.tag) := by
        intro tp htp n1 hn1
        obtain ⟨n0, hn0, hnm⟩ := hmeta1.exists_of_mem_right hn1
        rw [b1_listRel_nodeMetaRel_ancestorPathTags hmeta1 tp.1, hnm.1]
        exact hloc tp (List.mem_cons_of_mem _ htp) n0 hn0
      have hdesc1 : ∀ tp ∈ rest, ∀ n1 ∈ w1.nodes,
          isStrictDescendantOf w1.nodes tp.1 n1 =
            ((emb tp.1).isPrefixOf (emb n1.tag) && decide (n1.tag ≠ tp.1)) := by
        intro tp htp n1 hn1
        obtain ⟨n0, hn0, hnm⟩ := hmeta1.exists_of_mem_right hn1
        rw [b1_listRel_nodeMetaRel_isStrictDescendantOf hmeta1 tp.1 hnm, hnm.1]
        exact hdesc tp (List.mem_cons_of_mem _ htp) n0 hn0
      have hprune1 : FrameExitPruneInert off len w1 rest := hpruneTail w1 hw1
      have houtRest : ∀ tp ∈ rest, ∀ m1, nodeAt alloc1.extra.root (emb tp.1) = some m1 →
          OutsideNoProtectorAccess off len m1 := by
        intro tp htp m1 hm1 b p0 hp0 hb
        obtain ⟨pn0, hpn0, hp0', _, _, _⟩ := hframeNodes tp (List.mem_cons_of_mem _ htp)
        have htpMem := (mem_of_findNode?_eq_some hpn0).1
        have htpTag := (mem_of_findNode?_eq_some hpn0).2
        have hneTag : tp.1 ≠ t := by
          intro hEq
          have heqPn := b1_eq_of_mem_of_findNode?_of_nodup w.nodes t pn0 pn htagsNodup htpMem (htpTag.trans hEq) hpn
          subst heqPn
          rw [hpnProt] at hp0'
          cases hp0'
          exact hframeNodup.1 (List.mem_map.mpr ⟨tp, htp, rfl⟩)
        have hneEmb : emb tp.1 ≠ emb t := fun h => hneTag (by
          have h1 := hembInj (t, p) (List.mem_cons_self ..) pn0 htpMem (by rw [htpTag]; exact h)
          rw [htpTag] at h1; exact h1)
        obtain ⟨m0, hm0, _⟩ := hinv.nodes pn0 htpMem
        rw [htpTag] at hm0
        obtain ⟨m1', hm1', hsame⟩ := hout1 (emb tp.1) m0 hm0 hneEmb
        rw [hm1'] at hm1; cases hm1
        rw [hsame b hb] at hp0
        exact hOutside tp (List.mem_cons_of_mem _ htp) m0 hm0 b p0 hp0 hb
      obtain ⟨hr1, hr2, hr3⟩ := tbm_end_call_simulates_execFrameExitMiniRust_of_pruneInert rest
        tbm1 id alloc1 off len hlen emb w1 halloc1 hlive1 hEqLen1 hinv1 htags1 hframeNodup.2
        hfnRest hpu1 hemb1 hloc1 hdesc1 hprune1 houtRest
      exact ⟨tbm1, alloc1, hrel1, hwf1, hr1, hr2, hr3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro w' hw'
      rw [hconsWorld] at hw'
      cases hw1 : execFrameExitMiniRust w [(t, p)] with
      | error _ => rw [hw1] at hw'; cases hw'
      | ok w1 =>
        rw [hw1] at hw'
        obtain ⟨tbm1, _, hrel1, hwf1, hr1, _, _⟩ := hihOfStep w1 hw1
        obtain ⟨tbm', alloc', hend', halloc', hlive', hwf2, hinv'⟩ := hr1 w' hw'
        refine ⟨tbm', alloc', ?_, halloc', hlive', fun h => hwf2 (hwf1 h), hinv'⟩
        rw [hconsTbm, hrel1]
        exact hend'
    · intro e he
      rw [hconsWorld] at he
      cases hw1 : execFrameExitMiniRust w [(t, p)] with
      | error e1 =>
        obtain ⟨msg, hmsg⟩ := hstepErr e1 hw1
        exact ⟨msg, by rw [hconsTbm, hmsg]; rfl⟩
      | ok w1 =>
        rw [hw1] at he
        obtain ⟨tbm1, _, hrel1, _, _, hr2, _⟩ := hihOfStep w1 hw1
        obtain ⟨msg, hmsg⟩ := hr2 e he
        exact ⟨msg, by rw [hconsTbm, hrel1]; exact hmsg⟩
    · intro tbm' htbm'
      rw [hconsTbm] at htbm'
      obtain ⟨tbm1, hrel1, hend'⟩ := nwsr_bind_ok htbm'
      obtain ⟨w1, _, hw1, _, _, _⟩ := hstepBack tbm1 hrel1
      obtain ⟨tbm1', _, hrel1', _, _, _, hr3⟩ := hihOfStep w1 hw1
      rw [hrel1'] at hrel1; cases hrel1
      obtain ⟨w', alloc', hw', halloc', hlive', hinv'⟩ := hr3 tbm' hend'
      exact ⟨w', alloc', by rw [hconsWorld, hw1]; exact hw', halloc', hlive', hinv'⟩

/-- **Shallow-tree corollary of
`tbm_end_call_simulates_execFrameExitMiniRust_of_pruneInert`**: the multi-entry
`TreeBorrowsMemory.end_call` ↔ `execFrameExitMiniRust` simulation under the purely
topological hypothesis `NoNestedForeignAncestors` (every node off a released
node's access path hangs directly off that path — in particular a released node
has no grandchildren), which rules out Miri pruning up front
(`frameExitPruneInert_of_noNestedForeignAncestors`). Prefer the general theorem:
it places no restriction on the depth of the borrow tree. -/
theorem tbm_end_call_simulates_execFrameExitMiniRust :
    ∀ (frame : List (Nat × Nat))
      (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
      (id : Nat) (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
      (off len : Nat), 0 < len →
      ∀ (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld),
      tbm.mem.allocations[id]? = some alloc →
      alloc.live = true →
      (∀ q m, nodeAt alloc.extra.root q = some m → m.permissions.length = alloc.data.length) →
      TreeSimInv off len emb w alloc.extra.root →
      (w.nodes.map (·.tag)).Nodup →
      (frame.map Prod.snd).Nodup →
      (∀ tp ∈ frame, ∃ pn, findNode? w.nodes tp.1 = some pn ∧
        pn.protector = some tp.2 ∧ w.activeProtectors.contains tp.2 = true ∧
        pn.rangeOffset = off ∧ pn.rangeLen = len) →
      (∀ tp ∈ frame, ∀ n ∈ w.nodes, n.tag ≠ tp.1 → n.protector ≠ some tp.2) →
      (∀ tp ∈ frame, ∀ n ∈ w.nodes, emb n.tag = emb tp.1 → n.tag = tp.1) →
      (∀ tp ∈ frame, ∀ n ∈ w.nodes,
        (ancestorPathTags w.nodes tp.1).contains n.tag = locOf (some (emb tp.1)) (emb n.tag)) →
      (∀ tp ∈ frame, ∀ n ∈ w.nodes,
        isStrictDescendantOf w.nodes tp.1 n =
          ((emb tp.1).isPrefixOf (emb n.tag) && decide (n.tag ≠ tp.1))) →
      (∀ tp ∈ frame, NoNestedForeignAncestors w.nodes tp.1) →
      (∀ tp ∈ frame, ∀ m, nodeAt alloc.extra.root (emb tp.1) = some m →
        OutsideNoProtectorAccess off len m) →
      let extra : Gen.TreeBorrowsFrameExtra := ⟨frame.map (fun tp => (⟨(id : Int)⟩, emb tp.1))⟩
      (∀ w', execFrameExitMiniRust w frame = .ok w' →
        ∃ tbm' alloc',
          TreeBorrowsMemory.end_call tbm extra = .ok tbm' ∧
          tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
          (TreeBorrowsMemory.wfLive tbm → TreeBorrowsMemory.wfLive tbm') ∧
          TreeSimInv off len emb w' alloc'.extra.root) ∧
      (∀ e, execFrameExitMiniRust w frame = .error e →
        ∃ msg, TreeBorrowsMemory.end_call tbm extra = .error (.ub msg)) ∧
      (∀ tbm', TreeBorrowsMemory.end_call tbm extra = .ok tbm' →
        ∃ w' alloc',
          execFrameExitMiniRust w frame = .ok w' ∧
          tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
          TreeSimInv off len emb w' alloc'.extra.root) :=
  fun frame tbm id alloc off len hlen emb w halloc hlive hEqLen hinv htagsNodup hframeNodup
      hframeNodes hprotUnique hembInj hloc hdesc hnoNest hOutside =>
    tbm_end_call_simulates_execFrameExitMiniRust_of_pruneInert frame tbm id alloc off len hlen emb w
      halloc hlive hEqLen hinv htagsNodup hframeNodup hframeNodes hprotUnique hembInj hloc hdesc
      (frameExitPruneInert_of_noNestedForeignAncestors off len frame w hnoNest) hOutside

/-! #### Deallocation & Byte-Local Helpers -/

private theorem c1_accessChildren_cons (cid : Int) (path : Option Gen.Path) (k : Gen.AccessKind)
    (off len : Nat) (c : Gen.Node) (rest : List Gen.Node) :
    Node.accessChildren cid path k ⟨off⟩ ⟨len⟩ (c :: rest) =
      (Node.access c (subPathAt path cid) k ⟨off⟩ ⟨len⟩ >>= fun c' =>
        Node.accessChildren (cid + 1) path k ⟨off⟩ ⟨len⟩ rest >>= fun rest' =>
          pure (c' :: rest')) := by
  cases path with
  | none => rfl
  | some p => cases p <;> rfl

private theorem c1_listMutateAt_zero {T O : Type} (x : T) (rest : List T) (what : String)
    (f : T → Interp (O × T)) :
    listMutateAt (x :: rest) (0 : Int) what f =
      (f x >>= fun r => pure (r.1, r.2 :: rest)) := by
  simpa only [Int.natCast_zero, List.set_cons_zero] using
    a1_listMutateAt_natCast (x :: rest) 0 what f x rfl

private theorem c1_listMutateAt_one {T O : Type} (x0 x1 : T) (rest : List T) (what : String)
    (f : T → Interp (O × T)) :
    listMutateAt (x0 :: x1 :: rest) (1 : Int) what f =
      (f x1 >>= fun r => pure (r.1, x0 :: r.2 :: rest)) := by
  simpa only [Int.natCast_one, List.set_cons_succ, List.set_cons_zero] using
    a1_listMutateAt_natCast (x0 :: x1 :: rest) 1 what f x1 rfl

private theorem c1_in_or_out (off len b : Nat) :
    (off ≤ b ∧ b < off + len) ∨ (b < off ∨ off + len ≤ b) := by
  rcases Nat.lt_or_ge b off with hlt | hge
  · exact Or.inr (Or.inl hlt)
  · rcases Nat.lt_or_ge b (off + len) with hlt2 | hge2
    · exact Or.inl ⟨hge, hlt2⟩
    · exact Or.inr (Or.inr hge2)

private theorem c1_locOf_self : ∀ (p : Gen.Path), locOf (some p) p = true
  | [] => rfl
  | a :: rest => by
    show locOf (if a == a then some rest else none) rest = true
    rw [a1_int_beq_self a]
    exact c1_locOf_self rest

private theorem c1_ne_lt_or_succ_le (b x : Nat) (h : b ≠ x) : b < x ∨ x + 1 ≤ b := by
  rcases Nat.lt_or_ge b x with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (by omega)

private theorem c1_childrenWf_getElem? (sz : Nat) :
    ∀ (cs : List Gen.Node) (j : Nat) (c : Gen.Node),
      Node.childrenWf sz cs → cs[j]? = some c → Node.wf sz c
  | [], _, _, _, hc => by simp at hc
  | c0 :: rest, 0, c, hwf, hc => by
    rw [List.getElem?_cons_zero] at hc; cases hc
    rw [Node.childrenWf] at hwf; exact hwf.1
  | _ :: rest, j + 1, c, hwf, hc => by
    rw [List.getElem?_cons_succ] at hc
    rw [Node.childrenWf] at hwf
    exact c1_childrenWf_getElem? sz rest j c hwf.2 hc

private theorem c1_nodeWf_len_and_prot (sz : Nat) :
    ∀ (m : Gen.Node), Node.wf sz m →
      m.permissions.length = sz ∧
      ∀ p ∈ m.permissions, Permission.matches_protector p m.«protected» = true
  | ⟨_, _, _⟩, h => by rw [Node.wf] at h; exact ⟨h.1, h.2.1⟩

private theorem c1_nodeWf_nodeAt :
    ∀ (t : Gen.Node) (sz : Nat), Node.wf sz t →
      ∀ (q : Gen.Path) (m : Gen.Node), nodeAt t q = some m → Node.wf sz m
  | ⟨cs, ps, pr⟩, sz, hwf, [], m, hm => by
    cases hm; exact hwf
  | ⟨cs, ps, pr⟩, sz, hwf, i :: rest, m, hm => by
    rw [Node.wf] at hwf
    by_cases hi : 0 ≤ i
    · cases hc : cs[i.toNat]? with
      | none =>
        rw [nwsr_nodeAt_cons_none cs ps pr i rest hi hc] at hm
        cases hm
      | some c =>
        rw [nwsr_nodeAt_cons_some cs ps pr i rest c hi hc] at hm
        exact c1_nodeWf_nodeAt c sz (c1_childrenWf_getElem? sz cs i.toNat c hwf.2.2 hc) rest m hm
    · rw [nwsr_nodeAt_cons_neg cs ps pr i rest hi] at hm
      cases hm

private theorem c1_mapM_unprotect_of_prot :
    ∀ (ps : List Gen.Permission), (∀ p ∈ ps, ∃ pp, p = .Prot pp) →
      ∃ pairs, ps.mapM Permission.unprotect = .ok pairs ∧ pairs.length = ps.length
  | [], _ => ⟨[], rfl, rfl⟩
  | p :: rest, h => by
    obtain ⟨pp, rfl⟩ := h p (List.mem_cons_self ..)
    obtain ⟨pairs, hp, hlen⟩ := c1_mapM_unprotect_of_prot rest
      (fun q hq => h q (List.mem_cons_of_mem _ hq))
    refine ⟨(Gen.Permission.Unprot (PermissionProt.unprotect pp).1,
        (PermissionProt.unprotect pp).2) :: pairs, ?_, ?_⟩
    · rw [List.mapM_cons]
      simp only [Permission.unprotect, bind, Except.bind, pure, Except.pure, hp]
    · simp only [List.length_cons, hlen]

private theorem c1_access_node_of_nodeAt_ok {t t' : Gen.Node} {path : Option Gen.Path}
    {k : Gen.AccessKind} {off len : Nat} (h : Node.access t path k ⟨off⟩ ⟨len⟩ = .ok t') :
    AccessPost k off len path t t' := by
  have hpoint := node_access_ok_inv k off len t t' path h
  obtain ⟨t2, hacc2, hpost⟩ := node_access_ok_of_pointwise k off len t path hpoint
  rw [h] at hacc2
  cases hacc2
  exact hpost

private theorem c1_transitionRange_ok_full (r : Gen.NodeRelation) (k : Gen.AccessKind)
    (off len : Nat) (ps ps' : List Gen.Permission)
    (h : Node.transitionRange r k off len ps = .ok ps') :
    ps'.length = ps.length ∧
    (∀ b, b < off ∨ off + len ≤ b → ps'[b]? = ps[b]?) ∧
    (∀ b, off ≤ b → b < off + len →
      ∃ p p', ps[b]? = some p ∧ Permission.transition p k r = .ok p' ∧ ps'[b]? = some p') := by
  have hpoint : ∀ b, off ≤ b → b < off + len →
      ∃ p p', ps[b]? = some p ∧ Permission.transition p k r = .ok p' := by
    intro b h1 h2
    exact transitionRange_ok_inv r k len off ps ps' h b h1 h2
  obtain ⟨ps2, hrun2, hlen2, hout2, hin2⟩ :=
    transitionRange_ok_of_pointwise r k len off ps hpoint
  rw [h] at hrun2
  cases hrun2
  refine ⟨hlen2, hout2, fun b h1 h2 => ?_⟩
  obtain ⟨p, p', hp, htr⟩ := hpoint b h1 h2
  obtain ⟨p'', htr'', hget⟩ := hin2 b h1 h2 p hp
  rw [htr] at htr''
  cases htr''
  exact ⟨p, p', hp, htr, hget⟩

/-! ### 4.9 Symbolic `TreeBorrowsMemory.deallocate` (`Protected::Strong` vs. `Box<T>` `Protected::Weak`) -/

/-- **Exact equivalence between `Permission.prevents_deallocation` and foreign-write
protector UB** (the invariant stated as a comment in MiniRust's
`PermissionProt::prevents_deallocation`): for every `p : Gen.Permission`,
`p.prevents_deallocation = true` iff `Permission.transition p .Write .Foreign`
raises Tree Borrows UB. -/
theorem permission_prevents_deallocation_iff_foreign_write_err (p : Gen.Permission) :
    Permission.prevents_deallocation p = true ↔
      ∃ msg, Permission.transition p .Write .Foreign = .error (.ub msg) := by
  cases p with
  | Unprot u =>
    cases u <;> constructor
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
  | Prot pp =>
    cases pp with
    | Unique =>
      exact ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩
    | Reserved hlr hfr =>
      cases hlr with
      | false =>
        cases hfr <;> exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
      | true =>
        cases hfr <;> exact ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩
    | Frozen hlr =>
      cases hlr with
      | false => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
      | true => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩
    | Disabled =>
      exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
    | Cell =>
      exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩

private theorem c1_perm_local_write_preserves_prevents (p : Gen.Permission)
    (hp : Permission.prevents_deallocation p = true) :
    (∀ p', Permission.transition p .Write .Local = .ok p' →
      Permission.prevents_deallocation p' = true) ∧
    (∀ e, Permission.transition p .Write .Local = .error e → ∃ msg, e = .ub msg) := by
  cases p with
  | Unprot u => cases u <;> cases hp
  | Prot pp =>
    cases pp with
    | Unique => exact ⟨fun p' h => (by cases h; rfl), fun e h => (by cases h)⟩
    | Reserved hlr hfr =>
      cases hlr with
      | false => cases hp
      | true =>
        cases hfr with
        | false => exact ⟨fun p' h => (by cases h; rfl), fun e h => (by cases h)⟩
        | true => exact ⟨fun p' h => (by cases h), fun e h => (by cases h; exact ⟨_, rfl⟩)⟩
    | Frozen hlr =>
      cases hlr with
      | false => cases hp
      | true => exact ⟨fun p' h => (by cases h), fun e h => (by cases h; exact ⟨_, rfl⟩)⟩
    | Disabled => cases hp
    | Cell => cases hp

mutual

/-- **Whole-tree characterization of `Node.contains_strong_protector_preventing_deallocation`**:
returns `true` iff some reachable node `m` at path `q` carries `Protected::Strong`
and has at least one byte permission `p` with `Permission.prevents_deallocation p = true`. -/
theorem contains_strong_protector_iff :
    ∀ (t : Gen.Node),
      Node.contains_strong_protector_preventing_deallocation t = true ↔
        ∃ q m, nodeAt t q = some m ∧ m.«protected» = .Strong ∧
          ∃ p ∈ m.permissions, Permission.prevents_deallocation p = true
  | ⟨cs, ps, pr⟩ => by
    rw [Node.contains_strong_protector_preventing_deallocation, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, List.any_eq_true]
    constructor
    · rintro (⟨hpr, p, hp, hprev⟩ | hch)
      · exact ⟨[], ⟨cs, ps, pr⟩, rfl, hpr, p, hp, hprev⟩
      · obtain ⟨j, c, hc, q, m, hm, hpr, p, hp, hprev⟩ :=
          (c1_anyChildPreventsDeallocation_iff cs).mp hch
        refine ⟨(j : Int) :: q, m, ?_, hpr, p, hp, hprev⟩
        rw [nwsr_nodeAt_cons_some cs ps pr (j : Int) q c (Int.natCast_nonneg j) hc]
        exact hm
    · rintro ⟨q, m, hm, hpr, p, hp, hprev⟩
      cases q with
      | nil =>
        cases hm
        exact Or.inl ⟨hpr, p, hp, hprev⟩
      | cons i rest =>
        by_cases hi : 0 ≤ i
        · cases hc : cs[i.toNat]? with
          | none =>
            rw [nwsr_nodeAt_cons_none cs ps pr i rest hi hc] at hm
            cases hm
          | some c =>
            rw [nwsr_nodeAt_cons_some cs ps pr i rest c hi hc] at hm
            exact Or.inr ((c1_anyChildPreventsDeallocation_iff cs).mpr
              ⟨i.toNat, c, hc, rest, m, hm, hpr, p, hp, hprev⟩)
        · rw [nwsr_nodeAt_cons_neg cs ps pr i rest hi] at hm
          cases hm

private theorem c1_anyChildPreventsDeallocation_iff :
    ∀ (cs : List Gen.Node),
      Node.anyChildPreventsDeallocation cs = true ↔
        ∃ (j : Nat) (c : Gen.Node), cs[j]? = some c ∧
          ∃ q m, nodeAt c q = some m ∧ m.«protected» = .Strong ∧
            ∃ p ∈ m.permissions, Permission.prevents_deallocation p = true
  | [] =>
    ⟨fun h => (by cases h), fun ⟨j, _, hc, _⟩ => (by simp at hc)⟩
  | c0 :: rest => by
    rw [Node.anyChildPreventsDeallocation, Bool.or_eq_true, contains_strong_protector_iff c0,
      c1_anyChildPreventsDeallocation_iff rest]
    constructor
    · rintro (⟨q, m, hm, hpr, p, hp, hprev⟩ | ⟨j, c, hc, q, m, hm, hpr, p, hp, hprev⟩)
      · exact ⟨0, c0, rfl, q, m, hm, hpr, p, hp, hprev⟩
      · exact ⟨j + 1, c, by rw [List.getElem?_cons_succ]; exact hc, q, m, hm, hpr, p, hp, hprev⟩
    · rintro ⟨j, c, hc, q, m, hm, hpr, p, hp, hprev⟩
      cases j with
      | zero =>
        rw [List.getElem?_cons_zero] at hc
        cases hc
        exact Or.inl ⟨q, m, hm, hpr, p, hp, hprev⟩
      | succ j =>
        rw [List.getElem?_cons_succ] at hc
        exact Or.inr ⟨j, c, hc, q, m, hm, hpr, p, hp, hprev⟩

end

/-- **Unfolding equation for `TreeBorrowsMemory.deallocate`**: on any live
allocation matching `ptr.addr`, `kind`, `size`, and `align`, deallocation runs
a whole-allocation write access `Node.access … .Write ⟨0⟩ size`, checks
`Node.contains_strong_protector_preventing_deallocation`, and if clear marks
the allocation dead (`live := false`). -/
theorem tbm_deallocate_eq
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (kind : Gen.AllocationKind) (size : LibSpecr.Size) (align : LibSpecr.Align)
    (id : Nat) (path : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, path))
    (halloc : tbm.mem.allocations[id]? = some alloc)
    (hlive : alloc.live = true)
    (haddr : ptr.addr = alloc.addr)
    (hkind : kind = alloc.kind)
    (hsize : size = Allocation.size alloc)
    (halign : align = alloc.align) :
    TreeBorrowsMemory.deallocate tbm ptr kind size align =
      (Node.access alloc.extra.root (some path) .Write ⟨0⟩ size >>= fun root' =>
        if Node.contains_strong_protector_preventing_deallocation root' then
          ub "Tree Borrows: deallocating strongly protected allocation"
        else
          pure { tbm with mem := { tbm.mem with
            allocations := tbm.mem.allocations.set id
              { alloc with live := false, extra := { root := root' } } } }) := by
  have hnn : (0 : Int) ≤ (id : Int) := Int.natCast_nonneg id
  have htn : ((id : Int)).toNat = id := rfl
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate listIndex
  simp only [hprov, hnn, htn, halloc, hlive, haddr, hkind, hsize, halign,
    Bool.not_true, Bool.false_eq_true, ne_eq, not_true_eq_false, ↓reduceIte,
    bind, Except.bind, pure, Except.pure]
  cases Node.access alloc.extra.root (some path) .Write ⟨0⟩ (Allocation.size alloc) with
  | error e => rfl
  | ok root' =>
    cases hstr : Node.contains_strong_protector_preventing_deallocation root' with
    | true =>
      simp only [hstr, ↓reduceIte, ub]
    | false =>
      simp only [hstr, Bool.false_eq_true, ↓reduceIte, listSet, hnn, htn, hidlt, and_self,
        pure, Except.pure]

/-- **Universal strong-protector deallocation UB theorem**: on ANY `wfLive`
`TreeBorrowsMemory` and ANY live allocation `alloc` at `id` containing ANY
strongly protected node `m` (`m.«protected» = .Strong`) at path `q` with at
least one byte `b < alloc.data.length` where `Permission.prevents_deallocation p = true`
(covering BOTH `#[rustc_no_writable]` `&mut T` `.Prot (.Reserved true false)`,
standard `&mut T` `.Prot .Unique`, conflicted `&mut T` `.Prot (.Reserved true true)`,
and `&T` `.Prot (.Frozen true)`):
1. `TreeBorrowsMemory.deallocate` ALWAYS fails with Tree Borrows UB regardless
   of which provenance `path` attempts the deallocation;
2. Whenever the deallocation's write access succeeds (e.g. deallocating through
   an unconflicted `&mut T` under EITHER `#[rustc_no_writable]` or standard
   `&mut`), the exact error is
   `.ub "Tree Borrows: deallocating strongly protected allocation"`.

The byte hypothesis is essential: a strongly protected node none of whose bytes
`prevents_deallocation` (after the deallocation write) does NOT block
deallocation (`tbm_deallocate_ok_iff_pointwise`,
`canary_deallocate_exact_boundary`). -/
theorem tbm_deallocate_strong_protector_ub
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (hwf : TreeBorrowsMemory.wfLive tbm)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (id : Nat) (path : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, path))
    (halloc : tbm.mem.allocations[id]? = some alloc)
    (hlive : alloc.live = true)
    (haddr : ptr.addr = alloc.addr)
    (q : Gen.Path) (m : Gen.Node) (hm : nodeAt alloc.extra.root q = some m)
    (hstrong : m.«protected» = .Strong)
    (b : Nat) (hb : b < alloc.data.length) (p : Gen.Permission)
    (hpb : m.permissions[b]? = some p)
    (hprev : Permission.prevents_deallocation p = true) :
    (∃ msg, TreeBorrowsMemory.deallocate tbm ptr alloc.kind ⟨alloc.data.length⟩ alloc.align =
      .error (.ub msg)) ∧
    (∀ root', Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨alloc.data.length⟩ = .ok root' →
      TreeBorrowsMemory.deallocate tbm ptr alloc.kind ⟨alloc.data.length⟩ alloc.align =
        .error (.ub "Tree Borrows: deallocating strongly protected allocation")) := by
  have heq := tbm_deallocate_eq tbm ptr alloc.kind ⟨alloc.data.length⟩ alloc.align id path alloc
    hprov halloc hlive haddr rfl rfl rfl
  have hwfRoot : Node.wf alloc.data.length alloc.extra.root :=
    hwf alloc (List.mem_of_getElem? halloc) hlive
  have hstrongOk : ∀ root',
      Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨alloc.data.length⟩ = .ok root' →
      Node.contains_strong_protector_preventing_deallocation root' = true := by
    intro root' hacc
    have hpost := c1_access_node_of_nodeAt_ok hacc
    obtain ⟨m', hm', hprot', htr⟩ := (hpost q).1 m hm
    obtain ⟨_, _, hin⟩ := c1_transitionRange_ok_full (locRel (some path) q) .Write
      0 alloc.data.length m.permissions m'.permissions htr
    obtain ⟨p0, p', hp0, hstep, hp'⟩ := hin b (Nat.zero_le b) (by omega)
    rw [hpb] at hp0
    cases hp0
    cases hloc : locRel (some path) q with
    | Local =>
      rw [hloc] at hstep
      have hprev' := (c1_perm_local_write_preserves_prevents p hprev).1 p' hstep
      exact (contains_strong_protector_iff root').mpr
        ⟨q, m', hm', hprot'.trans hstrong, p', List.mem_of_getElem? hp', hprev'⟩
    | Foreign =>
      rw [hloc] at hstep
      obtain ⟨msg, hmsg⟩ := (permission_prevents_deallocation_iff_foreign_write_err p).mp hprev
      rw [hmsg] at hstep
      cases hstep
  refine ⟨?_, fun root' hacc => ?_⟩
  · cases hacc : Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨alloc.data.length⟩ with
    | ok root' =>
      refine ⟨"Tree Borrows: deallocating strongly protected allocation", ?_⟩
      rw [heq, hacc]
      dsimp only [bind, Except.bind]
      rw [hstrongOk root' hacc]
      rfl
    | error e =>
      obtain ⟨q', m', hm', herr⟩ := node_access_error_inv .Write 0 alloc.data.length
        alloc.extra.root (some path) e hacc
      have hwfM' := c1_nodeWf_len_and_prot alloc.data.length m'
        (c1_nodeWf_nodeAt alloc.extra.root alloc.data.length hwfRoot q' m' hm')
      obtain ⟨msg, hmsg⟩ := transitionRange_error_is_ub (locRel (some path) q') .Write
        alloc.data.length 0 m'.permissions e (by rw [hwfM'.1]; omega) herr
      refine ⟨msg, ?_⟩
      rw [heq, hacc, hmsg]
      rfl
  · rw [heq, hacc]
    dsimp only [bind, Except.bind]
    rw [hstrongOk root' hacc]
    rfl

/-- **Universal weak-protector (`Box<T>`) deallocation theorem**: on ANY `wfLive`
`TreeBorrowsMemory` and live allocation `alloc` at `id` containing NO strongly
protected node (such as root `.No` + `Box<T>` `Protected::Weak` + unprotected
references):
1. `TreeBorrowsMemory.deallocate` succeeds **iff** the whole-allocation write
   access `Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨alloc.data.length⟩`
   succeeds;
2. On success, the allocation becomes dead (`alloc'.live = false`),
   `TreeBorrowsMemory.wfLive tbm'` is preserved, AND releasing ANY protected
   node `q` of `alloc` via `TreeBorrowsMemory.release_protector tbm' (⟨id⟩, q)`
   (e.g., at `end_call` after the callee dropped `Box<T>`) immediately succeeds
   with `TreeBorrowsMemory.wfLive` preserved;
3. Conversely, if a weakly protected `Box<T>` node `m` at `q` is **conflicted**
   (`.Prot (.Reserved true true)` after a foreign read under `#[rustc_no_writable]`),
   deallocating through `q` raises
   `"Tree Borrows: local write to protected Reserved reference that had a foreign read"`;
   and if `m` has any preventing permission (`.Prot .Unique` or
   `.Prot (.Reserved true _)`), deallocating through ANY foreign pointer `path`
   (`locOf (some path) q = false`) raises foreign-write protector UB. -/
theorem tbm_deallocate_weak_box_ok_iff
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (hwf : TreeBorrowsMemory.wfLive tbm)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (id : Nat) (path : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, path))
    (halloc : tbm.mem.allocations[id]? = some alloc)
    (hlive : alloc.live = true)
    (haddr : ptr.addr = alloc.addr)
    (hnoStrong : ∀ q m, nodeAt alloc.extra.root q = some m → m.«protected» ≠ .Strong) :
    ((∃ tbm', TreeBorrowsMemory.deallocate tbm ptr alloc.kind ⟨alloc.data.length⟩ alloc.align =
        .ok tbm') ↔
      ∃ root', Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨alloc.data.length⟩ =
        .ok root') ∧
    (∀ tbm', TreeBorrowsMemory.deallocate tbm ptr alloc.kind ⟨alloc.data.length⟩ alloc.align =
        .ok tbm' →
      ∃ alloc', tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = false ∧
        TreeBorrowsMemory.wfLive tbm' ∧
        (∀ q m, nodeAt alloc.extra.root q = some m → Protected.yes m.«protected» = true →
          ∃ tbm'', TreeBorrowsMemory.release_protector tbm' (⟨(id : Int)⟩, q) = .ok tbm'' ∧
            TreeBorrowsMemory.wfLive tbm'')) ∧
    (∀ b, b < alloc.data.length → ∀ m, nodeAt alloc.extra.root path = some m →
      m.permissions[b]? = some (.Prot (.Reserved true true)) →
      ∃ msg, TreeBorrowsMemory.deallocate tbm ptr alloc.kind ⟨alloc.data.length⟩ alloc.align =
        .error (.ub msg)) ∧
    (∀ q m, nodeAt alloc.extra.root q = some m → locOf (some path) q = false →
      ∀ b, b < alloc.data.length → ∀ p, m.permissions[b]? = some p →
      Permission.prevents_deallocation p = true →
      ∃ msg, TreeBorrowsMemory.deallocate tbm ptr alloc.kind ⟨alloc.data.length⟩ alloc.align =
        .error (.ub msg)) := by
  have heq := tbm_deallocate_eq tbm ptr alloc.kind ⟨alloc.data.length⟩ alloc.align id path alloc
    hprov halloc hlive haddr rfl rfl rfl
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  have hwfRoot : Node.wf alloc.data.length alloc.extra.root :=
    hwf alloc (List.mem_of_getElem? halloc) hlive
  have hnoStrongPost : ∀ root',
      Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨alloc.data.length⟩ = .ok root' →
      Node.contains_strong_protector_preventing_deallocation root' = false := by
    intro root' hacc
    cases hc : Node.contains_strong_protector_preventing_deallocation root' with
    | false => rfl
    | true =>
      obtain ⟨q, m', hm', hstr, _⟩ := (contains_strong_protector_iff root').mp hc
      have hpost := c1_access_node_of_nodeAt_ok hacc
      cases hm0 : nodeAt alloc.extra.root q with
      | none =>
        rw [(hpost q).2 hm0] at hm'
        cases hm'
      | some m0 =>
        obtain ⟨m1, hm1, hprot1, _⟩ := (hpost q).1 m0 hm0
        rw [hm'] at hm1
        cases hm1
        exact absurd (hprot1.symm.trans hstr) (hnoStrong q m0 hm0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨tbm', hok⟩
      rw [heq] at hok
      cases hacc : Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨alloc.data.length⟩ with
      | ok root' => exact ⟨root', rfl⟩
      | error e => rw [hacc] at hok; cases hok
    · rintro ⟨root', hacc⟩
      rw [heq, hacc]
      dsimp only [bind, Except.bind]
      rw [hnoStrongPost root' hacc]
      exact ⟨_, rfl⟩
  · intro tbm' hok
    have hwf' : TreeBorrowsMemory.wfLive tbm' := TreeBorrowsMemory.deallocate_wfLive hwf hok
    rw [heq] at hok
    cases hacc : Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨alloc.data.length⟩ with
    | error e => rw [hacc] at hok; cases hok
    | ok root' =>
      rw [hacc] at hok
      dsimp only [bind, Except.bind] at hok
      rw [hnoStrongPost root' hacc] at hok
      dsimp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at hok
      cases hok
      refine ⟨{ alloc with live := false, extra := { root := root' } },
        List.getElem?_set_self hidlt, rfl, hwf', ?_⟩
      intro q m hm hprotYes
      have hpost := c1_access_node_of_nodeAt_ok hacc
      obtain ⟨m', hm', hprot', _⟩ := (hpost q).1 m hm
      have hwfRoot' : Node.wf alloc.data.length root' := Node.access_wf hwfRoot hacc
      have hwfM' := c1_nodeWf_len_and_prot alloc.data.length m'
        (c1_nodeWf_nodeAt root' alloc.data.length hwfRoot' q m' hm')
      have hprotYes' : Protected.yes m'.«protected» = true := by rw [hprot']; exact hprotYes
      have hallProt : ∀ p ∈ m'.permissions, ∃ pp, p = .Prot pp := by
        intro p hp
        have hmp := hwfM'.2 p hp
        unfold Permission.matches_protector at hmp
        rw [hprotYes'] at hmp
        cases p with
        | Prot pp => exact ⟨pp, rfl⟩
        | Unprot _ => cases hmp
      obtain ⟨pairs, hpairs, _⟩ := c1_mapM_unprotect_of_prot m'.permissions hallProt
      obtain ⟨tbm'', _, hrel, _, _, hwfImp⟩ := tbm_release_protector_deadAlloc_ok
        { tbm with mem := { tbm.mem with
          allocations := tbm.mem.allocations.set id
            { alloc with live := false, extra := { root := root' } } } }
        id q { alloc with live := false, extra := { root := root' } } m' pairs
        (List.getElem?_set_self hidlt) rfl hm' hprotYes' hpairs
      exact ⟨tbm'', hrel, hwfImp hwf'⟩
  · intro b hb m hm hpb
    cases hacc : Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨alloc.data.length⟩ with
    | ok root' =>
      exfalso
      obtain ⟨ps', htr⟩ := node_access_ok_inv .Write 0 alloc.data.length alloc.extra.root root'
        (some path) hacc path m hm
      obtain ⟨p0, p', hp0, hstep⟩ := transitionRange_ok_inv (locRel (some path) path) .Write
        alloc.data.length 0 m.permissions ps' htr b (Nat.zero_le b) (by omega)
      rw [hpb] at hp0
      cases hp0
      have hloc : locRel (some path) path = .Local := by
        unfold locRel
        rw [c1_locOf_self path]; rfl
      rw [hloc] at hstep
      cases hstep
    | error e =>
      obtain ⟨q', m', hm', herr⟩ := node_access_error_inv .Write 0 alloc.data.length
        alloc.extra.root (some path) e hacc
      have hwfM' := c1_nodeWf_len_and_prot alloc.data.length m'
        (c1_nodeWf_nodeAt alloc.extra.root alloc.data.length hwfRoot q' m' hm')
      obtain ⟨msg, hmsg⟩ := transitionRange_error_is_ub (locRel (some path) q') .Write
        alloc.data.length 0 m'.permissions e (by rw [hwfM'.1]; omega) herr
      exact ⟨msg, by rw [heq, hacc, hmsg]; rfl⟩
  · intro q m hm hfor b hb p hpb hprev
    cases hacc : Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨alloc.data.length⟩ with
    | ok root' =>
      exfalso
      obtain ⟨ps', htr⟩ := node_access_ok_inv .Write 0 alloc.data.length alloc.extra.root root'
        (some path) hacc q m hm
      obtain ⟨p0, p', hp0, hstep⟩ := transitionRange_ok_inv (locRel (some path) q) .Write
        alloc.data.length 0 m.permissions ps' htr b (Nat.zero_le b) (by omega)
      rw [hpb] at hp0
      cases hp0
      have hloc : locRel (some path) q = .Foreign := by
        unfold locRel; rw [hfor]; rfl
      rw [hloc] at hstep
      obtain ⟨msg, hmsg⟩ := (permission_prevents_deallocation_iff_foreign_write_err p).mp hprev
      rw [hmsg] at hstep
      cases hstep
    | error e =>
      obtain ⟨q', m', hm', herr⟩ := node_access_error_inv .Write 0 alloc.data.length
        alloc.extra.root (some path) e hacc
      have hwfM' := c1_nodeWf_len_and_prot alloc.data.length m'
        (c1_nodeWf_nodeAt alloc.extra.root alloc.data.length hwfRoot q' m' hm')
      obtain ⟨msg, hmsg⟩ := transitionRange_error_is_ub (locRel (some path) q') .Write
        alloc.data.length 0 m'.permissions e (by rw [hwfM'.1]; omega) herr
      exact ⟨msg, by rw [heq, hacc, hmsg]; rfl⟩

/-- **Closed non-vacuity canary for Section 4.9 (`tbm_deallocate_strong_protector_ub`
and `tbm_deallocate_weak_box_ok_iff`)**: exercises BOTH symbolic deallocation
theorems directly with zero hypotheses on:
1. strongly protected `#[rustc_no_writable]` `&mut u32` (`.Prot (.Reserved true false)`)
   → exact `.ub "Tree Borrows: deallocating strongly protected allocation"`;
2. strongly protected `&u32` (`.Prot (.Frozen true)`) → Tree Borrows UB;
3. weakly protected `Box<u32>` (`#[rustc_no_writable]` `.Prot (.Reserved true false)`)
   → deallocation succeeds, `alloc'.live = false`, `wfLive` preserved, and
   subsequent `release_protector` on the dead allocation succeeds;
4. weakly protected conflicted `#[rustc_no_writable]` `Box<u32>` (`.Prot (.Reserved true true)`)
   → deallocation through the `Box` raises UB;
5. weakly protected `Box<u32>` + foreign pointer deallocation → raises UB. -/
theorem canary_symbolic_deallocate_strong_vs_weak :
    let mkHeapTbm := fun (cPerms : List Gen.Permission) (cProt : Gen.Protected) =>
      ({ params := ⟨true⟩
         mem := {
           allocations := [{
             mkRootAllocTB (tbU32Bytes 7) 256 4 .Heap with
             extra := { root := ⟨[⟨[], cPerms, cProt⟩, ⟨[], List.replicate 4 (.Unprot .Reserved), .No⟩],
               List.replicate 4 (.Unprot .Unique), .No⟩ }
           }]
           _phantom := ⟨⟩ } } : Gen.TreeBorrowsMemory Gen.x86_64)
    let ptrChild : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
      { addr := 256, provenance := some (⟨0⟩, [0]) }
    let ptrForeign : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
      { addr := 256, provenance := some (⟨0⟩, [1]) }
    TreeBorrowsMemory.deallocate (mkHeapTbm (List.replicate 4 (.Prot (.Reserved true false))) .Strong)
        ptrChild .Heap ⟨4⟩ ⟨4⟩ =
      .error (.ub "Tree Borrows: deallocating strongly protected allocation") ∧
    (∃ msg, TreeBorrowsMemory.deallocate (mkHeapTbm (List.replicate 4 (.Prot (.Frozen true))) .Strong)
        ptrChild .Heap ⟨4⟩ ⟨4⟩ = .error (.ub msg)) ∧
    (∃ tbm' alloc' tbm'',
      TreeBorrowsMemory.deallocate (mkHeapTbm (List.replicate 4 (.Prot (.Reserved true false))) .Weak)
        ptrChild .Heap ⟨4⟩ ⟨4⟩ = .ok tbm' ∧
      tbm'.mem.allocations[0]? = some alloc' ∧ alloc'.live = false ∧
      TreeBorrowsMemory.wfLive tbm' ∧
      TreeBorrowsMemory.release_protector tbm' (⟨0⟩, [0]) = .ok tbm'' ∧
      TreeBorrowsMemory.wfLive tbm'') ∧
    (∃ msg, TreeBorrowsMemory.deallocate (mkHeapTbm (List.replicate 4 (.Prot (.Reserved true true))) .Weak)
        ptrChild .Heap ⟨4⟩ ⟨4⟩ = .error (.ub msg)) ∧
    (∃ msg, TreeBorrowsMemory.deallocate (mkHeapTbm (List.replicate 4 (.Prot (.Reserved true false))) .Weak)
        ptrForeign .Heap ⟨4⟩ ⟨4⟩ = .error (.ub msg)) := by
  dsimp only
  have hwf1 : TreeBorrowsMemory.wfLive
      ({ params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB (tbU32Bytes 7) 256 4 .Heap with
           extra := { root := ⟨[⟨[], List.replicate 4 (.Prot (.Reserved true false)), .Strong⟩,
             ⟨[], List.replicate 4 (.Unprot .Reserved), .No⟩],
             List.replicate 4 (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } } :
        Gen.TreeBorrowsMemory Gen.x86_64) :=
    tbm_wfLive_of_bool _ (by decide +kernel)
  have hwf2 : TreeBorrowsMemory.wfLive
      ({ params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB (tbU32Bytes 7) 256 4 .Heap with
           extra := { root := ⟨[⟨[], List.replicate 4 (.Prot (.Frozen true)), .Strong⟩,
             ⟨[], List.replicate 4 (.Unprot .Reserved), .No⟩],
             List.replicate 4 (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } } :
        Gen.TreeBorrowsMemory Gen.x86_64) :=
    tbm_wfLive_of_bool _ (by decide +kernel)
  have hwf3 : TreeBorrowsMemory.wfLive
      ({ params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB (tbU32Bytes 7) 256 4 .Heap with
           extra := { root := ⟨[⟨[], List.replicate 4 (.Prot (.Reserved true false)), .Weak⟩,
             ⟨[], List.replicate 4 (.Unprot .Reserved), .No⟩],
             List.replicate 4 (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } } :
        Gen.TreeBorrowsMemory Gen.x86_64) :=
    tbm_wfLive_of_bool _ (by decide +kernel)
  have hwf4 : TreeBorrowsMemory.wfLive
      ({ params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB (tbU32Bytes 7) 256 4 .Heap with
           extra := { root := ⟨[⟨[], List.replicate 4 (.Prot (.Reserved true true)), .Weak⟩,
             ⟨[], List.replicate 4 (.Unprot .Reserved), .No⟩],
             List.replicate 4 (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } } :
        Gen.TreeBorrowsMemory Gen.x86_64) :=
    tbm_wfLive_of_bool _ (by decide +kernel)
  have hnoStr : ∀ (cPerms : List Gen.Permission) (q : Gen.Path) (m : Gen.Node),
      nodeAt ⟨[⟨[], cPerms, .Weak⟩, ⟨[], List.replicate 4 (.Unprot .Reserved), .No⟩],
        List.replicate 4 (.Unprot .Unique), .No⟩ q = some m → m.«protected» ≠ .Strong := by
    intro cPerms q m hm
    rcases q with _ | ⟨i, rest⟩
    · cases hm; intro h; cases h
    · by_cases hi : 0 ≤ i
      · cases hi0 : i.toNat with
        | zero =>
          rw [nwsr_nodeAt_cons_some _ _ _ i rest ⟨[], cPerms, .Weak⟩ hi (by simp [hi0])] at hm
          cases rest with
          | nil => cases hm; intro h; cases h
          | cons j r =>
            by_cases hj : 0 ≤ j
            · rw [nwsr_nodeAt_cons_none _ _ _ j r hj (by simp)] at hm; cases hm
            · rw [nwsr_nodeAt_cons_neg _ _ _ j r hj] at hm; cases hm
        | succ k =>
          cases k with
          | zero =>
            rw [nwsr_nodeAt_cons_some _ _ _ i rest ⟨[], List.replicate 4 (.Unprot .Reserved), .No⟩ hi
              (by simp [hi0])] at hm
            cases rest with
            | nil => cases hm; intro h; cases h
            | cons j r =>
              by_cases hj : 0 ≤ j
              · rw [nwsr_nodeAt_cons_none _ _ _ j r hj (by simp)] at hm; cases hm
              · rw [nwsr_nodeAt_cons_neg _ _ _ j r hj] at hm; cases hm
          | succ k' =>
            rw [nwsr_nodeAt_cons_none _ _ _ i rest hi (by simp [hi0])] at hm; cases hm
      · rw [nwsr_nodeAt_cons_neg _ _ _ i rest hi] at hm; cases hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hacc1 : Node.access
        ⟨[⟨[], List.replicate 4 (.Prot (.Reserved true false)), .Strong⟩,
          ⟨[], List.replicate 4 (.Unprot .Reserved), .No⟩],
          List.replicate 4 (.Unprot .Unique), .No⟩ (some [0]) .Write ⟨0⟩ ⟨4⟩ =
        .ok ⟨[⟨[], List.replicate 4 (.Prot .Unique), .Strong⟩,
          ⟨[], List.replicate 4 (.Unprot .Disabled), .No⟩],
          List.replicate 4 (.Unprot .Unique), .No⟩ := rfl
    exact (tbm_deallocate_strong_protector_ub _ hwf1
      { addr := 256, provenance := some (⟨0⟩, [0]) } 0 [0] _ rfl rfl rfl rfl
      [0] _ rfl rfl 0 (by decide) _ rfl rfl).2 _ hacc1
  · exact (tbm_deallocate_strong_protector_ub _ hwf2
      { addr := 256, provenance := some (⟨0⟩, [0]) } 0 [0] _ rfl rfl rfl rfl
      [0] _ rfl rfl 0 (by decide) _ rfl rfl).1
  · have hweak := tbm_deallocate_weak_box_ok_iff _ hwf3
      { addr := 256, provenance := some (⟨0⟩, [0]) } 0 [0] _ rfl rfl rfl rfl (hnoStr _)
    have hacc3 : Node.access
        ⟨[⟨[], List.replicate 4 (.Prot (.Reserved true false)), .Weak⟩,
          ⟨[], List.replicate 4 (.Unprot .Reserved), .No⟩],
          List.replicate 4 (.Unprot .Unique), .No⟩ (some [0]) .Write ⟨0⟩ ⟨4⟩ =
        .ok ⟨[⟨[], List.replicate 4 (.Prot .Unique), .Weak⟩,
          ⟨[], List.replicate 4 (.Unprot .Disabled), .No⟩],
          List.replicate 4 (.Unprot .Unique), .No⟩ := rfl
    obtain ⟨tbm', htbm'⟩ := hweak.1.mpr ⟨_, hacc3⟩
    obtain ⟨alloc', ha', hdead, hwf', hrel⟩ := hweak.2.1 tbm' htbm'
    obtain ⟨tbm'', htbm'', hwf''⟩ := hrel [0] _ rfl rfl
    exact ⟨tbm', alloc', tbm'', htbm', ha', hdead, hwf', htbm'', hwf''⟩
  · exact (tbm_deallocate_weak_box_ok_iff _ hwf4
      { addr := 256, provenance := some (⟨0⟩, [0]) } 0 [0] _ rfl rfl rfl rfl (hnoStr _)).2.2.1
      0 (by decide) _ rfl rfl
  · exact (tbm_deallocate_weak_box_ok_iff _ hwf3
      { addr := 256, provenance := some (⟨0⟩, [1]) } 0 [1] _ rfl rfl rfl rfl (hnoStr _)).2.2.2
      [0] _ rfl rfl 0 (by decide) _ rfl rfl


/-! #### Exact Whole-Tree Deallocation Criterion (`Protected::Strong`, `Box<T>` `Protected::Weak`, Unprotected) -/

/-- **Per-byte deallocation admissibility table** of MiniRust Tree Borrows: whether
a byte permission `p` of a node standing in relation `rel` to the deallocating
pointer (`Local` = the pointer's own node or one of its ancestors, `Foreign` =
every other node) lets `TreeBorrowsMemory.deallocate` proceed, where `strong`
records whether that node carries `Protected::Strong`:
- `Foreign` nodes: exactly the permissions surviving a foreign write, i.e.
  `¬ Permission.prevents_deallocation p` — every `Unprot`, and the protected
  `Reserved { had_local_read: false }`, `Frozen { had_local_read: false }`,
  `Disabled`, and `Cell` (for BOTH `Protected::Weak` and `Protected::Strong`);
- `Local` unprotected nodes: every permission except `Frozen` / `Disabled`;
- `Local` protected nodes: `Cell` always; `Unique` and unconflicted `Reserved`
  only under a NON-strong protector (`Box<T>` `Protected::Weak`), since the
  deallocation write leaves them `Unique`, which
  `contains_strong_protector_preventing_deallocation` rejects under
  `Protected::Strong`; conflicted `Reserved`, `Frozen`, and `Disabled` never. -/
def permAllowsDealloc (rel : Gen.NodeRelation) (strong : Bool) : Gen.Permission → Bool
  | .Unprot u =>
    match rel, u with
    | .Local, .Frozen => false
    | .Local, .Disabled => false
    | _, _ => true
  | .Prot pp =>
    match rel, pp with
    | .Foreign, .Reserved false _ => true
    | .Foreign, .Frozen false => true
    | .Foreign, .Disabled => true
    | .Foreign, .Cell => true
    | .Local, .Cell => true
    | .Local, .Unique => !strong
    | .Local, .Reserved _ false => !strong
    | _, _ => false

private theorem nwsr_permAllowsDealloc_eq (rel : Gen.NodeRelation) (strong : Bool)
    (p : Gen.Permission) :
    permAllowsDealloc rel strong p =
      match Permission.transition p .Write rel with
      | .ok p' => !strong || !Permission.prevents_deallocation p'
      | .error _ => false := by
  cases rel <;> cases strong <;> cases p with
  | Unprot u => cases u <;> rfl
  | Prot pp =>
    cases pp with
    | Reserved a b => cases a <;> cases b <;> rfl
    | Frozen a => cases a <;> rfl
    | _ => rfl

/-- **Exactness of `permAllowsDealloc`**: the table holds iff the deallocation
write transition of the byte succeeds AND, under a strong protector, its
post-permission does not prevent deallocation. -/
theorem permAllowsDealloc_iff (rel : Gen.NodeRelation) (strong : Bool) (p : Gen.Permission) :
    permAllowsDealloc rel strong p = true ↔
      ∃ p', Permission.transition p .Write rel = .ok p' ∧
        (strong = true → Permission.prevents_deallocation p' = false) := by
  rw [nwsr_permAllowsDealloc_eq]
  cases Permission.transition p .Write rel with
  | error e => exact ⟨fun h => (by cases h), fun ⟨_, h, _⟩ => (by cases h)⟩
  | ok p' =>
    cases strong with
    | false => exact ⟨fun _ => ⟨p', rfl, fun h => (by cases h)⟩, fun _ => rfl⟩
    | true =>
      constructor
      · intro h
        refine ⟨p', rfl, fun _ => ?_⟩
        cases hprev : Permission.prevents_deallocation p' with
        | false => rfl
        | true =>
          dsimp only at h
          rw [hprev] at h
          cases h
      · rintro ⟨p'', hp'', hs⟩
        cases hp''
        dsimp only
        rw [hs rfl]
        rfl

/-- **Exact whole-tree characterization of `TreeBorrowsMemory.deallocate`
(`Protected::Strong`, `Protected::Weak`, and unprotected nodes alike)**: on ANY
`wfLive` memory and ANY live allocation deallocated with matching address,
kind, size, and alignment through the pointer at `path`, deallocation succeeds
**iff EVERY byte of EVERY node** of the allocation's borrow tree satisfies the
per-byte table `permAllowsDealloc` under the node's path-determined relation
and strong-protector flag. In particular (`permAllowsDealloc_iff`):
- a protected node FOREIGN to the deallocating pointer (`Protected::Weak` and
  `Protected::Strong` alike) blocks deallocation exactly on its locally accessed
  bytes (`Unique`, `Reserved` / `Frozen` with `had_local_read`);
- `Protected::Strong` additionally blocks deallocation through the protected
  pointer itself (or a pointer derived from it) on every byte the deallocation
  write leaves `Unique`; so a strongly protected node whose bytes are all
  `Cell`, never-accessed `Reserved` / `Frozen`, or `Disabled` (e.g. a zero-sized
  `&mut ()` or an `&UnsafeCell<T>` parameter) does NOT block deallocation;
- a `Box<T>` weak protector lets the `Box` (or a pointer derived from it)
  deallocate unless one of its bytes is conflicted
  (`Reserved { had_foreign_read: true }`), `Frozen`, or `Disabled`. -/
theorem tbm_deallocate_ok_iff_pointwise
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (hwf : TreeBorrowsMemory.wfLive tbm)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (id : Nat) (path : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, path))
    (halloc : tbm.mem.allocations[id]? = some alloc)
    (hlive : alloc.live = true)
    (haddr : ptr.addr = alloc.addr) :
    (∃ tbm', TreeBorrowsMemory.deallocate tbm ptr alloc.kind ⟨alloc.data.length⟩ alloc.align =
        .ok tbm') ↔
      ∀ q m, nodeAt alloc.extra.root q = some m →
        ∀ (b : Nat) (p : Gen.Permission), m.permissions[b]? = some p →
          permAllowsDealloc (locRel (some path) q) (decide (m.«protected» = .Strong)) p = true := by
  have heq := tbm_deallocate_eq tbm ptr alloc.kind ⟨alloc.data.length⟩ alloc.align id path alloc
    hprov halloc hlive haddr rfl rfl rfl
  have hwfRoot : Node.wf alloc.data.length alloc.extra.root :=
    hwf alloc (List.mem_of_getElem? halloc) hlive
  have hlenOf : ∀ q m, nodeAt alloc.extra.root q = some m →
      m.permissions.length = alloc.data.length := fun q m hm =>
    (c1_nodeWf_len_and_prot alloc.data.length m
      (c1_nodeWf_nodeAt alloc.extra.root alloc.data.length hwfRoot q m hm)).1
  constructor
  · rintro ⟨tbm', hok⟩ q m hm b p hpb
    rw [heq] at hok
    obtain ⟨root', hacc, hok⟩ := nwsr_bind_ok hok
    have hnoStr : Node.contains_strong_protector_preventing_deallocation root' = false := by
      cases hc : Node.contains_strong_protector_preventing_deallocation root' with
      | false => rfl
      | true => rw [hc] at hok; cases hok
    have hb : b < alloc.data.length := by
      rw [← hlenOf q m hm]; exact (List.getElem?_eq_some_iff.mp hpb).1
    obtain ⟨m', hm', hprot', htr⟩ := (c1_access_node_of_nodeAt_ok hacc q).1 m hm
    obtain ⟨_, _, hin⟩ := c1_transitionRange_ok_full (locRel (some path) q) .Write
      0 alloc.data.length m.permissions m'.permissions htr
    obtain ⟨p0, p', hp0, hstep, hp'⟩ := hin b (Nat.zero_le b) (by omega)
    rw [hpb] at hp0
    cases hp0
    refine (permAllowsDealloc_iff _ _ p).mpr ⟨p', hstep, fun hstrong => ?_⟩
    cases hprev : Permission.prevents_deallocation p' with
    | false => rfl
    | true =>
      have hcontains := (contains_strong_protector_iff root').mpr
        ⟨q, m', hm', hprot'.trans (of_decide_eq_true hstrong), p', List.mem_of_getElem? hp', hprev⟩
      rw [hnoStr] at hcontains
      cases hcontains
  · intro hall
    have hpoint : ∀ q m, nodeAt alloc.extra.root q = some m →
        ∃ ps', Node.transitionRange (locRel (some path) q) .Write 0 alloc.data.length
          m.permissions = .ok ps' := by
      intro q m hm
      obtain ⟨ps', hrun, _⟩ := transitionRange_ok_of_pointwise (locRel (some path) q) .Write
        alloc.data.length 0 m.permissions (by
          intro b _ hb2
          have hblt : b < m.permissions.length := by rw [hlenOf q m hm]; omega
          obtain ⟨p, hp⟩ : ∃ p, m.permissions[b]? = some p :=
            ⟨m.permissions[b], List.getElem?_eq_getElem hblt⟩
          obtain ⟨p', hstep, _⟩ := (permAllowsDealloc_iff _ _ p).mp (hall q m hm b p hp)
          exact ⟨p, p', hp, hstep⟩)
      exact ⟨ps', hrun⟩
    obtain ⟨root', hacc, hpost⟩ :=
      node_access_ok_of_pointwise .Write 0 alloc.data.length alloc.extra.root (some path) hpoint
    have hnoStr : Node.contains_strong_protector_preventing_deallocation root' = false := by
      cases hc : Node.contains_strong_protector_preventing_deallocation root' with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨q, m', hm', hstr, p', hp'mem, hprev⟩ := (contains_strong_protector_iff root').mp hc
        cases hm0 : nodeAt alloc.extra.root q with
        | none =>
          rw [(hpost q).2 hm0] at hm'
          cases hm'
        | some m0 =>
          obtain ⟨m1, hm1, hprot1, htr⟩ := (hpost q).1 m0 hm0
          rw [hm'] at hm1
          cases hm1
          obtain ⟨b, hb⟩ := List.getElem?_of_mem hp'mem
          obtain ⟨hlen', _, hin⟩ := c1_transitionRange_ok_full (locRel (some path) q) .Write
            0 alloc.data.length m0.permissions m'.permissions htr
          have hblt : b < alloc.data.length := by
            rw [← hlenOf q m0 hm0, ← hlen']; exact (List.getElem?_eq_some_iff.mp hb).1
          obtain ⟨p0, p'', hp0, hstep, hp''⟩ := hin b (Nat.zero_le b) (by omega)
          rw [hb] at hp''
          cases hp''
          obtain ⟨p3, hstep3, hsafe⟩ := (permAllowsDealloc_iff _ _ p0).mp (hall q m0 hm0 b p0 hp0)
          rw [hstep] at hstep3
          cases hstep3
          have := hsafe (decide_eq_true (hprot1.symm.trans hstr))
          rw [hprev] at this
          cases this
    rw [heq, hacc]
    dsimp only [bind, Except.bind]
    rw [hnoStr]
    exact ⟨_, rfl⟩

/-- Computable whole-tree checker for the per-byte deallocation table
(`permAllowsDealloc` at EVERY byte of EVERY node, enumerated by `nodePaths`). -/
def deallocAllowedBool (path : Gen.Path) (root : Gen.Node) : Bool :=
  (nodePaths root).all fun q =>
    match nodeAt root q with
    | some m =>
      m.permissions.all
        (permAllowsDealloc (locRel (some path) q) (decide (m.«protected» = .Strong)))
    | none => true

/-- `deallocAllowedBool` decides exactly the whole-tree per-byte table. -/
theorem deallocAllowedBool_iff (path : Gen.Path) (root : Gen.Node) :
    deallocAllowedBool path root = true ↔
      ∀ q m, nodeAt root q = some m →
        ∀ (b : Nat) (p : Gen.Permission), m.permissions[b]? = some p →
          permAllowsDealloc (locRel (some path) q) (decide (m.«protected» = .Strong)) p = true := by
  unfold deallocAllowedBool
  rw [List.all_eq_true]
  constructor
  · intro h q m hm b p hp
    have hq := h q (nodeAt_mem_nodePaths root q m hm)
    rw [hm] at hq
    exact List.all_eq_true.mp hq p (List.mem_of_getElem? hp)
  · intro h q _
    cases hm : nodeAt root q with
    | none => rfl
    | some m =>
      refine List.all_eq_true.mpr fun p hp => ?_
      obtain ⟨b, hb⟩ := List.getElem?_of_mem hp
      exact h q m hm b p hb

/-- **Exact boundary of the `BasicMemory`-level deallocation pre-checks**
(everything `TreeBorrowsMemory.deallocate` rejects BEFORE the Tree Borrows
access): a pointer without provenance, a dead allocation (`"double-free"`, e.g.
a second `Box<T>` drop after `tbm_deallocate_weak_box_ok_iff`), a pointer not at
the allocation base, and mismatched kind / size / alignment are each Undefined
Behavior, with the exact MiniRust message. -/
theorem tbm_deallocate_precheck_ub
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (kind : Gen.AllocationKind) (size : LibSpecr.Size) (align : LibSpecr.Align) :
    (ptr.provenance = none →
      TreeBorrowsMemory.deallocate tbm ptr kind size align =
        .error (.ub "deallocating invalid pointer")) ∧
    (∀ (id : Nat) (path : Gen.Path)
        (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra),
      ptr.provenance = some (⟨(id : Int)⟩, path) →
      tbm.mem.allocations[id]? = some alloc →
      (alloc.live = false →
        TreeBorrowsMemory.deallocate tbm ptr kind size align = .error (.ub "double-free")) ∧
      (alloc.live = true → ptr.addr ≠ alloc.addr →
        TreeBorrowsMemory.deallocate tbm ptr kind size align =
          .error (.ub "deallocating with pointer not to the beginning of its allocation")) ∧
      (alloc.live = true → ptr.addr = alloc.addr → kind ≠ alloc.kind →
        ∃ msg, TreeBorrowsMemory.deallocate tbm ptr kind size align = .error (.ub msg)) ∧
      (alloc.live = true → ptr.addr = alloc.addr → kind = alloc.kind →
        size ≠ ⟨alloc.data.length⟩ →
        TreeBorrowsMemory.deallocate tbm ptr kind size align =
          .error (.ub "deallocating with incorrect size information")) ∧
      (alloc.live = true → ptr.addr = alloc.addr → kind = alloc.kind →
        size = ⟨alloc.data.length⟩ → align ≠ alloc.align →
        TreeBorrowsMemory.deallocate tbm ptr kind size align =
          .error (.ub "deallocating with incorrect alignment information"))) := by
  refine ⟨fun hnone => ?_, fun id path alloc hprov halloc => ?_⟩
  · unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate
    simp only [hnone, bind, Except.bind, ub]
  · have hnn : (0 : Int) ≤ (id : Int) := Int.natCast_nonneg id
    have htn : ((id : Int)).toNat = id := rfl
    refine ⟨fun hdead => ?_, fun hlive haddr => ?_, fun hlive haddr hkind => ?_,
      fun hlive haddr hkind hsize => ?_, fun hlive haddr hkind hsize halign => ?_⟩
    · unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate listIndex
      simp only [hprov, hnn, htn, halloc, hdead, Bool.not_false, ↓reduceIte,
        bind, Except.bind, pure, Except.pure, ub]
    · unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate listIndex
      simp only [hprov, hnn, htn, halloc, hlive, haddr, Bool.not_true, Bool.false_eq_true,
        ne_eq, not_false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure, ub]
    · unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate listIndex
      simp only [hprov, hnn, htn, halloc, hlive, haddr, hkind, Bool.not_true, Bool.false_eq_true,
        ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte, bind, Except.bind, pure,
        Except.pure, ub]
      exact ⟨_, rfl⟩
    · have hsize' : size ≠ Allocation.size alloc := hsize
      unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate listIndex
      simp only [hprov, hnn, htn, halloc, hlive, haddr, hkind, hsize', Bool.not_true,
        Bool.false_eq_true, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte, bind,
        Except.bind, pure, Except.pure, ub]
    · have hsize' : size = Allocation.size alloc := hsize
      unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate listIndex
      simp only [hprov, hnn, htn, halloc, hlive, haddr, hkind, hsize', halign, Bool.not_true,
        Bool.false_eq_true, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte, bind,
        Except.bind, pure, Except.pure, ub]

/-- **Full-domain exact success criterion of `TreeBorrowsMemory.deallocate`**:
for ANY `wfLive` memory, ANY pointer with provenance `(id, path)` into an
existing allocation, and ANY requested `kind`, `size`, `align`, deallocation
succeeds **iff** the allocation is live, the pointer sits at its base, kind /
size / alignment match, AND the decidable whole-tree per-byte table
`deallocAllowedBool` holds (`permAllowsDealloc` at every byte of every node,
covering `Protected::Strong`, `Box<T>` `Protected::Weak`, and unprotected
nodes). -/
theorem tbm_deallocate_ok_iff_full
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (hwf : TreeBorrowsMemory.wfLive tbm)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (kind : Gen.AllocationKind) (size : LibSpecr.Size) (align : LibSpecr.Align)
    (id : Nat) (path : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, path))
    (halloc : tbm.mem.allocations[id]? = some alloc) :
    (∃ tbm', TreeBorrowsMemory.deallocate tbm ptr kind size align = .ok tbm') ↔
      (alloc.live = true ∧ ptr.addr = alloc.addr ∧ kind = alloc.kind ∧
        size = ⟨alloc.data.length⟩ ∧ align = alloc.align ∧
        deallocAllowedBool path alloc.extra.root = true) := by
  obtain ⟨hdead, haddrNe, hkindNe, hsizeNe, halignNe⟩ :=
    (tbm_deallocate_precheck_ub tbm ptr kind size align).2 id path alloc hprov halloc
  constructor
  · rintro ⟨tbm', hok⟩
    have hlive : alloc.live = true := by
      cases hl : alloc.live with
      | true => rfl
      | false => rw [hdead hl] at hok; cases hok
    have haddr : ptr.addr = alloc.addr := by
      rcases Decidable.em (ptr.addr = alloc.addr) with h | h
      · exact h
      · rw [haddrNe hlive h] at hok; cases hok
    have hkind : kind = alloc.kind := by
      rcases Decidable.em (kind = alloc.kind) with h | h
      · exact h
      · obtain ⟨msg, hmsg⟩ := hkindNe hlive haddr h
        rw [hmsg] at hok; cases hok
    have hsize : size = ⟨alloc.data.length⟩ := by
      rcases Decidable.em (size = ⟨alloc.data.length⟩) with h | h
      · exact h
      · rw [hsizeNe hlive haddr hkind h] at hok; cases hok
    have halign : align = alloc.align := by
      rcases Decidable.em (align = alloc.align) with h | h
      · exact h
      · rw [halignNe hlive haddr hkind hsize h] at hok; cases hok
    subst hkind hsize halign
    exact ⟨hlive, haddr, rfl, rfl, rfl, (deallocAllowedBool_iff path alloc.extra.root).mpr
      ((tbm_deallocate_ok_iff_pointwise tbm hwf ptr id path alloc hprov halloc hlive haddr).mp
        ⟨tbm', hok⟩)⟩
  · rintro ⟨hlive, haddr, hkind, hsize, halign, htable⟩
    subst hkind hsize halign
    exact (tbm_deallocate_ok_iff_pointwise tbm hwf ptr id path alloc hprov halloc hlive haddr).mpr
      ((deallocAllowedBool_iff path alloc.extra.root).mp htable)

/-! ### 4.10 Byte-Local Frame Laws, `<[T]>::get_mut` Disjoint Sub-Slices, & `TreeSimInvMulti` -/

/-- A read through a node holding `.Unprot .Disabled` on a byte of the accessed
window never succeeds (arbitrary tree, depth, and window). -/
theorem node_access_read_through_disabled_fails
    (t : Gen.Node) (qs : Gen.Path) (s : Gen.Node) (b o2 l2 : Nat)
    (hs : nodeAt t qs = some s) (hdis : s.permissions[b]? = some (.Unprot .Disabled))
    (h1 : o2 ≤ b) (h2 : b < o2 + l2) :
    ∀ t'', Node.access t (some qs) .Read ⟨o2⟩ ⟨l2⟩ ≠ .ok t'' := by
  intro t'' hrd
  obtain ⟨ps'', htr2⟩ := node_access_ok_inv .Read o2 l2 t t'' (some qs) hrd qs s hs
  obtain ⟨q0, q', hq0, hstep2⟩ := transitionRange_ok_inv (locRel (some qs) qs) .Read l2 o2
    s.permissions ps'' htr2 b h1 h2
  rw [hdis] at hq0
  cases hq0
  have hloc2 : locRel (some qs) qs = .Local := by unfold locRel; rw [c1_locOf_self qs]; rfl
  rw [hloc2] at hstep2
  cases hstep2

/-- **A foreign write kills every frozen reader on the written bytes (arbitrary
tree, depth, and windows)**: if a write access through `p` on `[off, off + len)`
succeeds on ANY borrow tree, then EVERY node `s` foreign to `p` that held
`.Unprot .Frozen` on a written byte `b` holds `.Unprot .Disabled` there
afterwards, and NO later read through `s` whose window contains `b` can
succeed. (An implicit `FnEntry` write of a standard `&mut [T]` retag is such an
access on the WHOLE retagged range.) -/
theorem node_access_foreign_write_kills_frozen_reader
    (t t' : Gen.Node) (p qs : Gen.Path) (s : Gen.Node) (off len b : Nat)
    (hacc : Node.access t (some p) .Write ⟨off⟩ ⟨len⟩ = .ok t')
    (hs : nodeAt t qs = some s) (hfor : locOf (some p) qs = false)
    (hb1 : off ≤ b) (hb2 : b < off + len)
    (hfrz : s.permissions[b]? = some (.Unprot .Frozen)) :
    (∃ s', nodeAt t' qs = some s' ∧ s'.permissions[b]? = some (.Unprot .Disabled)) ∧
    (∀ o2 l2, o2 ≤ b → b < o2 + l2 →
      ∀ t'', Node.access t' (some qs) .Read ⟨o2⟩ ⟨l2⟩ ≠ .ok t'') := by
  obtain ⟨s', hs', _, htr⟩ := (c1_access_node_of_nodeAt_ok hacc qs).1 s hs
  obtain ⟨_, _, hin⟩ := c1_transitionRange_ok_full (locRel (some p) qs) .Write off len
    s.permissions s'.permissions htr
  obtain ⟨p0, p', hp0, hstep, hp'⟩ := hin b hb1 hb2
  rw [hfrz] at hp0
  cases hp0
  have hloc : locRel (some p) qs = .Foreign := by unfold locRel; rw [hfor]; rfl
  rw [hloc] at hstep
  cases hstep
  exact ⟨⟨s', hs', hp'⟩, fun o2 l2 h1 h2 =>
    node_access_read_through_disabled_fails t' qs s' b o2 l2 hs' hp' h1 h2⟩

/-- **A foreign read never touches a frozen reader (arbitrary tree, depth, and
windows)**: after ANY successful read access through `p`, every node `s` foreign
to `p` keeps `.Unprot .Frozen` on every byte where it held it — so the read-only
`FnEntry` retag of a `#[rustc_no_writable]` `&mut [T]` leaves all sibling `&[T]`
readers intact, in contrast to `node_access_foreign_write_kills_frozen_reader`. -/
theorem node_access_foreign_read_preserves_frozen_reader
    (t t' : Gen.Node) (p qs : Gen.Path) (s : Gen.Node) (off len b : Nat)
    (hacc : Node.access t (some p) .Read ⟨off⟩ ⟨len⟩ = .ok t')
    (hs : nodeAt t qs = some s) (hfor : locOf (some p) qs = false)
    (hfrz : s.permissions[b]? = some (.Unprot .Frozen)) :
    ∃ s', nodeAt t' qs = some s' ∧ s'.permissions[b]? = some (.Unprot .Frozen) := by
  obtain ⟨s', hs', _, htr⟩ := (c1_access_node_of_nodeAt_ok hacc qs).1 s hs
  obtain ⟨_, hout, hin⟩ := c1_transitionRange_ok_full (locRel (some p) qs) .Read off len
    s.permissions s'.permissions htr
  refine ⟨s', hs', ?_⟩
  rcases Nat.lt_or_ge b off with h1 | h1
  · rw [hout b (Or.inl h1)]; exact hfrz
  · rcases Nat.lt_or_ge b (off + len) with h2 | h2
    · obtain ⟨p0, p', hp0, hstep, hp'⟩ := hin b h1 h2
      rw [hfrz] at hp0
      cases hp0
      have hloc : locRel (some p) qs = .Foreign := by unfold locRel; rw [hfor]; rfl
      rw [hloc] at hstep
      cases hstep
      exact hp'
    · rw [hout b (Or.inr h2)]; exact hfrz

/-- **Symbolic whole-tree sibling-reader theorem for the REAL
`TreeBorrowsMemory.retag_ptr` at `FnEntry` (`#[rustc_no_writable]` vs. standard
`&mut T` / `Box<T>`)**: on ANY live borrow tree of any depth, for ANY `&mut T` /
`Box<T>` pointee window `[off, off + len)` retagged through ANY
parent node, and ANY pre-existing node `s` that is foreign to the parent (a
sibling / cousin reader) and holds `.Unprot .Frozen` on a byte `b` of the window,
whenever the retag succeeds:
1. under the standard policy (`writableChildWrite`, the `FnEntry` implicit
   write) `s` holds `.Unprot .Disabled` on `b` IMMEDIATELY after the retag —
   for every byte of the retagged range — and no later tree read, hence no
   `TreeBorrowsMemory.load`, through `s` covering `b` can succeed;
2. under `#[rustc_no_writable]` (`rustcNoWritable`, read-only retag) `s` still
   holds `.Unprot .Frozen` on `b`. -/
theorem tbm_retag_ptr_fnEntry_frozen_reader_noWritable_vs_writable
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (frameExtra : Gen.TreeBorrowsFrameExtra)
    (ptr : Gen.Pointer Gen.TreeBorrowsProvenance)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable)
    (facts : ParamTypeFacts) (kind : RefParamKind) (attrs : ParamRetagAttrs)
    (hkind : kind ≠ .shared)
    (htbmParams : tbm.params = ⟨attrs.implicitWrites⟩)
    (id : Nat) (parentPath : Gen.Path)
    (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (pNode : Gen.Node)
    (off len align : Nat)
    (cells : List (Gen.Offset × LibSpecr.Size)) (mask : List Bool)
    (hmask : cellsToFreezeMask cells ⟨len⟩ = .ok mask)
    (hprov : ptr.thin_pointer.provenance = some (⟨(id : Int)⟩, parentPath))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (hoff : ptr.thin_pointer.addr - alloc.addr = (off : Int))
    (hbound : off + len ≤ alloc.data.length)
    (hpNode : nodeAt alloc.extra.root parentPath = some pNode)
    (qs : Gen.Path) (s : Gen.Node) (hs : nodeAt alloc.extra.root qs = some s)
    (hfor : locOf (some parentPath) qs = false)
    (b : Nat) (hb1 : off ≤ b) (hb2 : b < off + len)
    (hfrz : s.permissions[b]? = some (.Unprot .Frozen))
    (r : Gen.Pointer Gen.TreeBorrowsProvenance × Gen.TreeBorrowsMemory Gen.x86_64 ×
      Gen.TreeBorrowsFrameExtra)
    (hret : TreeBorrowsMemory.retag_ptr tbm frameExtra ptr
      (ptrTypeOfParamKind kind (pointeeInfoOfFacts facts len align cells)) true
      (!attrs.rustcNoWritable) lookup = .ok r) :
    (selectFnEntryPolicy facts kind attrs = .writableChildWrite →
      ∃ root' s',
        r.2.1.mem.allocations[id]? = some { alloc with extra := { root := root' } } ∧
        nodeAt root' qs = some s' ∧
        s'.permissions[b]? = some (.Unprot .Disabled) ∧
        (∀ o2 l2, o2 ≤ b → b < o2 + l2 →
          ∀ t'', Node.access root' (some qs) .Read ⟨o2⟩ ⟨l2⟩ ≠ .ok t'') ∧
        (∀ (ptrS : Gen.ThinPointer Gen.TreeBorrowsProvenance) (o2 l2 : Nat) (al2 : LibSpecr.Align),
          ptrS.provenance = some (⟨(id : Int)⟩, qs) →
          Align.is_aligned al2 ptrS.addr = true →
          ptrS.addr - alloc.addr = (o2 : Int) → l2 ≠ 0 → o2 + l2 ≤ alloc.data.length →
          o2 ≤ b → b < o2 + l2 →
          ∀ res, TreeBorrowsMemory.load r.2.1 ptrS ⟨l2⟩ al2 ≠ .ok res)) ∧
    (selectFnEntryPolicy facts kind attrs = .rustcNoWritable →
      ∃ root' s',
        r.2.1.mem.allocations[id]? = some { alloc with extra := { root := root' } } ∧
        nodeAt root' qs = some s' ∧
        s'.permissions[b]? = some (.Unprot .Frozen)) := by
  have hmaskLen : mask.length = len := a1_cellsToFreezeMask_length hmask
  have hsettings := reborrowSettings_fnEntry_mutOrBox_eq_policy lookup ptr facts kind attrs hkind
    len align cells mask hmask
  rw [← htbmParams] at hsettings
  have hidlt : id < tbm.mem.allocations.length := (List.getElem?_eq_some_iff.mp halloc).1
  have hcore : ∀ (pInit pRes : Gen.Permission) (k : Gen.AccessKind) (prot : Gen.Protected),
      Permission.init_access pInit = some k →
      Permission.matches_protector pInit prot = true →
      Permission.matches_protector (.Prot (.Reserved false false)) prot = true →
      Permission.transition (.Unprot .Frozen) k .Foreign = .ok pRes →
      ReborrowSettings.new lookup ptr
        (ptrTypeOfParamKind kind (pointeeInfoOfFacts facts len align cells)) true tbm.params
        (!attrs.rustcNoWritable) =
        .ok (some { inside := List.replicate len pInit, outside := .Prot (.Reserved false false),
                    «protected» := prot }) →
      ∃ root' s',
        r.2.1.mem.allocations[id]? = some { alloc with extra := { root := root' } } ∧
        nodeAt root' qs = some s' ∧ s'.permissions[b]? = some pRes := by
    intro pInit pRes k prot hinitK hmpInit hmpOut hres hnew
    have hsLen : (List.replicate len pInit).length = len := List.length_replicate
    obtain ⟨root1, hadd, hreb⟩ := tbm_reborrow_eq tbm ptr.thin_pointer
      { inside := List.replicate len pInit, outside := .Prot (.Reserved false false),
        «protected» := prot } frameExtra id parentPath alloc pNode off hprov halloc hlive hoff
      (by rw [hsLen]; exact hbound) hpNode hmpOut
      (fun p hp => by rw [List.eq_of_mem_replicate hp]; exact hmpInit)
    obtain ⟨root1', hadd', _, hexist1, _⟩ := node_add_node_spec alloc.extra.root pNode
      ⟨[], reborrowChildPerms alloc.data.length off (.Prot (.Reserved false false))
        (List.replicate len pInit), prot⟩ parentPath hpNode rfl
    rw [hadd] at hadd'
    cases hadd'
    obtain ⟨m1, hm1, hm1ps, _⟩ := hexist1 qs s hs
    unfold TreeBorrowsMemory.retag_ptr at hret
    rw [hnew] at hret
    simp only [bind, Except.bind, hreb] at hret
    cases hinit : TreeBorrowsMemory.reborrowInitAccess (parentPath ++ [(pNode.children.length : Int)])
        ⟨off⟩ 0 (List.replicate len pInit) root1 with
    | error e =>
      rw [hinit] at hret
      cases hret
    | ok root2 =>
      rw [hinit] at hret
      dsimp only [pure, Except.pure] at hret
      cases hret
      have hpw := reborrowInitAccess_ok_inv (parentPath ++ [(pNode.children.length : Int)]) off
        (List.replicate len pInit) 0 root1 root2 hinit
      obtain ⟨root2', hinit', hpost⟩ := reborrowInitAccess_ok_of_pointwise
        (parentPath ++ [(pNode.children.length : Int)]) off (List.replicate len pInit) 0 root1 hpw
      rw [hinit] at hinit'
      cases hinit'
      obtain ⟨m2, hm2, _, _, _, hin⟩ := (hpost qs).2 m1 hm1
      have hb' : b - off < (List.replicate len pInit).length := by rw [hsLen]; omega
      have hpm : (List.replicate len pInit)[b - off]? = some pInit :=
        nwsr_getElem?_replicate_lt (by omega)
      have hidx : off + 0 + (b - off) = b := by omega
      have hpb : m1.permissions[off + 0 + (b - off)]? = some (.Unprot .Frozen) := by
        rw [hidx, hm1ps]; exact hfrz
      have h := hin (b - off) hb' pInit hpm (.Unprot .Frozen) hpb
      rw [hinitK] at h
      obtain ⟨p', htr, hget⟩ := h
      have hlocF : locRel (some (parentPath ++ [(pNode.children.length : Int)])) qs = .Foreign := by
        unfold locRel
        rw [locOf_childPath_eq_parentPath alloc.extra.root parentPath qs pNode s hpNode hs, hfor]
        rfl
      rw [hlocF, hres] at htr
      cases htr
      rw [hidx] at hget
      exact ⟨root2, m2, List.getElem?_set_self hidlt, hm2, hget⟩
  have hProtYes : Protected.yes (if kind = .box then Gen.Protected.Weak else .Strong) = true := by
    split <;> rfl
  refine ⟨fun hpol => ?_, fun hpol => ?_⟩
  · have hnew := hsettings
    rw [hpol, hmaskLen] at hnew
    obtain ⟨root', s', hal, hs', hpb⟩ := hcore (.Prot .Unique) (.Unprot .Disabled) .Write _
      rfl (by simp [Permission.matches_protector, hProtYes])
      (by simp [Permission.matches_protector, hProtYes]) rfl hnew
    refine ⟨root', s', hal, hs', hpb,
      fun o2 l2 h1 h2 => node_access_read_through_disabled_fails root' qs s' b o2 l2
        hs' hpb h1 h2, ?_⟩
    intro ptrS o2 l2 al2 hprovS halS hoffS hl2 hbd h1 h2 res hload
    rw [tbm_load_eq_node_access r.2.1 ptrS l2 al2 id qs
      { alloc with extra := { root := root' } } o2 hprovS hal hlive halS hoffS hl2 hbd] at hload
    obtain ⟨root'', hacc, _⟩ := nwsr_bind_ok hload
    exact node_access_read_through_disabled_fails root' qs s' b o2 l2 hs' hpb h1 h2 root'' hacc
  · have hnew := hsettings
    rw [hpol, hmaskLen] at hnew
    exact hcore (.Prot (.Reserved false false)) (.Unprot .Frozen) .Read _
      rfl (by simp [Permission.matches_protector, hProtYes])
      (by simp [Permission.matches_protector, hProtYes]) rfl hnew

/-- **Byte-local frame law for `Node.access`**: a tree access on `[off, off + len)`
preserves every node's protector, permission-list length, and EVERY byte outside
`[off, off + len)`. -/
theorem node_access_frame_outside (t t' : Gen.Node) (path : Option Gen.Path)
    (k : Gen.AccessKind) (off len : Nat)
    (hacc : Node.access t path k ⟨off⟩ ⟨len⟩ = .ok t') :
    ∀ q m, nodeAt t q = some m →
      ∃ m', nodeAt t' q = some m' ∧ m'.«protected» = m.«protected» ∧
        m'.permissions.length = m.permissions.length ∧
        ∀ b, b < off ∨ off + len ≤ b → m'.permissions[b]? = m.permissions[b]? := by
  have hpost := c1_access_node_of_nodeAt_ok hacc
  intro q m hm
  obtain ⟨m', hm', hprot', htr⟩ := (hpost q).1 m hm
  obtain ⟨hlen, hout, _⟩ := c1_transitionRange_ok_full (locRel path q) k off len
    m.permissions m'.permissions htr
  exact ⟨m', hm', hprot', hlen, hout⟩

private theorem c1_transitionRange_comm_of_disjoint
    (r1 r2 : Gen.NodeRelation) (k1 k2 : Gen.AccessKind) (o1 l1 o2 l2 : Nat)
    (hdisj : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) (ps ps1 ps12 : List Gen.Permission)
    (h1 : Node.transitionRange r1 k1 o1 l1 ps = .ok ps1)
    (h2 : Node.transitionRange r2 k2 o2 l2 ps1 = .ok ps12) :
    ∃ ps2, Node.transitionRange r2 k2 o2 l2 ps = .ok ps2 ∧
      Node.transitionRange r1 k1 o1 l1 ps2 = .ok ps12 := by
  obtain ⟨hlen1, hout1, hin1⟩ := c1_transitionRange_ok_full r1 k1 o1 l1 ps ps1 h1
  obtain ⟨hlen12, hout12, hin12⟩ := c1_transitionRange_ok_full r2 k2 o2 l2 ps1 ps12 h2
  have hdisj2 : ∀ b, o2 ≤ b → b < o2 + l2 → b < o1 ∨ o1 + l1 ≤ b := by
    intro b hb1 hb2
    rcases hdisj with hd | hd
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hdisj1 : ∀ b, o1 ≤ b → b < o1 + l1 → b < o2 ∨ o2 + l2 ≤ b := by
    intro b hb1 hb2
    rcases hdisj with hd | hd
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hp2 : ∀ b, o2 ≤ b → b < o2 + l2 →
      ∃ p p', ps[b]? = some p ∧ Permission.transition p k2 r2 = .ok p' := by
    intro b hb1 hb2
    obtain ⟨p, p', hp1, htr, _⟩ := hin12 b hb1 hb2
    rw [hout1 b (hdisj2 b hb1 hb2)] at hp1
    exact ⟨p, p', hp1, htr⟩
  obtain ⟨ps2, hrun2, hlen2, hout2, hin2⟩ :=
    transitionRange_ok_of_pointwise r2 k2 l2 o2 ps hp2
  have hp1 : ∀ b, o1 ≤ b → b < o1 + l1 →
      ∃ p p', ps2[b]? = some p ∧ Permission.transition p k1 r1 = .ok p' := by
    intro b hb1 hb2
    obtain ⟨p, p', hp, htr, _⟩ := hin1 b hb1 hb2
    rw [hout2 b (hdisj1 b hb1 hb2)]
    exact ⟨p, p', hp, htr⟩
  obtain ⟨ps21, hrun21, hlen21, hout21, hin21⟩ :=
    transitionRange_ok_of_pointwise r1 k1 l1 o1 ps2 hp1
  have heq : ps21 = ps12 := by
    apply List.ext_getElem?
    intro b
    rcases c1_in_or_out o1 l1 b with ⟨h1a, h1b⟩ | h1out
    · have h2out := hdisj1 b h1a h1b
      obtain ⟨p, p', hp, htr, hp1'⟩ := hin1 b h1a h1b
      have hps2b : ps2[b]? = some p := by rw [hout2 b h2out]; exact hp
      obtain ⟨p'', htr'', hp21'⟩ := hin21 b h1a h1b p hps2b
      rw [htr] at htr''
      cases htr''
      rw [hp21', hout12 b h2out, hp1']
    · rcases c1_in_or_out o2 l2 b with ⟨h2a, h2b⟩ | h2out
      · obtain ⟨p, p', hp1b, htr, hp12'⟩ := hin12 b h2a h2b
        rw [hout1 b h1out] at hp1b
        obtain ⟨p'', htr'', hp2'⟩ := hin2 b h2a h2b p hp1b
        rw [htr] at htr''
        cases htr''
        rw [hout21 b h1out, hp2', hp12']
      · rw [hout21 b h1out, hout2 b h2out, hout12 b h2out, hout1 b h1out]
  rw [heq] at hrun21
  exact ⟨ps2, hrun2, hrun21⟩

private theorem c1_transitionRange_disjoint_err_imp
    (r1 r2 : Gen.NodeRelation) (k1 k2 : Gen.AccessKind) (o1 l1 o2 l2 : Nat)
    (hdisj : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) (ps ps1 : List Gen.Permission) (e : Stop)
    (h1 : Node.transitionRange r1 k1 o1 l1 ps = .ok ps1) :
    Node.transitionRange r2 k2 o2 l2 ps1 = .error e →
      Node.transitionRange r2 k2 o2 l2 ps = .error e := by
  obtain ⟨hlen1, hout1, _⟩ := c1_transitionRange_ok_full r1 k1 o1 l1 ps ps1 h1
  have hgen : ∀ (rem off : Nat), (∀ b, off ≤ b → b < off + rem → b < o1 ∨ o1 + l1 ≤ b) →
      ∀ (a b_list : List Gen.Permission),
        a.length = b_list.length →
        (∀ i, off ≤ i → i < off + rem → a[i]? = b_list[i]?) →
        Node.transitionRange r2 k2 off rem a = .error e →
        Node.transitionRange r2 k2 off rem b_list = .error e := by
    intro rem
    induction rem with
    | zero => intro _ _ _ _ _ _ h; cases h
    | succ rem ih =>
      intro off hrange a b_list hlen hagree herr
      unfold Node.transitionRange at herr ⊢
      cases ha : a[off]? with
      | none =>
        have hb : b_list[off]? = none := by rw [← hagree off (Nat.le_refl _) (by omega), ha]
        have hltA : ¬ off < a.length := by
          intro hlt; rw [List.getElem?_eq_getElem hlt] at ha; cases ha
        have hltB : ¬ off < b_list.length := by omega
        unfold listMutateAt listIndex at herr ⊢
        simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, Int.toNat_natCast, ↓reduceIte,
          ha, hb, bind, Except.bind] at herr ⊢
        exact herr
      | some p =>
        have hb : b_list[off]? = some p := by rw [← hagree off (Nat.le_refl _) (by omega), ha]
        rw [Int.ofNat_eq_natCast, a1_listMutateAt_natCast a off _ _ p ha] at herr
        rw [Int.ofNat_eq_natCast, a1_listMutateAt_natCast b_list off _ _ p hb]
        dsimp only [bind, Except.bind, pure, Except.pure] at herr ⊢
        cases htr : Permission.transition p k2 r2 with
        | error e0 =>
          rw [htr] at herr
          exact herr
        | ok p' =>
          rw [htr] at herr
          dsimp only at herr ⊢
          exact ih (off + 1) (fun i h1' h2' => hrange i (by omega) (by omega))
            (a.set off p') (b_list.set off p')
            (by rw [List.length_set, List.length_set, hlen])
            (fun i h1' h2' => by
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              exact hagree i (by omega) (by omega))
            herr
  exact hgen l2 o2
    (fun b h1' h2' => by
      rcases hdisj with hd | hd
      · exact Or.inr (by omega)
      · exact Or.inl (by omega))
    ps1 ps hlen1
    (fun b h1' h2' => hout1 b (by
      rcases hdisj with hd | hd
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)))

mutual

private theorem c1_node_access_comm_ok (o1 l1 o2 l2 : Nat)
    (hdisj : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) (k1 k2 : Gen.AccessKind) :
    ∀ (t t1 t12 : Gen.Node) (p1 p2 : Option Gen.Path),
      Node.access t p1 k1 ⟨o1⟩ ⟨l1⟩ = .ok t1 →
      Node.access t1 p2 k2 ⟨o2⟩ ⟨l2⟩ = .ok t12 →
      ∃ t2, Node.access t p2 k2 ⟨o2⟩ ⟨l2⟩ = .ok t2 ∧
        Node.access t2 p1 k1 ⟨o1⟩ ⟨l1⟩ = .ok t12
  | ⟨cs, ps, pr⟩, t1, t12, p1, p2, h1, h2 => by
    rw [nwsr_access_eq] at h1
    obtain ⟨ps1, hps1, h1⟩ := nwsr_bind_ok h1
    obtain ⟨cs1, hcs1, h1⟩ := nwsr_bind_ok h1
    cases h1
    rw [nwsr_access_eq] at h2
    obtain ⟨ps12, hps12, h2⟩ := nwsr_bind_ok h2
    obtain ⟨cs12, hcs12, h2⟩ := nwsr_bind_ok h2
    cases h2
    obtain ⟨ps2, hps2, hps21⟩ := c1_transitionRange_comm_of_disjoint
      (locRel p1 []) (locRel p2 []) k1 k2 o1 l1 o2 l2 hdisj ps ps1 ps12 hps1 hps12
    obtain ⟨cs2, hcs2, hcs21⟩ := c1_accessChildren_comm_ok o1 l1 o2 l2 hdisj k1 k2
      cs cs1 cs12 0 p1 p2 hcs1 hcs12
    refine ⟨⟨cs2, ps2, pr⟩, ?_, ?_⟩
    · rw [nwsr_access_eq, hps2]
      show (Node.accessChildren 0 p2 k2 ⟨o2⟩ ⟨l2⟩ cs >>= _) = _
      rw [hcs2]; rfl
    · rw [nwsr_access_eq, hps21]
      show (Node.accessChildren 0 p1 k1 ⟨o1⟩ ⟨l1⟩ cs2 >>= _) = _
      rw [hcs21]; rfl

private theorem c1_accessChildren_comm_ok (o1 l1 o2 l2 : Nat)
    (hdisj : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) (k1 k2 : Gen.AccessKind) :
    ∀ (cs cs1 cs12 : List Gen.Node) (cid : Int) (p1 p2 : Option Gen.Path),
      Node.accessChildren cid p1 k1 ⟨o1⟩ ⟨l1⟩ cs = .ok cs1 →
      Node.accessChildren cid p2 k2 ⟨o2⟩ ⟨l2⟩ cs1 = .ok cs12 →
      ∃ cs2, Node.accessChildren cid p2 k2 ⟨o2⟩ ⟨l2⟩ cs = .ok cs2 ∧
        Node.accessChildren cid p1 k1 ⟨o1⟩ ⟨l1⟩ cs2 = .ok cs12
  | [], cs1, cs12, cid, p1, p2, h1, h2 => by
    rw [Node.accessChildren] at h1; cases h1
    rw [Node.accessChildren] at h2; cases h2
    exact ⟨[], by rw [Node.accessChildren]; rfl, by rw [Node.accessChildren]; rfl⟩
  | c :: rest, cs1, cs12, cid, p1, p2, h1, h2 => by
    rw [c1_accessChildren_cons] at h1
    obtain ⟨c1, hc1, h1⟩ := nwsr_bind_ok h1
    obtain ⟨r1, hr1, h1⟩ := nwsr_bind_ok h1
    cases h1
    rw [c1_accessChildren_cons] at h2
    obtain ⟨c12, hc12, h2⟩ := nwsr_bind_ok h2
    obtain ⟨r12, hr12, h2⟩ := nwsr_bind_ok h2
    cases h2
    obtain ⟨c2, hc2, hc21⟩ := c1_node_access_comm_ok o1 l1 o2 l2 hdisj k1 k2
      c c1 c12 (subPathAt p1 cid) (subPathAt p2 cid) hc1 hc12
    obtain ⟨r2, hr2, hr21⟩ := c1_accessChildren_comm_ok o1 l1 o2 l2 hdisj k1 k2
      rest r1 r12 (cid + 1) p1 p2 hr1 hr12
    refine ⟨c2 :: r2, ?_, ?_⟩
    · rw [c1_accessChildren_cons, hc2]
      show (Node.accessChildren (cid + 1) p2 k2 ⟨o2⟩ ⟨l2⟩ rest >>= _) = _
      rw [hr2]; rfl
    · rw [c1_accessChildren_cons, hc21]
      show (Node.accessChildren (cid + 1) p1 k1 ⟨o1⟩ ⟨l1⟩ r2 >>= _) = _
      rw [hr21]; rfl

end

mutual

private theorem c1_node_access_disjoint_err (o1 l1 o2 l2 : Nat)
    (hdisj : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) (k1 k2 : Gen.AccessKind) :
    ∀ (t t1 : Gen.Node) (p1 p2 : Option Gen.Path) (e : Stop),
      Node.access t p1 k1 ⟨o1⟩ ⟨l1⟩ = .ok t1 →
      (Node.access t1 p2 k2 ⟨o2⟩ ⟨l2⟩ = .error e ↔
        Node.access t p2 k2 ⟨o2⟩ ⟨l2⟩ = .error e)
  | ⟨cs, ps, pr⟩, t1, p1, p2, e, h1 => by
    rw [nwsr_access_eq] at h1
    obtain ⟨ps1, hps1, h1⟩ := nwsr_bind_ok h1
    obtain ⟨cs1, hcs1, h1⟩ := nwsr_bind_ok h1
    cases h1
    have hpsErr : ∀ e0, Node.transitionRange (locRel p2 []) k2 o2 l2 ps1 = .error e0 ↔
        Node.transitionRange (locRel p2 []) k2 o2 l2 ps = .error e0 := by
      intro e0
      constructor
      · exact c1_transitionRange_disjoint_err_imp _ _ k1 k2 o1 l1 o2 l2 hdisj ps ps1 e0 hps1
      · intro herr
        cases htr1 : Node.transitionRange (locRel p2 []) k2 o2 l2 ps1 with
        | ok ps12 =>
          obtain ⟨ps2, hrun2, _⟩ := c1_transitionRange_comm_of_disjoint
            (locRel p1 []) (locRel p2 []) k1 k2 o1 l1 o2 l2 hdisj ps ps1 ps12 hps1 htr1
          rw [herr] at hrun2; cases hrun2
        | error e1 =>
          have h1' := c1_transitionRange_disjoint_err_imp _ _ k1 k2 o1 l1 o2 l2 hdisj ps ps1 e1
            hps1 htr1
          rw [herr] at h1'
          cases h1'
          rfl
    have hcsErr := c1_accessChildren_disjoint_err o1 l1 o2 l2 hdisj k1 k2 cs cs1 0 p1 p2 e hcs1
    rw [nwsr_access_eq, nwsr_access_eq]
    cases hp : Node.transitionRange (locRel p2 []) k2 o2 l2 ps with
    | error e0 =>
      rw [(hpsErr e0).mpr hp]
      rfl
    | ok ps2 =>
      cases hp1 : Node.transitionRange (locRel p2 []) k2 o2 l2 ps1 with
      | error e0 =>
        have hbad := (hpsErr e0).mp hp1
        rw [hp] at hbad; cases hbad
      | ok ps12 =>
        dsimp only [bind, Except.bind, pure, Except.pure]
        cases hc1 : Node.accessChildren 0 p2 k2 ⟨o2⟩ ⟨l2⟩ cs1 with
        | error e1 =>
          have hc0 := (c1_accessChildren_disjoint_err o1 l1 o2 l2 hdisj k1 k2 cs cs1 0 p1 p2 e1
            hcs1).mp hc1
          rw [hc0]
        | ok cs12 =>
          cases hc0 : Node.accessChildren 0 p2 k2 ⟨o2⟩ ⟨l2⟩ cs with
          | ok cs2 => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
          | error e0 =>
            have hbad := (c1_accessChildren_disjoint_err o1 l1 o2 l2 hdisj k1 k2 cs cs1 0 p1 p2 e0
              hcs1).mpr hc0
            rw [hc1] at hbad; cases hbad

private theorem c1_accessChildren_disjoint_err (o1 l1 o2 l2 : Nat)
    (hdisj : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) (k1 k2 : Gen.AccessKind) :
    ∀ (cs cs1 : List Gen.Node) (cid : Int) (p1 p2 : Option Gen.Path) (e : Stop),
      Node.accessChildren cid p1 k1 ⟨o1⟩ ⟨l1⟩ cs = .ok cs1 →
      (Node.accessChildren cid p2 k2 ⟨o2⟩ ⟨l2⟩ cs1 = .error e ↔
        Node.accessChildren cid p2 k2 ⟨o2⟩ ⟨l2⟩ cs = .error e)
  | [], cs1, cid, p1, p2, e, h1 => by
    rw [Node.accessChildren] at h1; cases h1
    rfl
  | c :: rest, cs1, cid, p1, p2, e, h1 => by
    rw [c1_accessChildren_cons] at h1
    obtain ⟨c1, hc1, h1⟩ := nwsr_bind_ok h1
    obtain ⟨r1, hr1, h1⟩ := nwsr_bind_ok h1
    cases h1
    rw [c1_accessChildren_cons, c1_accessChildren_cons]
    cases ha0 : Node.access c (subPathAt p2 cid) k2 ⟨o2⟩ ⟨l2⟩ with
    | error e0 =>
      have ha1 := (c1_node_access_disjoint_err o1 l1 o2 l2 hdisj k1 k2 c c1
        (subPathAt p1 cid) (subPathAt p2 cid) e0 hc1).mpr ha0
      rw [ha1]; rfl
    | ok c2 =>
      cases ha1 : Node.access c1 (subPathAt p2 cid) k2 ⟨o2⟩ ⟨l2⟩ with
      | error e0 =>
        have hbad := (c1_node_access_disjoint_err o1 l1 o2 l2 hdisj k1 k2 c c1
          (subPathAt p1 cid) (subPathAt p2 cid) e0 hc1).mp ha1
        rw [ha0] at hbad; cases hbad
      | ok c12 =>
        dsimp only [bind, Except.bind, pure, Except.pure]
        cases hr0 : Node.accessChildren (cid + 1) p2 k2 ⟨o2⟩ ⟨l2⟩ rest with
        | error e0 =>
          have hr1' := (c1_accessChildren_disjoint_err o1 l1 o2 l2 hdisj k1 k2 rest r1 (cid + 1)
            p1 p2 e0 hr1).mpr hr0
          rw [hr1']
        | ok r2 =>
          cases hr1' : Node.accessChildren (cid + 1) p2 k2 ⟨o2⟩ ⟨l2⟩ r1 with
          | ok r12 => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
          | error e0 =>
            have hbad := (c1_accessChildren_disjoint_err o1 l1 o2 l2 hdisj k1 k2 rest r1 (cid + 1)
              p1 p2 e0 hr1).mp hr1'
            rw [hr0] at hbad; cases hbad

end

/-- **Disjoint-range commutativity & error invariance of `Node.access`**: for ANY
borrow tree `t`, ANY two paths `p1, p2`, ANY access kinds `k1, k2`, and ANY two
disjoint byte windows `[o1, o1 + l1)` and `[o2, o2 + l2)`:
1. executing `p1` then `p2` succeeds **iff** executing `p2` then `p1` succeeds,
   yielding the **identical** post-tree `t12`;
2. whenever the first access `p1` succeeds (`t1`), the second access `p2` raises
   the exact same error `e` on `t1` as on `t`. -/
theorem node_access_comm_of_disjoint (t : Gen.Node) (p1 p2 : Option Gen.Path)
    (k1 k2 : Gen.AccessKind) (o1 l1 o2 l2 : Nat)
    (hdisj : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) :
    (∀ t1 t12, Node.access t p1 k1 ⟨o1⟩ ⟨l1⟩ = .ok t1 →
      Node.access t1 p2 k2 ⟨o2⟩ ⟨l2⟩ = .ok t12 →
      ∃ t2, Node.access t p2 k2 ⟨o2⟩ ⟨l2⟩ = .ok t2 ∧
        Node.access t2 p1 k1 ⟨o1⟩ ⟨l1⟩ = .ok t12) ∧
    (∀ t1, Node.access t p1 k1 ⟨o1⟩ ⟨l1⟩ = .ok t1 →
      ∀ e, Node.access t1 p2 k2 ⟨o2⟩ ⟨l2⟩ = .error e ↔
        Node.access t p2 k2 ⟨o2⟩ ⟨l2⟩ = .error e) :=
  ⟨fun t1 t12 h1 h2 => c1_node_access_comm_ok o1 l1 o2 l2 hdisj k1 k2 t t1 t12 p1 p2 h1 h2,
   fun t1 h1 e => c1_node_access_disjoint_err o1 l1 o2 l2 hdisj k1 k2 t t1 p1 p2 e h1⟩

private theorem c1_releaseProtectorPermissions_frame
    (r : Gen.NodeRelation) :
    ∀ (accesses : List (Option Gen.AccessKind)) (off : Nat) (ps ps' : List Gen.Permission),
      Node.releaseProtectorPermissions r off accesses ps = .ok ps' →
      ps'.length = ps.length ∧
      (∀ b, (b < off ∨ accesses[b - off]? = some none ∨ accesses[b - off]? = none) →
        ps'[b]? = ps[b]?)
  | [], _, ps, ps', h => by
    cases h
    exact ⟨rfl, fun _ _ => rfl⟩
  | none :: rest, off, ps, ps', h => by
    obtain ⟨hlen, hout⟩ := c1_releaseProtectorPermissions_frame r rest (off + 1) ps ps' h
    refine ⟨hlen, fun b hb => ?_⟩
    apply hout b
    rcases hb with hlt | hsome | hnone
    · exact Or.inl (by omega)
    · by_cases hbo : b = off
      · exact Or.inl (by omega)
      · rcases Nat.lt_or_ge b off with hlt | hge
        · exact Or.inl (by omega)
        · have hsub : b - off = (b - (off + 1)) + 1 := by omega
          rw [hsub, List.getElem?_cons_succ] at hsome
          exact Or.inr (Or.inl hsome)
    · by_cases hbo : b = off
      · exact Or.inl (by omega)
      · rcases Nat.lt_or_ge b off with hlt | hge
        · exact Or.inl (by omega)
        · have hsub : b - off = (b - (off + 1)) + 1 := by omega
          rw [hsub, List.getElem?_cons_succ] at hnone
          exact Or.inr (Or.inr hnone)
  | some k :: rest, off, ps, ps', h => by
    unfold Node.releaseProtectorPermissions at h
    obtain ⟨⟨_, ps1⟩, hmut, hrest⟩ := nwsr_bind_ok h
    cases hget : ps[off]? with
    | none =>
      unfold listMutateAt listIndex at hmut
      simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, Int.toNat_natCast, ↓reduceIte,
        hget, bind, Except.bind] at hmut
      cases hmut
    | some p =>
      rw [Int.ofNat_eq_natCast, a1_listMutateAt_natCast ps off _ _ p hget] at hmut
      obtain ⟨⟨_, p'⟩, htr, hmut⟩ := nwsr_bind_ok hmut
      cases hmut
      obtain ⟨hlen, hout⟩ := c1_releaseProtectorPermissions_frame r rest (off + 1)
        (ps.set off p') ps' hrest
      refine ⟨by rw [hlen, List.length_set], fun b hb => ?_⟩
      have hne : b ≠ off := by
        intro heq
        subst heq
        rcases hb with hlt | hsome | hnone
        · omega
        · simp at hsome
        · simp at hnone
      have hb' : b < off + 1 ∨ rest[b - (off + 1)]? = some none ∨
          rest[b - (off + 1)]? = none := by
        rcases hb with hlt | hsome | hnone
        · exact Or.inl (by omega)
        · rcases Nat.lt_or_ge b off with hlt | hge
          · exact Or.inl (by omega)
          · have hsub : b - off = (b - (off + 1)) + 1 := by omega
            rw [hsub, List.getElem?_cons_succ] at hsome
            exact Or.inr (Or.inl hsome)
        · rcases Nat.lt_or_ge b off with hlt | hge
          · exact Or.inl (by omega)
          · have hsub : b - off = (b - (off + 1)) + 1 := by omega
            rw [hsub, List.getElem?_cons_succ] at hnone
            exact Or.inr (Or.inr hnone)
      rw [hout b hb', List.getElem?_set_ne hne.symm]

mutual

/-- **Byte-local frame law for `Node.release_protector`**: every byte `b` where
`accesses[b]? = some none ∨ accesses[b]? = none` (in particular every byte outside
the released protector's inside range!) is untouched in **EVERY** node of the
borrow tree. -/
theorem node_release_protector_frame_outside (accesses : List (Option Gen.AccessKind)) :
    ∀ (t t' : Gen.Node) (path : Option Gen.Path),
      Node.release_protector t path accesses = .ok t' →
      ∀ q m, nodeAt t q = some m →
        ∃ m', nodeAt t' q = some m' ∧ m'.permissions.length = m.permissions.length ∧
          ∀ (b : Nat), (accesses[b]? = some none ∨ accesses[b]? = none) →
            m'.permissions[b]? = m.permissions[b]?
  | ⟨cs, ps, pr⟩, t', path, h, q, m, hm => by
    cases path with
    | some p =>
      cases p with
      | nil =>
        unfold Node.release_protector at h
        cases h
        cases q with
        | nil =>
          cases hm
          exact ⟨⟨cs, ps, .No⟩, rfl, rfl, fun _ _ => rfl⟩
        | cons i rest =>
          have hm' : nodeAt ⟨cs, ps, .No⟩ (i :: rest) = some m := by
            by_cases hi : 0 ≤ i
            · cases hc : cs[i.toNat]? with
              | none => rw [nwsr_nodeAt_cons_none _ _ _ i rest hi hc] at hm; cases hm
              | some c =>
                rw [nwsr_nodeAt_cons_some _ _ _ i rest c hi hc] at hm ⊢
                exact hm
            · rw [nwsr_nodeAt_cons_neg _ _ _ i rest hi] at hm; cases hm
          exact ⟨m, hm', rfl, fun _ _ => rfl⟩
      | cons hd tl =>
        unfold Node.release_protector at h
        obtain ⟨ps', hps', h⟩ := nwsr_bind_ok h
        obtain ⟨cs', hcs', h⟩ := nwsr_bind_ok h
        cases h
        obtain ⟨hlen, hout⟩ := c1_releaseProtectorPermissions_frame _ accesses 0 ps ps' hps'
        cases q with
        | nil =>
          cases hm
          exact ⟨⟨cs', ps', pr⟩, rfl, hlen, fun b hb => hout b (Or.inr (by simpa using hb))⟩
        | cons i rest =>
          by_cases hi : 0 ≤ i
          · cases hc : cs[i.toNat]? with
            | none => rw [nwsr_nodeAt_cons_none _ _ _ i rest hi hc] at hm; cases hm
            | some c =>
              rw [nwsr_nodeAt_cons_some _ _ _ i rest c hi hc] at hm
              obtain ⟨c', hc', m', hm', hlenM, houtM⟩ :=
                c1_releaseProtectorChildren_frame_outside accesses cs cs' 0 (some (hd :: tl))
                  hcs' i.toNat c hc rest m hm
              exact ⟨m', by rw [nwsr_nodeAt_cons_some _ _ _ i rest c' hi hc']; exact hm',
                hlenM, houtM⟩
          · rw [nwsr_nodeAt_cons_neg _ _ _ i rest hi] at hm; cases hm
    | none =>
      unfold Node.release_protector at h
      obtain ⟨ps', hps', h⟩ := nwsr_bind_ok h
      obtain ⟨cs', hcs', h⟩ := nwsr_bind_ok h
      cases h
      obtain ⟨hlen, hout⟩ := c1_releaseProtectorPermissions_frame _ accesses 0 ps ps' hps'
      cases q with
      | nil =>
        cases hm
        exact ⟨⟨cs', ps', pr⟩, rfl, hlen, fun b hb => hout b (Or.inr (by simpa using hb))⟩
      | cons i rest =>
        by_cases hi : 0 ≤ i
        · cases hc : cs[i.toNat]? with
          | none => rw [nwsr_nodeAt_cons_none _ _ _ i rest hi hc] at hm; cases hm
          | some c =>
            rw [nwsr_nodeAt_cons_some _ _ _ i rest c hi hc] at hm
            obtain ⟨c', hc', m', hm', hlenM, houtM⟩ :=
              c1_releaseProtectorChildren_frame_outside accesses cs cs' 0 none hcs'
                i.toNat c hc rest m hm
            exact ⟨m', by rw [nwsr_nodeAt_cons_some _ _ _ i rest c' hi hc']; exact hm',
              hlenM, houtM⟩
        · rw [nwsr_nodeAt_cons_neg _ _ _ i rest hi] at hm; cases hm

private theorem c1_releaseProtectorChildren_frame_outside
    (accesses : List (Option Gen.AccessKind)) :
    ∀ (cs cs' : List Gen.Node) (cid : Int) (path : Option Gen.Path),
      Node.releaseProtectorChildren cid path accesses cs = .ok cs' →
      ∀ (j : Nat) (c : Gen.Node), cs[j]? = some c →
        ∀ q m, nodeAt c q = some m →
          ∃ c', cs'[j]? = some c' ∧
            ∃ m', nodeAt c' q = some m' ∧ m'.permissions.length = m.permissions.length ∧
              ∀ (b : Nat), (accesses[b]? = some none ∨ accesses[b]? = none) →
                m'.permissions[b]? = m.permissions[b]?
  | [], _, _, _, _, _, _, hc, _, _, _ => by simp at hc
  | c0 :: rest, cs', cid, path, h, j, c, hc, q, m, hm => by
    unfold Node.releaseProtectorChildren at h
    obtain ⟨c0', hc0', h⟩ := nwsr_bind_ok h
    obtain ⟨rest', hrest', h⟩ := nwsr_bind_ok h
    cases h
    cases j with
    | zero =>
      rw [List.getElem?_cons_zero] at hc
      cases hc
      obtain ⟨m', hm', hlen, hout⟩ :=
        node_release_protector_frame_outside accesses c0 c0' _ hc0' q m hm
      exact ⟨c0', rfl, m', hm', hlen, hout⟩
    | succ j =>
      rw [List.getElem?_cons_succ] at hc
      obtain ⟨c', hc', m', hm', hlen, hout⟩ :=
        c1_releaseProtectorChildren_frame_outside accesses rest rest' (cid + 1) path hrest'
          j c hc q m hm
      exact ⟨c', by rw [List.getElem?_cons_succ]; exact hc', m', hm', hlen, hout⟩

end

/-- Sized freeze `Gen.PointeeInfo` for a contiguous slice window of `size` bytes
and alignment `align` (`Unpin`, `Freeze`, zero `UnsafeCell`s). -/
def slicePointeeInfoMR (size align : Nat) : Gen.PointeeInfo where
  layout := .Sized ⟨size⟩ ⟨align⟩
  inhabited := true
  unsafe_cells := .Sized []
  freeze := true
  unpin := true

private theorem c1_cellsToFreezeMask_nil (n : Nat) :
    cellsToFreezeMask [] ⟨n⟩ = .ok (List.replicate n true) := by
  have h1 : ¬ ((n : Int) - ((0 + 0 : Nat) : Int) < 0) := by omega
  have h2 : ((n : Int) - ((0 + 0 : Nat) : Int)).toNat = n := by omega
  unfold cellsToFreezeMask cellsToFreezeMaskLoop
  simp only [h1, h2, ↓reduceIte, List.replicate_zero, List.nil_append]
  unfold cellsToFreezeMaskLoop
  simp only [List.length_replicate, ne_eq, not_true_eq_false, ↓reduceIte,
    bind, Except.bind, pure, Except.pure]

private theorem c1_mapM_perm_const (f : Bool → Interp Gen.Permission)
    (p : Gen.Permission) (hf : f true = .ok p) :
    ∀ n, (List.replicate n true).mapM f = .ok (List.replicate n p)
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.replicate_succ, List.mapM_cons]
    simp only [hf, c1_mapM_perm_const f p hf n, bind, Except.bind, pure, Except.pure]

private theorem c1_reborrowSettings_slice_mut
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Gen.TreeBorrowsProvenance) (len align : Nat) (fnIw : Bool) :
    ReborrowSettings.new lookup ptr (.Ref .Mutable (slicePointeeInfoMR len align)) true
      ⟨true⟩ fnIw =
      .ok (some {
        inside := List.replicate len (if fnIw then .Prot .Unique else .Prot (.Reserved false false))
        outside := .Prot (.Reserved false false)
        «protected» := .Strong
      }) := by
  cases fnIw with
  | false =>
    simp only [ReborrowSettings.new, slicePointeeInfoMR, PtrType.safe_pointee,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, Protected.yes, Bool.and_false,
      UnsafeCellStrategy.freeze_mask, c1_cellsToFreezeMask_nil, bind, Except.bind, pure,
      Except.pure]
    rw [c1_mapM_perm_const _ (.Prot (.Reserved false false)) rfl len]
    rfl
  | true =>
    simp only [ReborrowSettings.new, slicePointeeInfoMR, PtrType.safe_pointee,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, Protected.yes, Bool.and_true,
      UnsafeCellStrategy.freeze_mask, c1_cellsToFreezeMask_nil, bind, Except.bind, pure,
      Except.pure]
    rw [c1_mapM_perm_const _ (.Prot .Unique) rfl len]
    rfl

private theorem c1_reborrowSettings_slice_shr
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable)
    (ptr : Gen.Pointer Gen.TreeBorrowsProvenance) (len align : Nat) (fnIw : Bool) :
    ReborrowSettings.new lookup ptr (.Ref .Immutable (slicePointeeInfoMR len align)) false
      ⟨true⟩ fnIw =
      .ok (some {
        inside := List.replicate len (.Unprot .Frozen)
        outside := .Unprot .Frozen
        «protected» := .No
      }) := by
  simp only [ReborrowSettings.new, slicePointeeInfoMR, PtrType.safe_pointee,
    Bool.false_eq_true, ↓reduceIte, Protected.yes, UnsafeCellStrategy.freeze_mask,
    c1_cellsToFreezeMask_nil, bind, Except.bind, pure, Except.pure]
  rw [c1_mapM_perm_const _ (.Unprot .Frozen) rfl len]
  rfl

private theorem c1_windowPerms_getElem? (n off len : Nat) (outP inP : Gen.Permission)
    (hb : off + len ≤ n) (b : Nat) (hbn : b < n) :
    (List.replicate off outP ++ List.replicate len inP ++
      List.replicate (n - (off + len)) outP)[b]? =
      some (if off ≤ b ∧ b < off + len then inP else outP) := by
  have hl1 : (List.replicate off outP).length = off := List.length_replicate
  have hl2 : (List.replicate len inP).length = len := List.length_replicate
  have hl12 : (List.replicate off outP ++ List.replicate len inP).length = off + len := by
    rw [List.length_append, hl1, hl2]
  rcases Nat.lt_or_ge b off with h1 | h1
  · have hn : ¬ (off ≤ b ∧ b < off + len) := by omega
    simp only [hn, ↓reduceIte]
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    exact nwsr_getElem?_replicate_lt h1
  · rcases Nat.lt_or_ge b (off + len) with h2 | h2
    · simp only [h1, h2, and_self, ↓reduceIte]
      rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega)]
      exact nwsr_getElem?_replicate_lt (by omega)
    · have hn : ¬ (off ≤ b ∧ b < off + len) := by omega
      simp only [hn, ↓reduceIte]
      rw [List.getElem?_append_right (by omega)]
      exact nwsr_getElem?_replicate_lt (by omega)

private theorem c1_reborrowInitAccess_const_ok
    (childPath : Gen.Path) (off : Nat) (inP : Gen.Permission) (k : Gen.AccessKind)
    (hinit : Permission.init_access inP = some k) :
    ∀ (m idx : Nat) (t : Gen.Node) (P : Nat → Gen.Node → Prop),
      P idx t →
      (∀ i ti, idx ≤ i → i < idx + m → P i ti →
        ∃ ti', Node.access ti (some childPath) k ⟨off + i⟩ ⟨1⟩ = .ok ti' ∧ P (i + 1) ti') →
      ∃ t', TreeBorrowsMemory.reborrowInitAccess childPath ⟨off⟩ idx (List.replicate m inP) t =
        .ok t' ∧ P (idx + m) t'
  | 0, idx, t, P, hP, _ => ⟨t, rfl, hP⟩
  | m + 1, idx, t, P, hP, hstep => by
    obtain ⟨t1, hacc, hP1⟩ := hstep idx t (Nat.le_refl _) (by omega) hP
    obtain ⟨t', hrest, hP'⟩ := c1_reborrowInitAccess_const_ok childPath off inP k hinit m (idx + 1)
      t1 P hP1 (fun i ti h1 h2 => hstep i ti (by omega) (by omega))
    refine ⟨t', ?_, ?_⟩
    · show (match Permission.init_access inP with
        | some access => do
          let root' ← Node.access t (some childPath) access (Size.add ⟨off⟩ ⟨idx⟩) ⟨1⟩
          TreeBorrowsMemory.reborrowInitAccess childPath ⟨off⟩ (idx + 1) (List.replicate m inP) root'
        | none =>
          TreeBorrowsMemory.reborrowInitAccess childPath ⟨off⟩ (idx + 1) (List.replicate m inP) t) = _
      rw [hinit]
      show (Node.access t (some childPath) k ⟨off + idx⟩ ⟨1⟩ >>= fun root' =>
        TreeBorrowsMemory.reborrowInitAccess childPath ⟨off⟩ (idx + 1) (List.replicate m inP) root') = _
      rw [hacc]
      exact hrest
    · have e : idx + 1 + m = idx + (m + 1) := by omega
      rw [← e]; exact hP'

private theorem c1_add_node_root (cs : List Gen.Node) (ps : List Gen.Permission)
    (pr : Gen.Protected) (child : Gen.Node) :
    Node.add_node ⟨cs, ps, pr⟩ [] child =
      .ok ([(cs.length : Int)], ⟨cs ++ [child], ps, pr⟩) := by
  unfold Node.add_node Node.access_node
  rfl

private theorem c1_reborrow_from_root
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int) (align : Nat)
    (cs : List Gen.Node) (off : Nat) (s : Gen.ReborrowSettings)
    (fe : Gen.TreeBorrowsFrameExtra)
    (hpos : 0 < s.inside.length) (hb : off + s.inside.length ≤ data.length)
    (hmatchOut : Permission.matches_protector s.outside s.«protected» = true)
    (hmatchIn : ∀ p ∈ s.inside, Permission.matches_protector p s.«protected» = true) :
    let tbm : Gen.TreeBorrowsMemory Gen.x86_64 :=
      { params := ⟨true⟩
        mem := {
          allocations := [{
            mkRootAllocTB data addr align .Stack with
            extra := { root := ⟨cs, List.replicate data.length (.Unprot .Unique), .No⟩ }
          }]
          _phantom := ⟨⟩ } }
    let childPerms :=
      (List.replicate data.length s.outside).take off ++ s.inside ++
        (List.replicate data.length s.outside).drop (off + s.inside.length)
    let childNode : Gen.Node := ⟨[], childPerms, s.«protected»⟩
    TreeBorrowsMemory.reborrow tbm { addr := addr + (off : Int), provenance := some (⟨0⟩, []) }
      s fe =
      (TreeBorrowsMemory.reborrowInitAccess [(cs.length : Int)] ⟨off⟩ 0 s.inside
          ⟨cs ++ [childNode], List.replicate data.length (.Unprot .Unique), .No⟩ >>= fun root2 =>
        pure (
          { addr := addr + (off : Int), provenance := some (⟨0⟩, [(cs.length : Int)]) },
          { tbm with mem := { tbm.mem with allocations := [{
              mkRootAllocTB data addr align .Stack with
              extra := { root := root2 } }] } },
          if Protected.yes s.«protected» then
            { protectors := fe.protectors ++ [(⟨0⟩, [(cs.length : Int)])] }
          else fe)) := by
  dsimp only
  have hnn : (0 : Int) ≤ (0 : Int) := Int.le_refl _
  have hcheck : BasicMemory.check_ptr
      ({ allocations := [{ mkRootAllocTB data addr align .Stack with
           extra := { root := ⟨cs, List.replicate data.length (.Unprot .Unique), .No⟩ } }],
         _phantom := ⟨⟩ } : Gen.BasicMemory Gen.x86_64 Gen.Path Gen.TreeBorrowsAllocationExtra)
      { addr := addr + (off : Int), provenance := some (⟨0⟩, []) } ⟨s.inside.length⟩ =
      .ok (some (⟨0⟩, [], ⟨off⟩)) := by
    unfold BasicMemory.check_ptr listIndex
    have hne : s.inside.length ≠ 0 := by omega
    have hsub : addr + (off : Int) - addr = (off : Int) := by omega
    have hc : ¬ ((off : Int) < 0 ∨ (off : Int) + (s.inside.length : Int) > (data.length : Int)) := by
      omega
    simp only [hne, ↓reduceIte, hnn, Int.toNat_zero, List.getElem?_cons_zero, mkRootAllocTB,
      Bool.not_true, Bool.false_eq_true, hsub, Allocation.size, hc, Int.toNat_natCast,
      bind, Except.bind, pure, Except.pure]
  have hsz : Size.from_bytes (addr + (off : Int) - addr) = some ⟨off⟩ := by
    have hsub : addr + (off : Int) - addr = (off : Int) := by omega
    rw [hsub]
    unfold Size.from_bytes
    simp only [Int.natCast_nonneg, Int.toNat_natCast, ↓reduceIte]
  have hws : writeSubsliceAtIndex (List.replicate data.length s.outside) (off : Int) s.inside =
      .ok ((List.replicate data.length s.outside).take off ++ s.inside ++
        (List.replicate data.length s.outside).drop (off + s.inside.length)) := by
    unfold writeSubsliceAtIndex
    have hw : (0 : Int) ≤ (off : Int) ∧
        (off : Int) + (s.inside.length : Int) ≤ ((List.replicate data.length s.outside).length : Int) := by
      rw [List.length_replicate]; exact ⟨by omega, by omega⟩
    simp only [hw.1, hw.2, and_self, ↓reduceIte, Int.toNat_natCast, pure, Except.pure]
  have hall : (((List.replicate data.length s.outside).take off ++ s.inside ++
      (List.replicate data.length s.outside).drop (off + s.inside.length)).all
      (fun x => Permission.matches_protector x s.«protected»)) = true := by
    rw [List.all_eq_true]
    intro p hp
    rcases List.mem_append.mp hp with hp1 | hp2
    · rcases List.mem_append.mp hp1 with hp1a | hp1b
      · have hm := List.mem_of_mem_take hp1a
        have heq := List.eq_of_mem_replicate hm
        rw [heq]; exact hmatchOut
      · exact hmatchIn p hp1b
    · have hm := List.mem_of_mem_drop hp2
      have heq := List.eq_of_mem_replicate hm
      rw [heq]; exact hmatchOut
  unfold TreeBorrowsMemory.reborrow
  simp only [hcheck, bind, Except.bind]
  unfold listMutateAt listIndex listSet
  simp only [hnn, Int.toNat_zero, List.getElem?_cons_zero, List.length_singleton, Nat.zero_lt_one,
    and_self, ↓reduceIte, mkRootAllocTB, Allocation.size, hsz, hpos, hws, hall,
    Bool.not_true, Bool.false_eq_true, c1_add_node_root, bind, Except.bind, pure, Except.pure]
  cases TreeBorrowsMemory.reborrowInitAccess [(cs.length : Int)] ⟨off⟩ 0 s.inside
      ⟨cs ++ [⟨[], (List.replicate data.length s.outside).take off ++ s.inside ++
        (List.replicate data.length s.outside).drop (off + s.inside.length), s.«protected»⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩ <;> rfl

private theorem c1_node_access_twoChildren
    (c0 c1 : Gen.Node) (rPerms : List Gen.Permission) (k : Gen.AccessKind) (off len : Nat)
    (path : Option Gen.Path) :
    Node.access ⟨[c0, c1], rPerms, .No⟩ path k ⟨off⟩ ⟨len⟩ =
      (Node.transitionRange (locRel path []) k off len rPerms >>= fun rps =>
        Node.access c0 (subPathAt path 0) k ⟨off⟩ ⟨len⟩ >>= fun c0' =>
          Node.access c1 (subPathAt path 1) k ⟨off⟩ ⟨len⟩ >>= fun c1' =>
            pure ⟨[c0', c1'], rps, .No⟩) := by
  rw [nwsr_access_eq, c1_accessChildren_cons, c1_accessChildren_cons, Node.accessChildren]
  have e1 : (0 : Int) + 1 = 1 := rfl
  rw [e1]
  cases Node.transitionRange (locRel path []) k off len rPerms with
  | error e => rfl
  | ok rps =>
    cases Node.access c0 (subPathAt path 0) k ⟨off⟩ ⟨len⟩ with
    | error e => rfl
    | ok c0' =>
      cases Node.access c1 (subPathAt path 1) k ⟨off⟩ ⟨len⟩ <;> rfl

private theorem c1_node_release_cons (cs : List Gen.Node) (ps : List Gen.Permission)
    (pr : Gen.Protected) (hd : Int) (tl : Gen.Path) (accesses : List (Option Gen.AccessKind)) :
    Node.release_protector ⟨cs, ps, pr⟩ (some (hd :: tl)) accesses =
      (Node.releaseProtectorPermissions .Local 0 accesses ps >>= fun ps' =>
        Node.releaseProtectorChildren 0 (some (hd :: tl)) accesses cs >>= fun cs' =>
          pure ⟨cs', ps', pr⟩) := rfl

private theorem c1_node_releaseChildren_cons (cid : Int) (path : Option Gen.Path)
    (accesses : List (Option Gen.AccessKind)) (c : Gen.Node) (rest : List Gen.Node) :
    Node.releaseProtectorChildren cid path accesses (c :: rest) =
      (Node.release_protector c (subPathAt path cid) accesses >>= fun c' =>
        Node.releaseProtectorChildren (cid + 1) path accesses rest >>= fun rest' =>
          pure (c' :: rest')) := by
  cases path with
  | none => rfl
  | some p => cases p <;> rfl

private theorem c1_node_release_twoChildren
    (c0 c1 : Gen.Node) (rPerms : List Gen.Permission) (accesses : List (Option Gen.AccessKind))
    (idx : Int) (hidx : idx = 0 ∨ idx = 1) :
    Node.release_protector ⟨[c0, c1], rPerms, .No⟩ (some [idx]) accesses =
      (Node.releaseProtectorPermissions .Local 0 accesses rPerms >>= fun rps =>
        Node.release_protector c0 (if idx = 0 then some [] else none) accesses >>= fun c0' =>
          Node.release_protector c1 (if idx = 1 then some [] else none) accesses >>= fun c1' =>
            pure ⟨[c0', c1'], rps, .No⟩) := by
  rw [c1_node_release_cons, c1_node_releaseChildren_cons, c1_node_releaseChildren_cons,
    Node.releaseProtectorChildren]
  rcases hidx with rfl | rfl
  · have hs0 : subPathAt (some [(0 : Int)]) 0 = some [] := rfl
    have hs1 : subPathAt (some [(0 : Int)]) (0 + 1) = none := rfl
    have hne : ¬ ((0 : Int) = 1) := by decide
    rw [hs0, hs1]
    simp only [hne, ↓reduceIte]
    cases Node.releaseProtectorPermissions .Local 0 accesses rPerms with
    | error e => rfl
    | ok rps =>
      cases Node.release_protector c0 (some []) accesses with
      | error e => rfl
      | ok c0' =>
        cases Node.release_protector c1 none accesses <;> rfl
  · have hs0 : subPathAt (some [(1 : Int)]) 0 = none := rfl
    have hs1 : subPathAt (some [(1 : Int)]) (0 + 1) = some [] := rfl
    have hne : ¬ ((1 : Int) = 0) := by decide
    rw [hs0, hs1]
    simp only [hne, ↓reduceIte]
    cases Node.releaseProtectorPermissions .Local 0 accesses rPerms with
    | error e => rfl
    | ok rps =>
      cases Node.release_protector c0 none accesses with
      | error e => rfl
      | ok c0' =>
        cases Node.release_protector c1 (some []) accesses <;> rfl

private theorem c1_releaseProtectorPerms_pointwise (r : Gen.NodeRelation) :
    ∀ (accesses : List (Option Gen.AccessKind)) (off : Nat) (ps : List Gen.Permission),
      (∀ i k, accesses[i]? = some (some k) →
        ∃ p p', ps[off + i]? = some p ∧ Permission.transition p k r = .ok p') →
      ∃ ps', Node.releaseProtectorPermissions r off accesses ps = .ok ps' ∧
        ps'.length = ps.length ∧
        (∀ b, (b < off ∨ accesses[b - off]? = some none ∨ accesses[b - off]? = none) →
          ps'[b]? = ps[b]?) ∧
        (∀ i k p p', accesses[i]? = some (some k) → ps[off + i]? = some p →
          Permission.transition p k r = .ok p' → ps'[off + i]? = some p')
  | [], off, ps, _ =>
    ⟨ps, rfl, rfl, fun _ _ => rfl, fun _ _ _ _ h => by cases h⟩
  | none :: rest, off, ps, h => by
    obtain ⟨ps', hrun, hlen, hout, hin⟩ :=
      c1_releaseProtectorPerms_pointwise r rest (off + 1) ps (fun i k hi => by
        have := h (i + 1) k (by rw [List.getElem?_cons_succ]; exact hi)
        have e : off + (i + 1) = off + 1 + i := by omega
        rw [← e]; exact this)
    refine ⟨ps', hrun, hlen, ?_, ?_⟩
    · intro b hb
      apply hout b
      rcases hb with hlt | hsome | hnone
      · exact Or.inl (by omega)
      · rcases Nat.lt_or_ge b (off + 1) with hlt | hge
        · exact Or.inl hlt
        · have e : b - off = (b - (off + 1)) + 1 := by omega
          rw [e, List.getElem?_cons_succ] at hsome
          exact Or.inr (Or.inl hsome)
      · rcases Nat.lt_or_ge b (off + 1) with hlt | hge
        · exact Or.inl hlt
        · have e : b - off = (b - (off + 1)) + 1 := by omega
          rw [e, List.getElem?_cons_succ] at hnone
          exact Or.inr (Or.inr hnone)
    · intro i k p p' hi hp htr
      cases i with
      | zero => cases hi
      | succ i =>
        rw [List.getElem?_cons_succ] at hi
        have e : off + (i + 1) = off + 1 + i := by omega
        rw [e] at hp ⊢
        exact hin i k p p' hi hp htr
  | some k :: rest, off, ps, h => by
    obtain ⟨p0, p0', hp0, htr0⟩ := h 0 k rfl
    have e0 : off + 0 = off := Nat.add_zero off
    rw [e0] at hp0
    obtain ⟨ps', hrun, hlen, hout, hin⟩ :=
      c1_releaseProtectorPerms_pointwise r rest (off + 1) (ps.set off p0') (fun i k' hi => by
        have := h (i + 1) k' (by rw [List.getElem?_cons_succ]; exact hi)
        have e : off + (i + 1) = off + 1 + i := by omega
        rw [List.getElem?_set_ne (by omega), ← e]
        exact this)
    refine ⟨ps', ?_, by rw [hlen, List.length_set], ?_, ?_⟩
    · unfold Node.releaseProtectorPermissions
      rw [Int.ofNat_eq_natCast, a1_listMutateAt_natCast ps off _ _ p0 hp0]
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [htr0]
      exact hrun
    · intro b hb
      have hne : b ≠ off := by
        intro heq; subst heq
        rcases hb with hlt | hsome | hnone
        · omega
        · rw [Nat.sub_self, List.getElem?_cons_zero] at hsome; cases hsome
        · rw [Nat.sub_self, List.getElem?_cons_zero] at hnone; cases hnone
      have hb' : b < off + 1 ∨ rest[b - (off + 1)]? = some none ∨
          rest[b - (off + 1)]? = none := by
        rcases hb with hlt | hsome | hnone
        · exact Or.inl (by omega)
        · rcases Nat.lt_or_ge b off with hlt | hge
          · exact Or.inl (by omega)
          · have e : b - off = (b - (off + 1)) + 1 := by omega
            rw [e, List.getElem?_cons_succ] at hsome
            exact Or.inr (Or.inl hsome)
        · rcases Nat.lt_or_ge b off with hlt | hge
          · exact Or.inl (by omega)
          · have e : b - off = (b - (off + 1)) + 1 := by omega
            rw [e, List.getElem?_cons_succ] at hnone
            exact Or.inr (Or.inr hnone)
      rw [hout b hb', List.getElem?_set_ne hne.symm]
    · intro i k' p p' hi hp htr
      cases i with
      | zero =>
        cases hi
        rw [e0] at hp ⊢
        rw [hp0] at hp; cases hp
        rw [htr0] at htr; cases htr
        rw [hout off (Or.inl (by omega)),
          List.getElem?_set_self (List.getElem?_eq_some_iff.mp hp0).1]
      | succ i =>
        rw [List.getElem?_cons_succ] at hi
        have e : off + (i + 1) = off + 1 + i := by omega
        rw [e] at hp ⊢
        exact hin i k' p p' hi (by rw [List.getElem?_set_ne (by omega)]; exact hp) htr

private theorem c1_mapM_unprotect_spec :
    ∀ (ps : List Gen.Permission), (∀ p ∈ ps, ∃ pp, p = .Prot pp) →
      ∃ pairs, ps.mapM Permission.unprotect = .ok pairs ∧
        pairs.length = ps.length ∧
        ∀ (b : Nat) (p : Gen.Permission) (pp : Gen.PermissionProt),
          ps[b]? = some p → p = .Prot pp →
          pairs[b]? = some (Gen.Permission.Unprot (PermissionProt.unprotect pp).1,
            (PermissionProt.unprotect pp).2)
  | [], _ => ⟨[], rfl, rfl, fun _ _ _ h _ => (by cases h)⟩
  | p :: rest, h => by
    obtain ⟨pp0, rfl⟩ := h p (List.mem_cons_self ..)
    obtain ⟨pairs, hp, hlen, hget⟩ := c1_mapM_unprotect_spec rest
      (fun q hq => h q (List.mem_cons_of_mem _ hq))
    refine ⟨(Gen.Permission.Unprot (PermissionProt.unprotect pp0).1,
        (PermissionProt.unprotect pp0).2) :: pairs, ?_,
      by rw [List.length_cons, List.length_cons, hlen], ?_⟩
    · rw [List.mapM_cons]
      simp only [Permission.unprotect, bind, Except.bind, pure, Except.pure, hp]
    · intro b q pp hq heq
      cases b with
      | zero =>
        rw [List.getElem?_cons_zero] at hq
        cases hq; cases heq; rfl
      | succ b =>
        rw [List.getElem?_cons_succ] at hq ⊢
        exact hget b q pp hq heq

private theorem c1_releaseProtectorPerms_unprot_wf (r : Gen.NodeRelation) :
    ∀ (accesses : List (Option Gen.AccessKind)) (off : Nat) (l l' : List Gen.Permission),
      (∀ p ∈ l, ∃ u, p = .Unprot u) →
      Node.releaseProtectorPermissions r off accesses l = .ok l' →
      l'.length = l.length ∧ ∀ p ∈ l', ∃ u, p = .Unprot u
  | [], _, l, l', hl, h0 => by cases h0; exact ⟨rfl, hl⟩
  | none :: rest, off, l, l', hl, h0 =>
    c1_releaseProtectorPerms_unprot_wf r rest (off + 1) l l' hl h0
  | some k :: rest, off, l, l', hl, h0 => by
    unfold Node.releaseProtectorPermissions at h0
    obtain ⟨⟨_, l1⟩, hmut, hrest⟩ := nwsr_bind_ok h0
    cases hg : l[off]? with
    | none =>
      unfold listMutateAt listIndex at hmut
      simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, Int.toNat_natCast,
        ↓reduceIte, hg, bind, Except.bind] at hmut
      cases hmut
    | some p =>
      rw [Int.ofNat_eq_natCast, a1_listMutateAt_natCast l off _ _ p hg] at hmut
      obtain ⟨⟨_, p'⟩, htr, hmut⟩ := nwsr_bind_ok hmut
      cases hmut
      obtain ⟨u, rfl⟩ := hl p (List.mem_of_getElem? hg)
      obtain ⟨p1, htr1, htr2⟩ := nwsr_bind_ok htr
      cases htr2
      unfold Permission.transition at htr1
      obtain ⟨u', _, htr1⟩ := nwsr_bind_ok htr1
      have hp' : p' = .Unprot u' := by cases htr1; rfl
      subst hp'
      have hl1 : ∀ q ∈ l.set off (.Unprot u'), ∃ u0, q = .Unprot u0 := by
        intro q hq
        obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hq
        by_cases hix : idx = off
        · subst idx
          rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hg).1] at hidx
          cases hidx; exact ⟨u', rfl⟩
        · rw [List.getElem?_set_ne (Ne.symm hix)] at hidx
          exact hl q (List.mem_of_getElem? hidx)
      obtain ⟨hl', hu'⟩ := c1_releaseProtectorPerms_unprot_wf r rest (off + 1) _ l' hl1 hrest
      exact ⟨by rw [hl', List.length_set], hu'⟩

private theorem c1_slice_disjoint_splitAtMut_endCalls
    (data12 : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int) (align : Nat)
    (off1 len1 off2 len2 : Nat)
    (hdisj : off1 + len1 ≤ off2) (hbound : off2 + len2 ≤ data12.length)
    (c0f c1f : List Gen.Permission)
    (hc0fLen : c0f.length = data12.length) (hc1fLen : c1f.length = data12.length)
    (hc0fGet : ∀ b, b < data12.length →
      c0f[b]? = some (if off1 ≤ b ∧ b < off1 + len1 then .Prot .Unique
        else if off2 ≤ b ∧ b < off2 + len2 then .Prot .Disabled
        else .Prot (.Reserved false false)))
    (hc1fGet : ∀ b, b < data12.length →
      c1f[b]? = some (if off1 ≤ b ∧ b < off1 + len1 then .Prot .Disabled
        else if off2 ≤ b ∧ b < off2 + len2 then .Prot .Unique
        else .Prot (.Reserved false false))) :
    let tbm12 : Gen.TreeBorrowsMemory Gen.x86_64 :=
      { params := ⟨true⟩
        mem := { allocations := [{
          mkRootAllocTB data12 addr align .Stack with
          extra := { root := ⟨[⟨[], c0f, .Strong⟩, ⟨[], c1f, .Strong⟩],
            List.replicate data12.length (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } }
    ∃ tbmEndFwd tbmEndRev,
      TreeBorrowsMemory.end_call tbm12 { protectors := [(⟨0⟩, [0]), (⟨0⟩, [1])] } = .ok tbmEndFwd ∧
      TreeBorrowsMemory.wfLive tbmEndFwd ∧
      TreeBorrowsMemory.end_call tbm12 { protectors := [(⟨0⟩, [1]), (⟨0⟩, [0])] } = .ok tbmEndRev ∧
      TreeBorrowsMemory.wfLive tbmEndRev := by
  dsimp only
  have hprot0 : ∀ p ∈ c0f, ∃ pp, p = .Prot pp := by
    intro p hp
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hp
    have hblt : b < data12.length := by rw [← hc0fLen]; exact (List.getElem?_eq_some_iff.mp hb).1
    rw [hc0fGet b hblt] at hb; cases hb
    split
    · exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩
  have hprot1 : ∀ p ∈ c1f, ∃ pp, p = .Prot pp := by
    intro p hp
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hp
    have hblt : b < data12.length := by rw [← hc1fLen]; exact (List.getElem?_eq_some_iff.mp hb).1
    rw [hc1fGet b hblt] at hb; cases hb
    split
    · exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩
  obtain ⟨pairs0, hpairs0, hp0Len, hp0Get⟩ := c1_mapM_unprotect_spec c0f hprot0
  obtain ⟨pairs1, hpairs1, hp1Len, hp1Get⟩ := c1_mapM_unprotect_spec c1f hprot1
  have hacc0Spec : ∀ b k, (pairs0.map Prod.snd)[b]? = some (some k) →
      off1 ≤ b ∧ b < off1 + len1 ∧ k = .Write := by
    intro b k hbk
    rw [List.getElem?_map] at hbk
    cases hg : pairs0[b]? with
    | none => rw [hg] at hbk; cases hbk
    | some pr =>
      rcases pr with ⟨pFst, pSnd⟩
      rw [hg] at hbk; cases hbk
      have hblt : b < data12.length := by
        rw [← hc0fLen, ← hp0Len]; exact (List.getElem?_eq_some_iff.mp hg).1
      have hcb := hc0fGet b hblt
      rcases c1_in_or_out off1 len1 b with ⟨h1, h2⟩ | hout
      · simp only [h1, h2, and_self, ↓reduceIte] at hcb
        have hp := hp0Get b _ _ hcb rfl
        rw [hg] at hp; cases hp
        exact ⟨h1, h2, rfl⟩
      · have hn1 : ¬ (off1 ≤ b ∧ b < off1 + len1) := by omega
        simp only [hn1, ↓reduceIte] at hcb
        by_cases h2 : off2 ≤ b ∧ b < off2 + len2
        · simp only [h2, and_self, ↓reduceIte] at hcb
          have hp := hp0Get b _ _ hcb rfl
          rw [hg] at hp; cases hp
        · simp only [h2, ↓reduceIte] at hcb
          have hp := hp0Get b _ _ hcb rfl
          rw [hg] at hp; cases hp
  have hacc1Spec : ∀ b k, (pairs1.map Prod.snd)[b]? = some (some k) →
      off2 ≤ b ∧ b < off2 + len2 ∧ k = .Write := by
    intro b k hbk
    rw [List.getElem?_map] at hbk
    cases hg : pairs1[b]? with
    | none => rw [hg] at hbk; cases hbk
    | some pr =>
      rcases pr with ⟨pFst, pSnd⟩
      rw [hg] at hbk; cases hbk
      have hblt : b < data12.length := by
        rw [← hc1fLen, ← hp1Len]; exact (List.getElem?_eq_some_iff.mp hg).1
      have hcb := hc1fGet b hblt
      rcases c1_in_or_out off2 len2 b with ⟨h1, h2⟩ | hout
      · have hn1 : ¬ (off1 ≤ b ∧ b < off1 + len1) := by omega
        simp only [hn1, ↓reduceIte] at hcb
        simp only [h1, h2, and_self, ↓reduceIte] at hcb
        have hp := hp1Get b _ _ hcb rfl
        rw [hg] at hp; cases hp
        exact ⟨h1, h2, rfl⟩
      · have hn2 : ¬ (off2 ≤ b ∧ b < off2 + len2) := by omega
        by_cases h1 : off1 ≤ b ∧ b < off1 + len1
        · simp only [h1, and_self, ↓reduceIte] at hcb
          have hp := hp1Get b _ _ hcb rfl
          rw [hg] at hp; cases hp
        · simp only [h1, hn2, ↓reduceIte] at hcb
          have hp := hp1Get b _ _ hcb rfl
          rw [hg] at hp; cases hp
  have huRoot : ∀ p ∈ List.replicate data12.length (Gen.Permission.Unprot .Unique),
      ∃ u, p = Gen.Permission.Unprot u :=
    fun p hp => ⟨Gen.PermissionUnprot.Unique, List.eq_of_mem_replicate hp⟩
  have huP0 : ∀ p ∈ pairs0.map Prod.fst, ∃ u, p = .Unprot u := by
    intro p hp
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hp
    rw [List.getElem?_map] at hb
    cases hpb : pairs0[b]? with
    | none => rw [hpb] at hb; cases hb
    | some pr =>
      rw [hpb] at hb; cases hb
      have hblt : b < data12.length := by
        rw [← hc0fLen, ← hp0Len]; exact (List.getElem?_eq_some_iff.mp hpb).1
      obtain ⟨q0, hq0⟩ : ∃ q0, c0f[b]? = some q0 :=
        ⟨c0f[b]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨pp, rfl⟩ := hprot0 q0 (List.mem_of_getElem? hq0)
      have he := hp0Get b _ _ hq0 rfl
      rw [hpb] at he; cases he; exact ⟨_, rfl⟩
  have huP1 : ∀ p ∈ pairs1.map Prod.fst, ∃ u, p = .Unprot u := by
    intro p hp
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hp
    rw [List.getElem?_map] at hb
    cases hpb : pairs1[b]? with
    | none => rw [hpb] at hb; cases hb
    | some pr =>
      rw [hpb] at hb; cases hb
      have hblt : b < data12.length := by
        rw [← hc1fLen, ← hp1Len]; exact (List.getElem?_eq_some_iff.mp hpb).1
      obtain ⟨q1, hq1⟩ : ∃ q1, c1f[b]? = some q1 :=
        ⟨c1f[b]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨pp, rfl⟩ := hprot1 q1 (List.mem_of_getElem? hq1)
      have he := hp1Get b _ _ hq1 rfl
      rw [hpb] at he; cases he; exact ⟨_, rfl⟩
  have hrootRel0 : Node.releaseProtectorPermissions .Local 0 (pairs0.map Prod.snd)
      (List.replicate data12.length (.Unprot .Unique)) =
      .ok (List.replicate data12.length (.Unprot .Unique)) := by
    obtain ⟨rps, hrun, _, hout, hin⟩ := c1_releaseProtectorPerms_pointwise .Local
      (pairs0.map Prod.snd) 0 (List.replicate data12.length (.Unprot .Unique)) (fun i k hi => by
        obtain ⟨_, h2, rfl⟩ := hacc0Spec i k hi
        exact ⟨.Unprot .Unique, .Unprot .Unique,
          by rw [Nat.zero_add]; exact nwsr_getElem?_replicate_lt (by omega), rfl⟩)
    have heq : rps = List.replicate data12.length (.Unprot .Unique) := by
      apply List.ext_getElem?
      intro b
      cases hb : (pairs0.map Prod.snd)[b]? with
      | none => exact hout b (Or.inr (Or.inr (by rw [Nat.sub_zero]; exact hb)))
      | some opt =>
        cases opt with
        | none => exact hout b (Or.inr (Or.inl (by rw [Nat.sub_zero]; exact hb)))
        | some k =>
          obtain ⟨_, h2, rfl⟩ := hacc0Spec b k hb
          have hget := nwsr_getElem?_replicate_lt (a := Gen.Permission.Unprot .Unique)
            (show b < data12.length by omega)
          have hrb := hin b .Write _ _ hb (by rw [Nat.zero_add]; exact hget) rfl
          rw [Nat.zero_add] at hrb; rw [hrb, hget]
    rw [heq] at hrun; exact hrun
  have hrootRel1 : Node.releaseProtectorPermissions .Local 0 (pairs1.map Prod.snd)
      (List.replicate data12.length (.Unprot .Unique)) =
      .ok (List.replicate data12.length (.Unprot .Unique)) := by
    obtain ⟨rps, hrun, _, hout, hin⟩ := c1_releaseProtectorPerms_pointwise .Local
      (pairs1.map Prod.snd) 0 (List.replicate data12.length (.Unprot .Unique)) (fun i k hi => by
        obtain ⟨_, h2, rfl⟩ := hacc1Spec i k hi
        exact ⟨.Unprot .Unique, .Unprot .Unique,
          by rw [Nat.zero_add]; exact nwsr_getElem?_replicate_lt (by omega), rfl⟩)
    have heq : rps = List.replicate data12.length (.Unprot .Unique) := by
      apply List.ext_getElem?
      intro b
      cases hb : (pairs1.map Prod.snd)[b]? with
      | none => exact hout b (Or.inr (Or.inr (by rw [Nat.sub_zero]; exact hb)))
      | some opt =>
        cases opt with
        | none => exact hout b (Or.inr (Or.inl (by rw [Nat.sub_zero]; exact hb)))
        | some k =>
          obtain ⟨_, h2, rfl⟩ := hacc1Spec b k hb
          have hget := nwsr_getElem?_replicate_lt (a := Gen.Permission.Unprot .Unique)
            (show b < data12.length by omega)
          have hrb := hin b .Write _ _ hb (by rw [Nat.zero_add]; exact hget) rfl
          rw [Nat.zero_add] at hrb; rw [hrb, hget]
    rw [heq] at hrun; exact hrun
  have hc1Rel0 : Node.releaseProtectorPermissions .Foreign 0 (pairs0.map Prod.snd) c1f = .ok c1f := by
    obtain ⟨ps', hrun, _, hout, hin⟩ := c1_releaseProtectorPerms_pointwise .Foreign
      (pairs0.map Prod.snd) 0 c1f (fun i k hi => by
        obtain ⟨h1, h2, rfl⟩ := hacc0Spec i k hi
        have hg := hc1fGet i (by omega)
        simp only [h1, h2, and_self, ↓reduceIte] at hg
        exact ⟨.Prot .Disabled, .Prot .Disabled, by rw [Nat.zero_add]; exact hg, rfl⟩)
    have heq : ps' = c1f := by
      apply List.ext_getElem?
      intro b
      cases hb : (pairs0.map Prod.snd)[b]? with
      | none => exact hout b (Or.inr (Or.inr (by rw [Nat.sub_zero]; exact hb)))
      | some opt =>
        cases opt with
        | none => exact hout b (Or.inr (Or.inl (by rw [Nat.sub_zero]; exact hb)))
        | some k =>
          obtain ⟨h1, h2, rfl⟩ := hacc0Spec b k hb
          have hg := hc1fGet b (by omega)
          simp only [h1, h2, and_self, ↓reduceIte] at hg
          have hrb := hin b .Write _ _ hb (by rw [Nat.zero_add]; exact hg) rfl
          rw [Nat.zero_add] at hrb; rw [hrb, hg]
    rw [heq] at hrun; exact hrun
  have hc0Rel1 : Node.releaseProtectorPermissions .Foreign 0 (pairs1.map Prod.snd) c0f = .ok c0f := by
    obtain ⟨ps', hrun, _, hout, hin⟩ := c1_releaseProtectorPerms_pointwise .Foreign
      (pairs1.map Prod.snd) 0 c0f (fun i k hi => by
        obtain ⟨h1, h2, rfl⟩ := hacc1Spec i k hi
        have hg := hc0fGet i (by omega)
        have hn1 : ¬ (off1 ≤ i ∧ i < off1 + len1) := by omega
        simp only [hn1, ↓reduceIte] at hg
        simp only [h1, h2, and_self, ↓reduceIte] at hg
        exact ⟨.Prot .Disabled, .Prot .Disabled, by rw [Nat.zero_add]; exact hg, rfl⟩)
    have heq : ps' = c0f := by
      apply List.ext_getElem?
      intro b
      cases hb : (pairs1.map Prod.snd)[b]? with
      | none => exact hout b (Or.inr (Or.inr (by rw [Nat.sub_zero]; exact hb)))
      | some opt =>
        cases opt with
        | none => exact hout b (Or.inr (Or.inl (by rw [Nat.sub_zero]; exact hb)))
        | some k =>
          obtain ⟨h1, h2, rfl⟩ := hacc1Spec b k hb
          have hg := hc0fGet b (by omega)
          have hn1 : ¬ (off1 ≤ b ∧ b < off1 + len1) := by omega
          simp only [hn1, ↓reduceIte] at hg
          simp only [h1, h2, and_self, ↓reduceIte] at hg
          have hrb := hin b .Write _ _ hb (by rw [Nat.zero_add]; exact hg) rfl
          rw [Nat.zero_add] at hrb; rw [hrb, hg]
    rw [heq] at hrun; exact hrun
  obtain ⟨ps0After1, hps0After1, _⟩ := c1_releaseProtectorPerms_pointwise .Foreign
    (pairs1.map Prod.snd) 0 (pairs0.map Prod.fst) (fun i k hi => by
      obtain ⟨h1, h2, rfl⟩ := hacc1Spec i k hi
      have hcb := hc0fGet i (by omega)
      have hn1 : ¬ (off1 ≤ i ∧ i < off1 + len1) := by omega
      simp only [hn1, ↓reduceIte] at hcb
      simp only [h1, h2, and_self, ↓reduceIte] at hcb
      have hp := hp0Get i _ _ hcb rfl
      have hget : (pairs0.map Prod.fst)[0 + i]? = some (.Unprot .Disabled) := by
        rw [Nat.zero_add, List.getElem?_map, hp]; rfl
      exact ⟨.Unprot .Disabled, .Unprot .Disabled, hget, rfl⟩)
  obtain ⟨ps1After0, hps1After0, _⟩ := c1_releaseProtectorPerms_pointwise .Foreign
    (pairs0.map Prod.snd) 0 (pairs1.map Prod.fst) (fun i k hi => by
      obtain ⟨h1, h2, rfl⟩ := hacc0Spec i k hi
      have hcb := hc1fGet i (by omega)
      simp only [h1, h2, and_self, ↓reduceIte] at hcb
      have hp := hp1Get i _ _ hcb rfl
      have hget : (pairs1.map Prod.fst)[0 + i]? = some (.Unprot .Disabled) := by
        rw [Nat.zero_add, List.getElem?_map, hp]; rfl
      exact ⟨.Unprot .Disabled, .Unprot .Disabled, hget, rfl⟩)
  obtain ⟨h0Len', h0Unprot'⟩ := c1_releaseProtectorPerms_unprot_wf .Foreign _ 0 _ _ huP0 hps0After1
  obtain ⟨h1Len', h1Unprot'⟩ := c1_releaseProtectorPerms_unprot_wf .Foreign _ 0 _ _ huP1 hps1After0
  let mkMem := fun (root : Gen.Node) =>
    ({ params := ⟨true⟩
       mem := { allocations := [{ mkRootAllocTB data12 addr align .Stack with
         extra := { root := root } }], _phantom := ⟨⟩ } } : Gen.TreeBorrowsMemory Gen.x86_64)
  let rootF : Gen.Node := ⟨[⟨[], c0f, .Strong⟩, ⟨[], c1f, .Strong⟩],
    List.replicate data12.length (.Unprot .Unique), .No⟩
  let rootMid0 : Gen.Node := ⟨[⟨[], pairs0.map Prod.fst, .No⟩, ⟨[], c1f, .Strong⟩],
    List.replicate data12.length (.Unprot .Unique), .No⟩
  let rootMid1 : Gen.Node := ⟨[⟨[], c0f, .Strong⟩, ⟨[], pairs1.map Prod.fst, .No⟩],
    List.replicate data12.length (.Unprot .Unique), .No⟩
  let rootEndFwd : Gen.Node := ⟨[⟨[], ps0After1, .No⟩, ⟨[], pairs1.map Prod.fst, .No⟩],
    List.replicate data12.length (.Unprot .Unique), .No⟩
  let rootEndRev : Gen.Node := ⟨[⟨[], pairs0.map Prod.fst, .No⟩, ⟨[], ps1After0, .No⟩],
    List.replicate data12.length (.Unprot .Unique), .No⟩
  have hpyS : Protected.yes Gen.Protected.Strong = true := rfl
  have hrel0 : TreeBorrowsMemory.release_protector (mkMem rootF) (⟨0⟩, [0]) = .ok (mkMem rootMid0) := by
    unfold TreeBorrowsMemory.release_protector
    dsimp only [mkMem, rootF, rootMid0]
    rw [c1_listMutateAt_zero]
    simp only [Node.access_node, Node.is_leaf, List.isEmpty, c1_listMutateAt_zero,
      hpyS, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpairs0,
      mkRootAllocTB, bind, Except.bind, pure, Except.pure]
    rw [c1_node_release_twoChildren _ _ _ _ 0 (Or.inl rfl)]
    have hne01 : ¬ ((0 : Int) = 1) := by decide
    simp only [hne01, ↓reduceIte, hrootRel0, bind, Except.bind, pure, Except.pure]
    have hr0 : Node.release_protector ⟨[], pairs0.map Prod.fst, .Strong⟩ (some [])
        (pairs0.map Prod.snd) = .ok ⟨[], pairs0.map Prod.fst, .No⟩ := rfl
    have hr1 : Node.release_protector ⟨[], c1f, .Strong⟩ none (pairs0.map Prod.snd) =
        .ok ⟨[], c1f, .Strong⟩ := by
      unfold Node.release_protector; simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte,
        hc1Rel0, Node.releaseProtectorChildren, bind, Except.bind, pure, Except.pure]
    rw [hr0, hr1]
  have hrel1After0 : TreeBorrowsMemory.release_protector (mkMem rootMid0) (⟨0⟩, [1]) =
      .ok (mkMem rootEndFwd) := by
    unfold TreeBorrowsMemory.release_protector
    dsimp only [mkMem, rootMid0, rootEndFwd]
    rw [c1_listMutateAt_zero]
    simp only [Node.access_node, Node.is_leaf, List.isEmpty, c1_listMutateAt_one,
      hpyS, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpairs1,
      mkRootAllocTB, bind, Except.bind, pure, Except.pure]
    rw [c1_node_release_twoChildren _ _ _ _ 1 (Or.inr rfl)]
    have hne10 : ¬ ((1 : Int) = 0) := by decide
    simp only [hne10, ↓reduceIte, hrootRel1, bind, Except.bind, pure, Except.pure]
    have hr0 : Node.release_protector ⟨[], pairs0.map Prod.fst, .No⟩ none (pairs1.map Prod.snd) =
        .ok ⟨[], ps0After1, .No⟩ := by
      unfold Node.release_protector; simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte,
        hps0After1, Node.releaseProtectorChildren, bind, Except.bind, pure, Except.pure]
    have hr1 : Node.release_protector ⟨[], pairs1.map Prod.fst, .Strong⟩ (some [])
        (pairs1.map Prod.snd) = .ok ⟨[], pairs1.map Prod.fst, .No⟩ := rfl
    rw [hr0, hr1]
  have hrel1 : TreeBorrowsMemory.release_protector (mkMem rootF) (⟨0⟩, [1]) = .ok (mkMem rootMid1) := by
    unfold TreeBorrowsMemory.release_protector
    dsimp only [mkMem, rootF, rootMid1]
    rw [c1_listMutateAt_zero]
    simp only [Node.access_node, Node.is_leaf, List.isEmpty, c1_listMutateAt_one,
      hpyS, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpairs1,
      mkRootAllocTB, bind, Except.bind, pure, Except.pure]
    rw [c1_node_release_twoChildren _ _ _ _ 1 (Or.inr rfl)]
    have hne10 : ¬ ((1 : Int) = 0) := by decide
    simp only [hne10, ↓reduceIte, hrootRel1, bind, Except.bind, pure, Except.pure]
    have hr0 : Node.release_protector ⟨[], c0f, .Strong⟩ none (pairs1.map Prod.snd) =
        .ok ⟨[], c0f, .Strong⟩ := by
      unfold Node.release_protector; simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte,
        hc0Rel1, Node.releaseProtectorChildren, bind, Except.bind, pure, Except.pure]
    have hr1 : Node.release_protector ⟨[], pairs1.map Prod.fst, .Strong⟩ (some [])
        (pairs1.map Prod.snd) = .ok ⟨[], pairs1.map Prod.fst, .No⟩ := rfl
    rw [hr0, hr1]
  have hrel0After1 : TreeBorrowsMemory.release_protector (mkMem rootMid1) (⟨0⟩, [0]) =
      .ok (mkMem rootEndRev) := by
    unfold TreeBorrowsMemory.release_protector
    dsimp only [mkMem, rootMid1, rootEndRev]
    rw [c1_listMutateAt_zero]
    simp only [Node.access_node, Node.is_leaf, List.isEmpty, c1_listMutateAt_zero,
      hpyS, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpairs0,
      mkRootAllocTB, bind, Except.bind, pure, Except.pure]
    rw [c1_node_release_twoChildren _ _ _ _ 0 (Or.inl rfl)]
    have hne01 : ¬ ((0 : Int) = 1) := by decide
    simp only [hne01, ↓reduceIte, hrootRel0, bind, Except.bind, pure, Except.pure]
    have hr0 : Node.release_protector ⟨[], pairs0.map Prod.fst, .Strong⟩ (some [])
        (pairs0.map Prod.snd) = .ok ⟨[], pairs0.map Prod.fst, .No⟩ := rfl
    have hr1 : Node.release_protector ⟨[], pairs1.map Prod.fst, .No⟩ none (pairs0.map Prod.snd) =
        .ok ⟨[], ps1After0, .No⟩ := by
      unfold Node.release_protector; simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte,
        hps1After0, Node.releaseProtectorChildren, bind, Except.bind, pure, Except.pure]
    rw [hr0, hr1]
  have hwfLeaf : ∀ (ps : List Gen.Permission), ps.length = data12.length →
      (∀ p ∈ ps, ∃ u, p = .Unprot u) → Node.wf data12.length ⟨[], ps, .No⟩ := by
    intro ps hlen hu
    rw [Node.wf, Node.childrenWf]
    exact ⟨hlen, fun p hp => by obtain ⟨u, rfl⟩ := hu p hp; rfl, trivial⟩
  have hwfMem : ∀ (c0 c1 : Gen.Node),
      Node.wf data12.length c0 → Node.wf data12.length c1 →
      TreeBorrowsMemory.wfLive (mkMem ⟨[c0, c1], List.replicate data12.length (.Unprot .Unique), .No⟩) := by
    intro c0 c1 h0 h1 a ha _
    have haEq := List.mem_singleton.mp ha
    subst haEq
    show Node.wf data12.length _
    rw [Node.wf, Node.childrenWf, Node.childrenWf, Node.childrenWf]
    exact ⟨List.length_replicate, fun p hp => by obtain ⟨u, rfl⟩ := huRoot p hp; rfl, h0, h1, trivial⟩
  refine ⟨mkMem rootEndFwd, mkMem rootEndRev, ?_, ?_, ?_, ?_⟩
  · unfold TreeBorrowsMemory.end_call
    dsimp only [List.foldlM, bind, Except.bind, pure, Except.pure]
    rw [hrel0]; dsimp only; rw [hrel1After0]
  · exact hwfMem _ _
      (hwfLeaf ps0After1 (by rw [h0Len', List.length_map, hp0Len, hc0fLen]) h0Unprot')
      (hwfLeaf (pairs1.map Prod.fst) (by rw [List.length_map, hp1Len, hc1fLen]) huP1)
  · unfold TreeBorrowsMemory.end_call
    dsimp only [List.foldlM, bind, Except.bind, pure, Except.pure]
    rw [hrel1]; dsimp only; rw [hrel0After1]
  · exact hwfMem _ _
      (hwfLeaf (pairs0.map Prod.fst) (by rw [List.length_map, hp0Len, hc0fLen]) huP0)
      (hwfLeaf ps1After0 (by rw [h1Len', List.length_map, hp1Len, hc1fLen]) h1Unprot')

private theorem c1_slice_disjoint_splitAtMut_sound
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int) (align : Nat)
    (off1 len1 off2 len2 : Nat)
    (hlen1 : 0 < len1) (hlen2 : 0 < len2)
    (hdisj : off1 + len1 ≤ off2) (hbound : off2 + len2 ≤ data.length)
    (wBytes1 wBytes2 : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (hw1 : wBytes1.length = len1) (hw2 : wBytes2.length = len2)
    (al1 al2 : Nat)
    (hal1 : Align.is_aligned ⟨al1⟩ (addr + (off1 : Int)) = true)
    (hal2 : Align.is_aligned ⟨al2⟩ (addr + (off2 : Int)) = true)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable)
    (fnIw1 fnIw2 : Bool) :
    let tbm0 : Gen.TreeBorrowsMemory Gen.x86_64 :=
      { params := ⟨true⟩
        mem := { allocations := [mkRootAllocTB data addr align .Stack], _phantom := ⟨⟩ } }
    let p1In : Gen.Pointer Gen.TreeBorrowsProvenance :=
      { thin_pointer := { addr := addr + (off1 : Int), provenance := some (⟨0⟩, []) },
        metadata := none }
    let p2In : Gen.Pointer Gen.TreeBorrowsProvenance :=
      { thin_pointer := { addr := addr + (off2 : Int), provenance := some (⟨0⟩, []) },
        metadata := none }
    ∃ tbm1 tbm2 fe1 fe2 tbm12 tbm21 tbmEndFwd tbmEndRev,
      TreeBorrowsMemory.retag_ptr tbm0 TreeBorrowsMemory.new_call p1In
          (.Ref .Mutable (slicePointeeInfoMR len1 al1)) true fnIw1 lookup =
        .ok ({ thin_pointer := { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) },
               metadata := none }, tbm1, fe1) ∧
      TreeBorrowsMemory.retag_ptr tbm1 fe1 p2In
          (.Ref .Mutable (slicePointeeInfoMR len2 al2)) true fnIw2 lookup =
        .ok ({ thin_pointer := { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) },
               metadata := none }, tbm2, fe2) ∧
      fe2 = { protectors := [(⟨0⟩, [0]), (⟨0⟩, [1])] } ∧
      TreeBorrowsMemory.wfLive tbm2 ∧
      (TreeBorrowsMemory.store tbm2
          { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } wBytes1 ⟨al1⟩ >>=
        fun t => TreeBorrowsMemory.store t
          { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩) =
        .ok tbm12 ∧
      (TreeBorrowsMemory.store tbm2
          { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩ >>=
        fun t => TreeBorrowsMemory.store t
          { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } wBytes1 ⟨al1⟩) =
        .ok tbm21 ∧
      tbmRootOf tbm12 0 = tbmRootOf tbm21 0 ∧
      TreeBorrowsMemory.end_call tbm12 fe2 = .ok tbmEndFwd ∧
      TreeBorrowsMemory.wfLive tbmEndFwd ∧
      TreeBorrowsMemory.end_call tbm12 { protectors := fe2.protectors.reverse } = .ok tbmEndRev ∧
      TreeBorrowsMemory.wfLive tbmEndRev := by
  dsimp only
  have hwf0 : TreeBorrowsMemory.wfLive
      ({ params := ⟨true⟩, mem := { allocations := [mkRootAllocTB data addr align .Stack], _phantom := ⟨⟩ } } : Gen.TreeBorrowsMemory Gen.x86_64) := by
    intro alloc ha _
    have := List.mem_singleton.mp ha
    subst this
    exact mkRootAllocTB_wf data addr align .Stack
  let p1Init : Gen.Permission := if fnIw1 then .Prot .Unique else .Prot (.Reserved false false)
  let p1After : Gen.Permission := if fnIw1 then .Prot .Unique else .Prot (.Reserved true false)
  let k1 : Gen.AccessKind := if fnIw1 then .Write else .Read
  let p2Init : Gen.Permission := if fnIw2 then .Prot .Unique else .Prot (.Reserved false false)
  let p2After : Gen.Permission := if fnIw2 then .Prot .Unique else .Prot (.Reserved true false)
  let k2 : Gen.AccessKind := if fnIw2 then .Write else .Read
  have hinit1 : Permission.init_access p1Init = some k1 := by cases fnIw1 <;> rfl
  have hinit2 : Permission.init_access p2Init = some k2 := by cases fnIw2 <;> rfl
  have htr1 : Permission.transition p1Init k1 .Local = .ok p1After := by cases fnIw1 <;> rfl
  have htr2 : Permission.transition p2Init k2 .Local = .ok p2After := by cases fnIw2 <;> rfl
  have hrootTr : ∀ k : Gen.AccessKind,
      Permission.transition (.Unprot .Unique) k .Local = .ok (.Unprot .Unique) := by
    intro k; cases k <;> rfl
  -- Step 1: retag_ptr for [0] on [off1, off1 + len1)
  let c0Perms0 := (List.replicate data.length (.Prot (.Reserved false false))).take off1 ++
    List.replicate len1 p1Init ++
    (List.replicate data.length (.Prot (.Reserved false false))).drop (off1 + len1)
  have hc0Len0 : c0Perms0.length = data.length := by
    simp only [c0Perms0, List.length_append, List.length_take, List.length_drop,
      List.length_replicate]; omega
  have hc0Get0 : ∀ b, b < data.length →
      c0Perms0[b]? = some (if off1 ≤ b ∧ b < off1 + len1 then p1Init else .Prot (.Reserved false false)) := by
    intro b hb
    have heq : c0Perms0 = List.replicate off1 (.Prot (.Reserved false false)) ++
        List.replicate len1 p1Init ++
        List.replicate (data.length - (off1 + len1)) (.Prot (.Reserved false false)) := by
      simp only [c0Perms0, List.take_replicate, List.drop_replicate,
        Nat.min_eq_left (show off1 ≤ data.length by omega)]
    rw [heq]
    exact c1_windowPerms_getElem? data.length off1 len1 (.Prot (.Reserved false false)) p1Init
      (by omega) b hb
  let P1 : Nat → Gen.Node → Prop := fun i t =>
    ∃ c0ps, t = ⟨[⟨[], c0ps, .Strong⟩], List.replicate data.length (.Unprot .Unique), .No⟩ ∧
      c0ps.length = data.length ∧
      ∀ b, b < data.length →
        c0ps[b]? = some (if off1 ≤ b ∧ b < off1 + i then p1After
          else if off1 ≤ b ∧ b < off1 + len1 then p1Init
          else .Prot (.Reserved false false))
  obtain ⟨root1, hinitRun1, ⟨c0ps1, hroot1Eq, hc0Len1, hc0Get1⟩⟩ :=
    c1_reborrowInitAccess_const_ok [0] off1 p1Init k1 hinit1 len1 0
      ⟨[⟨[], c0Perms0, .Strong⟩], List.replicate data.length (.Unprot .Unique), .No⟩ P1
      ⟨c0Perms0, rfl, hc0Len0, fun b hb => by
        rw [hc0Get0 b hb]
        have h0 : ¬ (off1 ≤ b ∧ b < off1 + 0) := fun ⟨_, _⟩ => by omega
        simp only [h0, ↓reduceIte]⟩
      (fun i ti _ hi hPi => by
        rcases hPi with ⟨cps, hti, hclen, hcget⟩
        subst hti
        have hrootStep : Node.transitionRange .Local k1 (off1 + i) 1
            (List.replicate data.length (.Unprot .Unique)) =
            .ok (List.replicate data.length (.Unprot .Unique)) :=
          transitionRange_stable_eq .Local k1 1 (off1 + i) _ (fun b _ h2 =>
            ⟨_, nwsr_getElem?_replicate_lt (by omega), hrootTr k1⟩)
        obtain ⟨cps', hrun, hlen', hout', hin'⟩ := transitionRange_ok_of_pointwise .Local k1
          1 (off1 + i) cps (fun b h1 h2 => by
            have hb : b = off1 + i := by omega
            subst hb
            have hg := hcget (off1 + i) (by omega)
            have hn1 : ¬ (off1 ≤ off1 + i ∧ off1 + i < off1 + i) := fun ⟨_, _⟩ => by omega
            have hy2 : off1 ≤ off1 + i ∧ off1 + i < off1 + len1 := ⟨by omega, by omega⟩
            simp only [hn1, ↓reduceIte] at hg
            simp only [hy2, and_self, ↓reduceIte] at hg
            exact ⟨p1Init, p1After, hg, htr1⟩)
        refine ⟨⟨[⟨[], cps', .Strong⟩], List.replicate data.length (.Unprot .Unique), .No⟩, ?_,
          ⟨cps', rfl, by rw [hlen', hclen], fun b hb => ?_⟩⟩
        · rw [node_access_rootChild_eq, hrootStep, hrun]; rfl
        · by_cases hbi : b = off1 + i
          · subst hbi
            have hg := hcget (off1 + i) (by omega)
            have hn1 : ¬ (off1 ≤ off1 + i ∧ off1 + i < off1 + i) := fun ⟨_, _⟩ => by omega
            have hy2 : off1 ≤ off1 + i ∧ off1 + i < off1 + len1 := ⟨by omega, by omega⟩
            simp only [hn1, ↓reduceIte] at hg
            simp only [hy2, and_self, ↓reduceIte] at hg
            obtain ⟨p'', htr'', hget'⟩ := hin' (off1 + i) (Nat.le_refl _) (by omega) p1Init hg
            rw [htr1] at htr''; cases htr''
            have hy1 : off1 ≤ off1 + i ∧ off1 + i < off1 + (i + 1) := ⟨by omega, by omega⟩
            simp only [hy1, and_self, ↓reduceIte, hget']
          · rw [hout' b (c1_ne_lt_or_succ_le b (off1 + i) hbi), hcget b hb]
            have hiff : (off1 ≤ b ∧ b < off1 + i) ↔ (off1 ≤ b ∧ b < off1 + (i + 1)) :=
              ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, by omega⟩⟩
            simp only [hiff])
  subst hroot1Eq
  simp only [Nat.zero_add] at hc0Get1
  have hretag1 : TreeBorrowsMemory.retag_ptr
      ({ params := ⟨true⟩, mem := { allocations := [mkRootAllocTB data addr align .Stack], _phantom := ⟨⟩ } } : Gen.TreeBorrowsMemory Gen.x86_64)
      TreeBorrowsMemory.new_call
      { thin_pointer := { addr := addr + (off1 : Int), provenance := some (⟨0⟩, []) },
        metadata := none }
      (.Ref .Mutable (slicePointeeInfoMR len1 al1)) true fnIw1 lookup =
      .ok ({ thin_pointer := { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) },
             metadata := none },
        { params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB data addr align .Stack with
            extra := { root := ⟨[⟨[], c0ps1, .Strong⟩],
              List.replicate data.length (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } },
        { protectors := [(⟨0⟩, [0])] }) := by
    unfold TreeBorrowsMemory.retag_ptr
    rw [c1_reborrowSettings_slice_mut]
    dsimp only [bind, Except.bind, pure, Except.pure, ThinPointer.widen]
    have hreb := c1_reborrow_from_root data addr align [] off1
      { inside := List.replicate len1 (if fnIw1 then .Prot .Unique else .Prot (.Reserved false false)),
        outside := .Prot (.Reserved false false), «protected» := .Strong }
      TreeBorrowsMemory.new_call
      (by rw [List.length_replicate]; exact hlen1)
      (by rw [List.length_replicate]; omega) rfl
      (fun p hp => by rw [List.eq_of_mem_replicate hp]; cases fnIw1 <;> rfl)
    have hmk : ({ params := ⟨true⟩, mem := { allocations := [mkRootAllocTB data addr align .Stack], _phantom := ⟨⟩ } } : Gen.TreeBorrowsMemory Gen.x86_64) =
        { params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB data addr align .Stack with
            extra := { root := ⟨[], List.replicate data.length (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } } := rfl
    rw [hmk] at *
    rw [hreb]
    have hlen0 : ((([] : List Gen.Node).length : Nat) : Int) = 0 := rfl
    simp only [hlen0, List.nil_append, List.length_replicate]
    dsimp only [p1Init, c0Perms0] at hinitRun1
    rw [hinitRun1]; rfl
  have hwf1 : TreeBorrowsMemory.wfLive
      ({ params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB data addr align .Stack with
          extra := { root := ⟨[⟨[], c0ps1, .Strong⟩],
            List.replicate data.length (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } } :
        Gen.TreeBorrowsMemory Gen.x86_64) :=
    TreeBorrowsMemory.retag_ptr_wfLive hwf0 hretag1
  -- Step 2: retag_ptr for [1] on [off2, off2 + len2)
  let c1Perms0 := (List.replicate data.length (.Prot (.Reserved false false))).take off2 ++
    List.replicate len2 p2Init ++
    (List.replicate data.length (.Prot (.Reserved false false))).drop (off2 + len2)
  have hc1Len0 : c1Perms0.length = data.length := by
    simp only [c1Perms0, List.length_append, List.length_take, List.length_drop,
      List.length_replicate]; omega
  have hc1Get0 : ∀ b, b < data.length →
      c1Perms0[b]? = some (if off2 ≤ b ∧ b < off2 + len2 then p2Init else .Prot (.Reserved false false)) := by
    intro b hb
    have heq : c1Perms0 = List.replicate off2 (.Prot (.Reserved false false)) ++
        List.replicate len2 p2Init ++
        List.replicate (data.length - (off2 + len2)) (.Prot (.Reserved false false)) := by
      simp only [c1Perms0, List.take_replicate, List.drop_replicate,
        Nat.min_eq_left (show off2 ≤ data.length by omega)]
    rw [heq]
    exact c1_windowPerms_getElem? data.length off2 len2 (.Prot (.Reserved false false)) p2Init
      (by omega) b hb
  let p0Out2 : Gen.Permission := if fnIw2 then .Prot .Disabled else .Prot (.Reserved false true)
  have hforResEq : Permission.transition (.Prot (.Reserved false false)) k2 .Foreign = .ok p0Out2 := by
    cases fnIw2 <;> rfl
  let P2 : Nat → Gen.Node → Prop := fun i t =>
    ∃ c0ps c1ps,
      t = ⟨[⟨[], c0ps, .Strong⟩, ⟨[], c1ps, .Strong⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩ ∧
      c0ps.length = data.length ∧ c1ps.length = data.length ∧
      (∀ b, b < data.length →
        c0ps[b]? = some (if off1 ≤ b ∧ b < off1 + len1 then p1After
          else if off2 ≤ b ∧ b < off2 + i then p0Out2
          else .Prot (.Reserved false false))) ∧
      (∀ b, b < data.length →
        c1ps[b]? = some (if off2 ≤ b ∧ b < off2 + i then p2After
          else if off2 ≤ b ∧ b < off2 + len2 then p2Init
          else .Prot (.Reserved false false)))
  obtain ⟨root2, hinitRun2, ⟨c0ps2, c1ps2, hroot2Eq, hc0Len2, hc1Len2, hc0Get2, hc1Get2⟩⟩ :=
    c1_reborrowInitAccess_const_ok [1] off2 p2Init k2 hinit2 len2 0
      ⟨[⟨[], c0ps1, .Strong⟩, ⟨[], c1Perms0, .Strong⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩ P2
      ⟨c0ps1, c1Perms0, rfl, hc0Len1, hc1Len0,
        fun b hb => by
          rw [hc0Get1 b hb]
          have h0 : ¬ (off2 ≤ b ∧ b < off2 + 0) := fun ⟨_, _⟩ => by omega
          simp only [h0, ↓reduceIte]
          by_cases h1 : off1 ≤ b ∧ b < off1 + len1
          · simp only [h1, and_self, ↓reduceIte]
          · simp only [h1, ↓reduceIte],
        fun b hb => by
          rw [hc1Get0 b hb]
          have h0 : ¬ (off2 ≤ b ∧ b < off2 + 0) := fun ⟨_, _⟩ => by omega
          simp only [h0, ↓reduceIte]⟩
      (fun i ti _ hi hPi => by
        rcases hPi with ⟨c0p, c1p, hti, hl0, hl1, hg0, hg1⟩
        subst hti
        have hrootStep : Node.transitionRange .Local k2 (off2 + i) 1
            (List.replicate data.length (.Unprot .Unique)) =
            .ok (List.replicate data.length (.Unprot .Unique)) :=
          transitionRange_stable_eq .Local k2 1 (off2 + i) _ (fun b _ h2 =>
            ⟨_, nwsr_getElem?_replicate_lt (by omega), hrootTr k2⟩)
        obtain ⟨c0p', hrun0, hlen0', hout0', hin0'⟩ := transitionRange_ok_of_pointwise .Foreign k2
          1 (off2 + i) c0p (fun b h1 h2 => by
            have hb : b = off2 + i := by omega
            subst hb
            have hg := hg0 (off2 + i) (by omega)
            have hn1 : ¬ (off1 ≤ off2 + i ∧ off2 + i < off1 + len1) := fun ⟨_, _⟩ => by omega
            have hn2 : ¬ (off2 ≤ off2 + i ∧ off2 + i < off2 + i) := fun ⟨_, _⟩ => by omega
            simp only [hn1, ↓reduceIte] at hg
            simp only [hn2, ↓reduceIte] at hg
            exact ⟨.Prot (.Reserved false false), p0Out2, hg, hforResEq⟩)
        obtain ⟨c1p', hrun1, hlen1', hout1', hin1'⟩ := transitionRange_ok_of_pointwise .Local k2
          1 (off2 + i) c1p (fun b h1 h2 => by
            have hb : b = off2 + i := by omega
            subst hb
            have hg := hg1 (off2 + i) (by omega)
            have hn1 : ¬ (off2 ≤ off2 + i ∧ off2 + i < off2 + i) := fun ⟨_, _⟩ => by omega
            have hy2 : off2 ≤ off2 + i ∧ off2 + i < off2 + len2 := ⟨by omega, by omega⟩
            simp only [hn1, ↓reduceIte] at hg
            simp only [hy2, and_self, ↓reduceIte] at hg
            exact ⟨p2Init, p2After, hg, htr2⟩)
        refine ⟨⟨[⟨[], c0p', .Strong⟩, ⟨[], c1p', .Strong⟩],
          List.replicate data.length (.Unprot .Unique), .No⟩, ?_,
          ⟨c0p', c1p', rfl, by rw [hlen0', hl0], by rw [hlen1', hl1], ?_, ?_⟩⟩
        · rw [c1_node_access_twoChildren]
          have hloc0 : locRel (some [(1 : Int)]) [] = .Local := rfl
          have hs0 : subPathAt (some [(1 : Int)]) 0 = none := rfl
          have hs1 : subPathAt (some [(1 : Int)]) 1 = some [] := rfl
          rw [hloc0, hs0, hs1, hrootStep]
          show (Node.access ⟨[], c0p, .Strong⟩ none k2 ⟨off2 + i⟩ ⟨1⟩ >>= fun c0' =>
            Node.access ⟨[], c1p, .Strong⟩ (some []) k2 ⟨off2 + i⟩ ⟨1⟩ >>= fun c1' => pure _) = _
          rw [nwsr_access_eq, nwsr_access_eq]
          have hlf : locRel none [] = .Foreign := rfl
          have hll : locRel (some ([] : Gen.Path)) [] = .Local := rfl
          rw [hlf, hll, hrun0, hrun1, Node.accessChildren]; rfl
        · intro b hb
          by_cases hbi : b = off2 + i
          · subst hbi
            have hg := hg0 (off2 + i) (by omega)
            have hn1 : ¬ (off1 ≤ off2 + i ∧ off2 + i < off1 + len1) := fun ⟨_, _⟩ => by omega
            have hn2 : ¬ (off2 ≤ off2 + i ∧ off2 + i < off2 + i) := fun ⟨_, _⟩ => by omega
            simp only [hn1, ↓reduceIte] at hg
            simp only [hn2, ↓reduceIte] at hg
            obtain ⟨p'', htr'', hget'⟩ := hin0' (off2 + i) (Nat.le_refl _) (by omega) _ hg
            rw [hforResEq] at htr''; cases htr''
            have hy2 : off2 ≤ off2 + i ∧ off2 + i < off2 + (i + 1) := ⟨by omega, by omega⟩
            simp only [hn1, hy2, and_self, ↓reduceIte, hget']
          · rw [hout0' b (c1_ne_lt_or_succ_le b (off2 + i) hbi), hg0 b hb]
            have hiff : (off2 ≤ b ∧ b < off2 + i) ↔ (off2 ≤ b ∧ b < off2 + (i + 1)) :=
              ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, by omega⟩⟩
            simp only [hiff]
        · intro b hb
          by_cases hbi : b = off2 + i
          · subst hbi
            have hg := hg1 (off2 + i) (by omega)
            have hn1 : ¬ (off2 ≤ off2 + i ∧ off2 + i < off2 + i) := fun ⟨_, _⟩ => by omega
            have hy2 : off2 ≤ off2 + i ∧ off2 + i < off2 + len2 := ⟨by omega, by omega⟩
            simp only [hn1, ↓reduceIte] at hg
            simp only [hy2, and_self, ↓reduceIte] at hg
            obtain ⟨p'', htr'', hget'⟩ := hin1' (off2 + i) (Nat.le_refl _) (by omega) _ hg
            rw [htr2] at htr''; cases htr''
            have hy1 : off2 ≤ off2 + i ∧ off2 + i < off2 + (i + 1) := ⟨by omega, by omega⟩
            simp only [hy1, and_self, ↓reduceIte, hget']
          · rw [hout1' b (c1_ne_lt_or_succ_le b (off2 + i) hbi), hg1 b hb]
            have hiff : (off2 ≤ b ∧ b < off2 + i) ↔ (off2 ≤ b ∧ b < off2 + (i + 1)) :=
              ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, by omega⟩⟩
            simp only [hiff])
  subst hroot2Eq
  simp only [Nat.zero_add] at hc0Get2 hc1Get2
  let tbm2 : Gen.TreeBorrowsMemory Gen.x86_64 :=
    { params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB data addr align .Stack with
        extra := { root := ⟨[⟨[], c0ps2, .Strong⟩, ⟨[], c1ps2, .Strong⟩],
          List.replicate data.length (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } }
  have hretag2 : TreeBorrowsMemory.retag_ptr
      ({ params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB data addr align .Stack with
          extra := { root := ⟨[⟨[], c0ps1, .Strong⟩],
            List.replicate data.length (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } } :
        Gen.TreeBorrowsMemory Gen.x86_64)
      { protectors := [(⟨0⟩, [0])] }
      { thin_pointer := { addr := addr + (off2 : Int), provenance := some (⟨0⟩, []) },
        metadata := none }
      (.Ref .Mutable (slicePointeeInfoMR len2 al2)) true fnIw2 lookup =
      .ok ({ thin_pointer := { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) },
             metadata := none },
        tbm2, { protectors := [(⟨0⟩, [0]), (⟨0⟩, [1])] }) := by
    unfold TreeBorrowsMemory.retag_ptr
    rw [c1_reborrowSettings_slice_mut]
    dsimp only [bind, Except.bind, pure, Except.pure, ThinPointer.widen]
    rw [c1_reborrow_from_root data addr align [⟨[], c0ps1, .Strong⟩] off2 _ _
      (by rw [List.length_replicate]; exact hlen2)
      (by rw [List.length_replicate]; omega) rfl
      (fun p hp => by rw [List.eq_of_mem_replicate hp]; cases fnIw2 <;> rfl)]
    have hlen1' : ((([⟨[], c0ps1, .Strong⟩] : List Gen.Node).length : Nat) : Int) = 1 := rfl
    simp only [hlen1', List.cons_append, List.nil_append, List.length_replicate]
    dsimp only [p2Init, c1Perms0] at hinitRun2
    rw [hinitRun2]; rfl
  have hwf2 : TreeBorrowsMemory.wfLive tbm2 := TreeBorrowsMemory.retag_ptr_wfLive hwf1 hretag2
  -- Step 3: stores on [off1, off1 + len1) via [0] and [off2, off2 + len2) via [1]
  have hp1W : Permission.transition p1After .Write .Local = .ok (.Prot .Unique) := by
    cases fnIw1 <;> rfl
  have hp2W : Permission.transition p2After .Write .Local = .ok (.Prot .Unique) := by
    cases fnIw2 <;> rfl
  have hp0OutW : Permission.transition p0Out2 .Write .Foreign = .ok (.Prot .Disabled) := by
    cases fnIw2 <;> rfl
  have hrootW1 : Node.transitionRange .Local .Write off1 len1
      (List.replicate data.length (.Unprot .Unique)) =
      .ok (List.replicate data.length (.Unprot .Unique)) :=
    transitionRange_stable_eq .Local .Write len1 off1 _ (fun b _ h2 =>
      ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
  obtain ⟨c0s, hc0r, hc0l, hc0o, hc0i⟩ := transitionRange_ok_of_pointwise .Local .Write
    len1 off1 c0ps2 (fun b h1 h2 => by
      have hg := hc0Get2 b (by omega)
      simp only [h1, h2, and_self, ↓reduceIte] at hg
      exact ⟨p1After, .Prot .Unique, hg, hp1W⟩)
  obtain ⟨c1s, hc1r, hc1l, hc1o, hc1i⟩ := transitionRange_ok_of_pointwise .Foreign .Write
    len1 off1 c1ps2 (fun b h1 h2 => by
      have hg := hc1Get2 b (by omega)
      have hn2 : ¬ (off2 ≤ b ∧ b < off2 + len2) := fun ⟨_, _⟩ => by omega
      simp only [hn2, ↓reduceIte] at hg
      exact ⟨.Prot (.Reserved false false), .Prot .Disabled, hg, rfl⟩)
  have hacc1 : Node.access ⟨[⟨[], c0ps2, .Strong⟩, ⟨[], c1ps2, .Strong⟩],
      List.replicate data.length (.Unprot .Unique), .No⟩ (some [0]) .Write ⟨off1⟩ ⟨len1⟩ =
      .ok ⟨[⟨[], c0s, .Strong⟩, ⟨[], c1s, .Strong⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩ := by
    rw [c1_node_access_twoChildren]
    have hloc0 : locRel (some [(0 : Int)]) [] = .Local := rfl
    have hs0 : subPathAt (some [(0 : Int)]) 0 = some [] := rfl
    have hs1 : subPathAt (some [(0 : Int)]) 1 = none := rfl
    rw [hloc0, hs0, hs1, hrootW1]
    show (Node.access ⟨[], c0ps2, .Strong⟩ (some []) .Write ⟨off1⟩ ⟨len1⟩ >>= fun c0' =>
      Node.access ⟨[], c1ps2, .Strong⟩ none .Write ⟨off1⟩ ⟨len1⟩ >>= fun c1' => pure _) = _
    rw [nwsr_access_eq, nwsr_access_eq]
    have hll : locRel (some ([] : Gen.Path)) [] = .Local := rfl
    have hlf : locRel none [] = .Foreign := rfl
    rw [hll, hlf, hc0r, hc1r, Node.accessChildren]; rfl
  have hc0sGet : ∀ b, b < data.length →
      c0s[b]? = some (if off1 ≤ b ∧ b < off1 + len1 then .Prot .Unique
        else if off2 ≤ b ∧ b < off2 + len2 then p0Out2 else .Prot (.Reserved false false)) := by
    intro b hb
    rcases c1_in_or_out off1 len1 b with ⟨h1, h2⟩ | hout
    · have hg := hc0Get2 b hb
      simp only [h1, h2, and_self, ↓reduceIte] at hg ⊢
      obtain ⟨p'', htr'', hget'⟩ := hc0i b h1 h2 p1After hg
      rw [hp1W] at htr''; cases htr''; exact hget'
    · rw [hc0o b hout, hc0Get2 b hb]
      have hn1 : ¬ (off1 ≤ b ∧ b < off1 + len1) := fun ⟨_, _⟩ => by omega
      simp only [hn1, ↓reduceIte]
  have hc1sGet : ∀ b, b < data.length →
      c1s[b]? = some (if off1 ≤ b ∧ b < off1 + len1 then .Prot .Disabled
        else if off2 ≤ b ∧ b < off2 + len2 then p2After else .Prot (.Reserved false false)) := by
    intro b hb
    rcases c1_in_or_out off1 len1 b with ⟨h1, h2⟩ | hout
    · have hg := hc1Get2 b hb
      have hn2 : ¬ (off2 ≤ b ∧ b < off2 + len2) := fun ⟨_, _⟩ => by omega
      simp only [hn2, ↓reduceIte] at hg
      simp only [h1, h2, and_self, ↓reduceIte]
      obtain ⟨p'', htr'', hget'⟩ := hc1i b h1 h2 _ hg
      cases htr''; exact hget'
    · rw [hc1o b hout, hc1Get2 b hb]
      have hn1 : ¬ (off1 ≤ b ∧ b < off1 + len1) := fun ⟨_, _⟩ => by omega
      simp only [hn1, ↓reduceIte]
      by_cases h2 : off2 ≤ b ∧ b < off2 + len2
      · simp only [h2, and_self, ↓reduceIte]
      · simp only [h2, ↓reduceIte]
  have hrootW2 : Node.transitionRange .Local .Write off2 len2
      (List.replicate data.length (.Unprot .Unique)) =
      .ok (List.replicate data.length (.Unprot .Unique)) :=
    transitionRange_stable_eq .Local .Write len2 off2 _ (fun b _ h2 =>
      ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
  obtain ⟨c0f, hc0r2, hc0l2, hc0o2, hc0i2⟩ := transitionRange_ok_of_pointwise .Foreign .Write
    len2 off2 c0s (fun b h1 h2 => by
      have hg := hc0sGet b (by omega)
      have hn1 : ¬ (off1 ≤ b ∧ b < off1 + len1) := fun ⟨_, _⟩ => by omega
      simp only [hn1, ↓reduceIte] at hg
      simp only [h1, h2, and_self, ↓reduceIte] at hg
      exact ⟨p0Out2, .Prot .Disabled, hg, hp0OutW⟩)
  obtain ⟨c1f, hc1r2, hc1l2, hc1o2, hc1i2⟩ := transitionRange_ok_of_pointwise .Local .Write
    len2 off2 c1s (fun b h1 h2 => by
      have hg := hc1sGet b (by omega)
      have hn1 : ¬ (off1 ≤ b ∧ b < off1 + len1) := fun ⟨_, _⟩ => by omega
      simp only [hn1, ↓reduceIte] at hg
      simp only [h1, h2, and_self, ↓reduceIte] at hg
      exact ⟨p2After, .Prot .Unique, hg, hp2W⟩)
  have hacc2 : Node.access ⟨[⟨[], c0s, .Strong⟩, ⟨[], c1s, .Strong⟩],
      List.replicate data.length (.Unprot .Unique), .No⟩ (some [1]) .Write ⟨off2⟩ ⟨len2⟩ =
      .ok ⟨[⟨[], c0f, .Strong⟩, ⟨[], c1f, .Strong⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩ := by
    rw [c1_node_access_twoChildren]
    have hloc0 : locRel (some [(1 : Int)]) [] = .Local := rfl
    have hs0 : subPathAt (some [(1 : Int)]) 0 = none := rfl
    have hs1 : subPathAt (some [(1 : Int)]) 1 = some [] := rfl
    rw [hloc0, hs0, hs1, hrootW2]
    show (Node.access ⟨[], c0s, .Strong⟩ none .Write ⟨off2⟩ ⟨len2⟩ >>= fun c0' =>
      Node.access ⟨[], c1s, .Strong⟩ (some []) .Write ⟨off2⟩ ⟨len2⟩ >>= fun c1' => pure _) = _
    rw [nwsr_access_eq, nwsr_access_eq]
    have hll : locRel (some ([] : Gen.Path)) [] = .Local := rfl
    have hlf : locRel none [] = .Foreign := rfl
    rw [hll, hlf, hc0r2, hc1r2, Node.accessChildren]; rfl
  have hc0fGet : ∀ b, b < data.length →
      c0f[b]? = some (if off1 ≤ b ∧ b < off1 + len1 then .Prot .Unique
        else if off2 ≤ b ∧ b < off2 + len2 then .Prot .Disabled
        else .Prot (.Reserved false false)) := by
    intro b hb
    rcases c1_in_or_out off2 len2 b with ⟨h1, h2⟩ | hout
    · have hg := hc0sGet b hb
      have hn1 : ¬ (off1 ≤ b ∧ b < off1 + len1) := fun ⟨_, _⟩ => by omega
      simp only [hn1, ↓reduceIte] at hg ⊢
      simp only [h1, h2, and_self, ↓reduceIte] at hg ⊢
      obtain ⟨p'', htr'', hget'⟩ := hc0i2 b h1 h2 p0Out2 hg
      rw [hp0OutW] at htr''; cases htr''; exact hget'
    · rw [hc0o2 b hout, hc0sGet b hb]
      have hn2 : ¬ (off2 ≤ b ∧ b < off2 + len2) := fun ⟨_, _⟩ => by omega
      simp only [hn2, ↓reduceIte]
  have hc1fGet : ∀ b, b < data.length →
      c1f[b]? = some (if off1 ≤ b ∧ b < off1 + len1 then .Prot .Disabled
        else if off2 ≤ b ∧ b < off2 + len2 then .Prot .Unique
        else .Prot (.Reserved false false)) := by
    intro b hb
    rcases c1_in_or_out off2 len2 b with ⟨h1, h2⟩ | hout
    · have hg := hc1sGet b hb
      have hn1 : ¬ (off1 ≤ b ∧ b < off1 + len1) := fun ⟨_, _⟩ => by omega
      simp only [hn1, ↓reduceIte] at hg ⊢
      simp only [h1, h2, and_self, ↓reduceIte] at hg ⊢
      obtain ⟨p'', htr'', hget'⟩ := hc1i2 b h1 h2 p2After hg
      rw [hp2W] at htr''; cases htr''; exact hget'
    · rw [hc1o2 b hout, hc1sGet b hb]
      have hn2 : ¬ (off2 ≤ b ∧ b < off2 + len2) := fun ⟨_, _⟩ => by omega
      simp only [hn2, ↓reduceIte]
  let data1 := data.take off1 ++ wBytes1 ++ data.drop (off1 + len1)
  have hdata1Len : data1.length = data.length := by
    simp only [data1, List.length_append, List.length_take, List.length_drop, hw1]; omega
  let tbmS1 : Gen.TreeBorrowsMemory Gen.x86_64 :=
    { tbm2 with mem := { tbm2.mem with allocations := [{
        mkRootAllocTB data addr align .Stack with
        data := data1,
        extra := { root := ⟨[⟨[], c0s, .Strong⟩, ⟨[], c1s, .Strong⟩],
          List.replicate data.length (.Unprot .Unique), .No⟩ } }] } }
  have hstore1 : TreeBorrowsMemory.store tbm2
      { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } wBytes1 ⟨al1⟩ = .ok tbmS1 := by
    have heq := tbm_store_eq_node_access tbm2
      { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } wBytes1 ⟨al1⟩ 0 [0] _
      off1 rfl rfl rfl hal1 (by show addr + (off1 : Int) - addr = (off1 : Int); omega)
      (by omega) (by show off1 + wBytes1.length ≤ data.length; omega)
    rw [heq, hw1, hacc1]; rfl
  let data12 := data1.take off2 ++ wBytes2 ++ data1.drop (off2 + len2)
  have hdata12Len : data12.length = data.length := by
    simp only [data12, List.length_append, List.length_take, List.length_drop, hw2, hdata1Len]; omega
  let rootF : Gen.Node := ⟨[⟨[], c0f, .Strong⟩, ⟨[], c1f, .Strong⟩],
    List.replicate data.length (.Unprot .Unique), .No⟩
  let tbm12 : Gen.TreeBorrowsMemory Gen.x86_64 :=
    { params := ⟨true⟩, mem := { allocations := [{
        mkRootAllocTB data12 addr align .Stack with extra := { root := rootF } }], _phantom := ⟨⟩ } }
  have hstore12 : TreeBorrowsMemory.store tbmS1
      { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩ = .ok tbm12 := by
    have heq := tbm_store_eq_node_access tbmS1
      { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩ 0 [1] _
      off2 rfl rfl rfl hal2 (by show addr + (off2 : Int) - addr = (off2 : Int); omega)
      (by omega) (by show off2 + wBytes2.length ≤ data1.length; rw [hdata1Len]; omega)
    rw [heq, hw2, hacc2]; rfl
  obtain ⟨rootRev1, haccRev1, haccRev2⟩ :=
    (node_access_comm_of_disjoint
      ⟨[⟨[], c0ps2, .Strong⟩, ⟨[], c1ps2, .Strong⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩
      (some [0]) (some [1]) .Write .Write off1 len1 off2 len2 (Or.inl hdisj)).1
      _ rootF hacc1 hacc2
  let data2 := data.take off2 ++ wBytes2 ++ data.drop (off2 + len2)
  have hdata2Len : data2.length = data.length := by
    simp only [data2, List.length_append, List.length_take, List.length_drop, hw2]; omega
  let tbmS2 : Gen.TreeBorrowsMemory Gen.x86_64 :=
    { tbm2 with mem := { tbm2.mem with allocations := [{
        mkRootAllocTB data addr align .Stack with
        data := data2, extra := { root := rootRev1 } }] } }
  have hstore2 : TreeBorrowsMemory.store tbm2
      { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩ = .ok tbmS2 := by
    have heq := tbm_store_eq_node_access tbm2
      { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩ 0 [1] _
      off2 rfl rfl rfl hal2 (by show addr + (off2 : Int) - addr = (off2 : Int); omega)
      (by omega) (by show off2 + wBytes2.length ≤ data.length; omega)
    rw [heq, hw2, haccRev1]; rfl
  let data21 := data2.take off1 ++ wBytes1 ++ data2.drop (off1 + len1)
  let tbm21 : Gen.TreeBorrowsMemory Gen.x86_64 :=
    { tbmS2 with mem := { tbmS2.mem with allocations := [{
        mkRootAllocTB data addr align .Stack with
        data := data21, extra := { root := rootF } }] } }
  have hstore21 : TreeBorrowsMemory.store tbmS2
      { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } wBytes1 ⟨al1⟩ = .ok tbm21 := by
    have heq := tbm_store_eq_node_access tbmS2
      { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } wBytes1 ⟨al1⟩ 0 [0] _
      off1 rfl rfl rfl hal1 (by show addr + (off1 : Int) - addr = (off1 : Int); omega)
      (by omega) (by show off1 + wBytes1.length ≤ data2.length; rw [hdata2Len]; omega)
    rw [heq, hw1, haccRev2]; rfl
  -- Step 4: end_call in both orders via c1_slice_disjoint_splitAtMut_endCalls!
  obtain ⟨tbmEndFwd, tbmEndRev, hEndFwd, hwfFwd, hEndRev, hwfRev⟩ :=
    c1_slice_disjoint_splitAtMut_endCalls data12 addr align off1 len1 off2 len2 hdisj
      (by rw [hdata12Len]; exact hbound) c0f c1f
      (by rw [hc0l2, hc0l, hc0Len2, hdata12Len])
      (by rw [hc1l2, hc1l, hc1Len2, hdata12Len])
      (fun b hb => hc0fGet b (by rw [← hdata12Len]; exact hb))
      (fun b hb => hc1fGet b (by rw [← hdata12Len]; exact hb))
  have htbm12Eq : tbm12 =
      { params := ⟨true⟩, mem := { allocations := [{
          mkRootAllocTB data12 addr align .Stack with
          extra := { root := ⟨[⟨[], c0f, .Strong⟩, ⟨[], c1f, .Strong⟩],
            List.replicate data12.length (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } } := by
    simp only [tbm12, rootF, hdata12Len]
  rw [← htbm12Eq] at hEndFwd hEndRev
  refine ⟨_, tbm2, { protectors := [(⟨0⟩, [0])] }, { protectors := [(⟨0⟩, [0]), (⟨0⟩, [1])] },
    tbm12, tbm21, tbmEndFwd, tbmEndRev,
    hretag1, hretag2, rfl, hwf2, ?_, ?_, rfl, hEndFwd, hwfFwd, hEndRev, hwfRev⟩
  · rw [hstore1]; exact hstore12
  · rw [hstore2]; exact hstore21

private theorem c1_slice_getMut_perByte_refinement
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int) (align : Nat)
    (off1 len1 off2 len2 : Nat)
    (hlen1 : 0 < len1) (hlen2 : 0 < len2)
    (hdisj : off1 + len1 ≤ off2) (hbound : off2 + len2 ≤ data.length)
    (wBytes2 : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (hw2 : wBytes2.length = len2)
    (al1 al2 : Nat)
    (hal1 : Align.is_aligned ⟨al1⟩ (addr + (off1 : Int)) = true)
    (hal2 : Align.is_aligned ⟨al2⟩ (addr + (off2 : Int)) = true)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable) :
    let tbm0 : Gen.TreeBorrowsMemory Gen.x86_64 :=
      { params := ⟨true⟩
        mem := { allocations := [mkRootAllocTB data addr align .Stack], _phantom := ⟨⟩ } }
    let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
      { thin_pointer := { addr := addr, provenance := some (⟨0⟩, []) }, metadata := none }
    ∃ tbmS tbmM feM tbmW tbmE tbmRd,
      TreeBorrowsMemory.retag_ptr tbm0 TreeBorrowsMemory.new_call rootPtr
          (.Ref .Immutable (slicePointeeInfoMR data.length align)) false true lookup =
        .ok ({ thin_pointer := { addr := addr, provenance := some (⟨0⟩, [0]) },
               metadata := none }, tbmS, TreeBorrowsMemory.new_call) ∧
      TreeBorrowsMemory.retag_ptr tbmS TreeBorrowsMemory.new_call rootPtr
          (.Ref .Mutable (slicePointeeInfoMR data.length align)) true false lookup =
        .ok ({ thin_pointer := { addr := addr, provenance := some (⟨0⟩, [1]) },
               metadata := none }, tbmM, feM) ∧
      TreeBorrowsMemory.store tbmM
          { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩ = .ok tbmW ∧
      TreeBorrowsMemory.end_call tbmW feM = .ok tbmE ∧
      TreeBorrowsMemory.wfLive tbmE ∧
      TreeBorrowsMemory.load tbmE
          { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } ⟨len1⟩ ⟨al1⟩ =
        .ok ((data.drop off1).take len1, tbmRd) ∧
      TreeBorrowsMemory.wfLive tbmRd ∧
      TreeBorrowsMemory.load tbmE
          { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [0]) } ⟨len2⟩ ⟨al2⟩ =
        .error (.ub "Tree Borrows: local read of Disabled reference") := by
  dsimp only
  have hwf0 : TreeBorrowsMemory.wfLive
      ({ params := ⟨true⟩, mem := { allocations := [mkRootAllocTB data addr align .Stack], _phantom := ⟨⟩ } } : Gen.TreeBorrowsMemory Gen.x86_64) := by
    intro alloc ha _
    have := List.mem_singleton.mp ha
    subst this
    exact mkRootAllocTB_wf data addr align .Stack
  have hdataPos : 0 < data.length := by omega
  let tbmS : Gen.TreeBorrowsMemory Gen.x86_64 :=
    { params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB data addr align .Stack with
        extra := { root := ⟨[⟨[], List.replicate data.length (.Unprot .Frozen), .No⟩],
          List.replicate data.length (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } }
  have hretagS : TreeBorrowsMemory.retag_ptr
      ({ params := ⟨true⟩, mem := { allocations := [mkRootAllocTB data addr align .Stack], _phantom := ⟨⟩ } } : Gen.TreeBorrowsMemory Gen.x86_64)
      TreeBorrowsMemory.new_call
      { thin_pointer := { addr := addr, provenance := some (⟨0⟩, []) }, metadata := none }
      (.Ref .Immutable (slicePointeeInfoMR data.length align)) false true lookup =
      .ok ({ thin_pointer := { addr := addr, provenance := some (⟨0⟩, [0]) }, metadata := none },
        tbmS, TreeBorrowsMemory.new_call) := by
    unfold TreeBorrowsMemory.retag_ptr
    rw [c1_reborrowSettings_slice_shr]
    dsimp only [bind, Except.bind, pure, Except.pure, ThinPointer.widen]
    have haddr0 : addr = addr + ((0 : Nat) : Int) := by omega
    have hmk : ({ params := ⟨true⟩, mem := { allocations := [mkRootAllocTB data addr align .Stack], _phantom := ⟨⟩ } } : Gen.TreeBorrowsMemory Gen.x86_64) =
        { params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB data addr align .Stack with
            extra := { root := ⟨[], List.replicate data.length (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } } := rfl
    have hreb := c1_reborrow_from_root data addr align [] 0
      { inside := List.replicate data.length (.Unprot .Frozen),
        outside := .Unprot .Frozen, «protected» := .No }
      TreeBorrowsMemory.new_call (by rw [List.length_replicate]; exact hdataPos)
      (by rw [List.length_replicate]; omega) rfl
      (fun p hp => by rw [List.eq_of_mem_replicate hp]; rfl)
    rw [← haddr0] at hreb
    rw [hmk] at *
    rw [hreb]
    have hsub : (List.replicate data.length (Gen.Permission.Unprot .Frozen)).take 0 ++
        List.replicate data.length (Gen.Permission.Unprot .Frozen) ++
        (List.replicate data.length (Gen.Permission.Unprot .Frozen)).drop (0 + data.length) =
        List.replicate data.length (Gen.Permission.Unprot .Frozen) := by
      rw [List.take_zero, List.nil_append, Nat.zero_add,
        List.drop_eq_nil_of_le (by rw [List.length_replicate]; exact Nat.le_refl _),
        List.append_nil]
    have hlen0 : ((([] : List Gen.Node).length : Nat) : Int) = 0 := rfl
    simp only [hlen0, List.nil_append, List.length_replicate, hsub]
    obtain ⟨r', hr', heq'⟩ := c1_reborrowInitAccess_const_ok [0] 0 (.Unprot .Frozen) .Read rfl
      data.length 0
      ⟨[⟨[], List.replicate data.length (.Unprot .Frozen), .No⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩
      (fun _ t => t = ⟨[⟨[], List.replicate data.length (.Unprot .Frozen), .No⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩)
      rfl
      (fun i ti _ hi hti => by
        subst hti
        refine ⟨_, ?_, rfl⟩
        rw [node_access_rootChild_eq,
          transitionRange_stable_eq .Local .Read 1 (0 + i) _ (fun b _ h2 =>
            ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩),
          transitionRange_stable_eq .Local .Read 1 (0 + i) _ (fun b _ h2 =>
            ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩)]
        rfl)
    rw [hr', heq']; rfl
  let P3 : Nat → Gen.Node → Prop := fun i t =>
    ∃ c1ps, t = ⟨[⟨[], List.replicate data.length (.Unprot .Frozen), .No⟩,
        ⟨[], c1ps, .Strong⟩], List.replicate data.length (.Unprot .Unique), .No⟩ ∧
      c1ps.length = data.length ∧
      ∀ b, b < data.length →
        c1ps[b]? = some (if b < i then .Prot (.Reserved true false) else .Prot (.Reserved false false))
  obtain ⟨rootM, hinitM, ⟨c1psM, hrootMEq, hc1MLen, hc1MGet⟩⟩ :=
    c1_reborrowInitAccess_const_ok [1] 0 (.Prot (.Reserved false false)) .Read rfl
      data.length 0
      ⟨[⟨[], List.replicate data.length (.Unprot .Frozen), .No⟩,
        ⟨[], List.replicate data.length (.Prot (.Reserved false false)), .Strong⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩ P3
      ⟨List.replicate data.length (.Prot (.Reserved false false)), rfl, List.length_replicate,
        fun b hb => by
          have h0 : ¬ b < 0 := fun _ => by omega
          simp only [h0, ↓reduceIte]
          exact nwsr_getElem?_replicate_lt hb⟩
      (fun i ti _ hi hPi => by
        rcases hPi with ⟨c1p, hti, hlen1, hg1⟩
        subst hti
        have hrootR : Node.transitionRange .Local .Read (0 + i) 1
            (List.replicate data.length (.Unprot .Unique)) =
            .ok (List.replicate data.length (.Unprot .Unique)) :=
          transitionRange_stable_eq .Local .Read 1 (0 + i) _ (fun b _ h2 =>
            ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
        have hsibR : Node.transitionRange .Foreign .Read (0 + i) 1
            (List.replicate data.length (.Unprot .Frozen)) =
            .ok (List.replicate data.length (.Unprot .Frozen)) :=
          transitionRange_stable_eq .Foreign .Read 1 (0 + i) _ (fun b _ h2 =>
            ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
        obtain ⟨c1p', hrun1, hlen1', hout1', hin1'⟩ := transitionRange_ok_of_pointwise .Local .Read
          1 (0 + i) c1p (fun b h1 h2 => by
            have hb : b = i := by omega
            subst b
            have hg := hg1 i (by omega)
            have hn : ¬ i < i := fun _ => by omega
            simp only [hn, ↓reduceIte] at hg
            exact ⟨.Prot (.Reserved false false), .Prot (.Reserved true false), hg, rfl⟩)
        refine ⟨⟨[⟨[], List.replicate data.length (.Unprot .Frozen), .No⟩,
            ⟨[], c1p', .Strong⟩], List.replicate data.length (.Unprot .Unique), .No⟩, ?_,
          ⟨c1p', rfl, by rw [hlen1', hlen1], fun b hb => ?_⟩⟩
        · rw [c1_node_access_twoChildren]
          have hloc0 : locRel (some [(1 : Int)]) [] = .Local := rfl
          have hs0 : subPathAt (some [(1 : Int)]) 0 = none := rfl
          have hs1 : subPathAt (some [(1 : Int)]) 1 = some [] := rfl
          rw [hloc0, hs0, hs1, hrootR]
          show (Node.access _ none .Read ⟨0 + i⟩ ⟨1⟩ >>= fun c0' =>
            Node.access _ (some []) .Read ⟨0 + i⟩ ⟨1⟩ >>= fun c1' => pure _) = _
          rw [nwsr_access_eq, nwsr_access_eq]
          have hlf : locRel none [] = .Foreign := rfl
          have hll : locRel (some ([] : Gen.Path)) [] = .Local := rfl
          rw [hlf, hll, hsibR, hrun1, Node.accessChildren]; rfl
        · by_cases hbi : b = i
          · subst b
            have hg := hg1 i (by omega)
            have hn : ¬ i < i := fun _ => by omega
            simp only [hn, ↓reduceIte] at hg
            obtain ⟨p'', htr'', hget'⟩ := hin1' i (by omega) (by omega) _ hg
            cases htr''
            have hy : i < i + 1 := by omega
            simp only [hy, ↓reduceIte, hget']
          · rw [hout1' b (by rw [Nat.zero_add]; exact c1_ne_lt_or_succ_le b i hbi), hg1 b hb]
            have hiff : (b < i) ↔ (b < i + 1) := ⟨fun h => by omega, fun h => by omega⟩
            simp only [hiff])
  subst hrootMEq
  simp only [Nat.zero_add] at hc1MGet
  have hc1MEq : c1psM = List.replicate data.length (.Prot (.Reserved true false)) := by
    apply List.ext_getElem?
    intro b
    rcases Nat.lt_or_ge b data.length with hb | hb
    · rw [hc1MGet b hb, nwsr_getElem?_replicate_lt hb]
      simp only [hb, ↓reduceIte]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by rw [List.length_replicate]; omega)]
  subst hc1MEq
  let tbmM : Gen.TreeBorrowsMemory Gen.x86_64 :=
    { params := ⟨true⟩, mem := { allocations := [{ mkRootAllocTB data addr align .Stack with
        extra := { root := ⟨[⟨[], List.replicate data.length (.Unprot .Frozen), .No⟩,
          ⟨[], List.replicate data.length (.Prot (.Reserved true false)), .Strong⟩],
          List.replicate data.length (.Unprot .Unique), .No⟩ } }], _phantom := ⟨⟩ } }
  have hretagM : TreeBorrowsMemory.retag_ptr tbmS TreeBorrowsMemory.new_call
      { thin_pointer := { addr := addr, provenance := some (⟨0⟩, []) }, metadata := none }
      (.Ref .Mutable (slicePointeeInfoMR data.length align)) true false lookup =
      .ok ({ thin_pointer := { addr := addr, provenance := some (⟨0⟩, [1]) }, metadata := none },
        tbmM, { protectors := [(⟨0⟩, [1])] }) := by
    unfold TreeBorrowsMemory.retag_ptr
    rw [c1_reborrowSettings_slice_mut]
    dsimp only [bind, Except.bind, pure, Except.pure, ThinPointer.widen]
    have haddr0 : addr = addr + ((0 : Nat) : Int) := by omega
    have hreb := c1_reborrow_from_root data addr align
      [⟨[], List.replicate data.length (.Unprot .Frozen), .No⟩] 0
      { inside := List.replicate data.length (.Prot (.Reserved false false)),
        outside := .Prot (.Reserved false false), «protected» := .Strong }
      TreeBorrowsMemory.new_call (by rw [List.length_replicate]; exact hdataPos)
      (by rw [List.length_replicate]; omega) rfl
      (fun p hp => by rw [List.eq_of_mem_replicate hp]; rfl)
    rw [← haddr0] at hreb
    dsimp only at hreb
    dsimp only [tbmS]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hreb]
    have hsub : (List.replicate data.length (Gen.Permission.Prot (.Reserved false false))).take 0 ++
        List.replicate data.length (Gen.Permission.Prot (.Reserved false false)) ++
        (List.replicate data.length (Gen.Permission.Prot (.Reserved false false))).drop (0 + data.length) =
        List.replicate data.length (Gen.Permission.Prot (.Reserved false false)) := by
      rw [List.take_zero, List.nil_append, Nat.zero_add,
        List.drop_eq_nil_of_le (by rw [List.length_replicate]; exact Nat.le_refl _),
        List.append_nil]
    have hlen1' : ((([⟨[], List.replicate data.length (.Unprot .Frozen), .No⟩] : List Gen.Node).length : Nat) : Int) = 1 := rfl
    simp only [hlen1', List.cons_append, List.nil_append, List.length_replicate, hsub]
    rw [hinitM]; rfl
  have hrootW : Node.transitionRange .Local .Write off2 len2
      (List.replicate data.length (.Unprot .Unique)) =
      .ok (List.replicate data.length (.Unprot .Unique)) :=
    transitionRange_stable_eq .Local .Write len2 off2 _ (fun b _ h2 =>
      ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
  obtain ⟨sibW, hsibWr, hsibWl, hsibWo, hsibWi⟩ := transitionRange_ok_of_pointwise .Foreign .Write
    len2 off2 (List.replicate data.length (.Unprot .Frozen)) (fun b _ h2 =>
      ⟨.Unprot .Frozen, .Unprot .Disabled, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
  obtain ⟨mutW, hmutWr, hmutWl, hmutWo, hmutWi⟩ := transitionRange_ok_of_pointwise .Local .Write
    len2 off2 (List.replicate data.length (.Prot (.Reserved true false))) (fun b _ h2 =>
      ⟨.Prot (.Reserved true false), .Prot .Unique, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
  have haccW : Node.access
      ⟨[⟨[], List.replicate data.length (.Unprot .Frozen), .No⟩,
        ⟨[], List.replicate data.length (.Prot (.Reserved true false)), .Strong⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩
      (some [1]) .Write ⟨off2⟩ ⟨len2⟩ =
      .ok ⟨[⟨[], sibW, .No⟩, ⟨[], mutW, .Strong⟩],
        List.replicate data.length (.Unprot .Unique), .No⟩ := by
    rw [c1_node_access_twoChildren]
    have hloc0 : locRel (some [(1 : Int)]) [] = .Local := rfl
    have hs0 : subPathAt (some [(1 : Int)]) 0 = none := rfl
    have hs1 : subPathAt (some [(1 : Int)]) 1 = some [] := rfl
    rw [hloc0, hs0, hs1, hrootW]
    show (Node.access _ none .Write ⟨off2⟩ ⟨len2⟩ >>= fun c0' =>
      Node.access _ (some []) .Write ⟨off2⟩ ⟨len2⟩ >>= fun c1' => pure _) = _
    rw [nwsr_access_eq, nwsr_access_eq]
    have hlf : locRel none [] = .Foreign := rfl
    have hll : locRel (some ([] : Gen.Path)) [] = .Local := rfl
    rw [hlf, hll, hsibWr, hmutWr, Node.accessChildren]; rfl
  let dataW := data.take off2 ++ wBytes2 ++ data.drop (off2 + len2)
  have hdataWLen : dataW.length = data.length := by
    simp only [dataW, List.length_append, List.length_take, List.length_drop, hw2]; omega
  let tbmW : Gen.TreeBorrowsMemory Gen.x86_64 :=
    { tbmM with mem := { tbmM.mem with allocations := [{
        mkRootAllocTB data addr align .Stack with
        data := dataW,
        extra := { root := ⟨[⟨[], sibW, .No⟩, ⟨[], mutW, .Strong⟩],
          List.replicate data.length (.Unprot .Unique), .No⟩ } }] } }
  have hstoreW : TreeBorrowsMemory.store tbmM
      { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩ = .ok tbmW := by
    have heq := tbm_store_eq_node_access tbmM
      { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩ 0 [1] _
      off2 rfl rfl rfl hal2 (by show addr + (off2 : Int) - addr = (off2 : Int); omega)
      (by omega) (by show off2 + wBytes2.length ≤ data.length; omega)
    rw [heq, hw2, haccW]; rfl
  have hsibWGet : ∀ b, b < data.length →
      sibW[b]? = some (if off2 ≤ b ∧ b < off2 + len2 then .Unprot .Disabled else .Unprot .Frozen) := by
    intro b hb
    rcases c1_in_or_out off2 len2 b with ⟨h1, h2⟩ | hout
    · simp only [h1, h2, and_self, ↓reduceIte]
      obtain ⟨p'', htr'', hget'⟩ := hsibWi b h1 h2 _ (nwsr_getElem?_replicate_lt hb)
      cases htr''; exact hget'
    · have hn : ¬ (off2 ≤ b ∧ b < off2 + len2) := fun ⟨_, _⟩ => by omega
      simp only [hn, ↓reduceIte]
      rw [hsibWo b hout, nwsr_getElem?_replicate_lt hb]
  have hmutWGet : ∀ b, b < data.length →
      mutW[b]? = some (if off2 ≤ b ∧ b < off2 + len2 then .Prot .Unique else .Prot (.Reserved true false)) := by
    intro b hb
    rcases c1_in_or_out off2 len2 b with ⟨h1, h2⟩ | hout
    · simp only [h1, h2, and_self, ↓reduceIte]
      obtain ⟨p'', htr'', hget'⟩ := hmutWi b h1 h2 _ (nwsr_getElem?_replicate_lt hb)
      cases htr''; exact hget'
    · have hn : ¬ (off2 ≤ b ∧ b < off2 + len2) := fun ⟨_, _⟩ => by omega
      simp only [hn, ↓reduceIte]
      rw [hmutWo b hout, nwsr_getElem?_replicate_lt hb]
  have hmutWProt : ∀ p ∈ mutW, ∃ pp, p = .Prot pp := by
    intro p hp
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hp
    have hblt : b < data.length := by
      rw [← List.length_replicate (n := data.length) (a := Gen.Permission.Prot (.Reserved true false)),
        ← hmutWl]; exact (List.getElem?_eq_some_iff.mp hb).1
    rw [hmutWGet b hblt] at hb; cases hb
    split <;> exact ⟨_, rfl⟩
  obtain ⟨pairsM, hpairsM, hpMLen, hpMGet⟩ := c1_mapM_unprotect_spec mutW hmutWProt
  have haccMSpec : ∀ b k, (pairsM.map Prod.snd)[b]? = some (some k) →
      b < data.length ∧ k = (if off2 ≤ b ∧ b < off2 + len2 then .Write else .Read) := by
    intro b k hbk
    rw [List.getElem?_map] at hbk
    cases hg : pairsM[b]? with
    | none => rw [hg] at hbk; cases hbk
    | some pr =>
      rcases pr with ⟨pFst, pSnd⟩
      rw [hg] at hbk; cases hbk
      have hblt : b < data.length := by
        rw [← List.length_replicate (n := data.length) (a := Gen.Permission.Prot (.Reserved true false)),
          ← hmutWl, ← hpMLen]; exact (List.getElem?_eq_some_iff.mp hg).1
      have hcb := hmutWGet b hblt
      by_cases h2 : off2 ≤ b ∧ b < off2 + len2
      · simp only [h2, and_self, ↓reduceIte] at hcb ⊢
        have hp := hpMGet b _ _ hcb rfl
        rw [hg] at hp; cases hp; exact ⟨hblt, rfl⟩
      · simp only [h2, ↓reduceIte] at hcb ⊢
        have hp := hpMGet b _ _ hcb rfl
        rw [hg] at hp; cases hp; exact ⟨hblt, rfl⟩
  have hrootEnd : Node.releaseProtectorPermissions .Local 0 (pairsM.map Prod.snd)
      (List.replicate data.length (.Unprot .Unique)) =
      .ok (List.replicate data.length (.Unprot .Unique)) := by
    obtain ⟨rps, hrun, _, hout, hin⟩ := c1_releaseProtectorPerms_pointwise .Local
      (pairsM.map Prod.snd) 0 (List.replicate data.length (.Unprot .Unique)) (fun i k hi => by
        obtain ⟨hblt, _⟩ := haccMSpec i k hi
        exact ⟨.Unprot .Unique, .Unprot .Unique,
          by rw [Nat.zero_add]; exact nwsr_getElem?_replicate_lt hblt, by cases k <;> rfl⟩)
    have heq : rps = List.replicate data.length (.Unprot .Unique) := by
      apply List.ext_getElem?
      intro b
      cases hb : (pairsM.map Prod.snd)[b]? with
      | none => exact hout b (Or.inr (Or.inr (by rw [Nat.sub_zero]; exact hb)))
      | some opt =>
        cases opt with
        | none => exact hout b (Or.inr (Or.inl (by rw [Nat.sub_zero]; exact hb)))
        | some k =>
          obtain ⟨hblt, _⟩ := haccMSpec b k hb
          have hget := nwsr_getElem?_replicate_lt (a := Gen.Permission.Unprot .Unique) hblt
          have hrb := hin b k _ _ hb (by rw [Nat.zero_add]; exact hget) (by cases k <;> rfl)
          rw [Nat.zero_add] at hrb; rw [hrb, hget]
    rw [heq] at hrun; exact hrun
  have hsibEnd : Node.releaseProtectorPermissions .Foreign 0 (pairsM.map Prod.snd) sibW = .ok sibW := by
    obtain ⟨ps', hrun, _, hout, hin⟩ := c1_releaseProtectorPerms_pointwise .Foreign
      (pairsM.map Prod.snd) 0 sibW (fun i k hi => by
        obtain ⟨hblt, hk⟩ := haccMSpec i k hi
        have hg := hsibWGet i hblt
        by_cases h2 : off2 ≤ i ∧ i < off2 + len2
        · simp only [h2, and_self, ↓reduceIte] at hg hk; subst hk
          exact ⟨.Unprot .Disabled, .Unprot .Disabled, by rw [Nat.zero_add]; exact hg, rfl⟩
        · simp only [h2, ↓reduceIte] at hg hk; subst hk
          exact ⟨.Unprot .Frozen, .Unprot .Frozen, by rw [Nat.zero_add]; exact hg, rfl⟩)
    have heq : ps' = sibW := by
      apply List.ext_getElem?
      intro b
      cases hb : (pairsM.map Prod.snd)[b]? with
      | none => exact hout b (Or.inr (Or.inr (by rw [Nat.sub_zero]; exact hb)))
      | some opt =>
        cases opt with
        | none => exact hout b (Or.inr (Or.inl (by rw [Nat.sub_zero]; exact hb)))
        | some k =>
          obtain ⟨hblt, hk⟩ := haccMSpec b k hb
          have hg := hsibWGet b hblt
          by_cases h2 : off2 ≤ b ∧ b < off2 + len2
          · simp only [h2, and_self, ↓reduceIte] at hg hk; subst hk
            have hrb := hin b .Write _ _ hb (by rw [Nat.zero_add]; exact hg) rfl
            rw [Nat.zero_add] at hrb; rw [hrb, hg]
          · simp only [h2, ↓reduceIte] at hg hk; subst hk
            have hrb := hin b .Read _ _ hb (by rw [Nat.zero_add]; exact hg) rfl
            rw [Nat.zero_add] at hrb; rw [hrb, hg]
    rw [heq] at hrun; exact hrun
  let tbmE : Gen.TreeBorrowsMemory Gen.x86_64 :=
    { tbmW with mem := { tbmW.mem with allocations := [{
        mkRootAllocTB data addr align .Stack with
        data := dataW,
        extra := { root := ⟨[⟨[], sibW, .No⟩, ⟨[], pairsM.map Prod.fst, .No⟩],
          List.replicate data.length (.Unprot .Unique), .No⟩ } }] } }
  have hendCall : TreeBorrowsMemory.end_call tbmW { protectors := [(⟨0⟩, [1])] } = .ok tbmE := by
    unfold TreeBorrowsMemory.end_call
    dsimp only [List.foldlM, bind, Except.bind, pure, Except.pure]
    unfold TreeBorrowsMemory.release_protector
    dsimp only [tbmW, tbmM, tbmE]
    have hpyS : Protected.yes Gen.Protected.Strong = true := rfl
    rw [c1_listMutateAt_zero]
    simp only [Node.access_node, Node.is_leaf, List.isEmpty, c1_listMutateAt_one,
      hpyS, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpairsM,
      mkRootAllocTB, bind, Except.bind, pure, Except.pure]
    rw [c1_node_release_twoChildren _ _ _ _ 1 (Or.inr rfl)]
    have hne10 : ¬ ((1 : Int) = 0) := by decide
    simp only [hne10, ↓reduceIte, hrootEnd, bind, Except.bind, pure, Except.pure]
    have hr0 : Node.release_protector ⟨[], sibW, .No⟩ none (pairsM.map Prod.snd) =
        .ok ⟨[], sibW, .No⟩ := by
      unfold Node.release_protector; simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte,
        hsibEnd, Node.releaseProtectorChildren, bind, Except.bind, pure, Except.pure]
    have hr1 : Node.release_protector ⟨[], pairsM.map Prod.fst, .Strong⟩ (some [])
        (pairsM.map Prod.snd) = .ok ⟨[], pairsM.map Prod.fst, .No⟩ := rfl
    rw [hr0, hr1]
  have hwfE : TreeBorrowsMemory.wfLive tbmE := by
    intro a ha _
    have haEq := List.mem_singleton.mp ha
    subst haEq
    show Node.wf dataW.length _
    rw [hdataWLen, Node.wf]
    refine ⟨List.length_replicate, fun p hp => by rw [List.eq_of_mem_replicate hp]; rfl, ?_⟩
    rw [Node.childrenWf, Node.childrenWf, Node.childrenWf, Node.wf, Node.wf, Node.childrenWf]
    refine ⟨⟨by rw [hsibWl, List.length_replicate], ?_, trivial⟩,
      ⟨by rw [List.length_map, hpMLen, hmutWl, List.length_replicate], ?_, trivial⟩, trivial⟩
    · intro p hp
      obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hp
      have hblt : b < data.length := by
        rw [← List.length_replicate (n := data.length) (a := Gen.Permission.Unprot .Frozen),
          ← hsibWl]; exact (List.getElem?_eq_some_iff.mp hb).1
      rw [hsibWGet b hblt] at hb; cases hb; split <;> rfl
    · intro p hp
      obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hp
      rw [List.getElem?_map] at hb
      cases hpb : pairsM[b]? with
      | none => rw [hpb] at hb; cases hb
      | some pr =>
        rw [hpb] at hb; cases hb
        have hblt : b < data.length := by
          rw [← List.length_replicate (n := data.length) (a := Gen.Permission.Prot (.Reserved true false)),
            ← hmutWl, ← hpMLen]; exact (List.getElem?_eq_some_iff.mp hpb).1
        obtain ⟨q1, hq1⟩ : ∃ q1, mutW[b]? = some q1 :=
          ⟨mutW[b]'(by rw [hmutWl, List.length_replicate]; exact hblt),
           List.getElem?_eq_getElem (by rw [hmutWl, List.length_replicate]; exact hblt)⟩
        obtain ⟨pp, rfl⟩ := hmutWProt q1 (List.mem_of_getElem? hq1)
        have he := hpMGet b _ _ hq1 rfl
        rw [hpb] at he; cases he; rfl
  have hload1Ok : ∃ tbmRd, TreeBorrowsMemory.load tbmE
      { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } ⟨len1⟩ ⟨al1⟩ =
      .ok ((data.drop off1).take len1, tbmRd) := by
    have heq := tbm_load_eq_node_access tbmE
      { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } len1 ⟨al1⟩ 0 [0] _
      off1 rfl rfl rfl hal1 (by show addr + (off1 : Int) - addr = (off1 : Int); omega)
      (by omega) (by show off1 + len1 ≤ dataW.length; rw [hdataWLen]; omega)
    have hrootR : Node.transitionRange .Local .Read off1 len1
        (List.replicate data.length (.Unprot .Unique)) =
        .ok (List.replicate data.length (.Unprot .Unique)) :=
      transitionRange_stable_eq .Local .Read len1 off1 _ (fun b _ h2 =>
        ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
    have hsibR : Node.transitionRange .Local .Read off1 len1 sibW = .ok sibW :=
      transitionRange_stable_eq .Local .Read len1 off1 sibW (fun b h1 h2 => by
        have hg := hsibWGet b (by omega)
        have hn2 : ¬ (off2 ≤ b ∧ b < off2 + len2) := fun ⟨_, _⟩ => by omega
        simp only [hn2, ↓reduceIte] at hg
        exact ⟨.Unprot .Frozen, hg, rfl⟩)
    obtain ⟨mutR, hmutR, _⟩ := transitionRange_ok_of_pointwise .Foreign .Read len1 off1
      (pairsM.map Prod.fst) (fun b h1 h2 => by
        have hcb := hmutWGet b (by omega)
        have hn2 : ¬ (off2 ≤ b ∧ b < off2 + len2) := fun ⟨_, _⟩ => by omega
        simp only [hn2, ↓reduceIte] at hcb
        have hp := hpMGet b _ _ hcb rfl
        have hget : (pairsM.map Prod.fst)[b]? = some (.Unprot .Reserved) := by
          rw [List.getElem?_map, hp]; rfl
        exact ⟨.Unprot .Reserved, .Unprot .Reserved, hget, rfl⟩)
    have haccR : Node.access
        ⟨[⟨[], sibW, .No⟩, ⟨[], pairsM.map Prod.fst, .No⟩],
          List.replicate data.length (.Unprot .Unique), .No⟩
        (some [0]) .Read ⟨off1⟩ ⟨len1⟩ =
        .ok ⟨[⟨[], sibW, .No⟩, ⟨[], mutR, .No⟩],
          List.replicate data.length (.Unprot .Unique), .No⟩ := by
      rw [c1_node_access_twoChildren]
      have hloc0 : locRel (some [(0 : Int)]) [] = .Local := rfl
      have hs0 : subPathAt (some [(0 : Int)]) 0 = some [] := rfl
      have hs1 : subPathAt (some [(0 : Int)]) 1 = none := rfl
      rw [hloc0, hs0, hs1, hrootR]
      show (Node.access _ (some []) .Read ⟨off1⟩ ⟨len1⟩ >>= fun c0' =>
        Node.access _ none .Read ⟨off1⟩ ⟨len1⟩ >>= fun c1' => pure _) = _
      rw [nwsr_access_eq, nwsr_access_eq]
      have hll : locRel (some ([] : Gen.Path)) [] = .Local := rfl
      have hlf : locRel none [] = .Foreign := rfl
      rw [hll, hlf, hsibR, hmutR, Node.accessChildren]; rfl
    have hbytesEq : (dataW.drop off1).take len1 = (data.drop off1).take len1 := by
      apply List.ext_getElem?
      intro i
      rcases Nat.lt_or_ge i len1 with hi | hi
      · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi,
          List.getElem?_drop, List.getElem?_drop]
        have hlt2 : off1 + i < (data.take off2).length := by
          rw [List.length_take]; omega
        have hlt2' : off1 + i < (data.take off2 ++ wBytes2).length := by
          rw [List.length_append, List.length_take]; omega
        simp only [dataW]
        rw [List.getElem?_append_left hlt2', List.getElem?_append_left hlt2,
          List.getElem?_take_of_lt (by omega)]
      · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
          List.getElem?_eq_none (by rw [List.length_take]; omega)]
    rw [heq, haccR]
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [hbytesEq]
    exact ⟨_, rfl⟩
  obtain ⟨tbmRd, hload1⟩ := hload1Ok
  have hwfRd : TreeBorrowsMemory.wfLive tbmRd := TreeBorrowsMemory.load_wfLive hwfE hload1
  have hload2Err : TreeBorrowsMemory.load tbmE
      { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [0]) } ⟨len2⟩ ⟨al2⟩ =
      .error (.ub "Tree Borrows: local read of Disabled reference") := by
    have heq := tbm_load_eq_node_access tbmE
      { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [0]) } len2 ⟨al2⟩ 0 [0] _
      off2 rfl rfl rfl hal2 (by show addr + (off2 : Int) - addr = (off2 : Int); omega)
      (by omega) (by show off2 + len2 ≤ dataW.length; rw [hdataWLen]; omega)
    have hrootR : Node.transitionRange .Local .Read off2 len2
        (List.replicate data.length (.Unprot .Unique)) =
        .ok (List.replicate data.length (.Unprot .Unique)) :=
      transitionRange_stable_eq .Local .Read len2 off2 _ (fun b _ h2 =>
        ⟨_, nwsr_getElem?_replicate_lt (by omega), rfl⟩)
    have hsibErr : Node.transitionRange .Local .Read off2 len2 sibW =
        .error (.ub "Tree Borrows: local read of Disabled reference") := by
      cases len2 with
      | zero => exfalso; omega
      | succ m =>
        unfold Node.transitionRange
        have hg := hsibWGet off2 (by omega)
        have hy : off2 ≤ off2 ∧ off2 < off2 + (m + 1) := ⟨by omega, by omega⟩
        simp only [hy, and_self, ↓reduceIte] at hg
        rw [Int.ofNat_eq_natCast, a1_listMutateAt_natCast sibW off2 _ _ _ hg]
        rfl
    rw [heq, c1_node_access_twoChildren]
    have hloc0 : locRel (some [(0 : Int)]) [] = .Local := rfl
    have hs0 : subPathAt (some [(0 : Int)]) 0 = some [] := rfl
    rw [hloc0, hs0, hrootR]
    show ((Node.access _ (some []) .Read ⟨off2⟩ ⟨len2⟩ >>= _) >>= _) = _
    rw [nwsr_access_eq]
    have hll : locRel (some ([] : Gen.Path)) [] = .Local := rfl
    rw [hll, hsibErr]
    rfl
  exact ⟨tbmS, tbmM, { protectors := [(⟨0⟩, [1])] }, tbmW, tbmE, tbmRd,
    hretagS, hretagM, hstoreW, hendCall, hwfE, hload1, hwfRd, hload2Err⟩

/-- **Symbolic `<[T]>::get_mut` and `split_at_mut` disjoint sub-slice soundness
on real `TreeBorrowsMemory` (arbitrary slice length `N` and disjoint windows
`[off1, off1 + len1)` / `[off2, off2 + len2)`)**:
1. **Disjoint mutable sub-slices (`split_at_mut`)**: for ANY combination of
   `#[rustc_no_writable]` / standard `&mut` (`fnIw1, fnIw2 : Bool`), reborrowing
   two disjoint mutable sub-slices into the SAME `FnEntry` frame succeeds with
   tags `[0]` and `[1]` (`TreeBorrowsMemory.wfLive` preserved); storing arbitrary
   aligned `bytes1` and `bytes2` into the two sub-slices succeeds in **EITHER**
   order (yielding the identical final borrow tree!); and `TreeBorrowsMemory.end_call`
   succeeds in **BOTH** protector-release orders (`[0, 1]` and `[1, 0]`),
   preserving `TreeBorrowsMemory.wfLive`!
2. **Per-byte `<[T]>::get_mut` refinement (no coarse-range over-approximation)**:
   given a shared sibling `&[T]` (`[0]`) over the full slice `[0, N)` and a
   `#[rustc_no_writable]` `FnEntry` `&mut [T]` (`[1]`) over `[0, N)`:
   - writing ONLY sub-range `[off2, off2 + len2)` through `[1]` and exiting via
     `end_call` preserves `TreeBorrowsMemory.wfLive`;
   - reading the unwritten sub-range `[off1, off1 + len1)` through sibling `[0]`
     **SUCCEEDS** (returning the original slice bytes `(data.drop off1).take len1`);
   - reading the written sub-range `[off2, off2 + len2)` through sibling `[0]`
     **FAILS** with exact `.error (.ub "Tree Borrows: local read of Disabled reference")`. -/
theorem tbm_slice_disjoint_getMut_sound
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int) (align : Nat)
    (off1 len1 off2 len2 : Nat)
    (hlen1 : 0 < len1) (hlen2 : 0 < len2)
    (hdisj : off1 + len1 ≤ off2) (hbound : off2 + len2 ≤ data.length)
    (wBytes1 wBytes2 : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (hw1 : wBytes1.length = len1) (hw2 : wBytes2.length = len2)
    (al1 al2 : Nat)
    (hal1 : Align.is_aligned ⟨al1⟩ (addr + (off1 : Int)) = true)
    (hal2 : Align.is_aligned ⟨al2⟩ (addr + (off2 : Int)) = true)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable) :
    let tbm0 : Gen.TreeBorrowsMemory Gen.x86_64 :=
      { params := ⟨true⟩
        mem := { allocations := [mkRootAllocTB data addr align .Stack], _phantom := ⟨⟩ } }
    let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
      { thin_pointer := { addr := addr, provenance := some (⟨0⟩, []) }, metadata := none }
    let p1In : Gen.Pointer Gen.TreeBorrowsProvenance :=
      { thin_pointer := { addr := addr + (off1 : Int), provenance := some (⟨0⟩, []) },
        metadata := none }
    let p2In : Gen.Pointer Gen.TreeBorrowsProvenance :=
      { thin_pointer := { addr := addr + (off2 : Int), provenance := some (⟨0⟩, []) },
        metadata := none }
    (∀ fnIw1 fnIw2 : Bool,
      ∃ tbm1 tbm2 fe1 fe2 tbm12 tbm21 tbmEndFwd tbmEndRev,
        TreeBorrowsMemory.retag_ptr tbm0 TreeBorrowsMemory.new_call p1In
            (.Ref .Mutable (slicePointeeInfoMR len1 al1)) true fnIw1 lookup =
          .ok ({ thin_pointer := { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) },
                 metadata := none }, tbm1, fe1) ∧
        TreeBorrowsMemory.retag_ptr tbm1 fe1 p2In
            (.Ref .Mutable (slicePointeeInfoMR len2 al2)) true fnIw2 lookup =
          .ok ({ thin_pointer := { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) },
                 metadata := none }, tbm2, fe2) ∧
        fe2 = { protectors := [(⟨0⟩, [0]), (⟨0⟩, [1])] } ∧
        TreeBorrowsMemory.wfLive tbm2 ∧
        (TreeBorrowsMemory.store tbm2
            { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } wBytes1 ⟨al1⟩ >>=
          fun t => TreeBorrowsMemory.store t
            { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩) =
          .ok tbm12 ∧
        (TreeBorrowsMemory.store tbm2
            { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩ >>=
          fun t => TreeBorrowsMemory.store t
            { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } wBytes1 ⟨al1⟩) =
          .ok tbm21 ∧
        tbmRootOf tbm12 0 = tbmRootOf tbm21 0 ∧
        TreeBorrowsMemory.end_call tbm12 fe2 = .ok tbmEndFwd ∧
        TreeBorrowsMemory.wfLive tbmEndFwd ∧
        TreeBorrowsMemory.end_call tbm12 { protectors := fe2.protectors.reverse } = .ok tbmEndRev ∧
        TreeBorrowsMemory.wfLive tbmEndRev) ∧
    (∃ tbmS tbmM feM tbmW tbmE tbmRd,
      TreeBorrowsMemory.retag_ptr tbm0 TreeBorrowsMemory.new_call rootPtr
          (.Ref .Immutable (slicePointeeInfoMR data.length align)) false true lookup =
        .ok ({ thin_pointer := { addr := addr, provenance := some (⟨0⟩, [0]) },
               metadata := none }, tbmS, TreeBorrowsMemory.new_call) ∧
      TreeBorrowsMemory.retag_ptr tbmS TreeBorrowsMemory.new_call rootPtr
          (.Ref .Mutable (slicePointeeInfoMR data.length align)) true false lookup =
        .ok ({ thin_pointer := { addr := addr, provenance := some (⟨0⟩, [1]) },
               metadata := none }, tbmM, feM) ∧
      TreeBorrowsMemory.store tbmM
          { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [1]) } wBytes2 ⟨al2⟩ = .ok tbmW ∧
      TreeBorrowsMemory.end_call tbmW feM = .ok tbmE ∧
      TreeBorrowsMemory.wfLive tbmE ∧
      TreeBorrowsMemory.load tbmE
          { addr := addr + (off1 : Int), provenance := some (⟨0⟩, [0]) } ⟨len1⟩ ⟨al1⟩ =
        .ok ((data.drop off1).take len1, tbmRd) ∧
      TreeBorrowsMemory.wfLive tbmRd ∧
      TreeBorrowsMemory.load tbmE
          { addr := addr + (off2 : Int), provenance := some (⟨0⟩, [0]) } ⟨len2⟩ ⟨al2⟩ =
        .error (.ub "Tree Borrows: local read of Disabled reference")) :=
  ⟨fun fnIw1 fnIw2 => c1_slice_disjoint_splitAtMut_sound data addr align off1 len1 off2 len2
      hlen1 hlen2 hdisj hbound wBytes1 wBytes2 hw1 hw2 al1 al2 hal1 hal2 lookup fnIw1 fnIw2,
   c1_slice_getMut_perByte_refinement data addr align off1 len1 off2 len2
      hlen1 hlen2 hdisj hbound wBytes2 hw2 al1 al2 hal1 hal2 lookup⟩

/-- **Foreign-passive byte permissions**: permissions on a byte OUTSIDE a node's
inside range (`ReborrowSettings.outside`) that survive EVERY foreign read AND
every foreign write without UB, and are closed under foreign transitions. -/
def permIsForeignPassive : Gen.Permission → Bool
  | .Unprot _ => true
  | .Prot (.Reserved false _) => true
  | .Prot (.Frozen false) => true
  | .Prot .Cell => true
  | .Prot .Disabled => true
  | _ => false

/-- `permIsForeignPassive` is closed under ALL foreign reads and foreign
writes (never raises UB). -/
theorem permission_isForeignPassive_preserved (p : Gen.Permission) (k : Gen.AccessKind)
    (hp : permIsForeignPassive p = true) :
    ∃ p', Permission.transition p k .Foreign = .ok p' ∧ permIsForeignPassive p' = true := by
  cases p with
  | Unprot u =>
    cases u <;> cases k <;> exact ⟨_, rfl, rfl⟩
  | Prot pp =>
    cases pp with
    | Unique => cases hp
    | Reserved hlr hfr =>
      cases hlr with
      | true => cases hp
      | false => cases hfr <;> cases k <;> exact ⟨_, rfl, rfl⟩
    | Frozen hlr =>
      cases hlr with
      | true => cases hp
      | false => cases k <;> exact ⟨_, rfl, rfl⟩
    | Cell => cases k <;> exact ⟨_, rfl, rfl⟩
    | Disabled => cases k <;> exact ⟨_, rfl, rfl⟩

/-- **Multi-range whole-tree relational invariant (`TreeSimInvMulti`)**: strictly
generalizes `TreeSimInv` by removing the universal `overlap` restriction (which
makes `TreeSimInv` unsatisfiable on multi-slice borrow trees with disjoint
sub-slices such as `disjointTwoParamWorld` / `<[T]>::split_at_mut`).
- Every Anneal node whose range overlaps `[off, off + len)` satisfies the exact
  window relation `NodeWindowRel`.
- Every Anneal node whose range is **disjoint** from `[off, off + len)` carries
  foreign-passive permissions (`permIsForeignPassive = true`, matching
  MiniRust's `ReborrowSettings.outside`) on `[off, off + len)`. -/
structure TreeSimInvMulti (off len : Nat) (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld)
    (t : Gen.Node) : Prop where
  nodes : ∀ n ∈ w.nodes, ∃ m, nodeAt t (emb n.tag) = some m ∧
    if rangesOverlap off len n.rangeOffset n.rangeLen = true then
      NodeWindowRel w.activeProtectors off len n m
    else
      Protected.yes m.«protected» = n.isProtected w.activeProtectors ∧
      ∀ b, off ≤ b → b < off + len → ∃ p, m.permissions[b]? = some p ∧ permIsForeignPassive p = true
  surj : ∀ q m, nodeAt t q = some m → ∃ n ∈ w.nodes, emb n.tag = q
  noProtIM : ∀ n ∈ w.nodes, n.isProtected w.activeProtectors = true → n.perm ≠ .reservedIM
  protUniqAcc : ∀ n ∈ w.nodes, n.isProtected w.activeProtectors = true →
    n.perm = .unique → n.accessed = true

/-- `TreeSimInvMulti` strictly generalizes `TreeSimInv`. -/
theorem treeSimInvMulti_of_treeSimInv (off len : Nat) (emb : Nat → Gen.Path)
    (w : FnEntryBorrowWorld) (t : Gen.Node) (h : TreeSimInv off len emb w t) :
    TreeSimInvMulti off len emb w t where
  nodes := fun n hn => by
    obtain ⟨m, hm, hrel⟩ := h.nodes n hn
    exact ⟨m, hm, by rw [h.overlap n hn]; exact hrel⟩
  surj := h.surj
  noProtIM := h.noProtIM
  protUniqAcc := h.protUniqAcc

/-- Computable checker for `TreeSimInvMulti`. -/
def treeSimInvMultiBool (off len : Nat) (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld)
    (t : Gen.Node) : Bool :=
  w.nodes.all (fun n =>
    (match nodeAt t (emb n.tag) with
      | some m =>
        if rangesOverlap off len n.rangeOffset n.rangeLen then
          nodeWindowRelBool w.activeProtectors off len n m
        else
          decide (Protected.yes m.«protected» = n.isProtected w.activeProtectors) &&
          (List.range len).all (fun i =>
            match m.permissions[off + i]? with
            | some p => permIsForeignPassive p
            | none => false)
      | none => false) &&
    (!n.isProtected w.activeProtectors ||
      (decide (n.perm ≠ .reservedIM) && (decide (n.perm ≠ .unique) || n.accessed)))) &&
  (nodePaths t).all (fun q => w.nodes.any (fun n => decide (emb n.tag = q)))

/-- Constructive soundness of `treeSimInvMultiBool` (zero `Classical.choice`). -/
theorem treeSimInvMulti_of_bool (off len : Nat) (emb : Nat → Gen.Path)
    (w : FnEntryBorrowWorld) (t : Gen.Node)
    (h : treeSimInvMultiBool off len emb w t = true) :
    TreeSimInvMulti off len emb w t := by
  unfold treeSimInvMultiBool at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨hn, hs⟩ := h
  have hn' : ∀ n ∈ w.nodes,
      (match nodeAt t (emb n.tag) with
        | some m =>
          if rangesOverlap off len n.rangeOffset n.rangeLen then
            nodeWindowRelBool w.activeProtectors off len n m
          else
            decide (Protected.yes m.«protected» = n.isProtected w.activeProtectors) &&
            (List.range len).all (fun i =>
              match m.permissions[off + i]? with
              | some p => permIsForeignPassive p
              | none => false)
        | none => false) = true ∧
      (!n.isProtected w.activeProtectors ||
        (decide (n.perm ≠ .reservedIM) && (decide (n.perm ≠ .unique) || n.accessed))) = true := by
    intro n hm
    have h0 := hn n hm
    rw [Bool.and_eq_true] at h0
    exact h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hm
    have h1 := (hn' n hm).1
    cases hq : nodeAt t (emb n.tag) with
    | none => rw [hq] at h1; cases h1
    | some m =>
      rw [hq] at h1
      refine ⟨m, rfl, ?_⟩
      cases hov : rangesOverlap off len n.rangeOffset n.rangeLen with
      | true =>
        simp only [hov, ↓reduceIte] at h1 ⊢
        exact nodeWindowRel_of_bool w.activeProtectors off len n m h1
      | false =>
        simp only [hov, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
        rw [Bool.and_eq_true, List.all_eq_true] at h1
        refine ⟨of_decide_eq_true h1.1, fun b hb1 hb2 => ?_⟩
        have hall := h1.2 (b - off) (List.mem_range.mpr (by omega))
        have e : off + (b - off) = b := by omega
        rw [e] at hall
        cases hpb : m.permissions[b]? with
        | none => rw [hpb] at hall; cases hall
        | some p => rw [hpb] at hall; exact ⟨p, rfl, hall⟩
  · intro q m hq
    have hmem := hs q (nodeAt_mem_nodePaths t q m hq)
    obtain ⟨n, hnmem, hdec⟩ := List.any_eq_true.mp hmem
    exact ⟨n, hnmem, of_decide_eq_true hdec⟩
  · intro n hm hprot
    have h2 := (hn' n hm).2
    rw [hprot] at h2
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h2
    exact of_decide_eq_true h2.1
  · intro n hm hprot huniq
    have h2 := (hn' n hm).2
    rw [hprot] at h2
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at h2
    rcases h2.2 with hne | hacc
    · exact absurd huniq (of_decide_eq_true hne)
    · exact hacc

private def c1_NodeStepSimMulti (ap : List Nat) (off len : Nat) (k : Gen.AccessKind)
    (step : Bool → TreeTagNode → Except RetagStepErr TreeTagNode) (n : TreeTagNode) : Prop :=
  (rangesOverlap off len n.rangeOffset n.rangeLen = true →
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
        ∃ msg, Permission.transition p k (nodeRelToMiniRust isLocal) = .error (.ub msg))) ∧
  (rangesOverlap off len n.rangeOffset n.rangeLen = false →
    ∀ isLocal, step isLocal n = .ok n)

private theorem c1_tree_sim_multi_core
    (k : Gen.AccessKind) (isWrite : Bool)
    (step : Bool → TreeTagNode → Except RetagStepErr TreeTagNode)
    (off len : Nat) (hlen : 0 < len) (emb : Nat → Gen.Path)
    (w : FnEntryBorrowWorld) (t : Gen.Node) (tag : Nat)
    (hinv : TreeSimInvMulti off len emb w t)
    (hstep : ∀ n ∈ w.nodes, c1_NodeStepSimMulti w.activeProtectors off len k step n)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = locOf (some (emb tag)) (emb n.tag))
    (hancOv : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = true →
      rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) isWrite off len n = true →
      step false n = .ok n) :
    (∀ nodes', ListRel (PrunedStepRel w tag isWrite off len step) w.nodes nodes' →
      ∃ t', Node.access t (some (emb tag)) k ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInvMulti off len emb { w with nodes := nodes' } t') ∧
    ((∀ nodes', ¬ ListRel (PrunedStepRel w tag isWrite off len step) w.nodes nodes') →
      ∃ msg, Node.access t (some (emb tag)) k ⟨off⟩ ⟨len⟩ = .error (.ub msg)) := by
  have hpr : ∀ n ∈ w.nodes, ∀ n', PrunedStepRel w tag isWrite off len step n n' →
      step (locOf (some (emb tag)) (emb n.tag)) n = .ok n' := by
    intro n hn n' hrel
    rcases hrel with ⟨hc, hs⟩ | ⟨hc, hp, hEq⟩ | ⟨hc, _, hs⟩
    · rw [← hloc n hn, hc]; exact hs
    · rw [← hloc n hn, hc, hEq]; exact hnoprune n hn hp
    · rw [← hloc n hn, hc]; exact hs
  have hrp : ∀ n ∈ w.nodes, ∀ n', step (locOf (some (emb tag)) (emb n.tag)) n = .ok n' →
      PrunedStepRel w tag isWrite off len step n n' := by
    intro n hn n' hs
    cases hl : locOf (some (emb tag)) (emb n.tag) with
    | true => rw [hl] at hs; exact Or.inl ⟨by rw [hloc n hn, hl], hs⟩
    | false =>
      rw [hl] at hs
      cases hp : isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) isWrite off len n with
      | false => exact Or.inr (Or.inr ⟨by rw [hloc n hn, hl], hp, hs⟩)
      | true =>
        rw [hnoprune n hn hp] at hs
        cases hs
        exact Or.inr (Or.inl ⟨by rw [hloc n hn, hl], hp, rfl⟩)
  have hdisjForeign : ∀ n ∈ w.nodes, rangesOverlap off len n.rangeOffset n.rangeLen = false →
      locRel (some (emb tag)) (emb n.tag) = .Foreign := by
    intro n hn hdisj
    unfold locRel
    cases hl : locOf (some (emb tag)) (emb n.tag) with
    | false => rfl
    | true =>
      have hanc : (ancestorPathTags w.nodes tag).contains n.tag = true := by rw [hloc n hn, hl]
      have hov := hancOv n hn hanc
      rw [hov] at hdisj; cases hdisj
  have hmr : ∀ q m, nodeAt t q = some m → ∃ n ∈ w.nodes, emb n.tag = q ∧
      (if rangesOverlap off len n.rangeOffset n.rangeLen = true then
        NodeWindowRel w.activeProtectors off len n m
       else
        Protected.yes m.«protected» = n.isProtected w.activeProtectors ∧
        ∀ b, off ≤ b → b < off + len → ∃ p, m.permissions[b]? = some p ∧ permIsForeignPassive p = true) := by
    intro q m hq
    obtain ⟨n, hn, hemb⟩ := hinv.surj q m hq
    obtain ⟨m', hm', hrel⟩ := hinv.nodes n hn
    rw [hemb, hq] at hm'; cases hm'
    exact ⟨n, hn, hemb, hrel⟩
  have hrelNode : ∀ (isLocal : Bool), nodeRelToMiniRust isLocal =
      (if isLocal then Gen.NodeRelation.Local else .Foreign) := fun _ => rfl
  constructor
  · intro nodes' hrel
    have hpoint : ∀ q m, nodeAt t q = some m →
        ∃ ps', Node.transitionRange (locRel (some (emb tag)) q) k off len m.permissions =
          .ok ps' := by
      intro q m hq
      obtain ⟨n, hn, hemb, hnod⟩ := hmr q m hq
      cases hov : rangesOverlap off len n.rangeOffset n.rangeLen with
      | true =>
        simp only [hov, ↓reduceIte] at hnod
        obtain ⟨_, p, hp, hwin⟩ := hnod
        obtain ⟨n', _, hnn'⟩ := hrel.exists_of_mem_left hn
        have hs := hpr n hn n' hnn'
        obtain ⟨p0, hp0, hok, _⟩ := (hstep n hn).1 hov (locOf (some (emb tag)) (emb n.tag))
        rw [hp] at hp0; cases hp0
        obtain ⟨_, _, _, _, _, _, p', htr, _⟩ := hok n' hs
        rw [hemb] at htr
        obtain ⟨ps', hrun, _⟩ := transitionRange_ok_of_pointwise
          (locRel (some (emb tag)) q) k len off m.permissions
          (fun b h1 h2 => ⟨p, p', hwin b h1 h2, htr⟩)
        exact ⟨ps', hrun⟩
      | false =>
        simp only [hov, Bool.false_eq_true, ↓reduceIte] at hnod
        have hfor := hdisjForeign n hn hov
        rw [hemb] at hfor
        rw [hfor]
        obtain ⟨ps', hrun, _⟩ := transitionRange_ok_of_pointwise .Foreign k len off m.permissions
          (fun b h1 h2 => by
            obtain ⟨p, hpb, hpas⟩ := hnod.2 b h1 h2
            obtain ⟨p', htr, _⟩ := permission_isForeignPassive_preserved p k hpas
            exact ⟨p, p', hpb, htr⟩)
        exact ⟨ps', hrun⟩
    obtain ⟨t', hacc, hpost⟩ :=
      node_access_ok_of_pointwise k off len t (some (emb tag)) hpoint
    refine ⟨t', hacc, ?_⟩
    have hnode : ∀ n' ∈ nodes', ∃ n ∈ w.nodes, n'.tag = n.tag ∧
        n'.rangeOffset = n.rangeOffset ∧ n'.rangeLen = n.rangeLen ∧
        (n'.isProtected w.activeProtectors = true → n'.perm ≠ .reservedIM) ∧
        (n'.isProtected w.activeProtectors = true → n'.perm = .unique → n'.accessed = true) ∧
        ∃ m', nodeAt t' (emb n'.tag) = some m' ∧
          if rangesOverlap off len n'.rangeOffset n'.rangeLen = true then
            NodeWindowRel w.activeProtectors off len n' m'
          else
            Protected.yes m'.«protected» = n'.isProtected w.activeProtectors ∧
            ∀ b, off ≤ b → b < off + len → ∃ p, m'.permissions[b]? = some p ∧ permIsForeignPassive p = true := by
      intro n' hn'
      obtain ⟨n, hn, hnn'⟩ := hrel.exists_of_mem_right hn'
      have hs := hpr n hn n' hnn'
      obtain ⟨m, hm, hnod⟩ := hinv.nodes n hn
      obtain ⟨m', hm', hprot', hrun⟩ := (hpost (emb n.tag)).1 m hm
      cases hov : rangesOverlap off len n.rangeOffset n.rangeLen with
      | true =>
        simp only [hov, ↓reduceIte] at hnod
        obtain ⟨hprotm, p, hp, hwin⟩ := hnod
        obtain ⟨p0, hp0, hok, _⟩ := (hstep n hn).1 hov (locOf (some (emb tag)) (emb n.tag))
        rw [hp] at hp0; cases hp0
        obtain ⟨htag, hpe, hro, hrl, hIM, hUA, p', htr, hp'⟩ := hok n' hs
        refine ⟨n, hn, htag, hro, hrl, hIM, hUA, m', by rw [htag]; exact hm', ?_⟩
        rw [hro, hrl]
        simp only [hov, ↓reduceIte]
        refine ⟨by rw [hprot', hprotm, hpe], p', by rw [hpe]; exact hp', fun b h1 h2 => ?_⟩
        obtain ⟨ps', hrun', _, _, hin⟩ := transitionRange_ok_of_pointwise
          (locRel (some (emb tag)) (emb n.tag)) k len off m.permissions
          (fun b h1 h2 => ⟨p, p', hwin b h1 h2, htr⟩)
        rw [hrun] at hrun'; cases hrun'
        obtain ⟨p'', htr'', hget⟩ := hin b h1 h2 p (hwin b h1 h2)
        have htr2 : Permission.transition p k (locRel (some (emb tag)) (emb n.tag)) = .ok p' := htr
        rw [htr2] at htr''; cases htr''
        exact hget
      | false =>
        simp only [hov, Bool.false_eq_true, ↓reduceIte] at hnod
        have hstay := (hstep n hn).2 hov (locOf (some (emb tag)) (emb n.tag))
        rw [hstay] at hs
        have hneq : n' = n := by cases hs; rfl
        subst hneq
        have hfor := hdisjForeign n' hn hov
        rw [hfor] at hrun
        obtain ⟨_, _, hin⟩ := c1_transitionRange_ok_full .Foreign k off len m.permissions
          m'.permissions hrun
        refine ⟨n', hn, rfl, rfl, rfl, hinv.noProtIM n' hn, hinv.protUniqAcc n' hn, m', hm', ?_⟩
        simp only [hov, Bool.false_eq_true, ↓reduceIte]
        refine ⟨by rw [hprot', hnod.1], fun b h1 h2 => ?_⟩
        obtain ⟨p, hpb, hpas⟩ := hnod.2 b h1 h2
        obtain ⟨p0, p', hp0, htr, hp'⟩ := hin b h1 h2
        rw [hpb] at hp0; cases hp0
        obtain ⟨p'', htr'', hpas'⟩ := permission_isForeignPassive_preserved p k hpas
        rw [htr] at htr''; cases htr''
        exact ⟨p', hp', hpas'⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n' hn'
      obtain ⟨_, _, _, _, _, _, _, m', hm', hrel'⟩ := hnode n' hn'
      exact ⟨m', hm', hrel'⟩
    · intro q m' hq'
      cases hq : nodeAt t q with
      | none => rw [(hpost q).2 hq] at hq'; cases hq'
      | some m =>
        obtain ⟨n, hn, hemb⟩ := hinv.surj q m hq
        obtain ⟨n', hn', hnn'⟩ := hrel.exists_of_mem_left hn
        have hs := hpr n hn n' hnn'
        cases hov : rangesOverlap off len n.rangeOffset n.rangeLen with
        | true =>
          obtain ⟨_, _, hok, _⟩ := (hstep n hn).1 hov (locOf (some (emb tag)) (emb n.tag))
          obtain ⟨htag, _⟩ := hok n' hs
          exact ⟨n', hn', by rw [htag]; exact hemb⟩
        | false =>
          have hstay := (hstep n hn).2 hov (locOf (some (emb tag)) (emb n.tag))
          rw [hstay] at hs
          have hneq : n' = n := by cases hs; rfl
          subst hneq
          exact ⟨n', hn', hemb⟩
    · intro n' hn'; obtain ⟨_, _, _, _, _, hIM, _⟩ := hnode n' hn'; exact hIM
    · intro n' hn'; obtain ⟨_, _, _, _, _, _, hUA, _⟩ := hnode n' hn'; exact hUA
  · intro hno
    cases hacc : Node.access t (some (emb tag)) k ⟨off⟩ ⟨len⟩ with
    | ok t' =>
      exfalso
      have hall : ∀ n ∈ w.nodes, ∃ n', PrunedStepRel w tag isWrite off len step n n' := by
        intro n hn
        cases hov : rangesOverlap off len n.rangeOffset n.rangeLen with
        | false =>
          exact ⟨n, hrp n hn n ((hstep n hn).2 hov (locOf (some (emb tag)) (emb n.tag)))⟩
        | true =>
          obtain ⟨m, hm, hnod⟩ := hinv.nodes n hn
          simp only [hov, ↓reduceIte] at hnod
          obtain ⟨_, p, hp, hwin⟩ := hnod
          obtain ⟨ps', hrun⟩ := node_access_ok_inv k off len t t' (some (emb tag)) hacc
            (emb n.tag) m hm
          obtain ⟨q0, q0', hq0, htr0⟩ := transitionRange_ok_inv
            (locRel (some (emb tag)) (emb n.tag)) k len off m.permissions ps' hrun off
            (Nat.le_refl _) (by omega)
          rw [hwin off (Nat.le_refl _) (by omega)] at hq0; cases hq0
          obtain ⟨p0, hp0, _, herr⟩ := (hstep n hn).1 hov (locOf (some (emb tag)) (emb n.tag))
          rw [hp] at hp0; cases hp0
          cases hs : step (locOf (some (emb tag)) (emb n.tag)) n with
          | ok n' => exact ⟨n', hrp n hn n' hs⟩
          | error e =>
            obtain ⟨msg, hmsg⟩ := herr e hs
            rw [hrelNode] at hmsg
            have htr0' : Permission.transition p k
                (if locOf (some (emb tag)) (emb n.tag) then Gen.NodeRelation.Local else .Foreign) =
                .ok q0' := htr0
            rw [htr0'] at hmsg; cases hmsg
      obtain ⟨nodes', hrel⟩ := nwsr_listRel_of_forall w.nodes hall
      exact hno nodes' hrel
    | error e =>
      obtain ⟨q, m, hq, herr⟩ := node_access_error_inv k off len t (some (emb tag)) e hacc
      obtain ⟨n, _, _, hnod⟩ := hmr q m hq
      have hlenM : off + len ≤ m.permissions.length := by
        cases hov : rangesOverlap off len n.rangeOffset n.rangeLen with
        | true =>
          simp only [hov, ↓reduceIte] at hnod
          obtain ⟨_, p, _, hwin⟩ := hnod
          have hlast := hwin (off + len - 1) (by omega) (by omega)
          have hlt := (List.getElem?_eq_some_iff.mp hlast).1
          omega
        | false =>
          simp only [hov, Bool.false_eq_true, ↓reduceIte] at hnod
          obtain ⟨p, hlast, _⟩ := hnod.2 (off + len - 1) (by omega) (by omega)
          have hlt := (List.getElem?_eq_some_iff.mp hlast).1
          omega
      obtain ⟨msg, hmsg⟩ := transitionRange_error_is_ub (locRel (some (emb tag)) q) k len off
        m.permissions e hlenM herr
      exact ⟨msg, by rw [hmsg]⟩

/-- **Multi-range whole-tree READ simulation (`TreeSimInvMulti`)**: generalizes
`tree_read_simulates_node_access` to multi-slice borrow trees containing disjoint
sub-slices (e.g., `disjointTwoParamWorld`, `<[T]>::split_at_mut`), requiring only
that the accessed tag's ancestors overlap `[off, off + len)` (`hancOv`). -/
theorem tree_read_simulates_node_access_multi
    (off len : Nat) (hlen : 0 < len) (emb : Nat → Gen.Path)
    (w : FnEntryBorrowWorld) (t : Gen.Node) (tag : Nat)
    (hinv : TreeSimInvMulti off len emb w t)
    (htag : ∃ n, findNode? w.nodes tag = some n)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = locOf (some (emb tag)) (emb n.tag))
    (hancOv : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = true →
      rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) false off len n = true →
      foreignStepInert w.activeProtectors false off len n = true) :
    (∀ w', execWorldRangeRead w tag off len = .ok w' →
      ∃ t', Node.access t (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInvMulti off len emb w' t') ∧
    (∀ e, execWorldRangeRead w tag off len = .error e →
      ∃ msg, Node.access t (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ = .error (.ub msg)) ∧
    (∀ t', Node.access t (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ = .ok t' →
      ∃ w', execWorldRangeRead w tag off len = .ok w' ∧ TreeSimInvMulti off len emb w' t') := by
  have hne : len ≠ 0 := by omega
  have hstep : ∀ n ∈ w.nodes, c1_NodeStepSimMulti w.activeProtectors off len .Read
      (fun isLoc m => stepNodeOnRangeRead w.activeProtectors isLoc off len m) n := by
    intro n hn
    refine ⟨fun hov isLocal => ?_, fun hdisj isLocal => ?_⟩
    · obtain ⟨p, hp, hok, herr⟩ := stepNodeOnRangeRead_simulates_permission_transition
        w.activeProtectors isLocal off len n hov (hinv.noProtIM n hn) (hinv.protUniqAcc n hn)
      refine ⟨p, hp, fun n' hn' => ?_, herr⟩
      obtain ⟨htag', hprot', hro, hrl, hIM', hUA'⟩ := nwsr_stepRead_meta _ isLocal off len n n' hn'
      have hpe : n'.isProtected w.activeProtectors = n.isProtected w.activeProtectors := by
        unfold TreeTagNode.isProtected; rw [hprot']
      exact ⟨htag', hpe, hro, hrl, fun hp' him => hinv.noProtIM n hn (hpe ▸ hp') (hIM' him),
        hUA' (hinv.protUniqAcc n hn), hok n' hn'⟩
    · unfold stepNodeOnRangeRead
      simp only [hdisj, Bool.not_false, ↓reduceIte]
  obtain ⟨hfwd, hbwd⟩ := c1_tree_sim_multi_core .Read false
    (fun isLoc m => stepNodeOnRangeRead w.activeProtectors isLoc off len m)
    off len hlen emb w t tag hinv hstep hloc hancOv
    (fun n hn hp => nwsr_foreignStepInert_read (hnoprune n hn hp))
  have h1 : ∀ w', execWorldRangeRead w tag off len = .ok w' →
      ∃ t', Node.access t (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInvMulti off len emb w' t' := by
    intro w' hok
    obtain ⟨_, nodes', hw', hrel⟩ := (execWorldRangeRead_ok_iff w w' tag off len hne).mp hok
    rw [hw']; exact hfwd nodes' hrel
  have h2 : ∀ e, execWorldRangeRead w tag off len = .error e →
      ∃ msg, Node.access t (some (emb tag)) .Read ⟨off⟩ ⟨len⟩ = .error (.ub msg) := by
    intro e herr
    apply hbwd
    intro nodes' hrel
    have hok := (execWorldRangeRead_ok_iff w { w with nodes := nodes' } tag off len hne).mpr
      ⟨htag, nodes', rfl, hrel⟩
    rw [herr] at hok; cases hok
  refine ⟨h1, h2, ?_⟩
  intro t' hacc
  cases hr : execWorldRangeRead w tag off len with
  | ok w' =>
    obtain ⟨t'', hacc'', hinv'⟩ := h1 w' hr
    rw [hacc] at hacc''; cases hacc''
    exact ⟨w', rfl, hinv'⟩
  | error e =>
    obtain ⟨msg, hmsg⟩ := h2 e hr
    rw [hacc] at hmsg; cases hmsg

/-- **Multi-range whole-tree WRITE simulation (`TreeSimInvMulti`)**: generalizes
`tree_write_simulates_node_access` to multi-slice borrow trees containing disjoint
sub-slices. -/
theorem tree_write_simulates_node_access_multi
    (off len : Nat) (hlen : 0 < len) (emb : Nat → Gen.Path)
    (w : FnEntryBorrowWorld) (t : Gen.Node) (tag : Nat)
    (hinv : TreeSimInvMulti off len emb w t)
    (hro : w.allocReadOnly = false)
    (htag : ∃ n, findNode? w.nodes tag = some n)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = locOf (some (emb tag)) (emb n.tag))
    (hancOv : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = true →
      rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) true off len n = true →
      foreignStepInert w.activeProtectors true off len n = true) :
    (∀ w', execWorldRangeWrite w tag off len = .ok w' →
      ∃ t', Node.access t (some (emb tag)) .Write ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInvMulti off len emb w' t') ∧
    (∀ e, execWorldRangeWrite w tag off len = .error e →
      ∃ msg, Node.access t (some (emb tag)) .Write ⟨off⟩ ⟨len⟩ = .error (.ub msg)) ∧
    (∀ t', Node.access t (some (emb tag)) .Write ⟨off⟩ ⟨len⟩ = .ok t' →
      ∃ w', execWorldRangeWrite w tag off len = .ok w' ∧ TreeSimInvMulti off len emb w' t') := by
  have hne : len ≠ 0 := by omega
  have hstep : ∀ n ∈ w.nodes, c1_NodeStepSimMulti w.activeProtectors off len .Write
      (fun isLoc m => stepNodeOnRangeWrite w.activeProtectors isLoc off len m) n := by
    intro n hn
    refine ⟨fun hov isLocal => ?_, fun hdisj isLocal => ?_⟩
    · obtain ⟨p, hp, hok, herr⟩ := stepNodeOnRangeWrite_simulates_permission_transition
        w.activeProtectors isLocal off len n hov (hinv.noProtIM n hn) (hinv.protUniqAcc n hn)
      refine ⟨p, hp, fun n' hn' => ?_, herr⟩
      obtain ⟨htag', hprot', hro', hrl, hIM', hUA'⟩ := nwsr_stepWrite_meta _ isLocal off len n n' hn'
      have hpe : n'.isProtected w.activeProtectors = n.isProtected w.activeProtectors := by
        unfold TreeTagNode.isProtected; rw [hprot']
      exact ⟨htag', hpe, hro', hrl, fun hp' him => hinv.noProtIM n hn (hpe ▸ hp') (hIM' him),
        hUA' (hinv.protUniqAcc n hn), hok n' hn'⟩
    · unfold stepNodeOnRangeWrite
      simp only [hdisj, Bool.not_false, ↓reduceIte]
  obtain ⟨hfwd, hbwd⟩ := c1_tree_sim_multi_core .Write true
    (fun isLoc m => stepNodeOnRangeWrite w.activeProtectors isLoc off len m)
    off len hlen emb w t tag hinv hstep hloc hancOv
    (fun n hn hp => nwsr_foreignStepInert_write (hnoprune n hn hp))
  have h1 : ∀ w', execWorldRangeWrite w tag off len = .ok w' →
      ∃ t', Node.access t (some (emb tag)) .Write ⟨off⟩ ⟨len⟩ = .ok t' ∧
        TreeSimInvMulti off len emb w' t' := by
    intro w' hok
    obtain ⟨_, _, nodes', hw', hrel⟩ := (execWorldRangeWrite_ok_iff w w' tag off len hne).mp hok
    rw [hw']; exact hfwd nodes' hrel
  have h2 : ∀ e, execWorldRangeWrite w tag off len = .error e →
      ∃ msg, Node.access t (some (emb tag)) .Write ⟨off⟩ ⟨len⟩ = .error (.ub msg) := by
    intro e herr
    apply hbwd
    intro nodes' hrel
    have hok := (execWorldRangeWrite_ok_iff w { w with nodes := nodes' } tag off len hne).mpr
      ⟨hro, htag, nodes', rfl, hrel⟩
    rw [herr] at hok; cases hok
  refine ⟨h1, h2, ?_⟩
  intro t' hacc
  cases hr : execWorldRangeWrite w tag off len with
  | ok w' =>
    obtain ⟨t'', hacc'', hinv'⟩ := h1 w' hr
    rw [hacc] at hacc''; cases hacc''
    exact ⟨w', rfl, hinv'⟩
  | error e =>
    obtain ⟨msg, hmsg⟩ := h2 e hr
    rw [hacc] at hmsg; cases hmsg

/-- **Lifted multi-range `TreeBorrowsMemory.load` simulation** (`TreeSimInvMulti`). -/
theorem tbm_load_simulates_execWorldRangeRead_multi
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (len : Nat) (align : LibSpecr.Align)
    (id : Nat) (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (off : Nat)
    (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld) (tag : Nat)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, emb tag))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (haligned : Align.is_aligned align ptr.addr = true)
    (hoff : ptr.addr - alloc.addr = (off : Int))
    (hlen : len ≠ 0) (hbound : off + len ≤ alloc.data.length)
    (hinv : TreeSimInvMulti off len emb w alloc.extra.root)
    (htag : ∃ n, findNode? w.nodes tag = some n)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = locOf (some (emb tag)) (emb n.tag))
    (hancOv : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = true →
      rangesOverlap off len n.rangeOffset n.rangeLen = true)
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) false off len n = true →
      foreignStepInert w.activeProtectors false off len n = true) :
    (∀ w', execWorldRangeRead w tag off len = .ok w' →
      ∃ tbm' alloc', TreeBorrowsMemory.load tbm ptr ⟨len⟩ align =
          .ok ((alloc.data.drop off).take len, tbm') ∧
        tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
        TreeSimInvMulti off len emb w' alloc'.extra.root) ∧
    (∀ e, execWorldRangeRead w tag off len = .error e →
      ∃ msg, TreeBorrowsMemory.load tbm ptr ⟨len⟩ align = .error (.ub msg)) ∧
    (∀ r, TreeBorrowsMemory.load tbm ptr ⟨len⟩ align = .ok r →
      ∃ w', execWorldRangeRead w tag off len = .ok w') := by
  obtain ⟨h1, h2, h3⟩ := tree_read_simulates_node_access_multi off len
    (Nat.pos_of_ne_zero hlen) emb w alloc.extra.root tag hinv htag hloc hancOv hnoprune
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
    | ok t' => obtain ⟨w', hw', _⟩ := h3 t' hacc; exact ⟨w', hw'⟩
    | error e => rw [hacc] at hok; cases hok

/-- **Lifted multi-range `TreeBorrowsMemory.store` simulation** (`TreeSimInvMulti`). -/
theorem tbm_store_simulates_execWorldRangeWrite_multi
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (align : LibSpecr.Align)
    (id : Nat) (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (off : Nat)
    (emb : Nat → Gen.Path) (w : FnEntryBorrowWorld) (tag : Nat)
    (hprov : ptr.provenance = some (⟨(id : Int)⟩, emb tag))
    (halloc : tbm.mem.allocations[id]? = some alloc) (hlive : alloc.live = true)
    (haligned : Align.is_aligned align ptr.addr = true)
    (hoff : ptr.addr - alloc.addr = (off : Int))
    (hlen : bytes.length ≠ 0) (hbound : off + bytes.length ≤ alloc.data.length)
    (hinv : TreeSimInvMulti off bytes.length emb w alloc.extra.root)
    (hro : w.allocReadOnly = false)
    (htag : ∃ n, findNode? w.nodes tag = some n)
    (hloc : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = locOf (some (emb tag)) (emb n.tag))
    (hancOv : ∀ n ∈ w.nodes,
      (ancestorPathTags w.nodes tag).contains n.tag = true →
      rangesOverlap off bytes.length n.rangeOffset n.rangeLen = true)
    (hnoprune : ∀ n ∈ w.nodes,
      isPrunedForeignNode w.nodes (ancestorPathTags w.nodes tag) true off bytes.length n = true →
      foreignStepInert w.activeProtectors true off bytes.length n = true) :
    (∀ w', execWorldRangeWrite w tag off bytes.length = .ok w' →
      ∃ tbm' alloc', TreeBorrowsMemory.store tbm ptr bytes align = .ok tbm' ∧
        tbm'.mem.allocations[id]? = some alloc' ∧ alloc'.live = true ∧
        TreeSimInvMulti off bytes.length emb w' alloc'.extra.root) ∧
    (∀ e, execWorldRangeWrite w tag off bytes.length = .error e →
      ∃ msg, TreeBorrowsMemory.store tbm ptr bytes align = .error (.ub msg)) ∧
    (∀ tbm', TreeBorrowsMemory.store tbm ptr bytes align = .ok tbm' →
      ∃ w', execWorldRangeWrite w tag off bytes.length = .ok w') := by
  obtain ⟨h1, h2, h3⟩ := tree_write_simulates_node_access_multi off bytes.length
    (Nat.pos_of_ne_zero hlen) emb w alloc.extra.root tag hinv hro htag hloc hancOv hnoprune
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
    | ok t' => obtain ⟨w', hw', _⟩ := h3 t' hacc; exact ⟨w', hw'⟩
    | error e => rw [hacc] at hok; cases hok

/-- **Multi-window frame preservation for `TreeSimInvMulti`**: if `w, t` satisfy
`TreeSimInvMulti` on window `[off2, off2 + len2)` and an access on a **disjoint**
window `[off1, off1 + len1)` (`off1 + len1 ≤ off2 ∨ off2 + len2 ≤ off1`) updates
`(w, t) ↦ (w', t')` without mutating the Anneal state of any node overlapping
`[off2, off2 + len2)` (e.g., root stays `.unique` and sub-slice nodes are disjoint),
then `TreeSimInvMulti off2 len2 emb w' t'` is preserved! -/
theorem treeSimInvMulti_preserved_on_disjoint_window
    (off1 len1 off2 len2 : Nat) (hdisj : off1 + len1 ≤ off2 ∨ off2 + len2 ≤ off1)
    (emb : Nat → Gen.Path) (w w' : FnEntryBorrowWorld) (t t' : Gen.Node)
    (path : Option Gen.Path) (k : Gen.AccessKind)
    (hinv2 : TreeSimInvMulti off2 len2 emb w t)
    (hacc : Node.access t path k ⟨off1⟩ ⟨len1⟩ = .ok t')
    (hpost : TreeSimInvMulti off1 len1 emb w' t')
    (hap : w'.activeProtectors = w.activeProtectors)
    (hsameNode : ∀ n' ∈ w'.nodes, ∃ n ∈ w.nodes,
      n'.tag = n.tag ∧ n'.protector = n.protector ∧
      n'.rangeOffset = n.rangeOffset ∧ n'.rangeLen = n.rangeLen ∧
      (rangesOverlap off2 len2 n.rangeOffset n.rangeLen = true →
        n'.perm = n.perm ∧ n'.accessed = n.accessed)) :
    TreeSimInvMulti off2 len2 emb w' t' := by
  have hframe := node_access_frame_outside t t' path k off1 len1 hacc
  have hout2 : ∀ b, off2 ≤ b → b < off2 + len2 → b < off1 ∨ off1 + len1 ≤ b := by
    intro b h1 h2
    rcases hdisj with hd | hd
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  refine ⟨?_, hpost.surj, hpost.noProtIM, hpost.protUniqAcc⟩
  intro n' hn'
  obtain ⟨n, hn, htag, hprot, hro, hrl, hstay⟩ := hsameNode n' hn'
  obtain ⟨m, hm, hnod⟩ := hinv2.nodes n hn
  obtain ⟨m', hm', hprotM, _, hbytes⟩ := hframe (emb n.tag) m hm
  have hpe : n'.isProtected w'.activeProtectors = n.isProtected w.activeProtectors := by
    unfold TreeTagNode.isProtected; rw [hprot, hap]
  refine ⟨m', by rw [htag]; exact hm', ?_⟩
  rw [hro, hrl]
  cases hov : rangesOverlap off2 len2 n.rangeOffset n.rangeLen with
  | true =>
    simp only [hov, ↓reduceIte] at hnod ⊢
    obtain ⟨hpm, p, hp, hwin⟩ := hnod
    obtain ⟨hperm, haccN⟩ := hstay hov
    refine ⟨by rw [hprotM, hpm, ← hpe], p, by rw [hpe, hperm, haccN]; exact hp, fun b h1 h2 => ?_⟩
    rw [hbytes b (hout2 b h1 h2), hwin b h1 h2]
  | false =>
    simp only [hov, Bool.false_eq_true, ↓reduceIte] at hnod ⊢
    refine ⟨by rw [hprotM, hnod.1, ← hpe], fun b h1 h2 => ?_⟩
    rw [hbytes b (hout2 b h1 h2)]
    exact hnod.2 b h1 h2

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

/-- Nested `<[u8]>::split_at_mut`-style trace on real `TreeBorrowsMemory`
operations over an 8-byte slice (`[11u32, 22u32]` bytes at address `256`):
1. the caller takes a `.Frozen` sibling `&[u8]` (`[0]`) over the WHOLE slice;
2. the callee `f(outer : &mut [u8])` retags `outer` (`[1]`) at `FnEntry` with
   `fnImplicitWrites := fnIwOuter` (`false` = `#[rustc_no_writable]`);
3. (`stage ≥ 1`) `f` splits `outer` into the DISJOINT sub-slices `[0, 2)` and
   `[4, 6)` and passes them to `g(a, b)`, whose `FnEntry` retags mint `[1, 0]`
   and `[1, 1]` BELOW `outer` in a second frame; `g` writes BOTH sub-slices and
   returns (`end_call` of the inner frame), then `f` returns (`end_call` of the
   outer frame).
The result is the memory right before the caller reads through the sibling. -/
def tbmNestedSplitAtMutTrace (fnIwOuter : Bool) (stage : Nat) :
    Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 : Gen.TreeBorrowsMemory Gen.x86_64 :=
    { params := ⟨true⟩
      mem := { allocations := [mkRootAllocTB (tbU32Bytes 11 ++ tbU32Bytes 22) 256 4 .Stack],
               _phantom := ⟨⟩ } }
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
    { thin_pointer := { addr := 256, provenance := some (⟨0⟩, []) }, metadata := none }
  let (_, tbm1, _) ←
    TreeBorrowsMemory.retag_ptr tbm0 TreeBorrowsMemory.new_call rootPtr
      (.Ref .Immutable (slicePointeeInfoMR 8 4)) false true nwsrVtableLookup
  let (outerPtr, tbm2, feOuter) ←
    TreeBorrowsMemory.retag_ptr tbm1 TreeBorrowsMemory.new_call rootPtr
      (.Ref .Mutable (slicePointeeInfoMR 8 4)) true fnIwOuter nwsrVtableLookup
  if stage = 0 then pure tbm2 else do
    let aIn : Gen.Pointer Gen.TreeBorrowsProvenance :=
      { thin_pointer := outerPtr.thin_pointer, metadata := none }
    let bIn : Gen.Pointer Gen.TreeBorrowsProvenance :=
      { thin_pointer := { outerPtr.thin_pointer with addr := outerPtr.thin_pointer.addr + 4 },
        metadata := none }
    let (aPtr, tbm3, feInner1) ←
      TreeBorrowsMemory.retag_ptr tbm2 TreeBorrowsMemory.new_call aIn
        (.Ref .Mutable (slicePointeeInfoMR 2 1)) true false nwsrVtableLookup
    let (bPtr, tbm4, feInner2) ←
      TreeBorrowsMemory.retag_ptr tbm3 feInner1 bIn
        (.Ref .Mutable (slicePointeeInfoMR 2 1)) true false nwsrVtableLookup
    let tbm5 ← TreeBorrowsMemory.store tbm4 aPtr.thin_pointer (tbU8Bytes 71 ++ tbU8Bytes 72) ⟨1⟩
    let tbm6 ← TreeBorrowsMemory.store tbm5 bPtr.thin_pointer (tbU8Bytes 81 ++ tbU8Bytes 82) ⟨1⟩
    let tbm7 ← TreeBorrowsMemory.end_call tbm6 feInner2
    TreeBorrowsMemory.end_call tbm7 feOuter

/-- Outcome of the caller's read of `[off, off + len)` through the `.Frozen`
sibling `[0]` after `tbmNestedSplitAtMutTrace fnIwOuter stage`. -/
def tbmNestedSplitAtMutSiblingRead (fnIwOuter : Bool) (stage : Nat) (off : Int) (len : Nat) :
    Option (List (Option UInt8) ⊕ String) :=
  tbBytesOutcome (tbmNestedSplitAtMutTrace fnIwOuter stage >>= fun tbm =>
    TreeBorrowsMemory.load tbm { addr := 256 + off, provenance := some (⟨0⟩, [0]) } ⟨len⟩ ⟨1⟩ >>=
      fun r => pure r.1)

/-- **End-to-end NESTED disjoint sub-slice witness on real `TreeBorrowsMemory`
(`retag_ptr` → sub-slice `retag_ptr`s → writes → `end_call`s → sibling reads)**:
1. under a `#[rustc_no_writable]` outer `&mut [u8]` the whole nested trace
   succeeds with `TreeBorrowsMemory.wfLive`, and afterwards the `.Frozen`
   sibling still reads EVERY byte outside the two written sub-slices (the gap
   `[2, 4)` and the tail `[6, 8)`), while each written sub-slice (`[0, 2)`,
   `[4, 6)`) is byte-precisely `Disabled`;
2. right after the `#[rustc_no_writable]` outer `FnEntry` retag the sibling
   reads the WHOLE slice;
3. whereas a standard outer `&mut [u8]` (`FnEntry` implicit write) disables the
   sibling across the ENTIRE slice immediately at entry — before any sub-slice
   exists — and it stays dead after the nested trace. -/
theorem tbm_nestedSplitAtMut_noWritable_vs_writable :
    (∃ tbm', tbmNestedSplitAtMutTrace false 1 = .ok tbm' ∧ TreeBorrowsMemory.wfLive tbm') ∧
    tbmNestedSplitAtMutSiblingRead false 1 2 2 = some (.inl [some 0, some 0]) ∧
    tbmNestedSplitAtMutSiblingRead false 1 6 2 = some (.inl [some 0, some 0]) ∧
    tbmNestedSplitAtMutSiblingRead false 1 0 2 =
      some (.inr "Tree Borrows: local read of Disabled reference") ∧
    tbmNestedSplitAtMutSiblingRead false 1 4 2 =
      some (.inr "Tree Borrows: local read of Disabled reference") ∧
    tbmNestedSplitAtMutSiblingRead false 0 0 8 =
      some (.inl [some 11, some 0, some 0, some 0, some 22, some 0, some 0, some 0]) ∧
    tbmNestedSplitAtMutSiblingRead true 0 2 2 =
      some (.inr "Tree Borrows: local read of Disabled reference") ∧
    tbmNestedSplitAtMutSiblingRead true 0 6 2 =
      some (.inr "Tree Borrows: local read of Disabled reference") ∧
    (∃ tbm', tbmNestedSplitAtMutTrace true 1 = .ok tbm' ∧ TreeBorrowsMemory.wfLive tbm') ∧
    tbmNestedSplitAtMutSiblingRead true 1 2 2 =
      some (.inr "Tree Borrows: local read of Disabled reference") :=
  ⟨tbm_trace_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel,
   tbm_trace_ok_and_wfLive_of_bool (by decide +kernel), by decide +kernel⟩

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
layouts, contents, write offsets, and write types of `mkStaticAccessMachTB`. Symbolic choice-free
post-state `MachTB.wfLive` preservation across arbitrary `stepsTB n` runs for all
six harness families is proved in Section 6.4 (`stepsTB_wfLive_choiceFree`,
`machTB_staticAccess_steps_wfLive`, `machTB_harnesses_steps_wfLive`). -/
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

/-! ### Part 5 Addition: End-to-End `MachTB` Witness for `Box<u32>` Weak vs. `&mut u32` / `&u32` Strong Deallocation -/

/-- Callee taking a heap pointer `_1 : .Ptr ptrTy`, executing `Validate(_1, true)`
(`FnEntry` retag under `Function.implicit_writes := fnImplicitWrites`), then
deallocating `_1` via `IntrinsicOp.Deallocate` (`4` bytes, align `4`), and
returning (`end_call` on the now-dead heap allocation for `Box<u32>`). -/
def deallocCalleeFn (ptrTy : Gen.PtrType) (fnImplicitWrites : Bool) : Gen.Function where
  locals := ⟨[
    (localName 0, unitTyMR),
    (localName 1, .Ptr ptrTy),
    (localName 2, unitTyMR)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Validate (.Local (localName 1)) true],
      .Intrinsic .Deallocate
        [.Load (.Local (localName 1)),
         .Constant (.Int 4) u32TyMR,
         .Constant (.Int 4) u32TyMR]
        (.Local (localName 2)) (some (bbName 1)),
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0)) (.Tuple [] unitTyMR)],
      .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := fnImplicitWrites

/-- Caller allocating a 4-byte aligned heap allocation (`IntrinsicOp.Allocate`),
initializing it to `42u32`, calling `deallocCalleeFn` (`fnName 1`), and
returning `77u32` after callee exit. -/
def deallocCallerFn (ptrTy : Gen.PtrType) : Gen.Function where
  locals := ⟨[
    (localName 0, u32TyMR),
    (localName 1, .Ptr ptrTy),
    (localName 2, unitTyMR)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .StorageLive (localName 2)],
      .Intrinsic .Allocate
        [.Constant (.Int 4) u32TyMR, .Constant (.Int 4) u32TyMR]
        (.Local (localName 1)) (some (bbName 1)),
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Deref (.Load (.Local (localName 1))) u32TyMR) (.Constant (.Int 42) u32TyMR)],
      .Call (.Constant (.FnPointer (fnName 1)) (.Ptr .FnPtr)) .Rust
        [.ByValue (.Load (.Local (localName 1)))]
        (.Local (localName 2)) (some (bbName 2)) none,
      .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0)) (.Constant (.Int 77) u32TyMR)],
      .Return, .Regular⟩)]⟩
  start := bbName 0
  implicit_writes := true

/-- **End-to-end `MachTB` deallocation witness (`Box<u32>` `Protected::Weak` vs.
`&mut u32` / `&u32` `Protected::Strong`)**: executes the full MiniRust machine
(`IntrinsicOp.Allocate` → `Call` → `Validate(_, true)` → `IntrinsicOp.Deallocate`
→ `Return` / `end_call`):
1. `Box<u32>` (`Protected::Weak`) succeeds under BOTH `#[rustc_no_writable]`
   (`fnIw = false`) and standard (`fnIw = true`), marks the heap allocation dead
   (`live = false`), completes `end_call` on the dead allocation, returns `77u32`,
   and preserves `MachTB.wfLive`;
2. `&mut u32` (`Protected::Strong`) faults at `IntrinsicOp.Deallocate` with
   `"Tree Borrows: deallocating strongly protected allocation"` under BOTH
   `#[rustc_no_writable]` (`fnIw = false`) and standard (`fnIw = true`);
3. `&u32` (`Protected::Strong`) faults at `IntrinsicOp.Deallocate` with
   `"Tree Borrows: local write to protected Frozen reference"`. -/
theorem machTB_box_weak_vs_mut_strong_dealloc_e2e :
    let boxPtrTy : Gen.PtrType := .Box (intPointeeInfo u32ItMR)
    let mutPtrTy : Gen.PtrType := refPtrType .mut u32ItMR
    let shrPtrTy : Gen.PtrType := refPtrType .not u32ItMR
    let mBoxNoWr := mkTwoFnMachTB (deallocCallerFn boxPtrTy) (deallocCalleeFn boxPtrTy false)
    let mBoxWr := mkTwoFnMachTB (deallocCallerFn boxPtrTy) (deallocCalleeFn boxPtrTy true)
    let mMutNoWr := mkTwoFnMachTB (deallocCallerFn mutPtrTy) (deallocCalleeFn mutPtrTy false)
    let mMutWr := mkTwoFnMachTB (deallocCallerFn mutPtrTy) (deallocCalleeFn mutPtrTy true)
    let mShr := mkTwoFnMachTB (deallocCallerFn shrPtrTy) (deallocCalleeFn shrPtrTy false)
    machRetSnapshot mBoxNoWr 12 = some (some (true, [some 77, some 0, some 0, some 0]), [1]) ∧
    (∃ m', Interp.stepsTB 12 mBoxNoWr = .ok m' ∧ MachTB.wfLive m') ∧
    machRetSnapshot mBoxWr 12 = some (some (true, [some 77, some 0, some 0, some 0]), [1]) ∧
    (∃ m', Interp.stepsTB 12 mBoxWr = .ok m' ∧ MachTB.wfLive m') ∧
    machStopOutcome mMutNoWr 8 =
      some (.ub "Tree Borrows: deallocating strongly protected allocation") ∧
    machStopOutcome mMutWr 8 =
      some (.ub "Tree Borrows: deallocating strongly protected allocation") ∧
    machStopOutcome mShr 8 =
      some (.ub "Tree Borrows: local write to protected Frozen reference") :=
  ⟨by decide +kernel,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel,
   machTB_steps_ok_and_wfLive_of_bool (by decide +kernel),
   by decide +kernel,
   by decide +kernel,
   by decide +kernel⟩


/-! ### 5.3 Faithful-Erasure Audits: Fuel-Universal `stepMirFnWithParamMap` ↔ `stepMirFn` Alignment & `permToMiniRust` Kernel -/

/-- **Universal multi-step alignment of the parameter-map runner with
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`**: under ANY parameter map
that assigns `rustcNoWritable` to every local, `runMirWithParamMap` coincides
with `runMirDirect` — the fuel-bounded iteration of the REAL trusted
`stepMirFn` — for EVERY body, EVERY machine state, and EVERY fuel `n`. Every
`StatementKind.retag .fnEntry` (`fnEntryRetagPerm`), `StatementKind.assign`
(including deref reads / writes), and `TerminatorKind.return_` step of such a
run is therefore a step of the trusted semantics itself; the adapter
`stepMirFnWithParamMap` adds behaviour ONLY at `FnEntry` retags of parameters
mapped to another policy (`stepMirFnWithParamMap_eq_stepMirFn_of_rustcNoWritable_at_pc`),
so the `writableChildWrite` side of `trusted_stepMirFn_forgetStyle_noWritable_vs_writable`
is a statement about that Anneal-side adapter, not about `stepMirFn`. -/
theorem runMirWithParamMap_eq_runMirDirect_of_rustcNoWritable
    (paramMap : FnParamRetagMap) (body : CapturedMir)
    (hmap : ∀ l, paramMap.policyFor l = .rustcNoWritable) :
    ∀ (n : Nat) (s : MachineState),
      runMirWithParamMap paramMap body n s = runMirDirect body n s
  | 0, _ => rfl
  | n + 1, s => by
    have ih := runMirWithParamMap_eq_runMirDirect_of_rustcNoWritable paramMap body hmap n
    simp only [runMirWithParamMap, runMirDirect,
      stepMirFnWithParamMap_eq_stepMirFn_of_rustcNoWritable_at_pc paramMap body s
        (fun _ place _ _ _ => hmap place.local_), ih]

/-- **Fuel monotonicity of `runMirWithParamMap`**: once a run has produced a
definite outcome (`.retScalar` or `.ub`, i.e. anything but the out-of-fuel /
unsupported marker `.other`), every larger fuel produces the same outcome. -/
theorem runMirWithParamMap_fuel_mono (paramMap : FnParamRetagMap) (body : CapturedMir) :
    ∀ (n : Nat) (s : MachineState) (r : MirParamRunOutcome),
      runMirWithParamMap paramMap body n s = r → r ≠ .other →
      ∀ m, n ≤ m → runMirWithParamMap paramMap body m s = r
  | 0, _, r, h, hne, _, _ => absurd h.symm hne
  | n + 1, s, r, h, hne, m, hm => by
    cases m with
    | zero => omega
    | succ m =>
      simp only [runMirWithParamMap] at h ⊢
      split at h
      · rename_i s' _
        exact runMirWithParamMap_fuel_mono paramMap body n s' r h hne m (by omega)
      · exact h
      · exact h
      · exact absurd h.symm hne

/-- **Fuel-universal `Trusted` separation (`core::mem::forget`-style witness)**:
for the two-function witness of `trusted_stepMirFn_forgetStyle_noWritable_vs_writable`
and EVERY fuel `n`:
1. the all-`rustcNoWritable` adapter run IS the run of the real trusted
   `stepMirFn` (`runMirDirect`);
2. the real trusted `stepMirFn` NEVER reports UB on this program, at any fuel,
   and returns `42u32` at every fuel `n ≥ 12` — `Retag([fn entry])`
   (`fnEntryRetagPerm .mut = .reservedFrz false`), the deref read `*_3`, and
   both `return`s are steps of the trusted semantics itself;
3. the `writableChildWrite` UB at every fuel `n ≥ 12` is produced ONLY by the
   Anneal-side adapter `stepMirFnWithParamMap` (`applyParamFnEntryImplicitWrite`),
   which is NOT part of `Trusted.Rustc.V2026_06_01.MirSemantics`. -/
theorem trusted_stepMirFn_forgetStyle_separation_all_fuel :
    let s0 := initMachineStateWithCallees forgetLikeMirBody [.scalar ⟨42, 4⟩]
      [forgetLikeCalleeMirBody]
    (∀ n, runMirWithParamMap (FnParamRetagMap.empty .rustcNoWritable) forgetLikeMirBody n s0 =
      runMirDirect forgetLikeMirBody n s0) ∧
    (∀ n, 12 ≤ n → runMirDirect forgetLikeMirBody n s0 = .retScalar 42 4) ∧
    (∀ n, runMirDirect forgetLikeMirBody n s0 ≠ .ub) ∧
    (∀ n, 12 ≤ n →
      runMirWithParamMap (FnParamRetagMap.empty .writableChildWrite) forgetLikeMirBody n s0 =
        .ub) := by
  intro s0
  have halign : ∀ n, runMirWithParamMap (FnParamRetagMap.empty .rustcNoWritable)
      forgetLikeMirBody n s0 = runMirDirect forgetLikeMirBody n s0 :=
    fun n => runMirWithParamMap_eq_runMirDirect_of_rustcNoWritable _ forgetLikeMirBody
      (fun _ => rfl) n s0
  have h12 : runMirWithParamMap (FnParamRetagMap.empty .rustcNoWritable) forgetLikeMirBody 12 s0 =
      .retScalar 42 4 := trusted_stepMirFn_forgetStyle_noWritable_vs_writable.2.1
  have h12w : runMirWithParamMap (FnParamRetagMap.empty .writableChildWrite) forgetLikeMirBody 12
      s0 = .ub := trusted_stepMirFn_forgetStyle_noWritable_vs_writable.2.2
  have hge : ∀ n, 12 ≤ n → runMirDirect forgetLikeMirBody n s0 = .retScalar 42 4 := by
    intro n hn
    rw [← halign n]
    exact runMirWithParamMap_fuel_mono _ forgetLikeMirBody 12 s0 _ h12 (by decide) n hn
  refine ⟨halign, hge, fun n hub => ?_, fun n hn =>
    runMirWithParamMap_fuel_mono _ forgetLikeMirBody 12 s0 _ h12w (by decide) n hn⟩
  rcases Nat.lt_or_ge n 12 with hlt | hge12
  · rw [← halign n] at hub
    have := runMirWithParamMap_fuel_mono _ forgetLikeMirBody n s0 _ hub (by decide) 12
      (Nat.le_of_lt hlt)
    rw [h12] at this
    cases this
  · rw [hge n hge12] at hub
    cases hub

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

/-! ### 5.4 Closed Non-Vacuity Canaries for Symbolic Whole-Tree `retag_ptr`, `end_call`, `deallocate`, Pruning, & `TreeSimInvMulti` -/

/-- **Closed non-vacuity canary for symbolic whole-tree `retag_ptr` simulation**:
exercises `tbm_retag_ptr_fnEntry_mutOrBox_simulates_world`,
`tbm_retag_ptr_fnEntry_mutOrBox_simulates_traversalOrderDirect`,
`tbm_retag_ptr_fnEntry_shared_wholeTree`, and
`tbm_retag_ptr_fnEntry_zst_wholeTree` on concrete live `TreeBorrowsMemory`
trees (`twoBranchTreeMR`) with zero remaining hypotheses:
1. `#[rustc_no_writable]` (`&mut u32`) retag preserves `TreeSimInv` across the
   4-node post-tree (with `Protected::Strong`, sibling `.Frozen` kept alive);
2. standard `&mut u32` retag preserves `TreeSimInv` (disabling the `.Frozen` sibling);
3. `Box<u32>` `#[rustc_no_writable]` retag preserves `TreeSimInv` with `Protected::Weak`;
4. `&u32` shared retag and `&mut ()` ZST retag fire their whole-tree theorems cleanly. -/
theorem canary_symbolic_retag_ptr_simulation :
    (∃ w' childTag tbm' alloc' mc,
      execFnEntryMutRetagPrunedSourceOrder (mkTwoBranchWorld .unique .frozen) 1 0 4
        .rustcNoWritable false = .ok (w', childTag) ∧
      TreeBorrowsMemory.retag_ptr (mkTbmWithTree (twoBranchTreeMR (.Unprot .Frozen)))
        TreeBorrowsMemory.new_call (ThinPointer.widen (tbmTreePtr [0]) .none)
        (ptrTypeOfParamKind .mutable (pointeeInfoOfFacts ⟨true, true, true⟩ 4 4 []))
        true false nwsrVtableLookup =
        .ok (ThinPointer.widen (tbmTreePtr [0, 0]) .none, tbm', ⟨[(⟨0⟩, [0, 0])]⟩) ∧
      tbm'.mem.allocations[0]? = some alloc' ∧
      nodeAt alloc'.extra.root [0, 0] = some mc ∧ mc.«protected» = .Strong ∧
      TreeSimInv 0 4 (extendEmb twoBranchEmb 3 [0, 0]) w' alloc'.extra.root) ∧
    (∃ w' childTag tbm' alloc' mc,
      execFnEntryMutRetagTraversalOrderDirect (mkTwoBranchWorld .unique .frozen) 1 0 4
        .writableChildWrite false = .ok (w', childTag) ∧
      TreeBorrowsMemory.retag_ptr (mkTbmWithTree (twoBranchTreeMR (.Unprot .Frozen)))
        TreeBorrowsMemory.new_call (ThinPointer.widen (tbmTreePtr [0]) .none)
        (ptrTypeOfParamKind .mutable (pointeeInfoOfFacts ⟨true, true, true⟩ 4 4 []))
        true true nwsrVtableLookup =
        .ok (ThinPointer.widen (tbmTreePtr [0, 0]) .none, tbm', ⟨[(⟨0⟩, [0, 0])]⟩) ∧
      tbm'.mem.allocations[0]? = some alloc' ∧
      nodeAt alloc'.extra.root [0, 0] = some mc ∧ mc.«protected» = .Strong ∧
      TreeSimInv 0 4 (extendEmb twoBranchEmb 3 [0, 0]) w' alloc'.extra.root) ∧
    (∃ w' childTag tbm' alloc' mc,
      execFnEntryMutRetagPrunedSourceOrder (mkTwoBranchWorld .unique .frozen) 1 0 4
        .rustcNoWritable false = .ok (w', childTag) ∧
      TreeBorrowsMemory.retag_ptr (mkTbmWithTree (twoBranchTreeMR (.Unprot .Frozen)))
        TreeBorrowsMemory.new_call (ThinPointer.widen (tbmTreePtr [0]) .none)
        (ptrTypeOfParamKind .box (pointeeInfoOfFacts ⟨true, true, true⟩ 4 4 []))
        true false nwsrVtableLookup =
        .ok (ThinPointer.widen (tbmTreePtr [0, 0]) .none, tbm', ⟨[(⟨0⟩, [0, 0])]⟩) ∧
      tbm'.mem.allocations[0]? = some alloc' ∧
      nodeAt alloc'.extra.root [0, 0] = some mc ∧ mc.«protected» = .Weak ∧
      TreeSimInv 0 4 (extendEmb twoBranchEmb 3 [0, 0]) w' alloc'.extra.root) ∧
    (∃ tbm' alloc' mc,
      TreeBorrowsMemory.retag_ptr (mkTbmWithTree (twoBranchTreeMR (.Unprot .Frozen)))
        TreeBorrowsMemory.new_call (ThinPointer.widen (tbmTreePtr [0]) .none)
        (ptrTypeOfParamKind .shared (pointeeInfoOfFacts ⟨true, true, true⟩ 4 4 []))
        true false nwsrVtableLookup =
        .ok (ThinPointer.widen (tbmTreePtr [0, 0]) .none, tbm', ⟨[(⟨0⟩, [0, 0])]⟩) ∧
      tbm'.mem.allocations[0]? = some alloc' ∧
      nodeAt alloc'.extra.root [0, 0] = some mc ∧ mc.«protected» = .Strong) ∧
    (∃ tbm' alloc' mc,
      (∀ fnIw : Bool,
        TreeBorrowsMemory.retag_ptr (mkTbmWithTree (twoBranchTreeMR (.Unprot .Frozen)))
          TreeBorrowsMemory.new_call (ThinPointer.widen (tbmTreePtr [0]) .none)
          (ptrTypeOfParamKind .mutable (pointeeInfoOfFacts ⟨true, true, true⟩ 0 1 []))
          true fnIw nwsrVtableLookup =
          .ok (ThinPointer.widen (tbmTreePtr [0, 0]) .none, tbm', ⟨[(⟨0⟩, [0, 0])]⟩)) ∧
      tbm'.mem.allocations[0]? = some alloc' ∧
      nodeAt alloc'.extra.root [0, 0] = some mc ∧ mc.«protected» = .Strong) := by
  have hinv : TreeSimInv 0 4 twoBranchEmb (mkTwoBranchWorld .unique .frozen)
      (twoBranchTreeMR (.Unprot .Frozen)) :=
    treeSimInv_of_bool _ _ _ _ _ (by decide +kernel)
  have hloc : ∀ n ∈ (mkTwoBranchWorld .unique .frozen).nodes,
      (ancestorPathTags (mkTwoBranchWorld .unique .frozen).nodes 1).contains n.tag =
        locOf (some (twoBranchEmb 1)) (twoBranchEmb n.tag) := by decide +kernel
  have hfreshT : ∀ n ∈ (mkTwoBranchWorld .unique .frozen).nodes,
      n.tag ≠ (mkTwoBranchWorld .unique .frozen).nextTag := by decide +kernel
  have hfreshP : ∀ n ∈ (mkTwoBranchWorld .unique .frozen).nodes,
      n.protector ≠ some (mkTwoBranchWorld .unique .frozen).nextProtector := by decide +kernel
  have hrooted : BorrowTreeRootedWF (mkTwoBranchWorld .unique .frozen) 0 := by
    refine ⟨by decide +kernel, ?_⟩
    intro n hn
    simp only [mkTwoBranchWorld, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact ⟨0, by decide, ReachesRoot.root _ rfl rfl⟩
    · exact ⟨1, by decide, ReachesRoot.step 0 1 0 _ rfl rfl (ReachesRoot.root _ rfl rfl)⟩
    · exact ⟨1, by decide, ReachesRoot.step 0 2 0 _ rfl rfl (ReachesRoot.root _ rfl rfl)⟩
  -- 1. `#[rustc_no_writable]` `&mut u32`
  obtain ⟨pNode1, hpNode1, h1ok, _, _⟩ := tbm_retag_ptr_fnEntry_mutOrBox_simulates_world
    (mkTbmWithTree (twoBranchTreeMR (.Unprot .Frozen))) TreeBorrowsMemory.new_call
    (ThinPointer.widen (tbmTreePtr [0]) .none) nwsrVtableLookup
    ⟨true, true, true⟩ .mutable ⟨true, true⟩ (by decide) rfl rfl
    0 _ 0 4 4 (by decide) [] [true, true, true, true] rfl
    twoBranchEmb (mkTwoBranchWorld .unique .frozen) 1 false
    rfl rfl rfl (by decide) (by decide) hinv ⟨_, rfl⟩ hfreshT hfreshP
    hloc (by decide +kernel) (fun h => by cases h)
  have hp1eq : pNode1.children.length = 0 := by
    change nodeAt (twoBranchTreeMR (.Unprot .Frozen)) [0] = some pNode1 at hpNode1
    have h0 : nodeAt (twoBranchTreeMR (.Unprot .Frozen)) [0] =
        some ⟨[], List.replicate 4 (.Unprot .Unique), .No⟩ := rfl
    rw [h0] at hpNode1; cases hpNode1; rfl
  have h1ok_check : (execFnEntryMutRetagPrunedSourceOrder (mkTwoBranchWorld .unique .frozen) 1 0 4
      .rustcNoWritable false).isOk = true := by decide +kernel
  have h1w : ∃ res, execFnEntryMutRetagPrunedSourceOrder (mkTwoBranchWorld .unique .frozen) 1 0 4
      .rustcNoWritable false = .ok res := by
    cases h : execFnEntryMutRetagPrunedSourceOrder (mkTwoBranchWorld .unique .frozen) 1 0 4
        .rustcNoWritable false with
    | ok res => exact ⟨res, rfl⟩
    | error _ => rw [h] at h1ok_check; cases h1ok_check
  obtain ⟨⟨w1, c1⟩, hw1⟩ := h1w
  obtain ⟨tbm1, alloc1, hret1, hal1, _, _, ⟨mc1, hmc1, hmc1p⟩, hinv1⟩ := h1ok w1 c1 hw1
  rw [hp1eq] at hret1 hmc1 hinv1
  -- 2. Standard `&mut u32` via `execFnEntryMutRetagTraversalOrderDirect`
  obtain ⟨pNode2, hpNode2, h2ok, _, _⟩ := tbm_retag_ptr_fnEntry_mutOrBox_simulates_traversalOrderDirect
    (mkTbmWithTree (twoBranchTreeMR (.Unprot .Frozen))) TreeBorrowsMemory.new_call
    (ThinPointer.widen (tbmTreePtr [0]) .none) nwsrVtableLookup
    ⟨true, true, true⟩ .mutable ⟨true, false⟩ (by decide) rfl rfl
    0 _ 0 4 4 (by decide) [] [true, true, true, true] rfl
    twoBranchEmb (mkTwoBranchWorld .unique .frozen) 0 1 false hrooted
    rfl rfl rfl (by decide) (by decide) hinv ⟨_, rfl⟩ hfreshT hfreshP
    hloc (by decide +kernel) (fun _ => ⟨rfl, rfl⟩)
  have hp2eq : pNode2.children.length = 0 := by
    change nodeAt (twoBranchTreeMR (.Unprot .Frozen)) [0] = some pNode2 at hpNode2
    have h0 : nodeAt (twoBranchTreeMR (.Unprot .Frozen)) [0] =
        some ⟨[], List.replicate 4 (.Unprot .Unique), .No⟩ := rfl
    rw [h0] at hpNode2; cases hpNode2; rfl
  have h2ok_check : (execFnEntryMutRetagTraversalOrderDirect (mkTwoBranchWorld .unique .frozen) 1 0 4
      .writableChildWrite false).isOk = true := by decide +kernel
  have h2w : ∃ res, execFnEntryMutRetagTraversalOrderDirect (mkTwoBranchWorld .unique .frozen) 1 0 4
      .writableChildWrite false = .ok res := by
    cases h : execFnEntryMutRetagTraversalOrderDirect (mkTwoBranchWorld .unique .frozen) 1 0 4
        .writableChildWrite false with
    | ok res => exact ⟨res, rfl⟩
    | error _ => rw [h] at h2ok_check; cases h2ok_check
  obtain ⟨⟨w2, c2⟩, hw2⟩ := h2w
  obtain ⟨tbm2, alloc2, hret2, hal2, _, _, ⟨mc2, hmc2, hmc2p⟩, hinv2⟩ := h2ok w2 c2 hw2
  rw [hp2eq] at hret2 hmc2 hinv2
  -- 3. `Box<u32>` `#[rustc_no_writable]`
  obtain ⟨pNode3, hpNode3, h3ok, _, _⟩ := tbm_retag_ptr_fnEntry_mutOrBox_simulates_world
    (mkTbmWithTree (twoBranchTreeMR (.Unprot .Frozen))) TreeBorrowsMemory.new_call
    (ThinPointer.widen (tbmTreePtr [0]) .none) nwsrVtableLookup
    ⟨true, true, true⟩ .box ⟨true, true⟩ (by decide) rfl rfl
    0 _ 0 4 4 (by decide) [] [true, true, true, true] rfl
    twoBranchEmb (mkTwoBranchWorld .unique .frozen) 1 false
    rfl rfl rfl (by decide) (by decide) hinv ⟨_, rfl⟩ hfreshT hfreshP
    hloc (by decide +kernel) (fun h => by cases h)
  have hp3eq : pNode3.children.length = 0 := by
    change nodeAt (twoBranchTreeMR (.Unprot .Frozen)) [0] = some pNode3 at hpNode3
    have h0 : nodeAt (twoBranchTreeMR (.Unprot .Frozen)) [0] =
        some ⟨[], List.replicate 4 (.Unprot .Unique), .No⟩ := rfl
    rw [h0] at hpNode3; cases hpNode3; rfl
  obtain ⟨tbm3, alloc3, hret3, hal3, _, _, ⟨mc3, hmc3, hmc3p⟩, hinv3⟩ := h3ok w1 c1 hw1
  rw [hp3eq] at hret3 hmc3 hinv3
  -- 4. Shared `&u32`
  obtain ⟨tbm4, alloc4, mc4, hret4, hal4, _, _, hmc4, hmc4p, _, _⟩ :=
    tbm_retag_ptr_fnEntry_shared_wholeTree
      (mkTbmWithTree (twoBranchTreeMR (.Unprot .Frozen))) TreeBorrowsMemory.new_call
      (ThinPointer.widen (tbmTreePtr [0]) .none) nwsrVtableLookup
      ⟨true, true, true⟩ ⟨true, true⟩ rfl 0 [0] _ _ 0 4 4 [] [true, true, true, true] rfl
      rfl rfl rfl (by decide) (by decide) rfl (by
        intro q m hm i hi _
        have hmem : q ∈ nodePaths (twoBranchTreeMR (.Unprot .Frozen)) :=
          nodeAt_mem_nodePaths _ q m hm
        have hpaths : nodePaths (twoBranchTreeMR (.Unprot .Frozen)) = [[], [0], [1]] := rfl
        rw [hpaths] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        have hi4 : 0 + i < 4 := by rw [Nat.zero_add]; simpa using hi
        rcases hmem with rfl | rfl | rfl
        · change some (twoBranchTreeMR (.Unprot .Frozen)) = some m at hm
          cases hm
          exact ⟨.Unprot .Unique, .Unprot .Unique, nwsr_getElem?_replicate_lt hi4, rfl⟩
        · change some ⟨[], List.replicate 4 (.Unprot .Unique), .No⟩ = some m at hm
          cases hm
          exact ⟨.Unprot .Unique, .Unprot .Unique, nwsr_getElem?_replicate_lt hi4, rfl⟩
        · change some ⟨[], List.replicate 4 (.Unprot .Frozen), .No⟩ = some m at hm
          cases hm
          exact ⟨.Unprot .Frozen, .Unprot .Frozen, nwsr_getElem?_replicate_lt hi4, rfl⟩)
  -- 5. ZST `&mut ()`
  obtain ⟨tbm5, alloc5, mc5, hret5, hal5, _, _, hmc5, hmc5eq, _, _, _⟩ :=
    tbm_retag_ptr_fnEntry_zst_wholeTree
      (mkTbmWithTree (twoBranchTreeMR (.Unprot .Frozen))) TreeBorrowsMemory.new_call
      (ThinPointer.widen (tbmTreePtr [0]) .none) nwsrVtableLookup
      ⟨true, true, true⟩ .mutable (by decide) rfl
      0 [0] _ _ 0 1 rfl rfl rfl (by decide) (by decide) rfl
  exact ⟨⟨w1, c1, tbm1, alloc1, mc1, hw1, hret1, hal1, hmc1, hmc1p, hinv1⟩,
    ⟨w2, c2, tbm2, alloc2, mc2, hw2, hret2, hal2, hmc2, hmc2p, hinv2⟩,
    ⟨w1, c1, tbm3, alloc3, mc3, hw1, hret3, hal3, hmc3, hmc3p, hinv3⟩,
    ⟨tbm4, alloc4, mc4, hret4, hal4, hmc4, hmc4p⟩,
    ⟨tbm5, alloc5, mc5, hret5, hal5, hmc5, by rw [hmc5eq]; rfl⟩⟩

/-- **Closed non-vacuity canary for symbolic multi-entry `end_call` simulation**:
instantiates `tbm_end_call_simulates_execFrameExitMiniRust` (ZERO remaining
hypotheses!) on:
1. the 2-entry overlapping frame `[(1, 8), (2, 7)]` on `exitOrderWorld` / `exitOrderTreeMR`
   (succeeds on both sides, preserves `TreeSimInv` and `wfLive`);
2. the reversed 2-entry frame `[(2, 7), (1, 8)]` on `exitOrderWorld` / `exitOrderTreeMR`
   (UB on both sides via the symbolic error direction!);
3. the singleton frame `[(1, 7)]` on `exitImplicitWorld none` / `exitImplicitTreeMR false`
   (succeeds, preserves `TreeSimInv` with `SkipChildrenOfAccessed` leaving child `3` untouched)
   and `exitImplicitWorld (some 5)` / `exitImplicitTreeMR true` (UB on both sides!). -/
theorem canary_symbolic_endCall_multiEntry_simulation :
    (∃ w' tbm' alloc',
      execFrameExitMiniRust exitOrderWorld [(1, 8), (2, 7)] = .ok w' ∧
      TreeBorrowsMemory.end_call (mkTbmWithTree exitOrderTreeMR)
        ⟨[(⟨0⟩, [0]), (⟨0⟩, [0, 0])]⟩ = .ok tbm' ∧
      tbm'.mem.allocations[0]? = some alloc' ∧
      TreeSimInv 0 8 exitOrderEmb w' alloc'.extra.root) ∧
    (∃ e msg,
      execFrameExitMiniRust exitOrderWorld [(2, 7), (1, 8)] = .error e ∧
      TreeBorrowsMemory.end_call (mkTbmWithTree exitOrderTreeMR)
        ⟨[(⟨0⟩, [0, 0]), (⟨0⟩, [0])]⟩ = .error (.ub msg)) ∧
    (∃ w' tbm' alloc',
      execFrameExitMiniRust (exitImplicitWorld none) [(1, 7)] = .ok w' ∧
      TreeBorrowsMemory.end_call (mkTbmWithTree (exitImplicitTreeMR false))
        ⟨[(⟨0⟩, [0])]⟩ = .ok tbm' ∧
      tbm'.mem.allocations[0]? = some alloc' ∧
      TreeSimInv 0 8 exitImplicitEmb w' alloc'.extra.root) ∧
    (∃ e msg,
      execFrameExitMiniRust (exitImplicitWorld (some 5)) [(1, 7)] = .error e ∧
      TreeBorrowsMemory.end_call (mkTbmWithTree (exitImplicitTreeMR true))
        ⟨[(⟨0⟩, [0])]⟩ = .error (.ub msg)) := by
  have hlenOrder : ∀ q m, nodeAt exitOrderTreeMR q = some m → m.permissions.length = 8 := by
    intro q m hm
    have hmem := nodeAt_mem_nodePaths exitOrderTreeMR q m hm
    have hps : nodePaths exitOrderTreeMR = [[], [0], [0, 0]] := rfl
    rw [hps] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> (cases hm; rfl)
  have houtOrder : ∀ (tp : Nat × Nat) (_ : tp ∈ ([(1, 8), (2, 7)] : List (Nat × Nat))),
      ∀ m, nodeAt exitOrderTreeMR (exitOrderEmb tp.1) = some m → OutsideNoProtectorAccess 0 8 m := by
    intro tp _ m hm b p hp hb
    have hlt : b < m.permissions.length := (List.getElem?_eq_some_iff.mp hp).1
    have h8 := hlenOrder _ m hm
    exfalso; omega
  have houtOrderRev : ∀ (tp : Nat × Nat) (_ : tp ∈ ([(2, 7), (1, 8)] : List (Nat × Nat))),
      ∀ m, nodeAt exitOrderTreeMR (exitOrderEmb tp.1) = some m → OutsideNoProtectorAccess 0 8 m := by
    intro tp _ m hm b p hp hb
    have hlt : b < m.permissions.length := (List.getElem?_eq_some_iff.mp hp).1
    have h8 := hlenOrder _ m hm
    exfalso; omega
  have hinvOrder : TreeSimInv 0 8 exitOrderEmb exitOrderWorld exitOrderTreeMR :=
    treeSimInv_of_bool _ _ _ _ _ (by decide +kernel)
  -- 1. `[(1, 8), (2, 7)]` ok
  obtain ⟨h1ok, _, _⟩ := tbm_end_call_simulates_execFrameExitMiniRust [(1, 8), (2, 7)]
    (mkTbmWithTree exitOrderTreeMR) 0 _ 0 8 (by decide) exitOrderEmb exitOrderWorld
    rfl rfl hlenOrder hinvOrder (by decide +kernel) (by decide +kernel)
    (by intro tp htp; simp only [List.mem_cons, List.not_mem_nil, or_false] at htp;
        rcases htp with rfl | rfl <;> exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro tp htp n hn; revert tp htp n hn; decide +kernel) houtOrder
  have h1chk : (execFrameExitMiniRust exitOrderWorld [(1, 8), (2, 7)]).isOk = true := by decide +kernel
  have h1w : ∃ w', execFrameExitMiniRust exitOrderWorld [(1, 8), (2, 7)] = .ok w' := by
    cases h : execFrameExitMiniRust exitOrderWorld [(1, 8), (2, 7)] with
    | ok w' => exact ⟨w', rfl⟩
    | error _ => rw [h] at h1chk; cases h1chk
  obtain ⟨w1, hw1⟩ := h1w
  obtain ⟨tbm1, alloc1, hend1, hal1, _, _, hinv1⟩ := h1ok w1 hw1
  -- 2. Reversed `[(2, 7), (1, 8)]` UB
  obtain ⟨_, h2err, _⟩ := tbm_end_call_simulates_execFrameExitMiniRust [(2, 7), (1, 8)]
    (mkTbmWithTree exitOrderTreeMR) 0 _ 0 8 (by decide) exitOrderEmb exitOrderWorld
    rfl rfl hlenOrder hinvOrder (by decide +kernel) (by decide +kernel)
    (by intro tp htp; simp only [List.mem_cons, List.not_mem_nil, or_false] at htp;
        rcases htp with rfl | rfl <;> exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro tp htp n hn; revert tp htp n hn; decide +kernel) houtOrderRev
  have h2errW : execFrameExitMiniRust exitOrderWorld [(2, 7), (1, 8)] =
      .error (.conflictedProtectedChildWrite 1) := rfl
  obtain ⟨msg2, hmsg2⟩ := h2err _ h2errW
  -- 3. `exitImplicitWorld none` ok
  have hlenImp : ∀ (b : Bool) q m, nodeAt (exitImplicitTreeMR b) q = some m → m.permissions.length = 8 := by
    intro b q m hm
    cases b with
    | false =>
      have hmem := nodeAt_mem_nodePaths (exitImplicitTreeMR false) q m hm
      have hps : nodePaths (exitImplicitTreeMR false) = [[], [0], [0, 0], [1]] := rfl
      rw [hps] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> (cases hm; rfl)
    | true =>
      have hmem := nodeAt_mem_nodePaths (exitImplicitTreeMR true) q m hm
      have hps : nodePaths (exitImplicitTreeMR true) = [[], [0], [0, 0], [1]] := rfl
      rw [hps] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> (cases hm; rfl)
  have houtImp : ∀ (b : Bool) (tp : Nat × Nat) (_ : tp ∈ ([(1, 7)] : List (Nat × Nat))),
      ∀ m, nodeAt (exitImplicitTreeMR b) (exitImplicitEmb tp.1) = some m → OutsideNoProtectorAccess 0 8 m := by
    intro b tp _ m hm b0 p hp hb
    have hlt : b0 < m.permissions.length := (List.getElem?_eq_some_iff.mp hp).1
    have h8 := hlenImp b _ m hm
    exfalso; omega
  obtain ⟨h3ok, _, _⟩ := tbm_end_call_simulates_execFrameExitMiniRust [(1, 7)]
    (mkTbmWithTree (exitImplicitTreeMR false)) 0 _ 0 8 (by decide) exitImplicitEmb (exitImplicitWorld none)
    rfl rfl (hlenImp false) (treeSimInv_of_bool _ _ _ _ _ (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
    (by intro tp htp; simp only [List.mem_cons, List.not_mem_nil, or_false] at htp; rcases htp with rfl;
        exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro tp htp n hn; revert tp htp n hn; decide +kernel) (houtImp false)
  have h3chk : (execFrameExitMiniRust (exitImplicitWorld none) [(1, 7)]).isOk = true := by decide +kernel
  have h3w : ∃ w', execFrameExitMiniRust (exitImplicitWorld none) [(1, 7)] = .ok w' := by
    cases h : execFrameExitMiniRust (exitImplicitWorld none) [(1, 7)] with
    | ok w' => exact ⟨w', rfl⟩
    | error _ => rw [h] at h3chk; cases h3chk
  obtain ⟨w3, hw3⟩ := h3w
  obtain ⟨tbm3, alloc3, hend3, hal3, _, _, hinv3⟩ := h3ok w3 hw3
  -- 4. `exitImplicitWorld (some 5)` UB
  obtain ⟨_, h4err, _⟩ := tbm_end_call_simulates_execFrameExitMiniRust [(1, 7)]
    (mkTbmWithTree (exitImplicitTreeMR true)) 0 _ 0 8 (by decide) exitImplicitEmb (exitImplicitWorld (some 5))
    rfl rfl (hlenImp true) (treeSimInv_of_bool _ _ _ _ _ (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
    (by intro tp htp; simp only [List.mem_cons, List.not_mem_nil, or_false] at htp; rcases htp with rfl;
        exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro tp htp n hn; revert tp htp n hn; decide +kernel) (houtImp true)
  have h4errW : execFrameExitMiniRust (exitImplicitWorld (some 5)) [(1, 7)] =
      .error (.protectedForeignConflict 2) := rfl
  obtain ⟨msg4, hmsg4⟩ := h4err _ h4errW
  exact ⟨⟨w1, tbm1, alloc1, hw1, hend1, hal1, hinv1⟩,
    ⟨_, msg2, h2errW, hmsg2⟩,
    ⟨w3, tbm3, alloc3, hw3, hend3, hal3, hinv3⟩,
    ⟨_, msg4, h4errW, hmsg4⟩⟩

/-- Deep borrow-tree world for the arbitrary-depth `end_call` canary, all on
`[0, 8)`: root `0`; strongly protected accessed `.reservedFrz false` node `1`
(protector `7`) with child `2` and GRANDCHILD `3` (itself protected, protector
`9`); `.frozen` sibling `4` of `1` with its own `.frozen` child `5` (a NESTED
foreign subtree, pruned by Miri's `SkipSelfAndChildren` on a foreign read). -/
def deepExitWorld : FnEntryBorrowWorld where
  nodes := [
    ⟨5, some 4, .frozen, 0, 8, none, true⟩,
    ⟨4, some 0, .frozen, 0, 8, none, true⟩,
    ⟨3, some 2, .reservedFrz false, 0, 8, some 9, true⟩,
    ⟨2, some 1, .reservedFrz false, 0, 8, none, true⟩,
    ⟨1, some 0, .reservedFrz false, 0, 8, some 7, true⟩,
    ⟨0, none, .unique, 0, 8, none, true⟩
  ]
  activeProtectors := [7, 9]
  nextTag := 6
  nextProtector := 10

/-- Tag-to-path embedding of `deepExitWorld` (`0 ↦ []`, `1 ↦ [0]`, `2 ↦ [0, 0]`,
`3 ↦ [0, 0, 0]`, `4 ↦ [1]`, `5 ↦ [1, 0]`). -/
def deepExitEmb : Nat → Gen.Path
  | 0 => []
  | 1 => [0]
  | 2 => [0, 0]
  | 3 => [0, 0, 0]
  | 4 => [1]
  | 5 => [1, 0]
  | _ => [7]

/-- MiniRust borrow tree mirroring `deepExitWorld` (depth 3 below the root). -/
def deepExitTreeMR : Gen.Node :=
  ⟨[⟨[⟨[⟨[], List.replicate 8 (.Prot (.Reserved true false)), .Strong⟩],
        List.replicate 8 (.Unprot .Reserved), .No⟩],
      List.replicate 8 (.Prot (.Reserved true false)), .Strong⟩,
    ⟨[⟨[], List.replicate 8 (.Unprot .Frozen), .No⟩],
      List.replicate 8 (.Unprot .Frozen), .No⟩],
    List.replicate 8 (.Unprot .Unique), .No⟩

/-- **Closed non-vacuity canary for the arbitrary-depth `end_call` simulation**
(zero hypotheses): on `deepExitWorld` / `deepExitTreeMR` — a protected node with a
protected GRANDCHILD and a nested, Miri-pruned foreign subtree —
1. the shallow-tree predicate `NoNestedForeignAncestors` FAILS for both frame
   entries, so `tbm_end_call_simulates_execFrameExitMiniRust` does not apply;
2. `FrameExitPruneInert` holds (decided by `frameExitPruneInertBool`);
3. `tbm_end_call_simulates_execFrameExitMiniRust_of_pruneInert` fires on the
   two-entry frame `[(1, 7), (3, 9)]`: both `execFrameExitMiniRust` and the real
   `TreeBorrowsMemory.end_call` succeed, preserving `TreeSimInv` and `wfLive`. -/
theorem canary_endCall_arbitraryDepth_simulation :
    ¬ NoNestedForeignAncestors deepExitWorld.nodes 1 ∧
    ¬ NoNestedForeignAncestors deepExitWorld.nodes 3 ∧
    FrameExitPruneInert 0 8 deepExitWorld [(1, 7), (3, 9)] ∧
    (∃ w' tbm' alloc',
      execFrameExitMiniRust deepExitWorld [(1, 7), (3, 9)] = .ok w' ∧
      TreeBorrowsMemory.end_call (mkTbmWithTree deepExitTreeMR)
        ⟨[(⟨0⟩, [0]), (⟨0⟩, [0, 0, 0])]⟩ = .ok tbm' ∧
      tbm'.mem.allocations[0]? = some alloc' ∧
      TreeBorrowsMemory.wfLive tbm' ∧
      TreeSimInv 0 8 deepExitEmb w' alloc'.extra.root) := by
  have hprune : FrameExitPruneInert 0 8 deepExitWorld [(1, 7), (3, 9)] :=
    frameExitPruneInert_of_bool 0 8 _ _ (by decide +kernel)
  have hlen : ∀ q m, nodeAt deepExitTreeMR q = some m → m.permissions.length = 8 := by
    intro q m hm
    have hmem := nodeAt_mem_nodePaths deepExitTreeMR q m hm
    have hps : nodePaths deepExitTreeMR = [[], [0], [0, 0], [0, 0, 0], [1], [1, 0]] := rfl
    rw [hps] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> (cases hm; rfl)
  have hout : ∀ (tp : Nat × Nat) (_ : tp ∈ ([(1, 7), (3, 9)] : List (Nat × Nat))),
      ∀ m, nodeAt deepExitTreeMR (deepExitEmb tp.1) = some m → OutsideNoProtectorAccess 0 8 m := by
    intro tp _ m hm b p hp hb
    have hlt : b < m.permissions.length := (List.getElem?_eq_some_iff.mp hp).1
    have h8 := hlen _ m hm
    exfalso; omega
  obtain ⟨hok, _, _⟩ := tbm_end_call_simulates_execFrameExitMiniRust_of_pruneInert [(1, 7), (3, 9)]
    (mkTbmWithTree deepExitTreeMR) 0 _ 0 8 (by decide) deepExitEmb deepExitWorld
    rfl rfl hlen (treeSimInv_of_bool _ _ _ _ _ (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
    (by intro tp htp; simp only [List.mem_cons, List.not_mem_nil, or_false] at htp;
        rcases htp with rfl | rfl <;> exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hprune hout
  have hchk : (execFrameExitMiniRust deepExitWorld [(1, 7), (3, 9)]).isOk = true := by
    decide +kernel
  have hw : ∃ w', execFrameExitMiniRust deepExitWorld [(1, 7), (3, 9)] = .ok w' := by
    cases h : execFrameExitMiniRust deepExitWorld [(1, 7), (3, 9)] with
    | ok w' => exact ⟨w', rfl⟩
    | error _ => rw [h] at hchk; cases hchk
  obtain ⟨w1, hw1⟩ := hw
  obtain ⟨tbm1, alloc1, hend1, hal1, _, hwf1, hinv1⟩ := hok w1 hw1
  refine ⟨by unfold NoNestedForeignAncestors; decide +kernel,
    by unfold NoNestedForeignAncestors; decide +kernel, hprune,
    w1, tbm1, alloc1, hw1, hend1, hal1,
    hwf1 (tbm_wfLive_of_bool _ (by decide +kernel)), hinv1⟩

/-- **Closed non-vacuity canary for the pruning-inert whole-tree simulations**
(zero hypotheses): on the depth-3 tree `deepExitWorld` / `deepExitTreeMR`, a read
or `#[rustc_no_writable]` `FnEntry` retag through node `2` (`[0, 0]`) makes
Miri's `SkipSelfAndChildren` pruning ACTIVE — the `.frozen` sibling `4` skips its
subtree, so node `5` is pruned and the former "no node is pruned" hypothesis is
FALSE — yet pruning is inert (`foreignStepInert`), and
1. `tbm_load_simulates_execWorldRangeRead` fires: `execWorldRangeRead` and the real
   `TreeBorrowsMemory.load` both succeed into `TreeSimInv`-related states;
2. `tbm_retag_ptr_fnEntry_mutOrBox_simulates_world` fires: the Anneal retag and
   the real `TreeBorrowsMemory.retag_ptr` both succeed, minting the child
   `[0, 0, 1]` (tag `6`) at depth 3 with `TreeSimInv` preserved. -/
theorem canary_pruneInert_deepTree_load_and_retag :
    (¬ ∀ n ∈ deepExitWorld.nodes,
      isPrunedForeignNode deepExitWorld.nodes (ancestorPathTags deepExitWorld.nodes 2)
        false 0 8 n = false) ∧
    (∃ w' bytes tbm' alloc',
      execWorldRangeRead deepExitWorld 2 0 8 = .ok w' ∧
      TreeBorrowsMemory.load (mkTbmWithTree deepExitTreeMR) (tbmTreePtr [0, 0]) ⟨8⟩ ⟨4⟩ =
        .ok (bytes, tbm') ∧
      tbm'.mem.allocations[0]? = some alloc' ∧
      TreeSimInv 0 8 deepExitEmb w' alloc'.extra.root) ∧
    (∃ w' childTag tbm' alloc',
      execFnEntryMutRetagPrunedSourceOrder deepExitWorld 2 0 8 .rustcNoWritable false =
        .ok (w', childTag) ∧
      TreeBorrowsMemory.retag_ptr (mkTbmWithTree deepExitTreeMR) TreeBorrowsMemory.new_call
          (ThinPointer.widen (tbmTreePtr [0, 0]) .none)
          (ptrTypeOfParamKind .mutable (pointeeInfoOfFacts ⟨true, true, true⟩ 8 4 []))
          true false nwsrVtableLookup =
        .ok (ThinPointer.widen (tbmTreePtr [0, 0, 1]) .none, tbm', ⟨[(⟨0⟩, [0, 0, 1])]⟩) ∧
      tbm'.mem.allocations[0]? = some alloc' ∧
      TreeSimInv 0 8 (extendEmb deepExitEmb 6 [0, 0, 1]) w' alloc'.extra.root) := by
  have hinv : TreeSimInv 0 8 deepExitEmb deepExitWorld deepExitTreeMR :=
    treeSimInv_of_bool _ _ _ _ _ (by decide +kernel)
  have hloc : ∀ n ∈ deepExitWorld.nodes,
      (ancestorPathTags deepExitWorld.nodes 2).contains n.tag =
        locOf (some (deepExitEmb 2)) (deepExitEmb n.tag) := by decide +kernel
  -- 1. load
  obtain ⟨hloadOk, _, _⟩ := tbm_load_simulates_execWorldRangeRead
    (mkTbmWithTree deepExitTreeMR) (tbmTreePtr [0, 0]) 8 ⟨4⟩ 0 _ 0 deepExitEmb deepExitWorld 2
    rfl rfl rfl (by decide) (by decide) (by decide) (by decide) hinv ⟨_, rfl⟩ hloc
    (by decide +kernel)
  have hrdChk : (execWorldRangeRead deepExitWorld 2 0 8).isOk = true := by decide +kernel
  have hrdW : ∃ w', execWorldRangeRead deepExitWorld 2 0 8 = .ok w' := by
    cases h : execWorldRangeRead deepExitWorld 2 0 8 with
    | ok w' => exact ⟨w', rfl⟩
    | error _ => rw [h] at hrdChk; cases hrdChk
  obtain ⟨wR, hwR⟩ := hrdW
  obtain ⟨tbmR, allocR, hloadR, hallocR, _, hinvR⟩ := hloadOk wR hwR
  -- 2. retag
  obtain ⟨pNode, hpNode, hretOk, _, _⟩ := tbm_retag_ptr_fnEntry_mutOrBox_simulates_world
    (mkTbmWithTree deepExitTreeMR) TreeBorrowsMemory.new_call
    (ThinPointer.widen (tbmTreePtr [0, 0]) .none) nwsrVtableLookup
    ⟨true, true, true⟩ .mutable ⟨true, true⟩ (by decide) rfl rfl
    0 _ 0 8 4 (by decide) [] [true, true, true, true, true, true, true, true] rfl
    deepExitEmb deepExitWorld 2 false
    rfl rfl rfl (by decide) (by decide) hinv ⟨_, rfl⟩ (by decide +kernel) (by decide +kernel)
    hloc (by decide +kernel) (fun h => by cases h)
  have hpeq : pNode.children.length = 1 := by
    change nodeAt deepExitTreeMR [0, 0] = some pNode at hpNode
    have h0 : nodeAt deepExitTreeMR [0, 0] =
        some ⟨[⟨[], List.replicate 8 (.Prot (.Reserved true false)), .Strong⟩],
          List.replicate 8 (.Unprot .Reserved), .No⟩ := rfl
    rw [h0] at hpNode; cases hpNode; rfl
  have hrtChk : (execFnEntryMutRetagPrunedSourceOrder deepExitWorld 2 0 8
      .rustcNoWritable false).isOk = true := by decide +kernel
  have hrtW : ∃ res, execFnEntryMutRetagPrunedSourceOrder deepExitWorld 2 0 8
      .rustcNoWritable false = .ok res := by
    cases h : execFnEntryMutRetagPrunedSourceOrder deepExitWorld 2 0 8
        .rustcNoWritable false with
    | ok res => exact ⟨res, rfl⟩
    | error _ => rw [h] at hrtChk; cases hrtChk
  obtain ⟨⟨wT, cT⟩, hwT⟩ := hrtW
  obtain ⟨tbmT, allocT, hretT, hallocT, _, _, _, hinvT⟩ := hretOk wT cT hwT
  rw [hpeq] at hretT hinvT
  exact ⟨by decide +kernel,
    ⟨wR, _, tbmR, allocR, hwR, hloadR, hallocR, hinvR⟩,
    ⟨wT, cT, tbmT, allocT, hwT, hretT, hallocT, hinvT⟩⟩

/-- World witnessing that pruning-inertness cannot be dropped, all on `[0, 8)`:
root `0`; reader `1` (`.reservedFrz false`); `.frozen` sibling `2` with a
PROTECTED accessed `.reservedFrz false` child `3` (protector `9`). -/
def pruneSeparationWorld : FnEntryBorrowWorld where
  nodes := [
    ⟨3, some 2, .reservedFrz false, 0, 8, some 9, true⟩,
    ⟨2, some 0, .frozen, 0, 8, none, true⟩,
    ⟨1, some 0, .reservedFrz false, 0, 8, none, true⟩,
    ⟨0, none, .unique, 0, 8, none, true⟩
  ]
  activeProtectors := [9]
  nextTag := 4
  nextProtector := 10

/-- Tag-to-path embedding of `pruneSeparationWorld`
(`0 ↦ []`, `1 ↦ [0]`, `2 ↦ [1]`, `3 ↦ [1, 0]`). -/
def pruneSeparationEmb : Nat → Gen.Path
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [1, 0]
  | _ => [7]

/-- MiniRust borrow tree mirroring `pruneSeparationWorld`, with child `[1, 0]`
carrying `childPerm` on every byte. -/
def pruneSeparationTreeMR (childPerm : Gen.Permission) : Gen.Node :=
  ⟨[⟨[], List.replicate 8 (.Unprot .Reserved), .No⟩,
    ⟨[⟨[], List.replicate 8 childPerm, .Strong⟩], List.replicate 8 (.Unprot .Frozen), .No⟩],
    List.replicate 8 (.Unprot .Unique), .No⟩

/-- **Pruning-inertness is necessary (model separation)**: on
`pruneSeparationWorld` the two models start `TreeSimInv`-related, but a read
through node `1` makes pinned Miri prune the protected node `3` beneath the
`.frozen` sibling (leaving it `.reservedFrz false`) while MiniRust applies the
foreign read (`Reserved { had_foreign_read: true }`): the pruned step is NOT
inert (`foreignStepInert = false`), BOTH accesses succeed, and the resulting
states are NOT `TreeSimInv`-related. So the `hnoprune` hypothesis of the
whole-tree simulations cannot be weakened further. -/
theorem pruneInert_necessary_separation :
    TreeSimInv 0 8 pruneSeparationEmb pruneSeparationWorld
      (pruneSeparationTreeMR (.Prot (.Reserved true false))) ∧
    isPrunedForeignNode pruneSeparationWorld.nodes
      (ancestorPathTags pruneSeparationWorld.nodes 1) false 0 8
      ⟨3, some 2, .reservedFrz false, 0, 8, some 9, true⟩ = true ∧
    foreignStepInert pruneSeparationWorld.activeProtectors false 0 8
      ⟨3, some 2, .reservedFrz false, 0, 8, some 9, true⟩ = false ∧
    execWorldRangeRead pruneSeparationWorld 1 0 8 = .ok pruneSeparationWorld ∧
    Node.access (pruneSeparationTreeMR (.Prot (.Reserved true false))) (some [0]) .Read ⟨0⟩ ⟨8⟩ =
      .ok (pruneSeparationTreeMR (.Prot (.Reserved true true))) ∧
    ¬ TreeSimInv 0 8 pruneSeparationEmb pruneSeparationWorld
      (pruneSeparationTreeMR (.Prot (.Reserved true true))) := by
  refine ⟨treeSimInv_of_bool _ _ _ _ _ (by decide +kernel), by decide +kernel, by decide +kernel,
    rfl, rfl, fun h => ?_⟩
  obtain ⟨m, hm, _, p, hp, hwin⟩ :=
    h.nodes ⟨3, some 2, .reservedFrz false, 0, 8, some 9, true⟩ (by decide)
  have hmEq : m = ⟨[], List.replicate 8 (.Prot (.Reserved true true)), .Strong⟩ := by
    cases hm; rfl
  subst hmEq
  have hp' : some (Gen.Permission.Prot (.Reserved true false)) = some p := hp
  cases hp'
  have h0 := hwin 0 (by decide) (by decide)
  have e0 : (List.replicate 8 (Gen.Permission.Prot (.Reserved true true)))[0]? =
      some (.Prot (.Reserved true true)) := rfl
  rw [e0] at h0
  cases h0

/-- Borrow tree of the deallocation-boundary canary: root `[]` (`Unprot Unique`)
with a protected child `[0]` (`cPerm` on all 8 bytes, protector `cProt`) and an
unprotected sibling `[1]` (`Unprot Reserved`). -/
def deallocCanaryTree (cPerm : Gen.Permission) (cProt : Gen.Protected) : Gen.Node :=
  ⟨[⟨[], List.replicate 8 cPerm, cProt⟩, ⟨[], List.replicate 8 (.Unprot .Reserved), .No⟩],
    List.replicate 8 (.Unprot .Unique), .No⟩

/-- **Closed non-vacuity canary for the exact deallocation criterion**
(`tbm_deallocate_ok_iff_full`, `tbm_deallocate_precheck_ub`; zero hypotheses):
1. an active `Protected::Strong` node does NOT by itself block deallocation: with
   never-accessed bytes (`Reserved { had_local_read: false }`, e.g. a zero-sized
   `&mut ()` parameter) deallocating through the sibling SUCCEEDS, and with
   `Cell` bytes (`&UnsafeCell<T>`) deallocating through the protected pointer
   itself SUCCEEDS;
2. a locally read strongly protected `#[rustc_no_writable]` `&mut T`
   (`Reserved { had_local_read: true }`) blocks deallocation through BOTH the
   sibling and itself;
3. a `Box<T>` `Protected::Weak` in the same state deallocates through the `Box`
   but not through the sibling; a conflicted `Box<T>`
   (`Reserved { had_foreign_read: true }`) cannot deallocate itself, yet when it
   was never locally read the sibling CAN deallocate (silent foreign-write
   disable);
4. boundary pre-checks: wrong size, wrong kind, and a second `Box<T>` drop
   (`"double-free"`) are UB. -/
theorem canary_deallocate_exact_boundary :
    (∃ tbm', TreeBorrowsMemory.deallocate
        (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved false false)) .Strong))
        (tbmTreePtr [1]) .Stack ⟨8⟩ ⟨4⟩ = .ok tbm') ∧
    (∃ tbm', TreeBorrowsMemory.deallocate
        (mkTbmWithTree (deallocCanaryTree (.Prot .Cell) .Strong))
        (tbmTreePtr [0]) .Stack ⟨8⟩ ⟨4⟩ = .ok tbm') ∧
    (¬ ∃ tbm', TreeBorrowsMemory.deallocate
        (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved true false)) .Strong))
        (tbmTreePtr [1]) .Stack ⟨8⟩ ⟨4⟩ = .ok tbm') ∧
    (¬ ∃ tbm', TreeBorrowsMemory.deallocate
        (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved true false)) .Strong))
        (tbmTreePtr [0]) .Stack ⟨8⟩ ⟨4⟩ = .ok tbm') ∧
    (∃ tbm', TreeBorrowsMemory.deallocate
        (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved true false)) .Weak))
        (tbmTreePtr [0]) .Stack ⟨8⟩ ⟨4⟩ = .ok tbm') ∧
    (¬ ∃ tbm', TreeBorrowsMemory.deallocate
        (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved true false)) .Weak))
        (tbmTreePtr [1]) .Stack ⟨8⟩ ⟨4⟩ = .ok tbm') ∧
    (¬ ∃ tbm', TreeBorrowsMemory.deallocate
        (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved false true)) .Weak))
        (tbmTreePtr [0]) .Stack ⟨8⟩ ⟨4⟩ = .ok tbm') ∧
    (∃ tbm', TreeBorrowsMemory.deallocate
        (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved false true)) .Weak))
        (tbmTreePtr [1]) .Stack ⟨8⟩ ⟨4⟩ = .ok tbm') ∧
    TreeBorrowsMemory.deallocate
        (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved true false)) .Weak))
        (tbmTreePtr [0]) .Stack ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating with incorrect size information") ∧
    (∃ msg, TreeBorrowsMemory.deallocate
        (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved true false)) .Weak))
        (tbmTreePtr [0]) .Heap ⟨8⟩ ⟨4⟩ = .error (.ub msg)) ∧
    tbUnitOutcome
        (TreeBorrowsMemory.deallocate
            (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved true false)) .Weak))
            (tbmTreePtr [0]) .Stack ⟨8⟩ ⟨4⟩ >>= fun tbm' =>
          TreeBorrowsMemory.deallocate tbm' (tbmTreePtr [0]) .Stack ⟨8⟩ ⟨4⟩) =
      some (.inr "double-free") := by
  have key : ∀ (cPerm : Gen.Permission) (cProt : Gen.Protected) (path : Gen.Path),
      TreeBorrowsMemory.wfLive (mkTbmWithTree (deallocCanaryTree cPerm cProt)) →
      ((∃ tbm', TreeBorrowsMemory.deallocate (mkTbmWithTree (deallocCanaryTree cPerm cProt))
          (tbmTreePtr path) .Stack ⟨8⟩ ⟨4⟩ = .ok tbm') ↔
        deallocAllowedBool path (deallocCanaryTree cPerm cProt) = true) :=
    fun cPerm cProt path hwf =>
      (tbm_deallocate_ok_iff_full _ hwf (tbmTreePtr path) .Stack ⟨8⟩ ⟨4⟩ 0 path _ rfl rfl).trans
        ⟨fun h => h.2.2.2.2.2, fun h => ⟨rfl, rfl, rfl, rfl, rfl, h⟩⟩
  have hpre := (tbm_deallocate_precheck_ub
    (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved true false)) .Weak)) (tbmTreePtr [0])
    .Stack ⟨4⟩ ⟨4⟩).2 0 [0] _ rfl rfl
  have hpreK := (tbm_deallocate_precheck_ub
    (mkTbmWithTree (deallocCanaryTree (.Prot (.Reserved true false)) .Weak)) (tbmTreePtr [0])
    .Heap ⟨8⟩ ⟨4⟩).2 0 [0] _ rfl rfl
  exact ⟨(key _ _ _ (tbm_wfLive_of_bool _ (by decide +kernel))).mpr (by decide +kernel),
    (key _ _ _ (tbm_wfLive_of_bool _ (by decide +kernel))).mpr (by decide +kernel),
    fun h => absurd ((key _ _ _ (tbm_wfLive_of_bool _ (by decide +kernel))).mp h)
      (by decide +kernel),
    fun h => absurd ((key _ _ _ (tbm_wfLive_of_bool _ (by decide +kernel))).mp h)
      (by decide +kernel),
    (key _ _ _ (tbm_wfLive_of_bool _ (by decide +kernel))).mpr (by decide +kernel),
    fun h => absurd ((key _ _ _ (tbm_wfLive_of_bool _ (by decide +kernel))).mp h)
      (by decide +kernel),
    fun h => absurd ((key _ _ _ (tbm_wfLive_of_bool _ (by decide +kernel))).mp h)
      (by decide +kernel),
    (key _ _ _ (tbm_wfLive_of_bool _ (by decide +kernel))).mpr (by decide +kernel),
    hpre.2.2.2.1 rfl rfl rfl (by decide),
    hpreK.2.2.1 rfl rfl (by decide),
    by decide +kernel⟩

/-- **Closed non-vacuity canary for the frozen-reader laws** (zero hypotheses): on
the tree root `[]` + `.Frozen` reader `[0]` + `.Reserved` writer `[1]`,
1. a 1-byte write through `[1]` at byte `2` fires
   `node_access_foreign_write_kills_frozen_reader`: the reader's byte `2` becomes
   `.Unprot .Disabled` and its whole-slice read `[0, 8)` can no longer succeed;
2. a whole-slice READ through `[1]` fires
   `node_access_foreign_read_preserves_frozen_reader`: the reader's byte `2`
   stays `.Unprot .Frozen`. -/
theorem canary_frozen_reader_foreign_write_vs_read :
    let t : Gen.Node :=
      ⟨[⟨[], List.replicate 8 (.Unprot .Frozen), .No⟩,
        ⟨[], List.replicate 8 (.Unprot .Reserved), .No⟩],
        List.replicate 8 (.Unprot .Unique), .No⟩
    (∃ t' s', Node.access t (some [1]) .Write ⟨2⟩ ⟨1⟩ = .ok t' ∧
      nodeAt t' [0] = some s' ∧ s'.permissions[2]? = some (.Unprot .Disabled) ∧
      ∀ t'', Node.access t' (some [0]) .Read ⟨0⟩ ⟨8⟩ ≠ .ok t'') ∧
    (∃ t' s', Node.access t (some [1]) .Read ⟨0⟩ ⟨8⟩ = .ok t' ∧
      nodeAt t' [0] = some s' ∧ s'.permissions[2]? = some (.Unprot .Frozen)) := by
  dsimp only
  have haccW : Node.access
      ⟨[⟨[], List.replicate 8 (.Unprot .Frozen), .No⟩,
        ⟨[], List.replicate 8 (.Unprot .Reserved), .No⟩],
        List.replicate 8 (.Unprot .Unique), .No⟩ (some [1]) .Write ⟨2⟩ ⟨1⟩ =
      .ok ⟨[⟨[], [.Unprot .Frozen, .Unprot .Frozen, .Unprot .Disabled, .Unprot .Frozen,
            .Unprot .Frozen, .Unprot .Frozen, .Unprot .Frozen, .Unprot .Frozen], .No⟩,
          ⟨[], [.Unprot .Reserved, .Unprot .Reserved, .Unprot .Unique, .Unprot .Reserved,
            .Unprot .Reserved, .Unprot .Reserved, .Unprot .Reserved, .Unprot .Reserved], .No⟩],
        List.replicate 8 (.Unprot .Unique), .No⟩ := rfl
  have haccR : Node.access
      ⟨[⟨[], List.replicate 8 (.Unprot .Frozen), .No⟩,
        ⟨[], List.replicate 8 (.Unprot .Reserved), .No⟩],
        List.replicate 8 (.Unprot .Unique), .No⟩ (some [1]) .Read ⟨0⟩ ⟨8⟩ =
      .ok ⟨[⟨[], List.replicate 8 (.Unprot .Frozen), .No⟩,
        ⟨[], List.replicate 8 (.Unprot .Reserved), .No⟩],
        List.replicate 8 (.Unprot .Unique), .No⟩ := rfl
  obtain ⟨⟨s', hs', hp'⟩, hdead⟩ := node_access_foreign_write_kills_frozen_reader _ _ [1] [0] _
    2 1 2 haccW rfl rfl (by decide) (by decide) rfl
  obtain ⟨s2, hs2, hp2⟩ := node_access_foreign_read_preserves_frozen_reader _ _ [1] [0] _
    0 8 2 haccR rfl rfl rfl
  exact ⟨⟨_, s', haccW, hs', hp', hdead 0 8 (by decide) (by decide)⟩, ⟨_, s2, haccR, hs2, hp2⟩⟩

/-- **Closed non-vacuity canary for
`tbm_retag_ptr_fnEntry_frozen_reader_noWritable_vs_writable`** (zero hypotheses):
on the tree root `[]` + parent `[0]` + `.Frozen` reader `[1]` over an 8-byte
allocation, the real `TreeBorrowsMemory.retag_ptr` of a `&mut` through `[0]`
1. with the `FnEntry` implicit write leaves the reader `.Unprot .Disabled` on
   byte `3` and makes its whole-slice `TreeBorrowsMemory.load` fail;
2. under `#[rustc_no_writable]` leaves the reader `.Unprot .Frozen` on byte `3`. -/
theorem canary_retag_frozen_reader_noWritable_vs_writable :
    let t : Gen.Node :=
      ⟨[⟨[], List.replicate 8 (.Unprot .Reserved), .No⟩,
        ⟨[], List.replicate 8 (.Unprot .Frozen), .No⟩],
        List.replicate 8 (.Unprot .Unique), .No⟩
    let ptrTy := ptrTypeOfParamKind .mutable (pointeeInfoOfFacts ⟨true, true, true⟩ 8 4 [])
    (∃ r root' s',
      TreeBorrowsMemory.retag_ptr (mkTbmWithTree t) TreeBorrowsMemory.new_call
        (ThinPointer.widen (tbmTreePtr [0]) .none) ptrTy true true nwsrVtableLookup = .ok r ∧
      nodeAt root' [1] = some s' ∧ s'.permissions[3]? = some (.Unprot .Disabled) ∧
      ∀ res, TreeBorrowsMemory.load r.2.1 (tbmTreePtr [1]) ⟨8⟩ ⟨4⟩ ≠ .ok res) ∧
    (∃ r root' s',
      TreeBorrowsMemory.retag_ptr (mkTbmWithTree t) TreeBorrowsMemory.new_call
        (ThinPointer.widen (tbmTreePtr [0]) .none) ptrTy true false nwsrVtableLookup = .ok r ∧
      nodeAt root' [1] = some s' ∧ s'.permissions[3]? = some (.Unprot .Frozen)) := by
  intro t ptrTy
  have hchkW : (TreeBorrowsMemory.retag_ptr (mkTbmWithTree t) TreeBorrowsMemory.new_call
      (ThinPointer.widen (tbmTreePtr [0]) .none) ptrTy true true nwsrVtableLookup).isOk = true := by
    decide +kernel
  have hchkN : (TreeBorrowsMemory.retag_ptr (mkTbmWithTree t) TreeBorrowsMemory.new_call
      (ThinPointer.widen (tbmTreePtr [0]) .none) ptrTy true false nwsrVtableLookup).isOk = true := by
    decide +kernel
  constructor
  · cases hr : TreeBorrowsMemory.retag_ptr (mkTbmWithTree t) TreeBorrowsMemory.new_call
        (ThinPointer.widen (tbmTreePtr [0]) .none) ptrTy true true nwsrVtableLookup with
    | error e => rw [hr] at hchkW; cases hchkW
    | ok r =>
      obtain ⟨hW, _⟩ := tbm_retag_ptr_fnEntry_frozen_reader_noWritable_vs_writable
        (mkTbmWithTree t) TreeBorrowsMemory.new_call (ThinPointer.widen (tbmTreePtr [0]) .none)
        nwsrVtableLookup ⟨true, true, true⟩ .mutable ⟨true, false⟩ (by decide) rfl
        0 [0] _ _ 0 8 4 [] [true, true, true, true, true, true, true, true] rfl
        rfl rfl rfl (by decide) (by decide) rfl [1] _ rfl rfl 3 (by decide) (by decide) rfl r hr
      obtain ⟨root', s', _, hs', hpb, _, hload⟩ := hW rfl
      exact ⟨r, root', s', rfl, hs', hpb, fun res =>
        hload (tbmTreePtr [1]) 0 8 ⟨4⟩ rfl (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) res⟩
  · cases hr : TreeBorrowsMemory.retag_ptr (mkTbmWithTree t) TreeBorrowsMemory.new_call
        (ThinPointer.widen (tbmTreePtr [0]) .none) ptrTy true false nwsrVtableLookup with
    | error e => rw [hr] at hchkN; cases hchkN
    | ok r =>
      obtain ⟨_, hN⟩ := tbm_retag_ptr_fnEntry_frozen_reader_noWritable_vs_writable
        (mkTbmWithTree t) TreeBorrowsMemory.new_call (ThinPointer.widen (tbmTreePtr [0]) .none)
        nwsrVtableLookup ⟨true, true, true⟩ .mutable ⟨true, true⟩ (by decide) rfl
        0 [0] _ _ 0 8 4 [] [true, true, true, true, true, true, true, true] rfl
        rfl rfl rfl (by decide) (by decide) rfl [1] _ rfl rfl 3 (by decide) (by decide) rfl r hr
      obtain ⟨root', s', _, hs', hpb⟩ := hN rfl
      exact ⟨r, root', s', rfl, hs', hpb⟩

/-- MiniRust borrow tree matching `disjointTwoParamWorld` on `[0, 4)` and `[4, 8)`. -/
def disjointTwoParamTreeMR : Gen.Node :=
  ⟨[⟨[], List.replicate 4 (.Prot .Unique) ++ List.replicate 4 (.Prot (.Reserved false false)), .Strong⟩,
    ⟨[], List.replicate 4 (.Unprot .Frozen) ++ List.replicate 4 (.Unprot .Reserved), .No⟩,
    ⟨[], List.replicate 4 (.Prot (.Reserved false false)) ++ List.replicate 4 (.Prot (.Reserved true false)), .Strong⟩,
    ⟨[], List.replicate 4 (.Unprot .Reserved) ++ List.replicate 4 (.Unprot .Frozen), .No⟩],
   List.replicate 8 (.Unprot .Unique), .No⟩

/-- Tag-to-path embedding for `disjointTwoParamWorld` ↔ `disjointTwoParamTreeMR`. -/
def disjointTwoParamEmb : Nat → Gen.Path
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | 4 => [3]
  | _ => [99]

/-- **Closed non-vacuity canary for `TreeSimInvMulti` vs. `B1`'s `TreeSimInv` on
disjoint sub-slices (`disjointTwoParamWorld` ↔ `disjointTwoParamTreeMR`)**:
1. Proves `B1`'s `TreeSimInv` is **UNSATISFIABLE** on ALL three windows
   `[0, 4)`, `[4, 8)`, and `[0, 8)` (`¬ TreeSimInv 0 4 ...`, `¬ TreeSimInv 4 4 ...`,
   `¬ TreeSimInv 0 8 ...`);
2. Proves `TreeSimInvMulti 0 4` AND `TreeSimInvMulti 4 4` **BOTH HOLD
   SIMULTANEOUSLY** on the very same borrow tree;
3. Fires `tbm_store_simulates_execWorldRangeWrite_multi` on `[0, 4)` (writing
   through tag `1`, disabling half-0 sibling `2`), preserves BOTH
   `TreeSimInvMulti 0 4` AND `TreeSimInvMulti 4 4` (via
   `treeSimInvMulti_preserved_on_disjoint_window`), and then fires
   `tbm_load_simulates_execWorldRangeRead_multi` on `[4, 8)` (succeeding through
   half-1 sibling `4`) and on `[0, 4)` (raising UB through half-0 sibling `2`)! -/
theorem canary_treeSimInvMulti_disjoint_slices :
    ¬ TreeSimInv 0 4 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR ∧
    ¬ TreeSimInv 4 4 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR ∧
    ¬ TreeSimInv 0 8 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR ∧
    TreeSimInvMulti 0 4 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR ∧
    TreeSimInvMulti 4 4 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR ∧
    (∃ w1 tbm1 alloc1 w2 tbm2 alloc2 msg,
      execWorldRangeWrite disjointTwoParamWorld 1 0 4 = .ok w1 ∧
      TreeBorrowsMemory.store (mkTbmWithTree disjointTwoParamTreeMR)
        (tbmTreePtr [0]) (tbU32Bytes 55) ⟨4⟩ = .ok tbm1 ∧
      tbm1.mem.allocations[0]? = some alloc1 ∧
      TreeSimInvMulti 0 4 disjointTwoParamEmb w1 alloc1.extra.root ∧
      TreeSimInvMulti 4 4 disjointTwoParamEmb w1 alloc1.extra.root ∧
      execWorldRangeRead w1 4 4 4 = .ok w2 ∧
      TreeBorrowsMemory.load tbm1
        { addr := 256 + ((4 : Nat) : Int), provenance := some (⟨0⟩, [3]) } ⟨4⟩ ⟨4⟩ =
        .ok ((alloc1.data.drop 4).take 4, tbm2) ∧
      tbm2.mem.allocations[0]? = some alloc2 ∧
      TreeSimInvMulti 4 4 disjointTwoParamEmb w2 alloc2.extra.root ∧
      TreeBorrowsMemory.load tbm2 (tbmTreePtr [1]) ⟨4⟩ ⟨4⟩ = .error (.ub msg)) := by
  have hnot04 : ¬ TreeSimInv 0 4 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR := by
    intro h
    have hov := h.overlap ⟨3, some 0, .reservedFrz false, 4, 4, some 11, true⟩ (by decide)
    cases hov
  have hnot44 : ¬ TreeSimInv 4 4 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR := by
    intro h
    have hov := h.overlap ⟨1, some 0, .unique, 0, 4, some 10, true⟩ (by decide)
    cases hov
  have hnot08 : ¬ TreeSimInv 0 8 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR := by
    intro h
    obtain ⟨m, hm, _, p, _, hwin⟩ := h.nodes ⟨1, some 0, .unique, 0, 4, some 10, true⟩ (by decide)
    have hmEq : m = ⟨[], List.replicate 4 (.Prot .Unique) ++
        List.replicate 4 (.Prot (.Reserved false false)), .Strong⟩ := by
      cases hm; rfl
    subst hmEq
    have h0 := hwin 0 (by decide) (by decide)
    have h4 := hwin 4 (by decide) (by decide)
    have e0 : (List.replicate 4 (Gen.Permission.Prot .Unique) ++
        List.replicate 4 (Gen.Permission.Prot (.Reserved false false)))[0]? =
        some (.Prot .Unique) := rfl
    have e4 : (List.replicate 4 (Gen.Permission.Prot .Unique) ++
        List.replicate 4 (Gen.Permission.Prot (.Reserved false false)))[4]? =
        some (.Prot (.Reserved false false)) := rfl
    rw [e0] at h0; rw [e4] at h4
    cases h0; cases h4
  have hinv04 : TreeSimInvMulti 0 4 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR :=
    treeSimInvMulti_of_bool 0 4 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR
      (by decide +kernel)
  have hinv44 : TreeSimInvMulti 4 4 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR :=
    treeSimInvMulti_of_bool 4 4 disjointTwoParamEmb disjointTwoParamWorld disjointTwoParamTreeMR
      (by decide +kernel)
  refine ⟨hnot04, hnot44, hnot08, hinv04, hinv44, ?_⟩
  -- Execute write on [0, 4) through tag 1
  let w1 : FnEntryBorrowWorld :=
    { nodes := [
        ⟨0, none, .unique, 0, 8, none, true⟩,
        ⟨1, some 0, .unique, 0, 4, some 10, true⟩,
        ⟨2, some 0, .disabled, 0, 4, none, true⟩,
        ⟨3, some 0, .reservedFrz false, 4, 4, some 11, true⟩,
        ⟨4, some 0, .frozen, 4, 4, none, true⟩],
      activeProtectors := [10, 11], nextTag := 5, nextProtector := 12 }
  have hw1 : execWorldRangeWrite disjointTwoParamWorld 1 0 4 = .ok w1 := rfl
  have hstSim := tbm_store_simulates_execWorldRangeWrite_multi
    (mkTbmWithTree disjointTwoParamTreeMR) (tbmTreePtr [0]) (tbU32Bytes 55) ⟨4⟩ 0 _ 0
    disjointTwoParamEmb disjointTwoParamWorld 1 rfl rfl rfl rfl (by decide) (by decide)
    (by decide) hinv04 rfl ⟨_, rfl⟩
    (fun n hn => by
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      cases hn)
    (fun n hn hanc => by
      rcases List.mem_cons.mp hn with rfl | hn; · rfl
      rcases List.mem_cons.mp hn with rfl | hn; · rfl
      rcases List.mem_cons.mp hn with rfl | hn; · cases hanc
      rcases List.mem_cons.mp hn with rfl | hn; · cases hanc
      rcases List.mem_cons.mp hn with rfl | hn; · cases hanc
      cases hn)
    (fun n hn => by
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      cases hn)
  obtain ⟨tbm1, alloc1, htbm1, ha1, hlive1, hinv1_04⟩ := hstSim.1 w1 hw1
  -- Extract Node.access witness and allocation metadata from htbm1
  have hst1Info : Node.access disjointTwoParamTreeMR (some [0]) .Write ⟨0⟩ ⟨4⟩ =
      .ok alloc1.extra.root ∧ alloc1.addr = 256 ∧ alloc1.data.length = 8 := by
    have heq := tbm_store_eq_node_access (mkTbmWithTree disjointTwoParamTreeMR)
      (tbmTreePtr [0]) (tbU32Bytes 55) ⟨4⟩ 0 [0] _ 0 rfl rfl rfl rfl (by decide)
      (by decide) (by decide)
    rw [heq] at htbm1
    obtain ⟨r1, hacc, htbm1Eq⟩ := nwsr_bind_ok htbm1
    cases htbm1Eq
    have ha1Eq : alloc1 = {
        (mkRootAllocTB (tbU32Bytes 1 ++ tbU32Bytes 2) 256 4 .Stack) with
        data := (tbU32Bytes 1 ++ tbU32Bytes 2).take 0 ++ tbU32Bytes 55 ++
          (tbU32Bytes 1 ++ tbU32Bytes 2).drop (0 + (tbU32Bytes 55).length),
        extra := { root := r1 } } := by
      cases ha1; rfl
    rw [ha1Eq]
    exact ⟨hacc, rfl, rfl⟩
  have hinv1_44 : TreeSimInvMulti 4 4 disjointTwoParamEmb w1 alloc1.extra.root :=
    treeSimInvMulti_preserved_on_disjoint_window 0 4 4 4 (Or.inl (Nat.le_refl 4))
      disjointTwoParamEmb disjointTwoParamWorld w1 disjointTwoParamTreeMR alloc1.extra.root
      (some [0]) .Write hinv44 hst1Info.1 hinv1_04 rfl (fun n' hn' => by
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨⟨0, none, .unique, 0, 8, none, true⟩, by decide, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨⟨1, some 0, .unique, 0, 4, some 10, true⟩, by decide, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨⟨2, some 0, .frozen, 0, 4, none, true⟩, by decide, rfl, rfl, rfl, rfl, fun h => by cases h⟩
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨⟨3, some 0, .reservedFrz false, 4, 4, some 11, true⟩, by decide, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨⟨4, some 0, .frozen, 4, 4, none, true⟩, by decide, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
        cases hn')
  -- Execute read on [4, 8) through tag 4 (latches conflicted on protected tag 3!)
  let w2 : FnEntryBorrowWorld :=
    { nodes := [
        ⟨0, none, .unique, 0, 8, none, true⟩,
        ⟨1, some 0, .unique, 0, 4, some 10, true⟩,
        ⟨2, some 0, .disabled, 0, 4, none, true⟩,
        ⟨3, some 0, .reservedFrz true, 4, 4, some 11, true⟩,
        ⟨4, some 0, .frozen, 4, 4, none, true⟩],
      activeProtectors := [10, 11], nextTag := 5, nextProtector := 12 }
  have hw2 : execWorldRangeRead w1 4 4 4 = .ok w2 := rfl
  have hldSim := tbm_load_simulates_execWorldRangeRead_multi tbm1
    { addr := 256 + ((4 : Nat) : Int), provenance := some (⟨0⟩, [3]) } 4 ⟨4⟩ 0 alloc1 4
    disjointTwoParamEmb w1 4 rfl ha1 hlive1 (by decide)
    (by show 256 + ((4 : Nat) : Int) - alloc1.addr = ((4 : Nat) : Int); rw [hst1Info.2.1]; omega)
    (by decide) (by rw [hst1Info.2.2]; decide) hinv1_44 ⟨_, rfl⟩
    (fun n hn => by
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      cases hn)
    (fun n hn hanc => by
      rcases List.mem_cons.mp hn with rfl | hn; · rfl
      rcases List.mem_cons.mp hn with rfl | hn; · cases hanc
      rcases List.mem_cons.mp hn with rfl | hn; · cases hanc
      rcases List.mem_cons.mp hn with rfl | hn; · cases hanc
      rcases List.mem_cons.mp hn with rfl | hn; · rfl
      cases hn)
    (fun n hn => by
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      cases hn)
  obtain ⟨tbm2, alloc2, htbm2, ha2, hlive2, hinv2_44⟩ := hldSim.1 w2 hw2
  -- Preserve TreeSimInvMulti 0 4 across the [4, 8) read, then trigger UB reading disabled tag 2!
  have hld2Info : Node.access alloc1.extra.root (some [3]) .Read ⟨4⟩ ⟨4⟩ = .ok alloc2.extra.root ∧
      alloc2.addr = 256 ∧ alloc2.data.length = 8 := by
    have heq := tbm_load_eq_node_access tbm1
      { addr := 256 + ((4 : Nat) : Int), provenance := some (⟨0⟩, [3]) } 4 ⟨4⟩ 0 [3] alloc1 4
      rfl ha1 hlive1 (by decide)
      (by show 256 + ((4 : Nat) : Int) - alloc1.addr = ((4 : Nat) : Int); rw [hst1Info.2.1]; omega)
      (by decide) (by rw [hst1Info.2.2]; decide)
    rw [heq] at htbm2
    obtain ⟨r2, hacc, htbm2Eq⟩ := nwsr_bind_ok htbm2
    cases htbm2Eq
    have hlen1 : 0 < tbm1.mem.allocations.length := (List.getElem?_eq_some_iff.mp ha1).1
    rw [List.getElem?_set_self hlen1] at ha2
    have ha2Eq : alloc2 = { alloc1 with extra := { root := r2 } } := by cases ha2; rfl
    rw [ha2Eq]
    exact ⟨hacc, hst1Info.2.1, hst1Info.2.2⟩
  have hinv2_04 : TreeSimInvMulti 0 4 disjointTwoParamEmb w2 alloc2.extra.root :=
    treeSimInvMulti_preserved_on_disjoint_window 4 4 0 4 (Or.inr (Nat.le_refl 4))
      disjointTwoParamEmb w1 w2 alloc1.extra.root alloc2.extra.root (some [3]) .Read
      hinv1_04 hld2Info.1 hinv2_44 rfl (fun n' hn' => by
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨⟨0, none, .unique, 0, 8, none, true⟩, by decide, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨⟨1, some 0, .unique, 0, 4, some 10, true⟩, by decide, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨⟨2, some 0, .disabled, 0, 4, none, true⟩, by decide, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨⟨3, some 0, .reservedFrz false, 4, 4, some 11, true⟩, by decide, rfl, rfl, rfl, rfl, fun h => by cases h⟩
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨⟨4, some 0, .frozen, 4, 4, none, true⟩, by decide, rfl, rfl, rfl, rfl, fun h => by cases h⟩
        cases hn')
  have hldErrSim := tbm_load_simulates_execWorldRangeRead_multi tbm2 (tbmTreePtr [1]) 4 ⟨4⟩
    0 alloc2 0 disjointTwoParamEmb w2 2 rfl ha2 hlive2 rfl
    (by show (256 : Int) - alloc2.addr = ((0 : Nat) : Int); rw [hld2Info.2.1]; rfl)
    (by decide) (by rw [hld2Info.2.2]; decide) hinv2_04 ⟨_, rfl⟩
    (fun n hn => by
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      cases hn)
    (fun n hn hanc => by
      rcases List.mem_cons.mp hn with rfl | hn; · rfl
      rcases List.mem_cons.mp hn with rfl | hn; · cases hanc
      rcases List.mem_cons.mp hn with rfl | hn; · rfl
      rcases List.mem_cons.mp hn with rfl | hn; · cases hanc
      rcases List.mem_cons.mp hn with rfl | hn; · cases hanc
      cases hn)
    (fun n hn => by
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      rcases List.mem_cons.mp hn with rfl | hn; · decide
      cases hn)
  obtain ⟨msg, hmsg⟩ := hldErrSim.2.1 (.disabledParentTag 2) rfl
  exact ⟨w1, tbm1, alloc1, w2, tbm2, alloc2, msg, hw1, htbm1, ha1, hinv1_04, hinv1_44,
    hw2, htbm2, ha2, hinv2_44, hmsg⟩

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

/-! ### 6.4 Full-Domain Static Retag (`StaticCellsValid` ↔ `StaticTyDesc`) & Choice-Free Symbolic `MachTB.wfLive` Preservation -/

/-! #### 6.4.1 Syntactic Freeze & Full-Domain Static Store (`wLen = 0`, OOB, `.not` vs `.mut`, Alignment) -/

mutual

/-- A syntactically `Freeze` `StaticTyDesc` contains zero non-zero-length
`UnsafeCell` intervals at every base offset. -/
theorem collectNonZeroUnsafeCells_nil_of_isSyntacticFreeze :
    ∀ (base : Nat) (d : StaticTyDesc),
      d.isSyntacticFreeze = true → collectNonZeroUnsafeCells base d = []
  | _, .freezeScalar _, _ => rfl
  | _, .padding _, _ => rfl
  | _, .unsafeCell _, h => by cases h
  | base, .composite _ fields, h =>
    collectFieldsNonZeroUnsafeCells_nil_of_fieldsSyntacticFreeze base fields h

/-- Field-list companion of `collectNonZeroUnsafeCells_nil_of_isSyntacticFreeze`. -/
theorem collectFieldsNonZeroUnsafeCells_nil_of_fieldsSyntacticFreeze :
    ∀ (base : Nat) (fs : List (Nat × StaticTyDesc)),
      fieldsSyntacticFreeze fs = true → collectFieldsNonZeroUnsafeCells base fs = []
  | _, [], _ => rfl
  | base, (off, d) :: rest, h => by
    unfold fieldsSyntacticFreeze at h
    have ⟨hd, hrest⟩ := Bool.and_eq_true_iff.mp h
    unfold collectFieldsNonZeroUnsafeCells
    rw [collectNonZeroUnsafeCells_nil_of_isSyntacticFreeze (base + off) d hd,
      collectFieldsNonZeroUnsafeCells_nil_of_fieldsSyntacticFreeze base rest hrest]
    rfl

end

/-- On any syntactically `Freeze` static descriptor, `byteInNonZeroUnsafeCell`
is `false` at every byte offset `b`. -/
theorem byteInNonZeroUnsafeCell_false_of_isSyntacticFreeze (desc : StaticTyDesc)
    (hfrz : desc.isSyntacticFreeze = true) (b : Nat) :
    byteInNonZeroUnsafeCell desc b = false := by
  unfold byteInNonZeroUnsafeCell
  rw [collectNonZeroUnsafeCells_nil_of_isSyntacticFreeze 0 desc hfrz]
  rfl

/-- **Zero-length store edge case (`wBytes = []`) on real `TreeBorrowsMemory.store`**:
every aligned zero-byte store succeeds unconditionally on ANY `TreeBorrowsMemory`
and ANY pointer (even out-of-bounds, even without provenance, even on `Frozen`
bytes), returning the memory state unchanged — matching `BasicMemory.check_ptr ... ⟨0⟩ = .ok none`
and `static_zstWrite_always_ok`. -/
theorem tbm_store_zeroLen_always_ok (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (align : LibSpecr.Align)
    (haligned : Align.is_aligned align ptr.addr = true) :
    TreeBorrowsMemory.store tbm ptr [] align = .ok tbm := by
  unfold TreeBorrowsMemory.store BasicMemory.store BasicMemory.check_ptr
  simp only [haligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_nil,
    bind, Except.bind, pure, Except.pure]

/-- **Out-of-bounds non-zero static store rejection on real `TreeBorrowsMemory.store`**:
on any single-allocation global `TreeBorrowsMemory` (covering both `staticTbm`
and `staticTbmRetagged`), any aligned non-empty store whose window
`[wOff, wOff + wBytes.length)` exceeds `data.length` fails at `BasicMemory.check_ptr`
with exact `.error (.ub "dereferencing pointer outside the bounds of its allocation")`
before Tree Borrows transitions run. -/
theorem tbm_static_store_outOfBounds
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (addr : Int) (align : Nat)
    (ex : Gen.TreeBorrowsAllocationExtra) (path : Gen.Path)
    (wOff : Nat) (wBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (wAlign : Nat)
    (hwlen : wBytes.length ≠ 0) (hoob : wOff + wBytes.length > data.length)
    (haligned : Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) = true) :
    let tbm : Gen.TreeBorrowsMemory Gen.x86_64 :=
      { params := ⟨true⟩
        mem := { allocations := [{ mkRootAllocTB data addr align .Global with extra := ex }],
                 _phantom := ⟨⟩ } }
    TreeBorrowsMemory.store tbm
        { addr := addr + (wOff : Int), provenance := some (⟨0⟩, path) } wBytes ⟨wAlign⟩ =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") := by
  dsimp only
  unfold TreeBorrowsMemory.store BasicMemory.store BasicMemory.check_ptr listIndex
  have hnn : (0 : Int) ≤ (0 : Int) := Int.le_refl _
  have hsub : addr + (wOff : Int) - addr = (wOff : Int) := by omega
  have hcond : (wOff : Int) < 0 ∨ (wOff : Int) + (wBytes.length : Int) > (data.length : Int) :=
    Or.inr (by omega)
  simp only [haligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hwlen, hnn,
    Int.toNat_zero, List.getElem?_cons_zero, mkRootAllocTB, hsub, Allocation.size, hcond,
    bind, Except.bind, pure, Except.pure, ub]

/-- Exact Anneal-side outcome classification for out-of-bounds non-zero static
writes (`wLen ≠ 0`, `wOff + wLen > desc.totalByteSize`) across both
`evalRawMutStaticWriteTB` (`.outOfBounds`) and `evalRawMutStaticWriteMiri`
(`.outOfBounds` on `.mut`, `.readOnlyAlloc` on `.not` since Miri's read-only
allocation check precedes bounds checking). -/
theorem evalRawMutStaticWrite_outOfBounds_exact (desc : StaticTyDesc)
    (rootTag tmpTag wOff wLen : Nat) (hwlen : wLen ≠ 0) (hoob : wOff + wLen > desc.totalByteSize) :
    evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag) wOff wLen = .outOfBounds ∧
    evalRawMutStaticWriteTB (retagStaticErasedAt desc rootTag) wOff wLen = .outOfBounds ∧
    (staticAllocMutability desc = .mut →
      evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag) wOff wLen =
        .outOfBounds ∧
      evalRawMutStaticWriteMiri desc (retagStaticErasedAt desc rootTag) wOff wLen =
        .outOfBounds) ∧
    (staticAllocMutability desc = .not →
      evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag) wOff wLen =
        .readOnlyAlloc ∧
      evalRawMutStaticWriteMiri desc (retagStaticErasedAt desc rootTag) wOff wLen =
        .readOnlyAlloc) := by
  have hlenF : (wLen == 0) = false := by
    cases wLen with
    | zero => exact absurd rfl hwlen
    | succ _ => rfl
  have hpresTB : evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag) wOff wLen =
      .outOfBounds := by
    unfold evalRawMutStaticWriteTB
    change (if (wLen == 0) = true then StaticWriteOutcome.ok
      else if wOff + wLen > desc.totalByteSize then .outOfBounds else _) = .outOfBounds
    simp only [hlenF, Bool.false_eq_true, ↓reduceIte, hoob]
  have herasTB : evalRawMutStaticWriteTB (retagStaticErasedAt desc rootTag) wOff wLen =
      .outOfBounds := by
    unfold evalRawMutStaticWriteTB
    change (if (wLen == 0) = true then StaticWriteOutcome.ok
      else if wOff + wLen > desc.totalByteSize then .outOfBounds else _) = .outOfBounds
    simp only [hlenF, Bool.false_eq_true, ↓reduceIte, hoob]
  refine ⟨hpresTB, herasTB, ?_, ?_⟩
  · intro hmut
    have hmutF : (staticAllocMutability desc == .not) = false := by rw [hmut]; rfl
    constructor <;> (
      unfold evalRawMutStaticWriteMiri
      change (if (wLen == 0) = true then StaticWriteOutcome.ok
        else if (staticAllocMutability desc == .not) = true then .readOnlyAlloc
        else if wOff + wLen > desc.totalByteSize then .outOfBounds else _) = .outOfBounds
      simp only [hlenF, hmutF, Bool.false_eq_true, ↓reduceIte, hoob])
  · intro hnot
    have hnotT : (staticAllocMutability desc == .not) = true := by rw [hnot]; rfl
    constructor <;> (
      unfold evalRawMutStaticWriteMiri
      simp only [hlenF, hnotT, Bool.false_eq_true, ↓reduceIte])

private theorem d1_evalRawMutStaticWriteTB_preserved_ub_of_freezeByte
    (desc : StaticTyDesc) (rootTag tmpTag wOff wLen : Nat)
    (hwlen : wLen ≠ 0) (hin : wOff + wLen ≤ desc.totalByteSize)
    (hbad : ∃ b, wOff ≤ b ∧ b < wOff + wLen ∧ byteInNonZeroUnsafeCell desc b = false) :
    evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag) wOff wLen = .ub := by
  obtain ⟨b, h1, h2, hb⟩ := hbad
  have htot : (retagStaticPreservedAt desc rootTag tmpTag).totalSize = desc.totalByteSize := rfl
  obtain ⟨s, hs, hkind, hs1, hs2⟩ :=
    (staticFreezeSegments_freeze_byte_iff desc b (by omega)).mpr hb
  have hov : rangesOverlap wOff wLen s.offset s.len = true :=
    (rangesOverlap_iff_exists_byte wOff wLen s.offset s.len).mpr ⟨b, h1, h2, hs1, hs2⟩
  exact (evalRawMutStaticWriteTB_ub_iff (retagStaticPreservedAt desc rootTag tmpTag) wOff wLen
    (by rw [htot]; exact hin) hwlen).1.mpr
    ⟨(s, .frozen),
      List.mem_map.mpr ⟨s, hs, by simp only [hkind]⟩,
      hov, Or.inl rfl⟩

private theorem d1_evalRawMutStaticWriteTB_erased_ok_iff
    (desc : StaticTyDesc) (rootTag wOff wLen : Nat) :
    evalRawMutStaticWriteTB (retagStaticErasedAt desc rootTag) wOff wLen = .ok ↔
      (wLen = 0 ∨ wOff + wLen ≤ desc.totalByteSize) := by
  cases wLen with
  | zero =>
    exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | succ m =>
    have hne : m + 1 ≠ 0 := Nat.succ_ne_zero m
    rcases Nat.lt_or_ge desc.totalByteSize (wOff + (m + 1)) with hoob | hin
    · have htb := (evalRawMutStaticWrite_outOfBounds_exact desc rootTag 0 wOff (m + 1) hne hoob).2.1
      rw [htb]
      constructor
      · intro h; cases h
      · rintro (h0 | hle)
        · exact absurd h0 hne
        · exact absurd hle (Nat.not_le_of_gt hoob)
    · have hlenF : ((m + 1) == 0) = false := rfl
      have hnotGt : ¬ (wOff + (m + 1) > desc.totalByteSize) := Nat.not_lt.mpr hin
      have hok : evalRawMutStaticWriteTB (retagStaticErasedAt desc rootTag) wOff (m + 1) = .ok := by
        unfold evalRawMutStaticWriteTB retagStaticErasedAt
        have htotNe : (desc.totalByteSize == 0) = false := by
          cases ht : desc.totalByteSize with
          | zero => omega
          | succ _ => rfl
        simp only [hlenF, htotNe, hnotGt, Bool.false_eq_true, ↓reduceIte,
          List.any_cons, List.any_nil, Bool.and_false, Bool.or_false]
      rw [hok]
      exact ⟨fun _ => Or.inr hin, fun _ => rfl⟩

/-- **Full-domain two-way static-retag write theorem on real
`TreeBorrowsMemory.retag_ptr` + `TreeBorrowsMemory.store` (`charon#1620`) for
ALIGNED write pointers**: removes the domain side-conditions `wLen ≠ 0`,
`wOff + wLen ≤ totalByteSize`, and `staticAllocMutability = .mut` from
`tbm_staticPreserved_retag_then_store_iff`; the remaining hypothesis `haligned`
is essential (`tbm_staticPreserved_retag_then_store_iff_aligned_and_miri`):
for EVERY valid static layout `desc` (`StaticCellsValid`: arbitrary unsorted
field declaration order, zero-sized `UnsafeCell<()>` at any offset, syntactic
`Freeze` OR interior-mutable, including ZST statics), EVERY write offset `wOff`,
EVERY byte payload `wBytes` (including `wBytes = []` zero-length stores and
out-of-bounds windows `wOff + wBytes.length > desc.totalByteSize`), and EVERY
tags `rootTag, tmpTag`:
1. the preserved `#1620` shared temporary retag `&S` succeeds, minting tag `[0]`
   with `TreeBorrowsMemory.wfLive tbm1`;
2. **two-way `iff` with `evalRawMutStaticWriteMiri`**: storing
   through `[0]` succeeds (preserving `TreeBorrowsMemory.wfLive`) **iff**
   `evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag) wOff wBytes.length = .ok`;
3. **two-way `iff` with `evalRawMutStaticWriteTB`**: storing
   through `[0]` succeeds (preserving `TreeBorrowsMemory.wfLive`) **iff**
   `evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag) wOff wBytes.length = .ok`;
4. **byte-level two-way `iff`**: storing through `[0]` succeeds
   (preserving `TreeBorrowsMemory.wfLive`) **iff** either `wBytes.length = 0` or
   `wOff + wBytes.length ≤ desc.totalByteSize` and every byte in
   `[wOff, wOff + wBytes.length)` satisfies `byteInNonZeroUnsafeCell desc b = true`;
5. **exact classification of every case**:
   - `wBytes.length = 0`: both preserved and erased stores return `.ok` unchanged;
   - `wBytes.length ≠ 0` and `wOff + wBytes.length > desc.totalByteSize`: MiniRust
     `TreeBorrowsMemory.store` returns exact `.error (.ub "dereferencing pointer outside the bounds of its allocation")`,
     `evalRawMutStaticWriteTB` returns `.outOfBounds`, and `evalRawMutStaticWriteMiri`
     returns `.outOfBounds` (`.mut`) or `.readOnlyAlloc` (`.not`);
   - `wBytes.length ≠ 0`, in-bounds, with a non-`UnsafeCell` byte: MiniRust
     `TreeBorrowsMemory.store` returns exact `.error (.ub "Tree Borrows: local write of Frozen reference")`,
     `evalRawMutStaticWriteTB` returns `.ub`, and `evalRawMutStaticWriteMiri`
     returns `.ub` (`.mut`) or `.readOnlyAlloc` (`.not`);
6. **full-domain erased raw static store `iff`**: the erased root
   tag `[]` succeeds (preserving `TreeBorrowsMemory.wfLive`) **iff**
   `wBytes.length = 0 ∨ wOff + wBytes.length ≤ desc.totalByteSize` **iff**
   `evalRawMutStaticWriteTB (retagStaticErasedAt desc rootTag) wOff wBytes.length = .ok`. -/
theorem tbm_staticPreserved_retag_then_store_full_iff
    (desc : StaticTyDesc) (hvalid : StaticCellsValid desc) (align : Nat)
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (hdata : data.length = desc.totalByteSize) (addr : Int)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable) (fnIw : Bool)
    (wOff : Nat) (wBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (wAlign : Nat)
    (haligned : Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) = true) :
    let ptr0 : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
      { addr := addr + (wOff : Int), provenance := some (⟨0⟩, [0]) }
    let ptrRoot : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
      { addr := addr + (wOff : Int), provenance := some (⟨0⟩, []) }
    ∃ tbm1,
      TreeBorrowsMemory.retag_ptr (staticTbm data addr align) TreeBorrowsMemory.new_call
          { thin_pointer := { addr := addr, provenance := some (⟨0⟩, []) }, metadata := none }
          (.Ref .Immutable (staticPointeeInfoMR desc align)) false fnIw lookup =
        .ok ({ thin_pointer := { addr := addr, provenance := some (⟨0⟩, [0]) }, metadata := none },
          tbm1, TreeBorrowsMemory.new_call) ∧
      TreeBorrowsMemory.wfLive tbm1 ∧
      (∀ rootTag tmpTag,
        (∃ tbm2, TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ = .ok tbm2 ∧
            TreeBorrowsMemory.wfLive tbm2) ↔
          evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag)
            wOff wBytes.length = .ok) ∧
      (∀ rootTag tmpTag,
        (∃ tbm2, TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ = .ok tbm2 ∧
            TreeBorrowsMemory.wfLive tbm2) ↔
          evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag)
            wOff wBytes.length = .ok) ∧
      ((∃ tbm2, TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ = .ok tbm2 ∧
            TreeBorrowsMemory.wfLive tbm2) ↔
        (wBytes.length = 0 ∨
          (wOff + wBytes.length ≤ desc.totalByteSize ∧
            ∀ b, wOff ≤ b → b < wOff + wBytes.length →
              byteInNonZeroUnsafeCell desc b = true))) ∧
      (wBytes.length = 0 →
        TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ = .ok tbm1 ∧
        TreeBorrowsMemory.store (staticTbm data addr align) ptrRoot wBytes ⟨wAlign⟩ =
          .ok (staticTbm data addr align)) ∧
      (wBytes.length ≠ 0 → wOff + wBytes.length > desc.totalByteSize →
        TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ =
          .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
        TreeBorrowsMemory.store (staticTbm data addr align) ptrRoot wBytes ⟨wAlign⟩ =
          .error (.ub "dereferencing pointer outside the bounds of its allocation")) ∧
      (wBytes.length ≠ 0 → wOff + wBytes.length ≤ desc.totalByteSize →
        (∃ b, wOff ≤ b ∧ b < wOff + wBytes.length ∧ byteInNonZeroUnsafeCell desc b = false) →
        TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ =
          .error (.ub "Tree Borrows: local write of Frozen reference") ∧
        (∀ rootTag tmpTag,
          evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag) wOff wBytes.length =
            .ub)) ∧
      ((∃ tbmE, TreeBorrowsMemory.store (staticTbm data addr align) ptrRoot wBytes ⟨wAlign⟩ =
            .ok tbmE ∧ TreeBorrowsMemory.wfLive tbmE) ↔
        (wBytes.length = 0 ∨ wOff + wBytes.length ≤ desc.totalByteSize)) ∧
      (∀ rootTag,
        (∃ tbmE, TreeBorrowsMemory.store (staticTbm data addr align) ptrRoot wBytes ⟨wAlign⟩ =
            .ok tbmE ∧ TreeBorrowsMemory.wfLive tbmE) ↔
          evalRawMutStaticWriteTB (retagStaticErasedAt desc rootTag) wOff wBytes.length = .ok) := by
  dsimp only
  have hdisj := staticCellsValid_disjointInBounds desc hvalid
  obtain ⟨inside, hlen, hbytes, hretag⟩ :=
    tbm_staticPreserved_retag_ptr desc align data addr lookup fnIw hdisj hdata
  have hwf0 : TreeBorrowsMemory.wfLive (staticTbm data addr align) :=
    staticTbm_wfLive data addr align
  have hwf1 : TreeBorrowsMemory.wfLive (staticTbmRetagged data addr align inside) :=
    TreeBorrowsMemory.retag_ptr_wfLive hwf0 hretag
  let tbm1 := staticTbmRetagged data addr align inside
  let ptr0 : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
    { addr := addr + (wOff : Int), provenance := some (⟨0⟩, [0]) }
  let ptrRoot : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
    { addr := addr + (wOff : Int), provenance := some (⟨0⟩, []) }
  have hzero : wBytes.length = 0 →
      TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ = .ok tbm1 ∧
      TreeBorrowsMemory.store (staticTbm data addr align) ptrRoot wBytes ⟨wAlign⟩ =
        .ok (staticTbm data addr align) := by
    intro hz
    have hnil : wBytes = [] := List.eq_nil_of_length_eq_zero hz
    subst hnil
    exact ⟨tbm_store_zeroLen_always_ok tbm1 ptr0 ⟨wAlign⟩ haligned,
      tbm_store_zeroLen_always_ok (staticTbm data addr align) ptrRoot ⟨wAlign⟩ haligned⟩
  have hoob : wBytes.length ≠ 0 → wOff + wBytes.length > desc.totalByteSize →
      TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ =
        .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
      TreeBorrowsMemory.store (staticTbm data addr align) ptrRoot wBytes ⟨wAlign⟩ =
        .error (.ub "dereferencing pointer outside the bounds of its allocation") := by
    intro hne hgt
    have hgt' : wOff + wBytes.length > data.length := by omega
    exact ⟨tbm_static_store_outOfBounds data addr align
        { root := ⟨[⟨[], inside, .No⟩], List.replicate data.length (.Unprot .Unique), .No⟩ }
        [0] wOff wBytes wAlign hne hgt' haligned,
      tbm_static_store_outOfBounds data addr align
        { root := ⟨[], List.replicate data.length (.Unprot .Unique), .No⟩ }
        [] wOff wBytes wAlign hne hgt' haligned⟩
  have hfrzErr : wBytes.length ≠ 0 → wOff + wBytes.length ≤ desc.totalByteSize →
      (∃ b, wOff ≤ b ∧ b < wOff + wBytes.length ∧ byteInNonZeroUnsafeCell desc b = false) →
      TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ =
        .error (.ub "Tree Borrows: local write of Frozen reference") ∧
      (∀ rootTag tmpTag,
        evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag) wOff wBytes.length =
          .ub) := by
    intro hne hin hbad
    exact ⟨(tbm_staticRetagged_store_ok_iff_all_bytes_in_unsafeCell desc align data addr inside
        hlen hdata hbytes wOff wBytes wAlign hne hin haligned).2 hbad,
      fun r t => d1_evalRawMutStaticWriteTB_preserved_ub_of_freezeByte desc r t wOff wBytes.length
        hne hin hbad⟩
  have hbyteIff : (∃ tbm2, TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ = .ok tbm2 ∧
        TreeBorrowsMemory.wfLive tbm2) ↔
      (wBytes.length = 0 ∨
        (wOff + wBytes.length ≤ desc.totalByteSize ∧
          ∀ b, wOff ≤ b → b < wOff + wBytes.length →
            byteInNonZeroUnsafeCell desc b = true)) := by
    by_cases hwl : wBytes.length = 0
    · have ⟨hst, _⟩ := hzero hwl
      exact ⟨fun _ => Or.inl hwl, fun _ => ⟨tbm1, hst, hwf1⟩⟩
    · rcases Nat.lt_or_ge desc.totalByteSize (wOff + wBytes.length) with hgt | hin
      · have ⟨herr, _⟩ := hoob hwl hgt
        constructor
        · rintro ⟨_, hst, _⟩; rw [herr] at hst; cases hst
        · rintro (h0 | ⟨hle, _⟩)
          · exact absurd h0 hwl
          · exact absurd hle (Nat.not_le_of_gt hgt)
      · have hcore := (tbm_staticRetagged_store_ok_iff_all_bytes_in_unsafeCell desc align data
          addr inside hlen hdata hbytes wOff wBytes wAlign hwl hin haligned).1
        constructor
        · rintro ⟨tbm2, hst, _⟩
          exact Or.inr ⟨hin, hcore.mp ⟨tbm2, hst⟩⟩
        · rintro (h0 | ⟨_, hall⟩)
          · exact absurd h0 hwl
          · obtain ⟨tbm2, hst⟩ := hcore.mpr hall
            exact ⟨tbm2, hst, TreeBorrowsMemory.store_wfLive hwf1 hst⟩
  have htbIff : ∀ rootTag tmpTag,
      (∃ tbm2, TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ = .ok tbm2 ∧
          TreeBorrowsMemory.wfLive tbm2) ↔
        evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag)
          wOff wBytes.length = .ok := by
    intro rootTag tmpTag
    rw [hbyteIff]
    by_cases hwl : wBytes.length = 0
    · rw [hwl]; exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩
    · rcases Nat.lt_or_ge desc.totalByteSize (wOff + wBytes.length) with hgt | hin
      · have htb := (evalRawMutStaticWrite_outOfBounds_exact desc rootTag tmpTag wOff wBytes.length
          hwl hgt).1
        rw [htb]
        constructor
        · rintro (h0 | ⟨hle, _⟩)
          · exact absurd h0 hwl
          · exact absurd hle (Nat.not_le_of_gt hgt)
        · intro h; cases h
      · cases hmut : staticAllocMutability desc with
        | «mut» =>
          have hlenF : (wBytes.length == 0) = false := by
            cases hln : wBytes.length with
            | zero => exact absurd hln hwl
            | succ _ => rfl
          have hmiri : evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag)
              wOff wBytes.length =
              evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag)
                wOff wBytes.length := by
            have hmutF : (staticAllocMutability desc == .not) = false := by rw [hmut]; rfl
            have hnotGt : ¬ (wOff + wBytes.length > desc.totalByteSize) := Nat.not_lt.mpr hin
            unfold evalRawMutStaticWriteMiri
            change (if (wBytes.length == 0) = true then StaticWriteOutcome.ok
              else if (staticAllocMutability desc == .not) = true then .readOnlyAlloc
              else if wOff + wBytes.length > desc.totalByteSize then .outOfBounds
              else evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag)
                wOff wBytes.length) = _
            simp only [hlenF, hmutF, hnotGt, Bool.false_eq_true, ↓reduceIte]
          rw [← hmiri, (static_preserved_write_ok_iff_all_bytes_in_unsafeCell desc rootTag tmpTag
            wOff wBytes.length hin hmut).1]
          exact ⟨fun h => by rcases h with h0 | ⟨_, hall⟩; exact absurd h0 hwl; exact hall,
            fun hall => Or.inr ⟨hin, hall⟩⟩
        | not =>
          have hfrz : desc.isSyntacticFreeze = true := by
            unfold staticAllocMutability at hmut
            cases hf : desc.isSyntacticFreeze with
            | true => rfl
            | false => rw [hf] at hmut; cases hmut
          have hb0 : byteInNonZeroUnsafeCell desc wOff = false :=
            byteInNonZeroUnsafeCell_false_of_isSyntacticFreeze desc hfrz wOff
          have hub := d1_evalRawMutStaticWriteTB_preserved_ub_of_freezeByte desc rootTag tmpTag
            wOff wBytes.length hwl hin ⟨wOff, Nat.le_refl _, by omega, hb0⟩
          rw [hub]
          constructor
          · rintro (h0 | ⟨_, hall⟩)
            · exact absurd h0 hwl
            · have hT := hall wOff (Nat.le_refl _) (by omega)
              rw [hb0] at hT; cases hT
          · intro h; cases h
  have hmiriIff : ∀ rootTag tmpTag,
      (∃ tbm2, TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ = .ok tbm2 ∧
          TreeBorrowsMemory.wfLive tbm2) ↔
        evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag)
          wOff wBytes.length = .ok := by
    intro rootTag tmpTag
    by_cases hwl : wBytes.length = 0
    · have ⟨hst, _⟩ := hzero hwl
      rw [hwl]
      exact ⟨fun _ => rfl, fun _ => ⟨tbm1, hst, hwf1⟩⟩
    · cases hmut : staticAllocMutability desc with
      | «mut» =>
        rcases Nat.lt_or_ge desc.totalByteSize (wOff + wBytes.length) with hgt | hin
        · have ⟨herr, _⟩ := hoob hwl hgt
          have hmo := ((evalRawMutStaticWrite_outOfBounds_exact desc rootTag tmpTag wOff
            wBytes.length hwl hgt).2.2.1 hmut).1
          rw [hmo]
          constructor
          · rintro ⟨_, hst, _⟩; rw [herr] at hst; cases hst
          · intro h; cases h
        · rw [hbyteIff, (static_preserved_write_ok_iff_all_bytes_in_unsafeCell desc rootTag tmpTag
            wOff wBytes.length hin hmut).1]
          exact ⟨fun h => by rcases h with h0 | ⟨_, hall⟩; exact absurd h0 hwl; exact hall,
            fun hall => Or.inr ⟨hin, hall⟩⟩
      | not =>
        have hfrz : desc.isSyntacticFreeze = true := by
          unfold staticAllocMutability at hmut
          cases hf : desc.isSyntacticFreeze with
          | true => rfl
          | false => rw [hf] at hmut; cases hmut
        have hlenF : (wBytes.length == 0) = false := by
          cases hln : wBytes.length with
          | zero => exact absurd hln hwl
          | succ _ => rfl
        have hnotT : (staticAllocMutability desc == .not) = true := by rw [hmut]; rfl
        have hro : evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag)
            wOff wBytes.length = .readOnlyAlloc := by
          unfold evalRawMutStaticWriteMiri
          simp only [hlenF, hnotT, Bool.false_eq_true, ↓reduceIte]
        rw [hro, hbyteIff]
        constructor
        · rintro (h0 | ⟨_, hall⟩)
          · exact absurd h0 hwl
          · have hT := hall wOff (Nat.le_refl _) (by omega)
            rw [byteInNonZeroUnsafeCell_false_of_isSyntacticFreeze desc hfrz wOff] at hT
            cases hT
        · intro h; cases h
  have herasIff : (∃ tbmE, TreeBorrowsMemory.store (staticTbm data addr align) ptrRoot wBytes
        ⟨wAlign⟩ = .ok tbmE ∧ TreeBorrowsMemory.wfLive tbmE) ↔
      (wBytes.length = 0 ∨ wOff + wBytes.length ≤ desc.totalByteSize) := by
    by_cases hwl : wBytes.length = 0
    · have ⟨_, hst⟩ := hzero hwl
      exact ⟨fun _ => Or.inl hwl, fun _ => ⟨staticTbm data addr align, hst, hwf0⟩⟩
    · rcases Nat.lt_or_ge desc.totalByteSize (wOff + wBytes.length) with hgt | hin
      · have ⟨_, herr⟩ := hoob hwl hgt
        constructor
        · rintro ⟨_, hst, _⟩; rw [herr] at hst; cases hst
        · rintro (h0 | hle)
          · exact absurd h0 hwl
          · exact absurd hle (Nat.not_le_of_gt hgt)
      · obtain ⟨tbmE, hst⟩ := tbm_staticErased_store_always_ok data addr align wOff wBytes wAlign
          hwl (by rw [hdata]; exact hin) haligned
        exact ⟨fun _ => Or.inr hin, fun _ => ⟨tbmE, hst, TreeBorrowsMemory.store_wfLive hwf0 hst⟩⟩
  refine ⟨tbm1, hretag, hwf1, hmiriIff, htbIff, hbyteIff, hzero, hoob, hfrzErr, herasIff,
    fun rootTag => herasIff.trans (d1_evalRawMutStaticWriteTB_erased_ok_iff desc rootTag wOff
      wBytes.length).symm⟩

/-- **Misaligned-store boundary of `TreeBorrowsMemory.store`**: on ANY memory,
ANY pointer, and ANY payload — including the zero-length payload `[]`, which
skips every other check — a store through a misaligned pointer is rejected
FIRST, with exact `.ub "store to a misaligned pointer"`. -/
theorem tbm_store_misaligned_ub (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (align : LibSpecr.Align)
    (hmis : Align.is_aligned align ptr.addr = false) :
    TreeBorrowsMemory.store tbm ptr bytes align =
      .error (.ub "store to a misaligned pointer") := by
  unfold TreeBorrowsMemory.store BasicMemory.store
  simp only [hmis, Bool.not_false, ↓reduceIte, bind, Except.bind, ub]

/-- **Alignment-complete static-retag write theorem (`charon#1620`)**: the
full-domain theorem `tbm_staticPreserved_retag_then_store_full_iff` still
assumes an ALIGNED write pointer, and that assumption is essential: Anneal's
`evalRawMutStaticWriteMiri` / `evalRawMutStaticWriteTB` have no alignment
component, whereas MiniRust's `BasicMemory::store` rejects a misaligned pointer
before anything else (even for `wBytes = []`). With NO alignment hypothesis, for
every valid static layout, write offset, payload, and write alignment:
1. the preserved `#1620` shared temporary retag `&S` succeeds (`wfLive`);
2. the store through the preserved tag `[0]` succeeds **iff** the write pointer
   is aligned AND `evalRawMutStaticWriteMiri` accepts the write (likewise for
   `evalRawMutStaticWriteTB`);
3. on a misaligned write pointer BOTH the preserved-tag store and the erased
   root-tag store raise exactly `.ub "store to a misaligned pointer"`, for every
   payload — so the Anneal verdict `.ok` of a zero-length (or otherwise valid)
   write is NOT matched by MiniRust there. -/
theorem tbm_staticPreserved_retag_then_store_iff_aligned_and_miri
    (desc : StaticTyDesc) (hvalid : StaticCellsValid desc) (align : Nat)
    (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (hdata : data.length = desc.totalByteSize) (addr : Int)
    (lookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable) (fnIw : Bool)
    (wOff : Nat) (wBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (wAlign : Nat) :
    let ptr0 : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
      { addr := addr + (wOff : Int), provenance := some (⟨0⟩, [0]) }
    let ptrRoot : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
      { addr := addr + (wOff : Int), provenance := some (⟨0⟩, []) }
    ∃ tbm1,
      TreeBorrowsMemory.retag_ptr (staticTbm data addr align) TreeBorrowsMemory.new_call
          { thin_pointer := { addr := addr, provenance := some (⟨0⟩, []) }, metadata := none }
          (.Ref .Immutable (staticPointeeInfoMR desc align)) false fnIw lookup =
        .ok ({ thin_pointer := { addr := addr, provenance := some (⟨0⟩, [0]) }, metadata := none },
          tbm1, TreeBorrowsMemory.new_call) ∧
      TreeBorrowsMemory.wfLive tbm1 ∧
      (∀ rootTag tmpTag,
        (∃ tbm2, TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ = .ok tbm2 ∧
            TreeBorrowsMemory.wfLive tbm2) ↔
          (Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) = true ∧
            evalRawMutStaticWriteMiri desc (retagStaticPreservedAt desc rootTag tmpTag)
              wOff wBytes.length = .ok)) ∧
      (∀ rootTag tmpTag,
        (∃ tbm2, TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ = .ok tbm2 ∧
            TreeBorrowsMemory.wfLive tbm2) ↔
          (Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) = true ∧
            evalRawMutStaticWriteTB (retagStaticPreservedAt desc rootTag tmpTag)
              wOff wBytes.length = .ok)) ∧
      (Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) = false →
        TreeBorrowsMemory.store tbm1 ptr0 wBytes ⟨wAlign⟩ =
          .error (.ub "store to a misaligned pointer") ∧
        TreeBorrowsMemory.store (staticTbm data addr align) ptrRoot wBytes ⟨wAlign⟩ =
          .error (.ub "store to a misaligned pointer")) := by
  dsimp only
  obtain ⟨inside, _, _, hretag⟩ :=
    tbm_staticPreserved_retag_ptr desc align data addr lookup fnIw
      (staticCellsValid_disjointInBounds desc hvalid) hdata
  have hwf1 : TreeBorrowsMemory.wfLive (staticTbmRetagged data addr align inside) :=
    TreeBorrowsMemory.retag_ptr_wfLive (staticTbm_wfLive data addr align) hretag
  have hmis : Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) = false →
      TreeBorrowsMemory.store (staticTbmRetagged data addr align inside)
          { addr := addr + (wOff : Int), provenance := some (⟨0⟩, [0]) } wBytes ⟨wAlign⟩ =
        .error (.ub "store to a misaligned pointer") ∧
      TreeBorrowsMemory.store (staticTbm data addr align)
          { addr := addr + (wOff : Int), provenance := some (⟨0⟩, []) } wBytes ⟨wAlign⟩ =
        .error (.ub "store to a misaligned pointer") :=
    fun h => ⟨tbm_store_misaligned_ub _ _ wBytes ⟨wAlign⟩ h,
      tbm_store_misaligned_ub _ _ wBytes ⟨wAlign⟩ h⟩
  refine ⟨staticTbmRetagged data addr align inside, hretag, hwf1, ?_, ?_, hmis⟩
  · intro rootTag tmpTag
    cases hal : Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) with
    | false =>
      constructor
      · rintro ⟨tbm2, hst, _⟩
        rw [(hmis hal).1] at hst
        cases hst
      · rintro ⟨h, _⟩
        cases h
    | true =>
      obtain ⟨tbmX, hretX, _, hmiriX, _⟩ :=
        tbm_staticPreserved_retag_then_store_full_iff desc hvalid align data hdata addr lookup
          fnIw wOff wBytes wAlign hal
      have heq : tbmX = staticTbmRetagged data addr align inside := by
        rw [hretag] at hretX
        injection hretX with h1
        exact (congrArg (fun x => x.2.1) h1).symm
      subst heq
      exact (hmiriX rootTag tmpTag).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  · intro rootTag tmpTag
    cases hal : Align.is_aligned ⟨wAlign⟩ (addr + (wOff : Int)) with
    | false =>
      constructor
      · rintro ⟨tbm2, hst, _⟩
        rw [(hmis hal).1] at hst
        cases hst
      · rintro ⟨h, _⟩
        cases h
    | true =>
      obtain ⟨tbmX, hretX, _, _, htbX, _⟩ :=
        tbm_staticPreserved_retag_then_store_full_iff desc hvalid align data hdata addr lookup
          fnIw wOff wBytes wAlign hal
      have heq : tbmX = staticTbmRetagged data addr align inside := by
        rw [hretag] at hretX
        injection hretX with h1
        exact (congrArg (fun x => x.2.1) h1).symm
      subst heq
      exact (htbX rootTag tmpTag).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

/-! #### 6.4.2 Choice-Free Symbolic `MachTB.wfLive` Preservation (`stepsTB_wfLive_choiceFree`) -/


private theorem d1_pure_ok {α : Type} {x y : α} (h : (pure x : Interp α) = .ok y) : x = y := by
  cases h; rfl


-- Choice-free wrappers mirroring `MiniRustSpec.Correspondence.Pointers` private helpers
private theorem d1_cm_tb_load_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : LibSpecr.Size} {align : LibSpecr.Align}
    {atomicity : Gen.Atomicity}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.load cm ptr len align atomicity = .ok (bytes, cm')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.load at h
  obtain ⟨⟨_, mem'⟩, hload, h⟩ := nwsr_bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
  exact TreeBorrowsMemory.load_wfLive hwf hload

private theorem d1_cm_tb_store_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)} {align : LibSpecr.Align}
    {atomicity : Gen.Atomicity}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.store cm ptr bytes align atomicity = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.store at h
  obtain ⟨mem', hstore, h⟩ := nwsr_bind_ok h
  obtain rfl := d1_pure_ok h
  exact TreeBorrowsMemory.store_wfLive hwf hstore

private theorem d1_cm_tb_deinit_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : LibSpecr.Size} {align : LibSpecr.Align}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.deinit cm ptr len align = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory :=
  d1_cm_tb_store_wfLive hwf h

private theorem d1_cm_tb_allocate_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {kind : Gen.AllocationKind} {size : LibSpecr.Size} {align : LibSpecr.Align}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.allocate cm kind size align = .ok (ptr, cm')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.allocate at h
  obtain ⟨⟨_, mem'⟩, halloc, h⟩ := nwsr_bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
  exact TreeBorrowsMemory.allocate_wfLive hwf halloc

private theorem d1_cm_tb_deallocate_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {kind : Gen.AllocationKind}
    {size : LibSpecr.Size} {align : LibSpecr.Align}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.deallocate cm ptr kind size align = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.deallocate at h
  obtain ⟨mem', hdealloc, h⟩ := nwsr_bind_ok h
  obtain rfl := d1_pure_ok h
  exact TreeBorrowsMemory.deallocate_wfLive hwf hdealloc

private theorem d1_cm_tb_end_call_wfLive_choiceFree {cm cm' : Gen.ConcurrentMemory TBM}
    {extra : Gen.TreeBorrowsFrameExtra}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.end_call cm extra = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.end_call at h
  obtain ⟨mem', hend, h⟩ := nwsr_bind_ok h
  obtain rfl := d1_pure_ok h
  exact tbm_end_call_wfLive_choiceFree hwf hend

private theorem d1_mutateCurFrameM_tb_wfLive {m m' : MachTB}
    {f : Gen.StackFrame TBM → Gen.StackFrame TBM}
    (hwf : MachTB.wfLive m) (h : mutateCurFrameM m f = .ok m') :
    MachTB.wfLive m' := by
  unfold mutateCurFrameM at h
  obtain ⟨t, _, h⟩ := nwsr_bind_ok h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some fr =>
    simp only [hlast] at h
    obtain ⟨_, _, h⟩ := nwsr_bind_ok h
    obtain rfl := d1_pure_ok h
    exact hwf

private theorem d1_jumpToBlockM_tb_wfLive {m m' : MachTB} {b : Gen.BbName}
    (hwf : MachTB.wfLive m) (h : jumpToBlockM m b = .ok m') :
    MachTB.wfLive m' :=
  d1_mutateCurFrameM_tb_wfLive hwf h

private theorem d1_terminateActiveThreadM_tb_wfLive {m m' : MachTB}
    (hwf : MachTB.wfLive m) (h : terminateActiveThreadM m = .ok m') :
    MachTB.wfLive m' := by
  unfold terminateActiveThreadM at h
  dsimp only at h
  by_cases ha : m.active_thread = 0
  · simp only [ha, ↓reduceIte] at h; cases h
  · simp only [ha, ↓reduceIte] at h
    obtain ⟨t, _, h⟩ := nwsr_bind_ok h
    by_cases hst : t.stack.length = 0
    · simp only [hst, ne_eq, not_true_eq_false, ↓reduceIte] at h
      obtain ⟨_, _, h⟩ := nwsr_bind_ok h
      obtain rfl := d1_pure_ok h
      exact hwf
    · simp only [ne_eq, hst, not_false_eq_true, ↓reduceIte] at h; cases h

private theorem d1_machineExitM_tb_ne_ok {α : Type} {m : MachTB} {x : α} :
    machineExitM (α := α) m ≠ .ok x := by
  intro h
  unfold machineExitM at h
  obtain ⟨_, _, h⟩ := nwsr_bind_ok h
  cases h

private theorem d1_loadRawDataM_tb_wfLive {m m' : MachTB}
    {ptr : Gen.Pointer Gen.TreeBorrowsProvenance} {ptrTy : Gen.PtrType} {data : List UInt8}
    (hwf : MachTB.wfLive m) (h : loadRawDataM m ptr ptrTy = .ok (data, m')) :
    MachTB.wfLive m' := by
  unfold loadRawDataM at h
  split at h
  · split at h
    · obtain ⟨⟨bytes, cm⟩, hl, h⟩ := nwsr_bind_ok h
      dsimp only at h
      split at h
      · obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
        exact d1_cm_tb_load_wfLive hwf hl
      · cases h
    · cases h
  · cases h

private theorem d1_prepareForInplacePassingM_tb_wfLive {m m' : MachTB} {place : Gen.Place TBM}
    {ty : Gen.Type} (hwf : MachTB.wfLive m)
    (h : prepareForInplacePassingM m place ty = .ok m') :
    MachTB.wfLive m' := by
  unfold prepareForInplacePassingM at h
  obtain ⟨_, _, h⟩ := nwsr_bind_ok h
  obtain ⟨_, _, h⟩ := nwsr_bind_ok h
  obtain ⟨_, _, h⟩ := nwsr_bind_ok h
  obtain ⟨_, _, h⟩ := nwsr_bind_ok h
  obtain ⟨cm, hd, h⟩ := nwsr_bind_ok h
  obtain rfl := d1_pure_ok h
  exact d1_cm_tb_deinit_wfLive hwf hd

private theorem d1_evalArgumentM_tb_wfLive {m m' : MachTB} {arg : Gen.ArgumentExpr}
    {v : Gen.Value TBM × Gen.Type} (hwf : MachTB.wfLive m)
    (h : evalArgumentM m arg = .ok (v, m')) : MachTB.wfLive m' := by
  cases arg with
  | ByValue e =>
    unfold evalArgumentM at h
    exact evalValueM_tb_wfLive e hwf h
  | InPlace p =>
    unfold evalArgumentM at h
    obtain ⟨⟨⟨place, ty⟩, m1⟩, hp, h⟩ := nwsr_bind_ok h
    obtain ⟨⟨val, m2⟩, hl, h⟩ := nwsr_bind_ok h
    obtain ⟨m3, hprep, h⟩ := nwsr_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
    exact d1_prepareForInplacePassingM_tb_wfLive
      (placeLoadM_tb_wfLive (evalPlaceM_tb_wfLive p hwf hp) hl) hprep

private theorem d1_evalArgumentsM_tb_wfLive :
    ∀ (args : List Gen.ArgumentExpr) {m m' : MachTB} {vs : List (Gen.Value TBM × Gen.Type)},
      MachTB.wfLive m → evalArgumentsM m args = .ok (vs, m') → MachTB.wfLive m'
  | [], _, _, _, hwf, h => by
    unfold evalArgumentsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
    exact hwf
  | a :: as, _, _, _, hwf, h => by
    unfold evalArgumentsM at h
    obtain ⟨⟨_, m1⟩, ha, h⟩ := nwsr_bind_ok h
    obtain ⟨⟨_, m2⟩, has, h⟩ := nwsr_bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
    exact d1_evalArgumentsM_tb_wfLive as (d1_evalArgumentM_tb_wfLive hwf ha) has

private theorem d1_allocFrameArgsM_tb_wfLive :
    ∀ (ls : List Gen.LocalName) {fr fr' : Gen.StackFrame TBM} {cm cm' : Gen.ConcurrentMemory TBM},
      TreeBorrowsMemory.wfLive cm.memory →
      allocFrameArgsM fr cm ls = .ok (fr', cm') → TreeBorrowsMemory.wfLive cm'.memory
  | [], _, _, _, _, hwf, h => by
    unfold allocFrameArgsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
    exact hwf
  | l :: ls, _, _, _, _, hwf, h => by
    unfold allocFrameArgsM at h
    obtain ⟨⟨fr1, cm1⟩, hsl, h⟩ := nwsr_bind_ok h
    exact d1_allocFrameArgsM_tb_wfLive ls (storageLiveM_tb_wfLive hwf hsl) h

private theorem d1_initFrameArgsM_tb_wfLive (frame : Gen.StackFrame TBM) :
    ∀ (ls : List Gen.LocalName) (args : List (Gen.Value TBM × Gen.Type)) {m m' : MachTB},
      MachTB.wfLive m → initFrameArgsM m frame ls args = .ok m' → MachTB.wfLive m'
  | [], _, _, _, hwf, h => by
    unfold initFrameArgsM at h
    obtain rfl := d1_pure_ok h
    exact hwf
  | _ :: _, [], _, _, hwf, h => by
    unfold initFrameArgsM at h
    obtain rfl := d1_pure_ok h
    exact hwf
  | l :: ls, (v, ty) :: args, m, _, hwf, h => by
    unfold initFrameArgsM at h
    obtain ⟨_, _, h⟩ := nwsr_bind_ok h
    obtain ⟨ok, _, h⟩ := nwsr_bind_ok h
    split at h
    · cases h
    · obtain ⟨_, _, h⟩ := nwsr_bind_ok h
      obtain ⟨_, _, h⟩ := nwsr_bind_ok h
      obtain ⟨ptr, _, h⟩ := nwsr_bind_ok h
      dsimp only at h
      split at h
      · rename_i m2 hst
        obtain ⟨m3, hm3, h⟩ := nwsr_bind_ok h
        obtain rfl := d1_pure_ok hm3
        exact d1_initFrameArgsM_tb_wfLive frame ls args (typedStoreM_tb_wfLive hwf hst) h
      all_goals
        obtain ⟨_, hbad, _⟩ := nwsr_bind_ok h
        cases hbad

private theorem d1_createFrameM_tb_wfLive {m m' : MachTB} {func : Gen.Function}
    {spa : Gen.StackPopAction TBM} {conv : Gen.CallingConvention} {retTy : Gen.Type}
    {args : List (Gen.Value TBM × Gen.Type)} {fr : Gen.StackFrame TBM}
    (hwf : MachTB.wfLive m) (h : createFrameM m func spa conv retTy args = .ok (fr, m')) :
    MachTB.wfLive m' := by
  unfold createFrameM at h
  obtain ⟨⟨fr1, cm1⟩, hsl, h⟩ := nwsr_bind_ok h
  obtain ⟨⟨fr2, cm2⟩, hal, h⟩ := nwsr_bind_ok h
  dsimp only at h
  have hcm2 : TreeBorrowsMemory.wfLive cm2.memory :=
    d1_allocFrameArgsM_tb_wfLive func.args (storageLiveM_tb_wfLive hwf hsl) hal
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := nwsr_bind_ok h
    obtain ⟨_, _, h⟩ := nwsr_bind_ok h
    split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨m3, hinit, h⟩ := nwsr_bind_ok h
        obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
        exact d1_initFrameArgsM_tb_wfLive fr2 func.args args (m := { m with mem := cm2 }) hcm2 hinit

private theorem d1_evalCallM_tb_wfLive {m m' : MachTB} {callee : Gen.Function}
    {conv : Gen.CallingConvention} {args : List (Gen.Value TBM × Gen.Type)}
    {ret : Gen.Place TBM × Gen.Type} {nb ub' : Option Gen.BbName}
    (hwf : MachTB.wfLive m) (h : evalCallM m callee conv args ret nb ub' = .ok m') :
    MachTB.wfLive m' := by
  unfold evalCallM at h
  obtain ⟨⟨fr, m1⟩, hc, h⟩ := nwsr_bind_ok h
  dsimp only at h
  have hm1 := d1_createFrameM_tb_wfLive hwf hc
  unfold mutateCurStackM at h
  obtain ⟨⟨_, m2⟩, hs, h⟩ := nwsr_bind_ok h
  obtain rfl := d1_pure_ok h
  obtain ⟨_, _, hs⟩ := nwsr_bind_ok hs
  obtain ⟨_, hpure, hs⟩ := nwsr_bind_ok hs
  obtain ⟨_, _, hs⟩ := nwsr_bind_ok hs
  obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok hs)
  exact hm1

/-- **Choice-free `evalIntrinsicM` preservation of `MachTB.wfLive`**
(zero `Classical.choice`, depending only on `{propext, Quot.sound}`). -/
theorem evalIntrinsicM_tb_wfLive_choiceFree {m m' : MachTB} {intrinsic : Gen.IntrinsicOp}
    {arguments : List (Gen.Value TBM × Gen.Type)} {retTy : Gen.Type} {val : Gen.Value TBM}
    (hwf : MachTB.wfLive m) (h : evalIntrinsicM m intrinsic arguments retTy = .ok (val, m')) :
    MachTB.wfLive m' := by
  cases intrinsic with
  | PointerExposeProvenance =>
    dsimp only [evalIntrinsicM] at h
    rcases arguments with _ | ⟨⟨v, tv⟩, _ | ⟨b, cs⟩⟩
    · have h0 : ¬ ((0 : Nat) = 1) := by decide
      simp only [List.length_nil, ne_eq, h0, not_false_eq_true, ↓reduceIte, ub] at h
      cases h
    · simp only [List.length_singleton, ne_eq, not_true_eq_false, ↓reduceIte] at h
      rcases v with _ | _ | ⟨ptr, _ | _⟩ | _ | _
      · dsimp only [ub] at h; cases h
      · dsimp only [ub] at h; cases h
      · rcases retTy with ⟨_ | _, ⟨sz⟩⟩ | _ | _ | _ | _ | _ | _ | _
        · by_cases hsz : sz = 8
          · subst hsz
            dsimp only at h
            obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
            exact hwf
          · dsimp only at h
            split at h
            · rename_i heq
              exact absurd (by injection heq with h1; injection h1 with _ h2; injection h2) hsz
            · dsimp only [ub] at h; cases h
        all_goals (dsimp only [ub] at h; cases h)
      all_goals (dsimp only [ub] at h; cases h)
    · have hne : ¬ (((v, tv) :: b :: cs).length = 1) := by
        simp only [List.length_cons]; omega
      simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte, ub] at h
      cases h
  | PointerWithExposedProvenance =>
    dsimp only [evalIntrinsicM] at h
    rcases arguments with _ | ⟨⟨v, tv⟩, _ | ⟨b, cs⟩⟩
    · have h0 : ¬ ((0 : Nat) = 1) := by decide
      simp only [List.length_nil, ne_eq, h0, not_false_eq_true, ↓reduceIte, ub] at h
      cases h
    · simp only [List.length_singleton, ne_eq, not_true_eq_false, ↓reduceIte] at h
      rcases v with addr | _ | _ | _ | _
      · cases retTy with
        | Ptr retPtrTy =>
          dsimp only at h
          by_cases hmk : PtrType.meta_kind retPtrTy = .None
          · simp only [hmk, not_true_eq_false, ↓reduceIte] at h
            obtain ⟨_, _, h⟩ := nwsr_bind_ok h
            obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
            exact hwf
          · simp only [hmk, not_false_eq_true, ↓reduceIte] at h
            dsimp only [ub] at h; cases h
        | _ => dsimp only [ub] at h; cases h
      all_goals (dsimp only [ub] at h; cases h)
    · have hne : ¬ (((v, tv) :: b :: cs).length = 1) := by
        simp only [List.length_cons]; omega
      simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte, ub] at h
      cases h
  | Exit =>
    dsimp only [evalIntrinsicM] at h
    exact absurd h d1_machineExitM_tb_ne_ok
  | Abort =>
    dsimp only [evalIntrinsicM, abort] at h; cases h
  | Assume =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h); exact hwf)
      | (dsimp only [ub] at h; cases h)
  | PrintStdout =>
    dsimp only [evalIntrinsicM] at h
    split at h
    · obtain ⟨_, _, h⟩ := nwsr_bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
      exact hwf
    · dsimp only [ub] at h; cases h
  | PrintStderr =>
    dsimp only [evalIntrinsicM] at h
    split at h
    · obtain ⟨_, _, h⟩ := nwsr_bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
      exact hwf
    · dsimp only [ub] at h; cases h
  | Allocate =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨⟨_, cm⟩, ha, h⟩ := nwsr_bind_ok h
         obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
         exact d1_cm_tb_allocate_wfLive hwf ha)
  | Deallocate =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨cm, hd, h⟩ := nwsr_bind_ok h
         obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
         exact d1_cm_tb_deallocate_wfLive hwf hd)
  | RawEq =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨⟨_, m1⟩, hl1, h⟩ := nwsr_bind_ok h
         obtain ⟨⟨_, m2⟩, hl2, h⟩ := nwsr_bind_ok h
         obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h)
         exact d1_loadRawDataM_tb_wfLive (d1_loadRawDataM_tb_wfLive hwf hl1) hl2)
  | GetUnwindPayload =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := nwsr_bind_ok h
         repeat' split at h
         all_goals first
           | (obtain ⟨_, rfl⟩ := Prod.mk.inj (d1_pure_ok h); exact hwf)
           | (dsimp only [ub] at h; cases h))
  | _ =>
    dsimp only [evalIntrinsicM, unsupported] at h; cases h

/-- **Choice-free `evalReturnM` preservation of `MachTB.wfLive`** across
return-value loading, local teardown (`deallocAllM`), and frame protector
release (`end_call`, via `tbm_end_call_wfLive_choiceFree`). -/
theorem evalReturnM_tb_wfLive_choiceFree {m m' : MachTB}
    (hwf : MachTB.wfLive m) (h : evalReturnM m = .ok m') :
    MachTB.wfLive m' := by
  unfold evalReturnM at h
  obtain ⟨t, _, h⟩ := nwsr_bind_ok h
  dsimp only at h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some f =>
    simp only [hlast] at h
    obtain ⟨frame, hfr, h⟩ := nwsr_bind_ok h
    cases d1_pure_ok hfr
    obtain ⟨threads, _, h⟩ := nwsr_bind_ok h
    obtain ⟨calleeTy, _, h⟩ := nwsr_bind_ok h
    obtain ⟨lay, _, h⟩ := nwsr_bind_ok h
    obtain ⟨align, _, h⟩ := nwsr_bind_ok h
    obtain ⟨retPtr, _, h⟩ := nwsr_bind_ok h
    obtain ⟨⟨retVal, m1⟩, hload, h⟩ := nwsr_bind_ok h
    have hm1 := typedLoadM_tb_wfLive (m := { m with threads := threads }) hwf hload
    obtain ⟨⟨frame1, cm1⟩, hdealloc, h⟩ := nwsr_bind_ok h
    dsimp only at h
    have hcm1 := deallocAllM_tb_wfLive f.locals.entries.length hm1 hdealloc
    obtain ⟨cm2, hend, h⟩ := nwsr_bind_ok h
    have hcm2 : MachTB.wfLive { m1 with mem := cm2 } :=
      d1_cm_tb_end_call_wfLive_choiceFree hcm1 hend
    cases hspa : frame1.stack_pop_action with
    | BottomOfStack =>
      simp only [hspa] at h
      exact d1_terminateActiveThreadM_tb_wfLive hcm2 h
    | BackToCaller nextBlock _ callerRetPtr =>
      simp only [hspa] at h
      obtain ⟨t2, _, h⟩ := nwsr_bind_ok h
      by_cases hst : t2.stack.length = 0
      · simp only [hst, ↓reduceIte] at h; cases h
      · simp only [hst, ↓reduceIte] at h
        obtain ⟨m2, hstore, h⟩ := nwsr_bind_ok h
        have hm2 := typedStoreM_tb_wfLive hcm2 hstore
        cases nextBlock with
        | none => cases h
        | some nb => exact d1_jumpToBlockM_tb_wfLive hm2 h

/-- **Choice-free `evalTerminatorM` preservation of `MachTB.wfLive`**. -/
theorem evalTerminatorM_tb_wfLive_choiceFree {m m' : MachTB} {term : Gen.Terminator}
    (hwf : MachTB.wfLive m) (h : evalTerminatorM m term = .ok m') :
    MachTB.wfLive m' := by
  cases term with
  | Goto blockName => exact d1_jumpToBlockM_tb_wfLive hwf h
  | Switch value cases fallback =>
    unfold evalTerminatorM at h
    obtain ⟨⟨⟨v, _⟩, m1⟩, hv, h⟩ := nwsr_bind_ok h
    dsimp only at h
    have hm1 := evalValueM_tb_wfLive value hwf hv
    cases v with
    | Int i => exact d1_jumpToBlockM_tb_wfLive hm1 h
    | _ => cases h
  | Unreachable => unfold evalTerminatorM at h; cases h
  | Call callee conv arguments retExpr nextBlock unwindBlock =>
    unfold evalTerminatorM at h
    obtain ⟨⟨⟨retPlace, retTy⟩, m1⟩, hp, h⟩ := nwsr_bind_ok h
    obtain ⟨m2, hprep, h⟩ := nwsr_bind_ok h
    obtain ⟨⟨⟨calleeVal, _⟩, m3⟩, hv, h⟩ := nwsr_bind_ok h
    obtain ⟨calleeFn, _, h⟩ := nwsr_bind_ok h
    obtain ⟨⟨args, m4⟩, hargs, h⟩ := nwsr_bind_ok h
    exact d1_evalCallM_tb_wfLive
      (d1_evalArgumentsM_tb_wfLive arguments
        (evalValueM_tb_wfLive callee
          (d1_prepareForInplacePassingM_tb_wfLive (evalPlaceM_tb_wfLive retExpr hwf hp) hprep) hv)
        hargs) h
  | Return => exact evalReturnM_tb_wfLive_choiceFree hwf h
  | Intrinsic intrinsic arguments retExpr nextBlock =>
    unfold evalTerminatorM at h
    obtain ⟨⟨⟨retPlace, retTy⟩, m1⟩, hp, h⟩ := nwsr_bind_ok h
    obtain ⟨⟨args, m2⟩, ha, h⟩ := nwsr_bind_ok h
    obtain ⟨⟨val, m3⟩, hi, h⟩ := nwsr_bind_ok h
    obtain ⟨m4, hs, h⟩ := nwsr_bind_ok h
    have hm4 := placeStoreM_tb_wfLive
      (evalIntrinsicM_tb_wfLive_choiceFree
        (evalArgsM_tb_wfLive arguments (evalPlaceM_tb_wfLive retExpr hwf hp) ha) hi) hs
    cases nextBlock with
    | none => cases h
    | some nb => exact d1_jumpToBlockM_tb_wfLive hm4 h
  | _ => unfold evalTerminatorM at h; cases h

/-- **Choice-free single-step `MachTB.wfLive` preservation (`stepTB`)**
(zero `Classical.choice`, depending only on `{propext, Quot.sound}`). -/
theorem stepTB_wfLive_choiceFree {m m' : MachTB}
    (hwf : MachTB.wfLive m) (h : stepTB m = .ok m') :
    MachTB.wfLive m' := by
  unfold stepTB stepM at h
  cases hany : m.threads.any (fun t => decide (t.state = .Enabled)) with
  | false => simp only [hany, Bool.not_false, ↓reduceIte] at h; cases h
  | true =>
    simp only [hany, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    dsimp only [resetDataRaceTrackingM] at h
    obtain ⟨tid, _, h⟩ := nwsr_bind_ok h
    obtain ⟨frame, _, h⟩ := nwsr_bind_ok h
    obtain ⟨block, _, h⟩ := nwsr_bind_ok h
    have hm0 : MachTB.wfLive
        { { m with mem := { m.mem with accesses := [] } } with active_thread := tid } := hwf
    by_cases hns : frame.next_stmt = (block.statements.length : Int)
    · simp only [hns, ↓reduceIte] at h
      obtain ⟨m2, hterm, h⟩ := nwsr_bind_ok h
      obtain ⟨_, _, h⟩ := nwsr_bind_ok h
      obtain rfl := d1_pure_ok h
      exact evalTerminatorM_tb_wfLive_choiceFree hm0 hterm
    · simp only [hns, ↓reduceIte] at h
      obtain ⟨stmt, _, h⟩ := nwsr_bind_ok h
      obtain ⟨m1, hev, h⟩ := nwsr_bind_ok h
      obtain ⟨m2, hmut, h⟩ := nwsr_bind_ok h
      obtain ⟨_, _, h⟩ := nwsr_bind_ok h
      obtain rfl := d1_pure_ok h
      exact d1_mutateCurFrameM_tb_wfLive (evalStatementM_tb_wfLive hm0 hev) hmut

/-- **Choice-free arbitrary multi-step `MachTB.wfLive` preservation (`stepsTB n`)**:
for EVERY `n : Nat` and EVERY `MachTB` machine, every non-faulting `n`-step
execution preserves `MachTB.wfLive` with zero `Classical.choice` (`{propext, Quot.sound}`
only), eliminating the choice-axiom gap noted in `machTB_harnesses_initial_wfLive`. -/
theorem stepsTB_wfLive_choiceFree :
    ∀ {n : Nat} {m m' : MachTB},
      MachTB.wfLive m → stepsTB n m = .ok m' → MachTB.wfLive m'
  | 0, _, _, hwf, h => by
    unfold stepsTB stepsM at h
    obtain rfl := d1_pure_ok h
    exact hwf
  | _ + 1, _, _, hwf, h => by
    unfold stepsTB stepsM at h
    obtain ⟨m1, hs, h⟩ := nwsr_bind_ok h
    exact stepsTB_wfLive_choiceFree (stepTB_wfLive_choiceFree hwf hs) h

/-- **Symbolic `MachTB.wfLive` preservation for ALL static-access programs**:
for EVERY static layout `desc`, MiniRust type `sTy`, alignment `align`, initial
bytes `initBytes`, `preserved : Bool`, write offset `writeOff`, write type
`writeTy`, write value `writeVal`, and EVERY step count `n : Nat`, every
non-faulting `n`-step execution of `mkStaticAccessMachTB` ends in a
`MachTB.wfLive` machine (symbolic, choice-free). -/
theorem machTB_staticAccess_steps_wfLive
    (desc : StaticTyDesc) (sTy : Gen.Type) (align : Nat)
    (initBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (preserved : Bool)
    (writeOff : Int) (writeTy : Gen.Type) (writeVal : Int)
    (n : Nat) (m' : MachTB)
    (hsteps : stepsTB n
      (mkStaticAccessMachTB desc sTy align initBytes preserved writeOff writeTy writeVal) = .ok m') :
    MachTB.wfLive m' :=
  stepsTB_wfLive_choiceFree
    (machTB_harnesses_initial_wfLive.2.2.2.2.1 desc sTy align initBytes preserved writeOff
      writeTy writeVal)
    hsteps

/-- **Symbolic `MachTB.wfLive` preservation across ALL six execution harness
families** (for every step count `n : Nat`, every `mutPointee`, `fnIw`, `mode`,
`callerFn`, `calleeFn`, static layout, and `staticShapeBRepeatedWriteMachTB`,
choice-free). -/
theorem machTB_harnesses_steps_wfLive :
    (∀ (mutPointee : Gen.PointeeInfo) (fnIw : Bool) (n : Nat) (m' : MachTB),
      stepsTB n (mkForgetStyleMachTB mutPointee fnIw) = .ok m' → MachTB.wfLive m') ∧
    (∀ (fnIw : Bool) (n : Nat) (m' : MachTB),
      stepsTB n (mkForgetStyleUninitMachTB fnIw) = .ok m' → MachTB.wfLive m') ∧
    (∀ (mode : NoWritableCalleeMode) (n : Nat) (m' : MachTB),
      stepsTB n (mkNoWritableConflictMachTB mode) = .ok m' → MachTB.wfLive m') ∧
    (∀ (callerFn calleeFn : Gen.Function) (n : Nat) (m' : MachTB),
      stepsTB n (mkTwoFnMachTB callerFn calleeFn) = .ok m' → MachTB.wfLive m') ∧
    (∀ (desc : StaticTyDesc) (sTy : Gen.Type) (align : Nat)
        (initBytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (preserved : Bool)
        (writeOff : Int) (writeTy : Gen.Type) (writeVal : Int) (n : Nat) (m' : MachTB),
      stepsTB n
        (mkStaticAccessMachTB desc sTy align initBytes preserved writeOff writeTy writeVal) =
        .ok m' → MachTB.wfLive m') ∧
    (∀ (n : Nat) (m' : MachTB),
      stepsTB n staticShapeBRepeatedWriteMachTB = .ok m' → MachTB.wfLive m') :=
  ⟨fun p f _ _ h => stepsTB_wfLive_choiceFree (machTB_harnesses_initial_wfLive.1 p f) h,
   fun f _ _ h => stepsTB_wfLive_choiceFree (machTB_harnesses_initial_wfLive.2.1 f) h,
   fun mo _ _ h => stepsTB_wfLive_choiceFree (machTB_harnesses_initial_wfLive.2.2.1 mo) h,
   fun c1 c2 _ _ h => stepsTB_wfLive_choiceFree (machTB_harnesses_initial_wfLive.2.2.2.1 c1 c2) h,
   fun d s a i p o t v n m' h => machTB_staticAccess_steps_wfLive d s a i p o t v n m' h,
   fun _ _ h => stepsTB_wfLive_choiceFree machTB_harnesses_initial_wfLive.2.2.2.2.2 h⟩

/-! #### 6.4.3 Closed Zero-Hypothesis Non-Vacuity Canary for Part 6.4 -/

/-- **Closed non-vacuity canary for Part 6.4** (zero hypotheses):
instantiates `tbm_staticPreserved_retag_then_store_full_iff` and
`machTB_staticAccess_steps_wfLive` across:
1. zero-length stores (`wBytes = []`) at out-of-bounds offset `100` on BOTH
   reverse-offset mixed Shape (e) (`.mut`) and syntactic-`Freeze` Shape (a) (`.not`);
2. out-of-bounds non-zero stores `[6, 10)` on Shape (e) (MiniRust OOB UB +
   Miri `.outOfBounds`) and Shape (a) (MiniRust OOB UB + Miri `.readOnlyAlloc`);
3. in-bounds `Freeze` store `[0, 4)` on Shape (a) (MiniRust `"local write of Frozen reference"`
   + Miri `.readOnlyAlloc`), and valid/invalid stores `[4, 8)` / `[0, 1)` on Shape (e);
4. symbolic `MachTB.wfLive` preservation via `machTB_staticAccess_steps_wfLive`
   on Shape (e) preserved `AtomicI32` write (`n = 7`). -/
theorem canary_part6_fullDomain_and_symbolic_machTB_wfLive :
    (∃ tbmE tbmA,
      TreeBorrowsMemory.wfLive tbmE ∧
      TreeBorrowsMemory.wfLive tbmA ∧
      TreeBorrowsMemory.store tbmE
        { addr := 256 + ((100 : Nat) : Int), provenance := some (⟨0⟩, [0]) } [] ⟨1⟩ = .ok tbmE ∧
      TreeBorrowsMemory.store tbmA
        { addr := 256 + ((100 : Nat) : Int), provenance := some (⟨0⟩, [0]) } [] ⟨1⟩ = .ok tbmA ∧
      TreeBorrowsMemory.store tbmE
        { addr := 256 + ((6 : Nat) : Int), provenance := some (⟨0⟩, [0]) } (tbU32Bytes 7) ⟨1⟩ =
        .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
      TreeBorrowsMemory.store tbmA
        { addr := 256 + ((6 : Nat) : Int), provenance := some (⟨0⟩, [0]) } (tbU32Bytes 7) ⟨1⟩ =
        .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
      TreeBorrowsMemory.store tbmA
        { addr := 256 + ((0 : Nat) : Int), provenance := some (⟨0⟩, [0]) } (tbU32Bytes 7) ⟨4⟩ =
        .error (.ub "Tree Borrows: local write of Frozen reference") ∧
      (∃ tbmE2, TreeBorrowsMemory.store tbmE
        { addr := 256 + ((4 : Nat) : Int), provenance := some (⟨0⟩, [0]) } (tbU32Bytes 55) ⟨4⟩ =
        .ok tbmE2 ∧ TreeBorrowsMemory.wfLive tbmE2) ∧
      evalRawMutStaticWriteMiri staticShapeEReverseDesc
        (retagStaticPreservedAt staticShapeEReverseDesc 1 2) 100 0 = .ok ∧
      evalRawMutStaticWriteMiri staticShapeADesc
        (retagStaticPreservedAt staticShapeADesc 1 2) 100 0 = .ok ∧
      evalRawMutStaticWriteMiri staticShapeEReverseDesc
        (retagStaticPreservedAt staticShapeEReverseDesc 1 2) 6 4 = .outOfBounds ∧
      evalRawMutStaticWriteMiri staticShapeADesc
        (retagStaticPreservedAt staticShapeADesc 1 2) 6 4 = .readOnlyAlloc ∧
      evalRawMutStaticWriteMiri staticShapeADesc
        (retagStaticPreservedAt staticShapeADesc 1 2) 0 4 = .readOnlyAlloc) ∧
    (∃ m', stepsTB 7 (mkStaticAccessMachTB staticShapeEReverseDesc staticShapeETyMR 4
        staticShapeCInitBytes true 4 i32TyMR 55) = .ok m' ∧ MachTB.wfLive m') := by
  have hvE : StaticCellsValid staticShapeEReverseDesc := by decide
  have hvA : StaticCellsValid staticShapeADesc := by decide
  obtain ⟨tbmE, hretE, hwfE, hmiriE_0, _, _, hzeroE, _, _, _, _⟩ :=
    tbm_staticPreserved_retag_then_store_full_iff staticShapeEReverseDesc hvE 4
      staticShapeCInitBytes rfl 256 nwsrVtableLookup true 100 [] 1 (by decide)
  obtain ⟨tbmE_oob, hretE_oob, _, _, _, _, _, hoobE, _, _, _⟩ :=
    tbm_staticPreserved_retag_then_store_full_iff staticShapeEReverseDesc hvE 4
      staticShapeCInitBytes rfl 256 nwsrVtableLookup true 6 (tbU32Bytes 7) 1 (by decide)
  obtain ⟨tbmE_ok, hretE_ok, _, hmiriE_ok, _, _, _, _, _, _, _⟩ :=
    tbm_staticPreserved_retag_then_store_full_iff staticShapeEReverseDesc hvE 4
      staticShapeCInitBytes rfl 256 nwsrVtableLookup true 4 (tbU32Bytes 55) 4 (by decide)
  have heqE1 : tbmE_oob = tbmE := by
    rw [hretE] at hretE_oob; injection hretE_oob with h1; exact (congrArg (fun x => x.2.1) h1).symm
  have heqE2 : tbmE_ok = tbmE := by
    rw [hretE] at hretE_ok; injection hretE_ok with h1; exact (congrArg (fun x => x.2.1) h1).symm
  subst tbmE_oob; subst tbmE_ok
  obtain ⟨tbmA, hretA, hwfA, _, _, _, hzeroA, _, _, _, _⟩ :=
    tbm_staticPreserved_retag_then_store_full_iff staticShapeADesc hvA 4
      (tbU32Bytes 1) rfl 256 nwsrVtableLookup true 100 [] 1 (by decide)
  obtain ⟨tbmA_oob, hretA_oob, _, _, _, _, _, hoobA, _, _, _⟩ :=
    tbm_staticPreserved_retag_then_store_full_iff staticShapeADesc hvA 4
      (tbU32Bytes 1) rfl 256 nwsrVtableLookup true 6 (tbU32Bytes 7) 1 (by decide)
  obtain ⟨tbmA_frz, hretA_frz, _, _, _, _, _, _, hfrzA, _, _⟩ :=
    tbm_staticPreserved_retag_then_store_full_iff staticShapeADesc hvA 4
      (tbU32Bytes 1) rfl 256 nwsrVtableLookup true 0 (tbU32Bytes 7) 4 (by decide)
  have heqA1 : tbmA_oob = tbmA := by
    rw [hretA] at hretA_oob; injection hretA_oob with h1; exact (congrArg (fun x => x.2.1) h1).symm
  have heqA2 : tbmA_frz = tbmA := by
    rw [hretA] at hretA_frz; injection hretA_frz with h1; exact (congrArg (fun x => x.2.1) h1).symm
  subst tbmA_oob; subst tbmA_frz
  constructor
  · refine ⟨tbmE, tbmA, hwfE, hwfA, (hzeroE rfl).1, (hzeroA rfl).1,
      (hoobE (by decide) (by decide)).1, (hoobA (by decide) (by decide)).1,
      (hfrzA (by decide) (by decide) ⟨0, Nat.le_refl _, by decide, rfl⟩).1,
      (hmiriE_ok 1 2).mpr (by decide +kernel),
      (hmiriE_0 1 2).mp ⟨tbmE, (hzeroE rfl).1, hwfE⟩,
      rfl,
      ((evalRawMutStaticWrite_outOfBounds_exact staticShapeEReverseDesc 1 2 6 4
        (by decide) (by decide)).2.2.1 rfl).1,
      ((evalRawMutStaticWrite_outOfBounds_exact staticShapeADesc 1 2 6 4
        (by decide) (by decide)).2.2.2 rfl).1,
      rfl⟩
  · have hok : (stepsTB 7 (mkStaticAccessMachTB staticShapeEReverseDesc staticShapeETyMR 4
        staticShapeCInitBytes true 4 i32TyMR 55)).isOk = true := by decide +kernel
    cases hs : stepsTB 7 (mkStaticAccessMachTB staticShapeEReverseDesc staticShapeETyMR 4
        staticShapeCInitBytes true 4 i32TyMR 55) with
    | error e => rw [hs] at hok; cases hok
    | ok m' =>
      exact ⟨m', rfl, machTB_staticAccess_steps_wfLive staticShapeEReverseDesc staticShapeETyMR 4
        staticShapeCInitBytes true 4 i32TyMR 55 7 m' hs⟩


/-- **Closed non-vacuity canary for the alignment boundary** (zero hypotheses):
on the reverse-offset Shape (e) static at address `256`,
1. the aligned `AtomicI32` write `[4, 8)` (`wAlign = 4`) is accepted by both
   models through `tbm_staticPreserved_retag_then_store_iff_aligned_and_miri`;
2. the SAME in-cell bytes written through a pointer that is misaligned for the
   requested `wAlign = 8` (`260 % 8 ≠ 0`) are rejected by MiniRust with
   `.ub "store to a misaligned pointer"` although Anneal answers `.ok`;
3. the zero-length write at the misaligned offset `1` (`wAlign = 4`) is `.ok` in
   BOTH Anneal models but `.ub "store to a misaligned pointer"` on MiniRust —
   through the preserved tag and through the erased root tag alike. -/
theorem canary_static_store_alignment_boundary :
    ∃ tbm1,
      TreeBorrowsMemory.retag_ptr (staticTbm staticShapeCInitBytes 256 4)
          TreeBorrowsMemory.new_call
          { thin_pointer := { addr := 256, provenance := some (⟨0⟩, []) }, metadata := none }
          (.Ref .Immutable (staticPointeeInfoMR staticShapeEReverseDesc 4)) false true
          nwsrVtableLookup =
        .ok ({ thin_pointer := { addr := 256, provenance := some (⟨0⟩, [0]) }, metadata := none },
          tbm1, TreeBorrowsMemory.new_call) ∧
      (∃ tbm2, TreeBorrowsMemory.store tbm1
          { addr := 256 + ((4 : Nat) : Int), provenance := some (⟨0⟩, [0]) } (tbU32Bytes 55) ⟨4⟩ =
          .ok tbm2 ∧ TreeBorrowsMemory.wfLive tbm2) ∧
      TreeBorrowsMemory.store tbm1
          { addr := 256 + ((4 : Nat) : Int), provenance := some (⟨0⟩, [0]) } (tbU32Bytes 55) ⟨8⟩ =
        .error (.ub "store to a misaligned pointer") ∧
      evalRawMutStaticWriteMiri staticShapeEReverseDesc
        (retagStaticPreservedAt staticShapeEReverseDesc 1 2) 4 4 = .ok ∧
      TreeBorrowsMemory.store tbm1
          { addr := 256 + ((1 : Nat) : Int), provenance := some (⟨0⟩, [0]) } [] ⟨4⟩ =
        .error (.ub "store to a misaligned pointer") ∧
      TreeBorrowsMemory.store (staticTbm staticShapeCInitBytes 256 4)
          { addr := 256 + ((1 : Nat) : Int), provenance := some (⟨0⟩, []) } [] ⟨4⟩ =
        .error (.ub "store to a misaligned pointer") ∧
      evalRawMutStaticWriteMiri staticShapeEReverseDesc
        (retagStaticPreservedAt staticShapeEReverseDesc 1 2) 1 0 = .ok ∧
      evalRawMutStaticWriteTB (retagStaticPreservedAt staticShapeEReverseDesc 1 2) 1 0 = .ok := by
  have hv : StaticCellsValid staticShapeEReverseDesc := by decide
  obtain ⟨tbm1, hret1, _, hmiri1, _, _⟩ :=
    tbm_staticPreserved_retag_then_store_iff_aligned_and_miri staticShapeEReverseDesc hv 4
      staticShapeCInitBytes rfl 256 nwsrVtableLookup true 4 (tbU32Bytes 55) 4
  obtain ⟨tbm1b, hret1b, _, _, _, hmis1b⟩ :=
    tbm_staticPreserved_retag_then_store_iff_aligned_and_miri staticShapeEReverseDesc hv 4
      staticShapeCInitBytes rfl 256 nwsrVtableLookup true 4 (tbU32Bytes 55) 8
  obtain ⟨tbm1c, hret1c, _, _, _, hmis1c⟩ :=
    tbm_staticPreserved_retag_then_store_iff_aligned_and_miri staticShapeEReverseDesc hv 4
      staticShapeCInitBytes rfl 256 nwsrVtableLookup true 1 [] 4
  have heqb : tbm1 = tbm1b := by
    rw [hret1] at hret1b; injection hret1b with h1; exact congrArg (fun x => x.2.1) h1
  have heqc : tbm1 = tbm1c := by
    rw [hret1] at hret1c; injection hret1c with h1; exact congrArg (fun x => x.2.1) h1
  subst heqb heqc
  have hmiriOk : evalRawMutStaticWriteMiri staticShapeEReverseDesc
      (retagStaticPreservedAt staticShapeEReverseDesc 1 2) 4 4 = .ok := by decide +kernel
  exact ⟨tbm1, hret1, (hmiri1 1 2).mpr ⟨by decide, hmiriOk⟩, (hmis1b (by decide)).1, hmiriOk,
    (hmis1c (by decide)).1, (hmis1c (by decide)).2, rfl, rfl⟩


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

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.reborrowSettings_prot_eq_protToMiniRust' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.reborrowSettings_prot_eq_protToMiniRust

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.locOf_childPath_eq_parentPath' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.locOf_childPath_eq_parentPath

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_node_spec' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_node_spec

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_add_node_spec' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_add_node_spec

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.reborrowInitAccess_ok_of_pointwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.reborrowInitAccess_ok_of_pointwise

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.reborrowInitAccess_ok_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.reborrowInitAccess_ok_inv

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.reborrowInitAccess_error_is_ub' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.reborrowInitAccess_error_is_ub

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_reborrow_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_reborrow_eq

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_ptr_fnEntry_mutOrBox_simulates_world' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_ptr_fnEntry_mutOrBox_simulates_world

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_ptr_fnEntry_mutOrBox_simulates_traversalOrderDirect' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_ptr_fnEntry_mutOrBox_simulates_traversalOrderDirect

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_ptr_fnEntry_shared_wholeTree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_ptr_fnEntry_shared_wholeTree

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_ptr_fnEntry_zst_wholeTree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_ptr_fnEntry_zst_wholeTree

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_symbolic_retag_ptr_simulation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_symbolic_retag_ptr_simulation

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.releaseProtectorPermissions_ok_of_pointwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.releaseProtectorPermissions_ok_of_pointwise

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.releaseProtectorPermissions_ok_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.releaseProtectorPermissions_ok_inv

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.releaseProtectorPermissions_error_is_ub' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.releaseProtectorPermissions_error_is_ub

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_release_protector_ok_of_pointwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_release_protector_ok_of_pointwise

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_release_protector_ok_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_release_protector_ok_inv

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_release_protector_error_is_ub' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_release_protector_error_is_ub

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_release_protector_wfLive_choiceFree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_release_protector_wfLive_choiceFree

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_end_call_wfLive_choiceFree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_end_call_wfLive_choiceFree

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_release_protector_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_release_protector_eq

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_release_protector_deadAlloc_ok' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_release_protector_deadAlloc_ok

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_release_protector_simulates_execFrameExitMiniRust_step' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_release_protector_simulates_execFrameExitMiniRust_step

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_end_call_simulates_execFrameExitMiniRust' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_end_call_simulates_execFrameExitMiniRust

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_symbolic_endCall_multiEntry_simulation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_symbolic_endCall_multiEntry_simulation

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.permission_prevents_deallocation_iff_foreign_write_err' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.permission_prevents_deallocation_iff_foreign_write_err

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.contains_strong_protector_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.contains_strong_protector_iff

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_eq

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_strong_protector_ub' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_strong_protector_ub

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_weak_box_ok_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_weak_box_ok_iff

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_symbolic_deallocate_strong_vs_weak' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_symbolic_deallocate_strong_vs_weak

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_frame_outside' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_frame_outside

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_comm_of_disjoint' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_comm_of_disjoint

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_release_protector_frame_outside' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_release_protector_frame_outside

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_slice_disjoint_getMut_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_slice_disjoint_getMut_sound

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.permission_isForeignPassive_preserved' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.permission_isForeignPassive_preserved

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.treeSimInvMulti_of_treeSimInv' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.treeSimInvMulti_of_treeSimInv

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.treeSimInvMulti_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.treeSimInvMulti_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tree_read_simulates_node_access_multi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tree_read_simulates_node_access_multi

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tree_write_simulates_node_access_multi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tree_write_simulates_node_access_multi

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_load_simulates_execWorldRangeRead_multi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_load_simulates_execWorldRangeRead_multi

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_store_simulates_execWorldRangeWrite_multi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_store_simulates_execWorldRangeWrite_multi

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.treeSimInvMulti_preserved_on_disjoint_window' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.treeSimInvMulti_preserved_on_disjoint_window

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_treeSimInvMulti_disjoint_slices' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_treeSimInvMulti_disjoint_slices

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_box_weak_vs_mut_strong_dealloc_e2e' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_box_weak_vs_mut_strong_dealloc_e2e

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.collectNonZeroUnsafeCells_nil_of_isSyntacticFreeze' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.collectNonZeroUnsafeCells_nil_of_isSyntacticFreeze

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.collectFieldsNonZeroUnsafeCells_nil_of_fieldsSyntacticFreeze' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.collectFieldsNonZeroUnsafeCells_nil_of_fieldsSyntacticFreeze

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.byteInNonZeroUnsafeCell_false_of_isSyntacticFreeze' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.byteInNonZeroUnsafeCell_false_of_isSyntacticFreeze

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_store_zeroLen_always_ok' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_store_zeroLen_always_ok

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_static_store_outOfBounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_static_store_outOfBounds

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.evalRawMutStaticWrite_outOfBounds_exact' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.evalRawMutStaticWrite_outOfBounds_exact

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_staticPreserved_retag_then_store_full_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_staticPreserved_retag_then_store_full_iff

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.evalIntrinsicM_tb_wfLive_choiceFree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.evalIntrinsicM_tb_wfLive_choiceFree

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.evalReturnM_tb_wfLive_choiceFree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.evalReturnM_tb_wfLive_choiceFree

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.evalTerminatorM_tb_wfLive_choiceFree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.evalTerminatorM_tb_wfLive_choiceFree

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.stepTB_wfLive_choiceFree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.stepTB_wfLive_choiceFree

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.stepsTB_wfLive_choiceFree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.stepsTB_wfLive_choiceFree

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_staticAccess_steps_wfLive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_staticAccess_steps_wfLive

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_harnesses_steps_wfLive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_harnesses_steps_wfLive

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_part6_fullDomain_and_symbolic_machTB_wfLive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_part6_fullDomain_and_symbolic_machTB_wfLive

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.permAllowsDealloc_iff' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.permAllowsDealloc_iff

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_ok_iff_pointwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_ok_iff_pointwise

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.deallocAllowedBool_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.deallocAllowedBool_iff

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_precheck_ub' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_precheck_ub

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_ok_iff_full' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_deallocate_ok_iff_full

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_deallocate_exact_boundary' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_deallocate_exact_boundary

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.frameExitPruneInert_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.frameExitPruneInert_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.execFrameExitMiniRust_singleton_nodeMetaRel' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.execFrameExitMiniRust_singleton_nodeMetaRel

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.frameExitPruneInert_of_noNestedForeignAncestors' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.frameExitPruneInert_of_noNestedForeignAncestors

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_end_call_simulates_execFrameExitMiniRust_of_pruneInert' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_end_call_simulates_execFrameExitMiniRust_of_pruneInert

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_endCall_arbitraryDepth_simulation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_endCall_arbitraryDepth_simulation

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_foreign_write_kills_frozen_reader' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_foreign_write_kills_frozen_reader

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_foreign_read_preserves_frozen_reader' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_foreign_read_preserves_frozen_reader

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_frozen_reader_foreign_write_vs_read' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_frozen_reader_foreign_write_vs_read

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_nestedSplitAtMut_noWritable_vs_writable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_nestedSplitAtMut_noWritable_vs_writable

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.runMirWithParamMap_eq_runMirDirect_of_rustcNoWritable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.runMirWithParamMap_eq_runMirDirect_of_rustcNoWritable

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.runMirWithParamMap_fuel_mono' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.runMirWithParamMap_fuel_mono

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.trusted_stepMirFn_forgetStyle_separation_all_fuel' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.trusted_stepMirFn_forgetStyle_separation_all_fuel

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_store_misaligned_ub' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_store_misaligned_ub

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_staticPreserved_retag_then_store_iff_aligned_and_miri' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_staticPreserved_retag_then_store_iff_aligned_and_miri

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_static_store_alignment_boundary' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_static_store_alignment_boundary

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_pruneInert_deepTree_load_and_retag' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_pruneInert_deepTree_load_and_retag

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.pruneInert_necessary_separation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.pruneInert_necessary_separation

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.node_access_read_through_disabled_fails' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.node_access_read_through_disabled_fails

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_ptr_fnEntry_frozen_reader_noWritable_vs_writable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.tbm_retag_ptr_fnEntry_frozen_reader_noWritable_vs_writable

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.canary_retag_frozen_reader_noWritable_vs_writable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.canary_retag_frozen_reader_noWritable_vs_writable

end AxiomGuards

end MiniRustSpec.NoWritableAndStaticRetag
