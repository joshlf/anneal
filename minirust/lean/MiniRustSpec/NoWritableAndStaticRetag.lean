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
(Parts 2A and 2B) and `Trusted.Rustc.V2026_06_01.MirSemantics` directly to the
mechanically generated MiniRust Tree Borrows specification (`MiniRustSpec.Gen`,
`MiniRustSpec.Interp`, and `MiniRustSpec.Correspondence.MachTB.wfLive`):

1. **Part 1 (`charon#1619` + `minirust#295`)**:
   - Exact bijection (`permToMiniRust` / `permFromMiniRust`) between Anneal's
     `TreeBorrowPerm` + `(isProtected, accessed)` and MiniRust's
     `Gen.Permission` (`PermissionUnprot` / `PermissionProt`), including the
     protected-`ReservedIM` invariant exclusion, exact `PermissionProt.unprotect`
     vs. `protectorEndAccessIsWriteMiniRust?` agreement, and full lockstep
     single-node simulation for `stepNodeOnRangeRead` / `stepNodeOnRangeWrite`
     vs. `Permission.transition`.
   - Universal policy correspondence relating `selectFnEntryPolicy`,
     `MiriRetagPolicyMirror.create`, and `Trusted.fnEntryRetagPerm` to
     MiniRust's `ReborrowSettings.new` across `&T`, `&mut T`, `Box<T>`,
     `!Unpin` skip-retag (`pinned_mutable_or_box_fnEntry_skips_retag`),
     `Protected::Weak` vs. `Protected::Strong`, and zero-sized `&mut ()`.
   - Two-sided `TBM` / `MachTB` (`stepsTB` + `MachTB.wfLive`) + `Trusted`
     (`stepMirFn` + `evalFnEntryRetagWithParamMap`) + `FnEntryBorrowWorld`
     separation between `#[rustc_no_writable]` (`core::mem::forget`,
     `<[T]>::get_mut`) and standard `&mut` `FnEntry` retags, plus multi-parameter
     disjoint-range frame-exit agreement (`execFrameExit_miri_eq_miniRust_of_disjointFrame`
     and `TreeBorrowsMemory.end_call`).

2. **Part 2 (`charon#1620`)**:
   - General symbolic byte-level equivalence between `StaticTyDesc` /
     `staticFreezeSegments` / `byteInNonZeroUnsafeCell` / `retagStaticPreservedAt`
     / `evalRawMutStaticWriteMiri` and MiniRust's `cellsToFreezeMask` /
     `UnsafeCellStrategy.freeze_mask` / `ReborrowSettings.new` for arbitrary
     disjoint in-bounds `UnsafeCell` layouts in any field declaration order.
   - End-to-end `TBM`, `MachTB` (`stepsTB` + `MachTB.wfLive`), and
     `ExtTreeMapAllocAndNoWritable` correspondence and separation across all
     four canonical static shapes:
     (a) pure `Freeze` (`static S: u32`),
     (b) pure `!Freeze` (`static S: AtomicI32` / `UnsafeCell<u32>`),
     (c) non-ZST mixed composite (`static S: (u8, Padding[3], AtomicI32)`,
         including out-of-offset-order `repr(Rust)` field declarations), and
     (d) zero-sized `UnsafeCell<()>` composite (`static S: (u8, UnsafeCell<()>)`).

3. **Part 3 (Closed Non-Vacuity Canaries & Axiom Pins)**:
   - Zero-hypothesis canary theorems exercising all positive and negative cases.
   - `#guard_msgs (whitespace := lax) in #print axioms` pins confirming every
     major theorem uses at most `{propext, Quot.sound}` (`0` `Classical.choice`,
     `0` `sorryAx`, `0` `Lean.ofReduceBool`).
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

/-! ## Part 3: Closed Non-Vacuity Canaries & `#guard_msgs in #print axioms` Pins -/

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

section AxiomGuards

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.nodeWf_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.nodeWf_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.machTB_steps_ok_and_wfLive_of_bool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.machTB_steps_ok_and_wfLive_of_bool

/--
info: 'MiniRustSpec.NoWritableAndStaticRetag.permToMiniRust_fromMiniRust' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms MiniRustSpec.NoWritableAndStaticRetag.permToMiniRust_fromMiniRust

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

end AxiomGuards

end MiniRustSpec.NoWritableAndStaticRetag
