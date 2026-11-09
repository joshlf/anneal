/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM3_3

/-!
# Real-Step Tree Borrows Witnesses for `LM-3.3`

Concrete, kernel-checked executions of Anneal's real `stepMirFn` on small
`Runtime(PostCleanup)` MIR bodies, each paired with the vendored `lean-miri`
one-location Tree Borrows access (`Tree.NormalTreeState.performAccess`) on the
`TreeBorrowsRel`-related tree (`basedNormalTree`):

* (a) `wit_lm3_3_reborrow_hierarchy_real_steps`: a child write through a
  two-level reborrow activates `ReservedFrz false → Unique` on the writer and
  its ancestor and disables a frozen cousin; a later parent read freezes the
  child. Both sides complete and stay related.
* (b) `wit_lm3_3_protected_conflict_ub_real_steps`: a function-entry retag
  creates a protected `ReservedFrz false` child; a foreign read sets its
  `conflicted` latch; the child write through it is undefined behavior in both.
* (c) `wit_lm3_3_protected_unique_foreign_read_ub_real_steps`: a protected tag
  activated to `Unique` by a child write is disabled by a foreign read, which
  is immediate undefined behavior in both.
* (d) `wit_lm3_3_unsafe_cell_vs_freeze_real_steps`: `&UnsafeCell<u32>` gets
  `Cell`, survives a foreign write, and still permits a child read, whereas
  `&u32` gets `Frozen`, is disabled by the same foreign write, and the
  subsequent child read is undefined behavior in both (certifying `I-11`).
-/

namespace LeanMiriSpec.Correspondence.WitnessLM3_3

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence
open LeanMiriSpec.Correspondence.SimLM3_3

/-! ## (a) Multi-level reborrow hierarchy -/

/-- ```text
bb0: _2 = &mut _1;        // tag 1, ReservedFrz false
     _3 = &mut (*_2);     // tag 2, ReservedFrz false, parent 1
     _4 = &(*_2);         // tag 3, Frozen, parent 1 (cousin of tag 2)
     (*_3) = const 99;    // child write through tag 2
     _0 = copy (*_2);     // parent read through tag 1
     return
``` -/
def bodyA : CapturedMir :=
  witBody "lm_3_3_witness::reborrow_hierarchy" 8
    [declOf u64T, declOf u64T, refMutDecl (.uint .u64), refMutDecl (.uint .u64),
      refDecl (.uint .u64)]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.assign (loc 3) (.ref (.mut false) (deref 2))),
     stmt (.assign (loc 4) (.ref .shared (deref 2))),
     stmt (.assign (deref 3) (.use (cU64 99))),
     stmt (.assign (loc 0) (.use (.copy (deref 2))))]

/-- Initial state of `bodyA`: `_1 = 7_u64`. -/
def initA : MachineState :=
  witInit [.uninit, .init (.scalar ⟨7, 8⟩), .uninit, .uninit, .uninit]

/-- **(a) `wit_lm3_3_reborrow_hierarchy_real_steps`**: five real Anneal steps
of `bodyA` and the two corresponding `lean-miri` tree accesses:
1. `&mut _1` creates root tag `1` as `ReservedFrz false` (`.reserved`);
2. `&mut (*_2)` creates child tag `2` as `ReservedFrz false`;
3. `&(*_2)` creates the frozen cousin tag `3`;
4. the child write `(*_3) = 99` activates tags `2` and `1` to `Unique` and
   disables the cousin tag `3`; Miri's normal-tree write from node `1`
   (tag `2`) completes with the related tree;
5. the parent read `copy (*_2)` yields `99`, freezes tag `2`, and keeps tag `1`
   `Unique`; Miri's read from node `2` (tag `1`) completes with the related
   tree. -/
theorem wit_lm3_3_reborrow_hierarchy_real_steps :
    ∃ s₁ s₂ s₃ s₄ s₅ : MachineState,
      stepMirFn bodyA initA = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reserved] ∧
      stepMirFn bodyA s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .reserved (some 1), entry 1 .reserved] ∧
      stepMirFn bodyA s₂ = .step s₃ ∧
      s₃.memory.borrows =
        [entry 3 .frozen (some 1), entry 2 .reserved (some 1), entry 1 .reserved] ∧
      stepMirFn bodyA s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .disabled (some 1), entry 2 .unique (some 1), entry 1 .unique] ∧
      get? s₄.frame.locals 1 = some (.init (.scalar ⟨99, 8⟩)) ∧
      stepMirFn bodyA s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 3 .disabled (some 1), entry 2 .frozen (some 1), entry 1 .unique] ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      TreeBorrowsRel s₃.memory.borrows []
        (basedNormalTree s₃.memory.borrows []) ∧
      ((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₄.memory.borrows []
        ((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).tree.performAccess 2 .Read
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₅.memory.borrows []
        (((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).tree.performAccess 2 .Read
          .VisitChildrenOfAccessed).tree := by
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨rfl, by decide, rfl, rfl, rfl⟩, by decide, ⟨by decide, by decide, rfl, rfl, rfl⟩,
    by decide, ⟨by decide, by decide, rfl, rfl, rfl⟩⟩


/-! ## (b) Protected `ReservedFrz` conflict -/

/-- ```text
bb0: _2 = &mut _1;               // tag 1, ReservedFrz false
     Retag([fn entry] _2);       // tag 2, protected ReservedFrz false, parent 1
     _3 = &_1;                   // tag 3, Frozen (unrelated root borrow)
     _0 = copy (*_3);            // foreign read for tag 2: conflicted := true
     (*_2) = const 9;            // protected child write of a conflicted tag: UB
     return
``` -/
def bodyB : CapturedMir :=
  witBody "lm_3_3_witness::protected_conflict" 8
    [declOf u64T, declOf u64T, refMutDecl (.uint .u64), refDecl (.uint .u64)]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.retag .fnEntry (loc 2)),
     stmt (.assign (loc 3) (.ref .shared (loc 1))),
     stmt (.assign (loc 0) (.use (.copy (deref 3)))),
     stmt (.assign (deref 2) (.use (cU64 9)))]

/-- Initial state of `bodyB` and `bodyC`: `_1 = 5_u64`. -/
def initBC : MachineState :=
  witInit [.uninit, .init (.scalar ⟨5, 8⟩), .uninit, .uninit]

/-- **(b) `wit_lm3_3_protected_conflict_ub_real_steps`**: real Anneal steps of
`bodyB`:
1. `&mut _1` creates tag `1` (`ReservedFrz false`);
2. the function-entry retag creates the protected child tag `2`
   (`ReservedFrz false`, protector `1`), activates protector `1`, and stores
   tag `2` into `_2`;
3. `&_1` creates the unrelated frozen tag `3`;
4. the read through tag `3` is a foreign read for the protected tag `2`, which
   sets its `conflicted` latch (`ReservedFrz true`), as Miri's normal-tree read
   from node `0` does;
5. the child write through the protected, conflicted tag `2` is undefined
   behavior in Anneal (`.fail .ub`) and a transition error in Miri's
   normal-tree write from node `1`. -/
theorem wit_lm3_3_protected_conflict_ub_real_steps :
    ∃ s₁ s₂ s₃ s₄ : MachineState,
      stepMirFn bodyB initBC = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reserved] ∧
      stepMirFn bodyB s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      s₂.memory.activeProtectors = [1] ∧
      get? s₂.frame.locals 2 = some (.init (.ptr ⟨2, 0⟩ 8)) ∧
      stepMirFn bodyB s₂ = .step s₃ ∧
      s₃.memory.borrows =
        [entry 3 .frozen, entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      stepMirFn bodyB s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .frozen, entry 2 (.reservedFrz true) (some 1) (some 1), entry 1 .reserved] ∧
      get? s₄.frame.locals 0 = some (.init (.scalar ⟨5, 8⟩)) ∧
      stepMirFn bodyB s₄ = .fail .ub ∧
      TreeBorrowsRel s₃.memory.borrows [1] (basedNormalTree s₃.memory.borrows [1]) ∧
      ((basedNormalTree s₃.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₄.memory.borrows [1]
        ((basedNormalTree s₃.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₃.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).tree.performAccess 1 .Write
          .VisitChildrenOfAccessed).status =
        .TransitionError 1 (.ChildAccessForbidden (.ReservedFrz true)) := by
  refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨rfl, by decide, rfl, rfl, rfl⟩, by decide, ⟨by decide, by decide, rfl, rfl, rfl⟩,
    by decide⟩

/-! ## (c) Protected `Unique` foreign-read disable -/

/-- ```text
bb0: _2 = &mut _1;               // tag 1, ReservedFrz false
     Retag([fn entry] _2);       // tag 2, protected ReservedFrz false, parent 1
     (*_2) = const 9;            // child write: tags 2 and 1 become Unique
     _3 = &_1;                   // tag 3, Frozen (unrelated root borrow)
     _0 = copy (*_3);            // foreign read disables protected Unique: UB
     return
``` -/
def bodyC : CapturedMir :=
  witBody "lm_3_3_witness::protected_unique_foreign_read" 8
    [declOf u64T, declOf u64T, refMutDecl (.uint .u64), refDecl (.uint .u64)]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.retag .fnEntry (loc 2)),
     stmt (.assign (deref 2) (.use (cU64 9))),
     stmt (.assign (loc 3) (.ref .shared (loc 1))),
     stmt (.assign (loc 0) (.use (.copy (deref 3))))]

/-- **(c) `wit_lm3_3_protected_unique_foreign_read_ub_real_steps`**: real
Anneal steps of `bodyC`: after the function-entry retag, the child write
through the protected tag `2` activates it (and its ancestor tag `1`) to
`Unique`; a read through the unrelated tag `3` is then a foreign read that
would disable the protected `Unique` tag `2`, which is immediate undefined
behavior in Anneal (`.fail .ub`) and a `ProtectedDisabled` transition error in
Miri's normal-tree read from node `0`. -/
theorem wit_lm3_3_protected_unique_foreign_read_ub_real_steps :
    ∃ s₁ s₂ s₃ s₄ : MachineState,
      stepMirFn bodyC initBC = .step s₁ ∧
      stepMirFn bodyC s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      stepMirFn bodyC s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      get? s₃.frame.locals 1 = some (.init (.scalar ⟨9, 8⟩)) ∧
      stepMirFn bodyC s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .frozen, entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyC s₄ = .fail .ub ∧
      TreeBorrowsRel s₄.memory.borrows [1] (basedNormalTree s₄.memory.borrows [1]) ∧
      ((basedNormalTree s₄.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).status =
        .TransitionError 1 (.ProtectedDisabled .Unique) := by
  refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨rfl, by decide, rfl, rfl, rfl⟩, by decide⟩

/-! ## (d) `&UnsafeCell<u32>` (`Cell`) vs. `&u32` (`Frozen`) -/

/-- ```text
bb0: _2 = &_1;                   // tag 1: Cell for UnsafeCell<u32>, Frozen for u32
     _3 = &raw mut _1;           // tag 2: unrelated raw tag (Unique)
     (*_3) = const 7_u32;        // foreign write for tag 1
     _0 = copy (*_2);            // child read through tag 1
     return
``` -/
def bodyD (pointee : Ty) : CapturedMir :=
  witBody "lm_3_3_witness::unsafe_cell_vs_freeze" 4
    [declOf u32T, declOf pointee, refDecl pointee.kind, rawMutDecl pointee.kind]
    [stmt (.assign (loc 2) (.ref .shared (loc 1))),
     stmt (.assign (loc 3) (.rawPtr .mut (loc 1))),
     stmt (.assign (deref 3) (.use (cU32 7))),
     stmt (.assign (loc 0) (.use (.copy (deref 2))))]

/-- Initial state of `bodyD`: `_1` holds `5_u32`. -/
def initD : MachineState :=
  witInit [.uninit, .init (.scalar ⟨5, 4⟩), .uninit, .uninit]

/-- **(d) `wit_lm3_3_unsafe_cell_vs_freeze_real_steps`** (certifying `I-11`):
* for `_1 : UnsafeCell<u32>`, `&_1` creates a `Cell` tag; the foreign write
  through the raw tag leaves it `Cell` (in Anneal and in Miri's normal-tree
  write), and the child read through it succeeds with the new value `7` (and
  completes in Miri);
* for `_1 : u32`, `&_1` creates a `Frozen` tag; the same foreign write disables
  it in both, and the subsequent child read is undefined behavior in Anneal
  (`.fail .ub`) and a `ChildAccessForbidden Disabled` transition error in
  Miri. -/
theorem wit_lm3_3_unsafe_cell_vs_freeze_real_steps :
    (∃ s₁ s₂ s₃ s₄ : MachineState,
      stepMirFn (bodyD unsafeCellU32T) initD = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .cell] ∧
      stepMirFn (bodyD unsafeCellU32T) s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .unique, entry 1 .cell] ∧
      stepMirFn (bodyD unsafeCellU32T) s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique, entry 1 .cell] ∧
      stepMirFn (bodyD unsafeCellU32T) s₃ = .step s₄ ∧
      get? s₄.frame.locals 0 = some (.init (.scalar ⟨7, 4⟩)) ∧
      ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₃.memory.borrows []
        ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree.performAccess 1 .Read
          .VisitChildrenOfAccessed).status = .Completed) ∧
    (∃ s₁ s₂ s₃ : MachineState,
      stepMirFn (bodyD u32T) initD = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .frozen] ∧
      stepMirFn (bodyD u32T) s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .unique, entry 1 .frozen] ∧
      stepMirFn (bodyD u32T) s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique, entry 1 .disabled] ∧
      stepMirFn (bodyD u32T) s₃ = .fail .ub ∧
      ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₃.memory.borrows []
        ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree.performAccess 1 .Read
          .VisitChildrenOfAccessed).status =
        .TransitionError 1 (.ChildAccessForbidden .Disabled)) := by
  refine ⟨⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide,
      ⟨by decide, by decide, rfl, rfl, rfl⟩, by decide⟩,
    ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide,
      ⟨by decide, by decide, rfl, rfl, rfl⟩, by decide⟩⟩

/-! ## (e) `&mut UnsafeCell<u32>` (`ReservedIM`) lifecycle vs. `Cell` -/

/-- ```text
bb0: _2 = &mut _1;               // tag 1: ReservedIM for UnsafeCell<u32>
     _3 = &raw mut _1;           // tag 2: unrelated raw tag (Unique)
     (*_3) = const 10_u32;       // foreign write: ReservedIM survives!
     (*_2) = const 20_u32;       // child write: ReservedIM activates to Unique!
     _1 = const 30_u32;          // foreign write: Unique is now disabled!
     _0 = copy (*_2);            // child read through disabled tag 1 -> UB!
     return
``` -/
def bodyE : CapturedMir :=
  witBody "lm_3_3_witness::reserved_im_lifecycle" 4
    [declOf u32T, declOf unsafeCellU32T, refMutDecl unsafeCellU32T.kind,
      rawMutDecl unsafeCellU32T.kind]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.assign (loc 3) (.rawPtr .mut (loc 1))),
     stmt (.assign (deref 3) (.use (cU32 10))),
     stmt (.assign (deref 2) (.use (cU32 20))),
     stmt (.assign (loc 1) (.use (cU32 30))),
     stmt (.assign (loc 0) (.use (.copy (deref 2))))]

/-- **(e) `wit_lm3_3_reservedIM_lifecycle_real_steps`** (certifying the
separation between `ReservedIM` and `Cell`):
1. `_2 = &mut _1` on `_1 : UnsafeCell<u32>` creates tag `1` in `ReservedIM`
   (`.reservedIM`);
2. `_3 = &raw mut _1` creates tag `2` in `Unique`;
3. the foreign write `(*_3) = 10` leaves tag `1` in `ReservedIM` (surviving
   foreign writes before activation);
4. the child write `(*_2) = 20` activates tag `1` from `ReservedIM` to `Unique`
   (unlike `Cell`, which stays `Cell`);
5. once activated to `Unique`, a subsequent foreign write `_1 = 30` disables
   tag `1` to `Disabled`, and the later child read `copy (*_2)` is undefined
   behavior in Anneal (`.fail .ub`) and a `ChildAccessForbidden Disabled`
   transition error in Miri. -/
theorem wit_lm3_3_reservedIM_lifecycle_real_steps :
    ∃ s₁ s₂ s₃ s₄ s₅ : MachineState,
      stepMirFn bodyE initD = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reservedIM] ∧
      stepMirFn bodyE s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .unique, entry 1 .reservedIM] ∧
      stepMirFn bodyE s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique, entry 1 .reservedIM] ∧
      get? s₃.frame.locals 1 = some (.init (.scalar ⟨10, 4⟩)) ∧
      stepMirFn bodyE s₃ = .step s₄ ∧
      s₄.memory.borrows = [entry 2 .disabled, entry 1 .unique] ∧
      get? s₄.frame.locals 1 = some (.init (.scalar ⟨20, 4⟩)) ∧
      stepMirFn bodyE s₄ = .step s₅ ∧
      s₅.memory.borrows = [entry 2 .disabled, entry 1 .disabled] ∧
      stepMirFn bodyE s₅ = .fail .ub ∧
      ((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₄.memory.borrows []
        ((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).tree ∧
      ((basedNormalTree s₅.memory.borrows []).performAccess 1 .Read
          .VisitChildrenOfAccessed).status =
        .TransitionError 1 (.ChildAccessForbidden .Disabled) := by
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, by decide, ⟨by decide, by decide, rfl, rfl, rfl⟩, by decide⟩

/-! ## (f) Shared deref reborrow `&(*_2)` of `UnsafeCell<u32>` (`Cell`) skips initial read -/

/-- ```text
bb0: _2 = &_1;                   // tag 1: Cell
     _3 = &mut _1;               // tag 2: ReservedIM
     (*_3) = const 42_u32;       // child write: tag 2 activates to Unique, tag 1 stays Cell
     _4 = &(*_2);                // tag 3: Cell reborrow (parent 1) — NO initial read!
     (*_3) = const 99_u32;       // child write through tag 2 still succeeds (stayed Unique)!
     return
``` -/
def bodyF : CapturedMir :=
  witBody "lm_3_3_witness::cell_reborrow_preserves_unique" 4
    [declOf u32T, declOf unsafeCellU32T, refDecl unsafeCellU32T.kind,
      refMutDecl unsafeCellU32T.kind, refDecl unsafeCellU32T.kind]
    [stmt (.assign (loc 2) (.ref .shared (loc 1))),
     stmt (.assign (loc 3) (.ref (.mut false) (loc 1))),
     stmt (.assign (deref 3) (.use (cU32 42))),
     stmt (.assign (loc 4) (.ref .shared (deref 2))),
     stmt (.assign (deref 3) (.use (cU32 99)))]

/-- Initial state of `bodyF`: `_1 = 5_u32`. -/
def initF : MachineState :=
  witInit [.uninit, .init (.scalar ⟨5, 4⟩), .uninit, .uninit, .uninit]

/-- **(f) `wit_lm3_3_cell_reborrow_preserves_unique_real_steps`**:
shared deref reborrow `_4 = &(*_2)` on `_2 : &UnsafeCell<u32>` assigns
permission `.cell` to the new child tag `3` (`parentTag = some 1`) and performs
no initial child read (`Permission.Cell.associatedAccess = none`), so the
sibling `Unique` tag `2` is not frozen to `Frozen` and still permits subsequent
writes `(*_3) = 99_u32`. -/
theorem wit_lm3_3_cell_reborrow_preserves_unique_real_steps :
    ∃ s₁ s₂ s₃ s₄ s₅ : MachineState,
      stepMirFn bodyF initF = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .cell] ∧
      stepMirFn bodyF s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .reservedIM, entry 1 .cell] ∧
      stepMirFn bodyF s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique, entry 1 .cell] ∧
      stepMirFn bodyF s₃ = .step s₄ ∧
      s₄.memory.borrows = [entry 3 .cell (some 1), entry 2 .unique, entry 1 .cell] ∧
      stepMirFn bodyF s₄ = .step s₅ ∧
      s₅.memory.borrows = [entry 3 .cell (some 1), entry 2 .unique, entry 1 .cell] ∧
      get? s₅.frame.locals 1 = some (.init (.scalar ⟨99, 4⟩)) := by
  exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## (g) Protector release on `TerminatorKind.return_` allows conflicted `ReservedFrz true` activation -/

/-- Callee body that performs `Retag([fn entry] _2)`, triggers a foreign read
that sets `conflicted := true` on protected tag `2` (`ReservedFrz true`), and
then executes `TerminatorKind.return_` to release protector `1`. -/
def calleeG : CapturedMir :=
  witBody "lm_3_3_witness::callee_release_protector" 8
    [declOf u64T, declOf u64T, refMutDecl (.uint .u64), refDecl (.uint .u64)]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.retag .fnEntry (loc 2)),
     stmt (.assign (loc 3) (.ref .shared (loc 1))),
     stmt (.assign (loc 0) (.use (.copy (deref 3))))]

/-- Caller body resumed after `calleeG` returns: writes `(*_2) = const 9_u64`
through the now-unprotected conflicted tag `2` (`ReservedFrz true → Unique`). -/
def callerG : CapturedMir :=
  witBody "lm_3_3_witness::caller_after_protector_release" 8
    [declOf u64T, declOf u64T, refMutDecl (.uint .u64)]
    [stmt (.assign (deref 2) (.use (cU64 9)))]

/-- Initial state inside `calleeG` with `callerG` on `callStack` waiting at
`bb0` with `_2` holding tag `2` (`&mut _1`). -/
def initG : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨5, 8⟩), .uninit, .uninit] }
    memory :=
      { emptyMemory with
        callStack :=
          [{ callerBody := callerG
             frame :=
               { blockIdx := 0
                 stmtIdx := 0
                 locals := [.uninit, .init (.scalar ⟨5, 8⟩), .init (.ptr ⟨2, 0⟩ 8)] }
             destination := loc 0
             returnTarget := 0
             callerProtector := none
             calleeProtectors := [] }]
        activeCallee := some calleeG } }

/-- **(g) `wit_lm3_3_protector_release_on_return_real_steps`**:
contrasting directly with `wit_lm3_3_protected_conflict_ub_real_steps` (`bodyB`),
where writing through a conflicted `ReservedFrz true` tag while its protector is
active faults with `.fail .ub`:
1. inside `calleeG`, `_2 = &mut _1` creates root tag `1` (`ReservedFrz false`),
   `Retag([fn entry] _2)` creates protected child tag `2` (`ReservedFrz false`,
   `protector = some 1`, `activeProtectors = [1]`), `_3 = &_1` creates shared
   tag `3` (`Frozen`), and `_0 = copy (*_3)` performs a foreign read that sets
   `conflicted := true` on tag `2` (`ReservedFrz true`);
2. executing `TerminatorKind.return_` at the end of `calleeG` returns to
   `callerG` and releases protector `1` (`activeProtectors = []`);
3. in `callerG`, the subsequent child write `(*_2) = const 9_u64` through tag `2`
   now **succeeds** and activates tag `2` (from `ReservedFrz true`) and parent
   tag `1` (from `ReservedFrz false`) to `Unique` while disabling tag `3`, in
   lockstep with Miri's normal-tree write on `basedNormalTree s₅.memory.borrows []`. -/
theorem wit_lm3_3_protector_release_on_return_real_steps :
    ∃ s₁ s₂ s₃ s₄ s₅ s₆ : MachineState,
      stepMirFn callerG initG = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reserved] ∧
      stepMirFn callerG s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      s₂.memory.activeProtectors = [1] ∧
      stepMirFn callerG s₂ = .step s₃ ∧
      s₃.memory.borrows =
        [entry 3 .frozen, entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      stepMirFn callerG s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .frozen, entry 2 (.reservedFrz true) (some 1) (some 1), entry 1 .reserved] ∧
      s₄.memory.activeProtectors = [1] ∧
      stepMirFn callerG s₄ = .step s₅ ∧
      s₅.memory.activeProtectors = [] ∧
      s₅.memory.borrows =
        [entry 3 .frozen, entry 2 (.reservedFrz true) (some 1) (some 1), entry 1 .reserved] ∧
      stepMirFn callerG s₅ = .step s₆ ∧
      s₆.memory.borrows =
        [entry 3 .disabled, entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      get? s₆.frame.locals 1 = some (.init (.scalar ⟨9, 8⟩)) ∧
      ((basedNormalTree s₅.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₆.memory.borrows []
        ((basedNormalTree s₅.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).tree := by
  refine ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, by decide, ⟨by decide, by decide, rfl, rfl, rfl⟩⟩

/-! ## (h) Non-`fnEntry` reference retags (`Default`, `TwoPhase`) and `Raw` scalar pointer retag -/

/-- ```text
bb0: _2 = &mut _1;               // tag 1: ReservedFrz false
     Retag([default] _2);        // tag 2: ReservedFrz false, parent 1, unprotected
     Retag([2phase] _2);         // tag 3: ReservedFrz false, parent 2, unprotected
     Retag([raw] _3);            // raw scalar pointer 0 as *mut u64: no-op, no tag allocated
     (*_2) = const 77_u64;       // child write through tag 3: activates 3, 2, 1 to Unique!
     return
``` -/
def bodyH : CapturedMir :=
  witBody "lm_3_3_witness::non_fn_entry_and_raw_retag" 8
    [declOf u64T, declOf u64T, refMutDecl (.uint .u64), rawMutDecl (.uint .u64)]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.retag .default (loc 2)),
     stmt (.retag .twoPhase (loc 2)),
     stmt (.retag .raw (loc 3)),
     stmt (.assign (deref 2) (.use (cU64 77)))]

/-- Initial state of `bodyH`: `_1 = 5_u64` and `_3 = 0 as *mut u64`
(provenance-free scalar raw pointer). -/
def initH : MachineState :=
  witInit [.uninit, .init (.scalar ⟨5, 8⟩), .uninit, .init (.scalar ⟨0, 8⟩)]

/-- **(h) `wit_lm3_3_non_fnEntry_retag_and_raw_retag_real_steps`**:
real Anneal steps of `bodyH` exercising `StatementKind.retag` across `.default`,
`.twoPhase`, and `.raw`:
1. `_2 = &mut _1` creates root tag `1` (`ReservedFrz false`);
2. `Retag([default] _2)` allocates unprotected child tag `2` (`ReservedFrz false`,
   `parentTag = some 1`);
3. `Retag([2phase] _2)` allocates unprotected grandchild tag `3`
   (`ReservedFrz false`, `parentTag = some 2`);
4. `Retag([raw] _3)` on provenance-free scalar raw pointer `_3 = .scalar ⟨0, 8⟩`
   steps cleanly without allocating a tag (`nextTag` remains `4`);
5. `(*_2) = const 77_u64` writes through grandchild tag `3`, activating the
   3-level chain (`tag 3`, `tag 2`, `tag 1`) to `Unique` in lockstep with Miri's
   normal-tree write on `basedNormalTree s₄.memory.borrows []`. -/
theorem wit_lm3_3_non_fnEntry_retag_and_raw_retag_real_steps :
    ∃ s₁ s₂ s₃ s₄ s₅ : MachineState,
      stepMirFn bodyH initH = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reserved] ∧
      stepMirFn bodyH s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .reserved (some 1), entry 1 .reserved] ∧
      s₂.memory.activeProtectors = [] ∧
      stepMirFn bodyH s₂ = .step s₃ ∧
      s₃.memory.borrows =
        [entry 3 .reserved (some 2), entry 2 .reserved (some 1), entry 1 .reserved] ∧
      s₃.memory.nextTag = 4 ∧
      stepMirFn bodyH s₃ = .step s₄ ∧
      s₄.memory.borrows = s₃.memory.borrows ∧
      s₄.memory.nextTag = 4 ∧
      stepMirFn bodyH s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 3 .unique (some 2), entry 2 .unique (some 1), entry 1 .unique] ∧
      get? s₅.frame.locals 1 = some (.init (.scalar ⟨77, 8⟩)) ∧
      ((basedNormalTree s₄.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₅.memory.borrows []
        ((basedNormalTree s₄.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree := by
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, by decide, ⟨by decide, by decide, rfl, rfl, rfl⟩⟩

end LeanMiriSpec.Correspondence.WitnessLM3_3
