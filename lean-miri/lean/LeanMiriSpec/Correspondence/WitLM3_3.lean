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

end LeanMiriSpec.Correspondence.WitnessLM3_3
