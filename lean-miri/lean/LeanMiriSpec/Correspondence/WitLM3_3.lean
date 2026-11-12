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
* (e) `wit_lm3_3_reservedIM_lifecycle_real_steps`: `&mut UnsafeCell<u32>` starts
  in `ReservedIM`, survives foreign writes before activation, activates to
  `Unique` on child write, and is disabled by subsequent foreign writes.
* (f) `wit_lm3_3_cell_reborrow_preserves_unique_real_steps`: shared deref
  reborrow `&(*_2)` on `&UnsafeCell<u32>` creates `Cell` without performing an
  initial read, preserving a sibling `Unique` borrow.
* (g) `wit_lm3_3_protector_release_on_return_real_steps`: `TerminatorKind.return_`
  releases active function-entry protectors so a conflicted `ReservedFrz true`
  borrow can subsequently activate to `Unique` in the caller.
* (h) `wit_lm3_3_non_fnEntry_retag_and_raw_retag_real_steps`: `Retag([default])`,
  `Retag([2phase])`, and `Retag([raw])` on a provenance-free scalar raw pointer,
  followed by 3-level ancestor activation.
* (i) `wit_lm3_3_zst_retag_skips_read_and_dangling_scalar_real_steps`:
  `Retag([fn entry])` on zero-sized `&()` skips the 0-byte initial read (so a
  protected `Unique` sibling survives without UB), and `Retag([default])` on a
  non-null provenance-free dangling `&()` steps cleanly while null `&()` faults
  with `.fail .ub`.
* (j) `wit_lm3_3_subprojection_disjoint_vs_overlapping_real_steps`: borrowing
  disjoint tuple fields `&mut (_1.0)` and `&(_1.1)` with a function-entry
  protector on `_1.1` allows writing through `&mut (_1.0)` without disabling or
  conflicting with the protected borrow of `_1.1`, whereas borrowing the
  overlapping field `&(_1.0)` causes the write to fault with `.fail .ub`.
* (k) `wit_lm3_3_zst_deref_reborrow_and_phantom_retag_real_steps`: a shared
  deref reborrow `_4 = &(*_3)` on `_3 : &mut ()` and a function-entry retag on
  `&PhantomData<u64>` both skip the 0-byte initial child read via
  `placeIsZeroSized` / `rigidTyIsZeroSized`, preserving a protected `Unique`
  sibling without UB.
* (l) `wit_lm3_3_uninhabited_ref_retag_ub_vs_inhabited_never_zst_real_steps`:
  retagging inhabited zero-sized `[!; 0]` and `PhantomData<!>` references
  succeeds cleanly (`rigidTyIsUninhabited = false`), whereas retagging
  uninhabited `&!` and `&[!; 1]` references (both provenance pointers and
  non-null dangling scalars) immediately faults with `.fail .ub`.
* (m) `wit_lm3_3_protected_cell_chain_under_disabled_root_real_steps`: a
  3-level interior-mutability chain `[g, c, r]` (`g` protected `Cell`, `c`
  `Cell`, `r` `Unique`) where a foreign write disables `r` while `c` and
  protected `g` survive as `Cell` (`borrowListChain3ProtInv = true` while
  unprotected `treeBorrowsChain3Inv = false`), subsequent foreign writes skip
  `r`'s subtree in lockstep (`SkipSelfAndChildren`), and a child read through
  `g` faults in both engines due to its `.disabled` ancestor `r`.
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

/-! ## (i) Zero-sized `&()` retag skips initial read + provenance-free dangling `&()` -/

/-- ```text
bb0: _2 = &mut _1;               // tag 1: ReservedFrz false on _1 : ()
     Retag([fn entry] _2);       // tag 2: protected ReservedFrz false, parent 1
     (*_2) = copy _1;            // child write activates tags 2 & 1 to Unique (tag 2 protected!)
     _3 = &_1;                   // tag 3: Frozen on _1 : ()
     Retag([fn entry] _3);       // tag 4: protected Frozen, parent 3 — 0-byte ZST skips read!
     Retag([default] _4);        // _4 : &() = 0x8 (non-null dangling ZST ref) -> steps cleanly!
     return
``` -/
def bodyI : CapturedMir :=
  witBody "lm_3_3_witness::zst_retag_and_dangling_scalar" 0
    [declOf { kind := .tuple [], layoutIdx := 0 },
      declOf { kind := .tuple [], layoutIdx := 0 },
      refMutDecl (.tuple []),
      refDecl (.tuple []), refDecl (.tuple [])]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.retag .fnEntry (loc 2)),
     stmt (.assign (deref 2) (.use (.copy (loc 1)))),
     stmt (.assign (loc 3) (.ref .shared (loc 1))),
     stmt (.retag .fnEntry (loc 3)),
     stmt (.retag .default (loc 4))]

/-- Initial state of `bodyI` with `_1 = ()` and `_4 = 0x8 as &()` (non-null
provenance-free dangling ZST reference, e.g. `NonNull::<()>::dangling().as_ref()`). -/
def initI : MachineState :=
  witInit [.uninit, .init .unit, .uninit, .uninit, .init (.scalar ⟨8, 8⟩)]

/-- Null-reference variant of `initI` at `stmtIdx = 5` (`_4 = 0x0 as &()`). -/
def initINullAt5 : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 5
        locals := [.uninit, .init .unit, .uninit, .uninit, .init (.scalar ⟨0, 8⟩)] }
    memory := emptyMemory }

/-- **(i) `wit_lm3_3_zst_retag_skips_read_and_dangling_scalar_real_steps`**:
1. `_2 = &mut _1`, `Retag([fn entry] _2)`, and `(*_2) = copy _1` activate
   protected child tag `2` (`protector = some 1`, `activeProtectors = [1]`) and
   parent tag `1` to `Unique` on `_1 : ()`;
2. `_3 = &_1` creates shared `Frozen` tag `3`, and `Retag([fn entry] _3)`
   allocates protected `Frozen` child tag `4` (`parentTag = some 3`,
   `protector = some 2`) while **skipping** the 0-byte initial child read — so
   the protected `Unique` sibling tag `2` survives untouched without triggering
   `ProtectedDisabled` UB (contrasting with 8-byte `bodyC`);
3. `Retag([default] _4)` on the non-null provenance-free scalar ZST reference
   `_4 = .scalar ⟨8, 8⟩` steps cleanly without allocating a tag (`nextTag = 5`),
   whereas a null scalar ZST reference (`initINullAt5`, `_4 = .scalar ⟨0, 8⟩`)
   faults with `.fail .ub`. -/
theorem wit_lm3_3_zst_retag_skips_read_and_dangling_scalar_real_steps :
    (∃ s₁ s₂ s₃ s₄ s₅ s₆ : MachineState,
      stepMirFn bodyI initI = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reserved] ∧
      stepMirFn bodyI s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      stepMirFn bodyI s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyI s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .frozen, entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyI s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 4 .frozen (some 3) (some 2),
          entry 3 .frozen,
          entry 2 .unique (some 1) (some 1),
          entry 1 .unique] ∧
      s₅.memory.activeProtectors = [2, 1] ∧
      s₅.memory.nextTag = 5 ∧
      stepMirFn bodyI s₅ = .step s₆ ∧
      s₆.memory = s₅.memory ∧
      TreeBorrowsRel s₆.memory.borrows s₆.memory.activeProtectors
        (basedNormalTree s₆.memory.borrows s₆.memory.activeProtectors)) ∧
    stepMirFn bodyI initINullAt5 = .fail .ub := by
  refine ⟨⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, ⟨by decide, by decide, rfl, rfl, rfl⟩⟩, rfl⟩

/-! ## (j) Disjoint vs. overlapping sub-place projections (`&mut (_1.0)` vs. `&(_1.1)` / `&(_1.0)`) -/

/-- `(u64, u64)` tuple type. -/
def tupleU64U64T : Ty :=
  { kind := .tuple [.uint .u64, .uint .u64], layoutIdx := 0 }

/-- Field projection `_(localIdx).(fieldIdx)` of type `u64`. -/
def fieldU64 (localIdx fieldIdx : Nat) : Place :=
  { local_ := localIdx, projection := [.field fieldIdx u64T] }

/-- `BorrowEntry` on `_1` at projection `proj`. -/
def entryProj (tag : Nat) (perm : TreeBorrowPerm) (proj : List ProjectionElem)
    (parentTag : Option Nat := none) (protector : Option Nat := none) : BorrowEntry :=
  { tag := tag
    targetLocal := 1
    targetProjection := proj
    perm := perm
    protector := protector
    parentTag := parentTag }

/-- Disjoint-field witness body:
```text
bb0: _2 = &mut (_1.0);           // tag 1: ReservedFrz false at [.field 0 u64T]
     _3 = &(_1.1);               // tag 2: Frozen at [.field 1 u64T]
     Retag([fn entry] _3);       // tag 3: protected Frozen at [.field 1 u64T], parent 2
     (*_2) = const 99_u64;       // writes _1.0: activates tag 1 to Unique, leaves tags 2 & 3 Frozen!
     _0 = copy (*_3);            // reads _1.1 = 20_u64 through protected tag 3!
     return
``` -/
def bodyJDisjoint : CapturedMir :=
  witBody "lm_3_3_witness::subproj_disjoint" 8
    [declOf u64T, declOf tupleU64U64T, refMutDecl (.uint .u64), refDecl (.uint .u64)]
    [stmt (.assign (loc 2) (.ref (.mut false) (fieldU64 1 0))),
     stmt (.assign (loc 3) (.ref .shared (fieldU64 1 1))),
     stmt (.retag .fnEntry (loc 3)),
     stmt (.assign (deref 2) (.use (cU64 99))),
     stmt (.assign (loc 0) (.use (.copy (deref 3))))]

/-- Overlapping-field witness body (borrowing `_1.0` instead of `_1.1`):
```text
bb0: _2 = &mut (_1.0);           // tag 1: ReservedFrz false at [.field 0 u64T]
     _3 = &(_1.0);               // tag 2: Frozen at [.field 0 u64T]
     Retag([fn entry] _3);       // tag 3: protected Frozen at [.field 0 u64T], parent 2
     (*_2) = const 99_u64;       // writes _1.0 while overlapping tag 3 is protected Frozen -> UB!
     return
``` -/
def bodyJOverlap : CapturedMir :=
  witBody "lm_3_3_witness::subproj_overlap" 8
    [declOf u64T, declOf tupleU64U64T, refMutDecl (.uint .u64), refDecl (.uint .u64)]
    [stmt (.assign (loc 2) (.ref (.mut false) (fieldU64 1 0))),
     stmt (.assign (loc 3) (.ref .shared (fieldU64 1 0))),
     stmt (.retag .fnEntry (loc 3)),
     stmt (.assign (deref 2) (.use (cU64 99)))]

/-- Initial state for `bodyJDisjoint` and `bodyJOverlap`: `_1 = (10_u64, 20_u64)`. -/
def initJ : MachineState :=
  witInit
    [.uninit,
     .init (.aggregate 0 [.scalar ⟨10, 8⟩, .scalar ⟨20, 8⟩]),
     .uninit,
     .uninit]

/-- **(j) `wit_lm3_3_subprojection_disjoint_vs_overlapping_real_steps`**:
contrasts disjoint vs. overlapping tuple-field borrows under an active
function-entry protector:
1. In `bodyJDisjoint`, `_2 = &mut (_1.0)` (`tag 1` at `[.field 0 u64T]`) and
   `Retag([fn entry] _3)` on `_3 = &(_1.1)` (`tag 3` protected `Frozen` at
   `[.field 1 u64T]`, `activeProtectors = [1]`) target disjoint projections
   (`borrowEntryOverlapsWrite = false`), so writing `(*_2) = 99` activates
   `tag 1` to `Unique` while leaving `tag 2` and protected `tag 3` untouched as
   `Frozen`, and `_0 = copy (*_3)` reads `20_u64`.
2. In `bodyJOverlap`, `_3 = &(_1.0)` borrows the same field `[.field 0 u64T]`;
   after `Retag([fn entry] _3)` protects `tag 3` on `_1.0`, the write
   `(*_2) = 99` faults with `.fail .ub` (`hasProtectedTreeWriteConflict = true`). -/
theorem wit_lm3_3_subprojection_disjoint_vs_overlapping_real_steps :
    (∃ s₁ s₂ s₃ s₄ s₅ : MachineState,
      stepMirFn bodyJDisjoint initJ = .step s₁ ∧
      s₁.memory.borrows = [entryProj 1 .reserved [.field 0 u64T]] ∧
      stepMirFn bodyJDisjoint s₁ = .step s₂ ∧
      s₂.memory.borrows =
        [entryProj 2 .frozen [.field 1 u64T],
         entryProj 1 .reserved [.field 0 u64T]] ∧
      stepMirFn bodyJDisjoint s₂ = .step s₃ ∧
      s₃.memory.borrows =
        [entryProj 3 .frozen [.field 1 u64T] (some 2) (some 1),
         entryProj 2 .frozen [.field 1 u64T],
         entryProj 1 .reserved [.field 0 u64T]] ∧
      s₃.memory.activeProtectors = [1] ∧
      stepMirFn bodyJDisjoint s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entryProj 3 .frozen [.field 1 u64T] (some 2) (some 1),
         entryProj 2 .frozen [.field 1 u64T],
         entryProj 1 .unique [.field 0 u64T]] ∧
      get? s₄.frame.locals 1 =
        some (.init (.aggregate 0 [.scalar ⟨99, 8⟩, .scalar ⟨20, 8⟩])) ∧
      stepMirFn bodyJDisjoint s₄ = .step s₅ ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨20, 8⟩))) ∧
    (∃ o₁ o₂ o₃ : MachineState,
      stepMirFn bodyJOverlap initJ = .step o₁ ∧
      stepMirFn bodyJOverlap o₁ = .step o₂ ∧
      stepMirFn bodyJOverlap o₂ = .step o₃ ∧
      o₃.memory.borrows =
        [entryProj 3 .frozen [.field 0 u64T] (some 2) (some 1),
         entryProj 2 .frozen [.field 0 u64T],
         entryProj 1 (.reservedFrz false) [.field 0 u64T]] ∧
      stepMirFn bodyJOverlap o₃ = .fail .ub) := by
  refine ⟨⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## (k) ZST deref reborrow `&(*_3)` and `PhantomData<u64>` retag skip initial reads -/

/-- ```text
bb0: _2 = &mut _1;               // tag 1: ReservedFrz false on _1 : ()
     Retag([fn entry] _2);       // tag 2: protected ReservedFrz false, parent 1
     (*_2) = copy _1;            // child write activates tags 2 & 1 to Unique (tag 2 protected!)
     _3 = &mut _1;               // tag 3: ReservedFrz false sibling on _1 : ()
     _4 = &(*_3);                // tag 4: Frozen, parent 3 — ZST deref reborrow skips read!
     _6 = &_5;                   // tag 5: Frozen on _5 : PhantomData<u64>
     Retag([fn entry] _6);       // tag 6: protected Frozen, parent 5 — PhantomData skips read!
     return
``` -/
def bodyK : CapturedMir :=
  witBody "lm_3_3_witness::zst_deref_reborrow_and_phantom" 8
    [declOf unitT, declOf unitT,
      refMutDecl (.tuple []), refMutDecl (.tuple []), refDecl (.tuple []),
      declOf phantomU64T, refDecl phantomU64T.kind]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.retag .fnEntry (loc 2)),
     stmt (.assign (deref 2) (.use (.copy (loc 1)))),
     stmt (.assign (loc 3) (.ref (.mut false) (loc 1))),
     stmt (.assign (loc 4) (.ref .shared (deref 3))),
     stmt (.assign (loc 6) (.ref .shared (loc 5))),
     stmt (.retag .fnEntry (loc 6))]

/-- Initial state of `bodyK` with `_1 = ()` and `_5 = PhantomData<u64>`. -/
def initK : MachineState :=
  witInit [.uninit, .init .unit, .uninit, .uninit, .uninit, .init .unit, .uninit]

/-- **(k) `wit_lm3_3_zst_deref_reborrow_and_phantom_retag_real_steps`**:
1. `_2 = &mut _1`, `Retag([fn entry] _2)`, and `(*_2) = copy _1` activate
   protected child tag `2` (`protector = some 1`, `activeProtectors = [1]`) and
   parent tag `1` to `Unique` on `_1 : ()` (even when `layouts[0]` has size `8`,
   via structural `placeIsZeroSized`);
2. `_3 = &mut _1` creates sibling `ReservedFrz false` tag `3`, and the shared
   deref reborrow `_4 = &(*_3)` allocates `Frozen` child tag `4`
   (`parentTag = some 3`) while **skipping** the 0-byte initial child read via
   `placeIsZeroSized`, so protected `Unique` sibling `tag 2` survives untouched
   without triggering `ProtectedDisabled` UB;
3. `_6 = &_5` and `Retag([fn entry] _6)` on `_5 : core::marker::PhantomData<u64>`
   allocate `Frozen` tag `5` and protected `Frozen` child tag `6`
   (`parentTag = some 5`, `protector = some 2`), also skipping the 0-byte
   initial child read via `rigidTyIsZeroSized` on `PhantomData`. -/
theorem wit_lm3_3_zst_deref_reborrow_and_phantom_retag_real_steps :
    ∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇ : MachineState,
      stepMirFn bodyK initK = .step s₁ ∧
      stepMirFn bodyK s₁ = .step s₂ ∧
      stepMirFn bodyK s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyK s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .reserved, entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyK s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 4 .frozen (some 3),
         entry 3 .reserved,
         entry 2 .unique (some 1) (some 1),
         entry 1 .unique] ∧
      stepMirFn bodyK s₅ = .step s₆ ∧
      stepMirFn bodyK s₆ = .step s₇ ∧
      s₇.memory.borrows =
        [{ tag := 6, targetLocal := 5, targetProjection := .nil, perm := .frozen,
           protector := some 2, parentTag := some 5 },
         { tag := 5, targetLocal := 5, targetProjection := .nil, perm := .frozen,
           protector := none, parentTag := none },
         entry 4 .frozen (some 3),
         entry 3 .reserved,
         entry 2 .unique (some 1) (some 1),
         entry 1 .unique] ∧
      s₇.memory.activeProtectors = [2, 1] ∧
      TreeBorrowsRel s₇.memory.borrows s₇.memory.activeProtectors
        (basedNormalTree s₇.memory.borrows s₇.memory.activeProtectors) := by
  refine ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, ⟨by decide, by decide, rfl, rfl, rfl⟩⟩

/-! ## (l) Uninhabited reference retag UB (`&!`, `&[!; 1]`) vs. inhabited `[!; 0]` / `PhantomData<!>` -/

/-- Inhabited zero-sized never-container witness body:
```text
bb0: _2 = &_1;                   // tag 1: Frozen on _1 : [!; 0]
     Retag([fn entry] _2);       // tag 2: protected Frozen, parent 1 — inhabited ZST!
     Retag([default] _3);        // _3 : &PhantomData<!> = 0x8 — inhabited ZST dangling!
     return
``` -/
def bodyLInhabited : CapturedMir :=
  witBody "lm_3_3_witness::inhabited_never_zst" 0
    [declOf unitT,
      declOf { kind := .array .never 0, layoutIdx := 0 },
      refDecl (.array .never 0),
      refDecl (.adt "core::marker::PhantomData" [.never])]
    [stmt (.assign (loc 2) (.ref .shared (loc 1))),
     stmt (.retag .fnEntry (loc 2)),
     stmt (.retag .default (loc 3))]

/-- Initial state for `bodyLInhabited`: `_1 = []` (`.aggregate 0 []`) and
`_3 = 0x8 as &PhantomData<!>`. -/
def initLInhabited : MachineState :=
  witInit [.uninit, .init (.aggregate 0 []), .uninit, .init (.scalar ⟨8, 8⟩)]

/-- Uninhabited `&!` retag body (`Retag([fn entry] _2)` on `_2 : &!`). -/
def bodyLNever : CapturedMir :=
  witBody "lm_3_3_witness::uninhabited_never_ref" 0
    [declOf unitT, declOf { kind := .never, layoutIdx := 0 }, refDecl .never]
    [stmt (.retag .fnEntry (loc 2))]

/-- Uninhabited `&[!; 1]` retag body (`Retag([default] _2)` on `_2 : &[!; 1]`). -/
def bodyLNeverArr1 : CapturedMir :=
  witBody "lm_3_3_witness::uninhabited_never_arr1_ref" 0
    [declOf unitT,
      declOf { kind := .array .never 1, layoutIdx := 0 },
      refDecl (.array .never 1)]
    [stmt (.retag .default (loc 2))]

/-- State for `bodyLNever` / `bodyLNeverArr1` with either provenance pointer
(`useScalar = false`) or non-null aligned dangling scalar `0x8`
(`useScalar = true`). -/
def initLUninhabited (useScalar : Bool) : MachineState :=
  simState
    [.uninit, .init .unit,
      .init (if useScalar then .scalar ⟨8, 8⟩ else .ptr ⟨1, 0⟩ 8)]
    [entry 1 .frozen] false

/-- **(l) `wit_lm3_3_uninhabited_ref_retag_ub_vs_inhabited_never_zst_real_steps`**:
1. In `bodyLInhabited`, `_1 : [!; 0]` and `_3 : &PhantomData<!>` have inhabited
   zero-sized pointees (`rigidTyIsUninhabited 16 = false`), so `_2 = &_1`,
   `Retag([fn entry] _2)`, and `Retag([default] _3)` all step cleanly and
   establish `TreeBorrowsRel`;
2. In `bodyLNever` (`&!`) and `bodyLNeverArr1` (`&[!; 1]`), the pointees are
   uninhabited (`rigidTyIsUninhabited 16 = true`), so `Retag` immediately
   faults with `.fail .ub` for **both** provenance pointers (`.ptr ⟨1, 0⟩ 8`)
   and non-null dangling scalars (`.scalar ⟨8, 8⟩`). -/
theorem wit_lm3_3_uninhabited_ref_retag_ub_vs_inhabited_never_zst_real_steps :
    (∃ s₁ s₂ s₃ : MachineState,
      stepMirFn bodyLInhabited initLInhabited = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .frozen] ∧
      stepMirFn bodyLInhabited s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .frozen (some 1) (some 1), entry 1 .frozen] ∧
      s₂.memory.activeProtectors = [1] ∧
      stepMirFn bodyLInhabited s₂ = .step s₃ ∧
      s₃.memory = s₂.memory ∧
      TreeBorrowsRel s₃.memory.borrows s₃.memory.activeProtectors
        (basedNormalTree s₃.memory.borrows s₃.memory.activeProtectors)) ∧
    stepMirFn bodyLNever (initLUninhabited false) = .fail .ub ∧
    stepMirFn bodyLNever (initLUninhabited true) = .fail .ub ∧
    stepMirFn bodyLNeverArr1 (initLUninhabited false) = .fail .ub ∧
    stepMirFn bodyLNeverArr1 (initLUninhabited true) = .fail .ub := by
  refine ⟨⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨by decide, by decide, rfl, rfl, rfl⟩⟩, rfl, rfl, rfl, rfl⟩

/-! ## (m) Protected `Cell` 3-level chain surviving under a `.disabled` root (`I-10` & `I-11`) -/

/-- ```text
bb0: _2 = &mut _1;               // tag 1 (root r): ReservedIM on _1 : UnsafeCell<u32>
     (*_2) = const 10_u32;       // child write activates tag 1 -> Unique
     _3 = &(*_2);                // tag 2 (child c): Cell, parent 1
     Retag([fn entry] _3);       // tag 3 (grandchild g): protected Cell, parent 2, prot 1
     _1 = const 55_u32;          // foreign write: disables tag 1; tags 2 & 3 survive as Cell!
     _1 = const 88_u32;          // 2nd foreign write: Miri SkipSelfAndChildren on disabled r!
     _0 = copy (*_3);            // child read via g: UB because ancestor tag 1 is Disabled!
     return
``` -/
def bodyM : CapturedMir :=
  witBody "lm_3_3_witness::protected_cell_chain_under_disabled_root" 4
    [declOf u32T, declOf unsafeCellU32T,
      refMutDecl unsafeCellU32T.kind, refDecl unsafeCellU32T.kind]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.assign (deref 2) (.use (cU32 10))),
     stmt (.assign (loc 3) (.ref .shared (deref 2))),
     stmt (.retag .fnEntry (loc 3)),
     stmt (.assign (loc 1) (.use (cU32 55))),
     stmt (.assign (loc 1) (.use (cU32 88))),
     stmt (.assign (loc 0) (.use (.copy (deref 3))))]

/-- Initial state of `bodyM`: `_1 = 1_u32`. -/
def initM : MachineState :=
  witInit [.uninit, .init (.scalar ⟨1, 4⟩), .uninit, .uninit]

/-- **(m) `wit_lm3_3_protected_cell_chain_under_disabled_root_real_steps`**:
1. Builds the 3-level chain `[entry 3 .cell (some 2) (some 1), entry 2 .cell (some 1),
   entry 1 .unique]` with `activeProtectors = [1]` (`borrowListChain3ProtInv = true`);
2. Executes `_1 = const 55_u32` (foreign write): disables unprotected root
   `entry 1` (`.unique → .disabled`) while `entry 2` (`.cell`) and protected
   `entry 3` (`.cell`, `protector = some 1`) survive untouched (`I-11`),
   yielding `[.cell (prot), .cell, .disabled]` where unprotected
   `treeBorrowsChain3Inv .cell .cell .disabled = false` yet inductive
   `borrowListChain3ProtInv s₅.memory.borrows [1] = true`;
3. Executes a second foreign write `_1 = const 88_u32` where Miri's
   `SkipSelfAndChildren` prunes `.disabled` root `entry 1` in lockstep with
   Anneal (`Completed` + `TreeBorrowsRel` + `borrowListChain3ProtInv = true`);
4. Confirms that a subsequent child read `_0 = copy (*_3)` through `entry 3`
   faults with `.fail .ub` in Anneal and `.TransitionError 2 (.ChildAccessForbidden .Disabled)`
   in Miri because ancestor `entry 1` at node `2` is `.disabled` (`I-10`). -/
theorem wit_lm3_3_protected_cell_chain_under_disabled_root_real_steps :
    ∃ s₁ s₂ s₃ s₄ s₅ s₆ : MachineState,
      stepMirFn bodyM initM = .step s₁ ∧
      stepMirFn bodyM s₁ = .step s₂ ∧
      stepMirFn bodyM s₂ = .step s₃ ∧
      stepMirFn bodyM s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .cell (some 2) (some 1), entry 2 .cell (some 1), entry 1 .unique] ∧
      s₄.memory.activeProtectors = [1] ∧
      borrowListChain3ProtInv s₄.memory.borrows [1] = true ∧
      stepMirFn bodyM s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 3 .cell (some 2) (some 1), entry 2 .cell (some 1), entry 1 .disabled] ∧
      treeBorrowsChain3Inv .cell .cell .disabled = false ∧
      borrowListChain3ProtInv s₅.memory.borrows [1] = true ∧
      ((basedNormalTree s₄.memory.borrows [1]).performAccess 3 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₅.memory.borrows [1]
        ((basedNormalTree s₄.memory.borrows [1]).performAccess 3 .Write
          .VisitChildrenOfAccessed).tree ∧
      stepMirFn bodyM s₅ = .step s₆ ∧
      s₆.memory.borrows = s₅.memory.borrows ∧
      ((basedNormalTree s₅.memory.borrows [1]).performAccess 3 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₆.memory.borrows [1]
        ((basedNormalTree s₅.memory.borrows [1]).performAccess 3 .Write
          .VisitChildrenOfAccessed).tree ∧
      stepMirFn bodyM s₆ = .fail .ub ∧
      ((basedNormalTree s₆.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).status =
        .TransitionError 2 (.ChildAccessForbidden .Disabled) := by
  refine ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide,
    rfl, rfl, rfl, by decide, by decide, ⟨by decide, by decide, rfl, rfl, rfl⟩,
    rfl, rfl, by decide, ⟨by decide, by decide, rfl, rfl, rfl⟩,
    rfl, by decide⟩

/-! ## (n) Transparent wrapper ZST (`UnsafeCell<()>`), `PhantomData<UnsafeCell<u32>>` `Freeze`, `Cell<u32>` `!Freeze`, and uninhabited `&UnsafeCell<!>` -/

/-- `core::cell::UnsafeCell<()>` (`!Freeze` and 0-byte ZST). -/
def unsafeCellUnitT : Ty :=
  { kind := .adt "core::cell::UnsafeCell" [.tuple []], layoutIdx := 0 }

/-- `core::marker::PhantomData<core::cell::UnsafeCell<u32>>` (`Freeze` and 0-byte ZST). -/
def phantomUnsafeCellU32T : Ty :=
  { kind := .adt "core::marker::PhantomData" [.adt "core::cell::UnsafeCell" [.uint .u32]],
    layoutIdx := 0 }

/-- `core::cell::Cell<u32>` (`!Freeze` even though `u32` is `Freeze`). -/
def cellU32T : Ty :=
  { kind := .adt "core::cell::Cell" [.uint .u32], layoutIdx := 0 }

/-- Witness body exercising `&mut UnsafeCell<()>` ZST retag (`ReservedIM`
skipping 0-byte read), `&PhantomData<UnsafeCell<u32>>` (`Frozen`), and
`&Cell<u32>` (`Cell` surviving foreign writes):
```text
bb0: _2 = &mut _1;               // tag 1: ReservedIM on _1 : UnsafeCell<()>
     Retag([fn entry] _2);       // tag 2: protected ReservedFrz false, parent 1 (skips ZST read)
     (*_2) = copy _1;            // child write activates tags 2 & 1 to Unique (tag 2 protected!)
     _3 = &mut _1;               // tag 3: ReservedIM sibling on _1 : UnsafeCell<()>
     Retag([default] _3);        // tag 4: ReservedIM child of 3 — skips ZST read so tag 2 survives!
     _5 = &_4;                   // tag 5: Frozen on _4 : PhantomData<UnsafeCell<u32>> (Freeze!)
     _7 = &_6;                   // tag 6: Cell on _6 : Cell<u32> (!Freeze!)
     _6 = const 99_u32;          // foreign write to _6: tag 6 survives as Cell!
     return
``` -/
def bodyN : CapturedMir :=
  witBody "lm_3_3_witness::wrapper_zst_freeze_and_cell" 4
    [declOf u32T,
      declOf unsafeCellUnitT,
      refMutDecl unsafeCellUnitT.kind,
      refMutDecl unsafeCellUnitT.kind,
      declOf phantomUnsafeCellU32T,
      refDecl phantomUnsafeCellU32T.kind,
      declOf cellU32T,
      refDecl cellU32T.kind]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.retag .fnEntry (loc 2)),
     stmt (.assign (deref 2) (.use (.copy (loc 1)))),
     stmt (.assign (loc 3) (.ref (.mut false) (loc 1))),
     stmt (.retag .default (loc 3)),
     stmt (.assign (loc 5) (.ref .shared (loc 4))),
     stmt (.assign (loc 7) (.ref .shared (loc 6))),
     stmt (.assign (loc 6) (.use (cU32 99)))]

/-- Initial state for `bodyN`. -/
def initN : MachineState :=
  witInit
    [.uninit, .init .unit, .uninit, .uninit,
     .init .unit, .uninit, .init (.scalar ⟨7, 4⟩), .uninit]

/-- Uninhabited `&UnsafeCell<!>` retag body (`Retag([fn entry] _2)` on
`_2 : &UnsafeCell<!>`). -/
def bodyNUnsafeCellNever : CapturedMir :=
  witBody "lm_3_3_witness::uninhabited_unsafecell_never_ref" 0
    [declOf unitT,
      declOf { kind := .adt "core::cell::UnsafeCell" [.never], layoutIdx := 0 },
      refDecl (.adt "core::cell::UnsafeCell" [.never])]
    [stmt (.retag .fnEntry (loc 2))]

/-- Uninhabited `&RefCell<!>` retag body (`Retag([fn entry] _2)` on
`_2 : &RefCell<!>`). -/
def bodyNRefCellNever : CapturedMir :=
  witBody "lm_3_3_witness::uninhabited_refcell_never_ref" 0
    [declOf unitT,
      declOf { kind := .adt "core::cell::RefCell" [.never], layoutIdx := 0 },
      refDecl (.adt "core::cell::RefCell" [.never])]
    [stmt (.retag .fnEntry (loc 2))]

/-- **(n) `wit_lm3_3_wrapper_zst_freeze_and_uninhabited_cell_real_steps`**:
1. On `_1 : UnsafeCell<()>`, `_2 = &mut _1`, `Retag([fn entry] _2)`, and
   `(*_2) = copy _1` activate protected `tag 2` (`protector = some 1`) and
   `tag 1` to `Unique`; then `_3 = &mut _1` (`tag 3`, `ReservedIM`) and
   `Retag([default] _3)` (`tag 4`, `ReservedIM`, `parentTag = some 3`) skip the
   0-byte initial child read via `rigidTyIsZeroSized` on `UnsafeCell<()>`, so
   protected `Unique` sibling `tag 2` survives without `ProtectedDisabled` UB;
2. On `_4 : PhantomData<UnsafeCell<u32>>`, `_5 = &_4` allocates `tag 5` with
   permission `.frozen` (`PhantomData<T>` is unconditionally `Freeze`);
3. On `_6 : Cell<u32>`, `_7 = &_6` allocates `tag 6` with permission `.cell`
   (`Cell<T>` is `!Freeze`), which survives the foreign write `_6 = 99_u32`;
4. On `bodyNUnsafeCellNever` (`_2 : &UnsafeCell<!>`) and `bodyNRefCellNever`
   (`_2 : &RefCell<!>`), `Retag([fn entry] _2)` immediately faults with
   `.fail .ub` for both provenance pointers and dangling scalars
   (`rigidTyIsUninhabited 16 = true`). -/
theorem wit_lm3_3_wrapper_zst_freeze_and_uninhabited_cell_real_steps :
    (∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ : MachineState,
      stepMirFn bodyN initN = .step s₁ ∧
      stepMirFn bodyN s₁ = .step s₂ ∧
      stepMirFn bodyN s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyN s₃ = .step s₄ ∧
      stepMirFn bodyN s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 4 .reservedIM (some 3),
         entry 3 .reservedIM,
         entry 2 .unique (some 1) (some 1),
         entry 1 .unique] ∧
      stepMirFn bodyN s₅ = .step s₆ ∧
      stepMirFn bodyN s₆ = .step s₇ ∧
      stepMirFn bodyN s₇ = .step s₈ ∧
      s₈.memory.borrows =
        [{ tag := 6, targetLocal := 6, targetProjection := .nil, perm := .cell,
           protector := none, parentTag := none },
         { tag := 5, targetLocal := 4, targetProjection := .nil, perm := .frozen,
           protector := none, parentTag := none },
         entry 4 .reservedIM (some 3),
         entry 3 .reservedIM,
         entry 2 .unique (some 1) (some 1),
         entry 1 .unique] ∧
      TreeBorrowsRel s₈.memory.borrows s₈.memory.activeProtectors
        (basedNormalTree s₈.memory.borrows s₈.memory.activeProtectors)) ∧
    stepMirFn bodyNUnsafeCellNever (initLUninhabited false) = .fail .ub ∧
    stepMirFn bodyNUnsafeCellNever (initLUninhabited true) = .fail .ub ∧
    stepMirFn bodyNRefCellNever (initLUninhabited false) = .fail .ub ∧
    stepMirFn bodyNRefCellNever (initLUninhabited true) = .fail .ub := by
  refine ⟨⟨_, _, _, _, _, _, _, _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨by decide, by decide, rfl, rfl, rfl⟩⟩, rfl, rfl, rfl, rfl⟩

/-! ## (o) Stage-1 `StorageDead` / `StorageLive` Protected Local Borrow UB vs. Unprotected Local Borrow Disable -/

/-- Protected `StorageDead(_1)` witness body:
```text
bb0: _2 = &mut _1;               // tag 1: ReservedFrz false on _1 : u32
     Retag([fn entry] _2);       // tag 2: protected ReservedFrz false (protector = some 1)
     StorageDead(_1);            // UB! _1 has an active protected borrow (tag 2)
     return
``` -/
def bodyOProtectedStorageDead : CapturedMir :=
  witBody "lm_3_3_witness::protected_storage_dead_ub" 4
    [declOf u32T, declOf u32T, refMutDecl (.uint .u32)]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.retag .fnEntry (loc 2)),
     stmt (.storageDead 1)]

/-- Unprotected `StorageDead(_1)` + use-after-`StorageDead` witness body:
```text
bb0: _2 = &mut _1;               // tag 1: ReservedFrz false on _1 : u32
     (*_2) = const 42_u32;       // child write activates tag 1 -> Unique
     StorageDead(_1);            // disables tag 1 -> Disabled (no active protector)
     _0 = copy (*_2);            // UB! deref read through disabled tag 1
     return
``` -/
def bodyOUnprotectedStorageDead : CapturedMir :=
  witBody "lm_3_3_witness::unprotected_storage_dead_disable" 4
    [declOf u32T, declOf u32T, refMutDecl (.uint .u32)]
    [stmt (.assign (loc 2) (.ref (.mut false) (loc 1))),
     stmt (.assign (deref 2) (.use (cU32 42))),
     stmt (.storageDead 1),
     stmt (.assign (loc 0) (.use (.copy (deref 2))))]

/-- Initial state for `bodyOProtectedStorageDead` and `bodyOUnprotectedStorageDead`. -/
def initO : MachineState :=
  witInit [.uninit, .init (.scalar ⟨7, 4⟩), .uninit]

/-- **(o) `wit_lm3_3_storageDead_protected_ub_vs_unprotected_disable_real_steps`**:
1. In `bodyOProtectedStorageDead`, `_2 = &mut _1` and `Retag([fn entry] _2)`
   create protected `tag 2` (`protector = some 1`, `activeProtectors = [1]`);
   then `StorageDead(_1)` immediately faults with `.fail .ub`
   (`hasProtectedLocalBorrow = true`), matching Miri's
   `BorrowTree.deallocateBorrowRange` failure (`.ProtectedDealloc ⟨0, 8⟩ ⟨1⟩`);
2. In `bodyOUnprotectedStorageDead`, `_2 = &mut _1` and `(*_2) = const 42_u32`
   activate unprotected `tag 1` to `.unique`; then `StorageDead(_1)` steps
   cleanly and disables `tag 1` (`s₃.memory.borrows = [entry 1 .disabled]`,
   satisfying `TreeBorrowsRel`), after which `_0 = copy (*_2)` faults with
   `.fail .ub` in Anneal and `.TransitionError 0 (.ChildAccessForbidden .Disabled)`
   in Miri. -/
theorem wit_lm3_3_storageDead_protected_ub_vs_unprotected_disable_real_steps :
    (∃ s₁ s₂ : MachineState,
      stepMirFn bodyOProtectedStorageDead initO = .step s₁ ∧
      stepMirFn bodyOProtectedStorageDead s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 (.reservedFrz false)] ∧
      s₂.memory.activeProtectors = [1] ∧
      stepMirFn bodyOProtectedStorageDead s₂ = .fail .ub ∧
      (∃ err,
        ((hooksTwoNodeTree (.reservedFrz false)).deallocateBorrowRange
          (.concrete (hooksAccessTag .foreignAccess))
          Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
          (hooksForChildProtected true).protectedTags).status =
            .AccessFailure err)) ∧
    (∃ s₁ s₂ s₃ : MachineState,
      stepMirFn bodyOUnprotectedStorageDead initO = .step s₁ ∧
      stepMirFn bodyOUnprotectedStorageDead s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 1 .unique] ∧
      stepMirFn bodyOUnprotectedStorageDead s₂ = .step s₃ ∧
      get? s₃.frame.locals 1 = some .dead ∧
      s₃.memory.borrows = [entry 1 .disabled] ∧
      TreeBorrowsRel s₃.memory.borrows [] (basedNormalTree s₃.memory.borrows []) ∧
      stepMirFn bodyOUnprotectedStorageDead s₃ = .fail .ub ∧
      ((basedNormalTree s₃.memory.borrows []).performAccess 0 .Read
        .VisitChildrenOfAccessed).status =
          .TransitionError 0 (.ChildAccessForbidden .Disabled)) := by
  refine ⟨⟨_, _, rfl, rfl, rfl, rfl, rfl,
      (borrowTree_deallocateBorrowRange_simulation .foreignAccess (.reservedFrz false) true).1 rfl⟩,
    ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ⟨by decide, by decide, rfl, rfl, rfl⟩, rfl, by decide⟩⟩

end LeanMiriSpec.Correspondence.WitnessLM3_3
