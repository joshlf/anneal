/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.TreeBorrowsRel
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine

/-!
# End-to-End MIR Step Simulations for `LM-3.3`

Step-level Tree Borrows correspondence between Anneal's real MIR step
(`stepMirFn` executing `evalStmt` on a dereferencing statement) and the vendored
`lean-miri` one-location Tree Borrows access
(`Tree.NormalTreeState.performAccess`) on the `TreeBorrowsRel`-related tree
`basedNormalTree`.

Each theorem fixes a one-statement MIR body and quantifies over **all six**
permissions of the accessed borrow (both values of `conflicted`) and **both**
protector settings, covering the four access shapes of Miri's
`perform_access` dispatch at the MIR level:

* `sim_lm3_3_child_write_step`: `(*_2) = const 99` through the borrow itself;
* `sim_lm3_3_child_read_step`: `_0 = copy (*_2)` through the borrow itself;
* `sim_lm3_3_foreign_write_step`: `(*_3) = const 99` through an unrelated
  `*mut` tag, a foreign write for the borrow;
* `sim_lm3_3_foreign_read_step`: `_0 = copy (*_3)` through an unrelated shared
  tag, a foreign read for the borrow.

In every case the Anneal step succeeds exactly when Miri's tree access
completes, and then the successor borrow table is `TreeBorrowsRel`-related to
Miri's successor tree; otherwise Anneal faults with undefined behavior and
Miri reports a transition error (or, for a protected `ReservedIM`, its
invariant failure, which Anneal treats as undefined behavior).
-/

namespace LeanMiriSpec.Correspondence.SimLM3_3

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## Shared MIR scaffolding -/

/-- Statement with the `LM-3.3` witness span. -/
def stmt (k : StatementKind) : MirAst.Statement := { kind := k, span := "lm-3.3-witness" }

/-- Whole local `_i`. -/
def loc (i : Nat) : Place := { local_ := i, projection := [] }

/-- Dereferenced local `*_i`. -/
def deref (i : Nat) : Place := { local_ := i, projection := [.deref] }

/-- `u64` type. -/
def u64T : Ty := { kind := .uint .u64, layoutIdx := 0 }

/-- `u32` type. -/
def u32T : Ty := { kind := .uint .u32, layoutIdx := 0 }

/-- `core::cell::UnsafeCell<u32>` type (`!Freeze`). -/
def unsafeCellU32T : Ty :=
  { kind := .adt "core::cell::UnsafeCell" [.uint .u32], layoutIdx := 0 }

/-- Local declaration of type `ty`. -/
def declOf (ty : Ty) : LocalDecl := { mutability := .mut, ty := ty, debugName := none }

/-- `&mut T` declaration. -/
def refMutDecl (pointee : RigidTy) : LocalDecl :=
  declOf { kind := .ref .mut pointee, layoutIdx := 0 }

/-- `&T` declaration. -/
def refDecl (pointee : RigidTy) : LocalDecl :=
  declOf { kind := .ref .not pointee, layoutIdx := 0 }

/-- `*mut T` declaration. -/
def rawMutDecl (pointee : RigidTy) : LocalDecl :=
  declOf { kind := .rawPtr .mut pointee, layoutIdx := 0 }

/-- `u64` constant. -/
def cU64 (n : Nat) : Operand := .constant { ty := u64T, val := .scalar (.int ⟨n, 8⟩) }

/-- `u32` constant. -/
def cU32 (n : Nat) : Operand := .constant { ty := u32T, val := .scalar (.int ⟨n, 4⟩) }

/-- Scalar ABI layout of `bytes` bytes. -/
def scalarLayout (bytes : Nat) : TypeLayout :=
  { size := { bytes := bytes }
    align := { bytes := bytes }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Single-block witness body returning a `bytes`-byte scalar. -/
def witBody (name : String) (bytes : Nat) (decls : List LocalDecl)
    (stmts : List MirAst.Statement) : CapturedMir where
  defPath := name
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := decls
  basicBlocks := [
    { statements := stmts
      terminator := { kind := .return_, span := "lm-3.3-witness" }
      isCleanup := false }]
  fnAbi :=
    { args := []
      ret := { layout := scalarLayout bytes, mode := .direct }
      conv := .rust
      canUnwind := false }
  layouts := emptyLayoutTable
  allocations := []

/-- Initial machine state with the given locals and an empty borrow table. -/
def witInit (locals : List LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
    memory := emptyMemory }

/-- Borrow entry with tag `tag` on local `1`, permission `perm`, protector
`prot`, and parent `parent`. -/
def entry (tag : Nat) (perm : TreeBorrowPerm) (parent : Option Nat := none)
    (prot : Option Nat := none) : BorrowEntry :=
  { tag := tag, targetLocal := 1, targetProjection := [], perm := perm,
    protector := prot, parentTag := parent }


/-! ## Step-simulation outcome relation -/

/-- One Anneal MIR step and one `lean-miri` normal-tree access correspond when
either both succeed with `TreeBorrowsRel`-related successor states, or Anneal
faults with undefined behavior exactly when Miri's access does not complete. -/
def StepTreeRel (node : MirStepNode) (result : Miri.TreeBorrows.Tree.NormalAccessResult) :
    Prop :=
  (result.status = .Completed ∧
    ∃ s', node = .step s' ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors result.tree) ∨
  (result.status ≠ .Completed ∧ node = .fail .ub)

/-- Protector of the accessed borrow (`some 1` when protected). -/
def protOf (isProtected : Bool) : Option Nat :=
  match isProtected with
  | true => some 1
  | false => none

/-- Active protectors (`[1]` when protected). -/
def activeOf (isProtected : Bool) : List Nat :=
  match isProtected with
  | true => [1]
  | false => []

/-- Machine state with locals `locals`, borrow table `borrows`, and protector
`1` active when `isProtected`. -/
def simState (locals : List LocalSlot) (borrows : List BorrowEntry) (isProtected : Bool) :
    MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
    memory :=
      { emptyMemory with
        borrows := borrows
        nextTag := 3
        activeProtectors := activeOf isProtected
        nextProtector := 2 } }

/-! ## Child accesses through the borrow itself -/

/-- `(*_2) = const 99` with `_2 : &mut u64` pointing at `_1`. -/
def childWriteBody : CapturedMir :=
  witBody "lm_3_3_sim::child_write" 8
    [declOf u64T, declOf u64T, refMutDecl (.uint .u64)]
    [stmt (.assign (deref 2) (.use (cU64 99)))]

/-- `_0 = copy (*_2)` with `_2 : &u64` pointing at `_1`. -/
def childReadBody : CapturedMir :=
  witBody "lm_3_3_sim::child_read" 8
    [declOf u64T, declOf u64T, refDecl (.uint .u64)]
    [stmt (.assign (loc 0) (.use (.copy (deref 2))))]

/-- State with `_1 = 7`, `_2` holding tag `1` with permission `perm`. -/
def childState (perm : TreeBorrowPerm) (isProtected : Bool) : MachineState :=
  simState [.uninit, .init (.scalar ⟨7, 8⟩), .init (.ptr ⟨1, 0⟩ 8)]
    [entry 1 perm none (protOf isProtected)] isProtected

/-- **`sim_lm3_3_child_write_step`**: for every permission and protector
setting, Anneal's real step of `(*_2) = const 99` through tag `1` corresponds to
Miri's normal-tree write from node `0` (tag `1`). -/
theorem sim_lm3_3_child_write_step (perm : TreeBorrowPerm) (isProtected : Bool) :
    TreeBorrowsRel (childState perm isProtected).memory.borrows (activeOf isProtected)
      (basedNormalTree (childState perm isProtected).memory.borrows (activeOf isProtected)) ∧
    StepTreeRel (stepMirFn childWriteBody (childState perm isProtected))
      ((basedNormalTree (childState perm isProtected).memory.borrows
        (activeOf isProtected)).performAccess 0 .Write .VisitChildrenOfAccessed) := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases isProtected <;>
    refine ⟨⟨rfl, by decide, rfl, rfl, rfl⟩, ?_⟩ <;>
    first
    | exact Or.inl ⟨by decide, _, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩
    | exact Or.inr ⟨by decide, rfl⟩

/-- **`sim_lm3_3_child_read_step`**: for every permission and protector setting,
Anneal's real step of `_0 = copy (*_2)` through tag `1` corresponds to Miri's
normal-tree read from node `0` (tag `1`). -/
theorem sim_lm3_3_child_read_step (perm : TreeBorrowPerm) (isProtected : Bool) :
    StepTreeRel (stepMirFn childReadBody (childState perm isProtected))
      ((basedNormalTree (childState perm isProtected).memory.borrows
        (activeOf isProtected)).performAccess 0 .Read .VisitChildrenOfAccessed) := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases isProtected <;>
    first
    | exact Or.inl ⟨by decide, _, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩
    | exact Or.inr ⟨by decide, rfl⟩

/-! ## Foreign accesses through an unrelated tag -/

/-- `(*_3) = const 99` with `_3 : *mut u64` (tag `2`) pointing at `_1`. -/
def foreignWriteBody : CapturedMir :=
  witBody "lm_3_3_sim::foreign_write" 8
    [declOf u64T, declOf u64T, refMutDecl (.uint .u64), rawMutDecl (.uint .u64)]
    [stmt (.assign (deref 3) (.use (cU64 99)))]

/-- `_0 = copy (*_3)` with `_3 : &u64` (tag `2`) pointing at `_1`. -/
def foreignReadBody : CapturedMir :=
  witBody "lm_3_3_sim::foreign_read" 8
    [declOf u64T, declOf u64T, refMutDecl (.uint .u64), refDecl (.uint .u64)]
    [stmt (.assign (loc 0) (.use (.copy (deref 3))))]

/-- State with `_1 = 7`, `_2` holding tag `1` (permission `perm`), and `_3`
holding the unrelated root tag `2` with permission `other`. -/
def foreignState (perm other : TreeBorrowPerm) (isProtected : Bool) : MachineState :=
  simState [.uninit, .init (.scalar ⟨7, 8⟩), .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8)]
    [entry 2 other, entry 1 perm none (protOf isProtected)] isProtected

/-- **`sim_lm3_3_foreign_write_step`**: for every permission and protector
setting of tag `1`, Anneal's real step of a write through the unrelated `*mut`
tag `2` corresponds to Miri's normal-tree write from node `0` (tag `2`), which
is a foreign write for node `1` (tag `1`). -/
theorem sim_lm3_3_foreign_write_step (perm : TreeBorrowPerm) (isProtected : Bool) :
    TreeBorrowsRel (foreignState perm .unique isProtected).memory.borrows
      (activeOf isProtected)
      (basedNormalTree (foreignState perm .unique isProtected).memory.borrows
        (activeOf isProtected)) ∧
    StepTreeRel (stepMirFn foreignWriteBody (foreignState perm .unique isProtected))
      ((basedNormalTree (foreignState perm .unique isProtected).memory.borrows
        (activeOf isProtected)).performAccess 0 .Write .VisitChildrenOfAccessed) := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases isProtected <;>
    refine ⟨⟨rfl, by decide, rfl, rfl, rfl⟩, ?_⟩ <;>
    first
    | exact Or.inl ⟨by decide, _, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩
    | exact Or.inr ⟨by decide, rfl⟩

/-- **`sim_lm3_3_foreign_read_step`**: for every permission and protector
setting of tag `1`, Anneal's real step of a read through the unrelated shared
tag `2` corresponds to Miri's normal-tree read from node `0` (tag `2`), which is
a foreign read for node `1` (tag `1`): the protector latch, the protected
`Unique` disable, and the unprotected freeze all agree. -/
theorem sim_lm3_3_foreign_read_step (perm : TreeBorrowPerm) (isProtected : Bool) :
    StepTreeRel (stepMirFn foreignReadBody (foreignState perm .frozen isProtected))
      ((basedNormalTree (foreignState perm .frozen isProtected).memory.borrows
        (activeOf isProtected)).performAccess 0 .Read .VisitChildrenOfAccessed) := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases isProtected <;>
    first
    | exact Or.inl ⟨by decide, _, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩
    | exact Or.inr ⟨by decide, rfl⟩

/-! ## Parent-child reborrow hierarchy accesses (`I-10` & `I-11`) -/

/-- State with `_1 = 7`, `_2` holding parent root tag `1` (permission
`parentPerm`, unprotected), and `_3` holding child reborrow tag `2`
(`parentTag = some 1`, permission `childPerm`, protected iff `isProtected`). -/
def reborrowHierarchyState (parentPerm childPerm : TreeBorrowPerm)
    (isProtected : Bool) : MachineState :=
  simState [.uninit, .init (.scalar ⟨7, 8⟩), .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8)]
    [entry 2 childPerm (some 1) (protOf isProtected), entry 1 parentPerm none none]
    isProtected

/-- **`sim_lm3_3_reborrow_child_write_step`**: across all 6 parent permissions,
all 6 child permissions, and both child protector settings (`6 × 6 × 2 = 72`
combinations), Anneal's real step of `(*_3) = const 99` through the child
reborrow tag `2` (`parentTag = some 1`) corresponds via `StepTreeRel` to Miri's
normal-tree write from node `0` (tag `2`), which visits both the child node `0`
and its parent node `1` as `LocalAccess` writes. -/
theorem sim_lm3_3_reborrow_child_write_step
    (parentPerm childPerm : TreeBorrowPerm) (isProtected : Bool) :
    TreeBorrowsRel (reborrowHierarchyState parentPerm childPerm isProtected).memory.borrows
      (activeOf isProtected)
      (basedNormalTree (reborrowHierarchyState parentPerm childPerm isProtected).memory.borrows
        (activeOf isProtected)) ∧
    StepTreeRel
      (stepMirFn foreignWriteBody (reborrowHierarchyState parentPerm childPerm isProtected))
      ((basedNormalTree (reborrowHierarchyState parentPerm childPerm isProtected).memory.borrows
        (activeOf isProtected)).performAccess 0 .Write .VisitChildrenOfAccessed) := by
  rcases parentPerm with _ | (_ | _) | _ | _ | _ | _ <;>
    rcases childPerm with _ | (_ | _) | _ | _ | _ | _ <;>
    cases isProtected <;>
    refine ⟨⟨rfl, by decide, rfl, rfl, rfl⟩, ?_⟩ <;>
    first
    | exact Or.inl ⟨by decide, _, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩
    | exact Or.inr ⟨by decide, rfl⟩

/-- **`sim_lm3_3_reborrow_parent_write_invalidates_child_step`**: across all 6
child permissions and both child protector settings, Anneal's real step of
`(*_2) = const 99` through the parent tag `1` (`parentPerm = .unique`) in the
parent-child hierarchy corresponds via `StepTreeRel` to Miri's normal-tree write
from node `1` (tag `1`), which visits the parent node `1` as a `LocalAccess`
write and visits the child reborrow node `0` (tag `2`, `parentTag = some 1`) as
a `ForeignAccess` write. -/
theorem sim_lm3_3_reborrow_parent_write_invalidates_child_step
    (childPerm : TreeBorrowPerm) (isProtected : Bool) :
    StepTreeRel
      (stepMirFn childWriteBody (reborrowHierarchyState .unique childPerm isProtected))
      ((basedNormalTree (reborrowHierarchyState .unique childPerm isProtected).memory.borrows
        (activeOf isProtected)).performAccess 1 .Write .VisitChildrenOfAccessed) := by
  rcases childPerm with _ | (_ | _) | _ | _ | _ | _ <;>
    cases isProtected <;>
    first
    | exact Or.inl ⟨by decide, _, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩
    | exact Or.inr ⟨by decide, rfl⟩

/-! ## `StatementKind.retag` across all 4 `RetagKind`s & raw-pointer modes -/

/-- Pointee type for `retagRefBody`: `u32` (`Freeze`) when `frozen = true`,
`UnsafeCell<u32>` (`!Freeze`) when `frozen = false`. -/
def retagPointeeTy (frozen : Bool) : Ty :=
  if frozen then u32T else unsafeCellU32T

/-- `Retag(rk, _2)` where `_2` is a reference (`&mut T` or `&T`) to `_1`. -/
def retagRefBody (rk : RetagKind) (mutability : Mutability) (frozen : Bool) : CapturedMir :=
  witBody "lm_3_3_sim::retag_ref" 4
    [declOf u32T, declOf (retagPointeeTy frozen),
      declOf { kind := .ref mutability (retagPointeeTy frozen).kind, layoutIdx := 0 }]
    [stmt (.retag rk (loc 2))]

/-- Pre-retag state with `_1 = 7_u32`, `_2` holding parent tag `1` (`Unique`),
and a sibling `Unique` borrow tag `2` on `_1` that freezes to `Frozen` iff the
retag performs an initial child read (`childPerm ≠ .cell`). -/
def retagRefState : MachineState :=
  simState [.uninit, .init (.scalar ⟨7, 4⟩), .init (.ptr ⟨1, 0⟩ 8)]
    [entry 2 .unique, entry 1 .unique] false

/-- **`sim_lm3_3_retag_ref_step`**: across all `4 × 2 × 2 = 16` combinations of
`(rk, mutability, frozen)`, Anneal's real step of `StatementKind.retag rk _2` on
a reference `_2`:
1. allocates fresh child tag `3` under `parentTag = some 1` (`I-10`) with
   permission `annealRetagPerm (retagKindToAnnealMode rk) mutability frozen` and
   installs protector `2` iff `rk = .fnEntry`;
2. skips the initial child read (preserving the sibling `entry 2 .unique`) iff
   the new permission is `.cell` (`&UnsafeCell<u32>`, certifying `I-11`), and
   otherwise freezes sibling `entry 2` to `.frozen`;
3. updates `_2` to provenance tag `3` and preserves `TreeBorrowsRel` on the
   successor borrow table. -/
theorem sim_lm3_3_retag_ref_step
    (rk : RetagKind) (mutability : Mutability) (frozen : Bool) :
    let childPerm := annealRetagPerm (retagKindToAnnealMode rk) mutability frozen
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let siblingPerm := match childPerm with | .cell => TreeBorrowPerm.unique | _ => .frozen
    let activeProts := match rk with | .fnEntry => [2] | _ => []
    ∃ s' : MachineState,
      stepMirFn (retagRefBody rk mutability frozen) retagRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) childProt, entry 2 siblingPerm, entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors) := by
  cases rk <;> cases mutability <;> cases frozen <;>
    exact ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩

/-- `Retag(rk, _2)` where `_2` is a raw pointer (`*mut u64` or `*const u64`). -/
def retagRawBody (rk : RetagKind) (mutability : Mutability) : CapturedMir :=
  witBody "lm_3_3_sim::retag_raw" 8
    [declOf u64T, declOf u64T,
      declOf { kind := .rawPtr mutability (.uint .u64), layoutIdx := 0 }]
    [stmt (.retag rk (loc 2))]

/-- **`sim_lm3_3_retag_raw_step`**: across all `4` `RetagKind`s, both raw-pointer
mutabilities, all 6 permissions (including `.disabled`), and both protector
settings, `StatementKind.retag rk _2` on a raw pointer `_2` succeeds without
allocating a tag or failing on `.disabled` provenance when `rk = .raw`, and
faults with `.fail .ub` (`rawPointerWrongMode`) for every non-`.raw` mode,
matching `retagPointerValue_rawPointer_simulation`. -/
theorem sim_lm3_3_retag_raw_step
    (rk : RetagKind) (mutability : Mutability)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    match rk with
    | .raw =>
      ∃ s' : MachineState,
        stepMirFn (retagRawBody rk mutability) (childState perm isProtected) = .step s' ∧
        s'.memory = (childState perm isProtected).memory ∧
        get? s'.frame.locals 2 = some (.init (.ptr ⟨1, 0⟩ 8))
    | .default | .twoPhase | .fnEntry =>
      stepMirFn (retagRawBody rk mutability) (childState perm isProtected) = .fail .ub := by
  cases mutability <;> cases rk
  all_goals
    first
    | exact ⟨_, rfl, rfl, rfl⟩
    | rfl

/-- State where `_2` holds a provenance-free scalar raw pointer (`0 as *mut u64` /
`0 as *const u64`, `.scalar ⟨0, 8⟩`). -/
def childScalarRawState : MachineState :=
  simState [.uninit, .init (.scalar ⟨7, 8⟩), .init (.scalar ⟨0, 8⟩)] [] false

/-- **`sim_lm3_3_retag_raw_scalar_step`**: across all `4` `RetagKind`s and both
raw-pointer mutabilities, `StatementKind.retag rk _2` on a provenance-free
scalar raw pointer (`_2 = .scalar ⟨0, 8⟩`, e.g., `0 as *const u64`) steps cleanly
without allocating a tag when `rk = .raw`, and faults with `.fail .ub`
(`rawPointerWrongMode`) for every non-`.raw` mode, matching
`retagPointerValue_rawPointer_simulation`. -/
theorem sim_lm3_3_retag_raw_scalar_step
    (rk : RetagKind) (mutability : Mutability) :
    match rk with
    | .raw =>
      ∃ s' : MachineState,
        stepMirFn (retagRawBody rk mutability) childScalarRawState = .step s' ∧
        s'.memory = childScalarRawState.memory ∧
        get? s'.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩))
    | .default | .twoPhase | .fnEntry =>
      stepMirFn (retagRawBody rk mutability) childScalarRawState = .fail .ub := by
  cases mutability <;> cases rk
  all_goals
    first
    | exact ⟨_, rfl, rfl, rfl⟩
    | rfl

end LeanMiriSpec.Correspondence.SimLM3_3
