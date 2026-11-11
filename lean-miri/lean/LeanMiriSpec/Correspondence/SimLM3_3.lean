/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM3_2
import LeanMiriSpec.Correspondence.TreeBorrowsRel
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine

/-!
# End-to-End MIR Step Simulations for `LM-3.3`

Step-level Tree Borrows correspondence between Anneal's real MIR step
(`stepMirFn` executing `evalStmt`) and the vendored `lean-miri` Tree Borrows and
MIR interpreter engines (`Tree.NormalTreeState.performAccess` and
`Miri.Interpreter.Step.step`):

* `sim_lm3_3_child_write_step`, `sim_lm3_3_child_read_step`,
  `sim_lm3_3_foreign_write_step`, `sim_lm3_3_foreign_read_step`: exhaustive
  6-state × protector step simulations across all four `perform_access` shapes;
* `sim_lm3_3_reborrow_child_write_step` and
  `sim_lm3_3_reborrow_parent_write_invalidates_child_step`: exhaustive `6 × 6 × 2`
  parent-child hierarchy simulations certifying `I-10` and `I-11`;
* `sim_lm3_3_retag_ref_step`, `sim_lm3_3_retag_raw_step`,
  `sim_lm3_3_retag_raw_scalar_step`, `sim_lm3_3_retag_zst_ref_step`,
  `sim_lm3_3_retag_zst_scalar_step`, `sim_lm3_3_retag_phantom_ref_step`, and
  `sim_lm3_3_zst_deref_reborrow_step`: `StatementKind.retag` and deref-reborrow
  simulations across all 4 `RetagKind`s, `Freeze` vs. `!Freeze` (`UnsafeCell`),
  raw pointers, and ZST references (`()` and `PhantomData<u64>`, certifying
  skipped initial reads across both `retag` and `Rvalue.ref` deref reborrows
  plus provenance-free scalar ZSTs);
* `stateRelLM3_2Tree_treeBorrowsRel`,
  `sim_lm3_3_interpreter_deref_read_step`,
  `sim_lm3_3_interpreter_deref_write_step`, and
  `sim_lm3_3_interpreter_reborrow_step`: general 3-way lockstep of
  `stepMirFn`, `Miri.Interpreter.Step.step` (`annealStepHooks`), and
  `TreeBorrowsRel` across all 5 readable (`perm ≠ .disabled`), all 5 writable
  (`perm ≠ .frozen ∧ perm ≠ .disabled`), and all reborrowable 6-state
  permissions.
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

/-- Zero-sized unit type `()`. -/
def unitT : Ty := { kind := .tuple [], layoutIdx := 0 }

/-- `Retag(rk, _2)` where `_2` is a reference (`&()` or `&mut ()`) to `_1 : ()`. -/
def retagZstRefBody (rk : RetagKind) (mutability : Mutability) : CapturedMir :=
  witBody "lm_3_3_sim::retag_zst_ref" 0
    [declOf unitT, declOf unitT,
      declOf { kind := .ref mutability (.tuple []), layoutIdx := 0 }]
    [stmt (.retag rk (loc 2))]

/-- Pre-retag state for `retagZstRefBody`: `_1 = ()`, `_2` holds parent tag `1`
(`Unique`), and sibling `entry 2` is a **protected** `Unique` borrow (`prot =
some 1`, `activeProtectors = [1]`) that would trigger immediate UB if the retag
performed a 1+-byte initial child read. -/
def retagZstRefState : MachineState :=
  simState [.uninit, .init .unit, .init (.ptr ⟨1, 0⟩ 8)]
    [entry 2 .unique none (some 1), entry 1 .unique] true

/-- **`sim_lm3_3_retag_zst_ref_step`**: across all `4 × 2 = 8` `(rk, mutability)`
combinations on a zero-sized pointee (`()`), `StatementKind.retag rk _2`
allocates child tag `3` under `parentTag = some 1` with permission
`annealRetagPerm (retagKindToAnnealMode rk) mutability true`, **skips** the
0-byte initial child read so even the protected `Unique` sibling `entry 2`
survives without UB or freezing (matching `retagPointerValue_zst_simulation`),
and preserves `TreeBorrowsRel`. -/
theorem sim_lm3_3_retag_zst_ref_step
    (rk : RetagKind) (mutability : Mutability) :
    let childPerm := annealRetagPerm (retagKindToAnnealMode rk) mutability true
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let activeProts := match rk with | .fnEntry => [2, 1] | _ => [1]
    ∃ s' : MachineState,
      stepMirFn (retagZstRefBody rk mutability) retagZstRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) childProt,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors) := by
  cases rk <;> cases mutability <;>
    exact ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩

/-- State where `_2 : &()` / `&mut ()` holds a provenance-free scalar pointer:
non-null aligned dangling `0x8` (`nonNull = true`, e.g.
`NonNull::<()>::dangling().as_ref()`) vs. null `0x0` (`nonNull = false`). -/
def retagZstScalarState (nonNull : Bool) : MachineState :=
  simState [.uninit, .init .unit, .init (.scalar ⟨if nonNull then 8 else 0, 8⟩)] [] false

/-- **`sim_lm3_3_retag_zst_scalar_step`**: across all `4` `RetagKind`s and both
reference mutabilities on zero-sized `()`, `StatementKind.retag rk _2` on a
non-null provenance-free scalar ZST reference (`_2 = .scalar ⟨8, 8⟩`) steps
cleanly without allocating a tag, whereas a null ZST reference (`_2 = .scalar
⟨0, 8⟩`) faults with `.fail .ub`, matching `retagPointerValue_zst_simulation`. -/
theorem sim_lm3_3_retag_zst_scalar_step
    (rk : RetagKind) (mutability : Mutability) (nonNull : Bool) :
    match nonNull with
    | true =>
      ∃ s' : MachineState,
        stepMirFn (retagZstRefBody rk mutability) (retagZstScalarState true) = .step s' ∧
        s'.memory = (retagZstScalarState true).memory ∧
        get? s'.frame.locals 2 = some (.init (.scalar ⟨8, 8⟩))
    | false =>
      stepMirFn (retagZstRefBody rk mutability) (retagZstScalarState false) = .fail .ub := by
  cases nonNull <;> cases mutability <;> cases rk
  all_goals
    first
    | exact ⟨_, rfl, rfl, rfl⟩
    | rfl

/-- Zero-sized `core::marker::PhantomData<u64>` type (`Freeze` and 0-byte ZST
even when `layoutIdx = 0` points to a non-zero layout entry). -/
def phantomU64T : Ty :=
  { kind := .adt "core::marker::PhantomData" [.uint .u64], layoutIdx := 0 }

/-- `Retag(rk, _2)` where `_2` is a reference (`&PhantomData<u64>` or
`&mut PhantomData<u64>`) in a body whose `layouts[0]` has non-zero size (`8`),
testing structural `rigidTyIsZeroSized` on `PhantomData`. -/
def retagPhantomRefBody (rk : RetagKind) (mutability : Mutability) : CapturedMir :=
  witBody "lm_3_3_sim::retag_phantom_ref" 8
    [declOf phantomU64T, declOf phantomU64T,
      declOf { kind := .ref mutability phantomU64T.kind, layoutIdx := 0 }]
    [stmt (.retag rk (loc 2))]

/-- **`sim_lm3_3_retag_phantom_ref_step`**: across all `4 × 2 = 8`
`(rk, mutability)` combinations on `core::marker::PhantomData<u64>` (even when
`layouts[0]` has `8`-byte size), `StatementKind.retag rk _2` recognizes
`PhantomData` as zero-sized via `rigidTyIsZeroSized`, allocates child tag `3`
under `parentTag = some 1`, skips the initial child read so the protected
`Unique` sibling `entry 2` survives without UB or freezing, and preserves
`TreeBorrowsRel`. -/
theorem sim_lm3_3_retag_phantom_ref_step
    (rk : RetagKind) (mutability : Mutability) :
    let childPerm := annealRetagPerm (retagKindToAnnealMode rk) mutability true
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let activeProts := match rk with | .fnEntry => [2, 1] | _ => [1]
    ∃ s' : MachineState,
      stepMirFn (retagPhantomRefBody rk mutability) retagZstRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) childProt,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors) := by
  cases rk <;> cases mutability <;>
    exact ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩

/-- `_3 = &bk (*_2)` where `_2 : &mut ()` and `_1 : ()` (even when `layouts[0]`
has `8`-byte size), testing that `evalRvalue` deref reborrows consult
`placeIsZeroSized` and skip the initial child read on ZST pointees. -/
def zstDerefReborrowBody (bk : BorrowKind) : CapturedMir :=
  let dstMut : Mutability := match bk with | .shared => .not | .mut _ => .mut
  witBody "lm_3_3_sim::zst_deref_reborrow" 8
    [declOf unitT, declOf unitT,
      refMutDecl (.tuple []),
      declOf { kind := .ref dstMut (.tuple []), layoutIdx := 0 }]
    [stmt (.assign (loc 3) (.ref bk (deref 2)))]

/-- Pre-reborrow state for `zstDerefReborrowBody`: `_1 = ()`, `_2` holds parent
tag `1` (`Unique`), `_3` is uninitialized, and sibling `entry 2` is a
**protected** `Unique` borrow (`prot = some 1`, `activeProtectors = [1]`) that
would fault with UB if `evalRvalue` performed a 1+-byte initial read. -/
def zstDerefReborrowState : MachineState :=
  simState [.uninit, .init .unit, .init (.ptr ⟨1, 0⟩ 8), .uninit]
    [entry 2 .unique none (some 1), entry 1 .unique] true

/-- **`sim_lm3_3_zst_deref_reborrow_step`**: across all 3 `BorrowKind`s
(`.shared`, `.mut false`, `.mut true`) on a zero-sized deref place `(*_2) : ()`,
`stepMirFn` executing `_3 = &bk (*_2)` allocates child tag `3` under
`parentTag = some 1` with permission `.frozen` (shared) or `.reservedFrz false`
(mutable) and **skips** the 0-byte initial child read via `placeIsZeroSized`, so
the protected `Unique` sibling `entry 2` survives without UB or freezing and
`TreeBorrowsRel` holds after the step. -/
theorem sim_lm3_3_zst_deref_reborrow_step (bk : BorrowKind) :
    let childPerm : TreeBorrowPerm :=
      match bk with
      | .shared => .frozen
      | .mut _ => .reservedFrz false
    ∃ s' : MachineState,
      stepMirFn (zstDerefReborrowBody bk) zstDerefReborrowState = .step s' ∧
      get? s'.frame.locals 3 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) none,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = [1] ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors) := by
  rcases bk with _ | ⟨_ | _⟩ <;>
    exact ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩

/-- `Retag(rk, _2)` where `_2` is a reference (`&pointee` or `&mut pointee`) to
an arbitrary `pointee : RigidTy`. -/
def retagPointeeRefBody (rk : RetagKind) (mutability : Mutability)
    (pointee : RigidTy) : CapturedMir :=
  witBody "lm_3_3_sim::retag_pointee_ref" 0
    [declOf unitT, declOf { kind := pointee, layoutIdx := 0 },
      declOf { kind := .ref mutability pointee, layoutIdx := 0 }]
    [stmt (.retag rk (loc 2))]

/-- **`sim_lm3_3_retag_uninhabited_ref_ub_step`**: for **every** `RetagKind`,
reference `Mutability`, initialized local value `val` in `_2` (whether a live
provenance pointer `.ptr ⟨1, 0⟩ 8` or a non-null dangling scalar `.scalar ⟨8, 8⟩`),
borrow table `borrows`, protector state `isProtected`, and uninhabited pointee
`pointee` (`rigidTyIsUninhabited 16 pointee = true`, e.g. `!`, `[!; 1]`,
`(!, ())`, or `core::convert::Infallible`), `StatementKind.retag rk _2`
immediately faults with `MirStepNode.fail .ub` rather than treating the
uninhabited reference as a benign ZST. -/
theorem sim_lm3_3_retag_uninhabited_ref_ub_step
    (rk : RetagKind) (mutability : Mutability) (pointee : RigidTy)
    (val : Value) (borrows : List BorrowEntry) (isProtected : Bool)
    (huninhab : rigidTyIsUninhabited 16 pointee = true) :
    stepMirFn (retagPointeeRefBody rk mutability pointee)
      (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub := by
  change
    (match rigidTyIsUninhabited 16 pointee with
     | true => MirStepNode.fail .ub
     | false => _) = .fail .ub
  rw [huninhab]

/-- **`sim_lm3_3_retag_inhabited_never_container_zst_step`**: in contrast to
`sim_lm3_3_retag_uninhabited_ref_ub_step` on `!` and `[!; 1]`, zero-sized
containers `[!; 0]` (`.array .never 0`) and `core::marker::PhantomData<!>`
(`.adt "core::marker::PhantomData" [.never]`) ARE inhabited
(`rigidTyIsUninhabited 16 = false`) and zero-sized (`rigidTyIsZeroSized 16 = true`),
so `StatementKind.retag rk _2` across all `4 × 2 = 8` `(rk, mutability)`
combinations steps cleanly on both provenance pointers (`retagZstRefState`,
preserving the protected `Unique` sibling `entry 2` and `TreeBorrowsRel`) and
non-null provenance-free scalar references (`retagZstScalarState true`). -/
theorem sim_lm3_3_retag_inhabited_never_container_zst_step
    (rk : RetagKind) (mutability : Mutability) (usePhantom : Bool) :
    let pointee : RigidTy :=
      if usePhantom then .adt "core::marker::PhantomData" [.never]
      else .array .never 0
    let childPerm := annealRetagPerm (retagKindToAnnealMode rk) mutability true
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let activeProts := match rk with | .fnEntry => [2, 1] | _ => [1]
    rigidTyIsUninhabited 16 pointee = false ∧
    rigidTyIsZeroSized 16 pointee = true ∧
    (∃ s' : MachineState,
      stepMirFn (retagPointeeRefBody rk mutability pointee) retagZstRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) childProt,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) ∧
    (∃ s'' : MachineState,
      stepMirFn (retagPointeeRefBody rk mutability pointee) (retagZstScalarState true) =
        .step s'' ∧
      s''.memory = (retagZstScalarState true).memory ∧
      get? s''.frame.locals 2 = some (.init (.scalar ⟨8, 8⟩))) := by
  cases usePhantom <;> cases rk <;> cases mutability <;>
    exact ⟨rfl, rfl,
      ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩,
      ⟨_, rfl, rfl, rfl⟩⟩

/-- **`sim_lm3_3_retag_unsafecell_zst_vs_never_step`**: across all `4 × 2 = 8`
`(rk, mutability)` combinations:
1. transparent/same-size wrappers `core::cell::UnsafeCell<()>` (`!Freeze`) and
   `core::mem::MaybeUninit<!>` (`Freeze`) are inhabited
   (`rigidTyIsUninhabited 16 = false`) and zero-sized
   (`rigidTyIsZeroSized 16 = true`), so `StatementKind.retag rk _2` steps
   cleanly on both provenance pointers (`retagZstRefState`, skipping the 0-byte
   initial child read even for `&mut UnsafeCell<()>` in `ReservedIM` /
   `ReservedFrz false` so protected `Unique` sibling `entry 2` survives) and
   non-null dangling scalars (`retagZstScalarState true`);
2. by-value `T` wrappers `core::cell::UnsafeCell<!>`, `core::cell::Cell<!>`,
   `core::cell::RefCell<!>`, and `core::mem::ManuallyDrop<!>` around `!` are
   uninhabited (`rigidTyIsUninhabited 16 = true`), so
   `StatementKind.retag rk _2` immediately faults with `.fail .ub` for every
   `val`, `borrows`, and `isProtected` (while `RefCell<()>` remains inhabited
   and non-zero-sized because of its `BorrowFlag` field). -/
theorem sim_lm3_3_retag_unsafecell_zst_vs_never_step
    (rk : RetagKind) (mutability : Mutability) (useMaybeUninit : Bool)
    (val : Value) (borrows : List BorrowEntry) (isProtected : Bool) :
    let zstPointee : RigidTy :=
      if useMaybeUninit then .adt "core::mem::MaybeUninit" [.never]
      else .adt "core::cell::UnsafeCell" [.tuple []]
    let childPerm :=
      annealRetagPerm (retagKindToAnnealMode rk) mutability useMaybeUninit
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let activeProts := match rk with | .fnEntry => [2, 1] | _ => [1]
    rigidTyIsUninhabited 16 zstPointee = false ∧
    rigidTyIsZeroSized 16 zstPointee = true ∧
    rigidTyIsFreeze 16 zstPointee = useMaybeUninit ∧
    rigidTyIsUninhabited 16 (.adt "core::cell::RefCell" [.tuple []]) = false ∧
    rigidTyIsZeroSized 16 (.adt "core::cell::RefCell" [.tuple []]) = false ∧
    rigidTyIsFreeze 16 (.adt "core::cell::RefCell" [.tuple []]) = false ∧
    (∃ s' : MachineState,
      stepMirFn (retagPointeeRefBody rk mutability zstPointee) retagZstRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) childProt,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) ∧
    (∃ s'' : MachineState,
      stepMirFn (retagPointeeRefBody rk mutability zstPointee) (retagZstScalarState true) =
        .step s'' ∧
      s''.memory = (retagZstScalarState true).memory ∧
      get? s''.frame.locals 2 = some (.init (.scalar ⟨8, 8⟩))) ∧
    stepMirFn (retagPointeeRefBody rk mutability (.adt "core::cell::UnsafeCell" [.never]))
      (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub ∧
    stepMirFn (retagPointeeRefBody rk mutability (.adt "core::cell::Cell" [.never]))
      (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub ∧
    stepMirFn (retagPointeeRefBody rk mutability (.adt "core::cell::RefCell" [.never]))
      (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub ∧
    stepMirFn (retagPointeeRefBody rk mutability (.adt "core::mem::ManuallyDrop" [.never]))
      (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub := by
  have hub_uc :
      stepMirFn (retagPointeeRefBody rk mutability (.adt "core::cell::UnsafeCell" [.never]))
        (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub :=
    sim_lm3_3_retag_uninhabited_ref_ub_step rk mutability
      (.adt "core::cell::UnsafeCell" [.never]) val borrows isProtected rfl
  have hub_c :
      stepMirFn (retagPointeeRefBody rk mutability (.adt "core::cell::Cell" [.never]))
        (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub :=
    sim_lm3_3_retag_uninhabited_ref_ub_step rk mutability
      (.adt "core::cell::Cell" [.never]) val borrows isProtected rfl
  have hub_rc :
      stepMirFn (retagPointeeRefBody rk mutability (.adt "core::cell::RefCell" [.never]))
        (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub :=
    sim_lm3_3_retag_uninhabited_ref_ub_step rk mutability
      (.adt "core::cell::RefCell" [.never]) val borrows isProtected rfl
  have hub_md :
      stepMirFn (retagPointeeRefBody rk mutability (.adt "core::mem::ManuallyDrop" [.never]))
        (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub :=
    sim_lm3_3_retag_uninhabited_ref_ub_step rk mutability
      (.adt "core::mem::ManuallyDrop" [.never]) val borrows isProtected rfl
  cases useMaybeUninit <;> cases rk <;> cases mutability <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩,
      ⟨_, rfl, rfl, rfl⟩,
      hub_uc, hub_c, hub_rc, hub_md⟩

/-- **`sim_lm3_3_retag_phantom_unsafecell_vs_cell_step`**: across all
`4 × 2 = 8` `(rk, mutability)` combinations:
1. `core::marker::PhantomData<core::cell::UnsafeCell<u64>>` is `Freeze`
   (`rigidTyIsFreeze 16 = true`, `unsafe impl<T: ?Sized> Freeze for PhantomData<T>`)
   and zero-sized (`rigidTyIsZeroSized 16 = true`), so `StatementKind.retag rk _2`
   assigns `annealRetagPerm (retagKindToAnnealMode rk) mutability true`
   (`.frozen` / `.reservedFrz false`, never `.cell` / `.reservedIM`) and skips
   the 0-byte initial read;
2. `core::cell::Cell<u64>` is `!Freeze` (`rigidTyIsFreeze 16 = false`) even
   though its generic argument `u64` is `Freeze`, so `StatementKind.retag rk _2`
   assigns `annealRetagPerm (retagKindToAnnealMode rk) mutability false`
   (`.cell` on shared references and `.reservedIM` / `.reservedFrz false` on
   mutable references). -/
theorem sim_lm3_3_retag_phantom_unsafecell_vs_cell_step
    (rk : RetagKind) (mutability : Mutability) :
    let phantomCellPt : RigidTy :=
      .adt "core::marker::PhantomData" [.adt "core::cell::UnsafeCell" [.uint .u64]]
    let cellU64Pt : RigidTy := .adt "core::cell::Cell" [.uint .u64]
    let mode := retagKindToAnnealMode rk
    let phPerm := annealRetagPerm mode mutability true
    let cellPerm := annealRetagPerm mode mutability false
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let activeProts := match rk with | .fnEntry => [2, 1] | _ => [1]
    rigidTyIsFreeze 16 phantomCellPt = true ∧
    rigidTyIsZeroSized 16 phantomCellPt = true ∧
    rigidTyIsFreeze 16 cellU64Pt = false ∧
    fnEntryRetagPerm mutability cellU64Pt = annealRetagPerm .fnEntry mutability false ∧
    retagPerm rk mutability cellU64Pt = cellPerm ∧
    (∃ s' : MachineState,
      stepMirFn (retagPointeeRefBody rk mutability phantomCellPt) retagZstRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 phPerm (some 1) childProt,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) := by
  cases rk <;> cases mutability <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl,
      ⟨_, rfl, rfl, rfl, rfl, ⟨rfl, by decide, rfl, rfl, rfl⟩⟩⟩

/-! ## General 6-State `Miri.Interpreter.Step.step` + `TreeBorrowsRel` Lockstep -/

/-- **`stateRelLM3_2Tree_treeBorrowsRel`**: every `StateRelLM3_2Tree` state
maintains distinct borrow tags and satisfies `TreeBorrowsRel` against its
one-location normal tree `basedNormalTree`. -/
theorem stateRelLM3_2Tree_treeBorrowsRel
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap) :
    (s.memory.borrows.map BorrowEntry.tag).Nodup ∧
      TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
        (basedNormalTree s.memory.borrows s.memory.activeProtectors) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc_e, _⟩ := id htree.erased_rel
  have htags :
      s.memory.borrows.map BorrowEntry.tag =
        (treeMap.map ReborrowMapEntry.toAllocMapEntry).map AllocMapEntry.tag := by
    rw [htree.borrows_eq, List.map_map, List.map_map]
    rfl
  have hnodup : (s.memory.borrows.map BorrowEntry.tag).Nodup := by
    rw [htags]
    exact halloc_e.tags_nodup
  exact ⟨hnodup, basedNormalTree_rel s.memory.borrows s.memory.activeProtectors hnodup⟩

/-- **`sim_lm3_3_interpreter_deref_read_step`**: general 3-way lockstep of
Anneal's `stepMirFn`, `lean-miri`'s `Miri.Interpreter.Step.step`
(`annealStepHooks`), and `TreeBorrowsRel` on `basedNormalTree` for safe-reference
dereference reads `_d = (copy|move) *_r` across **all 5 readable 6-state
permissions** (`e.perm ≠ .disabled`: `Cell`, `ReservedIM`,
`ReservedFrz false`, `ReservedFrz true`, `Unique`, `Frozen`). -/
theorem sim_lm3_3_interpreter_deref_read_step
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal, get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ treeMap, e.tag = ptrVal.tag →
        get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? body.localDecls e.localIdx = some decl →
            decl.ty.kind = dstDecl.ty.kind))
    (hanc_read : ∀ ptrVal,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ treeMap, e.tag = ptrVal.tag →
        treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    let treeMap' := derefReadNextTreeMap s.frame.locals treeMap refIdx
    TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
      (basedNormalTree s.memory.borrows s.memory.activeProtectors) ∧
    StepRelLM3_2Tree body m treeMap'
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ m',
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM3_2Tree body s' m' treeMap' ∧
        TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
          (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) := by
  dsimp only []
  have hpre := (stateRelLM3_2Tree_treeBorrowsRel htree).2
  have hstep := step_safeRef_deref_read_tree_simulation htree hphase hopKind hbb hstmt
    hdecl_dst hdecl_ref href_ty hdst_prim himm hlive_ref hanc_read hlay_coh
  refine ⟨hpre, hstep, fun s' hs' => ?_⟩
  generalize hm :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = mr at hstep ⊢
  rw [hs'] at hstep
  cases hstep with
  | step _ m' _ htree' =>
    exact ⟨m', rfl, htree', (stateRelLM3_2Tree_treeBorrowsRel htree').2⟩

private def actAllocEntry (e : ReborrowMapEntry) : AllocMapEntry :=
  { e.toAllocMapEntry with perm := .active }

private theorem sameAllocSkeleton_actAllocEntry (treeMap : List ReborrowMapEntry) :
    SameAllocSkeleton
      (treeMap.map ReborrowMapEntry.toAllocMapEntry)
      (treeMap.map actAllocEntry) := by
  induction treeMap with
  | nil => exact .nil
  | cons hd tl ih => exact .cons ⟨rfl, rfl, rfl⟩ ih

private theorem lookupAllocMapByTag_map_actAllocEntry
    (treeMap : List ReborrowMapEntry) (tag : Nat) :
    lookupAllocMapByTag (treeMap.map actAllocEntry) tag =
      (lookupTreeMapByTag treeMap tag).map actAllocEntry := by
  induction treeMap with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, lookupAllocMapByTag, lookupTreeMapByTag,
      actAllocEntry, ReborrowMapEntry.toAllocMapEntry]
    cases Nat.beq hd.tag tag
    · exact ih
    · rfl

private theorem sameAllocSkeleton_updateOnWrite_actAllocEntry
    (allBorrows : List BorrowEntry) (treeMap : List ReborrowMapEntry)
    (targetLocal : Local) (wTag : Nat) :
    SameAllocSkeleton
      ((treeMap.map actAllocEntry).map (fun x => x.updateOnWrite targetLocal (some wTag)))
      ((treeMap.map (ReborrowMapEntry.updateOnWrite allBorrows targetLocal wTag)).map
        ReborrowMapEntry.toAllocMapEntry) := by
  induction treeMap with
  | nil => exact .nil
  | cons hd tl ih =>
    simp only [List.map_cons]
    refine .cons ⟨?_, ?_, ?_⟩ ih
    · simp [AllocMapEntry.updateOnWrite, actAllocEntry, ReborrowMapEntry.toAllocMapEntry]
    · simp [AllocMapEntry.updateOnWrite, actAllocEntry, ReborrowMapEntry.toAllocMapEntry]
    · simp [AllocMapEntry.updateOnWrite, actAllocEntry, ReborrowMapEntry.toAllocMapEntry]

private theorem sameAllocSkeleton_actAllocEntry_symm (treeMap : List ReborrowMapEntry) :
    SameAllocSkeleton
      (treeMap.map actAllocEntry)
      (treeMap.map ReborrowMapEntry.toAllocMapEntry) := by
  induction treeMap with
  | nil => exact .nil
  | cons _ _ ih => exact .cons ⟨rfl, rfl, rfl⟩ ih

private theorem evalOperand_borrows_irrel_of_wtScalar
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (locals : List LocalSlot) (b₁ b₂ : List BorrowEntry)
    (globals : List CapturedAllocation) (callerLocals : List LocalSlot) :
    evalOperand locals op b₁ globals body.layouts callerLocals =
      evalOperand locals op b₂ globals body.layouts callerLocals := by
  cases hop with
  | constScalar _ _ _ _ _ _ _ _ _ => rfl
  | copyLocal _ _ _ _ _ => rfl

private theorem writeStackThinPtrTypedDeref_of_dead
    {locals : List LocalSlot} {entry : BorrowEntry} {ptrVal : ProvenancePtr}
    {val : Value} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {pointeeTyOpt accessedTyOpt : Option Ty}
    (hdead : get? locals entry.targetLocal = some .dead) :
    writeStackThinPtrTypedDeref locals locals entry ptrVal .nil val localDecls layouts
      pointeeTyOpt accessedTyOpt = .ub := by
  unfold writeStackThinPtrTypedDeref
  dsimp only []
  rw [hdead]
  dsimp only []
  cases val <;> cases Bool.and _ _ <;> rfl

private theorem writeStackThinPtrTypedDeref_of_same_target
    {locals : List LocalSlot} {e₁ e₂ : BorrowEntry} {ptrVal : ProvenancePtr}
    {val : Value} {d₀ : LocalDecl} {ds : List LocalDecl} {layouts : LayoutTable}
    {pointeeTyOpt accessedTyOpt : Option Ty}
    (htl : e₁.targetLocal = e₂.targetLocal)
    (htp : e₁.targetProjection = e₂.targetProjection) :
    writeStackThinPtrTypedDeref locals locals e₁ ptrVal .nil val (d₀ :: ds) layouts
      pointeeTyOpt accessedTyOpt =
    writeStackThinPtrTypedDeref locals locals e₂ ptrVal .nil val (d₀ :: ds) layouts
      pointeeTyOpt accessedTyOpt := by
  rcases e₁ with ⟨_, tl₁, tp₁, _, _, _⟩
  rcases e₂ with ⟨_, tl₂, tp₂, _, _, _⟩
  dsimp only at htl htp
  subst htl htp
  rfl

/-- **`sim_lm3_3_interpreter_deref_write_step`**: general 3-way lockstep of
Anneal's `stepMirFn`, `lean-miri`'s `Miri.Interpreter.Step.step`
(`annealStepHooks`), and `TreeBorrowsRel` on `basedNormalTree` for safe-reference
dereference writes `*_r = op` across **all 5 writable 6-state permissions**
(`e.perm ≠ .frozen ∧ e.perm ≠ .disabled`: `Cell`, `ReservedIM`,
`ReservedFrz false`, `ReservedFrz true`, and `Unique`), lifting `LM-3.2`'s
2-permission restriction (`e.perm = .active ∨ e.perm = .reserved`) to the full
6-state lattice (`I-10` & `I-11`). -/
theorem sim_lm3_3_interpreter_deref_write_step
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl : LocalDecl} {mutability : Mutability}
    {pointeeKind : RigidTy} {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal e tgtDecl,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm ≠ .frozen ∧ e.perm ≠ .disabled) ∧
        tgtDecl.ty.kind = pointeeKind)
    (hanc_write : ∀ ptrVal e,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .write s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    let treeMap' := derefWriteNextTreeMap s.frame.locals treeMap refIdx
    TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
      (basedNormalTree s.memory.borrows s.memory.activeProtectors) ∧
    StepRelLM3_2Tree body m treeMap'
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ m',
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM3_2Tree body s' m' treeMap' ∧
        TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
          (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) := by
  dsimp only []
  have hpre := (stateRelLM3_2Tree_treeBorrowsRel htree).2
  have hstep_main :
      StepRelLM3_2Tree body m (derefWriteNextTreeMap s.frame.locals treeMap refIdx)
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
    let s_e := eraseBorrowParents s treeMap
    let am_act := treeMap.map actAllocEntry
    let s_act : MachineState :=
      { s_e with memory := { s_e.memory with borrows := am_act.map AllocMapEntry.toBorrowEntry } }
    let treeMap' := derefWriteNextTreeMap s.frame.locals treeMap refIdx
    have hskel_act : SameAllocSkeleton (treeMap.map ReborrowMapEntry.toAllocMapEntry) am_act :=
      sameAllocSkeleton_actAllocEntry treeMap
    have hstate_act : StateRelLM3_2 body s_act m am_act :=
      htree.erased_rel.replace_borrows_skeleton hskel_act
    have hsim := step_safeRef_deref_write_simulation_explicit hstate_act hphase hbb hstmt
      hdecl_ref href_ty hval_prim hval_kind hop himm_ref (by
        intro ptrVal e' tgtDecl hget he' htag' hdecl_t hdead
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
        have hl := hlive_ref ptrVal e tgtDecl hget he htag' hdecl_t hdead
        exact ⟨hl.1, Or.inl rfl, hl.2.2⟩) hlay_coh
    obtain ⟨tf, hframes, _, _, hfr, hcal_e, _, hprot_e, hcaller_e, _, halloc_e, _⟩ :=
      id htree.erased_rel
    obtain ⟨_, _, _, _, _, hcal_a, _, hprot_a, hcaller_a, hbor_a, halloc_a, _⟩ := id hstate_act
    have hcal : s.memory.activeCallee = none := hcal_e
    have hprot : s.memory.activeProtectors = .nil := hprot_e
    have hcaller : s.memory.callerLocals = .nil := hcaller_e
    have hbor_s : s.memory.borrows = treeMap.map ReborrowMapEntry.toBorrowEntry := htree.borrows_eq
    have hnodup_tm : (treeMap.map ReborrowMapEntry.tag).Nodup := by
      have htags :
          (treeMap.map ReborrowMapEntry.toAllocMapEntry).map AllocMapEntry.tag =
            treeMap.map ReborrowMapEntry.tag := by
        rw [List.map_map]; rfl
      rw [← htags]; exact halloc_e.tags_nodup
    have hskel_next : SameAllocSkeleton (derefWriteNextAllocMap s.frame.locals am_act refIdx)
        (treeMap'.map ReborrowMapEntry.toAllocMapEntry) := by
      dsimp only [derefWriteNextAllocMap, derefWriteNextTreeMap, am_act, treeMap']
      cases hgr : get? s.frame.locals refIdx with
      | none => exact sameAllocSkeleton_actAllocEntry_symm treeMap
      | some slot =>
        cases slot with
        | dead => exact sameAllocSkeleton_actAllocEntry_symm treeMap
        | uninit => exact sameAllocSkeleton_actAllocEntry_symm treeMap
        | init v =>
          cases v with
          | unit => exact sameAllocSkeleton_actAllocEntry_symm treeMap
          | scalar _ => exact sameAllocSkeleton_actAllocEntry_symm treeMap
          | aggregate _ _ => exact sameAllocSkeleton_actAllocEntry_symm treeMap
          | ptr ptrVal sz =>
            by_cases hsz : sz = 8
            · subst hsz
              simp only [lookupAllocMapByTag_map_actAllocEntry]
              cases lookupTreeMapByTag treeMap ptrVal.tag with
              | none => exact sameAllocSkeleton_actAllocEntry_symm treeMap
              | some e =>
                dsimp only [Option.map, actAllocEntry, ReborrowMapEntry.toAllocMapEntry,
                  updateAllocMapOnWrite]
                exact sameAllocSkeleton_updateOnWrite_actAllocEntry
                  (treeMap.map ReborrowMapEntry.toBorrowEntry) treeMap e.localIdx ptrVal.tag
            · simp [hsz]
              exact sameAllocSkeleton_actAllocEntry_symm treeMap
    have hop_tf := hop tf hframes
    have hfa : s_act.frame = s.frame := rfl
    have hs_step := stepMirFn_eq_of_not_other body s hcal hphase
    have ha_step := stepMirFn_eq_of_not_other body s_act hcal_a hphase
    simp only [hbb, hstmt] at hs_step
    simp only [hfa, hbb, hstmt] at ha_step
    generalize hm_res :
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = mRes
      at hsim ⊢
    change StepRelLM3_2 body m _ (stepMirFn body s_act) mRes at hsim
    have hop_eq :
        evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals =
        evalOperand s.frame.locals op s_act.memory.borrows s_act.memory.globals body.layouts
          s_act.memory.callerLocals :=
      evalOperand_borrows_irrel_of_wtScalar hop_tf s.frame.locals
        s.memory.borrows s_act.memory.borrows s.memory.globals s.memory.callerLocals
    have hrv_s := evalRvalue_use_scalarOperand_eq_lm3_2 htree.erased_rel hframes hop_tf s.memory
    have hrv_a := evalRvalue_use_scalarOperand_eq_lm3_2 htree.erased_rel hframes hop_tf s_act.memory
    rw [hfa] at hrv_s hrv_a
    cases hop_res : evalOperand s.frame.locals op s_act.memory.borrows s_act.memory.globals
        body.layouts s_act.memory.callerLocals with
    | ub =>
      have ha_s : stepMirFn body s = .fail .ub := by
        rw [hs_step]; unfold evalStmt; dsimp only []; rw [hrv_s, hop_eq.trans hop_res]
      have ha_a : stepMirFn body s_act = .fail .ub := by
        rw [ha_step]; unfold evalStmt; rw [hfa]; dsimp only []; rw [hrv_a, hop_res]
      rw [ha_a] at hsim; rw [ha_s]
      cases hsim with | ub m' msg => exact .ub _ m' msg
    | unsupported =>
      have ha_a : stepMirFn body s_act = .unsupported := by
        rw [ha_step]; unfold evalStmt; rw [hfa]; dsimp only []; rw [hrv_a, hop_res]
      rw [ha_a] at hsim; cases hsim
    | ok val locals₁ =>
      have hloc₁_eq : locals₁ = s.frame.locals := by
        cases hop_tf with
        | constScalar c sc hcv _ _ _ _ _ _ =>
          unfold evalOperand at hop_res; dsimp only [] at hop_res
          rw [hcv] at hop_res; injection hop_res with _ hl; exact hl.symm
        | copyLocal idx _ _ _ _ =>
          unfold evalOperand at hop_res; dsimp only [] at hop_res
          cases hgi : get? s.frame.locals idx with
          | none => rw [hgi] at hop_res; cases hop_res
          | some sl =>
            rw [hgi] at hop_res
            cases sl with
            | dead => cases hop_res
            | uninit => cases hop_res
            | init _ =>
              simp only [readProjectedValue] at hop_res
              injection hop_res with _ hl; exact hl.symm
      subst hloc₁_eq
      obtain ⟨slot_r, mls_r, _, _, hslot_r, hmls_r, _, hloc_r⟩ := hfr.lookup_local hdecl_ref
      have hslot_r_s : get? s.frame.locals refIdx = some slot_r := hslot_r
      have hwp_eq :
          writePlaceValue s.frame.locals s.memory.borrows ⟨refIdx, .cons .deref .nil⟩ val
            body.localDecls body.layouts =
          writePlaceValue s.frame.locals s_act.memory.borrows ⟨refIdx, .cons .deref .nil⟩ val
            body.localDecls body.layouts := by
        rcases hloc_r.ref_immediate_cases href_ty ((himm_ref tf hframes) mls_r hmls_r) with
          ⟨hsr, _⟩ | ⟨hsr, _⟩ | ⟨_, _, hsr, _⟩ | ⟨ptrVal, _, hsr, hptrRel, _⟩
        · unfold writePlaceValue; cases body.localDecls <;> simp only [hslot_r_s, hsr]
        · unfold writePlaceValue; cases body.localDecls <;> simp only [hslot_r_s, hsr]
        · unfold writePlaceValue; cases body.localDecls <;> simp only [hslot_r_s, hsr]
        · have hsr_full : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) :=
            hslot_r_s.trans (congrArg some hsr)
          obtain ⟨_, _, _, _, _, _, ⟨e_am, he_am, htag_am, _⟩⟩ := hptrRel
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp he_am
          obtain ⟨tgtDecl, hdecl_t⟩ := halloc_e.target_decl e.toAllocMapEntry he_am
          have hlook_tm := lookupTreeMapByTag_of_mem_nodup hnodup_tm he htag_am
          have hlook_s : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by
            rw [hbor_s, lookupBorrow_map_toBorrowEntry_treeMap, hlook_tm]; rfl
          have he_act : actAllocEntry e ∈ am_act := List.mem_map_of_mem he
          have hlook_a :
              lookupBorrow s_act.memory.borrows ptrVal.tag =
                some (actAllocEntry e).toBorrowEntry := by
            rw [hbor_a, ← htag_am]
            exact lookupBorrow_map_toBorrowEntry_of_nodup halloc_a.tags_nodup he_act
          unfold writePlaceValue
          cases hld : body.localDecls with
          | nil =>
            dsimp only []
            rw [hsr_full]; dsimp only []
            rw [hlook_s, hlook_a]
            dsimp only [ReborrowMapEntry.toBorrowEntry, actAllocEntry,
              AllocMapEntry.toBorrowEntry, ReborrowMapEntry.toAllocMapEntry]
            by_cases hdead : get? s.frame.locals e.localIdx = some .dead
            · rw [hdead]
              cases e.perm <;> rfl
            · obtain ⟨_, ⟨hne_frz, hne_dis⟩, _⟩ :=
                hlive_ref ptrVal e tgtDecl hsr_full he htag_am hdecl_t.1 hdead
              cases hp : e.perm <;>
                first
                | exact absurd hp hne_frz
                | exact absurd hp hne_dis
                | rfl
          | cons d₀ ds =>
            dsimp only []
            rw [hsr_full]; dsimp only []
            rw [hlook_s, hlook_a]
            dsimp only []
            by_cases hdead : get? s.frame.locals e.localIdx = some .dead
            · have hdead_s : get? s.frame.locals e.toBorrowEntry.targetLocal = some .dead := hdead
              have hdead_a :
                  get? s.frame.locals (actAllocEntry e).toBorrowEntry.targetLocal = some .dead :=
                hdead
              rw [writeStackThinPtrTypedDeref_of_dead hdead_a,
                writeStackThinPtrTypedDeref_of_dead hdead_s]
              dsimp only [ReborrowMapEntry.toBorrowEntry]
              cases e.perm <;> rfl
            · obtain ⟨_, ⟨hne_frz, hne_dis⟩, _⟩ :=
                hlive_ref ptrVal e tgtDecl hsr_full he htag_am hdecl_t.1 hdead
              have hsame :
                  ∀ ptOpt accOpt,
                    writeStackThinPtrTypedDeref s.frame.locals s.frame.locals e.toBorrowEntry
                      ptrVal .nil val (d₀ :: ds) body.layouts ptOpt accOpt =
                    writeStackThinPtrTypedDeref s.frame.locals s.frame.locals
                      (actAllocEntry e).toBorrowEntry ptrVal .nil val (d₀ :: ds) body.layouts
                      ptOpt accOpt :=
                fun _ _ => writeStackThinPtrTypedDeref_of_same_target rfl rfl
              dsimp only [ReborrowMapEntry.toBorrowEntry, actAllocEntry,
                AllocMapEntry.toBorrowEntry, ReborrowMapEntry.toAllocMapEntry] at hsame ⊢
              cases hp : e.perm <;>
                first
                | exact absurd hp hne_frz
                | exact absurd hp hne_dis
                | exact hsame _ _
      cases hwp_res : writePlaceValue s.frame.locals s_act.memory.borrows
          ⟨refIdx, .cons .deref .nil⟩ val body.localDecls body.layouts with
      | ub =>
        have ha_s : stepMirFn body s = .fail .ub := by
          rw [hs_step]; unfold evalStmt; dsimp only []
          rw [hrv_s, hop_eq.trans hop_res]; dsimp only [evalPlaceWrite]
          rw [hprot]; dsimp only []; rw [hwp_eq.trans hwp_res, hcaller]
        have ha_a : stepMirFn body s_act = .fail .ub := by
          rw [ha_step]; unfold evalStmt; rw [hfa]; dsimp only []
          rw [hrv_a, hop_res]; dsimp only [evalPlaceWrite]
          rw [hprot_a]; dsimp only []; rw [hwp_res, hcaller_a]
        rw [ha_a] at hsim; rw [ha_s]
        cases hsim with | ub m' msg => exact .ub _ m' msg
      | unsupported =>
        have ha_a : stepMirFn body s_act = .unsupported := by
          rw [ha_step]; unfold evalStmt; rw [hfa]; dsimp only []
          rw [hrv_a, hop_res]; dsimp only [evalPlaceWrite]
          rw [hprot_a]; dsimp only []; rw [hwp_res]
        rw [ha_a] at hsim; cases hsim
      | ok locals₂ =>
        rcases hloc_r.ref_immediate_cases href_ty ((himm_ref tf hframes) mls_r hmls_r) with
          ⟨hsr, _⟩ | ⟨hsr, _⟩ | ⟨_, _, hsr, _⟩ | ⟨ptrVal, _, hsr, hptrRel, _⟩
        · unfold writePlaceValue at hwp_res
          cases body.localDecls <;> (simp only [hslot_r_s, hsr] at hwp_res; cases hwp_res)
        · unfold writePlaceValue at hwp_res
          cases body.localDecls <;> (simp only [hslot_r_s, hsr] at hwp_res; cases hwp_res)
        · unfold writePlaceValue at hwp_res
          cases body.localDecls <;> (simp only [hslot_r_s, hsr] at hwp_res; cases hwp_res)
        · have hsr_full : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) :=
            hslot_r_s.trans (congrArg some hsr)
          obtain ⟨_, _, _, _, _, _, ⟨e_am, he_am, htag_am, _⟩⟩ := hptrRel
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp he_am
          have hinv_s := invalidateDerefWriteBorrows_map_toBorrowEntry_tree
            s.frame.locals treeMap hnodup_tm refIdx ptrVal he htag_am hsr_full
          rw [← hbor_s] at hinv_s
          have hwub_s : derefWriteTreeUB s.frame.locals s.memory.borrows
              ⟨refIdx, .cons .deref .nil⟩ = false := by
            rw [hbor_s]
            exact derefWriteTreeUB_treeMap_eq_false s.frame.locals treeMap hnodup_tm refIdx ptrVal
              he htag_am hsr_full (by rw [← hbor_s]; exact hanc_write ptrVal e hsr_full he htag_am)
          have hwub_a : derefWriteTreeUB s.frame.locals s_act.memory.borrows
              ⟨refIdx, .cons .deref .nil⟩ = false := by
            rw [hbor_a]
            exact derefWriteTreeUB_map_toBorrowEntry_eq_false _ _ _
          have hinv_lay_s :
              invalidateDerefWriteBorrowsWithLayouts body.localDecls body.layouts
                s.frame.locals s.memory.borrows ⟨refIdx, .cons .deref .nil⟩ .nil =
              invalidateDerefWriteBorrows
                s.frame.locals s.memory.borrows ⟨refIdx, .cons .deref .nil⟩ .nil :=
            invalidateDerefWriteBorrowsWithLayouts_eq_of_thinPtr_nil_target
              body.localDecls body.layouts s.frame.locals s.memory.borrows refIdx ptrVal 8 hsr_full
              (fun b hb => by rw [hbor_s] at hb; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb; rfl)
          have hinv_lay_a :
              invalidateDerefWriteBorrowsWithLayouts body.localDecls body.layouts
                s.frame.locals s_act.memory.borrows ⟨refIdx, .cons .deref .nil⟩ .nil =
              invalidateDerefWriteBorrows
                s.frame.locals s_act.memory.borrows ⟨refIdx, .cons .deref .nil⟩ .nil :=
            invalidateDerefWriteBorrowsWithLayouts_eq_of_thinPtr_nil_target
              body.localDecls body.layouts s.frame.locals s_act.memory.borrows refIdx ptrVal 8
              hsr_full
              (fun b hb => by rw [hbor_a] at hb; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb; rfl)
          have ha_s :
              stepMirFn body s =
                .step (advanceStmt s locals₂
                  { s.memory with borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry }) := by
            rw [hs_step]; unfold evalStmt; dsimp only []
            rw [hrv_s, hop_eq.trans hop_res]; dsimp only [evalPlaceWrite]
            rw [hprot]; dsimp only []; rw [hwp_eq.trans hwp_res]
            dsimp only [derefWriteUnionProtectorUB, Bool.or]
            simp only [hwub_s, hcaller, hinv_lay_s]
            rw [hinv_s]
          have ha_a :
              stepMirFn body s_act =
                .step (advanceStmt s_act locals₂
                  { s_act.memory with
                    borrows := invalidateDerefWriteBorrows s.frame.locals s_act.memory.borrows
                      ⟨refIdx, .cons .deref .nil⟩ .nil }) := by
            rw [ha_step]; unfold evalStmt; rw [hfa]; dsimp only []
            rw [hrv_a, hop_res]; dsimp only [evalPlaceWrite]
            rw [hprot_a]; dsimp only []; rw [hwp_res]
            dsimp only [derefWriteUnionProtectorUB, Bool.or]
            simp only [hwub_a, hcaller_a, hinv_lay_a]
          rw [ha_a] at hsim; rw [ha_s]
          cases hsim with
          | step _ m' hrel_a =>
            have hs_eq :
                advanceStmt s locals₂
                  { s.memory with borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry } =
                { advanceStmt s_act locals₂
                    { s_act.memory with
                      borrows := invalidateDerefWriteBorrows s_act.frame.locals s_act.memory.borrows
                        ⟨refIdx, .cons .deref .nil⟩ .nil } with
                  memory :=
                    { (advanceStmt s_act locals₂
                        { s_act.memory with
                          borrows := invalidateDerefWriteBorrows s_act.frame.locals
                            s_act.memory.borrows ⟨refIdx, .cons .deref .nil⟩ .nil }).memory with
                      borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry } } := by
              dsimp only [s_act, s_e, eraseBorrowParents, advanceStmt]
            rw [hs_eq]
            exact .step _ _ treeMap' (StateRelLM3_2Tree.of_erased_skeleton hrel_a hskel_next)
  refine ⟨hpre, hstep_main, fun s' hs' => ?_⟩
  generalize hm :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = mr
    at hstep_main ⊢
  rw [hs'] at hstep_main
  cases hstep_main with
  | step _ m' _ htree' =>
    exact ⟨m', rfl, htree', (stateRelLM3_2Tree_treeBorrowsRel htree').2⟩

/-- **`sim_lm3_3_interpreter_reborrow_step`**: general 3-way lockstep of
Anneal's `stepMirFn`, `lean-miri`'s `Miri.Interpreter.Step.step`
(`annealStepHooks`), and `TreeBorrowsRel` on `basedNormalTree` for safe-reference
dereference reborrows `_d = &bk (*_r)` across **all reborrowable 6-state
permissions** (`e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared)`),
minting child tag `s.memory.nextTag` with `parentTag = some ptrVal.tag` and
performing the initial child read across the borrow hierarchy (`I-10`). -/
theorem sim_lm3_3_interpreter_reborrow_step
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : LocalDecl}
    {bk : BorrowKind} {refMut dstMut : Mutability}
    {pointeeKind dstPointee : RigidTy}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref refMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_zero_perm : ∀ ptrVal e,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      get? s.frame.locals e.localIdx ≠ some .dead ∧
      get? s.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hanc_read : ∀ ptrVal e,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    let treeMap' :=
      reborrowTreeMapNext body.localDecls body.layouts bk s.frame.locals treeMap refIdx
        s.memory.nextTag
    TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
      (basedNormalTree s.memory.borrows s.memory.activeProtectors) ∧
    StepRelLM3_2Tree body m treeMap'
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ m',
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM3_2Tree body s' m' treeMap' ∧
        TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
          (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) := by
  dsimp only []
  have hpre := (stateRelLM3_2Tree_treeBorrowsRel htree).2
  have hstep := step_reborrow_safeRef_tree_simulation_explicit htree hphase hbb hstmt
    hdecl_dst hdecl_ref href_ty hdst_ty hpk_prim himm hlive_zero_perm hanc_read hlay_coh
  refine ⟨hpre, hstep, fun s' hs' => ?_⟩
  generalize hm :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = mr at hstep ⊢
  rw [hs'] at hstep
  cases hstep with
  | step _ m' _ htree' =>
    exact ⟨m', rfl, htree', (stateRelLM3_2Tree_treeBorrowsRel htree').2⟩

end LeanMiriSpec.Correspondence.SimLM3_3
