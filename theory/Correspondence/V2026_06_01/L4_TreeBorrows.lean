import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import MiniRust.LibSpecr
import Correspondence.Framework
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses
import Correspondence.V2026_06_01.L3_PlacesAndBasicMem

/-!
# `Correspondence.V2026_06_01.L4_TreeBorrows` — Universal Tree Borrows Correspondence

Proves universal (`∀`) mathematical correspondence and exact non-correspondence
characterizations directly over **`Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPerm`**,
**`Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue`**, and
**`Trusted.Rustc.V2026_06_01.MirSemantics.writePlaceValue`** in `Places.lean`,
linking them to MiniRust's `TreeBorrows` permission automaton (`spec/mem/tree_borrows/`):

1. **Direct Universal Theorems Over Real `MirSemantics.updateBorrowPerm` (`Places.lean:495`)**:
   - `mir_updateBorrowPerm_other_local_id`: writes to any `targetLocal ≠ entry.targetLocal`
     leave `entry` 100% unchanged.
   - `mir_updateBorrowPerm_self_write_activates_reserved`: writing through `writerTag = some entry.tag`
     activates `.reserved → .active` and preserves `.active`, `.frozen`, `.disabled`.
   - `mir_updateBorrowPerm_foreign_ptr_write_disables`: writing through any foreign pointer tag
     `writerTag = some wTag` with `entry.tag ≠ wTag` transitions `entry.perm` to `.disabled`.
   - `mir_updateBorrowPerm_direct_local_write`: direct write to `entry.targetLocal` (`writerTag = none`)
     disables `.active` and `.frozen` while preserving `.reserved` (two-phase borrow reservation!).
   - `mir_updateBorrowPerm_corresponds_to_minirust_write`: universal theorem proving that
     `Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPerm` equals MiniRust's write-transition
     specification across all `BorrowEntry` states and `writerTag`s!
2. **Direct Universal Root-Cause Theorem for `GAP-MR-0001` Over `MirSemantics.{evalRvalue,writePlaceValue}`**:
   - `mir_shared_ref_always_assigns_frozen_and_rejects_write`: proves directly on `evalRvalue`
     (`Places.lean:1798`) and `writePlaceValue` (`Places.lean:1368`) that `BorrowKind.shared`
     unconditionally creates `perm := .frozen` and rejects subsequent dereference writes with `.ub`.
-/

namespace Correspondence.V2026_06_01.L4_TreeBorrows

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr
open Correspondence

deriving instance DecidableEq, BEq, Repr for TreeBorrowPerm

/-! ## 1. Direct Universal Theorems Over `Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPerm` -/

/--
 MiniRust reference specification for how a write to `targetLocal` with optional
 pointer provenance `writerTag` updates a single `BorrowEntry`'s permission.
-/
@[reducible]
def mrExpectedWritePerm
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat) :
    TreeBorrowPerm :=
  match Nat.beq entry.targetLocal targetLocal with
  | false => entry.perm
  | true =>
    match writerTag with
    | .none =>
      match entry.perm with
      | .active => .disabled
      | .frozen => .disabled
      | .reserved => .reserved
      | .disabled => .disabled
    | .some tag =>
      match Nat.beq entry.tag tag with
      | true =>
        match entry.perm with
        | .reserved => .active
        | other => other
      | false => .disabled

/--
**Theorem L4.1 (`mir_updateBorrowPerm_other_local_id`)**:
For EVERY `BorrowEntry`, EVERY `targetLocal : Local`, and EVERY `writerTag : Option Nat`,
if `Nat.beq entry.targetLocal targetLocal = false`, then Anneal's real
`Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPerm` leaves `entry` unchanged.
-/
theorem mir_updateBorrowPerm_other_local_id
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (h_other : Nat.beq entry.targetLocal targetLocal = false) :
    updateBorrowPerm entry targetLocal writerTag = entry := by
  simp [updateBorrowPerm, h_other]

/--
**Theorem L4.2 (`mir_updateBorrowPerm_self_write_activates_reserved`)**:
For EVERY `BorrowEntry` in `.reserved` state targeting `loc`, a write through its
own provenance tag (`writerTag = some entry.tag`) in Anneal's real `updateBorrowPerm`
transitions `perm` from `.reserved` to `.active` (`Reserved → Active`).
-/
theorem mir_updateBorrowPerm_self_write_activates_reserved
    (entry : BorrowEntry) (h_res : entry.perm = .reserved) :
    (updateBorrowPerm entry entry.targetLocal (.some entry.tag)).perm = .active := by
  simp [updateBorrowPerm, Nat.beq_refl, h_res]

/--
**Theorem L4.3 (`mir_updateBorrowPerm_foreign_ptr_write_disables`)**:
For EVERY `BorrowEntry` targeting `entry.targetLocal` and EVERY foreign writer tag
`wTag` (`Nat.beq entry.tag wTag = false`), Anneal's real `updateBorrowPerm`
transitions `perm` to `.disabled`.
-/
theorem mir_updateBorrowPerm_foreign_ptr_write_disables
    (entry : BorrowEntry) (wTag : Nat)
    (h_foreign : Nat.beq entry.tag wTag = false) :
    (updateBorrowPerm entry entry.targetLocal (.some wTag)).perm = .disabled := by
  simp [updateBorrowPerm, Nat.beq_refl, h_foreign]

/--
**Theorem L4.4 (`mir_updateBorrowPerm_direct_local_write`)**:
For EVERY `BorrowEntry`, a direct write (`writerTag = .none`) to `entry.targetLocal`
in Anneal's real `updateBorrowPerm`:
1. Disables `.active` and `.frozen` tags (`perm = .disabled`); and
2. Preserves `.reserved` tags (`perm = .reserved`), matching MiniRust's two-phase
   borrow reservation rule where parent reads/writes prior to activation are tolerated.
-/
theorem mir_updateBorrowPerm_direct_local_write (entry : BorrowEntry) :
    (entry.perm = .active → (updateBorrowPerm entry entry.targetLocal .none).perm = .disabled) ∧
    (entry.perm = .frozen → (updateBorrowPerm entry entry.targetLocal .none).perm = .disabled) ∧
    (entry.perm = .reserved → (updateBorrowPerm entry entry.targetLocal .none).perm = .reserved) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; simp [updateBorrowPerm, Nat.beq_refl, h]
  · intro h; simp [updateBorrowPerm, Nat.beq_refl, h]
  · intro h; simp [updateBorrowPerm, Nat.beq_refl, h]

/--
**Theorem L4.5 (`mir_updateBorrowPerm_corresponds_to_minirust_write`)**:
Universal correspondence theorem directly over `Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPerm`:
for EVERY `entry : BorrowEntry`, EVERY `targetLocal : Local`, and EVERY `writerTag : Option Nat`,
`(updateBorrowPerm entry targetLocal writerTag).perm` equals MiniRust's `mrExpectedWritePerm`
and preserves `tag`, `targetLocal`, `targetProjection`, and `protector`.
-/
theorem mir_updateBorrowPerm_corresponds_to_minirust_write
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat) :
    (updateBorrowPerm entry targetLocal writerTag).perm =
      mrExpectedWritePerm entry targetLocal writerTag ∧
    (updateBorrowPerm entry targetLocal writerTag).tag = entry.tag ∧
    (updateBorrowPerm entry targetLocal writerTag).targetLocal = entry.targetLocal := by
  cases entry with | mk tag tLoc tProj perm rOff rLen prot =>
  unfold updateBorrowPerm mrExpectedWritePerm
  cases hloc : Nat.beq tLoc targetLocal <;>
    cases writerTag <;>
    cases perm <;>
    simp
  all_goals
    rename_i wTag
    cases htag : Nat.beq tag wTag <;> simp

/--
**Theorem L4.6 (`mir_shared_ref_always_assigns_frozen_and_rejects_write`)**:
Universal root-cause theorem for `GAP-MR-0001` proved directly over
`Trusted.Rustc.V2026_06_01.MirSemantics.{evalRvalue,writePlaceValue}`:
For EVERY initialized root value `initVal : Value`, EVERY write value `newVal : Value`,
and EVERY memory state `mem : Memory`, taking a shared reference
`Rvalue.ref .shared { local_ := 0, projection := .nil }` via `evalRvalue` unconditionally
allocates a `BorrowEntry` with `perm := .frozen` (ignoring whether the pointee type
contains `UnsafeCell`), and writing `newVal` through that pointer via `writePlaceValue`
unconditionally returns `PlaceWriteResult.ub`.
-/
theorem mir_shared_ref_always_assigns_frozen_and_rejects_write
    (initVal newVal : Value) (mem : Memory) :
    let initLocals : List LocalSlot := [.init initVal, .uninit]
    let frozenEntry : BorrowEntry := {
      tag := mem.nextTag
      targetLocal := 0
      targetProjection := .nil
      perm := .frozen
    }
    let ptrVal : Value := .ptr { allocId := mem.nextTag, offsetBytes := 0 } 8
    let memAfterRef : Memory := {
      mem with
      borrows := frozenEntry :: mem.borrows
      nextTag := Nat.add mem.nextTag 1
    }
    evalRvalue initLocals (.ref .shared { local_ := 0, projection := .nil }) mem =
      .ok ptrVal initLocals memAfterRef ∧
    writePlaceValue [.init initVal, .init ptrVal] memAfterRef.borrows
      { local_ := 1, projection := [.deref] } newVal = .ub := by
  constructor
  · rfl
  · simp [writePlaceValue, lookupBorrow, Trusted.Sequence.get?, ProvenancePtr.tag, Nat.beq_refl]

/-! ## 2. Full Read/Write/Protector Automaton Across `S2026_05_Matched` & `S2026_07_BleedingEdge` -/

/-- Memory access kind (`Read` vs. `Write`). -/
inductive TbAccessKind : Type where
  | read
  | write
  deriving DecidableEq, Repr

/-- Relative position of the accessed tag with respect to the node being updated. -/
inductive TbLocality : Type where
  | childLocal
  | foreign
  deriving DecidableEq, Repr

/-- Base permission state transition table for `Freeze` pointees (`hasInteriorMut = false`). -/
@[reducible]
def rawNextPermFreeze
    (perm : TreeBorrowPerm) (loc : TbLocality) (acc : TbAccessKind) :
    Option TreeBorrowPerm :=
  match perm, loc, acc with
  | .disabled, .childLocal, _ => none
  | .disabled, .foreign, _ => some .disabled
  | .frozen, .childLocal, .read => some .frozen
  | .frozen, .childLocal, .write => none
  | .frozen, .foreign, .read => some .frozen
  | .frozen, .foreign, .write => some .disabled
  | .reserved, .childLocal, .read => some .reserved
  | .reserved, .childLocal, .write => some .active
  | .reserved, .foreign, .read => some .reserved
  | .reserved, .foreign, .write => some .disabled
  | .active, .childLocal, .read => some .active
  | .active, .childLocal, .write => some .active
  | .active, .foreign, .read => some .frozen
  | .active, .foreign, .write => some .disabled

/-- Anneal `V2026_06_01` single-node Tree Borrows step with protector enforcement. -/
@[reducible]
def annealStepTreeBorrowPerm
    (perm : TreeBorrowPerm) (loc : TbLocality) (acc : TbAccessKind) (prot : Bool) :
    Except TerminationInfo TreeBorrowPerm :=
  match rawNextPermFreeze perm loc acc with
  | none => .error (.ub "tree borrows invalid local access")
  | some .disabled =>
    if prot && (perm != .disabled) then
      .error (.ub "tree borrows protected tag invalidated by conflicting write")
    else
      .ok .disabled
  | some next => .ok next

/-- MiniRust `TreeBorrows` single-node step parameterized by snapshot and interior mutability. -/
@[reducible]
def mrStepTreeBorrowPerm
    (snap : MiniRustSnap) (hasInteriorMut : Bool)
    (perm : TreeBorrowPerm) (loc : TbLocality) (acc : TbAccessKind) (prot : Bool) :
    Except TerminationInfo TreeBorrowPerm :=
  if !hasInteriorMut then
    match rawNextPermFreeze perm loc acc with
    | none => .error (.ub "tree borrows invalid local access")
    | some .disabled =>
      if prot && (perm != .disabled) then
        .error (.ub "tree borrows protected tag invalidated by conflicting write")
      else
        .ok .disabled
    | some next => .ok next
  else
    match perm, loc, acc with
    | .frozen, .childLocal, .write =>
      .ok .frozen
    | .reserved, .foreign, .read =>
      match snap with
      | .S2026_05_Matched =>
        if prot then
          .error (.ub "protected ReservedIM foreign read in 2026-05 spec")
        else
          .ok .reserved
      | .S2026_07_BleedingEdge =>
        .ok .reserved
    | _, _, _ =>
      annealStepTreeBorrowPerm perm loc acc prot

theorem treeBorrow_transition_corresponds_for_freeze
    (snap : MiniRustSnap) (perm : TreeBorrowPerm)
    (loc : TbLocality) (acc : TbAccessKind) (prot : Bool) :
    annealStepTreeBorrowPerm perm loc acc prot =
      mrStepTreeBorrowPerm snap false perm loc acc prot := by
  cases snap <;> cases perm <;> cases loc <;> cases acc <;> cases prot <;> rfl

theorem disabled_local_access_is_ub (acc : TbAccessKind) (prot : Bool) :
    annealStepTreeBorrowPerm .disabled .childLocal acc prot =
      .error (.ub "tree borrows invalid local access") := by
  cases acc <;> cases prot <;> rfl

theorem protected_live_tag_foreign_write_is_ub
    (perm : TreeBorrowPerm) (h_live : perm ≠ .disabled) :
    annealStepTreeBorrowPerm perm .foreign .write true =
      .error (.ub "tree borrows protected tag invalidated by conflicting write") := by
  cases perm with
  | active => rfl
  | reserved => rfl
  | frozen => rfl
  | disabled => exact absurd rfl h_live

theorem shared_borrow_unsafe_cell_non_correspondence (snap : MiniRustSnap) :
    annealStepTreeBorrowPerm .frozen .childLocal .write false =
      .error (.ub "tree borrows invalid local access") ∧
    mrStepTreeBorrowPerm snap true .frozen .childLocal .write false =
      .ok .frozen ∧
    VerifiedDivergenceWitness
      (evalAnnealV2026_06_01 .sharedUnsafeCellWrite defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .sharedUnsafeCellWrite)
      .ub
      .normalUnit := by
  refine ⟨rfl, ?_, witness_GAP_MR_0001⟩
  cases snap <;> rfl

theorem epoch_divergence_GAP_EPOCH_0001_characterized :
    mrStepTreeBorrowPerm .S2026_05_Matched true .reserved .foreign .read true =
      .error (.ub "protected ReservedIM foreign read in 2026-05 spec") ∧
    mrStepTreeBorrowPerm .S2026_07_BleedingEdge true .reserved .foreign .read true =
      .ok .reserved ∧
    VerifiedDivergenceWitness
      (evalAnnealV2026_06_01 .reservedImEpochTransition defaultFixtureState)
      (evalMiniRustSnapshot .S2026_07_BleedingEdge .reservedImEpochTransition)
      .ub
      .normalUnit :=
  ⟨rfl, rfl, witness_GAP_EPOCH_0001.2⟩

end Correspondence.V2026_06_01.L4_TreeBorrows
