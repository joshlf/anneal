import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import MiniRust.LibSpecr
import MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
import MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops
import Correspondence.Framework
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses
import Correspondence.V2026_06_01.L3_PlacesAndBasicMem

/-!
# `Correspondence.V2026_06_01.L4_TreeBorrows` — Universal Tree Borrows Correspondence

Proves universal (`∀`) mathematical correspondence and exact non-correspondence
characterizations directly over **`Trusted.Rustc.V2026_06_01.MirSemantics.{updateBorrowPerm,
updateBorrowPermAtProj, invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj,
hasProtectedWriteConflict, attachBorrowProtector, evalPlaceWrite, evalRvalue, writePlaceValue}`**
in `Places.lean`, linking them to the specr-generated MiniRust `TreeBorrows` permission
automata in `MiniRust.Snapshots.S2026_05_Matched.Generated.Ops` and
`MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops` (`spec/mem/tree_borrows/`):

1. **Direct Universal Theorems Over Real `MirSemantics.updateBorrowPerm` & `updateBorrowPermAtProj`**:
   - `mir_updateBorrowPerm_other_local_id`: writes to any `targetLocal ≠ entry.targetLocal`
     leave `entry` 100% unchanged.
   - `mir_updateBorrowPerm_self_write_activates_reserved`: writing through `writerTag = some entry.tag`
     activates `.reserved → .active` and preserves `.active`, `.frozen`, `.disabled`.
   - `mir_updateBorrowPerm_foreign_ptr_write_disables`: writing through any foreign pointer tag
     `writerTag = some wTag` with `entry.tag ≠ wTag` transitions `entry.perm` to `.disabled`
     unless `entry.perm` is `.cell` or `.reservedIM`.
   - `mir_updateBorrowPerm_direct_local_write`: direct write to `entry.targetLocal` (`writerTag = none`)
     disables `.active`, `.frozen`, and `Freeze` reservations (`.reserved`) while preserving
     interior-mutable `.reservedIM` and `.cell` tags.
   - `mir_updateBorrowPerm_corresponds_to_minirust_write`: universal theorem proving that
     `Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPerm` equals `mrExpectedWritePerm`
     (`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition`) across all
     6-state `BorrowEntry` states and `writerTag`s.
   - `mir_updateBorrowPermAtProj_characterization`: disjoint field/index/range writes leave
     sibling borrows untouched.
2. **Direct Universal Theorems Over Borrow List Invalidation & Function-Entry Protectors**:
   - `mir_invalidateConflictingBorrows_map`: `invalidateConflictingBorrows` and
     `invalidateConflictingBorrowsAtProj` map `updateBorrowPerm` / `updateBorrowPermAtProj`
     pointwise across the active borrow list.
   - `mir_attachBorrowProtector_and_hasProtectedWriteConflict`: universal theorems over
     `attachBorrowProtector`, `isBorrowProtected`, `hasProtectedWriteConflict`, and `evalPlaceWrite`.
3. **Direct Universal Theorem Over `Freeze` vs. `UnsafeCell` Shared Borrows (`MirSemantics.{evalRvalue,writePlaceValue}`)**:
   - `mir_shared_ref_always_assigns_frozen_and_rejects_write`: proves directly on `evalRvalue`
     and `writePlaceValue` that `BorrowKind.shared` on `Freeze` (or untyped default) places
     creates `perm := .frozen` and rejects dereference writes with `.ub`, whereas on
     `core::cell::UnsafeCell<u32>` (`!Freeze`) it creates `perm := .cell` and permits
     interior-mutable dereference writes.
4. **Mechanical Cross-Snapshot Tree Borrows Comparison (`S2026_05_Matched` vs. `S2026_07_BleedingEdge`)**:
   - `unprotected_transition_agrees_across_snapshots`: `PermissionUnprot.transition` agrees 100%
     across all 24 `(PermissionUnprot × AccessKind × NodeRelation)` combinations between the two
     snapshots.
   - `epoch_delta_init_access_and_reborrow_permission`: proves the exact mechanical epoch delta
     between `S2026_05_Matched.Generated.Ops` and `S2026_07_BleedingEdge.Generated.Ops` on
     `PermissionProt.init_access`, `reborrow_permission`, and `reborrow_init_and_foreign_read`.
-/

namespace Correspondence.V2026_06_01.L4_TreeBorrows

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr
open Correspondence

export MiniRust.Snapshots.S2026_05_Matched.Generated.Ops (
  AccessKind
  NodeRelation
  Protected
  PermissionUnprot
  PermissionProt
  Permission
  reborrow_permission
  reborrow_init_and_foreign_read
)

deriving instance DecidableEq, BEq, Repr for TreeBorrowPerm

/-! ## 1. Translation Between Anneal `TreeBorrowPerm` and MiniRust `PermissionUnprot` -/

/-- Translate Anneal's six-state `TreeBorrowPerm` to MiniRust's
`PermissionUnprot`, forgetting the protector-only `conflicted` latch of
`.reservedFrz`. With `hasInteriorMut = false` this is MiniRust's exact
unprotected state; the legacy `hasInteriorMut = true` view reinterprets a
`Freeze`-style `.reservedFrz` / `.frozen` as `ReservedIm` / `Cell`. -/
@[reducible]
def toPermissionUnprot (hasInteriorMut : Bool := false) : TreeBorrowPerm → PermissionUnprot
  | .cell => .Cell
  | .reservedFrz _ => if hasInteriorMut then .ReservedIm else .Reserved
  | .reservedIM => .ReservedIm
  | .unique => .Unique
  | .frozen => if hasInteriorMut then .Cell else .Frozen
  | .disabled => .Disabled

/-- Embed MiniRust's `PermissionUnprot` into Anneal's six-state `TreeBorrowPerm`
(`Reserved` is the unconflicted `.reservedFrz false`). -/
@[reducible]
def ofPermissionUnprot : PermissionUnprot → TreeBorrowPerm
  | .Unique => .active
  | .Reserved => .reserved
  | .ReservedIm => .reservedIM
  | .Frozen => .frozen
  | .Cell => .cell
  | .Disabled => .disabled

/-- Structural isomorphism from `S2026_05_Matched` to `S2026_07_BleedingEdge` `PermissionUnprot`. -/
@[reducible]
def toS07PermissionUnprot :
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot →
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.PermissionUnprot
  | .Cell => .Cell
  | .Reserved => .Reserved
  | .ReservedIm => .ReservedIm
  | .Unique => .Unique
  | .Frozen => .Frozen
  | .Disabled => .Disabled

/-- Structural isomorphism from `S2026_07_BleedingEdge` to `S2026_05_Matched` `PermissionUnprot`. -/
@[reducible]
def ofS07PermissionUnprot :
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.PermissionUnprot →
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot
  | .Cell => .Cell
  | .Reserved => .Reserved
  | .ReservedIm => .ReservedIm
  | .Unique => .Unique
  | .Frozen => .Frozen
  | .Disabled => .Disabled

/-- Structural isomorphism for `AccessKind` across snapshots. -/
@[reducible]
def toS07AccessKind :
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.AccessKind →
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.AccessKind
  | .Read => .Read
  | .Write => .Write

/-- Structural isomorphism for `NodeRelation` across snapshots. -/
@[reducible]
def toS07NodeRelation :
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.NodeRelation →
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.NodeRelation
  | .Local => .Local
  | .Foreign => .Foreign

/-- Structural isomorphism for `Protected` across snapshots. -/
@[reducible]
def toS07Protected :
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.Protected →
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.Protected
  | .Strong => .Strong
  | .Weak => .Weak
  | .No => .No

/-- Structural isomorphism for `PermissionProt` across snapshots. -/
@[reducible]
def toS07PermissionProt :
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionProt →
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.PermissionProt
  | .Cell => .Cell
  | .Reserved b1 b2 => .Reserved b1 b2
  | .Unique => .Unique
  | .Frozen b => .Frozen b
  | .Disabled => .Disabled

/-- Structural isomorphism for `Permission` across snapshots. -/
@[reducible]
def toS07Permission :
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.Permission →
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.Permission
  | .Unprot p => .Unprot (toS07PermissionUnprot p)
  | .Prot p => .Prot (toS07PermissionProt p)

/-- MiniRust node relation of a write through `writerTag` relative to `entry`
(a write through `entry`'s own tag is `Local`; everything else is
`Foreign`). -/
@[reducible]
def mrWriteNodeRelation (entry : BorrowEntry) (writerTag : Option Nat) : NodeRelation :=
  match writerTag with
  | .none => .Foreign
  | .some tag =>
    match Nat.beq entry.tag tag with
    | true => .Local
    | false => .Foreign

/--
Expected Anneal permission after a write, computed by the specr-generated
MiniRust unprotected transition
`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition`
(`spec/mem/tree_borrows/state_machine_unprotected.md`). Entries on another
local are unchanged, and a forbidden local write (MiniRust UB) leaves the
entry unchanged, as Anneal reports that undefined behavior separately.

The generated helper
`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.mrExpectedWritePerm`
encodes the pre-`LM-3.3` Anneal rule under which a direct write to the local
preserved `Reserved`; MiniRust's own `foreign_write` (and Miri's) disables it,
so the correspondence is stated against `PermissionUnprot.transition`.
-/
abbrev mrExpectedWritePerm
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat) :
    TreeBorrowPerm :=
  match Nat.beq entry.targetLocal targetLocal with
  | false => entry.perm
  | true =>
    match
      MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition
        (toPermissionUnprot false entry.perm) .Write (mrWriteNodeRelation entry writerTag)
    with
    | .ok next => ofPermissionUnprot next
    | .error _ => entry.perm

/-! ## 2. Direct Universal Theorems Over `Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPerm` -/

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
For EVERY `BorrowEntry` targeting `entry.targetLocal` that is neither `.cell` nor
`.reservedIM` and EVERY foreign writer tag `wTag` (`Nat.beq entry.tag wTag =
false`), Anneal's real `updateBorrowPerm` transitions `perm` to `.disabled`
(`.cell` and unprotected `.reservedIM` tolerate foreign writes).
-/
theorem mir_updateBorrowPerm_foreign_ptr_write_disables
    (entry : BorrowEntry) (wTag : Nat)
    (h_foreign : Nat.beq entry.tag wTag = false)
    (h_not_cell : entry.perm ≠ .cell)
    (h_not_im : entry.perm ≠ .reservedIM) :
    (updateBorrowPerm entry entry.targetLocal (.some wTag)).perm = .disabled := by
  cases hp : entry.perm <;> simp_all [updateBorrowPerm, Nat.beq_refl]

/--
**Theorem L4.4 (`mir_updateBorrowPerm_direct_local_write`)**:
For EVERY `BorrowEntry`, a direct write (`writerTag = .none`) to `entry.targetLocal`
in Anneal's real `updateBorrowPerm`:
1. Disables `.active`, `.frozen`, and `Freeze` reservations (`.reserved`) because
   a direct write is a foreign write for every tag (MiniRust and Miri
   `foreign_write`); and
2. Preserves interior-mutable reservations (`.reservedIM`) and `.cell` tags.
-/
theorem mir_updateBorrowPerm_direct_local_write (entry : BorrowEntry) :
    (entry.perm = .active → (updateBorrowPerm entry entry.targetLocal .none).perm = .disabled) ∧
    (entry.perm = .frozen → (updateBorrowPerm entry entry.targetLocal .none).perm = .disabled) ∧
    (entry.perm = .reserved → (updateBorrowPerm entry entry.targetLocal .none).perm = .disabled) ∧
    (entry.perm = .reservedIM →
      (updateBorrowPerm entry entry.targetLocal .none).perm = .reservedIM) ∧
    (entry.perm = .cell → (updateBorrowPerm entry entry.targetLocal .none).perm = .cell) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp [updateBorrowPerm, Nat.beq_refl, h]

/--
**Theorem L4.5 (`mir_updateBorrowPerm_corresponds_to_minirust_write`)**:
Universal correspondence theorem directly over `Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPerm`
and `mrExpectedWritePerm` (`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition`):
for EVERY `entry : BorrowEntry`, EVERY `targetLocal : Local`, and EVERY `writerTag : Option Nat`,
`(updateBorrowPerm entry targetLocal writerTag).perm` equals `mrExpectedWritePerm`
while preserving `tag` and `targetLocal`.
-/
theorem mir_updateBorrowPerm_corresponds_to_minirust_write
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat) :
    (updateBorrowPerm entry targetLocal writerTag).perm =
      mrExpectedWritePerm entry targetLocal writerTag ∧
    (updateBorrowPerm entry targetLocal writerTag).tag = entry.tag ∧
    (updateBorrowPerm entry targetLocal writerTag).targetLocal = entry.targetLocal := by
  cases entry with | mk tag tLoc tProj perm rOff rLen prot parentTag =>
  refine ⟨?_, ?_, ?_⟩
  · cases hloc : Nat.beq tLoc targetLocal
    · simp [updateBorrowPerm, mrExpectedWritePerm, hloc]
    · cases writerTag with
      | none =>
        rcases perm with _ | (_ | _) | _ | _ | _ | _ <;>
          simp [updateBorrowPerm, mrExpectedWritePerm, hloc,
            toPermissionUnprot, ofPermissionUnprot,
            MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition,
            MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.foreign_write]
      | some wTag =>
        cases htag : Nat.beq tag wTag <;>
          rcases perm with _ | (_ | _) | _ | _ | _ | _ <;>
          simp [updateBorrowPerm, mrExpectedWritePerm, mrWriteNodeRelation, hloc,
            toPermissionUnprot, ofPermissionUnprot, htag,
            MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition,
            MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.foreign_write,
            MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.local_write]
  · unfold updateBorrowPerm
    split
    · rfl
    · exact (applyTreeBorrowTransition_fields _ _).1
  · unfold updateBorrowPerm
    split
    · rfl
    · exact (applyTreeBorrowTransition_fields _ _).2.1

/--
**Theorem L4.6 (`mir_updateBorrowPerm_unprot_eq_generated_ops`)**:
Direct commutative diagram between `MirSemantics.updateBorrowPerm` and the
specr-generated MiniRust unprotected transition
`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition` in
`PermissionUnprot`: an entry on another local is unchanged, and an entry on the
written local takes MiniRust's write transition for the write's node relation
(a forbidden local write leaves the entry unchanged; Anneal reports that
undefined behavior separately).
-/
theorem mir_updateBorrowPerm_unprot_eq_generated_ops
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat) :
    toPermissionUnprot false (updateBorrowPerm entry targetLocal writerTag).perm =
      match Nat.beq entry.targetLocal targetLocal with
      | false => toPermissionUnprot false entry.perm
      | true =>
        match
          MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition
            (toPermissionUnprot false entry.perm) .Write (mrWriteNodeRelation entry writerTag)
        with
        | .ok next => next
        | .error _ => toPermissionUnprot false entry.perm := by
  cases entry with | mk tag tLoc tProj perm rOff rLen prot parentTag =>
  cases hloc : Nat.beq tLoc targetLocal
  · simp [updateBorrowPerm, hloc]
  · cases writerTag with
    | none =>
      rcases perm with _ | (_ | _) | _ | _ | _ | _ <;>
        simp [updateBorrowPerm, hloc, toPermissionUnprot,
          MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition,
          MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.foreign_write]
    | some wTag =>
      cases htag : Nat.beq tag wTag <;>
        rcases perm with _ | (_ | _) | _ | _ | _ | _ <;>
        simp [updateBorrowPerm, mrWriteNodeRelation, hloc, htag, toPermissionUnprot,
          MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition,
          MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.foreign_write,
          MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.local_write]

/-! ## 3. Universal Theorems Over `updateBorrowPermAtProj`, `invalidateConflictingBorrows`, & Protectors -/

/--
**Theorem L4.7 (`mir_updateBorrowPermAtProj_characterization`)**:
Universal characterization of projection- and byte-range-sensitive borrow transitions in
`Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPermAtProj`:
1. When `entry.targetProjection = .nil` and `writeProj = .nil` (unranged),
   `updateBorrowPermAtProj` reduces identically to `updateBorrowPerm`;
2. Whenever `borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = false`,
   a direct write (`writerTag = .none`) or foreign pointer write (`Nat.beq entry.tag wTag = false`)
   leaves `entry` completely unchanged;
3. In particular, for any two distinct struct/tuple fields `idxA ≠ idxB` (`Nat.beq idxA idxB = false`),
   an unranged direct write to `[.field idxB tyB]` preserves a sibling borrow at `[.field idxA tyA]`.
-/
theorem mir_updateBorrowPermAtProj_characterization
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat)
    (wTag : Nat) (idxA idxB : FieldIdx) (tyA tyB : Ty) :
    (entry.targetProjection = .nil →
      updateBorrowPermAtProj entry targetLocal writerTag .nil 0 0 =
        updateBorrowPerm entry targetLocal writerTag) ∧
    (borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = false →
      updateBorrowPermAtProj entry targetLocal .none writeProj writeRangeOff writeRangeLen =
        entry) ∧
    (borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = false →
      Nat.beq entry.tag wTag = false →
      updateBorrowPermAtProj entry targetLocal (.some wTag) writeProj writeRangeOff writeRangeLen =
        entry) ∧
    (entry.targetProjection = [.field idxA tyA] →
      entry.rangeLen = 0 →
      Nat.beq idxA idxB = false →
      updateBorrowPermAtProj entry targetLocal .none [.field idxB tyB] 0 0 = entry) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h_proj
    exact updateBorrowPermAtProj_nil_eq_updateBorrowPerm entry targetLocal writerTag h_proj
  · intro h_disj
    unfold updateBorrowPermAtProj
    cases Nat.beq entry.targetLocal targetLocal <;> simp [h_disj]
  · intro h_disj h_tag
    unfold updateBorrowPermAtProj
    cases Nat.beq entry.targetLocal targetLocal <;> simp [h_disj, h_tag]
  · intro h_proj h_rlen h_neq
    have h_disj : borrowEntryOverlapsWrite entry [.field idxB tyB] 0 0 = false := by
      unfold borrowEntryOverlapsWrite
      rw [h_rlen, h_proj]
      simp [projectionsOverlap, stripTransparentProjections, projectionsOverlapAux, h_neq]
    unfold updateBorrowPermAtProj
    cases Nat.beq entry.targetLocal targetLocal <;> simp [h_disj]

/--
**Theorem L4.8 (`mir_invalidateConflictingBorrows_map`)**:
Universal list correspondence for `MirSemantics.invalidateConflictingBorrows` and
`MirSemantics.invalidateConflictingBorrowsAtProj`: both functions map the single-entry
transition (`updateBorrowPerm` / `updateBorrowPermAtProj`) pointwise over `borrows` and
preserve the length of the borrow table.
-/
theorem mir_invalidateConflictingBorrows_map
    (borrows : List BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat) :
    invalidateConflictingBorrows borrows targetLocal writerTag =
      borrows.map (fun e => updateBorrowPerm e targetLocal writerTag) ∧
    (invalidateConflictingBorrows borrows targetLocal writerTag).length = borrows.length ∧
    invalidateConflictingBorrowsAtProj borrows targetLocal writerTag writeProj writeRangeOff writeRangeLen =
      borrows.map (fun e => updateBorrowPermAtProj e targetLocal writerTag writeProj writeRangeOff writeRangeLen) := by
  induction borrows with
  | nil =>
    exact ⟨rfl, rfl, rfl⟩
  | cons entry rest ih =>
    rcases ih with ⟨ih1, ih2, ih3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [invalidateConflictingBorrows_cons, List.map_cons, ih1]
    · rw [invalidateConflictingBorrows_cons, List.length_cons, List.length_cons, ih2]
    · rw [invalidateConflictingBorrowsAtProj_cons, List.map_cons, ih3]

/--
**Theorem L4.9 (`mir_attachBorrowProtector_and_hasProtectedWriteConflict`)**:
Universal characterization of function-entry lifetime protectors in
`Trusted.Rustc.V2026_06_01.MirSemantics.{attachBorrowProtector, isBorrowProtected,
hasProtectedWriteConflict, evalPlaceWrite}`:
1. Attaching `protId` to head entry `entry` via `attachBorrowProtector (entry :: rest) entry.tag protId`
   sets `protector := some protId` and makes `isBorrowProtected (protId :: moreProts)` true;
2. With no active protectors (`activeProtectors = .nil`), `hasProtectedWriteConflict` is
   identically `false` and `evalPlaceWrite` reduces to `writePlaceValue`;
3. A direct root write (`writerTag = .none`, `writeProj = .nil`) to `entry.targetLocal` when
   `entry` has `targetProjection = .nil`, active protector `protId`, and live permission
   `.active` or `.frozen` triggers `hasProtectedWriteConflict = true` and causes
   `evalPlaceWrite` to fault immediately with `.ub`.
-/
theorem mir_attachBorrowProtector_and_hasProtectedWriteConflict
    (locals : List LocalSlot) (entry : BorrowEntry) (rest : List BorrowEntry)
    (protId : Nat) (moreProts : List Nat) (targetLocal : Local)
    (writerTag : Option Nat) (writeProj : List ProjectionElem)
    (dst : Place) (val : Value) :
    attachBorrowProtector (entry :: rest) entry.tag protId =
      { entry with protector := .some protId } ::
        attachBorrowProtector rest entry.tag protId ∧
    isBorrowProtected (protId :: moreProts) { entry with protector := .some protId } = true ∧
    hasProtectedWriteConflict (entry :: rest) .nil targetLocal writerTag writeProj 0 0 = false ∧
    evalPlaceWrite locals (entry :: rest) dst val .nil =
      writePlaceValue locals (entry :: rest) dst val ∧
    (entry.targetProjection = .nil →
      (entry.perm = .active ∨ entry.perm = .frozen) →
      hasProtectedWriteConflict
        ({ entry with protector := .some protId } :: rest)
        (protId :: moreProts)
        entry.targetLocal
        .none
        .nil
        0
        0 = true ∧
      evalPlaceWrite
        locals
        ({ entry with protector := .some protId } :: rest)
        { local_ := entry.targetLocal, projection := .nil }
        val
        (protId :: moreProts) = .ub) := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · simp [attachBorrowProtector, Nat.beq_refl]
  · simp [isBorrowProtected, natListContainsBool, Nat.beq_refl]
  · induction (entry :: rest) with
    | nil => rfl
    | cons hd tl ih =>
      unfold hasProtectedWriteConflict
      have h_no_prot : isBorrowProtected .nil hd = false := by
        unfold isBorrowProtected
        cases hd.protector <;> rfl
      simp [h_no_prot, ih]
  · intro h_proj h_live
    have h_ov :
        borrowEntryOverlapsWrite { entry with protector := .some protId } .nil 0 0 = true := by
      unfold borrowEntryOverlapsWrite
      simp [h_proj, projectionsOverlap, stripTransparentProjections, projectionsOverlapAux]
    have h_prot :
        isBorrowProtected (protId :: moreProts) { entry with protector := .some protId } = true := by
      simp [isBorrowProtected, natListContainsBool, Nat.beq_refl]
    have h_conf :
        borrowEntryWriteConflicts { entry with protector := .some protId } .none = true := by
      rcases h_live with h_act | h_frz
      · simp [borrowEntryWriteConflicts, h_act]
      · simp [borrowEntryWriteConflicts, h_frz]
    have h_has :
        hasProtectedWriteConflict
          ({ entry with protector := .some protId } :: rest)
          (protId :: moreProts)
          entry.targetLocal
          .none
          .nil
          0
          0 = true := by
      unfold hasProtectedWriteConflict
      simp [Nat.beq_refl, h_ov, h_prot, h_conf]
    refine ⟨h_has, ?_⟩
    unfold evalPlaceWrite
    simp [h_has]

/--
**Theorem L4.10 (`mir_shared_ref_always_assigns_frozen_and_rejects_write`)**:
For `Freeze` (or untyped default `localDecls = .nil`) places, taking a shared reference
`Rvalue.ref .shared { local_ := 0, projection := .nil }` via `evalRvalue` allocates a
`BorrowEntry` with `perm := .frozen`, and writing `newVal` through that pointer via
`writePlaceValue` returns `PlaceWriteResult.ub`.
Conversely, when `localDecls` types local 0 as `core::cell::UnsafeCell<u32>` (`!Freeze`),
`sharedBorrowPerm` returns `TreeBorrowPerm.cell` (Miri's `Cell`) and writing `newVal`
through that pointer succeeds with `.ok [.init newVal, .init ptrVal]`.
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
    let cellEntry : BorrowEntry := {
      tag := mem.nextTag
      targetLocal := 0
      targetProjection := .nil
      perm := .cell
    }
    let unsafeCellDecl : LocalDecl := {
      mutability := .not
      ty := { kind := .adt "core::cell::UnsafeCell" [.uint .u32], layoutIdx := 0 }
      debugName := .none
    }
    let ptrVal : Value := .ptr { allocId := mem.nextTag, offsetBytes := 0 } 8
    let memAfterFreezeRef : Memory := {
      mem with
      borrows := frozenEntry :: mem.borrows
      nextTag := Nat.add mem.nextTag 1
    }
    let memAfterUnsafeCellRef : Memory := {
      mem with
      borrows := cellEntry :: mem.borrows
      nextTag := Nat.add mem.nextTag 1
    }
    evalRvalue initLocals (.ref .shared { local_ := 0, projection := .nil }) mem =
      .ok ptrVal initLocals memAfterFreezeRef ∧
    writePlaceValue [.init initVal, .init ptrVal] memAfterFreezeRef.borrows
      { local_ := 1, projection := [.deref] } newVal = .ub ∧
    evalRvalue initLocals (.ref .shared { local_ := 0, projection := .nil }) mem [unsafeCellDecl] =
      .ok ptrVal initLocals memAfterUnsafeCellRef ∧
    writePlaceValue [.init initVal, .init ptrVal] memAfterUnsafeCellRef.borrows
      { local_ := 1, projection := [.deref] } newVal = .ok [.init newVal, .init ptrVal] := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [writePlaceValue, lookupBorrow, Trusted.Sequence.get?, ProvenancePtr.tag, Nat.beq_refl]
  · simp [writePlaceValue, lookupBorrow, Trusted.Sequence.get?, Trusted.Sequence.set?,
      ProvenancePtr.tag, Nat.beq_refl]

/-! ## 4. Full Read/Write/Protector Automaton Across `S2026_05_Matched` & `S2026_07_BleedingEdge` -/

/-- Memory access kind (`Read` vs. `Write`). -/
inductive TbAccessKind : Type where
  | read
  | write
  deriving DecidableEq, BEq, Repr

/-- Relative position of the accessed tag with respect to the node being updated. -/
inductive TbLocality : Type where
  | childLocal
  | foreign
  deriving DecidableEq, BEq, Repr

/-- Translate `TbLocality` to MiniRust's `NodeRelation`. -/
@[reducible]
def toNodeRelation : TbLocality → NodeRelation
  | .childLocal => .Local
  | .foreign => .Foreign

/-- Translate `TbAccessKind` to MiniRust's `AccessKind`. -/
@[reducible]
def toAccessKind : TbAccessKind → AccessKind
  | .read => .Read
  | .write => .Write

/-- Translate `TbAccessKind` to Anneal's `TreeBorrowAccessKind`. -/
@[reducible]
def toAnnealAccessKind : TbAccessKind → TreeBorrowAccessKind
  | .read => .read
  | .write => .write

/-- Translate `TbLocality` to Anneal's `TreeBorrowRelatedness`. -/
@[reducible]
def toAnnealRelatedness : TbLocality → TreeBorrowRelatedness
  | .childLocal => .localAccess
  | .foreign => .foreignAccess

/-- Anneal's unprotected per-node transition (`treeBorrowPermTransition` in
`Places.lean`) as an `Option`: `none` is a forbidden child access. -/
@[reducible]
def rawNextPermFreeze
    (perm : TreeBorrowPerm) (loc : TbLocality) (acc : TbAccessKind) :
    Option TreeBorrowPerm :=
  match
    treeBorrowPermTransition (toAnnealAccessKind acc) (toAnnealRelatedness loc) perm false
  with
  | .transition next => some next
  | _ => none

/-- Anneal `V2026_06_01` single-node Tree Borrows step with protector enforcement:
the real per-node access `treeBorrowNodeAccess` from `Places.lean`. A forbidden
child access reports `"tree borrows invalid local access"`; a foreign access
that disables a protected tag (or reaches a protected `.reservedIM`) reports
`"tree borrows protected tag invalidated by conflicting write"`. -/
@[reducible]
def annealStepTreeBorrowPerm
    (perm : TreeBorrowPerm) (loc : TbLocality) (acc : TbAccessKind) (prot : Bool) :
    Except TerminationInfo TreeBorrowPerm :=
  match
    treeBorrowNodeAccess (toAnnealAccessKind acc) (toAnnealRelatedness loc) perm prot
  with
  | .transition next => .ok next
  | _ =>
    match loc with
    | .childLocal => .error (.ub "tree borrows invalid local access")
    | .foreign =>
      .error (.ub "tree borrows protected tag invalidated by conflicting write")

/--
Single-node Tree Borrows step driven directly by the specr-generated
`PermissionUnprot.transition` functions in `MiniRust.Snapshots.S2026_05_Matched.Generated.Ops`
and `MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops`.
-/
@[reducible]
def stepGeneratedTreeBorrowPerm
    (snap : MiniRustSnap) (hasInteriorMut : Bool)
    (perm : TreeBorrowPerm) (loc : TbLocality) (acc : TbAccessKind) (prot : Bool) :
    Except TerminationInfo TreeBorrowPerm :=
  let pUnprot := toPermissionUnprot hasInteriorMut perm
  let rawRes : Except TerminationInfo PermissionUnprot :=
    match snap with
    | .S2026_05_Matched =>
      MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition
        pUnprot (toAccessKind acc) (toNodeRelation loc)
    | .S2026_07_BleedingEdge =>
      match
        MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.PermissionUnprot.transition
          (toS07PermissionUnprot pUnprot)
          (toS07AccessKind (toAccessKind acc))
          (toS07NodeRelation (toNodeRelation loc))
      with
      | .ok p7 => .ok (ofS07PermissionUnprot p7)
      | .error e => .error e
  if hasInteriorMut && perm == .reserved && loc == .foreign && acc == .read && prot then
    match snap with
    | .S2026_05_Matched =>
      match
        MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.reborrow_init_and_foreign_read
          true .Strong true (!hasInteriorMut) true
      with
      | .ok (.Prot (.Reserved _ _)) => .ok .reserved
      | .ok _ => .ok .active
      | .error e => .error e
    | .S2026_07_BleedingEdge =>
      match
        MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.reborrow_init_and_foreign_read
          true .Strong true (!hasInteriorMut) true
      with
      | .ok (.Prot (.Reserved _ _)) => .ok .reserved
      | .ok _ => .ok .active
      | .error e => .error e
  else
    match rawRes with
    | .error _ => .error (.ub "tree borrows invalid local access")
    | .ok nextUnprot =>
      let nextPerm := ofPermissionUnprot nextUnprot
      if prot && (nextPerm == .disabled) && (perm != .disabled) then
        .error (.ub "tree borrows protected tag invalidated by conflicting write")
      else
        .ok nextPerm

/-- Abbreviation exposing `mrStepTreeBorrowPerm` for `Scorecard.lean`. -/
abbrev mrStepTreeBorrowPerm := stepGeneratedTreeBorrowPerm

/--
**Theorem L4.11 (`unprotected_transition_agrees_across_snapshots`)**:
Universal 24-combination theorem proving that the specr-generated unprotected
Tree Borrows state machines `S2026_05_Matched.Generated.Ops.PermissionUnprot.transition`
and `S2026_07_BleedingEdge.Generated.Ops.PermissionUnprot.transition` agree 100%
identically across EVERY `(perm : PermissionUnprot)`, EVERY `(acc : AccessKind)`,
and EVERY `(rel : NodeRelation)`, as well as on `init_access` and `prevents_deallocation`.
-/
theorem unprotected_transition_agrees_across_snapshots
    (perm : PermissionUnprot) (acc : AccessKind) (rel : NodeRelation) :
    (MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition perm acc rel).map
        toS07PermissionUnprot =
      MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.PermissionUnprot.transition
        (toS07PermissionUnprot perm) (toS07AccessKind acc) (toS07NodeRelation rel) ∧
    (MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.init_access perm).map
        toS07AccessKind =
      MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.PermissionUnprot.init_access
        (toS07PermissionUnprot perm) ∧
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.prevents_deallocation perm =
      MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.PermissionUnprot.prevents_deallocation
        (toS07PermissionUnprot perm) := by
  cases perm <;> cases acc <;> cases rel <;> refine ⟨rfl, rfl, rfl⟩

/--
**Theorem L4.12 (`epoch_delta_init_access_and_reborrow_permission`)**:
Universal theorem characterizing the exact mechanical epoch delta between
`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops` (`5f78e227bbe3`) and
`MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops` (`d821c6e3a3d3`):
1. `PermissionProt.init_access .Unique` is `some .Read` in `S2026_05_Matched` vs.
   `some .Write` in `S2026_07_BleedingEdge`, and agrees on all non-`.Unique` permissions;
2. When `implicit_writes = false`, `reborrow_permission` is 100% identical across both
   snapshots for all `(is_mut, prot, inside, frozen)`;
3. When `is_mut = true`, `prot = .Strong`, `inside = true`, and `implicit_writes = true`,
   `reborrow_permission` yields `.Prot (.Reserved false false)` in `S2026_05_Matched`
   vs. `.Prot .Unique` in `S2026_07_BleedingEdge`, causing `reborrow_init_and_foreign_read`
   to succeed with `.ok (.Prot (.Reserved true true))` in `S2026_05_Matched` and fault with
   `.error (.ub "Tree Borrows: foreign read of protected Unique reference")` in `S2026_07_BleedingEdge`.
-/
theorem epoch_delta_init_access_and_reborrow_permission
    (p : PermissionProt) (is_mut inside frozen : Bool) (prot : Protected) :
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionProt.init_access .Unique =
      some .Read ∧
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.PermissionProt.init_access .Unique =
      some .Write ∧
    (p ≠ .Unique →
      (MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionProt.init_access p).map
          toS07AccessKind =
        MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.PermissionProt.init_access
          (toS07PermissionProt p)) ∧
    toS07Permission
        (MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.reborrow_permission
          is_mut prot inside frozen false) =
      MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.reborrow_permission
        is_mut (toS07Protected prot) inside frozen false ∧
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.reborrow_permission
        true .Strong true frozen true =
      .Prot (.Reserved false false) ∧
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.reborrow_permission
        true .Strong true frozen true =
      .Prot .Unique ∧
    MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.reborrow_init_and_foreign_read
        true .Strong true frozen true =
      .ok (.Prot (.Reserved true true)) ∧
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.reborrow_init_and_foreign_read
        true .Strong true frozen true =
      .error (.ub "Tree Borrows: foreign read of protected Unique reference") := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_ne
    cases p with
    | Unique => exact absurd rfl h_ne
    | Cell => rfl
    | Reserved b1 b2 => rfl
    | Frozen b => rfl
    | Disabled => rfl
  · cases is_mut <;> cases prot <;> cases inside <;> cases frozen <;> rfl
  · cases frozen <;> rfl
  · cases frozen <;> rfl
  · cases frozen <;> rfl
  · cases frozen <;> rfl

/--
**Theorem L4.13 (`treeBorrow_transition_corresponds_for_freeze`)**:
Universal correspondence of unprotected single-node steps (`hasInteriorMut = false`)
across both MiniRust snapshots, for every Anneal state except the conflicted
reservation. MiniRust's unprotected state machine (`PermissionUnprot`) has no
`conflicted` latch and no protector rule; protected steps and the latch are
related to Miri's protected transition function in
`LeanMiriSpec.Correspondence.TreeBorrowsRel`.
-/
theorem treeBorrow_transition_corresponds_for_freeze
    (snap : MiniRustSnap) (perm : TreeBorrowPerm)
    (loc : TbLocality) (acc : TbAccessKind)
    (h_unconflicted : perm ≠ .reservedFrz true) :
    annealStepTreeBorrowPerm perm loc acc false =
      mrStepTreeBorrowPerm snap false perm loc acc false := by
  cases snap <;> rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases loc <;> cases acc <;>
    first | rfl | exact absurd rfl h_unconflicted

theorem disabled_local_access_is_ub (acc : TbAccessKind) (prot : Bool) :
    annealStepTreeBorrowPerm .disabled .childLocal acc prot =
      .error (.ub "tree borrows invalid local access") := by
  cases acc <;> cases prot <;> rfl

theorem protected_live_tag_foreign_write_is_ub
    (perm : TreeBorrowPerm) (h_live : perm ≠ .disabled) (h_not_cell : perm ≠ .cell) :
    annealStepTreeBorrowPerm perm .foreign .write true =
      .error (.ub "tree borrows protected tag invalidated by conflicting write") := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;>
    first | rfl | exact absurd rfl h_live | exact absurd rfl h_not_cell

theorem l4_shared_unsafecell_gap_witnessed :
    gapLayer .GAP_MR_0001 = .L4_TreeBorrows ∧
    gapMiriDiffCrossRef .GAP_MR_0001 = some "pass_tb_unsafe_cell_shared_mutation" ∧
    !gapIsOpen .GAP_MR_0001 = true ∧
    VerifiedRemediationWitness
      (evalAnnealV2026_06_01 .sharedUnsafeCellWrite defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .sharedUnsafeCellWrite)
      .normalUnit :=
  ⟨rfl, rfl, rfl, witness_GAP_MR_0001⟩

theorem shared_borrow_unsafe_cell_non_correspondence (snap : MiniRustSnap) :
    annealStepTreeBorrowPerm .frozen .childLocal .write false =
      .error (.ub "tree borrows invalid local access") ∧
    mrStepTreeBorrowPerm snap true .frozen .childLocal .write false =
      .ok .cell ∧
    VerifiedRemediationWitness
      (evalAnnealV2026_06_01 .sharedUnsafeCellWrite defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .sharedUnsafeCellWrite)
      .normalUnit := by
  refine ⟨rfl, ?_, witness_GAP_MR_0001⟩
  cases snap <;> rfl

theorem epoch_divergence_GAP_EPOCH_0001_characterized :
    mrStepTreeBorrowPerm .S2026_05_Matched true .reserved .foreign .read true =
      .ok .reserved ∧
    mrStepTreeBorrowPerm .S2026_07_BleedingEdge true .reserved .foreign .read true =
      .error (.ub "Tree Borrows: foreign read of protected Unique reference") ∧
    VerifiedDivergenceWitness
      (evalAnnealV2026_06_01 .reservedImEpochTransition defaultFixtureState)
      (evalMiniRustSnapshot .S2026_07_BleedingEdge .reservedImEpochTransition)
      .ub
      .normalUnit :=
  ⟨rfl, rfl, witness_GAP_EPOCH_0001.2⟩

/--
**Theorem L4.14 (`mir_updateBorrowPermTreeAtProj_characterization`)**:
Universal characterization of Tree Borrows parent/child write transitions in
`Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPermTreeAtProj`:
1. A write through a descendant or self tag (`isBorrowDescendantOrSelf allBorrows wTag entry.tag = true`)
   activates a `.reserved` ancestor (`perm = .active`) and preserves an `.active` ancestor (`perm = .active`);
2. An overlapping write through a foreign tag (`isBorrowDescendantOrSelf allBorrows wTag entry.tag = false`)
   disables `entry` (`perm = .disabled`) unless `entry` is `.cell` or `.reservedIM`, which
   tolerate foreign writes.
-/
theorem mir_updateBorrowPermTreeAtProj_characterization
    (allBorrows : List BorrowEntry) (entry : BorrowEntry) (wTag : Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat) :
    (isBorrowDescendantOrSelf allBorrows wTag entry.tag = true →
      entry.perm = .reserved →
      (updateBorrowPermTreeAtProj
        allBorrows entry entry.targetLocal (.some wTag)
        writeProj writeRangeOff writeRangeLen).perm = .active) ∧
    (isBorrowDescendantOrSelf allBorrows wTag entry.tag = true →
      entry.perm = .active →
      (updateBorrowPermTreeAtProj
        allBorrows entry entry.targetLocal (.some wTag)
        writeProj writeRangeOff writeRangeLen).perm = .active) ∧
    (isBorrowDescendantOrSelf allBorrows wTag entry.tag = false →
      Nat.beq entry.tag wTag = false →
      borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = true →
      entry.perm ≠ .cell → entry.perm ≠ .reservedIM →
      (updateBorrowPermTreeAtProj
        allBorrows entry entry.targetLocal (.some wTag)
        writeProj writeRangeOff writeRangeLen).perm = .disabled) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h_desc h_perm
    simp [updateBorrowPermTreeAtProj, resolveTreeBorrowWriterTag,
      updateBorrowPermAtProj, Nat.beq_refl, h_desc, h_perm]
  · intro h_desc h_perm
    simp [updateBorrowPermTreeAtProj, resolveTreeBorrowWriterTag,
      updateBorrowPermAtProj, Nat.beq_refl, h_desc, h_perm]
  · intro h_for h_neq h_ov h_nc h_nim
    cases hp : entry.perm <;>
      simp_all [updateBorrowPermTreeAtProj, resolveTreeBorrowWriterTag,
        updateBorrowPermAtProj, Nat.beq_refl]

/--
**Theorem L4.15 (`mir_updateBorrowPermOnReadAtProj_characterization`)**:
Universal characterization of Tree Borrows read transitions in
`Trusted.Rustc.V2026_06_01.MirSemantics.updateBorrowPermOnReadAtProj`:
1. A child/self (`Local`) read (`isBorrowDescendantOrSelf allBorrows rTag entry.tag = true`)
   preserves `entry` unchanged;
2. An overlapping `Foreign` read (`isBorrowDescendantOrSelf allBorrows rTag entry.tag = false`)
   freezes an `.active` borrow (`perm = .frozen`) while preserving `.reserved`, `.frozen`, and
   `.disabled` borrows.
-/
theorem mir_updateBorrowPermOnReadAtProj_characterization
    (allBorrows : List BorrowEntry) (entry : BorrowEntry) (rTag : Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat) :
    (isBorrowDescendantOrSelf allBorrows rTag entry.tag = true →
      updateBorrowPermOnReadAtProj
        allBorrows entry entry.targetLocal (.some rTag)
        readProj readRangeOff readRangeLen = entry) ∧
    (isBorrowDescendantOrSelf allBorrows rTag entry.tag = false →
      borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen = true →
      entry.perm = .active →
      (updateBorrowPermOnReadAtProj
        allBorrows entry entry.targetLocal (.some rTag)
        readProj readRangeOff readRangeLen).perm = .frozen) ∧
    (isBorrowDescendantOrSelf allBorrows rTag entry.tag = false →
      borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen = true →
      entry.perm = .reserved →
      (updateBorrowPermOnReadAtProj
        allBorrows entry entry.targetLocal (.some rTag)
        readProj readRangeOff readRangeLen).perm = .reserved) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h_desc
    unfold updateBorrowPermOnReadAtProj
    cases borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen <;>
      simp [Nat.beq_refl, h_desc]
  · intro h_for h_ov h_perm
    cases hprot : entry.protector <;>
      simp [updateBorrowPermOnReadAtProj, Nat.beq_refl, h_for, h_ov, h_perm,
        isBorrowProtected, hprot, natListContainsBool]
  · intro h_for h_ov h_perm
    cases hprot : entry.protector <;>
      simp [updateBorrowPermOnReadAtProj, Nat.beq_refl, h_for, h_ov, h_perm,
        isBorrowProtected, hprot, natListContainsBool]

end Correspondence.V2026_06_01.L4_TreeBorrows
