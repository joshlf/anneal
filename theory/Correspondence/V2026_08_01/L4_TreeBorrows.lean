import Trusted.Rustc.V2026_08_01.MirSemantics.State
import Trusted.Rustc.V2026_08_01.MirSemantics.Places
import MiniRust.LibSpecr
import MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
import MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops
import Correspondence.Framework
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses
import Correspondence.V2026_08_01.L3_PlacesAndBasicMem

/-!
# `Correspondence.V2026_08_01.L4_TreeBorrows` — Universal Unconditional Tree Borrows Correspondence

Proves universal (`∀`) mathematical correspondence directly over
**`Trusted.Rustc.V2026_08_01.MirSemantics.{initProtectedReborrowPerm, protectedReborrowHasInitWrite,
rigidTyIsFreeze, tyIsFreeze, placeIsFreeze, updateBorrowPerm, updateBorrowPermAtProj,
invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj, hasProtectedWriteConflict,
attachBorrowProtector, evalPlaceWrite, evalRvalue, writePlaceValue}`**, linking them to the
specr-generated MiniRust `TreeBorrows` permission automata in
`MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops` and
`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops`:

1. **Direct Universal Theorems Over `MirSemantics.updateBorrowPerm` & `updateBorrowPermAtProj`**:
   - `mir_updateBorrowPerm_other_local_id`, `mir_updateBorrowPerm_self_write_activates_reserved`,
     `mir_updateBorrowPerm_foreign_ptr_write_disables`, `mir_updateBorrowPerm_direct_local_write`,
     `mir_updateBorrowPerm_corresponds_to_minirust_write`, `mir_updateBorrowPermAtProj_characterization`.
2. **Direct Universal Theorems Over Borrow List Invalidation & Function-Entry Protectors**:
   - `mir_invalidateConflictingBorrows_map`, `mir_attachBorrowProtector_and_hasProtectedWriteConflict`.
3. **Direct Universal `UnsafeCell` Shared-Borrow Theorem (`mir_shared_borrow_unsafe_cell_permits_write`,
   Closing `GAP-MR-0001`)**:
   - Proves over `placeIsFreeze`, `evalRvalue`, and `writePlaceValue` that taking a shared reference
     `Rvalue.ref .shared` to a `core::cell::UnsafeCell<T>` place assigns `perm := .reserved`
     (`!Freeze` interior mutability) and permits subsequent dereference writes!
4. **Direct Universal Protected Mutable Reborrow Theorem (`mir_protected_reborrow_init_write_matches_s2026_07`,
   Closing `GAP-EPOCH-0001` for `V2026_08_01` and Witnessing `GAP-EPOCH-0002` Against `S2026_05_Matched`)**:
   - Proves over `initProtectedReborrowPerm` and `protectedReborrowHasInitWrite` that `V2026_08_01`
     matches `S2026_07_BleedingEdge.Generated.Ops.reborrow_permission` unconditionally across all
     `(isMutable, isFreeze, implicitWrites)` combinations, and characterizes the intentional epoch
     delta `GAP-EPOCH-0002` against `S2026_05_Matched`.
-/

namespace Correspondence.V2026_08_01.L4_TreeBorrows

open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics
open MiniRust.LibSpecr
open Correspondence

export MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops (
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

/-- Translate Anneal's 4-state `TreeBorrowPerm` to MiniRust's `PermissionUnprot`. -/
@[reducible]
def toPermissionUnprot (hasInteriorMut : Bool := false) : TreeBorrowPerm → PermissionUnprot
  | .active => .Unique
  | .reserved => if hasInteriorMut then .ReservedIm else .Reserved
  | .frozen => if hasInteriorMut then .Cell else .Frozen
  | .disabled => .Disabled

/-- Project MiniRust's `PermissionUnprot` to Anneal's 4-state `TreeBorrowPerm`. -/
@[reducible]
def ofPermissionUnprot : PermissionUnprot → TreeBorrowPerm
  | .Unique => .active
  | .Reserved => .reserved
  | .ReservedIm => .reserved
  | .Frozen => .frozen
  | .Cell => .frozen
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

/--
Abbreviation wiring `mrExpectedWritePerm` directly to the generated
`MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.mrExpectedWritePerm` function.
-/
abbrev mrExpectedWritePerm
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat) :
    TreeBorrowPerm :=
  ofPermissionUnprot
    (MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.mrExpectedWritePerm
      (Nat.beq entry.targetLocal targetLocal)
      writerTag
      entry.tag
      (toPermissionUnprot false entry.perm))

/-! ## 2. Direct Universal Theorems Over `Trusted.Rustc.V2026_08_01.MirSemantics.updateBorrowPerm` -/

/--
**Theorem L4.1 (`mir_updateBorrowPerm_other_local_id`)**:
Writes to any `targetLocal ≠ entry.targetLocal` leave `entry` unchanged.
-/
theorem mir_updateBorrowPerm_other_local_id
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (h_other : Nat.beq entry.targetLocal targetLocal = false) :
    updateBorrowPerm entry targetLocal writerTag = entry := by
  simp [updateBorrowPerm, h_other]

/--
**Theorem L4.2 (`mir_updateBorrowPerm_self_write_activates_reserved`)**:
Writing through `writerTag = some entry.tag` transitions `.reserved → .active`.
-/
theorem mir_updateBorrowPerm_self_write_activates_reserved
    (entry : BorrowEntry) (h_res : entry.perm = .reserved) :
    (updateBorrowPerm entry entry.targetLocal (.some entry.tag)).perm = .active := by
  simp [updateBorrowPerm, Nat.beq_refl, h_res]

/--
**Theorem L4.3 (`mir_updateBorrowPerm_foreign_ptr_write_disables`)**:
Writing through a foreign pointer tag `wTag ≠ entry.tag` transitions `perm` to `.disabled`.
-/
theorem mir_updateBorrowPerm_foreign_ptr_write_disables
    (entry : BorrowEntry) (wTag : Nat)
    (h_foreign : Nat.beq entry.tag wTag = false) :
    (updateBorrowPerm entry entry.targetLocal (.some wTag)).perm = .disabled := by
  simp [updateBorrowPerm, Nat.beq_refl, h_foreign]

/--
**Theorem L4.4 (`mir_updateBorrowPerm_direct_local_write`)**:
Direct write (`writerTag = .none`) to `entry.targetLocal` disables `.active` and `.frozen`
while preserving `.reserved`.
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
Universal correspondence theorem directly over `Trusted.Rustc.V2026_08_01.MirSemantics.updateBorrowPerm`
and `MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.mrExpectedWritePerm`.
-/
theorem mir_updateBorrowPerm_corresponds_to_minirust_write
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat) :
    (updateBorrowPerm entry targetLocal writerTag).perm =
      mrExpectedWritePerm entry targetLocal writerTag ∧
    (updateBorrowPerm entry targetLocal writerTag).tag = entry.tag ∧
    (updateBorrowPerm entry targetLocal writerTag).targetLocal = entry.targetLocal := by
  cases entry with | mk tag tLoc tProj perm rOff rLen prot parentTag =>
  unfold updateBorrowPerm mrExpectedWritePerm
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.mrExpectedWritePerm
    toPermissionUnprot ofPermissionUnprot
  cases hloc : Nat.beq tLoc targetLocal <;>
    cases writerTag <;>
    cases perm <;>
    simp
  all_goals
    rename_i wTag
    cases htag : Nat.beq tag wTag <;> simp

/--
**Theorem L4.6 (`mir_updateBorrowPerm_unprot_eq_generated_ops`)**:
Direct commutative diagram between `MirSemantics.updateBorrowPerm` and
`MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.mrExpectedWritePerm` in `PermissionUnprot`.
-/
theorem mir_updateBorrowPerm_unprot_eq_generated_ops
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat) :
    toPermissionUnprot false (updateBorrowPerm entry targetLocal writerTag).perm =
      MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.mrExpectedWritePerm
        (Nat.beq entry.targetLocal targetLocal)
        writerTag
        entry.tag
        (toPermissionUnprot false entry.perm) := by
  cases entry with | mk tag tLoc tProj perm rOff rLen prot parentTag =>
  unfold updateBorrowPerm
    MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.mrExpectedWritePerm
    toPermissionUnprot
  cases hloc : Nat.beq tLoc targetLocal <;>
    cases writerTag <;>
    cases perm <;>
    simp
  all_goals
    rename_i wTag
    cases htag : Nat.beq tag wTag <;> simp

/-! ## 3. Universal Theorems Over `updateBorrowPermAtProj`, `invalidateConflictingBorrows`, & Protectors -/

/--
**Theorem L4.7 (`mir_updateBorrowPermAtProj_characterization`)**:
Universal characterization of projection- and byte-range-sensitive borrow transitions in
`Trusted.Rustc.V2026_08_01.MirSemantics.updateBorrowPermAtProj`.
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
`MirSemantics.invalidateConflictingBorrowsAtProj`.
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
Universal characterization of function-entry lifetime protectors.
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

/-! ## 4. Universal `UnsafeCell` Shared-Borrow Theorem (Closing `GAP-MR-0001`) -/

/--
**Theorem L4.10 (`mir_shared_borrow_unsafe_cell_permits_write`)**:
Universal correspondence theorem for `BorrowKind.shared` over `core::cell::UnsafeCell<T>`
in `Trusted.Rustc.V2026_08_01.MirSemantics.{placeIsFreeze,evalRvalue,writePlaceValue}`
(closing `GAP-MR-0001`):
For EVERY inner type `innerTy : Ty`, EVERY initialized root value `initVal : Value`,
EVERY write value `newVal : Value`, and EVERY memory state `mem : Memory` (with `mem.borrows = []`):
1. `placeIsFreeze` on a local of type `core::cell::UnsafeCell<innerTy>` evaluates to `false` (`!Freeze`);
2. Evaluating `Rvalue.ref .shared { local_ := 0, projection := .nil }` via `evalRvalue`
   assigns `perm := .reserved` (`ReservedIm` / `Cell`) instead of `.frozen`;
3. Writing `newVal` through the resulting pointer `{ local_ := 1, projection := [.deref] }`
   via `writePlaceValue` succeeds with `.ok [.init newVal, .init ptrVal]`;
4. `evalAnnealV2026_08_01 .sharedUnsafeCellWrite` agrees unconditionally with
   `evalMiniRustSnapshot .S2026_07_BleedingEdge .sharedUnsafeCellWrite` (`.normalUnit`).
-/
theorem mir_shared_borrow_unsafe_cell_permits_write
    (innerTy : RigidTy) (initVal newVal : Value) (mem : Memory)
    (h_empty_borrows : mem.borrows = .nil) :
    let unsafeCellRigid : RigidTy := .adt "core::cell::UnsafeCell" [innerTy]
    let unsafeCellTy : Ty := { kind := unsafeCellRigid, layoutIdx := 0 }
    let ptrTy : Ty := { kind := .ref .not unsafeCellRigid, layoutIdx := 0 }
    let localDecls : List LocalDecl := [
      { mutability := .not, ty := unsafeCellTy, debugName := .none },
      { mutability := .mut, ty := ptrTy, debugName := .none }
    ]
    let initLocals : List LocalSlot := [.init initVal, .uninit]
    let reservedEntry : BorrowEntry := {
      tag := mem.nextTag
      targetLocal := 0
      targetProjection := .nil
      perm := .reserved
    }
    let ptrVal : Value := .ptr { allocId := mem.nextTag, offsetBytes := 0 } 8
    let memAfterRef : Memory := {
      mem with
      borrows := reservedEntry :: mem.borrows
      nextTag := Nat.add mem.nextTag 1
    }
    placeIsFreeze localDecls emptyLayoutTable { local_ := 0, projection := .nil } = false ∧
    evalRvalue initLocals (.ref .shared { local_ := 0, projection := .nil }) mem localDecls =
      .ok ptrVal initLocals memAfterRef ∧
    writePlaceValue [.init initVal, .init ptrVal] memAfterRef.borrows
      { local_ := 1, projection := [.deref] } newVal =
      .ok [.init newVal, .init ptrVal] ∧
    evalAnnealV2026_08_01 .sharedUnsafeCellWrite defaultFixtureState =
      evalMiniRustSnapshot .S2026_07_BleedingEdge .sharedUnsafeCellWrite := by
  dsimp only
  refine ⟨rfl, rfl, ?_, by decide⟩
  rw [h_empty_borrows]
  simp [writePlaceValue, lookupBorrow, Trusted.Sequence.get?, ProvenancePtr.tag,
    Nat.beq_refl, Trusted.Sequence.set?]

/-! ## 5. Universal Protected Mutable Reborrow Theorem (Closing `GAP-EPOCH-0001` & Witnessing `GAP-EPOCH-0002`) -/

/--
**Theorem L4.11 (`mir_protected_reborrow_init_write_matches_s2026_07`)**:
Universal correspondence theorem for `Trusted.Rustc.V2026_08_01.MirSemantics.{initProtectedReborrowPerm,
protectedReborrowHasInitWrite}` against `MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.reborrow_permission`
(closing `GAP-EPOCH-0001` for `V2026_08_01`):
1. For EVERY `isFreeze : Bool`, when `isMutable = true` and `implicitWrites = true`,
   `initProtectedReborrowPerm true isFreeze true = .active` and
   `protectedReborrowHasInitWrite (initProtectedReborrowPerm true isFreeze true) = true`,
   matching `S2026_07_BleedingEdge.Generated.Ops.reborrow_permission true .Strong true isFreeze true = .Prot .Unique`
   whose `init_access` is `some .Write`;
2. When `isMutable = true` and `implicitWrites = false`, `initProtectedReborrowPerm true isFreeze false = .reserved`
   and `protectedReborrowHasInitWrite = false`, matching `S2026_07_BleedingEdge` `.Prot (.Reserved false isFreeze)`
   whose `init_access` is `some .Read`;
3. `evalAnnealV2026_08_01 .reservedImEpochTransition` agrees unconditionally with
   `evalMiniRustSnapshot .S2026_07_BleedingEdge .reservedImEpochTransition` (`.normalUnit`).
-/
theorem mir_protected_reborrow_init_write_matches_s2026_07 (isFreeze : Bool) :
    initProtectedReborrowPerm true isFreeze true = .active ∧
    protectedReborrowHasInitWrite (initProtectedReborrowPerm true isFreeze true) = true ∧
    (MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.reborrow_permission
      true .Strong true isFreeze true).init_access = .some .Write ∧
    initProtectedReborrowPerm true isFreeze false = .reserved ∧
    protectedReborrowHasInitWrite (initProtectedReborrowPerm true isFreeze false) = false ∧
    (MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.reborrow_permission
      true .Strong true isFreeze false).init_access = .some .Read ∧
    evalAnnealV2026_08_01 .reservedImEpochTransition defaultFixtureState =
      evalMiniRustSnapshot .S2026_07_BleedingEdge .reservedImEpochTransition := by
  cases isFreeze <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L4.12 (`mir_protected_reborrow_epoch_delta_s2026_05`)**:
Characterizes the sole intentional epoch divergence `GAP-EPOCH-0002` between
`Trusted.Rustc.V2026_08_01` (which targets `S2026_07_BleedingEdge`) and historical
snapshot `S2026_05_Matched`:
- `V2026_08_01` and `S2026_07_BleedingEdge` perform an initial write access on protected
  mutable reborrows with `implicit_writes = true` (`.normalUnit`);
- Historical snapshot `S2026_05_Matched` (`5f78e227bbe3`) assigns `.Prot (.Reserved false false)`
  with `init_access = .some .Read` (`.ub` on `.reservedImEpochTransition`).
-/
theorem mir_protected_reborrow_epoch_delta_s2026_05 :
    activeEpochDivergences .V2026_08_01 .S2026_07_BleedingEdge = [] ∧
    activeEpochDivergences .V2026_08_01 .S2026_05_Matched = [.GAP_EPOCH_0002] ∧
    VerifiedDivergenceWitness
      (evalAnnealV2026_08_01 .reservedImEpochTransition defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .reservedImEpochTransition)
      .normalUnit
      .ub :=
  ⟨by decide, by decide, witness_GAP_EPOCH_0002.2⟩

/-! ## 6. Full Read/Write/Protector Automaton Across `S2026_05_Matched` & `S2026_07_BleedingEdge` -/

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

/-- Anneal `V2026_08_01` single-node Tree Borrows step with protector enforcement. -/
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
      match
        MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.PermissionUnprot.transition
          (ofS07PermissionUnprot pUnprot)
          (match acc with | .read => .Read | .write => .Write)
          (match loc with | .childLocal => .Local | .foreign => .Foreign)
      with
      | .ok p5 => .ok (toS07PermissionUnprot p5)
      | .error e => .error e
    | .S2026_07_BleedingEdge =>
      MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.PermissionUnprot.transition
        pUnprot (toAccessKind acc) (toNodeRelation loc)
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
**Theorem L4.13 (`treeBorrow_transition_corresponds_for_freeze`)**:
Universal correspondence for `Freeze` pointees (`hasInteriorMut = false`) across both
MiniRust snapshots.
-/
theorem treeBorrow_transition_corresponds_for_freeze
    (snap : MiniRustSnap) (perm : TreeBorrowPerm)
    (loc : TbLocality) (acc : TbAccessKind) (prot : Bool) :
    annealStepTreeBorrowPerm perm loc acc prot =
      mrStepTreeBorrowPerm snap false perm loc acc prot := by
  cases snap <;> cases perm <;> cases loc <;> cases acc <;> cases prot <;> rfl

/--
**Theorem L4.14 (`mir_updateBorrowPermTreeAtProj_characterization`)**:
Universal characterization of Tree Borrows parent/child write transitions in
`Trusted.Rustc.V2026_08_01.MirSemantics.updateBorrowPermTreeAtProj`.
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
  · intro h_for h_neq h_ov
    simp [updateBorrowPermTreeAtProj, resolveTreeBorrowWriterTag,
      updateBorrowPermAtProj, Nat.beq_refl, h_for, h_neq, h_ov]

/--
**Theorem L4.15 (`mir_updateBorrowPermOnReadAtProj_characterization`)**:
Universal characterization of Tree Borrows read transitions in
`Trusted.Rustc.V2026_08_01.MirSemantics.updateBorrowPermOnReadAtProj`.
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
    simp [updateBorrowPermOnReadAtProj, Nat.beq_refl, h_for, h_ov, h_perm]
  · intro h_for h_ov h_perm
    simp [updateBorrowPermOnReadAtProj, Nat.beq_refl, h_for, h_ov, h_perm]

end Correspondence.V2026_08_01.L4_TreeBorrows
