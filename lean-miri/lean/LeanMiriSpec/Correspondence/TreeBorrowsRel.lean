/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Miri.TreeBorrows

/-!
# Six-State Tree Borrows Correspondence for `LM-3.3`

Relates Anneal's Tree Borrows permissions (`TreeBorrowPerm`, `BorrowEntry`, and
the per-node transition `treeBorrowPermTransition` /
`treeBorrowNodeAccess` in `Trusted.Rustc.V2026_06_01.MirSemantics`) to the
vendored `lean-miri` port of Miri's Tree Borrows
(`Miri/TreeBorrows/{Permissions,LocationState,Traversal,NormalTree,RangedNormalTree,TreeState,RetagPipeline,MachineMemoryHooks}`).

* `annealPermToMiri` / `miriPermToAnneal` and `TreeBorrowsBijection`: the exact
  bijection between Anneal's six states and `Miri.TreeBorrows.Permission`
  (`Cell`, `ReservedFrz conflicted`, `ReservedIM`, `Unique`, `Frozen`,
  `Disabled`).
* `performAccess_permission_simulation`: Anneal's per-node transition is
  Miri's `performAccess` on every `(Read | Write) × (Local | Foreign)` access,
  every one of the six states, and both protector settings, including the
  `ImpossibleProtectedReservedIM` invariant failure.
* `nodeAccess_locationState_simulation`: Anneal's full per-node access
  (`treeBorrowNodeAccess`, with the protector rule) is Miri's
  `Tree.LocationState.performAccess` on an accessed location.
* `unsafeCell_permission_simulation` (`I-11`) and
  `reservedFrz_conflicted_bijection`: the interior-mutability states and the
  protector conflict latch.
* `retag_pipeline_simulation`, `borrowTree_newChild_reference_simulation`,
  `retagPointerValue_rawPointer_simulation`,
  `retagPointerValue_zst_reference_simulation`,
  `retagPointerValue_cell_8byte_simulation`,
  `retagPointerValue_8byte_reference_simulation`,
  `borrowTree_performNormalAccessAt_simulation`,
  `borrowTree_performBorrowAccessRange_simulation`,
  `borrowTree_deallocateBorrowRange_simulation`,
  `machineMemoryHooks_beforeMemoryRead_simulation`,
  `machineMemoryHooks_beforeMemoryWrite_simulation`, and
  `machineMemoryHooks_beforeMemoryDeallocation_simulation`: operational
  correspondence across `RetagPolicy.create`, `BorrowTree.newChild`,
  `RetagPipeline.retagPointerValue`, `BorrowTree.performNormalAccessAt`,
  `BorrowTree.performBorrowAccessRange`, `BorrowTree.deallocateBorrowRange`,
  and `MachineMemoryHooks` (`beforeMemoryRead`, `beforeMemoryWrite`, and
  `beforeMemoryDeallocation`, including `Cell` strong-protector exemption and
  `ProtectedDealloc`).
* `TreeBorrowsRel`, `normalTree_relative_access_simulation` (`I-10`),
  `freezeTreeBorrowsOnReadAtProj_locationState_simulation`,
  `invalidateTreeBorrowsAtProj_locationState_simulation`,
  `byteRangesOverlapBool_iff`, `borrowEntryOverlapsWrite_iff`,
  `hasTreeReadUB_disjoint_tail`, `freezeTreeBorrowsOnReadAtProj_disjoint_tail`,
  `invalidateTreeBorrowsAtProj_disjoint_tail`,
  `basedNormalTree_performAccess_singleton_simulation`,
  `basedNormalTree_performAccess_parent_child_simulation`,
  `basedNormalTree_performAccess_siblings_simulation`,
  `basedNormalTree_performAccess_three_level_chain_simulation`,
  `basedNormalTree_performAccess_branching_children_simulation`,
  `treeBorrowsProtAncestorInv`,
  `basedNormalTree_performAccess_three_level_chain_prot_simulation`,
  `basedNormalTree_performAccess_branching_children_prot_simulation`, and
  `rangedNormalTree_performAccessRange_simulation`: `parentTag` ancestor-path
  classification, byte-range / sub-place overlap gating, disjoint-subprojection
  isolation, general borrow-table preservation, multi-node
  `NormalTreeState.performAccess` lockstep (including inductive protector-aware
  3-level reborrow chains and branching child trees with `Cell`/`ReservedIM`
  descendants under `Disabled` ancestors), and
  `RangedNormalTreeState.performAccessRange` delegation.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Exact six-state bijection -/

/-- Anneal permission to Miri permission (state for state). -/
def annealPermToMiri : TreeBorrowPerm → Miri.TreeBorrows.Permission
  | .cell => .Cell
  | .reservedFrz conflicted => .ReservedFrz conflicted
  | .reservedIM => .ReservedIM
  | .unique => .Unique
  | .frozen => .Frozen
  | .disabled => .Disabled

/-- Miri permission to Anneal permission (state for state). -/
def miriPermToAnneal : Miri.TreeBorrows.Permission → TreeBorrowPerm
  | .Cell => .cell
  | .ReservedFrz conflicted => .reservedFrz conflicted
  | .ReservedIM => .reservedIM
  | .Unique => .unique
  | .Frozen => .frozen
  | .Disabled => .disabled

theorem miriPermToAnneal_annealPermToMiri (perm : TreeBorrowPerm) :
    miriPermToAnneal (annealPermToMiri perm) = perm := by
  cases perm <;> rfl

theorem annealPermToMiri_miriPermToAnneal (perm : Miri.TreeBorrows.Permission) :
    annealPermToMiri (miriPermToAnneal perm) = perm := by
  cases perm <;> rfl

/-- **`TreeBorrowsBijection`**: `annealPermToMiri` and `miriPermToAnneal` are
mutually inverse, so Anneal's `TreeBorrowPerm` is in exact one-to-one
correspondence with `Miri.TreeBorrows.Permission`, including the
`conflicted` latch of `ReservedFrz`. -/
theorem TreeBorrowsBijection :
    (∀ perm : TreeBorrowPerm, miriPermToAnneal (annealPermToMiri perm) = perm) ∧
    (∀ perm : Miri.TreeBorrows.Permission,
      annealPermToMiri (miriPermToAnneal perm) = perm) :=
  ⟨miriPermToAnneal_annealPermToMiri, annealPermToMiri_miriPermToAnneal⟩

theorem annealPermToMiri_injective {a b : TreeBorrowPerm}
    (h : annealPermToMiri a = annealPermToMiri b) : a = b := by
  rw [← miriPermToAnneal_annealPermToMiri a, h, miriPermToAnneal_annealPermToMiri]

/-- The legacy names `.active` and `.reserved` denote `Unique` and
`ReservedFrz false`; `.cell` and `.reservedIM` are distinct Miri states. -/
theorem annealPermToMiri_legacy :
    annealPermToMiri .active = .Unique ∧
    annealPermToMiri .reserved = .ReservedFrz false ∧
    annealPermToMiri .cell = .Cell ∧
    annealPermToMiri .reservedIM = .ReservedIM ∧
    TreeBorrowPerm.cell ≠ .reservedIM ∧
    TreeBorrowPerm.cell ≠ .frozen :=
  ⟨rfl, rfl, rfl, rfl, (fun h => TreeBorrowPerm.noConfusion h),
    (fun h => TreeBorrowPerm.noConfusion h)⟩

/-! ## 2. Per-node permission transitions -/

/-- Anneal access kind to Miri access kind. -/
def annealAccessKindToMiri : TreeBorrowAccessKind → Miri.TreeBorrows.AccessKind
  | .read => .Read
  | .write => .Write

/-- Anneal relative position to Miri relative position. -/
def annealRelatednessToMiri :
    TreeBorrowRelatedness → Miri.TreeBorrows.AccessRelatedness
  | .localAccess => .LocalAccess
  | .foreignAccess => .ForeignAccess

/-- Miri access kind to Anneal access kind. -/
def miriAccessKindToAnneal : Miri.TreeBorrows.AccessKind → TreeBorrowAccessKind
  | .Read => .read
  | .Write => .write

/-- Miri relative position to Anneal relative position. -/
def miriRelatednessToAnneal :
    Miri.TreeBorrows.AccessRelatedness → TreeBorrowRelatedness
  | .LocalAccess => .localAccess
  | .ForeignAccess => .foreignAccess

/-- Anneal transition outcome to Miri's `AccessOutcome`. -/
def annealTransitionToMiri : TreeBorrowTransition → Miri.TreeBorrows.AccessOutcome
  | .transition perm => .Transition (annealPermToMiri perm)
  | .ub => .UndefinedBehavior
  | .protectedReservedIM => .ImpossibleProtectedReservedIM

/-- **`performAccess_permission_simulation`** (certifying `I-10`'s per-node
layer): for every access kind, relative position, Anneal permission (all six
states, both values of `conflicted`), and protector setting, Anneal's
`treeBorrowPermTransition` is Miri's `performAccess` under the bijection,
including the `UndefinedBehavior` and `ImpossibleProtectedReservedIM`
outcomes. -/
theorem performAccess_permission_simulation
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    annealTransitionToMiri (treeBorrowPermTransition kind rel perm isProtected) =
      Miri.TreeBorrows.performAccess
        (annealAccessKindToMiri kind) (annealRelatednessToMiri rel)
        (annealPermToMiri perm) isProtected := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases kind <;> cases rel <;>
    cases isProtected <;> rfl

/-- The same lockstep stated over Miri's inputs: Miri's `performAccess` on any
permission is Anneal's transition on the corresponding Anneal state. -/
theorem performAccess_permission_simulation_miri
    (kind : Miri.TreeBorrows.AccessKind) (rel : Miri.TreeBorrows.AccessRelatedness)
    (perm : Miri.TreeBorrows.Permission) (isProtected : Bool) :
    Miri.TreeBorrows.performAccess kind rel perm isProtected =
      annealTransitionToMiri
        (treeBorrowPermTransition
          (miriAccessKindToAnneal kind) (miriRelatednessToAnneal rel)
          (miriPermToAnneal perm) isProtected) := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases kind <;> cases rel <;>
    cases isProtected <;> rfl

/-- Anneal's fail-closed `.protectedReservedIM` outcome arises exactly for a
foreign access to a protected `.reservedIM` node, which is where Miri's
`assert!(!protected)` fires (`ImpossibleProtectedReservedIM`). -/
theorem protectedReservedIM_characterization
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    treeBorrowPermTransition kind rel perm isProtected = .protectedReservedIM ↔
      perm = .reservedIM ∧ isProtected = true ∧ rel = .foreignAccess := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases kind <;> cases rel <;>
    cases isProtected <;> simp

/-- Function-entry retags never create `.reservedIM`, so the
`ImpossibleProtectedReservedIM` branch is unreachable from Anneal's protected
tags. -/
theorem fnEntryRetagPerm_ne_reservedIM (mutability : Mutability) (pointee : RigidTy) :
    fnEntryRetagPerm mutability pointee ≠ .reservedIM := by
  cases mutability <;> simp [fnEntryRetagPerm] <;> split <;> simp

/-! ## 3. Full per-node access with the protector rule -/

/-- **`nodeAccess_locationState_simulation`**: Anneal's full per-node access
`treeBorrowNodeAccess` (permission transition plus the protector rule) is
Miri's `Tree.LocationState.performAccess` on an accessed location holding the
corresponding permission, for every access that Miri's visitor does not skip
(a foreign access to a `Disabled` node is skipped, see
`disabled_foreign_access_skipped`):
* a permitted access moves both to corresponding permissions;
* a forbidden child access or a protected disable is a Miri `Error`;
* a foreign access to a protected `.reservedIM` is Miri's
  `PermissionInvariantFailure`. -/
theorem nodeAccess_locationState_simulation
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool)
    (sifa : Miri.TreeBorrows.IdempotentForeignAccess)
    (hskip : rel = .foreignAccess → perm ≠ .disabled) :
    match treeBorrowNodeAccess kind rel perm isProtected with
    | .transition next =>
      ∃ transition,
        Miri.TreeBorrows.Tree.LocationState.performAccess
            ⟨annealPermToMiri perm, true, sifa⟩
            (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
          .Success ⟨annealPermToMiri next, true, sifa⟩ transition
    | .ub =>
      ∃ state error,
        Miri.TreeBorrows.Tree.LocationState.performAccess
            ⟨annealPermToMiri perm, true, sifa⟩
            (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
          .Error state error
    | .protectedReservedIM =>
      Miri.TreeBorrows.Tree.LocationState.performAccess
          ⟨annealPermToMiri perm, true, sifa⟩
          (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
        .PermissionInvariantFailure ⟨annealPermToMiri perm, true, sifa⟩ := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases kind <;> cases rel <;>
    cases isProtected <;>
    first
    | exact absurd rfl (hskip rfl)
    | exact ⟨_, rfl⟩
    | exact ⟨_, _, rfl⟩
    | rfl

/-- Miri's tree visitor skips every foreign access to a `Disabled` node
(`skip_if_known_noop`), which is why `treeBorrowNodeAccess` leaves a
`.disabled` entry untouched (and unreported, even when protected) on foreign
accesses. -/
theorem disabled_foreign_access_skipped
    (accessed : Bool) (sifa : Miri.TreeBorrows.IdempotentForeignAccess)
    (kind : TreeBorrowAccessKind) (isProtected : Bool) :
    Miri.TreeBorrows.Tree.LocationState.skipIfKnownNoop
        ⟨.Disabled, accessed, sifa⟩ (annealAccessKindToMiri kind) .ForeignAccess =
      .SkipSelfAndChildren ∧
    treeBorrowNodeAccess kind .foreignAccess .disabled isProtected =
      .transition .disabled := by
  refine ⟨?_, rfl⟩
  simp [Miri.TreeBorrows.Tree.LocationState.skipIfKnownNoop,
    Miri.TreeBorrows.AccessRelatedness.isForeign, Miri.TreeBorrows.Permission.isDisabled]

/-- Whenever the protected per-node write is not undefined behavior it agrees
with the unprotected one, which justifies Anneal's write-update functions
(`updateBorrowPerm`, `updateBorrowPermAtProj`) using the unprotected transition
after the protector checks (`hasProtectedWriteConflict`,
`hasProtectedTreeWriteConflict`) have passed. -/
theorem protected_write_success_eq_unprotected
    (rel : TreeBorrowRelatedness) (perm next : TreeBorrowPerm)
    (h : treeBorrowNodeAccess .write rel perm true = .transition next) :
    treeBorrowNodeAccess .write rel perm false = .transition next := by
  rcases perm with _ | (_ | _) | _ | _ | _ | _ <;> cases rel <;>
    simp at h ⊢ <;> exact h

/-! ## 4. Interior mutability (`I-11`): `Cell` vs. `ReservedIM` vs. `Frozen` -/

/-- **`unsafeCell_permission_simulation`** (certifying `I-11`):
1. A shared borrow of a `!Freeze` place gets `.cell` and of a `Freeze` place
   `.frozen` in Anneal, which are Miri's `NewPermission::new` choices for
   shared references (`RetagPolicy.create … .Shared …`).
2. `.cell` is isolated in both: every child or foreign read or write, protected
   or not, leaves it `Cell`.
3. `.frozen` (`&T` with `T : Freeze`) rejects child writes as undefined
   behavior and is disabled by foreign writes in both.
4. `.reservedIM` is not `.cell`: a child write activates it to `.unique`, after
   which a foreign read freezes it and a foreign write disables it, in both. -/
theorem unsafeCell_permission_simulation :
    (∀ (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (place : Place)
        (ty : Ty),
      placeTy localDecls layouts place = some ty →
      sharedBorrowPerm localDecls layouts place =
        (if tyIsFreeze ty then .frozen else .cell)) ∧
    (∀ (facts : Miri.TreeBorrows.RetagPolicy.TypeFacts)
        (config : Miri.TreeBorrows.RetagPolicy.PolicyConfig)
        (mode : Miri.TreeBorrows.RetagPolicy.RetagMode),
      mode ≠ .None →
      ∃ policy,
        Miri.TreeBorrows.RetagPolicy.create facts .Shared mode config = some policy ∧
        policy.outsidePermission =
          annealPermToMiri (if facts.isFreeze then .frozen else .cell) ∧
        policy.nonfreezePermission = annealPermToMiri .cell ∧
        policy.freezePermission = annealPermToMiri .frozen) ∧
    (∀ (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness) (isProtected : Bool),
      treeBorrowNodeAccess kind rel .cell isProtected = .transition .cell ∧
      Miri.TreeBorrows.performAccess
          (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) .Cell isProtected =
        .Transition .Cell) ∧
    (∀ isProtected : Bool,
      treeBorrowNodeAccess .write .localAccess .frozen isProtected = .ub ∧
      Miri.TreeBorrows.performAccess .Write .LocalAccess .Frozen isProtected =
        .UndefinedBehavior) ∧
    (treeBorrowNodeAccess .write .foreignAccess .frozen false = .transition .disabled ∧
      Miri.TreeBorrows.performAccess .Write .ForeignAccess .Frozen false =
        .Transition .Disabled) ∧
    (treeBorrowNodeAccess .write .localAccess .reservedIM false = .transition .unique ∧
      treeBorrowNodeAccess .read .foreignAccess .unique false = .transition .frozen ∧
      treeBorrowNodeAccess .write .foreignAccess .unique false = .transition .disabled ∧
      treeBorrowNodeAccess .write .foreignAccess .reservedIM false =
        .transition .reservedIM ∧
      Miri.TreeBorrows.performAccess .Write .LocalAccess .ReservedIM false =
        .Transition .Unique ∧
      Miri.TreeBorrows.performAccess .Read .ForeignAccess .Unique false =
        .Transition .Frozen ∧
      Miri.TreeBorrows.performAccess .Write .ForeignAccess .ReservedIM false =
        .Transition .ReservedIM) := by
  refine ⟨?_, ?_, ?_, ?_, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro localDecls layouts place ty hty
    simp only [sharedBorrowPerm, hty]
    cases tyIsFreeze ty <;> rfl
  · intro facts config mode hmode
    rcases facts with ⟨unpin, unsafeUnpin, freeze⟩
    rcases config with ⟨implicitWrites, noWritable⟩
    cases mode <;> cases unpin <;> cases unsafeUnpin <;> cases freeze <;>
      cases implicitWrites <;> cases noWritable <;>
      first
      | exact absurd rfl hmode
      | exact ⟨_, rfl, rfl, rfl, rfl⟩
  · intro kind rel isProtected
    cases kind <;> cases rel <;> cases isProtected <;> exact ⟨rfl, rfl⟩
  · intro isProtected
    cases isProtected <;> exact ⟨rfl, rfl⟩

/-! ## 5. The protector conflict latch of `ReservedFrz` -/

/-- **`reservedFrz_conflicted_bijection`**: the `conflicted` latch corresponds
exactly:
1. a foreign read of a protected `.reservedFrz false` sets `conflicted` in both;
2. a subsequent child write while still protected is undefined behavior in
   both;
3. once the protector is released, the child write activates the conflicted
   reservation to `.unique` in both;
4. an unprotected foreign read leaves the latch unchanged in both;
5. for every `conflicted` value and protector setting, all four accesses agree
   (the bijection carries `conflicted` through every transition). -/
theorem reservedFrz_conflicted_bijection :
    (treeBorrowNodeAccess .read .foreignAccess (.reservedFrz false) true =
        .transition (.reservedFrz true) ∧
      Miri.TreeBorrows.performAccess .Read .ForeignAccess (.ReservedFrz false) true =
        .Transition (.ReservedFrz true)) ∧
    (treeBorrowNodeAccess .write .localAccess (.reservedFrz true) true = .ub ∧
      Miri.TreeBorrows.performAccess .Write .LocalAccess (.ReservedFrz true) true =
        .UndefinedBehavior) ∧
    (treeBorrowNodeAccess .write .localAccess (.reservedFrz true) false =
        .transition .unique ∧
      Miri.TreeBorrows.performAccess .Write .LocalAccess (.ReservedFrz true) false =
        .Transition .Unique) ∧
    (∀ conflicted : Bool,
      treeBorrowNodeAccess .read .foreignAccess (.reservedFrz conflicted) false =
        .transition (.reservedFrz conflicted) ∧
      Miri.TreeBorrows.performAccess .Read .ForeignAccess (.ReservedFrz conflicted) false =
        .Transition (.ReservedFrz conflicted)) ∧
    (∀ (conflicted isProtected : Bool) (kind : TreeBorrowAccessKind)
        (rel : TreeBorrowRelatedness),
      annealTransitionToMiri
          (treeBorrowPermTransition kind rel (.reservedFrz conflicted) isProtected) =
        Miri.TreeBorrows.performAccess (annealAccessKindToMiri kind)
          (annealRelatednessToMiri rel) (.ReservedFrz conflicted) isProtected) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro conflicted
    cases conflicted <;> exact ⟨rfl, rfl⟩
  · intro conflicted isProtected kind rel
    exact performAccess_permission_simulation kind rel (.reservedFrz conflicted) isProtected

/-- The latch survives later foreign reads and is only cleared by activation:
on a protected `.reservedFrz true` a foreign read keeps it, and a foreign write
is a protected disable (undefined behavior) in both. -/
theorem reservedFrz_conflicted_protected_foreign :
    treeBorrowNodeAccess .read .foreignAccess (.reservedFrz true) true =
        .transition (.reservedFrz true) ∧
    treeBorrowNodeAccess .write .foreignAccess (.reservedFrz true) true = .ub ∧
    Miri.TreeBorrows.performAccess .Write .ForeignAccess (.ReservedFrz true) true =
      .Transition .Disabled :=
  ⟨rfl, rfl, rfl⟩

/-! ## 6. Retag policy: initial permissions and protectors -/

/-- Anneal's retag modes, mirroring `RetagKind` in MIR (`Default`, `TwoPhase`,
`Raw`, `FnEntry`). -/
inductive AnnealRetagMode : Type where
  | default
  | twoPhase
  | raw
  | fnEntry
  deriving DecidableEq, Repr

/-- Anneal retag mode to Miri's `RetagMode`. -/
def annealRetagModeToMiri : AnnealRetagMode → Miri.TreeBorrows.RetagPolicy.RetagMode
  | .default => .Default
  | .twoPhase => .TwoPhase
  | .raw => .Raw
  | .fnEntry => .FnEntry

/-- The permission Anneal assigns to a new reference tag for a pointee whose
`Freeze`-ness is `frozen`: `sharedBorrowPerm` / `mutableBorrowPerm` for
unprotected retags (`Rvalue.ref` performs the default and two-phase retags, and
a raw retag of a reference is a default retag) and `fnEntryRetagPerm` for
function-entry retags (`evalFnEntryRetag`). -/
def annealRetagPerm (mode : AnnealRetagMode) (mutability : Mutability)
    (frozen : Bool) : TreeBorrowPerm :=
  match mode, mutability with
  | .fnEntry, .not => if frozen then .frozen else .cell
  | .fnEntry, .mut => .reservedFrz false
  | _, .not => if frozen then .frozen else .cell
  | _, .mut => if frozen then .reservedFrz false else .reservedIM

/-- Anneal mutability to Miri's reference kind. -/
def annealRefKindToMiri : Mutability → Miri.TreeBorrows.RetagPolicy.ReferenceKind
  | .not => .Shared
  | .mut => .Mutable

/-- `annealRetagPerm` is the permission Anneal's executable choices produce:
`sharedBorrowPerm` / `mutableBorrowPerm` on a place of known type and
`fnEntryRetagPerm` on a reference type. -/
theorem annealRetagPerm_eq_trusted
    (localDecls : List LocalDecl) (layouts : Layout.LayoutTable) (place : Place)
    (ty : Ty) (hty : placeTy localDecls layouts place = some ty)
    (mutability : Mutability) (pointee : RigidTy) :
    sharedBorrowPerm localDecls layouts place =
      annealRetagPerm .default .not (tyIsFreeze ty) ∧
    mutableBorrowPerm localDecls layouts place =
      annealRetagPerm .default .mut (tyIsFreeze ty) ∧
    mutableBorrowPerm localDecls layouts place =
      annealRetagPerm .twoPhase .mut (tyIsFreeze ty) ∧
    fnEntryRetagPerm mutability pointee =
      annealRetagPerm .fnEntry mutability (rigidTyIsFreeze 16 pointee) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [sharedBorrowPerm, hty, annealRetagPerm]
    cases tyIsFreeze ty <;> rfl
  · simp only [mutableBorrowPerm, hty, annealRetagPerm]
    cases tyIsFreeze ty <;> rfl
  · simp only [mutableBorrowPerm, hty, annealRetagPerm]
    cases tyIsFreeze ty <;> rfl
  · cases mutability <;> simp only [fnEntryRetagPerm, annealRetagPerm] <;>
      cases rigidTyIsFreeze 16 pointee <;> rfl

/-- **`retag_pipeline_simulation`**: for every retag mode (`Default`,
`TwoPhase`, `Raw`, `FnEntry`), reference mutability, and pointee
`Freeze`-ness, with Miri's default configuration (no implicit writes) and an
`Unpin` pointee:
1. Miri's `NewPermission::new` (`RetagPolicy.create`) succeeds, and its
   permission for the reference's bytes (`outsidePermission`, and the
   per-byte permission of the matching `Freeze` part) is exactly Anneal's
   `annealRetagPerm` under the bijection;
2. Miri attaches a protector exactly for `FnEntry`, which is when Anneal's
   `evalFnEntryRetag` attaches `protector := some protId` to the new tag;
3. Miri's initial location state for that permission is accessed (so the
   retag performed an initial child read through the parent, which Anneal
   performs with `freezeTreeBorrowsOnReadAtProj`) exactly when the permission
   is not `Cell`; a `Cell` reborrow performs no initial access in both;
4. no protected retag yields `ReservedIM`. -/
theorem retag_pipeline_simulation
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool)
    (facts : Miri.TreeBorrows.RetagPolicy.TypeFacts)
    (hunpin : facts.isUnpin = true) (hunsafeUnpin : facts.isUnsafeUnpin = true)
    (hfreeze : facts.isFreeze = frozen) :
    ∃ policy,
      Miri.TreeBorrows.RetagPolicy.create facts (annealRefKindToMiri mutability)
          (annealRetagModeToMiri mode) ⟨false, false⟩ = some policy ∧
      policy.outsidePermission = annealPermToMiri (annealRetagPerm mode mutability frozen) ∧
      (if frozen then policy.freezePermission else policy.nonfreezePermission) =
        annealPermToMiri (annealRetagPerm mode mutability frozen) ∧
      (policy.protector.isSome = true ↔ mode = .fnEntry) ∧
      (∃ state,
        Miri.TreeBorrows.RetagPolicy.initialLocationState policy frozen = .ok state ∧
        state.permission = annealPermToMiri (annealRetagPerm mode mutability frozen) ∧
        (state.accessed = true ↔ annealRetagPerm mode mutability frozen ≠ .cell)) ∧
      (mode = .fnEntry → annealRetagPerm mode mutability frozen ≠ .reservedIM) := by
  rcases facts with ⟨unpin, unsafeUnpin, freeze⟩
  simp only at hunpin hunsafeUnpin hfreeze
  subst hunpin hunsafeUnpin hfreeze
  cases mode <;> cases mutability <;> cases freeze <;>
    exact ⟨_, rfl, rfl, rfl, by simp [annealRetagModeToMiri],
      ⟨_, rfl, rfl, by
        constructor <;> intro hx <;>
          first
          | rfl
          | (cases hx; done)
          | (simp [annealRetagPerm] at hx; done)
          | (simp [annealRetagPerm]; done)⟩,
      by simp [annealRetagPerm]⟩

/-- Miri never selects `ReservedIM` under a protector: every permission of a
function-entry `NewPermission` is different from `ReservedIM`, for every type
and configuration (with or without implicit writes). -/
theorem miri_fnEntry_policy_never_reservedIM
    (facts : Miri.TreeBorrows.RetagPolicy.TypeFacts)
    (kind : Miri.TreeBorrows.RetagPolicy.ReferenceKind)
    (config : Miri.TreeBorrows.RetagPolicy.PolicyConfig)
    (policy : Miri.TreeBorrows.RetagPolicy.NewPermission)
    (h : Miri.TreeBorrows.RetagPolicy.create facts kind .FnEntry config = some policy) :
    policy.freezePermission ≠ .ReservedIM ∧
    policy.nonfreezePermission ≠ .ReservedIM ∧
    policy.outsidePermission ≠ .ReservedIM := by
  rcases facts with ⟨unpin, unsafeUnpin, freeze⟩
  rcases config with ⟨implicitWrites, noWritable⟩
  cases kind <;> cases unpin <;> cases unsafeUnpin <;> cases freeze <;>
    cases implicitWrites <;> cases noWritable <;>
    first
    | (injection h with h; subst h; decide)
    | exact absurd h (by intro h'; cases h')

/-- **`retagPointerValue_associatedAccess_simulation`**: Miri's
`RetagPipeline.accessTreeForReborrow` consults `Permission.associatedAccess` on
each inside permission segment before performing a parent tree access. Under the
6-state bijection, the initial permission selected by `annealRetagPerm` has
`associatedAccess = none` when it is `.cell` (no parent access is performed) and
`associatedAccess = some .Read` otherwise (an initial child read is performed
through the parent, matching Anneal's `evalRvalue` `.ref` deref reborrow in
`Places.lean` and `evalFnEntryRetag` in `Statements.lean`). -/
theorem retagPointerValue_associatedAccess_simulation
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    (annealPermToMiri (annealRetagPerm mode mutability frozen)).associatedAccess =
      (match annealRetagPerm mode mutability frozen with
       | .cell => none
       | _ => some Miri.TreeBorrows.AccessKind.Read) := by
  cases mode <;> cases mutability <;> cases frozen <;> rfl

/-- **`retagPointerValue_rawPointer_simulation`**: Miri's
`RetagPipeline.retagPointerValue` on a raw-pointer type shape
(`RetagTypeShape.rawPointer`, `"We don't give new tags to raw pointers."`)
returns `.ok none` without allocating a tag or modifying the machine state when
`request.mode = .Raw`, and rejects any non-`Raw` mode with
`.error .rawPointerWrongMode`. -/
theorem retagPointerValue_rawPointer_simulation
    (state : Miri.TreeBorrows.RetagPipeline.MachineState Unit)
    (request : Miri.TreeBorrows.RetagPipeline.Request)
    (hshape : request.typeShape = .rawPointer) :
    Miri.TreeBorrows.RetagPipeline.retagPointerValue state request =
      if request.mode = .Raw then
        { state := state, outcome := .ok none, events := #[] }
      else
        { state := state, outcome := .error .rawPointerWrongMode, events := #[] } := by
  rcases request with ⟨typeShape, typeFacts, refKind, mode, config, sz, origProv, frz, pim, hooks⟩
  simp only at hshape
  subst hshape
  cases mode <;> rfl

/-- Bijection from Anneal's MIR `RetagKind` to `AnnealRetagMode`. -/
def retagKindToAnnealMode : RetagKind → AnnealRetagMode
  | .default => .default
  | .twoPhase => .twoPhase
  | .raw => .raw
  | .fnEntry => .fnEntry

/-- **`annealRetagPerm_eq_retagPerm`**: Anneal's `MirSemantics.retagPerm`
(used by `evalStmt` on `StatementKind.retag` across all four `RetagKind`s)
agrees identically with `annealRetagPerm` under `rigidTyIsFreeze 16`. -/
theorem annealRetagPerm_eq_retagPerm
    (retagKind : RetagKind) (mutability : Mutability) (pointee : RigidTy) :
    retagPerm retagKind mutability pointee =
      annealRetagPerm (retagKindToAnnealMode retagKind) mutability
        (rigidTyIsFreeze 16 pointee) := by
  cases retagKind <;> cases mutability <;>
    simp only [retagPerm, fnEntryRetagPerm, retagKindToAnnealMode, annealRetagPerm] <;>
    cases rigidTyIsFreeze 16 pointee <;> rfl

private def isExceptOkTB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

private def extractExceptOkTB {ε α : Type} (r : Except ε α) (h : isExceptOkTB r = true) : α :=
  match r, h with
  | .ok a, _ => a

/-- Canonical live 8-byte allocation ID for operational `RetagPipeline` and
`MachineMemoryHooks` correspondence. -/
def retagTestAllocId : Miri.Memory.AllocId := ⟨1, by decide⟩

/-- Root/parent `BorTag` (`1`) on `retagTestAllocId`. -/
def retagParentTag : Miri.Memory.BorTag := Miri.Memory.BorTag.one

/-- Newly allocated child `BorTag` (`2`) on `retagTestAllocId`. -/
def retagChildTag : Miri.Memory.BorTag := ⟨2, by decide⟩

/-- Base 8-byte mutable `Allocation` (with unit extra) before attaching a `BorrowTree`. -/
def baseRetagAllocation : Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  extractExceptOkTB
    (Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
      #[0, 0, 0, 0, 0, 0, 0, 0] Miri.ABI.Align.ONE .Mut)
    (by decide)

/-- Live 8-byte mutable `Allocation` carrying `tree` as its `BorrowTree` extra. -/
def liveTreeAllocation (tree : Miri.TreeBorrows.BorrowTree) :
    Miri.Memory.Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree :=
  baseRetagAllocation.withExtra tree

/-- Live `MemoryState` containing `retagTestAllocId` backed by `tree`. -/
def liveTreeMemory (tree : Miri.TreeBorrows.BorrowTree) :
    Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit :=
  { (Miri.Memory.MemoryState.empty :
      Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit) with
    nextAllocId := 2
    live := #[(retagTestAllocId, { kind := .stack, allocation := liveTreeAllocation tree })] }

private theorem liveTreeAllocation_extra (tree : Miri.TreeBorrows.BorrowTree) :
    (liveTreeAllocation tree).extra = tree := rfl

private theorem baseRetagAllocation_byteSize :
    baseRetagAllocation.byteSize = Miri.ABI.Size.ofBytes 8 := by decide

private theorem baseRetagAllocation_align :
    baseRetagAllocation.align = Miri.ABI.Align.ONE := by decide

private theorem baseRetagAllocation_mutability :
    baseRetagAllocation.mutability = .Mut := by decide

private theorem liveTreeAllocation_byteSize (tree : Miri.TreeBorrows.BorrowTree) :
    (liveTreeAllocation tree).byteSize = Miri.ABI.Size.ofBytes 8 :=
  baseRetagAllocation_byteSize

private theorem liveTreeAllocation_align (tree : Miri.TreeBorrows.BorrowTree) :
    (liveTreeAllocation tree).align = Miri.ABI.Align.ONE :=
  baseRetagAllocation_align

private theorem liveTreeAllocation_mutability (tree : Miri.TreeBorrows.BorrowTree) :
    (liveTreeAllocation tree).mutability = .Mut :=
  baseRetagAllocation_mutability

private theorem liveTreeAllocation_setExtra (tree tree' : Miri.TreeBorrows.BorrowTree) :
    (liveTreeAllocation tree).setExtra tree' = liveTreeAllocation tree' := rfl

private theorem liveTreeMemory_find (tree : Miri.TreeBorrows.BorrowTree) :
    (liveTreeMemory tree).live.find? (fun entry => entry.1 == retagTestAllocId) =
      some (retagTestAllocId, { kind := .stack, allocation := liveTreeAllocation tree }) := rfl

private theorem liveTreeMemory_setLiveAllocation (tree tree' : Miri.TreeBorrows.BorrowTree) :
    (liveTreeMemory tree).setLiveAllocation retagTestAllocId (liveTreeAllocation tree') =
      .ok (liveTreeMemory tree') := by
  rw [Miri.Memory.MemoryState.setLiveAllocation_of_find _ _ _ _ (liveTreeMemory_find tree)]
  rfl

private theorem liveTreeMemory_getAllocInfo (tree : Miri.TreeBorrows.BorrowTree) :
    (liveTreeMemory tree).getAllocInfo retagTestAllocId =
      .ok ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.ONE, .liveData, .Mut⟩ := by
  unfold Miri.Memory.MemoryState.getAllocInfo
  rw [liveTreeMemory_find tree]
  dsimp only [pure, Pure.pure, Except.pure]
  rw [liveTreeAllocation_byteSize, liveTreeAllocation_align, liveTreeAllocation_mutability]

/-- Read the `LocationState` of `tag` in the first homogeneous range segment of
`tree`. -/
def borrowTreeTagLocationState (tree : Miri.TreeBorrows.BorrowTree)
    (tag : Miri.Memory.BorTag) : Option Miri.TreeBorrows.Tree.LocationState :=
  tree.locations.entries[0]?.bind fun seg =>
    (tree.indexOfTag tag).bind (tree.locationStateAt seg.data)

/-- Read the `LocationState` of `tag` in the first homogeneous range segment of
`retagTestAllocId`'s `BorrowTree` in `memory`. -/
def liveTagLocationState
    (memory : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (tag : Miri.Memory.BorTag) : Option Miri.TreeBorrows.Tree.LocationState :=
  (memory.live.find? fun entry => entry.1 == retagTestAllocId).bind fun liveEntry =>
    borrowTreeTagLocationState liveEntry.2.allocation.extra tag

private theorem liveTagLocationState_liveTreeMemory (tree : Miri.TreeBorrows.BorrowTree)
    (tag : Miri.Memory.BorTag) :
    liveTagLocationState (liveTreeMemory tree) tag = borrowTreeTagLocationState tree tag := rfl

/-- Initial `RetagPipeline.MachineState` with root tag `1` (`Unique`) on
`retagTestAllocId` and `nextPointerTag = 2`. -/
def retagInitialMachineState : Miri.TreeBorrows.RetagPipeline.MachineState Unit :=
  { memory := liveTreeMemory (Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8))
    global :=
      { nextPointerTag := retagChildTag
        rootPointerTags := #[(retagTestAllocId, retagParentTag)]
        protectedTags := {}
        trackedPointerTags := #[] }
    frame := {} }

/-- Reference retag request on `retagTestAllocId` (under `retagParentTag`) for
`layoutSize`, `mode`, `mutability`, and `frozen` (`Unpin` pointee, default Miri
config). -/
def retagRefRequest (layoutSize : Miri.ABI.Size)
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    Miri.TreeBorrows.RetagPipeline.Request :=
  { typeShape := .reference
    typeFacts := { isUnpin := true, isUnsafeUnpin := true, isFreeze := frozen }
    referenceKind := annealRefKindToMiri mutability
    mode := annealRetagModeToMiri mode
    config := { implicitWrites := false, rustcNoWritable := false }
    layoutSize := layoutSize
    originalProvenance := some (.concrete retagTestAllocId retagParentTag)
    pointeeIsFreeze := frozen
    preciseInteriorMut := false
    hooks :=
      { allocationResolution :=
          some ⟨retagTestAllocId, Miri.ABI.Size.ZERO, .concrete retagParentTag⟩ } }

private theorem modifyRange_new_full {α : Type} [DecidableEq α]
    (size : Miri.ABI.Size) (value : α) (positive : size.bytes ≠ 0)
    (modify : Miri.DataStructures.ByteRange → α → α) :
    (Miri.DataStructures.DedupRangeMap.new size value).modifyRange Miri.ABI.Size.ZERO size modify =
      ⟨Miri.DataStructures.DedupRangeMap.new size (modify ⟨0, size.bytes⟩ value),
       #[0], #[⟨⟨0, size.bytes⟩, modify ⟨0, size.bytes⟩ value⟩], .ok ()⟩ := by
  have hiter :
      (Miri.DataStructures.DedupRangeMap.new size value).iterMutWithClone
        Miri.ABI.Size.ZERO size id =
      ⟨Miri.DataStructures.DedupRangeMap.new size value,
       #[0], #[⟨⟨0, size.bytes⟩, value⟩], .ok ()⟩ :=
    Miri.DataStructures.DedupRangeMap.iterMut_new_full size value positive
  unfold Miri.DataStructures.DedupRangeMap.modifyRange
    Miri.DataStructures.DedupRangeMap.modifyRangeWithClone
  rw [hiter]
  simp only [Miri.DataStructures.DedupRangeMap.new, positive, beq_iff_eq, ↓reduceIte,
    Id.run, bind, Bind.bind, pure, Pure.pure, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
  rfl

private def rootTreeParentDepth :
    Miri.TreeBorrows.BorrowTree.ZeroProtection.ParentDepth
      (Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)).nodes where
  depth := fun _ => 0
  bounded := fun _ _ _ => Nat.zero_le _
  parent := by
    intro idx node hget bef hpar
    have hlt : idx.toNat < 1 :=
      Miri.TreeBorrows.BorrowTree.ZeroProtection.lookup_valid _ idx node hget
    have hidx : idx = ⟨0⟩ :=
      Miri.TreeBorrows.BorrowTree.ZeroProtection.index_injective idx ⟨0⟩ (Nat.lt_one_iff.mp hlt)
    subst hidx
    have hget0 :
        (Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)).nodes.get ⟨0⟩ =
          some ⟨retagParentTag, none, #[], .Disabled, .None, false, none⟩ := by decide
    rw [hget0] at hget
    injection hget with hnode
    subst hnode
    cases hpar

private theorem nthParent_one_of_treeShape
    {cNode rNode : Miri.TreeBorrows.TreeNode}
    (after staged : Miri.TreeBorrows.BorrowTree)
    (hshape : Miri.TreeBorrows.BorrowTree.ZeroProtection.View.treeShape after =
      Miri.TreeBorrows.BorrowTree.ZeroProtection.View.treeShape staged)
    (hmap : staged.tagMapping.get retagChildTag = some ⟨1⟩)
    (hchild : staged.nodes.get ⟨1⟩ = some cNode)
    (hcpar : cNode.parent = some ⟨0⟩)
    (hroot : staged.nodes.get ⟨0⟩ = some rNode)
    (hrtag : rNode.tag = retagParentTag) :
    after.nthParent retagChildTag 1 = .ok retagParentTag := by
  have htm : after.tagMapping = staged.tagMapping := congrArg (fun s => s.1) hshape
  have hnd : after.nodes.data.map (Option.map Miri.TreeBorrows.BorrowTree.ZeroProtection.View.nodeShape) =
      staged.nodes.data.map (Option.map Miri.TreeBorrows.BorrowTree.ZeroProtection.View.nodeShape) :=
    congrArg (fun s => s.2.1) hshape
  have hc_obs := congrArg (fun a => (a[(⟨1⟩ : Miri.TreeBorrows.UniIndex).toNat]?).getD none) hnd
  rw [Miri.TreeBorrows.BorrowTree.ZeroProtection.View.mapped_lookup,
      Miri.TreeBorrows.BorrowTree.ZeroProtection.View.mapped_lookup, hchild] at hc_obs
  have hr_obs := congrArg (fun a => (a[(⟨0⟩ : Miri.TreeBorrows.UniIndex).toNat]?).getD none) hnd
  rw [Miri.TreeBorrows.BorrowTree.ZeroProtection.View.mapped_lookup,
      Miri.TreeBorrows.BorrowTree.ZeroProtection.View.mapped_lookup, hroot] at hr_obs
  cases hca : after.nodes.get ⟨1⟩ with
  | none => simp [hca] at hc_obs
  | some ca =>
    rw [hca] at hc_obs
    have hca_par : ca.parent = some ⟨0⟩ :=
      (congrArg (fun x => x.2.1) (Option.some.inj hc_obs)).trans hcpar
    cases hra : after.nodes.get ⟨0⟩ with
    | none => simp [hra] at hr_obs
    | some ra =>
      rw [hra] at hr_obs
      have hra_tag : ra.tag = retagParentTag :=
        (congrArg (fun x => x.1) (Option.some.inj hr_obs)).trans hrtag
      unfold Miri.TreeBorrows.BorrowTree.nthParent
      simp only [htm, hmap, bind, Bind.bind, pure, Pure.pure, Except.bind, Except.pure,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.range', List.forIn_cons, List.forIn_nil,
        hca, hca_par, hra, hra_tag]

private theorem tagLocationShape_of_treeShape
    {cNode : Miri.TreeBorrows.TreeNode}
    {seg : Miri.DataStructures.RangeMapSegment Miri.TreeBorrows.LocationTree}
    {st : Miri.TreeBorrows.Tree.LocationState}
    (after staged : Miri.TreeBorrows.BorrowTree)
    (hshape : Miri.TreeBorrows.BorrowTree.ZeroProtection.View.treeShape after =
      Miri.TreeBorrows.BorrowTree.ZeroProtection.View.treeShape staged)
    (hmap : staged.tagMapping.get retagChildTag = some ⟨1⟩)
    (hchild : staged.nodes.get ⟨1⟩ = some cNode)
    (hseg : staged.locations.entries[0]? = some seg)
    (hperm : seg.data.perms.get ⟨1⟩ = some st) :
    (borrowTreeTagLocationState after retagChildTag).map (fun s => (s.permission, s.accessed)) =
      some (st.permission, st.accessed) := by
  have htm : after.tagMapping = staged.tagMapping := congrArg (fun s => s.1) hshape
  have hnd : after.nodes.data.map (Option.map Miri.TreeBorrows.BorrowTree.ZeroProtection.View.nodeShape) =
      staged.nodes.data.map (Option.map Miri.TreeBorrows.BorrowTree.ZeroProtection.View.nodeShape) :=
    congrArg (fun s => s.2.1) hshape
  have hc_obs := congrArg (fun a => (a[(⟨1⟩ : Miri.TreeBorrows.UniIndex).toNat]?).getD none) hnd
  rw [Miri.TreeBorrows.BorrowTree.ZeroProtection.View.mapped_lookup,
      Miri.TreeBorrows.BorrowTree.ZeroProtection.View.mapped_lookup, hchild] at hc_obs
  have hloc :
      after.locations.entries.map
          (fun segment => (segment.range, Miri.TreeBorrows.BorrowTree.ZeroProtection.View.locationShape segment.data)) =
        staged.locations.entries.map
          (fun segment => (segment.range, Miri.TreeBorrows.BorrowTree.ZeroProtection.View.locationShape segment.data)) :=
    congrArg (fun s => s.2.2.1) hshape
  have hloc0 := congrArg (fun a => a[0]?) hloc
  simp only [Array.getElem?_map, hseg, Option.map_some] at hloc0
  cases hca : after.nodes.get ⟨1⟩ with
  | none => simp [hca] at hc_obs
  | some ca =>
    cases hsa : after.locations.entries[0]? with
    | none => simp [hsa] at hloc0
    | some sa =>
      rw [hsa] at hloc0
      have hlshape := congrArg Prod.snd (Option.some.inj hloc0)
      have hp_obs := congrArg (fun d => (d[(⟨1⟩ : Miri.TreeBorrows.UniIndex).toNat]?).getD none) hlshape
      change ((sa.data.perms.data.map (Option.map Miri.TreeBorrows.BorrowTree.ZeroProtection.View.stateShape))[(⟨1⟩ : Miri.TreeBorrows.UniIndex).toNat]?).getD none =
        ((seg.data.perms.data.map (Option.map Miri.TreeBorrows.BorrowTree.ZeroProtection.View.stateShape))[(⟨1⟩ : Miri.TreeBorrows.UniIndex).toNat]?).getD none at hp_obs
      rw [Miri.TreeBorrows.BorrowTree.ZeroProtection.View.mapped_lookup,
          Miri.TreeBorrows.BorrowTree.ZeroProtection.View.mapped_lookup, hperm] at hp_obs
      cases hpa : sa.data.perms.get ⟨1⟩ with
      | none => simp [hpa] at hp_obs
      | some pa =>
        rw [hpa] at hp_obs
        have hpa_eq : (pa.permission, pa.accessed) = (st.permission, st.accessed) :=
          Option.some.inj hp_obs
        unfold borrowTreeTagLocationState Miri.TreeBorrows.BorrowTree.indexOfTag
          Miri.TreeBorrows.BorrowTree.locationStateAt Miri.TreeBorrows.BorrowTree.nodeAt
        simp [htm, hmap, hsa, hca, hpa, hpa_eq]

private def extractSifa (p : Miri.TreeBorrows.Permission) (prot : Bool) :
    Miri.TreeBorrows.IdempotentForeignAccess :=
  match p.strongestIdempotentForeignAccess prot with
  | .Access s => s
  | .ImpossibleProtectedReservedIM => .None

private theorem rootTree_hatEnd :
    (⟨1⟩ : Miri.TreeBorrows.UniIndex).toNat =
      (Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)).nodes.data.size := by
  decide

section NewChildOperational

attribute [local irreducible] Miri.TreeBorrows.UniValMap.insert

private theorem borrowTree_newChild_8byte_core
    (st : Miri.TreeBorrows.Tree.LocationState)
    (outsidePerm : Miri.TreeBorrows.Permission)
    (isProtected : Bool)
    (hout_init : outsidePerm.isInitial = true)
    (hout_nuniq : outsidePerm.isUnique = false)
    (hout_sifa : outsidePerm.strongestIdempotentForeignAccess isProtected =
      .Access (extractSifa outsidePerm isProtected))
    (hin_init : st.permission.isInitial = true)
    (hin_sifa : st.permission.strongestIdempotentForeignAccess isProtected =
      .Access st.idempotentForeignAccess) :
    let rootTree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let inside := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) st
    let child := rootTree.newChild Miri.ABI.Size.ZERO (.concrete retagParentTag)
      retagChildTag inside outsidePerm isProtected
    child.outcome = .ok () ∧
    child.tree.nthParent retagChildTag 1 = .ok retagParentTag ∧
    (borrowTreeTagLocationState child.tree retagChildTag).map (fun s => (s.permission, s.accessed)) =
      some (st.permission, st.accessed) := by
  let rootTree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
  let outSifa := extractSifa outsidePerm isProtected
  let rootNode : Miri.TreeBorrows.TreeNode :=
    ⟨retagParentTag, none, #[], .Disabled, .None, false, none⟩
  let childNode : Miri.TreeBorrows.TreeNode :=
    ⟨retagChildTag, some ⟨0⟩, #[], outsidePerm, outSifa, false, none⟩
  let freshLoc : Miri.TreeBorrows.LocationTree :=
    { perms := ({} : Miri.TreeBorrows.UniValMap Miri.TreeBorrows.Tree.LocationState).insert
        ⟨0⟩ ⟨.Unique, true, .None⟩
      exposedCache := {} }
  let mapping : Miri.TreeBorrows.UniKeyMap Miri.Memory.BorTag :=
    { mapping := #[(retagParentTag, ⟨0⟩), (retagChildTag, ⟨1⟩)], deassigned := #[] }
  have hinserted : rootTree.tagMapping.insert retagChildTag = .Inserted mapping ⟨1⟩ := rfl
  have htagged : rootTree.tagMapping.get retagParentTag = some ⟨0⟩ := by decide
  have hrpres : rootTree.nodes.get ⟨0⟩ = some rootNode :=
    Miri.TreeBorrows.BorrowTree.ZeroProtection.Sparse.get_same {} ⟨0⟩ rootNode
  have hatEnd : (⟨1⟩ : Miri.TreeBorrows.UniIndex).toNat = rootTree.nodes.data.size :=
    rootTree_hatEnd
  have hdiff := Miri.TreeBorrows.BorrowTree.ZeroProtection.Append.parent_not_fresh
    rootTree.nodes ⟨1⟩ ⟨0⟩ rootNode hatEnd hrpres
  have hlookup := (Miri.TreeBorrows.BorrowTree.ZeroProtection.Append.append_get_other
    rootTree.nodes ⟨1⟩ ⟨0⟩ childNode hatEnd hdiff).trans hrpres
  have hloc : rootTree.locations =
      Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) freshLoc := rfl
  have hmod := modifyRange_new_full (Miri.ABI.Size.ofBytes 8) freshLoc (by decide)
    (fun _ location => { location with perms := location.perms.insert ⟨1⟩ st })
  have hiter8 : (Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) st).iterAll =
      #[⟨⟨0, 8⟩, st⟩] := rfl
  have hadd0 : Miri.ABI.Size.add (Miri.ABI.Size.ofBytes 0) Miri.ABI.Size.ZERO =
      .ok Miri.ABI.Size.ZERO := rfl
  have hsub8 : Miri.ABI.Size.ofBytes ((8 : UInt64) - 0) = Miri.ABI.Size.ofBytes 8 := rfl
  dsimp only [rootTree, childNode] at hinserted htagged hrpres hlookup hloc ⊢
  unfold Miri.TreeBorrows.BorrowTree.newChild
  rw [hinserted]
  simp only [htagged, Option.map_some, Bool.false_eq_true, ↓reduceIte,
    hout_init, hout_nuniq, hout_sifa, Bool.not_true, Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hlookup, hiter8]
  simp only [← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
    hin_init, hin_sifa, bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    hadd0, bind, Bind.bind, pure, Pure.pure]
  rw [hloc, hsub8, hmod]
  dsimp only []
  let modLocs := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8)
    { freshLoc with perms := freshLoc.perms.insert ⟨1⟩ st }
  let baseForSifa : Miri.TreeBorrows.BorrowTree :=
    { rootTree with tagMapping := mapping, locations := modLocs }
  let staged : Miri.TreeBorrows.BorrowTree :=
    { baseForSifa with
      nodes := Miri.TreeBorrows.BorrowTree.ZeroProtection.Append.attachedNodes
        rootTree.nodes ⟨1⟩ ⟨0⟩ rootNode childNode }
  have hmap1 : staged.tagMapping.get retagChildTag = some ⟨1⟩ := rfl
  have hchild1 : staged.nodes.get ⟨1⟩ = some childNode := by
    change ((rootTree.nodes.insert ⟨1⟩ childNode).insert ⟨0⟩
      { rootNode with children := rootNode.children.push ⟨1⟩ }).get ⟨1⟩ = some childNode
    rw [Miri.TreeBorrows.BorrowTree.ZeroProtection.Sparse.get_other _ ⟨0⟩ ⟨1⟩ _ (Ne.symm hdiff),
        Miri.TreeBorrows.BorrowTree.ZeroProtection.Sparse.get_same]
  have hroot0 : staged.nodes.get ⟨0⟩ = some { rootNode with children := #[⟨1⟩] } :=
    Miri.TreeBorrows.BorrowTree.ZeroProtection.Sparse.get_same _ ⟨0⟩ _
  have hseg0 : staged.locations.entries[0]? =
      some ⟨⟨0, 8⟩, { freshLoc with perms := freshLoc.perms.insert ⟨1⟩ st }⟩ := rfl
  have hperm1 : ({ freshLoc with perms := freshLoc.perms.insert ⟨1⟩ st } :
      Miri.TreeBorrows.LocationTree).perms.get ⟨1⟩ = some st :=
    Miri.TreeBorrows.BorrowTree.ZeroProtection.Sparse.get_same freshLoc.perms ⟨1⟩ st
  refine ⟨?_, ?_, ?_⟩
  · exact Miri.TreeBorrows.BorrowTree.ZeroProtection.Append.sifa_after_attach
      baseForSifa rootTreeParentDepth ⟨1⟩ ⟨0⟩ rootNode childNode hatEnd hrpres rfl _
  · exact nthParent_one_of_treeShape _ staged
      (Miri.TreeBorrows.BorrowTree.ZeroProtection.View.preserves staged ⟨0⟩ _)
      hmap1 hchild1 rfl hroot0 rfl
  · exact tagLocationShape_of_treeShape _ staged
      (Miri.TreeBorrows.BorrowTree.ZeroProtection.View.preserves staged ⟨0⟩ _)
      hmap1 hchild1 hseg0 hperm1

private theorem borrowTree_newChild_zst_core
    (st : Miri.TreeBorrows.Tree.LocationState)
    (outsidePerm : Miri.TreeBorrows.Permission)
    (isProtected : Bool)
    (hout_init : outsidePerm.isInitial = true)
    (hout_nuniq : outsidePerm.isUnique = false)
    (hout_sifa : outsidePerm.strongestIdempotentForeignAccess isProtected =
      .Access (extractSifa outsidePerm isProtected)) :
    let rootTree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let inside := Miri.DataStructures.DedupRangeMap.new Miri.ABI.Size.ZERO st
    let child := rootTree.newChild Miri.ABI.Size.ZERO (.concrete retagParentTag)
      retagChildTag inside outsidePerm isProtected
    child.outcome = .ok () ∧
    child.tree.nthParent retagChildTag 1 = .ok retagParentTag := by
  let rootTree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
  let outSifa := extractSifa outsidePerm isProtected
  let mapping : Miri.TreeBorrows.UniKeyMap Miri.Memory.BorTag :=
    { mapping := #[(retagParentTag, ⟨0⟩), (retagChildTag, ⟨1⟩)], deassigned := #[] }
  let rootNode : Miri.TreeBorrows.TreeNode :=
    ⟨retagParentTag, none, #[], .Disabled, .None, false, none⟩
  let childNode : Miri.TreeBorrows.TreeNode :=
    ⟨retagChildTag, some ⟨0⟩, #[], outsidePerm, outSifa, false, none⟩
  have hinserted : rootTree.tagMapping.insert retagChildTag = .Inserted mapping ⟨1⟩ := rfl
  have htagged : rootTree.tagMapping.get retagParentTag = some ⟨0⟩ := by decide
  have hrpres : rootTree.nodes.get ⟨0⟩ = some rootNode :=
    Miri.TreeBorrows.BorrowTree.ZeroProtection.Sparse.get_same {} ⟨0⟩ rootNode
  have hatEnd : (⟨1⟩ : Miri.TreeBorrows.UniIndex).toNat = rootTree.nodes.data.size :=
    rootTree_hatEnd
  have hdiff := Miri.TreeBorrows.BorrowTree.ZeroProtection.Append.parent_not_fresh
    rootTree.nodes ⟨1⟩ ⟨0⟩ rootNode hatEnd hrpres
  have hlookup := (Miri.TreeBorrows.BorrowTree.ZeroProtection.Append.append_get_other
    rootTree.nodes ⟨1⟩ ⟨0⟩ childNode hatEnd hdiff).trans hrpres
  have hiter0 : (Miri.DataStructures.DedupRangeMap.new Miri.ABI.Size.ZERO st).iterAll = #[] := rfl
  dsimp only [rootTree, childNode] at hinserted htagged hrpres hlookup ⊢
  unfold Miri.TreeBorrows.BorrowTree.newChild
  rw [hinserted]
  simp only [htagged, Option.map_some, Bool.false_eq_true, ↓reduceIte,
    hout_init, hout_nuniq, hout_sifa, Bool.not_true, Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hlookup, hiter0]
  simp only [← Array.forIn_toList, List.forIn_nil, pure, Pure.pure]
  let baseForSifa : Miri.TreeBorrows.BorrowTree := { rootTree with tagMapping := mapping }
  let staged : Miri.TreeBorrows.BorrowTree :=
    { baseForSifa with
      nodes := Miri.TreeBorrows.BorrowTree.ZeroProtection.Append.attachedNodes
        rootTree.nodes ⟨1⟩ ⟨0⟩ rootNode childNode }
  have hmap1 : staged.tagMapping.get retagChildTag = some ⟨1⟩ := rfl
  have hchild1 : staged.nodes.get ⟨1⟩ = some childNode := by
    change ((rootTree.nodes.insert ⟨1⟩ childNode).insert ⟨0⟩
      { rootNode with children := rootNode.children.push ⟨1⟩ }).get ⟨1⟩ = some childNode
    rw [Miri.TreeBorrows.BorrowTree.ZeroProtection.Sparse.get_other _ ⟨0⟩ ⟨1⟩ _ (Ne.symm hdiff),
        Miri.TreeBorrows.BorrowTree.ZeroProtection.Sparse.get_same]
  have hroot0 : staged.nodes.get ⟨0⟩ = some { rootNode with children := #[⟨1⟩] } :=
    Miri.TreeBorrows.BorrowTree.ZeroProtection.Sparse.get_same _ ⟨0⟩ _
  refine ⟨?_, ?_⟩
  · exact Miri.TreeBorrows.BorrowTree.ZeroProtection.Append.sifa_after_attach
      baseForSifa rootTreeParentDepth ⟨1⟩ ⟨0⟩ rootNode childNode hatEnd hrpres rfl outSifa
  · exact nthParent_one_of_treeShape _ staged
      (Miri.TreeBorrows.BorrowTree.ZeroProtection.View.preserves staged ⟨0⟩ outSifa)
      hmap1 hchild1 rfl hroot0 rfl

end NewChildOperational

/-- **`borrowTree_newChild_reference_simulation`**: on an 8-byte live allocation
whose root tag is `retagParentTag`, Miri's `BorrowTree.newChild` across all
`4 × 2 × 2 = 16` `(mode, mutability, frozen)` combinations succeeds (`.ok ()`),
links `retagChildTag`'s parent to `retagParentTag` (`nthParent = .ok retagParentTag`,
certifying `I-10`), and initializes `retagChildTag`'s `[0, 8)` `LocationState`
with `(permission := annealPermToMiri perm, accessed := annealPermToMiri perm != .Cell)`. -/
theorem borrowTree_newChild_reference_simulation
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    let rootTree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let facts : Miri.TreeBorrows.RetagPolicy.TypeFacts :=
      { isUnpin := true, isUnsafeUnpin := true, isFreeze := frozen }
    let perm := annealRetagPerm mode mutability frozen
    ∃ policy st,
      Miri.TreeBorrows.RetagPolicy.create facts (annealRefKindToMiri mutability)
        (annealRetagModeToMiri mode) ⟨false, false⟩ = some policy ∧
      Miri.TreeBorrows.RetagPolicy.initialLocationState policy frozen = .ok st ∧
      let inside := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) st
      let child := rootTree.newChild Miri.ABI.Size.ZERO (.concrete retagParentTag)
        retagChildTag inside policy.outsidePermission policy.protector.isSome
      child.outcome = .ok () ∧
      child.tree.nthParent retagChildTag 1 = .ok retagParentTag ∧
      (borrowTreeTagLocationState child.tree retagChildTag).map (fun s => (s.permission, s.accessed)) =
        some (annealPermToMiri perm, annealPermToMiri perm != .Cell) := by
  obtain ⟨policy, hpol, -, -, -, ⟨st, hst, hp, ha⟩, -⟩ :=
    retag_pipeline_simulation mode mutability frozen
      { isUnpin := true, isUnsafeUnpin := true, isFreeze := frozen } rfl rfl rfl
  refine ⟨policy, st, hpol, hst, ?_⟩
  cases mode <;> cases mutability <;> cases frozen <;>
  · have hpol_eq : policy = _ := Option.some.inj (hpol.symm.trans rfl)
    have hst_eq : st = _ := Except.ok.inj (hst.symm.trans (by rw [hpol_eq]; rfl))
    obtain ⟨h1, h2, h3⟩ := borrowTree_newChild_8byte_core st
      policy.outsidePermission policy.protector.isSome
      (by rw [hpol_eq]; decide) (by rw [hpol_eq]; decide) (by rw [hpol_eq]; decide)
      (by rw [hst_eq]; decide) (by rw [hpol_eq, hst_eq]; decide)
    have ha_eq : st.accessed = (st.permission != .Cell) := by
      rw [hst_eq]; decide
    refine ⟨h1, h2, ?_⟩
    rw [ha_eq, hp] at h3
    exact h3

private def expectedAccessTreeForReborrow
    (result : Miri.TreeBorrows.RetagPipeline.Result Unit)
    (request : Miri.TreeBorrows.RetagPipeline.Request)
    (inside : Miri.DataStructures.DedupRangeMap Miri.TreeBorrows.Tree.LocationState)
    (c : Miri.TreeBorrows.BorrowTree.ChildInsertResult) :
    Miri.TreeBorrows.RetagPipeline.Result Unit := Id.run do
  let location : Miri.TreeBorrows.RetagPipeline.ResolvedLocation :=
    ⟨retagTestAllocId, Miri.ABI.Size.ZERO, .concrete retagParentTag⟩
  let allocationMutability : Miri.Memory.Mutability := .Mut
  let newTag := retagChildTag
  let mut current := result
  let mut dataRacePosition := 0
  for segment in inside.iterAll do
    match segment.data.permission.associatedAccess with
    | none => pure ()
    | some kind =>
        if kind == .Write && allocationMutability == .Not then
          return { current with outcome := .error (.writeToReadOnly location.allocId) }
        let absoluteOffset? := match Miri.ABI.Size.add location.baseOffset
            (Miri.ABI.Size.ofBytes segment.range.start) with
          | .ok offset => some offset
          | .error _ => none
        let some absoluteOffset := absoluteOffset?
          | return { current with outcome := .error (.offsetOverflow location.baseOffset segment.range.start) }
        let length := Miri.ABI.Size.ofBytes (segment.range.stop - segment.range.start)
        let absoluteEnd? := match Miri.ABI.Size.add absoluteOffset length with
          | .ok endOffset => some endOffset
          | .error _ => none
        let some absoluteEnd := absoluteEnd?
          | return { current with outcome := .error (.rangeEndOverflow absoluteOffset length) }
        let range : Miri.DataStructures.ByteRange := ⟨absoluteOffset.bytes, absoluteEnd.bytes⟩
        current := { current with events := current.events.push (.parentTreeAccess kind range) }
        let some localEntry := current.state.memory.live.find? fun entry => entry.1 == location.allocId
          | return { current with outcome := .error (.treeExtraUnavailable location.allocId) }
        let access := localEntry.2.allocation.extra.performBorrowAccessRange
          location.parentProvenance absoluteOffset length kind
          current.state.global.protectedTags .VisitChildrenOfAccessed
        let nextMemory ← match (match current.state.memory.live.find? fun entry => entry.1 == location.allocId with
            | none => Except.error (Miri.Memory.AllocationLookupError.unavailable location.allocId)
            | some le => current.state.memory.setLiveAllocation location.allocId (le.2.allocation.setExtra access.tree)) with
          | .ok memory => pure memory
          | .error error => return { current with outcome := .error (.memoryUpdate error) }
        current := { current with state := { current.state with memory := nextMemory } }
        if access.status != .Completed then
          return { current with outcome := .error (.treeAccess range access.status) }
        if length.bytes != 0 then
          match request.hooks.dataRace with
          | none => pure ()
          | some hooks =>
              current := { current with events := current.events.push (.dataRaceAccess kind range) }
              match hooks[dataRacePosition]? with
              | none => return { current with outcome := .error (.missingDataRaceResult dataRacePosition) }
              | some (Except.error message) => return { current with outcome := .error (.dataRace message) }
              | some (Except.ok ()) => pure ()
              dataRacePosition := dataRacePosition + 1
  let some liveEntry := current.state.memory.live.find? fun entry => entry.1 == location.allocId
    | return { current with outcome := .error (.treeExtraUnavailable location.allocId) }
  let nextMemory ← match (match current.state.memory.live.find? fun entry => entry.1 == location.allocId with
      | none => Except.error (Miri.Memory.AllocationLookupError.unavailable location.allocId)
      | some le => current.state.memory.setLiveAllocation location.allocId (le.2.allocation.setExtra c.tree)) with
    | .ok memory => pure memory
    | .error error => return { current with outcome := .error (.memoryUpdate error) }
  let _ := liveEntry
  current := { current with state := { current.state with memory := nextMemory } }
  match c.outcome with
  | .error error => return { current with outcome := .error (.childInsert error) }
  | .ok () => pure ()
  return { current with events := current.events.push (.childInserted newTag) }

private def expectedRetagResult (sz : Miri.ABI.Size)
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool)
    (prot : Option Miri.TreeBorrows.ProtectorKind)
    (st : Miri.TreeBorrows.Tree.LocationState)
    (c : Miri.TreeBorrows.BorrowTree.ChildInsertResult) :
    Miri.TreeBorrows.RetagPipeline.Result Unit := Id.run do
  let req := retagRefRequest sz mode mutability frozen
  let g0 := retagInitialMachineState.global
  let g1 := { g0 with nextPointerTag := ⟨3, by decide⟩ }
  let tracked := g1.isTrackedPointerTag retagChildTag
  let (g2, f2) := match prot with
    | some p => g1.addProtector {} retagTestAllocId retagChildTag p
    | none => (g1, {})
  let evs0 : Array Miri.TreeBorrows.RetagPipeline.Event :=
    #[.placeConverted, .reborrowSizeSelected sz, .pointerTagAllocated retagChildTag,
      .pointerAccessChecked, .allocationResolution (some retagTestAllocId),
      .creationLogCalled retagChildTag (some retagTestAllocId) tracked]
  let evs1 := match prot with
    | some p => evs0.push (.protectorRegistered retagChildTag p)
    | none => evs0
  let baseEvs := (evs1.push (.allocationKindChecked retagTestAllocId .liveData)).push
    (.allocationExtraLoaded retagTestAllocId)
  let baseRes : Miri.TreeBorrows.RetagPipeline.Result Unit :=
    { state := { memory := retagInitialMachineState.memory, global := g2, frame := f2 }
      outcome := .ok none
      events := baseEvs }
  let inside := Miri.DataStructures.DedupRangeMap.new sz st
  let afterAccess := expectedAccessTreeForReborrow baseRes req inside c
  let prov := some (Miri.Memory.Provenance.concrete retagTestAllocId retagChildTag)
  let reborrowed : Miri.TreeBorrows.RetagPipeline.Result Unit :=
    match afterAccess.outcome with
    | .error _ => afterAccess
    | .ok _ =>
      let r := { afterAccess with events := afterAccess.events.push (.reborrowReturned prov) }
      { r with outcome := .ok prov }
  match reborrowed.outcome with
  | .error _ => return reborrowed
  | .ok provenance =>
    return { reborrowed with
      events := (reborrowed.events.push (.placeProvenanceReplaced provenance)).push
        .retaggedValueReconstructed }

private def retagPolOf (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    Miri.TreeBorrows.RetagPolicy.NewPermission :=
  (Miri.TreeBorrows.RetagPolicy.create
    { isUnpin := true, isUnsafeUnpin := true, isFreeze := frozen }
    (annealRefKindToMiri mutability) (annealRetagModeToMiri mode) ⟨false, false⟩).getD
    ⟨.Frozen, .Frozen, .Frozen, none⟩

private def retagStOf (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    Miri.TreeBorrows.Tree.LocationState :=
  match Miri.TreeBorrows.RetagPolicy.initialLocationState (retagPolOf mode mutability frozen) frozen with
  | .ok s => s
  | .error _ => ⟨.Disabled, false, .None⟩

private def retagChildOf (sz : Miri.ABI.Size)
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    Miri.TreeBorrows.BorrowTree.ChildInsertResult :=
  let pol := retagPolOf mode mutability frozen
  let st := retagStOf mode mutability frozen
  (Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)).newChild
    Miri.ABI.Size.ZERO (.concrete retagParentTag) retagChildTag
    (Miri.DataStructures.DedupRangeMap.new sz st)
    pol.outsidePermission pol.protector.isSome

section RetagOperational

attribute [local irreducible] Miri.TreeBorrows.BorrowTree.newChild

private theorem retagPointerValue_zst_eq_expected
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    Miri.TreeBorrows.RetagPipeline.retagPointerValue
      retagInitialMachineState (retagRefRequest Miri.ABI.Size.ZERO mode mutability frozen) =
    expectedRetagResult Miri.ABI.Size.ZERO mode mutability frozen
      (retagPolOf mode mutability frozen).protector
      (retagStOf mode mutability frozen)
      (retagChildOf Miri.ABI.Size.ZERO mode mutability frozen) := by
  cases mode <;> cases mutability <;> cases frozen <;> rfl

private theorem retagPointerValue_cell_8byte_eq_expected (mode : AnnealRetagMode) :
    Miri.TreeBorrows.RetagPipeline.retagPointerValue
      retagInitialMachineState (retagRefRequest (Miri.ABI.Size.ofBytes 8) mode .not false) =
    expectedRetagResult (Miri.ABI.Size.ofBytes 8) mode .not false
      (retagPolOf mode .not false).protector
      (retagStOf mode .not false)
      (retagChildOf (Miri.ABI.Size.ofBytes 8) mode .not false) := by
  cases mode <;> rfl

end RetagOperational

private theorem not_tracked_retagChildTag :
    ({ retagInitialMachineState.global with nextPointerTag := ⟨3, by decide⟩ } :
      Miri.TreeBorrows.GlobalState).isTrackedPointerTag retagChildTag = false := by
  simp [retagInitialMachineState, Miri.TreeBorrows.GlobalState.isTrackedPointerTag]

private theorem retagInitialMachineState_memory :
    retagInitialMachineState.memory =
      liveTreeMemory (Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)) :=
  rfl

/-- **`retagPointerValue_zst_reference_simulation`**: executing Miri's operational
`RetagPipeline.retagPointerValue` on `retagInitialMachineState` for zero-sized
(`Size.ZERO`) reference reborrows across all `4 × 2 × 2 = 16`
`(mode, mutability, frozen)` combinations:
1. allocates `retagChildTag` and returns `.ok (some (.concrete retagTestAllocId retagChildTag))`;
2. registers `retagChildTag` in both `GlobalState.protectedTags` and
   `FrameState.protectedTags` iff `mode = .fnEntry`, and `GlobalState.endCall`
   removes that protector on return;
3. emits `Event.childInserted retagChildTag` and links `nthParent retagChildTag 1`
   to `retagParentTag` in `retagTestAllocId`'s live `BorrowTree`. -/
theorem retagPointerValue_zst_reference_simulation
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    let res := Miri.TreeBorrows.RetagPipeline.retagPointerValue
      retagInitialMachineState (retagRefRequest Miri.ABI.Size.ZERO mode mutability frozen)
    res.outcome = .ok (some (.concrete retagTestAllocId retagChildTag)) ∧
    res.state.global.protectedTags.contains retagChildTag = (mode == .fnEntry) ∧
    res.state.frame.protectedTags =
      (if mode == .fnEntry then #[(retagTestAllocId, retagChildTag)] else #[]) ∧
    (res.state.global.endCall res.state.frame).protectedTags.contains retagChildTag = false ∧
    Miri.TreeBorrows.RetagPipeline.Event.childInserted retagChildTag ∈ res.events.toList ∧
    (res.state.memory.live.find? fun e => e.1 == retagTestAllocId).bind
        (fun e => (e.2.allocation.extra.nthParent retagChildTag 1).toOption) =
      some retagParentTag := by
  dsimp only []
  rw [retagPointerValue_zst_eq_expected]
  obtain ⟨hch_ok, hch_par⟩ := borrowTree_newChild_zst_core
    (retagStOf mode mutability frozen) (retagPolOf mode mutability frozen).outsidePermission
    (retagPolOf mode mutability frozen).protector.isSome
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
  have hiter0 :
      (Miri.DataStructures.DedupRangeMap.new Miri.ABI.Size.ZERO (retagStOf mode mutability frozen)).iterAll = #[] := rfl
  unfold expectedRetagResult expectedAccessTreeForReborrow
  dsimp only [retagChildOf]
  rw [hiter0]
  simp +zetaHave only [Id.run, bind, Bind.bind, pure, Pure.pure,
    ← Array.forIn_toList, List.forIn_nil, not_tracked_retagChildTag,
    retagInitialMachineState_memory, liveTreeMemory_find,
    liveTreeAllocation_setExtra, liveTreeMemory_setLiveAllocation, hch_ok]
  cases mode <;> cases mutability <;> cases frozen <;>
  · refine ⟨trivial, ?_, ?_, ?_, by decide, ?_⟩
    · simp [retagInitialMachineState, retagPolOf, Miri.TreeBorrows.RetagPolicy.create,
        annealRefKindToMiri, annealRetagModeToMiri, Miri.TreeBorrows.GlobalState.addProtector,
        Miri.TreeBorrows.ProtectedTags.contains, Miri.TreeBorrows.ProtectedTags.get,
        Miri.TreeBorrows.ProtectedTags.insert, retagChildTag]
    · simp [retagPolOf, Miri.TreeBorrows.RetagPolicy.create,
        annealRefKindToMiri, annealRetagModeToMiri, Miri.TreeBorrows.GlobalState.addProtector,
        Miri.TreeBorrows.FrameState.addProtector]
    · simp [retagInitialMachineState, retagPolOf, Miri.TreeBorrows.RetagPolicy.create,
        annealRefKindToMiri, annealRetagModeToMiri, Miri.TreeBorrows.GlobalState.addProtector,
        Miri.TreeBorrows.FrameState.addProtector, Miri.TreeBorrows.GlobalState.endCall,
        Miri.TreeBorrows.ProtectedTags.contains, Miri.TreeBorrows.ProtectedTags.get,
        Miri.TreeBorrows.ProtectedTags.insert, Miri.TreeBorrows.ProtectedTags.remove, retagChildTag]
    · dsimp only [Option.bind]
      rw [liveTreeAllocation_extra, hch_par]
      rfl

/-- **`retagPointerValue_cell_8byte_simulation`** (certifying `I-11` retag):
executing Miri's operational `RetagPipeline.retagPointerValue` on an 8-byte
shared `!Freeze` reference (`&UnsafeCell<u64>`, i.e. `mutability = .not, frozen = false`)
across all 4 `AnnealRetagMode`s:
1. allocates `retagChildTag`, registers/releases function-entry protectors iff
   `mode = .fnEntry`, and returns `.ok (some (.concrete retagTestAllocId retagChildTag))`;
2. emits **no** `Event.parentTreeAccess` (matching `Permission.Cell.associatedAccess = none`
   and Anneal's `Places.lean` / `Statements.lean` skip of the initial child read
   when `perm = .cell`);
3. inserts `retagChildTag` under `retagParentTag` (`nthParent = .ok retagParentTag`)
   across `[0, 8)` with `(permission := .Cell, accessed := false)`. -/
theorem retagPointerValue_cell_8byte_simulation (mode : AnnealRetagMode) :
    let res := Miri.TreeBorrows.RetagPipeline.retagPointerValue
      retagInitialMachineState (retagRefRequest (Miri.ABI.Size.ofBytes 8) mode .not false)
    res.outcome = .ok (some (.concrete retagTestAllocId retagChildTag)) ∧
    res.state.global.protectedTags.contains retagChildTag = (mode == .fnEntry) ∧
    res.state.frame.protectedTags =
      (if mode == .fnEntry then #[(retagTestAllocId, retagChildTag)] else #[]) ∧
    (res.state.global.endCall res.state.frame).protectedTags.contains retagChildTag = false ∧
    (∀ k r, Miri.TreeBorrows.RetagPipeline.Event.parentTreeAccess k r ∉ res.events.toList) ∧
    Miri.TreeBorrows.RetagPipeline.Event.childInserted retagChildTag ∈ res.events.toList ∧
    (res.state.memory.live.find? fun e => e.1 == retagTestAllocId).bind
        (fun e => (e.2.allocation.extra.nthParent retagChildTag 1).toOption) =
      some retagParentTag ∧
    (liveTagLocationState res.state.memory retagChildTag).map (fun s => (s.permission, s.accessed)) =
      some (.Cell, false) := by
  dsimp only []
  rw [retagPointerValue_cell_8byte_eq_expected]
  obtain ⟨hch_ok, hch_par, hch_loc⟩ := borrowTree_newChild_8byte_core
    (retagStOf mode .not false) (retagPolOf mode .not false).outsidePermission
    (retagPolOf mode .not false).protector.isSome
    (by cases mode <;> decide) (by cases mode <;> decide) (by cases mode <;> decide)
    (by cases mode <;> decide) (by cases mode <;> decide)
  have hiter8 :
      (Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) (retagStOf mode .not false)).iterAll =
        #[⟨⟨0, 8⟩, retagStOf mode .not false⟩] := rfl
  have hassoc : (retagStOf mode .not false).permission.associatedAccess = none := by
    cases mode <;> decide
  unfold expectedRetagResult expectedAccessTreeForReborrow
  dsimp only [retagChildOf]
  rw [hiter8]
  simp +zetaHave only [Id.run, bind, Bind.bind, pure, Pure.pure,
    ← Array.forIn_toList, List.forIn_cons, List.forIn_nil, hassoc, not_tracked_retagChildTag,
    retagInitialMachineState_memory, liveTreeMemory_find,
    liveTreeAllocation_setExtra, liveTreeMemory_setLiveAllocation, hch_ok]
  cases mode <;>
  · refine ⟨trivial, ?_, ?_, ?_, ?_, by decide, ?_, ?_⟩
    · simp [retagInitialMachineState, retagPolOf, Miri.TreeBorrows.RetagPolicy.create,
        annealRefKindToMiri, annealRetagModeToMiri, Miri.TreeBorrows.GlobalState.addProtector,
        Miri.TreeBorrows.ProtectedTags.contains, Miri.TreeBorrows.ProtectedTags.get,
        Miri.TreeBorrows.ProtectedTags.insert, retagChildTag]
    · simp [retagPolOf, Miri.TreeBorrows.RetagPolicy.create,
        annealRefKindToMiri, annealRetagModeToMiri, Miri.TreeBorrows.GlobalState.addProtector,
        Miri.TreeBorrows.FrameState.addProtector]
    · simp [retagInitialMachineState, retagPolOf, Miri.TreeBorrows.RetagPolicy.create,
        annealRefKindToMiri, annealRetagModeToMiri, Miri.TreeBorrows.GlobalState.addProtector,
        Miri.TreeBorrows.FrameState.addProtector, Miri.TreeBorrows.GlobalState.endCall,
        Miri.TreeBorrows.ProtectedTags.contains, Miri.TreeBorrows.ProtectedTags.get,
        Miri.TreeBorrows.ProtectedTags.insert, Miri.TreeBorrows.ProtectedTags.remove, retagChildTag]
    · intro k r hmem
      simp [retagPolOf, Miri.TreeBorrows.RetagPolicy.create,
        annealRefKindToMiri, annealRetagModeToMiri] at hmem
    · dsimp only [Option.bind]
      rw [liveTreeAllocation_extra, hch_par]
      rfl
    · rw [liveTagLocationState_liveTreeMemory]
      exact hch_loc

/-- Location tree for `hooksTwoNodeTree`: root `UniIndex 0` (`Unique`) and child
`UniIndex 1` (`annealPermToMiri perm`, accessed). -/
def hooksLocTree (perm : TreeBorrowPerm) : Miri.TreeBorrows.LocationTree :=
  { perms :=
      ⟨#[some ⟨.Unique, true, .None⟩,
         some ⟨annealPermToMiri perm, true, .None⟩]⟩
    exposedCache := {} }

/-- Two-node `UniValMap` for `hooksTwoNodeTree`. -/
def hooksTwoNodes : Miri.TreeBorrows.UniValMap Miri.TreeBorrows.TreeNode :=
  let rootIdx : Miri.TreeBorrows.UniIndex := ⟨0⟩
  let childIdx : Miri.TreeBorrows.UniIndex := ⟨1⟩
  let rootNode : Miri.TreeBorrows.TreeNode :=
    { tag := retagParentTag
      parent := none
      children := #[childIdx]
      defaultInitialPermission := .Disabled
      defaultInitialSifa := .None }
  let childNode : Miri.TreeBorrows.TreeNode :=
    { tag := retagChildTag
      parent := some rootIdx
      children := #[]
      defaultInitialPermission := .Disabled
      defaultInitialSifa := .None }
  ⟨#[some rootNode, some childNode]⟩

/-- Two-node `BorrowTree` on `[0, 8)` with root `retagParentTag` (`Unique`,
`UniIndex 0`) and child `retagChildTag` (`annealPermToMiri perm`, accessed,
`UniIndex 1`) for operational `TreeState` and `MachineMemoryHooks` correspondence. -/
def hooksTwoNodeTree (perm : TreeBorrowPerm) : Miri.TreeBorrows.BorrowTree :=
  { tagMapping :=
      { mapping := #[(retagParentTag, ⟨0⟩), (retagChildTag, ⟨1⟩)]
        deassigned := #[] }
    nodes := hooksTwoNodes
    locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) (hooksLocTree perm)
    roots := #[⟨0⟩] }

/-- Trivial data-race/sync callback bundle for `MachineMemoryHooks` with
`retagChildTag` protected iff `isProtected = true`. -/
def hooksForChildProtected (isProtected : Bool) :
    Miri.TreeBorrows.MachineMemoryHooks.Hooks Unit Unit Unit :=
  { protectedTags :=
      if isProtected then
        ({} : Miri.TreeBorrows.ProtectedTags).insert retagChildTag .StrongProtector
      else {}
    emitDiagnostic := fun s _ _ => s
    dataRaceRead := fun s _ _ _ => ⟨s, .ok ()⟩
    dataRaceWrite := fun s _ _ _ => ⟨s, .ok ()⟩
    dataRaceDeallocate := fun s _ _ _ _ => ⟨s, .ok ()⟩
    syncOnAccess := fun s _ _ => ⟨s, .ok ()⟩
    deleteOnWrite := fun _ => false
    recordDeallocatedSpan := fun s _ => s
    freeAllocId := fun s _ _ _ _ => s }

/-- Node index in `hooksTwoNodeTree` corresponding to a `localAccess` (`⟨1⟩`,
`retagChildTag`) vs `foreignAccess` (`⟨0⟩`, `retagParentTag`) relative to
`retagChildTag`. -/
def hooksAccessIndex : TreeBorrowRelatedness → Miri.TreeBorrows.UniIndex
  | .localAccess => ⟨1⟩
  | .foreignAccess => ⟨0⟩

private theorem hooksTwoNodes_entries :
    hooksTwoNodes.entries =
      #[(⟨0⟩, ⟨retagParentTag, none, #[⟨1⟩], .Disabled, .None, false, none⟩),
        (⟨1⟩, ⟨retagChildTag, some ⟨0⟩, #[], .Disabled, .None, false, none⟩)] := by
  unfold hooksTwoNodes Miri.TreeBorrows.UniValMap.entries
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  decide

private def hooksFailingNode? : Miri.TreeBorrows.Tree.NormalAccessStatus → Option Nat
  | .Completed => none
  | .TransitionError node _
  | .RecordDebugAssertion node
  | .PermissionInvariantFailure node
  | .TransitionApplicationInvariantFailure node
  | .PossibleInvariantFailure node
  | .MissingLocationState node => some node

private def hooksExpectedNormalProj (perm : TreeBorrowPerm)
    (ents : Array (Miri.TreeBorrows.UniIndex × Miri.TreeBorrows.TreeNode))
    (isProtected : Bool) : Miri.TreeBorrows.Tree.NormalTreeState :=
  let tree := hooksTwoNodeTree perm
  let location := hooksLocTree perm
  let protectedTags := (hooksForChildProtected isProtected).protectedTags
  let defaults := tree.nodes.data.map fun entry =>
    match entry with
    | some node => node.defaultLocationState
    | none => ⟨.Disabled, false, .None⟩
  let locationStates := tree.nodes.data.mapIdx fun position _ =>
    match Miri.TreeBorrows.UniIndex.ofNat? position with
    | none => none
    | some index => location.perms.get index
  let protectedNodes := ents.toList.filterMap fun (index, node) =>
    if protectedTags.contains node.tag then some index.toNat else none
  { topology :=
      ⟨tree.nodes.data.map fun entry =>
        match entry with
        | none => ⟨none, []⟩
        | some node =>
            ⟨node.parent.map Miri.TreeBorrows.UniIndex.toNat,
              node.children.toList.map Miri.TreeBorrows.UniIndex.toNat⟩⟩
    defaultStates := defaults
    protectedNodes
    locationStates }

private def hooksExpectedPerformAt (perm : TreeBorrowPerm)
    (ents : Array (Miri.TreeBorrows.UniIndex × Miri.TreeBorrows.TreeNode))
    (rel : TreeBorrowRelatedness) (kind : TreeBorrowAccessKind) (isProtected : Bool) :
    Miri.TreeBorrows.BorrowTree.NormalLocationAccessResult := Id.run do
  let tree := hooksTwoNodeTree perm
  let location := hooksLocTree perm
  let protectedTags := (hooksForChildProtected isProtected).protectedTags
  let access := Miri.TreeBorrows.Tree.NormalTreeState.performAccess
    (hooksExpectedNormalProj perm ents isProtected)
    (hooksAccessIndex rel).toNat (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
  let mut nextLocation := location
  for position in [:access.tree.locationStates.size] do
    match access.tree.locationStates[position]? with
    | some (some state) =>
        match Miri.TreeBorrows.UniIndex.ofNat? position with
        | some index =>
            nextLocation := { nextLocation with perms := nextLocation.perms.insert index state }
        | none => pure ()
    | _ => pure ()
  let mut cacheOutcome : Except Miri.TreeBorrows.ExposedCacheError Unit := .ok ()
  for event in access.visited do
    if cacheOutcome matches .ok _ then
      match Miri.TreeBorrows.UniIndex.ofNat? event.node with
      | none => cacheOutcome := .error (.InvalidIndex event.node)
      | some index =>
        match tree.nodeAt index with
        | none => cacheOutcome := .error (.MissingNode index)
        | some node =>
          if node.isExposed && hooksFailingNode? access.status != some event.node then
            match tree.locationStateAt location index, access.tree.stateAt event.node with
            | some oldState, some newState =>
                match Miri.TreeBorrows.performAccessTransition
                    (annealAccessKindToMiri kind) event.relatedness oldState.permission
                    (protectedTags.contains node.tag) with
                | .Transition transition =>
                    if !transition.isNoop then
                      let oldLevel := oldState.permission.strongestAllowedLocalAccess
                        (protectedTags.contains node.tag)
                      let newLevel := newState.permission.strongestAllowedLocalAccess
                        (protectedTags.contains node.tag)
                      let update := nextLocation.exposedCache.updateExposure tree.nodes index
                        oldLevel newLevel
                      nextLocation := { nextLocation with exposedCache := update.cache }
                      cacheOutcome := update.outcome
                | .UndefinedBehavior | .ImpossibleProtectedReservedIM => pure ()
            | _, _ => cacheOutcome := .error (.MissingNode index)
  return { location := nextLocation, access, outcome := cacheOutcome }

section NormalAccessAtStep

attribute [local irreducible] Miri.TreeBorrows.UniValMap.entries
attribute [local irreducible] Miri.TreeBorrows.Tree.NormalTreeState.performAccess

private theorem performNormalAccessAt_eq_expected
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
      (hooksAccessIndex rel) (annealAccessKindToMiri kind)
      (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed =
    hooksExpectedPerformAt perm hooksTwoNodes.entries rel kind isProtected := by
  cases kind <;> cases rel <;> (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases isProtected <;> rfl

end NormalAccessAtStep

private def normalAccessAtGoal
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) : Prop :=
  let res := (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
    (hooksAccessIndex rel) (annealAccessKindToMiri kind)
    (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
  let out := treeBorrowNodeAccess kind rel perm isProtected
  let dummy : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := perm }
  res.outcome = .ok () ∧
  res.access.root = 0 ∧
  (res.access.status = .Completed ↔ treeBorrowTransitionIsUB out = false) ∧
  (res.access.status = .Completed →
    (res.location.perms.get ⟨1⟩).map (·.permission) =
      some (annealPermToMiri (applyTreeBorrowTransition dummy out).perm))

private theorem hooksExpectedNormalProj_eq (perm : TreeBorrowPerm) (isProtected : Bool) :
    hooksExpectedNormalProj perm
        #[(⟨0⟩, ⟨retagParentTag, none, #[⟨1⟩], .Disabled, .None, false, none⟩),
          (⟨1⟩, ⟨retagChildTag, some ⟨0⟩, #[], .Disabled, .None, false, none⟩)]
        isProtected =
      { topology := ⟨#[⟨none, [1]⟩, ⟨some 0, []⟩]⟩
        defaultStates := #[⟨.Disabled, false, .None⟩, ⟨.Disabled, false, .None⟩]
        protectedNodes := if isProtected then [1] else []
        locationStates :=
          #[some ⟨.Unique, true, .None⟩, some ⟨annealPermToMiri perm, true, .None⟩] } := by
  cases isProtected <;>
    simp [hooksExpectedNormalProj, hooksTwoNodeTree, hooksTwoNodes, hooksLocTree,
      hooksForChildProtected, Miri.TreeBorrows.TreeNode.defaultLocationState,
      Miri.TreeBorrows.UniIndex.ofNat?, Miri.TreeBorrows.UniIndex.toNat,
      Miri.TreeBorrows.UniValMap.get,
      Miri.TreeBorrows.ProtectedTags.contains, Miri.TreeBorrows.ProtectedTags.get,
      Miri.TreeBorrows.ProtectedTags.insert, retagParentTag, retagChildTag,
      Miri.Memory.BorTag.one]

private theorem normalAccessAt_read_local (perm : TreeBorrowPerm) (isProtected : Bool) :
    normalAccessAtGoal .read .localAccess perm isProtected := by
  dsimp only [normalAccessAtGoal]
  rw [performNormalAccessAt_eq_expected, hooksTwoNodes_entries]
  unfold hooksExpectedPerformAt
  rw [hooksExpectedNormalProj_eq]
  (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases isProtected <;>
  · simp +zetaHave only [Id.run, bind, Bind.bind, pure, Pure.pure,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    decide

private theorem normalAccessAt_read_foreign (perm : TreeBorrowPerm) (isProtected : Bool) :
    normalAccessAtGoal .read .foreignAccess perm isProtected := by
  dsimp only [normalAccessAtGoal]
  rw [performNormalAccessAt_eq_expected, hooksTwoNodes_entries]
  unfold hooksExpectedPerformAt
  rw [hooksExpectedNormalProj_eq]
  (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases isProtected <;>
  · simp +zetaHave only [Id.run, bind, Bind.bind, pure, Pure.pure,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    decide

private theorem normalAccessAt_write_local (perm : TreeBorrowPerm) (isProtected : Bool) :
    normalAccessAtGoal .write .localAccess perm isProtected := by
  dsimp only [normalAccessAtGoal]
  rw [performNormalAccessAt_eq_expected, hooksTwoNodes_entries]
  unfold hooksExpectedPerformAt
  rw [hooksExpectedNormalProj_eq]
  (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases isProtected <;>
  · simp +zetaHave only [Id.run, bind, Bind.bind, pure, Pure.pure,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    decide

private theorem normalAccessAt_write_foreign (perm : TreeBorrowPerm) (isProtected : Bool) :
    normalAccessAtGoal .write .foreignAccess perm isProtected := by
  dsimp only [normalAccessAtGoal]
  rw [performNormalAccessAt_eq_expected, hooksTwoNodes_entries]
  unfold hooksExpectedPerformAt
  rw [hooksExpectedNormalProj_eq]
  (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases isProtected <;>
  · simp +zetaHave only [Id.run, bind, Bind.bind, pure, Pure.pure,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    decide

/-- **`borrowTree_performNormalAccessAt_simulation`**: Miri's operational
`BorrowTree.performNormalAccessAt` (`TreeState.lean`) on `hooksTwoNodeTree perm`
across all `2 × 2 × 7 × 2 = 56` `(kind, rel, perm, isProtected)` combinations
has `outcome = .ok ()`, completes (`access.status = .Completed`) iff Anneal's
`treeBorrowNodeAccess kind rel perm isProtected` is non-UB, and whenever it
completes, writes back the exact mapped Anneal successor permission at child
index `⟨1⟩`. -/
theorem borrowTree_performNormalAccessAt_simulation
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    let res := (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
      (hooksAccessIndex rel) (annealAccessKindToMiri kind)
      (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
    let out := treeBorrowNodeAccess kind rel perm isProtected
    let dummy : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := perm }
    res.outcome = .ok () ∧
    res.access.root = 0 ∧
    (res.access.status = .Completed ↔ treeBorrowTransitionIsUB out = false) ∧
    (res.access.status = .Completed →
      (res.location.perms.get ⟨1⟩).map (·.permission) =
        some (annealPermToMiri (applyTreeBorrowTransition dummy out).perm)) := by
  cases kind <;> cases rel
  · exact normalAccessAt_read_local perm isProtected
  · exact normalAccessAt_read_foreign perm isProtected
  · exact normalAccessAt_write_local perm isProtected
  · exact normalAccessAt_write_foreign perm isProtected

private def expectedHooksWriteResult
    (acc : Miri.TreeBorrows.BorrowTree.BorrowTreeAccessResult) :
    Miri.TreeBorrows.MachineMemoryHooks.AccessResult Unit Unit Unit :=
  let nextMem := liveTreeMemory acc.tree
  if acc.status != .Completed then
    { memory := nextMem
      context := ⟨(), .empty, false, #[]⟩
      outcome := .error s!"Tree Borrows write failed: {reprStr acc.status}" }
  else
    { memory := nextMem
      context := ⟨(), Miri.TreeBorrows.MachineMemoryHooks.SyncObjectStore.empty.set retagTestAllocId .empty, false, #[]⟩
      outcome := .ok () }

section HooksWriteOperational

attribute [local irreducible] Miri.TreeBorrows.BorrowTree.performBorrowAccessRange

/-- **`machineMemoryHooks_fresh_root_write_simulation`**: Miri's operational
`MachineMemoryHooks.beforeMemoryWrite` across the full 8-byte range `[0, 8)` on
a live allocation carrying `BorrowTree.new retagParentTag (Size.ofBytes 8)`
succeeds (`.ok ()`) and preserves `liveTreeMemory` for any global `protectedTags`
map (via vendored `BorrowTree.fresh_root_full_write`). -/
theorem machineMemoryHooks_fresh_root_write_simulation
    (isProtected : Bool) :
    let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let mem := liveTreeMemory tree
    let alloc := liveTreeAllocation tree
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId retagParentTag)⟩
    let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
    let res := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite
      mem ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      alloc ptr retagTestAllocId (.concrete retagParentTag) range
    res.outcome = .ok () ∧ res.memory = mem := by
  let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
  have hfresh := Miri.TreeBorrows.BorrowTree.fresh_root_full_write
    retagParentTag (Miri.ABI.Size.ofBytes 8) (hooksForChildProtected isProtected).protectedTags
  dsimp only [] at hfresh
  let acc := tree.performBorrowAccessRange (.concrete retagParentTag)
    Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) .Write
    (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
  have hstep : Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite
      (liveTreeMemory tree) ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      (liveTreeAllocation tree) ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId retagParentTag)⟩
      retagTestAllocId (.concrete retagParentTag)
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) =
      expectedHooksWriteResult acc := by
    cases isProtected <;> rfl
  dsimp only []
  rw [hstep]
  dsimp only [expectedHooksWriteResult]
  rw [hfresh.1, hfresh.2]
  exact ⟨rfl, rfl⟩

end HooksWriteOperational

section RootReadOperational

private def rootFreshLoc : Miri.TreeBorrows.LocationTree :=
  { perms := ({} : Miri.TreeBorrows.UniValMap Miri.TreeBorrows.Tree.LocationState).insert
      ⟨0⟩ ⟨.Unique, true, .None⟩
    exposedCache := {} }

private def rootFreshNormal : Miri.TreeBorrows.Tree.NormalTreeState :=
  ⟨⟨#[⟨none, []⟩]⟩, #[⟨.Disabled, false, .None⟩], [], #[some ⟨.Unique, true, .None⟩]⟩

private def rootExpectedNormalProj (prot : Option Miri.TreeBorrows.ProtectorKind)
    (ents : Array (Miri.TreeBorrows.UniIndex × Miri.TreeBorrows.TreeNode)) :
    Miri.TreeBorrows.Tree.NormalTreeState :=
  let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
  let location := rootFreshLoc
  let protectedTags : Miri.TreeBorrows.ProtectedTags :=
    match prot with
    | some p => ({} : Miri.TreeBorrows.ProtectedTags).insert retagChildTag p
    | none => {}
  let defaults := tree.nodes.data.map fun entry =>
    match entry with
    | some node => node.defaultLocationState
    | none => ⟨.Disabled, false, .None⟩
  let locationStates := tree.nodes.data.mapIdx fun position _ =>
    match Miri.TreeBorrows.UniIndex.ofNat? position with
    | none => none
    | some index => location.perms.get index
  let protectedNodes := ents.toList.filterMap fun (index, node) =>
    if protectedTags.contains node.tag then some index.toNat else none
  { topology :=
      ⟨tree.nodes.data.map fun entry =>
        match entry with
        | none => ⟨none, []⟩
        | some node =>
            ⟨node.parent.map Miri.TreeBorrows.UniIndex.toNat,
              node.children.toList.map Miri.TreeBorrows.UniIndex.toNat⟩⟩
    defaultStates := defaults
    protectedNodes
    locationStates }

private def rootExpectedPerformNormalRead (prot : Option Miri.TreeBorrows.ProtectorKind)
    (ents : Array (Miri.TreeBorrows.UniIndex × Miri.TreeBorrows.TreeNode)) :
    Miri.TreeBorrows.BorrowTree.NormalLocationAccessResult := Id.run do
  let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
  let location := rootFreshLoc
  let protectedTags : Miri.TreeBorrows.ProtectedTags :=
    match prot with
    | some p => ({} : Miri.TreeBorrows.ProtectedTags).insert retagChildTag p
    | none => {}
  let access := Miri.TreeBorrows.Tree.NormalTreeState.performAccess
    (rootExpectedNormalProj prot ents)
    (⟨0⟩ : Miri.TreeBorrows.UniIndex).toNat .Read .VisitChildrenOfAccessed
  let mut nextLocation := location
  for position in [:access.tree.locationStates.size] do
    match access.tree.locationStates[position]? with
    | some (some state) =>
        match Miri.TreeBorrows.UniIndex.ofNat? position with
        | some index =>
            nextLocation := { nextLocation with perms := nextLocation.perms.insert index state }
        | none => pure ()
    | _ => pure ()
  let mut cacheOutcome : Except Miri.TreeBorrows.ExposedCacheError Unit := .ok ()
  for event in access.visited do
    if cacheOutcome matches .ok _ then
      match Miri.TreeBorrows.UniIndex.ofNat? event.node with
      | none => cacheOutcome := .error (.InvalidIndex event.node)
      | some index =>
        match tree.nodeAt index with
        | none => cacheOutcome := .error (.MissingNode index)
        | some node =>
          if node.isExposed && hooksFailingNode? access.status != some event.node then
            match tree.locationStateAt location index, access.tree.stateAt event.node with
            | some oldState, some newState =>
                match Miri.TreeBorrows.performAccessTransition
                    .Read event.relatedness oldState.permission
                    (protectedTags.contains node.tag) with
                | .Transition transition =>
                    if !transition.isNoop then
                      let oldLevel := oldState.permission.strongestAllowedLocalAccess
                        (protectedTags.contains node.tag)
                      let newLevel := newState.permission.strongestAllowedLocalAccess
                        (protectedTags.contains node.tag)
                      let update := nextLocation.exposedCache.updateExposure tree.nodes index
                        oldLevel newLevel
                      nextLocation := { nextLocation with exposedCache := update.cache }
                      cacheOutcome := update.outcome
                | .UndefinedBehavior | .ImpossibleProtectedReservedIM => pure ()
            | _, _ => cacheOutcome := .error (.MissingNode index)
  return { location := nextLocation, access, outcome := cacheOutcome }

section RootNormalReadStep

attribute [local irreducible] Miri.TreeBorrows.UniValMap.entries
attribute [local irreducible] Miri.TreeBorrows.Tree.NormalTreeState.performAccess

private theorem root_performNormalAccessAt_eq_expected
    (prot : Option Miri.TreeBorrows.ProtectorKind) :
    let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let protectedTags : Miri.TreeBorrows.ProtectedTags :=
      match prot with
      | some p => ({} : Miri.TreeBorrows.ProtectedTags).insert retagChildTag p
      | none => {}
    tree.performNormalAccessAt rootFreshLoc ⟨0⟩ .Read protectedTags .VisitChildrenOfAccessed =
      rootExpectedPerformNormalRead prot tree.nodes.entries := by
  rcases prot with _ | (_ | _) <;> rfl

end RootNormalReadStep

private theorem rootTree_nodes_entries :
    (Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)).nodes.entries =
      #[(⟨0⟩, ⟨retagParentTag, none, #[], .Disabled, .None, false, none⟩)] := by
  unfold Miri.TreeBorrows.BorrowTree.new Miri.TreeBorrows.UniValMap.entries
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  decide

private theorem rootExpectedNormalProj_eq (prot : Option Miri.TreeBorrows.ProtectorKind) :
    rootExpectedNormalProj prot
        #[(⟨0⟩, ⟨retagParentTag, none, #[], .Disabled, .None, false, none⟩)] =
      rootFreshNormal := by
  have hnodes :
      (Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)).nodes =
        ⟨#[some ⟨retagParentTag, none, #[], .Disabled, .None, false, none⟩]⟩ := rfl
  have hperms :
      rootFreshLoc.perms = ⟨#[some ⟨.Unique, true, .None⟩]⟩ := rfl
  unfold rootExpectedNormalProj
  dsimp only []
  rw [hnodes, hperms]
  rcases prot with _ | (_ | _) <;>
    simp [rootFreshNormal, Miri.TreeBorrows.TreeNode.defaultLocationState,
      Miri.TreeBorrows.UniIndex.ofNat?, Miri.TreeBorrows.UniIndex.toNat,
      Miri.TreeBorrows.UniValMap.get,
      Miri.TreeBorrows.ProtectedTags.contains, Miri.TreeBorrows.ProtectedTags.get,
      Miri.TreeBorrows.ProtectedTags.insert, retagParentTag, retagChildTag,
      Miri.Memory.BorTag.one]

private theorem fresh_normal_read_at (prot : Option Miri.TreeBorrows.ProtectorKind) :
    let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let protectedTags : Miri.TreeBorrows.ProtectedTags :=
      match prot with
      | some p => ({} : Miri.TreeBorrows.ProtectedTags).insert retagChildTag p
      | none => {}
    tree.performNormalAccessAt rootFreshLoc ⟨0⟩ .Read protectedTags .VisitChildrenOfAccessed =
      ⟨rootFreshLoc, ⟨rootFreshNormal, 0, [⟨0, .LocalAccess⟩], .Completed⟩, .ok ()⟩ := by
  dsimp only []
  rw [root_performNormalAccessAt_eq_expected, rootTree_nodes_entries]
  unfold rootExpectedPerformNormalRead
  rw [rootExpectedNormalProj_eq]
  rcases prot with _ | (_ | _) <;>
  · simp +zetaHave only [Id.run, bind, Bind.bind, pure, Pure.pure,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    decide

private theorem setAtPos_new_8 (loc loc' : Miri.TreeBorrows.LocationTree) :
    (Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) loc).setAtPos 0 loc' =
      ⟨Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) loc', .ok ()⟩ := rfl

section RootFullReadStep

attribute [local irreducible] Miri.TreeBorrows.BorrowTree.performNormalAccessAt

private theorem uniIndex_ofNat_zero :
    Miri.TreeBorrows.UniIndex.ofNat? 0 = some ⟨0⟩ := rfl

private theorem rootTree_roots :
    (Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)).roots = #[⟨0⟩] := rfl

private theorem rootTree_nodes_get_zero :
    (Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)).nodes.get ⟨0⟩ =
      some ⟨retagParentTag, none, #[], .Disabled, .None, false, none⟩ := by decide

private theorem visitChildren_beq_skip :
    (Miri.TreeBorrows.Tree.ChildrenVisitMode.VisitChildrenOfAccessed == .SkipChildrenOfAccessed) = false := rfl

private theorem fresh_root_full_read (prot : Option Miri.TreeBorrows.ProtectorKind) :
    let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let protectedTags : Miri.TreeBorrows.ProtectedTags :=
      match prot with
      | some p => ({} : Miri.TreeBorrows.ProtectedTags).insert retagChildTag p
      | none => {}
    let result := tree.performBorrowAccessRange (.concrete retagParentTag)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) .Read protectedTags .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = tree := by
  let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
  have hsource : tree.indexOfTag retagParentTag = some ⟨0⟩ := rfl
  have hloc : tree.locations =
      Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) rootFreshLoc := rfl
  have hiter := Miri.DataStructures.DedupRangeMap.iterMut_new_full
    (Miri.ABI.Size.ofBytes 8) rootFreshLoc (by decide)
  have hnorm := fresh_normal_read_at prot
  dsimp only [tree] at hsource hloc hnorm ⊢
  unfold Miri.TreeBorrows.BorrowTree.performBorrowAccessRange
  dsimp only [Id.run]
  rw [hsource, hloc, hiter]
  simp only [bind, Bind.bind, pure, Pure.pure]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size_singleton,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [List.range', List.forIn_cons, List.forIn_nil, bind, Bind.bind, pure, Pure.pure]
  simp only [Option.isNone_some, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Array.getElem?_singleton]
  rw [setAtPos_new_8]
  dsimp only []
  refine ⟨?_, ?_⟩
  · conv =>
      lhs
      arg 1
      arg 1
      arg 2
      arg 2
      arg 1
      whnf
      rw [hnorm]
      simp +zetaHave only [uniIndex_ofNat_zero, rootTree_roots, rootTree_nodes_get_zero,
        visitChildren_beq_skip,
        Id.run, bind, Bind.bind, pure, Pure.pure,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size_singleton,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
        List.range', List.forIn_cons, List.forIn_nil,
        Option.isNone_none, Bool.not_false, Bool.true_and, Bool.false_and,
        bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Array.getElem?_singleton]
  · conv =>
      lhs
      arg 3
      arg 1
      arg 2
      arg 2
      arg 1
      whnf
      rw [hnorm]
      simp +zetaHave only [uniIndex_ofNat_zero, rootTree_roots, rootTree_nodes_get_zero,
        visitChildren_beq_skip,
        Id.run, bind, Bind.bind, pure, Pure.pure,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size_singleton,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
        List.range', List.forIn_cons, List.forIn_nil,
        Option.isNone_none, Bool.not_false, Bool.true_and, Bool.false_and,
        bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Array.getElem?_singleton]
    dsimp only []
    conv =>
      lhs
      arg 3
      arg 2
      arg 1
      whnf
      rw [hnorm]
      simp +zetaHave only [uniIndex_ofNat_zero, rootTree_roots, rootTree_nodes_get_zero,
        visitChildren_beq_skip,
        Id.run, bind, Bind.bind, pure, Pure.pure,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size_singleton,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
        List.range', List.forIn_cons, List.forIn_nil,
        Option.isNone_none, Bool.not_false, Bool.true_and, Bool.false_and,
        bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Array.getElem?_singleton]
    rfl

end RootFullReadStep

private def expectedUpdateTreeExtra [DecidableEq MachineKind]
    (memory : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree MachineKind)
    (allocId : Miri.Memory.AllocId) (tree : Miri.TreeBorrows.BorrowTree) :
    Except Miri.Memory.AllocationLookupError
      (Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree MachineKind) := do
  let some liveEntry := memory.live.find? fun entry => entry.1 == allocId
    | throw (.unavailable allocId)
  let allocation := liveEntry.2.allocation.setExtra tree
  memory.setLiveAllocation allocId allocation

private def expectedAccessTreeForReborrowFull [DecidableEq MachineKind]
    (result : Miri.TreeBorrows.RetagPipeline.Result MachineKind)
    (request : Miri.TreeBorrows.RetagPipeline.Request)
    (policy : Miri.TreeBorrows.RetagPolicy.NewPermission)
    (newTag : Miri.Memory.BorTag)
    (location : Miri.TreeBorrows.RetagPipeline.ResolvedLocation)
    (inside : Miri.DataStructures.DedupRangeMap Miri.TreeBorrows.Tree.LocationState)
    (allocationMutability : Miri.Memory.Mutability) :
    Miri.TreeBorrows.RetagPipeline.Result MachineKind := Id.run do
  let mut current := result
  let mut dataRacePosition := 0
  for segment in inside.iterAll do
    match segment.data.permission.associatedAccess with
    | none => pure ()
    | some kind =>
        if kind == .Write && allocationMutability == .Not then
          return { current with outcome := .error (.writeToReadOnly location.allocId) }
        let absoluteOffset? := match Miri.ABI.Size.add location.baseOffset
            (Miri.ABI.Size.ofBytes segment.range.start) with
          | .ok offset => some offset
          | .error _ => none
        let some absoluteOffset := absoluteOffset?
          | return { current with outcome := .error (.offsetOverflow location.baseOffset segment.range.start) }
        let length := Miri.ABI.Size.ofBytes (segment.range.stop - segment.range.start)
        let absoluteEnd? := match Miri.ABI.Size.add absoluteOffset length with
          | .ok endOffset => some endOffset
          | .error _ => none
        let some absoluteEnd := absoluteEnd?
          | return { current with outcome := .error (.rangeEndOverflow absoluteOffset length) }
        let range : Miri.DataStructures.ByteRange := ⟨absoluteOffset.bytes, absoluteEnd.bytes⟩
        current := { current with events := current.events.push (.parentTreeAccess kind range) }
        let some localEntry := current.state.memory.live.find? fun entry => entry.1 == location.allocId
          | return { current with outcome := .error (.treeExtraUnavailable location.allocId) }
        let access := localEntry.2.allocation.extra.performBorrowAccessRange
          location.parentProvenance absoluteOffset length kind
          current.state.global.protectedTags .VisitChildrenOfAccessed
        let nextMemory ← match expectedUpdateTreeExtra current.state.memory location.allocId access.tree with
          | .ok memory => pure memory
          | .error error => return { current with outcome := .error (.memoryUpdate error) }
        current := { current with state := { current.state with memory := nextMemory } }
        if access.status != .Completed then
          return { current with outcome := .error (.treeAccess range access.status) }
        if length.bytes != 0 then
          match request.hooks.dataRace with
          | none => pure ()
          | some hooks =>
              current := { current with events := current.events.push (.dataRaceAccess kind range) }
              match hooks[dataRacePosition]? with
              | none => return { current with outcome := .error (.missingDataRaceResult dataRacePosition) }
              | some (Except.error message) => return { current with outcome := .error (.dataRace message) }
              | some (Except.ok ()) => pure ()
              dataRacePosition := dataRacePosition + 1
  let some liveEntry := current.state.memory.live.find? fun entry => entry.1 == location.allocId
    | return { current with outcome := .error (.treeExtraUnavailable location.allocId) }
  let child := liveEntry.2.allocation.extra.newChild location.baseOffset
    location.parentProvenance newTag inside policy.outsidePermission
    policy.protector.isSome
  let nextMemory ← match expectedUpdateTreeExtra current.state.memory location.allocId child.tree with
    | .ok memory => pure memory
    | .error error => return { current with outcome := .error (.memoryUpdate error) }
  current := { current with state := { current.state with memory := nextMemory } }
  match child.outcome with
  | .error error => return { current with outcome := .error (.childInsert error) }
  | .ok () => pure ()
  return { current with events := current.events.push (.childInserted newTag) }

private def expectedRetagResultFull (sz : Miri.ABI.Size)
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool)
    (pol : Miri.TreeBorrows.RetagPolicy.NewPermission)
    (st : Miri.TreeBorrows.Tree.LocationState) :
    Miri.TreeBorrows.RetagPipeline.Result Unit := Id.run do
  let req := retagRefRequest sz mode mutability frozen
  let g0 := retagInitialMachineState.global
  let g1 := { g0 with nextPointerTag := ⟨3, by decide⟩ }
  let tracked := g1.isTrackedPointerTag retagChildTag
  let (g2, f2) := match pol.protector with
    | some p => g1.addProtector {} retagTestAllocId retagChildTag p
    | none => (g1, {})
  let evs0 : Array Miri.TreeBorrows.RetagPipeline.Event :=
    #[.placeConverted, .reborrowSizeSelected sz, .pointerTagAllocated retagChildTag,
      .pointerAccessChecked, .allocationResolution (some retagTestAllocId),
      .creationLogCalled retagChildTag (some retagTestAllocId) tracked]
  let evs1 := match pol.protector with
    | some p => evs0.push (.protectorRegistered retagChildTag p)
    | none => evs0
  let baseEvs := (evs1.push (.allocationKindChecked retagTestAllocId .liveData)).push
    (.allocationExtraLoaded retagTestAllocId)
  let baseRes : Miri.TreeBorrows.RetagPipeline.Result Unit :=
    { state := { memory := retagInitialMachineState.memory, global := g2, frame := f2 }
      outcome := .ok none
      events := baseEvs }
  let inside := Miri.DataStructures.DedupRangeMap.new sz st
  let location : Miri.TreeBorrows.RetagPipeline.ResolvedLocation :=
    ⟨retagTestAllocId, Miri.ABI.Size.ZERO, .concrete retagParentTag⟩
  let afterAccess := expectedAccessTreeForReborrowFull baseRes req pol retagChildTag location inside .Mut
  let prov := some (Miri.Memory.Provenance.concrete retagTestAllocId retagChildTag)
  let reborrowed : Miri.TreeBorrows.RetagPipeline.Result Unit :=
    match afterAccess.outcome with
    | .error _ => afterAccess
    | .ok _ =>
      let r := { afterAccess with events := afterAccess.events.push (.reborrowReturned prov) }
      { r with outcome := .ok prov }
  match reborrowed.outcome with
  | .error _ => return reborrowed
  | .ok provenance =>
    return { reborrowed with
      events := (reborrowed.events.push (.placeProvenanceReplaced provenance)).push
        .retaggedValueReconstructed }

section Retag8ByteOperational

attribute [local irreducible] Miri.TreeBorrows.BorrowTree.newChild
attribute [local irreducible] Miri.TreeBorrows.BorrowTree.performBorrowAccessRange

private theorem retagPointerValue_8byte_eq_expected
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    Miri.TreeBorrows.RetagPipeline.retagPointerValue
      retagInitialMachineState (retagRefRequest (Miri.ABI.Size.ofBytes 8) mode mutability frozen) =
    expectedRetagResultFull (Miri.ABI.Size.ofBytes 8) mode mutability frozen
      (retagPolOf mode mutability frozen)
      (retagStOf mode mutability frozen) := by
  cases mode <;> cases mutability <;> cases frozen <;> rfl

private def retagEvaluated8Byte
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    Miri.TreeBorrows.RetagPipeline.Result Unit :=
  let sz := Miri.ABI.Size.ofBytes 8
  let pol := retagPolOf mode mutability frozen
  let st := retagStOf mode mutability frozen
  let c := retagChildOf sz mode mutability frozen
  let g0 := retagInitialMachineState.global
  let g1 := { g0 with nextPointerTag := ⟨3, by decide⟩ }
  let (g2, f2) := match pol.protector with
    | some p => g1.addProtector {} retagTestAllocId retagChildTag p
    | none => (g1, {})
  let evs0 : Array Miri.TreeBorrows.RetagPipeline.Event :=
    #[.placeConverted, .reborrowSizeSelected sz, .pointerTagAllocated retagChildTag,
      .pointerAccessChecked, .allocationResolution (some retagTestAllocId),
      .creationLogCalled retagChildTag (some retagTestAllocId) false]
  let evs1 := match pol.protector with
    | some p => evs0.push (.protectorRegistered retagChildTag p)
    | none => evs0
  let evs2 := (evs1.push (.allocationKindChecked retagTestAllocId .liveData)).push
    (.allocationExtraLoaded retagTestAllocId)
  let evs3 := match st.permission.associatedAccess with
    | none => evs2
    | some kind => evs2.push (.parentTreeAccess kind ⟨0, 8⟩)
  let prov := some (Miri.Memory.Provenance.concrete retagTestAllocId retagChildTag)
  let evs4 := (((evs3.push (.childInserted retagChildTag)).push
    (.reborrowReturned prov)).push (.placeProvenanceReplaced prov)).push
    .retaggedValueReconstructed
  { state := { memory := liveTreeMemory c.tree, global := g2, frame := f2 }
    outcome := .ok prov
    events := evs4 }

private theorem g2_protectedTags_eq (prot : Option Miri.TreeBorrows.ProtectorKind) :
    (match prot with
      | some p => ({ retagInitialMachineState.global with nextPointerTag := ⟨3, by decide⟩ } :
          Miri.TreeBorrows.GlobalState).addProtector {} retagTestAllocId retagChildTag p
      | none => ({ retagInitialMachineState.global with nextPointerTag := ⟨3, by decide⟩ }, {})).1.protectedTags =
    match prot with
      | some p => ({} : Miri.TreeBorrows.ProtectedTags).insert retagChildTag p
      | none => {} := by
  cases prot <;> rfl

private theorem read_write_mut_not :
    (Miri.TreeBorrows.AccessKind.Read == .Write && Miri.Memory.Mutability.Mut == .Not) = false := rfl

private theorem uint64_8_sub_0 : (8 : UInt64) - (0 : UInt64) = 8 := rfl

private theorem size_add_zero_zero :
    Miri.ABI.Size.add Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 0) = .ok Miri.ABI.Size.ZERO := rfl

private theorem size_add_zero_8 :
    Miri.ABI.Size.add Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) = .ok (Miri.ABI.Size.ofBytes 8) := rfl

private theorem size_8_bytes_ne_zero :
    ((Miri.ABI.Size.ofBytes 8).bytes != 0) = true := rfl

private theorem expectedRetagResultFull_8byte_eq
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    expectedRetagResultFull (Miri.ABI.Size.ofBytes 8) mode mutability frozen
      (retagPolOf mode mutability frozen) (retagStOf mode mutability frozen) =
    retagEvaluated8Byte mode mutability frozen := by
  obtain ⟨hread_st, hread_tr⟩ := fresh_root_full_read (retagPolOf mode mutability frozen).protector
  have hch_ok := (borrowTree_newChild_8byte_core
    (retagStOf mode mutability frozen) (retagPolOf mode mutability frozen).outsidePermission
    (retagPolOf mode mutability frozen).protector.isSome
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)).1
  have hiter8 :
      (Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) (retagStOf mode mutability frozen)).iterAll =
        #[⟨⟨0, 8⟩, retagStOf mode mutability frozen⟩] := rfl
  have hdr : (retagRefRequest (Miri.ABI.Size.ofBytes 8) mode mutability frozen).hooks.dataRace = none := rfl
  have hassoc : (retagStOf mode mutability frozen).permission.associatedAccess = none ∨
      (retagStOf mode mutability frozen).permission.associatedAccess = some .Read := by
    cases mode <;> cases mutability <;> cases frozen <;> decide
  unfold expectedRetagResultFull expectedAccessTreeForReborrowFull expectedUpdateTreeExtra retagEvaluated8Byte
  dsimp only [retagChildOf]
  rw [hiter8]
  rcases hassoc with hnone | hsome
  · simp +zetaHave only [hnone, Id.run, bind, Bind.bind, pure, Pure.pure,
      ← Array.forIn_toList, List.forIn_cons, List.forIn_nil, not_tracked_retagChildTag,
      retagInitialMachineState_memory, liveTreeMemory_find,
      liveTreeAllocation_extra, liveTreeAllocation_setExtra, liveTreeMemory_setLiveAllocation,
      hch_ok]
  · simp +zetaHave only [hsome, hdr, g2_protectedTags_eq,
      read_write_mut_not, uint64_8_sub_0, size_add_zero_zero, size_add_zero_8, size_8_bytes_ne_zero,
      Id.run, bind, Bind.bind, pure, Pure.pure,
      ← Array.forIn_toList, List.forIn_cons, List.forIn_nil, not_tracked_retagChildTag,
      retagInitialMachineState_memory, liveTreeMemory_find,
      liveTreeAllocation_extra, liveTreeAllocation_setExtra, liveTreeMemory_setLiveAllocation,
      hread_st, hread_tr, hch_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rfl

end Retag8ByteOperational

/-- **`retagPointerValue_8byte_reference_simulation`** (certifying `I-10` & `I-11`
full-pipeline retag across all 16 reference/mode combinations):
executing Miri's operational `RetagPipeline.retagPointerValue` on an 8-byte live
allocation (`Size.ofBytes 8`) across all `4 × 2 × 2 = 16`
`(mode, mutability, frozen)` combinations:
1. allocates `retagChildTag` and returns `.ok (some (.concrete retagTestAllocId retagChildTag))`;
2. registers `retagChildTag` in both `GlobalState.protectedTags` and
   `FrameState.protectedTags` iff `mode = .fnEntry`, and `GlobalState.endCall`
   releases that protector on return;
3. emits `Event.parentTreeAccess .Read ⟨0, 8⟩` iff the mapped Anneal initial
   permission `annealRetagPerm mode mutability frozen` is not `.cell`
   (matching Anneal's `Places.lean` / `Statements.lean` initial child-read gate);
4. emits `Event.childInserted retagChildTag` and links `nthParent retagChildTag 1`
   to `retagParentTag` in `retagTestAllocId`'s live `BorrowTree`;
5. initializes `retagChildTag`'s `[0, 8)` `LocationState` to
   `(permission := annealPermToMiri perm, accessed := (annealPermToMiri perm != .Cell))`. -/
theorem retagPointerValue_8byte_reference_simulation
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    let res := Miri.TreeBorrows.RetagPipeline.retagPointerValue
      retagInitialMachineState (retagRefRequest (Miri.ABI.Size.ofBytes 8) mode mutability frozen)
    let perm := annealRetagPerm mode mutability frozen
    res.outcome = .ok (some (.concrete retagTestAllocId retagChildTag)) ∧
    res.state.global.protectedTags.contains retagChildTag = (mode == .fnEntry) ∧
    res.state.frame.protectedTags =
      (if mode == .fnEntry then #[(retagTestAllocId, retagChildTag)] else #[]) ∧
    (res.state.global.endCall res.state.frame).protectedTags.contains retagChildTag = false ∧
    (Miri.TreeBorrows.RetagPipeline.Event.parentTreeAccess .Read ⟨0, 8⟩ ∈ res.events.toList ↔
      perm ≠ .cell) ∧
    Miri.TreeBorrows.RetagPipeline.Event.childInserted retagChildTag ∈ res.events.toList ∧
    (res.state.memory.live.find? fun e => e.1 == retagTestAllocId).bind
        (fun e => (e.2.allocation.extra.nthParent retagChildTag 1).toOption) =
      some retagParentTag ∧
    (liveTagLocationState res.state.memory retagChildTag).map (fun s => (s.permission, s.accessed)) =
      some (annealPermToMiri perm, annealPermToMiri perm != .Cell) := by
  dsimp only []
  rw [retagPointerValue_8byte_eq_expected, expectedRetagResultFull_8byte_eq]
  obtain ⟨_, hch_par, hch_loc⟩ := borrowTree_newChild_8byte_core
    (retagStOf mode mutability frozen) (retagPolOf mode mutability frozen).outsidePermission
    (retagPolOf mode mutability frozen).protector.isSome
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
    (by cases mode <;> cases mutability <;> cases frozen <;> decide)
  dsimp only [retagEvaluated8Byte, retagChildOf]
  rw [liveTreeMemory_find, liveTagLocationState_liveTreeMemory, Option.bind, liveTreeAllocation_extra, hch_par, hch_loc]
  cases mode <;> cases mutability <;> cases frozen <;>
    refine ⟨rfl, by decide, by decide, by decide,
      ⟨fun h hc => by cases hc <;> (revert h; decide),
       fun h => by first | decide | exact False.elim (h rfl)⟩,
      by decide, rfl, by decide⟩

end RootReadOperational

/-- Tag in `hooksTwoNodeTree` corresponding to a `localAccess` (`retagChildTag`,
tag `2`) vs `foreignAccess` (`retagParentTag`, tag `1`) relative to
`retagChildTag`. -/
def hooksAccessTag : TreeBorrowRelatedness → Miri.Memory.BorTag
  | .localAccess => retagChildTag
  | .foreignAccess => retagParentTag

section HooksBorrowAccessRangeOperational

attribute [local irreducible] Miri.TreeBorrows.BorrowTree.performNormalAccessAt

private theorem hooksTwoNodeTree_roots (perm : TreeBorrowPerm) :
    (hooksTwoNodeTree perm).roots = #[⟨0⟩] := rfl

private theorem hooksTwoNodeTree_nodes_get_zero (perm : TreeBorrowPerm) :
    (hooksTwoNodeTree perm).nodes.get ⟨0⟩ =
      some ⟨retagParentTag, none, #[⟨1⟩], .Disabled, .None, false, none⟩ := by
  dsimp only [hooksTwoNodeTree]
  decide

private theorem hooksTwoNodeTree_indexOfTag
    (rel : TreeBorrowRelatedness) (perm : TreeBorrowPerm) :
    (hooksTwoNodeTree perm).indexOfTag (hooksAccessTag rel) =
      some (hooksAccessIndex rel) := by
  cases rel <;> rfl

private theorem hooksTwoNodeTree_performBorrowAccessRange_step
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let res := tree.performBorrowAccessRange (.concrete (hooksAccessTag rel))
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (annealAccessKindToMiri kind)
      (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
    let norm := tree.performNormalAccessAt (hooksLocTree perm)
      (hooksAccessIndex rel) (annealAccessKindToMiri kind)
      (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
    res.status = (if norm.access.status != .Completed then
      .AccessFailure ⟨0, 8⟩ norm.access.status else .Completed) ∧
    (norm.access.status = .Completed →
      res.tree = { tree with locations :=
        Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) norm.location }) := by
  let tree := hooksTwoNodeTree perm
  have hsource : tree.indexOfTag (hooksAccessTag rel) = some (hooksAccessIndex rel) :=
    hooksTwoNodeTree_indexOfTag rel perm
  have hloc : tree.locations =
      Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) (hooksLocTree perm) := rfl
  have hiter := Miri.DataStructures.DedupRangeMap.iterMut_new_full
    (Miri.ABI.Size.ofBytes 8) (hooksLocTree perm) (by decide)
  obtain ⟨hout, hroot, _, _⟩ :=
    borrowTree_performNormalAccessAt_simulation kind rel perm isProtected
  dsimp only [tree] at hsource hloc hout hroot ⊢
  let norm := (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
    (hooksAccessIndex rel) (annealAccessKindToMiri kind)
    (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
  have hnorm_eq : norm =
      ⟨norm.location, ⟨norm.access.tree, 0, norm.access.visited, norm.access.status⟩, .ok ()⟩ := by
    dsimp only [norm]
    rw [← hout, ← hroot]
  unfold Miri.TreeBorrows.BorrowTree.performBorrowAccessRange
  dsimp only [Id.run]
  rw [hsource, hloc, hiter]
  simp only [bind, Bind.bind, pure, Pure.pure]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size_singleton,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [List.range', List.forIn_cons, List.forIn_nil, bind, Bind.bind, pure, Pure.pure]
  simp only [Option.isNone_some, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Array.getElem?_singleton]
  rw [setAtPos_new_8]
  dsimp only []
  by_cases hc : norm.access.status = .Completed
  · have hnorm_ok : (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
        (hooksAccessIndex rel) (annealAccessKindToMiri kind)
        (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed =
        ⟨norm.location, ⟨norm.access.tree, 0, norm.access.visited, .Completed⟩, .ok ()⟩ := by
      rw [← hc]; exact hnorm_eq
    have hne : (norm.access.status != .Completed) = false := bne_eq_false_iff_eq.mpr hc
    dsimp only [norm] at hne
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, fun _ => ?_⟩
    · conv =>
        lhs
        arg 1
        arg 1
        arg 2
        arg 2
        arg 1
        whnf
        rw [hnorm_ok]
        simp +zetaHave only [uniIndex_ofNat_zero, hooksTwoNodeTree_roots, hooksTwoNodeTree_nodes_get_zero,
          visitChildren_beq_skip,
          Id.run, bind, Bind.bind, pure, Pure.pure,
          Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size_singleton,
          Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
          List.range', List.forIn_cons, List.forIn_nil,
          Option.isNone_none, Bool.not_false, Bool.true_and, Bool.false_and,
          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Array.getElem?_singleton]
    · conv =>
        lhs
        arg 3
        arg 1
        arg 2
        arg 2
        arg 1
        whnf
        rw [hnorm_ok]
        simp +zetaHave only [uniIndex_ofNat_zero, hooksTwoNodeTree_roots, hooksTwoNodeTree_nodes_get_zero,
          visitChildren_beq_skip,
          Id.run, bind, Bind.bind, pure, Pure.pure,
          Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size_singleton,
          Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
          List.range', List.forIn_cons, List.forIn_nil,
          Option.isNone_none, Bool.not_false, Bool.true_and, Bool.false_and,
          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Array.getElem?_singleton]
      dsimp only []
      conv =>
        lhs
        arg 3
        arg 2
        arg 1
        whnf
        rw [hnorm_ok]
        simp +zetaHave only [uniIndex_ofNat_zero, hooksTwoNodeTree_roots, hooksTwoNodeTree_nodes_get_zero,
          visitChildren_beq_skip,
          Id.run, bind, Bind.bind, pure, Pure.pure,
          Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size_singleton,
          Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
          List.range', List.forIn_cons, List.forIn_nil,
          Option.isNone_none, Bool.not_false, Bool.true_and, Bool.false_and,
          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Array.getElem?_singleton]
  · have hne_let : (norm.access.status != .Completed) = true := bne_iff_ne.mpr hc
    have hne : (norm.access.status != .Completed) = true := hne_let
    have hnorm_err : (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
        (hooksAccessIndex rel) (annealAccessKindToMiri kind)
        (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed =
        ⟨norm.location, ⟨norm.access.tree, 0, norm.access.visited, norm.access.status⟩, .ok ()⟩ :=
      hnorm_eq
    dsimp only [norm] at hne
    simp only [hne, ↓reduceIte]
    refine ⟨?_, fun hcomp => False.elim (hc hcomp)⟩
    conv =>
      lhs
      arg 1
      arg 1
      arg 2
      arg 2
      arg 1
      whnf
      rw [hnorm_err]
      simp +zetaHave only [hne_let, Id.run, bind, Bind.bind, pure, Pure.pure, ↓reduceIte]
    rfl

end HooksBorrowAccessRangeOperational

/-- **`borrowTree_performBorrowAccessRange_simulation`**: Miri's operational
`BorrowTree.performBorrowAccessRange` (`TreeState.lean`) across `[0, 8)` on
`hooksTwoNodeTree perm` for all `2 × 2 × 7 × 2 = 56`
`(kind, rel, perm, isProtected)` combinations:
1. completes (`res.status = .Completed`) iff Anneal's
   `treeBorrowNodeAccess kind rel perm isProtected` is non-UB;
2. whenever it completes, updates `res.tree` so that child node `⟨1⟩`
   (`retagChildTag`) at `[0, 8)` has the exact mapped Anneal successor
   permission `annealPermToMiri (applyTreeBorrowTransition dummy out).perm`. -/
theorem borrowTree_performBorrowAccessRange_simulation
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let res := tree.performBorrowAccessRange (.concrete (hooksAccessTag rel))
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (annealAccessKindToMiri kind)
      (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
    let out := treeBorrowNodeAccess kind rel perm isProtected
    let dummy : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := perm }
    (res.status = .Completed ↔ treeBorrowTransitionIsUB out = false) ∧
    (res.status = .Completed →
      (res.tree.locations.entries[0]?.bind (fun s => s.data.perms.get ⟨1⟩)).map (·.permission) =
        some (annealPermToMiri (applyTreeBorrowTransition dummy out).perm)) := by
  obtain ⟨hrange_st, hrange_tr⟩ :=
    hooksTwoNodeTree_performBorrowAccessRange_step kind rel perm isProtected
  obtain ⟨_, _, hst, hperm⟩ :=
    borrowTree_performNormalAccessAt_simulation kind rel perm isProtected
  dsimp only [] at hrange_st hrange_tr hst hperm ⊢
  rw [hrange_st]
  let norm := (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
    (hooksAccessIndex rel) (annealAccessKindToMiri kind)
    (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
  by_cases hc : norm.access.status = .Completed
  · have hne : (norm.access.status != .Completed) = false := bne_eq_false_iff_eq.mpr hc
    dsimp only [norm] at hne
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨fun _ => hst.mp hc, fun _ => trivial⟩, fun _ => ?_⟩
    rw [hrange_tr hc]
    dsimp only [Miri.DataStructures.DedupRangeMap.new, Miri.ABI.Size.ofBytes,
      bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Array.getElem?_singleton, Option.bind]
    exact hperm hc
  · have hne : (norm.access.status != .Completed) = true := bne_iff_ne.mpr hc
    dsimp only [norm] at hne
    simp only [hne, ↓reduceIte]
    exact ⟨⟨(fun h => nomatch h), (fun hub => False.elim (hc (hst.mpr hub)))⟩, fun h => nomatch h⟩

private theorem borrowTreeTagLocationState_hooksTwoNodeTree_with_locations
    (perm : TreeBorrowPerm) (loc : Miri.TreeBorrows.LocationTree) (p : Miri.TreeBorrows.Permission)
    (hp : (loc.perms.get ⟨1⟩).map (·.permission) = some p) :
    (borrowTreeTagLocationState
      { hooksTwoNodeTree perm with
        locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) loc }
      retagChildTag).map (·.permission) = some p := by
  cases hg : loc.perms.get ⟨1⟩ with
  | none => rw [hg] at hp; cases hp
  | some st =>
    rw [hg] at hp
    have hloc : borrowTreeTagLocationState
        { hooksTwoNodeTree perm with
          locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) loc }
        retagChildTag =
        some ((loc.perms.get ⟨1⟩).getD ⟨.Disabled, false, .None⟩) := rfl
    rw [hloc, hg]
    exact hp

private def expectedHooksReadResult
    (acc : Miri.TreeBorrows.BorrowTree.BorrowTreeAccessResult) :
    Miri.TreeBorrows.MachineMemoryHooks.AccessResult Unit Unit Unit :=
  let nextMem := liveTreeMemory acc.tree
  if acc.status != .Completed then
    { memory := nextMem
      context := ⟨(), .empty, false, #[]⟩
      outcome := .error s!"Tree Borrows read failed: {reprStr acc.status}" }
  else
    { memory := nextMem
      context := ⟨(), .empty, false, #[]⟩
      outcome := .ok () }

section HooksFullOperational

attribute [local irreducible] Miri.TreeBorrows.BorrowTree.performBorrowAccessRange

/-- **`machineMemoryHooks_fresh_root_read_simulation`**: Miri's operational
`MachineMemoryHooks.beforeMemoryRead` across the full 8-byte range `[0, 8)` on
a live allocation carrying `BorrowTree.new retagParentTag (Size.ofBytes 8)`
succeeds (`.ok ()`) and preserves `liveTreeMemory` for both protected and
unprotected child configurations. -/
theorem machineMemoryHooks_fresh_root_read_simulation
    (isProtected : Bool) :
    let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let mem := liveTreeMemory tree
    let alloc := liveTreeAllocation tree
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId retagParentTag)⟩
    let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
    let res := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead
      mem ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      alloc ptr retagTestAllocId (.concrete retagParentTag) range
    res.outcome = .ok () ∧ res.memory = mem := by
  let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
  have hfresh := fresh_root_full_read
    (if isProtected then some .StrongProtector else none)
  have hprot :
      (hooksForChildProtected isProtected).protectedTags =
        (match (if isProtected then some Miri.TreeBorrows.ProtectorKind.StrongProtector else none) with
        | some p => ({} : Miri.TreeBorrows.ProtectedTags).insert retagChildTag p
        | none => {}) := by
    cases isProtected <;> rfl
  let acc := tree.performBorrowAccessRange (.concrete retagParentTag)
    Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) .Read
    (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
  have hstep : Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead
      (liveTreeMemory tree) ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      (liveTreeAllocation tree) ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId retagParentTag)⟩
      retagTestAllocId (.concrete retagParentTag)
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) =
      expectedHooksReadResult acc := by
    cases isProtected <;> rfl
  dsimp only []
  rw [hstep]
  dsimp only [expectedHooksReadResult, acc]
  rw [hprot, hfresh.1, hfresh.2]
  exact ⟨rfl, rfl⟩

/-- **`machineMemoryHooks_beforeMemoryRead_simulation`** (certifying `I-10` &
`I-11` operational read hooks): Miri's `MachineMemoryHooks.beforeMemoryRead`
across `[0, 8)` on `hooksTwoNodeTree perm` for all `2 × 7 × 2 = 28`
`(rel, perm, isProtected)` combinations:
1. succeeds (`res.outcome = .ok ()`) iff Anneal's
   `treeBorrowNodeAccess .read rel perm isProtected` is non-UB;
2. whenever it succeeds, updates the live allocation's `BorrowTree` so that
   `retagChildTag` has the exact mapped Anneal successor permission. -/
theorem machineMemoryHooks_beforeMemoryRead_simulation
    (rel : TreeBorrowRelatedness) (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let mem := liveTreeMemory tree
    let alloc := liveTreeAllocation tree
    let tag := hooksAccessTag rel
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId tag)⟩
    let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
    let res := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead
      mem ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      alloc ptr retagTestAllocId (.concrete tag) range
    let out := treeBorrowNodeAccess .read rel perm isProtected
    let dummy : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := perm }
    (res.outcome = .ok () ↔ treeBorrowTransitionIsUB out = false) ∧
    (res.outcome = .ok () →
      (liveTagLocationState res.memory retagChildTag).map (·.permission) =
        some (annealPermToMiri (applyTreeBorrowTransition dummy out).perm)) := by
  let tree := hooksTwoNodeTree perm
  let tag := hooksAccessTag rel
  let acc := tree.performBorrowAccessRange (.concrete tag)
    Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) .Read
    (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
  have hstep : Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead
      (liveTreeMemory tree) ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      (liveTreeAllocation tree) ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId tag)⟩
      retagTestAllocId (.concrete tag)
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) =
      expectedHooksReadResult acc := by
    cases rel <;> (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases isProtected <;> rfl
  obtain ⟨hr_st, _⟩ :=
    borrowTree_performBorrowAccessRange_simulation .read rel perm isProtected
  obtain ⟨_, htr_eq⟩ :=
    hooksTwoNodeTree_performBorrowAccessRange_step .read rel perm isProtected
  obtain ⟨_, _, hnorm_st, hnorm_perm⟩ :=
    borrowTree_performNormalAccessAt_simulation .read rel perm isProtected
  dsimp only [annealAccessKindToMiri] at hr_st htr_eq hnorm_st hnorm_perm
  dsimp only []
  rw [hstep]
  dsimp only [expectedHooksReadResult]
  by_cases hc : acc.status = .Completed
  · have hne : (acc.status != .Completed) = false := bne_eq_false_iff_eq.mpr hc
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨fun _ => hr_st.mp hc, fun _ => trivial⟩, fun _ => ?_⟩
    rw [liveTagLocationState_liveTreeMemory]
    have hnorm_c : ((hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
        (hooksAccessIndex rel) .Read
        (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed).access.status =
        .Completed := hnorm_st.mpr (hr_st.mp hc)
    dsimp only [acc, tree, tag]
    rw [htr_eq hnorm_c]
    exact borrowTreeTagLocationState_hooksTwoNodeTree_with_locations perm _ _ (hnorm_perm hnorm_c)
  · have hne : (acc.status != .Completed) = true := bne_iff_ne.mpr hc
    simp only [hne, ↓reduceIte]
    exact ⟨⟨(fun h => nomatch h), (fun hub => False.elim (hc (hr_st.mpr hub)))⟩, fun h => nomatch h⟩

/-- **`machineMemoryHooks_beforeMemoryWrite_simulation`** (certifying `I-10` &
`I-11` operational write hooks): Miri's `MachineMemoryHooks.beforeMemoryWrite`
across `[0, 8)` on `hooksTwoNodeTree perm` for all `2 × 7 × 2 = 28`
`(rel, perm, isProtected)` combinations:
1. succeeds (`res.outcome = .ok ()`) iff Anneal's
   `treeBorrowNodeAccess .write rel perm isProtected` is non-UB;
2. whenever it succeeds, updates the live allocation's `BorrowTree` so that
   `retagChildTag` has the exact mapped Anneal successor permission. -/
theorem machineMemoryHooks_beforeMemoryWrite_simulation
    (rel : TreeBorrowRelatedness) (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let mem := liveTreeMemory tree
    let alloc := liveTreeAllocation tree
    let tag := hooksAccessTag rel
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId tag)⟩
    let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
    let res := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite
      mem ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      alloc ptr retagTestAllocId (.concrete tag) range
    let out := treeBorrowNodeAccess .write rel perm isProtected
    let dummy : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := perm }
    (res.outcome = .ok () ↔ treeBorrowTransitionIsUB out = false) ∧
    (res.outcome = .ok () →
      (liveTagLocationState res.memory retagChildTag).map (·.permission) =
        some (annealPermToMiri (applyTreeBorrowTransition dummy out).perm)) := by
  let tree := hooksTwoNodeTree perm
  let tag := hooksAccessTag rel
  let acc := tree.performBorrowAccessRange (.concrete tag)
    Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) .Write
    (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
  have hstep : Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite
      (liveTreeMemory tree) ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      (liveTreeAllocation tree) ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId tag)⟩
      retagTestAllocId (.concrete tag)
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) =
      expectedHooksWriteResult acc := by
    cases rel <;> (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases isProtected <;> rfl
  obtain ⟨hr_st, _⟩ :=
    borrowTree_performBorrowAccessRange_simulation .write rel perm isProtected
  obtain ⟨_, htr_eq⟩ :=
    hooksTwoNodeTree_performBorrowAccessRange_step .write rel perm isProtected
  obtain ⟨_, _, hnorm_st, hnorm_perm⟩ :=
    borrowTree_performNormalAccessAt_simulation .write rel perm isProtected
  dsimp only [annealAccessKindToMiri] at hr_st htr_eq hnorm_st hnorm_perm
  dsimp only []
  rw [hstep]
  dsimp only [expectedHooksWriteResult]
  by_cases hc : acc.status = .Completed
  · have hne : (acc.status != .Completed) = false := bne_eq_false_iff_eq.mpr hc
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨fun _ => hr_st.mp hc, fun _ => trivial⟩, fun _ => ?_⟩
    rw [liveTagLocationState_liveTreeMemory]
    have hnorm_c : ((hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
        (hooksAccessIndex rel) .Write
        (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed).access.status =
        .Completed := hnorm_st.mpr (hr_st.mp hc)
    dsimp only [acc, tree, tag]
    rw [htr_eq hnorm_c]
    exact borrowTreeTagLocationState_hooksTwoNodeTree_with_locations perm _ _ (hnorm_perm hnorm_c)
  · have hne : (acc.status != .Completed) = true := bne_iff_ne.mpr hc
    simp only [hne, ↓reduceIte]
    exact ⟨⟨(fun h => nomatch h), (fun hub => False.elim (hc (hr_st.mpr hub)))⟩, fun h => nomatch h⟩

end HooksFullOperational

section HooksDeallocOperational

private local instance : DecidableEq TreeBorrowPerm := fun a b =>
  if h : annealPermToMiri a = annealPermToMiri b then
    isTrue (annealPermToMiri_injective h)
  else
    isFalse (fun hab => h (congrArg annealPermToMiri hab))

private theorem hooksForChildProtected_get_parent (isProtected : Bool) :
    (hooksForChildProtected isProtected).protectedTags.get retagParentTag = none := by
  cases isProtected <;>
    simp [hooksForChildProtected, Miri.TreeBorrows.ProtectedTags.get,
      Miri.TreeBorrows.ProtectedTags.insert, retagParentTag, retagChildTag,
      Miri.Memory.BorTag.one]

private theorem hooksForChildProtected_get_child (isProtected : Bool) :
    (hooksForChildProtected isProtected).protectedTags.get retagChildTag =
      (if isProtected then some .StrongProtector else none) := by
  cases isProtected <;>
    simp [hooksForChildProtected, Miri.TreeBorrows.ProtectedTags.get,
      Miri.TreeBorrows.ProtectedTags.insert, retagChildTag]

private theorem hooksTwoNodeTree_topology (perm : TreeBorrowPerm) :
    (⟨(hooksTwoNodeTree perm).nodes.data.map fun entry =>
      match entry with
      | none => ⟨none, []⟩
      | some node =>
          ⟨node.parent.map Miri.TreeBorrows.UniIndex.toNat,
            node.children.toList.map Miri.TreeBorrows.UniIndex.toNat⟩⟩ :
      Miri.TreeBorrows.Tree.TraversalTree) =
    ⟨#[⟨none, [1]⟩, ⟨some 0, []⟩]⟩ := by
  simp [hooksTwoNodeTree, hooksTwoNodes, Miri.TreeBorrows.UniIndex.toNat]

private theorem hooksTwoNodeTree_traverse_zero :
    Miri.TreeBorrows.Tree.TraversalTree.traverse ⟨#[⟨none, [1]⟩, ⟨some 0, []⟩]⟩
      0 .VisitChildrenOfAccessed [] =
    (0, [⟨0, .LocalAccess⟩, ⟨1, .ForeignAccess⟩]) := rfl

private theorem hooksTwoNodeTree_traverse_one :
    Miri.TreeBorrows.Tree.TraversalTree.traverse ⟨#[⟨none, [1]⟩, ⟨some 0, []⟩]⟩
      1 .VisitChildrenOfAccessed [] =
    (0, [⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩]) := rfl

private def expectedDeallocAfterWrite
    (accTree : Miri.TreeBorrows.BorrowTree)
    (accStatus : Miri.TreeBorrows.BorrowTree.BorrowTreeAccessStatus)
    (tag : Miri.Memory.BorTag)
    (protectedTags : Miri.TreeBorrows.ProtectedTags) :
    Miri.TreeBorrows.BorrowTree.BorrowTreeDeallocResult := Id.run do
  if accStatus != .Completed then
    return { tree := accTree, status := .AccessFailure accStatus }
  let startIndex? := accTree.indexOfTag tag
  if startIndex?.isNone then
    return { tree := accTree, status := .MissingTag tag }
  let prepared := accTree.locations.iterMut Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
  let mut currentMap := prepared.state
  match prepared.outcome with
  | .error error =>
      let updatedTree := { accTree with locations := currentMap }
      return { tree := updatedTree, status := .RangeMapFailure error }
  | .ok () =>
      for cursor in [:prepared.positions.size] do
        match prepared.positions[cursor]?, prepared.segments[cursor]? with
        | some position, some segment =>
            let topology : Miri.TreeBorrows.Tree.TraversalTree :=
              ⟨accTree.nodes.data.map fun entry =>
                match entry with
                | none => ⟨none, []⟩
                | some node =>
                    ⟨node.parent.map Miri.TreeBorrows.UniIndex.toNat,
                      node.children.toList.map Miri.TreeBorrows.UniIndex.toNat⟩⟩
            let mut foundProtected : Option Miri.TreeBorrows.UniIndex := none
            let mut accessedRoot? : Option Miri.TreeBorrows.UniIndex := none
            if let some startIndex := startIndex? then
              let traversal := Miri.TreeBorrows.Tree.TraversalTree.traverse topology startIndex.toNat
                .VisitChildrenOfAccessed []
              accessedRoot? := Miri.TreeBorrows.UniIndex.ofNat? traversal.1
              for event in traversal.2 do
                if foundProtected.isNone then
                  match Miri.TreeBorrows.UniIndex.ofNat? event.node with
                  | none => pure ()
                  | some index =>
                      match accTree.nodeAt index with
                      | none => pure ()
                      | some node =>
                          let permission := segment.data.perms.get index
                            |>.getD node.defaultLocationState
                          if protectedTags.get node.tag == some .StrongProtector &&
                              !permission.permission.isCell && permission.accessed then
                            foundProtected := some index
            for root in accTree.roots.reverse do
              if accessedRoot? != some root && foundProtected.isNone then
                let events := (Miri.TreeBorrows.Tree.TraversalTree.traverse topology root.toNat
                  .VisitChildrenOfAccessed []).2
                for event in events do
                  if foundProtected.isNone then
                    match Miri.TreeBorrows.UniIndex.ofNat? event.node with
                    | none => pure ()
                    | some index =>
                        match accTree.nodeAt index with
                        | none => pure ()
                        | some node =>
                            let permission := segment.data.perms.get index
                              |>.getD node.defaultLocationState
                            if protectedTags.get node.tag == some .StrongProtector &&
                                !permission.permission.isCell && permission.accessed then
                              foundProtected := some index
            if let some index := foundProtected then
              let updatedTree := { accTree with locations := currentMap }
              return ⟨updatedTree, .ProtectedDealloc segment.range index⟩
            match currentMap.index position with
            | .error error =>
                let updatedTree := { accTree with locations := currentMap }
                return { tree := updatedTree, status := .RangeMapFailure error }
            | .ok _ => pure ()
        | _, _ =>
            let updatedTree := { accTree with locations := currentMap }
            return ⟨updatedTree,
              .RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size)⟩
  let updatedTree := { accTree with locations := currentMap }
  return { tree := updatedTree, status := .Deallocated }

section DeallocRangeStep

attribute [local irreducible] Miri.TreeBorrows.BorrowTree.performBorrowAccessRange

private theorem hooksTwoNodeTree_deallocateBorrowRange_eq_expected
    (rel : TreeBorrowRelatedness) (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let tag := hooksAccessTag rel
    let prots := (hooksForChildProtected isProtected).protectedTags
    tree.deallocateBorrowRange (.concrete tag) Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) prots =
      expectedDeallocAfterWrite
        (tree.performBorrowAccessRange (.concrete tag) Miri.ABI.Size.ZERO
          (Miri.ABI.Size.ofBytes 8) .Write prots .VisitChildrenOfAccessed).tree
        (tree.performBorrowAccessRange (.concrete tag) Miri.ABI.Size.ZERO
          (Miri.ABI.Size.ofBytes 8) .Write prots .VisitChildrenOfAccessed).status
        tag prots := by
  cases rel <;> (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases isProtected <;> rfl

end DeallocRangeStep

/-- **`borrowTree_deallocateBorrowRange_simulation`** (certifying `I-10` & `I-11`
deallocation protector semantics): Miri's operational
`BorrowTree.deallocateBorrowRange` (`TreeState.lean`) across `[0, 8)` on
`hooksTwoNodeTree perm` for all `2 × 7 × 2 = 28` `(rel, perm, isProtected)`
combinations:
1. when `treeBorrowNodeAccess .write rel perm isProtected` is UB, fails in its
   initial write stage (`∃ err, res.status = .AccessFailure err`);
2. when the initial write is non-UB and `retagChildTag` carries an active strong
   protector with `perm ≠ .cell` (for example, deallocating through a protected
   `&mut T` child in `Unique` or `ReservedFrz false`), fails in the tree-wide
   strong-protector scan with `res.status = .ProtectedDealloc ⟨0, 8⟩ ⟨1⟩`;
3. succeeds (`res.status = .Deallocated`) iff the initial write is non-UB and
   either `isProtected = false` (e.g. after `GlobalState.endCall` releases the
   protector) or `perm = .cell` (`&UnsafeCell<T>` is exempt from
   `ProtectedDealloc`, certifying `I-11`). -/
theorem borrowTree_deallocateBorrowRange_simulation
    (rel : TreeBorrowRelatedness) (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let res := tree.deallocateBorrowRange (.concrete (hooksAccessTag rel))
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
      (hooksForChildProtected isProtected).protectedTags
    let out := treeBorrowNodeAccess .write rel perm isProtected
    (treeBorrowTransitionIsUB out = true → ∃ err, res.status = .AccessFailure err) ∧
    (treeBorrowTransitionIsUB out = false → isProtected = true → perm ≠ .cell →
      res.status = .ProtectedDealloc ⟨0, 8⟩ ⟨1⟩) ∧
    (res.status = .Deallocated ↔
      (treeBorrowTransitionIsUB out = false ∧ (isProtected = false ∨ perm = .cell))) := by
  dsimp only []
  rw [hooksTwoNodeTree_deallocateBorrowRange_eq_expected rel perm isProtected]
  obtain ⟨hr_st, htr_eq⟩ :=
    hooksTwoNodeTree_performBorrowAccessRange_step .write rel perm isProtected
  obtain ⟨_, _, hnorm_st, _⟩ :=
    borrowTree_performNormalAccessAt_simulation .write rel perm isProtected
  let tree := hooksTwoNodeTree perm
  let tag := hooksAccessTag rel
  let prots := (hooksForChildProtected isProtected).protectedTags
  let norm := tree.performNormalAccessAt (hooksLocTree perm)
    (hooksAccessIndex rel) (annealAccessKindToMiri .write) prots .VisitChildrenOfAccessed
  let acc := tree.performBorrowAccessRange (.concrete tag)
    Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (annealAccessKindToMiri .write)
    prots .VisitChildrenOfAccessed
  change (treeBorrowTransitionIsUB _ = true →
      ∃ err, (expectedDeallocAfterWrite acc.tree acc.status tag prots).status = .AccessFailure err) ∧
    (treeBorrowTransitionIsUB _ = false → isProtected = true → perm ≠ .cell →
      (expectedDeallocAfterWrite acc.tree acc.status tag prots).status = .ProtectedDealloc ⟨0, 8⟩ ⟨1⟩) ∧
    ((expectedDeallocAfterWrite acc.tree acc.status tag prots).status = .Deallocated ↔ _)
  by_cases hc : norm.access.status = .Completed
  · have hne : (norm.access.status != .Completed) = false := bne_eq_false_iff_eq.mpr hc
    have hacc_st : acc.status = .Completed := by
      dsimp only [acc, tree, tag, prots]
      rw [hr_st]
      dsimp only [norm] at hne
      rw [hne]
      rfl
    have hacc_tr : acc.tree =
        { tree with
          locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8)
            (hooksExpectedPerformAt perm hooksTwoNodes.entries rel .write isProtected).location } := by
      dsimp only [acc, tree, tag, prots]
      rw [htr_eq hc, performNormalAccessAt_eq_expected .write rel perm isProtected]
    have hub_false : treeBorrowTransitionIsUB (treeBorrowNodeAccess .write rel perm isProtected) =
        false := hnorm_st.mp hc
    rw [hacc_tr, hacc_st, hub_false]
    refine And.intro (fun h => nomatch h) ?_
    rw [hooksTwoNodes_entries]
    unfold hooksExpectedPerformAt
    rw [hooksExpectedNormalProj_eq]
    dsimp only [tree, tag, prots]
    unfold expectedDeallocAfterWrite
    dsimp only []
    have hidx : ∀ locs,
        ({ hooksTwoNodeTree perm with locations := locs }).indexOfTag (hooksAccessTag rel) =
        some (hooksAccessIndex rel) := fun _ => hooksTwoNodeTree_indexOfTag rel perm
    have hroots : ∀ locs,
        ({ hooksTwoNodeTree perm with locations := locs }).roots.reverse = #[⟨0⟩] :=
      fun _ => rfl
    rw [hidx, hroots, hooksTwoNodeTree_topology perm]
    rw [Miri.DataStructures.DedupRangeMap.iterMut_new_full (Miri.ABI.Size.ofBytes 8) _ (by decide)]
    clear hc hne hacc_st hacc_tr hub_false hr_st htr_eq hnorm_st norm acc tree tag prots hidx hroots
    cases rel <;> (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases isProtected <;>
    · dsimp only [hooksAccessIndex, Miri.TreeBorrows.UniIndex.toNat]
      try rw [hooksTwoNodeTree_traverse_zero]
      try rw [hooksTwoNodeTree_traverse_one]
      simp +zetaHave only [Id.run, bind, Bind.bind, pure, Pure.pure,
        ← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      dsimp only [Miri.TreeBorrows.UniIndex.ofNat?,
        Miri.TreeBorrows.BorrowTree.nodeAt, Miri.TreeBorrows.UniValMap.get,
        hooksTwoNodeTree, hooksTwoNodes]
      try rw [hooksForChildProtected_get_child]
      try rw [hooksForChildProtected_get_parent]
      decide
  · have hne : (norm.access.status != .Completed) = true := bne_iff_ne.mpr hc
    have hacc_st : acc.status = .AccessFailure ⟨0, 8⟩ norm.access.status := by
      dsimp only [acc, tree, tag, prots]
      rw [hr_st]
      dsimp only [norm] at hne
      rw [hne]
      rfl
    have hub_true : treeBorrowTransitionIsUB (treeBorrowNodeAccess .write rel perm isProtected) =
        true := by
      cases hub : treeBorrowTransitionIsUB (treeBorrowNodeAccess .write rel perm isProtected)
      · exact False.elim (hc (hnorm_st.mpr hub))
      · rfl
    rw [hacc_st]
    have hexp : (expectedDeallocAfterWrite acc.tree (.AccessFailure ⟨0, 8⟩ norm.access.status)
        tag prots).status = .AccessFailure (.AccessFailure ⟨0, 8⟩ norm.access.status) := rfl
    rw [hexp, hub_true]
    exact And.intro (fun _ => ⟨_, rfl⟩)
      (And.intro (fun h => nomatch h) ⟨(fun h => nomatch h), (fun ⟨h, _⟩ => nomatch h)⟩)

section DeallocHooksStep

attribute [local irreducible] Miri.TreeBorrows.BorrowTree.deallocateBorrowRange

/-- **`machineMemoryHooks_beforeMemoryDeallocation_simulation`** (certifying
`I-10` & `I-11` operational deallocation hooks): Miri's
`MachineMemoryHooks.beforeMemoryDeallocation` on `hooksTwoNodeTree perm` across
all `2 × 7 × 2 = 28` `(rel, perm, isProtected)` combinations succeeds
(`res.outcome = .ok ()`) iff Anneal's `treeBorrowNodeAccess .write rel perm isProtected`
is non-UB and either `isProtected = false` or `perm = .cell` (`&UnsafeCell<T>`
strong-protector deallocation exemption). -/
theorem machineMemoryHooks_beforeMemoryDeallocation_simulation
    (rel : TreeBorrowRelatedness) (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let alloc := liveTreeAllocation tree
    let tag := hooksAccessTag rel
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId tag)⟩
    let res := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryDeallocation
      ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      alloc ptr retagTestAllocId (.concrete tag)
      (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.ONE .stack
    let out := treeBorrowNodeAccess .write rel perm isProtected
    res.outcome = .ok () ↔
      (treeBorrowTransitionIsUB out = false ∧ (isProtected = false ∨ perm = .cell)) := by
  obtain ⟨_, _, hdealloc_iff⟩ :=
    borrowTree_deallocateBorrowRange_simulation rel perm isProtected
  dsimp only [hooksForChildProtected] at hdealloc_iff
  dsimp only []
  have hcontains : (#[] : Array Miri.Memory.AllocId).contains retagTestAllocId = false := by
    simp
  have hsync : (Miri.TreeBorrows.MachineMemoryHooks.SyncObjectStore.empty :
      Miri.TreeBorrows.MachineMemoryHooks.SyncObjectStore Unit).get retagTestAllocId = .empty := rfl
  let tree := hooksTwoNodeTree perm
  let tag := hooksAccessTag rel
  let prots : Miri.TreeBorrows.ProtectedTags :=
    if isProtected then ({} : Miri.TreeBorrows.ProtectedTags).insert retagChildTag .StrongProtector
    else {}
  let dealloc := tree.deallocateBorrowRange (.concrete tag)
    Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) prots
  have halloc_extra : (liveTreeAllocation tree).extra = tree := rfl
  have hout :
      (Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryDeallocation
        ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
        (liveTreeAllocation tree)
        ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId tag)⟩
        retagTestAllocId (.concrete tag)
        (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.ONE .stack).outcome =
      (if dealloc.status != .Deallocated then
        Except.error s!"Tree Borrows deallocation failed: {reprStr dealloc.status}"
      else
        Except.ok ()) := by
    unfold Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryDeallocation
    rw [halloc_extra]
    dsimp only [Id.run, hooksForChildProtected]
    simp only [hcontains, Bool.false_eq_true, ↓reduceIte, bind, Bind.bind, pure, Pure.pure]
    by_cases hd : dealloc.status = .Deallocated
    · have hne : (dealloc.status != .Deallocated) = false := bne_eq_false_iff_eq.mpr hd
      dsimp only [dealloc, tree, tag, prots] at hne
      rw [hne]
      simp only [Bool.false_eq_true, ↓reduceIte, hsync,
        Miri.TreeBorrows.MachineMemoryHooks.SyncObjectMap.empty,
        ← Array.forIn_toList, List.forIn_nil, pure, Pure.pure]
    · have hne : (dealloc.status != .Deallocated) = true := bne_iff_ne.mpr hd
      dsimp only [dealloc, tree, tag, prots] at hne ⊢
      rw [hne]
      simp only [↓reduceIte]
  rw [hout]
  by_cases hd : dealloc.status = .Deallocated
  · have hne : (dealloc.status != .Deallocated) = false := bne_eq_false_iff_eq.mpr hd
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun _ => hdealloc_iff.mp hd, fun _ => trivial⟩
  · have hne : (dealloc.status != .Deallocated) = true := bne_iff_ne.mpr hd
    rw [hne]
    simp only [↓reduceIte]
    exact ⟨(fun h => nomatch h), (fun hok => False.elim (hd (hdealloc_iff.mpr hok)))⟩

end DeallocHooksStep

end HooksDeallocOperational

/-- Transparent copy of the vendored (private) `ancestorPathAux`: the start node
followed by its successive parents, for at most `fuel` parent steps. -/
def traversalAncestorPathAux (tree : Miri.TreeBorrows.Tree.TraversalTree) :
    Nat → Nat → List Nat
  | 0, current => [current]
  | fuel + 1, current =>
    match (tree.nodes[current]?.getD ⟨none, []⟩).parent with
    | none => [current]
    | some parent => current :: traversalAncestorPathAux tree fuel parent

/-- The vendored `TraversalTree.ancestorPath` is `traversalAncestorPathAux` with
fuel `tree.nodes.size`. -/
theorem ancestorPath_eq_traversalAncestorPathAux
    (tree : Miri.TreeBorrows.Tree.TraversalTree) (start : Nat) :
    tree.ancestorPath start = traversalAncestorPathAux tree tree.nodes.size start := by
  unfold Miri.TreeBorrows.Tree.TraversalTree.ancestorPath
  generalize tree.nodes.size = n
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    show (match (tree.nodes[start]?.getD ⟨none, []⟩).parent with
      | none => [start]
      | some p => start :: (_ : List Nat)) = _
    simp only [traversalAncestorPathAux]
    cases (tree.nodes[start]?.getD ⟨none, []⟩).parent with
    | none => rfl
    | some p => exact congrArg (List.cons start) (ih p)


/-- Transparent copy of the vendored (private) `foreignPostorder`: bottom-up
foreign events of the subtree rooted at `index`, pruning skipped nodes. -/
def traversalForeignPostorder (tree : Miri.TreeBorrows.Tree.TraversalTree)
    (skipNodes : List Nat) : Nat → Nat → List Miri.TreeBorrows.Tree.TraversalEvent
  | 0, _ => []
  | fuel + 1, index =>
    if skipNodes.contains index then []
    else
      ((tree.nodes[index]?.getD ⟨none, []⟩).children.reverse).flatMap
          (traversalForeignPostorder tree skipNodes fuel) ++
        [⟨index, .ForeignAccess⟩]

/-- Every event of `traversalForeignPostorder` is a foreign access. -/
theorem traversalForeignPostorder_foreign (tree : Miri.TreeBorrows.Tree.TraversalTree)
    (skipNodes : List Nat) :
    ∀ (fuel index : Nat) (event : Miri.TreeBorrows.Tree.TraversalEvent),
      event ∈ traversalForeignPostorder tree skipNodes fuel index →
      event.relatedness = .ForeignAccess := by
  intro fuel
  induction fuel with
  | zero => intro index event h; simp [traversalForeignPostorder] at h
  | succ n ih =>
    intro index event h
    simp only [traversalForeignPostorder] at h
    split at h
    · simp at h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨child, _, hc⟩ := List.mem_flatMap.mp h
        exact ih child event hc
      · simp at h; subst h; rfl

/-- **Traversal schedule shape**: the vendored normal-tree visitor
(`TraversalTree.traverse`) emits exactly the ancestor path of the accessed node
as `LocalAccess` events, followed by foreign-subtree events that are all
`ForeignAccess`. -/
theorem traverse_local_then_foreign (tree : Miri.TreeBorrows.Tree.TraversalTree)
    (start : Nat) (mode : Miri.TreeBorrows.Tree.ChildrenVisitMode) (skipNodes : List Nat) :
    ∃ foreignEvents,
      (tree.traverse start mode skipNodes).2 =
        (tree.ancestorPath start).map (fun index => ⟨index, .LocalAccess⟩) ++ foreignEvents ∧
      ∀ event ∈ foreignEvents, event.relatedness = .ForeignAccess := by
  unfold Miri.TreeBorrows.Tree.TraversalTree.traverse
  refine ⟨_, rfl, ?_⟩
  intro event hevent
  obtain ⟨root, -, hroot⟩ := List.mem_flatMap.mp hevent
  clear hevent
  generalize tree.nodes.size = n at hroot
  induction n generalizing root with
  | zero => exact absurd hroot (List.not_mem_nil (a := event))
  | succ n ih =>
    have h' : event ∈ (if skipNodes.contains root then []
        else ((tree.nodes[root]?.getD ⟨none, []⟩).children.reverse).flatMap
            (_ : Nat → List Miri.TreeBorrows.Tree.TraversalEvent) ++
          [⟨root, .ForeignAccess⟩]) := hroot
    split at h'
    · simp at h'
    · rcases List.mem_append.mp h' with h'' | h''
      · obtain ⟨child, _, hc⟩ := List.mem_flatMap.mp h''
        exact ih child hc
      · simp at h''; subst h''; rfl


/-! ## 7. `I-10`: Anneal's `parentTag` hierarchy as Miri's traversal tree -/

/-- `Trusted.Sequence.length` is `List.length`. -/
theorem sequence_length_eq {α : Type} (xs : List α) : length xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ _ => simp [length]

/-- Index of the first entry of `borrows` with provenance tag `tag`. -/
def borrowIndexOfTag : List BorrowEntry → Nat → Option Nat
  | .nil, _ => none
  | entry :: rest, tag =>
    match Nat.beq entry.tag tag with
    | true => some 0
    | false => (borrowIndexOfTag rest tag).map Nat.succ

/-- Miri traversal node of `entry` in `borrows`: its parent is the index of the
entry holding `entry.parentTag` (Anneal's `I-10` reborrow link), and its
children are the entries whose parent tag is `entry.tag`. -/
def annealTraversalNode (borrows : List BorrowEntry) (entry : BorrowEntry) :
    Miri.TreeBorrows.Tree.TraversalNode :=
  { parent := entry.parentTag.bind (borrowIndexOfTag borrows)
    children := (List.range borrows.length).filter (fun j =>
      match borrows[j]? with
      | some child => child.parentTag == some entry.tag
      | none => false) }

/-- The Miri traversal tree whose node `i` is Anneal borrow entry `borrows[i]`. -/
def annealTraversalTree (borrows : List BorrowEntry) :
    Miri.TreeBorrows.Tree.TraversalTree :=
  ⟨(borrows.map (annealTraversalNode borrows)).toArray⟩

/-- Distinct provenance tags, which Anneal maintains by allocating every tag
from `Memory.nextTag`. -/
def BorrowTagsUnique (borrows : List BorrowEntry) : Prop :=
  ∀ (i j : Nat) (hi : i < borrows.length) (hj : j < borrows.length),
    borrows[i].tag = borrows[j].tag → i = j

theorem annealTraversalTree_size (borrows : List BorrowEntry) :
    (annealTraversalTree borrows).nodes.size = borrows.length := by
  simp [annealTraversalTree]

theorem annealTraversalTree_node (borrows : List BorrowEntry) (s : Nat)
    (hs : s < borrows.length) :
    (annealTraversalTree borrows).nodes[s]?.getD ⟨none, []⟩ =
      annealTraversalNode borrows borrows[s] := by
  simp [annealTraversalTree, hs]

theorem BorrowTagsUnique.tail {entry : BorrowEntry} {rest : List BorrowEntry}
    (h : BorrowTagsUnique (entry :: rest)) : BorrowTagsUnique rest := by
  intro i j hi hj htag
  have := h (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by simpa using htag)
  omega

theorem BorrowTagsUnique.head_ne {entry : BorrowEntry} {rest : List BorrowEntry}
    (h : BorrowTagsUnique (entry :: rest)) (j : Nat) (hj : j < rest.length) :
    entry.tag ≠ rest[j].tag := by
  intro htag
  have := h 0 (j + 1) (by simp) (by simp; omega) (by simpa using htag)
  omega

theorem lookupBorrow_getElem (borrows : List BorrowEntry) (huniq : BorrowTagsUnique borrows)
    (j : Nat) (hj : j < borrows.length) :
    lookupBorrow borrows borrows[j].tag = some borrows[j] := by
  induction borrows generalizing j with
  | nil => simp at hj
  | cons entry rest ih =>
    cases j with
    | zero => simp [lookupBorrow]
    | succ k =>
      have hk : k < rest.length := by simp at hj; omega
      have hne := huniq.head_ne k hk
      have hbeq : Nat.beq entry.tag rest[k].tag = false := by
        cases hb : Nat.beq entry.tag rest[k].tag
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) hne
      simp only [List.getElem_cons_succ, lookupBorrow, hbeq]
      exact ih huniq.tail k hk

theorem borrowIndexOfTag_getElem (borrows : List BorrowEntry)
    (huniq : BorrowTagsUnique borrows) (j : Nat) (hj : j < borrows.length) :
    borrowIndexOfTag borrows borrows[j].tag = some j := by
  induction borrows generalizing j with
  | nil => simp at hj
  | cons entry rest ih =>
    cases j with
    | zero => simp [borrowIndexOfTag]
    | succ k =>
      have hk : k < rest.length := by simp at hj; omega
      have hne := huniq.head_ne k hk
      have hbeq : Nat.beq entry.tag rest[k].tag = false := by
        cases hb : Nat.beq entry.tag rest[k].tag
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) hne
      simp only [List.getElem_cons_succ, borrowIndexOfTag, hbeq, ih huniq.tail k hk]
      rfl

theorem borrowIndexOfTag_some (borrows : List BorrowEntry) (tag p : Nat)
    (h : borrowIndexOfTag borrows tag = some p) :
    ∃ hp : p < borrows.length, borrows[p].tag = tag := by
  induction borrows generalizing p with
  | nil => simp [borrowIndexOfTag] at h
  | cons entry rest ih =>
    simp only [borrowIndexOfTag] at h
    cases hb : Nat.beq entry.tag tag with
    | true =>
      rw [hb] at h
      cases h
      exact ⟨by simp, Nat.eq_of_beq_eq_true hb⟩
    | false =>
      rw [hb] at h
      cases hr : borrowIndexOfTag rest tag with
      | none => rw [hr] at h; cases h
      | some q =>
        rw [hr] at h
        cases h
        obtain ⟨hq, hqt⟩ := ih q hr
        exact ⟨by simp; omega, by simpa using hqt⟩

theorem borrowIndexOfTag_none (borrows : List BorrowEntry) (tag : Nat)
    (h : borrowIndexOfTag borrows tag = none) :
    lookupBorrow borrows tag = none ∧
      ∀ (j : Nat) (hj : j < borrows.length), borrows[j].tag ≠ tag := by
  induction borrows with
  | nil => exact ⟨rfl, fun j hj => absurd hj (by simp)⟩
  | cons entry rest ih =>
    simp only [borrowIndexOfTag] at h
    cases hb : Nat.beq entry.tag tag with
    | true => rw [hb] at h; cases h
    | false =>
      rw [hb] at h
      cases hr : borrowIndexOfTag rest tag with
      | some q => rw [hr] at h; cases h
      | none =>
        obtain ⟨hl, hne⟩ := ih hr
        refine ⟨by simp [lookupBorrow, hb, hl], ?_⟩
        intro j hj
        cases j with
        | zero =>
          intro heq
          simp at heq
          rw [heq] at hb
          simp at hb
        | succ k => simpa using hne k (by simp at hj; omega)

/-- A walk starting at a tag that no entry carries never reaches an entry's
tag. -/
theorem isBorrowDescendantOrSelfAux_absent (borrows : List BorrowEntry) (tag : Nat)
    (hlookup : lookupBorrow borrows tag = none)
    (hne : ∀ (j : Nat) (hj : j < borrows.length), borrows[j].tag ≠ tag)
    (n i : Nat) (hi : i < borrows.length) :
    isBorrowDescendantOrSelfAux n borrows tag borrows[i].tag = false := by
  have hbeq : Nat.beq tag borrows[i].tag = false := by
    cases hb : Nat.beq tag borrows[i].tag
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb).symm (hne i hi)
  cases n with
  | zero => simp [isBorrowDescendantOrSelfAux, hbeq]
  | succ n => simp [isBorrowDescendantOrSelfAux, hbeq, hlookup]

/-- Fuel-indexed core of `normalTree_local_classification`: with the same fuel,
Miri's ancestor path from node `s` contains node `i` exactly when Anneal's
`parentTag` walk from `borrows[s].tag` reaches `borrows[i].tag`. -/
theorem traversalAncestorPathAux_iff (borrows : List BorrowEntry)
    (huniq : BorrowTagsUnique borrows) (i : Nat) (hi : i < borrows.length) :
    ∀ (n s : Nat) (hs : s < borrows.length),
      i ∈ traversalAncestorPathAux (annealTraversalTree borrows) n s ↔
        isBorrowDescendantOrSelfAux n borrows borrows[s].tag borrows[i].tag = true := by
  intro n
  induction n with
  | zero =>
    intro s hs
    simp only [traversalAncestorPathAux, isBorrowDescendantOrSelfAux, List.mem_singleton]
    constructor
    · intro h; subst h; simp
    · intro h; exact (huniq s i hs hi (Nat.eq_of_beq_eq_true h)).symm
  | succ n ih =>
    intro s hs
    by_cases hsi : i = s
    · subst hsi
      simp [traversalAncestorPathAux, isBorrowDescendantOrSelfAux]
      split <;> simp
    · have hbeq : Nat.beq borrows[s].tag borrows[i].tag = false := by
        cases hb : Nat.beq borrows[s].tag borrows[i].tag
        · rfl
        · exact absurd (huniq s i hs hi (Nat.eq_of_beq_eq_true hb)).symm hsi
      simp only [traversalAncestorPathAux, isBorrowDescendantOrSelfAux, hbeq,
        annealTraversalTree_node borrows s hs, lookupBorrow_getElem borrows huniq s hs,
        annealTraversalNode]
      cases hpt : borrows[s].parentTag with
      | none => simp [hsi]
      | some pt =>
        cases hidx : borrowIndexOfTag borrows pt with
        | none =>
          obtain ⟨hl, hne⟩ := borrowIndexOfTag_none borrows pt hidx
          simp [hidx, hsi, isBorrowDescendantOrSelfAux_absent borrows pt hl hne n i hi]
        | some p =>
          obtain ⟨hp, hptag⟩ := borrowIndexOfTag_some borrows pt p hidx
          have := ih p hp
          rw [hptag] at this
          simp [hidx, hsi, this]

/-- **`normalTree_relative_access_simulation`** (certifying `I-10`): for an
Anneal borrow table with distinct tags, viewed as Miri's traversal tree
(`annealTraversalTree`, node `i` is `borrows[i]`, parents given by the `I-10`
`parentTag` links), and an access through entry `s`:
1. Miri's visitor (`TraversalTree.traverse`) emits `LocalAccess` events exactly
   for the nodes on the ancestor path of `s`, and every other event is a
   `ForeignAccess`;
2. node `i` is on that ancestor path exactly when Anneal classifies the access
   as a child access for `borrows[i]` (`isBorrowDescendantOrSelf borrows
   borrows[s].tag borrows[i].tag`), so Anneal's local/foreign classification is
   Miri's;
3. for every entry, Anneal's per-entry access with that classification is
   Miri's per-location access on the related node (permissions related by
   `annealPermToMiri`, protected-disable undefined behavior included), except
   for a foreign access to a `.disabled` entry, which both skip. -/
theorem normalTree_relative_access_simulation (borrows : List BorrowEntry)
    (huniq : BorrowTagsUnique borrows) (s : Nat) (hs : s < borrows.length)
    (mode : Miri.TreeBorrows.Tree.ChildrenVisitMode) (skipNodes : List Nat) :
    (∃ foreignEvents,
      ((annealTraversalTree borrows).traverse s mode skipNodes).2 =
        ((annealTraversalTree borrows).ancestorPath s).map
            (fun index => ⟨index, .LocalAccess⟩) ++ foreignEvents ∧
      ∀ event ∈ foreignEvents, event.relatedness = .ForeignAccess) ∧
    (∀ (i : Nat) (hi : i < borrows.length),
      i ∈ (annealTraversalTree borrows).ancestorPath s ↔
        isBorrowDescendantOrSelf borrows borrows[s].tag borrows[i].tag = true) ∧
    (∀ (i : Nat) (hi : i < borrows.length) (kind : TreeBorrowAccessKind)
        (isProtected : Bool) (sifa : Miri.TreeBorrows.IdempotentForeignAccess),
      let rel : TreeBorrowRelatedness :=
        if isBorrowDescendantOrSelf borrows borrows[s].tag borrows[i].tag = true
        then .localAccess else .foreignAccess
      (rel = .foreignAccess → borrows[i].perm ≠ .disabled) →
      match treeBorrowNodeAccess kind rel borrows[i].perm isProtected with
      | .transition next =>
        ∃ transition,
          Miri.TreeBorrows.Tree.LocationState.performAccess
              ⟨annealPermToMiri borrows[i].perm, true, sifa⟩
              (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
            .Success ⟨annealPermToMiri next, true, sifa⟩ transition
      | .ub =>
        ∃ state error,
          Miri.TreeBorrows.Tree.LocationState.performAccess
              ⟨annealPermToMiri borrows[i].perm, true, sifa⟩
              (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
            .Error state error
      | .protectedReservedIM =>
        Miri.TreeBorrows.Tree.LocationState.performAccess
            ⟨annealPermToMiri borrows[i].perm, true, sifa⟩
            (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
          .PermissionInvariantFailure ⟨annealPermToMiri borrows[i].perm, true, sifa⟩) := by
  refine ⟨traverse_local_then_foreign _ s mode skipNodes, ?_, ?_⟩
  · intro i hi
    rw [ancestorPath_eq_traversalAncestorPathAux, annealTraversalTree_size]
    unfold isBorrowDescendantOrSelf
    rw [sequence_length_eq]
    exact traversalAncestorPathAux_iff borrows huniq i hi borrows.length s hs
  · intro i hi kind isProtected sifa rel hskip
    exact nodeAccess_locationState_simulation kind rel borrows[i].perm isProtected sifa hskip


/-! ## 8. `TreeBorrowsRel`: Anneal borrow tables and Miri one-location trees -/

/-- Parent index of `entry` in the based traversal tree: the index of its parent
entry, or the base node `borrows.length` (the borrowed local's own tag, the root
of Miri's allocation tree) for a root borrow or a dangling parent tag. -/
def basedParentIndex (borrows : List BorrowEntry) (entry : BorrowEntry) : Nat :=
  match entry.parentTag with
  | none => borrows.length
  | some pt => (borrowIndexOfTag borrows pt).getD borrows.length

/-- Children of node `idx` in the based traversal tree. -/
def basedChildren (borrows : List BorrowEntry) (idx : Nat) : List Nat :=
  (List.range borrows.length).filter (fun j =>
    match borrows[j]? with
    | some child => Nat.beq (basedParentIndex borrows child) idx
    | none => false)

/-- Miri traversal tree of `borrows` with an explicit base node `borrows.length`
standing for the borrowed local's own tag, through which Anneal's direct local
accesses (`writerTag = .none`) go: node `i < borrows.length` is `borrows[i]`. -/
def basedTraversalTree (borrows : List BorrowEntry) :
    Miri.TreeBorrows.Tree.TraversalTree :=
  ⟨(borrows.mapIdx (fun (i : Nat) (e : BorrowEntry) =>
      Miri.TreeBorrows.Tree.TraversalNode.mk
        (some (basedParentIndex borrows e)) (basedChildren borrows i)) ++
    [Miri.TreeBorrows.Tree.TraversalNode.mk none (basedChildren borrows borrows.length)]).toArray⟩

/-- Indices of the protected entries of `borrows` under `activeProtectors`. -/
def protectedIndices (borrows : List BorrowEntry) (activeProtectors : List Nat) :
    List Nat :=
  (List.range borrows.length).filter (fun i =>
    match borrows[i]? with
    | some e => isBorrowProtected activeProtectors e
    | none => false)

/-- Miri's one-location normal tree for an Anneal borrow table: node `i` holds
`annealPermToMiri borrows[i].perm` as an accessed location (with no idempotent
foreign access recorded, so the visitor never skips a node through its SIFA
cache), the base node is an accessed `Unique`, and the protected nodes are the
entries protected under `activeProtectors`. -/
def basedNormalTree (borrows : List BorrowEntry) (activeProtectors : List Nat) :
    Miri.TreeBorrows.Tree.NormalTreeState :=
  { topology := basedTraversalTree borrows
    defaultStates :=
      (borrows.map (fun (e : BorrowEntry) =>
          Miri.TreeBorrows.Tree.LocationState.mk (annealPermToMiri e.perm) true .None) ++
        [Miri.TreeBorrows.Tree.LocationState.mk .Unique true .None]).toArray
    protectedNodes := protectedIndices borrows activeProtectors
    locationStates := (List.replicate (borrows.length + 1) none).toArray }

/-- Permissions of the first `n` nodes of a Miri tree, read back as Anneal
permissions. -/
def normalTreePerms (tree : Miri.TreeBorrows.Tree.NormalTreeState) (n : Nat) :
    List (Option TreeBorrowPerm) :=
  (List.range n).map (fun i => (tree.stateAt i).map (fun st => miriPermToAnneal st.permission))

/-- **`TreeBorrowsRel`**: Anneal's borrow table `borrows` with active protectors
`activeProtectors` corresponds to Miri's one-location tree `tree`:
* the topology is the based traversal tree of the `I-10` `parentTag` links;
* tags are distinct;
* node `i` holds the permission corresponding (by `TreeBorrowsBijection`) to
  `borrows[i].perm`, and the base node is `Unique`;
* node `i` is protected exactly when `borrows[i]` is. -/
structure TreeBorrowsRel (borrows : List BorrowEntry) (activeProtectors : List Nat)
    (tree : Miri.TreeBorrows.Tree.NormalTreeState) : Prop where
  topology : tree.topology = basedTraversalTree borrows
  tags_unique : (borrows.map BorrowEntry.tag).Nodup
  perms : normalTreePerms tree borrows.length = borrows.map (fun e => some e.perm)
  base_unique :
    (tree.stateAt borrows.length).map (fun st => st.permission) = some .Unique
  protected_eq : tree.protectedNodes = protectedIndices borrows activeProtectors

/-- Distinct tags in list form give the index form used by the `I-10`
classification. -/
theorem borrowTagsUnique_of_nodup (borrows : List BorrowEntry)
    (h : (borrows.map BorrowEntry.tag).Nodup) : BorrowTagsUnique borrows := by
  intro i j hi hj htag
  have hi' : i < (borrows.map BorrowEntry.tag).length := by simpa using hi
  have hj' : j < (borrows.map BorrowEntry.tag).length := by simpa using hj
  exact List.Nodup.eq_of_getElem_eq h hi' hj' (by simpa using htag)


/-! ## 9. General Borrow-Table Read/Write Correspondence & `TreeBorrowsRel` Preservation -/

/-- Relative position of an access through `accessTag` (`none` for a direct
local access, `some tag` for a pointer access) with respect to `entry` in full
borrow hierarchy `allBorrows` (`I-10` parent-child linkage). -/
def treeBorrowAccessRelatedness
    (allBorrows : List BorrowEntry)
    (entry : BorrowEntry)
    (accessTag : Option Nat) :
    TreeBorrowRelatedness :=
  match accessTag with
  | .none => .foreignAccess
  | .some tag =>
    match isBorrowDescendantOrSelf allBorrows tag entry.tag with
    | true => .localAccess
    | false => .foreignAccess

/-- Every borrow tag is a descendant-or-self of itself in `isBorrowDescendantOrSelf`. -/
@[simp]
theorem isBorrowDescendantOrSelf_self_eq_true
    (allBorrows : List BorrowEntry) (tag : Nat) :
    isBorrowDescendantOrSelf allBorrows tag tag = true := by
  unfold isBorrowDescendantOrSelf
  cases length allBorrows <;> simp [isBorrowDescendantOrSelfAux]

/-- Normalizing `writerTag` through `resolveTreeBorrowWriterTag` and then
testing tag equality via `treeBorrowWriterRelatedness` produces the exact
hierarchy relatedness `treeBorrowAccessRelatedness`. -/
@[simp]
theorem treeBorrowWriterRelatedness_resolveTreeBorrowWriterTag
    (allBorrows : List BorrowEntry)
    (entry : BorrowEntry)
    (writerTag : Option Nat) :
    treeBorrowWriterRelatedness entry
      (resolveTreeBorrowWriterTag allBorrows entry writerTag) =
      treeBorrowAccessRelatedness allBorrows entry writerTag := by
  cases writerTag with
  | none => rfl
  | some wTag =>
    unfold resolveTreeBorrowWriterTag treeBorrowAccessRelatedness
    cases hdesc : isBorrowDescendantOrSelf allBorrows wTag entry.tag with
    | true =>
      simp [hdesc, treeBorrowWriterRelatedness]
    | false =>
      cases hbeq : Nat.beq entry.tag wTag with
      | false =>
        simp [hdesc, treeBorrowWriterRelatedness, hbeq]
      | true =>
        have heq : entry.tag = wTag := Nat.eq_of_beq_eq_true hbeq
        rw [← heq, isBorrowDescendantOrSelf_self_eq_true] at hdesc
        cases hdesc

/-- **`borrowEntryReadUB_eq_nodeAccess`**: for any entry whose target local and
projection overlap the read, `borrowEntryReadUB` equals
`treeBorrowTransitionIsUB` of `treeBorrowNodeAccess .read` with hierarchy
relatedness `treeBorrowAccessRelatedness`. -/
theorem borrowEntryReadUB_eq_nodeAccess
    (allBorrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (entry : BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (hloc : entry.targetLocal = targetLocal)
    (hov : borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen = true) :
    borrowEntryReadUB allBorrows activeProtectors entry targetLocal readerTag
        readProj readRangeOff readRangeLen =
      treeBorrowTransitionIsUB
        (treeBorrowNodeAccess .read
          (treeBorrowAccessRelatedness allBorrows entry readerTag)
          entry.perm
          (isBorrowProtected activeProtectors entry)) := by
  unfold borrowEntryReadUB treeBorrowAccessRelatedness
  have hbeq : Nat.beq entry.targetLocal targetLocal = true := by simp [hloc]
  rw [hbeq, hov]; dsimp only []
  cases readerTag with
  | none => rfl
  | some rTag =>
    dsimp only []
    generalize isBorrowDescendantOrSelf allBorrows rTag entry.tag = d
    cases d <;> rfl

/-- **`updateBorrowPermOnReadAtProj_eq_nodeAccess`**: for any entry whose target
local and projection overlap the read, `updateBorrowPermOnReadAtProj` equals
`applyTreeBorrowTransition` of `treeBorrowNodeAccess .read` with hierarchy
relatedness `treeBorrowAccessRelatedness` (because a local read either preserves
`entry.perm` or is `.ub`, and `applyTreeBorrowTransition` leaves `entry`
unchanged on both). -/
theorem updateBorrowPermOnReadAtProj_eq_nodeAccess
    (allBorrows : List BorrowEntry)
    (entry : BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat)
    (hloc : entry.targetLocal = targetLocal)
    (hov : borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen = true) :
    updateBorrowPermOnReadAtProj allBorrows entry targetLocal readerTag
        readProj readRangeOff readRangeLen activeProtectors =
      applyTreeBorrowTransition entry
        (treeBorrowNodeAccess .read
          (treeBorrowAccessRelatedness allBorrows entry readerTag)
          entry.perm
          (isBorrowProtected activeProtectors entry)) := by
  unfold updateBorrowPermOnReadAtProj treeBorrowAccessRelatedness
  have hbeq : Nat.beq entry.targetLocal targetLocal = true := by simp [hloc]
  rw [hbeq, hov]; dsimp only []
  cases readerTag with
  | none => rfl
  | some rTag =>
    dsimp only []
    generalize isBorrowDescendantOrSelf allBorrows rTag entry.tag = d
    cases d with
    | false => rfl
    | true =>
      rcases entry with ⟨tag, tloc, tproj, perm, roff, rlen, prot, ptag⟩
      rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;>
        cases isBorrowProtected activeProtectors
          ⟨tag, tloc, tproj, _, roff, rlen, prot, ptag⟩ <;> rfl

/-- **`hasTreeReadUB_iff_exists`**: `hasTreeReadUB` reports undefined behavior on
`borrows` iff some `entry ∈ borrows` satisfies `borrowEntryReadUB = true`. -/
theorem hasTreeReadUB_iff_exists
    (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat) :
    hasTreeReadUB allBorrows borrows activeProtectors targetLocal readerTag
        readProj readRangeOff readRangeLen = true ↔
      ∃ entry ∈ borrows,
        borrowEntryReadUB allBorrows activeProtectors entry targetLocal readerTag
          readProj readRangeOff readRangeLen = true := by
  induction borrows with
  | nil =>
    simp [hasTreeReadUB]
  | cons hd tl ih =>
    unfold hasTreeReadUB
    cases hhd : borrowEntryReadUB allBorrows activeProtectors hd targetLocal
        readerTag readProj readRangeOff readRangeLen with
    | true =>
      simp only [true_iff]
      exact ⟨hd, List.Mem.head _, hhd⟩
    | false =>
      simp only [ih, List.mem_cons]
      constructor
      · rintro ⟨e, he, hub⟩
        exact ⟨e, Or.inr he, hub⟩
      · rintro ⟨e, rfl | he, hub⟩
        · rw [hhd] at hub; cases hub
        · exact ⟨e, he, hub⟩

/-- **`borrowEntryWriteConflicts_resolve_eq_nodeAccess`**: after hierarchy
normalization via `resolveTreeBorrowWriterTag`, `borrowEntryWriteConflicts`
equals `treeBorrowTransitionIsUB` of `treeBorrowNodeAccess .write` with
`isProtected = true` and hierarchy relatedness `treeBorrowAccessRelatedness`. -/
@[simp]
theorem borrowEntryWriteConflicts_resolve_eq_nodeAccess
    (allBorrows : List BorrowEntry)
    (entry : BorrowEntry)
    (writerTag : Option Nat) :
    borrowEntryWriteConflicts entry
        (resolveTreeBorrowWriterTag allBorrows entry writerTag) =
      treeBorrowTransitionIsUB
        (treeBorrowNodeAccess .write
          (treeBorrowAccessRelatedness allBorrows entry writerTag)
          entry.perm
          true) := by
  unfold borrowEntryWriteConflicts
  rw [treeBorrowWriterRelatedness_resolveTreeBorrowWriterTag]

/-- **`updateBorrowPermTreeAtProj_eq_nodeAccess`**: for any entry whose target
local and projection overlap the write, if the write does not trigger a
protected write conflict at `entry`, `updateBorrowPermTreeAtProj` equals
`applyTreeBorrowTransition` of `treeBorrowNodeAccess .write` with hierarchy
relatedness `treeBorrowAccessRelatedness` and `isBorrowProtected activeProtectors entry`. -/
theorem updateBorrowPermTreeAtProj_eq_nodeAccess
    (allBorrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (entry : BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (hloc : entry.targetLocal = targetLocal)
    (hov : borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = true)
    (hno_prot_ub :
      Bool.and (isBorrowProtected activeProtectors entry)
        (borrowEntryWriteConflicts entry
          (resolveTreeBorrowWriterTag allBorrows entry writerTag)) = false) :
    updateBorrowPermTreeAtProj allBorrows entry targetLocal writerTag
        writeProj writeRangeOff writeRangeLen =
      applyTreeBorrowTransition entry
        (treeBorrowNodeAccess .write
          (treeBorrowAccessRelatedness allBorrows entry writerTag)
          entry.perm
          (isBorrowProtected activeProtectors entry)) := by
  rw [borrowEntryWriteConflicts_resolve_eq_nodeAccess] at hno_prot_ub
  unfold updateBorrowPermTreeAtProj updateBorrowPermAtProj
  have hbeq : Nat.beq entry.targetLocal targetLocal = true := by simp [hloc]
  rw [hbeq, treeBorrowWriterRelatedness_resolveTreeBorrowWriterTag, hov]
  generalize treeBorrowAccessRelatedness allBorrows entry writerTag = rel at hno_prot_ub ⊢
  generalize isBorrowProtected activeProtectors entry = isProt at hno_prot_ub ⊢
  rcases entry with ⟨tag, tloc, tproj, perm, roff, rlen, prot, ptag⟩
  cases rel <;> cases isProt <;> rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;>
    first
    | rfl
    | cases hno_prot_ub

/-- **`hasProtectedTreeWriteConflict_iff_exists`**: `hasProtectedTreeWriteConflict`
reports undefined behavior on `borrows` iff some protected overlapping entry in
`borrows` targeting `targetLocal` has `treeBorrowTransitionIsUB = true` under
`treeBorrowNodeAccess .write`. -/
theorem hasProtectedTreeWriteConflict_iff_exists
    (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat) :
    hasProtectedTreeWriteConflict allBorrows borrows activeProtectors targetLocal
        writerTag writeProj writeRangeOff writeRangeLen = true ↔
      ∃ entry ∈ borrows,
        Bool.and (Nat.beq entry.targetLocal targetLocal)
          (Bool.and (borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen)
            (Bool.and (isBorrowProtected activeProtectors entry)
              (treeBorrowTransitionIsUB
                (treeBorrowNodeAccess .write
                  (treeBorrowAccessRelatedness allBorrows entry writerTag)
                  entry.perm true)))) = true := by
  induction borrows with
  | nil =>
    simp [hasProtectedTreeWriteConflict]
  | cons hd tl ih =>
    unfold hasProtectedTreeWriteConflict; dsimp only []
    rw [borrowEntryWriteConflicts_resolve_eq_nodeAccess]
    generalize hthis :
      Bool.and (Nat.beq hd.targetLocal targetLocal)
        (Bool.and (borrowEntryOverlapsWrite hd writeProj writeRangeOff writeRangeLen)
          (Bool.and (isBorrowProtected activeProtectors hd)
            (treeBorrowTransitionIsUB
              (treeBorrowNodeAccess .write
                (treeBorrowAccessRelatedness allBorrows hd writerTag)
                hd.perm true)))) = c
    cases c with
    | true =>
      simp only [true_iff]
      exact ⟨hd, List.Mem.head _, hthis⟩
    | false =>
      simp only [ih, List.mem_cons]
      constructor
      · rintro ⟨e, he, hub⟩
        exact ⟨e, Or.inr he, hub⟩
      · rintro ⟨e, rfl | he, hub⟩
        · rw [hthis] at hub; cases hub
        · exact ⟨e, he, hub⟩

/-- `freezeTreeBorrowsOnReadAtProj` is `List.map` of `updateBorrowPermOnReadAtProj`. -/
theorem freezeTreeBorrowsOnReadAtProj_eq_map
    (allBorrows borrows : List BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) :
    freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal readerTag
        readProj readRangeOff readRangeLen activeProtectors =
      borrows.map (fun e =>
        updateBorrowPermOnReadAtProj allBorrows e targetLocal readerTag
          readProj readRangeOff readRangeLen activeProtectors) := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    simp only [freezeTreeBorrowsOnReadAtProj, List.map_cons, ih]

/-- `invalidateTreeBorrowsAtProj` is `List.map` of `updateBorrowPermTreeAtProj`. -/
theorem invalidateTreeBorrowsAtProj_eq_map
    (allBorrows borrows : List BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat) :
    invalidateTreeBorrowsAtProj allBorrows borrows targetLocal writerTag
        writeProj writeRangeOff writeRangeLen =
      borrows.map (fun e =>
        updateBorrowPermTreeAtProj allBorrows e targetLocal writerTag
          writeProj writeRangeOff writeRangeLen) := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    simp only [invalidateTreeBorrowsAtProj, List.map_cons, ih]

/-- `basedNormalTree.stateAt` at index `i < borrows.length` returns the accessed
Miri `LocationState` for `borrows[i].perm`. -/
theorem basedNormalTree_stateAt_lt
    (borrows : List BorrowEntry) (activeProtectors : List Nat)
    (i : Nat) (hi : i < borrows.length) :
    (basedNormalTree borrows activeProtectors).stateAt i =
      some ⟨annealPermToMiri borrows[i].perm, true, .None⟩ := by
  have hi1 : i < borrows.length + 1 := Nat.lt_trans hi (Nat.lt_succ_self _)
  simp [basedNormalTree, Miri.TreeBorrows.Tree.NormalTreeState.stateAt, hi, hi1]

/-- `basedNormalTree.stateAt` at the base index `borrows.length` returns an
accessed `Unique` state. -/
theorem basedNormalTree_stateAt_base
    (borrows : List BorrowEntry) (activeProtectors : List Nat) :
    (basedNormalTree borrows activeProtectors).stateAt borrows.length =
      some ⟨.Unique, true, .None⟩ := by
  simp [basedNormalTree, Miri.TreeBorrows.Tree.NormalTreeState.stateAt]

/-- **`basedNormalTree_rel`**: for any Anneal borrow table `borrows` with
distinct tags, `basedNormalTree borrows activeProtectors` satisfies
`TreeBorrowsRel borrows activeProtectors`. -/
theorem basedNormalTree_rel
    (borrows : List BorrowEntry) (activeProtectors : List Nat)
    (hnodup : (borrows.map BorrowEntry.tag).Nodup) :
    TreeBorrowsRel borrows activeProtectors (basedNormalTree borrows activeProtectors) := by
  refine ⟨rfl, hnodup, ?_, ?_, rfl⟩
  · apply List.ext_getElem
    · simp [normalTreePerms]
    · intro i h₁ h₂
      have hi : i < borrows.length := by simpa using h₂
      simp only [normalTreePerms, List.getElem_map, List.getElem_range,
        basedNormalTree_stateAt_lt borrows activeProtectors i hi, Option.map,
        miriPermToAnneal_annealPermToMiri]
  · simp [basedNormalTree_stateAt_base]

private theorem map_tag_eq_of_preserve_tag
    (borrows : List BorrowEntry) (f : BorrowEntry → BorrowEntry)
    (htag : ∀ e, (f e).tag = e.tag) :
    (borrows.map f).map BorrowEntry.tag = borrows.map BorrowEntry.tag := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih => simp [htag, ih]

private theorem updateBorrowPermOnReadAtProj_preserves_tag_parent_prot
    (allBorrows : List BorrowEntry) (e : BorrowEntry)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) :
    let e' := updateBorrowPermOnReadAtProj allBorrows e targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors
    e'.tag = e.tag ∧ e'.parentTag = e.parentTag ∧ e'.protector = e.protector := by
  dsimp only []
  unfold updateBorrowPermOnReadAtProj
  cases Nat.beq e.targetLocal targetLocal with
  | false => exact ⟨rfl, rfl, rfl⟩
  | true =>
    cases borrowEntryOverlapsWrite e readProj readRangeOff readRangeLen with
    | false => exact ⟨rfl, rfl, rfl⟩
    | true =>
      have hf := applyTreeBorrowTransition_fields e
        (treeBorrowNodeAccess .read .foreignAccess e.perm (isBorrowProtected activeProtectors e))
      cases readerTag with
      | none => exact ⟨hf.1, hf.2.2.2.2.2.2, hf.2.2.2.2.2.1⟩
      | some rTag =>
        cases hdesc : isBorrowDescendantOrSelf allBorrows rTag e.tag with
        | true =>
          simp [hdesc]
        | false =>
          simp only [hdesc]
          exact ⟨hf.1, hf.2.2.2.2.2.2, hf.2.2.2.2.2.1⟩

private theorem updateBorrowPermTreeAtProj_preserves_tag_parent_prot
    (allBorrows : List BorrowEntry) (e : BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat) :
    let e' := updateBorrowPermTreeAtProj allBorrows e targetLocal writerTag
      writeProj writeRangeOff writeRangeLen
    e'.tag = e.tag ∧ e'.parentTag = e.parentTag ∧ e'.protector = e.protector := by
  dsimp only []
  unfold updateBorrowPermTreeAtProj updateBorrowPermAtProj
  cases Nat.beq e.targetLocal targetLocal with
  | false => exact ⟨rfl, rfl, rfl⟩
  | true =>
    cases treeBorrowWriterRelatedness e (resolveTreeBorrowWriterTag allBorrows e writerTag) with
    | localAccess =>
      have hf := applyTreeBorrowTransition_fields e
        (treeBorrowNodeAccess .write .localAccess e.perm false)
      exact ⟨hf.1, hf.2.2.2.2.2.2, hf.2.2.2.2.2.1⟩
    | foreignAccess =>
      cases borrowEntryOverlapsWrite e writeProj writeRangeOff writeRangeLen with
      | false => exact ⟨rfl, rfl, rfl⟩
      | true =>
        have hf := applyTreeBorrowTransition_fields e
          (treeBorrowNodeAccess .write .foreignAccess e.perm false)
        exact ⟨hf.1, hf.2.2.2.2.2.2, hf.2.2.2.2.2.1⟩

/-- **`freezeTreeBorrowsOnReadAtProj_preserves_rel`**: across any borrow table
`borrows` with distinct tags, `freezeTreeBorrowsOnReadAtProj` preserves tag
uniqueness and establishes `TreeBorrowsRel` with its `basedNormalTree`. -/
theorem freezeTreeBorrowsOnReadAtProj_preserves_rel
    (allBorrows borrows : List BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat)
    (hnodup : (borrows.map BorrowEntry.tag).Nodup) :
    let borrows' := freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal
      readerTag readProj readRangeOff readRangeLen activeProtectors
    (borrows'.map BorrowEntry.tag).Nodup ∧
      TreeBorrowsRel borrows' activeProtectors (basedNormalTree borrows' activeProtectors) := by
  dsimp only []
  have htags :
      ((freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal readerTag
          readProj readRangeOff readRangeLen activeProtectors).map BorrowEntry.tag) =
        borrows.map BorrowEntry.tag := by
    rw [freezeTreeBorrowsOnReadAtProj_eq_map]
    exact map_tag_eq_of_preserve_tag borrows _ (fun e =>
      (updateBorrowPermOnReadAtProj_preserves_tag_parent_prot allBorrows e targetLocal
        readerTag readProj readRangeOff readRangeLen activeProtectors).1)
  have hnodup' :
      ((freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal readerTag
          readProj readRangeOff readRangeLen activeProtectors).map BorrowEntry.tag).Nodup := by
    rw [htags]; exact hnodup
  exact ⟨hnodup', basedNormalTree_rel _ activeProtectors hnodup'⟩

/-- **`invalidateTreeBorrowsAtProj_preserves_rel`**: across any borrow table
`borrows` with distinct tags, `invalidateTreeBorrowsAtProj` preserves tag
uniqueness and establishes `TreeBorrowsRel` with its `basedNormalTree`. -/
theorem invalidateTreeBorrowsAtProj_preserves_rel
    (allBorrows borrows : List BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (activeProtectors : List Nat)
    (hnodup : (borrows.map BorrowEntry.tag).Nodup) :
    let borrows' := invalidateTreeBorrowsAtProj allBorrows borrows targetLocal
      writerTag writeProj writeRangeOff writeRangeLen
    (borrows'.map BorrowEntry.tag).Nodup ∧
      TreeBorrowsRel borrows' activeProtectors (basedNormalTree borrows' activeProtectors) := by
  dsimp only []
  have htags :
      ((invalidateTreeBorrowsAtProj allBorrows borrows targetLocal writerTag
          writeProj writeRangeOff writeRangeLen).map BorrowEntry.tag) =
        borrows.map BorrowEntry.tag := by
    rw [invalidateTreeBorrowsAtProj_eq_map]
    exact map_tag_eq_of_preserve_tag borrows _ (fun e =>
      (updateBorrowPermTreeAtProj_preserves_tag_parent_prot allBorrows e targetLocal
        writerTag writeProj writeRangeOff writeRangeLen).1)
  have hnodup' :
      ((invalidateTreeBorrowsAtProj allBorrows borrows targetLocal writerTag
          writeProj writeRangeOff writeRangeLen).map BorrowEntry.tag).Nodup := by
    rw [htags]; exact hnodup
  exact ⟨hnodup', basedNormalTree_rel _ activeProtectors hnodup'⟩

/-- `freezeTreeBorrowsOnReadAtProj` preserves the length of `borrows`. -/
@[simp]
theorem freezeTreeBorrowsOnReadAtProj_length
    (allBorrows borrows : List BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) :
    (freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors).length = borrows.length := by
  rw [freezeTreeBorrowsOnReadAtProj_eq_map, List.length_map]

/-- `invalidateTreeBorrowsAtProj` preserves the length of `borrows`. -/
@[simp]
theorem invalidateTreeBorrowsAtProj_length
    (allBorrows borrows : List BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat) :
    (invalidateTreeBorrowsAtProj allBorrows borrows targetLocal writerTag
      writeProj writeRangeOff writeRangeLen).length = borrows.length := by
  rw [invalidateTreeBorrowsAtProj_eq_map, List.length_map]

/-- Any non-UB `treeBorrowNodeAccess` outcome is `.transition` to the permission
produced by `applyTreeBorrowTransition`. -/
theorem treeBorrowNodeAccess_of_isUB_false
    (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (entry : BorrowEntry) (isProtected : Bool)
    (h : treeBorrowTransitionIsUB (treeBorrowNodeAccess kind rel entry.perm isProtected) = false) :
    treeBorrowNodeAccess kind rel entry.perm isProtected =
      .transition (applyTreeBorrowTransition entry (treeBorrowNodeAccess kind rel entry.perm isProtected)).perm := by
  cases hout : treeBorrowNodeAccess kind rel entry.perm isProtected with
  | transition next =>
    simp [applyTreeBorrowTransition]
  | ub =>
    rw [hout] at h; cases h
  | protectedReservedIM =>
    rw [hout] at h; cases h

/-- **`freezeTreeBorrowsOnReadAtProj_locationState_simulation`**: for any
borrow table `borrows`, index `i < borrows.length`, and overlapping entry
`borrows[i]` targeting `targetLocal`, when `hasTreeReadUB` is `false` on
`borrows`, Miri's `LocationState.performAccess` on node `i` of
`basedNormalTree borrows activeProtectors` succeeds and transitions to the exact
mapped permission of node `i` in
`basedNormalTree (freezeTreeBorrowsOnReadAtProj ...) activeProtectors`. -/
theorem freezeTreeBorrowsOnReadAtProj_locationState_simulation
    (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (i : Nat) (hi : i < borrows.length)
    (hloc : borrows[i].targetLocal = targetLocal)
    (hov : borrowEntryOverlapsWrite borrows[i] readProj readRangeOff readRangeLen = true)
    (hskip : treeBorrowAccessRelatedness allBorrows borrows[i] readerTag = .foreignAccess →
      borrows[i].perm ≠ .disabled)
    (hno_ub : hasTreeReadUB allBorrows borrows activeProtectors targetLocal readerTag
      readProj readRangeOff readRangeLen = false) :
    let borrows' := freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal
      readerTag readProj readRangeOff readRangeLen activeProtectors
    let hi' : i < borrows'.length := by
      dsimp only [borrows']
      rw [freezeTreeBorrowsOnReadAtProj_length]
      exact hi
    let nt := basedNormalTree borrows activeProtectors
    let nt' := basedNormalTree borrows' activeProtectors
    let rel := treeBorrowAccessRelatedness allBorrows borrows[i] readerTag
    let isProt := isBorrowProtected activeProtectors borrows[i]
    borrowEntryReadUB allBorrows activeProtectors borrows[i] targetLocal readerTag
      readProj readRangeOff readRangeLen = false ∧
    nt.stateAt i = some ⟨annealPermToMiri borrows[i].perm, true, .None⟩ ∧
    nt'.stateAt i = some ⟨annealPermToMiri (borrows'[i]'hi').perm, true, .None⟩ ∧
    (∃ transition,
      Miri.TreeBorrows.Tree.LocationState.performAccess
        ⟨annealPermToMiri borrows[i].perm, true, .None⟩
        .Read (annealRelatednessToMiri rel) isProt =
      .Success ⟨annealPermToMiri (borrows'[i]'hi').perm, true, .None⟩ transition) := by
  dsimp only []
  have hmem : borrows[i] ∈ borrows := List.getElem_mem hi
  have he_ub : borrowEntryReadUB allBorrows activeProtectors borrows[i] targetLocal readerTag
      readProj readRangeOff readRangeLen = false := by
    cases hb : borrowEntryReadUB allBorrows activeProtectors borrows[i] targetLocal readerTag
        readProj readRangeOff readRangeLen with
    | false => rfl
    | true =>
      have hex : hasTreeReadUB allBorrows borrows activeProtectors targetLocal readerTag
          readProj readRangeOff readRangeLen = true :=
        (hasTreeReadUB_iff_exists allBorrows borrows activeProtectors targetLocal readerTag
          readProj readRangeOff readRangeLen).mpr ⟨borrows[i], hmem, hb⟩
      rw [hno_ub] at hex
      cases hex
  have hnode_ub :
      treeBorrowTransitionIsUB
        (treeBorrowNodeAccess .read
          (treeBorrowAccessRelatedness allBorrows borrows[i] readerTag)
          borrows[i].perm
          (isBorrowProtected activeProtectors borrows[i])) = false := by
    rw [← borrowEntryReadUB_eq_nodeAccess allBorrows activeProtectors borrows[i]
      targetLocal readerTag readProj readRangeOff readRangeLen hloc hov]
    exact he_ub
  have htr := treeBorrowNodeAccess_of_isUB_false .read
    (treeBorrowAccessRelatedness allBorrows borrows[i] readerTag)
    borrows[i] (isBorrowProtected activeProtectors borrows[i]) hnode_ub
  have hsim := nodeAccess_locationState_simulation .read
    (treeBorrowAccessRelatedness allBorrows borrows[i] readerTag)
    borrows[i].perm (isBorrowProtected activeProtectors borrows[i]) .None hskip
  rw [htr] at hsim
  have hget' :
      (freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal readerTag
        readProj readRangeOff readRangeLen activeProtectors)[i]'(by
          rw [freezeTreeBorrowsOnReadAtProj_length]; exact hi) =
      applyTreeBorrowTransition borrows[i]
        (treeBorrowNodeAccess .read
          (treeBorrowAccessRelatedness allBorrows borrows[i] readerTag)
          borrows[i].perm
          (isBorrowProtected activeProtectors borrows[i])) := by
    simp only [freezeTreeBorrowsOnReadAtProj_eq_map, List.getElem_map]
    exact updateBorrowPermOnReadAtProj_eq_nodeAccess allBorrows borrows[i] targetLocal
      readerTag readProj readRangeOff readRangeLen activeProtectors hloc hov
  refine ⟨he_ub,
    basedNormalTree_stateAt_lt borrows activeProtectors i hi,
    basedNormalTree_stateAt_lt _ activeProtectors i _,
    ?_⟩
  rw [hget']
  exact hsim

/-- **`invalidateTreeBorrowsAtProj_locationState_simulation`**: for any
borrow table `borrows`, index `i < borrows.length`, and overlapping entry
`borrows[i]` targeting `targetLocal`, when `hasProtectedTreeWriteConflict` is
`false` on `borrows` and the per-node write transition at `borrows[i]` is
non-UB, Miri's `LocationState.performAccess` on node `i` of
`basedNormalTree borrows activeProtectors` succeeds and transitions to the exact
mapped permission of node `i` in
`basedNormalTree (invalidateTreeBorrowsAtProj ...) activeProtectors`. -/
theorem invalidateTreeBorrowsAtProj_locationState_simulation
    (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (i : Nat) (hi : i < borrows.length)
    (hloc : borrows[i].targetLocal = targetLocal)
    (hov : borrowEntryOverlapsWrite borrows[i] writeProj writeRangeOff writeRangeLen = true)
    (hskip : treeBorrowAccessRelatedness allBorrows borrows[i] writerTag = .foreignAccess →
      borrows[i].perm ≠ .disabled)
    (hno_prot : hasProtectedTreeWriteConflict allBorrows borrows activeProtectors targetLocal
      writerTag writeProj writeRangeOff writeRangeLen = false)
    (hnode_ub :
      treeBorrowTransitionIsUB
        (treeBorrowNodeAccess .write
          (treeBorrowAccessRelatedness allBorrows borrows[i] writerTag)
          borrows[i].perm
          (isBorrowProtected activeProtectors borrows[i])) = false) :
    let borrows' := invalidateTreeBorrowsAtProj allBorrows borrows targetLocal
      writerTag writeProj writeRangeOff writeRangeLen
    let hi' : i < borrows'.length := by
      dsimp only [borrows']
      rw [invalidateTreeBorrowsAtProj_length]
      exact hi
    let nt := basedNormalTree borrows activeProtectors
    let nt' := basedNormalTree borrows' activeProtectors
    let rel := treeBorrowAccessRelatedness allBorrows borrows[i] writerTag
    let isProt := isBorrowProtected activeProtectors borrows[i]
    nt.stateAt i = some ⟨annealPermToMiri borrows[i].perm, true, .None⟩ ∧
    nt'.stateAt i = some ⟨annealPermToMiri (borrows'[i]'hi').perm, true, .None⟩ ∧
    (∃ transition,
      Miri.TreeBorrows.Tree.LocationState.performAccess
        ⟨annealPermToMiri borrows[i].perm, true, .None⟩
        .Write (annealRelatednessToMiri rel) isProt =
      .Success ⟨annealPermToMiri (borrows'[i]'hi').perm, true, .None⟩ transition) := by
  dsimp only []
  have hmem : borrows[i] ∈ borrows := List.getElem_mem hi
  have hno_prot_i :
      Bool.and (isBorrowProtected activeProtectors borrows[i])
        (borrowEntryWriteConflicts borrows[i]
          (resolveTreeBorrowWriterTag allBorrows borrows[i] writerTag)) = false := by
    cases hb : Bool.and (isBorrowProtected activeProtectors borrows[i])
        (borrowEntryWriteConflicts borrows[i]
          (resolveTreeBorrowWriterTag allBorrows borrows[i] writerTag)) with
    | false => rfl
    | true =>
      rw [borrowEntryWriteConflicts_resolve_eq_nodeAccess] at hb
      have hbeq : Nat.beq borrows[i].targetLocal targetLocal = true := by simp [hloc]
      have hex : hasProtectedTreeWriteConflict allBorrows borrows activeProtectors targetLocal
          writerTag writeProj writeRangeOff writeRangeLen = true :=
        (hasProtectedTreeWriteConflict_iff_exists allBorrows borrows activeProtectors targetLocal
          writerTag writeProj writeRangeOff writeRangeLen).mpr
          ⟨borrows[i], hmem, by rw [hbeq, hov, hb]; rfl⟩
      rw [hno_prot] at hex
      cases hex
  have htr := treeBorrowNodeAccess_of_isUB_false .write
    (treeBorrowAccessRelatedness allBorrows borrows[i] writerTag)
    borrows[i] (isBorrowProtected activeProtectors borrows[i]) hnode_ub
  have hsim := nodeAccess_locationState_simulation .write
    (treeBorrowAccessRelatedness allBorrows borrows[i] writerTag)
    borrows[i].perm (isBorrowProtected activeProtectors borrows[i]) .None hskip
  rw [htr] at hsim
  have hget' :
      (invalidateTreeBorrowsAtProj allBorrows borrows targetLocal writerTag
        writeProj writeRangeOff writeRangeLen)[i]'(by
          rw [invalidateTreeBorrowsAtProj_length]; exact hi) =
      applyTreeBorrowTransition borrows[i]
        (treeBorrowNodeAccess .write
          (treeBorrowAccessRelatedness allBorrows borrows[i] writerTag)
          borrows[i].perm
          (isBorrowProtected activeProtectors borrows[i])) := by
    simp only [invalidateTreeBorrowsAtProj_eq_map, List.getElem_map]
    exact updateBorrowPermTreeAtProj_eq_nodeAccess allBorrows activeProtectors borrows[i]
      targetLocal writerTag writeProj writeRangeOff writeRangeLen hloc hov hno_prot_i
  refine ⟨basedNormalTree_stateAt_lt borrows activeProtectors i hi,
    basedNormalTree_stateAt_lt _ activeProtectors i _,
    ?_⟩
  rw [hget']
  exact hsim

/-! ## 10. Sub-Place / Byte-Range Overlap & Multi-Node `NormalTreeState.performAccess` Lockstep -/

private theorem nat_beq_eq_false_of_ne {a b : Nat} (h : a ≠ b) :
    Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem nat_beq_eq_false_iff_ne (a b : Nat) :
    Nat.beq a b = false ↔ a ≠ b :=
  ⟨fun h heq => by subst heq; simp at h, nat_beq_eq_false_of_ne⟩

/-- **`byteRangesOverlapBool_iff`**: Anneal's `byteRangesOverlapBool` is exact
non-empty intersection of positive half-open byte intervals
`[offA, offA + lenA) ∩ [offB, offB + lenB) ≠ ∅`. -/
theorem byteRangesOverlapBool_iff (offA lenA offB lenB : Nat) :
    byteRangesOverlapBool offA lenA offB lenB = true ↔
      0 < lenA ∧ 0 < lenB ∧ offA < offB + lenB ∧ offB < offA + lenA := by
  unfold byteRangesOverlapBool
  simp only [Bool.and_eq_true, Bool.not_eq_true', nat_beq_eq_false_iff_ne,
    Nat.ble_eq, Nat.add_eq]
  omega

/-- **`borrowEntryOverlapsWrite_iff`**: when both the access and `entry` carry
positive byte lengths, `borrowEntryOverlapsWrite` decides exact half-open byte
interval intersection; otherwise it delegates to structural `projectionsOverlap`
(`Places.lean`). -/
theorem borrowEntryOverlapsWrite_iff
    (entry : BorrowEntry) (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat) :
    borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = true ↔
      if 0 < writeRangeLen ∧ 0 < entry.rangeLen then
        entry.rangeOffset < writeRangeOff + writeRangeLen ∧
          writeRangeOff < entry.rangeOffset + entry.rangeLen
      else
        projectionsOverlap entry.targetProjection writeProj = true := by
  unfold borrowEntryOverlapsWrite
  by_cases hr : 0 < writeRangeLen ∧ 0 < entry.rangeLen
  · have h1 : Bool.not (Nat.beq writeRangeLen 0) = true := by
      simp only [Bool.not_eq_true', nat_beq_eq_false_iff_ne]; omega
    have h2 : Bool.not (Nat.beq entry.rangeLen 0) = true := by
      simp only [Bool.not_eq_true', nat_beq_eq_false_iff_ne]; omega
    simp only [h1, h2, Bool.and_self, hr, true_and, and_self, ↓reduceIte,
      byteRangesOverlapBool_iff]
  · have hb :
        Bool.and (Bool.not (Nat.beq writeRangeLen 0)) (Bool.not (Nat.beq entry.rangeLen 0)) =
          false := by
      cases hw : Nat.beq writeRangeLen 0 <;> cases he : Nat.beq entry.rangeLen 0
      · exfalso
        have hw0 : writeRangeLen ≠ 0 := (nat_beq_eq_false_iff_ne _ _).mp hw
        have he0 : entry.rangeLen ≠ 0 := (nat_beq_eq_false_iff_ne _ _).mp he
        exact hr ⟨Nat.pos_of_ne_zero hw0, Nat.pos_of_ne_zero he0⟩
      · rfl
      · rfl
      · rfl
    simp only [hb, hr, ↓reduceIte]

/-- **`borrowEntryReadUB_of_disjoint`**: a read on another local or a disjoint
projection / byte range never triggers undefined behavior at `entry`. -/
theorem borrowEntryReadUB_of_disjoint
    (allBorrows : List BorrowEntry) (activeProtectors : List Nat)
    (entry : BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (hdisj : entry.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen = false) :
    borrowEntryReadUB allBorrows activeProtectors entry targetLocal readerTag
      readProj readRangeOff readRangeLen = false := by
  unfold borrowEntryReadUB
  rcases hdisj with hloc | hov
  · rw [nat_beq_eq_false_of_ne hloc]
  · cases Nat.beq entry.targetLocal targetLocal
    · rfl
    · rw [hov]

/-- **`updateBorrowPermOnReadAtProj_of_disjoint`**: a read on another local or a
disjoint projection / byte range leaves `entry` unchanged. -/
theorem updateBorrowPermOnReadAtProj_of_disjoint
    (allBorrows : List BorrowEntry) (entry : BorrowEntry)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat)
    (hdisj : entry.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen = false) :
    updateBorrowPermOnReadAtProj allBorrows entry targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors = entry := by
  unfold updateBorrowPermOnReadAtProj
  rcases hdisj with hloc | hov
  · rw [nat_beq_eq_false_of_ne hloc]
  · cases Nat.beq entry.targetLocal targetLocal
    · rfl
    · rw [hov]

/-- **`updateBorrowPermTreeAtProj_of_foreign_disjoint`**: a write on another
local, or a foreign write to a disjoint projection / byte range within the same
local, leaves `entry` unchanged. -/
theorem updateBorrowPermTreeAtProj_of_foreign_disjoint
    (allBorrows : List BorrowEntry) (entry : BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat)
    (hdisj : entry.targetLocal ≠ targetLocal ∨
      (treeBorrowAccessRelatedness allBorrows entry writerTag = .foreignAccess ∧
        borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = false)) :
    updateBorrowPermTreeAtProj allBorrows entry targetLocal writerTag
      writeProj writeRangeOff writeRangeLen = entry := by
  unfold updateBorrowPermTreeAtProj updateBorrowPermAtProj
  rcases hdisj with hloc | ⟨hrel, hov⟩
  · rw [nat_beq_eq_false_of_ne hloc]
  · cases Nat.beq entry.targetLocal targetLocal
    · rfl
    · rw [treeBorrowWriterRelatedness_resolveTreeBorrowWriterTag, hrel, hov]

/-- **`hasTreeReadUB_of_all_disjoint`**: if every entry in `rest` targets a
different local or a projection / byte range disjoint from `(readProj,
readRangeOff, readRangeLen)`, `hasTreeReadUB` over `rest` is `false`. -/
theorem hasTreeReadUB_of_all_disjoint
    (allBorrows rest : List BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite e readProj readRangeOff readRangeLen = false) :
    hasTreeReadUB allBorrows rest activeProtectors targetLocal readerTag
      readProj readRangeOff readRangeLen = false := by
  induction rest with
  | nil => rfl
  | cons hd tl ih =>
    unfold hasTreeReadUB
    rw [borrowEntryReadUB_of_disjoint allBorrows activeProtectors hd targetLocal readerTag
      readProj readRangeOff readRangeLen (hdisj hd (List.Mem.head _))]
    exact ih (fun e he => hdisj e (List.Mem.tail _ he))

/-- **`hasTreeReadUB_disjoint_tail`**: when every entry in `rest` is disjoint
from the read at `(targetLocal, readProj, readRangeOff, readRangeLen)`,
`hasTreeReadUB` on `b₀ :: rest` reduces to `borrowEntryReadUB` on `b₀` alone. -/
theorem hasTreeReadUB_disjoint_tail
    (allBorrows : List BorrowEntry) (b₀ : BorrowEntry) (rest : List BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite e readProj readRangeOff readRangeLen = false) :
    hasTreeReadUB allBorrows (b₀ :: rest) activeProtectors targetLocal readerTag
      readProj readRangeOff readRangeLen =
    borrowEntryReadUB allBorrows activeProtectors b₀ targetLocal readerTag
      readProj readRangeOff readRangeLen := by
  unfold hasTreeReadUB
  rw [hasTreeReadUB_of_all_disjoint allBorrows rest activeProtectors targetLocal readerTag
    readProj readRangeOff readRangeLen hdisj]
  cases borrowEntryReadUB allBorrows activeProtectors b₀ targetLocal readerTag
    readProj readRangeOff readRangeLen <;> rfl

/-- **`freezeTreeBorrowsOnReadAtProj_of_all_disjoint`**: if every entry in
`rest` targets a different local or a projection / byte range disjoint from
`(readProj, readRangeOff, readRangeLen)`, `freezeTreeBorrowsOnReadAtProj` leaves
`rest` unchanged. -/
theorem freezeTreeBorrowsOnReadAtProj_of_all_disjoint
    (allBorrows rest : List BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite e readProj readRangeOff readRangeLen = false) :
    freezeTreeBorrowsOnReadAtProj allBorrows rest targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors = rest := by
  induction rest with
  | nil => rfl
  | cons hd tl ih =>
    unfold freezeTreeBorrowsOnReadAtProj
    rw [updateBorrowPermOnReadAtProj_of_disjoint allBorrows hd targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors (hdisj hd (List.Mem.head _)),
      ih (fun e he => hdisj e (List.Mem.tail _ he))]

/-- **`freezeTreeBorrowsOnReadAtProj_disjoint_tail`**: when every entry in
`rest` is disjoint from the read at `(targetLocal, readProj, readRangeOff,
readRangeLen)`, `freezeTreeBorrowsOnReadAtProj` updates `b₀` and preserves the
disjoint tail `rest` identically. -/
theorem freezeTreeBorrowsOnReadAtProj_disjoint_tail
    (allBorrows : List BorrowEntry) (b₀ : BorrowEntry) (rest : List BorrowEntry)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite e readProj readRangeOff readRangeLen = false) :
    freezeTreeBorrowsOnReadAtProj allBorrows (b₀ :: rest) targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors =
    updateBorrowPermOnReadAtProj allBorrows b₀ targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors :: rest := by
  unfold freezeTreeBorrowsOnReadAtProj
  rw [freezeTreeBorrowsOnReadAtProj_of_all_disjoint allBorrows rest targetLocal readerTag
    readProj readRangeOff readRangeLen activeProtectors hdisj]

/-- **`hasProtectedTreeWriteConflict_of_all_disjoint`**: if every entry in
`rest` targets a different local or a projection / byte range disjoint from
`(writeProj, writeRangeOff, writeRangeLen)`, `hasProtectedTreeWriteConflict`
over `rest` is `false` even when entries in `rest` carry active protectors. -/
theorem hasProtectedTreeWriteConflict_of_all_disjoint
    (allBorrows rest : List BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite e writeProj writeRangeOff writeRangeLen = false) :
    hasProtectedTreeWriteConflict allBorrows rest activeProtectors targetLocal
      writerTag writeProj writeRangeOff writeRangeLen = false := by
  induction rest with
  | nil => rfl
  | cons hd tl ih =>
    unfold hasProtectedTreeWriteConflict
    dsimp only []
    have hthis :
        Bool.and (Nat.beq hd.targetLocal targetLocal)
          (Bool.and (borrowEntryOverlapsWrite hd writeProj writeRangeOff writeRangeLen)
            (Bool.and (isBorrowProtected activeProtectors hd)
              (borrowEntryWriteConflicts hd
                (resolveTreeBorrowWriterTag allBorrows hd writerTag)))) = false := by
      rcases hdisj hd (List.Mem.head _) with hloc | hov
      · rw [nat_beq_eq_false_of_ne hloc]; rfl
      · rw [hov]; cases Nat.beq hd.targetLocal targetLocal <;> rfl
    rw [hthis]
    exact ih (fun e he => hdisj e (List.Mem.tail _ he))

/-- **`invalidateTreeBorrowsAtProj_of_all_foreign_disjoint`**: if every entry in
`rest` either targets another local or experiences a foreign write on a disjoint
projection / byte range, `invalidateTreeBorrowsAtProj` leaves `rest` unchanged. -/
theorem invalidateTreeBorrowsAtProj_of_all_foreign_disjoint
    (allBorrows rest : List BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      (treeBorrowAccessRelatedness allBorrows e writerTag = .foreignAccess ∧
        borrowEntryOverlapsWrite e writeProj writeRangeOff writeRangeLen = false)) :
    invalidateTreeBorrowsAtProj allBorrows rest targetLocal writerTag
      writeProj writeRangeOff writeRangeLen = rest := by
  induction rest with
  | nil => rfl
  | cons hd tl ih =>
    unfold invalidateTreeBorrowsAtProj
    rw [updateBorrowPermTreeAtProj_of_foreign_disjoint allBorrows hd targetLocal writerTag
      writeProj writeRangeOff writeRangeLen (hdisj hd (List.Mem.head _)),
      ih (fun e he => hdisj e (List.Mem.tail _ he))]

/-- **`invalidateTreeBorrowsAtProj_disjoint_tail`**: when every entry in `rest`
experiences a foreign write on a disjoint projection / byte range (or targets
another local), `invalidateTreeBorrowsAtProj` updates `b₀` and preserves the
disjoint tail `rest` identically. -/
theorem invalidateTreeBorrowsAtProj_disjoint_tail
    (allBorrows : List BorrowEntry) (b₀ : BorrowEntry) (rest : List BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      (treeBorrowAccessRelatedness allBorrows e writerTag = .foreignAccess ∧
        borrowEntryOverlapsWrite e writeProj writeRangeOff writeRangeLen = false)) :
    invalidateTreeBorrowsAtProj allBorrows (b₀ :: rest) targetLocal writerTag
      writeProj writeRangeOff writeRangeLen =
    updateBorrowPermTreeAtProj allBorrows b₀ targetLocal writerTag
      writeProj writeRangeOff writeRangeLen :: rest := by
  unfold invalidateTreeBorrowsAtProj
  rw [invalidateTreeBorrowsAtProj_of_all_foreign_disjoint allBorrows rest targetLocal writerTag
    writeProj writeRangeOff writeRangeLen hdisj]

/-- Tag accessed by starting a normal-tree traversal at node `start` in
`basedNormalTree borrows`: `some borrows[start].tag` for borrow nodes
`start < borrows.length`, and `none` (direct local access through the base root)
when `start = borrows.length`. -/
def basedAccessTag (borrows : List BorrowEntry) (start : Nat) : Option Nat :=
  (borrows[start]?).map BorrowEntry.tag

/-- Combined Anneal undefined-behavior predicate on `borrows` for an access of
`kind` at `targetLocal` initiated from node `start` of `basedNormalTree borrows`. -/
def annealTableAccessUB
    (kind : TreeBorrowAccessKind)
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (start : Nat) : Bool :=
  let tag := basedAccessTag borrows start
  match kind with
  | .read =>
    hasTreeReadUB borrows borrows activeProtectors targetLocal tag .nil 0 0
  | .write =>
    Bool.or
      (treeBorrowChainChildAccessUBAux .write (length borrows) borrows tag)
      (hasProtectedTreeWriteConflict borrows borrows activeProtectors targetLocal tag .nil 0 0)

/-- Successor Anneal borrow table after an access of `kind` at `targetLocal`
initiated from node `start` of `basedNormalTree borrows`. -/
def annealTableAfterAccess
    (kind : TreeBorrowAccessKind)
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (start : Nat) : List BorrowEntry :=
  let tag := basedAccessTag borrows start
  match kind with
  | .read =>
    freezeTreeBorrowsOnReadAtProj borrows borrows targetLocal tag .nil 0 0 activeProtectors
  | .write =>
    invalidateTreeBorrowsAtProj borrows borrows targetLocal tag .nil 0 0

private def mkNormalTree1 (perm : TreeBorrowPerm) (p₀ : Bool) :
    Miri.TreeBorrows.Tree.NormalTreeState :=
  { topology := ⟨#[⟨some 1, []⟩, ⟨none, [0]⟩]⟩
    defaultStates :=
      #[⟨annealPermToMiri perm, true, .None⟩, ⟨.Unique, true, .None⟩]
    protectedNodes := if p₀ then [0] else []
    locationStates := #[none, none] }

private def mkNormalTreeParentChild (cPerm pPerm : TreeBorrowPerm) (p₀ p₁ : Bool) :
    Miri.TreeBorrows.Tree.NormalTreeState :=
  { topology := ⟨#[⟨some 1, []⟩, ⟨some 2, [0]⟩, ⟨none, [1]⟩]⟩
    defaultStates :=
      #[⟨annealPermToMiri cPerm, true, .None⟩,
        ⟨annealPermToMiri pPerm, true, .None⟩,
        ⟨.Unique, true, .None⟩]
    protectedNodes := (if p₀ then [0] else []) ++ (if p₁ then [1] else [])
    locationStates := #[none, none, none] }

private def mkNormalTreeSiblings (perm₀ perm₁ : TreeBorrowPerm) (p₀ p₁ : Bool) :
    Miri.TreeBorrows.Tree.NormalTreeState :=
  { topology := ⟨#[⟨some 2, []⟩, ⟨some 2, []⟩, ⟨none, [0, 1]⟩]⟩
    defaultStates :=
      #[⟨annealPermToMiri perm₀, true, .None⟩,
        ⟨annealPermToMiri perm₁, true, .None⟩,
        ⟨.Unique, true, .None⟩]
    protectedNodes := (if p₀ then [0] else []) ++ (if p₁ then [1] else [])
    locationStates := #[none, none, none] }

private def mkNormalTreeChain3 (gPerm cPerm rPerm : TreeBorrowPerm) :
    Miri.TreeBorrows.Tree.NormalTreeState :=
  { topology := ⟨#[⟨some 1, []⟩, ⟨some 2, [0]⟩, ⟨some 3, [1]⟩, ⟨none, [2]⟩]⟩
    defaultStates :=
      #[⟨annealPermToMiri gPerm, true, .None⟩,
        ⟨annealPermToMiri cPerm, true, .None⟩,
        ⟨annealPermToMiri rPerm, true, .None⟩,
        ⟨.Unique, true, .None⟩]
    protectedNodes := []
    locationStates := #[none, none, none, none] }

private def mkNormalTreeBranch3 (c₀Perm c₁Perm pPerm : TreeBorrowPerm) :
    Miri.TreeBorrows.Tree.NormalTreeState :=
  { topology := ⟨#[⟨some 2, []⟩, ⟨some 2, []⟩, ⟨some 3, [0, 1]⟩, ⟨none, [2]⟩]⟩
    defaultStates :=
      #[⟨annealPermToMiri c₀Perm, true, .None⟩,
        ⟨annealPermToMiri c₁Perm, true, .None⟩,
        ⟨annealPermToMiri pPerm, true, .None⟩,
        ⟨.Unique, true, .None⟩]
    protectedNodes := []
    locationStates := #[none, none, none, none] }

private theorem basedNormalTree_singleton_eq (b₀ : BorrowEntry)
    (activeProtectors : List Nat) (hp₀ : b₀.parentTag = none) :
    basedNormalTree [b₀] activeProtectors =
      mkNormalTree1 b₀.perm (isBorrowProtected activeProtectors b₀) := by
  have hbp : basedParentIndex [b₀] b₀ = 1 := by simp [basedParentIndex, hp₀]
  have hrange : List.range 1 = [0] := rfl
  cases hprot : isBorrowProtected activeProtectors b₀ <;>
    simp [basedNormalTree, mkNormalTree1, basedTraversalTree, basedChildren,
      protectedIndices, hbp, hrange, hprot]

private theorem basedNormalTree_parent_child_eq (child parent : BorrowEntry)
    (activeProtectors : List Nat)
    (hneq : child.tag ≠ parent.tag)
    (hcpar : child.parentTag = some parent.tag)
    (hppar : parent.parentTag = none) :
    basedNormalTree [child, parent] activeProtectors =
      mkNormalTreeParentChild child.perm parent.perm
        (isBorrowProtected activeProtectors child)
        (isBorrowProtected activeProtectors parent) := by
  have hbeq : Nat.beq child.tag parent.tag = false := nat_beq_eq_false_of_ne hneq
  have hidx : borrowIndexOfTag [child, parent] parent.tag = some 1 := by
    simp [borrowIndexOfTag, hbeq]
  have hbpc : basedParentIndex [child, parent] child = 1 := by
    simp [basedParentIndex, hcpar, hidx]
  have hbpp : basedParentIndex [child, parent] parent = 2 := by
    simp [basedParentIndex, hppar]
  have hrange : List.range 2 = [0, 1] := rfl
  cases hp₀ : isBorrowProtected activeProtectors child <;>
    cases hp₁ : isBorrowProtected activeProtectors parent <;>
    simp [basedNormalTree, mkNormalTreeParentChild, basedTraversalTree, basedChildren,
      protectedIndices, hbpc, hbpp, hrange, hp₀, hp₁]

private theorem basedNormalTree_siblings_eq (b₀ b₁ : BorrowEntry)
    (activeProtectors : List Nat)
    (hp₀ : b₀.parentTag = none)
    (hp₁ : b₁.parentTag = none) :
    basedNormalTree [b₀, b₁] activeProtectors =
      mkNormalTreeSiblings b₀.perm b₁.perm
        (isBorrowProtected activeProtectors b₀)
        (isBorrowProtected activeProtectors b₁) := by
  have hbp₀ : basedParentIndex [b₀, b₁] b₀ = 2 := by simp [basedParentIndex, hp₀]
  have hbp₁ : basedParentIndex [b₀, b₁] b₁ = 2 := by simp [basedParentIndex, hp₁]
  have hrange : List.range 2 = [0, 1] := rfl
  cases hpr₀ : isBorrowProtected activeProtectors b₀ <;>
    cases hpr₁ : isBorrowProtected activeProtectors b₁ <;>
    simp [basedNormalTree, mkNormalTreeSiblings, basedTraversalTree, basedChildren,
      protectedIndices, hbp₀, hbp₁, hrange, hpr₀, hpr₁]

private theorem basedNormalTree_chain3_eq (g c r : BorrowEntry)
    (activeProtectors : List Nat)
    (hneq_gc : g.tag ≠ c.tag) (hneq_gr : g.tag ≠ r.tag) (hneq_cr : c.tag ≠ r.tag)
    (hgpar : g.parentTag = some c.tag)
    (hcpar : c.parentTag = some r.tag)
    (hrpar : r.parentTag = none)
    (hgprot : isBorrowProtected activeProtectors g = false)
    (hcprot : isBorrowProtected activeProtectors c = false)
    (hrprot : isBorrowProtected activeProtectors r = false) :
    basedNormalTree [g, c, r] activeProtectors =
      mkNormalTreeChain3 g.perm c.perm r.perm := by
  have hbeq_gc : Nat.beq g.tag c.tag = false := nat_beq_eq_false_of_ne hneq_gc
  have hbeq_gr : Nat.beq g.tag r.tag = false := nat_beq_eq_false_of_ne hneq_gr
  have hbeq_cr : Nat.beq c.tag r.tag = false := nat_beq_eq_false_of_ne hneq_cr
  have hidxc : borrowIndexOfTag [g, c, r] c.tag = some 1 := by
    simp [borrowIndexOfTag, hbeq_gc]
  have hidxr : borrowIndexOfTag [g, c, r] r.tag = some 2 := by
    simp [borrowIndexOfTag, hbeq_gr, hbeq_cr]
  have hbpg : basedParentIndex [g, c, r] g = 1 := by
    simp [basedParentIndex, hgpar, hidxc]
  have hbpc : basedParentIndex [g, c, r] c = 2 := by
    simp [basedParentIndex, hcpar, hidxr]
  have hbpr : basedParentIndex [g, c, r] r = 3 := by
    simp [basedParentIndex, hrpar]
  have hrange : List.range 3 = [0, 1, 2] := rfl
  simp [basedNormalTree, mkNormalTreeChain3, basedTraversalTree, basedChildren,
    protectedIndices, hbpg, hbpc, hbpr, hrange, hgprot, hcprot, hrprot]

private theorem basedNormalTree_branch3_eq (c₀ c₁ p : BorrowEntry)
    (activeProtectors : List Nat)
    (hneq₀p : c₀.tag ≠ p.tag) (hneq₁p : c₁.tag ≠ p.tag)
    (hc₀par : c₀.parentTag = some p.tag)
    (hc₁par : c₁.parentTag = some p.tag)
    (hppar : p.parentTag = none)
    (hc₀prot : isBorrowProtected activeProtectors c₀ = false)
    (hc₁prot : isBorrowProtected activeProtectors c₁ = false)
    (hpprot : isBorrowProtected activeProtectors p = false) :
    basedNormalTree [c₀, c₁, p] activeProtectors =
      mkNormalTreeBranch3 c₀.perm c₁.perm p.perm := by
  have hbeq₀p : Nat.beq c₀.tag p.tag = false := nat_beq_eq_false_of_ne hneq₀p
  have hbeq₁p : Nat.beq c₁.tag p.tag = false := nat_beq_eq_false_of_ne hneq₁p
  have hidxp : borrowIndexOfTag [c₀, c₁, p] p.tag = some 2 := by
    simp [borrowIndexOfTag, hbeq₀p, hbeq₁p]
  have hbpc₀ : basedParentIndex [c₀, c₁, p] c₀ = 2 := by
    simp [basedParentIndex, hc₀par, hidxp]
  have hbpc₁ : basedParentIndex [c₀, c₁, p] c₁ = 2 := by
    simp [basedParentIndex, hc₁par, hidxp]
  have hbpp : basedParentIndex [c₀, c₁, p] p = 3 := by
    simp [basedParentIndex, hppar]
  have hrange : List.range 3 = [0, 1, 2] := rfl
  simp [basedNormalTree, mkNormalTreeBranch3, basedTraversalTree, basedChildren,
    protectedIndices, hbpc₀, hbpc₁, hbpp, hrange, hc₀prot, hc₁prot, hpprot]

private def canon1 (perm : TreeBorrowPerm) (p₀ : Bool) : List BorrowEntry :=
  [{ tag := 1, targetLocal := 0, targetProjection := .nil, perm := perm,
     protector := if p₀ then some 1 else none, parentTag := none }]

private def canonProts1 (p₀ : Bool) : List Nat :=
  if p₀ then [1] else []

private def canonPC (cPerm pPerm : TreeBorrowPerm) (p₀ p₁ : Bool) : List BorrowEntry :=
  [{ tag := 2, targetLocal := 0, targetProjection := .nil, perm := cPerm,
     protector := if p₀ then some 1 else none, parentTag := some 1 },
   { tag := 1, targetLocal := 0, targetProjection := .nil, perm := pPerm,
     protector := if p₁ then some 2 else none, parentTag := none }]

private def canonSibs (perm₀ perm₁ : TreeBorrowPerm) (p₀ p₁ : Bool) : List BorrowEntry :=
  [{ tag := 2, targetLocal := 0, targetProjection := .nil, perm := perm₀,
     protector := if p₀ then some 1 else none, parentTag := none },
   { tag := 1, targetLocal := 0, targetProjection := .nil, perm := perm₁,
     protector := if p₁ then some 2 else none, parentTag := none }]

private def canonProts2 (p₀ p₁ : Bool) : List Nat :=
  (if p₀ then [1] else []) ++ (if p₁ then [2] else [])

private def canonChain3 (gPerm cPerm rPerm : TreeBorrowPerm) : List BorrowEntry :=
  [{ tag := 3, targetLocal := 0, targetProjection := .nil, perm := gPerm,
     protector := none, parentTag := some 2 },
   { tag := 2, targetLocal := 0, targetProjection := .nil, perm := cPerm,
     protector := none, parentTag := some 1 },
   { tag := 1, targetLocal := 0, targetProjection := .nil, perm := rPerm,
     protector := none, parentTag := none }]

private def canonBranch3 (c₀Perm c₁Perm pPerm : TreeBorrowPerm) : List BorrowEntry :=
  [{ tag := 3, targetLocal := 0, targetProjection := .nil, perm := c₀Perm,
     protector := none, parentTag := some 1 },
   { tag := 2, targetLocal := 0, targetProjection := .nil, perm := c₁Perm,
     protector := none, parentTag := some 1 },
   { tag := 1, targetLocal := 0, targetProjection := .nil, perm := pPerm,
     protector := none, parentTag := none }]

section CanonAccessEq

@[local simp] private theorem applyTreeBorrowTransition_perm_eq (entry : BorrowEntry)
    (out : TreeBorrowTransition) :
    (applyTreeBorrowTransition entry out).perm =
      match out with
      | .transition perm => perm
      | .ub => entry.perm
      | .protectedReservedIM => entry.perm := by
  cases out <;> rfl

@[local simp] private theorem isBorrowProtected_canon1 (perm : TreeBorrowPerm) (p₀ : Bool) :
    isBorrowProtected (canonProts1 p₀)
      { tag := 1, targetLocal := 0, targetProjection := .nil, perm := perm,
        protector := if p₀ then some 1 else none, parentTag := none } = p₀ := by
  cases p₀ <;> rfl

@[local simp] private theorem isBorrowProtected_canon2_0 (perm : TreeBorrowPerm) (pt : Option Nat)
    (p₀ p₁ : Bool) :
    isBorrowProtected (canonProts2 p₀ p₁)
      { tag := 2, targetLocal := 0, targetProjection := .nil, perm := perm,
        protector := if p₀ then some 1 else none, parentTag := pt } = p₀ := by
  cases p₀ <;> cases p₁ <;> rfl

@[local simp] private theorem isBorrowProtected_canon2_1 (perm : TreeBorrowPerm) (pt : Option Nat)
    (p₀ p₁ : Bool) :
    isBorrowProtected (canonProts2 p₀ p₁)
      { tag := 1, targetLocal := 0, targetProjection := .nil, perm := perm,
        protector := if p₁ then some 2 else none, parentTag := pt } = p₁ := by
  cases p₀ <;> cases p₁ <;> rfl

@[local simp] private theorem isBorrowProtected_nil (e : BorrowEntry) :
    isBorrowProtected [] e = false := by
  unfold isBorrowProtected
  cases e.protector <;> rfl

@[local simp] private theorem nat_beq_refl (a : Nat) : Nat.beq a a = true := by
  simp

private theorem borrowEntryOverlapsWrite_nil_eq_true (e : BorrowEntry)
    (hproj : e.targetProjection = .nil) :
    borrowEntryOverlapsWrite e .nil 0 0 = true := by
  unfold borrowEntryOverlapsWrite
  rw [hproj]
  rfl

@[local simp] private theorem borrowEntryOverlapsWrite_mk_nil (tag : Nat) (loc : Local)
    (perm : TreeBorrowPerm) (prot : Option Nat) (pt : Option Nat) :
    borrowEntryOverlapsWrite
      { tag := tag, targetLocal := loc, targetProjection := .nil, perm := perm,
        protector := prot, parentTag := pt } .nil 0 0 = true :=
  rfl

attribute [local simp] annealTableAccessUB annealTableAfterAccess basedAccessTag
  canon1 canonPC canonSibs canonChain3 canonBranch3 hasTreeReadUB borrowEntryReadUB
  freezeTreeBorrowsOnReadAtProj updateBorrowPermOnReadAtProj
  hasProtectedTreeWriteConflict hasProtectedWriteConflict borrowEntryWriteConflicts
  invalidateTreeBorrowsAtProj updateBorrowPermTreeAtProj updateBorrowPermAtProj
  resolveTreeBorrowWriterTag isBorrowDescendantOrSelf isBorrowDescendantOrSelfAux
  treeBorrowChainChildAccessUBAux lookupBorrow length

private theorem singleton_ub_after_eq (kind : TreeBorrowAccessKind) (b₀ : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 2)
    (hloc : b₀.targetLocal = targetLocal)
    (hproj : b₀.targetProjection = .nil) :
    let p₀ := isBorrowProtected activeProtectors b₀
    annealTableAccessUB kind [b₀] activeProtectors targetLocal start.val =
      annealTableAccessUB kind (canon1 b₀.perm p₀) (canonProts1 p₀) 0 start.val ∧
    (annealTableAfterAccess kind [b₀] activeProtectors targetLocal start.val).map
        (fun e => some e.perm) =
      (annealTableAfterAccess kind (canon1 b₀.perm p₀) (canonProts1 p₀) 0 start.val).map
        (fun e => some e.perm) := by
  have hov : borrowEntryOverlapsWrite b₀ .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true b₀ hproj
  dsimp only []
  generalize hpr : isBorrowProtected activeProtectors b₀ = p₀
  rcases start with ⟨_ | _ | _, hlt⟩
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · omega

private theorem parent_child_ub_after_eq (kind : TreeBorrowAccessKind)
    (child parent : BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (start : Fin 2)
    (hneq : child.tag ≠ parent.tag)
    (hcpar : child.parentTag = some parent.tag)
    (hppar : parent.parentTag = none)
    (hcloc : child.targetLocal = targetLocal)
    (hploc : parent.targetLocal = targetLocal)
    (hcproj : child.targetProjection = .nil)
    (hpproj : parent.targetProjection = .nil) :
    let p₀ := isBorrowProtected activeProtectors child
    let p₁ := isBorrowProtected activeProtectors parent
    annealTableAccessUB kind [child, parent] activeProtectors targetLocal start.val =
      annealTableAccessUB kind (canonPC child.perm parent.perm p₀ p₁) (canonProts2 p₀ p₁) 0
        start.val ∧
    (annealTableAfterAccess kind [child, parent] activeProtectors targetLocal start.val).map
        (fun e => some e.perm) =
      (annealTableAfterAccess kind (canonPC child.perm parent.perm p₀ p₁) (canonProts2 p₀ p₁) 0
        start.val).map (fun e => some e.perm) := by
  have hbeq_cp : Nat.beq child.tag parent.tag = false := nat_beq_eq_false_of_ne hneq
  have hbeq_pc : Nat.beq parent.tag child.tag = false := nat_beq_eq_false_of_ne hneq.symm
  have hcov : borrowEntryOverlapsWrite child .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true child hcproj
  have hpov : borrowEntryOverlapsWrite parent .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true parent hpproj
  dsimp only []
  generalize hpr₀ : isBorrowProtected activeProtectors child = p₀
  generalize hpr₁ : isBorrowProtected activeProtectors parent = p₁
  rcases start with ⟨_ | _ | _, hlt⟩
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · omega

private theorem siblings_ub_after_eq (kind : TreeBorrowAccessKind)
    (b₀ b₁ : BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (start : Fin 3)
    (hneq : b₀.tag ≠ b₁.tag)
    (hp₀ : b₀.parentTag = none)
    (hp₁ : b₁.parentTag = none)
    (hloc₀ : b₀.targetLocal = targetLocal)
    (hloc₁ : b₁.targetLocal = targetLocal)
    (hproj₀ : b₀.targetProjection = .nil)
    (hproj₁ : b₁.targetProjection = .nil) :
    let p₀ := isBorrowProtected activeProtectors b₀
    let p₁ := isBorrowProtected activeProtectors b₁
    annealTableAccessUB kind [b₀, b₁] activeProtectors targetLocal start.val =
      annealTableAccessUB kind (canonSibs b₀.perm b₁.perm p₀ p₁) (canonProts2 p₀ p₁) 0
        start.val ∧
    (annealTableAfterAccess kind [b₀, b₁] activeProtectors targetLocal start.val).map
        (fun e => some e.perm) =
      (annealTableAfterAccess kind (canonSibs b₀.perm b₁.perm p₀ p₁) (canonProts2 p₀ p₁) 0
        start.val).map (fun e => some e.perm) := by
  have hbeq₀₁ : Nat.beq b₀.tag b₁.tag = false := nat_beq_eq_false_of_ne hneq
  have hbeq₁₀ : Nat.beq b₁.tag b₀.tag = false := nat_beq_eq_false_of_ne hneq.symm
  have hov₀ : borrowEntryOverlapsWrite b₀ .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true b₀ hproj₀
  have hov₁ : borrowEntryOverlapsWrite b₁ .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true b₁ hproj₁
  dsimp only []
  generalize hpr₀ : isBorrowProtected activeProtectors b₀ = p₀
  generalize hpr₁ : isBorrowProtected activeProtectors b₁ = p₁
  rcases start with ⟨_ | _ | _ | _, hlt⟩
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · omega

private theorem chain3_ub_after_eq (kind : TreeBorrowAccessKind)
    (g c r : BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (start : Fin 4)
    (hneq_gc : g.tag ≠ c.tag) (hneq_gr : g.tag ≠ r.tag) (hneq_cr : c.tag ≠ r.tag)
    (hgpar : g.parentTag = some c.tag)
    (hcpar : c.parentTag = some r.tag)
    (hrpar : r.parentTag = none)
    (hgloc : g.targetLocal = targetLocal)
    (hcloc : c.targetLocal = targetLocal)
    (hrloc : r.targetLocal = targetLocal)
    (hgproj : g.targetProjection = .nil)
    (hcproj : c.targetProjection = .nil)
    (hrproj : r.targetProjection = .nil)
    (hgprot : isBorrowProtected activeProtectors g = false)
    (hcprot : isBorrowProtected activeProtectors c = false)
    (hrprot : isBorrowProtected activeProtectors r = false) :
    annealTableAccessUB kind [g, c, r] activeProtectors targetLocal start.val =
      annealTableAccessUB kind (canonChain3 g.perm c.perm r.perm) [] 0 start.val ∧
    (annealTableAfterAccess kind [g, c, r] activeProtectors targetLocal start.val).map
        (fun e => some e.perm) =
      (annealTableAfterAccess kind (canonChain3 g.perm c.perm r.perm) [] 0 start.val).map
        (fun e => some e.perm) := by
  have hbeq_gc : Nat.beq g.tag c.tag = false := nat_beq_eq_false_of_ne hneq_gc
  have hbeq_cg : Nat.beq c.tag g.tag = false := nat_beq_eq_false_of_ne hneq_gc.symm
  have hbeq_gr : Nat.beq g.tag r.tag = false := nat_beq_eq_false_of_ne hneq_gr
  have hbeq_rg : Nat.beq r.tag g.tag = false := nat_beq_eq_false_of_ne hneq_gr.symm
  have hbeq_cr : Nat.beq c.tag r.tag = false := nat_beq_eq_false_of_ne hneq_cr
  have hbeq_rc : Nat.beq r.tag c.tag = false := nat_beq_eq_false_of_ne hneq_cr.symm
  have hgov : borrowEntryOverlapsWrite g .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true g hgproj
  have hcov : borrowEntryOverlapsWrite c .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true c hcproj
  have hrov : borrowEntryOverlapsWrite r .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true r hrproj
  rcases start with ⟨_ | _ | _ | _ | _, hlt⟩
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · omega

private theorem branch3_ub_after_eq (kind : TreeBorrowAccessKind)
    (c₀ c₁ p : BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (start : Fin 4)
    (hneq₀₁ : c₀.tag ≠ c₁.tag) (hneq₀p : c₀.tag ≠ p.tag) (hneq₁p : c₁.tag ≠ p.tag)
    (hc₀par : c₀.parentTag = some p.tag)
    (hc₁par : c₁.parentTag = some p.tag)
    (hppar : p.parentTag = none)
    (hloc₀ : c₀.targetLocal = targetLocal)
    (hloc₁ : c₁.targetLocal = targetLocal)
    (hlocp : p.targetLocal = targetLocal)
    (hproj₀ : c₀.targetProjection = .nil)
    (hproj₁ : c₁.targetProjection = .nil)
    (hprojp : p.targetProjection = .nil)
    (hc₀prot : isBorrowProtected activeProtectors c₀ = false)
    (hc₁prot : isBorrowProtected activeProtectors c₁ = false)
    (hpprot : isBorrowProtected activeProtectors p = false) :
    annealTableAccessUB kind [c₀, c₁, p] activeProtectors targetLocal start.val =
      annealTableAccessUB kind (canonBranch3 c₀.perm c₁.perm p.perm) [] 0 start.val ∧
    (annealTableAfterAccess kind [c₀, c₁, p] activeProtectors targetLocal start.val).map
        (fun e => some e.perm) =
      (annealTableAfterAccess kind (canonBranch3 c₀.perm c₁.perm p.perm) [] 0 start.val).map
        (fun e => some e.perm) := by
  have hbeq₀₁ : Nat.beq c₀.tag c₁.tag = false := nat_beq_eq_false_of_ne hneq₀₁
  have hbeq₁₀ : Nat.beq c₁.tag c₀.tag = false := nat_beq_eq_false_of_ne hneq₀₁.symm
  have hbeq₀p : Nat.beq c₀.tag p.tag = false := nat_beq_eq_false_of_ne hneq₀p
  have hbeqp₀ : Nat.beq p.tag c₀.tag = false := nat_beq_eq_false_of_ne hneq₀p.symm
  have hbeq₁p : Nat.beq c₁.tag p.tag = false := nat_beq_eq_false_of_ne hneq₁p
  have hbeqp₁ : Nat.beq p.tag c₁.tag = false := nat_beq_eq_false_of_ne hneq₁p.symm
  have hov₀ : borrowEntryOverlapsWrite c₀ .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true c₀ hproj₀
  have hov₁ : borrowEntryOverlapsWrite c₁ .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true c₁ hproj₁
  have hovp : borrowEntryOverlapsWrite p .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true p hprojp
  rcases start with ⟨_ | _ | _ | _ | _, hlt⟩
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · omega

end CanonAccessEq

private theorem borrowIndexOfTag_map_of_preserve_tag
    (borrows : List BorrowEntry) (f : BorrowEntry → BorrowEntry)
    (htag : ∀ e, (f e).tag = e.tag) (pt : Nat) :
    borrowIndexOfTag (borrows.map f) pt = borrowIndexOfTag borrows pt := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, borrowIndexOfTag, htag hd, ih]

private theorem annealTableAfterAccess_preserves_shape
    (kind : TreeBorrowAccessKind) (borrows : List BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Nat) :
    let borrows' := annealTableAfterAccess kind borrows activeProtectors targetLocal start
    borrows'.length = borrows.length ∧
    borrows'.map BorrowEntry.tag = borrows.map BorrowEntry.tag ∧
    basedTraversalTree borrows' = basedTraversalTree borrows ∧
    protectedIndices borrows' activeProtectors = protectedIndices borrows activeProtectors := by
  dsimp only []
  have hex : ∃ f : BorrowEntry → BorrowEntry,
      annealTableAfterAccess kind borrows activeProtectors targetLocal start = borrows.map f ∧
      ∀ e, (f e).tag = e.tag ∧ (f e).parentTag = e.parentTag ∧ (f e).protector = e.protector := by
    cases kind
    · refine ⟨fun e => updateBorrowPermOnReadAtProj borrows e targetLocal
          (basedAccessTag borrows start) .nil 0 0 activeProtectors,
        freezeTreeBorrowsOnReadAtProj_eq_map ..,
        fun e => updateBorrowPermOnReadAtProj_preserves_tag_parent_prot borrows e targetLocal
          (basedAccessTag borrows start) .nil 0 0 activeProtectors⟩
    · refine ⟨fun e => updateBorrowPermTreeAtProj borrows e targetLocal
          (basedAccessTag borrows start) .nil 0 0,
        invalidateTreeBorrowsAtProj_eq_map ..,
        fun e => updateBorrowPermTreeAtProj_preserves_tag_parent_prot borrows e targetLocal
          (basedAccessTag borrows start) .nil 0 0⟩
  obtain ⟨f, hmap, hf⟩ := hex
  rw [hmap]
  have hlen : (borrows.map f).length = borrows.length := List.length_map f
  have htags : (borrows.map f).map BorrowEntry.tag = borrows.map BorrowEntry.tag :=
    map_tag_eq_of_preserve_tag borrows f (fun e => (hf e).1)
  have hidx_eq : ∀ pt, borrowIndexOfTag (borrows.map f) pt = borrowIndexOfTag borrows pt :=
    borrowIndexOfTag_map_of_preserve_tag borrows f (fun e => (hf e).1)
  have hbpi : ∀ e, basedParentIndex (borrows.map f) (f e) = basedParentIndex borrows e := by
    intro e
    simp only [basedParentIndex, (hf e).2.1, List.length_map]
    cases e.parentTag with
    | none => rfl
    | some pt => dsimp only []; rw [hidx_eq pt]
  have hbch : ∀ idx, basedChildren (borrows.map f) idx = basedChildren borrows idx := by
    intro idx
    unfold basedChildren
    rw [List.length_map]
    apply List.filter_congr
    intro j hj
    have hjlt : j < borrows.length := List.mem_range.mp hj
    simp only [List.getElem?_eq_getElem hjlt,
      List.getElem?_eq_getElem (by simpa using hjlt : j < (borrows.map f).length),
      List.getElem_map, hbpi]
  have htopo : basedTraversalTree (borrows.map f) = basedTraversalTree borrows := by
    unfold basedTraversalTree
    rw [List.length_map, hbch]
    congr 1
    congr 1
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      have hi : i < borrows.length := by simpa using h₂
      simp [hbpi, hbch]
  have hprot : protectedIndices (borrows.map f) activeProtectors =
      protectedIndices borrows activeProtectors := by
    unfold protectedIndices
    rw [List.length_map]
    apply List.filter_congr
    intro i hi
    have hilt : i < borrows.length := List.mem_range.mp hi
    simp only [List.getElem?_eq_getElem hilt,
      List.getElem?_eq_getElem (by simpa using hilt : i < (borrows.map f).length),
      List.getElem_map, isBorrowProtected, (hf borrows[i]).2.2]
  exact ⟨hlen, htags, htopo, hprot⟩

section CoreDecidable

private local instance : DecidableEq TreeBorrowPerm := fun a b =>
  if h : annealPermToMiri a = annealPermToMiri b then
    isTrue (annealPermToMiri_injective h)
  else
    isFalse (fun hab => h (congrArg annealPermToMiri hab))

private theorem singleton_canon_core (kind : TreeBorrowAccessKind) (perm : TreeBorrowPerm)
    (p₀ : Bool) (start : Fin 2) :
    let nres := (mkNormalTree1 perm p₀).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    (nres.status = .Completed ↔
      annealTableAccessUB kind (canon1 perm p₀) (canonProts1 p₀) 0 start.val = false) ∧
    (nres.status = .Completed →
      nres.tree.topology = (mkNormalTree1 perm p₀).topology ∧
      nres.tree.protectedNodes = (mkNormalTree1 perm p₀).protectedNodes ∧
      normalTreePerms nres.tree 1 =
        (annealTableAfterAccess kind (canon1 perm p₀) (canonProts1 p₀) 0 start.val).map
          (fun e => some e.perm) ∧
      (nres.tree.stateAt 1).map (fun st => st.permission) = some .Unique) := by
  rcases start with ⟨_ | _ | _, hlt⟩
  · dsimp only []
    cases kind <;> (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases p₀ <;> decide
  · dsimp only []
    cases kind <;> (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases p₀ <;> decide
  · omega

private abbrev pcCoreGoal (kind : TreeBorrowAccessKind) (cPerm pPerm : TreeBorrowPerm)
    (p₀ p₁ : Bool) (startVal : Nat) : Prop :=
  let nres := (mkNormalTreeParentChild cPerm pPerm p₀ p₁).performAccess startVal
    (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
  (nres.status = .Completed ↔
    annealTableAccessUB kind (canonPC cPerm pPerm p₀ p₁) (canonProts2 p₀ p₁) 0 startVal = false) ∧
  (nres.status = .Completed →
    nres.tree.topology = (mkNormalTreeParentChild cPerm pPerm p₀ p₁).topology ∧
    nres.tree.protectedNodes = (mkNormalTreeParentChild cPerm pPerm p₀ p₁).protectedNodes ∧
    normalTreePerms nres.tree 2 =
      (annealTableAfterAccess kind (canonPC cPerm pPerm p₀ p₁) (canonProts2 p₀ p₁) 0 startVal).map
        (fun e => some e.perm) ∧
    (nres.tree.stateAt 2).map (fun st => st.permission) = some .Unique)

private theorem pc_canon_read_0 (cPerm pPerm : TreeBorrowPerm) (p₀ p₁ : Bool) :
    pcCoreGoal .read cPerm pPerm p₀ p₁ 0 := by
  (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases p₀ <;> cases p₁ <;> decide

private theorem pc_canon_read_1 (cPerm pPerm : TreeBorrowPerm) (p₀ p₁ : Bool) :
    pcCoreGoal .read cPerm pPerm p₀ p₁ 1 := by
  (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases p₀ <;> cases p₁ <;> decide

private theorem pc_canon_write_0 (cPerm pPerm : TreeBorrowPerm) (p₀ p₁ : Bool) :
    pcCoreGoal .write cPerm pPerm p₀ p₁ 0 := by
  (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases p₀ <;> cases p₁ <;> decide

private theorem pc_canon_write_1 (cPerm pPerm : TreeBorrowPerm) (p₀ p₁ : Bool) :
    pcCoreGoal .write cPerm pPerm p₀ p₁ 1 := by
  (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases p₀ <;> cases p₁ <;> decide

private abbrev sibCoreGoal (kind : TreeBorrowAccessKind) (perm₀ perm₁ : TreeBorrowPerm)
    (p₀ p₁ : Bool) (startVal : Nat) : Prop :=
  let nres := (mkNormalTreeSiblings perm₀ perm₁ p₀ p₁).performAccess startVal
    (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
  (nres.status = .Completed ↔
    annealTableAccessUB kind (canonSibs perm₀ perm₁ p₀ p₁) (canonProts2 p₀ p₁) 0 startVal =
      false) ∧
  (nres.status = .Completed →
    nres.tree.topology = (mkNormalTreeSiblings perm₀ perm₁ p₀ p₁).topology ∧
    nres.tree.protectedNodes = (mkNormalTreeSiblings perm₀ perm₁ p₀ p₁).protectedNodes ∧
    normalTreePerms nres.tree 2 =
      (annealTableAfterAccess kind (canonSibs perm₀ perm₁ p₀ p₁) (canonProts2 p₀ p₁) 0
        startVal).map (fun e => some e.perm) ∧
    (nres.tree.stateAt 2).map (fun st => st.permission) = some .Unique)

private theorem sib_canon_read_0 (perm₀ perm₁ : TreeBorrowPerm) (p₀ p₁ : Bool) :
    sibCoreGoal .read perm₀ perm₁ p₀ p₁ 0 := by
  (rcases perm₀ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases perm₁ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases p₀ <;> cases p₁ <;> decide

private theorem sib_canon_read_1 (perm₀ perm₁ : TreeBorrowPerm) (p₀ p₁ : Bool) :
    sibCoreGoal .read perm₀ perm₁ p₀ p₁ 1 := by
  (rcases perm₀ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases perm₁ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases p₀ <;> cases p₁ <;> decide

private theorem sib_canon_read_2 (perm₀ perm₁ : TreeBorrowPerm) (p₀ p₁ : Bool) :
    sibCoreGoal .read perm₀ perm₁ p₀ p₁ 2 := by
  (rcases perm₀ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases perm₁ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases p₀ <;> cases p₁ <;> decide

private theorem sib_canon_write_0 (perm₀ perm₁ : TreeBorrowPerm) (p₀ p₁ : Bool) :
    sibCoreGoal .write perm₀ perm₁ p₀ p₁ 0 := by
  (rcases perm₀ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases perm₁ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases p₀ <;> cases p₁ <;> decide

private theorem sib_canon_write_1 (perm₀ perm₁ : TreeBorrowPerm) (p₀ p₁ : Bool) :
    sibCoreGoal .write perm₀ perm₁ p₀ p₁ 1 := by
  (rcases perm₀ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases perm₁ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases p₀ <;> cases p₁ <;> decide

private theorem sib_canon_write_2 (perm₀ perm₁ : TreeBorrowPerm) (p₀ p₁ : Bool) :
    sibCoreGoal .write perm₀ perm₁ p₀ p₁ 2 := by
  (rcases perm₀ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases perm₁ with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases p₀ <;> cases p₁ <;> decide

/-- Ancestor-descendant permission invariant along a parent-child pair
`(descPerm, ancPerm)` required for Miri's `SkipSelfAndChildren` foreign-subtree
pruning (`LocationState.skipIfKnownNoop`) to be observational-equivalent to
Anneal's flat table scan:
1. a `.disabled` ancestor has no non-`.disabled` descendant;
2. a `.frozen` ancestor has no `.unique` descendant. -/
def treeBorrowsAncestorInv (descPerm ancPerm : TreeBorrowPerm) : Bool :=
  (if ancPerm == .disabled then descPerm == .disabled else true) &&
  (if ancPerm == .frozen then descPerm != .unique else true)

/-- Ancestor-descendant permission invariant for a 3-level reborrow chain
`[g, c, r]` (`g` child of `c`, `c` child of `r`). -/
def treeBorrowsChain3Inv (gPerm cPerm rPerm : TreeBorrowPerm) : Bool :=
  treeBorrowsAncestorInv gPerm cPerm &&
  treeBorrowsAncestorInv gPerm rPerm &&
  treeBorrowsAncestorInv cPerm rPerm

/-- Ancestor-descendant permission invariant for a 3-node branching borrow tree
`[c₀, c₁, p]` (`c₀` and `c₁` children of `p`). -/
def treeBorrowsBranch3Inv (c₀Perm c₁Perm pPerm : TreeBorrowPerm) : Bool :=
  treeBorrowsAncestorInv c₀Perm pPerm &&
  treeBorrowsAncestorInv c₁Perm pPerm

private abbrev chain3CoreGoal (kind : TreeBorrowAccessKind)
    (gPerm cPerm rPerm : TreeBorrowPerm) (startVal : Nat) : Prop :=
  treeBorrowsChain3Inv gPerm cPerm rPerm = true →
  let nres := (mkNormalTreeChain3 gPerm cPerm rPerm).performAccess startVal
    (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
  (nres.status = .Completed ↔
    annealTableAccessUB kind (canonChain3 gPerm cPerm rPerm) [] 0 startVal = false) ∧
  (nres.status = .Completed →
    nres.tree.topology = (mkNormalTreeChain3 gPerm cPerm rPerm).topology ∧
    nres.tree.protectedNodes = (mkNormalTreeChain3 gPerm cPerm rPerm).protectedNodes ∧
    normalTreePerms nres.tree 3 =
      (annealTableAfterAccess kind (canonChain3 gPerm cPerm rPerm) [] 0 startVal).map
        (fun e => some e.perm) ∧
    (nres.tree.stateAt 3).map (fun st => st.permission) = some .Unique)

private theorem chain3_canon_read_0 (gPerm cPerm rPerm : TreeBorrowPerm) :
    chain3CoreGoal .read gPerm cPerm rPerm 0 := by
  (rcases gPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases rPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem chain3_canon_read_1 (gPerm cPerm rPerm : TreeBorrowPerm) :
    chain3CoreGoal .read gPerm cPerm rPerm 1 := by
  (rcases gPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases rPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem chain3_canon_read_2 (gPerm cPerm rPerm : TreeBorrowPerm) :
    chain3CoreGoal .read gPerm cPerm rPerm 2 := by
  (rcases gPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases rPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem chain3_canon_read_3 (gPerm cPerm rPerm : TreeBorrowPerm) :
    chain3CoreGoal .read gPerm cPerm rPerm 3 := by
  (rcases gPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases rPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem chain3_canon_write_0 (gPerm cPerm rPerm : TreeBorrowPerm) :
    chain3CoreGoal .write gPerm cPerm rPerm 0 := by
  (rcases gPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases rPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem chain3_canon_write_1 (gPerm cPerm rPerm : TreeBorrowPerm) :
    chain3CoreGoal .write gPerm cPerm rPerm 1 := by
  (rcases gPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases rPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem chain3_canon_write_2 (gPerm cPerm rPerm : TreeBorrowPerm) :
    chain3CoreGoal .write gPerm cPerm rPerm 2 := by
  (rcases gPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases rPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem chain3_canon_write_3 (gPerm cPerm rPerm : TreeBorrowPerm) :
    chain3CoreGoal .write gPerm cPerm rPerm 3 := by
  (rcases gPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases cPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases rPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem chain3_canon_core (kind : TreeBorrowAccessKind)
    (gPerm cPerm rPerm : TreeBorrowPerm) (start : Fin 4) :
    chain3CoreGoal kind gPerm cPerm rPerm start.val := by
  rcases start with ⟨_ | _ | _ | _ | _, hlt⟩
  · cases kind
    · exact chain3_canon_read_0 gPerm cPerm rPerm
    · exact chain3_canon_write_0 gPerm cPerm rPerm
  · cases kind
    · exact chain3_canon_read_1 gPerm cPerm rPerm
    · exact chain3_canon_write_1 gPerm cPerm rPerm
  · cases kind
    · exact chain3_canon_read_2 gPerm cPerm rPerm
    · exact chain3_canon_write_2 gPerm cPerm rPerm
  · cases kind
    · exact chain3_canon_read_3 gPerm cPerm rPerm
    · exact chain3_canon_write_3 gPerm cPerm rPerm
  · omega

private abbrev branch3CoreGoal (kind : TreeBorrowAccessKind)
    (c₀Perm c₁Perm pPerm : TreeBorrowPerm) (startVal : Nat) : Prop :=
  treeBorrowsBranch3Inv c₀Perm c₁Perm pPerm = true →
  let nres := (mkNormalTreeBranch3 c₀Perm c₁Perm pPerm).performAccess startVal
    (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
  (nres.status = .Completed ↔
    annealTableAccessUB kind (canonBranch3 c₀Perm c₁Perm pPerm) [] 0 startVal = false) ∧
  (nres.status = .Completed →
    nres.tree.topology = (mkNormalTreeBranch3 c₀Perm c₁Perm pPerm).topology ∧
    nres.tree.protectedNodes = (mkNormalTreeBranch3 c₀Perm c₁Perm pPerm).protectedNodes ∧
    normalTreePerms nres.tree 3 =
      (annealTableAfterAccess kind (canonBranch3 c₀Perm c₁Perm pPerm) [] 0 startVal).map
        (fun e => some e.perm) ∧
    (nres.tree.stateAt 3).map (fun st => st.permission) = some .Unique)

private theorem branch3_canon_read_0 (c₀Perm c₁Perm pPerm : TreeBorrowPerm) :
    branch3CoreGoal .read c₀Perm c₁Perm pPerm 0 := by
  (rcases c₀Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases c₁Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem branch3_canon_read_1 (c₀Perm c₁Perm pPerm : TreeBorrowPerm) :
    branch3CoreGoal .read c₀Perm c₁Perm pPerm 1 := by
  (rcases c₀Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases c₁Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem branch3_canon_read_2 (c₀Perm c₁Perm pPerm : TreeBorrowPerm) :
    branch3CoreGoal .read c₀Perm c₁Perm pPerm 2 := by
  (rcases c₀Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases c₁Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem branch3_canon_read_3 (c₀Perm c₁Perm pPerm : TreeBorrowPerm) :
    branch3CoreGoal .read c₀Perm c₁Perm pPerm 3 := by
  (rcases c₀Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases c₁Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem branch3_canon_write_0 (c₀Perm c₁Perm pPerm : TreeBorrowPerm) :
    branch3CoreGoal .write c₀Perm c₁Perm pPerm 0 := by
  (rcases c₀Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases c₁Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem branch3_canon_write_1 (c₀Perm c₁Perm pPerm : TreeBorrowPerm) :
    branch3CoreGoal .write c₀Perm c₁Perm pPerm 1 := by
  (rcases c₀Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases c₁Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem branch3_canon_write_2 (c₀Perm c₁Perm pPerm : TreeBorrowPerm) :
    branch3CoreGoal .write c₀Perm c₁Perm pPerm 2 := by
  (rcases c₀Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases c₁Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem branch3_canon_write_3 (c₀Perm c₁Perm pPerm : TreeBorrowPerm) :
    branch3CoreGoal .write c₀Perm c₁Perm pPerm 3 := by
  (rcases c₀Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases c₁Perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases pPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private theorem branch3_canon_core (kind : TreeBorrowAccessKind)
    (c₀Perm c₁Perm pPerm : TreeBorrowPerm) (start : Fin 4) :
    branch3CoreGoal kind c₀Perm c₁Perm pPerm start.val := by
  rcases start with ⟨_ | _ | _ | _ | _, hlt⟩
  · cases kind
    · exact branch3_canon_read_0 c₀Perm c₁Perm pPerm
    · exact branch3_canon_write_0 c₀Perm c₁Perm pPerm
  · cases kind
    · exact branch3_canon_read_1 c₀Perm c₁Perm pPerm
    · exact branch3_canon_write_1 c₀Perm c₁Perm pPerm
  · cases kind
    · exact branch3_canon_read_2 c₀Perm c₁Perm pPerm
    · exact branch3_canon_write_2 c₀Perm c₁Perm pPerm
  · cases kind
    · exact branch3_canon_read_3 c₀Perm c₁Perm pPerm
    · exact branch3_canon_write_3 c₀Perm c₁Perm pPerm
  · omega

end CoreDecidable

/-- **`basedNormalTree_performAccess_singleton_simulation`**: for any whole-local
root `BorrowEntry` `b₀` (`b₀.parentTag = none`, `b₀.targetProjection = .nil`),
any `activeProtectors` list, both access kinds (`.read` / `.write`), and both
starting nodes (`0` = access through `b₀.tag`, `1` = direct local access),
Miri's `NormalTreeState.performAccess` on `basedNormalTree [b₀] activeProtectors`
completes iff `annealTableAccessUB` is `false`, and whenever it completes,
establishes `TreeBorrowsRel` directly between `annealTableAfterAccess` and
`nres.tree`. -/
theorem basedNormalTree_performAccess_singleton_simulation
    (kind : TreeBorrowAccessKind) (b₀ : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 2)
    (hp₀ : b₀.parentTag = none) (hloc : b₀.targetLocal = targetLocal)
    (hproj : b₀.targetProjection = .nil) :
    let nres := (basedNormalTree [b₀] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [b₀] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [b₀] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed → TreeBorrowsRel borrows' activeProtectors nres.tree) := by
  dsimp only []
  have hnt := basedNormalTree_singleton_eq b₀ activeProtectors hp₀
  obtain ⟨hub_eq, hafter_eq⟩ :=
    singleton_ub_after_eq kind b₀ activeProtectors targetLocal start hloc hproj
  obtain ⟨hlen, htags, htopo, hprot⟩ :=
    annealTableAfterAccess_preserves_shape kind [b₀] activeProtectors targetLocal start.val
  obtain ⟨hcore_st, hcore_rel⟩ :=
    singleton_canon_core kind b₀.perm (isBorrowProtected activeProtectors b₀) start
  rw [hnt, hub_eq]
  refine ⟨hcore_st, fun hc => ?_⟩
  obtain ⟨ht_eq, hp_eq, hperms_eq, hbase_eq⟩ := hcore_rel hc
  have hnt_fields := congrArg (fun t => (t.topology, t.protectedNodes)) hnt
  injection hnt_fields with hnt_topo hnt_prot
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htopo, ht_eq, ← hnt_topo]; rfl
  · rw [htags]; simp
  · rw [hlen]; dsimp only [List.length_cons, List.length_nil]; rw [hperms_eq, ← hafter_eq]
  · rw [hlen]; exact hbase_eq
  · rw [hprot, hp_eq, ← hnt_prot]; rfl

/-- **`basedNormalTree_performAccess_parent_child_simulation`** (certifying
`I-10` & `I-11` operational parent-child traversal): for any whole-local
parent-child pair `[child, parent]` (`child.tag ≠ parent.tag`,
`child.parentTag = some parent.tag`, `parent.parentTag = none`), any
`activeProtectors` list, both access kinds (`.read` / `.write`), and both
pointer starting nodes (`0` = access through `child.tag`, `1` = access through
`parent.tag`), Miri's `NormalTreeState.performAccess` on
`basedNormalTree [child, parent] activeProtectors` completes iff
`annealTableAccessUB` is `false`, and whenever it completes, establishes
`TreeBorrowsRel` directly between `annealTableAfterAccess` and `nres.tree`. -/
theorem basedNormalTree_performAccess_parent_child_simulation
    (kind : TreeBorrowAccessKind) (child parent : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 2)
    (hneq : child.tag ≠ parent.tag)
    (hcpar : child.parentTag = some parent.tag)
    (hppar : parent.parentTag = none)
    (hcloc : child.targetLocal = targetLocal)
    (hploc : parent.targetLocal = targetLocal)
    (hcproj : child.targetProjection = .nil)
    (hpproj : parent.targetProjection = .nil) :
    let nres := (basedNormalTree [child, parent] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [child, parent] activeProtectors targetLocal
      start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [child, parent] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed → TreeBorrowsRel borrows' activeProtectors nres.tree) := by
  dsimp only []
  have hnt := basedNormalTree_parent_child_eq child parent activeProtectors hneq hcpar hppar
  obtain ⟨hub_eq, hafter_eq⟩ := parent_child_ub_after_eq kind child parent activeProtectors
    targetLocal start hneq hcpar hppar hcloc hploc hcproj hpproj
  obtain ⟨hlen, htags, htopo, hprot⟩ := annealTableAfterAccess_preserves_shape kind
    [child, parent] activeProtectors targetLocal start.val
  have hcore : pcCoreGoal kind child.perm parent.perm
      (isBorrowProtected activeProtectors child)
      (isBorrowProtected activeProtectors parent) start.val := by
    rcases start with ⟨_ | _ | _, hlt⟩
    · cases kind
      · exact pc_canon_read_0 ..
      · exact pc_canon_write_0 ..
    · cases kind
      · exact pc_canon_read_1 ..
      · exact pc_canon_write_1 ..
    · omega
  obtain ⟨hcore_st, hcore_rel⟩ := hcore
  rw [hnt, hub_eq]
  refine ⟨hcore_st, fun hc => ?_⟩
  obtain ⟨ht_eq, hp_eq, hperms_eq, hbase_eq⟩ := hcore_rel hc
  have hnt_fields := congrArg (fun t => (t.topology, t.protectedNodes)) hnt
  injection hnt_fields with hnt_topo hnt_prot
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htopo, ht_eq, ← hnt_topo]; rfl
  · rw [htags]; simp [hneq]
  · rw [hlen]; dsimp only [List.length_cons, List.length_nil]; rw [hperms_eq, ← hafter_eq]
  · rw [hlen]; exact hbase_eq
  · rw [hprot, hp_eq, ← hnt_prot]; rfl

/-- **`basedNormalTree_performAccess_siblings_simulation`**: for any whole-local
sibling pair `[b₀, b₁]` (`b₀.tag ≠ b₁.tag`, `b₀.parentTag = none`,
`b₁.parentTag = none`), any `activeProtectors` list, both access kinds (`.read`
/ `.write`), and all three starting nodes (`0` = access through `b₀.tag`, `1` =
access through `b₁.tag`, `2` = direct local access), Miri's
`NormalTreeState.performAccess` on `basedNormalTree [b₀, b₁] activeProtectors`
completes iff `annealTableAccessUB` is `false`, and whenever it completes,
establishes `TreeBorrowsRel` directly between `annealTableAfterAccess` and
`nres.tree`. -/
theorem basedNormalTree_performAccess_siblings_simulation
    (kind : TreeBorrowAccessKind) (b₀ b₁ : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 3)
    (hneq : b₀.tag ≠ b₁.tag)
    (hp₀ : b₀.parentTag = none)
    (hp₁ : b₁.parentTag = none)
    (hloc₀ : b₀.targetLocal = targetLocal)
    (hloc₁ : b₁.targetLocal = targetLocal)
    (hproj₀ : b₀.targetProjection = .nil)
    (hproj₁ : b₁.targetProjection = .nil) :
    let nres := (basedNormalTree [b₀, b₁] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [b₀, b₁] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [b₀, b₁] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed → TreeBorrowsRel borrows' activeProtectors nres.tree) := by
  dsimp only []
  have hnt := basedNormalTree_siblings_eq b₀ b₁ activeProtectors hp₀ hp₁
  obtain ⟨hub_eq, hafter_eq⟩ := siblings_ub_after_eq kind b₀ b₁ activeProtectors
    targetLocal start hneq hp₀ hp₁ hloc₀ hloc₁ hproj₀ hproj₁
  obtain ⟨hlen, htags, htopo, hprot⟩ := annealTableAfterAccess_preserves_shape kind
    [b₀, b₁] activeProtectors targetLocal start.val
  have hcore : sibCoreGoal kind b₀.perm b₁.perm
      (isBorrowProtected activeProtectors b₀)
      (isBorrowProtected activeProtectors b₁) start.val := by
    rcases start with ⟨_ | _ | _ | _, hlt⟩
    · cases kind
      · exact sib_canon_read_0 ..
      · exact sib_canon_write_0 ..
    · cases kind
      · exact sib_canon_read_1 ..
      · exact sib_canon_write_1 ..
    · cases kind
      · exact sib_canon_read_2 ..
      · exact sib_canon_write_2 ..
    · omega
  obtain ⟨hcore_st, hcore_rel⟩ := hcore
  rw [hnt, hub_eq]
  refine ⟨hcore_st, fun hc => ?_⟩
  obtain ⟨ht_eq, hp_eq, hperms_eq, hbase_eq⟩ := hcore_rel hc
  have hnt_fields := congrArg (fun t => (t.topology, t.protectedNodes)) hnt
  injection hnt_fields with hnt_topo hnt_prot
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htopo, ht_eq, ← hnt_topo]; rfl
  · rw [htags]; simp [hneq]
  · rw [hlen]; dsimp only [List.length_cons, List.length_nil]; rw [hperms_eq, ← hafter_eq]
  · rw [hlen]; exact hbase_eq
  · rw [hprot, hp_eq, ← hnt_prot]; rfl

/-- **`basedNormalTree_performAccess_three_level_chain_simulation`** (certifying
`I-10` multi-level ancestor/descendant traversal): for any whole-local 3-level
reborrow chain `[g, c, r]` (`g.parentTag = some c.tag`, `c.parentTag = some r.tag`,
`r.parentTag = none`, distinct tags, unprotected) satisfying Miri's
ancestor-descendant permission invariant `treeBorrowsChain3Inv`, both access
kinds (`.read` / `.write`), and all four starting nodes (`0` = grandchild `g`,
`1` = middle child `c`, `2` = root borrow `r`, `3` = direct local access),
Miri's `NormalTreeState.performAccess` on
`basedNormalTree [g, c, r] activeProtectors` completes iff
`annealTableAccessUB` is `false`, and whenever it completes, establishes
`TreeBorrowsRel` directly between `annealTableAfterAccess` and `nres.tree`. -/
theorem basedNormalTree_performAccess_three_level_chain_simulation
    (kind : TreeBorrowAccessKind) (g c r : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 4)
    (hneq_gc : g.tag ≠ c.tag) (hneq_gr : g.tag ≠ r.tag) (hneq_cr : c.tag ≠ r.tag)
    (hgpar : g.parentTag = some c.tag)
    (hcpar : c.parentTag = some r.tag)
    (hrpar : r.parentTag = none)
    (hgloc : g.targetLocal = targetLocal)
    (hcloc : c.targetLocal = targetLocal)
    (hrloc : r.targetLocal = targetLocal)
    (hgproj : g.targetProjection = .nil)
    (hcproj : c.targetProjection = .nil)
    (hrproj : r.targetProjection = .nil)
    (hgprot : isBorrowProtected activeProtectors g = false)
    (hcprot : isBorrowProtected activeProtectors c = false)
    (hrprot : isBorrowProtected activeProtectors r = false)
    (hinv : treeBorrowsChain3Inv g.perm c.perm r.perm = true) :
    let nres := (basedNormalTree [g, c, r] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [g, c, r] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [g, c, r] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed → TreeBorrowsRel borrows' activeProtectors nres.tree) := by
  dsimp only []
  have hnt := basedNormalTree_chain3_eq g c r activeProtectors hneq_gc hneq_gr hneq_cr
    hgpar hcpar hrpar hgprot hcprot hrprot
  obtain ⟨hub_eq, hafter_eq⟩ := chain3_ub_after_eq kind g c r activeProtectors targetLocal start
    hneq_gc hneq_gr hneq_cr hgpar hcpar hrpar hgloc hcloc hrloc hgproj hcproj hrproj
    hgprot hcprot hrprot
  obtain ⟨hlen, htags, htopo, hprot⟩ := annealTableAfterAccess_preserves_shape kind
    [g, c, r] activeProtectors targetLocal start.val
  obtain ⟨hcore_st, hcore_rel⟩ := chain3_canon_core kind g.perm c.perm r.perm start hinv
  rw [hnt, hub_eq]
  refine ⟨hcore_st, fun hc => ?_⟩
  obtain ⟨ht_eq, hp_eq, hperms_eq, hbase_eq⟩ := hcore_rel hc
  have hnt_fields := congrArg (fun t => (t.topology, t.protectedNodes)) hnt
  injection hnt_fields with hnt_topo hnt_prot
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htopo, ht_eq, ← hnt_topo]; rfl
  · rw [htags]; simp [hneq_gc, hneq_gr, hneq_cr]
  · rw [hlen]; dsimp only [List.length_cons, List.length_nil]; rw [hperms_eq, ← hafter_eq]
  · rw [hlen]; exact hbase_eq
  · rw [hprot, hp_eq, ← hnt_prot]; rfl

/-- **`basedNormalTree_performAccess_branching_children_simulation`** (certifying
`I-10` simultaneous ancestor-local & sibling-foreign propagation): for any
whole-local 3-node branching hierarchy `[c₀, c₁, p]` where both `c₀` and `c₁`
are child reborrows of `p` (`c₀.parentTag = some p.tag`,
`c₁.parentTag = some p.tag`, `p.parentTag = none`, distinct tags, unprotected)
satisfying `treeBorrowsBranch3Inv`, both access kinds (`.read` / `.write`), and
all four starting nodes (`0` = child `c₀`, `1` = sibling child `c₁`,
`2` = parent `p`, `3` = direct local access), Miri's
`NormalTreeState.performAccess` on `basedNormalTree [c₀, c₁, p] activeProtectors`
completes iff `annealTableAccessUB` is `false`, and whenever it completes,
establishes `TreeBorrowsRel` directly between `annealTableAfterAccess` and
`nres.tree`. -/
theorem basedNormalTree_performAccess_branching_children_simulation
    (kind : TreeBorrowAccessKind) (c₀ c₁ p : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 4)
    (hneq₀₁ : c₀.tag ≠ c₁.tag) (hneq₀p : c₀.tag ≠ p.tag) (hneq₁p : c₁.tag ≠ p.tag)
    (hc₀par : c₀.parentTag = some p.tag)
    (hc₁par : c₁.parentTag = some p.tag)
    (hppar : p.parentTag = none)
    (hloc₀ : c₀.targetLocal = targetLocal)
    (hloc₁ : c₁.targetLocal = targetLocal)
    (hlocp : p.targetLocal = targetLocal)
    (hproj₀ : c₀.targetProjection = .nil)
    (hproj₁ : c₁.targetProjection = .nil)
    (hprojp : p.targetProjection = .nil)
    (hc₀prot : isBorrowProtected activeProtectors c₀ = false)
    (hc₁prot : isBorrowProtected activeProtectors c₁ = false)
    (hpprot : isBorrowProtected activeProtectors p = false)
    (hinv : treeBorrowsBranch3Inv c₀.perm c₁.perm p.perm = true) :
    let nres := (basedNormalTree [c₀, c₁, p] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [c₀, c₁, p] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [c₀, c₁, p] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed → TreeBorrowsRel borrows' activeProtectors nres.tree) := by
  dsimp only []
  have hnt := basedNormalTree_branch3_eq c₀ c₁ p activeProtectors hneq₀p hneq₁p
    hc₀par hc₁par hppar hc₀prot hc₁prot hpprot
  obtain ⟨hub_eq, hafter_eq⟩ := branch3_ub_after_eq kind c₀ c₁ p activeProtectors targetLocal start
    hneq₀₁ hneq₀p hneq₁p hc₀par hc₁par hppar hloc₀ hloc₁ hlocp hproj₀ hproj₁ hprojp
    hc₀prot hc₁prot hpprot
  obtain ⟨hlen, htags, htopo, hprot⟩ := annealTableAfterAccess_preserves_shape kind
    [c₀, c₁, p] activeProtectors targetLocal start.val
  obtain ⟨hcore_st, hcore_rel⟩ := branch3_canon_core kind c₀.perm c₁.perm p.perm start hinv
  rw [hnt, hub_eq]
  refine ⟨hcore_st, fun hc => ?_⟩
  obtain ⟨ht_eq, hp_eq, hperms_eq, hbase_eq⟩ := hcore_rel hc
  have hnt_fields := congrArg (fun t => (t.topology, t.protectedNodes)) hnt
  injection hnt_fields with hnt_topo hnt_prot
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htopo, ht_eq, ← hnt_topo]; rfl
  · rw [htags]; simp [hneq₀₁, hneq₀p, hneq₁p]
  · rw [hlen]; dsimp only [List.length_cons, List.length_nil]; rw [hperms_eq, ← hafter_eq]
  · rw [hlen]; exact hbase_eq
  · rw [hprot, hp_eq, ← hnt_prot]; rfl

section ProtHierarchyOperational

private local instance : DecidableEq TreeBorrowPerm := fun a b =>
  if h : annealPermToMiri a = annealPermToMiri b then
    isTrue (annealPermToMiri_injective h)
  else
    isFalse (fun hab => h (congrArg annealPermToMiri hab))

/-- Exact inductive protector-aware ancestor-descendant invariant along a
parent-child or ancestor-descendant pair `((descPerm, descProt), (ancPerm, ancProt))`
under which Miri's `LocationState.skipIfKnownNoop` foreign-subtree pruning
(`.SkipSelfAndChildren` when `ancPerm = .disabled`, or when `ancPerm = .frozen`
on a foreign `.Read`) is observationally equivalent to Anneal's flat table scan
while permitting interior-mutable `.cell` (`&UnsafeCell<T>`) and unprotected
`.reservedIM` (`&mut UnsafeCell<T>`) descendants to survive under `.disabled`
ancestors (`I-10` & `I-11`):
1. no protected node is in `.reservedIM` (`ProtectedReservedIM` impossibility);
2. under a `.disabled` ancestor, every descendant is `.disabled`, `.cell`, or
   (unprotected) `.reservedIM`;
3. under a `.frozen` ancestor, no descendant is `.unique`, and no protected
   descendant is in `.reservedFrz false` (any foreign read that froze the
   ancestor already latched protected `.reservedFrz` descendants to
   `conflicted = true`, or any reborrow under an already-`.frozen` ancestor
   created a shared `.frozen` / `.cell` reference). -/
def treeBorrowsProtAncestorInv
    (descPerm : TreeBorrowPerm) (descProt : Bool)
    (ancPerm : TreeBorrowPerm) (ancProt : Bool) : Bool :=
  (if descProt then descPerm != .reservedIM else true) &&
  (if ancProt then ancPerm != .reservedIM else true) &&
  (if ancPerm == .disabled then
    descPerm == .disabled || descPerm == .cell || descPerm == .reservedIM
   else true) &&
  (if ancPerm == .frozen then
    descPerm != .unique &&
    (if descProt then descPerm != .reservedFrz false else true)
   else true)

/-- Inductive protector-aware ancestor-descendant invariant for a 3-level
reborrow chain `[g, c, r]` (`g` child of `c`, `c` child of `r`). -/
def treeBorrowsChain3ProtInv
    (gPerm cPerm rPerm : TreeBorrowPerm) (gProt cProt rProt : Bool) : Bool :=
  treeBorrowsProtAncestorInv gPerm gProt cPerm cProt &&
  treeBorrowsProtAncestorInv gPerm gProt rPerm rProt &&
  treeBorrowsProtAncestorInv cPerm cProt rPerm rProt

/-- Inductive protector-aware ancestor-descendant invariant for a 3-node
branching borrow tree `[c₀, c₁, p]` (`c₀` and `c₁` children of `p`). -/
def treeBorrowsBranch3ProtInv
    (c₀Perm c₁Perm pPerm : TreeBorrowPerm) (c₀Prot c₁Prot pProt : Bool) : Bool :=
  treeBorrowsProtAncestorInv c₀Perm c₀Prot pPerm pProt &&
  treeBorrowsProtAncestorInv c₁Perm c₁Prot pPerm pProt

/-- Borrow-list lift of `treeBorrowsChain3ProtInv` on `[g, c, r]` under arbitrary
`activeProtectors`. -/
def borrowListChain3ProtInv
    (borrows : List BorrowEntry) (activeProtectors : List Nat) : Bool :=
  match borrows with
  | [g, c, r] =>
    treeBorrowsChain3ProtInv g.perm c.perm r.perm
      (isBorrowProtected activeProtectors g)
      (isBorrowProtected activeProtectors c)
      (isBorrowProtected activeProtectors r)
  | _ => false

/-- Borrow-list lift of `treeBorrowsBranch3ProtInv` on `[c₀, c₁, p]` under
arbitrary `activeProtectors`. -/
def borrowListBranch3ProtInv
    (borrows : List BorrowEntry) (activeProtectors : List Nat) : Bool :=
  match borrows with
  | [c₀, c₁, p] =>
    treeBorrowsBranch3ProtInv c₀.perm c₁.perm p.perm
      (isBorrowProtected activeProtectors c₀)
      (isBorrowProtected activeProtectors c₁)
      (isBorrowProtected activeProtectors p)
  | _ => false

/-- **`treeBorrowsAncestorInv_imp_prot_false`**: the unprotected invariant
`treeBorrowsAncestorInv` strictly refines `treeBorrowsProtAncestorInv` when both
protectors are `false` (while `treeBorrowsProtAncestorInv` additionally admits
`.cell` and `.reservedIM` descendants under `.disabled` ancestors and arbitrary
active protectors). -/
theorem treeBorrowsAncestorInv_imp_prot_false
    (descPerm ancPerm : TreeBorrowPerm)
    (h : treeBorrowsAncestorInv descPerm ancPerm = true) :
    treeBorrowsProtAncestorInv descPerm false ancPerm false = true := by
  revert h
  (rcases descPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases ancPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

/-- **`treeBorrowsProtAncestorInv_retag_init`**: creating a child reference via
any retag mode (`annealRetagPerm mode mutability frozen`, protected iff
`mode == .fnEntry`) under any non-`.disabled` ancestor `(ancPerm, ancProt)`
satisfying `!ancProt ∨ ancPerm ≠ .reservedIM` (with `mutability = .not` when the
ancestor is `.frozen`) establishes `treeBorrowsProtAncestorInv`. -/
theorem treeBorrowsProtAncestorInv_retag_init
    (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool)
    (ancPerm : TreeBorrowPerm) (ancProt : Bool)
    (hanc_ndis : ancPerm ≠ .disabled)
    (hanc_nim : ancProt = true → ancPerm ≠ .reservedIM)
    (hfrz_sh : ancPerm = .frozen → mutability = .not) :
    treeBorrowsProtAncestorInv
      (annealRetagPerm mode mutability frozen) (mode == .fnEntry)
      ancPerm ancProt = true := by
  cases mutability
  · clear hfrz_sh; revert hanc_ndis hanc_nim
    cases mode <;> cases frozen <;>
      (rcases ancPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases ancProt <;> decide
  · by_cases hf : ancPerm = .frozen
    · exact False.elim (nomatch hfrz_sh hf)
    · clear hfrz_sh; revert hf hanc_ndis hanc_nim
      cases mode <;> cases frozen <;>
        (rcases ancPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases ancProt <;> decide

/-- **`treeBorrowsProtAncestorInv_release_protectors`**: releasing any subset of
active function-entry protectors on `Return` (`descProt' → descProt` and
`ancProt' → ancProt`) preserves `treeBorrowsProtAncestorInv`. -/
theorem treeBorrowsProtAncestorInv_release_protectors
    (descPerm : TreeBorrowPerm) (descProt descProt' : Bool)
    (ancPerm : TreeBorrowPerm) (ancProt ancProt' : Bool)
    (hd : descProt' = true → descProt = true)
    (ha : ancProt' = true → ancProt = true)
    (hinv : treeBorrowsProtAncestorInv descPerm descProt ancPerm ancProt = true) :
    treeBorrowsProtAncestorInv descPerm descProt' ancPerm ancProt' = true := by
  revert hd ha hinv
  (rcases descPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    (rcases ancPerm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
    cases descProt <;> cases descProt' <;> cases ancProt <;> cases ancProt' <;> decide

private def mkNormalTreeChain3Prot (gPerm cPerm rPerm : TreeBorrowPerm)
    (p₀ p₁ p₂ : Bool) : Miri.TreeBorrows.Tree.NormalTreeState :=
  { topology := ⟨#[⟨some 1, []⟩, ⟨some 2, [0]⟩, ⟨some 3, [1]⟩, ⟨none, [2]⟩]⟩
    defaultStates :=
      #[⟨annealPermToMiri gPerm, true, .None⟩,
        ⟨annealPermToMiri cPerm, true, .None⟩,
        ⟨annealPermToMiri rPerm, true, .None⟩,
        ⟨.Unique, true, .None⟩]
    protectedNodes :=
      (if p₀ then [0] else []) ++ (if p₁ then [1] else []) ++ (if p₂ then [2] else [])
    locationStates := #[none, none, none, none] }

private def mkNormalTreeBranch3Prot (c₀Perm c₁Perm pPerm : TreeBorrowPerm)
    (p₀ p₁ p₂ : Bool) : Miri.TreeBorrows.Tree.NormalTreeState :=
  { topology := ⟨#[⟨some 2, []⟩, ⟨some 2, []⟩, ⟨some 3, [0, 1]⟩, ⟨none, [2]⟩]⟩
    defaultStates :=
      #[⟨annealPermToMiri c₀Perm, true, .None⟩,
        ⟨annealPermToMiri c₁Perm, true, .None⟩,
        ⟨annealPermToMiri pPerm, true, .None⟩,
        ⟨.Unique, true, .None⟩]
    protectedNodes :=
      (if p₀ then [0] else []) ++ (if p₁ then [1] else []) ++ (if p₂ then [2] else [])
    locationStates := #[none, none, none, none] }

private theorem basedNormalTree_chain3Prot_eq (g c r : BorrowEntry)
    (activeProtectors : List Nat)
    (hneq_gc : g.tag ≠ c.tag) (hneq_gr : g.tag ≠ r.tag) (hneq_cr : c.tag ≠ r.tag)
    (hgpar : g.parentTag = some c.tag)
    (hcpar : c.parentTag = some r.tag)
    (hrpar : r.parentTag = none) :
    basedNormalTree [g, c, r] activeProtectors =
      mkNormalTreeChain3Prot g.perm c.perm r.perm
        (isBorrowProtected activeProtectors g)
        (isBorrowProtected activeProtectors c)
        (isBorrowProtected activeProtectors r) := by
  have hbeq_gc : Nat.beq g.tag c.tag = false := nat_beq_eq_false_of_ne hneq_gc
  have hbeq_gr : Nat.beq g.tag r.tag = false := nat_beq_eq_false_of_ne hneq_gr
  have hbeq_cr : Nat.beq c.tag r.tag = false := nat_beq_eq_false_of_ne hneq_cr
  have hidxc : borrowIndexOfTag [g, c, r] c.tag = some 1 := by
    simp [borrowIndexOfTag, hbeq_gc]
  have hidxr : borrowIndexOfTag [g, c, r] r.tag = some 2 := by
    simp [borrowIndexOfTag, hbeq_gr, hbeq_cr]
  have hbpg : basedParentIndex [g, c, r] g = 1 := by
    simp [basedParentIndex, hgpar, hidxc]
  have hbpc : basedParentIndex [g, c, r] c = 2 := by
    simp [basedParentIndex, hcpar, hidxr]
  have hbpr : basedParentIndex [g, c, r] r = 3 := by
    simp [basedParentIndex, hrpar]
  have hrange : List.range 3 = [0, 1, 2] := rfl
  cases hp₀ : isBorrowProtected activeProtectors g <;>
    cases hp₁ : isBorrowProtected activeProtectors c <;>
    cases hp₂ : isBorrowProtected activeProtectors r <;>
    simp [basedNormalTree, mkNormalTreeChain3Prot, basedTraversalTree, basedChildren,
      protectedIndices, hbpg, hbpc, hbpr, hrange, hp₀, hp₁, hp₂]

private theorem basedNormalTree_branch3Prot_eq (c₀ c₁ p : BorrowEntry)
    (activeProtectors : List Nat)
    (hneq₀p : c₀.tag ≠ p.tag) (hneq₁p : c₁.tag ≠ p.tag)
    (hc₀par : c₀.parentTag = some p.tag)
    (hc₁par : c₁.parentTag = some p.tag)
    (hppar : p.parentTag = none) :
    basedNormalTree [c₀, c₁, p] activeProtectors =
      mkNormalTreeBranch3Prot c₀.perm c₁.perm p.perm
        (isBorrowProtected activeProtectors c₀)
        (isBorrowProtected activeProtectors c₁)
        (isBorrowProtected activeProtectors p) := by
  have hbeq₀p : Nat.beq c₀.tag p.tag = false := nat_beq_eq_false_of_ne hneq₀p
  have hbeq₁p : Nat.beq c₁.tag p.tag = false := nat_beq_eq_false_of_ne hneq₁p
  have hidxp : borrowIndexOfTag [c₀, c₁, p] p.tag = some 2 := by
    simp [borrowIndexOfTag, hbeq₀p, hbeq₁p]
  have hbpc₀ : basedParentIndex [c₀, c₁, p] c₀ = 2 := by
    simp [basedParentIndex, hc₀par, hidxp]
  have hbpc₁ : basedParentIndex [c₀, c₁, p] c₁ = 2 := by
    simp [basedParentIndex, hc₁par, hidxp]
  have hbpp : basedParentIndex [c₀, c₁, p] p = 3 := by
    simp [basedParentIndex, hppar]
  have hrange : List.range 3 = [0, 1, 2] := rfl
  cases hp₀ : isBorrowProtected activeProtectors c₀ <;>
    cases hp₁ : isBorrowProtected activeProtectors c₁ <;>
    cases hp₂ : isBorrowProtected activeProtectors p <;>
    simp [basedNormalTree, mkNormalTreeBranch3Prot, basedTraversalTree, basedChildren,
      protectedIndices, hbpc₀, hbpc₁, hbpp, hrange, hp₀, hp₁, hp₂]

private def canonProts3 (p₀ p₁ p₂ : Bool) : List Nat :=
  (if p₀ then [1] else []) ++ (if p₁ then [2] else []) ++ (if p₂ then [3] else [])

private def canonChain3Prot (gPerm cPerm rPerm : TreeBorrowPerm)
    (p₀ p₁ p₂ : Bool) : List BorrowEntry :=
  [{ tag := 3, targetLocal := 0, targetProjection := .nil, perm := gPerm,
     protector := if p₀ then some 1 else none, parentTag := some 2 },
   { tag := 2, targetLocal := 0, targetProjection := .nil, perm := cPerm,
     protector := if p₁ then some 2 else none, parentTag := some 1 },
   { tag := 1, targetLocal := 0, targetProjection := .nil, perm := rPerm,
     protector := if p₂ then some 3 else none, parentTag := none }]

private def canonBranch3Prot (c₀Perm c₁Perm pPerm : TreeBorrowPerm)
    (p₀ p₁ p₂ : Bool) : List BorrowEntry :=
  [{ tag := 3, targetLocal := 0, targetProjection := .nil, perm := c₀Perm,
     protector := if p₀ then some 1 else none, parentTag := some 1 },
   { tag := 2, targetLocal := 0, targetProjection := .nil, perm := c₁Perm,
     protector := if p₁ then some 2 else none, parentTag := some 1 },
   { tag := 1, targetLocal := 0, targetProjection := .nil, perm := pPerm,
     protector := if p₂ then some 3 else none, parentTag := none }]

private theorem isBorrowProtected_canon3_0 (perm : TreeBorrowPerm) (pt : Option Nat)
    (p₀ p₁ p₂ : Bool) :
    isBorrowProtected (canonProts3 p₀ p₁ p₂)
      { tag := 3, targetLocal := 0, targetProjection := .nil, perm := perm,
        protector := if p₀ then some 1 else none, parentTag := pt } = p₀ := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;> rfl

private theorem isBorrowProtected_canon3_1 (perm : TreeBorrowPerm) (pt : Option Nat)
    (p₀ p₁ p₂ : Bool) :
    isBorrowProtected (canonProts3 p₀ p₁ p₂)
      { tag := 2, targetLocal := 0, targetProjection := .nil, perm := perm,
        protector := if p₁ then some 2 else none, parentTag := pt } = p₁ := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;> rfl

private theorem isBorrowProtected_canon3_2 (perm : TreeBorrowPerm) (pt : Option Nat)
    (p₀ p₁ p₂ : Bool) :
    isBorrowProtected (canonProts3 p₀ p₁ p₂)
      { tag := 1, targetLocal := 0, targetProjection := .nil, perm := perm,
        protector := if p₂ then some 3 else none, parentTag := pt } = p₂ := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;> rfl

section ProtCanonAccessEq

attribute [local simp] applyTreeBorrowTransition_perm_eq nat_beq_refl
  borrowEntryOverlapsWrite_mk_nil
  isBorrowProtected_canon3_0 isBorrowProtected_canon3_1 isBorrowProtected_canon3_2
  annealTableAccessUB annealTableAfterAccess basedAccessTag
  canonChain3Prot canonBranch3Prot hasTreeReadUB borrowEntryReadUB
  freezeTreeBorrowsOnReadAtProj updateBorrowPermOnReadAtProj
  hasProtectedTreeWriteConflict hasProtectedWriteConflict borrowEntryWriteConflicts
  invalidateTreeBorrowsAtProj updateBorrowPermTreeAtProj updateBorrowPermAtProj
  resolveTreeBorrowWriterTag isBorrowDescendantOrSelf isBorrowDescendantOrSelfAux
  treeBorrowChainChildAccessUBAux lookupBorrow length

private theorem chain3Prot_ub_after_eq (kind : TreeBorrowAccessKind)
    (g c r : BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (start : Fin 4)
    (hneq_gc : g.tag ≠ c.tag) (hneq_gr : g.tag ≠ r.tag) (hneq_cr : c.tag ≠ r.tag)
    (hgpar : g.parentTag = some c.tag)
    (hcpar : c.parentTag = some r.tag)
    (hrpar : r.parentTag = none)
    (hgloc : g.targetLocal = targetLocal)
    (hcloc : c.targetLocal = targetLocal)
    (hrloc : r.targetLocal = targetLocal)
    (hgproj : g.targetProjection = .nil)
    (hcproj : c.targetProjection = .nil)
    (hrproj : r.targetProjection = .nil) :
    let p₀ := isBorrowProtected activeProtectors g
    let p₁ := isBorrowProtected activeProtectors c
    let p₂ := isBorrowProtected activeProtectors r
    annealTableAccessUB kind [g, c, r] activeProtectors targetLocal start.val =
      annealTableAccessUB kind (canonChain3Prot g.perm c.perm r.perm p₀ p₁ p₂)
        (canonProts3 p₀ p₁ p₂) 0 start.val ∧
    (annealTableAfterAccess kind [g, c, r] activeProtectors targetLocal start.val).map
        (fun e => some e.perm) =
      (annealTableAfterAccess kind (canonChain3Prot g.perm c.perm r.perm p₀ p₁ p₂)
        (canonProts3 p₀ p₁ p₂) 0 start.val).map (fun e => some e.perm) := by
  have hbeq_gc : Nat.beq g.tag c.tag = false := nat_beq_eq_false_of_ne hneq_gc
  have hbeq_cg : Nat.beq c.tag g.tag = false := nat_beq_eq_false_of_ne hneq_gc.symm
  have hbeq_gr : Nat.beq g.tag r.tag = false := nat_beq_eq_false_of_ne hneq_gr
  have hbeq_rg : Nat.beq r.tag g.tag = false := nat_beq_eq_false_of_ne hneq_gr.symm
  have hbeq_cr : Nat.beq c.tag r.tag = false := nat_beq_eq_false_of_ne hneq_cr
  have hbeq_rc : Nat.beq r.tag c.tag = false := nat_beq_eq_false_of_ne hneq_cr.symm
  have hgov : borrowEntryOverlapsWrite g .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true g hgproj
  have hcov : borrowEntryOverlapsWrite c .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true c hcproj
  have hrov : borrowEntryOverlapsWrite r .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true r hrproj
  dsimp only []
  generalize hpr₀ : isBorrowProtected activeProtectors g = p₀
  generalize hpr₁ : isBorrowProtected activeProtectors c = p₁
  generalize hpr₂ : isBorrowProtected activeProtectors r = p₂
  rcases start with ⟨_ | _ | _ | _ | _, hlt⟩
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · omega

private theorem branch3Prot_ub_after_eq (kind : TreeBorrowAccessKind)
    (c₀ c₁ p : BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (start : Fin 4)
    (hneq₀₁ : c₀.tag ≠ c₁.tag) (hneq₀p : c₀.tag ≠ p.tag) (hneq₁p : c₁.tag ≠ p.tag)
    (hc₀par : c₀.parentTag = some p.tag)
    (hc₁par : c₁.parentTag = some p.tag)
    (hppar : p.parentTag = none)
    (hloc₀ : c₀.targetLocal = targetLocal)
    (hloc₁ : c₁.targetLocal = targetLocal)
    (hlocp : p.targetLocal = targetLocal)
    (hproj₀ : c₀.targetProjection = .nil)
    (hproj₁ : c₁.targetProjection = .nil)
    (hprojp : p.targetProjection = .nil) :
    let p₀ := isBorrowProtected activeProtectors c₀
    let p₁ := isBorrowProtected activeProtectors c₁
    let p₂ := isBorrowProtected activeProtectors p
    annealTableAccessUB kind [c₀, c₁, p] activeProtectors targetLocal start.val =
      annealTableAccessUB kind (canonBranch3Prot c₀.perm c₁.perm p.perm p₀ p₁ p₂)
        (canonProts3 p₀ p₁ p₂) 0 start.val ∧
    (annealTableAfterAccess kind [c₀, c₁, p] activeProtectors targetLocal start.val).map
        (fun e => some e.perm) =
      (annealTableAfterAccess kind (canonBranch3Prot c₀.perm c₁.perm p.perm p₀ p₁ p₂)
        (canonProts3 p₀ p₁ p₂) 0 start.val).map (fun e => some e.perm) := by
  have hbeq₀₁ : Nat.beq c₀.tag c₁.tag = false := nat_beq_eq_false_of_ne hneq₀₁
  have hbeq₁₀ : Nat.beq c₁.tag c₀.tag = false := nat_beq_eq_false_of_ne hneq₀₁.symm
  have hbeq₀p : Nat.beq c₀.tag p.tag = false := nat_beq_eq_false_of_ne hneq₀p
  have hbeqp₀ : Nat.beq p.tag c₀.tag = false := nat_beq_eq_false_of_ne hneq₀p.symm
  have hbeq₁p : Nat.beq c₁.tag p.tag = false := nat_beq_eq_false_of_ne hneq₁p
  have hbeqp₁ : Nat.beq p.tag c₁.tag = false := nat_beq_eq_false_of_ne hneq₁p.symm
  have hov₀ : borrowEntryOverlapsWrite c₀ .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true c₀ hproj₀
  have hov₁ : borrowEntryOverlapsWrite c₁ .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true c₁ hproj₁
  have hovp : borrowEntryOverlapsWrite p .nil 0 0 = true :=
    borrowEntryOverlapsWrite_nil_eq_true p hprojp
  dsimp only []
  generalize hpr₀ : isBorrowProtected activeProtectors c₀ = p₀
  generalize hpr₁ : isBorrowProtected activeProtectors c₁ = p₁
  generalize hpr₂ : isBorrowProtected activeProtectors p = p₂
  rcases start with ⟨_ | _ | _ | _ | _, hlt⟩
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · cases kind <;> simp [*, -applyTreeBorrowTransition]
  · omega

end ProtCanonAccessEq

private theorem annealTableAfterAccess_map_isBorrowProtected
    (kind : TreeBorrowAccessKind) (borrows : List BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Nat) :
    (annealTableAfterAccess kind borrows activeProtectors targetLocal start).map
      (isBorrowProtected activeProtectors) =
    borrows.map (isBorrowProtected activeProtectors) := by
  have hex : ∃ f : BorrowEntry → BorrowEntry,
      annealTableAfterAccess kind borrows activeProtectors targetLocal start = borrows.map f ∧
      ∀ e, (f e).protector = e.protector := by
    cases kind
    · refine ⟨fun e => updateBorrowPermOnReadAtProj borrows e targetLocal
          (basedAccessTag borrows start) .nil 0 0 activeProtectors,
        freezeTreeBorrowsOnReadAtProj_eq_map ..,
        fun e => (updateBorrowPermOnReadAtProj_preserves_tag_parent_prot borrows e targetLocal
          (basedAccessTag borrows start) .nil 0 0 activeProtectors).2.2⟩
    · refine ⟨fun e => updateBorrowPermTreeAtProj borrows e targetLocal
          (basedAccessTag borrows start) .nil 0 0,
        invalidateTreeBorrowsAtProj_eq_map ..,
        fun e => (updateBorrowPermTreeAtProj_preserves_tag_parent_prot borrows e targetLocal
          (basedAccessTag borrows start) .nil 0 0).2.2⟩
  obtain ⟨f, hmap, hf⟩ := hex
  rw [hmap, List.map_map]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, isBorrowProtected, hf e]

private theorem borrowListChain3ProtInv_eq_of_perms_prots
    (b₁ b₂ : List BorrowEntry) (ap₁ ap₂ : List Nat)
    (hperms : b₁.map (fun e => some e.perm) = b₂.map (fun e => some e.perm))
    (hprots : b₁.map (isBorrowProtected ap₁) = b₂.map (isBorrowProtected ap₂)) :
    borrowListChain3ProtInv b₁ ap₁ = borrowListChain3ProtInv b₂ ap₂ := by
  have hlen : b₁.length = b₂.length := by
    have h := congrArg List.length hperms
    simpa only [List.length_map] using h
  rcases b₁ with _ | ⟨e₀, _ | ⟨e₁, _ | ⟨e₂, _ | _⟩⟩⟩ <;>
    rcases b₂ with _ | ⟨f₀, _ | ⟨f₁, _ | ⟨f₂, _ | _⟩⟩⟩
  all_goals simp only [List.length_cons, List.length_nil] at hlen
  all_goals try omega
  · rfl
  · rfl
  · rfl
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, Option.some.injEq, and_true]
      at hperms hprots
    obtain ⟨hp₀, hp₁, hp₂⟩ := hperms
    obtain ⟨hq₀, hq₁, hq₂⟩ := hprots
    simp only [borrowListChain3ProtInv, hp₀, hp₁, hp₂, hq₀, hq₁, hq₂]
  · rfl

private theorem borrowListBranch3ProtInv_eq_of_perms_prots
    (b₁ b₂ : List BorrowEntry) (ap₁ ap₂ : List Nat)
    (hperms : b₁.map (fun e => some e.perm) = b₂.map (fun e => some e.perm))
    (hprots : b₁.map (isBorrowProtected ap₁) = b₂.map (isBorrowProtected ap₂)) :
    borrowListBranch3ProtInv b₁ ap₁ = borrowListBranch3ProtInv b₂ ap₂ := by
  have hlen : b₁.length = b₂.length := by
    have h := congrArg List.length hperms
    simpa only [List.length_map] using h
  rcases b₁ with _ | ⟨e₀, _ | ⟨e₁, _ | ⟨e₂, _ | _⟩⟩⟩ <;>
    rcases b₂ with _ | ⟨f₀, _ | ⟨f₁, _ | ⟨f₂, _ | _⟩⟩⟩
  all_goals simp only [List.length_cons, List.length_nil] at hlen
  all_goals try omega
  · rfl
  · rfl
  · rfl
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, Option.some.injEq, and_true]
      at hperms hprots
    obtain ⟨hp₀, hp₁, hp₂⟩ := hperms
    obtain ⟨hq₀, hq₁, hq₂⟩ := hprots
    simp only [borrowListBranch3ProtInv, hp₀, hp₁, hp₂, hq₀, hq₁, hq₂]
  · rfl

private abbrev chain3ProtCoreGoal (kind : TreeBorrowAccessKind)
    (gPerm cPerm rPerm : TreeBorrowPerm) (p₀ p₁ p₂ : Bool) (startVal : Nat) : Prop :=
  treeBorrowsChain3ProtInv gPerm cPerm rPerm p₀ p₁ p₂ = true →
  let nt := mkNormalTreeChain3Prot gPerm cPerm rPerm p₀ p₁ p₂
  let nres := nt.performAccess startVal (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
  let cb := canonChain3Prot gPerm cPerm rPerm p₀ p₁ p₂
  let cp := canonProts3 p₀ p₁ p₂
  let cafter := annealTableAfterAccess kind cb cp 0 startVal
  (nres.status = .Completed ↔ annealTableAccessUB kind cb cp 0 startVal = false) ∧
  (nres.status = .Completed →
    nres.tree.topology = nt.topology ∧
    nres.tree.protectedNodes = nt.protectedNodes ∧
    normalTreePerms nres.tree 3 = cafter.map (fun e => some e.perm) ∧
    (nres.tree.stateAt 3).map (fun st => st.permission) = some .Unique ∧
    borrowListChain3ProtInv cafter cp = true)

private def allPermsProt : List TreeBorrowPerm :=
  [.cell, .reservedFrz false, .reservedFrz true, .reservedIM, .unique, .frozen, .disabled]

private theorem mem_allPermsProt (p : TreeBorrowPerm) : p ∈ allPermsProt := by
  (rcases p with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> decide

private def allBoolsProt : List Bool := [false, true]

private theorem mem_allBoolsProt (b : Bool) : b ∈ allBoolsProt := by
  cases b <;> decide

private def checkChain3Prot (kind : TreeBorrowAccessKind) (startVal : Nat)
    (p₀ p₁ : Bool) : Bool :=
  allPermsProt.all fun g =>
  allPermsProt.all fun c =>
  allPermsProt.all fun r =>
  allBoolsProt.all fun p₂ =>
    decide (chain3ProtCoreGoal kind g c r p₀ p₁ p₂ startVal)

private theorem checkChain3Prot_r0_ff : checkChain3Prot .read 0 false false = true := by decide
private theorem checkChain3Prot_r0_ft : checkChain3Prot .read 0 false true = true := by decide
private theorem checkChain3Prot_r0_tf : checkChain3Prot .read 0 true false = true := by decide
private theorem checkChain3Prot_r0_tt : checkChain3Prot .read 0 true true = true := by decide
private theorem checkChain3Prot_r1_ff : checkChain3Prot .read 1 false false = true := by decide
private theorem checkChain3Prot_r1_ft : checkChain3Prot .read 1 false true = true := by decide
private theorem checkChain3Prot_r1_tf : checkChain3Prot .read 1 true false = true := by decide
private theorem checkChain3Prot_r1_tt : checkChain3Prot .read 1 true true = true := by decide
private theorem checkChain3Prot_r2_ff : checkChain3Prot .read 2 false false = true := by decide
private theorem checkChain3Prot_r2_ft : checkChain3Prot .read 2 false true = true := by decide
private theorem checkChain3Prot_r2_tf : checkChain3Prot .read 2 true false = true := by decide
private theorem checkChain3Prot_r2_tt : checkChain3Prot .read 2 true true = true := by decide
private theorem checkChain3Prot_r3_ff : checkChain3Prot .read 3 false false = true := by decide
private theorem checkChain3Prot_r3_ft : checkChain3Prot .read 3 false true = true := by decide
private theorem checkChain3Prot_r3_tf : checkChain3Prot .read 3 true false = true := by decide
private theorem checkChain3Prot_r3_tt : checkChain3Prot .read 3 true true = true := by decide
private theorem checkChain3Prot_w0_ff : checkChain3Prot .write 0 false false = true := by decide
private theorem checkChain3Prot_w0_ft : checkChain3Prot .write 0 false true = true := by decide
private theorem checkChain3Prot_w0_tf : checkChain3Prot .write 0 true false = true := by decide
private theorem checkChain3Prot_w0_tt : checkChain3Prot .write 0 true true = true := by decide
private theorem checkChain3Prot_w1_ff : checkChain3Prot .write 1 false false = true := by decide
private theorem checkChain3Prot_w1_ft : checkChain3Prot .write 1 false true = true := by decide
private theorem checkChain3Prot_w1_tf : checkChain3Prot .write 1 true false = true := by decide
private theorem checkChain3Prot_w1_tt : checkChain3Prot .write 1 true true = true := by decide
private theorem checkChain3Prot_w2_ff : checkChain3Prot .write 2 false false = true := by decide
private theorem checkChain3Prot_w2_ft : checkChain3Prot .write 2 false true = true := by decide
private theorem checkChain3Prot_w2_tf : checkChain3Prot .write 2 true false = true := by decide
private theorem checkChain3Prot_w2_tt : checkChain3Prot .write 2 true true = true := by decide
private theorem checkChain3Prot_w3_ff : checkChain3Prot .write 3 false false = true := by decide
private theorem checkChain3Prot_w3_ft : checkChain3Prot .write 3 false true = true := by decide
private theorem checkChain3Prot_w3_tf : checkChain3Prot .write 3 true false = true := by decide
private theorem checkChain3Prot_w3_tt : checkChain3Prot .write 3 true true = true := by decide

private theorem checkChain3Prot_eq_true (kind : TreeBorrowAccessKind) (start : Fin 4)
    (p₀ p₁ : Bool) :
    checkChain3Prot kind start.val p₀ p₁ = true := by
  rcases start with ⟨_ | _ | _ | _ | _, hlt⟩ <;> dsimp only []
  · cases kind <;> cases p₀ <;> cases p₁
    · exact checkChain3Prot_r0_ff
    · exact checkChain3Prot_r0_ft
    · exact checkChain3Prot_r0_tf
    · exact checkChain3Prot_r0_tt
    · exact checkChain3Prot_w0_ff
    · exact checkChain3Prot_w0_ft
    · exact checkChain3Prot_w0_tf
    · exact checkChain3Prot_w0_tt
  · cases kind <;> cases p₀ <;> cases p₁
    · exact checkChain3Prot_r1_ff
    · exact checkChain3Prot_r1_ft
    · exact checkChain3Prot_r1_tf
    · exact checkChain3Prot_r1_tt
    · exact checkChain3Prot_w1_ff
    · exact checkChain3Prot_w1_ft
    · exact checkChain3Prot_w1_tf
    · exact checkChain3Prot_w1_tt
  · cases kind <;> cases p₀ <;> cases p₁
    · exact checkChain3Prot_r2_ff
    · exact checkChain3Prot_r2_ft
    · exact checkChain3Prot_r2_tf
    · exact checkChain3Prot_r2_tt
    · exact checkChain3Prot_w2_ff
    · exact checkChain3Prot_w2_ft
    · exact checkChain3Prot_w2_tf
    · exact checkChain3Prot_w2_tt
  · cases kind <;> cases p₀ <;> cases p₁
    · exact checkChain3Prot_r3_ff
    · exact checkChain3Prot_r3_ft
    · exact checkChain3Prot_r3_tf
    · exact checkChain3Prot_r3_tt
    · exact checkChain3Prot_w3_ff
    · exact checkChain3Prot_w3_ft
    · exact checkChain3Prot_w3_tf
    · exact checkChain3Prot_w3_tt
  · omega

private theorem chain3Prot_canon_core (kind : TreeBorrowAccessKind)
    (g c r : TreeBorrowPerm) (p₀ p₁ p₂ : Bool) (start : Fin 4) :
    chain3ProtCoreGoal kind g c r p₀ p₁ p₂ start.val := by
  have hall := checkChain3Prot_eq_true kind start p₀ p₁
  dsimp only [checkChain3Prot] at hall
  have h₁ := List.all_eq_true.mp hall g (mem_allPermsProt g)
  have h₂ := List.all_eq_true.mp h₁ c (mem_allPermsProt c)
  have h₃ := List.all_eq_true.mp h₂ r (mem_allPermsProt r)
  have h₄ := List.all_eq_true.mp h₃ p₂ (mem_allBoolsProt p₂)
  exact of_decide_eq_true h₄

private abbrev branch3ProtCoreGoal (kind : TreeBorrowAccessKind)
    (c₀Perm c₁Perm pPerm : TreeBorrowPerm) (p₀ p₁ p₂ : Bool) (startVal : Nat) : Prop :=
  treeBorrowsBranch3ProtInv c₀Perm c₁Perm pPerm p₀ p₁ p₂ = true →
  let nt := mkNormalTreeBranch3Prot c₀Perm c₁Perm pPerm p₀ p₁ p₂
  let nres := nt.performAccess startVal (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
  let cb := canonBranch3Prot c₀Perm c₁Perm pPerm p₀ p₁ p₂
  let cp := canonProts3 p₀ p₁ p₂
  let cafter := annealTableAfterAccess kind cb cp 0 startVal
  (nres.status = .Completed ↔ annealTableAccessUB kind cb cp 0 startVal = false) ∧
  (nres.status = .Completed →
    nres.tree.topology = nt.topology ∧
    nres.tree.protectedNodes = nt.protectedNodes ∧
    normalTreePerms nres.tree 3 = cafter.map (fun e => some e.perm) ∧
    (nres.tree.stateAt 3).map (fun st => st.permission) = some .Unique ∧
    borrowListBranch3ProtInv cafter cp = true)

private def checkBranch3Prot (kind : TreeBorrowAccessKind) (startVal : Nat)
    (p₀ p₁ : Bool) : Bool :=
  allPermsProt.all fun c₀ =>
  allPermsProt.all fun c₁ =>
  allPermsProt.all fun p =>
  allBoolsProt.all fun p₂ =>
    decide (branch3ProtCoreGoal kind c₀ c₁ p p₀ p₁ p₂ startVal)

private theorem checkBranch3Prot_r0_ff : checkBranch3Prot .read 0 false false = true := by decide
private theorem checkBranch3Prot_r0_ft : checkBranch3Prot .read 0 false true = true := by decide
private theorem checkBranch3Prot_r0_tf : checkBranch3Prot .read 0 true false = true := by decide
private theorem checkBranch3Prot_r0_tt : checkBranch3Prot .read 0 true true = true := by decide
private theorem checkBranch3Prot_r1_ff : checkBranch3Prot .read 1 false false = true := by decide
private theorem checkBranch3Prot_r1_ft : checkBranch3Prot .read 1 false true = true := by decide
private theorem checkBranch3Prot_r1_tf : checkBranch3Prot .read 1 true false = true := by decide
private theorem checkBranch3Prot_r1_tt : checkBranch3Prot .read 1 true true = true := by decide
private theorem checkBranch3Prot_r2_ff : checkBranch3Prot .read 2 false false = true := by decide
private theorem checkBranch3Prot_r2_ft : checkBranch3Prot .read 2 false true = true := by decide
private theorem checkBranch3Prot_r2_tf : checkBranch3Prot .read 2 true false = true := by decide
private theorem checkBranch3Prot_r2_tt : checkBranch3Prot .read 2 true true = true := by decide
private theorem checkBranch3Prot_r3_ff : checkBranch3Prot .read 3 false false = true := by decide
private theorem checkBranch3Prot_r3_ft : checkBranch3Prot .read 3 false true = true := by decide
private theorem checkBranch3Prot_r3_tf : checkBranch3Prot .read 3 true false = true := by decide
private theorem checkBranch3Prot_r3_tt : checkBranch3Prot .read 3 true true = true := by decide
private theorem checkBranch3Prot_w0_ff : checkBranch3Prot .write 0 false false = true := by decide
private theorem checkBranch3Prot_w0_ft : checkBranch3Prot .write 0 false true = true := by decide
private theorem checkBranch3Prot_w0_tf : checkBranch3Prot .write 0 true false = true := by decide
private theorem checkBranch3Prot_w0_tt : checkBranch3Prot .write 0 true true = true := by decide
private theorem checkBranch3Prot_w1_ff : checkBranch3Prot .write 1 false false = true := by decide
private theorem checkBranch3Prot_w1_ft : checkBranch3Prot .write 1 false true = true := by decide
private theorem checkBranch3Prot_w1_tf : checkBranch3Prot .write 1 true false = true := by decide
private theorem checkBranch3Prot_w1_tt : checkBranch3Prot .write 1 true true = true := by decide
private theorem checkBranch3Prot_w2_ff : checkBranch3Prot .write 2 false false = true := by decide
private theorem checkBranch3Prot_w2_ft : checkBranch3Prot .write 2 false true = true := by decide
private theorem checkBranch3Prot_w2_tf : checkBranch3Prot .write 2 true false = true := by decide
private theorem checkBranch3Prot_w2_tt : checkBranch3Prot .write 2 true true = true := by decide
private theorem checkBranch3Prot_w3_ff : checkBranch3Prot .write 3 false false = true := by decide
private theorem checkBranch3Prot_w3_ft : checkBranch3Prot .write 3 false true = true := by decide
private theorem checkBranch3Prot_w3_tf : checkBranch3Prot .write 3 true false = true := by decide
private theorem checkBranch3Prot_w3_tt : checkBranch3Prot .write 3 true true = true := by decide

private theorem checkBranch3Prot_eq_true (kind : TreeBorrowAccessKind) (start : Fin 4)
    (p₀ p₁ : Bool) :
    checkBranch3Prot kind start.val p₀ p₁ = true := by
  rcases start with ⟨_ | _ | _ | _ | _, hlt⟩ <;> dsimp only []
  · cases kind <;> cases p₀ <;> cases p₁
    · exact checkBranch3Prot_r0_ff
    · exact checkBranch3Prot_r0_ft
    · exact checkBranch3Prot_r0_tf
    · exact checkBranch3Prot_r0_tt
    · exact checkBranch3Prot_w0_ff
    · exact checkBranch3Prot_w0_ft
    · exact checkBranch3Prot_w0_tf
    · exact checkBranch3Prot_w0_tt
  · cases kind <;> cases p₀ <;> cases p₁
    · exact checkBranch3Prot_r1_ff
    · exact checkBranch3Prot_r1_ft
    · exact checkBranch3Prot_r1_tf
    · exact checkBranch3Prot_r1_tt
    · exact checkBranch3Prot_w1_ff
    · exact checkBranch3Prot_w1_ft
    · exact checkBranch3Prot_w1_tf
    · exact checkBranch3Prot_w1_tt
  · cases kind <;> cases p₀ <;> cases p₁
    · exact checkBranch3Prot_r2_ff
    · exact checkBranch3Prot_r2_ft
    · exact checkBranch3Prot_r2_tf
    · exact checkBranch3Prot_r2_tt
    · exact checkBranch3Prot_w2_ff
    · exact checkBranch3Prot_w2_ft
    · exact checkBranch3Prot_w2_tf
    · exact checkBranch3Prot_w2_tt
  · cases kind <;> cases p₀ <;> cases p₁
    · exact checkBranch3Prot_r3_ff
    · exact checkBranch3Prot_r3_ft
    · exact checkBranch3Prot_r3_tf
    · exact checkBranch3Prot_r3_tt
    · exact checkBranch3Prot_w3_ff
    · exact checkBranch3Prot_w3_ft
    · exact checkBranch3Prot_w3_tf
    · exact checkBranch3Prot_w3_tt
  · omega

private theorem branch3Prot_canon_core (kind : TreeBorrowAccessKind)
    (c₀ c₁ p : TreeBorrowPerm) (p₀ p₁ p₂ : Bool) (start : Fin 4) :
    branch3ProtCoreGoal kind c₀ c₁ p p₀ p₁ p₂ start.val := by
  have hall := checkBranch3Prot_eq_true kind start p₀ p₁
  dsimp only [checkBranch3Prot] at hall
  have h₁ := List.all_eq_true.mp hall c₀ (mem_allPermsProt c₀)
  have h₂ := List.all_eq_true.mp h₁ c₁ (mem_allPermsProt c₁)
  have h₃ := List.all_eq_true.mp h₂ p (mem_allPermsProt p)
  have h₄ := List.all_eq_true.mp h₃ p₂ (mem_allBoolsProt p₂)
  exact of_decide_eq_true h₄

end ProtHierarchyOperational

/-- **`basedNormalTree_performAccess_three_level_chain_prot_simulation`**
(certifying `I-10` & `I-11` inductive multi-level ancestor/descendant traversal
with arbitrary active protectors and interior mutability): for any whole-local
3-level reborrow chain `[g, c, r]` (`g.parentTag = some c.tag`,
`c.parentTag = some r.tag`, `r.parentTag = none`, distinct tags), **any**
`activeProtectors` list (admitting protected nodes as well as `.cell` and
unprotected `.reservedIM` descendants surviving under `.disabled` ancestors),
both access kinds (`.read` / `.write`), and all four starting nodes
(`0..3`) satisfying `borrowListChain3ProtInv [g, c, r] activeProtectors = true`:
1. Miri's `NormalTreeState.performAccess` on `basedNormalTree [g, c, r] activeProtectors`
   completes iff `annealTableAccessUB` is `false`;
2. whenever it completes, it establishes `TreeBorrowsRel borrows' activeProtectors nres.tree`
   **and** inductively preserves `borrowListChain3ProtInv borrows' activeProtectors = true`
   for subsequent accesses. -/
theorem basedNormalTree_performAccess_three_level_chain_prot_simulation
    (kind : TreeBorrowAccessKind) (g c r : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 4)
    (hneq_gc : g.tag ≠ c.tag) (hneq_gr : g.tag ≠ r.tag) (hneq_cr : c.tag ≠ r.tag)
    (hgpar : g.parentTag = some c.tag)
    (hcpar : c.parentTag = some r.tag)
    (hrpar : r.parentTag = none)
    (hgloc : g.targetLocal = targetLocal)
    (hcloc : c.targetLocal = targetLocal)
    (hrloc : r.targetLocal = targetLocal)
    (hgproj : g.targetProjection = .nil)
    (hcproj : c.targetProjection = .nil)
    (hrproj : r.targetProjection = .nil)
    (hinv : borrowListChain3ProtInv [g, c, r] activeProtectors = true) :
    let nres := (basedNormalTree [g, c, r] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [g, c, r] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [g, c, r] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed →
      TreeBorrowsRel borrows' activeProtectors nres.tree ∧
      borrowListChain3ProtInv borrows' activeProtectors = true) := by
  dsimp only []
  dsimp only [borrowListChain3ProtInv] at hinv
  have hnt := basedNormalTree_chain3Prot_eq g c r activeProtectors
    hneq_gc hneq_gr hneq_cr hgpar hcpar hrpar
  obtain ⟨hub_eq, hafter_eq⟩ := chain3Prot_ub_after_eq kind g c r activeProtectors
    targetLocal start hneq_gc hneq_gr hneq_cr hgpar hcpar hrpar hgloc hcloc hrloc
    hgproj hcproj hrproj
  obtain ⟨hlen, htags, htopo, hprot⟩ := annealTableAfterAccess_preserves_shape kind
    [g, c, r] activeProtectors targetLocal start.val
  obtain ⟨hcore_st, hcore_rel⟩ := chain3Prot_canon_core kind g.perm c.perm r.perm
    (isBorrowProtected activeProtectors g)
    (isBorrowProtected activeProtectors c)
    (isBorrowProtected activeProtectors r) start hinv
  rw [hnt, hub_eq]
  refine ⟨hcore_st, fun hc => ?_⟩
  obtain ⟨ht_eq, hp_eq, hperms_eq, hbase_eq, hinv_post⟩ := hcore_rel hc
  have hnt_fields := congrArg (fun t => (t.topology, t.protectedNodes)) hnt
  injection hnt_fields with hnt_topo hnt_prot
  have hprots_eq :
      (annealTableAfterAccess kind [g, c, r] activeProtectors targetLocal start.val).map
        (isBorrowProtected activeProtectors) =
      (annealTableAfterAccess kind
        (canonChain3Prot g.perm c.perm r.perm
          (isBorrowProtected activeProtectors g)
          (isBorrowProtected activeProtectors c)
          (isBorrowProtected activeProtectors r))
        (canonProts3
          (isBorrowProtected activeProtectors g)
          (isBorrowProtected activeProtectors c)
          (isBorrowProtected activeProtectors r)) 0 start.val).map
        (isBorrowProtected (canonProts3
          (isBorrowProtected activeProtectors g)
          (isBorrowProtected activeProtectors c)
          (isBorrowProtected activeProtectors r))) := by
    rw [annealTableAfterAccess_map_isBorrowProtected, annealTableAfterAccess_map_isBorrowProtected]
    simp only [canonChain3Prot, List.map_cons, List.map_nil,
      isBorrowProtected_canon3_0, isBorrowProtected_canon3_1, isBorrowProtected_canon3_2]
  have hinv' : borrowListChain3ProtInv
      (annealTableAfterAccess kind [g, c, r] activeProtectors targetLocal start.val)
      activeProtectors = true := by
    rw [borrowListChain3ProtInv_eq_of_perms_prots _ _ _ _ hafter_eq hprots_eq]
    exact hinv_post
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hinv'⟩
  · rw [htopo, ht_eq, ← hnt_topo]; rfl
  · rw [htags]; simp [hneq_gc, hneq_gr, hneq_cr]
  · rw [hlen]; dsimp only [List.length_cons, List.length_nil]; rw [hperms_eq, ← hafter_eq]
  · rw [hlen]; exact hbase_eq
  · rw [hprot, hp_eq, ← hnt_prot]; rfl

/-- **`basedNormalTree_performAccess_branching_children_prot_simulation`**
(certifying `I-10` & `I-11` inductive branching sibling/ancestor traversal with
arbitrary active protectors and interior mutability): for any whole-local 3-node
branching hierarchy `[c₀, c₁, p]` (`c₀.parentTag = some p.tag`,
`c₁.parentTag = some p.tag`, `p.parentTag = none`, distinct tags), **any**
`activeProtectors` list, both access kinds (`.read` / `.write`), and all four
starting nodes (`0..3`) satisfying
`borrowListBranch3ProtInv [c₀, c₁, p] activeProtectors = true`:
1. Miri's `NormalTreeState.performAccess` on `basedNormalTree [c₀, c₁, p] activeProtectors`
   completes iff `annealTableAccessUB` is `false`;
2. whenever it completes, it establishes `TreeBorrowsRel borrows' activeProtectors nres.tree`
   **and** inductively preserves `borrowListBranch3ProtInv borrows' activeProtectors = true`
   for subsequent accesses. -/
theorem basedNormalTree_performAccess_branching_children_prot_simulation
    (kind : TreeBorrowAccessKind) (c₀ c₁ p : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 4)
    (hneq₀₁ : c₀.tag ≠ c₁.tag) (hneq₀p : c₀.tag ≠ p.tag) (hneq₁p : c₁.tag ≠ p.tag)
    (hc₀par : c₀.parentTag = some p.tag)
    (hc₁par : c₁.parentTag = some p.tag)
    (hppar : p.parentTag = none)
    (hloc₀ : c₀.targetLocal = targetLocal)
    (hloc₁ : c₁.targetLocal = targetLocal)
    (hlocp : p.targetLocal = targetLocal)
    (hproj₀ : c₀.targetProjection = .nil)
    (hproj₁ : c₁.targetProjection = .nil)
    (hprojp : p.targetProjection = .nil)
    (hinv : borrowListBranch3ProtInv [c₀, c₁, p] activeProtectors = true) :
    let nres := (basedNormalTree [c₀, c₁, p] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [c₀, c₁, p] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [c₀, c₁, p] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed →
      TreeBorrowsRel borrows' activeProtectors nres.tree ∧
      borrowListBranch3ProtInv borrows' activeProtectors = true) := by
  dsimp only []
  dsimp only [borrowListBranch3ProtInv] at hinv
  have hnt := basedNormalTree_branch3Prot_eq c₀ c₁ p activeProtectors
    hneq₀p hneq₁p hc₀par hc₁par hppar
  obtain ⟨hub_eq, hafter_eq⟩ := branch3Prot_ub_after_eq kind c₀ c₁ p activeProtectors
    targetLocal start hneq₀₁ hneq₀p hneq₁p hc₀par hc₁par hppar hloc₀ hloc₁ hlocp
    hproj₀ hproj₁ hprojp
  obtain ⟨hlen, htags, htopo, hprot⟩ := annealTableAfterAccess_preserves_shape kind
    [c₀, c₁, p] activeProtectors targetLocal start.val
  obtain ⟨hcore_st, hcore_rel⟩ := branch3Prot_canon_core kind c₀.perm c₁.perm p.perm
    (isBorrowProtected activeProtectors c₀)
    (isBorrowProtected activeProtectors c₁)
    (isBorrowProtected activeProtectors p) start hinv
  rw [hnt, hub_eq]
  refine ⟨hcore_st, fun hc => ?_⟩
  obtain ⟨ht_eq, hp_eq, hperms_eq, hbase_eq, hinv_post⟩ := hcore_rel hc
  have hnt_fields := congrArg (fun t => (t.topology, t.protectedNodes)) hnt
  injection hnt_fields with hnt_topo hnt_prot
  have hprots_eq :
      (annealTableAfterAccess kind [c₀, c₁, p] activeProtectors targetLocal start.val).map
        (isBorrowProtected activeProtectors) =
      (annealTableAfterAccess kind
        (canonBranch3Prot c₀.perm c₁.perm p.perm
          (isBorrowProtected activeProtectors c₀)
          (isBorrowProtected activeProtectors c₁)
          (isBorrowProtected activeProtectors p))
        (canonProts3
          (isBorrowProtected activeProtectors c₀)
          (isBorrowProtected activeProtectors c₁)
          (isBorrowProtected activeProtectors p)) 0 start.val).map
        (isBorrowProtected (canonProts3
          (isBorrowProtected activeProtectors c₀)
          (isBorrowProtected activeProtectors c₁)
          (isBorrowProtected activeProtectors p))) := by
    rw [annealTableAfterAccess_map_isBorrowProtected, annealTableAfterAccess_map_isBorrowProtected]
    simp only [canonBranch3Prot, List.map_cons, List.map_nil,
      isBorrowProtected_canon3_0, isBorrowProtected_canon3_1, isBorrowProtected_canon3_2]
  have hinv' : borrowListBranch3ProtInv
      (annealTableAfterAccess kind [c₀, c₁, p] activeProtectors targetLocal start.val)
      activeProtectors = true := by
    rw [borrowListBranch3ProtInv_eq_of_perms_prots _ _ _ _ hafter_eq hprots_eq]
    exact hinv_post
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hinv'⟩
  · rw [htopo, ht_eq, ← hnt_topo]; rfl
  · rw [htags]; simp [hneq₀₁, hneq₀p, hneq₁p]
  · rw [hlen]; dsimp only [List.length_cons, List.length_nil]; rw [hperms_eq, ← hafter_eq]
  · rw [hlen]; exact hbase_eq
  · rw [hprot, hp_eq, ← hnt_prot]; rfl

section RangedOperational

attribute [local irreducible] Miri.TreeBorrows.Tree.NormalTreeState.performAccess

/-- **`rangedNormalTree_performAccessRange_simulation`**: for any positive
allocation size (`size.bytes ≠ 0`) and any Anneal borrow table `borrows`,
executing Miri's `RangedNormalTreeState.performAccessRange` across the full
byte range `[0, size.bytes)` delegates directly to
`NormalTreeState.performAccess (basedNormalTree borrows activeProtectors)`,
completes iff that normal access completes, and commits the resulting
per-node `locationStates` into the `[0, size.bytes)` range segment. -/
theorem rangedNormalTree_performAccessRange_simulation
    (size : Miri.ABI.Size) (hpos : size.bytes ≠ 0)
    (borrows : List BorrowEntry) (activeProtectors : List Nat)
    (start : Nat) (kind : Miri.TreeBorrows.AccessKind)
    (mode : Miri.TreeBorrows.Tree.ChildrenVisitMode) :
    let nt := basedNormalTree borrows activeProtectors
    let rt := Miri.TreeBorrows.Tree.RangedNormalTreeState.new size
      nt.topology nt.defaultStates nt.protectedNodes nt.locationStates
    let nres := nt.performAccess start kind mode
    let rres := rt.performAccessRange Miri.ABI.Size.ZERO size start kind mode
    rres.locations = #[⟨⟨0, size.bytes⟩, nres⟩] ∧
    (rres.status = .Completed ↔ nres.status = .Completed) ∧
    rres.state.locations = Miri.DataStructures.DedupRangeMap.new size nres.tree.locationStates := by
  dsimp only []
  generalize basedNormalTree borrows activeProtectors = nt
  rcases nt with ⟨topo, defs, prots, locs⟩
  have hiter :
      (Miri.DataStructures.DedupRangeMap.new size locs).iterMut Miri.ABI.Size.ZERO size =
      ⟨Miri.DataStructures.DedupRangeMap.new size locs, #[0], #[⟨⟨0, size.bytes⟩, locs⟩], .ok ()⟩ :=
    Miri.DataStructures.DedupRangeMap.iterMut_new_full size locs hpos
  have hset : ∀ s',
      (Miri.DataStructures.DedupRangeMap.new size locs).setAtPos 0 s' =
      ⟨Miri.DataStructures.DedupRangeMap.new size s', .ok ()⟩ := by
    intro s'
    simp only [Miri.DataStructures.DedupRangeMap.new, hpos, beq_iff_eq, ↓reduceIte]
    rfl
  have hstep :
      (Miri.TreeBorrows.Tree.RangedNormalTreeState.new size topo defs prots locs).performAccessRange
          Miri.ABI.Size.ZERO size start kind mode =
      (Id.run do
        let prepared := (Miri.DataStructures.DedupRangeMap.new size locs).iterMut Miri.ABI.Size.ZERO size
        let mut currentMap := prepared.state
        let mut visited : Array Miri.TreeBorrows.Tree.RangedLocationResult := #[]
        let mut status := Miri.TreeBorrows.Tree.RangedAccessStatus.Completed
        match prepared.outcome with
        | .error error => status := .RangeMapFailure error
        | .ok _ =>
          for cursor in [:prepared.positions.size] do
            if status == .Completed then
              match prepared.positions[cursor]?, prepared.segments[cursor]? with
              | some position, some segment =>
                let tree : Miri.TreeBorrows.Tree.NormalTreeState :=
                  { topology := topo, defaultStates := defs, protectedNodes := prots, locationStates := segment.data }
                let result := tree.performAccess start kind mode
                let mutation := currentMap.setAtPos position result.tree.locationStates
                currentMap := mutation.state
                visited := visited.push ⟨segment.range, result⟩
                match mutation.outcome with
                | .error error => status := .LocationMapFailure segment.range error
                | .ok _ =>
                  if result.status != .Completed then
                    status := .AccessFailure segment.range result.status
              | _, _ =>
                status := .RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size)
        return {
          state := { topology := topo, defaultStates := defs, protectedNodes := prots, locations := currentMap }
          locations := visited
          status := status
        }) := rfl
  rw [hstep, hiter]
  simp +zetaHave only [Id.run, bind, Bind.bind, pure, Pure.pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  cases hstat :
    (({ topology := topo, defaultStates := defs, protectedNodes := prots, locationStates := locs } :
      Miri.TreeBorrows.Tree.NormalTreeState).performAccess start kind mode).status <;>
    simp [hstat, hset, bind, Bind.bind, pure, Pure.pure]

end RangedOperational

end LeanMiriSpec.Correspondence
