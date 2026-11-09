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
(`Miri/TreeBorrows/{Permissions,LocationState,Traversal,NormalTree,RetagPolicy}`).

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
* `retag_pipeline_simulation`: Anneal's initial-permission choices for
  default, two-phase, raw, and function-entry retags are Miri's
  `RetagPolicy.create` choices, and the initial location state Miri builds for
  them is the accessed (or, for `Cell`, lazy) state Anneal's entry stands for.
* `TreeBorrowsRel` and `normalTree_relative_access_simulation` (`I-10`):
  Anneal's `parentTag` ancestor walk (`isBorrowDescendantOrSelf`) computes
  exactly the ancestor path Miri's tree visitor (`TraversalTree.ancestorPath`)
  marks as `LocalAccess`, and every Anneal per-entry tree update is the
  corresponding Miri location transition.
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
    | .ok _ => { afterAccess with outcome := .ok prov, events := afterAccess.events.push (.reborrowReturned prov) }
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
