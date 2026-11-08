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

end LeanMiriSpec.Correspondence
