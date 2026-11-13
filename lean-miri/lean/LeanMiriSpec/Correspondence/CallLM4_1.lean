/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.TreeBorrowsRel
import LeanMiriSpec.Correspondence.Simulation
import LeanMiriSpec.Correspondence.LayoutLM2_2
import LeanMiriSpec.Correspondence.SimLM3_3
import Miri.Interpreter.Call

/-!
# Multi-Frame Call Stack & `CallId` Protector Correspondence (`LM-4.1`)

Formal correspondence between Anneal's multi-frame call stack
(`s.memory.callStack`, `s.memory.activeCallee`, `s.memory.callees`,
`s.memory.activeProtectors`, `s.memory.nextProtector`, `s.memory.callerLocals`
in `Trusted/Rustc/V2026_06_01/MirSemantics/{State,Terminators,Machine}.lean`)
and `lean-miri`'s `Miri/Interpreter/{Stack,Call,Step,ControlFlow}.lean` +
`Miri/TreeBorrows/{TreeState,GlobalState}.lean`:

1. **Active-`CallId` Protector Validity, `GlobalState.endCall`, and End-of-Call
   Access Divergence (`ActiveProtectorsValid`, `BorrowTrackerStackRel`,
   `borrowTree_protectorEndAccess_simulation`, `borrowTree_releaseProtector_full_simulation`,
   `cex_end_of_call_foreign_unique_frozen_divergence`)**:
   * In Miri's `BorrowTree.releaseProtector` (`Miri/TreeBorrows/TreeState.lean`),
     releasing a protected tag at function exit performs an implicit read/write
     (`Permission.associatedAccess` with `ChildrenVisitMode.SkipChildrenOfAccessed`)
     at every accessed location before `GlobalState.endCall` removes the frame's
     tags from `protectedTags`.
   * On the 2-node parent-child tree `hooksTwoNodeTree perm` (`[parent{Disabled}, child{perm}]`),
     for all 6 non-`.disabled` `TreeBorrowPerm` values (`Cell`, `ReservedFrz false`,
     `ReservedFrz true`, `ReservedIM`, `Unique`, `Frozen`), this implicit
     end-of-call access succeeds (`status = .Released`) and leaves the 2-node
     tree unchanged (`res.tree = tree`), while `.disabled` fails with
     `ChildAccessForbidden .Disabled`.
   * On general multi-node trees containing a foreign (sibling/ancestor) `Unique`
     node, Miri's end-of-call access acts as a foreign access to non-descendant
     nodes and freezes foreign `Unique` nodes to `Frozen`, whereas Anneal's
     Stage-1 `Trusted` `TerminatorKind.return_` (`Terminators.lean:3005-3039`,
     `restoreCallerProtectors`) restores `activeProtectors` without running an
     end-of-call `performAccess` pass on
     `s.memory.borrows` (certified as a divergence in
     `cex_end_of_call_foreign_unique_frozen_divergence`).
   * At the global borrow-tracker layer (`Miri.TreeBorrows.GlobalState`),
     `annealControlHooksLM4_1.popFrame` invokes `GlobalState.endCall` on
     `m.machine.borrowTracker` with the popped callee frame's `FrameState`
     (`annealPoppedFrameState s`), maintaining `BorrowTrackerStackRel` in
     lockstep with Anneal's `activeProtectors` across call and return while
     leaving `GlobalState.rootPointerTags` untouched.
2. **Depth-1 `TreeBorrowsStateRel` & Arbitrary-Depth `MultiFrameStateRel`
   (`CallStackStateRel`)**:
   * `FrameStackRel` (`List.Forall₂` of `FrameRel`) relates Anneal's caller stack
     plus active frame `s.memory.callStack.map (fun cf => (cf.callerBody, cf.frame))`
     and `(activeBody, s.frame)` to `m.stack.frames.toList.reverse`. Local values
     are related by `ImmediateRel` / `MemPlaceRel` in the pointer-free scalar,
     scalar-pair, unit, and array fragment (`ImmediateRel` has no pointer case;
     cross-frame `BorrowEntry.targetLocal` scoping in `Trusted` is documented and
     certified in `WitLM4_1.lean`; and for ZST `_0` such as `()`, `Trusted`'s
     `TerminatorKind.return_` faults with UB when `_0 = .uninit` where `RemoveZsts`
     strips `_0 = const ()`, whereas canonical Miri returns normally, which is
     captured by the explicit `hzst_init` hypothesis on return simulation).
   * `CallerDestinationRel` and `CallerStackLinksRel` relate every caller frame's
     `destination`, `returnTarget`, `callerProtector`, and `calleeProtectors` to
     the corresponding Miri frame's `returnPlace` (both `.frameLocal` immediate
     and `.memory` indirect places) and `returnContinuation`
     (`.goto (some cf.returnTarget)` for frames pushed by a returning call,
     `.goto none` for frames pushed by a diverging call with
     `cf.isDiverging = true` (Stage-1 `pushDivergingCalleeFrame`), and
     `.stop false` for the root frame).
   * `MultiFrameAllocDisjoint` ensures that all live `.indirect` stack allocations
     across the entire call stack have pairwise distinct `AllocId`s, so popping
     and deallocating a callee frame's `.indirect` locals preserves every caller
     frame's `FrameRel`.
   * Bidirectional depth-1 bridge theorems (`StateRel.toTreeBorrowsStateRel`,
     `TreeBorrowsStateRel.toStateRel_of_empty`, `StateRel.iff_multiFrameStateRel_depth1`,
     `TreeBorrowsStateRel.iff_multiFrameStateRel_depth1`) connect `MultiFrameStateRel`
     to `StateRel` and `TreeBorrowsStateRel` without touching `Relation.lean` or
     `TreeBorrowsRel.lean`.
-/

namespace List

/-- Standard pairwise list relation `List.Forall₂ R xs ys` relating two lists of
equal length element-by-element under `R`. -/
inductive Forall₂ {α β : Type _} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

theorem Forall₂.length_eq {α β : Type _} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : Forall₂ R xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Forall₂.append {α β : Type _} {R : α → β → Prop}
    {xs₁ xs₂ : List α} {ys₁ ys₂ : List β}
    (h₁ : Forall₂ R xs₁ ys₁) (h₂ : Forall₂ R xs₂ ys₂) :
    Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hab _ ih => exact .cons hab ih

theorem Forall₂.reverse {α β : Type _} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : Forall₂ R xs ys) : Forall₂ R xs.reverse ys.reverse := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    simp only [List.reverse_cons]
    exact ih.append (.cons hab .nil)

theorem forall₂_reverse_iff {α β : Type _} {R : α → β → Prop} {xs : List α} {ys : List β} :
    Forall₂ R xs.reverse ys.reverse ↔ Forall₂ R xs ys := by
  constructor
  · intro h
    have h' := h.reverse
    simpa [List.reverse_reverse] using h'
  · exact Forall₂.reverse

end List

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Active-`CallId` Protector Validity & `BorrowTree.releaseProtector` Correspondence -/

deriving instance DecidableEq for TreeBorrowPerm

/-- Well-formedness invariant on active `CallId` protectors:
every borrow entry in `borrows` whose `protector` is currently active in
`activeProtectors` has `perm ≠ .disabled`.

In Anneal (`Places.lean`, `Statements.lean`), any foreign read/write that would
disable an active-protected tag is eagerly rejected with `.fail .ub` at the
access site, and `RetagKind.fnEntry` refuses to create a child of a `.disabled`
parent. Consequently, `ActiveProtectorsValid` holds initially (`activeProtectors = []`)
and is an inductive invariant across all non-UB MIR steps. Under
`ActiveProtectorsValid`, the local end-of-call protector access
(`Permission.associatedAccess`) at the released node itself succeeds without
changing that node's permission (and on the 2-node parent-child tree
`hooksTwoNodeTree perm` with a `.Disabled` parent, leaves the 2-node tree
unchanged). On multi-node trees containing a foreign `Unique` node, Miri's
end-of-call access also acts as a foreign access that freezes foreign `Unique`
nodes to `Frozen`, whereas Anneal's `Trusted` `TerminatorKind.return_` only
restores `activeProtectors` (see `cex_end_of_call_foreign_unique_frozen_divergence`). -/
def ActiveProtectorsValid (borrows : List BorrowEntry) (activeProtectors : List Nat) : Prop :=
  ∀ e ∈ borrows, isBorrowProtected activeProtectors e = true → e.perm ≠ .disabled

/-- Boolean test for whether a `TreeBorrowPerm` is `.disabled`. -/
def isDisabledPerm : TreeBorrowPerm → Bool
  | .disabled => true
  | _ => false

/-- Boolean decision procedure for `ActiveProtectorsValid`. -/
def activeProtectorsValidB (borrows : List BorrowEntry) (activeProtectors : List Nat) : Bool :=
  borrows.all fun e => !(isBorrowProtected activeProtectors e && isDisabledPerm e.perm)

theorem activeProtectorsValid_iff_bool
    (borrows : List BorrowEntry) (activeProtectors : List Nat) :
    ActiveProtectorsValid borrows activeProtectors ↔
      activeProtectorsValidB borrows activeProtectors = true := by
  unfold ActiveProtectorsValid activeProtectorsValidB
  rw [List.all_eq_true]
  constructor
  · intro h e he
    have hne := h e he
    cases hp : isBorrowProtected activeProtectors e <;>
      (rcases hd : e.perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;>
      simp_all [isDisabledPerm]
  · intro h e he hprot hdis
    have he' := h e he
    simp [hprot, hdis, isDisabledPerm] at he'

instance instDecidableActiveProtectorsValid
    (borrows : List BorrowEntry) (activeProtectors : List Nat) :
    Decidable (ActiveProtectorsValid borrows activeProtectors) :=
  decidable_of_iff' (activeProtectorsValidB borrows activeProtectors = true)
    (activeProtectorsValid_iff_bool borrows activeProtectors)

/-- `ActiveProtectorsValid` holds trivially when `activeProtectors = []`. -/
theorem ActiveProtectorsValid.nil (borrows : List BorrowEntry) :
    ActiveProtectorsValid borrows [] := by
  intro e _ hprot
  cases hp : e.protector <;> simp [isBorrowProtected, natListContainsBool, hp] at hprot

theorem natListContainsBool_iff_mem (xs : List Nat) (x : Nat) :
    natListContainsBool xs x = true ↔ x ∈ xs := by
  induction xs with
  | nil =>
    simp [natListContainsBool]
  | cons y ys ih =>
    simp only [natListContainsBool, List.mem_cons]
    cases h : Nat.beq y x with
    | true =>
      have heq : y = x := Nat.eq_of_beq_eq_true h
      exact ⟨fun _ => Or.inl heq.symm, fun _ => rfl⟩
    | false =>
      have hne : x ≠ y := fun heq => by
        rw [heq, Nat.beq_refl] at h
        cases h
      exact ⟨fun hys => Or.inr (ih.mp hys), fun hmem => ih.mpr (hmem.resolve_left hne)⟩

theorem natListContainsBool_append_right (xs ys : List Nat) (x : Nat)
    (h : natListContainsBool ys x = true) :
    natListContainsBool (xs ++ ys) x = true := by
  rw [natListContainsBool_iff_mem] at h ⊢
  exact List.mem_append_right xs h

/-- Changing `activeProtectors` to `prots'` preserves `TreeBorrowsRel` on
`basedNormalTree borrows prots'` whenever `TreeBorrowsRel` already holds for
`prots`. -/
theorem TreeBorrowsRel.change_protectors
    {borrows : List BorrowEntry} {prots : List Nat}
    (htb : TreeBorrowsRel borrows prots (basedNormalTree borrows prots))
    (prots' : List Nat) :
    TreeBorrowsRel borrows prots' (basedNormalTree borrows prots') :=
  ⟨rfl, htb.tags_unique, htb.perms, htb.base_unique, rfl⟩

/-- Popping or filtering out a frame's released `CallId`(s) from `activeProtectors`
preserves `ActiveProtectorsValid` for any subset of remaining protectors. -/
theorem ActiveProtectorsValid.mono_protectors
    {borrows : List BorrowEntry} {prots prots' : List Nat}
    (h : ActiveProtectorsValid borrows prots)
    (hsub : ∀ cid, natListContainsBool prots' cid = true → natListContainsBool prots cid = true) :
    ActiveProtectorsValid borrows prots' := by
  intro e he hprot'
  apply h e he
  cases hp : e.protector with
  | none => simp [isBorrowProtected, hp] at hprot'
  | some cid =>
    simp only [isBorrowProtected, hp] at hprot' ⊢
    exact hsub cid hprot'

/-- Adding a newly retagged `FnEntry` borrow entry with `perm ≠ .disabled`
preserves `ActiveProtectorsValid` under the same `activeProtectors`. -/
theorem ActiveProtectorsValid.cons_of_ne_disabled
    {e : BorrowEntry} {borrows : List BorrowEntry} {prots : List Nat}
    (hne : e.perm ≠ .disabled)
    (h : ActiveProtectorsValid borrows prots) :
    ActiveProtectorsValid (e :: borrows) prots := by
  intro x hx hprot
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hne
  · exact h x hx' hprot

/-- Pushing a fresh `CallId` (`freshCallId`) onto `activeProtectors` when
entering a callee frame preserves `ActiveProtectorsValid` whenever no existing
entry in `borrows` already carries `protector = some freshCallId`. -/
theorem ActiveProtectorsValid.push_fresh_callId
    {borrows : List BorrowEntry} {prots : List Nat} {freshCallId : Nat}
    (h : ActiveProtectorsValid borrows prots)
    (hfresh : ∀ e ∈ borrows, e.protector ≠ some freshCallId) :
    ActiveProtectorsValid borrows (freshCallId :: prots) := by
  intro e he hprot
  apply h e he
  cases hp : e.protector with
  | none => simp [isBorrowProtected, hp] at hprot
  | some cid =>
    have hne : freshCallId ≠ cid := by
      intro heq
      exact hfresh e he (hp.trans (congrArg some heq.symm))
    have hbeq : Nat.beq freshCallId cid = false := by
      cases h : Nat.beq freshCallId cid with
      | false => rfl
      | true => exact False.elim (hne (Nat.eq_of_beq_eq_true h))
    simpa [isBorrowProtected, hp, natListContainsBool, hbeq] using hprot

/-- Associated access kind performed by Miri's `BorrowTree.releaseProtector`
(`Permission.associatedAccess` in `Miri/TreeBorrows/Permissions.lean`):
`none` for `.cell`, `some .Write` for `.unique`, and `some .Read` for all other
permissions. -/
def annealAssociatedAccess (perm : TreeBorrowPerm) : Option Miri.TreeBorrows.AccessKind :=
  (annealPermToMiri perm).associatedAccess

private theorem hooksTwoNodes_entries_lm4_1 :
    hooksTwoNodes.entries =
      #[(⟨0⟩, ⟨retagParentTag, none, #[⟨1⟩], .Disabled, .None, false, none⟩),
        (⟨1⟩, ⟨retagChildTag, some ⟨0⟩, #[], .Disabled, .None, false, none⟩)] := by
  unfold hooksTwoNodes Miri.TreeBorrows.UniValMap.entries
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  decide

private def hooksFailingNodeSkip? : Miri.TreeBorrows.Tree.NormalAccessStatus → Option Nat
  | .Completed => none
  | .TransitionError node _
  | .RecordDebugAssertion node
  | .PermissionInvariantFailure node
  | .TransitionApplicationInvariantFailure node
  | .PossibleInvariantFailure node
  | .MissingLocationState node => some node

private def hooksExpectedNormalProjSkip (perm : TreeBorrowPerm)
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

private def hooksExpectedPerformAtSkip (perm : TreeBorrowPerm)
    (ents : Array (Miri.TreeBorrows.UniIndex × Miri.TreeBorrows.TreeNode))
    (kind : Miri.TreeBorrows.AccessKind) (isProtected : Bool) :
    Miri.TreeBorrows.BorrowTree.NormalLocationAccessResult := Id.run do
  let tree := hooksTwoNodeTree perm
  let location := hooksLocTree perm
  let protectedTags := (hooksForChildProtected isProtected).protectedTags
  let access := Miri.TreeBorrows.Tree.NormalTreeState.performAccess
    (hooksExpectedNormalProjSkip perm ents isProtected)
    (⟨1⟩ : Miri.TreeBorrows.UniIndex).toNat kind .SkipChildrenOfAccessed
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
          if node.isExposed && hooksFailingNodeSkip? access.status != some event.node then
            match tree.locationStateAt location index, access.tree.stateAt event.node with
            | some oldState, some newState =>
                match Miri.TreeBorrows.performAccessTransition
                    kind event.relatedness oldState.permission
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

section NormalAccessAtSkipStep

attribute [local irreducible] Miri.TreeBorrows.UniValMap.entries
attribute [local irreducible] Miri.TreeBorrows.Tree.NormalTreeState.performAccess

private theorem performNormalAccessAt_skip_eq_expected
    (perm : TreeBorrowPerm) (kind : Miri.TreeBorrows.AccessKind) (isProtected : Bool) :
    (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
      ⟨1⟩ kind (hooksForChildProtected isProtected).protectedTags .SkipChildrenOfAccessed =
    hooksExpectedPerformAtSkip perm hooksTwoNodes.entries kind isProtected := by
  cases kind <;> (rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _) <;> cases isProtected <;> rfl

end NormalAccessAtSkipStep

private theorem hooksExpectedNormalProjSkip_eq (perm : TreeBorrowPerm) (isProtected : Bool) :
    hooksExpectedNormalProjSkip perm
        #[(⟨0⟩, ⟨retagParentTag, none, #[⟨1⟩], .Disabled, .None, false, none⟩),
          (⟨1⟩, ⟨retagChildTag, some ⟨0⟩, #[], .Disabled, .None, false, none⟩)]
        isProtected =
      { topology := ⟨#[⟨none, [1]⟩, ⟨some 0, []⟩]⟩
        defaultStates := #[⟨.Disabled, false, .None⟩, ⟨.Disabled, false, .None⟩]
        protectedNodes := if isProtected then [1] else []
        locationStates :=
          #[some ⟨.Unique, true, .None⟩, some ⟨annealPermToMiri perm, true, .None⟩] } := by
  cases isProtected <;>
    simp [hooksExpectedNormalProjSkip, hooksTwoNodeTree, hooksTwoNodes, hooksLocTree,
      hooksForChildProtected, Miri.TreeBorrows.TreeNode.defaultLocationState,
      Miri.TreeBorrows.UniIndex.ofNat?, Miri.TreeBorrows.UniIndex.toNat,
      Miri.TreeBorrows.UniValMap.get,
      Miri.TreeBorrows.ProtectedTags.contains, Miri.TreeBorrows.ProtectedTags.get,
      Miri.TreeBorrows.ProtectedTags.insert, retagParentTag, retagChildTag,
      Miri.Memory.BorTag.one]

/-- Access kind performed by Miri's end-of-call protector release for any
non-`Cell` permission (`.Write` for `.unique`, `.Read` otherwise). -/
def protectorEndAccessKind : TreeBorrowPerm → Miri.TreeBorrows.AccessKind
  | .unique => .Write
  | _ => .Read

private def protectorEndAccessGoal (perm : TreeBorrowPerm) : Prop :=
  let borrows : List BorrowEntry :=
    [{ tag := 2, targetLocal := 1, targetProjection := [], perm := perm,
       protector := some 1, parentTag := some 1 },
     { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique,
       protector := none, parentTag := none }]
  let kind := protectorEndAccessKind perm
  let norm := (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
    ⟨1⟩ kind (hooksForChildProtected true).protectedTags .SkipChildrenOfAccessed
  let nres := (basedNormalTree borrows [1]).performAccess 0 kind .SkipChildrenOfAccessed
  (perm ≠ .cell → annealAssociatedAccess perm = some kind) ∧
  norm.outcome = .ok () ∧
  norm.access.root = 0 ∧
  (norm.access.status = .Completed ↔ perm ≠ .disabled) ∧
  (nres.status = .Completed ↔ perm ≠ .disabled) ∧
  (perm = .disabled →
    norm.access.status = .TransitionError 1 (.ChildAccessForbidden .Disabled) ∧
    nres.status = .TransitionError 0 (.ChildAccessForbidden .Disabled)) ∧
  (perm ≠ .disabled →
    norm.location = hooksLocTree perm ∧
    normalTreePerms nres.tree borrows.length = borrows.map (fun e => some e.perm))

private theorem protectorEndAccessGoal_holds (perm : TreeBorrowPerm) :
    protectorEndAccessGoal perm := by
  dsimp only [protectorEndAccessGoal]
  rw [performNormalAccessAt_skip_eq_expected, hooksTwoNodes_entries_lm4_1]
  unfold hooksExpectedPerformAtSkip
  rw [hooksExpectedNormalProjSkip_eq]
  rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;>
  · simp +zetaHave only [protectorEndAccessKind, annealAssociatedAccess,
      Id.run, bind, Bind.bind, pure, Pure.pure,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    decide

private theorem protectorEndAccess_treeBorrowsRel (perm : TreeBorrowPerm) :
    let borrows : List BorrowEntry :=
      [{ tag := 2, targetLocal := 1, targetProjection := [], perm := perm,
         protector := some 1, parentTag := some 1 },
       { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique,
         protector := none, parentTag := none }]
    TreeBorrowsRel borrows [] (basedNormalTree borrows []) := by
  rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;>
    exact ⟨by decide, by decide, rfl, rfl, rfl⟩

/-- **`borrowTree_protectorEndAccess_simulation`**:
Miri's end-of-call protector release access across all 7 `TreeBorrowPerm` states
(`BorrowTree.performNormalAccessAt` and `NormalTreeState.performAccess` with
`ChildrenVisitMode.SkipChildrenOfAccessed` and `annealAssociatedAccess perm` at
`BorrowTree.releaseProtector`, `TreeState.lean:1053`):
1. For `.cell`, `annealAssociatedAccess .cell = none` (no tree access is
   performed, and `TreeBorrowsRel` holds directly after removing the protector);
2. For all 5 non-`.cell`, non-`.disabled` permissions (`ReservedFrz false`,
   `ReservedFrz true`, `ReservedIM`, `Unique`, `Frozen`), `annealAssociatedAccess perm = some kind`
   where `performNormalAccessAt` and `basedNormalTree.performAccess` with
   `.SkipChildrenOfAccessed` both succeed (`status = .Completed`), preserve all
   location permissions (`norm.location = hooksLocTree perm` and
   `normalTreePerms nres.tree borrows.length = borrows.map (fun e => some e.perm)`),
   and preserve `TreeBorrowsRel` when the protector is removed (`activeProtectors = []`);
3. For `.disabled`, `annealAssociatedAccess .disabled = some .Read`, and both
   `performNormalAccessAt` and `basedNormalTree.performAccess` fail with
   `.TransitionError _ (.ChildAccessForbidden .Disabled)` (which is why
   `ActiveProtectorsValid` is required and maintained by Anneal's eager
   protected-disable UB check). -/
theorem borrowTree_protectorEndAccess_simulation (perm : TreeBorrowPerm) :
    let borrows : List BorrowEntry :=
      [{ tag := 2, targetLocal := 1, targetProjection := [], perm := perm,
         protector := some 1, parentTag := some 1 },
       { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique,
         protector := none, parentTag := none }]
    (perm = .cell →
      annealAssociatedAccess perm = none ∧
      TreeBorrowsRel borrows [] (basedNormalTree borrows [])) ∧
    (perm ≠ .cell →
      ∃ kind,
        annealAssociatedAccess perm = some kind ∧
        let norm := (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
          ⟨1⟩ kind (hooksForChildProtected true).protectedTags .SkipChildrenOfAccessed
        let nres := (basedNormalTree borrows [1]).performAccess 0 kind .SkipChildrenOfAccessed
        norm.outcome = .ok () ∧
        norm.access.root = 0 ∧
        (norm.access.status = .Completed ↔ perm ≠ .disabled) ∧
        (nres.status = .Completed ↔ perm ≠ .disabled) ∧
        (perm = .disabled →
          norm.access.status = .TransitionError 1 (.ChildAccessForbidden .Disabled) ∧
          nres.status = .TransitionError 0 (.ChildAccessForbidden .Disabled)) ∧
        (perm ≠ .disabled →
          norm.location = hooksLocTree perm ∧
          normalTreePerms nres.tree borrows.length = borrows.map (fun e => some e.perm) ∧
          TreeBorrowsRel borrows [] (basedNormalTree borrows []))) := by
  have hg := protectorEndAccessGoal_holds perm
  dsimp only [protectorEndAccessGoal] at hg
  obtain ⟨hassoc, hout, hroot, hst1, hst2, hdis, hvalid⟩ := hg
  have hrel := protectorEndAccess_treeBorrowsRel perm
  refine ⟨fun hcell => ?_, fun hne => ⟨protectorEndAccessKind perm, hassoc hne,
    hout, hroot, hst1, hst2, hdis, fun hnd => ⟨(hvalid hnd).1, (hvalid hnd).2, hrel⟩⟩⟩
  subst hcell
  exact ⟨rfl, hrel⟩

section ReleaseProtectorOperational

attribute [local irreducible] Miri.TreeBorrows.BorrowTree.performNormalAccessAt

private theorem hooksTwoNodeTree_indexOfTag_child (perm : TreeBorrowPerm) :
    (hooksTwoNodeTree perm).indexOfTag retagChildTag = some ⟨1⟩ := rfl

private theorem hooksTwoNodeTree_indexOfTag_99 (perm : TreeBorrowPerm) :
    (hooksTwoNodeTree perm).indexOfTag ⟨99, by decide⟩ = none := by
  rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;> decide

private theorem hooksTwoNodeTree_locations_entries_size (perm : TreeBorrowPerm) :
    (hooksTwoNodeTree perm).locations.entries.size = 1 := rfl

private theorem hooksTwoNodeTree_locations_index_zero (perm : TreeBorrowPerm) :
    (hooksTwoNodeTree perm).locations.index 0 = .ok ⟨⟨0, 8⟩, hooksLocTree perm⟩ := rfl

private theorem hooksTwoNodeTree_locations_setAtPos_zero
    (perm : TreeBorrowPerm) (loc' : Miri.TreeBorrows.LocationTree) :
    (hooksTwoNodeTree perm).locations.setAtPos 0 loc' =
      ⟨Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) loc', .ok ()⟩ := rfl

private theorem hooksTwoNodeTree_roots_eq (perm : TreeBorrowPerm) :
    (hooksTwoNodeTree perm).roots = #[⟨0⟩] := rfl

private theorem hooksTwoNodeTree_updateExposure_child (perm : TreeBorrowPerm) :
    (hooksTwoNodeTree perm).updateExposureForProtectorRelease retagChildTag =
      ⟨hooksTwoNodeTree perm, .ok ()⟩ := by
  rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;> decide

private theorem hooksTwoNodeTree_updateExposure_child_loc
    (perm : TreeBorrowPerm) (loc : Miri.TreeBorrows.LocationTree) :
    ({ tagMapping := (hooksTwoNodeTree perm).tagMapping
       nodes := (hooksTwoNodeTree perm).nodes
       locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) loc
       roots := (hooksTwoNodeTree perm).roots : Miri.TreeBorrows.BorrowTree }.updateExposureForProtectorRelease
      retagChildTag) =
    ⟨{ tagMapping := (hooksTwoNodeTree perm).tagMapping
       nodes := (hooksTwoNodeTree perm).nodes
       locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) loc
       roots := (hooksTwoNodeTree perm).roots }, .ok ()⟩ := by
  rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;> rfl

private theorem releaseProtector_loop_snd
    (opt : Option Miri.TreeBorrows.BorrowTree.BorrowTreeAccessStatus)
    (c : Miri.TreeBorrows.BorrowTree) :
    (match
      (match opt with
       | some status =>
         ForInStep.done
           (MProd.mk
             (some
               ({ tree := c
                  status := Miri.TreeBorrows.BorrowTree.ProtectorReleaseStatus.AccessFailure
                    { start := 0, stop := 8 } status } :
                 Miri.TreeBorrows.BorrowTree.ProtectorReleaseResult))
             c)
       | none => ForInStep.yield (MProd.mk none c)) with
     | ForInStep.done b => b
     | ForInStep.yield b => b).snd = c := by
  cases opt <;> rfl

private theorem releaseProtector_loop_outer
    (opt : Option Miri.TreeBorrows.BorrowTree.BorrowTreeAccessStatus)
    (c : Miri.TreeBorrows.BorrowTree)
    (d : Miri.TreeBorrows.BorrowTree.ProtectorReleaseResult) :
    (match
      (match
        (match opt with
         | some status =>
           ForInStep.done
             (MProd.mk
               (some
                 ({ tree := c
                    status := Miri.TreeBorrows.BorrowTree.ProtectorReleaseStatus.AccessFailure
                      { start := 0, stop := 8 } status } :
                   Miri.TreeBorrows.BorrowTree.ProtectorReleaseResult))
               c)
         | none => ForInStep.yield (MProd.mk none c)) with
       | ForInStep.done b => b
       | ForInStep.yield b => b).fst with
     | some r => r
     | none => d) =
    match opt with
    | some status =>
      { tree := c
        status := Miri.TreeBorrows.BorrowTree.ProtectorReleaseStatus.AccessFailure
          { start := 0, stop := 8 } status }
    | none => d := by
  cases opt <;> rfl

private theorem hooksLocTree_perms_get_child (perm : TreeBorrowPerm) :
    (hooksLocTree perm).perms.get ⟨1⟩ = some ⟨annealPermToMiri perm, true, .None⟩ := by
  dsimp only [hooksLocTree, Miri.TreeBorrows.UniValMap.get, Miri.TreeBorrows.UniIndex.toNat]
  rfl

private theorem uniIndex_ofNat_zero_eq :
    Miri.TreeBorrows.UniIndex.ofNat? 0 = some ⟨0⟩ := rfl

private theorem forIn'_cons_match_ite_yield_fst {α β γ : Type} (p : Prop) [Decidable p]
    (x : α) (y : β) (z₁ z₂ : γ) :
    (List.forIn'_cons.match_1 (fun _ => Id (α × β × γ))
      (if p then ForInStep.yield (x, y, z₁) else ForInStep.yield (x, y, z₂))
      (fun b => b) (fun b => b)).fst = x := by
  by_cases hp : p <;> simp [hp]

private theorem forIn'_cons_match_ite_yield_snd_fst {α β γ : Type} (p : Prop) [Decidable p]
    (x : α) (y : β) (z₁ z₂ : γ) :
    (List.forIn'_cons.match_1 (fun _ => Id (α × β × γ))
      (if p then ForInStep.yield (x, y, z₁) else ForInStep.yield (x, y, z₂))
      (fun b => b) (fun b => b)).snd.fst = y := by
  by_cases hp : p <;> simp [hp]

/-- **`borrowTree_releaseProtector_full_simulation`**:
Miri's operational `BorrowTree.releaseProtector` (`TreeState.lean:1036`) on
`hooksTwoNodeTree perm` for `retagChildTag` across **all 7** `TreeBorrowPerm`
constructors:
1. succeeds (`res.status = .Released`) iff `perm ≠ .disabled`;
2. whenever `perm ≠ .disabled` (all 6 valid active-protected permissions under
   `ActiveProtectorsValid`), leaves the `BorrowTree` unchanged
   (`res.tree = hooksTwoNodeTree perm`);
3. when `perm = .disabled`, fails with
   `.AccessFailure ⟨0, 8⟩ (.AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled)))`.
4. For any tag not present in `tree.tagMapping` (e.g. `BorTag ⟨99, _⟩`),
   `BorrowTree.releaseProtector` returns `.MissingTag`. -/
theorem borrowTree_releaseProtector_full_simulation (perm : TreeBorrowPerm) :
    let tree := hooksTwoNodeTree perm
    let res := tree.releaseProtector retagChildTag (hooksForChildProtected true).protectedTags
    (res.status = .Released ↔ perm ≠ .disabled) ∧
    (perm ≠ .disabled → res.tree = tree) ∧
    (perm = .disabled →
      res.status =
        .AccessFailure ⟨0, 8⟩
          (.AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled)))) ∧
    ((hooksTwoNodeTree perm).releaseProtector ⟨99, by decide⟩
        (hooksForChildProtected true).protectedTags).status =
      .MissingTag ⟨99, by decide⟩ := by
  have hmiss :
      ((hooksTwoNodeTree perm).releaseProtector ⟨99, by decide⟩
        (hooksForChildProtected true).protectedTags).status =
      .MissingTag ⟨99, by decide⟩ := by
    unfold Miri.TreeBorrows.BorrowTree.releaseProtector
    dsimp only [Id.run]
    rw [hooksTwoNodeTree_indexOfTag_99 perm]
    rfl
  by_cases hcell : perm = .cell
  · subst hcell
    have hrel_cell :
        (hooksTwoNodeTree .cell).releaseProtector retagChildTag
          (hooksForChildProtected true).protectedTags =
        ⟨hooksTwoNodeTree .cell, .Released⟩ := by
      unfold Miri.TreeBorrows.BorrowTree.releaseProtector
      dsimp only [Id.run]
      rw [hooksTwoNodeTree_indexOfTag_child .cell,
        hooksTwoNodeTree_locations_entries_size .cell]
      simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
        List.range', List.forIn_cons, List.forIn_nil,
        bind, Bind.bind, pure, Pure.pure]
      rw [hooksTwoNodeTree_locations_index_zero .cell]
      dsimp only []
      rw [hooksLocTree_perms_get_child .cell]
      dsimp only [annealPermToMiri, Miri.TreeBorrows.Permission.associatedAccess,
        pure, Pure.pure, bind, Bind.bind]
      rw [hooksTwoNodeTree_updateExposure_child .cell]
    dsimp only []
    rw [hrel_cell]
    exact ⟨⟨(fun _ h => nomatch h), (fun _ => rfl)⟩, (fun _ => rfl), (fun h => nomatch h), hmiss⟩
  · obtain ⟨_, hnoncell⟩ := borrowTree_protectorEndAccess_simulation perm
    obtain ⟨kind, hassoc, hout, hroot, hst_iff, _, hdis_err, hvalid_loc⟩ := hnoncell hcell
    have hassoc' : (annealPermToMiri perm).associatedAccess = some kind := hassoc
    let norm := (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
      ⟨1⟩ kind (hooksForChildProtected true).protectedTags .SkipChildrenOfAccessed
    have hnorm_eq : norm =
        ⟨norm.location, ⟨norm.access.tree, 0, norm.access.visited, norm.access.status⟩, .ok ()⟩ := by
      dsimp only [norm]
      rw [← hout, ← hroot]
    by_cases hdis : perm = .disabled
    · subst hdis
      have herr_st : norm.access.status = .TransitionError 1 (.ChildAccessForbidden .Disabled) :=
        (hdis_err rfl).1
      have hnorm_dis :
          (hooksTwoNodeTree .disabled).performNormalAccessAt (hooksLocTree .disabled)
            ⟨1⟩ kind (hooksForChildProtected true).protectedTags .SkipChildrenOfAccessed =
          ⟨norm.location,
            ⟨norm.access.tree, 0, norm.access.visited,
              .TransitionError 1 (.ChildAccessForbidden .Disabled)⟩,
            .ok ()⟩ := by
        rw [← herr_st]; exact hnorm_eq
      have hrel_dis :
          ((hooksTwoNodeTree .disabled).releaseProtector retagChildTag
            (hooksForChildProtected true).protectedTags).status =
          .AccessFailure ⟨0, 8⟩
            (.AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled))) := by
        unfold Miri.TreeBorrows.BorrowTree.releaseProtector
        dsimp only [Id.run]
        rw [hooksTwoNodeTree_indexOfTag_child .disabled,
          hooksTwoNodeTree_locations_entries_size .disabled]
        simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
          Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
          List.range', List.forIn_cons, List.forIn_nil,
          bind, Bind.bind, pure, Pure.pure]
        rw [hooksTwoNodeTree_locations_index_zero .disabled]
        dsimp only []
        rw [hooksLocTree_perms_get_child .disabled]
        dsimp only []
        rw [hassoc']
        simp only [↓reduceIte]
        rw [hooksTwoNodeTree_locations_setAtPos_zero .disabled]
        dsimp only [bind, Bind.bind, pure, Pure.pure]
        conv =>
          lhs
          arg 1
          arg 2
          arg 1
          arg 2
          arg 2
          arg 1
          whnf
          rw [hnorm_dis]
        rfl
      dsimp only []
      rw [hrel_dis]
      exact ⟨⟨(fun h => nomatch h), (fun hne => False.elim (hne rfl))⟩,
        (fun hne => False.elim (hne rfl)), (fun _ => rfl), hmiss⟩
    · obtain ⟨hloc_eq, _, _⟩ := hvalid_loc hdis
      have hcomp : norm.access.status = .Completed := hst_iff.mpr hdis
      have hnorm_ok :
          (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
            ⟨1⟩ kind (hooksForChildProtected true).protectedTags .SkipChildrenOfAccessed =
          ⟨hooksLocTree perm, ⟨norm.access.tree, 0, norm.access.visited, .Completed⟩, .ok ()⟩ := by
        calc
          (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
              ⟨1⟩ kind (hooksForChildProtected true).protectedTags .SkipChildrenOfAccessed
            = ⟨norm.location, ⟨norm.access.tree, 0, norm.access.visited, norm.access.status⟩, .ok ()⟩ :=
              hnorm_eq
          _ = ⟨hooksLocTree perm, ⟨norm.access.tree, 0, norm.access.visited, .Completed⟩, .ok ()⟩ := by
              rw [hloc_eq, hcomp]
      have hrel_ok :
          (hooksTwoNodeTree perm).releaseProtector retagChildTag
            (hooksForChildProtected true).protectedTags =
          ⟨hooksTwoNodeTree perm, .Released⟩ := by
        unfold Miri.TreeBorrows.BorrowTree.releaseProtector
        rw [hooksTwoNodeTree_indexOfTag_child perm,
          hooksTwoNodeTree_locations_entries_size perm]
        simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
          Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
          List.range', List.forIn_cons, List.forIn_nil]
        rw [hooksTwoNodeTree_locations_index_zero perm]
        dsimp only []
        rw [hooksLocTree_perms_get_child perm]
        dsimp only []
        rw [hassoc']
        simp only [↓reduceIte]
        rw [hooksTwoNodeTree_locations_setAtPos_zero perm]
        dsimp only []
        conv =>
          lhs
          arg 1
          arg 1
          arg 1
          arg 2
          arg 1
          whnf
          rw [hnorm_ok]
          simp +zetaHave only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
            uniIndex_ofNat_zero_eq, hooksTwoNodeTree_roots_eq perm,
            Array.size_singleton,
            Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
            Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
            List.range', List.forIn_cons, List.forIn_nil,
            Option.isNone_none, Bool.not_false, Bool.true_and,
            Array.getElem?_singleton, beq_self_eq_true,
            bind, Bind.bind, pure, Pure.pure]
          rw [forIn'_cons_match_ite_yield_snd_fst, forIn'_cons_match_ite_yield_fst]
        conv =>
          lhs
          arg 1
          arg 1
          arg 1
          arg 4
          intro
          arg 1
          arg 1
          arg 2
          arg 3
          arg 2
          arg 1
          whnf
          rw [hnorm_ok]
          simp +zetaHave only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
            uniIndex_ofNat_zero_eq, hooksTwoNodeTree_roots_eq perm,
            Array.size_singleton,
            Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
            Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
            List.range', List.forIn_cons, List.forIn_nil,
            Option.isNone_none, Bool.not_false, Bool.true_and,
            Array.getElem?_singleton, beq_self_eq_true,
            bind, Bind.bind, pure, Pure.pure]
          rw [forIn'_cons_match_ite_yield_snd_fst, forIn'_cons_match_ite_yield_fst]
        rfl
      dsimp only []
      rw [hrel_ok]
      exact ⟨⟨fun _ => hdis, fun _ => rfl⟩, fun _ => rfl, fun hd => False.elim (hdis hd), hmiss⟩

end ReleaseProtectorOperational

/-- Protected (`CallId = 7`) unwritten `&mut` reborrow `e` of local `1` for the
`C2` end-of-call foreign-`Unique` divergence theorem. -/
def cexProtectedReservedFrzEntry : BorrowEntry :=
  { tag := 1
    targetLocal := 1
    targetProjection := []
    perm := .reservedFrz false
    protector := some 7
    parentTag := none }

/-- Unprotected activated (`Unique`) sibling reborrow `f` of local `1` for the
`C2` end-of-call foreign-`Unique` divergence theorem. -/
def cexForeignUniqueSiblingEntry : BorrowEntry :=
  { tag := 2
    targetLocal := 1
    targetProjection := []
    perm := .unique
    protector := none
    parentTag := none }

/-- Borrow table `[e, f]` containing a protected `ReservedFrz false` tag (`e`)
and a foreign sibling `Unique` tag (`f`). -/
def cexForeignUniqueBorrows : List BorrowEntry :=
  [cexProtectedReservedFrzEntry, cexForeignUniqueSiblingEntry]

/-- **Divergence Theorem (`C2`, `cex_end_of_call_foreign_unique_frozen_divergence`)**:
On a borrow table `bs = [e{ReservedFrz false, prot = some 7}, f{Unique, prot = none}]`
satisfying both `ActiveProtectorsValid bs [7]` and `TreeBorrowsRel bs [7] (basedNormalTree bs [7])`:
1. Canonical Miri's Tree Borrows end-of-call implicit protector access, evaluated
   on the separately constructed `basedNormalTree bs [7]` (`annealAssociatedAccess e.perm = some .Read`,
   `NormalTreeState.performAccess 0 .Read .SkipChildrenOfAccessed`), succeeds
   (`.status = .Completed`) and acts as a foreign read on the sibling `f`,
   freezing `f` from `Unique` to `Frozen`
   (`normalTreePerms res.tree 2 = [some (.reservedFrz false), some .frozen] ≠ [some (.reservedFrz false), some .unique]`);
2. Stage-1 `Trusted` `TerminatorKind.return_` (`Terminators.lean:3005-3039`,
   `restoreCallerProtectors` at `Terminators.lean:468`) restores `activeProtectors`
   without running an end-of-call `performAccess` pass on `s.memory.borrows`,
   leaving `f.perm = .unique`. (Note that `AnnealMachine` stores no per-allocation
   `BorrowTree`s—only `GlobalState` protector IDs—so `annealStepHooksLM4_1`
   steps in lockstep with Stage-1; this divergence is specifically against
   canonical Miri's Tree Borrows engine.) -/
theorem cex_end_of_call_foreign_unique_frozen_divergence :
    ActiveProtectorsValid cexForeignUniqueBorrows [7] ∧
    TreeBorrowsRel cexForeignUniqueBorrows [7]
      (basedNormalTree cexForeignUniqueBorrows [7]) ∧
    annealAssociatedAccess cexProtectedReservedFrzEntry.perm = some .Read ∧
    let res :=
      (basedNormalTree cexForeignUniqueBorrows [7]).performAccess 0 .Read .SkipChildrenOfAccessed
    res.status = .Completed ∧
    normalTreePerms res.tree cexForeignUniqueBorrows.length =
      [some (.reservedFrz false), some .frozen] ∧
    normalTreePerms res.tree cexForeignUniqueBorrows.length ≠
      cexForeignUniqueBorrows.map (fun e => some e.perm) := by
  refine ⟨by decide, ⟨rfl, by decide, by decide, by decide, rfl⟩, rfl, ?_⟩
  decide

/-- Active `CallId` protectors restored to `s.memory.activeProtectors` when
returning from the current frame (`Terminators.lean:468`, `restoreCallerProtectors`):
`[]` at the root frame (`callStack = []`), and
`match cf.callerProtector with | some protId => protId :: cf.calleeProtectors | none => cf.calleeProtectors`
when `callStack = cf :: _`. -/
def callerRestoredProtectors : List SavedCallerFrame → List Nat
  | [] => []
  | cf :: _ =>
    match cf.callerProtector with
    | some protId => protId :: cf.calleeProtectors
    | none => cf.calleeProtectors

/-- Stage-1 `Trusted` bridge: for a non-empty call stack `cf :: cs`,
`callerRestoredProtectors (cf :: cs)` is definitionally equal to
`Trusted.Rustc.V2026_06_01.MirSemantics.restoreCallerProtectors cf`. -/
@[simp]
theorem callerRestoredProtectors_cons_eq_restoreCallerProtectors
    (cf : SavedCallerFrame) (cs : List SavedCallerFrame) :
    callerRestoredProtectors (cf :: cs) = restoreCallerProtectors cf := rfl

/-- Arbitrary-depth `CallId` protector release (`releaseCallProtectors`):
popping `k` saved caller frames off `callStack` starting from
`activeProtectors` iteratively applies Stage-1 `restoreCallerProtectors cf`
(`Terminators.lean:468`; used by `TerminatorKind.return_` at `Terminators.lean:3022`
and by every pop of `unwindFromCallStack` at `Terminators.lean:639`) for each popped
`SavedCallerFrame`. Stage-1 pops several frames in a *single* step when unwinding
through `UnwindAction.continue_` callers, and
`unwindFromCallStack_running_releaseCallProtectors` proves that the protectors it
leaves active are exactly `releaseCallProtectors k callStack activeProtectors`.

Popping past the root frame (`k > callStack.length`) never yields a running Stage-1
state (`unwindFromCallStack [] _ = .halted .panic`, and a root `return_` halts with
`.retNormal`), so the `[]` result in that case is only a totalizing convention. -/
def releaseCallProtectors : Nat → List SavedCallerFrame → List Nat → List Nat
  | 0, _, activeProtectors => activeProtectors
  | _ + 1, [], _ => []
  | k + 1, cf :: rest, _ =>
    releaseCallProtectors k rest (restoreCallerProtectors cf)

/-- Single-step (`k = 1`) specialization of `releaseCallProtectors` on a
non-empty call stack `cf :: cs` equals Stage-1 `restoreCallerProtectors cf`. -/
@[simp]
theorem releaseCallProtectors_one_cons
    (cf : SavedCallerFrame) (cs : List SavedCallerFrame) (activeProtectors : List Nat) :
    releaseCallProtectors 1 (cf :: cs) activeProtectors = restoreCallerProtectors cf := rfl

/-- Totalizing convention of `releaseCallProtectors`: requesting
`callStack.length + 1` pops (past the root frame, which Stage-1 never resumes)
yields `[]`. -/
theorem releaseCallProtectors_full_clear
    (callStack : List SavedCallerFrame) (activeProtectors : List Nat) :
    releaseCallProtectors (callStack.length + 1) callStack activeProtectors = [] := by
  induction callStack generalizing activeProtectors with
  | nil => rfl
  | cons cf rest ih =>
    dsimp only [List.length_cons, releaseCallProtectors]
    exact ih (restoreCallerProtectors cf)

/-- `ActiveProtectorsValid` is preserved across `releaseCallProtectors k callStack activeProtectors`
at arbitrary stack depth `k` whenever `ActiveProtectorsValid borrows activeProtectors`
holds initially and every saved caller frame `cf ∈ callStack` has valid restored
protectors `ActiveProtectorsValid borrows (restoreCallerProtectors cf)`. -/
theorem ActiveProtectorsValid.of_releaseCallProtectors
    {borrows : List BorrowEntry}
    (k : Nat) (callStack : List SavedCallerFrame) (activeProtectors : List Nat)
    (hcur : ActiveProtectorsValid borrows activeProtectors)
    (hstack : ∀ cf ∈ callStack, ActiveProtectorsValid borrows (restoreCallerProtectors cf)) :
    ActiveProtectorsValid borrows (releaseCallProtectors k callStack activeProtectors) := by
  induction k generalizing callStack activeProtectors with
  | zero => exact hcur
  | succ k' ih =>
    cases callStack with
    | nil => exact ActiveProtectorsValid.nil borrows
    | cons cf rest =>
      dsimp only [releaseCallProtectors]
      exact ih rest (restoreCallerProtectors cf)
        (hstack cf List.mem_cons_self)
        (fun cf' hcf' => hstack cf' (List.mem_cons_of_mem _ hcf'))

/-- **Stage-1 grounding of `releaseCallProtectors`**
(`unwindFromCallStack_running_releaseCallProtectors`): whenever Stage-1
`unwindFromCallStack callStack mem` (`Terminators.lean:632-653`, executed by
`TerminatorKind.unwindResume` and by `applyUnwindAction .continue_`) resumes in a
caller frame (`.running s'`), it has popped some `k` saved caller frames
(`1 ≤ k ≤ callStack.length`; every popped frame but the last unwinds with
`.continue_`) in that single step, restoring each popped frame's protectors, so
that `s'.memory.activeProtectors = releaseCallProtectors k callStack mem.activeProtectors`
and `s'.memory.callStack = callStack.drop k`. -/
theorem unwindFromCallStack_running_releaseCallProtectors
    (callStack : List SavedCallerFrame) (mem : Memory) (s' : MachineState)
    (h : unwindFromCallStack callStack mem = .running s') :
    ∃ k, 1 ≤ k ∧ k ≤ callStack.length ∧
      s'.memory.activeProtectors = releaseCallProtectors k callStack mem.activeProtectors ∧
      s'.memory.callStack = callStack.drop k := by
  induction callStack generalizing mem with
  | nil => simp [unwindFromCallStack] at h
  | cons cf rest ih =>
    cases hru : cf.returnUnwind with
    | unreachable => simp [unwindFromCallStack, hru] at h
    | terminate => simp [unwindFromCallStack, hru] at h
    | continue_ =>
      simp only [unwindFromCallStack, hru] at h
      obtain ⟨k, hk1, hk2, hprot, hcs⟩ := ih _ h
      refine ⟨k + 1, by omega, by simp only [List.length_cons]; omega, ?_, ?_⟩
      · rw [hprot]; rfl
      · rw [hcs]; rfl
    | cleanup bb =>
      simp only [unwindFromCallStack, hru] at h
      injection h with h'
      subst h'
      exact ⟨1, Nat.le_refl 1, by simp only [List.length_cons]; omega, rfl, rfl⟩

/-- Multi-node 3-level chain (`[g, c, r]`) and 3-node branching (`[c₀, c₁, p]`)
protector release correspondence on canonical Tree Borrows (`basedNormalTree`,
constructed from the `BorrowEntry` table since `AnnealMachine` stores no
per-allocation `BorrowTree`s):
1. On a 3-level reborrow chain `[g{perm, prot = some 1, parent = some 2},
   c{Unique, parent = some 1}, r{Unique, parent = none}]`, canonical Tree Borrows'
   end-of-call protector access at grandchild `g`
   (`performAccess 0 (protectorEndAccessKind perm) .SkipChildrenOfAccessed`
   for `perm ≠ .cell`) succeeds iff `perm ≠ .disabled`, and when `perm ≠ .disabled`
   preserves all 3 permissions (`[some perm, some .unique, some .unique]`) because
   both parent `c` and root `r` are *ancestors* (`.LocalAccess`) of `g`—matching
   Stage-1 `restoreCallerProtectors`;
2. On a 3-node branching tree `[c₀{ReservedFrz false, prot = some 1, parent = some 1},
   c₁{Unique, prot = none, parent = some 1}, p{Unique, parent = none}]`, canonical
   Tree Borrows' end-of-call protector access at `c₀`
   (`performAccess 0 .Read .SkipChildrenOfAccessed`) preserves ancestor `p` at
   `some .unique` (`.LocalAccess`) while freezing foreign sibling `c₁` from
   `.unique` to `.frozen` (`.ForeignAccess`), diverging from Stage-1
   `restoreCallerProtectors` (which performs no tree access and leaves `c₁` `.unique`). -/
theorem basedNormalTree_releaseProtector_chain3_and_branch3_simulation
    (perm : TreeBorrowPerm) :
    let chain3 : List BorrowEntry :=
      [{ tag := 3, targetLocal := 1, targetProjection := [], perm := perm,
         protector := some 1, parentTag := some 2 },
       { tag := 2, targetLocal := 1, targetProjection := [], perm := .unique,
         protector := none, parentTag := some 1 },
       { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique,
         protector := none, parentTag := none }]
    let branch3 : List BorrowEntry :=
      [{ tag := 2, targetLocal := 1, targetProjection := [], perm := .reservedFrz false,
         protector := some 1, parentTag := some 1 },
       { tag := 3, targetLocal := 1, targetProjection := [], perm := .unique,
         protector := none, parentTag := some 1 },
       { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique,
         protector := none, parentTag := none }]
    let nresChain :=
      (basedNormalTree chain3 [1]).performAccess 0 (protectorEndAccessKind perm) .SkipChildrenOfAccessed
    let nresBranch :=
      (basedNormalTree branch3 [1]).performAccess 0 .Read .SkipChildrenOfAccessed
    TreeBorrowsRel chain3 [] (basedNormalTree chain3 []) ∧
    (perm ≠ .cell →
      (nresChain.status = .Completed ↔ perm ≠ .disabled) ∧
      (perm ≠ .disabled →
        normalTreePerms nresChain.tree 3 = [some perm, some .unique, some .unique])) ∧
    nresBranch.status = .Completed ∧
    normalTreePerms nresBranch.tree 3 =
      [some (.reservedFrz false), some .frozen, some .unique] := by
  rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;>
    exact ⟨⟨rfl, by decide, rfl, rfl, rfl⟩,
      fun hne => by decide,
      by decide,
      by decide⟩

/-- Whether `pt : Miri.TreeBorrows.ProtectedTags` contains the borrow tag `tag : Nat`
(via `Miri.Memory.BorTag.ofUInt64 (UInt64.ofNat tag)`). -/
def protectedTagsContainsNat (pt : Miri.TreeBorrows.ProtectedTags) (tag : Nat) : Bool :=
  match Miri.Memory.BorTag.ofUInt64 (UInt64.ofNat tag) with
  | some bt => pt.contains bt
  | none => false

/-- The popped callee frame's `Miri.TreeBorrows.FrameState` containing every
borrow tag in `borrows` that is protected by `activeProtectors` and not in the
restored caller protector set `restoredProtectors`.
Note that `Miri.TreeBorrows.GlobalState.endCall` only inspects the second
component (`pair.2 : BorTag`) of each `(AllocId, BorTag)` pair in
`frameState.protectedTags`. -/
def poppedCalleeFrameState
    (borrows : List BorrowEntry)
    (activeProtectors restoredProtectors : List Nat) :
    Miri.TreeBorrows.FrameState :=
  { protectedTags :=
      (borrows.filterMap fun e =>
        if isBorrowProtected activeProtectors e && !isBorrowProtected restoredProtectors e then
          (Miri.Memory.BorTag.ofUInt64 (UInt64.ofNat e.tag)).map fun btag =>
            (⟨1, by decide⟩, btag)
        else
          none).toArray }

/-- The `Miri.TreeBorrows.FrameState` released when popping the current top frame
of `s`: empty `{}` at the root frame (`s.memory.callStack = []`), and
`poppedCalleeFrameState s.memory.borrows s.memory.activeProtectors (callerRestoredProtectors [cf])`
when `s.memory.callStack = cf :: _`. -/
def annealPoppedFrameState (s : MachineState) : Miri.TreeBorrows.FrameState :=
  match s.memory.callStack with
  | [] => {}
  | cf :: _ =>
    poppedCalleeFrameState s.memory.borrows s.memory.activeProtectors
      (callerRestoredProtectors [cf])

/-- Release the popped frame's `FrameState` in `m.machine.borrowTracker` via
`Miri.TreeBorrows.GlobalState.endCall` without modifying `rootPointerTags`. -/
def popFrameBorrowTracker
    (frameState : Miri.TreeBorrows.FrameState)
    (bt : Option Miri.Interpreter.MachineHooks.BorrowState) :
    Option Miri.Interpreter.MachineHooks.BorrowState :=
  bt.map fun tracker =>
    { tracker with global := tracker.global.endCall frameState }

/-- Inductive correspondence between Anneal's `(borrows, activeProtectors, callStack)`
and `lean-miri`'s optional `m.machine.borrowTracker`
(`Option Miri.Interpreter.MachineHooks.BorrowState`) across arbitrary stack depth:
* Base (`callStack = []`): when `bt = some tracker`, every `e ∈ borrows` is
  registered in `tracker.global.protectedTags` iff `isBorrowProtected activeProtectors e = true`
  (with no artificial constraint on `tracker.global.rootPointerTags`).
* Step (`cf :: restStack`): when `bt = some tracker`, every `e ∈ borrows` is
  registered in `tracker.global.protectedTags` iff `isBorrowProtected activeProtectors e = true`,
  and popping the frame via `popFrameBorrowTracker` (`GlobalState.endCall` on
  `poppedCalleeFrameState borrows activeProtectors (callerRestoredProtectors [cf])`)
  satisfies `BorrowTrackerStackRel` for `(callerRestoredProtectors [cf], restStack)`. -/
inductive BorrowTrackerStackRel (borrows : List BorrowEntry) :
    List Nat → List SavedCallerFrame →
    Option Miri.Interpreter.MachineHooks.BorrowState → Prop where
  | root (activeProtectors : List Nat)
      (bt : Option Miri.Interpreter.MachineHooks.BorrowState) :
      (∀ tracker, bt = some tracker →
        ∀ e ∈ borrows,
          protectedTagsContainsNat tracker.global.protectedTags e.tag =
            isBorrowProtected activeProtectors e) →
      BorrowTrackerStackRel borrows activeProtectors [] bt
  | cons (activeProtectors : List Nat)
      (cf : SavedCallerFrame) (restStack : List SavedCallerFrame)
      (bt : Option Miri.Interpreter.MachineHooks.BorrowState) :
      (∀ tracker, bt = some tracker →
        ∀ e ∈ borrows,
          protectedTagsContainsNat tracker.global.protectedTags e.tag =
            isBorrowProtected activeProtectors e) →
      BorrowTrackerStackRel borrows (callerRestoredProtectors [cf]) restStack
        (popFrameBorrowTracker
          (poppedCalleeFrameState borrows activeProtectors (callerRestoredProtectors [cf]))
          bt) →
      BorrowTrackerStackRel borrows activeProtectors (cf :: restStack) bt

theorem BorrowTrackerStackRel.of_none
    (borrows : List BorrowEntry) (activeProtectors : List Nat)
    (callStack : List SavedCallerFrame) :
    BorrowTrackerStackRel borrows activeProtectors callStack none := by
  induction callStack generalizing activeProtectors with
  | nil => exact .root activeProtectors none (fun _ h => nomatch h)
  | cons cf rest ih =>
    exact .cons activeProtectors cf rest none (fun _ h => nomatch h)
      (ih (callerRestoredProtectors [cf]))

theorem BorrowTrackerStackRel.of_borrows_nil
    (activeProtectors : List Nat) (callStack : List SavedCallerFrame)
    (bt : Option Miri.Interpreter.MachineHooks.BorrowState) :
    BorrowTrackerStackRel [] activeProtectors callStack bt := by
  induction callStack generalizing activeProtectors bt with
  | nil => exact .root activeProtectors bt (fun _ _ _ h => nomatch h)
  | cons cf rest ih =>
    exact .cons activeProtectors cf rest bt (fun _ _ _ h => nomatch h)
      (ih (callerRestoredProtectors [cf])
        (popFrameBorrowTracker (poppedCalleeFrameState [] activeProtectors (callerRestoredProtectors [cf])) bt))

theorem BorrowTrackerStackRel.of_popFrame
    {borrows : List BorrowEntry} {activeProtectors : List Nat}
    {cf : SavedCallerFrame} {restStack : List SavedCallerFrame}
    {bt : Option Miri.Interpreter.MachineHooks.BorrowState}
    (h : BorrowTrackerStackRel borrows activeProtectors (cf :: restStack) bt) :
    BorrowTrackerStackRel borrows (callerRestoredProtectors [cf]) restStack
      (popFrameBorrowTracker
        (poppedCalleeFrameState borrows activeProtectors (callerRestoredProtectors [cf]))
        bt) := by
  cases h with
  | cons _ _ _ _ _ hpop => exact hpop

theorem BorrowTrackerStackRel.current_spec
    {borrows : List BorrowEntry} {activeProtectors : List Nat}
    {callStack : List SavedCallerFrame}
    {bt : Option Miri.Interpreter.MachineHooks.BorrowState}
    (h : BorrowTrackerStackRel borrows activeProtectors callStack bt) :
    ∀ tracker, bt = some tracker →
      ∀ e ∈ borrows,
        protectedTagsContainsNat tracker.global.protectedTags e.tag =
          isBorrowProtected activeProtectors e := by
  cases h with
  | root _ _ hspec => exact hspec
  | cons _ _ _ _ hspec _ => exact hspec

theorem poppedCalleeFrameState_self
    (borrows : List BorrowEntry) (prots : List Nat) :
    poppedCalleeFrameState borrows prots prots = {} := by
  unfold poppedCalleeFrameState
  have hfilter :
      borrows.filterMap (fun e =>
        if isBorrowProtected prots e && !isBorrowProtected prots e then
          (Miri.Memory.BorTag.ofUInt64 (UInt64.ofNat e.tag)).map fun btag =>
            ((⟨1, by decide⟩ : Miri.Memory.AllocId), btag)
        else
          none) = [] := by
    induction borrows with
    | nil => rfl
    | cons e rest ih =>
      have hfalse : (isBorrowProtected prots e && !isBorrowProtected prots e) = false := by
        cases isBorrowProtected prots e <;> rfl
      rw [List.filterMap_cons, hfalse]
      exact ih
  rw [hfilter]

theorem popFrameBorrowTracker_empty
    (bt : Option Miri.Interpreter.MachineHooks.BorrowState) :
    popFrameBorrowTracker {} bt = bt := by
  cases bt with
  | none => rfl
  | some tracker =>
    dsimp only [popFrameBorrowTracker, Option.map]
    rw [Miri.TreeBorrows.GlobalState.endCall_empty]

theorem BorrowTrackerStackRel.of_pushFrame
    {borrows : List BorrowEntry} {activeProtectors : List Nat}
    {savedCaller : SavedCallerFrame} {callStack : List SavedCallerFrame}
    {bt : Option Miri.Interpreter.MachineHooks.BorrowState}
    (h : BorrowTrackerStackRel borrows activeProtectors callStack bt)
    (hrestored : callerRestoredProtectors [savedCaller] = activeProtectors) :
    BorrowTrackerStackRel borrows activeProtectors (savedCaller :: callStack) bt := by
  refine .cons activeProtectors savedCaller callStack bt h.current_spec ?_
  rw [hrestored, poppedCalleeFrameState_self, popFrameBorrowTracker_empty]
  exact h

/-- Iteratively release the popped frames' `FrameState`s across `k` frame pops in
`m.machine.borrowTracker` via `popFrameBorrowTracker` (`GlobalState.endCall`). -/
def popFrameBorrowTrackerAtDepth :
    Nat → List BorrowEntry → List Nat → List SavedCallerFrame →
    Option Miri.Interpreter.MachineHooks.BorrowState →
    Option Miri.Interpreter.MachineHooks.BorrowState
  | 0, _, _, _, bt => bt
  | _ + 1, _, _, [], bt => bt
  | k + 1, borrows, activeProtectors, cf :: rest, bt =>
    popFrameBorrowTrackerAtDepth k borrows (restoreCallerProtectors cf) rest
      (popFrameBorrowTracker
        (poppedCalleeFrameState borrows activeProtectors (restoreCallerProtectors cf))
        bt)

/-- Arbitrary-depth `BorrowTrackerStackRel` preservation across `k` consecutive
frame pops (`k ≤ callStack.length`): popping `k` frames from `callStack` updates
`activeProtectors` to `releaseCallProtectors k callStack activeProtectors` and
`bt` to `popFrameBorrowTrackerAtDepth k borrows activeProtectors callStack bt`,
preserving `BorrowTrackerStackRel` on the remaining call stack `callStack.drop k`. -/
theorem BorrowTrackerStackRel.of_releaseCallProtectors
    {borrows : List BorrowEntry}
    (k : Nat) {activeProtectors : List Nat}
    {callStack : List SavedCallerFrame}
    {bt : Option Miri.Interpreter.MachineHooks.BorrowState}
    (h : BorrowTrackerStackRel borrows activeProtectors callStack bt)
    (hk : k ≤ callStack.length) :
    BorrowTrackerStackRel borrows
      (releaseCallProtectors k callStack activeProtectors)
      (callStack.drop k)
      (popFrameBorrowTrackerAtDepth k borrows activeProtectors callStack bt) := by
  induction k generalizing activeProtectors callStack bt with
  | zero => exact h
  | succ k' ih =>
    cases callStack with
    | nil => cases hk
    | cons cf rest =>
      dsimp only [releaseCallProtectors, List.drop_succ_cons, popFrameBorrowTrackerAtDepth]
      exact ih h.of_popFrame (Nat.le_of_succ_le_succ hk)

/-! ## 2. Depth-1 `TreeBorrowsStateRel` -/

/-- Depth-1 single-frame simulation relation extending `StateRel` with an
arbitrary Tree Borrows table `s.memory.borrows`, active `CallId` protector set
`s.memory.activeProtectors`, and Miri `m.machine.borrowTracker` related via
`TreeBorrowsRel`, `ActiveProtectorsValid`, and `BorrowTrackerStackRel`. -/
inductive TreeBorrowsStateRel
    (body : CapturedMir)
    (s : MachineState)
    (m : AnnealStepState) : Prop where
  | mk
      (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (frames_eq : m.stack.frames = #[topFrame])
      (returnContinuation_eq : topFrame.returnContinuation = .stop false)
      (returnPlace_eq :
        ∃ retLay,
          topFrame.returnPlace =
            .frameLocal 0 0 none retLay topFrame.localsIdentity)
      (frame_rel : FrameRel body m.machine s.frame topFrame)
      (activeCallee_ok : s.memory.activeCallee = none ∨ s.memory.activeCallee = some body)
      (callStack_nil : s.memory.callStack = .nil)
      (callerLocals_nil : s.memory.callerLocals = .nil)
      (memoryAllocDisjoint : MemoryAllocDisjoint topFrame)
      (treeBorrows_rel :
        TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
          (basedNormalTree s.memory.borrows s.memory.activeProtectors))
      (activeProtectors_valid :
        ActiveProtectorsValid s.memory.borrows s.memory.activeProtectors)
      (borrowTracker_rel :
        BorrowTrackerStackRel s.memory.borrows s.memory.activeProtectors
          s.memory.callStack m.machine.borrowTracker := by
          first
          | exact BorrowTrackerStackRel.of_none _ _ _
          | exact BorrowTrackerStackRel.of_borrows_nil _ _ _
          | decide) :
      TreeBorrowsStateRel body s m

/-! ## 3. Arbitrary-Depth Multi-Frame Simulation Relation (`MultiFrameStateRel` / `CallStackStateRel`) -/

/-- The active `CapturedMir` body executed by Anneal's current top frame:
`callee` when `s.memory.activeCallee = some callee`, and `rootBody` at depth 1
when `s.memory.activeCallee = none`. -/
def activeMirBody (rootBody : CapturedMir) (s : MachineState) : CapturedMir :=
  s.memory.activeCallee.getD rootBody

/-- Complete bottom-to-top list of `(CapturedMir, StackFrame)` pairs in Anneal's
machine state `s`: caller frames from `s.memory.callStack.reverse` (oldest
caller first, starting with `rootBody`) followed by the currently executing top
frame `(activeMirBody rootBody s, s.frame)`. -/
def annealFrameStackBottomUp (rootBody : CapturedMir) (s : MachineState) :
    List (CapturedMir × StackFrame) :=
  (s.memory.callStack.reverse.map fun cf => (cf.callerBody, cf.frame)) ++
    [(activeMirBody rootBody s, s.frame)]

/-- Complete top-to-bottom list of `(CapturedMir, StackFrame)` pairs in Anneal's
machine state `s`: the active top frame `(activeMirBody rootBody s, s.frame)`
followed by `s.memory.callStack` (most recent caller first). -/
def annealFrameStackTopDown (rootBody : CapturedMir) (s : MachineState) :
    List (CapturedMir × StackFrame) :=
  (activeMirBody rootBody s, s.frame) ::
    (s.memory.callStack.map fun cf => (cf.callerBody, cf.frame))

/-- Pairwise `List.Forall₂` frame simulation relation relating Anneal's active
frame plus `callStack` (`annealFrameStackTopDown rootBody s`) to `lean-miri`'s
call stack (`m.stack.frames.toList.reverse`, top-to-bottom). -/
def FrameStackRel (rootBody : CapturedMir) (s : MachineState) (m : AnnealStepState) : Prop :=
  List.Forall₂
    (fun (pair : CapturedMir × StackFrame)
         (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) =>
      FrameRel pair.1 m.machine pair.2 mf)
    (annealFrameStackTopDown rootBody s)
    m.stack.frames.toList.reverse

/-- `FrameStackRel` is equivalent to the bottom-to-top `List.Forall₂` between
`annealFrameStackBottomUp rootBody s` and `m.stack.frames.toList`. -/
theorem frameStackRel_iff_bottomUp
    (rootBody : CapturedMir) (s : MachineState) (m : AnnealStepState) :
    FrameStackRel rootBody s m ↔
      List.Forall₂
        (fun (pair : CapturedMir × StackFrame)
             (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) =>
          FrameRel pair.1 m.machine pair.2 mf)
        (annealFrameStackBottomUp rootBody s)
        m.stack.frames.toList := by
  unfold FrameStackRel annealFrameStackTopDown annealFrameStackBottomUp
  have hrev :
      ((activeMirBody rootBody s, s.frame) ::
        s.memory.callStack.map fun cf => (cf.callerBody, cf.frame)).reverse =
      (s.memory.callStack.reverse.map fun cf => (cf.callerBody, cf.frame)) ++
        [(activeMirBody rootBody s, s.frame)] := by
    simp [List.reverse_cons, List.map_reverse]
  rw [← List.forall₂_reverse_iff, hrev, List.reverse_reverse]

/-- Extract the optional initialized `Value` from a `LocalSlot` (`some v` for
`.init v`, `none` for `.uninit` or `.dead`). -/
def slotOptVal : LocalSlot → Option Value
  | .init v => some v
  | _ => none

/-- Correspondence between an Anneal `SavedCallerFrame.destination` (`Place` in
`cf.callerBody`) and a `lean-miri` callee frame's `returnPlace : RuntimeStackPlace`:
1. `.immediate`: an unprojected caller local `⟨destIdx, .nil⟩` backed by
   `RuntimeStackPlace.frameLocal callerFrameIdx destIdx none retLay callerFrame.localsIdentity`
   whose caller slot is currently live and immediate (`.live (.immediate _)`).
2. `.indirect`: an unprojected caller local `⟨destIdx, .nil⟩` backed by
   `RuntimeStackPlace.memory mp retLay` (or `.frameLocal` where the caller slot
   is `.live (.indirect mp)`) where `mp` is a valid memory-backed stack
   allocation of `destIdx` in `m.machine`. -/
inductive CallerDestinationRel
    (mach : AnnealMachine)
    (callerFrameIdx : Nat)
    (cf : SavedCallerFrame)
    (callerMiriFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    Miri.Interpreter.RuntimeStackPlace AnnealProv → Prop where
  | immediate
      (destIdx : Local) (destDecl : LocalDecl)
      (slot : LocalSlot) (imm : Miri.Interpreter.Immediate AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      cf.destination = ⟨destIdx, .nil⟩ →
      get? cf.callerBody.localDecls destIdx = some destDecl →
      get? cf.frame.locals destIdx = some slot →
      slot ≠ .dead →
      callerMiriFrame.locals[destIdx]? =
        some ⟨.live (.immediate imm), cachedLayout⟩ →
      CallerDestinationRel mach callerFrameIdx cf callerMiriFrame
        (.frameLocal callerFrameIdx destIdx none
          (translateTy destDecl.ty cf.callerBody.layouts)
          callerMiriFrame.localsIdentity)
  | indirect
      (destIdx : Local) (destDecl : LocalDecl)
      (slot : LocalSlot) (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout)
      (returnPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv)
      (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64) (relOffset : Miri.ABI.Size)
      (localAlloc :
        Miri.Memory.LocalAllocation
          AnnealProv
          (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
      (words : Array UInt64) :
      cf.destination = ⟨destIdx, .nil⟩ →
      get? cf.callerBody.localDecls destIdx = some destDecl →
      IsPrimScalarTy destDecl.ty →
      get? cf.frame.locals destIdx = some slot →
      slot ≠ .dead →
      callerMiriFrame.locals[destIdx]? =
        some ⟨.live (.indirect mp), cachedLayout⟩ →
      (returnPlace = .memory ⟨mp, translateTy destDecl.ty cf.callerBody.layouts⟩ ∨
       returnPlace = .frameLocal callerFrameIdx destIdx none
         (translateTy destDecl.ty cf.callerBody.layouts)
         callerMiriFrame.localsIdentity) →
      mp.ptr.provenance = some (.concrete allocId tag) →
      mp.misaligned = none →
      mp.metadata = .none →
      (allocId, localAlloc) ∈ mach.memory.live.toList →
      (mach.memory.live.toList.map Prod.fst).Nodup →
      mach.lookupBaseAddr allocId = some baseAddr →
      baseAddr.toNat + relOffset.bytes.toNat < 2 ^ 64 →
      mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes) →
      localAlloc.allocation.mutability = .Mut →
      localAlloc.allocation.len = localAlloc.allocation.byteSize.bytes.toNat →
      localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new →
      InitMaskWordRel localAlloc.allocation.initializationMask localAlloc.allocation.byteSize words →
      mp.ptr.offset.isAligned (translateTy destDecl.ty cf.callerBody.layouts).layout.align.abi = .ok true →
      relOffset.bytes.toNat + (translateTy destDecl.ty cf.callerBody.layouts).layout.size.bytes.toNat ≤
        localAlloc.allocation.byteSize.bytes.toNat →
      MemPlaceRel mach destDecl.ty cf.callerBody.layouts (slotOptVal slot) mp →
      CallerDestinationRel mach callerFrameIdx cf callerMiriFrame returnPlace

/-- Well-formedness of an `.indirect` return place `_0` in a root frame
(`rootMf.locals[0]? = some ⟨.live (.indirect mp0), lay0⟩`). -/
def RootIndirectRetWf
    (mach : AnnealMachine)
    (rootBody : CapturedMir) (curAf : StackFrame)
    (rootMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop :=
  ∀ (mp0 : Miri.Interpreter.MemPlace AnnealProv)
    (lay0 : Option Miri.Interpreter.LocalLayout)
    (decl0 : LocalDecl),
    rootMf.locals[0]? = some ⟨.live (.indirect mp0), lay0⟩ →
    get? rootBody.localDecls 0 = some decl0 →
    (mach.memory.live.toList.map Prod.fst).Nodup ∧
    IsPrimScalarTy decl0.ty ∧
    rootMf.returnPlace =
      .frameLocal 0 0 none (translateTy decl0.ty rootBody.layouts) rootMf.localsIdentity ∧
    (∀ retVal, get? curAf.locals 0 = some (.init retVal) → ∃ sc0, retVal = .scalar sc0) ∧
    (get? curAf.locals 0 = some .uninit →
      ∀ allocId0 tag0 localAlloc0 baseAddr0 off0,
        mp0.ptr.provenance = some (.concrete allocId0 tag0) →
        (allocId0, localAlloc0) ∈ mach.memory.live.toList →
        mach.lookupBaseAddr allocId0 = some baseAddr0 →
        mp0.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr0 + off0.bytes) →
        ∃ badRange,
          localAlloc0.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange off0 (translateTy decl0.ty rootBody.layouts).layout.size) =
            .ok (.error badRange))

theorem RootIndirectRetWf.of_immediate
    {mach : AnnealMachine}
    {rootBody : CapturedMir} {curAf : StackFrame}
    {rootMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (himm : IsImmediateFrameLocal rootMf 0) :
    RootIndirectRetWf mach rootBody curAf rootMf := by
  intro mp0 lay0 _ h0 _
  exact False.elim (himm _ h0 mp0 rfl)

/-- Well-formedness of an `.indirect` return place `_0` in a non-root callee frame
(`calleeMf.locals[0]? = some ⟨.live (.indirect mp0), lay0⟩`). -/
def CalleeIndirectRetWf
    (mach : AnnealMachine)
    (curBody : CapturedMir) (curAf : StackFrame)
    (cf : SavedCallerFrame)
    (calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop :=
  ∀ (mp0 : Miri.Interpreter.MemPlace AnnealProv)
    (lay0 : Option Miri.Interpreter.LocalLayout)
    (decl0 destDecl : LocalDecl) (destIdx : Local),
    calleeMf.locals[0]? = some ⟨.live (.indirect mp0), lay0⟩ →
    get? curBody.localDecls 0 = some decl0 →
    cf.destination = ⟨destIdx, .nil⟩ →
    get? cf.callerBody.localDecls destIdx = some destDecl →
    (mach.memory.live.toList.map Prod.fst).Nodup ∧
    IsPrimScalarTy destDecl.ty ∧
    translateTy destDecl.ty cf.callerBody.layouts = translateTy decl0.ty curBody.layouts ∧
    (∀ retVal, get? curAf.locals 0 = some (.init retVal) → ∃ sc0, retVal = .scalar sc0) ∧
    (get? curAf.locals 0 = some .uninit →
      ∀ allocId0 tag0 localAlloc0 baseAddr0 off0,
        mp0.ptr.provenance = some (.concrete allocId0 tag0) →
        (allocId0, localAlloc0) ∈ mach.memory.live.toList →
        mach.lookupBaseAddr allocId0 = some baseAddr0 →
        mp0.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr0 + off0.bytes) →
        ∃ badRange,
          localAlloc0.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange off0 (translateTy decl0.ty curBody.layouts).layout.size) =
            .ok (.error badRange))

/-- Inductive linkage invariant relating Anneal's `callStack : List SavedCallerFrame`
and `activeProtectors : List Nat` to `lean-miri`'s `m.stack.frames.toList.reverse`
(top-to-bottom):
* Base case (`callStack = []`, root frame `rootMf` at index `0`):
  - `rootMf.returnContinuation = .stop false`
  - `rootMf.returnPlace = .frameLocal 0 0 none retLay rootMf.localsIdentity`
  - `FrameRel rootBody mach curAf rootMf`
* Inductive step (`cf :: cs`, callee frame `calleeMf` above `callerMf :: restMfs`
  where `callerFrameIdx = restMfs.length`):
  - `calleeMf.returnContinuation = .goto (if cf.isDiverging then none else some cf.returnTarget) (translateUnwindAction cf.returnUnwind)`
  - `CallerDestinationRel mach restMfs.length cf callerMf calleeMf.returnPlace`
  - `FrameRel curBody mach curAf calleeMf`
  - `CalleeIndirectRetWf mach curBody curAf cf calleeMf`
  - `activeProtectors` decomposes as `curFrameProts ++ callerProts` where
    `restoreCallerProtectors cf = callerProts` and every `cid ∈ curFrameProts` is absent
    from `callerProts` (`∀ cid ∈ curFrameProts, natListContainsBool callerProts cid = false`). -/
inductive CallerStackLinksRel
    (rootBody : CapturedMir) (mach : AnnealMachine) :
    CapturedMir → StackFrame → List SavedCallerFrame → List Nat →
    List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) → Prop where
  | root
      (curAf : StackFrame)
      (rootMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (rootProts : List Nat) :
      rootMf.returnContinuation = .stop false →
      (∃ retLay,
        rootMf.returnPlace =
          .frameLocal 0 0 none retLay rootMf.localsIdentity) →
      FrameRel rootBody mach curAf rootMf →
      CallerStackLinksRel rootBody mach rootBody curAf [] rootProts [rootMf]
  | cons
      (curBody : CapturedMir) (curAf : StackFrame)
      (cf : SavedCallerFrame) (cs : List SavedCallerFrame)
      (curFrameProts callerProts : List Nat)
      (calleeMf callerMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)) :
      calleeMf.returnContinuation =
        .goto (if cf.isDiverging then none else some cf.returnTarget)
          (translateUnwindAction cf.returnUnwind) →
      CallerDestinationRel mach restMfs.length cf callerMf calleeMf.returnPlace →
      FrameRel curBody mach curAf calleeMf →
      CalleeIndirectRetWf mach curBody curAf cf calleeMf →
      (match cf.callerProtector with | some protId => protId :: cf.calleeProtectors | none => cf.calleeProtectors) = callerProts →
      (∀ cid ∈ curFrameProts, natListContainsBool callerProts cid = false) →
      CallerStackLinksRel rootBody mach cf.callerBody cf.frame cs callerProts (callerMf :: restMfs) →
      CallerStackLinksRel rootBody mach curBody curAf (cf :: cs)
        (curFrameProts ++ callerProts) (calleeMf :: callerMf :: restMfs)

theorem CallerStackLinksRel.toForall2
    {rootBody : CapturedMir} {mach : AnnealMachine}
    {curBody : CapturedMir} {curAf : StackFrame}
    {cs : List SavedCallerFrame} {prots : List Nat}
    {mfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    (h : CallerStackLinksRel rootBody mach curBody curAf cs prots mfs) :
    List.Forall₂
      (fun (pair : CapturedMir × StackFrame)
           (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) =>
        FrameRel pair.1 mach pair.2 mf)
      ((curBody, curAf) :: cs.map (fun cf => (cf.callerBody, cf.frame)))
      mfs := by
  induction h with
  | root _ _ _ _ _ hfr =>
    exact .cons hfr .nil
  | cons _ _ _ _ _ _ _ _ _ _ _ hfr _ _ _ _ ih =>
    exact .cons hfr ih

/-- Every `CallerStackLinksRel` implies `FrameStackRel`. -/
theorem CallerStackLinksRel.toFrameStackRel
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : CallerStackLinksRel rootBody m.machine (activeMirBody rootBody s) s.frame
      s.memory.callStack s.memory.activeProtectors m.stack.frames.toList.reverse) :
    FrameStackRel rootBody s m :=
  h.toForall2

/-- Multi-frame allocation disjointness:
1. Within every frame `mf ∈ m.stack.frames.toList`, `MemoryAllocDisjoint mf` holds
   (distinct `.indirect` locals of `mf` own distinct `AllocId`s);
2. Across distinct frames `mf₁, mf₂` at indices `f₁ ≠ f₂` in `m.stack.frames`,
   every `.indirect` local in `mf₁` and every `.indirect` local in `mf₂` own
   distinct `AllocId`s.

This guarantees that when `Stack.cleanupStackFrame` deallocates all `.indirect`
locals of the popped top frame on `Terminator.Return`, every live allocation
referenced by any caller frame's `FrameRel` or `CallerDestinationRel` remains
live and untouched in `m.machine.memory.live`. -/
structure MultiFrameAllocDisjoint
    (frames : Array (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)) : Prop where
  intra_frame :
    ∀ mf ∈ frames.toList, MemoryAllocDisjoint mf
  inter_frame :
    ∀ (f₁ f₂ i j : Nat)
      (mf₁ mf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp₁ mp₂ : Miri.Interpreter.MemPlace AnnealProv)
      (lay₁ lay₂ : Option Miri.Interpreter.LocalLayout),
      f₁ ≠ f₂ →
      frames[f₁]? = some mf₁ →
      frames[f₂]? = some mf₂ →
      mf₁.locals[i]? = some { value := .live (.indirect mp₁), layout := lay₁ } →
      mf₂.locals[j]? = some { value := .live (.indirect mp₂), layout := lay₂ } →
      mp₁.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp₂.ptr.provenance.bind Miri.Memory.Provenance.getAllocId

/-- Arbitrary-depth multi-frame simulation relation (`MultiFrameStateRel` /
`CallStackStateRel`) between Anneal's `MachineState` (`s`) and `lean-miri`'s
`AnnealStepState` (`m`) rooted at `rootBody`:
* `topFrame_eq`: `m.stack.frames.back? = some topFrame`;
* `activeCallee_root` / `activeCallee_nonroot`: at depth 1 (`s.memory.callStack = []`),
  `s.memory.activeCallee = none ∨ s.memory.activeCallee = some rootBody`; at
  depth `> 1` (`s.memory.callStack ≠ []`), `s.memory.activeCallee = some (activeMirBody rootBody s)`;
* `frameStack_rel`: `FrameStackRel rootBody s m` (`List.Forall₂ FrameRel` across
  all active + caller frames);
* `stackLinks_rel`: `CallerStackLinksRel` linking every frame's `returnContinuation`,
  `returnPlace`, `FrameRel`, and per-frame `CallId` protectors;
* `allocDisjoint`: `MultiFrameAllocDisjoint m.stack.frames` (intra-frame and
  inter-frame `.indirect` stack allocation disjointness);
* `treeBorrows_rel`: `TreeBorrowsRel s.memory.borrows s.memory.activeProtectors (basedNormalTree s.memory.borrows s.memory.activeProtectors)`;
* `activeProtectors_valid`: `ActiveProtectorsValid s.memory.borrows s.memory.activeProtectors`;
* `borrowTracker_rel`: `BorrowTrackerStackRel s.memory.borrows s.memory.activeProtectors s.memory.callStack m.machine.borrowTracker`
  relating Anneal's active protector stack to `lean-miri`'s `m.machine.borrowTracker`
  under `Miri.TreeBorrows.GlobalState.endCall`;
* `nextProtector_pos` / `nextProtector_gt_active` / `nextProtector_gt_borrows`:
  every active protector `cid ∈ s.memory.activeProtectors` and every borrow
  entry protector `some cid` in `s.memory.borrows` satisfies
  `cid < s.memory.nextProtector` (and `0 < s.memory.nextProtector`), so
  allocating `s.memory.nextProtector` on `RetagKind.fnEntry` produces a
  strictly fresh protector `CallId`. -/
inductive MultiFrameStateRel
    (rootBody : CapturedMir)
    (s : MachineState)
    (m : AnnealStepState) : Prop where
  | mk
      (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (topFrame_eq : m.stack.frames.back? = some topFrame)
      (activeCallee_root :
        s.memory.callStack = [] →
          s.memory.activeCallee = none ∨ s.memory.activeCallee = some rootBody)
      (activeCallee_nonroot :
        s.memory.callStack ≠ [] →
          s.memory.activeCallee = some (activeMirBody rootBody s))
      (frameStack_rel : FrameStackRel rootBody s m)
      (stackLinks_rel :
        CallerStackLinksRel rootBody m.machine (activeMirBody rootBody s) s.frame
          s.memory.callStack s.memory.activeProtectors m.stack.frames.toList.reverse)
      (allocDisjoint : MultiFrameAllocDisjoint m.stack.frames)
      (treeBorrows_rel :
        TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
          (basedNormalTree s.memory.borrows s.memory.activeProtectors))
      (activeProtectors_valid :
        ActiveProtectorsValid s.memory.borrows s.memory.activeProtectors)
      (nextProtector_pos : 0 < s.memory.nextProtector)
      (nextProtector_gt_active :
        ∀ cid ∈ s.memory.activeProtectors, cid < s.memory.nextProtector)
      (nextProtector_gt_borrows :
        ∀ e ∈ s.memory.borrows, ∀ cid, e.protector = some cid → cid < s.memory.nextProtector)
      (borrowTracker_rel :
        BorrowTrackerStackRel s.memory.borrows s.memory.activeProtectors
          s.memory.callStack m.machine.borrowTracker := by
          first
          | exact BorrowTrackerStackRel.of_none _ _ _
          | exact BorrowTrackerStackRel.of_borrows_nil _ _ _) :
      MultiFrameStateRel rootBody s m

/-- Alias `CallStackStateRel` for `MultiFrameStateRel`. -/
abbrev CallStackStateRel := MultiFrameStateRel

/-- Intermediate multi-frame unwinding relation (`UnwindingStateRel`) between a
Stage-1 `MachineState` `s` (holding the remaining `callStack` and restored
`activeProtectors` at an intermediate step of `unwindFromCallStack`) and
`lean-miri`'s `AnnealStepState` `m` whose active top frame sits at
`location = .unwinding span` (`ControlFlow.unwindToBlock` at `ControlFlow.lean:54`,
dispatched on the next step by `Step.step` at `Step.lean:90`). -/
def UnwindingStateRel
    (rootBody : CapturedMir)
    (s : MachineState)
    (m : AnnealStepState) : Prop :=
  ∃ (m_mir : AnnealStepState)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (span : Miri.MIR.SpanRef),
    m_mir.stack.frames.back? = some topFrame ∧
    m = { m_mir with stack := ⟨m_mir.stack.frames.pop.push { topFrame with location := .unwinding span }⟩ } ∧
    MultiFrameStateRel rootBody s m_mir

/-! ### Bidirectional Depth-1 Bridge Theorems (`StateRel` ↔ `TreeBorrowsStateRel` ↔ `MultiFrameStateRel`) -/

/-- Lift any depth-1 `StateRel` state directly to `TreeBorrowsStateRel`. -/
theorem StateRel.toTreeBorrowsStateRel
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m) :
    TreeBorrowsStateRel body s m := by
  rcases h with ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  refine .mk tf hframes hretCont hretPlace hfr (Or.inl hcal) hst hcaller hdisj ?_ ?_ ?_
  · rw [hbor, hprot]
    exact ⟨by decide, by decide, rfl, rfl, rfl⟩
  · rw [hprot]
    exact ActiveProtectorsValid.nil _
  · rw [hbor]
    exact BorrowTrackerStackRel.of_borrows_nil _ _ _

/-- Project a depth-1 `TreeBorrowsStateRel` state with an empty borrow table,
empty active protectors, and `activeCallee = none` back to `StateRel`. -/
theorem TreeBorrowsStateRel.toStateRel_of_empty
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : TreeBorrowsStateRel body s m)
    (hcal : s.memory.activeCallee = none)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil) :
    StateRel body s m := by
  rcases h with ⟨tf, hframes, hretCont, hretPlace, hfr, _, hst, hcaller, hdisj, _, _, _⟩
  exact StateRel.mk tf hframes hretCont hretPlace hfr hcal hst hbor hprot hcaller hdisj

/-- Lift any depth-1 `TreeBorrowsStateRel` state (with valid `nextProtector` bounds)
to `MultiFrameStateRel`. -/
theorem TreeBorrowsStateRel.toMultiFrameStateRel
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : TreeBorrowsStateRel body s m)
    (hcid_pos : 0 < s.memory.nextProtector)
    (hcid_act : ∀ cid ∈ s.memory.activeProtectors, cid < s.memory.nextProtector)
    (hcid_bor : ∀ e ∈ s.memory.borrows, ∀ cid, e.protector = some cid → cid < s.memory.nextProtector) :
    MultiFrameStateRel body s m := by
  rcases h with ⟨tf, hframes, hretCont, hretPlace, hfr, hcal_ok, hst, _, hdisj, htb, hvalid, hbt⟩
  have hact_body : activeMirBody body s = body := by
    unfold activeMirBody
    rcases hcal_ok with hnone | hsome
    · simp [hnone]
    · simp [hsome]
  have hrev : m.stack.frames.toList.reverse = [tf] := by
    rw [hframes]; rfl
  have hback : m.stack.frames.back? = some tf := by
    rw [hframes]; rfl
  have hlinks :
      CallerStackLinksRel body m.machine (activeMirBody body s) s.frame
        s.memory.callStack s.memory.activeProtectors m.stack.frames.toList.reverse := by
    rw [hact_body, hst, hrev]
    exact .root s.frame tf s.memory.activeProtectors hretCont hretPlace hfr
  refine .mk tf hback (fun _ => hcal_ok) (fun hne => False.elim (hne hst))
    hlinks.toFrameStackRel hlinks ?_ htb hvalid hcid_pos hcid_act hcid_bor hbt
  refine ⟨?_, ?_⟩
  · intro mf hmf
    rw [hframes] at hmf
    rcases List.mem_singleton.mp hmf with rfl
    exact hdisj
  · intro f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ _ _
    rw [hframes] at hf₁ hf₂
    cases f₁ with
    | zero =>
      cases f₂ with
      | zero => exact False.elim (hne rfl)
      | succ n => simp at hf₂
    | succ n => simp at hf₁

private theorem array_eq_singleton_of_toList_reverse_singleton {α : Type _}
    {arr : Array α} {x : α} (h : arr.toList.reverse = [x]) :
    arr = #[x] := by
  apply Array.ext'
  have h' := congrArg List.reverse h
  simpa [List.reverse_reverse] using h'

/-- Project any depth-1 `MultiFrameStateRel` state (`s.memory.callStack = []`,
`s.memory.callerLocals = []`) down to `TreeBorrowsStateRel`. -/
theorem MultiFrameStateRel.toTreeBorrowsStateRel_of_depth1
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : MultiFrameStateRel body s m)
    (hst : s.memory.callStack = .nil)
    (hcaller : s.memory.callerLocals = .nil) :
    TreeBorrowsStateRel body s m := by
  rcases h with ⟨_, _, hcal_root, _, _, hlinks, hdisj, htb, hvalid, _, _, _, hbt⟩
  have hcal_ok := hcal_root hst
  have hact_body : activeMirBody body s = body := by
    unfold activeMirBody
    rcases hcal_ok with hnone | hsome
    · simp [hnone]
    · simp [hsome]
  generalize hmfs : m.stack.frames.toList.reverse = mfs at hlinks
  rw [hst, hact_body] at hlinks
  cases hlinks with
  | root _ rootMf _ hretCont hretPlace hfr =>
    have hframes : m.stack.frames = #[rootMf] :=
      array_eq_singleton_of_toList_reverse_singleton hmfs
    have hd_root : MemoryAllocDisjoint rootMf := by
      apply hdisj.intra_frame rootMf
      rw [hframes]
      exact List.mem_singleton.mpr rfl
    exact .mk rootMf hframes hretCont hretPlace hfr hcal_ok hst hcaller hd_root htb hvalid hbt

/-- **Bidirectional depth-1 bridge (`TreeBorrowsStateRel.iff_multiFrameStateRel_depth1`)**:
At stack depth 1 (`s.memory.callStack = []`, `s.memory.callerLocals = []`, and
valid `nextProtector` bounds), `TreeBorrowsStateRel body s m` is equivalent to
`MultiFrameStateRel body s m`. -/
theorem TreeBorrowsStateRel.iff_multiFrameStateRel_depth1
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hst : s.memory.callStack = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hcid_pos : 0 < s.memory.nextProtector)
    (hcid_act : ∀ cid ∈ s.memory.activeProtectors, cid < s.memory.nextProtector)
    (hcid_bor : ∀ e ∈ s.memory.borrows, ∀ cid, e.protector = some cid → cid < s.memory.nextProtector) :
    TreeBorrowsStateRel body s m ↔ MultiFrameStateRel body s m :=
  ⟨fun h => h.toMultiFrameStateRel hcid_pos hcid_act hcid_bor,
   fun h => h.toTreeBorrowsStateRel_of_depth1 hst hcaller⟩

/-- **Bidirectional depth-1 bridge (`StateRel.iff_multiFrameStateRel_depth1`)**:
At stack depth 1 with an empty borrow/protector table (`s.memory.activeCallee = none`,
`s.memory.callStack = []`, `s.memory.borrows = []`, `s.memory.activeProtectors = []`,
`s.memory.callerLocals = []`, and `0 < s.memory.nextProtector`), `StateRel body s m`
is equivalent to `MultiFrameStateRel body s m`. -/
theorem StateRel.iff_multiFrameStateRel_depth1
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hcal : s.memory.activeCallee = none)
    (hst : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hcid_pos : 0 < s.memory.nextProtector) :
    StateRel body s m ↔ MultiFrameStateRel body s m := by
  constructor
  · intro h
    apply h.toTreeBorrowsStateRel.toMultiFrameStateRel hcid_pos
    · rw [hprot]; intro _ hmem; cases hmem
    · rw [hbor]; intro _ hmem; cases hmem
  · intro h
    exact (h.toTreeBorrowsStateRel_of_depth1 hst hcaller).toStateRel_of_empty hcal hbor hprot

/-- Bridge from `LM-3.3`'s `StateRelLM3_2Tree` to `TreeBorrowsRel` and
`ActiveProtectorsValid`. -/
theorem stateRelLM3_2Tree_to_treeBorrowsRel_and_activeProtectorsValid
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap) :
    (s.memory.borrows.map BorrowEntry.tag).Nodup ∧
    s.memory.activeProtectors = .nil ∧
    TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
      (basedNormalTree s.memory.borrows s.memory.activeProtectors) ∧
    ActiveProtectorsValid s.memory.borrows s.memory.activeProtectors := by
  obtain ⟨hnodup, htb⟩ := SimLM3_3.stateRelLM3_2Tree_treeBorrowsRel htree
  obtain ⟨_, _, _, _, _, _, _, hprot, _, _, _, _⟩ := id htree.erased_rel
  have hprot_s : s.memory.activeProtectors = .nil := hprot
  refine ⟨hnodup, hprot_s, htb, ?_⟩
  rw [hprot_s]
  exact ActiveProtectorsValid.nil _

/-! ## 4. Layered `LM-4.1` Stack, Control, Call, Terminator, and Step Hooks & `StepRelMultiFrame` -/

/-- Sequentially deallocate all `.live (.indirect mp)` locals in `slots` from
`mem` via `deallocLocalMemory`. -/
def deallocFrameLocalsList (mem : AnnealMemory) :
    List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) → AnnealMemory
  | [] => mem
  | slot :: rest => deallocFrameLocalsList (deallocLocalMemory mem slot.value) rest

/-- Deallocate all `.live (.indirect mp)` locals in `frame.locals` from `mem`. -/
def deallocFrameLocals (mem : AnnealMemory)
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : AnnealMemory :=
  deallocFrameLocalsList mem frame.locals.toList

/-- `StackLifecycleHooks` instantiated for `LM-4.1` multi-frame call and return
execution (`Stack.pushStackFrameRaw`, `Stack.pushStackFrameDone`,
`Stack.popStackFrameRaw`, `Stack.cleanupStackFrame`). -/
def annealStackLifecycleHooksLM4_1
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.StackLifecycleHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMemory where
  storage := annealLocalStorageHooks localDecls layouts
  freshLocalsIdentity := fun st => (st, .ofAllocationToken 0)
  initFrame := fun st frame => ⟨st, .ok frame⟩
  requiredConstants := fun stack st => ⟨stack, st, .ok ()⟩
  afterPush := fun stack st => ⟨stack, st, .ok ()⟩
  beforePop := fun stack st => ⟨stack, st, .ok ()⟩
  afterPop := fun stack st _ _ => ⟨stack, st, .ok .normal⟩
  alwaysLiveVarsAndTemps := fun _ => .ok #[]
  deallocateVararg := fun st _ => ⟨st, .ok ()⟩

/-- Every local slot in `slots` owns, if anything, a live allocation in `mem`. -/
def AllSlotsAllocLive (mem : AnnealMemory)
    (slots : List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)) : Prop :=
  ∀ s ∈ slots, LocalAllocLive mem s.value

/-- Distinct local slots in `slots` own disjoint `AllocId`s. -/
def SlotsAllocDisjoint
    (slots : List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)) : Prop :=
  List.Pairwise
    (fun s₁ s₂ =>
      ∀ mp₁ mp₂,
        s₁.value = .live (.indirect mp₁) →
        s₂.value = .live (.indirect mp₂) →
        mp₁.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
          mp₂.ptr.provenance.bind Miri.Memory.Provenance.getAllocId)
    slots

theorem LocalAllocLive.of_dealloc_disjoint
    {mem : AnnealMemory}
    {v₁ v₂ : Miri.Interpreter.LocalValue AnnealProv}
    (hlive : LocalAllocLive mem v₂)
    (hdisj : ∀ mp₁ mp₂,
      v₁ = .live (.indirect mp₁) →
      v₂ = .live (.indirect mp₂) →
      mp₁.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp₂.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    LocalAllocLive (deallocLocalMemory mem v₁) v₂ := by
  intro mp₂ hv₂
  obtain ⟨id₂, hid₂, hany₂⟩ := hlive mp₂ hv₂
  refine ⟨id₂, hid₂, ?_⟩
  cases hv₁ : v₁ with
  | dead =>
    simp [deallocLocalMemory, hany₂]
  | live op₁ =>
    cases op₁ with
    | immediate _ =>
      simp [deallocLocalMemory, hany₂]
    | indirect mp₁ =>
      have hne := hdisj mp₁ mp₂ hv₁ hv₂
      cases hid₁ : mp₁.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none =>
        simp [deallocLocalMemory, hid₁, hany₂]
      | some id₁ =>
        have hne_id : id₁ ≠ id₂ := by
          intro heq
          apply hne
          rw [hid₁, hid₂, heq]
        simp only [deallocLocalMemory, hid₁]
        rw [← Array.any_toList, List.any_eq_true] at hany₂
        rw [← Array.any_toList, Array.toList_filter, List.any_eq_true]
        obtain ⟨x, hx, hbeq⟩ := hany₂
        have hx_id : x.1 = id₂ := eq_of_beq hbeq
        refine ⟨x, List.mem_filter.mpr ⟨hx, ?_⟩, hbeq⟩
        rw [hx_id]
        exact bne_iff_ne.mpr (Ne.symm hne_id)

theorem cleanupStackFrame_root_stop
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (stack : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit)
    (mem : AnnealMemory)
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hstop : frame.returnContinuation = .stop false) :
    stack.cleanupStackFrame mem (annealStackLifecycleHooksLM4_1 localDecls layouts) false frame =
      ⟨stack, mem, .ok .noCleanup⟩ := by
  unfold Miri.Interpreter.Stack.cleanupStackFrame
  rw [hstop]
  rfl

private theorem forIn_deallocateLocal_list_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (stack : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit)
    {f : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout →
      Option (Miri.Interpreter.StackRunResult
        AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMemory Miri.Interpreter.ReturnAction) × AnnealMemory →
      Id (ForInStep
        (Option (Miri.Interpreter.StackRunResult
          AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMemory Miri.Interpreter.ReturnAction) × AnnealMemory))} :
    ∀ (slots : List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
      (mem : AnnealMemory),
      AllSlotsAllocLive mem slots →
      SlotsAllocDisjoint slots →
      (∀ slot __s,
        f slot __s =
          match
            (Miri.Interpreter.Frame.deallocateLocal
              (annealStackLifecycleHooksLM4_1 localDecls layouts).storage
              __s.2 slot.value).outcome with
          | .error error =>
              pure
                (ForInStep.done
                  (some ⟨stack,
                    (Miri.Interpreter.Frame.deallocateLocal
                      (annealStackLifecycleHooksLM4_1 localDecls layouts).storage
                      __s.2 slot.value).state,
                    .error error⟩,
                   (Miri.Interpreter.Frame.deallocateLocal
                     (annealStackLifecycleHooksLM4_1 localDecls layouts).storage
                     __s.2 slot.value).state))
          | .ok () =>
              pure
                (ForInStep.yield
                  (none,
                   (Miri.Interpreter.Frame.deallocateLocal
                     (annealStackLifecycleHooksLM4_1 localDecls layouts).storage
                     __s.2 slot.value).state))) →
      forIn (m := Id) slots (none, mem) f =
      ((none : Option (Miri.Interpreter.StackRunResult
        AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMemory Miri.Interpreter.ReturnAction)),
       deallocFrameLocalsList mem slots)
  | [], mem, _, _, _ => rfl
  | slot :: rest, mem, hlive, hdisj, hf => by
    have hlive_head : LocalAllocLive mem slot.value :=
      hlive slot List.mem_cons_self
    rcases List.pairwise_cons.mp hdisj with ⟨hhead_disj, hrest_disj⟩
    have hlive_rest : AllSlotsAllocLive (deallocLocalMemory mem slot.value) rest := by
      intro s hs
      exact (hlive s (List.mem_cons_of_mem _ hs)).of_dealloc_disjoint (hhead_disj s hs)
    have hdealloc :=
      annealLocalStorageHooks_deallocateLocal_eq localDecls layouts mem slot.value hlive_head
    rw [List.forIn_cons, hf]
    simp only [annealStackLifecycleHooksLM4_1, hdealloc,
      bind, Bind.bind, deallocFrameLocalsList]
    exact forIn_deallocateLocal_list_eq localDecls layouts stack rest
      (deallocLocalMemory mem slot.value) hlive_rest hrest_disj hf

/-- On a callee frame with `returnContinuation = .goto ret unwind` and `vaList = #[]`,
`Stack.cleanupStackFrame` deallocates every `.live (.indirect mp)` local of
`frame` (`deallocFrameLocals mem frame`) and returns `.ok .normal`. -/
theorem cleanupStackFrame_callee_goto
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (stack : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit)
    (mem : AnnealMemory)
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {ret : Option Miri.MIR.BasicBlockId} {unwind : Miri.MIR.UnwindAction}
    (hcont : frame.returnContinuation = .goto ret unwind)
    (hva : frame.vaList = #[])
    (hlive : AllSlotsAllocLive mem frame.locals.toList)
    (hdisj : SlotsAllocDisjoint frame.locals.toList) :
    stack.cleanupStackFrame mem (annealStackLifecycleHooksLM4_1 localDecls layouts) false frame =
      ⟨stack, deallocFrameLocals mem frame, .ok .normal⟩ := by
  unfold Miri.Interpreter.Stack.cleanupStackFrame deallocFrameLocals
  rw [hcont, hva]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ← Array.forIn_toList]
  rw [forIn_deallocateLocal_list_eq localDecls layouts stack frame.locals.toList mem hlive hdisj]
  · rfl
  · intro _ _; rfl

/-- On a callee frame with `returnContinuation = .goto ret unwind` and `vaList = #[]`,
`Stack.cleanupStackFrame` deallocates every `.live (.indirect mp)` local of
`frame` (`deallocFrameLocals mem frame`) and returns `.ok .normal` for both
normal return (`unwinding = false`) and stack unwinding (`unwinding = true`). -/
theorem cleanupStackFrame_callee_goto_any_unwinding
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (stack : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit)
    (mem : AnnealMemory)
    (unwinding : Bool)
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {ret : Option Miri.MIR.BasicBlockId} {unwind : Miri.MIR.UnwindAction}
    (hcont : frame.returnContinuation = .goto ret unwind)
    (hva : frame.vaList = #[])
    (hlive : AllSlotsAllocLive mem frame.locals.toList)
    (hdisj : SlotsAllocDisjoint frame.locals.toList) :
    stack.cleanupStackFrame mem (annealStackLifecycleHooksLM4_1 localDecls layouts) unwinding frame =
      ⟨stack, deallocFrameLocals mem frame, .ok .normal⟩ := by
  unfold Miri.Interpreter.Stack.cleanupStackFrame deallocFrameLocals
  rw [hcont, hva]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ← Array.forIn_toList]
  rw [forIn_deallocateLocal_list_eq localDecls layouts stack frame.locals.toList mem hlive hdisj]
  · rfl
  · intro _ _; rfl

/-- `FrameRel` implies `AllSlotsAllocLive` for `mf.locals.toList`. -/
theorem FrameRel.allSlotsAllocLive
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRel body mach af mf) :
    AllSlotsAllocLive mach.memory mf.locals.toList := by
  intro mls hmem
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  have hi_mf : i < mf.locals.size := by simpa using hi
  have hi_decl : i < body.localDecls.length := by rw [← hfr.mf_locals_size]; exact hi_mf
  have hdecl : get? body.localDecls i = some (body.localDecls[i]'hi_decl) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hi_decl]
  obtain ⟨_, mls', _, _, _, hmls', _, hloc⟩ := hfr.lookup_local hdecl
  rw [Array.getElem?_eq_getElem hi_mf] at hmls'
  injection hmls' with h_eq
  subst h_eq
  simpa using hloc.allocLive

/-- `MemoryAllocDisjoint` implies `SlotsAllocDisjoint` for `mf.locals.toList`. -/
theorem MemoryAllocDisjoint.slotsAllocDisjoint
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hdisj : MemoryAllocDisjoint mf) :
    SlotsAllocDisjoint mf.locals.toList := by
  unfold SlotsAllocDisjoint
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij mp₁ mp₂ hv₁ hv₂
  have hi_mf : i < mf.locals.size := by simpa using hi
  have hj_mf : j < mf.locals.size := by simpa using hj
  have hget_i : mf.locals[i]? = some { value := .live (.indirect mp₁), layout := (mf.locals[i]'hi_mf).layout } := by
    rw [Array.getElem?_eq_getElem hi_mf]
    have hv₁' : (mf.locals[i]'hi_mf).value = .live (.indirect mp₁) := hv₁
    cases hls : mf.locals[i]'hi_mf with
    | mk val lay =>
      rw [hls] at hv₁'
      dsimp only at hv₁' ⊢
      rw [hv₁']
  have hget_j : mf.locals[j]? = some { value := .live (.indirect mp₂), layout := (mf.locals[j]'hj_mf).layout } := by
    rw [Array.getElem?_eq_getElem hj_mf]
    have hv₂' : (mf.locals[j]'hj_mf).value = .live (.indirect mp₂) := hv₂
    cases hls : mf.locals[j]'hj_mf with
    | mk val lay =>
      rw [hls] at hv₂'
      dsimp only at hv₂' ⊢
      rw [hv₂']
  exact hdisj i j mp₁ mp₂ _ _ (Nat.ne_of_lt hij) hget_i hget_j

/-- `MemPlaceRel` is preserved across `deallocFrameLocalsList` whenever `mp`'s
allocation is disjoint from every slot in `slots`. -/
theorem MemPlaceRel.of_deallocFrameLocalsList
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {optVal : Option Value} {mp : Miri.Interpreter.MemPlace AnnealProv} :
    ∀ (slots : List (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
      (mem : AnnealMemory),
      MemPlaceRel { mach with memory := mem } ty layouts optVal mp →
      (∀ s ∈ slots, ∀ mp_s, s.value = .live (.indirect mp_s) →
        mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
          mp_s.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) →
      MemPlaceRel { mach with memory := deallocFrameLocalsList mem slots } ty layouts optVal mp
  | [], _, hmp, _ => hmp
  | slot :: rest, mem, hmp, hdisj => by
    have hmp' : MemPlaceRel { mach with memory := deallocLocalMemory mem slot.value } ty layouts optVal mp := by
      cases hs : slot.value with
      | dead =>
        simpa [deallocLocalMemory, hs] using hmp
      | live op =>
        cases op with
        | immediate _ =>
          simpa [deallocLocalMemory, hs] using hmp
        | indirect mp_s =>
          have hne := hdisj slot List.mem_cons_self mp_s hs
          cases hid : mp_s.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
          | none =>
            simpa [deallocLocalMemory, hs, hid] using hmp
          | some id =>
            have hne_id : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
              rw [← hid]; exact hne
            simpa [deallocLocalMemory, hs, hid] using hmp.of_filter_live hne_id
    exact MemPlaceRel.of_deallocFrameLocalsList rest (deallocLocalMemory mem slot.value) hmp'
      (fun s hs => hdisj s (List.mem_cons_of_mem _ hs))

/-- `FrameRel` on a caller frame `callerMf` is preserved when deallocating all
locals of a popped callee frame `calleeMf` whose `.indirect` allocations are
disjoint from `callerMf`'s `.indirect` allocations. -/
theorem FrameRel.of_deallocFrameLocals
    {callerBody : CapturedMir} {mach : AnnealMachine}
    {callerAf : StackFrame}
    {callerMf calleeMf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRel callerBody mach callerAf callerMf)
    (hdisj :
      ∀ (i j : Nat) (mp₁ mp₂ : Miri.Interpreter.MemPlace AnnealProv)
        (lay₁ lay₂ : Option Miri.Interpreter.LocalLayout),
        callerMf.locals[i]? = some { value := .live (.indirect mp₁), layout := lay₁ } →
        calleeMf.locals[j]? = some { value := .live (.indirect mp₂), layout := lay₂ } →
        mp₁.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
          mp₂.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    FrameRel callerBody
      { mach with memory := deallocFrameLocals mach.memory calleeMf }
      callerAf callerMf where
  body_eq := hfr.body_eq
  location_eq := hfr.location_eq
  af_locals_len := hfr.af_locals_len
  mf_locals_size := hfr.mf_locals_size
  locals_rel i decl slot mls hdecl hslot hmls := by
    have hloc := hfr.locals_rel i decl slot mls hdecl hslot hmls
    cases hloc with
    | dead c hc => exact .dead c hc
    | immediate _ imm c hc hv => exact .immediate slot imm c hc hv
    | indirect _ mp₁ c hc hne hmp =>
      refine .indirect slot mp₁ c hc hne ?_
      apply MemPlaceRel.of_deallocFrameLocalsList calleeMf.locals.toList mach.memory hmp
      intro s hs mp₂ hs_val
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      have hj_sz : j < calleeMf.locals.size := by simpa using hj
      have hget_j : calleeMf.locals[j]? =
          some { value := .live (.indirect mp₂), layout := (calleeMf.locals[j]'hj_sz).layout } := by
        rw [Array.getElem?_eq_getElem hj_sz]
        have hv₂ : (calleeMf.locals[j]'hj_sz).value = .live (.indirect mp₂) := hs_val
        cases hls : calleeMf.locals[j]'hj_sz with
        | mk val lay =>
          rw [hls] at hv₂
          dsimp only at hv₂ ⊢
          rw [hv₂]
      exact hdisj i j mp₁ mp₂ c _ hmls hget_j

/-- Extract the `_0` return operand in `LM-4.1`:
* faults with `StepError.undefinedBehavior` when `_0` is `.dead`;
* when `_0` is `.live (.immediate .uninit)`, succeeds with `.ok (.immediate .uninit)`
  if `_0` has a zero-sized layout in `(localDecls, layouts)` (such as `()`), and
  faults with `StepError.undefinedBehavior` if `_0` has non-zero size;
* when `_0` is `.live (.immediate (.scalar _))`, `.live (.immediate (.scalarPair _ _))`,
  or `.live (.indirect mp)`, succeeds with `.ok op`. -/
def annealReturnOperandLM4_1
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (state : AnnealStepState) :
    Miri.Interpreter.StepResult AnnealStepState (Miri.Interpreter.Operand AnnealProv) :=
  match state.stack.currentFrame? with
  | none => (state, .error (.stack .emptyStack))
  | some frame =>
    match frame.getLocal 0 with
    | .error e => (state, .error (.stack e))
    | .ok ls =>
      match ls.value with
      | .dead =>
        (state, .error (.undefinedBehavior "return with uninitialized or dead _0"))
      | .live (.immediate .uninit) =>
        match lookupLocalDeclLayout localDecls layouts 0 with
        | some lay =>
          if lay.layout.size == Miri.ABI.Size.ZERO then
            (state, .ok (.immediate .uninit))
          else
            match frame.location with
            | .mir loc =>
              match frame.body.basicBlocks[loc.block]? with
              | some block =>
                if block.cleanup then
                  (state, .ok (.immediate .uninit))
                else
                  (state, .error (.undefinedBehavior "return with uninitialized or dead _0"))
              | none =>
                (state, .error (.undefinedBehavior "return with uninitialized or dead _0"))
            | .unwinding _ =>
              (state, .ok (.immediate .uninit))
        | none =>
          (state, .error (.undefinedBehavior "return with uninitialized or dead _0"))
      | .live op => (state, .ok op)

/-- Pop the top stack frame in `LM-4.1` and, when popping a non-root callee
frame (`!stack'.frames.isEmpty`), release its frame-owned `CallId` protectors
(`poppedFrame`) in `m.machine.borrowTracker` via `popFrameBorrowTracker`
(`Miri.TreeBorrows.GlobalState.endCall`). -/
def annealPopFrameLM4_1
    (poppedFrame : Miri.TreeBorrows.FrameState := {})
    (state : AnnealStepState) :
    Miri.Interpreter.StepResult
      AnnealStepState
      (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :=
  match state.stack.popFrame with
  | .ok (stack', frame) =>
    let bt' :=
      if stack'.frames.isEmpty then
        state.machine.borrowTracker
      else
        popFrameBorrowTracker poppedFrame state.machine.borrowTracker
    ({ state with
       stack := stack'
       machine := { state.machine with borrowTracker := bt' } },
     .ok frame)
  | .error err => (state, .error (.stack err))

/-- Copy the callee return operand `retOp` into `returnPlace` on `Terminator.Return`,
handling root-frame return (empty stack, including `.indirect` `_0` read/initialization
validation via `annealReadIndirectImmediate`), `.immediate` caller destination locals
(`Frame.replaceLocalValue`), and `.indirect` caller destination places
(`.frameLocal` with `.live (.indirect mp)` or `.memory ⟨mp, retLay⟩`, written via
`annealWriteIndirectImmediate`). -/
def annealCopyReturnLM4_1
    (retOp : Miri.Interpreter.Operand AnnealProv)
    (returnPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv)
    (state : AnnealStepState) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  match returnPlace with
  | .frameLocal callerFrameIdx destLocal none retLay _ =>
    match state.stack.currentFrame? with
    | none =>
      match retOp with
      | .immediate _ => (state, .ok ())
      | .indirect srcMp =>
        Miri.Interpreter.runRvalue
          (do
            let _ ← annealReadIndirectImmediate srcMp retLay
            pure ())
          state
    | some callerFrame =>
      if callerFrameIdx != state.stack.frames.size - 1 then
        (state, .error (.invalidProgram "caller frame index mismatch"))
      else
        match callerFrame.getLocal destLocal with
        | .error e => (state, .error (.stack e))
        | .ok callerDestState =>
          match callerDestState.value with
          | .dead =>
            (state, .error (.undefinedBehavior "caller destination local is dead"))
          | .live (.immediate _) =>
            match Miri.Interpreter.runRvalue
              (match retOp with
               | .immediate imm => pure imm
               | .indirect srcMp => do
                  let rv ← annealReadIndirectImmediate srcMp retLay
                  pure rv.imm)
              state with
            | (state', .ok imm) =>
                match callerFrame.replaceLocalValue destLocal (.live (.immediate imm)) with
                | .error e => (state', .error (.stack e))
                | .ok updatedCaller =>
                  let idx := state'.stack.frames.size - 1
                  if h : idx < state'.stack.frames.size then
                    ({ state' with stack := { frames := state'.stack.frames.set idx updatedCaller h } }, .ok ())
                  else
                    (state', .error (.stack .emptyStack))
            | (state', .error e) => (state', .error e)
          | .live (.indirect mp) =>
            Miri.Interpreter.runRvalue
              (do
                let imm ← match retOp with
                          | .immediate imm => pure imm
                          | .indirect srcMp => do
                             let rv ← annealReadIndirectImmediate srcMp retLay
                             pure rv.imm
                annealWriteIndirectImmediate imm mp Miri.ABI.Size.ZERO retLay)
              state
  | .memory mplace =>
    Miri.Interpreter.runRvalue
      (do
        let imm ← match retOp with
                  | .immediate imm => pure imm
                  | .indirect srcMp => do
                     let rv ← annealReadIndirectImmediate srcMp mplace.layout
                     pure rv.imm
        annealWriteIndirectImmediate imm mplace.mplace Miri.ABI.Size.ZERO mplace.layout)
      state
  | _ =>
    (state, .error (.unsupported "projected frameLocal returnPlace"))

/-- `ControlHooks` for `LM-4.1` multi-frame execution, wiring
`annealReturnOperandLM4_1` (ZST-aware return operand extraction),
`annealPopFrameLM4_1` (`GlobalState.endCall` protector release on callee frame pop),
`annealCopyReturnLM4_1`, and `Stack.cleanupStackFrame` (`annealStackLifecycleHooksLM4_1`). -/
def annealControlHooksLM4_1
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (poppedFrame : Miri.TreeBorrows.FrameState := {}) :
    Miri.Interpreter.ControlHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.Operand AnnealProv) where
  bodySpan := fun _ => .ok defaultSpanRef
  returnOperand := fun _ state => annealReturnOperandLM4_1 localDecls layouts state
  popFrame := fun _ state => annealPopFrameLM4_1 poppedFrame state
  copyReturn := fun _ retOp returnPlace state =>
    annealCopyReturnLM4_1 retOp returnPlace state
  cleanupFrame := fun _ unwinding frame state =>
    let res :=
      state.stack.cleanupStackFrame
        state.machine.memory
        (annealStackLifecycleHooksLM4_1 localDecls layouts)
        unwinding
        frame
    let state' : AnnealStepState :=
      { stack := res.stack
        machine := { state.machine with memory := res.state } }
    match res.outcome with
    | .ok action => (state', .ok action)
    | .error err => (state', .error (.stack err))
  unwindTerminate := fun _ _ state => (state, .error (.unsupported "unwindTerminate"))

/-- Evaluate a `Terminator.Drop` in `LM-4.1` (`annealEvalDropLM4_1`):
* for an unprojected live immediate local `place = ⟨localId, #[]⟩`, deinitializes
  `localId` to `.live (.immediate .uninit)` and jumps to `(target, 0)`, faulting
  with `StepError.undefinedBehavior` when `localId` is `.dead`;
* for a projected place (`!place.projection.isEmpty`), keeps canonical
  `lean-miri`'s no-glue `Drop` behavior (`ExecutionMachine.stepHooks.drop` at
  `ExecutionMachine.lean:327-335`: `PlaceDynamic.evalPlace` followed by
  `ControlFlow.goToBlock target`, which never reads the dropped value): faults
  with `StepError.undefinedBehavior` when `localId` is `.dead` (Miri's dead-local
  place evaluation; Stage-1 `Terminators.lean:3044` agrees), and on a live
  immediate local holding a 2-field tuple/struct (`.scalarPair _ _`) or an
  uninitialized value (`.uninit`) with projection `[.Field 0 _]` or `[.Field 1 _]`
  advances to `(target, 0)` via `ControlFlow.goToBlock target state` without
  deinitializing `localId`.

Notes on Stage-1 `Trusted` vs. canonical `lean-miri`:
* (`H3`) on an *unprojected* drop `place = ⟨localId, .nil⟩`, Stage-1 `Trusted`
  deinitializes `localId` to `.uninit` whereas canonical `lean-miri` with
  `dropGlue = none` leaves `localId`'s value intact (certified in
  `canonical_drop_no_glue_preserves_local_divergence` and
  `step_terminator_drop_canonical_no_glue_step_divergence`);
* on a *projected* drop of an uninitialized root local, Stage-1 `Trusted`
  faults (`Terminators.lean:3066`: the root slot must be `.init`), whereas
  canonical `lean-miri` (and this hook) only evaluates the place and jumps
  (certified in `step_terminator_drop_projected_uninit_divergence`). -/
def annealEvalDropLM4_1
    (place : Miri.MIR.Place)
    (target : Miri.MIR.BasicBlockId)
    (_unwind : Miri.MIR.UnwindAction)
    (state : AnnealStepState) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  if !place.projection.isEmpty then
    match state.stack.currentFrame? with
    | none => (state, .error (.stack .emptyStack))
    | some frame =>
      match frame.getLocal place.localId with
      | .error e => (state, .error (.stack e))
      | .ok ls =>
        match ls.value with
        | .dead => (state, .error (.undefinedBehavior "drop of dead local"))
        | .live (.immediate .uninit) | .live (.immediate (.scalarPair _ _)) =>
          match place.projection.toList with
          | [.Field 0 _] | [.Field 1 _] =>
            Miri.Interpreter.ControlFlow.goToBlock target state
          | _ =>
            (state, .error (.unsupported "projected drop terminator"))
        | .live _ =>
          (state, .error (.unsupported "projected drop terminator"))
  else
    match state.stack.currentFrame? with
    | none => (state, .error (.stack .emptyStack))
    | some frame =>
      match frame.getLocal place.localId with
      | .error e => (state, .error (.stack e))
      | .ok ls =>
        match ls.value with
        | .dead => (state, .error (.undefinedBehavior "drop of dead local"))
        | .live (.immediate _) =>
          match frame.replaceLocalValue place.localId (.live (.immediate .uninit)) with
          | .error e => (state, .error (.stack e))
          | .ok updatedFrame =>
            let idx := state.stack.frames.size - 1
            if h : idx < state.stack.frames.size then
              let frameAtTarget := { updatedFrame with location := .mir ⟨target, 0⟩ }
              ({ state with stack := { frames := state.stack.frames.set idx frameAtTarget h } }, .ok ())
            else
              (state, .error (.stack .emptyStack))
        | .live (.indirect _) =>
          (state, .error (.unsupported "indirect drop terminator"))

/-- Evaluate a list of call argument operands left-to-right in the caller frame
via `annealEvalOperand` and `annealReadImmediate`. -/
def annealEvalCallArgsLM4_1
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    List Miri.MIR.Operand →
    Miri.Interpreter.RvalueM AnnealStepState (List (Miri.Interpreter.RvalueImmTy AnnealProv))
  | .nil => pure .nil
  | op :: rest => do
    let opTy ← annealEvalOperand localDecls layouts op none
    let imm ← annealReadImmediate opTy
    let restImms ← annealEvalCallArgsLM4_1 localDecls layouts rest
    return (imm :: restImms)

/-- Initialize callee argument locals `idx, idx + 1, ...` from `argImms` in
`frame`. -/
def initCalleeArgLocals
    (idx : Nat) :
    List (Miri.Interpreter.RvalueImmTy AnnealProv) →
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit →
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit
  | .nil, frame => frame
  | imm :: rest, frame =>
    let frame' :=
      if h : idx < frame.locals.size then
        { frame with
          locals := frame.locals.set idx
            { value := .live (.immediate imm.imm), layout := some imm.layout } h }
      else
        frame
    initCalleeArgLocals (idx + 1) rest frame'

/-- Resolve the caller destination `dest` (`Miri.MIR.Place`) in the current top
frame `callerFrame` (at stack index `callerFrameIdx`) to a `RuntimeStackPlace AnnealProv`:
* `.frameLocal callerFrameIdx dest.localId none destLay callerFrame.localsIdentity`
  when `callerFrame.locals[dest.localId]` is `.live (.immediate _)`;
* `.memory ⟨mp, destLay⟩` when `callerFrame.locals[dest.localId]` is `.live (.indirect mp)`. -/
def resolveCallerDestinationPlace
    (callerBody : CapturedMir)
    (callerFrameIdx : Nat)
    (callerFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (dest : Miri.MIR.Place) :
    Except Miri.Interpreter.StepError (Miri.Interpreter.RuntimeStackPlace AnnealProv) :=
  if !dest.projection.isEmpty then
    .error (.unsupported "projected call destination place")
  else
    match lookupLocalDeclLayout callerBody.localDecls callerBody.layouts dest.localId with
    | none => .error (.stack (.missingLocalType dest.localId))
    | some destLay =>
      match callerFrame.getLocal dest.localId with
      | .error e => .error (.stack e)
      | .ok ls =>
        match ls.value with
        | .dead =>
          -- Note: in Anneal's `evalTerminator (.call ...)`, `destination` is only
          -- checked when the callee returns (`writePlaceValue`). Keep `.frameLocal`
          -- so a call with a dead destination only faults if/when the callee returns.
          .ok (.frameLocal callerFrameIdx dest.localId none destLay callerFrame.localsIdentity)
        | .live (.immediate _) =>
          .ok (.frameLocal callerFrameIdx dest.localId none destLay callerFrame.localsIdentity)
        | .live (.indirect mp) =>
          .ok (.memory ⟨mp, destLay⟩)

/-- Push the linked callee `calleeBody`'s `lean-miri` frame in `LM-4.1` once the
call's argument immediates `argImms` have been evaluated in the caller frame of
`stateAfterArgs`: resolves the caller destination `dest`
(`resolveCallerDestinationPlace`), pushes the callee frame via
`Stack.pushStackFrameRaw` with return continuation `.goto targetOpt unwind`,
initializes argument locals `1..=argImms.length` via `initCalleeArgLocals`, and
finishes frame setup via `Stack.pushStackFrameDone` (making `_0` live and setting
`location = .mir .start`).

`targetOpt = some targetBb` for a returning call and `targetOpt = none` for a
diverging call (`target = none`, return type `!`), matching Miri's
`ReturnContinuation::Goto { ret: None, unwind }`, so that a later normal return
from the callee hits `ControlFlow.returnToBlock none`
(`.undefinedBehavior "Unreachable"`), exactly as Stage-1 `Trusted` faults on
`SavedCallerFrame.isDiverging = true` (`Terminators.lean:3011-3012`).

Like canonical `lean-miri`'s `Call.initStackFrame` (`Call.lean:261-264`:
`let cont := if h.abiCanUnwind calleeFnAbi then cont else .goto ret .Unreachable`),
the continuation's unwind action is replaced by `.Unreachable` when the callee's
`FnAbi` cannot unwind (`calleeBody.fnAbi.canUnwind = false`), so unwinding out of
a nounwind callee is undefined behavior. Stage-1 `Trusted` never consults
`FnAbi.canUnwind` (`pushCalleeFrame` keeps `returnUnwind := unwind`); the
resulting divergence is certified by
`WitnessLM4_1.wit_lm4_1_nounwind_callee_unwind_divergence`. -/
def annealPushCalleeFrameLM4_1
    (currentBody calleeBody : CapturedMir)
    (dest : Miri.MIR.Place)
    (targetOpt : Option Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction)
    (argImms : List (Miri.Interpreter.RvalueImmTy AnnealProv))
    (stateAfterArgs : AnnealStepState) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  match stateAfterArgs.stack.currentFrame? with
  | none => (stateAfterArgs, .error (.stack .emptyStack))
  | some callerFrameAfterArgs =>
    let callerFrameIdx := stateAfterArgs.stack.frames.size - 1
    match resolveCallerDestinationPlace currentBody callerFrameIdx callerFrameAfterArgs dest with
    | .error err => (stateAfterArgs, .error err)
    | .ok returnPlace =>
      let hooks := annealStackLifecycleHooksLM4_1 calleeBody.localDecls calleeBody.layouts
      let loadedCallee : Miri.Interpreter.LoadedBody :=
        ⟨.ofCanonicalIndex 0, translateBody calleeBody⟩
      let fnInst : Miri.Interpreter.CallInstance := ⟨.Item 0, #[]⟩
      let cont : Miri.Interpreter.ReturnContinuation :=
        .goto targetOpt (if calleeBody.fnAbi.canUnwind then unwind else .Unreachable)
      let rawRes :=
        stateAfterArgs.stack.pushStackFrameRaw
          stateAfterArgs.machine.memory
          hooks
          loadedCallee
          fnInst
          cont
          returnPlace
          defaultSpanRef
      match rawRes.outcome with
      | .error e =>
        ({ stack := rawRes.stack
           machine := { stateAfterArgs.machine with memory := rawRes.state } },
         .error (.stack e))
      | .ok () =>
        match rawRes.stack.currentFrame? with
        | none =>
          ({ stack := rawRes.stack
             machine := { stateAfterArgs.machine with memory := rawRes.state } },
           .error (.stack .emptyStack))
        | some rawCalleeFrame =>
          let calleeWithArgs := initCalleeArgLocals 1 argImms rawCalleeFrame
          let stackWithArgs : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit :=
            ⟨rawRes.stack.frames.pop.push calleeWithArgs⟩
          let doneRes :=
            stackWithArgs.pushStackFrameDone rawRes.state hooks
          let finalState : AnnealStepState :=
            { stack := doneRes.stack
              machine := { stateAfterArgs.machine with memory := doneRes.state } }
          match doneRes.outcome with
          | .ok () => (finalState, .ok ())
          | .error e => (finalState, .error (.stack e))

/-- 64-bit target integer ABI classification `(byteWidth, isSigned)` of an
Anneal `RigidTy`, matching `Miri.Interpreter.LayoutCompat.integer`
(`LayoutCompat.lean:193-206`, where `ptrSizedInteger = .ok .I64` equates `usize`
with `u64` and `isize` with `i64`, and `char` counts as the unsigned 4-byte
integer `(.I32, false)`, i.e. as `u32`). `char` ↔ `u32` is therefore
ABI-compatible in canonical `lean-miri`: the subsequent
`invariant (caller.eqAbi callee)` in `LayoutCompat.checkArgumentCompat`
(`LayoutCompat.lean:234-238`) compares `BackendRepr`s only up to validity
(`LayoutData.eqAbi` uses `BackendRepr.eqUpToValidity`, `Layout.lean:154-159`), so
`char`'s restricted `validRange` does not distinguish it from `u32`. -/
@[reducible]
def annealIntAbiOfRigidTy : RigidTy → Option (Nat × Bool)
  | .char => some (4, false)
  | .uint .u8 => some (1, false)
  | .uint .u16 => some (2, false)
  | .uint .u32 => some (4, false)
  | .uint .u64 | .uint .usize => some (8, false)
  | .uint .u128 => some (16, false)
  | .int .i8 => some (1, true)
  | .int .i16 => some (2, true)
  | .int .i32 => some (4, true)
  | .int .i64 | .int .isize => some (8, true)
  | .int .i128 => some (16, true)
  | _ => none

/-- Trivial-ABI 1-ZST `RigidTy` check following
`Miri.Interpreter.LayoutCompat.hasTrivialAbi` (`LayoutCompat.lean:68-91`) on the
non-ADT fragment:
* `!` and `FnDef` items are trivial-ABI 1-ZSTs;
* `[T; n]` is a trivial-ABI 1-ZST exactly when `T` is (canonical
  `.array element => hasTrivialAbi element`; a trivial-ABI `T` makes `[T; n]` a
  1-ZST for every `n`, and canonical rejects `[T; n]` whenever `T` is not
  trivial-ABI, e.g. `[u64; 0]` (alignment 8, not a 1-ZST) and `[u8; 0]` (a 1-ZST
  whose element is not));
* a tuple is a trivial-ABI 1-ZST when all of its fields are (canonical accepts
  every 1-ZST tuple; the only 1-ZST tuples rejected here contain a 1-ZST field that
  is not itself trivial-ABI, such as `[u8; 0]`).
ADTs, closures, and coroutines are conservatively treated as non-trivial. -/
def isTrivial1ZstRigidTy : RigidTy → Bool
  | .never | .fnDef _ _ => true
  | .array elem _ => isTrivial1ZstRigidTy elem
  | .tuple fields => isTrivial1ZstRigidTyList fields
  | _ => false
termination_by structural t => t
where
  /-- `isTrivial1ZstRigidTy` for every tuple field. -/
  isTrivial1ZstRigidTyList : List RigidTy → Bool
    | .nil => true
    | f :: fs => isTrivial1ZstRigidTy f && isTrivial1ZstRigidTyList fs
  termination_by structural fs => fs

/-- Thin raw-pointer `RigidTy` check (raw pointers `*const T` / `*mut T` to
pointees other than slices, `str`, and trait objects). Subsumed by
`isThinPtrRigidTy`, which `annealRigidTyLayoutCompat` uses. -/
@[reducible]
def isThinRawPtrRigidTy : RigidTy → Bool
  | .rawPtr _ pt =>
    match pt with
    | .slice _ | .str | .dynamic _ => false
    | _ => true
  | _ => false

/-- Thin pointer-like `RigidTy` check matching `Miri.Interpreter.LayoutCompat.thinPointer`
(`LayoutCompat.lean:185-188, 218-220`): references and raw pointers to pointees
other than slices, `str`, and trait objects, as well as function pointers, all have
`BackendRepr.Scalar (.Pointer AddressSpace(0))` on the 64-bit target, so any two of
them are ABI-compatible (e.g. `&u8` ↔ `*mut u32`, `fn()` ↔ `*const u8`). -/
@[reducible]
def isThinPtrRigidTy : RigidTy → Bool
  | .rawPtr _ pt | .ref _ pt =>
    match pt with
    | .slice _ | .str | .dynamic _ => false
    | _ => true
  | .fnPtr _ _ _ _ => true
  | _ => false

/-- Wide-pointer metadata class of a reference / raw pointer `RigidTy`, matching the
`pointee` / `pointerMetadataType` comparison of
`Miri.Interpreter.LayoutCompat.layoutCompat` (`LayoutCompat.lean:221-227`):
pointers to slices and `str` carry `usize` metadata (`some none`), pointers to
`dyn Trait` carry `DynMetadata<dyn Trait>` (`some (some traitPath)`), and every
other type has no wide-pointer metadata (`none`). -/
@[reducible]
def annealWidePtrMetadata : RigidTy → Option (Option DefPath)
  | .rawPtr _ pt | .ref _ pt =>
    match pt with
    | .slice _ | .str => some none
    | .dynamic traitPath => some (some traitPath)
    | _ => none
  | _ => none

/-- Runtime ABI layout compatibility between a caller `RigidTy` and a callee
`RigidTy` on a 64-bit target, relaxing syntactic `rigidTyEq` to follow canonical
`Miri.Interpreter.LayoutCompat.layoutCompat` / `checkArgumentCompat`
(`LayoutCompat.lean:208-238`) on the non-ADT fragment (transparent/NPO ADT
unfolding and C-type identity are not modelled, so such pairs are rejected unless
syntactically equal):
1. Syntactically equal types (`rigidTyEq callerTy calleeTy`);
2. Trivial-ABI 1-ZSTs on both sides (`isTrivial1ZstRigidTy`);
3. Thin pointers on both sides (`isThinPtrRigidTy`, e.g. `*const u8` ↔ `*mut u32`,
   `&u8` ↔ `*mut u32`, `fn()` ↔ `*const u8`);
4. Wide pointers with equal metadata types (`annealWidePtrMetadata`, e.g.
   `&str` ↔ `*mut [u32]`; `&dyn A` ↔ `&dyn B` only when `A = B`);
5. Same-width, same-signedness integers (`annealIntAbiOfRigidTy`, e.g.
   `usize` ↔ `u64`, `isize` ↔ `i64`, and `char` ↔ `u32`). -/
@[reducible]
def annealRigidTyLayoutCompat (callerTy calleeTy : RigidTy) : Bool :=
  Bool.or
    (rigidTyEq callerTy calleeTy)
    (Bool.or
      (Bool.and (isTrivial1ZstRigidTy callerTy) (isTrivial1ZstRigidTy calleeTy))
      (Bool.or
        (Bool.and (isThinPtrRigidTy callerTy) (isThinPtrRigidTy calleeTy))
        (Bool.or
          (match annealWidePtrMetadata callerTy, annealWidePtrMetadata calleeTy with
           | some none, some none => true
           | some (some t₁), some (some t₂) => stringEq t₁ t₂
           | _, _ => false)
          (match annealIntAbiOfRigidTy callerTy, annealIntAbiOfRigidTy calleeTy with
           | some (w₁, s₁), some (w₂, s₂) => Bool.and (Nat.beq w₁ w₂) (s₁ == s₂)
           | _, _ => false))))

/-- Pointwise `annealRigidTyLayoutCompat` over argument type lists. -/
@[reducible]
def annealRigidTyListLayoutCompat : List RigidTy → List RigidTy → Bool
  | .nil, .nil => true
  | x :: xs, y :: ys =>
    Bool.and (annealRigidTyLayoutCompat x y) (annealRigidTyListLayoutCompat xs ys)
  | _, _ => false

theorem annealRigidTyLayoutCompat_of_rigidTyEq
    {a b : RigidTy} (h : rigidTyEq a b = true) :
    annealRigidTyLayoutCompat a b = true := by
  unfold annealRigidTyLayoutCompat
  rw [h]
  rfl

theorem annealRigidTyListLayoutCompat_of_rigidTyListEq
    {xs ys : List RigidTy} (h : rigidTyListEq xs ys = true) :
    annealRigidTyListLayoutCompat xs ys = true := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x rest ih =>
    cases ys with
    | nil => cases h
    | cons y restY =>
      unfold rigidTyListEq rigidTyListEqAux at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hxy, hrest⟩
      unfold annealRigidTyListLayoutCompat
      rw [annealRigidTyLayoutCompat_of_rigidTyEq hxy, ih hrest]
      rfl

/-- `annealRigidTyLayoutCompat` is strictly coarser than syntactic `rigidTyEq`:
it equates `usize` ↔ `u64`, `isize` ↔ `i64`, and `*const u8` ↔ `*mut u32`
(where `rigidTyEq = false`), while still rejecting incompatible widths/signedness
such as `u8` ↔ `u64` and `i32` ↔ `u32`. -/
theorem annealRigidTyLayoutCompat_strictly_coarser_than_rigidTyEq :
    (annealRigidTyLayoutCompat (.uint .usize) (.uint .u64) = true ∧
      rigidTyEq (.uint .usize) (.uint .u64) = false) ∧
    (annealRigidTyLayoutCompat (.int .isize) (.int .i64) = true ∧
      rigidTyEq (.int .isize) (.int .i64) = false) ∧
    (annealRigidTyLayoutCompat (.rawPtr .not (.uint .u8)) (.rawPtr .mut (.uint .u32)) = true ∧
      rigidTyEq (.rawPtr .not (.uint .u8)) (.rawPtr .mut (.uint .u32)) = false) ∧
    annealRigidTyLayoutCompat (.uint .u8) (.uint .u64) = false ∧
    annealRigidTyLayoutCompat (.int .i32) (.uint .u32) = false := by
  decide

/-- Concrete agreement of `annealRigidTyLayoutCompat` with canonical
`LayoutCompat.layoutCompat` on cases where the pre-`ep1-B4` relation disagreed with
it or which exercise every compatibility class: `char` ↔ `u32` is compatible
(canonical `integer` maps `char` to `(.I32, false)`) while `char` ↔ `i32` is not;
`[u64; 0]` and `[u8; 0]` are not trivial-ABI 1-ZSTs (so not compatible with `()`),
while `((), !)` ↔ `[(); 3]` are; references, raw pointers, and function pointers to
thin pointees are mutually compatible; wide pointers are compatible exactly when
their metadata types agree (`&str` ↔ `*mut [u32]`, `&dyn A` ↔ `*mut dyn A`, but not
`&[u8]` ↔ `&u8` or `&dyn A` ↔ `&dyn B`). -/
theorem annealRigidTyLayoutCompat_canonical_cases :
    annealRigidTyLayoutCompat .char (.uint .u32) = true ∧
    annealRigidTyLayoutCompat .char (.int .i32) = false ∧
    annealRigidTyLayoutCompat (.array (.uint .u64) 0) (.tuple []) = false ∧
    annealRigidTyLayoutCompat (.array (.uint .u8) 0) (.tuple []) = false ∧
    annealRigidTyLayoutCompat (.tuple [.tuple [], .never]) (.array (.tuple []) 3) = true ∧
    annealRigidTyLayoutCompat (.ref .not (.uint .u8)) (.rawPtr .mut (.uint .u32)) = true ∧
    annealRigidTyLayoutCompat (.fnPtr [] (.tuple []) .safe .rust) (.rawPtr .not (.uint .u8)) = true ∧
    annealRigidTyLayoutCompat (.ref .not .str) (.rawPtr .mut (.slice (.uint .u32))) = true ∧
    annealRigidTyLayoutCompat (.ref .not (.slice (.uint .u8))) (.ref .not (.uint .u8)) = false ∧
    annealRigidTyLayoutCompat (.ref .not (.dynamic "A")) (.ref .not (.dynamic "B")) = false ∧
    annealRigidTyLayoutCompat (.ref .not (.dynamic "A")) (.rawPtr .mut (.dynamic "A")) = true := by
  decide

/-- Runtime `FnAbi` compatibility check between a function-pointer registry
entry `fnEntry` and the call site's `RigidTy.fnPtr callerInputs callerOutput _ callerAbi`
signature (`Call.evalCalleeAndArgs` / `Call.initStackFrame` at `Call.lean:190-197, 254-346`
and `LayoutCompat.checkArgumentCompat` at `LayoutCompat.lean:208-238`).
Unlike Stage-1 `fnEntryCompatibleWithCallSite` (`Terminators.lean:244-280`),
canonical `lean-miri`:
1. checks runtime `FnAbi` convention and arity without enforcing HIR/MIR
   `Safety` (`safetyCompatible`), because `unsafe fn()` and `fn()` share an
   identical runtime `FnAbi` in `rustc`;
2. checks argument and return ABI layout compatibility via
   `annealRigidTyListLayoutCompat` / `annealRigidTyLayoutCompat` rather than
   syntactic `rigidTyListEq` / `rigidTyEq` (permitting layout-compatible pairs
   such as `usize` ↔ `u64`, `isize` ↔ `i64`, `char` ↔ `u32`, `*const T` ↔ `*mut U`,
   `&T` ↔ `fn()`, and `&str` ↔ `*mut [U]`; see
   `annealRigidTyLayoutCompat_canonical_cases`). -/
def annealFnPtrAbiCompatible
    (fnEntry : FnPtrEntry)
    (callerInputs : List RigidTy)
    (callerOutput : RigidTy)
    (callerAbi : CallConv)
    (argCount : Nat) : Bool :=
  let entryArityOk :=
    match fnEntry.fnSig with
    | .none => true
    | .some (.fnPtr sigInputs _ _ sigAbi) =>
      Bool.and
        (Bool.not (callConvEq sigAbi .rustIntrinsic))
        (Nat.beq (length sigInputs) argCount)
    | .some _ => false
  let callerSigOk :=
    Bool.and
      (Bool.not (callConvEq callerAbi .rustIntrinsic))
      (Bool.and
        (Nat.beq (length callerInputs) argCount)
        (match fnEntry.fnSig with
         | .none => true
         | .some (.fnPtr sigInputs sigOutput _ sigAbi) =>
           Bool.and
             (Nat.beq (length callerInputs) (length sigInputs))
             (Bool.and
               (callConvEq callerAbi sigAbi)
               (Bool.and
                 (annealRigidTyListLayoutCompat callerInputs sigInputs)
                 (annealRigidTyLayoutCompat callerOutput sigOutput)))
         | .some _ => false))
  Bool.and entryArityOk callerSigOk

/-- Whenever Stage-1's stricter syntactic `fnEntryCompatibleWithCallSite`
succeeds for a `RigidTy.fnPtr callerInputs callerOutput callerSafety callerAbi`
call-site type, canonical Miri's layout-based `annealFnPtrAbiCompatible` also
succeeds. -/
theorem annealFnPtrAbiCompatible_of_fnEntryCompatibleWithCallSite
    {fnEntry : FnPtrEntry} {argCount : Nat} {fnTy : Ty}
    {callerInputs : List RigidTy} {callerOutput : RigidTy}
    {callerSafety : Safety} {callerAbi : CallConv}
    (hty : fnTy.kind = .fnPtr callerInputs callerOutput callerSafety callerAbi)
    (hcompat : fnEntryCompatibleWithCallSite fnEntry argCount (some fnTy) = true) :
    annealFnPtrAbiCompatible fnEntry callerInputs callerOutput callerAbi argCount = true := by
  cases fnTy with
  | mk k lidx =>
    dsimp only at hty
    subst hty
    unfold fnEntryCompatibleWithCallSite at hcompat
    unfold annealFnPtrAbiCompatible
    cases hfnSig : fnEntry.fnSig with
    | none =>
      rw [hfnSig] at hcompat
      dsimp only [Bool.true_and] at hcompat ⊢
      exact hcompat
    | some sigTy =>
      rw [hfnSig] at hcompat
      cases sigTy with
      | fnPtr sigInputs sigOutput sigSafety sigAbi =>
        dsimp only [] at hcompat ⊢
        rcases Bool.and_eq_true_iff.mp hcompat with ⟨hentry, hcaller⟩
        rw [hentry, Bool.true_and]
        rcases Bool.and_eq_true_iff.mp hcaller with ⟨hnot_intr, hrest₁⟩
        rcases Bool.and_eq_true_iff.mp hrest₁ with ⟨harity, hsig⟩
        rcases Bool.and_eq_true_iff.mp hsig with ⟨hlen, hsig₂⟩
        rcases Bool.and_eq_true_iff.mp hsig₂ with ⟨hconv, hsig₃⟩
        rcases Bool.and_eq_true_iff.mp hsig₃ with ⟨_, hsig₄⟩
        rcases Bool.and_eq_true_iff.mp hsig₄ with ⟨hin, hout⟩
        rw [hnot_intr, harity, hlen, hconv,
          annealRigidTyListLayoutCompat_of_rigidTyListEq hin,
          annealRigidTyLayoutCompat_of_rigidTyEq hout]
        rfl
      | _ => cases hcompat

/-- Embed Anneal's `fnPtrs : List FnPtrEntry` table into canonical `lean-miri`'s
`Miri.Interpreter.FunctionPointers.Registry FnPtrEntry` (`FunctionPointers.lean:16-19`).
Because `AnnealMachine` (`Translate.lean:923-928`) stores only `memory`,
`addresses`, and `borrowTracker` (so `AnnealMachine` struct literals across
`LM-1.1..LM-3.3` stay unchanged), `annealStepHooksLM4_1` takes `fnPtrs` as an
explicit parameter representing the machine's `FunctionPointers.Registry`.

Modelling note: canonical Miri registers a reified function item as
`FnVal.Instance callee` in `Registry.functions` (keyed by its `CallInstance` and
salt). Anneal identifies functions by `defPath` and has no `CallInstance`, so every
entry is embedded as an `FnVal.Other` payload in `Registry.extras`, which canonical
`FunctionPointers.getFnAlloc` consults first (`FunctionPointers.lean:137-139`). The
correspondence with Stage-1 `lookupFnPtr` holds for every table whose allocation
identifiers fit in `UInt64` (`annealFnPtrRegistry_find_eq`). -/
def annealFnPtrRegistry (fnPtrs : List FnPtrEntry) :
    Miri.Interpreter.FunctionPointers.Registry FnPtrEntry :=
  { functions := #[]
    extras :=
      (fnPtrs.filterMap fun e =>
        if h : UInt64.ofNat e.allocId ≠ 0 then
          some (⟨UInt64.ofNat e.allocId, h⟩, e)
        else
          none).toArray }

/-- Looking up `mAllocId` in `(annealFnPtrRegistry [fnEntry]).extras` (as
`Miri.Interpreter.FunctionPointers.getFnAlloc` does at `FunctionPointers.lean:138`)
agrees with `lookupFnPtr [fnEntry] mAllocId.value.toNat`. -/
theorem annealFnPtrRegistry_singleton_find_eq
    (fnEntry : FnPtrEntry) (mAllocId : Miri.Memory.AllocId)
    (hid : mAllocId.value.toNat = fnEntry.allocId) :
    ((annealFnPtrRegistry [fnEntry]).extras.find? (·.1 == mAllocId)).map Prod.snd =
      lookupFnPtr [fnEntry] mAllocId.value.toNat := by
  have hu64 : UInt64.ofNat fnEntry.allocId = mAllocId.value := by
    rw [← hid, UInt64.ofNat_toNat]
  have hnz : UInt64.ofNat fnEntry.allocId ≠ 0 := by
    rw [hu64]; exact mAllocId.nonzero
  have halloc_eq : (⟨UInt64.ofNat fnEntry.allocId, hnz⟩ : Miri.Memory.AllocId) = mAllocId := by
    cases mAllocId; simp [hu64]
  unfold annealFnPtrRegistry lookupFnPtr
  simp [hnz, halloc_eq, hid]

/-- General form of `annealFnPtrRegistry_singleton_find_eq`: whenever every entry's
`allocId` lies below `UInt64.size` (so `UInt64.ofNat` is injective on them), looking up
any `mAllocId` in `(annealFnPtrRegistry fnPtrs).extras` (as canonical
`FunctionPointers.getFnAlloc` does at `FunctionPointers.lean:138`) agrees with Stage-1
`lookupFnPtr fnPtrs mAllocId.value.toNat`, including when the lookup misses and when
the table contains an entry with `allocId = 0` (dropped by the embedding, never found
by `lookupFnPtr` because `mAllocId` is nonzero). -/
theorem annealFnPtrRegistry_find_eq
    (fnPtrs : List FnPtrEntry) (mAllocId : Miri.Memory.AllocId)
    (hrange : ∀ e ∈ fnPtrs, e.allocId < UInt64.size) :
    ((annealFnPtrRegistry fnPtrs).extras.find? (·.1 == mAllocId)).map Prod.snd =
      lookupFnPtr fnPtrs mAllocId.value.toNat := by
  unfold annealFnPtrRegistry
  simp only [List.find?_toArray]
  induction fnPtrs with
  | nil => rfl
  | cons e rest ih =>
    have he : e.allocId < UInt64.size := hrange e (List.mem_cons_self ..)
    have hrest : ∀ e' ∈ rest, e'.allocId < UInt64.size :=
      fun e' h => hrange e' (List.mem_cons_of_mem _ h)
    have hiff : (UInt64.ofNat e.allocId = mAllocId.value) ↔ e.allocId = mAllocId.value.toNat := by
      constructor
      · intro h
        have := congrArg UInt64.toNat h
        rwa [UInt64.toNat_ofNat_of_lt' he] at this
      · intro h
        rw [h, UInt64.ofNat_toNat]
    unfold lookupFnPtr
    simp only [List.filterMap_cons]
    by_cases hz : UInt64.ofNat e.allocId ≠ 0
    · simp only [hz, ne_eq, not_false_eq_true, ↓reduceDIte, List.find?_cons]
      by_cases heq : e.allocId = mAllocId.value.toNat
      · cases mAllocId
        simp_all
      · have hbeq : (⟨UInt64.ofNat e.allocId, hz⟩ == mAllocId) = false := by
          cases mAllocId
          simp_all
        simp only [hbeq]
        rw [Bool.eq_false_iff.mpr (fun h => heq (Nat.eq_of_beq_eq_true h))]
        exact ih hrest
    · have hz' : UInt64.ofNat e.allocId = 0 := by simpa using hz
      simp only [hz, ↓reduceDIte]
      have hne : e.allocId ≠ mAllocId.value.toNat := by
        intro h
        apply mAllocId.nonzero
        rw [← hiff.mpr h, hz']
      rw [Bool.eq_false_iff.mpr (fun h => hne (Nat.eq_of_beq_eq_true h))]
      exact ih hrest

/-- Runtime `FnAbi` compatibility between a resolved `fnEntry : FnPtrEntry` and
the linked `calleeBody : CapturedMir` (`Call.initStackFrame` at `Call.lean:254-264`,
matching Stage-1 `checkCalleeTargetCompatible` at `Terminators.lean:411-437`). -/
def annealCalleeAbiCompatible
    (fnEntry : FnPtrEntry)
    (calleeBody : CapturedMir)
    (argCount : Nat) : Bool :=
  Bool.and
    (Bool.not (callConvEq calleeBody.fnAbi.conv .rustIntrinsic))
    (Bool.and
      (Nat.beq calleeBody.argCount argCount)
      (match fnEntry.fnSig with
       | .none => true
       | .some (.fnPtr sigInputs sigOut _ sigAbi) =>
         Bool.and
           (Nat.beq (length sigInputs) calleeBody.argCount)
           (Bool.and
             (callConvEq sigAbi calleeBody.fnAbi.conv)
             (calleeLocalDeclsCompatible
               fnEntry.typeArgs
               calleeBody.localDecls
               calleeBody.argCount
               sigInputs
               sigOut))
       | .some _ => false))

/-- Evaluate a `Terminator.Call` with a non-constant `func` operand (`extractCalleeDefPath? func = none`),
following canonical `lean-miri`'s `Call.evalCalleeAndArgs` (`Call.lean:183-206`),
`FunctionPointers.allocation` / `getPtrFn` (`FunctionPointers.lean:122-145`), and
`Call.initStackFrame` (`Call.lean:254-264`):
1. Evaluates `func` (`annealEvalOperand`), faulting with UB on a `.dead` local
   and deinitializing on `.Move`;
2. Evaluates `argOps` left-to-right (`annealEvalCallArgsLM4_1`);
3. Dispatches on `func`'s declared type (`operandTy`):
   * Monomorphic ZST function item (`RigidTy.fnDef defPath []`): resolves
     `findCallee? callees defPath` and pushes `calleeBody` (or faults with UB on
     a diverging call to `isUnreachableCallTarget defPath`);
   * Indirect function pointer (`RigidTy.fnPtr callerInputs callerOutput _ callerAbi`):
     reads the pointer scalar (`annealReadImmediate` -> `toScalar` -> `toPointer`),
     faulting with UB on `.uninit`, provenance-free integer pointers
     (`intoPointerOrAddr = .error _` -> `DanglingIntPointer`), unmapped addresses
     (`annealResolvePtr = .error _` -> `DanglingIntPointer`), non-zero offsets
     (`offset != .ZERO` -> `InvalidFunctionPointer`), or non-function allocations
     (`lookupFnPtr fnPtrs allocId = none` -> `InvalidFunctionPointer`), then
     validates runtime `FnAbi` compatibility (`annealFnPtrAbiCompatible` and
     `annealCalleeAbiCompatible`, without checking HIR/MIR `Safety`) and pushes
     `calleeBody` via `annealPushCalleeFrameLM4_1`. -/
def annealEvalNonConstCallLM4_1
    (currentBody : CapturedMir)
    (callees : List CapturedMir)
    (fnPtrs : List FnPtrEntry)
    (func : MirAst.Operand)
    (argOps : List MirAst.Operand)
    (dest : Miri.MIR.Place)
    (targetOpt : Option Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction)
    (state : AnnealStepState) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  let mirFunc := translateOperand func
  let mirArgOps := argOps.map translateOperand
  match Miri.Interpreter.runRvalue
      (do
        let funcOp ← annealEvalOperand currentBody.localDecls currentBody.layouts mirFunc none
        let argImms ← annealEvalCallArgsLM4_1 currentBody.localDecls currentBody.layouts mirArgOps
        return (funcOp, argImms))
      state with
  | (stateAfterArgs, .error err) => (stateAfterArgs, .error err)
  | (stateAfterArgs, .ok (funcOp, argImms)) =>
    match operandTy currentBody.localDecls currentBody.layouts func with
    | .some { kind := .fnDef defPath .nil, .. } =>
      match findCallee? callees defPath with
      | some calleeBody =>
        annealPushCalleeFrameLM4_1 currentBody calleeBody dest targetOpt unwind
          argImms stateAfterArgs
      | none =>
        if targetOpt.isNone && isUnreachableCallTarget defPath then
          (stateAfterArgs, .error (.undefinedBehavior "entering unreachable_unchecked"))
        else
          (stateAfterArgs, .error (.unsupported "unresolved external call"))
    | .some { kind := .fnPtr callerInputs callerOutput _ callerAbi, .. } =>
      match Miri.Interpreter.runRvalue (annealReadImmediate funcOp) stateAfterArgs with
      | (stateAfterPtr, .error err) => (stateAfterPtr, .error err)
      | (stateAfterPtr, .ok fnImm) =>
        match fnImm.imm.toScalar with
        | .error err =>
          (stateAfterPtr, .error (Miri.Interpreter.ScalarOps.immediateError err))
        | .ok sc =>
          match sc.toPointer annealTargetDataLayout with
          | .error err =>
            (stateAfterPtr, .error (Miri.Interpreter.ScalarOps.scalarError err))
          | .ok ptr =>
            match ptr.intoPointerOrAddr with
            | .error _ =>
              (stateAfterPtr, .error (.undefinedBehavior "DanglingIntPointer"))
            | .ok _ =>
              match annealResolvePtr stateAfterPtr.machine ptr 0 with
              | .error _ =>
                (stateAfterPtr, .error (.undefinedBehavior "DanglingIntPointer"))
              | .ok resolved =>
                if resolved.offset != Miri.ABI.Size.ZERO then
                  (stateAfterPtr, .error (.undefinedBehavior "InvalidFunctionPointer"))
                else
                  match lookupFnPtr fnPtrs resolved.allocId.value.toNat with
                  | .none =>
                    (stateAfterPtr, .error (.undefinedBehavior "InvalidFunctionPointer"))
                  | .some fnEntry =>
                    if !fnEntry.typeArgs.isEmpty then
                      (stateAfterPtr, .error (.unsupported "polymorphic indirect fnPtr"))
                    else if !annealFnPtrAbiCompatible fnEntry callerInputs callerOutput callerAbi argImms.length then
                      (stateAfterPtr, .error (.undefinedBehavior "indirect call ABI mismatch"))
                    else
                      match findCallee? callees fnEntry.defPath with
                      | .none =>
                        (stateAfterPtr, .error (.unsupported "unresolved indirect external call"))
                      | .some calleeBody =>
                        if !annealCalleeAbiCompatible fnEntry calleeBody argImms.length then
                          (stateAfterPtr, .error (.undefinedBehavior "callee ABI mismatch"))
                        else
                          annealPushCalleeFrameLM4_1 currentBody calleeBody dest targetOpt unwind
                            argImms stateAfterPtr
    | _ =>
      (stateAfterArgs, .error (.unsupported "non-constant polymorphic or closure call"))

/-- Evaluate a `Terminator.Call` in `LM-4.1`, mirroring Stage-1 `Trusted`
`evalTerminator (.call ..)` (`Terminators.lean:3067-3246`) and canonical
`lean-miri`'s `Call.evalCalleeAndArgs` + `FunctionPointers.getPtrFn`:
1. Looks up the active basic block in `currentBody`:
   * For constant function-item callees (`extractCalleeDefPath? func = some defPath`),
     evaluates `argOps` left-to-right via `annealEvalCallArgsLM4_1` and pushes
     `calleeBody` when linked in `callees` (`findCallee?`), or faults with UB on
     a diverging call to `isUnreachableCallTarget defPath`;
   * For non-constant `func` operands (`extractCalleeDefPath? func = none`: local
     ZST `FnDef` items and indirect `FnPtr` function pointers), delegates to
     `annealEvalNonConstCallLM4_1` (`callees`, `fnPtrs`).
2. Every other unlinked call (external calls, unlinked `core::panicking` panic
   lang items) returns `.unsupported`. -/
def annealEvalCallLM4_1
    (currentBody : CapturedMir)
    (callees : List CapturedMir)
    (terminator : Miri.MIR.Terminator)
    (state : AnnealStepState)
    (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  match state.stack.currentFrame? with
  | none => (state, .error (.stack .emptyStack))
  | some callerFrame =>
    match callerFrame.location with
    | .unwinding _ => (state, .error (.invalidProgram "call terminator while unwinding"))
    | .mir loc =>
      match get? currentBody.basicBlocks loc.block with
      | none => (state, .error (.invalidBlock loc.block))
      | some bb =>
        match bb.terminator.kind, terminator.kind with
        | .call func argOps _ (.none) _, .Call _ _ dest .none unwind _ _ =>
          match extractCalleeDefPath? func with
          | none =>
            annealEvalNonConstCallLM4_1 currentBody callees fnPtrs func argOps
              dest none unwind state
          | some defPath =>
            let mirArgOps := argOps.map translateOperand
            match Miri.Interpreter.runRvalue
                (annealEvalCallArgsLM4_1 currentBody.localDecls currentBody.layouts mirArgOps)
                state with
            | (stateAfterArgs, .error err) => (stateAfterArgs, .error err)
            | (stateAfterArgs, .ok argImms) =>
              match findCallee? callees defPath with
              | some calleeBody =>
                annealPushCalleeFrameLM4_1 currentBody calleeBody dest none unwind
                  argImms stateAfterArgs
              | none =>
                if isUnreachableCallTarget defPath then
                  (stateAfterArgs, .error (.undefinedBehavior "entering unreachable_unchecked"))
                else
                  (stateAfterArgs,
                   .error (.unsupported "diverging call to unlinked non-unreachable callee"))
        | .call func argOps _ (.some targetBb) _, .Call _ _ dest (.some _) unwind _ _ =>
          match extractCalleeDefPath? func with
          | none =>
            annealEvalNonConstCallLM4_1 currentBody callees fnPtrs func argOps
              dest (some targetBb) unwind state
          | some defPath =>
            let mirArgOps := argOps.map translateOperand
            match Miri.Interpreter.runRvalue
                (annealEvalCallArgsLM4_1 currentBody.localDecls currentBody.layouts mirArgOps)
                state with
            | (stateAfterArgs, .error err) => (stateAfterArgs, .error err)
            | (stateAfterArgs, .ok argImms) =>
              match findCallee? callees defPath with
              | none => (stateAfterArgs, .error (.unsupported "unresolved external call"))
              | some calleeBody =>
                annealPushCalleeFrameLM4_1 currentBody calleeBody dest (some targetBb) unwind
                  argImms stateAfterArgs
        | _, _ => (state, .error (.invalidProgram "mismatched call terminator"))

/-- Function-pointer allocation hook (`CastHooks.functionPointer`) for the
`ReifyFnPointer` arm of canonical `Miri.Interpreter.Cast.cast` (`Cast.lean:336-341`:
`ensureMonomorphic`, `typeInfo` = `.fnDefinition`, `requireNoBoundVars`,
`resolveFunction`, then `writePointer (← functionPointer fnInstance) dest`;
`Miri.Interpreter.FunctionPointers.functionPointer` at `FunctionPointers.lean:117-118`).
Canonical Miri performs **no** signature, safety, or calling-convention validation
when reifying a function item: an ABI-incompatible function pointer only faults
when it is *called* (`Call.initStackFrame`, `annealFnPtrAbiCompatible`).

Modelling notes (this hook is deliberately *not* a replay of Stage-1
`evalReifyFnPointer` at `Places.lean:13784-13926`):
* **No Stage-1 reify-time validation.** Stage-1 additionally rejects
  `extern "rust-intrinsic"` targets, safety-incompatible targets
  (`reifyCoercionSafetyCompatible`), non-`fn`-pointer targets, and linked-callee
  signature mismatches (`checkCalleeSig`) at the cast itself. None of these are
  checked here; `step_stmt_assign_reifyFnPointer_to_indirectFnPtrMovePre_simulation`
  carries them purely as Stage-1-side preconditions (they hold for every
  rustc-typed `ReifyFnPointer`, whose target is the item's own signature).
* **Function identity.** `encodeTyId` collapses every `.fnDef defPath args` (and the
  unit tuple) to `TyId 51`, so the canonical `fnInstance` argument cannot carry the
  item's `defPath`. The hook recovers it from the active
  `StatementKind.assign _ (.cast (.pointerCoercion ck) op targetTy)` statement of
  `currentBody` via `extractReifyCoercionTarget?` on the *source operand type* (the
  information canonical `typeInfo` / `resolveFunction` supply), and uses the cast's
  destination type `targetTy.kind` only as the interning key. A generic item
  (non-empty type arguments, which canonical Miri would resolve) is reported as
  `StepError.unsupported`, and a non-`fnDef` source (canonical
  `invalid "reify fn pointer on non-function definition"`) as
  `StepError.invalidProgram`; neither is reported as undefined behavior.
* **Allocation identity.** `AnnealMachine` has no `FunctionPointers.Registry`
  (`annealFnPtrRegistry`), so Stage-1's `fnPtrs` table plays that role: an existing
  entry for `(defPath, [], some targetTy.kind)` is reused (canonical `reserve` dedup,
  `FunctionPointers.lean:74-78`), otherwise `nextFnPtrAllocId fnPtrs` is reserved
  (canonical `MemoryState.reserveAllocId`), so both machines name the function
  allocation by the same identifier (`mAllocId.value.toNat = allocId`).
* **Address and tag.** An address already assigned in `st.machine.addresses` is
  reused; otherwise `annealStackBaseAddr mAllocId` is recorded (abstracting canonical
  `adjustRootPointer`'s lazy address assignment). The root tag is `BorTag.one`
  (canonical `rootPointer` without a borrow tracker, `FunctionPointers.lean:104-115`). -/
def annealReifyFnPointerAlloc
    (currentBody : CapturedMir)
    (fnPtrs : List FnPtrEntry) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Memory.Pointer (Option AnnealProv)) :=
  fun st =>
    match st.stack.currentFrame? with
    | none => .error (.stack .emptyStack) st
    | some frame =>
      match frame.location with
      | .unwinding _ => .error .expectedMirLocation st
      | .mir loc =>
        match get? currentBody.basicBlocks loc.block with
        | none => .error (.invalidBlock loc.block) st
        | some bb =>
          match get? bb.statements loc.statementIndex with
          | some { kind := .assign _ (.cast (.pointerCoercion ck) op targetTy), .. } =>
            match extractReifyCoercionTarget? ck (operandTy currentBody.localDecls currentBody.layouts op) with
            | some (defPath, []) =>
              let allocId : Nat :=
                match findFnPtrEntry? fnPtrs defPath [] (some targetTy.kind) with
                | some existing => existing.allocId
                | none => nextFnPtrAllocId fnPtrs
              if h : UInt64.ofNat allocId ≠ 0 then
                let mAllocId : Miri.Memory.AllocId := ⟨UInt64.ofNat allocId, h⟩
                match st.machine.lookupBaseAddr mAllocId with
                | some baseAddr =>
                  .ok ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat 0),
                       some (.concrete mAllocId Miri.Memory.BorTag.one)⟩ st
                | none =>
                  let baseAddr := annealStackBaseAddr mAllocId
                  let addresses' :=
                    { st.machine.addresses with
                      baseAddr := #[⟨mAllocId, baseAddr⟩] ++ st.machine.addresses.baseAddr }
                  .ok ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat 0),
                       some (.concrete mAllocId Miri.Memory.BorTag.one)⟩
                    { st with machine := { st.machine with addresses := addresses' } }
              else
                .error (.resourceExhaustion "ReifyFnPointer function allocation ID wrap") st
            | some (_, _ :: _) =>
              .error (.unsupported "ReifyFnPointer of a generic function instance") st
            | none =>
              .error (.invalidProgram "reify fn pointer on non-function definition") st
          | _ => .error (.invalidProgram "expected ReifyFnPointer statement") st

/-- `CastHooks` for the `ReifyFnPointer` arm of `Miri.Interpreter.Cast.cast`
(`Cast.lean:336-341`), extending `annealCastHooks` with `typeInfo 51 = .fnDefinition`,
a placeholder `resolveFunction`, `functionPointer := annealReifyFnPointerAlloc`, and a
provenance-carrying `writePointer`.

Because `encodeTyId` maps both `.fnDef _ _` and the unit tuple to `TyId 51`, the
`typeInfo 51` override is only sound for the source operand of a `ReifyFnPointer`
cast; `annealRvalueHooksLM4_1` therefore dispatches *only* `ReifyFnPointer` casts to
these hooks and every other cast kind to `annealRvalueHooks`'s `annealCastHooks`
(`annealRvalueHooksLM4_1_cast_eq_of_not_reifyFnPointer`). -/
def annealCastHooksLM4_1
    (currentBody : CapturedMir)
    (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.CastHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealCastHooks currentBody.layouts with
    typeInfo := fun _ tyId =>
      if tyId == 51 then
        pure (.fnDefinition 0 #[])
      else
        match castTypeInfoOfEncodedTyId tyId with
        | .ok info => pure info
        | .error err => throw err
    resolveFunction := fun _ _ _ => pure (some ⟨.Item 0, #[]⟩)
    functionPointer := fun _ _ => annealReifyFnPointerAlloc currentBody fnPtrs
    writePointer := fun _ ptr dest =>
      match ptr.provenance with
      | some prov =>
        annealWriteImmediate
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨ptr.offset, prov⟩))
          dest
      | none =>
        throw (.invalidProgram "ReifyFnPointer produced provenance-free pointer") }

/-- `RvalueHooks` for `LM-4.1`: identical to `annealRvalueHooks` except that a
`CastKind.PointerCoercion (.ReifyFnPointer _) _` cast runs canonical
`Miri.Interpreter.Cast.cast` with `annealCastHooksLM4_1` (function-pointer
reification). Every other cast kind uses `annealRvalueHooks`'s own `cast`
(`annealRvalueHooksLM4_1_cast_eq_of_not_reifyFnPointer`), and every non-`cast`
field is `annealRvalueHooks`'s (`annealRvalueHooksLM4_1_eq_annealRvalueHooks_with_cast`). -/
def annealRvalueHooksLM4_1
    (currentBody : CapturedMir)
    (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.RvalueHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealRvalueHooks currentBody.localDecls currentBody.layouts with
    cast := fun c src kind ty dest =>
      match kind with
      | .PointerCoercion (.ReifyFnPointer _) _ =>
        Miri.Interpreter.Cast.cast (annealCastHooksLM4_1 currentBody fnPtrs) c 16 src kind ty dest
      | _ =>
        (annealRvalueHooks currentBody.localDecls currentBody.layouts).cast c src kind ty dest }

/-- `annealRvalueHooksLM4_1` differs from `annealRvalueHooks` in the `cast` field only. -/
theorem annealRvalueHooksLM4_1_eq_annealRvalueHooks_with_cast
    (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry) :
    { annealRvalueHooksLM4_1 currentBody fnPtrs with
        cast := (annealRvalueHooks currentBody.localDecls currentBody.layouts).cast } =
      annealRvalueHooks currentBody.localDecls currentBody.layouts := rfl

/-- On every cast kind other than `PointerCoercion (.ReifyFnPointer _) _`,
`annealRvalueHooksLM4_1`'s `cast` is exactly `annealRvalueHooks`'s (canonical
`Miri.Interpreter.Cast.cast` over `annealCastHooks`), so `annealStepHooksLM4_1`'s
`assign` agrees with `annealStepHooks`'s outside function-pointer reification. -/
theorem annealRvalueHooksLM4_1_cast_eq_of_not_reifyFnPointer
    (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry)
    (c : Unit) (src : Miri.Interpreter.OpTy AnnealProv) (kind : Miri.MIR.CastKind)
    (ty : Miri.MIR.TyId) (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (hkind : ∀ sf cs, kind ≠ .PointerCoercion (.ReifyFnPointer sf) cs) :
    (annealRvalueHooksLM4_1 currentBody fnPtrs).cast c src kind ty dest =
      (annealRvalueHooks currentBody.localDecls currentBody.layouts).cast c src kind ty dest := by
  unfold annealRvalueHooksLM4_1
  dsimp only []
  split
  · rename_i sf cs
    exact absurd rfl (hkind sf cs)
  · rfl

/-- `TerminatorHooks` for `LM-4.1`, extending `annealTerminatorHooks` with
`annealControlHooksLM4_1`, `annealEvalCallLM4_1` (including non-constant `FnDef`
and indirect `FnPtr` calls), `annealEvalDropLM4_1`, and `assertPanic` returning
`.unsupported` (rather than `Translate.lean`'s depth-1 scalar-fragment stub
`.undefinedBehavior "assert panic"`, matching `Panic.lean:6-7`: a failed
assertion invokes the `core::panicking` lang item rather than causing UB, and
`core` panic lang items are unlinked here). -/
def annealTerminatorHooksLM4_1
    (currentBody : CapturedMir)
    (callees : List CapturedMir := .nil)
    (poppedFrame : Miri.TreeBorrows.FrameState := {})
    (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.TerminatorHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.Operand AnnealProv)
      (Miri.Interpreter.RvalueImmTy AnnealProv) :=
  { annealTerminatorHooks currentBody.localDecls currentBody.layouts with
    toControlHooks := annealControlHooksLM4_1 currentBody.localDecls currentBody.layouts poppedFrame
    call := fun _ term state => annealEvalCallLM4_1 currentBody callees term state fnPtrs
    drop := fun _ place target unwind state => annealEvalDropLM4_1 place target unwind state
    assertPanic := fun _ _ _ state =>
      (state, .error (.unsupported "assert panic without linked panic lang item")) }

/-- `StepHooks` for `LM-4.1`, parameterized by the active `CapturedMir` body
`currentBody` (`activeMirBody rootBody s`), available `callees`
(`s.memory.callees`), the popped callee frame's `FrameState`
(`poppedFrame := annealPoppedFrameState s`), and optional registered function
pointers `fnPtrs` (`s.memory.fnPtrs`). Relative to `annealStepHooks`, `assign`
differs only on `PointerCoercion (.ReifyFnPointer _) _` casts
(`annealRvalueHooksLM4_1_eq_annealRvalueHooks_with_cast`,
`annealRvalueHooksLM4_1_cast_eq_of_not_reifyFnPointer`). -/
def annealStepHooksLM4_1
    (currentBody : CapturedMir)
    (callees : List CapturedMir := .nil)
    (poppedFrame : Miri.TreeBorrows.FrameState := {})
    (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.StepHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealStepHooks currentBody.localDecls currentBody.layouts with
    assign := fun choice place rvalue state =>
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace
          (annealRvalueHooksLM4_1 currentBody fnPtrs) choice rvalue place)
        state
    returnFromCurrentFrame := fun choice unwinding state =>
      Miri.Interpreter.ControlFlow.returnFromCurrentFrame
        (annealControlHooksLM4_1 currentBody.localDecls currentBody.layouts poppedFrame)
        choice unwinding state
    terminator := fun choice term state =>
      Miri.Interpreter.ControlFlow.evalTerminator
        (annealTerminatorHooksLM4_1 currentBody callees poppedFrame fnPtrs)
        choice term state }

/-- Canonical `LM-4.1` `StepHooks` instantiated at Stage-1 `MachineState` `s`
rooted at `rootBody` (`activeMirBody rootBody s`, `s.memory.callees`,
`annealPoppedFrameState s`, and `s.memory.fnPtrs`). -/
def annealStepHooksForState (rootBody : CapturedMir) (s : MachineState) :
    Miri.Interpreter.StepHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees
    (annealPoppedFrameState s) s.memory.fnPtrs

/-- **Non-canonical, lang-item-free** `ControlHooks` variant
(`annealControlHooksWithDirectUnwind`) where `unwindTerminate` halts immediately with
`StepError.termination (.abort "panic in a function that cannot unwind")`
(`Miri.Concurrency.TerminationInfo.abort` at `Termination.lean:21`).

Canonical `lean-miri` (`ExecutionControl.lean:28-30`) instead *calls* the
`unwindTerminateFunction` lang item (`core::panicking::panic_cannot_unwind` /
`panic_in_cleanup`) with continuation `.goto none .Unreachable`; that callee prints the
message and aborts, so this hook collapses a linked lang-item call into its observable
abnormal-termination outcome, which is exactly Stage-1's lang-item-free
`MirStepNode.retOutcome .abort` (`Terminators.lean:643, 681, 3004`). The canonical
`annealControlHooksLM4_1` (no `core` linked) reports `.unsupported "unwindTerminate"`. -/
def annealControlHooksWithDirectUnwind
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (poppedFrame : Miri.TreeBorrows.FrameState := {}) :
    Miri.Interpreter.ControlHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.Operand AnnealProv) :=
  { annealControlHooksLM4_1 localDecls layouts poppedFrame with
    unwindTerminate := fun _ _ state =>
      (state, .error (.termination (.abort "panic in a function that cannot unwind"))) }

/-- **Non-canonical, lang-item-free** `TerminatorHooks` variant
(`annealTerminatorHooksWithDirectUnwind`) where:
1. `toControlHooks` uses `annealControlHooksWithDirectUnwind`
   (`unwindTerminate` -> `StepError.termination (.abort ...)`), and
2. `assertPanic` dispatches `Miri.Interpreter.ControlFlow.unwindToBlock` directly
   on the assertion's `UnwindAction` (`ControlFlow.lean:42-60`), matching Stage-1
   `Trusted`'s lang-item-free `applyUnwindAction` (`Terminators.lean:3272`).

Canonical `lean-miri` (`ExecutionMachine.lean:339`, `Panic.assertPanic` at
`Panic.lean:103-118`) instead *calls* the assertion's `core::panicking` lang item with
the assertion's `UnwindAction`; that is a 2-step (push, then `UnwindResume`) execution
even when the lang item immediately unwinds (cf.
`step_terminator_call_linked_panic_unwind_simulation` under the canonical
`annealStepHooksForState`), whereas Stage-1 jumps in 1 step. This variant inlines the
lang item's unwinding effect so that the 1-step Stage-1 behaviour can be simulated in
lockstep; theorems stated over it are relative to that abstraction, not to canonical
`lean-miri`, whose `annealTerminatorHooksLM4_1.assertPanic` reports `.unsupported`. -/
def annealTerminatorHooksWithDirectUnwind
    (currentBody : CapturedMir)
    (callees : List CapturedMir := .nil)
    (poppedFrame : Miri.TreeBorrows.FrameState := {})
    (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.TerminatorHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.Operand AnnealProv)
      (Miri.Interpreter.RvalueImmTy AnnealProv) :=
  let ctrlHooks :=
    annealControlHooksWithDirectUnwind currentBody.localDecls currentBody.layouts poppedFrame
  { annealTerminatorHooksLM4_1 currentBody callees poppedFrame fnPtrs with
    toControlHooks := ctrlHooks
    assertPanic := fun choice _ unwind state =>
      Miri.Interpreter.ControlFlow.unwindToBlock ctrlHooks choice unwind state }

/-- **Non-canonical, lang-item-free** `StepHooks` variant
(`annealStepHooksWithDirectUnwind`) pairing `annealControlHooksWithDirectUnwind` and
`annealTerminatorHooksWithDirectUnwind` (see their docstrings) for direct
`applyUnwindAction` simulation on failed assertions and `TerminationInfo.abort`
simulation on `.terminate` unwinding. It agrees with `annealStepHooksForState` on
`assign` and every other non-control field. -/
def annealStepHooksWithDirectUnwind
    (rootBody : CapturedMir)
    (s : MachineState) :
    Miri.Interpreter.StepHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let currentBody := activeMirBody rootBody s
  let poppedFrame := annealPoppedFrameState s
  { annealStepHooksForState rootBody s with
    returnFromCurrentFrame := fun choice unwinding state =>
      Miri.Interpreter.ControlFlow.returnFromCurrentFrame
        (annealControlHooksWithDirectUnwind currentBody.localDecls currentBody.layouts poppedFrame)
        choice unwinding state
    terminator := fun choice term state =>
      Miri.Interpreter.ControlFlow.evalTerminator
        (annealTerminatorHooksWithDirectUnwind currentBody s.memory.callees poppedFrame s.memory.fnPtrs)
        choice term state }

/-- A `k`-step (`k ≥ 1`) execution trace of `Miri.Interpreter.Step.step` for
multi-frame stack unwinding where every step `i` uses the exact
`annealStepHooksForState rootBody s_i` of the corresponding Stage-1 state `s_i`
along `unwindFromCallStack`, and every intermediate step (`cons`) transitions
through an `UnwindingStateRel rootBody s_i m_i` state (`topFrame.location = .unwinding span`). -/
inductive MiriUnwindSteps (rootBody : CapturedMir) :
    Nat → MachineState → AnnealStepState →
    Miri.Interpreter.StepResult AnnealStepState Bool → Prop where
  | single (s₀ : MachineState) (m₀ m₁ : AnnealStepState)
      (out : Except Miri.Interpreter.StepError Bool) :
      Miri.Interpreter.Step.step (annealStepHooksForState rootBody s₀) () m₀ = (m₁, out) →
      MiriUnwindSteps rootBody 1 s₀ m₀ (m₁, out)
  | cons {k : Nat} (s₀ s₁ : MachineState) (m₀ m₁ : AnnealStepState)
      (res : Miri.Interpreter.StepResult AnnealStepState Bool) :
      s₀.memory.callStack ≠ [] →
      Miri.Interpreter.Step.step (annealStepHooksForState rootBody s₀) () m₀ = (m₁, .ok true) →
      UnwindingStateRel rootBody s₁ m₁ →
      MiriUnwindSteps rootBody k s₁ m₁ res →
      MiriUnwindSteps rootBody (k + 1) s₀ m₀ res

/-- Multi-frame one-step outcome correspondence (`StepRelMultiFrame`) between
Anneal's `stepMirFn rootBody s` and `lean-miri`'s
`Miri.Interpreter.Step.step (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees) () m`:
* `step`: both machines step to `MultiFrameStateRel rootBody`-related states (covers
  intra-frame steps, `Terminator.Call` pushing a frame to depth `d + 1`,
  `Terminator.Return` from a non-root callee popping back to depth `d`, and
  `Terminator.Drop`);
* `retRoot`: returning from the root frame (`s.memory.callStack = []`) produces
  `MirStepNode.retNormal retVal mem'` in Anneal and empties `lean-miri`'s stack
  (`m'.stack.frames = #[]`) with `ImmediateRel` or `MemPlaceRel`-related return
  operand in `_0`;
* `ub`: both machines fault with undefined behavior (`MirStepNode.fail .ub` ↔
  `.error (.undefinedBehavior msg)`). -/
inductive StepRelMultiFrame (rootBody : CapturedMir) (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  | step (s' : MachineState) (m' : AnnealStepState) :
      MultiFrameStateRel rootBody s' m' →
      StepRelMultiFrame rootBody m (MirStepNode.step s') (m', .ok true)
  | retRoot (decl0 : LocalDecl) (retVal : Value)
      (retOp : Miri.Interpreter.Operand AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? rootBody.localDecls 0 = some decl0 →
      (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).returnOperand () m =
        (m, .ok retOp) →
      ((∃ imm0, retOp = .immediate imm0 ∧ ImmediateRel decl0.ty rootBody.layouts retVal imm0) ∨
       (∃ mp0, retOp = .indirect mp0 ∧
         MemPlaceRel m.machine decl0.ty rootBody.layouts (some retVal) mp0)) →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRelMultiFrame rootBody m (MirStepNode.retNormal retVal mem') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelMultiFrame rootBody m (MirStepNode.fail .ub) (m', .error (.undefinedBehavior msg))

theorem MultiFrameStateRel.frames_ne_empty
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : MultiFrameStateRel rootBody s m) :
    m.stack.frames ≠ #[] := by
  rcases h with ⟨tf, hback, _, _, _, _, _, _, _, _, _, _, _⟩
  intro hemp
  rw [hemp] at hback
  cases hback

namespace StepRelMultiFrame

/-- Bidirectional normal step equivalence under `StepRelMultiFrame`. -/
theorem step_iff {rootBody : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelMultiFrame rootBody m aRes mRes) :
    (∃ s', aRes = .step s' ∧ MultiFrameStateRel rootBody s' mRes.1) ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames ≠ #[]) := by
  cases h with
  | step s' m' hrel =>
    exact ⟨fun _ => ⟨rfl, hrel.frames_ne_empty⟩, fun _ => ⟨s', rfl, hrel⟩⟩
  | retRoot _ _ _ _ _ _ _ _ hm' =>
    subst hm'
    constructor
    · rintro ⟨_, h, _⟩; cases h
    · rintro ⟨_, hne⟩; exact False.elim (hne rfl)
  | ub _ _ =>
    constructor
    · rintro ⟨_, h, _⟩; cases h
    · rintro ⟨hok, _⟩; cases hok

/-- Bidirectional root-frame normal return equivalence under `StepRelMultiFrame`. -/
theorem retNormal_iff {rootBody : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelMultiFrame rootBody m aRes mRes) :
    (∃ retVal mem', aRes = .retNormal retVal mem') ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames = #[]) := by
  cases h with
  | step s' m' hrel =>
    constructor
    · rintro ⟨_, _, h⟩; cases h
    · rintro ⟨_, hemp⟩; exact False.elim (hrel.frames_ne_empty hemp)
  | retRoot _ retVal _ mem' _ _ _ _ hm' =>
    subst hm'
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨retVal, mem', rfl⟩⟩
  | ub _ _ =>
    constructor
    · rintro ⟨_, _, h⟩; cases h
    · rintro ⟨hok, _⟩; cases hok

/-- Under `StepRelMultiFrame`, a root-frame normal return produces an
`ImmediateRel` or `MemPlaceRel`-related return operand in `lean-miri`'s `_0`
and empties the stack. -/
theorem retNormal_rel {rootBody : CapturedMir} {m : AnnealStepState}
    {retVal : Value} {mem' : Memory}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelMultiFrame rootBody m (.retNormal retVal mem') mRes) :
    ∃ decl0 retOp,
      get? rootBody.localDecls 0 = some decl0 ∧
      (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).returnOperand () m =
        (m, .ok retOp) ∧
      ((∃ imm0, retOp = .immediate imm0 ∧ ImmediateRel decl0.ty rootBody.layouts retVal imm0) ∨
       (∃ mp0, retOp = .indirect mp0 ∧
         MemPlaceRel m.machine decl0.ty rootBody.layouts (some retVal) mp0)) ∧
      mRes = ({ m with stack := ⟨#[]⟩ }, .ok true) := by
  cases h with
  | retRoot decl0 _ retOp _ _ hdecl hop hrel hm' =>
    subst hm'
    exact ⟨decl0, retOp, hdecl, hop, hrel, rfl⟩

/-- Bidirectional undefined-behavior equivalence under `StepRelMultiFrame`. -/
theorem ub_iff {rootBody : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelMultiFrame rootBody m aRes mRes) :
    (aRes = .fail .ub) ↔ (∃ msg, mRes.2 = .error (.undefinedBehavior msg)) := by
  cases h with
  | step _ _ _ =>
    constructor
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
  | retRoot _ _ _ _ _ _ _ _ _ =>
    constructor
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
  | ub _ msg =>
    exact ⟨fun _ => ⟨msg, rfl⟩, fun _ => rfl⟩

end StepRelMultiFrame

end LeanMiriSpec.Correspondence
