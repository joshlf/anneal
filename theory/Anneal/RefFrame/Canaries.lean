-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal.RefFrame.RangedTree

namespace Anneal.RefFrame

/-!
# `RangedBorrowTree` Canaries (`Anneal.RefFrame.Canaries`)

LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`, `0` `omega`) positive
and single-cause fail-closed negative witnesses for `Anneal.RefFrame.RangedTree`
(all authored declarations compile with zero axioms `[]`; Lean-synthesized
`.injEq` helpers use `propext`):

1. **3-arm `TbPermission.associatedAccess` & Miri protector-exit ordering
   (`interiorMutCell_protector_exit_emits_no_access`, `[]`):** Verifies `.Cell`
   (`accessed = true`) emits zero exit access, `.Unique`/`.Frozen` emit `.Write`
   / `.Read`, and Miri's protector-kept-during-access order catches co-frame
   aliasing UB that premature protector removal misses.
2. **Concrete shared 3-node `topo3` commutation + fault contrasts
   (`canary_shared_topo3_commutation_and_contrasts`, `[]`); the universal
   192-case theorem lives in `RangedTree.lean`.
3. **Straddling-segment split and 3-node chain children-visit mode witnesses
   (`canary_straddling_split_and_chain_visit_modes`, `[]`).
4. **Single-cause fail-closed `RangedBorrowTree` negative regressions
   (`canary_rangedBorrowTree_negative_fail_closed_tests`, `[]`), including
   local-first precedence, `.InvariantFailure` preservation, contiguous segment
   tiling, missing-tag/dangling-parent rejection, release-path coverage, and
   zero-length / skip-children guards.
-/

/-- Tree witnessing interior-mutable `Cell` (`accessed = true`) coexisting with
an accessed co-frame protected `Unique` sibling at `[0..8)`. -/
def cellAndUniqueAliasingTree : RangedBorrowTree :=
  { topology := topo3
    protectedTags := [1, 2]
    segments :=
      [⟨0, 8, [(0, ⟨.Cell, true⟩), (1, ⟨.Cell, true⟩), (2, ⟨.Unique, true⟩)]⟩] }

/-- Tree witnessing co-frame protected `Unique` and `ReservedFrz false` tags
(`[1, 2]`) on `[0..8)` plus unaccessed `[8..16)`. -/
def coframeAliasingOrderTree : RangedBorrowTree :=
  { topology := topo3
    protectedTags := [1, 2]
    segments :=
      [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
               (2, ⟨.ReservedFrz false, true⟩)]⟩,
       ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
               (2, ⟨.ReservedFrz false, false⟩)]⟩] }

/-- Tree witnessing clean 3-arm exit across `[0..8)` (`Cell`), `[8..16)`
(`Unique`), and `[16..24)` (`Frozen`). -/
def threeArmCleanExitTree : RangedBorrowTree :=
  { topology := topo3
    protectedTags := [1]
    segments :=
      [⟨0, 8, [(0, ⟨.Cell, true⟩), (1, ⟨.Cell, true⟩), (2, ⟨.Unique, true⟩)]⟩,
       ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
               (2, ⟨.Frozen, true⟩)]⟩,
       ⟨16, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Frozen, true⟩),
                (2, ⟨.Unique, true⟩)]⟩] }

/-- Verifies all 3 arms of `TbPermission.associatedAccess` and Miri's
protector-kept-during-access order sensitivity (`[]` zero axioms). -/
theorem interiorMutCell_protector_exit_emits_no_access :
    TbPermission.associatedAccess .Cell = none ∧
    TbPermission.associatedAccess .Unique = some .Write ∧
    TbPermission.associatedAccess .Frozen = some .Read ∧
    TbPermission.associatedAccess (.ReservedFrz false) = some .Read ∧
    (let rRel := releaseProtectorKeepProtected cellAndUniqueAliasingTree 1
     let rExit := exitFrameWithProtectors cellAndUniqueAliasingTree [1]
     rRel.status = .Released ∧
     rRel.tree.protectedTags = [1, 2] ∧
     rRel.tree.segments = cellAndUniqueAliasingTree.segments ∧
     rExit.status = .Released ∧
     rExit.tree.protectedTags = [2] ∧
     rExit.tree.segments = cellAndUniqueAliasingTree.segments) ∧
    (let rRel3 := releaseProtectorKeepProtected threeArmCleanExitTree 1
     let rExit3 := exitFrameWithProtectors threeArmCleanExitTree [1]
     rRel3.status = .Released ∧
     rRel3.tree.protectedTags = [1] ∧
     rExit3.status = .Released ∧
     rExit3.tree.protectedTags = [] ∧
     rExit3.tree.segments =
       [⟨0, 8, [(0, ⟨.Cell, true⟩), (1, ⟨.Cell, true⟩), (2, ⟨.Unique, true⟩)]⟩,
        ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Disabled, true⟩)]⟩,
        ⟨16, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Frozen, true⟩),
                 (2, ⟨.Frozen, true⟩)]⟩]) ∧
    (let miriOrder := exitFrameWithProtectors coframeAliasingOrderTree [2, 1]
     let prematurePop := endCallRemoveProtectors coframeAliasingOrderTree [2, 1]
     let buggyOrder := releaseProtectorKeepProtected prematurePop 2
     miriOrder.status = .AccessFailure 0 8 1 (.ProtectedDisabled .Unique) ∧
     buggyOrder.status = .Released) :=
  ⟨rfl, rfl, rfl, rfl,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl⟩⟩

/-- Canonical shared 3-node `topo3` tree with `protectedTags = [1, 2]`, `src`
`(Frozen, true)` on `[0..8)`, and `dst` `(ReservedFrz false, false)` on
`[8..16)`. -/
def sharedTopo3Disjoint16 : RangedBorrowTree :=
  mkSharedTopo3Tree16 .Frozen true (.ReservedFrz false) false [1, 2]

/-- Concrete shared `topo3` commutation + clean protector exit alongside
`accessed = true` and single-cause overlapping-write `.ProtectedDisabled` traps
(`[]` zero axioms). -/
theorem canary_shared_topo3_commutation_and_contrasts :
    (let s1 :=
       performRangedAccess sharedTopo3Disjoint16 0 8 1 .Read
         .VisitChildrenOfAccessed
     let s12 :=
       performRangedAccess s1.tree 8 8 2 .Write .VisitChildrenOfAccessed
     let s2 :=
       performRangedAccess sharedTopo3Disjoint16 8 8 2 .Write
         .VisitChildrenOfAccessed
     let s21 :=
       performRangedAccess s2.tree 0 8 1 .Read .VisitChildrenOfAccessed
     let ex := exitFrameWithProtectors s12.tree [1, 2]
     s12.status = .Completed ∧
     s21.status = .Completed ∧
     s12.tree = s21.tree ∧
     s12.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Frozen, true⟩),
                (2, ⟨.Disabled, false⟩)]⟩,
        ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
                (2, ⟨.Unique, true⟩)]⟩] ∧
     ex.status = .Released ∧
     ex.tree.protectedTags = []) ∧
    (let treeAccTrue : RangedBorrowTree :=
       { topology := topo3
         protectedTags := [1, 2]
         segments :=
           [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Frozen, true⟩),
                    (2, ⟨.Disabled, true⟩)]⟩,
            ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
                    (2, ⟨.ReservedFrz false, false⟩)]⟩] }
     (performRangedAccess treeAccTrue 0 8 1 .Read
        .VisitChildrenOfAccessed).status =
       .TransitionError 0 8 2 (.ProtectedDisabled .Disabled)) ∧
    (let treeOverlapWrite : RangedBorrowTree :=
       { topology := topo3
         protectedTags := [1, 2]
         segments :=
           [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Frozen, true⟩),
                    (2, ⟨.ReservedFrz false, false⟩)]⟩,
            ⟨8, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Disabled, false⟩),
                    (2, ⟨.ReservedFrz false, false⟩)]⟩] }
     (performRangedAccess treeOverlapWrite 0 8 2 .Write
        .VisitChildrenOfAccessed).status =
       .TransitionError 0 8 1 (.ProtectedDisabled .Frozen)) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- Straddling-segment split (`[4..12)` inside `[0..16)`) and 3-node chain
(`0 -> 1 -> 3`) `.SkipChildrenOfAccessed` vs `.VisitChildrenOfAccessed`
witnesses (`[]` zero axioms). -/
theorem canary_straddling_split_and_chain_visit_modes :
    (let singleSeg16 : RangedBorrowTree :=
       { topology := topo3
         protectedTags := []
         segments :=
           [⟨0, 16, [(0, ⟨.Unique, true⟩), (1, ⟨.ReservedFrz false, false⟩),
                     (2, ⟨.Frozen, true⟩)]⟩] }
     let res :=
       performRangedAccess singleSeg16 4 8 1 .Write .VisitChildrenOfAccessed
     res.status = .Completed ∧
     res.tree.segments =
       [⟨0, 4, [(0, ⟨.Unique, true⟩), (1, ⟨.ReservedFrz false, false⟩),
                (2, ⟨.Frozen, true⟩)]⟩,
        ⟨4, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Disabled, true⟩)]⟩,
        ⟨12, 4, [(0, ⟨.Unique, true⟩), (1, ⟨.ReservedFrz false, false⟩),
                 (2, ⟨.Frozen, true⟩)]⟩]) ∧
    (let chainTopo : List TbTopoNode :=
       [⟨0, none⟩, ⟨1, some 0⟩, ⟨3, some 1⟩]
     let chainTree : RangedBorrowTree :=
       { topology := chainTopo
         protectedTags := []
         segments :=
           [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                    (3, ⟨.Frozen, true⟩)]⟩] }
     let skipRes :=
       performRangedAccess chainTree 0 8 1 .Write .SkipChildrenOfAccessed
     let visitRes :=
       performRangedAccess chainTree 0 8 1 .Write .VisitChildrenOfAccessed
     skipRes.status = .Completed ∧
     skipRes.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (3, ⟨.Frozen, true⟩)]⟩] ∧
     visitRes.status = .Completed ∧
     visitRes.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (3, ⟨.Disabled, true⟩)]⟩]) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Single-cause fail-closed `RangedBorrowTree` regression suite (`[]` zero
axioms), covering local-first precedence, `.InvariantFailure` preservation,
contiguous segment tiling (rejecting gaps and overlaps), missing
actor/topology/parent tags, release-path missing-tag and
`.SkipChildrenOfAccessed` grandchild guards, full-chain leaf actor fuel,
`.ProtectedDisabled` write-back, protected `ReservedFrz true` conflict
marking, and zero-length access behavior. -/
theorem canary_rangedBorrowTree_negative_fail_closed_tests :
    let localFirstTree : RangedBorrowTree :=
      { topology := topo3
        protectedTags := [1, 2]
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                   (2, ⟨.Frozen, true⟩)]⟩] }
    let invPresTree : RangedBorrowTree :=
      { topology := [⟨0, none⟩, ⟨1, some 0⟩, ⟨2, some 0⟩, ⟨3, some 0⟩]
        protectedTags := [1, 2, 3]
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                   (2, ⟨.ReservedIM, false⟩), (3, ⟨.Unique, true⟩)]⟩] }
    let partialCovTree : RangedBorrowTree :=
      { topology := topo3
        protectedTags := [1]
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                   (2, ⟨.Disabled, false⟩)]⟩] }
    let missingNodeTree : RangedBorrowTree :=
      { topology := topo3
        protectedTags := [1, 2]
        segments :=
          [⟨0, 8, [(0, ⟨.Unique, true⟩), (2, ⟨.Disabled, false⟩)]⟩] }
    let validStates8 : List (Nat × TbLocationState) :=
      [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩), (2, ⟨.Disabled, false⟩)]
    let dupOverlapTree : RangedBorrowTree :=
      ⟨topo3, [], [⟨0, 4, validStates8⟩, ⟨0, 4, validStates8⟩]⟩
    let partialOverlapTree : RangedBorrowTree :=
      ⟨topo3, [], [⟨0, 6, validStates8⟩, ⟨2, 2, validStates8⟩]⟩
    let danglingParentTree : RangedBorrowTree :=
      ⟨[⟨0, none⟩, ⟨1, some 7⟩, ⟨2, some 0⟩], [],
       [⟨0, 8, [(0, ⟨.Frozen, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Disabled, false⟩)]⟩]⟩
    let danglingChain1 : RangedBorrowTree :=
      ⟨[⟨0, some 7⟩], [0], [⟨0, 8, [(0, ⟨.Unique, true⟩)]⟩]⟩
    let danglingChain2 : RangedBorrowTree :=
      ⟨[⟨0, some 7⟩, ⟨1, some 0⟩], [1],
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩)]⟩]⟩
    let actorInStatesNotTopoTree : RangedBorrowTree :=
      ⟨topo3, [], [⟨0, 8, validStates8 ++ [(99, ⟨.Unique, true⟩)]⟩]⟩
    let foreignStatelessTree : RangedBorrowTree :=
      ⟨topo3, [2], [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩)]⟩]⟩
    let unprotFrameTagTree : RangedBorrowTree :=
      ⟨topo3, [2], [⟨0, 8, validStates8⟩]⟩
    let cellMissingOtherTree : RangedBorrowTree :=
      ⟨topo3, [1], [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Cell, true⟩)]⟩]⟩
    let chainReleaseTree : RangedBorrowTree :=
      ⟨[⟨0, none⟩, ⟨1, some 0⟩, ⟨3, some 1⟩], [1],
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (3, ⟨.Unique, true⟩)]⟩]⟩
    let grandchildReleaseTree : RangedBorrowTree :=
      ⟨[⟨0, none⟩, ⟨1, some 0⟩, ⟨3, some 1⟩, ⟨4, some 3⟩], [1],
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (3, ⟨.Unique, true⟩), (4, ⟨.Unique, true⟩)]⟩]⟩
    let protDisabledTree : RangedBorrowTree :=
      ⟨topo3, [2],
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Unique, true⟩)]⟩]⟩
    let protResFrzTree : RangedBorrowTree :=
      ⟨topo3, [2],
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.ReservedFrz false, true⟩)]⟩]⟩
    (performRangedAccess sharedTopo3Disjoint16 0 8 99 .Read
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess sharedTopo3Disjoint16 100 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess ⟨topo3, [1], []⟩ 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess partialCovTree 0 16 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess missingNodeTree 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess dupOverlapTree 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess partialOverlapTree 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess danglingParentTree 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess danglingChain1 0 8 0 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (releaseProtectorKeepProtected danglingChain1 0).status = .MissingTag 0 ∧
    (performRangedAccess danglingChain2 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (releaseProtectorKeepProtected danglingChain2 1).status = .MissingTag 1 ∧
    (performRangedAccess actorInStatesNotTopoTree 0 8 99 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess actorInStatesNotTopoTree 0 0 99 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (performRangedAccess foreignStatelessTree 0 8 1 .Write
      .VisitChildrenOfAccessed).status = .UncoveredOrMissingTag ∧
    (exitFrameWithProtectors unprotFrameTagTree [1, 2]).status = .MissingTag 1 ∧
    performSegmentAccess topo3 [] ⟨0, 8, validStates8⟩ 99 .Write
      .VisitChildrenOfAccessed = .missingState ⟨0, 8, validStates8⟩ ∧
    (releaseProtectorKeepProtected sharedTopo3Disjoint16 99).status =
      .MissingTag 99 ∧
    (releaseProtectorKeepProtected missingNodeTree 1).status =
      .MissingTag 1 ∧
    (releaseProtectorKeepProtected cellMissingOtherTree 1).status =
      .MissingTag 1 ∧
    (releaseProtectorKeepProtected ⟨topo3, [1], []⟩ 1).status =
      .MissingTag 1 ∧
    performRangedAccess ⟨topo3, [1], []⟩ 0 0 1 .Write
      .VisitChildrenOfAccessed = ⟨⟨topo3, [1], []⟩, .Completed⟩ ∧
    (let rChain := exitFrameWithProtectors chainReleaseTree [1]
     rChain.status = .Released ∧
     rChain.tree.segments = chainReleaseTree.segments) ∧
    (let rLocal :=
       performRangedAccess localFirstTree 0 8 2 .Write .VisitChildrenOfAccessed
     rLocal.status = .TransitionError 0 8 2 (.ChildAccessForbidden .Frozen) ∧
     rLocal.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Frozen, true⟩)]⟩]) ∧
    (let rInv :=
       performRangedAccess invPresTree 0 8 1 .Write .VisitChildrenOfAccessed
     rInv.status = .InvariantFailure 0 8 2 ∧
     rInv.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.ReservedIM, false⟩), (3, ⟨.Unique, true⟩)]⟩]) ∧
    (performRangedAccess sharedTopo3Disjoint16 0 8 1 .Write
      .VisitChildrenOfAccessed).status =
      .TransitionError 0 8 1 (.ChildAccessForbidden .Frozen) ∧
    (TbLocationState.performAccess ⟨.ReservedIM, false⟩ .Read
      .ForeignAccess true) = .InvariantFailure ⟨.ReservedIM, false⟩ ∧
    (performRangedAccess chainReleaseTree 0 8 3 .Write
      .VisitChildrenOfAccessed).status = .Completed ∧
    (let rGrand := exitFrameWithProtectors grandchildReleaseTree [1]
     rGrand.status = .Released ∧
     rGrand.tree.segments = grandchildReleaseTree.segments) ∧
    (let rProtDis :=
       performRangedAccess protDisabledTree 0 8 1 .Write
         .VisitChildrenOfAccessed
     rProtDis.status = .TransitionError 0 8 2 (.ProtectedDisabled .Unique) ∧
     rProtDis.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.Disabled, true⟩)]⟩]) ∧
    (let rResFrz :=
       performRangedAccess protResFrzTree 0 8 1 .Read .VisitChildrenOfAccessed
     rResFrz.status = .Completed ∧
     rResFrz.tree.segments =
       [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨.Unique, true⟩),
                (2, ⟨.ReservedFrz true, true⟩)]⟩]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl,
   rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Anneal.RefFrame
