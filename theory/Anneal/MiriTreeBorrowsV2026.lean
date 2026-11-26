-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Statements
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators

/-!
# Miri Tree Borrows Model, Retag/Protector Pipeline, and V2026 Bridges (`Anneal.MiriTreeBorrowsV2026`)

Converges `google/zerocopy#4185` (`MiriTreeBorrows/{Model,Retag,Canaries}.lean`)
onto `unstable`'s unmodified `Trusted.Rustc.V2026_06_01.MirSemantics` without
`module` / `public import` / `@[expose]` syntax and with zero `Std.Do`,
`MiniRustSpec.*`, `Miri.*`, `LeanMiriSpec.*`, or `Lean` imports:

1. **Part I — Complete 6-Constructor / 7-State Permission, SIFA, Traversal & Ranged Model**:
   - `MiriPerm` (`.cell`, `.reservedFrz Bool`, `.reservedIM`, `.unique`, `.frozen`, `.disabled`),
     `MiriAccessKind`, `MiriRelatedness`, `MiriSifa`, `MiriRefKind`, `MiriVisitMode`,
     `MiriPermOutcome`, `MiriTbError`, `MiriTbResult`, full 56-cell transition table
     (`miriPerformPermAccess`), SIFA pruning (`miriSkipIfKnownNoop`, `miriSkippedForeignNodes`),
     pre-error SIFA commit (`miriPerformLocAccess`), local-before-foreign postorder ranged
     traversal (`miriPerformSegmentAccess`, `miriPerformRangedAccess`), and fail-closed
     multi-root / missing-tag / uncovered-range rejection.
2. **Part II — Reborrow Pipeline & Call-Frame Protector Release over V2026 `Memory`**:
   - Live/dead/read-only allocation inspection directly over unmodified
     `Trusted.Rustc.V2026_06_01.MirSemantics.Memory` (`mem.globals` + `mem.borrows`),
     `miriBeginFrame`, `miriRegisterProtectorOpt`, `miriReborrowTag`, `miriRegisterFnEntryArg`,
     `miriReleaseOneProtector`, `miriReleaseTagListForward`, `miriReleaseTagListReverse`,
     `miriEndCall`, and `miriExitCallFrame`.
3. **Part III — Shared V2026 Interface Predicates & Exact Bijections**:
   - Bijections between `MiriPerm`/`MiriAccessKind`/`MiriRelatedness`/`MiriPermOutcome` and
     `Trusted.Rustc.V2026_06_01.MirSemantics.{TreeBorrowPerm, TreeBorrowAccessKind,
     TreeBorrowRelatedness, TreeBorrowTransition}`, `RetagKind` → initial inside/outside
     permissions (`retagKindToInitialPerms`), and shared disjoint-range/frame/protector predicates.
4. **Part IV — Algebraic Laws & Unmodified `V2026_06_01.MirSemantics` Semantic Bridges**:
   - Permission monotonicity & absorbing-state laws, SIFA stability soundness, two-phase
     `ReservedFrz`/`ReservedIM` activation & conflict laws, disjoint-allocation/segment/tag frame
     preservation, protector release commutation & post-release unlock, plus direct agreement and
     preservation theorems over unmodified `V2026_06_01.MirSemantics.{treeBorrowPermTransition,
     treeBorrowNodeAccess, preventsDeallocation, retagPerm, fnEntryRetagPerm, rangesDisjoint,
     byteRangesOverlapBool, borrowEntryWriteConflicts, disableFrameBorrows,
     hasFrameDeallocProtectorConflict, restoreCallerProtectors, invalidateTreeBorrowsAtProj,
     freezeTreeBorrowsOnReadAtProj, evalFnEntryRetag, evalNonFnEntryRetag}`.
5. **Part V — Concrete Positive & Fail-Closed Negative UB Witnesses**:
   - Non-vacuous positive workflows (two-phase reborrow + activation + shared reborrow + frame
     push/exit, aliased read-only `FnEntry`, SIFA pruning, `Cell`/`ReservedIM` semantics) and
     genuine `.err ...` negative witnesses (write-to-read-only, protected foreign-write UB,
     frozen local write UB, dead/missing allocation rejection, duplicate tag/frame rejection,
     missing frame rejection, two-phase conflict UB with SIFA reset, lazy `.unique`, uncovered
     range, multi-root rejection, and forward-vs-reverse release separation).

Pass-1 hygiene: `0` `sorry`, `0` `noncomputable`, `0` `._unsafe_rec`, `0` `omega`, `0` `bv_decide`,
`0` `by_cases`, `0` `grind`, `0` `native_decide`; axioms strictly `⊆ {propext}`.
-/

namespace Anneal.MiriTreeBorrowsV2026

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

set_option autoImplicit false

/-! ## Part I. Permission, SIFA, Traversal & Ranged Access Model (`#4185`) -/

/-- Fuel-bounded structural `Nat.rec` fold helper (zero `._unsafe_rec`). -/
def natFold {α : Type} (init : α) (step : Nat → α → α) : Nat → α :=
  @Nat.rec (fun _ => α) init (fun n acc => step n acc)

/-- Computable boolean membership check on `List Nat`. -/
def miriNatListMem (x : Nat) (xs : List Nat) : Bool :=
  xs.foldl (fun acc y => acc || Nat.beq x y) false

/-- Miri 6-constructor / 7-state Tree Borrows permission. -/
inductive MiriPerm : Type where
  | cell : MiriPerm
  | reservedFrz (conflicted : Bool) : MiriPerm
  | reservedIM : MiriPerm
  | unique : MiriPerm
  | frozen : MiriPerm
  | disabled : MiriPerm

/-- Miri `AccessKind`. -/
inductive MiriAccessKind : Type where
  | read : MiriAccessKind
  | write : MiriAccessKind

/-- Miri `AccessRelatedness`. -/
inductive MiriRelatedness : Type where
  | localAccess : MiriRelatedness
  | foreignAccess : MiriRelatedness

/-- Miri `IdempotentForeignAccess` (SIFA cache). -/
inductive MiriSifa : Type where
  | none : MiriSifa
  | read : MiriSifa
  | write : MiriSifa

/-- Shared vs. mutable reference kind for `RetagPolicy.selectedPermission`. -/
inductive MiriRefKind : Type where
  | shared : MiriRefKind
  | mutable : MiriRefKind

/-- Miri `ChildrenVisitMode`. -/
inductive MiriVisitMode : Type where
  | visitChildrenOfAccessed : MiriVisitMode
  | skipChildrenOfAccessed : MiriVisitMode

/-- Per-permission transition outcome. -/
inductive MiriPermOutcome : Type where
  | transition (next : MiriPerm) : MiriPermOutcome
  | undefinedBehavior : MiriPermOutcome
  | impossibleProtectedReservedIM : MiriPermOutcome

/-- Tree Borrows transition, reborrow, frame, and coverage errors (`V2026_06_01.MirAst.AllocId`). -/
inductive MiriTbError : Type where
  | childAccessForbidden (tag : Nat) (perm : MiriPerm) : MiriTbError
  | protectedDisabled (tag : Nat) (perm : MiriPerm) : MiriTbError
  | impossibleProtectedReservedIM (tag : Nat) : MiriTbError
  | invalidLazyState (tag : Nat) : MiriTbError
  | nonInitialPerm (tag : Nat) (perm : MiriPerm) : MiriTbError
  | duplicateTag (tag : Nat) : MiriTbError
  | missingFrame (frameId : Nat) : MiriTbError
  | deadOrMissingAlloc (allocId : AllocId) : MiriTbError
  | writeToReadOnly (allocId : AllocId) : MiriTbError
  | missingTag (tag : Nat) : MiriTbError
  | uncoveredRange (allocId : AllocId) : MiriTbError
  | duplicateFrame (frameId : Nat) : MiriTbError
  | multipleRoots (tag : Nat) : MiriTbError

/-- State-retaining Tree Borrows outcome preserving committed updates on error. -/
inductive MiriTbResult (α : Type) : Type where
  | ok (val : α) : MiriTbResult α
  | err (partialState : α) (error : MiriTbError) : MiriTbResult α

/-- Returns `true` iff `p` is `.disabled`. -/
def miriPermIsDisabled : MiriPerm → Bool
  | .disabled => true
  | _ => false

/-- Returns `true` iff `p` is `.frozen`. -/
def miriPermIsFrozen : MiriPerm → Bool
  | .frozen => true
  | _ => false

/-- Returns `true` iff `p` is `.unique`. -/
def miriPermIsUnique : MiriPerm → Bool
  | .unique => true
  | _ => false

/-- Returns `true` iff `p` is `.cell`. -/
def miriPermIsCell : MiriPerm → Bool
  | .cell => true
  | _ => false

/-- Returns `true` iff `p` is a valid initial permission. -/
def miriPermIsInitial : MiriPerm → Bool
  | .cell => true
  | .reservedFrz conflicted => !conflicted
  | .reservedIM => true
  | .unique => true
  | .frozen => true
  | .disabled => false

/-- Returns `true` iff an accessed strongly protected permission `p` prevents deallocation. -/
def miriPermPreventsDealloc : MiriPerm → Bool
  | .cell => false
  | .reservedFrz _ => true
  | .reservedIM => true
  | .unique => true
  | .frozen => true
  | .disabled => false

/-- Reachability partial order on `MiriPerm` (matching `Miri.TreeBorrows.permissionLE`). -/
def miriPermLE : MiriPerm → MiriPerm → Bool
  | .cell, .cell => true
  | .reservedFrz false, .reservedFrz _ => true
  | .reservedFrz true, .reservedFrz true => true
  | .reservedFrz _, .unique => true
  | .reservedFrz _, .frozen => true
  | .reservedFrz _, .disabled => true
  | .reservedIM, .reservedIM => true
  | .reservedIM, .unique => true
  | .reservedIM, .frozen => true
  | .reservedIM, .disabled => true
  | .unique, .unique => true
  | .unique, .frozen => true
  | .unique, .disabled => true
  | .frozen, .frozen => true
  | .frozen, .disabled => true
  | .disabled, .disabled => true
  | _, _ => false

/-- Computable structural Boolean equality on `MiriPerm`. -/
def miriPermEq : MiriPerm → MiriPerm → Bool
  | .cell, .cell => true
  | .reservedFrz c1, .reservedFrz c2 =>
    match c1, c2 with
    | false, false => true
    | true, true => true
    | _, _ => false
  | .reservedIM, .reservedIM => true
  | .unique, .unique => true
  | .frozen, .frozen => true
  | .disabled, .disabled => true
  | _, _ => false

/-- Returns `true` iff `k` is `.read`. -/
def miriKindIsRead : MiriAccessKind → Bool
  | .read => true
  | .write => false

/-- Returns `true` iff `r` is `.foreignAccess`. -/
def miriRelIsForeign : MiriRelatedness → Bool
  | .localAccess => false
  | .foreignAccess => true

/-- Returns `true` iff `m` is `.visitChildrenOfAccessed`. -/
def miriIsVisitChildren : MiriVisitMode → Bool
  | .visitChildrenOfAccessed => true
  | .skipChildrenOfAccessed => false

/-- Exact 3-arm Miri `Permission.associatedAccess`:
`.cell => none`, `.unique => some .write`, all others `=> some .read`. -/
def miriAssociatedAccess : MiriPerm → Option MiriAccessKind
  | .cell => none
  | .unique => some .write
  | .reservedFrz _ => some .read
  | .reservedIM => some .read
  | .frozen => some .read
  | .disabled => some .read

/-- Total order rank on `MiriSifa` (`.none < .read < .write`). -/
def miriSifaRank : MiriSifa → Nat
  | .none => 0
  | .read => 1
  | .write => 2

/-- Maps a foreign `MiriAccessKind` to its `MiriSifa` level. -/
def miriSifaFromForeign : MiriAccessKind → MiriSifa
  | .read => .read
  | .write => .write

/-- Returns `true` iff `happeningNow ≤ recorded`. -/
def miriSifaCanSkipForeign (recorded happeningNow : MiriSifa) : Bool :=
  Nat.ble (miriSifaRank happeningNow) (miriSifaRank recorded)

/-- Updates SIFA after an access. -/
def miriSifaRecordNew (recorded : MiriSifa) (kind : MiriAccessKind)
    (rel : MiriRelatedness) : MiriSifa :=
  match rel with
  | .localAccess => .none
  | .foreignAccess =>
    let h := miriSifaFromForeign kind
    if Nat.ble (miriSifaRank recorded) (miriSifaRank h) then h else recorded

/-- Weakens `recorded` so it is no stronger than `strongestAllowed`. -/
def miriSifaEnsureNoStrongerThan (recorded strongestAllowed : MiriSifa) : MiriSifa :=
  if Nat.blt (miriSifaRank strongestAllowed) (miriSifaRank recorded) then
    strongestAllowed
  else
    recorded

/-- Exact Miri `Permission.strongestIdempotentForeignAccess`, returning `none` for
`ImpossibleProtectedReservedIM`. -/
def miriStrongestSifa (perm : MiriPerm) (isProtected : Bool) : Option MiriSifa :=
  match perm with
  | .cell => some .write
  | .reservedFrz conflicted =>
    match conflicted with
    | false => if isProtected then some .none else some .read
    | true => some .read
  | .reservedIM => if isProtected then none else some .write
  | .unique => some .none
  | .frozen => some .read
  | .disabled => some .write

/-- Miri `childRead`. -/
def miriChildReadPerm : MiriPerm → MiriPermOutcome
  | .cell => .transition .cell
  | .reservedFrz c => .transition (.reservedFrz c)
  | .reservedIM => .transition .reservedIM
  | .unique => .transition .unique
  | .frozen => .transition .frozen
  | .disabled => .undefinedBehavior

/-- Miri `foreignRead`. -/
def miriForeignReadPerm (state : MiriPerm) (isProtected : Bool) : MiriPermOutcome :=
  match state with
  | .cell => .transition .cell
  | .frozen => .transition .frozen
  | .disabled => .transition .disabled
  | .reservedFrz c =>
    if isProtected then .transition (.reservedFrz true)
    else .transition (.reservedFrz c)
  | .reservedIM =>
    if isProtected then .impossibleProtectedReservedIM
    else .transition .reservedIM
  | .unique =>
    if isProtected then .transition .disabled
    else .transition .frozen

/-- Miri `childWrite`. -/
def miriChildWritePerm (state : MiriPerm) (isProtected : Bool) : MiriPermOutcome :=
  match state with
  | .cell => .transition .cell
  | .reservedFrz conflicted =>
    match conflicted with
    | true =>
      if isProtected then .undefinedBehavior
      else .transition .unique
    | false => .transition .unique
  | .reservedIM => .transition .unique
  | .unique => .transition .unique
  | .frozen => .undefinedBehavior
  | .disabled => .undefinedBehavior

/-- Miri `foreignWrite`. -/
def miriForeignWritePerm (state : MiriPerm) (isProtected : Bool) : MiriPermOutcome :=
  match state with
  | .cell => .transition .cell
  | .reservedIM =>
    if isProtected then .impossibleProtectedReservedIM
    else .transition .reservedIM
  | .reservedFrz _ => .transition .disabled
  | .unique => .transition .disabled
  | .frozen => .transition .disabled
  | .disabled => .transition .disabled

/-- Full 56-cell `(MiriPerm × MiriAccessKind × MiriRelatedness × isProtected)` transition table. -/
def miriPerformPermAccess (kind : MiriAccessKind) (rel : MiriRelatedness)
    (old : MiriPerm) (isProtected : Bool) : MiriPermOutcome :=
  match kind with
  | .write =>
    match rel with
    | .foreignAccess => miriForeignWritePerm old isProtected
    | .localAccess => miriChildWritePerm old isProtected
  | .read =>
    match rel with
    | .foreignAccess => miriForeignReadPerm old isProtected
    | .localAccess => miriChildReadPerm old

/-- Per-node state at one allocation byte range. -/
structure MiriLocState : Type where
  perm : MiriPerm
  accessed : Bool
  sifa : MiriSifa

/-- `LocationState.newNonAccessed`: rejects non-initial/non-disabled permissions and lazy `.unique`. -/
def miriNewNonAccessed (tag : Nat) (perm : MiriPerm) (sifa : MiriSifa) :
    Except MiriTbError MiriLocState :=
  if miriPermIsInitial perm || miriPermIsDisabled perm then
    if miriPermIsUnique perm then .error (.invalidLazyState tag)
    else .ok ⟨perm, false, sifa⟩
  else
    .error (.invalidLazyState tag)

/-- `LocationState.newAccessed`. -/
def miriNewAccessed (perm : MiriPerm) (sifa : MiriSifa) : MiriLocState :=
  ⟨perm, true, sifa⟩

/-- Exact `RetagPolicy.selectedPermission` (shared vs. mutable). -/
def miriSelectRetagPerm (kind : MiriRefKind)
    (isInsideRange frozen isProtected implicitWrites : Bool) : MiriPerm :=
  match kind with
  | .shared => if frozen then .frozen else .cell
  | .mutable =>
    if implicitWrites && isInsideRange then .unique
    else if isProtected || frozen then .reservedFrz false
    else .reservedIM

/-- Inside-range initial location state: rejects non-initial permissions and protected `.reservedIM`;
initializes non-`Cell` (`miriAssociatedAccess = some _`) with `accessed = true`, and `Cell`
(`miriAssociatedAccess = none`) with `accessed = false`. -/
def miriInitialInsideLoc (tag : Nat) (perm : MiriPerm) (isProtected : Bool) :
    Except MiriTbError MiriLocState :=
  match miriPermIsInitial perm with
  | false => .error (.nonInitialPerm tag perm)
  | true =>
    match miriStrongestSifa perm isProtected with
    | none => .error (.impossibleProtectedReservedIM tag)
    | some sifa =>
      match miriAssociatedAccess perm with
      | some _ => .ok (miriNewAccessed perm sifa)
      | none => miriNewNonAccessed tag perm sifa

/-- Outside-range initial location state (`accessed = false`): rejects non-initial permissions,
protected `.reservedIM`, and lazy `.unique`. -/
def miriInitialOutsideLoc (tag : Nat) (outsidePerm : MiriPerm) (isProtected : Bool) :
    Except MiriTbError MiriLocState :=
  match miriPermIsInitial outsidePerm with
  | false => .error (.nonInitialPerm tag outsidePerm)
  | true =>
    match miriStrongestSifa outsidePerm isProtected with
    | none => .error (.impossibleProtectedReservedIM tag)
    | some sifa => miriNewNonAccessed tag outsidePerm sifa

/-- `LocationState.skipIfKnownNoop`. -/
def miriSkipIfKnownNoop (st : MiriLocState) (kind : MiriAccessKind)
    (rel : MiriRelatedness) : Bool :=
  if miriRelIsForeign rel then
    miriSifaCanSkipForeign st.sifa (miriSifaFromForeign kind) ||
      miriPermIsDisabled st.perm ||
      (miriPermIsFrozen st.perm && miriKindIsRead kind)
  else
    false

/-- `LocationState.performAccess` preceded by `recordNewAccess`: commits `recordedState` (with
updated `sifa`) even on `.childAccessForbidden`, and checks
`isProtected && nextAccessed && miriPermIsDisabled nextPerm` before committing `nextState` on
`.protectedDisabled`. -/
def miriPerformLocAccess (tag : Nat) (st : MiriLocState)
    (kind : MiriAccessKind) (rel : MiriRelatedness) (isProtected : Bool) :
    MiriTbResult MiriLocState :=
  let recordedSifa := miriSifaRecordNew st.sifa kind rel
  let recordedState : MiriLocState := ⟨st.perm, st.accessed, recordedSifa⟩
  match miriPerformPermAccess kind rel recordedState.perm isProtected with
  | .undefinedBehavior =>
    .err recordedState (.childAccessForbidden tag recordedState.perm)
  | .impossibleProtectedReservedIM =>
    .err recordedState (.impossibleProtectedReservedIM tag)
  | .transition nextPerm =>
    let nextAccessed := recordedState.accessed || !miriRelIsForeign rel
    let nextState : MiriLocState := ⟨nextPerm, nextAccessed, recordedState.sifa⟩
    if isProtected && nextAccessed && miriPermIsDisabled nextPerm then
      .err nextState (.protectedDisabled tag recordedState.perm)
    else
      .ok nextState

/-- Ordered tree topology node. -/
structure MiriTopoNode : Type where
  tag : Nat
  parent : Option Nat
  children : List Nat

/-- Tag-to-location-state entry inside a byte segment. -/
structure MiriTagEntry : Type where
  tag : Nat
  loc : MiriLocState

/-- Uniform byte-range segment `[offset, offset + size)` across all tags. -/
structure MiriSegment : Type where
  offset : Nat
  size : Nat
  entries : List MiriTagEntry

/-- Scheduled traversal event `(tag, relatedness)`. -/
structure MiriTraversalEvent : Type where
  tag : Nat
  rel : MiriRelatedness

/-- Call-frame protector registration list in forward registration order. -/
structure MiriFrameProtectors : Type where
  frameId : Nat
  protectedTags : List (AllocId × Nat)

/-- Per-allocation borrow tree (`tree` topology + disjoint positive-size `segments`). -/
structure MiriAllocTree : Type where
  allocId : AllocId
  tree : List MiriTopoNode
  segments : List MiriSegment

/-- Whole-machine Tree Borrows state (`frames` + per-allocation trees). -/
structure MiriTbState : Type where
  frames : List MiriFrameProtectors
  allocTrees : List MiriAllocTree

/-- Looks up a topology node by `tag`. -/
def miriFindTopoNode? (tag : Nat) (tree : List MiriTopoNode) : Option MiriTopoNode :=
  tree.foldl (fun acc n => if Nat.beq n.tag tag then some n else acc) none

/-- Returns the ordered child tags of `tag` in `tree`. -/
def miriChildrenOfTag (tag : Nat) (tree : List MiriTopoNode) : List Nat :=
  match miriFindTopoNode? tag tree with
  | none => []
  | some n => n.children

/-- Appends `newTag` as a child of `parentTag` in `tree`. -/
def miriInsertChildTopo (tree : List MiriTopoNode) (parentTag newTag : Nat) :
    List MiriTopoNode :=
  let updated :=
    tree.map (fun n =>
      if Nat.beq n.tag parentTag then
        { tag := n.tag, parent := n.parent, children := n.children ++ [newTag] }
      else
        n)
  updated ++ [{ tag := newTag, parent := some parentTag, children := [] }]

/-- `TraversalTree.ancestorPath`: `[startTag, parent, ..., root]`. -/
def miriAncestorPath (tree : List MiriTopoNode) (startTag : Nat) : List Nat :=
  let pair :=
    natFold ([], some startTag)
      (fun _ acc =>
        match acc.2 with
        | none => acc
        | some cur =>
          match miriFindTopoNode? cur tree with
          | none => (cur :: acc.1, none)
          | some n => (cur :: acc.1, n.parent))
      tree.length
  let fullRev :=
    match pair.2 with
    | none => pair.1
    | some rem => rem :: pair.1
  fullRev.reverse

/-- Filters out an optional tag `skip?` from `xs`, preserving list order. -/
def filterOutOpt (skip? : Option Nat) (xs : List Nat) : List Nat :=
  xs.foldl
    (fun acc x =>
      match skip? with
      | none => acc ++ [x]
      | some s => if Nat.beq x s then acc else acc ++ [x])
    []

/-- `TraversalTree.initialForeignRoots`. -/
def miriInitialForeignRoots (tree : List MiriTopoNode) (path : List Nat)
    (mode : MiriVisitMode) : List Nat :=
  let triple :=
    path.foldl
      (fun (st : List Nat × Option Nat × Bool) current =>
        let accRoots := st.1
        let prevOpt := st.2.1
        let isStart := st.2.2
        let shouldVisitChildren := (!isStart) || miriIsVisitChildren mode
        let siblings :=
          if shouldVisitChildren then
            filterOutOpt prevOpt (miriChildrenOfTag current tree).reverse
          else
            []
        (accRoots ++ siblings, some current, false))
      ([], none, true)
  triple.1

/-- `NormalTreeState.skippedForeignNodes`. -/
def miriSkippedForeignNodes (seg : MiriSegment) (kind : MiriAccessKind) : List Nat :=
  seg.entries.foldl
    (fun acc e =>
      if miriSkipIfKnownNoop e.loc kind .foreignAccess then
        acc ++ [e.tag]
      else
        acc)
    []

/-- `TraversalTree.foreignPostorder`: bottom-up foreign subtree schedule pruning any node in
`skipNodes` and all its descendants. -/
def miriForeignPostorder (tree : List MiriTopoNode) (skipNodes : List Nat)
    (rootTag : Nat) : List MiriTraversalEvent :=
  let stepFn :=
    natFold (fun (_ : Nat) => ([] : List MiriTraversalEvent))
      (fun _ recFn idx =>
        if miriNatListMem idx skipNodes then
          []
        else
          let chRev := (miriChildrenOfTag idx tree).reverse
          let chEvents := chRev.foldl (fun acc c => acc ++ recFn c) []
          chEvents ++ [{ tag := idx, rel := .foreignAccess }])
      tree.length
  stepFn rootTag

/-- `TraversalTree.traverse`: `localEvents ++ foreignEvents`. -/
def miriTraverseSegmentEvents (tree : List MiriTopoNode) (seg : MiriSegment)
    (startTag : Nat) (kind : MiriAccessKind) (mode : MiriVisitMode) :
    List MiriTraversalEvent :=
  let path := miriAncestorPath tree startTag
  let localEvents := path.map (fun idx => { tag := idx, rel := .localAccess })
  let skipped := miriSkippedForeignNodes seg kind
  let fRoots := miriInitialForeignRoots tree path mode
  let foreignEvents :=
    fRoots.foldl (fun acc r => acc ++ miriForeignPostorder tree skipped r) []
  localEvents ++ foreignEvents

/-- Looks up a tag entry in a segment. -/
def miriFindTagEntry? (tag : Nat) (entries : List MiriTagEntry) : Option MiriTagEntry :=
  entries.foldl (fun acc e => if Nat.beq e.tag tag then some e else acc) none

/-- Updates or appends `entry` in `entries`. -/
def miriUpsertTagEntry (entry : MiriTagEntry) (entries : List MiriTagEntry) :
    List MiriTagEntry :=
  let res :=
    entries.foldl
      (fun (acc : Bool × List MiriTagEntry) e =>
        if Nat.beq e.tag entry.tag then
          (true, acc.2 ++ [entry])
        else
          (acc.1, acc.2 ++ [e]))
      (false, [])
  if res.1 then res.2 else res.2 ++ [entry]

/-- Collects all protected tags registered on `allocId` across active `frames`. -/
def miriProtectedTagsOnAlloc (allocId : AllocId)
    (frames : List MiriFrameProtectors) : List Nat :=
  frames.foldl
    (fun acc f =>
      f.protectedTags.foldl
        (fun acc2 p => if Nat.beq p.1 allocId then acc2 ++ [p.2] else acc2)
        acc)
    []

/-- `NormalTreeState.processEvents`: steps events in forward order, halting on the first error
while retaining committed mutations, and failing closed with `.missingTag` if any visited tag is
absent from `seg`. -/
def miriProcessSegmentEvents (protectedOnAlloc : List Nat)
    (kind : MiriAccessKind) (seg : MiriSegment)
    (events : List MiriTraversalEvent) : MiriTbResult MiriSegment :=
  events.foldl
    (fun acc ev =>
      match acc with
      | .err partialSeg err => .err partialSeg err
      | .ok curSeg =>
        match miriFindTagEntry? ev.tag curSeg.entries with
        | none => .err curSeg (.missingTag ev.tag)
        | some e =>
          let isProt := miriNatListMem ev.tag protectedOnAlloc
          match miriPerformLocAccess ev.tag e.loc kind ev.rel isProt with
          | .ok nextLoc =>
            .ok { offset := curSeg.offset
                  size := curSeg.size
                  entries :=
                    miriUpsertTagEntry { tag := ev.tag, loc := nextLoc } curSeg.entries }
          | .err nextLoc err =>
            let updatedSeg : MiriSegment :=
              { offset := curSeg.offset
                size := curSeg.size
                entries :=
                  miriUpsertTagEntry { tag := ev.tag, loc := nextLoc } curSeg.entries }
            .err updatedSeg err)
    (.ok seg)

/-- Returns `true` iff `tree` has two or more roots (`parent = none`). -/
def miriTreeHasMultipleRoots (tree : List MiriTopoNode) : Bool :=
  let rootCount :=
    tree.foldl
      (fun acc n =>
        match n.parent with
        | none => acc + 1
        | some _ => acc)
      0
  Nat.blt 1 rootCount

/-- Performs a single-segment Tree Borrows access: validates `accessedTag`, steps `accessedTag`
locally first (short-circuiting before any ancestor or foreign event), steps remaining `localEvents`
and pruned `foreignEvents`, and fails closed with `.multipleRoots` on multi-root trees. -/
def miriPerformSegmentAccess (tree : List MiriTopoNode)
    (protectedOnAlloc : List Nat) (accessedTag : Nat) (kind : MiriAccessKind)
    (mode : MiriVisitMode) (seg : MiriSegment) : MiriTbResult MiriSegment :=
  match miriFindTopoNode? accessedTag tree with
  | none => .err seg (.missingTag accessedTag)
  | some _ =>
    match miriFindTagEntry? accessedTag seg.entries with
    | none => .err seg (.missingTag accessedTag)
    | some selfEntry =>
      let isSelfProt := miriNatListMem accessedTag protectedOnAlloc
      match miriPerformLocAccess accessedTag selfEntry.loc kind .localAccess isSelfProt with
      | .err nextSelfLoc err =>
        .err
          { offset := seg.offset
            size := seg.size
            entries := miriUpsertTagEntry { tag := accessedTag, loc := nextSelfLoc } seg.entries }
          err
      | .ok nextSelfLoc =>
        let segAfterSelf : MiriSegment :=
          { offset := seg.offset
            size := seg.size
            entries := miriUpsertTagEntry { tag := accessedTag, loc := nextSelfLoc } seg.entries }
        let allEvents := miriTraverseSegmentEvents tree seg accessedTag kind mode
        let tailEvents := allEvents.drop 1
        match miriProcessSegmentEvents protectedOnAlloc kind segAfterSelf tailEvents with
        | .err partialSeg err => .err partialSeg err
        | .ok segNormal =>
          if miriTreeHasMultipleRoots tree then
            .err segNormal (.multipleRoots accessedTag)
          else
            .ok segNormal

/-- Splits a single segment along `[cutStart, cutEnd)`. -/
def miriSplitOneSegment (cutStart cutEnd : Nat) (seg : MiriSegment) : List MiriSegment :=
  let a := seg.offset
  let b := seg.offset + seg.size
  if Nat.ble cutEnd cutStart || Nat.ble b cutStart || Nat.ble cutEnd a then
    [seg]
  else
    let midStart := if Nat.ble a cutStart then cutStart else a
    let midEnd := if Nat.ble cutEnd b then cutEnd else b
    let pref :=
      if Nat.blt a midStart then
        [{ offset := a, size := midStart - a, entries := seg.entries }]
      else []
    let mid :=
      if Nat.blt midStart midEnd then
        [{ offset := midStart, size := midEnd - midStart, entries := seg.entries }]
      else []
    let suff :=
      if Nat.blt midEnd b then
        [{ offset := midEnd, size := b - midEnd, entries := seg.entries }]
      else []
    pref ++ mid ++ suff

/-- Forward byte-range segment splitter preserving segment order. -/
def miriSplitSegmentsAt (off size : Nat) (segs : List MiriSegment) : List MiriSegment :=
  segs.foldl (fun acc seg => acc ++ miriSplitOneSegment off (off + size) seg) []

/-- Returns `true` iff `seg` overlaps `[off, off + size)` (`false` when either interval has zero
byte size). -/
def miriSegmentOverlaps (off size : Nat) (seg : MiriSegment) : Bool :=
  Nat.blt 0 size && Nat.blt 0 seg.size &&
    Nat.blt seg.offset (off + size) && Nat.blt off (seg.offset + seg.size)

/-- Returns `true` iff `[off, off + size)` is contiguously tiled by `segs` after splitting along
`[off, off + size)` (`true` when `size = 0`). -/
def miriRangeIsCovered (off size : Nat) (segs : List MiriSegment) : Bool :=
  let splitSegs := miriSplitSegmentsAt off size segs
  let res :=
    splitSegs.foldl
      (fun (acc : Nat × Bool) seg =>
        if !acc.2 then
          acc
        else if miriSegmentOverlaps off size seg then
          if Nat.beq seg.offset (off + acc.1) then
            (acc.1 + seg.size, true)
          else
            (acc.1, false)
        else
          acc)
      (0, true)
  res.2 && Nat.beq res.1 size

/-- Looks up an allocation's borrow tree by `allocId`. -/
def miriFindAllocTree? (allocId : AllocId) (trees : List MiriAllocTree) :
    Option MiriAllocTree :=
  trees.foldl (fun acc t => if Nat.beq t.allocId allocId then some t else acc) none

/-- Replaces an allocation's borrow tree in `trees`. -/
def miriReplaceAllocTree (t' : MiriAllocTree) (trees : List MiriAllocTree) :
    List MiriAllocTree :=
  trees.map (fun t => if Nat.beq t.allocId t'.allocId then t' else t)

/-- Forward ranged Tree Borrows access over `[off, off + size)`: fails closed on missing
allocation tree, missing `accessedTag`, or uncovered range gaps (`coveredLen ≠ size`), retaining
committed prefix mutations on error. -/
def miriPerformRangedAccess (st : MiriTbState) (allocId : AllocId)
    (accessedTag : Nat) (off size : Nat) (kind : MiriAccessKind)
    (mode : MiriVisitMode) : MiriTbResult MiriTbState :=
  match miriFindAllocTree? allocId st.allocTrees with
  | none => .err st (.uncoveredRange allocId)
  | some atree =>
    match miriFindTopoNode? accessedTag atree.tree with
    | none => .err st (.missingTag accessedTag)
    | some _ =>
      let prot := miriProtectedTagsOnAlloc allocId st.frames
      let splitSegs := miriSplitSegmentsAt off size atree.segments
      let foldRes :=
        splitSegs.foldl
          (fun (acc : List MiriSegment × Nat × Option MiriTbError) seg =>
            match acc.2.2 with
            | some err => (acc.1 ++ [seg], acc.2.1, some err)
            | none =>
              if miriSegmentOverlaps off size seg then
                match Nat.beq seg.offset (off + acc.2.1) with
                | false =>
                  (acc.1 ++ [seg], acc.2.1, some (.uncoveredRange allocId))
                | true =>
                  match miriPerformSegmentAccess atree.tree prot accessedTag kind mode seg with
                  | .ok seg' => (acc.1 ++ [seg'], acc.2.1 + seg.size, none)
                  | .err partialSeg err => (acc.1 ++ [partialSeg], acc.2.1, some err)
              else
                (acc.1 ++ [seg], acc.2.1, none))
          ([], 0, none)
      let st' : MiriTbState :=
        { frames := st.frames
          allocTrees :=
            miriReplaceAllocTree
              { allocId := allocId, tree := atree.tree, segments := foldRes.1 }
              st.allocTrees }
      match foldRes.2.2 with
      | some err => .err st' err
      | none =>
        if Nat.beq foldRes.2.1 size then
          .ok st'
        else
          .err st' (.uncoveredRange allocId)

/-! ## Part II. Reborrow Pipeline & Protector Release over `V2026_06_01.MirSemantics.Memory` -/

/-- Allocation liveness & mutability classification inspected directly from unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.Memory`. -/
inductive MiriV2026AllocInfo : Type where
  | missing : MiriV2026AllocInfo
  | dead : MiriV2026AllocInfo
  | live (mutability : Mutability) : MiriV2026AllocInfo

/-- Inspects `allocId` against unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.Memory`, using
EXACTLY V2026's own pointer-resolution precedence (`ptrAllocByteBound?`, place reads/writes,
unsizing coercions): `mem.borrows` is consulted FIRST (`lookupBorrow`) and `mem.globals`
(`lookupGlobalAlloc`) is only a fallback. V2026 numbers stack-borrow tags (`Memory.nextTag`) and
captured global allocation identifiers from the same origin (`1`), so a stack borrow entry
SHADOWS a same-numbered global (see the `disableLocalBorrows` documentation in
`MirSemantics/Statements.lean`):
- Stack-borrow allocations tracked in `mem.borrows` are `.dead` when `allocDead = true` (set by
  `StorageDead`, a repeated `StorageLive`, and the owning frame's `return_`) and `.live .mut`
  otherwise — regardless of any same-numbered global.
- Otherwise, global allocations in `mem.globals` are `.live ga.mutability` (V2026 never
  deallocates captured globals).
- Absent allocations are `.missing`. -/
def miriInspectAllocV2026 (allocId : AllocId) (mem : Memory) : MiriV2026AllocInfo :=
  match lookupBorrow mem.borrows allocId with
  | .some be =>
    match be.allocDead with
    | true => .dead
    | false => .live .mut
  | .none =>
    match lookupGlobalAlloc mem.globals allocId with
    | .some ga => .live ga.mutability
    | .none => .missing

/-- Returns `true` iff `allocId` is live in unmodified `V2026_06_01` `Memory`. -/
def miriIsAllocLive (allocId : AllocId) (mem : Memory) : Bool :=
  match miriInspectAllocV2026 allocId mem with
  | .live _ => true
  | .dead => false
  | .missing => false

/-- Returns `true` iff `allocId` is a live read-only (`.not`) allocation in `V2026_06_01` `Memory`. -/
def miriIsAllocReadOnly (allocId : AllocId) (mem : Memory) : Bool :=
  match miriInspectAllocV2026 allocId mem with
  | .live .not => true
  | _ => false

/-- Weakens ancestor SIFA caches along `ancPath` across `seg` to be no stronger than
`strongestAllowed`. -/
def miriWeakenSegmentAncestors (ancPath : List Nat) (strongestAllowed : MiriSifa)
    (seg : MiriSegment) : MiriSegment :=
  let entries' :=
    seg.entries.map (fun e =>
      if miriNatListMem e.tag ancPath then
        { tag := e.tag
          loc := { perm := e.loc.perm
                   accessed := e.loc.accessed
                   sifa := miriSifaEnsureNoStrongerThan e.loc.sifa strongestAllowed } }
      else
        e)
  { offset := seg.offset, size := seg.size, entries := entries' }

/-- Looks up a protector frame record by `frameId`. -/
def miriFindFrame? (frameId : Nat) (frames : List MiriFrameProtectors) :
    Option MiriFrameProtectors :=
  frames.foldl (fun acc f => if Nat.beq f.frameId frameId then some f else acc) none

/-- Validates an optional protector `frameId` against `frames`. -/
def miriCheckFrameOpt (frameIdOpt : Option Nat) (frames : List MiriFrameProtectors) :
    Except MiriTbError Unit :=
  match frameIdOpt with
  | none => .ok ()
  | some fid =>
    match miriFindFrame? fid frames with
    | none => .error (.missingFrame fid)
    | some _ => .ok ()

/-- Pushes a new empty protector frame onto `st.frames`, failing closed with `.duplicateFrame`
when `frameId` is already registered. -/
def miriBeginFrame (st : MiriTbState) (frameId : Nat) : MiriTbResult MiriTbState :=
  match miriFindFrame? frameId st.frames with
  | some _ => .err st (.duplicateFrame frameId)
  | none =>
    .ok { frames := { frameId := frameId, protectedTags := [] } :: st.frames
          allocTrees := st.allocTrees }

/-- Appends `(allocId, newTag)` to the protected tags of frame `fid` when `frameIdOpt = some fid`. -/
def miriRegisterProtectorOpt (st : MiriTbState) (frameIdOpt : Option Nat)
    (allocId : AllocId) (newTag : Nat) : MiriTbState :=
  match frameIdOpt with
  | none => st
  | some fid =>
    { frames :=
        st.frames.map (fun f =>
          if Nat.beq f.frameId fid then
            { frameId := f.frameId
              protectedTags := f.protectedTags ++ [(allocId, newTag)] }
          else
            f)
      allocTrees := st.allocTrees }

/-- Registers a child borrow tag against unmodified `V2026_06_01.MirSemantics.Memory`, mirroring
`RetagPipeline.runReborrow`, `RetagPipeline.accessTreeForReborrow`, and `BorrowTree.newChild`:
1. Validates `miriInitialInsideLoc` and `miriInitialOutsideLoc`.
2. Checks `frameIdOpt` and registers the protector BEFORE allocation lookup or parent access
   (so every later failure retains the registered protector).
3. Inspects `miriInspectAllocV2026 allocId mem` (rejecting `.dead` / `.missing` with
   `.deadOrMissingAlloc`, even when `size = 0`), checks allocation tree, fresh `newTag`, and
   existing `parentTag`.
4. For `size > 0`: checks range coverage for `.cell` (`associatedAccess = none`), rejects `.write`
   on read-only (`.not`) allocations with `.writeToReadOnly`, and executes parent
   `miriPerformRangedAccess` with `.visitChildrenOfAccessed`.
5. Globally weakens ancestor SIFA (`outsideLoc.sifa` when `size = 0`,
   `min(insideLoc.sifa, outsideLoc.sifa)` when `size > 0`) and inserts `newTag`. -/
def miriReborrowTag (mem : Memory) (st : MiriTbState)
    (frameIdOpt : Option Nat) (allocId : AllocId) (newTag parentTag : Nat)
    (insidePerm outsidePerm : MiriPerm) (off size : Nat) :
    MiriTbResult MiriTbState :=
  let isProtected :=
    match frameIdOpt with
    | some _ => true
    | none => false
  match miriInitialInsideLoc newTag insidePerm isProtected with
  | .error err => .err st err
  | .ok insideLoc =>
    match miriInitialOutsideLoc newTag outsidePerm isProtected with
    | .error err => .err st err
    | .ok outsideLoc =>
      match miriCheckFrameOpt frameIdOpt st.frames with
      | .error err => .err st err
      | .ok () =>
        let stReg := miriRegisterProtectorOpt st frameIdOpt allocId newTag
        match miriInspectAllocV2026 allocId mem with
        | .missing => .err stReg (.deadOrMissingAlloc allocId)
        | .dead => .err stReg (.deadOrMissingAlloc allocId)
        | .live mutability =>
          match miriFindAllocTree? allocId st.allocTrees with
          | none => .err stReg (.uncoveredRange allocId)
          | some atree0 =>
            match miriFindTopoNode? newTag atree0.tree with
            | some _ => .err stReg (.duplicateTag newTag)
            | none =>
              match miriFindTopoNode? parentTag atree0.tree with
              | none => .err stReg (.missingTag parentTag)
              | some _ =>
                let isReadOnly : Bool :=
                  match mutability with
                  | .not => true
                  | .mut => false
                let parentStep : MiriTbResult MiriTbState :=
                  match Nat.beq size 0 with
                  | true => .ok stReg
                  | false =>
                    match miriAssociatedAccess insidePerm with
                    | none =>
                      if miriRangeIsCovered off size atree0.segments then
                        .ok stReg
                      else
                        .err stReg (.uncoveredRange allocId)
                    | some pKind =>
                      match !miriKindIsRead pKind && isReadOnly with
                      | true => .err stReg (.writeToReadOnly allocId)
                      | false =>
                        miriPerformRangedAccess stReg allocId parentTag off size pKind
                          .visitChildrenOfAccessed
                match parentStep with
                | .err partialSt err => .err partialSt err
                | .ok stAfterParent =>
                  match miriFindAllocTree? allocId stAfterParent.allocTrees with
                  | none => .err stAfterParent (.uncoveredRange allocId)
                  | some atree =>
                    let ancPath := miriAncestorPath atree.tree parentTag
                    let tree' := miriInsertChildTopo atree.tree parentTag newTag
                    let splitSegs := miriSplitSegmentsAt off size atree.segments
                    let minSifa :=
                      if Nat.beq size 0 then
                        outsideLoc.sifa
                      else
                        miriSifaEnsureNoStrongerThan insideLoc.sifa outsideLoc.sifa
                    let segs' :=
                      splitSegs.map (fun seg =>
                        let wSeg := miriWeakenSegmentAncestors ancPath minSifa seg
                        let childLoc :=
                          if miriSegmentOverlaps off size seg then insideLoc else outsideLoc
                        { offset := wSeg.offset
                          size := wSeg.size
                          entries := wSeg.entries ++ [{ tag := newTag, loc := childLoc }] })
                    .ok { frames := stAfterParent.frames
                          allocTrees :=
                            miriReplaceAllocTree
                              { allocId := allocId, tree := tree', segments := segs' }
                              stAfterParent.allocTrees }

/-- `RetagMode.FnEntry` reborrow wrapper using `miriSelectRetagPerm` (uniform freeze over
`[off, off + size)`). -/
def miriRegisterFnEntryArg (mem : Memory) (st : MiriTbState)
    (frameId : Nat) (allocId : AllocId) (newTag parentTag : Nat)
    (refKind : MiriRefKind) (frozen implicitWrites : Bool)
    (off size : Nat) : MiriTbResult MiriTbState :=
  let inPerm := miriSelectRetagPerm refKind true frozen true implicitWrites
  let outPerm := miriSelectRetagPerm refKind false frozen true implicitWrites
  miriReborrowTag mem st (some frameId) allocId newTag parentTag inPerm outPerm off size

/-- Fail-closed `BorrowTree.releaseProtector`: iterates forward across segments, skips unaccessed
or `.cell` segments, and emits `miriAssociatedAccess e.loc.perm` through `tag` with
`.skipChildrenOfAccessed` while all `st.frames` protectors remain active. -/
def miriReleaseOneProtector (st : MiriTbState) (allocId : AllocId) (tag : Nat) :
    MiriTbResult MiriTbState :=
  match miriFindAllocTree? allocId st.allocTrees with
  | none => .err st (.uncoveredRange allocId)
  | some atree =>
    match miriFindTopoNode? tag atree.tree with
    | none => .err st (.missingTag tag)
    | some _ =>
      let prot := miriProtectedTagsOnAlloc allocId st.frames
      let foldRes :=
        atree.segments.foldl
          (fun (acc : List MiriSegment × Option MiriTbError) seg =>
            match acc.2 with
            | some err => (acc.1 ++ [seg], some err)
            | none =>
              match miriFindTagEntry? tag seg.entries with
              | none => (acc.1 ++ [seg], some (.missingTag tag))
              | some e =>
                match miriAssociatedAccess e.loc.perm with
                | none => (acc.1 ++ [seg], none)
                | some rKind =>
                  if e.loc.accessed then
                    match miriPerformSegmentAccess atree.tree prot tag rKind
                        .skipChildrenOfAccessed seg with
                    | .ok seg' => (acc.1 ++ [seg'], none)
                    | .err partialSeg err => (acc.1 ++ [partialSeg], some err)
                  else
                    (acc.1 ++ [seg], none))
          ([], none)
      let st' : MiriTbState :=
        { frames := st.frames
          allocTrees :=
            miriReplaceAllocTree
              { allocId := allocId, tree := atree.tree, segments := foldRes.1 }
              st.allocTrees }
      match foldRes.2 with
      | none => .ok st'
      | some err => .err st' err

/-- Forward protector release loop over `V2026_06_01.MirSemantics.Memory`: fails closed on
`.missing` allocations (`.deadOrMissingAlloc`), skips `.dead` allocations, and releases live
allocations in forward registration order while preserving partial mutations on error. -/
def miriReleaseTagListForward (mem : Memory) (st : MiriTbState)
    (tags : List (AllocId × Nat)) : MiriTbResult MiriTbState :=
  tags.foldl
    (fun acc pair =>
      match acc with
      | .err partialSt err => .err partialSt err
      | .ok curSt =>
        match miriInspectAllocV2026 pair.1 mem with
        | .missing => .err curSt (.deadOrMissingAlloc pair.1)
        | .dead => .ok curSt
        | .live _ => miriReleaseOneProtector curSt pair.1 pair.2)
    (.ok st)

/-- Reversed-order release comparator (`tags.reverse`). -/
def miriReleaseTagListReverse (mem : Memory) (st : MiriTbState)
    (tags : List (AllocId × Nat)) : MiriTbResult MiriTbState :=
  miriReleaseTagListForward mem st tags.reverse

/-- `GlobalState.endCall`: removes `frameId` from `st.frames`. -/
def miriEndCall (st : MiriTbState) (frameId : Nat) : MiriTbState :=
  let frames' :=
    st.frames.foldl
      (fun acc f => if Nat.beq f.frameId frameId then acc else acc ++ [f])
      []
  { frames := frames', allocTrees := st.allocTrees }

/-- Fail-closed `beforeStackPopWithEnsure` + `endCall`: rejects unknown `frameId`, releases all
`frame.protectedTags` in forward order while all protectors stay registered, and invokes
`miriEndCall` only after every release succeeds. -/
def miriExitCallFrame (mem : Memory) (st : MiriTbState) (frameId : Nat) :
    MiriTbResult MiriTbState :=
  match miriFindFrame? frameId st.frames with
  | none => .err st (.missingFrame frameId)
  | some frame =>
    match miriReleaseTagListForward mem st frame.protectedTags with
    | .err partialSt err => .err partialSt err
    | .ok releasedSt => .ok (miriEndCall releasedSt frameId)

/-! ## Part III. Shared V2026 Interface Predicates & Exact Bijections -/

/-- Exact bijection: `MiriPerm → Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm`. -/
def miriPermToV2026 : MiriPerm → TreeBorrowPerm
  | .cell => .cell
  | .reservedFrz c => .reservedFrz c
  | .reservedIM => .reservedIM
  | .unique => .unique
  | .frozen => .frozen
  | .disabled => .disabled

/-- Exact inverse bijection: `Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm → MiriPerm`. -/
def v2026PermToMiri : TreeBorrowPerm → MiriPerm
  | .cell => .cell
  | .reservedFrz c => .reservedFrz c
  | .reservedIM => .reservedIM
  | .unique => .unique
  | .frozen => .frozen
  | .disabled => .disabled

theorem v2026PermToMiri_miriPermToV2026 (p : MiriPerm) :
    v2026PermToMiri (miriPermToV2026 p) = p := by
  cases p <;> rfl

theorem miriPermToV2026_v2026PermToMiri (p : TreeBorrowPerm) :
    miriPermToV2026 (v2026PermToMiri p) = p := by
  cases p <;> rfl

/-- Exact bijection: `MiriAccessKind → TreeBorrowAccessKind`. -/
def miriAccessKindToV2026 : MiriAccessKind → TreeBorrowAccessKind
  | .read => .read
  | .write => .write

/-- Exact inverse: `TreeBorrowAccessKind → MiriAccessKind`. -/
def v2026AccessKindToMiri : TreeBorrowAccessKind → MiriAccessKind
  | .read => .read
  | .write => .write

theorem v2026AccessKindToMiri_miriAccessKindToV2026 (k : MiriAccessKind) :
    v2026AccessKindToMiri (miriAccessKindToV2026 k) = k := by
  cases k <;> rfl

theorem miriAccessKindToV2026_v2026AccessKindToMiri (k : TreeBorrowAccessKind) :
    miriAccessKindToV2026 (v2026AccessKindToMiri k) = k := by
  cases k <;> rfl

/-- Exact bijection: `MiriRelatedness → TreeBorrowRelatedness`. -/
def miriRelToV2026 : MiriRelatedness → TreeBorrowRelatedness
  | .localAccess => .localAccess
  | .foreignAccess => .foreignAccess

/-- Exact inverse: `TreeBorrowRelatedness → MiriRelatedness`. -/
def v2026RelToMiri : TreeBorrowRelatedness → MiriRelatedness
  | .localAccess => .localAccess
  | .foreignAccess => .foreignAccess

theorem v2026RelToMiri_miriRelToV2026 (r : MiriRelatedness) :
    v2026RelToMiri (miriRelToV2026 r) = r := by
  cases r <;> rfl

theorem miriRelToV2026_v2026RelToMiri (r : TreeBorrowRelatedness) :
    miriRelToV2026 (v2026RelToMiri r) = r := by
  cases r <;> rfl

/-- Exact bijection: `MiriPermOutcome → TreeBorrowTransition`. -/
def miriOutcomeToV2026 : MiriPermOutcome → TreeBorrowTransition
  | .transition next => .transition (miriPermToV2026 next)
  | .undefinedBehavior => .ub
  | .impossibleProtectedReservedIM => .protectedReservedIM

/-- Exact inverse: `TreeBorrowTransition → MiriPermOutcome`. -/
def v2026OutcomeToMiri : TreeBorrowTransition → MiriPermOutcome
  | .transition next => .transition (v2026PermToMiri next)
  | .ub => .undefinedBehavior
  | .protectedReservedIM => .impossibleProtectedReservedIM

theorem v2026OutcomeToMiri_miriOutcomeToV2026 (o : MiriPermOutcome) :
    v2026OutcomeToMiri (miriOutcomeToV2026 o) = o := by
  cases o with
  | transition p => cases p <;> rfl
  | undefinedBehavior => rfl
  | impossibleProtectedReservedIM => rfl

theorem miriOutcomeToV2026_v2026OutcomeToMiri (o : TreeBorrowTransition) :
    miriOutcomeToV2026 (v2026OutcomeToMiri o) = o := by
  cases o with
  | transition p => cases p <;> rfl
  | ub => rfl
  | protectedReservedIM => rfl

/-- Exact bijection between V2026 `Mutability` and `MiriRefKind`. -/
def mutabilityToMiriRefKind : Mutability → MiriRefKind
  | .not => .shared
  | .mut => .mutable

def miriRefKindToMutability : MiriRefKind → Mutability
  | .shared => .not
  | .mutable => .mut

theorem miriRefKindToMutability_mutabilityToMiriRefKind (m : Mutability) :
    miriRefKindToMutability (mutabilityToMiriRefKind m) = m := by
  cases m <;> rfl

theorem mutabilityToMiriRefKind_miriRefKindToMutability (k : MiriRefKind) :
    mutabilityToMiriRefKind (miriRefKindToMutability k) = k := by
  cases k <;> rfl

/-- Whether a V2026 `RetagKind` installs a function-entry protector (`true` iff `.fnEntry`). -/
def retagKindIsProtected : RetagKind → Bool
  | .fnEntry => true
  | .twoPhase => false
  | .raw => false
  | .default => false

/-- Maps a V2026 `RetagKind`, `Mutability`, `frozen` bit, and `implicitWrites` flag to the pair
`(insidePerm, outsidePerm)` of initial Tree Borrows permissions. -/
def retagKindToInitialPerms (rk : RetagKind) (mutability : Mutability)
    (frozen : Bool) (implicitWrites : Bool := false) : MiriPerm × MiriPerm :=
  let refKind := mutabilityToMiriRefKind mutability
  let isProt := retagKindIsProtected rk
  (miriSelectRetagPerm refKind true frozen isProt implicitWrites,
   miriSelectRetagPerm refKind false frozen isProt implicitWrites)

/-- Half-open byte-range disjointness predicate shared across Episode 1B and Episode 2. -/
def MiriDisjointRange (off₁ sz₁ off₂ sz₂ : Nat) : Prop :=
  off₁ + sz₁ ≤ off₂ ∨ off₂ + sz₂ ≤ off₁

/-- Computable boolean half-open byte-range disjointness check. -/
def miriRangesDisjointBool (off₁ sz₁ off₂ sz₂ : Nat) : Bool :=
  Nat.ble (off₁ + sz₁) off₂ || Nat.ble (off₂ + sz₂) off₁

/-- Shared allocation-tree framing predicate: `allocId` has the exact same `MiriAllocTree` in
`st₁` and `st₂`. -/
def MiriAllocTreeFrameEq (allocId : AllocId) (st₁ st₂ : MiriTbState) : Prop :=
  miriFindAllocTree? allocId st₁.allocTrees = miriFindAllocTree? allocId st₂.allocTrees

/-- Uniqueness invariant on `MiriTbState.allocTrees`: no two entries share an `allocId`. -/
def MiriAllocIdsNoDup (trees : List MiriAllocTree) : Prop :=
  List.Pairwise (fun a b => a.allocId ≠ b.allocId) trees

/-- Shared segment non-overlap framing predicate. -/
def MiriSegmentUntouched (off sz : Nat) (seg : MiriSegment) : Prop :=
  miriSegmentOverlaps off sz seg = false

/-- Shared protector membership predicate on `(allocId, tag)`. -/
def MiriTagProtectedIn (allocId : AllocId) (tag : Nat) (st : MiriTbState) : Prop :=
  miriNatListMem tag (miriProtectedTagsOnAlloc allocId st.frames) = true

/-- Shared well-formed initial permission invariant (excludes `.disabled`, conflicted `.reservedFrz`,
and protected `.reservedIM`). -/
def MiriWellFormedInitialPerm (p : MiriPerm) (isProtected : Bool) : Prop :=
  miriPermIsInitial p = true ∧ (isProtected = true → p ≠ .reservedIM)

/-! ## Part IV. Algebraic Laws & Real `V2026_06_01.MirSemantics` Semantic Bridges -/

/-! ### IV.1. Permission Monotonicity, Absorbing States & SIFA Soundness -/

theorem miriPermLE_refl (p : MiriPerm) : miriPermLE p p = true := by
  cases p with
  | reservedFrz c => cases c <;> rfl
  | _ => rfl

theorem miriPermLE_trans (p q r : MiriPerm)
    (hpq : miriPermLE p q = true) (hqr : miriPermLE q r = true) :
    miriPermLE p r = true := by
  rcases p with _ | (_ | _) | _ | _ | _ | _ <;>
  rcases q with _ | (_ | _) | _ | _ | _ | _ <;>
  rcases r with _ | (_ | _) | _ | _ | _ | _ <;>
    first
    | rfl
    | exact absurd hpq Bool.false_ne_true
    | exact absurd hqr Bool.false_ne_true

theorem miriPermLE_antisymm (p q : MiriPerm)
    (hpq : miriPermLE p q = true) (hqp : miriPermLE q p = true) : p = q := by
  rcases p with _ | (_ | _) | _ | _ | _ | _ <;>
  rcases q with _ | (_ | _) | _ | _ | _ | _ <;>
    first
    | rfl
    | exact absurd hpq Bool.false_ne_true
    | exact absurd hqp Bool.false_ne_true

/-- Universal `.cell` invariance (`[]`): `.cell` remains `.cell` on every access. -/
theorem miriCell_all_accesses_preserve_cell (kind : MiriAccessKind)
    (rel : MiriRelatedness) (isProtected : Bool) :
    miriPerformPermAccess kind rel .cell isProtected = .transition .cell := by
  cases kind <;> cases rel <;> rfl

/-- `.disabled` is absorbing under every foreign read or foreign write. -/
theorem miriDisabled_foreign_absorbing (kind : MiriAccessKind) (isProtected : Bool) :
    miriPerformPermAccess kind .foreignAccess .disabled isProtected = .transition .disabled := by
  cases kind <;> rfl

/-- `.disabled` rejects every local read or local write as `.undefinedBehavior`. -/
theorem miriDisabled_local_always_ub (kind : MiriAccessKind) (isProtected : Bool) :
    miriPerformPermAccess kind .localAccess .disabled isProtected = .undefinedBehavior := by
  cases kind <;> rfl

/-- No resurrection from `.disabled`: any successful transition from `.disabled` stays `.disabled`. -/
theorem miriDisabled_no_resurrection (kind : MiriAccessKind) (rel : MiriRelatedness)
    (isProtected : Bool) (next : MiriPerm)
    (h : miriPerformPermAccess kind rel .disabled isProtected = .transition next) :
    next = .disabled := by
  cases kind <;> cases rel <;> cases h <;> rfl

/-- Every successful permission transition in the 56-cell table is monotone in `miriPermLE`. -/
theorem miriPerformPermAccess_monotone (kind : MiriAccessKind) (rel : MiriRelatedness)
    (old next : MiriPerm) (isProtected : Bool)
    (h : miriPerformPermAccess kind rel old isProtected = .transition next) :
    miriPermLE old next = true := by
  cases kind <;> cases rel <;> rcases old with _ | (_ | _) | _ | _ | _ | _ <;>
    cases isProtected <;>
    (dsimp only [miriPerformPermAccess, miriChildReadPerm,
      miriForeignReadPerm, miriChildWritePerm, miriForeignWritePerm] at h;
     cases h <;> rfl)

/-- Foreign-read monotonicity corollary. -/
theorem miriForeignRead_monotone (old next : MiriPerm) (isProtected : Bool)
    (h : miriForeignReadPerm old isProtected = .transition next) :
    miriPermLE old next = true :=
  miriPerformPermAccess_monotone .read .foreignAccess old next isProtected h

/-- Foreign-write monotonicity corollary. -/
theorem miriForeignWrite_monotone (old next : MiriPerm) (isProtected : Bool)
    (h : miriForeignWritePerm old isProtected = .transition next) :
    miriPermLE old next = true :=
  miriPerformPermAccess_monotone .write .foreignAccess old next isProtected h

/-- Exact characterization of `.protectedDisabled` UB in `miriPerformLocAccess`:
it occurs iff `isProtected = true`, the transition yields `.disabled`, and the resulting location is
accessed (`st.accessed || !miriRelIsForeign rel = true`). -/
theorem miriPerformLocAccess_protectedDisabled_iff (tag : Nat) (st : MiriLocState)
    (kind : MiriAccessKind) (rel : MiriRelatedness) (isProtected : Bool) :
    (∃ st', miriPerformLocAccess tag st kind rel isProtected =
        .err st' (.protectedDisabled tag st.perm)) ↔
      (isProtected = true ∧
       (st.accessed || !miriRelIsForeign rel) = true ∧
       miriPerformPermAccess kind rel st.perm isProtected = .transition .disabled) := by
  unfold miriPerformLocAccess
  dsimp only
  cases hT : miriPerformPermAccess kind rel st.perm isProtected with
  | undefinedBehavior =>
    constructor
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, _, hEq⟩; cases hEq
  | impossibleProtectedReservedIM =>
    constructor
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, _, hEq⟩; cases hEq
  | transition nextPerm =>
    dsimp only
    cases isProtected with
    | false =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨_, h⟩; cases h
      · rintro ⟨hF, _, _⟩; cases hF
    | true =>
      simp only [Bool.true_and]
      cases hAcc : (st.accessed || !miriRelIsForeign rel) with
      | false =>
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        constructor
        · rintro ⟨_, h⟩; cases h
        · rintro ⟨_, hF, _⟩; cases hF
      | true =>
        simp only [Bool.true_and]
        cases nextPerm with
        | disabled =>
          simp only [miriPermIsDisabled, ↓reduceIte]
          constructor
          · intro _; exact ⟨trivial, trivial, trivial⟩
          · intro _; exact ⟨_, rfl⟩
        | cell | reservedFrz _ | reservedIM | unique | frozen =>
          simp only [miriPermIsDisabled, Bool.false_eq_true, ↓reduceIte]
          constructor
          · rintro ⟨_, h⟩; cases h
          · rintro ⟨_, _, hEq⟩; cases hEq

/-- SIFA `.read` soundness: whenever `miriStrongestSifa p isProt = some .read`, foreign read
leaves `p` unchanged. -/
theorem miriSifa_read_sound (p : MiriPerm) (isProt : Bool)
    (h : miriStrongestSifa p isProt = some .read) :
    miriPerformPermAccess .read .foreignAccess p isProt = .transition p := by
  rcases p with _ | (_ | _) | _ | _ | _ | _ <;> cases isProt <;>
    (dsimp only [miriStrongestSifa] at h; cases h <;> rfl)

/-- SIFA `.write` soundness: whenever `miriStrongestSifa p isProt = some .write`, BOTH foreign
read and foreign write leave `p` unchanged. -/
theorem miriSifa_write_sound (p : MiriPerm) (isProt : Bool) (k : MiriAccessKind)
    (h : miriStrongestSifa p isProt = some .write) :
    miriPerformPermAccess k .foreignAccess p isProt = .transition p := by
  rcases p with _ | (_ | _) | _ | _ | _ | _ <;> cases isProt <;> cases k <;>
    (dsimp only [miriStrongestSifa] at h; cases h <;> rfl)

/-- Universal pre-error SIFA commit on a forbidden local `.write` access to `.frozen`. -/
theorem miriPerformLocAccess_local_forbidden_resets_sifa (tag : Nat)
    (acc : Bool) (sifa : MiriSifa) (isProt : Bool) :
    miriPerformLocAccess tag ⟨.frozen, acc, sifa⟩ .write .localAccess isProt =
      .err ⟨.frozen, acc, .none⟩ (.childAccessForbidden tag .frozen) :=
  rfl

/-- Universal rejection of lazy `.unique` outside-range location states. -/
theorem miriInitialOutsideLoc_rejects_lazy_unique (tag : Nat) (isProtected : Bool) :
    miriInitialOutsideLoc tag .unique isProtected = .error (.invalidLazyState tag) := by
  cases isProtected <;> rfl

/-! ### IV.2. Two-Phase Borrow (`ReservedFrz` / `ReservedIM`) Activation & Conflict Laws -/

/-- Unconflicted two-phase borrow `.reservedFrz false` activates to `.unique` on child write
regardless of protector status. -/
theorem miriTwoPhase_unconflicted_activates (isProtected : Bool) :
    miriPerformPermAccess .write .localAccess (.reservedFrz false) isProtected =
      .transition .unique := by
  cases isProtected <;> rfl

/-- Foreign read sets the conflict latch on protected `.reservedFrz`, while unprotected foreign read
preserves `conflicted`. -/
theorem miriTwoPhase_foreignRead_sets_conflict (c : Bool) :
    miriPerformPermAccess .read .foreignAccess (.reservedFrz c) true =
      .transition (.reservedFrz true) ∧
    miriPerformPermAccess .read .foreignAccess (.reservedFrz c) false =
      .transition (.reservedFrz c) :=
  ⟨rfl, rfl⟩

/-- Activating a conflicted protected two-phase borrow (`.reservedFrz true`, `isProtected = true`)
is UB (`.undefinedBehavior`) and resets SIFA to `.none` in `miriPerformLocAccess`. -/
theorem miriTwoPhase_conflicted_protected_write_ub (tag : Nat) (acc : Bool) (sifa : MiriSifa) :
    miriPerformPermAccess .write .localAccess (.reservedFrz true) true = .undefinedBehavior ∧
    miriPerformLocAccess tag ⟨.reservedFrz true, acc, sifa⟩ .write .localAccess true =
      .err ⟨.reservedFrz true, acc, .none⟩ (.childAccessForbidden tag (.reservedFrz true)) :=
  ⟨rfl, rfl⟩

/-- Once protection ends (`isProtected = false`), activating a conflicted `.reservedFrz true`
succeeds and transitions to `.unique`. -/
theorem miriTwoPhase_conflicted_unprotected_activates (tag : Nat) (acc : Bool) (sifa : MiriSifa) :
    miriPerformPermAccess .write .localAccess (.reservedFrz true) false = .transition .unique ∧
    miriPerformLocAccess tag ⟨.reservedFrz true, acc, sifa⟩ .write .localAccess false =
      .ok ⟨.unique, true, .none⟩ := by
  cases acc <;> exact ⟨rfl, rfl⟩

/-- Interior-mutable two-phase `.reservedIM` survives unprotected foreign reads/writes, activates
to `.unique` on local write, and rejects protected foreign accesses as impossible. -/
theorem miriReservedIM_laws (k : MiriAccessKind) :
    miriPerformPermAccess k .foreignAccess .reservedIM false = .transition .reservedIM ∧
    miriPerformPermAccess k .foreignAccess .reservedIM true = .impossibleProtectedReservedIM ∧
    miriPerformPermAccess .write .localAccess .reservedIM false = .transition .unique := by
  cases k <;> exact ⟨rfl, rfl, rfl⟩

/-! ### IV.3. Disjoint-Allocation, Disjoint-Range & Disjoint-Tag Frame Preservation -/

private theorem natBeq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hEq : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (Nat.eq_of_beq_eq_true hEq))

private theorem natBle_true_of_le {a b : Nat} (h : a ≤ b) : Nat.ble a b = true :=
  Nat.ble_eq.mpr h

private theorem natBlt_false_of_le {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hLt : Nat.blt a b with
  | false => rfl
  | true =>
    have hLtNat : a < b := Nat.blt_eq.mp hLt
    exact False.elim (Nat.not_le_of_gt hLtNat h)

private theorem foldl_findAllocTree_replace_other (a : AllocId) (t' : MiriAllocTree)
    (hNe : t'.allocId ≠ a) :
    ∀ (trees : List MiriAllocTree) (init : Option MiriAllocTree),
      (miriReplaceAllocTree t' trees).foldl
          (fun acc t => if Nat.beq t.allocId a then some t else acc) init =
        trees.foldl (fun acc t => if Nat.beq t.allocId a then some t else acc) init
  | [], _ => rfl
  | t :: rest, init => by
    dsimp only [miriReplaceAllocTree, List.map, List.foldl]
    cases hEq : Nat.beq t.allocId t'.allocId with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact foldl_findAllocTree_replace_other a t' hNe rest _
    | true =>
      simp only [↓reduceIte]
      have hTid : t.allocId = t'.allocId := Nat.eq_of_beq_eq_true hEq
      have hNe1 : Nat.beq t'.allocId a = false := natBeq_false_of_ne hNe
      have hNe2 : Nat.beq t.allocId a = false := by rw [hTid]; exact hNe1
      simp only [hNe1, hNe2, Bool.false_eq_true, ↓reduceIte]
      exact foldl_findAllocTree_replace_other a t' hNe rest init

/-- Replacing the borrow tree of `t'.allocId` leaves `miriFindAllocTree? a₂` unchanged for every
disjoint allocation `a₂ ≠ t'.allocId`. -/
theorem miriFindAllocTree?_replace_other (a₂ : AllocId) (t' : MiriAllocTree)
    (trees : List MiriAllocTree) (hNe : t'.allocId ≠ a₂) :
    miriFindAllocTree? a₂ (miriReplaceAllocTree t' trees) = miriFindAllocTree? a₂ trees :=
  foldl_findAllocTree_replace_other a₂ t' hNe trees none

private theorem foldl_findAllocTree_replace_self (t' : MiriAllocTree) :
    ∀ (trees : List MiriAllocTree) (init₁ init₂ : Option MiriAllocTree),
      (match init₁ with | none => init₂ = none | some _ => init₂ = some t') →
      match trees.foldl (fun acc t => if Nat.beq t.allocId t'.allocId then some t else acc) init₁ with
      | none =>
        (miriReplaceAllocTree t' trees).foldl
          (fun acc t => if Nat.beq t.allocId t'.allocId then some t else acc) init₂ = none
      | some _ =>
        (miriReplaceAllocTree t' trees).foldl
          (fun acc t => if Nat.beq t.allocId t'.allocId then some t else acc) init₂ = some t'
  | [], init₁, _, hInit => by
    cases init₁ with
    | none => exact hInit
    | some _ => exact hInit
  | t :: rest, init₁, init₂, hInit => by
    dsimp only [miriReplaceAllocTree, List.map, List.foldl]
    cases hEq : Nat.beq t.allocId t'.allocId with
    | true =>
      have hSelf : Nat.beq t'.allocId t'.allocId = true := Nat.beq_refl t'.allocId
      simp only [hSelf, ↓reduceIte]
      exact foldl_findAllocTree_replace_self t' rest (some t) (some t') rfl
    | false =>
      simp only [hEq, Bool.false_eq_true, ↓reduceIte]
      exact foldl_findAllocTree_replace_self t' rest init₁ init₂ hInit

/-- Replacing `t'.allocId` when present always causes `miriFindAllocTree? t'.allocId` to return
`some t'` (even without a uniqueness precondition, because `miriReplaceAllocTree` updates every
matching entry). -/
theorem miriFindAllocTree?_replace_self (t' old : MiriAllocTree)
    (trees : List MiriAllocTree)
    (hFind : miriFindAllocTree? t'.allocId trees = some old) :
    miriFindAllocTree? t'.allocId (miriReplaceAllocTree t' trees) = some t' := by
  have h := foldl_findAllocTree_replace_self t' trees none none rfl
  unfold miriFindAllocTree? at hFind ⊢
  rw [hFind] at h
  exact h

private theorem foldl_findAllocTree_eq_init_of_forall_ne (a : AllocId) :
    ∀ (trees : List MiriAllocTree) (init : Option MiriAllocTree),
      (∀ t ∈ trees, a ≠ t.allocId) →
      trees.foldl (fun acc t => if Nat.beq t.allocId a then some t else acc) init = init
  | [], _, _ => rfl
  | t :: rest, init, hAll => by
    dsimp only [List.foldl]
    have hNe : t.allocId ≠ a := fun h => hAll t List.mem_cons_self h.symm
    have hF : Nat.beq t.allocId a = false := natBeq_false_of_ne hNe
    simp only [hF, Bool.false_eq_true, ↓reduceIte]
    exact foldl_findAllocTree_eq_init_of_forall_ne a rest init
      (fun u hu => hAll u (List.mem_cons_of_mem t hu))

/-- Under `MiriAllocIdsNoDup trees`, `miriFindAllocTree?` (last-match `foldl`) coincides
identically with `List.find?` (first-match), eliminating any duplicate-key discrepancy with
`miriReplaceAllocTree`! -/
theorem miriFindAllocTree?_eq_find?_of_noDup (a : AllocId) :
    ∀ (trees : List MiriAllocTree),
      MiriAllocIdsNoDup trees →
      miriFindAllocTree? a trees = trees.find? (fun t => Nat.beq t.allocId a)
  | [], _ => rfl
  | t :: rest, hNoDup => by
    cases hNoDup with
    | cons hHead hTail =>
      unfold miriFindAllocTree?
      dsimp only [List.foldl, List.find?]
      cases hEq : Nat.beq t.allocId a with
      | true =>
        simp only [↓reduceIte]
        have hTid : t.allocId = a := Nat.eq_of_beq_eq_true hEq
        exact foldl_findAllocTree_eq_init_of_forall_ne a rest (some t)
          (fun u hu => by rw [← hTid]; exact hHead u hu)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact miriFindAllocTree?_eq_find?_of_noDup a rest hTail

private theorem mem_replaceAllocTree_allocId (t' : MiriAllocTree) :
    ∀ (trees : List MiriAllocTree) (u : MiriAllocTree),
      u ∈ miriReplaceAllocTree t' trees →
      ∃ v ∈ trees, u.allocId = v.allocId
  | [], _, hMem => by cases hMem
  | t :: rest, u, hMem => by
    cases hMem with
    | head _ =>
      refine ⟨t, List.mem_cons_self, ?_⟩
      dsimp only
      cases hEq : Nat.beq t.allocId t'.allocId with
      | true =>
        simp only [↓reduceIte]
        exact (Nat.eq_of_beq_eq_true hEq).symm
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
    | tail _ hTail =>
      match mem_replaceAllocTree_allocId t' rest u hTail with
      | ⟨v, hv, hId⟩ => exact ⟨v, List.mem_cons_of_mem t hv, hId⟩

/-- `miriReplaceAllocTree` strictly preserves `MiriAllocIdsNoDup` (every element keeps its exact
`allocId`). -/
theorem miriReplaceAllocTree_preserves_noDup (t' : MiriAllocTree) :
    ∀ (trees : List MiriAllocTree),
      MiriAllocIdsNoDup trees →
      MiriAllocIdsNoDup (miriReplaceAllocTree t' trees)
  | [], _ => List.Pairwise.nil
  | t :: rest, hNoDup => by
    cases hNoDup with
    | cons hHead hTail =>
      dsimp only [miriReplaceAllocTree, List.map]
      refine List.Pairwise.cons ?_ (miriReplaceAllocTree_preserves_noDup t' rest hTail)
      intro u hu
      match mem_replaceAllocTree_allocId t' rest u hu with
      | ⟨v, hv, hId⟩ =>
        have hSelfId : (if Nat.beq t.allocId t'.allocId then t' else t).allocId = t.allocId := by
          cases hEq : Nat.beq t.allocId t'.allocId with
          | true => simp only [↓reduceIte]; exact (Nat.eq_of_beq_eq_true hEq).symm
          | false => simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hSelfId, hId]
        exact hHead v hv

/-- `miriPerformRangedAccess` preserves `MiriAllocIdsNoDup` on BOTH `.ok` and `.err` outcomes! -/
theorem miriPerformRangedAccess_preserves_noDup (st : MiriTbState)
    (allocId : AllocId) (accessedTag off size : Nat)
    (kind : MiriAccessKind) (mode : MiriVisitMode)
    (hNoDup : MiriAllocIdsNoDup st.allocTrees) :
    match miriPerformRangedAccess st allocId accessedTag off size kind mode with
    | .ok st' => MiriAllocIdsNoDup st'.allocTrees
    | .err st' _ => MiriAllocIdsNoDup st'.allocTrees := by
  unfold miriPerformRangedAccess
  cases miriFindAllocTree? allocId st.allocTrees with
  | none => exact hNoDup
  | some atree =>
    dsimp only
    cases miriFindTopoNode? accessedTag atree.tree with
    | none => exact hNoDup
    | some _ =>
      dsimp only
      generalize hFold :
        (miriSplitSegmentsAt off size atree.segments).foldl _ ([], 0, none) = foldRes
      cases foldRes with
      | mk segs rest =>
        cases rest with
        | mk cov errOpt =>
          have hRep := miriReplaceAllocTree_preserves_noDup
            { allocId := allocId, tree := atree.tree, segments := segs } st.allocTrees hNoDup
          cases errOpt with
          | some _ => exact hRep
          | none =>
            dsimp only
            cases Nat.beq cov size with
            | true => exact hRep
            | false => exact hRep

/-- `miriReleaseOneProtector` preserves `MiriAllocIdsNoDup` on BOTH `.ok` and `.err` outcomes! -/
theorem miriReleaseOneProtector_preserves_noDup (st : MiriTbState)
    (allocId : AllocId) (tag : Nat) (hNoDup : MiriAllocIdsNoDup st.allocTrees) :
    match miriReleaseOneProtector st allocId tag with
    | .ok st' => MiriAllocIdsNoDup st'.allocTrees
    | .err st' _ => MiriAllocIdsNoDup st'.allocTrees := by
  unfold miriReleaseOneProtector
  cases miriFindAllocTree? allocId st.allocTrees with
  | none => exact hNoDup
  | some atree =>
    dsimp only
    cases miriFindTopoNode? tag atree.tree with
    | none => exact hNoDup
    | some _ =>
      dsimp only
      generalize hFold : atree.segments.foldl _ ([], none) = foldRes
      cases foldRes with
      | mk segs errOpt =>
        have hRep := miriReplaceAllocTree_preserves_noDup
          { allocId := allocId, tree := atree.tree, segments := segs } st.allocTrees hNoDup
        cases errOpt with
        | some _ => exact hRep
        | none => exact hRep

/-- `miriBeginFrame` preserves `MiriAllocIdsNoDup` on both `.ok` and `.err`. -/
theorem miriBeginFrame_preserves_noDup (st : MiriTbState) (frameId : Nat)
    (hNoDup : MiriAllocIdsNoDup st.allocTrees) :
    match miriBeginFrame st frameId with
    | .ok st' => MiriAllocIdsNoDup st'.allocTrees
    | .err st' _ => MiriAllocIdsNoDup st'.allocTrees := by
  unfold miriBeginFrame
  cases miriFindFrame? frameId st.frames with
  | some _ => exact hNoDup
  | none => exact hNoDup

/-- `miriRegisterProtectorOpt` leaves `allocTrees` identically untouched. -/
theorem miriRegisterProtectorOpt_allocTrees (st : MiriTbState) (frameIdOpt : Option Nat)
    (allocId : AllocId) (newTag : Nat) :
    (miriRegisterProtectorOpt st frameIdOpt allocId newTag).allocTrees = st.allocTrees := by
  cases frameIdOpt <;> rfl

/-- `miriEndCall` leaves `allocTrees` identically untouched. -/
theorem miriEndCall_allocTrees (st : MiriTbState) (frameId : Nat) :
    (miriEndCall st frameId).allocTrees = st.allocTrees :=
  rfl

/-- `miriReborrowTag` preserves `MiriAllocIdsNoDup` across ALL `.ok` and `.err` paths! -/
theorem miriReborrowTag_preserves_noDup (mem : Memory) (st : MiriTbState)
    (frameIdOpt : Option Nat) (allocId : AllocId) (newTag parentTag : Nat)
    (insidePerm outsidePerm : MiriPerm) (off size : Nat)
    (hNoDup : MiriAllocIdsNoDup st.allocTrees) :
    match miriReborrowTag mem st frameIdOpt allocId newTag parentTag insidePerm outsidePerm off size with
    | .ok st' => MiriAllocIdsNoDup st'.allocTrees
    | .err st' _ => MiriAllocIdsNoDup st'.allocTrees := by
  unfold miriReborrowTag
  dsimp only
  cases miriInitialInsideLoc newTag insidePerm _ with
  | error _ => exact hNoDup
  | ok insideLoc =>
    dsimp only
    cases miriInitialOutsideLoc newTag outsidePerm _ with
    | error _ => exact hNoDup
    | ok outsideLoc =>
      dsimp only
      cases miriCheckFrameOpt frameIdOpt st.frames with
      | error _ => exact hNoDup
      | ok _ =>
        dsimp only
        have hRegNoDup :
            MiriAllocIdsNoDup (miriRegisterProtectorOpt st frameIdOpt allocId newTag).allocTrees := by
          rw [miriRegisterProtectorOpt_allocTrees]; exact hNoDup
        cases miriInspectAllocV2026 allocId mem with
        | missing => exact hRegNoDup
        | dead => exact hRegNoDup
        | live mutability =>
          dsimp only
          cases miriFindAllocTree? allocId st.allocTrees with
          | none => exact hRegNoDup
          | some atree0 =>
            dsimp only
            cases miriFindTopoNode? newTag atree0.tree with
            | some _ => exact hRegNoDup
            | none =>
              dsimp only
              cases miriFindTopoNode? parentTag atree0.tree with
              | none => exact hRegNoDup
              | some _ =>
                dsimp only
                have hParentStep :
                    match
                      (match Nat.beq size 0 with
                       | true => MiriTbResult.ok (miriRegisterProtectorOpt st frameIdOpt allocId newTag)
                       | false =>
                         match miriAssociatedAccess insidePerm with
                         | none =>
                           if miriRangeIsCovered off size atree0.segments then
                             .ok (miriRegisterProtectorOpt st frameIdOpt allocId newTag)
                           else
                             .err (miriRegisterProtectorOpt st frameIdOpt allocId newTag)
                               (.uncoveredRange allocId)
                         | some pKind =>
                           match !miriKindIsRead pKind &&
                             (match mutability with | .not => true | .mut => false) with
                           | true =>
                             .err (miriRegisterProtectorOpt st frameIdOpt allocId newTag)
                               (.writeToReadOnly allocId)
                           | false =>
                             miriPerformRangedAccess
                               (miriRegisterProtectorOpt st frameIdOpt allocId newTag)
                               allocId parentTag off size pKind .visitChildrenOfAccessed) with
                    | .ok stP => MiriAllocIdsNoDup stP.allocTrees
                    | .err stP _ => MiriAllocIdsNoDup stP.allocTrees := by
                  cases Nat.beq size 0 with
                  | true => exact hRegNoDup
                  | false =>
                    dsimp only
                    cases miriAssociatedAccess insidePerm with
                    | none =>
                      dsimp only
                      cases miriRangeIsCovered off size atree0.segments with
                      | true => exact hRegNoDup
                      | false => exact hRegNoDup
                    | some pKind =>
                      dsimp only
                      cases !miriKindIsRead pKind &&
                          (match mutability with | .not => true | .mut => false) with
                      | true => exact hRegNoDup
                      | false =>
                        dsimp only
                        exact miriPerformRangedAccess_preserves_noDup
                          (miriRegisterProtectorOpt st frameIdOpt allocId newTag)
                          allocId parentTag off size pKind .visitChildrenOfAccessed hRegNoDup
                have hFin :
                    ∀ (ps : MiriTbResult MiriTbState),
                      (match ps with
                       | .ok stP => MiriAllocIdsNoDup stP.allocTrees
                       | .err stP _ => MiriAllocIdsNoDup stP.allocTrees) →
                      match
                        (match ps with
                         | .err partialSt err => MiriTbResult.err partialSt err
                         | .ok stAfterParent =>
                           match miriFindAllocTree? allocId stAfterParent.allocTrees with
                           | none => .err stAfterParent (.uncoveredRange allocId)
                           | some atree =>
                             let ancPath := miriAncestorPath atree.tree parentTag
                             let tree' := miriInsertChildTopo atree.tree parentTag newTag
                             let splitSegs := miriSplitSegmentsAt off size atree.segments
                             let minSifa :=
                               if Nat.beq size 0 then
                                 outsideLoc.sifa
                               else
                                 miriSifaEnsureNoStrongerThan insideLoc.sifa outsideLoc.sifa
                             let segs' : List MiriSegment :=
                               splitSegs.map (fun seg =>
                                 let wSeg := miriWeakenSegmentAncestors ancPath minSifa seg
                                 let childLoc :=
                                   if miriSegmentOverlaps off size seg then insideLoc else outsideLoc
                                 MiriSegment.mk wSeg.offset wSeg.size
                                   (wSeg.entries ++ [MiriTagEntry.mk newTag childLoc]))
                             .ok { frames := stAfterParent.frames
                                   allocTrees :=
                                     miriReplaceAllocTree
                                       { allocId := allocId, tree := tree', segments := segs' }
                                       stAfterParent.allocTrees }) with
                      | .ok st' => MiriAllocIdsNoDup st'.allocTrees
                      | .err st' _ => MiriAllocIdsNoDup st'.allocTrees := by
                  intro ps hPs
                  cases ps with
                  | err partialSt err => exact hPs
                  | ok stAfterParent =>
                    dsimp only
                    cases miriFindAllocTree? allocId stAfterParent.allocTrees with
                    | none => exact hPs
                    | some atree =>
                      dsimp only
                      exact miriReplaceAllocTree_preserves_noDup _ stAfterParent.allocTrees hPs
                exact hFin _ hParentStep

/-- `miriReleaseTagListForward` preserves `MiriAllocIdsNoDup` on BOTH `.ok` and `.err` outcomes! -/
theorem miriReleaseTagListForward_preserves_noDup (mem : Memory)
    (tags : List (AllocId × Nat)) :
    ∀ (st : MiriTbState),
      MiriAllocIdsNoDup st.allocTrees →
      match miriReleaseTagListForward mem st tags with
      | .ok st' => MiriAllocIdsNoDup st'.allocTrees
      | .err st' _ => MiriAllocIdsNoDup st'.allocTrees := by
  induction tags with
  | nil =>
    intro st hNoDup
    exact hNoDup
  | cons pair rest ih =>
    intro st hNoDup
    have hFold :
        ∀ (acc : MiriTbResult MiriTbState),
          (match acc with
           | .ok s => MiriAllocIdsNoDup s.allocTrees
           | .err s _ => MiriAllocIdsNoDup s.allocTrees) →
          match rest.foldl
              (fun (a : MiriTbResult MiriTbState) p =>
                match a with
                | .err ps e => .err ps e
                | .ok cs =>
                  match miriInspectAllocV2026 p.1 mem with
                  | .missing => .err cs (.deadOrMissingAlloc p.1)
                  | .dead => .ok cs
                  | .live _ => miriReleaseOneProtector cs p.1 p.2) acc with
          | .ok st' => MiriAllocIdsNoDup st'.allocTrees
          | .err st' _ => MiriAllocIdsNoDup st'.allocTrees := by
      intro acc hAcc
      cases acc with
      | ok s => exact ih s hAcc
      | err ps e =>
        have hSticky :
            ∀ (xs : List (AllocId × Nat)),
              xs.foldl
                (fun (a : MiriTbResult MiriTbState) p =>
                  match a with
                  | .err ps' e' => .err ps' e'
                  | .ok cs =>
                    match miriInspectAllocV2026 p.1 mem with
                    | .missing => .err cs (.deadOrMissingAlloc p.1)
                    | .dead => .ok cs
                    | .live _ => miriReleaseOneProtector cs p.1 p.2)
                (MiriTbResult.err ps e) = MiriTbResult.err ps e := by
          intro xs
          induction xs with
          | nil => rfl
          | cons _ tl ihXs => exact ihXs
        rw [hSticky rest]
        exact hAcc
    unfold miriReleaseTagListForward
    dsimp only [List.foldl]
    apply hFold
    cases miriInspectAllocV2026 pair.1 mem with
    | missing => exact hNoDup
    | dead => exact hNoDup
    | live _ => exact miriReleaseOneProtector_preserves_noDup st pair.1 pair.2 hNoDup

/-- `miriExitCallFrame` preserves `MiriAllocIdsNoDup` on BOTH `.ok` and `.err` outcomes! -/
theorem miriExitCallFrame_preserves_noDup (mem : Memory) (st : MiriTbState) (frameId : Nat)
    (hNoDup : MiriAllocIdsNoDup st.allocTrees) :
    match miriExitCallFrame mem st frameId with
    | .ok st' => MiriAllocIdsNoDup st'.allocTrees
    | .err st' _ => MiriAllocIdsNoDup st'.allocTrees := by
  unfold miriExitCallFrame
  cases miriFindFrame? frameId st.frames with
  | none => exact hNoDup
  | some frame =>
    dsimp only
    have hRel := miriReleaseTagListForward_preserves_noDup mem frame.protectedTags st hNoDup
    cases hR : miriReleaseTagListForward mem st frame.protectedTags with
    | err partialSt err => rw [hR] at hRel; exact hRel
    | ok releasedSt => rw [hR] at hRel; exact hRel

/-- Disjoint-allocation frame preservation for `miriPerformRangedAccess`: accessing `a₁` leaves
`a₂ ≠ a₁` completely untouched on BOTH `.ok` and `.err` outcomes! -/
theorem miriPerformRangedAccess_preserves_other_alloc (st : MiriTbState)
    (a₁ a₂ : AllocId) (hNe : a₁ ≠ a₂) (accessedTag off size : Nat)
    (kind : MiriAccessKind) (mode : MiriVisitMode) :
    match miriPerformRangedAccess st a₁ accessedTag off size kind mode with
    | .ok st' => MiriAllocTreeFrameEq a₂ st' st
    | .err st' _ => MiriAllocTreeFrameEq a₂ st' st := by
  unfold miriPerformRangedAccess MiriAllocTreeFrameEq
  cases miriFindAllocTree? a₁ st.allocTrees with
  | none => rfl
  | some atree =>
    dsimp only
    cases miriFindTopoNode? accessedTag atree.tree with
    | none => rfl
    | some _ =>
      dsimp only
      have hPres : ∀ segs,
          miriFindAllocTree? a₂
            (miriReplaceAllocTree { allocId := a₁, tree := atree.tree, segments := segs }
              st.allocTrees) = miriFindAllocTree? a₂ st.allocTrees := fun segs =>
        miriFindAllocTree?_replace_other a₂ { allocId := a₁, tree := atree.tree, segments := segs }
          st.allocTrees hNe
      generalize hFold :
        (miriSplitSegmentsAt off size atree.segments).foldl _ ([], 0, none) = foldRes
      cases foldRes with
      | mk segs rest =>
        cases rest with
        | mk cov errOpt =>
          cases errOpt with
          | some _ => exact hPres segs
          | none =>
            dsimp only
            cases Nat.beq cov size with
            | true => exact hPres segs
            | false => exact hPres segs

/-- Disjoint byte ranges never overlap in `miriSegmentOverlaps`. -/
theorem miriSegmentOverlaps_false_of_disjoint (off size : Nat) (seg : MiriSegment)
    (hDisj : MiriDisjointRange off size seg.offset seg.size) :
    MiriSegmentUntouched off size seg := by
  unfold MiriSegmentUntouched miriSegmentOverlaps
  cases hDisj with
  | inl hLe =>
    have hF : Nat.blt seg.offset (off + size) = false := natBlt_false_of_le hLe
    rw [hF]
    cases Nat.blt 0 size <;> cases Nat.blt 0 seg.size <;> rfl
  | inr hLe =>
    have hF : Nat.blt off (seg.offset + seg.size) = false := natBlt_false_of_le hLe
    rw [hF]
    cases Nat.blt 0 size <;> cases Nat.blt 0 seg.size <;> cases Nat.blt seg.offset (off + size) <;> rfl

/-- Splitting a segment disjoint from `[cutStart, cutEnd)` returns `[seg]` untouched. -/
theorem miriSplitOneSegment_disjoint (cutStart cutEnd : Nat) (seg : MiriSegment)
    (hDisj : seg.offset + seg.size ≤ cutStart ∨ cutEnd ≤ seg.offset) :
    miriSplitOneSegment cutStart cutEnd seg = [seg] := by
  unfold miriSplitOneSegment
  dsimp only
  cases hDisj with
  | inl hLe =>
    have hB : Nat.ble (seg.offset + seg.size) cutStart = true := natBle_true_of_le hLe
    rw [hB]
    cases Nat.ble cutEnd cutStart <;> rfl
  | inr hLe =>
    have hB : Nat.ble cutEnd seg.offset = true := natBle_true_of_le hLe
    rw [hB]
    cases Nat.ble cutEnd cutStart <;> cases Nat.ble (seg.offset + seg.size) cutStart <;> rfl

/-- In the ranged-access fold step, any non-overlapping segment `seg` is appended verbatim without
changing the covered byte count or error status. -/
theorem miriRangedStep_preserves_disjoint_segment (allocId : AllocId)
    (tree : List MiriTopoNode) (prot : List Nat) (accessedTag off size : Nat)
    (kind : MiriAccessKind) (mode : MiriVisitMode)
    (acc : List MiriSegment × Nat × Option MiriTbError) (seg : MiriSegment)
    (hUntouched : MiriSegmentUntouched off size seg) :
    (match acc.2.2 with
     | some err => (acc.1 ++ [seg], acc.2.1, some err)
     | none =>
       if miriSegmentOverlaps off size seg then
         match Nat.beq seg.offset (off + acc.2.1) with
         | false => (acc.1 ++ [seg], acc.2.1, some (.uncoveredRange allocId))
         | true =>
           match miriPerformSegmentAccess tree prot accessedTag kind mode seg with
           | .ok seg' => (acc.1 ++ [seg'], acc.2.1 + seg.size, none)
           | .err partialSeg err => (acc.1 ++ [partialSeg], acc.2.1, some err)
       else
         (acc.1 ++ [seg], acc.2.1, none)) =
    (acc.1 ++ [seg], acc.2.1, acc.2.2) := by
  cases acc with
  | mk segs rest =>
    cases rest with
    | mk cov errOpt =>
      cases errOpt with
      | some err => rfl
      | none =>
        unfold MiriSegmentUntouched at hUntouched
        dsimp only
        rw [hUntouched]
        rfl

private theorem foldl_findTag_append (tag : Nat) (xs ys : List MiriTagEntry)
    (init : Option MiriTagEntry) :
    (xs ++ ys).foldl (fun acc e => if Nat.beq e.tag tag then some e else acc) init =
      ys.foldl (fun acc e => if Nat.beq e.tag tag then some e else acc)
        (xs.foldl (fun acc e => if Nat.beq e.tag tag then some e else acc) init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => exact ih _

private theorem foldl_upsert_step_other (tag : Nat) (entry : MiriTagEntry)
    (hNe : entry.tag ≠ tag) :
    ∀ (entries : List MiriTagEntry) (seen : Bool) (out : List MiriTagEntry),
      let res := entries.foldl
        (fun (acc : Bool × List MiriTagEntry) e =>
          if Nat.beq e.tag entry.tag then (true, acc.2 ++ [entry])
          else (acc.1, acc.2 ++ [e]))
        (seen, out)
      miriFindTagEntry? tag res.2 =
        entries.foldl (fun acc e => if Nat.beq e.tag tag then some e else acc)
          (miriFindTagEntry? tag out)
  | [], _, out => rfl
  | e :: rest, seen, out => by
    dsimp only [List.foldl]
    cases hEq : Nat.beq e.tag entry.tag with
    | true =>
      simp only [↓reduceIte]
      have hEt : e.tag = entry.tag := Nat.eq_of_beq_eq_true hEq
      have hNe1 : Nat.beq entry.tag tag = false := natBeq_false_of_ne hNe
      have hNe2 : Nat.beq e.tag tag = false := by rw [hEt]; exact hNe1
      have hStep := foldl_upsert_step_other tag entry hNe rest true (out ++ [entry])
      dsimp only at hStep
      rw [hStep]
      unfold miriFindTagEntry?
      rw [foldl_findTag_append]
      dsimp only [List.foldl]
      simp only [hNe1, hNe2, Bool.false_eq_true, ↓reduceIte]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hStep := foldl_upsert_step_other tag entry hNe rest seen (out ++ [e])
      dsimp only at hStep
      rw [hStep]
      unfold miriFindTagEntry?
      rw [foldl_findTag_append]
      rfl

/-- Disjoint-tag entry framing: upserting `entry` leaves `miriFindTagEntry? tag` unchanged for
every `tag ≠ entry.tag`. -/
theorem miriUpsertTagEntry_preserves_other_tag (tag : Nat) (entry : MiriTagEntry)
    (entries : List MiriTagEntry) (hNe : entry.tag ≠ tag) :
    miriFindTagEntry? tag (miriUpsertTagEntry entry entries) = miriFindTagEntry? tag entries := by
  unfold miriUpsertTagEntry
  have hMain := foldl_upsert_step_other tag entry hNe entries false []
  dsimp only at hMain
  generalize hRes :
    entries.foldl
      (fun (acc : Bool × List MiriTagEntry) e =>
        if Nat.beq e.tag entry.tag then (true, acc.2 ++ [entry])
        else (acc.1, acc.2 ++ [e]))
      (false, []) = res at hMain ⊢
  cases res with
  | mk found out =>
    dsimp only at hMain ⊢
    cases found with
    | true => simp only [↓reduceIte]; exact hMain
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold miriFindTagEntry?
      rw [foldl_findTag_append]
      dsimp only [List.foldl]
      simp only [natBeq_false_of_ne hNe, Bool.false_eq_true, ↓reduceIte]
      exact hMain

/-- Non-conflicting unprotected foreign reads preserve the permission of every non-`.unique` tag
(`.cell`, `.reservedFrz c`, `.reservedIM`, `.frozen`, `.disabled`). -/
theorem miriPerformLocAccess_unprotected_foreignRead_preserves_nonUnique
    (tag : Nat) (st : MiriLocState) (hNotUnique : miriPermIsUnique st.perm = false) :
    miriPerformLocAccess tag st .read .foreignAccess false =
      .ok ⟨st.perm, st.accessed, miriSifaRecordNew st.sifa .read .foreignAccess⟩ := by
  cases st with
  | mk p acc sifa =>
    cases p with
    | unique => cases hNotUnique
    | cell => cases acc <;> rfl
    | reservedFrz c => cases c <;> cases acc <;> rfl
    | reservedIM => cases acc <;> rfl
    | frozen => cases acc <;> rfl
    | disabled => cases acc <;> rfl

/-- Universal local-before-foreign short-circuiting: when the accessed tag itself fails locally,
`miriPerformSegmentAccess` halts with that local error without modifying any other tag's entry. -/
theorem miriPerformSegmentAccess_local_short_circuits_before_foreign
    (tree : List MiriTopoNode) (prot : List Nat) (tag : Nat)
    (kind : MiriAccessKind) (mode : MiriVisitMode) (seg : MiriSegment)
    (nd : MiriTopoNode) (selfEntry : MiriTagEntry) (nextLoc : MiriLocState)
    (err : MiriTbError)
    (hTopo : miriFindTopoNode? tag tree = some nd)
    (hSelf : miriFindTagEntry? tag seg.entries = some selfEntry)
    (hFail : miriPerformLocAccess tag selfEntry.loc kind .localAccess
      (miriNatListMem tag prot) = .err nextLoc err) :
    miriPerformSegmentAccess tree prot tag kind mode seg =
      .err
        { offset := seg.offset
          size := seg.size
          entries := miriUpsertTagEntry { tag := tag, loc := nextLoc } seg.entries }
        err := by
  unfold miriPerformSegmentAccess
  rw [hTopo, hSelf]
  dsimp only
  rw [hFail]

/-! ### IV.4. Protector Release Commutation & Post-Release Unlock Laws -/

private theorem foldl_endCall_filter (fid : Nat) :
    ∀ (fs acc : List MiriFrameProtectors),
      fs.foldl (fun a f => if Nat.beq f.frameId fid then a else a ++ [f]) acc =
        acc ++ fs.filter (fun f => !Nat.beq f.frameId fid)
  | [], acc => by
    dsimp only [List.foldl, List.filter]
    exact (List.append_nil acc).symm
  | f :: rest, acc => by
    dsimp only [List.foldl, List.filter]
    cases Nat.beq f.frameId fid with
    | true =>
      simp only [↓reduceIte, Bool.not_true]
      exact foldl_endCall_filter fid rest acc
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [foldl_endCall_filter fid rest (acc ++ [f]), List.append_assoc]
      rfl

private theorem list_filter_comm {α : Type} (p q : α → Bool) :
    ∀ xs : List α, (xs.filter p).filter q = (xs.filter q).filter p
  | [] => rfl
  | x :: xs => by
    dsimp only [List.filter]
    cases hp : p x <;> cases hq : q x
    · exact list_filter_comm p q xs
    · dsimp only [List.filter]; rw [hp]; exact list_filter_comm p q xs
    · dsimp only [List.filter]; rw [hq]; exact list_filter_comm p q xs
    · dsimp only [List.filter]; rw [hp, hq]; exact congrArg (List.cons x) (list_filter_comm p q xs)

/-- `miriEndCall` on any two frames `f₁, f₂` commutes unconditionally! -/
theorem miriEndCall_comm (st : MiriTbState) (f₁ f₂ : Nat) :
    miriEndCall (miriEndCall st f₁) f₂ = miriEndCall (miriEndCall st f₂) f₁ := by
  unfold miriEndCall
  dsimp only
  rw [foldl_endCall_filter f₁ st.frames [], foldl_endCall_filter f₂ st.frames [],
      foldl_endCall_filter f₂ _ [], foldl_endCall_filter f₁ _ []]
  dsimp only [List.nil_append]
  rw [list_filter_comm]

private theorem foldl_findFrame_filter_other (f₁ f₂ : Nat) (hNe : f₁ ≠ f₂) :
    ∀ (fs : List MiriFrameProtectors) (init : Option MiriFrameProtectors),
      (fs.filter (fun f => !Nat.beq f.frameId f₁)).foldl
          (fun acc f => if Nat.beq f.frameId f₂ then some f else acc) init =
        fs.foldl (fun acc f => if Nat.beq f.frameId f₂ then some f else acc) init
  | [], _ => rfl
  | f :: rest, init => by
    dsimp only [List.filter, List.foldl]
    cases hEq1 : Nat.beq f.frameId f₁ with
    | false =>
      simp only [Bool.not_false, List.foldl]
      exact foldl_findFrame_filter_other f₁ f₂ hNe rest _
    | true =>
      simp only [Bool.not_true]
      have hFid : f.frameId = f₁ := Nat.eq_of_beq_eq_true hEq1
      have hNe2 : Nat.beq f.frameId f₂ = false := by rw [hFid]; exact natBeq_false_of_ne hNe
      simp only [hNe2, Bool.false_eq_true, ↓reduceIte]
      exact foldl_findFrame_filter_other f₁ f₂ hNe rest init

/-- Removing frame `f₁` via `miriEndCall` leaves frame `f₂ ≠ f₁` intact. -/
theorem miriEndCall_preserves_other_frame (st : MiriTbState) (f₁ f₂ : Nat) (hNe : f₁ ≠ f₂) :
    miriFindFrame? f₂ (miriEndCall st f₁).frames = miriFindFrame? f₂ st.frames := by
  unfold miriEndCall miriFindFrame?
  dsimp only
  rw [foldl_endCall_filter f₁ st.frames []]
  dsimp only [List.nil_append]
  exact foldl_findFrame_filter_other f₁ f₂ hNe st.frames none

/-- Releasing a protector on `a₁` leaves every disjoint allocation `a₂ ≠ a₁` untouched (and
preserves `frames`) on BOTH `.ok` and `.err` outcomes! -/
theorem miriReleaseOneProtector_preserves_other_alloc (st : MiriTbState)
    (a₁ a₂ : AllocId) (hNe : a₁ ≠ a₂) (tag : Nat) :
    match miriReleaseOneProtector st a₁ tag with
    | .ok st' => MiriAllocTreeFrameEq a₂ st' st ∧ st'.frames = st.frames
    | .err st' _ => MiriAllocTreeFrameEq a₂ st' st ∧ st'.frames = st.frames := by
  unfold miriReleaseOneProtector MiriAllocTreeFrameEq
  cases miriFindAllocTree? a₁ st.allocTrees with
  | none => exact ⟨rfl, rfl⟩
  | some atree =>
    dsimp only
    cases miriFindTopoNode? tag atree.tree with
    | none => exact ⟨rfl, rfl⟩
    | some _ =>
      dsimp only
      have hPres : ∀ segs,
          miriFindAllocTree? a₂
            (miriReplaceAllocTree { allocId := a₁, tree := atree.tree, segments := segs }
              st.allocTrees) = miriFindAllocTree? a₂ st.allocTrees := fun segs =>
        miriFindAllocTree?_replace_other a₂ { allocId := a₁, tree := atree.tree, segments := segs }
          st.allocTrees hNe
      generalize hFold : atree.segments.foldl _ ([], none) = foldRes
      cases foldRes with
      | mk segs errOpt =>
        cases errOpt with
        | none => exact ⟨hPres segs, rfl⟩
        | some _ => exact ⟨hPres segs, rfl⟩

private theorem replaceAllocTree_comm (t₁ t₂ : MiriAllocTree) (hNe : t₁.allocId ≠ t₂.allocId) :
    ∀ trees : List MiriAllocTree,
      miriReplaceAllocTree t₂ (miriReplaceAllocTree t₁ trees) =
        miriReplaceAllocTree t₁ (miriReplaceAllocTree t₂ trees)
  | [] => rfl
  | t :: rest => by
    dsimp only [miriReplaceAllocTree, List.map]
    cases h1 : Nat.beq t.allocId t₁.allocId with
    | true =>
      have hEq1 : t.allocId = t₁.allocId := Nat.eq_of_beq_eq_true h1
      have h2 : Nat.beq t.allocId t₂.allocId = false := by
        rw [hEq1]; exact natBeq_false_of_ne hNe
      have h12 : Nat.beq t₁.allocId t₂.allocId = false := natBeq_false_of_ne hNe
      simp only [h2, h12, h1, ↓reduceIte, Bool.false_eq_true]
      exact congrArg (List.cons t₁) (replaceAllocTree_comm t₁ t₂ hNe rest)
    | false =>
      cases h2 : Nat.beq t.allocId t₂.allocId with
      | true =>
        have hEq2 : t.allocId = t₂.allocId := Nat.eq_of_beq_eq_true h2
        have h21 : Nat.beq t₂.allocId t₁.allocId = false := by
          rw [← hEq2]; exact h1
        simp only [h2, h21, ↓reduceIte, Bool.false_eq_true]
        exact congrArg (List.cons t₂) (replaceAllocTree_comm t₁ t₂ hNe rest)
      | false =>
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
        exact congrArg (List.cons t) (replaceAllocTree_comm t₁ t₂ hNe rest)

/-- Releasing protectors on two distinct allocations `a₁ ≠ a₂` commutes unconditionally when both
individual releases succeed! -/
theorem miriReleaseOneProtector_comm_disjoint_allocs (st : MiriTbState)
    (a₁ a₂ : AllocId) (hNe : a₁ ≠ a₂) (t₁ t₂ : Nat)
    (at₁ at₂ : MiriAllocTree) (nd₁ nd₂ : MiriTopoNode)
    (hFind₁ : miriFindAllocTree? a₁ st.allocTrees = some at₁)
    (hFind₂ : miriFindAllocTree? a₂ st.allocTrees = some at₂)
    (hTopo₁ : miriFindTopoNode? t₁ at₁.tree = some nd₁)
    (hTopo₂ : miriFindTopoNode? t₂ at₂.tree = some nd₂)
    (segs₁ segs₂ : List MiriSegment)
    (hOk₁ : miriReleaseOneProtector st a₁ t₁ =
      .ok { frames := st.frames
            allocTrees := miriReplaceAllocTree
              { allocId := a₁, tree := at₁.tree, segments := segs₁ } st.allocTrees })
    (hOk₂ : miriReleaseOneProtector st a₂ t₂ =
      .ok { frames := st.frames
            allocTrees := miriReplaceAllocTree
              { allocId := a₂, tree := at₂.tree, segments := segs₂ } st.allocTrees }) :
    (match miriReleaseOneProtector st a₁ t₁ with
     | .ok st₁ => miriReleaseOneProtector st₁ a₂ t₂
     | .err s e => .err s e) =
    (match miriReleaseOneProtector st a₂ t₂ with
     | .ok st₂ => miriReleaseOneProtector st₂ a₁ t₁
     | .err s e => .err s e) := by
  have hNeSym : a₂ ≠ a₁ := fun h => hNe h.symm
  rw [hOk₁, hOk₂]
  dsimp only
  unfold miriReleaseOneProtector
  rw [miriFindAllocTree?_replace_other a₂ { allocId := a₁, tree := at₁.tree, segments := segs₁ }
        st.allocTrees hNe, hFind₂]
  dsimp only
  rw [hTopo₂]
  rw [miriFindAllocTree?_replace_other a₁ { allocId := a₂, tree := at₂.tree, segments := segs₂ }
        st.allocTrees hNeSym, hFind₁]
  dsimp only
  rw [hTopo₁]
  dsimp only
  unfold miriReleaseOneProtector at hOk₁ hOk₂
  rw [hFind₁] at hOk₁; dsimp only at hOk₁; rw [hTopo₁] at hOk₁; dsimp only at hOk₁
  rw [hFind₂] at hOk₂; dsimp only at hOk₂; rw [hTopo₂] at hOk₂; dsimp only at hOk₂
  generalize hR₁ : at₁.segments.foldl _ ([], none) = r₁ at hOk₁ ⊢
  generalize hR₂ : at₂.segments.foldl _ ([], none) = r₂ at hOk₂ ⊢
  cases r₁ with
  | mk s₁ e₁ =>
    cases e₁ with
    | some _ => cases hOk₁
    | none =>
      cases r₂ with
      | mk s₂ e₂ =>
        cases e₂ with
        | some _ => cases hOk₂
        | none =>
          dsimp only at hOk₁ hOk₂ ⊢
          have hTreeEq₁ :
              miriReplaceAllocTree { allocId := a₁, tree := at₁.tree, segments := s₁ } st.allocTrees =
              miriReplaceAllocTree { allocId := a₁, tree := at₁.tree, segments := segs₁ } st.allocTrees := by
            injection hOk₁ with hSt
            exact congrArg MiriTbState.allocTrees hSt
          have hTreeEq₂ :
              miriReplaceAllocTree { allocId := a₂, tree := at₂.tree, segments := s₂ } st.allocTrees =
              miriReplaceAllocTree { allocId := a₂, tree := at₂.tree, segments := segs₂ } st.allocTrees := by
            injection hOk₂ with hSt
            exact congrArg MiriTbState.allocTrees hSt
          rw [← hTreeEq₁, ← hTreeEq₂]
          rw [replaceAllocTree_comm
            { allocId := a₁, tree := at₁.tree, segments := s₁ }
            { allocId := a₂, tree := at₂.tree, segments := s₂ } hNe st.allocTrees]

/-- Protector removal unlocks subsequent foreign writes: for any accessed non-`.cell`/non-`.reservedIM`
permission (`.reservedFrz c`, `.unique`, `.frozen`), a foreign write is UB (`.protectedDisabled`)
while protected, and succeeds (transitioning to `.disabled`) once protection is removed! -/
theorem miriProtectorRemoval_allows_foreign_write (tag : Nat) (p : MiriPerm) (sifa : MiriSifa)
    (hNotCell : p ≠ .cell) (hNotResIM : p ≠ .reservedIM) :
    miriPerformLocAccess tag ⟨p, true, sifa⟩ .write .foreignAccess true =
      .err ⟨.disabled, true, .write⟩ (.protectedDisabled tag p) ∧
    miriPerformLocAccess tag ⟨p, true, sifa⟩ .write .foreignAccess false =
      .ok ⟨.disabled, true, .write⟩ := by
  cases p with
  | cell => exact False.elim (hNotCell rfl)
  | reservedIM => exact False.elim (hNotResIM rfl)
  | reservedFrz c => cases c <;> cases sifa <;> exact ⟨rfl, rfl⟩
  | unique => cases sifa <;> exact ⟨rfl, rfl⟩
  | frozen => cases sifa <;> exact ⟨rfl, rfl⟩
  | disabled => cases sifa <;> exact ⟨rfl, rfl⟩

/-! ### IV.5. Universal `#4185` Retag & Protector Release Laws over V2026 `Memory` -/

/-- Universal rejection of protected `.reservedIM` inside range. -/
theorem miriReborrowTag_rejects_protected_reservedIM (mem : Memory)
    (st : MiriTbState) (fid : Nat) (allocId : AllocId)
    (newTag parentTag off size : Nat) (outsidePerm : MiriPerm) :
    miriReborrowTag mem st (some fid) allocId newTag parentTag .reservedIM
      outsidePerm off size =
      .err st (.impossibleProtectedReservedIM newTag) :=
  rfl

/-- Universal rejection of `.unique` (write-associated) reborrow on a live read-only (`.not`)
allocation in V2026 `Memory`, retaining the registered protector on failure. -/
theorem miriReborrowTag_rejects_write_on_readonly_alloc (mem : Memory)
    (st : MiriTbState) (frameIdOpt : Option Nat) (allocId : AllocId)
    (newTag parentTag off size : Nat) (outsidePerm : MiriPerm)
    (atree : MiriAllocTree) (pnd : MiriTopoNode) (outLoc : MiriLocState)
    (hOut : miriInitialOutsideLoc newTag outsidePerm
      (match frameIdOpt with | some _ => true | none => false) = .ok outLoc)
    (hFrame : miriCheckFrameOpt frameIdOpt st.frames = .ok ())
    (hAlloc : miriInspectAllocV2026 allocId mem = .live .not)
    (hTree : miriFindAllocTree? allocId st.allocTrees = some atree)
    (hFresh : miriFindTopoNode? newTag atree.tree = none)
    (hParent : miriFindTopoNode? parentTag atree.tree = some pnd)
    (hSize : Nat.beq size 0 = false) :
    miriReborrowTag mem st frameIdOpt allocId newTag parentTag .unique
      outsidePerm off size =
      .err (miriRegisterProtectorOpt st frameIdOpt allocId newTag)
        (.writeToReadOnly allocId) := by
  unfold miriReborrowTag
  dsimp only [miriInitialInsideLoc, miriPermIsInitial, miriStrongestSifa,
    miriAssociatedAccess, miriNewAccessed]
  rw [hOut]
  dsimp only
  rw [hFrame]
  dsimp only
  rw [hAlloc]
  dsimp only
  rw [hTree]
  dsimp only
  rw [hFresh]
  dsimp only
  rw [hParent]
  dsimp only
  rw [hSize]
  rfl

/-- Universal protector retention on dead/missing allocation failure in V2026 `Memory`. -/
theorem miriReborrowTag_dead_alloc_retains_protector (mem : Memory)
    (st : MiriTbState) (fid : Nat) (allocId : AllocId)
    (newTag parentTag off size : Nat) (insidePerm outsidePerm : MiriPerm)
    (inLoc outLoc : MiriLocState)
    (hIn : miriInitialInsideLoc newTag insidePerm true = .ok inLoc)
    (hOut : miriInitialOutsideLoc newTag outsidePerm true = .ok outLoc)
    (hFrame : miriCheckFrameOpt (some fid) st.frames = .ok ())
    (hDead : miriInspectAllocV2026 allocId mem = .dead) :
    miriReborrowTag mem st (some fid) allocId newTag parentTag insidePerm
      outsidePerm off size =
      .err (miriRegisterProtectorOpt st (some fid) allocId newTag)
        (.deadOrMissingAlloc allocId) := by
  unfold miriReborrowTag
  dsimp only
  rw [hIn]
  dsimp only
  rw [hOut]
  dsimp only
  rw [hFrame]
  dsimp only
  rw [hDead]

/-- Universal duplicate-frame rejection in `miriBeginFrame`. -/
theorem miriBeginFrame_rejects_duplicate (st : MiriTbState) (frameId : Nat)
    (frame : MiriFrameProtectors)
    (hDup : miriFindFrame? frameId st.frames = some frame) :
    miriBeginFrame st frameId = .err st (.duplicateFrame frameId) := by
  unfold miriBeginFrame
  rw [hDup]

/-- Uniform-freeze contract of `miriRegisterFnEntryArg`. -/
theorem miriRegisterFnEntryArg_uniform_freeze (mem : Memory)
    (st : MiriTbState) (frameId : Nat) (allocId : AllocId)
    (newTag parentTag : Nat) (refKind : MiriRefKind)
    (frozen implicitWrites : Bool) (off size : Nat) :
    miriRegisterFnEntryArg mem st frameId allocId newTag parentTag refKind
      frozen implicitWrites off size =
      miriReborrowTag mem st (some frameId) allocId newTag parentTag
        (miriSelectRetagPerm refKind true frozen true implicitWrites)
        (miriSelectRetagPerm refKind false frozen true implicitWrites)
        off size :=
  rfl

/-- Universal dead-allocation skip in `miriExitCallFrame` on V2026 `Memory`. -/
theorem miriExitCallFrame_skips_dead_alloc (mem : Memory)
    (st : MiriTbState) (frameId : Nat) (allocId : AllocId) (tag : Nat)
    (hFrame : miriFindFrame? frameId st.frames =
      some { frameId := frameId, protectedTags := [(allocId, tag)] })
    (hDead : miriInspectAllocV2026 allocId mem = .dead) :
    miriExitCallFrame mem st frameId = .ok (miriEndCall st frameId) := by
  unfold miriExitCallFrame
  rw [hFrame]
  dsimp only [miriReleaseTagListForward, List.foldl]
  rw [hDead]

/-- Universal failure propagation in `miriExitCallFrame` without invoking `miriEndCall`. -/
theorem miriExitCallFrame_preserves_failure_without_endCall (mem : Memory)
    (st partialSt : MiriTbState) (frameId : Nat)
    (frame : MiriFrameProtectors) (err : MiriTbError)
    (hFrame : miriFindFrame? frameId st.frames = some frame)
    (hFail : miriReleaseTagListForward mem st frame.protectedTags = .err partialSt err) :
    miriExitCallFrame mem st frameId = .err partialSt err := by
  unfold miriExitCallFrame
  rw [hFrame]
  dsimp only
  rw [hFail]

/-! ### IV.6. Real Semantic Bridges to Unmodified `Trusted.Rustc.V2026_06_01.MirSemantics` -/

/-- **Exact 56-cell bridge** to unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowPermTransition`. -/
theorem miriPerformPermAccess_eq_v2026_treeBorrowPermTransition
    (kind : MiriAccessKind) (rel : MiriRelatedness)
    (perm : MiriPerm) (isProtected : Bool) :
    miriOutcomeToV2026 (miriPerformPermAccess kind rel perm isProtected) =
      treeBorrowPermTransition
        (miriAccessKindToV2026 kind) (miriRelToV2026 rel)
        (miriPermToV2026 perm) isProtected := by
  cases kind <;> cases rel <;> cases perm with
  | reservedFrz c => cases c <;> cases isProtected <;> rfl
  | _ => cases isProtected <;> rfl

/-- **Exact per-location access bridge** to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowNodeAccess`: for every accessed location (and
non-disabled foreign access, which Miri's visitor skips via `miriSkipIfKnownNoop`),
`miriPerformLocAccess` agrees identically with `treeBorrowNodeAccess` on transitions, UB, and
protected-`ReservedIM` failures! -/
theorem miriPerformLocAccess_agrees_v2026_treeBorrowNodeAccess
    (tag : Nat) (kind : MiriAccessKind) (rel : MiriRelatedness)
    (perm : MiriPerm) (sifa : MiriSifa) (isProtected : Bool)
    (hNotSkipped : rel = .foreignAccess → perm ≠ .disabled) :
    match treeBorrowNodeAccess (miriAccessKindToV2026 kind) (miriRelToV2026 rel)
        (miriPermToV2026 perm) isProtected with
    | .transition next =>
      miriPerformLocAccess tag ⟨perm, true, sifa⟩ kind rel isProtected =
        .ok ⟨v2026PermToMiri next, true, miriSifaRecordNew sifa kind rel⟩
    | .ub =>
      ∃ st' err,
        miriPerformLocAccess tag ⟨perm, true, sifa⟩ kind rel isProtected = .err st' err ∧
        (err = .childAccessForbidden tag perm ∨ err = .protectedDisabled tag perm)
    | .protectedReservedIM =>
      miriPerformLocAccess tag ⟨perm, true, sifa⟩ kind rel isProtected =
        .err ⟨perm, true, miriSifaRecordNew sifa kind rel⟩ (.impossibleProtectedReservedIM tag) := by
  cases kind <;> cases rel <;> cases perm with
  | reservedFrz c =>
    cases c <;> cases isProtected <;>
      first
      | rfl
      | exact ⟨_, _, rfl, Or.inl rfl⟩
      | exact ⟨_, _, rfl, Or.inr rfl⟩
  | disabled =>
    cases isProtected <;>
      first
      | exact False.elim (hNotSkipped rfl rfl)
      | exact ⟨_, _, rfl, Or.inl rfl⟩
  | _ =>
    cases isProtected <;>
      first
      | rfl
      | exact ⟨_, _, rfl, Or.inl rfl⟩
      | exact ⟨_, _, rfl, Or.inr rfl⟩

/-- **Exact deallocation-protection bridge** to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.preventsDeallocation`. -/
theorem miriPermPreventsDealloc_eq_v2026_preventsDeallocation (p : MiriPerm) :
    miriPermPreventsDealloc p = preventsDeallocation (miriPermToV2026 p) := by
  cases p <;> rfl

/-- **Exact deallocated-allocation bridge** to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.ptrAllocByteBound?`: whenever `miriInspectAllocV2026`
classifies a pointer's provenance tag as `.dead`, V2026's own pointer-bound resolution (which,
exactly like `miriInspectAllocV2026`, consults `mem.borrows` BEFORE `mem.globals`) assigns that
pointer the zero byte bound of a deallocated allocation, for EVERY frame, layout, and locals. -/
theorem miriInspectAllocV2026_dead_eq_v2026_ptrAllocByteBound_zero
    (locals : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (ptrVal : ProvenancePtr)
    (hDead : miriInspectAllocV2026 ptrVal.tag mem = .dead) :
    ptrAllocByteBound? locals mem localDecls layouts ptrVal = .some 0 := by
  unfold miriInspectAllocV2026 at hDead
  unfold ptrAllocByteBound?
  cases hB : lookupBorrow mem.borrows ptrVal.tag with
  | some be =>
    rw [hB] at hDead
    dsimp only at hDead
    cases hD : be.allocDead with
    | true => dsimp only; rw [hD]
    | false => simp only [hD, reduceCtorEq] at hDead
  | none =>
    rw [hB] at hDead
    dsimp only at hDead
    revert hDead
    cases lookupGlobalAlloc mem.globals ptrVal.tag <;> intro hDead <;> simp only [reduceCtorEq] at hDead

/-- **Borrow-shadowing law**: whenever `mem.borrows` has a LIVE entry for `allocId`,
`miriInspectAllocV2026` reports a live mutable stack allocation irrespective of `mem.globals`
(mirroring V2026's `lookupBorrow`-first resolution), so a same-numbered READ-ONLY global can
never cause a spurious `.writeToReadOnly` rejection. -/
theorem miriInspectAllocV2026_live_borrow_shadows_globals (allocId : AllocId) (mem : Memory)
    (be : BorrowEntry) (hB : lookupBorrow mem.borrows allocId = .some be)
    (hLive : be.allocDead = false) :
    miriInspectAllocV2026 allocId mem = .live .mut := by
  unfold miriInspectAllocV2026
  rw [hB]
  dsimp only
  rw [hLive]

/-- **Global fallback law**: whenever no stack borrow shadows `allocId`, `miriInspectAllocV2026`
falls back identically to unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.lookupGlobalAlloc`. -/
theorem miriInspectAllocV2026_global_fallback_eq (allocId : AllocId) (mem : Memory)
    (hNoB : lookupBorrow mem.borrows allocId = .none) :
    miriInspectAllocV2026 allocId mem =
      match lookupGlobalAlloc mem.globals allocId with
      | .some ga => .live ga.mutability
      | .none => .missing := by
  unfold miriInspectAllocV2026
  rw [hNoB]

/-- **Exact missing-allocation characterization**: `miriInspectAllocV2026 allocId mem = .missing`
iff BOTH `lookupBorrow mem.borrows allocId = .none` AND `lookupGlobalAlloc mem.globals allocId = .none`. -/
theorem miriInspectAllocV2026_missing_iff (allocId : AllocId) (mem : Memory) :
    miriInspectAllocV2026 allocId mem = .missing ↔
      lookupBorrow mem.borrows allocId = .none ∧
      lookupGlobalAlloc mem.globals allocId = .none := by
  unfold miriInspectAllocV2026
  cases hB : lookupBorrow mem.borrows allocId with
  | some be =>
    dsimp only
    constructor
    · intro hM
      cases hD : be.allocDead with
      | true => rw [hD] at hM; cases hM
      | false => rw [hD] at hM; cases hM
    · intro hPair; cases hPair.1
  | none =>
    dsimp only
    cases hG : lookupGlobalAlloc mem.globals allocId with
    | some ga =>
      constructor
      · intro hM; cases hM
      · intro hPair; cases hPair.2
    | none =>
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- **Exact retag initial-permission bridge** to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.retagPerm` and `fnEntryRetagPerm` across all four
`RetagKind`s, both `Mutability`s, and every `RigidTy` pointee! -/
theorem retagKindToInitialPerms_eq_v2026_retagPerm
    (rk : RetagKind) (mutability : Mutability) (pointee : RigidTy) :
    miriPermToV2026 (retagKindToInitialPerms rk mutability (rigidTyIsFreeze 16 pointee) false).1 =
      retagPerm rk mutability pointee ∧
    miriPermToV2026 (retagKindToInitialPerms rk mutability (rigidTyIsFreeze 16 pointee) false).2 =
      retagPerm rk mutability pointee := by
  cases rk <;> cases mutability <;>
    simp only [retagKindToInitialPerms, retagPerm, fnEntryRetagPerm,
      mutabilityToMiriRefKind, retagKindIsProtected, miriSelectRetagPerm] <;>
    cases rigidTyIsFreeze 16 pointee <;> exact ⟨rfl, rfl⟩

/-- **Exact shared-borrow initial-permission bridge** to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.sharedBorrowPerm`. -/
theorem miriSelectRetagPerm_eq_v2026_sharedBorrowPerm
    (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place) :
    miriPermToV2026
        (miriSelectRetagPerm .shared true
          (match placeTy localDecls layouts place with
           | .some ty => tyIsFreeze ty
           | .none => true)
          false false) =
      sharedBorrowPerm localDecls layouts place := by
  unfold sharedBorrowPerm
  cases placeTy localDecls layouts place with
  | none => rfl
  | some ty => dsimp only; cases tyIsFreeze ty <;> rfl

/-- **Exact mutable-borrow initial-permission bridge** to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.mutableBorrowPerm`. -/
theorem miriSelectRetagPerm_eq_v2026_mutableBorrowPerm
    (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place) :
    miriPermToV2026
        (miriSelectRetagPerm .mutable true
          (match placeTy localDecls layouts place with
           | .some ty => tyIsFreeze ty
           | .none => true)
          false false) =
      mutableBorrowPerm localDecls layouts place := by
  unfold mutableBorrowPerm
  cases placeTy localDecls layouts place with
  | none => rfl
  | some ty => dsimp only; cases tyIsFreeze ty <;> rfl

/-- **Exact protector-check bridge** to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowProtectorCheck`: on any non-disabled foreign
access, `miriPerformLocAccess` agrees with `treeBorrowProtectorCheck` applied to
`treeBorrowPermTransition`. -/
theorem miriPerformLocAccess_foreign_eq_v2026_treeBorrowProtectorCheck
    (tag : Nat) (kind : MiriAccessKind) (perm : MiriPerm) (sifa : MiriSifa)
    (isProtected : Bool) (hNotDis : perm ≠ .disabled) :
    match treeBorrowProtectorCheck isProtected
        (treeBorrowPermTransition (miriAccessKindToV2026 kind) .foreignAccess
          (miriPermToV2026 perm) isProtected) with
    | .transition next =>
      miriPerformLocAccess tag ⟨perm, true, sifa⟩ kind .foreignAccess isProtected =
        .ok ⟨v2026PermToMiri next, true, miriSifaRecordNew sifa kind .foreignAccess⟩
    | .ub =>
      ∃ st' err,
        miriPerformLocAccess tag ⟨perm, true, sifa⟩ kind .foreignAccess isProtected = .err st' err ∧
        (err = .childAccessForbidden tag perm ∨ err = .protectedDisabled tag perm)
    | .protectedReservedIM =>
      miriPerformLocAccess tag ⟨perm, true, sifa⟩ kind .foreignAccess isProtected =
        .err ⟨perm, true, miriSifaRecordNew sifa kind .foreignAccess⟩
          (.impossibleProtectedReservedIM tag) := by
  have h := miriPerformLocAccess_agrees_v2026_treeBorrowNodeAccess tag kind .foreignAccess perm sifa
    isProtected (fun _ => hNotDis)
  cases perm with
  | disabled => exact False.elim (hNotDis rfl)
  | cell | reservedFrz _ | reservedIM | unique | frozen => exact h

/-- **Exact range-disjointness bridge** to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.rangesDisjoint`. -/
theorem miriRangesDisjointBool_eq_v2026_rangesDisjoint (off₁ sz₁ off₂ sz₂ : Nat) :
    miriRangesDisjointBool off₁ sz₁ off₂ sz₂ = rangesDisjoint off₁ sz₁ off₂ sz₂ :=
  rfl

private theorem natBlt_zero_eq_not_beq_zero (n : Nat) : Nat.blt 0 n = !(Nat.beq n 0) := by
  cases n <;> rfl

private theorem natBlt_eq_ble_succ (a b : Nat) : Nat.blt a b = Nat.ble (Nat.succ a) b := rfl

/-- **Exact byte-range overlap bridge** to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.byteRangesOverlapBool`. -/
theorem miriSegmentOverlaps_eq_v2026_byteRangesOverlapBool
    (off size : Nat) (seg : MiriSegment) :
    miriSegmentOverlaps off size seg = byteRangesOverlapBool off size seg.offset seg.size := by
  unfold miriSegmentOverlaps byteRangesOverlapBool
  rw [natBlt_zero_eq_not_beq_zero size, natBlt_zero_eq_not_beq_zero seg.size,
      natBlt_eq_ble_succ seg.offset (off + size), natBlt_eq_ble_succ off (seg.offset + seg.size)]
  cases Nat.beq size 0 <;> cases Nat.beq seg.size 0 <;>
    cases Nat.ble (Nat.succ off) (seg.offset + seg.size) <;>
    cases Nat.ble (Nat.succ seg.offset) (off + size) <;> rfl

/-- **Exact protected-write conflict bridge** to unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.borrowEntryWriteConflicts`: a protected `BorrowEntry`
conflicts with a write (`borrowEntryWriteConflicts entry writerTag = true`) iff
`miriPerformLocAccess` on the corresponding accessed non-skipped `MiriPerm` faults with `.err`! -/
theorem v2026_borrowEntryWriteConflicts_iff_miriPerformLocAccess_err
    (entry : BorrowEntry) (writerTag : Option Nat) (sifa : MiriSifa)
    (hNotSkipped : treeBorrowWriterRelatedness entry writerTag = .foreignAccess →
      entry.perm ≠ .disabled) :
    borrowEntryWriteConflicts entry writerTag = true ↔
      ∃ st' err,
        miriPerformLocAccess entry.tag ⟨v2026PermToMiri entry.perm, true, sifa⟩
          .write (v2026RelToMiri (treeBorrowWriterRelatedness entry writerTag)) true =
          .err st' err := by
  unfold borrowEntryWriteConflicts
  cases hRel : treeBorrowWriterRelatedness entry writerTag with
  | localAccess =>
    cases hP : entry.perm with
    | reservedFrz c =>
      cases c with
      | false =>
        exact ⟨(fun h => by cases h), (fun ⟨_, _, h⟩ => by cases h)⟩
      | true =>
        exact ⟨(fun _ => ⟨_, _, rfl⟩), (fun _ => rfl)⟩
    | cell =>
      exact ⟨(fun h => by cases h), (fun ⟨_, _, h⟩ => by cases h)⟩
    | reservedIM =>
      exact ⟨(fun h => by cases h), (fun ⟨_, _, h⟩ => by cases h)⟩
    | unique =>
      exact ⟨(fun h => by cases h), (fun ⟨_, _, h⟩ => by cases h)⟩
    | frozen =>
      exact ⟨(fun _ => ⟨_, _, rfl⟩), (fun _ => rfl)⟩
    | disabled =>
      exact ⟨(fun _ => ⟨_, _, rfl⟩), (fun _ => rfl)⟩
  | foreignAccess =>
    cases hP : entry.perm with
    | disabled => exact False.elim (hNotSkipped hRel hP)
    | cell =>
      exact ⟨(fun h => by cases h), (fun ⟨_, _, h⟩ => by cases h)⟩
    | reservedFrz c =>
      cases c <;> exact ⟨(fun _ => ⟨_, _, rfl⟩), (fun _ => rfl)⟩
    | reservedIM =>
      exact ⟨(fun _ => ⟨_, _, rfl⟩), (fun _ => rfl)⟩
    | unique =>
      exact ⟨(fun _ => ⟨_, _, rfl⟩), (fun _ => rfl)⟩
    | frozen =>
      exact ⟨(fun _ => ⟨_, _, rfl⟩), (fun _ => rfl)⟩

/-- Unmodified `V2026_06_01.MirSemantics.disableFrameBorrows` preserves every `BorrowEntry`
belonging to any other stack frame (`entry.targetFrameDepth ≠ depth`). -/
theorem v2026_disableFrameBorrows_preserves_other_frame
    (borrows : List BorrowEntry) (depth nLocals tag : Nat) (entry : BorrowEntry)
    (hLookup : lookupBorrow borrows tag = .some entry)
    (hOther : entry.targetFrameDepth ≠ depth) :
    lookupBorrow (disableFrameBorrows borrows depth nLocals) tag = .some entry := by
  induction borrows with
  | nil => cases hLookup
  | cons hd tl ih =>
    unfold lookupBorrow at hLookup
    unfold disableFrameBorrows
    cases hTag : Nat.beq hd.tag tag with
    | true =>
      rw [hTag] at hLookup
      cases hLookup
      have hNeD : Nat.beq entry.targetFrameDepth depth = false := natBeq_false_of_ne hOther
      rw [hNeD]
      simp only [Bool.false_and, lookupBorrow]
      rw [hTag]
    | false =>
      rw [hTag] at hLookup
      cases hMatch : Bool.and (Nat.beq hd.targetFrameDepth depth) (Nat.blt hd.targetLocal nLocals) with
      | true =>
        dsimp only [lookupBorrow]
        rw [hTag]
        exact ih hLookup
      | false =>
        dsimp only [lookupBorrow]
        rw [hTag]
        exact ih hLookup

/-- Unmodified `V2026_06_01.MirSemantics.hasFrameDeallocProtectorConflict` is `false` when no
protectors are active, and when every entry in `borrows` is `.cell` or `.disabled` (reflecting
`miriPermPreventsDealloc = false`). -/
theorem v2026_hasFrameDeallocProtectorConflict_false_of_cell_or_disabled
    (borrows : List BorrowEntry) (activeProtectors : List Nat) (depth nLocals : Nat)
    (hExempt : ∀ e, e ∈ borrows → miriPermPreventsDealloc (v2026PermToMiri e.perm) = false) :
    hasFrameDeallocProtectorConflict borrows activeProtectors depth nLocals = false := by
  cases activeProtectors with
  | nil => unfold hasFrameDeallocProtectorConflict; rfl
  | cons p ps =>
    induction borrows with
    | nil => rfl
    | cons hd tl ih =>
      unfold hasFrameDeallocProtectorConflict
      have hHd : miriPermPreventsDealloc (v2026PermToMiri hd.perm) = false :=
        hExempt hd List.mem_cons_self
      have hPrev : preventsDeallocation hd.perm = false := by
        rw [← miriPermToV2026_v2026PermToMiri hd.perm,
            ← miriPermPreventsDealloc_eq_v2026_preventsDeallocation]
        exact hHd
      dsimp only
      rw [hPrev]
      simp only [Bool.and_false]
      exact ih (fun e he => hExempt e (List.mem_cons_of_mem hd he))

/-- Unmodified `V2026_06_01.MirSemantics.restoreCallerProtectors` restores the caller's saved
protector stack cleanly on both `some` and `none` caller protectors. -/
theorem v2026_restoreCallerProtectors_spec (caller : SavedCallerFrame) :
    (∀ pid, caller.callerProtector = .some pid →
      restoreCallerProtectors caller = pid :: caller.calleeProtectors) ∧
    (caller.callerProtector = .none →
      restoreCallerProtectors caller = caller.calleeProtectors) := by
  constructor
  · intro pid h; unfold restoreCallerProtectors; rw [h]
  · intro h; unfold restoreCallerProtectors; rw [h]

/-- Unmodified `V2026_06_01.MirSemantics.invalidateTreeBorrowsAtProj` preserves every borrow entry
targeting a distinct local (`entry.targetLocal ≠ targetLocal`). -/
theorem v2026_invalidateTreeBorrowsAtProj_preserves_other_local
    (allBorrows borrows : List BorrowEntry) (targetLocal tag : Nat)
    (writerTag : Option Nat) (writeProj : List ProjectionElem)
    (off len depth : Nat) (entry : BorrowEntry)
    (hLookup : lookupBorrow borrows tag = .some entry)
    (hOther : entry.targetLocal ≠ targetLocal) :
    lookupBorrow
      (invalidateTreeBorrowsAtProj allBorrows borrows targetLocal writerTag writeProj off len depth)
      tag = .some entry := by
  induction borrows with
  | nil => cases hLookup
  | cons hd tl ih =>
    unfold lookupBorrow at hLookup
    unfold invalidateTreeBorrowsAtProj
    cases hTag : Nat.beq hd.tag tag with
    | true =>
      rw [hTag] at hLookup
      cases hLookup
      have hNeL : Nat.beq entry.targetLocal targetLocal = false := natBeq_false_of_ne hOther
      dsimp only [updateBorrowPermTreeAtProj, updateBorrowPermAtProj]
      rw [hNeL, Bool.and_false]
      dsimp only [lookupBorrow]
      rw [hTag]
    | false =>
      rw [hTag] at hLookup
      have hTagPres :
          (updateBorrowPermTreeAtProj allBorrows hd targetLocal writerTag writeProj off len depth).tag =
            hd.tag := by
        dsimp only [updateBorrowPermTreeAtProj, updateBorrowPermAtProj]
        cases Bool.and (Nat.beq hd.targetFrameDepth depth) (Nat.beq hd.targetLocal targetLocal) with
        | false => rfl
        | true =>
          cases treeBorrowWriterRelatedness hd (resolveTreeBorrowWriterTag allBorrows hd writerTag) with
          | localAccess =>
            exact (applyTreeBorrowTransition_fields hd _).1
          | foreignAccess =>
            cases borrowEntryOverlapsWrite hd writeProj off len with
            | false => rfl
            | true => exact (applyTreeBorrowTransition_fields hd _).1
      dsimp only [lookupBorrow]
      rw [hTagPres, hTag]
      exact ih hLookup

/-- Unmodified `V2026_06_01.MirSemantics.freezeTreeBorrowsOnReadAtProj` preserves every borrow
entry targeting a distinct local (`entry.targetLocal ≠ targetLocal`). -/
theorem v2026_freezeTreeBorrowsOnReadAtProj_preserves_other_local
    (allBorrows borrows : List BorrowEntry) (targetLocal tag : Nat)
    (readerTag : Option Nat) (readProj : List ProjectionElem)
    (off len depth : Nat) (activeProtectors : List Nat) (entry : BorrowEntry)
    (hLookup : lookupBorrow borrows tag = .some entry)
    (hOther : entry.targetLocal ≠ targetLocal) :
    lookupBorrow
      (freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal readerTag readProj off len
        activeProtectors depth)
      tag = .some entry := by
  induction borrows with
  | nil => cases hLookup
  | cons hd tl ih =>
    unfold lookupBorrow at hLookup
    unfold freezeTreeBorrowsOnReadAtProj
    cases hTag : Nat.beq hd.tag tag with
    | true =>
      rw [hTag] at hLookup
      cases hLookup
      have hNeL : Nat.beq entry.targetLocal targetLocal = false := natBeq_false_of_ne hOther
      dsimp only [updateBorrowPermOnReadAtProj]
      rw [hNeL, Bool.and_false]
      dsimp only [lookupBorrow]
      rw [hTag]
    | false =>
      rw [hTag] at hLookup
      have hTagPres :
          (updateBorrowPermOnReadAtProj allBorrows hd targetLocal readerTag readProj off len
            activeProtectors depth).tag = hd.tag := by
        dsimp only [updateBorrowPermOnReadAtProj]
        cases Bool.and (Nat.beq hd.targetFrameDepth depth) (Nat.beq hd.targetLocal targetLocal) with
        | false => rfl
        | true =>
          cases borrowEntryOverlapsWrite hd readProj off len with
          | false => rfl
          | true =>
            cases readerTag with
            | none => exact (applyTreeBorrowTransition_fields hd _).1
            | some rTag =>
              dsimp only
              cases isBorrowDescendantOrSelf allBorrows rTag hd.tag with
              | true => rfl
              | false => exact (applyTreeBorrowTransition_fields hd _).1
      dsimp only [lookupBorrow]
      rw [hTagPres, hTag]
      exact ih hLookup

/-- **Direct bridge to unmodified `V2026_06_01.MirSemantics.evalFnEntryRetag`**: retagging a
non-uninhabited reference local at function entry with no read UB installs a fresh protected child
whose permission is `miriPermToV2026 (retagKindToInitialPerms .fnEntry mutability (rigidTyIsFreeze 16 pointee) false).1`! -/
theorem v2026_evalFnEntryRetag_mints_protected_child
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (loc : Local) (ptrVal : ProvenancePtr) (sz : Nat)
    (parentEntry : BorrowEntry) (locals' locals'' : List LocalSlot)
    (mutability : Mutability) (pointee : RigidTy) (layoutIdx : LayoutIdx)
    (hTy : placeTy localDecls layouts { local_ := loc, projection := .nil } =
      .some { kind := .ref mutability pointee, layoutIdx := layoutIdx })
    (hInhab : rigidTyIsUninhabited 16 pointee = false)
    (hNoReadUB :
      fnEntryRetagPerm mutability pointee = .cell ∨
      rigidTyIsZeroSized 16 pointee = true ∨
      hasTreeReadUB s.memory.borrows s.memory.borrows s.memory.activeProtectors
        parentEntry.targetLocal (.some ptrVal.tag) parentEntry.targetProjection
        parentEntry.rangeOffset parentEntry.rangeLen parentEntry.targetFrameDepth = false)
    (hSet : set? locals' loc
      (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := ptrVal.offsetBytes } sz)) =
      .some locals'') :
    ∃ borrowsAfterRead : List BorrowEntry,
      evalFnEntryRetag s localDecls layouts { local_ := loc, projection := .nil }
        ptrVal sz parentEntry locals' =
      MirStepNode.step
        (advanceStmt s locals''
          { s.memory with
            borrows :=
              { tag := s.memory.nextTag
                targetLocal := parentEntry.targetLocal
                targetFrameDepth := parentEntry.targetFrameDepth
                allocDead := parentEntry.allocDead
                targetProjection := parentEntry.targetProjection
                perm := miriPermToV2026
                  (retagKindToInitialPerms .fnEntry mutability
                    (rigidTyIsFreeze 16 pointee) false).1
                rangeOffset := parentEntry.rangeOffset
                rangeLen := parentEntry.rangeLen
                protector := .some s.memory.nextProtector
                parentTag := .some ptrVal.tag } :: borrowsAfterRead
            nextTag := Nat.add s.memory.nextTag 1
            activeProtectors := s.memory.nextProtector :: s.memory.activeProtectors
            nextProtector := Nat.add s.memory.nextProtector 1 }) := by
  unfold evalFnEntryRetag
  rw [hTy]
  dsimp only
  rw [hInhab]
  dsimp only
  have hPermEq :
      fnEntryRetagPerm mutability pointee =
        miriPermToV2026
          (retagKindToInitialPerms .fnEntry mutability (rigidTyIsFreeze 16 pointee) false).1 :=
    (retagKindToInitialPerms_eq_v2026_retagPerm .fnEntry mutability pointee).1.symm
  cases hNoReadUB with
  | inl hCell =>
    rw [hCell] at hPermEq ⊢
    dsimp only
    rw [hSet, hPermEq]
    exact ⟨s.memory.borrows, rfl⟩
  | inr hRest =>
    cases hRest with
    | inl hZst =>
      cases hP : fnEntryRetagPerm mutability pointee with
      | cell =>
        rw [hP] at hPermEq
        dsimp only
        rw [hSet, hPermEq]
        exact ⟨s.memory.borrows, rfl⟩
      | reservedFrz _ | reservedIM | unique | frozen | disabled =>
        rw [hP] at hPermEq
        dsimp only
        rw [hZst]
        dsimp only
        rw [hSet, hPermEq]
        exact ⟨s.memory.borrows, rfl⟩
    | inr hNoUB =>
      cases hP : fnEntryRetagPerm mutability pointee with
      | cell =>
        rw [hP] at hPermEq
        dsimp only
        rw [hSet, hPermEq]
        exact ⟨s.memory.borrows, rfl⟩
      | reservedFrz _ | reservedIM | unique | frozen | disabled =>
        rw [hP] at hPermEq
        dsimp only
        cases rigidTyIsZeroSized 16 pointee with
        | true =>
          dsimp only
          rw [hSet, hPermEq]
          exact ⟨s.memory.borrows, rfl⟩
        | false =>
          dsimp only
          rw [hNoUB]
          dsimp only
          rw [hSet, hPermEq]
          exact ⟨_, rfl⟩

/-- **Direct bridge to unmodified `V2026_06_01.MirSemantics.evalNonFnEntryRetag`**: retagging a
non-uninhabited reference local outside `FnEntry` mints an unprotected child with permission
`miriPermToV2026 (retagKindToInitialPerms rk mutability (rigidTyIsFreeze 16 pointee) false).1`! -/
theorem v2026_evalNonFnEntryRetag_mints_unprotected_child
    (rk : RetagKind) (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (loc : Local) (ptrVal : ProvenancePtr) (sz : Nat)
    (parentEntry : BorrowEntry) (locals' locals'' : List LocalSlot)
    (mutability : Mutability) (pointee : RigidTy) (layoutIdx : LayoutIdx)
    (hTy : placeTy localDecls layouts { local_ := loc, projection := .nil } =
      .some { kind := .ref mutability pointee, layoutIdx := layoutIdx })
    (hInhab : rigidTyIsUninhabited 16 pointee = false)
    (hNoReadUB :
      retagPerm rk mutability pointee = .cell ∨
      rigidTyIsZeroSized 16 pointee = true ∨
      hasTreeReadUB s.memory.borrows s.memory.borrows s.memory.activeProtectors
        parentEntry.targetLocal (.some ptrVal.tag) parentEntry.targetProjection
        parentEntry.rangeOffset parentEntry.rangeLen parentEntry.targetFrameDepth = false)
    (hSet : set? locals' loc
      (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := ptrVal.offsetBytes } sz)) =
      .some locals'') :
    ∃ borrowsAfterRead : List BorrowEntry,
      evalNonFnEntryRetag rk s localDecls layouts { local_ := loc, projection := .nil }
        ptrVal sz parentEntry locals' =
      MirStepNode.step
        (advanceStmt s locals''
          { s.memory with
            borrows :=
              { tag := s.memory.nextTag
                targetLocal := parentEntry.targetLocal
                targetFrameDepth := parentEntry.targetFrameDepth
                allocDead := parentEntry.allocDead
                targetProjection := parentEntry.targetProjection
                perm := miriPermToV2026
                  (retagKindToInitialPerms rk mutability
                    (rigidTyIsFreeze 16 pointee) false).1
                rangeOffset := parentEntry.rangeOffset
                rangeLen := parentEntry.rangeLen
                protector := .none
                parentTag := .some ptrVal.tag } :: borrowsAfterRead
            nextTag := Nat.add s.memory.nextTag 1 }) := by
  unfold evalNonFnEntryRetag
  rw [hTy]
  dsimp only
  rw [hInhab]
  dsimp only
  have hPermEq :
      retagPerm rk mutability pointee =
        miriPermToV2026
          (retagKindToInitialPerms rk mutability (rigidTyIsFreeze 16 pointee) false).1 :=
    (retagKindToInitialPerms_eq_v2026_retagPerm rk mutability pointee).1.symm
  cases hNoReadUB with
  | inl hCell =>
    rw [hCell] at hPermEq ⊢
    dsimp only
    rw [hSet, hPermEq]
    exact ⟨s.memory.borrows, rfl⟩
  | inr hRest =>
    cases hRest with
    | inl hZst =>
      cases hP : retagPerm rk mutability pointee with
      | cell =>
        rw [hP] at hPermEq
        dsimp only
        rw [hSet, hPermEq]
        exact ⟨s.memory.borrows, rfl⟩
      | reservedFrz _ | reservedIM | unique | frozen | disabled =>
        rw [hP] at hPermEq
        dsimp only
        rw [hZst]
        dsimp only
        rw [hSet, hPermEq]
        exact ⟨s.memory.borrows, rfl⟩
    | inr hNoUB =>
      cases hP : retagPerm rk mutability pointee with
      | cell =>
        rw [hP] at hPermEq
        dsimp only
        rw [hSet, hPermEq]
        exact ⟨s.memory.borrows, rfl⟩
      | reservedFrz _ | reservedIM | unique | frozen | disabled =>
        rw [hP] at hPermEq
        dsimp only
        cases rigidTyIsZeroSized 16 pointee with
        | true =>
          dsimp only
          rw [hSet, hPermEq]
          exact ⟨s.memory.borrows, rfl⟩
        | false =>
          dsimp only
          rw [hNoUB]
          dsimp only
          rw [hSet, hPermEq]
          exact ⟨_, rfl⟩

/-! ## Part V. Concrete Positive & Fail-Closed Negative Witnesses on V2026 `Memory` (`#4185`) -/

/-- Live 16-byte mutable V2026 `Memory` fixture (`allocId = 1`, `mutability = .mut`). -/
def miriMem16Live : Memory :=
  { emptyMemory with
    nextAllocId := 2
    globals :=
      [{ allocId := 1
         bytes := List.replicate 16 (some 0x11)
         relocations := []
         align := { bytes := 4 }
         mutability := .mut }] }

/-- Live 16-byte read-only V2026 `Memory` fixture (`allocId = 1`, `mutability = .not`). -/
def miriMem16ReadOnly : Memory :=
  { emptyMemory with
    nextAllocId := 2
    globals :=
      [{ allocId := 1
         bytes := List.replicate 16 (some 0x11)
         relocations := []
         align := { bytes := 4 }
         mutability := .not }] }

/-- Dead 16-byte stack-allocation V2026 `Memory` fixture (`allocId = 1`, `allocDead = true`). -/
def miriMem16Dead : Memory :=
  { emptyMemory with
    nextAllocId := 2
    borrows :=
      [{ tag := 1
         targetLocal := 0
         targetProjection := []
         perm := .disabled
         allocDead := true }] }

/-- V2026 `Memory` fixture in which LIVE stack borrow tag `1` shares its number with READ-ONLY
global allocation `1` (V2026 numbers both from `1`; `lookupBorrow` wins). -/
def miriMem16ShadowedGlobal : Memory :=
  { miriMem16ReadOnly with
    borrows :=
      [{ tag := 1
         targetLocal := 0
         targetProjection := []
         perm := .unique }] }

/-- Initial single-root Tree Borrows state on `allocId = 1` (`[0, 16)`). -/
def miriTbRoot16 : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 1
         tree := [{ tag := 0, parent := none, children := [] }]
         segments :=
           [{ offset := 0
              size := 16
              entries := [{ tag := 0, loc := ⟨.unique, true, .none⟩ }] }] }] }

/-- Extracts the `MiriTbState` payload from a `MiriTbResult`. -/
def unwrapTb (r : MiriTbResult MiriTbState) : MiriTbState :=
  match r with
  | .ok st => st
  | .err st _ => st

/-- `miriTbRoot16` with an empty protector frame `1`. -/
def miriTbFrame1 : MiriTbState :=
  unwrapTb (miriBeginFrame miriTbRoot16 1)

/-- Computable 0-based list lookup returning `none` out of bounds. -/
def listNth? {α : Type} (xs : List α) (idx : Nat) : Option α :=
  (xs.foldl
    (fun (acc : Nat × Option α) x =>
      (acc.1 + 1, if Nat.beq acc.1 idx then some x else acc.2))
    (0, none)).2

/-- Looks up `(perm, accessed)` for `tag` in segment `segIdx` of `allocId`. -/
def lookupPermInSeg? (st : MiriTbState) (allocId : AllocId)
    (segIdx tag : Nat) : Option (MiriPerm × Bool) :=
  match miriFindAllocTree? allocId st.allocTrees with
  | none => none
  | some atree =>
    match listNth? atree.segments segIdx with
    | none => none
    | some seg =>
      match miriFindTagEntry? tag seg.entries with
      | none => none
      | some e => some (e.loc.perm, e.loc.accessed)

/-- Checks whether `r` failed with `.childAccessForbidden t p`. -/
def isChildForbiddenErr {α : Type} (t : Nat) (p : MiriPerm) (r : MiriTbResult α) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.childAccessForbidden et ep) => Nat.beq et t && miriPermEq ep p
  | .err _ _ => false

/-- Checks whether `r` failed with `.protectedDisabled t p`. -/
def isProtectedDisabledErr (t : Nat) (p : MiriPerm) (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.protectedDisabled et ep) => Nat.beq et t && miriPermEq ep p
  | .err _ _ => false

/-- Checks whether `r` failed with `.uncoveredRange aid`. -/
def isUncoveredErr (aid : AllocId) (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.uncoveredRange a) => Nat.beq a aid
  | .err _ _ => false

/-- Checks whether `r` failed with `.missingTag t`. -/
def isMissingTagErr {α : Type} (t : Nat) (r : MiriTbResult α) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.missingTag et) => Nat.beq et t
  | .err _ _ => false

/-- Checks whether `r` failed with `.writeToReadOnly aid`. -/
def isWriteToReadOnlyErr (aid : AllocId) (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.writeToReadOnly a) => Nat.beq a aid
  | .err _ _ => false

/-- Checks whether `r` failed with `.impossibleProtectedReservedIM t`. -/
def isImpossibleProtResIMErr (t : Nat) (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.impossibleProtectedReservedIM et) => Nat.beq et t
  | .err _ _ => false

/-- Checks whether `r` failed with `.duplicateTag t`. -/
def isDuplicateTagErr (t : Nat) (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.duplicateTag et) => Nat.beq et t
  | .err _ _ => false

/-- Checks whether `r` failed with `.missingFrame fid`. -/
def isMissingFrameErr (fid : Nat) (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.missingFrame ef) => Nat.beq ef fid
  | .err _ _ => false

/-- Checks whether `r` failed with `.deadOrMissingAlloc aid`. -/
def isDeadOrMissingAllocErr (aid : AllocId) (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.deadOrMissingAlloc ea) => Nat.beq ea aid
  | .err _ _ => false

/-- Checks whether `r` failed with `.duplicateFrame fid`. -/
def isDuplicateFrameErr (fid : Nat) (r : MiriTbResult MiriTbState) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.duplicateFrame ef) => Nat.beq ef fid
  | .err _ _ => false

/-- Checks whether `r` failed with `.multipleRoots t`. -/
def isMultipleRootsErr {α : Type} (t : Nat) (r : MiriTbResult α) : Bool :=
  match r with
  | .ok _ => false
  | .err _ (.multipleRoots et) => Nat.beq et t
  | .err _ _ => false

/-- **Positive Witness 1 (`[]`)**: valid two-phase mutable reborrow (`&mut [0, 8)` starting
`.reservedFrz false`) + activation by child write (`.reservedFrz false → .unique`) + disjoint shared
reborrow (`& [8, 16)`) + protector frame push (`miriBeginFrame`) and clean frame exit
(`miriExitCallFrame` leaving `frames = []`). -/
theorem witness_positive_twoPhase_activate_shared_frame_exit :
    (match miriBeginFrame miriTbRoot16 1 with
     | .err _ _ => false
     | .ok stF =>
       match miriRegisterFnEntryArg miriMem16Live stF 1 1 1 0 .mutable true false 0 8 with
       | .err _ _ => false
       | .ok stMut =>
         let isResBefore :=
           match lookupPermInSeg? stMut 1 0 1 with
           | some (p, acc) => miriPermEq p (.reservedFrz false) && acc
           | none => false
         match miriRegisterFnEntryArg miriMem16Live stMut 1 1 2 0 .shared true false 8 8 with
         | .err _ _ => false
         | .ok stBoth =>
           match miriPerformRangedAccess stBoth 1 1 0 8 .write .visitChildrenOfAccessed with
           | .err _ _ => false
           | .ok stAct =>
             let isUniqueAfter :=
               match lookupPermInSeg? stAct 1 0 1 with
               | some (p, acc) => miriPermEq p .unique && acc
               | none => false
             let isSharedIntact :=
               match lookupPermInSeg? stAct 1 1 2 with
               | some (p, acc) => miriPermEq p .frozen && acc
               | none => false
             match miriExitCallFrame miriMem16Live stAct 1 with
             | .err _ _ => false
             | .ok stEnd =>
               isResBefore && isUniqueAfter && isSharedIntact && stEnd.frames.isEmpty) = true :=
  rfl

/-- Two overlapping `FnEntry` arguments (`tag 1`: `&mut [0, 8)`, `tag 2`: `& [4, 12)`). -/
def miriReadOnlyAliasedEntry : MiriTbState :=
  let st0 := miriTbFrame1
  let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live st0 1 1 1 0 .mutable true false 0 8)
  unwrapTb (miriRegisterFnEntryArg miriMem16Live st1 1 1 2 0 .shared true false 4 8)

/-- **Positive & Two-Phase Conflict Witness (`[]`, Canary 1 + two-phase conflict UB)**:
1. Overlapping `& [4, 12)` marks protected `tag 1` (`ReservedFrz false`) as `ReservedFrz true`
   on `[4, 8)` while leaving `[0, 4)` unconflicted; read-only execution + clean exit succeed.
2. Attempting to ACTIVATE conflicted `tag 1` on `[4, 8)` while still protected in frame `1` traps
   with `.childAccessForbidden 1 (.reservedFrz true)`! -/
theorem witness_aliased_reservedFrz_readOnly_ok_vs_conflict_activation_ub :
    lookupPermInSeg? miriReadOnlyAliasedEntry 1 0 1 = some (.reservedFrz false, true) ∧
    lookupPermInSeg? miriReadOnlyAliasedEntry 1 1 1 = some (.reservedFrz true, true) ∧
    lookupPermInSeg? miriReadOnlyAliasedEntry 1 2 1 = some (.reservedFrz true, false) ∧
    (match miriPerformRangedAccess miriReadOnlyAliasedEntry 1 2 4 8 .read
        .visitChildrenOfAccessed with
     | .err _ _ => false
     | .ok stAfterRead =>
       match miriExitCallFrame miriMem16Live stAfterRead 1 with
       | .ok stEnd => stEnd.frames.isEmpty
       | .err _ _ => false) = true ∧
    isChildForbiddenErr 1 (.reservedFrz true)
      (miriPerformRangedAccess miriReadOnlyAliasedEntry 1 1 4 4 .write
        .visitChildrenOfAccessed) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Canary 2 (`[]`)**: protected `Unique` (`implicitWrites = true`) traps immediately on
overlapping second `FnEntry` retag with `.protectedDisabled 1 .unique`, while disjoint `Unique` +
`Frozen` succeeds through write and frame exit. -/
theorem witness_unique_reborrow_traps_vs_disjoint_ok :
    (let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live miriTbFrame1
       1 1 1 0 .mutable true true 0 8)
     let rShared := miriRegisterFnEntryArg miriMem16Live st1 1 1 2 0 .shared true false 4 8
     let rMut := miriRegisterFnEntryArg miriMem16Live st1 1 1 2 0 .mutable true false 4 8
     isProtectedDisabledErr 1 .unique rShared && isProtectedDisabledErr 1 .unique rMut) = true ∧
    (let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live miriTbFrame1
       1 1 1 0 .mutable true true 0 8)
     match miriRegisterFnEntryArg miriMem16Live st1 1 1 2 0 .shared true false 8 8 with
     | .err _ _ => false
     | .ok st2 =>
       match miriPerformRangedAccess st2 1 1 0 8 .write .visitChildrenOfAccessed with
       | .err _ _ => false
       | .ok stW =>
         match miriExitCallFrame miriMem16Live stW 1 with
         | .ok stEnd => stEnd.frames.isEmpty
         | .err _ _ => false) = true :=
  ⟨rfl, rfl⟩

/-- **Canary 3 (`[]`)**: unaccessed outside-range protected `ReservedFrz false` lazily disables on
foreign write without UB, while accessed inside-range traps with
`.protectedDisabled 1 (.reservedFrz false)`. -/
theorem witness_outside_unaccessed_lazy_disable_vs_inside_traps :
    (let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live miriTbFrame1
       1 1 1 0 .mutable true false 0 8)
     match miriPerformRangedAccess st1 1 0 8 8 .write .visitChildrenOfAccessed with
     | .err _ _ => false
     | .ok stOut =>
       match lookupPermInSeg? stOut 1 1 1 with
       | some (p, acc) => miriPermIsDisabled p && !acc
       | none => false) = true ∧
    (let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live miriTbFrame1
       1 1 1 0 .mutable true false 0 8)
     isProtectedDisabledErr 1 (.reservedFrz false)
       (miriPerformRangedAccess st1 1 0 0 8 .write .visitChildrenOfAccessed)) = true :=
  ⟨rfl, rfl⟩

/-- Three-node chain `0 -> 1 -> 2` fixture for SIFA subtree pruning. -/
def sifaGrandchildTree : List MiriTopoNode :=
  [{ tag := 0, parent := none, children := [1] },
   { tag := 1, parent := some 0, children := [2] },
   { tag := 2, parent := some 1, children := [] }]

def sifaGrandchildSeg : MiriSegment :=
  { offset := 0
    size := 8
    entries :=
      [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
       { tag := 1, loc := ⟨.reservedIM, false, .write⟩ },
       { tag := 2, loc := ⟨.frozen, true, .read⟩ }] }

def localBeforeForeignTree : List MiriTopoNode :=
  [{ tag := 0, parent := none, children := [1, 3] },
   { tag := 1, parent := some 0, children := [2] },
   { tag := 2, parent := some 1, children := [] },
   { tag := 3, parent := some 0, children := [] }]

def localBeforeForeignSeg : MiriSegment :=
  { offset := 0
    size := 8
    entries :=
      [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
       { tag := 1, loc := ⟨.frozen, true, .read⟩ },
       { tag := 2, loc := ⟨.unique, true, .none⟩ },
       { tag := 3, loc := ⟨.unique, true, .none⟩ }] }

/-- **Canary 4 (`[]`)**: SIFA subtree pruning, `.skipChildrenOfAccessed` during frame exit,
ancestor SIFA weakening with `min(inside, outside)`, and local-before-foreign error precedence. -/
theorem witness_sifa_pruning_skipChildren_and_local_precedence :
    miriSkippedForeignNodes sifaGrandchildSeg .write = [1] ∧
    (miriTraverseSegmentEvents sifaGrandchildTree sifaGrandchildSeg 0 .write
      .visitChildrenOfAccessed) = [{ tag := 0, rel := .localAccess }] ∧
    (match miriPerformSegmentAccess sifaGrandchildTree [2] 0 .write
        .visitChildrenOfAccessed sifaGrandchildSeg with
     | .ok _ => true
     | .err _ _ => false) = true ∧
    (let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live miriTbFrame1
       1 1 1 0 .mutable true true 0 8)
     match miriReborrowTag miriMem16Live st1 none 1 2 1 .unique .reservedIM 0 8 with
     | .err _ _ => false
     | .ok st2 =>
       match miriExitCallFrame miriMem16Live st2 1 with
       | .err _ _ => false
       | .ok st3 =>
         match miriPerformRangedAccess st3 1 2 0 8 .write .visitChildrenOfAccessed with
         | .ok _ => true
         | .err _ _ => false) = true ∧
    (match miriReborrowTag miriMem16Live miriTbRoot16 none 1 1 0 .reservedIM .reservedIM 0 16 with
     | .err _ _ => false
     | .ok st1 =>
       match miriReborrowTag miriMem16Live st1 none 1 2 1 .cell .frozen 0 8 with
       | .err _ _ => false
       | .ok st2 =>
         match miriPerformRangedAccess st2 1 0 8 8 .write .visitChildrenOfAccessed with
         | .err _ _ => false
         | .ok st3 =>
           isChildForbiddenErr 2 .disabled
             (miriPerformRangedAccess st3 1 2 8 8 .read .visitChildrenOfAccessed)) = true ∧
    isChildForbiddenErr 1 .frozen
      (miriPerformSegmentAccess localBeforeForeignTree [3] 2 .write
        .visitChildrenOfAccessed localBeforeForeignSeg) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Canary 5 (`[]`)**: unprotected `.reservedIM` survives foreign write, protected `.reservedIM`
fails closed, and protected `.cell` overlapping protected `.unique` emits no associated access. -/
theorem witness_reservedIM_and_cell_protector_semantics :
    (match miriReborrowTag miriMem16Live miriTbRoot16 none 1 1 0 .reservedIM .reservedIM 0 8 with
     | .err _ _ => false
     | .ok st1 =>
       match miriPerformRangedAccess st1 1 0 0 8 .write .visitChildrenOfAccessed with
       | .err _ _ => false
       | .ok stW =>
         match lookupPermInSeg? stW 1 0 1 with
         | some (p, acc) => miriPermEq p .reservedIM && acc
         | none => false) = true ∧
    isImpossibleProtResIMErr 1
      (miriReborrowTag miriMem16Live miriTbFrame1 (some 1) 1 1 0 .reservedIM .reservedIM 0 8) =
      true ∧
    (let st1 := unwrapTb (miriRegisterFnEntryArg miriMem16Live miriTbFrame1
       1 1 1 0 .shared false false 0 8)
     match miriPerformRangedAccess st1 1 1 0 8 .write .visitChildrenOfAccessed with
     | .err _ _ => false
     | .ok stCellAcc =>
       match miriRegisterFnEntryArg miriMem16Live stCellAcc 1 1 2 0 .mutable true true 0 8 with
       | .err _ _ => false
       | .ok stBoth =>
         match lookupPermInSeg? stBoth 1 0 1, lookupPermInSeg? stBoth 1 0 2 with
         | some (p1, a1), some (p2, a2) =>
           miriPermEq p1 .cell && a1 && miriPermEq p2 .unique && a2 &&
             match miriExitCallFrame miriMem16Live stBoth 1 with
             | .ok stEnd => stEnd.frames.isEmpty
             | .err _ _ => false
         | _, _ => false) = true :=
  ⟨rfl, rfl, rfl⟩

/-- Synthetic conflict fixture separating forward vs. reverse release order. -/
def syntheticConflictState : MiriTbState :=
  { frames := [{ frameId := 1, protectedTags := [(1, 1), (1, 2)] }]
    allocTrees :=
      [{ allocId := 1
         tree :=
           [{ tag := 0, parent := none, children := [1, 2] },
            { tag := 1, parent := some 0, children := [] },
            { tag := 2, parent := some 0, children := [] }]
         segments :=
           [{ offset := 0
              size := 8
              entries :=
                [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
                 { tag := 1, loc := ⟨.unique, true, .none⟩ },
                 { tag := 2, loc := ⟨.frozen, true, .read⟩ }] }] }] }

def danglingParentState : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 1
         tree :=
           [{ tag := 0, parent := none, children := [1] },
            { tag := 1, parent := some 99, children := [] }]
         segments :=
           [{ offset := 0
              size := 8
              entries :=
                [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
                 { tag := 1, loc := ⟨.unique, true, .none⟩ }] }] }] }

def gappedSegState : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 1
         tree := [{ tag := 0, parent := none, children := [] }]
         segments :=
           [{ offset := 0
              size := 4
              entries := [{ tag := 0, loc := ⟨.unique, true, .none⟩ }] }] }] }

def twoRootState : MiriTbState :=
  { frames := []
    allocTrees :=
      [{ allocId := 1
         tree :=
           [{ tag := 0, parent := none, children := [] },
            { tag := 5, parent := none, children := [] }]
         segments :=
           [{ offset := 0
              size := 8
              entries :=
                [{ tag := 0, loc := ⟨.unique, true, .none⟩ },
                 { tag := 5, loc := ⟨.unique, true, .none⟩ }] }] }] }

/-- **Allocation-classification regression witness (`[]`)**: `miriInspectAllocV2026` follows V2026's
`lookupBorrow`-first precedence — a live stack borrow shadows a same-numbered read-only global
(`.live .mut`), so a protected `&mut` (`Unique`) `FnEntry` reborrow through it SUCCEEDS, while the
un-shadowed read-only global still rejects the identical reborrow with `.writeToReadOnly 1`; dead
borrows are `.dead` (and V2026 bounds them to `0`) and empty memory is `.missing`. -/
theorem witness_inspectAlloc_borrow_precedence :
    miriInspectAllocV2026 1 miriMem16ShadowedGlobal = .live .mut ∧
    miriInspectAllocV2026 1 miriMem16ReadOnly = .live .not ∧
    miriInspectAllocV2026 1 miriMem16Live = .live .mut ∧
    miriInspectAllocV2026 1 miriMem16Dead = .dead ∧
    miriInspectAllocV2026 1 emptyMemory = .missing ∧
    (match miriRegisterFnEntryArg miriMem16ShadowedGlobal miriTbFrame1 1 1 1 0 .mutable true true
        0 8 with
     | .ok stOk => miriProtectedTagsOnAlloc 1 stOk.frames == [1]
     | .err _ _ => false) = true ∧
    isWriteToReadOnlyErr 1
      (miriRegisterFnEntryArg miriMem16ReadOnly miriTbFrame1 1 1 1 0 .mutable true true 0 8) =
      true ∧
    ptrAllocByteBound? [] miriMem16Dead [] emptyLayoutTable { allocId := 1, offsetBytes := 0 } =
      .some 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   miriInspectAllocV2026_dead_eq_v2026_ptrAllocByteBound_zero [] miriMem16Dead [] emptyLayoutTable
     { allocId := 1, offsetBytes := 0 } rfl⟩

/-- **Comprehensive Fail-Closed Negative UB Regression Suite (`[]`)**:
exercises genuine `.err ...` outcomes from satisfiable V2026 states for every failure mode:
1. Retag write-to-read-only (`.writeToReadOnly 1`);
2. Frozen local write UB (`.childAccessForbidden 2 .frozen`);
3. Protected foreign-write UB (`.protectedDisabled 1 .unique` & forward/reverse release separation);
4. Dead & missing allocation rejection (`.deadOrMissingAlloc 1`, `.deadOrMissingAlloc 99`);
5. Duplicate tag rejection (`.duplicateTag 0`);
6. Missing protector frame rejection on retag & exit (`.missingFrame 99`) and duplicate frame
   rejection (`.duplicateFrame 1`);
7. Two-phase conflict activation UB with pre-error SIFA reset to `.none`;
8. Non-initial permission, lazy `.unique`, dangling parent, uncovered range, dead-alloc exit skip
   vs. missing-alloc exit error, protector retention on failed reborrow, and multi-root rejection. -/
theorem witness_negative_fail_closed_ub_suite :
    isWriteToReadOnlyErr 1
      (miriRegisterFnEntryArg miriMem16ReadOnly miriTbFrame1 1 1 1 0 .mutable true true 0 8) =
      true ∧
    isChildForbiddenErr 2 .frozen
      (miriPerformRangedAccess miriReadOnlyAliasedEntry 1 2 4 8 .write
        .visitChildrenOfAccessed) = true ∧
    isProtectedDisabledErr 2 .frozen
      (miriReleaseTagListForward miriMem16Live syntheticConflictState [(1, 1), (1, 2)]) = true ∧
    isProtectedDisabledErr 1 .unique
      (miriReleaseTagListReverse miriMem16Live syntheticConflictState [(1, 1), (1, 2)]) = true ∧
    isDeadOrMissingAllocErr 1
      (miriReborrowTag miriMem16Dead miriTbRoot16 none 1 1 0 .frozen .frozen 0 8) = true ∧
    isDeadOrMissingAllocErr 99
      (miriReborrowTag miriMem16Live miriTbRoot16 none 99 1 0 .frozen .frozen 0 8) = true ∧
    isDuplicateTagErr 0
      (miriReborrowTag miriMem16Live miriTbRoot16 none 1 0 0 .frozen .frozen 0 8) = true ∧
    isMissingFrameErr 99
      (miriRegisterFnEntryArg miriMem16Live miriTbRoot16 99 1 1 0 .mutable true true 0 8) = true ∧
    isMissingFrameErr 99
      (miriExitCallFrame miriMem16Live miriTbRoot16 99) = true ∧
    isDuplicateFrameErr 1 (miriBeginFrame miriTbFrame1 1) = true ∧
    miriPerformLocAccess 7 ⟨.reservedFrz true, true, .read⟩ .write .localAccess true =
      .err ⟨.reservedFrz true, true, .none⟩ (.childAccessForbidden 7 (.reservedFrz true)) ∧
    miriInitialInsideLoc 5 .disabled true = .error (.nonInitialPerm 5 .disabled) ∧
    miriInitialInsideLoc 5 (.reservedFrz true) false =
      .error (.nonInitialPerm 5 (.reservedFrz true)) ∧
    miriNewNonAccessed 5 .unique .none = .error (.invalidLazyState 5) ∧
    isMissingTagErr 99
      (miriPerformRangedAccess danglingParentState 1 1 0 8 .read .visitChildrenOfAccessed) = true ∧
    isUncoveredErr 1
      (miriPerformRangedAccess gappedSegState 1 0 0 8 .read .visitChildrenOfAccessed) = true ∧
    (match miriExitCallFrame miriMem16Dead syntheticConflictState 1 with
     | .ok stEnd => stEnd.frames.isEmpty
     | .err _ _ => false) = true ∧
    isDeadOrMissingAllocErr 1
      (miriExitCallFrame emptyMemory syntheticConflictState 1) = true ∧
    miriProtectedTagsOnAlloc 1
      (unwrapTb (miriReborrowTag miriMem16Dead miriTbFrame1 (some 1) 1 1 0
        .frozen .frozen 0 8)).frames = [1] ∧
    isMultipleRootsErr 0
      (miriPerformRangedAccess twoRootState 1 0 0 8 .write .visitChildrenOfAccessed) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.MiriTreeBorrowsV2026
