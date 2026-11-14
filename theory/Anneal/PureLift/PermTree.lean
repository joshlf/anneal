-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Anneal.PureLift.Lens

namespace Anneal.PureLift

/-!
# First-Order Sub-Place Permission Trie (`PermTree`)

Tracks fine-grained read and write permissions across aggregate sub-places
using `List.foldr` (`listFold`), allowing fast, unbounded `whnf` reduction
inside the Lean 4 kernel without `noncomputable` declarations or compiler-only
`_unsafe_rec` definitions.

Key design invariants:
- `.shared (loans : List LoanId)` records the deduplicated list of active
  shared loan identifiers rather than an anonymous reference count. Releasing a
  loan by ID never accidentally unlocks a sibling or overlapping shared borrow,
  and makes permission release path-free across the entire `PermTree`.
- `.mutLocked (loan : LoanId)` records a single active mutable borrow, while
  `.mutJoined (mutLoans : List LoanId) (sharedLoans : List LoanId)` records
  multiple distinct loans merged across control-flow branches so that branch
  joins never drop active loans from either arm.
- `.split (entries : List (SubPath × SubPerm))` represents an aggregate with
  sub-place permissions scoped to their exact `SubPath`. Whenever all sub-place
  entries are released, `fromEntries` normalizes `.split` back to `.unborrowed`
  (or to a root permission when only path `[]` remains).
-/

/-- Borrow flavor requested when acquiring a sub-place loan. -/
inductive BorrowKind where
  | shared
  | mutBorrow

/-- Leaf permission state at a borrowed sub-place path. -/
inductive SubPerm where
  | shared (loans : List LoanId) : SubPerm
  | mutLocked (loan : LoanId) : SubPerm
  | mutJoined (mutLoans : List LoanId) (sharedLoans : List LoanId) : SubPerm

/-- First-order sub-place permission trie for an aggregate value cell. -/
inductive PermTree where
  | unborrowed : PermTree
  | shared (loans : List LoanId) : PermTree
  | mutLocked (loan : LoanId) : PermTree
  | mutJoined (mutLoans : List LoanId) (sharedLoans : List LoanId) : PermTree
  | split (entries : List (SubPath × SubPerm)) : PermTree

/-- True iff `lid` occurs in `xs`. -/
def elemLoanId (lid : LoanId) (xs : List LoanId) : Bool :=
  xs.foldr (fun x ih => x == lid || ih) false

/-- Canonicalize `xs` as a deduplicated list of loan identifiers. -/
def dedupLoanIds (xs : List LoanId) : List LoanId :=
  match xs with
  | [] => []
  | [x] => [x]
  | _ :: _ =>
    xs.foldr (fun x ih => if elemLoanId x ih then ih else x :: ih) []

/-- Merge two lists of loan identifiers without duplicates. -/
def mergeLoanIds (xs ys : List LoanId) : List LoanId :=
  xs.foldr (fun x ih => if elemLoanId x ih then ih else x :: ih)
    (dedupLoanIds ys)

/-- Remove all occurrences of `lid` from a list of loan identifiers. -/
def removeLoanId (lid : LoanId) (xs : List LoanId) : List LoanId :=
  xs.foldr (fun x ih => if x == lid then ih else x :: ih) []

/-- Replace `oldLid` with `newLid` in `xs`, deduplicating the result. -/
def replaceLoanId (oldLid newLid : LoanId) (xs : List LoanId) : List LoanId :=
  dedupLoanIds
    (xs.foldr (fun x ih => (if x == oldLid then newLid else x) :: ih) [])

/-- Structural equality on lists of loan identifiers. -/
def loanIdListEq (xs ys : List LoanId) : Bool :=
  xs.foldr
    (fun a ih bs =>
      match bs with
      | [] => false
      | b :: bs' => a == b && ih bs')
    (fun bs =>
      match bs with
      | [] => true
      | _ :: _ => false)
    ys

/-- Structural equality on `SubPath` lists. -/
abbrev subPathEq (p1 p2 : SubPath) : Bool :=
  loanIdListEq p1 p2

/-- True iff `p1` is a prefix of `p2`. -/
def subPathPrefix (p1 p2 : SubPath) : Bool :=
  p1.foldr
    (fun x ih ys =>
      match ys with
      | [] => false
      | y :: ys' => if x == y then ih ys' else false)
    (fun _ => true)
    p2

/-- Strip prefix `pref` from `full`, returning `some relSuffix` when `pref` is a
prefix of `full`. -/
def stripSubPathPrefix (pref full : SubPath) : Option SubPath :=
  pref.foldr
    (fun x ih ys =>
      match ys with
      | [] => none
      | y :: ys' => if x == y then ih ys' else none)
    (fun ys => some ys)
    full

/-- True iff `p1` and `p2` overlap (one is a prefix of the other). -/
def subPathOverlaps (p1 p2 : SubPath) : Bool :=
  subPathPrefix p1 p2 || subPathPrefix p2 p1

/-- Normalize a `SubPerm` from its active mutable and shared loan lists,
returning `none` when both lists are empty. -/
def mkSubPermOpt (mutLoans : List LoanId) (sharedLoans : List LoanId) :
    Option SubPerm :=
  let m := dedupLoanIds mutLoans
  let s := dedupLoanIds sharedLoans
  match m, s with
  | [], [] => none
  | [], _ :: _ => some (.shared s)
  | [lid], [] => some (.mutLocked lid)
  | _, _ => some (.mutJoined m s)

/-- Normalize a `SubPerm`, deduplicating its loan IDs and returning `none` when
it holds no active loans (such as `.shared []` or `.mutJoined [] []`). -/
def normalizeSubPerm (sp : SubPerm) : Option SubPerm :=
  match sp with
  | .shared ls => mkSubPermOpt [] ls
  | .mutLocked l => some (.mutLocked l)
  | .mutJoined m s => mkSubPermOpt m s

/-- Merge two `SubPerm` states at the same sub-place path. -/
def unionSubPerm (sp1 sp2 : SubPerm) : SubPerm :=
  let (m1, s1) : List LoanId × List LoanId :=
    match sp1 with
    | .shared ls => ([], ls)
    | .mutLocked l => ([l], [])
    | .mutJoined m s => (m, s)
  let (m2, s2) : List LoanId × List LoanId :=
    match sp2 with
    | .shared ls => ([], ls)
    | .mutLocked l => ([l], [])
    | .mutJoined m s => (m, s)
  match mkSubPermOpt (mergeLoanIds m1 m2) (mergeLoanIds s1 s2) with
  | some sp => sp
  | none => sp1

/-- Insert or merge `(path, sp)` into a list of `(SubPath × SubPerm)` entries,
ignoring `sp` if `normalizeSubPerm sp` is `none`. -/
def insertSubPermEntry (path : SubPath) (sp : SubPerm)
    (entries : List (SubPath × SubPerm)) : List (SubPath × SubPerm) :=
  match normalizeSubPerm sp with
  | none => entries
  | some spNorm =>
    match
      entries.foldr
        (fun entry (acc : Bool × List (SubPath × SubPerm)) =>
          match acc with
          | (found, rest) =>
            if subPathEq entry.1 path then
              match unionSubPerm entry.2 spNorm with
              | .shared ls => (true, (entry.1, .shared ls) :: rest)
              | .mutLocked l => (true, (entry.1, .mutLocked l) :: rest)
              | .mutJoined m s => (true, (entry.1, .mutJoined m s) :: rest)
            else
              (found, entry :: rest))
        (false, [])
    with
    | (true, updated) => updated
    | (false, updated) => updated ++ [(path, spNorm)]

/-- Extract the normalized `(SubPath × SubPerm)` entry list of a `PermTree`,
filtering out any degenerate empty `.shared []` or `.mutJoined [] []` entries
even inside hand-constructed `.split` trees. -/
def toEntries : PermTree → List (SubPath × SubPerm)
  | .unborrowed => []
  | .shared [] => []
  | .shared (l :: ls) => [([], .shared (l :: ls))]
  | .mutLocked lid => [([], .mutLocked lid)]
  | .mutJoined [] [] => []
  | .mutJoined [] (l :: ls) => [([], .shared (l :: ls))]
  | .mutJoined [lid] [] => [([], .mutLocked lid)]
  | .mutJoined m s => [([], .mutJoined m s)]
  | .split entries =>
    entries.foldr
      (fun entry ih =>
        match entry with
        | (_, .shared []) => ih
        | (_, .mutJoined [] []) => ih
        | (p, .mutJoined [] (s :: ss)) => (p, .shared (s :: ss)) :: ih
        | (p, .mutJoined [m] []) => (p, .mutLocked m) :: ih
        | (p, sp) => (p, sp) :: ih)
      []

/-- Collapse a normalized list of `(SubPath × SubPerm)` entries into a canonical
`PermTree`. -/
def fromCleanEntries (entries : List (SubPath × SubPerm)) : PermTree :=
  match entries with
  | [] => .unborrowed
  | [([], SubPerm.shared ls)] => .shared ls
  | [([], SubPerm.mutLocked lid)] => .mutLocked lid
  | [([], SubPerm.mutJoined m s)] => .mutJoined m s
  | _ => .split entries

/-- Normalize a list of `(SubPath × SubPerm)` entries into a canonical
`PermTree`. -/
def fromEntries (entries : List (SubPath × SubPerm)) : PermTree :=
  fromCleanEntries
    (entries.foldr
      (fun entry acc => insertSubPermEntry entry.1 entry.2 acc)
      [])

/-- Normalize a leaf permission from its active mutable and shared loan sets. -/
def mkLeafPerm (mutLoans : List LoanId) (sharedLoans : List LoanId) :
    PermTree :=
  match mkSubPermOpt mutLoans sharedLoans with
  | none => .unborrowed
  | some (.shared s) => .shared s
  | some (.mutLocked lid) => .mutLocked lid
  | some (.mutJoined m s) => .mutJoined m s

/-- True iff `sp` permits read access (i.e., holds no active mutable loan). -/
def subPermCanRead : SubPerm → Bool
  | .shared _ => true
  | .mutLocked _ => false
  | .mutJoined m _ => m.isEmpty

/-- True iff no active shared or mutable loans lock any part of the tree. -/
def isUnborrowed (t : PermTree) : Bool :=
  (toEntries t).isEmpty

/-- True iff every sub-place of the tree permits read access (i.e., no sub-place
has an active mutable lock). -/
def canReadTree (t : PermTree) : Bool :=
  (toEntries t).foldr (fun entry ih => subPermCanRead entry.2 && ih) true

/-- Project the permission subtree at nested `SubPath`. -/
def getPathPerm (path : SubPath) (t : PermTree) : PermTree :=
  match path with
  | [] => fromCleanEntries (toEntries t)
  | _ :: _ =>
    fromCleanEntries
      ((toEntries t).foldr
        (fun entry ih =>
          if subPathPrefix entry.1 path then
            insertSubPermEntry [] entry.2 ih
          else
            match stripSubPathPrefix path entry.1 with
            | some relSuffix => insertSubPermEntry relSuffix entry.2 ih
            | none => ih)
        [])

/-- Project the permission subtree for immediate field `f` from an aggregate
`PermTree`. -/
def getChildPerm (f : FieldIdx) (t : PermTree) : PermTree :=
  getPathPerm [f] t

/-- Update the permission subtree for field `f`. -/
def setChildPerm (f : FieldIdx) (newChild : PermTree) (t : PermTree) :
    PermTree :=
  let kept :=
    (toEntries t).foldr
      (fun entry ih =>
        match entry.1 with
        | f' :: _ => if f' == f then ih else entry :: ih
        | [] => entry :: ih)
      []
  let childShifted :=
    (toEntries newChild).foldr
      (fun entry ih => (f :: entry.1, entry.2) :: ih)
      []
  fromCleanEntries (kept ++ childShifted)

/-- Check whether `SubPath` can be read under `PermTree`. -/
def canReadPath (path : SubPath) (t : PermTree) : Bool :=
  (toEntries t).foldr
    (fun entry ih =>
      if subPathOverlaps entry.1 path then
        subPermCanRead entry.2 && ih
      else
        ih)
    true

/-- Check whether `SubPath` can be mutably written or mutably borrowed under
`PermTree`. -/
def canWritePath (path : SubPath) (t : PermTree) : Bool :=
  (toEntries t).foldr
    (fun entry ih =>
      if subPathOverlaps entry.1 path then false else ih)
    true

/-- Acquire permission of `kind` for loan `lid` at `SubPath`, returning `none`
if an incompatible borrow already locks an ancestor, target, or descendant
sub-place. -/
def acquirePerm (kind : BorrowKind) (lid : LoanId)
    (path : SubPath) (t : PermTree) : Option PermTree :=
  match kind with
  | .shared =>
    if canReadPath path t then
      some
        (fromCleanEntries
          (insertSubPermEntry path (.shared [lid]) (toEntries t)))
    else
      none
  | .mutBorrow =>
    if canWritePath path t then
      some
        (fromCleanEntries
          (insertSubPermEntry path (.mutLocked lid) (toEntries t)))
    else
      none

/-- Release all locks held by `lid` anywhere in `PermTree`, normalizing empty
`.shared`, `.mutJoined`, and `.split` nodes back to `.unborrowed`. -/
def releaseLoanPerm (lid : LoanId) (t : PermTree) : PermTree :=
  fromCleanEntries
    ((toEntries t).foldr
      (fun entry ih =>
        let spOpt : Option SubPerm :=
          match entry.2 with
          | .shared ls => mkSubPermOpt [] (removeLoanId lid ls)
          | .mutLocked l =>
            if l == lid then none else some (.mutLocked l)
          | .mutJoined m s =>
            mkSubPermOpt (removeLoanId lid m) (removeLoanId lid s)
        match spOpt with
        | some sp' => (entry.1, sp') :: ih
        | none => ih)
      [])

/-- Rename loan identifier `oldLid` to `newLid` throughout `PermTree`. -/
def renameLoanPerm (oldLid newLid : LoanId) (t : PermTree) : PermTree :=
  fromCleanEntries
    ((toEntries t).foldr
      (fun entry ih =>
        let spOpt : Option SubPerm :=
          match entry.2 with
          | .shared ls => mkSubPermOpt [] (replaceLoanId oldLid newLid ls)
          | .mutLocked l =>
            some (.mutLocked (if l == oldLid then newLid else l))
          | .mutJoined m s =>
            mkSubPermOpt
              (replaceLoanId oldLid newLid m)
              (replaceLoanId oldLid newLid s)
        match spOpt with
        | some sp' => (entry.1, sp') :: ih
        | none => ih)
      [])

/-- Conservative permission join across two control-flow branches, preserving
all active shared and mutable loans from both branches without duplication. -/
def unionPerm (t1 t2 : PermTree) : PermTree :=
  fromCleanEntries
    ((toEntries t2).foldr
      (fun entry acc => insertSubPermEntry entry.1 entry.2 acc)
      (toEntries t1))

/-- True iff `PermTree` records `lid` as an active mutable loan at `path`. -/
def hasMutLoanAtPath (lid : LoanId) (path : SubPath) (t : PermTree) : Bool :=
  (toEntries t).foldr
    (fun entry ih =>
      let here : Bool :=
        if subPathEq entry.1 path then
          match entry.2 with
          | .shared _ => false
          | .mutLocked l => l == lid
          | .mutJoined m _ => elemLoanId lid m
        else
          false
      here || ih)
    false

/-- True iff `PermTree` records `lid` as an active shared loan at `path`. -/
def hasSharedLoanAtPath (lid : LoanId) (path : SubPath) (t : PermTree) :
    Bool :=
  (toEntries t).foldr
    (fun entry ih =>
      let here : Bool :=
        if subPathEq entry.1 path then
          match entry.2 with
          | .shared s => elemLoanId lid s
          | .mutLocked _ => false
          | .mutJoined _ s => elemLoanId lid s
        else
          false
      here || ih)
    false

/-- Release loan identifier `lid` only from the entry at `targetPath` in `t`,
leaving other disjoint sub-paths in `t` untouched so multi-leaf writebacks to
the same owner validate and release each leaf path independently. -/
def releaseLoanPermAtPath (lid : LoanId) (targetPath : SubPath)
    (t : PermTree) : PermTree :=
  fromCleanEntries
    ((toEntries t).foldr
      (fun entry ih =>
        if !subPathEq entry.1 targetPath then
          entry :: ih
        else
          let spOpt : Option SubPerm :=
            match entry.2 with
            | .shared ls => mkSubPermOpt [] (removeLoanId lid ls)
            | .mutLocked l =>
              if l == lid then none else some (.mutLocked l)
            | .mutJoined m s =>
              mkSubPermOpt (removeLoanId lid m) (removeLoanId lid s)
          match spOpt with
          | some sp' => (entry.1, sp') :: ih
          | none => ih)
      [])

theorem isUnborrowed_unborrowed : isUnborrowed .unborrowed = true := rfl

theorem canReadPath_unborrowed (path : SubPath) :
    canReadPath path .unborrowed = true := rfl

theorem canWritePath_unborrowed (path : SubPath) :
    canWritePath path .unborrowed = true := rfl

theorem releaseLoanPerm_unborrowed (lid : LoanId) :
    releaseLoanPerm lid .unborrowed = .unborrowed := rfl

theorem acquire_release_root_mut (lid : LoanId) :
    acquirePerm .mutBorrow lid [] .unborrowed = some (.mutLocked lid) := rfl

/-!
## Exhaustive Kernel-Checked Tests for `PermTree`
-/

/-- 10-level nested `PermTree` with `subPerm` at path
`[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]`. -/
def deepPermTree10 (subPerm : SubPerm) : PermTree :=
  .split [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0], subPerm)]

/-- Traversal beyond depth 8 detects deep `.mutLocked` and `.shared` leaves,
blocking conflicting root borrows while permitting disjoint sibling borrows. -/
theorem permTree_deep_traversal_exhaustive :
    let deepMut := deepPermTree10 (.mutLocked 7)
    let deepSh := deepPermTree10 (.shared [7])
    let path10 : SubPath := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    isUnborrowed deepMut = false ∧
    canReadTree deepMut = false ∧
    acquirePerm .mutBorrow 8 [] deepMut = none ∧
    acquirePerm .shared 8 [] deepMut = none ∧
    canReadPath path10 deepMut = false ∧
    canWritePath path10 deepMut = false ∧
    canWritePath [1] deepMut = true ∧
    isUnborrowed deepSh = false ∧
    canReadTree deepSh = true ∧
    acquirePerm .mutBorrow 8 [] deepSh = none ∧
    releaseLoanPerm 7 deepMut = .unborrowed ∧
    releaseLoanPerm 7 deepSh = .unborrowed :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Joining two different mutable loans `.mutLocked 1` and `.mutLocked 2`
preserves both loans: releasing only one keeps the place locked, and releasing
both in either order restores `.unborrowed`. -/
theorem unionPerm_preserves_both_mut_loans :
    let joined := unionPerm (.mutLocked 1) (.mutLocked 2)
    isUnborrowed joined = false ∧
    canReadTree joined = false ∧
    releaseLoanPerm 1 joined = .mutLocked 2 ∧
    releaseLoanPerm 2 joined = .mutLocked 1 ∧
    isUnborrowed (releaseLoanPerm 1 joined) = false ∧
    canReadTree (releaseLoanPerm 1 joined) = false ∧
    releaseLoanPerm 2 (releaseLoanPerm 1 joined) = .unborrowed ∧
    releaseLoanPerm 1 (releaseLoanPerm 2 joined) = .unborrowed :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Joining `.mutLocked 1` with `.shared [2]` preserves both locks: releasing
the mutable loan `1` downgrades the place to `.shared [2]` (readable, not
writable), whereas releasing the shared loan `2` first leaves `.mutLocked 1`. -/
theorem unionPerm_preserves_mut_and_shared_loans :
    let joined := unionPerm (.mutLocked 1) (.shared [2])
    let joinedSym := unionPerm (.shared [2]) (.mutLocked 1)
    joined = joinedSym ∧
    canReadTree joined = false ∧
    isUnborrowed joined = false ∧
    releaseLoanPerm 1 joined = .shared [2] ∧
    canReadTree (releaseLoanPerm 1 joined) = true ∧
    isUnborrowed (releaseLoanPerm 1 joined) = false ∧
    releaseLoanPerm 2 joined = .mutLocked 1 ∧
    releaseLoanPerm 2 (releaseLoanPerm 1 joined) = .unborrowed ∧
    releaseLoanPerm 1 (releaseLoanPerm 2 joined) = .unborrowed :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Acquiring a descendant shared loan at `[0]` under an already-shared root
`.shared [1]` scopes loan `2` to `[0]`: releasing ancestor loan `1` unlocks the
disjoint sibling `[1]` for mutable access while keeping `[0]` shared-locked by
loan `2`. Releasing loan `2` first collapses the split back to `.shared [1]`. -/
theorem acquirePerm_descendant_shared_scoped :
    match acquirePerm .shared 2 [0] (.shared [1]) with
    | some tBoth =>
      let after1 := releaseLoanPerm 1 tBoth
      let after2 := releaseLoanPerm 2 tBoth
      canWritePath [1] after1 = true ∧
      canWritePath [0] after1 = false ∧
      canReadPath [0] after1 = true ∧
      releaseLoanPerm 2 after1 = .unborrowed ∧
      after2 = .shared [1] ∧
      releaseLoanPerm 1 after2 = .unborrowed
    | none => False :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Shared-permission joins are idempotent and deduplicate overlapping loan ID
lists. -/
theorem unionPerm_shared_idempotent :
    unionPerm (.shared [1]) (.shared [1]) = .shared [1] ∧
    unionPerm (.shared [1, 2]) (.shared [2, 3]) = .shared [1, 2, 3] ∧
    unionPerm (.mutLocked 1) (.mutLocked 1) = .mutLocked 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Joining a root `.mutLocked 1` with a split tree
`.split [([0], .mutLocked 2)]` preserves both loans on field `0` and loan `1` on
all other fields. -/
theorem unionPerm_root_mut_and_split_child :
    let tSplit := setChildPerm 0 (.mutLocked 2) .unborrowed
    let joined := unionPerm (.mutLocked 1) tSplit
    let after1 := releaseLoanPerm 1 joined
    canWritePath [1] after1 = true ∧
    canWritePath [0] after1 = false ∧
    releaseLoanPerm 2 after1 = .unborrowed :=
  ⟨rfl, rfl, rfl⟩

/-- Exhaustive unit tests for loan-ID set helpers (`elemLoanId`, `dedupLoanIds`,
`mergeLoanIds`, `removeLoanId`, `replaceLoanId`, `loanIdListEq`) and path prefix
and overlap relations (`subPathEq`, `subPathPrefix`, `stripSubPathPrefix`,
`subPathOverlaps`). -/
theorem loanId_and_subPath_helpers_exhaustive_tests :
    elemLoanId 2 [] = false ∧
    elemLoanId 2 [1, 2, 3] = true ∧
    elemLoanId 4 [1, 2, 3] = false ∧
    dedupLoanIds [1, 2, 1, 3, 2] = [1, 3, 2] ∧
    mergeLoanIds [1, 2] [2, 3, 4] = [1, 2, 3, 4] ∧
    removeLoanId 2 [1, 2, 3, 2] = [1, 3] ∧
    removeLoanId 9 [1, 2, 3] = [1, 2, 3] ∧
    replaceLoanId 2 1 [1, 2, 3] = [1, 3] ∧
    replaceLoanId 2 5 [1, 2, 3] = [1, 5, 3] ∧
    loanIdListEq [0, 1] [0, 1] = true ∧
    loanIdListEq [0, 1] [0, 2] = false ∧
    loanIdListEq [0, 1] [0, 1, 2] = false ∧
    subPathPrefix [] [0, 1] = true ∧
    subPathPrefix [0] [0, 1] = true ∧
    subPathPrefix [0, 1] [0, 1] = true ∧
    subPathPrefix [0, 1, 2] [0, 1] = false ∧
    subPathPrefix [0, 2] [0, 1] = false ∧
    stripSubPathPrefix [0] [0, 1, 2] = some [1, 2] ∧
    stripSubPathPrefix [0, 2] [0, 1, 2] = none ∧
    subPathOverlaps [0] [0, 1] = true ∧
    subPathOverlaps [0, 1] [0] = true ∧
    subPathOverlaps [0] [1] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exhaustive unit tests for `SubPerm`, `mkSubPermOpt`, `mkLeafPerm`,
`subPermCanRead`, `unionSubPerm`, and `renameLoanPerm`. -/
theorem subPerm_and_renameLoanPerm_exhaustive_tests :
    subPermCanRead (.shared [1]) = true ∧
    subPermCanRead (.mutLocked 1) = false ∧
    subPermCanRead (.mutJoined [1] [2]) = false ∧
    subPermCanRead (.mutJoined [] [2]) = true ∧
    mkSubPermOpt [] [] = none ∧
    mkSubPermOpt [] [3] = some (.shared [3]) ∧
    mkSubPermOpt [1] [] = some (.mutLocked 1) ∧
    mkSubPermOpt [1] [3] = some (.mutJoined [1] [3]) ∧
    mkLeafPerm [] [] = .unborrowed ∧
    mkLeafPerm [] [3] = .shared [3] ∧
    mkLeafPerm [1] [] = .mutLocked 1 ∧
    mkLeafPerm [1] [3] = .mutJoined [1] [3] ∧
    unionSubPerm (.mutJoined [1, 2] [3]) (.shared [4]) =
      .mutJoined [1, 2] [3, 4] ∧
    renameLoanPerm 2 1 (.shared [1, 2]) = .shared [1] ∧
    renameLoanPerm 2 9 (.mutLocked 2) = .mutLocked 9 ∧
    renameLoanPerm 2 1 (.mutJoined [1, 2] [3]) = .mutJoined [1] [3] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exhaustive positive and negative matrix for `acquirePerm` across root and
descendant paths on `.unborrowed`, `.shared`, `.mutLocked`, `.mutJoined`, and
`.split` trees. -/
theorem acquirePerm_positive_and_negative_matrix_tests :
    acquirePerm .shared 1 [] .unborrowed = some (.shared [1]) ∧
    acquirePerm .shared 2 [] (.shared [1]) = some (.shared [1, 2]) ∧
    acquirePerm .shared 1 [] (.shared [1]) = some (.shared [1]) ∧
    acquirePerm .shared 2 [] (.mutLocked 1) = none ∧
    acquirePerm .shared 3 [0] (.mutLocked 1) = none ∧
    acquirePerm .shared 3 [] (.mutJoined [1] [2]) = none ∧
    acquirePerm .shared 3 [0] (.mutJoined [1] [2]) = none ∧
    acquirePerm .mutBorrow 1 [] .unborrowed = some (.mutLocked 1) ∧
    acquirePerm .mutBorrow 2 [] (.shared [1]) = none ∧
    acquirePerm .mutBorrow 2 [0] (.shared [1]) = none ∧
    acquirePerm .mutBorrow 2 [] (.mutLocked 1) = none ∧
    acquirePerm .mutBorrow 2 [0] (.mutLocked 1) = none ∧
    acquirePerm .mutBorrow 3 [] (.mutJoined [1] [2]) = none ∧
    acquirePerm .mutBorrow 3 [0] (.mutJoined [1] [2]) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Multi-branch `.split` tree lifecycle: acquiring independent borrows at
`[0, 0]` (`.mutBorrow 1`), `[0, 1]` (`.shared 2`), and `[1]` (`.mutBorrow 3`),
verifying `getChildPerm`, `getPathPerm`, and descendant conflict detection on
ancestor paths, and releasing each loan until `.split` collapses back to
`.unborrowed`. -/
theorem split_tree_multibranch_lifecycle_and_conflict_tests :
    match acquirePerm .mutBorrow 1 [0, 0] .unborrowed with
    | some t1 =>
      match acquirePerm .shared 2 [0, 1] t1 with
      | some t2 =>
        match acquirePerm .mutBorrow 3 [1] t2 with
        | some t3 =>
          getChildPerm 1 t3 = .mutLocked 3 ∧
          getPathPerm [0, 1] t3 = .shared [2] ∧
          acquirePerm .mutBorrow 4 [0] t3 = none ∧
          acquirePerm .shared 4 [0] t3 = none ∧
          (match acquirePerm .shared 4 [0, 1] t3 with
           | some _ => true
           | none => false) = true ∧
          canWritePath [0, 0] t3 = false ∧
          canReadPath [0, 0] t3 = false ∧
          canReadPath [0, 1] t3 = true ∧
          canWritePath [0, 1] t3 = false ∧
          canWritePath [0, 2] t3 = true ∧
          canWritePath [1] t3 = false ∧
          canWritePath [2] t3 = true ∧
          canReadTree (releaseLoanPerm 3 (releaseLoanPerm 1 t3)) = true ∧
          releaseLoanPerm 2 (releaseLoanPerm 3 (releaseLoanPerm 1 t3)) =
            .unborrowed
        | none => False
      | none => False
    | none => False :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exhaustive tests for `unionPerm` across two `.split` trees with overlapping
and disjoint subpaths, and between `.shared` and `.split`. -/
theorem unionPerm_split_and_shared_combinations_tests :
    let s1 : PermTree := .split [([0], .mutLocked 1), ([2], .shared [4])]
    let s2 : PermTree := .split [([0], .shared [2]), ([1], .mutLocked 3)]
    let joined := unionPerm s1 s2
    let shSplit := unionPerm (.shared [5]) s1
    let splitSh := unionPerm s1 (.shared [5])
    canWritePath [3] splitSh = false ∧
    canReadPath [0] joined = false ∧
    canReadPath [1] joined = false ∧
    canReadPath [2] joined = true ∧
    canWritePath [2] joined = false ∧
    canWritePath [3] joined = true ∧
    canReadPath [0] (releaseLoanPerm 1 joined) = true ∧
    canWritePath [0] (releaseLoanPerm 1 joined) = false ∧
    canWritePath [0] (releaseLoanPerm 2 (releaseLoanPerm 1 joined)) = true ∧
    canWritePath [3] shSplit = false ∧
    canReadPath [3] shSplit = true ∧
    -- Degenerate `.split [([0], .shared [])]` normalizes to `.unborrowed`,
    -- `fromEntries` deduplicates `.shared [1, 1]`, and `releaseLoanPermAtPath`
    -- releases only the specified sub-path:
    isUnborrowed (.split [([0], .shared []), ([1], .mutJoined [] [])]) =
      true ∧
    canWritePath [0] (.split [([0], .shared [])]) = true ∧
    fromEntries [([0], .shared [1, 1])] = .split [([0], .shared [1])] ∧
    releaseLoanPermAtPath 1 [0]
      (.split [([0], .mutLocked 1), ([1], .mutLocked 1)]) =
      .split [([1], .mutLocked 1)] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PureLift
