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
import Init.Data.UInt.BasicAux
import Anneal.PureLift.Lens
import Anneal.PureLift.PermTree

namespace Anneal.PureLift

/-!
# Unified Loan Graph, Backward Morphisms, and Multi-Region Groups

Models active borrows, nested reborrows, conditional diamond borrow joins, and
multi-region-group call frames as a pure functional directed acyclic graph
(`SymState Val`).

Key design invariants:
- `PlaceCell Val` unifies local variable slots and active loan cells under a
  single `(val, perm)` representation, avoiding duplicated owner dispatch.
- `BackTarget Val` encodes how ending a mutable loan propagates its final value
  back to its parent owner(s), including conditional diamond borrows (`.choice`)
  and interprocedural lenses (`.lensCall` and `.regionOut`).
- `LoanPhase.spatialPinned` represents a mutable loan temporarily exported to
  the spatial memory zone as a loan lifecycle phase rather than a `BackTarget`
  constructor. Consequently, freezing and reabsorbing a loan preserves its
  `BackTarget` intact while automatically blocking pure reads, writes, and
  premature `endLoanInState` calls while pinned.
- `RegionGroupEntry` tracks lifetime outlives dependencies (`requiredChildren`)
  and verifies that all output loans of a region group are unborrowed
  (`isUnborrowed e.cell.perm`) before retiring the group.
-/

/-- Reference to the owner of a borrowed sub-place: either a local variable
register or an enclosing parent loan. -/
inductive OwnerRef where
  | localReg (reg : LocalId)
  | parentLoan (lid : LoanId)

def OwnerRef.beq : OwnerRef → OwnerRef → Bool
  | .localReg r1, .localReg r2 => r1 == r2
  | .parentLoan l1, .parentLoan l2 => l1 == l2
  | _, _ => false

/-- Elementary pre-order step in a serialized `BackTarget Val` tree. -/
inductive BackTargetStep (Val : Type) where
  | rootParam (paramIdx : Nat)
  | direct (owner : OwnerRef) (path : SubPath)
  | choiceJoin (cond : Val)
  | lensCall (targets : List (OwnerRef × SubPath))
      (backFn : Val → Option (List Val))
  | regionOut (groupId : RegionGroupId) (outIdx : Nat)

/-- Compositional backward writeback target for an active loan, represented as a
pre-order step sequence so right-to-left `listFold` (`List.foldr`) evaluates
arbitrarily nested `.choice` trees bottom-up as a computable Lean 4 definition:
- `BackTarget.rootParam paramIdx`: external `&` or `&mut` input parameter of the
  current function.
- `BackTarget.direct owner path`: borrow of `path` inside `owner`.
- `BackTarget.choice cond onTrue onFalse`: diamond conditional borrow merged
  across branches under symbolic condition `cond`.
- `BackTarget.lensCall targets backFn`: single-region interprocedural call
  returning a mutable borrow with backward lens `backFn`.
- `BackTarget.regionOut groupId outIdx`: output borrow `outIdx` of
  multi-region-group call frame `groupId`. -/
structure BackTarget (Val : Type) where
  steps : List (BackTargetStep Val)

namespace BackTarget

def rootParam {Val : Type} (paramIdx : Nat) : BackTarget Val :=
  ⟨[.rootParam paramIdx]⟩

def direct {Val : Type} (owner : OwnerRef) (path : SubPath) : BackTarget Val :=
  ⟨[.direct owner path]⟩

def choice {Val : Type} (cond : Val) (onTrue : BackTarget Val)
    (onFalse : BackTarget Val) : BackTarget Val :=
  ⟨.choiceJoin cond :: (onTrue.steps ++ onFalse.steps)⟩

def lensCall {Val : Type} (targets : List (OwnerRef × SubPath))
    (backFn : Val → Option (List Val)) : BackTarget Val :=
  ⟨[.lensCall targets backFn]⟩

def regionOut {Val : Type} (groupId : RegionGroupId) (outIdx : Nat) :
    BackTarget Val :=
  ⟨[.regionOut groupId outIdx]⟩

end BackTarget

/-- True iff `BackTarget` (or any branch inside a nested `.choice` tree)
contains a `.regionOut` target that must be retired via `endRegionGroupInState`
rather than `endLoanInState`. -/
def isRegionOutTarget {Val : Type} (t : BackTarget Val) : Bool :=
  t.steps.foldr
    (fun step ih =>
      match step with
      | .regionOut _ _ => true
      | _ => ih)
    false

/-- True iff `BackTarget` (or any branch inside a nested `.choice` tree)
contains a `.rootParam` target that represents an external caller parameter and
must be finalized at function return by `collectRootMutVals` rather than ended
intra-procedurally via `endLoanInState`. -/
def isRootParamTarget {Val : Type} (t : BackTarget Val) : Bool :=
  t.steps.foldr
    (fun step ih =>
      match step with
      | .rootParam _ => true
      | _ => ih)
    false

/-- Branch-sensitive variant of `isRegionOutTarget || isRootParamTarget`: true
iff an active branch of `target` contains a `.rootParam` or `.regionOut` step.
Untaken branches of a `.choice` whose condition is concrete are ignored; both
branches of a symbolic choice count. -/
def activeTargetHasSpecial {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) : Bool :=
  let stk : List Bool :=
    target.steps.foldr
      (fun step acc =>
        match step with
        | .rootParam _ => true :: acc
        | .direct _ _ => false :: acc
        | .choiceJoin cond =>
          match acc with
          | bTrue :: bFalse :: rest =>
            let merged :=
              match alg.asBool cond with
              | some true => bTrue
              | some false => bFalse
              | none => bTrue || bFalse
            merged :: rest
          | _ => [true]
        | .lensCall _ _ => false :: acc
        | .regionOut _ _ => true :: acc)
      []
  match stk with
  | [b] => b
  | _ => true

/-- True iff `target` is `.regionOut gid expectedIdx`. -/
def isMatchingRegionOut {Val : Type} (gid : RegionGroupId)
    (expectedIdx : Nat) (t : BackTarget Val) : Bool :=
  match t.steps with
  | [.regionOut g idx] => g == gid && idx == expectedIdx
  | _ => false

/-- Look up the updated value for `(owner, path)` from a parallel `(targets,
vals)` list produced by a `.lensCall` backward function, returning `none` if
`targets` and `vals` have different lengths, and `some vOld` if `(owner, path)`
does not appear in `targets`. -/
def lookupLensTargetVal {Val : Type} (owner : OwnerRef) (path : SubPath)
    (vOld : Val) (targets : List (OwnerRef × SubPath)) (vals : List Val) :
    Option Val :=
  targets.foldr
    (fun op ih vs =>
      match op, vs with
      | (o, p), vUpd :: restVals =>
        match ih restVals with
        | some tailVal =>
          if OwnerRef.beq owner o && subPathEq path p then
            some vUpd
          else
            some tailVal
        | none => none
      | _, [] => none)
    (fun vs =>
      match vs with
      | [] => some vOld
      | _ :: _ => none)
    vals

/-- True iff `(owner, path)` overlaps with any `(o, p)` entry in `xs`
(`OwnerRef.beq owner o && subPathOverlaps path p`). -/
def overlapsAnyOwnerPath (owner : OwnerRef) (path : SubPath)
    (xs : List (OwnerRef × SubPath)) : Bool :=
  xs.foldr
    (fun op ih =>
      match op with
      | (o, p) =>
        if OwnerRef.beq owner o && subPathOverlaps path p then true else ih)
    false

/-- True iff all `(owner, path)` entries in `xs` are pairwise disjoint (neither
equal nor overlapping sub-paths of the same owner). -/
def ownerPathsDisjoint (xs : List (OwnerRef × SubPath)) : Bool :=
  match
    xs.foldr
      (fun op acc =>
        match op, acc with
        | (o, p), (ok, seen) =>
          (ok && !overlapsAnyOwnerPath o p seen, (o, p) :: seen))
      (true, [])
  with
  | (ok, _) => ok

/-- True iff `(owner, path)` occurs in `xs`. -/
def containsOwnerPath (owner : OwnerRef) (path : SubPath)
    (xs : List (OwnerRef × SubPath)) : Bool :=
  xs.foldr
    (fun op ih =>
      match op with
      | (o, p) =>
        if OwnerRef.beq owner o && subPathEq path p then true else ih)
    false

/-- Deduplicate a list of `(OwnerRef × SubPath)` leaves via total structural
recursion so diamond writeback updates each underlying leaf once without
truncating large leaf sets. -/
def dedupOwnerPaths (xs : List (OwnerRef × SubPath)) :
    List (OwnerRef × SubPath) :=
  xs.foldr
    (fun op tail =>
      match op with
      | (o, p) =>
        if containsOwnerPath o p tail then tail else (o, p) :: tail)
    []

/-- Collect all leaf `(OwnerRef × SubPath)` targets referenced anywhere in
`target` via total structural recursion (`List.foldr`). -/
def targetLeaves {Val : Type} (target : BackTarget Val) :
    List (OwnerRef × SubPath) :=
  target.steps.foldr
    (fun step acc =>
      match step with
      | .rootParam _ => acc
      | .direct o p => (o, p) :: acc
      | .choiceJoin _ => acc
      | .lensCall targets _ => targets ++ acc
      | .regionOut _ _ => acc)
    []

/-- Collect the active leaf `(OwnerRef × SubPath)` targets of `target`, pruning
untaken branches whenever `.choiceJoin cond` has a concrete boolean condition
`alg.asBool cond = some b`. A malformed step sequence (a truncated `.choiceJoin`
or a stack that does not reduce to one tree) conservatively yields every
serialized leaf (`targetLeaves`), so dependency checks such as
`noActiveChildLoanEdgesIn` can never lose an edge through a malformed child
target. -/
def activeTargetLeaves {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) : List (OwnerRef × SubPath) :=
  let res : Bool × List (List (OwnerRef × SubPath)) :=
    target.steps.foldr
      (fun step (acc : Bool × List (List (OwnerRef × SubPath))) =>
        match acc with
        | (ok, stk) =>
          match step with
          | .rootParam _ => (ok, [] :: stk)
          | .direct o p => (ok, [(o, p)] :: stk)
          | .choiceJoin cond =>
            match stk with
            | lTrue :: lFalse :: rest =>
              let merged :=
                match alg.asBool cond with
                | some true => lTrue
                | some false => lFalse
                | none => lTrue ++ lFalse
              (ok, merged :: rest)
            | _ => (false, [[]])
          | .lensCall targets _ => (ok, targets :: stk)
          | .regionOut _ _ => (ok, [] :: stk))
      (true, [])
  match res with
  | (true, [leaves]) => leaves
  | _ => targetLeaves target

/-- Verify structural well-formedness of a shared-loan `BackTarget` step tree
(rejecting truncated `.choiceJoin` trees, `.rootParam` targets, `.regionOut`
targets, and `.choice` trees whose active branches target distinct overlapping
sub-paths of the same owner, while validating only the taken branch when
`.choiceJoin cond` has a concrete boolean condition). -/
def validateSharedBackTarget {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) : Bool :=
  if !ownerPathsDisjoint (dedupOwnerPaths (activeTargetLeaves alg target)) then
    false
  else
    let stk : List Bool :=
      target.steps.foldr
        (fun step acc =>
          match step with
          | .rootParam _ => false :: acc
          | .direct _ _ => true :: acc
          | .choiceJoin cond =>
            match acc with
            | bTrue :: bFalse :: rest =>
              let ok :=
                match alg.asBool cond with
                | some true => bTrue
                | some false => bFalse
                | none => bTrue && bFalse
              ok :: rest
            | _ => [false]
          | .lensCall targets _ => ownerPathsDisjoint targets :: acc
          | .regionOut _ _ => false :: acc)
        []
    match stk with
    | [true] => true
    | _ => false

/-- Verify that every active `.lensCall` branch inside `target` has
pairwise-disjoint `targets` and succeeds on its branch-projected loan value
with a value list matching its `targets` arity, that no active `.choice`
branches target distinct overlapping sub-paths of the same owner, that no
`.rootParam` or `.regionOut` node appears in `target`, and that the pre-order
step tree is well-formed. -/
def validateBackTarget {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) (vNew : Val) : Bool :=
  if !ownerPathsDisjoint (dedupOwnerPaths (activeTargetLeaves alg target)) then
    false
  else
    let stk : List (Val → Bool) :=
      target.steps.foldr
        (fun step acc =>
          match step with
          | .rootParam _ => (fun _ => false) :: acc
          | .direct _ _ => (fun _ => true) :: acc
          | .choiceJoin cond =>
            match acc with
            | fTrue :: fFalse :: rest =>
              let fBranch : Val → Bool :=
                fun vCur =>
                  match alg.asBool cond with
                  | some true => fTrue vCur
                  | some false => fFalse vCur
                  | none =>
                    fTrue (alg.projectBranchVal cond true vCur) &&
                    fFalse (alg.projectBranchVal cond false vCur)
              fBranch :: rest
            | _ => [fun _ => false]
          | .lensCall targets backFn =>
            let fLeaf : Val → Bool :=
              fun vCur =>
                ownerPathsDisjoint targets &&
                match backFn vCur with
                | some vals => vals.length == targets.length
                | none => false
            fLeaf :: acc
          | .regionOut _ _ => (fun _ => false) :: acc)
        []
    match stk with
    | [fRoot] => fRoot vNew
    | _ => false

/-- Evaluate the updated sub-value for `(owner, path)` when ending a loan with
`target`, new loan value `vNew`, and prior owner sub-value `vOld`. Supports
`.direct`, `.lensCall`, and arbitrarily nested `.choice` trees with
branch-sensitive evaluation and branch-specific value projection of both `vNew`
and `vOld`. -/
def evalBackVal {Val : Type} (alg : ValAlgebra Val)
    (owner : OwnerRef) (path : SubPath)
    (target : BackTarget Val) (vNew vOld : Val) : Option Val :=
  let stk : List (Val → Val → Option Val) :=
    target.steps.foldr
      (fun step acc =>
        match step with
        | .rootParam _ => (fun _ _ => none) :: acc
        | .direct o p =>
          let fLeaf : Val → Val → Option Val :=
            fun vCur vOldCur =>
              if OwnerRef.beq owner o && subPathEq path p then some vCur
              else some vOldCur
          fLeaf :: acc
        | .choiceJoin cond =>
          match acc with
          | fTrue :: fFalse :: rest =>
            let fBranch : Val → Val → Option Val :=
              fun vCur vOldCur =>
                match alg.asBool cond with
                | some true => fTrue vCur vOldCur
                | some false => fFalse vCur vOldCur
                | none =>
                  -- Both values are projected onto each branch before the
                  -- branch results are recombined with `zipVal`. `ValAlgebra`
                  -- pins `projectBranchVal` down only on concrete conditions
                  -- and on `zipVal` results, so for other values this is a
                  -- precision choice rather than a trusted step: end-to-end
                  -- claims hold only through `pure_lift_sound`'s simulation
                  -- obligation, which a projection that does not match the
                  -- machine would make unprovable rather than unsound.
                  match fTrue (alg.projectBranchVal cond true vCur)
                              (alg.projectBranchVal cond true vOldCur),
                        fFalse (alg.projectBranchVal cond false vCur)
                               (alg.projectBranchVal cond false vOldCur) with
                  | some v1, some v2 => some (alg.zipVal cond v1 v2)
                  | _, _ => none
            fBranch :: rest
          | _ => [fun _ _ => none]
        | .lensCall targets backFn =>
          let fLeaf : Val → Val → Option Val :=
            fun vCur vOldCur =>
              if !containsOwnerPath owner path targets then
                some vOldCur
              else
                match backFn vCur with
                | some updatedVals =>
                  lookupLensTargetVal owner path vOldCur targets updatedVals
                | none => none
          fLeaf :: acc
        | .regionOut _ _ => (fun _ _ => none) :: acc)
      []
  match stk with
  | [fRoot] => fRoot vNew vOld
  | _ => none

/-- Low-level spatial memory cell supporting initialized values, uninitialized
storage (`.uninit`), and raw byte views (`.rawByte`). A raw byte is a `UInt8`
so the representation cannot hold values outside Rust's 8-bit byte range. -/
inductive CellVal (Val : Type) where
  | init (v : Val)
  | uninit
  | rawByte (b : UInt8)

/-- True iff any cell in `cells` is `.uninit`. -/
def hasUninitCell {Val : Type} (cells : List (CellVal Val)) : Bool :=
  cells.foldr
    (fun c ih =>
      match c with
      | .uninit => true
      | .init _ => ih
      | .rawByte _ => ih)
    false

/-- Representation codec converting between pure values (`Val`) and spatial
memory cells (`List (CellVal Val)`), carrying a kernel-checked round-trip law
`decode_encode`. -/
structure SpatialCodec (Val : Type) where
  codecId : Nat
  encode : Val → List (CellVal Val)
  decode : List (CellVal Val) → Option Val
  decode_encode : ∀ v : Val, decode (encode v) = some v

/-- Lifecycle phase of a loan in the loan graph. `.spatialPinned` binds the
exact `SpatialCodec Val` used to freeze the loan so reabsorption cannot
substitute an unrelated decoder. -/
inductive LoanPhase (Val : Type) where
  | activeShared : LoanPhase Val
  | activeMut : LoanPhase Val
  | spatialPinned (bid : BlockId) (codec : SpatialCodec Val) : LoanPhase Val
  | ended : LoanPhase Val

def LoanPhase.isActive {Val : Type} : LoanPhase Val → Bool
  | .activeShared => true
  | .activeMut => true
  | .spatialPinned _ _ => false
  | .ended => false

def LoanPhase.isActiveMut {Val : Type} : LoanPhase Val → Bool
  | .activeMut => true
  | _ => false

def LoanPhase.isEnded {Val : Type} : LoanPhase Val → Bool
  | .ended => true
  | _ => false

def LoanPhase.samePhase {Val : Type} : LoanPhase Val → LoanPhase Val → Bool
  | .activeShared, .activeShared => true
  | .activeMut, .activeMut => true
  | .ended, .ended => true
  | _, _ => false

/-- Permissioned value cell shared by local variable slots and loan entries. -/
structure PlaceCell (Val : Type) where
  val : Val
  perm : PermTree

/-- Single node in the unified loan graph. -/
structure LoanEntry (Val : Type) where
  id : LoanId
  phase : LoanPhase Val
  cell : PlaceCell Val
  target : BackTarget Val

/-- Multi-region-group call frame tracking a lifetime group `groupId`, its
locked input places, its output loans, its required shorter-lived child groups,
and its pure backward function `backFn`. -/
structure RegionGroupEntry (Val : Type) where
  groupId : RegionGroupId
  active : Bool
  lockLid : LoanId
  inputTargets : List (OwnerRef × SubPath)
  outputLoans : List LoanId
  requiredChildren : List RegionGroupId
  backFn : List Val → List Val → Option (List Val × List Val)

/-- Spatial memory access permission for hybrid spatial blocks. -/
inductive SpatialPerm where
  | readOnly
  | readWrite

/-- Spatial memory block exported from an active mutable loan. -/
structure SpatialBlock (Val : Type) where
  blockId : BlockId
  originLoan : LoanId
  perm : SpatialPerm
  provenanceTag : Nat
  activeSubSplits : Nat
  cells : List (CellVal Val)

/-- Complete pure symbolic state of a `PureLift` evaluation.

Each entry `(gid, v)` of `regionDeposits` is a value deposited by the backward
function of region group `gid` when it ended. Only a group that lists `gid` in
its `requiredChildren` receives (and consumes) those values; see
`takeChildDeposits`. -/
structure SymState (Val : Type) where
  locals : List (PlaceCell Val)
  loans : List (LoanEntry Val)
  regionGroups : List (RegionGroupEntry Val)
  regionDeposits : List (RegionGroupId × Val)
  spatial : List (SpatialBlock Val)
  nextSpatialTag : Nat

/-- Look up index `idx` in `xs`, returning `defVal` when out of bounds. -/
def listGetVal {α : Type} (defVal : α) (idx : Nat) (xs : List α) : α :=
  natFold
    (fun ys =>
      match ys with
      | [] => defVal
      | x :: _ => x)
    (fun _ ih ys =>
      match ys with
      | [] => defVal
      | _ :: rest => ih rest)
    idx xs

def getLocalCell {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (st : SymState Val) : PlaceCell Val :=
  listGetVal ⟨alg.defaultVal, .unborrowed⟩ reg st.locals

/-- Force a `SubPerm` and its head loan IDs to constructor WHNF. -/
def strictSubPerm (sp : SubPerm) : SubPerm :=
  match sp with
  | .shared [] => .shared []
  | .shared [l1] => .shared [l1]
  | .shared [l1, l2] => .shared [l1, l2]
  | .shared (l1 :: l2 :: l3 :: ls) => .shared (l1 :: l2 :: l3 :: ls)
  | .mutLocked lid => .mutLocked lid
  | .mutJoined m s => .mutJoined m s

/-- Force a `(SubPath × SubPerm)` entry to constructor WHNF. -/
def strictSplitEntry (e : SubPath × SubPerm) : SubPath × SubPerm :=
  match e with
  | ([], sp) => ([], strictSubPerm sp)
  | ([f1], sp) => ([f1], strictSubPerm sp)
  | ([f1, f2], sp) => ([f1, f2], strictSubPerm sp)
  | (f1 :: f2 :: fs, sp) => (f1 :: f2 :: fs, strictSubPerm sp)

/-- Construct a `PlaceCell Val` after forcing `p : PermTree` (including `.split`
entry spines) to weak head normal form so multi-step plans never accumulate
chains of unreduced `PermTree` thunks inside `PlaceCell.perm`. -/
def mkStrictPlaceCell {Val : Type} (v : Val) (p : PermTree) : PlaceCell Val :=
  match p with
  | .unborrowed => ⟨v, .unborrowed⟩
  | .shared [] => ⟨v, .unborrowed⟩
  | .shared [l1] => ⟨v, .shared [l1]⟩
  | .shared (l1 :: l2 :: ls) => ⟨v, .shared (l1 :: l2 :: ls)⟩
  | .mutLocked lid => ⟨v, .mutLocked lid⟩
  | .mutJoined m s => ⟨v, .mutJoined m s⟩
  | .split [] => ⟨v, .unborrowed⟩
  | .split [e1] =>
    match strictSplitEntry e1 with
    | (p1, sp1) => ⟨v, .split [(p1, sp1)]⟩
  | .split [e1, e2] =>
    match strictSplitEntry e1, strictSplitEntry e2 with
    | (p1, sp1), (p2, sp2) => ⟨v, .split [(p1, sp1), (p2, sp2)]⟩
  | .split (e1 :: e2 :: e3 :: rest) =>
    match strictSplitEntry e1, strictSplitEntry e2, strictSplitEntry e3 with
    | (p1, sp1), (p2, sp2), (p3, sp3) =>
      ⟨v, .split ((p1, sp1) :: (p2, sp2) :: (p3, sp3) :: rest)⟩

/-- Single-pass linear modifier for an existing local register `idx`. Fails
when `idx` is not below `xs.length`: a local that no plan step has written has
no value to read, borrow, or update. Only a whole-local write may create the
next fresh local (`setLocalChecked`). -/
def modifyLocalAt {Val : Type}
    (f : Val → PermTree → Option (Val × PermTree))
    (idx : Nat) (xs : List (PlaceCell Val)) :
    Option (List (PlaceCell Val)) :=
  natFold
    (fun cells =>
      match cells with
      | [] => none
      | ⟨v, p⟩ :: rest =>
        match f v p with
        | some (v', p') => some (mkStrictPlaceCell v' p' :: rest)
        | none => none)
    (fun _ ih cells =>
      match cells with
      | [] => none
      | x :: rest =>
        match ih rest with
        | some rest' => some (x :: rest')
        | none => none)
    idx xs

def getLocal {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (st : SymState Val) : Val :=
  (getLocalCell alg reg st).val

/-- Fallible local assignment for plan steps: writes `v` to local `reg` only if
`reg` already exists and its `PermTree` permits writing the whole local
(`canWritePath []`), so no live `&` or `&mut` borrow of the local is bypassed,
or if `reg` is exactly one past the end, in which case a fresh unborrowed local
is created. -/
def setLocalChecked {Val : Type} (_alg : ValAlgebra Val) (reg : LocalId)
    (v : Val) (st : SymState Val) : Option (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    if reg == locals.length then
      some ⟨locals ++ [⟨v, .unborrowed⟩], loans, rgs, deps, sp, tag⟩
    else
      match modifyLocalAt
          (fun _ p => if canWritePath [] p then some (v, p) else none)
          reg locals with
      | some locals' => some ⟨locals', loans, rgs, deps, sp, tag⟩
      | none => none

def getLocalPerm {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (st : SymState Val) : PermTree :=
  (getLocalCell alg reg st).perm

/-- Count occurrences of loan ID `lid` in `loans`. -/
def countLoanId {Val : Type} (lid : LoanId)
    (loans : List (LoanEntry Val)) : Nat :=
  loans.foldr (fun e ih => if e.id == lid then ih + 1 else ih) 0

/-- True iff `lid` occurs exactly once in `loans`. -/
def hasUniqueLoanId {Val : Type} (lid : LoanId)
    (loans : List (LoanEntry Val)) : Bool :=
  countLoanId lid loans == 1

/-- Find loan `lid` in `loans`. -/
def findLoan {Val : Type} (lid : LoanId)
    (loans : List (LoanEntry Val)) : Option (LoanEntry Val) :=
  loans.foldr
    (fun e ih => if e.id == lid then some e else ih)
    none

/-- Update loan `lid` in `loans`. -/
def updateLoan {Val : Type} (lid : LoanId)
    (f : LoanEntry Val → LoanEntry Val)
    (loans : List (LoanEntry Val)) : List (LoanEntry Val) :=
  loans.foldr
    (fun e ih => if e.id == lid then f e :: ih else e :: ih)
    []

/-- Enumerate fields `0 .. n - 1` of `w` and concatenate their handles via `ih`. -/
def collectFieldsFuel {Val : Type} (alg : ValAlgebra Val)
    (ih : Val → Option (List LoanId)) (w : Val) (n : Nat) :
    Option (List LoanId) :=
  natFold (some [])
    (fun idx acc =>
      match acc, alg.getField idx w with
      | some ls, some field =>
        match ih field with
        | some ls' => some (ls ++ ls')
        | none => none
      | some ls, none => some ls
      | none, _ => none)
    n

/-- Single step of `collectHandles` for `w`, given recursive handle collector
`ih` for strict sub-values. -/
def collectHandlesStep {Val : Type} (alg : ValAlgebra Val)
    (ih : Val → Option (List LoanId)) (w : Val) : Option (List LoanId) :=
  match alg.decodeRef w with
  | some (lid, _) => some [lid]
  | none =>
    let fromFields := collectFieldsFuel alg ih w (alg.sizeBound w)
    (alg.branchParts w).foldr
      (fun part acc =>
        match acc, ih part with
        | some ls, some ls' => some (ls ++ ls')
        | _, _ => none)
      fromFields

/-- Bounded handle scan with fuel `k`. -/
def collectHandlesFuel {Val : Type} (alg : ValAlgebra Val) (k : Nat) (v : Val) :
    Option (List LoanId) :=
  natFold (fun _ => none) (fun _ ih w => collectHandlesStep alg ih w) k v

/-- Loan IDs named by the borrow handles in `v`, or `none` if `v` nests more
deeply than its traversal budget `alg.sizeBound v + 1`. The scan visits:
- the value itself, which is a leaf if it decodes as a handle
  (`decodeRef_getField`: a handle has no fields);
- every field, enumerated through `alg.getField` at every index below
  `alg.sizeBound`, which `getField_lt_sizeBound` makes complete; and
- the arms of a symbolic choice (`alg.branchParts`), which are not fields but
  which `projectBranchVal` can expose again. -/
def collectHandles {Val : Type} (alg : ValAlgebra Val) (v : Val) :
    Option (List LoanId) :=
  collectHandlesFuel alg (alg.sizeBound v + 1) v

/-- True iff `v` contains no decodable borrow handle (`collectHandles`). -/
def handleFreeVal {Val : Type} (alg : ValAlgebra Val) (v : Val) : Bool :=
  match collectHandles alg v with
  | some [] => true
  | _ => false

/-- True iff neither the return value nor any final `&mut` parameter value of
`out` contains a borrow handle. -/
def handleFreeOut {Val : Type} (alg : ValAlgebra Val) (out : FuncOut Val) :
    Bool :=
  handleFreeVal alg out.ret && out.mutFinals.all (handleFreeVal alg)

/-- Concatenated `collectHandles` of every value in `vs`. -/
def collectHandlesList {Val : Type} (alg : ValAlgebra Val) (vs : List Val) :
    Option (List LoanId) :=
  vs.foldr
    (fun v acc =>
      match collectHandles alg v, acc with
      | some ls, some rest => some (ls ++ rest)
      | _, _ => none)
    (some [])

/-- True iff a handle to loan `lid` may be duplicated: `lid` names exactly one
loan, and that loan is `.activeShared` or `.ended`. Copying a handle to an
`.activeMut` or `.spatialPinned` loan would leave two places able to use one
unique loan, and a handle to a loan ID that does not exist yet would alias
whichever loan is allocated next. -/
def handleCopyable {Val : Type} (loans : List (LoanEntry Val))
    (lid : LoanId) : Bool :=
  hasUniqueLoanId lid loans &&
    match findLoan lid loans with
    | some e =>
      match e.phase with
      | .activeShared => true
      | .ended => true
      | .activeMut => false
      | .spatialPinned _ _ => false
    | none => false

/-- True iff `v` may be duplicated into the symbolic state: every borrow handle
inside it (`collectHandles`) satisfies `handleCopyable`. Plan reads never
invalidate their source, so a plan must transfer a mutable reference by
reborrowing it rather than by copying its handle. -/
def copyableVal {Val : Type} (alg : ValAlgebra Val)
    (loans : List (LoanEntry Val)) (v : Val) : Bool :=
  match collectHandles alg v with
  | some lids => lids.all (handleCopyable loans)
  | none => false

/-- Number of occurrences of `x` in `xs`. -/
def countNat (x : Nat) (xs : List Nat) : Nat :=
  xs.foldr (fun y n => if y == x then n + 1 else n) 0

/-- True iff writing the values `news` in place of `olds` (one writeback that
may span several places) introduces no new handle that could not be copied:
every handle in `news` either satisfies `handleCopyable` or occurs in `news`
no more often than in `olds`. Counting across the whole writeback admits
moving or swapping unique handles between the written places (as in
`mem::swap` of two `&mut` references) while rejecting handles that
callee-supplied functions or spatial cells fabricate or duplicate. -/
def replaceableVals {Val : Type} (alg : ValAlgebra Val)
    (loans : List (LoanEntry Val)) (olds news : List Val) : Bool :=
  match collectHandlesList alg news, collectHandlesList alg olds with
  | some newLids, some oldLids =>
    newLids.all (fun lid =>
      handleCopyable loans lid ||
        Nat.ble (countNat lid newLids) (countNat lid oldLids))
  | _, _ => false

/-- `replaceableVals` for a single place: writing `vNew` in place of `vOld`. -/
def replaceableVal {Val : Type} (alg : ValAlgebra Val)
    (loans : List (LoanEntry Val)) (vOld vNew : Val) : Bool :=
  replaceableVals alg loans [vOld] [vNew]

theorem list_all_replaceable_self {Val : Type} (loans : List (LoanEntry Val))
    (lids : List LoanId) :
    ∀ (xs : List LoanId),
      xs.all (fun lid =>
        handleCopyable loans lid ||
          Nat.ble (countNat lid lids) (countNat lid lids)) = true
  | [] => rfl
  | lid :: rest => by
    change
      ((handleCopyable loans lid ||
        Nat.ble (countNat lid lids) (countNat lid lids)) &&
       rest.all (fun x =>
         handleCopyable loans x ||
           Nat.ble (countNat x lids) (countNat x lids))) = true
    rw [Nat.ble_eq_true_of_le (Nat.le_refl (countNat lid lids))]
    rw [Bool.or_true, list_all_replaceable_self loans lids rest]
    rfl

/-- Reflexivity of `replaceableVals` whenever `collectHandlesList` succeeds. -/
theorem replaceableVals_self_of_collectHandlesList {Val : Type}
    (alg : ValAlgebra Val) (loans : List (LoanEntry Val)) (vs : List Val)
    (lids : List LoanId) (h : collectHandlesList alg vs = some lids) :
    replaceableVals alg loans vs vs = true := by
  unfold replaceableVals
  rw [h]
  exact list_all_replaceable_self loans lids lids

/-- Reflexivity of `replaceableVal` whenever `collectHandles` succeeds. -/
theorem replaceableVal_self_of_collectHandles {Val : Type}
    (alg : ValAlgebra Val) (loans : List (LoanEntry Val)) (v : Val)
    (lids : List LoanId) (h : collectHandles alg v = some lids) :
    replaceableVal alg loans v v = true := by
  apply replaceableVals_self_of_collectHandlesList alg loans [v] (lids ++ [])
  change
    (match collectHandles alg v, some ([] : List LoanId) with
     | some ls, some rest => some (ls ++ rest)
     | _, _ => none) = some (lids ++ [])
  rw [h]

theorem collectFieldsFuel_zero {Val : Type} (alg : ValAlgebra Val)
    (ih : Val → Option (List LoanId)) (w : Val) :
    collectFieldsFuel alg ih w 0 = some [] := rfl

theorem collectFieldsFuel_succ {Val : Type} (alg : ValAlgebra Val)
    (ih : Val → Option (List LoanId)) (w : Val) (n : Nat) :
    collectFieldsFuel alg ih w (n + 1) =
      (match collectFieldsFuel alg ih w n, alg.getField n w with
       | some ls, some field =>
         match ih field with
         | some ls' => some (ls ++ ls')
         | none => none
       | some ls, none => some ls
       | none, _ => none) := rfl

theorem lensTest_collectFields_none (ih : LensTestVal → Option (List LoanId))
    (w : LensTestVal) (hNone : ∀ idx, lensTestGetField idx w = none) :
    ∀ (n : Nat),
      collectFieldsFuel lensTestValAlg ih w n = some []
  | 0 => rfl
  | n' + 1 => by
    rw [collectFieldsFuel_succ, lensTest_collectFields_none ih w hNone n']
    dsimp only [lensTestValAlg]
    rw [hNone n']

theorem lensTest_collectFields_branch (ih : LensTestVal → Option (List LoanId))
    (fl fr : Nat) (l : LensTestTree fl) (r : LensTestTree fr)
    (lsL lsR : List LoanId)
    (hL : ih ⟨fl, l⟩ = some lsL) (hR : ih ⟨fr, r⟩ = some lsR) :
    ∀ (m : Nat),
      collectFieldsFuel lensTestValAlg ih
        ⟨fl + fr + 1, .branch fl fr l r⟩ (m + 2) = some (lsL ++ lsR)
  | 0 => by
    change
      collectFieldsFuel lensTestValAlg ih
        ⟨fl + fr + 1, .branch fl fr l r⟩ ((0 + 1) + 1) = some (lsL ++ lsR)
    rw [collectFieldsFuel_succ, collectFieldsFuel_succ, collectFieldsFuel_zero]
    have hG0 :
        lensTestValAlg.getField 0 ⟨fl + fr + 1, .branch fl fr l r⟩ =
          some ⟨fl, l⟩ := rfl
    have hG1 :
        lensTestValAlg.getField 1 ⟨fl + fr + 1, .branch fl fr l r⟩ =
          some ⟨fr, r⟩ := rfl
    rw [hG0, hG1]
    dsimp only
    rw [hL]
    dsimp only [List.nil_append]
    rw [hR]
  | m' + 1 => by
    change
      collectFieldsFuel lensTestValAlg ih
        ⟨fl + fr + 1, .branch fl fr l r⟩ ((m' + 2) + 1) = some (lsL ++ lsR)
    rw [collectFieldsFuel_succ,
        lensTest_collectFields_branch ih fl fr l r lsL lsR hL hR m']
    rfl

theorem lensTestTree_collectHandlesFuel :
    ∀ {f : Nat} (t : LensTestTree f) (k : Nat),
      f ≤ k →
      Exists fun lids =>
        collectHandlesFuel lensTestValAlg (k + 1) ⟨f, t⟩ = some lids := by
  intro f t
  induction t with
  | atom n =>
    intro k _
    exact ⟨[], rfl⟩
  | ref lid path =>
    intro k _
    exact ⟨[lid], rfl⟩
  | branch fl fr l r ihl ihr =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fl + fr ≤ k' := Nat.le_of_succ_le_succ hLe
      have hFl : fl ≤ k' := Nat.le_trans (Nat.le_add_right fl fr) hSub
      have hFr : fr ≤ k' := Nat.le_trans (Nat.le_add_left fr fl) hSub
      cases ihl k' hFl with
      | intro lsL hL =>
        cases ihr k' hFr with
        | intro lsR hR =>
          refine ⟨lsL ++ lsR, ?_⟩
          cases fr with
          | zero => nomatch (lensTestTree_fuel_pos r)
          | succ fr' =>
            exact lensTest_collectFields_branch
              (collectHandlesFuel lensTestValAlg (k' + 1))
              fl (fr' + 1) l r lsL lsR hL hR (fl + fr')
  | choice fc ft ff c vt vf _ iht ihf =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fc + ft + ff ≤ k' := Nat.le_of_succ_le_succ hLe
      have hSub12 : fc + ft ≤ k' :=
        Nat.le_trans (Nat.le_add_right (fc + ft) ff) hSub
      have hFt : ft ≤ k' := Nat.le_trans (Nat.le_add_left ft fc) hSub12
      have hFf : ff ≤ k' := Nat.le_trans (Nat.le_add_left ff (fc + ft)) hSub
      cases iht k' hFt with
      | intro lsT hT =>
        cases ihf k' hFf with
        | intro lsF hF =>
          refine ⟨lsF ++ lsT, ?_⟩
          have hNone :
              ∀ idx,
                lensTestGetField idx
                  ⟨fc + ft + ff + 1, .choice fc ft ff c vt vf⟩ = none := by
            intro idx
            cases idx with
            | zero => rfl
            | succ idx' => cases idx' <;> rfl
          change
            (match
               (match
                  collectFieldsFuel lensTestValAlg
                    (collectHandlesFuel lensTestValAlg (k' + 1))
                    ⟨fc + ft + ff + 1, .choice fc ft ff c vt vf⟩
                    (fc + ft + ff + 1),
                  collectHandlesFuel lensTestValAlg (k' + 1) ⟨ff, vf⟩ with
                | some ls, some ls' => some (ls ++ ls')
                | _, _ => none),
               collectHandlesFuel lensTestValAlg (k' + 1) ⟨ft, vt⟩ with
             | some ls, some ls' => some (ls ++ ls')
             | _, _ => none) = some (lsF ++ lsT)
          rw [lensTest_collectFields_none
                (collectHandlesFuel lensTestValAlg (k' + 1))
                ⟨fc + ft + ff + 1, .choice fc ft ff c vt vf⟩ hNone
                (fc + ft + ff + 1),
              hF, hT]
          rfl

/-- `collectHandles` is total on all `LensTestVal` values. -/
theorem lensTest_collectHandles_total (v : LensTestVal) :
    Exists fun lids => collectHandles lensTestValAlg v = some lids := by
  cases v with
  | mk f t =>
    exact lensTestTree_collectHandlesFuel t f (Nat.le_refl f)

/-- `replaceableVal` is reflexive on all `LensTestVal` values. -/
theorem lensTest_replaceableVal_self (loans : List (LoanEntry LensTestVal))
    (v : LensTestVal) :
    replaceableVal lensTestValAlg loans v v = true := by
  cases lensTest_collectHandles_total v with
  | intro lids h =>
    exact replaceableVal_self_of_collectHandles lensTestValAlg loans v lids h

/-- True iff some step of `target` is a `.choiceJoin` whose condition is
symbolic (`alg.asBool cond = none`). -/
def targetHasSymbolicChoice {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) : Bool :=
  target.steps.any (fun step =>
    match step with
    | .choiceJoin cond =>
      match alg.asBool cond with
      | none => true
      | some _ => false
    | _ => false)

/-- True iff some live storage observer other than those in `exempt` covers
storage overlapping `(owner, path)`:
- a live (not `.ended`) loan outside `exempt` whose target selects an
  overlapping owner path (`activeTargetLeaves`, which follows concrete
  `.choice` conditions); or
- an active region group whose lock `lockLid` is not in `exempt` and one of
  whose `inputTargets` overlaps.

Writing back into such storage would change a value that a still-live borrow
or region group observes. Targets containing a symbolic `.choice` are not
inspected: a branch join pairs each such loan with a different target in the
other branch, and `evalBackVal` writes back branch by branch. -/
def liveLoanTargetsOverlap {Val : Type} (alg : ValAlgebra Val)
    (exempt : List LoanId) (owner : OwnerRef) (path : SubPath)
    (loans : List (LoanEntry Val)) (rgs : List (RegionGroupEntry Val)) :
    Bool :=
  let overlaps (t : OwnerRef × SubPath) : Bool :=
    OwnerRef.beq t.1 owner && subPathOverlaps t.2 path
  loans.any (fun e =>
    !elemLoanId e.id exempt && !e.phase.isEnded &&
      !targetHasSymbolicChoice alg e.target &&
      (activeTargetLeaves alg e.target).any overlaps) ||
    rgs.any (fun g =>
      g.active && !elemLoanId g.lockLid exempt && g.inputTargets.any overlaps)

/-- Single-pass linear modifier for loan `lid`, enforcing that `lid` occurs
uniquely in `loans` and is active (or `.activeMut` when `reqMut == true`). -/
def modifyLoanAt {Val : Type} (lid : LoanId) (reqMut : Bool)
    (f : Val → PermTree → Option (Val × PermTree))
    (loans : List (LoanEntry Val)) : Option (List (LoanEntry Val)) :=
  if !hasUniqueLoanId lid loans then none
  else
    match
      loans.foldr
        (fun e (acc : Bool × List (LoanEntry Val)) =>
          match e, acc with
          | ⟨id, phase, ⟨v, p⟩, target⟩, (found, rest) =>
            if id == lid then
              let okPhase :=
                if reqMut then phase.isActiveMut else phase.isActive
              if okPhase then
                match f v p with
                | some (v', p') =>
                  (true, ⟨id, phase, mkStrictPlaceCell v' p', target⟩ :: rest)
                | none => (false, rest)
              else (false, rest)
            else
              (found, ⟨id, phase, ⟨v, p⟩, target⟩ :: rest))
        (false, [])
    with
    | (true, updated) => some updated
    | (false, _) => none

/-- Modify the `PlaceCell` of `owner` in a single pass. -/
def modifyOwner {Val : Type} (_alg : ValAlgebra Val) (owner : OwnerRef)
    (reqMut : Bool) (f : Val → PermTree → Option (Val × PermTree))
    (st : SymState Val) : Option (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    match owner with
    | .localReg reg =>
      match modifyLocalAt f reg locals with
      | some locals' => some ⟨locals', loans, rgs, deps, sp, tag⟩
      | none => none
    | .parentLoan lid =>
      match modifyLoanAt lid reqMut f loans with
      | some loans' => some ⟨locals, loans', rgs, deps, sp, tag⟩
      | none => none

/-- Single-pass linear modifier for local register `idx` returning an auxiliary
result `Res`. -/
def modifyLocalAtRes {Val Res : Type}
    (f : Val → PermTree → Option (Res × Val × PermTree))
    (idx : Nat) (xs : List (PlaceCell Val)) :
    Option (Res × List (PlaceCell Val)) :=
  natFold
    (fun cells =>
      match cells with
      -- As in `modifyLocalAt`, a missing local cannot be modified.
      | [] => none
      | ⟨v, p⟩ :: rest =>
        match f v p with
        | some (res, v', p') => some (res, mkStrictPlaceCell v' p' :: rest)
        | none => none)
    (fun _ ih cells =>
      match cells with
      | [] => none
      | x :: rest =>
        match ih rest with
        | some (res, rest') => some (res, x :: rest')
        | none => none)
    idx xs

/-- Single-pass linear modifier for loan `lid` returning an auxiliary result
`Res`, requiring `lid` to occur uniquely in `loans`. -/
def modifyLoanAtRes {Val Res : Type} (lid : LoanId) (reqMut : Bool)
    (f : Val → PermTree → Option (Res × Val × PermTree))
    (loans : List (LoanEntry Val)) : Option (Res × List (LoanEntry Val)) :=
  if !hasUniqueLoanId lid loans then none
  else
    match
      loans.foldr
        (fun e (acc : Option Res × List (LoanEntry Val)) =>
          match e, acc with
          | ⟨id, phase, ⟨v, p⟩, target⟩, (resOpt, rest) =>
            if id == lid then
              let okPhase :=
                if reqMut then phase.isActiveMut else phase.isActive
              if okPhase then
                match f v p with
                | some (r, v', p') =>
                  (some r,
                   ⟨id, phase, mkStrictPlaceCell v' p', target⟩ :: rest)
                | none => (none, rest)
              else (none, rest)
            else
              (resOpt, ⟨id, phase, ⟨v, p⟩, target⟩ :: rest))
        (none, [])
    with
    | (some r, updated) => some (r, updated)
    | (none, _) => none

/-- Modify `owner` in a single pass and return an auxiliary result `Res`. -/
def modifyOwnerRes {Val Res : Type} (_alg : ValAlgebra Val)
    (owner : OwnerRef)
    (reqMut : Bool) (f : Val → PermTree → Option (Res × Val × PermTree))
    (st : SymState Val) : Option (Res × SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    match owner with
    | .localReg reg =>
      match modifyLocalAtRes f reg locals with
      | some (res, locals') => some (res, ⟨locals', loans, rgs, deps, sp, tag⟩)
      | none => none
    | .parentLoan lid =>
      match modifyLoanAtRes lid reqMut f loans with
      | some (res, loans') => some (res, ⟨locals, loans', rgs, deps, sp, tag⟩)
      | none => none

/-- Look up `owner` for read access at `path` (defaulting to the whole owner
`[]`), rejecting duplicate parent loan IDs, `.spatialPinned` and `.ended`
loans, as well as any cell whose `PermTree` has an active mutable borrow
overlapping `path` (`!canReadPath path cell.perm`). -/
def getOwnerForRead {Val : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (st : SymState Val) (path : SubPath := []) : Option (PlaceCell Val) :=
  match owner with
  | .localReg reg =>
    -- A local beyond `st.locals` was never written, so `getLocalCell` would
    -- return the synthetic `alg.defaultVal`; reading it must fail.
    if !decide (reg < st.locals.length) then none
    else
      match getLocalCell alg reg st with
      | ⟨v, p⟩ => if canReadPath path p then some ⟨v, p⟩ else none
  | .parentLoan lid =>
    if !hasUniqueLoanId lid st.loans then none
    else
      match findLoan lid st.loans with
      | some ⟨_, phase, ⟨v, p⟩, _⟩ =>
        if phase.isActive && canReadPath path p then some ⟨v, p⟩
        else none
      | none => none

/-- Look up `owner` for mutable access at `path` (defaulting to the whole owner
`[]`), rejecting duplicate parent loan IDs, `.activeShared`, `.spatialPinned`,
and `.ended` loans, as well as any cell whose `PermTree` has an active shared
or mutable borrow overlapping `path` (`!canWritePath path cell.perm`). -/
def getOwnerForMut {Val : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (st : SymState Val) (path : SubPath := []) : Option (PlaceCell Val) :=
  match owner with
  | .localReg reg =>
    -- As in `getOwnerForRead`: a local beyond `st.locals` does not exist.
    if !decide (reg < st.locals.length) then none
    else
      match getLocalCell alg reg st with
      | ⟨v, p⟩ => if canWritePath path p then some ⟨v, p⟩ else none
  | .parentLoan lid =>
    if !hasUniqueLoanId lid st.loans then none
    else
      match findLoan lid st.loans with
      | some ⟨_, phase, ⟨v, p⟩, _⟩ =>
        if phase.isActiveMut && canWritePath path p then
          some ⟨v, p⟩
        else none
      | none => none

/-- True iff `owner` names storage that already exists in `st`: a local
register below `st.locals.length`, or any parent loan (whose presence the loan
modifiers check themselves). Writeback and cleanup check it before modifying
an owner. -/
def ownerExists {Val : Type} (owner : OwnerRef) (st : SymState Val) : Bool :=
  match owner with
  | .localReg reg => decide (reg < st.locals.length)
  | .parentLoan _ => true

/-- Current value at `path` inside `owner`, or `none` if the owner does not
exist (or its loan ID is ambiguous) or the path does not resolve. -/
def ownerPathValue {Val : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (path : SubPath) (st : SymState Val) : Option Val :=
  match owner with
  | .localReg reg =>
    if !decide (reg < st.locals.length) then none
    else getPath alg path (getLocalCell alg reg st).val
  | .parentLoan lid =>
    if !hasUniqueLoanId lid st.loans then none
    else
      match findLoan lid st.loans with
      | some e => getPath alg path e.cell.val
      | none => none

/-- True iff writing `vals` into `targets` (one value per target) introduces no
new non-copyable handle, counting across all targets at once
(`replaceableVals`). -/
def targetsReplaceable {Val : Type} (alg : ValAlgebra Val)
    (targets : List (OwnerRef × SubPath)) (vals : List Val)
    (st : SymState Val) : Bool :=
  let olds : Option (List Val) :=
    targets.foldr
      (fun t acc =>
        match ownerPathValue alg t.1 t.2 st, acc with
        | some v, some rest => some (v :: rest)
        | _, _ => none)
      (some [])
  match olds with
  | some vs => replaceableVals alg st.loans vs vals
  | none => false

/-- Cleanup decision for an inactive leaf whose owner is a parent loan that the
cleanup cannot modify: one that is no longer active (for example, an untaken
branch's parent that already ended, which `noActiveChildLoanEdgesIn` permits)
or, for mutable cleanup (`reqMut`), an `.activeShared` parent. Such a cell
cannot be modified, but
it need not be: the leaf is skipped (`some (some st)`) if the cell carries no
permission overlapping `path` for `lid`, and rejected (`some none`) if it
retains a residual permission. `none` means the owner is not an inactive parent
loan and the caller should proceed normally. -/
def inactiveParentLeafCleanup {Val : Type} (lid : LoanId) (owner : OwnerRef)
    (path : SubPath) (st : SymState Val) (reqMut : Bool) :
    Option (Option (SymState Val)) :=
  match owner with
  | .parentLoan p =>
    match findLoan p st.loans with
    | some e =>
      -- Proceed normally only if the caller could actually modify this parent
      -- (`.activeMut` for mutable cleanup, any active phase for shared
      -- cleanup); otherwise inspect it read-only.
      if (if reqMut then e.phase.isActiveMut else e.phase.isActive) then none
      else if hasAnyLoanOverlappingPath lid path e.cell.perm then some none
      else some (some st)
    | none => none
  | .localReg _ => none

def writebackLeaf {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (target : BackTarget Val)
    (activeLeaves : List (OwnerRef × SubPath)) (vNew : Val)
    (owner : OwnerRef) (path : SubPath) (st : SymState Val) :
    Option (SymState Val) :=
  if containsOwnerPath owner path activeLeaves then
    if !ownerExists owner st ||
       liveLoanTargetsOverlap alg [lid] owner path st.loans st.regionGroups
    then none
    else
    modifyOwner alg owner true (fun ownerVal ownerPerm =>
      if !hasMutLoanAtPath lid path ownerPerm ||
         hasSharedLoanAtPath lid path ownerPerm then
        none
      else
        match getPath alg path ownerVal with
        | some vOld =>
          match evalBackVal alg owner path target vNew vOld with
          | some vUpd =>
            if !replaceableVal alg st.loans vOld vUpd then none
            else
            match putPath alg path ownerVal vUpd with
            | some ownerVal' =>
              some (ownerVal', releaseLoanPermAtPath lid path ownerPerm)
            | none => none
          | none => none
        | none => none) st
  else
    -- An inactive leaf naming a missing local holds no permission: skip it.
    if !ownerExists owner st then some st
    else
    match inactiveParentLeafCleanup lid owner path st true with
    | some decision => decision
    | none =>
    modifyOwner alg owner true (fun ownerVal ownerPerm =>
      if hasMutLoanAtPath lid path ownerPerm &&
         !hasSharedLoanAtPath lid path ownerPerm then
        some (ownerVal, releaseLoanPermAtPath lid path ownerPerm)
      else if hasAnyLoanOverlappingPath lid path ownerPerm then
        none
      else
        some (ownerVal, ownerPerm)) st

def writebackLeavesPass {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (target : BackTarget Val)
    (activeLeaves : List (OwnerRef × SubPath)) (wantActive : Bool)
    (vNew : Val) (leaves : List (OwnerRef × SubPath)) (st : SymState Val) :
    Option (SymState Val) :=
  leaves.foldr
    (fun op ih st0 =>
      match op with
      | (owner, path) =>
        if containsOwnerPath owner path activeLeaves == wantActive then
          match writebackLeaf alg lid target activeLeaves vNew owner path
              st0 with
          | some st1 => ih st1
          | none => none
        else
          ih st0)
    (fun st0 => some st0)
    st

def writebackLeaves {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (target : BackTarget Val) (vNew : Val)
    (leaves : List (OwnerRef × SubPath)) (st : SymState Val) :
    Option (SymState Val) :=
  let activeLeaves := activeTargetLeaves alg target
  match writebackLeavesPass alg lid target activeLeaves true vNew leaves
      st with
  | some st1 =>
    writebackLeavesPass alg lid target activeLeaves false vNew leaves st1
  | none => none

def writebackLensTargets {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (targets : List (OwnerRef × SubPath)) (vals : List Val)
    (st : SymState Val) : Option (SymState Val) :=
  -- Handles may move between the written places, but not multiply.
  if !targetsReplaceable alg targets vals st then none
  else
  targets.foldr
    (fun op ih vs st0 =>
      match op, vs with
      | (owner, path), vUpd :: restVals =>
        if !ownerExists owner st0 ||
           liveLoanTargetsOverlap alg [lid] owner path st0.loans
             st0.regionGroups then none
        else
        match modifyOwner alg owner true (fun ownerVal ownerPerm =>
          if !hasMutLoanAtPath lid path ownerPerm ||
             hasSharedLoanAtPath lid path ownerPerm then
            none
          else
            match putPath alg path ownerVal vUpd with
            | some ownerVal' =>
              some (ownerVal', releaseLoanPermAtPath lid path ownerPerm)
            | none => none) st0 with
        | some st1 => ih restVals st1
        | none => none
      | _, [] => none)
    (fun vs st0 =>
      match vs with
      | [] => some st0
      | _ :: _ => none)
    vals st

def releaseSharedLeavesPass {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (activeLeaves : List (OwnerRef × SubPath))
    (wantActive : Bool) (leaves : List (OwnerRef × SubPath))
    (st : SymState Val) : Option (SymState Val) :=
  leaves.foldr
    (fun op ih st0 =>
      match op with
      | (owner, path) =>
        if containsOwnerPath owner path activeLeaves == wantActive then
          if wantActive then
            if !ownerExists owner st0 then none
            else
            match modifyOwner alg owner false (fun ownerVal ownerPerm =>
              -- The shared loan must name a place that exists in the owner,
              -- not merely carry a (possibly forged) matching permission.
              match getPath alg path ownerVal with
              | none => none
              | some _ =>
                if !hasSharedLoanAtPath lid path ownerPerm ||
                   hasMutLoanAtPath lid path ownerPerm then
                  none
                else
                  some (ownerVal,
                        releaseLoanPermAtPath lid path ownerPerm)) st0 with
            | some st1 => ih st1
            | none => none
          else if !ownerExists owner st0 then ih st0
          else
            match inactiveParentLeafCleanup lid owner path st0 false with
            | some (some st1) => ih st1
            | some none => none
            | none =>
            match modifyOwner alg owner false (fun ownerVal ownerPerm =>
              if hasSharedLoanAtPath lid path ownerPerm &&
                 !hasMutLoanAtPath lid path ownerPerm then
                some (ownerVal,
                      releaseLoanPermAtPath lid path ownerPerm)
              else if hasAnyLoanOverlappingPath lid path ownerPerm then
                none
              else
                some (ownerVal, ownerPerm)) st0 with
            | some st1 => ih st1
            | none => none
        else
          ih st0)
    (fun st0 => some st0)
    st

def releaseSharedLeaves {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (activeLeaves : List (OwnerRef × SubPath))
    (leaves : List (OwnerRef × SubPath)) (st : SymState Val) :
    Option (SymState Val) :=
  match releaseSharedLeavesPass alg lid activeLeaves true leaves st with
  | some st1 =>
    releaseSharedLeavesPass alg lid activeLeaves false leaves st1
  | none => none

/-- True iff no local slot in `st.locals` and no loan cell in `st.loans`
retains any permission (mutable or shared, at any sub-path) for `lid`. -/
def noResidualLoanPerm {Val : Type} (lid : LoanId)
    (st : SymState Val) : Bool :=
  let localsClean :=
    st.locals.foldr
      (fun c ih => !hasAnyLoanOverlappingPath lid [] c.perm && ih)
      true
  let loansClean :=
    st.loans.foldr
      (fun e ih => !hasAnyLoanOverlappingPath lid [] e.cell.perm && ih)
      true
  localsClean && loansClean

/-- True iff no local slot or loan cell in `st` retains any permission for any
loan ID in `lids`. -/
def noResidualLoanListPerm {Val : Type} (lids : List LoanId)
    (st : SymState Val) : Bool :=
  lids.foldr (fun lid ih => noResidualLoanPerm lid st && ih) true

/-- True iff `targets` contains an edge targeting `.parentLoan lid`. -/
def hasParentLoanEdge (lid : LoanId)
    (targets : List (OwnerRef × SubPath)) : Bool :=
  targets.foldr
    (fun op ih => OwnerRef.beq op.1 (.parentLoan lid) || ih)
    false

/-- True iff no non-ended loan in `loans` has an active backward target edge to
`.parentLoan lid`. Untaken branches of `.choice` targets with a concrete
condition are ignored (`activeTargetLeaves`): the child's permission lives only
in the selected owner, so it does not depend on `lid`. Both branches of a
symbolic choice still count. -/
def noActiveChildLoanEdgesIn {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (loans : List (LoanEntry Val)) : Bool :=
  loans.foldr
    (fun e ih =>
      let isNonEnded :=
        match e.phase with
        | .ended => false
        | _ => true
      if isNonEnded && hasParentLoanEdge lid (activeTargetLeaves alg e.target)
      then
        false
      else
        ih)
    true

/-- Conservative variant of `noActiveChildLoanEdgesIn` that counts every
serialized leaf of each non-ended child's target, for callers without a value
algebra. -/
def noActiveChildLoanEdges {Val : Type} (lid : LoanId)
    (loans : List (LoanEntry Val)) : Bool :=
  loans.foldr
    (fun e ih =>
      let isNonEnded :=
        match e.phase with
        | .ended => false
        | _ => true
      if isNonEnded && hasParentLoanEdge lid (targetLeaves e.target) then
        false
      else
        ih)
    true

/-- True iff no active region group in `rgs` has an input target edge to
`.parentLoan lid`. -/
def noActiveChildRegionEdges {Val : Type} (lid : LoanId)
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  rgs.foldr
    (fun rg ih =>
      if rg.active && hasParentLoanEdge lid rg.inputTargets then
        false
      else
        ih)
    true

/-- Deactivate loan `lid` in a single pass, verifying that `lid` is unique in
`loans`, has no active child borrows (`isUnborrowed cellPerm` and
`noActiveChildLoanEdgesIn alg lid loans`), contains no `.regionOut` or
`.rootParam`
target, and is currently active (`phase.isActive`). -/
def deactivateLoan {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (loans : List (LoanEntry Val)) :
    Option (LoanEntry Val × List (LoanEntry Val)) :=
  if !noActiveChildLoanEdgesIn alg lid loans then none
  else
    match
      loans.foldr
        (fun e (acc : Bool × Option (LoanEntry Val) × List (LoanEntry Val)) =>
          match e, acc with
          | ⟨id, phase, ⟨cellVal, cellPerm⟩, target⟩, (dup, foundOpt, rest) =>
            if id == lid then
              match foundOpt with
              | some _ => (true, foundOpt, rest)
              | none =>
                if !isUnborrowed cellPerm ||
                   activeTargetHasSpecial alg target || !phase.isActive then
                  (true, none, rest)
                else
                  (dup,
                   some ⟨id, phase, ⟨cellVal, cellPerm⟩, target⟩,
                   ⟨id, .ended, ⟨cellVal, cellPerm⟩, target⟩ :: rest)
            else
              (dup, foundOpt,
               ⟨id, phase, ⟨cellVal, cellPerm⟩, target⟩ :: rest))
        (false, none, [])
    with
    | (false, some found, updated) => some (found, updated)
    | _ => none

/-- End active loan `lid` and propagate its backward writeback through the loan
graph, supporting `.direct`, `.lensCall`, and nested `.choice` targets. -/
def endLoanInState {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (st : SymState Val) : EvalOutcome (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    if !noActiveChildRegionEdges lid rgs then .fail
    else
      match deactivateLoan alg lid loans with
      | none => .fail
      | some (⟨_, phase, ⟨cellVal, _⟩, target⟩, loansDeact) =>
        let stDeact : SymState Val := ⟨locals, loansDeact, rgs, deps, sp, tag⟩
        match phase with
        | .activeShared =>
          if !validateSharedBackTarget alg target then .fail
          else
            let leaves := dedupOwnerPaths (targetLeaves target)
            let activeLeaves := activeTargetLeaves alg target
            match releaseSharedLeaves alg lid activeLeaves leaves stDeact with
            | some st' =>
              if noResidualLoanPerm lid st' then .ok st' else .fail
            | none => .fail
        | .activeMut =>
          if !validateBackTarget alg target cellVal then .fail
          else
            let leaves := dedupOwnerPaths (targetLeaves target)
            match writebackLeaves alg lid target cellVal leaves stDeact with
            | some st' =>
              if noResidualLoanPerm lid st' then .ok st' else .fail
            | none => .fail
        | .spatialPinned _ _ => .fail
        | .ended => .fail

/-- End a sequence of loans in order. -/
def endLoansInState {Val : Type} (alg : ValAlgebra Val)
    (lids : List LoanId) (st : SymState Val) : EvalOutcome (SymState Val) :=
  lids.foldr
    (fun lid ih st0 =>
      match endLoanInState alg lid st0 with
      | .ok st1 => ih st1
      | .fail => .fail)
    (fun st0 => .ok st0)
    st

/-- Count occurrences of region group ID `gid` in `rgs`. -/
def countRegionGroupId {Val : Type} (gid : RegionGroupId)
    (rgs : List (RegionGroupEntry Val)) : Nat :=
  rgs.foldr (fun g ih => if g.groupId == gid then ih + 1 else ih) 0

/-- True iff `gid` occurs exactly once in `rgs`. -/
def hasUniqueRegionGroupId {Val : Type} (gid : RegionGroupId)
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  countRegionGroupId gid rgs == 1

/-- Look up region group `gid`. -/
def findRegionGroup {Val : Type} (gid : RegionGroupId)
    (rgs : List (RegionGroupEntry Val)) : Option (RegionGroupEntry Val) :=
  rgs.foldr
    (fun g ih => if g.groupId == gid then some g else ih)
    none

/-- Update region group `gid`. -/
def updateRegionGroup {Val : Type} (gid : RegionGroupId)
    (f : RegionGroupEntry Val → RegionGroupEntry Val)
    (rgs : List (RegionGroupEntry Val)) : List (RegionGroupEntry Val) :=
  rgs.foldr
    (fun g ih => if g.groupId == gid then f g :: ih else g :: ih)
    []

def isRegionGroupEnded {Val : Type} (gid : RegionGroupId)
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  if !hasUniqueRegionGroupId gid rgs then false
  else
    match findRegionGroup gid rgs with
    | some g => !g.active
    | none => false

def allRequiredGroupsEnded {Val : Type} (rgs : List (RegionGroupEntry Val))
    (reqIds : List RegionGroupId) : Bool :=
  reqIds.foldr
    (fun gid ih => isRegionGroupEnded gid rgs && ih)
    true

/-- Retire all output loans of region group `gid`, verifying that each output
loan at position `expectedIdx` is unique in `st.loans`, is currently
`.activeMut`, has no active child sub-borrows (`isUnborrowed e.cell.perm`,
`noActiveChildLoanEdgesIn`, and `noActiveChildRegionEdges`), and has target
`.regionOut gid expectedIdx`. -/
def collectAndRetireOutputLoans {Val : Type} (alg : ValAlgebra Val)
    (gid : RegionGroupId) (expectedIdx : Nat) (outLids : List LoanId)
    (st : SymState Val) : Option (List Val × SymState Val) :=
  outLids.foldr
    (β := Nat → SymState Val → Option (List Val × SymState Val))
    (fun olid ih idx st0 =>
      if !hasUniqueLoanId olid st0.loans ||
         !noActiveChildLoanEdgesIn alg olid st0.loans ||
         !noActiveChildRegionEdges olid st0.regionGroups then
        none
      else
        match findLoan olid st0.loans with
        | none => none
        | some e =>
          if !e.phase.isActiveMut || !isUnborrowed e.cell.perm ||
             !isMatchingRegionOut gid idx e.target then
            none
          else
            let st1 : SymState Val :=
              match st0 with
              | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
                ⟨locals,
                  updateLoan olid
                    (fun x => ⟨x.id, .ended, x.cell, x.target⟩) loans,
                  rgs, deps, sp, tag⟩
            match ih (idx + 1) st1 with
            | some (vals, st2) => some (e.cell.val :: vals, st2)
            | none => none)
    (fun _ st0 => some ([], st0))
    expectedIdx st

def releaseLoanListPermAtPath (lids : List LoanId) (path : SubPath)
    (p : PermTree) : PermTree :=
  lids.foldr
    (fun lid ih p0 => ih (releaseLoanPermAtPath lid path p0))
    (fun p0 => p0)
    p

/-- True iff each loan in `lids` appears at `path` of `perm` only in the
permission flavor its phase in `loans` implies: an `.activeMut` loan must not
appear as a shared permission, and an `.activeShared` loan must not appear as a
mutable one. Region writeback releases every such loan at once, so a
contradictory flavor must be rejected first. -/
def releasedPermFlavorsMatch {Val : Type} (loans : List (LoanEntry Val))
    (lids : List LoanId) (path : SubPath) (perm : PermTree) : Bool :=
  lids.all (fun l =>
    match findLoan l loans with
    | some e =>
      match e.phase with
      | .activeMut => !hasSharedLoanAtPath l path perm
      | .activeShared => !hasMutLoanAtPath l path perm
      | _ => true
    | none => true)

def writebackRegionTargets {Val : Type} (alg : ValAlgebra Val)
    (lockLid : LoanId) (releaseLids : List LoanId)
    (targets : List (OwnerRef × SubPath)) (vals : List Val)
    (st : SymState Val)
    (phaseLoans : Option (List (LoanEntry Val)) := none) :
    Option (SymState Val) :=
  -- Handles may move between the written places, but not multiply.
  if !targetsReplaceable alg targets vals st then none
  else
  targets.foldr
    (fun op ih vs st0 =>
      match op, vs with
      | (owner, path), vUpd :: restVals =>
        if !ownerExists owner st0 ||
           liveLoanTargetsOverlap alg releaseLids owner path st0.loans
             st0.regionGroups then none
        else
        match modifyOwner alg owner true (fun ownerVal ownerPerm =>
          -- As in `writebackLeaf`, the lock must be held only as a mutable
          -- loan: a `lockLid` that also appears in the shared half of a
          -- `.mutJoined` permission is a contradictory borrow state. Every
          -- other released loan must likewise appear only in the flavor its
          -- phase implies before its permission is removed.
          if !hasMutLoanAtPath lockLid path ownerPerm ||
             hasSharedLoanAtPath lockLid path ownerPerm ||
             !releasedPermFlavorsMatch
               (match phaseLoans with
                | some ls => ls
                | none => st0.loans)
               releaseLids path ownerPerm then
            none
          else
            match putPath alg path ownerVal vUpd with
            | some ownerVal' =>
              some (ownerVal',
                    releaseLoanListPermAtPath releaseLids path ownerPerm)
            | none => none) st0 with
        | some st1 => ih restVals st1
        | none => none
      | _, [] => none)
    (fun vs st0 =>
      match vs with
      | [] => some st0
      | _ :: _ => none)
    vals st

/-- Split `deps` into the values deposited by the groups in `children` and the
remaining deposits. The values are ordered by their producer's position in
`children` and then by deposit order, so the result does not depend on the
order in which independent groups ended. A child listed twice contributes its
deposits once. Taken deposits are consumed, so if several groups require the
same child, only the first of them to end receives the child's deposits. -/
def takeChildDeposits {Val : Type} (children : List RegionGroupId)
    (deps : List (RegionGroupId × Val)) :
    List Val × List (RegionGroupId × Val) :=
  children.foldl
    (fun (acc : List Val × List (RegionGroupId × Val)) c =>
      match acc with
      | (taken, rest) =>
        (taken ++ (rest.filter (fun d => d.1 == c)).map (fun d => d.2),
         rest.filter (fun d => d.1 != c)))
    ([], deps)

/-- End multi-region group `gid`, enforcing uniqueness of `gid` in
`st.regionGroups`, `requiredChildren` outlives order, pairwise-disjoint
`inputTargets`, unborrowed output loans with matching `.regionOut gid idx`
targets, and backward lens propagation across `inputTargets`. The backward
function receives only the deposits of the group's `requiredChildren`
(`takeChildDeposits`), which are consumed; its own deposits are tagged with
`gid`. -/
def endRegionGroupInState {Val : Type} (alg : ValAlgebra Val)
    (gid : RegionGroupId) (st : SymState Val) : EvalOutcome (SymState Val) :=
  if !hasUniqueRegionGroupId gid st.regionGroups then .fail
  else
    match findRegionGroup gid st.regionGroups with
  | none => .fail
  | some g =>
    -- Deposits are consumed by the first group that ends, so another active
    -- group requiring one of the same children would silently receive none.
    let childShared : Bool :=
      st.regionGroups.any (fun o =>
        o.groupId != gid && o.active &&
          o.requiredChildren.any (fun c =>
            g.requiredChildren.any (fun c' => c' == c)))
    if !g.active || !ownerPathsDisjoint g.inputTargets ||
       !allRequiredGroupsEnded st.regionGroups g.requiredChildren ||
       childShared then
      .fail
    else
      match collectAndRetireOutputLoans alg gid 0 g.outputLoans st with
      | none => .fail
      | some (outVals, stRetired) =>
        let childSplit :=
          takeChildDeposits g.requiredChildren stRetired.regionDeposits
        match g.backFn outVals childSplit.1 with
        | none => .fail
        | some (updatedInputs, newDeposits) =>
          -- Newly deposited values must not fabricate or duplicate non-copyable
          -- handles that were not present in the retired outputs or child
          -- deposits.
          if !replaceableVals alg stRetired.loans
               (outVals ++ childSplit.1) newDeposits then
            .fail
          else
          -- Output loans are already `.ended` in `stRetired`, so their
          -- permission flavors are checked against the pre-retirement phases
          -- in `st.loans`.
          match writebackRegionTargets alg g.lockLid
                  (g.lockLid :: g.outputLoans)
                  g.inputTargets updatedInputs stRetired (some st.loans) with
          | none => .fail
          | some stWritten =>
            if !noResidualLoanListPerm (g.lockLid :: g.outputLoans) stWritten then
              .fail
            else
              match stWritten with
              | ⟨locals, loans, rgs, _, sp, tag⟩ =>
                let rgs' := updateRegionGroup gid
                  (fun x => ⟨x.groupId, false, x.lockLid, x.inputTargets,
                             x.outputLoans, x.requiredChildren, x.backFn⟩)
                  rgs
                .ok ⟨locals, loans, rgs',
                     childSplit.2 ++ newDeposits.map (fun v => (gid, v)), sp,
                     tag⟩

/-- End a list of region groups in order. -/
def endRegionGroupsInState {Val : Type} (alg : ValAlgebra Val)
    (gids : List RegionGroupId) (st : SymState Val) :
    EvalOutcome (SymState Val) :=
  gids.foldr
    (fun gid ih st0 =>
      match endRegionGroupInState alg gid st0 with
      | .ok st1 => ih st1
      | .fail => .fail)
    (fun st0 => .ok st0)
    st

/-- Extract `some paramIdx` if `t` is a root parameter backward target
(`.rootParam paramIdx`), or `none` otherwise. -/
def rootParamIdxOpt {Val : Type} (t : BackTarget Val) : Option Nat :=
  match t.steps with
  | [.rootParam idx] => some idx
  | _ => none

/-- True iff `t` is a root parameter backward target (`.rootParam paramIdx`). -/
def isRootTarget {Val : Type} (t : BackTarget Val) : Bool :=
  match rootParamIdxOpt t with
  | some _ => true
  | none => false

/-- Count how many entries in `loans` have backward target `.rootParam idx`. -/
def countRootParamIdx {Val : Type} (idx : Nat)
    (loans : List (LoanEntry Val)) : Nat :=
  loans.foldr
    (fun e ih =>
      match rootParamIdxOpt e.target with
      | some i => if i == idx then ih + 1 else ih
      | none => ih)
    0

/-- Insert `(idx, val)` into an ascending-index-sorted list of `(paramIdx, Val)`
pairs. -/
def insertRootMutByIdx {Val : Type} (idx : Nat) (v : Val)
    (sorted : List (Nat × Val)) : List (Nat × Val) :=
  sorted.foldr
    (fun (curIdx, curVal) ih =>
      match ih with
      | [] => [(curIdx, curVal), (idx, v)]
      | (headIdx, headVal) :: tail =>
        if Nat.ble idx curIdx then
          (idx, v) :: (curIdx, curVal) :: tail
        else
          (curIdx, curVal) :: (headIdx, headVal) :: tail)
    [(idx, v)]

/-- True iff every loan ID in `loans` is unique, every root parameter loan in
`loans` has a unique `.rootParam idx` index and is active with no active child
borrows (`isUnborrowed e.cell.perm`), and every non-root loan has ended. -/
def loansCleanAtReturn {Val : Type}
    (loans : List (LoanEntry Val)) : Bool :=
  loans.foldr
    (fun e ih =>
      let okHere : Bool :=
        if !hasUniqueLoanId e.id loans then false
        else
          match rootParamIdxOpt e.target with
          | some idx =>
            e.phase.isActive && isUnborrowed e.cell.perm &&
            countRootParamIdx idx loans == 1
          | none =>
            e.phase.isEnded
      okHere && ih)
    true

/-- True iff all region groups in `rgs` have ended (`!g.active`). -/
def allRegionGroupsEnded {Val : Type}
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  rgs.foldr
    (fun g ih => !g.active && ih)
    true

/-- True iff every region group in `rgs` has ended and no two share a
`groupId`, checked in a single pass so the return predicate inspects
`regionGroups` once. -/
def allRegionGroupsEndedUnique {Val : Type}
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  (rgs.foldr
    (fun g (acc : Bool × List RegionGroupId) =>
      match acc with
      | (ok, seen) =>
        (ok && !g.active && !seen.contains g.groupId, g.groupId :: seen))
    (true, [])).1

/-- True iff all non-root loans and region groups have ended, root parameter
loans have unique IDs, unique parameter indices, and no active child borrows,
no spatial blocks remain pinned, no local or loan cell retains any borrow
permission, and no region deposit is left unconsumed (a leftover deposit is a
backward result that no parent group received). -/
def stateCleanAtReturn {Val : Type} (st : SymState Val) : Bool :=
  loansCleanAtReturn st.loans &&
  allRegionGroupsEndedUnique st.regionGroups &&
  st.spatial.isEmpty &&
  st.regionDeposits.isEmpty &&
  -- Every non-root loan has ended, so no local and no loan cell may still
  -- carry a borrow permission; a stale permission means an inconsistent
  -- borrow state that must not reach the return boundary.
  st.locals.all (fun c => isUnborrowed c.perm) &&
  st.loans.all (fun e => isUnborrowed e.cell.perm)

/-- Collect the final values of all root `&mut` parameter loans sorted in
ascending parameter index order (`.rootParam paramIdx`). -/
def collectRootMutVals {Val : Type}
    (loans : List (LoanEntry Val)) : List Val :=
  let sortedPairs : List (Nat × Val) :=
    loans.foldr
      (fun e ih =>
        match e.phase, rootParamIdxOpt e.target with
        | .activeMut, some idx => insertRootMutByIdx idx e.cell.val ih
        | _, _ => ih)
      []
  sortedPairs.map Prod.snd

/-- Finalize function return from `st` with direct return value `retVal`,
verifying `stateCleanAtReturn st` and pairing `retVal` with
`collectRootMutVals st.loans`. -/
def finalizeRootReturn {Val : Type} (retVal : Val) (st : SymState Val) :
    EvalOutcome (FuncOut Val) :=
  if !stateCleanAtReturn st then .fail
  else .ok ⟨retVal, collectRootMutVals st.loans⟩

/-!
## Exhaustive Kernel-Checked Tests for `LoanGraph`
-/

/-- Local register access (`listGetVal`, `getLocal`, `setLocalChecked`,
`modifyLocalAt`, `modifyLocalAtRes`) is exact for local indices above eight
(`8`, `9`, `12`, `15`) and never aliases local `12` to local `8`. Writes may
overwrite an existing local or append exactly one past the end, but never pad
skipped slots, and reading a slot that was never written fails. -/
theorem loanGraph_locals_above_eight_no_aliasing :
    let set (reg : LocalId) (v : LensTestVal) (st : SymState LensTestVal) :
        SymState LensTestVal :=
      match setLocalChecked lensTestValAlg reg v st with
      | some st' => st'
      | none => st
    let st0 : SymState LensTestVal :=
      ⟨List.replicate 12 ⟨.atom 0, .unborrowed⟩, [], [], [], [], 0⟩
    let st1 := set 8 (.atom 80) st0
    let st2 := set 9 (.atom 90) st1
    let st3 := set 12 (.atom 120) st2
    let st4 := set 13 (.atom 130) st3
    let st5 := set 14 (.atom 140) st4
    let st6 := set 15 (.atom 150) st5
    getLocal lensTestValAlg 0 st6 = .atom 0 ∧
    getLocal lensTestValAlg 8 st6 = .atom 80 ∧
    getLocal lensTestValAlg 9 st6 = .atom 90 ∧
    getLocal lensTestValAlg 12 st6 = .atom 120 ∧
    getLocal lensTestValAlg 15 st6 = .atom 150 ∧
    -- No padding: a write two or more slots past the end fails, and the
    -- never-written slot is unreadable.
    setLocalChecked lensTestValAlg 20 (.atom 1) st6 = none ∧
    getOwnerForRead lensTestValAlg (.localReg 20) st6 = none ∧
    getOwnerForRead lensTestValAlg (.localReg 16) st6 = none ∧
    (getOwnerForRead lensTestValAlg (.localReg 15) st6).map PlaceCell.val =
      some (.atom 150) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Balanced `.choice` tree with 16 distinct leaves used to verify that
`targetLeaves` and `dedupOwnerPaths` preserve all 16 leaves without
truncation. -/
def choiceTree16 : BackTarget LensTestVal :=
  let c := LensTestVal.atom 1
  let pair (i : Nat) : BackTarget LensTestVal :=
    .choice c (.direct (.localReg (2 * i)) [])
              (.direct (.localReg (2 * i + 1)) [])
  let quad (j : Nat) : BackTarget LensTestVal :=
    .choice c (pair (2 * j)) (pair (2 * j + 1))
  let oct (k : Nat) : BackTarget LensTestVal :=
    .choice c (quad (2 * k)) (quad (2 * k + 1))
  .choice c (oct 0) (oct 1)

theorem dedupOwnerPaths_preserves_all_sixteen_leaves :
    (targetLeaves choiceTree16).length = 16 ∧
    (dedupOwnerPaths (targetLeaves choiceTree16)).length = 16 :=
  ⟨rfl, rfl⟩

/-- `isRegionOutTarget` detects `.regionOut` targets nested inside `.choice`
trees. `deactivateLoan` rejects ordinary `endLoanInState` when such a target
lies in an active branch (here, under a symbolic condition), but ignores it in
the untaken branch of a concrete choice. -/
theorem nested_regionOut_under_choice_rejected :
    let mkTarget (c : LensTestVal) : BackTarget LensTestVal :=
      .choice (.atom 1)
        (.direct (.localReg 0) [])
        (.choice c (.direct (.localReg 1) []) (.regionOut 0 0))
    let mkSt (c : LensTestVal) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .unborrowed⟩]
        loans := [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩, mkTarget c⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let symTarget : BackTarget LensTestVal :=
      .choice (.node (.atom 0) (.atom 1))
        (.direct (.localReg 0) []) (.regionOut 0 0)
    isRegionOutTarget (mkTarget (.atom 0)) = true ∧
    activeTargetHasSpecial lensTestValAlg (mkTarget (.atom 0)) = false ∧
    activeTargetHasSpecial lensTestValAlg symTarget = true ∧
    activeTargetHasSpecial lensTestValAlg
      (.choice (.atom 0) (.direct (.localReg 0) []) (.rootParam 0)) = true ∧
    (match endLoanInState lensTestValAlg 0 (mkSt (.atom 0)) with
     | .ok st' => getLocal lensTestValAlg 0 st' = .atom 99
     | .fail => False) ∧
    endLoanInState lensTestValAlg 0
      { mkSt (.atom 0) with
        loans := [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩, symTarget⟩] } =
      .fail :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `endLoanInState` executes backward lenses when `.lensCall` is nested inside
a `.choice` tree, propagating the branch-selected lens writeback to the owner
locals. -/
theorem nested_lensCall_under_choice_executes_writeback (cond : Bool) :
    let condVal : LensTestVal := .atom (if cond then 1 else 0)
    let tTrue : BackTarget LensTestVal :=
      .lensCall [(.localReg 0, [])]
        (fun v =>
          match v with
          | ⟨_, .atom n⟩ => some [.atom (n + 100)]
          | _ => none)
    let tFalse : BackTarget LensTestVal :=
      .lensCall [(.localReg 1, [])]
        (fun v =>
          match v with
          | ⟨_, .atom n⟩ => some [.atom (n + 200)]
          | _ => none)
    let choiceTarget : BackTarget LensTestVal := .choice condVal tTrue tFalse
    let st : SymState LensTestVal :=
      { locals := [⟨.atom 1, .mutLocked 0⟩, ⟨.atom 2, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 5, .unborrowed⟩, choiceTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    match endLoanInState lensTestValAlg 0 st with
    | .ok st' =>
      getLocal lensTestValAlg 0 st' =
        (if cond then .atom 105 else .atom 1) ∧
      getLocal lensTestValAlg 1 st' =
        (if cond then .atom 2 else .atom 205) ∧
      getLocalPerm lensTestValAlg 0 st' = .unborrowed ∧
      getLocalPerm lensTestValAlg 1 st' = .unborrowed
    | .fail => False := by
  cases cond <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- `endRegionGroupInState` rejects a region group whose `outputLoans` list
references a loan belonging to a different group ID or wrong output index. -/
theorem regionGroup_rejects_mismatched_output_loan_target :
    let rgWrongGroup : RegionGroupEntry LensTestVal :=
      { groupId := 0
        active := true
        lockLid := 0
        inputTargets := [(.localReg 0, [])]
        outputLoans := [0]
        requiredChildren := []
        backFn := fun outs _ => some (outs, []) }
    let stWrongGroup : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩, .regionOut 1 0⟩]
        regionGroups := [rgWrongGroup]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stWrongIdx : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩, .regionOut 0 1⟩]
        regionGroups := [rgWrongGroup]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    endRegionGroupInState lensTestValAlg 0 stWrongGroup = .fail ∧
    endRegionGroupInState lensTestValAlg 0 stWrongIdx = .fail :=
  ⟨rfl, rfl⟩

/-- `endLoanInState` and `endRegionGroupInState` reject mutable writeback into
an `.activeShared` parent loan (`reqMut = true` in `writebackLeaf`,
`writebackLensTargets`, and `writebackRegionTargets`). -/
theorem writeback_rejects_activeShared_parent_loan :
    let stDirect : SymState LensTestVal :=
      { locals := [⟨.atom 10, .shared [0]⟩]
        loans :=
          [ ⟨0, .activeShared, ⟨.atom 10, .mutLocked 1⟩,
              .direct (.localReg 0) []⟩,
            ⟨1, .activeMut, ⟨.atom 99, .unborrowed⟩,
              .direct (.parentLoan 0) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let rgOnSharedParent : RegionGroupEntry LensTestVal :=
      { groupId := 0
        active := true
        lockLid := 1
        inputTargets := [(.parentLoan 0, [])]
        outputLoans := [2]
        requiredChildren := []
        backFn := fun outs _ => some (outs, []) }
    let stRegion : SymState LensTestVal :=
      { locals := [⟨.atom 10, .shared [0]⟩]
        loans :=
          [ ⟨0, .activeShared, ⟨.atom 10, .mutJoined [1] [2]⟩,
              .direct (.localReg 0) []⟩,
            ⟨2, .activeMut, ⟨.atom 77, .unborrowed⟩, .regionOut 0 0⟩ ]
        regionGroups := [rgOnSharedParent]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    endLoanInState lensTestValAlg 1 stDirect = .fail ∧
    endRegionGroupInState lensTestValAlg 0 stRegion = .fail :=
  ⟨rfl, rfl⟩

/-- Exhaustive unit tests for `OwnerRef.beq`, `LoanPhase` predicates
(`isActive`, `isActiveMut`, `isEnded`, `samePhase`), `hasUninitCell`,
`lookupLensTargetVal`, `validateBackTarget`, and `evalBackVal`. -/
theorem loanPhase_and_backTarget_helpers_exhaustive_tests :
    let dummyCodec : SpatialCodec LensTestVal :=
      { codecId := 0
        encode := fun v => [.init v]
        decode := fun cs => match cs with | [.init v] => some v | _ => none
        decode_encode := fun _ => rfl }
    let pSh : LoanPhase LensTestVal := .activeShared
    let pMut : LoanPhase LensTestVal := .activeMut
    let pPin : LoanPhase LensTestVal := .spatialPinned 0 dummyCodec
    let pEnd : LoanPhase LensTestVal := .ended
    OwnerRef.beq (.localReg 1) (.localReg 1) = true ∧
    OwnerRef.beq (.localReg 1) (.localReg 2) = false ∧
    OwnerRef.beq (.parentLoan 1) (.parentLoan 1) = true ∧
    OwnerRef.beq (.localReg 1) (.parentLoan 1) = false ∧
    pSh.isActive = true ∧
    pSh.isActiveMut = false ∧
    pSh.isEnded = false ∧
    pMut.isActive = true ∧
    pMut.isActiveMut = true ∧
    pMut.isEnded = false ∧
    pPin.isActive = false ∧
    pPin.isActiveMut = false ∧
    pPin.isEnded = false ∧
    pEnd.isActive = false ∧
    pEnd.isActiveMut = false ∧
    pEnd.isEnded = true ∧
    LoanPhase.samePhase pSh pSh = true ∧
    LoanPhase.samePhase pMut pMut = true ∧
    LoanPhase.samePhase pEnd pEnd = true ∧
    LoanPhase.samePhase pSh pMut = false ∧
    LoanPhase.samePhase pPin pPin = false ∧
    hasUninitCell ([.init (.atom 1), .rawByte 2] :
      List (CellVal LensTestVal)) = false ∧
    hasUninitCell ([.init (.atom 1), .uninit] :
      List (CellVal LensTestVal)) = true ∧
    validateBackTarget lensTestValAlg (.rootParam 0 : BackTarget LensTestVal)
      (.atom 1) = false ∧
    validateBackTarget lensTestValAlg (.regionOut 0 0 : BackTarget LensTestVal)
      (.atom 1) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exhaustive unit tests for `getOwnerForRead`, `getOwnerForMut`,
`endLoanInState`, `endLoansInState`, `endRegionGroupInState`, and
`endRegionGroupsInState` across shared, mutable, child-locked, and multi-group
hierarchies. -/
theorem loanGraph_lifecycle_and_regionGroups_exhaustive_tests :
    let stSharedAndChild : SymState LensTestVal :=
      { locals := [⟨.atom 10, .shared [0]⟩, ⟨.atom 20, .mutLocked 1⟩]
        loans :=
          [ ⟨0, .activeShared, ⟨.atom 10, .unborrowed⟩,
              .direct (.localReg 0) []⟩
          , ⟨1, .activeMut, ⟨.atom 20, .mutLocked 2⟩,
              .direct (.localReg 1) []⟩
          , ⟨2, .activeMut, ⟨.atom 99, .unborrowed⟩,
              .direct (.parentLoan 1) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    -- 1. `.activeShared` owner allows read lookup (`getOwnerForRead`) and
    -- rejects mut lookup (`getOwnerForMut`):
    (match getOwnerForRead lensTestValAlg (.parentLoan 0) stSharedAndChild with
     | some _ => true
     | none => false) = true ∧
    getOwnerForMut lensTestValAlg (.parentLoan 0) stSharedAndChild = none ∧
    -- 2. Ending parent loan `1` before child loan `2` fails; ending `[0, 2, 1]`
    -- in child-first order via `endLoansInState` succeeds and writes `.atom 99`
    -- back to local `1`:
    endLoanInState lensTestValAlg 1 stSharedAndChild = .fail ∧
    (match endLoansInState lensTestValAlg [0, 2, 1] stSharedAndChild with
     | .ok stDone =>
       getLocal lensTestValAlg 0 stDone = .atom 10 ∧
       getLocal lensTestValAlg 1 stDone = .atom 99 ∧
       getLocalPerm lensTestValAlg 0 stDone = .unborrowed ∧
       getLocalPerm lensTestValAlg 1 stDone = .unborrowed ∧
       -- Ending an already-ended loan fails:
       endLoanInState lensTestValAlg 0 stDone = .fail
     | .fail => False) ∧
    -- 3. Multi-region group hierarchy with `requiredChildren = [1]` on group
    -- `0`: ending `[0, 1]` out of order fails, while ending `[1, 0]` via
    -- `endRegionGroupsInState` succeeds; the parent consumes the child's
    -- deposit and leaves its own, tagged with `0`:
    let rgParent : RegionGroupEntry LensTestVal :=
      { groupId := 0
        active := true
        lockLid := 0
        inputTargets := [(.localReg 0, [])]
        outputLoans := [0]
        requiredChildren := [1]
        backFn := fun outs _ =>
          match outs with
          | [⟨_, .atom v⟩] => some ([.atom (v + 1)], [.atom 900])
          | _ => none }
    let rgChild : RegionGroupEntry LensTestVal :=
      { groupId := 1
        active := true
        lockLid := 1
        inputTargets := [(.localReg 1, [])]
        outputLoans := [1]
        requiredChildren := []
        backFn := fun outs _ =>
          match outs with
          | [⟨_, .atom v⟩] => some ([.atom (v + 2)], [.atom 800])
          | _ => none }
    let stRg : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .mutLocked 1⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 30, .unborrowed⟩, .regionOut 0 0⟩
          , ⟨1, .activeMut, ⟨.atom 40, .unborrowed⟩, .regionOut 1 0⟩ ]
        regionGroups := [rgParent, rgChild]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    endRegionGroupsInState lensTestValAlg [0, 1] stRg = .fail ∧
    (match endRegionGroupsInState lensTestValAlg [1, 0] stRg with
     | .ok stRgDone =>
       getLocal lensTestValAlg 0 stRgDone = .atom 31 ∧
       getLocal lensTestValAlg 1 stRgDone = .atom 42 ∧
       stRgDone.regionDeposits = [(0, .atom 900)] ∧
       endRegionGroupInState lensTestValAlg 0 stRgDone = .fail
     | .fail => False) ∧
    -- 4. `validateBackTarget` rejects `.lensCall` with duplicate or overlapping
    -- `(owner, path)` targets, and `endLoanInState` / `endRegionGroupInState`
    -- reject ending a loan whose owner `PermTree` does not hold the loan at
    -- `path`:
    let dupLensTarget : BackTarget LensTestVal :=
      .lensCall [(.localReg 0, []), (.localReg 0, [0])]
        (fun v => some [v, v])
    let stUnownedMut : SymState LensTestVal :=
      { locals := [⟨.atom 10, .unborrowed⟩]
        loans :=
          [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩,
            .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stUnownedShared : SymState LensTestVal :=
      { locals := [⟨.atom 10, .unborrowed⟩]
        loans :=
          [⟨0, .activeShared, ⟨.atom 10, .unborrowed⟩,
            .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    validateBackTarget lensTestValAlg dupLensTarget (.atom 1) = false ∧
    endLoanInState lensTestValAlg 0 stUnownedMut = .fail ∧
    endLoanInState lensTestValAlg 0 stUnownedShared = .fail ∧
    -- 5. Multi-leaf `.choice`, `.lensCall`, and `RegionGroup` writebacks to
    -- disjoint sub-paths of the same owner (`[0]` and `[1]`) succeed because
    -- `releaseLoanPermAtPath` releases only the target sub-path at each step:
    let stChoiceSplit : SymState LensTestVal :=
      { locals :=
          [⟨.node (.atom 1) (.atom 2),
            .split [([0], .mutLocked 0), ([1], .mutLocked 0)]⟩]
        loans :=
          [⟨0, .activeMut, ⟨.atom 55, .unborrowed⟩,
            .choice (.atom 1)
              (.direct (.localReg 0) [0])
              (.direct (.localReg 0) [1])⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stLensSplit : SymState LensTestVal :=
      { locals :=
          [⟨.node (.atom 1) (.atom 2),
            .split [([0], .mutLocked 0), ([1], .mutLocked 0)]⟩]
        loans :=
          [⟨0, .activeMut, ⟨.atom 55, .unborrowed⟩,
            .lensCall [(.localReg 0, [0]), (.localReg 0, [1])]
              (fun _ => some [.atom 11, .atom 22])⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stDupLoanId : SymState LensTestVal :=
      { locals := [⟨.atom 1, .mutLocked 0⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 2, .unborrowed⟩, .direct (.localReg 0) []⟩
          , ⟨0, .activeMut, ⟨.atom 3, .unborrowed⟩, .direct (.localReg 0) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stBadSharedTarget : SymState LensTestVal :=
      { locals := [⟨.atom 1, .shared [0]⟩]
        loans :=
          [⟨0, .activeShared, ⟨.atom 1, .unborrowed⟩, dupLensTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stParentSplit : SymState LensTestVal :=
      { locals := [⟨.node (.atom 1) (.atom 2), .mutLocked 0⟩]
        loans :=
          [⟨0, .activeMut,
            ⟨.node (.atom 1) (.atom 2), .split [([0], .mutLocked 1)]⟩,
            .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stRootParamLoan : SymState LensTestVal :=
      { locals := []
        loans :=
          [⟨0, .activeMut, ⟨.atom 42, .unborrowed⟩, .rootParam 0⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stChoicePartialLens : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .unborrowed⟩]
        loans :=
          [⟨0, .activeMut, ⟨.atom 77, .unborrowed⟩,
            .choice (.atom 1)
              (.lensCall [(.localReg 0, [])]
                (fun v =>
                  match v with
                  | ⟨_, .atom 77⟩ => some [.atom 88]
                  | _ => none))
              (.lensCall [(.localReg 1, [])]
                (fun _ => none))⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let symCond : LensTestVal := .ref 99 []
    let stChoiceSymbolicLens : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .mutLocked 0⟩]
        loans :=
          [⟨0, .activeMut,
            ⟨lensTestValAlg.zipVal symCond (.atom 70) (.atom 80), .unborrowed⟩,
            .choice symCond
              (.lensCall [(.localReg 0, [])]
                (fun v =>
                  match v with
                  | ⟨_, .atom 70⟩ => some [.atom 71]
                  | _ => none))
              (.lensCall [(.localReg 1, [])]
                (fun v =>
                  match v with
                  | ⟨_, .atom 80⟩ => some [.atom 81]
                  | _ => none))⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stDupRegionGroup : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .mutLocked 1⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 30, .unborrowed⟩, .regionOut 0 0⟩
          , ⟨1, .activeMut, ⟨.atom 40, .unborrowed⟩, .regionOut 1 0⟩ ]
        regionGroups := [rgChild, rgChild]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stDupRegionOutLoan : SymState LensTestVal :=
      { locals := [⟨.atom 20, .mutLocked 1⟩]
        loans :=
          [ ⟨1, .activeMut, ⟨.atom 40, .unborrowed⟩, .regionOut 1 0⟩
          , ⟨1, .activeMut, ⟨.atom 41, .unborrowed⟩, .regionOut 1 0⟩ ]
        regionGroups := [rgChild]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    (match endLoanInState lensTestValAlg 0 stChoiceSplit with
     | .ok stC =>
       getLocal lensTestValAlg 0 stC = .node (.atom 55) (.atom 2) ∧
       getLocalPerm lensTestValAlg 0 stC = .unborrowed
     | .fail => False) ∧
    (match endLoanInState lensTestValAlg 0 stLensSplit with
     | .ok stL =>
       getLocal lensTestValAlg 0 stL = .node (.atom 11) (.atom 22) ∧
       getLocalPerm lensTestValAlg 0 stL = .unborrowed
     | .fail => False) ∧
    endLoanInState lensTestValAlg 0 stDupLoanId = .fail ∧
    endLoanInState lensTestValAlg 0 stBadSharedTarget = .fail ∧
    endLoanInState lensTestValAlg 0 stRootParamLoan = .fail ∧
    (match endLoanInState lensTestValAlg 0 stChoicePartialLens with
     | .ok stCP =>
       getLocal lensTestValAlg 0 stCP = .atom 88 ∧
       getLocal lensTestValAlg 1 stCP = .atom 20 ∧
       getLocalPerm lensTestValAlg 0 stCP = .unborrowed
     | .fail => False) ∧
    (match endLoanInState lensTestValAlg 0 stChoiceSymbolicLens with
     | .ok stCS =>
       getLocal lensTestValAlg 0 stCS =
         lensTestValAlg.zipVal symCond (.atom 71) (.atom 10) ∧
       getLocal lensTestValAlg 1 stCS =
         lensTestValAlg.zipVal symCond (.atom 20) (.atom 81) ∧
       getLocalPerm lensTestValAlg 0 stCS = .unborrowed ∧
       getLocalPerm lensTestValAlg 1 stCS = .unborrowed
     | .fail => False) ∧
    endRegionGroupInState lensTestValAlg 1 stDupRegionGroup = .fail ∧
    endRegionGroupInState lensTestValAlg 1 stDupRegionOutLoan = .fail ∧
    getOwnerForRead lensTestValAlg (.parentLoan 0) stParentSplit [0] = none ∧
    getOwnerForMut lensTestValAlg (.parentLoan 0) stParentSplit [0] = none ∧
    (match getOwnerForMut lensTestValAlg (.parentLoan 0) stParentSplit [1] with
     | some _ => true
     | none => false) = true ∧
    -- 6. Duplicate parent loan IDs are rejected by `modifyLoanAt`,
    -- `modifyLoanAtRes`, `getOwnerForRead`, and `getOwnerForMut`:
    modifyLoanAt 0 true (fun v p => some (v, p)) stDupLoanId.loans = none ∧
    modifyLoanAtRes 0 true (fun v p => some ((), v, p))
      stDupLoanId.loans = none ∧
    getOwnerForRead lensTestValAlg (.parentLoan 0) stDupLoanId = none ∧
    getOwnerForMut lensTestValAlg (.parentLoan 0) stDupLoanId = none ∧
    -- 7. `.choice` targets whose branches target distinct overlapping sub-paths
    -- of the same owner (`[]` and `[0]`) are rejected by `validateBackTarget`,
    -- `validateSharedBackTarget`, and `endLoanInState`:
    let overlapChoiceTarget : BackTarget LensTestVal :=
      .choice symCond
        (.direct (.localReg 0) [])
        (.direct (.localReg 0) [0])
    let stOverlapChoice : SymState LensTestVal :=
      { locals :=
          [⟨.node (.atom 1) (.atom 2),
            .split [([], .mutLocked 0), ([0], .mutLocked 0)]⟩]
        loans :=
          [⟨0, .activeMut, ⟨.node (.atom 9) (.atom 9), .unborrowed⟩,
            overlapChoiceTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    validateBackTarget lensTestValAlg overlapChoiceTarget
      (.node (.atom 9) (.atom 9)) = false ∧
    validateSharedBackTarget lensTestValAlg overlapChoiceTarget = false ∧
    endLoanInState lensTestValAlg 0 stOverlapChoice = .fail ∧
    -- 8. `collectRootMutVals` and `finalizeRootReturn` extract root `&mut`
    -- parameter values sorted by ascending `paramIdx` even when loan entries
    -- appear out of order, and reject duplicate `.rootParam` indices:
    let stOutOfOrderRootParams : SymState LensTestVal :=
      { locals := []
        loans :=
          [ ⟨20, .activeMut, ⟨.atom 200, .unborrowed⟩, .rootParam 2⟩
          , ⟨10, .activeMut, ⟨.atom 100, .unborrowed⟩, .rootParam 0⟩
          , ⟨15, .activeMut, ⟨.atom 150, .unborrowed⟩, .rootParam 1⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stDupRootParamIdx : SymState LensTestVal :=
      { locals := []
        loans :=
          [ ⟨10, .activeMut, ⟨.atom 100, .unborrowed⟩, .rootParam 0⟩
          , ⟨11, .activeMut, ⟨.atom 101, .unborrowed⟩, .rootParam 0⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    -- 9. Concrete `.choice` conditions prune untaken branch leaves before
    -- checking overlap in `validateBackTarget` and `validateSharedBackTarget`:
    let concretePrunedOverlapTarget : BackTarget LensTestVal :=
      .choice (.atom 1)
        (.direct (.localReg 0) [])
        (.direct (.localReg 0) [0])
    -- 10. `endLoanInState` and `endRegionGroupInState` reject retiring a parent
    -- loan that still has an active child loan or active region group edge even
    -- if its `cell.perm` is `.unborrowed`:
    let stForgedUnborrowedParent : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩,
              .direct (.localReg 0) []⟩
          , ⟨1, .activeMut, ⟨.atom 99, .unborrowed⟩,
              .direct (.parentLoan 0) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    collectRootMutVals stRootParamLoan.loans = [.atom 42] ∧
    finalizeRootReturn (.atom 7) stRootParamLoan =
      .ok ⟨.atom 7, [.atom 42]⟩ ∧
    finalizeRootReturn (.atom 7) stOutOfOrderRootParams =
      .ok ⟨.atom 7, [.atom 100, .atom 150, .atom 200]⟩ ∧
    finalizeRootReturn (.atom 7) stDupRootParamIdx = .fail ∧
    validateBackTarget lensTestValAlg concretePrunedOverlapTarget
      (.atom 9) = true ∧
    validateSharedBackTarget lensTestValAlg concretePrunedOverlapTarget = true ∧
    endLoanInState lensTestValAlg 0 stForgedUnborrowedParent = .fail ∧
    finalizeRootReturn (.atom 7) stParentSplit = .fail :=
  ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
   rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
   ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl,
   ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `writebackLeaf`, `writebackLensTargets`, and `releaseSharedLeaves` reject
inactive `.choice` leaves whose owner carries a wrong-kind or overlapping stale
permission for `lid` (`hasAnyLoanOverlappingPath`), while permitting an inactive
leaf whose owner was never locked by `lid` (`.unborrowed`). -/
theorem inactive_choice_leaf_rejects_malformed_owner_perm :
    let choiceTarget : BackTarget LensTestVal :=
      .choice (.atom 1)
        (.direct (.localReg 0) [])
        (.direct (.localReg 1) [])
    -- Valid inactive leaf (`local 1` is `.unborrowed`):
    let stValidInactive : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .unborrowed⟩]
        loans := [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩, choiceTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    -- Malformed inactive leaf (`local 1` has `.shared [0]` on an `.activeMut`
    -- loan `0`):
    let stMalformedInactive : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .shared [0]⟩]
        loans := [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩, choiceTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    (match endLoanInState lensTestValAlg 0 stValidInactive with
     | .ok st' =>
       getLocal lensTestValAlg 0 st' = .atom 99 ∧
       getLocal lensTestValAlg 1 st' = .atom 20
     | .fail => False) ∧
    endLoanInState lensTestValAlg 0 stMalformedInactive = .fail ∧
    -- Concrete `.choice (.atom 0) (.direct (.localReg 0) [])
    -- (.direct (.localReg 0) [0])` selects `[0]` and processes the active leaf
    -- `[0]` before the inactive overlapping leaf `[]`:
    (let sameOwnerChoice : BackTarget LensTestVal :=
       .choice (.atom 0)
         (.direct (.localReg 0) [])
         (.direct (.localReg 0) [0])
     let stSameOwnerActive0 : SymState LensTestVal :=
       { locals :=
           [⟨.node (.atom 10) (.atom 20), .split [([0], .mutLocked 0)]⟩]
         loans := [⟨0, .activeMut, ⟨.atom 55, .unborrowed⟩, sameOwnerChoice⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     let stUndeclaredSiblingPerm : SymState LensTestVal :=
       { locals :=
           [⟨.node (.atom 10) (.atom 20),
             .split [([0], .mutLocked 0), ([1], .mutLocked 0)]⟩]
         loans :=
           [⟨0, .activeMut, ⟨.atom 55, .unborrowed⟩,
             .direct (.localReg 0) [0]⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     (match endLoanInState lensTestValAlg 0 stSameOwnerActive0 with
      | .ok st' =>
        getLocal lensTestValAlg 0 st' = .node (.atom 55) (.atom 20) ∧
        isUnborrowed (getLocalCell lensTestValAlg 0 st').perm = true
      | .fail => False) ∧
     endLoanInState lensTestValAlg 0 stUndeclaredSiblingPerm = .fail) :=
  ⟨⟨rfl, rfl⟩, rfl, ⟨⟨rfl, rfl⟩, rfl⟩⟩

/-- Round 10 regression tests for `LoanGraph`:
1. `writebackRegionTargets` rejects a region lock ID that also appears in the
   shared half of a `.mutJoined` owner permission, while still accepting an
   exclusive `.mutLocked` lock, and
2. `CellVal.rawByte` stores a `UInt8`, so out-of-range raw bytes are not
   representable (`(256 : UInt8) = 0`). -/
theorem round10_loanGraph_regressions_exhaustive_tests :
    -- 1. Contradictory `.mutJoined [5] [5]` lock is rejected; `.mutLocked 5`
    -- is accepted and released:
    (let stJoined : SymState LensTestVal :=
       { locals := [⟨.atom 10, .mutJoined [5] [5]⟩]
         loans := []
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     writebackRegionTargets lensTestValAlg 5 [5] [(.localReg 0, [])]
       [.atom 7] stJoined = none) ∧
    (let stLocked : SymState LensTestVal :=
       { locals := [⟨.atom 10, .mutLocked 5⟩]
         loans := []
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     match writebackRegionTargets lensTestValAlg 5 [5] [(.localReg 0, [])]
         [.atom 7] stLocked with
     | some st' =>
       getLocal lensTestValAlg 0 st' = .atom 7 ∧
       isUnborrowed (getLocalCell lensTestValAlg 0 st').perm = true
     | none => False) ∧
    -- 2. Raw bytes are 8-bit:
    (CellVal.rawByte 256 : CellVal LensTestVal) = .rawByte 0 ∧
    hasUninitCell ([.rawByte 255] : List (CellVal LensTestVal)) = false :=
  ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl⟩

/-- Round 11 regression tests for `LoanGraph`:
1. Region writeback rejects a released output loan whose permission flavor
   contradicts its phase (an `.activeMut` loan in the shared half of
   `.mutJoined`), and accepts the consistent `.activeShared` case,
2. Ending a loan whose concrete choice leaves an inactive leaf naming a missing
   local neither fails nor fabricates that local,
3. Ending a shared loan whose target sub-path does not exist in the owner fails,
   even if the owner carries a matching (forged) permission, and
4. A non-ended child whose concrete choice does not select `.parentLoan 0` does
   not block ending loan `0`, while a selected or symbolic edge still does. -/
theorem round11_loanGraph_regressions_exhaustive_tests :
    -- 1. Released-loan flavor must match its phase:
    (let mkSt (outPhase : LoanPhase LensTestVal) : SymState LensTestVal :=
       { locals := [⟨.atom 10, .mutJoined [5] [6]⟩]
         loans := [⟨6, outPhase, ⟨.atom 0, .unborrowed⟩, .rootParam 9⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     writebackRegionTargets lensTestValAlg 5 [5, 6] [(.localReg 0, [])]
       [.atom 7] (mkSt .activeMut) = none ∧
     (match writebackRegionTargets lensTestValAlg 5 [5, 6]
         [(.localReg 0, [])] [.atom 7] (mkSt .activeShared) with
      | some st' => getLocal lensTestValAlg 0 st' = .atom 7
      | none => False)) ∧
    -- 2. Inactive leaf on a missing local is skipped, not allocated:
    (let st : SymState LensTestVal :=
       { locals := [⟨.atom 10, .mutLocked 0⟩]
         loans :=
           [⟨0, .activeMut, ⟨.atom 55, .unborrowed⟩,
             .choice (.atom 0) (.direct (.localReg 1) [])
               (.direct (.localReg 0) [])⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     match endLoanInState lensTestValAlg 0 st with
     | .ok st' =>
       st'.locals.length = 1 ∧ getLocal lensTestValAlg 0 st' = .atom 55
     | .fail => False) ∧
    -- 3. Shared target path must exist in the owner value:
    (let mkSt (ownerVal : LensTestVal) : SymState LensTestVal :=
       { locals := [⟨ownerVal, .split [([0], .shared [0])]⟩]
         loans :=
           [⟨0, .activeShared, ⟨.atom 1, .unborrowed⟩,
             .direct (.localReg 0) [0]⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     endLoanInState lensTestValAlg 0 (mkSt (.atom 10)) = .fail ∧
     (match endLoanInState lensTestValAlg 0
         (mkSt (.node (.atom 1) (.atom 2))) with
      | .ok st' =>
        isUnborrowed (getLocalCell lensTestValAlg 0 st').perm = true
      | .fail => False)) ∧
    -- 4. Branch-sensitive child edges:
    (let child (c : LensTestVal) : LoanEntry LensTestVal :=
       ⟨1, .activeMut, ⟨.atom 0, .unborrowed⟩,
        .choice c (.direct (.parentLoan 0) []) (.direct (.localReg 1) [])⟩
     let parent : LoanEntry LensTestVal :=
       ⟨0, .activeMut, ⟨.atom 0, .unborrowed⟩, .direct (.localReg 0) []⟩
     noActiveChildLoanEdgesIn lensTestValAlg 0 [parent, child (.atom 0)] =
       true ∧
     noActiveChildLoanEdgesIn lensTestValAlg 0 [parent, child (.atom 1)] =
       false ∧
     noActiveChildLoanEdgesIn lensTestValAlg 0
       [parent, child (.node (.atom 0) (.atom 1))] = false ∧
     noActiveChildLoanEdges 0 [parent, child (.atom 0)] = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Further Round 11 regression tests for `LoanGraph`:
1. `getOwnerForMut` rejects a local beyond `st.locals`, and
2. `stateCleanAtReturn` rejects a state in which a local still carries a
   permission for an ended loan. -/
theorem round11_loanGraph_return_and_projection_tests :
    -- 1. No mutable access to a missing local:
    getOwnerForMut lensTestValAlg (.localReg 2)
      (⟨[], [], [], [], [], 0⟩ : SymState LensTestVal) = none ∧
    -- 2. Residual permissions block the return boundary:
    (let mkSt (p : PermTree) : SymState LensTestVal :=
       { locals := [⟨.atom 1, p⟩]
         loans := [⟨7, .ended, ⟨.atom 0, .unborrowed⟩, .direct (.localReg 0) []⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     stateCleanAtReturn (mkSt (.mutLocked 7)) = false ∧
     stateCleanAtReturn (mkSt .unborrowed) = true) :=
  ⟨rfl, ⟨rfl, rfl⟩⟩

/-- Round 11 regression tests for region-group retirement and the return
boundary:
1. `endRegionGroupInState` rejects an `.activeMut` output loan that appears in
   the shared half of an input permission, checking flavors against the phases
   before the outputs are retired, and still ends the consistent group, and
2. `stateCleanAtReturn` rejects duplicate region-group IDs, even when every
   group is inactive. -/
theorem round11_region_retirement_and_return_tests :
    (let rg : RegionGroupEntry LensTestVal :=
       { groupId := 0
         active := true
         lockLid := 5
         inputTargets := [(.localReg 0, [])]
         outputLoans := [6]
         requiredChildren := []
         backFn := fun outs _ => some (outs, []) }
     let mkSt (p : PermTree) : SymState LensTestVal :=
       { locals := [⟨.atom 10, p⟩]
         loans := [⟨6, .activeMut, ⟨.atom 7, .unborrowed⟩, .regionOut 0 0⟩]
         regionGroups := [rg]
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     endRegionGroupInState lensTestValAlg 0 (mkSt (.mutJoined [5] [6])) =
       .fail ∧
     (match endRegionGroupInState lensTestValAlg 0 (mkSt (.mutLocked 5)) with
      | .ok st' => getLocal lensTestValAlg 0 st' = .atom 7
      | .fail => False)) ∧
    (let rgDone : RegionGroupEntry LensTestVal :=
       { groupId := 3
         active := false
         lockLid := 0
         inputTargets := []
         outputLoans := []
         requiredChildren := []
         backFn := fun outs _ => some (outs, []) }
     let mkSt (rgs : List (RegionGroupEntry LensTestVal)) :
         SymState LensTestVal :=
       { locals := []
         loans := []
         regionGroups := rgs
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     stateCleanAtReturn (mkSt [rgDone, rgDone]) = false ∧
     stateCleanAtReturn (mkSt [rgDone]) = true) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Round 11 regression tests for `setLocalChecked`: it writes an existing or
fresh local, but rejects a local behind a live `&mut` or `&` borrow and a slot
two or more past the end. -/
theorem round11_setLocalChecked_tests :
    let mkSt (p : PermTree) : SymState LensTestVal :=
      ⟨[⟨.atom 1, p⟩], [], [], [], [], 0⟩
    (match setLocalChecked lensTestValAlg 0 (.atom 2) (mkSt .unborrowed) with
     | some st' => getLocal lensTestValAlg 0 st' = .atom 2
     | none => False) ∧
    (match setLocalChecked lensTestValAlg 1 (.atom 2) (mkSt .unborrowed) with
     | some st' => st'.locals.length = 2
     | none => False) ∧
    setLocalChecked lensTestValAlg 0 (.atom 2) (mkSt (.mutLocked 3)) = none ∧
    setLocalChecked lensTestValAlg 0 (.atom 2) (mkSt (.shared [3])) = none ∧
    setLocalChecked lensTestValAlg 2 (.atom 2) (mkSt .unborrowed) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Round 12 regression test: after an untaken parent loan has ended, ending a
child whose concrete choice did not select that parent succeeds, while a
residual permission for the child on the ended parent still fails. -/
theorem round12_inactive_ended_parent_cleanup_tests :
    let mkSt (parentPerm : PermTree) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 1⟩]
        loans :=
          [⟨0, .ended, ⟨.atom 5, parentPerm⟩, .direct (.localReg 3) []⟩,
           ⟨1, .activeMut, ⟨.atom 77, .unborrowed⟩,
            .choice (.atom 0) (.direct (.parentLoan 0) [])
              (.direct (.localReg 0) [])⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    (match endLoanInState lensTestValAlg 1 (mkSt .unborrowed) with
     | .ok st' => getLocal lensTestValAlg 0 st' = .atom 77
     | .fail => False) ∧
    endLoanInState lensTestValAlg 1 (mkSt (.mutLocked 1)) = .fail :=
  ⟨rfl, rfl⟩

/-- Round 12 regression test: a non-ended child with a truncated choice target
`[.choiceJoin c, .direct (.parentLoan 0) []]` still counts as a dependency of
loan `0` (`activeTargetLeaves` falls back to every serialized leaf), so the
parent cannot be ended underneath it. -/
theorem round12_malformed_child_target_tests :
    let malformed : BackTarget LensTestVal :=
      ⟨[.choiceJoin (.atom 1), .direct (.parentLoan 0) []]⟩
    let child : LoanEntry LensTestVal :=
      ⟨1, .activeMut, ⟨.atom 0, .unborrowed⟩, malformed⟩
    let parent : LoanEntry LensTestVal :=
      ⟨0, .activeMut, ⟨.atom 0, .unborrowed⟩, .direct (.localReg 0) []⟩
    activeTargetLeaves lensTestValAlg malformed = [(.parentLoan 0, [])] ∧
    noActiveChildLoanEdgesIn lensTestValAlg 0 [parent, child] = false :=
  ⟨rfl, rfl⟩

/-- Round 12 regression test: an untaken leaf naming an `.activeShared` parent
that carries no permission for the child is skipped during mutable cleanup,
while a residual permission on it still fails. -/
theorem round12_inactive_shared_parent_cleanup_tests :
    let mkSt (parentPerm : PermTree) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 1⟩]
        loans :=
          [⟨0, .activeShared, ⟨.atom 5, parentPerm⟩, .direct (.localReg 3) []⟩,
           ⟨1, .activeMut, ⟨.atom 77, .unborrowed⟩,
            .choice (.atom 0) (.direct (.parentLoan 0) [])
              (.direct (.localReg 0) [])⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    (match endLoanInState lensTestValAlg 1 (mkSt .unborrowed) with
     | .ok st' => getLocal lensTestValAlg 0 st' = .atom 77
     | .fail => False) ∧
    endLoanInState lensTestValAlg 1 (mkSt (.mutLocked 1)) = .fail :=
  ⟨rfl, rfl⟩

end Anneal.PureLift
