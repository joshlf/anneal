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

/-- Verify structural well-formedness of a shared-loan `BackTarget` step tree
(rejecting truncated `.choiceJoin` trees, `.rootParam` targets, and `.regionOut`
targets, while validating only the taken branch when `.choiceJoin cond` has a
concrete boolean condition). -/
def validateSharedBackTarget {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) : Bool :=
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
with a value list matching its `targets` arity, that no `.rootParam` or
`.regionOut` node appears in `target`, and that the pre-order step tree is
well-formed. -/
def validateBackTarget {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) (vNew : Val) : Bool :=
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
                | some true => fTrue (alg.projectBranchVal cond true vCur)
                | some false => fFalse (alg.projectBranchVal cond false vCur)
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
branch-sensitive evaluation and branch-specific value projection. -/
def evalBackVal {Val : Type} (alg : ValAlgebra Val)
    (owner : OwnerRef) (path : SubPath)
    (target : BackTarget Val) (vNew vOld : Val) : Option Val :=
  let stk : List (Val → Option Val) :=
    target.steps.foldr
      (fun step acc =>
        match step with
        | .rootParam _ => (fun _ => none) :: acc
        | .direct o p =>
          let fLeaf : Val → Option Val :=
            fun vCur =>
              if OwnerRef.beq owner o && subPathEq path p then some vCur
              else some vOld
          fLeaf :: acc
        | .choiceJoin cond =>
          match acc with
          | fTrue :: fFalse :: rest =>
            let fBranch : Val → Option Val :=
              fun vCur =>
                match alg.asBool cond with
                | some true => fTrue (alg.projectBranchVal cond true vCur)
                | some false => fFalse (alg.projectBranchVal cond false vCur)
                | none =>
                  match fTrue (alg.projectBranchVal cond true vCur),
                        fFalse (alg.projectBranchVal cond false vCur) with
                  | some v1, some v2 => some (alg.zipVal cond v1 v2)
                  | _, _ => none
            fBranch :: rest
          | _ => [fun _ => none]
        | .lensCall targets backFn =>
          let fLeaf : Val → Option Val :=
            fun vCur =>
              if !containsOwnerPath owner path targets then
                some vOld
              else
                match backFn vCur with
                | some updatedVals =>
                  lookupLensTargetVal owner path vOld targets updatedVals
                | none => none
          fLeaf :: acc
        | .regionOut _ _ => (fun _ => none) :: acc)
      []
  match stk with
  | [fRoot] => fRoot vNew
  | _ => none

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
`alg.asBool cond = some b`. -/
def activeTargetLeaves {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) : List (OwnerRef × SubPath) :=
  let stk : List (List (OwnerRef × SubPath)) :=
    target.steps.foldr
      (fun step acc =>
        match step with
        | .rootParam _ => [] :: acc
        | .direct o p => [(o, p)] :: acc
        | .choiceJoin cond =>
          match acc with
          | lTrue :: lFalse :: rest =>
            let merged :=
              match alg.asBool cond with
              | some true => lTrue
              | some false => lFalse
              | none => lTrue ++ lFalse
            merged :: rest
          | _ => [[]]
        | .lensCall targets _ => targets :: acc
        | .regionOut _ _ => [] :: acc)
      []
  match stk with
  | [leaves] => leaves
  | _ => []

/-- Low-level spatial memory cell supporting initialized values, uninitialized
storage (`.uninit`), and raw byte views (`.rawByte`). -/
inductive CellVal (Val : Type) where
  | init (v : Val)
  | uninit
  | rawByte (b : Nat)

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

/-- Complete pure symbolic state of a `PureLift` evaluation. -/
structure SymState (Val : Type) where
  locals : List (PlaceCell Val)
  loans : List (LoanEntry Val)
  regionGroups : List (RegionGroupEntry Val)
  regionDeposits : List Val
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

/-- Update index `idx` in `xs` to `v`, padding with `defVal` if `idx` exceeds
`xs.length`. -/
def listSetVal {α : Type} (defVal : α) (idx : Nat) (v : α)
    (xs : List α) : List α :=
  natFold
    (fun ys =>
      match ys with
      | [] => [v]
      | _ :: rest => v :: rest)
    (fun _ ih ys =>
      match ys with
      | [] => defVal :: ih []
      | y :: rest => y :: ih rest)
    idx xs

def getLocalCell {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (st : SymState Val) : PlaceCell Val :=
  listGetVal ⟨alg.defaultVal, .unborrowed⟩ reg st.locals

def setLocalCell {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (c : PlaceCell Val) (st : SymState Val) : SymState Val :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    ⟨listSetVal ⟨alg.defaultVal, .unborrowed⟩ reg c locals,
      loans, rgs, deps, sp, tag⟩

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

/-- Single-pass linear modifier for local register `idx`. -/
def modifyLocalAt {Val : Type} (defVal : Val)
    (f : Val → PermTree → Option (Val × PermTree))
    (idx : Nat) (xs : List (PlaceCell Val)) :
    Option (List (PlaceCell Val)) :=
  natFold
    (fun cells =>
      match cells with
      | [] =>
        match f defVal .unborrowed with
        | some (v', p') => some [mkStrictPlaceCell v' p']
        | none => none
      | ⟨v, p⟩ :: rest =>
        match f v p with
        | some (v', p') => some (mkStrictPlaceCell v' p' :: rest)
        | none => none)
    (fun _ ih cells =>
      match cells with
      | [] =>
        match ih [] with
        | some rest => some (⟨defVal, .unborrowed⟩ :: rest)
        | none => none
      | x :: rest =>
        match ih rest with
        | some rest' => some (x :: rest')
        | none => none)
    idx xs

def getLocal {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (st : SymState Val) : Val :=
  (getLocalCell alg reg st).val

def setLocal {Val : Type} (alg : ValAlgebra Val) (reg : LocalId) (v : Val)
    (st : SymState Val) : SymState Val :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    match modifyLocalAt alg.defaultVal (fun _ p => some (v, p)) reg locals with
    | some locals' => ⟨locals', loans, rgs, deps, sp, tag⟩
    | none => ⟨locals, loans, rgs, deps, sp, tag⟩

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

/-- Single-pass linear modifier for loan `lid`, enforcing that the loan is
active (or `.activeMut` when `reqMut == true`). -/
def modifyLoanAt {Val : Type} (lid : LoanId) (reqMut : Bool)
    (f : Val → PermTree → Option (Val × PermTree))
    (loans : List (LoanEntry Val)) : Option (List (LoanEntry Val)) :=
  match
    loans.foldr
      (fun e (acc : Bool × List (LoanEntry Val)) =>
        match e, acc with
        | ⟨id, phase, ⟨v, p⟩, target⟩, (found, rest) =>
          if id == lid then
            let okPhase := if reqMut then phase.isActiveMut else phase.isActive
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
def modifyOwner {Val : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (reqMut : Bool) (f : Val → PermTree → Option (Val × PermTree))
    (st : SymState Val) : Option (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    match owner with
    | .localReg reg =>
      match modifyLocalAt alg.defaultVal f reg locals with
      | some locals' => some ⟨locals', loans, rgs, deps, sp, tag⟩
      | none => none
    | .parentLoan lid =>
      match modifyLoanAt lid reqMut f loans with
      | some loans' => some ⟨locals, loans', rgs, deps, sp, tag⟩
      | none => none

/-- Single-pass linear modifier for local register `idx` returning an auxiliary
result `Res`. -/
def modifyLocalAtRes {Val Res : Type} (defVal : Val)
    (f : Val → PermTree → Option (Res × Val × PermTree))
    (idx : Nat) (xs : List (PlaceCell Val)) :
    Option (Res × List (PlaceCell Val)) :=
  natFold
    (fun cells =>
      match cells with
      | [] =>
        match f defVal .unborrowed with
        | some (res, v', p') => some (res, [mkStrictPlaceCell v' p'])
        | none => none
      | ⟨v, p⟩ :: rest =>
        match f v p with
        | some (res, v', p') => some (res, mkStrictPlaceCell v' p' :: rest)
        | none => none)
    (fun _ ih cells =>
      match cells with
      | [] =>
        match ih [] with
        | some (res, rest) => some (res, ⟨defVal, .unborrowed⟩ :: rest)
        | none => none
      | x :: rest =>
        match ih rest with
        | some (res, rest') => some (res, x :: rest')
        | none => none)
    idx xs

/-- Single-pass linear modifier for loan `lid` returning an auxiliary result
`Res`. -/
def modifyLoanAtRes {Val Res : Type} (lid : LoanId) (reqMut : Bool)
    (f : Val → PermTree → Option (Res × Val × PermTree))
    (loans : List (LoanEntry Val)) : Option (Res × List (LoanEntry Val)) :=
  match
    loans.foldr
      (fun e (acc : Option Res × List (LoanEntry Val)) =>
        match e, acc with
        | ⟨id, phase, ⟨v, p⟩, target⟩, (resOpt, rest) =>
          if id == lid then
            let okPhase := if reqMut then phase.isActiveMut else phase.isActive
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
def modifyOwnerRes {Val Res : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (reqMut : Bool) (f : Val → PermTree → Option (Res × Val × PermTree))
    (st : SymState Val) : Option (Res × SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    match owner with
    | .localReg reg =>
      match modifyLocalAtRes alg.defaultVal f reg locals with
      | some (res, locals') => some (res, ⟨locals', loans, rgs, deps, sp, tag⟩)
      | none => none
    | .parentLoan lid =>
      match modifyLoanAtRes lid reqMut f loans with
      | some (res, loans') => some (res, ⟨locals, loans', rgs, deps, sp, tag⟩)
      | none => none

/-- Look up `owner` for read access at `path` (defaulting to the whole owner
`[]`), rejecting `.spatialPinned` and `.ended` loans as well as any cell whose
`PermTree` has an active mutable borrow overlapping `path` (`!canReadPath path
cell.perm`). -/
def getOwnerForRead {Val : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (st : SymState Val) (path : SubPath := []) : Option (PlaceCell Val) :=
  match owner with
  | .localReg reg =>
    match getLocalCell alg reg st with
    | ⟨v, p⟩ => if canReadPath path p then some ⟨v, p⟩ else none
  | .parentLoan lid =>
    match findLoan lid st.loans with
    | some ⟨_, phase, ⟨v, p⟩, _⟩ =>
      if phase.isActive && canReadPath path p then some ⟨v, p⟩
      else none
    | none => none

/-- Look up `owner` for mutable access at `path` (defaulting to the whole owner
`[]`), rejecting `.activeShared`, `.spatialPinned`, and `.ended` loans as well
as any cell whose `PermTree` has an active shared or mutable borrow overlapping
`path` (`!canWritePath path cell.perm`). -/
def getOwnerForMut {Val : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (st : SymState Val) (path : SubPath := []) : Option (PlaceCell Val) :=
  match owner with
  | .localReg reg =>
    match getLocalCell alg reg st with
    | ⟨v, p⟩ => if canWritePath path p then some ⟨v, p⟩ else none
  | .parentLoan lid =>
    match findLoan lid st.loans with
    | some ⟨_, phase, ⟨v, p⟩, _⟩ =>
      if phase.isActiveMut && canWritePath path p then
        some ⟨v, p⟩
      else none
    | none => none

/-- Update the `PlaceCell` of `owner`. -/
def putOwnerCell {Val : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (c : PlaceCell Val) (st : SymState Val) : SymState Val :=
  match owner with
  | .localReg reg => setLocalCell alg reg c st
  | .parentLoan lid =>
    match st with
    | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
      let loans' := updateLoan lid (fun e => ⟨e.id, e.phase, c, e.target⟩) loans
      ⟨locals, loans', rgs, deps, sp, tag⟩

def writebackLeaf {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (target : BackTarget Val)
    (activeLeaves : List (OwnerRef × SubPath)) (vNew : Val)
    (owner : OwnerRef) (path : SubPath) (st : SymState Val) :
    Option (SymState Val) :=
  if containsOwnerPath owner path activeLeaves then
    modifyOwner alg owner true (fun ownerVal ownerPerm =>
      if !hasMutLoanAtPath lid path ownerPerm then
        none
      else
        match getPath alg path ownerVal with
        | some vOld =>
          match evalBackVal alg owner path target vNew vOld with
          | some vUpd =>
            match putPath alg path ownerVal vUpd with
            | some ownerVal' =>
              some (ownerVal', releaseLoanPermAtPath lid path ownerPerm)
            | none => none
          | none => none
        | none => none) st
  else
    match modifyOwner alg owner true (fun ownerVal ownerPerm =>
      if !hasMutLoanAtPath lid path ownerPerm then
        none
      else
        some (ownerVal, releaseLoanPermAtPath lid path ownerPerm)) st with
    | some st' => some st'
    | none => some st

def writebackLeaves {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (target : BackTarget Val) (vNew : Val)
    (leaves : List (OwnerRef × SubPath)) (st : SymState Val) :
    Option (SymState Val) :=
  let activeLeaves := activeTargetLeaves alg target
  leaves.foldr
    (fun op ih st0 =>
      match op with
      | (owner, path) =>
        match writebackLeaf alg lid target activeLeaves vNew owner path st0 with
        | some st1 => ih st1
        | none => none)
    (fun st0 => some st0)
    st

def writebackLensTargets {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (targets : List (OwnerRef × SubPath)) (vals : List Val)
    (st : SymState Val) : Option (SymState Val) :=
  targets.foldr
    (fun op ih vs st0 =>
      match op, vs with
      | (owner, path), vUpd :: restVals =>
        match modifyOwner alg owner true (fun ownerVal ownerPerm =>
          if !hasMutLoanAtPath lid path ownerPerm then
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

def releaseSharedLeaves {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (activeLeaves : List (OwnerRef × SubPath))
    (leaves : List (OwnerRef × SubPath)) (st : SymState Val) :
    Option (SymState Val) :=
  leaves.foldr
    (fun op ih st0 =>
      match op with
      | (owner, path) =>
        if containsOwnerPath owner path activeLeaves then
          match modifyOwner alg owner false (fun ownerVal ownerPerm =>
            if !hasSharedLoanAtPath lid path ownerPerm then
              none
            else
              some (ownerVal,
                    releaseLoanPermAtPath lid path ownerPerm)) st0 with
          | some st1 => ih st1
          | none => none
        else
          match modifyOwner alg owner false (fun ownerVal ownerPerm =>
            if !hasSharedLoanAtPath lid path ownerPerm then
              none
            else
              some (ownerVal,
                    releaseLoanPermAtPath lid path ownerPerm)) st0 with
          | some st1 => ih st1
          | none => ih st0)
    (fun st0 => some st0)
    st

/-- Deactivate loan `lid` in a single pass, verifying that `lid` is unique in
`loans`, has no active child borrows (`isUnborrowed cellPerm`), contains no
`.regionOut` or `.rootParam` target, and is currently active
(`phase.isActive`). -/
def deactivateLoan {Val : Type} (lid : LoanId)
    (loans : List (LoanEntry Val)) :
    Option (LoanEntry Val × List (LoanEntry Val)) :=
  match
    loans.foldr
      (fun e (acc : Bool × Option (LoanEntry Val) × List (LoanEntry Val)) =>
        match e, acc with
        | ⟨id, phase, ⟨cellVal, cellPerm⟩, target⟩, (dup, foundOpt, rest) =>
          if id == lid then
            match foundOpt with
            | some _ => (true, foundOpt, rest)
            | none =>
              if !isUnborrowed cellPerm || isRegionOutTarget target ||
                 isRootParamTarget target || !phase.isActive then
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
    match deactivateLoan lid loans with
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
          | some st' => .ok st'
          | none => .fail
      | .activeMut =>
        if !validateBackTarget alg target cellVal then .fail
        else
          let leaves := dedupOwnerPaths (targetLeaves target)
          match writebackLeaves alg lid target cellVal leaves stDeact with
          | some st' => .ok st'
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
`.activeMut`, has no active child sub-borrows (`isUnborrowed e.cell.perm`), and
has target `.regionOut gid expectedIdx`. -/
def collectAndRetireOutputLoans {Val : Type}
    (gid : RegionGroupId) (expectedIdx : Nat) (outLids : List LoanId)
    (st : SymState Val) : Option (List Val × SymState Val) :=
  outLids.foldr
    (β := Nat → SymState Val → Option (List Val × SymState Val))
    (fun olid ih idx st0 =>
      if !hasUniqueLoanId olid st0.loans then none
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

def writebackRegionTargets {Val : Type} (alg : ValAlgebra Val)
    (lockLid : LoanId) (releaseLids : List LoanId)
    (targets : List (OwnerRef × SubPath)) (vals : List Val)
    (st : SymState Val) : Option (SymState Val) :=
  targets.foldr
    (fun op ih vs st0 =>
      match op, vs with
      | (owner, path), vUpd :: restVals =>
        match modifyOwner alg owner true (fun ownerVal ownerPerm =>
          if !hasMutLoanAtPath lockLid path ownerPerm then
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

/-- End multi-region group `gid`, enforcing uniqueness of `gid` in
`st.regionGroups`, `requiredChildren` outlives order, pairwise-disjoint
`inputTargets`, unborrowed output loans with matching `.regionOut gid idx`
targets, and backward lens propagation across `inputTargets`. -/
def endRegionGroupInState {Val : Type} (alg : ValAlgebra Val)
    (gid : RegionGroupId) (st : SymState Val) : EvalOutcome (SymState Val) :=
  if !hasUniqueRegionGroupId gid st.regionGroups then .fail
  else
    match findRegionGroup gid st.regionGroups with
  | none => .fail
  | some g =>
    if !g.active || !ownerPathsDisjoint g.inputTargets ||
       !allRequiredGroupsEnded st.regionGroups g.requiredChildren then
      .fail
    else
      match collectAndRetireOutputLoans gid 0 g.outputLoans st with
      | none => .fail
      | some (outVals, stRetired) =>
        match g.backFn outVals stRetired.regionDeposits with
        | none => .fail
        | some (updatedInputs, newDeposits) =>
          match writebackRegionTargets alg g.lockLid
                  (g.lockLid :: g.outputLoans)
                  g.inputTargets updatedInputs stRetired with
          | none => .fail
          | some stWritten =>
            match stWritten with
            | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
              let rgs' := updateRegionGroup gid
                (fun x => ⟨x.groupId, false, x.lockLid, x.inputTargets,
                           x.outputLoans, x.requiredChildren, x.backFn⟩)
                rgs
              .ok ⟨locals, loans, rgs', deps ++ newDeposits, sp, tag⟩

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

/-!
## Exhaustive Kernel-Checked Tests for `LoanGraph`
-/

/-- Local register access (`listGetVal`, `listSetVal`, `getLocal`, `setLocal`,
`modifyLocalAt`, `modifyLocalAtRes`) is exact for local indices above eight
(`8`, `9`, `12`, `15`) and never aliases local `12` to local `8`. -/
theorem loanGraph_locals_above_eight_no_aliasing :
    let st0 : SymState LensTestVal := ⟨[], [], [], [], [], 0⟩
    let st1 := setLocal lensTestValAlg 8 (.atom 80) st0
    let st2 := setLocal lensTestValAlg 9 (.atom 90) st1
    let st3 := setLocal lensTestValAlg 12 (.atom 120) st2
    let st4 := setLocal lensTestValAlg 15 (.atom 150) st3
    getLocal lensTestValAlg 0 st4 = .atom 0 ∧
    getLocal lensTestValAlg 8 st4 = .atom 80 ∧
    getLocal lensTestValAlg 9 st4 = .atom 90 ∧
    getLocal lensTestValAlg 12 st4 = .atom 120 ∧
    getLocal lensTestValAlg 15 st4 = .atom 150 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

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

/-- `isRegionOutTarget` and `deactivateLoan` detect `.regionOut` targets even
when nested inside `.choice` trees, rejecting ordinary `endLoanInState`. -/
theorem nested_regionOut_under_choice_rejected :
    let nestedTarget : BackTarget LensTestVal :=
      .choice (.atom 1)
        (.direct (.localReg 0) [])
        (.choice (.atom 0) (.direct (.localReg 1) []) (.regionOut 0 0))
    let st : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩, nestedTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    isRegionOutTarget nestedTarget = true ∧
    endLoanInState lensTestValAlg 0 st = .fail :=
  ⟨rfl, rfl⟩

/-- `endLoanInState` executes backward lenses when `.lensCall` is nested inside
a `.choice` tree, propagating the branch-selected lens writeback to the owner
locals. -/
theorem nested_lensCall_under_choice_executes_writeback (cond : Bool) :
    let condVal : LensTestVal := .atom (if cond then 1 else 0)
    let tTrue : BackTarget LensTestVal :=
      .lensCall [(.localReg 0, [])]
        (fun v =>
          match v with
          | .atom n => some [.atom (n + 100)]
          | _ => none)
    let tFalse : BackTarget LensTestVal :=
      .lensCall [(.localReg 1, [])]
        (fun v =>
          match v with
          | .atom n => some [.atom (n + 200)]
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
    -- `endRegionGroupsInState` succeeds and appends `regionDeposits`:
    let rgParent : RegionGroupEntry LensTestVal :=
      { groupId := 0
        active := true
        lockLid := 0
        inputTargets := [(.localReg 0, [])]
        outputLoans := [0]
        requiredChildren := [1]
        backFn := fun outs _ =>
          match outs with
          | [.atom v] => some ([.atom (v + 1)], [.atom 900])
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
          | [.atom v] => some ([.atom (v + 2)], [.atom 800])
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
       stRgDone.regionDeposits = [.atom 800, .atom 900] ∧
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
                  | .atom 77 => some [.atom 88]
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
                  | .atom 70 => some [.atom 71]
                  | _ => none))
              (.lensCall [(.localReg 1, [])]
                (fun v =>
                  match v with
                  | .atom 80 => some [.atom 81]
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
     | none => false) = true :=
  ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
   rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
   ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl,
   ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PureLift
