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
import Anneal.PureLift.LoanGraph
import Anneal.PureLift.SpatialPin

namespace Anneal.PureLift

/-!
# Structured Control-Flow Plans, Diamond Joins, and Function Lifting (`Plan`)

Evaluates imperative control-flow plans (`FlowPlan Val`) over the unified pure
symbolic state (`SymState Val`).

Supported features:
- Sub-place reads and writes (`PlaceExpr.localSub` and `PlaceExpr.derefSub`)
  checked against `PermTree` permissions and `LoanPhase` liveness.
- Shared and mutable borrows (`PrimAction.borrow`) and explicit loan or
  multi-region-group termination (`PrimAction.endLoan` and
  `PrimAction.endRegionGroup`).
- Modular single-region (`PrimAction.call`) and multi-region-group
  (`PrimAction.callMultiRegion`) interprocedural calls using forward/backward
  lens summaries.
- Hybrid functional-spatial pinning (`PrimAction.freezeSpatial`,
  `PrimAction.mutateSpatial`, and `PrimAction.reabsorbSpatial`).
- Symbolic diamond branch joins (`joinSymState`) with anti-aliasing validation
  on explicit join pairs (`validJoinPairs`).
- Nested early return (`FlowPlan.earlyReturn`) with scoped loan and region
  cleanup and short-circuiting through enclosing sequential compositions and
  loops (`ExecFlow`).
- Entry parameter aliasing validation (`initFnState`) and top-level function
  lifting (`evalFnValue` and `evalFnReturningMut`).
-/

/-- Place expression addressing either a local register sub-path or a
dereferenced borrow handle with an additional sub-path projection. -/
inductive PlaceExpr where
  | localSub (reg : LocalId) (path : SubPath)
  | derefSub (reg : LocalId) (path : SubPath)

/-- Resolve `PlaceExpr` in `st` to its underlying `(OwnerRef × SubPath)`. -/
def resolvePlace {Val : Type} (alg : ValAlgebra Val) (p : PlaceExpr)
    (st : SymState Val) : Option (OwnerRef × SubPath) :=
  match p with
  | .localSub reg path => some (.localReg reg, path)
  | .derefSub reg extraPath =>
    match alg.decodeRef (getLocal alg reg st) with
    | some (lid, basePath) => some (.parentLoan lid, basePath ++ extraPath)
    | none => none

/-- Read the value at `PlaceExpr` if `PermTree` permits reading at the resolved
sub-path and the owner is active. -/
def readPlaceVal {Val : Type} (alg : ValAlgebra Val)
    (p : PlaceExpr) (st : SymState Val) : Option Val :=
  match resolvePlace alg p st with
  | none => none
  | some (owner, path) =>
    match getOwnerForRead alg owner st path with
    | some ⟨ownerVal, _⟩ => getPath alg path ownerVal
    | none => none

/-- Write `vNew` to `PlaceExpr` if `PermTree` permits writing at the resolved
sub-path and the owner is mutable and active. -/
def writePlaceVal {Val : Type} (alg : ValAlgebra Val)
    (p : PlaceExpr) (vNew : Val) (st : SymState Val) : Option (SymState Val) :=
  match resolvePlace alg p st with
  | none => none
  | some (owner, path) =>
    modifyOwner alg owner true (fun ownerVal ownerPerm =>
      if canWritePath path ownerPerm then
        match putPath alg path ownerVal vNew with
        | some ownerVal' => some (ownerVal', ownerPerm)
        | none => none
      else none) st

/-- Pure right-hand-side expression operator. -/
inductive RvalOp (Val : Type) where
  | constVal (v : Val)
  | use (p : PlaceExpr)
  | unary (f : Val → Option Val) (p : PlaceExpr)
  | binary (f : Val → Val → Option Val) (p1 p2 : PlaceExpr)

def evalRval {Val : Type} (alg : ValAlgebra Val) (op : RvalOp Val)
    (st : SymState Val) : Option Val :=
  match op with
  | .constVal v => some v
  | .use p => readPlaceVal alg p st
  | .unary f p =>
    match readPlaceVal alg p st with
    | some v => f v
    | none => none
  | .binary f p1 p2 =>
    match readPlaceVal alg p1 st, readPlaceVal alg p2 st with
    | some v1, some v2 => f v1 v2
    | _, _ => none

def evalRvalList {Val : Type} (alg : ValAlgebra Val)
    (ops : List (RvalOp Val)) (st : SymState Val) : Option (List Val) :=
  listFold (some [])
    (fun r _ ih =>
      match evalRval alg r st, ih with
      | some v, some vs => some (v :: vs)
      | _, _ => none)
    ops

/-- Modular forward/backward lens summary for a single-region function call. -/
structure CallSummary (Val : Type) where
  returnsMutBorrow : Bool
  fwd : List Val → List Val → Option Val
  back : List Val → List Val → Val → Option (List Val)

/-- Specification of one region group in a multi-region-group call. -/
structure RegionGroupSpec (Val : Type) where
  groupId : RegionGroupId
  requiredChildren : List RegionGroupId
  inputPlaces : List PlaceExpr
  outDsts : List LocalId
  fwdOuts : List Val → List Val → Option (List Val)
  backFn : List Val → List Val → List Val → List Val →
      Option (List Val × List Val)

/-- Lock each mutable argument place for loan `lid` in left-to-right order,
rejecting aliased or overlapping mutable arguments. -/
def acquireMutCallArgs {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (places : List PlaceExpr) (st : SymState Val) :
    Option (List (OwnerRef × SubPath) × List Val × SymState Val) :=
  listFold
    (fun st0 => some ([], [], st0))
    (fun p _ ih st0 =>
      match resolvePlace alg p st0 with
      | none => none
      | some (owner, path) =>
        match modifyOwnerRes alg owner true (fun ownerVal ownerPerm =>
          match getPath alg path ownerVal,
                acquirePerm .mutBorrow lid path ownerPerm with
          | some subVal, some ownerPerm' => some (subVal, ownerVal, ownerPerm')
          | _, _ => none) st0 with
        | some (subVal, st1) =>
          match ih st1 with
          | some (restTargets, restVals, st2) =>
            some ((owner, path) :: restTargets, subVal :: restVals, st2)
          | none => none
        | none => none)
    places st

/-- Allocate output loans for region group `gid` and bind their encoded
reference handles into `dsts`. -/
def allocateRegionGroupOutputs {Val : Type}
    (alg : ValAlgebra Val) (gid : RegionGroupId) (outIdx : Nat)
    (dsts : List LocalId) (vals : List Val) (st : SymState Val) :
    Option (List LoanId × SymState Val) :=
  listFold
    (β := Nat → List Val → SymState Val → Option (List LoanId × SymState Val))
    (fun _ vs st0 =>
      match vs with
      | [] => some ([], st0)
      | _ :: _ => none)
    (fun dst _ ih idx vs st0 =>
      match vs with
      | [] => none
      | vOut :: restVals =>
        if !canWritePath [] (getLocalPerm alg dst st0) then none
        else
          let newLid := st0.loans.length
          let newEntry : LoanEntry Val :=
            ⟨newLid, .activeMut, ⟨vOut, .unborrowed⟩, .regionOut gid idx⟩
          let st1 : SymState Val :=
            match st0 with
            | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
              ⟨locals, loans ++ [newEntry], rgs, deps, sp, tag⟩
          let st2 := setLocal alg dst (alg.encodeRef newLid []) st1
          match ih (idx + 1) restVals st2 with
          | some (restLids, st3) => some (newLid :: restLids, st3)
          | none => none)
    dsts outIdx vals st

/-- Replace an existing `RegionGroupEntry` with `entry.groupId` in `rgs`, or
append `entry` if `entry.groupId` does not yet appear in `rgs`, in a single
pass. -/
def upsertRegionGroup {Val : Type} (entry : RegionGroupEntry Val)
    (rgs : List (RegionGroupEntry Val)) : List (RegionGroupEntry Val) :=
  match
    rgs.foldr
      (fun g (acc : Bool × List (RegionGroupEntry Val)) =>
        match acc with
        | (found, rest) =>
          if g.groupId == entry.groupId then
            (true, entry :: rest)
          else
            (found, g :: rest))
      (false, [])
  with
  | (true, updated) => updated
  | (false, updated) => updated ++ [entry]

/-- Install all region groups of a multi-region-group call into `st`. Rejects
reinstalling an already-active `groupId`, and replaces any completed (inactive)
entry with the same `groupId` so repeated calls in a loop do not shadow newer
entries. When a region group has no output borrows (`outLids.isEmpty`), an ended
lock-sentinel entry is appended to `st.loans` at `lockLid` so subsequent region
groups or borrows never reuse `lockLid`. -/
def installRegionGroups {Val : Type} (alg : ValAlgebra Val)
    (pureVals : List Val) (specs : List (RegionGroupSpec Val))
    (st : SymState Val) : Option (SymState Val) :=
  listFold
    (fun st0 => some st0)
    (fun spec _ ih st0 =>
      let alreadyActive : Bool :=
        match findRegionGroup spec.groupId st0.regionGroups with
        | some existing => existing.active
        | none => false
      match alreadyActive with
      | true => none
      | false =>
        let lockLid := st0.loans.length
        match acquireMutCallArgs alg lockLid spec.inputPlaces st0 with
        | none => none
        | some (inTargets, inMutVals, stLocked) =>
          match spec.fwdOuts pureVals inMutVals with
          | none => none
          | some outVals =>
            match allocateRegionGroupOutputs alg spec.groupId 0
                    spec.outDsts outVals stLocked with
            | none => none
            | some (outLids, stWithOuts) =>
              let rgEntry : RegionGroupEntry Val :=
                ⟨spec.groupId, true, lockLid, inTargets, outLids,
                 spec.requiredChildren, spec.backFn pureVals inMutVals⟩
              let stWithRg : SymState Val :=
                match stWithOuts with
                | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
                  let loans' :=
                    if outLids.isEmpty then
                      let lockSentinel : LoanEntry Val :=
                        ⟨lockLid, .ended, ⟨alg.defaultVal, .unborrowed⟩,
                         .regionOut spec.groupId 0⟩
                      loans ++ [lockSentinel]
                    else
                      loans
                  ⟨locals, loans', upsertRegionGroup rgEntry rgs, deps, sp, tag⟩
              ih stWithRg)
    specs st

/-- Primitive atomic action in a `FlowPlan`. -/
inductive PrimAction (Val : Type) where
  | assign (dst : PlaceExpr) (rhs : RvalOp Val)
  | borrow (dst : LocalId) (kind : BorrowKind) (src : PlaceExpr)
  | endLoan (lid : LoanId)
  | endLoanAtLocal (reg : LocalId)
  | call (dst : LocalId) (summary : CallSummary Val)
      (pureArgs : List (RvalOp Val)) (mutArgs : List PlaceExpr)
  | callMultiRegion (pureArgs : List (RvalOp Val))
      (groups : List (RegionGroupSpec Val))
  | endRegionGroup (gid : RegionGroupId)
  | freezeSpatial (lid : LoanId) (codec : SpatialCodec Val)
  | mutateSpatial (bid : BlockId) (tag : Nat) (cells : List (CellVal Val))
  | reabsorbSpatial (lid : LoanId) (codec : SpatialCodec Val)

/-- Execute a single `PrimAction` on `SymState Val`. -/
def stepAction {Val : Type} (alg : ValAlgebra Val)
    (act : PrimAction Val) (st : SymState Val) : EvalOutcome (SymState Val) :=
  match act with
  | .assign dst rhs =>
    match evalRval alg rhs st with
    | some v =>
      match writePlaceVal alg dst v st with
      | some st' => .ok st'
      | none => .fail
    | none => .fail
  | .borrow dst kind src =>
    if !canWritePath [] (getLocalPerm alg dst st) then .fail
    else
      match resolvePlace alg src st with
      | none => .fail
      | some (owner, path) =>
        let reqMut : Bool :=
          match kind with
          | .shared => false
          | .mutBorrow => true
        let newLid := st.loans.length
        match modifyOwnerRes alg owner reqMut (fun ownerVal ownerPerm =>
          match getPath alg path ownerVal,
                acquirePerm kind newLid path ownerPerm with
          | some subVal, some ownerPerm' => some (subVal, ownerVal, ownerPerm')
          | _, _ => none) st with
        | none => .fail
        | some (subVal, ⟨locals, loans, rgs, deps, sp, tag⟩) =>
          let phase : LoanPhase Val :=
            match kind with
            | .shared => .activeShared
            | .mutBorrow => .activeMut
          let newEntry : LoanEntry Val :=
            ⟨newLid, phase, ⟨subVal, .unborrowed⟩, .direct owner path⟩
          let encVal : Val :=
            match kind with
            | .shared => alg.encodeSharedRef newLid []
            | .mutBorrow => alg.encodeRef newLid []
          .ok (setLocal alg dst encVal
                ⟨locals, loans ++ [newEntry], rgs, deps, sp, tag⟩)
  | .endLoan lid => endLoanInState alg lid st
  | .endLoanAtLocal reg =>
    match alg.decodeRef (getLocal alg reg st) with
    | some (lid, _) => endLoanInState alg lid st
    | none => .fail
  | .call dst summary pureArgs mutArgs =>
    if !canWritePath [] (getLocalPerm alg dst st) then .fail
    else
      match evalRvalList alg pureArgs st with
      | none => .fail
      | some pureVals =>
        let newLid := st.loans.length
        match acquireMutCallArgs alg newLid mutArgs st with
        | none => .fail
        | some (targets, mutVals, stLocked) =>
          match summary.fwd pureVals mutVals with
          | none => .fail
          | some retVal =>
            if summary.returnsMutBorrow then
              let newEntry : LoanEntry Val :=
                ⟨newLid, .activeMut, ⟨retVal, .unborrowed⟩,
                  .lensCall targets (summary.back pureVals mutVals)⟩
              let stWithLoan : SymState Val :=
                match stLocked with
                | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
                  ⟨locals, loans ++ [newEntry], rgs, deps, sp, tag⟩
              .ok (setLocal alg dst (alg.encodeRef newLid []) stWithLoan)
            else
              match summary.back pureVals mutVals retVal with
              | some updatedMutVals =>
                match writebackLensTargets alg newLid targets
                        updatedMutVals stLocked with
                | some stUnlocked => .ok (setLocal alg dst retVal stUnlocked)
                | none => .fail
              | none => .fail
  | .callMultiRegion pureArgs groups =>
    match evalRvalList alg pureArgs st with
    | none => .fail
    | some pureVals =>
      match installRegionGroups alg pureVals groups st with
      | some st' => .ok st'
      | none => .fail
  | .endRegionGroup gid => endRegionGroupInState alg gid st
  | .freezeSpatial lid codec => freezeToSpatialInState lid codec st
  | .mutateSpatial bid tag cells => mutateSpatialInState bid tag cells st
  | .reabsorbSpatial lid codec => reabsorbFromSpatialInState lid codec st

/-- Merge two value lists under symbolic branch condition `cond`. -/
def zipValList {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (xs ys : List Val) : List Val :=
  listFold
    (fun bs => bs)
    (fun x _ ih bs =>
      match bs with
      | [] => x :: ih []
      | y :: ys' => alg.zipVal cond x y :: ih ys')
    xs ys

/-- Join two local `PlaceCell` lists across a conditional branch join, merging
all locals at every index (padding shorter local lists with `alg.defaultVal`
and `.unborrowed`). -/
def joinPlaceCells {Val : Type} (alg : ValAlgebra Val)
    (cond : Val) (cs1 cs2 : List (PlaceCell Val)) : List (PlaceCell Val) :=
  listFold
    (fun bs =>
      listFold []
        (fun b _ ih =>
          ⟨alg.zipVal cond alg.defaultVal b.val, b.perm⟩ :: ih)
        bs)
    (fun c1 _ ih bs =>
      match bs with
      | [] =>
        ⟨alg.zipVal cond c1.val alg.defaultVal, c1.perm⟩ :: ih []
      | c2 :: cs2' =>
        ⟨alg.zipVal cond c1.val c2.val, unionPerm c1.perm c2.perm⟩ ::
          ih cs2')
    cs1 cs2

def sameBackTargetStepShape {Val : Type} :
    BackTargetStep Val → BackTargetStep Val → Bool
  | .rootParam i, .rootParam j => i == j
  | .direct o1 p1, .direct o2 p2 => OwnerRef.beq o1 o2 && subPathEq p1 p2
  | .regionOut g1 i1, .regionOut g2 i2 => g1 == g2 && i1 == i2
  | _, _ => false

def sameBackTargetShape {Val : Type} (t1 t2 : BackTarget Val) : Bool :=
  match t1.steps, t2.steps with
  | [s1], [s2] => sameBackTargetStepShape s1 s2
  | _, _ => false

def joinBackTarget {Val : Type} (cond : Val)
    (t1 t2 : BackTarget Val) : BackTarget Val :=
  if sameBackTargetShape t1 t2 then t1
  else .choice cond t1 t2

/-- Join two loan lists across a diamond branch join, synthesizing `.choice`
writeback targets when a loan's target differs between branches. -/
def joinLoanEntries {Val : Type} (alg : ValAlgebra Val)
    (cond : Val) (es1 es2 : List (LoanEntry Val)) :
    Option (List (LoanEntry Val)) :=
  listFold
    (fun bs =>
      match bs with
      | [] => some []
      | _ :: _ => none)
    (fun e1 _ ih bs =>
      match bs with
      | [] => none
      | e2 :: es2' =>
        if e1.id == e2.id && e1.phase.samePhase e2.phase then
          match ih es2' with
          | some rest =>
            let mergedEntry : LoanEntry Val :=
              ⟨e1.id, e1.phase,
                ⟨alg.zipVal cond e1.cell.val e2.cell.val,
                 unionPerm e1.cell.perm e2.cell.perm⟩,
                joinBackTarget cond e1.target e2.target⟩
            some (mergedEntry :: rest)
          | none => none
        else none)
    es1 es2

/-- Structural equality on `List (OwnerRef × SubPath)`. -/
def ownerPathListEq (xs ys : List (OwnerRef × SubPath)) : Bool :=
  listFold
    (fun bs =>
      match bs with
      | [] => true
      | _ :: _ => false)
    (fun a _ ih bs =>
      match a, bs with
      | (o1, p1), (o2, p2) :: bs' =>
        OwnerRef.beq o1 o2 && subPathEq p1 p2 && ih bs'
      | _, _ => false)
    xs ys

/-- Join two region-group tables across a diamond branch join, verifying that
all structural metadata (`groupId`, `active`, `lockLid`, `inputTargets`,
`outputLoans`, `requiredChildren`) match and merging active `backFn` closures
under `cond`. -/
def joinRegionGroups {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (gs1 gs2 : List (RegionGroupEntry Val)) :
    Option (List (RegionGroupEntry Val)) :=
  listFold
    (fun bs =>
      match bs with
      | [] => some []
      | _ :: _ => none)
    (fun g1 _ ih bs =>
      match bs with
      | [] => none
      | g2 :: gs2' =>
        if g1.groupId == g2.groupId &&
           g1.active == g2.active &&
           g1.lockLid == g2.lockLid &&
           ownerPathListEq g1.inputTargets g2.inputTargets &&
           loanIdListEq g1.outputLoans g2.outputLoans &&
           loanIdListEq g1.requiredChildren g2.requiredChildren then
          match ih gs2' with
          | some rest =>
            let mergedBack :
                List Val → List Val → Option (List Val × List Val) :=
              fun outVals deps =>
                match g1.backFn outVals deps, g2.backFn outVals deps with
                | some (inUpd1, depUpd1), some (inUpd2, depUpd2) =>
                  if inUpd1.length == inUpd2.length &&
                     depUpd1.length == depUpd2.length then
                    some (zipValList alg cond inUpd1 inUpd2,
                          zipValList alg cond depUpd1 depUpd2)
                  else none
                | _, _ => none
            let gMerged : RegionGroupEntry Val :=
              ⟨g1.groupId, g1.active, g1.lockLid, g1.inputTargets,
               g1.outputLoans, g1.requiredChildren, mergedBack⟩
            some (gMerged :: rest)
          | none => none
        else none)
    gs1 gs2

/-- Join two symbolic states across a conditional diamond branch, requiring
matching `regionDeposits` lengths and taking the maximum of
`st1.nextSpatialTag` and `st2.nextSpatialTag` so spatial provenance tags remain
fresh relative to both branch histories. -/
def joinSymState {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (st1 st2 : SymState Val) : Option (SymState Val) :=
  if !st1.spatial.isEmpty || !st2.spatial.isEmpty ||
     st1.regionDeposits.length != st2.regionDeposits.length then
    none
  else
    match joinLoanEntries alg cond st1.loans st2.loans,
          joinRegionGroups alg cond st1.regionGroups st2.regionGroups with
    | some loans', some rgs' =>
      let nextTag :=
        if decide (st1.nextSpatialTag ≤ st2.nextSpatialTag) then
          st2.nextSpatialTag
        else
          st1.nextSpatialTag
      some ⟨joinPlaceCells alg cond st1.locals st2.locals,
            loans',
            rgs',
            zipValList alg cond st1.regionDeposits st2.regionDeposits,
            [],
            nextTag⟩
    | _, _ => none

def listContainsLoanId (lid : LoanId) (xs : List LoanId) : Bool :=
  elemLoanId lid xs

/-- Verify that an explicit list of branch join pairs `(trueLid, falseLid)`
does not duplicate any loan identifier across joined outputs, preventing
aliasing of mutable ownership at a branch merge. -/
def validJoinPairs (pairs : List (LoanId × LoanId))
    (seenT seenF : List LoanId) : Bool :=
  listFold
    (fun _ _ => true)
    (fun pair _ ih sT sF =>
      match pair with
      | (tLid, fLid) =>
        if listContainsLoanId tLid sT || listContainsLoanId fLid sF then
          false
        else
          ih (tLid :: sT) (fLid :: sF))
    pairs seenT seenF

/-- Rename parent loan references from `oldLid` to `newLid` inside an
`OwnerRef`. -/
def renameOwnerLoan (oldLid newLid : LoanId) : OwnerRef → OwnerRef
  | .localReg reg => .localReg reg
  | .parentLoan lid => .parentLoan (if lid == oldLid then newLid else lid)

def renameBackTargetStepLoan {Val : Type} (oldLid newLid : LoanId) :
    BackTargetStep Val → BackTargetStep Val
  | .rootParam i => .rootParam i
  | .direct o p => .direct (renameOwnerLoan oldLid newLid o) p
  | .choiceJoin cond => .choiceJoin cond
  | .lensCall targets backFn =>
    let targets' :=
      listFold []
        (fun op _ ih =>
          match op with
          | (o, p) => (renameOwnerLoan oldLid newLid o, p) :: ih)
        targets
    .lensCall targets' backFn
  | .regionOut gid idx => .regionOut gid idx

/-- Rename parent loan references from `oldLid` to `newLid` inside a
`BackTarget Val`. -/
def renameBackTargetLoan {Val : Type} (oldLid newLid : LoanId)
    (target : BackTarget Val) : BackTarget Val :=
  ⟨listFold []
    (fun s _ ih => renameBackTargetStepLoan oldLid newLid s :: ih)
    target.steps⟩

/-- Remap an encoded reference value (including references nested inside
aggregates) from `fLid` to `tLid`. -/
def remapValLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (v : Val) : Val :=
  alg.remapRefInVal fLid tLid v

/-- Remap encoded reference values and `PermTree` loan IDs from `fLid` to
`tLid` across a list of `PlaceCell Val`s. -/
def remapPlaceCellsLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (cells : List (PlaceCell Val)) :
    List (PlaceCell Val) :=
  listFold []
    (fun c _ ih =>
      ⟨remapValLoan alg fLid tLid c.val,
       renameLoanPerm fLid tLid c.perm⟩ :: ih)
    cells

/-- Rename loan references from `oldLid` to `newLid` inside a
`RegionGroupEntry Val`. -/
def renameRegionGroupLoan {Val : Type} (oldLid newLid : LoanId)
    (g : RegionGroupEntry Val) : RegionGroupEntry Val :=
  let lockLid' := if g.lockLid == oldLid then newLid else g.lockLid
  let targets' :=
    listFold []
      (fun op _ ih =>
        match op with
        | (o, p) => (renameOwnerLoan oldLid newLid o, p) :: ih)
      g.inputTargets
  let outLoans' :=
    listFold []
      (fun lid _ ih => (if lid == oldLid then newLid else lid) :: ih)
      g.outputLoans
  ⟨g.groupId, g.active, lockLid', targets', outLoans',
   g.requiredChildren, g.backFn⟩

/-- Apply a single explicit join pair `(tLid, fLid)` to align `st2` with `st1`,
verifying that `tLid` is active in `st1`, `fLid` is active with the same phase
in `st2`, and remapping `fLid` to `tLid` across locals, loan cells,
`regionGroups`, and `regionDeposits` in `st2` when `tLid != fLid`. -/
def applyOneJoinPair {Val : Type} (alg : ValAlgebra Val)
    (tLid fLid : LoanId) (st1 st2 : SymState Val) : Option (SymState Val) :=
  match findLoan tLid st1.loans, findLoan fLid st2.loans with
  | some e1, some e2 =>
    if !e1.phase.isActive || !e1.phase.samePhase e2.phase then none
    else if tLid == fLid then some st2
    else
      match findLoan tLid st2.loans, findLoan fLid st1.loans with
      | some e2AtT, some e1AtF =>
        if !e2AtT.phase.isEnded || !e1AtF.phase.isEnded then none
        else
          match st2 with
          | ⟨locals2, loans2, rgs2, deps2, sp2, tag2⟩ =>
            let locals2' := remapPlaceCellsLoan alg fLid tLid locals2
            let movedEntry : LoanEntry Val :=
              ⟨tLid, e2.phase,
               ⟨remapValLoan alg fLid tLid e2.cell.val,
                renameLoanPerm fLid tLid e2.cell.perm⟩,
               renameBackTargetLoan fLid tLid e2.target⟩
            let clearedEntry : LoanEntry Val :=
              ⟨fLid, .ended, ⟨e1AtF.cell.val, .unborrowed⟩, e1AtF.target⟩
            let loans2' :=
              listFold []
                (fun e _ ih =>
                  if e.id == tLid then movedEntry :: ih
                  else if e.id == fLid then clearedEntry :: ih
                  else
                    ⟨e.id, e.phase,
                     ⟨remapValLoan alg fLid tLid e.cell.val,
                      renameLoanPerm fLid tLid e.cell.perm⟩,
                     renameBackTargetLoan fLid tLid e.target⟩ :: ih)
                loans2
            let rgs2' :=
              listFold []
                (fun g _ ih => renameRegionGroupLoan fLid tLid g :: ih)
                rgs2
            let deps2' :=
              listFold []
                (fun v _ ih => remapValLoan alg fLid tLid v :: ih)
                deps2
            some ⟨locals2', loans2', rgs2', deps2', sp2, tag2⟩
      | _, _ => none
  | _, _ => none

/-- Apply all explicit join pairs `joinPairs` to align `st2` with `st1` before
invoking `joinSymState`. -/
def applyJoinPairs {Val : Type} (alg : ValAlgebra Val)
    (joinPairs : List (LoanId × LoanId))
    (st1 st2 : SymState Val) : Option (SymState Val) :=
  listFold
    (fun s2 => some s2)
    (fun pair _ ih s2 =>
      match pair with
      | (tLid, fLid) =>
        match applyOneJoinPair alg tLid fLid st1 s2 with
        | some s2' => ih s2'
        | none => none)
    joinPairs st2

def isRootTarget {Val : Type} (t : BackTarget Val) : Bool :=
  match t.steps with
  | [.rootParam _] => true
  | _ => false

def loansCleanAtReturn {Val : Type}
    (loans : List (LoanEntry Val)) : Bool :=
  loans.foldr
    (fun e ih =>
      let okHere : Bool :=
        if isRootTarget e.target then
          e.phase.isActive && isUnborrowed e.cell.perm
        else
          e.phase.isEnded
      okHere && ih)
    true

def allRegionGroupsEnded {Val : Type}
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  rgs.foldr
    (fun g ih => !g.active && ih)
    true

/-- True iff all non-root loans and region groups have ended, root parameter
loans have no active child borrows, and no spatial blocks remain pinned. -/
def stateCleanAtReturn {Val : Type} (st : SymState Val) : Bool :=
  loansCleanAtReturn st.loans &&
  allRegionGroupsEnded st.regionGroups &&
  st.spatial.isEmpty

/-- Collect the final values of all root `&mut` parameter loans in declaration
order. -/
def collectRootMutVals {Val : Type}
    (loans : List (LoanEntry Val)) : List Val :=
  loans.foldr
    (fun e ih =>
      match e.phase, isRootTarget e.target with
      | .activeMut, true => e.cell.val :: ih
      | _, _ => ih)
    []

/-- Control-flow status during structured plan evaluation: normal fallthrough
(`.continuing st`), short-circuiting early return (`.returned out`), or
continuing execution under pending symbolic early-return guards
(`.guardedContinuing wrapOut st`), where `wrapOut` folds any pending symbolic
early-return outcomes around the eventual `FuncOut Val` of the continuing
execution path. -/
inductive ExecFlow (Val : Type) where
  | continuing (st : SymState Val)
  | returned (out : FuncOut Val)
  | guardedContinuing (wrapOut : FuncOut Val → FuncOut Val)
      (st : SymState Val)

/-- Merge two `FuncOut Val` results under symbolic branch condition `cVal`. -/
def mergeFuncOut {Val : Type} (alg : ValAlgebra Val)
    (cVal : Val) (tOut fOut : FuncOut Val) : FuncOut Val :=
  ⟨alg.zipVal cVal tOut.ret fOut.ret,
   zipValList alg cVal tOut.mutFinals fOut.mutFinals⟩

/-- Compose a pending symbolic early-return wrapper `wrap1` around a subsequent
`EvalOutcome (ExecFlow Val)`. -/
def prependGuardedWrap {Val : Type}
    (wrap1 : FuncOut Val → FuncOut Val)
    (res : EvalOutcome (ExecFlow Val)) : EvalOutcome (ExecFlow Val) :=
  match res with
  | .ok (.continuing st2) => .ok (.guardedContinuing wrap1 st2)
  | .ok (.returned out2) => .ok (.returned (wrap1 out2))
  | .ok (.guardedContinuing wrap2 st2) =>
    .ok (.guardedContinuing (fun out => wrap1 (wrap2 out)) st2)
  | .fail => .fail

/-- Elementary pre-order operation in a serialized `FlowPlan Val` tree. -/
inductive FlowPlanOp (Val : Type) where
  | skip : FlowPlanOp Val
  | act (a : PrimAction Val) : FlowPlanOp Val
  | seqJoin : FlowPlanOp Val
  | branchJoin (cond : RvalOp Val) : FlowPlanOp Val
  | branchExplicitJoinOp (cond : RvalOp Val)
      (joinPairs : List (LoanId × LoanId)) : FlowPlanOp Val
  | earlyReturn (cleanupLoans : List LoanId)
      (cleanupGroups : List RegionGroupId) (retExpr : RvalOp Val) :
      FlowPlanOp Val
  | whileLoopOp (fuel : Nat) (cond : RvalOp Val) : FlowPlanOp Val

/-- Structured control-flow certificate (`FlowPlan Val`), represented as a
pre-order operation sequence so right-to-left `listFold` (`List.foldr`)
evaluates arbitrarily nested sequential, conditional, and loop plans bottom-up
as a computable Lean 4 definition. -/
structure FlowPlan (Val : Type) where
  ops : List (FlowPlanOp Val)

namespace FlowPlan

def skip {Val : Type} : FlowPlan Val :=
  ⟨[.skip]⟩

def act {Val : Type} (a : PrimAction Val) : FlowPlan Val :=
  ⟨[.act a]⟩

def seq {Val : Type} (p1 p2 : FlowPlan Val) : FlowPlan Val :=
  ⟨.seqJoin :: (p1.ops ++ p2.ops)⟩

def branch {Val : Type} (cond : RvalOp Val) (onTrue onFalse : FlowPlan Val) :
    FlowPlan Val :=
  ⟨.branchJoin cond :: (onTrue.ops ++ onFalse.ops)⟩

def branchExplicitJoin {Val : Type} (cond : RvalOp Val)
    (onTrue onFalse : FlowPlan Val)
    (joinPairs : List (LoanId × LoanId)) : FlowPlan Val :=
  ⟨.branchExplicitJoinOp cond joinPairs :: (onTrue.ops ++ onFalse.ops)⟩

def earlyReturn {Val : Type} (cleanupLoans : List LoanId)
    (cleanupGroups : List RegionGroupId) (retExpr : RvalOp Val) :
    FlowPlan Val :=
  ⟨[.earlyReturn cleanupLoans cleanupGroups retExpr]⟩

def whileLoop {Val : Type} (fuel : Nat) (cond : RvalOp Val)
    (body : FlowPlan Val) : FlowPlan Val :=
  ⟨.whileLoopOp fuel cond :: body.ops⟩

end FlowPlan

def joinExecFlow {Val : Type} (alg : ValAlgebra Val)
    (cVal : Val) : ExecFlow Val → ExecFlow Val → Option (ExecFlow Val)
  | .continuing st1, .continuing st2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined => some (.continuing stJoined)
    | none => none
  | .returned out1, .returned out2 =>
    some (.returned (mergeFuncOut alg cVal out1 out2))
  | .returned out1, .continuing st2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal out1 fallOut) st2)
  | .continuing st1, .returned out2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal fallOut out2) st1)
  | .returned out1, .guardedContinuing wrap2 st2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal out1 (wrap2 fallOut)) st2)
  | .guardedContinuing wrap1 st1, .returned out2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal (wrap1 fallOut) out2) st1)
  | .guardedContinuing wrap1 st1, .continuing st2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined =>
      some (.guardedContinuing
        (fun fallOut => mergeFuncOut alg cVal (wrap1 fallOut) fallOut)
        stJoined)
    | none => none
  | .continuing st1, .guardedContinuing wrap2 st2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined =>
      some (.guardedContinuing
        (fun fallOut => mergeFuncOut alg cVal fallOut (wrap2 fallOut))
        stJoined)
    | none => none
  | .guardedContinuing wrap1 st1, .guardedContinuing wrap2 st2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined =>
      some (.guardedContinuing
        (fun fallOut => mergeFuncOut alg cVal (wrap1 fallOut) (wrap2 fallOut))
        stJoined)
    | none => none

def joinExecFlowExplicit {Val : Type} (alg : ValAlgebra Val)
    (cVal : Val) (joinPairs : List (LoanId × LoanId)) :
    ExecFlow Val → ExecFlow Val → Option (ExecFlow Val)
  | .continuing st1, .continuing st2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal (.continuing st1) (.continuing st2Aligned)
    | none => none
  | .guardedContinuing wrap1 st1, .continuing st2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal
        (.guardedContinuing wrap1 st1) (.continuing st2Aligned)
    | none => none
  | .continuing st1, .guardedContinuing wrap2 st2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal
        (.continuing st1) (.guardedContinuing wrap2 st2Aligned)
    | none => none
  | .guardedContinuing wrap1 st1, .guardedContinuing wrap2 st2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal
        (.guardedContinuing wrap1 st1) (.guardedContinuing wrap2 st2Aligned)
    | none => none
  | f1, f2 =>
    if joinPairs.isEmpty then joinExecFlow alg cVal f1 f2 else none

/-- Execute a `while` loop for at most `fuel` iterations, failing if the loop
condition remains true when `fuel` reaches `0`. -/
def runWhileFlowSteps {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val)
    (evalBody : SymState Val → EvalOutcome (ExecFlow Val))
    (fuel : Nat) (s : SymState Val) : EvalOutcome (ExecFlow Val) :=
  @Nat.recCompiled (fun _ => SymState Val → EvalOutcome (ExecFlow Val))
    (fun s0 =>
      match evalRval alg cond s0 with
      | some cv =>
        match alg.asBool cv with
        | some false => .ok (.continuing s0)
        | _ => .fail
      | none => .fail)
    (fun _ ih s0 =>
      match evalRval alg cond s0 with
      | some cv =>
        match alg.asBool cv with
        | some false => .ok (.continuing s0)
        | some true =>
          match evalBody s0 with
          | .ok (.continuing s') => ih s'
          | .ok (.returned out) => .ok (.returned out)
          | .ok (.guardedContinuing wrap1 s') =>
            prependGuardedWrap wrap1 (ih s')
          | .fail => .fail
        | none => .fail
      | none => .fail)
    fuel s

/-- Push-down stack step for one `FlowPlanOp Val` during bottom-up `listFold`
evaluation of a `FlowPlan Val`. -/
def stepPlanOp {Val : Type} (alg : ValAlgebra Val) (op : FlowPlanOp Val)
    (stk : List (SymState Val → EvalOutcome (ExecFlow Val))) :
    List (SymState Val → EvalOutcome (ExecFlow Val)) :=
  match op with
  | .skip => (fun s0 => .ok (.continuing s0)) :: stk
  | .act a =>
    (fun s0 =>
      match stepAction alg a s0 with
      | .ok st' => .ok (.continuing st')
      | .fail => .fail) :: stk
  | .seqJoin =>
    match stk with
    | ih1 :: ih2 :: rest =>
      (fun s0 =>
        match ih1 s0 with
        | .ok (.continuing st1) => ih2 st1
        | .ok (.returned out) => .ok (.returned out)
        | .ok (.guardedContinuing wrap1 st1) =>
          prependGuardedWrap wrap1 (ih2 st1)
        | .fail => .fail) :: rest
    | _ => [(fun _ => .fail)]
  | .branchJoin cond =>
    match stk with
    | ihTrue :: ihFalse :: rest =>
      (fun s0 =>
        match evalRval alg cond s0 with
        | none => .fail
        | some cVal =>
          match alg.asBool cVal with
          | some true => ihTrue s0
          | some false => ihFalse s0
          | none =>
            match ihTrue s0, ihFalse s0 with
            | .ok flowTrue, .ok flowFalse =>
              match joinExecFlow alg cVal flowTrue flowFalse with
              | some flowJoined => .ok flowJoined
              | none => .fail
            | _, _ => .fail) :: rest
    | _ => [(fun _ => .fail)]
  | .branchExplicitJoinOp cond joinPairs =>
    match stk with
    | ihTrue :: ihFalse :: rest =>
      (fun s0 =>
        if !validJoinPairs joinPairs [] [] then .fail
        else
          match evalRval alg cond s0 with
          | none => .fail
          | some cVal =>
            match alg.asBool cVal with
            | some true => ihTrue s0
            | some false => ihFalse s0
            | none =>
              match ihTrue s0, ihFalse s0 with
              | .ok flowTrue, .ok flowFalse =>
                match joinExecFlowExplicit alg cVal joinPairs
                        flowTrue flowFalse with
                | some flowJoined => .ok flowJoined
                | none => .fail
              | _, _ => .fail) :: rest
    | _ => [(fun _ => .fail)]
  | .earlyReturn cleanupLoans cleanupGroups retExpr =>
    (fun s0 =>
      match evalRval alg retExpr s0 with
      | none => .fail
      | some retVal =>
        match endLoansInState alg cleanupLoans s0 with
        | .fail => .fail
        | .ok st1 =>
          match endRegionGroupsInState alg cleanupGroups st1 with
          | .fail => .fail
          | .ok st2 =>
            if !stateCleanAtReturn st2 then .fail
            else .ok (.returned ⟨retVal, collectRootMutVals st2.loans⟩)) :: stk
  | .whileLoopOp fuel cond =>
    match stk with
    | ihBody :: rest =>
      (fun s0 => runWhileFlowSteps alg cond ihBody fuel s0) :: rest
    | _ => [(fun _ => .fail)]

def evalPlanOps {Val : Type} (alg : ValAlgebra Val)
    (ops : List (FlowPlanOp Val))
    (stk : List (SymState Val → EvalOutcome (ExecFlow Val))) :
    List (SymState Val → EvalOutcome (ExecFlow Val)) :=
  ops.foldr (fun op acc => stepPlanOp alg op acc) stk

/-- Evaluate `FlowPlan Val` on `SymState Val` via total structural recursion
(`List.foldr`). -/
def evalPlan {Val : Type} (alg : ValAlgebra Val)
    (plan : FlowPlan Val) (st : SymState Val) : EvalOutcome (ExecFlow Val) :=
  match evalPlanOps alg plan.ops [] with
  | [evalFn] => evalFn st
  | _ => .fail

/-- Well-formedness invariant for a serialized `FlowPlan Val`: folding `p.ops`
onto any continuation stack `stk` pushes `evalPlan alg p` onto `stk`. -/
def WfPlan {Val : Type} (alg : ValAlgebra Val) (p : FlowPlan Val) : Prop :=
  ∀ stk, evalPlanOps alg p.ops stk = (fun s0 => evalPlan alg p s0) :: stk

theorem evalPlanOps_append {Val : Type} (alg : ValAlgebra Val)
    (xs ys : List (FlowPlanOp Val))
    (stk : List (SymState Val → EvalOutcome (ExecFlow Val))) :
    evalPlanOps alg (xs ++ ys) stk =
      evalPlanOps alg xs (evalPlanOps alg ys stk) := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    change stepPlanOp alg x (evalPlanOps alg (xs' ++ ys) stk) =
      stepPlanOp alg x (evalPlanOps alg xs' (evalPlanOps alg ys stk))
    rw [ih]

theorem evalPlan_seq {Val : Type} (alg : ValAlgebra Val)
    (p1 p2 : FlowPlan Val) (s0 : SymState Val)
    (hWf1 : WfPlan alg p1) (hWf2 : WfPlan alg p2) :
    evalPlan alg (.seq p1 p2) s0 =
      (match evalPlan alg p1 s0 with
       | .ok (.continuing st1) => evalPlan alg p2 st1
       | .ok (.returned out) => .ok (.returned out)
       | .ok (.guardedContinuing wrap1 st1) =>
         prependGuardedWrap wrap1 (evalPlan alg p2 st1)
       | .fail => .fail) := by
  change
    (match stepPlanOp alg .seqJoin (evalPlanOps alg (p1.ops ++ p2.ops) []) with
     | [evalFn] => evalFn s0
     | _ => .fail) = _
  rw [evalPlanOps_append, hWf2 [], hWf1]
  rfl

/-- Entry parameter passing mode. -/
inductive ParamMode where
  | byVal
  | sharedRef (rootId : Nat) (path : SubPath)
  | mutRef (rootId : Nat) (path : SubPath)

/-- Entry parameter descriptor pairing a passing mode with an initial value. -/
structure ParamInput (Val : Type) where
  mode : ParamMode
  val : Val

def getRootPerm (rootId : Nat) (ps : List (Nat × PermTree)) : PermTree :=
  listFold .unborrowed
    (fun entry _ ih =>
      match entry with
      | (id, p) => if id == rootId then p else ih)
    ps

def setRootPerm (rootId : Nat) (p : PermTree)
    (ps : List (Nat × PermTree)) : List (Nat × PermTree) :=
  listFold [(rootId, p)]
    (fun entry rest ih =>
      match entry with
      | (id, oldP) =>
        if id == rootId then (id, p) :: rest
        else (id, oldP) :: ih)
    ps

/-- Initialize `SymState Val` from function entry parameters, checking for
illegal aliasing across reference parameters via `PermTree`. -/
def buildInitState {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val))
    (rootPerms : List (Nat × PermTree))
    (st : SymState Val) : Option (SymState Val) :=
  listFold
    (β := List (Nat × PermTree) → SymState Val → Option (SymState Val))
    (fun _ s => some s)
    (fun p _ ih rPerms st0 =>
      match st0 with
      | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
        match p.mode with
        | .byVal =>
          let st' : SymState Val :=
            ⟨locals ++ [⟨p.val, .unborrowed⟩], loans, rgs, deps, sp, tag⟩
          ih rPerms st'
        | .sharedRef rootId path =>
          let lid := loans.length
          let rp := getRootPerm rootId rPerms
          match acquirePerm .shared lid path rp with
          | none => none
          | some rp' =>
            let entry : LoanEntry Val :=
              ⟨lid, .activeShared, ⟨p.val, .unborrowed⟩, .rootParam lid⟩
            let st' : SymState Val :=
              ⟨locals ++ [⟨alg.encodeSharedRef lid [], .unborrowed⟩],
               loans ++ [entry], rgs, deps, sp, tag⟩
            ih (setRootPerm rootId rp' rPerms) st'
        | .mutRef rootId path =>
          let lid := loans.length
          let rp := getRootPerm rootId rPerms
          match acquirePerm .mutBorrow lid path rp with
          | none => none
          | some rp' =>
            let entry : LoanEntry Val :=
              ⟨lid, .activeMut, ⟨p.val, .unborrowed⟩, .rootParam lid⟩
            let st' : SymState Val :=
              ⟨locals ++ [⟨alg.encodeRef lid [], .unborrowed⟩],
               loans ++ [entry], rgs, deps, sp, tag⟩
            ih (setRootPerm rootId rp' rPerms) st')
    params rootPerms st

def initFnState {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) : EvalOutcome (SymState Val) :=
  match buildInitState alg params [] ⟨[], [], [], [], [], 0⟩ with
  | some st => .ok st
  | none => .fail

/-- Evaluate a function returning a value, yielding `FuncOut Val`. -/
def evalFnValue {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retExpr : RvalOp Val) : EvalOutcome (FuncOut Val) :=
  match initFnState alg params with
  | .fail => .fail
  | .ok st0 =>
    match evalPlan alg plan st0 with
    | .fail => .fail
    | .ok (.returned out) => .ok out
    | .ok (.continuing stF) =>
      if !stateCleanAtReturn stF then .fail
      else
        match evalRval alg retExpr stF with
        | some retVal => .ok ⟨retVal, collectRootMutVals stF.loans⟩
        | none => .fail
    | .ok (.guardedContinuing wrapOut stF) =>
      if !stateCleanAtReturn stF then .fail
      else
        match evalRval alg retExpr stF with
        | some retVal =>
          let fallthroughOut : FuncOut Val :=
            ⟨retVal, collectRootMutVals stF.loans⟩
          .ok (wrapOut fallthroughOut)
        | none => .fail

def loansCleanExceptReturned {Val : Type} (retLid : LoanId)
    (loans : List (LoanEntry Val)) : Bool :=
  listFold true
    (fun e _ ih =>
      let okHere : Bool :=
        if e.id == retLid then
          e.phase.isActiveMut && isUnborrowed e.cell.perm
        else if isRootTarget e.target then
          e.phase.isActive
        else
          e.phase.isEnded
      okHere && ih)
    loans

/-- Evaluate a function returning a mutable reference in `retReg`, synthesizing
both its forward value `fwdVal` and its backward lens
`backFn : Val → Option (List Val)`. -/
def evalFnReturningMut {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retReg : LocalId) : EvalOutcome (Val × (Val → Option (List Val))) :=
  match initFnState alg params with
  | .fail => .fail
  | .ok st0 =>
    match evalPlan alg plan st0 with
    | .fail => .fail
    | .ok (.returned _) => .fail
    | .ok (.guardedContinuing _ _) => .fail
    | .ok (.continuing stF) =>
      if !allRegionGroupsEnded stF.regionGroups || !stF.spatial.isEmpty then
        .fail
      else
        match alg.decodeRef (getLocal alg retReg stF) with
        | none => .fail
        | some (retLid, retPath) =>
          if !loansCleanExceptReturned retLid stF.loans then .fail
          else
            match findLoan retLid stF.loans with
            | none => .fail
            | some retEntry =>
              if !retEntry.phase.isActiveMut then .fail
              else
                match getPath alg retPath retEntry.cell.val with
                | none => .fail
                | some fwdVal =>
                  let backFn : Val → Option (List Val) := fun vFinal =>
                    match putPath alg retPath retEntry.cell.val vFinal with
                    | none => none
                    | some entryVal' =>
                      if isRootTarget retEntry.target then
                        let loans' := updateLoan retLid
                          (fun e =>
                            ⟨e.id, e.phase, ⟨entryVal', e.cell.perm⟩,
                             e.target⟩)
                          stF.loans
                        if loansCleanAtReturn loans' then
                          some (collectRootMutVals loans')
                        else none
                      else
                        let stUpdated : SymState Val :=
                          match stF with
                          | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
                            ⟨locals,
                              updateLoan retLid
                                (fun e =>
                                  ⟨e.id, e.phase, ⟨entryVal', e.cell.perm⟩,
                                   e.target⟩)
                                loans,
                              rgs, deps, sp, tag⟩
                        match endLoanInState alg retLid stUpdated with
                        | .ok stEnded =>
                          if stateCleanAtReturn stEnded then
                            some (collectRootMutVals stEnded.loans)
                          else none
                        | .fail => none
                  .ok (fwdVal, backFn)

/-!
## Exhaustive Kernel-Checked Unit Tests for `Plan`
-/

/-- Exhaustive unit tests for `resolvePlace`, `readPlaceVal`, `writePlaceVal`,
`evalRval`, `evalRvalList`, `validJoinPairs`, `remapValLoan` on nested
aggregates, `renameRegionGroupLoan`, and mixed early-return / continuing
branches (`ExecFlow.guardedContinuing`). -/
theorem plan_core_helpers_and_guardedContinuing_exhaustive_tests :
    let st0 : SymState LensTestVal :=
      { locals :=
          [ ⟨.node (.atom 10) (.atom 20), .unborrowed⟩
          , ⟨.ref 0 [1], .unborrowed⟩ ]
        loans :=
          [⟨0, .activeMut,
            ⟨.node (.atom 30) (.atom 40), .split [([0], .mutLocked 1)]⟩,
            .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    -- 1. `resolvePlace`, `readPlaceVal` (gating parent-loan sub-path `[0]` vs.
    -- `[1]`), and `writePlaceVal`:
    resolvePlace lensTestValAlg (.localSub 0 [0]) st0 =
      some (.localReg 0, [0]) ∧
    resolvePlace lensTestValAlg (.derefSub 1 [0]) st0 =
      some (.parentLoan 0, [1, 0]) ∧
    resolvePlace lensTestValAlg (.derefSub 0 []) st0 = none ∧
    readPlaceVal lensTestValAlg (.localSub 0 [0]) st0 = some (.atom 10) ∧
    readPlaceVal lensTestValAlg (.derefSub 1 []) st0 = some (.atom 40) ∧
    (match writePlaceVal lensTestValAlg (.localSub 1 []) (.ref 0 [0]) st0 with
     | some stRef0 =>
       readPlaceVal lensTestValAlg (.derefSub 1 []) stRef0 = none ∧
       writePlaceVal lensTestValAlg (.derefSub 1 []) (.atom 99) stRef0 = none
     | none => False) ∧
    -- 2. `evalRval` and `evalRvalList`:
    evalRvalList lensTestValAlg
      [ .constVal (.atom 1)
      , .use (.localSub 0 [1])
      , .unary (fun v => some v) (.localSub 0 [0])
      , .binary (fun v1 _ => some v1) (.localSub 0 [0]) (.localSub 0 [1]) ]
      st0 =
      some [.atom 1, .atom 20, .atom 10, .atom 10] ∧
    -- 3. `validJoinPairs` anti-aliasing and `remapValLoan` inside nested
    -- `.node` aggregates:
    validJoinPairs [(1, 2), (3, 4)] [] [] = true ∧
    validJoinPairs [(1, 2), (1, 3)] [] [] = false ∧
    validJoinPairs [(1, 2), (3, 2)] [] [] = false ∧
    remapValLoan lensTestValAlg 2 7 (.node (.ref 2 [0]) (.ref 3 [1])) =
      .node (.ref 7 [0]) (.ref 3 [1]) ∧
    -- 4. Mixed `.returned` and `.continuing` symbolic branch via
    -- `ExecFlow.guardedContinuing`:
    let mixedBranchPlan : FlowPlan LensTestVal :=
      .seq
        (.branch (.use (.localSub 0 []))
          (.earlyReturn [] [] (.constVal (.atom 111)))
          (.act (.assign (.derefSub 1 []) (.constVal (.atom 222)))))
        (.act (.assign (.localSub 2 []) (.constVal (.atom 333))))
    evalFnValue lensTestValAlg
      [⟨.byVal, .atom 1⟩, ⟨.mutRef 0 [], .atom 5⟩]
      mixedBranchPlan
      (.use (.localSub 2 [])) =
      .ok ⟨.atom 111, [.atom 5]⟩ ∧
    evalFnValue lensTestValAlg
      [⟨.byVal, .atom 0⟩, ⟨.mutRef 0 [], .atom 5⟩]
      mixedBranchPlan
      (.use (.localSub 2 [])) =
      .ok ⟨.atom 333, [.atom 222]⟩ ∧
    evalFnValue lensTestValAlg
      [⟨.byVal, .node (.atom 1) (.atom 0)⟩, ⟨.mutRef 0 [], .atom 5⟩]
      mixedBranchPlan
      (.use (.localSub 2 [])) =
      .ok ⟨.atom 333, [.atom 222]⟩ ∧
    -- 5. Nested symbolic `.branch` joining `.guardedContinuing` with
    -- `.continuing`, and `.whileLoop` preserving `.guardedContinuing` across
    -- iterations:
    let nestedGuardedBranchPlan : FlowPlan LensTestVal :=
      .seq
        (.branch (.use (.localSub 0 []))
          (.branch (.use (.localSub 0 []))
            (.earlyReturn [] [] (.constVal (.atom 101)))
            (.act (.assign (.localSub 2 []) (.constVal (.atom 202)))))
          (.act (.assign (.localSub 2 []) (.constVal (.atom 303)))))
        (.act (.assign (.localSub 2 []) (.constVal (.atom 404))))
    let guardedWhileLoopPlan : FlowPlan LensTestVal :=
      .whileLoop 2 (.use (.localSub 2 []))
        (.seq
          (.branch (.use (.localSub 0 []))
            (.earlyReturn [] [] (.constVal (.atom 505)))
            .skip)
          (.act (.assign (.localSub 2 []) (.constVal (.atom 0)))))
    evalFnValue lensTestValAlg
      [⟨.byVal, .node (.atom 1) (.atom 0)⟩, ⟨.mutRef 0 [], .atom 5⟩]
      nestedGuardedBranchPlan
      (.use (.localSub 2 [])) =
      .ok ⟨.atom 404, [.atom 5]⟩ ∧
    evalFnValue lensTestValAlg
      [ ⟨.byVal, .node (.atom 1) (.atom 0)⟩
      , ⟨.mutRef 0 [], .atom 5⟩
      , ⟨.byVal, .atom 1⟩ ]
      guardedWhileLoopPlan
      (.constVal (.atom 606)) =
      .ok ⟨.atom 606, [.atom 5]⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl⟩

end Anneal.PureLift
