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

/-- Decode the borrow handle stored in local `reg`. Using a handle reads
`reg`, so `reg` must hold a written value whose `PermTree` permits reading (no
outstanding mutable borrow of the handle itself). Every consumer of a handle
local (dereferencing it or ending its loan) goes through this check. -/
def readLocalHandle {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (st : SymState Val) : Option (LoanId × SubPath) :=
  match getOwnerForRead alg (.localReg reg) st [] with
  | some ⟨handle, _⟩ => alg.decodeRef handle
  | none => none

/-- Resolve `PlaceExpr` in `st` to its underlying `(OwnerRef × SubPath)`. -/
def resolvePlace {Val : Type} (alg : ValAlgebra Val) (p : PlaceExpr)
    (st : SymState Val) : Option (OwnerRef × SubPath) :=
  match p with
  | .localSub reg path => some (.localReg reg, path)
  | .derefSub reg extraPath =>
    match readLocalHandle alg reg st with
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
    match owner, path with
    -- A whole-local write may also create the next fresh local.
    | .localReg reg, [] => setLocalChecked alg reg vNew st
    | _, _ =>
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

/-- Evaluate the by-value arguments of a call. Each argument is copied into
the callee, so each must satisfy `copyableVal`. -/
def evalRvalList {Val : Type} (alg : ValAlgebra Val)
    (ops : List (RvalOp Val)) (st : SymState Val) : Option (List Val) :=
  listFold (some [])
    (fun r _ ih =>
      match evalRval alg r st, ih with
      | some v, some vs =>
        if copyableVal alg st.loans v then some (v :: vs) else none
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
        let newLid := st0.loans.length
        let newEntry : LoanEntry Val :=
          ⟨newLid, .activeMut, ⟨vOut, .unborrowed⟩, .regionOut gid idx⟩
        let st1 : SymState Val :=
          match st0 with
          | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
            ⟨locals, loans ++ [newEntry], rgs, deps, sp, tag⟩
        match setLocalChecked alg dst (alg.encodeRef newLid []) st1 with
        | none => none
        | some st2 =>
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

/-- True iff `xs` contains no repeated element. -/
def allDistinctNat (xs : List Nat) : Bool :=
  listFold true (fun x rest ih => !elemLoanId x rest && ih) xs

/-- Install all region groups of a multi-region-group call into `st`. Rejects
reinstalling an already-active `groupId`, replaces any completed (inactive)
entry with the same `groupId` so repeated calls in a loop do not shadow newer
entries. When a region group has no output borrows (`outLids.isEmpty`), an
ended lock-sentinel entry is appended to `st.loans` at `lockLid` so subsequent
region groups or borrows never reuse `lockLid`.

A completed entry is not replaced while a group that was active before this
call lists its `groupId` in `requiredChildren`. That parent's outlives check
(`allRequiredGroupsEnded`) looks children up by `groupId`, and it consumes the
deposits tagged with that `groupId`, so a replacement would let it observe this
call's child instead of the child it was installed with. Installing a group
also discards leftover deposits tagged with its `groupId`: no active group may
consume them (by the rule above), and they must not reach a parent of the new
instance.

All output destinations of the call must be distinct. Outputs are bound one
at a time, so a repeated destination would let a later handle overwrite an
earlier one while both output loans stay active.

Every `requiredChildren` entry must name a group of the same call, and no two
groups of the call may require the same child; see `takeChildDeposits`. -/
def installRegionGroups {Val : Type} (alg : ValAlgebra Val)
    (pureVals : List Val) (specs : List (RegionGroupSpec Val))
    (st : SymState Val) : Option (SymState Val) :=
  let allDsts : List LocalId :=
    specs.foldr (fun spec acc => spec.outDsts ++ acc) []
  if !allDistinctNat allDsts then none
  else
  listFold
    (fun st0 => some st0)
    (fun spec _ ih st0 =>
      let alreadyActive : Bool :=
        match findRegionGroup spec.groupId st0.regionGroups with
        | some existing => existing.active
        | none => false
      let requiredByEarlierGroup : Bool :=
        st.regionGroups.any (fun g =>
          g.active && g.requiredChildren.any (fun c => c == spec.groupId))
      -- A parent's children must be groups of this same call, and no two
      -- groups of the call may share a child: a parent consumes its
      -- children's deposits, so a stale child from an earlier call or a
      -- second parent would observe the wrong deposits (or none).
      let childrenInCall : Bool :=
        spec.requiredChildren.all (fun c =>
          specs.any (fun other => other.groupId == c))
      let childShared : Bool :=
        specs.any (fun other =>
          other.groupId != spec.groupId &&
            other.requiredChildren.any (fun c =>
              spec.requiredChildren.any (fun c' => c' == c)))
      match alreadyActive || requiredByEarlierGroup || !childrenInCall ||
          childShared with
      | true => none
      | false =>
        let lockLid := st0.loans.length
        match acquireMutCallArgs alg lockLid spec.inputPlaces st0 with
        | none => none
        | some (inTargets, inMutVals, stLocked) =>
          match spec.fwdOuts pureVals inMutVals with
          | none => none
          | some outVals =>
            -- Forward output cells coexist with the locked `inTargets` (which
            -- retain their pre-call `vOld` for `targetsReplaceable` at
            -- `endRegionGroupInState`), so output cells may carry only copyable
            -- handles; otherwise a nested swap could move a unique handle out of
            -- an output cell before `backFn` resurrects it from `vOld`.
            if !outVals.all (copyableVal alg stLocked.loans) then none
            else
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
                  let deps' := deps.filter (fun d => d.1 != spec.groupId)
                  ⟨locals, loans', upsertRegionGroup rgEntry rgs, deps', sp,
                   tag⟩
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
      if !copyableVal alg st.loans v then .fail
      else
        match writePlaceVal alg dst v st with
        | some st' => .ok st'
        | none => .fail
    | none => .fail
  | .borrow dst kind src =>
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
        match setLocalChecked alg dst encVal
                ⟨locals, loans ++ [newEntry], rgs, deps, sp, tag⟩ with
        | some st' => .ok st'
        | none => .fail
  | .endLoan lid => endLoanInState alg lid st
  | .endLoanAtLocal reg =>
    match readLocalHandle alg reg st with
    | some (lid, _) => endLoanInState alg lid st
    | none => .fail
  | .call dst summary pureArgs mutArgs =>
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
            -- The returned mutable borrow cell coexists with the locked
            -- `targets` (which retain `vOld` for `replaceableVal` at
            -- `endLoanInState`), so `retVal` may carry only copyable handles;
            -- otherwise a nested swap could move a unique handle out of the
            -- returned loan cell before `summary.back` resurrects it from
            -- `vOld`.
            if !copyableVal alg stLocked.loans retVal then .fail
            else
            let newEntry : LoanEntry Val :=
              ⟨newLid, .activeMut, ⟨retVal, .unborrowed⟩,
                .lensCall targets (summary.back pureVals mutVals)⟩
            let stWithLoan : SymState Val :=
              match stLocked with
              | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
                ⟨locals, loans ++ [newEntry], rgs, deps, sp, tag⟩
            match setLocalChecked alg dst (alg.encodeRef newLid [])
                    stWithLoan with
            | some st' => .ok st'
            | none => .fail
          else
            match summary.back pureVals mutVals retVal with
            | some updatedMutVals =>
              match writebackLensTargets alg newLid targets
                      updatedMutVals stLocked with
              | some stUnlocked =>
                -- A by-value result is stored like an assigned value.
                if !copyableVal alg stUnlocked.loans retVal then .fail
                else
                  match setLocalChecked alg dst retVal stUnlocked with
                  | some st' => .ok st'
                  | none => .fail
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
  | .freezeSpatial lid codec => freezeToSpatialInState alg lid codec st
  | .mutateSpatial bid tag cells => mutateSpatialInState bid tag cells st
  | .reabsorbSpatial lid codec => reabsorbFromSpatialInState alg lid codec st

/-- Rebuild `v1` with each field present in both `v1` and `v2` replaced by
`ih f1 f2`, visiting every index below `maxFields` (gaps included). Fails if
some index is a field of only one of the two values. Callers pass a bound
above every field index of both values (`getField_lt_sizeBound`), so no field
is skipped. -/
def zipAggregateFields {Val : Type} (alg : ValAlgebra Val)
    (ih : Val → Val → Val) (maxFields : Nat) (v1 v2 : Val) : Option Val :=
  @Nat.recCompiled (fun _ => Nat → Val → Option Val)
    (fun _ acc => some acc)
    (fun _ ihField idx acc =>
      match alg.getField idx v1, alg.getField idx v2 with
      | none, none => ihField (idx + 1) acc
      | some f1, some f2 =>
        match alg.setField idx acc (ih f1 f2) with
        | some acc' => ihField (idx + 1) acc'
        | none => none
      | _, _ => none)
    maxFields 0 v1

/-- Merge two values under symbolic branch condition `cond`, preserving an
encoded reference handle unchanged when both branches hold a reference to the
exact same `(lid, path)` and recursively merging aggregate fields when both
branches hold an aggregate with matching field counts so field projections
(`alg.getField`) remain available after a symbolic branch join. -/
def zipOrKeepSameRef {Val : Type} (alg : ValAlgebra Val)
    (cond v1 v2 : Val) : Val :=
  @Nat.recCompiled (fun _ => Val → Val → Val)
    (fun a b =>
      match alg.decodeRef a, alg.decodeRef b with
      | some (l1, p1), some (l2, p2) =>
        if l1 == l2 && subPathEq p1 p2 then a
        else alg.zipVal cond a b
      | _, _ => alg.zipVal cond a b)
    (fun _ ih a b =>
      match alg.decodeRef a, alg.decodeRef b with
      | some (l1, p1), some (l2, p2) =>
        if l1 == l2 && subPathEq p1 p2 then a
        else alg.zipVal cond a b
      | _, _ =>
        match alg.getField 0 a, alg.getField 0 b with
        | some _, some _ =>
          -- Rebuilding from `a` is exact only when `a` and `b` differ at most
          -- in their fields (`sameAggregateShape_ext`).
          let fieldBound :=
            if decide (alg.sizeBound a ≤ alg.sizeBound b) then alg.sizeBound b
            else alg.sizeBound a
          if alg.sameAggregateShape a b then
            match zipAggregateFields alg ih fieldBound a b with
            | some agg => agg
            | none => alg.zipVal cond a b
          else alg.zipVal cond a b
        | _, _ => alg.zipVal cond a b)
    (alg.sizeBound v1 + 1) v1 v2

/-- Merge two value lists under symbolic branch condition `cond`. -/
def zipValList {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (xs ys : List Val) : List Val :=
  listFold
    (fun bs => bs)
    (fun x _ ih bs =>
      match bs with
      | [] => x :: ih []
      | y :: ys' => zipOrKeepSameRef alg cond x y :: ih ys')
    xs ys

/-- Project a list of branch-joined values to branch `branch` (`true` or
`false`) under condition `cond`. -/
def projectBranchValList {Val : Type} (alg : ValAlgebra Val)
    (cond : Val) (branch : Bool) (xs : List Val) : List Val :=
  listFold []
    (fun v _ ih => alg.projectBranchVal cond branch v :: ih)
    xs

/-- Join two local `PlaceCell` lists across a conditional branch join, merging
the locals that both branches hold. A local written in only one branch may be
uninitialized after the join, so it is dropped (making later reads fail)
instead of being merged with a synthetic `alg.defaultVal`. Dropping is only
sound if nothing borrows that local, so the join fails (`none`) when such a
branch-only local has a non-`.unborrowed` permission. -/
def joinPlaceCells {Val : Type} (alg : ValAlgebra Val)
    (cond : Val) (cs1 cs2 : List (PlaceCell Val)) :
    Option (List (PlaceCell Val)) :=
  let allUnborrowed (cs : List (PlaceCell Val)) : Bool :=
    listFold true (fun c _ ih => isUnborrowed c.perm && ih) cs
  listFold
    (fun bs => if allUnborrowed bs then some [] else none)
    (fun c1 rest ih bs =>
      match bs with
      | [] => if allUnborrowed (c1 :: rest) then some [] else none
      | c2 :: cs2' =>
        match ih cs2' with
        | some tail =>
          some (⟨zipOrKeepSameRef alg cond c1.val c2.val,
                 unionPerm c1.perm c2.perm⟩ :: tail)
        | none => none)
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

/-- True iff every loan entry in `es` is a fully ended branch-local loan
(with `.ended` phase, `.unborrowed` cell permissions, and not a root
parameter). Ended region-output loans (including lock sentinels) are allowed:
an ended loan is never written back again, and `joinRegionGroups` rejects any
branch-local region group that is still active, so these loans belong to
groups that ended inside the branch. -/
def allEndedBranchLocalLoans {Val : Type}
    (es : List (LoanEntry Val)) : Bool :=
  listFold true
    (fun e _ ih =>
      e.phase.isEnded && isUnborrowed e.cell.perm &&
      !isRootParamTarget e.target && ih)
    es

/-- Join two loan lists across a diamond branch join, synthesizing `.choice`
writeback targets when a loan's target differs between branches and preserving
trailing branch-local loans that were created and ended within one arm. -/
def joinLoanEntries {Val : Type} (alg : ValAlgebra Val)
    (cond : Val) (es1 es2 : List (LoanEntry Val)) :
    Option (List (LoanEntry Val)) :=
  listFold
    (fun bs =>
      if allEndedBranchLocalLoans bs then some bs else none)
    (fun e1 rest1 ih bs =>
      match bs with
      | [] =>
        if allEndedBranchLocalLoans (e1 :: rest1) then
          some (e1 :: rest1)
        else
          none
      | e2 :: es2' =>
        let specialMismatch : Bool :=
          !sameBackTargetShape e1.target e2.target &&
          (isRootParamTarget e1.target || isRootParamTarget e2.target ||
           isRegionOutTarget e1.target || isRegionOutTarget e2.target)
        if e1.id == e2.id && e1.phase.samePhase e2.phase && !specialMismatch then
          match ih es2' with
          | some rest =>
            let mergedEntry : LoanEntry Val :=
              ⟨e1.id, e1.phase,
                ⟨zipOrKeepSameRef alg cond e1.cell.val e2.cell.val,
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

/-- Join two region-group tables across a diamond branch join. Entries are
paired by position:
- Two active entries must agree on all structural metadata (`groupId`,
  `lockLid`, `inputTargets`, `outputLoans`, `requiredChildren`); their
  `backFn` closures are merged under `cond` after projecting `outVals` and
  `deps` to each branch via `projectBranchValList`.
- Two inactive entries need only agree on `groupId`: a completed group's
  metadata is never consulted again, so a branch that reinstalled and ended the
  group may differ from one that did not.
- Trailing entries present in only one branch are kept if they are inactive
  and no active group requires them. Such a group was installed and ended
  inside that branch; requiring absence of an active parent keeps the join
  from reporting a child as ended that the other branch never ran.

Any deposits left by a branch-local group make the deposit lists differ, which
`joinRegionDeposits` rejects. -/
def joinRegionGroups {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (gs1 gs2 : List (RegionGroupEntry Val)) :
    Option (List (RegionGroupEntry Val)) :=
  -- Active entries can only be paired with equal active entries, so the
  -- active groups of `gs1` are those of the joined table.
  let branchLocalOk (g : RegionGroupEntry Val) : Bool :=
    !g.active &&
      !gs1.any (fun a =>
        a.active && a.requiredChildren.any (fun c => c == g.groupId))
  listFold
    (fun bs => if bs.all branchLocalOk then some bs else none)
    (fun g1 rest1 ih bs =>
      match bs with
      | [] =>
        if (g1 :: rest1).all branchLocalOk then some (g1 :: rest1) else none
      | g2 :: gs2' =>
        if g1.groupId == g2.groupId && !g1.active && !g2.active then
          match ih gs2' with
          | some rest => some (g1 :: rest)
          | none => none
        else if g1.groupId == g2.groupId &&
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
                let outT := projectBranchValList alg cond true outVals
                let depsT := projectBranchValList alg cond true deps
                let outF := projectBranchValList alg cond false outVals
                let depsF := projectBranchValList alg cond false deps
                match alg.asBool cond with
                | some true => g1.backFn outT depsT
                | some false => g2.backFn outF depsF
                | none =>
                  match g1.backFn outT depsT, g2.backFn outF depsF with
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

/-- Join two tagged deposit lists across a conditional branch join. Both
branches must hold the same producers in the same order; the values are merged
under `cond`. -/
def joinRegionDeposits {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (ds1 ds2 : List (RegionGroupId × Val)) :
    Option (List (RegionGroupId × Val)) :=
  listFold
    (fun bs =>
      match bs with
      | [] => some []
      | _ :: _ => none)
    (fun d1 _ ih bs =>
      match bs with
      | [] => none
      | d2 :: bs' =>
        if d1.1 == d2.1 then
          match ih bs' with
          | some rest =>
            some ((d1.1, zipOrKeepSameRef alg cond d1.2 d2.2) :: rest)
          | none => none
        else none)
    ds1 ds2

/-- Join two symbolic states across a conditional diamond branch, requiring
matching `regionDeposits` producers (`joinRegionDeposits`) and taking the
maximum of `st1.nextSpatialTag` and `st2.nextSpatialTag` so spatial provenance
tags remain fresh relative to both branch histories. -/
def joinSymState {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (st1 st2 : SymState Val) : Option (SymState Val) :=
  if !st1.spatial.isEmpty || !st2.spatial.isEmpty then
    none
  else
    match joinLoanEntries alg cond st1.loans st2.loans,
          joinRegionGroups alg cond st1.regionGroups st2.regionGroups,
          joinRegionDeposits alg cond st1.regionDeposits st2.regionDeposits with
    | some loans', some rgs', some deps' =>
      let nextTag :=
        if decide (st1.nextSpatialTag ≤ st2.nextSpatialTag) then
          st2.nextSpatialTag
        else
          st1.nextSpatialTag
      match joinPlaceCells alg cond st1.locals st2.locals with
      | some locals' =>
        some ⟨locals',
              loans',
              rgs',
              deps',
              [],
              nextTag⟩
      | none => none
    | _, _, _ => none

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

/-- Remap an encoded reference value (including references nested inside
aggregates) from `fLid` to `tLid`. -/
def remapValLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (v : Val) : Val :=
  alg.remapRefInVal fLid tLid v

/-- Remap encoded reference values from `fLid` to `tLid` across a list of
values. -/
def remapValListLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (vals : List Val) : List Val :=
  listFold []
    (fun u _ ih => remapValLoan alg fLid tLid u :: ih)
    vals

def renameBackTargetStepLoan {Val : Type} (alg : ValAlgebra Val)
    (oldLid newLid : LoanId) :
    BackTargetStep Val → BackTargetStep Val
  | .rootParam i => .rootParam i
  | .direct o p => .direct (renameOwnerLoan oldLid newLid o) p
  | .choiceJoin cond => .choiceJoin (remapValLoan alg oldLid newLid cond)
  | .lensCall targets backFn =>
    let targets' :=
      listFold []
        (fun op _ ih =>
          match op with
          | (o, p) => (renameOwnerLoan oldLid newLid o, p) :: ih)
        targets
    let backFn' : Val → Option (List Val) :=
      fun v =>
        match backFn (remapValLoan alg newLid oldLid v) with
        | some vals => some (remapValListLoan alg oldLid newLid vals)
        | none => none
    .lensCall targets' backFn'
  | .regionOut gid idx => .regionOut gid idx

/-- Rename parent loan references and backward-lens output reference handles
from `oldLid` to `newLid` inside a `BackTarget Val`. -/
def renameBackTargetLoan {Val : Type} (alg : ValAlgebra Val)
    (oldLid newLid : LoanId) (target : BackTarget Val) : BackTarget Val :=
  ⟨listFold []
    (fun s _ ih => renameBackTargetStepLoan alg oldLid newLid s :: ih)
    target.steps⟩

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

/-- Rename loan references and backward-closure input/output reference handles
between `oldLid` and `newLid` inside a `RegionGroupEntry Val`. -/
def renameRegionGroupLoan {Val : Type} (alg : ValAlgebra Val)
    (oldLid newLid : LoanId) (g : RegionGroupEntry Val) :
    RegionGroupEntry Val :=
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
  let backFn' : List Val → List Val → Option (List Val × List Val) :=
    fun outs deps =>
      let outsOld := remapValListLoan alg newLid oldLid outs
      let depsOld := remapValListLoan alg newLid oldLid deps
      match g.backFn outsOld depsOld with
      | some (inUpd, depUpd) =>
        some (remapValListLoan alg oldLid newLid inUpd,
              remapValListLoan alg oldLid newLid depUpd)
      | none => none
  ⟨g.groupId, g.active, lockLid', targets', outLoans',
   g.requiredChildren, backFn'⟩

/-- True iff `v` may contain a handle to loan `lid` (or nests too deeply to
tell; see `collectHandles`). -/
def mayMentionLoan {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (v : Val) : Bool :=
  match collectHandles alg v with
  | some lids => elemLoanId lid lids
  | none => true

/-- True iff some local, loan cell, or region deposit of `st` may hold a handle
to loan `lid`. -/
def staleHandleTo {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (st : SymState Val) : Bool :=
  st.locals.any (fun c => mayMentionLoan alg lid c.val) ||
    st.loans.any (fun e => mayMentionLoan alg lid e.cell.val) ||
    st.regionDeposits.any (fun d => mayMentionLoan alg lid d.2)

/-- Apply a single explicit join pair `(tLid, fLid)` to align `st2` with `st1`,
verifying that `tLid` is active in `st1`, `fLid` is active with the same phase
in `st2`, and remapping `fLid` to `tLid` across locals, loan cells,
`BackTarget`s, `regionGroups`, and `regionDeposits` in `st2` when
`tLid != fLid`. -/
def applyOneJoinPair {Val : Type} (alg : ValAlgebra Val)
    (tLid fLid : LoanId) (st1 st2 : SymState Val) : Option (SymState Val) :=
  if !hasUniqueLoanId tLid st1.loans || !hasUniqueLoanId fLid st2.loans then none
  else
  match findLoan tLid st1.loans, findLoan fLid st2.loans with
  | some e1, some e2 =>
    if !e1.phase.isActive || !e1.phase.samePhase e2.phase then none
    else if tLid == fLid then some st2
    else if !hasUniqueLoanId tLid st2.loans || !hasUniqueLoanId fLid st1.loans then none
    else
      match findLoan tLid st2.loans, findLoan fLid st1.loans with
      | some e2AtT, some e1AtF =>
        -- Renaming a root-parameter loan would turn its `.rootParam` target
        -- into a `.choice` with a local target, which `isRootTarget` no
        -- longer recognizes; and renaming a `.regionOut` loan is only valid
        -- when both branches share the exact same `.regionOut gid idx` target.
        let regOutMismatch : Bool :=
          (isRegionOutTarget e1.target || isRegionOutTarget e2.target) &&
          !sameBackTargetShape e1.target e2.target
        if isRootParamTarget e1.target || isRootParamTarget e2.target ||
           isRootParamTarget e2AtT.target || isRootParamTarget e1AtF.target ||
           regOutMismatch then none
        else if !e2AtT.phase.isEnded || !e1AtF.phase.isEnded then none
        else if !noResidualLoanPerm tLid st2 || !noResidualLoanPerm fLid st1 then none
        -- `fLid` is renamed to `tLid` in `st2`, so a stale handle to `st2`'s
        -- ended loan `tLid` would come back to life as a handle to the moved
        -- entry.
        else if staleHandleTo alg tLid st2 then none
        else
          match st2 with
          | ⟨locals2, loans2, rgs2, deps2, sp2, tag2⟩ =>
            let locals2' := remapPlaceCellsLoan alg fLid tLid locals2
            let movedEntry : LoanEntry Val :=
              ⟨tLid, e2.phase,
               ⟨remapValLoan alg fLid tLid e2.cell.val,
                renameLoanPerm fLid tLid e2.cell.perm⟩,
               renameBackTargetLoan alg fLid tLid e2.target⟩
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
                     renameBackTargetLoan alg fLid tLid e.target⟩ :: ih)
                loans2
            let rgs2' :=
              listFold []
                (fun g _ ih => renameRegionGroupLoan alg fLid tLid g :: ih)
                rgs2
            let deps2' :=
              listFold []
                (fun d _ ih => (d.1, remapValLoan alg fLid tLid d.2) :: ih)
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

/-- Forward value and backward writeback closure synthesized for a function
returning a mutable reference. -/
abbrev MutRetSummary (Val : Type) := Val × (Val → Option (List Val))

/-- Sanitize a `MutRetSummary Val` so its forward value is handle-free and its
backward closure rejects any caller-supplied `vFinal` containing a borrow handle
as well as any final parameter list containing a borrow handle. -/
def sanitizeMutRetSummary {Val : Type} (alg : ValAlgebra Val)
    (m : MutRetSummary Val) : Option (MutRetSummary Val) :=
  if !handleFreeVal alg m.1 then none
  else
    some
      (m.1,
       fun vFinal =>
         if !handleFreeVal alg vFinal then none
         else
           match m.2 vFinal with
           | some finals =>
             if finals.all (handleFreeVal alg) then some finals else none
           | none => none)

/-- Merge two `MutRetSummary Val` results under symbolic branch condition
`cVal`, preserving identical encoded references via `zipOrKeepSameRef` and
projecting branch-specialized final values via `alg.projectBranchVal` before
invoking `back1` and `back2`. -/
def mergeMutRet {Val : Type} (alg : ValAlgebra Val) (cVal : Val)
    (tMut fMut : Option (MutRetSummary Val)) : Option (MutRetSummary Val) :=
  match tMut, fMut with
  | some (fwd1, back1), some (fwd2, back2) =>
    sanitizeMutRetSummary alg
      (zipOrKeepSameRef alg cVal fwd1 fwd2,
       fun vFinal =>
         let vFinal1 := alg.projectBranchVal cVal true vFinal
         let vFinal2 := alg.projectBranchVal cVal false vFinal
         match back1 vFinal1, back2 vFinal2 with
         | some finals1, some finals2 =>
           some (zipValList alg cVal finals1 finals2)
         | _, _ => none)
  | _, _ => none

def loansCleanExceptReturned {Val : Type} (retLid : LoanId)
    (loans : List (LoanEntry Val)) : Bool :=
  listFold true
    (fun e _ ih =>
      let okHere : Bool :=
        if !hasUniqueLoanId e.id loans then false
        else if e.id == retLid then
          e.phase.isActiveMut && isUnborrowed e.cell.perm &&
          noActiveChildLoanEdges retLid loans &&
          match rootParamIdxOpt e.target with
          | some idx => countRootParamIdx idx loans == 1
          | none => true
        else
          match rootParamIdxOpt e.target with
          | some idx =>
            e.phase.isActive && countRootParamIdx idx loans == 1
          | none =>
            e.phase.isEnded
      okHere && ih)
    loans

/-- True iff every leaf of `target` ultimately writes back to storage that
outlives the current frame: following `.direct (.parentLoan l)` leaves through
`loans` (bounded by `loans.length + 1` steps), no leaf may name a local
register (`.direct (.localReg _)`), which dies at return. Root parameters and
region outputs have no local leaves. -/
def targetOutlivesFrame {Val : Type} (loans : List (LoanEntry Val))
    (target : BackTarget Val) : Bool :=
  @Nat.recCompiled (fun _ => BackTarget Val → Bool)
    (fun _ => false)
    (fun _ ih t =>
      (targetLeaves t).all (fun leaf =>
        match leaf with
        | (.localReg _, _) => false
        | (.parentLoan l, _) =>
          match findLoan l loans with
          | some e => ih e.target
          | none => false))
    (loans.length + 1) target

/-- Synthesize `(fwdVal, backFn)` for a returned mutable reference `retRefVal`
in terminal or early-return state `stF`. -/
def synthesizeMutReturnFromVal {Val : Type} (alg : ValAlgebra Val)
    (retRefVal : Val) (stF : SymState Val) : Option (MutRetSummary Val) :=
  if !allRegionGroupsEnded stF.regionGroups || !stF.spatial.isEmpty ||
     !stF.regionDeposits.isEmpty then
    none
  else
    match alg.decodeRef retRefVal with
    | none => none
    | some (retLid, retPath) =>
      if !loansCleanExceptReturned retLid stF.loans then none
      else
        match findLoan retLid stF.loans with
        | none => none
        | some retEntry =>
          -- A returned `&mut` must not be backed by a local of this frame.
          if !retEntry.phase.isActiveMut ||
             !targetOutlivesFrame stF.loans retEntry.target then none
          else
            match getPath alg retPath retEntry.cell.val with
            | none => none
            | some fwdVal =>
              -- The forward value and the final parameter values reach the
              -- caller, so neither may carry a handle to a loan of this frame.
              if !handleFreeVal alg fwdVal then none
              else
              let handleFreeFinals (finals : List Val) : Option (List Val) :=
                if finals.all (handleFreeVal alg) then some finals else none
              let backFn : Val → Option (List Val) := fun vFinal =>
                if !handleFreeVal alg vFinal then none
                else
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
                      handleFreeFinals (collectRootMutVals loans')
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
                        handleFreeFinals (collectRootMutVals stEnded.loans)
                      else none
                    | .fail => none
              some (fwdVal, backFn)

/-- Control-flow status during structured plan evaluation: normal fallthrough
(`.continuing st`), short-circuiting early return (`.returned out valClean
mutOut`), or continuing execution under pending symbolic early-return guards
(`.guardedContinuing wrapOut st valClean wrapMut`), where `wrapOut` and
`wrapMut` fold any pending symbolic early-return outcomes around the eventual
return of the continuing execution path. -/
inductive ExecFlow (Val : Type) where
  | continuing (st : SymState Val)
  | returned (out : FuncOut Val)
      (valClean : Bool := true)
      (mutOut : Option (MutRetSummary Val) := none)
  | guardedContinuing (wrapOut : FuncOut Val → FuncOut Val)
      (st : SymState Val)
      (valClean : Bool := true)
      (wrapMut : Option (MutRetSummary Val) → Option (MutRetSummary Val) :=
        fun m => m)

/-- Merge two `FuncOut Val` results under symbolic branch condition `cVal`. -/
def mergeFuncOut {Val : Type} (alg : ValAlgebra Val)
    (cVal : Val) (tOut fOut : FuncOut Val) : FuncOut Val :=
  ⟨zipOrKeepSameRef alg cVal tOut.ret fOut.ret,
   zipValList alg cVal tOut.mutFinals fOut.mutFinals⟩

/-- Compose pending symbolic early-return wrappers around a subsequent
`EvalOutcome (ExecFlow Val)`. -/
def prependGuardedWrap {Val : Type}
    (wrap1 : FuncOut Val → FuncOut Val)
    (clean1 : Bool := true)
    (wrapMut1 : Option (MutRetSummary Val) → Option (MutRetSummary Val) :=
      fun m => m)
    (res : EvalOutcome (ExecFlow Val)) : EvalOutcome (ExecFlow Val) :=
  match res with
  | .ok (.continuing st2) =>
    .ok (.guardedContinuing wrap1 st2 clean1 wrapMut1)
  | .ok (.returned out2 clean2 mut2) =>
    .ok (.returned (wrap1 out2) (clean1 && clean2) (wrapMut1 mut2))
  | .ok (.guardedContinuing wrap2 st2 clean2 wrapMut2) =>
    .ok (.guardedContinuing
      (fun out => wrap1 (wrap2 out))
      st2
      (clean1 && clean2)
      (fun m => wrapMut1 (wrapMut2 m)))
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
  | .returned out1 c1 m1, .returned out2 c2 m2 =>
    some (.returned
      (mergeFuncOut alg cVal out1 out2)
      (c1 && c2)
      (mergeMutRet alg cVal m1 m2))
  | .returned out1 c1 m1, .continuing st2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal out1 fallOut)
      st2
      c1
      (fun fallMut => mergeMutRet alg cVal m1 fallMut))
  | .continuing st1, .returned out2 c2 m2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal fallOut out2)
      st1
      c2
      (fun fallMut => mergeMutRet alg cVal fallMut m2))
  | .returned out1 c1 m1, .guardedContinuing wrap2 st2 c2 wrapMut2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal out1 (wrap2 fallOut))
      st2
      (c1 && c2)
      (fun fallMut => mergeMutRet alg cVal m1 (wrapMut2 fallMut)))
  | .guardedContinuing wrap1 st1 c1 wrapMut1, .returned out2 c2 m2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal (wrap1 fallOut) out2)
      st1
      (c1 && c2)
      (fun fallMut => mergeMutRet alg cVal (wrapMut1 fallMut) m2))
  | .guardedContinuing wrap1 st1 c1 wrapMut1, .continuing st2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined =>
      some (.guardedContinuing
        (fun fallOut => mergeFuncOut alg cVal (wrap1 fallOut) fallOut)
        stJoined
        c1
        (fun fallMut => mergeMutRet alg cVal (wrapMut1 fallMut) fallMut))
    | none => none
  | .continuing st1, .guardedContinuing wrap2 st2 c2 wrapMut2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined =>
      some (.guardedContinuing
        (fun fallOut => mergeFuncOut alg cVal fallOut (wrap2 fallOut))
        stJoined
        c2
        (fun fallMut => mergeMutRet alg cVal fallMut (wrapMut2 fallMut)))
    | none => none
  | .guardedContinuing wrap1 st1 c1 wrapMut1,
    .guardedContinuing wrap2 st2 c2 wrapMut2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined =>
      some (.guardedContinuing
        (fun fallOut => mergeFuncOut alg cVal (wrap1 fallOut) (wrap2 fallOut))
        stJoined
        (c1 && c2)
        (fun fallMut =>
          mergeMutRet alg cVal (wrapMut1 fallMut) (wrapMut2 fallMut)))
    | none => none

def joinExecFlowExplicit {Val : Type} (alg : ValAlgebra Val)
    (cVal : Val) (joinPairs : List (LoanId × LoanId)) :
    ExecFlow Val → ExecFlow Val → Option (ExecFlow Val)
  | .continuing st1, .continuing st2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal (.continuing st1) (.continuing st2Aligned)
    | none => none
  | .guardedContinuing wrap1 st1 c1 wrapMut1, .continuing st2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal
        (.guardedContinuing wrap1 st1 c1 wrapMut1) (.continuing st2Aligned)
    | none => none
  | .continuing st1, .guardedContinuing wrap2 st2 c2 wrapMut2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal
        (.continuing st1) (.guardedContinuing wrap2 st2Aligned c2 wrapMut2)
    | none => none
  | .guardedContinuing wrap1 st1 c1 wrapMut1,
    .guardedContinuing wrap2 st2 c2 wrapMut2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal
        (.guardedContinuing wrap1 st1 c1 wrapMut1)
        (.guardedContinuing wrap2 st2Aligned c2 wrapMut2)
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
          | .ok (.returned out c m) => .ok (.returned out c m)
          | .ok (.guardedContinuing wrap1 s' c1 wrapMut1) =>
            prependGuardedWrap wrap1 c1 wrapMut1 (ih s')
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
        | .ok (.returned out c m) => .ok (.returned out c m)
        | .ok (.guardedContinuing wrap1 st1 c1 wrapMut1) =>
          prependGuardedWrap wrap1 c1 wrapMut1 (ih2 st1)
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
            let out : FuncOut Val := ⟨retVal, collectRootMutVals st2.loans⟩
            let valClean := stateCleanAtReturn st2 && handleFreeOut alg out
            let mutOut := synthesizeMutReturnFromVal alg retVal st2
            let noMutOut :=
              match mutOut with
              | none => true
              | some _ => false
            if !valClean && noMutOut then .fail
            else
              .ok (.returned out valClean mutOut)) :: stk
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
       | .ok (.returned out c m) => .ok (.returned out c m)
       | .ok (.guardedContinuing wrap1 st1 c1 wrapMut1) =>
         prependGuardedWrap wrap1 c1 wrapMut1 (evalPlan alg p2 st1)
       | .fail => .fail) := by
  change
    (match stepPlanOp alg .seqJoin (evalPlanOps alg (p1.ops ++ p2.ops) []) with
     | [evalFn] => evalFn s0
     | _ => .fail) = _
  rw [evalPlanOps_append, hWf2 [], hWf1]
  rfl

theorem wfPlan_skip {Val : Type} (alg : ValAlgebra Val) :
    WfPlan alg .skip :=
  fun _ => rfl

theorem wfPlan_act {Val : Type} (alg : ValAlgebra Val) (a : PrimAction Val) :
    WfPlan alg (.act a) :=
  fun _ => rfl

theorem wfPlan_earlyReturn {Val : Type} (alg : ValAlgebra Val)
    (ls : List LoanId) (gs : List RegionGroupId) (r : RvalOp Val) :
    WfPlan alg (.earlyReturn ls gs r) :=
  fun _ => rfl

theorem wfPlan_seq {Val : Type} (alg : ValAlgebra Val)
    {p1 p2 : FlowPlan Val} (hWf1 : WfPlan alg p1) (hWf2 : WfPlan alg p2) :
    WfPlan alg (.seq p1 p2) := by
  intro stk
  change stepPlanOp alg .seqJoin (evalPlanOps alg (p1.ops ++ p2.ops) stk) =
    (fun s0 =>
      match stepPlanOp alg .seqJoin (evalPlanOps alg (p1.ops ++ p2.ops) []) with
      | [evalFn] => evalFn s0
      | _ => .fail) :: stk
  rw [evalPlanOps_append, hWf2 stk, hWf1, evalPlanOps_append, hWf2 [], hWf1]
  rfl

theorem wfPlan_branch {Val : Type} (alg : ValAlgebra Val) (cond : RvalOp Val)
    {p1 p2 : FlowPlan Val} (hWf1 : WfPlan alg p1) (hWf2 : WfPlan alg p2) :
    WfPlan alg (.branch cond p1 p2) := by
  intro stk
  change stepPlanOp alg (.branchJoin cond) (evalPlanOps alg (p1.ops ++ p2.ops) stk) =
    (fun s0 =>
      match stepPlanOp alg (.branchJoin cond) (evalPlanOps alg (p1.ops ++ p2.ops) []) with
      | [evalFn] => evalFn s0
      | _ => .fail) :: stk
  rw [evalPlanOps_append, hWf2 stk, hWf1, evalPlanOps_append, hWf2 [], hWf1]
  rfl

theorem wfPlan_branchExplicitJoin {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val) (joinPairs : List (LoanId × LoanId))
    {p1 p2 : FlowPlan Val} (hWf1 : WfPlan alg p1) (hWf2 : WfPlan alg p2) :
    WfPlan alg (.branchExplicitJoin cond p1 p2 joinPairs) := by
  intro stk
  change stepPlanOp alg (.branchExplicitJoinOp cond joinPairs)
      (evalPlanOps alg (p1.ops ++ p2.ops) stk) =
    (fun s0 =>
      match stepPlanOp alg (.branchExplicitJoinOp cond joinPairs)
              (evalPlanOps alg (p1.ops ++ p2.ops) []) with
      | [evalFn] => evalFn s0
      | _ => .fail) :: stk
  rw [evalPlanOps_append, hWf2 stk, hWf1, evalPlanOps_append, hWf2 [], hWf1]
  rfl

theorem wfPlan_whileLoop {Val : Type} (alg : ValAlgebra Val)
    (fuel : Nat) (cond : RvalOp Val) {body : FlowPlan Val}
    (hWfB : WfPlan alg body) :
    WfPlan alg (.whileLoop fuel cond body) := by
  intro stk
  change stepPlanOp alg (.whileLoopOp fuel cond) (evalPlanOps alg body.ops stk) =
    (fun s0 =>
      match stepPlanOp alg (.whileLoopOp fuel cond) (evalPlanOps alg body.ops []) with
      | [evalFn] => evalFn s0
      | _ => .fail) :: stk
  rw [hWfB stk, hWfB []]
  rfl

theorem evalPlan_whileLoop {Val : Type} (alg : ValAlgebra Val)
    (fuel : Nat) (cond : RvalOp Val) (body : FlowPlan Val) (s0 : SymState Val)
    (hWfB : WfPlan alg body) :
    evalPlan alg (.whileLoop fuel cond body) s0 =
      runWhileFlowSteps alg cond (evalPlan alg body) fuel s0 := by
  change
    (match stepPlanOp alg (.whileLoopOp fuel cond) (evalPlanOps alg body.ops []) with
     | [evalFn] => evalFn s0
     | _ => .fail) = _
  rw [hWfB []]
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

/-- Value of a new shared parameter at `path` within a root whose existing
borrows are `rp`, keeping aliased shared parameters coherent. Each root-parameter
loan stores its own value, and `ValAlgebra` cannot compare values, so a shared
parameter that overlaps an earlier shared parameter of the same root takes its
value from that earlier loan instead of from the caller-supplied `supplied`:
- No earlier loan overlaps `path`: use `supplied`.
- An earlier shared loan `l0` at `p0` with `p0` a prefix of `path`: project
  `path`'s suffix out of `l0`'s value (`getPath`), so both parameters observe
  the same memory.
- Otherwise (`path` strictly encloses an earlier borrow, or the overlapping
  entry is not a shared loan): `none`, since the larger value cannot be derived
  from the smaller one. -/
def aliasedSharedParamVal {Val : Type} (alg : ValAlgebra Val)
    (path : SubPath) (rp : PermTree) (loans : List (LoanEntry Val))
    (supplied : Val) : Option Val :=
  -- `some none`: no overlap seen yet; `some (some v)`: derived value `v`;
  -- `none`: some overlapping entry cannot supply a coherent value.
  let derived : Option (Option Val) :=
    (toEntries rp).foldr
      (fun entry acc =>
        match acc with
        | none => none
        | some cand =>
          if !subPathOverlaps entry.1 path then some cand
          else
            match stripSubPathPrefix entry.1 path, entry.2 with
            | some rel, .shared (l0 :: _) =>
              match findLoan l0 loans with
              | some e0 =>
                match getPath alg rel e0.cell.val with
                | some v => some (some v)
                | none => none
              | none => none
            | _, _ => none)
      (some none)
  match derived with
  | none => none
  | some none => some supplied
  | some (some v) => some v

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
      -- Neither a by-value parameter nor the initial pointed-to value of a
      -- reference parameter may carry a decodable frame-loan handle, which
      -- would alias a parameter loan or a loan allocated later in the body.
      match collectHandles alg p.val with
      | some [] =>
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
            match aliasedSharedParamVal alg path rp loans p.val,
                  acquirePerm .shared lid path rp with
            | none, _ => none
            | _, none => none
            | some val, some rp' =>
              let entry : LoanEntry Val :=
                ⟨lid, .activeShared, ⟨val, .unborrowed⟩, .rootParam lid⟩
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
              ih (setRootPerm rootId rp' rPerms) st'
      | _ => none)
    params rootPerms st

def initFnState {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) : EvalOutcome (SymState Val) :=
  match buildInitState alg params [] ⟨[], [], [], [], [], 0⟩ with
  | some st => .ok st
  | none => .fail

/-- Evaluate a function returning a value, yielding `FuncOut Val`. Neither the
returned value nor any final `&mut` parameter value may contain a borrow
handle (`handleFreeOut`): a handle would name a loan of this frame (or a root
parameter loan the caller still owns), and functions that return references go
through `evalFnReturningMut` instead. -/
def evalFnValue {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retExpr : RvalOp Val) : EvalOutcome (FuncOut Val) :=
  match initFnState alg params with
  | .fail => .fail
  | .ok st0 =>
    match evalPlan alg plan st0 with
    | .fail => .fail
    | .ok (.returned out valClean _) =>
      if !valClean || !handleFreeOut alg out then .fail else .ok out
    | .ok (.continuing stF) =>
      if !stateCleanAtReturn stF then .fail
      else
        match evalRval alg retExpr stF with
        | some retVal =>
          let out : FuncOut Val := ⟨retVal, collectRootMutVals stF.loans⟩
          if !handleFreeOut alg out then .fail else .ok out
        | none => .fail
    | .ok (.guardedContinuing wrapOut stF valClean _) =>
      if !valClean || !stateCleanAtReturn stF then .fail
      else
        match evalRval alg retExpr stF with
        | some retVal =>
          let fallthroughOut : FuncOut Val :=
            ⟨retVal, collectRootMutVals stF.loans⟩
          let out := wrapOut fallthroughOut
          if !handleFreeOut alg out then .fail else .ok out
        | none => .fail

/-- Evaluate a function returning a mutable reference in `retReg` (or via
`.earlyReturn`), synthesizing both its forward value `fwdVal` and its backward
lens `backFn : Val → Option (List Val)`. -/
def evalFnReturningMut {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retReg : LocalId) : EvalOutcome (Val × (Val → Option (List Val))) :=
  match initFnState alg params with
  | .fail => .fail
  | .ok st0 =>
    let rawMut : Option (MutRetSummary Val) :=
      match evalPlan alg plan st0 with
      | .fail => none
      | .ok (.returned _ _ mutOpt) => mutOpt
      | .ok (.continuing stF) =>
        match readPlaceVal alg (.localSub retReg []) stF with
        | some retRef => synthesizeMutReturnFromVal alg retRef stF
        | none => none
      | .ok (.guardedContinuing _ stF _ wrapMut) =>
        let fallMut :=
          match readPlaceVal alg (.localSub retReg []) stF with
          | some retRef => synthesizeMutReturnFromVal alg retRef stF
          | none => none
        wrapMut fallMut
    match rawMut with
    | some mutRet =>
      match sanitizeMutRetSummary alg mutRet with
      | some cleanRet => .ok cleanRet
      | none => .fail
    | none => .fail

/-- Every successful `evalFnValue` return is handle-free (`handleFreeOut`). -/
theorem evalFnValue_handleFreeOut {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retExpr : RvalOp Val) (out : FuncOut Val)
    (h : evalFnValue alg params plan retExpr = .ok out) :
    handleFreeOut alg out = true := by
  dsimp [evalFnValue] at h
  revert h
  cases initFnState alg params with
  | fail => intro h; nomatch h
  | ok st0 =>
    dsimp
    cases evalPlan alg plan st0 with
    | fail => intro h; nomatch h
    | ok flow =>
      cases flow with
      | returned out' valClean _ =>
        dsimp
        cases valClean with
        | false => intro h; nomatch h
        | true =>
          cases hFree : handleFreeOut alg out' with
          | false => intro h; nomatch h
          | true =>
            dsimp
            intro h
            injection h with hEq
            subst hEq
            exact hFree
      | continuing stF =>
        dsimp
        cases stateCleanAtReturn stF with
        | false => intro h; nomatch h
        | true =>
          dsimp
          cases evalRval alg retExpr stF with
          | none => intro h; nomatch h
          | some retVal =>
            dsimp
            cases hFree : handleFreeOut alg ⟨retVal, collectRootMutVals stF.loans⟩ with
            | false => intro h; nomatch h
            | true =>
              dsimp
              intro h
              injection h with hEq
              subst hEq
              exact hFree
      | guardedContinuing wrapOut stF valClean _ =>
        dsimp
        cases valClean with
        | false => intro h; nomatch h
        | true =>
          cases stateCleanAtReturn stF with
          | false => intro h; nomatch h
          | true =>
            dsimp
            cases evalRval alg retExpr stF with
            | none => intro h; nomatch h
            | some retVal =>
              dsimp
              cases hFree :
                handleFreeOut alg
                  (wrapOut ⟨retVal, collectRootMutVals stF.loans⟩) with
              | false => intro h; nomatch h
              | true =>
                dsimp
                intro h
                injection h with hEq
                subst hEq
                exact hFree

theorem sanitizeMutRetSummary_handleFree {Val : Type} (alg : ValAlgebra Val)
    (mutRet : MutRetSummary Val) (fwd : Val) (backFn : Val → Option (List Val))
    (h : sanitizeMutRetSummary alg mutRet = some (fwd, backFn)) :
    handleFreeVal alg fwd = true ∧
    ∀ vFinal finals,
      backFn vFinal = some finals →
      handleFreeVal alg vFinal = true ∧
      finals.all (handleFreeVal alg) = true := by
  dsimp [sanitizeMutRetSummary] at h
  revert h
  cases hFwd : handleFreeVal alg mutRet.1 with
  | false => intro h; nomatch h
  | true =>
    dsimp
    intro h
    injection h with hPair
    injection hPair with hFwdEq hBackEq
    subst hFwdEq
    subst hBackEq
    refine ⟨hFwd, ?_⟩
    intro vFinal finals hBack
    change
      (if !handleFreeVal alg vFinal then none
       else
         match mutRet.2 vFinal with
         | some finals =>
           if finals.all (handleFreeVal alg) then some finals else none
         | none => none) = some finals at hBack
    cases hIn : handleFreeVal alg vFinal with
    | false =>
      rw [hIn] at hBack
      nomatch hBack
    | true =>
      rw [hIn] at hBack
      cases hRaw : mutRet.2 vFinal with
      | none =>
        rw [hRaw] at hBack
        nomatch hBack
      | some rawFinals =>
        rw [hRaw] at hBack
        change
          (if rawFinals.all (handleFreeVal alg) then some rawFinals
           else none) = some finals at hBack
        cases hOut : rawFinals.all (handleFreeVal alg) with
        | false =>
          rw [hOut] at hBack
          nomatch hBack
        | true =>
          rw [hOut] at hBack
          injection hBack with hFinEq
          subst hFinEq
          exact ⟨rfl, hOut⟩

/-- Every successful `evalFnReturningMut` summary has a handle-free forward
value, rejects caller inputs containing borrow handles, and produces only
handle-free final parameter values. -/
theorem evalFnReturningMut_handleFree {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retReg : LocalId) (fwd : Val) (backFn : Val → Option (List Val))
    (h : evalFnReturningMut alg params plan retReg = .ok (fwd, backFn)) :
    handleFreeVal alg fwd = true ∧
    ∀ vFinal finals,
      backFn vFinal = some finals →
      handleFreeVal alg vFinal = true ∧
      finals.all (handleFreeVal alg) = true := by
  unfold evalFnReturningMut at h
  cases hInit : initFnState alg params with
  | fail => rw [hInit] at h; nomatch h
  | ok st0 =>
    rw [hInit] at h
    dsimp only at h
    revert h
    generalize
      (match evalPlan alg plan st0 with
       | .fail => none
       | .ok (.returned _ _ mutOpt) => mutOpt
       | .ok (.continuing stF) =>
         match readPlaceVal alg (.localSub retReg []) stF with
         | some retRef => synthesizeMutReturnFromVal alg retRef stF
         | none => none
       | .ok (.guardedContinuing _ stF _ wrapMut) =>
         wrapMut
           (match readPlaceVal alg (.localSub retReg []) stF with
            | some retRef => synthesizeMutReturnFromVal alg retRef stF
            | none => none)) = rawMut
    cases rawMut with
    | none => intro h; nomatch h
    | some mutRet =>
      dsimp
      cases hSan : sanitizeMutRetSummary alg mutRet with
      | none => intro h; nomatch h
      | some cleanRet =>
        dsimp
        intro h
        injection h with hEq
        subst hEq
        exact sanitizeMutRetSummary_handleFree alg mutRet fwd backFn hSan

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
      .ok ⟨.choice (.node (.atom 1) (.atom 0)) (.atom 111) (.atom 333),
           [.choice (.node (.atom 1) (.atom 0)) (.atom 5) (.atom 222)]⟩ ∧
    -- 5. Nested symbolic `.branch` joining `.guardedContinuing` with
    -- `.continuing`, and `.whileLoop` preserving `.guardedContinuing` across
    -- iterations:
    let symBranchCond : LensTestVal := .node (.atom 1) (.atom 0)
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
    let fallMutFinal : LensTestVal :=
      .choice symBranchCond (.atom 5) (.atom 5)
    evalFnValue lensTestValAlg
      [⟨.byVal, symBranchCond⟩, ⟨.mutRef 0 [], .atom 5⟩]
      nestedGuardedBranchPlan
      (.use (.localSub 2 [])) =
      .ok ⟨.choice symBranchCond
             (.choice symBranchCond (.atom 101) (.atom 404))
             (.atom 404),
           [.choice symBranchCond
              (.choice symBranchCond (.atom 5) fallMutFinal)
              fallMutFinal]⟩ ∧
    evalFnValue lensTestValAlg
      [ ⟨.byVal, symBranchCond⟩
      , ⟨.mutRef 0 [], .atom 5⟩
      , ⟨.byVal, .atom 1⟩ ]
      guardedWhileLoopPlan
      (.constVal (.atom 606)) =
      .ok ⟨.choice symBranchCond (.atom 505) (.atom 606),
           [.choice symBranchCond (.atom 5) (.atom 5)]⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl⟩

/-- Exhaustive Round-6/7 regression tests for:
1. `joinRegionGroups` projecting branch-specific `outVals` and `deps` via
   `alg.projectBranchVal` before invoking `g1.backFn` and `g2.backFn`,
2. `renameBackTargetLoan` and `renameRegionGroupLoan` remapping references
   inside `.lensCall` and `RegionGroupEntry` backward-closure outputs,
3. `evalFnReturningMut` supporting `.earlyReturn` on all paths (`.returned`) and
   mixed early-return / continuing paths (`.guardedContinuing`), with
   `mergeMutRet` projecting branch-specialized `vFinal` values via
   `alg.projectBranchVal` and `zipOrKeepSameRef` preserving identical encoded
   references in `joinLoanEntries` and `mergeMutRet`, while `evalFnValue`
   rejects `.earlyReturn` when an unended child loan remains active. -/
theorem plan_round6_regressions_exhaustive_tests :
    -- 1. `joinRegionGroups` projects branch-specialized `outVals` and `deps`:
    (let gTrue : RegionGroupEntry LensTestVal :=
       ⟨0, true, 1, [(.localReg 0, [])], [1], [],
        fun outs deps =>
          match outs, deps with
          | [⟨_, .atom 100⟩], [⟨_, .atom 10⟩] => some ([.atom 110], [.atom 1])
          | _, _ => none⟩
     let gFalse : RegionGroupEntry LensTestVal :=
       ⟨0, true, 1, [(.localReg 0, [])], [1], [],
        fun outs deps =>
          match outs, deps with
          | [⟨_, .atom 200⟩], [⟨_, .atom 20⟩] => some ([.atom 220], [.atom 2])
          | _, _ => none⟩
     let symCond : LensTestVal := .ref 99 []
     let zippedOut := lensTestValAlg.zipVal symCond (.atom 100) (.atom 200)
     let zippedDep := lensTestValAlg.zipVal symCond (.atom 10) (.atom 20)
     match joinRegionGroups lensTestValAlg symCond [gTrue] [gFalse] with
     | some [gJoined] =>
       gJoined.backFn [zippedOut] [zippedDep] =
         some
           ([lensTestValAlg.zipVal symCond (.atom 110) (.atom 220)],
            [lensTestValAlg.zipVal symCond (.atom 1) (.atom 2)])
     | _ => False) ∧
    -- 2. `renameBackTargetLoan` and `renameRegionGroupLoan` remap references
    -- returned by `backFn`:
    (let bt : BackTarget LensTestVal :=
       .lensCall [(.localReg 0, [])] (fun _ => some [.ref 2 [0]])
     let bt' := renameBackTargetLoan lensTestValAlg 2 1 bt
     match bt'.steps with
     | [.lensCall _ backFn'] => backFn' (.atom 0) = some [.ref 1 [0]]
     | _ => False) ∧
    (let rg : RegionGroupEntry LensTestVal :=
       ⟨0, true, 2, [(.localReg 0, [])], [2], [],
        fun _ _ => some ([.ref 2 [0]], [.ref 2 [1]])⟩
     let rg' := renameRegionGroupLoan lensTestValAlg 2 1 rg
     rg'.backFn [] [] = some ([.ref 1 [0]], [.ref 1 [1]])) ∧
    -- 3. `evalFnReturningMut` with `.earlyReturn` (both direct `.returned` and
    -- mixed `.guardedContinuing`), plus `evalFnValue` rejecting unended child
    -- loans at `.earlyReturn`, plus `joinLoanEntries` preserving identical
    -- reference values inside loan cells via `zipOrKeepSameRef`:
    (let symCond : LensTestVal := .node (.atom 1) (.atom 0)
     let earlyMutPlan : FlowPlan LensTestVal :=
       .seq
         (.branch (.use (.localSub 0 []))
           (.seq
             (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))
             (.seq
               (.act (.assign (.derefSub 3 []) (.constVal (.atom 70))))
               (.earlyReturn [] [] (.use (.localSub 3 [])))))
           .skip)
         (.seq
           (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
           (.act (.assign (.derefSub 3 []) (.constVal (.atom 80)))))
     let eRef : LoanEntry LensTestVal :=
       ⟨0, .activeMut, ⟨.ref 1 [0], .unborrowed⟩, .rootParam 0⟩
     (match joinLoanEntries lensTestValAlg symCond [eRef] [eRef] with
      | some [eJoined] => eJoined.cell.val = .ref 1 [0]
      | _ => False) ∧
     (match evalFnReturningMut lensTestValAlg
         [⟨.byVal, .atom 1⟩, ⟨.mutRef 0 [], .atom 5⟩, ⟨.mutRef 1 [], .atom 6⟩]
         earlyMutPlan 3 with
      | .ok (fwdT, backT) =>
        fwdT = .atom 70 ∧ backT (.atom 99) = some [.atom 99, .atom 6]
      | .fail => False) ∧
     (match evalFnReturningMut lensTestValAlg
         [⟨.byVal, symCond⟩,
          ⟨.mutRef 0 [], .atom 5⟩,
          ⟨.mutRef 1 [], .atom 6⟩]
         earlyMutPlan 3 with
      | .ok (fwdSym, backSym) =>
        fwdSym = .choice symCond (.atom 70) (.atom 80) ∧
        backSym (.choice symCond (.atom 91) (.atom 92)) =
          some [.choice symCond (.atom 91) (.atom 5),
                .choice symCond (.atom 6) (.atom 92)]
      | .fail => False) ∧
     evalFnValue lensTestValAlg
       [⟨.byVal, .atom 1⟩, ⟨.mutRef 0 [], .atom 5⟩, ⟨.mutRef 1 [], .atom 6⟩]
       earlyMutPlan (.use (.localSub 3 [])) = .fail) :=
  ⟨rfl, rfl, rfl, ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩⟩

end Anneal.PureLift
