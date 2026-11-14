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
import Trusted.MirAst
import Trusted.MirSemantics
import Anneal.PureLift.Lens
import Anneal.PureLift.PermTree
import Anneal.PureLift.LoanGraph
import Anneal.PureLift.SpatialPin
import Anneal.PureLift.Plan
import Anneal.PureLift.BlockCfg
import Anneal.PureLift.Adapter

namespace Anneal.PureLift

open Trusted

/-!
# Bridge Between `PureLift` and `Trusted` MIR Semantics (`MirBridge.lean`)

Connects the language- and MIR-agnostic `Anneal.PureLift` transformation to the
trusted `Runtime(PostCleanup)` MIR syntax (`Trusted/MirAst.lean`) and
small-step operational semantics (`Trusted/MirSemantics.lean`):

1. **Value Algebra and Lawful Field Lenses (`mirValAlg`):** instantiates
   `ValAlgebra Trusted.MirVal`, proves the three bidirectional lens laws
   (`get_put`, `put_get`, `put_put`) for `Trusted.getMirField` and
   `Trusted.setMirField` over arbitrary `Trusted.MirVal` struct and tuple
   spines (`mirFieldLens_lawful`), and derives lawful nested sub-path lenses
   (`mirSubPathLens_lawful`).
2. **Small-Step Operational Adapter (`mirOperationalAdapter`):** connects
   `Trusted.stepMir` and `Trusted.runMirSteps` to `OperationalAdapter` and the
   adequacy theorem `pure_lift_sound` (`mir_pure_lift_sound`).
3. **End-to-End Verified MIR Workloads (`M-1` through `M-5`):** verifies
   concrete `Trusted.MirBody` programs—mutable reference mutation
   (`add_assign`), disjoint struct field swapping (`swap_fields`), multi-block
   conditional diamond reborrowing across `SwitchInt` basic blocks
   (`select_add`), multi-block loop accumulation (`loop_accumulate`), and
   storage-generation dangling-reference rejection—through `PureLift`.
-/

/-! ## Unfolding lemmas for `Trusted` `Nat.recCompiled` helpers -/

/-- Base-case unfolding of `Trusted.getSpineAt` on `.fieldCons` at index `0`. -/
theorem getSpineAt_zero_fieldCons (h t : MirVal) :
    getSpineAt 0 (.fieldCons h t) = some h := rfl

/-- Step-case unfolding of `Trusted.getSpineAt` on `.fieldCons` at `idx + 1`. -/
theorem getSpineAt_succ_fieldCons (idx : Nat) (h t : MirVal) :
    getSpineAt (idx + 1) (.fieldCons h t) = getSpineAt idx t := rfl

/-- Base-case unfolding of `Trusted.setSpineAt` on `.fieldCons` at index `0`. -/
theorem setSpineAt_zero_fieldCons (newVal h t : MirVal) :
    setSpineAt 0 newVal (.fieldCons h t) = some (.fieldCons newVal t) := rfl

/-- Step-case unfolding of `Trusted.setSpineAt` on `.fieldCons` at `idx + 1`. -/
theorem setSpineAt_succ_fieldCons (idx : Nat) (newVal h t : MirVal) :
    setSpineAt (idx + 1) newVal (.fieldCons h t) =
      match setSpineAt idx newVal t with
      | some t' => some (.fieldCons h t')
      | none => none := rfl

/-- Base-case unfolding of `Trusted.runMirSteps` at `0` fuel. -/
theorem runMirSteps_zero (body : MirBody) (st : MirState) :
    runMirSteps body 0 st = none := rfl

/-- Step-case unfolding of `Trusted.runMirSteps` at `fuel + 1`. -/
theorem runMirSteps_succ (body : MirBody) (fuel : Nat) (st : MirState) :
    runMirSteps body (fuel + 1) st =
      match stepMir body st with
      | .stepped next => runMirSteps body fuel next
      | .returned ret => some ret
      | .fault => none := rfl

/-! ## Value Algebra and Spine Lens Laws for `Trusted.MirVal` -/

/-- Conditional branch value selector on `Trusted.MirVal`. -/
def mirZipVal (cond vt vf : MirVal) : MirVal :=
  match cond with
  | .bool b => if b then vt else vf
  | .int n => if n != 0 then vt else vf
  | _ => vf

noncomputable def remapMirVal (oldLid newLid : LoanId) (v : MirVal) : MirVal :=
  @MirVal.rec (fun _ => MirVal)
    .uninit
    (fun n => .int n)
    (fun b => .bool b)
    .unit
    (fun id _ ihInner => .adt id ihInner)
    (fun _ _ ihH ihT => .fieldCons ihH ihT)
    (fun isMut refGen loc path depth =>
      if loc.index == oldLid then
        .ref isMut refGen ⟨newLid⟩ path depth
      else
        .ref isMut refGen loc path depth)
    v

/-- Instantiation of `PureLift.ValAlgebra` for `Trusted.MirVal`. -/
noncomputable def mirValAlg : ValAlgebra MirVal where
  defaultVal := .unit
  asBool v :=
    match v with
    | .bool b => some b
    | .int n => some (n != 0)
    | _ => none
  zipVal := mirZipVal
  getField idx v := getMirField idx v
  setField idx v child := setMirField idx child v
  encodeRef lid path := .ref true 0 ⟨lid⟩ path 0
  encodeSharedRef lid path := .ref false 0 ⟨lid⟩ path 0
  decodeRef v :=
    match v with
    | .ref _ _ ⟨lid⟩ path _ => some (lid, path)
    | _ => none
  remapRefInVal := remapMirVal

/-- `getSpineAt` followed by `setSpineAt` with the retrieved element restores
the original spine. -/
theorem getSpineAt_setSpineAt (idx : Nat) :
    ∀ (spine v : MirVal),
      getSpineAt idx spine = some v →
      setSpineAt idx v spine = some spine := by
  induction idx with
  | zero =>
    intro spine v hGet
    cases spine with
    | fieldCons h t =>
      rw [getSpineAt_zero_fieldCons] at hGet
      injection hGet with hEq
      subst hEq
      rfl
    | uninit => nomatch hGet
    | int _ => nomatch hGet
    | bool _ => nomatch hGet
    | unit => nomatch hGet
    | adt _ _ => nomatch hGet
    | ref _ _ _ _ _ => nomatch hGet
  | succ i ih =>
    intro spine v hGet
    cases spine with
    | fieldCons h t =>
      rw [getSpineAt_succ_fieldCons] at hGet
      rw [setSpineAt_succ_fieldCons, ih t v hGet]
    | uninit => nomatch hGet
    | int _ => nomatch hGet
    | bool _ => nomatch hGet
    | unit => nomatch hGet
    | adt _ _ => nomatch hGet
    | ref _ _ _ _ _ => nomatch hGet

/-- `setSpineAt` followed by `getSpineAt` at the same index returns the written
element. -/
theorem setSpineAt_getSpineAt (idx : Nat) :
    ∀ (spine v spine' : MirVal),
      setSpineAt idx v spine = some spine' →
      getSpineAt idx spine' = some v := by
  induction idx with
  | zero =>
    intro spine v spine' hSet
    cases spine with
    | fieldCons h t =>
      rw [setSpineAt_zero_fieldCons] at hSet
      injection hSet with hEq
      subst hEq
      rfl
    | uninit => nomatch hSet
    | int _ => nomatch hSet
    | bool _ => nomatch hSet
    | unit => nomatch hSet
    | adt _ _ => nomatch hSet
    | ref _ _ _ _ _ => nomatch hSet
  | succ i ih =>
    intro spine v spine' hSet
    cases spine with
    | fieldCons h t =>
      rw [setSpineAt_succ_fieldCons] at hSet
      revert hSet
      cases hRec : setSpineAt i v t with
      | none =>
        intro hFalse
        nomatch hFalse
      | some t' =>
        dsimp
        intro hSet
        injection hSet with hEq
        subst hEq
        rw [getSpineAt_succ_fieldCons]
        exact ih t v t' hRec
    | uninit => nomatch hSet
    | int _ => nomatch hSet
    | bool _ => nomatch hSet
    | unit => nomatch hSet
    | adt _ _ => nomatch hSet
    | ref _ _ _ _ _ => nomatch hSet

/-- Two consecutive `setSpineAt` updates at the same index overwrite the first
update. -/
theorem setSpineAt_setSpineAt (idx : Nat) :
    ∀ (spine v1 v2 spine1 : MirVal),
      setSpineAt idx v1 spine = some spine1 →
      setSpineAt idx v2 spine1 = setSpineAt idx v2 spine := by
  induction idx with
  | zero =>
    intro spine v1 v2 spine1 hSet
    cases spine with
    | fieldCons h t =>
      rw [setSpineAt_zero_fieldCons] at hSet
      injection hSet with hEq
      subst hEq
      rfl
    | uninit => nomatch hSet
    | int _ => nomatch hSet
    | bool _ => nomatch hSet
    | unit => nomatch hSet
    | adt _ _ => nomatch hSet
    | ref _ _ _ _ _ => nomatch hSet
  | succ i ih =>
    intro spine v1 v2 spine1 hSet
    cases spine with
    | fieldCons h t =>
      rw [setSpineAt_succ_fieldCons] at hSet
      revert hSet
      cases hRec : setSpineAt i v1 t with
      | none =>
        intro hFalse
        nomatch hFalse
      | some t' =>
        dsimp
        intro hSet
        injection hSet with hEq
        subst hEq
        rw [setSpineAt_succ_fieldCons, setSpineAt_succ_fieldCons,
            ih t v1 v2 t' hRec]
    | uninit => nomatch hSet
    | int _ => nomatch hSet
    | bool _ => nomatch hSet
    | unit => nomatch hSet
    | adt _ _ => nomatch hSet
    | ref _ _ _ _ _ => nomatch hSet

/-- If `setSpineAt idx v (.fieldCons h t) = some spine'`, then `spine'` is a
`.fieldCons` node so `getMirField` and `setMirField` delegate to `getSpineAt`
and `setSpineAt`. -/
theorem setSpineAt_is_fieldCons (idx : Nat) (h t v spine' : MirVal)
    (hSet : setSpineAt idx v (.fieldCons h t) = some spine') :
    getMirField idx spine' = getSpineAt idx spine' ∧
    (∀ v2, setMirField idx v2 spine' = setSpineAt idx v2 spine') := by
  cases idx with
  | zero =>
    rw [setSpineAt_zero_fieldCons] at hSet
    injection hSet with hEq
    subst hEq
    exact ⟨rfl, fun _ => rfl⟩
  | succ i =>
    rw [setSpineAt_succ_fieldCons] at hSet
    revert hSet
    cases setSpineAt i v t with
    | none =>
      intro hFalse
      nomatch hFalse
    | some t' =>
      dsimp
      intro hSet
      injection hSet with hEq
      subst hEq
      exact ⟨rfl, fun _ => rfl⟩

/-- `fieldLens mirValAlg f` satisfies the three bidirectional lens laws
(`get_put`, `put_get`, and `put_put`) for every field index `f : FieldIdx`. -/
theorem mirFieldLens_lawful (f : FieldIdx) :
    LawfulLens MirVal MirVal (fieldLens mirValAlg f) where
  get_put := by
    intro s a hGet
    cases s with
    | adt id inner =>
      dsimp [fieldLens, mirValAlg, getMirField] at hGet
      dsimp [fieldLens, mirValAlg, setMirField]
      rw [getSpineAt_setSpineAt f inner a hGet]
    | fieldCons h t =>
      dsimp [fieldLens, mirValAlg, getMirField] at hGet
      dsimp [fieldLens, mirValAlg, setMirField]
      exact getSpineAt_setSpineAt f (.fieldCons h t) a hGet
    | uninit => nomatch hGet
    | int _ => nomatch hGet
    | bool _ => nomatch hGet
    | unit => nomatch hGet
    | ref _ _ _ _ _ => nomatch hGet
  put_get := by
    intro s a s' hPut
    cases s with
    | adt id inner =>
      dsimp [fieldLens, mirValAlg, setMirField] at hPut
      revert hPut
      cases hRec : setSpineAt f a inner with
      | none =>
        intro hFalse
        nomatch hFalse
      | some inner' =>
        dsimp
        intro hPut
        injection hPut with hEq
        subst hEq
        dsimp [fieldLens, mirValAlg, getMirField]
        exact setSpineAt_getSpineAt f inner a inner' hRec
    | fieldCons h t =>
      dsimp [fieldLens, mirValAlg, setMirField] at hPut
      have hFC := setSpineAt_is_fieldCons f h t a s' hPut
      dsimp [fieldLens, mirValAlg]
      rw [hFC.1]
      exact setSpineAt_getSpineAt f (.fieldCons h t) a s' hPut
    | uninit => nomatch hPut
    | int _ => nomatch hPut
    | bool _ => nomatch hPut
    | unit => nomatch hPut
    | ref _ _ _ _ _ => nomatch hPut
  put_put := by
    intro s a1 a2 s1 hPut1
    cases s with
    | adt id inner =>
      dsimp [fieldLens, mirValAlg, setMirField] at hPut1
      revert hPut1
      cases hRec : setSpineAt f a1 inner with
      | none =>
        intro hFalse
        nomatch hFalse
      | some inner' =>
        dsimp
        intro hPut1
        injection hPut1 with hEq
        subst hEq
        dsimp [fieldLens, mirValAlg, setMirField]
        rw [setSpineAt_setSpineAt f inner a1 a2 inner' hRec]
    | fieldCons h t =>
      dsimp [fieldLens, mirValAlg, setMirField] at hPut1
      have hFC := setSpineAt_is_fieldCons f h t a1 s1 hPut1
      dsimp [fieldLens, mirValAlg]
      rw [hFC.2 a2]
      dsimp [setMirField]
      exact setSpineAt_setSpineAt f (.fieldCons h t) a1 a2 s1 hPut1
    | uninit => nomatch hPut1
    | int _ => nomatch hPut1
    | bool _ => nomatch hPut1
    | unit => nomatch hPut1
    | ref _ _ _ _ _ => nomatch hPut1

/-- Every nested sub-place path lens `subPathLens mirValAlg path` is lawful. -/
theorem mirSubPathLens_lawful (path : SubPath) :
    LawfulLens MirVal MirVal (subPathLens mirValAlg path) :=
  subPathLens_lawful mirValAlg mirFieldLens_lawful path

/-! ## Operational Adapter for `Trusted.MirBody` and `Trusted.MirState` -/

/-- Structural check that `v` contains no `.uninit` leaves and every embedded
`.ref` points to a live slot whose generation matches `localGens` (matching
`Trusted.MirVal.isValidInState` at arbitrary nesting depth without a fuel
cutoff). -/
noncomputable def mirValValidInState (localGens : List Nat) (v : MirVal) :
    Bool :=
  v.isValidInState localGens

/-- Extract the current values of `callerSlots` in `mirSt.locals` if every slot
is allocated, initialized, and valid in `mirSt.localGens` (no `.uninit` leaves
and no dangling or retired references). -/
noncomputable def extractCallerSlotVals (callerSlots : List Nat)
    (mirSt : MirState) : Option (List MirVal) :=
  callerSlots.foldr
    (fun slotIdx acc =>
      match lookupAt mirSt.locals slotIdx, acc with
      | some (some v), some vs =>
        if mirValValidInState mirSt.localGens v then
          some (v :: vs)
        else
          none
      | _, _ => none)
    (some [])

/-- Extract a `FuncOut MirVal` from a `Trusted.MirReturn` given the indices of
the caller-owned mutable-reference referent slots in `ret.state.locals`,
requiring every extracted caller-slot value to be valid in
`ret.state.localGens`. -/
noncomputable def extractMirFuncOut (callerSlots : List Nat) (ret : MirReturn) :
    Option (FuncOut MirVal) :=
  match extractCallerSlotVals callerSlots ret.state with
  | some wb => some ⟨ret.value, wb⟩
  | none => none

/-- `MirRunsTo callerSlots body st fuel out` holds when running `body` for
`fuel` small steps from `st` returns `ret` and `extractMirFuncOut callerSlots
ret` yields `some out`. -/
noncomputable def MirRunsTo (callerSlots : List Nat) (body : MirBody)
    (st : MirState) (fuel : Nat) (out : FuncOut MirVal) : Prop :=
  match runMirSteps body fuel st with
  | some ret => extractMirFuncOut callerSlots ret = some out
  | none => False

/-- Composable single-step reduction lemma for `MirRunsTo`: if `stepMir body st
= .stepped st'` and `st'` reaches `out` in `fuel` steps, then `st` reaches `out`
in `fuel + 1` steps. -/
theorem mir_stepped_runsTo (callerSlots : List Nat) (body : MirBody)
    (st st' : MirState) (fuel : Nat) (out : FuncOut MirVal)
    (hStep : stepMir body st = .stepped st')
    (hRest : MirRunsTo callerSlots body st' fuel out) :
    MirRunsTo callerSlots body st (fuel + 1) out := by
  dsimp [MirRunsTo]
  rw [runMirSteps_succ, hStep]
  exact hRest

/-- Composable terminal-step lemma for `MirRunsTo`: if `stepMir body st =
.returned ret` and `extractMirFuncOut callerSlots ret = some out`, then `st`
reaches `out` in `1` step. -/
theorem mir_returned_runsTo (callerSlots : List Nat) (body : MirBody)
    (st : MirState) (ret : MirReturn) (out : FuncOut MirVal)
    (hStep : stepMir body st = .returned ret)
    (hExt : extractMirFuncOut callerSlots ret = some out) :
    MirRunsTo callerSlots body st 1 out := by
  dsimp [MirRunsTo]
  rw [runMirSteps_succ, hStep]
  exact hExt

/-- `MirExecutesTo callerSlots body m0 fuel mFinal` holds when the style-1
machine state `m0` steps to `mFinal` in `fuel` small steps of
`Trusted.stepMir`. -/
inductive MirExecutesTo (callerSlots : List Nat) (body : MirBody) :
    M1MachState MirState MirVal → Nat → M1MachState MirState MirVal → Prop where
  | refl (m : M1MachState MirState MirVal) :
      MirExecutesTo callerSlots body m 0 m
  | trans {m1 m2 m3 : M1MachState MirState MirVal} {k1 k2 : Nat} :
      MirExecutesTo callerSlots body m1 k1 m2 →
      MirExecutesTo callerSlots body m2 k2 m3 →
      MirExecutesTo callerSlots body m1 (k1 + k2) m3
  | step_runs {st0 : MirState} {fuel : Nat} {out : FuncOut MirVal} :
      MirRunsTo callerSlots body st0 fuel out →
      MirExecutesTo callerSlots body (.running st0) fuel (.returned out)

/-- State relation connecting a `PureLift` `SymState MirVal` to a
`Trusted.MirState`: every caller-owned referent slot in `callerSlots` holds a
valid, initialized `MirVal` in `mirSt`, and at function entry (`block == 0` and
`stmtIdx == 0`) those referent values equal the active root `&mut` loan values
in `symSt`. -/
noncomputable def MirStateRel (callerSlots : List Nat) (symSt : SymState MirVal)
    (mirSt : MirState) : Prop :=
  match extractCallerSlotVals callerSlots mirSt with
  | some slotVals =>
    if mirSt.block == 0 && mirSt.stmtIdx == 0 then
      slotVals = collectRootMutVals symSt.loans
    else
      True
  | none => False

/-- `OperationalAdapter` connecting `Trusted.MirBody` and `Trusted.MirState`
to `PureLift`. -/
noncomputable def mirOperationalAdapter (callerSlots : List Nat)
    (body : MirBody) :
    OperationalAdapter (M1MachState MirState MirVal) MirVal where
  ExecutesTo := MirExecutesTo callerSlots body
  StateRel symSt m :=
    match m with
    | .running mirSt => MirStateRel callerSlots symSt mirSt
    | _ => False
  FinalLoansRel out m := m = .returned out
  exec_zero := MirExecutesTo.refl
  exec_trans := MirExecutesTo.trans

/-- Master soundness bridge specialized to `Trusted.MirBody` and
`Trusted.MirState`: any function postcondition `post` proved on the pure
functional lifting `evalFnValue mirValAlg params plan retExpr` transfers
directly to a terminating `Trusted.runMirSteps` execution of `body` from an
entry state `st0` related by `MirStateRel`. -/
theorem mir_pure_lift_sound
    (callerSlots : List Nat)
    (body : MirBody)
    (params : List (ParamInput MirVal))
    (plan : FlowPlan MirVal)
    (retExpr : RvalOp MirVal)
    (post : FuncOut MirVal → Prop)
    (st0 : MirState)
    (hInit : Exists fun sym0 =>
      initFnState mirValAlg params = .ok sym0 ∧
      MirStateRel callerSlots sym0 st0)
    (hSpec : HoldsFnSpec (evalFnValue mirValAlg params plan retExpr) post)
    (hSim : ∀ out, evalFnValue mirValAlg params plan retExpr = .ok out →
      Exists fun k => MirRunsTo callerSlots body st0 k out) :
    Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter callerSlots body).ExecutesTo
        (.running st0) k mFinal ∧
      (mirOperationalAdapter callerSlots body).FinalLoansRel out mFinal ∧
      post out := by
  exact pure_lift_sound
    (mirOperationalAdapter callerSlots body)
    mirValAlg params plan retExpr post (.running st0) hInit hSpec
    (by
      intro _ out _ _ hEval
      cases hSim out hEval with
      | intro k hk =>
        exact ⟨k, ⟨.returned out, MirExecutesTo.step_runs hk, rfl⟩⟩)

/-! ## End-to-End Verified `Trusted.MirBody` Workloads -/

/-- Modulus $2^{64}$ of 64-bit `MirTy.usize` arithmetic. -/
def mirUsizeModulus : Nat :=
  natPow2 64

/-- 64-bit `usize` wrapping addition modulo $2^{64}$. -/
def mirAddUsize (a b : Nat) : Nat :=
  Nat.mod (a + b) mirUsizeModulus

theorem mirUsizeModulus_pos : 0 < mirUsizeModulus := by
  decide

theorem decide_mirAddUsize_lt (a b : Nat) :
    decide (mirAddUsize a b < natPow2 64) = true :=
  decide_eq_true (Nat.mod_lt (a + b) mirUsizeModulus_pos)

/-- Pure 64-bit `usize` wrapping addition helper on `Trusted.MirVal`, matching
`Trusted.evalBinOp .add` on `MirTy.usize` operands. -/
def mirAddVal (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .int a, .int b => some (.int (mirAddUsize a b))
  | _, _ => none

/-- Pure 64-bit `usize` wrapping subtraction helper on `Trusted.MirVal`,
matching `Trusted.evalBinOp .sub` on `MirTy.usize` operands. -/
def mirSubUsizeVal (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .int a, .int b =>
    some (.int (Nat.mod (a + mirUsizeModulus - Nat.mod b mirUsizeModulus)
      mirUsizeModulus))
  | _, _ => none

/-- Pure checked integer subtraction helper on untyped `Trusted.MirVal`,
matching `Trusted.evalBinOp .sub` when `intWidthOpt = none` by rejecting
underflow (`b > a`). -/
def mirSubVal (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .int a, .int b =>
    if decide (b ≤ a) then some (.int (a - b)) else none
  | _, _ => none

/-- Pure integer `>` comparison helper on `Trusted.MirVal`. -/
def mirGtVal (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .int a, .int b => some (.bool (Nat.blt b a))
  | _, _ => none

/-! ### Workload M-1: Mutable Reference Borrow and Write (`add_assign`)

Rust equivalent:
```rust
fn add_assign(p: &mut usize, delta: usize) -> usize {
    let r = &mut *p;
    *r = *r + delta;
    *p
}
```
MIR locals:
- `_0`: return `usize`
- `_1`: `p: &mut usize` (points to caller slot `4`)
- `_2`: `delta: usize`
- `_3`: `r: &mut usize`
- `_4`: caller-owned referent slot for `*p`
-/

/-- `Trusted.MirBody` for `add_assign(p: &mut usize, delta: usize) -> usize`. -/
def mirAddAssignBody : MirBody :=
  { argCount := 2
    localCount := 4
    localTys := [.usize, .refMut .usize, .usize, .refMut .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨3⟩
            , .assign ⟨⟨3⟩, []⟩ (.refMut ⟨⟨1⟩, [.deref]⟩)
            , .assign ⟨⟨3⟩, [.deref]⟩
                (.binaryOp .add (.copy ⟨⟨3⟩, [.deref]⟩) (.copy ⟨⟨2⟩, []⟩))
            , .storageDead ⟨3⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirAddAssignBody`. -/
def mirAddAssignInitState (x delta : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨4⟩ [])
      , some (.int delta)
      , none
      , some (.int x)
      ]
    localGens := [0, 0, 0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- `PureLift` `FlowPlan` corresponding to `mirAddAssignBody`:
local `0` is `p: &mut usize`, local `1` is `delta: usize`, and local `2` is the
reborrow `r = &mut *p` (loan `1`). -/
def mirAddAssignPlan : FlowPlan MirVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [])))
    (.seq
      (.act (.assign (.derefSub 2 [])
        (.binary mirAddVal (.derefSub 2 []) (.localSub 1 []))))
      (.act (.endLoan 1)))

def mirAddAssignState4 (x delta : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨4⟩ [])
      , some (.int delta)
      , none
      , some (.int (mirAddUsize x delta))
      ]
    localGens := [0, 0, 0, 2, 0]
    block := 0
    stmtIdx := 4
  }

def mirAddAssignState5 (x delta : Nat) : MirState :=
  { locals :=
      [ some (.int (mirAddUsize x delta))
      , some (.ref true 0 ⟨4⟩ [])
      , some (.int delta)
      , none
      , some (.int (mirAddUsize x delta))
      ]
    localGens := [0, 0, 0, 2, 0]
    block := 0
    stmtIdx := 5
  }

theorem mirAddAssign_runsTo (x delta : Nat) :
    MirRunsTo [4] mirAddAssignBody (mirAddAssignInitState x delta) 7
      ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ := by
  change MirRunsTo [4] mirAddAssignBody (mirAddAssignState4 x delta) (2 + 1)
    ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩
  refine mir_stepped_runsTo [4] mirAddAssignBody
    (mirAddAssignState4 x delta) (mirAddAssignState5 x delta) 2
    ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ ?_ rfl
  change
    (match
      if decide (mirAddUsize x delta < natPow2 64) = true then
        some (mirAddAssignState5 x delta).locals
      else none with
     | some locals' =>
       StepOutcome.stepped ⟨locals', [0, 0, 0, 2, 0], 0, 5⟩
     | none => StepOutcome.fault) =
    StepOutcome.stepped (mirAddAssignState5 x delta)
  rw [decide_mirAddUsize_lt x delta]
  rfl

/-- End-to-end verification of `mirAddAssignBody`: both `PureLift`
(`evalFnValue` + `mir_pure_lift_sound`) and `Trusted.runMirSteps` return
`.int (mirAddUsize x delta)` and write back `.int (mirAddUsize x delta)` to
caller slot `4` for all `x, delta : Nat`. -/
theorem mir_add_assign_verified (x delta : Nat) :
    (evalFnValue mirValAlg
        [⟨.mutRef 0 [], .int x⟩, ⟨.byVal, .int delta⟩]
        mirAddAssignPlan
        (.use (.derefSub 0 [])) =
      .ok ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩) ∧
    MirRunsTo [4] mirAddAssignBody (mirAddAssignInitState x delta) 7
      ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ ∧
    (Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter [4] mirAddAssignBody).ExecutesTo
        (.running (mirAddAssignInitState x delta)) k mFinal ∧
      (mirOperationalAdapter [4] mirAddAssignBody).FinalLoansRel out mFinal ∧
      out = ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩) := by
  refine ⟨rfl, mirAddAssign_runsTo x delta, ?_⟩
  exact mir_pure_lift_sound [4] mirAddAssignBody
    [⟨.mutRef 0 [], .int x⟩, ⟨.byVal, .int delta⟩]
    mirAddAssignPlan
    (.use (.derefSub 0 []))
    (fun out =>
      out = ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩)
    (mirAddAssignInitState x delta)
    ⟨_, ⟨rfl, rfl⟩⟩
    rfl
    (by
      intro out hEval
      change
        EvalOutcome.ok
          ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ =
        EvalOutcome.ok out at hEval
      injection hEval with hOut
      subst hOut
      exact ⟨7, mirAddAssign_runsTo x delta⟩)

/-! ### Workload M-2: Disjoint Struct Field Borrows (`swap_fields`)

Rust equivalent:
```rust
struct Pair(usize, usize);
fn swap_fields(s: &mut Pair) -> usize {
    let p0 = &mut (*s).0;
    let p1 = &mut (*s).1;
    let tmp = *p0;
    *p0 = *p1;
    *p1 = tmp;
    (*s).0
}
```
-/

/-- Construct a 2-field `Pair(a, b)` struct `MirVal` (ADT `0`). -/
def mkMirPair (a b : Nat) : MirVal :=
  .adt 0 (.fieldCons (.int a) (.fieldCons (.int b) .unit))

/-- `Trusted.MirBody` for `swap_fields(s: &mut Pair) -> usize`. -/
def mirSwapFieldsBody : MirBody :=
  { argCount := 1
    localCount := 5
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨2⟩
            , .storageLive ⟨3⟩
            , .storageLive ⟨4⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, [.deref, .field 0]⟩)
            , .assign ⟨⟨3⟩, []⟩ (.refMut ⟨⟨1⟩, [.deref, .field 1]⟩)
            , .assign ⟨⟨4⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.copy ⟨⟨3⟩, [.deref]⟩))
            , .assign ⟨⟨3⟩, [.deref]⟩ (.use (.copy ⟨⟨4⟩, []⟩))
            , .storageDead ⟨4⟩
            , .storageDead ⟨3⟩
            , .storageDead ⟨2⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref, .field 0]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirSwapFieldsBody` with `Pair(a, b)` in
caller slot `5`. -/
def mirSwapFieldsInitState (a b : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨5⟩ [])
      , none
      , none
      , none
      , some (mkMirPair a b)
      ]
    localGens := [0, 0, 0, 0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- `PureLift` `FlowPlan` for `swap_fields`: local `0` is `s: &mut Pair`,
local `1` is `p0 = &mut (*s).0` (loan `1`), local `2` is `p1 = &mut (*s).1`
(loan `2`), and local `3` is `tmp = *p0`. -/
def mirSwapFieldsPlan : FlowPlan MirVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.assign (.localSub 3 []) (.use (.derefSub 1 []))))
        (.seq
          (.act (.assign (.derefSub 1 []) (.use (.derefSub 2 []))))
          (.seq
            (.act (.assign (.derefSub 2 []) (.use (.localSub 3 []))))
            (.seq
              (.act (.endLoan 2))
              (.act (.endLoan 1)))))))

/-- End-to-end verification of `mirSwapFieldsBody`: both `PureLift` and
`Trusted.runMirSteps` swap `Pair(a, b)` into `Pair(b, a)` via simultaneous
disjoint sub-place borrows (`[0]` and `[1]`) and return `.int b` for all
`a, b : Nat`. -/
theorem mir_swap_fields_verified (a b : Nat) :
    (evalFnValue mirValAlg
        [⟨.mutRef 0 [], mkMirPair a b⟩]
        mirSwapFieldsPlan
        (.use (.derefSub 0 [0])) =
      .ok ⟨.int b, [mkMirPair b a]⟩) ∧
    MirRunsTo [5] mirSwapFieldsBody (mirSwapFieldsInitState a b) 14
      ⟨.int b, [mkMirPair b a]⟩ ∧
    (Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter [5] mirSwapFieldsBody).ExecutesTo
        (.running (mirSwapFieldsInitState a b)) k mFinal ∧
      (mirOperationalAdapter [5] mirSwapFieldsBody).FinalLoansRel out mFinal ∧
      out = ⟨.int b, [mkMirPair b a]⟩) := by
  refine ⟨rfl, rfl, ?_⟩
  exact mir_pure_lift_sound [5] mirSwapFieldsBody
    [⟨.mutRef 0 [], mkMirPair a b⟩]
    mirSwapFieldsPlan
    (.use (.derefSub 0 [0]))
    (fun out => out = ⟨.int b, [mkMirPair b a]⟩)
    (mirSwapFieldsInitState a b)
    ⟨_, ⟨rfl, rfl⟩⟩
    rfl
    (by
      intro out hEval
      change EvalOutcome.ok ⟨.int b, [mkMirPair b a]⟩ =
        EvalOutcome.ok out at hEval
      injection hEval with hOut
      subst hOut
      exact ⟨14, rfl⟩)

/-! ### Workload M-3: Multi-Block Conditional Diamond Reborrow (`select_add`)

Rust equivalent:
```rust
fn select_add(flag: bool, x: &mut usize, y: &mut usize, v: usize) -> usize {
    let r = if flag { &mut *x } else { &mut *y };
    *r = *r + v;
    *r
}
```
Multi-block MIR CFG:
- `bb0`: `SwitchInt(_1)` (`0 -> bb2`, `otherwise -> bb1`)
- `bb1`: `_5 = &mut (*_2); goto -> bb3`
- `bb2`: `_5 = &mut (*_3); goto -> bb3`
- `bb3`: `(*_5) = (*_5) + _4; _0 = (*_5); return`
Caller-owned referent slots: `6` (`*x`) and `7` (`*y`).
-/

/-- 4-block `Trusted.MirBody` for `select_add`. -/
def mirSelectAddBody : MirBody :=
  { argCount := 4
    localCount := 6
    localTys :=
      [.usize, .bool, .refMut .usize, .refMut .usize, .usize, .refMut .usize]
    blocks :=
      [ -- bb0: branch on `_1` (`flag`)
        { stmts := [.storageLive ⟨5⟩]
          terminator :=
            .switchInt (.copy ⟨⟨1⟩, []⟩)
              { branches := [⟨0, ⟨2⟩⟩], otherwise := ⟨1⟩ }
        }
      , -- bb1 (`flag = true`): `_5 = &mut (*_2); goto bb3`
        { stmts := [.assign ⟨⟨5⟩, []⟩ (.refMut ⟨⟨2⟩, [.deref]⟩)]
          terminator := .goto ⟨3⟩
        }
      , -- bb2 (`flag = false`): `_5 = &mut (*_3); goto bb3`
        { stmts := [.assign ⟨⟨5⟩, []⟩ (.refMut ⟨⟨3⟩, [.deref]⟩)]
          terminator := .goto ⟨3⟩
        }
      , -- bb3 (join): `(*_5) = (*_5) + _4; _0 = (*_5); StorageDead(_5); return`
        { stmts :=
            [ .assign ⟨⟨5⟩, [.deref]⟩
                (.binaryOp .add (.copy ⟨⟨5⟩, [.deref]⟩) (.copy ⟨⟨4⟩, []⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨5⟩, [.deref]⟩))
            , .storageDead ⟨5⟩
            ]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirSelectAddBody`. -/
def mirSelectAddInitState (flag : Bool) (x y v : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.bool flag)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , none
      , some (.int x)
      , some (.int y)
      ]
    localGens := [0, 0, 0, 0, 0, 0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- `PureLift` `FlowPlan` for `select_add`, using `.branchExplicitJoin` with
`[(2, 2)]` so both branches execute and join through `joinSymState` and
`BackTarget.choice` across the diamond merge at `bb3`. -/
def mirSelectAddPlan : FlowPlan MirVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.act (.borrow 4 .mutBorrow (.derefSub 1 [])))
      (.act (.borrow 4 .mutBorrow (.derefSub 2 [])))
      [(2, 2)])
    (.seq
      (.act (.assign (.derefSub 4 [])
        (.binary mirAddVal (.derefSub 4 []) (.localSub 3 []))))
      (.seq
        (.act (.assign (.localSub 5 []) (.use (.derefSub 4 []))))
        (.act (.endLoan 2))))

def mirSelectAddStateTrue5 (x y v : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.bool true)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some (.ref true 0 ⟨6⟩ [] 1)
      , some (.int (mirAddUsize x v))
      , some (.int y)
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 3
    stmtIdx := 1
  }

def mirSelectAddStateTrue6 (x y v : Nat) : MirState :=
  { locals :=
      [ some (.int (mirAddUsize x v))
      , some (.bool true)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some (.ref true 0 ⟨6⟩ [] 1)
      , some (.int (mirAddUsize x v))
      , some (.int y)
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 3
    stmtIdx := 2
  }

def mirSelectAddStateFalse5 (x y v : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.bool false)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some (.ref true 0 ⟨7⟩ [] 1)
      , some (.int x)
      , some (.int (mirAddUsize y v))
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 3
    stmtIdx := 1
  }

def mirSelectAddStateFalse6 (x y v : Nat) : MirState :=
  { locals :=
      [ some (.int (mirAddUsize y v))
      , some (.bool false)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some (.ref true 0 ⟨7⟩ [] 1)
      , some (.int x)
      , some (.int (mirAddUsize y v))
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 3
    stmtIdx := 2
  }

theorem mirSelectAdd_runsTo (flag : Bool) (x y v : Nat) :
    MirRunsTo [6, 7] mirSelectAddBody
      (mirSelectAddInitState flag x y v) 9
      ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
       [if flag then .int (mirAddUsize x v) else .int x,
        if flag then .int y else .int (mirAddUsize y v)]⟩ := by
  cases flag with
  | true =>
    change MirRunsTo [6, 7] mirSelectAddBody
      (mirSelectAddStateTrue5 x y v) (3 + 1)
      ⟨.int (mirAddUsize x v), [.int (mirAddUsize x v), .int y]⟩
    refine mir_stepped_runsTo [6, 7] mirSelectAddBody
      (mirSelectAddStateTrue5 x y v) (mirSelectAddStateTrue6 x y v) 3
      ⟨.int (mirAddUsize x v), [.int (mirAddUsize x v), .int y]⟩ ?_ rfl
    change
      (match
        if decide (mirAddUsize x v < natPow2 64) = true then
          some (mirSelectAddStateTrue6 x y v).locals
        else none with
       | some locals' =>
         StepOutcome.stepped ⟨locals', [0, 0, 0, 0, 0, 1, 0, 0], 3, 2⟩
       | none => StepOutcome.fault) =
      StepOutcome.stepped (mirSelectAddStateTrue6 x y v)
    rw [decide_mirAddUsize_lt x v]
    rfl
  | false =>
    change MirRunsTo [6, 7] mirSelectAddBody
      (mirSelectAddStateFalse5 x y v) (3 + 1)
      ⟨.int (mirAddUsize y v), [.int x, .int (mirAddUsize y v)]⟩
    refine mir_stepped_runsTo [6, 7] mirSelectAddBody
      (mirSelectAddStateFalse5 x y v) (mirSelectAddStateFalse6 x y v) 3
      ⟨.int (mirAddUsize y v), [.int x, .int (mirAddUsize y v)]⟩ ?_ rfl
    change
      (match
        if decide (mirAddUsize y v < natPow2 64) = true then
          some (mirSelectAddStateFalse6 x y v).locals
        else none with
       | some locals' =>
         StepOutcome.stepped ⟨locals', [0, 0, 0, 0, 0, 1, 0, 0], 3, 2⟩
       | none => StepOutcome.fault) =
      StepOutcome.stepped (mirSelectAddStateFalse6 x y v)
    rw [decide_mirAddUsize_lt y v]
    rfl

/-- End-to-end verification of the 4-block `mirSelectAddBody` across both
branches (`flag = true` and `flag = false`) and all `x, y, v : Nat`:
`PureLift`'s diamond borrow join and `.choice` backward cascade match the exact
`Trusted.runMirSteps` execution of the multi-block `SwitchInt` CFG. -/
theorem mir_select_add_verified (flag : Bool) (x y v : Nat) :
    (evalFnValue mirValAlg
        [⟨.byVal, .bool flag⟩,
         ⟨.mutRef 0 [], .int x⟩,
         ⟨.mutRef 1 [], .int y⟩,
         ⟨.byVal, .int v⟩]
        mirSelectAddPlan
        (.use (.localSub 5 [])) =
      .ok ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
           [if flag then .int (mirAddUsize x v) else .int x,
            if flag then .int y else .int (mirAddUsize y v)]⟩) ∧
    MirRunsTo [6, 7] mirSelectAddBody
      (mirSelectAddInitState flag x y v) 9
      ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
       [if flag then .int (mirAddUsize x v) else .int x,
        if flag then .int y else .int (mirAddUsize y v)]⟩ ∧
    (Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter [6, 7] mirSelectAddBody).ExecutesTo
        (.running (mirSelectAddInitState flag x y v)) k mFinal ∧
      (mirOperationalAdapter [6, 7] mirSelectAddBody).FinalLoansRel out mFinal ∧
      out = ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
             [if flag then .int (mirAddUsize x v) else .int x,
              if flag then .int y else .int (mirAddUsize y v)]⟩) := by
  have hPure :
      evalFnValue mirValAlg
        [⟨.byVal, .bool flag⟩,
         ⟨.mutRef 0 [], .int x⟩,
         ⟨.mutRef 1 [], .int y⟩,
         ⟨.byVal, .int v⟩]
        mirSelectAddPlan
        (.use (.localSub 5 [])) =
      .ok ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
           [if flag then .int (mirAddUsize x v) else .int x,
            if flag then .int y else .int (mirAddUsize y v)]⟩ := by
    cases flag <;> rfl
  have hMir := mirSelectAdd_runsTo flag x y v
  refine ⟨hPure, hMir, ?_⟩
  exact mir_pure_lift_sound [6, 7] mirSelectAddBody
    [⟨.byVal, .bool flag⟩,
     ⟨.mutRef 0 [], .int x⟩,
     ⟨.mutRef 1 [], .int y⟩,
     ⟨.byVal, .int v⟩]
    mirSelectAddPlan
    (.use (.localSub 5 []))
    (fun out =>
      out = ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
             [if flag then .int (mirAddUsize x v) else .int x,
              if flag then .int y else .int (mirAddUsize y v)]⟩)
    (mirSelectAddInitState flag x y v)
    ⟨_, ⟨rfl, rfl⟩⟩
    (by cases flag <;> rfl)
    (by
      intro out hEval
      rw [hPure] at hEval
      injection hEval with hOut
      subst hOut
      exact ⟨9, hMir⟩)

/-! ### Workload M-4: Multi-Block Loop with Mutable Reborrow (`loop_accumulate`)

Rust equivalent:
```rust
fn loop_accumulate(acc: &mut usize, n: usize) -> usize {
    while n > 0 {
        let r = &mut *acc;
        *r = *r + 1;
        n = n - 1;
    }
    *acc
}
```
-/

/-- 3-block loop `Trusted.MirBody` for `loop_accumulate`. -/
def mirLoopAccumulateBody : MirBody :=
  { argCount := 2
    localCount := 5
    localTys := [.usize, .refMut .usize, .usize, .bool, .refMut .usize]
    blocks :=
      [ -- bb0: loop header (`_3 = _2 > 0; SwitchInt(_3)`)
        { stmts :=
            [ .assign ⟨⟨3⟩, []⟩
                (.binaryOp .gt (.copy ⟨⟨2⟩, []⟩) (.constVal (.int 0)))
            ]
          terminator :=
            .switchInt (.copy ⟨⟨3⟩, []⟩)
              { branches := [⟨0, ⟨2⟩⟩], otherwise := ⟨1⟩ }
        }
      , -- bb1: loop body (`_4 = &mut *_1; *_4 += 1; _2 -= 1; goto bb0`)
        { stmts :=
            [ .storageLive ⟨4⟩
            , .assign ⟨⟨4⟩, []⟩ (.refMut ⟨⟨1⟩, [.deref]⟩)
            , .assign ⟨⟨4⟩, [.deref]⟩
                (.binaryOp .add (.copy ⟨⟨4⟩, [.deref]⟩) (.constVal (.int 1)))
            , .storageDead ⟨4⟩
            , .assign ⟨⟨2⟩, []⟩
                (.binaryOp .sub (.copy ⟨⟨2⟩, []⟩) (.constVal (.int 1)))
            ]
          terminator := .goto ⟨0⟩
        }
      , -- bb2: loop exit (`_0 = *_1; return`)
        { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩))]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirLoopAccumulateBody`. -/
def mirLoopAccumulateInitState (acc n : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨5⟩ [])
      , some (.int n)
      , some .uninit
      , none
      , some (.int acc)
      ]
    localGens := [0, 0, 0, 0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- `PureLift` `.whileLoop` plan for `loop_accumulate`: local `0` is `acc: &mut
usize`, local `1` is `n: usize`, and local `2` is the per-iteration reborrow
`r = &mut *acc` retired via `.endLoanAtLocal 2`. -/
def mirLoopAccumulatePlan : FlowPlan MirVal :=
  .whileLoop 4
    (.unary (fun v => mirGtVal v (.int 0)) (.localSub 1 []))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [])))
      (.seq
        (.act (.assign (.derefSub 2 [])
          (.unary (fun v => mirAddVal v (.int 1)) (.derefSub 2 []))))
        (.seq
          (.act (.endLoanAtLocal 2))
          (.act (.assign (.localSub 1 [])
            (.unary (fun v => mirSubUsizeVal v (.int 1)) (.localSub 1 [])))))))

def mirLoopAcc3 (acc : Nat) : Nat :=
  mirAddUsize (mirAddUsize (mirAddUsize acc 1) 1) 1

def mirLoopAccumulateState26 (acc : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨5⟩ [])
      , some (.int 0)
      , some (.bool false)
      , none
      , some (.int (mirLoopAcc3 acc))
      ]
    localGens := [0, 0, 0, 0, 6, 0]
    block := 2
    stmtIdx := 0
  }

def mirLoopAccumulateState27 (acc : Nat) : MirState :=
  { locals :=
      [ some (.int (mirLoopAcc3 acc))
      , some (.ref true 0 ⟨5⟩ [])
      , some (.int 0)
      , some (.bool false)
      , none
      , some (.int (mirLoopAcc3 acc))
      ]
    localGens := [0, 0, 0, 0, 6, 0]
    block := 2
    stmtIdx := 1
  }

theorem mirLoopAccumulate_runsTo (acc : Nat) :
    MirRunsTo [5] mirLoopAccumulateBody
      (mirLoopAccumulateInitState acc 3) 28
      ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ := by
  change MirRunsTo [5] mirLoopAccumulateBody
    (mirLoopAccumulateState26 acc) (1 + 1)
    ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩
  refine mir_stepped_runsTo [5] mirLoopAccumulateBody
    (mirLoopAccumulateState26 acc) (mirLoopAccumulateState27 acc) 1
    ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ ?_ rfl
  change
    (match
      if decide (mirLoopAcc3 acc < natPow2 64) = true then
        some (mirLoopAccumulateState27 acc).locals
      else none with
     | some locals' =>
       StepOutcome.stepped ⟨locals', [0, 0, 0, 0, 6, 0], 2, 1⟩
     | none => StepOutcome.fault) =
    StepOutcome.stepped (mirLoopAccumulateState27 acc)
  rw [mirLoopAcc3, decide_mirAddUsize_lt (mirAddUsize (mirAddUsize acc 1) 1) 1]
  rfl

/-- End-to-end verification of `mirLoopAccumulateBody` for 3 loop iterations
(`n = 3`) and arbitrary initial accumulator `acc : Nat`. -/
theorem mir_loop_accumulate_verified (acc : Nat) :
    (evalFnValue mirValAlg
        [⟨.mutRef 0 [], .int acc⟩, ⟨.byVal, .int 3⟩]
        mirLoopAccumulatePlan
        (.use (.derefSub 0 [])) =
      .ok ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩) ∧
    MirRunsTo [5] mirLoopAccumulateBody
      (mirLoopAccumulateInitState acc 3) 28
      ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ ∧
    (Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter [5] mirLoopAccumulateBody).ExecutesTo
        (.running (mirLoopAccumulateInitState acc 3)) k mFinal ∧
      (mirOperationalAdapter [5] mirLoopAccumulateBody).FinalLoansRel
        out mFinal ∧
      out = ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩) := by
  refine ⟨rfl, mirLoopAccumulate_runsTo acc, ?_⟩
  exact mir_pure_lift_sound [5] mirLoopAccumulateBody
    [⟨.mutRef 0 [], .int acc⟩, ⟨.byVal, .int 3⟩]
    mirLoopAccumulatePlan
    (.use (.derefSub 0 []))
    (fun out => out = ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩)
    (mirLoopAccumulateInitState acc 3)
    ⟨_, ⟨rfl, rfl⟩⟩
    rfl
    (by
      intro out hEval
      change
        EvalOutcome.ok ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ =
        EvalOutcome.ok out at hEval
      injection hEval with hOut
      subst hOut
      exact ⟨28, mirLoopAccumulate_runsTo acc⟩)

/-! ### Workload M-5: Dangling Reference and Use-While-Borrowed Rejection

Verifies fail-closed rejection of the same two invalid borrow-lifecycle
programs in both `PureLift` and `Trusted.MirSemantics`:
1. **Use after loan end / `StorageDead`**: borrowing `_2 = &mut _1`, ending the
   loan / executing `StorageDead(_1)`, and then reading `*_2` fails in both
   `PureLift` (`evalFnValue = .fail`) and `Trusted.MirSemantics` (`runMirSteps =
   none`).
2. **Owner overwrite while borrowed + child dereference**: borrowing `_2 = &mut
   (*_1)`, overwriting `*_1 = 99` while `_2` is active, and then reading `*_2`
   fails in both `PureLift` (`evalFnValue = .fail`) and `Trusted.MirSemantics`
   (`runMirSteps = none`).
-/

/-- `Trusted.MirBody` that takes `&mut _1`, executes `StorageDead(_1)`, and then
attempts to read `*_2`. -/
def mirDanglingRefBody : MirBody :=
  { argCount := 0
    localCount := 3
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 42)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩)
            , .storageDead ⟨1⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirDanglingRefBody`. -/
def mirDanglingRefInitState : MirState :=
  { locals := [some .uninit, none, none]
    localGens := [0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- `Trusted.MirBody` that borrows `_2 = &mut (*_1)`, overwrites `*_1 = 99`
while `_2` is active (retiring `_2`), and then attempts to read `*_2`. -/
def mirWriteWhileBorrowedBody : MirBody :=
  { argCount := 1
    localCount := 3
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, [.deref]⟩)
            , .assign ⟨⟨1⟩, [.deref]⟩ (.use (.constVal (.int 99)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirWriteWhileBorrowedBody`. -/
def mirWriteWhileBorrowedInitState : MirState :=
  { locals := [some .uninit, some (.ref true 0 ⟨3⟩ [] 0), none, some (.int 42)]
    localGens := [0, 0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- Both `PureLift` (`evalFnValue`) and `Trusted.runMirSteps` fail closed on
both use-after-loan-end and owner-overwrite-while-borrowed workloads. -/
theorem mir_dangling_and_conflict_rejected :
    evalFnValue mirValAlg
      []
      (.seq
        (.act (.assign (.localSub 0 []) (.constVal (.int 42))))
        (.seq
          (.act (.borrow 1 .mutBorrow (.localSub 0 [])))
          (.seq
            (.act (.endLoan 0))
            (.act (.assign (.localSub 2 []) (.use (.derefSub 1 [])))))))
      (.use (.localSub 2 [])) = .fail ∧
    runMirSteps mirDanglingRefBody 10 mirDanglingRefInitState = none ∧
    evalFnValue mirValAlg
      [⟨.mutRef 0 [], .int 42⟩]
      (.seq
        (.act (.borrow 1 .mutBorrow (.derefSub 0 [])))
        (.act (.assign (.derefSub 0 []) (.constVal (.int 99)))))
      (.use (.derefSub 1 [])) = .fail ∧
    runMirSteps mirWriteWhileBorrowedBody 10
      mirWriteWhileBorrowedInitState = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Exhaustive MIR Semantics and Bridge Regression Suite -/

/-- `mirValAlg.asBool` and `mirSubVal` handle integer branch conditions (`0` vs.
nonzero) and reject integer subtraction underflow (`b > a`). -/
theorem mir_int_branch_and_checked_sub_tests :
    evalFnValue mirValAlg
      [⟨.byVal, .int 5⟩]
      (.branch (.use (.localSub 0 []))
        (.act (.assign (.localSub 1 []) (.constVal (.int 10))))
        (.act (.assign (.localSub 1 []) (.constVal (.int 20)))))
      (.use (.localSub 1 [])) = .ok ⟨.int 10, []⟩ ∧
    evalFnValue mirValAlg
      [⟨.byVal, .int 0⟩]
      (.branch (.use (.localSub 0 []))
        (.act (.assign (.localSub 1 []) (.constVal (.int 10))))
        (.act (.assign (.localSub 1 []) (.constVal (.int 20)))))
      (.use (.localSub 1 [])) = .ok ⟨.int 20, []⟩ ∧
    mirSubVal (.int 5) (.int 2) = some (.int 3) ∧
    mirSubVal (.int 2) (.int 5) = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `MirVal.isFullyInit`, `readFieldPath`, and `writeFieldPath` operate on
10-field and depth-10 nested aggregates without any 8-step truncation. -/
def tenFieldTupleVal : MirVal :=
  packSpine
    [ .int 0, .int 1, .int 2, .int 3, .int 4
    , .int 5, .int 6, .int 7, .int 8, .int 9 ]

def depthTenNestedMirVal : MirVal :=
  .adt 0 (.fieldCons
    (.adt 0 (.fieldCons
      (.adt 0 (.fieldCons
        (.adt 0 (.fieldCons
          (.adt 0 (.fieldCons
            (.adt 0 (.fieldCons
              (.adt 0 (.fieldCons
                (.adt 0 (.fieldCons
                  (.adt 0 (.fieldCons
                    (.adt 0 (.fieldCons (.int 42) .unit))
                  .unit))
                .unit))
              .unit))
            .unit))
          .unit))
        .unit))
      .unit))
    .unit))
  .unit)

theorem mir_deep_aggregate_spine_and_path_tests :
    tenFieldTupleVal.isFullyInit = true ∧
    getMirField 9 tenFieldTupleVal = some (.int 9) ∧
    depthTenNestedMirVal.isFullyInit = true ∧
    readFieldPath [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] depthTenNestedMirVal =
      some (.int 42) ∧
    (match writeFieldPath [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (.int 99)
        depthTenNestedMirVal with
     | some updated =>
       updated.isFullyInit = true ∧
       readFieldPath [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] updated = some (.int 99)
     | none => False) := by
  refine ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩

/-- Integer bitwise binary operations (`.bitAnd`, `.bitOr`, `.bitXor`) evaluate
properly on `MirVal.int`, including values above $2^{16}$ without truncation. -/
theorem mir_integer_bitwise_ops_tests :
    evalBinOp .bitAnd (.int 6) (.int 3) = some (.int 2) ∧
    evalBinOp .bitOr (.int 6) (.int 3) = some (.int 7) ∧
    evalBinOp .bitXor (.int 6) (.int 3) = some (.int 5) ∧
    evalBinOp .bitXor (.int 0) (.int 0) = some (.int 0) ∧
    evalBinOp .bitAnd (.int 65536) (.int 65536) = some (.int 65536) ∧
    evalBinOp .bitOr (.int 65536) (.int 1) = some (.int 65537) ∧
    evalBinOp .bitXor (.int 65537) (.int 65536) = some (.int 1) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `UnOp.not` computes bitwise complement $(2^w - 1) - n$ on `MirTy.uint w`
integer operands as well as logical negation on `.bool` operands. -/
def mirUint8BitNotBody (input : Nat) : MirBody :=
  { argCount := 0
    localCount := 2
    localTys := [.uint 8, .uint 8]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int input)))
            , .assign ⟨⟨0⟩, []⟩ (.unaryOp .not (.copy ⟨⟨1⟩, []⟩))
            ]
          terminator := .return_
        }
      ]
  }

theorem mir_unop_not_uint8_and_bool_tests :
    (match runMirSteps (mirUint8BitNotBody 0) 5
        ⟨[some .uninit, none], [0, 0], 0, 0⟩ with
     | some ret => ret.value = .int 255
     | none => False) ∧
    (match runMirSteps (mirUint8BitNotBody 170) 5
        ⟨[some .uninit, none], [0, 0], 0, 0⟩ with
     | some ret => ret.value = .int 85
     | none => False) ∧
    evalUnOp .not none (.bool true) = some (.bool false) := by
  refine ⟨rfl, rfl, rfl⟩

/-- `assignPlace` rejects direct root assignment to an unallocated (`none`)
local slot before `StorageLive` has allocated it. -/
def mirAssignDeadLocalBody : MirBody :=
  { argCount := 0
    localCount := 2
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 42)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            ]
          terminator := .return_
        }
      ]
  }

theorem mir_assign_to_dead_local_rejected :
    runMirSteps mirAssignDeadLocalBody 4
      ⟨[some .uninit, none], [0, 0], 0, 0⟩ = none := rfl

/-- `Operand.move` deinitializes the moved place (or sub-field) to `.uninit`,
causing subsequent reads of the moved place to fault while leaving sibling
fields readable. -/
def mirUseAfterMoveLocalBody : MirBody :=
  { argCount := 0
    localCount := 2
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 11)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.move ⟨⟨1⟩, []⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            ]
          terminator := .return_
        }
      ]
  }

def mirPartialFieldMoveSiblingReadBody : MirBody :=
  { argCount := 0
    localCount := 3
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .storageLive ⟨2⟩
            , .assign ⟨⟨1⟩, []⟩
                (.aggregateFields
                  [.constVal (.int 10), .constVal (.int 20)] (some 0))
            , .assign ⟨⟨2⟩, []⟩ (.use (.move ⟨⟨1⟩, [.field 0]⟩))
            , .assign ⟨⟨0⟩, []⟩
                (.binaryOp .add
                  (.copy ⟨⟨2⟩, []⟩)
                  (.copy ⟨⟨1⟩, [.field 1]⟩))
            ]
          terminator := .return_
        }
      ]
  }

def mirPartialFieldMoveSameFieldReadBody : MirBody :=
  { argCount := 0
    localCount := 3
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .storageLive ⟨2⟩
            , .assign ⟨⟨1⟩, []⟩
                (.aggregateFields
                  [.constVal (.int 10), .constVal (.int 20)] (some 0))
            , .assign ⟨⟨2⟩, []⟩ (.use (.move ⟨⟨1⟩, [.field 0]⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.field 0]⟩))
            ]
          terminator := .return_
        }
      ]
  }

theorem mir_move_deinitializes_place_and_subfield_tests :
    runMirSteps mirUseAfterMoveLocalBody 6
      ⟨[some .uninit, none], [0, 0], 0, 0⟩ = none ∧
    (match runMirSteps mirPartialFieldMoveSiblingReadBody 7
        ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ with
     | some ret => ret.value = .int 30
     | none => False) ∧
    runMirSteps mirPartialFieldMoveSameFieldReadBody 7
      ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ = none := by
  refine ⟨rfl, rfl, rfl⟩

/-- `Trusted.MirSemantics` enforces Stacked-Borrows reference exclusivity while
supporting non-lexical borrow lifetimes (NLL):
1. Reading or writing an owner local `_1` directly while `_2 = &mut _1` is in
   scope retires `_2`, so a subsequent dereference `*_2` faults
   (`mirReadOwnerWhileMutBorrowedBody`), whereas NLL code that never uses `_2`
   again after overwriting `_1` succeeds
   (`mirNllOverwriteOwnerAfterBorrowBody`).
2. Using a parent mutable reference `*_2` while a child reborrow `_3 = &mut *_2`
   is in scope retires `_3`, so a subsequent use of `*_3` faults
   (`mirUseParentWhileReborrowedBody`).
3. Entry states with aliasing mutable reference arguments (`_1` and `_2`
   pointing to overlapping paths of the same caller slot) fault at step 0. -/
def mirReadOwnerWhileMutBorrowedBody : MirBody :=
  { argCount := 0
    localCount := 3
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 7)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩)
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

def mirNllOverwriteOwnerAfterBorrowBody : MirBody :=
  { argCount := 0
    localCount := 3
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 7)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩)
            , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.constVal (.int 8)))
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 9)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            ]
          terminator := .return_
        }
      ]
  }

def mirUseParentWhileReborrowedBody : MirBody :=
  { argCount := 0
    localCount := 4
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 7)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩)
            , .storageLive ⟨3⟩
            , .assign ⟨⟨3⟩, []⟩ (.refMut ⟨⟨2⟩, [.deref]⟩)
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨3⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

def mirAliasedMutEntryArgsBody : MirBody :=
  { argCount := 2
    localCount := 3
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩)) ]
          terminator := .return_
        }
      ]
  }

theorem mir_reference_exclusivity_enforced :
    runMirSteps mirReadOwnerWhileMutBorrowedBody 8
      ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ = none ∧
    (match runMirSteps mirNllOverwriteOwnerAfterBorrowBody 9
        ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ with
     | some ret => ret.value = .int 9
     | none => False) ∧
    runMirSteps mirUseParentWhileReborrowedBody 10
      ⟨[some .uninit, none, none, none], [0, 0, 0, 0], 0, 0⟩ = none ∧
    runMirSteps mirAliasedMutEntryArgsBody 3
      ⟨[some .uninit,
        some (.ref true 0 ⟨3⟩ []),
        some (.ref true 0 ⟨3⟩ []),
        some (.int 99)],
       [0, 0, 0, 0], 0, 0⟩ = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `Stmt.placeMention` succeeds on a live `.uninit` local without loading it,
and faults on a dead (`none`) local. -/
def mirPlaceMentionUninitBody : MirBody :=
  { argCount := 0
    localCount := 2
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .placeMention ⟨⟨1⟩, []⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int 7)))
            ]
          terminator := .return_
        }
      ]
  }

def mirPlaceMentionDeadBody : MirBody :=
  { argCount := 0
    localCount := 2
    blocks :=
      [ { stmts :=
            [ .placeMention ⟨⟨1⟩, []⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int 7)))
            ]
          terminator := .return_
        }
      ]
  }

theorem mir_place_mention_uninit_vs_dead_tests :
    (match runMirSteps mirPlaceMentionUninitBody 5
        ⟨[some .uninit, none], [0, 0], 0, 0⟩ with
     | some ret => ret.value = .int 7
     | none => False) ∧
    runMirSteps mirPlaceMentionDeadBody 5
      ⟨[some .uninit, none], [0, 0], 0, 0⟩ = none := by
  exact ⟨rfl, rfl⟩

/-- `MirVal.isValidInState` rejects copying or returning a stale reference (or
an aggregate containing a stale reference) after `StorageDead` invalidates the
referent local's generation. -/
def mirReturnStaleRefBody : MirBody :=
  { argCount := 0
    localCount := 2
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 10)))
            , .assign ⟨⟨0⟩, []⟩ (.ref ⟨⟨1⟩, []⟩)
            , .storageDead ⟨1⟩
            ]
          terminator := .return_
        }
      ]
  }

def mirCopyStaleRefInAdtBody : MirBody :=
  { argCount := 0
    localCount := 3
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 10)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.ref ⟨⟨1⟩, []⟩)
            , .assign ⟨⟨0⟩, []⟩ (.aggregateFields [.copy ⟨⟨2⟩, []⟩] (some 0))
            , .storageDead ⟨1⟩
            ]
          terminator := .return_
        }
      ]
  }

theorem mir_stale_ref_copy_and_return_rejected :
    runMirSteps mirReturnStaleRefBody 6
      ⟨[some .uninit, none], [0, 0], 0, 0⟩ = none ∧
    runMirSteps mirCopyStaleRefInAdtBody 8
      ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ = none := by
  exact ⟨rfl, rfl⟩

/-- Direct place access to a slot index $\ge$ `body.localCount` is rejected even
when `st.locals` contains caller-owned referent slots at those indices. -/
def mirOutOfBoundsDirectPlaceBody : MirBody :=
  { argCount := 1
    localCount := 2
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, []⟩)) ]
          terminator := .return_
        }
      ]
  }

theorem mir_direct_access_beyond_localCount_rejected :
    runMirSteps mirOutOfBoundsDirectPlaceBody 3
      ⟨[some .uninit, some (.ref true 0 ⟨2⟩ []), some (.int 55)],
       [0, 0, 0], 0, 0⟩ = none := rfl

/-- `MirBody.localTys` enforces declared local types and `uint` bit-width bounds
in `assignPlace`. -/
def mirTypedUint8Body (valToStore : Nat) : MirBody :=
  { argCount := 0
    localCount := 1
    localTys := [.uint 8]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int valToStore))) ]
          terminator := .return_
        }
      ]
  }

theorem mir_localTys_uint8_bounds_enforced :
    (match runMirSteps (mirTypedUint8Body 255) 3
        ⟨[some .uninit], [0], 0, 0⟩ with
     | some ret => ret.value = .int 255
     | none => False) ∧
    runMirSteps (mirTypedUint8Body 256) 3
      ⟨[some .uninit], [0], 0, 0⟩ = none := by
  exact ⟨rfl, rfl⟩

/-- Exhaustive unit tests for `Rvalue.copyForDeref`, `Stmt.nop`,
`Terminator.switchInt` (matched branch vs. `otherwise`),
`Terminator.unreachable`, and remaining `BinOp` operators (`.mul`, `.eq`, `.ne`,
`.lt`, `.le`, `.gt`, `.ge`, and boolean `.bitAnd` / `.bitOr` / `.bitXor`). -/
def mirCopyForDerefAndSwitchBody (sel : Nat) : MirBody :=
  { argCount := 0
    localCount := 3
    blocks :=
      [ { stmts :=
            [ .nop
            , .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 15)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.ref ⟨⟨1⟩, []⟩)
            ]
          terminator :=
            .switchInt (.constVal (.int sel))
              { branches := [⟨1, ⟨1⟩⟩], otherwise := ⟨2⟩ }
        }
      , { stmts :=
            [ .assign ⟨⟨0⟩, []⟩ (.copyForDeref ⟨⟨2⟩, [.deref]⟩)
            , .storageDead ⟨2⟩
            , .storageDead ⟨1⟩
            ]
          terminator := .return_
        }
      , { stmts := []
          terminator := .unreachable
        }
      ]
  }

theorem mir_copyForDeref_switch_unreachable_and_binops_exhaustive_tests :
    (match runMirSteps (mirCopyForDerefAndSwitchBody 1) 10
        ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ with
     | some ret => ret.value = .int 15
     | none => False) ∧
    runMirSteps (mirCopyForDerefAndSwitchBody 99) 10
      ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ = none ∧
    evalBinOp .mul (.int 6) (.int 7) = some (.int 42) ∧
    evalBinOp .eq (.int 5) (.int 5) = some (.bool true) ∧
    evalBinOp .ne (.int 5) (.int 6) = some (.bool true) ∧
    evalBinOp .lt (.int 3) (.int 5) = some (.bool true) ∧
    evalBinOp .le (.int 5) (.int 5) = some (.bool true) ∧
    evalBinOp .gt (.int 7) (.int 2) = some (.bool true) ∧
    evalBinOp .ge (.int 7) (.int 7) = some (.bool true) ∧
    evalBinOp .bitAnd (.bool true) (.bool false) = some (.bool false) ∧
    evalBinOp .bitOr (.bool true) (.bool false) = some (.bool true) ∧
    evalBinOp .bitXor (.bool true) (.bool true) = some (.bool false) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exhaustive regression tests for:
1. `mirValAlg.encodeSharedRef` (`isMut = false`) and `remapRefInVal` preserving
   `isMut`, `refGen`, and `reborrowDepth` inside nested `.adt` / `.fieldCons`
   aggregates,
2. `extractMirFuncOut` rejecting `.uninit` or stale/retired references in
   caller-owned referent slots,
3. `MirBody.ptrWidthBits` (e.g. `16`-bit target) enforcing `.usize` width bounds
   and bitwise complement,
4. Wrapping unsigned arithmetic (`.add`, `.sub`, `.mul`) on typed `.uint 8`
   locals (`255 + 1 = 0`, `0 - 1 = 255`, `16 * 16 = 0`), and
5. Intra-function reborrowing into an argument local (`_1 = &mut *_2`,
   `reborrowDepth = 1`) succeeding without faulting in `entryArgsExclusive`. -/
def mirTypedUint8WrapBody : MirBody :=
  { argCount := 0
    localCount := 3
    localTys := [.uint 8, .uint 8, .uint 8]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .storageLive ⟨2⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 0)))
            , .assign ⟨⟨2⟩, []⟩
                (.binaryOp .sub (.copy ⟨⟨1⟩, []⟩) (.constVal (.int 1)))
            , .assign ⟨⟨0⟩, []⟩
                (.binaryOp .add (.copy ⟨⟨2⟩, []⟩) (.constVal (.int 2)))
            ]
          terminator := .return_
        }
      ]
  }

def mirReborrowIntoArgSlotBody : MirBody :=
  { argCount := 2
    localCount := 3
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨1⟩, []⟩ (.refMut ⟨⟨2⟩, [.deref]⟩)
            , .assign ⟨⟨1⟩, [.deref]⟩ (.use (.constVal (.int 88)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

theorem round4_mir_and_bridge_regressions_exhaustive_tests :
    -- 1. `encodeSharedRef` vs `encodeRef` and `remapRefInVal` on nested `.adt`:
    mirValAlg.encodeSharedRef 3 [0] = .ref false 0 ⟨3⟩ [0] 0 ∧
    mirValAlg.remapRefInVal 3 9
      (.adt 0 (.fieldCons (.ref false 2 ⟨3⟩ [1] 4) .unit)) =
      .adt 0 (.fieldCons (.ref false 2 ⟨9⟩ [1] 4) .unit) ∧
    -- 2. `extractMirFuncOut` rejects `.uninit` and dangling references in
    -- caller slots:
    extractMirFuncOut [1]
      ⟨.unit, ⟨[some .unit, some .uninit], [0, 0], 0, 0⟩⟩ = none ∧
    extractMirFuncOut [1]
      ⟨.unit, ⟨[some .unit, some (.ref true 1 ⟨0⟩ [] 0)], [0, 0], 0, 0⟩⟩ =
      none ∧
    -- 3. `ptrWidthBits` parameterizes `tyBitWidth` and `checkValMatchesTy`:
    tyBitWidth 32 .usize = some 32 ∧
    checkValMatchesTy 8 .usize (.int 255) = true ∧
    checkValMatchesTy 8 .usize (.int 256) = false ∧
    -- 4. Wrapping `.sub` and `.add` on typed `.uint 8` locals
    -- (`0 - 1 + 2 = 1`):
    (match runMirSteps mirTypedUint8WrapBody 7
        ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ with
     | some ret => ret.value = .int 1
     | none => False) ∧
    evalBinOp .mul (.int 16) (.int 16) (some 8) = some (.int 0) ∧
    -- 5. Reborrowing `_1 = &mut *_2` into an argument local succeeds:
    (match runMirSteps mirReborrowIntoArgSlotBody 5
        ⟨[some .uninit,
          some (.ref true 0 ⟨3⟩ [] 0),
          some (.ref true 0 ⟨4⟩ [] 0),
          some (.int 10),
          some (.int 20)],
         [0, 0, 0, 0, 0], 0, 0⟩ with
     | some ret =>
       extractMirFuncOut [3, 4] ret = some ⟨.int 88, [.int 10, .int 88]⟩
     | none => False) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exhaustive regression tests for Round 5 MIR and bridge invariants:
1. Projected tuple field width inference (`_1.0` where `_1 : (u8, u16)` wraps
   `255 + 1` to `0` and computes `8`-bit `!0 = 255`),
2. Recursive tuple type checking in `checkValMatchesTy` (accepting matching
   element types/arity and rejecting mismatched element types or wrong arity),
3. Entry argument exclusivity and validity (`entryArgsExclusive`) rejecting
   aliased mutable references nested inside a tuple argument as well as dangling
   reference arguments at entry,
4. `stepTerminator` at `Terminator.return_` rejecting return values that
   contain a reference into the returning frame (`targetLoc.index <
   body.localCount`) while allowing caller-owned references (`≥ localCount`),
   and
5. Boolean relational comparisons (`.lt`, `.le`, `.gt`, `.ge`) in `evalBinOp`.
-/
def mirProjectedTupleFieldBody : MirBody :=
  { argCount := 0
    localCount := 2
    localTys := [.uint 8, .tuple [.uint 8, .uint 16]]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩
                (.use (.constVal
                  (.fieldCons (.int 255) (.fieldCons (.int 1000) .unit))))
            , .assign ⟨⟨1⟩, [.field 0]⟩
                (.binaryOp .add
                  (.copy ⟨⟨1⟩, [.field 0]⟩)
                  (.constVal (.int 1)))
            , .assign ⟨⟨0⟩, []⟩ (.unaryOp .not (.copy ⟨⟨1⟩, [.field 0]⟩))
            ]
          terminator := .return_
        }
      ]
  }

def mirReturnFrameRefBody : MirBody :=
  { argCount := 0
    localCount := 2
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 7)))
            , .assign ⟨⟨0⟩, []⟩ (.ref ⟨⟨1⟩, []⟩)
            ]
          terminator := .return_
        }
      ]
  }

theorem round5_mir_and_bridge_regressions_exhaustive_tests :
    -- 1. Projected tuple field `u8` wrapping `.add` and `.not`:
    (match runMirSteps mirProjectedTupleFieldBody 6
        ⟨[some .uninit, none], [0, 0], 0, 0⟩ with
     | some ret => ret.value = .int 255
     | none => False) ∧
    -- 2. Recursive tuple validation in `checkValMatchesTy`:
    checkValMatchesTy 64 (.tuple [.uint 8, .bool])
      (.fieldCons (.int 200) (.fieldCons (.bool true) .unit)) = true ∧
    checkValMatchesTy 64 (.tuple [.uint 8])
      (.fieldCons (.bool true) (.fieldCons (.int 1) .unit)) = false ∧
    checkValMatchesTy 64 (.tuple [.uint 8, .bool])
      (.fieldCons (.int 300) (.fieldCons (.bool true) .unit)) = false ∧
    -- 3. `entryArgsExclusive` rejects nested aliased `&mut` inside a tuple arg
    -- and rejects a dangling reference argument at entry:
    entryArgsExclusive
      { argCount := 1, localCount := 2, blocks := [] }
      ⟨[some .uninit,
        some (.fieldCons (.ref true 0 ⟨2⟩ [] 0)
          (.fieldCons (.ref true 0 ⟨2⟩ [] 0) .unit)),
        some (.int 1)],
       [0, 0, 0], 0, 0⟩ = false ∧
    entryArgsExclusive
      { argCount := 1, localCount := 2, blocks := [] }
      ⟨[some .uninit, some (.ref false 1 ⟨2⟩ [] 0), some (.int 1)],
       [0, 0, 0], 0, 0⟩ = false ∧
    -- 4. Returning a reference to an in-frame local (`_1 < localCount`) faults:
    runMirSteps mirReturnFrameRefBody 6
      ⟨[some .uninit, none], [0, 0], 0, 0⟩ = none ∧
    -- 5. Boolean relational comparisons (`false < true`):
    evalBinOp .lt (.bool false) (.bool true) = some (.bool true) ∧
    evalBinOp .lt (.bool true) (.bool false) = some (.bool false) ∧
    evalBinOp .le (.bool true) (.bool true) = some (.bool true) ∧
    evalBinOp .gt (.bool true) (.bool false) = some (.bool true) ∧
    evalBinOp .ge (.bool false) (.bool true) = some (.bool false) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PureLift
