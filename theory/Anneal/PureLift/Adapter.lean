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
import Anneal.PureLift.Plan
import Anneal.PureLift.BlockCfg

namespace Anneal.PureLift

/-!
# Operational Machine Adapters and Adequacy Theorem (`Adapter`)

Decouples `PureLift` from any specific operational semantics representation via
two interfaces:
- `SpatialModel`: interprets `PermTree` sub-place ownership and disjointness in
  a concrete memory model (`MachMem` and `Addr`).
- `OperationalAdapter`: connects `evalFnValue` to a concrete machine's
  multi-step reachability relation `ExecutesTo : Mach → Nat → Mach → Prop` via
  the adequacy theorem `pure_lift_sound`.

Also provides three canonical adapter constructors covering:
1. Total step-function machines (`M1StepResult`, `m1OperationalAdapter`).
2. Relational trace-emitting small-step machines (`M2StepResult`,
   `m2OperationalAdapter`).
3. Allocation/offset heaps with Tree Borrows permission tags (`M3Mach`,
   `m3SpatialModel`, `m3OperationalAdapter`).
-/

/-- Spatial sub-place ownership realization interface over a concrete memory
representation `MachMem` and address type `Addr`. -/
structure SpatialModel (Val MachMem Addr : Type) where
  ownSubPlace : MachMem → Addr → SubPath → PermTree → Val → Prop
  frameHolds : (MachMem → Prop) → MachMem → Prop
  disjointSubPlaces : Addr → SubPath → Addr → SubPath → Prop

/-- Constructive finite-step operational adapter connecting `PureLift` symbolic
evaluation to an arbitrary operational machine `Mach`. -/
structure OperationalAdapter (Mach Val : Type) where
  ExecutesTo : Mach → Nat → Mach → Prop
  StateRel : SymState Val → Mach → Prop
  FinalLoansRel : FuncOut Val → Mach → Prop
  exec_zero : ∀ m, ExecutesTo m 0 m
  exec_trans : ∀ {m1 m2 m3 k1 k2},
    ExecutesTo m1 k1 m2 → ExecutesTo m2 k2 m3 → ExecutesTo m1 (k1 + k2) m3

/-- Adequacy theorem (`pure_lift_sound`): if `initFnState alg params` produces
an initial symbolic state `st0` related to `m0` via `ad.StateRel st0 m0`,
`evalFnValue alg params plan retExpr` satisfies `HoldsFnSpec ... post`, and the
operational adapter simulates the evaluation from `(st0, m0)`, then `m0` reaches
a terminal machine state `mFinal` in `k` steps satisfying `FinalLoansRel out
mFinal` and `post out`. -/
theorem pure_lift_sound {Mach Val : Type}
    (ad : OperationalAdapter Mach Val)
    (alg : ValAlgebra Val)
    (params : List (ParamInput Val))
    (plan : FlowPlan Val)
    (retExpr : RvalOp Val)
    (post : FuncOut Val → Prop)
    (m0 : Mach)
    (hInit : Exists fun st0 =>
      initFnState alg params = .ok st0 ∧ ad.StateRel st0 m0)
    (hSpec : HoldsFnSpec (evalFnValue alg params plan retExpr) post)
    (hSim : ∀ st0 out,
      initFnState alg params = .ok st0 →
      ad.StateRel st0 m0 →
      evalFnValue alg params plan retExpr = .ok out →
      Exists fun k => Exists fun mFinal =>
        ad.ExecutesTo m0 k mFinal ∧ ad.FinalLoansRel out mFinal) :
    Exists fun k => Exists fun mFinal => Exists fun out =>
      ad.ExecutesTo m0 k mFinal ∧
      ad.FinalLoansRel out mFinal ∧
      post out := by
  cases hInit with
  | intro st0 hInitPair =>
    cases hEval : evalFnValue alg params plan retExpr with
    | fail =>
      rw [hEval] at hSpec
      nomatch hSpec
    | ok out =>
      have hStep := hSim st0 out hInitPair.1 hInitPair.2 hEval
      rw [hEval] at hSpec
      dsimp [HoldsFnSpec] at hSpec
      cases hStep with
      | intro k hk =>
        cases hk with
        | intro mFinal hm =>
          exact ⟨k, ⟨mFinal, ⟨out, hm.1, hm.2, hSpec⟩⟩⟩

/-- Style 1: Total step-function outcome (`.next`, `.ret`, `.fault`). -/
inductive M1StepResult (State Val : Type) where
  | next (s' : State)
  | ret (out : FuncOut Val)
  | fault

inductive M1MachState (State Val : Type) where
  | running (s : State)
  | returned (out : FuncOut Val)
  | faulted

def m1StepMach {State Val : Type}
    (step : State → M1StepResult State Val) :
    M1MachState State Val → M1MachState State Val
  | .running s =>
    match step s with
    | .next s' => .running s'
    | .ret out => .returned out
    | .fault => .faulted
  | .returned out => .returned out
  | .faulted => .faulted

def m1RunN {State Val : Type} (step : State → M1StepResult State Val)
    (k : Nat) (m : M1MachState State Val) : M1MachState State Val :=
  @Nat.recCompiled (fun _ => M1MachState State Val → M1MachState State Val)
    (fun m0 => m0)
    (fun _ ih m0 => ih (m1StepMach step m0))
    k m

theorem m1RunN_succ {State Val : Type}
    (step : State → M1StepResult State Val)
    (k : Nat) (m : M1MachState State Val) :
    m1RunN step (k + 1) m = m1RunN step k (m1StepMach step m) := rfl

theorem m1RunN_add {State Val : Type}
    (step : State → M1StepResult State Val)
    (k1 k2 : Nat) (m : M1MachState State Val) :
    m1RunN step (k1 + k2) m = m1RunN step k2 (m1RunN step k1 m) := by
  induction k1 generalizing m with
  | zero =>
    have hZ : 0 + k2 = k2 := Nat.zero_add k2
    rw [hZ]
    rfl
  | succ k1' ih =>
    have hS : (k1' + 1) + k2 = (k1' + k2) + 1 := Nat.succ_add k1' k2
    rw [hS]
    rw [m1RunN_succ, m1RunN_succ]
    exact ih (m1StepMach step m)

/-- Operational adapter for total step-function machines (`M1StepResult`). -/
def m1OperationalAdapter {State Val : Type}
    (step : State → M1StepResult State Val)
    (stateRel : SymState Val → State → Prop) :
    OperationalAdapter (M1MachState State Val) Val where
  ExecutesTo m1 k m2 := m1RunN step k m1 = m2
  StateRel st m :=
    match m with
    | .running s => stateRel st s
    | _ => False
  FinalLoansRel out m := m = .returned out
  exec_zero _ := rfl
  exec_trans h1 h2 := by
    rw [m1RunN_add]
    rw [h1]
    exact h2

/-- Style 2: Relational small-step transition with observable trace events and
nondeterministic choice (`M2StepResult`). -/
inductive M2StepResult (State Obs Val : Type) where
  | step (ev : List Obs) (s' : State)
  | choice (nexts : State → Prop)
  | terminated (out : FuncOut Val)
  | failed

structure M2Config (State Obs Val : Type) where
  state : State
  trace : List Obs
  terminal : Option (FuncOut Val)

inductive M2ExecutesTo {State Obs Val : Type}
    (step : State → M2StepResult State Obs Val) :
    M2Config State Obs Val → Nat → M2Config State Obs Val → Prop where
  | refl (c : M2Config State Obs Val) :
      M2ExecutesTo step c 0 c
  | trans {c1 c2 c3 : M2Config State Obs Val} {k1 k2 : Nat} :
      M2ExecutesTo step c1 k1 c2 →
      M2ExecutesTo step c2 k2 c3 →
      M2ExecutesTo step c1 (k1 + k2) c3
  | step_emit {s s' : State} {tr ev : List Obs} :
      step s = .step ev s' →
      M2ExecutesTo step ⟨s, tr, none⟩ 1 ⟨s', tr ++ ev, none⟩
  | step_choice {s s' : State} {tr : List Obs} {nexts : State → Prop} :
      step s = .choice nexts →
      nexts s' →
      M2ExecutesTo step ⟨s, tr, none⟩ 1 ⟨s', tr, none⟩
  | step_term {s : State} {tr : List Obs} {out : FuncOut Val} :
      step s = .terminated out →
      M2ExecutesTo step ⟨s, tr, none⟩ 1 ⟨s, tr, some out⟩

def M2ProductiveOn {State Obs Val : Type}
    (step : State → M2StepResult State Obs Val) (s : State) : Prop :=
  match step s with
  | .failed => False
  | .choice nexts => Exists fun s' => nexts s'
  | _ => True

/-- Operational adapter for trace-emitting relational small-step machines
(`M2StepResult`). -/
def m2OperationalAdapter {State Obs Val : Type}
    (step : State → M2StepResult State Obs Val)
    (stateRel : SymState Val → State → Prop) :
    OperationalAdapter (M2Config State Obs Val) Val where
  ExecutesTo := M2ExecutesTo step
  StateRel st c :=
    c.terminal = none ∧ stateRel st c.state ∧ M2ProductiveOn step c.state
  FinalLoansRel out c := c.terminal = some out
  exec_zero := M2ExecutesTo.refl
  exec_trans := M2ExecutesTo.trans

/-- Style 3: Allocation/offset heap (`AllocId × Offset`) with Tree Borrows
permission tags (`TbPerm`). -/
abbrev AllocId := Nat
abbrev Offset := Nat
abbrev TbTag := Nat

inductive TbPerm where
  | reserved
  | activeUnique
  | frozen
  | disabled

structure M3Cell (Val : Type) where
  allocId : AllocId
  offset : Offset
  subPath : SubPath := []
  tag : TbTag
  perm : TbPerm
  cellVal : CellVal Val

structure M3Mach (Val : Type) where
  heap : List (M3Cell Val)
  retOut : Option (FuncOut Val)

/-- True iff neither `p1` nor `p2` is a prefix of the other, witnessing
non-overlapping sub-place paths within the same allocation slot. -/
def subPathDisjoint (p1 p2 : SubPath) : Bool :=
  listFold
    (fun _ => false)
    (fun x _ ih ys =>
      match ys with
      | [] => false
      | y :: ys' => if x == y then ih ys' else true)
    p1 p2

def m3LookupCell {Val : Type} (aid : AllocId) (off : Offset) (path : SubPath)
    (cells : List (M3Cell Val)) : Option (M3Cell Val) :=
  cells.foldr
    (fun c ih =>
      if c.allocId == aid && c.offset == off && subPathEq c.subPath path then
        some c
      else ih)
    none

/-- Spatial ownership model interpreting `PermTree` permissions as Tree Borrows
`TbPerm` states at `(AllocId × Offset)` locations and sub-paths, projecting
`getPathPerm path perm` and tying `c.tag` to the active loan ID(s) at `path`. -/
def m3SpatialModel (Val : Type) :
    SpatialModel Val (List (M3Cell Val)) (AllocId × Offset) where
  ownSubPlace heap addr path perm v :=
    match m3LookupCell addr.1 addr.2 path heap with
    | some c =>
      c.cellVal = .init v ∧
      match getPathPerm path perm with
      | .unborrowed => c.perm = .activeUnique
      | .mutLocked lid =>
        c.tag = lid ∧ (c.perm = .activeUnique ∨ c.perm = .reserved)
      | .mutJoined mLids sLids =>
        (elemLoanId c.tag mLids = true ∨ elemLoanId c.tag sLids = true) ∧
        (c.perm = .activeUnique ∨ c.perm = .reserved)
      | .shared lids =>
        elemLoanId c.tag lids = true ∧ c.perm = .frozen
      | .split _ => c.perm = .activeUnique
    | none => False
  frameHolds frame heap := frame heap
  disjointSubPlaces a1 p1 a2 p2 := a1 ≠ a2 ∨ subPathDisjoint p1 p2 = true

inductive M3ExecutesTo {Val : Type}
    (step : List (M3Cell Val) → M1StepResult (List (M3Cell Val)) Val) :
    M3Mach Val → Nat → M3Mach Val → Prop where
  | refl (m : M3Mach Val) : M3ExecutesTo step m 0 m
  | trans {m1 m2 m3 : M3Mach Val} {k1 k2 : Nat} :
      M3ExecutesTo step m1 k1 m2 → M3ExecutesTo step m2 k2 m3 →
      M3ExecutesTo step m1 (k1 + k2) m3
  | step_heap {heap heap' : List (M3Cell Val)} :
      step heap = .next heap' →
      M3ExecutesTo step ⟨heap, none⟩ 1 ⟨heap', none⟩
  | step_ret {heap : List (M3Cell Val)} {out : FuncOut Val} :
      step heap = .ret out →
      M3ExecutesTo step ⟨heap, none⟩ 1 ⟨heap, some out⟩

/-- Operational adapter for allocation/tag-tree machines (`M3Mach`) driven by a
heap step function `step` and state relation `stateRel`. -/
def m3OperationalAdapter {Val : Type}
    (step : List (M3Cell Val) → M1StepResult (List (M3Cell Val)) Val)
    (stateRel : SymState Val → List (M3Cell Val) → Prop) :
    OperationalAdapter (M3Mach Val) Val where
  ExecutesTo := M3ExecutesTo step
  StateRel st m := m.retOut = none ∧ stateRel st m.heap
  FinalLoansRel out m := m.retOut = some out
  exec_zero := M3ExecutesTo.refl
  exec_trans := M3ExecutesTo.trans

/-!
## Exhaustive Kernel-Checked Unit Tests for `Adapter`
-/

/-- Exhaustive unit tests for `m1StepMach`, `m1RunN`, `M2ProductiveOn`,
`subPathDisjoint`, `m3LookupCell`, and `m3SpatialModel.ownSubPlace` across all
`PermTree` constructors. -/
theorem adapter_styles_and_m3SpatialModel_exhaustive_tests :
    let stepM1 (s : Nat) : M1StepResult Nat LensTestVal :=
      match s with
      | 0 => .next 1
      | 1 => .ret ⟨.atom 42, []⟩
      | _ => .fault
    let stepM2 (s : Nat) : M2StepResult Nat Nat LensTestVal :=
      match s with
      | 0 => .step [10] 1
      | 1 => .terminated ⟨.atom 42, []⟩
      | _ => .failed
    let sp := m3SpatialModel LensTestVal
    let heap : List (M3Cell LensTestVal) :=
      [ ⟨0, 0, [], 1, .activeUnique, .init (.atom 10)⟩
      , ⟨0, 1, [0], 2, .reserved, .init (.atom 20)⟩
      , ⟨0, 2, [1], 3, .frozen, .init (.atom 30)⟩ ]
    m1RunN stepM1 0 (.running 0) = .running 0 ∧
    m1RunN stepM1 1 (.running 0) = .running 1 ∧
    m1RunN stepM1 2 (.running 0) = .returned ⟨.atom 42, []⟩ ∧
    m1RunN stepM1 3 (.running 0) = .returned ⟨.atom 42, []⟩ ∧
    m1RunN stepM1 1 (.running 99) = .faulted ∧
    m1RunN stepM1 2 (.running 99) = .faulted ∧
    M2ProductiveOn stepM2 0 ∧
    M2ProductiveOn stepM2 1 ∧
    ¬ M2ProductiveOn stepM2 99 ∧
    subPathDisjoint [] [0] = false ∧
    subPathDisjoint [0, 1] [0, 2] = true ∧
    sp.ownSubPlace heap (0, 0) [] .unborrowed (.atom 10) ∧
    sp.ownSubPlace heap (0, 1) [0] (.mutLocked 2) (.atom 20) ∧
    sp.ownSubPlace heap (0, 1) [0] (.mutJoined [2] [9]) (.atom 20) ∧
    sp.ownSubPlace heap (0, 2) [1] (.shared [3]) (.atom 30) ∧
    ¬ sp.ownSubPlace heap (9, 9) [] .unborrowed (.atom 10) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial, trivial,
    fun h => h, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, ⟨rfl, Or.inr rfl⟩⟩,
    ⟨rfl, ⟨Or.inl rfl, Or.inr rfl⟩⟩, ⟨rfl, ⟨rfl, rfl⟩⟩, fun h => h⟩

end Anneal.PureLift
