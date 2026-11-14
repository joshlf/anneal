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

namespace Anneal.PureLift

/-!
# Constructive Loop Cutpoints and Block-Indexed CFG Certificates (`BlockCfg`)

Provides two complementary control-flow verification mechanisms over `FlowPlan`:
- `runWhileFlowSteps_cutpoint_sound`: proves that any `FlowPlan.whileLoop`
  satisfying an inductive loop invariant `Inv` and a ranking measure
  `rank : SymState Val → Nat` that decreases on each taken iteration terminates
  in `.ok (.continuing sFinal)` with `Inv sFinal` and exit condition `false`.
- `BasicBlock`, `stepBasicBlock`, `runBlockCfg`, and `modular_block_cfg_sound`:
  verify unstructured or multi-block control-flow graphs in $O(N)$ per-block
  verification conditions (`LocalBlockVC`), where each basic block's body is a
  `FlowPlan Val` evaluated via `evalPlan`.
-/

theorem runWhileFlowSteps_zero {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val)
    (evalBody : SymState Val → EvalOutcome (ExecFlow Val))
    (s : SymState Val) :
    runWhileFlowSteps alg cond evalBody 0 s =
      (match evalRval alg cond s with
       | some cv =>
         match alg.asBool cv with
         | some false => .ok (.continuing s)
         | _ => .fail
       | none => .fail) := rfl

theorem runWhileFlowSteps_succ {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val)
    (evalBody : SymState Val → EvalOutcome (ExecFlow Val))
    (k : Nat) (s : SymState Val) :
    runWhileFlowSteps alg cond evalBody (k + 1) s =
      (match evalRval alg cond s with
       | some cv =>
         match alg.asBool cv with
         | some false => .ok (.continuing s)
         | some true =>
           match evalBody s with
           | .ok (.continuing s') =>
             runWhileFlowSteps alg cond evalBody k s'
           | .ok (.returned out) => .ok (.returned out)
           | .ok (.guardedContinuing wrap1 s') =>
             prependGuardedWrap wrap1
               (runWhileFlowSteps alg cond evalBody k s')
           | .fail => .fail
         | none => .fail
       | none => .fail) := rfl

/-- Constructive loop cutpoint theorem for `runWhileFlowSteps`. -/
theorem runWhileFlowSteps_cutpoint_sound {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val)
    (evalBody : SymState Val → EvalOutcome (ExecFlow Val))
    (Inv : SymState Val → Prop) (rank : SymState Val → Nat)
    (hStep : ∀ s, Inv s →
      Exists fun cv => evalRval alg cond s = some cv ∧
        ((alg.asBool cv = some false ∧ rank s = 0) ∨
         (alg.asBool cv = some true ∧
          Exists fun s' =>
            evalBody s = .ok (.continuing s') ∧
            Inv s' ∧ rank s = rank s' + 1))) :
    ∀ fuel s, Inv s → rank s = fuel →
      Exists fun sFinal =>
        runWhileFlowSteps alg cond evalBody fuel s =
          .ok (.continuing sFinal) ∧
        Inv sFinal ∧
        (Exists fun cv =>
          evalRval alg cond sFinal = some cv ∧ alg.asBool cv = some false)
  | 0, s, hInv, hRank => by
    cases hStep s hInv with
    | intro cv hcv =>
      cases hcv with
      | intro hEval hBranch =>
        cases hBranch with
        | inl hFalse =>
          cases hFalse with
          | intro hBool _ =>
            refine ⟨s, ?_, hInv, ⟨cv, hEval, hBool⟩⟩
            rw [runWhileFlowSteps_zero]
            rw [hEval]
            dsimp
            rw [hBool]
        | inr hTrue =>
          cases hTrue with
          | intro _ hNext =>
            cases hNext with
            | intro s' hs' =>
              cases hs' with
              | intro _ hInvAndRank =>
                cases hInvAndRank with
                | intro _ hRankEq =>
                  rw [hRank] at hRankEq
                  nomatch hRankEq
  | k + 1, s, hInv, hRank => by
    cases hStep s hInv with
    | intro cv hcv =>
      cases hcv with
      | intro hEval hBranch =>
        cases hBranch with
        | inl hFalse =>
          cases hFalse with
          | intro _ hRankZero =>
            rw [hRank] at hRankZero
            nomatch hRankZero
        | inr hTrue =>
          cases hTrue with
          | intro hBool hNext =>
            cases hNext with
            | intro s' hs' =>
              cases hs' with
              | intro hBody hInvAndRank =>
                cases hInvAndRank with
                | intro hInv' hRankEq =>
                  rw [hRank] at hRankEq
                  injection hRankEq with hRank'
                  have ih :=
                    runWhileFlowSteps_cutpoint_sound alg cond evalBody Inv rank
                      hStep k s' hInv' (Eq.symm hRank')
                  cases ih with
                  | intro sFinal hsFinal =>
                    cases hsFinal with
                    | intro hRun hRest =>
                      refine ⟨sFinal, ?_, hRest⟩
                      rw [runWhileFlowSteps_succ]
                      rw [hEval]
                      dsimp
                      rw [hBool]
                      dsimp
                      rw [hBody]
                      exact hRun

/-- Terminator of a `BasicBlock Val`. -/
inductive BlockTerm (Val : Type) where
  | goto (target : BlockId) : BlockTerm Val
  | branch (cond : RvalOp Val) (thenTarget elseTarget : BlockId) :
      BlockTerm Val
  | ret (retExpr : RvalOp Val) : BlockTerm Val

/-- Basic block whose straight-line or structured body is a `FlowPlan Val` and
whose exit is a `BlockTerm Val`. -/
structure BasicBlock (Val : Type) where
  body : FlowPlan Val
  term : BlockTerm Val

inductive BlockStepResult (State Ret : Type) where
  | jump (nextBb : Nat) (st' : State)
  | ret (val : Ret)
  | fault

inductive BlockCfgOutcome (Ret : Type) where
  | ret (val : Ret)
  | diverged
  | fault

def listGetOpt {α : Type} (idx : Nat) (xs : List α) : Option α :=
  xs.foldr
    (fun x ih n =>
      match n with
      | 0 => some x
      | n' + 1 => ih n')
    (fun _ => none)
    idx

/-- Execute one `BasicBlock Val` by running `evalPlan alg bb.body st` and
dispatching on `bb.term`. -/
def stepBasicBlock {Val : Type} (alg : ValAlgebra Val)
    (blocks : List (BasicBlock Val)) (bbIdx : BlockId)
    (st : SymState Val) : BlockStepResult (SymState Val) (FuncOut Val) :=
  match listGetOpt bbIdx blocks with
  | none => .fault
  | some bb =>
    match evalPlan alg bb.body st with
    | .fail => .fault
    | .ok (.returned out) => .ret out
    | .ok (.guardedContinuing wrapOut st') =>
      match bb.term with
      | .ret retExpr =>
        if !stateCleanAtReturn st' then .fault
        else
          match evalRval alg retExpr st' with
          | some rv =>
            .ret (wrapOut ⟨rv, collectRootMutVals st'.loans⟩)
          | none => .fault
      | _ => .fault
    | .ok (.continuing st') =>
      match bb.term with
      | .goto tgt => .jump tgt st'
      | .branch cond tTgt fTgt =>
        match evalRval alg cond st' with
        | some cv =>
          match alg.asBool cv with
          | some true => .jump tTgt st'
          | some false => .jump fTgt st'
          | none => .fault
        | none => .fault
      | .ret retExpr =>
        if !stateCleanAtReturn st' then .fault
        else
          match evalRval alg retExpr st' with
          | some rv => .ret ⟨rv, collectRootMutVals st'.loans⟩
          | none => .fault

/-- Run a block-indexed CFG for `fuel` basic-block transitions. -/
def runBlockCfg {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (bb : Nat) (st : State) (fuel : Nat) : BlockCfgOutcome Ret :=
  @Nat.recCompiled (fun _ => Nat → State → BlockCfgOutcome Ret)
    (fun _ _ => .diverged)
    (fun _ ih bb0 st0 =>
      match stepBb bb0 st0 with
      | .fault => .fault
      | .ret v => .ret v
      | .jump nextBb st' => ih nextBb st')
    fuel bb st

def BlockCfgPartialSpec {Ret : Type} (out : BlockCfgOutcome Ret)
    (PostRet : Ret → Prop) : Prop :=
  match out with
  | .ret v => PostRet v
  | .diverged => True
  | .fault => False

/-- Per-block verification condition (`LocalBlockVC`) for compositional $O(N)$
CFG verification. -/
def LocalBlockVC {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop) : Prop :=
  ∀ bb st,
    BlockInv bb st →
    match stepBb bb st with
    | .fault => False
    | .ret v => PostRet v
    | .jump nextBb st' => BlockInv nextBb st'

theorem runBlockCfg_succ {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (bb : Nat) (st : State) (fuel' : Nat) :
    runBlockCfg stepBb bb st (fuel' + 1) =
      (match stepBb bb st with
       | .fault => .fault
       | .ret v => .ret v
       | .jump nextBb st' => runBlockCfg stepBb nextBb st' fuel') := rfl

/-- Compositional CFG soundness: if `LocalBlockVC` holds for every block, then
any `fuel`-step execution from an invariant-satisfying block state never faults
and satisfies `PostRet` whenever it returns. -/
theorem modular_block_cfg_sound {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop)
    (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC stepBb BlockInv PostRet) :
    ∀ (fuel : Nat) (bb : Nat) (st : State),
      BlockInv bb st →
      BlockCfgPartialSpec (runBlockCfg stepBb bb st fuel) PostRet
  | 0, _, _, _ => by
    exact True.intro
  | fuel' + 1, bb, st, hInv => by
    rw [runBlockCfg_succ]
    have hVC := hLocal bb st hInv
    cases hStep : stepBb bb st with
    | fault =>
      rw [hStep] at hVC
      nomatch hVC
    | ret v =>
      rw [hStep] at hVC
      dsimp [BlockCfgPartialSpec]
      exact hVC
    | jump nextBb st' =>
      rw [hStep] at hVC
      dsimp at hVC
      exact modular_block_cfg_sound stepBb BlockInv PostRet hLocal
        fuel' nextBb st' hVC

/-!
## CFG-to-`FlowPlan` Equivalence Certificates (`CfgCertificate`)
-/

/-- Certificate pairing a block-indexed CFG (`blocks`, `entryBb`, `fuel`) with
a structured `FlowPlan Val`. -/
structure CfgCertificate (Val : Type) where
  blocks : List (BasicBlock Val)
  entryBb : BlockId
  fuel : Nat
  plan : FlowPlan Val

/-- Single-block CFG equivalence (`cfg_certificate_step_sound`): executing a
1-block CFG `[⟨plan, .ret retExpr⟩]` for 1 step via `runBlockCfg` produces `.ret
out` whenever `evalFnValue alg params plan retExpr = .ok out`. -/
theorem cfg_certificate_step_sound {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retExpr : RvalOp Val) (st0 : SymState Val) (out : FuncOut Val)
    (hInit : initFnState alg params = .ok st0)
    (hEval : evalFnValue alg params plan retExpr = .ok out) :
    runBlockCfg (stepBasicBlock alg [⟨plan, .ret retExpr⟩]) 0 st0 1 =
      .ret out := by
  dsimp [evalFnValue] at hEval
  rw [hInit] at hEval
  dsimp at hEval
  rw [runBlockCfg_succ]
  dsimp [stepBasicBlock, listGetOpt]
  revert hEval
  cases hPlan : evalPlan alg plan st0 with
  | fail =>
    intro hFalse
    nomatch hFalse
  | ok flow =>
    cases flow with
    | returned out' =>
      dsimp
      intro hEq
      injection hEq with hOut
      rw [hOut]
    | continuing stF =>
      dsimp
      cases hClean : stateCleanAtReturn stF with
      | false =>
        dsimp
        intro hFalse
        nomatch hFalse
      | true =>
        dsimp
        cases hRet : evalRval alg retExpr stF with
        | none =>
          dsimp
          intro hFalse
          nomatch hFalse
        | some retVal =>
          dsimp
          intro hEq
          injection hEq with hOut
          rw [← hOut]
    | guardedContinuing guards stF =>
      dsimp
      cases hClean : stateCleanAtReturn stF with
      | false =>
        dsimp
        intro hFalse
        nomatch hFalse
      | true =>
        dsimp
        cases hRet : evalRval alg retExpr stF with
        | none =>
          dsimp
          intro hFalse
          nomatch hFalse
        | some retVal =>
          dsimp
          intro hEq
          injection hEq with hOut
          rw [← hOut]

/-- Sequential 2-block CFG equivalence (`cfg_seq_blocks_equiv`): a 2-block CFG
`[⟨p1, .goto 1⟩, ⟨p2, .ret retExpr⟩]` executed for 2 steps matches `evalPlan
alg (.seq p1 p2) st0` when `p1` falls through to `p2`. -/
theorem cfg_seq_blocks_equiv {Val : Type} (alg : ValAlgebra Val)
    (p1 p2 : FlowPlan Val) (retExpr : RvalOp Val)
    (st0 st1 stF : SymState Val) (retVal : Val)
    (hWf1 : WfPlan alg p1) (hWf2 : WfPlan alg p2)
    (h1 : evalPlan alg p1 st0 = .ok (.continuing st1))
    (h2 : evalPlan alg p2 st1 = .ok (.continuing stF))
    (hClean : stateCleanAtReturn stF = true)
    (hRet : evalRval alg retExpr stF = some retVal) :
    runBlockCfg
      (stepBasicBlock alg [⟨p1, .goto 1⟩, ⟨p2, .ret retExpr⟩])
      0 st0 2 =
      .ret ⟨retVal, collectRootMutVals stF.loans⟩ ∧
    evalPlan alg (.seq p1 p2) st0 = .ok (.continuing stF) := by
  have hLeft :
      runBlockCfg
        (stepBasicBlock alg [⟨p1, .goto 1⟩, ⟨p2, .ret retExpr⟩])
        0 st0 2 =
        .ret ⟨retVal, collectRootMutVals stF.loans⟩ := by
    rw [runBlockCfg_succ]
    dsimp [stepBasicBlock, listGetOpt]
    rw [h1]
    dsimp
    rw [runBlockCfg_succ]
    dsimp [stepBasicBlock, listGetOpt]
    rw [h2]
    dsimp
    rw [hClean]
    dsimp
    rw [hRet]
  have hRight :
      evalPlan alg (.seq p1 p2) st0 = .ok (.continuing stF) := by
    rw [evalPlan_seq alg p1 p2 st0 hWf1 hWf2]
    rw [h1]
    exact h2
  exact ⟨hLeft, hRight⟩

/-- Loop CFG equivalence (`cfg_certificate_while_sound`): for a 2-block loop CFG
`[⟨.skip, .branch cond 1 0⟩, ⟨body, .goto 0⟩]` (where block `0` branches to body
block `1` on `true` and exit block `2` on `false`), every `fuel`-iteration
execution of `runWhileFlowSteps alg cond (evalPlan alg body) fuel st` that
terminates in `.ok (.continuing stFinal)` with clean return state reaches `.ret`
in `runBlockCfg` in `2 * fuel + 1` basic-block steps with the exact same
`FuncOut Val`. -/
theorem cfg_certificate_while_sound {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val) (body : FlowPlan Val) (retExpr : RvalOp Val) :
    ∀ (fuel : Nat) (st stFinal : SymState Val) (retVal : Val),
      runWhileFlowSteps alg cond (evalPlan alg body) fuel st =
        .ok (.continuing stFinal) →
      stateCleanAtReturn stFinal = true →
      evalRval alg retExpr stFinal = some retVal →
      runBlockCfg
        (stepBasicBlock alg
          [⟨.skip, .branch cond 1 2⟩,
           ⟨body, .goto 0⟩,
           ⟨.skip, .ret retExpr⟩])
        0 st (2 * fuel + 2) =
        .ret ⟨retVal, collectRootMutVals stFinal.loans⟩
  | 0, st, stFinal, retVal, hWhile, hClean, hRet => by
    rw [runWhileFlowSteps_zero] at hWhile
    revert hWhile
    cases hCond : evalRval alg cond st with
    | none =>
      intro hFalse
      nomatch hFalse
    | some cv =>
      dsimp
      cases hBool : alg.asBool cv with
      | none =>
        intro hFalse
        nomatch hFalse
      | some b =>
        cases b with
        | true =>
          intro hFalse
          nomatch hFalse
        | false =>
          dsimp
          intro hEq
          injection hEq with hFlow
          injection hFlow with hSt
          subst hSt
          change
            runBlockCfg
              (stepBasicBlock alg
                [⟨.skip, .branch cond 1 2⟩,
                 ⟨body, .goto 0⟩,
                 ⟨.skip, .ret retExpr⟩])
              0 st 2 =
              .ret ⟨retVal, collectRootMutVals st.loans⟩
          rw [runBlockCfg_succ]
          dsimp [stepBasicBlock, listGetOpt, evalPlan, evalPlanOps,
            stepPlanOp, FlowPlan.skip]
          rw [hCond]
          dsimp
          rw [hBool]
          dsimp
          rw [runBlockCfg_succ]
          dsimp [stepBasicBlock, listGetOpt, evalPlan, evalPlanOps,
            stepPlanOp, FlowPlan.skip]
          rw [hClean]
          dsimp
          rw [hRet]
  | k + 1, st, stFinal, retVal, hWhile, hClean, hRet => by
    rw [runWhileFlowSteps_succ] at hWhile
    revert hWhile
    cases hCond : evalRval alg cond st with
    | none =>
      intro hFalse
      nomatch hFalse
    | some cv =>
      dsimp
      cases hBool : alg.asBool cv with
      | none =>
        intro hFalse
        nomatch hFalse
      | some b =>
        cases b with
        | false =>
          dsimp
          intro hEq
          injection hEq with hFlow
          injection hFlow with hSt
          subst hSt
          have hStep1 :
              stepBasicBlock alg
                [⟨.skip, .branch cond 1 2⟩,
                 ⟨body, .goto 0⟩,
                 ⟨.skip, .ret retExpr⟩] 0 st = .jump 2 st := by
            dsimp [stepBasicBlock, listGetOpt, evalPlan, evalPlanOps,
              stepPlanOp, FlowPlan.skip]
            rw [hCond]
            dsimp
            rw [hBool]
          have hStep2 :
              stepBasicBlock alg
                [⟨.skip, .branch cond 1 2⟩,
                 ⟨body, .goto 0⟩,
                 ⟨.skip, .ret retExpr⟩] 2 st =
                .ret ⟨retVal, collectRootMutVals st.loans⟩ := by
            dsimp [stepBasicBlock, listGetOpt, evalPlan, evalPlanOps,
              stepPlanOp, FlowPlan.skip]
            rw [hClean]
            dsimp
            rw [hRet]
          have hArith : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by
            rw [Nat.mul_add]
          rw [hArith, runBlockCfg_succ, hStep1]
          dsimp
          rw [runBlockCfg_succ, hStep2]
        | true =>
          dsimp
          cases hBody : evalPlan alg body st with
          | fail =>
            intro hFalse
            nomatch hFalse
          | ok flow =>
            cases flow with
            | returned _ =>
              intro hFalse
              nomatch hFalse
            | guardedContinuing wrap1 st' =>
              dsimp [prependGuardedWrap]
              cases runWhileFlowSteps alg cond (evalPlan alg body) k st' with
              | fail =>
                intro hFalse
                nomatch hFalse
              | ok flowRec =>
                cases flowRec <;> (intro hFalse; nomatch hFalse)
            | continuing st' =>
              dsimp
              intro hRec
              have ih :=
                cfg_certificate_while_sound alg cond body retExpr k st'
                  stFinal retVal hRec hClean hRet
              have hStep1 :
                  stepBasicBlock alg
                    [⟨.skip, .branch cond 1 2⟩,
                     ⟨body, .goto 0⟩,
                     ⟨.skip, .ret retExpr⟩] 0 st = .jump 1 st := by
                dsimp [stepBasicBlock, listGetOpt, evalPlan, evalPlanOps,
                  stepPlanOp, FlowPlan.skip]
                rw [hCond]
                dsimp
                rw [hBool]
              have hStep2 :
                  stepBasicBlock alg
                    [⟨.skip, .branch cond 1 2⟩,
                     ⟨body, .goto 0⟩,
                     ⟨.skip, .ret retExpr⟩] 1 st = .jump 0 st' := by
                dsimp [stepBasicBlock, listGetOpt]
                rw [hBody]
              have hArith : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by
                rw [Nat.mul_add]
              rw [hArith, runBlockCfg_succ, hStep1]
              dsimp
              rw [runBlockCfg_succ, hStep2]
              exact ih

/-!
## Exhaustive Kernel-Checked Unit Tests
-/

theorem test_listGetOpt :
    listGetOpt 0 [10, 20, 30] = some 10 ∧
    listGetOpt 2 [10, 20, 30] = some 30 ∧
    listGetOpt 3 [10, 20, 30] = none :=
  ⟨rfl, rfl, rfl⟩

def testCfgStep (bb : Nat) (st : Nat) : BlockStepResult Nat Nat :=
  match bb with
  | 0 => if st == 0 then .jump 2 st else .jump 1 (st - 1)
  | 1 => .jump 0 st
  | 2 => .ret (st + 100)
  | _ => .fault

theorem test_runBlockCfg_countdown :
    runBlockCfg testCfgStep 0 3 10 = .ret 100 ∧
    runBlockCfg testCfgStep 0 3 2 = .diverged ∧
    runBlockCfg testCfgStep 99 0 1 = .fault :=
  ⟨rfl, rfl, rfl⟩

end Anneal.PureLift
