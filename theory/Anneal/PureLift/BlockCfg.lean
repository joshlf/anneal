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
           | .ok (.returned out c m) => .ok (.returned out c m)
           | .ok (.guardedContinuing wrap1 s' c1 wrapMut1) =>
             prependGuardedWrap wrap1 c1 wrapMut1
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
  | jumpWrapped (wrapRet : Ret → Ret) (nextBb : Nat) (st' : State)
  | branchJump (mergeRet : Ret → Ret → Ret) (thenBb elseBb : Nat)
      (st' : State)
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
    | .ok (.returned out valClean _) =>
      if !valClean || !handleFreeOut alg out then .fault else .ret out
    | .ok (.guardedContinuing wrapOut st' valClean _) =>
      if !valClean then .fault
      else
        match bb.term with
        | .goto tgt => .jumpWrapped wrapOut tgt st'
        | .branch cond tTgt fTgt =>
          match evalRval alg cond st' with
          | some cv =>
            match alg.asBool cv with
            | some true => .jumpWrapped wrapOut tTgt st'
            | some false => .jumpWrapped wrapOut fTgt st'
            | none =>
              -- Both successors coincide: run the target once instead of
              -- evaluating it twice and merging identical results.
              if tTgt == fTgt then .jumpWrapped wrapOut tTgt st'
              else
                .branchJump
                  (fun tOut fOut => wrapOut (mergeFuncOut alg cv tOut fOut))
                  tTgt fTgt st'
          | none => .fault
        | .ret retExpr =>
          if !stateCleanAtReturn st' then .fault
          else
            match evalRval alg retExpr st' with
            | some rv =>
              let out := wrapOut ⟨rv, collectRootMutVals st'.loans⟩
              if !handleFreeOut alg out then .fault else .ret out
            | none => .fault
    | .ok (.continuing st') =>
      match bb.term with
      | .goto tgt => .jump tgt st'
      | .branch cond tTgt fTgt =>
        match evalRval alg cond st' with
        | some cv =>
          match alg.asBool cv with
          | some true => .jump tTgt st'
          | some false => .jump fTgt st'
          | none =>
            if tTgt == fTgt then .jump tTgt st'
            else .branchJump (mergeFuncOut alg cv) tTgt fTgt st'
        | none => .fault
      | .ret retExpr =>
        if !stateCleanAtReturn st' then .fault
        else
          match evalRval alg retExpr st' with
          | some rv =>
            let out : FuncOut Val := ⟨rv, collectRootMutVals st'.loans⟩
            if !handleFreeOut alg out then .fault else .ret out
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
      | .jump nextBb st' => ih nextBb st'
      | .jumpWrapped wrapRet nextBb st' =>
        match ih nextBb st' with
        | .ret v => .ret (wrapRet v)
        | .diverged => .diverged
        | .fault => .fault
      | .branchJump mergeRet thenBb elseBb st' =>
        match ih thenBb st', ih elseBb st' with
        | .ret vt, .ret vf => .ret (mergeRet vt vf)
        | .fault, _ => .fault
        | _, .fault => .fault
        | _, _ => .diverged)
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
    | .jumpWrapped wrapRet nextBb st' =>
      BlockInv nextBb st' ∧ (∀ v, PostRet v → PostRet (wrapRet v))
    | .branchJump mergeRet thenBb elseBb st' =>
      BlockInv thenBb st' ∧ BlockInv elseBb st' ∧
      (∀ vt vf, PostRet vt → PostRet vf → PostRet (mergeRet vt vf))

theorem runBlockCfg_succ {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (bb : Nat) (st : State) (fuel' : Nat) :
    runBlockCfg stepBb bb st (fuel' + 1) =
      (match stepBb bb st with
       | .fault => .fault
       | .ret v => .ret v
       | .jump nextBb st' => runBlockCfg stepBb nextBb st' fuel'
       | .jumpWrapped wrapRet nextBb st' =>
         match runBlockCfg stepBb nextBb st' fuel' with
         | .ret v => .ret (wrapRet v)
         | .diverged => .diverged
         | .fault => .fault
       | .branchJump mergeRet thenBb elseBb st' =>
         match runBlockCfg stepBb thenBb st' fuel',
               runBlockCfg stepBb elseBb st' fuel' with
         | .ret vt, .ret vf => .ret (mergeRet vt vf)
         | .fault, _ => .fault
         | _, .fault => .fault
         | _, _ => .diverged) := rfl

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
    | jumpWrapped wrapRet nextBb st' =>
      rw [hStep] at hVC
      dsimp at hVC
      dsimp [BlockCfgPartialSpec]
      have ih :=
        modular_block_cfg_sound stepBb BlockInv PostRet hLocal
          fuel' nextBb st' hVC.1
      cases hRun : runBlockCfg stepBb nextBb st' fuel' with
      | ret v =>
        rw [hRun] at ih
        dsimp [BlockCfgPartialSpec] at ih
        dsimp
        exact hVC.2 v ih
      | diverged =>
        exact True.intro
      | fault =>
        rw [hRun] at ih
        nomatch ih
    | branchJump mergeRet thenBb elseBb st' =>
      rw [hStep] at hVC
      dsimp at hVC
      dsimp [BlockCfgPartialSpec]
      have ihT :=
        modular_block_cfg_sound stepBb BlockInv PostRet hLocal
          fuel' thenBb st' hVC.1
      have ihF :=
        modular_block_cfg_sound stepBb BlockInv PostRet hLocal
          fuel' elseBb st' hVC.2.1
      cases hRunT : runBlockCfg stepBb thenBb st' fuel' with
      | fault =>
        rw [hRunT] at ihT
        nomatch ihT
      | diverged =>
        cases hRunF : runBlockCfg stepBb elseBb st' fuel' with
        | fault =>
          rw [hRunF] at ihF
          nomatch ihF
        | diverged =>
          exact True.intro
        | ret _ =>
          exact True.intro
      | ret vt =>
        cases hRunF : runBlockCfg stepBb elseBb st' fuel' with
        | fault =>
          rw [hRunF] at ihF
          nomatch ihF
        | diverged =>
          exact True.intro
        | ret vf =>
          rw [hRunT] at ihT
          rw [hRunF] at ihF
          dsimp [BlockCfgPartialSpec] at ihT ihF
          dsimp
          exact hVC.2.2 vt vf ihT ihF

/-!
## CFG-to-`FlowPlan` Equivalence Certificates (`CfgCertificate`)
-/

/-- Certificate pairing a block-indexed CFG (`blocks`, `entryBb`, `fuel`) with
a structured `FlowPlan Val` and return expression `retExpr`, together with the
evidence `sound` that relates their executions: whenever the structured plan
returns `out` from an entry state, the CFG run for `fuel` block steps from the
same entry state returns the same `out`. Possessing a `CfgCertificate` thus
certifies the CFG-to-plan correspondence; it cannot be built for an unrelated
CFG and plan without proving `sound`. -/
structure CfgCertificate {Val : Type} (alg : ValAlgebra Val) where
  blocks : List (BasicBlock Val)
  entryBb : BlockId
  fuel : Nat
  plan : FlowPlan Val
  retExpr : RvalOp Val
  sound :
    ∀ (params : List (ParamInput Val)) (st0 : SymState Val)
      (out : FuncOut Val),
      initFnState alg params = .ok st0 →
      evalFnValue alg params plan retExpr = .ok out →
      runBlockCfg (stepBasicBlock alg blocks) entryBb st0 fuel = .ret out

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
    | returned out' valClean _ =>
      dsimp
      cases valClean with
      | false =>
        dsimp
        intro hFalse
        nomatch hFalse
      | true =>
        cases handleFreeOut alg out' with
        | false =>
          dsimp
          intro hFalse
          nomatch hFalse
        | true =>
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
          cases handleFreeOut alg ⟨retVal, collectRootMutVals stF.loans⟩ with
          | false =>
            dsimp
            intro hFalse
            nomatch hFalse
          | true =>
            dsimp
            intro hEq
            injection hEq with hOut
            rw [← hOut]
    | guardedContinuing guards stF valClean _ =>
      dsimp
      cases valClean with
      | false =>
        dsimp
        intro hFalse
        nomatch hFalse
      | true =>
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
            cases handleFreeOut alg
                (guards ⟨retVal, collectRootMutVals stF.loans⟩) with
            | false =>
              dsimp
              intro hFalse
              nomatch hFalse
            | true =>
              dsimp
              intro hEq
              injection hEq with hOut
              rw [← hOut]

/-- Converse of `cfg_certificate_step_sound`: any `.ret out` of the 1-block CFG
`[⟨plan, .ret retExpr⟩]` comes from `evalFnValue alg params plan retExpr = .ok
out`, because `stepBasicBlock` enforces the same `valClean`, `stateCleanAtReturn`,
and `handleFreeOut` checks at return as `evalFnValue`. -/
theorem cfg_certificate_step_complete {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retExpr : RvalOp Val) (st0 : SymState Val) (out : FuncOut Val)
    (hInit : initFnState alg params = .ok st0)
    (hRun :
      runBlockCfg (stepBasicBlock alg [⟨plan, .ret retExpr⟩]) 0 st0 1 =
        .ret out) :
    evalFnValue alg params plan retExpr = .ok out := by
  dsimp [evalFnValue]
  rw [hInit]
  dsimp
  rw [runBlockCfg_succ] at hRun
  dsimp [stepBasicBlock, listGetOpt] at hRun
  revert hRun
  cases hPlan : evalPlan alg plan st0 with
  | fail =>
    intro hFalse
    nomatch hFalse
  | ok flow =>
    cases flow with
    | returned out' valClean _ =>
      dsimp
      cases valClean with
      | false =>
        dsimp
        intro hFalse
        nomatch hFalse
      | true =>
        cases handleFreeOut alg out' with
        | false =>
          dsimp
          intro hFalse
          nomatch hFalse
        | true =>
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
          cases handleFreeOut alg ⟨retVal, collectRootMutVals stF.loans⟩ with
          | false =>
            dsimp
            intro hFalse
            nomatch hFalse
          | true =>
            dsimp
            intro hEq
            injection hEq with hOut
            rw [← hOut]
    | guardedContinuing guards stF valClean _ =>
      dsimp
      cases valClean with
      | false =>
        dsimp
        intro hFalse
        nomatch hFalse
      | true =>
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
            cases handleFreeOut alg
                (guards ⟨retVal, collectRootMutVals stF.loans⟩) with
            | false =>
              dsimp
              intro hFalse
              nomatch hFalse
            | true =>
              dsimp
              intro hEq
              injection hEq with hOut
              rw [← hOut]

/-- Bidirectional single-block CFG equivalence (`cfg_certificate_step_iff`):
from initialized state `st0`, the 1-block CFG `[⟨plan, .ret retExpr⟩]` returns
`out` in 1 step iff `evalFnValue alg params plan retExpr = .ok out`. -/
theorem cfg_certificate_step_iff {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retExpr : RvalOp Val) (st0 : SymState Val) (out : FuncOut Val)
    (hInit : initFnState alg params = .ok st0) :
    runBlockCfg (stepBasicBlock alg [⟨plan, .ret retExpr⟩]) 0 st0 1 = .ret out ↔
      evalFnValue alg params plan retExpr = .ok out :=
  ⟨cfg_certificate_step_complete alg params plan retExpr st0 out hInit,
   cfg_certificate_step_sound alg params plan retExpr st0 out hInit⟩

/-- Single-block `CfgCertificate`: the 1-block CFG `[⟨plan, .ret retExpr⟩]`
run for one step, certified by `cfg_certificate_step_sound`. -/
def CfgCertificate.singleBlock {Val : Type} (alg : ValAlgebra Val)
    (plan : FlowPlan Val) (retExpr : RvalOp Val) : CfgCertificate alg where
  blocks := [⟨plan, .ret retExpr⟩]
  entryBb := 0
  fuel := 1
  plan := plan
  retExpr := retExpr
  sound := fun params st0 out hInit hEval =>
    cfg_certificate_step_sound alg params plan retExpr st0 out hInit hEval

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
    (hRet : evalRval alg retExpr stF = some retVal)
    (hFree :
      handleFreeOut alg ⟨retVal, collectRootMutVals stF.loans⟩ = true) :
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
    dsimp
    rw [hFree]
    rfl
  have hRight :
      evalPlan alg (.seq p1 p2) st0 = .ok (.continuing stF) := by
    rw [evalPlan_seq alg p1 p2 st0 hWf1 hWf2]
    rw [h1]
    exact h2
  exact ⟨hLeft, hRight⟩

/-- Loop CFG equivalence (`cfg_certificate_while_sound`): for the 3-block loop
CFG `[⟨.skip, .branch cond 1 2⟩, ⟨body, .goto 0⟩, ⟨.skip, .ret retExpr⟩]`
(block `0` branches to body block `1` on `true` and to exit block `2` on
`false`), every execution of `runWhileFlowSteps alg cond (evalPlan alg body)
fuel st` that terminates in `.ok (.continuing stFinal)` with a clean,
handle-free return state reaches `.ret` in `runBlockCfg` within `2 * fuel + 2`
basic-block steps with the same `FuncOut Val`. -/
theorem cfg_certificate_while_sound {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val) (body : FlowPlan Val) (retExpr : RvalOp Val) :
    ∀ (fuel : Nat) (st stFinal : SymState Val) (retVal : Val),
      runWhileFlowSteps alg cond (evalPlan alg body) fuel st =
        .ok (.continuing stFinal) →
      stateCleanAtReturn stFinal = true →
      evalRval alg retExpr stFinal = some retVal →
      handleFreeOut alg ⟨retVal, collectRootMutVals stFinal.loans⟩ = true →
      runBlockCfg
        (stepBasicBlock alg
          [⟨.skip, .branch cond 1 2⟩,
           ⟨body, .goto 0⟩,
           ⟨.skip, .ret retExpr⟩])
        0 st (2 * fuel + 2) =
        .ret ⟨retVal, collectRootMutVals stFinal.loans⟩
  | 0, st, stFinal, retVal, hWhile, hClean, hRet, hFree => by
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
          dsimp
          rw [hFree]
          rfl
  | k + 1, st, stFinal, retVal, hWhile, hClean, hRet, hFree => by
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
            dsimp
            rw [hFree]
            rfl
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
            | returned _ _ _ =>
              intro hFalse
              nomatch hFalse
            | guardedContinuing wrap1 st' c1 wrapMut1 =>
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
                  stFinal retVal hRec hClean hRet hFree
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

/-- Exhaustive Round-6 unit tests for `stepBasicBlock` and `runBlockCfg` across
`.jumpWrapped` (when `evalPlan` returns `.guardedContinuing` before a `.goto` or
`.branch` terminator) and `.branchJump` (when a `.branch` terminator has a
symbolic condition `alg.asBool cv = none`). -/
theorem test_blockCfg_jumpWrapped_and_symbolic_branchJump :
    let guardedGotoBlocks : List (BasicBlock LensTestVal) :=
      [ ⟨.branch (.use (.localSub 0 []))
           (.earlyReturn [] [] (.constVal (.atom 10)))
           (.act (.assign (.localSub 1 []) (.constVal (.atom 20)))),
         .goto 1⟩
      , ⟨.act (.assign (.localSub 1 []) (.constVal (.atom 30))),
         .ret (.use (.localSub 1 []))⟩ ]
    let symBranchBlocks : List (BasicBlock LensTestVal) :=
      [ ⟨.skip, .branch (.use (.localSub 0 [])) 1 2⟩
      , ⟨.act (.assign (.localSub 1 []) (.constVal (.atom 111))),
         .ret (.use (.localSub 1 []))⟩
      , ⟨.act (.assign (.localSub 1 []) (.constVal (.atom 222))),
         .ret (.use (.localSub 1 []))⟩ ]
    (match initFnState lensTestValAlg [⟨.byVal, .node (.atom 1) (.atom 0)⟩] with
     | .ok stSym =>
       runBlockCfg (stepBasicBlock lensTestValAlg guardedGotoBlocks) 0 stSym 3 =
         .ret
           ⟨lensTestValAlg.zipVal (.node (.atom 1) (.atom 0))
              (.atom 10) (.atom 30), []⟩ ∧
       runBlockCfg (stepBasicBlock lensTestValAlg symBranchBlocks) 0 stSym 3 =
         .ret
           ⟨lensTestValAlg.zipVal (.node (.atom 1) (.atom 0))
              (.atom 111) (.atom 222), []⟩
     | .fail => False) :=
  ⟨rfl, rfl⟩

end Anneal.PureLift
