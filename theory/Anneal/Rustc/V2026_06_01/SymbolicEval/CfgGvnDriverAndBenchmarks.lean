import Anneal.Rustc.V2026_06_01.SymbolicEval.MirCfgAndJoinPruning

namespace Anneal.Rustc.V2026_06_01.SymbolicEval

open Trusted.Refinement
open Trusted.Sequence
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Scalars
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower

/-!
Single-continuation symbolic CFG evaluator (`symEvalCfgGvn`) with end-to-end soundness and
kernel-checked `k`-diamond multi-block CFG benchmarks (sections 3.5-3.6).
-/

/-!
### 3.5 Single-Continuation Symbolic CFG Evaluator (`symEvalCfgGvn`) & End-to-End Soundness
-/

/-- Constant-folded branch condition: `some b` iff `condId` is interned as a constant. -/
def constCond? (tbl : SymTable) (condId : SymId) : Option Bool :=
  match tbl.nodes[condId]? with
  | some (.const v) => some (wrap64 v != 0)
  | _ => none

theorem constCond?_sound {tbl : SymTable} {condId : SymId} {b : Bool} (hValid : ValidTable tbl)
    (h : constCond? tbl condId = some b) (env : SymEnv) :
    (evalSymId tbl env condId != 0) = b := by
  unfold constCond? at h
  split at h
  · rename_i v hNode
    injection h with hb
    subst hb
    rw [evalSymId_eq_evalSymNodeWith hValid env hNode]
    rfl
  · cases h

/-- Combine the explorations of both successors of a *path-split* (non-merged) `switchInt`,
    threading the append-only table from the `then` exploration into the `else` one. -/
def combineSplit (resT : Option (List SymId × SymTable))
    (resF : SymTable → Option (List SymId × SymTable)) : Option (List SymId × SymTable) :=
  match resT with
  | none => none
  | some (retsT, tblT) =>
    match resF tblT with
    | none => none
    | some (retsF, tblF) => some (retsT ++ retsF, tblF)

theorem combineSplit_eq_some {resT : Option (List SymId × SymTable)}
    {resF : SymTable → Option (List SymId × SymTable)} {rets : List SymId} {tbl' : SymTable}
    (h : combineSplit resT resF = some (rets, tbl')) :
    ∃ retsT tblT retsF, resT = some (retsT, tblT) ∧ resF tblT = some (retsF, tbl') ∧
      rets = retsT ++ retsF := by
  unfold combineSplit at h
  cases hT : resT with
  | none => rw [hT] at h; cases h
  | some pT =>
    rcases pT with ⟨retsT, tblT⟩
    rw [hT] at h
    dsimp only at h
    cases hF : resF tblT with
    | none => rw [hF] at h; cases h
    | some pF =>
      rcases pF with ⟨retsF, tblF⟩
      rw [hF] at h
      dsimp only at h
      injection h with h1
      injection h1 with hR hTb
      subst hR hTb
      exact ⟨retsT, tblT, retsF, rfl, hF, rfl⟩

/-- One spare unit of fuel never changes a **returning** mask-free concrete execution (fuel only
    bounds the number of executed blocks). Used for the direct side of a merged triangle, whose
    concrete path reaches the join one block earlier than the arm side. -/
theorem execCfg_ret_succ (cfg : MirCfg) :
    ∀ (fuel : Nat) (bb : BlockId) (st : CanonState Nat) (v : Nat),
      execCfg cfg fuel bb st = .ret v → execCfg cfg (fuel + 1) bb st = .ret v
  | 0, _, _, _, h => by cases h
  | fuel + 1, bb, st, v, h => by
    rw [execCfg] at h ⊢
    cases hBlk : cfg.blocks[bb]? with
    | none => rw [hBlk] at h; cases h
    | some blk =>
      rw [hBlk] at h
      dsimp only at h ⊢
      cases hS : execStmts st blk.stmts with
      | none => rw [hS] at h; cases h
      | some st₁ =>
        rw [hS] at h
        dsimp only at h ⊢
        cases hT : blk.term with
        | goto t =>
          rw [hT] at h
          exact execCfg_ret_succ cfg fuel t st₁ v h
        | switchInt d t e =>
          rw [hT] at h
          dsimp only at h ⊢
          cases hR : readConcreteScalar st₁ d with
          | none => rw [hR] at h; cases h
          | some w =>
            rw [hR] at h
            dsimp only at h ⊢
            cases hW : (w != 0) with
            | true =>
              rw [hW, ite_eq_left rfl] at h
              rw [ite_eq_left rfl]
              exact execCfg_ret_succ cfg fuel t _ v h
            | false =>
              rw [hW, ite_eq_right Bool.false_ne_true] at h
              rw [ite_eq_right Bool.false_ne_true]
              exact execCfg_ret_succ cfg fuel e _ v h
        | switchTable d cases otherwiseBb =>
          rw [hT] at h
          dsimp only at h ⊢
          cases hR : readConcreteScalar st₁ d with
          | none => rw [hR] at h; cases h
          | some w =>
            rw [hR] at h
            exact execCfg_ret_succ cfg fuel (lookupCfgSwitchTarget w cases otherwiseBb) _ v h
        | ret r =>
          rw [hT] at h
          exact h
        | unreachable =>
          rw [hT] at h
          cases h

/-- Extract the arm statements for a list of `(caseVal, armBb)` pairs that all end in
    `goto joinBb`. -/
def matchSwitchCases (cfg : MirCfg) (joinBb : BlockId) :
    List (Nat × BlockId) → Option (List (Nat × List MirStmt))
  | [] => some []
  | (val, bb) :: rest =>
    match cfg.blocks[bb]?, matchSwitchCases cfg joinBb rest with
    | some blk, some restArms =>
      match armGoto? blk with
      | some j => if j = joinBb then some ((val, blk.stmts) :: restArms) else none
      | none => none
    | _, _ => none

/-- Recognize an N-way `switchTable` diamond: `otherwiseBb` and every target in `cases` are arm
    blocks ending in `goto` the same hinted `joinBb`. -/
def switchTableMergePlan (cfg : MirCfg) (hints : JoinHints)
    (cases : List (Nat × BlockId)) (otherwiseBb : BlockId) :
    Option (List (Nat × List MirStmt) × List MirStmt × BlockId × List Bool) :=
  match cfg.blocks[otherwiseBb]? with
  | some oBlk =>
    match armGoto? oBlk with
    | some joinBb =>
      match hints joinBb, matchSwitchCases cfg joinBb cases with
      | some mask, some caseArms => some (caseArms, oBlk.stmts, joinBb, mask)
      | _, _ => none
    | none => none
  | none => none

theorem switchTableMergePlan_spec {cfg : MirCfg} {hints : JoinHints}
    {cases : List (Nat × BlockId)} {otherwiseBb joinBb : BlockId}
    {caseArms : List (Nat × List MirStmt)} {otherwiseStmts : List MirStmt} {mask : List Bool}
    (h : switchTableMergePlan cfg hints cases otherwiseBb =
      some (caseArms, otherwiseStmts, joinBb, mask)) :
    ∃ oBlk, cfg.blocks[otherwiseBb]? = some oBlk ∧ oBlk.stmts = otherwiseStmts ∧
      oBlk.term = .goto joinBb ∧ matchSwitchCases cfg joinBb cases = some caseArms := by
  unfold switchTableMergePlan at h
  split at h
  · rename_i oBlk hO
    split at h
    · rename_i j hj
      split at h
      · rename_i m cArms hM hCA
        injection h with h1
        injection h1 with hCAEq h2
        injection h2 with hOSEq h3
        injection h3 with hJEq _
        subst hCAEq hOSEq hJEq
        exact ⟨oBlk, hO, rfl, armGoto?_spec hj, hCA⟩
      · cases h
    · cases h
  · cases h

/-- Extract the arm statements for a list of `(caseVal, armBb)` pairs in an N-way `switchTable`
    triangle: each `armBb` may either jump **directly** to `joinBb` (`armBb = joinBb`, contributing
    `[]` arm statements) or be an arm block ending in `goto joinBb` (`armGoto? blk = some joinBb`,
    contributing `blk.stmts`). -/
def matchSwitchTriangleCases (cfg : MirCfg) (joinBb : BlockId) :
    List (Nat × BlockId) → Option (List (Nat × List MirStmt))
  | [] => some []
  | (val, bb) :: rest =>
    if bb = joinBb then
      match matchSwitchTriangleCases cfg joinBb rest with
      | some restArms => some ((val, []) :: restArms)
      | none => none
    else
      match cfg.blocks[bb]?, matchSwitchTriangleCases cfg joinBb rest with
      | some blk, some restArms =>
        match armGoto? blk with
        | some j => if j = joinBb then some ((val, blk.stmts) :: restArms) else none
        | none => none
      | _, _ => none

/-- N-way `switchTable` triangle plan where `otherwiseBb` **is** the hinted `joinBb` (`otherwiseStmts = []`). -/
def switchTableDirectOtherwisePlan (cfg : MirCfg) (hints : JoinHints)
    (cases : List (Nat × BlockId)) (otherwiseBb : BlockId) :
    Option (List (Nat × List MirStmt) × List MirStmt × BlockId × List Bool) :=
  match hints otherwiseBb, matchSwitchTriangleCases cfg otherwiseBb cases with
  | some mask, some caseArms => some (caseArms, [], otherwiseBb, mask)
  | _, _ => none

/-- N-way `switchTable` triangle plan where `otherwiseBb` is an arm block ending in `goto joinBb`,
    and one or more case targets in `cases` jump directly to `joinBb`. -/
def switchTableArmOtherwiseTrianglePlan (cfg : MirCfg) (hints : JoinHints)
    (cases : List (Nat × BlockId)) (otherwiseBb : BlockId) :
    Option (List (Nat × List MirStmt) × List MirStmt × BlockId × List Bool) :=
  match cfg.blocks[otherwiseBb]? with
  | some oBlk =>
    match armGoto? oBlk with
    | some joinBb =>
      match hints joinBb, matchSwitchTriangleCases cfg joinBb cases with
      | some mask, some caseArms => some (caseArms, oBlk.stmts, joinBb, mask)
      | _, _ => none
    | none => none
  | none => none

/-- Combined N-way `switchTable` triangle merge plan: handles both `otherwiseBb = joinBb` and
    arm-block `otherwiseBb -> joinBb` when any subset of `cases` jumps directly to `joinBb`. -/
def switchTableTrianglePlan (cfg : MirCfg) (hints : JoinHints)
    (cases : List (Nat × BlockId)) (otherwiseBb : BlockId) :
    Option (List (Nat × List MirStmt) × List MirStmt × BlockId × List Bool) :=
  match switchTableDirectOtherwisePlan cfg hints cases otherwiseBb with
  | some plan => some plan
  | none => switchTableArmOtherwiseTrianglePlan cfg hints cases otherwiseBb

theorem switchTableDirectOtherwisePlan_spec {cfg : MirCfg} {hints : JoinHints}
    {cases : List (Nat × BlockId)} {otherwiseBb joinBb : BlockId}
    {caseArms : List (Nat × List MirStmt)} {otherwiseStmts : List MirStmt} {mask : List Bool}
    (h : switchTableDirectOtherwisePlan cfg hints cases otherwiseBb =
      some (caseArms, otherwiseStmts, joinBb, mask)) :
    otherwiseBb = joinBb ∧ otherwiseStmts = [] ∧
      matchSwitchTriangleCases cfg joinBb cases = some caseArms := by
  unfold switchTableDirectOtherwisePlan at h
  split at h
  · rename_i m cArms hM hCA
    injection h with h1
    injection h1 with hCAEq h2
    injection h2 with hOSEq h3
    injection h3 with hJEq _
    subst hCAEq hOSEq hJEq
    exact ⟨rfl, rfl, hCA⟩
  · cases h

theorem switchTableArmOtherwiseTrianglePlan_spec {cfg : MirCfg} {hints : JoinHints}
    {cases : List (Nat × BlockId)} {otherwiseBb joinBb : BlockId}
    {caseArms : List (Nat × List MirStmt)} {otherwiseStmts : List MirStmt} {mask : List Bool}
    (h : switchTableArmOtherwiseTrianglePlan cfg hints cases otherwiseBb =
      some (caseArms, otherwiseStmts, joinBb, mask)) :
    ∃ oBlk, cfg.blocks[otherwiseBb]? = some oBlk ∧ oBlk.stmts = otherwiseStmts ∧
      oBlk.term = .goto joinBb ∧ matchSwitchTriangleCases cfg joinBb cases = some caseArms := by
  unfold switchTableArmOtherwiseTrianglePlan at h
  split at h
  · rename_i oBlk hO
    split at h
    · rename_i j hj
      split at h
      · rename_i m cArms hM hCA
        injection h with h1
        injection h1 with hCAEq h2
        injection h2 with hOSEq h3
        injection h3 with hJEq _
        subst hCAEq hOSEq hJEq
        exact ⟨oBlk, hO, rfl, armGoto?_spec hj, hCA⟩
      · cases h
    · cases h
  · cases h

theorem switchTableTrianglePlan_spec {cfg : MirCfg} {hints : JoinHints}
    {cases : List (Nat × BlockId)} {otherwiseBb joinBb : BlockId}
    {caseArms : List (Nat × List MirStmt)} {otherwiseStmts : List MirStmt} {mask : List Bool}
    (h : switchTableTrianglePlan cfg hints cases otherwiseBb =
      some (caseArms, otherwiseStmts, joinBb, mask)) :
    ((otherwiseBb = joinBb ∧ otherwiseStmts = []) ∨
      (∃ oBlk, cfg.blocks[otherwiseBb]? = some oBlk ∧ oBlk.stmts = otherwiseStmts ∧
        oBlk.term = .goto joinBb)) ∧
      matchSwitchTriangleCases cfg joinBb cases = some caseArms := by
  unfold switchTableTrianglePlan at h
  cases hD : switchTableDirectOtherwisePlan cfg hints cases otherwiseBb with
  | some p =>
    rw [hD] at h
    injection h with hEq
    subst hEq
    rcases switchTableDirectOtherwisePlan_spec hD with ⟨hOB, hOS, hCA⟩
    exact ⟨Or.inl ⟨hOB, hOS⟩, hCA⟩
  | none =>
    rw [hD] at h
    rcases switchTableArmOtherwiseTrianglePlan_spec h with ⟨oBlk, hOB, hOS, hOT, hCA⟩
    exact ⟨Or.inr ⟨oBlk, hOB, hOS, hOT⟩, hCA⟩

/-- Concrete statement list selected by an N-way `switchTable` for discriminator value `v`. -/
def lookupSwitchArmStmts (v : Nat) : List (Nat × List MirStmt) → List MirStmt → List MirStmt
  | [], otherwiseStmts => otherwiseStmts
  | (caseVal, armStmts) :: rest, otherwiseStmts =>
    if v == wrap64 caseVal then armStmts else lookupSwitchArmStmts v rest otherwiseStmts

/-- Execute an N-way `switchTable` diamond symbolically: evaluates `otherwiseStmts` and each
    `(caseVal, armStmts)` arm from `st`, prunes every arm post-state with `mask`, and folds
    them into a single canonical join state under `discrId == wrap64 caseVal`. -/
def symExecSwitchTableJoin (st : CanonState SymId) (discrId : SymId) (mask : List Bool)
    (otherwiseStmts : List MirStmt) :
    List (Nat × List MirStmt) → SymTable → (pc : PathCond := []) →
      Option (CanonState SymId × SymTable)
  | [], tbl, pc =>
    match symExecStmts st tbl otherwiseStmts pc with
    | none => none
    | some (stDef, tbl₁) => some (joinCanon mask stDef, tbl₁)
  | (caseVal, armStmts) :: rest, tbl, pc =>
    let (constId, tbl₁) := internNode tbl (.const caseVal)
    let (eqId, tbl₂) := internNode tbl₁ (.op2 .eq discrId constId)
    match symExecStmts st tbl₂ armStmts ((eqId, true) :: pc) with
    | none => none
    | some (stArm, tbl₃) =>
      match symExecSwitchTableJoin st discrId mask otherwiseStmts rest tbl₃ ((eqId, false) :: pc) with
      | none => none
      | some (stRest, tbl₄) =>
        mergeJoinStates tbl₄ eqId (joinCanon mask stArm) stRest

/-- **Path-Sensitive Compositional N-Way `switchTable` Join Soundness (`wpSwitchTableJoin_under_sound`)**:
    Under an enclosing conjunctive `pc : PathCond`, `symExecSwitchTableJoin` executes each case arm
    under `(eqId, true) :: pc`, threads the negated prior-case literal `(eqId, false) :: pc` into
    subsequent cases and `otherwiseStmts`, and produces a single canonical state `stM` refining
    whichever arm `lookupSwitchArmStmts` selects. -/
theorem wpSwitchTableJoin_under_sound {st : CanonState SymId} {discrId : SymId}
    {mask : List Bool} {otherwiseStmts : List MirStmt} :
    ∀ (caseArms : List (Nat × List MirStmt)) {tbl tblM : SymTable} {stM : CanonState SymId}
      {pc : PathCond},
      ValidTable tbl →
      ValidSymCanonState tbl.nodes.length st →
      discrId < tbl.nodes.length →
      PathCondValid tbl.nodes.length pc →
      symExecSwitchTableJoin st discrId mask otherwiseStmts caseArms tbl pc = some (stM, tblM) →
      ValidTable tblM ∧ tbl.Extends tblM ∧ ValidSymCanonState tblM.nodes.length stM ∧
        ∀ (env : SymEnv) (cst : CanonState Nat),
          PathCondHolds tbl env pc →
          StateRefines (evalSymCanonState tbl env st) cst →
          ∃ cst',
            execStmts cst
              (lookupSwitchArmStmts (evalSymId tbl env discrId) caseArms otherwiseStmts) =
                some cst' ∧
              StateRefines (evalSymCanonState tblM env stM) cst'
  | [], tbl, tblM, stM, pc, hValid, hSt, _, hPcValid, hJoin => by
    unfold symExecSwitchTableJoin at hJoin
    cases hDef : symExecStmts st tbl otherwiseStmts pc with
    | none => rw [hDef] at hJoin; cases hJoin
    | some pDef =>
      rcases pDef with ⟨stDef, tbl₁⟩
      rw [hDef] at hJoin
      injection hJoin with h1
      injection h1 with hStM hTblM
      subst hStM hTblM
      rcases symExecStmts_under_sound otherwiseStmts hValid hSt hDef hPcValid with
        ⟨hValid₁, hExt₁, hStDef, hEvalDef⟩
      refine ⟨hValid₁, hExt₁, hStDef.joinCanon mask, ?_⟩
      intro env cst hPc hR
      rcases execStmts_refines otherwiseStmts hR (hEvalDef env hPc) with ⟨cDef, hCDef, hRDef⟩
      refine ⟨cDef, hCDef, ?_⟩
      rw [evalSymCanonState_joinCanon]
      exact hRDef.joinCanon mask
  | (caseVal, armStmts) :: rest, tbl, tblM, stM, pc, hValid, hSt, hDiscr, hPcValid, hJoin => by
    unfold symExecSwitchTableJoin at hJoin
    let resC := internNode tbl (.const caseVal)
    have hNodeC : ValidNode tbl.nodes.length (.const caseVal) := trivial
    have hVC := internNode_valid hValid hNodeC
    have hValid₁ : ValidTable resC.2 := hVC.1
    have hConstLt : resC.1 < resC.2.nodes.length := hVC.2
    have hExt₁ : tbl.Extends resC.2 := internNode_extends tbl (.const caseVal)
    have hEvalC : ∀ env, evalSymId resC.2 env resC.1 = wrap64 caseVal :=
      fun env => internNode_eval hValid hNodeC env
    have hDiscr₁ : discrId < resC.2.nodes.length := Nat.lt_of_lt_of_le hDiscr hExt₁.length_le
    let resEq := internNode resC.2 (.op2 .eq discrId resC.1)
    have hNodeEq : ValidNode resC.2.nodes.length (.op2 .eq discrId resC.1) := ⟨hDiscr₁, hConstLt⟩
    have hVEq := internNode_valid hValid₁ hNodeEq
    have hValid₂ : ValidTable resEq.2 := hVEq.1
    have hEqLt : resEq.1 < resEq.2.nodes.length := hVEq.2
    have hExt₂ : resC.2.Extends resEq.2 := internNode_extends resC.2 (.op2 .eq discrId resC.1)
    have hExt₀₂ : tbl.Extends resEq.2 := hExt₁.trans hExt₂
    have hEvalEq : ∀ env,
        (evalSymId resEq.2 env resEq.1 != 0) = (evalSymId tbl env discrId == wrap64 caseVal) := by
      intro env
      have hE := internNode_eval hValid₁ hNodeEq env
      change evalSymId resEq.2 env resEq.1 =
        evalSymOp2 .eq (evalSymId resC.2 env discrId) (evalSymId resC.2 env resC.1) at hE
      rw [hE, ← evalSymId_mono hValid hExt₁ env hDiscr, hEvalC env]
      dsimp [evalSymOp2]
      cases (evalSymId tbl env discrId == wrap64 caseVal) <;> rfl
    have hSt₂ : ValidSymCanonState resEq.2.nodes.length st :=
      ValidSymSlots.mono hSt hExt₀₂.length_le
    have hPcValid₂ : PathCondValid resEq.2.nodes.length pc := hPcValid.mono hExt₀₂.length_le
    cases hArm : symExecStmts st resEq.2 armStmts ((resEq.1, true) :: pc) with
    | none =>
      change (match symExecStmts st resEq.2 armStmts ((resEq.1, true) :: pc) with
        | none => none
        | some (stArm, tbl₃) =>
          match symExecSwitchTableJoin st discrId mask otherwiseStmts rest tbl₃ ((resEq.1, false) :: pc) with
          | none => none
          | some (stRest, tbl₄) =>
            mergeJoinStates tbl₄ resEq.1 (joinCanon mask stArm) stRest) = some (stM, tblM) at hJoin
      rw [hArm] at hJoin
      cases hJoin
    | some pArm =>
      rcases pArm with ⟨stArm, tbl₃⟩
      change (match symExecStmts st resEq.2 armStmts ((resEq.1, true) :: pc) with
        | none => none
        | some (stArm, tbl₃) =>
          match symExecSwitchTableJoin st discrId mask otherwiseStmts rest tbl₃ ((resEq.1, false) :: pc) with
          | none => none
          | some (stRest, tbl₄) =>
            mergeJoinStates tbl₄ resEq.1 (joinCanon mask stArm) stRest) = some (stM, tblM) at hJoin
      rw [hArm] at hJoin
      dsimp only at hJoin
      rcases symExecStmts_under_sound armStmts hValid₂ hSt₂ hArm ⟨hEqLt, hPcValid₂⟩ with
        ⟨hValid₃, hExt₃, hStArm, hEvalArm⟩
      have hExt₀₃ : tbl.Extends tbl₃ := hExt₀₂.trans hExt₃
      have hSt₃ : ValidSymCanonState tbl₃.nodes.length st :=
        ValidSymSlots.mono hSt hExt₀₃.length_le
      have hDiscr₃ : discrId < tbl₃.nodes.length :=
        Nat.lt_of_lt_of_le hDiscr hExt₀₃.length_le
      have hEqLt₃ : resEq.1 < tbl₃.nodes.length :=
        Nat.lt_of_lt_of_le hEqLt hExt₃.length_le
      have hPcValid₃ : PathCondValid tbl₃.nodes.length ((resEq.1, false) :: pc) :=
        ⟨hEqLt₃, hPcValid.mono hExt₀₃.length_le⟩
      cases hRest : symExecSwitchTableJoin st discrId mask otherwiseStmts rest tbl₃ ((resEq.1, false) :: pc) with
      | none => rw [hRest] at hJoin; cases hJoin
      | some pRest =>
        rcases pRest with ⟨stRest, tbl₄⟩
        rw [hRest] at hJoin
        dsimp only at hJoin
        rcases wpSwitchTableJoin_under_sound rest hValid₃ hSt₃ hDiscr₃ hPcValid₃ hRest with
          ⟨hValid₄, hExt₄, hStRest, hEvalRest⟩
        have hExt₂₄ : resEq.2.Extends tbl₄ := hExt₃.trans hExt₄
        have hEqLt₄ : resEq.1 < tbl₄.nodes.length := Nat.lt_of_lt_of_le hEqLt hExt₂₄.length_le
        have hStArmc₄ : ValidSymCanonState tbl₄.nodes.length (joinCanon mask stArm) :=
          ValidSymSlots.mono (hStArm.joinCanon mask) hExt₄.length_le
        rcases mergeJoinStates_eval hValid₄ hEqLt₄ hStArmc₄ hStRest hJoin with
          ⟨hValidM, hExtM, hStM, hEvalM⟩
        refine ⟨hValidM, (hExt₀₃.trans hExt₄).trans hExtM, hStM, ?_⟩
        intro env cst hPc hR
        rw [hEvalM env, ← evalSymId_mono hValid₂ hExt₂₄ env hEqLt, hEvalEq env]
        dsimp only [lookupSwitchArmStmts]
        cases hB : (evalSymId tbl env discrId == wrap64 caseVal) with
        | true =>
          have hR₂ : StateRefines (evalSymCanonState resEq.2 env st) cst := by
            rw [← evalSymCanonState_mono hValid hExt₀₂ env hSt]
            exact hR
          have hPc₂ : PathCondHolds resEq.2 env ((resEq.1, true) :: pc) := by
            refine ⟨?_, PathCondHolds.mono hValid hExt₀₂ hPcValid hPc⟩
            show (evalSymId resEq.2 env resEq.1 != 0) = true
            rw [hEvalEq env]
            exact hB
          rcases execStmts_refines armStmts hR₂ (hEvalArm env hPc₂) with ⟨cArm, hCArm, hRArm⟩
          refine ⟨cArm, by rw [ite_eq_left rfl]; exact hCArm, ?_⟩
          rw [ite_eq_left rfl, ← evalSymCanonState_mono hValid₃ hExt₄ env (hStArm.joinCanon mask),
            evalSymCanonState_joinCanon]
          exact hRArm.joinCanon mask
        | false =>
          have hR₃ : StateRefines (evalSymCanonState tbl₃ env st) cst := by
            rw [← evalSymCanonState_mono hValid hExt₀₃ env hSt]
            exact hR
          have hPc₃ : PathCondHolds tbl₃ env ((resEq.1, false) :: pc) := by
            refine ⟨?_, PathCondHolds.mono hValid hExt₀₃ hPcValid hPc⟩
            show (evalSymId tbl₃ env resEq.1 != 0) = false
            rw [← evalSymId_mono hValid₂ hExt₃ env hEqLt, hEvalEq env]
            exact hB
          rcases hEvalRest env cst hPc₃ hR₃ with ⟨cRest, hCRest, hRRest⟩
          rw [← evalSymId_mono hValid hExt₀₃ env hDiscr] at hCRest
          refine ⟨cRest, by rw [ite_eq_right Bool.false_ne_true]; exact hCRest, ?_⟩
          rw [ite_eq_right Bool.false_ne_true]
          exact hRRest

/-- **Compositional N-Way `switchTable` Join Soundness (`wpSwitchTableJoin_sound`)**:
    For any number of `(caseVal, armStmts)` arms and `otherwiseStmts` converging at `joinBb`,
    `symExecSwitchTableJoin` produces a single canonical state `stM` that refines the concrete
    post-state of whichever arm `lookupSwitchArmStmts` selects. -/
theorem wpSwitchTableJoin_sound {st : CanonState SymId} {discrId : SymId}
    {mask : List Bool} {otherwiseStmts : List MirStmt}
    (caseArms : List (Nat × List MirStmt)) {tbl tblM : SymTable} {stM : CanonState SymId}
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hDiscr : discrId < tbl.nodes.length)
    (hJoin : symExecSwitchTableJoin st discrId mask otherwiseStmts caseArms tbl = some (stM, tblM)) :
    ValidTable tblM ∧ tbl.Extends tblM ∧ ValidSymCanonState tblM.nodes.length stM ∧
      ∀ (env : SymEnv) (cst : CanonState Nat),
        StateRefines (evalSymCanonState tbl env st) cst →
        ∃ cst',
          execStmts cst
            (lookupSwitchArmStmts (evalSymId tbl env discrId) caseArms otherwiseStmts) =
              some cst' ∧
            StateRefines (evalSymCanonState tblM env stM) cst' := by
  rcases wpSwitchTableJoin_under_sound caseArms (pc := []) hValid hSt hDiscr trivial hJoin with
    ⟨hVM, hEM, hStM, hEv⟩
  exact ⟨hVM, hEM, hStM, fun env cst hR => hEv env cst trivial hR⟩

theorem execCfg_lookupSwitchTarget_of_matchSwitchCases {cfg : MirCfg} {joinBb : BlockId} :
    ∀ (cases : List (Nat × BlockId)) {caseArms : List (Nat × List MirStmt)}
      {otherwiseBb : BlockId} {oBlk : MirBlock} {f : Nat} {v : Nat}
      {cst cst' : CanonState Nat},
      matchSwitchCases cfg joinBb cases = some caseArms →
      cfg.blocks[otherwiseBb]? = some oBlk →
      oBlk.term = .goto joinBb →
      execStmts cst (lookupSwitchArmStmts v caseArms oBlk.stmts) = some cst' →
      execCfg cfg (f + 1) (lookupCfgSwitchTarget v cases otherwiseBb) cst =
        execCfg cfg f joinBb cst'
  | [], _, otherwiseBb, oBlk, f, v, cst, cst', hCases, hOBlk, hOTerm, hExec => by
    injection hCases with hNil
    subst hNil
    dsimp only [lookupCfgSwitchTarget, lookupSwitchArmStmts] at hExec ⊢
    dsimp only [execCfg]
    rw [hOBlk]
    dsimp only
    rw [hExec]
    dsimp only
    rw [hOTerm]
  | (caseVal, targetBb) :: rest, _, otherwiseBb, oBlk, f, v, cst, cst', hCases, hOBlk, hOTerm, hExec => by
    unfold matchSwitchCases at hCases
    split at hCases
    · rename_i tBlk restArms hTBlk hRest
      split at hCases
      · rename_i j hj
        split at hCases
        · rename_i hjEq
          subst hjEq
          injection hCases with hCons
          subst hCons
          dsimp only [lookupCfgSwitchTarget, lookupSwitchArmStmts] at hExec ⊢
          cases hEq : (v == wrap64 caseVal) with
          | true =>
            rw [hEq, ite_eq_left rfl] at hExec
            rw [ite_eq_left rfl]
            dsimp only [execCfg]
            rw [hTBlk]
            dsimp only
            rw [hExec]
            dsimp only
            rw [armGoto?_spec hj]
          | false =>
            rw [hEq, ite_eq_right Bool.false_ne_true] at hExec
            rw [ite_eq_right Bool.false_ne_true]
            exact execCfg_lookupSwitchTarget_of_matchSwitchCases rest hRest hOBlk hOTerm hExec
        · cases hCases
      · cases hCases
    · cases hCases

theorem execCfg_lookupSwitchTarget_of_matchSwitchTriangleCases {cfg : MirCfg} {joinBb : BlockId} :
    ∀ (cases : List (Nat × BlockId)) {caseArms : List (Nat × List MirStmt)}
      {otherwiseBb : BlockId} {otherwiseStmts : List MirStmt} {f : Nat} {v : Nat}
      {cst cst' : CanonState Nat} {retVal : Nat},
      matchSwitchTriangleCases cfg joinBb cases = some caseArms →
      ((otherwiseBb = joinBb ∧ otherwiseStmts = []) ∨
        (∃ oBlk, cfg.blocks[otherwiseBb]? = some oBlk ∧ oBlk.stmts = otherwiseStmts ∧
          oBlk.term = .goto joinBb)) →
      execStmts cst (lookupSwitchArmStmts v caseArms otherwiseStmts) = some cst' →
      execCfg cfg f joinBb cst' = .ret retVal →
      execCfg cfg (f + 1) (lookupCfgSwitchTarget v cases otherwiseBb) cst = .ret retVal
  | [], _, otherwiseBb, otherwiseStmts, f, v, cst, cst', retVal, hCases, hO, hExec, hRet => by
    injection hCases with hNil
    subst hNil
    dsimp only [lookupCfgSwitchTarget, lookupSwitchArmStmts] at hExec ⊢
    rcases hO with ⟨hOB, hOS⟩ | ⟨oBlk, hOBlk, hOS, hOTerm⟩
    · subst hOB hOS
      have hc : cst = cst' := Option.some.inj hExec
      subst hc
      exact execCfg_ret_succ cfg f otherwiseBb cst _ hRet
    · subst hOS
      dsimp only [execCfg]
      rw [hOBlk]
      dsimp only
      rw [hExec]
      dsimp only
      rw [hOTerm]
      exact hRet
  | (caseVal, targetBb) :: rest, _, otherwiseBb, otherwiseStmts, f, v, cst, cst', retVal, hCases, hO, hExec, hRet => by
    unfold matchSwitchTriangleCases at hCases
    by_cases hEqBb : targetBb = joinBb
    · rw [ite_eq_left hEqBb] at hCases
      cases hRest : matchSwitchTriangleCases cfg joinBb rest with
      | none => rw [hRest] at hCases; cases hCases
      | some restArms =>
        rw [hRest] at hCases
        injection hCases with hCons
        subst hCons
        dsimp only [lookupCfgSwitchTarget, lookupSwitchArmStmts] at hExec ⊢
        cases hEq : (v == wrap64 caseVal) with
        | true =>
          rw [hEq, ite_eq_left rfl] at hExec
          rw [ite_eq_left rfl, hEqBb]
          have hc : cst = cst' := Option.some.inj hExec
          subst hc
          exact execCfg_ret_succ cfg f joinBb cst _ hRet
        | false =>
          rw [hEq, ite_eq_right Bool.false_ne_true] at hExec
          rw [ite_eq_right Bool.false_ne_true]
          exact execCfg_lookupSwitchTarget_of_matchSwitchTriangleCases rest hRest hO hExec hRet
    · rw [ite_eq_right hEqBb] at hCases
      split at hCases
      · rename_i tBlk restArms hTBlk hRest
        split at hCases
        · rename_i j hj
          split at hCases
          · rename_i hjEq
            subst hjEq
            injection hCases with hCons
            subst hCons
            dsimp only [lookupCfgSwitchTarget, lookupSwitchArmStmts] at hExec ⊢
            cases hEq : (v == wrap64 caseVal) with
            | true =>
              rw [hEq, ite_eq_left rfl] at hExec
              rw [ite_eq_left rfl]
              dsimp only [execCfg]
              rw [hTBlk]
              dsimp only
              rw [hExec]
              dsimp only
              rw [armGoto?_spec hj]
              exact hRet
            | false =>
              rw [hEq, ite_eq_right Bool.false_ne_true] at hExec
              rw [ite_eq_right Bool.false_ne_true]
              exact execCfg_lookupSwitchTarget_of_matchSwitchTriangleCases rest hRest hO hExec hRet
          · cases hCases
        · cases hCases
      · cases hCases

/-- Statically known `switchTable` target for a **constant** discriminant (the N-way analogue of
    `constCond?`): `lookupCfgSwitchTarget (wrap64 v) cases otherwiseBb` when `discrId` is interned as
    `.const v`. Infeasible arms are then neither merged nor explored, so an arm that can never run
    (e.g. one that asserts `false`) cannot make verification fail. -/
def constSwitchTarget? (tbl : SymTable) (discrId : SymId) (cases : List (Nat × BlockId))
    (otherwiseBb : BlockId) : Option BlockId :=
  match tbl.nodes[discrId]? with
  | some (.const v) => some (lookupCfgSwitchTarget (wrap64 v) cases otherwiseBb)
  | _ => none

theorem constSwitchTarget?_sound {tbl : SymTable} {discrId : SymId} {cases : List (Nat × BlockId)}
    {otherwiseBb targetBb : BlockId} (hValid : ValidTable tbl)
    (h : constSwitchTarget? tbl discrId cases otherwiseBb = some targetBb) (env : SymEnv) :
    lookupCfgSwitchTarget (evalSymId tbl env discrId) cases otherwiseBb = targetBb := by
  unfold constSwitchTarget? at h
  split at h
  · rename_i v hNode
    injection h with hT
    subst hT
    rw [evalSymId_eq_evalSymNodeWith hValid env hNode]
    rfl
  · cases h

/-- Path-splitting fallback for an unhinted N-way `switchTable`: evaluates each `(caseVal, targetBb)`
    under **that case's path condition** `discrId == wrap64 caseVal` (the same interned
    `.op2 .eq discrId (.const caseVal)` node `symExecSwitchTableJoin` uses for merged arms), and
    finally `otherwiseBb` under the outer `pc`, threading the append-only `SymTable` through
    `combineSplit` (the N-way analogue of the `some (condId, true/false)` split of `switchInt`). -/
def evalSwitchTableSplit
    (evalBlock : BlockId → SymTable → PathCond → Option (List SymId × SymTable))
    (discrId : SymId) (pc : PathCond) :
    List (Nat × BlockId) → BlockId → SymTable → Option (List SymId × SymTable)
  | [], otherwiseBb, tbl => evalBlock otherwiseBb tbl pc
  | (caseVal, targetBb) :: rest, otherwiseBb, tbl =>
    let resC := internNode tbl (.const caseVal)
    let resEq := internNode resC.2 (.op2 .eq discrId resC.1)
    combineSplit (evalBlock targetBb resEq.2 ((resEq.1, true) :: pc))
      (fun tblT => evalSwitchTableSplit evalBlock discrId ((resEq.1, false) :: pc) rest otherwiseBb tblT)

theorem evalSwitchTableSplit_sound {cfg : MirCfg} {fuel : Nat} {st₂ : CanonState SymId}
    {discrId : SymId}
    {evalBlock : BlockId → SymTable → PathCond → Option (List SymId × SymTable)}
    (hBlockSound : ∀ (targetBb : BlockId) (tblIn : SymTable) (pcIn : PathCond)
        (retsOut : List SymId) (tblOut : SymTable),
        ValidTable tblIn → ValidSymCanonState tblIn.nodes.length st₂ →
        PathCondValid tblIn.nodes.length pcIn →
        evalBlock targetBb tblIn pcIn = some (retsOut, tblOut) →
        ValidTable tblOut ∧ tblIn.Extends tblOut ∧ (∀ r ∈ retsOut, r < tblOut.nodes.length) ∧
          ∀ (env : SymEnv) (cst₂ : CanonState Nat),
            PathCondHolds tblIn env pcIn →
            StateRefines (evalSymCanonState tblIn env st₂) cst₂ →
            ∃ r ∈ retsOut, execCfg cfg fuel targetBb cst₂ = .ret (evalSymId tblOut env r)) :
    ∀ (cases : List (Nat × BlockId)) (otherwiseBb : BlockId) (tbl₁ : SymTable)
      (pc : PathCond) (rets : List SymId) (tbl' : SymTable),
      ValidTable tbl₁ →
      ValidSymCanonState tbl₁.nodes.length st₂ →
      PathCondValid tbl₁.nodes.length pc →
      discrId < tbl₁.nodes.length →
      evalSwitchTableSplit evalBlock discrId pc cases otherwiseBb tbl₁ = some (rets, tbl') →
      ValidTable tbl' ∧ tbl₁.Extends tbl' ∧ (∀ r ∈ rets, r < tbl'.nodes.length) ∧
        ∀ (env : SymEnv) (cst₂ : CanonState Nat),
          PathCondHolds tbl₁ env pc →
          StateRefines (evalSymCanonState tbl₁ env st₂) cst₂ →
          ∃ r ∈ rets,
            execCfg cfg fuel
                (lookupCfgSwitchTarget (evalSymId tbl₁ env discrId) cases otherwiseBb) cst₂ =
              .ret (evalSymId tbl' env r)
  | [], otherwiseBb, tbl₁, pc, rets, tbl', hV₁, hS₁, hP₁, _, hSplit => by
    rcases hBlockSound otherwiseBb tbl₁ pc rets tbl' hV₁ hS₁ hP₁ hSplit with ⟨hV', hE', hLt', hEv'⟩
    exact ⟨hV', hE', hLt', fun env cst₂ hPc hR => hEv' env cst₂ hPc hR⟩
  | (caseVal, targetBb) :: rest, otherwiseBb, tbl₁, pc, rets, tbl', hV₁, hS₁, hP₁, hD₁, hSplit => by
    let resC := internNode tbl₁ (.const caseVal)
    have hNodeC : ValidNode tbl₁.nodes.length (.const caseVal) := trivial
    have hVC := internNode_valid hV₁ hNodeC
    have hExtC : tbl₁.Extends resC.2 := internNode_extends tbl₁ (.const caseVal)
    have hEvalC : ∀ env, evalSymId resC.2 env resC.1 = wrap64 caseVal :=
      fun env => internNode_eval hV₁ hNodeC env
    have hDC : discrId < resC.2.nodes.length := Nat.lt_of_lt_of_le hD₁ hExtC.length_le
    let resEq := internNode resC.2 (.op2 .eq discrId resC.1)
    have hNodeEq : ValidNode resC.2.nodes.length (.op2 .eq discrId resC.1) := ⟨hDC, hVC.2⟩
    have hVEq := internNode_valid hVC.1 hNodeEq
    have hExtEq : resC.2.Extends resEq.2 := internNode_extends resC.2 (.op2 .eq discrId resC.1)
    have hExt₁₂ : tbl₁.Extends resEq.2 := hExtC.trans hExtEq
    have hEvalEq : ∀ env,
        (evalSymId resEq.2 env resEq.1 != 0) = (evalSymId tbl₁ env discrId == wrap64 caseVal) := by
      intro env
      have hE := internNode_eval hVC.1 hNodeEq env
      change evalSymId resEq.2 env resEq.1 =
        evalSymOp2 .eq (evalSymId resC.2 env discrId) (evalSymId resC.2 env resC.1) at hE
      rw [hE, ← evalSymId_mono hV₁ hExtC env hD₁, hEvalC env]
      dsimp [evalSymOp2]
      cases (evalSymId tbl₁ env discrId == wrap64 caseVal) <;> rfl
    have hS₂ : ValidSymCanonState resEq.2.nodes.length st₂ :=
      ValidSymSlots.mono hS₁ hExt₁₂.length_le
    have hPCase : PathCondValid resEq.2.nodes.length ((resEq.1, true) :: pc) :=
      ⟨hVEq.2, hP₁.mono hExt₁₂.length_le⟩
    change combineSplit (evalBlock targetBb resEq.2 ((resEq.1, true) :: pc))
      (fun tblT => evalSwitchTableSplit evalBlock discrId ((resEq.1, false) :: pc) rest otherwiseBb tblT) =
        some (rets, tbl') at hSplit
    rcases combineSplit_eq_some hSplit with ⟨retsT, tblT, retsF, hT, hF, hRets⟩
    subst hRets
    rcases hBlockSound targetBb resEq.2 ((resEq.1, true) :: pc) retsT tblT hVEq.1 hS₂ hPCase hT with
      ⟨hVT, hET, hLtT, hEvT⟩
    have hExt₁T : tbl₁.Extends tblT := hExt₁₂.trans hET
    have hST : ValidSymCanonState tblT.nodes.length st₂ := ValidSymSlots.mono hS₁ hExt₁T.length_le
    have hEqLtT : resEq.1 < tblT.nodes.length := Nat.lt_of_lt_of_le hVEq.2 hET.length_le
    have hPT : PathCondValid tblT.nodes.length ((resEq.1, false) :: pc) :=
      ⟨hEqLtT, hP₁.mono hExt₁T.length_le⟩
    have hDT : discrId < tblT.nodes.length := Nat.lt_of_lt_of_le hD₁ hExt₁T.length_le
    rcases evalSwitchTableSplit_sound hBlockSound rest otherwiseBb tblT ((resEq.1, false) :: pc)
      retsF tbl' hVT hST hPT hDT hF with ⟨hVF, hEF, hLtF, hEvF⟩
    refine ⟨hVF, hExt₁T.trans hEF, ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact Nat.lt_of_lt_of_le (hLtT r hr) hEF.length_le
      · exact hLtF r hr
    · intro env cst₂ hPc hR
      dsimp only [lookupCfgSwitchTarget]
      cases hMatch : (evalSymId tbl₁ env discrId == wrap64 caseVal) with
      | true =>
        have hPcCase : PathCondHolds resEq.2 env ((resEq.1, true) :: pc) := by
          refine ⟨?_, PathCondHolds.mono hV₁ hExt₁₂ hP₁ hPc⟩
          show (evalSymId resEq.2 env resEq.1 != 0) = true
          rw [hEvalEq env, hMatch]
        have hR₂ : StateRefines (evalSymCanonState resEq.2 env st₂) cst₂ := by
          rw [← evalSymCanonState_mono hV₁ hExt₁₂ env hS₁]
          exact hR
        rcases hEvT env cst₂ hPcCase hR₂ with ⟨r, hr, hExec⟩
        refine ⟨r, List.mem_append_left _ hr, ?_⟩
        rw [ite_eq_left rfl, hExec, evalSymId_mono hVT hEF env (hLtT r hr)]
      | false =>
        have hPcT : PathCondHolds tblT env ((resEq.1, false) :: pc) := by
          refine ⟨?_, PathCondHolds.mono hV₁ hExt₁T hP₁ hPc⟩
          show (evalSymId tblT env resEq.1 != 0) = false
          rw [← evalSymId_mono hVEq.1 hET env hVEq.2, hEvalEq env, hMatch]
        have hRT : StateRefines (evalSymCanonState tblT env st₂) cst₂ := by
          rw [← evalSymCanonState_mono hV₁ hExt₁T env hS₁]
          exact hR
        rcases hEvF env cst₂ hPcT hRT with ⟨r, hr, hExec⟩
        refine ⟨r, List.mem_append_right _ hr, ?_⟩
        rw [ite_eq_right Bool.false_ne_true, evalSymId_mono hV₁ hExt₁T env hD₁]
        exact hExec

/-- Single-continuation compositional symbolic GVN evaluator for multi-block `MirCfg`s.
    Returns the list of returned `SymId`s (one per explored path) in the final append-only
    table. At a symbolic `switchInt` whose arms form a diamond with a hinted join block, both
    arms are executed, pruned with the join mask (`joinCanon`), merged (`mergeJoinStates`,
    GVN + `ite c v v ↦ v`), and the join continuation is evaluated **once** (consuming one
    extra unit of fuel for the arm block, exactly as the concrete execution does). A hinted
    **triangle** (`if c { arm }` without `else`: one successor is an arm block ending in `goto j`
    and the other successor is `j` itself, the shape post-`SimplifyCfg` MIR gives every
    `if` without `else`) is merged the same way with an empty statement list on the direct side
    (whose concrete path reaches `j` with one spare unit of fuel, `execCfg_ret_succ`). Without a
    hint it path-splits. CPS spine forcing (`forceCanonState`) is applied at every block. -/
def symEvalCfgGvn (cfg : MirCfg) (hints : JoinHints) :
    Nat → BlockId → CanonState SymId → SymTable → (pc : PathCond := []) →
      Option (List SymId × SymTable)
  | 0, _, _, _, _ => none
  | fuel + 1, bb, st, tbl, pc =>
    match cfg.blocks[bb]? with
    | none => none
    | some blk =>
      match symExecStmts st tbl blk.stmts pc with
      | none => none
      | some (st₀, tbl₁) =>
        forceCanonState st₀ fun st₁ =>
        match blk.term with
        | .goto target => symEvalCfgGvn cfg hints fuel target st₁ tbl₁ pc
        | .switchInt discr thenBb elseBb =>
          match readSymScalar st₁ discr with
          | none => none
          | some condId =>
            let st₂ := st₁.ownerReadLoc discr
            match constCond? tbl₁ condId with
            | some b =>
              if b then symEvalCfgGvn cfg hints fuel thenBb st₂ tbl₁ pc
              else symEvalCfgGvn cfg hints fuel elseBb st₂ tbl₁ pc
            | none =>
              if thenBb = elseBb then
                symEvalCfgGvn cfg hints fuel thenBb st₂ tbl₁ pc
              else
                match diamondMergePlan cfg hints thenBb elseBb with
                | some (thenStmts, elseStmts, joinBb, mask) =>
                  match fuel with
                  | 0 => none
                  | f + 1 =>
                    match symExecDiamondJoin st₂ tbl₁ condId thenStmts elseStmts mask pc with
                    | none => none
                    | some (stM, tblM) => symEvalCfgGvn cfg hints f joinBb stM tblM pc
                | none =>
                  match triangleMergePlan cfg hints thenBb elseBb with
                  | some (thenStmts, elseStmts, joinBb, mask) =>
                    match fuel with
                    | 0 => none
                    | f + 1 =>
                      match symExecDiamondJoin st₂ tbl₁ condId thenStmts elseStmts mask pc with
                      | none => none
                      | some (stM, tblM) => symEvalCfgGvn cfg hints f joinBb stM tblM pc
                  | none =>
                    combineSplit (symEvalCfgGvn cfg hints fuel thenBb st₂ tbl₁ ((condId, true) :: pc))
                      (fun tblT => symEvalCfgGvn cfg hints fuel elseBb st₂ tblT ((condId, false) :: pc))
        | .switchTable discr cases otherwiseBb =>
          match readSymScalar st₁ discr with
          | none => none
          | some discrId =>
            let st₂ := st₁.ownerReadLoc discr
            match constSwitchTarget? tbl₁ discrId cases otherwiseBb with
            | some targetBb => symEvalCfgGvn cfg hints fuel targetBb st₂ tbl₁ pc
            | none =>
              match switchTableMergePlan cfg hints cases otherwiseBb with
              | some (caseArms, otherwiseStmts, joinBb, mask) =>
                match fuel with
                | 0 => none
                | f + 1 =>
                  match symExecSwitchTableJoin st₂ discrId mask otherwiseStmts caseArms tbl₁ pc with
                  | none => none
                  | some (stM, tblM) => symEvalCfgGvn cfg hints f joinBb stM tblM pc
              | none =>
                match switchTableTrianglePlan cfg hints cases otherwiseBb with
                | some (caseArms, otherwiseStmts, joinBb, mask) =>
                  match fuel with
                  | 0 => none
                  | f + 1 =>
                    match symExecSwitchTableJoin st₂ discrId mask otherwiseStmts caseArms tbl₁ pc with
                    | none => none
                    | some (stM, tblM) => symEvalCfgGvn cfg hints f joinBb stM tblM pc
                | none =>
                  evalSwitchTableSplit
                    (fun targetBb tblIn pcIn => symEvalCfgGvn cfg hints fuel targetBb st₂ tblIn pcIn)
                    discrId pc cases otherwiseBb tbl₁
        | .ret retLoc =>
          match readSymScalar st₁ retLoc with
          | some retSymId => some ([retSymId], tbl₁)
          | none => none
        | .unreachable => none

/-- Path-sensitive soundness obligation for a symbolic CFG result `(rets, tbl')` under `pc`. -/
def CfgResultSoundUnder (cfg : MirCfg) (fuel : Nat) (bb : BlockId) (st : CanonState SymId)
    (tbl : SymTable) (pc : PathCond) (rets : List SymId) (tbl' : SymTable) : Prop :=
  ValidTable tbl' ∧ tbl.Extends tbl' ∧ (∀ r ∈ rets, r < tbl'.nodes.length) ∧
    ∀ (env : SymEnv) (cst : CanonState Nat),
      PathCondHolds tbl env pc →
      StateRefines (evalSymCanonState tbl env st) cst →
      ∃ r ∈ rets, execCfg cfg fuel bb cst = .ret (evalSymId tbl' env r)

/-- Soundness obligation for a symbolic CFG result `(rets, tbl')` from `(bb, st, tbl)`: the
    final table is a valid extension, every returned `SymId` is allocated, and from **every**
    concrete state refined by the evaluated entry state, the mask-free concrete execution with
    the same fuel returns (no fault, no fuel exhaustion) the value of some returned `SymId`. -/
def CfgResultSound (cfg : MirCfg) (fuel : Nat) (bb : BlockId) (st : CanonState SymId)
    (tbl : SymTable) (rets : List SymId) (tbl' : SymTable) : Prop :=
  ValidTable tbl' ∧ tbl.Extends tbl' ∧ (∀ r ∈ rets, r < tbl'.nodes.length) ∧
    ∀ (env : SymEnv) (cst : CanonState Nat),
      StateRefines (evalSymCanonState tbl env st) cst →
      ∃ r ∈ rets, execCfg cfg fuel bb cst = .ret (evalSymId tbl' env r)

/-- **Path-Sensitive Symbolic CFG Soundness (`symEvalCfgGvn_under_sound`)**, for every
    (untrusted) `hints` and active branch path condition `pc`. -/
theorem symEvalCfgGvn_under_sound (cfg : MirCfg) (hints : JoinHints) :
    ∀ (fuel : Nat) (bb : BlockId) (st : CanonState SymId) (tbl : SymTable) (pc : PathCond)
      (rets : List SymId) (tbl' : SymTable),
      ValidTable tbl →
      ValidSymCanonState tbl.nodes.length st →
      PathCondValid tbl.nodes.length pc →
      symEvalCfgGvn cfg hints fuel bb st tbl pc = some (rets, tbl') →
      CfgResultSoundUnder cfg fuel bb st tbl pc rets tbl'
  | 0, _, _, _, _, _, _, _, _, _, hEval => by cases hEval
  | fuel + 1, bb, st, tbl, pc, rets, tbl', hValid, hSt, hPcValid, hEval => by
    rw [symEvalCfgGvn] at hEval
    cases hBlk : cfg.blocks[bb]? with
    | none => rw [hBlk] at hEval; cases hEval
    | some blk =>
      rw [hBlk] at hEval
      dsimp only at hEval
      cases hStmts : symExecStmts st tbl blk.stmts pc with
      | none => rw [hStmts] at hEval; cases hEval
      | some pair₁ =>
        rcases pair₁ with ⟨st₁, tbl₁⟩
        rw [hStmts] at hEval
        dsimp only at hEval
        rw [forceCanonState_eq] at hEval
        rcases symExecStmts_under_sound blk.stmts hValid hSt hStmts hPcValid with
          ⟨hValid₁, hExt₁, hSt₁, hEvalStmts⟩
        have hPcValid₁ : PathCondValid tbl₁.nodes.length pc := hPcValid.mono hExt₁.length_le
        have hPrefix : ∀ env cst, PathCondHolds tbl env pc →
            StateRefines (evalSymCanonState tbl env st) cst →
            ∃ c₁, execStmts cst blk.stmts = some c₁ ∧
              StateRefines (evalSymCanonState tbl₁ env st₁) c₁ ∧
              PathCondHolds tbl₁ env pc :=
          fun env _ hPc hR =>
            let ⟨c₁, hC₁, hR₁⟩ := execStmts_refines blk.stmts hR (hEvalStmts env hPc)
            ⟨c₁, hC₁, hR₁, PathCondHolds.mono hValid hExt₁ hPcValid hPc⟩
        cases hTerm : blk.term with
        | goto target =>
          rw [hTerm] at hEval
          rcases symEvalCfgGvn_under_sound cfg hints fuel target st₁ tbl₁ pc rets tbl'
            hValid₁ hSt₁ hPcValid₁ hEval with ⟨hV', hE', hLt', hEv'⟩
          refine ⟨hV', hExt₁.trans hE', hLt', ?_⟩
          intro env cst hPc hR
          rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
          rcases hEv' env c₁ hPc₁ hR₁ with ⟨r, hr, hExec⟩
          refine ⟨r, hr, ?_⟩
          dsimp only [execCfg]
          rw [hBlk]
          dsimp only
          rw [hC₁]
          dsimp only
          rw [hTerm]
          exact hExec
        | switchInt discr thenBb elseBb =>
          rw [hTerm] at hEval
          dsimp only at hEval
          cases hDiscr : readSymScalar st₁ discr with
          | none => rw [hDiscr] at hEval; cases hEval
          | some condId =>
            rw [hDiscr] at hEval
            dsimp only at hEval
            have hCondLt : condId < tbl₁.nodes.length := by
              have hSpec := readSymScalar_spec (fun _ => 0) hSt₁ (loc := discr)
              rw [hDiscr] at hSpec
              exact hSpec.1
            -- Reading the discriminant is an owner read: both successors start from `st₂`.
            have hSt₂ : ValidSymCanonState tbl₁.nodes.length (st₁.ownerReadLoc discr) :=
              hSt₁.ownerReadLoc discr
            have hR₂ : ∀ env c₁, StateRefines (evalSymCanonState tbl₁ env st₁) c₁ →
                StateRefines (evalSymCanonState tbl₁ env (st₁.ownerReadLoc discr))
                  (c₁.ownerReadLoc discr) := by
              intro env c₁ hR₁
              rw [evalSymCanonState_ownerReadLoc]
              exact hR₁.ownerReadLoc discr
            have hStepC : ∀ env cst c₁, execStmts cst blk.stmts = some c₁ →
                StateRefines (evalSymCanonState tbl₁ env st₁) c₁ →
                execCfg cfg (fuel + 1) bb cst =
                  (if evalSymId tbl₁ env condId != 0 then
                      execCfg cfg fuel thenBb (c₁.ownerReadLoc discr)
                    else execCfg cfg fuel elseBb (c₁.ownerReadLoc discr)) := by
              intro env cst c₁ hC₁ hR₁
              have hSpec := readSymScalar_spec env hSt₁ (loc := discr)
              rw [hDiscr] at hSpec
              dsimp only [execCfg]
              rw [hBlk]
              dsimp only
              rw [hC₁]
              dsimp only
              rw [hTerm]
              dsimp only
              rw [readConcreteScalar_refines hR₁ hSpec.2]
            have hSplitCase : combineSplit
                (symEvalCfgGvn cfg hints fuel thenBb (st₁.ownerReadLoc discr) tbl₁
                  ((condId, true) :: pc))
                (fun tblT => symEvalCfgGvn cfg hints fuel elseBb (st₁.ownerReadLoc discr) tblT
                  ((condId, false) :: pc)) =
                  some (rets, tbl') →
                CfgResultSoundUnder cfg (fuel + 1) bb st tbl pc rets tbl' := by
              intro hComb
              rcases combineSplit_eq_some hComb with ⟨retsT, tblT, retsF, hT, hF, hRets⟩
              subst hRets
              rcases symEvalCfgGvn_under_sound cfg hints fuel thenBb (st₁.ownerReadLoc discr) tbl₁
                ((condId, true) :: pc) retsT tblT hValid₁ hSt₂ ⟨hCondLt, hPcValid₁⟩ hT with
                ⟨hVT, hET, hLtT, hEvT⟩
              have hSt₂T : ValidSymCanonState tblT.nodes.length (st₁.ownerReadLoc discr) :=
                ValidSymSlots.mono hSt₂ hET.length_le
              have hCondLtT : PathCondValid tblT.nodes.length ((condId, false) :: pc) :=
                ⟨Nat.lt_of_lt_of_le hCondLt hET.length_le, hPcValid₁.mono hET.length_le⟩
              rcases symEvalCfgGvn_under_sound cfg hints fuel elseBb (st₁.ownerReadLoc discr) tblT
                ((condId, false) :: pc) retsF tbl' hVT hSt₂T hCondLtT hF with
                ⟨hVF, hEF, hLtF, hEvF⟩
              refine ⟨hVF, (hExt₁.trans hET).trans hEF, ?_, ?_⟩
              · intro r hr
                rcases List.mem_append.1 hr with hr | hr
                · exact Nat.lt_of_lt_of_le (hLtT r hr) hEF.length_le
                · exact hLtF r hr
              · intro env cst hPc hR
                rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                rw [hStepC env cst c₁ hC₁ hR₁]
                cases hB : (evalSymId tbl₁ env condId != 0) with
                | true =>
                  rcases hEvT env (c₁.ownerReadLoc discr) ⟨hB, hPc₁⟩ (hR₂ env c₁ hR₁) with ⟨r, hr, hExec⟩
                  refine ⟨r, List.mem_append_left _ hr, ?_⟩
                  rw [ite_eq_left rfl, hExec, evalSymId_mono hVT hEF env (hLtT r hr)]
                | false =>
                  have hR₂T : StateRefines (evalSymCanonState tblT env (st₁.ownerReadLoc discr))
                      (c₁.ownerReadLoc discr) := by
                    rw [← evalSymCanonState_mono hValid₁ hET env hSt₂]
                    exact hR₂ env c₁ hR₁
                  have hPcF : PathCondHolds tblT env ((condId, false) :: pc) := by
                    refine ⟨?_, PathCondHolds.mono hValid₁ hET hPcValid₁ hPc₁⟩
                    show (evalSymId tblT env condId != 0) = false
                    rw [← evalSymId_mono hValid₁ hET env hCondLt]
                    exact hB
                  rcases hEvF env (c₁.ownerReadLoc discr) hPcF hR₂T with ⟨r, hr, hExec⟩
                  refine ⟨r, List.mem_append_right _ hr, ?_⟩
                  rw [ite_eq_right Bool.false_ne_true, hExec]
            cases hC : constCond? tbl₁ condId with
            | some b =>
              rw [hC] at hEval
              dsimp only at hEval
              have hB := constCond?_sound hValid₁ hC
              cases b with
              | true =>
                rw [ite_eq_left rfl] at hEval
                rcases symEvalCfgGvn_under_sound cfg hints fuel thenBb (st₁.ownerReadLoc discr) tbl₁
                  pc rets tbl' hValid₁ hSt₂ hPcValid₁ hEval with ⟨hV', hE', hLt', hEv'⟩
                refine ⟨hV', hExt₁.trans hE', hLt', ?_⟩
                intro env cst hPc hR
                rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                rcases hEv' env (c₁.ownerReadLoc discr) hPc₁ (hR₂ env c₁ hR₁) with ⟨r, hr, hExec⟩
                refine ⟨r, hr, ?_⟩
                rw [hStepC env cst c₁ hC₁ hR₁, hB env, ite_eq_left rfl]
                exact hExec
              | false =>
                rw [ite_eq_right Bool.false_ne_true] at hEval
                rcases symEvalCfgGvn_under_sound cfg hints fuel elseBb (st₁.ownerReadLoc discr) tbl₁
                  pc rets tbl' hValid₁ hSt₂ hPcValid₁ hEval with ⟨hV', hE', hLt', hEv'⟩
                refine ⟨hV', hExt₁.trans hE', hLt', ?_⟩
                intro env cst hPc hR
                rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                rcases hEv' env (c₁.ownerReadLoc discr) hPc₁ (hR₂ env c₁ hR₁) with ⟨r, hr, hExec⟩
                refine ⟨r, hr, ?_⟩
                rw [hStepC env cst c₁ hC₁ hR₁, hB env, ite_eq_right Bool.false_ne_true]
                exact hExec
            | none =>
              rw [hC] at hEval
              dsimp only at hEval
              by_cases hSameBb : thenBb = elseBb
              · rw [ite_eq_left hSameBb] at hEval
                rcases symEvalCfgGvn_under_sound cfg hints fuel thenBb (st₁.ownerReadLoc discr) tbl₁
                  pc rets tbl' hValid₁ hSt₂ hPcValid₁ hEval with ⟨hV', hE', hLt', hEv'⟩
                refine ⟨hV', hExt₁.trans hE', hLt', ?_⟩
                intro env cst hPc hR
                rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                rcases hEv' env (c₁.ownerReadLoc discr) hPc₁ (hR₂ env c₁ hR₁) with ⟨r, hr, hExec⟩
                refine ⟨r, hr, ?_⟩
                rw [hStepC env cst c₁ hC₁ hR₁, ← hSameBb]
                cases (evalSymId tbl₁ env condId != 0) <;> exact hExec
              · rw [ite_eq_right hSameBb] at hEval
                cases hPlan : diamondMergePlan cfg hints thenBb elseBb with
                | none =>
                  rw [hPlan] at hEval
                  dsimp only at hEval
                  cases hTri : triangleMergePlan cfg hints thenBb elseBb with
                  | none =>
                    rw [hTri] at hEval
                    exact hSplitCase hEval
                  | some plan =>
                    rcases plan with ⟨thenStmts, elseStmts, joinBb, mask⟩
                    rw [hTri] at hEval
                    cases fuel with
                    | zero => cases hEval
                    | succ f =>
                      dsimp only at hEval
                      cases hJoin : symExecDiamondJoin (st₁.ownerReadLoc discr) tbl₁ condId
                          thenStmts elseStmts mask pc with
                      | none => rw [hJoin] at hEval; cases hEval
                      | some pM =>
                        rcases pM with ⟨stM, tblM⟩
                        rw [hJoin] at hEval
                        dsimp only at hEval
                        rcases wpJoinBlock_under_sound hValid₁ hSt₂ hCondLt hPcValid₁ hJoin with
                          ⟨hVM, hEM, hStM, hJoinC⟩
                        have hPcValidM : PathCondValid tblM.nodes.length pc :=
                          hPcValid₁.mono hEM.length_le
                        rcases symEvalCfgGvn_under_sound cfg hints f joinBb stM tblM pc rets tbl'
                          hVM hStM hPcValidM hEval with ⟨hV', hE', hLt', hEv'⟩
                        refine ⟨hV', (hExt₁.trans hEM).trans hE', hLt', ?_⟩
                        intro env cst hPc hR
                        rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                        rcases hJoinC env (c₁.ownerReadLoc discr) hPc₁ (hR₂ env c₁ hR₁) with
                          ⟨c₂, hC₂, hR₂'⟩
                        have hPcM : PathCondHolds tblM env pc :=
                          PathCondHolds.mono hValid₁ hEM hPcValid₁ hPc₁
                        rcases hEv' env c₂ hPcM hR₂' with ⟨r, hr, hExec⟩
                        refine ⟨r, hr, ?_⟩
                        rw [hStepC env cst c₁ hC₁ hR₁]
                        rcases triangleMergePlan_spec hTri with
                          ⟨tBlk, hTB, hTS, hTT, hEJ, hES⟩ | ⟨eBlk, hEB, hES, hET, hTJ, hTS⟩
                        · -- Arm on the `then` side; the `else` successor is the join itself.
                          cases hB : (evalSymId tbl₁ env condId != 0) with
                          | true =>
                            rw [hB, ite_eq_left rfl] at hC₂
                            rw [ite_eq_left rfl]
                            dsimp only [execCfg]
                            rw [hTB]
                            dsimp only
                            rw [hTS, hC₂]
                            dsimp only
                            rw [hTT]
                            exact hExec
                          | false =>
                            rw [hB, ite_eq_right Bool.false_ne_true, hES] at hC₂
                            have hc : c₁.ownerReadLoc discr = c₂ := Option.some.inj hC₂
                            rw [ite_eq_right Bool.false_ne_true, hEJ, hc]
                            exact execCfg_ret_succ cfg f joinBb c₂ _ hExec
                        · -- Arm on the `else` side; the `then` successor is the join itself.
                          cases hB : (evalSymId tbl₁ env condId != 0) with
                          | true =>
                            rw [hB, ite_eq_left rfl, hTS] at hC₂
                            have hc : c₁.ownerReadLoc discr = c₂ := Option.some.inj hC₂
                            rw [ite_eq_left rfl, hTJ, hc]
                            exact execCfg_ret_succ cfg f joinBb c₂ _ hExec
                          | false =>
                            rw [hB, ite_eq_right Bool.false_ne_true] at hC₂
                            rw [ite_eq_right Bool.false_ne_true]
                            dsimp only [execCfg]
                            rw [hEB]
                            dsimp only
                            rw [hES, hC₂]
                            dsimp only
                            rw [hET]
                            exact hExec
                | some plan =>
                  rcases plan with ⟨thenStmts, elseStmts, joinBb, mask⟩
                  rw [hPlan] at hEval
                  cases fuel with
                  | zero => cases hEval
                  | succ f =>
                    dsimp only at hEval
                    cases hJoin : symExecDiamondJoin (st₁.ownerReadLoc discr) tbl₁ condId thenStmts
                        elseStmts mask pc with
                    | none => rw [hJoin] at hEval; cases hEval
                    | some pM =>
                      rcases pM with ⟨stM, tblM⟩
                      rw [hJoin] at hEval
                      dsimp only at hEval
                      rcases wpJoinBlock_under_sound hValid₁ hSt₂ hCondLt hPcValid₁ hJoin with
                        ⟨hVM, hEM, hStM, hJoinC⟩
                      have hPcValidM : PathCondValid tblM.nodes.length pc :=
                        hPcValid₁.mono hEM.length_le
                      rcases symEvalCfgGvn_under_sound cfg hints f joinBb stM tblM pc rets tbl'
                        hVM hStM hPcValidM hEval with ⟨hV', hE', hLt', hEv'⟩
                      rcases matchDiamond_spec (diamondMergePlan_spec hPlan) with
                        ⟨tBlk, eBlk, hTB, hEB, hTS, hES, hTT, hET⟩
                      refine ⟨hV', (hExt₁.trans hEM).trans hE', hLt', ?_⟩
                      intro env cst hPc hR
                      rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                      rcases hJoinC env (c₁.ownerReadLoc discr) hPc₁ (hR₂ env c₁ hR₁) with
                        ⟨c₂, hC₂, hR₂'⟩
                      have hPcM : PathCondHolds tblM env pc :=
                        PathCondHolds.mono hValid₁ hEM hPcValid₁ hPc₁
                      rcases hEv' env c₂ hPcM hR₂' with ⟨r, hr, hExec⟩
                      refine ⟨r, hr, ?_⟩
                      rw [hStepC env cst c₁ hC₁ hR₁]
                      cases hB : (evalSymId tbl₁ env condId != 0) with
                      | true =>
                        rw [hB, ite_eq_left rfl] at hC₂
                        rw [ite_eq_left rfl]
                        dsimp only [execCfg]
                        rw [hTB]
                        dsimp only
                        rw [hTS, hC₂]
                        dsimp only
                        rw [hTT]
                        exact hExec
                      | false =>
                        rw [hB, ite_eq_right Bool.false_ne_true] at hC₂
                        rw [ite_eq_right Bool.false_ne_true]
                        dsimp only [execCfg]
                        rw [hEB]
                        dsimp only
                        rw [hES, hC₂]
                        dsimp only
                        rw [hET]
                        exact hExec
        | switchTable discr cases otherwiseBb =>
          rw [hTerm] at hEval
          dsimp only at hEval
          cases hDiscr : readSymScalar st₁ discr with
          | none => rw [hDiscr] at hEval; cases hEval
          | some discrId =>
            rw [hDiscr] at hEval
            dsimp only at hEval
            have hDiscrLt : discrId < tbl₁.nodes.length := by
              have hSpec := readSymScalar_spec (fun _ => 0) hSt₁ (loc := discr)
              rw [hDiscr] at hSpec
              exact hSpec.1
            have hSt₂ : ValidSymCanonState tbl₁.nodes.length (st₁.ownerReadLoc discr) :=
              hSt₁.ownerReadLoc discr
            have hR₂ : ∀ env c₁, StateRefines (evalSymCanonState tbl₁ env st₁) c₁ →
                StateRefines (evalSymCanonState tbl₁ env (st₁.ownerReadLoc discr))
                  (c₁.ownerReadLoc discr) := by
              intro env c₁ hR₁
              rw [evalSymCanonState_ownerReadLoc]
              exact hR₁.ownerReadLoc discr
            have hStepT : ∀ env cst c₁, execStmts cst blk.stmts = some c₁ →
                StateRefines (evalSymCanonState tbl₁ env st₁) c₁ →
                execCfg cfg (fuel + 1) bb cst =
                  execCfg cfg fuel
                    (lookupCfgSwitchTarget (evalSymId tbl₁ env discrId) cases otherwiseBb)
                    (c₁.ownerReadLoc discr) := by
              intro env cst c₁ hC₁ hR₁
              have hSpec := readSymScalar_spec env hSt₁ (loc := discr)
              rw [hDiscr] at hSpec
              dsimp only [execCfg]
              rw [hBlk]
              dsimp only
              rw [hC₁]
              dsimp only
              rw [hTerm]
              dsimp only
              rw [readConcreteScalar_refines hR₁ hSpec.2]
            cases hConst : constSwitchTarget? tbl₁ discrId cases otherwiseBb
            case some targetBb =>
              rw [hConst] at hEval
              dsimp only at hEval
              rcases symEvalCfgGvn_under_sound cfg hints fuel targetBb (st₁.ownerReadLoc discr)
                tbl₁ pc rets tbl' hValid₁ hSt₂ hPcValid₁ hEval with ⟨hV', hE', hLt', hEv'⟩
              refine ⟨hV', hExt₁.trans hE', hLt', ?_⟩
              intro env cst hPc hR
              rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
              rcases hEv' env (c₁.ownerReadLoc discr) hPc₁ (hR₂ env c₁ hR₁) with ⟨r, hr, hExec⟩
              refine ⟨r, hr, ?_⟩
              rw [hStepT env cst c₁ hC₁ hR₁, constSwitchTarget?_sound hValid₁ hConst env]
              exact hExec
            rw [hConst] at hEval
            dsimp only at hEval
            cases hPlan : switchTableMergePlan cfg hints cases otherwiseBb with
            | none =>
              rw [hPlan] at hEval
              dsimp only at hEval
              cases hTriPlan : switchTableTrianglePlan cfg hints cases otherwiseBb with
              | none =>
                rw [hTriPlan] at hEval
                dsimp only at hEval
                have hBlockSound :
                    ∀ (targetBb : BlockId) (tblIn : SymTable) (pcIn : PathCond)
                      (retsOut : List SymId) (tblOut : SymTable),
                      ValidTable tblIn →
                      ValidSymCanonState tblIn.nodes.length (st₁.ownerReadLoc discr) →
                      PathCondValid tblIn.nodes.length pcIn →
                      symEvalCfgGvn cfg hints fuel targetBb (st₁.ownerReadLoc discr) tblIn pcIn =
                        some (retsOut, tblOut) →
                      ValidTable tblOut ∧ tblIn.Extends tblOut ∧
                        (∀ r ∈ retsOut, r < tblOut.nodes.length) ∧
                        ∀ (env : SymEnv) (cst₂ : CanonState Nat),
                          PathCondHolds tblIn env pcIn →
                          StateRefines (evalSymCanonState tblIn env (st₁.ownerReadLoc discr)) cst₂ →
                          ∃ r ∈ retsOut,
                            execCfg cfg fuel targetBb cst₂ = .ret (evalSymId tblOut env r) :=
                  fun targetBb tblIn pcIn retsOut tblOut hV hS hP hE =>
                    symEvalCfgGvn_under_sound cfg hints fuel targetBb (st₁.ownerReadLoc discr)
                      tblIn pcIn retsOut tblOut hV hS hP hE
                rcases evalSwitchTableSplit_sound hBlockSound cases otherwiseBb tbl₁ pc rets tbl'
                  hValid₁ hSt₂ hPcValid₁ hDiscrLt hEval with ⟨hV', hE', hLt', hEv'⟩
                refine ⟨hV', hExt₁.trans hE', hLt', ?_⟩
                intro env cst hPc hR
                rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                rcases hEv' env (c₁.ownerReadLoc discr)
                  hPc₁ (hR₂ env c₁ hR₁) with ⟨r, hr, hExec⟩
                refine ⟨r, hr, ?_⟩
                rw [hStepT env cst c₁ hC₁ hR₁]
                exact hExec
              | some triPlan =>
                rcases triPlan with ⟨caseArms, otherwiseStmts, joinBb, mask⟩
                rw [hTriPlan] at hEval
                cases fuel with
                | zero => cases hEval
                | succ f =>
                  dsimp only at hEval
                  cases hJoin : symExecSwitchTableJoin (st₁.ownerReadLoc discr) discrId mask
                      otherwiseStmts caseArms tbl₁ pc with
                  | none => rw [hJoin] at hEval; cases hEval
                  | some pM =>
                    rcases pM with ⟨stM, tblM⟩
                    rw [hJoin] at hEval
                    dsimp only at hEval
                    rcases wpSwitchTableJoin_under_sound caseArms hValid₁ hSt₂ hDiscrLt hPcValid₁
                      hJoin with ⟨hVM, hEM, hStM, hJoinC⟩
                    have hPcValidM : PathCondValid tblM.nodes.length pc :=
                      hPcValid₁.mono hEM.length_le
                    rcases symEvalCfgGvn_under_sound cfg hints f joinBb stM tblM pc rets tbl'
                      hVM hStM hPcValidM hEval with ⟨hV', hE', hLt', hEv'⟩
                    rcases switchTableTrianglePlan_spec hTriPlan with ⟨hO, hCases⟩
                    refine ⟨hV', (hExt₁.trans hEM).trans hE', hLt', ?_⟩
                    intro env cst hPc hR
                    rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                    rcases hJoinC env (c₁.ownerReadLoc discr) hPc₁ (hR₂ env c₁ hR₁) with
                      ⟨c₂, hC₂, hR₂'⟩
                    have hPcM : PathCondHolds tblM env pc :=
                      PathCondHolds.mono hValid₁ hEM hPcValid₁ hPc₁
                    rcases hEv' env c₂ hPcM hR₂' with ⟨r, hr, hExec⟩
                    refine ⟨r, hr, ?_⟩
                    rw [hStepT env cst c₁ hC₁ hR₁]
                    exact execCfg_lookupSwitchTarget_of_matchSwitchTriangleCases cases hCases hO hC₂ hExec
            | some plan =>
              rcases plan with ⟨caseArms, otherwiseStmts, joinBb, mask⟩
              rw [hPlan] at hEval
              cases fuel with
              | zero => cases hEval
              | succ f =>
                dsimp only at hEval
                cases hJoin : symExecSwitchTableJoin (st₁.ownerReadLoc discr) discrId mask
                    otherwiseStmts caseArms tbl₁ pc with
                | none => rw [hJoin] at hEval; cases hEval
                | some pM =>
                  rcases pM with ⟨stM, tblM⟩
                  rw [hJoin] at hEval
                  dsimp only at hEval
                  rcases wpSwitchTableJoin_under_sound caseArms hValid₁ hSt₂ hDiscrLt hPcValid₁
                    hJoin with ⟨hVM, hEM, hStM, hJoinC⟩
                  have hPcValidM : PathCondValid tblM.nodes.length pc :=
                    hPcValid₁.mono hEM.length_le
                  rcases symEvalCfgGvn_under_sound cfg hints f joinBb stM tblM pc rets tbl'
                    hVM hStM hPcValidM hEval with ⟨hV', hE', hLt', hEv'⟩
                  rcases switchTableMergePlan_spec hPlan with
                    ⟨oBlk, hOB, hOS, hOT, hCases⟩
                  refine ⟨hV', (hExt₁.trans hEM).trans hE', hLt', ?_⟩
                  intro env cst hPc hR
                  rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                  rcases hJoinC env (c₁.ownerReadLoc discr) hPc₁ (hR₂ env c₁ hR₁) with
                    ⟨c₂, hC₂, hR₂'⟩
                  have hPcM : PathCondHolds tblM env pc :=
                    PathCondHolds.mono hValid₁ hEM hPcValid₁ hPc₁
                  rcases hEv' env c₂ hPcM hR₂' with ⟨r, hr, hExec⟩
                  refine ⟨r, hr, ?_⟩
                  rw [hStepT env cst c₁ hC₁ hR₁]
                  rw [← hOS] at hC₂
                  rw [execCfg_lookupSwitchTarget_of_matchSwitchCases cases hCases hOB hOT hC₂]
                  exact hExec
        | ret retLoc =>
          rw [hTerm] at hEval
          dsimp only at hEval
          cases hRet : readSymScalar st₁ retLoc with
          | none => rw [hRet] at hEval; cases hEval
          | some rId =>
            rw [hRet] at hEval
            dsimp only at hEval
            injection hEval with hPair
            injection hPair with hR hT
            subst hR hT
            have hSpec0 := readSymScalar_spec (fun _ => 0) hSt₁ (loc := retLoc)
            rw [hRet] at hSpec0
            refine ⟨hValid₁, hExt₁, ?_, ?_⟩
            · intro r hr
              rw [List.mem_singleton] at hr
              subst hr
              exact hSpec0.1
            · intro env cst hPc hR
              rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, _⟩
              have hSpec := readSymScalar_spec env hSt₁ (loc := retLoc)
              rw [hRet] at hSpec
              refine ⟨rId, List.mem_singleton.2 rfl, ?_⟩
              dsimp only [execCfg]
              rw [hBlk]
              dsimp only
              rw [hC₁]
              dsimp only
              rw [hTerm]
              dsimp only
              rw [readConcreteScalar_refines hR₁ hSpec.2]
        | unreachable =>
          rw [hTerm] at hEval
          cases hEval

/-- **End-to-End Symbolic CFG Soundness (`symEvalCfgGvn_sound`)**, for every (untrusted)
    `hints` (`pc = []`). -/
theorem symEvalCfgGvn_sound (cfg : MirCfg) (hints : JoinHints)
    (fuel : Nat) (bb : BlockId) (st : CanonState SymId) (tbl : SymTable)
    (rets : List SymId) (tbl' : SymTable)
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hEval : symEvalCfgGvn cfg hints fuel bb st tbl = some (rets, tbl')) :
    CfgResultSound cfg fuel bb st tbl rets tbl' := by
  rcases symEvalCfgGvn_under_sound cfg hints fuel bb st tbl [] rets tbl' hValid hSt trivial hEval
    with ⟨hV, hE, hLt, hEv⟩
  exact ⟨hV, hE, hLt, fun env cst hR => hEv env cst trivial hR⟩

/-- Symbolic GVN + Canonical-Join Weakest Precondition (`wpCfgSymGvn`): evaluates `cfg`
    symbolically once and requires `post` of every returned `SymId` for all `env`. -/
def wpCfgSymGvn (cfg : MirCfg) (hints : JoinHints) (fuel : Nat) (bb : BlockId)
    (st : CanonState SymId) (tbl : SymTable) (post : SymEnv → Nat → Prop) : Prop :=
  match symEvalCfgGvn cfg hints fuel bb st tbl with
  | none => False
  | some (rets, tbl') => ∀ env : SymEnv, ∀ r ∈ rets, post env (evalSymId tbl' env r)

/-- **End-to-End WP Soundness (`wpCfgSymGvn_sound`)**: for every (untrusted) join hint map, if
    `wpCfgSymGvn` holds then, for every `env` and every concrete state refined by the evaluated
    symbolic entry state, the **mask-free** concrete execution never faults (no assertion
    failure, no read/write of a dead or uninitialized local, no stale-generation loan), never
    runs out of fuel, and returns a value satisfying `post`. -/
theorem wpCfgSymGvn_sound {cfg : MirCfg} {hints : JoinHints} {fuel : Nat} {bb : BlockId}
    {st : CanonState SymId} {tbl : SymTable} {post : SymEnv → Nat → Prop}
    (hValid : ValidTable tbl) (hSt : ValidSymCanonState tbl.nodes.length st)
    (hWp : wpCfgSymGvn cfg hints fuel bb st tbl post) :
    ∀ (env : SymEnv) (cst : CanonState Nat), StateRefines (evalSymCanonState tbl env st) cst →
      ∃ retVal : Nat, execCfg cfg fuel bb cst = .ret retVal ∧ post env retVal := by
  unfold wpCfgSymGvn at hWp
  cases hSym : symEvalCfgGvn cfg hints fuel bb st tbl with
  | none =>
    rw [hSym] at hWp
    exact False.elim hWp
  | some pair =>
    rcases pair with ⟨rets, tbl'⟩
    rw [hSym] at hWp
    rcases symEvalCfgGvn_sound cfg hints fuel bb st tbl rets tbl' hValid hSt hSym with
      ⟨_, _, _, hExec⟩
    intro env cst hR
    rcases hExec env cst hR with ⟨r, hr, hRet⟩
    exact ⟨_, hRet, hWp env r hr⟩

/-- `wpCfgSymGvn_sound` specialized to the exact evaluated symbolic entry state. -/
theorem wpCfgSymGvn_sound_init {cfg : MirCfg} {hints : JoinHints} {fuel : Nat} {bb : BlockId}
    {st : CanonState SymId} {tbl : SymTable} {post : SymEnv → Nat → Prop}
    (hValid : ValidTable tbl) (hSt : ValidSymCanonState tbl.nodes.length st)
    (hWp : wpCfgSymGvn cfg hints fuel bb st tbl post) (env : SymEnv) :
    ∃ retVal : Nat, execCfg cfg fuel bb (evalSymCanonState tbl env st) = .ret retVal ∧
      post env retVal :=
  wpCfgSymGvn_sound hValid hSt hWp env _ (StateRefines.refl _)

/-- Executable verification checker: run `symEvalCfgGvn`, GVN-intern the functional spec tree
    into the final table, and accept iff every returned `SymId` is GVN-identical to the spec's
    `SymId` (sound, incomplete syntactic equivalence check). -/
def checkCfgAgainstTree (cfg : MirCfg) (hints : JoinHints) (fuel : Nat) (bb : BlockId)
    (st : CanonState SymId) (tbl : SymTable) (spec : ExprTree) : Bool :=
  match symEvalCfgGvn cfg hints fuel bb st tbl with
  | none => false
  | some (rets, tbl') => rets.all (fun r => r == (internTree tbl' spec).1)

/-- **Checker Soundness (`checkCfgAgainstTree_sound`)**: an accepted check proves that the
    mask-free concrete execution returns exactly `spec.eval env` for every `env` and every
    refined concrete state. -/
theorem checkCfgAgainstTree_sound {cfg : MirCfg} {hints : JoinHints} {fuel : Nat} {bb : BlockId}
    {st : CanonState SymId} {tbl : SymTable} {spec : ExprTree}
    (hCheck : checkCfgAgainstTree cfg hints fuel bb st tbl spec = true)
    (hValid : ValidTable tbl) (hSt : ValidSymCanonState tbl.nodes.length st) :
    ∀ (env : SymEnv) (cst : CanonState Nat), StateRefines (evalSymCanonState tbl env st) cst →
      execCfg cfg fuel bb cst = .ret (spec.eval env) := by
  unfold checkCfgAgainstTree at hCheck
  cases hSym : symEvalCfgGvn cfg hints fuel bb st tbl with
  | none => rw [hSym] at hCheck; cases hCheck
  | some pair =>
    rcases pair with ⟨rets, tbl'⟩
    rw [hSym] at hCheck
    dsimp only at hCheck
    rcases symEvalCfgGvn_sound cfg hints fuel bb st tbl rets tbl' hValid hSt hSym with
      ⟨hV', _, hLt', hExec⟩
    rcases internTree_spec spec tbl' hV' with ⟨_, hExtS, _, hEvalS⟩
    intro env cst hR
    rcases hExec env cst hR with ⟨r, hr, hRet⟩
    have hrEq : r = (internTree tbl' spec).1 := beq_iff_eq.1 (List.all_eq_true.1 hCheck r hr)
    rw [hRet, evalSymId_mono hV' hExtS env (hLt' r hr), hrEq, hEvalS env]

/-!
### 3.6 Kernel-Checked `k`-Diamond Multi-Block CFG Benchmarks & Fault Witnesses (`by rfl`)
-/

/-- Diamond `i` of the benchmark CFG (blocks `3i`, `3i+1`, `3i+2`, joining at `3i+3`):
    - head `3i`: `switchInt _1 → 3i+1 | 3i+2` (symbolic discriminant `_1`),
    - then-arm `3i+1`: `StorageLive(_2); _2 := xor(_0, i+1); _0 := _2 + _2; goto 3i+3` — the
      branch-local temporary `_2` is left **live**, so the two arm states differ at the join
      (`_2` live vs. dead) and only join-point pruning (`_2 ∉` live mask) lets them merge,
    - else-arm `3i+2`: `_0 := xor(_0, i+1); _0 := _0 + _0; goto 3i+3` (never touches `_2`). -/
def mkDiamondBlocks (i : Nat) : List MirBlock :=
  [ { stmts := [], term := .switchInt 1 (3 * i + 1) (3 * i + 2) },
    { stmts := [ .storageLive 2, .assign 2 (.op1 (.xorConst (i + 1)) 0),
        .assign 0 (.op2 .add 2 2) ]
      term := .goto (3 * i + 3) },
    { stmts := [ .assign 0 (.op1 (.xorConst (i + 1)) 0), .assign 0 (.op2 .add 0 0) ]
      term := .goto (3 * i + 3) } ]

/-- `count` diamonds starting at diamond index `i`, followed by a return block that checks a
    GVN-recognizable reflexive assertion (`_2 := _0 == _0; assert _2`) and returns `_0`. -/
def mkDiamondBlocksAux : Nat → Nat → List MirBlock
  | _, 0 =>
    [ { stmts := [ .storageLive 2, .assign 2 (.op2 .eq 0 0), .assert 2, .storageDead 2 ]
        term := .ret 0 } ]
  | i, count + 1 => mkDiamondBlocks i ++ mkDiamondBlocksAux (i + 1) count

/-- The `k`-diamond MIR CFG (`3k + 1` blocks, `2^k` concrete paths). -/
def mkDiamondCfg (k : Nat) : MirCfg :=
  { blocks := mkDiamondBlocksAux 0 k }

/-- Untrusted join hints for `mkDiamondCfg`: every join block `3(i+1)` gets live mask
    `[true, true, false]` (`_0`, `_1` live; `_2` dead). -/
def diamondJoinHints : JoinHints := fun bb =>
  if bb % 3 == 0 && bb != 0 then some [true, true, false] else none

/-- No hints at all: the evaluator path-splits every diamond (`2^k` paths, GVN still shared). -/
def noJoinHints : JoinHints := fun _ => none

/-- Hints that keep every local live (no pruning): merging fails on the `_2` shape mismatch. -/
def noPruneJoinHints : JoinHints := fun bb =>
  if bb % 3 == 0 && bb != 0 then some [true, true, true] else none

/-- Initial symbolic state: `_0 ↦ SymId 0 (.var 0)`, `_1 ↦ SymId 1 (.var 1)`, `_2` dead. -/
def diamondInitSymState : CanonState SymId :=
  { slots := [.live 0 0 false none, .live 1 0 false none, .dead 0] }

def diamondInitSymTable : SymTable :=
  { nodes := [.var 0, .var 1] }

theorem diamondInitSymTable_valid : ValidTable diamondInitSymTable := by
  intro idx node hGet
  cases idx with
  | zero =>
    dsimp [diamondInitSymTable] at hGet
    injection hGet with hEq
    subst hEq
    trivial
  | succ i =>
    cases i with
    | zero =>
      dsimp [diamondInitSymTable] at hGet
      injection hGet with hEq
      subst hEq
      trivial
    | succ j =>
      dsimp [diamondInitSymTable] at hGet
      cases hGet

theorem diamondInitSymState_valid :
    ValidSymCanonState diamondInitSymTable.nodes.length diamondInitSymState :=
  ⟨Nat.zero_lt_succ 1, Nat.lt_succ_self 1, trivial, trivial⟩

/-- **5-Diamond Verification Benchmark (`diamond5_verified_rfl`)**: one symbolic pass
    (`2 * 5 + 1 = 11` blocks of fuel) proves the 5-diamond CFG (`2^5 = 32` concrete paths)
    returns exactly `(buildDiamondTree 5).eval env`. -/
theorem diamond5_verified_rfl :
    checkCfgAgainstTree (mkDiamondCfg 5) diamondJoinHints 11 0 diamondInitSymState
      diamondInitSymTable (buildDiamondTree 5) = true := by
  decide +kernel

/-- **6-Diamond Verification Benchmark (`diamond6_verified_rfl`)**: one symbolic pass verifies
    the 6-diamond CFG (`2^6 = 64` concrete paths) against `buildDiamondTree 6`. -/
theorem diamond6_verified_rfl :
    checkCfgAgainstTree (mkDiamondCfg 6) diamondJoinHints 13 0 diamondInitSymState
      diamondInitSymTable (buildDiamondTree 6) = true := by
  decide +kernel

/-- Single-continuation vs. path-splitting shape witness at `k = 6`: with join hints the
    evaluator returns **1** path and a `15`-node table; without hints it explores all **64**
    paths (GVN keeps the table at `15` nodes); with non-pruning hints the merge is rejected
    (`_2` is live in one arm and dead in the other), so join-point pruning is load-bearing. -/
theorem diamond6_join_vs_split_witness :
    (symEvalCfgGvn (mkDiamondCfg 6) diamondJoinHints 13 0 diamondInitSymState
        diamondInitSymTable).map (fun res => (res.1.length, res.2.nodes.length)) = some (1, 15) ∧
      (symEvalCfgGvn (mkDiamondCfg 6) noJoinHints 13 0 diamondInitSymState
        diamondInitSymTable).map (fun res => (res.1.length, res.2.nodes.length)) = some (64, 15) ∧
      symEvalCfgGvn (mkDiamondCfg 6) noPruneJoinHints 13 0 diamondInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- **End-to-End Concrete Corollary (`diamond6_cfg_concrete_sound`)**: for every `env`, the
    mask-free concrete execution of the 6-diamond CFG returns `(buildDiamondTree 6).eval env`. -/
theorem diamond6_cfg_concrete_sound (env : SymEnv) :
    execCfg (mkDiamondCfg 6) 13 0 (evalSymCanonState diamondInitSymTable env diamondInitSymState) =
      .ret ((buildDiamondTree 6).eval env) :=
  checkCfgAgainstTree_sound diamond6_verified_rfl diamondInitSymTable_valid
    diamondInitSymState_valid env _ (StateRefines.refl _)

/-- Triangle `i` of the `if`-without-`else` benchmark CFG (blocks `2i`, `2i+1`, joining at `2i+2`),
    the shape post-`SimplifyCfg` MIR gives `if c { … }` (no empty `else` block survives):
    - head `2i`: `switchInt _1 → 2i+1 | 2i+2` — the `else` successor **is** the join block,
    - arm `2i+1`: `StorageLive(_2); _2 := xor(_0, i+1); _0 := _2 + _2; goto 2i+2` (the temporary
      `_2` is left **live**, so only join-point pruning lets the two incoming states merge). -/
def mkTriangleBlocks (i : Nat) : List MirBlock :=
  [ { stmts := [], term := .switchInt 1 (2 * i + 1) (2 * i + 2) },
    { stmts := [ .storageLive 2, .assign 2 (.op1 (.xorConst (i + 1)) 0),
        .assign 0 (.op2 .add 2 2) ]
      term := .goto (2 * i + 2) } ]

/-- `count` triangles starting at triangle index `i`, followed by the same reflexive-assertion
    return block as `mkDiamondBlocksAux`. -/
def mkTriangleBlocksAux : Nat → Nat → List MirBlock
  | _, 0 =>
    [ { stmts := [ .storageLive 2, .assign 2 (.op2 .eq 0 0), .assert 2, .storageDead 2 ]
        term := .ret 0 } ]
  | i, count + 1 => mkTriangleBlocks i ++ mkTriangleBlocksAux (i + 1) count

/-- The `k`-triangle MIR CFG (`2k + 1` blocks, `2^k` concrete paths of different lengths). -/
def mkTriangleCfg (k : Nat) : MirCfg :=
  { blocks := mkTriangleBlocksAux 0 k }

/-- Untrusted join hints for `mkTriangleCfg`: every join block `2(i+1)` gets live mask
    `[true, true, false]` (`_0`, `_1` live; `_2` dead). -/
def triangleJoinHints : JoinHints := fun bb =>
  if bb % 2 == 0 && bb != 0 then some [true, true, false] else none

/-- Hints that keep every local live: the triangle merge fails on the `_2` shape mismatch. -/
def triangleNoPruneHints : JoinHints := fun bb =>
  if bb % 2 == 0 && bb != 0 then some [true, true, true] else none

/-- Functional spec of the `k`-triangle CFG: triangle `i + 1` replaces `_0` by
    `xor(_0, i+1) + xor(_0, i+1)` when `_1 ≠ 0` and keeps it otherwise. -/
def buildTriangleTree : Nat → ExprTree
  | 0 => .var 0
  | i + 1 =>
    let prev := buildTriangleTree i
    let br := ExprTree.op1 (.xorConst (i + 1)) prev
    .ite (.var 1) (.op2 .add br br) prev

/-- **6-Triangle Verification Benchmark (`triangle6_verified_rfl`)**: one symbolic pass
    (`2 * 6 + 1 = 13` blocks of fuel) proves the `if`-without-`else` CFG (`2^6 = 64` concrete paths)
    returns exactly `(buildTriangleTree 6).eval env`; the hinted triangle merge
    (`triangleMergePlan`) evaluates every join once. -/
theorem triangle6_verified_rfl :
    checkCfgAgainstTree (mkTriangleCfg 6) triangleJoinHints 13 0 diamondInitSymState
      diamondInitSymTable (buildTriangleTree 6) = true := by
  decide +kernel

/-- Single-continuation vs. path-splitting shape witness for triangles: with join hints the
    evaluator returns **1** path and a `21`-node table at `k = 6`; with non-pruning hints the
    `k = 6` merge is rejected (`_2` live vs. dead). Without hints it explores every path, and
    since the two sides of a triangle compute different values GVN cannot share them: the
    split comparison runs at `k = 4` (**16** paths, `33` nodes), because the unhinted `k = 6`
    evaluation (`64` paths, `129` nodes) exceeds the `-M2048` memory budget of the audit's
    kernel replay (`trusted/audit/check_trusted.py`). -/
theorem triangle6_join_vs_split_witness :
    (symEvalCfgGvn (mkTriangleCfg 6) triangleJoinHints 13 0 diamondInitSymState
        diamondInitSymTable).map (fun res => (res.1.length, res.2.nodes.length)) = some (1, 21) ∧
      (symEvalCfgGvn (mkTriangleCfg 4) noJoinHints 9 0 diamondInitSymState
        diamondInitSymTable).map (fun res => (res.1.length, res.2.nodes.length)) = some (16, 33) ∧
      symEvalCfgGvn (mkTriangleCfg 6) triangleNoPruneHints 13 0 diamondInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- **End-to-End Concrete Corollary (`triangle6_cfg_concrete_sound`)**: for every `env`, the
    mask-free concrete execution of the 6-triangle CFG returns `(buildTriangleTree 6).eval env`,
    although its paths consume between `7` and `13` blocks of the `13` available. -/
theorem triangle6_cfg_concrete_sound (env : SymEnv) :
    execCfg (mkTriangleCfg 6) 13 0 (evalSymCanonState diamondInitSymTable env diamondInitSymState) =
      .ret ((buildTriangleTree 6).eval env) :=
  checkCfgAgainstTree_sound triangle6_verified_rfl diamondInitSymTable_valid
    diamondInitSymState_valid env _ (StateRefines.refl _)

/-- Stage `i` of the 3-way `switchTable` benchmark CFG (blocks `4i`, `4i+1`, `4i+2`, `4i+3`,
    joining at `4i+4`):
    - head `4i`: `switchTable _1 [(0, 4i+1), (1, 4i+2)] (4i+3)` (3 targets!),
    - case `0` (`4i+1`): `StorageLive(_2); _2 := xor(_0, i+1); _0 := _2 + _2; goto 4i+4`
      (`_2` left **live**),
    - case `1` (`4i+2`): `StorageLive(_2); _2 := xor(_0, i+1); _0 := _2 + _2; StorageDead(_2); goto 4i+4`
      (`_2` killed),
    - `otherwise` (`4i+3`): `_0 := xor(_0, i+1); _0 := _0 + _0; goto 4i+4`
      (`_2` never touched). -/
def mkSwitchTableBlocks (i : Nat) : List MirBlock :=
  [ { stmts := [], term := .switchTable 1 [(0, 4 * i + 1), (1, 4 * i + 2)] (4 * i + 3) },
    { stmts := [ .storageLive 2, .assign 2 (.op1 (.xorConst (i + 1)) 0),
        .assign 0 (.op2 .add 2 2) ]
      term := .goto (4 * i + 4) },
    { stmts := [ .storageLive 2, .assign 2 (.op1 (.xorConst (i + 1)) 0),
        .assign 0 (.op2 .add 2 2), .storageDead 2 ]
      term := .goto (4 * i + 4) },
    { stmts := [ .assign 0 (.op1 (.xorConst (i + 1)) 0),
        .assign 0 (.op2 .add 0 0) ]
      term := .goto (4 * i + 4) } ]

def mkSwitchTableBlocksAux : Nat → Nat → List MirBlock
  | _, 0 =>
    [ { stmts := [ .storageLive 2, .assign 2 (.op2 .eq 0 0), .assert 2, .storageDead 2 ]
        term := .ret 0 } ]
  | i, count + 1 => mkSwitchTableBlocks i ++ mkSwitchTableBlocksAux (i + 1) count

/-- The `k`-stage 3-way `switchTable` MIR CFG (`4k + 1` blocks, `3^k` concrete paths). -/
def mkSwitchTableCfg (k : Nat) : MirCfg :=
  { blocks := mkSwitchTableBlocksAux 0 k }

def switchTableJoinHints : JoinHints := fun bb =>
  if bb % 4 == 0 && bb != 0 then some [true, true, false] else none

def switchTableNoPruneHints : JoinHints := fun bb =>
  if bb % 4 == 0 && bb != 0 then some [true, true, true] else none

/-- **4-Stage 3-Way `switchTable` Verification Benchmark (`switchTable4_verified_rfl`)**:
    One symbolic pass (`2 * 4 + 1 = 9` blocks of fuel) proves the 4-stage 3-way `switchTable` CFG
    (`3^4 = 81` concrete paths) returns `(buildDiamondTree 4).eval env`. -/
theorem switchTable4_verified_rfl :
    checkCfgAgainstTree (mkSwitchTableCfg 4) switchTableJoinHints 9 0 diamondInitSymState
      diamondInitSymTable (buildDiamondTree 4) = true := by
  decide +kernel

/-- Single-continuation vs. path-splitting shape witness for 3-way `switchTable` at `k = 4`:
    - with `switchTableJoinHints`: **1** path (all 3 arms at each stage merge into a single shared
      GVN node via `ite c x x ↦ x`),
    - without hints (`noJoinHints`): **81** paths (`3^4`),
    - with non-pruning hints (`switchTableNoPruneHints`): `none` (`_2` liveness mismatch rejected). -/
theorem switchTable4_join_vs_split_witness :
    (symEvalCfgGvn (mkSwitchTableCfg 4) switchTableJoinHints 9 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 1 ∧
      (symEvalCfgGvn (mkSwitchTableCfg 4) noJoinHints 9 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 81 ∧
      symEvalCfgGvn (mkSwitchTableCfg 4) switchTableNoPruneHints 9 0 diamondInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- **End-to-End Concrete Corollary for 3-Way `switchTable` (`switchTable4_cfg_concrete_sound`)**:
    for every `env`, the mask-free concrete execution of `mkSwitchTableCfg 4` returns
    `(buildDiamondTree 4).eval env`. -/
theorem switchTable4_cfg_concrete_sound (env : SymEnv) :
    execCfg (mkSwitchTableCfg 4) 9 0
      (evalSymCanonState diamondInitSymTable env diamondInitSymState) =
      .ret ((buildDiamondTree 4).eval env) :=
  checkCfgAgainstTree_sound switchTable4_verified_rfl diamondInitSymTable_valid
    diamondInitSymState_valid env _ (StateRefines.refl _)

/-- 3-way `switchTable` CFG whose 3 arms compute **distinct** values (`_0 + 10` on `_1 == 0`,
    `_0 + 20` on `_1 == 1`, `_0 + 30` otherwise) and converge at `bb 4` (`_0 := _0 + _1; ret _0`). -/
def distinctSwitchTableCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchTable 1 [(0, 1), (1, 2)] 3 },
        { stmts := [ .storageLive 2, .assign 2 (.op1 (.addConst 10) 0), .assign 0 (.use 2) ]
          term := .goto 4 },
        { stmts := [ .assign 0 (.op1 (.addConst 20) 0) ]
          term := .goto 4 },
        { stmts := [ .assign 0 (.op1 (.addConst 30) 0) ]
          term := .goto 4 },
        { stmts := [ .assign 0 (.op2 .add 0 1) ]
          term := .ret 0 } ] }

def distinctSwitchTableTree : ExprTree :=
  let armTree :=
    ExprTree.ite (.op2 .eq (.var 1) (.const 0))
      (.op1 (.addConst 10) (.var 0))
      (.ite (.op2 .eq (.var 1) (.const 1))
        (.op1 (.addConst 20) (.var 0))
        (.op1 (.addConst 30) (.var 0)))
  .op2 .add armTree (.var 1)

theorem distinctSwitchTable_verified_rfl :
    checkCfgAgainstTree distinctSwitchTableCfg (fun bb => if bb == 4 then some [true, true, false] else none)
      3 0 diamondInitSymState diamondInitSymTable distinctSwitchTableTree = true := by
  decide +kernel

theorem distinctSwitchTable_concrete_sound (env : SymEnv) :
    execCfg distinctSwitchTableCfg 3 0
      (evalSymCanonState diamondInitSymTable env diamondInitSymState) =
      .ret (distinctSwitchTableTree.eval env) :=
  checkCfgAgainstTree_sound distinctSwitchTable_verified_rfl diamondInitSymTable_valid
    diamondInitSymState_valid env _ (StateRefines.refl _)

/-- Unhinted `switchTable` whose `3 =>` arm asserts its own case condition
    (`_2 := 3; _2 := _1 == _2; assert _2`) before returning `_0`; `otherwise` returns `_0`. -/
def switchCaseAssertCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchTable 1 [(3, 1)] 2 },
        { stmts := [ .storageLive 2, .assign 2 (.const 3), .assign 2 (.op2 .eq 1 2), .assert 2,
            .storageDead 2 ]
          term := .ret 0 },
        { stmts := [], term := .ret 0 } ] }

/-- The same `switchTable`, but the `otherwise` arm asserts `_1 == 3`, which is false there. -/
def switchOtherwiseAssertCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchTable 1 [(3, 1)] 2 },
        { stmts := [], term := .ret 0 },
        { stmts := [ .storageLive 2, .assign 2 (.const 3), .assign 2 (.op2 .eq 1 2), .assert 2,
            .storageDead 2 ]
          term := .ret 0 } ] }

/-- **Case path conditions on path-split `switchTable` arms (`switchCase_pathCond_verified`)**:
    without join hints, the evaluator explores both `switchTable` targets, and the `3 =>` arm is
    explored under `_1 == 3` (`evalSwitchTableSplit`), so its assertion is discharged and both paths
    return `_0`; the same assertion in the `otherwise` arm (where it is false) is rejected. -/
theorem switchCase_pathCond_verified :
    checkCfgAgainstTree switchCaseAssertCfg noJoinHints 2 0 diamondInitSymState
        diamondInitSymTable (.var 0) = true ∧
      (symEvalCfgGvn switchCaseAssertCfg noJoinHints 2 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 2 ∧
      symEvalCfgGvn switchOtherwiseAssertCfg noJoinHints 2 0 diamondInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- Concrete corollary: for every `env`, the `3 =>` arm's assertion never fails and the CFG
    returns `_0`. -/
theorem switchCaseAssert_concrete_sound (env : SymEnv) :
    execCfg switchCaseAssertCfg 2 0
      (evalSymCanonState diamondInitSymTable env diamondInitSymState) =
      .ret ((ExprTree.var 0).eval env) :=
  checkCfgAgainstTree_sound switchCase_pathCond_verified.1 diamondInitSymTable_valid
    diamondInitSymState_valid env _ (StateRefines.refl _)

/-- `switchTable` on a **constant** discriminant (`_2 := 5; switchTable _2 [(3, bb1)] bb2`), whose
    infeasible `3 =>` arm asserts `false` (`_2 := 0; assert _2`). Exploring or merging that arm would
    reject the CFG; `constSwitchTarget?` folds the switch to `bb2`. -/
def constSwitchTableCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .storageLive 2, .assign 2 (.const 5) ], term := .switchTable 2 [(3, 1)] 2 },
        { stmts := [ .assign 2 (.const 0), .assert 2 ], term := .ret 0 },
        { stmts := [], term := .ret 0 } ] }

/-- **Constant-discriminant `switchTable` folding (`constSwitchTable_folded_verified`)**: with and
    without join hints, the evaluator follows only the statically selected target (**1** path), so
    the infeasible arm's `assert false` is never explored; the CFG returns `_0`. -/
theorem constSwitchTable_folded_verified :
    checkCfgAgainstTree constSwitchTableCfg noJoinHints 2 0 diamondInitSymState
        diamondInitSymTable (.var 0) = true ∧
      (symEvalCfgGvn constSwitchTableCfg noJoinHints 2 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 1 ∧
      (symEvalCfgGvn constSwitchTableCfg (fun bb => if bb == 2 then some [true, true, false] else none)
        2 0 diamondInitSymState diamondInitSymTable).map (fun res => res.1.length) = some 1 := by
  decide +kernel

/-- Concrete corollary: for every `env`, the constant-discriminant `switchTable` returns `_0`. -/
theorem constSwitchTable_concrete_sound (env : SymEnv) :
    execCfg constSwitchTableCfg 2 0
      (evalSymCanonState diamondInitSymTable env diamondInitSymState) =
      .ret ((ExprTree.var 0).eval env) :=
  checkCfgAgainstTree_sound constSwitchTable_folded_verified.1 diamondInitSymTable_valid
    diamondInitSymState_valid env _ (StateRefines.refl _)

/-- 3-way `switchTable` on `_1` (`3 => bb1 | 5 => bb2 | otherwise => bb3`) converging at `bb4`:
    - `bb1` asserts `_1 == 3`,
    - `bb2` asserts `_1 == 5` AND the negated prior case `!(_1 == 3)`,
    - `bb3` (`otherwise`) asserts BOTH negated prior cases `!(_1 == 3)` AND `!(_1 == 5)`. -/
def switchOtherwiseNegatedCaseCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchTable 1 [(3, 1), (5, 2)] 3 },
        { stmts :=
            [ .storageLive 2,
              .assign 2 (.const 3),
              .assign 2 (.op2 .eq 1 2),
              .assert 2,
              .storageDead 2,
              .assign 0 (.op1 (.addConst 10) 0) ]
          term := .goto 4 },
        { stmts :=
            [ .storageLive 2,
              .assign 2 (.const 5),
              .assign 2 (.op2 .eq 1 2),
              .assert 2,
              .assign 2 (.const 3),
              .assign 2 (.op2 .eq 1 2),
              .assign 2 (.op1 .boolNot 2),
              .assert 2,
              .storageDead 2,
              .assign 0 (.op1 (.addConst 10) 0) ]
          term := .goto 4 },
        { stmts :=
            [ .storageLive 2,
              .assign 2 (.const 3),
              .assign 2 (.op2 .eq 1 2),
              .assign 2 (.op1 .boolNot 2),
              .assert 2,
              .assign 2 (.const 5),
              .assign 2 (.op2 .eq 1 2),
              .assign 2 (.op1 .boolNot 2),
              .assert 2,
              .storageDead 2,
              .assign 0 (.op1 (.addConst 10) 0) ]
          term := .goto 4 },
        { stmts := [], term := .ret 0 } ] }

/-- **Negated Prior-Case Path Conditions in `switchTable` Subsequent & `otherwise` Arms
    (`switchOtherwiseNegatedCase_verified`)**:
    Both `symExecSwitchTableJoin` (merged at `bb4`, `1` path) and `evalSwitchTableSplit`
    (path-split without hints, `3` paths) thread `(eqId, false) :: pc` across subsequent cases and
    into `otherwise`, discharging `assert(!(_1 == 3))` in `5 =>` and
    `assert(!(_1 == 3) && !(_1 == 5))` in `otherwise`. -/
theorem switchOtherwiseNegatedCase_verified :
    let hints : JoinHints := fun bb => if bb == 4 then some [true, true, false] else none
    (symEvalCfgGvn switchOtherwiseNegatedCaseCfg hints 3 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 1 ∧
      checkCfgAgainstTree switchOtherwiseNegatedCaseCfg hints 3 0 diamondInitSymState
        diamondInitSymTable (.op1 (.addConst 10) (.var 0)) = true ∧
      (symEvalCfgGvn switchOtherwiseNegatedCaseCfg noJoinHints 3 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 3 ∧
      checkCfgAgainstTree switchOtherwiseNegatedCaseCfg noJoinHints 3 0 diamondInitSymState
        diamondInitSymTable (.op1 (.addConst 10) (.var 0)) = true := by
  decide +kernel

theorem switchOtherwiseNegatedCase_concrete_sound (env : SymEnv) :
    execCfg switchOtherwiseNegatedCaseCfg 3 0
      (evalSymCanonState diamondInitSymTable env diamondInitSymState) =
      .ret ((ExprTree.op1 (.addConst 10) (.var 0)).eval env) :=
  checkCfgAgainstTree_sound switchOtherwiseNegatedCase_verified.2.1 diamondInitSymTable_valid
    diamondInitSymState_valid env _ (StateRefines.refl _)

/-- N-way `switchTable` triangle (`3 => bb1 | 5 => bb2 | otherwise => bb2`) where `bb1` executes
    `_0 := _0 + 10; goto bb2` while BOTH `5 => bb2` and `otherwise => bb2` jump **directly** to the
    join block `bb2` (`ret 0`), the post-`SimplifyCfg` MIR shape of `match _1 { 3 => _0 += 10, 5 | _ => {} }`. -/
def switchTableTriangleCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchTable 1 [(3, 1), (5, 2)] 2 },
        { stmts := [ .assign 0 (.op1 (.addConst 10) 0) ], term := .goto 2 },
        { stmts := [], term := .ret 0 } ] }

def switchTableTriangleTree : ExprTree :=
  .ite (.op2 .eq (.var 1) (.const 3))
    (.op1 (.addConst 10) (.var 0))
    (.var 0)

/-- **N-Way `switchTable` Triangle Merge Witness (`switchTableTriangle_verified`)**:
    `switchTableTrianglePlan` merges the arm block `3 => bb1` with the direct-to-join edges
    `5 => bb2` and `otherwise => bb2` into **1** path at `bb2` (vs. `3` paths without hints). -/
theorem switchTableTriangle_verified :
    let hints : JoinHints := fun bb => if bb == 2 then some [true, true, false] else none
    (symEvalCfgGvn switchTableTriangleCfg hints 3 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 1 ∧
      checkCfgAgainstTree switchTableTriangleCfg hints 3 0 diamondInitSymState
        diamondInitSymTable switchTableTriangleTree = true ∧
      (symEvalCfgGvn switchTableTriangleCfg noJoinHints 3 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 3 := by
  decide +kernel

theorem switchTableTriangle_concrete_sound (env : SymEnv) :
    execCfg switchTableTriangleCfg 3 0
      (evalSymCanonState diamondInitSymTable env diamondInitSymState) =
      .ret (switchTableTriangleTree.eval env) :=
  checkCfgAgainstTree_sound switchTableTriangle_verified.2.1 diamondInitSymTable_valid
    diamondInitSymState_valid env _ (StateRefines.refl _)

/-- Nested `switchInt` CFG: outer `switchInt _1 -> 1 | 2` where `bb1` (`_1 != 0`) branches on
    inner `switchInt _0 -> 3 | 4` converging at `bb5` (`ret 0`), and `bb3`/`bb4` assert **both**
    the outer branch condition `_1` and their respective inner branch condition (`_0` / `!_0`). -/
def nestedBranchCondAssertCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchInt 1 1 2 },
        { stmts := [], term := .switchInt 0 3 4 },
        { stmts :=
            [ .storageLive 2,
              .assign 2 (.op1 .boolNot 1),
              .assert 2,
              .storageDead 2,
              .assign 0 (.use 1) ]
          term := .goto 5 },
        { stmts := [ .assert 1, .assert 0, .assign 0 (.use 1) ], term := .goto 5 },
        { stmts :=
            [ .assert 1,
              .storageLive 2,
              .assign 2 (.op1 .boolNot 0),
              .assert 2,
              .storageDead 2,
              .assign 0 (.use 1) ]
          term := .goto 5 },
        { stmts := [], term := .ret 0 } ] }

/-- **Conjunctive Nested Branch-Condition Witness (`nestedBranchCondAssert_verified`)**:
    Because `PathCond` is a conjunctive stack `List (SymId × Bool)`, inner diamond arms (`bb3`,
    `bb4`) retain the outer branch literal `(_1, true)` alongside their inner branch literal
    (`(_0, true)` / `(_0, false)`), both when `bb5` is merged (`2` paths) and when path-split
    without hints (`3` paths). -/
theorem nestedBranchCondAssert_verified :
    let hints : JoinHints := fun bb => if bb == 5 then some [true, true, false] else none
    (symEvalCfgGvn nestedBranchCondAssertCfg hints 4 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 2 ∧
      checkCfgAgainstTree nestedBranchCondAssertCfg hints 4 0 diamondInitSymState
        diamondInitSymTable (.var 1) = true ∧
      (symEvalCfgGvn nestedBranchCondAssertCfg noJoinHints 4 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 3 ∧
      checkCfgAgainstTree nestedBranchCondAssertCfg noJoinHints 4 0 diamondInitSymState
        diamondInitSymTable (.var 1) = true := by
  decide +kernel

theorem nestedBranchCondAssert_concrete_sound (env : SymEnv) :
    execCfg nestedBranchCondAssertCfg 4 0
      (evalSymCanonState diamondInitSymTable env diamondInitSymState) =
      .ret ((ExprTree.var 1).eval env) :=
  checkCfgAgainstTree_sound nestedBranchCondAssert_verified.2.1 diamondInitSymTable_valid
    diamondInitSymState_valid env _ (StateRefines.refl _)

/-- Diamond whose arms compute the same sum with swapped operands:
    then-arm `_0 := _0 + _1`, else-arm `_0 := _1 + _0`. -/
def commDiamondCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchInt 1 1 2 },
        { stmts := [ .assign 0 (.op2 .add 0 1) ], term := .goto 3 },
        { stmts := [ .assign 0 (.op2 .add 1 0) ], term := .goto 3 },
        { stmts := [], term := .ret 0 } ] }

/-- **Commutative GVN at a Join (`commDiamond_shared_join_witness`)**: thanks to canonical
    operand order both arms intern the *same* `SymId` for `_0`, so the merge allocates no `ite`
    node (table stays at `3` nodes) and the program verifies against `x₁ + x₀`. -/
theorem commDiamond_shared_join_witness :
    (symEvalCfgGvn commDiamondCfg (fun _ => some [true, true, false]) 3 0 diamondInitSymState
        diamondInitSymTable).map (fun res => (res.1, res.2.nodes.length)) = some ([2], 3) ∧
      checkCfgAgainstTree commDiamondCfg (fun _ => some [true, true, false]) 3 0
        diamondInitSymState diamondInitSymTable (.op2 .add (.var 1) (.var 0)) = true := by
  decide +kernel

/-- 4-local initial state for the fault / borrow witnesses: `_0`, `_1` live inputs, `_2`, `_3`
    declared but uninitialized. -/
def borrowInitSymState : CanonState SymId :=
  { slots := [.live 0 0 false none, .live 1 0 false none, .uninit 0, .uninit 0] }

theorem borrowInitSymState_valid :
    ValidSymCanonState diamondInitSymTable.nodes.length borrowInitSymState :=
  ⟨Nat.zero_lt_succ 1, Nat.lt_succ_self 1, trivial, trivial, trivial⟩

/-- Writes `_1` after `StorageDead(_1)` (use-after-dead write). -/
def deadWriteCfg : MirCfg :=
  { blocks := [ { stmts := [.storageDead 1, .assign 1 (.const 7)], term := .ret 0 } ] }

/-- Takes `_2 := &_1`, recycles `_1`'s storage (`StorageDead`/`StorageLive`), re-borrows the
    new incarnation (`_3 := &_1`), then dereferences the **stale** loan `_2`. -/
def staleLoanCfg : MirCfg :=
  { blocks := [ { stmts := [ .retagBorrow 2 1, .storageDead 1, .storageLive 1,
      .assign 1 (.const 5), .retagBorrow 3 1, .assign 0 (.derefRef 2) ], term := .ret 0 } ] }

/-- Fresh-loan dereference: `_2 := &_1; _0 := *_2; return _0`. -/
def freshLoanCfg : MirCfg :=
  { blocks := [ { stmts := [ .retagBorrow 2 1, .assign 0 (.derefRef 2) ], term := .ret 0 } ] }

/-- **Fault Non-Vacuity Witnesses**: the concrete semantics genuinely faults on a dead-local
    write and on a stale-generation dereference (even after the target is re-borrowed, so the
    borrow flag alone would not catch it), the symbolic evaluator rejects both programs, and
    a fresh loan verifies (returns `_1`). -/
theorem fault_and_loan_witnesses :
    execCfg deadWriteCfg 1 0 (evalSymCanonState diamondInitSymTable (fun _ => 3)
        borrowInitSymState) = .fault ∧
      symEvalCfgGvn deadWriteCfg noJoinHints 1 0 borrowInitSymState diamondInitSymTable = none ∧
      execCfg staleLoanCfg 1 0 (evalSymCanonState diamondInitSymTable (fun _ => 3)
        borrowInitSymState) = .fault ∧
      symEvalCfgGvn staleLoanCfg noJoinHints 1 0 borrowInitSymState diamondInitSymTable = none ∧
      checkCfgAgainstTree freshLoanCfg noJoinHints 1 0 borrowInitSymState diamondInitSymTable
        (.var 1) = true := by
  decide +kernel

/-- Diamond whose then-arm borrows the branch-local `_2` and kills it (bumping its
    borrow-dirtied generation to `1`), while the else-arm leaves `_2` dead at generation `0`. -/
def borrowGenDiamondCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchInt 1 1 2 },
        { stmts := [ .storageLive 2, .assign 2 (.use 0), .retagBorrow 3 2, .storageDead 2 ]
          term := .goto 3 },
        { stmts := [], term := .goto 3 },
        { stmts := [], term := .ret 0 } ] }

/-- **Borrow-Generation Join Witness**: the generation mismatch on dead `_2` (`1` vs. `0`) makes
    the canonical merge fail — the join never conflates distinct storage incarnations — while
    path-splitting still verifies the program returns `_0`. -/
theorem borrowGen_join_rejected_split_verified :
    symEvalCfgGvn borrowGenDiamondCfg (fun _ => some [true, true, false, false]) 3 0
        borrowInitSymState diamondInitSymTable = none ∧
      checkCfgAgainstTree borrowGenDiamondCfg noJoinHints 3 0 borrowInitSymState
        diamondInitSymTable (.var 0) = true := by
  decide +kernel

/-- Write **and** read through the same fresh loan: `_2 := &_1; *_2 := _0 + 10; _0 := *_2`. -/
def freshStoreRefCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .storeRef 2 (.op1 (.addConst 10) 0),
              .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- Co-aliased loans, write through the older one, read through the newer one:
    `_2 := &_1; _3 := &_1; *_2 := _0 + 10; _0 := *_3`. Under the model's unique-loan (Stacked
    Borrows `&mut`) discipline the retag of `_3` already invalidates `_2`, so the write through
    `_2` faults. (Tree Borrows would allow that write — `_2` is still `Reserved` — but it is a
    foreign write that disables `_3`, so the final read is UB there too.) -/
def freshStoreRefAliasCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .retagBorrow 3 1,
              .storeRef 2 (.op1 (.addConst 10) 0),
              .assign 0 (.derefRef 3) ]
          term := .ret 0 } ] }

/-- An owner write invalidates outstanding loans: `_2 := &_1; _1 := 5; _0 := *_2`. -/
def ownerWriteInvalidatesCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .assign 1 (.const 5), .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- Indirect write through a **stale** loan (`_2 := &_1`, recycle `_1` via `StorageDead`/
    `StorageLive`, re-borrow `_3 := &_1`, then attempt `*_2 := _0`). -/
def staleStoreRefCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .storageDead 1,
              .storageLive 1,
              .assign 1 (.const 5),
              .retagBorrow 3 1,
              .storeRef 2 (.use 0) ]
          term := .ret 1 } ] }

/-- **Write-Through-Reference (`storeRef`) Aliasing Discipline Witness**:
    1. writing `*_2 := _0 + 10` and reading back through the same loan verifies
       (`= _0 + 10` for every input);
    2. with co-aliased loans `_2`, `_3` to `_1`, the program faults concretely and is rejected
       symbolically (the re-borrow `_3 := &_1` invalidates `_2`, so `*_2 := …` faults);
    3. an owner write (`_1 := 5`) invalidates the outstanding loan `_2` likewise;
    4. a write through a loan whose target storage was recycled faults and is rejected. -/
theorem storeRef_mutation_and_stale_fault_witness :
    checkCfgAgainstTree freshStoreRefCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable (.op1 (.addConst 10) (.var 0)) = true ∧
      execCfg freshStoreRefAliasCfg 1 0 (evalSymCanonState diamondInitSymTable (fun _ => 3)
        borrowInitSymState) = .fault ∧
      symEvalCfgGvn freshStoreRefAliasCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg ownerWriteInvalidatesCfg 1 0 (evalSymCanonState diamondInitSymTable (fun _ => 3)
        borrowInitSymState) = .fault ∧
      symEvalCfgGvn ownerWriteInvalidatesCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg staleStoreRefCfg 1 0 (evalSymCanonState diamondInitSymTable (fun _ => 3)
        borrowInitSymState) = .fault ∧
      symEvalCfgGvn staleStoreRefCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- Legal owner read after loan use is finished: `_2 := &_1; *_2 := _0 + 10; _0 := _1`. -/
def ownerReadAfterStoreRefValidCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .storeRef 2 (.op1 (.addConst 10) 0),
              .assign 0 (.use 1) ]
          term := .ret 0 } ] }

/-- Owner read of a borrowed local invalidates the loan (`_2 := &_1; _0 := _1; _0 := *_2`). -/
def ownerReadInvalidatesLoanDerefCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .assign 0 (.use 1), .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- Owner read of a borrowed local invalidates a subsequent indirect write
    (`_2 := &_1; _0 := _1; *_2 := 9`). -/
def ownerReadInvalidatesLoanStoreCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .assign 0 (.use 1), .storeRef 2 (.const 9) ]
          term := .ret 1 } ] }

/-- **Owner-Read Loan Invalidation Witness (`owner_read_invalidation_witness`)**:
    1. Writing through `_2 = &_1` and then reading `_1` through its owner (without using `_2`
       afterward) is legal and verifies (`= _0 + 10` for all inputs);
    2. Reading `_1` through its owner bumps `_1`'s borrow generation (`Slot.ownerRead`), so
       either reading (`*_2`) or writing (`*_2 := 9`) through `_2` afterward faults in
       `execCfg` and is rejected (`none`) by `symEvalCfgGvn`. -/
theorem owner_read_invalidation_witness :
    checkCfgAgainstTree ownerReadAfterStoreRefValidCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable (.op1 (.addConst 10) (.var 0)) = true ∧
      execCfg ownerReadInvalidatesLoanDerefCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn ownerReadInvalidatesLoanDerefCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg ownerReadInvalidatesLoanStoreCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn ownerReadInvalidatesLoanStoreCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- Owner read through a `switchInt` discriminant while a loan is live:
    `_2 := &_1; switchInt _1 → bb1 | bb2`, and both arms then read through `_2` (`_0 := *_2`). -/
def switchOwnerReadDerefCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1 ], term := .switchInt 1 1 2 },
        { stmts := [ .assign 0 (.derefRef 2) ], term := .ret 0 },
        { stmts := [ .assign 0 (.derefRef 2) ], term := .ret 0 } ] }

/-- The loan is finished before the `switchInt` reads its target (legal):
    `_2 := &_1; *_2 := _0 + 10; switchInt _1 → bb1 | bb2`, both arms `return _1`. -/
def switchOwnerReadValidCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .storeRef 2 (.op1 (.addConst 10) 0) ],
          term := .switchInt 1 1 2 },
        { stmts := [], term := .ret 1 },
        { stmts := [], term := .ret 1 } ] }

/-- Write through a loan, re-borrow the target, then write through the **old** loan:
    `_2 := &_1; *_2 := 5; _3 := &_1; *_2 := 6`. UB under Stacked Borrows (the retag of `_3`
    pops `_2`) and under Tree Borrows (the retag's read access freezes the `Active` `_2`). -/
def reborrowInvalidatesOldLoanCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .storeRef 2 (.const 5), .retagBorrow 3 1,
            .storeRef 2 (.const 6) ]
          term := .ret 1 } ] }

/-- The newest loan stays usable after a re-borrow:
    `_2 := &_1; _3 := &_1; *_3 := _0 + 1; _0 := *_3`. -/
def reborrowNewLoanValidCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .retagBorrow 3 1, .storeRef 3 (.op1 (.addConst 1) 0),
            .assign 0 (.derefRef 3) ]
          term := .ret 0 } ] }

/-- **Discriminant-Read & Re-Borrow Loan Invalidation Witness
    (`switch_and_reborrow_loan_invalidation_witness`)**:
    1. a `switchInt` on a borrowed local is an owner read: using the loan in either arm faults
       concretely (for a non-zero and a zero discriminant) and is rejected symbolically, while
       finishing the loan before the `switchInt` verifies (`= _0 + 10` on both paths);
    2. re-borrowing a target invalidates every earlier loan to it (`_2` after `_3 := &_1`
       faults and is rejected), while the newest loan verifies (`= _0 + 1`). -/
theorem switch_and_reborrow_loan_invalidation_witness :
    checkCfgAgainstTree switchOwnerReadValidCfg noJoinHints 2 0 borrowInitSymState
        diamondInitSymTable (.op1 (.addConst 10) (.var 0)) = true ∧
      execCfg switchOwnerReadDerefCfg 2 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      execCfg switchOwnerReadDerefCfg 2 0
        (evalSymCanonState diamondInitSymTable (fun _ => 0) borrowInitSymState) = .fault ∧
      symEvalCfgGvn switchOwnerReadDerefCfg noJoinHints 2 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg reborrowInvalidatesOldLoanCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn reborrowInvalidatesOldLoanCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      checkCfgAgainstTree reborrowNewLoanValidCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable (.op1 (.addConst 1) (.var 0)) = true := by
  decide +kernel

/-- Borrowing the pointer local `_2` itself (`_3 := &_2`) and then writing through `*_2`
    (`storeRef 2 (.const 9)`) performs an owner read on `_2`, invalidating `_3`'s loan to `_2`
    so a subsequent `_0 := *_3` faults. -/
def storeRefPtrOwnerReadInvalidatesLoanCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .retagBorrow 3 2,
              .storeRef 2 (.const 9),
              .assign 0 (.derefRef 3) ]
          term := .ret 0 } ] }

/-- Borrowing `_2` (`_3 := &_2`), writing through `*_2 := _0 + 9`, and reading back through `_2`
    itself (`_0 := *_2`, without touching the invalidated `_3`) succeeds and returns `_0 + 9`. -/
def storeRefPtrOwnerReadValidSelfCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .retagBorrow 3 2,
              .storeRef 2 (.op1 (.addConst 9) 0),
              .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- **Pointer-Local Owner-Read Invalidation in `storeRef`
    (`storeRef_ptr_owner_read_invalidation_witness`)**:
    1. When `_2 := &_1` and `_3 := &_2` (so `_3` borrows the pointer slot `_2`), executing
       `*_2 := 9` (`storeRef 2 (.const 9)`) directly reads `_2` by its owner (`storeThrough`
       applies `ownerReadLoc 2`), bumping `_2`'s generation and invalidating `_3` so a subsequent
       `_0 := *_3` faults in `execCfg` and returns `none` in `symEvalCfgGvn`.
    2. Meanwhile, `_2`'s own loan to `_1` is re-validated at `_1`'s bumped generation, so reading
       back through `*_2` (`storeRefPtrOwnerReadValidSelfCfg`) verifies `= _0 + 9`. -/
theorem storeRef_ptr_owner_read_invalidation_witness :
    execCfg storeRefPtrOwnerReadInvalidatesLoanCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn storeRefPtrOwnerReadInvalidatesLoanCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      checkCfgAgainstTree storeRefPtrOwnerReadValidSelfCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable (.op1 (.addConst 9) (.var 0)) = true := by
  decide +kernel

/-- Reading a reference local as a scalar: `_2 := &_1; *_2 := 7; _0 := _2` (ill-typed MIR — a
    `&mut u64` is not a `u64`). -/
def pointerAsScalarCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .storeRef 2 (.const 7), .assign 0 (.use 2) ]
          term := .ret 0 } ] }

/-- Returning a reference local as the scalar result: `_2 := &_1; return _2`. -/
def pointerReturnCfg : MirCfg :=
  { blocks := [ { stmts := [ .retagBorrow 2 1 ], term := .ret 2 } ] }

/-- Reading back through the reference instead: `_2 := &_1; *_2 := 7; _0 := *_2`. -/
def pointerDerefCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .storeRef 2 (.const 7), .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- **Pointer Locals Are Not Scalars (`pointer_scalar_read_rejected_witness`)**: a slot holding a
    loan cannot be read as a scalar, so the untyped model no longer exposes the stale snapshot of
    the referent taken at borrow time. Before B4, `pointerAsScalarCfg` *verified* against the
    **old** `_1` (`.var 1`) although `_1` had been overwritten with `7`. Both ill-typed programs
    now fault concretely, the first is rejected symbolically, and the deref reads the current
    referent (`= 7`). -/
theorem pointer_scalar_read_rejected_witness :
    execCfg pointerAsScalarCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn pointerAsScalarCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg pointerReturnCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      checkCfgAgainstTree pointerDerefCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable (.const 7) = true := by
  decide +kernel

/-- Two-level stale-snapshot read via `derefRef` on a reference-to-reference (`_2 := &_1;
    _3 := &_2; _1 := 7; _0 := *_3; return _0`): in B4 (`9f2fc8f8`), `_1 := 7` invalidated `_2`'s
    loan to `_1` without touching `_2`'s own generation, and `derefRef 3` matched `st.getSlot 2`
    against `.live targetVal curGen true _` (ignoring `targetLoan = some (1, 0)`), so B4 verified
    `_0 := *_3` against the stale borrow-time snapshot `.var 1` (`3`, even though `_1` had been
    overwritten with `7`!). Requiring `targetLoan = none` in `derefRef` rejects this both
    concretely and symbolically. -/
def refToRefDerefCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .retagBorrow 3 2, .assign 1 (.const 7),
            .assign 0 (.derefRef 3) ]
          term := .ret 0 } ] }

/-- Two-level scalar overwrite of a reference slot via `storeRef` (`_2 := &_1; _3 := &_2;
    *_3 := 7; _0 := *_2`): in B4, `storeRef 3 (.const 7)` overwrote `_2`'s snapshot with `7`
    while keeping `_2`'s `loanTarget = some (1, 0)`. Requiring `targetLoan = none` in `storeRef`
    rejects scalar writes into reference slots. -/
def refToRefStoreCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .retagBorrow 3 2, .storeRef 3 (.const 7),
            .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- **Reference-to-Reference Scalar Deref/Store Rejection (`ref_to_ref_deref_and_store_rejected_witness`)**:
    neither `derefRef` nor `storeRef` may treat a reference slot (`targetLoan = some _`) as a
    scalar referent, closing B4's residual two-level stale-snapshot soundness hole (`PROTOTYPE_REPORT.md`
    §2.7, §3.2). -/
theorem ref_to_ref_deref_and_store_rejected_witness :
    execCfg refToRefDerefCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn refToRefDerefCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg refToRefStoreCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn refToRefStoreCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- Diamond with branch-condition-dependent `MirStmt.assert`s in both arms:
    - `then` arm (`bb 1`, where `_1 != 0`) asserts `_1` directly and computes `_0 := _0 + 7`,
    - `else` arm (`bb 2`, where `_1 == 0`) computes `_2 := boolNot(_1)`, asserts `_2`, kills
      `_2`, and computes `_0 := _0 + 7`. -/
def branchCondAssertDiamondCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchInt 1 1 2 },
        { stmts := [ .assert 1, .assign 0 (.op1 (.addConst 7) 0) ], term := .goto 3 },
        { stmts :=
            [ .storageLive 2,
              .assign 2 (.op1 .boolNot 1),
              .assert 2,
              .storageDead 2,
              .assign 0 (.op1 (.addConst 7) 0) ]
          term := .goto 3 },
        { stmts := [], term := .ret 0 } ] }

/-- Non-diamond `switchInt` where both arms assert their branch condition and return directly
    (`.ret 0`, so `diamondMergePlan = none` and `combineSplit` path-splits). -/
def branchCondEarlyReturnCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchInt 1 1 2 },
        { stmts := [ .assert 1, .assign 0 (.op1 (.addConst 7) 0) ], term := .ret 0 },
        { stmts :=
            [ .storageLive 2,
              .assign 2 (.op1 .boolNot 1),
              .assert 2,
              .storageDead 2,
              .assign 0 (.op1 (.addConst 7) 0) ]
          term := .ret 0 } ] }

/-- **Path-Sensitive Branch-Assertion Diamond & Split Witness (`branch_cond_assert_diamond_verified`)**:
    `symEvalCfgGvn` discharges branch-dependent assertions (`assert _1` in the `then` arm and
    `assert (boolNot _1)` in the `else` arm) both when merging at a join (`diamondJoinHints`,
    `1` path) AND when path-splitting without join hints (`noJoinHints`, `2` paths) or on
    early-return arms (`branchCondEarlyReturnCfg`). -/
theorem branch_cond_assert_diamond_verified :
    (symEvalCfgGvn branchCondAssertDiamondCfg diamondJoinHints 3 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 1 ∧
      checkCfgAgainstTree branchCondAssertDiamondCfg diamondJoinHints 3 0 diamondInitSymState
        diamondInitSymTable (.op1 (.addConst 7) (.var 0)) = true ∧
      (symEvalCfgGvn branchCondAssertDiamondCfg noJoinHints 3 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 2 ∧
      checkCfgAgainstTree branchCondAssertDiamondCfg noJoinHints 3 0 diamondInitSymState
        diamondInitSymTable (.op1 (.addConst 7) (.var 0)) = true ∧
      checkCfgAgainstTree branchCondEarlyReturnCfg noJoinHints 2 0 diamondInitSymState
        diamondInitSymTable (.op1 (.addConst 7) (.var 0)) = true := by
  decide +kernel

/-- Asserts `!(x < x)` and `!(x - x)` (folded by `peepholeOp2` to `.const 0`, then negated by
    `.op1 .boolNot` and discharged by `isProvablyNonZero`). -/
def assertNotLtIrreflCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .storageLive 2,
              .assign 2 (.op2 .lt 0 0),
              .assign 2 (.op1 .boolNot 2),
              .assert 2,
              .assign 2 (.op2 .sub 0 0),
              .assign 2 (.op1 .boolNot 2),
              .assert 2,
              .storageDead 2 ]
          term := .ret 0 } ] }

/-- **Negated Zero-Constant Assertion Witness (`assert_not_lt_irrefl_verified`)**:
    `peepholeOp2` folds `_0 < _0` and `_0 - _0` to `.const 0`, and `isProvablyNonZero`
    recognizes `boolNot (.const 0)` as provably non-zero. -/
theorem assert_not_lt_irrefl_verified :
    checkCfgAgainstTree assertNotLtIrreflCfg noJoinHints 1 0 diamondInitSymState
      diamondInitSymTable (.var 0) = true := by
  decide +kernel

end Anneal.Rustc.V2026_06_01.SymbolicEval
