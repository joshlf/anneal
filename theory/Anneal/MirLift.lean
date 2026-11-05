
import Lean
import Trusted
import Anneal.MirFuelFree
import Anneal.MirLiftCore
import Anneal.PureMirExec
import Anneal.MirLiftBench

open Lean Meta Elab Command Tactic
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirFuelFree
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.PureMirExec

attribute [local irreducible] LiftBlock LiftResidualBlock wpMirExecSym

set_option maxHeartbeats 100000

elab "apply_lift_block_of_lookup" : tactic => do
  let g ← getMainGoal
  let tgt ← g.getType
  let tgt ← instantiateMVars tgt
  if tgt.isAppOf ``Anneal.MirLiftCore.LiftBlock then
    evalTactic (← `(tactic| apply Anneal.MirLiftCore.LiftBlock.of_lookup (by rfl)))
    let g2 ← getMainGoal
    g2.withContext do
      let tgt2 ← g2.getType
      let tgt2 ← instantiateMVars tgt2
      let g3 ← g2.change tgt2
      replaceMainGoal [g3]
    evalTactic (← `(tactic| try dsimp))
  else
    throwError "Not a LiftBlock goal"

elab "apply_residual_block" : tactic => do
  let g ← getMainGoal
  let tgt ← g.getType
  let tgt ← instantiateMVars tgt
  if tgt.isAppOf ``Anneal.MirLiftCore.LiftBlock then
    let applied ← withMainContext do
      let lctx ← getLCtx
      for decl in lctx do
        if decl.isImplementationDetail then continue
        if decl.userName.toString.startsWith "h_res_" then
          try
            let id := mkIdent decl.userName
            evalTactic (← `(tactic| exact Anneal.MirLiftCore.LiftResidualBlock.to_LiftBlock (f2 := 100) $id (by decide)))
            return true
          catch _ => pure ()
      return false
    if !applied then
      throwError "ASSUMPTION FAILED!"
  else
    throwError "Not a LiftBlock goal"

syntax "lift_mir_step" : tactic
macro_rules
| `(tactic| lift_mir_step) => `(tactic|
    first
    | exact (by assumption)
    | apply_residual_block
    | apply_lift_block_of_lookup
    | apply LiftStmtsTerminator.term_goto (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl)
    | apply LiftStmtsTerminator.term_return (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl)
    | apply LiftStmtsTerminator.cons_eval (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl)
    | apply LiftStmtsTerminator.term_switchInt (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.term_assert (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.term_drop (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl) (by rfl) (by intro h; contradiction) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.term_call (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.cons (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl) (by assumption)
    | dsimp [evalPureStmt, isPureStatement, evalStmt, evalRvalue, evalOperand, advanceStmt, PureState.toMachineState, MachineState.frame, emptyMemory, invalidateConflictingBorrows, LocalSlot.init, Value.scalar, Rvalue.use, Operand.constant, Option.map, Option.bind, List.set, initPureEnv, initLocals, initLocalsAux, Trusted.Sequence.get?, List.length, Nat.add, writePurePlaceValue]; rfl
    | dsimp [initPureEnv, initLocals, initLocalsAux, List.set, Trusted.Sequence.get?]; rfl
  )

syntax (name := mirLiftCmd) "#mir_lift " ("(" &"residual" " := " ident ")")? ident : command

@[command_elab mirLiftCmd]
def elabMirLift : CommandElab := fun stx => do
  match stx with
  | `(command| #mir_lift $[(residual := $res?:ident)]? $id:ident) =>
    let name := id.getId
    
    let modelName := mkIdent (name.appendBefore "_model")
    let soundName := mkIdent (name.appendBefore "_lift_sound")
    let targetName := mkIdent name

    let val ← liftTermElabM do
      let env ← getEnv
      let some info := env.find? name | throwError "unknown constant {name}"
      unsafe evalExpr CapturedMir (mkConst ``CapturedMir) info.value!
      
    let blocksArr := val.basicBlocks.toArray

    let cmd1 ← `(command| def $modelName := ())
    
    let mut residualHyps : Array (TSyntax [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder]) := #[]
    let isResidual := res?.isSome
    if isResidual then
      for i in [0:blocksArr.size] do
        if h : i < blocksArr.size then
          let bb : BasicBlockData := blocksArr[i]
          let mut isBackEdge := false
          let checkUnwind (u : UnwindAction) : Bool := match u with | .cleanup target => target ≤ i | _ => false
          match bb.terminator.kind with
          | .goto target => if target ≤ i then isBackEdge := true
          | .drop _ target u => if target ≤ i || checkUnwind u then isBackEdge := true
          | .assert _ _ target u => if target ≤ i || checkUnwind u then isBackEdge := true
          | .call _ _ _ t u =>
            if checkUnwind u then isBackEdge := true
            if let some target := t then if target ≤ i then isBackEdge := true
          | .switchInt _ targets =>
            if targets.otherwise ≤ i then isBackEdge := true
            for b in targets.branches do
              if b.snd ≤ i then isBackEdge := true
          | _ => pure ()
          
          let mut needsResidual := isBackEdge
          match bb.terminator.kind with
          | .call .. => needsResidual := true
          | _ => pure ()
          
          if needsResidual then
            let hypName := mkIdent (Name.mkSimple s!"h_res_{i}")
            let bbIdxStx := Syntax.mkNumLit (toString i)
            let hypType ← `(∀ env, Anneal.MirLiftCore.LiftResidualBlock $targetName $bbIdxStx env (fun _ => True) 100)
            let b ← `(bracketedBinder| ($hypName : $hypType))
            residualHyps := residualHyps.push b
        
    let cmd2 ← `(command| theorem $soundName $residualHyps* : MirWpConverges $targetName (initMachineState $targetName []) (mirNormalPost (fun retVal mem' => mem' = (initMachineState $targetName []).memory ∧ (fun _ => True) retVal)) := by
      exact mirWpConverges_of_pureExec_init (by rfl) (lift_PureMirConverges (by rfl) (by apply LiftBlock.of_lookup (by rfl); repeat (first | lift_mir_step | trivial))))
    elabCommand cmd1
    elabCommand cmd2
  | _ => throwUnsupportedSyntax

-- E2E Test Suite Definitions
def makeEmptyReturnBody (name : String) : CapturedMir := {
  benchBody with
  defPath := name,
  basicBlocks := [
    { statements := [
        { kind := .assign { local_ := 0, projection := [] } (.use (.constant { ty := pureU32Ty, val := .scalar (.int { bits := 0, sizeBytes := 4 }) })), span := "bench" }
      ], terminator := { kind := .return_, span := "bench" }, isCleanup := false }
  ]
}

def makeBranchBody (name : String) : CapturedMir := {
  benchBody with
  defPath := name,
  basicBlocks := [
    { statements := [], terminator := { kind := .switchInt (.constant { ty := pureU32Ty, val := .scalar (.int { bits := 0, sizeBytes := 4 }) }) { branches := [(0, 1)], otherwise := 1 }, span := "bench" }, isCleanup := false },
    { statements := [
        { kind := .assign { local_ := 0, projection := [] } (.use (.constant { ty := pureU32Ty, val := .scalar (.int { bits := 0, sizeBytes := 4 }) })), span := "bench" }
      ], terminator := { kind := .return_, span := "bench" }, isCleanup := false }
  ]
}

def makeLoopBody (name : String) : CapturedMir := {
  benchBody with
  defPath := name,
  basicBlocks := [
    { statements := [], terminator := { kind := .goto 0, span := "bench" }, isCleanup := false }
  ]
}

def makeMultiCalleeBody (name : String) : CapturedMir := {
  benchBody with
  defPath := name,
  basicBlocks := [
    { statements := [], terminator := { kind := .call (.constant { ty := pureU32Ty, val := .scalar (.int { bits := 0, sizeBytes := 4 }) }) [] { local_ := 0, projection := [] } (some 1) .unreachable, span := "bench" }, isCleanup := false },
    { statements := [
        { kind := .assign { local_ := 0, projection := [] } (.use (.constant { ty := pureU32Ty, val := .scalar (.int { bits := 0, sizeBytes := 4 }) })), span := "bench" }
      ], terminator := { kind := .return_, span := "bench" }, isCleanup := false }
  ]
}

def straightBody : CapturedMir := makeEmptyReturnBody "straight"
#mir_lift straightBody

def branchBody : CapturedMir := makeBranchBody "branch"
#mir_lift branchBody

def loopBody : CapturedMir := makeLoopBody "loop"
#mir_lift (residual := true) loopBody

def multiCalleeBody : CapturedMir := makeMultiCalleeBody "multi"
-- -- #mir_lift (residual := true) multiCalleeBody

def makeGotoBody (name : String) : CapturedMir := {
  benchBody with
  defPath := name,
  basicBlocks := [
    { statements := [], terminator := { kind := .goto 1, span := "bench" }, isCleanup := false },
    { statements := [
        { kind := .assign { local_ := 0, projection := [] } (.use (.constant { ty := pureU32Ty, val := .scalar (.int { bits := 0, sizeBytes := 4 }) })), span := "bench" }
      ], terminator := { kind := .return_, span := "bench" }, isCleanup := false }
  ]
}

def gotoBody : CapturedMir := makeGotoBody "goto"
#mir_lift gotoBody

def partialBody : CapturedMir := makeBranchBody "partial"
#mir_lift (residual := true) partialBody

def makeDropLoopBody (name : String) : CapturedMir := {
  benchBody with
  defPath := name,
  basicBlocks := [
    { statements := [], terminator := { kind := .drop { local_ := 0, projection := [] } 0 .unreachable, span := "bench" }, isCleanup := false }
  ]
}

def dropLoopBody : CapturedMir := makeDropLoopBody "dropLoop"
#mir_lift (residual := true) dropLoopBody
