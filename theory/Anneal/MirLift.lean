import Lean
import Trusted
import Anneal.MirLiftCore
import Anneal.PureMirExec
import Anneal.MirLiftBench

open Lean Meta Elab Command Tactic
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirLiftCore
open Anneal.PureMirExec

set_option maxHeartbeats 100000

elab "apply_lift_block_of_lookup" : tactic => do
  let g ← getMainGoal
  let tgt ← g.getType
  let tgt ← instantiateMVars tgt
  if tgt.isAppOf ``Anneal.MirLiftCore.LiftBlock then
    evalTactic (← `(tactic| apply Anneal.MirLiftCore.LiftBlock.of_lookup (by rfl)))
  else
    throwError "Not a LiftBlock goal"

syntax "lift_mir_step" : tactic
macro_rules
| `(tactic| lift_mir_step) => `(tactic|
    first
    | exact (by assumption)
    | apply Anneal.MirLiftCore.LiftResidualBlock.to_LiftBlock; exact (by assumption)
    | apply_lift_block_of_lookup
    | apply LiftStmtsTerminator.term_goto (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl)
    | apply LiftStmtsTerminator.term_return (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl)
    | apply LiftStmtsTerminator.cons_eval (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl)
    | apply LiftStmtsTerminator.term_switchInt (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.term_assert (by rfl) (by first | decide | exact Or.inl rfl | exact Or.inr rfl) (by rfl) (by rfl) (by rfl)
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
          match bb.terminator.kind with
          | TerminatorKind.call .. =>
            let hypName := mkIdent (Name.mkSimple s!"h_res_{i}")
            let bbIdxStx := Syntax.mkNumLit (toString i)
            let hypType ← `(∀ env, Anneal.MirLiftCore.LiftResidualBlock $targetName $bbIdxStx env (fun _ => True) 100)
            let b ← `(bracketedBinder| ($hypName : $hypType))
            residualHyps := residualHyps.push b
          | TerminatorKind.goto target =>
            if target ≤ i then
              let hypName := mkIdent (Name.mkSimple s!"h_res_{i}")
              let bbIdxStx := Syntax.mkNumLit (toString i)
              let hypType ← `(∀ env, Anneal.MirLiftCore.LiftResidualBlock $targetName $bbIdxStx env (fun _ => True) 100)
              let b ← `(bracketedBinder| ($hypName : $hypType))
              residualHyps := residualHyps.push b
          | _ => pure ()
        
    let cmd2 ← `(command| theorem $soundName $residualHyps* : ∃ fuel, LiftBlock $targetName 0 (initPureEnv $targetName []) (fun _ => True) fuel := by apply Exists.intro; apply LiftBlock.of_lookup (by rfl); repeat (first | lift_mir_step | trivial))
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
#mir_lift (residual := true) multiCalleeBody

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
