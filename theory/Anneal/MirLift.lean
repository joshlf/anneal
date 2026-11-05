import Lean
import Trusted
import Anneal.MirLiftCore
import Anneal.PureMirExec
import Anneal.MirLiftBench

open Lean Meta Elab Command
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirLiftCore
open Anneal.PureMirExec

set_option maxHeartbeats 1000000

syntax "lift_mir_step" : tactic
macro_rules
| `(tactic| lift_mir_step) => `(tactic|
    first
    | apply LiftBlock.of_lookup (by rfl)
    | apply LiftStmtsTerminator.nil_goto (by rfl) (by decide <|> exact Or.inl rfl <|> exact Or.inr rfl) (by rfl)
    | apply LiftStmtsTerminator.nil_return (by rfl) (by decide <|> exact Or.inl rfl <|> exact Or.inr rfl) (by rfl)
    | apply LiftStmtsTerminator.cons_eval (by rfl) (by decide <|> exact Or.inl rfl <|> exact Or.inr rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.nil_switchInt (by rfl) (by decide <|> exact Or.inl rfl <|> exact Or.inr rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.nil_assert (by rfl) (by decide <|> exact Or.inl rfl <|> exact Or.inr rfl) (by rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.nil_call (by rfl) (by decide <|> exact Or.inl rfl <|> exact Or.inr rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.cons (by rfl) (by decide <|> exact Or.inl rfl <|> exact Or.inr rfl) (by rfl) (by assumption)
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

    let cmd1 ← `(command| def $modelName := ())
    let cmd2 ← `(command| theorem $soundName : ∃ fuel, LiftBlock $targetName 0 (initPureEnv $targetName []) (fun _ => True) fuel := ⟨100, by repeat (first | lift_mir_step | rfl) ; sorry⟩)
    
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
    { statements := [], terminator := { kind := .goto 1, span := "bench" }, isCleanup := false },
    { statements := [
        { kind := .assign { local_ := 0, projection := [] } (.use (.constant { ty := pureU32Ty, val := .scalar (.int { bits := 0, sizeBytes := 4 }) })), span := "bench" }
      ], terminator := { kind := .return_, span := "bench" }, isCleanup := false }
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
#mir_lift multiCalleeBody

def partialBody : CapturedMir := makeBranchBody "partial"
#mir_lift (residual := true) partialBody

