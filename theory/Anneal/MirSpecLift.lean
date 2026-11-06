import Lean
import Trusted
import Anneal.MirFuelFree
import Anneal.PureMirExec
import Anneal.MirLiftCore
import Anneal.MirLift

set_option maxRecDepth 2048
namespace Anneal.PureMirExec

open Lean Meta Elab Command Tactic
open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

syntax (name := mirLiftSpecCmd) "#mir_lift_spec" ident ident (atomic("(" &"callees") " := " term ")")? term : command

def elabMirLiftSpec (thmId : Ident) (id : Ident) (calleesStx : Term) (argsStx : Term) : CommandElabM Unit := do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let ns ← getCurrNamespace
  let soundName := ns ++ thmId.getId
  liftTermElabM do
    let bodyE := mkConst declName
    let valueTy := mkConst ``Value
    let calleesE ← Term.elabTermEnsuringType calleesStx
      (mkApp (mkConst ``List [Level.zero]) (mkConst ``CapturedMir))
    Term.synthesizeSyntheticMVarsNoPostponing
    let calleesE ← instantiateMVars calleesE
    let argsE ← Term.elabTermEnsuringType argsStx (mkApp (mkConst ``List [Level.zero]) valueTy)
    Term.synthesizeSyntheticMVarsNoPostponing
    let argsE ← instantiateMVars argsE
    
    let expectedRetValStx ← `(Value.scalar ({ bits := 1, sizeBytes := 1 } : ScalarInt))
    let expectedRetVal ← Term.elabTermEnsuringType expectedRetValStx valueTy
    Term.synthesizeSyntheticMVarsNoPostponing
    let expectedRetVal ← instantiateMVars expectedRetVal
    
    let retMVar ← mkFreshExprMVar valueTy
    let fuelMVar ← mkFreshExprMVar (mkConst ``Nat)
    let postOf (target : Expr) : MetaM Expr :=
      withLocalDeclD `retVal valueTy fun v => do
        mkLambdaFVars #[v] (← mkEq v target)
    let postE ← postOf retMVar
    let envE ← mkAppM ``initPureEnv #[bodyE, argsE]
    let initE ← mkAppM ``initMachineStateWithCallees #[bodyE, argsE, calleesE]
    let memE ← mkAppM ``MachineState.memory #[initE]
    let goalTy ← mkAppM ``LiftFrame
      #[bodyE, mkNatLit 0, mkNatLit 0, envE, memE, postE, fuelMVar]
    let goal ← mkFreshExprSyntheticOpaqueMVar goalTy
    let remaining ← Tactic.run goal.mvarId! do
      Tactic.evalTactic (← `(tactic| lift_frame))
    unless remaining.isEmpty do
      throwError "#mir_lift_spec: could not lift {declName} with the linked callees;         unsolved lifting goals:{indentD (MessageData.joinSep
          (remaining.map MessageData.ofGoal) Format.line)}"
    let proof ← instantiateMVars goal
    let fuel ← instantiateMVars fuelMVar
    let retVal ← instantiateMVars retMVar
    if proof.hasExprMVar || fuel.hasExprMVar || retVal.hasExprMVar then
      throwError "#mir_lift_spec: lifting {declName} left unassigned metavariables"
    
    let isCalleesEmpty ← match calleesE.getAppFnArgs with
      | (``List.nil, _) => pure true
      | _ => pure false

    let mut thmTy : Expr := mkConst ``True
    let mut thmVal : Expr := mkConst ``True.intro
    
    if isCalleesEmpty then
      let normalPost ←
        withLocalDeclD `retVal valueTy fun v =>
          withLocalDeclD `mem (mkConst ``Memory) fun m => do
            mkLambdaFVars #[v, m] (← mkEq v expectedRetVal)
      let wpConvTy ← mkAppM ``MirWpConverges
        #[bodyE, initE, ← mkAppM ``mirSafePost #[normalPost]]
      let wpConvVal ← mkAppOptM ``LiftFrame.mirWpConverges_withCallees
        #[bodyE, argsE, calleesE, ← postOf expectedRetVal, fuel, proof]
      thmTy ← mkAppM ``MirBoolPredicateHolds #[bodyE, argsE]
      thmVal ← mkAppM ``mirBoolPredicateHolds_of_wpConverges #[bodyE, argsE, wpConvVal]
    else
      let normalPost ←
        withLocalDeclD `retVal valueTy fun v =>
          withLocalDeclD `mem (mkConst ``Memory) fun m => do
            mkLambdaFVars #[v, m] (← mkEq v expectedRetVal)
      let wpConvTy ← mkAppM ``MirWpConverges
        #[bodyE, initE, ← mkAppM ``mirSafePost #[normalPost]]
      let wpConvVal ← mkAppOptM ``LiftFrame.mirWpConverges_withCallees
        #[bodyE, argsE, calleesE, ← postOf expectedRetVal, fuel, proof]
      thmTy ← mkAppM ``Anneal.MirFuelFree.MirBoolPredicateHoldsWithCallees #[bodyE, calleesE, argsE]
      thmVal ← mkAppM ``mirBoolPredicateHoldsWithCallees_of_wpConverges #[bodyE, calleesE, argsE, wpConvVal]
    
    thmVal ← mkExpectedTypeHint thmVal thmTy
    addDecl <| .thmDecl
      { name := soundName, levelParams := [], type := thmTy, value := thmVal }

@[command_elab mirLiftSpecCmd]
def elabMirLiftSpecCmd : CommandElab
  | `(command| #mir_lift_spec $thmId:ident $id:ident $[(callees := $callees?:term)]? $args:term) => do
    let calleesStx ← match callees? with
      | some cs => pure cs
      | none => `([])
    elabMirLiftSpec thmId id calleesStx args
  | _ => throwUnsupportedSyntax

end Anneal.PureMirExec
