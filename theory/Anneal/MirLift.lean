-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Trusted
import Anneal.MirFuelFree
import Anneal.MirLiftCore
import Anneal.PureMirExec
import Anneal.MirLiftBench

/-!
# `#mir_lift`: proof-producing lifting of captured MIR bodies

`#mir_lift <item>` inspects the `CapturedMir` constant `<item>` and proves that
running it on no arguments returns normally, with no undefined behavior, panic,
or abort. It has two modes:

- **Call-free mode** (`#mir_lift [(residual := true)] <item>`): lifts the body
  along the alias-erased `LiftBlock` rules and transports the result to
  `initMachineState` through `mirWpConverges_of_pureExec_init`, which requires
  `checkPureMir <item>`. With `(residual := true)`, blocks on back edges are
  abstracted by `LiftResidualBlock` hypotheses of the generated theorem.
- **Linked-callee mode** (`#mir_lift (callees := [c₁, …]) <item>`): lifts the
  body along the memory-carrying `LiftFrame` rules from
  `initMachineStateWithCallees <item> [] [c₁, …]`, so the body may reify
  function pointers, call linked callees directly or through function
  pointers, and instantiate generic callees. Lifting synthesizes the return
  value: the command defines `<item>_model : Value` and proves
  `<item>_lift_sound : MirWpConverges <item> (initMachineStateWithCallees <item>
  [] [c₁, …]) (mirNormalPost (fun retVal _ => retVal = <item>_model))` and
  `<item>_verified`, the trusted `VerificationResult` of the claim
  `{ body := <item>, callees := [c₁, …], pre := (· = []),
  post := fun _ ret => ret = <item>_model }`. A call-free body that still fails
  `checkPureMir` (for example, one that reifies a function pointer) uses this
  mode with no callees.

Both modes run `<item>` on the empty argument list, so they apply only to
closed bodies (`argCount = 0`) and reject any other body. In linked-callee mode
every call must resolve to a linked callee or to the inline
`core::intrinsics::exact_div`. Calls to external functions, diverging calls
(`target = none`), unwinding, and cleanup blocks have no lifting rule, so
lifting fails on them (see the `LiftTerminator` docstring in
`Anneal.MirLiftCore`).

This module imports `Lean` for its command elaborator, so it is a tool rather
than part of the audited `Anneal` umbrella (the trusted-boundary audit admits
only `Init` and `Std` imports in downstream modules). Every theorem it emits is
an ordinary declaration checked by the Lean kernel when this module is built.
-/

open Lean Meta Elab Command Tactic
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirFuelFree
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.PureMirExec

-- `LiftBlock`, `LiftResidualBlock`, and `LiftFrame` are globally irreducible
-- (see `Anneal.MirLiftCore`); also seal `wpMirExecSym` here so `isDefEq` never
-- falls back to symbolic evaluation while matching lifting rules.
attribute [local irreducible] wpMirExecSym

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

/-!
### Frame-lifting tactics

`lift_frame_step` applies one `LiftFrame.stmt` or `LiftFrame.term` rule,
choosing the first `LiftStmtMem` or `LiftTerminator` constructor whose premises
hold on the concrete frame. Every premise is an evaluation fact closed by
`rfl`, so the kernel replays the trusted evaluator on exactly the visited
statements and terminators while `body` stays a constant in every goal.
`lift_frame` repeats steps until the root return, then closes the
postcondition (`rfl` or `trivial`) and any fuel left unconstrained by the final
step (`0`). They live here rather than in `Anneal.MirLiftCore` because the
trusted-boundary audit admits no `syntax` or `macro_rules` commands in audited
modules; audited proofs apply the same rules explicitly (see
`Anneal.MirLiftBench`).
-/

/-- Apply one memory-carrying statement or terminator lifting rule. -/
syntax (name := liftFrameStep) "lift_frame_step" : tactic

macro_rules
  | `(tactic| lift_frame_step) => `(tactic|
      first
      | (apply Anneal.MirLiftCore.LiftFrame.stmt (by rfl)
            (by first | exact Or.inl rfl | exact Or.inr rfl) (by rfl) (by rfl)
            (by rfl)
         first
         | apply Anneal.MirLiftCore.LiftStmtMem.pure (by rfl) (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftStmtMem.reifyFnPointerPlace (by rfl)
             (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
             (by rfl) (by rfl) (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftStmtMem.unsafeFnPointer (by rfl)
             (by rfl) (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftStmtMem.fnPtrToPtr (by rfl) (by rfl)
             (by rfl)
         dsimp only [advanceStmt, PureState.toMachineState, List.set, Nat.add])
      | (apply Anneal.MirLiftCore.LiftFrame.term (by rfl)
            (by first | exact Or.inl rfl | exact Or.inr rfl) (by rfl) (by rfl)
            (by rfl)
         first
         | apply Anneal.MirLiftCore.LiftTerminator.goto
         | apply Anneal.MirLiftCore.LiftTerminator.switchInt (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.assert (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.drop (by rfl) (by rfl) (by rfl)
             (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.dropProjected (by rfl)
             (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.return_ (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.returnToCaller (by rfl) (by rfl)
             (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.callDirect (by rfl) (by rfl)
             (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.callFnItem (by rfl) (by rfl)
             (by rfl) (by rfl) (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.callIndirect (by rfl) (by rfl)
             (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.callExactDiv (by rfl) (by rfl)
             (by rfl) (by rfl) (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.tailCallDirect (by rfl)
             (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.tailCallFnItem (by rfl)
             (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
         | apply Anneal.MirLiftCore.LiftTerminator.tailCallIndirect (by rfl)
             (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
             (by rfl)
         dsimp only [Anneal.MirLiftCore.FrameStep.Continues,
           Anneal.MirLiftCore.callFrameMem,
           Anneal.MirLiftCore.tailCallFrameMem,
           Anneal.MirLiftCore.returnFrameMem,
           restoreCallerProtectors, lookupSwitchTarget,
           Option.getD, List.set, Nat.add]))

/-- Lift a whole execution from an entry `LiftFrame` goal to the root return. -/
syntax (name := liftFrame) "lift_frame" : tactic

macro_rules
  | `(tactic| lift_frame) => `(tactic|
      (repeat lift_frame_step
       all_goals first | rfl | trivial | exact 0))

syntax (name := mirLiftCmd) "#mir_lift "
  (atomic("(" &"residual") " := " ident ")")?
  (atomic("(" &"callees") " := " term ")")? ident : command

/--
Linked-callee mode of `#mir_lift`: lift `declName` from
`initMachineStateWithCallees declName [] callees` with `lift_frame`, reading
the root return value off the final `LiftTerminator.return_` step, then add
`<item>_model` (that value), `<item>_lift_sound` (the convergence theorem), and
`<item>_verified` (the trusted `VerificationResult` of the closed claim with
`callees` linked).
-/
def elabMirLiftFrame (id : Ident) (calleesStx : Term) : CommandElabM Unit := do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let ns ← getCurrNamespace
  let modelName := ns ++ id.getId.appendAfter "_model"
  let soundName := ns ++ id.getId.appendAfter "_lift_sound"
  let verifiedName := ns ++ id.getId.appendAfter "_verified"
  liftTermElabM do
    let bodyE := mkConst declName
    let valueTy := mkConst ``Value
    let calleesE ← Term.elabTermEnsuringType calleesStx
      (mkApp (mkConst ``List [Level.zero]) (mkConst ``CapturedMir))
    Term.synthesizeSyntheticMVarsNoPostponing
    let calleesE ← instantiateMVars calleesE
    let argsE := mkApp (mkConst ``List.nil [Level.zero]) valueTy
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
      throwError "#mir_lift: could not lift {declName} with the linked callees; \
        unsolved lifting goals:{indentD (MessageData.joinSep
          (remaining.map MessageData.ofGoal) Format.line)}"
    let proof ← instantiateMVars goal
    let fuel ← instantiateMVars fuelMVar
    let retVal ← instantiateMVars retMVar
    if proof.hasExprMVar || fuel.hasExprMVar || retVal.hasExprMVar then
      throwError "#mir_lift: lifting {declName} left unassigned metavariables"
    -- The return value is a closed `Value` term; normalize it so the model is
    -- a readable literal rather than the evaluator's unreduced projections.
    let retVal ← withTransparency .all <| Meta.reduce retVal
    addAndCompile <| .defnDecl
      { name := modelName, levelParams := [], type := valueTy, value := retVal,
        hints := .abbrev, safety := .safe }
    let modelE := mkConst modelName
    let postModel ← postOf modelE
    let normalPost ←
      withLocalDeclD `retVal valueTy fun v =>
        withLocalDeclD `mem (mkConst ``Memory) fun m => do
          mkLambdaFVars #[v, m] (← mkEq v modelE)
    let thmTy ← mkAppM ``MirWpConverges
      #[bodyE, initE, ← mkAppM ``mirNormalPost #[normalPost]]
    let thmVal ← mkAppOptM ``LiftFrame.mirWpConverges_withCallees
      #[bodyE, argsE, calleesE, postModel, fuel, proof]
    let thmVal ← mkExpectedTypeHint thmVal thmTy
    addDecl <| .thmDecl
      { name := soundName, levelParams := [], type := thmTy, value := thmVal }
    -- Package the same lifted execution as the trusted certificate for the
    -- closed claim `{ body, callees, pre := (· = []), post := (· = model) }`.
    let argsTy := mkApp (mkConst ``List [Level.zero]) valueTy
    let preE ← withLocalDeclD `args argsTy fun a => do
      mkLambdaFVars #[a] (← mkEq a argsE)
    let claimPostE ←
      withLocalDeclD `args argsTy fun a =>
        withLocalDeclD `ret valueTy fun r => do
          mkLambdaFVars #[a, r] (← mkEq r modelE)
    let claimE := mkAppN (mkConst ``Trusted.VerificationResult.Claim.mk)
      #[bodyE, preE, claimPostE, calleesE]
    let hPreE ← withLocalDeclD `args argsTy fun a => do
      withLocalDeclD `h (← mkEq a argsE) fun h => mkLambdaFVars #[a, h] h
    let verTy := mkApp (mkConst ``Trusted.VerificationResult.VerificationResult) claimE
    let verVal ← mkAppOptM ``LiftFrame.verificationResult
      #[claimE, argsE, fuel, hPreE, proof]
    let verVal ← mkExpectedTypeHint verVal verTy
    addDecl <| .thmDecl
      { name := verifiedName, levelParams := [], type := verTy, value := verVal }

@[command_elab mirLiftCmd]
def elabMirLift : CommandElab := fun stx => do
  match stx with
  | `(command| #mir_lift $[(residual := $res?:ident)]? $[(callees := $callees?:term)]? $id:ident) =>
    let name := id.getId
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

    let modelName := mkIdent (name.appendAfter "_model")
    let soundName := mkIdent (name.appendAfter "_lift_sound")
    let targetName := mkCIdent declName

    let val ← liftTermElabM do
      let env ← getEnv
      let some info := env.find? declName | throwError "unknown constant {declName}"
      unsafe evalExpr CapturedMir (mkConst ``CapturedMir) info.value!

    -- Both modes run the body on the empty argument list; refuse bodies that
    -- take arguments rather than certify a call with missing arguments.
    unless val.argCount == 0 do
      throwError "#mir_lift: {declName} takes {val.argCount} argument(s); only \
        closed bodies (`argCount = 0`) can be lifted"

    -- Bodies with linked callees, or that fail `checkPureMir` (function-pointer
    -- casts, calls), need the memory-carrying mode; call-free bodies keep the
    -- alias-erased mode and its `mem' = mem₀` postcondition.
    let isPure := checkPureMir val
    if callees?.isSome || !isPure then
      if res?.isSome then
        -- A residual block hypothesis would have to hold for every locals and
        -- memory configuration, including foreign active callees, so it is
        -- almost never satisfiable and would make the generated theorem
        -- vacuous; refuse instead.
        throwError "#mir_lift: `(residual := true)` applies only to call-free \
          bodies without linked callees; the memory-carrying mode has no sound \
          residual abstraction"
      let calleesStx ← match callees? with
        | some cs => pure cs
        | none => `([])
      elabMirLiftFrame id calleesStx
      return

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
          | .tailCall .. => needsResidual := true
          | _ => pure ()

          if needsResidual then
            let hypName := mkIdent (Name.mkSimple s!"h_res_{i}")
            let bbIdxStx := Syntax.mkNumLit (toString i)
            let hypType ←
              `(∀ env, Anneal.MirLiftCore.LiftResidualBlock $targetName $bbIdxStx env (fun _ => True) 100)
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

/-!
`multiCalleeBody` calls a `u32` constant. `resolveCallTarget` rejects a callee
operand that is neither a function item nor a function pointer as undefined
behavior, so no lifting may succeed: the body does not converge from its
callee-aware initial state, and the universally quantified residual hypothesis
`∀ env mem, LiftFrame multiCalleeBody 0 0 env mem _ 100` that a residual
abstraction of its call block would assume is refutable.
-/

theorem multiCalleeBody_not_converges (post : MirOutcome → Prop) :
    ¬ MirWpConverges multiCalleeBody
      (initMachineStateWithCallees multiCalleeBody [] []) post := by
  -- `wpMirExecSym` is sealed in this module; unfold one step explicitly. The
  -- first terminator then evaluates to `MirStepNode.fail .ub`.
  rintro ⟨_ | fuel, h⟩ <;> unfold wpMirSym wpMirExecSym at h <;> exact h

theorem multiCalleeBody_residual_false :
    ¬ ∀ env mem, LiftFrame multiCalleeBody 0 0 env mem (fun _ => True) 100 :=
  fun h => multiCalleeBody_not_converges _
    (LiftFrame.mirWpConverges_withCallees (h _ _))

example : True := by
  fail_if_success
    (have : LiftFrame multiCalleeBody 0 0 (initPureEnv multiCalleeBody [])
        (initMachineStateWithCallees multiCalleeBody [] []).memory
        (fun _ => True) 1 := by lift_frame)
  trivial

/--
error: #mir_lift: `(residual := true)` applies only to call-free bodies without linked callees; the memory-carrying mode has no sound residual abstraction
-/
#guard_msgs in
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

def makeDropLoopBody (name : String) : CapturedMir := {
  benchBody with
  defPath := name,
  basicBlocks := [
    { statements := [], terminator := { kind := .drop { local_ := 0, projection := [] } 0 .unreachable, span := "bench" }, isCleanup := false }
  ]
}

def dropLoopBody : CapturedMir := makeDropLoopBody "dropLoop"
#mir_lift (residual := true) dropLoopBody

/-! ## Linked-callee mode: polymorphic indirect-call benchmark (`FF-3.3`) -/

-- `liftIndirectCallerMir` reifies `lift_poly_id::<u32>` into a function
-- pointer and calls it indirectly; `liftDirectCallerMir` calls and tail-calls
-- the same generic callee through its function-item constant;
-- `liftPolyLayoutCallerMir` exercises projected `ReifyFnPointer`,
-- `UnsafeFnPointer`, `FnPtrToPtr` followed by a byte-level `Transmute`
-- provenance round-trip, indirect `tailCall`, local fn-item calls, projected
-- `drop`, and polymorphic compound layout recomputation
-- (`LayoutTable.instantiateForBody`) on `Wrapper<T>`;
-- `liftClosureAndTraitCallerMir` calls a `ClosureFnPointer` coercion (which
-- tail-calls a local fn item via `tailCallFnItem`), a reified trait method
-- resolved through `TraitImplEntry`, the inline `core::intrinsics::exact_div`
-- intrinsic, and `drop`/`assert`/`switchInt`/`goto`; `liftPolyApplyCallerMir`
-- passes reified function pointers to the generic higher-order
-- `lift_poly_apply` at two instantiations and writes their return values into
-- projected tuple fields `_2.0` and `_2.1` (see `Anneal.MirLiftBench`).
#mir_lift (callees := [liftPolyIdMir]) liftIndirectCallerMir
#mir_lift (callees := [liftPolyIdMir]) liftDirectCallerMir
#mir_lift (callees := liftPolyLayoutCallees) liftPolyLayoutCallerMir
#mir_lift (callees := liftClosureAndTraitCallees) liftClosureAndTraitCallerMir
#mir_lift (callees := liftPolyApplyCallees) liftPolyApplyCallerMir

-- The synthesized models are the values returned through each call.
example : liftIndirectCallerMir_model = Value.scalar ⟨7, 4⟩ := rfl
example : liftDirectCallerMir_model = Value.scalar ⟨7, 4⟩ := rfl
example : liftPolyLayoutCallerMir_model = Value.scalar ⟨7, 4⟩ := rfl
example : liftClosureAndTraitCallerMir_model = Value.scalar ⟨7, 4⟩ := rfl
example : liftPolyApplyCallerMir_model = Value.scalar ⟨7, 4⟩ := rfl

-- The linked-callee mode also applies to call-free bodies: with
-- `(callees := [])` it synthesizes the returned value, which the call-free
-- mode does not record.
def branchFrameBody : CapturedMir := makeBranchBody "branchFrame"
#mir_lift (callees := []) branchFrameBody
example : branchFrameBody_model = Value.scalar ⟨0, 4⟩ := rfl

example :
    MirWpConverges liftIndirectCallerMir
      (initMachineStateWithCallees liftIndirectCallerMir [] [liftPolyIdMir])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨7, 4⟩)) :=
  liftIndirectCallerMir_lift_sound

example :
    MirWpConverges liftPolyLayoutCallerMir
      (initMachineStateWithCallees liftPolyLayoutCallerMir [] liftPolyLayoutCallees)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨7, 4⟩)) :=
  liftPolyLayoutCallerMir_lift_sound

example :
    MirWpConverges liftClosureAndTraitCallerMir
      (initMachineStateWithCallees liftClosureAndTraitCallerMir []
        liftClosureAndTraitCallees)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨7, 4⟩)) :=
  liftClosureAndTraitCallerMir_lift_sound

example :
    MirWpConverges liftPolyApplyCallerMir
      (initMachineStateWithCallees liftPolyApplyCallerMir [] liftPolyApplyCallees)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨7, 4⟩)) :=
  liftPolyApplyCallerMir_lift_sound

/--
info: 'liftIndirectCallerMir_lift_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms liftIndirectCallerMir_lift_sound

/--
info: 'liftDirectCallerMir_lift_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms liftDirectCallerMir_lift_sound

/--
info: 'liftPolyLayoutCallerMir_lift_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms liftPolyLayoutCallerMir_lift_sound

/--
info: 'liftClosureAndTraitCallerMir_lift_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms liftClosureAndTraitCallerMir_lift_sound

/--
info: 'liftPolyApplyCallerMir_lift_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms liftPolyApplyCallerMir_lift_sound

-- `#mir_lift` also emits the trusted certificate of the closed claim.
example :
    Trusted.VerificationResult.VerificationResult
      { body := liftIndirectCallerMir, callees := [liftPolyIdMir],
        pre := fun args => args = [],
        post := fun _ ret => ret = Value.scalar ⟨7, 4⟩ } :=
  liftIndirectCallerMir_verified

example :
    Trusted.VerificationResult.VerificationResult
      { body := liftPolyApplyCallerMir, callees := liftPolyApplyCallees,
        pre := fun args => args = [],
        post := fun _ ret => ret = Value.scalar ⟨7, 4⟩ } :=
  liftPolyApplyCallerMir_verified

/--
info: 'liftIndirectCallerMir_verified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms liftIndirectCallerMir_verified

/--
info: 'liftPolyApplyCallerMir_verified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms liftPolyApplyCallerMir_verified

-- Without the linked callee, the indirect call does not lift.
example : True := by
  fail_if_success
    (have : LiftFrame liftIndirectCallerMir 0 0 (initPureEnv liftIndirectCallerMir [])
        (initMachineStateWithCallees liftIndirectCallerMir [] []).memory
        (fun v => v = Value.scalar ⟨7, 4⟩) 7 := by lift_frame)
  trivial

-- A wrong expected result does not lift.
example : True := by
  fail_if_success
    (have : LiftFrame liftIndirectCallerMir 0 0 (initPureEnv liftIndirectCallerMir [])
        (initMachineStateWithCallees liftIndirectCallerMir [] [liftPolyIdMir]).memory
        (fun v => v = Value.scalar ⟨8, 4⟩) 7 := by lift_frame)
  trivial

-- Signature mismatches are undefined behavior (`liftBadReifySig_not_converges`,
-- `liftBadCallSig_not_converges`), so neither reification nor the indirect
-- call may lift.
example : True := by
  fail_if_success
    (have : LiftFrame liftBadReifySigMir 0 0 (initPureEnv liftBadReifySigMir [])
        (initMachineStateWithCallees liftBadReifySigMir [] [liftPolyIdMir]).memory
        (fun _ => True) 7 := by lift_frame)
  trivial

example : True := by
  fail_if_success
    (have : LiftFrame liftBadCallSigMir 0 0 (initPureEnv liftBadCallSigMir [])
        (initMachineStateWithCallees liftBadCallSigMir [] [liftPolyIdMir]).memory
        (fun _ => True) 7 := by lift_frame)
  trivial

-- A diverging call (`target = none`) never returns normally: returning is
-- undefined behavior (`liftBadDivergingReturn_not_converges`), and unwinding
-- through a well-formed cleanup block panics at the root
-- (`liftDivergingPanic_not_converges`). Neither lifts.
example : True := by
  fail_if_success
    (have : LiftFrame liftBadDivergingReturnMir 0 0
        (initPureEnv liftBadDivergingReturnMir [])
        (initMachineStateWithCallees liftBadDivergingReturnMir []
          [liftPolyIdMir]).memory
        (fun _ => True) 7 := by lift_frame)
  trivial

example : True := by
  fail_if_success
    (have : LiftFrame liftDivergingPanicCallerMir 0 0
        (initPureEnv liftDivergingPanicCallerMir [])
        (initMachineStateWithCallees liftDivergingPanicCallerMir []
          [liftAssertPanicMir]).memory
        (fun _ => True) 7 := by lift_frame)
  trivial

-- Transmuting a null pointer (`0_usize`) to `fn(u32) -> u32`
-- (`liftBadNullFnPtrTransmute_not_converges`), calling
-- `core::intrinsics::exact_div` with a non-zero remainder
-- (`liftBadExactDiv_not_converges`), and returning from a cleanup basic block
-- (`isCleanup = true`) all fail to lift.
example : True := by
  fail_if_success
    (have : LiftFrame liftBadNullFnPtrTransmuteMir 0 0
        (initPureEnv liftBadNullFnPtrTransmuteMir [])
        (initMachineStateWithCallees liftBadNullFnPtrTransmuteMir [] []).memory
        (fun _ => True) 4 := by lift_frame)
  trivial

example : True := by
  fail_if_success
    (have : LiftFrame liftBadExactDivMir 0 0
        (initPureEnv liftBadExactDivMir [])
        (initMachineStateWithCallees liftBadExactDivMir [] []).memory
        (fun _ => True) 4 := by lift_frame)
  trivial

example : True := by
  fail_if_success
    (have : LiftFrame liftBadCleanupReturnMir 0 0
        (initPureEnv liftBadCleanupReturnMir [])
        (initMachineStateWithCallees liftBadCleanupReturnMir [] []).memory
        (fun _ => True) 4 := by lift_frame)
  trivial

-- A function pointer whose signature does not match the instantiated parameter
-- type `fn(T) -> T` of `lift_poly_apply::<u32>` is undefined behavior
-- (`liftBadPolyApplySig_not_converges`), so it does not lift.
example : True := by
  fail_if_success
    (have : LiftFrame liftBadPolyApplySigMir 0 0
        (initPureEnv liftBadPolyApplySigMir [])
        (initMachineStateWithCallees liftBadPolyApplySigMir []
          liftPolyApplyCallees).memory
        (fun _ => True) 7 := by lift_frame)
  trivial

-- `#mir_lift` runs bodies on the empty argument list, so it refuses bodies
-- that take arguments.
/--
error: #mir_lift: liftPolyIdMir takes 1 argument(s); only closed bodies (`argCount = 0`) can be lifted
-/
#guard_msgs in
#mir_lift (callees := []) liftPolyIdMir

-- The tactic reproduces the explicit audited proof in `Anneal.MirLiftBench`.
example :
    LiftFrame liftIndirectCallerMir 0 0 (initPureEnv liftIndirectCallerMir [])
      (initMachineStateWithCallees liftIndirectCallerMir [] [liftPolyIdMir]).memory
      (fun v => v = Value.scalar ⟨7, 4⟩) 7 := by
  lift_frame

-- The lifting judgments are still irreducible after every `#mir_lift` above,
-- so `isDefEq` cannot unfold them into whole-body symbolic evaluation.
run_meta do
  for n in [``LiftBlock, ``LiftResidualBlock, ``LiftStmtsTerminator,
      ``LiftFrame] do
    unless (← Lean.getReducibilityStatus n) matches .irreducible do
      throwError "{n} is not irreducible"
