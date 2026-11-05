import Trusted
import Anneal.MirFuelFree
import Anneal.PureMirExec
import Anneal.MirLoops

set_option maxRecDepth 2048
namespace Anneal.MirLiftCore

open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.MirLoops

abbrev PureEnv := List SlotState

def initPureEnv (body : CapturedMir) (args : List Value) : PureEnv :=
  initLocals body args

def evalPureRvalue (env : PureEnv) (rv : Rvalue) : RvalueEvalResult :=
  evalRvalue env rv emptyMemory [] emptyLayoutTable

def evalPureStmt (env : PureEnv) (stmt : Statement) : Option PureEnv :=
  match evalStmt (PureState.toMachineState { bb := 0, stmtIdx := 0, env := env } emptyMemory) stmt with
  | .step ms' => some ms'.frame.locals
  | _ => none

inductive LiftRvalue : PureEnv → Rvalue → (Value × PureEnv → Prop) → Prop
  | use (env op post val env' mem') :
      evalPureRvalue env (.use op) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue env (.use op) post
  | binaryOp (env op lhs rhs post val env' mem') :
      evalPureRvalue env (.binaryOp op lhs rhs) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue env (.binaryOp op lhs rhs) post
  | unaryOp (env op val post result env' mem') :
      evalPureRvalue env (.unaryOp op val) = .ok result env' mem' →
      post (result, env') →
      LiftRvalue env (.unaryOp op val) post
  | cast (env kind op targetTy post val env' mem') :
      evalPureRvalue env (.cast kind op targetTy) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue env (.cast kind op targetTy) post
  | aggregate (env kind operands post val env' mem') :
      evalPureRvalue env (.aggregate kind operands) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue env (.aggregate kind operands) post
  | discriminant (env place post val env' mem') :
      evalPureRvalue env (.discriminant place) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue env (.discriminant place) post
  | repeat (env op count post val env' mem') :
      evalPureRvalue env (.repeat op count) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue env (.repeat op count) post
  | len (env place post val env' mem') :
      evalPureRvalue env (.len place) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue env (.len place) post

inductive LiftStmt : PureEnv → Statement → (PureEnv → Prop) → Prop
  | assign (env place span rv post env') :
      evalPureStmt env { kind := .assign place rv, span := span } = some env' →
      post env' →
      LiftStmt env { kind := .assign place rv, span := span } post
  | setDiscriminant (env place variantIdx span post env') :
      evalPureStmt env { kind := .setDiscriminant place variantIdx, span := span } = some env' →
      post env' →
      LiftStmt env { kind := .setDiscriminant place variantIdx, span := span } post
  | storageLive (env local_ span post env') :
      evalPureStmt env { kind := .storageLive local_, span := span } = some env' →
      post env' →
      LiftStmt env { kind := .storageLive local_, span := span } post
  | storageDead (env local_ span post env') :
      evalPureStmt env { kind := .storageDead local_, span := span } = some env' →
      post env' →
      LiftStmt env { kind := .storageDead local_, span := span } post
  | nop (env span post env') :
      evalPureStmt env { kind := .nop, span := span } = some env' →
      post env' →
      LiftStmt env { kind := .nop, span := span } post

mutual
inductive LiftStmtsTerminator (body : CapturedMir) : PureEnv → List Statement → Terminator → (Value → Prop) → Nat → Prop
  | nil_goto (env target span post fuel) :
      LiftBlock body target env post fuel →
      LiftStmtsTerminator body env [] { kind := .goto target, span := span } post (fuel + 1)
  | nil_return (env span post val) :
      Trusted.Sequence.get? env 0 = some (.init val) →
      post val →
      LiftStmtsTerminator body env [] { kind := .return_, span := span } post 1
  | nil_switchInt (env discr targets span post sc env' target fuel) :
      evalPureOperand env discr = .ok (.scalar sc) env' →
      target = lookupSwitchTarget sc.bits targets.branches targets.otherwise →
      LiftBlock body target env' post fuel →
      LiftStmtsTerminator body env [] { kind := .switchInt discr targets, span := span } post (fuel + 1)
  | nil_assert (env cond expected target unwind span post sc env' expectedBit fuel) :
      evalPureOperand env cond = .ok (.scalar sc) env' →
      expectedBit = (if expected then 1 else 0) →
      sc.bits = expectedBit →
      LiftBlock body target env' post fuel →
      LiftStmtsTerminator body env [] { kind := .assert cond expected target unwind, span := span } post (fuel + 1)
  | nil_call (env func args dest target unwind span post ms' fuel) :
      evalTerminator (PureState.toMachineState { bb := 0, stmtIdx := 0, env := env } emptyMemory) { kind := .call func args dest target unwind, span := span } none = .step ms' →
      LiftBlock body ms'.frame.blockIdx ms'.frame.locals post fuel →
      LiftStmtsTerminator body env [] { kind := .call func args dest target unwind, span := span } post (fuel + 1)
  | cons (env stmt stmts term post env' fuel) :
      LiftStmt env stmt (fun e => e = env') →
      LiftStmtsTerminator body env' stmts term post fuel →
      LiftStmtsTerminator body env (stmt :: stmts) term post (fuel + 1)

inductive LiftBlock (body : CapturedMir) : BasicBlockIdx → PureEnv → (Value → Prop) → Nat → Prop
  | step (bbIdx env post bb fuel) :
      body.basicBlocks[bbIdx]? = some bb →
      LiftStmtsTerminator body env bb.statements bb.terminator post fuel →
      LiftBlock body bbIdx env post (fuel + 1)
end

theorem LiftBlock.of_lookup {body : CapturedMir} {bbIdx : BasicBlockIdx} {env : PureEnv} {post : Value → Prop} {fuel : Nat}
  (h_bb : body.basicBlocks[bbIdx]? = some bb)
  (h_lift : LiftStmtsTerminator body env bb.statements bb.terminator post fuel) :
  LiftBlock body bbIdx env post (fuel + 1) :=
  .step bbIdx env post bb fuel h_bb h_lift

def LiftLoop (body : CapturedMir) (bbIdx : BasicBlockIdx) (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
  (LoopInv : Nat → α → PureEnv → Prop) (env₀ : PureEnv) (post : Value → Prop) : Prop :=
  LoopInv lo init env₀ ∧
  (∀ i (h_le : lo ≤ i) (h_lt : i < hi) a env, LoopInv i a env →
    ∃ fuel, LiftBlock body bbIdx env (fun _ => False) fuel)

theorem lift_PureMirConverges
  {body : CapturedMir} {args : List Value} {post : Value → Prop} {fuel : Nat}
  (h_pure : checkPureMir body = true)
  (h_lift : LiftBlock body 0 (initPureEnv body args) post fuel) :
  PureMirConverges body (initPureState body args) post := by
  use fuel
  sorry

EOF