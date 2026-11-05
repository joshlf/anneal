import Trusted
import Anneal.MirFuelFree
import Anneal.PureMirExec
import Anneal.MirLoops

set_option maxRecDepth 2048
set_option linter.unusedVariables false

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

def LiftBlock (body : CapturedMir) (bbIdx : BasicBlockIdx) (env : PureEnv) (post : Value → Prop) (fuel : Nat) : Prop :=
  wpPureMirExec fuel body { bb := bbIdx, stmtIdx := 0, env := env } post

def LiftStmtsTerminator (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat) (env : PureEnv) (stmts : List Statement) (term : Terminator) (post : Value → Prop) (fuel : Nat) : Prop :=
  wpMirExecSym fuel body (.running (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } emptyMemory)) (mirNormalPost (fun retVal _ => post retVal))

theorem LiftBlock.of_lookup {body : CapturedMir} {bbIdx : BasicBlockIdx} {env : PureEnv} {post : Value → Prop} {fuel : Nat}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
  (h_lift : LiftStmtsTerminator body bbIdx 0 env bb.statements bb.terminator post fuel) :
  LiftBlock body bbIdx env post fuel :=
  h_lift

theorem LiftStmtsTerminator.nil_goto {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {target : BasicBlockIdx} {span : String} {post : Value → Prop} {fuel : Nat}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := [], terminator := { kind := .goto target, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_stmtIdx : stmtIdx = 0)
  (h_lift : LiftBlock body target env post fuel) :
  LiftStmtsTerminator body bbIdx stmtIdx env [] { kind := .goto target, span := span } post (fuel + 1) := by
  subst h_stmtIdx
  rcases h_phase with hp | hp
  · dsimp [LiftStmtsTerminator, wpMirExecSym, evalSymNodeTree, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
    simp [hp, h_bb, evalTerminatorSymTree, evalTerminator]
    exact h_lift
  · dsimp [LiftStmtsTerminator, wpMirExecSym, evalSymNodeTree, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
    simp [hp, h_bb, evalTerminatorSymTree, evalTerminator]
    exact h_lift

theorem LiftStmtsTerminator.nil_return {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {span : String} {post : Value → Prop} {val : Value}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := [], terminator := { kind := .return_, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_stmtIdx : stmtIdx = 0)
  (h_ret : Trusted.Sequence.get? env 0 = some (.init val))
  (h_post : post val) :
  LiftStmtsTerminator body bbIdx stmtIdx env [] { kind := .return_, span := span } post 1 := by
  subst h_stmtIdx
  rcases h_phase with hp | hp
  · dsimp [LiftStmtsTerminator, wpMirExecSym, evalSymNodeTree, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
    simp [hp, h_bb, evalTerminatorSymTree, evalTerminator, h_ret]
    exact h_post
  · dsimp [LiftStmtsTerminator, wpMirExecSym, evalSymNodeTree, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
    simp [hp, h_bb, evalTerminatorSymTree, evalTerminator, h_ret]
    exact h_post

def LiftLoop (body : CapturedMir) (bbIdx : BasicBlockIdx) (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
  (LoopInv : Nat → α → PureEnv → Prop) (env₀ : PureEnv) (post : Value → Prop) : Prop :=
  LoopInv lo init env₀ ∧
  (∀ i (h_le : lo ≤ i) (h_lt : i < hi) a env, LoopInv i a env →
    ∃ fuel, LiftBlock body bbIdx env (fun _ => False) fuel)

theorem lift_PureMirConverges
  {body : CapturedMir} {args : List Value} {post : Value → Prop} {fuel : Nat}
  (h_pure : checkPureMir body = true)
  (h_lift : LiftBlock body 0 (initPureEnv body args) post fuel) :
  PureMirConverges body (initPureState body args) post :=
  ⟨fuel, h_lift⟩

theorem LiftStmtsTerminator.nil_switchInt {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv} {discr : Operand} {targets : SwitchTargets} {span : String} {post : Value → Prop} {fuel : Nat} {sc : ScalarInt} {target : BasicBlockIdx}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := [], terminator := { kind := .switchInt discr targets, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_stmtIdx : stmtIdx = 0)
  (h_eval : evalOperand env discr [] [] body.layouts [] = .ok (.scalar sc) env')
  (h_target : target = lookupSwitchTarget sc.bits targets.branches targets.otherwise)
  (h_next : wpMirExecSym fuel body (.running (PureState.toMachineState { bb := target, stmtIdx := 0, env := env' } emptyMemory)) (mirNormalPost (fun retVal _ => post retVal))) :
  LiftStmtsTerminator body bbIdx stmtIdx env [] { kind := .switchInt discr targets, span := span } post (fuel + 1) := by
  subst h_stmtIdx h_target
  dsimp [LiftStmtsTerminator, wpMirExecSym, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
  rcases h_phase with hp | hp <;> rw [hp, h_bb] <;> dsimp [Trusted.Sequence.get?, List.length, beq_iff_eq]
  · simp [evalTerminatorSymTree, h_eval, MirObsE, ObsE]
    split
    · simp only [evalSymNodeTree_eq, SymTree.bind_eval, lookupSwitchTargetTree_eval]
      dsimp [evalNodeWP]
      exact h_next
    · contradiction
  · simp [evalTerminatorSymTree, h_eval, MirObsE, ObsE]
    split
    · simp only [evalSymNodeTree_eq, SymTree.bind_eval, lookupSwitchTargetTree_eval]
      dsimp [evalNodeWP]
      exact h_next
    · contradiction

theorem LiftStmtsTerminator.nil_assert {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv} {cond : Operand} {expected : Bool} {target : BasicBlockIdx} {unwind : UnwindAction} {span : String} {post : Value → Prop} {fuel : Nat} {sc : ScalarInt}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := [], terminator := { kind := .assert cond expected target unwind, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_stmtIdx : stmtIdx = 0)
  (h_eval : evalOperand env cond [] [] body.layouts [] = .ok (.scalar sc) env')
  (h_cond : sc.bits = (match expected with | true => 1 | false => 0))
  (h_next : wpMirExecSym fuel body (.running (PureState.toMachineState { bb := target, stmtIdx := 0, env := env' } emptyMemory)) (mirNormalPost (fun retVal _ => post retVal))) :
  LiftStmtsTerminator body bbIdx stmtIdx env [] { kind := .assert cond expected target unwind, span := span } post (fuel + 1) := by
  subst h_stmtIdx
  dsimp [LiftStmtsTerminator, wpMirExecSym, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
  rcases h_phase with hp | hp <;> rw [hp, h_bb] <;> dsimp [Trusted.Sequence.get?, List.length, beq_iff_eq]
  · simp [evalTerminatorSymTree, h_eval]
    cases expected <;> dsimp at h_cond ⊢ <;> rw [h_cond] <;> simp only [Nat.beq_refl, evalSymNodeTree_eq] <;> dsimp [evalNodeWP] <;> exact h_next
  · simp [evalTerminatorSymTree, h_eval]
    cases expected <;> dsimp at h_cond ⊢ <;> rw [h_cond] <;> simp only [Nat.beq_refl, evalSymNodeTree_eq] <;> dsimp [evalNodeWP] <;> exact h_next

theorem LiftStmtsTerminator.nil_call {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {func : Operand} {args : List Operand} {destination : Place} {target : Option BasicBlockIdx} {unwind : UnwindAction} {span : String} {post : Value → Prop} {fuel : Nat} {ms' : MachineState}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := [], terminator := { kind := .call func args destination target unwind, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_stmtIdx : stmtIdx = 0)
  (h_eval : evalTerminator (PureState.toMachineState { bb := bbIdx, stmtIdx := 0, env := env } emptyMemory) { kind := .call func args destination target unwind, span := span } (some body) = .step ms')
  (h_next : wpMirExecSym fuel body (.running ms') (mirNormalPost (fun retVal _ => post retVal))) :
  LiftStmtsTerminator body bbIdx stmtIdx env [] { kind := .call func args destination target unwind, span := span } post (fuel + 1) := by
  subst h_stmtIdx
  dsimp [LiftStmtsTerminator, wpMirExecSym, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory] at h_eval ⊢
  rcases h_phase with hp | hp <;> rw [hp, h_bb] <;> dsimp [Trusted.Sequence.get?, List.length, beq_iff_eq]
  · simp [evalTerminatorSymTree]
    rw [h_eval]
    rw [evalSymNodeTree_eq]
    dsimp [evalNodeWP]
    exact h_next
  · simp [evalTerminatorSymTree]
    rw [h_eval]
    rw [evalSymNodeTree_eq]
    dsimp [evalNodeWP]
    exact h_next

theorem LiftStmtsTerminator.cons {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv} {stmt : Statement} {stmts : List Statement} {term : Terminator} {post : Value → Prop} {fuel : Nat}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := stmts, terminator := term, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_get : Trusted.Sequence.get? stmts stmtIdx = some stmt)
  (h_eval : evalStmt (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } emptyMemory) stmt body.localDecls body.layouts = .step (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx + 1, env := env' } emptyMemory))
  (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + 1) env' stmts term post fuel) :
  LiftStmtsTerminator body bbIdx stmtIdx env stmts term post (fuel + 1) := by
  dsimp [LiftStmtsTerminator, wpMirExecSym, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory] at h_next h_eval ⊢
  rcases h_phase with hp | hp <;> rw [hp, h_bb] <;> dsimp [Trusted.Sequence.get?, beq_iff_eq] at h_get ⊢ <;> rw [h_get] <;> dsimp only
  · rw [evalSymNodeTree_eq, evalStmtSymTree_eval]
    rw [h_eval]
    dsimp [evalNodeWP]
    exact h_next
  · rw [evalSymNodeTree_eq, evalStmtSymTree_eval]
    rw [h_eval]
    dsimp [evalNodeWP]
    exact h_next

