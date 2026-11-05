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

def evalPureRvalue (body : CapturedMir) (env : PureEnv) (rv : Rvalue) : RvalueEvalResult :=
  evalRvalue env rv emptyMemory [] body.layouts

def evalPureOperand (body : CapturedMir) (env : PureEnv) (op : Operand) : PlaceReadResult :=
  evalOperand env op [] [] body.layouts []

def evalPureStmt (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat) (env : PureEnv) (stmt : Statement) : Option PureEnv :=
  if isPureStatement stmt.kind then
  match evalStmt (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } emptyMemory) stmt body.localDecls body.layouts with
  | .step ms' => some ms'.frame.locals
  | _ => none
  else none

def evalPureTerminator (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat) (env : PureEnv) (term : Terminator) : MirStepNode :=
  evalTerminator (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } emptyMemory) term (some body)

inductive LiftRvalue : CapturedMir → PureEnv → Rvalue → (Value × PureEnv → Prop) → Prop
  | use (body env op post val env' mem') :
      evalPureRvalue body env (.use op) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue body env (.use op) post
  | binaryOp (body env op lhs rhs post val env' mem') :
      evalPureRvalue body env (.binaryOp op lhs rhs) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue body env (.binaryOp op lhs rhs) post
  | unaryOp (body env op val post result env' mem') :
      evalPureRvalue body env (.unaryOp op val) = .ok result env' mem' →
      post (result, env') →
      LiftRvalue body env (.unaryOp op val) post
  | cast (body env kind op targetTy post val env' mem') :
      evalPureRvalue body env (.cast kind op targetTy) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue body env (.cast kind op targetTy) post
  | aggregate (body env kind operands post val env' mem') :
      evalPureRvalue body env (.aggregate kind operands) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue body env (.aggregate kind operands) post
  | discriminant (body env place post val env' mem') :
      evalPureRvalue body env (.discriminant place) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue body env (.discriminant place) post
  | repeat (body env op count post val env' mem') :
      evalPureRvalue body env (.repeat op count) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue body env (.repeat op count) post
  | len (body env place post val env' mem') :
      evalPureRvalue body env (.len place) = .ok val env' mem' →
      post (val, env') →
      LiftRvalue body env (.len place) post


theorem evalStmt_preserves_frame {bbIdx stmtIdx env mem stmt decls layouts ms'}
  (h_pure : isPureStatement stmt.kind = true)
  (h_step : evalStmt { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := env }, memory := mem } stmt decls layouts = .step ms') :
  ms'.frame.blockIdx = bbIdx ∧ ms'.frame.stmtIdx = stmtIdx + 1 := by
  cases h_k : stmt.kind <;> (
    unfold evalStmt at h_step
    rw [h_k] at h_step h_pure
    dsimp [isPureStatement] at h_pure
    first | contradiction | (
      dsimp only at h_step
      revert ms' h_step
      repeat' split
      all_goals {
        intro ms' h_step
        try (
          injection h_step with h_eq
          try (
            injection h_eq with h_eq2
            rw [←h_eq2]
            dsimp [advanceStmt]
            exact ⟨rfl, rfl⟩
          )
        )
        try contradiction
        try (
          rename_i heq
          injection heq with heq_inner
          subst heq_inner
          dsimp only at h_pure
          contradiction
        )
      }
    )
  )

theorem evalPureStmt_eq_step {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {stmt : Statement} {env' : PureEnv}
  (h_eval : evalPureStmt body bbIdx stmtIdx env stmt = some env') :
  evalStmt (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } emptyMemory) stmt body.localDecls body.layouts =
  .step (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx + 1, env := env' } emptyMemory) := by
  dsimp [evalPureStmt] at h_eval
  split at h_eval
  · rename_i h_pure
    split at h_eval
    · rename_i ms' h_step
      injection h_eval with h_env
      have h_eq := evalStmt_toMachineState_eq_withMem { bb := bbIdx, stmtIdx := stmtIdx, env := env } emptyMemory stmt body.localDecls body.layouts h_pure rootActiveMemory_emptyMemory
      rw [h_step] at h_eq
      dsimp [MirStepNode.withMem, MirExecState.withMem] at h_eq
      injection h_eq with h_ms
      injection h_ms with h_ms_inner
      
      have h_preserves := evalStmt_preserves_frame h_pure h_step
      have h_frame_locals : ms'.frame.locals = env' := by rw [←h_env]
      have h_frame_bb : ms'.frame.blockIdx = bbIdx := h_preserves.left
      have h_frame_stmtIdx : ms'.frame.stmtIdx = stmtIdx + 1 := h_preserves.right
      
      have h_ms'_eq : ms' = PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx + 1, env := env' } emptyMemory := by
        calc ms' = { frame := ms'.frame, memory := emptyMemory } := h_ms_inner
             _ = { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx + 1, locals := env' }, memory := emptyMemory } := by
               congr 1
               cases h_f : ms'.frame
               rw [h_f] at h_frame_locals h_frame_bb h_frame_stmtIdx
               dsimp only at h_frame_locals h_frame_bb h_frame_stmtIdx
               subst h_frame_locals h_frame_bb h_frame_stmtIdx
               rfl
      
      rw [h_ms'_eq] at h_step
      exact h_step
    · contradiction
  · contradiction
inductive LiftStmt : CapturedMir → BasicBlockIdx → Nat → PureEnv → Statement → (PureEnv → Prop) → Prop
  | assign (body bbIdx stmtIdx env place span rv post env') :
      evalPureStmt body bbIdx stmtIdx env { kind := .assign place rv, span := span } = some env' →
      post env' →
      LiftStmt body bbIdx stmtIdx env { kind := .assign place rv, span := span } post
  | setDiscriminant (body bbIdx stmtIdx env place variantIdx span post env') :
      evalPureStmt body bbIdx stmtIdx env { kind := .setDiscriminant place variantIdx, span := span } = some env' →
      post env' →
      LiftStmt body bbIdx stmtIdx env { kind := .setDiscriminant place variantIdx, span := span } post
  | storageLive (body bbIdx stmtIdx env local_ span post env') :
      evalPureStmt body bbIdx stmtIdx env { kind := .storageLive local_, span := span } = some env' →
      post env' →
      LiftStmt body bbIdx stmtIdx env { kind := .storageLive local_, span := span } post
  | storageDead (body bbIdx stmtIdx env local_ span post env') :
      evalPureStmt body bbIdx stmtIdx env { kind := .storageDead local_, span := span } = some env' →
      post env' →
      LiftStmt body bbIdx stmtIdx env { kind := .storageDead local_, span := span } post
  | nop (body bbIdx stmtIdx env span post env') :
      evalPureStmt body bbIdx stmtIdx env { kind := .nop, span := span } = some env' →
      post env' →
      LiftStmt body bbIdx stmtIdx env { kind := .nop, span := span } post

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
  (h_eval : evalPureOperand body env discr = .ok (.scalar sc) env')
  (h_target : target = lookupSwitchTarget sc.bits targets.branches targets.otherwise)
  (h_next : wpMirExecSym fuel body (.running (PureState.toMachineState { bb := target, stmtIdx := 0, env := env' } emptyMemory)) (mirNormalPost (fun retVal _ => post retVal))) :
  LiftStmtsTerminator body bbIdx stmtIdx env [] { kind := .switchInt discr targets, span := span } post (fuel + 1) := by
  subst h_stmtIdx h_target
  dsimp [evalPureOperand] at h_eval
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
  (h_eval : evalPureOperand body env cond = .ok (.scalar sc) env')
  (h_cond : sc.bits = (match expected with | true => 1 | false => 0))
  (h_next : wpMirExecSym fuel body (.running (PureState.toMachineState { bb := target, stmtIdx := 0, env := env' } emptyMemory)) (mirNormalPost (fun retVal _ => post retVal))) :
  LiftStmtsTerminator body bbIdx stmtIdx env [] { kind := .assert cond expected target unwind, span := span } post (fuel + 1) := by
  subst h_stmtIdx
  dsimp [evalPureOperand] at h_eval
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
  (h_eval : evalPureTerminator body bbIdx 0 env { kind := .call func args destination target unwind, span := span } = .step ms')
  (h_next : wpMirExecSym fuel body (.running ms') (mirNormalPost (fun retVal _ => post retVal))) :
  LiftStmtsTerminator body bbIdx stmtIdx env [] { kind := .call func args destination target unwind, span := span } post (fuel + 1) := by
  subst h_stmtIdx
  dsimp [evalPureTerminator] at h_eval
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

theorem LiftStmtsTerminator.cons_eval {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv} {stmt : Statement} {stmts : List Statement} {term : Terminator} {post : Value → Prop} {fuel : Nat}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := stmts, terminator := term, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_get : Trusted.Sequence.get? stmts stmtIdx = some stmt)
  (h_eval : evalPureStmt body bbIdx stmtIdx env stmt = some env')
  (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + 1) env' stmts term post fuel) :
  LiftStmtsTerminator body bbIdx stmtIdx env stmts term post (fuel + 1) := by
  dsimp [LiftStmtsTerminator, wpMirExecSym, stepMirExecSymTree, stepMirSymTree] at h_next ⊢
  unfold PureState.toMachineState at h_next ⊢
  dsimp [emptyMemory] at h_next ⊢
  rcases h_phase with hp | hp <;> rw [hp, h_bb] <;> dsimp [Trusted.Sequence.get?, beq_iff_eq] at h_get ⊢ <;> rw [h_get] <;> dsimp only
  · rw [evalSymNodeTree_eq, evalStmtSymTree_eval]
    have h_eq := evalPureStmt_eq_step h_eval
    unfold PureState.toMachineState at h_eq
    dsimp [emptyMemory] at h_eq
    rw [h_eq]
    dsimp [evalNodeWP]
    exact h_next
  · rw [evalSymNodeTree_eq, evalStmtSymTree_eval]
    have h_eq := evalPureStmt_eq_step h_eval
    unfold PureState.toMachineState at h_eq
    dsimp [emptyMemory] at h_eq
    rw [h_eq]
    dsimp [evalNodeWP]
    exact h_next

theorem LiftStmtsTerminator.cons {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv} {stmt : Statement} {stmts : List Statement} {term : Terminator} {post : Value → Prop} {fuel : Nat}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := stmts, terminator := term, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_get : Trusted.Sequence.get? stmts stmtIdx = some stmt)
  (h_stmt : LiftStmt body bbIdx stmtIdx env stmt (fun e => e = env'))
  (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + 1) env' stmts term post fuel) :
  LiftStmtsTerminator body bbIdx stmtIdx env stmts term post (fuel + 1) := by
  cases h_stmt <;> rename_i h_eval h_p <;> cases h_p
  · exact LiftStmtsTerminator.cons_eval h_bb h_phase h_get h_eval h_next
  · exact LiftStmtsTerminator.cons_eval h_bb h_phase h_get h_eval h_next
  · exact LiftStmtsTerminator.cons_eval h_bb h_phase h_get h_eval h_next
  · exact LiftStmtsTerminator.cons_eval h_bb h_phase h_get h_eval h_next
  · exact LiftStmtsTerminator.cons_eval h_bb h_phase h_get h_eval h_next


