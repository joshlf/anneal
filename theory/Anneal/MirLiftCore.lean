-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

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
set_option linter.unusedSimpArgs false
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
    unfold evalStmt evalSetDiscriminantDerefWrite evalForeignFrameDerefWrite evalSetDiscriminantLocal at h_step
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


def LiftResidualBlock (body : CapturedMir) (bbIdx : BasicBlockIdx) (env : PureEnv) (post : Value → Prop) (fuel : Nat) : Prop :=
  LiftBlock body bbIdx env post fuel

theorem LiftResidualBlock.to_LiftBlock {body : CapturedMir} {bbIdx : BasicBlockIdx} {env : PureEnv} {post : Value → Prop} {f1 f2 : Nat}
  (h : ∀ env, LiftResidualBlock body bbIdx env post f1) (h_le : f1 ≤ f2) : LiftBlock body bbIdx env post f2 :=
  wpMirExecSym_mono h_le (h env)

def LiftStmtsTerminator (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat) (env : PureEnv) (stmts : List Statement) (term : Terminator) (post : Value → Prop) (fuel : Nat) : Prop :=
  wpMirExecSym fuel body (.running (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } emptyMemory)) (mirNormalPost (fun retVal _ => post retVal))


theorem LiftBlock.of_lookup {body : CapturedMir} {bbIdx : BasicBlockIdx} {env : PureEnv} {post : Value → Prop} {fuel : Nat}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
  (h_lift : LiftStmtsTerminator body bbIdx 0 env bb.statements bb.terminator post fuel) :
  LiftBlock body bbIdx env post fuel :=
  h_lift

theorem get_length_none_seq {α} (l : List α) : Trusted.Sequence.get? l (List.length l) = none := by
  simp [Trusted.Sequence.get?]

theorem get_length_none_list {α} (l : List α) : l[List.length l]? = none := by
  simp

theorem ite_length_eq {α β} (l : List α) (a b : β) : (if l.length = length l then a else b) = a := by
  have : l.length = length l := rfl
  simp [this]

theorem LiftStmtsTerminator.term_goto {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {target : BasicBlockIdx} {span : String} {post : Value → Prop} {fuel : Nat}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := stmts, terminator := { kind := .goto target, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_end : stmtIdx = List.length stmts)
  (h_lift : LiftBlock body target env post fuel) :
  LiftStmtsTerminator body bbIdx stmtIdx env stmts { kind := .goto target, span := span } post (fuel + 1) := by
  subst h_end
  rcases h_phase with hp | hp
  · dsimp [LiftStmtsTerminator, wpMirExecSym, evalSymNodeTree, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
    simp [hp, h_bb, get_length_none_seq, get_length_none_list, ite_length_eq, evalTerminatorSymTree, evalTerminator]
    exact h_lift
  · dsimp [LiftStmtsTerminator, wpMirExecSym, evalSymNodeTree, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
    simp [hp, h_bb, get_length_none_seq, get_length_none_list, ite_length_eq, evalTerminatorSymTree, evalTerminator]
    exact h_lift

theorem LiftStmtsTerminator.term_return {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {span : String} {post : Value → Prop} {val : Value}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := stmts, terminator := { kind := .return_, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_end : stmtIdx = List.length stmts)
  (h_ret : Trusted.Sequence.get? env 0 = some (.init val))
  (h_post : post val) :
  LiftStmtsTerminator body bbIdx stmtIdx env stmts { kind := .return_, span := span } post 1 := by
  subst h_end
  rcases h_phase with hp | hp
  · dsimp [LiftStmtsTerminator, wpMirExecSym, evalSymNodeTree, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
    simp [hp, h_bb, get_length_none_seq, get_length_none_list, ite_length_eq, evalTerminatorSymTree, evalTerminator, h_ret]
    exact h_post
  · dsimp [LiftStmtsTerminator, wpMirExecSym, evalSymNodeTree, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
    simp [hp, h_bb, get_length_none_seq, get_length_none_list, ite_length_eq, evalTerminatorSymTree, evalTerminator, h_ret]
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

theorem LiftStmtsTerminator.term_switchInt {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv} {discr : Operand} {targets : SwitchTargets} {span : String} {post : Value → Prop} {fuel : Nat} {sc : ScalarInt} {target : BasicBlockIdx}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := stmts, terminator := { kind := .switchInt discr targets, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_end : stmtIdx = List.length stmts)
  (h_eval : evalPureOperand body env discr = .ok (.scalar sc) env')
  (h_target : target = lookupSwitchTarget sc.bits targets.branches targets.otherwise)
  (h_next : LiftBlock body target env' post fuel) :
  LiftStmtsTerminator body bbIdx stmtIdx env stmts { kind := .switchInt discr targets, span := span } post (fuel + 1) := by
  dsimp [evalPureOperand] at h_eval
  dsimp [LiftStmtsTerminator, wpMirExecSym, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
  subst h_end
  rcases h_phase with hp | hp <;> rw [hp, h_bb] <;> dsimp [Trusted.Sequence.get?, List.length, beq_iff_eq]
  · simp [evalTerminatorSymTree, get_length_none_seq, get_length_none_list, ite_length_eq, h_eval, MirObsE, ObsE]
    rw [h_target] at h_next
    simp only [evalSymNodeTree_eq, SymTree.bind_eval, lookupSwitchTargetTree_eval]
    dsimp [evalNodeWP]
    exact h_next
  · simp [evalTerminatorSymTree, get_length_none_seq, get_length_none_list, ite_length_eq, h_eval, MirObsE, ObsE]
    rw [h_target] at h_next
    simp only [evalSymNodeTree_eq, SymTree.bind_eval, lookupSwitchTargetTree_eval]
    dsimp [evalNodeWP]
    exact h_next

theorem LiftStmtsTerminator.term_assert {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv} {cond : Operand} {expected : Bool} {target : BasicBlockIdx} {unwind : UnwindAction} {span : String} {post : Value → Prop} {fuel : Nat} {sc : ScalarInt}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := stmts, terminator := { kind := .assert cond expected target unwind, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_end : stmtIdx = List.length stmts)
  (h_eval : evalPureOperand body env cond = .ok (.scalar sc) env')
  (h_cond : sc.bits = (match expected with | true => 1 | false => 0))
  (h_next : LiftBlock body target env' post fuel) :
  LiftStmtsTerminator body bbIdx stmtIdx env stmts { kind := .assert cond expected target unwind, span := span } post (fuel + 1) := by
  dsimp [evalPureOperand] at h_eval
  dsimp [LiftStmtsTerminator, wpMirExecSym, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
  subst h_end
  rcases h_phase with hp | hp <;> rw [hp, h_bb] <;> dsimp [Trusted.Sequence.get?, List.length, beq_iff_eq]
  · simp [evalTerminatorSymTree, get_length_none_seq, get_length_none_list, ite_length_eq, h_eval]
    cases expected <;> dsimp at h_cond ⊢ <;> rw [h_cond] <;> simp only [Nat.beq_refl, evalSymNodeTree_eq] <;> dsimp [evalNodeWP] <;> exact h_next
  · simp [evalTerminatorSymTree, get_length_none_seq, get_length_none_list, ite_length_eq, h_eval]
    cases expected <;> dsimp at h_cond ⊢ <;> rw [h_cond] <;> simp only [Nat.beq_refl, evalSymNodeTree_eq] <;> dsimp [evalNodeWP] <;> exact h_next

theorem LiftStmtsTerminator.term_call {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {func : Operand} {args : List Operand} {destination : Place} {target : Option BasicBlockIdx} {unwind : UnwindAction} {span : String} {post : Value → Prop} {fuel : Nat} {ms' : MachineState}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := stmts, terminator := { kind := .call func args destination target unwind, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_end : stmtIdx = List.length stmts)
  (h_eval : evalPureTerminator body bbIdx (List.length stmts) env { kind := .call func args destination target unwind, span := span } = .step ms')
  (h_next : wpMirExecSym fuel body (.running ms') (mirNormalPost (fun retVal _ => post retVal))) :
  LiftStmtsTerminator body bbIdx stmtIdx env stmts { kind := .call func args destination target unwind, span := span } post (fuel + 1) := by
  dsimp [evalPureTerminator] at h_eval
  dsimp [LiftStmtsTerminator, wpMirExecSym, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory] at h_eval ⊢
  subst h_end
  rcases h_phase with hp | hp <;> rw [hp, h_bb] <;> dsimp [Trusted.Sequence.get?, List.length, beq_iff_eq]
  · simp [evalTerminatorSymTree, get_length_none_seq, get_length_none_list, ite_length_eq]
    rw [h_eval]
    rw [evalSymNodeTree_eq]
    dsimp [evalNodeWP]
    exact h_next
  · simp [evalTerminatorSymTree, get_length_none_seq, get_length_none_list, ite_length_eq]
    rw [h_eval]
    rw [evalSymNodeTree_eq]
    dsimp [evalNodeWP]
    exact h_next

theorem LiftStmtsTerminator.cons_eval {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv} {stmt : Statement} {term : Terminator} {post : Value → Prop} {fuel : Nat}
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

theorem LiftStmtsTerminator.cons {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv} {stmt : Statement} {term : Terminator} {post : Value → Prop} {fuel : Nat}
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

/--
Forces the `List` and `SlotState` constructor spine of a `PureEnv` before
returning `some env`, so `rfl` on `forcePureEnv? rawEnv = some ?env'` reduces
any pending `List.set` applications in `rawEnv` instead of unifying `?env'`
with an unreduced `List.set` thunk.
-/
def forcePureEnv? : PureEnv → Option PureEnv
  | [] => some []
  | .dead :: rest =>
    match forcePureEnv? rest with
    | some rest' => some (.dead :: rest')
    | none => none
  | .uninit :: rest =>
    match forcePureEnv? rest with
    | some rest' => some (.uninit :: rest')
    | none => none
  | .init v :: rest =>
    match forcePureEnv? rest with
    | some rest' => some (.init v :: rest')
    | none => none

theorem forcePureEnv?_eq_some (env : PureEnv) : forcePureEnv? env = some env := by
  induction env with
  | nil => rfl
  | cons s rest ih => cases s <;> dsimp [forcePureEnv?] <;> rw [ih]

/-- `set?_of_forcePureEnv? rfl` proves `set? env loc s = some env'` while
instantiating `env'` with the flat slot list that `forcePureEnv?` computes,
not with an unreduced `List.set` application. -/
theorem set?_of_forcePureEnv? {env env' : PureEnv} {loc : Local}
    {s : SlotState} (h : (set? env loc s).bind forcePureEnv? = some env') :
    set? env loc s = some env' := by
  cases hSet : set? env loc s with
  | none => rw [hSet] at h; nomatch h
  | some e =>
    rw [hSet, Option.bind_some, forcePureEnv?_eq_some] at h
    exact h

/--
Evaluates a single pure statement and normalizes the resulting `PureEnv` list
spine via `forcePureEnv?`.
-/
def evalPureStmtNorm (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat)
    (env : PureEnv) (stmt : Statement) : Option PureEnv :=
  match evalPureStmt body bbIdx stmtIdx env stmt with
  | some rawEnv => forcePureEnv? rawEnv
  | none => none

theorem evalPureStmtNorm_eq_evalPureStmt
    (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat)
    (env : PureEnv) (stmt : Statement) :
    evalPureStmtNorm body bbIdx stmtIdx env stmt =
      evalPureStmt body bbIdx stmtIdx env stmt := by
  unfold evalPureStmtNorm
  cases evalPureStmt body bbIdx stmtIdx env stmt with
  | none => rfl
  | some rawEnv => exact forcePureEnv?_eq_some rawEnv

theorem LiftStmtsTerminator.cons_eval_norm {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env env' : PureEnv} {stmt : Statement} {term : Terminator}
    {post : Value → Prop} {fuel : Nat}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_get : Trusted.Sequence.get? stmts stmtIdx = some stmt)
    (h_eval : evalPureStmtNorm body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + 1) env' stmts term post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env stmts term post (fuel + 1) := by
  rw [evalPureStmtNorm_eq_evalPureStmt] at h_eval
  exact LiftStmtsTerminator.cons_eval h_bb h_phase h_get h_eval h_next

/-- `cons_eval_norm` premise for `dst = rv` when `rv` is evaluated by a
separate lemma `h_rv`, for rvalues (such as transmutes of symbolic bytes)
that `rfl` cannot evaluate. -/
theorem evalPureStmtNorm_assign_local_of_evalRvalue
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat}
    {env env' : PureEnv} {dstLoc : Local} {rv : Rvalue} {span : String}
    {val : Value} {oldSlot : LocalSlot}
    (h_pure : isPureStatement
      (.assign { local_ := dstLoc, projection := [] } rv) = true)
    (h_rv : evalRvalue env rv emptyMemory body.localDecls body.layouts =
      .ok val env emptyMemory)
    (h_get : get? env dstLoc = some oldSlot)
    (h_live : oldSlot ≠ .dead)
    (h_set : (set? env dstLoc (.init val)).bind forcePureEnv? = some env') :
    evalPureStmtNorm body bbIdx stmtIdx env
      { kind := .assign { local_ := dstLoc, projection := [] } rv,
        span := span } = some env' := by
  dsimp only [evalPureStmtNorm, evalPureStmt]
  rw [h_pure]
  dsimp only [↓reduceIte, evalStmt, PureState.toMachineState]
  rw [h_rv]
  dsimp only [emptyMemory]
  rw [h_get]
  cases oldSlot with
  | dead => exact False.elim (h_live rfl)
  | uninit | init _ =>
    dsimp only
    cases hSet : set? env dstLoc (.init val) with
    | none => rw [hSet] at h_set; nomatch h_set
    | some locals₂ =>
      rw [hSet] at h_set
      exact h_set

/--
Evaluates `n` consecutive pure statements starting at `stmtIdx` in `stmts`,
normalizing the `PureEnv` spine via `forcePureEnv?` after each statement.
-/
def evalPureStmtsN (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmts : List Statement) :
    Nat → Nat → PureEnv → Option PureEnv
  | 0, _, env => forcePureEnv? env
  | n + 1, stmtIdx, env =>
    match Trusted.Sequence.get? stmts stmtIdx with
    | some stmt =>
      match evalPureStmtNorm body bbIdx stmtIdx env stmt with
      | some env₁ => evalPureStmtsN body bbIdx stmts n (stmtIdx + 1) env₁
      | none => none
    | none => none

theorem LiftStmtsTerminator.eval_n {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {n stmtIdx : Nat} {env env' : PureEnv} {stmts : List Statement} {term : Terminator}
    {post : Value → Prop} {fuel : Nat}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_eval : evalPureStmtsN body bbIdx stmts n stmtIdx env = some env')
    (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + n) env' stmts term post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env stmts term post (fuel + n) := by
  induction n generalizing stmtIdx env with
  | zero =>
    dsimp [evalPureStmtsN] at h_eval
    rw [forcePureEnv?_eq_some] at h_eval
    injection h_eval with h_eq
    subst h_eq
    simpa only [Nat.add_zero] using h_next
  | succ k ih =>
    dsimp [evalPureStmtsN] at h_eval
    cases h_get : Trusted.Sequence.get? stmts stmtIdx with
    | none =>
      rw [h_get] at h_eval
      contradiction
    | some stmt =>
      rw [h_get] at h_eval
      dsimp only at h_eval
      cases h_step : evalPureStmtNorm body bbIdx stmtIdx env stmt with
      | none =>
        rw [h_step] at h_eval
        contradiction
      | some env₁ =>
        rw [h_step] at h_eval
        dsimp only at h_eval
        have h_next' : LiftStmtsTerminator body bbIdx ((stmtIdx + 1) + k) env' stmts term post fuel := by
          have h_idx : (stmtIdx + 1) + k = stmtIdx + (k + 1) := by omega
          rw [h_idx]
          exact h_next
        have h_rec := ih h_eval h_next'
        have h_one := LiftStmtsTerminator.cons_eval_norm h_bb h_phase h_get h_step h_rec
        have h_fuel : (fuel + k) + 1 = fuel + (k + 1) := by omega
        rw [← h_fuel]
        exact h_one

/-- `eval_n` over every remaining statement of the block. The count
`List.length stmts - stmtIdx` comes from the block, so a proof that lifts a
straight-line block never states how many statements it has. -/
theorem LiftStmtsTerminator.eval_rest {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {term : Terminator} {post : Value → Prop}
    {fuel : Nat}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_eval : evalPureStmtsN body bbIdx stmts (List.length stmts - stmtIdx)
      stmtIdx env = some env')
    (h_next : LiftStmtsTerminator body bbIdx
      (stmtIdx + (List.length stmts - stmtIdx)) env' stmts term post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env stmts term post
      (fuel + (List.length stmts - stmtIdx)) :=
  LiftStmtsTerminator.eval_n h_bb h_phase h_eval h_next



theorem LiftStmtsTerminator.term_drop {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv} {place : Place} {target : BasicBlockIdx} {unwind : UnwindAction} {span : String} {post : Value → Prop} {fuel : Nat} {slot : LocalSlot}
  (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some { statements := stmts, terminator := { kind := .drop place target unwind, span := span }, isCleanup := false })
  (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
  (h_end : stmtIdx = List.length stmts)
  (h_get : Trusted.Sequence.get? env place.local_ = some slot)
  (h_not_dead : slot ≠ .dead)
  (h_proj : place.projection = [])
  (h_set : Trusted.Sequence.set? env place.local_ .uninit = some env')
  (h_next : LiftBlock body target env' post fuel) :
  LiftStmtsTerminator body bbIdx stmtIdx env stmts { kind := .drop place target unwind, span := span } post (fuel + 1) := by
  dsimp [LiftStmtsTerminator, wpMirExecSym, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
  subst h_end
  rcases h_phase with hp | hp <;> rw [hp, h_bb] <;> dsimp [Trusted.Sequence.get?, List.length, beq_iff_eq]
  · simp [evalTerminatorSymTree, get_length_none_seq, get_length_none_list, ite_length_eq, evalTerminator]
    rw [h_get]
    cases slot
    · contradiction
    · rw [h_proj]; simp; rw [h_set]; exact h_next
    · rw [h_proj]; simp; rw [h_set]; exact h_next
  · simp [evalTerminatorSymTree, get_length_none_seq, get_length_none_list, ite_length_eq, evalTerminator]
    rw [h_get]
    cases slot
    · contradiction
    · rw [h_proj]; simp; rw [h_set]; exact h_next
    · rw [h_proj]; simp; rw [h_set]; exact h_next


/-!
## Memory-carrying activation frames: function pointers and indirect calls

The judgments above erase `Memory` to `emptyMemory`, which is sound only for
call-free bodies (`checkPureMir`). Two constructs introduced by the
polymorphic-call work cannot be expressed in that erased model:

- **Function-pointer reification.** `_d = f::<Ts> as fn(..) -> R
  (PointerCoercion(ReifyFnPointer))` interns `(f, Ts, fn(..) -> R)` in
  `Memory.fnPtrs` (`internFnPtr`) and stores the synthetic pointer
  `.ptr ⟨allocId, 0⟩ 8`, so the step changes memory.
- **Indirect and polymorphic calls.** `_d = move _p(args) -> bbN` resolves the
  callee through `Memory.fnPtrs` (`resolveCallTarget`), instantiates a generic
  callee through `lookupCallee` (`CapturedMir.instantiate`, which recomputes the
  callee's layouts from the caller's layout table), pushes a `SavedCallerFrame`
  onto `Memory.callStack`, and runs the callee as `Memory.activeCallee`.

`LiftFrame` therefore keeps the full `Memory` alongside the alias-erased frame
`(bbIdx, stmtIdx, env)`. Every rule names the *active body* `cur`, which is
`mem.activeCallee.getD body`: the root body before a call, the instantiated
callee inside it, and the root body again after `TerminatorKind.return_` pops
the saved caller frame. `LiftStmtMem` and `LiftTerminator` are one-step
judgments whose premises mirror the trusted evaluator's success path, so each
is discharged by evaluating concrete side conditions; `LiftFrame.stmt` and
`LiftFrame.term` prove that one such step refines `wpMirExecSym`.
-/

section FrameLifting

/--
Lifting judgment for one activation frame of `body`'s execution: from the frame
at basic block `bbIdx`, statement `stmtIdx`, locals `env`, and memory `mem`,
execution returns normally from the root frame within `fuel` steps with a value
satisfying `post`, with no undefined behavior, panic, or abort.
-/
def LiftFrame (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat)
    (env : PureEnv) (mem : Memory) (post : Value → Prop) (fuel : Nat) : Prop :=
  wpMirExecSym fuel body
    (.running
      (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem))
    (mirNormalPost (fun retVal _ => post retVal))

/-- At `emptyMemory`, a block-entry frame is exactly `LiftBlock`. -/
theorem LiftFrame.iff_liftBlock {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {env : PureEnv} {post : Value → Prop} {fuel : Nat} :
    LiftFrame body bbIdx 0 env emptyMemory post fuel ↔
      LiftBlock body bbIdx env post fuel :=
  Iff.rfl

/-- At `emptyMemory`, a mid-block frame is exactly `LiftStmtsTerminator`. -/
theorem LiftFrame.iff_liftStmtsTerminator {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {stmts : List Statement} {term : Terminator} {post : Value → Prop}
    {fuel : Nat} :
    LiftFrame body bbIdx stmtIdx env emptyMemory post fuel ↔
      LiftStmtsTerminator body bbIdx stmtIdx env stmts term post fuel :=
  Iff.rfl

/-- Liveness of a local slot: only `.dead` slots reject writes and drops. -/
def slotLive : LocalSlot → Bool
  | .dead => false
  | _ => true

/-- A zero-sized function-item value (`fn` item constants evaluate to one). -/
def isZstFnItemValue : Value → Bool
  | .unit => true
  | .aggregate 0 .nil => true
  | _ => false

/--
Write `val` to a local place `dst` (either unprojected or along a non-deref
projection path) in `locals` and invalidate conflicting borrows in `borrows`,
matching the protector-free `StatementKind.assign` transition of `evalStmt`.
-/
def assignLocalPlace (locals : PureEnv) (borrows : List BorrowEntry)
    (dst : Place) (val : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (targetFrameDepth : Nat := 0) : Option (PureEnv × List BorrowEntry) :=
  match dst.projection with
  | [] =>
    match get? locals dst.local_ with
    | some .dead => none
    | some _ =>
      match set? locals dst.local_ (.init val) with
      | some locals' =>
        some (locals',
          invalidateConflictingBorrows borrows dst.local_ .none targetFrameDepth)
      | none => none
    | none => none
  | .deref :: _ => none
  | proj :: rest =>
    match get? locals dst.local_ with
    | some (.init rootVal) =>
      match
        writeProjectedForLocal
          locals
          localDecls
          layouts
          dst.local_
          (ensureNestedFieldShells rootVal (proj :: rest))
          (proj :: rest)
          val
      with
      | .ok rootVal' =>
        match set? locals dst.local_ (.init rootVal') with
        | some locals' =>
          let resolvedLocalProj :=
            resolveBorrowWriteLocalProj
              localDecls
              layouts
              locals
              dst.local_
              (proj :: rest)
          some (locals',
            invalidateConflictingBorrowsAtProj borrows dst.local_ .none
              resolvedLocalProj 0 0 targetFrameDepth)
        | none => none
      | _ => none
    | _ => none

/--
Memory after `TerminatorKind.call` inlines `calleeBody` from the caller frame
`(bbIdx, stmtIdx)` of `callerBody`: the caller frame, with locals `callerEnv`
after argument evaluation, is pushed onto `mem.callStack` and `calleeBody`
becomes the active body. This is `(pushCalleeFrame ..).memory` written out.
-/
@[reducible]
def callFrameMem (callerBody : CapturedMir) (bbIdx : BasicBlockIdx)
    (stmtIdx : Nat) (callerEnv : PureEnv) (mem : Memory) (destination : Place)
    (targetBb : BasicBlockIdx) (unwind : UnwindAction) (calleeBody : CapturedMir) :
    Memory :=
  { mem with
    callStack :=
      { callerBody := callerBody
        frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := callerEnv }
        destination := destination
        returnTarget := targetBb
        calleeProtectors := mem.activeProtectors
        returnUnwind := unwind
        isDiverging := false } :: mem.callStack
    activeCallee := some calleeBody }

/--
Memory after `TerminatorKind.tailCall` enters `calleeBody` without pushing a
new caller frame onto `mem.callStack`. This is
`(enterTailCalleeFrame ..).memory`.
-/
@[reducible]
def tailCallFrameMem (mem : Memory) (calleeNumLocals : Nat)
    (calleeBody : CapturedMir) : Memory :=
  { mem with
    borrows :=
      disableFrameBorrows mem.borrows (length mem.callStack) calleeNumLocals
    activeCallee := some calleeBody }

/--
Memory after `TerminatorKind.return_` tears down the returning callee's locals
(`disableFrameBorrows`), pops `caller` (with remaining stack `rest`), and
restores `caller.callerBody` and protectors prior to `writeReturnDestination`.
-/
@[reducible]
def returnFrameMem (mem : Memory) (calleeNumLocals : Nat)
    (caller : SavedCallerFrame) (rest : List SavedCallerFrame) : Memory :=
  { mem with
    borrows :=
      disableFrameBorrows mem.borrows (length mem.callStack) calleeNumLocals
    callStack := rest
    activeCallee := some caller.callerBody
    activeProtectors := restoreCallerProtectors caller }

/--
Memory-carrying one-statement judgment: executing `stmt` at `(bbIdx, stmtIdx)`
of the active body `cur` from `(env, mem)` steps to `(env', mem')` with
`post env' mem'`.
-/
inductive LiftStmtMem (cur : CapturedMir) (bbIdx : BasicBlockIdx)
    (stmtIdx : Nat) (env : PureEnv) (mem : Memory)
    (post : PureEnv → Memory → Prop) : Statement → Prop
  /--
  A pure statement (`isPureStatement`) evaluated by `evalPureStmt` leaves
  memory unchanged when `mem` has no live borrows and no active protectors,
  which holds in root, callee, and resumed caller frames of borrow-free code.
  -/
  | pure {stmt : Statement} {env' : PureEnv} :
      mem.borrows = [] →
      mem.activeProtectors = [] →
      evalPureStmt cur bbIdx stmtIdx env stmt = some env' →
      post env' mem →
      LiftStmtMem cur bbIdx stmtIdx env mem post stmt
  /--
  Function-pointer reification `dst = op as fn(..) (PointerCoercion(ck))` into
  an unprojected or non-deref projected local place `dst` (e.g., `_1` or a
  tuple/struct field `_1.0`).

  The premises are the success path of the trusted `evalReifyFnPointer`: `op`
  is a zero-sized function item or non-capturing closure whose type names
  `(defPath, typeArgs)`, the target type is a non-intrinsic `fn` pointer whose
  safety the coercion admits, the linked callee (if any) has a matching
  signature (`checkCalleeSig`, which resolves trait methods through
  `mem.traitImpls` and instantiates generic callees with `typeArgs`), and
  `internFnPtr` returns the synthetic `allocId`. The remaining premises are the
  protector-free local assignment `assignLocalPlace`.
  -/
  | reifyFnPointerPlace {dst : Place} {coercionKind : String} {op : Operand}
      {targetTy : Ty} {span : String} {fnItem : Value} {env₁ env₂ : PureEnv}
      {fnInputs : List RigidTy} {fnOutput : RigidTy} {fnSafety : Safety}
      {fnAbi : CallConv} {defPath : DefPath} {typeArgs : List RigidTy}
      {allocId : AllocId} {mem₁ : Memory} {borrows' : List BorrowEntry} :
      isReifyFnPointerCoercion coercionKind = true →
      stringEq coercionKind "UnsafeFnPointer" = false →
      evalOperand env op mem.borrows mem.globals cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok fnItem env₁ →
      isZstFnItemValue fnItem = true →
      targetTy.kind = .fnPtr fnInputs fnOutput fnSafety fnAbi →
      callConvEq fnAbi .rustIntrinsic = false →
      reifyCoercionSafetyCompatible coercionKind fnSafety = true →
      extractReifyCoercionTarget? coercionKind
          (operandTy cur.localDecls cur.layouts op) =
        some (defPath, typeArgs) →
      checkCalleeSig mem.callees defPath fnInputs fnOutput fnAbi typeArgs
          mem.traitImpls = true →
      internFnPtr mem defPath typeArgs (some targetTy.kind) = (allocId, mem₁) →
      assignLocalPlace env₁ mem₁.borrows dst
          (.ptr { allocId := allocId, offsetBytes := 0 } 8)
          cur.localDecls cur.layouts (length mem₁.callStack) =
        some (env₂, borrows') →
      mem₁.activeProtectors = [] →
      post env₂ { mem₁ with borrows := borrows' } →
      LiftStmtMem cur bbIdx stmtIdx env mem post
        { kind := .assign dst (.cast (.pointerCoercion coercionKind) op targetTy),
          span := span }
  /--
  Safe-to-unsafe function-pointer coercion
  `dst = op as unsafe fn(..) (PointerCoercion("UnsafeFnPointer"))`, preserving
  the pointer's `ProvenancePtr` after `evalUnsafeFnPointer` validates its
  signature in `Memory.fnPtrs`.
  -/
  | unsafeFnPointer {dst : Place} {coercionKind : String} {op : Operand}
      {targetTy : Ty} {span : String} {ptrVal : ProvenancePtr}
      {env₁ env₂ : PureEnv} {borrows' : List BorrowEntry} :
      coercionKind = "UnsafeFnPointer" →
      evalUnsafeFnPointer env op targetTy mem cur.localDecls cur.layouts =
        .ok (.ptr ptrVal 8) env₁ mem →
      assignLocalPlace env₁ mem.borrows dst (.ptr ptrVal 8)
          cur.localDecls cur.layouts (length mem.callStack) =
        some (env₂, borrows') →
      mem.activeProtectors = [] →
      post env₂ { mem with borrows := borrows' } →
      LiftStmtMem cur bbIdx stmtIdx env mem post
        { kind := .assign dst (.cast (.pointerCoercion coercionKind) op targetTy),
          span := span }
  /--
  Function-pointer to thin raw-pointer cast `dst = op as *const T (FnPtrToPtr)`,
  preserving `ptrVal : ProvenancePtr` after `evalFnPtrToPtr` validates its
  entry in `Memory.fnPtrs`.
  -/
  | fnPtrToPtr {dst : Place} {op : Operand} {targetTy : Ty} {span : String}
      {ptrVal : ProvenancePtr} {env₁ env₂ : PureEnv}
      {borrows' : List BorrowEntry} :
      evalFnPtrToPtr env op targetTy mem cur.localDecls cur.layouts =
        .ok (.ptr ptrVal 8) env₁ mem →
      assignLocalPlace env₁ mem.borrows dst (.ptr ptrVal 8)
          cur.localDecls cur.layouts (length mem.callStack) =
        some (env₂, borrows') →
      mem.activeProtectors = [] →
      post env₂ { mem with borrows := borrows' } →
      LiftStmtMem cur bbIdx stmtIdx env mem post
        { kind := .assign dst (.cast .fnPtrToPtr op targetTy), span := span }

/--
Unprojected `assignLocalPlace` reduction when `dst.projection = []` and
`dst.local_` holds a live slot in `env₁`.
-/
theorem assignLocalPlace_unprojected {env₁ env₂ : PureEnv}
    {borrows : List BorrowEntry} {dst : Place} {slot : LocalSlot} {val : Value}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {targetFrameDepth : Nat}
    (h_proj : dst.projection = [])
    (h_slot : get? env₁ dst.local_ = some slot)
    (h_live : slotLive slot = true)
    (h_set : set? env₁ dst.local_ (.init val) = some env₂) :
    assignLocalPlace env₁ borrows dst val localDecls layouts targetFrameDepth =
      some (env₂,
        invalidateConflictingBorrows borrows dst.local_ .none targetFrameDepth) := by
  rcases dst with ⟨dstLoc, dstProj⟩
  dsimp only at h_proj h_slot h_set
  subst h_proj
  unfold assignLocalPlace
  dsimp only []
  rw [h_slot]
  cases slot with
  | dead => cases h_live
  | uninit =>
    dsimp only []
    rw [h_set]
  | init _ =>
    dsimp only []
    rw [h_set]

/--
Unprojected function-pointer reification `dst = op as fn(..)
(PointerCoercion(ck))` (`dst.projection = []`), derived as a special case of
`LiftStmtMem.reifyFnPointerPlace`.
-/
theorem LiftStmtMem.reifyFnPointer {cur : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {mem : Memory}
    {post : PureEnv → Memory → Prop} {dst : Place} {coercionKind : String}
    {op : Operand} {targetTy : Ty} {span : String} {fnItem : Value}
    {env₁ env₂ : PureEnv} {fnInputs : List RigidTy} {fnOutput : RigidTy}
    {fnSafety : Safety} {fnAbi : CallConv} {defPath : DefPath}
    {typeArgs : List RigidTy} {allocId : AllocId} {mem₁ : Memory}
    {slot : LocalSlot}
    (h_kind : isReifyFnPointerCoercion coercionKind = true)
    (h_unsafe : stringEq coercionKind "UnsafeFnPointer" = false)
    (h_op :
      evalOperand env op mem.borrows mem.globals cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok fnItem env₁)
    (h_zst : isZstFnItemValue fnItem = true)
    (h_ty : targetTy.kind = .fnPtr fnInputs fnOutput fnSafety fnAbi)
    (h_abi : callConvEq fnAbi .rustIntrinsic = false)
    (h_safety : reifyCoercionSafetyCompatible coercionKind fnSafety = true)
    (h_target :
      extractReifyCoercionTarget? coercionKind
          (operandTy cur.localDecls cur.layouts op) =
        some (defPath, typeArgs))
    (h_sig :
      checkCalleeSig mem.callees defPath fnInputs fnOutput fnAbi typeArgs
          mem.traitImpls = true)
    (h_intern :
      internFnPtr mem defPath typeArgs (some targetTy.kind) = (allocId, mem₁))
    (h_proj : dst.projection = [])
    (h_slot : get? env₁ dst.local_ = some slot)
    (h_live : slotLive slot = true)
    (h_set :
      set? env₁ dst.local_ (.init (.ptr { allocId := allocId, offsetBytes := 0 } 8)) =
        some env₂)
    (h_prot : mem₁.activeProtectors = [])
    (h_next :
      post env₂
        { mem₁ with
          borrows :=
            invalidateConflictingBorrows mem₁.borrows dst.local_ .none
              (length mem₁.callStack) }) :
    LiftStmtMem cur bbIdx stmtIdx env mem post
      { kind := .assign dst (.cast (.pointerCoercion coercionKind) op targetTy),
        span := span } :=
  .reifyFnPointerPlace h_kind h_unsafe h_op h_zst h_ty h_abi h_safety h_target
    h_sig h_intern (assignLocalPlace_unprojected h_proj h_slot h_live h_set)
    h_prot h_next

/--
Every pure `LiftStmt` derivation (`FF-3.1`) embeds into `LiftStmtMem` at any
memory with no live borrows and no active protectors.
-/
theorem LiftStmt.toMem {cur : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {mem : Memory} {stmt : Statement}
    {P : PureEnv → Prop} {Q : PureEnv → Memory → Prop}
    (h : LiftStmt cur bbIdx stmtIdx env stmt P)
    (h_borrows : mem.borrows = []) (h_prot : mem.activeProtectors = [])
    (h_imp : ∀ env', P env' → Q env' mem) :
    LiftStmtMem cur bbIdx stmtIdx env mem Q stmt := by
  cases h <;> exact .pure h_borrows h_prot ‹_› (h_imp _ ‹_›)

/-- Memory-carrying statement judgment exposed in the `LiftStmt` namespace. -/
abbrev LiftStmt.Mem := LiftStmtMem

/-- Pure statement rule exposed in the `LiftStmt` namespace. -/
abbrev LiftStmt.pure := @LiftStmtMem.pure

/-- Function-pointer reification rule exposed in the `LiftStmt` namespace. -/
abbrev LiftStmt.reifyFnPointer := @LiftStmtMem.reifyFnPointer

/-- Projected function-pointer reification rule exposed in `LiftStmt`. -/
abbrev LiftStmt.reifyFnPointerPlace := @LiftStmtMem.reifyFnPointerPlace

/-- Safe-to-unsafe function-pointer coercion rule exposed in `LiftStmt`. -/
abbrev LiftStmt.unsafeFnPointer := @LiftStmtMem.unsafeFnPointer

/-- Function-pointer to raw-pointer cast rule exposed in `LiftStmt`. -/
abbrev LiftStmt.fnPtrToPtr := @LiftStmtMem.fnPtrToPtr

/-- Outcome of one lifted terminator step. -/
inductive FrameStep : Type where
  /-- Continue at activation frame `(bbIdx, stmtIdx, env, mem)`. -/
  | frame (bbIdx : BasicBlockIdx) (stmtIdx : Nat) (env : PureEnv) (mem : Memory)
  /-- Return `retVal` from the root frame. -/
  | ret (retVal : Value)

/--
Continuation for a terminator step of `body`: frames continue as `LiftFrame`
with the remaining `fuel`, and a root return must satisfy `post`.
-/
def FrameStep.Continues (body : CapturedMir) (post : Value → Prop) (fuel : Nat) :
    FrameStep → Prop
  | .frame bbIdx stmtIdx env mem => LiftFrame body bbIdx stmtIdx env mem post fuel
  | .ret retVal => post retVal

/--
Memory-carrying one-terminator judgment: executing `term` at the end of block
`bbIdx` (statement index `stmtIdx`) of the active body `cur` from `(env, mem)`
takes one step whose outcome satisfies `post`.

The call and tail-call constructors cover inlined calls to linked callees and
inline compiler intrinsics: `callDirect`/`tailCallDirect` for function-item
constants (including generic items and trait methods resolved through
`lookupCallee`), `callFnItem`/`tailCallFnItem` for zero-sized function items
(`RigidTy.fnDef`) stored in locals or projected places,
`callIndirect`/`tailCallIndirect` for calls through a reified function pointer
or `ClosureFnPointer`-coerced non-capturing closure resolved via
`Memory.fnPtrs`, and `callExactDiv` for direct calls to
`core::intrinsics::exact_div` evaluated inline by `evalTerminator`'s call
branch.

There are deliberately no rules for diverging calls (`target = none`), failed
assertions, or `TerminatorKind.unwindResume`: in MIR that rustc emits, none of
them can reach the normal root return that `LiftFrame` certifies. A diverging
callee faults if it returns (`SavedCallerFrame.isDiverging`). An unwind
continues only through cleanup blocks, and rustc's MIR validator forbids
cleanup blocks from returning or branching to non-cleanup blocks, so every
unwind ends in `.panic` or `.abort`; `LiftFrame.stmt` and `LiftFrame.term`
further enforce `blk.isCleanup = false` on every lifted step.
`liftBadDivergingReturnMir` and `liftDivergingPanicCallerMir` in
`Anneal.MirLiftBench` exercise both cases.
-/
inductive LiftTerminator (cur : CapturedMir) (bbIdx : BasicBlockIdx)
    (stmtIdx : Nat) (env : PureEnv) (mem : Memory) (post : FrameStep → Prop) :
    Terminator → Prop
  | goto {target : BasicBlockIdx} {span : String} :
      post (.frame target 0 env mem) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .goto target, span := span }
  | switchInt {discr : Operand} {targets : SwitchTargets} {span : String}
      {sc : ScalarInt} {env' : PureEnv} :
      evalOperand env discr mem.borrows mem.globals cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok (.scalar sc) env' →
      post (.frame (lookupSwitchTarget sc.bits targets.branches targets.otherwise)
        0 env' mem) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .switchInt discr targets, span := span }
  | assert {cond : Operand} {expected : Bool} {target : BasicBlockIdx}
      {unwind : UnwindAction} {span : String} {sc : ScalarInt} {env' : PureEnv} :
      evalOperand env cond mem.borrows mem.globals cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok (.scalar sc) env' →
      Nat.beq sc.bits (match expected with | true => 1 | false => 0) = true →
      post (.frame target 0 env' mem) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .assert cond expected target unwind, span := span }
  | drop {place : Place} {target : BasicBlockIdx} {unwind : UnwindAction}
      {span : String} {slot : LocalSlot} {env' : PureEnv} :
      get? env place.local_ = some slot →
      slotLive slot = true →
      place.projection = [] →
      set? env place.local_ .uninit = some env' →
      post (.frame target 0 env' mem) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .drop place target unwind, span := span }
  /-- Drop of a projected place (`place.projection = proj :: rest`). -/
  | dropProjected {place : Place} {target : BasicBlockIdx}
      {unwind : UnwindAction} {span : String} {proj : ProjectionElem}
      {rest : List ProjectionElem} {rootVal projVal : Value} :
      get? env place.local_ = some (.init rootVal) →
      place.projection = proj :: rest →
      readProjectedValue env rootVal (proj :: rest) = .ok projVal →
      post (.frame target 0 env mem) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .drop place target unwind, span := span }
  /--
  Return from the root frame (empty call stack) when no active function-entry
  protector blocks deallocating the root frame's locals.
  -/
  | return_ {span : String} {retVal : Value} :
      get? env 0 = some (.init retVal) →
      mem.callStack = [] →
      hasFrameDeallocProtectorConflict mem.borrows mem.activeProtectors
          0 (length env) = false →
      post (.ret retVal) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .return_, span := span }
  /--
  Return from an inlined callee: verify no active function-entry protector
  blocks deallocating the callee's locals, disable callee borrows via
  `returnFrameMem`, write `_0` into the saved caller's `destination` via
  `writeReturnDestination`, and resume the caller at its return target.
  -/
  | returnToCaller {span : String} {retVal : Value} {caller : SavedCallerFrame}
      {rest : List SavedCallerFrame} {callerEnv : PureEnv} {mem' : Memory} :
      get? env 0 = some (.init retVal) →
      mem.callStack = caller :: rest →
      hasFrameDeallocProtectorConflict mem.borrows mem.activeProtectors
          (length mem.callStack) (length env) = false →
      caller.isDiverging = false →
      writeReturnDestination caller.frame.locals
          (returnFrameMem mem (length env) caller rest) caller.destination retVal
          caller.callerBody.localDecls caller.callerBody.layouts =
        .ok callerEnv mem' →
      post (.frame caller.returnTarget 0 callerEnv mem') →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .return_, span := span }
  /--
  Inlined call of a function-item constant `func` naming `(defPath, typeArgs)`
  to the linked body `calleeBody` that `lookupCallee` resolves (instantiating a
  generic callee with `typeArgs`).
  -/
  | callDirect {func : Operand} {argOps : List Operand} {destination : Place}
      {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
      {defPath : DefPath} {typeArgs : List RigidTy} {argVals : List Value}
      {env' : PureEnv} {calleeBody : CapturedMir} :
      extractCallee? func = some (defPath, typeArgs) →
      evalOperands env argOps mem.borrows mem.globals cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok argVals env' →
      CalleeCtx mem.callees cur.layouts defPath typeArgs mem.traitImpls calleeBody →
      post (.frame 0 0 (initLocals calleeBody argVals)
        (callFrameMem cur bbIdx stmtIdx env' mem destination targetBb unwind
          calleeBody)) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .call func argOps destination (some targetBb) unwind, span := span }
  /--
  Inlined call of a zero-sized function item (`RigidTy.fnDef`) held in a local
  or projected operand `func`.
  -/
  | callFnItem {func : Operand} {argOps : List Operand} {destination : Place}
      {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
      {fnVal : Value} {envAfterFunc : PureEnv} {defPath : DefPath}
      {typeArgs : List RigidTy} {argVals : List Value} {env' : PureEnv}
      {calleeBody : CapturedMir} :
      extractCalleeDefPath? func = none →
      evalOperand env func mem.borrows mem.globals cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok fnVal envAfterFunc →
      isZstFnItemValue fnVal = true →
      extractFnItemTarget? (operandTy cur.localDecls cur.layouts func) =
        some (defPath, typeArgs) →
      evalOperands envAfterFunc argOps mem.borrows mem.globals cur.layouts
          mem.callerLocals (callStack := mem.callStack) =
        .ok argVals env' →
      CalleeCtx mem.callees cur.layouts defPath typeArgs mem.traitImpls calleeBody →
      post (.frame 0 0 (initLocals calleeBody argVals)
        (callFrameMem cur bbIdx stmtIdx env' mem destination targetBb unwind
          calleeBody)) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .call func argOps destination (some targetBb) unwind, span := span }
  /--
  Inlined call through a reified function pointer: `func` evaluates to an
  8-byte pointer at offset `0` with no stack-borrow provenance whose `allocId`
  names `fnEntry` in `Memory.fnPtrs`, the entry's signature is compatible with
  the call site, and the linked callee that `lookupCallee` resolves for
  `(fnEntry.defPath, fnEntry.typeArgs)` passes `checkCalleeTargetCompatible`.
  -/
  | callIndirect {func : Operand} {argOps : List Operand} {destination : Place}
      {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
      {ptrVal : ProvenancePtr} {envAfterFunc : PureEnv} {fnEntry : FnPtrEntry}
      {argVals : List Value} {env' : PureEnv} {calleeBody : CapturedMir} :
      extractCalleeDefPath? func = none →
      evalOperand env func mem.borrows mem.globals cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok (.ptr ptrVal 8) envAfterFunc →
      ptrVal.offsetBytes = 0 →
      lookupBorrow mem.borrows ptrVal.tag = none →
      lookupFnPtr mem.fnPtrs ptrVal.allocId = some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps)
          (operandTy cur.localDecls cur.layouts func) = true →
      evalOperands envAfterFunc argOps mem.borrows mem.globals cur.layouts
          mem.callerLocals (callStack := mem.callStack) =
        .ok argVals env' →
      CalleeCtx mem.callees cur.layouts fnEntry.defPath fnEntry.typeArgs
          mem.traitImpls calleeBody →
      checkCalleeTargetCompatible
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs,
            fnSig := fnEntry.fnSig, isIndirect := true }
          calleeBody (length argVals) = true →
      post (.frame 0 0 (initLocals calleeBody argVals)
        (callFrameMem cur bbIdx stmtIdx env' mem destination targetBb unwind
          calleeBody)) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .call func argOps destination (some targetBb) unwind, span := span }
  /--
  Inline `core::intrinsics::exact_div` call (`isDirectExactDivTarget`): when no
  linked override exists in `mem.callees`, `evalTerminator`'s call branch
  evaluates `evalExactDiv` on the two scalar arguments, with the signedness
  that `resolveIntrinsicIsSigned` reads from the call's type arguments, and
  writes `.scalar retScalar` to `destination` in the current frame.
  -/
  | callExactDiv {func lhsOp : Operand} {rhsOps : List Operand}
      {destination : Place} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
      {span : String} {resolvedTarget : ResolvedCallTarget}
      {envAfterFunc env' updatedEnv : PureEnv}
      {isSigned : Bool} {lhs rhs retScalar : ScalarInt} :
      resolveCallTarget
          (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
          func (length (lhsOp :: rhsOps)) cur.localDecls cur.layouts =
        .ok resolvedTarget envAfterFunc →
      evalOperands envAfterFunc (lhsOp :: rhsOps) mem.borrows mem.globals
          cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok [.scalar lhs, .scalar rhs] env' →
      lookupCallee mem.callees cur.layouts resolvedTarget.defPath
          resolvedTarget.typeArgs mem.traitImpls = none →
      isDirectExactDivTarget resolvedTarget = true →
      resolveIntrinsicIsSigned resolvedTarget cur.localDecls cur.layouts
          (lhsOp :: rhsOps) = some isSigned →
      evalExactDiv lhs rhs isSigned = some retScalar →
      (match destination.projection with
       | .deref :: _ => PlaceWriteResult.ub
       | _ =>
         writePlaceValue env' mem.borrows destination (.scalar retScalar)
           (callStack := mem.callStack)) =
        .ok updatedEnv →
      post (.frame targetBb 0 updatedEnv
        (invalidateDirectDestWriteBorrows mem env' destination)) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .call func (lhsOp :: rhsOps) destination (some targetBb) unwind,
          span := span }
  /--
  Inlined tail call (`TerminatorKind.tailCall`) of a function-item constant
  `func` naming `(defPath, typeArgs)`.
  -/
  | tailCallDirect {func : Operand} {argOps : List Operand} {span : String}
      {defPath : DefPath} {typeArgs : List RigidTy} {argVals : List Value}
      {env' : PureEnv} {calleeBody : CapturedMir} :
      extractCallee? func = some (defPath, typeArgs) →
      evalOperands env argOps mem.borrows mem.globals cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok argVals env' →
      CalleeCtx mem.callees cur.layouts defPath typeArgs mem.traitImpls calleeBody →
      hasFrameDeallocProtectorConflict mem.borrows mem.activeProtectors
          (length mem.callStack) (length env) = false →
      post (.frame 0 0 (initLocals calleeBody argVals)
        (tailCallFrameMem mem (length env) calleeBody)) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .tailCall func argOps, span := span }
  /--
  Inlined tail call (`TerminatorKind.tailCall`) of a zero-sized function item
  (`RigidTy.fnDef`) held in a local or projected operand `func`.
  -/
  | tailCallFnItem {func : Operand} {argOps : List Operand} {span : String}
      {fnVal : Value} {envAfterFunc : PureEnv} {defPath : DefPath}
      {typeArgs : List RigidTy} {argVals : List Value} {env' : PureEnv}
      {calleeBody : CapturedMir} :
      extractCalleeDefPath? func = none →
      evalOperand env func mem.borrows mem.globals cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok fnVal envAfterFunc →
      isZstFnItemValue fnVal = true →
      extractFnItemTarget? (operandTy cur.localDecls cur.layouts func) =
        some (defPath, typeArgs) →
      evalOperands envAfterFunc argOps mem.borrows mem.globals cur.layouts
          mem.callerLocals (callStack := mem.callStack) =
        .ok argVals env' →
      CalleeCtx mem.callees cur.layouts defPath typeArgs mem.traitImpls calleeBody →
      hasFrameDeallocProtectorConflict mem.borrows mem.activeProtectors
          (length mem.callStack) (length env) = false →
      post (.frame 0 0 (initLocals calleeBody argVals)
        (tailCallFrameMem mem (length env) calleeBody)) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .tailCall func argOps, span := span }
  /--
  Inlined tail call (`TerminatorKind.tailCall`) through a reified function
  pointer in `Memory.fnPtrs`.
  -/
  | tailCallIndirect {func : Operand} {argOps : List Operand} {span : String}
      {ptrVal : ProvenancePtr} {envAfterFunc : PureEnv} {fnEntry : FnPtrEntry}
      {argVals : List Value} {env' : PureEnv} {calleeBody : CapturedMir} :
      extractCalleeDefPath? func = none →
      evalOperand env func mem.borrows mem.globals cur.layouts mem.callerLocals (callStack := mem.callStack) =
        .ok (.ptr ptrVal 8) envAfterFunc →
      ptrVal.offsetBytes = 0 →
      lookupBorrow mem.borrows ptrVal.tag = none →
      lookupFnPtr mem.fnPtrs ptrVal.allocId = some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps)
          (operandTy cur.localDecls cur.layouts func) = true →
      evalOperands envAfterFunc argOps mem.borrows mem.globals cur.layouts
          mem.callerLocals (callStack := mem.callStack) =
        .ok argVals env' →
      CalleeCtx mem.callees cur.layouts fnEntry.defPath fnEntry.typeArgs
          mem.traitImpls calleeBody →
      checkCalleeTargetCompatible
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs,
            fnSig := fnEntry.fnSig, isIndirect := true }
          calleeBody (length argVals) = true →
      hasFrameDeallocProtectorConflict mem.borrows mem.activeProtectors
          (length mem.callStack) (length env) = false →
      post (.frame 0 0 (initLocals calleeBody argVals)
        (tailCallFrameMem mem (length env) calleeBody)) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .tailCall func argOps, span := span }

/-- `evalPureStmt` succeeds only on statements accepted by `isPureStatement`. -/
theorem isPureStatement_of_evalPureStmt {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmt : Statement}
    (h : evalPureStmt body bbIdx stmtIdx env stmt = some env') :
    isPureStatement stmt.kind = true := by
  unfold evalPureStmt at h
  split at h
  · assumption
  · cases h

/--
Reduce `stepMirFn` at a statement of the active body `cur`
(`mem.activeCallee.getD body = cur`).
-/
theorem stepMirFn_frame_stmt {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {stmt : Statement}
    (h_cur : s.memory.activeCallee.getD body = cur)
    (h_phase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (h_bb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (h_get : get? blk.statements s.frame.stmtIdx = some stmt) :
    stepMirFn body s = evalStmt s stmt cur.localDecls cur.layouts := by
  unfold stepMirFn
  rw [h_cur]
  dsimp only []
  rcases h_phase with hp | hp <;>
    (rw [hp]; dsimp only []; rw [h_bb]; dsimp only []; rw [h_get])

/--
Reduce `stepMirFn` at the terminator of block `blk` of the active body `cur`.
-/
theorem stepMirFn_frame_term {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData}
    (h_cur : s.memory.activeCallee.getD body = cur)
    (h_phase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (h_bb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (h_end : s.frame.stmtIdx = length blk.statements) :
    stepMirFn body s = evalTerminator s blk.terminator (some cur) := by
  have h_none : get? blk.statements s.frame.stmtIdx = none := by
    rw [h_end]
    simp [Trusted.Sequence.get?, Trusted.Sequence.length]
  have h_beq : (s.frame.stmtIdx == length blk.statements) = true := by
    rw [h_end]
    simp
  unfold stepMirFn
  rw [h_cur]
  dsimp only []
  rcases h_phase with hp | hp <;>
    (rw [hp]; dsimp only []; rw [h_bb]; dsimp only []; rw [h_none]; dsimp only [];
     rw [h_beq]; rfl)

/-- One `stepMirFn` transition followed by `evalNodeWP` proves `LiftFrame`. -/
theorem LiftFrame.of_stepMirFn {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {mem : Memory} {post : Value → Prop}
    {fuel : Nat} {node : MirStepNode}
    (h_step :
      stepMirFn body
          (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem) =
        node)
    (h_node :
      evalNodeWP
        (fun st' => wpMirExecSym fuel body st' (mirNormalPost (fun retVal _ => post retVal)))
        (mirNormalPost (fun retVal _ => post retVal))
        node) :
    LiftFrame body bbIdx stmtIdx env mem post (fuel + 1) := by
  unfold LiftFrame wpMirExecSym
  rw [evalSymNodeTree_eq, stepMirExecSymTree_eval]
  show evalNodeWP _ _ (stepMirFn body _)
  rw [h_step]
  exact h_node

/-- A zero-sized function-item value is `.unit` or the empty aggregate. -/
theorem isZstFnItemValue_eq_true {v : Value} (h : isZstFnItemValue v = true) :
    v = .unit ∨ v = .aggregate 0 [] := by
  unfold isZstFnItemValue at h
  split at h
  · exact Or.inl rfl
  · exact Or.inr rfl
  · cases h

/--
Success path of `evalStmt` for `StatementKind.assign dst rv` when `evalRvalue`
returns `.ok val env₁ mem₁`, `mem₁.activeProtectors = []`, and
`assignLocalPlace` succeeds.
-/
theorem evalStmt_assign_of_evalRvalue {bbIdx : BasicBlockIdx} {stmtIdx : Nat}
    {env env₁ env₂ : PureEnv} {mem mem₁ : Memory} {dst : Place} {rv : Rvalue}
    {span : String} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {val : Value} {borrows' : List BorrowEntry}
    (h_rv : evalRvalue env rv mem localDecls layouts = .ok val env₁ mem₁)
    (h_prot : mem₁.activeProtectors = [])
    (h_write :
      assignLocalPlace env₁ mem₁.borrows dst val localDecls layouts
        (length mem₁.callStack) = some (env₂, borrows')) :
    evalStmt
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        { kind := .assign dst rv, span := span } localDecls layouts =
      .step
        (PureState.toMachineState
          { bb := bbIdx, stmtIdx := stmtIdx + 1, env := env₂ }
          { mem₁ with borrows := borrows' }) := by
  rcases dst with ⟨dstLoc, dstProj⟩
  unfold evalStmt
  dsimp only [PureState.toMachineState]
  rw [h_rv]
  dsimp only []
  unfold assignLocalPlace at h_write
  dsimp only [] at h_write
  cases dstProj with
  | nil =>
    dsimp only [] at h_write ⊢
    cases h_get : get? env₁ dstLoc with
    | none => rw [h_get] at h_write; cases h_write
    | some slot =>
      rw [h_get] at h_write
      cases slot with
      | dead => cases h_write
      | uninit =>
        dsimp only [] at h_write ⊢
        cases h_set : set? env₁ dstLoc (.init val) with
        | none => rw [h_set] at h_write; cases h_write
        | some locals₂ =>
          rw [h_set] at h_write
          injection h_write with h_pair
          injection h_pair with h_env h_borrows
          subst h_env h_borrows
          dsimp only []
          rw [h_prot]
          rfl
      | init _ =>
        dsimp only [] at h_write ⊢
        cases h_set : set? env₁ dstLoc (.init val) with
        | none => rw [h_set] at h_write; cases h_write
        | some locals₂ =>
          rw [h_set] at h_write
          injection h_write with h_pair
          injection h_pair with h_env h_borrows
          subst h_env h_borrows
          dsimp only []
          rw [h_prot]
          rfl
  | cons proj rest =>
    cases proj <;>
      first
      | cases h_write
      | (dsimp only [] at h_write ⊢
         cases h_get : get? env₁ dstLoc with
         | none => rw [h_get] at h_write; cases h_write
         | some slot =>
           rw [h_get] at h_write
           cases slot with
           | dead => cases h_write
           | uninit => cases h_write
           | init rootVal =>
             dsimp only [] at h_write ⊢
             cases h_wp :
                 writeProjectedForLocal
                   env₁
                   localDecls
                   layouts
                   dstLoc
                   (ensureNestedFieldShells rootVal (_ :: rest))
                   (_ :: rest)
                   val with
             | ub => rw [h_wp] at h_write; cases h_write
             | unsupported => rw [h_wp] at h_write; cases h_write
             | ok rootVal' =>
               rw [h_wp] at h_write
               dsimp only [] at h_write ⊢
               cases h_set : set? env₁ dstLoc (.init rootVal') with
               | none => rw [h_set] at h_write; cases h_write
               | some locals₂ =>
                 rw [h_set] at h_write
                 injection h_write with h_pair
                 injection h_pair with h_env h_borrows
                 subst h_env h_borrows
                 dsimp only []
                 rw [h_prot]
                 rfl)

/--
Success path of the trusted `evalReifyFnPointer` for a reifying coercion: the
function item is interned in `Memory.fnPtrs` and evaluates to the synthetic
8-byte pointer at offset `0`.
-/
theorem evalRvalue_reifyFnPointer {env env₁ : PureEnv} {mem mem₁ : Memory}
    {coercionKind : String} {op : Operand} {targetTy : Ty}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {fnItem : Value}
    {fnInputs : List RigidTy} {fnOutput : RigidTy} {fnSafety : Safety}
    {fnAbi : CallConv} {defPath : DefPath} {typeArgs : List RigidTy}
    {allocId : AllocId}
    (h_kind : isReifyFnPointerCoercion coercionKind = true)
    (h_unsafe : stringEq coercionKind "UnsafeFnPointer" = false)
    (h_op : evalOperand env op mem.borrows mem.globals layouts mem.callerLocals (callStack := mem.callStack) =
      .ok fnItem env₁)
    (h_zst : isZstFnItemValue fnItem = true)
    (h_ty : targetTy.kind = .fnPtr fnInputs fnOutput fnSafety fnAbi)
    (h_abi : callConvEq fnAbi .rustIntrinsic = false)
    (h_safety : reifyCoercionSafetyCompatible coercionKind fnSafety = true)
    (h_target : extractReifyCoercionTarget? coercionKind
        (operandTy localDecls layouts op) = some (defPath, typeArgs))
    (h_sig : checkCalleeSig mem.callees defPath fnInputs fnOutput fnAbi typeArgs
        mem.traitImpls = true)
    (h_intern : internFnPtr mem defPath typeArgs (some targetTy.kind) =
      (allocId, mem₁)) :
    evalRvalue env (.cast (.pointerCoercion coercionKind) op targetTy) mem
        localDecls layouts =
      .ok (.ptr { allocId := allocId, offsetBytes := 0 } 8) env₁ mem₁ := by
  have h_fst : (internFnPtr mem defPath typeArgs (some targetTy.kind)).1 = allocId := by
    rw [h_intern]
  have h_snd : (internFnPtr mem defPath typeArgs (some targetTy.kind)).2 = mem₁ := by
    rw [h_intern]
  rw [← h_fst, ← h_snd]
  rcases isZstFnItemValue_eq_true h_zst with rfl | rfl <;>
    simp only [evalRvalue, evalReifyFnPointer, h_kind, h_unsafe, h_op, h_ty, h_abi,
      h_safety, h_target, h_sig, Bool.not_false, Bool.true_and]

/--
Soundness of `LiftStmtMem`: the trusted `evalStmt` transition satisfies the
continuation `LiftFrame` at the next statement.
-/
theorem LiftStmtMem.evalNodeWP_of {body cur : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {mem : Memory}
    {stmt : Statement} {post : Value → Prop} {fuel : Nat}
    (h : LiftStmtMem cur bbIdx stmtIdx env mem
      (fun env' mem' => LiftFrame body bbIdx (stmtIdx + 1) env' mem' post fuel) stmt) :
    evalNodeWP
      (fun st' => wpMirExecSym fuel body st' (mirNormalPost (fun retVal _ => post retVal)))
      (mirNormalPost (fun retVal _ => post retVal))
      (evalStmt
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        stmt cur.localDecls cur.layouts) := by
  cases h with
  | pure h_borrows h_prot h_eval h_next =>
    rw [evalStmt_toMachineState_eq_withMem_of_frameFree _ mem _ _ _
      (isPureStatement_of_evalPureStmt h_eval) h_borrows h_prot]
    rw [evalPureStmt_eq_step h_eval]
    exact h_next
  | reifyFnPointerPlace h_kind h_unsafe h_op h_zst h_ty h_abi h_safety h_target
      h_sig h_intern h_write h_prot h_next =>
    have h_rv :=
      evalRvalue_reifyFnPointer h_kind h_unsafe h_op h_zst h_ty h_abi h_safety
        h_target h_sig h_intern
    rw [evalStmt_assign_of_evalRvalue h_rv h_prot h_write]
    exact h_next
  | unsafeFnPointer h_ck h_eval h_write h_prot h_next =>
    rename_i dst coercionKind op targetTy span ptrVal env₁ env₂ borrows'
    subst h_ck
    have h_rv :
        evalRvalue env (.cast (.pointerCoercion "UnsafeFnPointer") op targetTy) mem
            cur.localDecls cur.layouts =
          .ok (.ptr ptrVal 8) env₁ mem := by
      unfold evalRvalue evalReifyFnPointer
      dsimp only [isReifyFnPointerCoercion, stringEq]
      exact h_eval
    rw [evalStmt_assign_of_evalRvalue h_rv h_prot h_write]
    exact h_next
  | fnPtrToPtr h_eval h_write h_prot h_next =>
    rename_i dst op targetTy span ptrVal env₁ env₂ borrows'
    have h_rv :
        evalRvalue env (.cast .fnPtrToPtr op targetTy) mem cur.localDecls cur.layouts =
          .ok (.ptr ptrVal 8) env₁ mem :=
      h_eval
    rw [evalStmt_assign_of_evalRvalue h_rv h_prot h_write]
    exact h_next

/--
Statement step on an activation frame: a `LiftStmtMem` step in a non-cleanup
basic block (`blk.isCleanup = false`) of the active body `cur` refines
`wpMirExecSym` by one unit of fuel.
-/
theorem LiftFrame.stmt {body cur : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {mem : Memory} {blk : BasicBlockData}
    {stmt : Statement} {post : Value → Prop} {fuel : Nat}
    (h_cur : mem.activeCallee.getD body = cur)
    (h_phase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (h_bb : get? cur.basicBlocks bbIdx = some blk)
    (h_cleanup : blk.isCleanup = false)
    (h_get : get? blk.statements stmtIdx = some stmt)
    (h_lift : LiftStmtMem cur bbIdx stmtIdx env mem
      (fun env' mem' => LiftFrame body bbIdx (stmtIdx + 1) env' mem' post fuel) stmt) :
    LiftFrame body bbIdx stmtIdx env mem post (fuel + 1) :=
  LiftFrame.of_stepMirFn (stepMirFn_frame_stmt h_cur h_phase h_bb h_get)
    (LiftStmtMem.evalNodeWP_of h_lift)

/--
`resolveCallTarget` reduction for a zero-sized function item (`RigidTy.fnDef`)
held in a local or projected operand `func`.
-/
theorem resolveCallTarget_fnItem (s : MachineState) (func : Operand)
    (argCount : Nat) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (fnVal : Value)
    (localsAfterFunc : List LocalSlot) (defPath : DefPath)
    (typeArgs : List RigidTy)
    (h_nonConst : extractCalleeDefPath? func = none)
    (h_eval :
      evalOperand s.frame.locals func s.memory.borrows s.memory.globals
          bodyLayouts s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok fnVal localsAfterFunc)
    (h_zst : isZstFnItemValue fnVal = true)
    (h_target :
      extractFnItemTarget? (operandTy bodyLocalDecls bodyLayouts func) =
        some (defPath, typeArgs)) :
    resolveCallTarget s func argCount bodyLocalDecls bodyLayouts =
      .ok
        { defPath := defPath
          typeArgs := typeArgs
          fnSig := none
          isIndirect := false }
        localsAfterFunc := by
  rcases isZstFnItemValue_eq_true h_zst with rfl | rfl
  · unfold resolveCallTarget
    rw [h_nonConst, h_eval, h_target]
  · unfold resolveCallTarget
    rw [h_nonConst, h_eval, h_target]
    rfl

/--
`resolveCallTarget` reduction for a constant function-item operand `func`
satisfying `extractCallee? func = some (defPath, typeArgs)`.
-/
theorem resolveCallTarget_of_extractCallee (s : MachineState) (func : Operand)
    (argCount : Nat) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (defPath : DefPath)
    (typeArgs : List RigidTy)
    (h_callee : extractCallee? func = some (defPath, typeArgs)) :
    resolveCallTarget s func argCount bodyLocalDecls bodyLayouts =
      .ok
        { defPath := defPath
          typeArgs := typeArgs
          fnSig := none
          isIndirect := false }
        s.frame.locals := by
  have h_path : extractCalleeDefPath? func = some defPath := by
    unfold extractCallee? at h_callee
    split at h_callee
    · rename_i p h_p
      injection h_callee with h_pair
      injection h_pair with h_dp _
      rw [h_p, h_dp]
    · cases h_callee
  have h_args' : extractCalleeTypeArgs func = typeArgs := by
    unfold extractCallee? at h_callee
    rw [h_path] at h_callee
    injection h_callee with h_pair
    injection h_pair
  unfold resolveCallTarget
  rw [h_path, h_args']

/--
Soundness of `LiftTerminator`: the trusted `evalTerminator` transition
satisfies the continuation `FrameStep.Continues`.
-/
theorem LiftTerminator.evalNodeWP_of {body cur : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {mem : Memory}
    {term : Terminator} {post : Value → Prop} {fuel : Nat}
    (h : LiftTerminator cur bbIdx stmtIdx env mem
      (FrameStep.Continues body post fuel) term) :
    evalNodeWP
      (fun st' => wpMirExecSym fuel body st' (mirNormalPost (fun retVal _ => post retVal)))
      (mirNormalPost (fun retVal _ => post retVal))
      (evalTerminator
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        term (some cur)) := by
  cases h with
  | goto h_next => exact h_next
  | switchInt h_eval h_next =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_eval]
    exact h_next
  | assert h_eval h_cond h_next =>
    rename_i cond expected target unwind span sc env'
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_eval]
    -- The expected-bit `match` in the premise and in `evalTerminator` are
    -- distinct auxiliary matchers, so align them by splitting on `expected`.
    cases expected <;> (dsimp only [] at h_cond ⊢; rw [h_cond]; exact h_next)
  | drop h_get h_live h_proj h_set h_next =>
    rename_i place target unwind span slot env'
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_get]
    cases slot with
    | dead => cases h_live
    | uninit =>
      dsimp only []
      rw [h_proj]
      dsimp only []
      rw [h_set]
      exact h_next
    | init _ =>
      dsimp only []
      rw [h_proj]
      dsimp only []
      rw [h_set]
      exact h_next
  | dropProjected h_get h_proj h_read h_next =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_get]
    dsimp only []
    rw [h_proj]
    dsimp only []
    rw [h_read]
    exact h_next
  | return_ h_ret h_stack h_noDealloc h_post =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_ret]
    dsimp only []
    rw [h_stack]
    dsimp only [Trusted.Sequence.length, List.length] at h_noDealloc ⊢
    rw [h_noDealloc]
    exact h_post
  | returnToCaller h_ret h_stack h_noDealloc h_div h_write h_next =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_ret]
    dsimp only []
    rw [h_noDealloc]
    dsimp only []
    unfold returnFrameMem at h_write
    revert h_write
    rw [h_stack]
    dsimp only []
    rw [h_div]
    dsimp only []
    intro h_write
    rw [h_write]
    exact h_next
  | callDirect h_callee h_args h_ctx h_next =>
    rename_i func argOps destination targetBb unwind span defPath typeArgs argVals
      env' calleeBody
    have h_res :=
      resolveCallTarget_of_extractCallee
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func (length argOps) cur.localDecls cur.layouts defPath typeArgs h_callee
    have h_tree :=
      evalTerminatorSymTree_call_inlined_of_calleeCtx
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func argOps destination targetBb unwind span cur _ env argVals env' calleeBody
        h_res h_args h_ctx (checkCalleeTargetCompatible_direct _ _ _ _ _)
    rw [← evalTerminatorSymTree_eval, h_tree]
    exact h_next
  | callFnItem h_const h_func h_zst h_target h_args h_ctx h_next =>
    rename_i func argOps destination targetBb unwind span fnVal envAfterFunc
      defPath typeArgs argVals env' calleeBody
    have h_res :=
      resolveCallTarget_fnItem
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func (length argOps) cur.localDecls cur.layouts fnVal envAfterFunc
        defPath typeArgs h_const h_func h_zst h_target
    have h_tree :=
      evalTerminatorSymTree_call_inlined_of_calleeCtx
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func argOps destination targetBb unwind span cur _ envAfterFunc argVals
        env' calleeBody h_res h_args h_ctx
        (checkCalleeTargetCompatible_direct _ _ _ _ _)
    rw [← evalTerminatorSymTree_eval, h_tree]
    exact h_next
  | callIndirect h_const h_func h_off h_noBorrow h_fnPtr h_compat h_args h_ctx
      h_target h_next =>
    rename_i func argOps destination targetBb unwind span ptrVal envAfterFunc fnEntry
      argVals env' calleeBody
    have h_res :=
      resolveCallTarget_indirect_fnPtr
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func (length argOps) cur.localDecls cur.layouts ptrVal envAfterFunc fnEntry
        h_const h_func h_off h_noBorrow h_fnPtr h_compat
    have h_tree :=
      evalTerminatorSymTree_call_inlined_of_calleeCtx
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func argOps destination targetBb unwind span cur _ envAfterFunc argVals env'
        calleeBody h_res h_args h_ctx h_target
    rw [← evalTerminatorSymTree_eval, h_tree]
    exact h_next
  | callExactDiv h_res h_args h_lookup h_exact h_signed h_div h_write h_next =>
    unfold evalTerminator
    dsimp only [bodyLocalDeclsOf]
    rw [h_res]
    dsimp only [PureState.toMachineState]
    rw [h_args]
    dsimp only []
    rw [h_lookup]
    dsimp only []
    rw [h_exact]
    dsimp only []
    rw [h_signed]
    dsimp only []
    rw [h_div]
    rename_i func lhsOp rhsOps destination _ _ _ _ _ _ _ _ _ _ _
    rcases destination with ⟨dLoc, _ | ⟨dHd, dTl⟩⟩
    · dsimp only [writeIntrinsicReturn] at h_write ⊢
      rw [h_write]
      exact h_next
    · cases dHd <;>
      first
      | (cases h_write; done)
      | (dsimp only [writeIntrinsicReturn] at h_write ⊢; rw [h_write]; exact h_next)
  | tailCallDirect h_callee h_args h_ctx h_noDealloc h_next =>
    rename_i func argOps span defPath typeArgs argVals env' calleeBody
    have h_res :=
      resolveCallTarget_of_extractCallee
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func (length argOps) cur.localDecls cur.layouts defPath typeArgs h_callee
    have h_tree :=
      evalTerminatorSymTree_tailCall_inlined_of_calleeCtx
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func argOps span cur _ env argVals env' calleeBody h_res h_args h_ctx
        (checkCalleeTargetCompatible_direct _ _ _ _ _) h_noDealloc
    rw [← evalTerminatorSymTree_eval, h_tree]
    exact h_next
  | tailCallFnItem h_const h_func h_zst h_target h_args h_ctx h_noDealloc h_next =>
    rename_i func argOps span fnVal envAfterFunc defPath typeArgs argVals env'
      calleeBody
    have h_res :=
      resolveCallTarget_fnItem
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func (length argOps) cur.localDecls cur.layouts fnVal envAfterFunc
        defPath typeArgs h_const h_func h_zst h_target
    have h_tree :=
      evalTerminatorSymTree_tailCall_inlined_of_calleeCtx
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func argOps span cur _ envAfterFunc argVals env' calleeBody h_res h_args
        h_ctx (checkCalleeTargetCompatible_direct _ _ _ _ _) h_noDealloc
    rw [← evalTerminatorSymTree_eval, h_tree]
    exact h_next
  | tailCallIndirect h_const h_func h_off h_noBorrow h_fnPtr h_compat h_args
      h_ctx h_target h_noDealloc h_next =>
    rename_i func argOps span ptrVal envAfterFunc fnEntry argVals env' calleeBody
    have h_res :=
      resolveCallTarget_indirect_fnPtr
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func (length argOps) cur.localDecls cur.layouts ptrVal envAfterFunc fnEntry
        h_const h_func h_off h_noBorrow h_fnPtr h_compat
    have h_tree :=
      evalTerminatorSymTree_tailCall_inlined_of_calleeCtx
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func argOps span cur _ envAfterFunc argVals env' calleeBody h_res h_args
        h_ctx h_target h_noDealloc
    rw [← evalTerminatorSymTree_eval, h_tree]
    exact h_next

/--
Terminator step on an activation frame: a `LiftTerminator` step in a
non-cleanup basic block (`blk.isCleanup = false`) of the active body `cur`
refines `wpMirExecSym` by one unit of fuel.
-/
theorem LiftFrame.term {body cur : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {mem : Memory} {blk : BasicBlockData}
    {post : Value → Prop} {fuel : Nat}
    (h_cur : mem.activeCallee.getD body = cur)
    (h_phase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (h_bb : get? cur.basicBlocks bbIdx = some blk)
    (h_cleanup : blk.isCleanup = false)
    (h_end : stmtIdx = length blk.statements)
    (h_lift : LiftTerminator cur bbIdx stmtIdx env mem
      (FrameStep.Continues body post fuel) blk.terminator) :
    LiftFrame body bbIdx stmtIdx env mem post (fuel + 1) :=
  LiftFrame.of_stepMirFn (stepMirFn_frame_term h_cur h_phase h_bb h_end)
    (LiftTerminator.evalNodeWP_of h_lift)

/-- Fuel monotonicity for `LiftFrame`. -/
theorem LiftFrame.mono {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {mem : Memory} {post : Value → Prop}
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    (h : LiftFrame body bbIdx stmtIdx env mem post f₁) :
    LiftFrame body bbIdx stmtIdx env mem post f₂ :=
  wpMirExecSym_mono h_le h

/--
Entry bridge for bodies with linked callees: a lifted entry frame at the
callee-aware initial memory proves `MirWpConverges` from
`initMachineStateWithCallees`, the initial state of `Claim.holds`.
-/
theorem LiftFrame.mirWpConverges_withCallees {body : CapturedMir}
    {args : List Value} {callees : List CapturedMir} {post : Value → Prop}
    {fuel : Nat}
    (h : LiftFrame body 0 0 (initPureEnv body args)
      (initMachineStateWithCallees body args callees).memory post fuel) :
    MirWpConverges body (initMachineStateWithCallees body args callees)
      (mirNormalPost (fun retVal _ => post retVal)) := by
  refine ⟨fuel, ?_⟩
  unfold LiftFrame at h
  unfold wpMirSym
  rw [initMachineStateWithCallees_eq_withMemory]
  exact h

/--
Discharge the trusted `VerificationResult c` of a claim with linked callees
`c.callees` whose precondition pins the arguments to `args₀`, from a lifted
entry frame.
-/
theorem LiftFrame.verificationResult (c : Claim) (args₀ : List Value)
    {fuel : Nat}
    (h_pre : ∀ args, c.pre args → args = args₀)
    (h : LiftFrame c.body 0 0 (initPureEnv c.body args₀)
      (initMachineStateWithCallees c.body args₀ c.callees).memory (c.post args₀) fuel) :
    VerificationResult c :=
  verifyMirNoPanic_of_wpConverges c (fun args h_args => by
    rw [h_pre args h_args]
    exact LiftFrame.mirWpConverges_withCallees h)

end FrameLifting

/-!
The lifting judgments are opaque outside this module: callers, including the
`#mir_lift` elaborator, must use the rules above instead of unfolding the
judgments into `wpMirExecSym`, which keeps `body` opaque in goal states and
prevents `isDefEq` from falling back to whole-body symbolic evaluation.
-/
attribute [irreducible] LiftBlock LiftResidualBlock LiftStmtsTerminator LiftFrame

end Anneal.MirLiftCore

set_option linter.all false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Anneal.PureMirExec

open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.ITreeWP
open Anneal.MirFuelFree
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
# Fuel-Free Specification and MIR Lifting Infrastructure (`Anneal.MirSpecLift`)

Provides:
1. Fuel-free `MirBoolPredicateHolds` introduction and elimination bridges over
   `PureMirConverges` and `MirWpConverges`.
2. Fast `CapturedMir` symbolic and CFG evaluation (`wpCfgStep`, `wpBlockLinear`,
   `runCfgSteps`) parameterized directly by `body : CapturedMir` with internal
   structural step bounds (`defaultSpecSteps`, `defaultCfgSteps`) so downstream
   proofs require zero manual fuel constants and zero per-file evaluator boilerplate.
-/

theorem mirBoolPredicateHolds_elim_of_pureExec
    (specBody : CapturedMir) (args : List Value) {P : Prop} [Decidable P]
    (h_pure : checkPureMir specBody = true)
    (h_conv : PureMirConverges specBody (initPureState specBody args)
      (· = .scalar { bits := if P then 1 else 0, sizeBytes := 1 })) :
    MirBoolPredicateHolds specBody args → P := by
  intro h_holds
  have h_conv_wp := mirWpConverges_of_pureExec_init h_pure h_conv
  have h_term : MirWpConverges specBody (initMachineState specBody args) (fun _ => True) :=
    MirWpConverges.mono (fun _ _ => trivial) h_conv_wp
  have h_holds_wp := (mirBoolPredicateHolds_iff_wpConverges specBody args h_term).1 h_holds
  have h_conj := MirWpConverges.conj h_conv_wp h_holds_wp
  rcases MirWpConverges.exists_outcome h_conj with ⟨out, h_out_conv, h_out_holds⟩
  cases out with
  | normal ret =>
    rcases ret with ⟨v, mem⟩
    have h_post : v = .scalar { bits := if P then 1 else 0, sizeBytes := 1 } := h_out_conv.2
    have h_post' : v = .scalar { bits := 1, sizeBytes := 1 } := h_out_holds
    rw [h_post'] at h_post
    injection h_post with h_eq
    injection h_eq with h_eq
    by_cases hP : P
    · exact hP
    · rw [ite_eq_right_iff.mpr (fun h => (hP h).elim)] at h_eq
      contradiction
  | panic => exact False.elim h_out_conv
  | abort => exact False.elim h_out_conv

theorem mirBoolPredicateHoldsWithCallees_iff_wpConverges
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (h_term :
      MirWpConverges specBody (initMachineStateWithCallees specBody args callees) (fun _ => True)) :
    Anneal.MirFuelFree.MirBoolPredicateHoldsWithCallees specBody callees args ↔
      MirWpConverges specBody (initMachineStateWithCallees specBody args callees)
        (mirSafePost
          (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 })) := by
  constructor
  · intro h_holds
    rcases h_term with ⟨fuel, hf_term⟩
    exact ⟨fuel,
      (mirBoolPredicateHoldsWithCallees_iff_wpMirBoolWithCalleesSym
        fuel specBody callees args hf_term).1 h_holds⟩
  · exact mirBoolPredicateHoldsWithCallees_of_wpConverges specBody callees args

theorem mirBoolPredicateHoldsWithCallees_elim_of_pureExec
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value)
    {P : Prop} [Decidable P]
    (h_pure : checkPureMir specBody = true)
    (h_conv : PureMirConvergesWithCallees specBody callees (initPureState specBody args)
      (· = .scalar { bits := if P then 1 else 0, sizeBytes := 1 })) :
    Anneal.MirFuelFree.MirBoolPredicateHoldsWithCallees specBody callees args → P := by
  intro h_holds
  have h_pure' := checkPureMirWithCallees_of_checkPureMir callees 0 specBody.traitImpls h_pure
  have h_conv_wp := mirWpConverges_of_pureExecWithCallees_init h_pure' h_conv
  have h_term :
      MirWpConverges specBody (initMachineStateWithCallees specBody args callees) (fun _ => True) :=
    MirWpConverges.mono (fun _ _ => trivial) h_conv_wp
  have h_holds_wp :=
    (mirBoolPredicateHoldsWithCallees_iff_wpConverges specBody callees args h_term).1 h_holds
  have h_conj := MirWpConverges.conj h_conv_wp h_holds_wp
  rcases MirWpConverges.exists_outcome h_conj with ⟨out, h_out_conv, h_out_holds⟩
  cases out with
  | normal ret =>
    rcases ret with ⟨v, mem⟩
    have h_post : v = .scalar { bits := if P then 1 else 0, sizeBytes := 1 } := h_out_conv.2
    have h_post' : v = .scalar { bits := 1, sizeBytes := 1 } := h_out_holds
    rw [h_post'] at h_post
    injection h_post with h_eq
    injection h_eq with h_eq
    by_cases hP : P
    · exact hP
    · rw [ite_eq_right_iff.mpr (fun h => (hP h).elim)] at h_eq
      contradiction
  | panic => exact False.elim h_out_conv
  | abort => exact False.elim h_out_conv

def PureMirUniqueTruePath (specBody : CapturedMir) (args : List Value) {P : Prop} : Prop :=
  checkPureMir specBody = true ∧
  (P → PureMirConverges specBody (initPureState specBody args)
    (· = .scalar { bits := 1, sizeBytes := 1 })) ∧
  (¬ P → PureMirConverges specBody (initPureState specBody args)
    (· = .scalar { bits := 0, sizeBytes := 1 }))

theorem mirBoolPredicateHolds_elim_of_uniqueTruePath
    (specBody : CapturedMir) (args : List Value) {P : Prop} [Decidable P]
    (h_uniq : PureMirUniqueTruePath specBody args (P := P)) :
    MirBoolPredicateHolds specBody args → P := by
  intro h_holds
  by_cases hP : P
  · exact hP
  · have h_conv : PureMirConverges specBody (initPureState specBody args)
        (· = .scalar { bits := 0, sizeBytes := 1 }) :=
      h_uniq.2.2 hP
    have h_conv_wp := mirWpConverges_of_pureExec_init h_uniq.1 h_conv
    have h_term : MirWpConverges specBody (initMachineState specBody args) (fun _ => True) :=
      MirWpConverges.mono (fun _ _ => trivial) h_conv_wp
    have h_holds_wp := (mirBoolPredicateHolds_iff_wpConverges specBody args h_term).1 h_holds
    have h_conj := MirWpConverges.conj h_conv_wp h_holds_wp
    rcases MirWpConverges.exists_outcome h_conj with ⟨out, h_out_conv, h_out_holds⟩
    cases out with
    | normal ret =>
      rcases ret with ⟨v, mem⟩
      have h_post : v = .scalar { bits := 0, sizeBytes := 1 } := h_out_conv.2
      have h_post' : v = .scalar { bits := 1, sizeBytes := 1 } := h_out_holds
      rw [h_post'] at h_post
      injection h_post with h_eq
      injection h_eq with h_eq
      contradiction
    | panic => exact False.elim h_out_conv
    | abort => exact False.elim h_out_conv

theorem mirBoolPredicateHolds_intro_of_pureExec
    (specBody : CapturedMir) (args : List Value) {P : Prop}
    (h_pure : checkPureMir specBody = true)
    (h_conv : P → PureMirConverges specBody (initPureState specBody args)
      (· = .scalar { bits := 1, sizeBytes := 1 })) :
    P → MirBoolPredicateHolds specBody args := by
  intro hP
  exact mirBoolPredicateHolds_of_pureExec specBody args h_pure (h_conv hP)

def defaultSpecSteps (body : CapturedMir) : Nat :=
  Nat.add (Nat.mul (length body.basicBlocks) 16) 80

def defaultCfgSteps (body : CapturedMir) : Nat :=
  Nat.add (Nat.mul (length body.basicBlocks) 16) 40

structure Hold (P : Prop) : Prop where
  val : P

theorem get?_append_cons {α : Type u} (pfx rest : List α) (x : α) :
    get? (pfx ++ (x :: rest)) (length pfx) = some x := by
  simp [get?, length]

theorem get?_length_none {α : Type u} (xs : List α) :
    get? xs (length xs) = none := by
  simp [get?, length]

theorem length_append_singleton {α : Type u} (pfx : List α) (x : α) :
    length (pfx ++ [x]) = Nat.add (length pfx) 1 := by
  simp [length]

theorem scalarModulus_1 : scalarModulus 1 = 256 := rfl
theorem scalarModulus_2 : scalarModulus 2 = 65536 := rfl
theorem scalarModulus_4 : scalarModulus 4 = 4294967296 := rfl
theorem scalarModulus_8 : scalarModulus 8 = 18446744073709551616 := rfl
theorem mul_1_8 : Nat.mul 1 8 = 8 := rfl
theorem mul_2_8 : Nat.mul 2 8 = 16 := rfl
theorem mul_4_8 : Nat.mul 4 8 = 32 := rfl
theorem mul_8_8 : Nat.mul 8 8 = 64 := rfl
theorem mod_1_2 : 1 % 2 = 1 := rfl
theorem bitwiseAndBits_8_1_0 : bitwiseAndBits 8 1 0 = 0 := rfl
theorem bitwiseAndBits_one_one : bitwiseAndBits 8 1 1 = 1 := rfl
theorem bitwiseAndBits_one_zero : bitwiseAndBits 8 1 0 = 0 := rfl

theorem eq_zero_or_one_of_mod2_eq {x a : Nat} (h : x = a % 2) :
    x = 0 ∨ x = 1 := by omega

theorem beq_mod2_zero_of_odd {a : Nat} (h : a % 2 = 1) :
    Nat.beq (a % 2) 0 = false := by
  rw [h]; rfl

theorem beq_mod2_zero_of_not_odd {a : Nat} (h : ¬ a % 2 = 1) :
    Nat.beq (a % 2) 0 = true := by
  have h0 : a % 2 = 0 := by omega
  rw [h0]; rfl

theorem eq_one_of_zero_or_one_and_odd {a : Nat}
    (h1 : a = 0 ∨ a = 1) (h2 : a % 2 = 1) : a = 1 := by omega

theorem eq_zero_of_zero_or_one_and_not_odd {a : Nat}
    (h1 : a = 0 ∨ a = 1) (h2 : ¬ a % 2 = 1) : a = 0 := by omega

theorem isBorrowProtected_nil (entry : BorrowEntry) :
    isBorrowProtected .nil entry = false := by
  unfold isBorrowProtected
  cases entry.protector <;> rfl

theorem hasProtectedWriteConflict_nil
    (borrows : List BorrowEntry)
    (targetLocal : LocalIdx)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    {targetFrameDepth : Nat} :
    hasProtectedWriteConflict borrows .nil targetLocal writerTag writeProj
      writeRangeOff writeRangeLen targetFrameDepth = false := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    unfold hasProtectedWriteConflict
    simp only [isBorrowProtected_nil, Bool.false_and, Bool.and_false]
    exact ih

theorem readProjectedValue_nil (locals : List LocalSlot) (v : Value) :
    readProjectedValue locals v [] = .ok v := rfl

theorem readProjectedValue_field
    (locals : List LocalSlot) (vIdx : Nat) (fields : List Value)
    (idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    readProjectedValue locals (.aggregate vIdx fields) (.field idx ty :: rest) =
      match get? fields idx with
      | .some fieldVal => readProjectedValue locals fieldVal rest
      | .none => .ub := rfl

theorem readProjectedValue_index
    (locals : List LocalSlot) (fields : List Value)
    (idxLocal : LocalIdx) (rest : List ProjectionElem) :
    readProjectedValue locals (.aggregate 0 fields) (.index idxLocal :: rest) =
      match get? locals idxLocal with
      | .some (.init (.scalar sc)) =>
        match get? fields sc.bits with
        | .some elemVal => readProjectedValue locals elemVal rest
        | .none => .ub
      | _ => .ub := rfl

def evalOperandFallback (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) : PlaceReadResult :=
  evalOperand locals op borrows globals layouts callerLocals localDecls callStack

def evalDerefGlobalFallback
    (globals : List CapturedAllocation) (ptrVal : ProvenancePtr) (sz : Nat)
    (locals : List LocalSlot) (restProj : List ProjectionElem)
    (layouts : LayoutTable) : PlaceReadResult :=
  match lookupGlobalAlloc globals ptrVal.allocId with
  | .some alloc =>
    evalGlobalDerefRead locals alloc ptrVal.offsetBytes sz restProj layouts .none
  | .none => .ub

def evalThinPtrElemDerefReadFallback
    (locals callerLocals : List LocalSlot) (entry : BorrowEntry)
    (ptrVal : ProvenancePtr) (restProj : List ProjectionElem) : PlaceReadResult :=
  match get? locals entry.targetLocal with
  | .some (.init targetRootVal) =>
    match resolveStackThinPtrTargetProj? locals targetRootVal entry ptrVal restProj with
    | .none => .ub
    | .some fullProj =>
      match readProjectedValue locals targetRootVal fullProj with
      | .ok fieldVal => .ok fieldVal locals
      | .ub => .ub
      | .unsupported => .unsupported
  | .some _ => .ub
  | .none =>
    match get? callerLocals entry.targetLocal with
    | .some (.init targetRootVal) =>
      match resolveStackThinPtrTargetProj? locals targetRootVal entry ptrVal restProj with
      | .none => .ub
      | .some fullProj =>
        match readProjectedValue locals targetRootVal fullProj with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
    | _ => .ub

def evalOperandFast (body : CapturedMir) (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) : PlaceReadResult :=
  match op with
  | .constant c =>
    match c.val with
    | .indirect _ _ =>
      evalOperandFallback locals (.constant c) borrows globals body.layouts callerLocals localDecls
        callStack
    | .unevaluated _ => .unsupported
    | cv =>
      match evalConstValue cv c.ty globals body.layouts with
      | .some v => .ok v locals
      | .none => .unsupported
  | .copy p =>
    match p.projection with
    | .deref :: restProj =>
      match localDecls, callStack with
      | .nil, _ :: _ =>
        evalOperandFallback locals (.copy p) borrows globals body.layouts callerLocals .nil callStack
      | .nil, .nil =>
        match get? locals p.local_ with
        | .some (.init (.ptr ptrVal sz)) =>
          match lookupBorrow borrows ptrVal.tag with
          | .some entry =>
            match entry.perm with
            | .disabled => .ub
            | _ =>
              let needsElemRes :=
                match entry.targetProjection with
                | .nil => false
                | pHead :: pTail =>
                  let norm :=
                    normalizeSubsliceProjections (stripTransparentProjections (pHead :: pTail))
                  match endsWithSubslice norm with
                  | true => true
                  | false => Bool.not (Nat.beq ptrVal.offsetBytes 0)
              match needsElemRes with
              | false =>
                match get? locals entry.targetLocal with
                | .some (.init targetRootVal) =>
                  let fullProj :=
                    match entry.targetProjection with
                    | .nil => restProj
                    | ph :: pt => ph :: appendProjections pt restProj
                  match readProjectedValue locals targetRootVal fullProj with
                  | .ok fieldVal => .ok fieldVal locals
                  | .ub => .ub
                  | .unsupported => .unsupported
                | .some _ => .ub
                | .none =>
                  match get? callerLocals entry.targetLocal with
                  | .some (.init targetRootVal) =>
                    let fullProj :=
                      match entry.targetProjection with
                      | .nil => restProj
                      | ph :: pt => ph :: appendProjections pt restProj
                    match readProjectedValue locals targetRootVal fullProj with
                    | .ok fieldVal => .ok fieldVal locals
                    | .ub => .ub
                    | .unsupported => .unsupported
                  | _ => .ub
              | true =>
                evalThinPtrElemDerefReadFallback locals callerLocals entry ptrVal restProj
          | .none => evalDerefGlobalFallback globals ptrVal sz locals restProj body.layouts
        | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
          evalSliceFatPtrDerefRead locals ptrVal ptrSz lenSc restProj borrows globals
            body.layouts callerLocals .none
        | _ => .ub
      | d :: ds, _ =>
        evalOperandFallback locals (.copy p) borrows globals body.layouts callerLocals (d :: ds)
          callStack
    | _ =>
      match placeTouchesUnion localDecls body.layouts p with
      | true =>
        evalOperandFallback locals (.copy p) borrows globals body.layouts callerLocals localDecls
          callStack
      | false =>
        match get? locals p.local_ with
        | .some (.init rootVal) =>
          match readProjectedValue locals rootVal p.projection with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | .some .uninit => .ub
        | .some .dead => .ub
        | .none => .ub
  | .move p =>
    match p.projection with
    | .nil =>
      match get? locals p.local_ with
      | .some (.init v) =>
        match set? locals p.local_ .uninit with
        | .some locals' => .ok v locals'
        | .none => .ub
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
    | .field idx ty :: rest =>
      match placeTouchesUnion localDecls body.layouts p with
      | true =>
        evalOperandFallback locals (.move p) borrows globals body.layouts callerLocals localDecls
          callStack
      | false =>
        match get? locals p.local_ with
        | .some (.init rootVal) =>
          match readProjectedValue locals rootVal (.field idx ty :: rest) with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | .some .uninit => .ub
        | .some .dead => .ub
        | .none => .ub
    | _ =>
      evalOperandFallback locals (.move p) borrows globals body.layouts callerLocals localDecls
        callStack

theorem evalOperandFast_eq (body : CapturedMir) (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperandFast body locals op borrows globals callerLocals localDecls callStack =
      evalOperand locals op borrows globals body.layouts callerLocals localDecls callStack := by
  cases op with
  | constant c =>
    rcases c with ⟨ty, val⟩
    cases val <;> rfl
  | copy p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil =>
      cases localDecls <;> rfl
    | cons hd tl =>
      cases hd with
      | deref =>
        cases localDecls <;> cases callStack <;> rfl
      | field _ _ | downcast _ _ | index _ | constantIndex _ _ _ | subslice _ _ _
      | opaqueCast _ | unwrapUnsafeBinder _ =>
        dsimp only [evalOperandFast, evalOperand, evalOperandFallback]
        cases hGet : get? locals loc with
        | none =>
          cases placeTouchesUnion localDecls body.layouts ⟨loc, _⟩ <;> rfl
        | some s =>
          cases s with
          | uninit | dead =>
            cases placeTouchesUnion localDecls body.layouts ⟨loc, _⟩ <;> rfl
          | init rootVal =>
            cases hU : placeTouchesUnion localDecls body.layouts ⟨loc, _⟩
            · simp only [hGet, hU]; rfl
            · simp only [hGet, hU]
  | move p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil => rfl
    | cons hd tl =>
      cases hd with
      | field idx ty =>
        dsimp only [evalOperandFast, evalOperand, evalOperandFallback]
        cases hGet : get? locals loc with
        | none =>
          cases placeTouchesUnion localDecls body.layouts ⟨loc, _⟩ <;> rfl
        | some s =>
          cases s with
          | uninit | dead =>
            cases placeTouchesUnion localDecls body.layouts ⟨loc, _⟩ <;> rfl
          | init rootVal =>
            cases hU : placeTouchesUnion localDecls body.layouts ⟨loc, _⟩
            · simp only [hGet, hU]; rfl
            · simp only [hGet, hU]
      | deref | downcast _ _ | index _ | constantIndex _ _ _ | subslice _ _ _
      | opaqueCast _ | unwrapUnsafeBinder _ => rfl

def evalOperandsFast
    (body : CapturedMir) (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) : OperandsEvalResult :=
  match ops with
  | .nil => .ok .nil locals
  | op :: rest =>
    match evalOperandFast body locals op borrows globals callerLocals localDecls callStack with
    | .ok v locals₁ =>
      match evalOperandsFast body locals₁ rest borrows globals callerLocals localDecls callStack with
      | .ok vs locals₂ => .ok (v :: vs) locals₂
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported

theorem evalOperandsFast_eq
    (body : CapturedMir) (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperandsFast body locals ops borrows globals callerLocals localDecls callStack =
      evalOperands locals ops borrows globals body.layouts callerLocals localDecls callStack := by
  induction ops generalizing locals with
  | nil => rfl
  | cons op rest ih =>
    change
      (match evalOperandFast body locals op borrows globals callerLocals localDecls callStack with
       | .ok v locals₁ =>
         match evalOperandsFast body locals₁ rest borrows globals callerLocals localDecls callStack with
         | .ok vs locals₂ => OperandsEvalResult.ok (v :: vs) locals₂
         | .ub => OperandsEvalResult.ub
         | .unsupported => OperandsEvalResult.unsupported
       | .ub => OperandsEvalResult.ub
       | .unsupported => OperandsEvalResult.unsupported) =
      (match evalOperand locals op borrows globals body.layouts callerLocals localDecls callStack with
       | .ok v locals₁ =>
         match evalOperands locals₁ rest borrows globals body.layouts callerLocals localDecls
             callStack with
         | .ok vs locals₂ => OperandsEvalResult.ok (v :: vs) locals₂
         | .ub => OperandsEvalResult.ub
         | .unsupported => OperandsEvalResult.unsupported
       | .ub => OperandsEvalResult.ub
       | .unsupported => OperandsEvalResult.unsupported)
    rw [evalOperandFast_eq]
    cases evalOperand locals op borrows globals body.layouts callerLocals localDecls callStack with
    | ok v locals₁ =>
      dsimp only
      rw [ih locals₁]
    | ub => rfl
    | unsupported => rfl

private theorem bitwiseAndBits_8_1_local (a : Nat) :
    bitwiseAndBits 8 a 1 = a % 2 := by
  rw [Anneal.Scalars.bitwiseAndBits_eq_land, Nat.and_one_is_mod]
  omega

def bitwiseAndBitsFast (numBits a b : Nat) : Nat :=
  match Nat.beq numBits 8, Nat.beq b 1 with
  | true, true => a % 2
  | _, _ => bitwiseAndBits numBits a b

theorem bitwiseAndBitsFast_eq (numBits a b : Nat) :
    bitwiseAndBitsFast numBits a b = bitwiseAndBits numBits a b := by
  unfold bitwiseAndBitsFast
  cases h1 : Nat.beq numBits 8 with
  | false => rfl
  | true =>
    cases h2 : Nat.beq b 1 with
    | false => rfl
    | true =>
      rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
      exact (bitwiseAndBits_8_1_local a).symm

def evalByteCastAfterOperand
    (body : CapturedMir)
    (op : Operand)
    (targetTy : Ty)
    (v : Value)
    (locals' : List LocalSlot)
    (mem : Memory) :
    RvalueEvalResult :=
  let rTargetTy := resolveTyWithLocalDecls body.localDecls body.layouts targetTy
  match tyByteSize body.localDecls body.layouts rTargetTy with
  | .none => .unsupported
  | .some dstSize =>
    match operandTy body.localDecls body.layouts op with
    | .some srcTy =>
      let rSrcTy := resolveTyWithLocalDecls body.localDecls body.layouts srcTy
      match tyByteSize body.localDecls body.layouts rSrcTy with
      | .none => .unsupported
      | .some srcSize =>
        match Nat.beq srcSize dstSize with
        | false => .unsupported
        | true =>
          let encodedOpt : Option (List AbstractByte) :=
            encodeByteCastSourceBytes body.layouts rSrcTy v
          match encodedOpt with
          | .none => .ub
          | .some bs =>
            match Nat.beq (length bs) dstSize with
            | false => .ub
            | true =>
              match decodeTypedValueFromBytes defaultCodecFuel body.layouts rTargetTy bs with
              | .some v' => .ok v' locals' mem
              | .none => .ub
    | .none =>
      match encodeUntypedValueToBytes defaultCodecFuel v with
      | .none => .unsupported
      | .some bs =>
        match Nat.beq (length bs) dstSize with
        | false => .unsupported
        | true =>
          match decodeTypedValueFromBytes defaultCodecFuel body.layouts rTargetTy bs with
          | .some v' => .ok v' locals' mem
          | .none => .ub

def evalRvalueFallback (locals : List LocalSlot) (rv : Rvalue)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) : RvalueEvalResult :=
  evalRvalue locals rv mem localDecls layouts

def evalRvalueFast
    (body : CapturedMir) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    RvalueEvalResult :=
  match rv with
  | .use op =>
    match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
    | .ok v locals' =>
      match validateLoadedValue body.layouts body.localDecls op v with
      | false => .ub
      | true =>
        match op, mem.borrows with
        | .copy { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
          match derefReadTreeUB locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors with
          | true => .ub
          | false =>
            .ok v locals'
              { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors }
        | .move { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
          match derefReadTreeUB locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors with
          | true => .ub
          | false =>
            .ok v locals'
              { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors }
        | _, _ => .ok v locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast ck op targetTy =>
    match ck with
    | .intToInt =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok (.scalar sc) locals' =>
        match Nat.beq sc.sizeBytes 0 with
        | true => .unsupported
        | false =>
          match intCastTargetBytes targetTy.kind with
          | .some targetBytes =>
            let modulus := scalarModulus targetBytes
            let castedBits :=
              match operandIsSigned body.localDecls op body.layouts with
              | false => wrapScalarBits sc.bits modulus
              | true =>
                match Nat.ble targetBytes sc.sizeBytes with
                | true => wrapScalarBits sc.bits modulus
                | false => signExtendBits sc.bits sc.sizeBytes targetBytes
            .ok (.scalar ⟨castedBits, targetBytes⟩) locals' mem
          | .none => .unsupported
      | .ok _ _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | .transmute =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ub => .ub
      | .unsupported => .unsupported
      | .ok v locals' =>
        evalByteCastAfterOperand body op targetTy v locals' mem
    | _ => evalRvalueFallback locals (.cast ck op targetTy) mem body.localDecls body.layouts
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandFast body locals lhsOp mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
    | .ok lhsVal locals₁ =>
      match evalOperandFast body locals₁ rhsOp mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          match op with
          | .offset =>
            evalScalarPtrOffsetBinOp locals₂ mem body.localDecls body.layouts lhsOp lhs rhs
          | _ =>
            let isSigned := operandIsSigned body.localDecls lhsOp body.layouts
            evalScalarBinOp op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            evalPtrOffsetBinOp locals₂ mem body.localDecls body.layouts lhsOp ptrVal sz offsetSc
          | _ =>
            match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
            | true =>
              match
                ptrAddressScalar?
                  locals₂
                  mem.borrows
                  mem.callerLocals
                  body.localDecls
                  body.layouts
                  (layoutPointerBytes body.layouts)
                  ptrVal
                  sz
                  mem.callStack
              with
              | .some lhsAddrSc =>
                evalScalarBinOp op lhsAddrSc offsetSc locals₂ mem false
              | .none => .unsupported
            | false => .unsupported
        | .scalar lhsSc, .ptr ptrVal sz =>
          match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
          | true =>
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                (layoutPointerBytes body.layouts)
                ptrVal
                sz
                mem.callStack
            with
            | .some rhsAddrSc =>
              evalScalarBinOp op lhsSc rhsAddrSc locals₂ mem false
            | .none => .unsupported
          | false => .unsupported
        | .ptr lhsPtr lhsSz, .ptr rhsPtr rhsSz =>
          match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
          | true =>
            let ptrBytes := layoutPointerBytes body.layouts
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                ptrBytes
                lhsPtr
                lhsSz
                mem.callStack,
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                ptrBytes
                rhsPtr
                rhsSz
                mem.callStack
            with
            | .some lhsAddrSc, .some rhsAddrSc =>
              evalScalarBinOp op lhsAddrSc rhsAddrSc locals₂ mem false
            | _, _ => .unsupported
          | false => .unsupported
        | .aggregate lhsVar lhsFields, .aggregate rhsVar rhsFields =>
          evalWidePtrAggregateRelBinOp
            op
            lhsOp
            lhsVar
            lhsFields
            rhsVar
            rhsFields
            locals₂
            mem
            body.localDecls
            body.layouts
        | _, _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .unaryOp uop op =>
    match uop with
    | .not =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok (.scalar sc) locals' =>
        evalUnaryNot sc (operandTy body.localDecls body.layouts op) locals' mem
      | .ok _ _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | _ => evalRvalueFallback locals (.unaryOp uop op) mem body.localDecls body.layouts
  | _ => evalRvalueFallback locals rv mem body.localDecls body.layouts

theorem evalRvalueFast_eq
    (body : CapturedMir) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    evalRvalueFast body locals rv mem =
      evalRvalue locals rv mem body.localDecls body.layouts := by
  cases rv with
  | use op =>
    dsimp only [evalRvalueFast, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
  | cast ck op targetTy =>
    cases ck with
    | intToInt =>
      dsimp only [evalRvalueFast, evalRvalue]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | transmute =>
      dsimp only [evalRvalueFast, evalRvalue, evalByteCast]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
    | _ => rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueFast, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals lhsOp mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [evalOperandFast_eq]
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalueFast, evalRvalue]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | neg => rfl
    | ptrMetadata => rfl
  | _ => rfl

def evalRvalueSymTreeFast
    (body : CapturedMir) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    SymTree RvalueEvalResult :=
  match rv with
  | .use op =>
    match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
    | .ok v locals' =>
      .leaf (match validateLoadedValue body.layouts body.localDecls op v with
      | false => .ub
      | true =>
        match op, mem.borrows with
        | .copy { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
          match derefReadTreeUB locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors with
          | true => .ub
          | false =>
            .ok v locals'
              { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors }
        | .move { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
          match derefReadTreeUB locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors with
          | true => .ub
          | false =>
            .ok v locals'
              { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) mem.activeProtectors }
        | _, _ => .ok v locals' mem)
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
  | .ref bk p =>
    match bk, p.projection with
    | .shared, .nil =>
      match get? locals p.local_ with
      | .none => .leaf .ub
      | .some .dead => .leaf .ub
      | .some _ =>
        let tag := mem.nextTag
        let entry : BorrowEntry := {
          tag := tag
          targetLocal := p.local_
          targetProjection := .nil
          perm :=
            sharedBorrowPerm body.localDecls body.layouts
              { local_ := p.local_, projection := .nil }
          targetFrameDepth := length mem.callStack
        }
        let mem' := {
          mem with
          borrows := entry :: mem.borrows
          nextTag := Nat.add tag 1
        }
        .leaf (.ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem')
    | _, _ => .leaf (evalRvalueFallback locals (.ref bk p) mem body.localDecls body.layouts)
  | .cast .transmute op targetTy =>
    match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
    | .ok v locals' =>
      .leaf (evalByteCastAfterOperand body op targetTy v locals' mem)
  | .aggregate ak ops =>
    match ak with
    | .tuple =>
      match evalOperandsFast body locals ops mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok vals locals' => .leaf (.ok (.aggregate 0 vals) locals' mem)
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | _ => .leaf (evalRvalueFallback locals (.aggregate ak ops) mem body.localDecls body.layouts)
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandFast body locals lhsOp mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
    | .ok lhsVal locals₁ =>
      match evalOperandFast body locals₁ rhsOp mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          match op with
          | .offset =>
            .leaf (evalScalarPtrOffsetBinOp locals₂ mem body.localDecls body.layouts lhsOp lhs rhs)
          | .bitAnd =>
            .branch (Nat.beq lhs.sizeBytes 0) (.leaf .unsupported)
              (.branch (Nat.beq lhs.sizeBytes rhs.sizeBytes)
                (.leaf
                  (.ok
                    (.scalar
                      ⟨bitwiseAndBitsFast (Nat.mul lhs.sizeBytes 8) lhs.bits rhs.bits,
                       lhs.sizeBytes⟩)
                    locals₂ mem))
                (.leaf .unsupported))
          | .eq => evalScalarBinOpSymTree .eq lhs rhs locals₂ mem false
          | .ne => evalScalarBinOpSymTree .ne lhs rhs locals₂ mem false
          | _ =>
            let isSigned := operandIsSigned body.localDecls lhsOp body.layouts
            evalScalarBinOpSymTree op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            evalPtrOffsetBinOpSymTree locals₂ mem body.localDecls body.layouts
              lhsOp ptrVal sz offsetSc
          | _ =>
            match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
            | true =>
              match
                ptrAddressScalar?
                  locals₂
                  mem.borrows
                  mem.callerLocals
                  body.localDecls
                  body.layouts
                  (layoutPointerBytes body.layouts)
                  ptrVal
                  sz
                  mem.callStack
              with
              | .some lhsAddrSc =>
                evalScalarBinOpSymTree op lhsAddrSc offsetSc locals₂ mem false
              | .none => .leaf .unsupported
            | false => .leaf .unsupported
        | .scalar lhsSc, .ptr ptrVal sz =>
          match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
          | true =>
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                (layoutPointerBytes body.layouts)
                ptrVal
                sz
                mem.callStack
            with
            | .some rhsAddrSc =>
              evalScalarBinOpSymTree op lhsSc rhsAddrSc locals₂ mem false
            | .none => .leaf .unsupported
          | false => .leaf .unsupported
        | .ptr lhsPtr lhsSz, .ptr rhsPtr rhsSz =>
          match isPtrRelationalBinOp op body.localDecls body.layouts lhsOp rhsOp with
          | true =>
            let ptrBytes := layoutPointerBytes body.layouts
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                ptrBytes
                lhsPtr
                lhsSz
                mem.callStack,
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                body.localDecls
                body.layouts
                ptrBytes
                rhsPtr
                rhsSz
                mem.callStack
            with
            | .some lhsAddrSc, .some rhsAddrSc =>
              evalScalarBinOpSymTree op lhsAddrSc rhsAddrSc locals₂ mem false
            | _, _ => .leaf .unsupported
          | false => .leaf .unsupported
        | .aggregate lhsVar lhsFields, .aggregate rhsVar rhsFields =>
          .leaf
            (evalWidePtrAggregateRelBinOp
              op
              lhsOp
              lhsVar
              lhsFields
              rhsVar
              rhsFields
              locals₂
              mem
              body.localDecls
              body.layouts)
        | _, _ => .leaf .unsupported
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
  | .unaryOp uop op =>
    match uop with
    | .not =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals body.localDecls
        mem.callStack with
      | .ok (.scalar sc) locals' =>
        evalUnaryNotSymTree sc (operandTy body.localDecls body.layouts op) locals' mem
      | .ok _ _ => .leaf .unsupported
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | _ => .leaf (evalRvalueFallback locals (.unaryOp uop op) mem body.localDecls body.layouts)
  | _ => .leaf (evalRvalueFallback locals rv mem body.localDecls body.layouts)

theorem evalRvalueSymTreeFast_eq
    (body : CapturedMir) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    evalRvalueSymTreeFast body locals rv mem =
      evalRvalueSymTree locals rv mem body.localDecls body.layouts := by
  cases rv with
  | use op =>
    dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
  | ref bk p =>
    cases bk with
    | shared =>
      rcases p with ⟨loc, proj⟩
      cases proj with
      | nil =>
        dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
        cases get? locals loc with
        | none => rfl
        | some slot => cases slot <;> rfl
      | cons hd _ => cases hd <;> rfl
    | _ => rfl
  | cast ck op targetTy =>
    cases ck with
    | transmute =>
      dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalueFallback,
        evalRvalue, evalByteCast]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
    | _ => rfl
  | aggregate ak ops =>
    cases ak with
    | tuple =>
      dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
      rw [evalOperandsFast_eq]
      cases evalOperands locals ops mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack <;> rfl
    | _ => rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree]
    rw [evalOperandFast_eq]
    cases evalOperand locals lhsOp mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [evalOperandFast_eq]
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok v₂ locals₂ =>
        cases v with
        | scalar lhs =>
          cases v₂ with
          | scalar rhs =>
            cases op <;> simp only [evalScalarBinOpSymTree, bitwiseAndBitsFast_eq]
          | _ => rfl
        | _ => cases v₂ <;> rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls mem.callStack with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | neg => rfl
    | ptrMetadata => rfl
  | _ => rfl

def finishAssignStmtNodeFast
    (s : MachineState) (dst : Place) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvalueEvalResult → MirStepNode
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok val locals₁ mem₁ =>
    match dst.projection with
    | .nil =>
      match get? locals₁ dst.local_ with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? locals₁ dst.local_ (.init val) with
        | .some locals₂ =>
          match hasProtectedWriteConflict mem₁.borrows mem₁.activeProtectors
              dst.local_ .none .nil 0 0 (length mem₁.callStack) with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrows mem₁.borrows dst.local_ .none
                (length mem₁.callStack)
            MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | _ => finishAssignStmtNode s dst localDecls layouts (.ok val locals₁ mem₁)

theorem finishAssignStmtNodeFast_eq
    (s : MachineState) (dst : Place) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (res : RvalueEvalResult) :
    finishAssignStmtNodeFast s dst localDecls layouts res =
      finishAssignStmtNode s dst localDecls layouts res := by
  cases res with
  | ub => rfl
  | unsupported => rfl
  | ok val locals₁ mem₁ =>
    rcases dst with ⟨loc, proj⟩
    cases proj with
    | nil =>
      dsimp only [finishAssignStmtNodeFast, finishAssignStmtNode]
      cases get? locals₁ loc with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | uninit =>
          dsimp only
          cases set? locals₁ loc (.init val) with
          | none => rfl
          | some locals₂ =>
            cases mem₁.activeProtectors with
            | nil =>
              dsimp only
              rw [hasProtectedWriteConflict_nil]
            | cons _ _ => rfl
        | init _ =>
          dsimp only
          cases set? locals₁ loc (.init val) with
          | none => rfl
          | some locals₂ =>
            cases mem₁.activeProtectors with
            | nil =>
              dsimp only
              rw [hasProtectedWriteConflict_nil]
            | cons _ _ => rfl
    | cons _ _ => rfl

def evalStmtFallback (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  evalStmt s stmt localDecls layouts

def evalStmtFast
    (body : CapturedMir) (s : MachineState) (stmt : Statement) : MirStepNode :=
  match stmt.kind with
  | .assign dst rv =>
    finishAssignStmtNodeFast s dst body.localDecls body.layouts
      (evalRvalueFast body s.frame.locals rv s.memory)
  | .storageLive loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .uninit with
      | .some locals' =>
        match s.memory.activeProtectors with
        | .nil =>
          MirStepNode.step
            (advanceStmt s locals'
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
        | protHead :: protTail =>
          match
            hasProtectedLocalBorrow
              s.memory.borrows
              (protHead :: protTail)
              loc
              (length s.memory.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals'
                { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .storageDead loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .dead with
      | .some locals' =>
        match s.memory.activeProtectors with
        | .nil =>
          MirStepNode.step
            (advanceStmt s locals'
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
        | protHead :: protTail =>
          match
            hasProtectedLocalBorrow
              s.memory.borrows
              (protHead :: protTail)
              loc
              (length s.memory.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals'
                { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .nop => MirStepNode.step (advanceStmt s s.frame.locals)
  | _ => evalStmtFallback s stmt body.localDecls body.layouts

theorem evalStmtFast_eq
    (body : CapturedMir) (s : MachineState) (stmt : Statement) :
    evalStmtFast body s stmt =
      evalStmt s stmt body.localDecls body.layouts := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    show finishAssignStmtNodeFast s dst body.localDecls body.layouts
      (evalRvalueFast body s.frame.locals rv s.memory) = _
    rw [finishAssignStmtNodeFast_eq, evalRvalueFast_eq]
    dsimp only [finishAssignStmtNode, evalStmt]
    cases evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts <;> rfl
  | _ => rfl

def finishAssignSymTree (s : MachineState) (dst : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    SymTree RvalueEvalResult → SymTree MirStepNode
  | .leaf res => .leaf (finishAssignStmtNode s dst localDecls layouts res)
  | .branch c t1 t2 =>
    .branch c (finishAssignSymTree s dst localDecls layouts t1)
      (finishAssignSymTree s dst localDecls layouts t2)

theorem finishAssignSymTree_eq (s : MachineState) (dst : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (t : SymTree RvalueEvalResult) :
    finishAssignSymTree s dst localDecls layouts t =
      t.bind (fun res => .leaf (finishAssignStmtNode s dst localDecls layouts res)) := by
  induction t with
  | leaf _ => rfl
  | branch _ _ _ ih1 ih2 =>
    dsimp only [finishAssignSymTree, SymTree.bind]
    rw [ih1, ih2]

def evalStmtSymTreeFast
    (body : CapturedMir) (s : MachineState) (stmt : Statement) : SymTree MirStepNode :=
  match stmt.kind with
  | .assign dst rv =>
    finishAssignSymTree s dst body.localDecls body.layouts
      (evalRvalueSymTreeFast body s.frame.locals rv s.memory)
  | .storageLive loc =>
    .leaf
      (match get? s.frame.locals loc with
       | .some _ =>
         match set? s.frame.locals loc .uninit with
         | .some locals' =>
           match s.memory.activeProtectors with
           | .nil =>
             MirStepNode.step
               (advanceStmt s locals'
                 { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
           | protHead :: protTail =>
             match
               hasProtectedLocalBorrow
                 s.memory.borrows
                 (protHead :: protTail)
                 loc
                 (length s.memory.callStack)
             with
             | true => MirStepNode.fail .ub
             | false =>
               MirStepNode.step
                 (advanceStmt s locals'
                   { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
         | .none => MirStepNode.fail .ub
       | .none => MirStepNode.fail .ub)
  | .storageDead loc =>
    .leaf
      (match get? s.frame.locals loc with
       | .some _ =>
         match set? s.frame.locals loc .dead with
         | .some locals' =>
           match s.memory.activeProtectors with
           | .nil =>
             MirStepNode.step
               (advanceStmt s locals'
                 { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
           | protHead :: protTail =>
             match
               hasProtectedLocalBorrow
                 s.memory.borrows
                 (protHead :: protTail)
                 loc
                 (length s.memory.callStack)
             with
             | true => MirStepNode.fail .ub
             | false =>
               MirStepNode.step
                 (advanceStmt s locals'
                   { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
         | .none => MirStepNode.fail .ub
       | .none => MirStepNode.fail .ub)
  | .nop => .leaf (MirStepNode.step (advanceStmt s s.frame.locals))
  | _ => .leaf (evalStmtFallback s stmt body.localDecls body.layouts)

theorem evalStmtSymTreeFast_eq
    (body : CapturedMir) (s : MachineState) (stmt : Statement) :
    evalStmtSymTreeFast body s stmt =
      evalStmtSymTree s stmt body.localDecls body.layouts := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    show finishAssignSymTree s dst body.localDecls body.layouts
        (evalRvalueSymTreeFast body s.frame.locals rv s.memory) =
      (evalRvalueSymTree s.frame.locals rv s.memory body.localDecls body.layouts).bind _
    rw [finishAssignSymTree_eq, evalRvalueSymTreeFast_eq]
  | _ => rfl

def evalTerminatorFallback (s : MachineState) (term : Terminator)
    (currentBody : CapturedMir) : SymTree MirStepNode :=
  evalTerminatorSymTree s term currentBody

def evalTerminatorSymTreeFast
    (body : CapturedMir) (s : MachineState) (term : Terminator) : SymTree MirStepNode :=
  match term.kind with
  | .goto target =>
    .leaf (MirStepNode.step { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
  | .return_ =>
    match s.memory.callStack with
    | .nil =>
      match get? s.frame.locals 0 with
      | .some (.init retVal) =>
        .leaf
          (match
            hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              (length s.memory.callStack) (length s.frame.locals)
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.retNormal retVal
              { s.memory with
                borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack)
                  (length s.frame.locals) })
      | _ => .leaf (MirStepNode.fail .ub)
    | _ :: _ => evalTerminatorFallback s term body
  | .switchInt discr targets =>
    match evalOperandFast body s.frame.locals discr s.memory.borrows s.memory.globals
        s.memory.callerLocals (callStack := s.memory.callStack) with
    | .ok (.scalar sc) locals' =>
      (lookupSwitchTargetTree sc.bits targets.branches targets.otherwise).bind
        (fun target =>
          .leaf (.vis (.inr (.inl (.emit (.event sc.bits))))
            (fun _ =>
              .running { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })))
    | .ok _ _ => .leaf (MirStepNode.fail .ub)
    | .ub => .leaf (MirStepNode.fail .ub)
    | .unsupported => .leaf MirStepNode.unsupported
  | .assert cond expected target unwind =>
    match evalOperandFast body s.frame.locals cond s.memory.borrows s.memory.globals
        s.memory.callerLocals (callStack := s.memory.callStack) with
    | .ok (.scalar sc) locals' =>
      let expectedBit := match expected with | true => 1 | false => 0
      .branch (Nat.beq sc.bits expectedBit)
        (.leaf
          (MirStepNode.step { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }))
        (.leaf
          (match applyUnwindAction s locals' s.memory unwind with
          | .running nextState => MirStepNode.step nextState
          | .halted out => .ret out
          | .faulted fk => MirStepNode.fail fk))
    | _ => evalTerminatorFallback s term body
  | _ => evalTerminatorFallback s term body

theorem evalTerminatorSymTreeFast_eq
    (body : CapturedMir) (s : MachineState) (term : Terminator) :
    evalTerminatorSymTreeFast body s term =
      evalTerminatorSymTree s term body := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | return_ =>
    show evalTerminatorSymTreeFast body s { kind := .return_, span := span } =
      evalTerminatorSymTree s { kind := .return_, span := span } body
    unfold evalTerminatorSymTreeFast evalTerminatorFallback evalTerminatorSymTree evalTerminator
    dsimp only
    cases s.memory.callStack with
    | nil =>
      cases get? s.frame.locals 0 with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | uninit => rfl
        | init _ =>
          cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              0 (length s.frame.locals) <;> rfl
    | cons _ _ => rfl
  | switchInt discr targets =>
    show evalTerminatorSymTreeFast body s { kind := .switchInt discr targets, span := span } =
      evalTerminatorSymTree s { kind := .switchInt discr targets, span := span } body
    unfold evalTerminatorSymTreeFast evalTerminatorSymTree
    dsimp only
    rw [evalOperandFast_eq]
    rfl
  | assert cond expected target unwind =>
    unfold evalTerminatorSymTreeFast evalTerminatorFallback evalTerminatorSymTree
    dsimp only
    rw [evalOperandFast_eq]
    cases evalOperand s.frame.locals cond s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals (callStack := s.memory.callStack) with
    | ub => rfl
    | unsupported => rfl
    | ok v _ => cases v <;> rfl
  | _ => rfl

def stepMirSymTreeFast (body : CapturedMir) (s : MachineState) : SymTree MirStepNode :=
  match s.memory.activeCallee with
  | .some _ => stepMirSymTree body s
  | .none =>
    match body.phase with
    | .other _ => .leaf MirStepNode.unsupported
    | _ =>
      match get? body.basicBlocks s.frame.blockIdx with
      | none => .leaf (MirStepNode.fail .ub)
      | some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | some stmt =>
          evalStmtSymTreeFast body s stmt
        | none =>
          if s.frame.stmtIdx == length bb.statements then
            evalTerminatorSymTreeFast body s bb.terminator
          else
            .leaf (MirStepNode.fail .ub)

theorem stepMirSymTreeFast_eq (body : CapturedMir) (s : MachineState) :
    stepMirSymTreeFast body s = stepMirSymTree body s := by
  unfold stepMirSymTreeFast stepMirSymTree
  cases s.memory.activeCallee with
  | some _ => rfl
  | none =>
    dsimp only [Option.getD]
    cases body.phase with
    | other _ => rfl
    | _ =>
      all_goals
        dsimp only
        cases get? body.basicBlocks s.frame.blockIdx with
        | none => rfl
        | some bb =>
          dsimp only
          cases get? bb.statements s.frame.stmtIdx with
          | some stmt =>
            dsimp only
            rw [evalStmtSymTreeFast_eq]
          | none =>
            dsimp only
            split
            · exact evalTerminatorSymTreeFast_eq body s bb.terminator
            · rfl

def wpExecGen (zeroVal : Prop) (body : CapturedMir) (post : MirOutcome → Prop) :
    Nat → MirExecState → Prop
  | 0, _ => zeroVal
  | _ + 1, .halted out => post out
  | _ + 1, .faulted _ => False
  | fuel' + 1, .running s =>
    evalSymNodeTree (wpExecGen zeroVal body post fuel') post (stepMirSymTreeFast body s)

theorem wpMirExecSym_eq_gen
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) (post : MirOutcome → Prop) :
    wpMirExecSym fuel body st post = wpExecGen False body post fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    have h_fn : (fun st' => wpMirExecSym fuel' body st' post) = wpExecGen False body post fuel' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, wpExecGen]
      rw [h_fn, stepMirSymTreeFast_eq body s]
    | halted out =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, wpExecGen]
    | faulted fk =>
      cases fk <;>
        dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, MirStepNode.fail, wpExecGen]

theorem wpMirExecOrExhaustedSym_eq_gen
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) (post : MirOutcome → Prop) :
    wpMirExecOrExhaustedSym fuel body st post = wpExecGen True body post fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    have h_fn :
        (fun st' => wpMirExecOrExhaustedSym fuel' body st' post) =
          wpExecGen True body post fuel' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      dsimp only [wpMirExecOrExhaustedSym, stepMirExecSymTree, wpExecGen]
      rw [h_fn, stepMirSymTreeFast_eq body s]
    | halted out =>
      dsimp only [wpMirExecOrExhaustedSym, stepMirExecSymTree, evalSymNodeTree, wpExecGen]
    | faulted fk =>
      cases fk <;>
        dsimp only [wpMirExecOrExhaustedSym, stepMirExecSymTree, evalSymNodeTree,
          MirStepNode.fail, wpExecGen]

def wpExecFallback (zeroVal : Prop) (body : CapturedMir) (post : MirOutcome → Prop)
    (fuel : Nat) (st : MirExecState) : Prop :=
  wpExecGen zeroVal body post fuel st

def lookupBlock (body : CapturedMir) (idx : Nat) : Option BasicBlockData :=
  get? body.basicBlocks idx

def dispatchBlock
    (fallback : Prop)
    (s : MachineState)
    (body : CapturedMir)
    (post : MirOutcome → Prop)
    (kNone : MirExecState → Prop)
    (kSome : Nat → List Statement → Terminator → MirExecState → Prop) :
    Option BasicBlockData → Prop
  | .none => fallback
  | .some { statements := [], terminator := term, isCleanup := _ } =>
    evalSymNodeTree kNone post (evalTerminatorSymTreeFast body s term)
  | .some { statements := stmt :: rest, terminator := term, isCleanup := _ } =>
    evalSymNodeTree (kSome s.frame.blockIdx rest term) post (evalStmtSymTreeFast body s stmt)

def wpCfgStep
    (zeroVal : Prop) (body : CapturedMir) (post : MirOutcome → Prop) :
    Nat → Option (Nat × Nat × List Statement × Terminator) → MirExecState → Prop
  | 0, _, _ => zeroVal
  | _ + 1, _, .halted out => post out
  | _ + 1, _, .faulted _ => False
  | fuel' + 1, .none, .running s =>
      match s.memory.activeCallee with
      | .some _ => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.stmtIdx 0 with
        | false => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
        | true =>
          dispatchBlock
            False
            s body post
            (wpCfgStep zeroVal body post fuel' .none)
            (fun bIdx rest term => wpCfgStep zeroVal body post fuel' (.some (bIdx, 1, rest, term)))
            (lookupBlock body s.frame.blockIdx)
  | fuel' + 1, .some (blockIdx, stmtIdx, [], term), .running s =>
      match s.memory.activeCallee with
      | .some _ => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
          | true =>
            evalSymNodeTree
              (wpCfgStep zeroVal body post fuel' .none)
              post
              (evalTerminatorSymTreeFast body s term)
  | fuel' + 1, .some (blockIdx, stmtIdx, stmt :: rest, term), .running s =>
      match s.memory.activeCallee with
      | .some _ => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => wpExecFallback zeroVal body post (fuel' + 1) (.running s)
          | true =>
            evalSymNodeTree
              (wpCfgStep zeroVal body post fuel' (.some (blockIdx, Nat.add stmtIdx 1, rest, term)))
              post
              (evalStmtSymTreeFast body s stmt)

abbrev wpBlockLinear
    (zeroVal : Prop) (body : CapturedMir)
    (term : Terminator) (post : MirOutcome → Prop)
    (blockIdx stmtIdx fuel : Nat)
    (stmts : List Statement) (locals : List LocalSlot) (mem : Memory) : Prop :=
  wpCfgStep zeroVal body post fuel (.some (blockIdx, stmtIdx, stmts, term))
    (.running { frame := { blockIdx := blockIdx, stmtIdx := stmtIdx, locals := locals }, memory := mem })

theorem wpCfgStep_eq
    (zeroVal : Prop) (body : CapturedMir)
    (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) :
    ∀ (fuel : Nat) (cur : Option (Nat × Nat × List Statement × Terminator))
      (st : MirExecState),
      (∀ bIdx sIdx stmts term,
        cur = .some (bIdx, sIdx, stmts, term) →
        ∃ bb pfx,
          get? body.basicBlocks bIdx = some bb ∧
          sIdx = length pfx ∧
          bb.statements = pfx ++ stmts ∧
          term = bb.terminator) →
      wpExecGen zeroVal body post fuel st =
        wpCfgStep zeroVal body post fuel cur st := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel' ih =>
    intro cur st h_cur
    cases st with
    | halted _ =>
      cases cur with
      | none => rfl
      | some tup => rcases tup with ⟨_, _, stmts, _⟩; cases stmts <;> rfl
    | faulted _ =>
      cases cur with
      | none => rfl
      | some tup => rcases tup with ⟨_, _, stmts, _⟩; cases stmts <;> rfl
    | running s =>
      cases cur with
      | none =>
        dsimp only [wpCfgStep, wpExecFallback]
        cases h_ac : s.memory.activeCallee with
        | some _ => rfl
        | none =>
          dsimp only
          cases h_si : Nat.beq s.frame.stmtIdx 0 with
          | false => rfl
          | true =>
            dsimp only [lookupBlock]
            have h_si_eq : s.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_si
            dsimp only [wpExecGen, stepMirSymTreeFast]
            rw [h_ac]
            dsimp only
            rw [h_phase]
            dsimp only
            cases h_bb : get? body.basicBlocks s.frame.blockIdx with
            | none =>
              dsimp only [evalSymNodeTree, MirStepNode.fail, dispatchBlock]
            | some bb =>
              rcases bb with ⟨stmts, term, isCleanup⟩
              dsimp only
              rw [h_si_eq]
              cases stmts with
              | nil =>
                dsimp only [dispatchBlock, get?, length, BEq.beq, instBEqOfDecidableEq,
                  Nat.decEq, instDecidableEqNat, decide]
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                exact ih .none st' (fun _ _ _ _ h => nomatch h)
              | cons stmt rest =>
                dsimp only [dispatchBlock, get?]
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                refine ih (.some (s.frame.blockIdx, 1, rest, term)) st' ?_
                intro bIdx sIdx stmts' term' h_some
                injection h_some with h_tup
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup with ⟨rfl, h_tup2⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup2 with ⟨rfl, h_tup3⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup3 with ⟨rfl, rfl⟩
                exact ⟨⟨stmt :: rest, term, isCleanup⟩, [stmt], h_bb, rfl, rfl, rfl⟩
      | some tup =>
        rcases tup with ⟨blockIdx, stmtIdx, stmts, term⟩
        rcases h_cur blockIdx stmtIdx stmts term rfl with ⟨bb, pfx, h_bb, rfl, h_stmts, rfl⟩
        cases stmts with
        | nil =>
          dsimp only [wpCfgStep, wpExecFallback]
          cases h_ac : s.memory.activeCallee with
          | some _ => rfl
          | none =>
            dsimp only
            cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
            | false => rfl
            | true =>
              dsimp only
              cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
              | false => rfl
              | true =>
                dsimp only
                have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
                have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
                have h_eq : bb.statements = pfx := by simpa using h_stmts
                subst h_eq
                dsimp only [wpExecGen, stepMirSymTreeFast]
                rw [h_ac]
                dsimp only
                rw [h_phase]
                dsimp only
                rw [h_bi_eq, h_bb]
                dsimp only
                rw [h_si_eq, get?_length_none]
                dsimp only
                have h_beq : (length bb.statements == length bb.statements) = true :=
                  beq_self_eq_true _
                rw [h_beq]
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                exact ih .none st' (fun _ _ _ _ h => nomatch h)
        | cons stmt rest =>
          dsimp only [wpCfgStep, wpExecFallback]
          cases h_ac : s.memory.activeCallee with
          | some _ => rfl
          | none =>
            dsimp only
            cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
            | false => rfl
            | true =>
              dsimp only
              cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
              | false => rfl
              | true =>
                dsimp only
                have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
                have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
                dsimp only [wpExecGen, stepMirSymTreeFast]
                rw [h_ac]
                dsimp only
                rw [h_phase]
                dsimp only
                rw [h_bi_eq, h_bb]
                dsimp only
                rw [h_si_eq, h_stmts, get?_append_cons]
                dsimp only
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                refine ih (.some (blockIdx, Nat.add (length pfx) 1, rest, bb.terminator)) st' ?_
                intro bIdx sIdx stmts' term' h_some
                injection h_some with h_tup
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup with ⟨rfl, h_tup2⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup2 with ⟨rfl, h_tup3⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup3 with ⟨rfl, rfl⟩
                refine ⟨bb, pfx ++ [stmt], h_bb, ?_, by simp [h_stmts, List.append_assoc], rfl⟩
                exact (length_append_singleton pfx stmt).symm

theorem wpExecGen_eq_wpCfgStep
    (zeroVal : Prop) (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat) (st : MirExecState) :
    wpExecGen zeroVal body post fuel st =
      wpCfgStep zeroVal body post fuel .none st :=
  wpCfgStep_eq zeroVal body post h_phase fuel .none st (fun _ _ _ _ h => nomatch h)

theorem wpStartBlock0_eq
    (zeroVal : Prop) (body : CapturedMir) (bb : BasicBlockData)
    (post : MirOutcome → Prop) (fuel : Nat) (args : List Value)
    (h_phase : body.phase = .runtimeOptimized)
    (h_bb : get? body.basicBlocks 0 = some bb) :
    wpExecGen zeroVal body post fuel (.running (initMachineState body args)) =
      wpBlockLinear zeroVal body bb.terminator post
        0 0 fuel bb.statements (initLocalsAux 0 body.localDecls args)
        (initMachineState body args).memory := by
  refine wpCfgStep_eq zeroVal body post h_phase fuel
    (.some (0, 0, bb.statements, bb.terminator))
    (.running (initMachineState body args)) ?_
  intro bIdx sIdx stmts term h_some
  injection h_some with h_tup
  rcases Prod.mk.injEq _ _ _ _ ▸ h_tup with ⟨rfl, h_tup2⟩
  rcases Prod.mk.injEq _ _ _ _ ▸ h_tup2 with ⟨rfl, h_tup3⟩
  rcases Prod.mk.injEq _ _ _ _ ▸ h_tup3 with ⟨rfl, rfl⟩
  exact ⟨bb, [], h_bb, rfl, rfl, rfl⟩

def boolTruePost : MirOutcome → Prop :=
  fun out =>
    ∀ retVal mem',
      out = .normal (retVal, mem') →
      retVal = .scalar { bits := 1, sizeBytes := 1 }

theorem boolTruePost_normal_one (mem' : Memory) :
    boolTruePost (.normal (.scalar { bits := 1, sizeBytes := 1 }, mem')) := by
  intro retVal _ h
  injection h with hp
  injection hp with hv _
  exact hv.symm

theorem mirBoolPredicateHolds_of_wpMirSym_true
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h : wpMirSym fuel specBody (initMachineState specBody args) boolTruePost) :
    MirBoolPredicateHolds specBody args :=
  (mirBoolPredicateHolds_iff_dwlp specBody args).2 (dwlp_of_wpMirSym h)

def dummyBB : BasicBlockData :=
  { statements := [], terminator := { kind := .unreachable, span := "" }, isCleanup := false }

def entryBB (body : CapturedMir) : BasicBlockData :=
  (get? body.basicBlocks 0).getD dummyBB

theorem hold_mirBool_of_blockLinear
    (body : CapturedMir) (args : List Value)
    (h_phase : body.phase = .runtimeOptimized)
    (h_bb0 : get? body.basicBlocks 0 = some (entryBB body))
    (h : Hold
      (wpBlockLinear False body (entryBB body).terminator
        boolTruePost 0 0 (defaultSpecSteps body) (entryBB body).statements
        (initLocalsAux 0 body.localDecls args)
        (initMachineState body args).memory)) :
    Hold (MirBoolPredicateHolds body args) := by
  refine ⟨mirBoolPredicateHolds_of_wpMirSym_true (defaultSpecSteps body) body args ?_⟩
  unfold wpMirSym
  rw [wpMirExecSym_eq_gen,
      wpStartBlock0_eq False body (entryBB body) _ (defaultSpecSteps body) args h_phase h_bb0]
  exact h.val

theorem holdBoolReq_of_mirBool
    (body : CapturedMir) (args : List Value)
    (h_phase : body.phase = .runtimeOptimized)
    (h_bb0 : get? body.basicBlocks 0 = some (entryBB body))
    (h : MirBoolPredicateHolds body args) :
    Hold
      (wpBlockLinear True body (entryBB body).terminator
        (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
        0 0 (defaultSpecSteps body) (entryBB body).statements
        (initLocalsAux 0 body.localDecls args)
        (initMachineState body args).memory) := by
  refine ⟨?_⟩
  rw [← wpStartBlock0_eq True body (entryBB body) _ (defaultSpecSteps body) args h_phase h_bb0,
      ← wpMirExecOrExhaustedSym_eq_gen]
  exact holdBoolMirSym_of_mirBoolPredicateHolds (defaultSpecSteps body) body args h

theorem hold_wpMirSym_of_blockLinear
    (body : CapturedMir) (args : List Value) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (h_bb0 : get? body.basicBlocks 0 = some (entryBB body))
    (h : Hold
      (wpBlockLinear False body (entryBB body).terminator
        post 0 0 (defaultSpecSteps body) (entryBB body).statements
        (initLocalsAux 0 body.localDecls args)
        (initMachineState body args).memory)) :
    Hold (wpMirSym (defaultSpecSteps body) body (initMachineState body args) post) := by
  refine ⟨?_⟩
  unfold wpMirSym
  rw [wpMirExecSym_eq_gen,
      wpStartBlock0_eq False body (entryBB body) _ (defaultSpecSteps body) args h_phase h_bb0]
  exact h.val

theorem verifyMirNoPanic_of_blockLinear
    (c : Claim)
    (h_phase : c.body.phase = .runtimeOptimized)
    (h_bb0 : get? c.body.basicBlocks 0 = some (entryBB c.body))
    (h_callees : c.callees = [])
    (h_wp : ∀ args, c.pre args →
      Hold
        (wpBlockLinear False c.body (entryBB c.body).terminator
          (mirNormalPost (fun retVal _ => c.post args retVal))
          0 0 (defaultSpecSteps c.body) (entryBB c.body).statements
          (initLocalsAux 0 c.body.localDecls args)
          (initMachineState c.body args).memory)) :
    VerificationResult c := by
  refine verifyMirNoPanicSym c (defaultSpecSteps c.body) ?_
  intro args h_pre
  rw [h_callees]
  exact (hold_wpMirSym_of_blockLinear c.body args _ h_phase h_bb0 (h_wp args h_pre)).val

theorem verifyMirNoPanic_of_cfg
    (c : Claim)
    (h_phase : c.body.phase = .runtimeOptimized)
    (h_callees : c.callees = [])
    (h_wp : ∀ args, c.pre args →
      Hold
        (wpCfgStep False c.body (mirNormalPost (fun retVal _ => c.post args retVal))
          (defaultSpecSteps c.body) .none (.running (initMachineState c.body args)))) :
    VerificationResult c := by
  refine verifyMirNoPanicSym c (defaultSpecSteps c.body) ?_
  intro args h_pre
  rw [h_callees]
  unfold wpMirSym
  rw [wpMirExecSym_eq_gen, wpExecGen_eq_wpCfgStep False c.body _ h_phase]
  exact (h_wp args h_pre).val

theorem verifyStatefulMirNoPanic_of_cfg
    (c : StatefulClaim)
    (h_phase : c.body.phase = .runtimeOptimized)
    (h_callees : c.callees = [])
    (h_wp : ∀ args mem, c.pre args mem →
      Hold
        (wpCfgStep False c.body (mirNormalPost (c.post args mem))
          (defaultSpecSteps c.body) .none
          (.running (initMachineStateWithMemory c.body args mem)))) :
    StatefulVerificationResult c := by
  refine verifyStatefulMirNoPanicSym c (defaultSpecSteps c.body) ?_
  intro args mem h_pre
  rw [h_callees]
  unfold wpMirSym
  rw [wpMirExecSym_eq_gen, wpExecGen_eq_wpCfgStep False c.body _ h_phase]
  exact (h_wp args mem h_pre).val

inductive CfgExecState where
  | running
      (ok : Bool)
      (cur : Option (Nat × Nat × List Statement × Terminator))
      (s : MachineState)
  | halted (ok : Bool) (out : MirOutcome)
  | faulted

def cfgOk : CfgExecState → Bool
  | .running ok _ _ => ok
  | .halted ok _ => ok
  | .faulted => false

def cfgStateWP (post : MirOutcome → Prop) : CfgExecState → Prop
  | .halted ok out => ok = true ∧ post out
  | _ => False

def stepNodeToCfg
    (ok : Bool)
    (nextCur : Option (Nat × Nat × List Statement × Terminator)) :
    MirStepNode → CfgExecState
  | .ret out => .halted ok out
  | .tau (.running s') => .running ok nextCur s'
  | .tau (.halted out) => .halted ok out
  | .tau (.faulted _) => .faulted
  | .vis (.inr (.inl _)) k =>
    match k PUnit.unit with
    | .running s' => .running ok nextCur s'
    | .halted out => .halted ok out
    | .faulted _ => .faulted
  | .vis _ _ => .faulted

def evalTerminatorCfg
    (body : CapturedMir) (ok : Bool) (s : MachineState)
    (term : Terminator) : CfgExecState :=
  match term.kind with
  | .goto target =>
    .running ok .none { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } }
  | .return_ =>
    match s.memory.callStack with
    | .nil =>
      match get? s.frame.locals 0 with
      | .some (.init retVal) =>
        match
          hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
            (length s.memory.callStack) (length s.frame.locals)
        with
        | true => .faulted
        | false =>
          .halted ok
            (.normal (retVal,
              { s.memory with
                borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack)
                  (length s.frame.locals) }))
      | _ => .faulted
    | _ :: _ => .faulted
  | .switchInt discr targets =>
    match evalOperandFast body s.frame.locals discr s.memory.borrows s.memory.globals
        s.memory.callerLocals (callStack := s.memory.callStack) with
    | .ok (.scalar sc) locals' =>
      let target := lookupSwitchTarget sc.bits targets.branches targets.otherwise
      .running ok .none { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }
    | _ => .faulted
  | .assert cond expected target _ =>
    match evalOperandFast body s.frame.locals cond s.memory.borrows s.memory.globals
        s.memory.callerLocals (callStack := s.memory.callStack) with
    | .ok (.scalar sc) locals' =>
      let expectedBit := match expected with | true => 1 | false => 0
      .running (Bool.and ok (Nat.beq sc.bits expectedBit)) .none
        { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }
    | _ => .faulted
  | _ => .faulted

def dispatchBlockCfg
    (ok : Bool) (s : MachineState) (body : CapturedMir) :
    Option BasicBlockData → CfgExecState
  | .none => .faulted
  | .some { statements := [], terminator := term, isCleanup := _ } =>
    evalTerminatorCfg body ok s term
  | .some { statements := stmt :: rest, terminator := term, isCleanup := _ } =>
    stepNodeToCfg ok (.some (s.frame.blockIdx, 1, rest, term)) (evalStmtFast body s stmt)

def stepCfgState (body : CapturedMir) : CfgExecState → CfgExecState
  | .halted ok out => .halted ok out
  | .faulted => .faulted
  | .running ok cur s =>
    match s.memory.activeCallee with
    | .some _ => .faulted
    | .none =>
      match cur with
      | .none =>
        match Nat.beq s.frame.stmtIdx 0 with
        | false => .faulted
        | true => dispatchBlockCfg ok s body (lookupBlock body s.frame.blockIdx)
      | .some (blockIdx, stmtIdx, [], term) =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => .faulted
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => .faulted
          | true => evalTerminatorCfg body ok s term
      | .some (blockIdx, stmtIdx, stmt :: rest, term) =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => .faulted
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => .faulted
          | true =>
            stepNodeToCfg ok
              (.some (blockIdx, Nat.add stmtIdx 1, rest, term))
              (evalStmtFast body s stmt)

def runCfgSteps (body : CapturedMir) (cfg : CfgExecState) : Nat → CfgExecState
  | 0 => cfg
  | fuel' + 1 => stepCfgState body (runCfgSteps body cfg fuel')

theorem runCfgSteps_step (body : CapturedMir) (cfg : CfgExecState) (fuel : Nat) :
    runCfgSteps body cfg (fuel + 1) = runCfgSteps body (stepCfgState body cfg) fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel' ih =>
    change stepCfgState body (runCfgSteps body cfg (fuel' + 1)) =
      stepCfgState body (runCfgSteps body (stepCfgState body cfg) fuel')
    rw [ih]

theorem runCfgSteps_halted (body : CapturedMir) (ok : Bool) (out : MirOutcome) (fuel : Nat) :
    runCfgSteps body (.halted ok out) fuel = .halted ok out := by
  induction fuel with
  | zero => rfl
  | succ fuel' ih =>
    dsimp only [runCfgSteps]
    rw [ih]
    rfl

def CurValid (body : CapturedMir) :
    Option (Nat × Nat × List Statement × Terminator) → Prop
  | .none => True
  | .some (bIdx, sIdx, stmts, term) =>
    ∃ bb pfx,
      get? body.basicBlocks bIdx = some bb ∧
      sIdx = length pfx ∧
      bb.statements = pfx ++ stmts ∧
      term = bb.terminator

def CfgValid (body : CapturedMir) : CfgExecState → MirExecState → Prop
  | .running _ cur s, st => st = .running s ∧ CurValid body cur
  | .halted _ out, st => st = .halted out
  | .faulted, _ => True

theorem cfgOk_stepNodeToCfg_false
    (nextCur : Option (Nat × Nat × List Statement × Terminator))
    (node : MirStepNode) :
    cfgOk (stepNodeToCfg false nextCur node) = false := by
  cases node with
  | ret _ => rfl
  | tau st' => cases st' <;> rfl
  | vis i k =>
    rcases i with f | (e | c)
    · rfl
    · dsimp only [stepNodeToCfg, cfgOk]
      cases k PUnit.unit <;> rfl
    · rfl

theorem cfgOk_evalTerminatorCfg_false
    (body : CapturedMir) (s : MachineState) (term : Terminator) :
    cfgOk (evalTerminatorCfg body false s term) = false := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto _ => rfl
  | return_ =>
    dsimp only [evalTerminatorCfg]
    cases s.memory.callStack with
    | cons _ _ => rfl
    | nil =>
      cases get? s.frame.locals 0 with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | uninit => rfl
        | init _ =>
          cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              (length ([] : List SavedCallerFrame)) (length s.frame.locals) <;> rfl
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg]
    cases evalOperandFast body s.frame.locals discr s.memory.borrows s.memory.globals
        s.memory.callerLocals (callStack := s.memory.callStack) with
    | ok v _ => cases v <;> rfl
    | _ => rfl
  | assert cond expected target unwind =>
    dsimp only [evalTerminatorCfg]
    cases evalOperandFast body s.frame.locals cond s.memory.borrows s.memory.globals
        s.memory.callerLocals (callStack := s.memory.callStack) with
    | ok v _ => cases v <;> rfl
    | _ => rfl
  | _ => rfl

theorem cfgOk_dispatchBlockCfg_false
    (s : MachineState) (body : CapturedMir) (bbOpt : Option BasicBlockData) :
    cfgOk (dispatchBlockCfg false s body bbOpt) = false := by
  cases bbOpt with
  | none => rfl
  | some bb =>
    rcases bb with ⟨stmts, term, isCleanup⟩
    cases stmts with
    | nil => exact cfgOk_evalTerminatorCfg_false body s term
    | cons stmt rest => exact cfgOk_stepNodeToCfg_false _ _

theorem cfgOk_stepCfgState_false
    (body : CapturedMir) (cfg : CfgExecState) (h : cfgOk cfg = false) :
    cfgOk (stepCfgState body cfg) = false := by
  cases cfg with
  | faulted => rfl
  | halted ok out => exact h
  | running ok cur s =>
    change ok = false at h
    subst h
    cases h_ac : s.memory.activeCallee with
    | some _ =>
      dsimp only [stepCfgState]
      rw [h_ac]
      rfl
    | none =>
      cases cur with
      | none =>
        dsimp only [stepCfgState]
        rw [h_ac]
        dsimp only
        cases Nat.beq s.frame.stmtIdx 0 with
        | false => rfl
        | true => exact cfgOk_dispatchBlockCfg_false s body _
      | some tup =>
        rcases tup with ⟨bIdx, sIdx, stmts, term⟩
        cases stmts with
        | nil =>
          dsimp only [stepCfgState]
          rw [h_ac]
          dsimp only
          cases Nat.beq s.frame.blockIdx bIdx with
          | false => rfl
          | true =>
            cases Nat.beq s.frame.stmtIdx sIdx with
            | false => rfl
            | true => exact cfgOk_evalTerminatorCfg_false body s term
        | cons stmt rest =>
          dsimp only [stepCfgState]
          rw [h_ac]
          dsimp only
          cases Nat.beq s.frame.blockIdx bIdx with
          | false => rfl
          | true =>
            cases Nat.beq s.frame.stmtIdx sIdx with
            | false => rfl
            | true => exact cfgOk_stepNodeToCfg_false _ _

theorem cfgOk_of_runCfgSteps_true
    (body : CapturedMir) (fuel : Nat) (cfg : CfgExecState)
    (h : cfgOk (runCfgSteps body cfg fuel) = true) :
    cfgOk cfg = true := by
  cases h_ok : cfgOk cfg with
  | true => rfl
  | false =>
    have h_false : ∀ n, cfgOk (runCfgSteps body cfg n) = false := by
      intro n
      induction n with
      | zero => exact h_ok
      | succ fuel' ih =>
        dsimp only [runCfgSteps]
        exact cfgOk_stepCfgState_false body (runCfgSteps body cfg fuel') ih
    have h_f := h_false fuel
    rw [h] at h_f
    nomatch h_f

def stepNodeWP (body : CapturedMir) (post : MirOutcome → Prop) (fuel : Nat)
    (node : MirStepNode) : Prop :=
  match node with
  | .ret out => post out
  | .tau st' =>
    wpCoalBounded fuel mirNoCallWP (stepMirState body) (fun out _ => post out) st' PUnit.unit
  | .vis i k =>
    mirNoCallWP.wp i
      (fun o s' =>
        wpCoalBounded fuel mirNoCallWP (stepMirState body) (fun out _ => post out) (k o) s')
      PUnit.unit

theorem wpCoalBounded_succ_eq
    (body : CapturedMir) (post : MirOutcome → Prop) (fuel : Nat) (st : MirExecState) :
    wpCoalBounded (fuel + 1) mirNoCallWP (stepMirState body)
      (fun out _ => post out) st PUnit.unit =
    stepNodeWP body post fuel (stepMirState body st) := by
  unfold wpCoalBounded stepNodeWP
  cases stepMirState body st <;> rfl

theorem wpCoalBounded_stepNodeToCfg
    (body : CapturedMir) (post : MirOutcome → Prop) (fuel' : Nat)
    (nextCur : Option (Nat × Nat × List Statement × Terminator))
    (node : MirStepNode)
    (h_cur : CurValid body nextCur)
    (h_ok : cfgOk (stepNodeToCfg true nextCur node) = true)
    (ih : ∀ cfg' st', CfgValid body cfg' st' →
      cfgStateWP post (runCfgSteps body cfg' fuel') →
      wpCoalBounded (fuel' + 1) mirNoCallWP (stepMirState body)
        (fun out _ => post out) st' PUnit.unit)
    (h_wp : cfgStateWP post (runCfgSteps body (stepNodeToCfg true nextCur node) fuel')) :
    stepNodeWP body post (fuel' + 1) node := by
  cases node with
  | ret out =>
    dsimp only [stepNodeToCfg] at h_wp
    rw [runCfgSteps_halted] at h_wp
    exact h_wp.2
  | tau st' =>
    cases st' with
    | running s' =>
      exact ih (.running true nextCur s') (.running s') ⟨rfl, h_cur⟩ h_wp
    | halted out =>
      exact ih (.halted true out) (.halted out) rfl h_wp
    | faulted _ => nomatch h_ok
  | vis i k =>
    rcases i with f | (e | c)
    · nomatch h_ok
    · cases e
      dsimp only [stepNodeToCfg] at h_ok h_wp
      cases h_k : k PUnit.unit with
      | running s' =>
        rw [h_k] at h_wp
        have h_res := ih (.running true nextCur s') (.running s') ⟨rfl, h_cur⟩ h_wp
        rw [← h_k] at h_res
        exact h_res
      | halted out =>
        rw [h_k] at h_wp
        have h_res := ih (.halted true out) (.halted out) rfl h_wp
        rw [← h_k] at h_res
        exact h_res
      | faulted _ =>
        rw [h_k] at h_ok
        nomatch h_ok
    · nomatch h_ok

theorem wpCoalBounded_evalTerminatorCfg
    (body : CapturedMir) (post : MirOutcome → Prop) (fuel' : Nat)
    (s : MachineState) (term : Terminator)
    (h_ok : cfgOk (evalTerminatorCfg body true s term) = true)
    (ih : ∀ cfg' st', CfgValid body cfg' st' →
      cfgStateWP post (runCfgSteps body cfg' fuel') →
      wpCoalBounded (fuel' + 1) mirNoCallWP (stepMirState body)
        (fun out _ => post out) st' PUnit.unit)
    (h_wp : cfgStateWP post (runCfgSteps body (evalTerminatorCfg body true s term) fuel')) :
    stepNodeWP body post (fuel' + 1) (evalTerminator s term (some body)) := by
  rcases term with ⟨kind, span⟩
  revert h_ok h_wp
  cases kind with
  | goto target =>
    intro _ h_wp
    exact ih (.running true .none { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
      (.running { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
      ⟨rfl, trivial⟩ h_wp
  | return_ =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    cases s.memory.callStack with
    | cons _ _ => rintro ⟨⟩ _
    | nil =>
      dsimp only
      cases get? s.frame.locals 0 with
      | none => rintro ⟨⟩ _
      | some slot =>
        cases slot with
        | dead => rintro ⟨⟩ _
        | uninit => rintro ⟨⟩ _
        | init retVal =>
          cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              (length ([] : List SavedCallerFrame)) (length s.frame.locals) with
          | true => rintro ⟨⟩ _
          | false =>
            intro _ h_wp
            dsimp only [stepNodeWP, MirStepNode.retNormal] at h_wp ⊢
            rw [runCfgSteps_halted] at h_wp
            exact h_wp.2
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    rw [evalOperandFast_eq]
    cases evalOperand s.frame.locals discr s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals (callStack := s.memory.callStack) with
    | ub => rintro ⟨⟩ _
    | unsupported => rintro ⟨⟩ _
    | ok v locals' =>
      cases v with
      | scalar sc =>
        dsimp only [stepNodeWP, MirStepNode.step]
        intro _ h_wp
        exact ih
          (.running true .none
            { s with
              frame :=
                { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise
                  stmtIdx := 0
                  locals := locals' } })
          (.running
            { s with
              frame :=
                { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise
                  stmtIdx := 0
                  locals := locals' } })
          ⟨rfl, trivial⟩ h_wp
      | _ => rintro ⟨⟩ _
  | assert cond expected target unwind =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    rw [evalOperandFast_eq]
    cases evalOperand s.frame.locals cond s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals (callStack := s.memory.callStack) with
    | ub => rintro ⟨⟩ _
    | unsupported => rintro ⟨⟩ _
    | ok v locals' =>
      cases v with
      | scalar sc =>
        cases expected <;>
        · dsimp only [cfgOk, Bool.and]
          intro h_ok h_wp
          rw [h_ok] at h_wp ⊢
          dsimp only [stepNodeWP, MirStepNode.step] at h_wp ⊢
          exact ih
            (.running true .none { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })
            (.running { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })
            ⟨rfl, trivial⟩ h_wp
      | _ => rintro ⟨⟩ _
  | _ => rintro ⟨⟩ _

theorem wpCoalBounded_of_runCfgSteps
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) :
    ∀ (fuel : Nat) (cfg : CfgExecState) (st : MirExecState),
      CfgValid body cfg st →
      cfgStateWP post (runCfgSteps body cfg fuel) →
      wpCoalBounded (fuel + 1) mirNoCallWP (stepMirState body)
        (fun out _ => post out) st PUnit.unit := by
  intro fuel
  induction fuel with
  | zero =>
    intro cfg st h_valid h_wp
    dsimp only [runCfgSteps] at h_wp
    cases cfg with
    | running _ _ _ => exact False.elim h_wp
    | faulted => exact False.elim h_wp
    | halted ok out =>
      change st = .halted out at h_valid
      subst h_valid
      exact h_wp.2
  | succ fuel' ih =>
    intro cfg st h_valid h_wp
    rw [runCfgSteps_step] at h_wp
    have h_ok1 : cfgOk (stepCfgState body cfg) = true :=
      cfgOk_of_runCfgSteps_true body fuel' (stepCfgState body cfg)
        (by
          cases h_end : runCfgSteps body (stepCfgState body cfg) fuel' with
          | halted ok out =>
            rw [h_end] at h_wp
            exact h_wp.1
          | running _ _ _ =>
            rw [h_end] at h_wp
            exact False.elim h_wp
          | faulted =>
            rw [h_end] at h_wp
            exact False.elim h_wp)
    have h_ok0 : cfgOk cfg = true := by
      cases h_c : cfgOk cfg with
      | true => rfl
      | false =>
        rw [cfgOk_stepCfgState_false body cfg h_c] at h_ok1
        nomatch h_ok1
    cases cfg with
    | faulted => nomatch h_ok0
    | halted ok out =>
      change st = .halted out at h_valid
      subst h_valid
      change ok = true at h_ok0
      subst h_ok0
      dsimp only [stepCfgState] at h_wp
      rw [runCfgSteps_halted] at h_wp
      exact h_wp.2
    | running ok cur s =>
      change ok = true at h_ok0
      subst h_ok0
      rcases h_valid with ⟨rfl, h_cur⟩
      dsimp only [stepCfgState] at h_ok1 h_wp
      cases h_ac : s.memory.activeCallee with
      | some _ =>
        rw [h_ac] at h_ok1
        nomatch h_ok1
      | none =>
        rw [h_ac] at h_ok1 h_wp
        dsimp only at h_ok1 h_wp
        rw [wpCoalBounded_succ_eq]
        dsimp only [stepMirState, stepMirFn]
        rw [h_ac]
        dsimp only [Option.getD]
        rw [h_phase]
        dsimp only
        cases cur with
        | none =>
          cases h_si : Nat.beq s.frame.stmtIdx 0 with
          | false =>
            rw [h_si] at h_ok1
            nomatch h_ok1
          | true =>
            rw [h_si] at h_ok1 h_wp
            dsimp only [lookupBlock] at h_ok1 h_wp
            have h_si_eq : s.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_si
            cases h_bb : get? body.basicBlocks s.frame.blockIdx with
            | none =>
              rw [h_bb] at h_ok1
              nomatch h_ok1
            | some bb =>
              rw [h_bb] at h_ok1 h_wp
              rcases bb with ⟨stmts, term, isCleanup⟩
              rw [h_si_eq]
              cases stmts with
              | nil =>
                dsimp only [dispatchBlockCfg, get?, GetElem?.getElem?,
                  List.instGetElem?NatLtLength, List.get?Internal, length, BEq.beq,
                  instBEqOfDecidableEq, Nat.decEq, instDecidableEqNat, decide] at h_ok1 h_wp ⊢
                exact wpCoalBounded_evalTerminatorCfg body post fuel' s term h_ok1 ih h_wp
              | cons stmt rest =>
                dsimp only [dispatchBlockCfg, get?, GetElem?.getElem?,
                  List.instGetElem?NatLtLength, List.get?Internal] at h_ok1 h_wp ⊢
                rw [← evalStmtFast_eq body s stmt]
                exact wpCoalBounded_stepNodeToCfg body post fuel'
                  (.some (s.frame.blockIdx, 1, rest, term))
                  (evalStmtFast body s stmt)
                  ⟨⟨stmt :: rest, term, isCleanup⟩, [stmt], h_bb, rfl, rfl, rfl⟩
                  h_ok1 ih h_wp
        | some tup =>
          rcases tup with ⟨blockIdx, stmtIdx, stmts, term⟩
          rcases h_cur with ⟨bb, pfx, h_bb, rfl, h_stmts, rfl⟩
          cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
          | false =>
            cases stmts <;> (dsimp only at h_ok1; rw [h_bi] at h_ok1; nomatch h_ok1)
          | true =>
            have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
            cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
            | false =>
              cases stmts <;> (dsimp only at h_ok1; rw [h_bi, h_si] at h_ok1; nomatch h_ok1)
            | true =>
              have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
              rw [h_bi_eq, h_bb, h_si_eq]
              dsimp only
              cases stmts with
              | nil =>
                dsimp only at h_ok1 h_wp
                rw [h_bi, h_si] at h_ok1 h_wp
                have h_eq : bb.statements = pfx := by simpa using h_stmts
                rw [← h_eq, get?_length_none]
                dsimp only
                have h_beq : (length bb.statements == length bb.statements) = true :=
                  beq_self_eq_true _
                rw [h_beq, if_pos rfl]
                exact wpCoalBounded_evalTerminatorCfg body post fuel' s bb.terminator h_ok1 ih h_wp
              | cons stmt rest =>
                dsimp only at h_ok1 h_wp
                rw [h_bi, h_si] at h_ok1 h_wp
                rw [h_stmts, get?_append_cons]
                dsimp only
                rw [← evalStmtFast_eq body s stmt]
                exact wpCoalBounded_stepNodeToCfg body post fuel'
                  (.some (blockIdx, Nat.add (length pfx) 1, rest, bb.terminator))
                  (evalStmtFast body s stmt)
                  ⟨bb, pfx ++ [stmt], h_bb, (length_append_singleton pfx stmt).symm,
                    by simp [h_stmts, List.append_assoc], rfl⟩
                  h_ok1 ih h_wp

theorem wpCoalBounded_default_of_noCall
    (fuel : Nat) (body : CapturedMir) (post : MirOutcome → Prop) (st : MirExecState)
    (h : wpCoalBounded fuel mirNoCallWP (stepMirState body) (fun out _ => post out) st PUnit.unit) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body) (fun out _ => post out) st PUnit.unit := by
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpCoalBounded at h ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h ⊢
      exact h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih st' h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · exact False.elim h
      · cases e
        exact ih (k PUnit.unit) h
      · exact False.elim h

theorem cfgStateWP_of_eq
    {post : MirOutcome → Prop} {cfg : CfgExecState} {out : MirOutcome}
    (h_eq : cfg = .halted true out) (h_post : post out) :
    cfgStateWP post cfg := by
  rw [h_eq]
  exact ⟨rfl, h_post⟩

def evalMirSpecBool (specBody : CapturedMir) (args : List Value) : Bool :=
  match runCfgSteps specBody
    (.running true .none (initMachineState specBody args))
    (defaultSpecSteps specBody) with
  | .halted true (.normal (.scalar { bits := 1, sizeBytes := 1 }, _)) => true
  | _ => false

theorem mirBoolPredicateHolds_of_evalMirSpecBool_true
    (specBody : CapturedMir) (args : List Value)
    (h_phase : specBody.phase = .runtimeOptimized)
    (h_eval : evalMirSpecBool specBody args = true) :
    MirBoolPredicateHolds specBody args := by
  apply mirBoolPredicateHolds_of_wpMirSym_true (defaultSpecSteps specBody + 1) specBody args
  unfold wpMirSym
  rw [wpMirExecSym_eq_wpCoalBounded]
  apply wpCoalBounded_default_of_noCall
  refine wpCoalBounded_of_runCfgSteps specBody boolTruePost h_phase (defaultSpecSteps specBody)
    (.running true .none (initMachineState specBody args))
    (.running (initMachineState specBody args))
    ⟨rfl, trivial⟩ ?_
  unfold evalMirSpecBool at h_eval
  revert h_eval
  cases runCfgSteps specBody
    (.running true .none (initMachineState specBody args))
    (defaultSpecSteps specBody) with
  | running _ _ _ => intro h; contradiction
  | faulted => intro h; contradiction
  | halted ok out =>
    cases ok with
    | false => intro h; contradiction
    | true =>
      cases out with
      | panic => intro h; contradiction
      | abort => intro h; contradiction
      | normal rv =>
        rcases rv with ⟨v, mem'⟩
        cases v with
        | scalar sc =>
          rcases sc with ⟨bits, sz⟩
          cases bits with
          | zero => intro h; contradiction
          | succ b' =>
            cases b' with
            | zero =>
              cases sz with
              | zero => intro h; contradiction
              | succ sz' =>
                cases sz' with
                | zero => intro _; exact ⟨rfl, boolTruePost_normal_one mem'⟩
                | succ _ => intro h; contradiction
            | succ _ => intro h; contradiction
        | _ => intro h; contradiction

theorem verifyStatefulMirNoPanic_of_runCfgSteps
    (c : StatefulClaim)
    (h_phase : c.body.phase = .runtimeOptimized)
    (h_bb0 : get? c.body.basicBlocks 0 = some (entryBB c.body))
    (h_callees : c.callees = [])
    (h_wp : ∀ args mem, c.pre args mem →
      ∃ retVal,
        runCfgSteps c.body
          (.running true (.some (0, 0, (entryBB c.body).statements, (entryBB c.body).terminator))
            (initMachineStateWithMemory c.body args mem))
          (defaultCfgSteps c.body) = .halted true (.normal (retVal, mem)) ∧
        c.post args mem retVal mem) :
    StatefulVerificationResult c := by
  refine verifyStatefulMirNoPanicSym c (defaultCfgSteps c.body + 1) ?_
  intro args mem h_pre
  rw [h_callees]
  rcases h_wp args mem h_pre with ⟨retVal, h_eq, h_post⟩
  unfold wpMirSym
  rw [wpMirExecSym_eq_wpCoalBounded]
  exact wpCoalBounded_default_of_noCall (defaultCfgSteps c.body + 1) c.body
    (mirNormalPost (c.post args mem))
    (.running (initMachineStateWithMemory c.body args mem))
    (wpCoalBounded_of_runCfgSteps c.body
      (mirNormalPost (c.post args mem))
      h_phase (defaultCfgSteps c.body)
      (.running true (.some (0, 0, (entryBB c.body).statements, (entryBB c.body).terminator))
        (initMachineStateWithMemory c.body args mem))
      (.running (initMachineStateWithMemory c.body args mem))
      ⟨rfl, ⟨entryBB c.body, [], h_bb0, rfl, rfl, rfl⟩⟩
      (cfgStateWP_of_eq h_eq h_post))

theorem verifyStatefulEquivMir_of_runCfgSteps
    (c : StatefulEquivClaim)
    (model : List Value → Memory → Value × Memory)
    (h_impl_phase : c.implBody.phase = .runtimeOptimized)
    (h_impl_bb0 : get? c.implBody.basicBlocks 0 = some (entryBB c.implBody))
    (h_impl_callees : c.implCallees = [])
    (h_spec_phase : c.specBody.phase = .runtimeOptimized)
    (h_spec_bb0 : get? c.specBody.basicBlocks 0 = some (entryBB c.specBody))
    (h_spec_callees : c.specCallees = [])
    (h_impl : ∀ args mem, c.pre args mem →
      runCfgSteps c.implBody
        (.running true
          (.some (0, 0, (entryBB c.implBody).statements, (entryBB c.implBody).terminator))
          (initMachineStateWithMemory c.implBody args mem))
        (defaultCfgSteps c.implBody) = .halted true (.normal (model args mem)) ∧
      c.post args mem (model args mem).1 (model args mem).2)
    (h_spec : ∀ args mem, c.pre args mem →
      runCfgSteps c.specBody
        (.running true
          (.some (0, 0, (entryBB c.specBody).statements, (entryBB c.specBody).terminator))
          (initMachineStateWithMemory c.specBody args mem))
        (defaultCfgSteps c.specBody) = .halted true (.normal (model args mem))) :
    StatefulEquivVerificationResult c := by
  refine verifyStatefulEquivMirBounded c
    (defaultCfgSteps c.implBody + 1) (defaultCfgSteps c.specBody + 1) model
    (fun args mem h_pre => ?_)
    (fun args mem h_pre => ?_)
  · rcases h_impl args mem h_pre with ⟨h_eq, h_post⟩
    unfold wpMirNoCallBounded
    rw [h_impl_callees]
    exact wpCoalBounded_of_runCfgSteps c.implBody _ h_impl_phase (defaultCfgSteps c.implBody)
      (.running true
        (.some (0, 0, (entryBB c.implBody).statements, (entryBB c.implBody).terminator))
        (initMachineStateWithMemory c.implBody args mem))
      (.running (initMachineStateWithMemory c.implBody args mem))
      ⟨rfl, ⟨entryBB c.implBody, [], h_impl_bb0, rfl, rfl, rfl⟩⟩
      (cfgStateWP_of_eq h_eq ⟨rfl, h_post⟩)
  · have h_eq := h_spec args mem h_pre
    unfold wpMirNoCallBounded
    rw [h_spec_callees]
    exact wpCoalBounded_of_runCfgSteps c.specBody _ h_spec_phase (defaultCfgSteps c.specBody)
      (.running true
        (.some (0, 0, (entryBB c.specBody).statements, (entryBB c.specBody).terminator))
        (initMachineStateWithMemory c.specBody args mem))
      (.running (initMachineStateWithMemory c.specBody args mem))
      ⟨rfl, ⟨entryBB c.specBody, [], h_spec_bb0, rfl, rfl, rfl⟩⟩
      (cfgStateWP_of_eq h_eq rfl)

def stepsExecMid (mid : MachineState → Prop) (post : MirOutcome → Prop) : MirExecState → Prop
  | .running s' => mid s'
  | .halted out => post out
  | .faulted _ => False

def cfgStepsWP (mid : MachineState → Prop) (post : MirOutcome → Prop) : CfgExecState → Prop
  | .running ok _ s => ok = true ∧ mid s
  | .halted ok out => ok = true ∧ post out
  | .faulted => False

theorem cfgOk_of_cfgStepsWP
    {mid : MachineState → Prop} {post : MirOutcome → Prop} {cfg : CfgExecState}
    (h : cfgStepsWP mid post cfg) :
    cfgOk cfg = true := by
  cases cfg with
  | running ok _ _ => exact h.1
  | halted ok _ => exact h.1
  | faulted => exact False.elim h

def stepNodeStepsWP
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (fuel : Nat) (node : MirStepNode) : Prop :=
  match node with
  | .ret out => post out
  | .tau st' =>
    wpMirExecStepsSym fuel body st' (stepsExecMid mid post) post
  | .vis i k =>
    mirNoCallWP.wp i
      (fun o _ =>
        wpMirExecStepsSym fuel body (k o) (stepsExecMid mid post) post)
      PUnit.unit

theorem wpMirExecStepsSym_succ_eq
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (fuel : Nat) (st : MirExecState) :
    wpMirExecStepsSym (fuel + 1) body st (stepsExecMid mid post) post =
      stepNodeStepsWP body mid post fuel (stepMirState body st) := by
  unfold wpMirExecStepsSym stepNodeStepsWP
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
  rfl

theorem wpMirExecStepsSym_halted
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (fuel : Nat) (out : MirOutcome) (h : post out) :
    wpMirExecStepsSym fuel body (.halted out) (stepsExecMid mid post) post := by
  induction fuel with
  | zero => exact h
  | succ _ _ =>
    unfold wpMirExecStepsSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
    dsimp only [stepMirState]
    exact h

theorem wpMirExecStepsSym_stepNodeToCfg
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (fuel' : Nat)
    (nextCur : Option (Nat × Nat × List Statement × Terminator))
    (node : MirStepNode)
    (h_cur : CurValid body nextCur)
    (h_ok : cfgOk (stepNodeToCfg true nextCur node) = true)
    (ih : ∀ cfg' st', CfgValid body cfg' st' →
      cfgStepsWP mid post (runCfgSteps body cfg' fuel') →
      wpMirExecStepsSym fuel' body st' (stepsExecMid mid post) post)
    (h_wp : cfgStepsWP mid post (runCfgSteps body (stepNodeToCfg true nextCur node) fuel')) :
    stepNodeStepsWP body mid post fuel' node := by
  cases node with
  | ret out =>
    dsimp only [stepNodeToCfg] at h_wp
    rw [runCfgSteps_halted] at h_wp
    exact h_wp.2
  | tau st' =>
    cases st' with
    | running s' =>
      exact ih (.running true nextCur s') (.running s') ⟨rfl, h_cur⟩ h_wp
    | halted out =>
      exact ih (.halted true out) (.halted out) rfl h_wp
    | faulted _ => nomatch h_ok
  | vis i k =>
    rcases i with f | (e | c)
    · nomatch h_ok
    · cases e
      dsimp only [stepNodeToCfg] at h_ok h_wp
      cases h_k : k PUnit.unit with
      | running s' =>
        rw [h_k] at h_wp
        have h_res := ih (.running true nextCur s') (.running s') ⟨rfl, h_cur⟩ h_wp
        rw [← h_k] at h_res
        exact h_res
      | halted out =>
        rw [h_k] at h_wp
        have h_res := ih (.halted true out) (.halted out) rfl h_wp
        rw [← h_k] at h_res
        exact h_res
      | faulted _ =>
        rw [h_k] at h_ok
        nomatch h_ok
    · nomatch h_ok

theorem wpMirExecStepsSym_evalTerminatorCfg
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (fuel' : Nat) (s : MachineState) (term : Terminator)
    (h_ok : cfgOk (evalTerminatorCfg body true s term) = true)
    (ih : ∀ cfg' st', CfgValid body cfg' st' →
      cfgStepsWP mid post (runCfgSteps body cfg' fuel') →
      wpMirExecStepsSym fuel' body st' (stepsExecMid mid post) post)
    (h_wp : cfgStepsWP mid post (runCfgSteps body (evalTerminatorCfg body true s term) fuel')) :
    stepNodeStepsWP body mid post fuel' (evalTerminator s term (some body)) := by
  rcases term with ⟨kind, span⟩
  revert h_ok h_wp
  cases kind with
  | goto target =>
    intro _ h_wp
    exact ih (.running true .none { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
      (.running { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
      ⟨rfl, trivial⟩ h_wp
  | return_ =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    cases s.memory.callStack with
    | cons _ _ => rintro ⟨⟩ _
    | nil =>
      dsimp only
      cases get? s.frame.locals 0 with
      | none => rintro ⟨⟩ _
      | some slot =>
        cases slot with
        | dead => rintro ⟨⟩ _
        | uninit => rintro ⟨⟩ _
        | init retVal =>
          cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              (length ([] : List SavedCallerFrame)) (length s.frame.locals) with
          | true => rintro ⟨⟩ _
          | false =>
            intro _ h_wp
            dsimp only [stepNodeStepsWP, MirStepNode.retNormal] at h_wp ⊢
            rw [runCfgSteps_halted] at h_wp
            exact h_wp.2
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    rw [evalOperandFast_eq]
    cases evalOperand s.frame.locals discr s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals (callStack := s.memory.callStack) with
    | ub => rintro ⟨⟩ _
    | unsupported => rintro ⟨⟩ _
    | ok v locals' =>
      cases v with
      | scalar sc =>
        dsimp only [stepNodeStepsWP, MirStepNode.step]
        intro _ h_wp
        exact ih
          (.running true .none
            { s with
              frame :=
                { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise
                  stmtIdx := 0
                  locals := locals' } })
          (.running
            { s with
              frame :=
                { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise
                  stmtIdx := 0
                  locals := locals' } })
          ⟨rfl, trivial⟩ h_wp
      | _ => rintro ⟨⟩ _
  | assert cond expected target unwind =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    rw [evalOperandFast_eq]
    cases evalOperand s.frame.locals cond s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals (callStack := s.memory.callStack) with
    | ub => rintro ⟨⟩ _
    | unsupported => rintro ⟨⟩ _
    | ok v locals' =>
      cases v with
      | scalar sc =>
        cases expected <;>
        · dsimp only [cfgOk, Bool.and]
          intro h_ok h_wp
          rw [h_ok] at h_wp ⊢
          dsimp only [stepNodeStepsWP, MirStepNode.step] at h_wp ⊢
          exact ih
            (.running true .none { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })
            (.running { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })
            ⟨rfl, trivial⟩ h_wp
      | _ => rintro ⟨⟩ _
  | _ => rintro ⟨⟩ _

theorem wpMirExecStepsSym_of_runCfgSteps
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) :
    ∀ (fuel : Nat) (cfg : CfgExecState) (st : MirExecState),
      CfgValid body cfg st →
      cfgStepsWP mid post (runCfgSteps body cfg fuel) →
      wpMirExecStepsSym fuel body st (stepsExecMid mid post) post := by
  intro fuel
  induction fuel with
  | zero =>
    intro cfg st h_valid h_wp
    dsimp only [runCfgSteps] at h_wp
    cases cfg with
    | running ok _ s =>
      rcases h_valid with ⟨rfl, _⟩
      exact h_wp.2
    | faulted => exact False.elim h_wp
    | halted ok out =>
      change st = .halted out at h_valid
      subst h_valid
      exact h_wp.2
  | succ fuel' ih =>
    intro cfg st h_valid h_wp
    rw [runCfgSteps_step] at h_wp
    have h_ok1 : cfgOk (stepCfgState body cfg) = true :=
      cfgOk_of_runCfgSteps_true body fuel' (stepCfgState body cfg) (cfgOk_of_cfgStepsWP h_wp)
    have h_ok0 : cfgOk cfg = true := by
      cases h_c : cfgOk cfg with
      | true => rfl
      | false =>
        rw [cfgOk_stepCfgState_false body cfg h_c] at h_ok1
        nomatch h_ok1
    cases cfg with
    | faulted => nomatch h_ok0
    | halted ok out =>
      change st = .halted out at h_valid
      subst h_valid
      change ok = true at h_ok0
      subst h_ok0
      dsimp only [stepCfgState] at h_wp
      rw [runCfgSteps_halted] at h_wp
      exact wpMirExecStepsSym_halted body mid post (fuel' + 1) out h_wp.2
    | running ok cur s =>
      change ok = true at h_ok0
      subst h_ok0
      rcases h_valid with ⟨rfl, h_cur⟩
      dsimp only [stepCfgState] at h_ok1 h_wp
      cases h_ac : s.memory.activeCallee with
      | some _ =>
        rw [h_ac] at h_ok1
        nomatch h_ok1
      | none =>
        rw [h_ac] at h_ok1 h_wp
        dsimp only at h_ok1 h_wp
        rw [wpMirExecStepsSym_succ_eq]
        dsimp only [stepMirState, stepMirFn]
        rw [h_ac]
        dsimp only [Option.getD]
        rw [h_phase]
        dsimp only
        cases cur with
        | none =>
          cases h_si : Nat.beq s.frame.stmtIdx 0 with
          | false =>
            rw [h_si] at h_ok1
            nomatch h_ok1
          | true =>
            rw [h_si] at h_ok1 h_wp
            dsimp only [lookupBlock] at h_ok1 h_wp
            have h_si_eq : s.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_si
            cases h_bb : get? body.basicBlocks s.frame.blockIdx with
            | none =>
              rw [h_bb] at h_ok1
              nomatch h_ok1
            | some bb =>
              rw [h_bb] at h_ok1 h_wp
              rcases bb with ⟨stmts, term, isCleanup⟩
              rw [h_si_eq]
              cases stmts with
              | nil =>
                dsimp only [dispatchBlockCfg, get?, GetElem?.getElem?,
                  List.instGetElem?NatLtLength, List.get?Internal, length, BEq.beq,
                  instBEqOfDecidableEq, Nat.decEq, instDecidableEqNat, decide] at h_ok1 h_wp ⊢
                exact wpMirExecStepsSym_evalTerminatorCfg body mid post fuel' s term h_ok1 ih h_wp
              | cons stmt rest =>
                dsimp only [dispatchBlockCfg, get?, GetElem?.getElem?,
                  List.instGetElem?NatLtLength, List.get?Internal] at h_ok1 h_wp ⊢
                rw [← evalStmtFast_eq body s stmt]
                exact wpMirExecStepsSym_stepNodeToCfg body mid post fuel'
                  (.some (s.frame.blockIdx, 1, rest, term))
                  (evalStmtFast body s stmt)
                  ⟨⟨stmt :: rest, term, isCleanup⟩, [stmt], h_bb, rfl, rfl, rfl⟩
                  h_ok1 ih h_wp
        | some tup =>
          rcases tup with ⟨blockIdx, stmtIdx, stmts, term⟩
          rcases h_cur with ⟨bb, pfx, h_bb, rfl, h_stmts, rfl⟩
          cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
          | false =>
            cases stmts <;> (dsimp only at h_ok1; rw [h_bi] at h_ok1; nomatch h_ok1)
          | true =>
            have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
            cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
            | false =>
              cases stmts <;> (dsimp only at h_ok1; rw [h_bi, h_si] at h_ok1; nomatch h_ok1)
            | true =>
              have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
              rw [h_bi_eq, h_bb, h_si_eq]
              dsimp only
              cases stmts with
              | nil =>
                dsimp only at h_ok1 h_wp
                rw [h_bi, h_si] at h_ok1 h_wp
                have h_eq : bb.statements = pfx := by simpa using h_stmts
                rw [← h_eq, get?_length_none]
                dsimp only
                have h_beq : (length bb.statements == length bb.statements) = true :=
                  beq_self_eq_true _
                rw [h_beq, if_pos rfl]
                exact wpMirExecStepsSym_evalTerminatorCfg body mid post fuel' s bb.terminator h_ok1 ih h_wp
              | cons stmt rest =>
                dsimp only at h_ok1 h_wp
                rw [h_bi, h_si] at h_ok1 h_wp
                rw [h_stmts, get?_append_cons]
                dsimp only
                rw [← evalStmtFast_eq body s stmt]
                exact wpMirExecStepsSym_stepNodeToCfg body mid post fuel'
                  (.some (blockIdx, Nat.add (length pfx) 1, rest, bb.terminator))
                  (evalStmtFast body s stmt)
                  ⟨bb, pfx ++ [stmt], h_bb, (length_append_singleton pfx stmt).symm,
                    by simp [h_stmts, List.append_assoc], rfl⟩
                  h_ok1 ih h_wp

theorem mirStepsConverges_of_cfgStepsWP
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat)
    (cur : Option (Nat × Nat × List Statement × Terminator))
    (s : MachineState)
    (h_cur : CurValid body cur)
    (h_wp : cfgStepsWP mid post (runCfgSteps body (.running true cur s) fuel)) :
    MirStepsConverges body s mid post :=
  ⟨fuel, wpMirExecStepsSym_of_runCfgSteps body mid post h_phase fuel
    (.running true cur s) (.running s) ⟨rfl, h_cur⟩ h_wp⟩

theorem mirStepsConverges_of_cfgStepsWP_none
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat) (s : MachineState)
    (h_wp : cfgStepsWP mid post (runCfgSteps body (.running true .none s) fuel)) :
    MirStepsConverges body s mid post :=
  mirStepsConverges_of_cfgStepsWP body mid post h_phase fuel .none s trivial h_wp

theorem mirStepsConverges_of_runCfgSteps
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat)
    (cur : Option (Nat × Nat × List Statement × Terminator))
    (s : MachineState)
    (cur' : Option (Nat × Nat × List Statement × Terminator))
    (s' : MachineState)
    (h_cur : CurValid body cur)
    (h_eq : runCfgSteps body (.running true cur s) fuel = .running true cur' s')
    (h_mid : mid s') :
    MirStepsConverges body s mid post :=
  mirStepsConverges_of_cfgStepsWP body mid post h_phase fuel cur s h_cur
    (by rw [h_eq]; exact ⟨rfl, h_mid⟩)

theorem mirStepsConverges_of_runCfgSteps_none
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat) (s : MachineState)
    (cur' : Option (Nat × Nat × List Statement × Terminator))
    (s' : MachineState)
    (h_eq : runCfgSteps body (.running true .none s) fuel = .running true cur' s')
    (h_mid : mid s') :
    MirStepsConverges body s mid post :=
  mirStepsConverges_of_runCfgSteps body mid post h_phase fuel .none s cur' s' trivial h_eq h_mid

theorem mirNoCallWpConverges_of_cfgStateWP
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat)
    (cur : Option (Nat × Nat × List Statement × Terminator))
    (s : MachineState)
    (h_cur : CurValid body cur)
    (h_wp : cfgStateWP post (runCfgSteps body (.running true cur s) fuel)) :
    MirNoCallWpConverges body s post := by
  refine ⟨fuel + 1, ?_⟩
  rw [wpMirNoCallSym_eq_wpMirNoCallBounded]
  exact wpCoalBounded_of_runCfgSteps body post h_phase fuel
    (.running true cur s) (.running s) ⟨rfl, h_cur⟩ h_wp

theorem mirWpConverges_of_cfgStateWP
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat)
    (cur : Option (Nat × Nat × List Statement × Terminator))
    (s : MachineState)
    (h_cur : CurValid body cur)
    (h_wp : cfgStateWP post (runCfgSteps body (.running true cur s) fuel)) :
    MirWpConverges body s post :=
  MirWpConverges.of_noCall
    (mirNoCallWpConverges_of_cfgStateWP body post h_phase fuel cur s h_cur h_wp)

theorem mirWpConverges_of_cfgStateWP_none
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat) (s : MachineState)
    (h_wp : cfgStateWP post (runCfgSteps body (.running true .none s) fuel)) :
    MirWpConverges body s post :=
  mirWpConverges_of_cfgStateWP body post h_phase fuel .none s trivial h_wp

theorem mirWpConverges_of_runCfgSteps
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat)
    (cur : Option (Nat × Nat × List Statement × Terminator))
    (s : MachineState) (out : MirOutcome)
    (h_cur : CurValid body cur)
    (h_eq : runCfgSteps body (.running true cur s) fuel = .halted true out)
    (h_post : post out) :
    MirWpConverges body s post :=
  mirWpConverges_of_cfgStateWP body post h_phase fuel cur s h_cur
    (cfgStateWP_of_eq h_eq h_post)

theorem mirWpConverges_of_runCfgSteps_none
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized)
    (fuel : Nat) (s : MachineState) (out : MirOutcome)
    (h_eq : runCfgSteps body (.running true .none s) fuel = .halted true out)
    (h_post : post out) :
    MirWpConverges body s post :=
  mirWpConverges_of_runCfgSteps body post h_phase fuel .none s out trivial h_eq h_post

/-! ### Running to the next block entry without a step count

`runCfgToBlock body target cfg` steps the CFG evaluator from `cfg` until it
next enters basic block `target` (a running state with no cached block at
statement 0 of `target`), halts, or faults. The first step is always taken,
so a loop header reaches itself again one iteration later. Proofs therefore
never state how many steps a loop iteration or a straight-line segment
takes; `length body.basicBlocks + 256` only bounds the recursion.

`runCfgUntilAux` checks `cfgAtBlock` before each step and returns as soon as
`target`, `.halted`, or `.faulted` is reached, so `dsimp` neither evaluates
a step past the target/halt nor unfolds the unused part of the bound.
-/

/-- Whether `cfg` is about to dispatch basic block `target` or has halted /
faulted. -/
def cfgAtBlock (target : Nat) : CfgExecState → Bool
  | .running _ .none s =>
    Nat.beq s.frame.blockIdx target && Nat.beq s.frame.stmtIdx 0
  | .running _ (.some _) _ => false
  | .halted _ _ => true
  | .faulted => true

/-- Step from `cfg` until `atTarget = cfgAtBlock target cfg` holds, taking
at most `budget` steps. -/
def runCfgUntilAux (body : CapturedMir) (target : Nat) :
    Nat → CfgExecState → Bool → CfgExecState
  | _, cfg, true => cfg
  | 0, cfg, false => cfg
  | budget + 1, cfg, false =>
    runCfgUntilAux body target budget (stepCfgState body cfg)
      (cfgAtBlock target (stepCfgState body cfg))

/-- Evaluate from `cfg` until the next entry into block `target`, a halt, or
a fault, taking at least one and at most `length body.basicBlocks + 256 + 1`
steps. -/
def runCfgToBlock (body : CapturedMir) (target : Nat) (cfg : CfgExecState) :
    CfgExecState :=
  runCfgUntilAux body target (Nat.add (length body.basicBlocks) 256)
    (stepCfgState body cfg) (cfgAtBlock target (stepCfgState body cfg))

theorem runCfgUntilAux_eq_runCfgSteps (body : CapturedMir) (target : Nat) :
    ∀ budget cfg atTarget, ∃ k,
      runCfgUntilAux body target budget cfg atTarget = runCfgSteps body cfg k
  | _, cfg, true => ⟨0, by cases ‹Nat› <;> rfl⟩
  | 0, cfg, false => ⟨0, rfl⟩
  | budget + 1, cfg, false => by
    obtain ⟨k, hk⟩ := runCfgUntilAux_eq_runCfgSteps body target budget
      (stepCfgState body cfg) (cfgAtBlock target (stepCfgState body cfg))
    exact ⟨k + 1, by rw [runCfgUntilAux, hk, runCfgSteps_step]⟩

/-- Every `runCfgToBlock` run is a prefix of `runCfgSteps`. -/
theorem runCfgToBlock_eq_runCfgSteps (body : CapturedMir) (target : Nat)
    (cfg : CfgExecState) :
    ∃ k, runCfgToBlock body target cfg = runCfgSteps body cfg k := by
  obtain ⟨k, hk⟩ := runCfgUntilAux_eq_runCfgSteps body target
    (Nat.add (length body.basicBlocks) 256) (stepCfgState body cfg)
    (cfgAtBlock target (stepCfgState body cfg))
  exact ⟨k + 1, by rw [runCfgToBlock, hk, runCfgSteps_step]⟩

/-- `mirStepsConverges_of_cfgStepsWP_none` without a step count: the segment
from `s` ends at the next entry into block `target`, or halts. -/
theorem mirStepsConverges_of_runCfgToBlock
    (body : CapturedMir) (mid : MachineState → Prop) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) (target : Nat) (s : MachineState)
    (h_wp : cfgStepsWP mid post
      (runCfgToBlock body target (.running true .none s))) :
    MirStepsConverges body s mid post := by
  obtain ⟨k, hk⟩ :=
    runCfgToBlock_eq_runCfgSteps body target (.running true .none s)
  rw [hk] at h_wp
  exact mirStepsConverges_of_cfgStepsWP body mid post h_phase k .none s
    trivial h_wp

/-- `mirNoCallWpConverges_of_cfgStateWP` without a step count, for a segment
that halts before it re-enters block `target`. -/
theorem mirNoCallWpConverges_of_runCfgToBlock
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) (target : Nat) (s : MachineState)
    (h_wp : cfgStateWP post
      (runCfgToBlock body target (.running true .none s))) :
    MirNoCallWpConverges body s post := by
  obtain ⟨k, hk⟩ :=
    runCfgToBlock_eq_runCfgSteps body target (.running true .none s)
  rw [hk] at h_wp
  exact mirNoCallWpConverges_of_cfgStateWP body post h_phase k .none s
    trivial h_wp

/-- `mirWpConverges_of_cfgStateWP_none` without a step count, for a segment
that halts before it re-enters block `target`. -/
theorem mirWpConverges_of_runCfgToBlock
    (body : CapturedMir) (post : MirOutcome → Prop)
    (h_phase : body.phase = .runtimeOptimized) (target : Nat) (s : MachineState)
    (h_wp : cfgStateWP post
      (runCfgToBlock body target (.running true .none s))) :
    MirWpConverges body s post :=
  MirWpConverges.of_noCall
    (mirNoCallWpConverges_of_runCfgToBlock body post h_phase target s h_wp)

/--
Fuel-bounded partial-correctness (`mirSafePost`) state-to-state symbolic stepper
over alias-erased `PureState` (permitting clean panics/aborts while forbidding UB;
defaults `post` to `fun _ => False` matching `wpPureMirSteps`).
-/
def wpPureMirSafeSteps
    (fuel : Nat) (body : CapturedMir) (ps : PureState)
    (mid : PureState → Prop)
    (post : Value → Prop := fun _ => False) : Prop :=
  wpMirStepsSym fuel body (ps.toMachineState emptyMemory)
    (fun ms' => mid (PureState.ofMachineState ms'))
    (mirSafePost (fun retVal _ => post retVal))

/--
Fuel-free partial-correctness (`mirSafePost`) intermediate state convergence
over alias-erased `PureState` (defaults `post` to `fun _ => False` matching
`PureMirStepsConverges`).
-/
def PureMirSafeStepsConverges
    (body : CapturedMir) (ps : PureState)
    (mid : PureState → Prop)
    (post : Value → Prop := fun _ => False) : Prop :=
  ∃ fuel : Nat, wpPureMirSafeSteps fuel body ps mid post

/-- Zero-step reflexivity for `PureMirSafeStepsConverges`. -/
theorem PureMirSafeStepsConverges.refl
    {body : CapturedMir} {ps : PureState}
    {mid : PureState → Prop} {post : Value → Prop}
    (h : mid ps) :
    PureMirSafeStepsConverges body ps mid post :=
  ⟨0, h⟩

/-- Lift a panic-forbidding `PureMirStepsConverges` step into `PureMirSafeStepsConverges`. -/
theorem PureMirSafeStepsConverges.of_steps
    {body : CapturedMir} {ps : PureState}
    {mid : PureState → Prop} {post : Value → Prop}
    (h : PureMirStepsConverges body ps mid post) :
    PureMirSafeStepsConverges body ps mid post := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirStepsSym_mono (fun _ hm => hm) (fun _ => mirNormalPost_imp_mirSafePost) h_wp⟩

/--
Sequential composition (`bind`) for partial-correctness `PureMirSafeConverges`
over alias-erased `PureState`.
-/
theorem PureMirSafeConverges.bind
    {body : CapturedMir} {ps : PureState}
    {mid : PureState → Prop} {post : Value → Prop}
    (h₁ : PureMirSafeStepsConverges body ps mid post)
    (h₂ : ∀ ps', mid ps' → PureMirSafeConverges body ps' post)
    (h_pure : checkPureMir body = true) :
    PureMirSafeConverges body ps post := by
  rcases h₁ with ⟨f₁, hf₁⟩
  have h_steps :
      MirStepsConverges body (ps.toMachineState emptyMemory)
        (fun ms' =>
          mid (PureState.ofMachineState ms') ∧
          ms' = (PureState.ofMachineState ms').toMachineState emptyMemory)
        (mirSafePost (fun retVal _ => post retVal)) := by
    suffices ∀ (f : Nat) (st : MirExecState),
        wpMirExecStepsSym f body (MirExecState.withMem emptyMemory st)
          (fun
            | .running s' => mid (PureState.ofMachineState s')
            | .halted out => mirSafePost (fun retVal _ => post retVal) out
            | .faulted _ => False)
          (mirSafePost (fun retVal _ => post retVal)) →
        wpMirExecStepsSym f body (MirExecState.withMem emptyMemory st)
          (fun
            | .running s' =>
              mid (PureState.ofMachineState s') ∧
              s' = (PureState.ofMachineState s').toMachineState emptyMemory
            | .halted out => mirSafePost (fun retVal _ => post retVal) out
            | .faulted _ => False)
          (mirSafePost (fun retVal _ => post retVal)) from
      ⟨f₁, this f₁ (.running (ps.toMachineState emptyMemory)) hf₁⟩
    intro f
    induction f with
    | zero =>
      intro st h_st
      cases st with
      | running s' => exact ⟨h_st, rfl⟩
      | halted out => exact h_st
      | faulted _ => exact False.elim h_st
    | succ f' ih =>
      intro st h_st
      cases st with
      | halted _ =>
        unfold wpMirExecStepsSym at h_st ⊢
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
        exact h_st
      | faulted _ =>
        unfold wpMirExecStepsSym at h_st
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st
        exact False.elim h_st
      | running s =>
        unfold wpMirExecStepsSym at h_st ⊢
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
        dsimp only [MirExecState.withMem, stepMirState] at h_st ⊢
        have h_eq :=
          stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
            (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
        dsimp only [PureState.toMachineState_ofMachineState] at h_eq
        rw [h_eq] at h_st ⊢
        cases h_step : stepMirFn body { s with memory := emptyMemory } with
        | ret _ =>
          rw [h_step] at h_st
          dsimp only [MirStepNode.withMem] at h_st
          exact h_st
        | tau st' =>
          rw [h_step] at h_st
          dsimp only [MirStepNode.withMem] at h_st
          exact ih st' h_st
        | vis i k =>
          rw [h_step] at h_st
          dsimp only [MirStepNode.withMem] at h_st
          cases i with
          | inl _ => exact False.elim h_st
          | inr i2 => cases i2 with
            | inl _ => exact ih (k PUnit.unit) h_st
            | inr _ => exact False.elim h_st
  exact MirWpConverges.bind h_steps (fun ms' ⟨h_mid, h_eq⟩ => by
    rw [h_eq]
    exact h₂ (PureState.ofMachineState ms') h_mid)

end Anneal.PureMirExec

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

/-!
## `MirFragment` Preconditions & Readiness Bridges (`Anneal.MirLiftCore`)

Connects the 5-element decidable `MirFragment` lattice (`Anneal.PureMirExec`)
with the phase (`body.phase ∈ {.runtimePostCleanup, .runtimeOptimized}`) and
non-cleanup (`bb.isCleanup = false`) preconditions of `MirLiftCore` and
`MirLoops`.
-/

/--
True iff `body.phase` is one of the two runtime MIR phases supported by
`MirLiftCore` (`MirPhaseTag.runtimePostCleanup` or `MirPhaseTag.runtimeOptimized`).
-/
def isMirLiftPhase (body : CapturedMir) : Bool :=
  match body.phase with
  | .runtimePostCleanup | .runtimeOptimized => true
  | _ => false

/--
Exact biconditional between `isMirLiftPhase body = true` and the phase
disjunction required by `LiftStmtsTerminator` rules.
-/
@[simp]
theorem isMirLiftPhase_iff (body : CapturedMir) :
    isMirLiftPhase body = true ↔
      body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized := by
  unfold isMirLiftPhase
  cases body.phase <;> simp

@[simp]
theorem isMirLiftPhase_instantiate (body : CapturedMir) (args : TypeSubst) :
    isMirLiftPhase (body.instantiate args) = isMirLiftPhase body :=
  rfl

/--
True iff every basic block in `body.basicBlocks` has `bb.isCleanup = false`
(matching the `isCleanup := false` premise of `LiftStmtsTerminator` rules).
-/
def hasNoCleanupBlocks (body : CapturedMir) : Bool :=
  body.basicBlocks.all (fun bb => !bb.isCleanup)

/--
Extract `bb.isCleanup = false` at any in-bounds basic block
`Trusted.Sequence.get? body.basicBlocks bbIdx = some bb` from
`hasNoCleanupBlocks body = true`.
-/
theorem isCleanup_false_of_hasNoCleanupBlocks
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h_clean : hasNoCleanupBlocks body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb) :
    bb.isCleanup = false := by
  have h_not : (!bb.isCleanup) = true :=
    list_all_of_get? (xs := body.basicBlocks) (idx := (bbIdx : Nat)) h_clean h_bb
  cases h_ic : bb.isCleanup
  · rfl
  · rw [h_ic] at h_not
    cases h_not

theorem hasNoCleanupBlocks_aux_iff :
    ∀ (bbs : List BasicBlockData),
      bbs.all (fun bb => !bb.isCleanup) = true ↔
        ∀ (idx : Nat) (bb : BasicBlockData),
          Trusted.Sequence.get? bbs idx = some bb → bb.isCleanup = false
  | [] => by
    constructor
    · intro _ _ _ h_get
      cases h_get
    · intro _
      rfl
  | hd :: tl => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · rintro ⟨h_hd, h_tl⟩ idx bb h_get
      cases idx with
      | zero =>
        cases h_get
        exact h_hd
      | succ idx' =>
        exact (hasNoCleanupBlocks_aux_iff tl).mp h_tl idx' bb h_get
    · intro h_all
      exact ⟨h_all 0 hd rfl,
        (hasNoCleanupBlocks_aux_iff tl).mpr (fun idx' bb h_get => h_all (idx' + 1) bb h_get)⟩

/--
Exact biconditional characterizing `hasNoCleanupBlocks body = true` across all
`Trusted.Sequence.get? body.basicBlocks bbIdx = some bb` lookups.
-/
theorem hasNoCleanupBlocks_iff (body : CapturedMir) :
    hasNoCleanupBlocks body = true ↔
      ∀ (bbIdx : BasicBlockIdx) (bb : BasicBlockData),
        Trusted.Sequence.get? body.basicBlocks bbIdx = some bb →
          bb.isCleanup = false :=
  hasNoCleanupBlocks_aux_iff body.basicBlocks

theorem hasNoCleanupBlocks_instantiateList
    (tbl : LayoutTable) (args : TypeSubst) :
    ∀ (bbs : List BasicBlockData),
      (BasicBlockData.instantiateList tbl args bbs).all (fun bb => !bb.isCleanup) =
        bbs.all (fun bb => !bb.isCleanup)
  | [] => rfl
  | bb :: rest => by
    dsimp only [BasicBlockData.instantiateList, BasicBlockData.instantiate, List.all_cons]
    rw [hasNoCleanupBlocks_instantiateList tbl args rest]

@[simp]
theorem hasNoCleanupBlocks_instantiate (body : CapturedMir) (args : TypeSubst) :
    hasNoCleanupBlocks (body.instantiate args) = hasNoCleanupBlocks body := by
  dsimp only [CapturedMir.instantiate, hasNoCleanupBlocks]
  rw [hasNoCleanupBlocks_instantiateList]

/--
Decidable readiness guard for pure MIR lifting (`.pureBoundedLoop` and below):
requires borrow-free purity (`checkBorrowFreeBodyFragment .pureBoundedLoop body`),
supported runtime MIR phase (`isMirLiftPhase body`), and no unwind cleanup
blocks (`hasNoCleanupBlocks body`).
-/
def checkMirLiftReady (body : CapturedMir) : Bool :=
  checkBorrowFreeBodyFragment .pureBoundedLoop body &&
    isMirLiftPhase body &&
    hasNoCleanupBlocks body

/--
Decidable single-pass `#mir_lift` readiness guard for DAG pure MIR
(`.pureLoopFree`): requires `checkBorrowFreeBodyFragment .pureLoopFree body`,
`isMirLiftPhase body`, and `hasNoCleanupBlocks body`.
-/
def checkMirLiftDagReady (body : CapturedMir) : Bool :=
  checkBorrowFreeBodyFragment .pureLoopFree body &&
    isMirLiftPhase body &&
    hasNoCleanupBlocks body

/--
Decidable loop-lifting readiness guard (`MirLoops` + `PureMirExec`): requires
`checkPureMir body`, `isMirLiftPhase body`, and `hasNoCleanupBlocks body`.
-/
def checkMirLoopLiftReady (body : CapturedMir) : Bool :=
  checkPureMir body &&
    isMirLiftPhase body &&
    hasNoCleanupBlocks body

/--
`checkMirLiftReady` and `checkMirLoopLiftReady` are extensionally identical
because `checkBorrowFreeBodyFragment .pureBoundedLoop body = checkPureMir body`.
-/
@[simp]
theorem checkMirLiftReady_eq_checkMirLoopLiftReady (body : CapturedMir) :
    checkMirLiftReady body = checkMirLoopLiftReady body := by
  unfold checkMirLiftReady checkMirLoopLiftReady
  rw [checkBorrowFreeBodyFragment_pureBoundedLoop_eq_checkPureMir]

/--
`checkMirLiftDagReady body` equals `checkMirLiftReady body && !hasCfgBackedge body`.
-/
theorem checkMirLiftDagReady_eq (body : CapturedMir) :
    checkMirLiftDagReady body = (checkMirLiftReady body && !hasCfgBackedge body) := by
  unfold checkMirLiftDagReady checkMirLiftReady
  rw [checkBorrowFreeBodyFragment_pureLoopFree_eq,
    checkBorrowFreeBodyFragment_pureBoundedLoop_eq_checkPureMir]
  cases checkPureMir body <;>
    cases hasCfgBackedge body <;>
    cases isMirLiftPhase body <;>
    cases hasNoCleanupBlocks body <;>
    rfl

theorem checkMirLiftReady_iff (body : CapturedMir) :
    checkMirLiftReady body = true ↔
      checkPureMir body = true ∧
      isMirLiftPhase body = true ∧
      hasNoCleanupBlocks body = true := by
  unfold checkMirLiftReady
  rw [checkBorrowFreeBodyFragment_pureBoundedLoop_eq_checkPureMir]
  simp only [Bool.and_eq_true, and_assoc]

theorem checkMirLiftDagReady_iff (body : CapturedMir) :
    checkMirLiftDagReady body = true ↔
      checkPureMir body = true ∧
      hasCfgBackedge body = false ∧
      isMirLiftPhase body = true ∧
      hasNoCleanupBlocks body = true := by
  unfold checkMirLiftDagReady
  rw [checkBorrowFreeBodyFragment_pureLoopFree_eq]
  simp only [Bool.and_eq_true, Bool.not_eq_true', and_assoc]

theorem checkMirLoopLiftReady_iff (body : CapturedMir) :
    checkMirLoopLiftReady body = true ↔
      checkPureMir body = true ∧
      isMirLiftPhase body = true ∧
      hasNoCleanupBlocks body = true := by
  unfold checkMirLoopLiftReady
  simp only [Bool.and_eq_true, and_assoc]

/--
Exact lattice characterization of `checkMirLiftReady` in terms of
`inferBorrowFreeMinFragment body ≤ .pureBoundedLoop`.
-/
theorem checkMirLiftReady_iff_inferBorrowFreeMinFragment (body : CapturedMir) :
    checkMirLiftReady body = true ↔
      inferBorrowFreeMinFragment body ≤ .pureBoundedLoop ∧
      isMirLiftPhase body = true ∧
      hasNoCleanupBlocks body = true := by
  rw [checkMirLiftReady_iff, inferBorrowFreeMinFragment_le_pureBoundedLoop_iff_checkPureMir]

/--
Exact lattice characterization of `checkMirLiftDagReady` in terms of
`inferBorrowFreeMinFragment body = .pureLoopFree`.
-/
theorem checkMirLiftDagReady_iff_inferBorrowFreeMinFragment (body : CapturedMir) :
    checkMirLiftDagReady body = true ↔
      inferBorrowFreeMinFragment body = .pureLoopFree ∧
      isMirLiftPhase body = true ∧
      hasNoCleanupBlocks body = true := by
  rw [checkMirLiftDagReady_iff, inferBorrowFreeMinFragment_eq_pureLoopFree_iff]
  simp only [and_assoc]

/-- Every DAG-ready body (`checkMirLiftDagReady`) is lift-ready (`checkMirLiftReady`). -/
theorem checkMirLiftReady_of_dagReady {body : CapturedMir}
    (h : checkMirLiftDagReady body = true) :
    checkMirLiftReady body = true := by
  rw [checkMirLiftDagReady_eq, Bool.and_eq_true] at h
  exact h.1

theorem checkMirLoopLiftReady_of_mirLiftReady {body : CapturedMir}
    (h : checkMirLiftReady body = true) :
    checkMirLoopLiftReady body = true := by
  rwa [← checkMirLiftReady_eq_checkMirLoopLiftReady]

theorem checkMirLiftReady_of_loopLiftReady {body : CapturedMir}
    (h : checkMirLoopLiftReady body = true) :
    checkMirLiftReady body = true := by
  rwa [checkMirLiftReady_eq_checkMirLoopLiftReady]

/--
Build `checkMirLiftReady body = true` from syntactic
`inferMinFragment body ≤ .pureBoundedLoop` plus decidable side conditions.
-/
theorem checkMirLiftReady_of_inferMinFragment_le_pureBoundedLoop
    (body : CapturedMir)
    (h_frag : inferMinFragment body ≤ .pureBoundedLoop)
    (h_no_ptr_rel : hasNoPtrRelationalAssign body = true := by decide)
    (h_phase : isMirLiftPhase body = true := by decide)
    (h_clean : hasNoCleanupBlocks body = true := by decide) :
    checkMirLiftReady body = true :=
  (checkMirLiftReady_iff body).mpr
    ⟨checkPureMir_of_inferMinFragment_le_pureBoundedLoop body h_frag h_no_ptr_rel,
     h_phase,
     h_clean⟩

/--
Build `checkMirLiftDagReady body = true` from syntactic
`inferMinFragment body = .pureLoopFree` plus decidable side conditions.
-/
theorem checkMirLiftDagReady_of_inferMinFragment_eq_pureLoopFree
    (body : CapturedMir)
    (h_frag : inferMinFragment body = .pureLoopFree)
    (h_no_ptr_rel : hasNoPtrRelationalAssign body = true := by decide)
    (h_phase : isMirLiftPhase body = true := by decide)
    (h_clean : hasNoCleanupBlocks body = true := by decide) :
    checkMirLiftDagReady body = true := by
  have h_le : inferMinFragment body ≤ .pureBoundedLoop := by
    rw [h_frag]; decide
  have h_no_be : hasCfgBackedge body = false :=
    ((inferMinFragment_eq_pureLoopFree_iff_pureStatement body).mp h_frag).2
  exact (checkMirLiftDagReady_iff body).mpr
    ⟨checkPureMir_of_inferMinFragment_le_pureBoundedLoop body h_le h_no_ptr_rel,
     h_no_be,
     h_phase,
     h_clean⟩

/-! ### Helper Premise-Extraction Lemmas -/

/-- Extract `checkPureMir body = true` from `checkMirLiftReady body = true`. -/
theorem checkPureMir_of_mirLiftReady {body : CapturedMir}
    (h : checkMirLiftReady body = true) :
    checkPureMir body = true :=
  ((checkMirLiftReady_iff body).mp h).1

/-- Extract `isMirLiftPhase body = true` from `checkMirLiftReady body = true`. -/
theorem isMirLiftPhase_of_mirLiftReady {body : CapturedMir}
    (h : checkMirLiftReady body = true) :
    isMirLiftPhase body = true :=
  ((checkMirLiftReady_iff body).mp h).2.1

/--
Extract the phase disjunction `body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized`
from `checkMirLiftReady body = true`.
-/
theorem phase_of_mirLiftReady {body : CapturedMir}
    (h : checkMirLiftReady body = true) :
    body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized :=
  (isMirLiftPhase_iff body).mp (isMirLiftPhase_of_mirLiftReady h)

/-- Extract `hasNoCleanupBlocks body = true` from `checkMirLiftReady body = true`. -/
theorem hasNoCleanupBlocks_of_mirLiftReady {body : CapturedMir}
    (h : checkMirLiftReady body = true) :
    hasNoCleanupBlocks body = true :=
  ((checkMirLiftReady_iff body).mp h).2.2

/--
Extract `bb.isCleanup = false` at any block lookup from `checkMirLiftReady body = true`.
-/
theorem isCleanup_false_of_mirLiftReady
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb) :
    bb.isCleanup = false :=
  isCleanup_false_of_hasNoCleanupBlocks (hasNoCleanupBlocks_of_mirLiftReady h) h_bb

/--
Rewrite any block lookup `get? body.basicBlocks bbIdx = some bb` into the explicit
`isCleanup := false` record shape expected by `LiftStmtsTerminator` rules.
-/
theorem lookup_cleanup_false_of_mirLiftReady
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb) :
    Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := bb.statements, terminator := bb.terminator, isCleanup := false } := by
  have h_ic := isCleanup_false_of_mirLiftReady h h_bb
  rcases bb with ⟨stmts, term, ic⟩
  dsimp only at h_ic ⊢
  subst h_ic
  exact h_bb

/--
Extract block-level syntactic purity (`isPureStatement` on every statement and
`isPureTerminator` on the terminator) from `checkMirLiftReady body = true`.
-/
theorem isPure_block_of_mirLiftReady
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb) :
    bb.statements.all (fun s => isPureStatement s.kind) = true ∧
    isPureTerminator bb.terminator.kind = true :=
  checkPureMir_block (checkPureMir_of_mirLiftReady h) h_bb

theorem isPureStatement_of_mirLiftReady
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    {stmtIdx : Nat} {stmt : Statement}
    (h : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_stmt : Trusted.Sequence.get? bb.statements stmtIdx = some stmt) :
    isPureStatement stmt.kind = true :=
  list_all_of_get? (p := fun s => isPureStatement s.kind)
    (isPure_block_of_mirLiftReady h h_bb).1 h_stmt

theorem isPureTerminator_of_mirLiftReady
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb) :
    isPureTerminator bb.terminator.kind = true :=
  (isPure_block_of_mirLiftReady h h_bb).2

theorem inferBorrowFreeMinFragment_le_of_mirLiftReady {body : CapturedMir}
    (h : checkMirLiftReady body = true) :
    inferBorrowFreeMinFragment body ≤ .pureBoundedLoop :=
  (inferBorrowFreeMinFragment_le_pureBoundedLoop_iff_checkPureMir body).mpr
    (checkPureMir_of_mirLiftReady h)

theorem inferMinFragment_le_of_mirLiftReady {body : CapturedMir}
    (h : checkMirLiftReady body = true) :
    inferMinFragment body ≤ .pureBoundedLoop :=
  MirFragment.le_trans
    (inferMinFragment_le_inferBorrowFreeMinFragment body)
    (inferBorrowFreeMinFragment_le_of_mirLiftReady h)

/-- Extract `checkPureMir body = true` from `checkMirLiftDagReady body = true`. -/
theorem checkPureMir_of_mirLiftDagReady {body : CapturedMir}
    (h : checkMirLiftDagReady body = true) :
    checkPureMir body = true :=
  ((checkMirLiftDagReady_iff body).mp h).1

/-- Extract `hasCfgBackedge body = false` from `checkMirLiftDagReady body = true`. -/
theorem hasCfgBackedge_false_of_mirLiftDagReady {body : CapturedMir}
    (h : checkMirLiftDagReady body = true) :
    hasCfgBackedge body = false :=
  ((checkMirLiftDagReady_iff body).mp h).2.1

/-- Rule out all directed CFG cycles from `checkMirLiftDagReady body = true`. -/
theorem no_cfg_cycle_of_mirLiftDagReady {body : CapturedMir}
    (h : checkMirLiftDagReady body = true) (u : BasicBlockIdx) :
    ¬ CfgPath body u u :=
  no_cfg_cycle_of_hasCfgBackedge_false (hasCfgBackedge_false_of_mirLiftDagReady h) u

/--
Every directed CFG edge `u → v` in a DAG-ready body (`checkMirLiftDagReady body = true`)
strictly increases basic-block index (`u < v`).
-/
theorem cfgEdge_lt_of_mirLiftDagReady {body : CapturedMir} {u v : BasicBlockIdx}
    (h : checkMirLiftDagReady body = true)
    (h_edge : CfgEdge body u v) :
    u < v :=
  cfgEdge_lt_of_hasCfgBackedge_false (hasCfgBackedge_false_of_mirLiftDagReady h) h_edge

/--
Every non-empty directed CFG path `u →⁺ v` in a DAG-ready body strictly increases
basic-block index (`u < v`).
-/
theorem cfgPath_lt_of_mirLiftDagReady {body : CapturedMir} {u v : BasicBlockIdx}
    (h : checkMirLiftDagReady body = true)
    (h_path : CfgPath body u v) :
    u < v :=
  cfgPath_lt_of_hasCfgBackedge_false (hasCfgBackedge_false_of_mirLiftDagReady h) h_path

/--
Every outgoing successor `succ ∈ blockTargets bb` of an in-bounds block
`Trusted.Sequence.get? body.basicBlocks bbIdx = some bb` in a DAG-ready body
strictly increases basic-block index (`bbIdx < succ`).
-/
theorem blockTarget_lt_of_mirLiftDagReady
    {body : CapturedMir} {bbIdx succ : BasicBlockIdx} {bb : BasicBlockData}
    (h : checkMirLiftDagReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_succ : succ ∈ blockTargets bb) :
    bbIdx < succ :=
  cfgEdge_lt_of_mirLiftDagReady h ⟨bb, h_bb, h_succ⟩

/-- Extract `isMirLiftPhase body = true` from `checkMirLiftDagReady body = true`. -/
theorem isMirLiftPhase_of_mirLiftDagReady {body : CapturedMir}
    (h : checkMirLiftDagReady body = true) :
    isMirLiftPhase body = true :=
  ((checkMirLiftDagReady_iff body).mp h).2.2.1

/-- Extract the runtime phase disjunction from `checkMirLiftDagReady body = true`. -/
theorem phase_of_mirLiftDagReady {body : CapturedMir}
    (h : checkMirLiftDagReady body = true) :
    body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized :=
  phase_of_mirLiftReady (checkMirLiftReady_of_dagReady h)

/-- Extract `hasNoCleanupBlocks body = true` from `checkMirLiftDagReady body = true`. -/
theorem hasNoCleanupBlocks_of_mirLiftDagReady {body : CapturedMir}
    (h : checkMirLiftDagReady body = true) :
    hasNoCleanupBlocks body = true :=
  ((checkMirLiftDagReady_iff body).mp h).2.2.2

/-- Extract `bb.isCleanup = false` at any block lookup from `checkMirLiftDagReady body = true`. -/
theorem isCleanup_false_of_mirLiftDagReady
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h : checkMirLiftDagReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb) :
    bb.isCleanup = false :=
  isCleanup_false_of_mirLiftReady (checkMirLiftReady_of_dagReady h) h_bb

theorem lookup_cleanup_false_of_mirLiftDagReady
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h : checkMirLiftDagReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb) :
    Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := bb.statements, terminator := bb.terminator, isCleanup := false } :=
  lookup_cleanup_false_of_mirLiftReady (checkMirLiftReady_of_dagReady h) h_bb

theorem isPure_block_of_mirLiftDagReady
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h : checkMirLiftDagReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb) :
    bb.statements.all (fun s => isPureStatement s.kind) = true ∧
    isPureTerminator bb.terminator.kind = true :=
  isPure_block_of_mirLiftReady (checkMirLiftReady_of_dagReady h) h_bb

theorem inferBorrowFreeMinFragment_eq_of_mirLiftDagReady {body : CapturedMir}
    (h : checkMirLiftDagReady body = true) :
    inferBorrowFreeMinFragment body = .pureLoopFree :=
  (inferBorrowFreeMinFragment_eq_pureLoopFree_iff body).mpr
    ⟨checkPureMir_of_mirLiftDagReady h, hasCfgBackedge_false_of_mirLiftDagReady h⟩

theorem inferMinFragment_eq_of_mirLiftDagReady {body : CapturedMir}
    (h : checkMirLiftDagReady body = true) :
    inferMinFragment body = .pureLoopFree := by
  have h_le : inferMinFragment body ≤ .pureLoopFree := by
    rw [← inferBorrowFreeMinFragment_eq_of_mirLiftDagReady h]
    exact inferMinFragment_le_inferBorrowFreeMinFragment body
  exact MirFragment.le_antisymm h_le (MirFragment.bot_le _)

theorem checkPureMir_of_mirLoopLiftReady {body : CapturedMir}
    (h : checkMirLoopLiftReady body = true) :
    checkPureMir body = true :=
  ((checkMirLoopLiftReady_iff body).mp h).1

theorem isMirLiftPhase_of_mirLoopLiftReady {body : CapturedMir}
    (h : checkMirLoopLiftReady body = true) :
    isMirLiftPhase body = true :=
  ((checkMirLoopLiftReady_iff body).mp h).2.1

theorem phase_of_mirLoopLiftReady {body : CapturedMir}
    (h : checkMirLoopLiftReady body = true) :
    body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized :=
  (isMirLiftPhase_iff body).mp (isMirLiftPhase_of_mirLoopLiftReady h)

theorem hasNoCleanupBlocks_of_mirLoopLiftReady {body : CapturedMir}
    (h : checkMirLoopLiftReady body = true) :
    hasNoCleanupBlocks body = true :=
  ((checkMirLoopLiftReady_iff body).mp h).2.2

theorem isCleanup_false_of_mirLoopLiftReady
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h : checkMirLoopLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb) :
    bb.isCleanup = false :=
  isCleanup_false_of_hasNoCleanupBlocks (hasNoCleanupBlocks_of_mirLoopLiftReady h) h_bb

theorem lookup_cleanup_false_of_mirLoopLiftReady
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h : checkMirLoopLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb) :
    Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := bb.statements, terminator := bb.terminator, isCleanup := false } :=
  lookup_cleanup_false_of_mirLiftReady (checkMirLiftReady_of_loopLiftReady h) h_bb

/-! ### Lifting, Verification & Loop Convergence Bridges -/

/--
Fragment-guarded companion to `lift_PureMirConverges`: discharges `PureMirConverges`
from `checkMirLiftReady body = true` and a lifted entry block `LiftBlock`.
-/
theorem lift_PureMirConverges_of_mirLiftReady
    {body : CapturedMir} {args : List Value} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftReady body = true)
    (h_lift : LiftBlock body 0 (initPureEnv body args) post fuel) :
    PureMirConverges body (initPureState body args) post :=
  lift_PureMirConverges (checkPureMir_of_mirLiftReady h_ready) h_lift

/--
DAG-guarded companion to `lift_PureMirConverges`: discharges `PureMirConverges`
from `checkMirLiftDagReady body = true` and a lifted entry block `LiftBlock`.
-/
theorem lift_PureMirConverges_of_mirLiftDagReady
    {body : CapturedMir} {args : List Value} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftDagReady body = true)
    (h_lift : LiftBlock body 0 (initPureEnv body args) post fuel) :
    PureMirConverges body (initPureState body args) post :=
  lift_PureMirConverges (checkPureMir_of_mirLiftDagReady h_ready) h_lift

theorem lift_PureMirConverges_of_borrowFreeFragment
    {body : CapturedMir} {f : MirFragment} {args : List Value}
    {post : Value → Prop} {fuel : Nat}
    (h_frag : checkBorrowFreeBodyFragment f body = true)
    (h_lift : LiftBlock body 0 (initPureEnv body args) post fuel)
    (h_le : f ≤ .pureBoundedLoop := by decide) :
    PureMirConverges body (initPureState body args) post :=
  lift_PureMirConverges
    (checkPureMir_of_borrowFreeFragment_le_pureBoundedLoop h_frag h_le)
    h_lift

theorem lift_PureMirConverges_of_inferMinFragment_le_pureBoundedLoop
    {body : CapturedMir} {args : List Value} {post : Value → Prop} {fuel : Nat}
    (h_frag : inferMinFragment body ≤ .pureBoundedLoop)
    (h_lift : LiftBlock body 0 (initPureEnv body args) post fuel)
    (h_no_ptr_rel : hasNoPtrRelationalAssign body = true := by decide) :
    PureMirConverges body (initPureState body args) post :=
  lift_PureMirConverges
    (checkPureMir_of_inferMinFragment_le_pureBoundedLoop body h_frag h_no_ptr_rel)
    h_lift

/--
Partial-correctness (`mirSafePost`) block-lifting judgment over alias-erased
`PureEnv`: forbids UB while permitting clean panics/aborts, and guarantees `post`
on any normal return within `fuel` steps.
-/
def LiftSafeBlock (body : CapturedMir) (bbIdx : BasicBlockIdx) (env : PureEnv)
    (post : Value → Prop) (fuel : Nat) : Prop :=
  wpPureMirSafeExec fuel body { bb := bbIdx, stmtIdx := 0, env := env } post

/-- Every panic-forbidding `LiftBlock` proof implies `LiftSafeBlock`. -/
theorem LiftSafeBlock.of_liftBlock
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {env : PureEnv}
    {post : Value → Prop} {fuel : Nat}
    (h : LiftBlock body bbIdx env post fuel) :
    LiftSafeBlock body bbIdx env post fuel := by
  unfold LiftBlock wpPureMirExec at h
  unfold LiftSafeBlock wpPureMirSafeExec
  exact wpMirExecSym_mono_post (fun _ h_out => mirNormalPost_imp_mirSafePost h_out) h

theorem liftSafe_PureMirSafeConverges_of_mirLiftReady
    {body : CapturedMir} {args : List Value} {post : Value → Prop} {fuel : Nat}
    (_h_ready : checkMirLiftReady body = true)
    (h_lift : LiftSafeBlock body 0 (initPureEnv body args) post fuel) :
    PureMirSafeConverges body (initPureState body args) post :=
  ⟨fuel, h_lift⟩

theorem liftSafe_PureMirSafeConverges_of_mirLiftDagReady
    {body : CapturedMir} {args : List Value} {post : Value → Prop} {fuel : Nat}
    (_h_ready : checkMirLiftDagReady body = true)
    (h_lift : LiftSafeBlock body 0 (initPureEnv body args) post fuel) :
    PureMirSafeConverges body (initPureState body args) post :=
  ⟨fuel, h_lift⟩

private def maxRankBoundAux (rank : Nat → Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => max (maxRankBoundAux rank k) (rank k + 1)

private theorem rank_lt_maxRankBoundAux (rank : Nat → Nat) :
    ∀ (n i : Nat), i < n → rank i < maxRankBoundAux rank n
  | 0, _, hi => nomatch hi
  | k + 1, i, hi => by
    dsimp only [maxRankBoundAux]
    if h_eq : i = k then
      subst h_eq
      omega
    else
      have h_lt : rank i < maxRankBoundAux rank k :=
        rank_lt_maxRankBoundAux rank k i (by omega)
      omega

/--
**General Rank-Certificate DAG Block Induction (`dagBlockInduct_of_hasRankViolation_false`)**:
Along any violation-free rank certificate `hasRankViolation rank body = false`,
every in-range edge `bbIdx → succ` strictly increases `rank` and strictly
decreases `maxRankBoundAux rank body.basicBlocks.length - rank bbIdx` (with
out-of-bounds targets given measure `0`). Proves `Goal 0 env₀` for any
`Goal : BasicBlockIdx → PureEnv → Prop` from per-block `CfgEdge` stepping
without requiring any user-supplied loop measure or in-bounds invariant side
condition.
-/
theorem dagBlockInduct_of_hasRankViolation_false
    {body : CapturedMir} {rank : Nat → Nat} {env₀ : PureEnv}
    (h_no : hasRankViolation rank body = false)
    (BlockInv Goal : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' → Goal succ env') →
      Goal bbIdx env) :
    Goal 0 env₀ := by
  let n := body.basicBlocks.length
  let M := maxRankBoundAux rank n
  let mu : BasicBlockIdx → Nat := fun idx =>
    if idx < n then M - rank idx else 0
  have h_gen :
      ∀ d bbIdx env,
        mu bbIdx = d →
        BlockInv bbIdx env →
        Goal bbIdx env := by
    apply nat_strong_induction
      (fun d => ∀ bbIdx env, mu bbIdx = d → BlockInv bbIdx env → Goal bbIdx env)
    intro d ih bbIdx env h_eq h_inv
    refine h_step bbIdx env h_inv (fun succ env' h_edge h_succ_inv => ?_)
    have h_u_lt : bbIdx < n := lt_length_of_cfgEdge h_edge
    have h_ru_lt : rank bbIdx < M := rank_lt_maxRankBoundAux rank n bbIdx h_u_lt
    have h_mu_lt : mu succ < d := by
      dsimp only [mu] at h_eq ⊢
      simp only [h_u_lt, ↓reduceIte] at h_eq
      if h_v_lt : succ < n then
        have h_rv_lt : rank succ < M := rank_lt_maxRankBoundAux rank n succ h_v_lt
        have h_edge_rk : rank bbIdx < rank succ :=
          cfgEdge_rank_lt_of_hasRankViolation_false h_no h_edge h_v_lt
        simp only [h_v_lt, ↓reduceIte]
        omega
      else
        simp only [h_v_lt, ↓reduceIte]
        omega
    exact ih (mu succ) h_mu_lt succ env' rfl h_succ_inv
  exact h_gen (mu 0) 0 env₀ rfl h_init

/--
Index-order specialization of `dagBlockInduct_of_hasRankViolation_false` under
`hasCfgBackedge body = false` (`rank = id`).
-/
theorem dagBlockInduct_of_hasCfgBackedge_false
    {body : CapturedMir} {env₀ : PureEnv}
    (h_no_be : hasCfgBackedge body = false)
    (BlockInv Goal : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' → Goal succ env') →
      Goal bbIdx env) :
    Goal 0 env₀ :=
  dagBlockInduct_of_hasRankViolation_false
    ((hasRankViolation_id_eq_hasCfgBackedge body).trans h_no_be)
    BlockInv Goal h_init h_step

/--
General DAG specialization of `dagBlockInduct_of_hasRankViolation_false` under
`isCfgDag body = true` (`rank = dagRank body`), handling acyclic MIR bodies with
non-topological block numbering (such as `rustc`'s shared-return blocks).
-/
theorem dagBlockInduct_of_isCfgDag
    {body : CapturedMir} {env₀ : PureEnv}
    (h_dag : isCfgDag body = true)
    (BlockInv Goal : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' → Goal succ env') →
      Goal bbIdx env) :
    Goal 0 env₀ :=
  dagBlockInduct_of_hasRankViolation_false
    (by simpa [isCfgDag] using h_dag)
    BlockInv Goal h_init h_step

/--
Rank-certificate `LiftBlock` DAG induction (`hasRankViolation rank body = false`):
eliminates global path-fuel bounds and loop ranking functions (each block steps
locally and composes its step count with the existential fuel of its `CfgEdge`
successors).
-/
theorem liftBlock_of_hasRankViolation_false_induct
    {body : CapturedMir} {rank : Nat → Nat} {env₀ : PureEnv} {post : Value → Prop}
    (h_no : hasRankViolation rank body = false)
    (BlockInv : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' →
        ∃ fuel, LiftBlock body succ env' post fuel) →
      ∃ fuel, LiftBlock body bbIdx env post fuel) :
    ∃ fuel, LiftBlock body 0 env₀ post fuel :=
  dagBlockInduct_of_hasRankViolation_false h_no BlockInv
    (fun bbIdx env => ∃ fuel, LiftBlock body bbIdx env post fuel)
    h_init h_step

/--
CFG-only `LiftBlock` DAG induction (`hasCfgBackedge body = false`): lifts any
multi-block index-order DAG from block `0` without global path-fuel bounds or
user-supplied ranking functions (per-block fuel still composes existentially
with successor fuel).
-/
theorem liftBlock_of_hasCfgBackedge_false_induct
    {body : CapturedMir} {env₀ : PureEnv} {post : Value → Prop}
    (h_no_be : hasCfgBackedge body = false)
    (BlockInv : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' →
        ∃ fuel, LiftBlock body succ env' post fuel) →
      ∃ fuel, LiftBlock body bbIdx env post fuel) :
    ∃ fuel, LiftBlock body 0 env₀ post fuel :=
  dagBlockInduct_of_hasCfgBackedge_false h_no_be BlockInv
    (fun bbIdx env => ∃ fuel, LiftBlock body bbIdx env post fuel)
    h_init h_step

/--
General-DAG `LiftBlock` induction (`isCfgDag body = true`): lifts any acyclic
CFG (including non-topologically numbered `rustc` MIR with shared return blocks)
from block `0` using `dagRank body`, without global path-fuel bounds or a
user-supplied ranking function.
-/
theorem liftBlock_of_isCfgDag_induct
    {body : CapturedMir} {env₀ : PureEnv} {post : Value → Prop}
    (h_dag : isCfgDag body = true)
    (BlockInv : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' →
        ∃ fuel, LiftBlock body succ env' post fuel) →
      ∃ fuel, LiftBlock body bbIdx env post fuel) :
    ∃ fuel, LiftBlock body 0 env₀ post fuel :=
  dagBlockInduct_of_isCfgDag h_dag BlockInv
    (fun bbIdx env => ∃ fuel, LiftBlock body bbIdx env post fuel)
    h_init h_step

/--
**Backwards Topological DAG Lifting (`liftBlock_of_mirLiftDagReady_induct`)**:
Specialization of `liftBlock_of_hasCfgBackedge_false_induct` to
`checkMirLiftDagReady body = true`. Eliminates global path-fuel bounds and
user-supplied ranking functions when lifting multi-block branching DAGs from
entry block `0` (while each single block still composes its local step count
with the existential fuel of its outgoing `CfgEdge` successors).
-/
theorem liftBlock_of_mirLiftDagReady_induct
    {body : CapturedMir} {env₀ : PureEnv} {post : Value → Prop}
    (h_ready : checkMirLiftDagReady body = true)
    (BlockInv : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' →
        ∃ fuel, LiftBlock body succ env' post fuel) →
      ∃ fuel, LiftBlock body bbIdx env post fuel) :
    ∃ fuel, LiftBlock body 0 env₀ post fuel :=
  liftBlock_of_hasCfgBackedge_false_induct
    (hasCfgBackedge_false_of_mirLiftDagReady h_ready)
    BlockInv h_init h_step

theorem liftSafeBlock_of_hasRankViolation_false_induct
    {body : CapturedMir} {rank : Nat → Nat} {env₀ : PureEnv} {post : Value → Prop}
    (h_no : hasRankViolation rank body = false)
    (BlockInv : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' →
        ∃ fuel, LiftSafeBlock body succ env' post fuel) →
      ∃ fuel, LiftSafeBlock body bbIdx env post fuel) :
    ∃ fuel, LiftSafeBlock body 0 env₀ post fuel :=
  dagBlockInduct_of_hasRankViolation_false h_no BlockInv
    (fun bbIdx env => ∃ fuel, LiftSafeBlock body bbIdx env post fuel)
    h_init h_step

theorem liftSafeBlock_of_hasCfgBackedge_false_induct
    {body : CapturedMir} {env₀ : PureEnv} {post : Value → Prop}
    (h_no_be : hasCfgBackedge body = false)
    (BlockInv : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' →
        ∃ fuel, LiftSafeBlock body succ env' post fuel) →
      ∃ fuel, LiftSafeBlock body bbIdx env post fuel) :
    ∃ fuel, LiftSafeBlock body 0 env₀ post fuel :=
  dagBlockInduct_of_hasCfgBackedge_false h_no_be BlockInv
    (fun bbIdx env => ∃ fuel, LiftSafeBlock body bbIdx env post fuel)
    h_init h_step

theorem liftSafeBlock_of_isCfgDag_induct
    {body : CapturedMir} {env₀ : PureEnv} {post : Value → Prop}
    (h_dag : isCfgDag body = true)
    (BlockInv : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' →
        ∃ fuel, LiftSafeBlock body succ env' post fuel) →
      ∃ fuel, LiftSafeBlock body bbIdx env post fuel) :
    ∃ fuel, LiftSafeBlock body 0 env₀ post fuel :=
  dagBlockInduct_of_isCfgDag h_dag BlockInv
    (fun bbIdx env => ∃ fuel, LiftSafeBlock body bbIdx env post fuel)
    h_init h_step

theorem liftSafeBlock_of_mirLiftDagReady_induct
    {body : CapturedMir} {env₀ : PureEnv} {post : Value → Prop}
    (h_ready : checkMirLiftDagReady body = true)
    (BlockInv : BasicBlockIdx → PureEnv → Prop)
    (h_init : BlockInv 0 env₀)
    (h_step : ∀ bbIdx env, BlockInv bbIdx env →
      (∀ succ env', CfgEdge body bbIdx succ → BlockInv succ env' →
        ∃ fuel, LiftSafeBlock body succ env' post fuel) →
      ∃ fuel, LiftSafeBlock body bbIdx env post fuel) :
    ∃ fuel, LiftSafeBlock body 0 env₀ post fuel :=
  liftSafeBlock_of_hasCfgBackedge_false_induct
    (hasCfgBackedge_false_of_mirLiftDagReady h_ready)
    BlockInv h_init h_step

/--
Readiness-discharged `cons_eval` step rule: extracts `h_phase` and
`bb.isCleanup = false` directly from `checkMirLiftReady body = true`.
-/
theorem LiftStmtsTerminator.cons_eval_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {stmt : Statement} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_get : Trusted.Sequence.get? bb.statements stmtIdx = some stmt)
    (h_eval : MirLiftCore.evalPureStmt body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + 1) env' bb.statements bb.terminator post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + 1) :=
  LiftStmtsTerminator.cons_eval
    (lookup_cleanup_false_of_mirLiftReady h_ready h_bb)
    (phase_of_mirLiftReady h_ready)
    h_get
    h_eval
    h_next

/--
Readiness-discharged `cons` (`LiftStmt`) step rule: extracts `h_phase` and
`bb.isCleanup = false` directly from `checkMirLiftReady body = true`.
-/
theorem LiftStmtsTerminator.cons_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {stmt : Statement} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_get : Trusted.Sequence.get? bb.statements stmtIdx = some stmt)
    (h_stmt : LiftStmt body bbIdx stmtIdx env stmt (fun e => e = env'))
    (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + 1) env' bb.statements bb.terminator post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + 1) :=
  LiftStmtsTerminator.cons
    (lookup_cleanup_false_of_mirLiftReady h_ready h_bb)
    (phase_of_mirLiftReady h_ready)
    h_get
    h_stmt
    h_next

/--
Readiness-discharged `cons_eval_norm` step rule: extracts `h_phase` and
`bb.isCleanup = false` directly from `checkMirLiftReady body = true`.
-/
theorem LiftStmtsTerminator.cons_eval_norm_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {stmt : Statement} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_get : Trusted.Sequence.get? bb.statements stmtIdx = some stmt)
    (h_eval : evalPureStmtNorm body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + 1) env' bb.statements bb.terminator post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + 1) :=
  LiftStmtsTerminator.cons_eval_norm
    (lookup_cleanup_false_of_mirLiftReady h_ready h_bb)
    (phase_of_mirLiftReady h_ready)
    h_get
    h_eval
    h_next

/--
Readiness-discharged `eval_n` multi-statement step rule: extracts `h_phase` and
`bb.isCleanup = false` directly from `checkMirLiftReady body = true`.
-/
theorem LiftStmtsTerminator.eval_n_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {n stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsN body bbIdx bb.statements n stmtIdx env = some env')
    (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + n) env' bb.statements bb.terminator post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + n) :=
  LiftStmtsTerminator.eval_n
    (lookup_cleanup_false_of_mirLiftReady h_ready h_bb)
    (phase_of_mirLiftReady h_ready)
    h_eval
    h_next

/--
Readiness-discharged `eval_rest` step rule: extracts `h_phase` and
`bb.isCleanup = false` directly from `checkMirLiftReady body = true`.
-/
theorem LiftStmtsTerminator.eval_rest_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsN body bbIdx bb.statements
      (List.length bb.statements - stmtIdx) stmtIdx env = some env')
    (h_next : LiftStmtsTerminator body bbIdx
      (stmtIdx + (List.length bb.statements - stmtIdx))
      env' bb.statements bb.terminator post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post
      (fuel + (List.length bb.statements - stmtIdx)) :=
  LiftStmtsTerminator.eval_rest
    (lookup_cleanup_false_of_mirLiftReady h_ready h_bb)
    (phase_of_mirLiftReady h_ready)
    h_eval
    h_next

/--
Readiness-discharged `term_return` rule: extracts `h_phase` and
`bb.isCleanup = false` directly from `checkMirLiftReady body = true`.
-/
theorem LiftStmtsTerminator.term_return_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {bb : BasicBlockData} {span : String} {post : Value → Prop} {val : Value}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .return_, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_ret : Trusted.Sequence.get? env 0 = some (.init val))
    (h_post : post val) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post 1 := by
  have h_bb' := lookup_cleanup_false_of_mirLiftReady h_ready h_bb
  rw [h_term] at h_bb' ⊢
  exact LiftStmtsTerminator.term_return h_bb' (phase_of_mirLiftReady h_ready) h_end h_ret h_post

/--
Readiness-discharged `term_goto` rule: extracts `h_phase` and
`bb.isCleanup = false` directly from `checkMirLiftReady body = true`.
-/
theorem LiftStmtsTerminator.term_goto_ready {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {bb : BasicBlockData} {span : String} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .goto target, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_lift : LiftBlock body target env post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + 1) := by
  have h_bb' := lookup_cleanup_false_of_mirLiftReady h_ready h_bb
  rw [h_term] at h_bb' ⊢
  exact LiftStmtsTerminator.term_goto h_bb' (phase_of_mirLiftReady h_ready) h_end h_lift

/--
Readiness-discharged `term_switchInt` rule: extracts `h_phase` and
`bb.isCleanup = false` directly from `checkMirLiftReady body = true`.
-/
theorem LiftStmtsTerminator.term_switchInt_ready {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {discr : Operand} {targets : SwitchTargets}
    {span : String} {post : Value → Prop} {fuel : Nat} {sc : ScalarInt}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .switchInt discr targets, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_eval : MirLiftCore.evalPureOperand body env discr = .ok (.scalar sc) env')
    (h_target : target = lookupSwitchTarget sc.bits targets.branches targets.otherwise)
    (h_next : LiftBlock body target env' post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + 1) := by
  have h_bb' := lookup_cleanup_false_of_mirLiftReady h_ready h_bb
  rw [h_term] at h_bb' ⊢
  exact LiftStmtsTerminator.term_switchInt h_bb' (phase_of_mirLiftReady h_ready)
    h_end h_eval h_target h_next

/--
Readiness-discharged `term_assert` rule: extracts `h_phase` and
`bb.isCleanup = false` directly from `checkMirLiftReady body = true`.
-/
theorem LiftStmtsTerminator.term_assert_ready {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {cond : Operand} {expected : Bool}
    {unwind : UnwindAction} {span : String} {post : Value → Prop}
    {fuel : Nat} {sc : ScalarInt}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .assert cond expected target unwind, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_eval : MirLiftCore.evalPureOperand body env cond = .ok (.scalar sc) env')
    (h_cond : sc.bits = (match expected with | true => 1 | false => 0))
    (h_next : LiftBlock body target env' post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + 1) := by
  have h_bb' := lookup_cleanup_false_of_mirLiftReady h_ready h_bb
  rw [h_term] at h_bb' ⊢
  exact LiftStmtsTerminator.term_assert h_bb' (phase_of_mirLiftReady h_ready)
    h_end h_eval (by cases expected <;> simpa using h_cond) h_next

/--
Readiness-discharged `term_drop` rule: extracts `h_phase` and
`bb.isCleanup = false` directly from `checkMirLiftReady body = true`.
-/
theorem LiftStmtsTerminator.term_drop_ready {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {place : Place} {unwind : UnwindAction}
    {span : String} {post : Value → Prop} {fuel : Nat} {slot : LocalSlot}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .drop place target unwind, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_get : Trusted.Sequence.get? env place.local_ = some slot)
    (h_not_dead : slot ≠ .dead)
    (h_proj : place.projection = [])
    (h_set : Trusted.Sequence.set? env place.local_ .uninit = some env')
    (h_next : LiftBlock body target env' post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + 1) := by
  have h_bb' := lookup_cleanup_false_of_mirLiftReady h_ready h_bb
  rw [h_term] at h_bb' ⊢
  exact LiftStmtsTerminator.term_drop h_bb' (phase_of_mirLiftReady h_ready)
    h_end h_get h_not_dead h_proj h_set h_next

/--
Stateless panic-forbidding verification gate bridge from
`checkMirLiftReady c.body = true` and `LiftBlock`.
-/
theorem verifyMirNoPanic_of_mirLiftReady
    (c : Claim)
    (h_ready : checkMirLiftReady c.body = true)
    (h_lift : ∀ args, c.pre args →
      ∃ fuel, LiftBlock c.body 0 (initPureEnv c.body args) (c.post args) fuel) :
    VerificationResult c :=
  verifyMirNoPanic_of_pureExec c
    (checkPureMir_of_mirLiftReady h_ready)
    (fun args h_pre =>
      let ⟨_, hf⟩ := h_lift args h_pre
      lift_PureMirConverges_of_mirLiftReady h_ready hf)

/--
Uniform-fuel specialization of `verifyMirNoPanic_of_mirLiftReady`.
-/
theorem verifyMirNoPanic_of_mirLiftReady_fuel
    (c : Claim) (fuel : Nat)
    (h_ready : checkMirLiftReady c.body = true)
    (h_lift : ∀ args, c.pre args →
      LiftBlock c.body 0 (initPureEnv c.body args) (c.post args) fuel) :
    VerificationResult c :=
  verifyMirNoPanic_of_mirLiftReady c h_ready (fun args hp => ⟨fuel, h_lift args hp⟩)

/--
Stateless partial-correctness verification gate bridge from
`checkMirLiftReady c.body = true` and `PureMirSafeConverges`.
-/
theorem verifyMirSafe_of_mirLiftReady
    (c : Claim)
    (h_ready : checkMirLiftReady c.body = true)
    (h_exec : ∀ args, c.pre args →
      PureMirSafeConverges c.body (initPureState c.body args) (c.post args)) :
    VerificationResult c :=
  verifyMirSafe_of_pureExec c
    (checkPureMir_of_mirLiftReady h_ready)
    h_exec

/--
Stateless panic-forbidding verification gate bridge for DAG-ready pure MIR
(`checkMirLiftDagReady c.body = true`).
-/
theorem verifyMirNoPanic_of_mirLiftDagReady
    (c : Claim)
    (h_ready : checkMirLiftDagReady c.body = true)
    (h_lift : ∀ args, c.pre args →
      ∃ fuel, LiftBlock c.body 0 (initPureEnv c.body args) (c.post args) fuel) :
    VerificationResult c :=
  verifyMirNoPanic_of_mirLiftReady c
    (checkMirLiftReady_of_dagReady h_ready)
    h_lift

/--
Uniform-fuel specialization of `verifyMirNoPanic_of_mirLiftDagReady` for static
DAG path bounds.
-/
theorem verifyMirNoPanic_of_mirLiftDagReady_fuel
    (c : Claim) (fuel : Nat)
    (h_ready : checkMirLiftDagReady c.body = true)
    (h_lift : ∀ args, c.pre args →
      LiftBlock c.body 0 (initPureEnv c.body args) (c.post args) fuel) :
    VerificationResult c :=
  verifyMirNoPanic_of_mirLiftDagReady c h_ready (fun args hp => ⟨fuel, h_lift args hp⟩)

/--
Backwards-topological DAG induction gate (`verifyMirNoPanic_of_mirLiftDagReady_induct`):
discharges `VerificationResult c` for any `checkMirLiftDagReady c.body = true`
body by stepping each `BlockInv` block to its outgoing `CfgEdge` successors,
removing any global path-fuel bound or user-supplied loop ranking function
(each block composes its local step fuel with its successor's existential fuel).
-/
theorem verifyMirNoPanic_of_mirLiftDagReady_induct
    (c : Claim)
    (h_ready : checkMirLiftDagReady c.body = true)
    (BlockInv : List Value → BasicBlockIdx → PureEnv → Prop)
    (h_init : ∀ args, c.pre args → BlockInv args 0 (initPureEnv c.body args))
    (h_step : ∀ args, c.pre args → ∀ bbIdx env, BlockInv args bbIdx env →
      (∀ succ env', CfgEdge c.body bbIdx succ → BlockInv args succ env' →
        ∃ fuel, LiftBlock c.body succ env' (c.post args) fuel) →
      ∃ fuel, LiftBlock c.body bbIdx env (c.post args) fuel) :
    VerificationResult c :=
  verifyMirNoPanic_of_mirLiftDagReady c h_ready (fun args h_pre =>
    liftBlock_of_mirLiftDagReady_induct h_ready (BlockInv args)
      (h_init args h_pre) (h_step args h_pre))

/--
General-DAG induction gate (`verifyMirNoPanic_of_isCfgDag_mirLiftReady_induct`):
discharges `VerificationResult c` for any `checkMirLiftReady c.body = true` body
certified acyclic by `isCfgDag c.body = true` (including non-topological `rustc`
MIR with shared return blocks), removing global path-fuel bounds and user-supplied
ranking functions.
-/
theorem verifyMirNoPanic_of_isCfgDag_mirLiftReady_induct
    (c : Claim)
    (h_ready : checkMirLiftReady c.body = true)
    (BlockInv : List Value → BasicBlockIdx → PureEnv → Prop)
    (h_init : ∀ args, c.pre args → BlockInv args 0 (initPureEnv c.body args))
    (h_step : ∀ args, c.pre args → ∀ bbIdx env, BlockInv args bbIdx env →
      (∀ succ env', CfgEdge c.body bbIdx succ → BlockInv args succ env' →
        ∃ fuel, LiftBlock c.body succ env' (c.post args) fuel) →
      ∃ fuel, LiftBlock c.body bbIdx env (c.post args) fuel)
    (h_dag : isCfgDag c.body = true := by decide) :
    VerificationResult c :=
  verifyMirNoPanic_of_mirLiftReady c h_ready (fun args h_pre =>
    liftBlock_of_isCfgDag_induct h_dag (BlockInv args)
      (h_init args h_pre) (h_step args h_pre))

theorem verifyMirSafe_of_mirLiftDagReady
    (c : Claim)
    (h_ready : checkMirLiftDagReady c.body = true)
    (h_exec : ∀ args, c.pre args →
      PureMirSafeConverges c.body (initPureState c.body args) (c.post args)) :
    VerificationResult c :=
  verifyMirSafe_of_mirLiftReady c
    (checkMirLiftReady_of_dagReady h_ready)
    h_exec

/--
Partial-correctness (`mirSafePost`) backwards-topological DAG induction gate
(`verifyMirSafe_of_mirLiftDagReady_induct`) over `LiftSafeBlock`, removing
global path-fuel bounds and loop ranking functions while permitting clean panics.
-/
theorem verifyMirSafe_of_mirLiftDagReady_induct
    (c : Claim)
    (h_ready : checkMirLiftDagReady c.body = true)
    (BlockInv : List Value → BasicBlockIdx → PureEnv → Prop)
    (h_init : ∀ args, c.pre args → BlockInv args 0 (initPureEnv c.body args))
    (h_step : ∀ args, c.pre args → ∀ bbIdx env, BlockInv args bbIdx env →
      (∀ succ env', CfgEdge c.body bbIdx succ → BlockInv args succ env' →
        ∃ fuel, LiftSafeBlock c.body succ env' (c.post args) fuel) →
      ∃ fuel, LiftSafeBlock c.body bbIdx env (c.post args) fuel) :
    VerificationResult c :=
  verifyMirSafe_of_mirLiftDagReady c h_ready (fun args h_pre =>
    let ⟨_, hf⟩ :=
      liftSafeBlock_of_mirLiftDagReady_induct h_ready (BlockInv args)
        (h_init args h_pre) (h_step args h_pre)
    liftSafe_PureMirSafeConverges_of_mirLiftDagReady h_ready hf)

theorem verifyStatefulMirNoPanic_of_mirLiftReady
    (c : StatefulClaim)
    (h_ready : checkMirLiftReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_lift : ∀ args mem, c.pre args mem →
      ∃ fuel, LiftBlock c.body 0 (initPureEnv c.body args)
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)
        fuel) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_pureExec c
    (checkPureMir_of_mirLiftReady h_ready)
    h_root
    (fun args mem hp =>
      let ⟨_, hf⟩ := h_lift args mem hp
      lift_PureMirConverges_of_mirLiftReady h_ready hf)

theorem verifyStatefulMirSafe_of_mirLiftReady
    (c : StatefulClaim)
    (h_ready : checkMirLiftReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_exec : ∀ args mem, c.pre args mem →
      PureMirSafeConverges c.body (initPureState c.body args)
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)) :
    StatefulVerificationResult c :=
  verifyStatefulMirSafe_of_pureExec c
    (checkPureMir_of_mirLiftReady h_ready)
    h_root
    h_exec

theorem verifyStatefulMirNoPanic_of_mirLiftDagReady
    (c : StatefulClaim)
    (h_ready : checkMirLiftDagReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_lift : ∀ args mem, c.pre args mem →
      ∃ fuel, LiftBlock c.body 0 (initPureEnv c.body args)
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)
        fuel) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_mirLiftReady c
    (checkMirLiftReady_of_dagReady h_ready)
    h_root
    h_lift

/--
Stateful panic-forbidding backwards-topological DAG induction gate
(`verifyStatefulMirNoPanic_of_mirLiftDagReady_induct`), removing global path-fuel
bounds and user-supplied ranking functions while framing initial memory.
-/
theorem verifyStatefulMirNoPanic_of_mirLiftDagReady_induct
    (c : StatefulClaim)
    (h_ready : checkMirLiftDagReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (BlockInv : List Value → Memory → BasicBlockIdx → PureEnv → Prop)
    (h_init : ∀ args mem, c.pre args mem →
      BlockInv args mem 0 (initPureEnv c.body args))
    (h_step : ∀ args mem, c.pre args mem → ∀ bbIdx env, BlockInv args mem bbIdx env →
      (∀ succ env', CfgEdge c.body bbIdx succ → BlockInv args mem succ env' →
        ∃ fuel, LiftBlock c.body succ env'
          (fun retVal =>
            c.post args mem retVal
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                c.body args mem c.callees).memory)
          fuel) →
      ∃ fuel, LiftBlock c.body bbIdx env
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)
        fuel) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_mirLiftDagReady c h_ready h_root (fun args mem hp =>
    liftBlock_of_mirLiftDagReady_induct h_ready (BlockInv args mem)
      (h_init args mem hp) (h_step args mem hp))

theorem verifyStatefulMirSafe_of_mirLiftDagReady
    (c : StatefulClaim)
    (h_ready : checkMirLiftDagReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_exec : ∀ args mem, c.pre args mem →
      PureMirSafeConverges c.body (initPureState c.body args)
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)) :
    StatefulVerificationResult c :=
  verifyStatefulMirSafe_of_mirLiftReady c
    (checkMirLiftReady_of_dagReady h_ready)
    h_root
    h_exec

/--
Stateful partial-correctness (`mirSafePost`) backwards-topological DAG induction
gate (`verifyStatefulMirSafe_of_mirLiftDagReady_induct`) over `LiftSafeBlock`.
-/
theorem verifyStatefulMirSafe_of_mirLiftDagReady_induct
    (c : StatefulClaim)
    (h_ready : checkMirLiftDagReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (BlockInv : List Value → Memory → BasicBlockIdx → PureEnv → Prop)
    (h_init : ∀ args mem, c.pre args mem →
      BlockInv args mem 0 (initPureEnv c.body args))
    (h_step : ∀ args mem, c.pre args mem → ∀ bbIdx env, BlockInv args mem bbIdx env →
      (∀ succ env', CfgEdge c.body bbIdx succ → BlockInv args mem succ env' →
        ∃ fuel, LiftSafeBlock c.body succ env'
          (fun retVal =>
            c.post args mem retVal
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                c.body args mem c.callees).memory)
          fuel) →
      ∃ fuel, LiftSafeBlock c.body bbIdx env
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)
        fuel) :
    StatefulVerificationResult c :=
  verifyStatefulMirSafe_of_mirLiftDagReady c h_ready h_root (fun args mem hp =>
    let ⟨_, hf⟩ :=
      liftSafeBlock_of_mirLiftDagReady_induct h_ready (BlockInv args mem)
        (h_init args mem hp) (h_step args mem hp)
    liftSafe_PureMirSafeConverges_of_mirLiftDagReady h_ready hf)

theorem verifyTotalMir_of_mirLiftReady
    (c : TotalClaim)
    (h_ready : checkMirLiftReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_lift : ∀ args mem, c.pre args mem →
      ∃ fuel, LiftBlock c.body 0 (initPureEnv c.body args)
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)
        fuel) :
    TotalVerificationResult c :=
  verifyTotalMir_of_pureExec c
    (checkPureMir_of_mirLiftReady h_ready)
    h_root
    (fun args mem hp =>
      let ⟨_, hf⟩ := h_lift args mem hp
      lift_PureMirConverges_of_mirLiftReady h_ready hf)

theorem verifyTotalMir_of_mirLiftDagReady
    (c : TotalClaim)
    (h_ready : checkMirLiftDagReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_lift : ∀ args mem, c.pre args mem →
      ∃ fuel, LiftBlock c.body 0 (initPureEnv c.body args)
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)
        fuel) :
    TotalVerificationResult c :=
  verifyTotalMir_of_mirLiftReady c
    (checkMirLiftReady_of_dagReady h_ready)
    h_root
    h_lift

/--
Total-correctness (`TotalVerificationResult`) backwards-topological DAG induction
gate (`verifyTotalMir_of_mirLiftDagReady_induct`), removing global path-fuel
bounds and user-supplied ranking functions while framing initial memory.
-/
theorem verifyTotalMir_of_mirLiftDagReady_induct
    (c : TotalClaim)
    (h_ready : checkMirLiftDagReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (BlockInv : List Value → Memory → BasicBlockIdx → PureEnv → Prop)
    (h_init : ∀ args mem, c.pre args mem →
      BlockInv args mem 0 (initPureEnv c.body args))
    (h_step : ∀ args mem, c.pre args mem → ∀ bbIdx env, BlockInv args mem bbIdx env →
      (∀ succ env', CfgEdge c.body bbIdx succ → BlockInv args mem succ env' →
        ∃ fuel, LiftBlock c.body succ env'
          (fun retVal =>
            c.post args mem retVal
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                c.body args mem c.callees).memory)
          fuel) →
      ∃ fuel, LiftBlock c.body bbIdx env
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)
        fuel) :
    TotalVerificationResult c :=
  verifyTotalMir_of_mirLiftDagReady c h_ready h_root (fun args mem hp =>
    liftBlock_of_mirLiftDagReady_induct h_ready (BlockInv args mem)
      (h_init args mem hp) (h_step args mem hp))

/--
Alias-erased well-founded `while`-loop convergence over `PureState`:
given `checkPureMir body = true`, a decreasing `rank : α → Nat`, and
`PureMirStepsConverges` steps preserving `LoopInv`, execution converges
(`PureMirConverges`) without mentioning `Memory` in `LoopInv`.
-/
theorem pureMirConverges_whileRank {α : Type}
    (rank : α → Nat)
    (body : CapturedMir)
    (LoopInv : α → PureState → Prop)
    (ps₀ : PureState)
    (a₀ : α)
    (post : Value → Prop)
    (h_pure : checkPureMir body = true)
    (h_init : LoopInv a₀ ps₀)
    (h_step : ∀ a ps, LoopInv a ps →
      PureMirStepsConverges body ps
        (fun ps' => ∃ a', LoopInv a' ps' ∧ rank a' < rank a)
        post) :
    PureMirConverges body ps₀ post := by
  have h_gen : ∀ r a ps, rank a = r → LoopInv a ps → PureMirConverges body ps post := by
    apply nat_strong_induction
      (fun r => ∀ a ps, rank a = r → LoopInv a ps → PureMirConverges body ps post)
    intro r ih a ps h_eq h_inv
    refine PureMirConverges.bind (h_step a ps h_inv) (fun ps' h_mid => ?_) h_pure
    rcases h_mid with ⟨a', h_inv', h_lt⟩
    exact ih (rank a') (h_eq ▸ h_lt) a' ps' rfl h_inv'
  exact h_gen (rank a₀) a₀ ps₀ rfl h_init

/--
Alias-erased bounded-range (`forRangeUp`) loop convergence over `PureState`:
proves `PureMirConverges` by induction on `hi - lo` without mentioning `Memory`.
-/
theorem pureMirConverges_forRangeUp {α : Type}
    (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (body : CapturedMir)
    (LoopInv : Nat → α → PureState → Prop)
    (ps₀ : PureState)
    (post : Value → Prop)
    (h_pure : checkPureMir body = true)
    (h_init : LoopInv lo init ps₀)
    (h_body : ∀ i h_i_le h_i_lt a ps, LoopInv i a ps →
      PureMirStepsConverges body ps
        (fun ps' => LoopInv (i + 1) (step i h_i_le h_i_lt a) ps')
        post)
    (h_exit : ∀ i a ps, hi ≤ i → LoopInv i a ps → PureMirConverges body ps post) :
    PureMirConverges body ps₀ post := by
  generalize h_d : hi - lo = d
  induction d generalizing lo init step ps₀ with
  | zero =>
    exact h_exit lo init ps₀ (Nat.le_of_sub_eq_zero h_d) h_init
  | succ d ih =>
    have h_lt : lo < hi := Nat.lt_of_sub_eq_succ h_d
    refine PureMirConverges.bind
      (h_body lo (Nat.le_refl _) h_lt init ps₀ h_init)
      (fun ps' h_mid => ?_)
      h_pure
    have h_sub : hi - (lo + 1) = d := by
      have h_sub_succ : hi - (lo + 1) = (hi - lo).pred := Nat.sub_succ hi lo
      rw [h_sub_succ, h_d]
      rfl
    exact ih (lo + 1) (step lo (Nat.le_refl _) h_lt init)
      (fun i h_le' h_lt' a => step i (Nat.le_trans (Nat.le_succ _) h_le') h_lt' a)
      ps'
      h_mid
      (fun i h_le' h_lt' a ps h_inv =>
        h_body i (Nat.le_trans (Nat.le_succ _) h_le') h_lt' a ps h_inv)
      h_sub

/--
**Loop-Lifting Convergence Bridge (`mirWpConverges_of_mirLoopLiftReady`)**:
Connects `checkMirLoopLiftReady body = true` with well-founded `whileRank` loop
reasoning over alias-erased `PureState`, automatically framing arbitrary
root-active initial memory `mem₀ : Memory` (`mem' = mem₀`).
-/
theorem mirWpConverges_of_mirLoopLiftReady {α : Type}
    {body : CapturedMir} {args : List Value} {post : Value → Prop}
    {mem₀ : Memory}
    (h_ready : checkMirLoopLiftReady body = true)
    (rank : α → Nat)
    (LoopInv : α → PureState → Prop)
    (a₀ : α)
    (h_init : LoopInv a₀ (initPureState body args))
    (h_step : ∀ a ps, LoopInv a ps →
      PureMirStepsConverges body ps
        (fun ps' => ∃ a', LoopInv a' ps' ∧ rank a' < rank a)
        post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) :=
  mirWpConverges_of_pureExec
    (checkPureMir_of_mirLoopLiftReady h_ready)
    (pureMirConverges_whileRank rank body LoopInv
      (initPureState body args) a₀ post
      (checkPureMir_of_mirLoopLiftReady h_ready)
      h_init h_step)
    h_root

/--
Bounded-range (`forRangeUp`) variant of `mirWpConverges_of_mirLoopLiftReady`,
automatically framing arbitrary root-active initial memory `mem₀ : Memory`.
-/
theorem mirWpConverges_forRangeUp_of_mirLoopLiftReady {α : Type}
    {body : CapturedMir} {args : List Value} {post : Value → Prop}
    {mem₀ : Memory}
    (h_ready : checkMirLoopLiftReady body = true)
    (lo hi : Nat) (init : α) (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (LoopInv : Nat → α → PureState → Prop)
    (h_init : LoopInv lo init (initPureState body args))
    (h_body : ∀ i h_i_le h_i_lt a ps, LoopInv i a ps →
      PureMirStepsConverges body ps
        (fun ps' => LoopInv (i + 1) (step i h_i_le h_i_lt a) ps')
        post)
    (h_exit : ∀ i a ps, hi ≤ i → LoopInv i a ps → PureMirConverges body ps post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) :=
  mirWpConverges_of_pureExec
    (checkPureMir_of_mirLoopLiftReady h_ready)
    (pureMirConverges_forRangeUp lo hi init step body LoopInv
      (initPureState body args) post
      (checkPureMir_of_mirLoopLiftReady h_ready)
      h_init h_body h_exit)
    h_root

/--
Stateless verification gate bridge for loop-ready pure MIR (`checkMirLoopLiftReady`).
-/
theorem verifyMirNoPanic_of_mirLoopLiftReady {α : Type}
    (c : Claim)
    (h_ready : checkMirLoopLiftReady c.body = true)
    (rank : List Value → α → Nat)
    (LoopInv : List Value → α → PureState → Prop)
    (a₀ : List Value → α)
    (h_init : ∀ args, c.pre args → LoopInv args (a₀ args) (initPureState c.body args))
    (h_step : ∀ args, c.pre args → ∀ a ps, LoopInv args a ps →
      PureMirStepsConverges c.body ps
        (fun ps' => ∃ a', LoopInv args a' ps' ∧ rank args a' < rank args a)
        (c.post args)) :
    VerificationResult c :=
  verifyMirNoPanic_of_pureExec c
    (checkPureMir_of_mirLoopLiftReady h_ready)
    (fun args hp =>
      pureMirConverges_whileRank (rank args) c.body (LoopInv args)
        (initPureState c.body args) (a₀ args) (c.post args)
        (checkPureMir_of_mirLoopLiftReady h_ready)
        (h_init args hp) (h_step args hp))

/--
Alias-erased partial-correctness (`mirSafePost`) well-founded `while`-loop
convergence over `PureState`, permitting panicking assertions inside the loop.
-/
theorem pureMirSafeConverges_whileRank {α : Type}
    (rank : α → Nat)
    (body : CapturedMir)
    (LoopInv : α → PureState → Prop)
    (ps₀ : PureState)
    (a₀ : α)
    (post : Value → Prop)
    (h_pure : checkPureMir body = true)
    (h_init : LoopInv a₀ ps₀)
    (h_step : ∀ a ps, LoopInv a ps →
      PureMirSafeStepsConverges body ps
        (fun ps' => ∃ a', LoopInv a' ps' ∧ rank a' < rank a)
        post) :
    PureMirSafeConverges body ps₀ post := by
  have h_gen : ∀ r a ps, rank a = r → LoopInv a ps → PureMirSafeConverges body ps post := by
    apply nat_strong_induction
      (fun r => ∀ a ps, rank a = r → LoopInv a ps → PureMirSafeConverges body ps post)
    intro r ih a ps h_eq h_inv
    refine PureMirSafeConverges.bind (h_step a ps h_inv) (fun ps' h_mid => ?_) h_pure
    rcases h_mid with ⟨a', h_inv', h_lt⟩
    exact ih (rank a') (h_eq ▸ h_lt) a' ps' rfl h_inv'
  exact h_gen (rank a₀) a₀ ps₀ rfl h_init

/--
Stateless partial-correctness (`mirSafePost`) verification gate bridge for
loop-ready pure MIR (`checkMirLoopLiftReady`), permitting clean panics inside
loop iterations.
-/
theorem verifyMirSafe_of_mirLoopLiftReady {α : Type}
    (c : Claim)
    (h_ready : checkMirLoopLiftReady c.body = true)
    (rank : List Value → α → Nat)
    (LoopInv : List Value → α → PureState → Prop)
    (a₀ : List Value → α)
    (h_init : ∀ args, c.pre args → LoopInv args (a₀ args) (initPureState c.body args))
    (h_step : ∀ args, c.pre args → ∀ a ps, LoopInv args a ps →
      PureMirSafeStepsConverges c.body ps
        (fun ps' => ∃ a', LoopInv args a' ps' ∧ rank args a' < rank args a)
        (c.post args)) :
    VerificationResult c :=
  verifyMirSafe_of_pureExec c
    (checkPureMir_of_mirLoopLiftReady h_ready)
    (fun args hp =>
      pureMirSafeConverges_whileRank (rank args) c.body (LoopInv args)
        (initPureState c.body args) (a₀ args) (c.post args)
        (checkPureMir_of_mirLoopLiftReady h_ready)
        (h_init args hp) (h_step args hp))

/--
Stateful panic-forbidding verification gate bridge for loop-ready pure MIR
(`checkMirLoopLiftReady`), automatically framing initial memory.
-/
theorem verifyStatefulMirNoPanic_of_mirLoopLiftReady {α : Type}
    (c : StatefulClaim)
    (h_ready : checkMirLoopLiftReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (rank : List Value → Memory → α → Nat)
    (LoopInv : List Value → Memory → α → PureState → Prop)
    (a₀ : List Value → Memory → α)
    (h_init : ∀ args mem, c.pre args mem →
      LoopInv args mem (a₀ args mem) (initPureState c.body args))
    (h_step : ∀ args mem, c.pre args mem → ∀ a ps, LoopInv args mem a ps →
      PureMirStepsConverges c.body ps
        (fun ps' => ∃ a', LoopInv args mem a' ps' ∧ rank args mem a' < rank args mem a)
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_pureExec c
    (checkPureMir_of_mirLoopLiftReady h_ready)
    h_root
    (fun args mem hp =>
      pureMirConverges_whileRank (rank args mem) c.body (LoopInv args mem)
        (initPureState c.body args) (a₀ args mem) _
        (checkPureMir_of_mirLoopLiftReady h_ready)
        (h_init args mem hp) (h_step args mem hp))

/--
Stateful partial-correctness (`mirSafePost`) verification gate bridge for
loop-ready pure MIR (`checkMirLoopLiftReady`).
-/
theorem verifyStatefulMirSafe_of_mirLoopLiftReady {α : Type}
    (c : StatefulClaim)
    (h_ready : checkMirLoopLiftReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (rank : List Value → Memory → α → Nat)
    (LoopInv : List Value → Memory → α → PureState → Prop)
    (a₀ : List Value → Memory → α)
    (h_init : ∀ args mem, c.pre args mem →
      LoopInv args mem (a₀ args mem) (initPureState c.body args))
    (h_step : ∀ args mem, c.pre args mem → ∀ a ps, LoopInv args mem a ps →
      PureMirSafeStepsConverges c.body ps
        (fun ps' => ∃ a', LoopInv args mem a' ps' ∧ rank args mem a' < rank args mem a)
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)) :
    StatefulVerificationResult c :=
  verifyStatefulMirSafe_of_pureExec c
    (checkPureMir_of_mirLoopLiftReady h_ready)
    h_root
    (fun args mem hp =>
      pureMirSafeConverges_whileRank (rank args mem) c.body (LoopInv args mem)
        (initPureState c.body args) (a₀ args mem) _
        (checkPureMir_of_mirLoopLiftReady h_ready)
        (h_init args mem hp) (h_step args mem hp))

/--
Total-correctness (`TotalVerificationResult`) gate bridge for loop-ready pure MIR
(`checkMirLoopLiftReady`), automatically framing initial memory while proving
termination, UB-freedom, and panic-freedom.
-/
theorem verifyTotalMir_of_mirLoopLiftReady {α : Type}
    (c : TotalClaim)
    (h_ready : checkMirLoopLiftReady c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (rank : List Value → Memory → α → Nat)
    (LoopInv : List Value → Memory → α → PureState → Prop)
    (a₀ : List Value → Memory → α)
    (h_init : ∀ args mem, c.pre args mem →
      LoopInv args mem (a₀ args mem) (initPureState c.body args))
    (h_step : ∀ args mem, c.pre args mem → ∀ a ps, LoopInv args mem a ps →
      PureMirStepsConverges c.body ps
        (fun ps' => ∃ a', LoopInv args mem a' ps' ∧ rank args mem a' < rank args mem a)
        (fun retVal =>
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)) :
    TotalVerificationResult c :=
  verifyTotalMir_of_pureExec c
    (checkPureMir_of_mirLoopLiftReady h_ready)
    h_root
    (fun args mem hp =>
      pureMirConverges_whileRank (rank args mem) c.body (LoopInv args mem)
        (initPureState c.body args) (a₀ args mem) _
        (checkPureMir_of_mirLoopLiftReady h_ready)
        (h_init args mem hp) (h_step args mem hp))

/--
Stateless bounded-range (`forRangeUp`) verification gate bridge for loop-ready
pure MIR (`checkMirLoopLiftReady`).
-/
theorem verifyMirNoPanic_forRangeUp_of_mirLoopLiftReady {α : Type}
    (c : Claim)
    (h_ready : checkMirLoopLiftReady c.body = true)
    (lo hi : List Value → Nat)
    (init : List Value → α)
    (step : (args : List Value) → (i : Nat) → lo args ≤ i → i < hi args → α → α)
    (LoopInv : List Value → Nat → α → PureState → Prop)
    (h_init : ∀ args, c.pre args →
      LoopInv args (lo args) (init args) (initPureState c.body args))
    (h_body : ∀ args, c.pre args → ∀ i h_le h_lt a ps, LoopInv args i a ps →
      PureMirStepsConverges c.body ps
        (fun ps' => LoopInv args (i + 1) (step args i h_le h_lt a) ps')
        (c.post args))
    (h_exit : ∀ args, c.pre args → ∀ i a ps, hi args ≤ i → LoopInv args i a ps →
      PureMirConverges c.body ps (c.post args)) :
    VerificationResult c :=
  verifyMirNoPanic_of_pureExec c
    (checkPureMir_of_mirLoopLiftReady h_ready)
    (fun args hp =>
      pureMirConverges_forRangeUp (lo args) (hi args) (init args) (step args)
        c.body (LoopInv args) (initPureState c.body args) (c.post args)
        (checkPureMir_of_mirLoopLiftReady h_ready)
        (h_init args hp) (h_body args hp) (h_exit args hp))

/-! ### Kernel-Checked Readiness & Lifting Regression Witnesses -/

namespace MirLiftReadyWitness

open MirFragment.Witness

theorem checkMirLiftDagReady_witnessPureLoopFree :
    checkMirLiftDagReady witnessPureLoopFree = true := rfl

theorem checkMirLiftReady_witnessPureLoopFree :
    checkMirLiftReady witnessPureLoopFree = true := rfl

theorem checkMirLiftReady_witnessPureBoundedLoop :
    checkMirLiftReady witnessPureBoundedLoop = true := rfl

theorem checkMirLiftDagReady_witnessPureBoundedLoop :
    checkMirLiftDagReady witnessPureBoundedLoop = false := rfl

theorem checkMirLoopLiftReady_witnessPureBoundedLoop :
    checkMirLoopLiftReady witnessPureBoundedLoop = true := rfl

theorem checkMirLoopLiftReady_witnessRustcSharedReturn :
    checkMirLoopLiftReady witnessRustcSharedReturn = true := rfl

theorem checkMirLiftReady_witnessPtrRelAssign :
    checkMirLiftReady witnessPtrRelAssign = false := rfl

theorem checkMirLiftReady_witnessExposeProvenanceCast :
    checkMirLiftReady witnessExposeProvenanceCast = false := rfl

theorem checkMirLiftReady_witnessWithExposedProvenanceCast :
    checkMirLiftReady witnessWithExposedProvenanceCast = false := rfl

/--
End-to-end non-vacuous `VerificationResult` witness exercising
`verifyMirNoPanic_of_mirLiftDagReady_fuel`, `eval_rest_ready`, and
`term_return_ready` on `witnessPureLoopFree`.
-/
theorem verify_witnessPureLoopFree_via_mirLiftDagReady :
    VerificationResult
      { body := witnessPureLoopFree
        pre := fun args => args = []
        post := fun _ retVal => retVal = .scalar { bits := 0, sizeBytes := 4 }
        callees := [] } := by
  refine verifyMirNoPanic_of_mirLiftDagReady_fuel _ 2
    checkMirLiftDagReady_witnessPureLoopFree
    (fun args h_args => ?_)
  subst h_args
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.eval_rest_ready
    checkMirLiftReady_witnessPureLoopFree (by rfl) (by rfl)
  exact LiftStmtsTerminator.term_return_ready
    checkMirLiftReady_witnessPureLoopFree (by rfl) rfl rfl (by rfl) rfl

private def witnessBoolLayout : TypeLayout :=
  { size := { bytes := 1 }
    align := { bytes := 1 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

private def witnessU32Layout : TypeLayout :=
  { size := { bytes := 4 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

private def witnessBoolTy : Ty := { kind := .bool, layoutIdx := 0 }
private def witnessU32Ty : Ty := { kind := .uint .u32, layoutIdx := 1 }

private def witnessLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries := [witnessBoolLayout, witnessU32Layout] }

private def witnessConstU32 (n : Nat) : Operand :=
  .constant { ty := witnessU32Ty, val := .scalar (.int ⟨n, 4⟩) }

private theorem wrapScalarBits_u32_of_lt {v : Nat} (h : v < 4294967296) :
    wrapScalarBits v (scalarModulus 4) = v := by
  unfold wrapScalarBits
  have hm : scalarModulus 4 = 4294967296 := rfl
  rw [hm]
  cases h_b : Nat.ble 4294967296 v
  · rfl
  · exact False.elim (Nat.not_le_of_lt h (Nat.le_of_ble_eq_true h_b))

/--
Multi-block branching DAG witness (`argCount := 2`: `_1 : bool`, `_2 : u32`):
- `bb0`: `StorageLive(_3); _3 = Copy(_2); assert(Copy(_1) == true) -> bb1`
- `bb1`: `drop(_3) -> bb2`
- `bb2`: `switchInt(Copy(_2)) [0 => bb3, otherwise => bb4]`
- `bb3`: `_0 = const 1u32; goto -> bb5`
- `bb4`: `_0 = Add(Copy(_2), const 1u32); goto -> bb5`
- `bb5`: `return_`
-/
def witnessDagBranching : CapturedMir where
  defPath := "Anneal::MirLiftCore::witness_dag_branching"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := witnessU32Ty, debugName := some "_0" },
    { mutability := .not, ty := witnessBoolTy, debugName := some "ok" },
    { mutability := .not, ty := witnessU32Ty, debugName := some "x" },
    { mutability := .mut, ty := witnessU32Ty, debugName := some "tmp" }
  ]
  basicBlocks := [
    -- bb0
    { statements := [
        { kind := .storageLive 3, span := "s0" },
        { kind := .assign { local_ := 3, projection := [] } (.use (.copy { local_ := 2, projection := [] })), span := "s1" }
      ]
      terminator := {
        kind := .assert (.copy { local_ := 1, projection := [] }) true 1 .continue_
        span := "t0"
      }
      isCleanup := false },
    -- bb1
    { statements := []
      terminator := {
        kind := .drop { local_ := 3, projection := [] } 2 .continue_
        span := "t1"
      }
      isCleanup := false },
    -- bb2
    { statements := []
      terminator := {
        kind := .switchInt (.copy { local_ := 2, projection := [] })
          { branches := [(0, 3)], otherwise := 4 }
        span := "t2"
      }
      isCleanup := false },
    -- bb3 (x == 0)
    { statements := [
        { kind := .assign { local_ := 0, projection := [] } (.use (witnessConstU32 1)), span := "s3" }
      ]
      terminator := { kind := .goto 5, span := "t3" }
      isCleanup := false },
    -- bb4 (x != 0)
    { statements := [
        { kind := .assign { local_ := 0, projection := [] }
            (.binaryOp .add (.copy { local_ := 2, projection := [] }) (witnessConstU32 1)),
          span := "s4" }
      ]
      terminator := { kind := .goto 5, span := "t4" }
      isCleanup := false },
    -- bb5 (join & return)
    { statements := []
      terminator := { kind := .return_, span := "t5" }
      isCleanup := false }
  ]
  fnAbi := {
    args := [
      { layout := witnessBoolLayout, mode := .direct },
      { layout := witnessU32Layout, mode := .direct }
    ]
    ret := { layout := witnessU32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := witnessLayouts
  allocations := []

theorem checkMirLiftDagReady_witnessDagBranching :
    checkMirLiftDagReady witnessDagBranching = true := rfl

theorem checkMirLiftReady_witnessDagBranching :
    checkMirLiftReady witnessDagBranching = true := rfl

/-- Precondition for `witnessDagBranching`: `ok = true` and `x < 100`. -/
def witnessDagBranchingPre (args : List Value) : Prop :=
  ∃ x : Nat, x < 100 ∧
    args = [.scalar { bits := 1, sizeBytes := 1 }, .scalar { bits := x, sizeBytes := 4 }]

theorem witnessDagBranchingPre_nonVacuous :
    ∃ args, witnessDagBranchingPre args :=
  ⟨[.scalar { bits := 1, sizeBytes := 1 }, .scalar { bits := 42, sizeBytes := 4 }],
   42, by decide, rfl⟩

/--
Block invariant for `witnessDagBranching` used by
`verifyMirNoPanic_of_mirLiftDagReady_induct` (no fuel or rank annotations).
-/
def witnessDagBlockInv (args : List Value) (bbIdx : BasicBlockIdx) (env : PureEnv) : Prop :=
  ∃ x : Nat, x < 100 ∧
    args = [.scalar { bits := 1, sizeBytes := 1 }, .scalar { bits := x, sizeBytes := 4 }] ∧
    match bbIdx with
    | 0 => env = [.uninit, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨x, 4⟩), .dead]
    | 1 => env = [.uninit, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨x, 4⟩), .init (.scalar ⟨x, 4⟩)]
    | 2 => env = [.uninit, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨x, 4⟩), .uninit]
    | 3 => x = 0 ∧ env = [.uninit, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0, 4⟩), .uninit]
    | 4 => x ≠ 0 ∧ env = [.uninit, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨x, 4⟩), .uninit]
    | 5 => env = [.init (.scalar ⟨if x = 0 then 1 else x + 1, 4⟩),
                  .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨x, 4⟩), .uninit]
    | _ => False

/--
End-to-end symbolic `VerificationResult` for `witnessDagBranching` over all `x < 100`,
exercising `verifyMirNoPanic_of_mirLiftDagReady_induct` together with
`eval_n_ready`, `cons_eval_norm_ready`, `eval_rest_ready`, `term_assert_ready`,
`term_drop_ready`, `term_switchInt_ready`, `term_goto_ready`, and `term_return_ready`.
-/
theorem verify_witnessDagBranching_via_induct :
    VerificationResult
      { body := witnessDagBranching
        pre := witnessDagBranchingPre
        post := fun args retVal =>
          ∀ x : Nat,
            args = [.scalar { bits := 1, sizeBytes := 1 }, .scalar { bits := x, sizeBytes := 4 }] →
            retVal = .scalar { bits := if x = 0 then 1 else x + 1, sizeBytes := 4 }
        callees := [] } := by
  have h_r := checkMirLiftReady_witnessDagBranching
  refine verifyMirNoPanic_of_mirLiftDagReady_induct _
    checkMirLiftDagReady_witnessDagBranching
    witnessDagBlockInv
    (fun args hp => by
      rcases hp with ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl, rfl⟩)
    (fun args _ bbIdx env h_inv ih => ?_)
  rcases h_inv with ⟨x, hx, h_args, h_env⟩
  subst h_args
  match bbIdx with
  | 0 =>
    subst h_env
    have h_edge : CfgEdge witnessDagBranching 0 1 := ⟨_, rfl, by simp [blockTargets, terminatorTargets]⟩
    obtain ⟨f, hf⟩ := ih 1 _ h_edge ⟨x, hx, rfl, rfl⟩
    refine ⟨f + 1 + 2, LiftBlock.of_lookup (by rfl) ?_⟩
    exact LiftStmtsTerminator.eval_n_ready (n := 2) h_r (by rfl) (by rfl)
      (LiftStmtsTerminator.term_assert_ready h_r (by rfl) rfl rfl (by rfl) rfl hf)
  | 1 =>
    subst h_env
    have h_edge : CfgEdge witnessDagBranching 1 2 := ⟨_, rfl, by simp [blockTargets, terminatorTargets]⟩
    obtain ⟨f, hf⟩ := ih 2 _ h_edge ⟨x, hx, rfl, rfl⟩
    refine ⟨f + 1, LiftBlock.of_lookup (by rfl) ?_⟩
    exact LiftStmtsTerminator.term_drop_ready h_r (by rfl) rfl rfl (by rfl)
      (by intro h_dead; nomatch h_dead) rfl (by rfl) hf
  | 2 =>
    subst h_env
    cases x with
    | zero =>
      have h_edge : CfgEdge witnessDagBranching 2 3 := ⟨_, rfl, by simp [blockTargets, terminatorTargets]⟩
      obtain ⟨f, hf⟩ := ih 3 _ h_edge ⟨0, hx, rfl, rfl, rfl⟩
      refine ⟨f + 1, LiftBlock.of_lookup (by rfl) ?_⟩
      exact LiftStmtsTerminator.term_switchInt_ready (sc := ⟨0, 4⟩)
        h_r (by rfl) rfl rfl (by rfl) rfl hf
    | succ x' =>
      have h_edge : CfgEdge witnessDagBranching 2 4 := ⟨_, rfl, by simp [blockTargets, terminatorTargets]⟩
      obtain ⟨f, hf⟩ := ih 4 _ h_edge ⟨x' + 1, hx, rfl, Nat.succ_ne_zero x', rfl⟩
      refine ⟨f + 1, LiftBlock.of_lookup (by rfl) ?_⟩
      exact LiftStmtsTerminator.term_switchInt_ready (sc := ⟨x' + 1, 4⟩)
        h_r (by rfl) rfl rfl (by rfl) rfl hf
  | 3 =>
    rcases h_env with ⟨rfl, h_e⟩
    subst h_e
    have h_edge : CfgEdge witnessDagBranching 3 5 := ⟨_, rfl, by simp [blockTargets, terminatorTargets]⟩
    obtain ⟨f, hf⟩ := ih 5 _ h_edge ⟨0, hx, rfl, rfl⟩
    refine ⟨f + 1 + 1, LiftBlock.of_lookup (by rfl) ?_⟩
    exact LiftStmtsTerminator.cons_eval_norm_ready h_r (by rfl) (by rfl) (by rfl)
      (LiftStmtsTerminator.term_goto_ready h_r (by rfl) rfl rfl hf)
  | 4 =>
    rcases h_env with ⟨hx_ne, h_e⟩
    subst h_e
    have h_wrap : wrapScalarBits (x + 1) (scalarModulus 4) = x + 1 :=
      wrapScalarBits_u32_of_lt (by omega)
    have h_if : (if x = 0 then 1 else x + 1) = x + 1 := if_neg hx_ne
    have h_edge : CfgEdge witnessDagBranching 4 5 := ⟨_, rfl, by simp [blockTargets, terminatorTargets]⟩
    obtain ⟨f, hf⟩ :=
      ih 5 [.init (.scalar ⟨x + 1, 4⟩), .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨x, 4⟩), .uninit]
        h_edge ⟨x, hx, rfl, by rw [h_if]; rfl⟩
    refine ⟨f + 1 + 1, LiftBlock.of_lookup (by rfl) ?_⟩
    refine LiftStmtsTerminator.eval_rest_ready h_r (by rfl) ?_
      (LiftStmtsTerminator.term_goto_ready h_r (by rfl) rfl rfl hf)
    change (some [.init (.scalar ⟨wrapScalarBits (x + 1) (scalarModulus 4), 4⟩),
                  .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨x, 4⟩), .uninit] : Option PureEnv) =
      some [.init (.scalar ⟨x + 1, 4⟩),
            .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨x, 4⟩), .uninit]
    rw [h_wrap]
  | 5 =>
    subst h_env
    refine ⟨1, LiftBlock.of_lookup (by rfl) ?_⟩
    refine LiftStmtsTerminator.term_return_ready h_r (by rfl) rfl rfl (by rfl) ?_
    intro x' h_eq
    injection h_eq with _ h_tl
    injection h_tl with h_sc _
    injection h_sc with h_v
    cases h_v
    rfl
  | n + 6 =>
    exact False.elim h_env

/--
Pure bounded-loop witness (`fn countdown_accum(mut x: u32) -> u32`):
initializes `_0 = 0`, loops while `_1 != 0` performing `_0 = Add(_0, 1); _1 = Sub(_1, 1)`,
and returns `_0` (`= x`).
-/
def witnessCountdownAccumLoop : CapturedMir where
  defPath := "Anneal::MirLiftCore::witness_countdown_accum_loop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := witnessU32Ty, debugName := some "_0" },
    { mutability := .mut, ty := witnessU32Ty, debugName := some "x" }
  ]
  basicBlocks := [
    -- bb0: _0 = 0; goto bb1
    { statements := [
        { kind := .assign { local_ := 0, projection := [] } (.use (witnessConstU32 0)), span := "init" }
      ]
      terminator := { kind := .goto 1, span := "goto_hdr" }
      isCleanup := false },
    -- bb1: switchInt(Copy(_1)) [0 => bb3, otherwise => bb2]
    { statements := []
      terminator := {
        kind := .switchInt (.copy { local_ := 1, projection := [] })
          { branches := [(0, 3)], otherwise := 2 }
        span := "hdr_sw"
      }
      isCleanup := false },
    -- bb2: _0 = Add(Copy(_0), 1); _1 = Sub(Copy(_1), 1); goto bb1
    { statements := [
        { kind := .assign { local_ := 0, projection := [] }
            (.binaryOp .add (.copy { local_ := 0, projection := [] }) (witnessConstU32 1)),
          span := "inc_acc" },
        { kind := .assign { local_ := 1, projection := [] }
            (.binaryOp .sub (.copy { local_ := 1, projection := [] }) (witnessConstU32 1)),
          span := "dec_x" }
      ]
      terminator := { kind := .goto 1, span := "backedge" }
      isCleanup := false },
    -- bb3: return_
    { statements := []
      terminator := { kind := .return_, span := "ret" }
      isCleanup := false }
  ]
  fnAbi := {
    args := [{ layout := witnessU32Layout, mode := .direct }]
    ret := { layout := witnessU32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := witnessLayouts
  allocations := []

theorem checkMirLoopLiftReady_witnessCountdownAccumLoop :
    checkMirLoopLiftReady witnessCountdownAccumLoop = true := rfl

theorem checkMirLiftReady_witnessCountdownAccumLoop :
    checkMirLiftReady witnessCountdownAccumLoop = true := rfl

theorem checkMirLiftDagReady_witnessCountdownAccumLoop :
    checkMirLiftDagReady witnessCountdownAccumLoop = false := rfl

theorem inferBorrowFreeMinFragment_witnessCountdownAccumLoop :
    inferBorrowFreeMinFragment witnessCountdownAccumLoop = .pureBoundedLoop := rfl

/-- Stateful precondition for `witnessCountdownAccumLoop` over all `x < 2^32` and root-active `mem`. -/
def witnessCountdownLoopPre (args : List Value) (mem : Memory) : Prop :=
  (∃ x : Nat, x < 4294967296 ∧ args = [.scalar { bits := x, sizeBytes := 4 }]) ∧
  RootActiveMemory mem

theorem witnessCountdownLoopPre_nonVacuous :
    NonVacuousStatefulPre witnessCountdownLoopPre :=
  ⟨[.scalar { bits := 17, sizeBytes := 4 }],
   emptyMemory,
   ⟨17, by decide, rfl⟩,
   rootActiveMemory_emptyMemory⟩

private def countdownRank : Sum Nat Nat → Nat
  | .inl x => x + 1
  | .inr rem => rem

private def countdownInv (args : List Value) (st : Sum Nat Nat) (ps : PureState) : Prop :=
  ∃ x : Nat, x < 4294967296 ∧
    args = [.scalar { bits := x, sizeBytes := 4 }] ∧
    match st with
    | .inl x₀ =>
      x₀ = x ∧ ps = { bb := 0, stmtIdx := 0, env := [.uninit, .init (.scalar ⟨x, 4⟩)] }
    | .inr rem =>
      rem ≤ x ∧
      ps = { bb := 1
             stmtIdx := 0
             env := [.init (.scalar ⟨x - rem, 4⟩), .init (.scalar ⟨rem, 4⟩)] }

/--
End-to-end symbolic `TotalVerificationResult` for `witnessCountdownAccumLoop`
over all `x < 2^32` and arbitrary `RootActiveMemory mem`, proved via
`verifyTotalMir_of_mirLoopLiftReady`. Certifies termination, UB-freedom,
panic-freedom, exact return value `retVal = .scalar ⟨x, 4⟩`, and exact memory
framing `mem' = mem`.
-/
theorem verifyTotal_witnessCountdownAccumLoop :
    TotalVerificationResult
      { body := witnessCountdownAccumLoop
        pre := witnessCountdownLoopPre
        post := fun args mem retVal mem' =>
          mem' = mem ∧
          ∀ x : Nat,
            args = [.scalar { bits := x, sizeBytes := 4 }] →
            retVal = .scalar { bits := x, sizeBytes := 4 }
        callees := [] } := by
  refine verifyTotalMir_of_mirLoopLiftReady _
    checkMirLoopLiftReady_witnessCountdownAccumLoop
    (fun _ _ hp => hp.2)
    (fun _ _ => countdownRank)
    (fun args _ => countdownInv args)
    (fun args _ => match args with
      | [.scalar sc] => .inl sc.bits
      | _ => .inl 0)
    (fun args _ hp => by
      rcases hp.1 with ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl, rfl, rfl⟩)
    (fun args mem hp a ps h_inv => ?_)
  rcases h_inv with ⟨x, hx, h_args, h_st⟩
  subst h_args
  cases a with
  | inl x₀ =>
    rcases h_st with ⟨h_x₀, rfl⟩
    subst x₀
    refine ⟨2, .inr x, ⟨x, hx, rfl, Nat.le_refl x, ?_⟩, by dsimp [countdownRank]; omega⟩
    change ({ bb := 1
              stmtIdx := 0
              env := [.init (.scalar ⟨0, 4⟩), .init (.scalar ⟨x, 4⟩)] } : PureState) =
      { bb := 1
        stmtIdx := 0
        env := [.init (.scalar ⟨x - x, 4⟩), .init (.scalar ⟨x, 4⟩)] }
    rw [Nat.sub_self]
  | inr rem =>
    rcases h_st with ⟨h_rem_le, rfl⟩
    cases rem with
    | zero =>
      refine ⟨2, ?_⟩
      have h_sub0 : x - 0 = x := Nat.sub_zero x
      rw [h_sub0]
      refine ⟨rfl, ?_⟩
      intro x' h_eq
      injection h_eq with h_sc _
    | succ rem' =>
      cases rem' with
      | zero =>
        have h_acc_wrap : wrapScalarBits (x - 1 + 1) (scalarModulus 4) = x - 0 := by
          have h_eq : x - 1 + 1 = x - 0 := by omega
          rw [h_eq]
          exact wrapScalarBits_u32_of_lt (by omega)
        refine ⟨4, .inr 0, ⟨x, hx, rfl, Nat.zero_le x, ?_⟩, by dsimp [countdownRank]; omega⟩
        change ({ bb := 1
                  stmtIdx := 0
                  env := [.init (.scalar ⟨wrapScalarBits (x - 1 + 1) (scalarModulus 4), 4⟩),
                          .init (.scalar ⟨0, 4⟩)] } : PureState) =
          { bb := 1
            stmtIdx := 0
            env := [.init (.scalar ⟨x - 0, 4⟩), .init (.scalar ⟨0, 4⟩)] }
        rw [h_acc_wrap]
      | succ r =>
        have h_acc_wrap : wrapScalarBits (x - (r + 1 + 1) + 1) (scalarModulus 4) = x - (r + 1) := by
          have h_eq : x - (r + 1 + 1) + 1 = x - (r + 1) := by omega
          rw [h_eq]
          exact wrapScalarBits_u32_of_lt (by omega)
        have h_rem_wrap : wrapScalarBits (r + 1) (scalarModulus 4) = r + 1 :=
          wrapScalarBits_u32_of_lt (by omega)
        refine ⟨4, .inr (r + 1), ⟨x, hx, rfl, by omega, ?_⟩, by dsimp [countdownRank]; omega⟩
        change ({ bb := 1
                  stmtIdx := 0
                  env := [.init (.scalar ⟨wrapScalarBits (x - (r + 1 + 1) + 1) (scalarModulus 4), 4⟩),
                          .init (.scalar ⟨wrapScalarBits (r + 1) (scalarModulus 4), 4⟩)] } : PureState) =
          { bb := 1
            stmtIdx := 0
            env := [.init (.scalar ⟨x - (r + 1), 4⟩), .init (.scalar ⟨r + 1, 4⟩)] }
        rw [h_acc_wrap, h_rem_wrap]

/--
Non-topologically-numbered shared-return DAG witness (`argCount := 1`, `_1 : u32`):
- `bb0`: `switchInt(Copy(_1)) [0 => bb2, otherwise => bb3]`
- `bb1`: `return_` (shared return block numbered BEFORE `bb2` and `bb3`)
- `bb2`: `_0 = const 10u32; goto -> bb1` (index back-edge `2 -> 1`, `1 ≤ 2`)
- `bb3`: `_0 = const 20u32; goto -> bb1` (index back-edge `3 -> 1`, `1 ≤ 3`)
Here `hasCfgBackedge = true` (`checkMirLiftDagReady = false`), yet `isCfgDag = true`
and `checkMirLiftReady = true`.
-/
def witnessSharedReturnDag : CapturedMir where
  defPath := "Anneal::MirLiftCore::witness_shared_return_dag"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := witnessU32Ty, debugName := some "_0" },
    { mutability := .not, ty := witnessU32Ty, debugName := some "x" }
  ]
  basicBlocks := [
    -- bb0
    { statements := []
      terminator := {
        kind := .switchInt (.copy { local_ := 1, projection := [] })
          { branches := [(0, 2)], otherwise := 3 }
        span := "sw"
      }
      isCleanup := false },
    -- bb1 (shared return numbered before arms!)
    { statements := []
      terminator := { kind := .return_, span := "ret" }
      isCleanup := false },
    -- bb2 (x == 0)
    { statements := [
        { kind := .assign { local_ := 0, projection := [] } (.use (witnessConstU32 10)), span := "c10" }
      ]
      terminator := { kind := .goto 1, span := "g1a" }
      isCleanup := false },
    -- bb3 (x != 0)
    { statements := [
        { kind := .assign { local_ := 0, projection := [] } (.use (witnessConstU32 20)), span := "c20" }
      ]
      terminator := { kind := .goto 1, span := "g1b" }
      isCleanup := false }
  ]
  fnAbi := {
    args := [{ layout := witnessU32Layout, mode := .direct }]
    ret := { layout := witnessU32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := witnessLayouts
  allocations := []

theorem hasCfgBackedge_witnessSharedReturnDag :
    hasCfgBackedge witnessSharedReturnDag = true := rfl

theorem checkMirLiftDagReady_witnessSharedReturnDag :
    checkMirLiftDagReady witnessSharedReturnDag = false := rfl

theorem isCfgDag_witnessSharedReturnDag :
    isCfgDag witnessSharedReturnDag = true := rfl

theorem checkMirLiftReady_witnessSharedReturnDag :
    checkMirLiftReady witnessSharedReturnDag = true := rfl

def witnessSharedReturnDagPre (args : List Value) : Prop :=
  ∃ x : Nat, args = [.scalar { bits := x, sizeBytes := 4 }]

theorem witnessSharedReturnDagPre_nonVacuous :
    ∃ args, witnessSharedReturnDagPre args :=
  ⟨[.scalar { bits := 7, sizeBytes := 4 }], 7, rfl⟩

private def witnessSharedReturnBlockInv
    (args : List Value) (bbIdx : BasicBlockIdx) (env : PureEnv) : Prop :=
  ∃ x : Nat,
    args = [.scalar { bits := x, sizeBytes := 4 }] ∧
    match bbIdx with
    | 0 => env = [.uninit, .init (.scalar ⟨x, 4⟩)]
    | 1 => env = [.init (.scalar ⟨if x = 0 then 10 else 20, 4⟩), .init (.scalar ⟨x, 4⟩)]
    | 2 => x = 0 ∧ env = [.uninit, .init (.scalar ⟨0, 4⟩)]
    | 3 => x ≠ 0 ∧ env = [.uninit, .init (.scalar ⟨x, 4⟩)]
    | _ => False

/--
End-to-end symbolic `VerificationResult` for `witnessSharedReturnDag` (where
`hasCfgBackedge = true` and `isCfgDag = true`), proved via
`verifyMirNoPanic_of_isCfgDag_mirLiftReady_induct` with no user-supplied rank
function.
-/
theorem verify_witnessSharedReturnDag_via_isCfgDag_induct :
    VerificationResult
      { body := witnessSharedReturnDag
        pre := witnessSharedReturnDagPre
        post := fun args retVal =>
          ∀ x : Nat,
            args = [.scalar { bits := x, sizeBytes := 4 }] →
            retVal = .scalar { bits := if x = 0 then 10 else 20, sizeBytes := 4 }
        callees := [] } := by
  have h_r := checkMirLiftReady_witnessSharedReturnDag
  refine verifyMirNoPanic_of_isCfgDag_mirLiftReady_induct _
    h_r witnessSharedReturnBlockInv
    (fun args hp => by
      rcases hp with ⟨x, rfl⟩
      exact ⟨x, rfl, rfl⟩)
    (fun args _ bbIdx env h_inv ih => ?_)
  rcases h_inv with ⟨x, h_args, h_env⟩
  subst h_args
  match bbIdx with
  | 0 =>
    subst h_env
    cases x with
    | zero =>
      have h_edge : CfgEdge witnessSharedReturnDag 0 2 := ⟨_, rfl, by simp [blockTargets, terminatorTargets]⟩
      obtain ⟨f, hf⟩ := ih 2 _ h_edge ⟨0, rfl, rfl, rfl⟩
      refine ⟨f + 1, LiftBlock.of_lookup (by rfl) ?_⟩
      exact LiftStmtsTerminator.term_switchInt_ready (sc := ⟨0, 4⟩)
        h_r (by rfl) rfl rfl (by rfl) rfl hf
    | succ x' =>
      have h_edge : CfgEdge witnessSharedReturnDag 0 3 := ⟨_, rfl, by simp [blockTargets, terminatorTargets]⟩
      obtain ⟨f, hf⟩ := ih 3 _ h_edge ⟨x' + 1, rfl, Nat.succ_ne_zero x', rfl⟩
      refine ⟨f + 1, LiftBlock.of_lookup (by rfl) ?_⟩
      exact LiftStmtsTerminator.term_switchInt_ready (sc := ⟨x' + 1, 4⟩)
        h_r (by rfl) rfl rfl (by rfl) rfl hf
  | 1 =>
    subst h_env
    refine ⟨1, LiftBlock.of_lookup (by rfl) ?_⟩
    refine LiftStmtsTerminator.term_return_ready h_r (by rfl) rfl rfl (by rfl) ?_
    intro x' h_eq
    injection h_eq with h_sc _
    injection h_sc with h_v
    cases h_v
    rfl
  | 2 =>
    rcases h_env with ⟨rfl, h_e⟩
    subst h_e
    have h_edge : CfgEdge witnessSharedReturnDag 2 1 := ⟨_, rfl, by simp [blockTargets, terminatorTargets]⟩
    obtain ⟨f, hf⟩ := ih 1 _ h_edge ⟨0, rfl, rfl⟩
    refine ⟨f + 1 + 1, LiftBlock.of_lookup (by rfl) ?_⟩
    exact LiftStmtsTerminator.eval_rest_ready h_r (by rfl) (by rfl)
      (LiftStmtsTerminator.term_goto_ready h_r (by rfl) rfl rfl hf)
  | 3 =>
    rcases h_env with ⟨hx_ne, h_e⟩
    subst h_e
    have h_if : (if x = 0 then 10 else 20) = 20 := if_neg hx_ne
    have h_edge : CfgEdge witnessSharedReturnDag 3 1 := ⟨_, rfl, by simp [blockTargets, terminatorTargets]⟩
    obtain ⟨f, hf⟩ :=
      ih 1 [.init (.scalar ⟨20, 4⟩), .init (.scalar ⟨x, 4⟩)]
        h_edge ⟨x, rfl, by rw [h_if]; rfl⟩
    refine ⟨f + 1 + 1, LiftBlock.of_lookup (by rfl) ?_⟩
    exact LiftStmtsTerminator.eval_rest_ready h_r (by rfl) (by rfl)
      (LiftStmtsTerminator.term_goto_ready h_r (by rfl) rfl rfl hf)
  | n + 4 =>
    exact False.elim h_env

end MirLiftReadyWitness

end Anneal.MirLiftCore

/-!
## Fuel-Free Loop-Lifting Core in the `Anneal.PureMirExec` Namespace

The generic Kleene fuel calculus, header-targeted stepping, structural `[lo, hi)`
loops, and the live `CapturedMir` embedding (`mirStep`, `runMirToBlock`) keep their
`Anneal.PureMirExec` names but are elaborated here rather than in `PureMirExec.lean`,
which is already close to the 60-second per-module elaboration budget of
`trusted/audit/check_trusted.py`.
-/

namespace Anneal.PureMirExec

open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.Rustc.V2026_06_01.Lower

/-!
### Kleene Fuel Order, Header-Targeted `runToTarget` / `runMirToBlock`, and Structural Loop Lifting
-/

/-! #### Generic Deterministic Small-Step Machine and the Kleene Fuel Order -/

/-- Outcome of one deterministic small step. -/
inductive Step (σ α : Type) where
  /-- Continue at `next`. -/
  | cont (next : σ)
  /-- Halt returning `ret`. -/
  | done (ret : α)
  /-- Stuck / undefined behavior. -/
  | fault
  deriving DecidableEq, Repr

/-- Outcome of a bounded-fuel evaluation: running out of fuel is *not* a fault
and is never conflated with halting. -/
inductive FuelResult (α : Type) where
  | outOfFuel
  | halted (v : α)
  | faulted
  deriving DecidableEq, Repr

/-- Flat Kleene information order: `outOfFuel` is bottom; `halted v` and
`faulted` are maximal. -/
def FuelOrder {α : Type} : FuelResult α → FuelResult α → Prop
  | .outOfFuel, _ => True
  | .halted v₁, .halted v₂ => v₁ = v₂
  | .faulted, .faulted => True
  | _, _ => False

theorem FuelOrder.refl {α : Type} (r : FuelResult α) : FuelOrder r r := by
  cases r with
  | outOfFuel => exact trivial
  | halted v => exact rfl
  | faulted => exact trivial

theorem FuelOrder.trans {α : Type} {r₁ r₂ r₃ : FuelResult α}
    (h₁₂ : FuelOrder r₁ r₂) (h₂₃ : FuelOrder r₂ r₃) : FuelOrder r₁ r₃ := by
  cases r₁ <;> cases r₂ <;> cases r₃ <;> simp_all [FuelOrder]

theorem FuelOrder.halted_stable {α : Type} {v : α} {r : FuelResult α}
    (h : FuelOrder (.halted v) r) : r = .halted v := by
  cases r <;> simp_all [FuelOrder]

theorem FuelOrder.faulted_stable {α : Type} {r : FuelResult α}
    (h : FuelOrder .faulted r) : r = .faulted := by
  cases r <;> simp_all [FuelOrder]

/-- Fueled evaluator by structural recursion on the fuel. -/
def evalFuel {σ α : Type} (step : σ → Step σ α) : Nat → σ → FuelResult α
  | 0, _ => .outOfFuel
  | k + 1, s =>
    match step s with
    | .cont s' => evalFuel step k s'
    | .done v => .halted v
    | .fault => .faulted

/-- **Kleene fuel monotonicity**: adding fuel preserves every terminal outcome. -/
theorem evalFuel_mono {σ α : Type} (step : σ → Step σ α) :
    ∀ {k₁ k₂ : Nat} (s : σ), k₁ ≤ k₂ →
      FuelOrder (evalFuel step k₁ s) (evalFuel step k₂ s)
  | 0, _, _, _ => trivial
  | k₁ + 1, 0, _, hle => absurd hle (Nat.not_succ_le_zero k₁)
  | k₁ + 1, k₂ + 1, s, hle => by
    unfold evalFuel
    cases step s with
    | cont s' => exact evalFuel_mono step s' (Nat.le_of_succ_le_succ hle)
    | done v => exact rfl
    | fault => exact trivial

theorem evalFuel_halted_mono {σ α : Type} {step : σ → Step σ α} {k₁ k₂ : Nat}
    {s : σ} {v : α} (h : evalFuel step k₁ s = .halted v) (hle : k₁ ≤ k₂) :
    evalFuel step k₂ s = .halted v := by
  have hm := evalFuel_mono step s hle
  rw [h] at hm
  exact FuelOrder.halted_stable hm

theorem evalFuel_faulted_mono {σ α : Type} {step : σ → Step σ α} {k₁ k₂ : Nat}
    {s : σ} (h : evalFuel step k₁ s = .faulted) (hle : k₁ ≤ k₂) :
    evalFuel step k₂ s = .faulted := by
  have hm := evalFuel_mono step s hle
  rw [h] at hm
  exact FuelOrder.faulted_stable hm

/-- Halting results are fuel-independent (determinism). -/
theorem evalFuel_halted_deterministic {σ α : Type} {step : σ → Step σ α}
    {k₁ k₂ : Nat} {s : σ} {v₁ v₂ : α}
    (h₁ : evalFuel step k₁ s = .halted v₁) (h₂ : evalFuel step k₂ s = .halted v₂) :
    v₁ = v₂ := by
  have e₁ := evalFuel_halted_mono h₁ (Nat.le_max_left k₁ k₂)
  have e₂ := evalFuel_halted_mono h₂ (Nat.le_max_right k₁ k₂)
  rw [e₁] at e₂
  exact FuelResult.halted.inj e₂

/-- A state that faults under some fuel never halts under any fuel: faults are
never conflated with termination. -/
theorem evalFuel_faulted_ne_halted {σ α : Type} {step : σ → Step σ α}
    {k₁ k₂ : Nat} {s : σ} {v : α}
    (hf : evalFuel step k₁ s = .faulted) : evalFuel step k₂ s ≠ .halted v := by
  intro hh
  have e₁ := evalFuel_faulted_mono hf (Nat.le_max_left k₁ k₂)
  have e₂ := evalFuel_halted_mono hh (Nat.le_max_right k₁ k₂)
  rw [e₁] at e₂
  cases e₂

/-- Fuel-free total-correctness predicate: some finite budget halts in `post`. -/
def WpConverges {σ α : Type} (step : σ → Step σ α) (s : σ) (post : α → Prop) : Prop :=
  ∃ k v, evalFuel step k s = .halted v ∧ post v

theorem WpConverges.of_done {σ α : Type} {step : σ → Step σ α} {s : σ} {v : α}
    {post : α → Prop} (hd : step s = .done v) (hp : post v) :
    WpConverges step s post :=
  ⟨1, v, by simp [evalFuel, hd], hp⟩

theorem WpConverges.of_cont {σ α : Type} {step : σ → Step σ α} {s s' : σ}
    {post : α → Prop} (hs : step s = .cont s') (h : WpConverges step s' post) :
    WpConverges step s post := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact ⟨k + 1, v, by simp [evalFuel, hs, hk], hp⟩

theorem WpConverges.mono {σ α : Type} {step : σ → Step σ α} {s : σ}
    {P Q : α → Prop} (himp : ∀ v, P v → Q v) (h : WpConverges step s P) :
    WpConverges step s Q := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact ⟨k, v, hk, himp v hp⟩

/-- Fault soundness: a faulting state never converges. -/
theorem not_wpConverges_of_faulted {σ α : Type} {step : σ → Step σ α} {s : σ}
    {k : Nat} {post : α → Prop} (hf : evalFuel step k s = .faulted) :
    ¬ WpConverges step s post := by
  rintro ⟨k', v, hk', _⟩
  exact evalFuel_faulted_ne_halted hf hk'

/-- Converged return values are unique. -/
theorem WpConverges.deterministic {σ α : Type} {step : σ → Step σ α} {s : σ}
    {v₁ v₂ : α} (h₁ : WpConverges step s (· = v₁)) (h₂ : WpConverges step s (· = v₂)) :
    v₁ = v₂ := by
  obtain ⟨k₁, w₁, hk₁, hw₁⟩ := h₁
  obtain ⟨k₂, w₂, hk₂, hw₂⟩ := h₂
  subst hw₁ hw₂
  exact evalFuel_halted_deterministic hk₁ hk₂

/-- Multi-step segment reachability of an intermediate predicate `mid`. -/
inductive StepsTo {σ α : Type} (step : σ → Step σ α) : σ → (σ → Prop) → Prop where
  | refl {s : σ} {mid : σ → Prop} (h : mid s) : StepsTo step s mid
  | step {s s' : σ} {mid : σ → Prop}
      (hstep : step s = .cont s') (hrest : StepsTo step s' mid) : StepsTo step s mid

/-- **Sequential bind rule**: fuel budgets are synthesized existentially across
segments, so user proofs never mention fuel numerals. -/
theorem StepsTo.bind_wp {σ α : Type} {step : σ → Step σ α} {s : σ}
    {mid : σ → Prop} {post : α → Prop}
    (hseg : StepsTo step s mid)
    (hcont : ∀ s₁, mid s₁ → WpConverges step s₁ post) :
    WpConverges step s post := by
  induction hseg with
  | refl hm => exact hcont _ hm
  | step hs _ ih => exact WpConverges.of_cont hs (ih hcont)

theorem StepsTo.trans {σ α : Type} {step : σ → Step σ α} {s : σ}
    {mid₁ mid₂ : σ → Prop}
    (h₁ : StepsTo step s mid₁) (h₂ : ∀ s₁, mid₁ s₁ → StepsTo step s₁ mid₂) :
    StepsTo step s mid₂ := by
  induction h₁ with
  | refl hm => exact h₂ _ hm
  | step hs _ ih => exact StepsTo.step hs (ih h₂)

theorem StepsTo.mono {σ α : Type} {step : σ → Step σ α} {s : σ}
    {mid₁ mid₂ : σ → Prop} (himp : ∀ s₁, mid₁ s₁ → mid₂ s₁)
    (h : StepsTo step s mid₁) : StepsTo step s mid₂ :=
  h.trans (fun s₁ hm => StepsTo.refl (himp s₁ hm))

/-! #### Header-Targeted Stepping (`TargetOutcome`, `FirstHitIn`, `runToTarget`) -/

/-- Outcome of a header-targeted segment run. The four outcomes are pairwise
distinct constructors: reaching the target, halting, getting stuck, and running
out of the internal step ceiling are never conflated. -/
inductive TargetOutcome (σ α : Type) where
  | reached (s : σ)
  | halted (v : α)
  | stuck
  | outOfFuel
  deriving DecidableEq, Repr

/-- Zero-or-more-step search for the next target state. -/
def runUntilTarget {σ α : Type} (step : σ → Step σ α) (atTarget : σ → Bool) :
    Nat → σ → TargetOutcome σ α
  | 0, s => if atTarget s then .reached s else .outOfFuel
  | bound + 1, s =>
    if atTarget s then .reached s
    else
      match step s with
      | .cont s' => runUntilTarget step atTarget bound s'
      | .done v => .halted v
      | .fault => .stuck

/-- One mandatory step (so starting *at* a loop header advances through the
body) followed by the search for the next target entry within `bound` extra
steps. -/
def runToTarget {σ α : Type} (step : σ → Step σ α) (atTarget : σ → Bool)
    (bound : Nat) (s : σ) : TargetOutcome σ α :=
  match step s with
  | .cont s' => runUntilTarget step atTarget bound s'
  | .done v => .halted v
  | .fault => .stuck

theorem runUntilTarget_reached_atTarget {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s s_hit : σ),
      runUntilTarget step atTarget bound s = .reached s_hit → atTarget s_hit = true
  | 0, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ht
    | false => rw [ht] at h; cases h
  | bound + 1, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ht
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        exact runUntilTarget_reached_atTarget step atTarget bound s' s_hit h
      | done _ => rw [hs] at h; cases h
      | fault => rw [hs] at h; cases h

/-- A `.reached` outcome always lands on a target state. -/
theorem runToTarget_reached_atTarget {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s s_hit : σ}
    (h : runToTarget step atTarget bound s = .reached s_hit) : atTarget s_hit = true := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' => rw [hs] at h; exact runUntilTarget_reached_atTarget step atTarget bound s' s_hit h
  | done _ => rw [hs] at h; cases h
  | fault => rw [hs] at h; cases h

theorem stepsTo_of_runUntilTarget_reached {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s s_hit : σ),
      runUntilTarget step atTarget bound s = .reached s_hit → StepsTo step s (· = s_hit)
  | 0, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact StepsTo.refl rfl
    | false => rw [ht] at h; cases h
  | bound + 1, s, s_hit, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact StepsTo.refl rfl
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        exact StepsTo.step hs (stepsTo_of_runUntilTarget_reached step atTarget bound s' s_hit h)
      | done _ => rw [hs] at h; cases h
      | fault => rw [hs] at h; cases h

/-- **Target arrival soundness** (generic form). -/
theorem stepsTo_of_runToTarget_reached {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s s_hit : σ}
    (h : runToTarget step atTarget bound s = .reached s_hit) :
    StepsTo step s (· = s_hit) := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    exact StepsTo.step hs (stepsTo_of_runUntilTarget_reached step atTarget bound s' s_hit h)
  | done _ => rw [hs] at h; cases h
  | fault => rw [hs] at h; cases h

theorem wpConverges_of_runUntilTarget_halted {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) {post : α → Prop} :
    ∀ (bound : Nat) (s : σ) (v : α),
      runUntilTarget step atTarget bound s = .halted v → post v → WpConverges step s post
  | 0, s, _, h, _ => by
    unfold runUntilTarget at h
    cases ht : atTarget s <;> rw [ht] at h <;> cases h
  | bound + 1, s, v, h, hp => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        exact WpConverges.of_cont hs
          (wpConverges_of_runUntilTarget_halted step atTarget bound s' v h hp)
      | done v₀ => rw [hs] at h; cases h; exact WpConverges.of_done hs hp
      | fault => rw [hs] at h; cases h

/-- **Halting soundness** (generic form). -/
theorem wpConverges_of_runToTarget_halted {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s : σ} {v : α} {post : α → Prop}
    (h : runToTarget step atTarget bound s = .halted v) (hp : post v) :
    WpConverges step s post := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    exact WpConverges.of_cont hs (wpConverges_of_runUntilTarget_halted step atTarget bound s' v h hp)
  | done v₀ => rw [hs] at h; cases h; exact WpConverges.of_done hs hp
  | fault => rw [hs] at h; cases h

theorem faulted_of_runUntilTarget_stuck {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s : σ),
      runUntilTarget step atTarget bound s = .stuck → ∃ k, evalFuel step k s = .faulted
  | 0, s, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s <;> rw [ht] at h <;> cases h
  | bound + 1, s, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        obtain ⟨k, hk⟩ := faulted_of_runUntilTarget_stuck step atTarget bound s' h
        exact ⟨k + 1, by simp [evalFuel, hs, hk]⟩
      | done _ => rw [hs] at h; cases h
      | fault => exact ⟨1, by simp [evalFuel, hs]⟩

/-- **Stuck soundness**: a `.stuck` outcome is a genuine fault, so the state can
never converge (stuck is never conflated with halting). -/
theorem not_wpConverges_of_runToTarget_stuck {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s : σ} {post : α → Prop}
    (h : runToTarget step atTarget bound s = .stuck) : ¬ WpConverges step s post := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    obtain ⟨k, hk⟩ := faulted_of_runUntilTarget_stuck step atTarget bound s' h
    exact not_wpConverges_of_faulted (k := k + 1) (by simp [evalFuel, hs, hk])
  | done _ => rw [hs] at h; cases h
  | fault => exact not_wpConverges_of_faulted (k := 1) (by simp [evalFuel, hs])

theorem runUntilTarget_mono_bound {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ {b₁ b₂ : Nat} (s : σ),
      runUntilTarget step atTarget b₁ s ≠ .outOfFuel → b₁ ≤ b₂ →
      runUntilTarget step atTarget b₂ s = runUntilTarget step atTarget b₁ s
  | 0, 0, _, _, _ => rfl
  | 0, b₂ + 1, s, hne, _ => by
    unfold runUntilTarget at hne ⊢
    cases ht : atTarget s with
    | true => rfl
    | false => rw [ht] at hne; exact absurd rfl hne
  | _ + 1, 0, _, _, hle => absurd hle (Nat.not_succ_le_zero _)
  | b₁ + 1, b₂ + 1, s, hne, hle => by
    unfold runUntilTarget at hne ⊢
    cases ht : atTarget s with
    | true => rfl
    | false =>
      rw [ht] at hne
      cases hs : step s with
      | cont s' =>
        rw [hs] at hne
        exact runUntilTarget_mono_bound step atTarget s' hne (Nat.le_of_succ_le_succ hle)
      | done _ => rfl
      | fault => rfl

/-- **Ceiling monotonicity**: once a run is conclusive (`≠ .outOfFuel`) under
`b₁`, every larger ceiling returns the identical outcome. -/
theorem runToTarget_mono_bound {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {b₁ b₂ : Nat} {s : σ}
    (hne : runToTarget step atTarget b₁ s ≠ .outOfFuel) (hle : b₁ ≤ b₂) :
    runToTarget step atTarget b₂ s = runToTarget step atTarget b₁ s := by
  unfold runToTarget at hne ⊢
  cases hs : step s with
  | cont s' =>
    rw [hs] at hne
    exact runUntilTarget_mono_bound step atTarget s' hne hle
  | done _ => rfl
  | fault => rfl

/-- `FirstHitIn n s s_hit`: after one mandatory step and `n` further silent
steps through non-target states, `s` reaches the target state `s_hit`, and no
earlier visited state (other than possibly `s` itself) is a target. -/
inductive FirstHitIn {σ α : Type} (step : σ → Step σ α) (atTarget : σ → Bool) :
    Nat → σ → σ → Prop where
  | here {s s' : σ} (hs : step s = .cont s') (ht : atTarget s' = true) :
      FirstHitIn step atTarget 0 s s'
  | later {n : Nat} {s s' s_hit : σ} (hs : step s = .cont s') (hnt : atTarget s' = false)
      (hrest : FirstHitIn step atTarget n s' s_hit) :
      FirstHitIn step atTarget (n + 1) s s_hit

/-- The first target re-entry is unique (and so is its step count). -/
theorem FirstHitIn.unique {σ α : Type} {step : σ → Step σ α} {atTarget : σ → Bool} :
    ∀ {n₁ n₂ : Nat} {s a b : σ},
      FirstHitIn step atTarget n₁ s a → FirstHitIn step atTarget n₂ s b → a = b ∧ n₁ = n₂
  | _, _, _, _, _, .here hs₁ ht₁, .here hs₂ _ => by
    rw [hs₁] at hs₂; cases hs₂; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, .here hs₁ ht₁, .later hs₂ hnt₂ _ => by
    rw [hs₁] at hs₂; cases hs₂; rw [ht₁] at hnt₂; cases hnt₂
  | _, _, _, _, _, .later hs₁ hnt₁ _, .here hs₂ ht₂ => by
    rw [hs₁] at hs₂; cases hs₂; rw [ht₂] at hnt₁; cases hnt₁
  | _, _, _, _, _, .later hs₁ _ h₁, .later hs₂ _ h₂ => by
    rw [hs₁] at hs₂; cases hs₂
    obtain ⟨hab, hn⟩ := FirstHitIn.unique h₁ h₂
    exact ⟨hab, congrArg (· + 1) hn⟩

theorem firstHitIn_of_runUntilTarget_reached {σ α : Type} (step : σ → Step σ α)
    (atTarget : σ → Bool) :
    ∀ (bound : Nat) (s₀ s s_hit : σ), step s₀ = .cont s →
      runUntilTarget step atTarget bound s = .reached s_hit →
      ∃ n, n ≤ bound ∧ FirstHitIn step atTarget n s₀ s_hit
  | 0, s₀, s, s_hit, h0, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ⟨0, Nat.le_refl 0, .here h0 ht⟩
    | false => rw [ht] at h; cases h
  | bound + 1, s₀, s, s_hit, h0, h => by
    unfold runUntilTarget at h
    cases ht : atTarget s with
    | true => rw [ht] at h; cases h; exact ⟨0, Nat.zero_le _, .here h0 ht⟩
    | false =>
      rw [ht] at h
      cases hs : step s with
      | cont s' =>
        rw [hs] at h
        obtain ⟨n, hn, hfh⟩ := firstHitIn_of_runUntilTarget_reached step atTarget bound s s' s_hit hs h
        exact ⟨n + 1, Nat.succ_le_succ hn, .later h0 ht hfh⟩
      | done _ => rw [hs] at h; cases h
      | fault => rw [hs] at h; cases h

/-- **No overshoot**: a `.reached s_hit` outcome is exactly the *first* target
re-entry (within the ceiling); combined with `FirstHitIn.unique`, the stepper
can never skip past a loop header, even on self-loops. -/
theorem firstHitIn_of_runToTarget_reached {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {bound : Nat} {s s_hit : σ}
    (h : runToTarget step atTarget bound s = .reached s_hit) :
    ∃ n, n ≤ bound ∧ FirstHitIn step atTarget n s s_hit := by
  unfold runToTarget at h
  cases hs : step s with
  | cont s' =>
    rw [hs] at h
    exact firstHitIn_of_runUntilTarget_reached step atTarget bound s s' s_hit hs h
  | done _ => rw [hs] at h; cases h
  | fault => rw [hs] at h; cases h

theorem runUntilTarget_of_firstHitIn {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} :
    ∀ {n : Nat} {s₀ s_hit : σ}, FirstHitIn step atTarget n s₀ s_hit →
      ∀ (s : σ), step s₀ = .cont s → ∀ (bound : Nat), n ≤ bound →
        runUntilTarget step atTarget bound s = .reached s_hit
  | _, _, _, .here hs ht, s, h0, bound, _ => by
    rw [hs] at h0; cases h0
    cases bound with
    | zero => unfold runUntilTarget; rw [ht]; rfl
    | succ b => unfold runUntilTarget; rw [ht]; rfl
  | _, _, _, .later (n := n) (s' := s') hs hnt hrest, s, h0, bound, hle => by
    rw [hs] at h0; cases h0
    cases bound with
    | zero => exact absurd hle (Nat.not_succ_le_zero n)
    | succ b =>
      unfold runUntilTarget
      rw [hnt]
      cases hrest with
      | here hs' ht' =>
        rw [hs']
        exact runUntilTarget_of_firstHitIn (.here hs' ht') _ hs' b (Nat.zero_le b)
      | later hs' hnt' hrest' =>
        rw [hs']
        exact runUntilTarget_of_firstHitIn (.later hs' hnt' hrest') _ hs' b
          (Nat.le_of_succ_le_succ hle)

/-- **Completeness**: the first target re-entry is found by every sufficiently
large ceiling, so the ceiling only affects completeness, never soundness. -/
theorem runToTarget_of_firstHitIn {σ α : Type} {step : σ → Step σ α}
    {atTarget : σ → Bool} {n bound : Nat} {s s_hit : σ}
    (h : FirstHitIn step atTarget n s s_hit) (hle : n ≤ bound) :
    runToTarget step atTarget bound s = .reached s_hit := by
  cases h with
  | here hs ht =>
    unfold runToTarget; rw [hs]
    exact runUntilTarget_of_firstHitIn (.here hs ht) _ hs bound hle
  | later hs hnt hrest =>
    unfold runToTarget; rw [hs]
    exact runUntilTarget_of_firstHitIn (.later hs hnt hrest) _ hs bound hle

/-! #### Structural `[lo, hi)` Range Loops (`forRangeUpAux`, `PureMirExec.forRangeUp`, `wpConverges_forRangeUp`, `stepsTo_forRangeUp`) -/

/-- Structural range fold over `[i, hi)` indexed by the remaining trip count. -/
def forRangeUpAux {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    (i rem : Nat) → lo ≤ i → i + rem = hi → α → α
  | _, 0, _, _, acc => acc
  | i, rem + 1, hlo, hsum, acc =>
    forRangeUpAux lo hi step (i + 1) rem (Nat.le_succ_of_le hlo) (by omega)
      (step i hlo (by omega) acc)

/-- Structurally recursive `for i in lo..hi` fold (kernel-reducible). -/
protected def forRangeUp {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) : α :=
  if h : lo ≤ hi then
    forRangeUpAux lo hi step lo (hi - lo) (Nat.le_refl lo) (by omega) init
  else
    init

theorem forRangeUpAux_induction {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → Prop) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (acc : α),
      inv i acc →
      (∀ j (hjlo : lo ≤ j) (hjlt : j < hi) a, inv j a → inv (j + 1) (step j hjlo hjlt a)) →
      inv hi (forRangeUpAux lo hi step i rem hlo hsum acc)
  | i, 0, _, hsum, acc, hinv, _ => by
    have : i = hi := by omega
    subst this
    exact hinv
  | i, rem + 1, hlo, hsum, acc, hinv, hstep =>
    forRangeUpAux_induction lo hi step inv (i + 1) rem _ _ _ (hstep i hlo (by omega) acc hinv) hstep

/-- **Structural `[lo, hi)` loop induction**. -/
protected theorem forRangeUp_induction {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init)
    (hstep : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a, inv i a → inv (i + 1) (step i hlo hlt a)) :
    inv hi (PureMirExec.forRangeUp lo hi init step) := by
  unfold PureMirExec.forRangeUp
  simp only [hle, ↓reduceDIte]
  exact forRangeUpAux_induction lo hi step inv lo (hi - lo) _ _ init hinit hstep

/-- Empty-range identity (`hi ≤ lo`): `PureMirExec.forRangeUp` returns `init`
immediately in both the `lo = hi` (`hi - lo = 0`) and `hi < lo` branches. -/
protected theorem forRangeUp_eq_init_of_ge {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (hge : hi ≤ lo) :
    PureMirExec.forRangeUp lo hi init step = init := by
  unfold PureMirExec.forRangeUp
  by_cases hle : lo ≤ hi
  · have heq : hi = lo := Nat.le_antisymm hge hle
    subst heq
    simp [forRangeUpAux]
  · simp [hle]

theorem forRangeUpAux_eq_live {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (acc : α),
      forRangeUpAux lo hi step i rem hlo hsum acc =
        Anneal.MirLoops.forRangeUp i hi acc
          (fun j hj hlt a => step j (Nat.le_trans hlo hj) hlt a)
  | i, 0, _, _, _ => by
    rw [Anneal.MirLoops.forRangeUp_eq_init_of_ge _ _ _ _ (by omega)]
    rfl
  | i, rem + 1, _, _, _ => by
    rw [Anneal.MirLoops.forRangeUp_step_of_lt _ _ _ _ (by omega)]
    exact forRangeUpAux_eq_live lo hi step (i + 1) rem _ _ _

/-- **Bridge to the live `Anneal.MirLoops.forRangeUp`** in `Anneal.PureMirExec`. -/
protected theorem forRangeUp_eq_live {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    PureMirExec.forRangeUp lo hi init step = Anneal.MirLoops.forRangeUp lo hi init step := by
  unfold PureMirExec.forRangeUp
  split
  · next hle => exact forRangeUpAux_eq_live lo hi step lo (hi - lo) _ _ init
  · next hgt => rw [Anneal.MirLoops.forRangeUp_eq_init_of_ge _ _ _ _ (by omega)]

/-- Non-empty step-unrolling identity (`lo < hi`) for `PureMirExec.forRangeUp`. -/
protected theorem forRangeUp_step_of_lt {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (h : lo < hi) :
    PureMirExec.forRangeUp lo hi init step =
      PureMirExec.forRangeUp (lo + 1) hi (step lo (Nat.le_refl _) h init)
        (fun i h_le h_lt a => step i (Nat.le_trans (Nat.le_succ _) h_le) h_lt a) := by
  rw [PureMirExec.forRangeUp_eq_live, PureMirExec.forRangeUp_eq_live,
    Anneal.MirLoops.forRangeUp_step_of_lt lo hi init step h]

theorem stepsTo_forRangeUpAux {σ out α : Type} (stepOp : σ → Step σ out)
    (lo hi : Nat) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (a : α) (s : σ),
      inv i a s →
      (∀ j (hjlo : lo ≤ j) (hjlt : j < hi) acc s₀,
        inv j acc s₀ → StepsTo stepOp s₀ (inv (j + 1) (f j hjlo hjlt acc))) →
      StepsTo stepOp s (inv hi (forRangeUpAux lo hi f i rem hlo hsum a))
  | i, 0, _, hsum, _, s, hinv, _ => by
    have hi_eq : i = hi := by omega
    subst hi_eq
    exact StepsTo.refl hinv
  | i, rem + 1, hlo, hsum, a, s, hinv, hiter => by
    have hlt : i < hi := by omega
    exact (hiter i hlo hlt a s hinv).trans (fun s₁ hinv₁ =>
      stepsTo_forRangeUpAux stepOp lo hi f inv (i + 1) rem _ _ (f i hlo hlt a) s₁ hinv₁ hiter)

/-- **Fuel-free range loop as a segment (`StepsTo`)**: unlike
`wpConverges_forRangeUp`, which ends the program, this rule reaches the loop
*exit state* `inv hi (forRangeUp lo hi init f)` as an intermediate segment, so a
loop can sit inside another loop's iteration (nested loops) or be followed by
further `StepsTo` segments, still with no step count or fuel numeral. -/
theorem stepsTo_forRangeUp {σ out α : Type} (stepOp : σ → Step σ out)
    (lo hi : Nat) (init : α) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop) (s₀ : σ) (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s,
      inv i a s → StepsTo stepOp s (inv (i + 1) (f i hlo hlt a))) :
    StepsTo stepOp s₀ (inv hi (PureMirExec.forRangeUp lo hi init f)) := by
  unfold PureMirExec.forRangeUp
  simp only [hle, ↓reduceDIte]
  exact stepsTo_forRangeUpAux stepOp lo hi f inv lo (hi - lo) _ _ init s₀ hinit hiter

theorem wpConverges_forRangeUpAux {σ out α : Type} (stepOp : σ → Step σ out)
    (lo hi : Nat) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop) (post : out → Prop)
    (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (a : α) (s : σ)
    (hinv : inv i a s)
    (hiter : ∀ j (hjlo : lo ≤ j) (hjlt : j < hi) acc s₀,
      inv j acc s₀ → StepsTo stepOp s₀ (inv (j + 1) (f j hjlo hjlt acc)))
    (hexit : ∀ s_exit, inv hi (forRangeUpAux lo hi f i rem hlo hsum a) s_exit →
      WpConverges stepOp s_exit post) :
    WpConverges stepOp s post :=
  (stepsTo_forRangeUpAux stepOp lo hi f inv i rem hlo hsum a s hinv hiter).bind_wp hexit

/-- **Fuel-free range-loop rule**: per-iteration segment reachability plus an
exit obligation imply convergence, with no step count or fuel numeral
(factored directly through `stepsTo_forRangeUp` and `StepsTo.bind_wp`). -/
theorem wpConverges_forRangeUp {σ out α : Type} (stepOp : σ → Step σ out)
    (lo hi : Nat) (init : α) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop) (s₀ : σ) (post : out → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s,
      inv i a s → StepsTo stepOp s (inv (i + 1) (f i hlo hlt a)))
    (hexit : ∀ s_exit, inv hi (PureMirExec.forRangeUp lo hi init f) s_exit → WpConverges stepOp s_exit post) :
    WpConverges stepOp s₀ post :=
  (stepsTo_forRangeUp stepOp lo hi init f inv s₀ hle hinit hiter).bind_wp hexit

/-! #### Live `CapturedMir` Small-Step Embedding (`mirStep`) & Header-Targeted `runMirToBlock` -/

/-- Embedding of the live trusted step function `stepMirFn` into the generic
machine. Both silent `.tau` transitions and `MirObsE` observation steps
(`.vis (.inr (.inl (.emit _)))`, including `.event _` emitted by live
`.switchInt` terminators and `.silent`) continue, and root returns halt;
external calls and faults are mapped conservatively to `.fault`, matching live
`Anneal.FunctionalTranslation.runMirToBlock`. -/
def mirStep (body : CapturedMir) (s : MachineState) : Step MachineState MirOutcome :=
  match stepMirFn body s with
  | .tau (.running s') => .cont s'
  | .vis (.inr (.inl (.emit _))) k =>
    match k PUnit.unit with
    | .running s' => .cont s'
    | _ => .fault
  | .ret out => .done out
  | _ => .fault

theorem stepMirFn_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    (h : mirStep body s = .cont s') :
    stepMirFn body s = .tau (.running s') ∨
      ∃ obs k, stepMirFn body s = .vis (.inr (.inl (.emit obs))) k ∧ k PUnit.unit = .running s' := by
  unfold mirStep at h
  split at h
  · rename_i s'' heq
    cases h
    exact Or.inl heq
  · rename_i obs k heq
    split at h
    · rename_i s'' hk
      cases h
      exact Or.inr ⟨obs, k, heq, hk⟩
    · cases h
  · cases h
  · cases h

theorem stepMirFn_of_mirStep_done {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    (h : mirStep body s = .done out) : stepMirFn body s = .ret out := by
  unfold mirStep at h
  split at h
  · cases h
  · split at h <;> cases h
  · rename_i out' heq
    cases h
    exact heq
  · cases h

theorem mirStepsConverges_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (hs : mirStep body s = .cont s')
    (hnext : Anneal.MirFuelFree.MirStepsConverges body s' mid post) :
    Anneal.MirFuelFree.MirStepsConverges body s mid post := by
  rcases stepMirFn_of_mirStep_cont hs with htau | ⟨obs, k, hvis, hk⟩
  · exact Anneal.MirFuelFree.MirStepsConverges.step_tau htau hnext
  · rcases hnext with ⟨fuel, h_wp⟩
    refine ⟨fuel + 1, ?_⟩
    unfold Anneal.MirFuelFree.wpMirStepsSym
      Anneal.MirFuelFree.wpMirExecStepsSym
    rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTreeNoCall_eq,
      Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeNoCallWP_eq]
    dsimp only [stepMirState]
    cases obs <;> (
      rw [hvis]
      change Anneal.MirFuelFree.wpMirExecStepsSym fuel body (k PUnit.unit) _ post
      rw [hk]
      exact h_wp)

/-- **Bridge to the live `Anneal.MirFuelFree.MirStepsConverges`**: generic
segment reachability over `mirStep` is live fuel-free reachability (including
across all `MirObsE` observation steps). -/
theorem mirStepsConverges_of_stepsTo {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h : StepsTo (mirStep body) s mid) :
    Anneal.MirFuelFree.MirStepsConverges body s mid post := by
  induction h with
  | refl hm => exact Anneal.MirFuelFree.MirStepsConverges.refl hm
  | step hs _ ih => exact mirStepsConverges_of_mirStep_cont hs ih

theorem mirWpConverges_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    {post : MirOutcome → Prop}
    (hs : mirStep body s = .cont s')
    (hnext : Anneal.MirFuelFree.MirWpConverges body s' post) :
    Anneal.MirFuelFree.MirWpConverges body s post := by
  rcases stepMirFn_of_mirStep_cont hs with htau | ⟨obs, k, hvis, hk⟩
  · exact Anneal.MirFuelFree.MirWpConverges.step_tau htau hnext
  · rcases hnext with ⟨fuel, h_wp⟩
    refine ⟨fuel + 1, ?_⟩
    unfold Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirSym
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym
    rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTree_eq,
      Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeWP_eq]
    dsimp only [stepMirState]
    cases obs <;> (
      rw [hvis]
      change Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body (k PUnit.unit) post
      rw [hk]
      exact h_wp)

theorem mirWpConverges_of_evalFuel {body : CapturedMir} {post : MirOutcome → Prop} :
    ∀ (k : Nat) (s : MachineState) (v : MirOutcome),
      evalFuel (mirStep body) k s = .halted v → post v →
      Anneal.MirFuelFree.MirWpConverges body s post
  | 0, _, _, h, _ => by cases h
  | k + 1, s, v, h, hp => by
    unfold evalFuel at h
    cases hs : mirStep body s with
    | cont s' =>
      rw [hs] at h
      exact mirWpConverges_of_mirStep_cont hs
        (mirWpConverges_of_evalFuel k s' v h hp)
    | done out =>
      rw [hs] at h
      cases h
      exact Anneal.MirFuelFree.MirWpConverges.ret_of_step (stepMirFn_of_mirStep_done hs) hp
    | fault =>
      rw [hs] at h
      cases h

/-- **Bridge to the live `Anneal.MirFuelFree.MirWpConverges`**. -/
theorem mirWpConverges_of_wpConverges {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop} (h : WpConverges (mirStep body) s post) :
    Anneal.MirFuelFree.MirWpConverges body s post := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact mirWpConverges_of_evalFuel k s v hk hp

/-- Mixed composition: a generic segment followed by a live continuation
(through the live `MirWpConverges.bind`). -/
theorem mirWpConverges_of_stepsTo_bind {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : StepsTo (mirStep body) s mid)
    (h₂ : ∀ s', mid s' → Anneal.MirFuelFree.MirWpConverges body s' post) :
    Anneal.MirFuelFree.MirWpConverges body s post :=
  Anneal.MirFuelFree.MirWpConverges.bind (mirStepsConverges_of_stepsTo h₁) h₂

theorem mirNoCallWpConverges_of_mirStep_done {body : CapturedMir} {s : MachineState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (hs : mirStep body s = .done out) (hp : post out) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s post := by
  have hret := stepMirFn_of_mirStep_done hs
  refine ⟨1, ?_⟩
  unfold Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirNoCallSym
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecNoCallSym
  rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTreeNoCall_eq,
    Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
    Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeNoCallWP_eq]
  dsimp only [stepMirState]
  rw [hret]
  exact hp

theorem mirNoCallWpConverges_of_mirStep_cont {body : CapturedMir} {s s' : MachineState}
    {post : MirOutcome → Prop}
    (hs : mirStep body s = .cont s')
    (hnext : Anneal.MirFuelFree.MirNoCallWpConverges body s' post) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s post :=
  Anneal.MirFuelFree.MirNoCallWpConverges.bind
    (mirStepsConverges_of_mirStep_cont (mid := (· = s')) (post := post) hs
      (Anneal.MirFuelFree.MirStepsConverges.refl rfl))
    (fun _ heq => heq ▸ hnext)

theorem mirNoCallWpConverges_of_evalFuel {body : CapturedMir} {post : MirOutcome → Prop} :
    ∀ (k : Nat) (s : MachineState) (v : MirOutcome),
      evalFuel (mirStep body) k s = .halted v → post v →
      Anneal.MirFuelFree.MirNoCallWpConverges body s post
  | 0, _, _, h, _ => by cases h
  | k + 1, s, v, h, hp => by
    unfold evalFuel at h
    cases hs : mirStep body s with
    | cont s' =>
      rw [hs] at h
      exact mirNoCallWpConverges_of_mirStep_cont hs
        (mirNoCallWpConverges_of_evalFuel k s' v h hp)
    | done out =>
      rw [hs] at h
      cases h
      exact mirNoCallWpConverges_of_mirStep_done hs hp
    | fault =>
      rw [hs] at h
      cases h

/-- **Bridge to the live `Anneal.MirFuelFree.MirNoCallWpConverges`**. -/
theorem mirNoCallWpConverges_of_wpConverges {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop} (h : WpConverges (mirStep body) s post) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s post := by
  obtain ⟨k, v, hk, hp⟩ := h
  exact mirNoCallWpConverges_of_evalFuel k s v hk hp

/-- Mixed call-free composition: a generic `StepsTo` segment followed by a live
`MirNoCallWpConverges` continuation. -/
theorem mirNoCallWpConverges_of_stepsTo_bind {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : StepsTo (mirStep body) s mid)
    (h₂ : ∀ s', mid s' → Anneal.MirFuelFree.MirNoCallWpConverges body s' post) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s post :=
  Anneal.MirFuelFree.MirNoCallWpConverges.bind (mirStepsConverges_of_stepsTo h₁) h₂

/-- Ceiling for live header-targeted stepping: the total number of statements
and terminators of the body (one live step each). -/
def mirSegmentBound (body : CapturedMir) : Nat :=
  body.basicBlocks.foldl (fun acc bb => acc + bb.statements.length + 1) 0

theorem mirSegmentBound_foldl_ge (l : List BasicBlockData) :
    ∀ a : Nat, a + l.length ≤ l.foldl (fun acc bb => acc + bb.statements.length + 1) a := by
  induction l with
  | nil => intro a; exact Nat.le_refl a
  | cons bb rest ih =>
    intro a
    refine Nat.le_trans ?_ (ih (a + bb.statements.length + 1))
    rw [List.length_cons]
    omega

/-- The live ceiling is derived from the CFG: it is at least the number of basic
blocks (`body.basicBlocks.length`), plus one step per statement. -/
theorem basicBlocks_length_le_mirSegmentBound (body : CapturedMir) :
    body.basicBlocks.length ≤ mirSegmentBound body := by
  have h := mirSegmentBound_foldl_ge body.basicBlocks 0
  rw [Nat.zero_add] at h
  exact h

/-- Header-targeted stepping over live MIR: takes one mandatory step and stops
at the first statement of basic block `target`. -/
protected def runMirToBlock (body : CapturedMir) (target : BasicBlockIdx) (s : MachineState) :
    TargetOutcome MachineState MirOutcome :=
  runToTarget (mirStep body)
    (fun ms => ms.frame.blockIdx == target && ms.frame.stmtIdx == 0) (mirSegmentBound body) s

theorem runMirToBlock_reached_block_and_stmt {body : CapturedMir}
    {target : BasicBlockIdx} {s s' : MachineState}
    (h : PureMirExec.runMirToBlock body target s = .reached s') :
    s'.frame.blockIdx = target ∧ s'.frame.stmtIdx = 0 := by
  unfold PureMirExec.runMirToBlock at h
  have ht0 := runToTarget_reached_atTarget h
  have ht := Bool.and_eq_true_iff.mp ht0
  exact ⟨beq_iff_eq.mp ht.1, beq_iff_eq.mp ht.2⟩

theorem mirStepsConverges_of_runMirToBlock_reached {body : CapturedMir}
    {target : BasicBlockIdx} {s s' : MachineState} {post : MirOutcome → Prop}
    (h : PureMirExec.runMirToBlock body target s = .reached s') :
    Anneal.MirFuelFree.MirStepsConverges body s (· = s') post :=
  mirStepsConverges_of_stepsTo (stepsTo_of_runToTarget_reached h)

theorem mirWpConverges_of_runMirToBlock_halted {body : CapturedMir}
    {target : BasicBlockIdx} {s : MachineState} {v : MirOutcome} {post : MirOutcome → Prop}
    (h : PureMirExec.runMirToBlock body target s = .halted v) (hp : post v) :
    Anneal.MirFuelFree.MirWpConverges body s post :=
  mirWpConverges_of_wpConverges (wpConverges_of_runToTarget_halted h hp)

theorem mirNoCallWpConverges_of_runMirToBlock_halted {body : CapturedMir}
    {target : BasicBlockIdx} {s : MachineState} {v : MirOutcome} {post : MirOutcome → Prop}
    (h : PureMirExec.runMirToBlock body target s = .halted v) (hp : post v) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s post :=
  mirNoCallWpConverges_of_wpConverges (wpConverges_of_runToTarget_halted h hp)

theorem not_wpConverges_of_runMirToBlock_stuck {body : CapturedMir}
    {target : BasicBlockIdx} {s : MachineState} {post : MirOutcome → Prop}
    (h : PureMirExec.runMirToBlock body target s = .stuck) :
    ¬ WpConverges (mirStep body) s post :=
  not_wpConverges_of_runToTarget_stuck h

theorem pureMirStepsConverges_of_stepsTo {body : CapturedMir} {ps : PureState}
    {mid : PureState → Prop} {post : Value → Prop}
    (h : StepsTo (mirStep body) (ps.toMachineState emptyMemory)
      (fun ms' => mid (PureState.ofMachineState ms'))) :
    PureMirStepsConverges body ps mid post :=
  mirStepsConverges_of_stepsTo h

theorem pureMirConverges_of_wpConverges {body : CapturedMir} {ps : PureState}
    {post : Value → Prop}
    (h : WpConverges (mirStep body) (ps.toMachineState emptyMemory)
      (mirNormalPost (fun retVal _ => post retVal))) :
    PureMirConverges body ps post :=
  mirWpConverges_of_wpConverges h

theorem pureMirStepsConverges_of_runMirToBlock_reached {body : CapturedMir}
    {target : BasicBlockIdx} {ps ps' : PureState} {post : Value → Prop}
    (h : PureMirExec.runMirToBlock body target (ps.toMachineState emptyMemory) =
      .reached (ps'.toMachineState emptyMemory)) :
    PureMirStepsConverges body ps (· = ps') post := by
  have hs := stepsTo_of_runToTarget_reached h
  refine pureMirStepsConverges_of_stepsTo (hs.mono ?_)
  intro ms' hms'
  rw [hms', PureState.ofMachineState_toMachineState]

theorem pureMirConverges_of_runMirToBlock_halted {body : CapturedMir}
    {target : BasicBlockIdx} {ps : PureState} {v : Value} {mem : Memory} {post : Value → Prop}
    (h : PureMirExec.runMirToBlock body target (ps.toMachineState emptyMemory) =
      .halted (.normal (v, mem)))
    (hp : post v) :
    PureMirConverges body ps post :=
  mirWpConverges_of_runMirToBlock_halted h hp

end Anneal.PureMirExec

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

/-!
## Single-Pass Bounds-Checked Slot Normalization (`setSpineChecked?` & `forcePureEnv`)
-/

section ForcePureEnv

/-- Projection of the `n`-slot prefix of a frame, padding missing slots with `d`.
Pattern-matches on `env` once per slot so symbolic frames are never duplicated
across `headD`/`tail` projections. -/
def forcePureEnvD {α : Type} (d : α) : Nat → List α → List α
  | 0, _ => []
  | n + 1, [] => d :: forcePureEnvD d n []
  | n + 1, x :: xs => x :: forcePureEnvD d n xs

/-- **`forcePureEnv`**: projection-based normalization of the `n`-slot prefix. -/
def forcePureEnv {α : Type} [Inhabited α] (n : Nat) (env : List α) : List α :=
  forcePureEnvD default n env

theorem length_forcePureEnvD {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α), (forcePureEnvD d n env).length = n
  | 0, _ => rfl
  | n + 1, [] => by simp only [forcePureEnvD, List.length_cons, length_forcePureEnvD d n []]
  | n + 1, _ :: xs => by simp only [forcePureEnvD, List.length_cons, length_forcePureEnvD d n xs]

theorem forcePureEnvD_eq_self {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α), env.length = n → forcePureEnvD d n env = env
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | n + 1, [], h => absurd h.symm (Nat.succ_ne_zero n)
  | n + 1, _ :: xs, h => by
    have h' : xs.length = n := Nat.succ.inj h
    simp only [forcePureEnvD, forcePureEnvD_eq_self d n xs h']

/-- **Exact identity on well-sized frames**. -/
theorem forcePureEnv_eq_self {α : Type} [Inhabited α] (n : Nat) (env : List α)
    (h : env.length = n) : forcePureEnv n env = env :=
  forcePureEnvD_eq_self default n env h

/-- Closed form under arbitrary frame lengths (truncates when `n < env.length`
and pads with `n - env.length` copies of `d` when `env.length < n`). -/
theorem forcePureEnvD_eq_take_append_replicate {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α),
      forcePureEnvD d n env = env.take n ++ List.replicate (n - env.length) d
  | 0, _ => by
    simp only [forcePureEnvD, List.take_zero, Nat.zero_sub, List.replicate_zero, List.append_nil]
  | n + 1, [] => by
    simp only [forcePureEnvD, List.take_nil, List.nil_append, List.length_nil, Nat.sub_zero,
      List.replicate_succ, forcePureEnvD_eq_take_append_replicate d n []]
  | n + 1, _ :: xs => by
    simp only [forcePureEnvD, List.take_succ_cons, List.cons_append, List.length_cons,
      Nat.succ_sub_succ_eq_sub, forcePureEnvD_eq_take_append_replicate d n xs]

/-- **Length-mismatch failure**: when `env.length ≠ n`, `forcePureEnv n env`
differs from `env`. -/
theorem forcePureEnv_ne_self_of_length_ne {α : Type} [Inhabited α] {n : Nat} {env : List α}
    (hne : env.length ≠ n) : forcePureEnv n env ≠ env := by
  intro heq
  have hlen := congrArg List.length heq
  rw [forcePureEnv, length_forcePureEnvD] at hlen
  exact hne hlen.symm

/-- **Exact biconditional**: `forcePureEnv n env = env` iff `env.length = n`. -/
theorem forcePureEnv_eq_self_iff {α : Type} [Inhabited α] (n : Nat) (env : List α) :
    forcePureEnv n env = env ↔ env.length = n :=
  ⟨fun h => by
    have hlen := congrArg List.length h
    rw [forcePureEnv, length_forcePureEnvD] at hlen
    exact hlen.symm,
   forcePureEnv_eq_self n env⟩

theorem getD_zero_eq_headD {α : Type} (env : List α) (d : α) : env.getD 0 d = env.headD d := by
  cases env <;> rfl

theorem getD_succ_eq_tail {α : Type} (env : List α) (i : Nat) (d : α) :
    env.getD (i + 1) d = env.tail.getD i d := by
  cases env <;> rfl

theorem getElem?_forcePureEnvD {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α) (i : Nat),
      (forcePureEnvD d n env)[i]? = if i < n then some (env.getD i d) else none
  | 0, _, _ => by simp [forcePureEnvD]
  | n + 1, [], 0 => by
    simp only [forcePureEnvD, List.getElem?_cons_zero, List.getD_nil, Nat.zero_lt_succ, ↓reduceIte]
  | n + 1, _ :: _, 0 => by
    simp only [forcePureEnvD, List.getElem?_cons_zero, List.getD_cons_zero, Nat.zero_lt_succ, ↓reduceIte]
  | n + 1, [], i + 1 => by
    simp only [forcePureEnvD, List.getElem?_cons_succ, getElem?_forcePureEnvD d n [] i,
      List.getD_nil, Nat.add_lt_add_iff_right]
  | n + 1, _ :: xs, i + 1 => by
    simp only [forcePureEnvD, List.getElem?_cons_succ, getElem?_forcePureEnvD d n xs i,
      List.getD_cons_succ, Nat.add_lt_add_iff_right]

/-- **Slot projection**: reads through `forcePureEnv` are slot reads. -/
theorem getElem?_forcePureEnv {α : Type} [Inhabited α] (n : Nat) (env : List α) (i : Nat) :
    (forcePureEnv n env)[i]? = if i < n then some (env.getD i default) else none :=
  getElem?_forcePureEnvD default n env i

theorem forcePureEnvD_set_comm {α : Type} (d : α) :
    ∀ (n : Nat) (env : List α) (i : Nat) (v : α), (i < env.length ∨ n ≤ i) →
      forcePureEnvD d n (env.set i v) = (forcePureEnvD d n env).set i v
  | 0, _, _, _, _ => rfl
  | n + 1, [], i, v, h => by
    have hi : n + 1 ≤ i := by
      rcases h with h | h
      · exact absurd h (Nat.not_lt_zero i)
      · exact h
    rw [List.set_eq_of_length_le (by simp), List.set_eq_of_length_le (by rw [length_forcePureEnvD]; exact hi)]
  | n + 1, _ :: _, 0, _, _ => rfl
  | n + 1, _ :: xs, i + 1, v, h => by
    have h' : i < xs.length ∨ n ≤ i := by
      rcases h with h | h
      · left; simpa using h
      · right; omega
    simp only [List.set_cons_succ, forcePureEnvD, forcePureEnvD_set_comm d n xs i v h']

/-- **Projection commutes with in-range slot updates**. The side condition is
necessary (see `forcePureEnv_set_comm_counterexample`). -/
theorem forcePureEnv_set_comm {α : Type} [Inhabited α] (n : Nat) (env : List α) (i : Nat) (v : α)
    (h : i < env.length ∨ n ≤ i) :
    forcePureEnv n (env.set i v) = (forcePureEnv n env).set i v :=
  forcePureEnvD_set_comm default n env i v h

/-- Without the side condition the commutation fails: updating a padding slot. -/
theorem forcePureEnv_set_comm_counterexample :
    forcePureEnv 2 (([] : List Nat).set 0 5) ≠ (forcePureEnv 2 ([] : List Nat)).set 0 5 := by
  decide

/-- **Exact side condition** of `forcePureEnv_set_comm`: projection commutes with
`List.set` iff the slot is in range, lies outside the projected prefix, or the
written value coincides with the padding value `default` (the only way an
out-of-range write into the padded region can be invisible). -/
theorem forcePureEnv_set_comm_iff {α : Type} [Inhabited α] (n : Nat) (env : List α) (i : Nat)
    (v : α) :
    forcePureEnv n (env.set i v) = (forcePureEnv n env).set i v ↔
      (i < env.length ∨ n ≤ i ∨ v = default) := by
  have hlenF : (forcePureEnv n env).length = n := length_forcePureEnvD default n env
  have hgetD : env.length ≤ i → env.getD i default = default := fun hge => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rfl
  constructor
  · intro h
    rcases Nat.lt_or_ge i env.length with hlt | hge
    · exact Or.inl hlt
    · rcases Nat.lt_or_ge i n with hin | hni
      · refine Or.inr (Or.inr ?_)
        have h_i := congrArg (fun l => l[i]?) h
        rw [List.set_eq_of_length_le hge, getElem?_forcePureEnv, ite_eq_left hin,
          List.getElem?_set_self (by rw [hlenF]; exact hin), hgetD hge] at h_i
        exact (Option.some.inj h_i).symm
      · exact Or.inr (Or.inl hni)
  · rintro (h | h | h)
    · exact forcePureEnv_set_comm n env i v (Or.inl h)
    · exact forcePureEnv_set_comm n env i v (Or.inr h)
    · subst h
      rcases Nat.lt_or_ge i env.length with hlt | hge
      · exact forcePureEnv_set_comm n env i default (Or.inl hlt)
      · rcases Nat.lt_or_ge i n with hin | hni
        · rw [List.set_eq_of_length_le hge]
          apply List.ext_getElem?
          intro j
          rw [List.getElem?_set]
          by_cases hij : i = j
          · subst hij
            rw [ite_eq_left rfl, ite_eq_left (by rw [hlenF]; exact hin), getElem?_forcePureEnv,
              ite_eq_left hin, hgetD hge]
          · rw [ite_eq_right hij]
        · exact forcePureEnv_set_comm n env i default (Or.inr hni)

/-- Collapse lemma: a chain equals its projection-normal form. -/
theorem eq_of_forcePureEnv {α : Type} [Inhabited α] {n : Nat} {chain flat : List α}
    (hlen : chain.length = n) (h : forcePureEnv n chain = flat) : chain = flat := by
  rw [← h, forcePureEnv_eq_self n chain hlen]

/-- **Symbolic chained-update collapse by `rfl`**: four nested `List.set`
updates over symbolic slot values collapse to one flat list literal by kernel
reduction of the projection, without `List.set` commutation `simp` lemmas. -/
theorem chained_sets_collapse_rfl (a b c d x y z : Nat) :
    (((([a, b, c, d].set 0 x).set 2 y).set 0 z).set 3 (x + y)) = [z, b, y, x + y] :=
  eq_of_forcePureEnv (n := 4) rfl rfl

/-- Spine-forcing normalizer (the generic form of `forcePureEnv?`): reducing
`forceSpine? l` to `some _` materializes the whole list spine in one pass. -/
def forceSpine? {α : Type} : List α → Option (List α)
  | [] => some []
  | x :: xs =>
    match forceSpine? xs with
    | some ys => some (x :: ys)
    | none => none

theorem forceSpine?_eq_some {α : Type} : ∀ (l : List α), forceSpine? l = some l
  | [] => rfl
  | _ :: xs => by simp only [forceSpine?, forceSpine?_eq_some xs]

theorem forceSpine?_eq_some_forcePureEnv {α : Type} [Inhabited α] (l : List α) :
    forceSpine? l = some (forcePureEnv l.length l) := by
  rw [forceSpine?_eq_some, forcePureEnv_eq_self l.length l rfl]

/-- Single-pass spine-forcing slot update: forces the list spine up to index `i`
and stops at `0` (`some (v :: xs)`), avoiding a second full-list traversal over
the untouched suffix `xs`. -/
def setSpine? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => some []
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, i + 1, v =>
    match setSpine? xs i v with
    | some xs' => some (x :: xs')
    | none => none

theorem setSpine?_eq_some_set {α : Type} :
    ∀ (env : List α) (i : Nat) (v : α), setSpine? env i v = some (env.set i v)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, v => by simp only [setSpine?, setSpine?_eq_some_set xs i v, List.set_cons_succ]

theorem setSpine?_eq_forceSpine?_set {α : Type} (env : List α) (i : Nat) (v : α) :
    setSpine? env i v = forceSpine? (env.set i v) := by
  rw [setSpine?_eq_some_set, forceSpine?_eq_some]

/-- Sequential local updates (`env[i₁] := v₁; …; env[i_K] := v_K`). -/
def applySlotUpdates {α : Type} (env : List α) (ups : List (Nat × α)) : List α :=
  ups.foldl (fun e u => e.set u.1 u.2) env

/-- Step-wise normalized execution: after every update the modified prefix spine
is forced via `setSpine?`, so the next update always acts on a flat literal. -/
def applySlotUpdatesForced {α : Type} : List (Nat × α) → List α → Option (List α)
  | [], env => some env
  | u :: ups, env =>
    match setSpine? env u.1 u.2 with
    | some env' => applySlotUpdatesForced ups env'
    | none => none

theorem applySlotUpdatesForced_eq {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α),
      applySlotUpdatesForced ups env = some (applySlotUpdates env ups)
  | [], _ => rfl
  | _ :: ups, _ => by
    simp only [applySlotUpdatesForced, setSpine?_eq_some_set, applySlotUpdates, List.foldl]
    exact applySlotUpdatesForced_eq ups _

/-- Soundness of step-wise normalization: a `rfl` proof of the forced run
proves the unnormalized update sequence. -/
theorem applySlotUpdates_eq_of_forced {α : Type} {env flat : List α} {ups : List (Nat × α)}
    (h : applySlotUpdatesForced ups env = some flat) : applySlotUpdates env ups = flat := by
  rw [applySlotUpdatesForced_eq] at h
  exact Option.some.inj h

theorem length_applySlotUpdates {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α), (applySlotUpdates env ups).length = env.length
  | [], _ => rfl
  | u :: ups, env => by
    simp only [applySlotUpdates, List.foldl] at *
    rw [show List.foldl (fun e u => e.set u.1 u.2) (env.set u.1 u.2) ups =
      applySlotUpdates (env.set u.1 u.2) ups from rfl, length_applySlotUpdates ups, List.length_set]

/-- **Single-pass forcing is `forcePureEnv`-normalization of the update**:
`setSpine?` returns exactly the `forcePureEnv` normal form of `env.set i v`. -/
theorem setSpine?_eq_some_forcePureEnv_set {α : Type} [Inhabited α] (env : List α) (i : Nat)
    (v : α) : setSpine? env i v = some (forcePureEnv env.length (env.set i v)) := by
  rw [setSpine?_eq_some_set, forcePureEnv_eq_self env.length (env.set i v) List.length_set]

/-- **The step-wise run computes the `forcePureEnv` normal form** of the
unnormalized update sequence (`applySlotUpdates`). -/
theorem applySlotUpdatesForced_eq_forcePureEnv {α : Type} [Inhabited α] (ups : List (Nat × α))
    (env : List α) :
    applySlotUpdatesForced ups env = some (forcePureEnv env.length (applySlotUpdates env ups)) := by
  rw [applySlotUpdatesForced_eq, forcePureEnv_eq_self env.length _ (length_applySlotUpdates ups env)]

/-- Twelve symbolic updates collapse by `rfl` through step-wise forcing. -/
theorem slotUpdates_collapse_forced (a₀ a₁ a₂ a₃ a₄ a₅ x₁ x₂ x₃ x₄ x₅ x₆ : Nat) :
    applySlotUpdates [a₀, a₁, a₂, a₃, a₄, a₅]
      [(3, x₁), (0, x₂), (3, x₃), (5, x₄), (1, x₅), (0, x₆),
       (2, x₁ + x₂), (4, x₃), (5, x₆), (1, x₂), (3, x₄), (0, x₅)] =
      [x₅, x₂, x₁ + x₂, x₄, x₃, x₆] :=
  applySlotUpdates_eq_of_forced rfl

/-- Specialization of `forcePureEnv` to `PureEnv` (`List SlotState`), padding
with `.uninit`. -/
def forcePureEnvSlots (n : Nat) (env : PureEnv) : PureEnv :=
  forcePureEnvD LocalSlot.uninit n env

theorem forcePureEnvSlots_eq_self (env : PureEnv) :
    forcePureEnvSlots env.length env = env :=
  forcePureEnvD_eq_self _ env.length env rfl

/-- **Bridge to `forcePureEnv?`**: the generic spine forcer agrees with
`forcePureEnv?` on every `PureEnv`. -/
theorem forceSpine?_eq_live (env : PureEnv) :
    forceSpine? env = forcePureEnv? env := by
  rw [forceSpine?_eq_some, forcePureEnv?_eq_some]

/-- Bridge to the trusted `Trusted.Sequence.set?` used by `evalPureStmt`:
a successful slot update commutes with the projection. -/
theorem forcePureEnvSlots_set? {env env' : PureEnv} {loc : Nat}
    {s : LocalSlot}
    (h : Trusted.Sequence.set? env loc s = some env') :
    forcePureEnvSlots env.length env' = (forcePureEnvSlots env.length env).set loc s := by
  unfold Trusted.Sequence.set? at h
  by_cases hlt : loc < env.length
  · rw [ite_eq_left hlt] at h
    cases h
    exact forcePureEnvD_set_comm _ env.length env loc s (Or.inl hlt)
  · rw [ite_eq_right hlt] at h
    cases h

/-- **Bridge from the trusted slot update `Trusted.Sequence.set?`** to
single-pass forcing: in range the update *is* `setSpine?`, out of range it fails. -/
theorem liveSet?_eq_setSpine? {α : Type} (env : List α) (loc : Nat) (v : α) :
    Trusted.Sequence.set? env loc v = if loc < env.length then setSpine? env loc v else none := by
  unfold Trusted.Sequence.set?
  rw [setSpine?_eq_some_set]

/-- Sequential slot updates through `Trusted.Sequence.set?` (failing on the
first out-of-range slot). -/
def applySlotUpdatesLive? {α : Type} : List (Nat × α) → List α → Option (List α)
  | [], env => some env
  | u :: ups, env =>
    match Trusted.Sequence.set? env u.1 u.2 with
    | some env' => applySlotUpdatesLive? ups env'
    | none => none

/-- **Live update chains are computed by the step-wise forced run**: when every
updated slot is in range, the `Trusted.Sequence.set?` chain equals
`applySlotUpdatesForced`. -/
theorem applySlotUpdatesLive?_eq_forced {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α), (∀ u ∈ ups, u.1 < env.length) →
      applySlotUpdatesLive? ups env = applySlotUpdatesForced ups env
  | [], _, _ => rfl
  | u :: ups, env, h => by
    have hu : u.1 < env.length := h u (List.mem_cons_self ..)
    have hrest : ∀ w ∈ ups, w.1 < (env.set u.1 u.2).length := fun w hw => by
      rw [List.length_set]
      exact h w (List.mem_cons_of_mem _ hw)
    have hlive : Trusted.Sequence.set? env u.1 u.2 = some (env.set u.1 u.2) := by
      unfold Trusted.Sequence.set?
      rw [ite_eq_left hu]
    simp only [applySlotUpdatesLive?, applySlotUpdatesForced, hlive, setSpine?_eq_some_set]
    exact applySlotUpdatesLive?_eq_forced ups (env.set u.1 u.2) hrest

/-- An out-of-range update makes `applySlotUpdatesLive?` fail. -/
theorem applySlotUpdatesLive?_oob {α : Type} (u : Nat × α) (ups : List (Nat × α)) (env : List α)
    (h : env.length ≤ u.1) : applySlotUpdatesLive? (u :: ups) env = none := by
  have hlive : Trusted.Sequence.set? env u.1 u.2 = none := by
    unfold Trusted.Sequence.set?
    rw [ite_eq_right (Nat.not_lt.mpr h)]
  simp only [applySlotUpdatesLive?, hlive]

/-- Two-pass step-wise forcing with the structure of `evalPureStmtNorm` /
`set?_of_forcePureEnv?`: a bounds-checked `Trusted.Sequence.set?` followed by
a full spine-forcing pass (`forceSpine?`). -/
def applySlotUpdatesTwoPass {α : Type} : List (Nat × α) → List α → Option (List α)
  | [], env => some env
  | u :: ups, env =>
    match (Trusted.Sequence.set? env u.1 u.2).bind forceSpine? with
    | some env' => applySlotUpdatesTwoPass ups env'
    | none => none

/-- The two-pass run computes the `Trusted.Sequence.set?` chain. -/
theorem applySlotUpdatesTwoPass_eq_live? {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α),
      applySlotUpdatesTwoPass ups env = applySlotUpdatesLive? ups env
  | [], _ => rfl
  | u :: ups, env => by
    cases h : Trusted.Sequence.set? env u.1 u.2 with
    | none => simp only [applySlotUpdatesTwoPass, applySlotUpdatesLive?, h, Option.bind_none]
    | some e =>
      simp only [applySlotUpdatesTwoPass, applySlotUpdatesLive?, h, Option.bind_some, forceSpine?_eq_some]
      exact applySlotUpdatesTwoPass_eq_live? ups e

/-- **Soundness of the two-pass strategy**: a successful run proves the
unnormalized update sequence. -/
theorem applySlotUpdates_eq_of_twoPass {α : Type} :
    ∀ {ups : List (Nat × α)} {env flat : List α},
      applySlotUpdatesTwoPass ups env = some flat → applySlotUpdates env ups = flat
  | [], _, _, h => Option.some.inj h
  | u :: ups, env, _, h => by
    have hset : ∀ e, Trusted.Sequence.set? env u.1 u.2 = some e → e = env.set u.1 u.2 := by
      intro e he
      unfold Trusted.Sequence.set? at he
      by_cases hlt : u.1 < env.length
      · rw [ite_eq_left hlt] at he
        exact (Option.some.inj he).symm
      · rw [ite_eq_right hlt] at he
        cases he
    cases hs : Trusted.Sequence.set? env u.1 u.2 with
    | none => simp only [applySlotUpdatesTwoPass, hs, Option.bind_none] at h; cases h
    | some e =>
      simp only [applySlotUpdatesTwoPass, hs, Option.bind_some, forceSpine?_eq_some] at h
      rw [show applySlotUpdates env (u :: ups) = applySlotUpdates (env.set u.1 u.2) ups from rfl,
        ← hset e hs]
      exact applySlotUpdates_eq_of_twoPass h

/-- Single-pass constructor-forcing slot update over `PureEnv` (`List LocalSlot`):
checks bounds like `Trusted.Sequence.set?`, forces both the `List` spine and
`LocalSlot` constructors (`.dead`, `.uninit`, `.init v`) along `[0..loc]`, and
stops at `loc` without a second pass over the tail. -/
def setPureEnvSlot? : PureEnv → Nat → LocalSlot → Option PureEnv
  | [], _, _ => none
  | _ :: rest, 0, .dead => some (.dead :: rest)
  | _ :: rest, 0, .uninit => some (.uninit :: rest)
  | _ :: rest, 0, .init v => some (.init v :: rest)
  | .dead :: rest, i + 1, s =>
    match setPureEnvSlot? rest i s with
    | some rest' => some (.dead :: rest')
    | none => none
  | .uninit :: rest, i + 1, s =>
    match setPureEnvSlot? rest i s with
    | some rest' => some (.uninit :: rest')
    | none => none
  | .init v :: rest, i + 1, s =>
    match setPureEnvSlot? rest i s with
    | some rest' => some (.init v :: rest')
    | none => none

/-- **Single-pass `setPureEnvSlot?` equals `Trusted.Sequence.set?`**. -/
theorem setPureEnvSlot?_eq_set? :
    ∀ (env : PureEnv) (loc : Nat) (s : LocalSlot),
      setPureEnvSlot? env loc s = Trusted.Sequence.set? env loc s
  | [], _, _ => by
    simp [setPureEnvSlot?, Trusted.Sequence.set?]
  | x :: rest, 0, s => by
    unfold Trusted.Sequence.set?
    have h0 : 0 < (x :: rest).length := Nat.zero_lt_succ rest.length
    rw [ite_eq_left h0]
    cases s <;> rfl
  | x :: rest, i + 1, s => by
    have ih := setPureEnvSlot?_eq_set? rest i s
    unfold Trusted.Sequence.set? at ih ⊢
    by_cases hlt : i < rest.length
    · have hlt' : i + 1 < (x :: rest).length := Nat.succ_lt_succ hlt
      rw [ite_eq_left hlt] at ih
      rw [ite_eq_left hlt']
      cases x <;> simp only [setPureEnvSlot?, ih, List.set_cons_succ]
    · have hlt' : ¬ i + 1 < (x :: rest).length := fun h => hlt (Nat.lt_of_succ_lt_succ h)
      rw [ite_eq_right hlt] at ih
      rw [ite_eq_right hlt']
      cases x <;> simp only [setPureEnvSlot?, ih]

/-- **Single-pass `setPureEnvSlot?` equals `(set? env loc s).bind forcePureEnv?`**. -/
theorem setPureEnvSlot?_eq_live_bind_forcePureEnv? (env : PureEnv)
    (loc : Nat) (s : LocalSlot) :
    setPureEnvSlot? env loc s =
      (Trusted.Sequence.set? env loc s).bind forcePureEnv? := by
  rw [setPureEnvSlot?_eq_set?]
  cases Trusted.Sequence.set? env loc s with
  | none => rfl
  | some env' => exact (forcePureEnv?_eq_some env').symm

/-- **Bridge from `evalPureStmtNorm` to `forceSpine?`**:
`evalPureStmtNorm` equals `evalPureStmt` followed by `forceSpine?`. -/
theorem evalPureStmtNorm_eq_bind_forceSpine?
    (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat)
    (env : PureEnv) (stmt : Statement) :
    evalPureStmtNorm body bbIdx stmtIdx env stmt =
      (evalPureStmt body bbIdx stmtIdx env stmt).bind forceSpine? := by
  unfold evalPureStmtNorm
  cases evalPureStmt body bbIdx stmtIdx env stmt with
  | none => rfl
  | some rawEnv => exact (forceSpine?_eq_live rawEnv).symm

/-- **Bounds-checked single-pass spine-forcing slot update**: returns `none`
out of bounds and forces the modified prefix `[0..loc]` in a single pass
without calling `env.length`, traversing the suffix `[loc+1..)`, or
pattern-matching on untouched `LocalSlot` elements. -/
def setSpineChecked? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, i + 1, v =>
    match setSpineChecked? xs i v with
    | some xs' => some (x :: xs')
    | none => none

/-- **Exact unconditional agreement with `Trusted.Sequence.set?`**:
`setSpineChecked?` equals `Trusted.Sequence.set?` on every list and index
(both in-bounds and out-of-bounds, with no `loc < env.length` side condition). -/
theorem setSpineChecked?_eq_live_set? {α : Type} :
    ∀ (env : List α) (loc : Nat) (v : α),
      setSpineChecked? env loc v = Trusted.Sequence.set? env loc v
  | [], _, _ => by
    simp [setSpineChecked?, Trusted.Sequence.set?]
  | x :: xs, 0, _ => by
    unfold Trusted.Sequence.set?
    have h0 : 0 < (x :: xs).length := Nat.zero_lt_succ xs.length
    rw [ite_eq_left h0]
    rfl
  | x :: xs, i + 1, v => by
    have ih := setSpineChecked?_eq_live_set? xs i v
    unfold Trusted.Sequence.set? at ih ⊢
    by_cases hlt : i < xs.length
    · have hlt' : i + 1 < (x :: xs).length := Nat.succ_lt_succ hlt
      rw [ite_eq_left hlt] at ih
      rw [ite_eq_left hlt']
      simp only [setSpineChecked?, ih, List.set_cons_succ]
    · have hlt' : ¬ i + 1 < (x :: xs).length := fun h => hlt (Nat.lt_of_succ_lt_succ h)
      rw [ite_eq_right hlt] at ih
      rw [ite_eq_right hlt']
      simp only [setSpineChecked?, ih]

/-- **Drop-in single-pass replacement for `(set? env loc s).bind forcePureEnv?`**
that also reduces when untouched prefix slots are symbolic `LocalSlot` variables. -/
theorem setSpineChecked?_eq_live_bind_forcePureEnv? (env : PureEnv)
    (loc : Nat) (s : LocalSlot) :
    setSpineChecked? env loc s =
      (Trusted.Sequence.set? env loc s).bind forcePureEnv? := by
  rw [setSpineChecked?_eq_live_set?]
  cases Trusted.Sequence.set? env loc s with
  | none => rfl
  | some env' => exact (forcePureEnv?_eq_some env').symm

/-- **Symbolic `LocalSlot` framing by `rfl`**: unlike `forcePureEnv?` and
`setPureEnvSlot?` (both of which pattern-match on `.dead`/`.uninit`/`.init` at
every prefix element and get stuck when an untouched slot is a symbolic
`s₀ : LocalSlot`), `setSpineChecked?` reduces to `some [...]` by `rfl`. -/
theorem setSpineChecked?_symbolic_slot_rfl
    (s₀ s₁ : LocalSlot) (v₂ v₂' : Value) :
    setSpineChecked? [s₀, s₁, .init v₂] 2 (.init v₂') = some [s₀, s₁, .init v₂'] :=
  rfl

/-- Bounds-checked single-pass step-wise update chain. -/
def applySlotUpdatesChecked {α : Type} : List (Nat × α) → List α → Option (List α)
  | [], env => some env
  | u :: ups, env =>
    match setSpineChecked? env u.1 u.2 with
    | some env' => applySlotUpdatesChecked ups env'
    | none => none

/-- `applySlotUpdatesChecked` equals the `Trusted.Sequence.set?` chain on
every update list (both in-bounds and out-of-bounds). -/
theorem applySlotUpdatesChecked_eq_live? {α : Type} :
    ∀ (ups : List (Nat × α)) (env : List α),
      applySlotUpdatesChecked ups env = applySlotUpdatesLive? ups env
  | [], _ => rfl
  | u :: ups, env => by
    simp only [applySlotUpdatesChecked, applySlotUpdatesLive?, setSpineChecked?_eq_live_set?]
    cases Trusted.Sequence.set? env u.1 u.2 with
    | none => rfl
    | some env' => exact applySlotUpdatesChecked_eq_live? ups env'

/-- **Soundness of bounds-checked single-pass normalization**: a `rfl` proof of
`applySlotUpdatesChecked` proves the unnormalized `applySlotUpdates` chain. -/
theorem applySlotUpdates_eq_of_checked {α : Type} {ups : List (Nat × α)} {env flat : List α}
    (h : applySlotUpdatesChecked ups env = some flat) : applySlotUpdates env ups = flat := by
  rw [applySlotUpdatesChecked_eq_live?, ← applySlotUpdatesTwoPass_eq_live?] at h
  exact applySlotUpdates_eq_of_twoPass h

/-- **Soundness of the bare `Trusted.Sequence.set?` chain** without the
`forcePureEnv?` pass. -/
theorem applySlotUpdates_eq_of_live? {α : Type} {ups : List (Nat × α)} {env flat : List α}
    (h : applySlotUpdatesLive? ups env = some flat) : applySlotUpdates env ups = flat := by
  rw [← applySlotUpdatesTwoPass_eq_live?] at h
  exact applySlotUpdates_eq_of_twoPass h

/-- **Single-pass drop-in replacement for `set?_of_forcePureEnv?`**:
proves `Trusted.Sequence.set? env loc s = some env'` directly from `setSpineChecked?`. -/
theorem set?_of_setSpineChecked? {env env' : PureEnv}
    {loc : Local} {s : LocalSlot}
    (h : setSpineChecked? env loc s = some env') :
    Trusted.Sequence.set? env loc s = some env' := by
  rwa [← setSpineChecked?_eq_live_set?]

/-- **Single-pass drop-in replacement for `evalPureStmtNorm_assign_local_of_evalRvalue`**:
replaces the two-pass `(set? env dstLoc (.init val)).bind forcePureEnv? = some env'`
premise with single-pass `setSpineChecked?` (without modifying `trusted/lean/`
and without getting stuck on symbolic `LocalSlot` prefix entries). -/
theorem evalPureStmtNorm_assign_local_of_setSpineChecked?
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat}
    {env env' : PureEnv} {dstLoc : Local}
    {rv : Rvalue} {span : String}
    {val : Value} {oldSlot : LocalSlot}
    (h_pure : isPureStatement
      (.assign { local_ := dstLoc, projection := [] } rv) = true)
    (h_rv : evalRvalue env rv emptyMemory body.localDecls body.layouts =
      .ok val env emptyMemory)
    (h_get : Trusted.Sequence.get? env dstLoc = some oldSlot)
    (h_live : oldSlot ≠ .dead)
    (h_set : setSpineChecked? env dstLoc (.init val) = some env') :
    evalPureStmtNorm body bbIdx stmtIdx env
      { kind := .assign { local_ := dstLoc, projection := [] } rv, span := span } = some env' := by
  rw [setSpineChecked?_eq_live_bind_forcePureEnv?] at h_set
  exact evalPureStmtNorm_assign_local_of_evalRvalue
    h_pure h_rv h_get h_live h_set

/-- Unforced multi-statement pure execution matching `evalPureStmtsN` without
the per-statement `forcePureEnv?` pass. -/
def evalPureStmtsUnforced
    (body : CapturedMir) (bbIdx : BasicBlockIdx)
    (stmts : List Statement) :
    Nat → Nat → PureEnv → Option PureEnv
  | 0, _, env => some env
  | n + 1, stmtIdx, env =>
    match Trusted.Sequence.get? stmts stmtIdx with
    | some stmt =>
      match evalPureStmt body bbIdx stmtIdx env stmt with
      | some env₁ => evalPureStmtsUnforced body bbIdx stmts n (stmtIdx + 1) env₁
      | none => none
    | none => none

/-- **Bridge from multi-statement `evalPureStmtsN` to unforced `evalPureStmt` execution**:
extensionally identical on every block segment. Computationally they differ:
the per-statement forcing pass of `evalPureStmtsN` is what keeps `rfl`
evaluation linear, so the unforced form is a specification, not a faster evaluator. -/
theorem evalPureStmtsN_eq_unforced
    (body : CapturedMir) (bbIdx : BasicBlockIdx)
    (stmts : List Statement) :
    ∀ (n stmtIdx : Nat) (env : PureEnv),
      evalPureStmtsN body bbIdx stmts n stmtIdx env =
        evalPureStmtsUnforced body bbIdx stmts n stmtIdx env
  | 0, _, env => forcePureEnv?_eq_some env
  | n + 1, stmtIdx, env => by
    unfold evalPureStmtsN evalPureStmtsUnforced
    cases Trusted.Sequence.get? stmts stmtIdx with
    | none => rfl
    | some stmt =>
      dsimp only
      rw [evalPureStmtNorm_eq_evalPureStmt]
      cases evalPureStmt body bbIdx stmtIdx env stmt with
      | none => rfl
      | some env₁ => exact evalPureStmtsN_eq_unforced body bbIdx stmts n (stmtIdx + 1) env₁

/-- Untrusted single-pass pure statement normalizer: uses `setSpineChecked?`
directly on local `.storageLive`, `.storageDead`, `.deinit`, and `.assign`
updates so modified prefixes are normalized in a single pass without calling
`env.length` or pattern-matching on untouched `LocalSlot` constructors, while
remaining extensionally identical to `evalPureStmt` and `evalPureStmtNorm`. -/
def evalPureStmtChecked (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat)
    (env : PureEnv) (stmt : Statement) : Option PureEnv :=
  if isPureStatement stmt.kind then
    match stmt.kind with
    | .nop | .coverage | .constEvalCounter => some env
    | .storageLive loc =>
      match get? env loc with
      | some _ => setSpineChecked? env loc .uninit
      | none => none
    | .storageDead loc =>
      match get? env loc with
      | some _ => setSpineChecked? env loc .dead
      | none => none
    | .deinit { local_ := loc, projection := [] } =>
      match get? env loc with
      | some .dead => none
      | some _ => setSpineChecked? env loc .uninit
      | none => none
    | .assign { local_ := dstLoc, projection := [] } rv =>
      match evalRvalue env rv emptyMemory body.localDecls body.layouts with
      | .ok val locals₁ mem₁ =>
        match get? locals₁ dstLoc with
        | some .dead => none
        | some _ =>
          match setSpineChecked? locals₁ dstLoc (.init val) with
          | some locals₂ =>
            match mem₁.activeProtectors with
            | [] => some locals₂
            | protHead :: protTail =>
              match hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstLoc .none .nil 0 0 (length mem₁.callStack) with
              | true => none
              | false => some locals₂
          | none => none
        | none => none
      | _ => none
    | _ => (evalPureStmt body bbIdx stmtIdx env stmt).bind forceSpine?
  else none

/-- **Exact agreement between single-pass `evalPureStmtChecked` and `evalPureStmt`**. -/
theorem evalPureStmtChecked_eq_evalPureStmt
    (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat)
    (env : PureEnv) (stmt : Statement) :
    evalPureStmtChecked body bbIdx stmtIdx env stmt =
      evalPureStmt body bbIdx stmtIdx env stmt := by
  rcases stmt with ⟨kind, span⟩
  unfold evalPureStmtChecked
  cases hp : isPureStatement kind with
  | false =>
    unfold evalPureStmt
    rw [hp]
    rfl
  | true =>
    rw [ite_eq_left rfl]
    cases kind with
    | nop | coverage | constEvalCounter =>
      unfold evalPureStmt
      rw [hp]
      rfl
    | storageLive loc | storageDead loc =>
      unfold evalPureStmt
      rw [hp, ite_eq_left rfl]
      dsimp only [evalStmt, PureState.toMachineState, emptyMemory]
      rw [setSpineChecked?_eq_live_set?]
      cases get? env loc with
      | none => rfl
      | some _ =>
        cases set? env loc _ <;> rfl
    | deinit p =>
      rcases p with ⟨loc, proj⟩
      cases proj with
      | nil =>
        unfold evalPureStmt
        rw [hp, ite_eq_left rfl]
        dsimp only [evalStmt, PureState.toMachineState, emptyMemory]
        rw [setSpineChecked?_eq_live_set?]
        cases get? env loc with
        | none => rfl
        | some slot =>
          cases slot with
          | dead => rfl
          | uninit | init _ =>
            cases set? env loc .uninit <;> rfl
      | cons _ _ =>
        dsimp only
        cases evalPureStmt body bbIdx stmtIdx env { kind := .deinit ⟨loc, _ :: _⟩, span := span } with
        | none => rfl
        | some e => exact forceSpine?_eq_some e
    | assign dst rv =>
      rcases dst with ⟨dstLoc, proj⟩
      cases proj with
      | nil =>
        unfold evalPureStmt
        rw [hp, ite_eq_left rfl]
        dsimp only [evalStmt, PureState.toMachineState]
        cases evalRvalue env rv emptyMemory body.localDecls body.layouts with
        | ub | unsupported => rfl
        | ok val locals₁ mem₁ =>
          dsimp only
          rw [setSpineChecked?_eq_live_set?]
          cases get? locals₁ dstLoc with
          | none => rfl
          | some slot =>
            cases slot with
            | dead => rfl
            | uninit | init _ =>
              cases set? locals₁ dstLoc (.init val) with
              | none => rfl
              | some locals₂ =>
                cases mem₁.activeProtectors with
                | nil => rfl
                | cons ph pt =>
                  dsimp only
                  cases hasProtectedWriteConflict mem₁.borrows (ph :: pt) dstLoc .none [] 0 0 (length mem₁.callStack) <;> rfl
      | cons _ _ =>
        dsimp only
        cases evalPureStmt body bbIdx stmtIdx env { kind := .assign ⟨dstLoc, _ :: _⟩ rv, span := span } with
        | none => rfl
        | some e => exact forceSpine?_eq_some e
    | _ =>
      dsimp only
      cases evalPureStmt body bbIdx stmtIdx env _ with
      | none => rfl
      | some e => exact forceSpine?_eq_some e

theorem evalPureStmtChecked_eq_evalPureStmtNorm
    (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat)
    (env : PureEnv) (stmt : Statement) :
    evalPureStmtChecked body bbIdx stmtIdx env stmt =
      evalPureStmtNorm body bbIdx stmtIdx env stmt := by
  rw [evalPureStmtChecked_eq_evalPureStmt, evalPureStmtNorm_eq_evalPureStmt]

/-- Multi-statement pure execution using single-pass `evalPureStmtChecked` and
`forceSpine?`. -/
def evalPureStmtsCheckedN
    (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmts : List Statement) :
    Nat → Nat → PureEnv → Option PureEnv
  | 0, _, env => forceSpine? env
  | n + 1, stmtIdx, env =>
    match Trusted.Sequence.get? stmts stmtIdx with
    | some stmt =>
      match evalPureStmtChecked body bbIdx stmtIdx env stmt with
      | some env₁ => evalPureStmtsCheckedN body bbIdx stmts n (stmtIdx + 1) env₁
      | none => none
    | none => none

theorem evalPureStmtsCheckedN_eq_evalPureStmtsN
    (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmts : List Statement) :
    ∀ (n stmtIdx : Nat) (env : PureEnv),
      evalPureStmtsCheckedN body bbIdx stmts n stmtIdx env =
        evalPureStmtsN body bbIdx stmts n stmtIdx env
  | 0, _, env => forceSpine?_eq_live env
  | n + 1, stmtIdx, env => by
    unfold evalPureStmtsCheckedN evalPureStmtsN
    cases Trusted.Sequence.get? stmts stmtIdx with
    | none => rfl
    | some stmt =>
      dsimp only
      rw [evalPureStmtChecked_eq_evalPureStmtNorm]
      cases evalPureStmtNorm body bbIdx stmtIdx env stmt with
      | none => rfl
      | some env₁ => exact evalPureStmtsCheckedN_eq_evalPureStmtsN body bbIdx stmts n (stmtIdx + 1) env₁

theorem evalPureStmtsCheckedN_eq_unforced
    (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmts : List Statement)
    (n stmtIdx : Nat) (env : PureEnv) :
    evalPureStmtsCheckedN body bbIdx stmts n stmtIdx env =
      evalPureStmtsUnforced body bbIdx stmts n stmtIdx env := by
  rw [evalPureStmtsCheckedN_eq_evalPureStmtsN, evalPureStmtsN_eq_unforced]

/-- Out-of-bounds slot update (`env.length ≤ loc`) deterministically returns
`none` in `setSpineChecked?`. -/
theorem setSpineChecked?_oob_none {α : Type} (env : List α) (loc : Nat) (v : α)
    (h_oob : env.length ≤ loc) :
    setSpineChecked? env loc v = none := by
  rw [setSpineChecked?_eq_live_set?]
  unfold Trusted.Sequence.set?
  rw [ite_eq_right (Nat.not_lt.mpr h_oob)]

/-- Out-of-bounds `.storageLive` / `.storageDead` deterministically returns
`none` in `evalPureStmtChecked`. -/
theorem evalPureStmtChecked_storageLive_oob_none
    (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat)
    (env : PureEnv) (loc : Local) (span : String)
    (h_oob : env.length ≤ loc) :
    evalPureStmtChecked body bbIdx stmtIdx env
      { kind := .storageLive loc, span := span } = none ∧
    evalPureStmtChecked body bbIdx stmtIdx env
      { kind := .storageDead loc, span := span } = none := by
  have hget : get? env loc = none := List.getElem?_eq_none h_oob
  unfold evalPureStmtChecked isPureStatement
  rw [ite_eq_left rfl, ite_eq_left rfl]
  dsimp only
  rw [hget]
  exact ⟨rfl, rfl⟩

/-- Assigning to a `.dead` local slot deterministically returns `none` in
`evalPureStmtChecked`. -/
theorem evalPureStmtChecked_assign_dead_none
    (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat)
    (env : PureEnv) (dstLoc : Local) (rv : Rvalue) (span : String)
    {val : Value}
    (h_rv : evalRvalue env rv emptyMemory body.localDecls body.layouts =
      .ok val env emptyMemory)
    (h_dead : get? env dstLoc = some .dead) :
    evalPureStmtChecked body bbIdx stmtIdx env
      { kind := .assign { local_ := dstLoc, projection := [] } rv, span := span } = none := by
  unfold evalPureStmtChecked
  cases isPureStatement (.assign { local_ := dstLoc, projection := [] } rv) with
  | false => rfl
  | true =>
    rw [ite_eq_left rfl]
    dsimp only
    rw [h_rv]
    dsimp only
    rw [h_dead]

set_option maxHeartbeats 20000 in
/-- **Heartbeat-bounded regression guard (`maxHeartbeats := 20000`)**: 6 consecutive
local `.storageLive` / `.storageDead` / `.deinit` updates across an 8-slot
environment with 4 untouched symbolic `LocalSlot` entries (`s₀ s₁ s₂ s₃ : LocalSlot`)
normalize to a flat `PureEnv` in a single pass by `rfl` within 20,000 heartbeats
(whereas two-pass `evalPureStmtsN` / `forcePureEnv?` cannot reduce at all over
symbolic `s₀ : LocalSlot` entries). -/
theorem evalPureStmtsCheckedN_multi_update_symbolic_slots_rfl
    (body : CapturedMir) (bbIdx : BasicBlockIdx)
    (s₀ s₁ s₂ s₃ : LocalSlot) (v₄ v₅ : Value) :
    evalPureStmtsCheckedN body bbIdx
      [{ kind := .storageLive 6, span := "s0" },
       { kind := .storageLive 7, span := "s1" },
       { kind := .deinit { local_ := 4, projection := [] }, span := "s2" },
       { kind := .storageDead 5, span := "s3" },
       { kind := .storageLive 5, span := "s4" },
       { kind := .storageDead 7, span := "s5" }]
      6 0 [s₀, s₁, s₂, s₃, .init v₄, .init v₅, .dead, .dead] =
      some [s₀, s₁, s₂, s₃, .uninit, .uninit, .uninit, .dead] :=
  rfl

theorem LiftStmtsTerminator.cons_eval_checked {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env env' : PureEnv} {stmts : List Statement} {stmt : Statement}
    {term : Terminator} {post : Value → Prop} {fuel : Nat}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_get : Trusted.Sequence.get? stmts stmtIdx = some stmt)
    (h_eval : evalPureStmtChecked body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + 1) env' stmts term post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env stmts term post (fuel + 1) := by
  rw [evalPureStmtChecked_eq_evalPureStmt] at h_eval
  exact LiftStmtsTerminator.cons_eval h_bb h_phase h_get h_eval h_next

theorem LiftStmtsTerminator.cons_eval_checked_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {stmt : Statement} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_get : Trusted.Sequence.get? bb.statements stmtIdx = some stmt)
    (h_eval : evalPureStmtChecked body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + 1) env' bb.statements bb.terminator post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + 1) := by
  rw [evalPureStmtChecked_eq_evalPureStmtNorm] at h_eval
  exact LiftStmtsTerminator.cons_eval_norm_ready h_ready h_bb h_get h_eval h_next

theorem LiftStmtsTerminator.eval_n_checked {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {n stmtIdx : Nat} {env env' : PureEnv} {stmts : List Statement} {term : Terminator}
    {post : Value → Prop} {fuel : Nat}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_eval : evalPureStmtsCheckedN body bbIdx stmts n stmtIdx env = some env')
    (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + n) env' stmts term post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env stmts term post (fuel + n) := by
  rw [evalPureStmtsCheckedN_eq_evalPureStmtsN] at h_eval
  exact LiftStmtsTerminator.eval_n h_bb h_phase h_eval h_next

theorem LiftStmtsTerminator.eval_n_checked_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {n stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsCheckedN body bbIdx bb.statements n stmtIdx env = some env')
    (h_next : LiftStmtsTerminator body bbIdx (stmtIdx + n) env' bb.statements bb.terminator post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + n) := by
  rw [evalPureStmtsCheckedN_eq_evalPureStmtsN] at h_eval
  exact LiftStmtsTerminator.eval_n_ready h_ready h_bb h_eval h_next

theorem LiftStmtsTerminator.eval_rest_checked {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {term : Terminator} {post : Value → Prop}
    {fuel : Nat}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_eval : evalPureStmtsCheckedN body bbIdx stmts (List.length stmts - stmtIdx)
      stmtIdx env = some env')
    (h_next : LiftStmtsTerminator body bbIdx
      (stmtIdx + (List.length stmts - stmtIdx)) env' stmts term post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env stmts term post
      (fuel + (List.length stmts - stmtIdx)) :=
  LiftStmtsTerminator.eval_n_checked h_bb h_phase h_eval h_next

theorem LiftStmtsTerminator.eval_rest_checked_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {post : Value → Prop} {fuel : Nat}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsCheckedN body bbIdx bb.statements
      (List.length bb.statements - stmtIdx) stmtIdx env = some env')
    (h_next : LiftStmtsTerminator body bbIdx
      (stmtIdx + (List.length bb.statements - stmtIdx))
      env' bb.statements bb.terminator post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post
      (fuel + (List.length bb.statements - stmtIdx)) :=
  LiftStmtsTerminator.eval_n_checked_ready h_ready h_bb h_eval h_next

theorem LiftStmtsTerminator.term_drop_checked_ready {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {place : Place} {unwind : UnwindAction}
    {span : String} {post : Value → Prop} {fuel : Nat} {slot : LocalSlot}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .drop place target unwind, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_get : Trusted.Sequence.get? env place.local_ = some slot)
    (h_not_dead : slot ≠ .dead)
    (h_proj : place.projection = [])
    (h_set : setSpineChecked? env place.local_ .uninit = some env')
    (h_next : LiftBlock body target env' post fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post (fuel + 1) :=
  LiftStmtsTerminator.term_drop_ready h_ready h_bb h_term h_end h_get h_not_dead
    h_proj (set?_of_setSpineChecked? h_set) h_next

end ForcePureEnv

/-!
## Opaque-Postcondition `LiftBlock` Diamond Join Sharing (`liftBlock_diamond_shared`)
-/

section DiamondJoinSharing

/-- Fuel monotonicity for `LiftBlock`. -/
theorem LiftBlock.mono_fuel {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {env : PureEnv} {post : Value → Prop} {f₁ f₂ : Nat}
    (h_le : f₁ ≤ f₂) (h : LiftBlock body bbIdx env post f₁) :
    LiftBlock body bbIdx env post f₂ := by
  unfold LiftBlock wpPureMirExec at h ⊢
  exact MirFuelFree.wpMirExecSym_mono h_le h

/-- Postcondition monotonicity for `LiftBlock`. -/
theorem LiftBlock.mono_post {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {env : PureEnv} {P Q : Value → Prop} {fuel : Nat}
    (h_imp : ∀ v, P v → Q v) (h : LiftBlock body bbIdx env P fuel) :
    LiftBlock body bbIdx env Q fuel := by
  unfold LiftBlock wpPureMirExec at h ⊢
  refine MirFuelFree.wpMirExecSym_mono_post ?_ h
  intro out h_out
  cases out with
  | normal rv => exact h_imp rv.1 h_out
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out

/-- Combined fuel and postcondition monotonicity for `LiftBlock`. -/
theorem LiftBlock.mono {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {env : PureEnv} {P Q : Value → Prop} {f₁ f₂ : Nat}
    (h_le : f₁ ≤ f₂) (h_imp : ∀ v, P v → Q v)
    (h : LiftBlock body bbIdx env P f₁) :
    LiftBlock body bbIdx env Q f₂ :=
  LiftBlock.mono_post h_imp (LiftBlock.mono_fuel h_le h)

/-- Fuel monotonicity for `LiftStmtsTerminator`. -/
theorem LiftStmtsTerminator.mono_fuel {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {stmts : List Statement} {term : Terminator}
    {post : Value → Prop} {f₁ f₂ : Nat}
    (h_le : f₁ ≤ f₂) (h : LiftStmtsTerminator body bbIdx stmtIdx env stmts term post f₁) :
    LiftStmtsTerminator body bbIdx stmtIdx env stmts term post f₂ := by
  unfold LiftStmtsTerminator at h ⊢
  exact MirFuelFree.wpMirExecSym_mono h_le h

/-- Postcondition monotonicity for `LiftStmtsTerminator`. -/
theorem LiftStmtsTerminator.mono_post {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {stmts : List Statement} {term : Terminator}
    {P Q : Value → Prop} {fuel : Nat}
    (h_imp : ∀ v, P v → Q v)
    (h : LiftStmtsTerminator body bbIdx stmtIdx env stmts term P fuel) :
    LiftStmtsTerminator body bbIdx stmtIdx env stmts term Q fuel := by
  unfold LiftStmtsTerminator at h ⊢
  refine MirFuelFree.wpMirExecSym_mono_post ?_ h
  intro out h_out
  cases out with
  | normal rv => exact h_imp rv.1 h_out
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out

/-- Combined fuel and postcondition monotonicity for `LiftStmtsTerminator`. -/
theorem LiftStmtsTerminator.mono {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {stmts : List Statement} {term : Terminator}
    {P Q : Value → Prop} {f₁ f₂ : Nat}
    (h_le : f₁ ≤ f₂) (h_imp : ∀ v, P v → Q v)
    (h : LiftStmtsTerminator body bbIdx stmtIdx env stmts term P f₁) :
    LiftStmtsTerminator body bbIdx stmtIdx env stmts term Q f₂ :=
  LiftStmtsTerminator.mono_post h_imp (LiftStmtsTerminator.mono_fuel h_le h)

/-- Fuel-free block lifting judgment (`∃ fuel, LiftBlock body bbIdx env post fuel`):
allows branches of a CFG diamond with different path lengths to package their own
existential fuel budgets and share a single continuation proof for a join block. -/
def LiftBlockConverges (body : CapturedMir) (bbIdx : BasicBlockIdx)
    (env : PureEnv) (post : Value → Prop) : Prop :=
  ∃ fuel, LiftBlock body bbIdx env post fuel

/-- Fuel-free statement/terminator lifting judgment. -/
def LiftStmtsConverges (body : CapturedMir) (bbIdx : BasicBlockIdx)
    (stmtIdx : Nat) (env : PureEnv) (stmts : List Statement) (term : Terminator)
    (post : Value → Prop) : Prop :=
  ∃ fuel, LiftStmtsTerminator body bbIdx stmtIdx env stmts term post fuel

theorem LiftBlockConverges.iff_pureMirConverges {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {env : PureEnv} {post : Value → Prop} :
    LiftBlockConverges body bbIdx env post ↔
      PureMirConverges body { bb := bbIdx, stmtIdx := 0, env := env } post := by
  unfold LiftBlockConverges LiftBlock PureMirConverges
  exact Iff.rfl

theorem LiftBlockConverges.of_liftBlock {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {env : PureEnv} {post : Value → Prop} {fuel : Nat}
    (h : LiftBlock body bbIdx env post fuel) :
    LiftBlockConverges body bbIdx env post :=
  ⟨fuel, h⟩

theorem LiftBlockConverges.mono {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {env : PureEnv} {P Q : Value → Prop}
    (h_imp : ∀ v, P v → Q v) (h : LiftBlockConverges body bbIdx env P) :
    LiftBlockConverges body bbIdx env Q := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, LiftBlock.mono_post h_imp hf⟩

theorem LiftBlockConverges.of_lookup {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {bb : BasicBlockData} {env : PureEnv} {post : Value → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_lift : LiftStmtsConverges body bbIdx 0 env bb.statements bb.terminator post) :
    LiftBlockConverges body bbIdx env post := by
  obtain ⟨fuel, hf⟩ := h_lift
  exact ⟨fuel, LiftBlock.of_lookup h_bb hf⟩

theorem LiftStmtsConverges.of_liftStmtsTerminator {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {stmts : List Statement} {term : Terminator} {post : Value → Prop} {fuel : Nat}
    (h : LiftStmtsTerminator body bbIdx stmtIdx env stmts term post fuel) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts term post :=
  ⟨fuel, h⟩

theorem LiftStmtsConverges.mono {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {stmts : List Statement} {term : Terminator} {P Q : Value → Prop}
    (h_imp : ∀ v, P v → Q v)
    (h : LiftStmtsConverges body bbIdx stmtIdx env stmts term P) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts term Q := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, LiftStmtsTerminator.mono_post h_imp hf⟩

theorem LiftStmtsConverges.cons_eval {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env env' : PureEnv} {stmts : List Statement} {stmt : Statement}
    {term : Terminator} {post : Value → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_get : Trusted.Sequence.get? stmts stmtIdx = some stmt)
    (h_eval : MirLiftCore.evalPureStmt body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsConverges body bbIdx (stmtIdx + 1) env' stmts term post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts term post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.cons_eval h_bb h_phase h_get h_eval hf⟩

theorem LiftStmtsConverges.cons_eval_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {stmt : Statement} {post : Value → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_get : Trusted.Sequence.get? bb.statements stmtIdx = some stmt)
    (h_eval : MirLiftCore.evalPureStmt body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsConverges body bbIdx (stmtIdx + 1) env' bb.statements bb.terminator post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.cons_eval_ready h_ready h_bb h_get h_eval hf⟩

theorem LiftStmtsConverges.cons_eval_norm {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env env' : PureEnv} {stmts : List Statement} {stmt : Statement}
    {term : Terminator} {post : Value → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_get : Trusted.Sequence.get? stmts stmtIdx = some stmt)
    (h_eval : evalPureStmtNorm body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsConverges body bbIdx (stmtIdx + 1) env' stmts term post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts term post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.cons_eval_norm h_bb h_phase h_get h_eval hf⟩

theorem LiftStmtsConverges.cons_eval_norm_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {stmt : Statement} {post : Value → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_get : Trusted.Sequence.get? bb.statements stmtIdx = some stmt)
    (h_eval : evalPureStmtNorm body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsConverges body bbIdx (stmtIdx + 1) env' bb.statements bb.terminator post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.cons_eval_norm_ready h_ready h_bb h_get h_eval hf⟩

theorem LiftStmtsConverges.cons_eval_checked {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env env' : PureEnv} {stmts : List Statement} {stmt : Statement}
    {term : Terminator} {post : Value → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_get : Trusted.Sequence.get? stmts stmtIdx = some stmt)
    (h_eval : evalPureStmtChecked body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsConverges body bbIdx (stmtIdx + 1) env' stmts term post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts term post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.cons_eval_checked h_bb h_phase h_get h_eval hf⟩

theorem LiftStmtsConverges.cons_eval_checked_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {stmt : Statement} {post : Value → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_get : Trusted.Sequence.get? bb.statements stmtIdx = some stmt)
    (h_eval : evalPureStmtChecked body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsConverges body bbIdx (stmtIdx + 1) env' bb.statements bb.terminator post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.cons_eval_checked_ready h_ready h_bb h_get h_eval hf⟩

theorem LiftStmtsConverges.eval_n {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {n stmtIdx : Nat} {env env' : PureEnv} {stmts : List Statement} {term : Terminator}
    {post : Value → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_eval : evalPureStmtsN body bbIdx stmts n stmtIdx env = some env')
    (h_next : LiftStmtsConverges body bbIdx (stmtIdx + n) env' stmts term post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts term post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + n, LiftStmtsTerminator.eval_n h_bb h_phase h_eval hf⟩

theorem LiftStmtsConverges.eval_n_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {n stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {post : Value → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsN body bbIdx bb.statements n stmtIdx env = some env')
    (h_next : LiftStmtsConverges body bbIdx (stmtIdx + n) env' bb.statements bb.terminator post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + n, LiftStmtsTerminator.eval_n_ready h_ready h_bb h_eval hf⟩

theorem LiftStmtsConverges.eval_n_checked {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {n stmtIdx : Nat} {env env' : PureEnv} {stmts : List Statement} {term : Terminator}
    {post : Value → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_eval : evalPureStmtsCheckedN body bbIdx stmts n stmtIdx env = some env')
    (h_next : LiftStmtsConverges body bbIdx (stmtIdx + n) env' stmts term post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts term post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + n, LiftStmtsTerminator.eval_n_checked h_bb h_phase h_eval hf⟩

theorem LiftStmtsConverges.eval_n_checked_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {n stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {post : Value → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsCheckedN body bbIdx bb.statements n stmtIdx env = some env')
    (h_next : LiftStmtsConverges body bbIdx (stmtIdx + n) env' bb.statements bb.terminator post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + n, LiftStmtsTerminator.eval_n_checked_ready h_ready h_bb h_eval hf⟩

theorem LiftStmtsConverges.eval_rest {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {term : Terminator} {post : Value → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_eval : evalPureStmtsN body bbIdx stmts (List.length stmts - stmtIdx)
      stmtIdx env = some env')
    (h_next : LiftStmtsConverges body bbIdx
      (stmtIdx + (List.length stmts - stmtIdx)) env' stmts term post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts term post :=
  LiftStmtsConverges.eval_n h_bb h_phase h_eval h_next

theorem LiftStmtsConverges.eval_rest_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {post : Value → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsN body bbIdx bb.statements
      (List.length bb.statements - stmtIdx) stmtIdx env = some env')
    (h_next : LiftStmtsConverges body bbIdx
      (stmtIdx + (List.length bb.statements - stmtIdx))
      env' bb.statements bb.terminator post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post :=
  LiftStmtsConverges.eval_n_ready h_ready h_bb h_eval h_next

theorem LiftStmtsConverges.eval_rest_checked {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {term : Terminator} {post : Value → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_eval : evalPureStmtsCheckedN body bbIdx stmts (List.length stmts - stmtIdx)
      stmtIdx env = some env')
    (h_next : LiftStmtsConverges body bbIdx
      (stmtIdx + (List.length stmts - stmtIdx)) env' stmts term post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts term post :=
  LiftStmtsConverges.eval_n_checked h_bb h_phase h_eval h_next

theorem LiftStmtsConverges.eval_rest_checked_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {post : Value → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsCheckedN body bbIdx bb.statements
      (List.length bb.statements - stmtIdx) stmtIdx env = some env')
    (h_next : LiftStmtsConverges body bbIdx
      (stmtIdx + (List.length bb.statements - stmtIdx))
      env' bb.statements bb.terminator post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post :=
  LiftStmtsConverges.eval_n_checked_ready h_ready h_bb h_eval h_next

theorem LiftStmtsConverges.term_return {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv} {stmts : List Statement}
    {span : String} {post : Value → Prop} {val : Value}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := { kind := .return_, span := span }, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_end : stmtIdx = List.length stmts)
    (h_ret : Trusted.Sequence.get? env 0 = some (.init val))
    (h_post : post val) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts { kind := .return_, span := span } post :=
  ⟨1, LiftStmtsTerminator.term_return h_bb h_phase h_end h_ret h_post⟩

theorem LiftStmtsConverges.term_return_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {bb : BasicBlockData} {span : String} {post : Value → Prop} {val : Value}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .return_, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_ret : Trusted.Sequence.get? env 0 = some (.init val))
    (h_post : post val) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post :=
  ⟨1, LiftStmtsTerminator.term_return_ready h_ready h_bb h_term h_end h_ret h_post⟩

theorem LiftStmtsConverges.term_goto {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {stmts : List Statement} {span : String} {post : Value → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := { kind := .goto target, span := span }, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_end : stmtIdx = List.length stmts)
    (h_lift : LiftBlockConverges body target env post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts { kind := .goto target, span := span } post := by
  obtain ⟨fuel, hf⟩ := h_lift
  exact ⟨fuel + 1, LiftStmtsTerminator.term_goto h_bb h_phase h_end hf⟩

theorem LiftStmtsConverges.term_goto_ready {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {bb : BasicBlockData} {span : String} {post : Value → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .goto target, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_lift : LiftBlockConverges body target env post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post := by
  obtain ⟨fuel, hf⟩ := h_lift
  exact ⟨fuel + 1, LiftStmtsTerminator.term_goto_ready h_ready h_bb h_term h_end hf⟩

theorem LiftStmtsConverges.term_switchInt {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {discr : Operand} {targets : SwitchTargets}
    {span : String} {post : Value → Prop} {sc : ScalarInt}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := { kind := .switchInt discr targets, span := span }, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_end : stmtIdx = List.length stmts)
    (h_eval : MirLiftCore.evalPureOperand body env discr = .ok (.scalar sc) env')
    (h_target : target = lookupSwitchTarget sc.bits targets.branches targets.otherwise)
    (h_next : LiftBlockConverges body target env' post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts { kind := .switchInt discr targets, span := span } post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.term_switchInt h_bb h_phase h_end h_eval h_target hf⟩

theorem LiftStmtsConverges.term_switchInt_ready {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {discr : Operand} {targets : SwitchTargets}
    {span : String} {post : Value → Prop} {sc : ScalarInt}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .switchInt discr targets, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_eval : MirLiftCore.evalPureOperand body env discr = .ok (.scalar sc) env')
    (h_target : target = lookupSwitchTarget sc.bits targets.branches targets.otherwise)
    (h_next : LiftBlockConverges body target env' post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.term_switchInt_ready h_ready h_bb h_term h_end h_eval h_target hf⟩

theorem LiftStmtsConverges.term_assert {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {cond : Operand} {expected : Bool}
    {unwind : UnwindAction} {span : String} {post : Value → Prop} {sc : ScalarInt}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := { kind := .assert cond expected target unwind, span := span }, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_end : stmtIdx = List.length stmts)
    (h_eval : MirLiftCore.evalPureOperand body env cond = .ok (.scalar sc) env')
    (h_cond : sc.bits = (match expected with | true => 1 | false => 0))
    (h_next : LiftBlockConverges body target env' post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts { kind := .assert cond expected target unwind, span := span } post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.term_assert h_bb h_phase h_end h_eval
    (by cases expected <;> simpa using h_cond) hf⟩

theorem LiftStmtsConverges.term_assert_ready {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {cond : Operand} {expected : Bool}
    {unwind : UnwindAction} {span : String} {post : Value → Prop} {sc : ScalarInt}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .assert cond expected target unwind, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_eval : MirLiftCore.evalPureOperand body env cond = .ok (.scalar sc) env')
    (h_cond : sc.bits = (match expected with | true => 1 | false => 0))
    (h_next : LiftBlockConverges body target env' post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.term_assert_ready h_ready h_bb h_term h_end h_eval h_cond hf⟩

theorem LiftStmtsConverges.term_drop {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {place : Place} {unwind : UnwindAction}
    {span : String} {post : Value → Prop} {slot : LocalSlot}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := { kind := .drop place target unwind, span := span }, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_end : stmtIdx = List.length stmts)
    (h_get : Trusted.Sequence.get? env place.local_ = some slot)
    (h_not_dead : slot ≠ .dead)
    (h_proj : place.projection = [])
    (h_set : Trusted.Sequence.set? env place.local_ .uninit = some env')
    (h_next : LiftBlockConverges body target env' post) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts { kind := .drop place target unwind, span := span } post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.term_drop h_bb h_phase h_end h_get h_not_dead h_proj h_set hf⟩

theorem LiftStmtsConverges.term_drop_ready {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {place : Place} {unwind : UnwindAction}
    {span : String} {post : Value → Prop} {slot : LocalSlot}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .drop place target unwind, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_get : Trusted.Sequence.get? env place.local_ = some slot)
    (h_not_dead : slot ≠ .dead)
    (h_proj : place.projection = [])
    (h_set : Trusted.Sequence.set? env place.local_ .uninit = some env')
    (h_next : LiftBlockConverges body target env' post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post := by
  obtain ⟨fuel, hf⟩ := h_next
  exact ⟨fuel + 1, LiftStmtsTerminator.term_drop_ready h_ready h_bb h_term h_end h_get h_not_dead h_proj h_set hf⟩

theorem LiftStmtsConverges.term_drop_checked_ready {body : CapturedMir}
    {bbIdx target : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {place : Place} {unwind : UnwindAction}
    {span : String} {post : Value → Prop} {slot : LocalSlot}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .drop place target unwind, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_get : Trusted.Sequence.get? env place.local_ = some slot)
    (h_not_dead : slot ≠ .dead)
    (h_proj : place.projection = [])
    (h_set : setSpineChecked? env place.local_ .uninit = some env')
    (h_next : LiftBlockConverges body target env' post) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post :=
  LiftStmtsConverges.term_drop_ready h_ready h_bb h_term h_end h_get h_not_dead
    h_proj (set?_of_setSpineChecked? h_set) h_next

/-- Opaque-postcondition block-to-join lifting judgment: from `(bbIdx, env)`,
whenever every environment `env_j` at `joinBb` satisfying `JoinInv env_j`
converges to an arbitrary postcondition `Q`, `(bbIdx, env)` also converges to `Q`. -/
def LiftBlockToJoin (body : CapturedMir) (bbIdx : BasicBlockIdx) (env : PureEnv)
    (joinBb : BasicBlockIdx) (JoinInv : PureEnv → Prop) : Prop :=
  ∀ (Q : Value → Prop),
    (∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j Q) →
    LiftBlockConverges body bbIdx env Q

theorem LiftBlockToJoin.refl {body : CapturedMir} {joinBb : BasicBlockIdx}
    {env : PureEnv} {JoinInv : PureEnv → Prop} (h_inv : JoinInv env) :
    LiftBlockToJoin body joinBb env joinBb JoinInv :=
  fun _ h_join => h_join env h_inv

theorem LiftBlockToJoin.trans {body : CapturedMir}
    {bb₀ bb₁ bb₂ : BasicBlockIdx} {env₀ : PureEnv}
    {MidInv JoinInv : PureEnv → Prop}
    (h₁ : LiftBlockToJoin body bb₀ env₀ bb₁ MidInv)
    (h₂ : ∀ env₁, MidInv env₁ → LiftBlockToJoin body bb₁ env₁ bb₂ JoinInv) :
    LiftBlockToJoin body bb₀ env₀ bb₂ JoinInv :=
  fun Q h_join => h₁ Q (fun env₁ h_mid => h₂ env₁ h_mid Q h_join)

theorem LiftBlockToJoin.mono {body : CapturedMir}
    {bbIdx joinBb : BasicBlockIdx} {env : PureEnv}
    {Inv₁ Inv₂ : PureEnv → Prop}
    (h_imp : ∀ e, Inv₁ e → Inv₂ e)
    (h : LiftBlockToJoin body bbIdx env joinBb Inv₁) :
    LiftBlockToJoin body bbIdx env joinBb Inv₂ :=
  fun Q h_join => h Q (fun e he => h_join e (h_imp e he))

/-- **Opaque-postcondition diamond join sharing (`liftBlock_diamond_shared`)**:
proves the shared join block `joinBb` **once** under `JoinInv : PureEnv → Prop`,
and passes it as an opaque continuation hypothesis to the upstream branching
prefix `h_branches`, avoiding any branch duplication of `joinBb` (even when
incoming branches have different instruction counts). -/
theorem liftBlock_diamond_shared {body : CapturedMir}
    {entryBb joinBb : BasicBlockIdx} {env₀ : PureEnv}
    {JoinInv : PureEnv → Prop} {post : Value → Prop}
    (h_branches :
      (∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j post) →
      LiftBlockConverges body entryBb env₀ post)
    (h_join : ∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j post) :
    LiftBlockConverges body entryBb env₀ post :=
  h_branches h_join

/-- `PureMirConverges` entry-block specialization of `liftBlock_diamond_shared`. -/
theorem pureMirConverges_of_shared_join {body : CapturedMir}
    {args : List Value} {joinBb : BasicBlockIdx}
    (JoinInv : PureEnv → Prop) {post : Value → Prop}
    (h_branches :
      (∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j post) →
      LiftBlockConverges body 0 (initPureEnv body args) post)
    (h_join : ∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j post) :
    PureMirConverges body (initPureState body args) post :=
  LiftBlockConverges.iff_pureMirConverges.mp (h_branches h_join)

/-- Multi-join composition: chains an upstream diamond reaching `midBb` under
`MidInv` with a downstream diamond from `midBb` to `exitBb` under `ExitInv` and
a single shared proof of `exitBb`. -/
theorem liftBlock_two_diamonds_shared {body : CapturedMir}
    {entryBb midBb exitBb : BasicBlockIdx} {env₀ : PureEnv}
    {MidInv ExitInv : PureEnv → Prop} {post : Value → Prop}
    (h_first : LiftBlockToJoin body entryBb env₀ midBb MidInv)
    (h_second : ∀ env_m, MidInv env_m → LiftBlockToJoin body midBb env_m exitBb ExitInv)
    (h_exit : ∀ env_e, ExitInv env_e → LiftBlockConverges body exitBb env_e post) :
    LiftBlockConverges body entryBb env₀ post :=
  (h_first.trans h_second) post h_exit

/-- Direct 4-block `switchInt` diamond rule (`bb_entry -> {bb_then, bb_else} -> bb_join`):
evaluates `bb_entry` up to its `switchInt`, branches on a decidable condition `C`
into `bb_then` vs `bb_else` (which may have different statement lengths), and
proves `bb_join` **once** for `JoinInv`. -/
theorem liftBlock_switchInt_diamond_shared {body : CapturedMir}
    {entryBb thenBb elseBb joinBb : BasicBlockIdx}
    {bbEntry : BasicBlockData} {env₀ envSw env' : PureEnv}
    {discr : Operand} {targets : SwitchTargets} {span : String}
    {sc : ScalarInt} (C : Prop) [Decidable C]
    (JoinInv : PureEnv → Prop) {post : Value → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks entryBb = some bbEntry)
    (h_eval : evalPureStmtsCheckedN body entryBb bbEntry.statements
      (List.length bbEntry.statements) 0 env₀ = some envSw)
    (h_term : bbEntry.terminator = { kind := .switchInt discr targets, span := span })
    (h_op : MirLiftCore.evalPureOperand body envSw discr = .ok (.scalar sc) env')
    (h_then : C →
      lookupSwitchTarget sc.bits targets.branches targets.otherwise = thenBb ∧
      ((∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j post) →
        LiftBlockConverges body thenBb env' post))
    (h_else : ¬ C →
      lookupSwitchTarget sc.bits targets.branches targets.otherwise = elseBb ∧
      ((∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j post) →
        LiftBlockConverges body elseBb env' post))
    (h_join : ∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j post) :
    LiftBlockConverges body entryBb env₀ post := by
  refine LiftBlockConverges.of_lookup h_bb ?_
  have h_eval' : evalPureStmtsCheckedN body entryBb bbEntry.statements
      (List.length bbEntry.statements - 0) 0 env₀ = some envSw := h_eval
  refine LiftStmtsConverges.eval_rest_checked_ready h_ready h_bb h_eval' ?_
  by_cases hC : C
  · obtain ⟨h_tgt, h_th⟩ := h_then hC
    exact LiftStmtsConverges.term_switchInt_ready h_ready h_bb h_term
      (Nat.zero_add _) h_op h_tgt.symm (h_th h_join)
  · obtain ⟨h_tgt, h_el⟩ := h_else hC
    exact LiftStmtsConverges.term_switchInt_ready h_ready h_bb h_term
      (Nat.zero_add _) h_op h_tgt.symm (h_el h_join)

/-- Readiness-discharged `VerificationResult` gate using fuel-free `LiftBlockConverges`. -/
theorem verifyMirNoPanic_of_mirLiftReady_converges
    (c : Claim)
    (h_ready : checkMirLiftReady c.body = true)
    (h_lift : ∀ args, c.pre args →
      LiftBlockConverges c.body 0 (initPureEnv c.body args) (c.post args)) :
    VerificationResult c :=
  verifyMirNoPanic_of_mirLiftReady c h_ready h_lift

/--
Asymmetric diamond CFG witness (`argCount := 2`: `_1 : u32`, `_2 : u32`):
- `bb0`: `_3 = Le(Copy(_1), Copy(_2)); switchInt(Move(_3)) [0 => bb2, otherwise => bb1]`
- `bb1` (1 statement): `_4 = Copy(_1); goto -> bb3`
- `bb2` (2 statements, asymmetric fuel!): `_4 = Copy(_2); _1 = Copy(_2); goto -> bb3`
- `bb3` (shared join block with 2 statements + return):
  `_0 = Copy(_4); StorageDead(_4); return_`
-/
def witnessDiamondShared : CapturedMir where
  defPath := "Anneal::MirLiftCore::witness_diamond_shared"
  phase := .runtimeOptimized
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "_0" },
    { mutability := .mut, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "a" },
    { mutability := .not, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "b" },
    { mutability := .mut, ty := MirLiftReadyWitness.witnessBoolTy, debugName := some "cond" },
    { mutability := .mut, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "chosen" }
  ]
  basicBlocks := [
    -- bb0
    { statements := [
        { kind := .storageLive 3, span := "s0" },
        { kind := .storageLive 4, span := "s1" },
        { kind := .assign { local_ := 3, projection := [] }
            (.binaryOp .le (.copy { local_ := 1, projection := [] })
              (.copy { local_ := 2, projection := [] })),
          span := "s2" }
      ]
      terminator := {
        kind := .switchInt (.move { local_ := 3, projection := [] })
          { branches := [(0, 2)], otherwise := 1 }
        span := "t0"
      }
      isCleanup := false },
    -- bb1 (a <= b: 1 statement)
    { statements := [
        { kind := .assign { local_ := 4, projection := [] }
            (.use (.copy { local_ := 1, projection := [] })),
          span := "s3" }
      ]
      terminator := { kind := .goto 3, span := "t1" }
      isCleanup := false },
    -- bb2 (a > b: 2 statements — different step count from bb1!)
    { statements := [
        { kind := .assign { local_ := 4, projection := [] }
            (.use (.copy { local_ := 2, projection := [] })),
          span := "s4" },
        { kind := .assign { local_ := 1, projection := [] }
            (.use (.copy { local_ := 2, projection := [] })),
          span := "s5" }
      ]
      terminator := { kind := .goto 3, span := "t2" }
      isCleanup := false },
    -- bb3 (shared join & return: 2 statements + return)
    { statements := [
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.copy { local_ := 4, projection := [] })),
          span := "s6" },
        { kind := .storageDead 4, span := "s7" }
      ]
      terminator := { kind := .return_, span := "t3" }
      isCleanup := false }
  ]
  fnAbi := {
    args := [
      { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct },
      { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct }
    ]
    ret := { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := MirLiftReadyWitness.witnessLayouts
  allocations := []

theorem checkMirLiftReady_witnessDiamondShared :
    checkMirLiftReady witnessDiamondShared = true := rfl

theorem checkMirLiftDagReady_witnessDiamondShared :
    checkMirLiftDagReady witnessDiamondShared = true := rfl

set_option maxHeartbeats 20000 in
/-- **Heartbeat-bounded `.assign` normalization over symbolic `LocalSlot`s (`maxHeartbeats := 20000`)**:
`evalPureStmtsCheckedN` normalizes two consecutive local `.assign` statements
(`_4 = Copy(_2); _1 = Copy(_2)`) across an environment containing untouched
symbolic `LocalSlot` entries (`s₀ s₃ : LocalSlot`) in a single pass by `rfl`
within 20,000 heartbeats, whereas two-pass `evalPureStmtsN` cannot reduce by
`rfl` because `forcePureEnv?` gets stuck on `s₀` and `s₃`. -/
theorem evalPureStmtsCheckedN_assign_symbolic_slots_rfl
    (s₀ s₃ : LocalSlot) (v₁ b v₄ : Nat) :
    evalPureStmtsCheckedN witnessDiamondShared 2
      [{ kind := .assign { local_ := 4, projection := [] }
           (.use (.copy { local_ := 2, projection := [] })),
         span := "s4" },
       { kind := .assign { local_ := 1, projection := [] }
           (.use (.copy { local_ := 2, projection := [] })),
         span := "s5" }]
      2 0 [s₀, .init (.scalar ⟨v₁, 4⟩), .init (.scalar ⟨b, 4⟩), s₃, .init (.scalar ⟨v₄, 4⟩)] =
      some [s₀, .init (.scalar ⟨b, 4⟩), .init (.scalar ⟨b, 4⟩), s₃, .init (.scalar ⟨b, 4⟩)] :=
  rfl

/-- End-to-end verification of `witnessDiamondShared` using
`liftBlock_switchInt_diamond_shared`: the shared join block `bb3` is proved
**once** over a symbolic slot `s₁ : LocalSlot` (via single-pass
`eval_rest_checked_ready`, which reduces across symbolic `s₁` by `rfl`), even
though `bb1` and `bb2` have different statement counts and leave `_1` in
different states. -/
theorem verify_witnessDiamondShared_via_diamond_shared :
    VerificationResult
      { body := witnessDiamondShared
        pre := fun args =>
          ∃ a b : Nat,
            args = [.scalar { bits := a, sizeBytes := 4 },
                    .scalar { bits := b, sizeBytes := 4 }]
        post := fun args retVal =>
          ∀ a b : Nat,
            args = [.scalar { bits := a, sizeBytes := 4 },
                    .scalar { bits := b, sizeBytes := 4 }] →
            retVal = .scalar { bits := if a ≤ b then a else b, sizeBytes := 4 }
        callees := [] } := by
  have hr := checkMirLiftReady_witnessDiamondShared
  refine verifyMirNoPanic_of_mirLiftReady_converges _ hr (fun args hpre => ?_)
  rcases hpre with ⟨a, b, rfl⟩
  dsimp only
  let chosen := if a ≤ b then a else b
  refine liftBlock_switchInt_diamond_shared (thenBb := 1) (elseBb := 2) (joinBb := 3)
    (sc := boolToScalar (Nat.ble a b)) (C := a ≤ b)
    (JoinInv := fun env_j =>
      ∃ s₁ : LocalSlot,
        env_j = [.uninit, s₁, .init (.scalar ⟨b, 4⟩), .uninit,
                 .init (.scalar ⟨chosen, 4⟩)])
    hr (by rfl) (by rfl) rfl (by rfl) ?_ ?_ ?_
  · intro hle
    refine ⟨?_, fun h_join => ?_⟩
    · change lookupSwitchTarget (boolToScalar (Nat.ble a b)).bits [(0, 2)] 1 = 1
      rw [Nat.ble_eq_true_of_le hle]; rfl
    · refine LiftBlockConverges.of_lookup (by rfl) ?_
      refine LiftStmtsConverges.eval_rest_checked_ready hr (by rfl) (by rfl) ?_
      refine LiftStmtsConverges.term_goto_ready hr (by rfl) rfl rfl ?_
      exact h_join _ ⟨.init (.scalar ⟨a, 4⟩), by dsimp [chosen]; rw [ite_eq_left hle]⟩
  · intro hgt
    have hble : Nat.ble a b = false :=
      Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (Nat.lt_of_not_le hgt)
    refine ⟨?_, fun h_join => ?_⟩
    · change lookupSwitchTarget (boolToScalar (Nat.ble a b)).bits [(0, 2)] 1 = 2
      rw [hble]; rfl
    · refine LiftBlockConverges.of_lookup (by rfl) ?_
      refine LiftStmtsConverges.eval_rest_checked_ready hr (by rfl) (by rfl) ?_
      refine LiftStmtsConverges.term_goto_ready hr (by rfl) rfl rfl ?_
      exact h_join _ ⟨.init (.scalar ⟨b, 4⟩), by dsimp [chosen]; rw [ite_eq_right hgt]⟩
  · intro env_j ⟨s₁, h_env⟩
    subst h_env
    refine LiftBlockConverges.of_lookup (by rfl) ?_
    refine LiftStmtsConverges.eval_rest_checked_ready hr (by rfl) (by rfl) ?_
    refine LiftStmtsConverges.term_return_ready hr (by rfl) rfl rfl (by rfl) ?_
    intro a' b' h_eq
    injection h_eq with ha hb
    injection hb with hb' _
    injection ha with ha_sc
    injection ha_sc with ha_bits _
    injection hb' with hb_sc
    injection hb_sc with hb_bits _
    subst ha_bits hb_bits
    rfl

/-! ### Compositional opaque-postcondition join paths (`LiftStmtsToJoin` / `LiftBlockToJoin`)

`LiftBlockToJoin body bb env joinBb JoinInv` is parametric in the final
postcondition `Q`, so a path proof to a join block is written once and reused
for every downstream continuation. The constructors below build such paths
block by block (single-pass statement evaluation, `goto`, `switchInt`, `assert`,
`drop`), so sequential diamonds compose through `LiftBlockToJoin.trans` /
`liftBlock_two_diamonds_shared` without unfolding any definition. -/

/-- Opaque-postcondition statement-suffix judgment: from statement `stmtIdx` of
block `bbIdx`, every path reaches `joinBb` in an environment satisfying
`JoinInv`, so the suffix converges to every postcondition `Q` that `joinBb`
converges to from all `JoinInv` environments. -/
def LiftStmtsToJoin (body : CapturedMir) (bbIdx : BasicBlockIdx) (stmtIdx : Nat)
    (env : PureEnv) (stmts : List Statement) (term : Terminator)
    (joinBb : BasicBlockIdx) (JoinInv : PureEnv → Prop) : Prop :=
  ∀ (Q : Value → Prop),
    (∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j Q) →
    LiftStmtsConverges body bbIdx stmtIdx env stmts term Q

/-- Enter block `bbIdx` at statement `0`. -/
theorem LiftBlockToJoin.of_lookup {body : CapturedMir} {bbIdx joinBb : BasicBlockIdx}
    {bb : BasicBlockData} {env : PureEnv} {JoinInv : PureEnv → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h : LiftStmtsToJoin body bbIdx 0 env bb.statements bb.terminator joinBb JoinInv) :
    LiftBlockToJoin body bbIdx env joinBb JoinInv :=
  fun Q h_join => LiftBlockConverges.of_lookup h_bb (h Q h_join)

/-- Case split on a decidable path condition. -/
theorem LiftBlockToJoin.by_cases {body : CapturedMir} {bbIdx joinBb : BasicBlockIdx}
    {env : PureEnv} {JoinInv : PureEnv → Prop} (C : Prop) [Decidable C]
    (h_pos : C → LiftBlockToJoin body bbIdx env joinBb JoinInv)
    (h_neg : Not C → LiftBlockToJoin body bbIdx env joinBb JoinInv) :
    LiftBlockToJoin body bbIdx env joinBb JoinInv :=
  if hC : C then h_pos hC else h_neg hC

/-- Discharge the shared join proof: a path to `joinBb` plus one proof of
`joinBb` for every `JoinInv` environment yields convergence. -/
theorem LiftBlockToJoin.converges {body : CapturedMir} {bbIdx joinBb : BasicBlockIdx}
    {env : PureEnv} {JoinInv : PureEnv → Prop} {post : Value → Prop}
    (h : LiftBlockToJoin body bbIdx env joinBb JoinInv)
    (h_join : ∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j post) :
    LiftBlockConverges body bbIdx env post :=
  h post h_join

/-- Entry-block (`bb = 0`, `initPureEnv body args`) bridge from `LiftBlockToJoin`
directly to `PureMirConverges`. -/
theorem LiftBlockToJoin.pureMirConverges {body : CapturedMir} {args : List Value}
    {joinBb : BasicBlockIdx} {JoinInv : PureEnv → Prop} {post : Value → Prop}
    (h : LiftBlockToJoin body 0 (initPureEnv body args) joinBb JoinInv)
    (h_join : ∀ env_j, JoinInv env_j → LiftBlockConverges body joinBb env_j post) :
    PureMirConverges body (initPureState body args) post :=
  LiftBlockConverges.iff_pureMirConverges.mp (h.converges h_join)

/-- Readiness-discharged `VerificationResult` gate directly from an entry-to-join
path `LiftBlockToJoin c.body 0 (initPureEnv c.body args) joinBb (JoinInv args)`
and a single shared proof of `joinBb`. -/
theorem verifyMirNoPanic_of_mirLiftReady_toJoin
    (c : Claim) (joinBb : BasicBlockIdx)
    (JoinInv : List Value → PureEnv → Prop)
    (h_ready : checkMirLiftReady c.body = true)
    (h_path : ∀ args, c.pre args →
      LiftBlockToJoin c.body 0 (initPureEnv c.body args) joinBb (JoinInv args))
    (h_join : ∀ args, c.pre args → ∀ env_j, JoinInv args env_j →
      LiftBlockConverges c.body joinBb env_j (c.post args)) :
    VerificationResult c :=
  verifyMirNoPanic_of_mirLiftReady_converges c h_ready (fun args hp =>
    (h_path args hp).converges (h_join args hp))

/-- Single-pass (`evalPureStmtChecked`) evaluation of one statement along a join
path under explicit block/phase hypotheses (usable even on sub-CFGs of bodies
with loops elsewhere). -/
theorem LiftStmtsToJoin.cons_eval_checked {body : CapturedMir}
    {bbIdx joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {stmt : Statement} {term : Terminator}
    {JoinInv : PureEnv → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_get : Trusted.Sequence.get? stmts stmtIdx = some stmt)
    (h_eval : evalPureStmtChecked body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsToJoin body bbIdx (stmtIdx + 1) env' stmts term joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env stmts term joinBb JoinInv :=
  fun Q h_join => LiftStmtsConverges.cons_eval_checked h_bb h_phase h_get h_eval (h_next Q h_join)

/-- Single-pass (`evalPureStmtsCheckedN`) evaluation of `n` statements along a
join path under explicit block/phase hypotheses. -/
theorem LiftStmtsToJoin.eval_n_checked {body : CapturedMir}
    {bbIdx joinBb : BasicBlockIdx} {n stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {term : Terminator} {JoinInv : PureEnv → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_eval : evalPureStmtsCheckedN body bbIdx stmts n stmtIdx env = some env')
    (h_next : LiftStmtsToJoin body bbIdx (stmtIdx + n) env' stmts term joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env stmts term joinBb JoinInv :=
  fun Q h_join => LiftStmtsConverges.eval_n_checked h_bb h_phase h_eval (h_next Q h_join)

/-- Single-pass (`evalPureStmtsCheckedN`) evaluation of remaining statements along
a join path under explicit block/phase hypotheses. -/
theorem LiftStmtsToJoin.eval_rest_checked {body : CapturedMir}
    {bbIdx joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {term : Terminator} {JoinInv : PureEnv → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := term, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_eval : evalPureStmtsCheckedN body bbIdx stmts (List.length stmts - stmtIdx)
      stmtIdx env = some env')
    (h_next : LiftStmtsToJoin body bbIdx (stmtIdx + (List.length stmts - stmtIdx))
      env' stmts term joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env stmts term joinBb JoinInv :=
  fun Q h_join => LiftStmtsConverges.eval_rest_checked h_bb h_phase h_eval (h_next Q h_join)

/-- `goto target` along a join path under explicit block/phase hypotheses. -/
theorem LiftStmtsToJoin.term_goto {body : CapturedMir}
    {bbIdx target joinBb : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {stmts : List Statement} {span : String} {JoinInv : PureEnv → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := { kind := .goto target, span := span }, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_end : stmtIdx = List.length stmts)
    (h_next : LiftBlockToJoin body target env joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env stmts { kind := .goto target, span := span } joinBb JoinInv :=
  fun Q h_join => LiftStmtsConverges.term_goto h_bb h_phase h_end (h_next Q h_join)

/-- `switchInt` along a join path under explicit block/phase hypotheses. -/
theorem LiftStmtsToJoin.term_switchInt {body : CapturedMir}
    {bbIdx target joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {discr : Operand} {targets : SwitchTargets}
    {span : String} {sc : ScalarInt} {JoinInv : PureEnv → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := { kind := .switchInt discr targets, span := span }, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_end : stmtIdx = List.length stmts)
    (h_eval : MirLiftCore.evalPureOperand body env discr = .ok (.scalar sc) env')
    (h_target : target = lookupSwitchTarget sc.bits targets.branches targets.otherwise)
    (h_next : LiftBlockToJoin body target env' joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env stmts { kind := .switchInt discr targets, span := span } joinBb JoinInv :=
  fun Q h_join =>
    LiftStmtsConverges.term_switchInt h_bb h_phase h_end h_eval h_target (h_next Q h_join)

/-- Two-way `switchInt` split along a join path under explicit block/phase hypotheses. -/
theorem LiftStmtsToJoin.term_switchInt_cases {body : CapturedMir}
    {bbIdx thenBb elseBb joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {discr : Operand} {targets : SwitchTargets}
    {span : String} {sc : ScalarInt} {JoinInv : PureEnv → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := { kind := .switchInt discr targets, span := span }, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_end : stmtIdx = List.length stmts)
    (h_eval : MirLiftCore.evalPureOperand body env discr = .ok (.scalar sc) env')
    (C : Prop) [Decidable C]
    (h_then : C → lookupSwitchTarget sc.bits targets.branches targets.otherwise = thenBb ∧
      LiftBlockToJoin body thenBb env' joinBb JoinInv)
    (h_else : ¬ C → lookupSwitchTarget sc.bits targets.branches targets.otherwise = elseBb ∧
      LiftBlockToJoin body elseBb env' joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env stmts { kind := .switchInt discr targets, span := span } joinBb JoinInv :=
  if hC : C then
    LiftStmtsToJoin.term_switchInt h_bb h_phase h_end h_eval
      (h_then hC).1.symm (h_then hC).2
  else
    LiftStmtsToJoin.term_switchInt h_bb h_phase h_end h_eval
      (h_else hC).1.symm (h_else hC).2

/-- A passing `assert` along a join path under explicit block/phase hypotheses. -/
theorem LiftStmtsToJoin.term_assert {body : CapturedMir}
    {bbIdx target joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {cond : Operand} {expected : Bool}
    {unwind : UnwindAction} {span : String} {sc : ScalarInt} {JoinInv : PureEnv → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := { kind := .assert cond expected target unwind, span := span }, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_end : stmtIdx = List.length stmts)
    (h_eval : MirLiftCore.evalPureOperand body env cond = .ok (.scalar sc) env')
    (h_cond : sc.bits = (match expected with | true => 1 | false => 0))
    (h_next : LiftBlockToJoin body target env' joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env stmts { kind := .assert cond expected target unwind, span := span } joinBb JoinInv :=
  fun Q h_join =>
    LiftStmtsConverges.term_assert h_bb h_phase h_end h_eval h_cond (h_next Q h_join)

/-- A `drop` of a local (single-pass `setSpineChecked?` update) along a join path
under explicit block/phase hypotheses. -/
theorem LiftStmtsToJoin.term_drop_checked {body : CapturedMir}
    {bbIdx target joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {stmts : List Statement} {place : Place} {unwind : UnwindAction}
    {span : String} {slot : LocalSlot} {JoinInv : PureEnv → Prop}
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx =
      some { statements := stmts, terminator := { kind := .drop place target unwind, span := span }, isCleanup := false })
    (h_phase : body.phase = .runtimePostCleanup ∨ body.phase = .runtimeOptimized)
    (h_end : stmtIdx = List.length stmts)
    (h_get : Trusted.Sequence.get? env place.local_ = some slot)
    (h_not_dead : slot ≠ .dead)
    (h_proj : place.projection = [])
    (h_set : setSpineChecked? env place.local_ .uninit = some env')
    (h_next : LiftBlockToJoin body target env' joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env stmts { kind := .drop place target unwind, span := span } joinBb JoinInv :=
  fun Q h_join =>
    LiftStmtsConverges.term_drop h_bb h_phase h_end h_get h_not_dead
      h_proj (set?_of_setSpineChecked? h_set) (h_next Q h_join)

/-- Single-pass (`evalPureStmtChecked`) evaluation of one statement along a join path. -/
theorem LiftStmtsToJoin.cons_eval_checked_ready {body : CapturedMir}
    {bbIdx joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {stmt : Statement} {JoinInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_get : Trusted.Sequence.get? bb.statements stmtIdx = some stmt)
    (h_eval : evalPureStmtChecked body bbIdx stmtIdx env stmt = some env')
    (h_next : LiftStmtsToJoin body bbIdx (stmtIdx + 1) env' bb.statements bb.terminator joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env bb.statements bb.terminator joinBb JoinInv :=
  fun Q h_join => LiftStmtsConverges.cons_eval_checked_ready h_ready h_bb h_get h_eval (h_next Q h_join)

/-- Single-pass (`evalPureStmtsCheckedN`) evaluation of `n` statements along a join path. -/
theorem LiftStmtsToJoin.eval_n_checked_ready {body : CapturedMir}
    {bbIdx joinBb : BasicBlockIdx} {n stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {JoinInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsCheckedN body bbIdx bb.statements n stmtIdx env = some env')
    (h_next : LiftStmtsToJoin body bbIdx (stmtIdx + n) env' bb.statements bb.terminator joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env bb.statements bb.terminator joinBb JoinInv :=
  fun Q h_join => LiftStmtsConverges.eval_n_checked_ready h_ready h_bb h_eval (h_next Q h_join)

/-- Single-pass (`evalPureStmtsCheckedN`) evaluation of the remaining statements. -/
theorem LiftStmtsToJoin.eval_rest_checked_ready {body : CapturedMir}
    {bbIdx joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {JoinInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsCheckedN body bbIdx bb.statements
      (List.length bb.statements - stmtIdx) stmtIdx env = some env')
    (h_next : LiftStmtsToJoin body bbIdx (stmtIdx + (List.length bb.statements - stmtIdx))
      env' bb.statements bb.terminator joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env bb.statements bb.terminator joinBb JoinInv :=
  fun Q h_join => LiftStmtsConverges.eval_rest_checked_ready h_ready h_bb h_eval (h_next Q h_join)

/-- `goto target` continues along a path to the join. -/
theorem LiftStmtsToJoin.term_goto_ready {body : CapturedMir}
    {bbIdx target joinBb : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {bb : BasicBlockData} {span : String} {JoinInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .goto target, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_next : LiftBlockToJoin body target env joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env bb.statements bb.terminator joinBb JoinInv :=
  fun Q h_join => LiftStmtsConverges.term_goto_ready h_ready h_bb h_term h_end (h_next Q h_join)

/-- `switchInt` with a resolved target continues along a path to the join. -/
theorem LiftStmtsToJoin.term_switchInt_ready {body : CapturedMir}
    {bbIdx target joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {discr : Operand} {targets : SwitchTargets}
    {span : String} {sc : ScalarInt} {JoinInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .switchInt discr targets, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_eval : MirLiftCore.evalPureOperand body env discr = .ok (.scalar sc) env')
    (h_target : target = lookupSwitchTarget sc.bits targets.branches targets.otherwise)
    (h_next : LiftBlockToJoin body target env' joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env bb.statements bb.terminator joinBb JoinInv :=
  fun Q h_join =>
    LiftStmtsConverges.term_switchInt_ready h_ready h_bb h_term h_end h_eval h_target
      (h_next Q h_join)

/-- Two-way `switchInt` split on a decidable guard `C`: each branch supplies its
resolved target and its own (opaque-postcondition) path to the shared join. -/
theorem LiftStmtsToJoin.term_switchInt_cases_ready {body : CapturedMir}
    {bbIdx thenBb elseBb joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {discr : Operand} {targets : SwitchTargets}
    {span : String} {sc : ScalarInt} {JoinInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .switchInt discr targets, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_eval : MirLiftCore.evalPureOperand body env discr = .ok (.scalar sc) env')
    (C : Prop) [Decidable C]
    (h_then : C → lookupSwitchTarget sc.bits targets.branches targets.otherwise = thenBb ∧
      LiftBlockToJoin body thenBb env' joinBb JoinInv)
    (h_else : ¬ C → lookupSwitchTarget sc.bits targets.branches targets.otherwise = elseBb ∧
      LiftBlockToJoin body elseBb env' joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env bb.statements bb.terminator joinBb JoinInv :=
  if hC : C then
    LiftStmtsToJoin.term_switchInt_ready h_ready h_bb h_term h_end h_eval
      (h_then hC).1.symm (h_then hC).2
  else
    LiftStmtsToJoin.term_switchInt_ready h_ready h_bb h_term h_end h_eval
      (h_else hC).1.symm (h_else hC).2

/-- A passing `assert` continues along a path to the join. -/
theorem LiftStmtsToJoin.term_assert_ready {body : CapturedMir}
    {bbIdx target joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {cond : Operand} {expected : Bool}
    {unwind : UnwindAction} {span : String} {sc : ScalarInt} {JoinInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .assert cond expected target unwind, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_eval : MirLiftCore.evalPureOperand body env cond = .ok (.scalar sc) env')
    (h_cond : sc.bits = (match expected with | true => 1 | false => 0))
    (h_next : LiftBlockToJoin body target env' joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env bb.statements bb.terminator joinBb JoinInv :=
  fun Q h_join =>
    LiftStmtsConverges.term_assert_ready h_ready h_bb h_term h_end h_eval h_cond (h_next Q h_join)

/-- A `drop` of a local (single-pass `setSpineChecked?` update) continues along
a path to the join. -/
theorem LiftStmtsToJoin.term_drop_checked_ready {body : CapturedMir}
    {bbIdx target joinBb : BasicBlockIdx} {stmtIdx : Nat} {env env' : PureEnv}
    {bb : BasicBlockData} {place : Place} {unwind : UnwindAction}
    {span : String} {slot : LocalSlot} {JoinInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .drop place target unwind, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_get : Trusted.Sequence.get? env place.local_ = some slot)
    (h_not_dead : slot ≠ .dead)
    (h_proj : place.projection = [])
    (h_set : setSpineChecked? env place.local_ .uninit = some env')
    (h_next : LiftBlockToJoin body target env' joinBb JoinInv) :
    LiftStmtsToJoin body bbIdx stmtIdx env bb.statements bb.terminator joinBb JoinInv :=
  fun Q h_join =>
    LiftStmtsConverges.term_drop_checked_ready h_ready h_bb h_term h_end h_get h_not_dead
      h_proj h_set (h_next Q h_join)

/-- **Opaque-postcondition `switchInt` diamond (`bb_entry -> {bb_then, bb_else} -> joinBb`)**:
both branch paths are postcondition-parametric `LiftBlockToJoin` proofs, so the
resulting entry path composes with further diamonds (`LiftBlockToJoin.trans`)
and the join block is proved exactly once by whoever consumes the path. -/
theorem liftBlock_switchInt_diamond_toJoin {body : CapturedMir}
    {entryBb thenBb elseBb joinBb : BasicBlockIdx}
    {bbEntry : BasicBlockData} {env₀ envSw env' : PureEnv}
    {discr : Operand} {targets : SwitchTargets} {span : String}
    {sc : ScalarInt} (C : Prop) [Decidable C] {JoinInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks entryBb = some bbEntry)
    (h_eval : evalPureStmtsCheckedN body entryBb bbEntry.statements
      (List.length bbEntry.statements) 0 env₀ = some envSw)
    (h_term : bbEntry.terminator = { kind := .switchInt discr targets, span := span })
    (h_op : MirLiftCore.evalPureOperand body envSw discr = .ok (.scalar sc) env')
    (h_then : C → lookupSwitchTarget sc.bits targets.branches targets.otherwise = thenBb ∧
      LiftBlockToJoin body thenBb env' joinBb JoinInv)
    (h_else : ¬ C → lookupSwitchTarget sc.bits targets.branches targets.otherwise = elseBb ∧
      LiftBlockToJoin body elseBb env' joinBb JoinInv) :
    LiftBlockToJoin body entryBb env₀ joinBb JoinInv :=
  LiftBlockToJoin.of_lookup h_bb
    (LiftStmtsToJoin.eval_rest_checked_ready h_ready h_bb h_eval
      (LiftStmtsToJoin.term_switchInt_cases_ready h_ready h_bb h_term (Nat.zero_add _) h_op
        C h_then h_else))

/-- Straight-line block ending in `goto`: single-pass statement evaluation, then
continue along a path to the join. -/
theorem liftBlock_goto_toJoin {body : CapturedMir} {bbIdx target joinBb : BasicBlockIdx}
    {bb : BasicBlockData} {env env' : PureEnv} {span : String} {JoinInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_eval : evalPureStmtsCheckedN body bbIdx bb.statements
      (List.length bb.statements) 0 env = some env')
    (h_term : bb.terminator = { kind := .goto target, span := span })
    (h_next : LiftBlockToJoin body target env' joinBb JoinInv) :
    LiftBlockToJoin body bbIdx env joinBb JoinInv :=
  LiftBlockToJoin.of_lookup h_bb
    (LiftStmtsToJoin.eval_rest_checked_ready h_ready h_bb h_eval
      (LiftStmtsToJoin.term_goto_ready h_ready h_bb h_term (Nat.zero_add _) h_next))

/--
Two sequential diamonds sharing a middle join and an exit join
(`argCount := 3`: `_1 = a`, `_2 = b`, `_3 = c`, all `u32`), computing
`min (max a b) c`:
- `bb0`: `_4 = Le(Copy(_1), Copy(_2)); switchInt(Move(_4)) [0 => bb2, otherwise => bb1]`
- `bb1`: `_5 = Copy(_2); goto -> bb3`; `bb2`: `_5 = Copy(_1); goto -> bb3`
- `bb3` (middle join): `_6 = Le(Copy(_5), Copy(_3)); switchInt(Move(_6)) [0 => bb5, otherwise => bb4]`
- `bb4`: `_0 = Copy(_5); goto -> bb6`; `bb5`: `_0 = Copy(_3); goto -> bb6`
- `bb6` (exit join): `StorageDead(_6); return_`
-/
def witnessTwoDiamonds : CapturedMir where
  defPath := "Anneal::MirLiftCore::witness_two_diamonds"
  phase := .runtimeOptimized
  role := .subject
  argCount := 3
  localDecls := [
    { mutability := .mut, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "_0" },
    { mutability := .not, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "a" },
    { mutability := .not, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "b" },
    { mutability := .not, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "c" },
    { mutability := .mut, ty := MirLiftReadyWitness.witnessBoolTy, debugName := some "le_ab" },
    { mutability := .mut, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "m" },
    { mutability := .mut, ty := MirLiftReadyWitness.witnessBoolTy, debugName := some "le_mc" }
  ]
  basicBlocks := [
    -- bb0
    { statements := [
        { kind := .storageLive 4, span := "d0" },
        { kind := .storageLive 5, span := "d1" },
        { kind := .assign { local_ := 4, projection := [] }
            (.binaryOp .le (.copy { local_ := 1, projection := [] })
              (.copy { local_ := 2, projection := [] })),
          span := "d2" }
      ]
      terminator := {
        kind := .switchInt (.move { local_ := 4, projection := [] })
          { branches := [(0, 2)], otherwise := 1 }
        span := "e0"
      }
      isCleanup := false },
    -- bb1 (a <= b)
    { statements := [
        { kind := .assign { local_ := 5, projection := [] }
            (.use (.copy { local_ := 2, projection := [] })),
          span := "d3" }
      ]
      terminator := { kind := .goto 3, span := "e1" }
      isCleanup := false },
    -- bb2 (a > b)
    { statements := [
        { kind := .assign { local_ := 5, projection := [] }
            (.use (.copy { local_ := 1, projection := [] })),
          span := "d4" }
      ]
      terminator := { kind := .goto 3, span := "e2" }
      isCleanup := false },
    -- bb3 (middle join)
    { statements := [
        { kind := .storageLive 6, span := "d5" },
        { kind := .assign { local_ := 6, projection := [] }
            (.binaryOp .le (.copy { local_ := 5, projection := [] })
              (.copy { local_ := 3, projection := [] })),
          span := "d6" }
      ]
      terminator := {
        kind := .switchInt (.move { local_ := 6, projection := [] })
          { branches := [(0, 5)], otherwise := 4 }
        span := "e3"
      }
      isCleanup := false },
    -- bb4 (m <= c)
    { statements := [
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.copy { local_ := 5, projection := [] })),
          span := "d7" }
      ]
      terminator := { kind := .goto 6, span := "e4" }
      isCleanup := false },
    -- bb5 (m > c)
    { statements := [
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.copy { local_ := 3, projection := [] })),
          span := "d8" }
      ]
      terminator := { kind := .goto 6, span := "e5" }
      isCleanup := false },
    -- bb6 (exit join & return)
    { statements := [
        { kind := .storageDead 6, span := "d9" }
      ]
      terminator := { kind := .return_, span := "e6" }
      isCleanup := false }
  ]
  fnAbi := {
    args := [
      { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct },
      { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct },
      { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct }
    ]
    ret := { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := MirLiftReadyWitness.witnessLayouts
  allocations := []

theorem checkMirLiftReady_witnessTwoDiamonds :
    checkMirLiftReady witnessTwoDiamonds = true := rfl

/-- **Sequential diamonds with shared joins, end to end**: the first diamond is a
postcondition-parametric path `bb0 -> bb3` (`liftBlock_switchInt_diamond_toJoin`),
the second is a family of paths `bb3 -> bb6` over the middle-join invariant, and
the exit block `bb6` is proved **once**; `liftBlock_two_diamonds_shared` glues
them, so neither join block is re-verified per incoming branch. -/
theorem verify_witnessTwoDiamonds_via_shared_joins :
    VerificationResult
      { body := witnessTwoDiamonds
        pre := fun args =>
          ∃ a b c : Nat,
            args = [.scalar { bits := a, sizeBytes := 4 }, .scalar { bits := b, sizeBytes := 4 },
                    .scalar { bits := c, sizeBytes := 4 }]
        post := fun args retVal =>
          ∀ a b c : Nat,
            args = [.scalar { bits := a, sizeBytes := 4 }, .scalar { bits := b, sizeBytes := 4 },
                    .scalar { bits := c, sizeBytes := 4 }] →
            retVal = .scalar { bits := if (if a ≤ b then b else a) ≤ c then
                (if a ≤ b then b else a) else c, sizeBytes := 4 }
        callees := [] } := by
  have hr := checkMirLiftReady_witnessTwoDiamonds
  refine verifyMirNoPanic_of_mirLiftReady_converges _ hr (fun args hpre => ?_)
  rcases hpre with ⟨a, b, c, rfl⟩
  dsimp only
  refine liftBlock_two_diamonds_shared (midBb := 3) (exitBb := 6)
    (MidInv := fun env => ∃ m : Nat, m = (if a ≤ b then b else a) ∧
      env = [.uninit, .init (.scalar ⟨a, 4⟩), .init (.scalar ⟨b, 4⟩), .init (.scalar ⟨c, 4⟩),
             .uninit, .init (.scalar ⟨m, 4⟩), .dead])
    (ExitInv := fun env => ∃ m : Nat, m = (if a ≤ b then b else a) ∧
      env = [.init (.scalar ⟨if m ≤ c then m else c, 4⟩), .init (.scalar ⟨a, 4⟩),
             .init (.scalar ⟨b, 4⟩), .init (.scalar ⟨c, 4⟩), .uninit, .init (.scalar ⟨m, 4⟩),
             .uninit])
    ?_ ?_ ?_
  · -- first diamond: bb0 -> {bb1, bb2} -> bb3 (postcondition-parametric)
    refine liftBlock_switchInt_diamond_toJoin (thenBb := 1) (elseBb := 2)
      (sc := boolToScalar (Nat.ble a b)) (a ≤ b) hr (by rfl) (by rfl) rfl (by rfl) ?_ ?_
    · intro hle
      refine ⟨?_, ?_⟩
      · change lookupSwitchTarget (boolToScalar (Nat.ble a b)).bits [(0, 2)] 1 = 1
        rw [Nat.ble_eq_true_of_le hle]; rfl
      · exact liftBlock_goto_toJoin hr (by rfl) (by rfl) rfl
          (LiftBlockToJoin.refl ⟨b, (ite_eq_left hle).symm, rfl⟩)
    · intro hgt
      have hble : Nat.ble a b = false :=
        Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (Nat.lt_of_not_le hgt)
      refine ⟨?_, ?_⟩
      · change lookupSwitchTarget (boolToScalar (Nat.ble a b)).bits [(0, 2)] 1 = 2
        rw [hble]; rfl
      · exact liftBlock_goto_toJoin hr (by rfl) (by rfl) rfl
          (LiftBlockToJoin.refl ⟨a, (ite_eq_right hgt).symm, rfl⟩)
  · -- second diamond: bb3 -> {bb4, bb5} -> bb6, for every middle-join environment
    intro env_m ⟨m, hm, h_env⟩
    subst h_env
    refine liftBlock_switchInt_diamond_toJoin (thenBb := 4) (elseBb := 5)
      (sc := boolToScalar (Nat.ble m c)) (m ≤ c) hr (by rfl) (by rfl) rfl (by rfl) ?_ ?_
    · intro hle
      refine ⟨?_, ?_⟩
      · change lookupSwitchTarget (boolToScalar (Nat.ble m c)).bits [(0, 5)] 4 = 4
        rw [Nat.ble_eq_true_of_le hle]; rfl
      · refine liftBlock_goto_toJoin hr (by rfl) (by rfl) rfl (LiftBlockToJoin.refl ⟨m, hm, ?_⟩)
        rw [ite_eq_left hle]
    · intro hgt
      have hble : Nat.ble m c = false :=
        Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (Nat.lt_of_not_le hgt)
      refine ⟨?_, ?_⟩
      · change lookupSwitchTarget (boolToScalar (Nat.ble m c)).bits [(0, 5)] 4 = 5
        rw [hble]; rfl
      · refine liftBlock_goto_toJoin hr (by rfl) (by rfl) rfl (LiftBlockToJoin.refl ⟨m, hm, ?_⟩)
        rw [ite_eq_right hgt]
  · -- exit join `bb6`, proved once
    intro env_e ⟨m, hm, h_env⟩
    subst h_env
    refine LiftBlockConverges.of_lookup (by rfl) ?_
    refine LiftStmtsConverges.eval_rest_checked_ready hr (by rfl) (by rfl) ?_
    refine LiftStmtsConverges.term_return_ready hr (by rfl) rfl rfl (by rfl) ?_
    intro a' b' c' h_eq
    injection h_eq with ha h_tl
    injection h_tl with hb h_tl'
    injection h_tl' with hc _
    injection ha with ha_sc
    injection ha_sc with ha_bits _
    injection hb with hb_sc
    injection hb_sc with hb_bits _
    injection hc with hc_sc
    injection hc_sc with hc_bits _
    subst ha_bits hb_bits hc_bits hm
    rfl

/-- **Cascading multi-guard early-return combinator (`liftBlock_early_exit_toJoin`)**:
a guard block `entryBb` branches on a decidable condition `C` between an
early-exit block `earlyBb` (which jumps directly to the shared return/cleanup
join block `exitBb` under `ExitInv`) and a continuation block `contBb` (which
may contain further guard diamonds also converging on `exitBb` under `ExitInv`).
Chaining `k` guards via `liftBlock_early_exit_toJoin` verifies `k + 1` incoming
return paths with $O(k)$ proof steps and a single shared proof of `exitBb`. -/
theorem liftBlock_early_exit_toJoin {body : CapturedMir}
    {entryBb earlyBb contBb exitBb : BasicBlockIdx}
    {bbEntry bbEarly : BasicBlockData} {env₀ envSw env' envEarly : PureEnv}
    {discr : Operand} {targets : SwitchTargets} {span spanEarly : String}
    {sc : ScalarInt} (C : Prop) [Decidable C] {ExitInv : PureEnv → Prop}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks entryBb = some bbEntry)
    (h_eval : evalPureStmtsCheckedN body entryBb bbEntry.statements
      (List.length bbEntry.statements) 0 env₀ = some envSw)
    (h_term : bbEntry.terminator = { kind := .switchInt discr targets, span := span })
    (h_op : MirLiftCore.evalPureOperand body envSw discr = .ok (.scalar sc) env')
    (h_early_bb : Trusted.Sequence.get? body.basicBlocks earlyBb = some bbEarly)
    (h_early_term : bbEarly.terminator = { kind := .goto exitBb, span := spanEarly })
    (h_early : C →
      lookupSwitchTarget sc.bits targets.branches targets.otherwise = earlyBb ∧
      evalPureStmtsCheckedN body earlyBb bbEarly.statements
        (List.length bbEarly.statements) 0 env' = some envEarly ∧
      ExitInv envEarly)
    (h_cont : ¬ C →
      lookupSwitchTarget sc.bits targets.branches targets.otherwise = contBb ∧
      LiftBlockToJoin body contBb env' exitBb ExitInv) :
    LiftBlockToJoin body entryBb env₀ exitBb ExitInv := by
  refine liftBlock_switchInt_diamond_toJoin (thenBb := earlyBb) (elseBb := contBb)
    C h_ready h_bb h_eval h_term h_op ?_ h_cont
  intro hC
  obtain ⟨h_tgt, h_ev, h_inv⟩ := h_early hC
  exact ⟨h_tgt, liftBlock_goto_toJoin h_ready h_early_bb h_ev h_early_term (LiftBlockToJoin.refl h_inv)⟩

/--
Cascading multi-guard early-return CFG witness (`argCount := 3`: `_1 = x`,
`_2 = lo`, `_3 = hi`, all `u32`), clamping `x` into `[lo, hi]` via two early
returns and a fallback branch that all converge on shared return block `bb5`:
- `bb0` (guard 1): `_4 = Le(Copy(_1), Copy(_2)); switchInt(Move(_4)) [0 => bb2, otherwise => bb1]`
- `bb1` (early return 1: `x ≤ lo`, 1 statement): `_0 = Copy(_2); goto -> bb5`
- `bb2` (guard 2: `lo < x`, 2 statements):
  `StorageLive(_5); _5 = Le(Copy(_3), Copy(_1)); switchInt(Move(_5)) [0 => bb4, otherwise => bb3]`
- `bb3` (early return 2: `hi ≤ x`, 2 statements): `StorageDead(_5); _0 = Copy(_3); goto -> bb5`
- `bb4` (normal path: `lo < x < hi`, 2 statements): `StorageDead(_5); _0 = Copy(_1); goto -> bb5`
- `bb5` (shared cleanup & return join block, reached by 3 paths of different depths!):
  `StorageDead(_4); return_`
-/
def witnessMultiGuardEarlyReturn : CapturedMir where
  defPath := "Anneal::MirLiftCore::witness_multi_guard_early_return"
  phase := .runtimeOptimized
  role := .subject
  argCount := 3
  localDecls := [
    { mutability := .mut, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "_0" },
    { mutability := .not, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "x" },
    { mutability := .not, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "lo" },
    { mutability := .not, ty := MirLiftReadyWitness.witnessU32Ty, debugName := some "hi" },
    { mutability := .mut, ty := MirLiftReadyWitness.witnessBoolTy, debugName := some "le_lo" },
    { mutability := .mut, ty := MirLiftReadyWitness.witnessBoolTy, debugName := some "ge_hi" }
  ]
  basicBlocks := [
    -- bb0: guard 1 (`x ≤ lo`)
    { statements := [
        { kind := .storageLive 4, span := "g0" },
        { kind := .assign { local_ := 4, projection := [] }
            (.binaryOp .le (.copy { local_ := 1, projection := [] })
              (.copy { local_ := 2, projection := [] })),
          span := "g1" }
      ]
      terminator := {
        kind := .switchInt (.move { local_ := 4, projection := [] })
          { branches := [(0, 2)], otherwise := 1 }
        span := "gt0"
      }
      isCleanup := false },
    -- bb1: early return `lo` (`x ≤ lo`)
    { statements := [
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.copy { local_ := 2, projection := [] })),
          span := "g2" }
      ]
      terminator := { kind := .goto 5, span := "gt1" }
      isCleanup := false },
    -- bb2: guard 2 (`hi ≤ x`)
    { statements := [
        { kind := .storageLive 5, span := "g3" },
        { kind := .assign { local_ := 5, projection := [] }
            (.binaryOp .le (.copy { local_ := 3, projection := [] })
              (.copy { local_ := 1, projection := [] })),
          span := "g4" }
      ]
      terminator := {
        kind := .switchInt (.move { local_ := 5, projection := [] })
          { branches := [(0, 4)], otherwise := 3 }
        span := "gt2"
      }
      isCleanup := false },
    -- bb3: early return `hi` (`hi ≤ x`)
    { statements := [
        { kind := .storageDead 5, span := "g5" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.copy { local_ := 3, projection := [] })),
          span := "g6" }
      ]
      terminator := { kind := .goto 5, span := "gt3" }
      isCleanup := false },
    -- bb4: fallback return `x` (`lo < x < hi`)
    { statements := [
        { kind := .storageDead 5, span := "g7" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.copy { local_ := 1, projection := [] })),
          span := "g8" }
      ]
      terminator := { kind := .goto 5, span := "gt4" }
      isCleanup := false },
    -- bb5: shared cleanup & return block (3 incoming branches of depths 2, 3, 3)
    { statements := [
        { kind := .storageDead 4, span := "g9" }
      ]
      terminator := { kind := .return_, span := "gt5" }
      isCleanup := false }
  ]
  fnAbi := {
    args := [
      { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct },
      { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct },
      { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct }
    ]
    ret := { layout := MirLiftReadyWitness.witnessU32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := MirLiftReadyWitness.witnessLayouts
  allocations := []

theorem checkMirLiftReady_witnessMultiGuardEarlyReturn :
    checkMirLiftReady witnessMultiGuardEarlyReturn = true := rfl

theorem checkMirLiftDagReady_witnessMultiGuardEarlyReturn :
    checkMirLiftDagReady witnessMultiGuardEarlyReturn = true := rfl

/-- **End-to-end multi-guard early-return verification via `liftBlock_early_exit_toJoin`**:
verifies the 3-way cascading guard clamp `witnessMultiGuardEarlyReturn` while
proving the shared cleanup/return block `bb5` **once**. -/
theorem verify_witnessMultiGuardEarlyReturn_via_early_exit :
    VerificationResult
      { body := witnessMultiGuardEarlyReturn
        pre := fun args =>
          ∃ x lo hi : Nat,
            args = [.scalar { bits := x, sizeBytes := 4 },
                    .scalar { bits := lo, sizeBytes := 4 },
                    .scalar { bits := hi, sizeBytes := 4 }]
        post := fun args retVal =>
          ∀ x lo hi : Nat,
            args = [.scalar { bits := x, sizeBytes := 4 },
                    .scalar { bits := lo, sizeBytes := 4 },
                    .scalar { bits := hi, sizeBytes := 4 }] →
            retVal = .scalar { bits := if x ≤ lo then lo else if hi ≤ x then hi else x,
                               sizeBytes := 4 }
        callees := [] } := by
  have hr := checkMirLiftReady_witnessMultiGuardEarlyReturn
  refine verifyMirNoPanic_of_mirLiftReady_converges _ hr (fun args hpre => ?_)
  rcases hpre with ⟨x, lo, hi, rfl⟩
  dsimp only
  let clamped := if x ≤ lo then lo else if hi ≤ x then hi else x
  refine LiftBlockToJoin.converges
    (joinBb := 5)
    (JoinInv := fun env =>
      env = [.init (.scalar ⟨clamped, 4⟩), .init (.scalar ⟨x, 4⟩),
             .init (.scalar ⟨lo, 4⟩), .init (.scalar ⟨hi, 4⟩), .uninit, .dead])
    ?_ ?_
  · -- guard 1 (`x ≤ lo`): early exit `bb1 -> bb5`, or continue to guard 2 (`bb2`)
    refine liftBlock_early_exit_toJoin (earlyBb := 1) (contBb := 2)
      (envEarly := [.init (.scalar ⟨lo, 4⟩), .init (.scalar ⟨x, 4⟩),
                    .init (.scalar ⟨lo, 4⟩), .init (.scalar ⟨hi, 4⟩), .uninit, .dead])
      (sc := boolToScalar (Nat.ble x lo)) (x ≤ lo)
      hr (by rfl) (by rfl) rfl (by rfl) (by rfl) rfl ?_ ?_
    · intro hle
      refine ⟨?_, rfl, ?_⟩
      · change lookupSwitchTarget (boolToScalar (Nat.ble x lo)).bits [(0, 2)] 1 = 1
        rw [Nat.ble_eq_true_of_le hle]; rfl
      · dsimp [clamped]; rw [ite_eq_left hle]
    · intro hgt
      have hble1 : Nat.ble x lo = false :=
        Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (Nat.lt_of_not_le hgt)
      refine ⟨?_, ?_⟩
      · change lookupSwitchTarget (boolToScalar (Nat.ble x lo)).bits [(0, 2)] 1 = 2
        rw [hble1]; rfl
      · -- guard 2 (`hi ≤ x`): early exit `bb3 -> bb5`, or fallback `bb4 -> bb5`
        refine liftBlock_early_exit_toJoin (earlyBb := 3) (contBb := 4)
          (envEarly := [.init (.scalar ⟨hi, 4⟩), .init (.scalar ⟨x, 4⟩),
                        .init (.scalar ⟨lo, 4⟩), .init (.scalar ⟨hi, 4⟩), .uninit, .dead])
          (sc := boolToScalar (Nat.ble hi x)) (hi ≤ x)
          hr (by rfl) (by rfl) rfl (by rfl) (by rfl) rfl ?_ ?_
        · intro hge
          refine ⟨?_, rfl, ?_⟩
          · change lookupSwitchTarget (boolToScalar (Nat.ble hi x)).bits [(0, 4)] 3 = 3
            rw [Nat.ble_eq_true_of_le hge]; rfl
          · dsimp [clamped]; rw [ite_eq_right hgt, ite_eq_left hge]
        · intro hlt
          have hble2 : Nat.ble hi x = false :=
            Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (Nat.lt_of_not_le hlt)
          refine ⟨?_, ?_⟩
          · change lookupSwitchTarget (boolToScalar (Nat.ble hi x)).bits [(0, 4)] 3 = 4
            rw [hble2]; rfl
          · refine liftBlock_goto_toJoin hr (by rfl) (by rfl) rfl (LiftBlockToJoin.refl ?_)
            dsimp [clamped]; rw [ite_eq_right hgt, ite_eq_right hlt]
  · -- shared cleanup & return block `bb5`, proved once
    intro env_e h_env
    subst h_env
    refine LiftBlockConverges.of_lookup (by rfl) ?_
    refine LiftStmtsConverges.eval_rest_checked_ready hr (by rfl) (by rfl) ?_
    refine LiftStmtsConverges.term_return_ready hr (by rfl) rfl rfl (by rfl) ?_
    intro x' lo' hi' h_eq
    injection h_eq with hx h_tl
    injection h_tl with hlo h_tl'
    injection h_tl' with hhi _
    injection hx with hx_sc
    injection hx_sc with hx_bits _
    injection hlo with hlo_sc
    injection hlo_sc with hlo_bits _
    injection hhi with hhi_sc
    injection hhi_sc with hhi_bits _
    subst hx_bits hlo_bits hhi_bits
    rfl

end DiamondJoinSharing

/-!
## Header-Targeted `runCfgToBlock` / `runMirToBlock`, Structural `forRangeUp`, and Fuel-Free Loop Lifting
-/

section FuelFreeLoops

/-- **Stationary-at-header limitation of live `Anneal.FunctionalTranslation.runMirToBlock`**:
because the live stepper checks `blockIdx == target && stmtIdx == 0` *before*
stepping, calling it from a loop header `(target, 0)` immediately returns `some s`
in zero steps without advancing through the loop body. -/
theorem live_runMirToBlock_stationary_at_target (body : CapturedMir)
    (target : BasicBlockIdx) (bound : Nat) (s : MachineState)
    (hbb : s.frame.blockIdx = target) (hstmt : s.frame.stmtIdx = 0) :
    Anneal.FunctionalTranslation.runMirToBlock (bound + 1) body target s = some s := by
  unfold Anneal.FunctionalTranslation.runMirToBlock
  have hcond : (Nat.beq s.frame.blockIdx target && Nat.beq s.frame.stmtIdx 0) = true := by
    rw [hbb, hstmt, Nat.beq_refl, Nat.beq_refl]; rfl
  rw [ite_eq_left hcond]

theorem live_runMirToBlock_step_of_not_target (body : CapturedMir)
    (target : BasicBlockIdx) (bound : Nat) (s : MachineState)
    (hnt : (s.frame.blockIdx == target && s.frame.stmtIdx == 0) = false) :
    Anneal.FunctionalTranslation.runMirToBlock (bound + 1) body target s =
      match mirStep body s with
      | .cont s' => Anneal.FunctionalTranslation.runMirToBlock bound body target s'
      | _ => none := by
  have hnt' : (Nat.beq s.frame.blockIdx target && Nat.beq s.frame.stmtIdx 0) = false := by
    simpa [BEq.beq] using hnt
  conv => lhs; unfold Anneal.FunctionalTranslation.runMirToBlock
  unfold mirStep
  rw [ite_eq_right (by rw [hnt']; exact Bool.false_ne_true)]
  cases hstep : stepMirFn body s with
  | ret _ => rfl
  | tau st =>
    cases st <;> rfl
  | vis req k =>
    rcases req with _ | (e | _)
    · rfl
    · cases e
      cases hk : k PUnit.unit <;> simp only [hk]
    · rfl

/-- **Exact bridge between `runUntilTarget (mirStep body)` and live
`Anneal.FunctionalTranslation.runMirToBlock`**: `runUntilTarget` reaches `s_hit`
within `bound` steps iff the live `runMirToBlock (bound + 1)` returns `some s_hit`. -/
theorem runUntilTarget_reached_iff_live_runMirToBlock (body : CapturedMir)
    (target : BasicBlockIdx) :
    ∀ (bound : Nat) (s s_hit : MachineState),
      runUntilTarget (mirStep body)
        (fun ms => ms.frame.blockIdx == target && ms.frame.stmtIdx == 0) bound s = .reached s_hit ↔
        Anneal.FunctionalTranslation.runMirToBlock (bound + 1) body target s = some s_hit
  | 0, s, s_hit => by
    unfold runUntilTarget
    cases ht : (s.frame.blockIdx == target && s.frame.stmtIdx == 0) with
    | true =>
      have ht' : (Nat.beq s.frame.blockIdx target && Nat.beq s.frame.stmtIdx 0) = true := by
        simpa [BEq.beq] using ht
      conv => rhs; lhs; unfold Anneal.FunctionalTranslation.runMirToBlock
      simp only [↓reduceIte, ht']
      exact Iff.intro (fun h => by cases h; rfl) (fun h => by cases h; rfl)
    | false =>
      rw [live_runMirToBlock_step_of_not_target body target 0 s ht]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases mirStep body s <;> exact Iff.intro (fun h => by cases h) (fun h => by cases h)
  | bound + 1, s, s_hit => by
    unfold runUntilTarget
    cases ht : (s.frame.blockIdx == target && s.frame.stmtIdx == 0) with
    | true =>
      have ht' : (Nat.beq s.frame.blockIdx target && Nat.beq s.frame.stmtIdx 0) = true := by
        simpa [BEq.beq] using ht
      conv => rhs; lhs; unfold Anneal.FunctionalTranslation.runMirToBlock
      simp only [↓reduceIte, ht']
      exact Iff.intro (fun h => by cases h; rfl) (fun h => by cases h; rfl)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [live_runMirToBlock_step_of_not_target body target (bound + 1) s ht]
      cases hs : mirStep body s with
      | cont s' =>
        exact runUntilTarget_reached_iff_live_runMirToBlock body target bound s' s_hit
      | done _ => exact Iff.intro (fun h => by cases h) (fun h => by cases h)
      | fault => exact Iff.intro (fun h => by cases h) (fun h => by cases h)

/-- **Exact bridge from header-advancing `runMirToBlock` to live
`Anneal.FunctionalTranslation.runMirToBlock`**: `runMirToBlock` reaches `s_hit`
iff taking one mandatory `mirStep` (`mirStep body s = .cont s₁`) followed by the
live `Anneal.FunctionalTranslation.runMirToBlock` reaches `s_hit`. -/
theorem runMirToBlock_reached_iff_step_and_live (body : CapturedMir)
    (target : BasicBlockIdx) (s s_hit : MachineState) :
    PureMirExec.runMirToBlock body target s = .reached s_hit ↔
      ∃ s₁, mirStep body s = .cont s₁ ∧
        Anneal.FunctionalTranslation.runMirToBlock (mirSegmentBound body + 1) body target s₁ = some s_hit := by
  unfold PureMirExec.runMirToBlock runToTarget
  cases hs : mirStep body s with
  | cont s₁ =>
    rw [runUntilTarget_reached_iff_live_runMirToBlock]
    exact Iff.intro (fun h => ⟨s₁, rfl, h⟩) (fun ⟨s₂, hs₂, h⟩ => by cases hs₂; exact h)
  | done _ =>
    exact Iff.intro (fun h => by cases h) (fun ⟨_, hs₁, _⟩ => by cases hs₁)
  | fault =>
    exact Iff.intro (fun h => by cases h) (fun ⟨_, hs₁, _⟩ => by cases hs₁)

/-- **Outcome-collapse characterization of live `Anneal.FunctionalTranslation.runMirToBlock`**:
the live stepper returns `none` iff `runUntilTarget` does not return `.reached _`,
thereby collapsing `.halted`, `.stuck`, and `.outOfFuel` into a single `none`. -/
theorem runUntilTarget_not_reached_iff_live_runMirToBlock_none (body : CapturedMir)
    (target : BasicBlockIdx) (bound : Nat) (s : MachineState) :
    (∀ s_hit, runUntilTarget (mirStep body)
      (fun ms => ms.frame.blockIdx == target && ms.frame.stmtIdx == 0) bound s ≠ .reached s_hit) ↔
      Anneal.FunctionalTranslation.runMirToBlock (bound + 1) body target s = none := by
  cases hlive : Anneal.FunctionalTranslation.runMirToBlock (bound + 1) body target s with
  | none =>
    refine Iff.intro (fun _ => rfl) (fun _ s_hit hreach => ?_)
    have hsome := (runUntilTarget_reached_iff_live_runMirToBlock body target bound s s_hit).mp hreach
    rw [hlive] at hsome
    cases hsome
  | some s_hit =>
    refine Iff.intro (fun hall => ?_) (fun hnone => by cases hnone)
    have hreach := (runUntilTarget_reached_iff_live_runMirToBlock body target bound s s_hit).mpr hlive
    exact absurd hreach (hall s_hit)

/-! ### Toy Multi-Block CFG Language (`Instr`, `CfgState`, `stepCfg`) & `MirFragment` Lattice Bridges -/

/-- One instruction per basic block (block-granular steps). -/
inductive Instr where
  /-- `env[dst] := c; goto next`. -/
  | setConst (dst c next : Nat)
  /-- `env[dst] := env[src] + c; goto next`. -/
  | addConst (dst src c next : Nat)
  /-- `if env[lhs] < env[rhs] then goto thenBB else goto elseBB`. -/
  | branchLt (lhs rhs thenBB elseBB : Nat)
  /-- Self-loop header: `if env[ctr] < env[bnd] then (env[ctr] += 1; goto loopBB) else goto exitBB`. -/
  | incBranchLt (ctr bnd loopBB exitBB : Nat)
  /-- `goto next`. -/
  | goto (next : Nat)
  /-- `return env[slot]`. -/
  | ret (slot : Nat)
  deriving DecidableEq, Repr

/-- Toy CFG machine state: current block and a slot environment. -/
structure CfgState where
  bb : Nat
  env : List Nat
  deriving DecidableEq, Repr

/-- Honest concrete block semantics: out-of-range blocks, slots, and reads fault. -/
def stepCfg (cfg : List Instr) (s : CfgState) : Step CfgState Nat :=
  match cfg[s.bb]? with
  | none => .fault
  | some (.setConst dst c next) =>
    if dst < s.env.length then .cont ⟨next, s.env.set dst c⟩ else .fault
  | some (.addConst dst src c next) =>
    match s.env[src]? with
    | some v => if dst < s.env.length then .cont ⟨next, s.env.set dst (v + c)⟩ else .fault
    | none => .fault
  | some (.branchLt lhs rhs thenBB elseBB) =>
    match s.env[lhs]?, s.env[rhs]? with
    | some a, some b => .cont ⟨if a < b then thenBB else elseBB, s.env⟩
    | _, _ => .fault
  | some (.incBranchLt ctr bnd loopBB exitBB) =>
    match s.env[ctr]?, s.env[bnd]? with
    | some i, some n =>
      if i < n then .cont ⟨loopBB, s.env.set ctr (i + 1)⟩ else .cont ⟨exitBB, s.env⟩
    | _, _ => .fault
  | some (.goto next) => .cont ⟨next, s.env⟩
  | some (.ret slot) =>
    match s.env[slot]? with
    | some v => .done v
    | none => .fault

/-- Successor blocks of a toy instruction, in the live `terminatorTargets` order. -/
def Instr.targets : Instr → List Nat
  | .setConst _ _ next => [next]
  | .addConst _ _ _ next => [next]
  | .branchLt _ _ thenBB elseBB => [elseBB, thenBB]
  | .incBranchLt _ _ loopBB exitBB => [exitBB, loopBB]
  | .goto next => [next]
  | .ret _ => []

def instrBackedgeAux : Nat → List Instr → Bool
  | _, [] => false
  | i, ins :: rest =>
    ins.targets.any (fun succ => decide (succ ≤ i)) || instrBackedgeAux (i + 1) rest

/-- Index-order back-edge detector for toy CFGs (mirrors the live `hasCfgBackedge`). -/
def hasInstrBackedge (cfg : List Instr) : Bool := instrBackedgeAux 0 cfg

protected def shapeSpan : String := "fuel-free-shape"

protected def shapeU64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }

protected def shapeLocal (i : Nat) : Place := { local_ := i, projection := [] }

protected def shapeConst (c : Nat) : Operand :=
  .constant { ty := MirLiftCore.shapeU64Ty, val := .scalar (.int ⟨c, 8⟩) }

protected def shapeBranch (lhs rhs thenBB elseBB : Nat) : BasicBlockData :=
  { statements :=
      [{ kind := .assign (MirLiftCore.shapeLocal 0)
           (.binaryOp .lt (.copy (MirLiftCore.shapeLocal lhs)) (.copy (MirLiftCore.shapeLocal rhs))),
         span := MirLiftCore.shapeSpan }],
    terminator :=
      { kind := .switchInt (.copy (MirLiftCore.shapeLocal 0)) { branches := [(0, elseBB)], otherwise := thenBB },
        span := MirLiftCore.shapeSpan },
    isCleanup := false }

/-- Shape translation of a toy instruction to a live basic block: identical
successor structure and pure statement kinds. -/
def Instr.toMirBlock : Instr → BasicBlockData
  | .setConst dst c next =>
    { statements := [{ kind := .assign (MirLiftCore.shapeLocal dst) (.use (MirLiftCore.shapeConst c)),
                       span := MirLiftCore.shapeSpan }],
      terminator := { kind := .goto next, span := MirLiftCore.shapeSpan }, isCleanup := false }
  | .addConst dst src c next =>
    { statements :=
        [{ kind := .assign (MirLiftCore.shapeLocal dst)
             (.binaryOp .add (.copy (MirLiftCore.shapeLocal src)) (MirLiftCore.shapeConst c)),
           span := MirLiftCore.shapeSpan }],
      terminator := { kind := .goto next, span := MirLiftCore.shapeSpan }, isCleanup := false }
  | .branchLt lhs rhs thenBB elseBB => MirLiftCore.shapeBranch lhs rhs thenBB elseBB
  | .incBranchLt ctr bnd loopBB exitBB => MirLiftCore.shapeBranch ctr bnd loopBB exitBB
  | .goto next =>
    { statements := [], terminator := { kind := .goto next, span := MirLiftCore.shapeSpan }, isCleanup := false }
  | .ret _ =>
    { statements := [], terminator := { kind := .return_, span := MirLiftCore.shapeSpan }, isCleanup := false }

/-- Live `CapturedMir` with the toy CFG's block shapes. -/
def toMirShape (cfg : List Instr) : CapturedMir :=
  { pureAdtMultiBlockBody with basicBlocks := cfg.map Instr.toMirBlock }

theorem blockTargets_toMirBlock (ins : Instr) : blockTargets ins.toMirBlock = ins.targets := by
  cases ins <;> rfl

theorem hasCfgBackedgeAux_map_toMirBlock :
    ∀ (i : Nat) (cfg : List Instr),
      hasCfgBackedgeAux i (cfg.map Instr.toMirBlock) = instrBackedgeAux i cfg
  | _, [] => rfl
  | i, ins :: rest => by
    simp only [List.map_cons, hasCfgBackedgeAux, instrBackedgeAux, hasBlockBackedge,
      blockTargets_toMirBlock, hasCfgBackedgeAux_map_toMirBlock (i + 1) rest]

/-- The live back-edge analysis of a translated shape equals the toy analysis. -/
theorem hasCfgBackedge_toMirShape (cfg : List Instr) :
    hasCfgBackedge (toMirShape cfg) = hasInstrBackedge cfg :=
  hasCfgBackedgeAux_map_toMirBlock 0 cfg

theorem checkBlockFragment_toMirBlock (f : MirFragment) (ins : Instr) :
    checkBlockFragment f ins.toMirBlock = true := by
  cases ins <;> rfl

theorem all_checkBlockFragment_toMirShape (f : MirFragment) (cfg : List Instr) :
    (cfg.map Instr.toMirBlock).all (checkBlockFragment f) = true := by
  induction cfg with
  | nil => rfl
  | cons ins rest ih =>
    simp only [List.map_cons, List.all_cons, checkBlockFragment_toMirBlock, ih, Bool.and_self]

/-- **`MirFragment` characterization**: the live minimal-fragment classifier
puts a toy CFG shape in `.pureBoundedLoop` exactly when it has a back-edge and
in `.pureLoopFree` otherwise; loop lifting targets the two lowest lattice levels. -/
theorem inferMinFragment_toMirShape (cfg : List Instr) :
    inferMinFragment (toMirShape cfg) =
      if hasInstrBackedge cfg then .pureBoundedLoop else .pureLoopFree := by
  have hall := all_checkBlockFragment_toMirShape
  have hbe := hasCfgBackedge_toMirShape cfg
  unfold inferMinFragment checkBodyFragment
  cases hb : hasInstrBackedge cfg with
  | true =>
    simp only [toMirShape] at hbe ⊢
    simp only [hall, hbe, hb, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  | false =>
    simp only [toMirShape] at hbe ⊢
    simp only [hall, hbe, hb, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]

/-- A loop-free straight-line CFG. -/
protected def straightLineCfg : List Instr := [.setConst 1 0 1, .addConst 1 1 2 2, .ret 1]

theorem inferMinFragment_straightLine :
    inferMinFragment (toMirShape MirLiftCore.straightLineCfg) = .pureLoopFree := by
  rw [inferMinFragment_toMirShape]
  rfl

/-- A straight-line shape whose first block takes `&mut _2` (a local borrow). -/
protected def refShapeBody : CapturedMir :=
  { toMirShape MirLiftCore.straightLineCfg with
    basicBlocks :=
      { statements :=
          [{ kind := .assign (MirLiftCore.shapeLocal 1)
               (.ref (.mut false) (MirLiftCore.shapeLocal 2)),
             span := MirLiftCore.shapeSpan }],
        terminator := { kind := .goto 1, span := MirLiftCore.shapeSpan }, isCleanup := false } ::
        (MirLiftCore.straightLineCfg.drop 1).map Instr.toMirBlock }

/-- Taking a local `&mut` borrow lifts the shape to `.treeBorrowsLocal`. -/
theorem inferMinFragment_refShape : inferMinFragment MirLiftCore.refShapeBody = .treeBorrowsLocal := rfl

/-- The three characterized levels are strictly ordered in the live lattice. -/
theorem fragment_levels_strict :
    MirFragment.pureLoopFree < .pureBoundedLoop ∧
      MirFragment.pureBoundedLoop < .treeBorrowsLocal :=
  ⟨by decide, by decide⟩

/-- **`runCfgToBlock`**: header-targeted block stepping on toy `Instr` CFGs
whose internal ceiling is derived from the CFG (`cfg.length`, an upper bound on
the length of any header-free acyclic segment), so call sites contain no step
numerals. -/
protected def runCfgToBlock (cfg : List Instr) (target : Nat) (s : CfgState) :
    TargetOutcome CfgState Nat :=
  runToTarget (stepCfg cfg) (fun s' => s'.bb == target) cfg.length s

theorem runCfgToBlock_reached_bb {cfg : List Instr} {target : Nat} {s s' : CfgState}
    (h : MirLiftCore.runCfgToBlock cfg target s = .reached s') : s'.bb = target := by
  unfold MirLiftCore.runCfgToBlock at h
  have ht := runToTarget_reached_atTarget h
  exact beq_iff_eq.mp ht

/-- **Target arrival soundness** for `runCfgToBlock`. -/
theorem stepsTo_of_runCfgToBlock_reached {cfg : List Instr} {target : Nat}
    {s s' : CfgState} (h : MirLiftCore.runCfgToBlock cfg target s = .reached s') :
    StepsTo (stepCfg cfg) s (· = s') :=
  stepsTo_of_runToTarget_reached h

/-- **Halting soundness** for `runCfgToBlock`. -/
theorem wpConverges_of_runCfgToBlock_halted {cfg : List Instr} {target : Nat}
    {s : CfgState} {v : Nat} {post : Nat → Prop}
    (h : MirLiftCore.runCfgToBlock cfg target s = .halted v) (hp : post v) :
    WpConverges (stepCfg cfg) s post :=
  wpConverges_of_runToTarget_halted h hp

/-- **Stuck soundness** for `runCfgToBlock`. -/
theorem not_wpConverges_of_runCfgToBlock_stuck {cfg : List Instr} {target : Nat}
    {s : CfgState} {post : Nat → Prop}
    (h : MirLiftCore.runCfgToBlock cfg target s = .stuck) : ¬ WpConverges (stepCfg cfg) s post :=
  not_wpConverges_of_runToTarget_stuck h

/-- Multi-block `countUp(n)` with a symbolic accumulator (slots `[n, i, acc]`). -/
def countUpCfg : List Instr :=
  [.setConst 1 0 1, .branchLt 1 0 2 4, .addConst 2 2 1 3, .addConst 1 1 1 1, .ret 2]

/-- Entry state of `countUp(n)` with accumulator `x` and arbitrary junk in `i`. -/
def countUpInit (n x junk : Nat) : CfgState := ⟨0, [n, junk, x]⟩

/-- Loop-header state of `countUp`. -/
def countUpHeader (n i acc : Nat) : CfgState := ⟨1, [n, i, acc]⟩

theorem countUp_entry_step (n x junk : Nat) :
    stepCfg countUpCfg (countUpInit n x junk) = .cont (countUpHeader n 0 x) := rfl

theorem countUp_header_exit_steps (n acc : Nat) :
    stepCfg countUpCfg (countUpHeader n n acc) = .cont ⟨4, [n, n, acc]⟩ ∧
      stepCfg countUpCfg ⟨4, [n, n, acc]⟩ = .done acc := by
  refine ⟨?_, rfl⟩
  simp [stepCfg, countUpCfg, countUpHeader]

theorem countUp_header_iter_steps (n i acc : Nat) (hlt : i < n) :
    stepCfg countUpCfg (countUpHeader n i acc) = .cont ⟨2, [n, i, acc]⟩ ∧
      stepCfg countUpCfg ⟨2, [n, i, acc]⟩ = .cont ⟨3, [n, i, acc + 1]⟩ ∧
      stepCfg countUpCfg ⟨3, [n, i, acc + 1]⟩ = .cont (countUpHeader n (i + 1) (acc + 1)) := by
  refine ⟨?_, rfl, rfl⟩
  simp [stepCfg, countUpCfg, countUpHeader, hlt]

/-- Exact fuel characterization of `countUp` from its header: with `d = n - i`
remaining iterations, `3 * d + 2` steps are necessary and sufficient. -/
theorem evalFuel_countUp_header :
    ∀ (d n i acc k : Nat), i + d = n →
      evalFuel (stepCfg countUpCfg) k (countUpHeader n i acc) =
        if 3 * d + 2 ≤ k then .halted (acc + d) else .outOfFuel
  | 0, n, i, acc, k, _ => by
    have hi : i = n := by omega
    subst hi
    obtain ⟨h1, h2⟩ := countUp_header_exit_steps i acc
    match k with
    | 0 => rfl
    | 1 => simp [evalFuel, h1]
    | k + 2 =>
      simp only [evalFuel, h1, h2]
      have hk : 3 * 0 + 2 ≤ k + 2 := by omega
      simp only [hk, ↓reduceIte, Nat.add_zero]
  | d + 1, n, i, acc, k, _ => by
    have hlt : i < n := by omega
    obtain ⟨h1, h2, h3⟩ := countUp_header_iter_steps n i acc hlt
    have ih := evalFuel_countUp_header d n (i + 1) (acc + 1)
    match k with
    | 0 => rfl
    | 1 => simp [evalFuel, h1]
    | 2 => simp [evalFuel, h1, h2]
    | k + 3 =>
      simp only [evalFuel, h1, h2, h3]
      rw [ih k (by omega)]
      by_cases hk : 3 * d + 2 ≤ k
      · have hk' : 3 * (d + 1) + 2 ≤ k + 3 := by omega
        simp only [hk, hk', ↓reduceIte, Nat.add_assoc, Nat.add_comm 1 d]
      · have hk' : ¬ 3 * (d + 1) + 2 ≤ k + 3 := by omega
        simp only [hk, hk', ↓reduceIte]

/-- Naive explicit-fuel verification of `countUp(n)` needs `3 * n + 3` steps. -/
theorem countUp_halts_with_fuel (n x junk : Nat) :
    evalFuel (stepCfg countUpCfg) (3 * n + 3) (countUpInit n x junk) = .halted (x + n) := by
  have h := evalFuel_countUp_header n n 0 x (3 * n + 2) (by omega)
  simp only [Nat.le_refl, ↓reduceIte] at h
  show evalFuel (stepCfg countUpCfg) ((3 * n + 2) + 1) (countUpInit n x junk) = _
  simp only [evalFuel, countUp_entry_step]
  exact h

/-- **Impossibility of a uniform fuel constant**: for the multi-block
`countUp(n)` CFG, no fixed `F : Nat` halts the program for every bound `n`. -/
theorem no_uniform_fuel_countUp :
    ¬ ∃ F : Nat, ∀ n : Nat, ∃ v, evalFuel (stepCfg countUpCfg) F (countUpInit n 0 0) = .halted v := by
  rintro ⟨F, hF⟩
  obtain ⟨v, hv⟩ := hF F
  match F, hv with
  | 0, hv => cases hv
  | F + 1, hv =>
    simp only [evalFuel, countUp_entry_step] at hv
    have hlt : ¬ 3 * (F + 1) + 2 ≤ F := by omega
    rw [evalFuel_countUp_header (F + 1) (F + 1) 0 0 F (by omega)] at hv
    simp only [hlt, ↓reduceIte] at hv
    cases hv

/-- One loop iteration from the re-entrant header `bb1` back to `bb1`: the
stepper stops at the first re-entry (three block steps), never overshooting. -/
theorem runCfgToBlock_countUp_iter (n i acc : Nat) (hlt : i < n) :
    MirLiftCore.runCfgToBlock countUpCfg 1 (countUpHeader n i acc) =
      .reached (countUpHeader n (i + 1) (acc + 1)) := by
  obtain ⟨h1, _, _⟩ := countUp_header_iter_steps n i acc hlt
  simp only [MirLiftCore.runCfgToBlock, runToTarget, h1]
  rfl

/-- Exit from the header halts with the accumulator. -/
theorem runCfgToBlock_countUp_exit (n acc : Nat) :
    MirLiftCore.runCfgToBlock countUpCfg 1 (countUpHeader n n acc) = .halted acc := by
  obtain ⟨h1, _⟩ := countUp_header_exit_steps n acc
  simp only [MirLiftCore.runCfgToBlock, runToTarget, h1]
  rfl

/-- The entry block reaches the loop header in one step. -/
theorem runCfgToBlock_countUp_entry (n x junk : Nat) :
    MirLiftCore.runCfgToBlock countUpCfg 1 (countUpInit n x junk) = .reached (countUpHeader n 0 x) := rfl

/-- Structurally recursive `for i in lo..hi` fold (re-exported in `MirLiftCore`). -/
protected def forRangeUp {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) : α :=
  PureMirExec.forRangeUp lo hi init step

/-- **Bridge to the live `Anneal.MirLoops.forRangeUp`**: the structural fold is
extensionally identical to the live well-founded definition. -/
theorem forRangeUp_eq_live {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    MirLiftCore.forRangeUp lo hi init step = Anneal.MirLoops.forRangeUp lo hi init step :=
  PureMirExec.forRangeUp_eq_live lo hi init step

/-- Non-empty step-unrolling identity (`lo < hi`) for `MirLiftCore.forRangeUp`. -/
protected theorem forRangeUp_step_of_lt {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (h : lo < hi) :
    MirLiftCore.forRangeUp lo hi init step =
      MirLiftCore.forRangeUp (lo + 1) hi (step lo (Nat.le_refl _) h init)
        (fun i h_le h_lt a => step i (Nat.le_trans (Nat.le_succ _) h_le) h_lt a) :=
  PureMirExec.forRangeUp_step_of_lt lo hi init step h

/-- **Structural `[lo, hi)` loop induction** (re-exported in `MirLiftCore`). -/
protected theorem forRangeUp_induction {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init)
    (hstep : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a, inv i a → inv (i + 1) (step i hlo hlt a)) :
    inv hi (MirLiftCore.forRangeUp lo hi init step) :=
  PureMirExec.forRangeUp_induction lo hi init step inv hle hinit hstep

/-- Range induction transported to the live `Anneal.MirLoops.forRangeUp`
through `forRangeUp_eq_live`. -/
theorem live_forRangeUp_induction {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init)
    (hstep : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a, inv i a → inv (i + 1) (step i hlo hlt a)) :
    inv hi (Anneal.MirLoops.forRangeUp lo hi init step) := by
  rw [← forRangeUp_eq_live]
  exact MirLiftCore.forRangeUp_induction lo hi init step inv hle hinit hstep

/-- **Kernel reducibility of the structural fold**: on concrete bounds the
structural `forRangeUp` evaluates by `rfl` even over a symbolic accumulator `x`
(no well-founded recursion to unfold, unlike the live
`Anneal.MirLoops.forRangeUp`, which needs `forRangeUp_step_of_lt` rewriting). -/
theorem forRangeUp_reduces_rfl (x : Nat) :
    MirLiftCore.forRangeUp 2 6 x (fun i _ _ acc => acc + i) = x + 2 + 3 + 4 + 5 :=
  rfl

/-- **Fuel-free total correctness of `countUp(n)` for every symbolic `n`** (and
symbolic accumulator `x`): the statement contains no fuel numeral, and the proof
composes `runCfgToBlock` segment soundness with `wpConverges_forRangeUp`. -/
theorem countUp_wpConverges_all_n (n x junk : Nat) :
    WpConverges (stepCfg countUpCfg) (countUpInit n x junk) (fun v => v = x + n) := by
  have hfold : PureMirExec.forRangeUp 0 n x (fun _ _ _ acc => acc + 1) = x + n :=
    PureMirExec.forRangeUp_induction 0 n x (fun _ _ _ acc => acc + 1) (fun i acc => acc = x + i)
      (Nat.zero_le n) rfl (fun _ _ _ _ h => by rw [h]; rfl)
  refine StepsTo.bind_wp (stepsTo_of_runCfgToBlock_reached (runCfgToBlock_countUp_entry n x junk))
    (fun s₁ hs₁ => ?_)
  subst hs₁
  refine wpConverges_forRangeUp (stepCfg countUpCfg) 0 n x (fun _ _ _ acc => acc + 1)
    (fun i acc s => s = countUpHeader n i acc) (countUpHeader n 0 x) (fun v => v = x + n)
    (Nat.zero_le n) rfl ?_ ?_
  · intro i _ hlt a s hs
    subst hs
    exact (stepsTo_of_runCfgToBlock_reached (runCfgToBlock_countUp_iter n i a hlt)).mono
      (fun _ h => h)
  · intro s_exit hs
    rw [hfold] at hs
    subst hs
    exact wpConverges_of_runCfgToBlock_halted (runCfgToBlock_countUp_exit n (x + n)) rfl

/-- Single-block self-loop (slots `[n, i]`): `bb0` re-enters itself directly. -/
def selfLoopCfg : List Instr := [.incBranchLt 1 0 0 1, .ret 1]

/-- **No overshoot on self-loops**: from the self-looping header, the stepper
stops after one iteration even though `bb0` is re-entered immediately. -/
theorem selfLoop_iter_step (n i : Nat) (hlt : i < n) :
    stepCfg selfLoopCfg ⟨0, [n, i]⟩ = .cont ⟨0, [n, i + 1]⟩ := by
  simp [stepCfg, selfLoopCfg, hlt]

theorem selfLoop_exit_steps (n : Nat) :
    stepCfg selfLoopCfg ⟨0, [n, n]⟩ = .cont ⟨1, [n, n]⟩ ∧
      stepCfg selfLoopCfg ⟨1, [n, n]⟩ = .done n := by
  refine ⟨?_, rfl⟩
  simp [stepCfg, selfLoopCfg]

theorem runCfgToBlock_selfLoop_no_overshoot (n i : Nat) (hlt : i < n) :
    MirLiftCore.runCfgToBlock selfLoopCfg 0 ⟨0, [n, i]⟩ = .reached ⟨0, [n, i + 1]⟩ := by
  simp only [MirLiftCore.runCfgToBlock, runToTarget, selfLoop_iter_step n i hlt]
  rfl

/-- The first-hit characterization pins the self-loop successor uniquely. -/
theorem selfLoop_firstHit_unique (n i : Nat) (hlt : i < n) {m : Nat} {s' : CfgState}
    (h : FirstHitIn (stepCfg selfLoopCfg) (fun s => s.bb == 0) m ⟨0, [n, i]⟩ s') :
    s' = ⟨0, [n, i + 1]⟩ ∧ m = 0 :=
  FirstHitIn.unique h (.here (selfLoop_iter_step n i hlt) rfl)

/-- Fuel-free convergence of the self-loop for every symbolic bound. -/
theorem selfLoop_wpConverges_all_n (n : Nat) :
    WpConverges (stepCfg selfLoopCfg) ⟨0, [n, 0]⟩ (fun v => v = n) := by
  refine wpConverges_forRangeUp (stepCfg selfLoopCfg) 0 n () (fun _ _ _ u => u)
    (fun i _ s => s = ⟨0, [n, i]⟩) ⟨0, [n, 0]⟩ (fun v => v = n) (Nat.zero_le n) rfl ?_ ?_
  · intro i _ hlt _ s hs
    subst hs
    exact (stepsTo_of_runCfgToBlock_reached (runCfgToBlock_selfLoop_no_overshoot n i hlt)).mono
      (fun _ h => h)
  · intro s_exit hs
    subst hs
    have hexit : MirLiftCore.runCfgToBlock selfLoopCfg 0 ⟨0, [n, n]⟩ = .halted n := by
      simp only [MirLiftCore.runCfgToBlock, runToTarget, (selfLoop_exit_steps n).1]
      rfl
    exact wpConverges_of_runCfgToBlock_halted hexit rfl

/-- `.stuck` is reported for a jump to a missing block and soundly refutes
convergence. -/
theorem runCfgToBlock_stuck_example :
    MirLiftCore.runCfgToBlock [.goto 7] 0 ⟨0, []⟩ = .stuck ∧
      ¬ WpConverges (stepCfg [.goto 7]) ⟨0, []⟩ (fun _ => True) :=
  ⟨rfl, not_wpConverges_of_runCfgToBlock_stuck (target := 0) rfl⟩

/-- `.outOfFuel` is inconclusive and ceiling-sensitive. -/
theorem runToTarget_outOfFuel_vs_reached (n i acc : Nat) (hlt : i < n) :
    runToTarget (stepCfg countUpCfg) (fun s => s.bb == 1) 0 (countUpHeader n i acc) = .outOfFuel ∧
      runToTarget (stepCfg countUpCfg) (fun s => s.bb == 1) 2 (countUpHeader n i acc) =
        .reached (countUpHeader n (i + 1) (acc + 1)) := by
  obtain ⟨h1, h2, h3⟩ := countUp_header_iter_steps n i acc hlt
  refine ⟨?_, ?_⟩
  · simp only [runToTarget, h1, runUntilTarget]; rfl
  · simp only [runToTarget, h1, runUntilTarget, h2, h3]; rfl

/-- Non-terminating single-block self-loop (`bb0: goto bb0`). -/
def infiniteLoopCfg : List Instr := [.goto 0]

theorem stepCfg_infiniteLoop (env : List Nat) :
    stepCfg infiniteLoopCfg ⟨0, env⟩ = .cont ⟨0, env⟩ := rfl

/-- **Non-terminating loop fuel characterization**: under every finite fuel
budget `k`, `infiniteLoopCfg` returns `.outOfFuel` (never `.halted` or `.faulted`). -/
theorem evalFuel_infiniteLoop_outOfFuel :
    ∀ (k : Nat) (env : List Nat),
      evalFuel (stepCfg infiniteLoopCfg) k ⟨0, env⟩ = .outOfFuel
  | 0, _ => rfl
  | k + 1, env => evalFuel_infiniteLoop_outOfFuel k env

/-- **Non-terminating loop refutes `WpConverges`**. -/
theorem not_wpConverges_infiniteLoop (env : List Nat) (post : Nat → Prop) :
    ¬ WpConverges (stepCfg infiniteLoopCfg) ⟨0, env⟩ post := by
  rintro ⟨k, v, hk, _⟩
  rw [evalFuel_infiniteLoop_outOfFuel k env] at hk
  cases hk

theorem runUntilTarget_infiniteLoop_unreached :
    ∀ (bound : Nat) (env : List Nat),
      runUntilTarget (stepCfg infiniteLoopCfg) (fun s => s.bb == 1) bound ⟨0, env⟩ = .outOfFuel
  | 0, _ => rfl
  | bound + 1, env => runUntilTarget_infiniteLoop_unreached bound env

/-- Targeting an unreachable exit block (`bb1`) on `infiniteLoopCfg` returns
`.outOfFuel` for every ceiling `bound`, whereas targeting the loop header (`bb0`)
stops after one step without overshooting. -/
theorem runToTarget_infiniteLoop_outOfFuel (bound : Nat) (env : List Nat) :
    runToTarget (stepCfg infiniteLoopCfg) (fun s => s.bb == 1) bound ⟨0, env⟩ = .outOfFuel ∧
      MirLiftCore.runCfgToBlock infiniteLoopCfg 0 ⟨0, env⟩ = .reached ⟨0, env⟩ :=
  ⟨runUntilTarget_infiniteLoop_unreached bound env, rfl⟩

theorem inferMinFragment_countUp :
    inferMinFragment (toMirShape countUpCfg) = .pureBoundedLoop := by
  rw [inferMinFragment_toMirShape]
  rfl

theorem inferMinFragment_selfLoop :
    inferMinFragment (toMirShape selfLoopCfg) = .pureBoundedLoop := by
  rw [inferMinFragment_toMirShape]
  rfl

/-- Nested `[0, n) × [0, m)` loops over slots `[n, m, i, j, acc]`: the outer header
`bb1` and the inner header `bb3` are distinct re-entrant blocks. -/
def nestedLoopCfg : List Instr :=
  [ .setConst 2 0 1,
    .branchLt 2 0 2 7,
    .setConst 3 0 3,
    .branchLt 3 1 4 6,
    .addConst 4 4 1 5,
    .addConst 3 3 1 3,
    .addConst 2 2 1 1,
    .ret 4 ]

/-- Outer header to inner header (`bb1 -> bb2 -> bb3`, resetting `j`). -/
theorem nestedLoop_outer_to_inner (n m i j acc : Nat) (hi : i < n) :
    MirLiftCore.runCfgToBlock nestedLoopCfg 3 ⟨1, [n, m, i, j, acc]⟩ =
      .reached ⟨3, [n, m, i, 0, acc]⟩ := by
  have h1 : stepCfg nestedLoopCfg ⟨1, [n, m, i, j, acc]⟩ = .cont ⟨2, [n, m, i, j, acc]⟩ := by
    simp [stepCfg, nestedLoopCfg, hi]
  simp only [MirLiftCore.runCfgToBlock, runToTarget, h1]
  rfl

/-- One inner iteration (`bb3 -> bb4 -> bb5 -> bb3`). -/
theorem nestedLoop_inner_iter (n m i j acc : Nat) (hj : j < m) :
    MirLiftCore.runCfgToBlock nestedLoopCfg 3 ⟨3, [n, m, i, j, acc]⟩ =
      .reached ⟨3, [n, m, i, j + 1, acc + 1]⟩ := by
  have h1 : stepCfg nestedLoopCfg ⟨3, [n, m, i, j, acc]⟩ = .cont ⟨4, [n, m, i, j, acc]⟩ := by
    simp [stepCfg, nestedLoopCfg, hj]
  simp only [MirLiftCore.runCfgToBlock, runToTarget, h1]
  rfl

/-- Inner exit back to the outer header (`bb3 -> bb6 -> bb1`). -/
theorem nestedLoop_inner_to_outer (n m i acc : Nat) :
    MirLiftCore.runCfgToBlock nestedLoopCfg 1 ⟨3, [n, m, i, m, acc]⟩ =
      .reached ⟨1, [n, m, i + 1, m, acc]⟩ := by
  have h1 : stepCfg nestedLoopCfg ⟨3, [n, m, i, m, acc]⟩ = .cont ⟨6, [n, m, i, m, acc]⟩ := by
    simp [stepCfg, nestedLoopCfg]
  simp only [MirLiftCore.runCfgToBlock, runToTarget, h1]
  rfl

/-- Outer exit (`bb1 -> bb7 -> return`). -/
theorem nestedLoop_exit (n m j acc : Nat) :
    MirLiftCore.runCfgToBlock nestedLoopCfg 1 ⟨1, [n, m, n, j, acc]⟩ = .halted acc := by
  have h1 : stepCfg nestedLoopCfg ⟨1, [n, m, n, j, acc]⟩ = .cont ⟨7, [n, m, n, j, acc]⟩ := by
    simp [stepCfg, nestedLoopCfg]
  simp only [MirLiftCore.runCfgToBlock, runToTarget, h1]
  rfl

/-- **Fuel-free total correctness of nested loops for all symbolic bounds**: the
outer `[0, n)` loop (`wpConverges_forRangeUp`) contains the inner `[0, m)` loop as a
segment (`stepsTo_forRangeUp`), with header-to-header `runCfgToBlock` segments and
arbitrary initial junk in both counters; no step count or fuel numeral appears. -/
theorem nestedLoop_wpConverges_all (n m x i₀ j₀ : Nat) :
    WpConverges (stepCfg nestedLoopCfg) ⟨0, [n, m, i₀, j₀, x]⟩ (fun v => v = x + n * m) := by
  have hfold : PureMirExec.forRangeUp 0 n x (fun _ _ _ acc => acc + m) = x + n * m :=
    PureMirExec.forRangeUp_induction 0 n x (fun _ _ _ acc => acc + m) (fun i acc => acc = x + i * m)
      (Nat.zero_le n) (by simp) (fun i _ _ a h => by rw [h, Nat.succ_mul, Nat.add_assoc])
  refine StepsTo.bind_wp (mid := fun s => s = ⟨1, [n, m, 0, j₀, x]⟩) ?_ (fun s₁ hs₁ => ?_)
  · exact StepsTo.step rfl (StepsTo.refl rfl)
  subst hs₁
  refine wpConverges_forRangeUp (stepCfg nestedLoopCfg) 0 n x (fun _ _ _ acc => acc + m)
    (fun i acc s => ∃ j, s = ⟨1, [n, m, i, j, acc]⟩) ⟨1, [n, m, 0, j₀, x]⟩ (fun v => v = x + n * m)
    (Nat.zero_le n) ⟨j₀, rfl⟩ ?_ ?_
  · intro i _ hlt acc s ⟨j, hs⟩
    subst hs
    refine (stepsTo_of_runCfgToBlock_reached (nestedLoop_outer_to_inner n m i j acc hlt)).trans
      (fun s₁ hs₁ => ?_)
    subst hs₁
    have hinner := stepsTo_forRangeUp (stepCfg nestedLoopCfg) 0 m acc (fun _ _ _ a => a + 1)
      (fun j a s => s = ⟨3, [n, m, i, j, a]⟩) ⟨3, [n, m, i, 0, acc]⟩ (Nat.zero_le m) rfl
      (fun j _ hj a s hs => by
        subst hs
        exact (stepsTo_of_runCfgToBlock_reached (nestedLoop_inner_iter n m i j a hj)).mono
          (fun _ h => h))
    have hinner_fold : PureMirExec.forRangeUp 0 m acc (fun _ _ _ a => a + 1) = acc + m :=
      PureMirExec.forRangeUp_induction 0 m acc (fun _ _ _ a => a + 1) (fun j a => a = acc + j)
        (Nat.zero_le m) rfl (fun j _ _ a h => by rw [h, Nat.add_assoc])
    rw [hinner_fold] at hinner
    refine hinner.trans (fun s₂ hs₂ => ?_)
    subst hs₂
    exact (stepsTo_of_runCfgToBlock_reached (nestedLoop_inner_to_outer n m i (acc + m))).mono
      (fun _ h => ⟨m, h⟩)
  · intro s_exit ⟨j, hs⟩
    rw [hfold] at hs
    subst hs
    exact wpConverges_of_runCfgToBlock_halted (nestedLoop_exit n m j (x + n * m)) rfl

theorem inferMinFragment_nestedLoop :
    inferMinFragment (toMirShape nestedLoopCfg) = .pureBoundedLoop := by
  rw [inferMinFragment_toMirShape]
  rfl

/-- **Live-MIR range loop as a segment (`MirStepsConverges`)**, stated with the live
`Anneal.MirLoops.forRangeUp`: the building block for nested loops over live
`CapturedMir` bodies. -/
theorem mirStepsConverges_forRangeUp {α : Type} (body : CapturedMir) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → MachineState → Prop)
    (s₀ : MachineState) (post : MirOutcome → Prop) (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s,
      inv i a s → StepsTo (mirStep body) s (inv (i + 1) (f i hlo hlt a))) :
    Anneal.MirFuelFree.MirStepsConverges body s₀
      (inv hi (Anneal.MirLoops.forRangeUp lo hi init f)) post := by
  have h := stepsTo_forRangeUp (mirStep body) lo hi init f inv s₀ hle hinit hiter
  change StepsTo (mirStep body) s₀ (inv hi (MirLiftCore.forRangeUp lo hi init f)) at h
  rw [forRangeUp_eq_live] at h
  exact mirStepsConverges_of_stepsTo h

/-- **Header-targeted `runMirToBlock` range loop as a segment (`StepsTo`)**:
when each iteration `[lo, hi)` steps from `stateAt i a` back to `headerBb` at
`stateAt (i + 1) (f i a)` via `PureMirExec.runMirToBlock`, the entire loop is a
single `StepsTo (mirStep body)` segment from `stateAt lo init` to
`stateAt hi (Anneal.MirLoops.forRangeUp lo hi init f)` with zero fuel numerals. -/
theorem stepsTo_forRangeUp_of_runMirToBlock {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (stateAt : Nat → α → MachineState)
    (hle : lo ≤ hi)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a,
      PureMirExec.runMirToBlock body headerBb (stateAt i a) =
        .reached (stateAt (i + 1) (f i hlo hlt a))) :
    StepsTo (mirStep body) (stateAt lo init)
      (fun s => s = stateAt hi (Anneal.MirLoops.forRangeUp lo hi init f)) := by
  have h := stepsTo_forRangeUp (mirStep body) lo hi init f
    (fun i a s => s = stateAt i a) (stateAt lo init) hle rfl
    (fun i hlo hlt a s hs => by
      subst hs
      exact stepsTo_of_runToTarget_reached (hiter i hlo hlt a))
  change StepsTo (mirStep body) (stateAt lo init)
    (fun s => s = stateAt hi (MirLiftCore.forRangeUp lo hi init f)) at h
  rwa [forRangeUp_eq_live] at h

/-- **Invariant-based `runMirToBlock` range loop as a segment (`StepsTo`)**:
reaches a loop-exit state satisfying `inv hi (Anneal.MirLoops.forRangeUp lo hi init f)`
from any header state satisfying `inv lo init`. -/
theorem stepsTo_forRangeUp_of_runMirToBlock_inv {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → MachineState → Prop)
    (s₀ : MachineState) (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s, inv i a s →
      ∃ s', PureMirExec.runMirToBlock body headerBb s = .reached s' ∧
        inv (i + 1) (f i hlo hlt a) s') :
    StepsTo (mirStep body) s₀ (inv hi (Anneal.MirLoops.forRangeUp lo hi init f)) := by
  have h := stepsTo_forRangeUp (mirStep body) lo hi init f inv s₀ hle hinit
    (fun i hlo hlt a s h_inv => by
      obtain ⟨s', h_step, h_inv'⟩ := hiter i hlo hlt a s h_inv
      exact (stepsTo_of_runToTarget_reached h_step).mono (by rintro _ rfl; exact h_inv'))
  change StepsTo (mirStep body) s₀ (inv hi (MirLiftCore.forRangeUp lo hi init f)) at h
  rwa [forRangeUp_eq_live] at h

/-- **Live-MIR `MirStepsConverges` range-loop segment via `runMirToBlock`**. -/
theorem mirStepsConverges_forRangeUp_of_runMirToBlock {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (stateAt : Nat → α → MachineState)
    (post : MirOutcome → Prop)
    (hle : lo ≤ hi)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a,
      PureMirExec.runMirToBlock body headerBb (stateAt i a) =
        .reached (stateAt (i + 1) (f i hlo hlt a))) :
    Anneal.MirFuelFree.MirStepsConverges body (stateAt lo init)
      (fun s => s = stateAt hi (Anneal.MirLoops.forRangeUp lo hi init f)) post :=
  mirStepsConverges_of_stepsTo
    (stepsTo_forRangeUp_of_runMirToBlock body headerBb lo hi init f stateAt hle hiter)

/-- **Invariant-based live-MIR `MirStepsConverges` range-loop segment via `runMirToBlock`**. -/
theorem mirStepsConverges_forRangeUp_of_runMirToBlock_inv {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → MachineState → Prop)
    (s₀ : MachineState) (post : MirOutcome → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s, inv i a s →
      ∃ s', PureMirExec.runMirToBlock body headerBb s = .reached s' ∧
        inv (i + 1) (f i hlo hlt a) s') :
    Anneal.MirFuelFree.MirStepsConverges body s₀
      (inv hi (Anneal.MirLoops.forRangeUp lo hi init f)) post :=
  mirStepsConverges_of_stepsTo
    (stepsTo_forRangeUp_of_runMirToBlock_inv body headerBb lo hi init f inv s₀ hle hinit hiter)

/-- **Alias-erased `PureMirStepsConverges` range-loop segment via `runMirToBlock`**. -/
theorem pureMirStepsConverges_forRangeUp_of_runMirToBlock {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (stateAt : Nat → α → PureState)
    (post : Value → Prop)
    (hle : lo ≤ hi)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a,
      PureMirExec.runMirToBlock body headerBb ((stateAt i a).toMachineState emptyMemory) =
        .reached ((stateAt (i + 1) (f i hlo hlt a)).toMachineState emptyMemory)) :
    PureMirStepsConverges body (stateAt lo init)
      (fun ps => ps = stateAt hi (Anneal.MirLoops.forRangeUp lo hi init f)) post := by
  have hs := stepsTo_forRangeUp_of_runMirToBlock body headerBb lo hi init f
    (fun i a => (stateAt i a).toMachineState emptyMemory) hle hiter
  refine pureMirStepsConverges_of_stepsTo (hs.mono ?_)
  intro ms' hms'
  rw [hms', PureState.ofMachineState_toMachineState]

/-- **Invariant-based alias-erased `PureMirStepsConverges` range-loop segment via `runMirToBlock`**. -/
theorem pureMirStepsConverges_forRangeUp_of_runMirToBlock_inv {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → PureState → Prop)
    (ps₀ : PureState) (post : Value → Prop)
    (hle : lo ≤ hi) (hinit : inv lo init ps₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a ps, inv i a ps →
      ∃ ps', PureMirExec.runMirToBlock body headerBb (ps.toMachineState emptyMemory) =
        .reached (ps'.toMachineState emptyMemory) ∧ inv (i + 1) (f i hlo hlt a) ps') :
    PureMirStepsConverges body ps₀
      (inv hi (Anneal.MirLoops.forRangeUp lo hi init f)) post := by
  have hs := stepsTo_forRangeUp_of_runMirToBlock_inv body headerBb lo hi init f
    (fun i a ms => ∃ ps, ms = ps.toMachineState emptyMemory ∧ inv i a ps)
    (ps₀.toMachineState emptyMemory) hle ⟨ps₀, rfl, hinit⟩
    (fun i hlo hlt a _ ⟨ps, hms, hps⟩ => by
      subst hms
      obtain ⟨ps', hstep, hinv'⟩ := hiter i hlo hlt a ps hps
      exact ⟨ps'.toMachineState emptyMemory, hstep, ps', rfl, hinv'⟩)
  refine pureMirStepsConverges_of_stepsTo (hs.mono ?_)
  rintro _ ⟨ps', rfl, hinv⟩
  rwa [PureState.ofMachineState_toMachineState]

/-- **Fuel-free range-loop rule for live MIR**, stated with the live
`Anneal.MirLoops.forRangeUp`. -/
protected theorem mirWpConverges_forRangeUp {α : Type} (body : CapturedMir) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → MachineState → Prop)
    (s₀ : MachineState) (post : MirOutcome → Prop) (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s,
      inv i a s → StepsTo (mirStep body) s (inv (i + 1) (f i hlo hlt a)))
    (hexit : ∀ s_exit, inv hi (Anneal.MirLoops.forRangeUp lo hi init f) s_exit →
      WpConverges (mirStep body) s_exit post) :
    Anneal.MirFuelFree.MirWpConverges body s₀ post := by
  refine mirWpConverges_of_wpConverges
    (wpConverges_forRangeUp (mirStep body) lo hi init f inv s₀ post hle hinit hiter ?_)
  intro s_exit h
  change inv hi (MirLiftCore.forRangeUp lo hi init f) s_exit at h
  rw [forRangeUp_eq_live] at h
  exact hexit s_exit h

/-- **Call-free range-loop rule for live MIR (`MirNoCallWpConverges`)** via `StepsTo (mirStep body)`. -/
theorem mirNoCallWpConverges_forRangeUp_of_stepsTo {α : Type}
    (body : CapturedMir) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α) (inv : Nat → α → MachineState → Prop)
    (s₀ : MachineState) (post : MirOutcome → Prop) (hle : lo ≤ hi) (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s,
      inv i a s → StepsTo (mirStep body) s (inv (i + 1) (f i hlo hlt a)))
    (hexit : ∀ s_exit, inv hi (Anneal.MirLoops.forRangeUp lo hi init f) s_exit →
      WpConverges (mirStep body) s_exit post) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s₀ post := by
  refine mirNoCallWpConverges_of_wpConverges
    (wpConverges_forRangeUp (mirStep body) lo hi init f inv s₀ post hle hinit hiter ?_)
  intro s_exit h
  change inv hi (MirLiftCore.forRangeUp lo hi init f) s_exit at h
  rw [forRangeUp_eq_live] at h
  exact hexit s_exit h

/-- **Header-targeted `runMirToBlock` range-loop rule (`MirNoCallWpConverges`)**:
takes an entry segment to `headerBb`, per-iteration `runMirToBlock` re-entry to
`headerBb`, and a halting exit segment from `headerBb`, discharging the loop
with zero fuel numerals. -/
theorem mirNoCallWpConverges_forRangeUp_of_runMirToBlock {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (stateAt : Nat → α → MachineState)
    (s₀ : MachineState) (post : MirOutcome → Prop)
    (hle : lo ≤ hi)
    (hentry : PureMirExec.runMirToBlock body headerBb s₀ = .reached (stateAt lo init))
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a,
      PureMirExec.runMirToBlock body headerBb (stateAt i a) =
        .reached (stateAt (i + 1) (f i hlo hlt a)))
    (hexit : ∃ out,
      PureMirExec.runMirToBlock body headerBb (stateAt hi (Anneal.MirLoops.forRangeUp lo hi init f)) =
        .halted out ∧ post out) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s₀ post := by
  refine mirNoCallWpConverges_of_stepsTo_bind
    (stepsTo_of_runToTarget_reached hentry) (fun s₁ hs₁ => ?_)
  subst hs₁
  refine mirNoCallWpConverges_forRangeUp_of_stepsTo body lo hi init f
    (fun i a s => s = stateAt i a) (stateAt lo init) post hle rfl ?_ ?_
  · intro i hlo hlt a s hs
    subst hs
    exact stepsTo_of_runToTarget_reached (hiter i hlo hlt a)
  · intro s_exit hs
    subst hs
    obtain ⟨out, hout, hp⟩ := hexit
    exact wpConverges_of_runToTarget_halted hout hp

/-- **Header-targeted `runMirToBlock` range-loop rule (`MirWpConverges`)**. -/
theorem mirWpConverges_forRangeUp_of_runMirToBlock {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (stateAt : Nat → α → MachineState)
    (s₀ : MachineState) (post : MirOutcome → Prop)
    (hle : lo ≤ hi)
    (hentry : PureMirExec.runMirToBlock body headerBb s₀ = .reached (stateAt lo init))
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a,
      PureMirExec.runMirToBlock body headerBb (stateAt i a) =
        .reached (stateAt (i + 1) (f i hlo hlt a)))
    (hexit : ∃ out,
      PureMirExec.runMirToBlock body headerBb (stateAt hi (Anneal.MirLoops.forRangeUp lo hi init f)) =
        .halted out ∧ post out) :
    Anneal.MirFuelFree.MirWpConverges body s₀ post :=
  Anneal.MirFuelFree.MirWpConverges.of_noCall
    (mirNoCallWpConverges_forRangeUp_of_runMirToBlock body headerBb lo hi init f
      stateAt s₀ post hle hentry hiter hexit)

/-- **Alias-erased `PureMirConverges` range-loop rule via `runMirToBlock`**. -/
theorem pureMirConverges_forRangeUp_of_runMirToBlock {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (stateAt : Nat → α → PureState)
    (ps₀ : PureState) (post : Value → Prop)
    (hle : lo ≤ hi)
    (hentry : PureMirExec.runMirToBlock body headerBb (ps₀.toMachineState emptyMemory) =
      .reached ((stateAt lo init).toMachineState emptyMemory))
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a,
      PureMirExec.runMirToBlock body headerBb ((stateAt i a).toMachineState emptyMemory) =
        .reached ((stateAt (i + 1) (f i hlo hlt a)).toMachineState emptyMemory))
    (hexit : ∃ retVal mem',
      PureMirExec.runMirToBlock body headerBb
        ((stateAt hi (Anneal.MirLoops.forRangeUp lo hi init f)).toMachineState emptyMemory) =
        .halted (.normal (retVal, mem')) ∧ post retVal) :
    PureMirConverges body ps₀ post := by
  refine mirWpConverges_forRangeUp_of_runMirToBlock body headerBb lo hi init f
    (fun i a => (stateAt i a).toMachineState emptyMemory)
    (ps₀.toMachineState emptyMemory)
    (mirNormalPost (fun retVal _ => post retVal))
    hle hentry hiter ?_
  obtain ⟨retVal, mem', hout, hp⟩ := hexit
  exact ⟨.normal (retVal, mem'), hout, hp⟩

/-- **Stateless `VerificationResult` gate for `.pureBoundedLoop` via `runMirToBlock` + `forRangeUp`**. -/
theorem verifyMirNoPanic_forRangeUp_of_runMirToBlock {α : Type}
    (c : Claim)
    (h_pure : checkPureMir c.body = true)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Nat)
    (init : List Value → α)
    (f : (args : List Value) → (i : Nat) → lo args ≤ i → i < hi args → α → α)
    (stateAt : List Value → Nat → α → PureState)
    (hle : ∀ args, c.pre args → lo args ≤ hi args)
    (hentry : ∀ args, c.pre args →
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached ((stateAt args (lo args) (init args)).toMachineState emptyMemory))
    (hiter : ∀ args, c.pre args → ∀ i (hlo : lo args ≤ i) (hlt : i < hi args) a,
      PureMirExec.runMirToBlock c.body headerBb ((stateAt args i a).toMachineState emptyMemory) =
        .reached ((stateAt args (i + 1) (f args i hlo hlt a)).toMachineState emptyMemory))
    (hexit : ∀ args, c.pre args → ∃ retVal mem',
      PureMirExec.runMirToBlock c.body headerBb
        ((stateAt args (hi args)
          (Anneal.MirLoops.forRangeUp (lo args) (hi args) (init args) (f args))).toMachineState emptyMemory) =
        .halted (.normal (retVal, mem')) ∧ c.post args retVal) :
    VerificationResult c :=
  verifyMirNoPanic_of_pureExec c h_pure (fun args hp =>
    pureMirConverges_forRangeUp_of_runMirToBlock c.body headerBb
      (lo args) (hi args) (init args) (f args) (stateAt args)
      (initPureState c.body args) (c.post args)
      (hle args hp) (hentry args hp) (hiter args hp) (hexit args hp))

/-- **Stateful `StatefulVerificationResult` gate for `.pureBoundedLoop` via `runMirToBlock` + `forRangeUp`**. -/
theorem verifyStatefulMirNoPanic_forRangeUp_of_runMirToBlock {α : Type}
    (c : StatefulClaim)
    (h_pure : checkPureMir c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Memory → Nat)
    (init : List Value → Memory → α)
    (f : (args : List Value) → (mem : Memory) → (i : Nat) → lo args mem ≤ i → i < hi args mem → α → α)
    (stateAt : List Value → Memory → Nat → α → PureState)
    (hle : ∀ args mem, c.pre args mem → lo args mem ≤ hi args mem)
    (hentry : ∀ args mem, c.pre args mem →
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached ((stateAt args mem (lo args mem) (init args mem)).toMachineState emptyMemory))
    (hiter : ∀ args mem, c.pre args mem → ∀ i (hlo : lo args mem ≤ i) (hlt : i < hi args mem) a,
      PureMirExec.runMirToBlock c.body headerBb ((stateAt args mem i a).toMachineState emptyMemory) =
        .reached ((stateAt args mem (i + 1) (f args mem i hlo hlt a)).toMachineState emptyMemory))
    (hexit : ∀ args mem, c.pre args mem → ∃ retVal mem_e,
      PureMirExec.runMirToBlock c.body headerBb
        ((stateAt args mem (hi args mem)
          (Anneal.MirLoops.forRangeUp (lo args mem) (hi args mem) (init args mem) (f args mem))).toMachineState emptyMemory) =
        .halted (.normal (retVal, mem_e)) ∧
        c.post args mem retVal
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees).memory) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_pureExec c h_pure h_root (fun args mem hp =>
    pureMirConverges_forRangeUp_of_runMirToBlock c.body headerBb
      (lo args mem) (hi args mem) (init args mem) (f args mem) (stateAt args mem)
      (initPureState c.body args) _
      (hle args mem hp) (hentry args mem hp) (hiter args mem hp) (hexit args mem hp))

/-- **Total-correctness `TotalVerificationResult` gate for `.pureBoundedLoop` via `runMirToBlock` + `forRangeUp`**. -/
theorem verifyTotalMir_forRangeUp_of_runMirToBlock {α : Type}
    (c : TotalClaim)
    (h_pure : checkPureMir c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Memory → Nat)
    (init : List Value → Memory → α)
    (f : (args : List Value) → (mem : Memory) → (i : Nat) → lo args mem ≤ i → i < hi args mem → α → α)
    (stateAt : List Value → Memory → Nat → α → PureState)
    (hle : ∀ args mem, c.pre args mem → lo args mem ≤ hi args mem)
    (hentry : ∀ args mem, c.pre args mem →
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached ((stateAt args mem (lo args mem) (init args mem)).toMachineState emptyMemory))
    (hiter : ∀ args mem, c.pre args mem → ∀ i (hlo : lo args mem ≤ i) (hlt : i < hi args mem) a,
      PureMirExec.runMirToBlock c.body headerBb ((stateAt args mem i a).toMachineState emptyMemory) =
        .reached ((stateAt args mem (i + 1) (f args mem i hlo hlt a)).toMachineState emptyMemory))
    (hexit : ∀ args mem, c.pre args mem → ∃ retVal mem_e,
      PureMirExec.runMirToBlock c.body headerBb
        ((stateAt args mem (hi args mem)
          (Anneal.MirLoops.forRangeUp (lo args mem) (hi args mem) (init args mem) (f args mem))).toMachineState emptyMemory) =
        .halted (.normal (retVal, mem_e)) ∧
        c.post args mem retVal
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees).memory) :
    TotalVerificationResult c :=
  verifyTotalMir_of_pureExec c h_pure h_root (fun args mem hp =>
    pureMirConverges_forRangeUp_of_runMirToBlock c.body headerBb
      (lo args mem) (hi args mem) (init args mem) (f args mem) (stateAt args mem)
      (initPureState c.body args) _
      (hle args mem hp) (hentry args mem hp) (hiter args mem hp) (hexit args mem hp))

/-! ### Invariant-based `runMirToBlock` loop gates

The gates above pin the loop-header state exactly (`stateAt i acc`). Real MIR
headers often carry slots that are not a function of the loop counter (stale
temporaries, arguments, symbolic `LocalSlot`s), so the variants below take a
header **invariant** `inv i acc ps` instead and quantify over every header state
satisfying it. -/

/-- **Call-free invariant-based `MirNoCallWpConverges` range-loop rule via `runMirToBlock`**. -/
theorem mirNoCallWpConverges_forRangeUp_of_runMirToBlock_inv {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → MachineState → Prop)
    (s₀ : MachineState) (post : MirOutcome → Prop)
    (hle : lo ≤ hi)
    (hentry : ∃ s₁, PureMirExec.runMirToBlock body headerBb s₀ = .reached s₁ ∧ inv lo init s₁)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s, inv i a s →
      ∃ s', PureMirExec.runMirToBlock body headerBb s = .reached s' ∧
        inv (i + 1) (f i hlo hlt a) s')
    (hexit : ∀ s_exit, inv hi (Anneal.MirLoops.forRangeUp lo hi init f) s_exit →
      ∃ out, PureMirExec.runMirToBlock body headerBb s_exit = .halted out ∧ post out) :
    Anneal.MirFuelFree.MirNoCallWpConverges body s₀ post := by
  obtain ⟨s₁, h_entry, h_inv₁⟩ := hentry
  refine mirNoCallWpConverges_of_stepsTo_bind
    (stepsTo_of_runToTarget_reached h_entry) (fun s_start hs => ?_)
  cases hs
  refine mirNoCallWpConverges_forRangeUp_of_stepsTo body lo hi init f inv s₁ post hle h_inv₁ ?_ ?_
  · intro i hlo hlt a s h_inv
    obtain ⟨s', h_step, h_inv'⟩ := hiter i hlo hlt a s h_inv
    exact (stepsTo_of_runToTarget_reached h_step).mono (by rintro _ rfl; exact h_inv')
  · intro s_exit h_inv
    obtain ⟨out, h_halt, h_post⟩ := hexit s_exit h_inv
    exact wpConverges_of_runToTarget_halted h_halt h_post

/-- **Invariant-based `MirWpConverges` range-loop rule via `runMirToBlock`**. -/
theorem mirWpConverges_forRangeUp_of_runMirToBlock_inv {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → MachineState → Prop)
    (s₀ : MachineState) (post : MirOutcome → Prop)
    (hle : lo ≤ hi)
    (hentry : ∃ s₁, PureMirExec.runMirToBlock body headerBb s₀ = .reached s₁ ∧ inv lo init s₁)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s, inv i a s →
      ∃ s', PureMirExec.runMirToBlock body headerBb s = .reached s' ∧
        inv (i + 1) (f i hlo hlt a) s')
    (hexit : ∀ s_exit, inv hi (Anneal.MirLoops.forRangeUp lo hi init f) s_exit →
      ∃ out, PureMirExec.runMirToBlock body headerBb s_exit = .halted out ∧ post out) :
    Anneal.MirFuelFree.MirWpConverges body s₀ post :=
  Anneal.MirFuelFree.MirWpConverges.of_noCall
    (mirNoCallWpConverges_forRangeUp_of_runMirToBlock_inv body headerBb lo hi init f
      inv s₀ post hle hentry hiter hexit)

/-- **Invariant-based `PureMirConverges` range-loop rule via `runMirToBlock`**:
every header state satisfying `inv i acc` re-enters the header in a state
satisfying `inv (i + 1) (f i acc)`, and every exit state satisfying
`inv hi (forRangeUp lo hi init f)` halts normally in `post`. -/
theorem pureMirConverges_forRangeUp_of_runMirToBlock_inv {α : Type}
    (body : CapturedMir) (headerBb : BasicBlockIdx) (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → PureState → Prop)
    (ps₀ : PureState) (post : Value → Prop)
    (hle : lo ≤ hi)
    (hentry : ∃ ps₁, PureMirExec.runMirToBlock body headerBb (ps₀.toMachineState emptyMemory) =
      .reached (ps₁.toMachineState emptyMemory) ∧ inv lo init ps₁)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a ps, inv i a ps →
      ∃ ps', PureMirExec.runMirToBlock body headerBb (ps.toMachineState emptyMemory) =
        .reached (ps'.toMachineState emptyMemory) ∧ inv (i + 1) (f i hlo hlt a) ps')
    (hexit : ∀ ps, inv hi (Anneal.MirLoops.forRangeUp lo hi init f) ps → ∃ retVal mem',
      PureMirExec.runMirToBlock body headerBb (ps.toMachineState emptyMemory) =
        .halted (.normal (retVal, mem')) ∧ post retVal) :
    PureMirConverges body ps₀ post := by
  obtain ⟨ps₁, h_entry, h_inv₁⟩ := hentry
  refine mirWpConverges_forRangeUp_of_runMirToBlock_inv body headerBb lo hi init f
    (fun i a ms => ∃ ps, ms = ps.toMachineState emptyMemory ∧ inv i a ps)
    (ps₀.toMachineState emptyMemory) (mirNormalPost (fun retVal _ => post retVal)) hle
    ⟨ps₁.toMachineState emptyMemory, h_entry, ps₁, rfl, h_inv₁⟩ ?_ ?_
  · intro i hlo hlt a _ ⟨ps, hms, hps⟩
    subst hms
    obtain ⟨ps', h_step, h_inv'⟩ := hiter i hlo hlt a ps hps
    exact ⟨ps'.toMachineState emptyMemory, h_step, ps', rfl, h_inv'⟩
  · intro _ ⟨ps, hms, hps⟩
    subst hms
    obtain ⟨retVal, mem', h_halt, h_post⟩ := hexit ps hps
    exact ⟨.normal (retVal, mem'), h_halt, h_post⟩

/-- **Invariant-based stateless loop gate** (`VerificationResult`). -/
theorem verifyMirNoPanic_forRangeUp_of_runMirToBlock_inv {α : Type}
    (c : Claim)
    (h_pure : checkPureMir c.body = true)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Nat)
    (init : List Value → α)
    (f : (args : List Value) → (i : Nat) → lo args ≤ i → i < hi args → α → α)
    (inv : List Value → Nat → α → PureState → Prop)
    (hle : ∀ args, c.pre args → lo args ≤ hi args)
    (hentry : ∀ args, c.pre args → ∃ ps₁,
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached (ps₁.toMachineState emptyMemory) ∧ inv args (lo args) (init args) ps₁)
    (hiter : ∀ args, c.pre args → ∀ i (hlo : lo args ≤ i) (hlt : i < hi args) a ps,
      inv args i a ps → ∃ ps',
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .reached (ps'.toMachineState emptyMemory) ∧ inv args (i + 1) (f args i hlo hlt a) ps')
    (hexit : ∀ args, c.pre args → ∀ ps,
      inv args (hi args) (Anneal.MirLoops.forRangeUp (lo args) (hi args) (init args) (f args)) ps →
      ∃ retVal mem',
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .halted (.normal (retVal, mem')) ∧ c.post args retVal) :
    VerificationResult c :=
  verifyMirNoPanic_of_pureExec c h_pure (fun args hp =>
    pureMirConverges_forRangeUp_of_runMirToBlock_inv c.body headerBb
      (lo args) (hi args) (init args) (f args) (inv args)
      (initPureState c.body args) (c.post args)
      (hle args hp) (hentry args hp) (hiter args hp) (hexit args hp))

/-- **Invariant-based stateful loop gate** (`StatefulVerificationResult`). -/
theorem verifyStatefulMirNoPanic_forRangeUp_of_runMirToBlock_inv {α : Type}
    (c : StatefulClaim)
    (h_pure : checkPureMir c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Memory → Nat)
    (init : List Value → Memory → α)
    (f : (args : List Value) → (mem : Memory) → (i : Nat) → lo args mem ≤ i → i < hi args mem → α → α)
    (inv : List Value → Memory → Nat → α → PureState → Prop)
    (hle : ∀ args mem, c.pre args mem → lo args mem ≤ hi args mem)
    (hentry : ∀ args mem, c.pre args mem → ∃ ps₁,
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached (ps₁.toMachineState emptyMemory) ∧ inv args mem (lo args mem) (init args mem) ps₁)
    (hiter : ∀ args mem, c.pre args mem → ∀ i (hlo : lo args mem ≤ i) (hlt : i < hi args mem) a ps,
      inv args mem i a ps → ∃ ps',
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .reached (ps'.toMachineState emptyMemory) ∧
          inv args mem (i + 1) (f args mem i hlo hlt a) ps')
    (hexit : ∀ args mem, c.pre args mem → ∀ ps,
      inv args mem (hi args mem)
        (Anneal.MirLoops.forRangeUp (lo args mem) (hi args mem) (init args mem) (f args mem)) ps →
      ∃ retVal mem_e,
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .halted (.normal (retVal, mem_e)) ∧
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_pureExec c h_pure h_root (fun args mem hp =>
    pureMirConverges_forRangeUp_of_runMirToBlock_inv c.body headerBb
      (lo args mem) (hi args mem) (init args mem) (f args mem) (inv args mem)
      (initPureState c.body args) _
      (hle args mem hp) (hentry args mem hp) (hiter args mem hp) (hexit args mem hp))

/-- **Invariant-based total-correctness loop gate** (`TotalVerificationResult`). -/
theorem verifyTotalMir_forRangeUp_of_runMirToBlock_inv {α : Type}
    (c : TotalClaim)
    (h_pure : checkPureMir c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Memory → Nat)
    (init : List Value → Memory → α)
    (f : (args : List Value) → (mem : Memory) → (i : Nat) → lo args mem ≤ i → i < hi args mem → α → α)
    (inv : List Value → Memory → Nat → α → PureState → Prop)
    (hle : ∀ args mem, c.pre args mem → lo args mem ≤ hi args mem)
    (hentry : ∀ args mem, c.pre args mem → ∃ ps₁,
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached (ps₁.toMachineState emptyMemory) ∧ inv args mem (lo args mem) (init args mem) ps₁)
    (hiter : ∀ args mem, c.pre args mem → ∀ i (hlo : lo args mem ≤ i) (hlt : i < hi args mem) a ps,
      inv args mem i a ps → ∃ ps',
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .reached (ps'.toMachineState emptyMemory) ∧
          inv args mem (i + 1) (f args mem i hlo hlt a) ps')
    (hexit : ∀ args mem, c.pre args mem → ∀ ps,
      inv args mem (hi args mem)
        (Anneal.MirLoops.forRangeUp (lo args mem) (hi args mem) (init args mem) (f args mem)) ps →
      ∃ retVal mem_e,
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .halted (.normal (retVal, mem_e)) ∧
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory) :
    TotalVerificationResult c :=
  verifyTotalMir_of_pureExec c h_pure h_root (fun args mem hp =>
    pureMirConverges_forRangeUp_of_runMirToBlock_inv c.body headerBb
      (lo args mem) (hi args mem) (init args mem) (f args mem) (inv args mem)
      (initPureState c.body args) _
      (hle args mem hp) (hentry args mem hp) (hiter args mem hp) (hexit args mem hp))

/-- **`MirFragment`-keyed invariant-based stateless loop gate** (`VerificationResult`). -/
theorem verifyMirNoPanic_forRangeUp_of_inferMinFragment_le_pureBoundedLoop_inv {α : Type}
    (c : Claim)
    (h_frag : inferMinFragment c.body ≤ .pureBoundedLoop)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Nat)
    (init : List Value → α)
    (f : (args : List Value) → (i : Nat) → lo args ≤ i → i < hi args → α → α)
    (inv : List Value → Nat → α → PureState → Prop)
    (hle : ∀ args, c.pre args → lo args ≤ hi args)
    (hentry : ∀ args, c.pre args → ∃ ps₁,
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached (ps₁.toMachineState emptyMemory) ∧ inv args (lo args) (init args) ps₁)
    (hiter : ∀ args, c.pre args → ∀ i (hlo : lo args ≤ i) (hlt : i < hi args) a ps,
      inv args i a ps → ∃ ps',
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .reached (ps'.toMachineState emptyMemory) ∧ inv args (i + 1) (f args i hlo hlt a) ps')
    (hexit : ∀ args, c.pre args → ∀ ps,
      inv args (hi args) (Anneal.MirLoops.forRangeUp (lo args) (hi args) (init args) (f args)) ps →
      ∃ retVal mem',
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .halted (.normal (retVal, mem')) ∧ c.post args retVal)
    (h_no_ptr_rel : hasNoPtrRelationalAssign c.body = true := by decide) :
    VerificationResult c :=
  verifyMirNoPanic_forRangeUp_of_runMirToBlock_inv c
    (checkPureMir_of_inferMinFragment_le_pureBoundedLoop c.body h_frag h_no_ptr_rel)
    headerBb lo hi init f inv hle hentry hiter hexit

/-- **`MirFragment`-keyed invariant-based stateful loop gate** (`StatefulVerificationResult`). -/
theorem verifyStatefulMirNoPanic_forRangeUp_of_inferMinFragment_le_pureBoundedLoop_inv {α : Type}
    (c : StatefulClaim)
    (h_frag : inferMinFragment c.body ≤ .pureBoundedLoop)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Memory → Nat)
    (init : List Value → Memory → α)
    (f : (args : List Value) → (mem : Memory) → (i : Nat) → lo args mem ≤ i → i < hi args mem → α → α)
    (inv : List Value → Memory → Nat → α → PureState → Prop)
    (hle : ∀ args mem, c.pre args mem → lo args mem ≤ hi args mem)
    (hentry : ∀ args mem, c.pre args mem → ∃ ps₁,
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached (ps₁.toMachineState emptyMemory) ∧ inv args mem (lo args mem) (init args mem) ps₁)
    (hiter : ∀ args mem, c.pre args mem → ∀ i (hlo : lo args mem ≤ i) (hlt : i < hi args mem) a ps,
      inv args mem i a ps → ∃ ps',
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .reached (ps'.toMachineState emptyMemory) ∧
          inv args mem (i + 1) (f args mem i hlo hlt a) ps')
    (hexit : ∀ args mem, c.pre args mem → ∀ ps,
      inv args mem (hi args mem)
        (Anneal.MirLoops.forRangeUp (lo args mem) (hi args mem) (init args mem) (f args mem)) ps →
      ∃ retVal mem_e,
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .halted (.normal (retVal, mem_e)) ∧
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)
    (h_no_ptr_rel : hasNoPtrRelationalAssign c.body = true := by decide) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_forRangeUp_of_runMirToBlock_inv c
    (checkPureMir_of_inferMinFragment_le_pureBoundedLoop c.body h_frag h_no_ptr_rel)
    h_root headerBb lo hi init f inv hle hentry hiter hexit

/-- **`MirFragment`-keyed invariant-based total-correctness loop gate** (`TotalVerificationResult`). -/
theorem verifyTotalMir_forRangeUp_of_inferMinFragment_le_pureBoundedLoop_inv {α : Type}
    (c : TotalClaim)
    (h_frag : inferMinFragment c.body ≤ .pureBoundedLoop)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Memory → Nat)
    (init : List Value → Memory → α)
    (f : (args : List Value) → (mem : Memory) → (i : Nat) → lo args mem ≤ i → i < hi args mem → α → α)
    (inv : List Value → Memory → Nat → α → PureState → Prop)
    (hle : ∀ args mem, c.pre args mem → lo args mem ≤ hi args mem)
    (hentry : ∀ args mem, c.pre args mem → ∃ ps₁,
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached (ps₁.toMachineState emptyMemory) ∧ inv args mem (lo args mem) (init args mem) ps₁)
    (hiter : ∀ args mem, c.pre args mem → ∀ i (hlo : lo args mem ≤ i) (hlt : i < hi args mem) a ps,
      inv args mem i a ps → ∃ ps',
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .reached (ps'.toMachineState emptyMemory) ∧
          inv args mem (i + 1) (f args mem i hlo hlt a) ps')
    (hexit : ∀ args mem, c.pre args mem → ∀ ps,
      inv args mem (hi args mem)
        (Anneal.MirLoops.forRangeUp (lo args mem) (hi args mem) (init args mem) (f args mem)) ps →
      ∃ retVal mem_e,
        PureMirExec.runMirToBlock c.body headerBb (ps.toMachineState emptyMemory) =
          .halted (.normal (retVal, mem_e)) ∧
          c.post args mem retVal
            (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
              c.body args mem c.callees).memory)
    (h_no_ptr_rel : hasNoPtrRelationalAssign c.body = true := by decide) :
    TotalVerificationResult c :=
  verifyTotalMir_forRangeUp_of_runMirToBlock_inv c
    (checkPureMir_of_inferMinFragment_le_pureBoundedLoop c.body h_frag h_no_ptr_rel)
    h_root headerBb lo hi init f inv hle hentry hiter hexit

/-- Entry segment of the live `Anneal.MirLoops.countToNBody n` executed through
`runMirToBlock` (reaches loop header `bb1` in two steps). -/
theorem runMirToBlock_countToN_entry (n : Nat) :
    PureMirExec.runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      (Anneal.MirLoops.countStateMem 0 0 0 emptyMemory) =
      .reached (Anneal.MirLoops.countStateMem 1 0 0 emptyMemory) := rfl

/-- Loop-body iteration segment of the live `Anneal.MirLoops.countToNBody n`
executed through `runMirToBlock`: steps across `bb1`'s `.switchInt` (`.emitStep`)
and `bb2`'s increment + `goto 1` back to `bb1` without overshooting. -/
theorem runMirToBlock_countToN_iter (n i : Nat) (hlt : i < n) (hn : n < 4294967296) :
    PureMirExec.runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      (Anneal.MirLoops.countStateMem 1 0 i emptyMemory) =
      .reached (Anneal.MirLoops.countStateMem 1 0 (i + 1) emptyMemory) := by
  have hbeq : Nat.beq i n = false := (Bool.not_eq_true _).mp (Nat.ne_of_lt hlt ∘ Nat.eq_of_beq_eq_true)
  have hs1 : mirStep (Anneal.MirLoops.countToNBody n) (Anneal.MirLoops.countStateMem 1 0 i emptyMemory) =
      .cont (Anneal.MirLoops.countStateMem (match Nat.beq i n with | true => 3 | false => 2) 0 i emptyMemory) := rfl
  rw [hbeq] at hs1
  have hs2 : mirStep (Anneal.MirLoops.countToNBody n) (Anneal.MirLoops.countStateMem 2 0 i emptyMemory) =
      .cont (Anneal.MirLoops.countStateMem 2 1 (i + 1) emptyMemory) := by
    have hmod : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
    unfold mirStep stepMirFn
    dsimp [Anneal.MirLoops.countStateMem, emptyMemory]
    simp [Anneal.MirLoops.countToNBody, Anneal.MirLoops.mkMirBody,
      Anneal.MirLoops.constU32, Trusted.Sequence.get?, evalStmt, evalOperand,
      readProjectedValue, evalRvalue, evalConstValue, advanceStmt, Trusted.Sequence.set?,
      invalidateConflictingBorrows, hmod]
    rfl
  have hs3 : mirStep (Anneal.MirLoops.countToNBody n)
      (Anneal.MirLoops.countStateMem 2 1 (i + 1) emptyMemory) =
      .cont (Anneal.MirLoops.countStateMem 1 0 (i + 1) emptyMemory) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (Anneal.MirLoops.countToNBody n) = 7 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

/-- Loop-exit segment of the live `Anneal.MirLoops.countToNBody n` executed
through `runMirToBlock`: steps from `bb1` (`i = n`) through `bb3` to `.halted`. -/
theorem runMirToBlock_countToN_exit (n : Nat) :
    PureMirExec.runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      (Anneal.MirLoops.countStateMem 1 0 n emptyMemory) =
      .halted (.normal (.scalar ⟨n, 4⟩, emptyMemory)) := by
  have hs1 : mirStep (Anneal.MirLoops.countToNBody n) (Anneal.MirLoops.countStateMem 1 0 n emptyMemory) =
      .cont (Anneal.MirLoops.countStateMem (match Nat.beq n n with | true => 3 | false => 2) 0 n emptyMemory) := rfl
  rw [Nat.beq_refl] at hs1
  have hs2 : mirStep (Anneal.MirLoops.countToNBody n) (Anneal.MirLoops.countStateMem 3 0 n emptyMemory) =
      .cont (Anneal.MirLoops.countStateMemRet 3 1 n emptyMemory) := rfl
  have hs3 : mirStep (Anneal.MirLoops.countToNBody n)
      (Anneal.MirLoops.countStateMemRet 3 1 n emptyMemory) =
      .done (.normal (.scalar ⟨n, 4⟩, emptyMemory)) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (Anneal.MirLoops.countToNBody n) = 7 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

/-- **End-to-end live `CapturedMir` fuel-free loop verification**:
`Anneal.MirLoops.countToNBody n` converges for every symbolic `n < 2^32` via
`runMirToBlock` + `mirWpConverges_forRangeUp` with zero fuel numerals. -/
theorem live_countToN_mirWpConverges_all_n (n : Nat) (hn : n < 4294967296) :
    Anneal.MirFuelFree.MirWpConverges (Anneal.MirLoops.countToNBody n)
      (Anneal.MirLoops.countStateMem 0 0 0 emptyMemory)
      (fun out => out = .normal (.scalar ⟨n, 4⟩, emptyMemory)) :=
  mirWpConverges_forRangeUp_of_runMirToBlock
    (Anneal.MirLoops.countToNBody n) 1 0 n () (fun _ _ _ u => u)
    (fun i _ => Anneal.MirLoops.countStateMem 1 0 i emptyMemory)
    (Anneal.MirLoops.countStateMem 0 0 0 emptyMemory)
    (fun out => out = .normal (.scalar ⟨n, 4⟩, emptyMemory))
    (Nat.zero_le n)
    (runMirToBlock_countToN_entry n)
    (fun i _ hlt _ => runMirToBlock_countToN_iter n i hlt hn)
    ⟨.normal (.scalar ⟨n, 4⟩, emptyMemory), runMirToBlock_countToN_exit n, rfl⟩

/-- Call-free `MirNoCallWpConverges` verification of `Anneal.MirLoops.countToNBody n`
over every symbolic `n < 2^32`. -/
theorem live_countToN_mirNoCallWpConverges_all_n (n : Nat) (hn : n < 4294967296) :
    Anneal.MirFuelFree.MirNoCallWpConverges (Anneal.MirLoops.countToNBody n)
      (Anneal.MirLoops.countStateMem 0 0 0 emptyMemory)
      (fun out => out = .normal (.scalar ⟨n, 4⟩, emptyMemory)) :=
  mirNoCallWpConverges_forRangeUp_of_runMirToBlock
    (Anneal.MirLoops.countToNBody n) 1 0 n () (fun _ _ _ u => u)
    (fun i _ => Anneal.MirLoops.countStateMem 1 0 i emptyMemory)
    (Anneal.MirLoops.countStateMem 0 0 0 emptyMemory)
    (fun out => out = .normal (.scalar ⟨n, 4⟩, emptyMemory))
    (Nat.zero_le n)
    (runMirToBlock_countToN_entry n)
    (fun i _ hlt _ => runMirToBlock_countToN_iter n i hlt hn)
    ⟨.normal (.scalar ⟨n, 4⟩, emptyMemory), runMirToBlock_countToN_exit n, rfl⟩

theorem checkPureMir_countToNBody (n : Nat) :
    checkPureMir (Anneal.MirLoops.countToNBody n) = true := rfl

theorem inferMinFragment_countToNBody (n : Nat) :
    inferMinFragment (Anneal.MirLoops.countToNBody n) = .pureBoundedLoop := rfl

/-- Alias-erased `PureState` for `Anneal.MirLoops.countToNBody n` starting from
`initPureState` (where return slot `_0` is `.uninit` until exit block `bb3`). -/
def countToNPureState (bb stmt i : Nat) : PureState :=
  { bb := bb, stmtIdx := stmt, env := [.uninit, .init (.scalar ⟨i, 4⟩)] }

theorem runMirToBlock_countToN_entry_initPureState (n : Nat) (v₀ : Value) :
    PureMirExec.runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      ((initPureState (Anneal.MirLoops.countToNBody n) [v₀]).toMachineState emptyMemory) =
      .reached ((countToNPureState 1 0 0).toMachineState emptyMemory) := rfl

theorem runMirToBlock_countToN_iter_initPureState (n i : Nat) (hlt : i < n) (hn : n < 4294967296) :
    PureMirExec.runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      ((countToNPureState 1 0 i).toMachineState emptyMemory) =
      .reached ((countToNPureState 1 0 (i + 1)).toMachineState emptyMemory) := by
  have hbeq : Nat.beq i n = false := (Bool.not_eq_true _).mp (Nat.ne_of_lt hlt ∘ Nat.eq_of_beq_eq_true)
  have hs1 : mirStep (Anneal.MirLoops.countToNBody n) ((countToNPureState 1 0 i).toMachineState emptyMemory) =
      .cont ((countToNPureState (match Nat.beq i n with | true => 3 | false => 2) 0 i).toMachineState emptyMemory) := rfl
  rw [hbeq] at hs1
  have hs2 : mirStep (Anneal.MirLoops.countToNBody n) ((countToNPureState 2 0 i).toMachineState emptyMemory) =
      .cont ((countToNPureState 2 1 (i + 1)).toMachineState emptyMemory) := by
    have hmod : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
    unfold mirStep stepMirFn
    dsimp [countToNPureState, PureState.toMachineState, emptyMemory]
    simp [Anneal.MirLoops.countToNBody, Anneal.MirLoops.mkMirBody,
      Anneal.MirLoops.constU32, Trusted.Sequence.get?, evalStmt, evalOperand,
      readProjectedValue, evalRvalue, evalConstValue, advanceStmt, Trusted.Sequence.set?,
      invalidateConflictingBorrows, hmod]
    rfl
  have hs3 : mirStep (Anneal.MirLoops.countToNBody n)
      ((countToNPureState 2 1 (i + 1)).toMachineState emptyMemory) =
      .cont ((countToNPureState 1 0 (i + 1)).toMachineState emptyMemory) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (Anneal.MirLoops.countToNBody n) = 7 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

theorem runMirToBlock_countToN_exit_initPureState (n : Nat) :
    PureMirExec.runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      ((countToNPureState 1 0 n).toMachineState emptyMemory) =
      .halted (.normal (.scalar ⟨n, 4⟩, emptyMemory)) := by
  have hs1 : mirStep (Anneal.MirLoops.countToNBody n) ((countToNPureState 1 0 n).toMachineState emptyMemory) =
      .cont ((countToNPureState (match Nat.beq n n with | true => 3 | false => 2) 0 n).toMachineState emptyMemory) := rfl
  rw [Nat.beq_refl] at hs1
  have hs2 : mirStep (Anneal.MirLoops.countToNBody n) ((countToNPureState 3 0 n).toMachineState emptyMemory) =
      .cont { frame := { blockIdx := 3, stmtIdx := 1, locals := [.init (.scalar ⟨n, 4⟩), .init (.scalar ⟨n, 4⟩)] }, memory := emptyMemory } := rfl
  have hs3 : mirStep (Anneal.MirLoops.countToNBody n)
      { frame := { blockIdx := 3, stmtIdx := 1, locals := [.init (.scalar ⟨n, 4⟩), .init (.scalar ⟨n, 4⟩)] }, memory := emptyMemory } =
      .done (.normal (.scalar ⟨n, 4⟩, emptyMemory)) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (Anneal.MirLoops.countToNBody n) = 7 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

/-- Alias-erased `PureMirConverges` from `initPureState (countToNBody n) [v₀]`
for every symbolic `n < 2^32`. -/
theorem live_countToN_pureMirConverges_all_n (n : Nat) (hn : n < 4294967296) (v₀ : Value) :
    PureMirConverges (Anneal.MirLoops.countToNBody n)
      (initPureState (Anneal.MirLoops.countToNBody n) [v₀])
      (fun retVal => retVal = .scalar ⟨n, 4⟩) :=
  pureMirConverges_forRangeUp_of_runMirToBlock
    (Anneal.MirLoops.countToNBody n) 1 0 n () (fun _ _ _ u => u)
    (fun i _ => countToNPureState 1 0 i)
    (initPureState (Anneal.MirLoops.countToNBody n) [v₀])
    (fun retVal => retVal = .scalar ⟨n, 4⟩)
    (Nat.zero_le n)
    (runMirToBlock_countToN_entry_initPureState n v₀)
    (fun i _ hlt _ => runMirToBlock_countToN_iter_initPureState n i hlt hn)
    ⟨.scalar ⟨n, 4⟩, emptyMemory, runMirToBlock_countToN_exit_initPureState n, rfl⟩

/-- Stateless `VerificationResult` for `Anneal.MirLoops.countToNBody n` over
every symbolic `n < 2^32` with zero fuel numerals. -/
theorem live_countToN_verifyMir_all_n (n : Nat) (hn : n < 4294967296) :
    VerificationResult
      { body := Anneal.MirLoops.countToNBody n
        pre := fun args => ∃ v₀, args = [v₀]
        post := fun _ retVal => retVal = .scalar ⟨n, 4⟩
        callees := [] } :=
  verifyMirNoPanic_forRangeUp_of_runMirToBlock _
    (checkPureMir_countToNBody n) 1
    (fun _ => 0) (fun _ => n) (fun _ => ()) (fun _ _ _ _ u => u)
    (fun _ i _ => countToNPureState 1 0 i)
    (fun _ _ => Nat.zero_le n)
    (fun args ⟨v₀, hargs⟩ => by subst hargs; exact runMirToBlock_countToN_entry_initPureState n v₀)
    (fun _ _ i _ hlt _ => runMirToBlock_countToN_iter_initPureState n i hlt hn)
    (fun _ _ => ⟨.scalar ⟨n, 4⟩, emptyMemory, runMirToBlock_countToN_exit_initPureState n, rfl⟩)

/-- **End-to-end `StatefulVerificationResult` for live `Anneal.MirLoops.countToNBody n`**
over every symbolic `n < 2^32` and arbitrary root-active memory `mem`, with
zero fuel numerals and purely constructive axioms (`⊆ {propext, Quot.sound}`). -/
theorem live_countToN_statefulVerificationResult_all_n (n : Nat) (hn : n < 4294967296) :
    StatefulVerificationResult
      { body := Anneal.MirLoops.countToNBody n
        pre := fun args mem => (∃ v₀, args = [v₀]) ∧ RootActiveMemory mem
        post := fun _ mem retVal mem' =>
          mem' = mem ∧ retVal = .scalar ⟨n, 4⟩
        callees := [] } :=
  verifyStatefulMirNoPanic_forRangeUp_of_runMirToBlock _
    (checkPureMir_countToNBody n)
    (fun _ _ hp => hp.2) 1
    (fun _ _ => 0) (fun _ _ => n) (fun _ _ => ()) (fun _ _ _ _ _ u => u)
    (fun _ _ i _ => countToNPureState 1 0 i)
    (fun _ _ _ => Nat.zero_le n)
    (fun args _ ⟨⟨v₀, hargs⟩, _⟩ => by rw [hargs]; exact runMirToBlock_countToN_entry_initPureState n v₀)
    (fun _ _ _ i _ hlt _ => runMirToBlock_countToN_iter_initPureState n i hlt hn)
    (fun _ _ _ => ⟨.scalar ⟨n, 4⟩, emptyMemory, runMirToBlock_countToN_exit_initPureState n, rfl, rfl⟩)

/-- **End-to-end `TotalVerificationResult` for live `Anneal.MirLoops.countToNBody n`**
over every symbolic `n < 2^32` and arbitrary root-active memory `mem`, with
zero fuel numerals in the statement or proof. -/
theorem live_countToN_totalVerificationResult_all_n (n : Nat) (hn : n < 4294967296) :
    TotalVerificationResult
      { body := Anneal.MirLoops.countToNBody n
        pre := fun args mem => (∃ v₀, args = [v₀]) ∧ RootActiveMemory mem
        post := fun _ mem retVal mem' =>
          mem' = mem ∧ retVal = .scalar ⟨n, 4⟩
        callees := [] } :=
  verifyTotalMir_forRangeUp_of_runMirToBlock _
    (checkPureMir_countToNBody n)
    (fun _ _ hp => hp.2) 1
    (fun _ _ => 0) (fun _ _ => n) (fun _ _ => ()) (fun _ _ _ _ _ u => u)
    (fun _ _ i _ => countToNPureState 1 0 i)
    (fun _ _ _ => Nat.zero_le n)
    (fun args _ ⟨⟨v₀, hargs⟩, _⟩ => by rw [hargs]; exact runMirToBlock_countToN_entry_initPureState n v₀)
    (fun _ _ _ i _ hlt _ => runMirToBlock_countToN_iter_initPureState n i hlt hn)
    (fun _ _ _ => ⟨.scalar ⟨n, 4⟩, emptyMemory, runMirToBlock_countToN_exit_initPureState n, rfl, rfl⟩)

/-- **Concrete witness that live `Anneal.FunctionalTranslation.runMirToBlock` conflates
normal halting, faulting, and out-of-fuel**: on the live `Anneal.MirLoops.countToNBody n`,
stepping from the return block `bb3`, from an invalid block `bb99`, and from `bb0` with
insufficient fuel all evaluate to `none` in the live stepper, whereas `runUntilTarget`
distinguishes `.halted`, `.stuck`, and `.outOfFuel`. -/
theorem live_runMirToBlock_conflates_halt_stuck_outOfFuel (n : Nat) :
    let body := Anneal.MirLoops.countToNBody n
    let atHdr := fun (ms : MachineState) => ms.frame.blockIdx == 1 && ms.frame.stmtIdx == 0
    let sHalt := Anneal.MirLoops.countStateMem 3 0 n emptyMemory
    let sFault := Anneal.MirLoops.countStateMem 99 0 0 emptyMemory
    let sOOF := Anneal.MirLoops.countStateMem 0 0 0 emptyMemory
    runUntilTarget (mirStep body) atHdr 7 sHalt = .halted (.normal (.scalar ⟨n, 4⟩, emptyMemory)) ∧
      Anneal.FunctionalTranslation.runMirToBlock 8 body 1 sHalt = none ∧
      runUntilTarget (mirStep body) atHdr 7 sFault = .stuck ∧
      Anneal.FunctionalTranslation.runMirToBlock 8 body 1 sFault = none ∧
      runUntilTarget (mirStep body) atHdr 1 sOOF = .outOfFuel ∧
      Anneal.FunctionalTranslation.runMirToBlock 2 body 1 sOOF = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### No overshoot and completeness of live `runMirToBlock` -/

/-- **No overshoot on live MIR**: a `.reached s_hit` outcome of `runMirToBlock`
is the *first* re-entry into `(target, 0)` after the mandatory step, within the
CFG-derived ceiling `mirSegmentBound body` (unique by `FirstHitIn.unique`). -/
theorem firstHitIn_of_runMirToBlock_reached {body : CapturedMir} {target : BasicBlockIdx}
    {s s_hit : MachineState}
    (h : PureMirExec.runMirToBlock body target s = .reached s_hit) :
    ∃ n, n ≤ mirSegmentBound body ∧
      FirstHitIn (mirStep body)
        (fun ms => ms.frame.blockIdx == target && ms.frame.stmtIdx == 0) n s s_hit :=
  firstHitIn_of_runToTarget_reached h

/-- **Completeness on live MIR**: every first re-entry into `(target, 0)` whose
silent prefix fits the CFG-derived ceiling is found by `runMirToBlock`. -/
theorem runMirToBlock_of_firstHitIn {body : CapturedMir} {target : BasicBlockIdx}
    {n : Nat} {s s_hit : MachineState}
    (h : FirstHitIn (mirStep body)
      (fun ms => ms.frame.blockIdx == target && ms.frame.stmtIdx == 0) n s s_hit)
    (hle : n ≤ mirSegmentBound body) :
    PureMirExec.runMirToBlock body target s = .reached s_hit :=
  runToTarget_of_firstHitIn h hle

/-! ### `MirFragment`-keyed loop-lifting entrypoints (`inferMinFragment ≤ .pureBoundedLoop`)

These gates take the live minimal-fragment classifier verdict
`inferMinFragment c.body ≤ .pureBoundedLoop` (plus the auto-discharged
`hasNoPtrRelationalAssign`) instead of a raw `checkPureMir` certificate, so the
`.pureBoundedLoop` level of the `MirFragment` lattice routes directly to
header-targeted `runMirToBlock` + `forRangeUp` loop lifting. -/

/-- **`MirFragment`-keyed stateless loop gate** (`VerificationResult`). -/
theorem verifyMirNoPanic_forRangeUp_of_inferMinFragment_le_pureBoundedLoop {α : Type}
    (c : Claim)
    (h_frag : inferMinFragment c.body ≤ .pureBoundedLoop)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Nat)
    (init : List Value → α)
    (f : (args : List Value) → (i : Nat) → lo args ≤ i → i < hi args → α → α)
    (stateAt : List Value → Nat → α → PureState)
    (hle : ∀ args, c.pre args → lo args ≤ hi args)
    (hentry : ∀ args, c.pre args →
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached ((stateAt args (lo args) (init args)).toMachineState emptyMemory))
    (hiter : ∀ args, c.pre args → ∀ i (hlo : lo args ≤ i) (hlt : i < hi args) a,
      PureMirExec.runMirToBlock c.body headerBb ((stateAt args i a).toMachineState emptyMemory) =
        .reached ((stateAt args (i + 1) (f args i hlo hlt a)).toMachineState emptyMemory))
    (hexit : ∀ args, c.pre args → ∃ retVal mem',
      PureMirExec.runMirToBlock c.body headerBb
        ((stateAt args (hi args)
          (Anneal.MirLoops.forRangeUp (lo args) (hi args) (init args) (f args))).toMachineState emptyMemory) =
        .halted (.normal (retVal, mem')) ∧ c.post args retVal)
    (h_no_ptr_rel : hasNoPtrRelationalAssign c.body = true := by decide) :
    VerificationResult c :=
  verifyMirNoPanic_forRangeUp_of_runMirToBlock c
    (checkPureMir_of_inferMinFragment_le_pureBoundedLoop c.body h_frag h_no_ptr_rel)
    headerBb lo hi init f stateAt hle hentry hiter hexit

/-- **`MirFragment`-keyed stateful loop gate** (`StatefulVerificationResult`). -/
theorem verifyStatefulMirNoPanic_forRangeUp_of_inferMinFragment_le_pureBoundedLoop {α : Type}
    (c : StatefulClaim)
    (h_frag : inferMinFragment c.body ≤ .pureBoundedLoop)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Memory → Nat)
    (init : List Value → Memory → α)
    (f : (args : List Value) → (mem : Memory) → (i : Nat) → lo args mem ≤ i → i < hi args mem → α → α)
    (stateAt : List Value → Memory → Nat → α → PureState)
    (hle : ∀ args mem, c.pre args mem → lo args mem ≤ hi args mem)
    (hentry : ∀ args mem, c.pre args mem →
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached ((stateAt args mem (lo args mem) (init args mem)).toMachineState emptyMemory))
    (hiter : ∀ args mem, c.pre args mem → ∀ i (hlo : lo args mem ≤ i) (hlt : i < hi args mem) a,
      PureMirExec.runMirToBlock c.body headerBb ((stateAt args mem i a).toMachineState emptyMemory) =
        .reached ((stateAt args mem (i + 1) (f args mem i hlo hlt a)).toMachineState emptyMemory))
    (hexit : ∀ args mem, c.pre args mem → ∃ retVal mem_e,
      PureMirExec.runMirToBlock c.body headerBb
        ((stateAt args mem (hi args mem)
          (Anneal.MirLoops.forRangeUp (lo args mem) (hi args mem) (init args mem) (f args mem))).toMachineState emptyMemory) =
        .halted (.normal (retVal, mem_e)) ∧
        c.post args mem retVal
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees).memory)
    (h_no_ptr_rel : hasNoPtrRelationalAssign c.body = true := by decide) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_forRangeUp_of_runMirToBlock c
    (checkPureMir_of_inferMinFragment_le_pureBoundedLoop c.body h_frag h_no_ptr_rel)
    h_root headerBb lo hi init f stateAt hle hentry hiter hexit

/-- **`MirFragment`-keyed total-correctness loop gate** (`TotalVerificationResult`). -/
theorem verifyTotalMir_forRangeUp_of_inferMinFragment_le_pureBoundedLoop {α : Type}
    (c : TotalClaim)
    (h_frag : inferMinFragment c.body ≤ .pureBoundedLoop)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (headerBb : BasicBlockIdx)
    (lo hi : List Value → Memory → Nat)
    (init : List Value → Memory → α)
    (f : (args : List Value) → (mem : Memory) → (i : Nat) → lo args mem ≤ i → i < hi args mem → α → α)
    (stateAt : List Value → Memory → Nat → α → PureState)
    (hle : ∀ args mem, c.pre args mem → lo args mem ≤ hi args mem)
    (hentry : ∀ args mem, c.pre args mem →
      PureMirExec.runMirToBlock c.body headerBb ((initPureState c.body args).toMachineState emptyMemory) =
        .reached ((stateAt args mem (lo args mem) (init args mem)).toMachineState emptyMemory))
    (hiter : ∀ args mem, c.pre args mem → ∀ i (hlo : lo args mem ≤ i) (hlt : i < hi args mem) a,
      PureMirExec.runMirToBlock c.body headerBb ((stateAt args mem i a).toMachineState emptyMemory) =
        .reached ((stateAt args mem (i + 1) (f args mem i hlo hlt a)).toMachineState emptyMemory))
    (hexit : ∀ args mem, c.pre args mem → ∃ retVal mem_e,
      PureMirExec.runMirToBlock c.body headerBb
        ((stateAt args mem (hi args mem)
          (Anneal.MirLoops.forRangeUp (lo args mem) (hi args mem) (init args mem) (f args mem))).toMachineState emptyMemory) =
        .halted (.normal (retVal, mem_e)) ∧
        c.post args mem retVal
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees).memory)
    (h_no_ptr_rel : hasNoPtrRelationalAssign c.body = true := by decide) :
    TotalVerificationResult c :=
  verifyTotalMir_forRangeUp_of_runMirToBlock c
    (checkPureMir_of_inferMinFragment_le_pureBoundedLoop c.body h_frag h_no_ptr_rel)
    h_root headerBb lo hi init f stateAt hle hentry hiter hexit

/-- The live classifier places every `Anneal.MirLoops.countToNBody n` at or below
`.pureBoundedLoop`. -/
theorem inferMinFragment_countToNBody_le_pureBoundedLoop (n : Nat) :
    inferMinFragment (Anneal.MirLoops.countToNBody n) ≤ .pureBoundedLoop := by
  rw [inferMinFragment_countToNBody]
  exact Nat.le_refl _

/-- Stateless `VerificationResult` for `Anneal.MirLoops.countToNBody n` routed by
the live `MirFragment` classifier (`.pureBoundedLoop`) with zero fuel numerals. -/
theorem live_countToN_verifyMir_all_n_of_fragment (n : Nat) (hn : n < 4294967296) :
    VerificationResult
      { body := Anneal.MirLoops.countToNBody n
        pre := fun args => ∃ v₀, args = [v₀]
        post := fun _ retVal => retVal = .scalar ⟨n, 4⟩
        callees := [] } :=
  verifyMirNoPanic_forRangeUp_of_inferMinFragment_le_pureBoundedLoop _
    (inferMinFragment_countToNBody_le_pureBoundedLoop n) 1
    (fun _ => 0) (fun _ => n) (fun _ => ()) (fun _ _ _ _ u => u)
    (fun _ i _ => countToNPureState 1 0 i)
    (fun _ _ => Nat.zero_le n)
    (fun args ⟨v₀, hargs⟩ => by subst hargs; exact runMirToBlock_countToN_entry_initPureState n v₀)
    (fun _ _ i _ hlt _ => runMirToBlock_countToN_iter_initPureState n i hlt hn)
    (fun _ _ => ⟨.scalar ⟨n, 4⟩, emptyMemory, runMirToBlock_countToN_exit_initPureState n, rfl⟩)
    rfl

/-- **`End-to-end `StatefulVerificationResult` for live `Anneal.MirLoops.countToNBody n`
routed by the live `MirFragment` classifier** (`.pureBoundedLoop`), over every
symbolic `n < 2^32` and root-active memory, with zero fuel numerals and purely
constructive axioms (`⊆ {propext, Quot.sound}`). -/
theorem live_countToN_statefulVerificationResult_all_n_of_fragment (n : Nat) (hn : n < 4294967296) :
    StatefulVerificationResult
      { body := Anneal.MirLoops.countToNBody n
        pre := fun args mem => (∃ v₀, args = [v₀]) ∧ RootActiveMemory mem
        post := fun _ mem retVal mem' =>
          mem' = mem ∧ retVal = .scalar ⟨n, 4⟩
        callees := [] } :=
  verifyStatefulMirNoPanic_forRangeUp_of_inferMinFragment_le_pureBoundedLoop _
    (inferMinFragment_countToNBody_le_pureBoundedLoop n)
    (fun _ _ hp => hp.2) 1
    (fun _ _ => 0) (fun _ _ => n) (fun _ _ => ()) (fun _ _ _ _ _ u => u)
    (fun _ _ i _ => countToNPureState 1 0 i)
    (fun _ _ _ => Nat.zero_le n)
    (fun args _ ⟨⟨v₀, hargs⟩, _⟩ => by rw [hargs]; exact runMirToBlock_countToN_entry_initPureState n v₀)
    (fun _ _ _ i _ hlt _ => runMirToBlock_countToN_iter_initPureState n i hlt hn)
    (fun _ _ _ => ⟨.scalar ⟨n, 4⟩, emptyMemory, runMirToBlock_countToN_exit_initPureState n, rfl, rfl⟩)
    rfl

/-- **End-to-end `TotalVerificationResult` for live `Anneal.MirLoops.countToNBody n`
routed by the live `MirFragment` classifier** (`.pureBoundedLoop`), over every
symbolic `n < 2^32` and root-active memory, with zero fuel numerals. -/
theorem live_countToN_totalVerificationResult_all_n_of_fragment (n : Nat) (hn : n < 4294967296) :
    TotalVerificationResult
      { body := Anneal.MirLoops.countToNBody n
        pre := fun args mem => (∃ v₀, args = [v₀]) ∧ RootActiveMemory mem
        post := fun _ mem retVal mem' =>
          mem' = mem ∧ retVal = .scalar ⟨n, 4⟩
        callees := [] } :=
  verifyTotalMir_forRangeUp_of_inferMinFragment_le_pureBoundedLoop _
    (inferMinFragment_countToNBody_le_pureBoundedLoop n)
    (fun _ _ hp => hp.2) 1
    (fun _ _ => 0) (fun _ _ => n) (fun _ _ => ()) (fun _ _ _ _ _ u => u)
    (fun _ _ i _ => countToNPureState 1 0 i)
    (fun _ _ _ => Nat.zero_le n)
    (fun args _ ⟨⟨v₀, hargs⟩, _⟩ => by rw [hargs]; exact runMirToBlock_countToN_entry_initPureState n v₀)
    (fun _ _ _ i _ hlt _ => runMirToBlock_countToN_iter_initPureState n i hlt hn)
    (fun _ _ _ => ⟨.scalar ⟨n, 4⟩, emptyMemory, runMirToBlock_countToN_exit_initPureState n, rfl, rfl⟩)
    rfl

/-- `countToNBody n` frame whose return slot `_0` is an arbitrary `LocalSlot`. -/
def countToNSymState (s₀ : LocalSlot) (bb stmt i : Nat) : PureState :=
  { bb := bb, stmtIdx := stmt, env := [s₀, .init (.scalar ⟨i, 4⟩)] }

/-- One live loop iteration of `countToNBody n` with a symbolic, untouched `_0` slot. -/
theorem runMirToBlock_countToN_iter_sym (s₀ : LocalSlot) (n i : Nat) (hlt : i < n)
    (hn : n < 4294967296) :
    PureMirExec.runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      ((countToNSymState s₀ 1 0 i).toMachineState emptyMemory) =
      .reached ((countToNSymState s₀ 1 0 (i + 1)).toMachineState emptyMemory) := by
  have hbeq : Nat.beq i n = false := (Bool.not_eq_true _).mp (Nat.ne_of_lt hlt ∘ Nat.eq_of_beq_eq_true)
  have hs1 : mirStep (Anneal.MirLoops.countToNBody n) ((countToNSymState s₀ 1 0 i).toMachineState emptyMemory) =
      .cont ((countToNSymState s₀ (match Nat.beq i n with | true => 3 | false => 2) 0 i).toMachineState emptyMemory) := rfl
  rw [hbeq] at hs1
  have hs2 : mirStep (Anneal.MirLoops.countToNBody n) ((countToNSymState s₀ 2 0 i).toMachineState emptyMemory) =
      .cont ((countToNSymState s₀ 2 1 (i + 1)).toMachineState emptyMemory) := by
    have hmod : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
    unfold mirStep stepMirFn
    dsimp [countToNSymState, PureState.toMachineState, emptyMemory]
    simp [Anneal.MirLoops.countToNBody, Anneal.MirLoops.mkMirBody,
      Anneal.MirLoops.constU32, Trusted.Sequence.get?, evalStmt, evalOperand,
      readProjectedValue, evalRvalue, evalConstValue, advanceStmt, Trusted.Sequence.set?,
      invalidateConflictingBorrows, hmod]
    rfl
  have hs3 : mirStep (Anneal.MirLoops.countToNBody n)
      ((countToNSymState s₀ 2 1 (i + 1)).toMachineState emptyMemory) =
      .cont ((countToNSymState s₀ 1 0 (i + 1)).toMachineState emptyMemory) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (Anneal.MirLoops.countToNBody n) = 7 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

/-- Entry segment from an arbitrary non-dead frame `[s₀, s₁]`. -/
theorem countToN_sym_entry (s₀ s₁ : LocalSlot) (h₁ : s₁ ≠ .dead) (n : Nat) :
    PureMirExec.runMirToBlock (Anneal.MirLoops.countToNBody n) 1
      (({ bb := 0, stmtIdx := 0, env := [s₀, s₁] } : PureState).toMachineState emptyMemory) =
      .reached ((countToNSymState s₀ 1 0 0).toMachineState emptyMemory) := by
  cases s₁ with
  | dead => exact absurd rfl h₁
  | uninit => rfl
  | init v => rfl

/-- Exit segment from a header frame with a symbolic non-dead `_0` slot. -/
theorem countToN_sym_exit (s₀ : LocalSlot) (h₀ : s₀ ≠ .dead) (n : Nat) :
    ∃ retVal mem',
      PureMirExec.runMirToBlock (Anneal.MirLoops.countToNBody n) 1
        ((countToNSymState s₀ 1 0 n).toMachineState emptyMemory) =
        .halted (.normal (retVal, mem')) ∧ retVal = .scalar ⟨n, 4⟩ := by
  have hs1 : mirStep (Anneal.MirLoops.countToNBody n) ((countToNSymState s₀ 1 0 n).toMachineState emptyMemory) =
      .cont ((countToNSymState s₀ (match Nat.beq n n with | true => 3 | false => 2) 0 n).toMachineState emptyMemory) := rfl
  rw [Nat.beq_refl] at hs1
  have hs2 : mirStep (Anneal.MirLoops.countToNBody n) ((countToNSymState s₀ 3 0 n).toMachineState emptyMemory) =
      .cont { frame := { blockIdx := 3, stmtIdx := 1,
                         locals := [.init (.scalar ⟨n, 4⟩), .init (.scalar ⟨n, 4⟩)] },
              memory := emptyMemory } := by
    cases s₀ with
    | dead => exact absurd rfl h₀
    | uninit => rfl
    | init v => rfl
  have hs3 : mirStep (Anneal.MirLoops.countToNBody n)
      { frame := { blockIdx := 3, stmtIdx := 1,
                   locals := [.init (.scalar ⟨n, 4⟩), .init (.scalar ⟨n, 4⟩)] },
        memory := emptyMemory } =
      .done (.normal (.scalar ⟨n, 4⟩, emptyMemory)) := rfl
  refine ⟨.scalar ⟨n, 4⟩, emptyMemory, ?_, rfl⟩
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (Anneal.MirLoops.countToNBody n) = 7 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

/-- **Invariant-based loop lifting over symbolic `LocalSlot` frames**: live
`Anneal.MirLoops.countToNBody n` converges to `n` from *every* non-dead initial frame
`[s₀, s₁]`, via `pureMirConverges_forRangeUp_of_runMirToBlock_inv` with a header
invariant that is existential over the untouched `_0` slot (live `runMirToBlock`
iterations carry the symbolic slot without forcing its constructor). -/
theorem live_countToN_pureMirConverges_any_frame (n : Nat) (hn : n < 4294967296)
    (s₀ s₁ : LocalSlot) (h₀ : s₀ ≠ .dead) (h₁ : s₁ ≠ .dead) :
    PureMirConverges (Anneal.MirLoops.countToNBody n)
      { bb := 0, stmtIdx := 0, env := [s₀, s₁] }
      (fun retVal => retVal = .scalar ⟨n, 4⟩) :=
  pureMirConverges_forRangeUp_of_runMirToBlock_inv
    (Anneal.MirLoops.countToNBody n) 1 0 n () (fun _ _ _ u => u)
    (fun i _ ps => ∃ t₀ : LocalSlot, t₀ ≠ .dead ∧ ps = countToNSymState t₀ 1 0 i)
    { bb := 0, stmtIdx := 0, env := [s₀, s₁] } _ (Nat.zero_le n)
    ⟨_, countToN_sym_entry s₀ s₁ h₁ n, s₀, h₀, rfl⟩
    (fun i _ hlt _ ps ⟨t₀, ht₀, hps⟩ => by
      subst hps
      exact ⟨_, runMirToBlock_countToN_iter_sym t₀ n i hlt hn, t₀, ht₀, rfl⟩)
    (fun ps ⟨t₀, ht₀, hps⟩ => by
      subst hps
      exact countToN_sym_exit t₀ ht₀ n)

/-- Empty-range identity for `MirLiftCore.forRangeUp` (`hi ≤ lo`). -/
protected theorem forRangeUp_eq_init_of_ge {α : Type} (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α) (hge : hi ≤ lo) :
    MirLiftCore.forRangeUp lo hi init f = init :=
  PureMirExec.forRangeUp_eq_init_of_ge lo hi init f hge

/--
Loop-carried staging-temporary MIR body (`countToNWithTempBody n`, 3 locals:
`_0` return, `_1` counter `i`, `_2` loop-body staging temporary `next_i`):
- `bb0`: `StorageLive(_2); _1 = const 0_u32; goto -> bb1`
  (reaches `bb1` at `i = 0` with `_2 = .uninit`)
- `bb1` (header): `switchInt(Copy(_1)) [n => bb3, otherwise => bb2]`
- `bb2` (body): `_2 = Add(Copy(_1), const 1_u32); _1 = Copy(_2); goto -> bb1`
  (re-enters `bb1` at `i + 1` with `_2 = .init (.scalar ⟨i + 1, 4⟩)`)
- `bb3` (exit): `StorageDead(_2); _0 = Copy(_1); return_`

Because `_2` is `.uninit` upon initial entry to `bb1` (`i = 0`) and
`.init (.scalar ⟨i, 4⟩)` upon every subsequent re-entry (`i > 0`), an exact
header state would need a case split on `i = 0` inside `stateAt`; the relational
header invariant `∃ s₂ : LocalSlot, s₂ ≠ .dead ∧ ...` instead discharges entry,
iteration, and exit uniformly.
-/
def countToNWithTempBody (n : Nat) : CapturedMir :=
  Anneal.MirLoops.mkMirBody "Anneal::MirLiftCore::count_to_n_with_temp" 1
    [ { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "i" }
    , { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "next_i" } ]
    [ -- bb0: StorageLive(_2); _1 = 0; goto bb1
      { statements :=
          [ { kind := .storageLive 2, span := "t0" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.use (Anneal.MirLoops.constU32 0)),
              span := "t1" } ]
        terminator := { kind := .goto 1, span := "t2" }
        isCleanup := false }
    , -- bb1: switchInt(Copy(_1)) [n => bb3, otherwise => bb2]
      { statements := []
        terminator :=
          { kind := .switchInt (.copy { local_ := 1, projection := [] })
              { branches := [(n, 3)], otherwise := 2 }
            span := "t3" }
        isCleanup := false }
    , -- bb2: _2 = Add(Copy(_1), 1); _1 = Copy(_2); goto bb1
      { statements :=
          [ { kind := .assign { local_ := 2, projection := [] }
                (.binaryOp .add (.copy { local_ := 1, projection := [] })
                  (Anneal.MirLoops.constU32 1)),
              span := "t4" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.use (.copy { local_ := 2, projection := [] })),
              span := "t5" } ]
        terminator := { kind := .goto 1, span := "t6" }
        isCleanup := false }
    , -- bb3: StorageDead(_2); _0 = Copy(_1); return
      { statements :=
          [ { kind := .storageDead 2, span := "t7" }
          , { kind := .assign { local_ := 0, projection := [] }
                (.use (.copy { local_ := 1, projection := [] })),
              span := "t8" } ]
        terminator := { kind := .return_, span := "t9" }
        isCleanup := false } ]

theorem checkPureMir_countToNWithTempBody (n : Nat) :
    checkPureMir (countToNWithTempBody n) = true := rfl

theorem inferMinFragment_countToNWithTempBody (n : Nat) :
    inferMinFragment (countToNWithTempBody n) = .pureBoundedLoop := rfl

theorem inferMinFragment_countToNWithTempBody_le_pureBoundedLoop (n : Nat) :
    inferMinFragment (countToNWithTempBody n) ≤ .pureBoundedLoop := by
  rw [inferMinFragment_countToNWithTempBody]
  exact Nat.le_refl _

/-- Frame of `countToNWithTempBody n` with counter `i` and staging slot `s₂`. -/
def countToNWithTempState (bb stmt i : Nat) (s₂ : LocalSlot) : PureState :=
  { bb := bb, stmtIdx := stmt, env := [.uninit, .init (.scalar ⟨i, 4⟩), s₂] }

theorem runMirToBlock_countToNWithTemp_entry (n : Nat) (v₀ : Value) :
    PureMirExec.runMirToBlock (countToNWithTempBody n) 1
      ((initPureState (countToNWithTempBody n) [v₀]).toMachineState emptyMemory) =
      .reached ((countToNWithTempState 1 0 0 .uninit).toMachineState emptyMemory) := rfl

theorem runMirToBlock_countToNWithTemp_iter (n i : Nat) (s₂ : LocalSlot)
    (hs₂ : s₂ ≠ .dead) (hlt : i < n) (hn : n < 4294967296) :
    PureMirExec.runMirToBlock (countToNWithTempBody n) 1
      ((countToNWithTempState 1 0 i s₂).toMachineState emptyMemory) =
      .reached ((countToNWithTempState 1 0 (i + 1) (.init (.scalar ⟨i + 1, 4⟩))).toMachineState emptyMemory) := by
  have hbeq : Nat.beq i n = false := (Bool.not_eq_true _).mp (Nat.ne_of_lt hlt ∘ Nat.eq_of_beq_eq_true)
  have hs1 : mirStep (countToNWithTempBody n) ((countToNWithTempState 1 0 i s₂).toMachineState emptyMemory) =
      .cont ((countToNWithTempState (match Nat.beq i n with | true => 3 | false => 2) 0 i s₂).toMachineState emptyMemory) := rfl
  rw [hbeq] at hs1
  have hs2 : mirStep (countToNWithTempBody n) ((countToNWithTempState 2 0 i s₂).toMachineState emptyMemory) =
      .cont ((countToNWithTempState 2 1 i (.init (.scalar ⟨i + 1, 4⟩))).toMachineState emptyMemory) := by
    have hmod : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
    cases s₂ with
    | dead => exact absurd rfl hs₂
    | uninit | init _ =>
      unfold mirStep stepMirFn
      dsimp [countToNWithTempState, PureState.toMachineState, emptyMemory]
      simp [countToNWithTempBody, Anneal.MirLoops.mkMirBody,
        Anneal.MirLoops.constU32,
        Trusted.Sequence.get?, evalStmt, evalOperand,
        readProjectedValue, evalRvalue, evalConstValue, advanceStmt, Trusted.Sequence.set?,
        invalidateConflictingBorrows, hmod]
      rfl
  have hs3 : mirStep (countToNWithTempBody n)
      ((countToNWithTempState 2 1 i (.init (.scalar ⟨i + 1, 4⟩))).toMachineState emptyMemory) =
      .cont ((countToNWithTempState 2 2 (i + 1) (.init (.scalar ⟨i + 1, 4⟩))).toMachineState emptyMemory) := rfl
  have hs4 : mirStep (countToNWithTempBody n)
      ((countToNWithTempState 2 2 (i + 1) (.init (.scalar ⟨i + 1, 4⟩))).toMachineState emptyMemory) =
      .cont ((countToNWithTempState 1 0 (i + 1) (.init (.scalar ⟨i + 1, 4⟩))).toMachineState emptyMemory) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (countToNWithTempBody n) = 10 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3, hs4]
  rfl

theorem runMirToBlock_countToNWithTemp_exit (n : Nat) (s₂ : LocalSlot) :
    PureMirExec.runMirToBlock (countToNWithTempBody n) 1
      ((countToNWithTempState 1 0 n s₂).toMachineState emptyMemory) =
      .halted (.normal (.scalar ⟨n, 4⟩, emptyMemory)) := by
  have hs1 : mirStep (countToNWithTempBody n) ((countToNWithTempState 1 0 n s₂).toMachineState emptyMemory) =
      .cont ((countToNWithTempState (match Nat.beq n n with | true => 3 | false => 2) 0 n s₂).toMachineState emptyMemory) := rfl
  rw [Nat.beq_refl] at hs1
  have hs2 : mirStep (countToNWithTempBody n) ((countToNWithTempState 3 0 n s₂).toMachineState emptyMemory) =
      .cont ((countToNWithTempState 3 1 n .dead).toMachineState emptyMemory) := rfl
  have hs3 : mirStep (countToNWithTempBody n) ((countToNWithTempState 3 1 n .dead).toMachineState emptyMemory) =
      .cont { frame := { blockIdx := 3, stmtIdx := 2,
                         locals := [.init (.scalar ⟨n, 4⟩), .init (.scalar ⟨n, 4⟩), .dead] },
              memory := emptyMemory } := rfl
  have hs4 : mirStep (countToNWithTempBody n)
      { frame := { blockIdx := 3, stmtIdx := 2,
                   locals := [.init (.scalar ⟨n, 4⟩), .init (.scalar ⟨n, 4⟩), .dead] },
        memory := emptyMemory } =
      .done (.normal (.scalar ⟨n, 4⟩, emptyMemory)) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (countToNWithTempBody n) = 10 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3, hs4]
  rfl

/-- **End-to-end `VerificationResult` for `countToNWithTempBody n` via the
`MirFragment`-routed invariant gate**: at `i = 0` the staging temporary `_2` is
`.uninit`, while at `i > 0` it holds `.init (.scalar ⟨i, 4⟩)`; the relational
header invariant `∃ s₂ ≠ .dead, ps = countToNWithTempState 1 0 i s₂` discharges
the loop uniformly across all `n < 2^32`. -/
theorem verify_countToNWithTemp_all_n (n : Nat) (hn : n < 4294967296) :
    VerificationResult
      { body := countToNWithTempBody n
        pre := fun args => ∃ v₀, args = [v₀]
        post := fun _ retVal => retVal = .scalar ⟨n, 4⟩
        callees := [] } :=
  verifyMirNoPanic_forRangeUp_of_inferMinFragment_le_pureBoundedLoop_inv _
    (inferMinFragment_countToNWithTempBody_le_pureBoundedLoop n) 1
    (fun _ => 0) (fun _ => n) (fun _ => ()) (fun _ _ _ _ u => u)
    (fun _ i _ ps => ∃ s₂ : LocalSlot, s₂ ≠ .dead ∧ ps = countToNWithTempState 1 0 i s₂)
    (fun _ _ => Nat.zero_le n)
    (fun args ⟨v₀, hargs⟩ => by
      subst hargs
      exact ⟨_, runMirToBlock_countToNWithTemp_entry n v₀, .uninit, ⟨(by intro h; nomatch h), rfl⟩⟩)
    (fun _ _ i _ hlt _ ps ⟨s₂, hs₂, hps⟩ => by
      subst hps
      exact ⟨_, runMirToBlock_countToNWithTemp_iter n i s₂ hs₂ hlt hn,
        .init (.scalar ⟨i + 1, 4⟩), ⟨(by intro h; nomatch h), rfl⟩⟩)
    (fun _ _ ps ⟨s₂, _, hps⟩ => by
      subst hps
      exact ⟨.scalar ⟨n, 4⟩, emptyMemory, runMirToBlock_countToNWithTemp_exit n s₂, rfl⟩)
    rfl

/-- **Constructive `StatefulVerificationResult` for `countToNWithTempBody n`**
(`⊆ {propext, Quot.sound}`) routed by `inferMinFragment ≤ .pureBoundedLoop`
and the relational header invariant over the loop-mutated temporary `_2`. -/
theorem verifyStateful_countToNWithTemp_all_n (n : Nat) (hn : n < 4294967296) :
    StatefulVerificationResult
      { body := countToNWithTempBody n
        pre := fun args mem => (∃ v₀, args = [v₀]) ∧ RootActiveMemory mem
        post := fun _ mem retVal mem' =>
          mem' = mem ∧ retVal = .scalar ⟨n, 4⟩
        callees := [] } :=
  verifyStatefulMirNoPanic_forRangeUp_of_inferMinFragment_le_pureBoundedLoop_inv _
    (inferMinFragment_countToNWithTempBody_le_pureBoundedLoop n)
    (fun _ _ hp => hp.2) 1
    (fun _ _ => 0) (fun _ _ => n) (fun _ _ => ()) (fun _ _ _ _ _ u => u)
    (fun _ _ i _ ps => ∃ s₂ : LocalSlot, s₂ ≠ .dead ∧ ps = countToNWithTempState 1 0 i s₂)
    (fun _ _ _ => Nat.zero_le n)
    (fun args _ ⟨⟨v₀, hargs⟩, _⟩ => by
      rw [hargs]
      exact ⟨_, runMirToBlock_countToNWithTemp_entry n v₀, .uninit, ⟨(by intro h; nomatch h), rfl⟩⟩)
    (fun _ _ _ i _ hlt _ ps ⟨s₂, hs₂, hps⟩ => by
      subst hps
      exact ⟨_, runMirToBlock_countToNWithTemp_iter n i s₂ hs₂ hlt hn,
        .init (.scalar ⟨i + 1, 4⟩), ⟨(by intro h; nomatch h), rfl⟩⟩)
    (fun _ _ _ ps ⟨s₂, _, hps⟩ => by
      subst hps
      exact ⟨.scalar ⟨n, 4⟩, emptyMemory, runMirToBlock_countToNWithTemp_exit n s₂, rfl, rfl⟩)
    rfl

/--
Live 2D nested-loop `CapturedMir` body (`nestedCountToNMBody n m`, 3 locals:
`_0` accumulator/return, `_1` outer counter `i`, `_2` inner counter `j`):
- `bb0`: `StorageLive(_2); _0 = const 0_u32; _1 = const 0_u32; goto -> bb1`
- `bb1` (outer header): `switchInt(Copy(_1)) [n => bb6, otherwise => bb2]`
- `bb2` (inner init): `_2 = const 0_u32; goto -> bb3`
- `bb3` (inner header): `switchInt(Copy(_2)) [m => bb5, otherwise => bb4]`
- `bb4` (inner body): `_0 = Add(Copy(_0), const 1_u32); _2 = Add(Copy(_2), const 1_u32); goto -> bb3`
- `bb5` (outer latch): `_1 = Add(Copy(_1), const 1_u32); goto -> bb1`
- `bb6` (outer exit): `StorageDead(_2); return_`
-/
def nestedCountToNMBody (n m : Nat) : CapturedMir :=
  Anneal.MirLoops.mkMirBody "Anneal::MirLiftCore::nested_count_to_n_m" 1
    [ { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "i" }
    , { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "j" } ]
    [ -- bb0: StorageLive(_2); _0 = 0; _1 = 0; goto bb1
      { statements :=
          [ { kind := .storageLive 2, span := "n0" }
          , { kind := .assign { local_ := 0, projection := [] }
                (.use (Anneal.MirLoops.constU32 0)),
              span := "n1" }
          , { kind := .assign { local_ := 1, projection := [] }
                (.use (Anneal.MirLoops.constU32 0)),
              span := "n2" } ]
        terminator := { kind := .goto 1, span := "n3" }
        isCleanup := false }
    , -- bb1 (outer header): switchInt(Copy(_1)) [n => bb6, otherwise => bb2]
      { statements := []
        terminator :=
          { kind := .switchInt (.copy { local_ := 1, projection := [] })
              { branches := [(n, 6)], otherwise := 2 }
            span := "n4" }
        isCleanup := false }
    , -- bb2 (inner init): _2 = 0; goto bb3
      { statements :=
          [ { kind := .assign { local_ := 2, projection := [] }
                (.use (Anneal.MirLoops.constU32 0)),
              span := "n5" } ]
        terminator := { kind := .goto 3, span := "n6" }
        isCleanup := false }
    , -- bb3 (inner header): switchInt(Copy(_2)) [m => bb5, otherwise => bb4]
      { statements := []
        terminator :=
          { kind := .switchInt (.copy { local_ := 2, projection := [] })
              { branches := [(m, 5)], otherwise := 4 }
            span := "n7" }
        isCleanup := false }
    , -- bb4 (inner body): _0 = Add(Copy(_0), 1); _2 = Add(Copy(_2), 1); goto bb3
      { statements :=
          [ { kind := .assign { local_ := 0, projection := [] }
                (.binaryOp .add (.copy { local_ := 0, projection := [] })
                  (Anneal.MirLoops.constU32 1)),
              span := "n8" }
          , { kind := .assign { local_ := 2, projection := [] }
                (.binaryOp .add (.copy { local_ := 2, projection := [] })
                  (Anneal.MirLoops.constU32 1)),
              span := "n9" } ]
        terminator := { kind := .goto 3, span := "n10" }
        isCleanup := false }
    , -- bb5 (outer latch): _1 = Add(Copy(_1), 1); goto bb1
      { statements :=
          [ { kind := .assign { local_ := 1, projection := [] }
                (.binaryOp .add (.copy { local_ := 1, projection := [] })
                  (Anneal.MirLoops.constU32 1)),
              span := "n11" } ]
        terminator := { kind := .goto 1, span := "n12" }
        isCleanup := false }
    , -- bb6 (outer exit): StorageDead(_2); return
      { statements :=
          [ { kind := .storageDead 2, span := "n13" } ]
        terminator := { kind := .return_, span := "n14" }
        isCleanup := false } ]

theorem checkPureMir_nestedCountToNMBody (n m : Nat) :
    checkPureMir (nestedCountToNMBody n m) = true := rfl

theorem inferMinFragment_nestedCountToNMBody (n m : Nat) :
    inferMinFragment (nestedCountToNMBody n m) = .pureBoundedLoop := rfl

theorem inferMinFragment_nestedCountToNMBody_le_pureBoundedLoop (n m : Nat) :
    inferMinFragment (nestedCountToNMBody n m) ≤ .pureBoundedLoop := by
  rw [inferMinFragment_nestedCountToNMBody]
  exact Nat.le_refl _

/-- Frame of `nestedCountToNMBody n m` with accumulator `acc`, outer counter `i`,
and inner counter slot `s₂`. -/
def nestedCountState (bb stmt acc i : Nat) (s₂ : LocalSlot) : PureState :=
  { bb := bb, stmtIdx := stmt,
    env := [.init (.scalar ⟨acc, 4⟩), .init (.scalar ⟨i, 4⟩), s₂] }

theorem runMirToBlock_nestedCountToNM_entry (n m : Nat) (v₀ : Value) :
    PureMirExec.runMirToBlock (nestedCountToNMBody n m) 1
      ((initPureState (nestedCountToNMBody n m) [v₀]).toMachineState emptyMemory) =
      .reached ((nestedCountState 1 0 0 0 .uninit).toMachineState emptyMemory) := rfl

theorem runMirToBlock_nestedCountToNM_outer_to_inner (n m acc i : Nat) (s₂ : LocalSlot)
    (hs₂ : s₂ ≠ .dead) (hi : i < n) :
    PureMirExec.runMirToBlock (nestedCountToNMBody n m) 3
      ((nestedCountState 1 0 acc i s₂).toMachineState emptyMemory) =
      .reached ((nestedCountState 3 0 acc i (.init (.scalar ⟨0, 4⟩))).toMachineState emptyMemory) := by
  have hbeq : Nat.beq i n = false := (Bool.not_eq_true _).mp (Nat.ne_of_lt hi ∘ Nat.eq_of_beq_eq_true)
  have hs1 : mirStep (nestedCountToNMBody n m) ((nestedCountState 1 0 acc i s₂).toMachineState emptyMemory) =
      .cont ((nestedCountState (match Nat.beq i n with | true => 6 | false => 2) 0 acc i s₂).toMachineState emptyMemory) := rfl
  rw [hbeq] at hs1
  have hs2 : mirStep (nestedCountToNMBody n m) ((nestedCountState 2 0 acc i s₂).toMachineState emptyMemory) =
      .cont ((nestedCountState 2 1 acc i (.init (.scalar ⟨0, 4⟩))).toMachineState emptyMemory) := by
    cases s₂ with
    | dead => exact absurd rfl hs₂
    | uninit | init _ => rfl
  have hs3 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 2 1 acc i (.init (.scalar ⟨0, 4⟩))).toMachineState emptyMemory) =
      .cont ((nestedCountState 3 0 acc i (.init (.scalar ⟨0, 4⟩))).toMachineState emptyMemory) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (nestedCountToNMBody n m) = 15 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

theorem runMirToBlock_nestedCountToNM_inner_iter (n m acc i j : Nat)
    (hj : j < m) (hacc : acc + 1 < 4294967296) (hm : m < 4294967296) :
    PureMirExec.runMirToBlock (nestedCountToNMBody n m) 3
      ((nestedCountState 3 0 acc i (.init (.scalar ⟨j, 4⟩))).toMachineState emptyMemory) =
      .reached ((nestedCountState 3 0 (acc + 1) i (.init (.scalar ⟨j + 1, 4⟩))).toMachineState emptyMemory) := by
  have hbeq : Nat.beq j m = false := (Bool.not_eq_true _).mp (Nat.ne_of_lt hj ∘ Nat.eq_of_beq_eq_true)
  have hs1 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 3 0 acc i (.init (.scalar ⟨j, 4⟩))).toMachineState emptyMemory) =
      .cont ((nestedCountState (match Nat.beq j m with | true => 5 | false => 4) 0 acc i (.init (.scalar ⟨j, 4⟩))).toMachineState emptyMemory) := rfl
  rw [hbeq] at hs1
  have hs2 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 4 0 acc i (.init (.scalar ⟨j, 4⟩))).toMachineState emptyMemory) =
      .cont ((nestedCountState 4 1 (acc + 1) i (.init (.scalar ⟨j, 4⟩))).toMachineState emptyMemory) := by
    have hmod : (acc + 1) % 4294967296 = acc + 1 := Nat.mod_eq_of_lt hacc
    unfold mirStep stepMirFn
    dsimp [nestedCountState, PureState.toMachineState, emptyMemory]
    simp [nestedCountToNMBody, Anneal.MirLoops.mkMirBody, Anneal.MirLoops.constU32,
      Trusted.Sequence.get?, evalStmt, evalOperand, readProjectedValue, evalRvalue,
      evalConstValue, advanceStmt, Trusted.Sequence.set?, invalidateConflictingBorrows, hmod]
    rfl
  have hs3 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 4 1 (acc + 1) i (.init (.scalar ⟨j, 4⟩))).toMachineState emptyMemory) =
      .cont ((nestedCountState 4 2 (acc + 1) i (.init (.scalar ⟨j + 1, 4⟩))).toMachineState emptyMemory) := by
    have hmod : (j + 1) % 4294967296 = j + 1 := Nat.mod_eq_of_lt (by omega)
    unfold mirStep stepMirFn
    dsimp [nestedCountState, PureState.toMachineState, emptyMemory]
    simp [nestedCountToNMBody, Anneal.MirLoops.mkMirBody, Anneal.MirLoops.constU32,
      Trusted.Sequence.get?, evalStmt, evalOperand, readProjectedValue, evalRvalue,
      evalConstValue, advanceStmt, Trusted.Sequence.set?, invalidateConflictingBorrows, hmod]
    rfl
  have hs4 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 4 2 (acc + 1) i (.init (.scalar ⟨j + 1, 4⟩))).toMachineState emptyMemory) =
      .cont ((nestedCountState 3 0 (acc + 1) i (.init (.scalar ⟨j + 1, 4⟩))).toMachineState emptyMemory) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (nestedCountToNMBody n m) = 15 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3, hs4]
  rfl

/-- **Inner `[0, m)` loop of `nestedCountToNMBody n m` lifted as a `StepsTo` segment**
via `stepsTo_forRangeUp_of_runMirToBlock`. -/
theorem stepsTo_nestedCountToNM_inner (n m acc i : Nat)
    (haccm : acc + m < 4294967296) (hm : m < 4294967296) :
    StepsTo (mirStep (nestedCountToNMBody n m))
      ((nestedCountState 3 0 acc i (.init (.scalar ⟨0, 4⟩))).toMachineState emptyMemory)
      (fun s => s = (nestedCountState 3 0 (acc + m) i (.init (.scalar ⟨m, 4⟩))).toMachineState emptyMemory) :=
  stepsTo_forRangeUp_of_runMirToBlock (nestedCountToNMBody n m) 3 0 m () (fun _ _ _ u => u)
    (fun j _ => (nestedCountState 3 0 (acc + j) i (.init (.scalar ⟨j, 4⟩))).toMachineState emptyMemory)
    (Nat.zero_le m)
    (fun j _ hj _ =>
      runMirToBlock_nestedCountToNM_inner_iter n m (acc + j) i j hj (by omega) hm)

theorem runMirToBlock_nestedCountToNM_inner_to_outer (n m acc i : Nat)
    (hi : i < n) (hn : n < 4294967296) :
    PureMirExec.runMirToBlock (nestedCountToNMBody n m) 1
      ((nestedCountState 3 0 acc i (.init (.scalar ⟨m, 4⟩))).toMachineState emptyMemory) =
      .reached ((nestedCountState 1 0 acc (i + 1) (.init (.scalar ⟨m, 4⟩))).toMachineState emptyMemory) := by
  have hs1 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 3 0 acc i (.init (.scalar ⟨m, 4⟩))).toMachineState emptyMemory) =
      .cont ((nestedCountState (match Nat.beq m m with | true => 5 | false => 4) 0 acc i (.init (.scalar ⟨m, 4⟩))).toMachineState emptyMemory) := rfl
  rw [Nat.beq_refl] at hs1
  have hs2 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 5 0 acc i (.init (.scalar ⟨m, 4⟩))).toMachineState emptyMemory) =
      .cont ((nestedCountState 5 1 acc (i + 1) (.init (.scalar ⟨m, 4⟩))).toMachineState emptyMemory) := by
    have hmod : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
    unfold mirStep stepMirFn
    dsimp [nestedCountState, PureState.toMachineState, emptyMemory]
    simp [nestedCountToNMBody, Anneal.MirLoops.mkMirBody, Anneal.MirLoops.constU32,
      Trusted.Sequence.get?, evalStmt, evalOperand, readProjectedValue, evalRvalue,
      evalConstValue, advanceStmt, Trusted.Sequence.set?, invalidateConflictingBorrows, hmod]
    rfl
  have hs3 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 5 1 acc (i + 1) (.init (.scalar ⟨m, 4⟩))).toMachineState emptyMemory) =
      .cont ((nestedCountState 1 0 acc (i + 1) (.init (.scalar ⟨m, 4⟩))).toMachineState emptyMemory) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (nestedCountToNMBody n m) = 15 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

theorem runMirToBlock_nestedCountToNM_exit (n m acc : Nat) (s₂ : LocalSlot) :
    PureMirExec.runMirToBlock (nestedCountToNMBody n m) 1
      ((nestedCountState 1 0 acc n s₂).toMachineState emptyMemory) =
      .halted (.normal (.scalar ⟨acc, 4⟩, emptyMemory)) := by
  have hs1 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 1 0 acc n s₂).toMachineState emptyMemory) =
      .cont ((nestedCountState (match Nat.beq n n with | true => 6 | false => 2) 0 acc n s₂).toMachineState emptyMemory) := rfl
  rw [Nat.beq_refl] at hs1
  have hs2 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 6 0 acc n s₂).toMachineState emptyMemory) =
      .cont ((nestedCountState 6 1 acc n .dead).toMachineState emptyMemory) := rfl
  have hs3 : mirStep (nestedCountToNMBody n m)
      ((nestedCountState 6 1 acc n .dead).toMachineState emptyMemory) =
      .done (.normal (.scalar ⟨acc, 4⟩, emptyMemory)) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (nestedCountToNMBody n m) = 15 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3]
  rfl

/-- **Fuel-free `PureMirConverges` for the live 2D nested-loop `nestedCountToNMBody n m`**
over all symbolic bounds `n, m` (`n < 2^32`, `m < 2^32`, `n * m < 2^32`):
composes `mirWpConverges_forRangeUp` (outer `[0, n)` loop with relational header
invariant over `s₂ : LocalSlot`) with `stepsTo_nestedCountToNM_inner` (inner
`[0, m)` loop lifted via `stepsTo_forRangeUp_of_runMirToBlock`). -/
theorem live_nestedCountToNM_pureMirConverges_all (n m : Nat)
    (hn : n < 4294967296) (hm : m < 4294967296) (hnm : n * m < 4294967296)
    (v₀ : Value) :
    PureMirConverges (nestedCountToNMBody n m)
      (initPureState (nestedCountToNMBody n m) [v₀])
      (fun retVal => retVal = .scalar ⟨n * m, 4⟩) := by
  refine mirWpConverges_of_stepsTo_bind
    (stepsTo_of_runToTarget_reached (runMirToBlock_nestedCountToNM_entry n m v₀))
    (fun s_start hs => ?_)
  cases hs
  refine MirLiftCore.mirWpConverges_forRangeUp (nestedCountToNMBody n m) 0 n () (fun _ _ _ u => u)
    (fun i _ ms => ∃ s₂ : LocalSlot, s₂ ≠ .dead ∧
      ms = (nestedCountState 1 0 (m * i) i s₂).toMachineState emptyMemory)
    ((nestedCountState 1 0 0 0 .uninit).toMachineState emptyMemory)
    (mirNormalPost (fun retVal _ => retVal = .scalar ⟨n * m, 4⟩))
    (Nat.zero_le n) ⟨.uninit, ⟨(by intro h; nomatch h), rfl⟩⟩ ?_ ?_
  · intro i _ hi _ s ⟨s₂, hs₂, hs⟩
    subst hs
    have h_le : m * (i + 1) ≤ m * n := Nat.mul_le_mul_left m hi
    have h_accm : m * i + m < 4294967296 := by
      rw [Nat.mul_comm] at hnm
      exact Nat.lt_of_le_of_lt h_le hnm
    refine (stepsTo_of_runToTarget_reached
      (runMirToBlock_nestedCountToNM_outer_to_inner n m (m * i) i s₂ hs₂ hi)).trans
      (fun s₁ hs₁ => ?_)
    subst hs₁
    refine (stepsTo_nestedCountToNM_inner n m (m * i) i h_accm hm).trans
      (fun s₂' hs₂' => ?_)
    subst hs₂'
    exact (stepsTo_of_runToTarget_reached
      (runMirToBlock_nestedCountToNM_inner_to_outer n m (m * (i + 1)) i hi hn)).mono
      (by rintro _ rfl; exact ⟨.init (.scalar ⟨m, 4⟩), ⟨(by intro h; nomatch h), rfl⟩⟩)
  · intro s_exit ⟨s₂, _, hs⟩
    subst hs
    rw [Nat.mul_comm m n]
    exact wpConverges_of_runToTarget_halted
      (runMirToBlock_nestedCountToNM_exit n m (n * m) s₂) rfl

/-- **End-to-end `VerificationResult` for the live 2D nested-loop `nestedCountToNMBody n m`**
over all symbolic bounds `n, m` (`n < 2^32`, `m < 2^32`, `n * m < 2^32`), with
zero fuel numerals and purely constructive axioms (`⊆ {propext, Quot.sound}`). -/
theorem verify_nestedCountToNM_all_n_m (n m : Nat)
    (hn : n < 4294967296) (hm : m < 4294967296) (hnm : n * m < 4294967296) :
    VerificationResult
      { body := nestedCountToNMBody n m
        pre := fun args => ∃ v₀, args = [v₀]
        post := fun _ retVal => retVal = .scalar ⟨n * m, 4⟩
        callees := [] } :=
  verifyMirNoPanic_of_inferMinFragment_le_pureBoundedLoop _
    (inferMinFragment_nestedCountToNMBody_le_pureBoundedLoop n m)
    (fun args ⟨v₀, hargs⟩ => by
      subst hargs
      exact live_nestedCountToNM_pureMirConverges_all n m hn hm hnm v₀)
    rfl

/-- **Constructive `StatefulVerificationResult` for the live 2D nested-loop
`nestedCountToNMBody n m`** (`⊆ {propext, Quot.sound}`). -/
theorem verifyStateful_nestedCountToNM_all_n_m (n m : Nat)
    (hn : n < 4294967296) (hm : m < 4294967296) (hnm : n * m < 4294967296) :
    StatefulVerificationResult
      { body := nestedCountToNMBody n m
        pre := fun args mem => (∃ v₀, args = [v₀]) ∧ RootActiveMemory mem
        post := fun _ mem retVal mem' =>
          mem' = mem ∧ retVal = .scalar ⟨n * m, 4⟩
        callees := [] } :=
  verifyStatefulMirNoPanic_of_inferMinFragment_le_pureBoundedLoop _
    (inferMinFragment_nestedCountToNMBody_le_pureBoundedLoop n m)
    (fun _ _ hp => hp.2)
    (fun args _ ⟨⟨v₀, hargs⟩, _⟩ => by
      subst hargs
      exact (live_nestedCountToNM_pureMirConverges_all n m hn hm hnm v₀).mono
        (fun _ h => ⟨rfl, h⟩))
    rfl

/-- Live single-block self-loop (`do { i += 1 } while i != n`): the loop header
`bb1` jumps back to itself, so the next target re-entry is reached immediately
after one body execution. -/
def selfLoopMirBody (n : Nat) : CapturedMir :=
  Anneal.MirLoops.mkMirBody "Anneal::MirLiftCore::self_loop_mir" 0
    [ { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "_0" }
    , { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "i" } ]
    [ { statements :=
          [ { kind := .assign { local_ := 1, projection := [] } (.use (Anneal.MirLoops.constU32 0)),
              span := "l0" } ]
        terminator := { kind := .goto 1, span := "l1" }
        isCleanup := false }
    , { statements :=
          [ { kind := .assign { local_ := 1, projection := [] }
                (.binaryOp .add (.copy { local_ := 1, projection := [] }) (Anneal.MirLoops.constU32 1)),
              span := "l2" } ]
        terminator :=
          { kind := .switchInt (.copy { local_ := 1, projection := [] })
              { branches := [(n, 2)], otherwise := 1 }
            span := "l3" }
        isCleanup := false }
    , { statements :=
          [ { kind := .assign { local_ := 0, projection := [] }
                (.use (.copy { local_ := 1, projection := [] })),
              span := "l4" } ]
        terminator := { kind := .return_, span := "l5" }
        isCleanup := false } ]

/-- The increment statement of the self-looping header. -/
theorem selfLoopMir_incr_step (n i : Nat) (hi : i + 1 < 4294967296) :
    mirStep (selfLoopMirBody n) ((countToNPureState 1 0 i).toMachineState emptyMemory) =
      .cont ((countToNPureState 1 1 (i + 1)).toMachineState emptyMemory) := by
  have hmod : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt hi
  unfold mirStep stepMirFn
  dsimp [countToNPureState, PureState.toMachineState, emptyMemory]
  simp [selfLoopMirBody, Anneal.MirLoops.mkMirBody, Anneal.MirLoops.constU32,
    Trusted.Sequence.get?, evalStmt, evalOperand, readProjectedValue, evalRvalue,
    evalConstValue, advanceStmt, Trusted.Sequence.set?, invalidateConflictingBorrows, hmod]
  rfl

/-- **No overshoot on a live self-loop**: from the header `(bb1, 0)` the
header-targeted stepper stops at the *first* re-entry, one iteration later. -/
theorem runMirToBlock_selfLoopMir_iter (n i : Nat) (hne : i + 1 ≠ n) (hi : i + 1 < 4294967296) :
    PureMirExec.runMirToBlock (selfLoopMirBody n) 1 ((countToNPureState 1 0 i).toMachineState emptyMemory) =
      .reached ((countToNPureState 1 0 (i + 1)).toMachineState emptyMemory) := by
  have hbeq : Nat.beq (i + 1) n = false := (Bool.not_eq_true _).mp (hne ∘ Nat.eq_of_beq_eq_true)
  have hs1 := selfLoopMir_incr_step n i hi
  have hs2 : mirStep (selfLoopMirBody n) ((countToNPureState 1 1 (i + 1)).toMachineState emptyMemory) =
      .cont ((countToNPureState (match Nat.beq (i + 1) n with | true => 2 | false => 1) 0 (i + 1)).toMachineState emptyMemory) := rfl
  rw [hbeq] at hs2
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (selfLoopMirBody n) = 6 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2]
  rfl

/-- On the same live self-loop header, `PureMirExec.runMirToBlock` (mandatory first
step) advances exactly one iteration, while live
`Anneal.FunctionalTranslation.runMirToBlock` stays put. -/
theorem selfLoopMir_no_overshoot_vs_live_stationary (n i bound : Nat) (hne : i + 1 ≠ n)
    (hi : i + 1 < 4294967296) :
    PureMirExec.runMirToBlock (selfLoopMirBody n) 1 ((countToNPureState 1 0 i).toMachineState emptyMemory) =
        .reached ((countToNPureState 1 0 (i + 1)).toMachineState emptyMemory) ∧
      Anneal.FunctionalTranslation.runMirToBlock (bound + 1) (selfLoopMirBody n) 1
        ((countToNPureState 1 0 i).toMachineState emptyMemory) =
        some ((countToNPureState 1 0 i).toMachineState emptyMemory) :=
  ⟨runMirToBlock_selfLoopMir_iter n i hne hi,
   live_runMirToBlock_stationary_at_target _ 1 bound _ rfl rfl⟩

/-- Entry segment (`bb0 -> bb1`). -/
theorem runMirToBlock_selfLoopMir_entry (n : Nat) (v₀ : Value) :
    PureMirExec.runMirToBlock (selfLoopMirBody n) 1
      ((initPureState (selfLoopMirBody n) [v₀]).toMachineState emptyMemory) =
      .reached ((countToNPureState 1 0 0).toMachineState emptyMemory) := rfl

/-- Final iteration from counter `k` exits through `bb2` and returns `k + 1`. -/
theorem runMirToBlock_selfLoopMir_exit (k : Nat) (hk : k + 1 < 4294967296) :
    PureMirExec.runMirToBlock (selfLoopMirBody (k + 1)) 1
      ((countToNPureState 1 0 k).toMachineState emptyMemory) =
      .halted (.normal (.scalar ⟨k + 1, 4⟩, emptyMemory)) := by
  have hs1 := selfLoopMir_incr_step (k + 1) k hk
  have hs2 : mirStep (selfLoopMirBody (k + 1)) ((countToNPureState 1 1 (k + 1)).toMachineState emptyMemory) =
      .cont ((countToNPureState (match Nat.beq (k + 1) (k + 1) with | true => 2 | false => 1) 0 (k + 1)).toMachineState emptyMemory) := rfl
  rw [Nat.beq_refl] at hs2
  have hs3 : mirStep (selfLoopMirBody (k + 1)) ((countToNPureState 2 0 (k + 1)).toMachineState emptyMemory) =
      .cont { frame := { blockIdx := 2, stmtIdx := 1,
                         locals := [.init (.scalar ⟨k + 1, 4⟩), .init (.scalar ⟨k + 1, 4⟩)] },
              memory := emptyMemory } := rfl
  have hs4 : mirStep (selfLoopMirBody (k + 1))
      { frame := { blockIdx := 2, stmtIdx := 1,
                   locals := [.init (.scalar ⟨k + 1, 4⟩), .init (.scalar ⟨k + 1, 4⟩)] },
        memory := emptyMemory } =
      .done (.normal (.scalar ⟨k + 1, 4⟩, emptyMemory)) := rfl
  unfold PureMirExec.runMirToBlock
  have hmb : mirSegmentBound (selfLoopMirBody (k + 1)) = 6 := rfl
  rw [hmb]
  simp only [runToTarget, hs1, runUntilTarget, hs2, hs3, hs4]
  rfl

theorem checkPureMir_selfLoopMirBody (n : Nat) :
    checkPureMir (selfLoopMirBody n) = true := rfl

theorem inferMinFragment_selfLoopMirBody (n : Nat) :
    inferMinFragment (selfLoopMirBody n) = .pureBoundedLoop := rfl

theorem inferMinFragment_selfLoopMirBody_le_pureBoundedLoop (n : Nat) :
    inferMinFragment (selfLoopMirBody n) ≤ .pureBoundedLoop := by
  rw [inferMinFragment_selfLoopMirBody]
  exact Nat.le_refl _

/-- **First-hit uniqueness on the live single-block self-loop `selfLoopMirBody n`**:
from `(bb1, 0, i)` with `i + 1 ≠ n`, the unique first re-entry to `(bb1, 0)` occurs
at `(bb1, 0, i + 1)` after `m = 1` intermediate step (`(bb1, 1, i + 1)`). -/
theorem selfLoopMir_firstHit_unique (n i : Nat) (hne : i + 1 ≠ n)
    (hi : i + 1 < 4294967296) {m : Nat} {s' : MachineState}
    (h : FirstHitIn (mirStep (selfLoopMirBody n))
      (fun ms => ms.frame.blockIdx == 1 && ms.frame.stmtIdx == 0) m
      ((countToNPureState 1 0 i).toMachineState emptyMemory) s') :
    s' = (countToNPureState 1 0 (i + 1)).toMachineState emptyMemory ∧ m = 1 := by
  have hbeq : Nat.beq (i + 1) n = false := (Bool.not_eq_true _).mp (hne ∘ Nat.eq_of_beq_eq_true)
  have hs1 := selfLoopMir_incr_step n i hi
  have hs2 : mirStep (selfLoopMirBody n) ((countToNPureState 1 1 (i + 1)).toMachineState emptyMemory) =
      .cont ((countToNPureState (match Nat.beq (i + 1) n with | true => 2 | false => 1) 0 (i + 1)).toMachineState emptyMemory) := rfl
  rw [hbeq] at hs2
  exact FirstHitIn.unique h (.later hs1 rfl (.here hs2 rfl))

/-- **End-to-end `VerificationResult` for the live self-loop** over every symbolic
bound (fragment-routed `runMirToBlock` + `forRangeUp` gate, zero fuel numerals). -/
theorem verify_selfLoopMir_all_k (k : Nat) (hk : k + 1 < 4294967296) :
    VerificationResult
      { body := selfLoopMirBody (k + 1)
        pre := fun args => ∃ v₀, args = [v₀]
        post := fun _ retVal => retVal = .scalar ⟨k + 1, 4⟩
        callees := [] } :=
  verifyMirNoPanic_forRangeUp_of_inferMinFragment_le_pureBoundedLoop _
    (inferMinFragment_selfLoopMirBody_le_pureBoundedLoop (k + 1)) 1
    (fun _ => 0) (fun _ => k) (fun _ => ()) (fun _ _ _ _ u => u)
    (fun _ i _ => countToNPureState 1 0 i)
    (fun _ _ => Nat.zero_le k)
    (fun args ⟨v₀, hargs⟩ => by subst hargs; exact runMirToBlock_selfLoopMir_entry (k + 1) v₀)
    (fun _ _ i _ hlt _ =>
      runMirToBlock_selfLoopMir_iter (k + 1) i (by omega) (by omega))
    (fun _ _ => ⟨.scalar ⟨k + 1, 4⟩, emptyMemory, runMirToBlock_selfLoopMir_exit k hk, rfl⟩)
    rfl

/-- **Constructive `StatefulVerificationResult` for the live self-loop `selfLoopMirBody (k + 1)`**
(`⊆ {propext, Quot.sound}`) over every symbolic `k` (`k + 1 < 2^32`) and root-active memory. -/
theorem verifyStateful_selfLoopMir_all_k (k : Nat) (hk : k + 1 < 4294967296) :
    StatefulVerificationResult
      { body := selfLoopMirBody (k + 1)
        pre := fun args mem => (∃ v₀, args = [v₀]) ∧ RootActiveMemory mem
        post := fun _ mem retVal mem' =>
          mem' = mem ∧ retVal = .scalar ⟨k + 1, 4⟩
        callees := [] } :=
  verifyStatefulMirNoPanic_forRangeUp_of_inferMinFragment_le_pureBoundedLoop _
    (inferMinFragment_selfLoopMirBody_le_pureBoundedLoop (k + 1))
    (fun _ _ hp => hp.2) 1
    (fun _ _ => 0) (fun _ _ => k) (fun _ _ => ()) (fun _ _ _ _ _ u => u)
    (fun _ _ i _ => countToNPureState 1 0 i)
    (fun _ _ _ => Nat.zero_le k)
    (fun args _ ⟨⟨v₀, hargs⟩, _⟩ => by rw [hargs]; exact runMirToBlock_selfLoopMir_entry (k + 1) v₀)
    (fun _ _ _ i _ hlt _ =>
      runMirToBlock_selfLoopMir_iter (k + 1) i (by omega) (by omega))
    (fun _ _ _ => ⟨.scalar ⟨k + 1, 4⟩, emptyMemory, runMirToBlock_selfLoopMir_exit k hk, rfl, rfl⟩)
    rfl

/-- Live non-terminating `CapturedMir` self-loop (`bb0: goto -> bb0`, 1 local `_0`). -/
def infiniteLoopMirBody : CapturedMir :=
  Anneal.MirLoops.mkMirBody "Anneal::MirLiftCore::infinite_loop_mir" 0
    [ { mutability := .mut, ty := Anneal.MirFuelFree.u32Ty, debugName := some "_0" } ]
    [ { statements := []
        terminator := { kind := .goto 0, span := "inf0" }
        isCleanup := false } ]

theorem checkPureMir_infiniteLoopMirBody :
    checkPureMir infiniteLoopMirBody = true := rfl

theorem inferMinFragment_infiniteLoopMirBody :
    inferMinFragment infiniteLoopMirBody = .pureBoundedLoop := rfl

theorem stepMirFn_infiniteLoopMirBody (env : PureEnv) :
    stepMirFn infiniteLoopMirBody
      (({ bb := 0, stmtIdx := 0, env := env } : PureState).toMachineState emptyMemory) =
      .tau (.running (({ bb := 0, stmtIdx := 0, env := env } : PureState).toMachineState emptyMemory)) :=
  rfl

theorem mirStep_infiniteLoopMirBody (env : PureEnv) :
    mirStep infiniteLoopMirBody
      (({ bb := 0, stmtIdx := 0, env := env } : PureState).toMachineState emptyMemory) =
      .cont (({ bb := 0, stmtIdx := 0, env := env } : PureState).toMachineState emptyMemory) :=
  rfl

theorem evalFuel_infiniteLoopMirBody_outOfFuel :
    ∀ (k : Nat) (env : PureEnv),
      evalFuel (mirStep infiniteLoopMirBody) k
        (({ bb := 0, stmtIdx := 0, env := env } : PureState).toMachineState emptyMemory) =
        .outOfFuel
  | 0, _ => rfl
  | k + 1, env => evalFuel_infiniteLoopMirBody_outOfFuel k env

/-- **Non-terminating live `CapturedMir` loop refutes `WpConverges (mirStep _)`**. -/
theorem not_wpConverges_infiniteLoopMirBody (env : PureEnv) (post : MirOutcome → Prop) :
    ¬ WpConverges (mirStep infiniteLoopMirBody)
        (({ bb := 0, stmtIdx := 0, env := env } : PureState).toMachineState emptyMemory) post := by
  rintro ⟨k, v, hk, _⟩
  rw [evalFuel_infiniteLoopMirBody_outOfFuel k env] at hk
  cases hk

/-- Targeting an unreachable exit block (`bb1`) on `infiniteLoopMirBody` returns
`.outOfFuel`, whereas targeting the self-looping header (`bb0`) stops after one
mandatory step with `.reached`. -/
theorem runMirToBlock_infiniteLoopMirBody_outOfFuel_vs_self (env : PureEnv) :
    PureMirExec.runMirToBlock infiniteLoopMirBody 1
        (({ bb := 0, stmtIdx := 0, env := env } : PureState).toMachineState emptyMemory) = .outOfFuel ∧
      PureMirExec.runMirToBlock infiniteLoopMirBody 0
        (({ bb := 0, stmtIdx := 0, env := env } : PureState).toMachineState emptyMemory) =
        .reached (({ bb := 0, stmtIdx := 0, env := env } : PureState).toMachineState emptyMemory) :=
  ⟨rfl, rfl⟩

theorem not_wpMirExecSym_of_tau_self {body : CapturedMir} {s : MachineState}
    (hs : stepMirFn body s = .tau (.running s)) (post : MirOutcome → Prop) :
    ∀ (fuel : Nat),
      ¬ Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body (.running s) post
  | 0, h => h
  | fuel + 1, h => by
    unfold Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym at h
    rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTree_eq,
      Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeWP_eq] at h
    dsimp only [stepMirState] at h
    rw [hs] at h
    exact not_wpMirExecSym_of_tau_self hs post fuel h

/-- **General stationary `.tau` self-loop refutes live `MirWpConverges`**. -/
theorem not_mirWpConverges_of_tau_self {body : CapturedMir} {s : MachineState}
    (hs : stepMirFn body s = .tau (.running s)) (post : MirOutcome → Prop) :
    ¬ Anneal.MirFuelFree.MirWpConverges body s post := by
  rintro ⟨fuel, h⟩
  exact not_wpMirExecSym_of_tau_self hs post fuel h

/-- **Live non-terminating `infiniteLoopMirBody` refutes `MirWpConverges` and `PureMirConverges`**. -/
theorem not_pureMirConverges_infiniteLoopMirBody (env : PureEnv) (post : Value → Prop) :
    ¬ PureMirConverges infiniteLoopMirBody { bb := 0, stmtIdx := 0, env := env } post :=
  not_mirWpConverges_of_tau_self (stepMirFn_infiniteLoopMirBody env) _

end FuelFreeLoops

/-!
## Call-Cone Narrowing (`calleesAgreeOn`, `withCallees` Bisimulation, `CallConeClosed`)

`Memory.callees : List CapturedMir` is consulted by exactly two families of trusted
lookups: `lookupCallee` (through `resolveCalleeBodyAndArgs?` / `findCallee?`) at
`TerminatorKind.call` / `.tailCall` (and the `const_eval_select` runtime target), and
`checkCalleeSig` at function-pointer reification casts. This section proves that
replacing the callee table `c₁` by any `c₂` that agrees with it (under `findCallee?`
first-match semantics) on a *call cone* of definition paths preserves every
`stepMirState` step, every bounded run (`runMirExecBounded`), and every fuel-bounded
weakest precondition (`wpMirExecSym`, `MirWpConverges`) whose postcondition ignores
`Memory.callees`:

* `Memory.withCalleeCtx` / `Memory.withCallees` and the `mapMem` lifts to
  `MachineState`, `RvalueEvalResult`, `MirOutcome`, `MirExecState`, `MirStepNode`
  (external-call requests carry the transformed memory; continuations are
  untouched, since `resumeExternal*` read only the caller frame and the answer).
* `evalRvalue_withCalleeCtx` / `evalStmt_withCalleeCtx`: statements that are not
  function-pointer reifications (`Statement.calleeQueryFree`) commute with every
  replacement of `(callees, activeCallee, traitImpls)`. `Memory.callStack` is kept:
  statements read it (the active frame's depth scopes `BorrowEntry.targetFrameDepth`,
  and dereferencing writes reach suspended caller frames through it).
* `evalTerminator_withCallees` / `stepMirState_callees_cone_eq`: one-step
  bisimulation under `calleesAgreeOn` and the per-step cone condition `StepConeSafe`.
* `runMirExecBounded_cone_narrow`, `wpMirExecSym_cone_narrow`,
  `runCfgWithCallees_cone_narrow`, `mirWpConverges_cone_narrow`: multi-step
  transfer along `ConeReach` (the semantic step-invariant).
* `CallConeClosed` (decidable, fails closed on indirect / fn-pointer / fn-item-local
  / generic / intrinsic calls and on reification casts) implies `ConeReach` from
  `initMachineStateWithMemoryAndCallees`.
-/

section CallConeNarrowing

/-- The type of `Memory.callees`. -/
abbrev CalleeEnv := List CapturedMir

/-- Replace the callee table, active callee, and trait-impl table of `m` (but not its
call stack, which statement evaluation reads). -/
@[reducible]
def Memory.withCalleeCtx (c : CalleeEnv) (ac : Option CapturedMir)
    (ti : List TraitImplEntry) (m : Memory) : Memory :=
  { m with callees := c, activeCallee := ac, traitImpls := ti }

/-- Replace only the callee table of `m` (the `withCallees` narrowing map). -/
@[reducible]
def Memory.withCallees (c : CalleeEnv) (m : Memory) : Memory :=
  { m with callees := c }

/-- Apply a memory transformer to a `MachineState`. -/
def MachineState.mapMem (f : Memory → Memory) (s : MachineState) : MachineState :=
  { s with memory := f s.memory }

/-- Apply a memory transformer to the memory of an `RvalueEvalResult`. -/
def RvalueEvalResult.mapMem (f : Memory → Memory) : RvalueEvalResult → RvalueEvalResult
  | .ok v l m => .ok v l (f m)
  | .ub => .ub
  | .unsupported => .unsupported

/-- Apply a memory transformer to the final memory of a normal `MirOutcome`. -/
def MirOutcome.mapMem (f : Memory → Memory) : MirOutcome → MirOutcome
  | .normal (v, m) => .normal (v, f m)
  | .panic => .panic
  | .abort => .abort

/-- Apply a memory transformer to a `MirExecState`. -/
def MirExecState.mapMem (f : Memory → Memory) : MirExecState → MirExecState
  | .running s => .running (MachineState.mapMem f s)
  | .halted out => .halted (MirOutcome.mapMem f out)
  | .faulted fk => .faulted fk

/--
Apply a memory transformer to a `MirStepNode`: successor states and outcomes are
mapped, an external-call request carries the mapped memory, and external-call
continuations are left untouched (the answer supplies the post-call memory).
-/
def MirStepNode.mapMem (f : Memory → Memory) : MirStepNode → MirStepNode
  | .ret out => .ret (MirOutcome.mapMem f out)
  | .tau st => .tau (MirExecState.mapMem f st)
  | .vis (.inl fk) k => .vis (.inl fk) k
  | .vis (.inr (.inl obs)) k => .vis (.inr (.inl obs)) (fun u => MirExecState.mapMem f (k u))
  | .vis (.inr (.inr (.call req))) k =>
    .vis (.inr (.inr (.call { req with memory := f req.memory }))) k

/--
`true` unless `rv` is a function-pointer reification cast whose evaluation consults
`Memory.callees` through `checkCalleeSig` (`UnsafeFnPointer` casts only read
`Memory.fnPtrs`).
-/
def Rvalue.calleeQueryFree : Rvalue → Bool
  | .cast (.pointerCoercion ck) _ _ =>
    !isReifyFnPointerCoercion ck || stringEq ck "UnsafeFnPointer"
  | _ => true

/-- `true` unless `stmt` assigns a `Rvalue.calleeQueryFree = false` reification cast. -/
def Statement.calleeQueryFree (stmt : Statement) : Bool :=
  match stmt.kind with
  | .assign _ rv => Rvalue.calleeQueryFree rv
  | _ => true

theorem Rvalue.calleeQueryFree_pointerCoercion {ck : String} {op : Operand} {ty : Ty}
    (h : Rvalue.calleeQueryFree (.cast (.pointerCoercion ck) op ty) = true) :
    isReifyFnPointerCoercion ck = false ∨ stringEq ck "UnsafeFnPointer" = true := by
  change (!isReifyFnPointerCoercion ck || stringEq ck "UnsafeFnPointer") = true at h
  cases h_r : isReifyFnPointerCoercion ck with
  | false => exact Or.inl rfl
  | true =>
    rw [h_r] at h
    exact Or.inr h

private def ccEvalAssignNonDeref
    (s : MachineState) (dstLoc : Local) (proj : List ProjectionElem)
    (val : Value) (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  match get? locals₁ dstLoc with
  | .some (.init rootVal) =>
    match
      writeProjectedForLocal
        locals₁
        localDecls
        layouts
        dstLoc
        (ensureNestedFieldShells rootVal proj)
        proj
        val
    with
    | .ok rootVal' =>
      match set? locals₁ dstLoc (.init rootVal') with
      | .some locals₂ =>
        let resolvedLocalProj :=
          resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc proj
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' :=
            invalidateConflictingBorrowsAtProj
              mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict
              mem₁.borrows (protHead :: protTail) dstLoc .none resolvedLocalProj 0 0
              (length mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrowsAtProj
                mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | .some .uninit =>
    match (match proj with
       | hd :: tl => uninitFieldWriteShell? localDecls layouts dstLoc hd tl
       | .nil => .none) with
    | .some rootVal =>
      match writeProjectedForLocal locals₁ localDecls layouts dstLoc rootVal proj val with
      | .ok rootVal' =>
        match set? locals₁ dstLoc (.init rootVal') with
        | .some locals₂ =>
          let resolvedLocalProj :=
            resolveBorrowWriteLocalProj
              localDecls
              layouts
              locals₁
              dstLoc
              proj
          match mem₁.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrowsAtProj
                mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                mem₁.borrows (protHead :: protTail) dstLoc .none resolvedLocalProj 0 0
                (length mem₁.callStack)
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
    | .none => MirStepNode.fail .ub
  | .some .dead => MirStepNode.fail .ub
  | .none => MirStepNode.fail .ub

private def ccEvalAssignDst
    (s : MachineState) (dst : Place) (val : Value)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  match dst.projection with
  | .nil =>
    match get? locals₁ dst.local_ with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? locals₁ dst.local_ (.init val) with
      | .some locals₂ =>
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' :=
            invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict
              mem₁.borrows (protHead :: protTail) dst.local_ .none .nil 0 0
              (length mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .deref :: restProj =>
    match
      evalPlaceWrite locals₁ mem₁.borrows dst val mem₁.activeProtectors localDecls layouts
        mem₁.callStack
    with
    | .ok locals₂ =>
      match
        Bool.or
          (derefWriteTreeUB locals₁ mem₁.borrows dst)
          (derefWriteUnionProtectorUB
            localDecls layouts locals₁ mem₁.borrows mem₁.activeProtectors dst restProj
            mem₁.callStack)
      with
      | true => MirStepNode.fail .ub
      | false =>
        let borrows' :=
          invalidateDerefWriteBorrowsWithLayouts
            localDecls layouts locals₁ mem₁.borrows dst restProj mem₁.callStack
        MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
    | .ub =>
      match mem₁.callStack with
      | .nil =>
        match mem₁.callerLocals with
        | .nil => MirStepNode.fail .ub
        | _ :: _ =>
          match
            evalCallerPlaceWrite
              locals₁ mem₁.callerLocals mem₁.borrows dst val mem₁.activeProtectors
          with
          | .ok callerLocals' =>
            match derefWriteTreeUB locals₁ mem₁.borrows dst with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateDerefWriteBorrows
                  locals₁ mem₁.borrows dst restProj mem₁.callerLocals
              MirStepNode.step
                (advanceStmt s locals₁
                  { mem₁ with borrows := borrows', callerLocals := callerLocals' })
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
      | _ :: _ =>
        evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts
    | .unsupported => MirStepNode.unsupported
  | hd :: tl =>
    ccEvalAssignNonDeref s dst.local_ (hd :: tl) val locals₁ mem₁ localDecls layouts

private theorem ccEvalStmt_assign_eq
    (s : MachineState) (dst : Place) (rv : Rvalue) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt s ⟨.assign dst rv, span⟩ localDecls layouts =
      match evalRvalue s.frame.locals rv s.memory localDecls layouts with
      | .ok val locals₁ mem₁ => ccEvalAssignDst s dst val locals₁ mem₁ localDecls layouts
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold evalStmt
  dsimp only
  cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
  | ub => rfl
  | unsupported => rfl
  | ok val locals₁ mem₁ =>
    rcases dst with ⟨dstLoc, dstProj⟩
    cases dstProj with
    | nil => rfl
    | cons hd tl => cases hd <;> rfl

private theorem ccEvalAssignDst_nonDeref
    (s : MachineState) (dstLoc : Local) (hd : ProjectionElem)
    (tl : List ProjectionElem) (val : Value)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_nd : hd ≠ .deref) :
    ccEvalAssignDst s ⟨dstLoc, hd :: tl⟩ val locals₁ mem₁ localDecls layouts =
      ccEvalAssignNonDeref s dstLoc (hd :: tl) val locals₁ mem₁ localDecls layouts := by
  cases hd with
  | deref => exact False.elim (h_nd rfl)
  | _ => rfl

/-- Constructive decision of `hd = .deref` (`ProjectionElem` has no `DecidableEq`, and a
`by_cases` would fall back to `Classical.propDecidable`). -/
private def ccProjIsDeref : (hd : ProjectionElem) → Decidable (hd = .deref)
  | .deref => isTrue rfl
  | .field .. => isFalse (fun h => ProjectionElem.noConfusion h)
  | .index .. => isFalse (fun h => ProjectionElem.noConfusion h)
  | .constantIndex .. => isFalse (fun h => ProjectionElem.noConfusion h)
  | .subslice .. => isFalse (fun h => ProjectionElem.noConfusion h)
  | .downcast .. => isFalse (fun h => ProjectionElem.noConfusion h)
  | .opaqueCast .. => isFalse (fun h => ProjectionElem.noConfusion h)
  | .unwrapUnsafeBinder .. => isFalse (fun h => ProjectionElem.noConfusion h)
private theorem rvalCtx_ub {c : CalleeEnv} {ac : Option CapturedMir} {ti : List TraitImplEntry} :
    RvalueEvalResult.ub = RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti) RvalueEvalResult.ub := rfl

private theorem rvalCtx_unsupported {c : CalleeEnv} {ac : Option CapturedMir} {ti : List TraitImplEntry} :
    RvalueEvalResult.unsupported =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti) RvalueEvalResult.unsupported := rfl

private theorem rvalCtx_ok
    {c : CalleeEnv} {ac : Option CapturedMir} {ti : List TraitImplEntry}
    {v : Value} {l : List LocalSlot} {m₁ m₂ : Memory}
    (h : m₁ = Memory.withCalleeCtx c ac ti m₂) :
    RvalueEvalResult.ok v l m₁ =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti) (RvalueEvalResult.ok v l m₂) :=
  h ▸ rfl


private theorem stepCtx_fail {c : CalleeEnv} {ac : Option CapturedMir} {ti : List TraitImplEntry} {fk : FailureKind} :
    MirStepNode.fail fk = MirStepNode.mapMem (Memory.withCalleeCtx c ac ti) (MirStepNode.fail fk) := rfl

private theorem stepCtx_step
    {c : CalleeEnv} {ac : Option CapturedMir} {ti : List TraitImplEntry} {s₁ s₂ : MachineState}
    (h : s₁ = MachineState.mapMem (Memory.withCalleeCtx c ac ti) s₂) :
    MirStepNode.step s₁ = MirStepNode.mapMem (Memory.withCalleeCtx c ac ti) (MirStepNode.step s₂) :=
  h ▸ rfl

/-- Apply a memory transformer to the memory of a `FrameWriteResult`. -/
def FrameWriteResult.mapMem (f : Memory → Memory) : FrameWriteResult → FrameWriteResult
  | .ok l m => .ok l (f m)
  | .ub => .ub
  | .unsupported => .unsupported

/-- Committing a foreign-frame write (`commitForeignFrameLocals`, which updates a saved
frame's locals in `Memory.callStack` or `Memory.callerLocals`) commutes with
`Memory.withCalleeCtx`. -/
theorem commitForeignFrameLocals_withCalleeCtx (c : CalleeEnv) (ac : Option CapturedMir)
    (ti : List TraitImplEntry) (m : Memory) (t : ForeignFrameTarget) (l : List LocalSlot) :
    commitForeignFrameLocals (Memory.withCalleeCtx c ac ti m) t l =
      (commitForeignFrameLocals m t l).map (Memory.withCalleeCtx c ac ti) := by
  cases t with
  | callerReferent _ => rfl
  | savedFrame idx _ =>
    unfold commitForeignFrameLocals
    dsimp only [Memory.withCalleeCtx]
    cases get? m.callStack idx with
    | none => rfl
    | some sf =>
      dsimp only
      cases set? m.callStack idx { sf with frame := { sf.frame with locals := l } } <;> rfl

theorem commitForeignFrameLocals_withCalleeCtx' (c : CalleeEnv) (ac : Option CapturedMir)
    (ti : List TraitImplEntry) (m : Memory) (t : ForeignFrameTarget) (l : List LocalSlot) :
    commitForeignFrameLocals { m with callees := c, activeCallee := ac, traitImpls := ti } t l =
      (commitForeignFrameLocals m t l).map (Memory.withCalleeCtx c ac ti) :=
  commitForeignFrameLocals_withCalleeCtx c ac ti m t l

/-- A dereferencing write into a suspended caller frame (`foreignFrameDerefWrite`) reads
and commits `Memory.callStack` / `Memory.callerLocals` only. -/
theorem foreignFrameDerefWrite_withCalleeCtx (c : CalleeEnv) (ac : Option CapturedMir)
    (ti : List TraitImplEntry) (locals₁ : List LocalSlot) (mem₁ : Memory) (dst : Place)
    (restProj : List ProjectionElem) (val : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    foreignFrameDerefWrite locals₁ (Memory.withCalleeCtx c ac ti mem₁) dst restProj val
        localDecls layouts =
      FrameWriteResult.mapMem (Memory.withCalleeCtx c ac ti)
        (foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts) := by
  unfold foreignFrameDerefWrite
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | rfl | split)
  all_goals (
    simp only [commitForeignFrameLocals_withCalleeCtx'] at *
    simp only [*, Option.map] at *
    first
    | (simp at *; done)
    | (simp only [Option.some.injEq] at *; subst_vars; rfl))

theorem foreignFrameDerefWrite_withCalleeCtx' (c : CalleeEnv) (ac : Option CapturedMir)
    (ti : List TraitImplEntry) (locals₁ : List LocalSlot) (m : Memory) (dst : Place)
    (restProj : List ProjectionElem) (val : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    foreignFrameDerefWrite locals₁ { m with callees := c, activeCallee := ac, traitImpls := ti }
        dst restProj val localDecls layouts =
      FrameWriteResult.mapMem (Memory.withCalleeCtx c ac ti)
        (foreignFrameDerefWrite locals₁ m dst restProj val localDecls layouts) :=
  foreignFrameDerefWrite_withCalleeCtx c ac ti locals₁ m dst restProj val localDecls layouts


theorem evalUnsafeFnPointer_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUnsafeFnPointer locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalUnsafeFnPointer locals op targetTy mem localDecls layouts) := by
  unfold evalUnsafeFnPointer
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem deriveStackElemThinPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mem : Memory) (ptrVal : ProvenancePtr)
    (parentEntry : BorrowEntry) (elemCountOpt : Option Nat)
    (ptrBytes : Nat) :
    deriveStackElemThinPtr locals (Memory.withCalleeCtx c ac ti mem)
        ptrVal parentEntry elemCountOpt ptrBytes =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (deriveStackElemThinPtr locals mem ptrVal parentEntry elemCountOpt ptrBytes) := by
  unfold deriveStackElemThinPtr
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalUnsizeCoercion_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUnsizeCoercion locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalUnsizeCoercion locals op targetTy mem localDecls layouts) := by
  unfold evalUnsizeCoercion
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalSliceFatPtrDerefBorrow_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mem : Memory) (parentPtr : ProvenancePtr)
    (ptrSz : Nat) (lenSc : ScalarInt) (restProj : List ProjectionElem)
    (perm : TreeBorrowPerm) (isMut : Bool) (pointeeTyOpt : Option Ty)
    (layouts : LayoutTable) (checkPerm : Bool)
    (localDecls : List LocalDecl) (fullPlaceTyOpt : Option Ty)
    (checkRefElemAlign : Bool) :
    evalSliceFatPtrDerefBorrow locals
        (Memory.withCalleeCtx c ac ti mem)
        parentPtr ptrSz lenSc restProj perm isMut pointeeTyOpt layouts checkPerm
        localDecls fullPlaceTyOpt checkRefElemAlign =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalSliceFatPtrDerefBorrow locals mem
          parentPtr ptrSz lenSc restProj perm isMut pointeeTyOpt layouts checkPerm
          localDecls fullPlaceTyOpt checkRefElemAlign) := by
  unfold evalSliceFatPtrDerefBorrow
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalGlobalThinPtrDerefBorrow_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mem : Memory) (alloc : CapturedAllocation)
    (parentPtr : ProvenancePtr) (ptrSz : Nat) (restProj : List ProjectionElem)
    (isMut : Bool) (pointeeTyOpt : Option Ty) (layouts : LayoutTable)
    (localDecls : List LocalDecl) (rawPtrMode : Bool)
    (fullPlaceTyOpt : Option Ty) :
    evalGlobalThinPtrDerefBorrow locals
        (Memory.withCalleeCtx c ac ti mem)
        alloc parentPtr ptrSz restProj isMut pointeeTyOpt layouts localDecls rawPtrMode
        fullPlaceTyOpt =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalGlobalThinPtrDerefBorrow locals mem
          alloc parentPtr ptrSz restProj isMut pointeeTyOpt layouts localDecls rawPtrMode
          fullPlaceTyOpt) := by
  unfold evalGlobalThinPtrDerefBorrow
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalScalarSliceFatPtrDerefRaw_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mem : Memory) (addrSc lenSc : ScalarInt)
    (restProj : List ProjectionElem) (pointeeTyOpt : Option Ty)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalScalarSliceFatPtrDerefRaw locals
        (Memory.withCalleeCtx c ac ti mem)
        addrSc lenSc restProj pointeeTyOpt localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalScalarSliceFatPtrDerefRaw locals mem
          addrSc lenSc restProj pointeeTyOpt localDecls layouts) := by
  unfold evalScalarSliceFatPtrDerefRaw
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalScalarPtrOffsetBinOp_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp : Operand) (lhs rhs : ScalarInt) :
    evalScalarPtrOffsetBinOp locals₂
        (Memory.withCalleeCtx c ac ti mem)
        localDecls layouts lhsOp lhs rhs =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalScalarPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp lhs rhs) := by
  unfold evalScalarPtrOffsetBinOp
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalPtrOffsetBinOp_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp : Operand) (ptrVal : ProvenancePtr)
    (sz : Nat) (offsetSc : ScalarInt) :
    evalPtrOffsetBinOp locals₂ (Memory.withCalleeCtx c ac ti mem)
        localDecls layouts lhsOp ptrVal sz offsetSc =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp ptrVal sz
          offsetSc) := by
  unfold evalPtrOffsetBinOp ptrAllocByteBound?
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalPlaceLen_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (place : Place) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPlaceLen locals place (Memory.withCalleeCtx c ac ti mem)
        localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalPlaceLen locals place mem localDecls layouts) := by
  unfold evalPlaceLen
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalPlaceDiscriminant_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (val : Value) (locals' : List LocalSlot) (mem : Memory) (place : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPlaceDiscriminant val locals'
        (Memory.withCalleeCtx c ac ti mem) place localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalPlaceDiscriminant val locals' mem place localDecls layouts) := by
  unfold evalPlaceDiscriminant
  dsimp only
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalReifyFnPointer_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (coercionKind : String)
    (h_free : isReifyFnPointerCoercion coercionKind = false ∨
      stringEq coercionKind "UnsafeFnPointer" = true) :
    evalReifyFnPointer locals op targetTy
        (Memory.withCalleeCtx c ac ti mem)
        localDecls layouts coercionKind =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalReifyFnPointer locals op targetTy mem
          localDecls layouts coercionKind) := by
  unfold evalReifyFnPointer
  cases h_r : isReifyFnPointerCoercion coercionKind with
  | false =>
    dsimp only [Memory.withCalleeCtx]
    repeat' (first
      | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl
      | exact evalUnsizeCoercion_withCalleeCtx ..
      | exact deriveStackElemThinPtr_withCalleeCtx ..
      | split)
  | true =>
    cases h_s : stringEq coercionKind "UnsafeFnPointer" with
    | true =>
      exact evalUnsafeFnPointer_withCalleeCtx c ac ti
        locals op targetTy mem localDecls layouts
    | false =>
      exfalso
      rcases h_free with h | h
      · rw [h_r] at h; cases h
      · rw [h_s] at h; cases h

theorem evalFnPtrToPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalFnPtrToPtr locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalFnPtrToPtr locals op targetTy mem localDecls layouts) := by
  unfold evalFnPtrToPtr
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalByteCast_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalByteCast locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalByteCast locals op targetTy mem localDecls layouts) := by
  unfold evalByteCast
  dsimp only [Memory.withCalleeCtx]
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => rfl
  | unsupported => rfl
  | ok v locals' =>
    dsimp only
    repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)
    all_goals try dsimp (config := { zeta := true })
    repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)
    all_goals try rfl

theorem evalSignedDiv_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedDiv a b sz locals (Memory.withCalleeCtx c ac ti mem) =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalSignedDiv a b sz locals mem) := by
  unfold evalSignedDiv
  dsimp only
  cases Bool.and
    (Nat.beq (wrapScalarBits a (scalarModulus sz))
      (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz))
      (Nat.sub (scalarModulus sz) 1)) <;> rfl

theorem evalSignedRem_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedRem a b sz locals (Memory.withCalleeCtx c ac ti mem) =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalSignedRem a b sz locals mem) := by
  unfold evalSignedRem
  dsimp only
  cases Bool.and
    (Nat.beq (wrapScalarBits a (scalarModulus sz))
      (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz))
      (Nat.sub (scalarModulus sz) 1)) <;> rfl

theorem evalScalarBinOp_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (op : BinOp) (lhs rhs : ScalarInt) (locals : List LocalSlot)
    (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp op lhs rhs locals
        (Memory.withCalleeCtx c ac ti mem) isSigned =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalScalarBinOp op lhs rhs locals mem isSigned) := by
  unfold evalScalarBinOp
  cases Nat.beq lhs.sizeBytes 0 with
  | true => rfl
  | false =>
    dsimp only
    cases op <;> dsimp only
    all_goals
      repeat' (first
        | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl
        | exact evalSignedDiv_withCalleeCtx ..
        | exact evalSignedRem_withCalleeCtx ..
        | split)

theorem evalUnaryNot_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    evalUnaryNot sc optTy locals
        (Memory.withCalleeCtx c ac ti mem) =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalUnaryNot sc optTy locals mem) := by
  unfold evalUnaryNot
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalRvalueRefDeref_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (borrowKind : BorrowKind) (place : Place)
    (restProj : List ProjectionElem) (perm : TreeBorrowPerm) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalueRefDeref locals borrowKind place restProj perm
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalRvalueRefDeref locals borrowKind place restProj perm mem localDecls layouts) := by
  dsimp only [evalRvalueRefDeref, Memory.withCalleeCtx]
  repeat' (first
    | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl
    | exact evalSliceFatPtrDerefBorrow_withCalleeCtx ..
    | exact evalGlobalThinPtrDerefBorrow_withCalleeCtx ..
    | split)

theorem evalRvalueRawPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mutability : Mutability) (place : Place)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalueRawPtr locals mutability place
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalRvalueRawPtr locals mutability place mem localDecls layouts) := by
  dsimp only [evalRvalueRawPtr, Memory.withCalleeCtx]
  repeat' (first
    | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl
    | exact evalSliceFatPtrDerefBorrow_withCalleeCtx ..
    | exact evalGlobalThinPtrDerefBorrow_withCalleeCtx ..
    | exact evalScalarSliceFatPtrDerefRaw_withCalleeCtx ..
    | split)

theorem evalCastPtrToPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalCastPtrToPtr locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalCastPtrToPtr locals op targetTy mem localDecls layouts) := by
  dsimp only [evalCastPtrToPtr, Memory.withCalleeCtx]
  repeat' (first
    | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl
    | exact deriveStackElemThinPtr_withCalleeCtx ..
    | split)

theorem evalPointerExposeProvenance_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPointerExposeProvenance locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalPointerExposeProvenance locals op targetTy mem localDecls layouts) := by
  dsimp only [evalPointerExposeProvenance, Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalPointerWithExposedProvenance_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPointerWithExposedProvenance locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalPointerWithExposedProvenance locals op targetTy mem localDecls layouts) := by
  dsimp only [evalPointerWithExposedProvenance, Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalAggregateRawPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (pointeeTy : Ty) (ops : List Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalAggregateRawPtr locals pointeeTy ops
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalAggregateRawPtr locals pointeeTy ops mem localDecls layouts) := by
  dsimp only [evalAggregateRawPtr, Memory.withCalleeCtx]
  repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

theorem evalAggregateAdt_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (defPath : DefPath) (variantIdx : VariantIdx)
    (activeField : Option FieldIdx) (ops : List Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalAggregateAdt locals defPath variantIdx activeField ops
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalAggregateAdt locals defPath variantIdx activeField ops mem localDecls layouts) := by
  unfold evalAggregateAdt
  dsimp only [Memory.withCalleeCtx]
  cases evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => rfl
  | unsupported => rfl
  | ok vals locals' =>
    dsimp only
    repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)

/--
`evalRvalue` is independent of `Memory.activeCallee` and `Memory.traitImpls`, and of
`Memory.callees` whenever `rv` is not a function-pointer reification cast
(`Rvalue.calleeQueryFree`): it commutes with `Memory.withCalleeCtx`.
-/
theorem evalRvalue_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_free : Rvalue.calleeQueryFree rv = true) :
    evalRvalue locals rv (Memory.withCalleeCtx c ac ti mem)
        localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalRvalue locals rv mem localDecls layouts) := by
  cases rv with
  | use op =>
    cases op
    all_goals (dsimp only [evalRvalue, Memory.withCalleeCtx]; repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split))
  | «repeat» op count =>
    cases op
    all_goals (dsimp only [evalRvalue, Memory.withCalleeCtx]; repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split))
  | ref bk place =>
    dsimp only [evalRvalue, Memory.withCalleeCtx]
    repeat' (first
      | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl
      | exact evalRvalueRefDeref_withCalleeCtx ..
      | split)
  | threadLocalRef _ => rfl
  | rawPtr mutab place =>
    exact evalRvalueRawPtr_withCalleeCtx c ac ti locals mutab place mem localDecls layouts
  | len place =>
    dsimp only [evalRvalue]
    exact evalPlaceLen_withCalleeCtx c ac ti locals place mem
      localDecls layouts
  | cast ck op targetTy =>
    cases ck with
    | pointerCoercion ckStr =>
      refine evalReifyFnPointer_withCalleeCtx c ac ti
        locals op targetTy mem localDecls layouts ckStr ?_
      exact Rvalue.calleeQueryFree_pointerCoercion h_free
    | fnPtrToPtr =>
      exact evalFnPtrToPtr_withCalleeCtx c ac ti
        locals op targetTy mem localDecls layouts
    | ptrToPtr =>
      exact evalCastPtrToPtr_withCalleeCtx c ac ti
        locals op targetTy mem localDecls layouts
    | pointerExposeProvenance =>
      exact evalPointerExposeProvenance_withCalleeCtx c ac ti
        locals op targetTy mem localDecls layouts
    | pointerWithExposedProvenance =>
      exact evalPointerWithExposedProvenance_withCalleeCtx c ac ti
        locals op targetTy mem localDecls layouts
    | transmute =>
      exact evalByteCast_withCalleeCtx c ac ti
        locals op targetTy mem localDecls layouts
    | subtype =>
      exact evalByteCast_withCalleeCtx c ac ti
        locals op targetTy mem localDecls layouts
    | _ =>
      dsimp only [evalRvalue, evalFloatCastRvalue, Memory.withCalleeCtx]
      repeat' (first
        | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl
        | split)
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalue, Memory.withCalleeCtx]
    cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | ub => rfl
    | unsupported => rfl
    | ok lhsVal locals₁ =>
      dsimp only
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok rhsVal locals₂ =>
        dsimp only
        cases lhsVal with
        | scalar lhsSc =>
          cases rhsVal with
          | scalar rhsSc =>
            cases op with
            | offset =>
              exact evalScalarPtrOffsetBinOp_withCalleeCtx c ac ti
                locals₂ mem localDecls layouts lhsOp lhsSc rhsSc
            | _ =>
              exact evalScalarBinOp_withCalleeCtx c ac ti
                _ lhsSc rhsSc locals₂ mem _
          | ptr ptrVal sz =>
            cases isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
            | false => rfl
            | true =>
              dsimp only
              cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
              | none => rfl
              | some rhsAddrSc =>
                exact evalScalarBinOp_withCalleeCtx c ac ti op lhsSc rhsAddrSc locals₂ mem false
          | _ => rfl
        | ptr ptrVal sz =>
          cases rhsVal with
          | scalar rhsSc =>
            cases op with
            | offset =>
              exact evalPtrOffsetBinOp_withCalleeCtx c ac ti
                locals₂ mem localDecls layouts lhsOp ptrVal sz rhsSc
            | _ =>
              cases isPtrRelationalBinOp _ localDecls layouts lhsOp rhsOp with
              | false => rfl
              | true =>
                dsimp only
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
                | none => rfl
                | some lhsAddrSc =>
                  exact evalScalarBinOp_withCalleeCtx c ac ti _ lhsAddrSc rhsSc locals₂ mem false
          | ptr rhsPtr rhsSz =>
            cases isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
            | false => rfl
            | true =>
              dsimp only
              cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
              | none =>
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) rhsPtr rhsSz mem.callStack <;> rfl
              | some lhsAddrSc =>
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) rhsPtr rhsSz mem.callStack with
                | none => rfl
                | some rhsAddrSc =>
                  exact evalScalarBinOp_withCalleeCtx c ac ti op lhsAddrSc rhsAddrSc locals₂ mem false
          | _ => rfl
        | aggregate lhsVar lhsFields =>
          cases rhsVal with
          | aggregate rhsVar rhsFields =>
            dsimp only [evalWidePtrAggregateRelBinOp, evalWidePtrRelBinOp]
            repeat' (first
              | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl
              | exact evalScalarBinOp_withCalleeCtx ..
              | split)
          | _ => rfl
        | _ => rfl
  | nullaryOp _ _ => rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalue, Memory.withCalleeCtx]
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok v locals' =>
        cases v with
        | scalar sc =>
          exact evalUnaryNot_withCalleeCtx c ac ti sc _ locals' mem
        | _ => rfl
    | neg =>
      dsimp only [evalRvalue, Memory.withCalleeCtx]
      repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)
    | ptrMetadata =>
      dsimp only [evalRvalue, evalUnaryPtrMetadata, Memory.withCalleeCtx]
      repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)
  | discriminant place =>
    dsimp only [evalRvalue, Memory.withCalleeCtx]
    repeat' (first
      | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl
      | exact evalPlaceDiscriminant_withCalleeCtx ..
      | split)
  | aggregate kind ops =>
    cases kind with
    | rawPtr pointeeTy _ =>
      exact evalAggregateRawPtr_withCalleeCtx c ac ti locals pointeeTy ops mem localDecls layouts
    | adt defPath variantIdx activeField =>
      exact evalAggregateAdt_withCalleeCtx c ac ti locals defPath variantIdx activeField ops mem localDecls layouts
    | _ =>
      dsimp only [evalRvalue, Memory.withCalleeCtx]
      repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)
  | shallowInitBox _ _ => rfl
  | copyForDeref place =>
    dsimp only [evalRvalue, Memory.withCalleeCtx]
    cases evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack <;> repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split)
  | wrapUnsafeBinder op _ =>
    cases op
    all_goals (dsimp only [evalRvalue, Memory.withCalleeCtx]; repeat' (first | exact rvalCtx_ub | exact rvalCtx_unsupported | exact rvalCtx_ok rfl | split))

theorem evalCopySingleDirect_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (locals₃ : List LocalSlot) :
    evalCopySingleDirect
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃ =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalCopySingleDirect
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃) := by
  unfold evalCopySingleDirect
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
  all_goals try dsimp (config := { zeta := true })
  repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
  all_goals try rfl

private def ccCopyWriteDstVal
    (s : MachineState) (locals₃ : List LocalSlot) (dstPlace : Place)
    (dstLoc : Local) (dstTag : Nat) (newVal : Value)
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match writePlaceValue locals₃ s.memory.borrows dstPlace newVal localDecls layouts with
  | .ok locals₄ =>
    let borrows' :=
      invalidateConflictingBorrows s.memory.borrows dstLoc (.some dstTag)
        (length s.memory.callStack)
    MirStepNode.step (advanceStmt s locals₄ { s.memory with borrows := borrows' })
  | .unsupported => MirStepNode.unsupported
  | .ub =>
    match get? locals₃ dstPlace.local_ with
    | .some _ => MirStepNode.fail .ub
    | .none =>
      let callerIdx :=
        match get? s.memory.callerLocals dstPlace.local_ with
        | .some _ => dstPlace.local_
        | .none => Nat.sub dstPlace.local_ (length locals₃)
      let callerWriteRes : PlaceWriteResult :=
        match dstPlace.projection with
        | .nil =>
          match get? s.memory.callerLocals callerIdx with
          | .some .dead => .ub
          | .some _ =>
            match set? s.memory.callerLocals callerIdx (.init newVal) with
            | .some callerLocals' => .ok callerLocals'
            | .none => .ub
          | .none => .ub
        | .deref :: _ => .ub
        | proj :: rest =>
          match get? s.memory.callerLocals callerIdx with
          | .some (.init rootVal) =>
            match writeProjectedValue locals₃ rootVal (proj :: rest) newVal with
            | .ok rootVal' =>
              match set? s.memory.callerLocals callerIdx (.init rootVal') with
              | .some callerLocals' => .ok callerLocals'
              | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
          | _ => .ub
      match callerWriteRes with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callerLocals' =>
        let borrows' := invalidateConflictingBorrows s.memory.borrows dstLoc (.some dstTag) 0
        MirStepNode.step
          (advanceStmt s locals₃
            { s.memory with borrows := borrows', callerLocals := callerLocals' })

private def ccCopyViaBytesBody
    (s : MachineState) (dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) (dstPlace : Place) (dstLocalPlaceTy : Option Ty)
    (dstIsAdt : Bool) (srcSubVal dstSubVal : Value) : MirStepNode :=
  let n := countBits
  let srcStart := srcPtr.offsetBytes
  let dstStart := dstPtr.offsetBytes
  let overlaps :=
    match Nat.beq srcPtr.tag dstPtr.tag with
    | true => true
    | false =>
      match Nat.beq srcEntry.targetLocal dstEntry.targetLocal with
      | false => false
      | true => projectionsOverlap srcEntry.targetProjection dstEntry.targetProjection
  match overlaps with
  | true => MirStepNode.fail .ub
  | false =>
    let srcSliceVal : Option Value :=
      match srcSubVal with
      | .aggregate 0 srcElems =>
        match Nat.ble (Nat.add srcStart n) (length srcElems) with
        | true => .some (.aggregate 0 (takeValues n (dropValues srcStart srcElems)))
        | false =>
          match Nat.beq srcStart 0 with
          | true => .some srcSubVal
          | false => .none
      | _ => .some srcSubVal
    let dstTargetTyOpt : Option Ty :=
      match dstLocalPlaceTy with
      | .some t => .some t
      | .none => operandPointeeTy localDecls layouts dst
    match srcSliceVal with
    | .none => MirStepNode.fail .ub
    | .some sVal =>
      match encodeUntypedValueToBytes defaultCodecFuel sVal with
      | .none => MirStepNode.unsupported
      | .some bs =>
        let spliceBytesToDstArray : Option Value :=
          match Bool.not dstIsAdt, dstSubVal with
          | true, .aggregate 0 dstElems =>
            match Nat.ble (Nat.add dstStart (length bs)) (length dstElems) with
            | false => .none
            | true =>
              match decodeArrayChunksWith
                  (fun chunk => decodeValueFromBytes defaultCodecFuel layouts { kind := .uint .u8, layoutIdx := 0 } chunk)
                  1 (length bs) bs with
              | .some copiedBytes => .some (.aggregate 0 (spliceValues copiedBytes dstStart dstElems))
              | .none => .none
          | _, _ => .none
        let preferSplicedArray : Bool :=
          match dstLocalPlaceTy, dstSubVal with
          | .none, .aggregate 0 _ => true
          | _, _ => false
        match preferSplicedArray, spliceBytesToDstArray with
        | true, .some splicedVal =>
          ccCopyWriteDstVal s locals₃ dstPlace dstEntry.targetLocal dstPtr.tag splicedVal localDecls layouts
        | _, _ =>
          match dstTargetTyOpt with
          | .some dstPt =>
            match rigidTyByteSize layouts dstPt with
            | .some dstBytes =>
              match Nat.beq (length bs) dstBytes with
              | true =>
                match decodeValueFromBytes defaultCodecFuel layouts dstPt bs with
                | .some decodedVal =>
                  ccCopyWriteDstVal s locals₃ dstPlace dstEntry.targetLocal dstPtr.tag decodedVal localDecls layouts
                | .none =>
                  match spliceBytesToDstArray with
                  | .some splicedVal =>
                    ccCopyWriteDstVal s locals₃ dstPlace dstEntry.targetLocal dstPtr.tag splicedVal localDecls layouts
                  | .none => MirStepNode.fail .ub
              | false =>
                match spliceBytesToDstArray with
                | .some splicedVal =>
                  ccCopyWriteDstVal s locals₃ dstPlace dstEntry.targetLocal dstPtr.tag splicedVal localDecls layouts
                | .none => MirStepNode.unsupported
            | .none =>
              match spliceBytesToDstArray with
              | .some splicedVal =>
                ccCopyWriteDstVal s locals₃ dstPlace dstEntry.targetLocal dstPtr.tag splicedVal localDecls layouts
              | .none => MirStepNode.unsupported
          | .none =>
            match spliceBytesToDstArray with
            | .some splicedVal =>
              ccCopyWriteDstVal s locals₃ dstPlace dstEntry.targetLocal dstPtr.tag splicedVal localDecls layouts
            | .none => MirStepNode.fail .ub

private def ccEvalCopyNonOverlappingPermOk
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) : MirStepNode :=
  let n := countBits
  let srcStart := srcPtr.offsetBytes
  let dstStart := dstPtr.offsetBytes
  let srcUnionOpt :=
    resolveUnionEndpoint? localDecls layouts locals₃ srcEntry
  let dstUnionOpt :=
    resolveUnionEndpoint? localDecls layouts locals₃ dstEntry
  let hasUnionEndpoint :=
    match srcUnionOpt, dstUnionOpt with
    | .none, .none => false
    | _, _ => true
  match hasUnionEndpoint with
  | true =>
    evalCopyUnionBytes
      s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
      srcUnionOpt dstUnionOpt n locals₃
  | false =>
    let isSingleDirect :=
      Bool.and (Nat.beq n 1) (Bool.and (Nat.beq srcStart 0) (Nat.beq dstStart 0))
    match isSingleDirect with
    | true =>
      evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃
    | false =>
      let srcRootSlot : Option LocalSlot :=
        match get? locals₃ srcEntry.targetLocal with
        | .some slot => .some slot
        | .none =>
          match get? s.memory.callerLocals srcEntry.targetLocal with
          | .some slot => .some slot
          | .none => get? s.memory.callerLocals (Nat.sub srcEntry.targetLocal (length locals₃))
      let dstRootSlot : Option LocalSlot :=
        match get? locals₃ dstEntry.targetLocal with
        | .some slot => .some slot
        | .none =>
          match get? s.memory.callerLocals dstEntry.targetLocal with
          | .some slot => .some slot
          | .none => get? s.memory.callerLocals (Nat.sub dstEntry.targetLocal (length locals₃))
      match srcRootSlot, dstRootSlot with
      | .some (.init srcRootVal), .some (.init dstRootVal) =>
        let dstPlace : Place := {
          local_ := dstEntry.targetLocal
          projection := dstEntry.targetProjection
        }
        let dstLocalPlaceTy : Option Ty :=
          match get? locals₃ dstPlace.local_ with
          | .some _ => placeTy localDecls layouts dstPlace
          | .none => .none
        let dstIsAdt : Bool :=
          match dstLocalPlaceTy with
          | .some { kind := .adt _ _, .. } => true
          | _ => false
        match readProjectedValue locals₃ srcRootVal srcEntry.targetProjection,
              readProjectedValue locals₃ dstRootVal dstEntry.targetProjection with
        | .ok (.aggregate 0 srcElems), .ok (.aggregate 0 dstElems) =>
          let inBounds :=
            Bool.and (Bool.not dstIsAdt)
              (Bool.and (Nat.ble (Nat.add srcStart n) (length srcElems))
                (Nat.ble (Nat.add dstStart n) (length dstElems)))
          match inBounds with
          | false =>
            match Bool.and (Nat.beq dstStart 0) (Nat.ble (Nat.add srcStart n) (length srcElems)) with
            | true =>
              ccCopyViaBytesBody s dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
                countBits locals₃ dstPlace dstLocalPlaceTy dstIsAdt
                (.aggregate 0 srcElems) (.aggregate 0 dstElems)
            | false => MirStepNode.fail .ub
          | true =>
            let sameContainer :=
              Bool.and (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
                (projectionsOverlap srcEntry.targetProjection dstEntry.targetProjection)
            let disjoint :=
              match Nat.beq srcPtr.tag dstPtr.tag with
              | true => false
              | false =>
                match sameContainer with
                | false => true
                | true =>
                  Bool.or (Nat.ble (Nat.add srcStart n) dstStart)
                    (Nat.ble (Nat.add dstStart n) srcStart)
            match disjoint with
            | false => MirStepNode.fail .ub
            | true =>
              let copiedSlice := takeValues n (dropValues srcStart srcElems)
              let dstElems' := spliceValues copiedSlice dstStart dstElems
              ccCopyWriteDstVal s locals₃ dstPlace dstEntry.targetLocal dstPtr.tag
                (.aggregate 0 dstElems') localDecls layouts
        | .ok srcSubVal, .ok dstSubVal =>
          ccCopyViaBytesBody s dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
            countBits locals₃ dstPlace dstLocalPlaceTy dstIsAdt srcSubVal dstSubVal
        | .ok srcSubVal, .ub =>
          match Nat.beq dstStart 0 with
          | true =>
            ccCopyViaBytesBody s dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
              countBits locals₃ dstPlace dstLocalPlaceTy dstIsAdt srcSubVal .unit
          | false => MirStepNode.fail .ub
        | _, _ => MirStepNode.fail .ub
      | _, _ => MirStepNode.fail .ub

/-- Trusted's `evalCopyNonOverlappingPermOk` is the `cc` mirror (whose union / byte-path
pieces are factored through `ccCopyViaBytesBody` / `ccCopyWriteDstVal`), definitionally. -/
private theorem evalCopyNonOverlappingPermOk_eq_cc
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk s src dst localDecls
        layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃ =
      ccEvalCopyNonOverlappingPermOk s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        countBits locals₃ := by
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk
    ccEvalCopyNonOverlappingPermOk
  rfl

private theorem copyWriteDstVal_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals₃ : List LocalSlot) (dstPlace : Place)
    (dstLoc : Local) (dstTag : Nat) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    ccCopyWriteDstVal (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals₃ dstPlace dstLoc dstTag newVal localDecls layouts =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (ccCopyWriteDstVal s locals₃ dstPlace dstLoc dstTag newVal localDecls layouts) := by
  unfold ccCopyWriteDstVal
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)

private theorem copyViaBytesBody_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) (dstPlace : Place) (dstLocalPlaceTy : Option Ty)
    (dstIsAdt : Bool) (srcSubVal dstSubVal : Value) :
    ccCopyViaBytesBody (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits
        locals₃ dstPlace dstLocalPlaceTy dstIsAdt srcSubVal dstSubVal =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (ccCopyViaBytesBody s dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
          countBits locals₃ dstPlace dstLocalPlaceTy dstIsAdt srcSubVal dstSubVal) := by
  unfold ccCopyViaBytesBody
  dsimp only
  repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | exact copyWriteDstVal_withCalleeCtx .. | split)

private theorem evalCopyUnionBytes_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo)
    (n : Nat) (locals₃ : List LocalSlot) :
    evalCopyUnionBytes
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃ =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalCopyUnionBytes
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
          srcUnionOpt dstUnionOpt n locals₃) := by
  unfold evalCopyUnionBytes
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | exact copyWriteDstVal_withCalleeCtx .. | split)

private theorem evalCopyNonOverlappingPermOk_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    ccEvalCopyNonOverlappingPermOk
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃ =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (ccEvalCopyNonOverlappingPermOk
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold ccEvalCopyNonOverlappingPermOk
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first
    | exact stepCtx_fail | exact stepCtx_step rfl
    | exact evalCopyUnionBytes_withCalleeCtx ..
    | exact evalCopySingleDirect_withCalleeCtx ..
    | exact copyViaBytesBody_withCalleeCtx ..
    | exact copyWriteDstVal_withCalleeCtx ..
    | split)

private theorem evalCopyNonOverlappingPermOk_trusted_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃ =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  rw [evalCopyNonOverlappingPermOk_eq_cc, evalCopyNonOverlappingPermOk_eq_cc]
  exact evalCopyNonOverlappingPermOk_withCalleeCtx c ac ti
    s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃

/-- The frame-qualified single-element copy into or out of a suspended caller frame
(`evalForeignFrameCopySingleDirect`) reads and writes `Memory.callStack` /
`Memory.callerLocals` only, so it commutes with `Memory.withCalleeCtx`. -/
private theorem evalForeignFrameCopySingleDirect_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    evalForeignFrameCopySingleDirect
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃ =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalForeignFrameCopySingleDirect
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold evalForeignFrameCopySingleDirect
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)

theorem evalCopyNonOverlappingWithCount_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingWithCount
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcVal dstVal countBits locals₃ =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalCopyNonOverlappingWithCount
          s src dst localDecls layouts srcVal dstVal countBits locals₃) := by
  unfold evalCopyNonOverlappingWithCount
  cases Nat.beq countBits 0 with
  | true => rfl
  | false =>
    cases srcVal with
    | ptr srcPtr _ =>
      cases dstVal with
      | ptr dstPtr _ =>
        dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
        cases lookupBorrow s.memory.borrows srcPtr.tag with
        | none => rfl
        | some srcEntry =>
          cases lookupBorrow s.memory.borrows dstPtr.tag with
          | none => rfl
          | some dstEntry =>
            dsimp only
            cases srcEntry.perm <;> cases dstEntry.perm <;>
              cases copyEntriesTargetActiveFrame s.memory.callStack srcEntry dstEntry <;>
              first
              | rfl
              | exact evalCopyNonOverlappingPermOk_trusted_withCalleeCtx c ac ti
                  s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃
              | exact evalForeignFrameCopySingleDirect_withCalleeCtx c ac ti
                  s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃
      | _ => rfl
    | _ => rfl

theorem evalCopyNonOverlapping_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst count : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalCopyNonOverlapping
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst count localDecls layouts =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalCopyNonOverlapping s src dst count localDecls layouts) := by
  unfold evalCopyNonOverlapping
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  cases evalOperand s.frame.locals src s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
  | ub => rfl
  | unsupported => rfl
  | ok srcVal locals₁ =>
    dsimp only
    cases evalOperand locals₁ dst s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
    | ub => rfl
    | unsupported => rfl
    | ok dstVal locals₂ =>
      dsimp only
      cases evalOperand locals₂ count s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok countVal locals₃ =>
        cases countVal with
        | scalar countSc =>
          exact evalCopyNonOverlappingWithCount_withCalleeCtx
            c ac ti s src dst localDecls layouts
            srcVal dstVal countSc.bits locals₃
        | _ => rfl

/-- `evalSetDiscriminantLocal` reads only the active frame, borrows, and protectors. -/
theorem evalSetDiscriminantLocal_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (loc : Local) (variantIdx : Nat) (fields : List Value) :
    evalSetDiscriminantLocal (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        loc variantIdx fields =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalSetDiscriminantLocal s loc variantIdx fields) := by
  unfold evalSetDiscriminantLocal
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)

/-- A dereferencing write into a suspended caller frame (`evalForeignFrameDerefWrite`)
reads and commits `Memory.callStack` / `Memory.callerLocals` only. -/
theorem evalForeignFrameDerefWrite_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals₁ : List LocalSlot) (mem₁ : Memory) (dst : Place)
    (restProj : List ProjectionElem) (val : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalForeignFrameDerefWrite (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals₁ (Memory.withCalleeCtx c ac ti mem₁) dst restProj val localDecls layouts =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts) := by
  unfold evalForeignFrameDerefWrite
  rw [foreignFrameDerefWrite_withCalleeCtx]
  cases foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts <;> rfl

/-- The dereferencing `SetDiscriminant` write (`evalSetDiscriminantDerefWrite`). -/
theorem evalSetDiscriminantDerefWrite_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals₁ : List LocalSlot) (p : Place)
    (rest : List ProjectionElem) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalSetDiscriminantDerefWrite (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals₁ p rest newVal localDecls layouts =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalSetDiscriminantDerefWrite s locals₁ p rest newVal localDecls layouts) := by
  unfold evalSetDiscriminantDerefWrite
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first
    | exact stepCtx_fail | exact stepCtx_step rfl
    | exact evalForeignFrameDerefWrite_withCalleeCtx c ac ti s locals₁ s.memory p rest newVal
        localDecls layouts
    | split)

/--
`evalStmt` is independent of `Memory.activeCallee`, `Memory.traitImpls`, and (for
`Statement.calleeQueryFree` statements) `Memory.callees`: it commutes with
`Memory.withCalleeCtx c ac ti` for every replacement triple.
-/
theorem evalStmt_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_free : Statement.calleeQueryFree stmt = true) :
    evalStmt (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        stmt localDecls layouts =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | nop => rfl
  | coverage => rfl
  | constEvalCounter => rfl
  | placeMention p =>
    unfold evalStmt
    dsimp only [MachineState.mapMem]
    repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
  | retag rk p =>
    unfold evalStmt evalFnEntryRetag evalNonFnEntryRetag
    dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
    repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
  | storageLive loc =>
    unfold evalStmt
    dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
    repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
  | storageDead loc =>
    unfold evalStmt
    dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
    repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
  | deinit p =>
    unfold evalStmt
    dsimp only [MachineState.mapMem]
    repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
  | intrinsic intr =>
    cases intr with
    | assume op =>
      unfold evalStmt
      dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
      repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
    | copyNonOverlapping src dst count =>
      exact evalCopyNonOverlapping_withCalleeCtx c ac ti
        s src dst count localDecls layouts
  | setDiscriminant p variantIdx =>
    unfold evalStmt
    dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
    repeat' (first
      | exact stepCtx_fail | exact stepCtx_step rfl
      | exact evalSetDiscriminantLocal_withCalleeCtx c ac ti s _ _ _
      | exact evalSetDiscriminantDerefWrite_withCalleeCtx c ac ti s _ _ _ _ localDecls layouts
      | split)
  | assign dst rv =>
    rw [ccEvalStmt_assign_eq, ccEvalStmt_assign_eq]
    dsimp only [MachineState.mapMem]
    rw [evalRvalue_withCalleeCtx c ac ti
      s.frame.locals rv s.memory localDecls layouts h_free]
    cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | ub => rfl
    | unsupported => rfl
    | ok val locals₁ mem₁ =>
      dsimp only [RvalueEvalResult.mapMem, Memory.withCalleeCtx]
      rcases dst with ⟨dstLoc, dstProj⟩
      cases dstProj with
      | nil =>
        unfold ccEvalAssignDst
        dsimp only [Memory.withCalleeCtx]
        repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
      | cons hd tl =>
        cases ccProjIsDeref hd with
        | isTrue h_d =>
          subst h_d
          unfold ccEvalAssignDst
          dsimp only [Memory.withCalleeCtx]
          repeat' (first
            | exact stepCtx_fail | exact stepCtx_step rfl
            | exact evalForeignFrameDerefWrite_withCalleeCtx c ac ti s _ mem₁ _ _ _ localDecls
                layouts
            | split)
        | isFalse h_d =>
          rw [ccEvalAssignDst_nonDeref _ _ _ _ _ _ _ _ _ h_d,
              ccEvalAssignDst_nonDeref _ _ _ _ _ _ _ _ _ h_d]
          unfold ccEvalAssignNonDeref
          dsimp only [Memory.withCalleeCtx]
          repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
  | _ => rfl

/-! ### Generic `mapMem` algebra -/

@[simp]
theorem MachineState.mapMem_frame (f : Memory → Memory) (s : MachineState) :
    (MachineState.mapMem f s).frame = s.frame := rfl

@[simp]
theorem MachineState.mapMem_memory (f : Memory → Memory) (s : MachineState) :
    (MachineState.mapMem f s).memory = f s.memory := rfl

theorem MirOutcome.mapMem_comp (f g : Memory → Memory) (out : MirOutcome) :
    MirOutcome.mapMem g (MirOutcome.mapMem f out) = MirOutcome.mapMem (g ∘ f) out := by
  rcases out with ⟨v, m⟩ | _ | _ <;> rfl

theorem MirExecState.mapMem_comp (f g : Memory → Memory) (st : MirExecState) :
    MirExecState.mapMem g (MirExecState.mapMem f st) = MirExecState.mapMem (g ∘ f) st := by
  cases st with
  | running s => rfl
  | halted out => exact congrArg MirExecState.halted (MirOutcome.mapMem_comp f g out)
  | faulted fk => rfl

theorem MirStepNode.mapMem_comp (f g : Memory → Memory) (n : MirStepNode) :
    MirStepNode.mapMem g (MirStepNode.mapMem f n) = MirStepNode.mapMem (g ∘ f) n := by
  cases n with
  | ret out => exact congrArg Trusted.ITree.ITreeF.ret (MirOutcome.mapMem_comp f g out)
  | tau st => exact congrArg Trusted.ITree.ITreeF.tau (MirExecState.mapMem_comp f g st)
  | vis e k =>
    rcases e with fk | obs | ⟨req⟩
    · rfl
    · simp only [MirStepNode.mapMem, MirExecState.mapMem_comp]
    · rfl

/-- On successor states, `withCalleeCtx c₂ ac ti` after `withCalleeCtx c ac ti` is
`withCallees c₂` after `withCalleeCtx c ac ti`. -/
theorem Memory.withCallees_comp_withCalleeCtx (c c₂ : CalleeEnv) (ac : Option CapturedMir)
    (ti : List TraitImplEntry) :
    Memory.withCallees c₂ ∘ Memory.withCalleeCtx c ac ti =
      Memory.withCalleeCtx c₂ ac ti ∘ Memory.withCalleeCtx c ac ti := rfl

/-- `MachineState.mapMem (Memory.withCallees c₂) s` is the `withCalleeCtx` replacement
that keeps `s`'s own active callee and call stack. -/
theorem MachineState.withCallees_eq_withCalleeCtx (c₂ : CalleeEnv) (s : MachineState) :
    MachineState.mapMem (Memory.withCallees c₂) s =
      MachineState.mapMem
        (Memory.withCalleeCtx c₂ s.memory.activeCallee s.memory.traitImpls) s := rfl

/-- The identity replacement. -/
theorem MachineState.withCalleeCtx_self (s : MachineState) :
    MachineState.mapMem
        (Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls) s =
      s := rfl

/--
**Statement frame preservation**: a `Statement.calleeQueryFree` statement never changes
`Memory.callees`, `Memory.activeCallee`, or `Memory.traitImpls` in any successor. (It may
update a suspended caller frame's `frame.locals` through a dereferencing write, but never a
saved frame's body: `evalStmt_callerBodies`.)
-/
theorem evalStmt_calleeCtx_preserved (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_free : Statement.calleeQueryFree stmt = true) :
    evalStmt s stmt localDecls layouts =
      MirStepNode.mapMem
        (Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls)
        (evalStmt s stmt localDecls layouts) := by
  have h := evalStmt_withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls
    s stmt localDecls layouts h_free
  rw [MachineState.withCalleeCtx_self] at h
  exact h

/-- **Statement narrowing**: `evalStmt` commutes with `Memory.withCallees c₂` on
`Statement.calleeQueryFree` statements, for every replacement table `c₂`. -/
theorem evalStmt_withCallees (c₂ : CalleeEnv) (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_free : Statement.calleeQueryFree stmt = true) :
    evalStmt (MachineState.mapMem (Memory.withCallees c₂) s) stmt localDecls layouts =
      MirStepNode.mapMem (Memory.withCallees c₂) (evalStmt s stmt localDecls layouts) := by
  rw [MachineState.withCallees_eq_withCalleeCtx,
    evalStmt_withCalleeCtx _ _ _ s stmt localDecls layouts h_free,
    evalStmt_calleeCtx_preserved s stmt localDecls layouts h_free,
    MirStepNode.mapMem_comp, MirStepNode.mapMem_comp, Memory.withCallees_comp_withCalleeCtx]

/-! ### Callee-table agreement (`calleesAgreeOn`) -/

/--
**Callee-table agreement on a call cone.** `c₁` and `c₂` agree on `cone` when
`findCallee?` returns the same body for every definition path in `cone`. Because
`findCallee?` returns the *first* entry whose `defPath` matches, agreement is stated on
the lookup result itself: duplicate entries in either table are resolved by first-match
semantics on both sides, so a shadowed duplicate can neither break nor fake agreement
(`calleesAgreeOn_dup_shadow_witness` in the test suite).
-/
def calleesAgreeOn (cone : List DefPath) (c₁ c₂ : CalleeEnv) : Prop :=
  ∀ dp, dp ∈ cone → findCallee? c₁ dp = findCallee? c₂ dp

theorem calleesAgreeOn.refl (cone : List DefPath) (c : CalleeEnv) : calleesAgreeOn cone c c :=
  fun _ _ => rfl

theorem calleesAgreeOn.symm {cone : List DefPath} {c₁ c₂ : CalleeEnv}
    (h : calleesAgreeOn cone c₁ c₂) : calleesAgreeOn cone c₂ c₁ :=
  fun dp hdp => (h dp hdp).symm

theorem calleesAgreeOn.trans {cone : List DefPath} {c₁ c₂ c₃ : CalleeEnv}
    (h₁₂ : calleesAgreeOn cone c₁ c₂) (h₂₃ : calleesAgreeOn cone c₂ c₃) :
    calleesAgreeOn cone c₁ c₃ :=
  fun dp hdp => (h₁₂ dp hdp).trans (h₂₃ dp hdp)

theorem calleesAgreeOn.mono {cone cone' : List DefPath} {c₁ c₂ : CalleeEnv}
    (h : calleesAgreeOn cone c₁ c₂) (hsub : ∀ dp, dp ∈ cone' → dp ∈ cone) :
    calleesAgreeOn cone' c₁ c₂ :=
  fun dp hdp => h dp (hsub dp hdp)

/-- Monomorphic `lookupCallee` depends on the callee table only through `findCallee?`. -/
theorem lookupCallee_nil_eq_of_findCallee_eq {c₁ c₂ : CalleeEnv} {dp : DefPath}
    (L : LayoutTable) (ti : List TraitImplEntry)
    (h : findCallee? c₁ dp = findCallee? c₂ dp) :
    lookupCallee c₁ L dp [] ti = lookupCallee c₂ L dp [] ti := by
  have hr : resolveCalleeBodyAndArgs? c₁ dp [] ti = resolveCalleeBodyAndArgs? c₂ dp [] ti := by
    unfold resolveCalleeBodyAndArgs?
    dsimp only
    rw [h]
  unfold lookupCallee
  rw [hr]

/-- Monomorphic `checkCalleeSig` (`typeArgs = []`) depends on the callee table only through
`findCallee?`, including when either table is empty (`[]`). -/
theorem checkCalleeSig_nil_eq_of_findCallee_eq {c₁ c₂ : CalleeEnv} {dp : DefPath}
    (fnInputs : List RigidTy) (fnOutput : RigidTy) (fnAbi : CallConv)
    (ti : List TraitImplEntry)
    (h : findCallee? c₁ dp = findCallee? c₂ dp) :
    checkCalleeSig c₁ dp fnInputs fnOutput fnAbi [] ti =
      checkCalleeSig c₂ dp fnInputs fnOutput fnAbi [] ti := by
  cases c₁ with
  | nil =>
    cases c₂ with
    | nil => rfl
    | cons b₂ r₂ =>
      have h₂ : findCallee? (b₂ :: r₂) dp = none := h.symm
      unfold checkCalleeSig resolveCalleeBodyAndArgs?
      dsimp only
      rw [h₂]
  | cons b₁ r₁ =>
    cases c₂ with
    | nil =>
      have h₁ : findCallee? (b₁ :: r₁) dp = none := h
      unfold checkCalleeSig resolveCalleeBodyAndArgs?
      dsimp only
      rw [h₁]
    | cons b₂ r₂ =>
      unfold checkCalleeSig resolveCalleeBodyAndArgs?
      dsimp only
      rw [h]

/-- When no `TraitImplEntry` in `ti` targets `dp` (`hasTraitImplForDefPath ti dp = false`),
`collectMatchingTraitImpls` leaves `acc` unchanged for every `typeArgs`. -/
theorem collectMatchingTraitImpls_eq_of_no_traitImpl (callees : CalleeEnv) :
    ∀ (ti : List TraitImplEntry) (dp : DefPath) (typeArgs : List RigidTy)
      (acc : List (TraitImplEntry × Option (List RigidTy))),
      hasTraitImplForDefPath ti dp = false →
      collectMatchingTraitImpls callees ti dp typeArgs acc = acc
  | [], _, _, acc, _ => rfl
  | entry :: rest, dp, typeArgs, acc, h => by
    unfold hasTraitImplForDefPath at h
    cases hs : stringEq entry.traitRef.defPath dp with
    | true => rw [hs] at h; cases h
    | false =>
      rw [hs] at h
      unfold collectMatchingTraitImpls
      rw [if_neg (by rw [hs]; decide)]
      exact collectMatchingTraitImpls_eq_of_no_traitImpl callees rest dp typeArgs acc h

/-- When no `TraitImplEntry` in `ti ++ flatMapTraitImpls c` targets `dp`,
`resolveCalleeBodyAndArgs? c dp typeArgs ti` reduces to `findCallee? c dp` for *every*
`typeArgs : List RigidTy` (both monomorphic `[]` and polymorphic `firstArg :: restArgs`). -/
theorem resolveCalleeBodyAndArgs?_eq_of_no_traitImpl (c : CalleeEnv) (dp : DefPath)
    (typeArgs : List RigidTy) (ti : List TraitImplEntry)
    (h_no : hasTraitImplForDefPath (ti ++ flatMapTraitImpls c) dp = false) :
    resolveCalleeBodyAndArgs? c dp typeArgs ti =
      match findCallee? c dp with
      | some b => some (b, typeArgs)
      | none => none := by
  cases typeArgs with
  | nil => rfl
  | cons firstArg restArgs =>
    have h_col := collectMatchingTraitImpls_eq_of_no_traitImpl c (ti ++ flatMapTraitImpls c)
      dp (firstArg :: restArgs) [] h_no
    cases firstArg <;> (
      unfold resolveCalleeBodyAndArgs?
      dsimp only
      try rw [h_col]
      try dsimp only
      cases findCallee? c dp with
      | none => rfl
      | some b =>
        dsimp only
        rw [h_no]
        try rfl)

/-- Polymorphic `lookupCallee` (`typeArgs` arbitrary) depends on `c₁` and `c₂` only through
`findCallee?` whenever neither table's trait-impl list registers `dp`. -/
theorem lookupCallee_eq_of_findCallee_eq_of_no_traitImpl {c₁ c₂ : CalleeEnv} {dp : DefPath}
    (L : LayoutTable) (typeArgs : List RigidTy) (ti : List TraitImplEntry)
    (h : findCallee? c₁ dp = findCallee? c₂ dp)
    (h₁ : hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₁) dp = false)
    (h₂ : hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₂) dp = false) :
    lookupCallee c₁ L dp typeArgs ti = lookupCallee c₂ L dp typeArgs ti := by
  unfold lookupCallee
  rw [resolveCalleeBodyAndArgs?_eq_of_no_traitImpl c₁ dp typeArgs ti h₁,
    resolveCalleeBodyAndArgs?_eq_of_no_traitImpl c₂ dp typeArgs ti h₂, h]

/-- Polymorphic `checkCalleeSig` (`typeArgs` arbitrary) depends on `c₁` and `c₂` only through
`findCallee?` (including when either table is `[]`) whenever neither table registers a
`TraitImplEntry` for `dp`. -/
theorem checkCalleeSig_eq_of_findCallee_eq_of_no_traitImpl {c₁ c₂ : CalleeEnv} {dp : DefPath}
    (fnInputs : List RigidTy) (fnOutput : RigidTy) (fnAbi : CallConv)
    (typeArgs : List RigidTy) (ti : List TraitImplEntry)
    (h : findCallee? c₁ dp = findCallee? c₂ dp)
    (h₁ : hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₁) dp = false)
    (h₂ : hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₂) dp = false) :
    checkCalleeSig c₁ dp fnInputs fnOutput fnAbi typeArgs ti =
      checkCalleeSig c₂ dp fnInputs fnOutput fnAbi typeArgs ti := by
  cases c₁ with
  | nil =>
    cases c₂ with
    | nil => rfl
    | cons b₂ r₂ =>
      have hfn : findCallee? (b₂ :: r₂) dp = none := h.symm
      unfold checkCalleeSig
      rw [resolveCalleeBodyAndArgs?_eq_of_no_traitImpl (b₂ :: r₂) dp typeArgs ti h₂, hfn]
  | cons b₁ r₁ =>
    cases c₂ with
    | nil =>
      have hfn : findCallee? (b₁ :: r₁) dp = none := h
      unfold checkCalleeSig
      rw [resolveCalleeBodyAndArgs?_eq_of_no_traitImpl (b₁ :: r₁) dp typeArgs ti h₁, hfn]
    | cons b₂ r₂ =>
      unfold checkCalleeSig
      rw [resolveCalleeBodyAndArgs?_eq_of_no_traitImpl (b₁ :: r₁) dp typeArgs ti h₁,
        resolveCalleeBodyAndArgs?_eq_of_no_traitImpl (b₂ :: r₂) dp typeArgs ti h₂, h]

/-- `internFnPtr` depends only on `Memory.fnPtrs` and `Memory.nextTag`, so it commutes with
`Memory.withCalleeCtx`. -/
theorem internFnPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry := [])
    (mem : Memory) (defPath : DefPath) (typeArgs : List RigidTy) (fnSig : Option RigidTy) :
    internFnPtr (Memory.withCalleeCtx c ac ti mem) defPath typeArgs fnSig =
      let (allocId, mem') := internFnPtr mem defPath typeArgs fnSig
      (allocId, Memory.withCalleeCtx c ac ti mem') := by
  unfold internFnPtr
  dsimp only [Memory.withCalleeCtx]
  cases findFnPtrEntry? mem.fnPtrs defPath typeArgs fnSig <;> rfl

/-- `Option RustIntrinsicKind` predicate excluding `.constEvalSelect` (the only compiler
intrinsic whose dispatch in `evalDirectRustIntrinsic?` consults `Memory.callees` on a
dynamically unpacked runtime callee argument). All 24 other `RustIntrinsicKind` variants execute
inline via `evalNonSelectIntrinsicCall` without touching `Memory.callees`. -/
def isNonSelectIntrinsicOpt : Option RustIntrinsicKind → Bool
  | some .constEvalSelect => false
  | _ => true

theorem isNonSelectIntrinsicOpt_of_eq_none {o : Option RustIntrinsicKind} (h : o = none) :
    isNonSelectIntrinsicOpt o = true := by
  rw [h]; rfl

/-! ### Semantic per-step cone safety -/

/--
Call-target cone condition: every target that `resolveCallTarget` resolves for `func`
(direct constants, function items in locals, *and* indirect calls through reified
function pointers) has its definition path in `cone`, is resolved monomorphically
(`typeArgs = []`, so trait-impl tables are never consulted), and is not
`core::intrinsics::const_eval_select` (`isNonSelectIntrinsicOpt` holds, permitting both
regular callees and all 24 inline non-select compiler intrinsics such as `ub_checks`,
`ctpop`, `bswap`, `size_of_val`, `align_of_val`, `arith_offset`, etc.).
-/
def CallTargetInCone (cone : List DefPath) (s : MachineState) (cur : CapturedMir)
    (func : Operand) (argCount : Nat) : Prop :=
  ∀ target localsAfterFunc,
    resolveCallTarget s func argCount (bodyLocalDeclsOf (some cur)) cur.layouts =
        .ok target localsAfterFunc →
      target.defPath ∈ cone ∧ target.typeArgs = [] ∧
        isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true

/-- Terminator cone condition: only `call` / `tailCall` consult `Memory.callees`. -/
def TermConeSafe (cone : List DefPath) (s : MachineState) (cur : CapturedMir)
    (term : Terminator) : Prop :=
  match term.kind with
  | .call func argOps _ _ _ => CallTargetInCone cone s cur func (length argOps)
  | .tailCall func argOps => CallTargetInCone cone s cur func (length argOps)
  | _ => True

/--
**Semantic step-invariant** at `s`: the instruction that `stepMirFn body s` executes in
the active body is either a `Statement.calleeQueryFree` statement or a terminator whose
call targets all lie in `cone` (`TermConeSafe`).
-/
def StepConeSafe (cone : List DefPath) (body : CapturedMir) (s : MachineState) : Prop :=
  ∀ blk, get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some blk →
    (∀ stmt, get? blk.statements s.frame.stmtIdx = some stmt →
      Statement.calleeQueryFree stmt = true) ∧
    TermConeSafe cone s (s.memory.activeCallee.getD body) blk.terminator

/-! ### Terminator and step bisimulation -/

theorem unwindFromCallStack_withCallees (c : CalleeEnv) :
    ∀ (stk : List SavedCallerFrame) (m : Memory),
      unwindFromCallStack stk (Memory.withCallees c m) =
        MirExecState.mapMem (Memory.withCallees c) (unwindFromCallStack stk m)
  | [], _ => rfl
  | caller :: rest, m => by
    unfold unwindFromCallStack
    dsimp only
    cases caller.returnUnwind with
    | unreachable => rfl
    | terminate => rfl
    | continue_ =>
      exact unwindFromCallStack_withCallees c rest
        { m with
          callStack := rest
          activeCallee := some caller.callerBody
          activeProtectors := restoreCallerProtectors caller }
    | cleanup bb => rfl

theorem applyUnwindAction_withCallees (c : CalleeEnv) (s : MachineState)
    (l : List LocalSlot) (m : Memory) (u : UnwindAction) :
    applyUnwindAction (MachineState.mapMem (Memory.withCallees c) s) l (Memory.withCallees c m) u =
      MirExecState.mapMem (Memory.withCallees c) (applyUnwindAction s l m u) := by
  cases u with
  | unreachable => rfl
  | terminate => rfl
  | continue_ => exact unwindFromCallStack_withCallees c m.callStack m
  | cleanup bb => rfl

private theorem nodeCC_fail {f : Memory → Memory} {fk : FailureKind} :
    MirStepNode.fail fk = MirStepNode.mapMem f (MirStepNode.fail fk) := rfl

private theorem nodeCC_unwind (c : CalleeEnv) (s : MachineState) (l : List LocalSlot)
    (u : UnwindAction) :
    (match applyUnwindAction (MachineState.mapMem (Memory.withCallees c) s) l
        (Memory.withCallees c s.memory) u with
      | .running nextState => MirStepNode.step nextState
      | .halted out => MirStepNode.retOutcome out
      | .faulted fk => MirStepNode.fail fk) =
      MirStepNode.mapMem (Memory.withCallees c)
        (match applyUnwindAction s l s.memory u with
          | .running nextState => MirStepNode.step nextState
          | .halted out => MirStepNode.retOutcome out
          | .faulted fk => MirStepNode.fail fk) := by
  rw [applyUnwindAction_withCallees]
  cases applyUnwindAction s l s.memory u <;> rfl


@[simp] theorem Memory.withCallees_callees (c : CalleeEnv) (m : Memory) :
    (Memory.withCallees c m).callees = c := rfl
@[simp] theorem Memory.withCallees_borrows (c : CalleeEnv) (m : Memory) :
    (Memory.withCallees c m).borrows = m.borrows := rfl
@[simp] theorem Memory.withCallees_globals (c : CalleeEnv) (m : Memory) :
    (Memory.withCallees c m).globals = m.globals := rfl
@[simp] theorem Memory.withCallees_callerLocals (c : CalleeEnv) (m : Memory) :
    (Memory.withCallees c m).callerLocals = m.callerLocals := rfl
@[simp] theorem Memory.withCallees_fnPtrs (c : CalleeEnv) (m : Memory) :
    (Memory.withCallees c m).fnPtrs = m.fnPtrs := rfl
@[simp] theorem Memory.withCallees_traitImpls (c : CalleeEnv) (m : Memory) :
    (Memory.withCallees c m).traitImpls = m.traitImpls := rfl
@[simp] theorem Memory.withCallees_callStack (c : CalleeEnv) (m : Memory) :
    (Memory.withCallees c m).callStack = m.callStack := rfl
@[simp] theorem Memory.withCallees_activeCallee (c : CalleeEnv) (m : Memory) :
    (Memory.withCallees c m).activeCallee = m.activeCallee := rfl
@[simp] theorem Memory.withCallees_activeProtectors (c : CalleeEnv) (m : Memory) :
    (Memory.withCallees c m).activeProtectors = m.activeProtectors := rfl

theorem commitForeignFrameLocals_withCallees (c : CalleeEnv) (m : Memory)
    (t : ForeignFrameTarget) (l : List LocalSlot) :
    commitForeignFrameLocals { m with callees := c } t l =
      (commitForeignFrameLocals m t l).map (Memory.withCallees c) := by
  cases t with
  | callerReferent _ => rfl
  | savedFrame idx _ =>
    unfold commitForeignFrameLocals
    dsimp only
    cases get? m.callStack idx with
    | none => rfl
    | some sf =>
      dsimp only
      cases set? m.callStack idx { sf with frame := { sf.frame with locals := l } } <;> rfl

theorem foreignFrameDerefWrite_withCallees (c : CalleeEnv) (locals₁ : List LocalSlot)
    (mem₁ : Memory) (dst : Place) (restProj : List ProjectionElem) (val : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    foreignFrameDerefWrite locals₁ { mem₁ with callees := c } dst restProj val localDecls layouts =
      FrameWriteResult.mapMem (Memory.withCallees c)
        (foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts) := by
  unfold foreignFrameDerefWrite
  dsimp only
  repeat' (first | rfl | split)
  all_goals (
    simp only [commitForeignFrameLocals_withCallees] at *
    simp only [*, Option.map] at *
    first
    | (simp at *; done)
    | (simp only [Option.some.injEq] at *; subst_vars; rfl))

/-- The caller-frame write of `TerminatorKind.return_` (`writeReturnDestination`) commutes
with `Memory.withCallees`. -/
theorem writeReturnDestination_withCallees (c : CalleeEnv) (callerLocals : List LocalSlot)
    (mem : Memory) (dst : Place) (retVal : Value) (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    writeReturnDestination callerLocals { mem with callees := c } dst retVal localDecls layouts =
      FrameWriteResult.mapMem (Memory.withCallees c)
        (writeReturnDestination callerLocals mem dst retVal localDecls layouts) := by
  unfold writeReturnDestination
  dsimp only
  repeat' (first | rfl | split)
  all_goals (
    try simp only [foreignFrameDerefWrite_withCallees] at *
    try simp only [*, FrameWriteResult.mapMem] at *
    try (simp at *; done)
    try (simp only [FrameWriteResult.ok.injEq] at *
         obtain ⟨h₁, h₂⟩ := ‹_ ∧ _›
         subst_vars
         rfl))

/-- The memory with which `TerminatorKind.return_` resumes `caller` before
`writeReturnDestination`: the returning frame torn down (`disableFrameBorrows`), `caller`
popped, and its protectors restored. -/
def ccReturnCallerMem (s : MachineState) (caller : SavedCallerFrame)
    (restStack : List SavedCallerFrame) : Memory :=
  { s.memory with
    borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack)
      (length s.frame.locals)
    callStack := restStack
    activeCallee := .some caller.callerBody
    activeProtectors := restoreCallerProtectors caller }

/-- `TerminatorKind.return_` arm of `evalTerminator`, with the resumed caller's memory
named by `ccReturnCallerMem` (`ccEvalReturn_eq`). -/
def ccEvalReturn (s : MachineState) : MirStepNode :=
  match get? s.frame.locals 0 with
  | .some (.init retVal) =>
    match hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
        (length s.memory.callStack) (length s.frame.locals) with
    | true => MirStepNode.fail .ub
    | false =>
      match s.memory.callStack with
      | .nil =>
        MirStepNode.retNormal retVal
          { s.memory with
            borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack)
              (length s.frame.locals) }
      | caller :: restStack =>
        match caller.isDiverging with
        | true => MirStepNode.fail .ub
        | false =>
          match writeReturnDestination caller.frame.locals (ccReturnCallerMem s caller restStack)
              caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts with
          | .ok updatedCallerLocals mem' =>
            MirStepNode.step {
              frame := { caller.frame with
                blockIdx := caller.returnTarget, stmtIdx := 0, locals := updatedCallerLocals }
              memory := mem' }
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
  | _ => MirStepNode.fail .ub

theorem ccEvalReturn_eq (s : MachineState) (span : String) (cb : Option CapturedMir) :
    evalTerminator s ⟨.return_, span⟩ cb = ccEvalReturn s := rfl

/-- `writeReturnDestination_withCallees` at the resumed caller's memory: under
`Memory.withCallees c₂` that memory is `{ ccReturnCallerMem s caller restStack with callees := c₂ }`. -/
theorem writeReturnDestination_ccReturnCallerMem_withCallees (c₂ : CalleeEnv) (s : MachineState)
    (caller : SavedCallerFrame) (restStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot) (dst : Place) (retVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    writeReturnDestination callerLocals
        (ccReturnCallerMem (MachineState.mapMem (Memory.withCallees c₂) s) caller restStack)
        dst retVal localDecls layouts =
      FrameWriteResult.mapMem (Memory.withCallees c₂)
        (writeReturnDestination callerLocals (ccReturnCallerMem s caller restStack) dst retVal
          localDecls layouts) :=
  writeReturnDestination_withCallees c₂ callerLocals (ccReturnCallerMem s caller restStack) dst
    retVal localDecls layouts

/-- `TerminatorKind.return_` narrowing: the frame teardown, protector check, and caller
write never consult `Memory.callees`. -/
theorem evalTerminator_return_withCallees (c₂ : CalleeEnv) (s : MachineState) (span : String)
    (cb : Option CapturedMir) :
    evalTerminator (MachineState.mapMem (Memory.withCallees c₂) s) ⟨.return_, span⟩ cb =
      MirStepNode.mapMem (Memory.withCallees c₂) (evalTerminator s ⟨.return_, span⟩ cb) := by
  rw [ccEvalReturn_eq, ccEvalReturn_eq]
  unfold ccEvalReturn
  simp only [writeReturnDestination_ccReturnCallerMem_withCallees]
  dsimp only [MachineState.mapMem, Memory.withCallees]
  repeat' (first | exact nodeCC_fail | rfl | split)
  all_goals (
    try simp only [*, FrameWriteResult.mapMem] at *
    try (simp at *; done)
    try (simp only [FrameWriteResult.ok.injEq] at *
         obtain ⟨h₁, h₂⟩ := ‹_ ∧ _›
         subst_vars
         rfl))

theorem evalDirectRustIntrinsic?_eq_none_of_classify {s : MachineState}
    {currentBody : Option CapturedMir} {target : ResolvedCallTarget}
    {bodyLocalDecls : List LocalDecl} {bodyLayouts : LayoutTable} {argOps : List Operand}
    {argVals : List Value} {locals' : List LocalSlot} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    (h : classifyRustIntrinsic? target.defPath = none) :
    evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts argOps argVals
      locals' destination targetBb unwind = none := by
  unfold evalDirectRustIntrinsic?
  rw [h]

theorem writeIntrinsicReturn_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (retVal : Value) :
    writeIntrinsicReturn (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals' destination targetBb retVal =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (writeIntrinsicReturn s locals' destination targetBb retVal) := by
  unfold writeIntrinsicReturn invalidateDirectDestWriteBorrows
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)
  all_goals (
    simp only [foreignFrameDerefWrite_withCalleeCtx'] at *
    simp only [*, FrameWriteResult.mapMem] at *
    first
    | (simp at *; done)
    | (simp only [FrameWriteResult.ok.injEq] at *
       obtain ⟨h₁, h₂⟩ := ‹_ ∧ _›
       subst_vars
       rfl))

theorem writeIntrinsicScalarResult_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (resOpt : Option ScalarInt) :
    writeIntrinsicScalarResult (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals' destination targetBb resOpt =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (writeIntrinsicScalarResult s locals' destination targetBb resOpt) := by
  cases resOpt with
  | none => rfl
  | some sc =>
    exact writeIntrinsicReturn_withCalleeCtx c ac ti s locals' destination targetBb (.scalar sc)

theorem writeIntrinsicReturn_calleeCtx_preserved
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (retVal : Value) :
    writeIntrinsicReturn s locals' destination targetBb retVal =
      MirStepNode.mapMem
        (Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls)
        (writeIntrinsicReturn s locals' destination targetBb retVal) := by
  have h := writeIntrinsicReturn_withCalleeCtx
    s.memory.callees s.memory.activeCallee s.memory.traitImpls s locals' destination targetBb retVal
  rw [MachineState.withCalleeCtx_self] at h
  exact h

theorem writeIntrinsicReturn_withCallees
    (c₂ : CalleeEnv) (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (retVal : Value) :
    writeIntrinsicReturn (MachineState.mapMem (Memory.withCallees c₂) s)
        locals' destination targetBb retVal =
      MirStepNode.mapMem (Memory.withCallees c₂)
        (writeIntrinsicReturn s locals' destination targetBb retVal) := by
  rw [MachineState.withCallees_eq_withCalleeCtx,
    writeIntrinsicReturn_withCalleeCtx _ _ _ s locals' destination targetBb retVal,
    writeIntrinsicReturn_calleeCtx_preserved s locals' destination targetBb retVal,
    MirStepNode.mapMem_comp, MirStepNode.mapMem_comp, Memory.withCallees_comp_withCalleeCtx]

theorem evalNonSelectIntrinsicCall_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (kind : RustIntrinsicKind) (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall kind (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb) := by
  have hMissing : intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps) := by
    unfold intrinsicMissingPointeeStep
    repeat' (first | exact nodeCC_fail | rfl | split)
  have hUnres : ∀ pt, intrinsicUnresolvedLayoutStep pt =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti) (intrinsicUnresolvedLayoutStep pt) := by
    intro pt
    unfold intrinsicUnresolvedLayoutStep
    repeat' (first | exact nodeCC_fail | rfl | split)
  have hWide : ∀ pt, intrinsicWidePointeeStep pt =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti) (intrinsicWidePointeeStep pt) := by
    intro pt
    unfold intrinsicWidePointeeStep
    repeat' (first | exact nodeCC_fail | rfl | split)
  cases kind with
  | sizeOfVal =>
    rcases argVals with _ | ⟨ptrArgVal, _ | _⟩ <;> try rfl
    unfold evalNonSelectIntrinsicCall
    dsimp only
    cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
    | none =>
      dsimp only
      repeat' (first | exact nodeCC_fail | exact hMissing | rfl | split)
    | some pt =>
      cases pt <;>
        (dsimp only;
         repeat' (first
           | exact nodeCC_fail | exact hMissing | exact hUnres _ | exact hWide _ | rfl
           | exact writeIntrinsicReturn_withCalleeCtx ..
           | exact writeIntrinsicScalarResult_withCalleeCtx ..
           | split))
  | alignOfVal =>
    rcases argVals with _ | ⟨ptrArgVal, _ | _⟩ <;> try rfl
    unfold evalNonSelectIntrinsicCall
    dsimp only
    cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
    | none =>
      dsimp only
      repeat' (first | exact nodeCC_fail | exact hMissing | rfl | split)
    | some pt =>
      cases pt <;>
        (dsimp only;
         repeat' (first
           | exact nodeCC_fail | exact hMissing | exact hUnres _ | exact hWide _ | rfl
           | exact writeIntrinsicReturn_withCalleeCtx ..
           | exact writeIntrinsicScalarResult_withCalleeCtx ..
           | split))
  | _ =>
    dsimp only [evalNonSelectIntrinsicCall]
    repeat' (first
      | exact nodeCC_fail | exact hMissing | exact hUnres _ | exact hWide _ | rfl
      | exact writeIntrinsicReturn_withCalleeCtx ..
      | exact writeIntrinsicScalarResult_withCalleeCtx ..
      | split)

theorem evalNonSelectIntrinsicCall_calleeCtx_preserved
    (kind : RustIntrinsicKind) (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb =
      MirStepNode.mapMem
        (Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls)
        (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb) := by
  have h := evalNonSelectIntrinsicCall_withCalleeCtx
    s.memory.callees s.memory.activeCallee s.memory.traitImpls
    kind s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb
  rw [MachineState.withCalleeCtx_self] at h
  exact h

theorem evalNonSelectIntrinsicCall_withCallees
    (c₂ : CalleeEnv) (kind : RustIntrinsicKind) (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall kind (MachineState.mapMem (Memory.withCallees c₂) s)
        target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb =
      MirStepNode.mapMem (Memory.withCallees c₂)
        (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb) := by
  rw [MachineState.withCallees_eq_withCalleeCtx,
    evalNonSelectIntrinsicCall_withCalleeCtx _ _ _ kind s target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb,
    evalNonSelectIntrinsicCall_calleeCtx_preserved kind s target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb,
    MirStepNode.mapMem_comp, MirStepNode.mapMem_comp, Memory.withCallees_comp_withCalleeCtx]

theorem evalDirectRustIntrinsic?_withCallees_of_nonSelect (c₂ : CalleeEnv)
    (s : MachineState) (currentBody : Option CapturedMir) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (h : isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true) :
    evalDirectRustIntrinsic? (MachineState.mapMem (Memory.withCallees c₂) s) currentBody
        target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb unwind =
      (evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts argOps argVals
        locals' destination targetBb unwind).map (MirStepNode.mapMem (Memory.withCallees c₂)) := by
  unfold evalDirectRustIntrinsic?
  cases h_cl : classifyRustIntrinsic? target.defPath with
  | none => rfl
  | some kind =>
    rw [h_cl] at h
    cases kind with
    | constEvalSelect => cases h
    | _ =>
      dsimp only [Option.map]
      exact congrArg some
        (evalNonSelectIntrinsicCall_withCallees c₂ _ s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)

/--
**Terminator narrowing.** A terminator whose call targets lie in `cone`
(`TermConeSafe`) steps identically under any callee table `c₂` that agrees with
`s.memory.callees` on `cone`, modulo `Memory.withCallees c₂` on every successor state,
outcome, and external-call request.
-/
theorem evalTerminator_withCallees (cone : List DefPath) (c₂ : CalleeEnv) (s : MachineState)
    (term : Terminator) (cur : CapturedMir)
    (h_agree : calleesAgreeOn cone s.memory.callees c₂)
    (h_safe : TermConeSafe cone s cur term) :
    evalTerminator (MachineState.mapMem (Memory.withCallees c₂) s) term (some cur) =
      MirStepNode.mapMem (Memory.withCallees c₂) (evalTerminator s term (some cur)) := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => rfl
  | switchInt discr targets =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
      Memory.withCallees_globals, Memory.withCallees_callerLocals]
    repeat' (first | exact nodeCC_fail | rfl | split)
  | unwindResume =>
    show (match unwindFromCallStack s.memory.callStack (Memory.withCallees c₂ s.memory) with
      | .running nextState => MirStepNode.step nextState
      | .halted out => MirStepNode.retOutcome out
      | .faulted fk => MirStepNode.fail fk) =
      MirStepNode.mapMem (Memory.withCallees c₂)
        (match unwindFromCallStack s.memory.callStack s.memory with
          | .running nextState => MirStepNode.step nextState
          | .halted out => MirStepNode.retOutcome out
          | .faulted fk => MirStepNode.fail fk)
    rw [unwindFromCallStack_withCallees]
    cases unwindFromCallStack s.memory.callStack s.memory <;> rfl
  | unwindTerminate => rfl
  | return_ => exact evalTerminator_return_withCallees c₂ s span (some cur)
  | unreachable => rfl
  | drop place target unwind =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory]
    repeat' (first | exact nodeCC_fail | rfl | split)
  | assert cond expected target unwind =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
      Memory.withCallees_globals, Memory.withCallees_callerLocals]
    repeat' (first
      | exact nodeCC_fail | rfl
      | exact nodeCC_unwind c₂ s _ _
      | split)
  | call func argOps destination target unwind =>
    have hq : CallTargetInCone cone s cur func (length argOps) := h_safe
    cases target with
    | some targetBb =>
      unfold evalTerminator
      dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
        Memory.withCallees_globals, Memory.withCallees_callerLocals, Memory.withCallees_callees,
        Memory.withCallees_traitImpls]
      rw [show resolveCallTarget (MachineState.mapMem (Memory.withCallees c₂) s) func (length argOps)
          (bodyLocalDeclsOf (some cur)) cur.layouts =
        resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts from rfl]
      cases h_res : resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts with
      | ub => rfl
      | unsupported => rfl
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_ta, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
            s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => rfl
        | unsupported => rfl
        | ok argVals locals' =>
          dsimp only
          rw [h_ta, lookupCallee_nil_eq_of_findCallee_eq cur.layouts s.memory.traitImpls
              (h_agree tgt.defPath h_dp).symm,
            evalDirectRustIntrinsic?_withCallees_of_nonSelect c₂ s (some cur) tgt
              (bodyLocalDeclsOf (some cur)) cur.layouts argOps argVals locals' destination
              targetBb unwind h_cl]
          cases evalDirectRustIntrinsic? s (some cur) tgt (bodyLocalDeclsOf (some cur))
              cur.layouts argOps argVals locals' destination targetBb unwind <;>
            repeat' (first
              | exact nodeCC_fail | rfl
              | exact writeIntrinsicReturn_withCallees c₂ s _ _ _ _
              | split)
    | none =>
      unfold evalTerminator
      dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
        Memory.withCallees_globals, Memory.withCallees_callerLocals, Memory.withCallees_callees,
        Memory.withCallees_traitImpls]
      rw [show resolveCallTarget (MachineState.mapMem (Memory.withCallees c₂) s) func (length argOps)
          (bodyLocalDeclsOf (some cur)) cur.layouts =
        resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts from rfl]
      cases h_res : resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts with
      | ub => rfl
      | unsupported => rfl
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_ta, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
            s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => rfl
        | unsupported => rfl
        | ok argVals locals' =>
          dsimp only
          rw [h_ta, lookupCallee_nil_eq_of_findCallee_eq cur.layouts s.memory.traitImpls
              (h_agree tgt.defPath h_dp).symm]
          repeat' (first
            | exact nodeCC_fail | rfl
            | exact nodeCC_unwind c₂ s _ _
            | split)
  | tailCall func argOps =>
    have hq : CallTargetInCone cone s cur func (length argOps) := h_safe
    unfold evalTerminator
    dsimp only
    unfold evalTailCallTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
      Memory.withCallees_globals, Memory.withCallees_callerLocals, Memory.withCallees_callees,
      Memory.withCallees_traitImpls]
    rw [show resolveCallTarget (MachineState.mapMem (Memory.withCallees c₂) s) func (length argOps)
        (bodyLocalDeclsOf (some cur)) cur.layouts =
      resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts from rfl]
    cases h_res : resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts with
    | ub => rfl
    | unsupported => rfl
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, h_ta, h_cl⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
          s.memory.callerLocals (callStack := s.memory.callStack) with
      | ub => rfl
      | unsupported => rfl
      | ok argVals locals' =>
        dsimp only
        rw [h_ta, lookupCallee_nil_eq_of_findCallee_eq cur.layouts s.memory.traitImpls
            (h_agree tgt.defPath h_dp).symm]
        repeat' (first
          | exact nodeCC_fail | rfl
          | split)
  | _ => rfl


/--
**One-step `withCallees` bisimulation** (`stepMirFn`): under `calleesAgreeOn` and the
semantic per-step cone condition `StepConeSafe`, replacing the callee table by `c₂`
commutes with one machine step.
-/
theorem stepMirFn_withCallees (cone : List DefPath) (body : CapturedMir) (s : MachineState)
    (c₂ : CalleeEnv) (h_agree : calleesAgreeOn cone s.memory.callees c₂)
    (h_safe : StepConeSafe cone body s) :
    stepMirFn body (MachineState.mapMem (Memory.withCallees c₂) s) =
      MirStepNode.mapMem (Memory.withCallees c₂) (stepMirFn body s) := by
  unfold stepMirFn
  dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_activeCallee]
  split
  · rfl
  · cases h_bb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => rfl
    | some blk =>
      obtain ⟨h_stmt, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact evalStmt_withCallees c₂ s stmt _ _ (h_stmt stmt h_st)
      | none =>
        dsimp only
        by_cases h_end : (s.frame.stmtIdx == length blk.statements) = true
        · exact (if_pos h_end).trans
            ((evalTerminator_withCallees cone c₂ s blk.terminator _ h_agree h_term).trans
              (congrArg (MirStepNode.mapMem (Memory.withCallees c₂)) (if_pos h_end).symm))
        · conv => rhs; rw [if_neg h_end]
          exact if_neg h_end

/--
**`stepMirState_callees_cone_eq`**: the `MirExecState` form of `stepMirFn_withCallees`.
Executing from `s` with callee table `c₂` produces exactly the `withCallees c₂` image of
the step taken with `s.memory.callees` (successor states, outcomes, and external-call
requests differ only in `Memory.callees`).
-/
theorem stepMirState_callees_cone_eq (cone : List DefPath) (body : CapturedMir)
    (s : MachineState) (c₂ : CalleeEnv) (h_agree : calleesAgreeOn cone s.memory.callees c₂)
    (h_safe : StepConeSafe cone body s) :
    stepMirState body (.running (MachineState.mapMem (Memory.withCallees c₂) s)) =
      MirStepNode.mapMem (Memory.withCallees c₂) (stepMirState body (.running s)) :=
  stepMirFn_withCallees cone body s c₂ h_agree h_safe

/-- A cone-safe step never changes `Memory.callees` in any successor or outcome. -/
theorem stepMirFn_callees_preserved (cone : List DefPath) (body : CapturedMir)
    (s : MachineState) (h_safe : StepConeSafe cone body s) :
    stepMirFn body s = MirStepNode.mapMem (Memory.withCallees s.memory.callees) (stepMirFn body s) :=
  stepMirFn_withCallees cone body s s.memory.callees (calleesAgreeOn.refl _ _) h_safe

private theorem callees_of_running_fixed {c : CalleeEnv} {st : MirExecState} {s' : MachineState}
    (hfix : st = MirExecState.mapMem (Memory.withCallees c) st) (h : st = .running s') :
    s'.memory.callees = c := by
  subst h
  have h2 : s' = MachineState.mapMem (Memory.withCallees c) s' := MirExecState.running.inj hfix
  exact congrArg (fun t : MachineState => t.memory.callees) h2

private theorem tau_fixed {c : CalleeEnv} {st : MirExecState}
    (hfix : (Trusted.ITree.ITreeF.tau st : MirStepNode) =
      MirStepNode.mapMem (Memory.withCallees c) (Trusted.ITree.ITreeF.tau st)) :
    st = MirExecState.mapMem (Memory.withCallees c) st :=
  Trusted.ITree.ITreeF.tau.inj hfix

/-- `wpMirExecSym` one-step unfolding through `evalNodeWP` and the concrete `stepMirState`. -/
theorem wpMirExecSym_succ_eq (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) :
    wpMirExecSym (fuel + 1) body st post =
      evalNodeWP (fun st' => wpMirExecSym fuel body st' post) post (stepMirState body st) := by
  show evalSymNodeTree _ _ _ = _
  rw [evalSymNodeTree_eq, stepMirExecSymTree_eval]

/--
**Semantic step-invariant along an execution** (`ConeReach body P fuel st`): `P` holds at
every `.running` state reached from `st` by the first `fuel` deterministic (`.tau` /
observation) steps of `stepMirState body`. External calls end the obligation: after an
external call, the narrowed and original executions continue from the *same*
answer-supplied state.
-/
def ConeReach (body : CapturedMir) (P : MachineState → Prop) : Nat → MirExecState → Prop
  | 0, _ => True
  | fuel + 1, .running s =>
    P s ∧
      match stepMirFn body s with
      | .tau st' => ConeReach body P fuel st'
      | .vis (.inr (.inl _)) k => ConeReach body P fuel (k PUnit.unit)
      | _ => True
  | _ + 1, .halted _ => True
  | _ + 1, .faulted _ => True

/-- Callee-table agreement of a possibly-halted state. -/
def AgreesAt (cone : List DefPath) (c₂ : CalleeEnv) (st : MirExecState) : Prop :=
  ∀ s, st = .running s → calleesAgreeOn cone s.memory.callees c₂

private theorem agreesAt_succ {cone : List DefPath} {c₂ : CalleeEnv} {s : MachineState}
    {st' : MirExecState} (h_ag : calleesAgreeOn cone s.memory.callees c₂)
    (hfix : st' = MirExecState.mapMem (Memory.withCallees s.memory.callees) st') :
    AgreesAt cone c₂ st' := by
  intro s' hs'
  rw [callees_of_running_fixed hfix hs']
  exact h_ag

/--
**`runMirExecBounded` call-cone narrowing**: along a `ConeReach (StepConeSafe cone body)`
execution, the bounded runner with callee table `c₂` returns exactly the `withCallees c₂`
image of the outcome computed with the original table.
-/
theorem runMirExecBounded_cone_narrow (cone : List DefPath) (body : CapturedMir)
    (c₂ : CalleeEnv) :
    ∀ (fuel : Nat) (st : MirExecState),
      ConeReach body (StepConeSafe cone body) fuel st → AgreesAt cone c₂ st →
      runMirExecBounded fuel body (MirExecState.mapMem (Memory.withCallees c₂) st) =
        (runMirExecBounded fuel body st).map (MirOutcome.mapMem (Memory.withCallees c₂))
  | 0, _, _, _ => rfl
  | _ + 1, .halted _, _, _ => rfl
  | _ + 1, .faulted _, _, _ => rfl
  | fuel + 1, .running s, h_reach, h_agree => by
    have h_ag := h_agree s rfl
    obtain ⟨h_safe, h_next⟩ := h_reach
    have h_step := stepMirFn_withCallees cone body s c₂ h_ag h_safe
    have h_fix := stepMirFn_callees_preserved cone body s h_safe
    show (match stepMirFn body (MachineState.mapMem (Memory.withCallees c₂) s) with
        | .ret out => some out
        | .tau st' => runMirExecBounded fuel body st'
        | .vis (.inr (.inl _)) k => runMirExecBounded fuel body (k PUnit.unit)
        | .vis (.inl _) _ => none
        | .vis (.inr (.inr _)) _ => none) =
      (match stepMirFn body s with
        | .ret out => some out
        | .tau st' => runMirExecBounded fuel body st'
        | .vis (.inr (.inl _)) k => runMirExecBounded fuel body (k PUnit.unit)
        | .vis (.inl _) _ => none
        | .vis (.inr (.inr _)) _ => none).map (MirOutcome.mapMem (Memory.withCallees c₂))
    rw [h_step]
    revert h_next h_fix
    cases stepMirFn body s with
    | ret out => intro _ _; rfl
    | tau st' =>
      intro h_next h_fix
      exact runMirExecBounded_cone_narrow cone body c₂ fuel st' h_next
        (agreesAt_succ h_ag (tau_fixed h_fix))
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _ _; rfl
      · intro h_next h_fix
        have hk : k PUnit.unit =
            MirExecState.mapMem (Memory.withCallees s.memory.callees) (k PUnit.unit) :=
          congrFun (eq_of_heq (Trusted.ITree.ITreeF.vis.inj h_fix).2) PUnit.unit
        exact runMirExecBounded_cone_narrow cone body c₂ fuel (k PUnit.unit) h_next
          (agreesAt_succ h_ag hk)
      · intro _ _; rfl

/--
**`wpMirExecSym` call-cone narrowing.** For every postcondition that does not inspect
`Memory.callees`, the fuel-bounded symbolic weakest precondition is invariant under
replacing the callee table by any `c₂` agreeing on `cone`, along a
`ConeReach (StepConeSafe cone body)` execution. External calls are demonic in both runs
and resume from the identical answer-supplied state.
-/
theorem wpMirExecSym_cone_narrow (cone : List DefPath) (body : CapturedMir) (c₂ : CalleeEnv)
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out) :
    ∀ (fuel : Nat) (st : MirExecState),
      ConeReach body (StepConeSafe cone body) fuel st → AgreesAt cone c₂ st →
      (wpMirExecSym fuel body (MirExecState.mapMem (Memory.withCallees c₂) st) post ↔
        wpMirExecSym fuel body st post)
  | 0, _, _, _ => Iff.rfl
  | fuel + 1, .halted out, _, _ => by
    rw [wpMirExecSym_succ_eq, wpMirExecSym_succ_eq]
    exact h_post out
  | fuel + 1, .faulted _, _, _ => by
    rw [wpMirExecSym_succ_eq, wpMirExecSym_succ_eq]
    exact Iff.rfl
  | fuel + 1, .running s, h_reach, h_agree => by
    have h_ag := h_agree s rfl
    obtain ⟨h_safe, h_next⟩ := h_reach
    have h_step := stepMirFn_withCallees cone body s c₂ h_ag h_safe
    have h_fix := stepMirFn_callees_preserved cone body s h_safe
    rw [wpMirExecSym_succ_eq, wpMirExecSym_succ_eq]
    show evalNodeWP _ post (stepMirFn body (MachineState.mapMem (Memory.withCallees c₂) s)) ↔
      evalNodeWP _ post (stepMirFn body s)
    rw [h_step]
    revert h_next h_fix
    cases stepMirFn body s with
    | ret out => intro _ _; exact h_post out
    | tau st' =>
      intro h_next h_fix
      exact wpMirExecSym_cone_narrow cone body c₂ post h_post fuel st' h_next
        (agreesAt_succ h_ag (tau_fixed h_fix))
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _ _; exact Iff.rfl
      · intro h_next h_fix
        have hk : k PUnit.unit =
            MirExecState.mapMem (Memory.withCallees s.memory.callees) (k PUnit.unit) :=
          congrFun (eq_of_heq (Trusted.ITree.ITreeF.vis.inj h_fix).2) PUnit.unit
        exact wpMirExecSym_cone_narrow cone body c₂ post h_post fuel (k PUnit.unit) h_next
          (agreesAt_succ h_ag hk)
      · intro _ _; exact Iff.rfl

/--
**`MirWpConverges` call-cone narrowing** for a state whose entire execution is cone-safe.
-/
theorem mirWpConverges_cone_narrow (cone : List DefPath) (body : CapturedMir) (c₂ : CalleeEnv)
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out)
    (s : MachineState)
    (h_reach : ∀ fuel, ConeReach body (StepConeSafe cone body) fuel (.running s))
    (h_agree : calleesAgreeOn cone s.memory.callees c₂) :
    MirWpConverges body (MachineState.mapMem (Memory.withCallees c₂) s) post ↔
      MirWpConverges body s post := by
  have h_at : AgreesAt cone c₂ (.running s) := fun s' hs' => by cases hs'; exact h_agree
  constructor
  · rintro ⟨fuel, h⟩
    exact ⟨fuel,
      (wpMirExecSym_cone_narrow cone body c₂ post h_post fuel (.running s) (h_reach fuel) h_at).1 h⟩
  · rintro ⟨fuel, h⟩
    exact ⟨fuel,
      (wpMirExecSym_cone_narrow cone body c₂ post h_post fuel (.running s) (h_reach fuel) h_at).2 h⟩

/-! ### Entry states and the multi-callee runner -/

/-- The entry state of `body` with callee table `c₂` is the `withCallees c₂` image of the
entry state with any other non-empty table `c₁`. -/
theorem initMachineStateWithMemoryAndCallees_withCallees (body : CapturedMir)
    (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv} (h₁ : c₁ ≠ []) (h₂ : c₂ ≠ []) :
    Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₂ =
      MachineState.mapMem (Memory.withCallees c₂)
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) := by
  cases c₁ with
  | nil => exact absurd rfl h₁
  | cons b₁ r₁ =>
    cases c₂ with
    | nil => exact absurd rfl h₂
    | cons b₂ r₂ => rfl

theorem initMachineStateWithMemoryAndCallees_callees (body : CapturedMir) (args : List Value)
    (mem : Memory) {c : CalleeEnv} (h : c ≠ []) :
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c).memory.callees = c := by
  cases c with
  | nil => exact absurd rfl h
  | cons b r => rfl

/-- Multi-callee bounded runner from `Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c`. -/
def runCfgWithCallees (fuel : Nat) (body : CapturedMir) (args : List Value) (mem : Memory)
    (c : CalleeEnv) : Option MirOutcome :=
  runMirExecBounded fuel body (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c))

/--
**`runCfgWithCallees_cone_narrow`**: running `body` with the narrowed callee table `c₂`
returns exactly the `withCallees c₂` image of the run with `c₁`, whenever `c₁` and `c₂`
agree on `cone` and the `c₁` execution is cone-safe for `fuel` steps.
-/
theorem runCfgWithCallees_cone_narrow (cone : List DefPath) (fuel : Nat) (body : CapturedMir)
    (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv} (h₁ : c₁ ≠ []) (h₂ : c₂ ≠ [])
    (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_reach : ConeReach body (StepConeSafe cone body) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁))) :
    runCfgWithCallees fuel body args mem c₂ =
      (runCfgWithCallees fuel body args mem c₁).map (MirOutcome.mapMem (Memory.withCallees c₂)) := by
  unfold runCfgWithCallees
  rw [initMachineStateWithMemoryAndCallees_withCallees body args mem h₁ h₂]
  refine runMirExecBounded_cone_narrow cone body c₂ fuel _ h_reach ?_
  intro s hs
  cases hs
  rw [initMachineStateWithMemoryAndCallees_callees body args mem h₁]
  exact h_agree

/-- Exact return-value equality: a normal return `(v, m)` with `c₁` is a normal return
`(v, withCallees c₂ m)` with `c₂`. -/
theorem runCfgWithCallees_cone_narrow_normal (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : c₁ ≠ []) (h₂ : c₂ ≠ []) (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_reach : ConeReach body (StepConeSafe cone body) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁)))
    {v : Value} {m : Memory}
    (h_run : runCfgWithCallees fuel body args mem c₁ = some (.normal (v, m))) :
    runCfgWithCallees fuel body args mem c₂ = some (.normal (v, Memory.withCallees c₂ m)) := by
  rw [runCfgWithCallees_cone_narrow cone fuel body args mem h₁ h₂ h_agree h_reach, h_run]
  rfl

/-- **`wpMirExecSym` transfer between entry states** with callee tables `c₁` and `c₂`. -/
theorem wpMirExecSym_cone_narrow_init (cone : List DefPath) (fuel : Nat) (body : CapturedMir)
    (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv} (h₁ : c₁ ≠ []) (h₂ : c₂ ≠ [])
    (h_agree : calleesAgreeOn cone c₁ c₂) (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out)
    (h_reach : ConeReach body (StepConeSafe cone body) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁))) :
    wpMirExecSym fuel body (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₂)) post ↔
      wpMirExecSym fuel body (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁)) post := by
  rw [initMachineStateWithMemoryAndCallees_withCallees body args mem h₁ h₂]
  refine wpMirExecSym_cone_narrow cone body c₂ post h_post fuel _ h_reach ?_
  intro s hs
  cases hs
  rw [initMachineStateWithMemoryAndCallees_callees body args mem h₁]
  exact h_agree

/-- **`MirWpConverges` transfer between entry states** with callee tables `c₁` and `c₂`. -/
theorem mirWpConverges_cone_narrow_init (cone : List DefPath) (body : CapturedMir)
    (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv} (h₁ : c₁ ≠ []) (h₂ : c₂ ≠ [])
    (h_agree : calleesAgreeOn cone c₁ c₂) (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out)
    (h_reach : ∀ fuel, ConeReach body (StepConeSafe cone body) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁))) :
    MirWpConverges body (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₂) post ↔
      MirWpConverges body (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) post := by
  rw [initMachineStateWithMemoryAndCallees_withCallees body args mem h₁ h₂]
  refine mirWpConverges_cone_narrow cone body c₂ post h_post _ h_reach ?_
  rw [initMachineStateWithMemoryAndCallees_callees body args mem h₁]
  exact h_agree


/-! ### Decidable syntactic call-cone closure (`CallConeClosed`) -/

private theorem coneListByteEq_eq_of_true : ∀ (xs ys : List UInt8),
    Trusted.Rustc.V2026_06_01.MirSemantics.listByteEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | b₁ :: bs₁, b₂ :: bs₂, h => by
    unfold Trusted.Rustc.V2026_06_01.MirSemantics.listByteEq at h
    cases hb : Nat.beq b₁.toBitVec.toNat b₂.toBitVec.toNat with
    | false => rw [hb] at h; nomatch h
    | true =>
      rw [hb] at h
      have hByte : b₁ = b₂ :=
        UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb))
      rw [hByte, coneListByteEq_eq_of_true bs₁ bs₂ h]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

private theorem coneListByteEq_self : ∀ (xs : List UInt8),
    Trusted.Rustc.V2026_06_01.MirSemantics.listByteEq xs xs = true
  | [] => rfl
  | b :: bs => by
    simp [Trusted.Rustc.V2026_06_01.MirSemantics.listByteEq, coneListByteEq_self bs]

/-- Trusted `stringEq` decides `String` equality (used by `findCallee?`). -/
theorem coneStringEq_iff {a b : String} : stringEq a b = true ↔ a = b := by
  constructor
  · intro h
    unfold stringEq at h
    exact String.toByteArray_inj.mp
      (ByteArray.ext (Array.toList_inj.mp (coneListByteEq_eq_of_true _ _ h)))
  · rintro rfl
    unfold stringEq
    exact coneListByteEq_self _

/-- Decidable cone membership through trusted `stringEq`. -/
def inCone (cone : List DefPath) (dp : DefPath) : Bool :=
  cone.any (fun d => stringEq d dp)

theorem inCone_iff {cone : List DefPath} {dp : DefPath} : inCone cone dp = true ↔ dp ∈ cone := by
  unfold inCone
  rw [List.any_eq_true]
  constructor
  · rintro ⟨d, hd, h⟩
    rw [coneStringEq_iff.mp h] at hd
    exact hd
  · intro h
    exact ⟨dp, h, coneStringEq_iff.mpr rfl⟩

/-- `findCallee?` returns a member of the table whose `defPath` is the queried path. -/
theorem findCallee?_spec : ∀ {c : CalleeEnv} {dp : DefPath} {b : CapturedMir},
    findCallee? c dp = some b → b ∈ c ∧ b.defPath = dp
  | [], _, _, h => nomatch h
  | b' :: rest, dp, b, h => by
    unfold findCallee? at h
    cases hs : stringEq b'.defPath dp with
    | true =>
      rw [hs] at h
      cases h
      exact ⟨List.Mem.head _, coneStringEq_iff.mp hs⟩
    | false =>
      rw [hs] at h
      obtain ⟨hm, hd⟩ := findCallee?_spec h
      exact ⟨List.Mem.tail _ hm, hd⟩

/-- Monomorphic `lookupCallee` results are `findCallee?` results. -/
theorem lookupCallee_nil_eq_some {c : CalleeEnv} {L : LayoutTable} {dp : DefPath}
    {ti : List TraitImplEntry} {b : CapturedMir}
    (h : lookupCallee c L dp [] ti = some b) : findCallee? c dp = some b := by
  unfold lookupCallee resolveCalleeBodyAndArgs? at h
  dsimp only at h
  cases hf : findCallee? c dp with
  | none => rw [hf] at h; cases h
  | some b' =>
    rw [hf] at h
    dsimp only at h
    by_cases h0 : b'.typeParamCount = 0
    · have h1 : (b'.typeParamCount == 0 && ([] : List RigidTy).isEmpty) = true := by
        rw [h0]; rfl
      rw [if_pos h1] at h
      exact h
    · have h1 : ¬ (b'.typeParamCount == 0 && ([] : List RigidTy).isEmpty) = true := by
        intro hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact h0 hc.1
      have h2 : (([] : List RigidTy).length != b'.typeParamCount) = true := by
        simp only [List.length_nil, bne_iff_ne, ne_eq]
        exact fun hc => h0 hc.symm
      rw [if_neg h1, if_pos h2] at h
      cases h

/-- Callee bodies whose `defPath` lies in `cone` (in table order, duplicates kept). -/
def coneBodies (cone : List DefPath) (c₁ : CalleeEnv) : CalleeEnv :=
  c₁.filter (fun b => inCone cone b.defPath)

theorem findCallee?_coneBodies {cone : List DefPath} :
    ∀ (c₁ : CalleeEnv) {dp : DefPath}, dp ∈ cone →
      findCallee? (coneBodies cone c₁) dp = findCallee? c₁ dp
  | [], _, _ => rfl
  | b :: rest, dp, hdp => by
    by_cases hb : inCone cone b.defPath = true
    · have hf : coneBodies cone (b :: rest) = b :: coneBodies cone rest := by
        unfold coneBodies
        simp only [List.filter_cons, hb, ↓reduceIte]
      rw [hf]
      unfold findCallee?
      cases stringEq b.defPath dp with
      | true => rfl
      | false => exact findCallee?_coneBodies rest hdp
    · have hf : coneBodies cone (b :: rest) = coneBodies cone rest := by
        unfold coneBodies
        simp only [List.filter_cons, hb, ↓reduceIte, Bool.false_eq_true]
      have hs : stringEq b.defPath dp = false := by
        cases hs : stringEq b.defPath dp with
        | false => rfl
        | true => exact absurd (inCone_iff.mpr ((coneStringEq_iff.mp hs) ▸ hdp)) hb
      rw [hf, findCallee?_coneBodies rest hdp]
      conv => rhs; unfold findCallee?
      rw [hs]

/--
**Canonical narrowing.** Restricting a callee table to the bodies whose `defPath` lies in
`cone` always agrees with it on `cone`, including in the presence of duplicate entries
(first-match `findCallee?` semantics are preserved by `List.filter`).
-/
theorem calleesAgreeOn_coneBodies (cone : List DefPath) (c₁ : CalleeEnv) :
    calleesAgreeOn cone c₁ (coneBodies cone c₁) :=
  fun _ hdp => (findCallee?_coneBodies c₁ hdp).symm

/-- `hasTraitImplForDefPath` distributes over `++`. -/
theorem hasTraitImplForDefPath_append (xs ys : List TraitImplEntry) (dp : DefPath) :
    hasTraitImplForDefPath (xs ++ ys) dp =
      (hasTraitImplForDefPath xs dp || hasTraitImplForDefPath ys dp) := by
  induction xs with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.cons_append, hasTraitImplForDefPath]
    cases stringEq e.traitRef.defPath dp with
    | true => rfl
    | false => exact ih

/-- Filtering a callee table via `coneBodies` never introduces a `TraitImplEntry` for `dp`. -/
theorem hasTraitImplForDefPath_flatMapTraitImpls_coneBodies (cone : List DefPath) :
    ∀ (c₁ : CalleeEnv) (dp : DefPath),
      hasTraitImplForDefPath (flatMapTraitImpls c₁) dp = false →
      hasTraitImplForDefPath (flatMapTraitImpls (coneBodies cone c₁)) dp = false
  | [], _, _ => rfl
  | b :: rest, dp, h => by
    unfold flatMapTraitImpls at h
    rw [hasTraitImplForDefPath_append, Bool.or_eq_false_iff] at h
    have ih := hasTraitImplForDefPath_flatMapTraitImpls_coneBodies cone rest dp h.2
    by_cases hb : inCone cone b.defPath = true
    · have hf : coneBodies cone (b :: rest) = b :: coneBodies cone rest := by
        unfold coneBodies
        simp only [List.filter_cons, hb, ↓reduceIte]
      rw [hf]
      unfold flatMapTraitImpls
      rw [hasTraitImplForDefPath_append, h.1, ih]
      rfl
    · have hf : coneBodies cone (b :: rest) = coneBodies cone rest := by
        unfold coneBodies
        simp only [List.filter_cons, hb, ↓reduceIte, Bool.false_eq_true]
      rw [hf]
      exact ih

/--
A call operand accepted by `CallConeClosed`: a direct constant function item whose
monomorphic (`typeArgs = []`), non-`constEvalSelect` definition path lies in `cone`
(including inline non-select compiler intrinsics such as `ub_checks`, `ctpop`, `bswap`,
`size_of_val`, `align_of_val`, `arith_offset`, etc.). Every other callee operand
(function pointers, function items held in locals, generic or trait-dispatched calls, or
`core::intrinsics::const_eval_select`) fails closed.
-/
def directCallInCone (cone : List DefPath) (func : Operand) : Bool :=
  match extractCalleeDefPath? func with
  | some dp =>
    inCone cone dp && (extractCalleeTypeArgs func).isEmpty &&
      isNonSelectIntrinsicOpt (classifyRustIntrinsic? dp)
  | none => false

/-- Terminator check: only `call` / `tailCall` are constrained. -/
def termCallsInCone (cone : List DefPath) (term : Terminator) : Bool :=
  match term.kind with
  | .call func _ _ _ _ => directCallInCone cone func
  | .tailCall func _ => directCallInCone cone func
  | _ => true

/-- Body check: every statement is `calleeQueryFree` and every call stays in `cone`. -/
def bodyCallsInCone (cone : List DefPath) (b : CapturedMir) : Bool :=
  b.basicBlocks.all (fun blk =>
    blk.statements.all Statement.calleeQueryFree && termCallsInCone cone blk.terminator)

/--
**Decidable syntactic call-cone closure.** `CallConeClosed cone root c₁` checks the root
body and every body of `c₁` whose `defPath` lies in `cone`: no function-pointer
reification casts, and every `call` / `tailCall` is a direct, monomorphic, non-intrinsic
call to a definition path in `cone`. It fails closed on any call whose target could be
resolved at runtime (indirect / fn-pointer / fn-item local / trait / intrinsic).
-/
def CallConeClosed (cone : List DefPath) (root : CapturedMir) (c₁ : CalleeEnv) : Bool :=
  bodyCallsInCone cone root && (coneBodies cone c₁).all (bodyCallsInCone cone)

/-- `b` is the root body or one of the `cone` bodies of `c₁`. -/
def InConeSet (cone : List DefPath) (root : CapturedMir) (c₁ : CalleeEnv) (b : CapturedMir) :
    Prop :=
  b = root ∨ b ∈ coneBodies cone c₁

/-- Reachable-state invariant of a cone-closed execution from the entry state. -/
def ClosedInv (cone : List DefPath) (root : CapturedMir) (c₁ : CalleeEnv) (s : MachineState) :
    Prop :=
  s.memory.callees = c₁ ∧ InConeSet cone root c₁ (s.memory.activeCallee.getD root) ∧
    ∀ f, f ∈ s.memory.callStack → InConeSet cone root c₁ f.callerBody

/-- Every `.tau` / observation `.running` successor of `n` satisfies `P`. -/
def NodeSuccs (P : MachineState → Prop) : MirStepNode → Prop
  | .tau (.running s') => P s'
  | .vis (.inr (.inl _)) k =>
    match k PUnit.unit with
    | .running s' => P s'
    | _ => True
  | _ => True

private theorem mem_of_get? {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : get? xs i = some x) : x ∈ xs := by
  unfold get? at h
  exact List.mem_of_getElem? h

theorem bodyCallsInCone_of_inConeSet {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {b : CapturedMir} (h_closed : CallConeClosed cone root c₁ = true)
    (hb : InConeSet cone root c₁ b) : bodyCallsInCone cone b = true := by
  unfold CallConeClosed at h_closed
  rw [Bool.and_eq_true] at h_closed
  rcases hb with rfl | hb
  · exact h_closed.1
  · exact List.all_eq_true.mp h_closed.2 b hb

theorem callTargetInCone_of_directCallInCone {cone : List DefPath} {s : MachineState}
    {cur : CapturedMir} {func : Operand} {n : Nat} (h : directCallInCone cone func = true) :
    CallTargetInCone cone s cur func n := by
  intro target l h_res
  unfold directCallInCone at h
  cases h_dp : extractCalleeDefPath? func with
  | none => rw [h_dp] at h; cases h
  | some dp =>
    rw [h_dp] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h_in, h_ta⟩, h_cl⟩ := h
    have h_eq : resolveCallTarget s func n (bodyLocalDeclsOf (some cur)) cur.layouts =
        .ok { defPath := dp, typeArgs := extractCalleeTypeArgs func, fnSig := none,
              isIndirect := false } s.frame.locals := by
      unfold resolveCallTarget
      rw [h_dp]
    rw [h_eq] at h_res
    cases h_res
    exact ⟨inCone_iff.mp h_in, List.isEmpty_iff.mp h_ta, h_cl⟩

theorem termConeSafe_of_termCallsInCone {cone : List DefPath} {s : MachineState}
    {cur : CapturedMir} {term : Terminator} (h : termCallsInCone cone term = true) :
    TermConeSafe cone s cur term := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | call func argOps destination target unwind =>
    exact callTargetInCone_of_directCallInCone h
  | tailCall func argOps =>
    exact callTargetInCone_of_directCallInCone h
  | _ => trivial

/-- `CallConeClosed` and the reachable-state invariant give the semantic step-invariant. -/
theorem stepConeSafe_of_closedInv {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {s : MachineState} (h_closed : CallConeClosed cone root c₁ = true)
    (h_inv : ClosedInv cone root c₁ s) : StepConeSafe cone root s := by
  intro blk h_bb
  have h_body := bodyCallsInCone_of_inConeSet h_closed h_inv.2.1
  unfold bodyCallsInCone at h_body
  have h_blk := List.all_eq_true.mp h_body blk (mem_of_get? h_bb)
  rw [Bool.and_eq_true] at h_blk
  exact ⟨fun stmt h_st => List.all_eq_true.mp h_blk.1 stmt (mem_of_get? h_st),
    termConeSafe_of_termCallsInCone h_blk.2⟩

theorem nodeSuccs_of_fixed {P : MachineState → Prop} {g : Memory → Memory} {n : MirStepNode}
    (hfix : n = MirStepNode.mapMem g n)
    (hP : ∀ s', s' = MachineState.mapMem g s' → P s') : NodeSuccs P n := by
  cases n with
  | ret _ => trivial
  | tau st =>
    cases st with
    | running s' => exact hP s' (MirExecState.running.inj (Trusted.ITree.ITreeF.tau.inj hfix))
    | halted _ => trivial
    | faulted _ => trivial
  | vis e k =>
    rcases e with fk | obs | ⟨req⟩
    · trivial
    · have hk : k PUnit.unit = MirExecState.mapMem g (k PUnit.unit) :=
        congrFun (eq_of_heq (Trusted.ITree.ITreeF.vis.inj hfix).2) PUnit.unit
      show (match k PUnit.unit with
        | .running s' => P s'
        | _ => True)
      revert hk
      cases k PUnit.unit with
      | running s' => intro hk; exact hP s' (MirExecState.running.inj hk)
      | halted _ => intro _; trivial
      | faulted _ => intro _; trivial
    · trivial

/--
`cs'` keeps the `callerBody` of every saved frame of `cs`, in order. Statements, intrinsic
result writes, and the caller write of `TerminatorKind.return_` may update a suspended
frame's `frame.locals` (`commitForeignFrameLocals` / `writeFrameLocalSlot`, a
dereferencing write through a pointer into a caller frame) but never its body.
-/
def CallerBodiesEq (cs cs' : List SavedCallerFrame) : Prop :=
  cs'.map SavedCallerFrame.callerBody = cs.map SavedCallerFrame.callerBody

theorem CallerBodiesEq.mem {cs cs' : List SavedCallerFrame} (h : CallerBodiesEq cs cs')
    {f : SavedCallerFrame} (hf : f ∈ cs') : ∃ f₀, f₀ ∈ cs ∧ f₀.callerBody = f.callerBody := by
  have hm : f.callerBody ∈ cs'.map SavedCallerFrame.callerBody := List.mem_map.mpr ⟨f, hf, rfl⟩
  unfold CallerBodiesEq at h
  rw [h] at hm
  exact List.mem_map.mp hm

/-! ## Statements and intrinsic / return writes keep every saved caller body

Statement evaluation, inline intrinsic calls, and the return-destination write change the
call stack only through `commitForeignFrameLocals` / `writeFrameLocalSlot`, which rewrite a
saved frame's `frame.locals` and nothing else: every saved `callerBody` is unchanged. -/

theorem CallerBodiesEq.refl (cs : List SavedCallerFrame) : CallerBodiesEq cs cs := rfl

theorem CallerBodiesEq.trans {a b c : List SavedCallerFrame} (h₁ : CallerBodiesEq a b)
    (h₂ : CallerBodiesEq b c) : CallerBodiesEq a c :=
  Eq.trans h₂ h₁

theorem CallerBodiesEq.of_eq {cs cs' : List SavedCallerFrame} (h : cs' = cs) :
    CallerBodiesEq cs cs' :=
  h ▸ rfl

private theorem ns_fail {P : MachineState → Prop} {fk : FailureKind} :
    NodeSuccs P (MirStepNode.fail fk) := trivial

private theorem ns_unsupported {P : MachineState → Prop} :
    NodeSuccs P MirStepNode.unsupported := trivial

private theorem ns_step {P : MachineState → Prop} {st : MachineState} (h : P st) :
    NodeSuccs P (MirStepNode.step st) := h

/-- Replacing a saved frame by one with the same `callerBody` keeps the caller bodies. -/
private theorem callerBodiesEq_set {xs ys : List SavedCallerFrame} {i : Nat}
    {sf y : SavedCallerFrame} (hget : get? xs i = some sf) (hset : set? xs i y = some ys)
    (hy : y.callerBody = sf.callerBody) : CallerBodiesEq xs ys := by
  unfold set? at hset
  unfold get? at hget
  split at hset
  · rename_i hlt
    cases hset
    unfold CallerBodiesEq
    rw [List.map_set]
    have hx : xs[i] = sf := by
      rw [List.getElem?_eq_getElem hlt] at hget
      exact Option.some.inj hget
    have hlt' : i < (xs.map SavedCallerFrame.callerBody).length := by simpa using hlt
    have hmi : (xs.map SavedCallerFrame.callerBody)[i]'hlt' = y.callerBody := by
      rw [List.getElem_map, hx, hy]
    rw [← hmi, List.set_getElem_self]
  · cases hset

theorem commitForeignFrameLocals_callerBodies {mem mem' : Memory} {target : ForeignFrameTarget}
    {locals' : List LocalSlot} (h : commitForeignFrameLocals mem target locals' = some mem') :
    CallerBodiesEq mem.callStack mem'.callStack := by
  unfold commitForeignFrameLocals at h
  split at h
  · cases h
    exact CallerBodiesEq.refl _
  · split at h
    · rename_i sf hget
      split at h
      · rename_i cs' hset
        cases h
        exact callerBodiesEq_set hget hset rfl
      · cases h
    · cases h

theorem writeFrameLocalSlot_callerBodies {locals locals' : List LocalSlot}
    {cs cs' : List SavedCallerFrame} {cl cl' : List LocalSlot} {d loc : Nat} {slot : LocalSlot}
    (h : writeFrameLocalSlot locals cs cl d loc slot = some (locals', cs', cl')) :
    CallerBodiesEq cs cs' := by
  unfold writeFrameLocalSlot at h
  split at h
  · split at h
    · cases h
      exact CallerBodiesEq.refl _
    · cases h
  · split at h
    · split at h
      · rename_i frameLocals' sf _ hget
        split at h
        · rename_i cs'' hset
          cases h
          exact callerBodiesEq_set hget hset rfl
        · cases h
      · cases h
    · split at h
      · cases h
        exact CallerBodiesEq.refl _
      · cases h
    · cases h

private theorem commitForeignFrameLocals_callerBodies' {mem mem₂ : Memory}
    {target : ForeignFrameTarget} {locals' : List LocalSlot} {cs : List SavedCallerFrame}
    (h : commitForeignFrameLocals mem target locals' = some mem₂) (hcs : cs = mem₂.callStack) :
    CallerBodiesEq mem.callStack cs :=
  hcs ▸ commitForeignFrameLocals_callerBodies h

theorem foreignFrameDerefWrite_callerBodies {locals₁ locals₂ : List LocalSlot}
    {mem₁ mem₂ : Memory} {dst : Place} {restProj : List ProjectionElem} {val : Value}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h : foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts =
      .ok locals₂ mem₂) :
    CallerBodiesEq mem₁.callStack mem₂.callStack := by
  unfold foreignFrameDerefWrite at h
  repeat' (first
    | (cases h; done)
    | (cases h; exact commitForeignFrameLocals_callerBodies' (by assumption) (by rfl))
    | split at h
    | (dsimp only at h))

/-- **The return-destination write keeps every saved caller body.** -/
theorem writeReturnDestination_callerBodies {callerLocals : List LocalSlot} {mem : Memory}
    {dst : Place} {retVal : Value} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {locals' : List LocalSlot} {mem' : Memory}
    (h : writeReturnDestination callerLocals mem dst retVal localDecls layouts = .ok locals' mem') :
    CallerBodiesEq mem.callStack mem'.callStack := by
  unfold writeReturnDestination at h
  repeat' (first
    | (cases h; done)
    | (cases h; exact CallerBodiesEq.refl _)
    | exact foreignFrameDerefWrite_callerBodies h
    | split at h
    | (dsimp only at h))

/-! ### `evalRvalue` never changes the call stack -/

/-- `r` can only succeed with a memory whose call stack is `cs`. -/
def RvCS (cs : List SavedCallerFrame) : RvalueEvalResult → Prop
  | .ok _ _ m => m.callStack = cs
  | _ => True

private theorem rvCS_ub {cs : List SavedCallerFrame} : RvCS cs .ub := trivial

private theorem rvCS_unsupported {cs : List SavedCallerFrame} : RvCS cs .unsupported := trivial

private theorem rvCS_ok {cs : List SavedCallerFrame} {v : Value} {l : List LocalSlot}
    {m : Memory} (h : m.callStack = cs) : RvCS cs (.ok v l m) := h

theorem RvCS.callStack_eq {cs : List SavedCallerFrame} {r : RvalueEvalResult} (h : RvCS cs r)
    {v : Value} {l : List LocalSlot} {m : Memory} (hr : r = .ok v l m) : m.callStack = cs := by
  subst hr
  exact h

theorem evalUnsafeFnPointer_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalUnsafeFnPointer locals op targetTy mem localDecls layouts) := by
  unfold evalUnsafeFnPointer
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem deriveStackElemThinPtr_rvCS (locals : List LocalSlot) (mem : Memory)
    (ptrVal : ProvenancePtr) (parentEntry : BorrowEntry) (elemCountOpt : Option Nat)
    (ptrBytes : Nat) :
    RvCS mem.callStack
      (deriveStackElemThinPtr locals mem ptrVal parentEntry elemCountOpt ptrBytes) := by
  unfold deriveStackElemThinPtr
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalUnsizeCoercion_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalUnsizeCoercion locals op targetTy mem localDecls layouts) := by
  unfold evalUnsizeCoercion
  repeat' (first
    | extract_lets
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl))
  all_goals (try dsimp +zetaDelta only)
  all_goals repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalSliceFatPtrDerefBorrow_rvCS (locals : List LocalSlot) (mem : Memory)
    (parentPtr : ProvenancePtr) (ptrSz : Nat) (lenSc : ScalarInt)
    (restProj : List ProjectionElem) (perm : TreeBorrowPerm) (isMut : Bool)
    (pointeeTyOpt : Option Ty) (layouts : LayoutTable) (checkPerm : Bool)
    (localDecls : List LocalDecl) (accessedTyOpt : Option Ty) (checkResultRefAlign : Bool) :
    RvCS mem.callStack
      (evalSliceFatPtrDerefBorrow locals mem parentPtr ptrSz lenSc restProj perm isMut
        pointeeTyOpt layouts checkPerm localDecls accessedTyOpt checkResultRefAlign) := by
  unfold evalSliceFatPtrDerefBorrow
  repeat' (first
    | extract_lets
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl))
  all_goals (try dsimp +zetaDelta only)
  all_goals repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalGlobalThinPtrDerefBorrow_rvCS (locals : List LocalSlot) (mem : Memory)
    (alloc : CapturedAllocation) (parentPtr : ProvenancePtr) (ptrSz : Nat)
    (restProj : List ProjectionElem) (isMut : Bool) (pointeeTyOpt : Option Ty)
    (layouts : LayoutTable) (localDecls : List LocalDecl) (rawPtrMode : Bool)
    (accessedTyOpt : Option Ty) :
    RvCS mem.callStack
      (evalGlobalThinPtrDerefBorrow locals mem alloc parentPtr ptrSz restProj isMut
        pointeeTyOpt layouts localDecls rawPtrMode accessedTyOpt) := by
  unfold evalGlobalThinPtrDerefBorrow
  repeat' (first
    | extract_lets
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl))
  all_goals (try dsimp +zetaDelta only)
  all_goals repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalScalarSliceFatPtrDerefRaw_rvCS (locals : List LocalSlot) (mem : Memory)
    (addrSc lenSc : ScalarInt) (restProj : List ProjectionElem) (pointeeTyOpt : Option Ty)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalScalarSliceFatPtrDerefRaw locals mem addrSc lenSc restProj pointeeTyOpt localDecls
        layouts) := by
  unfold evalScalarSliceFatPtrDerefRaw
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalScalarPtrOffsetBinOp_rvCS (locals₂ : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (lhsOp : Operand)
    (lhs rhs : ScalarInt) :
    RvCS mem.callStack
      (evalScalarPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp lhs rhs) := by
  unfold evalScalarPtrOffsetBinOp
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalPtrOffsetBinOp_rvCS (locals₂ : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (lhsOp : Operand)
    (ptrVal : ProvenancePtr) (sz : Nat) (offsetSc : ScalarInt) :
    RvCS mem.callStack
      (evalPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc) := by
  unfold evalPtrOffsetBinOp
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalPlaceLen_rvCS (locals : List LocalSlot) (place : Place) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalPlaceLen locals place mem localDecls layouts) := by
  unfold evalPlaceLen
  repeat' (first
    | extract_lets
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl))
  all_goals (try dsimp +zetaDelta only)
  all_goals repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalPlaceDiscriminant_rvCS (val : Value) (locals' : List LocalSlot) (mem : Memory)
    (place : Place) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalPlaceDiscriminant val locals' mem place localDecls layouts) := by
  unfold evalPlaceDiscriminant
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem internFnPtr_callStack (mem : Memory) (defPath : DefPath) (typeArgs : List RigidTy)
    (fnSig : Option RigidTy) : (internFnPtr mem defPath typeArgs fnSig).2.callStack =
      mem.callStack := by
  unfold internFnPtr
  split <;> rfl

private theorem internFnPtr_callStack' {mem mem' : Memory} {defPath : DefPath}
    {typeArgs : List RigidTy} {fnSig : Option RigidTy} {a : AllocId}
    (h : internFnPtr mem defPath typeArgs fnSig = (a, mem')) : mem'.callStack = mem.callStack := by
  have := internFnPtr_callStack mem defPath typeArgs fnSig
  rw [h] at this
  exact this

theorem evalReifyFnPointer_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (coercionKind : String) :
    RvCS mem.callStack
      (evalReifyFnPointer locals op targetTy mem localDecls layouts coercionKind) := by
  unfold evalReifyFnPointer
  repeat' (first
    | split
    | with_reducible (first
      | exact rvCS_ub
      | exact rvCS_unsupported
      | exact rvCS_ok rfl
      | exact evalUnsizeCoercion_rvCS ..
      | exact deriveStackElemThinPtr_rvCS ..
      | exact evalUnsafeFnPointer_rvCS ..
      | exact rvCS_ok (internFnPtr_callStack' (by assumption)))
    | (dsimp only))

theorem evalFnPtrToPtr_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalFnPtrToPtr locals op targetTy mem localDecls layouts) := by
  unfold evalFnPtrToPtr
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalByteCast_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalByteCast locals op targetTy mem localDecls layouts) := by
  unfold evalByteCast
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))
  all_goals try dsimp (config := { zeta := true })
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalSignedDiv_rvCS (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    RvCS mem.callStack (evalSignedDiv a b sz locals mem) := by
  unfold evalSignedDiv
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalSignedRem_rvCS (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    RvCS mem.callStack (evalSignedRem a b sz locals mem) := by
  unfold evalSignedRem
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalScalarBinOp_rvCS (op : BinOp) (lhs rhs : ScalarInt) (locals : List LocalSlot)
    (mem : Memory) (isSigned : Bool) :
    RvCS mem.callStack (evalScalarBinOp op lhs rhs locals mem isSigned) := by
  unfold evalScalarBinOp
  cases Nat.beq lhs.sizeBytes 0 with
  | true => exact rvCS_unsupported
  | false =>
    dsimp only
    cases op <;> dsimp only
    all_goals
      repeat' (first
        | split
        | with_reducible (first
          | exact rvCS_ub
          | exact rvCS_unsupported
          | exact rvCS_ok rfl
          | exact evalSignedDiv_rvCS ..
          | exact evalSignedRem_rvCS ..)
        | (dsimp only))

theorem evalUnaryNot_rvCS (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    RvCS mem.callStack (evalUnaryNot sc optTy locals mem) := by
  unfold evalUnaryNot
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalRvalueRefDeref_rvCS (locals : List LocalSlot) (borrowKind : BorrowKind)
    (place : Place) (restProj : List ProjectionElem) (perm : TreeBorrowPerm) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalRvalueRefDeref locals borrowKind place restProj perm mem localDecls layouts) := by
  unfold evalRvalueRefDeref
  repeat' (first
    | extract_lets
    | split
    | with_reducible (first
      | exact rvCS_ub
      | exact rvCS_unsupported
      | exact rvCS_ok rfl
      | exact evalSliceFatPtrDerefBorrow_rvCS ..
      | exact evalGlobalThinPtrDerefBorrow_rvCS ..))
  all_goals (try dsimp +zetaDelta only)
  all_goals repeat' (first
    | split
    | with_reducible (first
      | exact rvCS_ub
      | exact rvCS_unsupported
      | exact rvCS_ok rfl
      | exact evalSliceFatPtrDerefBorrow_rvCS ..
      | exact evalGlobalThinPtrDerefBorrow_rvCS ..)
    | (dsimp only))

theorem evalRvalueRawPtr_rvCS (locals : List LocalSlot) (mutability : Mutability)
    (place : Place) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalRvalueRawPtr locals mutability place mem localDecls layouts) := by
  unfold evalRvalueRawPtr
  repeat' (first
    | extract_lets
    | split
    | with_reducible (first
      | exact rvCS_ub
      | exact rvCS_unsupported
      | exact rvCS_ok rfl
      | exact evalSliceFatPtrDerefBorrow_rvCS ..
      | exact evalGlobalThinPtrDerefBorrow_rvCS ..
      | exact evalScalarSliceFatPtrDerefRaw_rvCS ..))
  all_goals (try dsimp +zetaDelta only)
  all_goals repeat' (first
    | split
    | with_reducible (first
      | exact rvCS_ub
      | exact rvCS_unsupported
      | exact rvCS_ok rfl
      | exact evalSliceFatPtrDerefBorrow_rvCS ..
      | exact evalGlobalThinPtrDerefBorrow_rvCS ..
      | exact evalScalarSliceFatPtrDerefRaw_rvCS ..)
    | (dsimp only))

theorem evalCastPtrToPtr_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalCastPtrToPtr locals op targetTy mem localDecls layouts) := by
  unfold evalCastPtrToPtr
  repeat' (first
    | split
    | with_reducible (first
      | exact rvCS_ub
      | exact rvCS_unsupported
      | exact rvCS_ok rfl
      | exact deriveStackElemThinPtr_rvCS ..)
    | (dsimp only))

theorem evalPointerExposeProvenance_rvCS (locals : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalPointerExposeProvenance locals op targetTy mem localDecls layouts) := by
  unfold evalPointerExposeProvenance
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalPointerWithExposedProvenance_rvCS (locals : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalPointerWithExposedProvenance locals op targetTy mem localDecls layouts) := by
  unfold evalPointerWithExposedProvenance
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalAggregateRawPtr_rvCS (locals : List LocalSlot) (pointeeTy : Ty)
    (ops : List Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalAggregateRawPtr locals pointeeTy ops mem localDecls layouts) := by
  unfold evalAggregateRawPtr
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalAggregateAdt_rvCS (locals : List LocalSlot) (defPath : DefPath)
    (variantIdx : VariantIdx) (activeField : Option FieldIdx) (ops : List Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalAggregateAdt locals defPath variantIdx activeField ops mem localDecls layouts) := by
  unfold evalAggregateAdt
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalFloatCastRvalue_rvCS (locals : List LocalSlot) (kind : CastKind) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalFloatCastRvalue locals kind op targetTy mem localDecls layouts) := by
  unfold evalFloatCastRvalue
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalUnaryPtrMetadata_rvCS (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalUnaryPtrMetadata locals op mem localDecls layouts) := by
  unfold evalUnaryPtrMetadata
  repeat' (first
    | split
    | with_reducible (first | exact rvCS_ub | exact rvCS_unsupported | exact rvCS_ok rfl)
    | (dsimp only))

theorem evalWidePtrRelBinOp_rvCS (op : BinOp) (lhsThin lhsMeta rhsThin rhsMeta : Value)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (ptrBytes : Nat) :
    RvCS mem.callStack
      (evalWidePtrRelBinOp op lhsThin lhsMeta rhsThin rhsMeta locals₂ mem localDecls layouts
        ptrBytes) := by
  unfold evalWidePtrRelBinOp
  repeat' (first
    | split
    | with_reducible (first
      | exact rvCS_ub
      | exact rvCS_unsupported
      | exact rvCS_ok rfl
      | exact evalScalarBinOp_rvCS ..)
    | (dsimp only))

theorem evalWidePtrAggregateRelBinOp_rvCS (op : BinOp) (lhsOp : Operand) (lhsVar : Nat)
    (lhsFields : List Value) (rhsVar : Nat) (rhsFields : List Value) (locals₂ : List LocalSlot)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalWidePtrAggregateRelBinOp op lhsOp lhsVar lhsFields rhsVar rhsFields locals₂ mem
        localDecls layouts) := by
  unfold evalWidePtrAggregateRelBinOp
  repeat' (first
    | split
    | with_reducible (first
      | exact rvCS_ub
      | exact rvCS_unsupported
      | exact rvCS_ok rfl
      | exact evalWidePtrRelBinOp_rvCS ..
      | exact evalScalarBinOp_rvCS ..)
    | (dsimp only))

/-- `evalRvalue` never changes `Memory.callStack`. -/
theorem evalRvalue_rvCS (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalRvalue locals rv mem localDecls layouts) := by
  unfold evalRvalue
  repeat' (first
    | extract_lets
    | split
    | with_reducible (first
      | exact rvCS_ub
      | exact rvCS_unsupported
      | exact rvCS_ok rfl
      | exact evalRvalueRefDeref_rvCS ..
      | exact evalRvalueRawPtr_rvCS ..
      | exact evalPlaceLen_rvCS ..
      | exact evalReifyFnPointer_rvCS ..
      | exact evalFnPtrToPtr_rvCS ..
      | exact evalCastPtrToPtr_rvCS ..
      | exact evalPointerExposeProvenance_rvCS ..
      | exact evalPointerWithExposedProvenance_rvCS ..
      | exact evalByteCast_rvCS ..
      | exact evalFloatCastRvalue_rvCS ..
      | exact evalScalarPtrOffsetBinOp_rvCS ..
      | exact evalPtrOffsetBinOp_rvCS ..
      | exact evalScalarBinOp_rvCS ..
      | exact evalWidePtrAggregateRelBinOp_rvCS ..
      | exact evalUnaryNot_rvCS ..
      | exact evalUnaryPtrMetadata_rvCS ..
      | exact evalPlaceDiscriminant_rvCS ..
      | exact evalAggregateRawPtr_rvCS ..
      | exact evalAggregateAdt_rvCS ..))
  all_goals (try dsimp +zetaDelta only)
  all_goals repeat' (first
    | split
    | with_reducible (first
      | exact rvCS_ub
      | exact rvCS_unsupported
      | exact rvCS_ok rfl
      | exact evalRvalueRefDeref_rvCS ..
      | exact evalRvalueRawPtr_rvCS ..
      | exact evalPlaceLen_rvCS ..
      | exact evalReifyFnPointer_rvCS ..
      | exact evalFnPtrToPtr_rvCS ..
      | exact evalCastPtrToPtr_rvCS ..
      | exact evalPointerExposeProvenance_rvCS ..
      | exact evalPointerWithExposedProvenance_rvCS ..
      | exact evalByteCast_rvCS ..
      | exact evalFloatCastRvalue_rvCS ..
      | exact evalScalarPtrOffsetBinOp_rvCS ..
      | exact evalPtrOffsetBinOp_rvCS ..
      | exact evalScalarBinOp_rvCS ..
      | exact evalWidePtrAggregateRelBinOp_rvCS ..
      | exact evalUnaryNot_rvCS ..
      | exact evalUnaryPtrMetadata_rvCS ..
      | exact evalPlaceDiscriminant_rvCS ..
      | exact evalAggregateRawPtr_rvCS ..
      | exact evalAggregateAdt_rvCS ..)
    | (dsimp only))

theorem evalRvalue_callStack {locals locals' : List LocalSlot} {rv : Rvalue} {mem mem' : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {v : Value}
    (h : evalRvalue locals rv mem localDecls layouts = .ok v locals' mem') :
    mem'.callStack = mem.callStack :=
  (evalRvalue_rvCS locals rv mem localDecls layouts).callStack_eq h


/-! ### Statement steps, inline intrinsics, and intrinsic return writes -/

private theorem ns_advance {cs : List SavedCallerFrame} {s : MachineState} {l : List LocalSlot}
    {M : Memory} (h : CallerBodiesEq cs M.callStack) :
    NodeSuccs (fun s' => CallerBodiesEq cs s'.memory.callStack)
      (MirStepNode.step (advanceStmt s l M)) := h

private theorem ns_mk {cs : List SavedCallerFrame} {f : StackFrame} {M : Memory}
    (h : CallerBodiesEq cs M.callStack) :
    NodeSuccs (fun s' => CallerBodiesEq cs s'.memory.callStack)
      (MirStepNode.step { frame := f, memory := M }) := h

private theorem cb_of_rvalue {locals locals' : List LocalSlot} {rv : Rvalue} {mem mem' : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {v : Value} {x : List SavedCallerFrame}
    (h : evalRvalue locals rv mem localDecls layouts = .ok v locals' mem')
    (hx : x = mem'.callStack) : CallerBodiesEq mem.callStack x :=
  CallerBodiesEq.of_eq (hx.trans (evalRvalue_callStack h))

private theorem cb_of_writeFrameLocalSlot {locals locals' : List LocalSlot}
    {cs cs' : List SavedCallerFrame} {cl cl' : List LocalSlot} {d loc : Nat} {slot : LocalSlot}
    {x : List SavedCallerFrame}
    (h : writeFrameLocalSlot locals cs cl d loc slot = some (locals', cs', cl'))
    (hx : x = cs') : CallerBodiesEq cs x :=
  hx ▸ writeFrameLocalSlot_callerBodies h

private theorem cb_of_foreignFrameDerefWrite {locals₁ locals₂ : List LocalSlot}
    {mem₁ mem₂ : Memory} {dst : Place} {restProj : List ProjectionElem} {val : Value}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {x : List SavedCallerFrame}
    (h : foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts =
      .ok locals₂ mem₂)
    (hx : x = mem₂.callStack) : CallerBodiesEq mem₁.callStack x :=
  hx ▸ foreignFrameDerefWrite_callerBodies h

theorem invalidateDirectDestWriteBorrows_callStack (mem : Memory) (locals : List LocalSlot)
    (dst : Place) : (invalidateDirectDestWriteBorrows mem locals dst).callStack = mem.callStack := by
  unfold invalidateDirectDestWriteBorrows
  try dsimp only
  repeat' (first | rfl | split)

theorem evalForeignFrameDerefWrite_callerBodies {cs : List SavedCallerFrame} (s : MachineState)
    (locals₁ : List LocalSlot) (mem₁ : Memory) (dst : Place) (restProj : List ProjectionElem)
    (val : Value) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h : CallerBodiesEq cs mem₁.callStack) :
    NodeSuccs (fun s' => CallerBodiesEq cs s'.memory.callStack)
      (evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts) := by
  unfold evalForeignFrameDerefWrite
  split
  · rename_i locals₂ mem₂ hw
    exact ns_step (h.trans (foreignFrameDerefWrite_callerBodies hw))
  · exact ns_fail
  · exact ns_unsupported

theorem evalSetDiscriminantLocal_callerBodies (s : MachineState) (loc : Local)
    (variantIdx : Nat) (fields : List Value) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalSetDiscriminantLocal s loc variantIdx fields) := by
  unfold evalSetDiscriminantLocal
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _))
    | (dsimp only))

theorem evalSetDiscriminantDerefWrite_callerBodies (s : MachineState)
    (locals₁ : List LocalSlot) (p : Place) (rest : List ProjectionElem) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalSetDiscriminantDerefWrite s locals₁ p rest newVal localDecls layouts) := by
  unfold evalSetDiscriminantDerefWrite
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _)
      | exact evalForeignFrameDerefWrite_callerBodies _ _ _ _ _ _ _ _ (CallerBodiesEq.refl _))
    | (dsimp only))

theorem evalFnEntryRetag_callerBodies (s : MachineState) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (place : Place) (ptrVal : ProvenancePtr) (sz : Nat)
    (parentEntry : BorrowEntry) (locals' : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalFnEntryRetag s localDecls layouts place ptrVal sz parentEntry locals') := by
  unfold evalFnEntryRetag
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _))
    | (dsimp only))

theorem evalNonFnEntryRetag_callerBodies (retagKind : RetagKind) (s : MachineState)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place)
    (ptrVal : ProvenancePtr) (sz : Nat) (parentEntry : BorrowEntry) (locals' : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalNonFnEntryRetag retagKind s localDecls layouts place ptrVal sz parentEntry locals') := by
  unfold evalNonFnEntryRetag
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _))
    | (dsimp only))

theorem evalCopySingleDirect_callerBodies (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (locals₃ : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        locals₃) := by
  unfold evalCopySingleDirect
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _))
    | (dsimp only))

theorem commitCopyDstPlaceWrite_callerBodies (s : MachineState) (dstPlace : Place)
    (dstTargetLocal : LocalIdx) (dstTag : Nat) (locals₃ : List LocalSlot) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (commitCopyDstPlaceWrite s dstPlace dstTargetLocal dstTag locals₃ newVal localDecls
        layouts) := by
  unfold commitCopyDstPlaceWrite
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _))
    | (dsimp only))

theorem evalCopyUnionBytes_callerBodies (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo)
    (n : Nat) (locals₃ : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalCopyUnionBytes s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃) := by
  unfold evalCopyUnionBytes
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _)
      | exact commitCopyDstPlaceWrite_callerBodies ..)
    | (dsimp only))

theorem evalCopyNonOverlappingPermOk_callerBodies (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (countBits : Nat) (locals₃ : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk s src dst localDecls
        layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _)
      | exact evalCopySingleDirect_callerBodies ..
      | exact evalCopyUnionBytes_callerBodies ..
      | exact commitCopyDstPlaceWrite_callerBodies ..)
    | (dsimp only))

theorem evalForeignFrameCopySingleDirect_callerBodies (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (countBits : Nat) (locals₃ : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalForeignFrameCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry
        dstEntry countBits locals₃) := by
  unfold evalForeignFrameCopySingleDirect
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _)
      | exact ns_advance (cb_of_writeFrameLocalSlot (by assumption) (by rfl))
      | exact ns_mk (cb_of_writeFrameLocalSlot (by assumption) (by rfl)))
    | (dsimp only))

theorem evalCopyNonOverlappingWithCount_callerBodies (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits
        locals₃) := by
  unfold evalCopyNonOverlappingWithCount
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _)
      | exact evalCopyNonOverlappingPermOk_callerBodies ..
      | exact evalForeignFrameCopySingleDirect_callerBodies ..)
    | (dsimp only))

theorem evalCopyNonOverlapping_callerBodies (s : MachineState) (src dst count : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalCopyNonOverlapping s src dst count localDecls layouts) := by
  unfold evalCopyNonOverlapping
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact evalCopyNonOverlappingWithCount_callerBodies ..)
    | (dsimp only))

/-- **Statement steps keep every saved caller body.** Every `.running` successor of
`evalStmt s stmt` has a call stack whose saved caller bodies are those of `s` (statements
only rewrite saved frames' locals, through `commitForeignFrameLocals` /
`writeFrameLocalSlot`). -/
theorem evalStmt_callerBodies (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | intrinsic intr =>
    cases intr with
    | assume op =>
      unfold evalStmt
      dsimp only
      repeat' (first
        | split
        | with_reducible (first
          | exact ns_fail
          | exact ns_unsupported
          | exact ns_advance (CallerBodiesEq.refl _)
          | exact ns_mk (CallerBodiesEq.refl _))
        | (dsimp only))
    | copyNonOverlapping src dst count =>
      unfold evalStmt
      dsimp only
      exact evalCopyNonOverlapping_callerBodies s src dst count localDecls layouts
  | _ =>
    unfold evalStmt
    dsimp only
    repeat' (first
      | split
      | with_reducible (first
        | exact ns_fail
        | exact ns_unsupported
        | exact ns_advance (CallerBodiesEq.refl _)
        | exact ns_mk (CallerBodiesEq.refl _)
        | exact ns_advance (cb_of_rvalue (by assumption) (by rfl))
        | exact evalFnEntryRetag_callerBodies ..
        | exact evalNonFnEntryRetag_callerBodies ..
        | exact evalSetDiscriminantLocal_callerBodies ..
        | exact evalSetDiscriminantDerefWrite_callerBodies ..
        | exact evalForeignFrameDerefWrite_callerBodies _ _ _ _ _ _ _ _ (cb_of_rvalue (by assumption) (by rfl)))
      | (dsimp only))

theorem writeIntrinsicReturn_callerBodies (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (retVal : Value) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (writeIntrinsicReturn s locals' destination targetBb retVal) := by
  unfold writeIntrinsicReturn
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact ns_advance (CallerBodiesEq.refl _)
      | exact ns_mk (CallerBodiesEq.refl _)
      | exact ns_mk (cb_of_foreignFrameDerefWrite (by assumption) (by rfl))
      | exact ns_mk (CallerBodiesEq.of_eq (invalidateDirectDestWriteBorrows_callStack ..)))
    | (dsimp only))

theorem writeIntrinsicScalarResult_callerBodies (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (resOpt : Option ScalarInt) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (writeIntrinsicScalarResult s locals' destination targetBb resOpt) := by
  unfold writeIntrinsicScalarResult
  split
  · exact writeIntrinsicReturn_callerBodies ..
  · exact ns_fail

theorem intrinsicUnresolvedLayoutStep_callerBodies {P : MachineState → Prop} (ty : RigidTy) :
    NodeSuccs P (intrinsicUnresolvedLayoutStep ty) := by
  unfold intrinsicUnresolvedLayoutStep
  split
  · exact ns_fail
  · exact ns_unsupported

theorem intrinsicWidePointeeStep_callerBodies {P : MachineState → Prop} (ty : RigidTy) :
    NodeSuccs P (intrinsicWidePointeeStep ty) := by
  unfold intrinsicWidePointeeStep
  split
  · exact ns_unsupported
  · exact ns_fail

theorem intrinsicMissingPointeeStep_callerBodies {P : MachineState → Prop}
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable) (argOps : List Operand) :
    NodeSuccs P (intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps) := by
  unfold intrinsicMissingPointeeStep
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first | exact ns_fail | exact ns_unsupported)
    | (dsimp only))

/-- **Inline intrinsic calls keep every saved caller body.** -/
theorem evalNonSelectIntrinsicCall_callerBodies (kind : RustIntrinsicKind) (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts argOps argVals locals'
        destination targetBb) := by
  unfold evalNonSelectIntrinsicCall
  try dsimp only
  repeat' (first
    | split
    | with_reducible (first
      | exact ns_fail
      | exact ns_unsupported
      | exact writeIntrinsicReturn_callerBodies ..
      | exact writeIntrinsicScalarResult_callerBodies ..
      | exact intrinsicUnresolvedLayoutStep_callerBodies ..
      | exact intrinsicWidePointeeStep_callerBodies ..
      | exact intrinsicMissingPointeeStep_callerBodies ..)
    | (dsimp only))


theorem NodeSuccs.mono {P Q : MachineState → Prop} {n : MirStepNode}
    (h : ∀ s, P s → Q s) (hP : NodeSuccs P n) : NodeSuccs Q n := by
  cases n with
  | ret _ => trivial
  | tau st =>
    cases st with
    | running s' => exact h s' hP
    | halted _ => trivial
    | faulted _ => trivial
  | vis e k =>
    rcases e with fk | obs | ⟨req⟩
    · trivial
    · revert hP
      show (match k PUnit.unit with
        | .running s' => P s'
        | _ => True) →
        (match k PUnit.unit with
        | .running s' => Q s'
        | _ => True)
      cases k PUnit.unit with
      | running s' => exact h s'
      | halted _ => intro _; trivial
      | faulted _ => intro _; trivial
    · trivial

theorem NodeSuccs.and {P Q : MachineState → Prop} {n : MirStepNode}
    (hP : NodeSuccs P n) (hQ : NodeSuccs Q n) : NodeSuccs (fun s => P s ∧ Q s) n := by
  cases n with
  | ret _ => trivial
  | tau st =>
    cases st with
    | running s' => exact ⟨hP, hQ⟩
    | halted _ => trivial
    | faulted _ => trivial
  | vis e k =>
    rcases e with fk | obs | ⟨req⟩
    · trivial
    · revert hP hQ
      show (match k PUnit.unit with
        | .running s' => P s'
        | _ => True) →
        (match k PUnit.unit with
        | .running s' => Q s'
        | _ => True) →
        (match k PUnit.unit with
        | .running s' => P s' ∧ Q s'
        | _ => True)
      cases k PUnit.unit with
      | running s' => exact fun hp hq => ⟨hp, hq⟩
      | halted _ => intro _ _; trivial
      | faulted _ => intro _ _; trivial
    · trivial

/-- `ClosedInv` transfers to any state with the same callee table and active callee
whose saved frames keep their bodies. -/
theorem closedInv_of_callerBodies {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {s s' : MachineState} (h_inv : ClosedInv cone root c₁ s)
    (hc : s'.memory.callees = s.memory.callees)
    (hac : s'.memory.activeCallee = s.memory.activeCallee)
    (hb : CallerBodiesEq s.memory.callStack s'.memory.callStack) :
    ClosedInv cone root c₁ s' := by
  refine ⟨hc.trans h_inv.1, hac ▸ h_inv.2.1, ?_⟩
  intro f hf
  obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
  exact he ▸ h_inv.2.2 f₀ hf₀

/-- Successors of a step that fixes `(callees, activeCallee, traitImpls)` and keeps every
saved frame's body preserve `ClosedInv`. -/
theorem nodeSuccs_closedInv_of_ctx {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {s : MachineState} {n : MirStepNode}
    (h_inv : ClosedInv cone root c₁ s)
    (hfix : n = MirStepNode.mapMem
      (Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls) n)
    (hb : NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack) n) :
    NodeSuccs (ClosedInv cone root c₁) n := by
  refine NodeSuccs.mono ?_
    (NodeSuccs.and
      (nodeSuccs_of_fixed (P := fun s' => s' = MachineState.mapMem
        (Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls) s')
        hfix (fun _ h => h))
      hb)
  rintro s' ⟨hs', hb'⟩
  have hm : s'.memory =
      Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls s'.memory :=
    congrArg MachineState.memory hs'
  exact closedInv_of_callerBodies h_inv (by rw [hm]) (by rw [hm]) hb'

/-- The caller write of `TerminatorKind.return_` commutes with `Memory.withCalleeCtx`. -/
theorem writeReturnDestination_withCalleeCtx (c : CalleeEnv) (ac : Option CapturedMir)
    (ti : List TraitImplEntry) (callerLocals : List LocalSlot) (mem : Memory) (dst : Place)
    (retVal : Value) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    writeReturnDestination callerLocals (Memory.withCalleeCtx c ac ti mem) dst retVal localDecls
        layouts =
      FrameWriteResult.mapMem (Memory.withCalleeCtx c ac ti)
        (writeReturnDestination callerLocals mem dst retVal localDecls layouts) := by
  unfold writeReturnDestination
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | rfl | split)
  all_goals (
    try simp only [foreignFrameDerefWrite_withCalleeCtx'] at *
    try simp only [*, FrameWriteResult.mapMem] at *
    try (simp at *; done)
    try (simp only [FrameWriteResult.ok.injEq] at *
         obtain ⟨h₁, h₂⟩ := ‹_ ∧ _›
         subst_vars
         rfl))

/-- `writeReturnDestination` keeps `callees`, `activeCallee`, and `traitImpls`. -/
theorem writeReturnDestination_ctx_preserved {callerLocals : List LocalSlot} {mem : Memory}
    {dst : Place} {retVal : Value} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {locals' : List LocalSlot} {mem' : Memory}
    (h : writeReturnDestination callerLocals mem dst retVal localDecls layouts = .ok locals' mem') :
    mem'.callees = mem.callees ∧ mem'.activeCallee = mem.activeCallee ∧
      mem'.traitImpls = mem.traitImpls := by
  have hfix : writeReturnDestination callerLocals mem dst retVal localDecls layouts =
      FrameWriteResult.mapMem
        (Memory.withCalleeCtx mem.callees mem.activeCallee mem.traitImpls)
        (writeReturnDestination callerLocals mem dst retVal localDecls layouts) :=
    writeReturnDestination_withCalleeCtx mem.callees mem.activeCallee mem.traitImpls
      callerLocals mem dst retVal localDecls layouts
  rw [h] at hfix
  simp only [FrameWriteResult.mapMem, FrameWriteResult.ok.injEq] at hfix
  obtain ⟨_, hm⟩ := hfix
  exact ⟨by rw [hm], by rw [hm], by rw [hm]⟩

/-- `TerminatorKind.return_` into `caller` preserves `ClosedInv`: the resumed body is the
popped frame's (in the cone by `ClosedInv`) and the remaining frames keep their bodies. -/
theorem closedInv_return {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {s : MachineState} {caller : SavedCallerFrame} {rest : List SavedCallerFrame}
    {retVal : Value} {locals' : List LocalSlot} {mem' : Memory} {F : StackFrame}
    (h_inv : ClosedInv cone root c₁ s) (h_cs : s.memory.callStack = caller :: rest)
    (h_w : writeReturnDestination caller.frame.locals (ccReturnCallerMem s caller rest)
      caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts =
        .ok locals' mem') :
    ClosedInv cone root c₁ { frame := F, memory := mem' } := by
  obtain ⟨hc, hac, _⟩ := writeReturnDestination_ctx_preserved h_w
  have hb := writeReturnDestination_callerBodies h_w
  refine ⟨hc.trans h_inv.1, ?_, ?_⟩
  · show InConeSet cone root c₁ (mem'.activeCallee.getD root)
    rw [hac]
    exact h_inv.2.2 caller (by rw [h_cs]; exact List.Mem.head _)
  · intro f hf
    obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
    exact he ▸ h_inv.2.2 f₀ (by rw [h_cs]; exact List.Mem.tail _ hf₀)

theorem nodeSuccs_evalStmt {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {s : MachineState} {stmt : Statement} {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h_inv : ClosedInv cone root c₁ s) (h_free : Statement.calleeQueryFree stmt = true) :
    NodeSuccs (ClosedInv cone root c₁) (evalStmt s stmt localDecls layouts) :=
  nodeSuccs_closedInv_of_ctx h_inv (evalStmt_calleeCtx_preserved s stmt localDecls layouts h_free)
    (evalStmt_callerBodies s stmt localDecls layouts)

theorem closedInv_unwindFromCallStack {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} :
    ∀ (stk : List SavedCallerFrame) (m : Memory), m.callees = c₁ →
      (∀ f, f ∈ stk → InConeSet cone root c₁ f.callerBody) →
      ∀ s', unwindFromCallStack stk m = .running s' → ClosedInv cone root c₁ s'
  | [], _, _, _, _, h => by cases h
  | caller :: rest, m, hc, hf, s', h => by
    unfold unwindFromCallStack at h
    dsimp only at h
    cases hr : caller.returnUnwind with
    | unreachable => rw [hr] at h; dsimp only at h; cases h
    | terminate => rw [hr] at h; dsimp only at h; cases h
    | continue_ =>
      rw [hr] at h
      dsimp only at h
      exact closedInv_unwindFromCallStack rest
        { m with
          callStack := rest
          activeCallee := some caller.callerBody
          activeProtectors := restoreCallerProtectors caller }
        hc (fun f hm => hf f (List.Mem.tail _ hm)) s' h
    | cleanup bb =>
      rw [hr] at h
      dsimp only at h
      cases h
      exact ⟨hc, hf caller (List.Mem.head _), fun f hm => hf f (List.Mem.tail _ hm)⟩

private theorem nodeSuccs_unwindMatch {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} (st : MirExecState)
    (h : ∀ s', st = .running s' → ClosedInv cone root c₁ s') :
    NodeSuccs (ClosedInv cone root c₁)
      (match (generalizing := false) st with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  cases st with
  | running s' => exact h s' rfl
  | halted _ => trivial
  | faulted _ => trivial

private theorem nodeSuccs_applyUnwind {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {s : MachineState} (h_inv : ClosedInv cone root c₁ s)
    (l : List LocalSlot) (u : UnwindAction) :
    NodeSuccs (ClosedInv cone root c₁)
      (match applyUnwindAction s l s.memory u with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  refine nodeSuccs_unwindMatch _ ?_
  intro s' hs'
  cases u with
  | unreachable => cases hs'
  | terminate => cases hs'
  | continue_ =>
    exact closedInv_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.2 s' hs'
  | cleanup bb =>
    cases hs'
    exact h_inv

private theorem inConeSet_of_lookup {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {L : LayoutTable} {dp : DefPath} {ti : List TraitImplEntry}
    {b : CapturedMir} (h_dp : dp ∈ cone) (h_lk : lookupCallee c₁ L dp [] ti = some b) :
    InConeSet cone root c₁ b := by
  obtain ⟨hm, hd⟩ := findCallee?_spec (lookupCallee_nil_eq_some h_lk)
  right
  unfold coneBodies
  rw [List.mem_filter]
  exact ⟨hm, inCone_iff.mpr (hd ▸ h_dp)⟩

private theorem closedInv_push {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {s : MachineState} {saved : SavedCallerFrame} {b : CapturedMir} {F : StackFrame}
    (h_inv : ClosedInv cone root c₁ s) (h_saved : InConeSet cone root c₁ saved.callerBody)
    (h_b : InConeSet cone root c₁ b) :
    ClosedInv cone root c₁
      { frame := F,
        memory := { s.memory with
          callStack := saved :: s.memory.callStack
          activeCallee := some b } } := by
  refine ⟨h_inv.1, h_b, ?_⟩
  intro f hf
  cases hf with
  | head => exact h_saved
  | tail _ hf => exact h_inv.2.2 f hf

theorem nodeSuccs_evalDirectRustIntrinsic?_of_nonSelect {cone : List DefPath}
    {root : CapturedMir} {c₁ : CalleeEnv} {s : MachineState}
    (h_inv : ClosedInv cone root c₁ s) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (h_cl : isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true)
    (fallback : MirStepNode) (h_fb : NodeSuccs (ClosedInv cone root c₁) fallback) :
    NodeSuccs (ClosedInv cone root c₁)
      (match evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb unwind with
       | some stepNode => stepNode
       | none => fallback) := by
  unfold evalDirectRustIntrinsic?
  cases h_k : classifyRustIntrinsic? target.defPath with
  | none => exact h_fb
  | some kind =>
    rw [h_k] at h_cl
    have h_step : ∀ (k : RustIntrinsicKind),
        NodeSuccs (ClosedInv cone root c₁)
          (evalNonSelectIntrinsicCall k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb) := by
      intro k
      exact nodeSuccs_closedInv_of_ctx h_inv
        (evalNonSelectIntrinsicCall_calleeCtx_preserved k s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
        (evalNonSelectIntrinsicCall_callerBodies k s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
    cases kind with
    | constEvalSelect => cases h_cl
    | _ => exact h_step _

theorem nodeSuccs_evalTerminator {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {s : MachineState} {term : Terminator} (h_inv : ClosedInv cone root c₁ s)
    (h_term : TermConeSafe cone s (s.memory.activeCallee.getD root) term) :
    NodeSuccs (ClosedInv cone root c₁)
      (evalTerminator s term (some (s.memory.activeCallee.getD root))) := by
  have h_cur : InConeSet cone root c₁ (s.memory.activeCallee.getD root) := h_inv.2.1
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => exact h_inv
  | switchInt discr targets =>
    unfold evalTerminator
    dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | unwindResume =>
    unfold evalTerminator
    dsimp only
    exact nodeSuccs_unwindMatch _
      (closedInv_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.2)
  | unwindTerminate => trivial
  | return_ =>
    rw [ccEvalReturn_eq]
    unfold ccEvalReturn
    repeat' (first | trivial | exact closedInv_return h_inv ‹_› ‹_› | split)
  | unreachable => trivial
  | drop place target unwind =>
    unfold evalTerminator
    dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | assert cond expected target unwind =>
    unfold evalTerminator
    dsimp only
    repeat' (first | trivial | exact h_inv | exact nodeSuccs_applyUnwind h_inv _ _ | split)
  | call func argOps destination target unwind =>
    have hq : CallTargetInCone cone s (s.memory.activeCallee.getD root) func (length argOps) :=
      h_term
    cases target with
    | some targetBb =>
      unfold evalTerminator
      dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_ta, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          rw [h_ta]
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath [] s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1] at h_lk
              exact closedInv_push h_inv h_cur (inConeSet_of_lookup h_dp h_lk)
          | none =>
            dsimp only
            repeat' (first
              | trivial | exact h_inv
              | exact nodeSuccs_closedInv_of_ctx h_inv (writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                  (writeIntrinsicReturn_callerBodies _ _ _ _ _)
              | exact nodeSuccs_evalDirectRustIntrinsic?_of_nonSelect h_inv _ _ _ _ _ _ _ _ _ _ h_cl _
                  (by
                    repeat' (first
                      | trivial | exact h_inv
                      | exact nodeSuccs_closedInv_of_ctx h_inv
                          (writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                          (writeIntrinsicReturn_callerBodies _ _ _ _ _)
                      | split))
              | split)
    | none =>
      unfold evalTerminator
      dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_ta, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          rw [h_ta]
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath [] s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1] at h_lk
              exact closedInv_push h_inv h_cur (inConeSet_of_lookup h_dp h_lk)
          | none =>
            dsimp only
            repeat' (first | trivial | exact nodeSuccs_applyUnwind h_inv _ _ | split)
  | tailCall func argOps =>
    have hq : CallTargetInCone cone s (s.memory.activeCallee.getD root) func (length argOps) :=
      h_term
    unfold evalTerminator
    dsimp only
    unfold evalTailCallTerminator
    dsimp only
    cases h_res : resolveCallTarget s func (length argOps)
        (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
        (s.memory.activeCallee.getD root).layouts with
    | ub => trivial
    | unsupported => trivial
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, h_ta, h_cl⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
          (s.memory.activeCallee.getD root).layouts s.memory.callerLocals (callStack := s.memory.callStack) with
      | ub => trivial
      | unsupported => trivial
      | ok argVals locals' =>
        dsimp only
        rw [h_ta]
        cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
            tgt.defPath [] s.memory.traitImpls with
        | some calleeBody =>
          dsimp only
          rw [h_inv.1] at h_lk
          repeat' (first
            | trivial
            | exact ⟨h_inv.1, inConeSet_of_lookup h_dp h_lk, h_inv.2.2⟩
            | split)
        | none =>
          dsimp only
          repeat' (first | trivial | split)
  | _ => trivial

theorem nodeSuccs_stepMirFn {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {s : MachineState} (h_closed : CallConeClosed cone root c₁ = true)
    (h_inv : ClosedInv cone root c₁ s) :
    NodeSuccs (ClosedInv cone root c₁) (stepMirFn root s) := by
  have h_safe := stepConeSafe_of_closedInv h_closed h_inv
  unfold stepMirFn
  dsimp only
  split
  · trivial
  · cases h_bb : get? (s.memory.activeCallee.getD root).basicBlocks s.frame.blockIdx with
    | none => trivial
    | some blk =>
      obtain ⟨h_stmt, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact nodeSuccs_evalStmt h_inv (h_stmt stmt h_st)
      | none =>
        dsimp only
        by_cases h_end : (s.frame.stmtIdx == length blk.statements) = true
        · rw [if_pos h_end]
          exact nodeSuccs_evalTerminator h_inv h_term
        · rw [if_neg h_end]
          trivial

/-- **Syntactic closure implies the semantic step-invariant** for every fuel bound. -/
theorem coneReach_of_closedInv {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    (h_closed : CallConeClosed cone root c₁ = true) :
    ∀ (fuel : Nat) (s : MachineState), ClosedInv cone root c₁ s →
      ConeReach root (StepConeSafe cone root) fuel (.running s)
  | 0, _, _ => trivial
  | fuel + 1, s, h_inv => by
    refine ⟨stepConeSafe_of_closedInv h_closed h_inv, ?_⟩
    have h_succ := nodeSuccs_stepMirFn h_closed h_inv
    revert h_succ
    cases stepMirFn root s with
    | ret _ => intro _; trivial
    | tau st' =>
      cases st' with
      | running s' => intro h; exact coneReach_of_closedInv h_closed fuel s' h
      | halted _ => intro _; cases fuel <;> trivial
      | faulted _ => intro _; cases fuel <;> trivial
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _; trivial
      · intro h
        show ConeReach root _ fuel (k PUnit.unit)
        revert h
        show (match k PUnit.unit with
          | .running s' => ClosedInv cone root c₁ s'
          | _ => True) → _
        cases k PUnit.unit with
        | running s' => intro h; exact coneReach_of_closedInv h_closed fuel s' h
        | halted _ => intro _; cases fuel <;> trivial
        | faulted _ => intro _; cases fuel <;> trivial
      · intro _; trivial

/--
Well-formedness of `(body, mem, c)` for `initMachineStateWithMemoryAndCallees`: either `c` is
non-empty (`c ≠ []`), or `mem` is a clean entry memory (`mem.callees = [] ∧ mem.traitImpls =
body.traitImpls`), allowing call-cone narrowing all the way down to an empty callee table
`c₂ = []` (`coneBodies [] c₁ = []`).
-/
def CalleeInitWf (body : CapturedMir) (mem : Memory) (c : CalleeEnv) : Prop :=
  c ≠ [] ∨ (mem.callees = [] ∧ mem.traitImpls = body.traitImpls)

theorem initMachineStateWithMemoryAndCallees_withCallees_of_wf (body : CapturedMir)
    (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : CalleeInitWf body mem c₁) (h₂ : CalleeInitWf body mem c₂) :
    Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₂ =
      MachineState.mapMem (Memory.withCallees c₂)
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) := by
  cases c₁ with
  | nil =>
    rcases h₁ with hne | ⟨hc₁, hti₁⟩
    · exact absurd rfl hne
    · cases c₂ with
      | nil =>
        unfold Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          Trusted.VerificationResult.initMachineStateWithMemory
          MachineState.mapMem Memory.withCallees
        dsimp only
        cases mem
        dsimp only at hc₁
        subst hc₁
        rfl
      | cons b₂ r₂ =>
        unfold Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          Trusted.VerificationResult.initMachineStateWithMemory
          MachineState.mapMem Memory.withCallees
        dsimp only
        cases mem
        dsimp only at hti₁
        subst hti₁
        rfl
  | cons b₁ r₁ =>
    cases c₂ with
    | nil =>
      rcases h₂ with hne | ⟨hc₂, hti₂⟩
      · exact absurd rfl hne
      · unfold Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          Trusted.VerificationResult.initMachineStateWithMemory
          MachineState.mapMem Memory.withCallees
        dsimp only
        cases mem
        dsimp only at hc₂ hti₂
        subst hc₂ hti₂
        rfl
    | cons b₂ r₂ => rfl

theorem initMachineStateWithMemoryAndCallees_callees_of_wf (body : CapturedMir)
    (args : List Value) (mem : Memory) {c : CalleeEnv} (h : CalleeInitWf body mem c) :
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c).memory.callees = c := by
  cases c with
  | nil =>
    rcases h with hne | ⟨hc, _⟩
    · exact absurd rfl hne
    · exact hc
  | cons b r => rfl

theorem closedInv_init_of_wf (cone : List DefPath) (body : CapturedMir) (args : List Value)
    (mem : Memory) {c₁ : CalleeEnv} (h₁ : CalleeInitWf body mem c₁)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    ClosedInv cone body c₁
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) := by
  refine ⟨initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁, ?_, ?_⟩
  · cases c₁ <;> (
      show InConeSet cone body _ (mem.activeCallee.getD body)
      rw [h_ac]
      exact Or.inl rfl)
  · intro f hf
    cases c₁ <;> (
      have hf' : f ∈ mem.callStack := hf
      rw [h_cs] at hf'
      cases hf')

/--
**Syntactic call-cone narrowing (`runCfgWithCallees`) allowing empty target cones (`c₂ = []`).**
-/
theorem runCfgWithCallees_cone_narrow_of_closed_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : CalleeInitWf body mem c₁) (h₂ : CalleeInitWf body mem c₂)
    (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_closed : CallConeClosed cone body c₁ = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    runCfgWithCallees fuel body args mem c₂ =
      (runCfgWithCallees fuel body args mem c₁).map (MirOutcome.mapMem (Memory.withCallees c₂)) := by
  unfold runCfgWithCallees
  rw [initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine runMirExecBounded_cone_narrow cone body c₂ fuel _
    (coneReach_of_closedInv h_closed fuel _ (closedInv_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact h_agree

/--
**Syntactic call-cone narrowing (`wpMirExecSym`) allowing empty target cones (`c₂ = []`).**
-/
theorem wpMirExecSym_cone_narrow_of_closed_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : CalleeInitWf body mem c₁) (h₂ : CalleeInitWf body mem c₂)
    (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_closed : CallConeClosed cone body c₁ = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out) :
    wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₂))
        post ↔
      wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁))
        post := by
  rw [initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine wpMirExecSym_cone_narrow cone body c₂ post h_post fuel _
    (coneReach_of_closedInv h_closed fuel _ (closedInv_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact h_agree

/--
**Syntactic call-cone narrowing (`MirWpConverges`) allowing empty target cones (`c₂ = []`).**
-/
theorem mirWpConverges_cone_narrow_of_closed_wf (cone : List DefPath) (body : CapturedMir)
    (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : CalleeInitWf body mem c₁) (h₂ : CalleeInitWf body mem c₂)
    (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_closed : CallConeClosed cone body c₁ = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out) :
    MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₂) post ↔
      MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) post := by
  rw [initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine mirWpConverges_cone_narrow cone body c₂ post h_post _
    (fun fuel =>
      coneReach_of_closedInv h_closed fuel _ (closedInv_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  rw [initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact h_agree

/-- The entry state with a non-empty callee table satisfies the closure invariant. -/
theorem closedInv_init (cone : List DefPath) (body : CapturedMir) (args : List Value)
    (mem : Memory) {c₁ : CalleeEnv} (h₁ : c₁ ≠ [])
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    ClosedInv cone body c₁
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) :=
  closedInv_init_of_wf cone body args mem (Or.inl h₁) h_ac h_cs

/--
**Syntactic call-cone narrowing (`runCfgWithCallees`).** If `CallConeClosed cone body c₁`
holds (decidable, e.g. by `decide` / `rfl`), the run of `body` with any non-empty table
`c₂` agreeing with `c₁` on `cone` (for instance `coneBodies cone c₁`) is the
`withCallees c₂` image of the run with `c₁`, for every fuel bound, starting from any
root-frame memory (`activeCallee = none`, empty call stack).
-/
theorem runCfgWithCallees_cone_narrow_of_closed (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : c₁ ≠ []) (h₂ : c₂ ≠ []) (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_closed : CallConeClosed cone body c₁ = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    runCfgWithCallees fuel body args mem c₂ =
      (runCfgWithCallees fuel body args mem c₁).map (MirOutcome.mapMem (Memory.withCallees c₂)) :=
  runCfgWithCallees_cone_narrow cone fuel body args mem h₁ h₂ h_agree
    (coneReach_of_closedInv h_closed fuel _ (closedInv_init cone body args mem h₁ h_ac h_cs))

/--
**Syntactic call-cone narrowing (`wpMirExecSym`).** Under `CallConeClosed`, every
callee-insensitive postcondition transfers between the entry states with `c₁` and `c₂`.
-/
theorem wpMirExecSym_cone_narrow_of_closed (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : c₁ ≠ []) (h₂ : c₂ ≠ []) (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_closed : CallConeClosed cone body c₁ = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out) :
    wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₂))
        post ↔
      wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁))
        post :=
  wpMirExecSym_cone_narrow_init cone fuel body args mem h₁ h₂ h_agree post h_post
    (coneReach_of_closedInv h_closed fuel _ (closedInv_init cone body args mem h₁ h_ac h_cs))

/--
**Syntactic call-cone narrowing (`MirWpConverges`)**: the fuel-free corollary.
-/
theorem mirWpConverges_cone_narrow_of_closed (cone : List DefPath) (body : CapturedMir)
    (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : c₁ ≠ []) (h₂ : c₂ ≠ []) (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_closed : CallConeClosed cone body c₁ = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out) :
    MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₂) post ↔
      MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) post :=
  mirWpConverges_cone_narrow_init cone body args mem h₁ h₂ h_agree post h_post
    (fun fuel =>
      coneReach_of_closedInv h_closed fuel _ (closedInv_init cone body args mem h₁ h_ac h_cs))

/-! ### Polymorphic Call-Cone Narrowing (`CallConeClosedPoly` & Generic Body Monomorphization) -/

/--
Polymorphic call-target cone condition: every target that `resolveCallTarget` resolves for `func`
has its `defPath` in `cone`, has no `TraitImplEntry` registered for `defPath` in either
`s.memory.callees` or `c₂` (with `s.memory.traitImpls`), and is not `const_eval_select`.
Unlike `CallTargetInCone`, `target.typeArgs` may be arbitrary (`List RigidTy`), covering both
polymorphic inline intrinsics (`size_of_val::<[u32]>`, `align_of_val::<[u32]>`,
`arith_offset::<u32>`, `wrapping_add::<u32>`, etc.) and generic non-trait Rust callees.
-/
def CallTargetInConePoly (cone : List DefPath) (c₂ : CalleeEnv) (s : MachineState)
    (cur : CapturedMir) (func : Operand) (argCount : Nat) : Prop :=
  ∀ target localsAfterFunc,
    resolveCallTarget s func argCount (bodyLocalDeclsOf (some cur)) cur.layouts =
        .ok target localsAfterFunc →
      target.defPath ∈ cone ∧
        hasTraitImplForDefPath (s.memory.traitImpls ++ flatMapTraitImpls s.memory.callees)
          target.defPath = false ∧
        hasTraitImplForDefPath (s.memory.traitImpls ++ flatMapTraitImpls c₂)
          target.defPath = false ∧
        isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true

def TermConeSafePoly (cone : List DefPath) (c₂ : CalleeEnv) (s : MachineState) (cur : CapturedMir)
    (term : Terminator) : Prop :=
  match term.kind with
  | .call func argOps _ _ _ => CallTargetInConePoly cone c₂ s cur func (length argOps)
  | .tailCall func argOps => CallTargetInConePoly cone c₂ s cur func (length argOps)
  | _ => True

def StepConeSafePoly (cone : List DefPath) (c₂ : CalleeEnv) (body : CapturedMir)
    (s : MachineState) : Prop :=
  ∀ blk, get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some blk →
    (∀ stmt, get? blk.statements s.frame.stmtIdx = some stmt →
      Statement.calleeQueryFree stmt = true) ∧
    TermConeSafePoly cone c₂ s (s.memory.activeCallee.getD body) blk.terminator

theorem StepConeSafePoly.toSelf {cone : List DefPath} {c₂ : CalleeEnv} {body : CapturedMir}
    {s : MachineState} (h : StepConeSafePoly cone c₂ body s) :
    StepConeSafePoly cone s.memory.callees body s := by
  intro blk h_bb
  obtain ⟨h_stmt, h_term⟩ := h blk h_bb
  refine ⟨h_stmt, ?_⟩
  revert h_term
  rcases blk.terminator with ⟨kind, span⟩
  intro h_term
  cases kind with
  | call func argOps _ _ _ =>
    intro tgt l h_res
    obtain ⟨h_dp, h_no₁, _, h_cl⟩ := h_term tgt l h_res
    exact ⟨h_dp, h_no₁, h_no₁, h_cl⟩
  | tailCall func argOps =>
    intro tgt l h_res
    obtain ⟨h_dp, h_no₁, _, h_cl⟩ := h_term tgt l h_res
    exact ⟨h_dp, h_no₁, h_no₁, h_cl⟩
  | _ => trivial

/--
**Polymorphic terminator narrowing (`evalTerminator_withCallees_poly`).** Under `TermConeSafePoly`
and `calleesAgreeOn`, `evalTerminator` commutes with `Memory.withCallees c₂` for arbitrary
generic `typeArgs`.
-/
theorem evalTerminator_withCallees_poly (cone : List DefPath) (c₂ : CalleeEnv) (s : MachineState)
    (term : Terminator) (cur : CapturedMir)
    (h_agree : calleesAgreeOn cone s.memory.callees c₂)
    (h_safe : TermConeSafePoly cone c₂ s cur term) :
    evalTerminator (MachineState.mapMem (Memory.withCallees c₂) s) term (some cur) =
      MirStepNode.mapMem (Memory.withCallees c₂) (evalTerminator s term (some cur)) := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => rfl
  | switchInt discr targets =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
      Memory.withCallees_globals, Memory.withCallees_callerLocals]
    repeat' (first | exact nodeCC_fail | rfl | split)
  | unwindResume =>
    show (match unwindFromCallStack s.memory.callStack (Memory.withCallees c₂ s.memory) with
      | .running nextState => MirStepNode.step nextState
      | .halted out => MirStepNode.retOutcome out
      | .faulted fk => MirStepNode.fail fk) =
      MirStepNode.mapMem (Memory.withCallees c₂)
        (match unwindFromCallStack s.memory.callStack s.memory with
          | .running nextState => MirStepNode.step nextState
          | .halted out => MirStepNode.retOutcome out
          | .faulted fk => MirStepNode.fail fk)
    rw [unwindFromCallStack_withCallees]
    cases unwindFromCallStack s.memory.callStack s.memory <;> rfl
  | unwindTerminate => rfl
  | return_ => exact evalTerminator_return_withCallees c₂ s span (some cur)
  | unreachable => rfl
  | drop place target unwind =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory]
    repeat' (first | exact nodeCC_fail | rfl | split)
  | assert cond expected target unwind =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
      Memory.withCallees_globals, Memory.withCallees_callerLocals]
    repeat' (first
      | exact nodeCC_fail | rfl
      | exact nodeCC_unwind c₂ s _ _
      | split)
  | call func argOps destination target unwind =>
    have hq : CallTargetInConePoly cone c₂ s cur func (length argOps) := h_safe
    cases target with
    | some targetBb =>
      unfold evalTerminator
      dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
        Memory.withCallees_globals, Memory.withCallees_callerLocals, Memory.withCallees_callees,
        Memory.withCallees_traitImpls]
      rw [show resolveCallTarget (MachineState.mapMem (Memory.withCallees c₂) s) func (length argOps)
          (bodyLocalDeclsOf (some cur)) cur.layouts =
        resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts from rfl]
      cases h_res : resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts with
      | ub => rfl
      | unsupported => rfl
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_no₁, h_no₂, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
            s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => rfl
        | unsupported => rfl
        | ok argVals locals' =>
          dsimp only
          rw [lookupCallee_eq_of_findCallee_eq_of_no_traitImpl cur.layouts tgt.typeArgs
              s.memory.traitImpls (h_agree tgt.defPath h_dp).symm h_no₂ h_no₁,
            evalDirectRustIntrinsic?_withCallees_of_nonSelect c₂ s (some cur) tgt
              (bodyLocalDeclsOf (some cur)) cur.layouts argOps argVals locals' destination
              targetBb unwind h_cl]
          cases evalDirectRustIntrinsic? s (some cur) tgt (bodyLocalDeclsOf (some cur))
              cur.layouts argOps argVals locals' destination targetBb unwind <;>
            repeat' (first
              | exact nodeCC_fail | rfl
              | exact writeIntrinsicReturn_withCallees c₂ s _ _ _ _
              | split)
    | none =>
      unfold evalTerminator
      dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
        Memory.withCallees_globals, Memory.withCallees_callerLocals, Memory.withCallees_callees,
        Memory.withCallees_traitImpls]
      rw [show resolveCallTarget (MachineState.mapMem (Memory.withCallees c₂) s) func (length argOps)
          (bodyLocalDeclsOf (some cur)) cur.layouts =
        resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts from rfl]
      cases h_res : resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts with
      | ub => rfl
      | unsupported => rfl
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_no₁, h_no₂, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
            s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => rfl
        | unsupported => rfl
        | ok argVals locals' =>
          dsimp only
          rw [lookupCallee_eq_of_findCallee_eq_of_no_traitImpl cur.layouts tgt.typeArgs
              s.memory.traitImpls (h_agree tgt.defPath h_dp).symm h_no₂ h_no₁]
          repeat' (first
            | exact nodeCC_fail | rfl
            | exact nodeCC_unwind c₂ s _ _
            | split)
  | tailCall func argOps =>
    have hq : CallTargetInConePoly cone c₂ s cur func (length argOps) := h_safe
    unfold evalTerminator
    dsimp only
    unfold evalTailCallTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
      Memory.withCallees_globals, Memory.withCallees_callerLocals, Memory.withCallees_callees,
      Memory.withCallees_traitImpls]
    rw [show resolveCallTarget (MachineState.mapMem (Memory.withCallees c₂) s) func (length argOps)
        (bodyLocalDeclsOf (some cur)) cur.layouts =
      resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts from rfl]
    cases h_res : resolveCallTarget s func (length argOps) (bodyLocalDeclsOf (some cur)) cur.layouts with
    | ub => rfl
    | unsupported => rfl
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, h_no₁, h_no₂, _⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals cur.layouts
          s.memory.callerLocals (callStack := s.memory.callStack) with
      | ub => rfl
      | unsupported => rfl
      | ok argVals locals' =>
        dsimp only
        rw [lookupCallee_eq_of_findCallee_eq_of_no_traitImpl cur.layouts tgt.typeArgs
            s.memory.traitImpls (h_agree tgt.defPath h_dp).symm h_no₂ h_no₁]
        repeat' (first
          | exact nodeCC_fail | rfl
          | split)
  | _ => rfl

theorem stepMirFn_withCallees_poly (cone : List DefPath) (body : CapturedMir) (s : MachineState)
    (c₂ : CalleeEnv) (h_agree : calleesAgreeOn cone s.memory.callees c₂)
    (h_safe : StepConeSafePoly cone c₂ body s) :
    stepMirFn body (MachineState.mapMem (Memory.withCallees c₂) s) =
      MirStepNode.mapMem (Memory.withCallees c₂) (stepMirFn body s) := by
  unfold stepMirFn
  dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_activeCallee]
  split
  · rfl
  · cases h_bb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => rfl
    | some blk =>
      obtain ⟨h_stmt, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact evalStmt_withCallees c₂ s stmt _ _ (h_stmt stmt h_st)
      | none =>
        dsimp only
        by_cases h_end : (s.frame.stmtIdx == length blk.statements) = true
        · exact (if_pos h_end).trans
            ((evalTerminator_withCallees_poly cone c₂ s blk.terminator _ h_agree h_term).trans
              (congrArg (MirStepNode.mapMem (Memory.withCallees c₂)) (if_pos h_end).symm))
        · conv => rhs; rw [if_neg h_end]
          exact if_neg h_end

theorem stepMirFn_callees_preserved_poly (cone : List DefPath) (c₂ : CalleeEnv)
    (body : CapturedMir) (s : MachineState) (h_safe : StepConeSafePoly cone c₂ body s) :
    stepMirFn body s = MirStepNode.mapMem (Memory.withCallees s.memory.callees) (stepMirFn body s) :=
  stepMirFn_withCallees_poly cone body s s.memory.callees (calleesAgreeOn.refl _ _) h_safe.toSelf

theorem runMirExecBounded_cone_narrow_poly (cone : List DefPath) (body : CapturedMir)
    (c₂ : CalleeEnv) :
    ∀ (fuel : Nat) (st : MirExecState),
      ConeReach body (StepConeSafePoly cone c₂ body) fuel st → AgreesAt cone c₂ st →
      runMirExecBounded fuel body (MirExecState.mapMem (Memory.withCallees c₂) st) =
        (runMirExecBounded fuel body st).map (MirOutcome.mapMem (Memory.withCallees c₂))
  | 0, _, _, _ => rfl
  | _ + 1, .halted _, _, _ => rfl
  | _ + 1, .faulted _, _, _ => rfl
  | fuel + 1, .running s, h_reach, h_agree => by
    have h_ag := h_agree s rfl
    obtain ⟨h_safe, h_next⟩ := h_reach
    have h_step := stepMirFn_withCallees_poly cone body s c₂ h_ag h_safe
    have h_fix := stepMirFn_callees_preserved_poly cone c₂ body s h_safe
    show (match stepMirFn body (MachineState.mapMem (Memory.withCallees c₂) s) with
        | .ret out => some out
        | .tau st' => runMirExecBounded fuel body st'
        | .vis (.inr (.inl _)) k => runMirExecBounded fuel body (k PUnit.unit)
        | .vis (.inl _) _ => none
        | .vis (.inr (.inr _)) _ => none) =
      (match stepMirFn body s with
        | .ret out => some out
        | .tau st' => runMirExecBounded fuel body st'
        | .vis (.inr (.inl _)) k => runMirExecBounded fuel body (k PUnit.unit)
        | .vis (.inl _) _ => none
        | .vis (.inr (.inr _)) _ => none).map (MirOutcome.mapMem (Memory.withCallees c₂))
    rw [h_step]
    revert h_next h_fix
    cases stepMirFn body s with
    | ret out => intro _ _; rfl
    | tau st' =>
      intro h_next h_fix
      exact runMirExecBounded_cone_narrow_poly cone body c₂ fuel st' h_next
        (agreesAt_succ h_ag (tau_fixed h_fix))
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _ _; rfl
      · intro h_next h_fix
        have hk : k PUnit.unit =
            MirExecState.mapMem (Memory.withCallees s.memory.callees) (k PUnit.unit) :=
          congrFun (eq_of_heq (Trusted.ITree.ITreeF.vis.inj h_fix).2) PUnit.unit
        exact runMirExecBounded_cone_narrow_poly cone body c₂ fuel (k PUnit.unit) h_next
          (agreesAt_succ h_ag hk)
      · intro _ _; rfl

theorem wpMirExecSym_cone_narrow_poly (cone : List DefPath) (body : CapturedMir) (c₂ : CalleeEnv)
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out) :
    ∀ (fuel : Nat) (st : MirExecState),
      ConeReach body (StepConeSafePoly cone c₂ body) fuel st → AgreesAt cone c₂ st →
      (wpMirExecSym fuel body (MirExecState.mapMem (Memory.withCallees c₂) st) post ↔
        wpMirExecSym fuel body st post)
  | 0, _, _, _ => Iff.rfl
  | fuel + 1, .halted out, _, _ => by
    rw [wpMirExecSym_succ_eq, wpMirExecSym_succ_eq]
    exact h_post out
  | fuel + 1, .faulted _, _, _ => by
    rw [wpMirExecSym_succ_eq, wpMirExecSym_succ_eq]
    exact Iff.rfl
  | fuel + 1, .running s, h_reach, h_agree => by
    have h_ag := h_agree s rfl
    obtain ⟨h_safe, h_next⟩ := h_reach
    have h_step := stepMirFn_withCallees_poly cone body s c₂ h_ag h_safe
    have h_fix := stepMirFn_callees_preserved_poly cone c₂ body s h_safe
    rw [wpMirExecSym_succ_eq, wpMirExecSym_succ_eq]
    show evalNodeWP _ post (stepMirFn body (MachineState.mapMem (Memory.withCallees c₂) s)) ↔
      evalNodeWP _ post (stepMirFn body s)
    rw [h_step]
    revert h_next h_fix
    cases stepMirFn body s with
    | ret out => intro _ _; exact h_post out
    | tau st' =>
      intro h_next h_fix
      exact wpMirExecSym_cone_narrow_poly cone body c₂ post h_post fuel st' h_next
        (agreesAt_succ h_ag (tau_fixed h_fix))
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _ _; exact Iff.rfl
      · intro h_next h_fix
        have hk : k PUnit.unit =
            MirExecState.mapMem (Memory.withCallees s.memory.callees) (k PUnit.unit) :=
          congrFun (eq_of_heq (Trusted.ITree.ITreeF.vis.inj h_fix).2) PUnit.unit
        exact wpMirExecSym_cone_narrow_poly cone body c₂ post h_post fuel (k PUnit.unit) h_next
          (agreesAt_succ h_ag hk)
      · intro _ _; exact Iff.rfl

/-- Extract `DefPath` from a constant `.fnDef` operand (preserved by `Operand.instantiate`). -/
def extractFnDefPath? : Operand → Option DefPath
  | .constant c =>
    match c.ty.kind with
    | .fnDef defPath _ => some defPath
    | _ => none
  | _ => none

theorem extractCalleeDefPath?_of_extractFnDefPath? {func : Operand} {dp : DefPath}
    (h : extractFnDefPath? func = some dp) : extractCalleeDefPath? func = some dp := by
  cases func with
  | copy _ => cases h
  | move _ => cases h
  | constant c =>
    rcases c with ⟨⟨kind, lidx⟩, val⟩
    cases kind <;> cases h <;> rfl

theorem extractFnDefPath?_instantiate {tbl : LayoutTable} {subst : TypeSubst}
    {func : Operand} {dp : DefPath} (h : extractFnDefPath? func = some dp) :
    extractFnDefPath? (Operand.instantiate tbl subst func) = some dp := by
  cases func with
  | copy _ => cases h
  | move _ => cases h
  | constant c =>
    rcases c with ⟨⟨kind, lidx⟩, val⟩
    cases kind <;> cases h <;> rfl

/-- Polymorphic direct-call cone check (allows arbitrary `typeArgs` on `.fnDef` constants). -/
def directCallInConePoly (cone : List DefPath) (func : Operand) : Bool :=
  match extractFnDefPath? func with
  | some dp => inCone cone dp && isNonSelectIntrinsicOpt (classifyRustIntrinsic? dp)
  | none => false

theorem directCallInConePoly_instantiate {cone : List DefPath} {tbl : LayoutTable}
    {subst : TypeSubst} {func : Operand} (h : directCallInConePoly cone func = true) :
    directCallInConePoly cone (Operand.instantiate tbl subst func) = true := by
  unfold directCallInConePoly at h ⊢
  cases h_dp : extractFnDefPath? func with
  | none => rw [h_dp] at h; cases h
  | some dp =>
    rw [h_dp] at h
    rw [extractFnDefPath?_instantiate h_dp]
    exact h

def termCallsInConePoly (cone : List DefPath) (term : Terminator) : Bool :=
  match term.kind with
  | .call func _ _ _ _ => directCallInConePoly cone func
  | .tailCall func _ => directCallInConePoly cone func
  | _ => true

theorem termCallsInConePoly_instantiate {cone : List DefPath} {tbl : LayoutTable}
    {subst : TypeSubst} {term : Terminator} (h : termCallsInConePoly cone term = true) :
    termCallsInConePoly cone (Terminator.instantiate tbl subst term) = true := by
  rcases term with ⟨kind, span⟩
  cases kind <;> (try exact directCallInConePoly_instantiate h) <;> rfl

theorem Rvalue.calleeQueryFree_instantiate (tbl : LayoutTable) (subst : TypeSubst) (rv : Rvalue) :
    Rvalue.calleeQueryFree (Rvalue.instantiate tbl subst rv) = Rvalue.calleeQueryFree rv := by
  cases rv with
  | cast kind op targetTy => cases kind <;> rfl
  | _ => rfl

theorem Statement.calleeQueryFree_instantiate (tbl : LayoutTable) (subst : TypeSubst)
    (stmt : Statement) :
    Statement.calleeQueryFree (Statement.instantiate tbl subst stmt) =
      Statement.calleeQueryFree stmt := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign p rv => exact Rvalue.calleeQueryFree_instantiate tbl subst rv
  | _ => rfl

private theorem statement_instantiateList_all_calleeQueryFree (tbl : LayoutTable)
    (subst : TypeSubst) :
    ∀ (ss : List Statement),
      (Statement.instantiateList tbl subst ss).all Statement.calleeQueryFree =
        ss.all Statement.calleeQueryFree
  | [] => rfl
  | s :: rest => by
    simp only [Statement.instantiateList, List.all_cons, Statement.calleeQueryFree_instantiate,
      statement_instantiateList_all_calleeQueryFree tbl subst rest]

def bodyCallsInConePoly (cone : List DefPath) (b : CapturedMir) : Bool :=
  b.basicBlocks.all (fun blk =>
    blk.statements.all Statement.calleeQueryFree && termCallsInConePoly cone blk.terminator)

private theorem basicBlockData_instantiateList_all (cone : List DefPath) (tbl : LayoutTable)
    (subst : TypeSubst) :
    ∀ (bs : List BasicBlockData),
      bs.all (fun blk =>
        blk.statements.all Statement.calleeQueryFree && termCallsInConePoly cone blk.terminator) =
        true →
      (BasicBlockData.instantiateList tbl subst bs).all (fun blk =>
        blk.statements.all Statement.calleeQueryFree && termCallsInConePoly cone blk.terminator) =
        true
  | [], _ => rfl
  | blk :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [BasicBlockData.instantiateList, BasicBlockData.instantiate, List.all_cons,
      Bool.and_eq_true, statement_instantiateList_all_calleeQueryFree]
    exact ⟨⟨h.1.1, termCallsInConePoly_instantiate h.1.2⟩,
      basicBlockData_instantiateList_all cone tbl subst rest h.2⟩

/-- Monomorphizing a generic `CapturedMir` body via `CapturedMir.instantiate` preserves
`bodyCallsInConePoly`. -/
theorem bodyCallsInConePoly_instantiate {cone : List DefPath} {b : CapturedMir}
    (subst : TypeSubst) (h : bodyCallsInConePoly cone b = true) :
    bodyCallsInConePoly cone (b.instantiate subst) = true :=
  basicBlockData_instantiateList_all cone b.layouts subst b.basicBlocks h

/--
**Decidable polymorphic call-cone closure (`CallConeClosedPoly`).** Checks that `root` and every
body in `coneBodies cone c₁` satisfy `bodyCallsInConePoly cone` (allowing arbitrary `typeArgs` on
direct `.fnDef` calls to targets in `cone`), and that no target `dp ∈ cone` has a registered
`TraitImplEntry` in `ti ++ flatMapTraitImpls c₁`.
-/
def CallConeClosedPoly (cone : List DefPath) (root : CapturedMir) (c₁ : CalleeEnv)
    (ti : List TraitImplEntry := []) : Bool :=
  bodyCallsInConePoly cone root &&
    (coneBodies cone c₁).all (bodyCallsInConePoly cone) &&
    cone.all (fun dp => !hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₁) dp)

def InConeSetPoly (cone : List DefPath) (root : CapturedMir) (c₁ : CalleeEnv)
    (b : CapturedMir) : Prop :=
  b = root ∨ ∃ b₀ subst, b₀ ∈ coneBodies cone c₁ ∧ b = b₀.instantiate subst

theorem bodyCallsInConePoly_of_inConeSetPoly {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry} {b : CapturedMir}
    (h_closed : CallConeClosedPoly cone root c₁ ti = true)
    (hb : InConeSetPoly cone root c₁ b) : bodyCallsInConePoly cone b = true := by
  unfold CallConeClosedPoly at h_closed
  simp only [Bool.and_eq_true] at h_closed
  rcases hb with rfl | ⟨b₀, subst, hb₀, rfl⟩
  · exact h_closed.1.1
  · exact bodyCallsInConePoly_instantiate subst (List.all_eq_true.mp h_closed.1.2 b₀ hb₀)

theorem noTraitImpl_of_callConeClosedPoly {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry} {dp : DefPath}
    (h_closed : CallConeClosedPoly cone root c₁ ti = true) (h_dp : dp ∈ cone) :
    hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₁) dp = false := by
  unfold CallConeClosedPoly at h_closed
  simp only [Bool.and_eq_true] at h_closed
  have h := List.all_eq_true.mp h_closed.2 dp h_dp
  cases htr : hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₁) dp with
  | false => rfl
  | true => rw [htr] at h; cases h

/-- Polymorphic `lookupCallee` under `hasTraitImplForDefPath = false` returns either `b` or
`b.instantiate subst` for the entry `findCallee? c dp = some b`. -/
theorem lookupCallee_eq_some_of_no_traitImpl {c : CalleeEnv} {L : LayoutTable} {dp : DefPath}
    {typeArgs : List RigidTy} {ti : List TraitImplEntry} {calleeBody : CapturedMir}
    (h_no : hasTraitImplForDefPath (ti ++ flatMapTraitImpls c) dp = false)
    (h_lk : lookupCallee c L dp typeArgs ti = some calleeBody) :
    ∃ b subst, findCallee? c dp = some b ∧ calleeBody = b.instantiate subst := by
  unfold lookupCallee at h_lk
  rw [resolveCalleeBodyAndArgs?_eq_of_no_traitImpl c dp typeArgs ti h_no] at h_lk
  cases hf : findCallee? c dp with
  | none => rw [hf] at h_lk; cases h_lk
  | some b =>
    rw [hf] at h_lk
    dsimp only at h_lk
    split at h_lk
    · cases h_lk
      exact ⟨calleeBody, [], rfl, (CapturedMir.instantiate_nil calleeBody).symm⟩
    · split at h_lk
      · cases h_lk
      · split at h_lk
        · rename_i argLayouts _
          cases h_lk
          exact ⟨b, typeArgs.zip argLayouts, rfl, rfl⟩
        · cases h_lk

private theorem inConeSetPoly_of_lookup {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {L : LayoutTable} {dp : DefPath} {typeArgs : List RigidTy}
    {ti : List TraitImplEntry} {calleeBody : CapturedMir}
    (h_dp : dp ∈ cone)
    (h_no : hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₁) dp = false)
    (h_lk : lookupCallee c₁ L dp typeArgs ti = some calleeBody) :
    InConeSetPoly cone root c₁ calleeBody := by
  obtain ⟨b, subst, hf, hinst⟩ := lookupCallee_eq_some_of_no_traitImpl h_no h_lk
  obtain ⟨hm, hd⟩ := findCallee?_spec hf
  right
  refine ⟨b, subst, ?_, hinst⟩
  unfold coneBodies
  rw [List.mem_filter]
  exact ⟨hm, inCone_iff.mpr (hd ▸ h_dp)⟩

def ClosedInvPoly (cone : List DefPath) (root : CapturedMir) (c₁ : CalleeEnv)
    (ti : List TraitImplEntry) (s : MachineState) : Prop :=
  s.memory.callees = c₁ ∧ s.memory.traitImpls = ti ∧
    InConeSetPoly cone root c₁ (s.memory.activeCallee.getD root) ∧
    ∀ f, f ∈ s.memory.callStack → InConeSetPoly cone root c₁ f.callerBody

theorem stepConeSafePoly_of_closedInvPoly {cone : List DefPath} {root : CapturedMir}
    {c₁ c₂ : CalleeEnv} {ti : List TraitImplEntry} {s : MachineState}
    (h_closed : CallConeClosedPoly cone root c₁ ti = true)
    (h_no₂ : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₂) dp = false)
    (h_inv : ClosedInvPoly cone root c₁ ti s) :
    StepConeSafePoly cone c₂ root s := by
  intro blk h_bb
  have h_body := bodyCallsInConePoly_of_inConeSetPoly h_closed h_inv.2.2.1
  unfold bodyCallsInConePoly at h_body
  have h_blk := List.all_eq_true.mp h_body blk (mem_of_get? h_bb)
  rw [Bool.and_eq_true] at h_blk
  refine ⟨fun stmt h_st => List.all_eq_true.mp h_blk.1 stmt (mem_of_get? h_st), ?_⟩
  have h_tc := h_blk.2
  revert h_tc
  rcases blk.terminator with ⟨kind, span⟩
  intro h_tc
  cases kind with
  | call func argOps _ _ _ =>
    intro tgt l h_res
    unfold termCallsInConePoly directCallInConePoly at h_tc
    dsimp only at h_tc
    cases h_fn : extractFnDefPath? func with
    | none => rw [h_fn] at h_tc; cases h_tc
    | some dp =>
      rw [h_fn, Bool.and_eq_true] at h_tc
      have h_cd := extractCalleeDefPath?_of_extractFnDefPath? h_fn
      unfold resolveCallTarget at h_res
      rw [h_cd] at h_res
      cases h_res
      have h_dp : dp ∈ cone := inCone_iff.mp h_tc.1
      rw [h_inv.1, h_inv.2.1]
      exact ⟨h_dp, noTraitImpl_of_callConeClosedPoly h_closed h_dp, h_no₂ dp h_dp, h_tc.2⟩
  | tailCall func argOps =>
    intro tgt l h_res
    unfold termCallsInConePoly directCallInConePoly at h_tc
    dsimp only at h_tc
    cases h_fn : extractFnDefPath? func with
    | none => rw [h_fn] at h_tc; cases h_tc
    | some dp =>
      rw [h_fn, Bool.and_eq_true] at h_tc
      have h_cd := extractCalleeDefPath?_of_extractFnDefPath? h_fn
      unfold resolveCallTarget at h_res
      rw [h_cd] at h_res
      cases h_res
      have h_dp : dp ∈ cone := inCone_iff.mp h_tc.1
      rw [h_inv.1, h_inv.2.1]
      exact ⟨h_dp, noTraitImpl_of_callConeClosedPoly h_closed h_dp, h_no₂ dp h_dp, h_tc.2⟩
  | _ => trivial

theorem closedInvPoly_unwindFromCallStack {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry} :
    ∀ (stk : List SavedCallerFrame) (m : Memory), m.callees = c₁ → m.traitImpls = ti →
      (∀ f, f ∈ stk → InConeSetPoly cone root c₁ f.callerBody) →
      ∀ s', unwindFromCallStack stk m = .running s' → ClosedInvPoly cone root c₁ ti s'
  | [], _, _, _, _, _, h => by cases h
  | caller :: rest, m, hc, hti, hf, s', h => by
    unfold unwindFromCallStack at h
    dsimp only at h
    cases hr : caller.returnUnwind with
    | unreachable => rw [hr] at h; dsimp only at h; cases h
    | terminate => rw [hr] at h; dsimp only at h; cases h
    | continue_ =>
      rw [hr] at h
      dsimp only at h
      exact closedInvPoly_unwindFromCallStack rest
        { m with
          callStack := rest
          activeCallee := some caller.callerBody
          activeProtectors := restoreCallerProtectors caller }
        hc hti (fun f hm => hf f (List.Mem.tail _ hm)) s' h
    | cleanup bb =>
      rw [hr] at h
      dsimp only at h
      cases h
      exact ⟨hc, hti, hf caller (List.Mem.head _), fun f hm => hf f (List.Mem.tail _ hm)⟩

private theorem nodeSuccs_unwindMatchPoly {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry} (st : MirExecState)
    (h : ∀ s', st = .running s' → ClosedInvPoly cone root c₁ ti s') :
    NodeSuccs (ClosedInvPoly cone root c₁ ti)
      (match (generalizing := false) st with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  cases st with
  | running s' => exact h s' rfl
  | halted _ => trivial
  | faulted _ => trivial

private theorem nodeSuccs_applyUnwindPoly {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry} {s : MachineState}
    (h_inv : ClosedInvPoly cone root c₁ ti s) (l : List LocalSlot) (u : UnwindAction) :
    NodeSuccs (ClosedInvPoly cone root c₁ ti)
      (match applyUnwindAction s l s.memory u with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  refine nodeSuccs_unwindMatchPoly _ ?_
  intro s' hs'
  cases u with
  | unreachable => cases hs'
  | terminate => cases hs'
  | continue_ =>
    exact closedInvPoly_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.1
      h_inv.2.2.2 s' hs'
  | cleanup bb =>
    cases hs'
    exact h_inv

private theorem closedInvPoly_push {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {ti : List TraitImplEntry} {s : MachineState} {saved : SavedCallerFrame}
    {b : CapturedMir} {F : StackFrame} (h_inv : ClosedInvPoly cone root c₁ ti s)
    (h_saved : InConeSetPoly cone root c₁ saved.callerBody)
    (h_b : InConeSetPoly cone root c₁ b) :
    ClosedInvPoly cone root c₁ ti
      { frame := F,
        memory := { s.memory with
          callStack := saved :: s.memory.callStack
          activeCallee := some b } } := by
  refine ⟨h_inv.1, h_inv.2.1, h_b, ?_⟩
  intro f hf
  cases hf with
  | head => exact h_saved
  | tail _ hf => exact h_inv.2.2.2 f hf

/-- `ClosedInvPoly` transfers to any state with the same callee table, trait-impl table,
and active callee whose saved frames keep their bodies. -/
theorem closedInvPoly_of_callerBodies {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry} {s s' : MachineState}
    (h_inv : ClosedInvPoly cone root c₁ ti s)
    (hc : s'.memory.callees = s.memory.callees)
    (hti : s'.memory.traitImpls = s.memory.traitImpls)
    (hac : s'.memory.activeCallee = s.memory.activeCallee)
    (hb : CallerBodiesEq s.memory.callStack s'.memory.callStack) :
    ClosedInvPoly cone root c₁ ti s' := by
  refine ⟨hc.trans h_inv.1, hti.trans h_inv.2.1, hac ▸ h_inv.2.2.1, ?_⟩
  intro f hf
  obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
  exact he ▸ h_inv.2.2.2 f₀ hf₀

theorem nodeSuccs_closedInvPoly_of_ctx {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry} {s : MachineState} {n : MirStepNode}
    (h_inv : ClosedInvPoly cone root c₁ ti s)
    (hfix : n = MirStepNode.mapMem
      (Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls) n)
    (hb : NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack) n) :
    NodeSuccs (ClosedInvPoly cone root c₁ ti) n := by
  refine NodeSuccs.mono ?_
    (NodeSuccs.and
      (nodeSuccs_of_fixed (P := fun s' => s' = MachineState.mapMem
        (Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls) s')
        hfix (fun _ h => h))
      hb)
  rintro s' ⟨hs', hb'⟩
  have hm : s'.memory =
      Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls s'.memory :=
    congrArg MachineState.memory hs'
  exact closedInvPoly_of_callerBodies h_inv (by rw [hm]) (by rw [hm]) (by rw [hm]) hb'

theorem closedInvPoly_return {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {ti : List TraitImplEntry} {s : MachineState} {caller : SavedCallerFrame}
    {rest : List SavedCallerFrame} {retVal : Value} {locals' : List LocalSlot} {mem' : Memory}
    {F : StackFrame}
    (h_inv : ClosedInvPoly cone root c₁ ti s) (h_cs : s.memory.callStack = caller :: rest)
    (h_w : writeReturnDestination caller.frame.locals (ccReturnCallerMem s caller rest)
      caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts =
        .ok locals' mem') :
    ClosedInvPoly cone root c₁ ti { frame := F, memory := mem' } := by
  obtain ⟨hc, hac, hti⟩ := writeReturnDestination_ctx_preserved h_w
  have hb := writeReturnDestination_callerBodies h_w
  refine ⟨hc.trans h_inv.1, hti.trans h_inv.2.1, ?_, ?_⟩
  · show InConeSetPoly cone root c₁ (mem'.activeCallee.getD root)
    rw [hac]
    exact h_inv.2.2.2 caller (by rw [h_cs]; exact List.Mem.head _)
  · intro f hf
    obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
    exact he ▸ h_inv.2.2.2 f₀ (by rw [h_cs]; exact List.Mem.tail _ hf₀)

theorem nodeSuccs_evalStmtPoly {cone : List DefPath} {root : CapturedMir} {c₁ : CalleeEnv}
    {ti : List TraitImplEntry} {s : MachineState} {stmt : Statement}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h_inv : ClosedInvPoly cone root c₁ ti s) (h_free : Statement.calleeQueryFree stmt = true) :
    NodeSuccs (ClosedInvPoly cone root c₁ ti) (evalStmt s stmt localDecls layouts) :=
  nodeSuccs_closedInvPoly_of_ctx h_inv
    (evalStmt_calleeCtx_preserved s stmt localDecls layouts h_free)
    (evalStmt_callerBodies s stmt localDecls layouts)

theorem nodeSuccs_evalDirectRustIntrinsic?_poly {cone : List DefPath}
    {root : CapturedMir} {c₁ : CalleeEnv} {ti : List TraitImplEntry} {s : MachineState}
    (h_inv : ClosedInvPoly cone root c₁ ti s) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (h_cl : isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true)
    (fallback : MirStepNode) (h_fb : NodeSuccs (ClosedInvPoly cone root c₁ ti) fallback) :
    NodeSuccs (ClosedInvPoly cone root c₁ ti)
      (match evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb unwind with
       | some stepNode => stepNode
       | none => fallback) := by
  unfold evalDirectRustIntrinsic?
  cases h_k : classifyRustIntrinsic? target.defPath with
  | none => exact h_fb
  | some kind =>
    rw [h_k] at h_cl
    have h_step : ∀ (k : RustIntrinsicKind),
        NodeSuccs (ClosedInvPoly cone root c₁ ti)
          (evalNonSelectIntrinsicCall k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb) := by
      intro k
      exact nodeSuccs_closedInvPoly_of_ctx h_inv
        (evalNonSelectIntrinsicCall_calleeCtx_preserved k s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
        (evalNonSelectIntrinsicCall_callerBodies k s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
    cases kind with
    | constEvalSelect => cases h_cl
    | _ => exact h_step _

theorem nodeSuccs_evalTerminatorPoly {cone : List DefPath} {root : CapturedMir}
    {c₁ c₂ : CalleeEnv} {ti : List TraitImplEntry} {s : MachineState} {term : Terminator}
    (h_inv : ClosedInvPoly cone root c₁ ti s)
    (h_term : TermConeSafePoly cone c₂ s (s.memory.activeCallee.getD root) term) :
    NodeSuccs (ClosedInvPoly cone root c₁ ti)
      (evalTerminator s term (some (s.memory.activeCallee.getD root))) := by
  have h_cur : InConeSetPoly cone root c₁ (s.memory.activeCallee.getD root) := h_inv.2.2.1
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => exact h_inv
  | switchInt discr targets =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | unwindResume =>
    unfold evalTerminator; dsimp only
    exact nodeSuccs_unwindMatchPoly _
      (closedInvPoly_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.1 h_inv.2.2.2)
  | unwindTerminate => trivial
  | return_ =>
    rw [ccEvalReturn_eq]
    unfold ccEvalReturn
    repeat' (first | trivial | exact closedInvPoly_return h_inv ‹_› ‹_› | split)
  | unreachable => trivial
  | drop place target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | assert cond expected target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | exact nodeSuccs_applyUnwindPoly h_inv _ _ | split)
  | call func argOps destination target unwind =>
    have hq : CallTargetInConePoly cone c₂ s (s.memory.activeCallee.getD root) func
        (length argOps) := h_term
    cases target with
    | some targetBb =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_no₁, _, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath tgt.typeArgs s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1, h_inv.2.1] at h_lk h_no₁
              exact closedInvPoly_push h_inv h_cur (inConeSetPoly_of_lookup h_dp h_no₁ h_lk)
          | none =>
            dsimp only
            repeat' (first
              | trivial | exact h_inv
              | exact nodeSuccs_closedInvPoly_of_ctx h_inv
                  (writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                  (writeIntrinsicReturn_callerBodies _ _ _ _ _)
              | exact nodeSuccs_evalDirectRustIntrinsic?_poly h_inv _ _ _ _ _ _ _ _ _ _ h_cl _
                  (by
                    repeat' (first
                      | trivial | exact h_inv
                      | exact nodeSuccs_closedInvPoly_of_ctx h_inv
                          (writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                          (writeIntrinsicReturn_callerBodies _ _ _ _ _)
                      | split))
              | split)
    | none =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_no₁, _, _⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath tgt.typeArgs s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1, h_inv.2.1] at h_lk h_no₁
              exact closedInvPoly_push h_inv h_cur (inConeSetPoly_of_lookup h_dp h_no₁ h_lk)
          | none =>
            dsimp only
            repeat' (first | trivial | exact nodeSuccs_applyUnwindPoly h_inv _ _ | split)
  | tailCall func argOps =>
    have hq : CallTargetInConePoly cone c₂ s (s.memory.activeCallee.getD root) func
        (length argOps) := h_term
    unfold evalTerminator; dsimp only
    unfold evalTailCallTerminator; dsimp only
    cases h_res : resolveCallTarget s func (length argOps)
        (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
        (s.memory.activeCallee.getD root).layouts with
    | ub => trivial
    | unsupported => trivial
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, h_no₁, _, _⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
          (s.memory.activeCallee.getD root).layouts s.memory.callerLocals (callStack := s.memory.callStack) with
      | ub => trivial
      | unsupported => trivial
      | ok argVals locals' =>
        dsimp only
        cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
            tgt.defPath tgt.typeArgs s.memory.traitImpls with
        | some calleeBody =>
          dsimp only
          rw [h_inv.1, h_inv.2.1] at h_lk h_no₁
          repeat' (first
            | trivial
            | exact ⟨h_inv.1, h_inv.2.1, inConeSetPoly_of_lookup h_dp h_no₁ h_lk, h_inv.2.2.2⟩
            | split)
        | none =>
          dsimp only
          repeat' (first | trivial | split)
  | _ => trivial

theorem nodeSuccs_stepMirFnPoly {cone : List DefPath} {root : CapturedMir} {c₁ c₂ : CalleeEnv}
    {ti : List TraitImplEntry} {s : MachineState}
    (h_closed : CallConeClosedPoly cone root c₁ ti = true)
    (h_no₂ : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₂) dp = false)
    (h_inv : ClosedInvPoly cone root c₁ ti s) :
    NodeSuccs (ClosedInvPoly cone root c₁ ti) (stepMirFn root s) := by
  have h_safe := stepConeSafePoly_of_closedInvPoly h_closed h_no₂ h_inv
  unfold stepMirFn; dsimp only
  split
  · trivial
  · cases h_bb : get? (s.memory.activeCallee.getD root).basicBlocks s.frame.blockIdx with
    | none => trivial
    | some blk =>
      obtain ⟨h_stmt, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact nodeSuccs_evalStmtPoly h_inv (h_stmt stmt h_st)
      | none =>
        dsimp only
        by_cases h_end : (s.frame.stmtIdx == length blk.statements) = true
        · rw [if_pos h_end]
          exact nodeSuccs_evalTerminatorPoly h_inv h_term
        · rw [if_neg h_end]
          trivial

theorem coneReach_of_closedInvPoly {cone : List DefPath} {root : CapturedMir}
    {c₁ c₂ : CalleeEnv} {ti : List TraitImplEntry}
    (h_closed : CallConeClosedPoly cone root c₁ ti = true)
    (h_no₂ : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ flatMapTraitImpls c₂) dp = false) :
    ∀ (fuel : Nat) (s : MachineState), ClosedInvPoly cone root c₁ ti s →
      ConeReach root (StepConeSafePoly cone c₂ root) fuel (.running s)
  | 0, _, _ => trivial
  | fuel + 1, s, h_inv => by
    refine ⟨stepConeSafePoly_of_closedInvPoly h_closed h_no₂ h_inv, ?_⟩
    have h_succ := nodeSuccs_stepMirFnPoly h_closed h_no₂ h_inv
    revert h_succ
    cases stepMirFn root s with
    | ret _ => intro _; trivial
    | tau st' =>
      cases st' with
      | running s' => intro h; exact coneReach_of_closedInvPoly h_closed h_no₂ fuel s' h
      | halted _ => intro _; cases fuel <;> trivial
      | faulted _ => intro _; cases fuel <;> trivial
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _; trivial
      · intro h
        show ConeReach root _ fuel (k PUnit.unit)
        revert h
        show (match k PUnit.unit with
          | .running s' => ClosedInvPoly cone root c₁ ti s'
          | _ => True) → _
        cases k PUnit.unit with
        | running s' => intro h; exact coneReach_of_closedInvPoly h_closed h_no₂ fuel s' h
        | halted _ => intro _; cases fuel <;> trivial
        | faulted _ => intro _; cases fuel <;> trivial
      · intro _; trivial

theorem initMachineStateWithMemoryAndCallees_traitImpls_of_wf (body : CapturedMir)
    (args : List Value) (mem : Memory) {c : CalleeEnv} (h : CalleeInitWf body mem c) :
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c).memory.traitImpls =
      body.traitImpls := by
  cases c with
  | nil =>
    rcases h with hne | ⟨_, hti⟩
    · exact absurd rfl hne
    · exact hti
  | cons b r => rfl

theorem closedInvPoly_init_of_wf (cone : List DefPath) (body : CapturedMir) (args : List Value)
    (mem : Memory) {c₁ : CalleeEnv} (h₁ : CalleeInitWf body mem c₁)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    ClosedInvPoly cone body c₁ body.traitImpls
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) := by
  refine ⟨initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁,
    initMachineStateWithMemoryAndCallees_traitImpls_of_wf body args mem h₁, ?_, ?_⟩
  · cases c₁ <;> (
      show InConeSetPoly cone body _ (mem.activeCallee.getD body)
      rw [h_ac]
      exact Or.inl rfl)
  · intro f hf
    cases c₁ <;> (
      have hf' : f ∈ mem.callStack := hf
      rw [h_cs] at hf'
      cases hf')

/--
**Polymorphic syntactic call-cone narrowing (`runCfgWithCallees_cone_narrow_of_closed_poly_wf`)**:
if `CallConeClosedPoly cone body c₁ body.traitImpls = true` (decidable by `rfl` / `decide`), then
narrowing `c₁` to any `c₂` that agrees with `c₁` on `cone` and registers no `TraitImplEntry` for
any `dp ∈ cone` (including `c₂ = coneBodies cone c₁` and `c₂ = []`) commutes with
`runCfgWithCallees`, even when `body` or its callees execute polymorphic inline intrinsics or
monomorphized generic functions (`CapturedMir.instantiate`).
-/
theorem runCfgWithCallees_cone_narrow_of_closed_poly_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : CalleeInitWf body mem c₁) (h₂ : CalleeInitWf body mem c₂)
    (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ flatMapTraitImpls c₂) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    runCfgWithCallees fuel body args mem c₂ =
      (runCfgWithCallees fuel body args mem c₁).map (MirOutcome.mapMem (Memory.withCallees c₂)) := by
  unfold runCfgWithCallees
  rw [initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine runMirExecBounded_cone_narrow_poly cone body c₂ fuel _
    (coneReach_of_closedInvPoly h_closed h_no₂ fuel _
      (closedInvPoly_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact h_agree

theorem wpMirExecSym_cone_narrow_of_closed_poly_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : CalleeInitWf body mem c₁) (h₂ : CalleeInitWf body mem c₂)
    (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ flatMapTraitImpls c₂) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out) :
    wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₂))
        post ↔
      wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁))
        post := by
  rw [initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine wpMirExecSym_cone_narrow_poly cone body c₂ post h_post fuel _
    (coneReach_of_closedInvPoly h_closed h_no₂ fuel _
      (closedInvPoly_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact h_agree

theorem mirWpConverges_cone_narrow_of_closed_poly_wf (cone : List DefPath) (body : CapturedMir)
    (args : List Value) (mem : Memory) {c₁ c₂ : CalleeEnv}
    (h₁ : CalleeInitWf body mem c₁) (h₂ : CalleeInitWf body mem c₂)
    (h_agree : calleesAgreeOn cone c₁ c₂)
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ flatMapTraitImpls c₂) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees c₂) out) ↔ post out) :
    MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₂) post ↔
      MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) post := by
  rw [initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  have h_at : AgreesAt cone c₂
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁)) := by
    intro s hs
    cases hs
    rw [initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
    exact h_agree
  constructor
  · rintro ⟨fuel, h⟩
    exact ⟨fuel,
      (wpMirExecSym_cone_narrow_poly cone body c₂ post h_post fuel _
        (coneReach_of_closedInvPoly h_closed h_no₂ fuel _
          (closedInvPoly_init_of_wf cone body args mem h₁ h_ac h_cs))
        h_at).1 h⟩
  · rintro ⟨fuel, h⟩
    exact ⟨fuel,
      (wpMirExecSym_cone_narrow_poly cone body c₂ post h_post fuel _
        (coneReach_of_closedInvPoly h_closed h_no₂ fuel _
          (closedInvPoly_init_of_wf cone body args mem h₁ h_ac h_cs))
        h_at).2 h⟩

/-- `CallConeClosedPoly` also rules out trait-impl dispatch for every cone target in the
narrowed table `coneBodies cone c₁` (filtering never adds a `TraitImplEntry`). -/
theorem noTraitImpl_coneBodies_of_callConeClosedPoly {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry}
    (h_closed : CallConeClosedPoly cone root c₁ ti = true) :
    ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (ti ++ flatMapTraitImpls (coneBodies cone c₁)) dp = false := by
  intro dp hdp
  have h := noTraitImpl_of_callConeClosedPoly h_closed hdp
  rw [hasTraitImplForDefPath_append, Bool.or_eq_false_iff] at h ⊢
  exact ⟨h.1, hasTraitImplForDefPath_flatMapTraitImpls_coneBodies cone c₁ dp h.2⟩

/--
**Decidable polymorphic narrowing to the call cone (`runCfgWithCallees`).** The single
`rfl`/`decide`-checkable condition `CallConeClosedPoly cone body c₁ body.traitImpls = true`
discharges *both* side conditions of `runCfgWithCallees_cone_narrow_of_closed_poly_wf` (cone
agreement and absence of trait-impl dispatch in the narrowed table) for `c₂ := coneBodies cone c₁`.
-/
theorem runCfgWithCallees_coneBodies_narrow_of_closed_poly (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {c₁ : CalleeEnv}
    (h₁ : CalleeInitWf body mem c₁) (h₂ : CalleeInitWf body mem (coneBodies cone c₁))
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    runCfgWithCallees fuel body args mem (coneBodies cone c₁) =
      (runCfgWithCallees fuel body args mem c₁).map
        (MirOutcome.mapMem (Memory.withCallees (coneBodies cone c₁))) :=
  runCfgWithCallees_cone_narrow_of_closed_poly_wf cone fuel body args mem h₁ h₂
    (calleesAgreeOn_coneBodies cone c₁) h_closed
    (noTraitImpl_coneBodies_of_callConeClosedPoly h_closed) h_ac h_cs

/-- **Decidable polymorphic narrowing to the call cone (`wpMirExecSym`).** -/
theorem wpMirExecSym_coneBodies_narrow_of_closed_poly (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {c₁ : CalleeEnv}
    (h₁ : CalleeInitWf body mem c₁) (h₂ : CalleeInitWf body mem (coneBodies cone c₁))
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees (coneBodies cone c₁)) out) ↔
      post out) :
    wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          (coneBodies cone c₁))) post ↔
      wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          c₁)) post :=
  wpMirExecSym_cone_narrow_of_closed_poly_wf cone fuel body args mem h₁ h₂
    (calleesAgreeOn_coneBodies cone c₁) h_closed
    (noTraitImpl_coneBodies_of_callConeClosedPoly h_closed) h_ac h_cs post h_post

/-- **Decidable polymorphic narrowing to the call cone (`MirWpConverges`).** -/
theorem mirWpConverges_coneBodies_narrow_of_closed_poly (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) {c₁ : CalleeEnv}
    (h₁ : CalleeInitWf body mem c₁) (h₂ : CalleeInitWf body mem (coneBodies cone c₁))
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees (coneBodies cone c₁)) out) ↔
      post out) :
    MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          (coneBodies cone c₁)) post ↔
      MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) post :=
  mirWpConverges_cone_narrow_of_closed_poly_wf cone body args mem h₁ h₂
    (calleesAgreeOn_coneBodies cone c₁) h_closed
    (noTraitImpl_coneBodies_of_callConeClosedPoly h_closed) h_ac h_cs post h_post

/-- Any clean entry memory (`mem.callees = []` and `mem.traitImpls = body.traitImpls`, e.g.
`emptyMemory` when `body.traitImpls = []`) satisfies `CalleeInitWf` for every `c : CalleeEnv`
(both non-empty and empty `[]`). -/
theorem calleeInitWf_of_clean_mem (body : CapturedMir) (mem : Memory) (c : CalleeEnv)
    (h_mc : mem.callees = []) (h_mti : mem.traitImpls = body.traitImpls) :
    CalleeInitWf body mem c :=
  Or.inr ⟨h_mc, h_mti⟩

/-- **Uniform `rfl`-checkable polymorphic narrowing to `coneBodies cone c₁` (`runCfgWithCallees`)**:
works uniformly whether `coneBodies cone c₁` is non-empty or empty (`[]`). -/
theorem runCfgWithCallees_coneBodies_narrow_of_closed_poly_clean (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) (c₁ : CalleeEnv)
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_mc : mem.callees = []) (h_mti : mem.traitImpls = body.traitImpls)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    runCfgWithCallees fuel body args mem (coneBodies cone c₁) =
      (runCfgWithCallees fuel body args mem c₁).map
        (MirOutcome.mapMem (Memory.withCallees (coneBodies cone c₁))) :=
  runCfgWithCallees_coneBodies_narrow_of_closed_poly cone fuel body args mem
    (calleeInitWf_of_clean_mem body mem c₁ h_mc h_mti)
    (calleeInitWf_of_clean_mem body mem (coneBodies cone c₁) h_mc h_mti)
    h_closed h_ac h_cs

/-- **Uniform `rfl`-checkable polymorphic narrowing to `coneBodies cone c₁` (`wpMirExecSym`)**. -/
theorem wpMirExecSym_coneBodies_narrow_of_closed_poly_clean (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) (c₁ : CalleeEnv)
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_mc : mem.callees = []) (h_mti : mem.traitImpls = body.traitImpls)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees (coneBodies cone c₁)) out) ↔
      post out) :
    wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          (coneBodies cone c₁))) post ↔
      wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          c₁)) post :=
  wpMirExecSym_coneBodies_narrow_of_closed_poly cone fuel body args mem
    (calleeInitWf_of_clean_mem body mem c₁ h_mc h_mti)
    (calleeInitWf_of_clean_mem body mem (coneBodies cone c₁) h_mc h_mti)
    h_closed h_ac h_cs post h_post

/-- **Uniform `rfl`-checkable polymorphic narrowing to `coneBodies cone c₁` (`MirWpConverges`)**. -/
theorem mirWpConverges_coneBodies_narrow_of_closed_poly_clean (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) (c₁ : CalleeEnv)
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_mc : mem.callees = []) (h_mti : mem.traitImpls = body.traitImpls)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees (coneBodies cone c₁)) out) ↔
      post out) :
    MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          (coneBodies cone c₁)) post ↔
      MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) post :=
  mirWpConverges_coneBodies_narrow_of_closed_poly cone body args mem
    (calleeInitWf_of_clean_mem body mem c₁ h_mc h_mti)
    (calleeInitWf_of_clean_mem body mem (coneBodies cone c₁) h_mc h_mti)
    h_closed h_ac h_cs post h_post

theorem calleesAgreeOn_nil_of_coneBodies_eq_nil {cone : List DefPath} {c₁ : CalleeEnv}
    (h_nil : coneBodies cone c₁ = []) : calleesAgreeOn cone c₁ [] :=
  h_nil ▸ calleesAgreeOn_coneBodies cone c₁

theorem noTraitImpl_nil_of_callConeClosedPoly {cone : List DefPath} {root : CapturedMir}
    {c₁ : CalleeEnv} {ti : List TraitImplEntry}
    (h_closed : CallConeClosedPoly cone root c₁ ti = true) :
    ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (ti ++ flatMapTraitImpls []) dp = false := by
  intro dp hdp
  have h := noTraitImpl_of_callConeClosedPoly h_closed hdp
  rw [hasTraitImplForDefPath_append, Bool.or_eq_false_iff] at h ⊢
  exact ⟨h.1, rfl⟩

/-- **Direct polymorphic narrowing to the empty callee table `[]` (`runCfgWithCallees`)** when
`coneBodies cone c₁ = []` (e.g. functions calling only polymorphic inline intrinsics such as
`size_of_val::<[u32]>` or `align_of_val::<[u32]>`). -/
theorem runCfgWithCallees_nil_narrow_of_closed_poly_clean (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) (c₁ : CalleeEnv)
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_nil : coneBodies cone c₁ = [])
    (h_mc : mem.callees = []) (h_mti : mem.traitImpls = body.traitImpls)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    runCfgWithCallees fuel body args mem [] =
      (runCfgWithCallees fuel body args mem c₁).map
        (MirOutcome.mapMem (Memory.withCallees [])) :=
  runCfgWithCallees_cone_narrow_of_closed_poly_wf cone fuel body args mem
    (calleeInitWf_of_clean_mem body mem c₁ h_mc h_mti)
    (calleeInitWf_of_clean_mem body mem [] h_mc h_mti)
    (calleesAgreeOn_nil_of_coneBodies_eq_nil h_nil) h_closed
    (noTraitImpl_nil_of_callConeClosedPoly h_closed) h_ac h_cs

/-- **Direct polymorphic narrowing to the empty callee table `[]` (`wpMirExecSym`)**. -/
theorem wpMirExecSym_nil_narrow_of_closed_poly_clean (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) (c₁ : CalleeEnv)
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_nil : coneBodies cone c₁ = [])
    (h_mc : mem.callees = []) (h_mti : mem.traitImpls = body.traitImpls)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees []) out) ↔ post out) :
    wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          [])) post ↔
      wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          c₁)) post :=
  wpMirExecSym_cone_narrow_of_closed_poly_wf cone fuel body args mem
    (calleeInitWf_of_clean_mem body mem c₁ h_mc h_mti)
    (calleeInitWf_of_clean_mem body mem [] h_mc h_mti)
    (calleesAgreeOn_nil_of_coneBodies_eq_nil h_nil) h_closed
    (noTraitImpl_nil_of_callConeClosedPoly h_closed) h_ac h_cs post h_post

/-- **Direct polymorphic narrowing to the empty callee table `[]` (`MirWpConverges`)**. -/
theorem mirWpConverges_nil_narrow_of_closed_poly_clean (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) (c₁ : CalleeEnv)
    (h_closed : CallConeClosedPoly cone body c₁ body.traitImpls = true)
    (h_nil : coneBodies cone c₁ = [])
    (h_mc : mem.callees = []) (h_mti : mem.traitImpls = body.traitImpls)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out, post (MirOutcome.mapMem (Memory.withCallees []) out) ↔ post out) :
    MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem []) post ↔
      MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c₁) post :=
  mirWpConverges_cone_narrow_of_closed_poly_wf cone body args mem
    (calleeInitWf_of_clean_mem body mem c₁ h_mc h_mti)
    (calleeInitWf_of_clean_mem body mem [] h_mc h_mti)
    (calleesAgreeOn_nil_of_coneBodies_eq_nil h_nil) h_closed
    (noTraitImpl_nil_of_callConeClosedPoly h_closed) h_ac h_cs post h_post

end CallConeNarrowing

end Anneal.MirLiftCore
