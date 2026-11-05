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
Memory after `TerminatorKind.call` inlines `calleeBody` from the caller frame
`(bbIdx, stmtIdx)` of `callerBody`: the caller frame, with locals `callerEnv`
after argument evaluation, is pushed onto `mem.callStack` and `calleeBody`
becomes the active body. This is `(pushCalleeFrame ..).memory` written out.
-/
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
Memory after `TerminatorKind.return_` pops `caller` (with remaining stack
`rest`) and resumes `caller.callerBody`.
-/
def returnFrameMem (mem : Memory) (caller : SavedCallerFrame)
    (rest : List SavedCallerFrame) : Memory :=
  { mem with
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
  Function-pointer reification `dst = op as fn(..) (PointerCoercion(ck))`.

  The premises are the success path of the trusted `evalReifyFnPointer`: `op`
  is a zero-sized function item whose type names `(defPath, typeArgs)`, the
  target type is a non-intrinsic `fn` pointer whose safety the coercion admits,
  the linked callee (if any) has a matching signature (`checkCalleeSig`, which
  instantiates a generic callee with `typeArgs`), and `internFnPtr` returns the
  synthetic `allocId`. The remaining premises are the trusted assignment to an
  unprojected live local with no active protectors.
  -/
  | reifyFnPointer {dst : Place} {coercionKind : String} {op : Operand}
      {targetTy : Ty} {span : String} {fnItem : Value} {env₁ env₂ : PureEnv}
      {fnInputs : List RigidTy} {fnOutput : RigidTy} {fnSafety : Safety}
      {fnAbi : CallConv} {defPath : DefPath} {typeArgs : List RigidTy}
      {allocId : AllocId} {mem₁ : Memory} {slot : LocalSlot} :
      isReifyFnPointerCoercion coercionKind = true →
      stringEq coercionKind "UnsafeFnPointer" = false →
      evalOperand env op mem.borrows mem.globals cur.layouts mem.callerLocals =
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
      dst.projection = [] →
      get? env₁ dst.local_ = some slot →
      slotLive slot = true →
      set? env₁ dst.local_ (.init (.ptr { allocId := allocId, offsetBytes := 0 } 8)) =
        some env₂ →
      mem₁.activeProtectors = [] →
      post env₂
        { mem₁ with borrows := invalidateConflictingBorrows mem₁.borrows dst.local_ .none } →
      LiftStmtMem cur bbIdx stmtIdx env mem post
        { kind := .assign dst (.cast (.pointerCoercion coercionKind) op targetTy),
          span := span }

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

The call constructors cover inlined calls to linked callees: `callDirect` for
function-item constants (including generic items such as `f::<u32>`, whose
`typeArgs` drive `lookupCallee`'s instantiation) and `callIndirect` for calls
through a reified function pointer, resolved via `Memory.fnPtrs` exactly as in
`resolveCallTarget_indirect_fnPtr`. Calls to unlinked callees emit `MirCallE`,
whose answers may abort, so they cannot meet a panic-forbidding postcondition
and have no constructor.
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
      evalOperand env discr mem.borrows mem.globals cur.layouts mem.callerLocals =
        .ok (.scalar sc) env' →
      post (.frame (lookupSwitchTarget sc.bits targets.branches targets.otherwise)
        0 env' mem) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .switchInt discr targets, span := span }
  | assert {cond : Operand} {expected : Bool} {target : BasicBlockIdx}
      {unwind : UnwindAction} {span : String} {sc : ScalarInt} {env' : PureEnv} :
      evalOperand env cond mem.borrows mem.globals cur.layouts mem.callerLocals =
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
  /-- Return from the root frame (empty call stack). -/
  | return_ {span : String} {retVal : Value} :
      get? env 0 = some (.init retVal) →
      mem.callStack = [] →
      post (.ret retVal) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .return_, span := span }
  /--
  Return from an inlined callee: write `_0` into the saved caller's
  `destination` and resume the caller at its return target.
  -/
  | returnToCaller {span : String} {retVal : Value} {caller : SavedCallerFrame}
      {rest : List SavedCallerFrame} {callerEnv : PureEnv} :
      get? env 0 = some (.init retVal) →
      mem.callStack = caller :: rest →
      caller.isDiverging = false →
      writePlaceValue caller.frame.locals mem.borrows caller.destination retVal =
        .ok callerEnv →
      post (.frame caller.returnTarget 0 callerEnv (returnFrameMem mem caller rest)) →
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
      evalOperands env argOps mem.borrows mem.globals cur.layouts mem.callerLocals =
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
      evalOperand env func mem.borrows mem.globals cur.layouts mem.callerLocals =
        .ok (.ptr ptrVal 8) envAfterFunc →
      ptrVal.offsetBytes = 0 →
      lookupBorrow mem.borrows ptrVal.tag = none →
      lookupFnPtr mem.fnPtrs ptrVal.allocId = some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps)
          (operandTy cur.localDecls cur.layouts func) = true →
      evalOperands envAfterFunc argOps mem.borrows mem.globals cur.layouts
          mem.callerLocals =
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
    (h_op : evalOperand env op mem.borrows mem.globals layouts mem.callerLocals =
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
  | reifyFnPointer h_kind h_unsafe h_op h_zst h_ty h_abi h_safety h_target
      h_sig h_intern h_proj h_slot h_live h_set h_prot h_next =>
    rename_i dst coercionKind op targetTy span fnItem env₁ env₂ fnInputs fnOutput
      fnSafety fnAbi defPath typeArgs allocId mem₁ slot
    have h_rv :
        evalRvalue env (.cast (.pointerCoercion coercionKind) op targetTy) mem
            cur.localDecls cur.layouts =
          .ok (.ptr { allocId := allocId, offsetBytes := 0 } 8) env₁ mem₁ :=
      evalRvalue_reifyFnPointer h_kind h_unsafe h_op h_zst h_ty h_abi h_safety
        h_target h_sig h_intern
    rcases dst with ⟨dstLoc, dstProj⟩
    dsimp only at h_proj h_slot h_set h_next
    subst h_proj
    show evalNodeWP _ _ (evalStmt _ _ _ _)
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    rw [h_rv]
    dsimp only []
    rw [h_slot]
    cases slot with
    | dead => cases h_live
    | uninit =>
      dsimp only []
      rw [h_set]
      dsimp only []
      rw [h_prot] at h_next ⊢
      exact h_next
    | init _ =>
      dsimp only []
      rw [h_set]
      dsimp only []
      rw [h_prot] at h_next ⊢
      exact h_next

/--
Statement step on an activation frame: a `LiftStmtMem` step of the active body
`cur` refines `wpMirExecSym` by one unit of fuel.
-/
theorem LiftFrame.stmt {body cur : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {mem : Memory} {blk : BasicBlockData}
    {stmt : Statement} {post : Value → Prop} {fuel : Nat}
    (h_cur : mem.activeCallee.getD body = cur)
    (h_phase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (h_bb : get? cur.basicBlocks bbIdx = some blk)
    (h_get : get? blk.statements stmtIdx = some stmt)
    (h_lift : LiftStmtMem cur bbIdx stmtIdx env mem
      (fun env' mem' => LiftFrame body bbIdx (stmtIdx + 1) env' mem' post fuel) stmt) :
    LiftFrame body bbIdx stmtIdx env mem post (fuel + 1) :=
  LiftFrame.of_stepMirFn (stepMirFn_frame_stmt h_cur h_phase h_bb h_get)
    (LiftStmtMem.evalNodeWP_of h_lift)

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
  | return_ h_ret h_stack h_post =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_ret]
    dsimp only []
    rw [h_stack]
    exact h_post
  | returnToCaller h_ret h_stack h_div h_write h_next =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_ret]
    dsimp only []
    rw [h_stack]
    dsimp only []
    rw [h_div]
    dsimp only []
    rw [h_write]
    exact h_next
  | callDirect h_callee h_args h_ctx h_next =>
    rename_i func argOps destination targetBb unwind span defPath typeArgs argVals
      env' calleeBody
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
    have h_res :
        resolveCallTarget
            (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
            func (length argOps) cur.localDecls cur.layouts =
          .ok { defPath := defPath, typeArgs := typeArgs, fnSig := none,
                isIndirect := false } env := by
      unfold resolveCallTarget
      rw [h_path, h_args']
      rfl
    have h_tree :=
      evalTerminatorSymTree_call_inlined_of_calleeCtx
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func argOps destination targetBb unwind span cur _ env argVals env' calleeBody
        h_res h_args h_ctx (checkCalleeTargetCompatible_direct _ _ _ _ _)
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

/--
Terminator step on an activation frame: a `LiftTerminator` step of the active
body `cur` refines `wpMirExecSym` by one unit of fuel.
-/
theorem LiftFrame.term {body cur : CapturedMir} {bbIdx : BasicBlockIdx}
    {stmtIdx : Nat} {env : PureEnv} {mem : Memory} {blk : BasicBlockData}
    {post : Value → Prop} {fuel : Nat}
    (h_cur : mem.activeCallee.getD body = cur)
    (h_phase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (h_bb : get? cur.basicBlocks bbIdx = some blk)
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
