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
    (dst : Place) (val : Value) : Option (PureEnv × List BorrowEntry) :=
  match dst.projection with
  | [] =>
    match get? locals dst.local_ with
    | some .dead => none
    | some _ =>
      match set? locals dst.local_ (.init val) with
      | some locals' =>
        some (locals', invalidateConflictingBorrows borrows dst.local_ .none)
      | none => none
    | none => none
  | .deref :: _ => none
  | proj :: rest =>
    match get? locals dst.local_ with
    | some (.init rootVal) =>
      match writeProjectedValue locals rootVal (proj :: rest) val with
      | .ok rootVal' =>
        match set? locals dst.local_ (.init rootVal') with
        | some locals' =>
          let resolvedLocalProj :=
            match resolveBorrowProjectionElems locals (proj :: rest) with
            | some rp => rp
            | none => proj :: rest
          some (locals',
            invalidateConflictingBorrowsAtProj borrows dst.local_ .none
              resolvedLocalProj)
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
def tailCallFrameMem (mem : Memory) (calleeBody : CapturedMir) : Memory :=
  { mem with activeCallee := some calleeBody }

/--
Memory after `TerminatorKind.return_` pops `caller` (with remaining stack
`rest`) and resumes `caller.callerBody`.
-/
@[reducible]
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
      assignLocalPlace env₁ mem₁.borrows dst
          (.ptr { allocId := allocId, offsetBytes := 0 } 8) =
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
      assignLocalPlace env₁ mem.borrows dst (.ptr ptrVal 8) =
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
      assignLocalPlace env₁ mem.borrows dst (.ptr ptrVal 8) =
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
    (h_proj : dst.projection = [])
    (h_slot : get? env₁ dst.local_ = some slot)
    (h_live : slotLive slot = true)
    (h_set : set? env₁ dst.local_ (.init val) = some env₂) :
    assignLocalPlace env₁ borrows dst val =
      some (env₂, invalidateConflictingBorrows borrows dst.local_ .none) := by
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
      evalOperand env op mem.borrows mem.globals cur.layouts mem.callerLocals =
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
        { mem₁ with borrows := invalidateConflictingBorrows mem₁.borrows dst.local_ .none }) :
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
  Inlined call of a zero-sized function item (`RigidTy.fnDef`) held in a local
  or projected operand `func`.
  -/
  | callFnItem {func : Operand} {argOps : List Operand} {destination : Place}
      {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
      {fnVal : Value} {envAfterFunc : PureEnv} {defPath : DefPath}
      {typeArgs : List RigidTy} {argVals : List Value} {env' : PureEnv}
      {calleeBody : CapturedMir} :
      extractCalleeDefPath? func = none →
      evalOperand env func mem.borrows mem.globals cur.layouts mem.callerLocals =
        .ok fnVal envAfterFunc →
      isZstFnItemValue fnVal = true →
      extractFnItemTarget? (operandTy cur.localDecls cur.layouts func) =
        some (defPath, typeArgs) →
      evalOperands envAfterFunc argOps mem.borrows mem.globals cur.layouts
          mem.callerLocals =
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
          cur.layouts mem.callerLocals =
        .ok [.scalar lhs, .scalar rhs] env' →
      lookupCallee mem.callees cur.layouts resolvedTarget.defPath
          resolvedTarget.typeArgs mem.traitImpls = none →
      isDirectExactDivTarget resolvedTarget = true →
      resolveIntrinsicIsSigned resolvedTarget cur.localDecls cur.layouts
          (lhsOp :: rhsOps) = some isSigned →
      evalExactDiv lhs rhs isSigned = some retScalar →
      writePlaceValue env' mem.borrows destination (.scalar retScalar) =
        .ok updatedEnv →
      post (.frame targetBb 0 updatedEnv mem) →
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
      evalOperands env argOps mem.borrows mem.globals cur.layouts mem.callerLocals =
        .ok argVals env' →
      CalleeCtx mem.callees cur.layouts defPath typeArgs mem.traitImpls calleeBody →
      post (.frame 0 0 (initLocals calleeBody argVals)
        (tailCallFrameMem mem calleeBody)) →
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
      evalOperand env func mem.borrows mem.globals cur.layouts mem.callerLocals =
        .ok fnVal envAfterFunc →
      isZstFnItemValue fnVal = true →
      extractFnItemTarget? (operandTy cur.localDecls cur.layouts func) =
        some (defPath, typeArgs) →
      evalOperands envAfterFunc argOps mem.borrows mem.globals cur.layouts
          mem.callerLocals =
        .ok argVals env' →
      CalleeCtx mem.callees cur.layouts defPath typeArgs mem.traitImpls calleeBody →
      post (.frame 0 0 (initLocals calleeBody argVals)
        (tailCallFrameMem mem calleeBody)) →
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
        (tailCallFrameMem mem calleeBody)) →
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
    (h_write : assignLocalPlace env₁ mem₁.borrows dst val = some (env₂, borrows')) :
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
             cases h_wp : writeProjectedValue env₁ rootVal (_ :: rest) val with
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
          bodyLayouts s.memory.callerLocals =
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
    dsimp only []
    rw [h_write]
    exact h_next
  | tailCallDirect h_callee h_args h_ctx h_next =>
    rename_i func argOps span defPath typeArgs argVals env' calleeBody
    have h_res :=
      resolveCallTarget_of_extractCallee
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func (length argOps) cur.localDecls cur.layouts defPath typeArgs h_callee
    have h_tree :=
      evalTerminatorSymTree_tailCall_inlined_of_calleeCtx
        (PureState.toMachineState { bb := bbIdx, stmtIdx := stmtIdx, env := env } mem)
        func argOps span cur _ env argVals env' calleeBody h_res h_args h_ctx
        (checkCalleeTargetCompatible_direct _ _ _ _ _)
    rw [← evalTerminatorSymTree_eval, h_tree]
    exact h_next
  | tailCallFnItem h_const h_func h_zst h_target h_args h_ctx h_next =>
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
        h_ctx (checkCalleeTargetCompatible_direct _ _ _ _ _)
    rw [← evalTerminatorSymTree_eval, h_tree]
    exact h_next
  | tailCallIndirect h_const h_func h_off h_noBorrow h_fnPtr h_compat h_args
      h_ctx h_target h_next =>
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
        h_ctx h_target
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
    (writeRangeOff writeRangeLen : Nat) :
    hasProtectedWriteConflict borrows .nil targetLocal writerTag writeProj writeRangeOff writeRangeLen = false := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    unfold hasProtectedWriteConflict
    rw [isBorrowProtected_nil]
    dsimp only [Bool.and]
    cases Nat.beq entry.targetLocal targetLocal <;>
      cases borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen <;>
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
    (layouts : LayoutTable) (callerLocals : List LocalSlot) : PlaceReadResult :=
  evalOperand locals op borrows globals layouts callerLocals

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
    (callerLocals : List LocalSlot) : PlaceReadResult :=
  match op with
  | .constant c =>
    match c.val with
    | .indirect _ _ =>
      evalOperandFallback locals (.constant c) borrows globals body.layouts callerLocals
    | .unevaluated _ => .unsupported
    | cv =>
      match evalConstValue cv c.ty globals body.layouts with
      | .some v => .ok v locals
      | .none => .unsupported
  | .copy p =>
    match p.projection with
    | .deref :: restProj =>
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
    | _ =>
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
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue locals rootVal (.field idx ty :: rest) with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
    | _ => evalOperandFallback locals (.move p) borrows globals body.layouts callerLocals

theorem evalOperandFast_eq (body : CapturedMir) (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) :
    evalOperandFast body locals op borrows globals callerLocals =
      evalOperand locals op borrows globals body.layouts callerLocals := by
  cases op with
  | constant c =>
    rcases c with ⟨ty, val⟩
    cases val <;> rfl
  | copy p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil => rfl
    | cons hd _ => cases hd <;> rfl
  | move p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil => rfl
    | cons hd _ => cases hd <;> rfl

def evalOperandsFast
    (body : CapturedMir) (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) : OperandsEvalResult :=
  match ops with
  | .nil => .ok .nil locals
  | op :: rest =>
    match evalOperandFast body locals op borrows globals callerLocals with
    | .ok v locals₁ =>
      match evalOperandsFast body locals₁ rest borrows globals callerLocals with
      | .ok vs locals₂ => .ok (v :: vs) locals₂
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported

theorem evalOperandsFast_eq
    (body : CapturedMir) (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) :
    evalOperandsFast body locals ops borrows globals callerLocals =
      evalOperands locals ops borrows globals body.layouts callerLocals := by
  induction ops generalizing locals with
  | nil => rfl
  | cons op rest ih =>
    change
      (match evalOperandFast body locals op borrows globals callerLocals with
       | .ok v locals₁ =>
         match evalOperandsFast body locals₁ rest borrows globals callerLocals with
         | .ok vs locals₂ => OperandsEvalResult.ok (v :: vs) locals₂
         | .ub => OperandsEvalResult.ub
         | .unsupported => OperandsEvalResult.unsupported
       | .ub => OperandsEvalResult.ub
       | .unsupported => OperandsEvalResult.unsupported) =
      (match evalOperand locals op borrows globals body.layouts callerLocals with
       | .ok v locals₁ =>
         match evalOperands locals₁ rest borrows globals body.layouts callerLocals with
         | .ok vs locals₂ => OperandsEvalResult.ok (v :: vs) locals₂
         | .ub => OperandsEvalResult.ub
         | .unsupported => OperandsEvalResult.unsupported
       | .ub => OperandsEvalResult.ub
       | .unsupported => OperandsEvalResult.unsupported)
    rw [evalOperandFast_eq]
    cases evalOperand locals op borrows globals body.layouts callerLocals with
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
  match rigidTyByteSize body.layouts targetTy with
  | .none => .unsupported
  | .some dstSize =>
    match operandTy body.localDecls body.layouts op with
    | .some srcTy =>
      match rigidTyByteSize body.layouts srcTy with
      | .none => .unsupported
      | .some srcSize =>
        match Nat.beq srcSize dstSize with
        | false => .unsupported
        | true =>
          let encodedOpt : Option (List AbstractByte) :=
            match encodeValueToBytes defaultCodecFuel body.layouts srcTy v with
            | .some bs => .some bs
            | .none => encodeUntypedValueToBytes defaultCodecFuel v
          match encodedOpt with
          | .none => .ub
          | .some bs =>
            match Nat.beq (length bs) dstSize with
            | false => .ub
            | true =>
              match decodeValueFromBytes defaultCodecFuel body.layouts targetTy bs with
              | .some v' => .ok v' locals' mem
              | .none => .ub
    | .none =>
      match encodeUntypedValueToBytes defaultCodecFuel v with
      | .none => .unsupported
      | .some bs =>
        match Nat.beq (length bs) dstSize with
        | false => .unsupported
        | true =>
          match decodeValueFromBytes defaultCodecFuel body.layouts targetTy bs with
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
    match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals with
    | .ok v locals' =>
      match op, mem.borrows with
      | .copy { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
        .ok v locals'
          { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) }
      | .move { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
        .ok v locals'
          { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) }
      | _, _ => .ok v locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast ck op targetTy =>
    match ck with
    | .intToInt =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals with
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
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals with
      | .ub => .ub
      | .unsupported => .unsupported
      | .ok v locals' =>
        evalByteCastAfterOperand body op targetTy v locals' mem
    | _ => evalRvalueFallback locals (.cast ck op targetTy) mem body.localDecls body.layouts
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandFast body locals lhsOp mem.borrows mem.globals mem.callerLocals with
    | .ok lhsVal locals₁ =>
      match evalOperandFast body locals₁ rhsOp mem.borrows mem.globals mem.callerLocals with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          let isSigned := operandIsSigned body.localDecls lhsOp body.layouts
          evalScalarBinOp op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            evalPtrOffsetBinOp locals₂ mem body.localDecls body.layouts lhsOp ptrVal sz offsetSc
          | _ => .unsupported
        | _, _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .unaryOp uop op =>
    match uop with
    | .not =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals with
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
    cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals <;> rfl
  | cast ck op targetTy =>
    cases ck with
    | intToInt =>
      dsimp only [evalRvalueFast, evalRvalue]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | transmute =>
      dsimp only [evalRvalueFast, evalRvalue, evalByteCast]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals <;> rfl
    | _ => rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueFast, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals lhsOp mem.borrows mem.globals body.layouts mem.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [evalOperandFast_eq]
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals body.layouts mem.callerLocals <;> rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalueFast, evalRvalue]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals with
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
    match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals with
    | .ok v locals' =>
      .leaf (match op, mem.borrows with
      | .copy { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
        .ok v locals'
          { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) }
      | .move { local_ := ptrLoc, projection := .deref :: restProj }, b₁ :: b₂ :: restBorrows =>
        .ok v locals'
          { mem with borrows := freezeDerefReadBorrowsAt locals ptrLoc restProj (b₁ :: b₂ :: restBorrows) }
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
        }
        let mem' := {
          mem with
          borrows := entry :: mem.borrows
          nextTag := Nat.add tag 1
        }
        .leaf (.ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem')
    | _, _ => .leaf (evalRvalueFallback locals (.ref bk p) mem body.localDecls body.layouts)
  | .cast .transmute op targetTy =>
    match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals with
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
    | .ok v locals' =>
      .leaf (evalByteCastAfterOperand body op targetTy v locals' mem)
  | .aggregate ak ops =>
    match ak with
    | .tuple =>
      match evalOperandsFast body locals ops mem.borrows mem.globals mem.callerLocals with
      | .ok vals locals' => .leaf (.ok (.aggregate 0 vals) locals' mem)
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | _ => .leaf (evalRvalueFallback locals (.aggregate ak ops) mem body.localDecls body.layouts)
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandFast body locals lhsOp mem.borrows mem.globals mem.callerLocals with
    | .ok lhsVal locals₁ =>
      match evalOperandFast body locals₁ rhsOp mem.borrows mem.globals mem.callerLocals with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          match op with
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
          | _ => .leaf .unsupported
        | _, _ => .leaf .unsupported
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
  | .unaryOp uop op =>
    match uop with
    | .not =>
      match evalOperandFast body locals op mem.borrows mem.globals mem.callerLocals with
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
    cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals <;> rfl
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
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals <;> rfl
    | _ => rfl
  | aggregate ak ops =>
    cases ak with
    | tuple =>
      dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
      rw [evalOperandsFast_eq]
      cases evalOperands locals ops mem.borrows mem.globals body.layouts mem.callerLocals <;> rfl
    | _ => rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree]
    rw [evalOperandFast_eq]
    cases evalOperand locals lhsOp mem.borrows mem.globals body.layouts mem.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [evalOperandFast_eq]
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals body.layouts mem.callerLocals with
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
      cases evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | neg => rfl
    | ptrMetadata => rfl
  | _ => rfl

def finishAssignStmtNodeFast
    (s : MachineState) (dst : Place) : RvalueEvalResult → MirStepNode
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
              dst.local_ .none .nil with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' := invalidateConflictingBorrows mem₁.borrows dst.local_ .none
            MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | _ => finishAssignStmtNode s dst (.ok val locals₁ mem₁)

theorem finishAssignStmtNodeFast_eq
    (s : MachineState) (dst : Place) (res : RvalueEvalResult) :
    finishAssignStmtNodeFast s dst res = finishAssignStmtNode s dst res := by
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
    finishAssignStmtNodeFast s dst
      (evalRvalueFast body s.frame.locals rv s.memory)
  | .storageLive loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .uninit with
      | .some locals' => MirStepNode.step (advanceStmt s locals')
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .storageDead loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .dead with
      | .some locals' => MirStepNode.step (advanceStmt s locals')
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
    show finishAssignStmtNodeFast s dst (evalRvalueFast body s.frame.locals rv s.memory) = _
    rw [finishAssignStmtNodeFast_eq, evalRvalueFast_eq]
    dsimp only [finishAssignStmtNode, evalStmt]
    cases evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts <;> rfl
  | _ => rfl

def finishAssignSymTree (s : MachineState) (dst : Place) :
    SymTree RvalueEvalResult → SymTree MirStepNode
  | .leaf res => .leaf (finishAssignStmtNode s dst res)
  | .branch c t1 t2 => .branch c (finishAssignSymTree s dst t1) (finishAssignSymTree s dst t2)

theorem finishAssignSymTree_eq (s : MachineState) (dst : Place)
    (t : SymTree RvalueEvalResult) :
    finishAssignSymTree s dst t =
      t.bind (fun res => .leaf (finishAssignStmtNode s dst res)) := by
  induction t with
  | leaf _ => rfl
  | branch _ _ _ ih1 ih2 =>
    dsimp only [finishAssignSymTree, SymTree.bind]
    rw [ih1, ih2]

def evalStmtSymTreeFast
    (body : CapturedMir) (s : MachineState) (stmt : Statement) : SymTree MirStepNode :=
  match stmt.kind with
  | .assign dst rv =>
    finishAssignSymTree s dst
      (evalRvalueSymTreeFast body s.frame.locals rv s.memory)
  | .storageLive loc =>
    .leaf
      (match get? s.frame.locals loc with
       | .some _ =>
         match set? s.frame.locals loc .uninit with
         | .some locals' => MirStepNode.step (advanceStmt s locals')
         | .none => MirStepNode.fail .ub
       | .none => MirStepNode.fail .ub)
  | .storageDead loc =>
    .leaf
      (match get? s.frame.locals loc with
       | .some _ =>
         match set? s.frame.locals loc .dead with
         | .some locals' => MirStepNode.step (advanceStmt s locals')
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
    show finishAssignSymTree s dst (evalRvalueSymTreeFast body s.frame.locals rv s.memory) =
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
      | .some (.init retVal) => .leaf (MirStepNode.retNormal retVal s.memory)
      | _ => .leaf (MirStepNode.fail .ub)
    | _ :: _ => evalTerminatorFallback s term body
  | .switchInt discr targets =>
    match evalOperandFast body s.frame.locals discr s.memory.borrows s.memory.globals
        s.memory.callerLocals with
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
        s.memory.callerLocals with
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
      | some slot => cases slot <;> rfl
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
        body.layouts s.memory.callerLocals with
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
      | .some (.init retVal) => .halted ok (.normal (retVal, s.memory))
      | _ => .faulted
    | _ :: _ => .faulted
  | .switchInt discr targets =>
    match evalOperandFast body s.frame.locals discr s.memory.borrows s.memory.globals
        s.memory.callerLocals with
    | .ok (.scalar sc) locals' =>
      let target := lookupSwitchTarget sc.bits targets.branches targets.otherwise
      .running ok .none { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }
    | _ => .faulted
  | .assert cond expected target _ =>
    match evalOperandFast body s.frame.locals cond s.memory.borrows s.memory.globals
        s.memory.callerLocals with
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
      | some slot => cases slot <;> rfl
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg]
    cases evalOperandFast body s.frame.locals discr s.memory.borrows s.memory.globals
        s.memory.callerLocals with
    | ok v _ => cases v <;> rfl
    | _ => rfl
  | assert cond expected target unwind =>
    dsimp only [evalTerminatorCfg]
    cases evalOperandFast body s.frame.locals cond s.memory.borrows s.memory.globals
        s.memory.callerLocals with
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
          intro _ h_wp
          dsimp only [stepNodeWP, MirStepNode.retNormal] at h_wp ⊢
          rw [runCfgSteps_halted] at h_wp
          exact h_wp.2
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    rw [evalOperandFast_eq]
    cases evalOperand s.frame.locals discr s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals with
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
        body.layouts s.memory.callerLocals with
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
          intro _ h_wp
          dsimp only [stepNodeStepsWP, MirStepNode.retNormal] at h_wp ⊢
          rw [runCfgSteps_halted] at h_wp
          exact h_wp.2
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    rw [evalOperandFast_eq]
    cases evalOperand s.frame.locals discr s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals with
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
        body.layouts s.memory.callerLocals with
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

end Anneal.PureMirExec
