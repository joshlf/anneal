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


private def FrameAdvanced (bbIdx stmtIdx : Nat) : MirStepNode → Prop
  | .tau (.running ms') => ms'.frame.blockIdx = bbIdx ∧ ms'.frame.stmtIdx = stmtIdx + 1
  | _ => True

private theorem fa_fail {bbIdx stmtIdx : Nat} {fk : FailureKind} :
    FrameAdvanced bbIdx stmtIdx (.fail fk) := trivial

private theorem fa_unsupported {bbIdx stmtIdx : Nat} :
    FrameAdvanced bbIdx stmtIdx .unsupported := trivial

private theorem fa_step {bbIdx stmtIdx : Nat} {env : List LocalSlot} {mem : Memory}
    {l' : List LocalSlot} {m' : Memory} :
    FrameAdvanced bbIdx stmtIdx
      (.step (advanceStmt { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := env }, memory := mem } l' m')) :=
  ⟨rfl, rfl⟩

private theorem evalForeignFrameDerefWrite_fa {bbIdx stmtIdx : Nat} {env : List LocalSlot} {mem : Memory}
    (locals₁ : List LocalSlot) (mem₁ : Memory) (dst : Place) (restProj : List ProjectionElem)
    (val : Value) (decls : List LocalDecl) (layouts : LayoutTable) :
    FrameAdvanced bbIdx stmtIdx
      (evalForeignFrameDerefWrite { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := env }, memory := mem }
        locals₁ mem₁ dst restProj val decls layouts) := by
  unfold evalForeignFrameDerefWrite
  cases foreignFrameDerefWrite locals₁ mem₁ dst restProj val decls layouts with
  | ok _ _ => exact fa_step
  | ub => exact fa_fail
  | unsupported => exact fa_unsupported

private theorem evalSetDiscriminantDerefWrite_fa {bbIdx stmtIdx : Nat} {env : List LocalSlot} {mem : Memory}
    (locals₁ : List LocalSlot) (p : Place) (rest : List ProjectionElem) (newVal : Value)
    (decls : List LocalDecl) (layouts : LayoutTable) :
    FrameAdvanced bbIdx stmtIdx
      (evalSetDiscriminantDerefWrite { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := env }, memory := mem }
        locals₁ p rest newVal decls layouts) := by
  unfold evalSetDiscriminantDerefWrite; dsimp only
  repeat' (first
    | with_reducible (first | exact fa_fail | exact fa_unsupported | exact fa_step | exact evalForeignFrameDerefWrite_fa ..)
    | split
    | (dsimp only))

private theorem evalSetDiscriminantLocal_fa {bbIdx stmtIdx : Nat} {env : List LocalSlot} {mem : Memory}
    (loc : Local) (variantIdx : Nat) (fields : List Value) :
    FrameAdvanced bbIdx stmtIdx
      (evalSetDiscriminantLocal { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := env }, memory := mem }
        loc variantIdx fields) := by
  unfold evalSetDiscriminantLocal; dsimp only
  repeat' (first | with_reducible (first | exact fa_fail | exact fa_step) | split | (dsimp only))

theorem evalStmt_preserves_frame {bbIdx stmtIdx env mem stmt decls layouts ms'}
  (h_pure : isPureStatement stmt.kind = true)
  (h_step : evalStmt { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := env }, memory := mem } stmt decls layouts = .step ms') :
  ms'.frame.blockIdx = bbIdx ∧ ms'.frame.stmtIdx = stmtIdx + 1 := by
  suffices h : FrameAdvanced bbIdx stmtIdx
      (evalStmt { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := env }, memory := mem } stmt decls layouts) by
    rw [h_step] at h; exact h
  rcases stmt with ⟨skind, sspan⟩
  dsimp only at h_pure
  cases skind with
  | nop | coverage | constEvalCounter => exact fa_step
  | retag _ _ => cases h_pure
  | intrinsic intr =>
    cases intr with
    | copyNonOverlapping _ _ _ => cases h_pure
    | assume _ =>
      dsimp only [evalStmt]
      repeat' (first | with_reducible (first | exact fa_fail | exact fa_unsupported | exact fa_step) | split | (dsimp only))
  | storageLive _ | storageDead _ | placeMention _ | deinit _ =>
    dsimp +zetaDelta only [evalStmt]
    repeat' (first | with_reducible (first | exact fa_fail | exact fa_unsupported | exact fa_step) | split | (dsimp only))
  | setDiscriminant p variantIdx =>
    dsimp +zetaDelta only [evalStmt]
    repeat' (first
      | with_reducible (first
        | exact fa_fail | exact fa_unsupported | exact fa_step
        | exact evalSetDiscriminantLocal_fa ..
        | exact evalSetDiscriminantDerefWrite_fa ..)
      | split
      | (dsimp only))
  | assign dst rv =>
    dsimp only [evalStmt]
    cases evalRvalue env rv mem decls layouts with
    | ub => exact fa_fail
    | unsupported => exact fa_unsupported
    | ok val locals₁ mem₁ =>
      dsimp only
      repeat' (first
        | with_reducible (first
          | exact fa_fail | exact fa_unsupported | exact fa_step
          | exact evalForeignFrameDerefWrite_fa ..)
        | split
        | (dsimp only))
  | _ => cases h_pure

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
  (h_post : post val)
  (h_init : valueContainsUninit val = false := by rfl) :
  LiftStmtsTerminator body bbIdx stmtIdx env stmts { kind := .return_, span := span } post 1 := by
  subst h_end
  rcases h_phase with hp | hp
  · dsimp [LiftStmtsTerminator, wpMirExecSym, evalSymNodeTree, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
    simp [hp, h_bb, get_length_none_seq, get_length_none_list, ite_length_eq, evalTerminatorSymTree, evalTerminator, h_ret, h_init]
    exact h_post
  · dsimp [LiftStmtsTerminator, wpMirExecSym, evalSymNodeTree, stepMirExecSymTree, stepMirSymTree, PureState.toMachineState, emptyMemory]
    simp [hp, h_bb, get_length_none_seq, get_length_none_list, ite_length_eq, evalTerminatorSymTree, evalTerminator, h_ret, h_init]
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
        ensureNestedFieldShells
          rootVal
          (proj :: rest)
          localDecls
          layouts
          (placeTy localDecls layouts { local_ := dst.local_, projection := .nil })
      with
      | .none => none
      | .some shelledRoot =>
        match
          writeProjectedForLocal
            locals
            localDecls
            layouts
            dst.local_
            shelledRoot
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
      hasProtectedWriteConflict mem.borrows mem.activeProtectors
        place.local_ .none .nil 0 0 (length mem.callStack) = false →
      post (.frame target 0 env'
        { mem with
          borrows :=
            invalidateConflictingBorrows mem.borrows place.local_ .none
              (length mem.callStack) }) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .drop place target unwind, span := span }
  /-- Drop of a projected place (`place.projection = proj :: rest`). -/
  | dropProjected {place : Place} {target : BasicBlockIdx}
      {unwind : UnwindAction} {span : String} {proj : ProjectionElem}
      {rest : List ProjectionElem} {rootVal rootVal' : Value} {env' : PureEnv} :
      get? env place.local_ = some (.init rootVal) →
      place.projection = proj :: rest →
      deinitProjectedForLocal env cur.localDecls cur.layouts place.local_ rootVal (proj :: rest) = .ok rootVal' →
      set? env place.local_ (.init rootVal') = some env' →
      hasProtectedWriteConflict mem.borrows mem.activeProtectors
        place.local_ .none
        (resolveBorrowWriteLocalProj cur.localDecls cur.layouts env place.local_ (proj :: rest))
        0 0 (length mem.callStack) = false →
      post (.frame target 0 env'
        { mem with
          borrows :=
            invalidateConflictingBorrowsAtProj mem.borrows place.local_ .none
              (resolveBorrowWriteLocalProj cur.localDecls cur.layouts env place.local_ (proj :: rest))
              0 0 (length mem.callStack) }) →
      LiftTerminator cur bbIdx stmtIdx env mem post
        { kind := .drop place target unwind, span := span }
  /--
  Return from the root frame (empty call stack) when no active function-entry
  protector blocks deallocating the root frame's locals.
  -/
  | return_ {span : String} {retVal : Value} :
      get? env 0 = some (.init retVal) →
      valueContainsUninit retVal = false →
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
      valueContainsUninit retVal = false →
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
private theorem assignLocalPlace_cons_inv
    {env₁ env₂ : PureEnv} {borrows borrows' : List BorrowEntry}
    {dstLoc : Local} {proj : ProjectionElem} {rest : List ProjectionElem}
    {val : Value} {localDecls : List LocalDecl} {layouts : LayoutTable} {depth : Nat}
    (h_write :
      assignLocalPlace env₁ borrows { local_ := dstLoc, projection := proj :: rest } val
        localDecls layouts depth = some (env₂, borrows')) :
    proj ≠ .deref ∧
    ∃ rootVal shelledRoot rootVal',
      get? env₁ dstLoc = some (.init rootVal) ∧
      ensureNestedFieldShells rootVal (proj :: rest) localDecls layouts
        (placeTy localDecls layouts { local_ := dstLoc, projection := .nil }) = some shelledRoot ∧
      writeProjectedForLocal env₁ localDecls layouts dstLoc shelledRoot (proj :: rest) val = .ok rootVal' ∧
      set? env₁ dstLoc (.init rootVal') = some env₂ ∧
      borrows' =
        invalidateConflictingBorrowsAtProj borrows dstLoc .none
          (resolveBorrowWriteLocalProj localDecls layouts env₁ dstLoc (proj :: rest)) 0 0 depth := by
  have h_nd : proj ≠ .deref := by
    intro h_eq; subst h_eq; simp [assignLocalPlace] at h_write
  refine ⟨h_nd, ?_⟩
  have h_unfold :
      (match get? env₁ dstLoc with
       | some (.init rootVal) =>
         match ensureNestedFieldShells rootVal (proj :: rest) localDecls layouts
             (placeTy localDecls layouts { local_ := dstLoc, projection := .nil }) with
         | .none => none
         | .some shelledRoot =>
           match writeProjectedForLocal env₁ localDecls layouts dstLoc shelledRoot (proj :: rest) val with
           | .ok rootVal' =>
             match set? env₁ dstLoc (.init rootVal') with
             | some locals' =>
               some (locals',
                 invalidateConflictingBorrowsAtProj borrows dstLoc .none
                   (resolveBorrowWriteLocalProj localDecls layouts env₁ dstLoc (proj :: rest)) 0 0 depth)
             | none => none
           | _ => none
       | _ => none) = some (env₂, borrows') := by
    cases proj with
    | deref => exact False.elim (h_nd rfl)
    | _ => exact h_write
  cases h_get : get? env₁ dstLoc with
  | none => rw [h_get] at h_unfold; cases h_unfold
  | some slot =>
    rw [h_get] at h_unfold
    cases slot with
    | dead => cases h_unfold
    | uninit => cases h_unfold
    | init rootVal =>
      dsimp only at h_unfold
      cases h_ens : ensureNestedFieldShells rootVal (proj :: rest) localDecls layouts
          (placeTy localDecls layouts { local_ := dstLoc, projection := .nil }) with
      | none => rw [h_ens] at h_unfold; cases h_unfold
      | some shelledRoot =>
        rw [h_ens] at h_unfold
        dsimp only at h_unfold
        cases h_wp : writeProjectedForLocal env₁ localDecls layouts dstLoc shelledRoot (proj :: rest) val with
        | ub => rw [h_wp] at h_unfold; cases h_unfold
        | unsupported => rw [h_wp] at h_unfold; cases h_unfold
        | ok rootVal' =>
          rw [h_wp] at h_unfold
          dsimp only at h_unfold
          cases h_set : set? env₁ dstLoc (.init rootVal') with
          | none => rw [h_set] at h_unfold; cases h_unfold
          | some locals₂ =>
            rw [h_set] at h_unfold
            injection h_unfold with h_pair
            injection h_pair with h_env h_bor
            subst h_env
            refine ⟨rootVal, shelledRoot, rootVal', ?_, ?_, ?_, ?_, h_bor.symm⟩ <;> first | rfl | assumption

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
  cases dstProj with
  | nil =>
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    rw [h_rv]
    dsimp only []
    unfold assignLocalPlace at h_write
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
    obtain ⟨h_nd, rootVal, shelledRoot, rootVal', h_get, h_ens, h_wp, h_set, h_bor⟩ :=
      assignLocalPlace_cons_inv h_write
    subst h_bor
    cases proj with
    | deref => exact False.elim (h_nd rfl)
    | _ =>
      unfold evalStmt
      dsimp only [PureState.toMachineState]
      rw [h_rv]
      dsimp only []
      rw [h_get]
      dsimp only []
      rw [h_ens]
      dsimp only []
      rw [h_wp]
      dsimp only []
      rw [h_set]
      dsimp only []
      rw [h_prot]
      rfl

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
  | drop h_get h_live h_proj h_set h_noConflict h_next =>
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
      rcases mem with ⟨_, _, _, _, _, _, _, _, _ | ⟨ph, pt⟩, _, _, _, _⟩
      · exact h_next
      · dsimp only [] at h_noConflict ⊢
        rw [h_noConflict]
        exact h_next
    | init _ =>
      dsimp only []
      rw [h_proj]
      dsimp only []
      rw [h_set]
      rcases mem with ⟨_, _, _, _, _, _, _, _, _ | ⟨ph, pt⟩, _, _, _, _⟩
      · exact h_next
      · dsimp only [] at h_noConflict ⊢
        rw [h_noConflict]
        exact h_next
  | dropProjected h_get h_proj h_deinit h_set h_noConflict h_next =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState, bodyLocalDeclsOf]
    rw [h_get]
    dsimp only []
    rw [h_proj]
    dsimp only []
    rw [h_deinit]
    dsimp only []
    rw [h_set]
    rcases mem with ⟨_, _, _, _, _, _, _, _, _ | ⟨ph, pt⟩, _, _, _, _⟩
    · exact h_next
    · dsimp only [] at h_noConflict ⊢
      rw [h_noConflict]
      exact h_next
  | return_ h_ret h_init h_stack h_noDealloc h_post =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_ret]
    dsimp only []
    rw [h_stack]
    dsimp only [Trusted.Sequence.length, List.length] at h_noDealloc ⊢
    rw [h_noDealloc]
    dsimp only []
    rw [h_init]
    exact h_post
  | returnToCaller h_ret h_init h_stack h_noDealloc h_div h_write h_next =>
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
    rw [h_init]
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

/-!
## Modular Pure Execution Continuation (`PureMirModularConverges`) in `Anneal.PureMirExec`

The remainder of Section 9C–10C (starting at `PureMirModularConverges.step_unwindResume`)
keeps its `Anneal.PureMirExec` names and signatures and is elaborated here while the
first part (`ModularRootMemory` through `verifyModularMir_of_pureModularExec_any`) lives in
`PureMirExec.lean`, keeping both `PureMirExec.lean` and `MirLiftCore.lean` comfortably
below 1800 MiB under `-j4 -M2048 -DElab.async=true` in `trusted/audit/check_trusted.py`.
-/
section ModularPureExecContinuation
set_option maxRecDepth 2048
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

/--
1-step `unwindResume` terminator rule for `PureMirModularConverges`: in any root
modular caller (`m.callStack = []`), completing a cleanup landing pad (`isCleanup
= true`) via `TerminatorKind.unwindResume` halts cleanly with `.halted .panic`,
satisfying `mirSafePost`.
-/
theorem PureMirModularConverges.step_unwindResume
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .unwindResume) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator]
    rw [hm.2.2.1]
    dsimp only [unwindFromCallStack, MirStepNode.retOutcome,
      Trusted.ITree.ITreeF.map]
    trivial

/--
1-step `unwindTerminate` terminator rule for `PureMirModularConverges`:
halting via `TerminatorKind.unwindTerminate` produces `.halted .abort`,
satisfying `mirSafePost`.
-/
theorem PureMirModularConverges.step_unwindTerminate
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .unwindTerminate) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator, MirStepNode.retOutcome, Trusted.ITree.ITreeF.map]
    trivial

/--
Generalized subsumption-aware 1-step external modular call rule
(`PureMirModularConverges.call_modular_resolved`):
supports arbitrary call-target resolution via `resolveCallTarget` (including
local/projected zero-sized `RigidTy.fnDef` slots with `Operand.move` slot
invalidation and indirect `FnPtrEntry` targets) AND full `.cleanup cleanupBb`
unwind landing-pad recovery alongside `.continue_`, `.terminate`, and
non-unwinding contracts.
-/
theorem PureMirModularConverges.call_modular_resolved
    {subContract contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub : MirCallContract.Subsumes subContract contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_resolve :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        resolveCallTarget (ps.toMachineState m) func (length argOps)
          body.localDecls body.layouts = .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts resolvedTarget.defPath
        resolvedTarget.typeArgs traitImpls = none)
    (h_not_exact : isDirectExactDivTarget resolvedTarget = false := by decide)
    (h_contract_pre :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        subContract.pre
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m })
    (h_contract_ret :
      ∀ (m retMem : Memory) (retVal : Value),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (.returned retVal retMem) →
        ModularRootMemory body callees traitImpls retMem ∧ calleePost retVal)
    (h_contract_panic :
      unwind = .continue_ ∨
      unwind = .terminate ∨
      (∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        ¬ subContract.post
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (.panicked panicMem)) ∨
      ∃ cleanupBb : BasicBlockIdx,
        unwind = .cleanup cleanupBb ∧
        (∀ (m panicMem : Memory),
          ModularRootMemory body callees traitImpls m →
          subContract.post
            { defPath := resolvedTarget.defPath
              typeArgs := resolvedTarget.typeArgs
              args := argVals
              memory := m }
            (.panicked panicMem) →
          ModularRootMemory body callees traitImpls panicMem) ∧
        PureMirModularConverges contract body callees
          { bb := cleanupBb, stmtIdx := 0, env := envAfterArgs }
          post traitImpls)
    (h_panic_stack :
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (.panicked panicMem) →
        panicMem.callStack = [])
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic :
      resolvedTarget.isIndirect = true ∨
      classifyRustIntrinsic? resolvedTarget.defPath = none := by
      first | exact Or.inr (by decide) | exact Or.inl (by decide)) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.extCall
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (resumeExternalCall (ps.toMachineState m) envAfterArgs
            destination targetBb unwind) := by
    have h_res_m := h_resolve m hm
    dsimp only [PureState.toMachineState] at h_res_m
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf]
      rw [h_res_m]
      dsimp only
      rw [evalOperands_pure_eq envAfterFunc argOps m.borrows m.globals
        body.layouts m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only
      rw [h_not_exact]
      dsimp only
      cases h_ind : resolvedTarget.isIndirect with
      | true => rfl
      | false =>
        rcases h_not_intrinsic with h_ind_t | h_ni
        · rw [h_ind] at h_ind_t
          exact False.elim (Bool.false_ne_true h_ind_t)
        · dsimp only [evalDirectRustIntrinsic?]
          rw [h_ni]
  rw [h_step_eq]
  dsimp only [MirStepNode.extCall, Trusted.ITree.ITreeF.map, mirModularWP,
    MirCallContract.toCallContract]
  rcases h_sub _ (h_contract_pre m hm) with ⟨h_cpre, h_cpost_imp⟩
  refine ⟨h_cpre, fun ans hp_sup => ?_⟩
  have hp := h_cpost_imp ans hp_sup
  cases ans with
  | aborted =>
    dsimp only [resumeExternalCall]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | panicked panicMem =>
    rcases h_contract_panic with
      rfl | rfl | h_no_panic | ⟨cleanupBb, rfl, h_mod_p, h_clean⟩
    · dsimp only [resumeExternalCall, applyUnwindAction]
      rw [h_panic_stack m panicMem hm hp]
      dsimp only [unwindFromCallStack]
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      trivial
    · dsimp only [resumeExternalCall, applyUnwindAction]
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      trivial
    · exact False.elim (h_no_panic m panicMem hm hp)
    · dsimp only [resumeExternalCall, applyUnwindAction]
      exact h_clean panicMem (h_mod_p m panicMem hm hp)
  | returned retVal retMem =>
    rcases h_contract_ret m retMem retVal hm hp with ⟨h_mod_ret, h_cp⟩
    rcases h_after retVal h_cp with ⟨updEnv, h_wr, h_next⟩
    dsimp only
    rw [resumeExternalCall_pure_returned_eq _ envAfterArgs destination targetBb unwind
      retVal retMem h_dst_pure h_mod_ret.2.2.2.2]
    unfold writePurePlaceValue at h_wr
    rw [h_wr]
    exact h_next _ (h_mod_ret.withDirectDestBorrows envAfterArgs destination)

/--
Subsumption-aware 1-step polymorphic `#[external_spec]` call rule supporting
both constant and local/projected zero-sized `RigidTy.fnDef` operands
(`extractPureCalleeTarget?` + `resolvePureCalleeTarget`) AND `.cleanup
cleanupBb` unwind landing-pad recovery.
-/
theorem PureMirModularConverges.call_poly_external_spec_pureTarget
    {contract : MirCallContract}
    {targetDefPath : DefPath}
    {expectedTypeArgs : List RigidTy}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (polyExternalSpecCallContract targetDefPath expectedTypeArgs
          sidecarBody extraPre extraPost)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (targetDefPath, expectedTypeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func targetDefPath expectedTypeArgs
        body.layouts = .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts targetDefPath expectedTypeArgs traitImpls = none)
    (h_not_exact : stringEq targetDefPath "core::intrinsics::exact_div" = false := by decide)
    (h_arity : length argVals = sidecarBody.argCount)
    (h_param_tys : argsMatchCalleeParamTys sidecarBody argVals)
    (h_extra_pre : extraPre argVals)
    (h_unwind :
      unwind = .continue_ ∨
      unwind = .terminate ∨
      sidecarTargetCanUnwind sidecarBody = false ∨
      ∃ cleanupBb : BasicBlockIdx,
        unwind = .cleanup cleanupBb ∧
        PureMirModularConverges contract body callees
          { bb := cleanupBb, stmtIdx := 0, env := envAfterArgs }
          post traitImpls)
    (h_after :
      ∀ (retVal : Value),
        retMatchesCalleeReturnTy sidecarBody retVal ∧ extraPost argVals retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic : classifyRustIntrinsic? targetDefPath = none := by decide) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  refine PureMirModularConverges.call_modular_resolved
    (resolvedTarget := { defPath := targetDefPath, typeArgs := expectedTypeArgs, fnSig := .none, isIndirect := false })
    h_sub h_phase h_bb h_end h_term h_dst_pure h_args_pure
    (fun m _ => by
      rw [resolveCallTarget_eq_of_extractPureCalleeTarget
        (ps.toMachineState m) func (length argOps) body.localDecls body.layouts
        h_ext]
      exact h_res_pure)
    h_args h_lookup h_not_exact
    (fun _ _ => ⟨rfl, rfl, h_arity, h_param_tys, h_extra_pre⟩)
    (fun m _ _ hm hp =>
      ⟨ModularRootMemory.of_callFrameAndTraitsPreserved hm hp.1, hp.2⟩)
    ?_
    (fun m _ hm hp => by
      dsimp only [polyExternalSpecCallContract] at hp
      cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
      · exact False.elim hp
      · rw [hp.1.2.1, hm.2.2.1])
    h_after
    (Or.inr h_not_intrinsic)
  rcases h_unwind with hu | hu | h_nu | ⟨cleanupBb, h_cl, h_clean_wp⟩
  · exact Or.inl hu
  · exact Or.inr (Or.inl hu)
  · refine Or.inr (Or.inr (Or.inl (fun _ _ _ hp => ?_)))
    dsimp only [polyExternalSpecCallContract] at hp
    rw [h_nu] at hp
    exact hp
  · refine Or.inr (Or.inr (Or.inr ⟨cleanupBb, h_cl, ?_, h_clean_wp⟩))
    intro m panicMem hm hp
    dsimp only [polyExternalSpecCallContract] at hp
    cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
    · exact False.elim hp
    · exact ModularRootMemory.of_callFrameAndTraitsPreserved hm hp

/--
Subsumption-aware 1-step pure `CallConv.rustIntrinsic` call rule supporting
both constant and local/projected zero-sized `RigidTy.fnDef` operands
(`extractPureCalleeTarget?` + `resolvePureCalleeTarget`).
-/
theorem PureMirModularConverges.call_intrinsic_pureTarget
    {contract : MirCallContract}
    {pointerBytes : Nat}
    {ubChecksEnabled : Bool}
    {rtEval : DefPath → List RigidTy → List Value → Option Value}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {typeArgs : List RigidTy}
    {resolvedTarget : ResolvedCallTarget}
    {kind : PureRustIntrinsicKind}
    {envAfterFunc envAfterArgs updatedEnv : List SlotState}
    {argVals : List Value}
    {retVal : Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (defPath, typeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func defPath typeArgs body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup : lookupCallee callees body.layouts defPath typeArgs traitImpls = none)
    (h_not_exact : stringEq defPath "core::intrinsics::exact_div" = false := by decide)
    (h_kind : classifyPureRustIntrinsic? defPath = some kind)
    (h_eval :
      evalPureRustIntrinsicWithRuntime rtEval kind typeArgs argVals pointerBytes
        ubChecksEnabled = some retVal)
    (h_wr : writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv)
    (h_after :
      PureMirModularConverges contract body callees
        { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic : classifyRustIntrinsic? defPath = none := by decide) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  refine PureMirModularConverges.call_modular_resolved
    (resolvedTarget := { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false })
    (calleePost := (· = retVal))
    h_sub h_phase h_bb h_end h_term h_dst_pure h_args_pure
    (fun m _ => by
      rw [resolveCallTarget_eq_of_extractPureCalleeTarget
        (ps.toMachineState m) func (length argOps) body.localDecls body.layouts
        h_ext]
      exact h_res_pure)
    h_args h_lookup h_not_exact
    (fun _ _ => ⟨kind, retVal, h_kind, h_eval⟩)
    (fun m _ rv hm hp => by
      rcases hp with ⟨rfl, _, hk', hev'⟩
      rw [h_kind] at hk'
      injection hk' with hk_eq
      subst hk_eq
      rw [h_eval] at hev'
      injection hev' with hrv_eq
      exact ⟨hm, hrv_eq.symm⟩)
    (Or.inr (Or.inr (Or.inl (fun _ _ _ hp => hp))))
    (fun _ _ _ hp => False.elim hp)
    (fun rv h_eq => by
      subst h_eq
      exact ⟨updatedEnv, h_wr, h_after⟩)
    (Or.inr h_not_intrinsic)

/--
1-step inline `core::intrinsics::exact_div` call rule supporting both constant
and local/projected zero-sized `RigidTy.fnDef` operands
(`extractPureCalleeTarget?` + `resolvePureCalleeTarget`).
-/
theorem PureMirModularConverges.call_exact_div_pureTarget
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {func : Operand}
    {argOps : List Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {defPath : DefPath} {typeArgs : List RigidTy}
    {resolvedTarget : ResolvedCallTarget}
    {lhs rhs retScalar : ScalarInt} {isSigned : Bool}
    {envAfterFunc envAfterArgs updatedEnv : List SlotState}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (defPath, typeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func defPath typeArgs body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_exact_path : stringEq defPath "core::intrinsics::exact_div" = true := by decide)
    (h_args :
      evalPureOperands envAfterFunc argOps body.layouts =
        .ok [.scalar lhs, .scalar rhs] envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath typeArgs traitImpls = none)
    (h_signed :
      resolveIntrinsicIsSigned
        { defPath := defPath
          typeArgs := typeArgs
          fnSig := .none
          isIndirect := false }
        body.localDecls body.layouts argOps = some isSigned := by rfl)
    (h_div : evalExactDiv lhs rhs isSigned = some retScalar)
    (h_wr :
      writePurePlaceValue envAfterArgs destination (.scalar retScalar) =
        .ok updatedEnv)
    (h_next :
      PureMirModularConverges contract body callees
        { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.step
          (({ bb := targetBb, stmtIdx := 0, env := updatedEnv } : PureState).toMachineState
            (invalidateDirectDestWriteBorrows m envAfterArgs destination)) := by
    have h_res_m :
        resolveCallTarget (ps.toMachineState m) func (length argOps)
          body.localDecls body.layouts =
          .ok { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false }
            envAfterFunc := by
      rw [resolveCallTarget_eq_of_extractPureCalleeTarget
        (ps.toMachineState m) func (length argOps)
        body.localDecls body.layouts h_ext]
      exact h_res_pure
    dsimp only [PureState.toMachineState] at h_res_m
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf]
      rw [h_res_m]
      dsimp only
      rw [evalOperands_pure_eq envAfterFunc argOps m.borrows m.globals
        body.layouts m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only [isDirectExactDivTarget]
      rw [h_exact_path]
      dsimp only
      rw [h_signed]
      dsimp only
      rw [h_div]
      dsimp only
      rw [writeIntrinsicReturn_pure_eq _ envAfterArgs destination targetBb
        (.scalar retScalar) h_dst_pure]
      unfold writePurePlaceValue at h_wr
      rw [h_wr]
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step_eq]
  exact h_next _ (hm.withDirectDestBorrows envAfterArgs destination)

/--
Generalized subsumption-aware 1-step external `tailCall` rule
(`PureMirModularConverges.tailCall_modular_resolved`):
supports arbitrary call-target resolution via `resolveCallTarget` (including
local/projected zero-sized `RigidTy.fnDef` slots and indirect `FnPtrEntry`
targets).
-/
theorem PureMirModularConverges.tailCall_modular_resolved
    {subContract contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub : MirCallContract.Subsumes subContract contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_resolve :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        resolveCallTarget (ps.toMachineState m) func (length argOps)
          body.localDecls body.layouts = .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts resolvedTarget.defPath
        resolvedTarget.typeArgs traitImpls = none)
    (h_contract_pre :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        subContract.pre
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m })
    (h_contract_ret :
      ∀ (m retMem : Memory) (retVal : Value),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (.returned retVal retMem) →
        retMem.callStack = [] ∧ post retVal)
    (h_panic_stack :
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (.panicked panicMem) →
        panicMem.callStack = []) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  let mTd : Memory :=
    { m with borrows := disableFrameBorrows m.borrows (length m.callStack) (length ps.env) }
  have hmTd : ModularRootMemory body callees traitImpls mTd :=
    ModularRootMemory.withBorrows hm _
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.extCall
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := mTd }
          resumeExternalTailCall := by
    have h_res_m := h_resolve m hm
    dsimp only [PureState.toMachineState] at h_res_m
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf]
      rw [h_res_m]
      dsimp only
      rw [evalOperands_pure_eq envAfterFunc argOps m.borrows m.globals
        body.layouts m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      have h_lk_m :
          lookupCallee m.callees body.layouts resolvedTarget.defPath
            resolvedTarget.typeArgs m.traitImpls = none := by
        rw [hm.1, hm.2.1, h_lookup]
      rw [hasFrameDeallocProtectorConflict_of_eq_nil hm.2.2.2.2, h_lk_m]
  rw [h_step_eq]
  dsimp only [MirStepNode.extCall, Trusted.ITree.ITreeF.map, mirModularWP,
    MirCallContract.toCallContract]
  rcases h_sub _ (h_contract_pre mTd hmTd) with ⟨h_cpre, h_cpost_imp⟩
  refine ⟨h_cpre, fun ans hp_sup => ?_⟩
  have hp := h_cpost_imp ans hp_sup
  cases ans with
  | aborted =>
    dsimp only [resumeExternalTailCall]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | panicked panicMem =>
    dsimp only [resumeExternalTailCall]
    rw [h_panic_stack mTd panicMem hmTd hp]
    dsimp only [unwindFromCallStack]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | returned retVal retMem =>
    rcases h_contract_ret mTd retMem retVal hmTd hp with ⟨h_cs, h_post_ret⟩
    dsimp only [resumeExternalTailCall]
    rw [h_cs]
    dsimp only
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    exact h_post_ret

/--
Subsumption-aware 1-step polymorphic `#[external_spec]` `tailCall` rule
supporting both constant and local/projected zero-sized `RigidTy.fnDef`
operands (`extractPureCalleeTarget?` + `resolvePureCalleeTarget`).
-/
theorem PureMirModularConverges.tailCall_poly_external_spec_pureTarget
    {contract : MirCallContract}
    {targetDefPath : DefPath}
    {expectedTypeArgs : List RigidTy}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (polyExternalSpecCallContract targetDefPath expectedTypeArgs
          sidecarBody extraPre extraPost)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (targetDefPath, expectedTypeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func targetDefPath expectedTypeArgs
        body.layouts = .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts targetDefPath expectedTypeArgs traitImpls = none)
    (h_arity : length argVals = sidecarBody.argCount)
    (h_param_tys : argsMatchCalleeParamTys sidecarBody argVals)
    (h_extra_pre : extraPre argVals)
    (h_imp :
      ∀ retVal : Value,
        retMatchesCalleeReturnTy sidecarBody retVal ∧ extraPost argVals retVal →
        post retVal) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  exact PureMirModularConverges.tailCall_modular_resolved
    (subContract := polyExternalSpecCallContract targetDefPath expectedTypeArgs
      sidecarBody extraPre extraPost)
    (resolvedTarget := { defPath := targetDefPath, typeArgs := expectedTypeArgs, fnSig := .none, isIndirect := false })
    h_sub
    h_phase h_bb h_end h_term h_args_pure
    (fun m _ => by
      rw [resolveCallTarget_eq_of_extractPureCalleeTarget
        (ps.toMachineState m) func (length argOps) body.localDecls body.layouts
        h_ext]
      exact h_res_pure)
    h_args h_lookup
    (fun _ _ => ⟨rfl, rfl, h_arity, h_param_tys, h_extra_pre⟩)
    (fun m _ retVal hm hp =>
      ⟨(ModularRootMemory.of_callFrameAndTraitsPreserved hm hp.1).2.2.1,
        h_imp retVal hp.2⟩)
    (fun m _ hm hp => by
      dsimp only [polyExternalSpecCallContract] at hp
      cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
      · exact False.elim hp
      · rw [hp.1.2.1, hm.2.2.1])

/--
Subsumption-aware 1-step pure `CallConv.rustIntrinsic` `tailCall` rule
supporting both constant and local/projected zero-sized `RigidTy.fnDef`
operands (`extractPureCalleeTarget?` + `resolvePureCalleeTarget`).
-/
theorem PureMirModularConverges.tailCall_intrinsic_pureTarget
    {contract : MirCallContract}
    {pointerBytes : Nat}
    {ubChecksEnabled : Bool}
    {rtEval : DefPath → List RigidTy → List Value → Option Value}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {defPath : DefPath}
    {typeArgs : List RigidTy}
    {resolvedTarget : ResolvedCallTarget}
    {kind : PureRustIntrinsicKind}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {retVal : Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (defPath, typeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func defPath typeArgs body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup : lookupCallee callees body.layouts defPath typeArgs traitImpls = none)
    (h_kind : classifyPureRustIntrinsic? defPath = some kind)
    (h_eval :
      evalPureRustIntrinsicWithRuntime rtEval kind typeArgs argVals pointerBytes
        ubChecksEnabled = some retVal)
    (h_post : post retVal) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  exact PureMirModularConverges.tailCall_modular_resolved
    (subContract := pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
    (resolvedTarget := { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false })
    h_sub
    h_phase h_bb h_end h_term h_args_pure
    (fun m _ => by
      rw [resolveCallTarget_eq_of_extractPureCalleeTarget
        (ps.toMachineState m) func (length argOps) body.localDecls body.layouts
        h_ext]
      exact h_res_pure)
    h_args h_lookup
    (fun _ _ => ⟨kind, retVal, h_kind, h_eval⟩)
    (fun m _ rv hm hp => by
      rcases hp with ⟨rfl, _, hk', hev'⟩
      rw [h_kind] at hk'
      injection hk' with hk_eq
      subst hk_eq
      rw [h_eval] at hev'
      injection hev' with hrv_eq
      subst hrv_eq
      exact ⟨hm.2.2.1, h_post⟩)
    (fun _ _ _ hp => False.elim hp)


end Anneal.PureMirExec
end ModularPureExecContinuation

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
    (h_post : post val)
    (h_init : valueContainsUninit val = false := by rfl) :
    LiftStmtsTerminator body bbIdx stmtIdx env bb.statements bb.terminator post 1 := by
  have h_bb' := lookup_cleanup_false_of_mirLiftReady h_ready h_bb
  rw [h_term] at h_bb' ⊢
  exact LiftStmtsTerminator.term_return h_bb' (phase_of_mirLiftReady h_ready) h_end h_ret h_post h_init

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
private theorem wpPureMirSteps_step
    {fuel : Nat} {body : CapturedMir} {ps ps' : PureState}
    {mid : PureState → Prop} {post : Value → Prop}
    (h_step : stepMirState body (.running (ps.toMachineState emptyMemory)) =
      .tau (.running (ps'.toMachineState emptyMemory)))
    (h_next : wpPureMirSteps fuel body ps' mid post) :
    wpPureMirSteps (fuel + 1) body ps mid post := by
  unfold wpPureMirSteps wpMirStepsSym wpMirExecStepsSym
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq, h_step]
  exact h_next

private theorem wpPureMirSteps_return
    {fuel : Nat} {body : CapturedMir} {ps : PureState} {v : Value} {m : Memory}
    {mid : PureState → Prop} {post : Value → Prop}
    (h_step : stepMirState body (.running (ps.toMachineState emptyMemory)) =
      .ret (.normal (v, m)))
    (h_post : post v) :
    wpPureMirSteps (fuel + 1) body ps mid post := by
  unfold wpPureMirSteps wpMirStepsSym wpMirExecStepsSym
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq, h_step]
  exact h_post

private theorem countdown_step_bb0_0 (x : Nat) :
    stepMirState witnessCountdownAccumLoop
      (.running (PureState.toMachineState
        { bb := 0, stmtIdx := 0, env := [.uninit, .init (.scalar ⟨x, 4⟩)] } emptyMemory)) =
    .tau (.running (PureState.toMachineState
      { bb := 0, stmtIdx := 1, env := [.init (.scalar ⟨0, 4⟩), .init (.scalar ⟨x, 4⟩)] }
      emptyMemory)) := rfl

private theorem countdown_step_bb0_1 (x : Nat) :
    stepMirState witnessCountdownAccumLoop
      (.running (PureState.toMachineState
        { bb := 0, stmtIdx := 1, env := [.init (.scalar ⟨0, 4⟩), .init (.scalar ⟨x, 4⟩)] }
        emptyMemory)) =
    .tau (.running (PureState.toMachineState
      { bb := 1, stmtIdx := 0, env := [.init (.scalar ⟨0, 4⟩), .init (.scalar ⟨x, 4⟩)] }
      emptyMemory)) := rfl

private theorem wpPureMirSteps_emit
    {fuel : Nat} {body : CapturedMir} {ps ps' : PureState} {ev : MirObsE.I}
    {mid : PureState → Prop} {post : Value → Prop}
    (h_step : stepMirState body (.running (ps.toMachineState emptyMemory)) =
      .vis (.inr (.inl ev)) (fun _ => .running (ps'.toMachineState emptyMemory)))
    (h_next : wpPureMirSteps fuel body ps' mid post) :
    wpPureMirSteps (fuel + 1) body ps mid post := by
  unfold wpPureMirSteps wpMirStepsSym wpMirExecStepsSym
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq, h_step]
  exact h_next

private theorem countdown_step_bb1_zero (acc : Nat) :
    stepMirState witnessCountdownAccumLoop
      (.running (PureState.toMachineState
        { bb := 1, stmtIdx := 0, env := [.init (.scalar ⟨acc, 4⟩), .init (.scalar ⟨0, 4⟩)] }
        emptyMemory)) =
    .vis (.inr (.inl (.emit (.event 0)))) (fun _ => .running (PureState.toMachineState
      { bb := 3, stmtIdx := 0, env := [.init (.scalar ⟨acc, 4⟩), .init (.scalar ⟨0, 4⟩)] }
      emptyMemory)) := rfl

private theorem countdown_step_bb3 (acc : Nat) :
    stepMirState witnessCountdownAccumLoop
      (.running (PureState.toMachineState
        { bb := 3, stmtIdx := 0, env := [.init (.scalar ⟨acc, 4⟩), .init (.scalar ⟨0, 4⟩)] }
        emptyMemory)) =
    .ret (.normal (.scalar ⟨acc, 4⟩, emptyMemory)) := rfl

private theorem countdown_step_bb1_succ (acc k : Nat) :
    stepMirState witnessCountdownAccumLoop
      (.running (PureState.toMachineState
        { bb := 1, stmtIdx := 0, env := [.init (.scalar ⟨acc, 4⟩), .init (.scalar ⟨k + 1, 4⟩)] }
        emptyMemory)) =
    .vis (.inr (.inl (.emit (.event (k + 1))))) (fun _ => .running (PureState.toMachineState
      { bb := 2, stmtIdx := 0, env := [.init (.scalar ⟨acc, 4⟩), .init (.scalar ⟨k + 1, 4⟩)] }
      emptyMemory)) := rfl

private theorem countdown_step_bb2_0 (acc k : Nat) :
    stepMirState witnessCountdownAccumLoop
      (.running (PureState.toMachineState
        { bb := 2, stmtIdx := 0, env := [.init (.scalar ⟨acc, 4⟩), .init (.scalar ⟨k + 1, 4⟩)] }
        emptyMemory)) =
    .tau (.running (PureState.toMachineState
      { bb := 2, stmtIdx := 1,
        env := [.init (.scalar ⟨wrapScalarBits (acc + 1) (scalarModulus 4), 4⟩),
                .init (.scalar ⟨k + 1, 4⟩)] }
      emptyMemory)) := rfl

private theorem countdown_step_bb2_1 (acc' k : Nat) :
    stepMirState witnessCountdownAccumLoop
      (.running (PureState.toMachineState
        { bb := 2, stmtIdx := 1, env := [.init (.scalar ⟨acc', 4⟩), .init (.scalar ⟨k + 1, 4⟩)] }
        emptyMemory)) =
    .tau (.running (PureState.toMachineState
      { bb := 2, stmtIdx := 2,
        env := [.init (.scalar ⟨acc', 4⟩),
                .init (.scalar ⟨wrapScalarBits (Nat.sub (k + 1) 1) (scalarModulus 4), 4⟩)] }
      emptyMemory)) := rfl

private theorem countdown_step_bb2_2 (acc' rem' : Nat) :
    stepMirState witnessCountdownAccumLoop
      (.running (PureState.toMachineState
        { bb := 2, stmtIdx := 2, env := [.init (.scalar ⟨acc', 4⟩), .init (.scalar ⟨rem', 4⟩)] }
        emptyMemory)) =
    .tau (.running (PureState.toMachineState
      { bb := 1, stmtIdx := 0, env := [.init (.scalar ⟨acc', 4⟩), .init (.scalar ⟨rem', 4⟩)] }
      emptyMemory)) := rfl

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
    refine ⟨2, wpPureMirSteps_step (countdown_step_bb0_0 x) (wpPureMirSteps_step (countdown_step_bb0_1 x) ?_)⟩
    refine ⟨.inr x, ⟨x, hx, rfl, Nat.le_refl x, ?_⟩, by dsimp [countdownRank]; omega⟩
    dsimp only [PureState.ofMachineState, PureState.toMachineState]
    rw [Nat.sub_self]
  | inr rem =>
    rcases h_st with ⟨h_rem_le, rfl⟩
    cases rem with
    | zero =>
      refine ⟨2, wpPureMirSteps_emit (countdown_step_bb1_zero (x - 0))
        (wpPureMirSteps_return (countdown_step_bb3 (x - 0)) ?_)⟩
      have h_sub0 : x - 0 = x := Nat.sub_zero x
      rw [h_sub0]
      refine ⟨rfl, ?_⟩
      intro x' h_eq
      injection h_eq with h_sc _
    | succ k =>
      have h_acc_wrap : wrapScalarBits (x - (k + 1) + 1) (scalarModulus 4) = x - k := by
        have h_eq : x - (k + 1) + 1 = x - k := by omega
        rw [h_eq]
        exact wrapScalarBits_u32_of_lt (by omega)
      have h_rem_wrap : wrapScalarBits (Nat.sub (k + 1) 1) (scalarModulus 4) = k := by
        have h_eq : Nat.sub (k + 1) 1 = k := Nat.add_sub_cancel k 1
        rw [h_eq]
        exact wrapScalarBits_u32_of_lt (by omega)
      have h2_0 := countdown_step_bb2_0 (x - (k + 1)) k
      rw [h_acc_wrap] at h2_0
      have h2_1 := countdown_step_bb2_1 (x - k) k
      rw [h_rem_wrap] at h2_1
      refine ⟨4,
        wpPureMirSteps_emit (countdown_step_bb1_succ (x - (k + 1)) k)
          (wpPureMirSteps_step h2_0
            (wpPureMirSteps_step h2_1
              (wpPureMirSteps_step (countdown_step_bb2_2 (x - k) k) ?_)))⟩
      exact ⟨.inr k, ⟨x, hx, rfl, by omega, rfl⟩, by dsimp [countdownRank]; omega⟩

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
    (h_post : post val)
    (h_init : valueContainsUninit val = false := by rfl) :
    LiftStmtsConverges body bbIdx stmtIdx env stmts { kind := .return_, span := span } post :=
  ⟨1, LiftStmtsTerminator.term_return h_bb h_phase h_end h_ret h_post h_init⟩

theorem LiftStmtsConverges.term_return_ready {body : CapturedMir}
    {bbIdx : BasicBlockIdx} {stmtIdx : Nat} {env : PureEnv}
    {bb : BasicBlockData} {span : String} {post : Value → Prop} {val : Value}
    (h_ready : checkMirLiftReady body = true)
    (h_bb : Trusted.Sequence.get? body.basicBlocks bbIdx = some bb)
    (h_term : bb.terminator = { kind := .return_, span := span })
    (h_end : stmtIdx = List.length bb.statements)
    (h_ret : Trusted.Sequence.get? env 0 = some (.init val))
    (h_post : post val)
    (h_init : valueContainsUninit val = false := by rfl) :
    LiftStmtsConverges body bbIdx stmtIdx env bb.statements bb.terminator post :=
  ⟨1, LiftStmtsTerminator.term_return_ready h_ready h_bb h_term h_end h_ret h_post h_init⟩

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
      ensureNestedFieldShells
        rootVal
        proj
        localDecls
        layouts
        (placeTy localDecls layouts { local_ := dstLoc, projection := .nil })
    with
    | .none => MirStepNode.fail .ub
    | .some shelledRoot =>
      match
        writeProjectedForLocal
          locals₁
          localDecls
          layouts
          dstLoc
          shelledRoot
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
    match proj with
    | hd :: tl =>
      match uninitFieldWriteShell? localDecls layouts dstLoc hd tl with
      | .some rootVal =>
        match writeProjectedForLocal locals₁ localDecls layouts dstLoc rootVal (hd :: tl) val with
        | .ok rootVal' =>
          match set? locals₁ dstLoc (.init rootVal') with
          | .some locals₂ =>
            let resolvedLocalProj :=
              resolveBorrowWriteLocalProj
                localDecls
                layouts
                locals₁
                dstLoc
                (hd :: tl)
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
    | .nil => MirStepNode.fail .ub
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

/-- Every `.tau` / observation `.running` successor of `n` satisfies `P`. -/
def NodeSuccs (P : MachineState → Prop) : MirStepNode → Prop
  | .tau (.running s') => P s'
  | .vis (.inr (.inl _)) k =>
    match k PUnit.unit with
    | .running s' => P s'
    | _ => True
  | _ => True

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

theorem internFnPtr_callStack (mem : Memory) (defPath : DefPath) (typeArgs : List RigidTy)
    (fnSig : Option RigidTy) : (internFnPtr mem defPath typeArgs fnSig).2.callStack =
      mem.callStack := by
  unfold internFnPtr
  split <;> rfl

theorem invalidateDirectDestWriteBorrows_callStack (mem : Memory) (locals : List LocalSlot)
    (dst : Place) : (invalidateDirectDestWriteBorrows mem locals dst).callStack = mem.callStack := by
  unfold invalidateDirectDestWriteBorrows
  try dsimp only
  repeat' (first | rfl | split)

private theorem ns_advance {cs : List SavedCallerFrame} {s : MachineState} {l : List LocalSlot}
    {M : Memory} (h : CallerBodiesEq cs M.callStack) :
    NodeSuccs (fun s' => CallerBodiesEq cs s'.memory.callStack)
      (MirStepNode.step (advanceStmt s l M)) := h

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

/-- Combined callee-context independence and `RvCS` call-stack invariance for `RvalueEvalResult`,
so each rvalue helper is split once instead of twice. -/
private def RvCtxCS (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (cs : List SavedCallerFrame) (r1 r2 : RvalueEvalResult) : Prop :=
  r1 = RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti) r2 ∧ RvCS cs r2

private theorem rvCtxCS_ub {c : CalleeEnv} {ac : Option CapturedMir} {ti : List TraitImplEntry}
    {cs : List SavedCallerFrame} : RvCtxCS c ac ti cs .ub .ub := ⟨rfl, trivial⟩

private theorem rvCtxCS_unsupported {c : CalleeEnv} {ac : Option CapturedMir}
    {ti : List TraitImplEntry} {cs : List SavedCallerFrame} :
    RvCtxCS c ac ti cs .unsupported .unsupported := ⟨rfl, trivial⟩

private theorem rvCtxCS_ok {c : CalleeEnv} {ac : Option CapturedMir} {ti : List TraitImplEntry}
    {cs : List SavedCallerFrame} {v : Value} {l : List LocalSlot} {m1 m2 : Memory}
    (h1 : m1 = Memory.withCalleeCtx c ac ti m2) (h2 : m2.callStack = cs) :
    RvCtxCS c ac ti cs (.ok v l m1) (.ok v l m2) :=
  ⟨h1 ▸ rfl, h2⟩

/-- Combined callee-context independence and `CallerBodiesEq` invariance for `MirStepNode`,
so each statement / intrinsic helper is split once instead of twice. -/
private def StepCtxCB (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (cs : List SavedCallerFrame) (n1 n2 : MirStepNode) : Prop :=
  n1 = MirStepNode.mapMem (Memory.withCalleeCtx c ac ti) n2 ∧
    NodeSuccs (fun s' => CallerBodiesEq cs s'.memory.callStack) n2

private theorem stepCtxCB_fail {c : CalleeEnv} {ac : Option CapturedMir}
    {ti : List TraitImplEntry} {cs : List SavedCallerFrame} {fk : FailureKind} :
    StepCtxCB c ac ti cs (.fail fk) (.fail fk) := ⟨rfl, trivial⟩

private theorem stepCtxCB_unsupported {c : CalleeEnv} {ac : Option CapturedMir}
    {ti : List TraitImplEntry} {cs : List SavedCallerFrame} :
    StepCtxCB c ac ti cs .unsupported .unsupported := ⟨rfl, trivial⟩

private theorem stepCtxCB_mk {c : CalleeEnv} {ac : Option CapturedMir}
    {ti : List TraitImplEntry} {cs : List SavedCallerFrame}
    {f : StackFrame} {m1 m2 : Memory}
    (h1 : m1 = Memory.withCalleeCtx c ac ti m2) (h2 : CallerBodiesEq cs m2.callStack) :
    StepCtxCB c ac ti cs (.step { frame := f, memory := m1 }) (.step { frame := f, memory := m2 }) :=
  ⟨h1 ▸ rfl, h2⟩

private theorem stepCtxCB_advance {c : CalleeEnv} {ac : Option CapturedMir}
    {ti : List TraitImplEntry} {cs : List SavedCallerFrame}
    {s1 s2 : MachineState} {l : List LocalSlot} {m1 m2 : Memory}
    (hf : s1.frame = s2.frame) (h1 : m1 = Memory.withCalleeCtx c ac ti m2)
    (h2 : CallerBodiesEq cs m2.callStack) :
    StepCtxCB c ac ti cs (.step (advanceStmt s1 l m1)) (.step (advanceStmt s2 l m2)) := by
  unfold advanceStmt StepCtxCB
  rw [hf, h1]
  exact ⟨rfl, h2⟩

private theorem evalUnsafeFnPointer_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalUnsafeFnPointer locals op targetTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalUnsafeFnPointer locals op targetTy mem localDecls layouts) := by
  unfold evalUnsafeFnPointer
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalUnsafeFnPointer_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUnsafeFnPointer locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalUnsafeFnPointer locals op targetTy mem localDecls layouts) :=
  (evalUnsafeFnPointer_rvCtxCS c ac ti locals op targetTy mem localDecls layouts).1

theorem evalUnsafeFnPointer_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalUnsafeFnPointer locals op targetTy mem localDecls layouts) :=
  (evalUnsafeFnPointer_rvCtxCS [] none [] locals op targetTy mem localDecls layouts).2

private theorem deriveStackElemThinPtr_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mem : Memory) (ptrVal : ProvenancePtr)
    (parentEntry : BorrowEntry) (elemCountOpt : Option Nat) (ptrBytes : Nat) :
    RvCtxCS c ac ti mem.callStack
      (deriveStackElemThinPtr locals (Memory.withCalleeCtx c ac ti mem) ptrVal parentEntry elemCountOpt ptrBytes)
      (deriveStackElemThinPtr locals mem ptrVal parentEntry elemCountOpt ptrBytes) := by
  unfold deriveStackElemThinPtr
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem deriveStackElemThinPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mem : Memory) (ptrVal : ProvenancePtr)
    (parentEntry : BorrowEntry) (elemCountOpt : Option Nat)
    (ptrBytes : Nat) :
    deriveStackElemThinPtr locals (Memory.withCalleeCtx c ac ti mem)
        ptrVal parentEntry elemCountOpt ptrBytes =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (deriveStackElemThinPtr locals mem ptrVal parentEntry elemCountOpt ptrBytes) :=
  (deriveStackElemThinPtr_rvCtxCS c ac ti locals mem ptrVal parentEntry elemCountOpt ptrBytes).1

theorem deriveStackElemThinPtr_rvCS (locals : List LocalSlot) (mem : Memory)
    (ptrVal : ProvenancePtr) (parentEntry : BorrowEntry) (elemCountOpt : Option Nat)
    (ptrBytes : Nat) :
    RvCS mem.callStack
      (deriveStackElemThinPtr locals mem ptrVal parentEntry elemCountOpt ptrBytes) :=
  (deriveStackElemThinPtr_rvCtxCS [] none [] locals mem ptrVal parentEntry elemCountOpt ptrBytes).2

private theorem evalUnsizeCoercion_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalUnsizeCoercion locals op targetTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalUnsizeCoercion locals op targetTy mem localDecls layouts) := by
  unfold evalUnsizeCoercion
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalUnsizeCoercion_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUnsizeCoercion locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalUnsizeCoercion locals op targetTy mem localDecls layouts) :=
  (evalUnsizeCoercion_rvCtxCS c ac ti locals op targetTy mem localDecls layouts).1

theorem evalUnsizeCoercion_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalUnsizeCoercion locals op targetTy mem localDecls layouts) :=
  (evalUnsizeCoercion_rvCtxCS [] none [] locals op targetTy mem localDecls layouts).2

private theorem evalSliceFatPtrDerefBorrow_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mem : Memory) (parentPtr : ProvenancePtr)
    (ptrSz : Nat) (lenSc : ScalarInt) (restProj : List ProjectionElem)
    (perm : TreeBorrowPerm) (isMut : Bool) (pointeeTyOpt : Option Ty)
    (layouts : LayoutTable) (checkPerm : Bool)
    (localDecls : List LocalDecl) (fullPlaceTyOpt : Option Ty)
    (checkRefElemAlign : Bool) :
    RvCtxCS c ac ti mem.callStack
      (evalSliceFatPtrDerefBorrow locals (Memory.withCalleeCtx c ac ti mem)
        parentPtr ptrSz lenSc restProj perm isMut pointeeTyOpt layouts checkPerm
        localDecls fullPlaceTyOpt checkRefElemAlign)
      (evalSliceFatPtrDerefBorrow locals mem
        parentPtr ptrSz lenSc restProj perm isMut pointeeTyOpt layouts checkPerm
        localDecls fullPlaceTyOpt checkRefElemAlign) := by
  unfold evalSliceFatPtrDerefBorrow
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

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
          localDecls fullPlaceTyOpt checkRefElemAlign) :=
  (evalSliceFatPtrDerefBorrow_rvCtxCS c ac ti locals mem parentPtr ptrSz lenSc restProj perm isMut
    pointeeTyOpt layouts checkPerm localDecls fullPlaceTyOpt checkRefElemAlign).1

theorem evalSliceFatPtrDerefBorrow_rvCS (locals : List LocalSlot) (mem : Memory)
    (parentPtr : ProvenancePtr) (ptrSz : Nat) (lenSc : ScalarInt)
    (restProj : List ProjectionElem) (perm : TreeBorrowPerm) (isMut : Bool)
    (pointeeTyOpt : Option Ty) (layouts : LayoutTable) (checkPerm : Bool)
    (localDecls : List LocalDecl) (accessedTyOpt : Option Ty) (checkResultRefAlign : Bool) :
    RvCS mem.callStack
      (evalSliceFatPtrDerefBorrow locals mem parentPtr ptrSz lenSc restProj perm isMut
        pointeeTyOpt layouts checkPerm localDecls accessedTyOpt checkResultRefAlign) :=
  (evalSliceFatPtrDerefBorrow_rvCtxCS [] none [] locals mem parentPtr ptrSz lenSc restProj perm
    isMut pointeeTyOpt layouts checkPerm localDecls accessedTyOpt checkResultRefAlign).2

private theorem evalGlobalThinPtrDerefBorrow_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mem : Memory) (alloc : CapturedAllocation)
    (parentPtr : ProvenancePtr) (ptrSz : Nat) (restProj : List ProjectionElem)
    (isMut : Bool) (pointeeTyOpt : Option Ty) (layouts : LayoutTable)
    (localDecls : List LocalDecl) (rawPtrMode : Bool)
    (fullPlaceTyOpt : Option Ty) :
    RvCtxCS c ac ti mem.callStack
      (evalGlobalThinPtrDerefBorrow locals (Memory.withCalleeCtx c ac ti mem)
        alloc parentPtr ptrSz restProj isMut pointeeTyOpt layouts localDecls rawPtrMode
        fullPlaceTyOpt)
      (evalGlobalThinPtrDerefBorrow locals mem
        alloc parentPtr ptrSz restProj isMut pointeeTyOpt layouts localDecls rawPtrMode
        fullPlaceTyOpt) := by
  unfold evalGlobalThinPtrDerefBorrow
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

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
          fullPlaceTyOpt) :=
  (evalGlobalThinPtrDerefBorrow_rvCtxCS c ac ti locals mem alloc parentPtr ptrSz restProj isMut
    pointeeTyOpt layouts localDecls rawPtrMode fullPlaceTyOpt).1

theorem evalGlobalThinPtrDerefBorrow_rvCS (locals : List LocalSlot) (mem : Memory)
    (alloc : CapturedAllocation) (parentPtr : ProvenancePtr) (ptrSz : Nat)
    (restProj : List ProjectionElem) (isMut : Bool) (pointeeTyOpt : Option Ty)
    (layouts : LayoutTable) (localDecls : List LocalDecl) (rawPtrMode : Bool)
    (accessedTyOpt : Option Ty) :
    RvCS mem.callStack
      (evalGlobalThinPtrDerefBorrow locals mem alloc parentPtr ptrSz restProj isMut
        pointeeTyOpt layouts localDecls rawPtrMode accessedTyOpt) :=
  (evalGlobalThinPtrDerefBorrow_rvCtxCS [] none [] locals mem alloc parentPtr ptrSz restProj isMut
    pointeeTyOpt layouts localDecls rawPtrMode accessedTyOpt).2

private theorem evalScalarSliceFatPtrDerefRaw_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mem : Memory) (addrSc lenSc : ScalarInt)
    (restProj : List ProjectionElem) (pointeeTyOpt : Option Ty)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalScalarSliceFatPtrDerefRaw locals (Memory.withCalleeCtx c ac ti mem)
        addrSc lenSc restProj pointeeTyOpt localDecls layouts)
      (evalScalarSliceFatPtrDerefRaw locals mem
        addrSc lenSc restProj pointeeTyOpt localDecls layouts) := by
  unfold evalScalarSliceFatPtrDerefRaw
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

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
          addrSc lenSc restProj pointeeTyOpt localDecls layouts) :=
  (evalScalarSliceFatPtrDerefRaw_rvCtxCS c ac ti locals mem addrSc lenSc restProj pointeeTyOpt
    localDecls layouts).1

theorem evalScalarSliceFatPtrDerefRaw_rvCS (locals : List LocalSlot) (mem : Memory)
    (addrSc lenSc : ScalarInt) (restProj : List ProjectionElem) (pointeeTyOpt : Option Ty)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalScalarSliceFatPtrDerefRaw locals mem addrSc lenSc restProj pointeeTyOpt localDecls
        layouts) :=
  (evalScalarSliceFatPtrDerefRaw_rvCtxCS [] none [] locals mem addrSc lenSc restProj pointeeTyOpt
    localDecls layouts).2

private theorem evalScalarPtrOffsetBinOp_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp : Operand) (lhs rhs : ScalarInt) :
    RvCtxCS c ac ti mem.callStack
      (evalScalarPtrOffsetBinOp locals₂ (Memory.withCalleeCtx c ac ti mem) localDecls layouts lhsOp lhs rhs)
      (evalScalarPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp lhs rhs) := by
  unfold evalScalarPtrOffsetBinOp
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalScalarPtrOffsetBinOp_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp : Operand) (lhs rhs : ScalarInt) :
    evalScalarPtrOffsetBinOp locals₂
        (Memory.withCalleeCtx c ac ti mem)
        localDecls layouts lhsOp lhs rhs =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalScalarPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp lhs rhs) :=
  (evalScalarPtrOffsetBinOp_rvCtxCS c ac ti locals₂ mem localDecls layouts lhsOp lhs rhs).1

theorem evalScalarPtrOffsetBinOp_rvCS (locals₂ : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (lhsOp : Operand)
    (lhs rhs : ScalarInt) :
    RvCS mem.callStack
      (evalScalarPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp lhs rhs) :=
  (evalScalarPtrOffsetBinOp_rvCtxCS [] none [] locals₂ mem localDecls layouts lhsOp lhs rhs).2

private theorem evalPtrOffsetBinOp_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp : Operand) (ptrVal : ProvenancePtr)
    (sz : Nat) (offsetSc : ScalarInt) :
    RvCtxCS c ac ti mem.callStack
      (evalPtrOffsetBinOp locals₂ (Memory.withCalleeCtx c ac ti mem) localDecls layouts lhsOp ptrVal sz offsetSc)
      (evalPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc) := by
  unfold evalPtrOffsetBinOp ptrAllocByteBound?
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalPtrOffsetBinOp_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp : Operand) (ptrVal : ProvenancePtr)
    (sz : Nat) (offsetSc : ScalarInt) :
    evalPtrOffsetBinOp locals₂ (Memory.withCalleeCtx c ac ti mem)
        localDecls layouts lhsOp ptrVal sz offsetSc =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp ptrVal sz
          offsetSc) :=
  (evalPtrOffsetBinOp_rvCtxCS c ac ti locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc).1

theorem evalPtrOffsetBinOp_rvCS (locals₂ : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (lhsOp : Operand)
    (ptrVal : ProvenancePtr) (sz : Nat) (offsetSc : ScalarInt) :
    RvCS mem.callStack
      (evalPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc) :=
  (evalPtrOffsetBinOp_rvCtxCS [] none [] locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc).2

private theorem evalPlaceLen_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (place : Place) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalPlaceLen locals place (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalPlaceLen locals place mem localDecls layouts) := by
  unfold evalPlaceLen
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalPlaceLen_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (place : Place) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPlaceLen locals place (Memory.withCalleeCtx c ac ti mem)
        localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalPlaceLen locals place mem localDecls layouts) :=
  (evalPlaceLen_rvCtxCS c ac ti locals place mem localDecls layouts).1

theorem evalPlaceLen_rvCS (locals : List LocalSlot) (place : Place) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalPlaceLen locals place mem localDecls layouts) :=
  (evalPlaceLen_rvCtxCS [] none [] locals place mem localDecls layouts).2

private theorem evalPlaceDiscriminant_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (val : Value) (locals' : List LocalSlot) (mem : Memory) (place : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalPlaceDiscriminant val locals' (Memory.withCalleeCtx c ac ti mem) place localDecls layouts)
      (evalPlaceDiscriminant val locals' mem place localDecls layouts) := by
  unfold evalPlaceDiscriminant
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)
  all_goals try dsimp (config := { zeta := true })
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalPlaceDiscriminant_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (val : Value) (locals' : List LocalSlot) (mem : Memory) (place : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPlaceDiscriminant val locals'
        (Memory.withCalleeCtx c ac ti mem) place localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalPlaceDiscriminant val locals' mem place localDecls layouts) :=
  (evalPlaceDiscriminant_rvCtxCS c ac ti val locals' mem place localDecls layouts).1

theorem evalPlaceDiscriminant_rvCS (val : Value) (locals' : List LocalSlot) (mem : Memory)
    (place : Place) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalPlaceDiscriminant val locals' mem place localDecls layouts) :=
  (evalPlaceDiscriminant_rvCtxCS [] none [] val locals' mem place localDecls layouts).2

private theorem evalReifyFnPointer_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (coercionKind : String)
    (h_free : isReifyFnPointerCoercion coercionKind = false ∨
      stringEq coercionKind "UnsafeFnPointer" = true) :
    RvCtxCS c ac ti mem.callStack
      (evalReifyFnPointer locals op targetTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts coercionKind)
      (evalReifyFnPointer locals op targetTy mem localDecls layouts coercionKind) := by
  have hUnsize : RvCtxCS c ac ti mem.callStack
      (evalUnsizeCoercion locals op targetTy
        { mem with callees := c, activeCallee := ac, traitImpls := ti } localDecls layouts)
      (evalUnsizeCoercion locals op targetTy mem localDecls layouts) :=
    ⟨evalUnsizeCoercion_withCalleeCtx c ac ti locals op targetTy mem localDecls layouts,
     evalUnsizeCoercion_rvCS locals op targetTy mem localDecls layouts⟩
  have hDerive : ∀ l m p e len sz,
      RvCtxCS c ac ti m.callStack
        (deriveStackElemThinPtr l { m with callees := c, activeCallee := ac, traitImpls := ti } p e len sz)
        (deriveStackElemThinPtr l m p e len sz) :=
    fun l m p e len sz =>
      ⟨deriveStackElemThinPtr_withCalleeCtx c ac ti l m p e len sz,
       deriveStackElemThinPtr_rvCS l m p e len sz⟩
  unfold evalReifyFnPointer
  cases h_r : isReifyFnPointerCoercion coercionKind with
  | false =>
    dsimp only [Memory.withCalleeCtx]
    repeat' (first
      | with_reducible (first
        | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl
        | exact hUnsize
        | exact hDerive ..)
      | split)
  | true =>
    cases h_s : stringEq coercionKind "UnsafeFnPointer" with
    | true =>
      exact ⟨evalUnsafeFnPointer_withCalleeCtx c ac ti locals op targetTy mem localDecls layouts,
        evalUnsafeFnPointer_rvCS locals op targetTy mem localDecls layouts⟩
    | false =>
      exfalso
      rcases h_free with h | h
      · rw [h_r] at h; cases h
      · rw [h_s] at h; cases h

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
          localDecls layouts coercionKind) :=
  (evalReifyFnPointer_rvCtxCS c ac ti locals op targetTy mem localDecls layouts coercionKind h_free).1

theorem evalReifyFnPointer_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (coercionKind : String) :
    RvCS mem.callStack
      (evalReifyFnPointer locals op targetTy mem localDecls layouts coercionKind) := by
  cases h_r : isReifyFnPointerCoercion coercionKind with
  | false =>
    exact (evalReifyFnPointer_rvCtxCS [] none [] locals op targetTy mem localDecls layouts
      coercionKind (Or.inl h_r)).2
  | true =>
    unfold evalReifyFnPointer
    rw [h_r]
    dsimp only
    cases stringEq coercionKind "UnsafeFnPointer" with
    | true => exact evalUnsafeFnPointer_rvCS locals op targetTy mem localDecls layouts
    | false =>
      dsimp only
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals (callStack := mem.callStack) with
      | ub => exact rvCS_ub
      | unsupported => exact rvCS_unsupported
      | ok v locals' =>
        dsimp only
        split
        · exact rvCS_ub
        · cases targetTy.kind with
          | fnPtr fnInputs fnOutput fnSafety fnAbi =>
            dsimp only
            cases Bool.and (Bool.not (callConvEq fnAbi .rustIntrinsic))
                (reifyCoercionSafetyCompatible coercionKind fnSafety) with
            | false => exact rvCS_ub
            | true =>
              dsimp only
              cases extractReifyCoercionTarget? coercionKind (operandTy localDecls layouts op) with
              | none => exact rvCS_ub
              | some pair =>
                rcases pair with ⟨defPath, typeArgs⟩
                dsimp only
                cases checkCalleeSig mem.callees defPath fnInputs fnOutput fnAbi typeArgs mem.traitImpls with
                | false => exact rvCS_ub
                | true =>
                  exact rvCS_ok (internFnPtr_callStack mem defPath typeArgs (.some _))
          | _ => exact rvCS_ub

private theorem evalFnPtrToPtr_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalFnPtrToPtr locals op targetTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalFnPtrToPtr locals op targetTy mem localDecls layouts) := by
  unfold evalFnPtrToPtr
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalFnPtrToPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalFnPtrToPtr locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalFnPtrToPtr locals op targetTy mem localDecls layouts) :=
  (evalFnPtrToPtr_rvCtxCS c ac ti locals op targetTy mem localDecls layouts).1

theorem evalFnPtrToPtr_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalFnPtrToPtr locals op targetTy mem localDecls layouts) :=
  (evalFnPtrToPtr_rvCtxCS [] none [] locals op targetTy mem localDecls layouts).2

private theorem evalByteCast_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalByteCast locals op targetTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalByteCast locals op targetTy mem localDecls layouts) := by
  unfold evalByteCast
  dsimp only [Memory.withCalleeCtx]
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => exact rvCtxCS_ub
  | unsupported => exact rvCtxCS_unsupported
  | ok v locals' =>
    dsimp only
    repeat' (first
      | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
      | split)
    all_goals try dsimp (config := { zeta := true })
    repeat' (first
      | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
      | split)

theorem evalByteCast_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalByteCast locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalByteCast locals op targetTy mem localDecls layouts) :=
  (evalByteCast_rvCtxCS c ac ti locals op targetTy mem localDecls layouts).1

theorem evalByteCast_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalByteCast locals op targetTy mem localDecls layouts) :=
  (evalByteCast_rvCtxCS [] none [] locals op targetTy mem localDecls layouts).2

private theorem evalSignedDiv_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    RvCtxCS c ac ti mem.callStack
      (evalSignedDiv a b sz locals (Memory.withCalleeCtx c ac ti mem))
      (evalSignedDiv a b sz locals mem) := by
  unfold evalSignedDiv
  dsimp only
  cases Bool.and
    (Nat.beq (wrapScalarBits a (scalarModulus sz))
      (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz))
      (Nat.sub (scalarModulus sz) 1)) with
  | true => exact rvCtxCS_ub
  | false => exact rvCtxCS_ok rfl rfl

theorem evalSignedDiv_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedDiv a b sz locals (Memory.withCalleeCtx c ac ti mem) =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalSignedDiv a b sz locals mem) :=
  (evalSignedDiv_rvCtxCS c ac ti a b sz locals mem).1

theorem evalSignedDiv_rvCS (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    RvCS mem.callStack (evalSignedDiv a b sz locals mem) :=
  (evalSignedDiv_rvCtxCS [] none [] a b sz locals mem).2

private theorem evalSignedRem_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    RvCtxCS c ac ti mem.callStack
      (evalSignedRem a b sz locals (Memory.withCalleeCtx c ac ti mem))
      (evalSignedRem a b sz locals mem) := by
  unfold evalSignedRem
  dsimp only
  cases Bool.and
    (Nat.beq (wrapScalarBits a (scalarModulus sz))
      (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz))
      (Nat.sub (scalarModulus sz) 1)) with
  | true => exact rvCtxCS_ub
  | false => exact rvCtxCS_ok rfl rfl

theorem evalSignedRem_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedRem a b sz locals (Memory.withCalleeCtx c ac ti mem) =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalSignedRem a b sz locals mem) :=
  (evalSignedRem_rvCtxCS c ac ti a b sz locals mem).1

theorem evalSignedRem_rvCS (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    RvCS mem.callStack (evalSignedRem a b sz locals mem) :=
  (evalSignedRem_rvCtxCS [] none [] a b sz locals mem).2

private theorem evalScalarBinOp_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (op : BinOp) (lhs rhs : ScalarInt) (locals : List LocalSlot)
    (mem : Memory) (isSigned : Bool) :
    RvCtxCS c ac ti mem.callStack
      (evalScalarBinOp op lhs rhs locals (Memory.withCalleeCtx c ac ti mem) isSigned)
      (evalScalarBinOp op lhs rhs locals mem isSigned) := by
  unfold evalScalarBinOp
  cases Nat.beq lhs.sizeBytes 0 with
  | true => exact rvCtxCS_unsupported
  | false =>
    have hDiv : ∀ a b sz l m,
        RvCtxCS c ac ti m.callStack
          (evalSignedDiv a b sz l (Memory.withCalleeCtx c ac ti m))
          (evalSignedDiv a b sz l m) :=
      fun a b sz l m => ⟨evalSignedDiv_withCalleeCtx c ac ti a b sz l m,
        evalSignedDiv_rvCS a b sz l m⟩
    have hRem : ∀ a b sz l m,
        RvCtxCS c ac ti m.callStack
          (evalSignedRem a b sz l (Memory.withCalleeCtx c ac ti m))
          (evalSignedRem a b sz l m) :=
      fun a b sz l m => ⟨evalSignedRem_withCalleeCtx c ac ti a b sz l m,
        evalSignedRem_rvCS a b sz l m⟩
    dsimp only
    cases op <;> dsimp only
    all_goals
      repeat' (first
        | with_reducible (first
          | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl
          | exact hDiv .. | exact hRem ..)
        | split)

theorem evalScalarBinOp_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (op : BinOp) (lhs rhs : ScalarInt) (locals : List LocalSlot)
    (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp op lhs rhs locals
        (Memory.withCalleeCtx c ac ti mem) isSigned =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalScalarBinOp op lhs rhs locals mem isSigned) :=
  (evalScalarBinOp_rvCtxCS c ac ti op lhs rhs locals mem isSigned).1

theorem evalScalarBinOp_rvCS (op : BinOp) (lhs rhs : ScalarInt) (locals : List LocalSlot)
    (mem : Memory) (isSigned : Bool) :
    RvCS mem.callStack (evalScalarBinOp op lhs rhs locals mem isSigned) :=
  (evalScalarBinOp_rvCtxCS [] none [] op lhs rhs locals mem isSigned).2

private theorem evalUnaryNot_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    RvCtxCS c ac ti mem.callStack
      (evalUnaryNot sc optTy locals (Memory.withCalleeCtx c ac ti mem))
      (evalUnaryNot sc optTy locals mem) := by
  unfold evalUnaryNot
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalUnaryNot_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    evalUnaryNot sc optTy locals
        (Memory.withCalleeCtx c ac ti mem) =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalUnaryNot sc optTy locals mem) :=
  (evalUnaryNot_rvCtxCS c ac ti sc optTy locals mem).1

theorem evalUnaryNot_rvCS (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    RvCS mem.callStack (evalUnaryNot sc optTy locals mem) :=
  (evalUnaryNot_rvCtxCS [] none [] sc optTy locals mem).2

private theorem evalRvalueRefDeref_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (borrowKind : BorrowKind) (place : Place)
    (restProj : List ProjectionElem) (perm : TreeBorrowPerm) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalRvalueRefDeref locals borrowKind place restProj perm (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalRvalueRefDeref locals borrowKind place restProj perm mem localDecls layouts) := by
  have hSlice : ∀ l m p ps ls rp pm im pt ly cp ld fpt cra,
      RvCtxCS c ac ti m.callStack
        (evalSliceFatPtrDerefBorrow l { m with callees := c, activeCallee := ac, traitImpls := ti } p ps ls rp pm im pt ly cp ld fpt cra)
        (evalSliceFatPtrDerefBorrow l m p ps ls rp pm im pt ly cp ld fpt cra) :=
    fun l m p ps ls rp pm im pt ly cp ld fpt cra =>
      ⟨evalSliceFatPtrDerefBorrow_withCalleeCtx c ac ti l m p ps ls rp pm im pt ly cp ld fpt cra,
       evalSliceFatPtrDerefBorrow_rvCS l m p ps ls rp pm im pt ly cp ld fpt cra⟩
  have hGlob : ∀ l m a p ps rp im pt ly ld rpm fpt,
      RvCtxCS c ac ti m.callStack
        (evalGlobalThinPtrDerefBorrow l { m with callees := c, activeCallee := ac, traitImpls := ti } a p ps rp im pt ly ld rpm fpt)
        (evalGlobalThinPtrDerefBorrow l m a p ps rp im pt ly ld rpm fpt) :=
    fun l m a p ps rp im pt ly ld rpm fpt =>
      ⟨evalGlobalThinPtrDerefBorrow_withCalleeCtx c ac ti l m a p ps rp im pt ly ld rpm fpt,
       evalGlobalThinPtrDerefBorrow_rvCS l m a p ps rp im pt ly ld rpm fpt⟩
  dsimp only [evalRvalueRefDeref, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl
      | exact hSlice .. | exact hGlob ..)
    | split)

theorem evalRvalueRefDeref_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (borrowKind : BorrowKind) (place : Place)
    (restProj : List ProjectionElem) (perm : TreeBorrowPerm) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalueRefDeref locals borrowKind place restProj perm
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalRvalueRefDeref locals borrowKind place restProj perm mem localDecls layouts) :=
  (evalRvalueRefDeref_rvCtxCS c ac ti locals borrowKind place restProj perm mem localDecls layouts).1

theorem evalRvalueRefDeref_rvCS (locals : List LocalSlot) (borrowKind : BorrowKind)
    (place : Place) (restProj : List ProjectionElem) (perm : TreeBorrowPerm) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalRvalueRefDeref locals borrowKind place restProj perm mem localDecls layouts) :=
  (evalRvalueRefDeref_rvCtxCS [] none [] locals borrowKind place restProj perm mem localDecls
    layouts).2

private theorem evalRvalueRawPtr_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mutability : Mutability) (place : Place)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalRvalueRawPtr locals mutability place (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalRvalueRawPtr locals mutability place mem localDecls layouts) := by
  have hSlice : ∀ l m p ps ls rp pm im pt ly cp ld fpt cra,
      RvCtxCS c ac ti m.callStack
        (evalSliceFatPtrDerefBorrow l { m with callees := c, activeCallee := ac, traitImpls := ti } p ps ls rp pm im pt ly cp ld fpt cra)
        (evalSliceFatPtrDerefBorrow l m p ps ls rp pm im pt ly cp ld fpt cra) :=
    fun l m p ps ls rp pm im pt ly cp ld fpt cra =>
      ⟨evalSliceFatPtrDerefBorrow_withCalleeCtx c ac ti l m p ps ls rp pm im pt ly cp ld fpt cra,
       evalSliceFatPtrDerefBorrow_rvCS l m p ps ls rp pm im pt ly cp ld fpt cra⟩
  have hGlob : ∀ l m a p ps rp im pt ly ld rpm fpt,
      RvCtxCS c ac ti m.callStack
        (evalGlobalThinPtrDerefBorrow l { m with callees := c, activeCallee := ac, traitImpls := ti } a p ps rp im pt ly ld rpm fpt)
        (evalGlobalThinPtrDerefBorrow l m a p ps rp im pt ly ld rpm fpt) :=
    fun l m a p ps rp im pt ly ld rpm fpt =>
      ⟨evalGlobalThinPtrDerefBorrow_withCalleeCtx c ac ti l m a p ps rp im pt ly ld rpm fpt,
       evalGlobalThinPtrDerefBorrow_rvCS l m a p ps rp im pt ly ld rpm fpt⟩
  have hScal : ∀ l m a ls rp pt ld ly,
      RvCtxCS c ac ti m.callStack
        (evalScalarSliceFatPtrDerefRaw l { m with callees := c, activeCallee := ac, traitImpls := ti } a ls rp pt ld ly)
        (evalScalarSliceFatPtrDerefRaw l m a ls rp pt ld ly) :=
    fun l m a ls rp pt ld ly =>
      ⟨evalScalarSliceFatPtrDerefRaw_withCalleeCtx c ac ti l m a ls rp pt ld ly,
       evalScalarSliceFatPtrDerefRaw_rvCS l m a ls rp pt ld ly⟩
  dsimp only [evalRvalueRawPtr, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl
      | exact hSlice .. | exact hGlob .. | exact hScal ..)
    | split)

theorem evalRvalueRawPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (mutability : Mutability) (place : Place)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalueRawPtr locals mutability place
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalRvalueRawPtr locals mutability place mem localDecls layouts) :=
  (evalRvalueRawPtr_rvCtxCS c ac ti locals mutability place mem localDecls layouts).1

theorem evalRvalueRawPtr_rvCS (locals : List LocalSlot) (mutability : Mutability)
    (place : Place) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalRvalueRawPtr locals mutability place mem localDecls layouts) :=
  (evalRvalueRawPtr_rvCtxCS [] none [] locals mutability place mem localDecls layouts).2

private theorem evalCastPtrToPtr_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalCastPtrToPtr locals op targetTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalCastPtrToPtr locals op targetTy mem localDecls layouts) := by
  have hDerive : ∀ l m p e el pb,
      RvCtxCS c ac ti m.callStack
        (deriveStackElemThinPtr l { m with callees := c, activeCallee := ac, traitImpls := ti } p e el pb)
        (deriveStackElemThinPtr l m p e el pb) :=
    fun l m p e el pb => ⟨deriveStackElemThinPtr_withCalleeCtx c ac ti l m p e el pb,
      deriveStackElemThinPtr_rvCS l m p e el pb⟩
  dsimp only [evalCastPtrToPtr, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl
      | exact hDerive ..)
    | split)

theorem evalCastPtrToPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalCastPtrToPtr locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalCastPtrToPtr locals op targetTy mem localDecls layouts) :=
  (evalCastPtrToPtr_rvCtxCS c ac ti locals op targetTy mem localDecls layouts).1

theorem evalCastPtrToPtr_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalCastPtrToPtr locals op targetTy mem localDecls layouts) :=
  (evalCastPtrToPtr_rvCtxCS [] none [] locals op targetTy mem localDecls layouts).2

private theorem evalPointerExposeProvenance_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalPointerExposeProvenance locals op targetTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalPointerExposeProvenance locals op targetTy mem localDecls layouts) := by
  dsimp only [evalPointerExposeProvenance, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalPointerExposeProvenance_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPointerExposeProvenance locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalPointerExposeProvenance locals op targetTy mem localDecls layouts) :=
  (evalPointerExposeProvenance_rvCtxCS c ac ti locals op targetTy mem localDecls layouts).1

theorem evalPointerExposeProvenance_rvCS (locals : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalPointerExposeProvenance locals op targetTy mem localDecls layouts) :=
  (evalPointerExposeProvenance_rvCtxCS [] none [] locals op targetTy mem localDecls layouts).2

private theorem evalPointerWithExposedProvenance_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalPointerWithExposedProvenance locals op targetTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalPointerWithExposedProvenance locals op targetTy mem localDecls layouts) := by
  dsimp only [evalPointerWithExposedProvenance, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalPointerWithExposedProvenance_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPointerWithExposedProvenance locals op targetTy
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalPointerWithExposedProvenance locals op targetTy mem localDecls layouts) :=
  (evalPointerWithExposedProvenance_rvCtxCS c ac ti locals op targetTy mem localDecls layouts).1

theorem evalPointerWithExposedProvenance_rvCS (locals : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalPointerWithExposedProvenance locals op targetTy mem localDecls layouts) :=
  (evalPointerWithExposedProvenance_rvCtxCS [] none [] locals op targetTy mem localDecls layouts).2

private theorem evalAggregateRawPtr_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (pointeeTy : Ty) (ops : List Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalAggregateRawPtr locals pointeeTy ops (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalAggregateRawPtr locals pointeeTy ops mem localDecls layouts) := by
  unfold evalAggregateRawPtr
  dsimp only [Memory.withCalleeCtx]
  cases evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => exact rvCtxCS_ub
  | unsupported => exact rvCtxCS_unsupported
  | ok vals locals' =>
    repeat' (first
      | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
      | split)

theorem evalAggregateRawPtr_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (pointeeTy : Ty) (ops : List Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalAggregateRawPtr locals pointeeTy ops
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalAggregateRawPtr locals pointeeTy ops mem localDecls layouts) :=
  (evalAggregateRawPtr_rvCtxCS c ac ti locals pointeeTy ops mem localDecls layouts).1

theorem evalAggregateRawPtr_rvCS (locals : List LocalSlot) (pointeeTy : Ty)
    (ops : List Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalAggregateRawPtr locals pointeeTy ops mem localDecls layouts) :=
  (evalAggregateRawPtr_rvCtxCS [] none [] locals pointeeTy ops mem localDecls layouts).2

private theorem evalAggregateAdt_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (defPath : DefPath) (variantIdx : VariantIdx)
    (activeField : Option FieldIdx) (ops : List Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalAggregateAdt locals defPath variantIdx activeField ops (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalAggregateAdt locals defPath variantIdx activeField ops mem localDecls layouts) := by
  unfold evalAggregateAdt
  dsimp only [Memory.withCalleeCtx]
  cases evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => exact rvCtxCS_ub
  | unsupported => exact rvCtxCS_unsupported
  | ok vals locals' =>
    dsimp only
    repeat' (first
      | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
      | split)

theorem evalAggregateAdt_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (defPath : DefPath) (variantIdx : VariantIdx)
    (activeField : Option FieldIdx) (ops : List Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalAggregateAdt locals defPath variantIdx activeField ops
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalAggregateAdt locals defPath variantIdx activeField ops mem localDecls layouts) :=
  (evalAggregateAdt_rvCtxCS c ac ti locals defPath variantIdx activeField ops mem localDecls layouts).1

theorem evalAggregateAdt_rvCS (locals : List LocalSlot) (defPath : DefPath)
    (variantIdx : VariantIdx) (activeField : Option FieldIdx) (ops : List Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalAggregateAdt locals defPath variantIdx activeField ops mem localDecls layouts) :=
  (evalAggregateAdt_rvCtxCS [] none [] locals defPath variantIdx activeField ops mem localDecls
    layouts).2

private theorem evalFloatCastRvalue_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (kind : CastKind) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalFloatCastRvalue locals kind op targetTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalFloatCastRvalue locals kind op targetTy mem localDecls layouts) := by
  unfold evalFloatCastRvalue
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalFloatCastRvalue_rvCS (locals : List LocalSlot) (kind : CastKind) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalFloatCastRvalue locals kind op targetTy mem localDecls layouts) :=
  (evalFloatCastRvalue_rvCtxCS [] none [] locals kind op targetTy mem localDecls layouts).2

private theorem evalUnaryPtrMetadata_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalUnaryPtrMetadata locals op (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalUnaryPtrMetadata locals op mem localDecls layouts) := by
  unfold evalUnaryPtrMetadata
  dsimp only [Memory.withCalleeCtx]
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => exact rvCtxCS_ub
  | unsupported => exact rvCtxCS_unsupported
  | ok v locals' =>
    repeat' (first
      | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
      | split)

theorem evalUnaryPtrMetadata_rvCS (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalUnaryPtrMetadata locals op mem localDecls layouts) :=
  (evalUnaryPtrMetadata_rvCtxCS [] none [] locals op mem localDecls layouts).2

private theorem evalWidePtrRelBinOp_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (op : BinOp) (lhsThin lhsMeta rhsThin rhsMeta : Value)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (ptrBytes : Nat) :
    RvCtxCS c ac ti mem.callStack
      (evalWidePtrRelBinOp op lhsThin lhsMeta rhsThin rhsMeta locals₂ (Memory.withCalleeCtx c ac ti mem) localDecls layouts ptrBytes)
      (evalWidePtrRelBinOp op lhsThin lhsMeta rhsThin rhsMeta locals₂ mem localDecls layouts ptrBytes) := by
  have hBin : ∀ o a b l m sg,
      RvCtxCS c ac ti m.callStack
        (evalScalarBinOp o a b l { m with callees := c, activeCallee := ac, traitImpls := ti } sg)
        (evalScalarBinOp o a b l m sg) :=
    fun o a b l m sg => ⟨evalScalarBinOp_withCalleeCtx c ac ti o a b l m sg,
      evalScalarBinOp_rvCS o a b l m sg⟩
  unfold evalWidePtrRelBinOp
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl
      | exact hBin ..)
    | split)

theorem evalWidePtrRelBinOp_rvCS (op : BinOp) (lhsThin lhsMeta rhsThin rhsMeta : Value)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (ptrBytes : Nat) :
    RvCS mem.callStack
      (evalWidePtrRelBinOp op lhsThin lhsMeta rhsThin rhsMeta locals₂ mem localDecls layouts
        ptrBytes) :=
  (evalWidePtrRelBinOp_rvCtxCS [] none [] op lhsThin lhsMeta rhsThin rhsMeta locals₂ mem localDecls
    layouts ptrBytes).2

private theorem evalWidePtrAggregateRelBinOp_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (op : BinOp) (lhsOp : Operand) (lhsVar : Nat) (lhsFields : List Value)
    (rhsVar : Nat) (rhsFields : List Value) (locals₂ : List LocalSlot)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalWidePtrAggregateRelBinOp op lhsOp lhsVar lhsFields rhsVar rhsFields locals₂
        (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalWidePtrAggregateRelBinOp op lhsOp lhsVar lhsFields rhsVar rhsFields locals₂
        mem localDecls layouts) := by
  have hWide : ∀ o a b d e l m ld ly pb,
      RvCtxCS c ac ti m.callStack
        (evalWidePtrRelBinOp o a b d e l { m with callees := c, activeCallee := ac, traitImpls := ti } ld ly pb)
        (evalWidePtrRelBinOp o a b d e l m ld ly pb) :=
    fun o a b d e l m ld ly pb => ⟨(evalWidePtrRelBinOp_rvCtxCS c ac ti o a b d e l m ld ly pb).1,
      evalWidePtrRelBinOp_rvCS o a b d e l m ld ly pb⟩
  have hBin : ∀ o a b l m sg,
      RvCtxCS c ac ti m.callStack
        (evalScalarBinOp o a b l { m with callees := c, activeCallee := ac, traitImpls := ti } sg)
        (evalScalarBinOp o a b l m sg) :=
    fun o a b l m sg => ⟨evalScalarBinOp_withCalleeCtx c ac ti o a b l m sg,
      evalScalarBinOp_rvCS o a b l m sg⟩
  unfold evalWidePtrAggregateRelBinOp
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl
      | exact hWide .. | exact hBin ..)
    | split)

theorem evalWidePtrAggregateRelBinOp_rvCS (op : BinOp) (lhsOp : Operand) (lhsVar : Nat)
    (lhsFields : List Value) (rhsVar : Nat) (rhsFields : List Value) (locals₂ : List LocalSlot)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack
      (evalWidePtrAggregateRelBinOp op lhsOp lhsVar lhsFields rhsVar rhsFields locals₂ mem
        localDecls layouts) :=
  (evalWidePtrAggregateRelBinOp_rvCtxCS [] none [] op lhsOp lhsVar lhsFields rhsVar rhsFields
    locals₂ mem localDecls layouts).2

private theorem evalNullaryOp_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : NullOp) (argTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalNullaryOp locals op argTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalNullaryOp locals op argTy mem localDecls layouts) := by
  unfold evalNullaryOp
  dsimp only [Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
    | split)

theorem evalNullaryOp_rvCS (locals : List LocalSlot) (op : NullOp) (argTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalNullaryOp locals op argTy mem localDecls layouts) :=
  (evalNullaryOp_rvCtxCS [] none [] locals op argTy mem localDecls layouts).2

private theorem evalUseRvalue_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalUseRvalue locals op (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalUseRvalue locals op mem localDecls layouts) := by
  cases op
  all_goals
    dsimp only [evalUseRvalue, Memory.withCalleeCtx]
    repeat' (first
      | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
      | split)

theorem evalUseRvalue_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUseRvalue locals op (Memory.withCalleeCtx c ac ti mem)
        localDecls layouts =
      RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti)
        (evalUseRvalue locals op mem localDecls layouts) :=
  (evalUseRvalue_rvCtxCS c ac ti locals op mem localDecls layouts).1

theorem evalUseRvalue_rvCS (locals : List LocalSlot) (op : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalUseRvalue locals op mem localDecls layouts) :=
  (evalUseRvalue_rvCtxCS [] none [] locals op mem localDecls layouts).2

private theorem evalShallowInitBox_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (contentTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalShallowInitBox locals op contentTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalShallowInitBox locals op contentTy mem localDecls layouts) := by
  dsimp only [evalShallowInitBox]
  have hUse : RvCtxCS c ac ti mem.callStack _ _ :=
    ⟨evalUseRvalue_withCalleeCtx c ac ti locals op mem localDecls layouts,
     evalUseRvalue_rvCS locals op mem localDecls layouts⟩
  rw [hUse.1]
  cases hEq : evalUseRvalue locals op mem localDecls layouts with
  | ub => exact rvCtxCS_ub
  | unsupported => exact rvCtxCS_unsupported
  | ok v locals' mem' =>
    have hCS : mem'.callStack = mem.callStack := hUse.2.callStack_eq hEq
    rw [show RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti) (.ok v locals' mem') =
      .ok v locals' (Memory.withCalleeCtx c ac ti mem') from rfl]
    dsimp +zetaDelta only
    repeat' (first
      | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl hCS)
      | split
      | dsimp +zetaDelta only)

theorem evalShallowInitBox_rvCS (locals : List LocalSlot) (op : Operand) (contentTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalShallowInitBox locals op contentTy mem localDecls layouts) :=
  (evalShallowInitBox_rvCtxCS [] none [] locals op contentTy mem localDecls layouts).2

private theorem evalWrapUnsafeBinder_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCtxCS c ac ti mem.callStack
      (evalWrapUnsafeBinder locals op targetTy (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalWrapUnsafeBinder locals op targetTy mem localDecls layouts) := by
  dsimp only [evalWrapUnsafeBinder]
  have hUse : RvCtxCS c ac ti mem.callStack _ _ :=
    ⟨evalUseRvalue_withCalleeCtx c ac ti locals op mem localDecls layouts,
     evalUseRvalue_rvCS locals op mem localDecls layouts⟩
  rw [hUse.1]
  cases hEq : evalUseRvalue locals op mem localDecls layouts with
  | ub => exact rvCtxCS_ub
  | unsupported => exact rvCtxCS_unsupported
  | ok v locals' mem' =>
    have hCS : mem'.callStack = mem.callStack := hUse.2.callStack_eq hEq
    rw [show RvalueEvalResult.mapMem (Memory.withCalleeCtx c ac ti) (.ok v locals' mem') =
      .ok v locals' (Memory.withCalleeCtx c ac ti mem') from rfl]
    dsimp +zetaDelta only
    repeat' (first
      | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl hCS)
      | split
      | dsimp +zetaDelta only)

theorem evalWrapUnsafeBinder_rvCS (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalWrapUnsafeBinder locals op targetTy mem localDecls layouts) :=
  (evalWrapUnsafeBinder_rvCtxCS [] none [] locals op targetTy mem localDecls layouts).2

/-- `evalRvalue` never changes `Memory.callStack`. -/

private theorem evalRvalue_rvCtxCS
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_free : Rvalue.calleeQueryFree rv = true) :
    RvCtxCS c ac ti mem.callStack
      (evalRvalue locals rv (Memory.withCalleeCtx c ac ti mem) localDecls layouts)
      (evalRvalue locals rv mem localDecls layouts) := by
  cases rv with
  | use op =>
    exact ⟨evalUseRvalue_withCalleeCtx c ac ti locals op mem localDecls layouts,
      evalUseRvalue_rvCS locals op mem localDecls layouts⟩
  | «repeat» op count =>
    cases op
    all_goals
      dsimp only [evalRvalue, Memory.withCalleeCtx]
      repeat' (first
        | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
        | split)
  | ref bk place =>
    have hRef : ∀ l b p rp pm m ld ly,
        RvCtxCS c ac ti m.callStack
          (evalRvalueRefDeref l b p rp pm { m with callees := c, activeCallee := ac, traitImpls := ti } ld ly)
          (evalRvalueRefDeref l b p rp pm m ld ly) :=
      fun l b p rp pm m ld ly => ⟨evalRvalueRefDeref_withCalleeCtx c ac ti l b p rp pm m ld ly,
        evalRvalueRefDeref_rvCS l b p rp pm m ld ly⟩
    dsimp only [evalRvalue, Memory.withCalleeCtx]
    repeat' (first
      | with_reducible (first
        | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl
        | exact hRef ..)
      | split)
  | threadLocalRef _ => exact rvCtxCS_unsupported
  | rawPtr mutab place =>
    exact ⟨evalRvalueRawPtr_withCalleeCtx c ac ti locals mutab place mem localDecls layouts,
      evalRvalueRawPtr_rvCS locals mutab place mem localDecls layouts⟩
  | len place =>
    exact ⟨evalPlaceLen_withCalleeCtx c ac ti locals place mem localDecls layouts,
      evalPlaceLen_rvCS locals place mem localDecls layouts⟩
  | cast ck op targetTy =>
    cases ck with
    | pointerCoercion ckStr =>
      exact ⟨evalReifyFnPointer_withCalleeCtx c ac ti locals op targetTy mem localDecls layouts ckStr
        (Rvalue.calleeQueryFree_pointerCoercion h_free),
        evalReifyFnPointer_rvCS locals op targetTy mem localDecls layouts ckStr⟩
    | fnPtrToPtr =>
      exact ⟨evalFnPtrToPtr_withCalleeCtx c ac ti locals op targetTy mem localDecls layouts,
        evalFnPtrToPtr_rvCS locals op targetTy mem localDecls layouts⟩
    | ptrToPtr =>
      exact ⟨evalCastPtrToPtr_withCalleeCtx c ac ti locals op targetTy mem localDecls layouts,
        evalCastPtrToPtr_rvCS locals op targetTy mem localDecls layouts⟩
    | pointerExposeProvenance =>
      exact ⟨evalPointerExposeProvenance_withCalleeCtx c ac ti locals op targetTy mem localDecls layouts,
        evalPointerExposeProvenance_rvCS locals op targetTy mem localDecls layouts⟩
    | pointerWithExposedProvenance =>
      exact ⟨evalPointerWithExposedProvenance_withCalleeCtx c ac ti locals op targetTy mem localDecls layouts,
        evalPointerWithExposedProvenance_rvCS locals op targetTy mem localDecls layouts⟩
    | transmute | subtype =>
      exact ⟨evalByteCast_withCalleeCtx c ac ti locals op targetTy mem localDecls layouts,
        evalByteCast_rvCS locals op targetTy mem localDecls layouts⟩
    | floatToInt | intToFloat | floatToFloat =>
      exact ⟨(evalFloatCastRvalue_rvCtxCS c ac ti locals _ op targetTy mem localDecls layouts).1,
        evalFloatCastRvalue_rvCS locals _ op targetTy mem localDecls layouts⟩
    | intToInt =>
      dsimp only [evalRvalue, Memory.withCalleeCtx]
      repeat' (first
        | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
        | split)
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalue, Memory.withCalleeCtx]
    cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | ub => exact rvCtxCS_ub
    | unsupported => exact rvCtxCS_unsupported
    | ok lhsVal locals₁ =>
      dsimp only
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => exact rvCtxCS_ub
      | unsupported => exact rvCtxCS_unsupported
      | ok rhsVal locals₂ =>
        dsimp only
        cases lhsVal with
        | scalar lhsSc =>
          cases rhsVal with
          | scalar rhsSc =>
            cases op with
            | offset =>
              exact ⟨evalScalarPtrOffsetBinOp_withCalleeCtx c ac ti
                locals₂ mem localDecls layouts lhsOp lhsSc rhsSc,
                evalScalarPtrOffsetBinOp_rvCS locals₂ mem localDecls layouts lhsOp lhsSc rhsSc⟩
            | _ =>
              exact ⟨evalScalarBinOp_withCalleeCtx c ac ti _ lhsSc rhsSc locals₂ mem _,
                evalScalarBinOp_rvCS _ lhsSc rhsSc locals₂ mem _⟩
          | ptr ptrVal sz =>
            cases isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
            | false => exact rvCtxCS_unsupported
            | true =>
              dsimp only
              cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
              | none => exact rvCtxCS_unsupported
              | some rhsAddrSc =>
                exact ⟨evalScalarBinOp_withCalleeCtx c ac ti op lhsSc rhsAddrSc locals₂ mem false,
                  evalScalarBinOp_rvCS op lhsSc rhsAddrSc locals₂ mem false⟩
          | _ => exact rvCtxCS_unsupported
        | ptr ptrVal sz =>
          cases rhsVal with
          | scalar rhsSc =>
            cases op with
            | offset =>
              exact ⟨evalPtrOffsetBinOp_withCalleeCtx c ac ti
                locals₂ mem localDecls layouts lhsOp ptrVal sz rhsSc,
                evalPtrOffsetBinOp_rvCS locals₂ mem localDecls layouts lhsOp ptrVal sz rhsSc⟩
            | _ =>
              cases isPtrRelationalBinOp _ localDecls layouts lhsOp rhsOp with
              | false => exact rvCtxCS_unsupported
              | true =>
                dsimp only
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
                | none => exact rvCtxCS_unsupported
                | some lhsAddrSc =>
                  exact ⟨evalScalarBinOp_withCalleeCtx c ac ti _ lhsAddrSc rhsSc locals₂ mem false,
                    evalScalarBinOp_rvCS _ lhsAddrSc rhsSc locals₂ mem false⟩
          | ptr rhsPtr rhsSz =>
            cases isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
            | false => exact rvCtxCS_unsupported
            | true =>
              dsimp only
              cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
              | none =>
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) rhsPtr rhsSz mem.callStack with
                | none => exact rvCtxCS_unsupported
                | some _ => exact rvCtxCS_unsupported
              | some lhsAddrSc =>
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) rhsPtr rhsSz mem.callStack with
                | none => exact rvCtxCS_unsupported
                | some rhsAddrSc =>
                  exact ⟨evalScalarBinOp_withCalleeCtx c ac ti op lhsAddrSc rhsAddrSc locals₂ mem false,
                    evalScalarBinOp_rvCS op lhsAddrSc rhsAddrSc locals₂ mem false⟩
          | _ => exact rvCtxCS_unsupported
        | aggregate lhsVar lhsFields =>
          cases rhsVal with
          | aggregate rhsVar rhsFields =>
            exact ⟨(evalWidePtrAggregateRelBinOp_rvCtxCS c ac ti op lhsOp lhsVar lhsFields
              rhsVar rhsFields locals₂ mem localDecls layouts).1,
              evalWidePtrAggregateRelBinOp_rvCS op lhsOp lhsVar lhsFields
              rhsVar rhsFields locals₂ mem localDecls layouts⟩
          | _ => exact rvCtxCS_unsupported
        | _ => exact rvCtxCS_unsupported
  | nullaryOp op argTy =>
    exact ⟨(evalNullaryOp_rvCtxCS c ac ti locals op argTy mem localDecls layouts).1,
      evalNullaryOp_rvCS locals op argTy mem localDecls layouts⟩
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalue, Memory.withCalleeCtx]
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => exact rvCtxCS_ub
      | unsupported => exact rvCtxCS_unsupported
      | ok v locals' =>
        cases v with
        | scalar sc =>
          exact ⟨evalUnaryNot_withCalleeCtx c ac ti sc _ locals' mem,
            evalUnaryNot_rvCS sc _ locals' mem⟩
        | _ => exact rvCtxCS_unsupported
    | neg =>
      dsimp only [evalRvalue, Memory.withCalleeCtx]
      repeat' (first
        | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
        | split)
    | ptrMetadata =>
      exact ⟨(evalUnaryPtrMetadata_rvCtxCS c ac ti locals op mem localDecls layouts).1,
        evalUnaryPtrMetadata_rvCS locals op mem localDecls layouts⟩
  | discriminant place =>
    have hDisc : ∀ v l m p ld ly,
        RvCtxCS c ac ti m.callStack
          (evalPlaceDiscriminant v l { m with callees := c, activeCallee := ac, traitImpls := ti } p ld ly)
          (evalPlaceDiscriminant v l m p ld ly) :=
      fun v l m p ld ly => ⟨evalPlaceDiscriminant_withCalleeCtx c ac ti v l m p ld ly,
        evalPlaceDiscriminant_rvCS v l m p ld ly⟩
    dsimp only [evalRvalue, Memory.withCalleeCtx]
    repeat' (first
      | with_reducible (first
        | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl
        | exact hDisc ..)
      | split)
  | aggregate kind ops =>
    cases kind with
    | rawPtr pointeeTy _ =>
      exact ⟨evalAggregateRawPtr_withCalleeCtx c ac ti locals pointeeTy ops mem localDecls layouts,
        evalAggregateRawPtr_rvCS locals pointeeTy ops mem localDecls layouts⟩
    | adt defPath variantIdx activeField =>
      exact ⟨evalAggregateAdt_withCalleeCtx c ac ti locals defPath variantIdx activeField ops mem localDecls layouts,
        evalAggregateAdt_rvCS locals defPath variantIdx activeField ops mem localDecls layouts⟩
    | _ =>
      dsimp only [evalRvalue, Memory.withCalleeCtx]
      repeat' (first
        | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
        | split)
  | shallowInitBox op contentTy =>
    exact ⟨(evalShallowInitBox_rvCtxCS c ac ti locals op contentTy mem localDecls layouts).1,
      evalShallowInitBox_rvCS locals op contentTy mem localDecls layouts⟩
  | copyForDeref place =>
    dsimp only [evalRvalue, Memory.withCalleeCtx]
    cases evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack <;>
      repeat' (first
        | with_reducible (first | exact rvCtxCS_ub | exact rvCtxCS_unsupported | exact rvCtxCS_ok rfl rfl)
        | split)
  | wrapUnsafeBinder op targetTy =>
    exact ⟨(evalWrapUnsafeBinder_rvCtxCS c ac ti locals op targetTy mem localDecls layouts).1,
      evalWrapUnsafeBinder_rvCS locals op targetTy mem localDecls layouts⟩

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
        (evalRvalue locals rv mem localDecls layouts) :=
  (evalRvalue_rvCtxCS c ac ti locals rv mem localDecls layouts h_free).1

theorem evalRvalue_rvCS (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvCS mem.callStack (evalRvalue locals rv mem localDecls layouts) := by
  cases rv with
  | cast ck op targetTy =>
    cases ck with
    | pointerCoercion ckStr =>
      exact evalReifyFnPointer_rvCS locals op targetTy mem localDecls layouts ckStr
    | _ =>
      exact (evalRvalue_rvCtxCS [] none [] locals (.cast _ op targetTy) mem localDecls layouts rfl).2
  | _ =>
    exact (evalRvalue_rvCtxCS [] none [] locals _ mem localDecls layouts rfl).2

theorem evalRvalue_callStack {locals locals' : List LocalSlot} {rv : Rvalue} {mem mem' : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {v : Value}
    (h : evalRvalue locals rv mem localDecls layouts = .ok v locals' mem') :
    mem'.callStack = mem.callStack :=
  (evalRvalue_rvCS locals rv mem localDecls layouts).callStack_eq h

private theorem evalCopySingleDirect_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (locals₃ : List LocalSlot) :
    StepCtxCB c ac ti s.memory.callStack
      (evalCopySingleDirect
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃)
      (evalCopySingleDirect
        s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃) := by
  unfold evalCopySingleDirect
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact stepCtxCB_fail | exact stepCtxCB_unsupported
      | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_mk rfl (CallerBodiesEq.refl _))
    | split)
  all_goals try dsimp (config := { zeta := true })
  repeat' (first
    | with_reducible (first
      | exact stepCtxCB_fail | exact stepCtxCB_unsupported
      | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_mk rfl (CallerBodiesEq.refl _))
    | split)

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
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃) :=
  (evalCopySingleDirect_stepCtxCB c ac ti s src dst localDecls layouts srcPtr dstPtr srcEntry
    dstEntry locals₃).1

theorem evalCopySingleDirect_callerBodies (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (locals₃ : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        locals₃) :=
  (evalCopySingleDirect_stepCtxCB [] none [] s src dst localDecls layouts srcPtr dstPtr srcEntry
    dstEntry locals₃).2

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
          commitCopyDstPlaceWrite s dstPlace dstEntry.targetLocal dstPtr.tag locals₃ splicedVal localDecls layouts
        | _, _ =>
          match dstTargetTyOpt with
          | .some dstPt =>
            match rigidTyByteSize layouts dstPt with
            | .some dstBytes =>
              match Nat.beq (length bs) dstBytes with
              | true =>
                match decodeValueFromBytes defaultCodecFuel layouts dstPt bs with
                | .some decodedVal =>
                  commitCopyDstPlaceWrite s dstPlace dstEntry.targetLocal dstPtr.tag locals₃ decodedVal localDecls layouts
                | .none =>
                  match spliceBytesToDstArray with
                  | .some splicedVal =>
                    commitCopyDstPlaceWrite s dstPlace dstEntry.targetLocal dstPtr.tag locals₃ splicedVal localDecls layouts
                  | .none => MirStepNode.fail .ub
              | false =>
                match spliceBytesToDstArray with
                | .some splicedVal =>
                  commitCopyDstPlaceWrite s dstPlace dstEntry.targetLocal dstPtr.tag locals₃ splicedVal localDecls layouts
                | .none => MirStepNode.unsupported
            | .none =>
              match spliceBytesToDstArray with
              | .some splicedVal =>
                commitCopyDstPlaceWrite s dstPlace dstEntry.targetLocal dstPtr.tag locals₃ splicedVal localDecls layouts
              | .none => MirStepNode.unsupported
          | .none =>
            match spliceBytesToDstArray with
            | .some splicedVal =>
              commitCopyDstPlaceWrite s dstPlace dstEntry.targetLocal dstPtr.tag locals₃ splicedVal localDecls layouts
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
              commitCopyDstPlaceWrite s dstPlace dstEntry.targetLocal dstPtr.tag locals₃
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
pieces are factored through `ccCopyViaBytesBody` / `commitCopyDstPlaceWrite`), definitionally. -/
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

private theorem commitCopyDstPlaceWrite_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (dstPlace : Place) (dstTargetLocal : LocalIdx) (dstTag : Nat)
    (locals₃ : List LocalSlot) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    StepCtxCB c ac ti s.memory.callStack
      (commitCopyDstPlaceWrite (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        dstPlace dstTargetLocal dstTag locals₃ newVal localDecls layouts)
      (commitCopyDstPlaceWrite s dstPlace dstTargetLocal dstTag locals₃ newVal localDecls layouts) := by
  unfold commitCopyDstPlaceWrite
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact stepCtxCB_fail | exact stepCtxCB_unsupported
      | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_mk rfl (CallerBodiesEq.refl _))
    | split)

theorem commitCopyDstPlaceWrite_callerBodies (s : MachineState) (dstPlace : Place)
    (dstTargetLocal : LocalIdx) (dstTag : Nat) (locals₃ : List LocalSlot) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (commitCopyDstPlaceWrite s dstPlace dstTargetLocal dstTag locals₃ newVal localDecls
        layouts) :=
  (commitCopyDstPlaceWrite_stepCtxCB [] none [] s dstPlace dstTargetLocal dstTag locals₃ newVal
    localDecls layouts).2

private theorem copyViaBytesBody_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) (dstPlace : Place) (dstLocalPlaceTy : Option Ty)
    (dstIsAdt : Bool) (srcSubVal dstSubVal : Value) :
    StepCtxCB c ac ti s.memory.callStack
      (ccCopyViaBytesBody (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits
        locals₃ dstPlace dstLocalPlaceTy dstIsAdt srcSubVal dstSubVal)
      (ccCopyViaBytesBody s dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        countBits locals₃ dstPlace dstLocalPlaceTy dstIsAdt srcSubVal dstSubVal) := by
  unfold ccCopyViaBytesBody
  dsimp only
  repeat' (first
    | with_reducible (first
      | exact stepCtxCB_fail | exact stepCtxCB_unsupported
      | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_mk rfl (CallerBodiesEq.refl _)
      | exact commitCopyDstPlaceWrite_stepCtxCB ..)
    | split)

private theorem evalCopyUnionBytes_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo)
    (n : Nat) (locals₃ : List LocalSlot) :
    StepCtxCB c ac ti s.memory.callStack
      (evalCopyUnionBytes
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃)
      (evalCopyUnionBytes
        s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃) := by
  unfold evalCopyUnionBytes
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact stepCtxCB_fail | exact stepCtxCB_unsupported
      | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_mk rfl (CallerBodiesEq.refl _))
    | exact commitCopyDstPlaceWrite_stepCtxCB ..
    | split)

theorem evalCopyUnionBytes_callerBodies (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo)
    (n : Nat) (locals₃ : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalCopyUnionBytes s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃) :=
  (evalCopyUnionBytes_stepCtxCB [] none [] s src dst localDecls layouts srcPtr dstPtr srcEntry
    dstEntry srcUnionOpt dstUnionOpt n locals₃).2

private theorem evalCopyNonOverlappingPermOk_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    StepCtxCB c ac ti s.memory.callStack
      (ccEvalCopyNonOverlappingPermOk
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃)
      (ccEvalCopyNonOverlappingPermOk
        s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold ccEvalCopyNonOverlappingPermOk
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact stepCtxCB_fail | exact stepCtxCB_unsupported
      | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_mk rfl (CallerBodiesEq.refl _))
    | exact ⟨(evalCopyUnionBytes_stepCtxCB ..).1, evalCopyUnionBytes_callerBodies ..⟩
    | exact ⟨evalCopySingleDirect_withCalleeCtx .., evalCopySingleDirect_callerBodies ..⟩
    | exact copyViaBytesBody_stepCtxCB ..
    | exact ⟨(commitCopyDstPlaceWrite_stepCtxCB ..).1, commitCopyDstPlaceWrite_callerBodies ..⟩
    | split)

private theorem evalCopyNonOverlappingPermOk_trusted_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    StepCtxCB c ac ti s.memory.callStack
      (Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃)
      (Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk
        s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  rw [evalCopyNonOverlappingPermOk_eq_cc, evalCopyNonOverlappingPermOk_eq_cc]
  exact evalCopyNonOverlappingPermOk_stepCtxCB c ac ti
    s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃

/-- The frame-qualified single-element copy into or out of a suspended caller frame
(`evalForeignFrameCopySingleDirect`) reads and writes `Memory.callStack` /
`Memory.callerLocals` only, so it commutes with `Memory.withCalleeCtx` and preserves caller bodies. -/
theorem evalCopyNonOverlappingPermOk_callerBodies (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (countBits : Nat) (locals₃ : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk s src dst localDecls
        layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) :=
  (evalCopyNonOverlappingPermOk_trusted_stepCtxCB [] none [] s src dst localDecls layouts srcPtr
    dstPtr srcEntry dstEntry countBits locals₃).2

private theorem evalForeignFrameCopySingleDirect_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    StepCtxCB c ac ti s.memory.callStack
      (evalForeignFrameCopySingleDirect
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃)
      (evalForeignFrameCopySingleDirect
        s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold evalForeignFrameCopySingleDirect
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact stepCtxCB_fail | exact stepCtxCB_unsupported
      | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_mk rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_advance rfl rfl (cb_of_writeFrameLocalSlot (by assumption) (by rfl))
      | exact stepCtxCB_mk rfl (cb_of_writeFrameLocalSlot (by assumption) (by rfl)))
    | split)

theorem evalForeignFrameCopySingleDirect_callerBodies (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (countBits : Nat) (locals₃ : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalForeignFrameCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry
        dstEntry countBits locals₃) :=
  (evalForeignFrameCopySingleDirect_stepCtxCB [] none [] s src dst localDecls layouts srcPtr
    dstPtr srcEntry dstEntry countBits locals₃).2

private theorem evalCopyNonOverlappingWithCount_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    StepCtxCB c ac ti s.memory.callStack
      (evalCopyNonOverlappingWithCount
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst localDecls layouts srcVal dstVal countBits locals₃)
      (evalCopyNonOverlappingWithCount
        s src dst localDecls layouts srcVal dstVal countBits locals₃) := by
  unfold evalCopyNonOverlappingWithCount
  cases Nat.beq countBits 0 with
  | true => exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
  | false =>
    cases srcVal with
    | ptr srcPtr _ =>
      cases dstVal with
      | ptr dstPtr _ =>
        dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
        cases lookupBorrow s.memory.borrows srcPtr.tag with
        | none => exact stepCtxCB_fail
        | some srcEntry =>
          cases lookupBorrow s.memory.borrows dstPtr.tag with
          | none => exact stepCtxCB_fail
          | some dstEntry =>
            dsimp only
            cases srcEntry.perm <;> cases dstEntry.perm <;>
              cases copyEntriesTargetActiveFrame s.memory.callStack srcEntry dstEntry <;>
              first
              | exact stepCtxCB_fail
              | exact stepCtxCB_unsupported
              | exact ⟨(evalCopyNonOverlappingPermOk_trusted_stepCtxCB c ac ti
                  s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃).1,
                  evalCopyNonOverlappingPermOk_callerBodies s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃⟩
              | exact ⟨(evalForeignFrameCopySingleDirect_stepCtxCB c ac ti
                  s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃).1,
                  evalForeignFrameCopySingleDirect_callerBodies s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃⟩
      | _ => exact stepCtxCB_fail
    | _ => exact stepCtxCB_fail

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
          s src dst localDecls layouts srcVal dstVal countBits locals₃) :=
  (evalCopyNonOverlappingWithCount_stepCtxCB c ac ti s src dst localDecls layouts srcVal dstVal
    countBits locals₃).1

theorem evalCopyNonOverlappingWithCount_callerBodies (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits
        locals₃) :=
  (evalCopyNonOverlappingWithCount_stepCtxCB [] none [] s src dst localDecls layouts srcVal dstVal
    countBits locals₃).2

private theorem evalCopyNonOverlapping_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst count : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    StepCtxCB c ac ti s.memory.callStack
      (evalCopyNonOverlapping
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst count localDecls layouts)
      (evalCopyNonOverlapping s src dst count localDecls layouts) := by
  unfold evalCopyNonOverlapping
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  cases evalOperand s.frame.locals src s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
  | ub => exact stepCtxCB_fail
  | unsupported => exact stepCtxCB_unsupported
  | ok srcVal locals₁ =>
    dsimp only
    cases evalOperand locals₁ dst s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
    | ub => exact stepCtxCB_fail
    | unsupported => exact stepCtxCB_unsupported
    | ok dstVal locals₂ =>
      dsimp only
      cases evalOperand locals₂ count s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
      | ub => exact stepCtxCB_fail
      | unsupported => exact stepCtxCB_unsupported
      | ok countVal locals₃ =>
        cases countVal with
        | scalar countSc =>
          exact ⟨evalCopyNonOverlappingWithCount_withCalleeCtx
            c ac ti s src dst localDecls layouts srcVal dstVal countSc.bits locals₃,
            evalCopyNonOverlappingWithCount_callerBodies
            s src dst localDecls layouts srcVal dstVal countSc.bits locals₃⟩
        | _ => exact stepCtxCB_fail

theorem evalCopyNonOverlapping_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (src dst count : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalCopyNonOverlapping
        (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        src dst count localDecls layouts =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalCopyNonOverlapping s src dst count localDecls layouts) :=
  (evalCopyNonOverlapping_stepCtxCB c ac ti s src dst count localDecls layouts).1

theorem evalCopyNonOverlapping_callerBodies (s : MachineState) (src dst count : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalCopyNonOverlapping s src dst count localDecls layouts) :=
  (evalCopyNonOverlapping_stepCtxCB [] none [] s src dst count localDecls layouts).2

/-- **Statement steps keep every saved caller body.** Every `.running` successor of
`evalStmt s stmt` has a call stack whose saved caller bodies are those of `s` (statements
only rewrite saved frames' locals, through `commitForeignFrameLocals` /
`writeFrameLocalSlot`). -/

private theorem evalSetDiscriminantLocal_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (loc : Local) (variantIdx : Nat) (fields : List Value) :
    StepCtxCB c ac ti s.memory.callStack
      (evalSetDiscriminantLocal (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        loc variantIdx fields)
      (evalSetDiscriminantLocal s loc variantIdx fields) := by
  unfold evalSetDiscriminantLocal
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact stepCtxCB_fail | exact stepCtxCB_unsupported
      | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_mk rfl (CallerBodiesEq.refl _))
    | split)

/-- `evalSetDiscriminantLocal` reads only the active frame, borrows, and protectors. -/
theorem evalSetDiscriminantLocal_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (loc : Local) (variantIdx : Nat) (fields : List Value) :
    evalSetDiscriminantLocal (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        loc variantIdx fields =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalSetDiscriminantLocal s loc variantIdx fields) :=
  (evalSetDiscriminantLocal_stepCtxCB c ac ti s loc variantIdx fields).1

theorem evalSetDiscriminantLocal_callerBodies (s : MachineState) (loc : Local)
    (variantIdx : Nat) (fields : List Value) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalSetDiscriminantLocal s loc variantIdx fields) :=
  (evalSetDiscriminantLocal_stepCtxCB [] none [] s loc variantIdx fields).2

private theorem evalForeignFrameDerefWrite_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    {cs : List SavedCallerFrame}
    (s : MachineState) (locals₁ : List LocalSlot) (mem₁ : Memory) (dst : Place)
    (restProj : List ProjectionElem) (val : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hcs : CallerBodiesEq cs mem₁.callStack) :
    StepCtxCB c ac ti cs
      (evalForeignFrameDerefWrite (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals₁ (Memory.withCalleeCtx c ac ti mem₁) dst restProj val localDecls layouts)
      (evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts) := by
  unfold evalForeignFrameDerefWrite
  rw [foreignFrameDerefWrite_withCalleeCtx]
  cases hw : foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts with
  | ub => exact stepCtxCB_fail
  | unsupported => exact stepCtxCB_unsupported
  | ok locals₂ mem₂ =>
    exact stepCtxCB_advance rfl rfl (hcs.trans (foreignFrameDerefWrite_callerBodies hw))

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
        (evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts) :=
  (evalForeignFrameDerefWrite_stepCtxCB c ac ti s locals₁ mem₁ dst restProj val localDecls layouts
    (CallerBodiesEq.refl _)).1

theorem evalForeignFrameDerefWrite_callerBodies {cs : List SavedCallerFrame} (s : MachineState)
    (locals₁ : List LocalSlot) (mem₁ : Memory) (dst : Place) (restProj : List ProjectionElem)
    (val : Value) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h : CallerBodiesEq cs mem₁.callStack) :
    NodeSuccs (fun s' => CallerBodiesEq cs s'.memory.callStack)
      (evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts) :=
  (evalForeignFrameDerefWrite_stepCtxCB [] none [] s locals₁ mem₁ dst restProj val localDecls
    layouts h).2

private theorem evalSetDiscriminantDerefWrite_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals₁ : List LocalSlot) (p : Place)
    (rest : List ProjectionElem) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    StepCtxCB c ac ti s.memory.callStack
      (evalSetDiscriminantDerefWrite (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals₁ p rest newVal localDecls layouts)
      (evalSetDiscriminantDerefWrite s locals₁ p rest newVal localDecls layouts) := by
  unfold evalSetDiscriminantDerefWrite
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact stepCtxCB_fail | exact stepCtxCB_unsupported
      | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_mk rfl (CallerBodiesEq.refl _))
    | exact ⟨evalForeignFrameDerefWrite_withCalleeCtx c ac ti s locals₁ s.memory p rest newVal
        localDecls layouts,
        evalForeignFrameDerefWrite_callerBodies s locals₁ s.memory p rest newVal
        localDecls layouts (CallerBodiesEq.refl _)⟩
    | split)

/-- The dereferencing `SetDiscriminant` write (`evalSetDiscriminantDerefWrite`). -/
theorem evalSetDiscriminantDerefWrite_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals₁ : List LocalSlot) (p : Place)
    (rest : List ProjectionElem) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalSetDiscriminantDerefWrite (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals₁ p rest newVal localDecls layouts =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalSetDiscriminantDerefWrite s locals₁ p rest newVal localDecls layouts) :=
  (evalSetDiscriminantDerefWrite_stepCtxCB c ac ti s locals₁ p rest newVal localDecls layouts).1

theorem evalSetDiscriminantDerefWrite_callerBodies (s : MachineState)
    (locals₁ : List LocalSlot) (p : Place) (rest : List ProjectionElem) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalSetDiscriminantDerefWrite s locals₁ p rest newVal localDecls layouts) :=
  (evalSetDiscriminantDerefWrite_stepCtxCB [] none [] s locals₁ p rest newVal localDecls layouts).2

private theorem evalFnEntryRetag_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Place) (ptrVal : ProvenancePtr) (sz : Nat)
    (parentEntry : BorrowEntry) (locals' : List LocalSlot) :
    StepCtxCB c ac ti s.memory.callStack
      (evalFnEntryRetag (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        localDecls layouts place ptrVal sz parentEntry locals')
      (evalFnEntryRetag s localDecls layouts place ptrVal sz parentEntry locals') := by
  unfold evalFnEntryRetag
  dsimp (config := { zeta := false }) only [MachineState.mapMem, Memory.withCalleeCtx]
  cases placeTy localDecls layouts place with
  | none => exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
  | some ty =>
    dsimp (config := { zeta := false }) only
    cases ty.kind with
    | ref mutability pointee =>
      dsimp (config := { zeta := false }) only
      cases rigidTyIsUninhabited 16 pointee with
      | true => exact stepCtxCB_fail
      | false =>
        dsimp (config := { zeta := false }) only
        extract_lets _protId _childPerm _skipInitRead tag readUB
        cases readUB with
        | true => exact stepCtxCB_fail
        | false =>
          dsimp (config := { zeta := false }) only
          cases place.projection with
          | nil =>
            dsimp (config := { zeta := false }) only
            cases set? locals' place.local_
              (.init (.ptr { allocId := tag, offsetBytes := ptrVal.offsetBytes } sz)) <;>
              first | exact stepCtxCB_fail | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
          | cons _ _ =>
            dsimp only
            exact stepCtxCB_unsupported
    | _ => exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)

theorem evalFnEntryRetag_callerBodies (s : MachineState) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (place : Place) (ptrVal : ProvenancePtr) (sz : Nat)
    (parentEntry : BorrowEntry) (locals' : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalFnEntryRetag s localDecls layouts place ptrVal sz parentEntry locals') :=
  (evalFnEntryRetag_stepCtxCB [] none [] s localDecls layouts place ptrVal sz parentEntry locals').2

private theorem evalNonFnEntryRetag_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (retagKind : RetagKind) (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Place) (ptrVal : ProvenancePtr) (sz : Nat)
    (parentEntry : BorrowEntry) (locals' : List LocalSlot) :
    StepCtxCB c ac ti s.memory.callStack
      (evalNonFnEntryRetag retagKind (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        localDecls layouts place ptrVal sz parentEntry locals')
      (evalNonFnEntryRetag retagKind s localDecls layouts place ptrVal sz parentEntry locals') := by
  unfold evalNonFnEntryRetag
  dsimp (config := { zeta := false }) only [MachineState.mapMem, Memory.withCalleeCtx]
  cases placeTy localDecls layouts place with
  | none => exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
  | some ty =>
    dsimp (config := { zeta := false }) only
    cases ty.kind with
    | ref mutability pointee =>
      dsimp (config := { zeta := false }) only
      cases rigidTyIsUninhabited 16 pointee with
      | true => exact stepCtxCB_fail
      | false =>
        dsimp (config := { zeta := false }) only
        extract_lets _childPerm _skipInitRead tag readUB
        cases readUB with
        | true => exact stepCtxCB_fail
        | false =>
          dsimp (config := { zeta := false }) only
          cases place.projection with
          | nil =>
            dsimp (config := { zeta := false }) only
            cases set? locals' place.local_
              (.init (.ptr { allocId := tag, offsetBytes := ptrVal.offsetBytes } sz)) <;>
              first | exact stepCtxCB_fail | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
          | cons _ _ =>
            dsimp only
            exact stepCtxCB_unsupported
    | _ => exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)

theorem evalNonFnEntryRetag_callerBodies (retagKind : RetagKind) (s : MachineState)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place)
    (ptrVal : ProvenancePtr) (sz : Nat) (parentEntry : BorrowEntry) (locals' : List LocalSlot) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalNonFnEntryRetag retagKind s localDecls layouts place ptrVal sz parentEntry locals') :=
  (evalNonFnEntryRetag_stepCtxCB [] none [] retagKind s localDecls layouts place ptrVal sz
    parentEntry locals').2

private theorem evalStmt_retag_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (rk : RetagKind) (p : Place) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    StepCtxCB c ac ti s.memory.callStack
      (evalStmt (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        { kind := .retag rk p, span := span } localDecls layouts)
      (evalStmt s { kind := .retag rk p, span := span } localDecls layouts) := by
  unfold evalStmt
  dsimp (config := { zeta := false }) only [MachineState.mapMem, Memory.withCalleeCtx]
  cases evalOperand s.frame.locals (.copy p) s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls s.memory.callStack with
  | ub => exact stepCtxCB_fail
  | unsupported => exact stepCtxCB_unsupported
  | ok val locals' =>
    dsimp (config := { zeta := false }) only
    extract_lets placeTyOpt isMutRefPlace _elemSz _pointeeBytes checkGlobalRetagL retagPtrValL _protId _srcM checkGlobalRetagR retagPtrValR
    have h_cg : ∀ ptrOrFatVal ptrVal,
        StepCtxCB c ac ti s.memory.callStack
          (checkGlobalRetagL ptrOrFatVal ptrVal) (checkGlobalRetagR ptrOrFatVal ptrVal) := by
      intro ptrOrFatVal ptrVal
      dsimp (config := { zeta := false }) only [checkGlobalRetagL, checkGlobalRetagR]
      cases lookupGlobalAlloc s.memory.globals ptrVal.allocId with
      | some alloc =>
        dsimp (config := { zeta := false }) only
        extract_lets mutOk boundsOk
        cases Bool.and mutOk boundsOk with
        | true => exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
        | false => exact stepCtxCB_fail
      | none =>
        dsimp (config := { zeta := false }) only
        extract_lets isNonNullEmptySlice
        cases isNonNullEmptySlice with
        | true => exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
        | false => exact stepCtxCB_fail
    have h_rp : ∀ ptrVal sz allowGlobal,
        StepCtxCB c ac ti s.memory.callStack
          (retagPtrValL ptrVal sz allowGlobal) (retagPtrValR ptrVal sz allowGlobal) := by
      intro ptrVal sz allowGlobal
      dsimp (config := { zeta := false }) only [retagPtrValL, retagPtrValR]
      cases lookupBorrow s.memory.borrows ptrVal.tag with
      | some entry =>
        dsimp (config := { zeta := false }) only
        cases entry.perm with
        | disabled => exact stepCtxCB_fail
        | _ =>
          dsimp (config := { zeta := false }) only
          cases rk with
          | fnEntry =>
            exact ⟨(evalFnEntryRetag_stepCtxCB c ac ti s localDecls layouts p ptrVal sz entry locals').1,
              evalFnEntryRetag_callerBodies s localDecls layouts p ptrVal sz entry locals'⟩
          | default =>
            exact ⟨(evalNonFnEntryRetag_stepCtxCB c ac ti .default s localDecls layouts p ptrVal sz entry locals').1,
              evalNonFnEntryRetag_callerBodies .default s localDecls layouts p ptrVal sz entry locals'⟩
          | twoPhase =>
            exact ⟨(evalNonFnEntryRetag_stepCtxCB c ac ti .twoPhase s localDecls layouts p ptrVal sz entry locals').1,
              evalNonFnEntryRetag_callerBodies .twoPhase s localDecls layouts p ptrVal sz entry locals'⟩
          | raw =>
            exact ⟨(evalNonFnEntryRetag_stepCtxCB c ac ti .raw s localDecls layouts p ptrVal sz entry locals').1,
              evalNonFnEntryRetag_callerBodies .raw s localDecls layouts p ptrVal sz entry locals'⟩
      | none =>
        dsimp (config := { zeta := false }) only
        cases allowGlobal with
        | true => exact h_cg val ptrVal
        | false => exact stepCtxCB_fail
    cases h_pt : placeTyOpt with
    | none =>
      dsimp (config := { zeta := false }) only
      cases val with
      | ptr ptrVal sz => exact h_rp ptrVal sz false
      | aggregate v fs =>
        repeat' (first
          | contradiction
          | with_reducible (first
            | exact stepCtxCB_fail | exact stepCtxCB_unsupported
            | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
            | exact h_cg _ _)
          | split)
      | _ => first | exact stepCtxCB_fail | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
    | some ty =>
      cases ty with
      | mk kind lIdx =>
        cases kind with
        | rawPtr _ _ =>
          dsimp (config := { zeta := false }) only
          cases rk <;> first | exact stepCtxCB_fail | exact stepCtxCB_unsupported | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
        | ref _ pointee =>
          dsimp (config := { zeta := false }) only
          cases rigidTyIsUninhabited 16 pointee with
          | true => exact stepCtxCB_fail
          | false =>
            dsimp (config := { zeta := false }) only
            cases val with
            | ptr ptrVal sz => exact h_rp ptrVal sz true
            | scalar sc =>
              dsimp (config := { zeta := false }) only
              cases Bool.and (rigidTyIsZeroSized 16 pointee) (Bool.not (Nat.beq sc.bits 0)) with
              | true => exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
              | false => exact stepCtxCB_fail
            | aggregate v fs =>
              try dsimp (config := { zeta := false }) only
              repeat' (first
                | contradiction
                | with_reducible (first
                  | exact stepCtxCB_fail | exact stepCtxCB_unsupported
                  | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
                  | exact h_cg _ _)
                | split)
            | _ => first | exact stepCtxCB_fail | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
        | _ =>
          dsimp (config := { zeta := false }) only
          cases val with
          | ptr ptrVal sz => exact h_rp ptrVal sz true
          | _ => first | exact stepCtxCB_fail | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)

private theorem ccEvalAssignDst_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    {cs : List SavedCallerFrame}
    (s : MachineState) (dst : Place) (val : Value)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hcs : CallerBodiesEq cs mem₁.callStack) :
    StepCtxCB c ac ti cs
      (ccEvalAssignDst (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s) dst val locals₁
        (Memory.withCalleeCtx c ac ti mem₁) localDecls layouts)
      (ccEvalAssignDst s dst val locals₁ mem₁ localDecls layouts) := by
  rcases dst with ⟨dstLoc, dstProj⟩
  cases dstProj with
  | nil =>
    unfold ccEvalAssignDst
    dsimp only [Memory.withCalleeCtx]
    repeat' (first
      | with_reducible (first
        | exact stepCtxCB_fail | exact stepCtxCB_unsupported
        | exact stepCtxCB_advance rfl rfl hcs)
      | split)
  | cons hd tl =>
    cases ccProjIsDeref hd with
    | isTrue h_d =>
      subst h_d
      have hFor : ∀ l p rp v,
          StepCtxCB c ac ti cs
            (evalForeignFrameDerefWrite (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s) l
              { mem₁ with callees := c, activeCallee := ac, traitImpls := ti } p rp v localDecls layouts)
            (evalForeignFrameDerefWrite s l mem₁ p rp v localDecls layouts) :=
        fun l p rp v => ⟨evalForeignFrameDerefWrite_withCalleeCtx c ac ti s l mem₁ p rp v localDecls layouts,
          evalForeignFrameDerefWrite_callerBodies s l mem₁ p rp v localDecls layouts hcs⟩
      unfold ccEvalAssignDst
      dsimp only [Memory.withCalleeCtx]
      repeat' (first
        | with_reducible (first
          | exact stepCtxCB_fail | exact stepCtxCB_unsupported
          | exact stepCtxCB_advance rfl rfl hcs
          | exact hFor ..)
        | split)
    | isFalse h_d =>
      rw [ccEvalAssignDst_nonDeref _ _ _ _ _ _ _ _ _ h_d,
          ccEvalAssignDst_nonDeref _ _ _ _ _ _ _ _ _ h_d]
      unfold ccEvalAssignNonDeref
      dsimp only [Memory.withCalleeCtx]
      repeat' (first
        | with_reducible (first
          | exact stepCtxCB_fail | exact stepCtxCB_unsupported
          | exact stepCtxCB_advance rfl rfl hcs)
        | split)

private theorem evalStmt_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_free : Statement.calleeQueryFree stmt = true) :
    StepCtxCB c ac ti s.memory.callStack
      (evalStmt (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s) stmt localDecls layouts)
      (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | nop | coverage | constEvalCounter =>
    exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)
  | placeMention p =>
    dsimp +zetaDelta only [evalStmt, MachineState.mapMem, Memory.withCalleeCtx]
    repeat' (first
      | with_reducible (first
        | exact stepCtxCB_fail | exact stepCtxCB_unsupported
        | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _))
      | split)
  | retag rk p =>
    exact evalStmt_retag_stepCtxCB c ac ti s rk p span localDecls layouts
  | storageLive loc | storageDead loc =>
    dsimp +zetaDelta only [evalStmt, MachineState.mapMem, Memory.withCalleeCtx]
    repeat' (first
      | with_reducible (first
        | exact stepCtxCB_fail | exact stepCtxCB_unsupported
        | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _))
      | split)
  | deinit p =>
    rcases p with ⟨pLoc, pProj⟩
    cases pProj <;> {
      dsimp +zetaDelta only [evalStmt, MachineState.mapMem, Memory.withCalleeCtx]
      repeat' (first
        | with_reducible (first
          | exact stepCtxCB_fail | exact stepCtxCB_unsupported
          | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _))
        | split)
    }
  | intrinsic intr =>
    cases intr with
    | assume op =>
      dsimp +zetaDelta only [evalStmt, MachineState.mapMem, Memory.withCalleeCtx]
      repeat' (first
        | with_reducible (first
          | exact stepCtxCB_fail | exact stepCtxCB_unsupported
          | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _))
        | split)
    | copyNonOverlapping src dst count =>
      exact ⟨evalCopyNonOverlapping_withCalleeCtx c ac ti s src dst count localDecls layouts,
        evalCopyNonOverlapping_callerBodies s src dst count localDecls layouts⟩
  | setDiscriminant p variantIdx =>
    rcases p with ⟨pLoc, pProj⟩
    cases pProj <;> {
      dsimp +zetaDelta only [evalStmt, MachineState.mapMem, Memory.withCalleeCtx]
      repeat' (first
        | with_reducible (first
          | exact stepCtxCB_fail | exact stepCtxCB_unsupported
          | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _))
        | exact ⟨evalSetDiscriminantLocal_withCalleeCtx c ac ti s _ _ _,
            evalSetDiscriminantLocal_callerBodies s _ _ _⟩
        | exact ⟨evalSetDiscriminantDerefWrite_withCalleeCtx c ac ti s _ _ _ _ localDecls layouts,
            evalSetDiscriminantDerefWrite_callerBodies s _ _ _ _ localDecls layouts⟩
        | split)
    }
  | assign dst rv =>
    rw [ccEvalStmt_assign_eq, ccEvalStmt_assign_eq]
    dsimp only [MachineState.mapMem]
    have hRv : RvCtxCS c ac ti s.memory.callStack _ _ :=
      ⟨evalRvalue_withCalleeCtx c ac ti s.frame.locals rv s.memory localDecls layouts h_free,
       evalRvalue_rvCS s.frame.locals rv s.memory localDecls layouts⟩
    rw [hRv.1]
    cases hEq : evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | ub => exact stepCtxCB_fail
    | unsupported => exact stepCtxCB_unsupported
    | ok val locals₁ mem₁ =>
      dsimp only [RvalueEvalResult.mapMem]
      exact ccEvalAssignDst_stepCtxCB c ac ti s dst val locals₁ mem₁ localDecls layouts
        (CallerBodiesEq.of_eq (hRv.2.callStack_eq hEq))
  | _ =>
    first
    | exact stepCtxCB_fail
    | exact stepCtxCB_unsupported
    | exact stepCtxCB_advance rfl rfl (CallerBodiesEq.refl _)

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
        (evalStmt s stmt localDecls layouts) :=
  (evalStmt_stepCtxCB c ac ti s stmt localDecls layouts h_free).1

/-! ### Generic `mapMem` algebra -/

@[simp]
theorem evalStmt_callerBodies (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    rw [ccEvalStmt_assign_eq]
    cases h_rv : evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | ub | unsupported => trivial
    | ok val locals₁ mem₁ =>
      exact (ccEvalAssignDst_stepCtxCB [] none [] s dst val locals₁ mem₁ localDecls layouts
        (CallerBodiesEq.of_eq (evalRvalue_callStack h_rv))).2
  | _ =>
    exact (evalStmt_stepCtxCB [] none [] s ⟨_, span⟩ localDecls layouts rfl).2

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
        match valueContainsUninit retVal with
        | true => MirStepNode.fail .ub
        | false =>
          MirStepNode.retNormal retVal
            { s.memory with
              borrows := disableFrameBorrows s.memory.borrows (length s.memory.callStack)
                (length s.frame.locals) }
      | caller :: restStack =>
        match caller.isDiverging with
        | true => MirStepNode.fail .ub
        | false =>
          match valueContainsUninit retVal with
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

private theorem invalidateDirectDestWriteBorrows_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (mem : Memory) (locals : List LocalSlot) (dst : Place) :
    invalidateDirectDestWriteBorrows (Memory.withCalleeCtx c ac ti mem) locals dst =
      Memory.withCalleeCtx c ac ti (invalidateDirectDestWriteBorrows mem locals dst) := by
  unfold invalidateDirectDestWriteBorrows
  dsimp only [Memory.withCalleeCtx]
  repeat' (first | rfl | split)

private theorem writeIntrinsicReturn_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (retVal : Value) :
    StepCtxCB c ac ti s.memory.callStack
      (writeIntrinsicReturn (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals' destination targetBb retVal)
      (writeIntrinsicReturn s locals' destination targetBb retVal) := by
  unfold writeIntrinsicReturn
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first
    | with_reducible (first
      | exact stepCtxCB_fail | exact stepCtxCB_unsupported
      | exact stepCtxCB_mk rfl (CallerBodiesEq.refl _)
      | exact stepCtxCB_mk (invalidateDirectDestWriteBorrows_withCalleeCtx ..)
          (CallerBodiesEq.of_eq (invalidateDirectDestWriteBorrows_callStack ..)))
    | split)
  all_goals (
    simp only [foreignFrameDerefWrite_withCalleeCtx'] at *
    simp only [*, FrameWriteResult.mapMem] at *
    first
    | (simp at *; done)
    | (simp only [FrameWriteResult.ok.injEq] at *
       obtain ⟨h₁, h₂⟩ := ‹_ ∧ _›
       subst_vars
       exact stepCtxCB_mk rfl (cb_of_foreignFrameDerefWrite (by assumption) (by rfl))))

theorem writeIntrinsicReturn_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (retVal : Value) :
    writeIntrinsicReturn (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals' destination targetBb retVal =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (writeIntrinsicReturn s locals' destination targetBb retVal) :=
  (writeIntrinsicReturn_stepCtxCB c ac ti s locals' destination targetBb retVal).1

theorem writeIntrinsicReturn_callerBodies (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (retVal : Value) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (writeIntrinsicReturn s locals' destination targetBb retVal) :=
  (writeIntrinsicReturn_stepCtxCB [] none [] s locals' destination targetBb retVal).2

private theorem writeIntrinsicScalarResult_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (resOpt : Option ScalarInt) :
    StepCtxCB c ac ti s.memory.callStack
      (writeIntrinsicScalarResult (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals' destination targetBb resOpt)
      (writeIntrinsicScalarResult s locals' destination targetBb resOpt) := by
  cases resOpt with
  | none => exact stepCtxCB_fail
  | some sc =>
    exact ⟨writeIntrinsicReturn_withCalleeCtx c ac ti s locals' destination targetBb (.scalar sc),
      writeIntrinsicReturn_callerBodies s locals' destination targetBb (.scalar sc)⟩

theorem writeIntrinsicScalarResult_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (resOpt : Option ScalarInt) :
    writeIntrinsicScalarResult (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals' destination targetBb resOpt =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (writeIntrinsicScalarResult s locals' destination targetBb resOpt) :=
  (writeIntrinsicScalarResult_stepCtxCB c ac ti s locals' destination targetBb resOpt).1

theorem writeIntrinsicScalarResult_callerBodies (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (resOpt : Option ScalarInt) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (writeIntrinsicScalarResult s locals' destination targetBb resOpt) :=
  (writeIntrinsicScalarResult_stepCtxCB [] none [] s locals' destination targetBb resOpt).2

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
    | with_reducible (first | exact ns_fail | exact ns_unsupported)
    | split
    | (dsimp only))

/-- **Inline intrinsic calls keep every saved caller body.** -/

private theorem evalNonSelectIntrinsicCall_stepCtxCB
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (kind : RustIntrinsicKind) (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    StepCtxCB c ac ti s.memory.callStack
      (evalNonSelectIntrinsicCall kind (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb)
      (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb) := by
  have hMissing : StepCtxCB c ac ti s.memory.callStack
      (intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps)
      (intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps) :=
    ⟨by unfold intrinsicMissingPointeeStep
        repeat' (first | rfl | split),
     intrinsicMissingPointeeStep_callerBodies bodyLocalDecls bodyLayouts argOps⟩
  have hUnres : ∀ pt, StepCtxCB c ac ti s.memory.callStack
      (intrinsicUnresolvedLayoutStep pt) (intrinsicUnresolvedLayoutStep pt) := fun pt =>
    ⟨by unfold intrinsicUnresolvedLayoutStep; split <;> rfl,
     intrinsicUnresolvedLayoutStep_callerBodies pt⟩
  have hWide : ∀ pt, StepCtxCB c ac ti s.memory.callStack
      (intrinsicWidePointeeStep pt) (intrinsicWidePointeeStep pt) := fun pt =>
    ⟨by unfold intrinsicWidePointeeStep; split <;> rfl,
     intrinsicWidePointeeStep_callerBodies pt⟩
  have hRet : ∀ v, StepCtxCB c ac ti s.memory.callStack
      (writeIntrinsicReturn (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals' destination targetBb v)
      (writeIntrinsicReturn s locals' destination targetBb v) := fun v =>
    ⟨writeIntrinsicReturn_withCalleeCtx c ac ti s locals' destination targetBb v,
     writeIntrinsicReturn_callerBodies s locals' destination targetBb v⟩
  have hScalar : ∀ r, StepCtxCB c ac ti s.memory.callStack
      (writeIntrinsicScalarResult (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        locals' destination targetBb r)
      (writeIntrinsicScalarResult s locals' destination targetBb r) := fun r =>
    ⟨writeIntrinsicScalarResult_withCalleeCtx c ac ti s locals' destination targetBb r,
     writeIntrinsicScalarResult_callerBodies s locals' destination targetBb r⟩
  unfold evalNonSelectIntrinsicCall
  cases kind <;> (
    dsimp only
    repeat' (first
      | with_reducible (first
        | exact stepCtxCB_fail | exact stepCtxCB_unsupported
        | exact hMissing | exact hUnres _ | exact hWide _
        | exact hRet _ | exact hScalar _)
      | split))

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
          argOps argVals locals' destination targetBb) :=
  (evalNonSelectIntrinsicCall_stepCtxCB c ac ti kind s target bodyLocalDecls bodyLayouts
    argOps argVals locals' destination targetBb).1

theorem evalNonSelectIntrinsicCall_callerBodies (kind : RustIntrinsicKind) (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts argOps argVals locals'
        destination targetBb) :=
  (evalNonSelectIntrinsicCall_stepCtxCB [] none [] kind s target bodyLocalDecls bodyLayouts
    argOps argVals locals' destination targetBb).2

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

private theorem finishMemIntrinsicCall_mapMem_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (node : MirStepNode) (destination : Place) (targetBb : BasicBlockIdx) :
    finishMemIntrinsicCall (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        (MirStepNode.mapMem (Memory.withCalleeCtx c ac ti) node) destination targetBb =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (finishMemIntrinsicCall s node destination targetBb) := by
  cases node with
  | ret _ => rfl
  | vis e k => rcases e with _ | _ | ⟨_⟩ <;> rfl
  | tau st =>
    cases st with
    | halted _ => rfl
    | faulted _ => rfl
    | running s' =>
      exact writeIntrinsicReturn_withCalleeCtx c ac ti { s with memory := s'.memory }
        s'.frame.locals destination targetBb .unit

theorem evalCopyNonOverlappingCall_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    evalCopyNonOverlappingCall (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalCopyNonOverlappingCall s bodyLocalDecls bodyLayouts argOps argVals locals'
          destination targetBb) := by
  unfold evalCopyNonOverlappingCall
  rcases argOps with _ | ⟨srcOp, _ | ⟨dstOp, _ | ⟨countOp, tlOps⟩⟩⟩ <;> try rfl
  cases tlOps <;> try rfl
  rcases argVals with _ | ⟨srcVal, _ | ⟨dstVal, _ | ⟨countVal, tlVals⟩⟩⟩ <;> try rfl
  cases countVal <;> cases tlVals <;> try rfl
  rename_i countSc
  dsimp only
  cases Nat.beq countSc.sizeBytes (layoutPointerBytes bodyLayouts) with
  | false => rfl
  | true =>
    dsimp only
    rw [evalCopyNonOverlappingWithCount_withCalleeCtx c ac ti s srcOp dstOp bodyLocalDecls
      bodyLayouts srcVal dstVal countSc.bits locals']
    exact finishMemIntrinsicCall_mapMem_withCalleeCtx c ac ti s _ destination targetBb

theorem evalCopyNonOverlappingCall_calleeCtx_preserved
    (s : MachineState) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    evalCopyNonOverlappingCall s bodyLocalDecls bodyLayouts argOps argVals locals'
        destination targetBb =
      MirStepNode.mapMem
        (Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls)
        (evalCopyNonOverlappingCall s bodyLocalDecls bodyLayouts argOps argVals locals'
          destination targetBb) := by
  have h := evalCopyNonOverlappingCall_withCalleeCtx
    s.memory.callees s.memory.activeCallee s.memory.traitImpls
    s bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb
  rw [MachineState.withCalleeCtx_self] at h
  exact h

theorem evalCopyNonOverlappingCall_withCallees
    (c₂ : CalleeEnv) (s : MachineState) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand) (argVals : List Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx) :
    evalCopyNonOverlappingCall (MachineState.mapMem (Memory.withCallees c₂) s)
        bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb =
      MirStepNode.mapMem (Memory.withCallees c₂)
        (evalCopyNonOverlappingCall s bodyLocalDecls bodyLayouts argOps argVals locals'
          destination targetBb) := by
  rw [MachineState.withCallees_eq_withCalleeCtx,
    evalCopyNonOverlappingCall_withCalleeCtx _ _ _ s bodyLocalDecls bodyLayouts argOps argVals
      locals' destination targetBb,
    evalCopyNonOverlappingCall_calleeCtx_preserved s bodyLocalDecls bodyLayouts argOps argVals
      locals' destination targetBb,
    MirStepNode.mapMem_comp, MirStepNode.mapMem_comp, Memory.withCallees_comp_withCalleeCtx]

private theorem commitWriteBytesDstPlaceWrite_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (dstPlace : Place) (dstTag : Nat) (locals₃ : List LocalSlot)
    (newVal : Value) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    commitWriteBytesDstPlaceWrite (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        dstPlace dstTag locals₃ newVal localDecls layouts =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (commitWriteBytesDstPlaceWrite s dstPlace dstTag locals₃ newVal localDecls layouts) := by
  unfold commitWriteBytesDstPlaceWrite
  dsimp only [MachineState.mapMem, Memory.withCalleeCtx]
  repeat' (first | exact stepCtx_fail | exact stepCtx_step rfl | split)

theorem evalWriteBytesCall_withCalleeCtx
    (c : CalleeEnv) (ac : Option CapturedMir) (ti : List TraitImplEntry)
    (s : MachineState) (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand) (argVals : List Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx) :
    evalWriteBytesCall (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s)
        target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb =
      MirStepNode.mapMem (Memory.withCalleeCtx c ac ti)
        (evalWriteBytesCall s target bodyLocalDecls bodyLayouts argOps argVals locals'
          destination targetBb) := by
  unfold evalWriteBytesCall
  have hAct :
      writeBytesAction (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s).memory.borrows
        (length (MachineState.mapMem (Memory.withCalleeCtx c ac ti) s).memory.callStack)
        target bodyLocalDecls bodyLayouts argOps argVals =
      writeBytesAction s.memory.borrows (length s.memory.callStack)
        target bodyLocalDecls bodyLayouts argOps argVals := rfl
  rw [hAct]
  cases writeBytesAction s.memory.borrows (length s.memory.callStack) target bodyLocalDecls
      bodyLayouts argOps argVals with
  | fault kind => rfl
  | noWrite =>
    exact writeIntrinsicReturn_withCalleeCtx c ac ti s locals' destination targetBb .unit
  | store dstPlace _ dstTag newVal =>
    dsimp only
    rw [commitWriteBytesDstPlaceWrite_withCalleeCtx c ac ti s dstPlace dstTag locals' newVal
      bodyLocalDecls bodyLayouts]
    exact finishMemIntrinsicCall_mapMem_withCalleeCtx c ac ti s _ destination targetBb

theorem evalWriteBytesCall_calleeCtx_preserved
    (s : MachineState) (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand) (argVals : List Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx) :
    evalWriteBytesCall s target bodyLocalDecls bodyLayouts argOps argVals locals'
        destination targetBb =
      MirStepNode.mapMem
        (Memory.withCalleeCtx s.memory.callees s.memory.activeCallee s.memory.traitImpls)
        (evalWriteBytesCall s target bodyLocalDecls bodyLayouts argOps argVals locals'
          destination targetBb) := by
  have h := evalWriteBytesCall_withCalleeCtx
    s.memory.callees s.memory.activeCallee s.memory.traitImpls
    s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb
  rw [MachineState.withCalleeCtx_self] at h
  exact h

theorem evalWriteBytesCall_withCallees
    (c₂ : CalleeEnv) (s : MachineState) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    evalWriteBytesCall (MachineState.mapMem (Memory.withCallees c₂) s)
        target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb =
      MirStepNode.mapMem (Memory.withCallees c₂)
        (evalWriteBytesCall s target bodyLocalDecls bodyLayouts argOps argVals locals'
          destination targetBb) := by
  rw [MachineState.withCallees_eq_withCalleeCtx,
    evalWriteBytesCall_withCalleeCtx _ _ _ s target bodyLocalDecls bodyLayouts argOps argVals
      locals' destination targetBb,
    evalWriteBytesCall_calleeCtx_preserved s target bodyLocalDecls bodyLayouts argOps argVals
      locals' destination targetBb,
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
    | copyNonOverlapping =>
      dsimp only [Option.map]
      exact congrArg some
        (evalCopyNonOverlappingCall_withCallees c₂ s bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
    | writeBytes =>
      dsimp only [Option.map]
      exact congrArg some
        (evalWriteBytesCall_withCallees c₂ s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
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
      Memory.withCallees_globals, Memory.withCallees_callerLocals, Memory.withCallees_callStack,
      Memory.withCallees_activeProtectors]
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
    rcases place with ⟨pLoc, pProj⟩
    cases pProj <;> {
      unfold evalTerminator
      dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
        Memory.withCallees_callStack, Memory.withCallees_activeProtectors]
      repeat' (first | exact nodeCC_fail | rfl | split)
    }
  | assert cond expected target unwind =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
      Memory.withCallees_globals, Memory.withCallees_callerLocals, Memory.withCallees_callStack,
      Memory.withCallees_activeProtectors]
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

private theorem finishMemIntrinsicCall_callerBodies (s : MachineState) (node : MirStepNode)
    (destination : Place) (targetBb : BasicBlockIdx)
    (hNode : NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack) node) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (finishMemIntrinsicCall s node destination targetBb) := by
  cases node with
  | ret _ => trivial
  | vis e k => exact hNode
  | tau st =>
    cases st with
    | halted _ => trivial
    | faulted _ => trivial
    | running s' =>
      exact NodeSuccs.mono (fun _ hs'' => hNode.trans hs'')
        (writeIntrinsicReturn_callerBodies { s with memory := s'.memory } s'.frame.locals
          destination targetBb .unit)

theorem evalCopyNonOverlappingCall_callerBodies (s : MachineState)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalCopyNonOverlappingCall s bodyLocalDecls bodyLayouts argOps argVals locals'
        destination targetBb) := by
  unfold evalCopyNonOverlappingCall
  rcases argOps with _ | ⟨srcOp, _ | ⟨dstOp, _ | ⟨countOp, tlOps⟩⟩⟩ <;> try exact ns_fail
  cases tlOps <;> try exact ns_fail
  rcases argVals with _ | ⟨srcVal, _ | ⟨dstVal, _ | ⟨countVal, tlVals⟩⟩⟩ <;> try exact ns_fail
  cases countVal <;> cases tlVals <;> try exact ns_fail
  rename_i countSc
  dsimp only
  cases Nat.beq countSc.sizeBytes (layoutPointerBytes bodyLayouts) with
  | false => exact ns_fail
  | true =>
    exact finishMemIntrinsicCall_callerBodies s _ destination targetBb
      (evalCopyNonOverlappingWithCount_callerBodies s srcOp dstOp bodyLocalDecls bodyLayouts
        srcVal dstVal countSc.bits locals')

private theorem commitWriteBytesDstPlaceWrite_callerBodies (s : MachineState)
    (dstPlace : Place) (dstTag : Nat) (locals₃ : List LocalSlot) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (commitWriteBytesDstPlaceWrite s dstPlace dstTag locals₃ newVal localDecls layouts) := by
  unfold commitWriteBytesDstPlaceWrite
  try dsimp only
  repeat' (first
    | split
    | (with_reducible exact ns_fail)
    | (with_reducible exact ns_unsupported)
    | ((with_reducible apply ns_advance); exact CallerBodiesEq.refl _)
    | (dsimp only))

theorem evalWriteBytesCall_callerBodies (s : MachineState) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    NodeSuccs (fun s' => CallerBodiesEq s.memory.callStack s'.memory.callStack)
      (evalWriteBytesCall s target bodyLocalDecls bodyLayouts argOps argVals locals'
        destination targetBb) := by
  unfold evalWriteBytesCall
  cases writeBytesAction s.memory.borrows (length s.memory.callStack) target bodyLocalDecls
      bodyLayouts argOps argVals with
  | fault _ => exact ns_fail
  | noWrite => exact writeIntrinsicReturn_callerBodies s locals' destination targetBb .unit
  | store dstPlace _ dstTag newVal =>
    exact finishMemIntrinsicCall_callerBodies s _ destination targetBb
      (commitWriteBytesDstPlaceWrite_callerBodies s dstPlace dstTag locals' newVal
        bodyLocalDecls bodyLayouts)

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
    | copyNonOverlapping =>
      exact nodeSuccs_closedInv_of_ctx h_inv
        (evalCopyNonOverlappingCall_calleeCtx_preserved s bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
        (evalCopyNonOverlappingCall_callerBodies s bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
    | writeBytes =>
      exact nodeSuccs_closedInv_of_ctx h_inv
        (evalWriteBytesCall_calleeCtx_preserved s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
        (evalWriteBytesCall_callerBodies s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
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
      Memory.withCallees_globals, Memory.withCallees_callerLocals, Memory.withCallees_callStack,
      Memory.withCallees_activeProtectors]
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
    rcases place with ⟨pLoc, pProj⟩
    cases pProj <;> {
      unfold evalTerminator
      dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
        Memory.withCallees_callStack, Memory.withCallees_activeProtectors]
      repeat' (first | exact nodeCC_fail | rfl | split)
    }
  | assert cond expected target unwind =>
    unfold evalTerminator
    dsimp only [MachineState.mapMem_frame, MachineState.mapMem_memory, Memory.withCallees_borrows,
      Memory.withCallees_globals, Memory.withCallees_callerLocals, Memory.withCallees_callStack,
      Memory.withCallees_activeProtectors]
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
    | copyNonOverlapping =>
      exact nodeSuccs_closedInvPoly_of_ctx h_inv
        (evalCopyNonOverlappingCall_calleeCtx_preserved s bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
        (evalCopyNonOverlappingCall_callerBodies s bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
    | writeBytes =>
      exact nodeSuccs_closedInvPoly_of_ctx h_inv
        (evalWriteBytesCall_calleeCtx_preserved s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
        (evalWriteBytesCall_callerBodies s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
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

/-!
## Unsized DST Pointer Metadata, `AggregateKind.rawPtr`, and Dynamic Layout Intrinsics

Composable ground-MIR evaluation, `PureMirExec.mirStep`, `wpMirExecSym`, and
`MirWpConverges` step combinators across six subsections:
1. `Rvalue.unaryOp .ptrMetadata` (wide `[T]` / `str` pointers and thin pointers,
   plus width-mismatch UB refutations), `Rvalue.aggregate (.rawPtr pointeeTy mut)`
   (`ptr::from_raw_parts(_mut)` / `ptr::slice_from_raw_parts(_mut)`), and
   decomposed 2-field `(data, meta)` tuple/aggregate `.field 0` / `.field 1`
   round-trips (plus negative UB / unsupported characterizations);
2. `core::intrinsics::size_of_val` (`size_of_val_raw`) and
   `core::intrinsics::align_of_val` (`align_of_val_raw`) value-level helpers on
   `[T]` (including `ZST` and empty slices), `str`, and sized `T`, with exact
   `isize` (`signedHalfModulus 8 = 2^63`) overflow, thin-pointer-on-DST, and
   pointer-width UB characterizations;
3. `writeIntrinsicReturn`, `evalTerminator`, `mirStep`, `wpMirBounded`, and
   `WpConverges` call-terminator lifters plus `Layout::for_value(_raw)`
   `(size, align)` tuple assembly;
4. General non-`select` intrinsic-call combinators, `stepMirFn`-level UB fault
   lifters, and sized `size_of_val` / `align_of_val` lifters;
5. `MirWpConverges` / `wpMirExecSym` step-transport combinators, provenance-free
   (integer-address) wide-pointer metadata & `AggregateKind.rawPtr` lifters, and
   remaining fail-closed characterizations;
6. `CastKind.ptrToPtr` on wide pointers (`ptr.cast()`, and rustc's actual MIR
   lowering of `<*const [T]>::to_raw_parts` via `CastKind.ptrToPtr` +
   `UnOp.ptrMetadata`, since MIR forbids `.field` projections on raw pointers).
-/

section UnsizedDstMetadataLifters

/-- `updateBorrowPerm` preserves `entry.tag`. -/
@[simp]
theorem updateBorrowPerm_tag (entry : BorrowEntry) (targetLocal : Local)
    (writerTag : Option Nat) (targetFrameDepth : Nat) :
    (updateBorrowPerm entry targetLocal writerTag targetFrameDepth).tag = entry.tag := by
  unfold updateBorrowPerm
  cases Bool.and (Nat.beq entry.targetFrameDepth targetFrameDepth)
      (Nat.beq entry.targetLocal targetLocal) with
  | false => rfl
  | true =>
    unfold applyTreeBorrowTransition
    cases treeBorrowNodeAccess .write (treeBorrowWriterRelatedness entry writerTag) entry.perm false <;> rfl

/-- `updateBorrowPerm` leaves `entry` unchanged when `entry.targetLocal ≠ targetLocal`
(constructive `Classical.choice`-free proof kept in `MirLiftCore` for the
constructive-axiom audit without importing `SepLogic`). -/
theorem updateBorrowPerm_eq_self_of_ne (entry : BorrowEntry) {targetLocal : Local}
    (writerTag : Option Nat) (targetFrameDepth : Nat) (hNe : entry.targetLocal ≠ targetLocal) :
    updateBorrowPerm entry targetLocal writerTag targetFrameDepth = entry := by
  have hBeq : Nat.beq entry.targetLocal targetLocal = false := by
    cases h : Nat.beq entry.targetLocal targetLocal with
    | false => rfl
    | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true h))
  unfold updateBorrowPerm
  rw [hBeq, Bool.and_false]

/-- `lookupBorrow` commutes with `invalidateConflictingBorrows`
(constructive `MirLiftCore`-local counterpart of `SepLogic`'s lemma). -/
theorem lookupBorrow_invalidateConflictingBorrows (borrows : List BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat) (targetFrameDepth tag : Nat) :
    lookupBorrow (invalidateConflictingBorrows borrows targetLocal writerTag targetFrameDepth) tag =
      (lookupBorrow borrows tag).map (fun e =>
        updateBorrowPerm e targetLocal writerTag targetFrameDepth) := by
  induction borrows with
  | nil => rfl
  | cons e rest ih =>
    unfold invalidateConflictingBorrows lookupBorrow
    rw [updateBorrowPerm_tag]
    cases Nat.beq e.tag tag with
    | true => rfl
    | false => exact ih

/-- Writing to a local `dstLoc ≠ entry.targetLocal` preserves `lookupBorrow borrows tag = some entry`
across `invalidateConflictingBorrows`. -/
theorem lookupBorrow_invalidateConflictingBorrows_of_ne {borrows : List BorrowEntry}
    {tag : Nat} {entry : BorrowEntry} {dstLoc : Local}
    (writerTag : Option Nat) (targetFrameDepth : Nat)
    (hLookup : lookupBorrow borrows tag = some entry) (hNe : entry.targetLocal ≠ dstLoc) :
    lookupBorrow (invalidateConflictingBorrows borrows dstLoc writerTag targetFrameDepth) tag =
      some entry := by
  rw [lookupBorrow_invalidateConflictingBorrows, hLookup, Option.map_some,
    updateBorrowPerm_eq_self_of_ne entry writerTag targetFrameDepth hNe]

/-- Writing to an unprojected local `dstLoc ≠ entry.targetLocal` preserves
`lookupBorrow mem.borrows tag = some entry` across `invalidateDirectDestWriteBorrows`. -/
theorem lookupBorrow_invalidateDirectDestWriteBorrows_of_ne (mem : Memory)
    (locals : List LocalSlot) {tag : Nat} {entry : BorrowEntry} {dstLoc : Local}
    (hLookup : lookupBorrow mem.borrows tag = some entry) (hNe : entry.targetLocal ≠ dstLoc) :
    lookupBorrow
      (invalidateDirectDestWriteBorrows mem locals { local_ := dstLoc, projection := [] }).borrows
      tag = some entry := by
  unfold invalidateDirectDestWriteBorrows
  cases hb : mem.borrows with
  | nil => rw [hb] at hLookup; cases hLookup
  | cons bHead bTail =>
    dsimp only
    rw [← hb]
    exact lookupBorrow_invalidateConflictingBorrows_of_ne .none (length mem.callStack) hLookup hNe

/-- When no entry in `borrows` targets `dstLoc`, `invalidateConflictingBorrows` is the identity. -/
theorem invalidateConflictingBorrows_eq_self_of_forall_ne :
    ∀ (borrows : List BorrowEntry) (dstLoc : Local) (writerTag : Option Nat)
      (targetFrameDepth : Nat),
      (∀ e ∈ borrows, e.targetLocal ≠ dstLoc) →
      invalidateConflictingBorrows borrows dstLoc writerTag targetFrameDepth = borrows
  | [], _, _, _, _ => rfl
  | e :: rest, dstLoc, writerTag, depth, hDisj => by
    unfold invalidateConflictingBorrows
    rw [updateBorrowPerm_eq_self_of_ne e writerTag depth (hDisj e (List.Mem.head _)),
      invalidateConflictingBorrows_eq_self_of_forall_ne rest dstLoc writerTag depth
        (fun b hb => hDisj b (List.Mem.tail _ hb))]

/-- When no entry in `mem.borrows` targets `dstLoc`, `invalidateDirectDestWriteBorrows` on
`{ local_ := dstLoc, projection := [] }` leaves `mem` identically unchanged. -/
theorem invalidateDirectDestWriteBorrows_eq_self_of_forall_ne (mem : Memory)
    (locals : List LocalSlot) (dstLoc : Local)
    (hDisj : ∀ e ∈ mem.borrows, e.targetLocal ≠ dstLoc) :
    invalidateDirectDestWriteBorrows mem locals { local_ := dstLoc, projection := [] } = mem := by
  unfold invalidateDirectDestWriteBorrows
  cases hb : mem.borrows with
  | nil => rfl
  | cons bHead bTail =>
    dsimp only
    have hEq :
        invalidateConflictingBorrows (bHead :: bTail) dstLoc .none (length mem.callStack) =
          bHead :: bTail :=
      invalidateConflictingBorrows_eq_self_of_forall_ne (bHead :: bTail) dstLoc .none
        (length mem.callStack) (by rw [← hb]; exact hDisj)
    rw [hEq, ← hb]

/-- `invalidateDirectDestWriteBorrows` only rewrites `borrows`: it is `{ mem with borrows := bs }`
for some `bs`, for every destination place. -/
theorem invalidateDirectDestWriteBorrows_eq_with_borrows (mem : Memory) (locals : List LocalSlot)
    (dst : Place) :
    ∃ bs, invalidateDirectDestWriteBorrows mem locals dst = { mem with borrows := bs } := by
  unfold invalidateDirectDestWriteBorrows
  cases mem.borrows with
  | nil => exact ⟨mem.borrows, rfl⟩
  | cons bHead bTail =>
    dsimp only
    cases dst.projection with
    | nil => exact ⟨_, rfl⟩
    | cons proj rest =>
      cases proj with
      | deref => exact ⟨mem.borrows, rfl⟩
      | _ => exact ⟨_, rfl⟩

@[simp]
theorem invalidateDirectDestWriteBorrows_globals (mem : Memory) (locals : List LocalSlot)
    (dst : Place) : (invalidateDirectDestWriteBorrows mem locals dst).globals = mem.globals := by
  obtain ⟨bs, h⟩ := invalidateDirectDestWriteBorrows_eq_with_borrows mem locals dst
  rw [h]

@[simp]
theorem invalidateDirectDestWriteBorrows_callerLocals (mem : Memory) (locals : List LocalSlot)
    (dst : Place) :
    (invalidateDirectDestWriteBorrows mem locals dst).callerLocals = mem.callerLocals := by
  obtain ⟨bs, h⟩ := invalidateDirectDestWriteBorrows_eq_with_borrows mem locals dst
  rw [h]

/-- When no entry of `borrows` targets `targetLocal`, `hasProtectedWriteConflict` reports no
conflict for any set of active protectors (e.g. writes to fresh MIR temporaries inside a
function whose `&mut` / `&` arguments carry `FnEntry` protectors). -/
theorem hasProtectedWriteConflict_eq_false_of_forall_ne :
    ∀ (borrows : List BorrowEntry) (activeProtectors : List Nat) (targetLocal : Local)
      (writerTag : Option Nat) (writeProj : List ProjectionElem)
      (writeRangeOff writeRangeLen targetFrameDepth : Nat),
      (∀ e ∈ borrows, e.targetLocal ≠ targetLocal) →
      hasProtectedWriteConflict borrows activeProtectors targetLocal writerTag writeProj
        writeRangeOff writeRangeLen targetFrameDepth = false
  | [], _, _, _, _, _, _, _, _ => rfl
  | e :: rest, prots, targetLocal, writerTag, writeProj, off, len, depth, hDisj => by
    have ih := hasProtectedWriteConflict_eq_false_of_forall_ne rest prots targetLocal writerTag
      writeProj off len depth (fun b hb => hDisj b (List.Mem.tail _ hb))
    have hBeq : Nat.beq e.targetLocal targetLocal = false := by
      cases hb : Nat.beq e.targetLocal targetLocal with
      | false => rfl
      | true => exact False.elim (hDisj e (List.Mem.head _) (Nat.eq_of_beq_eq_true hb))
    unfold hasProtectedWriteConflict
    simp only [hBeq, Bool.and_false, Bool.false_and]
    exact ih

/-! ### 1. `UnOp.ptrMetadata`, `AggregateKind.rawPtr`, and Decomposed `(data, meta)` Round-Trips -/

/-- **`evalRvalue_unaryOp_ptrMetadata_wide`**: `Rvalue.unaryOp .ptrMetadata op` on a wide pointer
`.aggregate 0 [.ptr p ptrBytes, .scalar ⟨len, ptrBytes⟩]` (`ptrBytes = layoutPointerBytes layouts`)
returns `.ok (.scalar ⟨len, ptrBytes⟩) locals' mem` without dereferencing or mutating `mem`. -/
theorem evalRvalue_unaryOp_ptrMetadata_wide (locals locals' : List LocalSlot) (op : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (len : Nat)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.ptr p (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals') :
    evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls layouts =
      .ok (.scalar ⟨len, layoutPointerBytes layouts⟩) locals' mem := by
  show evalUnaryPtrMetadata locals op mem localDecls layouts = _
  unfold evalUnaryPtrMetadata
  simp only [hOp, Nat.beq_refl, Bool.and_self]

/-- **`evalRvalue_unaryOp_ptrMetadata_thin`**: `Rvalue.unaryOp .ptrMetadata op` on a thin pointer
`.ptr p ptrBytes` (`ptrBytes = layoutPointerBytes layouts`) returns `.ok .unit locals' mem`. -/
theorem evalRvalue_unaryOp_ptrMetadata_thin (locals locals' : List LocalSlot) (op : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) (p : ProvenancePtr)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p (layoutPointerBytes layouts)) locals') :
    evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls layouts =
      .ok .unit locals' mem := by
  show evalUnaryPtrMetadata locals op mem localDecls layouts = _
  unfold evalUnaryPtrMetadata
  simp only [hOp, Nat.beq_refl]

/-- Negative: `Rvalue.unaryOp .ptrMetadata` faults with `.ub` when a wide pointer's data pointer
or metadata scalar byte width mismatches `layoutPointerBytes layouts`. -/
theorem evalRvalue_unaryOp_ptrMetadata_wide_width_mismatch_ub (locals locals' : List LocalSlot)
    (op : Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (ptrSz : Nat) (metaSc : ScalarInt)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.aggregate 0 [.ptr p ptrSz, .scalar metaSc]) locals')
    (hBad : Bool.and (Nat.beq ptrSz (layoutPointerBytes layouts))
      (Nat.beq metaSc.sizeBytes (layoutPointerBytes layouts)) = false) :
    evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls layouts = .ub := by
  show evalUnaryPtrMetadata locals op mem localDecls layouts = _
  unfold evalUnaryPtrMetadata
  simp only [hOp, hBad]

/-- Negative: `Rvalue.unaryOp .ptrMetadata` faults with `.ub` when a thin pointer's byte width
mismatches `layoutPointerBytes layouts`. -/
theorem evalRvalue_unaryOp_ptrMetadata_thin_width_mismatch_ub (locals locals' : List LocalSlot)
    (op : Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (ptrSz : Nat)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p ptrSz) locals')
    (hBad : Nat.beq ptrSz (layoutPointerBytes layouts) = false) :
    evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls layouts = .ub := by
  show evalUnaryPtrMetadata locals op mem localDecls layouts = _
  unfold evalUnaryPtrMetadata
  simp only [hOp, hBad]

/-- **`evalRvalue_aggregate_rawPtr_wide`**: `Rvalue.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]`
(`ptr::from_raw_parts` / `ptr::from_raw_parts_mut` / `ptr::slice_from_raw_parts(_mut)`) for any
non-`dyn` wide pointee (`wideAggregatePointeeIsDyn? pointeeTy = some false`, including `.slice elemTy`
and `.str`) assembles `.aggregate 0 [.ptr p ptrBytes, .scalar ⟨len, ptrBytes⟩]` with `mem` unchanged. -/
theorem evalRvalue_aggregate_rawPtr_wide (locals locals₁ locals₂ : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (dataOp metaOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (len : Nat)
    (hWide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p (layoutPointerBytes layouts)) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar ⟨len, layoutPointerBytes layouts⟩) locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]) mem
      localDecls layouts =
        .ok (.aggregate 0 [.ptr p (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals₂ mem := by
  show evalAggregateRawPtr locals pointeeTy [dataOp, metaOp] mem localDecls layouts = _
  unfold evalAggregateRawPtr evalOperands
  rw [hData]
  dsimp only [evalOperands]
  rw [hMeta]
  dsimp only [evalOperands]
  rw [hWide, Nat.beq_refl, Bool.and_self]

/-- **`evalRvalue_aggregate_rawPtr_slice`**: specialization of `evalRvalue_aggregate_rawPtr_wide`
to `.slice elemTy`. -/
theorem evalRvalue_aggregate_rawPtr_slice (locals locals₁ locals₂ : List LocalSlot)
    (elemTy : RigidTy) (lIdx : LayoutIdx) (mutability : Mutability) (dataOp metaOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (len : Nat)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p (layoutPointerBytes layouts)) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar ⟨len, layoutPointerBytes layouts⟩) locals₂) :
    evalRvalue locals
      (.aggregate (.rawPtr { kind := .slice elemTy, layoutIdx := lIdx } mutability) [dataOp, metaOp])
      mem localDecls layouts =
        .ok (.aggregate 0 [.ptr p (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals₂ mem :=
  evalRvalue_aggregate_rawPtr_wide locals locals₁ locals₂
    { kind := .slice elemTy, layoutIdx := lIdx } mutability dataOp metaOp mem localDecls layouts
    p len rfl hData hMeta

/-- **`evalRvalue_aggregate_rawPtr_str`**: specialization of `evalRvalue_aggregate_rawPtr_wide`
to `.str`. -/
theorem evalRvalue_aggregate_rawPtr_str (locals locals₁ locals₂ : List LocalSlot)
    (lIdx : LayoutIdx) (mutability : Mutability) (dataOp metaOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (len : Nat)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p (layoutPointerBytes layouts)) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar ⟨len, layoutPointerBytes layouts⟩) locals₂) :
    evalRvalue locals
      (.aggregate (.rawPtr { kind := .str, layoutIdx := lIdx } mutability) [dataOp, metaOp])
      mem localDecls layouts =
        .ok (.aggregate 0 [.ptr p (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals₂ mem :=
  evalRvalue_aggregate_rawPtr_wide locals locals₁ locals₂
    { kind := .str, layoutIdx := lIdx } mutability dataOp metaOp mem localDecls layouts
    p len rfl hData hMeta

/-- **`evalRvalue_aggregate_rawPtr_thin`**: `Rvalue.aggregate (.rawPtr pointeeTy mutability) [dataOp, unitOp]`
for a sized pointee (`isUnsizedRawPtrPointee pointeeTy = false`) and `.unit` metadata returns
`.ok (.ptr p ptrBytes) locals₂ mem`. -/
theorem evalRvalue_aggregate_rawPtr_thin (locals locals₁ locals₂ : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (dataOp unitOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr)
    (hSized : isUnsizedRawPtrPointee pointeeTy = false)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p (layoutPointerBytes layouts)) locals₁)
    (hUnit : evalOperand locals₁ unitOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok .unit locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, unitOp]) mem
      localDecls layouts = .ok (.ptr p (layoutPointerBytes layouts)) locals₂ mem := by
  show evalAggregateRawPtr locals pointeeTy [dataOp, unitOp] mem localDecls layouts = _
  unfold evalAggregateRawPtr evalOperands
  rw [hData]
  dsimp only [evalOperands]
  rw [hUnit]
  dsimp only [evalOperands]
  rw [hSized, Nat.beq_refl]

/-- Negative: passing scalar slice metadata `.scalar metaSc` to `AggregateKind.rawPtr` for a
sized primitive/array/pointer pointee (`wideAggregatePointeeIsDyn? pointeeTy = none`) faults with `.ub`. -/
theorem evalRvalue_aggregate_rawPtr_sized_wideMeta_ub (locals locals₁ locals₂ : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (dataOp metaOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (ptrSz : Nat) (metaSc : ScalarInt)
    (hSized : wideAggregatePointeeIsDyn? pointeeTy = none)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p ptrSz) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar metaSc) locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]) mem
      localDecls layouts = .ub := by
  show evalAggregateRawPtr locals pointeeTy [dataOp, metaOp] mem localDecls layouts = _
  unfold evalAggregateRawPtr evalOperands
  rw [hData]
  dsimp only [evalOperands]
  rw [hMeta]
  dsimp only [evalOperands]
  rw [hSized]

/-- Negative: passing `.unit` metadata to `AggregateKind.rawPtr` for an unsized pointee
(`isUnsizedRawPtrPointee pointeeTy = true`, e.g. `.slice _` or `.str`) faults with `.ub`. -/
theorem evalRvalue_aggregate_rawPtr_unsized_unitMeta_ub (locals locals₁ locals₂ : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (dataOp unitOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (ptrSz : Nat)
    (hUnsized : isUnsizedRawPtrPointee pointeeTy = true)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p ptrSz) locals₁)
    (hUnit : evalOperand locals₁ unitOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok .unit locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, unitOp]) mem
      localDecls layouts = .ub := by
  show evalAggregateRawPtr locals pointeeTy [dataOp, unitOp] mem localDecls layouts = _
  unfold evalAggregateRawPtr evalOperands
  rw [hData]
  dsimp only [evalOperands]
  rw [hUnit]
  dsimp only [evalOperands]
  rw [hUnsized]

/-- Negative: `AggregateKind.rawPtr` on a slice/str pointee faults with `.ub` when the data pointer
or metadata scalar byte width mismatches `layoutPointerBytes layouts`. -/
theorem evalRvalue_aggregate_rawPtr_wide_width_mismatch_ub (locals locals₁ locals₂ : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (dataOp metaOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (ptrSz : Nat) (metaSc : ScalarInt)
    (hWide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p ptrSz) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar metaSc) locals₂)
    (hBad : Bool.and (Nat.beq ptrSz (layoutPointerBytes layouts))
      (Nat.beq metaSc.sizeBytes (layoutPointerBytes layouts)) = false) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]) mem
      localDecls layouts = .ub := by
  show evalAggregateRawPtr locals pointeeTy [dataOp, metaOp] mem localDecls layouts = _
  unfold evalAggregateRawPtr evalOperands
  rw [hData]
  dsimp only [evalOperands]
  rw [hMeta]
  dsimp only [evalOperands]
  rw [hWide, hBad]

/-- Negative: `AggregateKind.rawPtr` with empty operand list `[]` fails closed
with `.unsupported`. -/
theorem evalRvalue_aggregate_rawPtr_nil_unsupported (locals : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) []) mem localDecls layouts =
      .unsupported := rfl

/-- **`evalOperand_copy_widePtr_field0`**: projecting `.field 0` (data component
of a decomposed 2-field `(data, meta)` aggregate in local `loc`) returns
`dataVal` with `locals` unchanged. (Rustc lowers `<*const [T]>::to_raw_parts`
to `CastKind.ptrToPtr` + `UnOp.ptrMetadata`; see §6.) -/
theorem evalOperand_copy_widePtr_field0 (locals : List LocalSlot) (loc : Local)
    (fTy : Ty) (dataVal metaVal : Value) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame)
    (hSlot : get? locals loc = some (.init (.aggregate 0 [dataVal, metaVal])))
    (hNoUnion : placeTouchesUnion localDecls layouts
      { local_ := loc, projection := [.field 0 fTy] } = false)
    (hNoUninit : valueContainsUninit dataVal = false := by rfl) :
    evalOperand locals (.copy { local_ := loc, projection := [.field 0 fTy] })
      borrows globals layouts callerLocals localDecls callStack = .ok dataVal locals := by
  unfold evalOperand
  dsimp only
  rw [hSlot, hNoUnion]
  simp only [readProjectedValue, get?, List.getElem?_cons_zero, hNoUninit]

/-- **`evalOperand_copy_widePtr_field1`**: projecting `.field 1` (metadata
component of a decomposed 2-field `(data, meta)` aggregate in local `loc`)
returns `metaVal` with `locals` unchanged. -/
theorem evalOperand_copy_widePtr_field1 (locals : List LocalSlot) (loc : Local)
    (fTy : Ty) (dataVal metaVal : Value) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame)
    (hSlot : get? locals loc = some (.init (.aggregate 0 [dataVal, metaVal])))
    (hNoUnion : placeTouchesUnion localDecls layouts
      { local_ := loc, projection := [.field 1 fTy] } = false)
    (hNoUninit : valueContainsUninit metaVal = false := by rfl) :
    evalOperand locals (.copy { local_ := loc, projection := [.field 1 fTy] })
      borrows globals layouts callerLocals localDecls callStack = .ok metaVal locals := by
  unfold evalOperand
  dsimp only
  rw [hSlot, hNoUnion]
  simp only [readProjectedValue, get?, List.getElem?_cons_succ, List.getElem?_cons_zero, hNoUninit]

/-- **`evalRvalue_aggregate_rawPtr_to_raw_parts_roundtrip`**: projecting
`.field 0` and `.field 1` from a decomposed 2-field `(data, meta)` aggregate
`.aggregate 0 [.ptr p ptrBytes, .scalar ⟨len, ptrBytes⟩]` at `loc` and
reassembling via `Rvalue.aggregate (.rawPtr pointeeTy mutability)` is the exact
identity on the wide-pointer value and preserves `locals` and `mem`. -/
theorem evalRvalue_aggregate_rawPtr_to_raw_parts_roundtrip (locals : List LocalSlot)
    (loc : Local) (pointeeTy dataTy metaTy : Ty) (mutability : Mutability)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (len : Nat)
    (hWide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hSlot : get? locals loc =
      some (.init (.aggregate 0 [.ptr p (layoutPointerBytes layouts),
        .scalar ⟨len, layoutPointerBytes layouts⟩])))
    (hNoUnion0 : placeTouchesUnion localDecls layouts
      { local_ := loc, projection := [.field 0 dataTy] } = false)
    (hNoUnion1 : placeTouchesUnion localDecls layouts
      { local_ := loc, projection := [.field 1 metaTy] } = false) :
    evalRvalue locals
      (.aggregate (.rawPtr pointeeTy mutability)
        [.copy { local_ := loc, projection := [.field 0 dataTy] },
         .copy { local_ := loc, projection := [.field 1 metaTy] }])
      mem localDecls layouts =
        .ok (.aggregate 0 [.ptr p (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals mem :=
  evalRvalue_aggregate_rawPtr_wide locals locals locals pointeeTy mutability
    (.copy { local_ := loc, projection := [.field 0 dataTy] })
    (.copy { local_ := loc, projection := [.field 1 metaTy] })
    mem localDecls layouts p len hWide
    (evalOperand_copy_widePtr_field0 locals loc dataTy _ _ mem.borrows mem.globals layouts
      mem.callerLocals localDecls mem.callStack hSlot hNoUnion0)
    (evalOperand_copy_widePtr_field1 locals loc metaTy _ _ mem.borrows mem.globals layouts
      mem.callerLocals localDecls mem.callStack hSlot hNoUnion1)

/-- **`evalRvalue_aggregate_tuple_pair`**: evaluating `Rvalue.aggregate .tuple [op0, op1]`
(such as `Layout::for_value(_raw)` `(size, align)` pair assembly) produces
`.ok (.aggregate 0 [v0, v1]) locals₂ mem`. -/
theorem evalRvalue_aggregate_tuple_pair (locals locals₁ locals₂ : List LocalSlot)
    (op0 op1 : Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v0 v1 : Value)
    (h0 : evalOperand locals op0 mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok v0 locals₁)
    (h1 : evalOperand locals₁ op1 mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok v1 locals₂) :
    evalRvalue locals (.aggregate .tuple [op0, op1]) mem localDecls layouts =
      .ok (.aggregate 0 [v0, v1]) locals₂ mem := by
  unfold evalRvalue evalOperands
  dsimp only []
  rw [h0]
  dsimp only [evalOperands]
  rw [h1]

/-! ### 2. `core::intrinsics::size_of_val` and `core::intrinsics::align_of_val` Lemmas -/

/-- `resolveIntrinsicPointeeTy?` resolves `pointeeTy` directly from `target.typeArgs = pointeeTy :: rest`. -/
@[simp]
theorem resolveIntrinsicPointeeTy?_of_typeArgs (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable) (argOps : List Operand)
    (pointeeTy : RigidTy) (rest : List RigidTy) (hArgs : target.typeArgs = pointeeTy :: rest) :
    resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some pointeeTy := by
  unfold resolveIntrinsicPointeeTy?
  rw [hArgs]

/-- `resolveIntrinsicPointeeTy?` resolves `pointeeTy` from `operandTy` of the first argument
(`*const T` / `*mut T`) when `target.typeArgs = []`. -/
theorem resolveIntrinsicPointeeTy?_of_rawPtr_operand (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (ptrOp : Operand) (restOps : List Operand)
    (mutability : Mutability) (pointeeTy : RigidTy) (lIdx : LayoutIdx)
    (hNoTypeArgs : target.typeArgs = [])
    (hOpTy : operandTy bodyLocalDecls bodyLayouts ptrOp =
      some { kind := .rawPtr mutability pointeeTy, layoutIdx := lIdx }) :
    resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts (ptrOp :: restOps) =
      some pointeeTy := by
  unfold resolveIntrinsicPointeeTy?
  rw [hNoTypeArgs]
  dsimp only
  rw [hOpTy]

/-- `resolveIntrinsicPointeeTy?` resolves `pointeeTy` from `operandTy` of the first argument
(`&T` / `&mut T`) when `target.typeArgs = []`. -/
theorem resolveIntrinsicPointeeTy?_of_ref_operand (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (ptrOp : Operand) (restOps : List Operand)
    (mutability : Mutability) (pointeeTy : RigidTy) (lIdx : LayoutIdx)
    (hNoTypeArgs : target.typeArgs = [])
    (hOpTy : operandTy bodyLocalDecls bodyLayouts ptrOp =
      some { kind := .ref mutability pointeeTy, layoutIdx := lIdx }) :
    resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts (ptrOp :: restOps) =
      some pointeeTy := by
  unfold resolveIntrinsicPointeeTy?
  rw [hNoTypeArgs]
  dsimp only
  rw [hOpTy]

private theorem signedHalfModulus_8_lt_scalarModulus_8 :
    signedHalfModulus 8 < scalarModulus 8 := by decide

private theorem nul_lt_signedHalfModulus_8 :
    0 < signedHalfModulus 8 := by decide

/-- Whenever `len * elemSz < signedHalfModulus 8`, `Nat.mul elemSz (wrapScalarBits len (scalarModulus 8))`
equals `len * elemSz` (covering both `elemSz = 0` for arbitrary `len` and `0 < elemSz` where
`len ≤ len * elemSz < signedHalfModulus 8 < scalarModulus 8`). -/
theorem elemSz_mul_wrapScalarBits_eq_of_lt_signedHalfModulus (elemSz len : Nat)
    (hLt : len * elemSz < signedHalfModulus 8) :
    Nat.mul elemSz (wrapScalarBits len (scalarModulus 8)) = len * elemSz := by
  cases elemSz with
  | zero =>
    change 0 * wrapScalarBits len (scalarModulus 8) = len * 0
    rw [Nat.zero_mul, Nat.mul_zero]
  | succ k =>
    have hLe : len ≤ len * (k + 1) := by
      have h1 : len * 1 ≤ len * (k + 1) := Nat.mul_le_mul_left len (Nat.le_add_left 1 k)
      rw [Nat.mul_one] at h1
      exact h1
    have hLenLt : len < scalarModulus 8 :=
      Nat.lt_trans (Nat.lt_of_le_of_lt hLe hLt) signedHalfModulus_8_lt_scalarModulus_8
    have hBle : Nat.ble (scalarModulus 8) len = false := by
      cases hb : Nat.ble (scalarModulus 8) len with
      | false => rfl
      | true => exact False.elim (Nat.not_le.mpr hLenLt (Nat.le_of_ble_eq_true hb))
    unfold wrapScalarBits
    rw [hBle]
    exact Nat.mul_comm (k + 1) len

/-- **`evalSliceSizeOfVal_eq_some`**: when `len * elemSz < signedHalfModulus 8` (`2^63`),
`evalSliceSizeOfVal elemSz ⟨len, 8⟩ = some ⟨len * elemSz, 8⟩`. -/
theorem evalSliceSizeOfVal_eq_some (elemSz len : Nat)
    (hLt : len * elemSz < signedHalfModulus 8) :
    evalSliceSizeOfVal elemSz ⟨len, 8⟩ = some ⟨len * elemSz, 8⟩ := by
  have hMul := elemSz_mul_wrapScalarBits_eq_of_lt_signedHalfModulus elemSz len hLt
  have hBle : Nat.ble (signedHalfModulus 8) (len * elemSz) = false := by
    cases hb : Nat.ble (signedHalfModulus 8) (len * elemSz) with
    | false => rfl
    | true => exact False.elim (Nat.not_le.mpr hLt (Nat.le_of_ble_eq_true hb))
  unfold evalSliceSizeOfVal
  dsimp only [Nat.beq_refl]
  rw [hMul, hBle]

/-- **`evalSliceSizeOfVal_zst`**: for a zero-sized element (`elemSz = 0`), `evalSliceSizeOfVal 0 ⟨len, 8⟩`
succeeds with `some ⟨0, 8⟩` for every `len : Nat`. -/
@[simp]
theorem evalSliceSizeOfVal_zst (len : Nat) :
    evalSliceSizeOfVal 0 ⟨len, 8⟩ = some ⟨0, 8⟩ := by
  have h := evalSliceSizeOfVal_eq_some 0 len (by rw [Nat.mul_zero]; exact nul_lt_signedHalfModulus_8)
  rw [Nat.mul_zero] at h
  exact h

/-- **`evalSliceSizeOfVal_empty`**: for an empty slice (`len = 0`), `evalSliceSizeOfVal elemSz ⟨0, 8⟩`
succeeds with `some ⟨0, 8⟩` for every `elemSz : Nat`. -/
@[simp]
theorem evalSliceSizeOfVal_empty (elemSz : Nat) :
    evalSliceSizeOfVal elemSz ⟨0, 8⟩ = some ⟨0, 8⟩ := by
  have h := evalSliceSizeOfVal_eq_some elemSz 0 (by rw [Nat.zero_mul]; exact nul_lt_signedHalfModulus_8)
  rw [Nat.zero_mul] at h
  exact h

/-- **`evalSliceSizeOfVal_eq_none_of_le`**: when `len < scalarModulus 8` (`2^64`) and
`signedHalfModulus 8 ≤ len * elemSz` (`isize` overflow, `≥ 2^63`), `evalSliceSizeOfVal elemSz ⟨len, 8⟩ = none`. -/
theorem evalSliceSizeOfVal_eq_none_of_le (elemSz len : Nat)
    (hLen : len < scalarModulus 8) (hGe : signedHalfModulus 8 ≤ len * elemSz) :
    evalSliceSizeOfVal elemSz ⟨len, 8⟩ = none := by
  have hBleLen : Nat.ble (scalarModulus 8) len = false := by
    cases hb : Nat.ble (scalarModulus 8) len with
    | false => rfl
    | true => exact False.elim (Nat.not_le.mpr hLen (Nat.le_of_ble_eq_true hb))
  have hWrap : wrapScalarBits len (scalarModulus 8) = len := by
    unfold wrapScalarBits
    rw [hBleLen]
  have hMul : Nat.mul elemSz len = len * elemSz := Nat.mul_comm elemSz len
  have hBleGe : Nat.ble (signedHalfModulus 8) (len * elemSz) = true :=
    Nat.ble_eq_true_of_le hGe
  unfold evalSliceSizeOfVal
  dsimp only [Nat.beq_refl]
  rw [hWrap, hMul, hBleGe]

/-- **`evalSliceSizeOfVal_eq_none_of_sizeBytes_ne`**: when `lenSc.sizeBytes ≠ 8`,
`evalSliceSizeOfVal elemSz lenSc = none`. -/
theorem evalSliceSizeOfVal_eq_none_of_sizeBytes_ne (elemSz : Nat) (lenSc : ScalarInt)
    (hNe : lenSc.sizeBytes ≠ 8) :
    evalSliceSizeOfVal elemSz lenSc = none := by
  have hBeq : Nat.beq lenSc.sizeBytes 8 = false := by
    cases hb : Nat.beq lenSc.sizeBytes 8 with
    | false => rfl
    | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hb))
  unfold evalSliceSizeOfVal
  rw [hBeq]

/-- **`evalNonSelectIntrinsicCall_sizeOfVal_slice`**: `size_of_val` on `.slice elemTy` with
`len * elemSz < signedHalfModulus 8` writes `.scalar ⟨len * elemSz, 8⟩` via `writeIntrinsicReturn`. -/
theorem evalNonSelectIntrinsicCall_sizeOfVal_slice (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (elemTy : RigidTy) (elemSz : Nat)
    (p : ProvenancePtr) (len : Nat)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some (.slice elemTy))
    (hSz : intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy = some elemSz)
    (hLt : len * elemSz < signedHalfModulus 8) :
    evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' destination targetBb =
      writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨len * elemSz, 8⟩) := by
  unfold evalNonSelectIntrinsicCall
  simp only [hPt, Nat.beq_refl, hSz, evalSliceSizeOfVal_eq_some elemSz len hLt,
    writeIntrinsicScalarResult]

/-- **`evalNonSelectIntrinsicCall_sizeOfVal_str`**: `size_of_val` on `.str` with
`len < signedHalfModulus 8` writes `.scalar ⟨len, 8⟩` via `writeIntrinsicReturn`. -/
theorem evalNonSelectIntrinsicCall_sizeOfVal_str (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (p : ProvenancePtr) (len : Nat)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some .str)
    (hLt : len < signedHalfModulus 8) :
    evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' destination targetBb =
      writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨len, 8⟩) := by
  have hLt1 : len * 1 < signedHalfModulus 8 := by rw [Nat.mul_one]; exact hLt
  have hEv := evalSliceSizeOfVal_eq_some 1 len hLt1
  rw [Nat.mul_one] at hEv
  unfold evalNonSelectIntrinsicCall
  simp only [hPt, Nat.beq_refl, hEv, writeIntrinsicScalarResult]

/-- **`evalNonSelectIntrinsicCall_sizeOfVal_sized`**: `size_of_val` on a sized `pointeeTy`
with a thin pointer `.ptr p 8` and `sz < signedHalfModulus 8` writes `.scalar ⟨sz, 8⟩`. -/
theorem evalNonSelectIntrinsicCall_sizeOfVal_sized (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (pointeeTy : RigidTy) (sz : Nat) (p : ProvenancePtr)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some pointeeTy)
    (hSized : isUnsizedRawPtrPointee { kind := pointeeTy, layoutIdx := 0 } = false)
    (hNoExt : intrinsicTailIsExtern 8 pointeeTy = false)
    (hSz : intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy = some sz)
    (hLt : sz < signedHalfModulus 8) :
    evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
      [.ptr p 8] locals' destination targetBb =
      writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨sz, 8⟩) := by
  have hBle : Nat.ble (signedHalfModulus 8) sz = false := by
    cases hb : Nat.ble (signedHalfModulus 8) sz with
    | false => rfl
    | true => exact False.elim (Nat.not_le.mpr hLt (Nat.le_of_ble_eq_true hb))
  have hEval :
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
        [.ptr p 8] locals' destination targetBb =
      (match intrinsicTailIsExtern 8 pointeeTy with
       | true => MirStepNode.unsupported
       | false =>
         match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
         | some sz =>
           match Nat.ble (signedHalfModulus 8) sz with
           | true => MirStepNode.fail .ub
           | false =>
             writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨sz, 8⟩)
         | none => intrinsicUnresolvedLayoutStep pointeeTy) := by
    unfold evalNonSelectIntrinsicCall
    dsimp only
    rw [hPt]
    cases pointeeTy <;> first | (cases hSized; done) | rfl
  rw [hEval, hNoExt]
  dsimp only
  rw [hSz]
  dsimp only
  rw [hBle]

/-- **`evalNonSelectIntrinsicCall_alignOfVal_slice`**: `align_of_val` on `.slice elemTy` with
`len * elemSz < signedHalfModulus 8` writes `.scalar ⟨alignBytes, 8⟩` via `writeIntrinsicReturn`. -/
theorem evalNonSelectIntrinsicCall_alignOfVal_slice (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (elemTy : RigidTy) (elemSz alignBytes : Nat)
    (p : ProvenancePtr) (len : Nat)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some (.slice elemTy))
    (hSz : intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy = some elemSz)
    (hAlign : intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy = some alignBytes)
    (hLt : len * elemSz < signedHalfModulus 8) :
    evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' destination targetBb =
      writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨alignBytes, 8⟩) := by
  unfold evalNonSelectIntrinsicCall
  simp only [hPt, Nat.beq_refl, hSz, hAlign, evalSliceSizeOfVal_eq_some elemSz len hLt]

/-- **`evalNonSelectIntrinsicCall_alignOfVal_str`**: `align_of_val` on `.str` with
`len < signedHalfModulus 8` writes `.scalar ⟨1, 8⟩` via `writeIntrinsicReturn`. -/
theorem evalNonSelectIntrinsicCall_alignOfVal_str (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (p : ProvenancePtr) (len : Nat)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some .str)
    (hLt : len < signedHalfModulus 8) :
    evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' destination targetBb =
      writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 8⟩) := by
  have hLt1 : len * 1 < signedHalfModulus 8 := by rw [Nat.mul_one]; exact hLt
  unfold evalNonSelectIntrinsicCall
  simp only [hPt, Nat.beq_refl, evalSliceSizeOfVal_eq_some 1 len hLt1]

/-- **`evalNonSelectIntrinsicCall_alignOfVal_sized`**: `align_of_val` on a sized `pointeeTy`
with a thin pointer `.ptr p 8` writes `.scalar ⟨alignBytes, 8⟩`. -/
theorem evalNonSelectIntrinsicCall_alignOfVal_sized (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (pointeeTy : RigidTy) (alignBytes : Nat) (p : ProvenancePtr)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some pointeeTy)
    (hSized : isUnsizedRawPtrPointee { kind := pointeeTy, layoutIdx := 0 } = false)
    (hNoExt : intrinsicTailIsExtern 8 pointeeTy = false)
    (hAlign : intrinsicRigidTyAlign bodyLocalDecls bodyLayouts pointeeTy = some alignBytes) :
    evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
      [.ptr p 8] locals' destination targetBb =
      writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨alignBytes, 8⟩) := by
  have hEval :
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
        [.ptr p 8] locals' destination targetBb =
      (match intrinsicTailIsExtern 8 pointeeTy with
       | true => MirStepNode.unsupported
       | false =>
         match intrinsicRigidTyAlign bodyLocalDecls bodyLayouts pointeeTy with
         | some alignBytes =>
           writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨alignBytes, 8⟩)
         | none => intrinsicUnresolvedLayoutStep pointeeTy) := by
    unfold evalNonSelectIntrinsicCall
    dsimp only
    rw [hPt]
    cases pointeeTy <;> first | (cases hSized; done) | rfl
  rw [hEval, hNoExt]
  dsimp only
  rw [hAlign]

/-- **UB Characterization (`size_of_val` `isize` overflow on `[T]`)**: when
`signedHalfModulus 8 ≤ len * elemSz` (`len < scalarModulus 8`), `size_of_val` faults with `.fail .ub`. -/
theorem evalNonSelectIntrinsicCall_sizeOfVal_slice_overflow_ub (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (elemTy : RigidTy) (elemSz : Nat)
    (p : ProvenancePtr) (len : Nat)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some (.slice elemTy))
    (hSz : intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy = some elemSz)
    (hLen : len < scalarModulus 8)
    (hGe : signedHalfModulus 8 ≤ len * elemSz) :
    evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' destination targetBb =
      MirStepNode.fail .ub := by
  unfold evalNonSelectIntrinsicCall
  simp only [hPt, Nat.beq_refl, hSz, evalSliceSizeOfVal_eq_none_of_le elemSz len hLen hGe,
    writeIntrinsicScalarResult]

/-- **UB Characterization (`align_of_val` `isize` overflow on `[T]`)**: `align_of_val` enforces
the exact same `signedHalfModulus 8` (`2^63`) slice byte-size bound and faults with `.fail .ub`
when `signedHalfModulus 8 ≤ len * elemSz` (`len < scalarModulus 8`). -/
theorem evalNonSelectIntrinsicCall_alignOfVal_slice_overflow_ub (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (elemTy : RigidTy) (elemSz alignBytes : Nat)
    (p : ProvenancePtr) (len : Nat)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some (.slice elemTy))
    (hSz : intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy = some elemSz)
    (hAlign : intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy = some alignBytes)
    (hLen : len < scalarModulus 8)
    (hGe : signedHalfModulus 8 ≤ len * elemSz) :
    evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' destination targetBb =
      MirStepNode.fail .ub := by
  unfold evalNonSelectIntrinsicCall
  simp only [hPt, Nat.beq_refl, hSz, hAlign, evalSliceSizeOfVal_eq_none_of_le elemSz len hLen hGe]

/-- **UB Characterization (`size_of_val` `isize` overflow on `str`)**: when
`signedHalfModulus 8 ≤ len` (`len < scalarModulus 8`), `size_of_val` on `str` faults with `.fail .ub`. -/
theorem evalNonSelectIntrinsicCall_sizeOfVal_str_overflow_ub (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (p : ProvenancePtr) (len : Nat)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some .str)
    (hLen : len < scalarModulus 8)
    (hGe : signedHalfModulus 8 ≤ len) :
    evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' destination targetBb =
      MirStepNode.fail .ub := by
  have hGe1 : signedHalfModulus 8 ≤ len * 1 := by rw [Nat.mul_one]; exact hGe
  unfold evalNonSelectIntrinsicCall
  simp only [hPt, Nat.beq_refl, evalSliceSizeOfVal_eq_none_of_le 1 len hLen hGe1,
    writeIntrinsicScalarResult]

/-- **UB Characterization (`align_of_val` `isize` overflow on `str`)**: when
`signedHalfModulus 8 ≤ len` (`len < scalarModulus 8`), `align_of_val` on `str` faults with `.fail .ub`. -/
theorem evalNonSelectIntrinsicCall_alignOfVal_str_overflow_ub (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (p : ProvenancePtr) (len : Nat)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some .str)
    (hLen : len < scalarModulus 8)
    (hGe : signedHalfModulus 8 ≤ len) :
    evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' destination targetBb =
      MirStepNode.fail .ub := by
  have hGe1 : signedHalfModulus 8 ≤ len * 1 := by rw [Nat.mul_one]; exact hGe
  unfold evalNonSelectIntrinsicCall
  simp only [hPt, Nat.beq_refl, evalSliceSizeOfVal_eq_none_of_le 1 len hLen hGe1]

/-- **UB Characterization (thin pointer passed for unsized `.slice elemTy` or `.str`)**: passing
`.ptr p ptrSz` to `size_of_val` or `align_of_val` when the pointee is `.slice elemTy` or `.str`
faults with `.fail .ub`. -/
theorem evalNonSelectIntrinsicCall_unsized_thinPtr_ub (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (elemTy : RigidTy) (p : ProvenancePtr) (ptrSz : Nat) :
    (resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some (.slice elemTy) →
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
        [.ptr p ptrSz] locals' destination targetBb = MirStepNode.fail .ub ∧
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
        [.ptr p ptrSz] locals' destination targetBb = MirStepNode.fail .ub) ∧
    (resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some .str →
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
        [.ptr p ptrSz] locals' destination targetBb = MirStepNode.fail .ub ∧
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
        [.ptr p ptrSz] locals' destination targetBb = MirStepNode.fail .ub) := by
  refine ⟨fun hSl => ⟨by unfold evalNonSelectIntrinsicCall; simp only [hSl],
                      by unfold evalNonSelectIntrinsicCall; simp only [hSl]⟩,
          fun hStr => ⟨by unfold evalNonSelectIntrinsicCall; simp only [hStr],
                       by unfold evalNonSelectIntrinsicCall; simp only [hStr]⟩⟩

/-- **UB Characterization (`ptrSz ≠ 8` on `.slice elemTy`)**: non-64-bit pointer width faults with
`.fail .ub` in both `size_of_val` and `align_of_val`. -/
theorem evalNonSelectIntrinsicCall_slice_ptrSz_ne_ub (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (elemTy : RigidTy) (p : ProvenancePtr) (ptrSz : Nat) (lenSc : ScalarInt)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some (.slice elemTy))
    (hNe : ptrSz ≠ 8) :
    evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p ptrSz, .scalar lenSc]] locals' destination targetBb =
        MirStepNode.fail .ub ∧
    evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p ptrSz, .scalar lenSc]] locals' destination targetBb =
        MirStepNode.fail .ub := by
  have hBeq : Nat.beq ptrSz 8 = false := by
    cases hb : Nat.beq ptrSz 8 with
    | false => rfl
    | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hb))
  refine ⟨?_, ?_⟩ <;> (unfold evalNonSelectIntrinsicCall; simp only [hPt, hBeq])

/-! ### 3. `writeIntrinsicReturn`, `evalTerminator`, `mirStep`, `wpMirBounded`, & `WpConverges` Lifters -/

/-- `writeIntrinsicReturn` reduction for an unprojected destination local `{ local_ := dstLoc, projection := [] }`. -/
theorem writeIntrinsicReturn_local (s : MachineState) (locals' updatedLocals : List LocalSlot)
    (dstLoc : Local) (slot : LocalSlot) (targetBb : BasicBlockIdx) (retVal : Value)
    (hSlot : get? locals' dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals' dstLoc (.init retVal) = some updatedLocals) :
    writeIntrinsicReturn s locals' { local_ := dstLoc, projection := [] } targetBb retVal =
      MirStepNode.step {
        frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
        memory :=
          invalidateDirectDestWriteBorrows s.memory locals' { local_ := dstLoc, projection := [] }
      } := by
  unfold writeIntrinsicReturn writePlaceValue
  dsimp only []
  rw [hSlot]
  cases slot with
  | dead => cases hLive
  | uninit => dsimp only []; rw [hSet]
  | init _ => dsimp only []; rw [hSet]

-- Constructive (`Classical.choice`-free) copies of call-target and frame-terminator
-- helpers so all declarations in `UnsizedDstMetadataLifters` pass the constructive
-- `run_cmd` axiom audit.
private theorem resolveCallTarget_of_extractCallee_constructive (s : MachineState) (func : Operand)
    (argCount : Nat) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (defPath : DefPath) (typeArgs : List RigidTy)
    (hCallee : extractCallee? func = some (defPath, typeArgs)) :
    resolveCallTarget s func argCount bodyLocalDecls bodyLayouts =
      .ok { defPath := defPath, typeArgs := typeArgs, fnSig := none, isIndirect := false }
        s.frame.locals := by
  unfold extractCallee? at hCallee
  cases hp : extractCalleeDefPath? func with
  | none => rw [hp] at hCallee; cases hCallee
  | some p =>
    rw [hp] at hCallee
    injection hCallee with hPair
    injection hPair with hDp hArgs
    subst hDp hArgs
    unfold resolveCallTarget
    rw [hp]

private theorem get?_eq_none_of_eq_length {α : Type} :
    ∀ (xs : List α) (i : Nat), i = length xs → get? xs i = none
  | [], _, rfl => rfl
  | _ :: tl, _, rfl => get?_eq_none_of_eq_length tl (length tl) rfl

private theorem cond_true_eq {α : Type} {b : Bool} {t e : α} (hb : b = true) :
    (if b = true then t else e) = t := by
  cases b with
  | true => rfl
  | false => cases hb

private theorem stepMirFn_frame_term_constructive {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements) :
    stepMirFn body s = evalTerminator s blk.terminator (some cur) := by
  have hNone : get? blk.statements s.frame.stmtIdx = none :=
    get?_eq_none_of_eq_length blk.statements s.frame.stmtIdx hEnd
  have hBeq : (s.frame.stmtIdx == length blk.statements) = true := by
    rw [hEnd]
    exact decide_eq_true rfl
  unfold stepMirFn
  rw [hCur]
  dsimp only []
  rcases hPhase with hp | hp <;>
    (rw [hp]; dsimp only []; rw [hBb]; dsimp only []; rw [hNone]; dsimp only [];
     exact cond_true_eq hBeq)

/-- General `evalTerminator` reduction for a direct call to any non-`const_eval_select` compiler
intrinsic (`size_of_val`, `align_of_val`, `arith_offset`, etc.) when no override exists in
`s.memory.callees`. -/
theorem evalTerminator_call_nonSelectIntrinsic (s : MachineState) (cur : CapturedMir)
    (func : Operand) (argOps : List Operand) (destination : Place)
    (targetBb : BasicBlockIdx) (unwind : UnwindAction) (span : String)
    (defPath : DefPath) (typeArgs : List RigidTy) (kind : RustIntrinsicKind)
    (argVals : List Value) (locals' : List LocalSlot)
    (hCallee : extractCallee? func = some (defPath, typeArgs))
    (hArgs : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) = .ok argVals locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts defPath typeArgs
      s.memory.traitImpls = none)
    (hNoExact :
      isDirectExactDivTarget
        { defPath := defPath, typeArgs := typeArgs, fnSig := none, isIndirect := false } = false)
    (hKind : classifyRustIntrinsic? defPath = some kind)
    (hNonSelect : isNonSelectIntrinsicOpt (some kind) = true)
    (hNotMem : kind ≠ .copyNonOverlapping ∧ kind ≠ .writeBytes := by constructor <;> intro h <;> cases h) :
    evalTerminator s
      { kind := .call func argOps destination (some targetBb) unwind, span := span }
      (some cur) =
      evalNonSelectIntrinsicCall kind s
        { defPath := defPath, typeArgs := typeArgs, fnSig := none, isIndirect := false }
        cur.localDecls cur.layouts argOps argVals locals' destination targetBb := by
  have hRes := resolveCallTarget_of_extractCallee_constructive s func (length argOps)
    cur.localDecls cur.layouts defPath typeArgs hCallee
  unfold evalTerminator
  dsimp only [bodyLocalDeclsOf]
  rw [hRes]
  dsimp only []
  rw [hArgs]
  dsimp only []
  rw [hNoOverride]
  dsimp only []
  rw [hNoExact]
  dsimp only [evalDirectRustIntrinsic?]
  rw [hKind]
  cases kind with
  | constEvalSelect => cases hNonSelect
  | copyNonOverlapping => exact False.elim (hNotMem.1 rfl)
  | writeBytes => exact False.elim (hNotMem.2 rfl)
  | _ => rfl

/-- One-step `stepMirFn` / `mirStep` / `wpMirBounded` / `WpConverges` bridge from any
`stepMirFn body s = MirStepNode.step s'` transition. -/
theorem mirStep_and_wp_of_stepMirFn_step {body : CapturedMir} {s s' : MachineState}
    (hStep : stepMirFn body s = MirStepNode.step s') :
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) := by
  have hMirStep : mirStep body s = .cont s' := by
    unfold mirStep
    rw [hStep]
    rfl
  refine ⟨hMirStep, ?_, fun post hConv => WpConverges.of_cont hMirStep hConv⟩
  intro fuel post
  have hL :
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post =
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post := by
    unfold Anneal.Rustc.V2026_06_01.Lower.wpMirBounded
    conv =>
      lhs
      unfold Anneal.ITreeWP.wpCoalBounded
      dsimp only [stepMirState]
    rw [hStep]
    rfl
  rw [hL]

/-- **`mirStep_assign_local`**: composable single-step lifter for `StatementKind.assign` into an
unprojected local `{ local_ := dstLoc, projection := [] }`, yielding `stepMirFn`, `mirStep`,
`wpMirBounded`, and `WpConverges` transitions in one rule.

The protector side condition is exactly the trusted one: the write must not conflict with a
protected borrow (`hasProtectedWriteConflict ... = false`). It holds for any write when no
protectors are active (`hasProtectedWriteConflict_nil`) and for writes to locals no
borrow targets (`hasProtectedWriteConflict_eq_false_of_forall_ne`), so the lifter also applies
inside callees whose reference arguments carry `FnEntry` protectors. -/
theorem mirStep_assign_local {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {dstLoc : Local} {rv : Rvalue} {span : String}
    {val : Value} {locals₁ locals₂ : List LocalSlot} {mem₁ : Memory} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hStmt : get? blk.statements s.frame.stmtIdx =
      some { kind := .assign { local_ := dstLoc, projection := [] } rv, span := span })
    (hRv : evalRvalue s.frame.locals rv s.memory cur.localDecls cur.layouts = .ok val locals₁ mem₁)
    (hProt : hasProtectedWriteConflict mem₁.borrows mem₁.activeProtectors dstLoc .none .nil 0 0
      (length mem₁.callStack) = false)
    (hSlot : get? locals₁ dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals₁ dstLoc (.init val) = some locals₂) :
    let s' : MachineState :=
      { frame := { blockIdx := s.frame.blockIdx, stmtIdx := s.frame.stmtIdx + 1, locals := locals₂ }
        memory := { mem₁ with
          borrows := invalidateConflictingBorrows mem₁.borrows dstLoc .none (length mem₁.callStack) } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) := by
  intro s'
  have hStepStmt := stepMirFn_frame_stmt hCur hPhase hBb hStmt
  have hEv :
      evalStmt s { kind := .assign { local_ := dstLoc, projection := [] } rv, span := span }
        cur.localDecls cur.layouts = MirStepNode.step s' := by
    unfold evalStmt
    dsimp only []
    rw [hRv]
    dsimp only []
    rw [hSlot]
    cases slot with
    | dead => cases hLive
    | uninit =>
      dsimp only []
      rw [hSet]
      dsimp only []
      unfold s'
      cases hP : mem₁.activeProtectors with
      | nil =>
        rcases s with ⟨⟨bb, stIdx, locs⟩, mem⟩
        rfl
      | cons ph pt =>
        rw [hP] at hProt
        dsimp only []
        rw [hProt]
        rcases s with ⟨⟨bb, stIdx, locs⟩, mem⟩
        rfl
    | init _ =>
      dsimp only []
      rw [hSet]
      dsimp only []
      unfold s'
      cases hP : mem₁.activeProtectors with
      | nil =>
        rcases s with ⟨⟨bb, stIdx, locs⟩, mem⟩
        rfl
      | cons ph pt =>
        rw [hP] at hProt
        dsimp only []
        rw [hProt]
        rcases s with ⟨⟨bb, stIdx, locs⟩, mem⟩
        rfl
  have hStep : stepMirFn body s = MirStepNode.step s' := hStepStmt.trans hEv
  obtain ⟨hMir, hWp, hConv⟩ := mirStep_and_wp_of_stepMirFn_step hStep
  exact ⟨hStep, hMir, hWp, hConv⟩

/-- **`mirStep_assign_ptrMetadata_wide`**: one-step lifter for `dstLoc = PtrMetadata(op)` on a
wide pointer `.aggregate 0 [.ptr p ptrBytes, .scalar ⟨len, ptrBytes⟩]`. -/
theorem mirStep_assign_ptrMetadata_wide {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {dstLoc : Local} {op : Operand} {span : String}
    {p : ProvenancePtr} {len : Nat} {locals₁ locals₂ : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hStmt : get? blk.statements s.frame.stmtIdx =
      some { kind := .assign { local_ := dstLoc, projection := [] } (.unaryOp .ptrMetadata op),
             span := span })
    (hOp : evalOperand s.frame.locals op s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals cur.localDecls s.memory.callStack =
        .ok (.aggregate 0 [.ptr p (layoutPointerBytes cur.layouts),
          .scalar ⟨len, layoutPointerBytes cur.layouts⟩]) locals₁)
    (hProt : hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors dstLoc .none
      .nil 0 0 (length s.memory.callStack) = false)
    (hSlot : get? locals₁ dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals₁ dstLoc (.init (.scalar ⟨len, layoutPointerBytes cur.layouts⟩)) =
      some locals₂) :
    let s' : MachineState :=
      { frame := { blockIdx := s.frame.blockIdx, stmtIdx := s.frame.stmtIdx + 1, locals := locals₂ }
        memory := { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none
            (length s.memory.callStack) } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) :=
  mirStep_assign_local hCur hPhase hBb hStmt
    (evalRvalue_unaryOp_ptrMetadata_wide s.frame.locals locals₁ op s.memory cur.localDecls
      cur.layouts p len hOp)
    hProt hSlot hLive hSet

/-- **`mirStep_assign_aggregate_rawPtr_wide`**: one-step lifter for
`dstLoc = AggregateKind.rawPtr pointeeTy mutability [dataOp, metaOp]` (`ptr::from_raw_parts(_mut)`). -/
theorem mirStep_assign_aggregate_rawPtr_wide {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {dstLoc : Local} {pointeeTy : Ty} {mutability : Mutability}
    {dataOp metaOp : Operand} {span : String}
    {p : ProvenancePtr} {len : Nat} {locals₁ locals₂ locals₃ : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hStmt : get? blk.statements s.frame.stmtIdx =
      some { kind := .assign { local_ := dstLoc, projection := [] }
               (.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]),
             span := span })
    (hWide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hData : evalOperand s.frame.locals dataOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals cur.localDecls s.memory.callStack =
        .ok (.ptr p (layoutPointerBytes cur.layouts)) locals₁)
    (hMeta : evalOperand locals₁ metaOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals cur.localDecls s.memory.callStack =
        .ok (.scalar ⟨len, layoutPointerBytes cur.layouts⟩) locals₂)
    (hProt : hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors dstLoc .none
      .nil 0 0 (length s.memory.callStack) = false)
    (hSlot : get? locals₂ dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals₂ dstLoc
      (.init (.aggregate 0 [.ptr p (layoutPointerBytes cur.layouts),
        .scalar ⟨len, layoutPointerBytes cur.layouts⟩])) = some locals₃) :
    let s' : MachineState :=
      { frame := { blockIdx := s.frame.blockIdx, stmtIdx := s.frame.stmtIdx + 1, locals := locals₃ }
        memory := { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none
            (length s.memory.callStack) } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) :=
  mirStep_assign_local hCur hPhase hBb hStmt
    (evalRvalue_aggregate_rawPtr_wide s.frame.locals locals₁ locals₂ pointeeTy mutability
      dataOp metaOp s.memory cur.localDecls cur.layouts p len hWide hData hMeta)
    hProt hSlot hLive hSet

/-- **`mirStep_assign_layout_tuple`**: one-step lifter for `Layout::for_value(_raw)` `(size, align)`
tuple assembly `dstLoc = (sizeOp, alignOp)`. -/
theorem mirStep_assign_layout_tuple {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {dstLoc : Local} {sizeOp alignOp : Operand} {span : String}
    {vSize vAlign : Value} {locals₁ locals₂ locals₃ : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hStmt : get? blk.statements s.frame.stmtIdx =
      some { kind := .assign { local_ := dstLoc, projection := [] }
               (.aggregate .tuple [sizeOp, alignOp]),
             span := span })
    (hSize : evalOperand s.frame.locals sizeOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals cur.localDecls s.memory.callStack = .ok vSize locals₁)
    (hAlign : evalOperand locals₁ alignOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals cur.localDecls s.memory.callStack = .ok vAlign locals₂)
    (hProt : hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors dstLoc .none
      .nil 0 0 (length s.memory.callStack) = false)
    (hSlot : get? locals₂ dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals₂ dstLoc (.init (.aggregate 0 [vSize, vAlign])) = some locals₃) :
    let s' : MachineState :=
      { frame := { blockIdx := s.frame.blockIdx, stmtIdx := s.frame.stmtIdx + 1, locals := locals₃ }
        memory := { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none
            (length s.memory.callStack) } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) :=
  mirStep_assign_local hCur hPhase hBb hStmt
    (evalRvalue_aggregate_tuple_pair s.frame.locals locals₁ locals₂ sizeOp alignOp s.memory
      cur.localDecls cur.layouts vSize vAlign hSize hAlign)
    hProt hSlot hLive hSet

/-- **`mirStep_call_sizeOfVal_slice`**: one-step terminator lifter for a `TerminatorKind.call` to
`core::intrinsics::size_of_val` on `.slice elemTy` (`len * elemSz < signedHalfModulus 8`). -/
theorem mirStep_call_sizeOfVal_slice {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {dstLoc : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {elemTy : RigidTy} {elemSz : Nat}
    {p : ProvenancePtr} {len : Nat} {locals' updatedLocals : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] { local_ := dstLoc, projection := [] } (some targetBb) unwind,
        span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::size_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::size_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some (.slice elemTy))
    (hSz : intrinsicRigidTyByteSize cur.localDecls cur.layouts elemTy = some elemSz)
    (hLt : len * elemSz < signedHalfModulus 8)
    (hSlot : get? locals' dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals' dstLoc (.init (.scalar ⟨len * elemSz, 8⟩)) = some updatedLocals) :
    let s' : MachineState :=
      { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
        memory :=
          invalidateDirectDestWriteBorrows s.memory locals' { local_ := dstLoc, projection := [] } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) := by
  intro s'
  have hStepTerm := stepMirFn_frame_term_constructive hCur hPhase hBb hEnd
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hEvTerm := evalTerminator_call_nonSelectIntrinsic s cur func [ptrOp]
    { local_ := dstLoc, projection := [] } targetBb unwind span
    "core::intrinsics::size_of_val" typeArgs .sizeOfVal
    [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals'
    hCallee hArgs hNoOverride rfl rfl rfl
  have hEvIntr := evalNonSelectIntrinsicCall_sizeOfVal_slice s
    { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
      isIndirect := false }
    cur.localDecls cur.layouts [ptrOp] locals' { local_ := dstLoc, projection := [] }
    targetBb elemTy elemSz p len hPt hSz hLt
  have hWr := writeIntrinsicReturn_local s locals' updatedLocals dstLoc slot targetBb
    (.scalar ⟨len * elemSz, 8⟩) hSlot hLive hSet
  have hStep : stepMirFn body s = MirStepNode.step s' := by
    rw [hStepTerm, hTerm, hEvTerm, hEvIntr, hWr]
  obtain ⟨hMir, hWp, hConv⟩ := mirStep_and_wp_of_stepMirFn_step hStep
  exact ⟨hStep, hMir, hWp, hConv⟩

/-- **`mirStep_call_sizeOfVal_str`**: one-step terminator lifter for a `TerminatorKind.call` to
`core::intrinsics::size_of_val` on `.str` (`len < signedHalfModulus 8`). -/
theorem mirStep_call_sizeOfVal_str {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {dstLoc : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {p : ProvenancePtr} {len : Nat}
    {locals' updatedLocals : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] { local_ := dstLoc, projection := [] } (some targetBb) unwind,
        span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::size_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::size_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some .str)
    (hLt : len < signedHalfModulus 8)
    (hSlot : get? locals' dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals' dstLoc (.init (.scalar ⟨len, 8⟩)) = some updatedLocals) :
    let s' : MachineState :=
      { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
        memory :=
          invalidateDirectDestWriteBorrows s.memory locals' { local_ := dstLoc, projection := [] } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) := by
  intro s'
  have hStepTerm := stepMirFn_frame_term_constructive hCur hPhase hBb hEnd
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hEvTerm := evalTerminator_call_nonSelectIntrinsic s cur func [ptrOp]
    { local_ := dstLoc, projection := [] } targetBb unwind span
    "core::intrinsics::size_of_val" typeArgs .sizeOfVal
    [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals'
    hCallee hArgs hNoOverride rfl rfl rfl
  have hEvIntr := evalNonSelectIntrinsicCall_sizeOfVal_str s
    { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
      isIndirect := false }
    cur.localDecls cur.layouts [ptrOp] locals' { local_ := dstLoc, projection := [] }
    targetBb p len hPt hLt
  have hWr := writeIntrinsicReturn_local s locals' updatedLocals dstLoc slot targetBb
    (.scalar ⟨len, 8⟩) hSlot hLive hSet
  have hStep : stepMirFn body s = MirStepNode.step s' := by
    rw [hStepTerm, hTerm, hEvTerm, hEvIntr, hWr]
  obtain ⟨hMir, hWp, hConv⟩ := mirStep_and_wp_of_stepMirFn_step hStep
  exact ⟨hStep, hMir, hWp, hConv⟩

/-- **`mirStep_call_alignOfVal_slice`**: one-step terminator lifter for a `TerminatorKind.call` to
`core::intrinsics::align_of_val` on `.slice elemTy` (`len * elemSz < signedHalfModulus 8`). -/
theorem mirStep_call_alignOfVal_slice {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {dstLoc : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {elemTy : RigidTy} {elemSz alignBytes : Nat}
    {p : ProvenancePtr} {len : Nat} {locals' updatedLocals : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] { local_ := dstLoc, projection := [] } (some targetBb) unwind,
        span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::align_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::align_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some (.slice elemTy))
    (hSz : intrinsicRigidTyByteSize cur.localDecls cur.layouts elemTy = some elemSz)
    (hAlign : intrinsicRigidTyAlign cur.localDecls cur.layouts elemTy = some alignBytes)
    (hLt : len * elemSz < signedHalfModulus 8)
    (hSlot : get? locals' dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals' dstLoc (.init (.scalar ⟨alignBytes, 8⟩)) = some updatedLocals) :
    let s' : MachineState :=
      { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
        memory :=
          invalidateDirectDestWriteBorrows s.memory locals' { local_ := dstLoc, projection := [] } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) := by
  intro s'
  have hStepTerm := stepMirFn_frame_term_constructive hCur hPhase hBb hEnd
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hEvTerm := evalTerminator_call_nonSelectIntrinsic s cur func [ptrOp]
    { local_ := dstLoc, projection := [] } targetBb unwind span
    "core::intrinsics::align_of_val" typeArgs .alignOfVal
    [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals'
    hCallee hArgs hNoOverride rfl rfl rfl
  have hEvIntr := evalNonSelectIntrinsicCall_alignOfVal_slice s
    { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
      isIndirect := false }
    cur.localDecls cur.layouts [ptrOp] locals' { local_ := dstLoc, projection := [] }
    targetBb elemTy elemSz alignBytes p len hPt hSz hAlign hLt
  have hWr := writeIntrinsicReturn_local s locals' updatedLocals dstLoc slot targetBb
    (.scalar ⟨alignBytes, 8⟩) hSlot hLive hSet
  have hStep : stepMirFn body s = MirStepNode.step s' := by
    rw [hStepTerm, hTerm, hEvTerm, hEvIntr, hWr]
  obtain ⟨hMir, hWp, hConv⟩ := mirStep_and_wp_of_stepMirFn_step hStep
  exact ⟨hStep, hMir, hWp, hConv⟩

/-- **`mirStep_call_alignOfVal_str`**: one-step terminator lifter for a `TerminatorKind.call` to
`core::intrinsics::align_of_val` on `.str` (`len < signedHalfModulus 8`). -/
theorem mirStep_call_alignOfVal_str {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {dstLoc : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {p : ProvenancePtr} {len : Nat}
    {locals' updatedLocals : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] { local_ := dstLoc, projection := [] } (some targetBb) unwind,
        span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::align_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::align_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some .str)
    (hLt : len < signedHalfModulus 8)
    (hSlot : get? locals' dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals' dstLoc (.init (.scalar ⟨1, 8⟩)) = some updatedLocals) :
    let s' : MachineState :=
      { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
        memory :=
          invalidateDirectDestWriteBorrows s.memory locals' { local_ := dstLoc, projection := [] } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) := by
  intro s'
  have hStepTerm := stepMirFn_frame_term_constructive hCur hPhase hBb hEnd
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hEvTerm := evalTerminator_call_nonSelectIntrinsic s cur func [ptrOp]
    { local_ := dstLoc, projection := [] } targetBb unwind span
    "core::intrinsics::align_of_val" typeArgs .alignOfVal
    [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals'
    hCallee hArgs hNoOverride rfl rfl rfl
  have hEvIntr := evalNonSelectIntrinsicCall_alignOfVal_str s
    { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
      isIndirect := false }
    cur.localDecls cur.layouts [ptrOp] locals' { local_ := dstLoc, projection := [] }
    targetBb p len hPt hLt
  have hWr := writeIntrinsicReturn_local s locals' updatedLocals dstLoc slot targetBb
    (.scalar ⟨1, 8⟩) hSlot hLive hSet
  have hStep : stepMirFn body s = MirStepNode.step s' := by
    rw [hStepTerm, hTerm, hEvTerm, hEvIntr, hWr]
  obtain ⟨hMir, hWp, hConv⟩ := mirStep_and_wp_of_stepMirFn_step hStep
  exact ⟨hStep, hMir, hWp, hConv⟩

/-! ### 4. General Intrinsic-Call Combinators, `stepMirFn`-Level UB Faults, and Sized Lifters -/

/-- **`stepMirFn_call_nonSelectIntrinsic`**: at a block terminator, a direct
`TerminatorKind.call` to any non-`const_eval_select` compiler intrinsic with no
`s.memory.callees` override steps exactly as `evalNonSelectIntrinsicCall`, so every
intrinsic-level lemma (positive or `.ub`) lifts to `stepMirFn` by one rewrite. -/
theorem stepMirFn_call_nonSelectIntrinsic {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func : Operand} {argOps : List Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {defPath : DefPath} {typeArgs : List RigidTy} {kind : RustIntrinsicKind}
    {argVals : List Value} {locals' : List LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func argOps destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some (defPath, typeArgs))
    (hArgs : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) = .ok argVals locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts defPath typeArgs
      s.memory.traitImpls = none)
    (hNoExact :
      isDirectExactDivTarget
        { defPath := defPath, typeArgs := typeArgs, fnSig := none, isIndirect := false } = false)
    (hKind : classifyRustIntrinsic? defPath = some kind)
    (hNonSelect : isNonSelectIntrinsicOpt (some kind) = true)
    (hNotMem : kind ≠ .copyNonOverlapping ∧ kind ≠ .writeBytes := by constructor <;> intro h <;> cases h) :
    stepMirFn body s =
      evalNonSelectIntrinsicCall kind s
        { defPath := defPath, typeArgs := typeArgs, fnSig := none, isIndirect := false }
        cur.localDecls cur.layouts argOps argVals locals' destination targetBb := by
  rw [stepMirFn_frame_term_constructive hCur hPhase hBb hEnd, hTerm]
  exact evalTerminator_call_nonSelectIntrinsic s cur func argOps destination targetBb unwind span
    defPath typeArgs kind argVals locals' hCallee hArgs hNoOverride hNoExact hKind hNonSelect
    hNotMem

/-- A `MirStepNode.fail fk` trusted step is a `mirStep` `.fault`. -/
theorem mirStep_of_stepMirFn_fail {body : CapturedMir} {s : MachineState} {fk : FailureKind}
    (h : stepMirFn body s = MirStepNode.fail fk) : mirStep body s = .fault := by
  unfold mirStep
  rw [h]
  rfl

/-- **`mirStep_call_nonSelectIntrinsic_fail`**: an intrinsic-level fault
(`evalNonSelectIntrinsicCall ... = MirStepNode.fail fk`) at a block terminator is a `stepMirFn`
fault and a `mirStep` `.fault`. -/
theorem mirStep_call_nonSelectIntrinsic_fail {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func : Operand} {argOps : List Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {defPath : DefPath} {typeArgs : List RigidTy} {kind : RustIntrinsicKind}
    {argVals : List Value} {locals' : List LocalSlot} {fk : FailureKind}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func argOps destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some (defPath, typeArgs))
    (hArgs : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) = .ok argVals locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts defPath typeArgs
      s.memory.traitImpls = none)
    (hNoExact :
      isDirectExactDivTarget
        { defPath := defPath, typeArgs := typeArgs, fnSig := none, isIndirect := false } = false)
    (hKind : classifyRustIntrinsic? defPath = some kind)
    (hNonSelect : isNonSelectIntrinsicOpt (some kind) = true)
    (hFail : evalNonSelectIntrinsicCall kind s
        { defPath := defPath, typeArgs := typeArgs, fnSig := none, isIndirect := false }
        cur.localDecls cur.layouts argOps argVals locals' destination targetBb =
      MirStepNode.fail fk)
    (hNotMem : kind ≠ .copyNonOverlapping ∧ kind ≠ .writeBytes := by constructor <;> intro h <;> cases h) :
    stepMirFn body s = MirStepNode.fail fk ∧ mirStep body s = .fault := by
  have hStep : stepMirFn body s = MirStepNode.fail fk :=
    (stepMirFn_call_nonSelectIntrinsic hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
      hNoExact hKind hNonSelect hNotMem).trans hFail
  exact ⟨hStep, mirStep_of_stepMirFn_fail hStep⟩

/-- **`mirStep_call_nonSelectIntrinsic_write_local`**: an intrinsic-level return write
(`evalNonSelectIntrinsicCall ... = writeIntrinsicReturn s locals' dst targetBb retVal`) into a
live unprojected local steps `stepMirFn` / `mirStep` / `wpMirBounded` / `WpConverges`. -/
theorem mirStep_call_nonSelectIntrinsic_write_local {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func : Operand} {argOps : List Operand} {dstLoc : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {defPath : DefPath} {typeArgs : List RigidTy} {kind : RustIntrinsicKind}
    {argVals : List Value} {retVal : Value} {locals' updatedLocals : List LocalSlot}
    {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func argOps { local_ := dstLoc, projection := [] } (some targetBb) unwind,
        span := span })
    (hCallee : extractCallee? func = some (defPath, typeArgs))
    (hArgs : evalOperands s.frame.locals argOps s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) = .ok argVals locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts defPath typeArgs
      s.memory.traitImpls = none)
    (hNoExact :
      isDirectExactDivTarget
        { defPath := defPath, typeArgs := typeArgs, fnSig := none, isIndirect := false } = false)
    (hKind : classifyRustIntrinsic? defPath = some kind)
    (hNonSelect : isNonSelectIntrinsicOpt (some kind) = true)
    (hEval : evalNonSelectIntrinsicCall kind s
        { defPath := defPath, typeArgs := typeArgs, fnSig := none, isIndirect := false }
        cur.localDecls cur.layouts argOps argVals locals' { local_ := dstLoc, projection := [] }
        targetBb =
      writeIntrinsicReturn s locals' { local_ := dstLoc, projection := [] } targetBb retVal)
    (hSlot : get? locals' dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals' dstLoc (.init retVal) = some updatedLocals)
    (hNotMem : kind ≠ .copyNonOverlapping ∧ kind ≠ .writeBytes := by constructor <;> intro h <;> cases h) :
    let s' : MachineState :=
      { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
        memory :=
          invalidateDirectDestWriteBorrows s.memory locals' { local_ := dstLoc, projection := [] } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) := by
  intro s'
  have hStep : stepMirFn body s = MirStepNode.step s' := by
    rw [stepMirFn_call_nonSelectIntrinsic hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
      hNoExact hKind hNonSelect hNotMem, hEval,
      writeIntrinsicReturn_local s locals' updatedLocals dstLoc slot targetBb retVal hSlot hLive
        hSet]
  obtain ⟨hMir, hWp, hConv⟩ := mirStep_and_wp_of_stepMirFn_step hStep
  exact ⟨hStep, hMir, hWp, hConv⟩

/-- **`mirStep_call_sizeOfVal_sized`**: one-step terminator lifter for
`core::intrinsics::size_of_val` on a sized pointee (thin pointer `.ptr p 8`, non-`extern` tail,
`sz < signedHalfModulus 8`), resolved via `typeArgs` or the `operandTy` fallback. -/
theorem mirStep_call_sizeOfVal_sized {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {dstLoc : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {pointeeTy : RigidTy} {sz : Nat}
    {p : ProvenancePtr} {locals' updatedLocals : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] { local_ := dstLoc, projection := [] } (some targetBb) unwind,
        span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::size_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack = .ok (.ptr p 8) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::size_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some pointeeTy)
    (hSized : isUnsizedRawPtrPointee { kind := pointeeTy, layoutIdx := 0 } = false)
    (hNoExt : intrinsicTailIsExtern 8 pointeeTy = false)
    (hSz : intrinsicRigidTyByteSize cur.localDecls cur.layouts pointeeTy = some sz)
    (hLt : sz < signedHalfModulus 8)
    (hSlot : get? locals' dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals' dstLoc (.init (.scalar ⟨sz, 8⟩)) = some updatedLocals) :
    let s' : MachineState :=
      { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
        memory :=
          invalidateDirectDestWriteBorrows s.memory locals' { local_ := dstLoc, projection := [] } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) = .ok [.ptr p 8] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  exact mirStep_call_nonSelectIntrinsic_write_local hCur hPhase hBb hEnd hTerm hCallee hArgs
    hNoOverride rfl rfl rfl
    (evalNonSelectIntrinsicCall_sizeOfVal_sized s _ cur.localDecls cur.layouts [ptrOp] locals'
      { local_ := dstLoc, projection := [] } targetBb pointeeTy sz p hPt hSized hNoExt hSz hLt)
    hSlot hLive hSet

/-- **`mirStep_call_alignOfVal_sized`**: one-step terminator lifter for
`core::intrinsics::align_of_val` on a sized pointee (thin pointer `.ptr p 8`, non-`extern`
tail). -/
theorem mirStep_call_alignOfVal_sized {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {dstLoc : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {pointeeTy : RigidTy} {alignBytes : Nat}
    {p : ProvenancePtr} {locals' updatedLocals : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] { local_ := dstLoc, projection := [] } (some targetBb) unwind,
        span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::align_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack = .ok (.ptr p 8) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::align_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some pointeeTy)
    (hSized : isUnsizedRawPtrPointee { kind := pointeeTy, layoutIdx := 0 } = false)
    (hNoExt : intrinsicTailIsExtern 8 pointeeTy = false)
    (hAlign : intrinsicRigidTyAlign cur.localDecls cur.layouts pointeeTy = some alignBytes)
    (hSlot : get? locals' dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals' dstLoc (.init (.scalar ⟨alignBytes, 8⟩)) = some updatedLocals) :
    let s' : MachineState :=
      { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
        memory :=
          invalidateDirectDestWriteBorrows s.memory locals' { local_ := dstLoc, projection := [] } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) = .ok [.ptr p 8] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  exact mirStep_call_nonSelectIntrinsic_write_local hCur hPhase hBb hEnd hTerm hCallee hArgs
    hNoOverride rfl rfl rfl
    (evalNonSelectIntrinsicCall_alignOfVal_sized s _ cur.localDecls cur.layouts [ptrOp] locals'
      { local_ := dstLoc, projection := [] } targetBb pointeeTy alignBytes p hPt hSized hNoExt
      hAlign)
    hSlot hLive hSet

/-- **`mirStep_call_sizeOfVal_slice_overflow_ub`** (`stepMirFn`-level exact `isize` boundary):
`size_of_val::<[T]>` on `.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]` with
`signedHalfModulus 8 ≤ len * elemSz` (`len < 2^64`) steps to `MirStepNode.fail .ub`
(`mirStep` `.fault`), for any destination place. -/
theorem mirStep_call_sizeOfVal_slice_overflow_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {elemTy : RigidTy} {elemSz : Nat}
    {p : ProvenancePtr} {len : Nat} {locals' : List LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::size_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::size_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some (.slice elemTy))
    (hSz : intrinsicRigidTyByteSize cur.localDecls cur.layouts elemTy = some elemSz)
    (hLen : len < scalarModulus 8)
    (hGe : signedHalfModulus 8 ≤ len * elemSz) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl
    (evalNonSelectIntrinsicCall_sizeOfVal_slice_overflow_ub s _ cur.localDecls cur.layouts [ptrOp]
      locals' destination targetBb elemTy elemSz p len hPt hSz hLen hGe)

/-- **`mirStep_call_alignOfVal_slice_overflow_ub`** (`stepMirFn`-level exact `isize` boundary):
`align_of_val::<[T]>` enforces the same `signedHalfModulus 8` slice byte-size bound and steps to
`MirStepNode.fail .ub` (`mirStep` `.fault`) when `signedHalfModulus 8 ≤ len * elemSz`. -/
theorem mirStep_call_alignOfVal_slice_overflow_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {elemTy : RigidTy} {elemSz alignBytes : Nat}
    {p : ProvenancePtr} {len : Nat} {locals' : List LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::align_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::align_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some (.slice elemTy))
    (hSz : intrinsicRigidTyByteSize cur.localDecls cur.layouts elemTy = some elemSz)
    (hAlign : intrinsicRigidTyAlign cur.localDecls cur.layouts elemTy = some alignBytes)
    (hLen : len < scalarModulus 8)
    (hGe : signedHalfModulus 8 ≤ len * elemSz) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl
    (evalNonSelectIntrinsicCall_alignOfVal_slice_overflow_ub s _ cur.localDecls cur.layouts
      [ptrOp] locals' destination targetBb elemTy elemSz alignBytes p len hPt hSz hAlign hLen hGe)

/-- **`mirStep_call_sizeOfVal_unsized_thinPtr_ub`** (`stepMirFn`-level): passing a thin pointer
`.ptr p ptrSz` to `size_of_val` for an unsized `.slice elemTy` or `.str` pointee steps to
`MirStepNode.fail .ub` (`mirStep` `.fault`). -/
theorem mirStep_call_sizeOfVal_unsized_thinPtr_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {dstTy : RigidTy}
    {p : ProvenancePtr} {ptrSz : Nat} {locals' : List LocalSlot}
    (hDstTy : (∃ elemTy, dstTy = .slice elemTy) ∨ dstTy = .str)
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::size_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack = .ok (.ptr p ptrSz) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::size_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some dstTy) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) = .ok [.ptr p ptrSz] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hThin := evalNonSelectIntrinsicCall_unsized_thinPtr_ub s
    { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
      isIndirect := false }
    cur.localDecls cur.layouts [ptrOp] locals' destination targetBb
  have hFail : evalNonSelectIntrinsicCall .sizeOfVal s
      { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] [.ptr p ptrSz] locals' destination targetBb =
      MirStepNode.fail .ub := by
    rcases hDstTy with ⟨elemTy, rfl⟩ | rfl
    · exact ((hThin elemTy p ptrSz).1 hPt).1
    · exact ((hThin (.tuple []) p ptrSz).2 hPt).1
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl hFail

/-- **`mirStep_assign_ptrMetadata_thin`**: one-step lifter for `dstLoc = PtrMetadata(op)` on a
thin pointer `.ptr p (layoutPointerBytes cur.layouts)`, writing `.unit` to `dstLoc`. -/
theorem mirStep_assign_ptrMetadata_thin {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {dstLoc : Local} {op : Operand} {span : String}
    {p : ProvenancePtr} {locals₁ locals₂ : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hStmt : get? blk.statements s.frame.stmtIdx =
      some { kind := .assign { local_ := dstLoc, projection := [] } (.unaryOp .ptrMetadata op),
             span := span })
    (hOp : evalOperand s.frame.locals op s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals cur.localDecls s.memory.callStack =
        .ok (.ptr p (layoutPointerBytes cur.layouts)) locals₁)
    (hProt : hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors dstLoc .none
      .nil 0 0 (length s.memory.callStack) = false)
    (hSlot : get? locals₁ dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals₁ dstLoc (.init .unit) = some locals₂) :
    let s' : MachineState :=
      { frame := { blockIdx := s.frame.blockIdx, stmtIdx := s.frame.stmtIdx + 1, locals := locals₂ }
        memory := { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none
            (length s.memory.callStack) } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) :=
  mirStep_assign_local hCur hPhase hBb hStmt
    (evalRvalue_unaryOp_ptrMetadata_thin s.frame.locals locals₁ op s.memory cur.localDecls
      cur.layouts p hOp)
    hProt hSlot hLive hSet

/-- **`mirStep_assign_aggregate_rawPtr_thin`**: one-step lifter for
`dstLoc = AggregateKind.rawPtr pointeeTy mutability [dataOp, unitOp]` (`ptr::from_raw_parts(_mut)`
for a sized `pointeeTy` with `.unit` metadata). -/
theorem mirStep_assign_aggregate_rawPtr_thin {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {dstLoc : Local} {pointeeTy : Ty} {mutability : Mutability}
    {dataOp unitOp : Operand} {span : String}
    {p : ProvenancePtr} {locals₁ locals₂ locals₃ : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hStmt : get? blk.statements s.frame.stmtIdx =
      some { kind := .assign { local_ := dstLoc, projection := [] }
               (.aggregate (.rawPtr pointeeTy mutability) [dataOp, unitOp]),
             span := span })
    (hSized : isUnsizedRawPtrPointee pointeeTy = false)
    (hData : evalOperand s.frame.locals dataOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals cur.localDecls s.memory.callStack =
        .ok (.ptr p (layoutPointerBytes cur.layouts)) locals₁)
    (hUnit : evalOperand locals₁ unitOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals cur.localDecls s.memory.callStack = .ok .unit locals₂)
    (hProt : hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors dstLoc .none
      .nil 0 0 (length s.memory.callStack) = false)
    (hSlot : get? locals₂ dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals₂ dstLoc (.init (.ptr p (layoutPointerBytes cur.layouts))) = some locals₃) :
    let s' : MachineState :=
      { frame := { blockIdx := s.frame.blockIdx, stmtIdx := s.frame.stmtIdx + 1, locals := locals₃ }
        memory := { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none
            (length s.memory.callStack) } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) :=
  mirStep_assign_local hCur hPhase hBb hStmt
    (evalRvalue_aggregate_rawPtr_thin s.frame.locals locals₁ locals₂ pointeeTy mutability
      dataOp unitOp s.memory cur.localDecls cur.layouts p hSized hData hUnit)
    hProt hSlot hLive hSet

/-- **`mirStep_call_sizeOfVal_str_overflow_ub`** (`stepMirFn`-level exact `isize` boundary on `str`):
`size_of_val::<str>` on `.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]` with
`signedHalfModulus 8 ≤ len` (`len < 2^64`) steps to `MirStepNode.fail .ub` (`mirStep` `.fault`). -/
theorem mirStep_call_sizeOfVal_str_overflow_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {p : ProvenancePtr} {len : Nat} {locals' : List LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::size_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::size_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some .str)
    (hLen : len < scalarModulus 8)
    (hGe : signedHalfModulus 8 ≤ len) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl
    (evalNonSelectIntrinsicCall_sizeOfVal_str_overflow_ub s _ cur.localDecls cur.layouts [ptrOp]
      locals' destination targetBb p len hPt hLen hGe)

/-- **`mirStep_call_alignOfVal_str_overflow_ub`** (`stepMirFn`-level exact `isize` boundary on `str`):
`align_of_val::<str>` on `.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]` with
`signedHalfModulus 8 ≤ len` (`len < 2^64`) steps to `MirStepNode.fail .ub` (`mirStep` `.fault`). -/
theorem mirStep_call_alignOfVal_str_overflow_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {p : ProvenancePtr} {len : Nat} {locals' : List LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::align_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::align_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some .str)
    (hLen : len < scalarModulus 8)
    (hGe : signedHalfModulus 8 ≤ len) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl
    (evalNonSelectIntrinsicCall_alignOfVal_str_overflow_ub s _ cur.localDecls cur.layouts [ptrOp]
      locals' destination targetBb p len hPt hLen hGe)

/-- **`mirStep_call_alignOfVal_unsized_thinPtr_ub`** (`stepMirFn`-level): passing a thin pointer
`.ptr p ptrSz` to `align_of_val` for an unsized `.slice elemTy` or `.str` pointee steps to
`MirStepNode.fail .ub` (`mirStep` `.fault`). -/
theorem mirStep_call_alignOfVal_unsized_thinPtr_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {dstTy : RigidTy}
    {p : ProvenancePtr} {ptrSz : Nat} {locals' : List LocalSlot}
    (hDstTy : (∃ elemTy, dstTy = .slice elemTy) ∨ dstTy = .str)
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::align_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack = .ok (.ptr p ptrSz) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::align_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some dstTy) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) = .ok [.ptr p ptrSz] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hThin := evalNonSelectIntrinsicCall_unsized_thinPtr_ub s
    { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
      isIndirect := false }
    cur.localDecls cur.layouts [ptrOp] locals' destination targetBb
  have hFail : evalNonSelectIntrinsicCall .alignOfVal s
      { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] [.ptr p ptrSz] locals' destination targetBb =
      MirStepNode.fail .ub := by
    rcases hDstTy with ⟨elemTy, rfl⟩ | rfl
    · exact ((hThin elemTy p ptrSz).1 hPt).2
    · exact ((hThin (.tuple []) p ptrSz).2 hPt).2
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl hFail

/-- **`mirStep_call_sizeOfVal_slice_ptrSz_ne_ub`** (`stepMirFn`-level non-64-bit `ptrSz ≠ 8` fault):
`size_of_val::<[T]>` on `.aggregate 0 [.ptr p ptrSz, .scalar lenSc]` with `ptrSz ≠ 8` steps to
`MirStepNode.fail .ub` (`mirStep` `.fault`). -/
theorem mirStep_call_sizeOfVal_slice_ptrSz_ne_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {elemTy : RigidTy}
    {p : ProvenancePtr} {ptrSz : Nat} {lenSc : ScalarInt} {locals' : List LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::size_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p ptrSz, .scalar lenSc]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::size_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some (.slice elemTy))
    (hNe : ptrSz ≠ 8) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p ptrSz, .scalar lenSc]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hFail := (evalNonSelectIntrinsicCall_slice_ptrSz_ne_ub s _ cur.localDecls cur.layouts [ptrOp]
    locals' destination targetBb elemTy p ptrSz lenSc hPt hNe).1
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl hFail

/-- **`mirStep_call_alignOfVal_slice_ptrSz_ne_ub`** (`stepMirFn`-level non-64-bit `ptrSz ≠ 8` fault):
`align_of_val::<[T]>` on `.aggregate 0 [.ptr p ptrSz, .scalar lenSc]` with `ptrSz ≠ 8` steps to
`MirStepNode.fail .ub` (`mirStep` `.fault`). -/
theorem mirStep_call_alignOfVal_slice_ptrSz_ne_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {elemTy : RigidTy}
    {p : ProvenancePtr} {ptrSz : Nat} {lenSc : ScalarInt} {locals' : List LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::align_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p ptrSz, .scalar lenSc]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::align_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some (.slice elemTy))
    (hNe : ptrSz ≠ 8) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p ptrSz, .scalar lenSc]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hFail := (evalNonSelectIntrinsicCall_slice_ptrSz_ne_ub s _ cur.localDecls cur.layouts [ptrOp]
    locals' destination targetBb elemTy p ptrSz lenSc hPt hNe).2
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl hFail

/-! ### 5. `MirWpConverges` / `wpMirExecSym` Combinators, Provenance-Free Wide Pointers, and
Remaining Fail-Closed Characterizations -/

/-- **`mirWpConverges_of_stepMirFn_step`**: a silent trusted step `stepMirFn body s = .step s'`
transports fuel-free `MirWpConverges` backwards from `s'` to `s` and shifts bounded symbolic
`wpMirExecSym` fuel by exactly one, so every `stepMirFn` lifter in this section composes into
`MirWpConverges` / `wpMirExecSym` obligations without evaluating `wpMirSym` by computation. -/
theorem mirWpConverges_of_stepMirFn_step {body : CapturedMir} {s s' : MachineState}
    (hStep : stepMirFn body s = MirStepNode.step s') :
    (∀ post, Anneal.MirFuelFree.MirWpConverges body s' post →
      Anneal.MirFuelFree.MirWpConverges body s post) ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym (fuel + 1) body (.running s) post ↔
        Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body (.running s') post) := by
  refine ⟨fun post h => Anneal.MirFuelFree.MirWpConverges.step_tau hStep h, ?_⟩
  intro fuel post
  have key : ∀ (k : MirExecState → Prop) (post' : MirOutcome → Prop),
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTree k post'
          (Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree body (.running s)) ↔
        k (.running s') := by
    intro k post'
    rw [Anneal.Rustc.V2026_06_01.SymbolicEval.evalSymNodeTree_eq,
      Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirExecSymTree_eval,
      Anneal.Rustc.V2026_06_01.SymbolicEval.evalNodeWP_eq]
    dsimp only [stepMirState]
    rw [hStep]
    exact Iff.rfl
  exact key (fun st' => Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body st' post) post

/-- **`evalRvalue_unaryOp_ptrMetadata_wide_scalarAddr`**: `Rvalue.unaryOp .ptrMetadata op` on a
provenance-free wide pointer `.aggregate 0 [.scalar addrSc, .scalar metaSc]` (the trusted
representation of `ptr::slice_from_raw_parts(ptr::null(), len)` /
`NonNull::slice_from_raw_parts(NonNull::dangling(), len)`, whose data pointer is an integer
address) returns the wrapped length `.scalar ⟨metaSc.bits mod 2^(8·ptrBytes), ptrBytes⟩` with
`mem` unchanged, provided the operand is not statically typed as a non-wide aggregate. -/
theorem evalRvalue_unaryOp_ptrMetadata_wide_scalarAddr (locals locals' : List LocalSlot)
    (op : Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (addr len : Nat)
    (hTy : isNonWidePtrAggregateTy (operandTy localDecls layouts op) = false)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.scalar ⟨addr, layoutPointerBytes layouts⟩,
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals') :
    evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls layouts =
      .ok (.scalar ⟨wrapScalarBits len (scalarModulus (layoutPointerBytes layouts)),
        layoutPointerBytes layouts⟩) locals' mem := by
  show evalUnaryPtrMetadata locals op mem localDecls layouts = _
  unfold evalUnaryPtrMetadata
  simp only [hOp, hTy, Nat.beq_refl, Bool.and_self]

/-- **`evalRvalue_aggregate_rawPtr_wide_scalarAddr`**: `AggregateKind.rawPtr` on a non-`dyn`
wide pointee (`[T]` / `str`) from a provenance-free integer address `.scalar ⟨addr, ptrBytes⟩`
and length `.scalar ⟨len, ptrBytes⟩` (`ptr::slice_from_raw_parts(ptr::null(), len)`) assembles
the wrapped provenance-free wide pointer with `mem` unchanged. -/
theorem evalRvalue_aggregate_rawPtr_wide_scalarAddr (locals locals₁ locals₂ : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (dataOp metaOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) (addr len : Nat)
    (hWide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar ⟨addr, layoutPointerBytes layouts⟩) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar ⟨len, layoutPointerBytes layouts⟩) locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]) mem
      localDecls layouts =
        .ok (.aggregate 0
          [.scalar ⟨wrapScalarBits addr (scalarModulus (layoutPointerBytes layouts)),
             layoutPointerBytes layouts⟩,
           .scalar ⟨wrapScalarBits len (scalarModulus (layoutPointerBytes layouts)),
             layoutPointerBytes layouts⟩]) locals₂ mem := by
  show evalAggregateRawPtr locals pointeeTy [dataOp, metaOp] mem localDecls layouts = _
  unfold evalAggregateRawPtr evalOperands
  rw [hData]
  dsimp only [evalOperands]
  rw [hMeta]
  dsimp only [evalOperands]
  rw [hWide, Nat.beq_refl, Bool.and_self]

/-- **Fail-closed (trusted limitation)**: `size_of_val` and `align_of_val` on `[T]` / `str` only
accept wide pointers whose data component is a provenance-carrying `.ptr _ 8`; a provenance-free
wide pointer `.aggregate 0 [.scalar addrSc, .scalar lenSc]` (e.g. a dangling empty slice built
from `NonNull::dangling()`) faults with `MirStepNode.fail .ub` even for `len = 0`, although
`UnOp.ptrMetadata` accepts it (`evalRvalue_unaryOp_ptrMetadata_wide_scalarAddr`). -/
theorem evalNonSelectIntrinsicCall_unsized_scalarAddr_ub (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (dstTy : RigidTy) (addrSc lenSc : ScalarInt)
    (hDstTy : (∃ elemTy, dstTy = .slice elemTy) ∨ dstTy = .str)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some dstTy) :
    evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
        [.aggregate 0 [.scalar addrSc, .scalar lenSc]] locals' destination targetBb =
      MirStepNode.fail .ub ∧
    evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
        [.aggregate 0 [.scalar addrSc, .scalar lenSc]] locals' destination targetBb =
      MirStepNode.fail .ub := by
  rcases hDstTy with ⟨elemTy, rfl⟩ | rfl <;>
    refine ⟨?_, ?_⟩ <;> (unfold evalNonSelectIntrinsicCall; simp only [hPt])

/-- **UB Characterization (`ptrSz ≠ 8` on `str`)**: a non-64-bit data pointer in a `&str` /
`*const str` wide pointer faults with `.fail .ub` in both `size_of_val` and `align_of_val`. -/
theorem evalNonSelectIntrinsicCall_str_ptrSz_ne_ub (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (p : ProvenancePtr) (ptrSz : Nat) (lenSc : ScalarInt)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some .str)
    (hNe : ptrSz ≠ 8) :
    evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p ptrSz, .scalar lenSc]] locals' destination targetBb =
        MirStepNode.fail .ub ∧
    evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
      [.aggregate 0 [.ptr p ptrSz, .scalar lenSc]] locals' destination targetBb =
        MirStepNode.fail .ub := by
  have hBeq : Nat.beq ptrSz 8 = false := by
    cases hb : Nat.beq ptrSz 8 with
    | false => rfl
    | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hb))
  refine ⟨?_, ?_⟩ <;> (unfold evalNonSelectIntrinsicCall; simp only [hPt, hBeq])

/-- Negative: `AggregateKind.rawPtr` on a non-`dyn` wide pointee (`[T]` / `str`) with
vtable-pointer metadata `.ptr vtPtr vtSz` (non-scalar metadata) fails closed with `.ub`. -/
theorem evalRvalue_aggregate_rawPtr_wide_vtableMeta_ub (locals locals₁ locals₂ : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (dataOp metaOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p vtPtr : ProvenancePtr) (ptrSz vtSz : Nat)
    (hWide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p ptrSz) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr vtPtr vtSz) locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]) mem
      localDecls layouts = .ub := by
  show evalAggregateRawPtr locals pointeeTy [dataOp, metaOp] mem localDecls layouts = _
  unfold evalAggregateRawPtr evalOperands
  rw [hData]
  dsimp only [evalOperands]
  rw [hMeta]
  dsimp only [evalOperands]
  rw [hWide]

/-- **`wrapScalarBits_eq_of_lt`**: when `val < modulus`, `wrapScalarBits val modulus`
reduces constructively (`Classical.choice`-free) to `val`. -/
theorem wrapScalarBits_eq_of_lt {val modulus : Nat} (h : val < modulus) :
    wrapScalarBits val modulus = val := by
  unfold wrapScalarBits
  cases hb : Nat.ble modulus val with
  | false => rfl
  | true => exact False.elim (Nat.not_le.mpr h (Nat.le_of_ble_eq_true hb))

/-- **`evalRvalue_unaryOp_ptrMetadata_wide_scalarAddr_of_lt`**: bounded form of
`evalRvalue_unaryOp_ptrMetadata_wide_scalarAddr` when `len < scalarModulus (layoutPointerBytes layouts)`,
reducing `wrapScalarBits` directly to `.scalar ⟨len, layoutPointerBytes layouts⟩`. -/
theorem evalRvalue_unaryOp_ptrMetadata_wide_scalarAddr_of_lt (locals locals' : List LocalSlot)
    (op : Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (addr len : Nat)
    (hTy : isNonWidePtrAggregateTy (operandTy localDecls layouts op) = false)
    (hLen : len < scalarModulus (layoutPointerBytes layouts))
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.scalar ⟨addr, layoutPointerBytes layouts⟩,
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals') :
    evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls layouts =
      .ok (.scalar ⟨len, layoutPointerBytes layouts⟩) locals' mem := by
  rw [evalRvalue_unaryOp_ptrMetadata_wide_scalarAddr locals locals' op mem localDecls layouts addr
    len hTy hOp, wrapScalarBits_eq_of_lt hLen]

/-- **`evalRvalue_aggregate_rawPtr_wide_scalarAddr_of_lt`**: bounded form of
`evalRvalue_aggregate_rawPtr_wide_scalarAddr` when `addr, len < scalarModulus (layoutPointerBytes layouts)`,
reducing `wrapScalarBits` directly to `.aggregate 0 [.scalar ⟨addr, ptrBytes⟩, .scalar ⟨len, ptrBytes⟩]`. -/
theorem evalRvalue_aggregate_rawPtr_wide_scalarAddr_of_lt (locals locals₁ locals₂ : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (dataOp metaOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) (addr len : Nat)
    (hWide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hAddr : addr < scalarModulus (layoutPointerBytes layouts))
    (hLen : len < scalarModulus (layoutPointerBytes layouts))
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar ⟨addr, layoutPointerBytes layouts⟩) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar ⟨len, layoutPointerBytes layouts⟩) locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]) mem
      localDecls layouts =
        .ok (.aggregate 0 [.scalar ⟨addr, layoutPointerBytes layouts⟩,
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals₂ mem := by
  rw [evalRvalue_aggregate_rawPtr_wide_scalarAddr locals locals₁ locals₂ pointeeTy mutability
    dataOp metaOp mem localDecls layouts addr len hWide hData hMeta,
    wrapScalarBits_eq_of_lt hAddr, wrapScalarBits_eq_of_lt hLen]

/-- **`evalRvalue_aggregate_rawPtr_to_raw_parts_roundtrip_scalarAddr`**:
decomposed `.field 0` / `.field 1` `(addr, len)` aggregate projections +
`AggregateKind.rawPtr` round-trip on a provenance-free (integer-address) wide
pointer `.aggregate 0 [.scalar ⟨addr, ptrBytes⟩, .scalar ⟨len, ptrBytes⟩]` with
`addr, len < scalarModulus ptrBytes`. -/
theorem evalRvalue_aggregate_rawPtr_to_raw_parts_roundtrip_scalarAddr (locals : List LocalSlot)
    (loc : Local) (pointeeTy dataTy metaTy : Ty) (mutability : Mutability)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (addr len : Nat)
    (hWide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hAddr : addr < scalarModulus (layoutPointerBytes layouts))
    (hLen : len < scalarModulus (layoutPointerBytes layouts))
    (hSlot : get? locals loc =
      some (.init (.aggregate 0 [.scalar ⟨addr, layoutPointerBytes layouts⟩,
        .scalar ⟨len, layoutPointerBytes layouts⟩])))
    (hNoUnion0 : placeTouchesUnion localDecls layouts
      { local_ := loc, projection := [.field 0 dataTy] } = false)
    (hNoUnion1 : placeTouchesUnion localDecls layouts
      { local_ := loc, projection := [.field 1 metaTy] } = false) :
    evalRvalue locals
      (.aggregate (.rawPtr pointeeTy mutability)
        [.copy { local_ := loc, projection := [.field 0 dataTy] },
         .copy { local_ := loc, projection := [.field 1 metaTy] }])
      mem localDecls layouts =
        .ok (.aggregate 0 [.scalar ⟨addr, layoutPointerBytes layouts⟩,
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals mem :=
  evalRvalue_aggregate_rawPtr_wide_scalarAddr_of_lt locals locals locals pointeeTy mutability
    (.copy { local_ := loc, projection := [.field 0 dataTy] })
    (.copy { local_ := loc, projection := [.field 1 metaTy] })
    mem localDecls layouts addr len hWide hAddr hLen
    (evalOperand_copy_widePtr_field0 locals loc dataTy _ _ mem.borrows mem.globals layouts
      mem.callerLocals localDecls mem.callStack hSlot hNoUnion0)
    (evalOperand_copy_widePtr_field1 locals loc metaTy _ _ mem.borrows mem.globals layouts
      mem.callerLocals localDecls mem.callStack hSlot hNoUnion1)

/-- Runtime representations of `()` metadata accepted by `evalAggregateRawPtr` for sized pointees:
both `.unit` (`ConstantValue.zeroSized`) and `.aggregate 0 []` (`Rvalue.aggregate .tuple []`). -/
@[reducible]
def IsThinRawPtrMetaVal (v : Value) : Prop :=
  v = .unit ∨ v = .aggregate 0 []

/-- **`evalRvalue_aggregate_rawPtr_thin_of_isThinMeta`**: `AggregateKind.rawPtr` on a sized pointee
(`isUnsizedRawPtrPointee pointeeTy = false`) with a provenance-carrying data pointer `.ptr p ptrBytes`
and either `.unit` or `.aggregate 0 []` (`Tuple([])`) metadata returns `.ok (.ptr p ptrBytes) locals₂ mem`. -/
theorem evalRvalue_aggregate_rawPtr_thin_of_isThinMeta (locals locals₁ locals₂ : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (dataOp unitOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (unitVal : Value)
    (hSized : isUnsizedRawPtrPointee pointeeTy = false)
    (hMetaVal : IsThinRawPtrMetaVal unitVal)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr p (layoutPointerBytes layouts)) locals₁)
    (hUnit : evalOperand locals₁ unitOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok unitVal locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, unitOp]) mem
      localDecls layouts = .ok (.ptr p (layoutPointerBytes layouts)) locals₂ mem := by
  rcases hMetaVal with rfl | rfl <;> {
    show evalAggregateRawPtr locals pointeeTy [dataOp, unitOp] mem localDecls layouts = _
    unfold evalAggregateRawPtr evalOperands
    rw [hData]
    dsimp only [evalOperands]
    rw [hUnit]
    simp only [hSized, Nat.beq_refl]
  }

/-- **`evalRvalue_aggregate_rawPtr_thin_scalarAddr`**: `AggregateKind.rawPtr` on a sized pointee
(`isUnsizedRawPtrPointee pointeeTy = false`) from a provenance-free integer address
`.scalar ⟨addr, ptrBytes⟩` (`addr < scalarModulus ptrBytes`) and `.unit` or `.aggregate 0 []`
metadata returns `.ok (.scalar ⟨addr, ptrBytes⟩) locals₂ mem`. -/
theorem evalRvalue_aggregate_rawPtr_thin_scalarAddr (locals locals₁ locals₂ : List LocalSlot)
    (pointeeTy : Ty) (mutability : Mutability) (dataOp unitOp : Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (addr : Nat) (unitVal : Value)
    (hSized : isUnsizedRawPtrPointee pointeeTy = false)
    (hAddr : addr < scalarModulus (layoutPointerBytes layouts))
    (hMetaVal : IsThinRawPtrMetaVal unitVal)
    (hData : evalOperand locals dataOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar ⟨addr, layoutPointerBytes layouts⟩) locals₁)
    (hUnit : evalOperand locals₁ unitOp mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok unitVal locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, unitOp]) mem
      localDecls layouts =
        .ok (.scalar ⟨addr, layoutPointerBytes layouts⟩) locals₂ mem := by
  rcases hMetaVal with rfl | rfl <;> {
    show evalAggregateRawPtr locals pointeeTy [dataOp, unitOp] mem localDecls layouts = _
    unfold evalAggregateRawPtr evalOperands
    rw [hData]
    dsimp only [evalOperands]
    rw [hUnit]
    simp only [hSized, Nat.beq_refl, wrapScalarBits_eq_of_lt hAddr]
  }

/-- **`evalRvalue_unaryOp_ptrMetadata_thin_scalarAddr`**: `Rvalue.unaryOp .ptrMetadata op` on a
provenance-free thin pointer `.scalar ⟨addr, ptrBytes⟩` returns `.ok .unit locals' mem` when
`isThinPtrMetadataOperandTy (operandTy localDecls layouts op) = true`. -/
theorem evalRvalue_unaryOp_ptrMetadata_thin_scalarAddr (locals locals' : List LocalSlot)
    (op : Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (addr : Nat)
    (hThinTy : isThinPtrMetadataOperandTy (operandTy localDecls layouts op) = true)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar ⟨addr, layoutPointerBytes layouts⟩) locals') :
    evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls layouts =
      .ok .unit locals' mem := by
  show evalUnaryPtrMetadata locals op mem localDecls layouts = _
  unfold evalUnaryPtrMetadata
  simp only [hOp, hThinTy, Nat.beq_refl, Bool.and_self]

/-- Negative: `Rvalue.unaryOp .ptrMetadata op` faults with `.ub` when a scalar `.scalar sc` is
evaluated for an operand whose static type is a wide pointer/reference
(`isThinPtrMetadataOperandTy (operandTy localDecls layouts op) = false`). -/
theorem evalRvalue_unaryOp_ptrMetadata_scalar_wideTy_ub (locals locals' : List LocalSlot)
    (op : Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (sc : ScalarInt)
    (hNotThin : isThinPtrMetadataOperandTy (operandTy localDecls layouts op) = false)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.scalar sc) locals') :
    evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls layouts = .ub := by
  show evalUnaryPtrMetadata locals op mem localDecls layouts = _
  unfold evalUnaryPtrMetadata
  simp only [hOp, hNotThin, Bool.and_false]

/-- **`mirStep_call_sizeOfVal_str_ptrSz_ne_ub`**: `stepMirFn` and `mirStep` fault with `.ub`
when `core::intrinsics::size_of_val` on `.str` receives a wide pointer with `ptrSz ≠ 8`. -/
theorem mirStep_call_sizeOfVal_str_ptrSz_ne_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {p : ProvenancePtr} {ptrSz : Nat} {lenSc : ScalarInt}
    {locals' : List LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::size_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p ptrSz, .scalar lenSc]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::size_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some .str)
    (hNe : ptrSz ≠ 8) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p ptrSz, .scalar lenSc]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hFail := (evalNonSelectIntrinsicCall_str_ptrSz_ne_ub s _ cur.localDecls cur.layouts [ptrOp]
    locals' destination targetBb p ptrSz lenSc hPt hNe).1
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl hFail

/-- **`mirStep_call_alignOfVal_str_ptrSz_ne_ub`**: `stepMirFn` and `mirStep` fault with `.ub`
when `core::intrinsics::align_of_val` on `.str` receives a wide pointer with `ptrSz ≠ 8`. -/
theorem mirStep_call_alignOfVal_str_ptrSz_ne_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {p : ProvenancePtr} {ptrSz : Nat} {lenSc : ScalarInt}
    {locals' : List LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::align_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.ptr p ptrSz, .scalar lenSc]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::align_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some .str)
    (hNe : ptrSz ≠ 8) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.ptr p ptrSz, .scalar lenSc]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hFail := (evalNonSelectIntrinsicCall_str_ptrSz_ne_ub s _ cur.localDecls cur.layouts [ptrOp]
    locals' destination targetBb p ptrSz lenSc hPt hNe).2
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl hFail

/-- **`mirStep_call_sizeOfVal_unsized_scalarAddr_ub`**: `stepMirFn` and `mirStep` fault with `.ub`
when `core::intrinsics::size_of_val` on an unsized `.slice elemTy` or `.str` receives a
provenance-free wide pointer `.aggregate 0 [.scalar addrSc, .scalar lenSc]`. -/
theorem mirStep_call_sizeOfVal_unsized_scalarAddr_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {dstTy : RigidTy} {addrSc lenSc : ScalarInt}
    {locals' : List LocalSlot}
    (hDstTy : (∃ elemTy, dstTy = .slice elemTy) ∨ dstTy = .str)
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::size_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.scalar addrSc, .scalar lenSc]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::size_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::size_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some dstTy) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.scalar addrSc, .scalar lenSc]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hFail := (evalNonSelectIntrinsicCall_unsized_scalarAddr_ub s _ cur.localDecls cur.layouts
    [ptrOp] locals' destination targetBb dstTy addrSc lenSc hDstTy hPt).1
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl hFail

/-- **`mirStep_call_alignOfVal_unsized_scalarAddr_ub`**: `stepMirFn` and `mirStep` fault with `.ub`
when `core::intrinsics::align_of_val` on an unsized `.slice elemTy` or `.str` receives a
provenance-free wide pointer `.aggregate 0 [.scalar addrSc, .scalar lenSc]`. -/
theorem mirStep_call_alignOfVal_unsized_scalarAddr_ub {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {func ptrOp : Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {span : String}
    {typeArgs : List RigidTy} {dstTy : RigidTy} {addrSc lenSc : ScalarInt}
    {locals' : List LocalSlot}
    (hDstTy : (∃ elemTy, dstTy = .slice elemTy) ∨ dstTy = .str)
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator =
      { kind := .call func [ptrOp] destination (some targetBb) unwind, span := span })
    (hCallee : extractCallee? func = some ("core::intrinsics::align_of_val", typeArgs))
    (hArg : evalOperand s.frame.locals ptrOp s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals .nil s.memory.callStack =
        .ok (.aggregate 0 [.scalar addrSc, .scalar lenSc]) locals')
    (hNoOverride : lookupCallee s.memory.callees cur.layouts "core::intrinsics::align_of_val"
      typeArgs s.memory.traitImpls = none)
    (hPt : resolveIntrinsicPointeeTy?
      { defPath := "core::intrinsics::align_of_val", typeArgs := typeArgs, fnSig := none,
        isIndirect := false }
      cur.localDecls cur.layouts [ptrOp] = some dstTy) :
    stepMirFn body s = MirStepNode.fail .ub ∧ mirStep body s = .fault := by
  have hArgs : evalOperands s.frame.locals [ptrOp] s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals (callStack := s.memory.callStack) =
        .ok [.aggregate 0 [.scalar addrSc, .scalar lenSc]] locals' := by
    unfold evalOperands
    rw [hArg]
    rfl
  have hFail := (evalNonSelectIntrinsicCall_unsized_scalarAddr_ub s _ cur.localDecls cur.layouts
    [ptrOp] locals' destination targetBb dstTy addrSc lenSc hDstTy hPt).2
  exact mirStep_call_nonSelectIntrinsic_fail hCur hPhase hBb hEnd hTerm hCallee hArgs hNoOverride
    rfl rfl rfl hFail

/-! ### 6. `CastKind.ptrToPtr` on Wide Pointers (`ptr.cast()`, rustc's `to_raw_parts` Lowering) -/

/-- **`evalRvalue_cast_ptrToPtr_wide_to_thin`** (`p.cast::<U>()`, the data half of
`<*const [T]>::to_raw_parts` as rustc lowers it: `(p as *const (), PtrMetadata(p))`): a
`CastKind.ptrToPtr` from a wide `[T]` / `str` pointer `.aggregate 0 [.ptr q ptrBytes,
.scalar ⟨len, ptrBytes⟩]` to a thin raw pointer type returns the bare data pointer
`.ptr q ptrBytes` with `mem` unchanged when the data pointer carries no live borrow
(`lookupBorrow mem.borrows q.tag = none`, e.g. a pointer into a captured global); borrow-backed
pointers instead derive a child element pointer (`deriveStackElemThinPtr`). -/
theorem evalRvalue_cast_ptrToPtr_wide_to_thin (locals locals' : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (q : ProvenancePtr) (len : Nat)
    (hThin : isThinRawPtrTy targetTy = true)
    (hNoBorrow : lookupBorrow mem.borrows q.tag = none)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.ptr q (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals') :
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts =
      .ok (.ptr q (layoutPointerBytes layouts)) locals' mem := by
  show evalCastPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, Bool.and_self, hThin, hNoBorrow]

/-- **`evalRvalue_cast_ptrToPtr_wide_to_wide`**: a `CastKind.ptrToPtr` between non-`dyn` wide raw
pointer types (`*const [T] as *mut [T]`, `*const [u8] as *const [U]`, `*const str as
*const [u8]`) keeps both the data pointer and the element-count metadata unchanged (the byte
extent changes with the element type, the length does not). -/
theorem evalRvalue_cast_ptrToPtr_wide_to_wide (locals locals' : List LocalSlot) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (q : ProvenancePtr) (len : Nat)
    (hNotThin : isThinRawPtrTy targetTy = false)
    (hWide : wideRawPtrIsDyn? targetTy = some false)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.ptr q (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals') :
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts =
      .ok (.aggregate 0 [.ptr q (layoutPointerBytes layouts),
        .scalar ⟨len, layoutPointerBytes layouts⟩]) locals' mem := by
  show evalCastPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, Bool.and_self, hNotThin, hWide]

/-- **`evalRvalue_cast_ptrToPtr_wide_to_thin_already_subslice`**: when a stack-borrow-backed wide
slice pointer `.aggregate 0 [.ptr q ptrBytes, .scalar ⟨len, ptrBytes⟩]` is cast to a thin raw
pointer (`isThinRawPtrTy targetTy = true`) and its `BorrowEntry`'s container projection already
ends with a `.subslice` covering `[0 .. length elems)` at element offset `0`
(`alreadySubslice = true` in `deriveStackElemThinPtr`), `evalCastPtrToPtr` returns
`.ok (.ptr q ptrBytes) locals' mem` with `mem` **unchanged** (no fresh tag is allocated), so
`(p as *const U, PtrMetadata(p))` + `AggregateKind.rawPtr` is the exact identity on subslice-backed
borrow pointers as well as global-backed pointers. -/
theorem evalRvalue_cast_ptrToPtr_wide_to_thin_already_subslice
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (q : ProvenancePtr) (len : Nat) (parentEntry : BorrowEntry) (rootVal : Value)
    (containerProj : List ProjectionElem) (baseIdx : Nat) (elems : List Value)
    (rawElemOffset : Nat)
    (hThin : isThinRawPtrTy targetTy = true)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.ptr q (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals')
    (hBorrow : lookupBorrow mem.borrows q.tag = some parentEntry)
    (hPerm : parentEntry.perm ≠ .disabled)
    (hRoot : activeFrameSlot? locals' mem.callStack parentEntry.targetFrameDepth
      parentEntry.targetLocal = some (.init rootVal))
    (hRead : readSliceBackingAggregate? locals' rootVal
      (normalizeSubsliceProjections (stripTransparentProjections parentEntry.targetProjection))
      len = some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? q.offsetBytes (inferElemListByteStride elems) =
      some rawElemOffset)
    (hBound : Nat.ble (Nat.add (Nat.add rawElemOffset baseIdx) len) (length elems) = true)
    (hAlready : Bool.and (endsWithSubslice containerProj)
      (Bool.and (Nat.beq (Nat.add rawElemOffset baseIdx) 0) (Nat.beq len (length elems))) =
        true) :
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts =
      .ok (.ptr q (layoutPointerBytes layouts)) locals' mem := by
  show evalCastPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, Bool.and_self, hThin, hBorrow]
  unfold deriveStackElemThinPtr
  rcases parentEntry with ⟨tag, tLoc, tProj, perm, rOff, rLen, prot, pTag, tDepth, aDead⟩
  dsimp only at hPerm hRoot hRead ⊢
  cases perm
  all_goals first
    | exact absurd rfl hPerm
    | (simp only [hRoot, hRead, hOff, hBound, hAlready] <;> rfl)

/-- **`evalRvalue_cast_ptrToPtr_wide_to_thin_fresh_subslice`**: when a stack-borrow-backed wide
slice pointer `.aggregate 0 [.ptr q ptrBytes, .scalar ⟨len, ptrBytes⟩]` is cast to a thin raw
pointer (`isThinRawPtrTy targetTy = true`) and its container projection does not already end with
a matching `[0 .. length elems)` `.subslice` (`alreadySubslice = false`), `deriveStackElemThinPtr`
allocates a fresh narrowed child borrow entry at `mem.nextTag` and returns
`.ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } ptrBytes) locals' mem'`. -/
theorem evalRvalue_cast_ptrToPtr_wide_to_thin_fresh_subslice
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (q : ProvenancePtr) (len : Nat) (parentEntry : BorrowEntry) (rootVal : Value)
    (containerProj : List ProjectionElem) (baseIdx : Nat) (elems : List Value)
    (rawElemOffset : Nat)
    (hThin : isThinRawPtrTy targetTy = true)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.ptr q (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals')
    (hBorrow : lookupBorrow mem.borrows q.tag = some parentEntry)
    (hPerm : parentEntry.perm ≠ .disabled)
    (hRoot : activeFrameSlot? locals' mem.callStack parentEntry.targetFrameDepth
      parentEntry.targetLocal = some (.init rootVal))
    (hRead : readSliceBackingAggregate? locals' rootVal
      (normalizeSubsliceProjections (stripTransparentProjections parentEntry.targetProjection))
      len = some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? q.offsetBytes (inferElemListByteStride elems) =
      some rawElemOffset)
    (hBound : Nat.ble (Nat.add (Nat.add rawElemOffset baseIdx) len) (length elems) = true)
    (hFresh : Bool.and (endsWithSubslice containerProj)
      (Bool.and (Nat.beq (Nat.add rawElemOffset baseIdx) 0) (Nat.beq len (length elems))) =
        false) :
    let elemOffset := Nat.add rawElemOffset baseIdx
    let endOffset := Nat.add elemOffset len
    let subProj := ProjectionElem.subslice elemOffset endOffset false :: .nil
    let fullProj :=
      match containerProj with
      | .nil => subProj
      | ph :: pt => ph :: appendProjections pt subProj
    let entry : BorrowEntry :=
      { tag := mem.nextTag
        targetLocal := parentEntry.targetLocal
        targetFrameDepth := parentEntry.targetFrameDepth
        allocDead := parentEntry.allocDead
        targetProjection := normalizeSubsliceProjections fullProj
        perm := parentEntry.perm }
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } (layoutPointerBytes layouts)) locals'
        { mem with borrows := entry :: mem.borrows, nextTag := Nat.add mem.nextTag 1 } := by
  rcases parentEntry with ⟨tag, tLoc, tProj, perm, rOff, rLen, prot, pTag, tDepth, aDead⟩
  intro elemOffset endOffset subProj fullProj entry
  show evalCastPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, Bool.and_self, hThin, hBorrow]
  unfold deriveStackElemThinPtr
  dsimp only [entry, fullProj, subProj, endOffset, elemOffset] at hPerm hRoot hRead ⊢
  cases perm
  all_goals first
    | exact absurd rfl hPerm
    | (cases containerProj <;> simp only [hRoot, hRead, hOff, hBound, hFresh] <;> rfl)

/-- **UB Characterization (`CastKind.ptrToPtr` on `.disabled` borrow)**: unlike `UnOp.ptrMetadata`
(which never consults `mem.borrows`), casting a wide pointer `.aggregate 0 [.ptr q ptrBytes,
.scalar ⟨len, ptrBytes⟩]` to a thin raw pointer (`p as *const ()`) consults `lookupBorrow` via
`deriveStackElemThinPtr` and faults with `.ub` when `parentEntry.perm = .disabled`. -/
theorem evalRvalue_cast_ptrToPtr_wide_to_thin_disabled_ub
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (q : ProvenancePtr) (len : Nat) (parentEntry : BorrowEntry)
    (hThin : isThinRawPtrTy targetTy = true)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.ptr q (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals')
    (hBorrow : lookupBorrow mem.borrows q.tag = some parentEntry)
    (hDis : parentEntry.perm = .disabled) :
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts = .ub := by
  show evalCastPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, Bool.and_self, hThin, hBorrow]
  unfold deriveStackElemThinPtr
  rw [hDis]

/-- **`evalRvalue_cast_ptrToPtr_wide_scalarAddr_to_thin`**: `CastKind.ptrToPtr` on a provenance-free
(integer-address) wide pointer `.aggregate 0 [.scalar ⟨addr, ptrBytes⟩, .scalar ⟨len, ptrBytes⟩]`
(`addr < scalarModulus ptrBytes`) to a thin raw pointer (`isThinRawPtrTy targetTy = true`) returns
`.ok (.scalar ⟨addr, ptrBytes⟩) locals' mem` without consulting `mem.borrows`. -/
theorem evalRvalue_cast_ptrToPtr_wide_scalarAddr_to_thin
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (addr len : Nat)
    (hThin : isThinRawPtrTy targetTy = true)
    (hAddr : addr < scalarModulus (layoutPointerBytes layouts))
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.scalar ⟨addr, layoutPointerBytes layouts⟩,
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals') :
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts =
      .ok (.scalar ⟨addr, layoutPointerBytes layouts⟩) locals' mem := by
  show evalCastPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, Bool.and_self, hThin, wrapScalarBits_eq_of_lt hAddr]

/-- **`evalRvalue_cast_ptrToPtr_wide_scalarAddr_to_wide`**: `CastKind.ptrToPtr` on a provenance-free
wide pointer `.aggregate 0 [.scalar ⟨addr, ptrBytes⟩, .scalar ⟨len, ptrBytes⟩]`
(`addr, len < scalarModulus ptrBytes`) between non-`dyn` wide raw pointer types returns the
provenance-free wide pointer unchanged. -/
theorem evalRvalue_cast_ptrToPtr_wide_scalarAddr_to_wide
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (addr len : Nat)
    (hNotThin : isThinRawPtrTy targetTy = false)
    (hWide : wideRawPtrIsDyn? targetTy = some false)
    (hAddr : addr < scalarModulus (layoutPointerBytes layouts))
    (hLen : len < scalarModulus (layoutPointerBytes layouts))
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.scalar ⟨addr, layoutPointerBytes layouts⟩,
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals') :
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts =
      .ok (.aggregate 0 [.scalar ⟨addr, layoutPointerBytes layouts⟩,
        .scalar ⟨len, layoutPointerBytes layouts⟩]) locals' mem := by
  show evalCastPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, Bool.and_self, hNotThin, hWide,
    wrapScalarBits_eq_of_lt hAddr, wrapScalarBits_eq_of_lt hLen]

/-- **Negative (`CastKind.ptrToPtr` thin-to-wide)**: casting a thin pointer `.ptr q ptrBytes` to a
wide raw pointer (`thinRawPtrPointee? targetTy = none`) via `CastKind.ptrToPtr` faults with `.ub`. -/
theorem evalRvalue_cast_ptrToPtr_thin_to_wide_ub
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (q : ProvenancePtr)
    (hNotThin : thinRawPtrPointee? targetTy = none)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok (.ptr q (layoutPointerBytes layouts)) locals') :
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts = .ub := by
  show evalCastPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, hNotThin]

/-- **Negative (`CastKind.ptrToPtr` slice-to-`dyn`)**: casting a slice/str wide pointer
(`isSliceOrStrPtrOrRefTy (operandTy localDecls layouts op) = true`) to a `dyn Trait` wide pointer
(`isThinRawPtrTy targetTy = false`, `wideRawPtrIsDyn? targetTy = some true`) via `CastKind.ptrToPtr`
faults with `.ub`. -/
theorem evalRvalue_cast_ptrToPtr_wide_slice_to_dyn_ub
    (locals locals' : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (q : ProvenancePtr) (len : Nat)
    (hNotThin : isThinRawPtrTy targetTy = false)
    (hDyn : wideRawPtrIsDyn? targetTy = some true)
    (hSliceSrc : isSliceOrStrPtrOrRefTy (operandTy localDecls layouts op) = true)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack =
        .ok (.aggregate 0 [.ptr q (layoutPointerBytes layouts),
          .scalar ⟨len, layoutPointerBytes layouts⟩]) locals') :
    evalRvalue locals (.cast .ptrToPtr op targetTy) mem localDecls layouts = .ub := by
  show evalCastPtrToPtr locals op targetTy mem localDecls layouts = _
  unfold evalCastPtrToPtr
  simp only [hOp, Nat.beq_refl, Bool.and_self, hNotThin, hDyn, hSliceSrc]

/-- **`mirStep_assign_cast_ptrToPtr_wide_to_thin`**: one-step `stepMirFn` / `mirStep` lifter for
`StatementKind.assign { local_ := dstLoc, projection := [] } (.cast .ptrToPtr op targetTy)` on a
wide pointer with `lookupBorrow s.memory.borrows q.tag = none` (rustc's `p as *const ()` data-half
lowering in `to_raw_parts`). -/
theorem mirStep_assign_cast_ptrToPtr_wide_to_thin {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {dstLoc : Local} {op : Operand} {targetTy : Ty} {span : String}
    {q : ProvenancePtr} {len : Nat} {locals₁ locals₂ : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hStmt : get? blk.statements s.frame.stmtIdx =
      some { kind := .assign { local_ := dstLoc, projection := [] } (.cast .ptrToPtr op targetTy),
             span := span })
    (hThin : isThinRawPtrTy targetTy = true)
    (hNoBorrow : lookupBorrow s.memory.borrows q.tag = none)
    (hOp : evalOperand s.frame.locals op s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals cur.localDecls s.memory.callStack =
        .ok (.aggregate 0 [.ptr q (layoutPointerBytes cur.layouts),
          .scalar ⟨len, layoutPointerBytes cur.layouts⟩]) locals₁)
    (hProt : hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors dstLoc .none
      .nil 0 0 (length s.memory.callStack) = false)
    (hSlot : get? locals₁ dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals₁ dstLoc (.init (.ptr q (layoutPointerBytes cur.layouts))) = some locals₂) :
    let s' : MachineState :=
      { frame := { blockIdx := s.frame.blockIdx, stmtIdx := s.frame.stmtIdx + 1, locals := locals₂ }
        memory := { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none
            (length s.memory.callStack) } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) :=
  mirStep_assign_local hCur hPhase hBb hStmt
    (evalRvalue_cast_ptrToPtr_wide_to_thin s.frame.locals locals₁ op targetTy s.memory
      cur.localDecls cur.layouts q len hThin hNoBorrow hOp)
    hProt hSlot hLive hSet

/-- **`mirStep_assign_cast_ptrToPtr_wide_to_wide`**: one-step `stepMirFn` / `mirStep` lifter for
`StatementKind.assign { local_ := dstLoc, projection := [] } (.cast .ptrToPtr op targetTy)` between
non-`dyn` wide raw pointer types (`*const [T] as *mut [T]`, `*const str as *const [u8]`). -/
theorem mirStep_assign_cast_ptrToPtr_wide_to_wide {body cur : CapturedMir} {s : MachineState}
    {blk : BasicBlockData} {dstLoc : Local} {op : Operand} {targetTy : Ty} {span : String}
    {q : ProvenancePtr} {len : Nat} {locals₁ locals₂ : List LocalSlot} {slot : LocalSlot}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hStmt : get? blk.statements s.frame.stmtIdx =
      some { kind := .assign { local_ := dstLoc, projection := [] } (.cast .ptrToPtr op targetTy),
             span := span })
    (hNotThin : isThinRawPtrTy targetTy = false)
    (hWide : wideRawPtrIsDyn? targetTy = some false)
    (hOp : evalOperand s.frame.locals op s.memory.borrows s.memory.globals cur.layouts
      s.memory.callerLocals cur.localDecls s.memory.callStack =
        .ok (.aggregate 0 [.ptr q (layoutPointerBytes cur.layouts),
          .scalar ⟨len, layoutPointerBytes cur.layouts⟩]) locals₁)
    (hProt : hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors dstLoc .none
      .nil 0 0 (length s.memory.callStack) = false)
    (hSlot : get? locals₁ dstLoc = some slot)
    (hLive : slotLive slot = true)
    (hSet : set? locals₁ dstLoc
      (.init (.aggregate 0 [.ptr q (layoutPointerBytes cur.layouts),
        .scalar ⟨len, layoutPointerBytes cur.layouts⟩])) = some locals₂) :
    let s' : MachineState :=
      { frame := { blockIdx := s.frame.blockIdx, stmtIdx := s.frame.stmtIdx + 1, locals := locals₂ }
        memory := { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none
            (length s.memory.callStack) } }
    stepMirFn body s = MirStepNode.step s' ∧
    mirStep body s = .cont s' ∧
    (∀ fuel post,
      Anneal.Rustc.V2026_06_01.Lower.wpMirBounded (fuel + 1) body s post ↔
        Anneal.Rustc.V2026_06_01.Lower.wpMirBounded fuel body s' post) ∧
    (∀ post, WpConverges (mirStep body) s' post → WpConverges (mirStep body) s post) :=
  mirStep_assign_local hCur hPhase hBb hStmt
    (evalRvalue_cast_ptrToPtr_wide_to_wide s.frame.locals locals₁ op targetTy s.memory
      cur.localDecls cur.layouts q len hNotThin hWide hOp)
    hProt hSlot hLive hSet

end UnsizedDstMetadataLifters

end Anneal.MirLiftCore
