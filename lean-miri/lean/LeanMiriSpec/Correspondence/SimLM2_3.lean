import LeanMiriSpec.Correspondence.Simulation
import LeanMiriSpec.Correspondence.SimLM2_2
import LeanMiriSpec.Correspondence.Translate

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Sequence

namespace LeanMiriSpec.Correspondence

inductive WellTypedLM2_3EnumAggregate
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (defPath : DefPath) (variantIdx : VariantIdx)
    (ops : List MirAst.Operand) : Prop where
  | mk (decl : LocalDecl)
       (fields : List StructFieldDesc)
       (paths : List (List ProjectionElem))
       (decl_lookup : get? body.localDecls dstIdx = some decl)
       (env_lookup : env decl.ty = some (fields, paths))
       (is_adt : ∃ args, decl.ty.kind = .adt defPath args)
       (valid_layout : ValidStructLayout (translateTy decl.ty body.layouts).layout fields)

theorem evalRvalue_aggregate_enum_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local}
    {variantIdx : VariantIdx} {defPath : DefPath} {activeField : Option FieldIdx}
    {ops : List MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩)
    (hwt : WellTypedLM2_3EnumAggregate body env stEnv dstIdx defPath variantIdx ops) :
    StepRelLM2_2 body env (aggPostStaticEnv stEnv dstIdx ops) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  cases hwt with
  | mk decl fields paths decl_lookup env_lookup is_adt valid_layout =>
    obtain ⟨slot_dst, mls_dst0, hlt_dst0, _, hslot_dst, _, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local decl_lookup
    cases hloc_dst0 with
    | base _ _ henv_none _ => rw [env_lookup] at henv_none; cases henv_none
    | structDead _ _ _ _ _ =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
        sorry
      have hm_ub : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩) m = (m, .error (.undefinedBehavior "write to dead local")) := by
        sorry
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub m "write to dead local"
    | structUninitImm _ _ _ _ _ =>
      obtain ⟨s', ha_ok⟩ : ∃ s', evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩ body.localDecls body.layouts = .step s' := by sorry
      obtain ⟨m', hm_ok⟩ : ∃ m', Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩) m = (m', .ok ()) := by sorry
      rw [ha_ok]
      have hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true) := by sorry
      rw [hstep]
      exact StepRelLM2_2.step s' m' sorry
    | structUninitInd _ _ _ _ _ _ _ =>
      obtain ⟨s', ha_ok⟩ : ∃ s', evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩ body.localDecls body.layouts = .step s' := by sorry
      obtain ⟨m', hm_ok⟩ : ∃ m', Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩) m = (m', .ok ()) := by sorry
      rw [ha_ok]
      have hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true) := by sorry
      rw [hstep]
      exact StepRelLM2_2.step s' m' sorry
    | structImm _ _ _ _ _ _ _ _ =>
      obtain ⟨s', ha_ok⟩ : ∃ s', evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩ body.localDecls body.layouts = .step s' := by sorry
      obtain ⟨m', hm_ok⟩ : ∃ m', Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩) m = (m', .ok ()) := by sorry
      rw [ha_ok]
      have hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true) := by sorry
      rw [hstep]
      exact StepRelLM2_2.step s' m' sorry
    | structInd _ _ _ _ _ _ _ _ =>
      obtain ⟨s', ha_ok⟩ : ∃ s', evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩ body.localDecls body.layouts = .step s' := by sorry
      obtain ⟨m', hm_ok⟩ : ∃ m', Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩) m = (m', .ok ()) := by sorry
      rw [ha_ok]
      have hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true) := by sorry
      rw [hstep]
      exact StepRelLM2_2.step s' m' sorry


inductive WellTypedLM2_3SetDiscriminant
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (place : Place) (variantIdx : VariantIdx) : Prop where
  | mk (decl : LocalDecl)
       (defPath : DefPath)
       (fields : List StructFieldDesc)
       (paths : List (List ProjectionElem))
       (decl_lookup : get? body.localDecls place.local_ = some decl)
       (proj_nil : place.projection = [])
       (env_lookup : env decl.ty = some (fields, paths))
       (is_adt : ∃ args, decl.ty.kind = .adt defPath args)
       (valid_layout : ValidStructLayout (translateTy decl.ty body.layouts).layout fields)

theorem step_setDiscriminant_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {place : Place} {variantIdx : VariantIdx} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.setDiscriminant place variantIdx, span⟩)
    (hwt : WellTypedLM2_3SetDiscriminant body env stEnv place variantIdx) :
    StepRelLM2_2 body env stEnv k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  cases hwt with
  | mk decl decl_lookup =>
    obtain ⟨s', ha_ok⟩ : ∃ s', evalStmt s ⟨.setDiscriminant place variantIdx, span⟩ body.localDecls body.layouts = .step s' := by sorry
    obtain ⟨m', hm_ok⟩ : ∃ m', Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.setDiscriminant place variantIdx, span⟩) m = (m', .ok ()) := by sorry
    rw [ha_ok]
    have hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true) := by sorry
    rw [hstep]
    exact StepRelLM2_2.step s' m' sorry

inductive WellTypedLM2_3DiscriminantRead
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (place : Place) : Prop where
  | mk (decl : LocalDecl)
       (placeDecl : LocalDecl)
       (defPath : DefPath)
       (fields : List StructFieldDesc)
       (paths : List (List ProjectionElem))
       (decl_lookup : get? body.localDecls dstIdx = some decl)
       (place_lookup : get? body.localDecls place.local_ = some placeDecl)
       (env_lookup : env placeDecl.ty = some (fields, paths))
       (is_adt : ∃ args, placeDecl.ty.kind = .adt defPath args)
       (valid_layout : ValidStructLayout (translateTy placeDecl.ty body.layouts).layout fields)

theorem evalRvalue_discriminant_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {place : Place} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩)
    (hwt : WellTypedLM2_3DiscriminantRead body env stEnv dstIdx place) :
    StepRelLM2_2 body env stEnv k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  cases hwt with
  | mk decl placeDecl defPath fields paths decl_lookup place_lookup env_lookup is_adt valid_layout =>
    obtain ⟨slot_dst, mls_dst0, hlt_dst0, _, hslot_dst, _, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local place_lookup
    cases hloc_dst0 with
    | base _ _ henv_none _ => rw [env_lookup] at henv_none; cases henv_none
    | structDead _ _ _ _ _ =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
        sorry
      have hm_ub : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩) m = (m, .error (.undefinedBehavior "read of dead local")) := by
        sorry
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub m "read of dead local"
    | structUninitImm _ _ _ _ _ =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
        sorry
      have hm_ub : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩) m = (m, .error (.undefinedBehavior "read of uninitialized local")) := by
        sorry
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub m "read of uninitialized local"
    | structUninitInd _ _ _ _ _ _ _ =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
        sorry
      have hm_ub : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩) m = (m, .error (.undefinedBehavior "read of uninitialized local")) := by
        sorry
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub m "read of uninitialized local"
    | structImm _ _ _ _ _ _ _ _ =>
      obtain ⟨s', ha_ok⟩ : ∃ s', evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩ body.localDecls body.layouts = .step s' := by sorry
      obtain ⟨m', hm_ok⟩ : ∃ m', Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩) m = (m', .ok ()) := by sorry
      rw [ha_ok]
      have hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true) := by sorry
      rw [hstep]
      exact StepRelLM2_2.step s' m' sorry
    | structInd _ _ _ _ _ _ _ _ =>
      obtain ⟨s', ha_ok⟩ : ∃ s', evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩ body.localDecls body.layouts = .step s' := by sorry
      obtain ⟨m', hm_ok⟩ : ∃ m', Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩) m = (m', .ok ()) := by sorry
      rw [ha_ok]
      have hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true) := by sorry
      rw [hstep]
      exact StepRelLM2_2.step s' m' sorry



inductive WellTypedLM2_3Downcast
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (base : Local) (projs : List ProjectionElem)
    (variantName : String) (variantIdx : VariantIdx) (field : FieldIdx) (ty : Ty) : Prop where
  | mk (decl : LocalDecl)

theorem evalProjection_downcast_field_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {base : Local} {projs : List ProjectionElem}
    {variantName : String} {variantIdx : VariantIdx} {field : FieldIdx} {ty : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨base, projs ++ [.downcast variantName variantIdx, .field field ty]⟩)), span⟩)
    (hwt : WellTypedLM2_3Downcast body env stEnv dstIdx base projs variantName variantIdx field ty) :
    StepRelLM2_2 body env stEnv k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  cases hwt with
  | mk decl =>

    obtain ⟨s', ha_ok⟩ : ∃ s', evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨base, projs ++ [.downcast variantName variantIdx, .field field ty]⟩)), span⟩ body.localDecls body.layouts = .step s' := by sorry
    obtain ⟨m', hm_ok⟩ : ∃ m', Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨base, projs ++ [.downcast variantName variantIdx, .field field ty]⟩)), span⟩) m = (m', .ok ()) := by sorry
    rw [ha_ok]
    have hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true) := by sorry
    rw [hstep]
    exact StepRelLM2_2.step s' m' sorry


inductive WellTypedLM2_3SwitchInt
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (discr : MirAst.Operand) (targets : SwitchTargets) : Prop where
  | mk (decl : LocalDecl)
       (isMove : Bool)
       (dstIdx : Local)
       (is_discr : discr = mkPlaceOperand isMove ⟨dstIdx, []⟩)
       (decl_lookup : get? body.localDecls dstIdx = some decl)

theorem enum_match_switchInt_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {discr : MirAst.Operand} {targets : SwitchTargets}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : bb.terminator.kind = .switchInt discr targets)
    (hwt : WellTypedLM2_3SwitchInt body env stEnv discr targets) :
    StepRelLM2_2 body env stEnv k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  cases hwt with
  | mk decl isMove dstIdx is_discr decl_lookup =>
    obtain ⟨slot_dst, mls_dst0, hlt_dst0, _, hslot_dst, _, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local decl_lookup
    cases hloc_dst0 with
    | base _ _ henv_none _ =>
      sorry
    | structDead _ _ _ _ _ =>
      sorry
    | structUninitImm _ _ _ _ _ =>
      sorry
    | structUninitInd _ _ _ _ _ _ _ =>
      sorry
    | structImm _ _ _ _ _ _ _ _ =>
      sorry
    | structInd _ _ _ _ _ _ _ _ =>
      sorry

end LeanMiriSpec.Correspondence
