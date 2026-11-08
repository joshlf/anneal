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
    have hm_ok : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩) m = (sorry, .ok ()) := by sorry
    have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.adt defPath variantIdx activeField) ops), span⟩ body.localDecls body.layouts = MirStepNode.step sorry := by sorry
    sorry

inductive WellTypedLM2_3SetDiscriminant
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (place : Place) (variantIdx : VariantIdx) : Prop where
  | mk (decl : LocalDecl)
       (decl_lookup : get? body.localDecls place.local_ = some decl)

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
    have hm_ok : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.setDiscriminant place variantIdx, span⟩) m = (sorry, .ok ()) := by sorry
    have ha_ok : evalStmt s ⟨.setDiscriminant place variantIdx, span⟩ body.localDecls body.layouts = MirStepNode.step sorry := by sorry
    sorry

inductive WellTypedLM2_3DiscriminantRead
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (place : Place) : Prop where
  | mk (decl : LocalDecl)
       (placeDecl : LocalDecl)
       (decl_lookup : get? body.localDecls dstIdx = some decl)
       (place_lookup : get? body.localDecls place.local_ = some placeDecl)

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
  | mk decl placeDecl decl_lookup place_lookup =>
    have hm_ok : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩) m = (sorry, .ok ()) := by sorry
    have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.discriminant place), span⟩ body.localDecls body.layouts = MirStepNode.step sorry := by sorry
    sorry

inductive WellTypedLM2_3Downcast
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (place : Place) (variantIdx : VariantIdx) : Prop where
  | mk (decl : LocalDecl)
       (placeDecl : LocalDecl)
       (decl_lookup : get? body.localDecls dstIdx = some decl)
       (place_lookup : get? body.localDecls place.local_ = some placeDecl)

theorem evalProjection_downcast_field_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {base : Local} {projs : List ProjectionElem}
    {variantName : Option String} {variantIdx : VariantIdx} {field : FieldIdx} {ty : Ty}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨base, projs ++ [.downcast variantName variantIdx, .field field ty]⟩)), span⟩)
    (hwt : WellTypedLM2_3Downcast body env stEnv dstIdx ⟨base, projs⟩ variantIdx) :
    StepRelLM2_2 body env stEnv k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  cases hwt with
  | mk decl placeDecl decl_lookup place_lookup =>
    have hm_ok : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨base, projs ++ [.downcast variantName variantIdx, .field field ty]⟩)), span⟩) m = (sorry, .ok ()) := by sorry
    have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨base, projs ++ [.downcast variantName variantIdx, .field field ty]⟩)), span⟩ body.localDecls body.layouts = MirStepNode.step sorry := by sorry
    sorry

inductive WellTypedLM2_3SwitchInt
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (discr : MirAst.Operand) (targets : SwitchTargets) : Prop where
  | mk (ty : Ty)
       (wt_discr : WellTypedLM2_2Operand body env stEnv discr ty)

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
  rcases hwt with ⟨ty, hwt_discr⟩
  have hbbt : bb.terminator = ⟨.switchInt discr targets, bb.terminator.span⟩ := by
    cases hb : bb.terminator with | mk kind span =>
      rw [hb] at hterm
      change kind = _ at hterm
      subst hterm
      rfl
  rw [hbbt]
  have hfr_exc : FrameRelLM2_2Except body env none m.machine s.frame topFrame :=
      FrameRelLM2_2Except.of_frameRel none hframe
  have hop_sim := evalLM2_2Operand_except hframes hfr_exc
    (fun j hj _ => hinit_env j hj)
    (fun j hj _ => himm_env j hj)
    (by nofun) hwt_discr s.memory.globals none
  generalize ha_op : evalOperand s.frame.locals discr [] s.memory.globals body.layouts = aOp at hop_sim
  generalize hm_op : (annealEvalOperand body.localDecls body.layouts (translateOperand discr) none >>=
    annealReadImmediate) m = mOp at hop_sim
  cases hop_sim with
  | ub m' msg =>
    have hm_term' : translateTerminator { kind := TerminatorKind.switchInt discr targets, span := bb.terminator.span } =
        { sourceInfo := defaultSourceInfo,
          kind := .SwitchInt (translateOperand discr) (translateSwitchTargets targets) } := rfl
    have hdisc : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m = (m', .error (.undefinedBehavior msg)) := by
      sorry
    have hleft : evalTerminator s { kind := TerminatorKind.switchInt discr targets, span := bb.terminator.span } (some body) = MirStepNode.fail .ub := by
      unfold evalTerminator
      dsimp only
      rw [hbor, hcaller, ha_op]
    have hright : Miri.Interpreter.ControlFlow.evalTerminator (annealTerminatorHooks body.localDecls body.layouts) ()
          (translateTerminator { kind := TerminatorKind.switchInt discr targets, span := bb.terminator.span }) m =
        (m', Except.error (Miri.Interpreter.StepError.undefinedBehavior msg)) := by
      rw [hm_term']
      exact evalTerminator_switchInt_error _ () _ _ _ m m' _ hdisc
    simp only [hleft, hright]
    sorry
  | ok =>
    have hm_term' : translateTerminator { kind := TerminatorKind.switchInt discr targets, span := bb.terminator.span } =
        { sourceInfo := defaultSourceInfo,
          kind := .SwitchInt (translateOperand discr) (translateSwitchTargets targets) } := rfl
    have hdisc : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m = (m, .ok sorry) := by
      sorry
    have hcmp : ∀ val target_b, (val, target_b) ∈ targets.branches →
      (annealTerminatorHooks body.localDecls body.layouts).compareSwitchCase () sorry val m = (m, .ok (Nat.beq sorry val)) := by
      sorry
    have hleft : evalTerminator s { kind := TerminatorKind.switchInt discr targets, span := bb.terminator.span } (some body) =
        MirStepNode.step sorry := sorry
    have hright : Miri.Interpreter.ControlFlow.evalTerminator (annealTerminatorHooks body.localDecls body.layouts) ()
          (translateTerminator { kind := TerminatorKind.switchInt discr targets, span := bb.terminator.span }) m =
        Miri.Interpreter.ControlFlow.goToBlock sorry m := by
      sorry
    simp only [hleft, hright]
    sorry

end LeanMiriSpec.Correspondence
