/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

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
  | mk (decl : LocalDecl) (hdecl : get? body.localDecls dstIdx = some decl)

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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by sorry

inductive WellTypedLM2_3SetDiscriminant
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (place : Place) (variantIdx : VariantIdx) : Prop where
  | mk (decl : LocalDecl) (hdecl : get? body.localDecls place.local_ = some decl)

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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by sorry

inductive WellTypedLM2_3DiscriminantRead
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (place : Place) : Prop where
  | mk (decl : LocalDecl) (hdecl : get? body.localDecls dstIdx = some decl)

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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by sorry

inductive WellTypedLM2_3Downcast
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (place : Place) (variantIdx : VariantIdx) : Prop where
  | mk (decl : LocalDecl) (hdecl : get? body.localDecls dstIdx = some decl)

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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by sorry

inductive WellTypedLM2_3SwitchInt
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (discr : MirAst.Operand) (targets : SwitchTargets) : Prop where
  | mk (h : True)

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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by sorry

end LeanMiriSpec.Correspondence
