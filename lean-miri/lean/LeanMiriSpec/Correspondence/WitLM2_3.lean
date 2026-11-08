import LeanMiriSpec.Correspondence.SimLM2_3
import LeanMiriSpec.Correspondence.WitLM2_2

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace LeanMiriSpec.Correspondence.Witness

def lm23StEnv : LM2_2StaticEnv :=
  { initLocals := [], immLocals := [] }

theorem wit_evalRvalue_aggregate_enum_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (defPath : DefPath) (variantIdx : VariantIdx)
    (ops : List MirAst.Operand),
  WellTypedLM2_3EnumAggregate body env stEnv dstIdx defPath variantIdx ops := by
  refine ⟨lm22UnpaddedBody, lm22UnpaddedEnv, lm23StEnv, 1, "lm22::UnpaddedTriple", 0, [],
    .mk lm22UnpaddedDecl lm22UnpaddedFields lm22UnpaddedPaths (by rfl) (by rfl) ⟨[], rfl⟩ lm22Unpadded_validStructLayout⟩

theorem wit_step_setDiscriminant_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (place : Place) (variantIdx : VariantIdx),
  WellTypedLM2_3SetDiscriminant body env stEnv place variantIdx := by
  refine ⟨lm22UnpaddedBody, lm22UnpaddedEnv, lm23StEnv, ⟨1, []⟩, 0,
    .mk lm22UnpaddedDecl "lm22::UnpaddedTriple" lm22UnpaddedFields lm22UnpaddedPaths (by rfl) (by rfl) (by rfl) ⟨[], rfl⟩ lm22Unpadded_validStructLayout⟩

theorem wit_evalRvalue_discriminant_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (place : Place),
  WellTypedLM2_3DiscriminantRead body env stEnv dstIdx place := by
  refine ⟨lm22UnpaddedBody, lm22UnpaddedEnv, lm23StEnv, 1, ⟨1, []⟩,
    .mk lm22UnpaddedDecl lm22UnpaddedDecl "lm22::UnpaddedTriple" lm22UnpaddedFields lm22UnpaddedPaths (by rfl) (by rfl) (by rfl) ⟨[], rfl⟩ lm22Unpadded_validStructLayout⟩

theorem wit_evalProjection_downcast_field_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (base : Local) (projs : List ProjectionElem)
    (variantName : String) (variantIdx : VariantIdx) (field : FieldIdx) (ty : Ty),
  WellTypedLM2_3Downcast body env stEnv dstIdx base projs variantName variantIdx field ty := by
  refine ⟨lm22UnpaddedBody, lm22UnpaddedEnv, lm23StEnv, 1, 1, [], "lm22::UnpaddedTriple", 0, 0, lm22U32Ty, .mk lm22UnpaddedDecl⟩

theorem wit_enum_match_switchInt_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (discr : MirAst.Operand) (targets : SwitchTargets),
  WellTypedLM2_3SwitchInt body env stEnv discr targets := by
  refine ⟨lm22UnpaddedBody, lm22UnpaddedEnv, lm23StEnv, .constant (lm22ConstU32 0), { branches := [], otherwise := 0 },
    .mk lm22U32Ty (lm22_constU32_wt 0 (by decide) (by rfl))⟩

end LeanMiriSpec.Correspondence.Witness
