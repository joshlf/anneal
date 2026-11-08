import LeanMiriSpec.Correspondence.SimLM2_3
import LeanMiriSpec.Correspondence.WitLM2_2

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace LeanMiriSpec.Correspondence.Witness

def lm23StEnv : LM2_2StaticEnv :=
  { initLocals := [], immLocals := [] }

theorem lm22Unpadded_ops_ok : WellTypedLM2_2AggFields lm22UnpaddedBody lm22UnpaddedEnv 1 (translateTy lm22UnpaddedDecl.ty lm22UnpaddedBody.layouts) lm22UnpaddedFields lm22UnpaddedPaths lm23StEnv 0 0 [.constant (lm22ConstU32 10), .constant (lm22ConstU32 20), .constant (lm22ConstU32 30)] :=
  .cons lm23StEnv 0 0 1 _ _ trivial
    (.primLeaf (by decide) _ (lm22_constU32_wt 10 (by decide) (by rfl)) rfl lm22_u32_prim rfl rfl rfl rfl (by decide) rfl)
  (.cons _ 1 1 2 _ _ trivial
    (.primLeaf (by decide) _ (lm22_constU32_wt 20 (by decide) (by rfl)) rfl lm22_u32_prim rfl rfl rfl rfl (by decide) rfl)
  (.cons _ 2 2 3 _ _ trivial
    (.primLeaf (by decide) _ (lm22_constU32_wt 30 (by decide) (by rfl)) rfl lm22_u32_prim rfl rfl rfl rfl (by decide) rfl)
  (.nil _ 3)))

theorem wit_evalRvalue_aggregate_enum_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (defPath : DefPath) (variantIdx : VariantIdx)
    (ops : List MirAst.Operand),
  WellTypedLM2_3EnumAggregate body env stEnv dstIdx defPath variantIdx ops := by
  refine ⟨lm22UnpaddedBody, lm22UnpaddedEnv, lm23StEnv, 1, "lm22::UnpaddedTriple", 0, [.constant (lm22ConstU32 10), .constant (lm22ConstU32 20), .constant (lm22ConstU32 30)],
    WellTypedLM2_3EnumAggregate.mk (body := lm22UnpaddedBody) (env := lm22UnpaddedEnv) (stEnv := lm23StEnv) (dstIdx := 1) (defPath := "lm22::UnpaddedTriple") (variantIdx := 0) (ops := _) lm22UnpaddedDecl lm22UnpaddedFields lm22UnpaddedPaths rfl rfl ⟨[], rfl⟩ lm22Unpadded_validStructLayout lm22Unpadded_ops_ok⟩

theorem wit_step_setDiscriminant_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (place : Place) (variantIdx : VariantIdx),
  WellTypedLM2_3SetDiscriminant body env stEnv place variantIdx := by
  refine ⟨lm22UnpaddedBody, lm22UnpaddedEnv, lm23StEnv, ⟨1, []⟩, 0,
    WellTypedLM2_3SetDiscriminant.mk (body := lm22UnpaddedBody) (env := lm22UnpaddedEnv) (stEnv := lm23StEnv) (place := ⟨1, []⟩) (variantIdx := 0) lm22UnpaddedDecl "lm22::UnpaddedTriple" lm22UnpaddedFields lm22UnpaddedPaths rfl rfl rfl ⟨[], rfl⟩ lm22Unpadded_validStructLayout⟩

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
  refine ⟨lm22UnpaddedBody, lm22UnpaddedEnv, lm23StEnv, 1, 1, [], "lm22::UnpaddedTriple", 0, 0, lm22U32Ty, WellTypedLM2_3Downcast.mk (body := lm22UnpaddedBody) (env := lm22UnpaddedEnv) (stEnv := lm23StEnv) (dstIdx := 1) (base := 1) (projs := []) (variantName := "lm22::UnpaddedTriple") (variantIdx := 0) (field := 0) (ty := lm22U32Ty) lm22UnpaddedDecl lm22UnpaddedDecl "lm22::UnpaddedTriple" lm22UnpaddedFields lm22UnpaddedPaths rfl rfl rfl ⟨[], rfl⟩ lm22Unpadded_validStructLayout⟩

theorem wit_enum_match_switchInt_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (discr : MirAst.Operand) (targets : SwitchTargets),
  WellTypedLM2_3SwitchInt body env stEnv discr targets := by
  refine ⟨lm22UnpaddedBody, lm22UnpaddedEnv, lm23StEnv, .copy ⟨1, []⟩, { branches := [], otherwise := 0 },
    WellTypedLM2_3SwitchInt.mk (body := lm22UnpaddedBody) (env := lm22UnpaddedEnv) (stEnv := lm23StEnv) (discr := .copy ⟨1, []⟩) (targets := { branches := [], otherwise := 0 }) lm22UnpaddedDecl false 1 rfl rfl⟩

end LeanMiriSpec.Correspondence.Witness

