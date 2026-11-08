/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM2_3

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace LeanMiriSpec.Correspondence.Witness

theorem wit_evalRvalue_aggregate_enum_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (defPath : DefPath) (variantIdx : VariantIdx)
    (ops : List MirAst.Operand),
  WellTypedLM2_3EnumAggregate body env stEnv dstIdx defPath variantIdx ops := by sorry

theorem wit_step_setDiscriminant_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (place : Place) (variantIdx : VariantIdx),
  WellTypedLM2_3SetDiscriminant body env stEnv place variantIdx := by sorry

theorem wit_evalRvalue_discriminant_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (place : Place),
  WellTypedLM2_3DiscriminantRead body env stEnv dstIdx place := by sorry

theorem wit_evalProjection_downcast_field_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (base : Local) (variantIdx : VariantIdx),
  WellTypedLM2_3Downcast body env stEnv dstIdx ⟨base, []⟩ variantIdx := by sorry

theorem wit_enum_match_switchInt_simulation :
  ∃ (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (discr : MirAst.Operand) (targets : SwitchTargets),
  WellTypedLM2_3SwitchInt body env stEnv discr targets := by sorry

end LeanMiriSpec.Correspondence.Witness
