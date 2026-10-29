import Anneal.Refinement

-- anneal-audit: policy=file-local-axioms

/-!
Axiomatic context tests for Layer 1A (`Trusted.Refinement` and
`Anneal.Refinement`) over `LE` and `Std.IsPreorder`.
-/

namespace Anneal.Tests.AxiomaticYDiagram

open Trusted.Refinement
open Anneal.Refinement

axiom Artifact : Type
axiom MirProgram : Type
axiom MidVerifProgram : Type
axiom FinalVerifProgram : Type
axiom OptMirProgram : Type
axiom TgtProgram : Type

axiom MirBeh : Type
axiom MidVerifBeh : Type
axiom FinalVerifBeh : Type
axiom OptMirBeh : Type
axiom TgtBeh : Type

axiom instLEMir : LE MirBeh
axiom instLEMidVerif : LE MidVerifBeh
axiom instLEFinalVerif : LE FinalVerifBeh
axiom instLEOptMir : LE OptMirBeh
axiom instLETgt : LE TgtBeh
attribute [instance] instLEMir instLEMidVerif instLEFinalVerif instLEOptMir instLETgt

axiom instPreorderMir : Std.IsPreorder MirBeh
axiom instPreorderMidVerif : Std.IsPreorder MidVerifBeh
axiom instPreorderFinalVerif : Std.IsPreorder FinalVerifBeh
axiom instPreorderOptMir : Std.IsPreorder OptMirBeh
axiom instPreorderTgt : Std.IsPreorder TgtBeh
attribute [instance] instPreorderMir instPreorderMidVerif instPreorderFinalVerif
  instPreorderOptMir instPreorderTgt

axiom MirSem : Semantics MirProgram MirBeh
axiom MidVerifSem : Semantics MidVerifProgram MidVerifBeh
axiom FinalVerifSem : Semantics FinalVerifProgram FinalVerifBeh
axiom OptMirSem : Semantics OptMirProgram OptMirBeh
axiom TgtSem : Semantics TgtProgram TgtBeh

axiom MirNoUB : Spec MirBeh
axiom MidVerifNoUB : Spec MidVerifBeh
axiom FinalVerifNoUB : Spec FinalVerifBeh
axiom OptMirNoUB : Spec OptMirBeh

axiom parseCapture : Artifact → Option MirProgram
axiom optimizeMir : MirProgram → OptMirProgram
axiom codegen : OptMirProgram → TgtProgram

axiom π_opt : MirBeh → OptMirBeh
axiom π_cg : OptMirBeh → TgtBeh
axiom h_mono_opt : Monotone π_opt
axiom h_mono_cg : Monotone π_cg

axiom h_optimize_pass :
  ∀ p, CompilerPass MirSem OptMirSem MirNoUB π_opt p (optimizeMir p)
axiom h_codegen_pass :
  ∀ p, CompilerPass OptMirSem TgtSem OptMirNoUB π_cg p (codegen p)
axiom h_opt_preserves_noUB :
  ∀ b_mir, MirNoUB.holds b_mir → OptMirNoUB.holds (π_opt b_mir)

axiom π_v1 : MidVerifBeh → MirBeh
axiom π_v2 : FinalVerifBeh → MidVerifBeh
axiom h_mono_v1 : Monotone π_v1

axiom h_reflect_v2_to_v1 :
  ∀ b_final, FinalVerifNoUB.holds b_final → MidVerifNoUB.holds (π_v2 b_final)
axiom h_reflect_v1_to_mir :
  ∀ b_mid, MidVerifNoUB.holds b_mid → MirNoUB.holds (π_v1 b_mid)

axiom artifact₀ : Artifact
axiom p_mir₀ : MirProgram
axiom p_mid₀ : MidVerifProgram
axiom p_final₀ : FinalVerifProgram

axiom h_capture₀ : parseCapture artifact₀ = some p_mir₀
axiom h_vpass₁ : VerifierPass MirSem MidVerifSem MidVerifNoUB π_v1 p_mir₀ p_mid₀
axiom h_vpass₂ : VerifierPass MidVerifSem FinalVerifSem FinalVerifNoUB π_v2 p_mid₀ p_final₀
axiom h_final_noUB₀ : FinalVerifNoUB.holds (FinalVerifSem p_final₀)

axiom targetSpec : Spec TgtBeh
axiom h_spec_on_final₀ :
  targetSpec.holds (π_cg (π_opt (π_v1 (π_v2 (FinalVerifSem p_final₀)))))

theorem composed_compiler_pass (p : MirProgram) :
    CompilerPass MirSem TgtSem MirNoUB (fun b => π_cg (π_opt b))
      p (codegen (optimizeMir p)) :=
  CompilerPass.comp (h_optimize_pass p) (h_codegen_pass (optimizeMir p)) h_mono_cg
    (fun _ _ h_noUB h_ref =>
      OptMirNoUB.downward_closed h_ref (h_opt_preserves_noUB _ h_noUB))

theorem composed_verifier_pass :
    VerifierPass MirSem FinalVerifSem FinalVerifNoUB (fun b => π_v1 (π_v2 b))
      p_mir₀ p_final₀ :=
  VerifierPass.comp h_vpass₁ h_vpass₂ h_mono_v1
    (fun _ _ h_noUB h_ref =>
      MidVerifNoUB.downward_closed h_ref (h_reflect_v2_to_v1 _ h_noUB))

theorem reflected_mir_noUB : MirNoUB.holds (MirSem p_mir₀) :=
  VerifierPass.reflect_guard composed_verifier_pass
    (fun h_noUB => h_reflect_v1_to_mir _ (h_reflect_v2_to_v1 _ h_noUB))
    h_final_noUB₀

theorem axiomatic_end_to_end_target_spec :
    targetSpec.holds (TgtSem (codegen (optimizeMir p_mir₀))) :=
  anneal_is_correct
    MirSem FinalVerifSem TgtSem MirNoUB FinalVerifNoUB
    parseCapture (fun p => codegen (optimizeMir p)) (fun b => π_cg (π_opt b))
    (Monotone.comp h_mono_cg h_mono_opt)
    composed_compiler_pass
    artifact₀ p_mir₀ p_final₀ (fun b => π_v1 (π_v2 b)) h_capture₀
    composed_verifier_pass
    (fun _ h_noUB => h_reflect_v1_to_mir _ (h_reflect_v2_to_v1 _ h_noUB))
    h_final_noUB₀ targetSpec h_spec_on_final₀

/-! ## Query-Indexed `Language` / `Partial` Pipeline (`Compiles`, `Abstracts`) -/

axiom MirLang : Language
axiom MidVerifLang : Language
axiom FinalVerifLang : Language
axiom OptMirLang : Language
axiom TgtLang : Language

axiom optMirLang : MirLang.Prog → OptMirLang.Prog
axiom codegenLang : OptMirLang.Prog → TgtLang.Prog

axiom π_opt_lang : MirLang.Behavior → OptMirLang.Behavior
axiom π_cg_lang : OptMirLang.Behavior → TgtLang.Behavior
axiom h_mono_opt_lang : Monotone π_opt_lang
axiom h_mono_cg_lang : Monotone π_cg_lang

axiom h_compiles_opt : ∀ p, Compiles MirLang OptMirLang π_opt_lang p (optMirLang p)
axiom h_compiles_cg : ∀ p, Compiles OptMirLang TgtLang π_cg_lang p (codegenLang p)

axiom π_v1_lang : MidVerifLang.Behavior → MirLang.Behavior
axiom π_v2_lang : FinalVerifLang.Behavior → MidVerifLang.Behavior
axiom h_mono_v1_lang : Monotone π_v1_lang
axiom h_mono_v2_lang : Monotone π_v2_lang

axiom p_mir_lang₀ : MirLang.Prog
axiom p_mid_lang₀ : MidVerifLang.Prog
axiom p_final_lang₀ : FinalVerifLang.Prog

axiom h_abstracts₁ : Abstracts MidVerifLang MirLang π_v1_lang p_mid_lang₀ p_mir_lang₀
axiom h_abstracts₂ : Abstracts FinalVerifLang MidVerifLang π_v2_lang p_final_lang₀ p_mid_lang₀

axiom verifSpec₀ : FinalVerifLang.Behavior
axiom h_final_refines_spec₀ : FinalVerifLang.sem p_final_lang₀ ≤ verifSpec₀

axiom safetyPre₀ : MirLang.Query → Prop
axiom h_spec_wf_on₀ : π_v1_lang (π_v2_lang verifSpec₀) ≤ MirLang.WellFormedOn safetyPre₀
axiom h_spec_wf₀ : π_v1_lang (π_v2_lang verifSpec₀) ≤ MirLang.WellFormed

theorem composed_language_compiles (p : MirLang.Prog) :
    Compiles MirLang TgtLang (fun b => π_cg_lang (π_opt_lang b))
      p (codegenLang (optMirLang p)) :=
  Compiles.comp (h_compiles_opt p) (h_compiles_cg (optMirLang p)) h_mono_cg_lang

theorem composed_language_abstracts :
    Abstracts FinalVerifLang MirLang (fun b => π_v1_lang (π_v2_lang b))
      p_final_lang₀ p_mir_lang₀ :=
  Abstracts.comp h_abstracts₁ h_abstracts₂ h_mono_v1_lang

theorem axiomatic_verify_on_through_passes :
    MirLang.sem p_mir_lang₀ ≤ MirLang.WellFormedOn safetyPre₀ ∧
    TgtLang.sem (codegenLang (optMirLang p_mir_lang₀)) ≤
      π_cg_lang (π_opt_lang (π_v1_lang (π_v2_lang verifSpec₀))) :=
  verify_on_through_passes
    (Monotone.comp h_mono_cg_lang h_mono_opt_lang)
    (Monotone.comp h_mono_v1_lang h_mono_v2_lang)
    (composed_language_compiles p_mir_lang₀)
    composed_language_abstracts
    h_final_refines_spec₀
    h_spec_wf_on₀

theorem axiomatic_verify_through_passes :
    MirLang.sem p_mir_lang₀ ≤ MirLang.WellFormed ∧
    TgtLang.sem (codegenLang (optMirLang p_mir_lang₀)) ≤
      π_cg_lang (π_opt_lang (π_v1_lang (π_v2_lang verifSpec₀))) :=
  verify_through_passes
    (Monotone.comp h_mono_cg_lang h_mono_opt_lang)
    (Monotone.comp h_mono_v1_lang h_mono_v2_lang)
    (composed_language_compiles p_mir_lang₀)
    composed_language_abstracts
    h_final_refines_spec₀
    h_spec_wf₀

end Anneal.Tests.AxiomaticYDiagram
