import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.Pass

-- anneal-audit: policy=file-local-axioms

/-!
Axiomatic context test for Layer 1B / Layer 2 (`ITreeMachine`, cross-effect
coinductive `WeakObsRef` compiler passes, `WeakRef` verifier passes, and
non-vacuous prefix projection).
-/

namespace AxiomaticSimulation

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.Pass

axiom ProgSrc : Type
axiom ProgTgt : Type
axiom ProgVer : Type
axiom StateSrc : Type
axiom StateTgt : Type
axiom StateVer : Type
axiom Obs : Type
axiom Val : Type

axiom E_src : Effect.{0}
axiom E_tgt : Effect.{0}
axiom instFaultSrc : FaultEffect E_src
axiom instFaultTgt : FaultEffect E_tgt
attribute [instance] instFaultSrc instFaultTgt

axiom M_src : ITreeMachine ProgSrc StateSrc E_src (Outcome Val)
axiom M_tgt : ITreeMachine ProgTgt StateTgt E_tgt (Outcome Val)
axiom M_ver : ITreeMachine ProgVer StateVer E_src (Outcome Val)

axiom proj_src : EffectObs E_src Obs
axiom proj_tgt : EffectObs E_tgt Obs

axiom compile : ProgSrc → ProgTgt
axiom verify : ProgSrc → ProgVer

axiom ax_weakObsRef :
  ∀ p : ProgSrc,
    WeakObsRef proj_tgt proj_src (M_tgt.run (compile p)) (M_src.run p)

axiom ax_ver_weakRef :
  ∀ p : ProgSrc, WeakRef (M_src.run p) (M_ver.run (verify p))

axiom Q : Spec (BehaviorSet (ObsPrefix Obs (Outcome Val)))
axiom p₀ : ProgSrc
axiom ax_p₀_verified :
  (NoUBObsSpec Obs (Outcome Val)).holds (MachineSemantics M_ver proj_src (verify p₀)) ∧
  Q.holds (MachineSemantics M_ver proj_src (verify p₀))

theorem axiomaticCompilerPass (p : ProgSrc) :
    CompilerPass
      (MachineSemantics M_src proj_src)
      (MachineSemantics M_tgt proj_tgt)
      (NoUBObsSpec Obs (Outcome Val)) id p (compile p) :=
  compilerPass_of_weakObsRef M_src proj_src M_tgt proj_tgt (ax_weakObsRef p)

theorem axiomaticCompiles (p : ProgSrc) :
    Compiles
      (M_src.toLanguage proj_src)
      (M_tgt.toLanguage proj_tgt)
      id p (compile p) :=
  compiles_of_weakObsRef M_src proj_src M_tgt proj_tgt (ax_weakObsRef p)

theorem axiomaticVerifierPass (p : ProgSrc) :
    VerifierPass
      (MachineSemantics M_src proj_src)
      (MachineSemantics M_ver proj_src)
      (NoUBObsSpec Obs (Outcome Val)) id p (verify p) :=
  verifierPass_of_weakRef M_src M_ver proj_src (ax_ver_weakRef p)

theorem axiomatic_source_treeSafe_and_non_vacuous :
    TreeSafe (M_src.run p₀) ∧
    ∃ pref : ObsPrefix Obs (Outcome Val),
      pref.outcome.isSafe ∧ MachineSemantics M_src proj_src p₀ pref := by
  have hnoUB_src :
      (NoUBObsSpec Obs (Outcome Val)).holds (MachineSemantics M_src proj_src p₀) :=
    VerifierPass.reflect_guard (axiomaticVerifierPass p₀) (fun h => h) ax_p₀_verified.1
  exact
    ⟨(noUBObsSpec_holds_iff_treeSafe proj_src (M_src.run p₀)).mp hnoUB_src,
     exists_safe_obsPrefix proj_src (M_src.run p₀)⟩

theorem axiomatic_compiled_target_satisfies_Q :
    Q.holds (MachineSemantics M_tgt proj_tgt (compile p₀)) :=
  anneal_is_correct
    (MachineSemantics M_src proj_src)
    (MachineSemantics M_ver proj_src)
    (MachineSemantics M_tgt proj_tgt)
    (NoUBObsSpec Obs (Outcome Val))
    (NoUBObsSpec Obs (Outcome Val))
    some compile id monotone_id axiomaticCompilerPass
    p₀ p₀ (verify p₀) id rfl
    (axiomaticVerifierPass p₀) (fun _ h => h)
    ax_p₀_verified.1 Q ax_p₀_verified.2

end AxiomaticSimulation
