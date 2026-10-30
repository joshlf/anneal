import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.Pass

-- anneal-audit: policy=file-local-axioms

/-!
Axiomatic context test for Layer 2 (`Anneal.Pass`: certificate checkers and
both resolved-label `CFGSystem` and `.tau`-erasing `TauCFGSystem` forwarder-block
elimination).
-/

namespace AxiomaticForwarder

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.Pass

axiom Prog : Type
axiom State : Type
axiom Obs : Type
axiom Val : Type
axiom BlockId : Type
axiom Cert : Type

axiom E : Effect.{0}
axiom instFault : FaultEffect E
attribute [instance] instFault

axiom proj : EffectObs E Obs
axiom sys : CFGSystem Prog State E Val BlockId
axiom ax_pureJump : PureJumpLaw sys
axiom ax_targetLabelIndep : TargetLabelIndependenceLaw sys
axiom ax_pcDispatch : PCDispatchLaw sys

axiom tauSys : TauCFGSystem Prog State E Val BlockId
axiom ax_tauLaw : TauForwarderLaw tauSys

axiom checkCert : Prog → Prog → Cert → Bool
axiom ax_check_exact :
  VerifiedExactChecker
    (MachineSemantics sys.machine proj)
    (MachineSemantics sys.machine proj)
    id id checkCert

axiom p₀ : Prog
axiom p_verif : Prog
axiom cert₀ : Cert
axiom b₀ : BlockId
axiom c₀ : BlockId

axiom ax_b₀_ne_c₀ : b₀ ≠ c₀
axiom ax_b₀_forwarder : sys.isForwarder p₀ b₀ c₀
axiom ax_b₀_tauForwarder : tauSys.isForwarder p₀ b₀ c₀
axiom ax_cert₀_ok : checkCert p₀ p_verif cert₀ = true

axiom Q : Spec (BehaviorSet (ObsPrefix Obs (Outcome Val)))
axiom ax_p_verif_holds :
  (NoUBObsSpec Obs (Outcome Val)).holds (MachineSemantics sys.machine proj p_verif) ∧
  Q.holds (MachineSemantics sys.machine proj p_verif)

theorem axiomatic_forwarder_exact
    (p : Prog) (b c : BlockId) (hne : b ≠ c) (hfwd : sys.isForwarder p b c) :
    ExactPass
      (MachineSemantics sys.machine proj)
      (MachineSemantics sys.machine proj)
      id id p (sys.redirectEdges p b c) :=
  eliminateForwarder_exactPass
    sys proj ax_pureJump ax_targetLabelIndep ax_pcDispatch p b c hne hfwd

theorem axiomatic_tau_forwarder_eutt_and_exact :
    Eutt (tauSys.machine.run p₀) (tauSys.machine.run (tauSys.redirectEdges p₀ b₀ c₀)) ∧
    ExactPass
      (MachineSemantics tauSys.machine proj)
      (MachineSemantics tauSys.machine proj)
      id id p₀ (tauSys.redirectEdges p₀ b₀ c₀) :=
  ⟨eliminateTauForwarder_eutt tauSys ax_tauLaw p₀ b₀ c₀ ax_b₀_ne_c₀ ax_b₀_tauForwarder,
   eliminateTauForwarder_exactPass tauSys proj ax_tauLaw p₀ b₀ c₀ ax_b₀_ne_c₀ ax_b₀_tauForwarder⟩

theorem axiomatic_cert_verifierPass :
    VerifierPass
      (MachineSemantics sys.machine proj)
      (MachineSemantics sys.machine proj)
      (NoUBObsSpec Obs (Outcome Val))
      id p₀ p_verif :=
  (ax_check_exact.toVerifierChecker (NoUBObsSpec Obs (Outcome Val))).sound ax_cert₀_ok

theorem axiomatic_cfg_y_diagram_sound :
    Q.holds (MachineSemantics sys.machine proj (sys.redirectEdges p₀ b₀ c₀)) ∧
    (NoUBObsSpec Obs (Outcome Val)).holds (MachineSemantics sys.machine proj p₀) :=
  y_diagram_sound
    (MachineSemantics sys.machine proj)
    (MachineSemantics sys.machine proj)
    (MachineSemantics sys.machine proj)
    (NoUBObsSpec Obs (Outcome Val))
    (NoUBObsSpec Obs (Outcome Val))
    id id monotone_id
    ((axiomatic_forwarder_exact p₀ b₀ c₀ ax_b₀_ne_c₀ ax_b₀_forwarder).toCompilerPass
      (NoUBObsSpec Obs (Outcome Val)))
    axiomatic_cert_verifierPass
    (fun _ h => h)
    ax_p_verif_holds.1 Q ax_p_verif_holds.2

end AxiomaticForwarder
