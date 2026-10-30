import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.Pass
import Anneal.EffectWP
import Anneal.ITreeWP
import Anneal.Scalars
import Anneal.Memory
import Anneal.BitValidity
import Anneal.UnsafeObligations
import Anneal.SepLogic
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Anneal.Rustc.V2026_06_01.SymReflect
import Anneal.FunctionalTranslation

namespace Anneal

/-!
Top-level umbrella module exporting the untrusted verification library
(`theory/`) layered over `Trusted`.
-/

export Anneal.Refinement (
  VerifierPass CompilerPass BugFinderPass SanitizerPass ExactPass
  Compiles Abstracts
  y_diagram_sound anneal_is_correct
  verify_on_through_passes verify_through_passes
)

export Anneal.Effect (
  EffectHom
)

export Anneal.ITree (
  StrongBisim strongBisim_iff_eq
  Eutt WeakSim WeakCSim WeakRef TotalWeakRef
  CoAlways Eventually InfinitelyOften
  Stream' FollowsStream followsStream_deterministic
  EnvStrategy reaches_iff_exists_strategy
  BridgeContract bridgeTree
)

export Anneal.Pass (
  VerifiedVerifierChecker VerifiedCompilerChecker VerifiedExactChecker
  ITreeMachine EffectObs ObsPrefix UBClosedObsPrefixes WeakObsRef
  compilerPass_of_weakObsRef compiles_of_weakObsRef
  verifierPass_of_weakRef exactPass_of_eutt
  CFGSystem TauCFGSystem
)

export Anneal.EffectWP (
  StateEffectWP EffectWP PureEffectWP
  PureSoundWP TraceSoundWP
  emptyWP failWP obsIgnoreWP obsTraceWP
  pickWP demonicWP witnessWP angelicWP stateWP
  unconstrainedCallWP CallContract contractCallWP eventTraceWP
)

export Anneal.ITreeWP (
  DWLP DWP
  dwlp_pure_adequacy dwlp_trace_adequacy dwp_pure_adequacy
  dwp_interp dwlp_interp dwp_interpState dwlp_interpState
  wpCoalBounded dwp_cofix_of_wpCoalBounded dwlp_cofix_of_wpCoalBounded
)

/-- Smoke-test witness exported from `Anneal`. -/
theorem trivial_witness : True := trivial

end Anneal
