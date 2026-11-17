import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.Pass
import Anneal.EffectWP
import Anneal.ITreeWP
import Anneal.MirLoops
import Anneal.Scalars
import Anneal.Memory
import Anneal.BitValidity
import Anneal.FaultSiteCensus
import Anneal.UnsafeObligations
import Anneal.SepLogic
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Anneal.Rustc.V2026_06_01.SymReflect
import Anneal.Rustc.V2026_06_01.TraceCheck
import Anneal.FunctionalTranslation
import Anneal.MirFuelFree
import Anneal.PureMirExec
import Anneal.MirLiftCore
import Anneal.MirLiftBench
import Anneal.SepLogicLenses
import Anneal.PureLift

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

export Anneal.FaultSiteCensus (
  MirFaultClass FaultSite PropertyStatus PropertyRegistry
  allVerifiedRegistry unemittedRegistry registryWithStatus
  censusMirBodyFaultSites censusRvalueFaultClasses censusStmtFaultClasses censusTerminatorFaultClasses
  evalRvalue_ub_implies_mem_censusRvalue evalStmt_assign_rvalue_ub_justified
  evalStmt_assume_operand_ub_justified evalTerminator_switchInt_discr_ub_justified
  evalTerminator_assert_cond_ub_justified evalTerminator_call_args_ub_justified
  evalTerminator_tailCall_args_ub_justified
  evalTerminator_call_func_ub_justified evalTerminator_tailCall_func_ub_justified
  stepMirFn_fault_in_census stepMirFn_exposesUb_in_census
  CoverageVerdict reconcileFaultCoverage reconcileFaultCoverageWithRegistry
  stepMirFn_fault_in_discharged_of_reconciled initMachineState_mirStepsTop_reconciled_safety
  CoverageBatch reconcileCoverageBatch stepMirFn_exposesUb_in_batch_discharged
  reconcileCoverageBatchWellFormed reconcileCoverageBatchWellFormed_iff
  initMachineState_mirStepsInterproc_wellFormed_batch_safety
)

export Anneal.UnsafeObligations (
  evalOperand_deref_reconciled_of_obligations
  writePlaceValue_deref_reconciled_of_obligations
  evalStmt_offset_reconciled_of_validSliceRange
  evalCopyNonOverlapping_one_not_exposesUb_and_census_of_obligations
  evalStmt_deref_load_reconciled_of_obligations
  evalStmt_deref_store_reconciled_of_obligations
)

/-- Smoke-test witness exported from `Anneal`. -/
theorem trivial_witness : True := trivial

end Anneal
