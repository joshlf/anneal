# Reproduction Guide — `FF-1.1`: `Anneal.MirFuelFree` (Kleene Monotonicity & Fuel-Free WP/Eval)

## Overview

`theory/Anneal/MirFuelFree.lean` (imported by `theory/Anneal.lean` without modifying `SymbolicEval.lean`) establishes:

1. **Kleene Fuel Monotonicity & Conjunction**:
   - `wpCoalBounded_mono_fuel`, `wpCoalBounded_mono_both`, and `wpCoalBounded_conj` across `.ret`, `.tau`, and `.vis` branches.
   - `wpMirExecSym_mono`, `wpMirSym_mono`, `wpMirBounded_mono`, `wpMirExecNoCallSym_mono`, `wpMirNoCallSym_mono`, `wpMirExecUbWaivedSym_mono`, `wpMirUbWaivedSym_mono`, `wpMirExecModularSym_mono`, `wpMirModularSym_mono`, `wpMirExecTraceSym_mono`, `wpMirTraceSym_mono`, `wpMirTraceBounded_mono`, `wpMirSilentBounded_mono`.
   - `runMirExecBounded_mono`, `runMirBounded_mono`, `runMirExecBounded_det`, `runMirBounded_det`, `runMirTauToRet_mono`, `runMirTauToBlock_mono`, `runMirToBlock_mono`, `runMirToBinarySwitch_mono`, `checkMirBoolExecBounded_mono`, `checkMirBoolBounded_mono`.
2. **Fuel-Free Predicates & Determinism (`MirWpConverges`, `MirConverges`, `MirNoCallWpConverges`, `MirUbWaivedWpConverges`, `MirModularWpConverges`, `MirTraceWpConverges`)**:
   - `MirWpConverges`, `MirExecWpConverges`, `MirConverges`, `MirExecConverges`, `MirNoCallWpConverges`, `MirUbWaivedWpConverges`, `MirModularWpConverges`, `MirTraceWpConverges`, `MirTraceStepsConverges`.
   - `MirWpConverges.mono`, `MirWpConverges.of_wpMirSym`, `MirWpConverges.of_mirConverges`, `MirWpConverges.conj`, `MirUbWaivedWpConverges.conj`, `MirModularWpConverges.conj`, `MirTraceWpConverges.conj`, `MirWpConverges.not_false`, `MirWpConverges.exists_outcome`, `MirConverges.det`, `MirConverges.iff_wpConverges_of_det`.
3. **Fuel-Free Step & Sequential Composition (`step` & `bind`)**:
   - `MirWpConverges.step`, `MirWpConverges.step_tau`, `MirWpConverges.step_emit`, `MirWpConverges.ret_of_step`, `MirWpConverges.bind`, `MirWpConverges.bind_reachState`.
   - `MirStepsConverges.step`, `MirStepsConverges.trans`, `MirReachState.refl`, `MirReachState.trans`, `MirNoCallWpConverges.step`, `MirNoCallWpConverges.bind`, `MirUbWaivedWpConverges.step`, `MirUbWaivedWpConverges.bind`, `MirModularWpConverges.step`, `MirModularWpConverges.bind`, `MirTraceStepsConverges.step`, `MirTraceStepsConverges.step_tau`, `MirTraceStepsConverges.step_emit`, `MirTraceStepsConverges.trans`, `MirTraceStepsConverges.of_runMirTauToBlock`, `MirTraceWpConverges.step`, `MirTraceWpConverges.bind`, `MirTraceWpConverges.bind_silent`, `MirTraceWpConverges.of_runMirTauToRet`, `MirConverges.bind`.
4. **Callee-Aware (`BRIEF-3.2`) State Initialization & Adequacy Bridges Across All 7 Trusted Certificates**:
   - `Memory.withDefaultCallees`, `initMachineStateWithMemoryAndCallees`, `mirCallTreeWithCallees`, `mirStatefulTreeWithCallees`, `MirBoolPredicateHoldsWithCallees`, `RootActiveMemory`.
   - `dwp_of_mirWpConverges`, `dwlp_of_mirWpConverges`, `dwp_mirCallTreeWithCallees_of_mirWpConverges`, `dwp_mirStatefulTreeWithCallees_of_mirWpConverges`, `dwp_of_mirNoCallWpConverges`, `dwp_of_mirUbWaivedWpConverges`, `dwlp_of_mirUbWaivedWpConverges`, `dwp_of_mirModularWpConverges`, `dwlp_of_mirModularWpConverges`, `dwp_of_mirTraceWpConverges`, `dwlp_of_mirTraceWpConverges`, `mirBoolPredicateHoldsWithCallees_of_wpConverges`.
   - `verifyMirSafe_of_wpConverges`, `verifyMirNoPanic_of_wpConverges`, `verifyStatefulMirSafe_of_wpConverges`, `verifyStatefulMirNoPanic_of_wpConverges`, `verifyTotalMir_of_wpConverges`, `verifyStatefulEquivMir_of_wpConverges`, `verifyUbExceptionMir_of_wpConverges`, `verifyModularContractMir_of_wpConverges`, `verifyTraceMir_of_wpConverges`.
   - `dischargeStatelessEq_of_wpConverges`, `dischargeStatefulEq_of_wpConverges`, `verifyWellTypedScalarArg1_of_wpConverges`, `verifyWellTypedSafeScalarArg1_of_wpConverges`, `verifyWellTypedScalarArg2_of_wpConverges`, `verifyWellTypedSafeScalarArg2_of_wpConverges`.
5. **Concrete Multi-Block Fuel-Free Verification Witnesses (All 7 Trusted Certificates)**:
   - `multiBlockPipeline_stage1_converges`, `multiBlockPipeline_stage2_converges`, `multiBlockPipeline_wpConverges`, `multiBlockPipeline_noCallWpConverges`, `multiBlockPipeline_ubWaivedWpConverges`, `multiBlockPipeline_modularWpConverges`, `multiBlockPipeline_traceWpConverges`, `multiBlockPipeline_converges`, `multiBlockPipeline_withMemoryAndCallees_wpConverges`, `multiBlockPipeline_withCallees_wpConverges`.
   - `branchingTracePipeline_stage1_traceStepsConverges`, `branchingTracePipeline_stage2_traceWpConverges`, `branchingTracePipeline_traceWpConverges` (non-empty `MirObs.event` trace composition via `MirTraceWpConverges.bind`).
   - `verify_multiBlockPipelineClaim`, `verify_multiBlockPipelineStatefulClaim`, `verify_multiBlockPipelineTotalClaim`, `verify_multiBlockPipelineEquivClaim`, `verify_multiBlockPipelineUbExceptionClaim`, `verify_multiBlockPipelineModularClaim`, `verify_multiBlockPipelineTraceClaim`, `verify_branchingTracePipelineTraceClaim`.
   - **Non-vacuous Test Witnesses**: `multiBlockPipelineClaim_nonVacuous`, `multiBlockPipelineStatefulClaim_nonVacuous`, `multiBlockPipelineTotalClaim_nonVacuous`, `multiBlockPipelineEquivClaim_nonVacuous`, `multiBlockPipelineUbExceptionClaim_nonVacuous`, `multiBlockPipelineUbExceptionClaim_strictDomain_nonVacuous`, `multiBlockPipelineUbExceptionClaim_waivedDomain_nonVacuous`, `multiBlockPipelineModularClaim_nonVacuous`, `multiBlockPipelineTraceClaim_nonVacuous`, `branchingTracePipelineTraceClaim_nonVacuous`.

## Step-by-Step Verification Commands

Run from `/usr/local/google/Projects/anneal-workspace/anneal-wt-ff-1-1`:

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# 1. Verify zero unfinished-task markers
./ci/check_todo.sh

# 2. Fast trusted-base closure & axiom audit (verifies zero sorryAx and zero custom axioms)
python3 trusted/audit/check_trusted.py --fast

# 3. Fast single-file kernel check of theory/Anneal/MirFuelFree.lean (~5s)
cd examples && anneal-lean-run --mode file --concurrency 2 -- lake env lean ../theory/Anneal/MirFuelFree.lean && cd ..

# 4. Full Anneal library build under hardware-bounded cgroup limits
cd examples && anneal-lean-run --mode build --concurrency 2 -- lake build Anneal && cd ..
```

## Expected Output

- `./ci/check_todo.sh`: exits `0` with empty output.
- `python3 trusted/audit/check_trusted.py --fast`: prints `PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary` with `axioms=['propext', 'Classical.choice', 'Quot.sound']`.
- `lake build Anneal`: prints `Build completed successfully` with zero warnings and zero `sorryAx`.
