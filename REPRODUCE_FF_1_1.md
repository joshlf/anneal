# Reproduction Guide — `FF-1.1`: `Anneal.MirFuelFree` (Kleene Monotonicity & Fuel-Free WP/Eval)

## Overview

`theory/Anneal/MirFuelFree.lean` (imported by `theory/Anneal.lean` without modifying `SymbolicEval.lean`) establishes:

1. **Kleene Fuel Monotonicity**:
   - `wpCoalBounded_mono_fuel` and `wpCoalBounded_mono_both` across `.ret`, `.tau`, and `.vis` branches.
   - `wpMirExecSym_mono`, `wpMirSym_mono`, `wpMirBounded_mono`, `wpMirExecNoCallSym_mono`, `wpMirNoCallSym_mono`, `wpMirExecUbWaivedSym_mono`, `wpMirUbWaivedSym_mono`, `wpMirExecModularSym_mono`, `wpMirModularSym_mono`.
   - `runMirExecBounded_mono`, `runMirBounded_mono`, `runMirExecBounded_det`, `runMirBounded_det`, `runMirTauToRet_mono`, `runMirTauToBlock_mono`, `runMirToBlock_mono`, `runMirToBinarySwitch_mono`, `checkMirBoolExecBounded_mono`, `checkMirBoolBounded_mono`.
2. **Fuel-Free Predicates & Determinism (`MirWpConverges`, `MirConverges`, `MirNoCallWpConverges`)**:
   - `MirWpConverges`, `MirExecWpConverges`, `MirConverges`, `MirExecConverges`, `MirNoCallWpConverges`.
   - `MirWpConverges.mono`, `MirWpConverges.of_wpMirSym`, `MirWpConverges.of_mirConverges`, `MirWpConverges.conj`, `MirWpConverges.not_false`, `MirWpConverges.exists_outcome`, `MirConverges.det`, `MirConverges.iff_wpConverges_of_det`.
3. **Fuel-Free Step & Sequential Composition (`step` & `bind`)**:
   - `MirWpConverges.step`, `MirWpConverges.step_tau`, `MirWpConverges.step_emit`, `MirWpConverges.ret_of_step`, `MirWpConverges.bind`, `MirWpConverges.bind_reachState`.
   - `MirStepsConverges.step`, `MirStepsConverges.trans`, `MirReachState.refl`, `MirReachState.trans`, `MirNoCallWpConverges.step`, `MirNoCallWpConverges.bind`, `MirConverges.bind`.
4. **Callee-Aware (`BRIEF-3.2`) State Initialization & Adequacy Bridges**:
   - `Memory.withDefaultCallees`, `initMachineStateWithMemoryAndCallees`, `mirCallTreeWithCallees`, `mirStatefulTreeWithCallees`, `RootActiveMemory`.
   - `dwp_of_mirWpConverges`, `dwlp_of_mirWpConverges`, `dwp_mirCallTreeWithCallees_of_mirWpConverges`, `dwp_mirStatefulTreeWithCallees_of_mirWpConverges`, `dwp_of_mirNoCallWpConverges`.
   - `verifyMirSafe_of_wpConverges`, `verifyMirNoPanic_of_wpConverges`, `verifyStatefulMirSafe_of_wpConverges`, `verifyStatefulMirNoPanic_of_wpConverges`, `verifyTotalMir_of_wpConverges`, `verifyStatefulEquivMir_of_wpConverges`.
5. **Concrete Multi-Block Fuel-Free Verification Witnesses**:
   - `multiBlockPipeline_stage1_converges`, `multiBlockPipeline_stage2_converges`, `multiBlockPipeline_wpConverges`, `multiBlockPipeline_converges`, `multiBlockPipeline_withMemoryAndCallees_wpConverges`, `multiBlockPipeline_withCallees_wpConverges`.
   - `verify_multiBlockPipelineClaim`, `verify_multiBlockPipelineStatefulClaim`, `verify_multiBlockPipelineTotalClaim`.

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
