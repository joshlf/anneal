<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproduction Guide for FF-2.2: Compositional Callee, Polymorphic,
# `#[external_spec]` & Pure `CallConv.rustIntrinsic` Call Resolution

This guide provides self-contained instructions for an independent reviewer or
CI job to compile, kernel-check, and audit the `FF-2.2` extensions in
`theory/Anneal/PureMirExec.lean` inside the `anneal-wt-ff-2-2` worktree.

## Overview of `FF-2.2` Deliverables

All `FF-2.1` definitions and theorem signatures (`PureState`, `MirFrameSim`,
`checkPureMir`, `PureMirConverges`, `mirWpConverges_of_pureExec`,
`mirWpConverges_of_pureExec_init`, etc.) are preserved intact so downstream
`MirLiftCore.lean`, `MirLift.lean`, and `MirLiftBench.lean` compile without
modification. `theory/Anneal/PureMirExec.lean` adds:

1. **Compositional 1-Step Callee & Tail-Call Summaries
   (`PureMirConverges.call_summary`, `PureMirConverges.tailCall_summary`,
   `PureMirConvergesWithCallees.{call_summary,tailCall_summary}`,
   `MirWpConverges.{call_summary,tailCall_summary,tailCall_nested_summary}`)**:
   - Introduces `ActiveRootMemory` (`mem' = mem₀ ∨ ∃ activeBody, mem' = { mem₀
     with activeCallee := some activeBody }`) and stack-suffix simulation
     (`Memory.pushBaseStack`, `wpMirExecNoCallSym_pushCalleeFrame`) so an
     established callee summary (including callees ending in
     `TerminatorKind.tailCall`) lifts across arbitrary caller `callStack`s and
     restores caller locals, `activeCallee`, and `activeProtectors` on return.
   - Resolves direct, trait-dispatched (`TraitImplEntry`), and polymorphic
     `(defPath, typeArgs)` callees via `lookupCallee` and
     `checkCalleeTargetCompatible` (`callDepth < maxCallDepth`), advancing the
     caller in 1 compositional step without re-stepping callee basic blocks or
     guessing combined fuel.
2. **Inline Pure Callee Checker (`checkPureMirWithCallees`), Computable
   Evaluator (`evalPureMirWithCallees`), & Soundness**:
   - Recursively checks linked pure helper callees in `callees` (including
     local/projected zero-sized `RigidTy.fnDef` function-item operands via
     `extractPureCalleeTarget?`, polymorphic `(defPath, typeArgs)`
     instantiations, `TraitImplEntry` dispatch, `.call`, `.tailCall`, inline
     `core::intrinsics::exact_div`, and diverging panic/abort calls) up to
     structural `maxCallDepth`.
   - Provides executable evaluators `evalPureMirStateWithCallees`,
     `evalPureMirWithCallees`, and `checkPureMirBoolPredWithCallees` alongside
     soundness bridges `pureMirConvergesWithCallees_of_evalPureMirWithCallees`,
     `mirWpConverges_of_evalPureMirWithCallees`, and
     `mirBoolPredicateHoldsWithCallees_of_checkPureMirBoolPredWithCallees`.
   - Transports `PureMirConvergesWithCallees` to `MirNoCallWpConverges`,
     `MirWpConverges` (`mirWpConverges_of_pureExecWithCallees`,
     `mirWpConverges_of_pureExecWithCallees_init`), `VerificationResult`,
     `StatefulVerificationResult` (including `c.callees = []` via
     `verifyStatefulMirNoPanic_of_pureExecWithCallees_any`),
     `TotalVerificationResult` (`verifyTotalMir_of_pureExecWithCallees_any`),
     and `MirBoolPredicateHoldsWithCallees` via `Memory.replaceRoot`.
3. **Pure `CallConv.rustIntrinsic` & `#[external_spec]` Modular Execution**:
   - Models 23 pure `CallConv.rustIntrinsic` operations (`ctlz`, `ctlz_nonzero`,
     `cttz`, `cttz_nonzero`, `ctpop`, `bswap`, `bitreverse`,
     `wrapping_add/sub/mul`, `saturating_add/sub`,
     `unchecked_add/sub/mul/div/rem/shl/shr`, `exact_div`, `three_way_compare`,
     `ub_checks`, and `const_eval_select`) in `PureRustIntrinsicKind`,
     `evalPureRustIntrinsicWithRuntime`, `calleeRuntimeEval` (with operational
     soundness `calleeRuntimeEval_sound`), and `pureRustIntrinsicContract`,
     normalizing `ScalarInt` bit widths, handling `.fnDef`/`.closure` and ZST
     tuple arguments in `const_eval_select` (with bounded nested
     `const_eval_select` and scalar-intrinsic fallback), and failing closed
     (`none`) on UB inputs.
   - Provides compositional contract combination (`combineMirCallContracts` and
     `MirCallContract.Subsumes`) and `PureMirModularConverges` (`mono_contract`,
     `call_modular`, `call_modular_sub`, `call_poly_external_spec`,
     `call_poly_external_spec_sub`, `call_external_spec`,
     `call_external_spec_sub`, `call_intrinsic`, `call_intrinsic_sub`,
     `call_summary`, `call_summary_resolved`, `tailCall_summary`,
     `tailCall_summary_resolved`, `tailCall_modular`, `tailCall_modular_sub`,
     `tailCall_poly_external_spec_sub`, `tailCall_external_spec_sub`,
     `tailCall_intrinsic`, `tailCall_intrinsic_sub`, `call_diverging_panic`,
     `call_diverging_modular_sub`, `call_exact_div`, `step_assert`, and
     `step_drop`), discharging `ModularVerificationResult` via
     `verifyModularMir_of_pureModularExec_any`,
     `verifyModularMirWithCallees_of_pureModularExec`, and
     `verifyModularMir_of_pureModularExec`.
4. **Concrete Multi-Callee, Polymorphic, Higher-Order Function-Item,
   `TraitImplEntry`, Tail-Call, Intrinsic, & `#[external_spec]` Witnesses**:
   - Proves `nestedMultiCalleeCallerBody` invoking 2 nested helpers in
     `demoCallees := [polySwapPairBody, scaleSwapAndDivBody]` both via
     `PureMirConverges.call_summary` (`nestedMultiCalleeCaller_compositional`)
     and via `checkPureMirWithCallees` (`nestedMultiCalleeCaller_inline`),
     `combinedModularPipelineBody` (`verify_combinedModularPipeline`),
     `traitAndTailMultiMonoCallerBody` (`u32` + `u64` multi-monomorphization,
     `TraitImplEntry` dispatch, and `tailCall`), `higherOrderFnItemCallerBody`
     (invoking local `Operand.move`/`Operand.copy` function-item slots in
     `.call` and `.tailCall`), and `calleeBackedConstEvalAndIntrinsicTailBody`
     (`verify_calleeBackedConstEvalAndIntrinsicTail` combining
     `calleeRuntimeEval` inside `const_eval_select`, `switchInt`,
     `call_diverging_panic`, and `tailCall_intrinsic_sub`).

## Step-by-Step Verification

1. **Configure `PATH` and Enter the Worktree**
   ```bash
   export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
   cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-2-2
   ```

2. **Run Repository Hygiene and Trusted Computing Base Audits**
   ```bash
   ./ci/check_todo.sh
   python3 trusted/audit/check_trusted.py --fast
   ```
   Both commands must exit with code `0` (`Trusted verification boundary audit
   passed`).

3. **Fast Single-File Kernel Typecheck (`PureMirExec.lean`)**
   ```bash
   cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-2-2/examples
   anneal-lean-run --mode file --concurrency 2 -- \
     lake env lean ../theory/Anneal/PureMirExec.lean
   ```
   Expected result: exit code `0` with zero errors and zero `sorry` warnings.

4. **Full `Anneal` Library Build Receipt (Including `MirLift*` Dependents)**
   ```bash
   cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-2-2/examples
   anneal-lean-run --mode build --concurrency 2 -- lake build Anneal
   ```
   Expected result: `Build completed successfully (64 jobs).` (`exit 0`).

5. **Kernel `#print axioms` Audit (`sorry_free=true`, Zero `native_decide`)**
   Verify from an ephemeral temporary file outside the repository that every
   headline theorem depends only on Lean's standard propositional/classical
   axioms (`propext`, `Classical.choice`, `Quot.sound`) — never `sorryAx`,
   `Lean.ofReduceBool`, or custom axioms:
   ```bash
   TMP_AXIOMS="$(mktemp /tmp/ff_2_2_axioms_XXXXXX.lean)"
   cat > "$TMP_AXIOMS" <<'EOF'
   import Anneal.PureMirExec
   open Anneal.PureMirExec
   #print axioms MirWpConverges.call_summary
   #print axioms MirWpConverges.tailCall_summary
   #print axioms MirWpConverges.tailCall_nested_summary
   #print axioms PureMirConverges.call_summary
   #print axioms PureMirConverges.tailCall_summary
   #print axioms mirWpConverges_of_pureExecWithCallees
   #print axioms pureMirConvergesWithCallees_of_evalPureMirWithCallees
   #print axioms mirBoolPredicateHoldsWithCallees_of_checkPureMirBoolPredWithCallees
   #print axioms PureMirModularConverges.mono_contract
   #print axioms PureMirModularConverges.call_poly_external_spec
   #print axioms PureMirModularConverges.call_poly_external_spec_sub
   #print axioms PureMirModularConverges.call_intrinsic
   #print axioms PureMirModularConverges.call_intrinsic_sub
   #print axioms PureMirModularConverges.call_summary
   #print axioms PureMirModularConverges.call_summary_resolved
   #print axioms PureMirModularConverges.tailCall_summary
   #print axioms PureMirModularConverges.tailCall_summary_resolved
   #print axioms PureMirModularConverges.tailCall_modular_sub
   #print axioms PureMirModularConverges.tailCall_poly_external_spec_sub
   #print axioms PureMirModularConverges.tailCall_external_spec_sub
   #print axioms PureMirModularConverges.tailCall_intrinsic_sub
   #print axioms PureMirModularConverges.call_diverging_panic
   #print axioms PureMirModularConverges.call_diverging_modular_sub
   #print axioms PureMirModularConverges.step_assert
   #print axioms PureMirModularConverges.step_drop
   #print axioms PureMirModularConverges.call_exact_div
   #print axioms resolveCallTarget_eq_of_extractPureCalleeTarget
   #print axioms calleeRuntimeEval_sound
   #print axioms verifyModularMir_of_pureModularExec_any
   #print axioms nestedMultiCalleeCaller_compositional
   #print axioms nestedMultiCalleeCaller_inline
   #print axioms verify_nestedMultiCalleeStatefulClaim
   #print axioms verify_nestedMultiCalleeTotalClaim
   #print axioms verify_pureIntrinsicCallerModular
   #print axioms verify_externalSpecAndPolyCalleeModular
   #print axioms verify_combinedModularPipeline
   #print axioms traitAndTailMultiMonoCaller_compositional
   #print axioms traitAndTailMultiMonoCaller_evalConcrete
   #print axioms higherOrderFnItemCaller_compositional
   #print axioms higherOrderFnItemCaller_mirWpConverges
   #print axioms higherOrderFnItemCaller_evalConcrete
   #print axioms verify_calleeBackedConstEvalAndIntrinsicTail
   EOF
   cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-2-2/examples
   anneal-lean-run --mode file --concurrency 2 -- lake env lean "$TMP_AXIOMS"
   rm -f "$TMP_AXIOMS"
   ```

## Audit Notes

- `[diversity-reduced]`: Under `anneal-model-policy` quota reserve routing for
  Tier `P1`, Agent A (`ff22a`) and Agent B (`ff22b`, switched from
  `gemini-launch-candidate-high` prior to `B1` due to `Family Y` quota floor)
  ran on `gemini-pro-coordinator`.
- Pass `B1` generalized `ActiveRootMemory` for arbitrary `activeBody` on tail
  returns, added compositional `tailCall_summary` / `tailCall_nested_summary`
  rules across `MirWpConverges`, `PureMirConvergesWithCallees`,
  `PureMirConverges`, and `PureMirModularConverges`, added computable
  `evalPureMirWithCallees` / `checkPureMirBoolPredWithCallees` with soundness
  theorems, hardened `evalSaturatingAdd`/`Sub` and `const_eval_select`
  intrinsic evaluation, refactored `combineMirCallContracts` with
  `MirCallContract.Subsumes` + `_sub`/`step_assert`/`step_drop`/`call_exact_div`
  rules, and added `combinedModularPipelineBody` and
  `traitAndTailMultiMonoCallerBody` end-to-end witnesses.
- Pass `A1` extended `checkPureTerminatorWith` and `checkPureMirWithCallees`
  (`extractPureCalleeTarget?` and
  `resolveCallTarget_eq_of_extractPureCalleeTarget`) to accept local and
  projected zero-sized `RigidTy.fnDef` function-item slots
  (`Operand.copy`/`Operand.move`), added `calleeRuntimeEval` +
  `calleeRuntimeEval_sound` and bounded nested `const_eval_select` evaluation,
  added modular external `tailCall_*` and diverging-call
  (`call_diverging_panic`, `call_diverging_modular_sub`) rules plus unified
  `verifyModularMir_of_pureModularExec_any`, and added
  `higherOrderFnItemCallerBody` and `calleeBackedConstEvalAndIntrinsicTailBody`
  witnesses.
