<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproduction Guide for FF-2.2: Compositional Callee, Polymorphic `(defPath, typeArgs)`, `#[external_spec]` & Pure `CallConv.rustIntrinsic` Call Resolution

This guide provides self-contained instructions for an independent reviewer or
CI job to compile, kernel-check, and audit the `FF-2.2` extensions in
`theory/Anneal/PureMirExec.lean` inside the `anneal-wt-ff-2-2` worktree.

## Overview of `FF-2.2` Deliverables

All `FF-2.1` definitions and theorem signatures (`PureState`, `MirFrameSim`,
`checkPureMir`, `PureMirConverges`, `mirWpConverges_of_pureExec`,
`mirWpConverges_of_pureExec_init`, etc.) are preserved intact so downstream
`MirLiftCore.lean`, `MirLift.lean`, and `MirLiftBench.lean` compile without
modification. `theory/Anneal/PureMirExec.lean` adds:

1. **Compositional 1-Step Callee Summaries (`PureMirConverges.call_summary`,
   `PureMirConvergesWithCallees.call_summary`, `MirWpConverges.call_summary`)**:
   - Introduces `ActiveRootMemory` (`mem' = mem₀ ∨ mem' = { mem₀ with
     activeCallee := some body }`) and stack-suffix simulation
     (`Memory.pushBaseStack`, `wpMirExecNoCallSym_pushCalleeFrame`) so an
     established callee summary lifts across arbitrary caller `callStack`s and
     restores caller locals, `activeCallee`, and `activeProtectors` on return.
   - Resolves direct and polymorphic `(defPath, typeArgs)` callees via
     `lookupCallee` and `checkCalleeTargetCompatible` (`callDepth <
     maxCallDepth`), advancing the caller to `targetBb` with `dest := retVal` in
     1 compositional step without re-stepping callee basic blocks or guessing
     combined fuel.
2. **Inline Pure Callee Checker (`checkPureMirWithCallees`) & Soundness**:
   - Recursively checks linked pure helper callees in `callees` (including
     polymorphic `(defPath, typeArgs)` instantiations, `.call`, `.tailCall`,
     inline `core::intrinsics::exact_div`, and diverging panic/abort calls) up
     to structural `maxCallDepth`.
   - Transports `PureMirConvergesWithCallees` to `MirNoCallWpConverges`,
     `MirWpConverges` (`mirWpConverges_of_pureExecWithCallees`,
     `mirWpConverges_of_pureExecWithCallees_init`), `VerificationResult`,
     `StatefulVerificationResult`, `TotalVerificationResult`, and
     `MirBoolPredicateHoldsWithCallees` via `Memory.replaceRoot`.
3. **Pure `CallConv.rustIntrinsic` & `#[external_spec]` Modular Execution**:
   - Models 23 pure `CallConv.rustIntrinsic` operations (`ctlz`, `ctlz_nonzero`,
     `cttz`, `cttz_nonzero`, `ctpop`, `bswap`, `bitreverse`,
     `wrapping_add/sub/mul`, `saturating_add/sub`,
     `unchecked_add/sub/mul/div/rem/shl/shr`, `exact_div`, `three_way_compare`,
     `ub_checks`, and `const_eval_select`) in `PureRustIntrinsicKind`,
     `evalPureRustIntrinsicWithRuntime`, and `pureRustIntrinsicContract`,
     failing closed (`none`) on UB inputs.
   - Provides `PureMirModularConverges` (`call_modular`,
     `call_poly_external_spec`, `call_external_spec`, `call_intrinsic`, and
     `call_summary`) discharging `ModularVerificationResult` via
     `verifyModularMirWithCallees_of_pureModularExec` and
     `verifyModularMir_of_pureModularExec`.
4. **Concrete Multi-Callee, Polymorphic, Intrinsic, & `#[external_spec]`
   Witnesses**:
   - Proves `nestedMultiCalleeCallerBody` invoking 2 nested helpers in
     `demoCallees := [polySwapPairBody, scaleSwapAndDivBody]` (combining
     polymorphic `demo::poly_swap_pair<T>` and inline `exact_div`) both via
     `PureMirConverges.call_summary` (`nestedMultiCalleeCaller_compositional`)
     and via `checkPureMirWithCallees` (`nestedMultiCalleeCaller_inline`), plus
     `VerificationResult`, `StatefulVerificationResult`,
     `TotalVerificationResult`, and `ModularVerificationResult` certificates
     with non-vacuity witnesses.

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
   Expected result: all 65 targets build cleanly (`exit 0`).

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
   #print axioms PureMirConverges.call_summary
   #print axioms mirWpConverges_of_pureExecWithCallees
   #print axioms PureMirModularConverges.call_poly_external_spec
   #print axioms PureMirModularConverges.call_intrinsic
   #print axioms PureMirModularConverges.call_summary
   #print axioms nestedMultiCalleeCaller_compositional
   #print axioms nestedMultiCalleeCaller_inline
   #print axioms verify_nestedMultiCalleeStatefulClaim
   #print axioms verify_nestedMultiCalleeTotalClaim
   #print axioms verify_pureIntrinsicCallerModular
   #print axioms verify_externalSpecAndPolyCalleeModular
   EOF
   cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-2-2/examples
   anneal-lean-run --mode file --concurrency 2 -- lake env lean "$TMP_AXIOMS"
   rm -f "$TMP_AXIOMS"
   ```

## Audit Notes

- `[diversity-reduced]`: Under `anneal-model-policy` quota reserve routing for
  Tier `P1`, Agent A (`ff22a`) ran on `gemini-pro-coordinator` paired against
  Agent B (`ff22b`) on `gemini-launch-candidate-high`.
