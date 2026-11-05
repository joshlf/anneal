# Reproduction Guide for FF-2.1: PureMirExec Simulation & Tier 1 Alias Erasure

This guide contains the step-by-step instructions for an independent adversary (or CI) to compile, type-check, and verify the `PureMirExec` specification, alias-erased states (`PureState`), syntatic purity checking (`checkPureMir`), and the `mirWpConverges_of_pureExec` and `StatefulVerificationResult` correctness proofs in the `anneal-wt-ff-2-1` worktree.

## Prerequisites

1. Access to the Anneal workspace (`/usr/local/google/Projects/anneal-workspace/anneal-wt-ff-2-1`).
2. Elan and Lean 4 installed in the standard environment.
3. Access to `anneal-lean-run` wrapper (to prevent OOM/slowdowns during multi-worktree execution).

## Steps to Verify

1. **Set Up the Environment**
   Open a terminal and set your PATH so that Elan and Cargo are prioritized:
   ```bash
   export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
   cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-2-1
   ```

2. **Run Quick Code Quality Audits**
   Ensure there are no unresolved task markers left in the code:
   ```bash
   ./ci/check_todo.sh
   ```
   *Expected Output*: (Exit code 0, no output)

   Ensure all trusted definitions (`trusted/`) maintain their audit invariants (e.g. no rogue axioms or changes to the Trusted Computing Base):
   ```bash
   python3 trusted/audit/check_trusted.py --fast
   ```
   *Expected Output*: The script should print success and exit with code 0.

3. **Verify the Lean proofs without building the whole repository (Fast path)**
   To quickly type-check the single file containing all our theorems (`PureMirExec.lean`):
   ```bash
   cd examples
   anneal-lean-run --mode file --concurrency 2 -- lake env lean ../theory/Anneal/PureMirExec.lean
   ```
   *Expected Output*: (Exit code 0, no output or warnings about unused variables only)
   This command ensures that:
   - `checkPureMir` computable syntactic check is defined.
   - `MirFrameSim` properly checks `ms.memory = mem₀`.
   - `mirWpConverges_of_pureExec` is fully proven (no `sorryAx`).
   - The multi-block `pureAdtMultiBlock_wpConverges` witness builds successfully.

4. **Verify the Full Workspace (Slow Path)**
   For a comprehensive end-to-end receipt of all proofs in the `Anneal` library, run the full lake build:
   ```bash
   cd examples
   anneal-lean-run --mode build --concurrency 2 -- lake build Anneal
   ```
   *Expected Output*: `lake` finishes building `Anneal` and its dependencies without errors. You should see no `sorryAx` warnings for `theory/Anneal/PureMirExec.lean`.

## Proof Highlights
- The core structural simulation lemma is `stepMirExecSymTree_eq_withMem`, proven by mutually recursive induction alongside `evalSymNodeTree_eq_withMem`.
- All memory interactions in `PureState` are bypassed by matching directly against the syntactically restricted set of `checkPureMir`.
- The multi-block `pureAdtMultiBlockBody` witness discharges a `StatefulVerificationResult` strictly via structural equality on `mem₀` across blocks, without constructing memory maps or provenance.
