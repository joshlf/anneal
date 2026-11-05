# Reproducing FF-1.2 Verification

To verify the fuel-free MIR loop combinators (`MirWpConverges.join_of_branches`, `mirWpConverges_forRangeUp`, `mirWpConverges_whileRank`) and the concrete non-vacuity witness (`countTo10_terminates`), run the following commands:

```bash
# 1. Ensure the Lean/Cargo environment is active
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# 2. Check for missing tasks and repository hygiene
./ci/check_todo.sh

# 3. Audit trusted files and verify the dependency graph (fast mode)
python3 trusted/audit/check_trusted.py --fast

# 4. Kernel-check all Lean 4 theorems in Anneal (including MirLoops.lean) 
# Note: Uses hardware-matched anneal-lean-run wrapper
cd examples && anneal-lean-run --mode build --concurrency 2 -- lake build Anneal
```

Upon successful completion, the `lake build` step will verify all definitions and theorems in `theory/Anneal/MirLoops.lean` without any `sorry` or `sorryAx` warnings.

**Audit Note**: This verification is part of the `[diversity-reduced]` adversarial execution.
