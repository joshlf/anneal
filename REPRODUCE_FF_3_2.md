# Reproduction Guide for FF-3.2: MirLift

To compile and kernel-check the Lean 4 proofs for `#mir_lift`:

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# 1. Run codebase checks
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast

# 2. Build the main Anneal library
cd examples
anneal-lean-run --mode build --concurrency 2 -- lake build Anneal

# 3. Check the MirLift elaborator and its E2E test suite
anneal-lean-run --mode file --concurrency 2 -- lake env lean ../theory/Anneal/MirLift.lean
```

