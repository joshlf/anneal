# Reproduction Guide for FF-2.1 [diversity-reduced]

## Steps

1. Export path:
   ```bash
   export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
   ```

2. Run Pre-Commit Checks:
   ```bash
   ./ci/check_todo.sh
   python3 trusted/audit/check_trusted.py --fast
   ```

3. Build the Anneal library:
   ```bash
   cd examples && anneal-lean-run --mode build --concurrency 2 -- lake build Anneal
   ```

Note: A0 contains `sorry` for `mirWpConverges_of_pureExec` and `pureTestMir_correct` which will be addressed in future adversarial rounds.
