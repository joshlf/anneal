# Reproducing FF-1.1

## Prerequisites
Ensure `$HOME/.elan/bin`, `$HOME/.cargo/bin`, and `$HOME/.local/bin` are in your `PATH`.
You can set this up via:
```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
```

## Steps
1. Navigate to the root of the `anneal-wt-ff-1-1` worktree.
2. Check for zero TODOs: `./ci/check_todo.sh`
3. Audit trusted codebase: `python3 trusted/audit/check_trusted.py --fast`
4. Build Lean code and check for zero `sorryAx`:
```bash
cd examples && anneal-lean-run --mode build --concurrency 2 -- lake build Anneal
```

5. After the build completes successfully, you should observe no errors or warnings, and the build ensures there are zero `sorryAx` remaining in the codebase.
