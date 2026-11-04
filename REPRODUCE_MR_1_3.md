# Reproducing MR-1.3

To check the current state:

```bash
# 1. Run the CI script for TODOs
./ci/check_todo.sh

# 2. Audit the axioms
python3 trusted/audit/check_trusted.py --fast

# 3. Check the anchors against the spec
cargo test -p anneal-minirust-gen --offline

# 4. Build the Lean proofs
cd examples && anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec
```
