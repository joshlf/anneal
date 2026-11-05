# Reproduce MR-2.3 (Enums/ADTs)

This guide walks through reproducing the `MR-2.3` milestone, which adds semantic translation and simulation for Minirust Enums/ADTs (Discriminator, SetDiscriminant, GetDiscriminant, Downcast).

## Prerequisites

- You must be inside the `MR-2.3` worktree.
- Run commands with `anneal-lean-run` to enforce concurrency limits and resource constraints.

## Steps

### 1. Verify Rust Quotations

Check that the Rust quotes test for Enum statements is passing and tamper-checked:

```bash
cargo test -p anneal-minirust-gen --test quotes -- mr_2_3
```

You should see:
```
test mr_2_3_enum_quotations_are_pinned_and_tamper_checked ... ok
```

### 2. Verify Semantic Translation & Simulation (Lean)

Run the Lean build to verify the proofs in `Witness.lean`, `Translate.lean`, and `Simulation.lean` are valid and the `Audit.lean` target evaluates to `sorry_free=true`:

```bash
cd examples
anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec
```

This will run for a while and should complete without errors. Ensure the final `Audit.lean` evaluates without hitting `sorry`.

### 3. Check for TODOs / Axioms

Verify that there are no unapproved `todo!`, `sorry`, or unsupported axioms:

```bash
cd ..
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```

The output should indicate no violations.
