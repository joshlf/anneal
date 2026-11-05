# Reproduction Guide for FF-1.2 Adversarial Check

This guide explains how to compile and kernel-check the Fuel-Free `TransPlan` Join Points & Structural Loop Combinators.

## Prerequisites

1. Set up the Lean 4 environment:
```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
```

## Step 1: Verify Zero Sorry Axioms in `MirLoops.lean`

Run the following command to kernel-check `theory/Anneal/MirLoops.lean` explicitly:

```bash
cd examples && anneal-lean-run --mode file --concurrency 2 -- lake env lean ../theory/Anneal/MirLoops.lean
```

You should see zero output, confirming there are no warnings or `sorry` axioms.

## Step 2: Full Workspace Build

Run a complete workspace build:

```bash
cd examples && anneal-lean-run --mode build --concurrency 2 -- lake build Anneal
```

You should see `Build completed successfully`.

## Step 3: Run the Audit Scripts

Run the scripts to check for `sorry` and ensure the trust boundary is intact:

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```

Both should exit with code 0.