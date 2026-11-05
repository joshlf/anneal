# Reproduction Guide for FF-1

This document provides self-contained step-by-step instructions to compile and kernel-check the Lean 4 proofs for `FF-1` (Fuel-Free Core, Structural Loop Combinators & Closed-Form Scalar Bridges), covering `FF-1.1`, `FF-1.2`, and `FF-1.3`.

## Prerequisites
- Elan (Lean toolchain manager) installed.
- Cargo (Rust package manager) installed.

Ensure they are on your path:
```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
```

## Step 1: Pre-Commit Checks
We first check for missing unfinished task markers or hygiene violations using the provided script:
```bash
./ci/check_todo.sh
```

## Step 2: Audit Trusted Code
We execute the trusted auditing scripts which check for custom axioms, `sorry` placeholders, or other unsafe `native_decide` escapes in the trusted path:
```bash
python3 trusted/audit/check_trusted.py --fast
```

## Step 3: Full Workspace Build
Compile the full `Anneal` Lean 4 workspace using the provided bounding script:
```bash
cd examples && anneal-lean-run --mode build --concurrency 2 -- lake build Anneal
```
The build completes successfully, indicating 0 errors and all theorems are verified by the Lean kernel.
