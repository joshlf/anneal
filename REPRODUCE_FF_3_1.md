# Reproduction Guide for FF-3.1 (Variable-Headed Opaque-Body Bridge Rules)

This guide documents how to compile and kernel-check the 10+ basic block benchmark for the variable-headed MIR lifting rules developed in `FF-3.1`.

## 1. Setup

Navigate to the worktree root:
```bash
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-ff-3-1
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
```

## 2. Compile the Lean 4 Proofs

Run the hardware-bounded Lean checker to build the `Anneal` library, which includes the benchmark `MirLiftBench.lean`:
```bash
cd examples
anneal-lean-run --mode build --concurrency 2 -- lake build Anneal
```

## 3. Kernel-Check and Verify `sorry_free`

The `MirLiftBench.lean` file contains a 10-basic-block proof `bench_converges` that uses `.step` constructors explicitly (without unfolding the huge `.basicBlocks` array using `BlockCtx`).

You can verify that it compiles and contains zero `sorry` or `sorryAx` by running:
```bash
cd examples
anneal-lean-run --mode file --concurrency 2 -- lake env lean ../theory/Anneal/MirLiftBench.lean
```

If it succeeds with no output (and specifically no warnings about `sorry` or `sorryAx`), the proof is kernel-checked and complete!
