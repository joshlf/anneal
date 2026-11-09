# Reproduction Guide for FF-2.3 (Anneal.MirSpecLift)

This guide provides instructions to verify `MirSpecLift` and its tests against the kernel.

## Prerequisites

1.  A standard Linux x86_64 environment.
2.  `elan` installed with Lean 4 toolchain (matches `lean-toolchain`).

## Steps

1.  **Enter the workspace:**
    ```bash
    cd <path/to/anneal>
    export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
    ```

2.  **Run Style and Sanity Checks:**
    ```bash
    ./ci/check_todo.sh
    python3 trusted/audit/check_trusted.py --fast
    ```

3.  **Compile and Verify the Proofs:**
    Run the multi-threaded build to check all untrusted modules and examples (including `MirSpecLift.lean` and `WireframeDemo` companions):
    ```bash
    cd examples
    anneal-lean-run --mode build --concurrency 2 -- lake build
    ```

## Verification

The build will complete with exit code 0 if all proofs are accepted by the Lean kernel and no `sorryAx` or custom axioms are used in the trusted components.
