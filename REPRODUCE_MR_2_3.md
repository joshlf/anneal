# Reproduce MR-2.3

This document outlines the steps to verify the implementation of `MR-2.3` (Enums/ADTs, Discriminator, SetDiscriminant, GetDiscriminant & Downcast) in the MiniRust Lean specification.

## Prerequisites

- Lean 4 toolchain (installed via `elan`)
- Rust toolchain (installed via `rustup`)

Ensure `elan` and `cargo` are in your `PATH`.

## Verification Steps

1. **Verify the Concrete Enum Witness**
   Check the `Witness.lean` file, which includes tests for `Type.encode`, `Type.decode`, `checkValue`, and `Interp.evalPlace` using a custom `Option<u8>`-like enum:
   ```bash
   cd examples
   anneal-lean-run --mode file --concurrency 3 -- lake env lean ../minirust/lean/MiniRustSpec/Correspondence/Witness.lean
   ```

2. **Full Project Build**
   Build the entire `MiniRustSpec` project to ensure all definitions and correspondence theorems type-check properly:
   ```bash
   cd examples
   anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec
   ```

3. **Check Upstream Quotes Sync**
   Verify that the docstrings accurately reflect the upstream MiniRust specification by running the quote checker:
   ```bash
   cargo test -p anneal-minirust-gen --offline
   ```

4. **Audit Trusted Base and TODOs**
   Ensure no regressions in the trusted components and check for unresolved TODOs:
   ```bash
   ./ci/check_todo.sh
   python3 trusted/audit/check_trusted.py --fast
   ```
