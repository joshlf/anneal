# Reproduction Instructions for BRIEF-4.3 (In-Place Fuchsia `usercopy` Verification Pilot)

## Context
This document verifies the target functions in Fuchsia's `usercopy` (`do_hermetic_copy`, `Usercopy::raw_hermetic_copy`, `copyout`, `copyin`, `copyin_until_null_byte`, `atomic_load_u32_relaxed`, `atomic_load_u32_acquire`) in place using the completed MIR semantics, default `core` lowering, and explicit `#[external_spec]` contracts for FFI/OS boundaries.

## Worktrees
1. **Anneal Worktree**: `/usr/local/google/Projects/anneal-workspace/anneal-wt-brief-4-3` (branch `adv/brief-4-3`)
2. **Fuchsia Worktree**: `/usr/local/google/Projects/anneal-workspace/fuchsia-wt-brief-4-3` (contains the `examples/fuchsia-usercopy` crate)

## Steps to Reproduce

### 1. Build and Run Verification
Execute the following command to run the end-to-end verification of the `fuchsia-usercopy` crate against the Anneal semantics:

```bash
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-4-3
export PATH="$(pwd)/target/debug:$PATH"
cargo build -p cargo-anneal -p anneal-rustc-capture
cargo run --manifest-path Cargo.toml -p cargo-anneal -- agent-verify --manifest-path /usr/local/google/Projects/anneal-workspace/fuchsia-wt-brief-4-3/examples/fuchsia-usercopy/Cargo.toml
```

**Expected Outcome:**
The command should exit with code `0`. You should see `125/125` jobs completed successfully with `0 sorryAx` audit warnings, confirming that all obligations are perfectly discharged and the kernel replay passes the TrustedBoundary audit.

### 2. Audit proofs
You can also manually audit individual Lean proof files using `anneal-lean-run` or by opening them in VS Code with the Lean 4 extension.

```bash
cd /usr/local/google/Projects/anneal-workspace/fuchsia-wt-brief-4-3/examples/fuchsia-usercopy
lake env lean .anneal/generated/Proof/FuchsiaUsercopy/hermetic_copy_stub.lean
```

**Expected Outcome:**
No errors, `0 sorry`, `0 disallowed axioms`.
