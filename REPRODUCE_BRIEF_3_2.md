# BRIEF-3.2 Reproduction Guide: Transitive `s.memory.callees` Population by Default and Explicit `#[external_spec]` Override + Default Well-Typed Spec Generation

This document provides exact, copy-pasteable commands to reproduce and verify `BRIEF-3.2` in `/usr/local/google/Projects/anneal-workspace/anneal-wt-brief-3-2`.

## 1. Environment Setup

```bash
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-3-2
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
```

## 2. Lean 4 Trusted Verification Surface & Theory Libraries

Build `Trusted` (`trusted/lean/Trusted/VerificationResult.lean`) and `Anneal`:
- `initMachineStateWithMemoryAndCallees`, `mirCallTreeWithCallees`, `mirStatefulTreeWithCallees`, `MirExecPartialWithCallees`, `MirContractHoldsWithCallees`, `MirStatefulContractHoldsWithCallees`, `RefinesStatefulMirWithCallees`,
- Default `callees : List CapturedMir := .nil` fields on `Claim`, `StatefulClaim`, `ModularClaim`, `TraceClaim`, `TotalClaim`, `UbExceptionClaim`, and `StatefulEquivClaim`,
- Non-vacuous return-type and layout validity predicates (`valueValidForTy`, `valueValidForReturnDecl`, `retMatchesCalleeReturnTy`, and `externalSpecCallContract`).

```bash
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-3-2/examples
lake build Trusted Anneal
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-3-2
```

## 3. Macro Expansion & `rustc-capture` Sidecar Target Resolution

Verify clause-less and clause-bearing `#[anneal_spec::external_spec(for = <target>)]` macro expansion (`crates/anneal-spec-macros`) and `rustc-capture` canonical `def_path` resolution across local items (`crate::local_helper`), inherent slice methods (`<[u8]>::len` -> `core::slice::<impl [T]>::len`), and `core`/`std` functions (`std::slice::from_raw_parts_mut` -> `core::slice::from_raw_parts_mut`):

```bash
cargo test -p anneal-spec-macros -- --nocapture
cargo test -p anneal-rustc-capture driver_resolves_external_spec_targets_across_local_inherent_and_core_paths -- --nocapture
```

## 4. End-to-End Transitive `defaultCallees`, `#[external_spec]` Override, `generate-external-spec` CLI, & Lean 4 Kernel Proofs

Run the `cargo-anneal` unit and multi-crate end-to-end integration tests verifying:
1. Cycle-safe transitive callee discovery (`populate_called_callees`) across primary crate functions, dependency crate functions (`crate_b::helper_add` -> `crate_b::inner_leaf`), and `core` sysroot functions (`<[T]>::len`, `RangeBounds::contains`),
2. Exclusion of targets with explicit `#[external_spec(for = <target>)]` overrides (both with `requires`/`ensures` clauses and clause-less) from `defaultCallees`,
3. Emission of `externalCallContract_<ident> : MirCallContract := externalSpecCallContract ...` wired into `defaultModularSpec.envAssumed`,
4. `cargo anneal generate-external-spec <target>` CLI snippet generation from captured MIR metadata, and
5. Lean 4 kernel (`lean`) verification (`VerifyBrief32.lean`) proving that `defaultCallees` populates `s.memory.callees`, `lookupCallee` resolves un-overridden direct and transitive callees while returning `.none` for overridden targets, and `externalSpecCallContract` enforces non-vacuous return-type and layout validity:

```bash
cargo test -p cargo-anneal renders_transitive_default_callees_and_external_spec_contracts -- --nocapture
cargo test -p cargo-anneal transitive_callees_closure_is_cycle_safe_and_excludes_external_spec_overrides -- --nocapture
cargo test -p cargo-anneal cli_generate_external_spec_parses_and_emits_snippet -- --nocapture
cargo test -p cargo-anneal multi_crate_transitive_callees_and_external_spec_override_end_to_end -- --nocapture
```

## 5. Full Test Suites & Trusted Audit Gate

```bash
cargo test -p anneal-spec-macros -p anneal-rustc-capture -p cargo-anneal
python3 trusted/audit/check_trusted.py --fast
```
