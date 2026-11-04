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
- Non-vacuous return-type and layout validity predicates (`valueValidForTy`, `valueValidForReturnDecl`, `retMatchesCalleeReturnTy`, `argsMatchCalleeParamTys`, and `externalSpecCallContract`). `valueValidForTy` accepts every representation `MirSemantics` produces for a valid value (wide `[ptr, metadata]` aggregates for references and raw pointers to slices, `str`, and `dyn Trait`; `.unit` for zero-sized constants), so assuming it of external return values never excludes real callee behavior.
- `externalSpecCallContract` requires the target path, arity, well-typed arguments, and the optional `requires` clause; on a normal return it assumes a well-typed result, the optional `ensures` clause, and an unchanged call frame (`callFramePreserved`: call stack, active body, and callee table), while permitting arbitrary heap mutation, unwinding, and aborting.

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
2. Exclusion of targets with explicit `#[external_spec(for = <target>)]` overrides (both with `requires`/`ensures` clauses and clause-less, including a true `extern "C"` FFI function `crate_a::ffi_checksum` with no MIR body) from `defaultCallees`,
3. Emission of `externalCallContract_<ident> : MirCallContract := externalSpecCallContract ...` for every reachable overridden target, all conjoined into `defaultModularSpec.envAssumed` (with the sidecar's `requires`/`ensures` companions matched by exact `<parent>::__anodized_fn_{requires,ensures}_<sidecar>` path),
4. Evaluation of call-containing `requires`/`ensures` companion predicates with their transitive callees linked (`defaultSpecCallees` + `MirBoolPredicateHoldsWithCallees`), so that a call inside a predicate cannot make the predicate unsatisfiable,
5. `cargo anneal generate-external-spec <target>` CLI snippet generation from captured MIR metadata, and
6. Lean 4 kernel (`lean`) verification (`VerifyBrief32.lean`) proving that `defaultCallees` populates `s.memory.callees`, `findCallee?` resolves un-overridden direct and transitive callees while returning `.none` for overridden targets, `externalSpecCallContract` accepts valid and rejects invalid return values and arguments (including wide slice pointers), permits heap mutation, unwinding, and aborting, and that the modular environment assumes every external call contract:

```bash
cargo test -p cargo-anneal renders_transitive_default_callees_and_external_spec_contracts -- --nocapture
cargo test -p cargo-anneal transitive_callees_closure_is_cycle_safe_and_excludes_external_spec_overrides -- --nocapture
cargo test -p cargo-anneal spec_companion_callees_are_linked_without_widening_the_modular_environment -- --nocapture
cargo test -p cargo-anneal external_spec_companions_match_by_exact_sidecar_path -- --nocapture
cargo test -p cargo-anneal default_env_assumed_conjoins_every_abstracted_callee_contract -- --nocapture
cargo test -p cargo-anneal call_containing_companions_are_evaluated_with_default_spec_callees -- --nocapture
cargo test -p cargo-anneal cli_generate_external_spec_parses_and_emits_snippet -- --nocapture
cargo test -p cargo-anneal multi_crate_transitive_callees_and_external_spec_override_end_to_end -- --nocapture
```

## 5. Full Test Suites & Trusted Audit Gate

The `anneal-rustc-capture` integration tests compile emitted modules with `lean`
from temporary directories, where `elan` would otherwise select its default
toolchain; pin the repository toolchain so the `examples/.lake` oleans load:

```bash
export ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1
cargo test -p anneal-spec-macros -p anneal-rustc-capture -p cargo-anneal
python3 trusted/audit/check_trusted.py --fast
./ci/check_todo.sh
```
