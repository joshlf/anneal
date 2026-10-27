# Test suites and meta-validation canaries (`tests/`)

This directory holds `AnnealTests.*` (`tests/Smoke.lean` and
`tests/trusted-boundary/positive.lean`): pure, effect-free Lean regression and
canary modules that test both Anneal's semantic models and its
[`trusted/`](../trusted/README.md) containment boundary
([#1 `#E-EVAL-02`](https://github.com/joshlf/anneal/issues/1),
[#100](https://github.com/joshlf/anneal/issues/100) §6–§7,
[#103](https://github.com/joshlf/anneal/issues/103)).

## Test categories

1. **`trusted/` boundary and auditor regressions (`tests/trusted-boundary/` and `trusted/cargo-anneal/src/self_test.rs`):**
   Positive and negative fixtures verifying that
   [`trusted/cargo-anneal/`](../trusted/cargo-anneal/README.md) and
   [`trusted/audit/TrustedBoundary.lean`](../trusted/audit/README.md) reject:
   - Any dependency from `trusted/lean/` onto `theory/` or unpinned modules,
   - Any reference to `theory/` (`Anneal.*`) inside the **type (`ci.type`)** of a
     `Trusted.CrateTheorem` / `VerificationResult` theorem (Statement-vs.-Proof
     Origin Separation),
   - Unapproved axioms, `sorryAx`, `unsafe`, `partial`, `native_decide`,
     `implemented_by`, recursor-rule/opaque-body leaks, Cargo workspace members
     or path dependencies outside `trusted/`, and tampered
     `CaptureManifest.json` digests.
2. **Structural non-vacuity and Rust adequacy canaries (`MetaValidation`):**
   Positive and negative canary theorems ([#100](https://github.com/joshlf/anneal/issues/100)
   §6.2) verifying that:
   - `MirSem` satisfies `TotalStep` and `InhabitedDemonic` (ruling out silent
     stuck states and empty demonic choices),
   - UB before an infinite loop (`*bad_ptr; loop {}`) and discarded invalid
     values (`let _ = *bad_bool;`) violate `MirLang.WellFormed`,
   - Pure infinite loops (`loop {}`) satisfy `MirLang.WellFormed`, and
   - Secret-dependent branches violate constant-time leakage specifications.
3. **End-to-end pipeline and policy tests (`trusted/cargo-anneal/tests/verify_id.rs`):**
   Tests exercising end-to-end `cargo anneal verify` capture, proof generation,
   and kernel verification across safe and `unsafe` Rust functions, including
   negative tests for false specifications, unsupported MIR constructs,
   post-capture `Mir.lean` tampering, and spoofed `Proof.verify_crate` theorem
   types ([#103](https://github.com/joshlf/anneal/issues/103) §3–§4,
   [#109](https://github.com/joshlf/anneal/issues/109)).

## Axiom policies in `tests/` (`strict` vs. `file-local-axioms`)

By default, test modules use the **`strict`** zero-custom-axiom policy. A test
module `AnnealTests.Foo` that exercises end-to-end `pass_trans` /
`verify_through_passes` composition against a placeholder external stage may opt
into `-- anneal-audit: policy=file-local-axioms`; `TrustedBoundary.lean` then
verifies in the compiled `.olean` `Environment` (`env.getModuleIdxFor? ax`) that
every non-standard axiom used in `AnnealTests.Foo` was declared in
`AnnealTests.Foo` itself and never leaks into other modules
([#100](https://github.com/joshlf/anneal/issues/100) §7.1).
