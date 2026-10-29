# Test suites and meta-validation canaries (`tests/`)

This directory holds the regression and canary suites that test both Anneal's
semantic models and its [`trusted/`](../trusted/README.md) containment boundary
([#1 `#E-EVAL-02`](https://github.com/joshlf/anneal/issues/1),
[#100](https://github.com/joshlf/anneal/issues/100) §6–§7,
[#103](https://github.com/joshlf/anneal/issues/103)).

## Test categories

1. **`trusted/` boundary and auditor regressions (`tests/trusted-boundary/test_boundary.py`):**
   16 fixture groups (`python3 -B trusted/audit/check_trusted.py --self-test`)
   verifying that [`trusted/audit/`](../trusted/audit/README.md) rejects:
   - Any dependency from `trusted/lean/` onto `theory/` or unpinned non-stdlib
     modules,
   - Any reference to `theory/` (`Anneal.*`) inside the **type (`ci.type`)** of a
     claim theorem (Statement-vs.-Proof Origin Separation),
   - Unapproved axioms, `sorryAx`, `unsafe`, `partial`, `native_decide`,
     `implemented_by`, recursor-rule/opaque-body leaks, Cargo DAG violations, and
     tampered `CaptureManifest.json` digests, while validating `--fast` cache
     invalidation and per-toolchain lock resolution.
2. **Statement-vs.-Proof Origin Separation claim suite (`tests/Smoke.lean`):**
   Audited under `role = "claim"` by `checkStatementOrigins` in
   `trusted/audit/TrustedBoundary.lean`, covering Layer 1A
   (`layer1a_claim_origin_check`), Layer 1B (`layer1b_claim_origin_check`),
   Layer 1 partial semantics (`layer1_partial_claim_origin_check`), Layer 2
   (`layer2_claim_origin_check`), and all five MIR verification gates
   (`VerificationResult`, `StatefulVerificationResult`,
   `TraceVerificationResult`, `TotalVerificationResult`, and
   `ModularVerificationResult`).
3. **Layer 1A, Layer 1B, and Layer 2 positive/negative suites (`tests/refinement/`, `tests/step-result/`, `tests/pass/`):**
   Concrete and axiomatic tests exercising `GuardedRefines.trans` and
   `Language` composition (`AxiomaticYDiagram.lean`, `ConcreteYDiagram.lean`),
   `ITreeMachine` cross-effect `WeakObsRef` simulation
   (`AxiomaticSimulation.lean`), non-vacuity and failure-taxonomy controls,
   foreign/ISA `BridgeContract` / `bridgeTree` refinement, prefix preservation
   before UB (`UBClosedPrefixes`), the 2×2 Smyth `WeakRef` / `WeakSim` /
   `WeakCSim` / `TotalWeakRef` lattice separation, infinite reactive stream
   `FollowsStream` / `InfinitelyOften` verification, and `Std.Do.Triple`
   verification over `ITree` `do`-blocks (`tests/step-result/Canaries.lean`),
   alongside resolved-label and `.tau`-erasing CFG forwarder controls
   (`AxiomaticForwarder.lean`, `ConcreteForwarder.lean`).
4. **End-to-end Rust-to-Lean pipeline, Tutor, and user-journey tests (`crates/cargo-anneal/tests/`):**
   Exercises `cargo anneal extract`, `scaffold`, `verify`, `lock-specs`, and
   `agent-verify` across multi-item Rust packages (`end_to_end_pipeline.rs`),
   the six-chapter Anneal Tutor (`end_to_end_tutor.rs`), and the four-journey
   `wireframe-demo` crate (`end_to_end_demo_journeys.rs`).

## Axiom policies in `tests/` (`strict` vs. `file-local-axioms`)

By default, test modules use the **`strict`** zero-custom-axiom policy. A test
module `Foo` that exercises end-to-end `GuardedRefines.trans` composition against
a placeholder external stage may opt into
`-- anneal-audit: policy=file-local-axioms`; `trusted/audit/` then verifies in
the compiled `.olean` `Environment` (`env.getModuleIdxFor? ax`) that every
non-standard axiom used in `Foo` was declared in `Foo` itself and never leaks
into other modules ([#100](https://github.com/joshlf/anneal/issues/100) §7.1).
