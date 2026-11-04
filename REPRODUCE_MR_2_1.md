<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction Guide — `MR-2.1`: Homogeneous Arrays (`Type::Array`), `Repeat`, `Len`, and `Index`/`ConstantIndex` Projections

This guide provides self-contained, step-by-step commands to independently
reproduce and audit the `MR-2.1` implementation, verbatim upstream MiniRust
specification/translator quote checks, and kernel-checked Lean 4 correspondence
proofs and witnesses.

## 1. Environment Setup

From the repository root (`/usr/local/google/Projects/anneal-workspace/anneal-wt-mr-2-1`):

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
```

## 2. Repository Hygiene & Trusted Base Audit

Verify that the hygiene check and Anneal's trusted-base audit pass:

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```

## 3. Mechanical MiniRust Generator & Verbatim Quote Verification

Run the offline test suite for `anneal-minirust-gen`, which checks:
- Deterministic regeneration of `minirust/lean/MiniRustSpec/Generated/*.lean`
  from the vendored MiniRust specification (`minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/`).
- Every `> "..."` quotation in `minirust/lean/MiniRustSpec/Interp.lean` and
  `minirust/lean/MiniRustSpec/Correspondence/Translate.lean` (including
  `Type::Array`, `ValueExpr::Tuple`, `PlaceExpr::Index`, `ptr_offset_inbounds`,
  `dereferenceable`, `signed_dereferenceable`, `rs::TyKind::Array`,
  `smir::ProjectionElem::Index`, `smir::Rvalue::Aggregate(Array)`,
  `smir::Rvalue::Repeat`, and `smir::Rvalue::Len`) against the vendored
  MiniRust specification and `tooling/minimize/src/*.rs`:

```bash
cargo test -p anneal-minirust-gen --offline
```

## 4. Lean 4 Kernel Verification (`MiniRustSpec`)

Compile and kernel-check the full `MiniRustSpec` target (including
`MiniRustSpec.Interp`, `MiniRustSpec.Anchors`,
`MiniRustSpec.Correspondence.Translate`, `MiniRustSpec.Correspondence.Relation`,
`MiniRustSpec.Correspondence.Lemmas`, `MiniRustSpec.Correspondence.MiniRustEval`,
`MiniRustSpec.Correspondence.AnnealEval`, `MiniRustSpec.Correspondence.Simulation`,
`MiniRustSpec.Correspondence.Run`, `MiniRustSpec.Correspondence.Witness`, and
`MiniRustSpec.Audit`):

```bash
cd examples && anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec
```

## 5. Inspecting Anchor, Simulation, and Witness Axiom Audits

To inspect the explicit `#assert_standard_axioms` and
`#assert_all_minirustspec_standard_axioms` output from `MiniRustSpec/Audit.lean`
(including the `[ANCHOR-AUDIT]`, `[SIMULATION-AUDIT]`, and `[WITNESS-AUDIT]`
lines confirming `sorry_free=true` and dependence solely on Lean's standard
axioms `propext`, `Quot.sound`, `Classical.choice`):

```bash
cd examples && anneal-lean-run --mode file --concurrency 3 -- lake env lean ../minirust/lean/MiniRustSpec/Audit.lean | grep -E '\[(ANCHOR|SIMULATION|WITNESS)-AUDIT\]|exhaustively verified'
```

Expected audit summary lines:

```text
MiniRustSpec.Audit: exhaustively verified standard axioms for ... declarations across all MiniRustSpec.* modules
[ANCHOR-AUDIT] sorry_free=true anchors_ok=true anchors_nodup=true
[SIMULATION-AUDIT] sorry_free=true step_correspondence=true mirCall_ret=true mirCall_ub=true
[WITNESS-AUDIT] sorry_free=true arrayOpsOk=true arrayOpsOob=true arraySignedIdx=true zeroArray=true
```
