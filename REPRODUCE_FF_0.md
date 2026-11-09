<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction & Closeout Guide: Root Coordinator FF-0 (`sup/ff-0`)

Workstream `FF-0` (`sup/ff-0`) integrates all four supervisor branches
(`sup/ff-1`..`sup/ff-4`) and all 13 leaf adversarial work units (`FF-1.1`,
`FF-1.2`, `FF-1.3`, `FF-2.1`, `FF-2.2`, `FF-2.3`, `FF-3.1`, `FF-3.2`,
`FF-3.3`, `FF-4.1`, `FF-4.2`, `FF-4.2b`, and `FF-4.3`) for Anneal's fuel-free
MIR program lifters and two-tier alias-erasure discipline, reconciled with
upstream `sup/brief-4` (`087b015b`).

For supervisor- and leaf-level reproduction guides, see `REPRODUCE_FF_1.md`
(`REPRODUCE_FF_1_{1,2,3}.md`), `REPRODUCE_FF_2.md`
(`REPRODUCE_FF_2_{1,2,3}.md`), `REPRODUCE_FF_3_{1,2,3}.md`, and
`REPRODUCE_FF_4.md` (`REPRODUCE_FF_4_{1,2,2B,3}.md`).

> [!WARNING]
> **`[diversity-reduced]` & Reserve-Fallback 3rd-Party Audit Notice**
>
> Under the `hierarchical-supervision` + `model-policy-cli` quota reserve
> policy (`P0 = 2%`, `P1 = 15%`, `P2 = 40%`), the following leaf units executed
> either wholly or partially under `[diversity-reduced]` or `MODEL_Z_RESERVE`
> (`supervisor-model-primary` / `supervisor-model-fallback`) fallback when `Model X`
> (`model-family-x-primary`) or `Model Y` (`model-family-y-primary`) was below the
> tier reserve floor:
>
> - **Single-Family `[diversity-reduced]` Leaves (Require Cross-Family `Model X`
>   or Human 3rd-Party Audit Before `main` Merge / `reference` Publication)**:
>   - `FF-1.1` (`58f80e68`), `FF-1.2` (`18ac6afd`), `FF-1.3` (`a2988dd4`)
>   - `FF-2.1` (`259e4f94`), `FF-2.2` (`1568fef3`), `FF-2.3` (`51fd2dfe`)
>   - `FF-3.1` (`9a48afb7`), `FF-3.2` (`c66b48f9`)
>   - `FF-4.1` Pass `B4` (`a6bebfc2`; Rounds 1-3 ran cross-family `Claude <->
>     Gemini`, Pass `B4` switched `ff41-b` to `supervisor-model-primary`)
>   - `FF-4.3` (`adv/ff-4-3` @ `549ffba8` -> `sup/ff-4` @ `05763dcf`; local
>     `zerocopy-reference` `adv/ff-4-3-reference` @ `8ceec4bd6`)
> - **Cross-Family Leaves With `MODEL_Z_RESERVE` Substitution (True `Anthropic
>   Claude <-> Google Gemini` Diversity Preserved Across All Passes)**:
>   - `FF-3.3` (`e4760a0e`: `model-family-x-primary` vs `model-family-y-primary`)
>   - `FF-4.2` (`60d08cac` -> `25814f93`: `model-family-x-primary` vs
>     `model-family-y-primary` -> `supervisor-model-primary` on Pass `B4`)
>   - `FF-4.2b` (`cfad3ee4` -> `9ec41a30`: `model-family-x-primary` vs
>     `supervisor-model-primary` across all 5 passes)
>
> Both frontier pools (`model-family-x-primary` and `model-family-y-primary`) have
> now refreshed (`>96%` available). Run a cross-family (`Model X`) or human
> review on the single-family `[diversity-reduced]` units listed above prior to
> merging `sup/ff-0` to `main` or pushing `adv/ff-4-3-reference` to
> `google/zerocopy`.

---

## 1. End-to-End Architecture & Workstream Summary

1. **`FF-1` (`sup/ff-1` @ `18ac6afd`: `FF-1.1`, `FF-1.2`, `FF-1.3`)**:
   - Eliminated manual step-fuel parameters from MIR verification theorems via
     fuel-free reachability (`StepsTo`, `StepsToTerminal`, `WpConverges`) in
     `theory/Anneal/MirFuelFree.lean`, structural bounded-range loop invariants
     (`forRangeUp`, `runCfgToBlock`) in `theory/Anneal/MirLoops.lean`, and
     Tier 1 pure stack-local alias erasure (`PureState`, `evalPureBlock`) in
     `theory/Anneal/PureMirExec.lean`.
2. **`FF-2` (`sup/ff-2` @ `51fd2dfe`: `FF-2.1`, `FF-2.2`, `FF-2.3`)**:
   - Introduced relational Hoare block triples (`LiftBlock`), backward WP
     chaining (`liftBlock_seq`), and inter-procedural `#[spec]` /
     `#[external_spec]` call lifting (`liftBlock_call_spec`, `#mir_lift_spec`)
     in `theory/Anneal/MirSpecLift.lean`.
3. **`FF-3` (`sup/ff-3` @ `e4760a0e`: `FF-3.1`, `FF-3.2`, `FF-3.3`)**:
   - Implemented the `#mir_lift` metaprogramming command in
     `theory/Anneal/MirLiftCore.lean` and `theory/Anneal/MirLift.lean`,
     automatically synthesizing per-block `LiftBlock` theorems, acyclic DAG
     continuations, and closed whole-function `VerificationResult` /
     `TotalVerificationResult` / `EquivVerificationResult` proofs without
     hand-written `BlockCtx` records or fuel numerals.
4. **`FF-4` (`sup/ff-4` @ `10f309cf`: `FF-4.1`, `FF-4.2`, `FF-4.2b`,
   `FF-4.3`)**:
   - **`FF-4.1` (`a6bebfc2`)**: Built Tier 2 separation-logic lenses (`MutLens`,
     `DisjointSiblings`, `LiftLensBlock`, `verifyStatefulMir_of_sepLenses`) in
     `theory/Anneal/SepLogicLenses.lean` and updated `skills/anneal-prove/`.
   - **`FF-4.2` (`60d08cac` -> `25814f93`)**: Migrated all 7 `WireframeDemo`
     proofs (`8,009 -> 1,421` LOC, **`-82.3%`** vs `a6bebfc2` / **`-66.7%`** vs
     `0d3242d3`; deterministic elaboration heartbeats **`-52.1%`**),
     `FrameTutor/*.lean`, and 6 pure `MirVerification.lean` proofs with zero
     `BlockCtx`, zero manual fuel/step numerals, and zero `iterate k`.
   - **`FF-4.2b` (`cfad3ee4` -> `9ec41a30`)**: Semantically reconciled
     `sup/brief-4` (`087b015b`) with `FF-1..FF-4.2` with zero upstream file
     reversions and optimized standalone `PureMirExec.lean` compile time from
     `85 s` to `35.1 s`.
   - **`FF-4.3` (`549ffba8` -> `05763dcf`; local `zerocopy-reference`
     `adv/ff-4-3-reference` @ `8ceec4bd6`)**: Added non-breaking `#mir_lift` /
     `#mir_lift_spec` / `forRangeUp` / `SepLogicLenses` strategy selection and
     starter hints to `cargo-anneal` (`99/99` tests passing across 11 suites)
     and authored the self-contained cold-reader report package
     `reports/anneal-fuel-free-mir-lifting-and-alias-erasure/` (`18`
     constructive Lean `v4.34.1` theorems, `0` push to `origin/reference`).

---

## 2. Reproducible Verification Receipts (`sup/ff-0`)

Run from `<path/to/anneal>`:

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# 1. Repository hygiene & TrustedBoundary kernel replay audit
cd <path/to/anneal>
./ci/check_todo.sh
git diff 087b015b..HEAD -- trusted/lean/
python3 trusted/audit/check_trusted.py --fast

# 2. WireframeDemo compression & zero-fuel / zero-BlockCtx invariants
D=examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo
wc -l $D/*.lean
! grep -nE 'BlockCtx|defaultCfgSteps|runCfgSteps' $D/*.lean
! grep -nE 'LiftBlock .* [0-9]+ :=|^\s*[0-9]+ := by|\(n := [0-9]+\)' $D/*.lean
! grep -nE '\brfl [0-9]+\b|iterate [0-9]+' $D/*.lean

# 3. Lean 4 theory + MirVerification + full cargo-anneal test suite (99 tests)
(cd examples && \
  anneal-lean-run --mode build --concurrency 1 -- \
  lake build Anneal MiniRust MirVerification)
anneal-lean-run --mode build --concurrency 1 -- cargo miri setup
anneal-lean-run --mode build --concurrency 1 -- cargo test -p cargo-anneal

# 4. End-to-end crate verification with TrustedBoundary kernel replay
anneal-lean-run --mode build --concurrency 1 -- \
  ./target/debug/cargo-anneal verify \
  --manifest-path examples/wireframe-demo/Cargo.toml
anneal-lean-run --mode build --concurrency 1 -- \
  ./target/debug/cargo-anneal verify \
  --manifest-path examples/tutor/Cargo.toml
rm -rf examples/wireframe-demo/.anneal examples/wireframe-demo/Cargo.lock \
  examples/tutor/.anneal examples/tutor/Cargo.lock
test -z "$(git status --porcelain)"

# 5. Local zerocopy-reference report package & no-push verification
cd <path/to/zerocopy-reference>
test "$(git rev-parse origin/reference)" = \
  "64e9b5c4d271fe3f3aadfea71f36bc784ff3391b"
python3 \
reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/verify_probes.py
python3 tools/reference.py catalog
python3 tools/reference.py check
python3 -m unittest discover -s tests
test -z "$(git status --porcelain)"
```

---

## 3. Publishing `adv/ff-4-3-reference` to `google/zerocopy` (`markdittmer`)

`origin/reference` (`64e9b5c4d271fe3f3aadfea71f36bc784ff3391b`) has **not** been
pushed. After human / cross-family review of `adv/ff-4-3-reference`
(`8ceec4bd6`), follow `REPRODUCE_FF_4_3.md` §4 (or `REPRODUCE_FF_4.md` §4) to
stage the report directory onto `origin/reference` as a single linear
fast-forward commit and push `HEAD:refs/heads/reference` from workstations.
