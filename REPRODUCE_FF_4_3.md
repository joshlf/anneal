<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction & Publication Guide: FF-4.3 (`adv/ff-4-3`)

Work unit `FF-4.3` delivers:

1. **Tailored MIR Lifting Strategy Guidance & Starter Hints in `cargo-anneal`**
   (`crates/cargo-anneal/src/{scaffold.rs,agent.rs,lib.rs}`): non-breaking
   `#mir_lift`, `#mir_lift_spec`, `forRangeUp` / `runCfgToBlock`, and
   `Anneal.SepLogicLenses` strategy selection surfaced in both starter
   `Proof/<Item>.lean` files (`--init-proofs`) and `cargo anneal agent-context`.
2. **Self-Contained `zerocopy-reference` Convergence & Benchmark Report Package**
   (`reports/anneal-fuel-free-mir-lifting-and-alias-erasure/` on local branch
   `adv/ff-4-3-reference` in
   `/home/groupagent-anneal-fuzz-bot/Projects/markdittmer/zerocopy-reference`):
   synthesizes the fuel-free MIR lifting, two-tier alias-erasure, bounded range
   loop, and elaboration-scaling results with a standalone Lean `v4.34.1`
   mechanization (`support/FuelFreeMirLiftingAndLensesProbe.lean`), empirical
   dataset (`support/wireframe_benchmark_metrics.json`), and automated probe
   verifier (`support/verify_probes.py`).

> [!WARNING]
> **`[diversity-reduced]` 3rd-Party Audit Notice**
>
> Under Priority Tier `P2` (`40%` frontier reserve floor), `anneal-model-policy`
> recorded `MODEL_X` (`opus-5.5-max`, `3p-wtu-daily`) at `4.5%` remaining (`<
> 40%` floor) and `MODEL_Y` (`gemini-launch-candidate-high`) at `0.0%`
> remaining. Both adversarial leaf slots (`ff43-a` and `ff43-b`) therefore
> executed on the single-family reserve model `gemini-pro-coordinator` (`Family
> Z`, `DIVERSITY_REDUCED=true`). Before merging `adv/ff-4-3` into `main` or
> publishing `adv/ff-4-3-reference` to `google/zerocopy` `refs/heads/reference`,
> run an independent cross-family (`Model X`) or human review pass.

---

## 1. Summary of `cargo-anneal` Changes (`adv/ff-4-3`)

### 1.1 Static MIR Lifting Profile (`crates/cargo-anneal/src/scaffold.rs`)

- Added `MirLiftingProfile`, `analyze_mir_lifting_profile`, and
  `analyze_workspace_lifting_profile`, which inspect the generated
  `Mir/<Item>.lean` module (after stripping `--` line comments, nested `/- ...
  -/` block comments, and double-quoted string literals so user string constants
  cannot spoof AST tokens) to mirror `Anneal.PureMirExec.checkPureMir` and
  classify each verification target along four axes:
  1. `body_appears_pure`: absence of `.deref`, `.unwrapUnsafeBinder`,
     `BinOp.offset`, `Rvalue.{ref, rawPtr, threadLocalRef, shallowInitBox,
     copyForDeref}`, `CastKind.{pointerCoercion, fnPtrToPtr, ptrToPtr}`,
     `ConstValue.indirect`, `ConstSlice.ptr`, `StatementKind.{fakeRead, retag,
     backwardIncompatibleDropHint}`, non-`assume` intrinsics, and
     `TerminatorKind.{call, tailCall, inlineAsm}`.
  2. `has_mut_ref`: presence of mutable reference types or borrows
     (`RigidTy.ref Mutability.mut`, `BorrowKind.mut`) indicating Tier 2
     `Anneal.SepLogicLenses` (`MutLens`, `SepLensStateInv`,
     `SepSubplaceLensStateInv`, `LiftLensBlock`, `verifyStatefulMir_of_sepLenses`).
  3. `has_loop_backedge`: presence of a CFG edge `bb_i -> bb_j` with `j <= i`
     indicating fuel-free loop invariants via `Anneal.MirLoops.forRangeUp`
     (`mirNoCallWpConverges_forRangeUp`) and `Anneal.MirLiftCore.runCfgToBlock`.
  4. `companions_appear_pure` vs. `has_impure_companion`: distinguishes
     `#[requires]` / `#[ensures]` companion bodies eligible for
     `#mir_lift_spec` + `holdBoolReq_of_mirBool` from closure-capturing
     companions (`Rvalue.ref` + `.deref`) that require `defaultSpecSteps` and
     count-free `repeat` unfolding.
- Added `render_scaffold_lifting_hints` and `render_proof_template_with_hints`
  (re-exported from `crates/cargo-anneal/src/lib.rs`), emitting `<= 80`-column
  `--` Lean comment blocks compatible with `TrustedBoundary.lean` and ignored by
  comment-stripping checks in `detect_authored_item_modules` and
  `check_specs_non_vacuous`.

### 1.2 `agent-context` Strategy Guide (`crates/cargo-anneal/src/agent.rs`)

- Updated `render_agent_context` to include:
  - A top-level `## Proof Lifting Strategy Guide (Lift First, Evaluate Last)`
    documenting Patterns A (`#mir_lift` + `#mir_lift_spec`), B (`forRangeUp` +
    `runCfgToBlock`), C (`Anneal.SepLogicLenses`), D (stateful/interprocedural
    `MirWpConverges`), and `TrustedBoundary` zero-fuel / count-free `repeat`
    discipline;
  - A per-target `### Recommended Lifting Strategy` subsection tailored to that
    item's `MirLiftingProfile`; and
  - Hint-enriched `### Starter Proof Template` blocks matching `--init-proofs`.
- Added unit tests in `scaffold.rs`
  (`scaffold_init_proofs_surfaces_tailored_lifting_hints_within_80_cols`) and
  `agent.rs`
  (`render_agent_context_surfaces_mir_lift_spec_loops_and_sep_logic_lenses_guidance`).

### 1.3 Post-`FF-4.2b` Integration Sync (`WireframeDemo` `layoutIdx` & `Tutor` Chapters)

- Updated `examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo/{decode_wire_header,checksum_frame_fast}.lean`
  to match the fresh `layoutIdx` numbering emitted by post-`087b015b`
  `anneal-rustc-capture` (`[u8; 4]` `layoutIdx := 1 -> 2` in
  `decode_wire_header.lean`; `[u16; 4]` `layoutIdx := 2 -> 5` in
  `checksum_frame_fast.lean`), keeping `Proof/WireframeDemo/*.lean` at `1,421`
  LOC (`0` `BlockCtx`, `0` fuel) and restoring `end_to_end_demo_journeys`.
- Synchronized `examples/tutor-ch4/anneal/proofs/Proof/FrameTutor/{advance_offset,pin_magic,total_frame_len}.lean`
  with `examples/tutor`'s `*FuelFree` wrappers and regenerated
  `docs/tutor/{01,02,04,05}-*.md` via `python3 docs/tutor/workflow/tutor_workflow.py render`
  (reflecting both `*FuelFree` tutor proofs and the new `--init-proofs`
  lifting hints in Chapter 4), restoring all 4 `end_to_end_tutor` tests (`96
  passed; 0 failed` across all 11 `cargo test -p cargo-anneal` suites).

---

## 2. Summary of Local `zerocopy-reference` Report Package

Committed **locally only** on branch `adv/ff-4-3-reference` in
`/home/groupagent-anneal-fuzz-bot/Projects/markdittmer/zerocopy-reference`
(`origin/reference` remains untouched at `64e9b5c4d`):

- `reports/anneal-fuel-free-mir-lifting-and-alias-erasure/REPORT.json`:
  canonical topic namespaces (`anneal/*`, `lean/*`, `rust/*`, `verification/*`),
  12 durable upstream `subjects` (`leanprover/lean4` `v4.34.1`, `rust-lang/rust`
  `1.98.0-nightly`, `joshlf/anneal` `origin/main` revisions `5fc1139f`,
  `f2bc17e9`, `c065b55a`, and primary PL/verification papers), and
  `"observed_at": "2026-11-07"`.
- `reports/anneal-fuel-free-mir-lifting-and-alias-erasure/REPORT.md`:
  self-contained cold-reader technical report with all six canonical H2 sections
  (`Summary`, `Applicability`, `Findings`, `Boundaries`, `Evidence`,
  `Revalidation`), explicit `Basis:` roles on findings `F-01`–`F-08`, and
  explicit `Boundaries` classifications (`unsupported`, `known not to apply`,
  `not examined`, `unknown`).
- `reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/`:
  - `FuelFreeMirLiftingAndLensesProbe.lean`: 502-line self-contained Lean
    `v4.34.1` mechanization (`Init`-only, zero `sorry`, constructive axioms
    only) proving `evalFuel_mono`, `StepsTo.bind_wp`, `stepPure_simulates`,
    `wpConverges_of_pureExec`, `chained_sets_collapse_rfl`,
    `forRangeUp_induction`, `wpConverges_forRangeUp`,
    `subplaceFieldLens_disjoint`, and `liftLens_twoBorrowAdd_sound`.
  - `wireframe_benchmark_metrics.json`: verified per-function LOC (`8,009 ->
    1,421`, `-82.3%`), `BlockCtx` (`111 -> 0`), deterministic heartbeats
    (`1,388,934k -> 665,228k`, `-52.1%`), shared-theory amortization (`+2,972`
    net LOC), and `PureMirExec` scaling (`85 s -> 35.1 s`).
  - `verify_probes.py`: automated verifier running Lean `v4.34.1`, `#print
    axioms` audit, and dataset cross-checks.
- `CATALOG.json`: deterministically regenerated by `python3 tools/reference.py
  catalog` (`166` reports).

---

## 3. Exact Verification Commands

Run from `/home/groupagent-anneal-fuzz-bot/Projects/markdittmer/anneal-wt-ff-4-3`:

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# 1. Repository hygiene & TrustedBoundary audit
cd /home/groupagent-anneal-fuzz-bot/Projects/markdittmer/anneal-wt-ff-4-3
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast

# 2. Full cargo-anneal unit + integration test suite & Anneal theory build
anneal-lean-run --mode build --concurrency 1 -- cargo test -p cargo-anneal
cd examples && anneal-lean-run --mode build --concurrency 1 -- lake build Anneal

# 3. Reference corpus catalog, structural check, unit tests, and Lean probe
cd /home/groupagent-anneal-fuzz-bot/Projects/markdittmer/zerocopy-reference
python3 reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/verify_probes.py
python3 tools/reference.py catalog
python3 tools/reference.py check
python3 -m unittest discover -s tests
```

---

## 4. Step-by-Step Inspection & Publication Instructions for `markdittmer`

Per architectural constraint §2.1, **nothing has been pushed** to
`origin/reference`. Follow these steps to inspect the local package and publish
it atomically to `google/zerocopy` `refs/heads/reference`:

### Step 1: Inspect the Local Candidate on the Capsule

```bash
cd /home/groupagent-anneal-fuzz-bot/Projects/markdittmer/zerocopy-reference
git status --short
git log --oneline origin/reference..adv/ff-4-3-reference
git diff --stat origin/reference..adv/ff-4-3-reference
python3 reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/verify_probes.py
python3 tools/reference.py check
```

Confirm `origin/reference` is still `64e9b5c4d` (or the latest upstream tip) and
that only `CATALOG.json` and
`reports/anneal-fuel-free-mir-lifting-and-alias-erasure/` differ.

### Step 2: Export the Candidate Package to Shared x20 Staging (Optional if Publishing from Cloudtop)

If publishing from your personal Cloudtop checkout of `google/zerocopy` rather
than directly via Capsule sync, archive the validated report directory to x20
using `fileutil` at HEAD (never `/google/data/rw/...`):

```bash
tar -C /home/groupagent-anneal-fuzz-bot/Projects/markdittmer/zerocopy-reference \
  -czf /tmp/ff43-reference-report.tar.gz \
  reports/anneal-fuel-free-mir-lifting-and-alias-erasure

/usr/bin/fileutil --x20_force_client_creation_at_head cp -f \
  /tmp/ff43-reference-report.tar.gz \
  /x20/teams/anneal-agent/markdittmer/ff43-reference-report.tar.gz
rm -f /tmp/ff43-reference-report.tar.gz
```

### Step 3: Atomic Single-Parent Fast-Forward Publication to `refs/heads/reference`

Following `zerocopy-reference/AGENTS.md` ("Publication", Steps 1–7), on your
authenticated `google/zerocopy` `reference` worktree on Cloudtop:

```bash
# 1. Fetch and inspect the current remote reference tip
git fetch origin reference
git checkout -B reference-publish origin/reference

# 2. Materialize the report package onto the observed remote tip
/usr/bin/fileutil --x20_force_client_creation_at_head cp -f \
  /x20/teams/anneal-agent/markdittmer/ff43-reference-report.tar.gz \
  /tmp/ff43-reference-report.tar.gz
tar -xzf /tmp/ff43-reference-report.tar.gz
rm -f /tmp/ff43-reference-report.tar.gz

# 3. Regenerate CATALOG.json and run self-validation + probe verification
python3 reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/verify_probes.py
python3 tools/reference.py catalog
python3 tools/reference.py check
git status --short

# 4. Create a single coherent linear commit whose sole parent is origin/reference
git add CATALOG.json reports/anneal-fuel-free-mir-lifting-and-alias-erasure
git commit -m "[reference] Add fuel-free MIR lifting and alias-erasure report"

# 5. Fast-forward push to refs/heads/reference (never --force, never merge)
#    If another writer advanced origin/reference, fetch, git rebase origin/reference,
#    rerun 'python3 tools/reference.py catalog && python3 tools/reference.py check',
#    and retry.
git push origin HEAD:refs/heads/reference

# 6. Read back the remote tip and verify clean linear history
git fetch origin reference
git rev-parse HEAD origin/reference
```
