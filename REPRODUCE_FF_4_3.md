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
2. **Self-Contained `zerocopy-reference` Convergence & Benchmark Report**
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
  `analyze_workspace_lifting_profile`, which inspect inline `basicBlocks :=`
  definitions in `Mir/<Item>.lean` (falling back to `target/anneal/units` before
  `scaffold` runs and skipping non-inline alias wrappers) using single-pass
  string- and char-literal-aware comment/literal stripping
  (`strip_lean_comments_and_strings`, preventing `"--"` or `"/-"` inside `span`
  or `defPath` strings from inverting string polarity) to mirror
  `Anneal.PureMirExec.checkPureMir` across five axes:
  1. `is_pure_call_free_candidate`: absence of `.deref`, `.unwrapUnsafeBinder`,
     `BinOp.offset`, `Rvalue.{ref, rawPtr, threadLocalRef, shallowInitBox,
     copyForDeref}` (without false-triggering on nested `RigidTy.{ref, rawPtr}`
     or pure `AggregateKind.rawPtr`), `CastKind.{pointerCoercion, fnPtrToPtr,
     ptrToPtr}`, `ConstValue.indirect`, `ConstValue.slice (ConstScalar.ptr ..)`,
     `StatementKind.{retag, backwardIncompatibleDropHint}`, non-`assume`
     intrinsics, and `TerminatorKind.{call, tailCall, inlineAsm}`.
  2. `has_mut_borrow` vs. `has_deref_projection`: separates exclusive `&mut`
     borrows (`BorrowKind.mut`, or `ProjectionElem.deref` with `&mut` locals)
     targeting Tier 2 `Anneal.SepLogicLenses` (`SepLensStateInv`,
     `SepSubplaceLensStateInv`, `LiftLensBlock`, and
     `verifyStatefulMir_of_sepLenses`) from read-only shared `&T` or
     raw-pointer dereferences (`Anneal.PureMirExec.runCfgToBlock` +
     `Anneal.MirFuelFree.verifyStatefulMirNoPanic_of_wpConverges` or
     `Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeStatefulEqFuelFree`).
  3. `has_cfg_back_edge`: presence of a CFG edge `bb_i -> bb_j` with `j <= i`
     (including `u128` `SwitchTargets` discriminants and `UnwindAction.cleanup`
     edges) indicating fuel-free loop invariants via
     `Anneal.MirLoops.forRangeUp` (`mirNoCallWpConverges_forRangeUp`) and
     `Anneal.PureMirExec.runCfgToBlock`.
  4. `type_param_count`: generic `CapturedMir` bodies (`CapturedMir.instantiate`
     / `LayoutTable.instantiateForBody` via `open Trusted.MirAst
     Anneal.PureMirExec Anneal.MirLiftCore` and fuel-free lifting of `*ClaimFor
     typeArgs`).
  5. `has_inline_companions` & `has_impure_inline_companions`: distinguishes
     `#[spec]` `requires` / `ensures` companion bodies eligible for the
     `#mir_lift_spec` theorem family in `Anneal.PureMirExec`
     (`mirBoolPredicateHolds_*_of_pureExec`) from closure-capturing companions
     (`Rvalue.ref` + `.deref`) that use `holdBoolReq_of_mirBool` + count-free
     `repeat` and `hold_mirBool_of_blockLinear` (`defaultSpecSteps`).
- Added `render_scaffold_lifting_hints` and `render_proof_template_with_hints`
  (re-exported from `crates/cargo-anneal/src/lib.rs`), emitting `<= 80`-column
  `--` Lean comment blocks with verified `open` namespaces (`Trusted.MirAst`,
  `Anneal.PureMirExec`, `Anneal.MirLiftCore`, `Anneal.MirFuelFree`,
  `Anneal.MirLoops`, `Anneal.SepLogicLenses`, `Anneal.FunctionalTranslation`,
  `Anneal.BitValidity`, and `Anneal.Rustc.V2026_06_01.SymbolicEval`), compatible
  with `TrustedBoundary.lean` and ignored by comment-stripping checks in
  `detect_authored_item_modules` and `check_specs_non_vacuous`.

### 1.2 `agent-context` Strategy Guide (`crates/cargo-anneal/src/agent.rs`)

- Made `strip_lean_comments` string- and char-literal-aware so `"--"` or `"/-"`
  inside `ItemSpec "..."` string literals never truncates spec declarations.
- Updated `render_agent_context` (including pre-scaffold fallback to
  `target/anneal/units`) to include:
  - A top-level `## Proof Lifting Strategy Guide (Lift First, Evaluate Last)`
    documenting `#mir_lift` (`argCount = 0` closed-body elaborator) vs.
    parametric `Proof/*.lean` `LiftBlock` rules, `#mir_lift_spec` companion
    theorems, `forRangeUp` + `runCfgToBlock`, `Anneal.SepLogicLenses`,
    `Anneal.BitValidity`, and `TrustedBoundary` zero-fuel / count-free `repeat`
    discipline;
  - A per-target `### Recommended Lifting Strategy` subsection tailored to that
    item's `MirLiftingProfile` and `CapturedItemKind`; and
  - Hint-enriched `### Starter Proof Template` blocks matching `--init-proofs`.
- Added unit tests in `scaffold.rs`
  (`scaffold_init_proofs_surfaces_tailored_lifting_hints_within_80_cols`,
  `mir_lifting_profile_handles_strings_slice_ptrs_u128_and_cleanup`) and
  `agent.rs`
  (`strip_lean_comments_preserves_comment_markers_inside_string_literals`
  and `render_agent_context` lifting-strategy coverage).

### 1.3 Post-`FF-4.2b` Integration Sync (`WireframeDemo` & `Tutor`)

- Updated `WireframeDemo/{decode_wire_header,checksum_frame_fast}.lean` under
  `examples/wireframe-demo/anneal/proofs/Proof/` to match the fresh `layoutIdx`
  numbering emitted by post-`087b015b` `anneal-rustc-capture` (`[u8; 4]`
  `layoutIdx := 1 -> 2` in `decode_wire_header.lean`; `[u16; 4]` `layoutIdx :=
  2 -> 5` in `checksum_frame_fast.lean`), keeping `Proof/WireframeDemo/*.lean`
  at `1,421` LOC (`0` `BlockCtx`, `0` fuel) and restoring
  `end_to_end_demo_journeys`.
- Synchronized `FrameTutor/{advance_offset,pin_magic,total_frame_len}.lean`
  under `examples/tutor-ch4/anneal/proofs/Proof/` with `examples/tutor`'s
  `*FuelFree` wrappers and regenerated `docs/tutor/{01,02,04,05}-*.md` via
  `python3 docs/tutor/workflow/tutor_workflow.py render`, restoring all 4
  `end_to_end_tutor` tests (`98 passed; 0 failed` across all 11 `cargo test -p
  cargo-anneal` suites).

---

## 2. Summary of Local `zerocopy-reference` Report Package

Committed **locally only** on branch `adv/ff-4-3-reference` in
`/home/groupagent-anneal-fuzz-bot/Projects/markdittmer/zerocopy-reference`
(`origin/reference` remains untouched at `64e9b5c4d`):

- `reports/anneal-fuel-free-mir-lifting-and-alias-erasure/REPORT.json`:
  canonical topic namespaces (`anneal/*`, `lean/*`, `rust/*`, `verification/*`),
  12 durable upstream `subjects` (`leanprover/lean4` `v4.34.1`, `rust-lang/rust`
  `1.98.0-nightly`, `joshlf/anneal` revisions `5fc1139f`, `f2bc17e9`,
  `c065b55a`, and primary PL/verification papers), and `"observed_at":
  "2026-11-07"`.
- `reports/anneal-fuel-free-mir-lifting-and-alias-erasure/REPORT.md`:
  self-contained cold-reader technical report (`<= 80`-column prose) with all
  six canonical H2 sections (`Summary`, `Applicability`, `Findings`,
  `Boundaries`, `Evidence`, `Revalidation`), explicit `Basis:` roles on
  findings `F-01`–`F-08`, and explicit `Boundaries` classifications
  (`unsupported`, `known not to apply`, `not examined`, `unknown`).
- `reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/`:
  - `FuelFreeMirLiftingAndLensesProbe.lean`: 837-line self-contained Lean
    `v4.34.1` mechanization (`Init`-only, zero `sorry`, constructive axioms
    only) proving 17 exported theorems: `evalFuel_mono`, `StepsTo.bind_wp`,
    `checkPureProg_rejects_deref`, `stepPure_simulates`,
    `wpConverges_of_pureExec`, `chained_sets_collapse_rfl`,
    `forRangeUp_induction`, `wpConverges_forRangeUp`,
    `stepsTo_of_runToTarget_reached`, `wpConverges_of_runToTarget_halted`,
    `runToTarget_mono_bound`, `stepsTo_of_runCfgToBlock_reached`,
    `wpConverges_of_runCfgToBlock_halted`, `no_uniform_fuel_countUp`,
    `countUp_wpConverges_all_n`, `subplaceFieldLens_disjoint`, and
    `liftLens_twoBorrowAdd_sound`.
  - `wireframe_benchmark_metrics.json`: verified per-function LOC (`8,009 ->
    1,421`, `-82.3%`), `BlockCtx` (`111 -> 0`), deterministic heartbeats
    (`1,388,934k -> 665,228k`, `-52.1%`), `uses_mir_lift_rules` classification,
    shared-theory migration delta (`+2,972` net LOC), and post-integration
    module LOC (`PureMirExec.lean` `20,564` LOC, `85 s -> 35.1 s`).
  - `verify_probes.py`: automated verifier checking 80-column formatting, Lean
    `v4.34.1` compilation, `#print axioms` on all 17 theorems, zero step/fuel
    numerals in `countUp_wpConverges_all_n`, report prose width /
    theorem-declaration line-range citations / public-hygiene checks, and
    dataset cross-checks.
- `CATALOG.json`: deterministically regenerated by `python3 tools/reference.py
  catalog` (`166` reports).

---

## 3. Exact Verification Commands

Run from the worktree root
(`/home/groupagent-anneal-fuzz-bot/Projects/markdittmer/anneal-wt-ff-4-3`):

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
python3 \
reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/verify_probes.py
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
python3 \
reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/verify_probes.py
python3 tools/reference.py check
```

Confirm `origin/reference` is still `64e9b5c4d` (or the latest upstream tip) and
that only `CATALOG.json` and
`reports/anneal-fuel-free-mir-lifting-and-alias-erasure/` differ.

### Step 2: Export Candidate Package to Shared x20 Staging (Optional)

If publishing from your personal Cloudtop checkout of `google/zerocopy` rather
than directly via Capsule sync, archive the validated report directory to x20
using `fileutil` at HEAD (never `/google/data/rw/...`):

```bash
cd /home/groupagent-anneal-fuzz-bot/Projects/markdittmer/zerocopy-reference
tar -czf /tmp/ff43-reference-report.tar.gz \
  reports/anneal-fuel-free-mir-lifting-and-alias-erasure

/usr/bin/fileutil --x20_force_client_creation_at_head cp -f \
  /tmp/ff43-reference-report.tar.gz \
  /x20/teams/anneal-agent/markdittmer/ff43-reference-report.tar.gz
rm -f /tmp/ff43-reference-report.tar.gz
```

### Step 3: Atomic Single-Parent Fast-Forward Publication to `reference`

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
python3 \
reports/anneal-fuel-free-mir-lifting-and-alias-erasure/support/verify_probes.py
python3 tools/reference.py catalog
python3 tools/reference.py check
git status --short

# 4. Create a single linear commit whose sole parent is origin/reference
git add CATALOG.json reports/anneal-fuel-free-mir-lifting-and-alias-erasure
git commit -m "[reference] Add fuel-free MIR lifting and alias-erasure report" \
  -m "Agent-authored-by: AI agent acting on Mark Dittmer's behalf"

# 5. Fast-forward push to refs/heads/reference (never --force, never merge).
#    If another writer advanced origin/reference, fetch, rebase onto
#    origin/reference, rerun catalog + check, and retry.
git push origin HEAD:refs/heads/reference

# 6. Read back the remote tip and verify clean linear history
git fetch origin reference
git rev-parse HEAD origin/reference
```
