<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction & Compression Report: FF-4.2 (`adv/ff-4-2`)

Work unit `FF-4.2` migrates the `examples/wireframe-demo`, `examples/tutor`,
and `examples/mir/MirVerification.lean` proofs off hand-written `BlockCtx`
records and per-proof fuel constants, onto the lifting infrastructure in
`Anneal.PureMirExec`, `Anneal.MirLiftCore`, `Anneal.MirLoops`, and
`Anneal.SepLogicLenses`, while keeping `trusted/` byte-for-byte identical to
the base `0d3242d3`.

Every number below is produced by a command in Section 6; rerun them rather
than trusting this file.

## 1. Status summary

- `trusted/` is unchanged (`git diff 0d3242d3 -- trusted/` is empty), and
  `python3 trusted/audit/check_trusted.py --fast` passes.
- No `sorry`, `admit`, `sorryAx`, `#[trusted]`, or `native_decide` in
  `theory/` or `examples/`, and no `axiom` outside the pre-existing
  `Assumptions.FrameTutor.pin_magic` module of the `tutor-ch3` lesson on
  conditional verification. The wireframe-demo and tutor crates verify
  `UNCONDITIONAL`, with `TrustedBoundary kernel replay: PASS`.
- No `BlockCtx` and no fuel numeral in any migrated proof file.
- Proof LOC in `Proof/WireframeDemo/*.lean`: `8,009 → 2,310` (−71.2%) against
  the last complete proof corpus `a6bebfc2`, and `4,264 → 2,310` (−45.8%)
  against `0d3242d3` (whose `clamp_payload_window`, `frame_total_len`, and
  `parse_compression_flag` files are 33/33/158-line stubs without `verified`,
  see Section 3). The migration added `+2,759` net LOC of shared theory
  (Section 3.2).

## 2. Which lifting API each proof uses

| Proof | Route | `#mir_lift` rules | `#mir_lift_spec` | `forRangeUp` | `SepLogicLenses` | Budget |
| :--- | :--- | :---: | :---: | :---: | :---: | :--- |
| `WireframeDemo/frame_total_len` | `verifyMirNoPanic_of_pureExec` + rules | body | — (companions impure) | — | — | companions: `defaultSpecSteps` |
| `WireframeDemo/clamp_payload_window` | `verifyMirNoPanic_of_pureExec` + rules | body | — (companions impure) | — | — | companions: `defaultSpecSteps` |
| `WireframeDemo/parse_compression_flag` | `verifyMirNoPanic_of_pureExec` + rules | body | — (companions impure) | — | — | `requires`: `defaultSpecSteps` |
| `WireframeDemo/decode_wire_header` | `verifyMirNoPanic_of_pureExec` + rules (`eval_n`, `cons_eval_norm`) | body | n/a | — | — | none |
| `WireframeDemo/advance_cursor` | `verifyStatefulMir_of_sepLenses` + `LiftLensBlock` | — | n/a | — | yes | none |
| `WireframeDemo/checksum_frame_safe` | `verifyStatefulMirNoPanic_of_wpConverges` + `mirWpConverges_forRangeUp` | — | n/a | yes | — | entry `29`, iter `36`, exit `5` |
| `WireframeDemo/checksum_frame_fast` | `verifyStatefulEquivMir_of_runCfgSteps` | — | n/a | — | — | `defaultCfgSteps` |
| `MirVerification` (6 pure examples¹) | `*_of_pureExec` + rules | yes | `example_companion_bool_spec_holds` | — | — | none |
| `MirVerification` (trace/stateful/modular²) | `*FuelFree` wrappers | — | — | — | — | fixed `16` |
| `FrameTutor/*` (6 files) | `*FuelFree` wrappers | — | — | — | — | fixed `16`/`64`/`128` |

¹ `addU32SafeClaim_verified`, `addU32TotalClaim_verified`,
`example_companion_bool_spec_holds`, `countdownTotalClaim_verified` (the rules
unroll its three loop iterations), `calleeAddOne_satisfies_contract`, and
`polySwapPairU32Claim_verified`.
² `example_branch_obs_trace_verified`, `reborrowWriteStatefulClaim_verified`,
`pureConstFfiModularClaim_verified`, `callerAddTwoModular_verified`, and the
stateful unaligned-set example.

"Budget" names any remaining bounded evaluation: `defaultSpecSteps body =
16 * #blocks + 80` and `defaultCfgSteps body = 16 * #blocks + 40` are derived
from the CFG size, and the `*FuelFree` wrappers in
`Anneal.Rustc.V2026_06_01.SymbolicEval` fix the budget inside `Anneal`.
`decode_wire_header` (pure `#mir_lift` rules with `eval_n` and `cons_eval_norm`)
and `advance_cursor` (`verifyStatefulMir_of_sepLenses` + `LiftLensBlock`) have
no step budget at all; `checksum_frame_safe` structures its `while i < 4` loop
around `forRangeUp` and `mirWpConverges_forRangeUp` (with per-iteration
`MirStepsConverges` discharged via `mirStepsConverges_of_cfgStepsWP_none`).

Known blocker for the remaining companion and equivalence rows:

- The generated `__anodized_fn_requires_*` / `__anodized_fn_ensures_*`
  companions capture their arguments by reference through a closure
  (`_6 = &_1`, `copy (*_10).0`), so `checkPureMir` is `false` for all six of
  them and the pure `#mir_lift_spec` theorems
  (`mirBoolPredicateHolds_elim_of_pureExec` and friends) do not apply.
  Stepping them with memory-carrying `rfl` rules is impractical as is: the
  first `Rvalue.ref` step alone exceeds `400,000` heartbeats.

## 3. Line counts

### 3.1 `examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo/*.lean`

`wc -l` at each revision. `a6bebfc2` is the last revision whose seven proofs
all compile; at `0d3242d3` three files were truncated to stubs that end after
their `wpReq_inversion` lemma, call the `mir_lift_spec` tactic that the
`Anneal` umbrella never imports, and define no `verified` theorem, so the
`0d3242d3` column understates the cost of a complete proof.

| Proof | `a6bebfc2` | `0d3242d3` | `[adv B1]` `a6aae5b8` | `[adv A1]` `07b582eb` | this revision | vs `a6bebfc2` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `advance_cursor.lean` | 227 | 227 | 171 | 149 | 258 | +13.7% |
| `checksum_frame_fast.lean` | 1,592 | 1,592 | 433 | 433 | 433 | −72.8% |
| `checksum_frame_safe.lean` | 1,242 | 1,242 | 196 | 196 | 569 | −54.2% |
| `clamp_payload_window.lean` | 1,595 | 33 (stub) | 330 | 315 | 315 | −80.3% |
| `decode_wire_header.lean` | 979 | 979 | 425 | 425 | 336 | −65.7% |
| `frame_total_len.lean` | 1,268 | 33 (stub) | 287 | 261 | 261 | −79.4% |
| `parse_compression_flag.lean` | 1,106 | 158 (stub) | 176 | 138 | 138 | −87.5% |
| **Total** | **8,009** | **4,264** | **2,018** | **1,917** | **2,310** | **−71.2%** |

Against `0d3242d3` the total falls by `45.8%` (`4,264 → 2,310`). Lines that
mention `BlockCtx`: `111` at `a6bebfc2` (28/26/26/23/8 in `checksum_frame_fast`,
`checksum_frame_safe`, `clamp_payload_window`, `frame_total_len`,
`parse_compression_flag`), `0` now.

### 3.2 Shared theory added by the migration (`0d3242d3 → this revision`)

| Module | `0d3242d3` | now | Δ | Contents |
| :--- | ---: | ---: | ---: | :--- |
| `theory/Anneal/MirLiftCore.lean` | 1,594 | 4,308 | +2,714 | fast evaluators, `wpBlockLinear`, `runCfgSteps`, `eval_n`/`cons_eval_norm`, `cfgStepsWP`/`mirStepsConverges_of_cfgStepsWP`, `#mir_lift_spec` theorems moved from `MirSpecLift.lean` |
| `theory/Anneal/SepLogicLenses.lean` | 13,655 | 13,677 | +22 | generalized `LiftLensBlock` and `verifyStatefulMir_of_sepLenses` to `isRuntimeMirPhase body.phase = true` |
| `theory/Anneal/Rustc/V2026_06_01/SymReflect.lean` | 7,125 | 7,301 | +176 | `swap_le_u16_lane`, fixed-budget `*FuelFree` wrappers |
| `theory/Anneal/MirSpecLift.lean` | 139 | — | −139 | removed (never imported by `Anneal`, not in `DOWNSTREAM_TARGETS`) |
| `theory/Anneal/PureMirExec.lean` | 18,475 | 18,461 | −14 | `sup/ff-4` `18c85931` (`I-10`) plus unused-binder fixes |
| **Net** | | | **+2,759** | |

The WireframeDemo proofs shrink by `5,699` lines against `a6bebfc2`; less than
half of that moved into reusable theory.

### 3.3 Tutor and `MirVerification`

| File | `0d3242d3` | now | Change |
| :--- | ---: | ---: | :--- |
| `FrameTutor/*.lean` (6 files) | 309 | 300 | fuel arguments replaced by fixed-budget `*FuelFree` wrappers |
| `examples/mir/MirVerification.lean` | 1,986 | 2,042 | 6 pure examples lifted with explicit `#mir_lift` rules (+56: each lift spells out its rule loop) |

## 4. Elaboration cost

Wall-clock time of one sequential `lake env lean` per file (Section 6, step 6)
on `cpl-direct-electron-37838` with `anneal-lean-run --mode file
--concurrency 1`, after `cargo-anneal verify` has built the imports. Each file
sets `maxHeartbeats` itself; no file raises it above `800,000`.

| Proof | `maxHeartbeats` | Wall clock | Dominated by |
| :--- | ---: | ---: | :--- |
| `advance_cursor.lean` | 400,000 | 2.5 s | `verifyStatefulMir_of_sepLenses` + `LiftLensBlock` |
| `checksum_frame_fast.lean` | 800,000 | 56.6 s | `runCfgSteps` unrolling of both bodies |
| `checksum_frame_safe.lean` | 400,000 | 34.4 s | `mirWpConverges_forRangeUp` + per-iteration `cfgStepsWP` |
| `clamp_payload_window.lean` | 800,000 | 23.2 s | companion lemmas |
| `decode_wire_header.lean` | 400,000 | 7.8 s | `LiftStmtsTerminator.eval_n` + `cons_eval_norm` |
| `frame_total_len.lean` | 800,000 | 32.6 s | companion lemmas |
| `parse_compression_flag.lean` | 800,000 | 11.4 s | `requires` companion lemma |

The `#mir_lift` part is cheap: with the companion lemmas replaced by `sorry`
in a scratch copy, the whole of `frame_total_len.lean`, including `import`
time, elaborates in `1.5 s` (`clamp_payload_window.lean`: `1.4 s`,
`parse_compression_flag.lean`: `3.2 s`), and `decode_wire_header.lean`
elaborates in `7.8 s` (down from `18.8 s` under `wpBlockLinear`).

## 5. Changes across passes (`[adv B1]` → `[adv A1]` → `[adv B2]`)

- `advance_cursor` (`[adv B2]`): generalized `LiftLensBlock` and nine
  downstream `SepLogicLenses` theorems from `body.phase = .runtimePostCleanup`
  to `isRuntimeMirPhase body.phase = true` (`theory/Anneal/SepLogicLenses.lean`)
  and migrated `Proof/WireframeDemo/advance_cursor.lean` onto
  `verifyStatefulMir_of_sepLenses` + `LiftLensBlock` (eliminating
  `defaultSpecSteps` and `verifyStatefulMirNoPanic_of_cfg`).
- `decode_wire_header` (`[adv B2]`): added `forcePureEnv?`,
  `evalPureStmtNorm`, `LiftStmtsTerminator.cons_eval_norm`, `evalPureStmtsN`,
  and `LiftStmtsTerminator.eval_n` to `theory/Anneal/MirLiftCore.lean` to
  eliminate `List.set` tower blowup on long straight-line blocks, and migrated
  `Proof/WireframeDemo/decode_wire_header.lean` from
  `verifyMirNoPanic_of_blockLinear` (`18.8 s`, `425` lines) to
  `verifyMirNoPanic_of_pureExec` + `#mir_lift` rules (`7.8 s`, `336` lines,
  `0` `defaultSpecSteps` / `wpBlockLinear`).
- `checksum_frame_safe` (`[adv B2]`): added `cfgStepsWP`,
  `wpMirExecStepsSym_of_runCfgSteps`, `mirStepsConverges_of_cfgStepsWP`,
  `mirStepsConverges_of_cfgStepsWP_none`, `mirWpConverges_of_cfgStateWP`, and
  `mirWpConverges_of_runCfgSteps_none` to `theory/Anneal/MirLiftCore.lean` and
  migrated `Proof/WireframeDemo/checksum_frame_safe.lean` from whole-loop
  `verifyStatefulMirNoPanic_of_runCfgSteps` unrolling onto `forRangeUp`,
  `checksumLoopInv`, `mirWpConverges_forRangeUp`, and
  `verifyStatefulMirNoPanic_of_wpConverges` (`0` `defaultCfgSteps`).
- `frame_total_len`, `clamp_payload_window`, `parse_compression_flag`
  (`[adv A1]`): the subject bodies are lifted with
  `verifyMirNoPanic_of_pureExec` and the `#mir_lift` rules instead of
  `verifyMirNoPanic_of_blockLinear` plus a hundred-symbol `dsimp only` list;
  the unused `ensures_holds_of_eq_*` helpers are gone.
- `MirVerification.lean` (`[adv A1]`): six pure examples (footnote ¹ above) are
  lifted with the rules; `calleeAddOne_satisfies_contract` no longer supplies
  `⟨defaultCfgSteps …, by rfl⟩` as its convergence witness.
- `SymReflect.lean` is unchanged from `[adv B1]`. Its `*FuelFree` wrappers
  only fix the budget of a bounded combinator (`verifyByWPFuelFree c h :=
  verifyByWP c 16 h`), so they are documented here and in `SKILL.md`
  (Pattern E) as fixed-budget evaluators. Renaming them is blocked by the
  audit harness: any edit to `SymReflect.lean` invalidates
  `check_trusted.py --fast`'s cached `tests/mir/SymbolicEvalTests.lean`
  artifact, and recompiling that 2,000-line test suite took `2 m 10 s` under
  `anneal-lean-run --mode file` on this host, beyond the harness's fixed
  60-second per-compile limit. The lifted proofs above do not use the wrappers;
  the tutor and the remaining `MirVerification` examples still do.

## 6. Reproduction commands

Run from the worktree root
(`/home/groupagent-anneal-fuzz-bot/Projects/markdittmer/anneal-wt-ff-4-2`):

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# 1. Trusted computing base unchanged and audited.
git diff --stat 0d3242d3 -- trusted/          # expect no output
python3 trusted/audit/check_trusted.py --fast  # expect PASS
./ci/check_todo.sh                             # expect exit 0

# 2. No soundness escapes. Only expected hit: the pre-existing
#    `Assumptions.FrameTutor.pin_magic` axiom of the tutor-ch3 lesson on
#    conditional verification, which FF-4.2 does not touch.
grep -rnwE 'sorry|admit|sorryAx|native_decide' theory examples \
  --include=*.lean --exclude-dir=.anneal --exclude-dir=.lake
grep -rnE '^\s*(private\s+)?axiom\s' theory examples \
  --include=*.lean --exclude-dir=.anneal --exclude-dir=.lake

# 3. Line counts, BlockCtx, and remaining budgets (Section 3).
D=examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo
for rev in a6bebfc2 0d3242d3; do
  for f in $D/*.lean; do echo "$rev $(basename "$f") $(git show "$rev:$f" | wc -l)"; done
done
wc -l $D/*.lean
grep -c BlockCtx $D/*.lean
grep -c -E 'defaultCfgSteps|defaultSpecSteps' $D/*.lean
grep -n -E 'lift_PureMirConverges|LiftStmtsTerminator|verifyStatefulMir_of_sepLenses|mirWpConverges_forRangeUp' $D/*.lean examples/mir/MirVerification.lean

# 4. Build the theory and the MirVerification examples.
(cd examples && anneal-lean-run --mode build --concurrency 1 -- lake build Anneal MirVerification)

# 5. End-to-end verification with TrustedBoundary kernel replay.
anneal-lean-run --mode build --concurrency 1 -- \
  cargo-anneal verify --manifest-path examples/wireframe-demo/Cargo.toml
anneal-lean-run --mode build --concurrency 1 -- \
  cargo-anneal verify --manifest-path examples/tutor/Cargo.toml
#    expect "Totals: 9 unconditional, 0 conditional" and
#    "Totals: 7 unconditional, 0 conditional", each with
#    "TrustedBoundary kernel replay: PASS".

# 6. Per-file timings (Section 4), after step 5 built the imports.
(cd examples/wireframe-demo/.anneal && TIMEFORMAT='%R s'; for f in ../anneal/proofs/Proof/WireframeDemo/*.lean; do
  echo -n "$f: "
  time anneal-lean-run --mode file --concurrency 1 -- lake env lean "$f"
done)

# 7. Remove the untracked build artifacts before committing.
git status --porcelain   # `examples/*/.anneal/` and `examples/*/Cargo.lock`
