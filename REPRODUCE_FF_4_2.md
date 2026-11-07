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
- Proof LOC in `Proof/WireframeDemo/*.lean`: `8,009 → 1,917` (−76.1%) against
  the last complete proof corpus `a6bebfc2`, and `4,264 → 1,917` (−55.0%)
  against `0d3242d3` (whose `clamp_payload_window`, `frame_total_len`, and
  `parse_compression_flag` files are 33/33/158-line stubs without `verified`,
  see Section 3). The migration added `+2,216` net LOC of shared theory
  (Section 3.2).

## 2. Which lifting API each proof uses

| Proof | Route | `#mir_lift` rules | `#mir_lift_spec` | `forRangeUp` | `SepLogicLenses` | Budget |
| :--- | :--- | :---: | :---: | :---: | :---: | :--- |
| `WireframeDemo/frame_total_len` | `verifyMirNoPanic_of_pureExec` + rules | body | — (companions impure) | — | — | companions: `defaultSpecSteps` |
| `WireframeDemo/clamp_payload_window` | `verifyMirNoPanic_of_pureExec` + rules | body | — (companions impure) | — | — | companions: `defaultSpecSteps` |
| `WireframeDemo/parse_compression_flag` | `verifyMirNoPanic_of_pureExec` + rules | body | — (companions impure) | — | — | `requires`: `defaultSpecSteps` |
| `WireframeDemo/decode_wire_header` | `verifyMirNoPanic_of_blockLinear` | — | n/a | — | — | `defaultSpecSteps` |
| `WireframeDemo/advance_cursor` | `verifyStatefulMirNoPanic_of_cfg` | — | n/a | — | — (phase) | `defaultSpecSteps` |
| `WireframeDemo/checksum_frame_safe` | `verifyStatefulMirNoPanic_of_runCfgSteps` | — | n/a | — (unrolled) | — (phase) | `defaultCfgSteps` |
| `WireframeDemo/checksum_frame_fast` | `verifyStatefulEquivMir_of_runCfgSteps` | — | n/a | — | — (phase) | `defaultCfgSteps` |
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

"Budget" names the remaining bounded evaluation: `defaultSpecSteps body =
16 * #blocks + 80` and `defaultCfgSteps body = 16 * #blocks + 40` are derived
from the CFG size, and the `*FuelFree` wrappers in
`Anneal.Rustc.V2026_06_01.SymbolicEval` fix the budget inside `Anneal`. None
of these is a numeral in a proof file, but all of them are bounded evaluators;
only the `#mir_lift` rows are fuel-free (the rules synthesize the step count by
unification).

Known blockers for the remaining rows:

- The generated `__anodized_fn_requires_*` / `__anodized_fn_ensures_*`
  companions capture their arguments by reference through a closure
  (`_6 = &_1`, `copy (*_10).0`), so `checkPureMir` is `false` for all six of
  them and the pure `#mir_lift_spec` theorems
  (`mirBoolPredicateHolds_elim_of_pureExec` and friends) do not apply.
  Stepping them with memory-carrying `rfl` rules is impractical as is: the
  first `Rvalue.ref` step alone exceeds `400,000` heartbeats.
- `LiftLensBlock` (`Anneal.SepLogicLenses`) requires
  `body.phase = .runtimePostCleanup`, but every captured WireframeDemo body is
  `.runtimeOptimized`, so `mirWpConverges_of_sepLenses` cannot lift
  `advance_cursor` or the checksum bodies until that premise is generalized.
- `decode_wire_header`'s 13-statement entry block makes the `cons_eval` `rfl`
  double in cost per statement (`0.17 s → 8.3 s`) because the lifted locals
  form an unshared `List.set` tower; it needs a normalizing `cons_eval` variant.
- `checksum_frame_safe` still unrolls its `while i < 4` loop through
  `runCfgSteps` instead of `mirWpConverges_forRangeUp`.

## 3. Line counts

### 3.1 `examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo/*.lean`

`wc -l` at each revision. `a6bebfc2` is the last revision whose seven proofs
all compile; at `0d3242d3` three files were truncated to stubs that end after
their `wpReq_inversion` lemma, call the `mir_lift_spec` tactic that the
`Anneal` umbrella never imports, and define no `verified` theorem, so the
`0d3242d3` column understates the cost of a complete proof.

| Proof | `a6bebfc2` | `0d3242d3` | `[adv B1]` `a6aae5b8` | this revision | vs `a6bebfc2` |
| :--- | ---: | ---: | ---: | ---: | ---: |
| `advance_cursor.lean` | 227 | 227 | 171 | 149 | −34.4% |
| `checksum_frame_fast.lean` | 1,592 | 1,592 | 433 | 433 | −72.8% |
| `checksum_frame_safe.lean` | 1,242 | 1,242 | 196 | 196 | −84.2% |
| `clamp_payload_window.lean` | 1,595 | 33 (stub) | 330 | 315 | −80.3% |
| `decode_wire_header.lean` | 979 | 979 | 425 | 425 | −56.6% |
| `frame_total_len.lean` | 1,268 | 33 (stub) | 287 | 261 | −79.4% |
| `parse_compression_flag.lean` | 1,106 | 158 (stub) | 176 | 138 | −87.5% |
| **Total** | **8,009** | **4,264** | **2,018** | **1,917** | **−76.1%** |

Against `0d3242d3` the total falls by `55.0%` (`4,264 → 1,917`). Lines that
mention `BlockCtx`: `111` at `a6bebfc2` (28/26/26/23/8 in `checksum_frame_fast`,
`checksum_frame_safe`, `clamp_payload_window`, `frame_total_len`,
`parse_compression_flag`), `0` now.

### 3.2 Shared theory added by the migration (`0d3242d3 → this revision`)

| Module | `0d3242d3` | now | Δ | Contents |
| :--- | ---: | ---: | ---: | :--- |
| `theory/Anneal/MirLiftCore.lean` | 1,594 | 3,787 | +2,193 | fast evaluators, `wpBlockLinear`, `runCfgSteps`, `#mir_lift_spec` theorems moved from `MirSpecLift.lean` |
| `theory/Anneal/Rustc/V2026_06_01/SymReflect.lean` | 7,125 | 7,301 | +176 | `swap_le_u16_lane`, fixed-budget `*FuelFree` wrappers |
| `theory/Anneal/MirSpecLift.lean` | 139 | — | −139 | removed (never imported by `Anneal`, not in `DOWNSTREAM_TARGETS`) |
| `theory/Anneal/PureMirExec.lean` | 18,475 | 18,461 | −14 | `sup/ff-4` `18c85931` (`I-10`) plus unused-binder fixes |
| **Net** | | | **+2,216** | |

The WireframeDemo proofs shrink by `6,092` lines against `a6bebfc2`; about a
third of that moved into reusable theory.

### 3.3 Tutor and `MirVerification`

| File | `0d3242d3` | now | Change |
| :--- | ---: | ---: | :--- |
| `FrameTutor/*.lean` (6 files) | 309 | 300 | fuel arguments replaced by fixed-budget `*FuelFree` wrappers |
| `examples/mir/MirVerification.lean` | 1,986 | 2,042 | 6 pure examples lifted with explicit `#mir_lift` rules (+56: each lift spells out its rule loop) |

## 4. Elaboration cost

Wall-clock time of one sequential `lake env lean` per file (Section 6, step 5)
on `cpl-direct-electron-37838` with `anneal-lean-run --mode file
--concurrency 1`, after `cargo-anneal verify` has built the imports. Each file
sets `maxHeartbeats` itself; no file raises it above `800,000`.

| Proof | `maxHeartbeats` | Wall clock | Dominated by |
| :--- | ---: | ---: | :--- |
| `advance_cursor.lean` | 800,000 | 2.1 s | `verifyStatefulMirNoPanic_of_cfg` + `dsimp` |
| `checksum_frame_fast.lean` | 800,000 | 54.1 s | `runCfgSteps` unrolling of both bodies |
| `checksum_frame_safe.lean` | 400,000 | 33.1 s | `runCfgSteps` unrolling of the loop |
| `clamp_payload_window.lean` | 800,000 | 23.2 s | companion lemmas |
| `decode_wire_header.lean` | 800,000 | 18.8 s | `wpBlockLinear` evaluation |
| `frame_total_len.lean` | 800,000 | 32.0 s | companion lemmas |
| `parse_compression_flag.lean` | 800,000 | 10.8 s | `requires` companion lemma |

The `#mir_lift` part is cheap: with the companion lemmas replaced by `sorry`
in a scratch copy, the whole of `frame_total_len.lean`, including `import`
time, elaborates in `1.5 s` (`clamp_payload_window.lean`: `1.4 s`,
`parse_compression_flag.lean`: `3.2 s`). The companion lemmas, which still
evaluate the impure companions with `defaultSpecSteps`, account for the rest.

## 5. Changes relative to `[adv B1]` (`a6aae5b8`)

- `frame_total_len`, `clamp_payload_window`, `parse_compression_flag`: the
  subject bodies are now lifted with `verifyMirNoPanic_of_pureExec` and the
  `#mir_lift` rules instead of `verifyMirNoPanic_of_blockLinear` plus a
  hundred-symbol `dsimp only` list; the unused `ensures_holds_of_eq_*` helpers
  are gone.
- `MirVerification.lean`: six pure examples (footnote ¹ above) are lifted with
  the rules; `calleeAddOne_satisfies_contract` no longer supplies
  `⟨defaultCfgSteps …, by rfl⟩` as its convergence witness.
- `SymReflect.lean` is unchanged from `[adv B1]`. Its `*FuelFree` wrappers
  only fix the budget of a bounded combinator (`verifyByWPFuelFree c h :=
  verifyByWP c 16 h`), so they are documented here and in `SKILL.md`
  (Pattern E) as fixed-budget evaluators. Renaming them is blocked by the
  audit harness: any edit to `SymReflect.lean` invalidates
  `check_trusted.py --fast`'s cached `tests/mir/SymbolicEvalTests.lean`
  artifact, and recompiling that 2,000-line test suite took `2 m 10 s` under
  `anneal-lean-run --mode file` on this host, beyond the harness's fixed
  60-second per-compile limit (two `--fast` runs failed with `direct Lean child
  exceeded 60 seconds` on a renamed `SymReflect.lean`). The lifted proofs above
  do not use the wrappers; the tutor and the remaining `MirVerification`
  examples still do.
- `advance_cursor`: removed `frameCursorCodec`, `advanceCursorUpdate`, and
  `advanceCursorUpdate_preserves_invariant`, which `verified` never used.
- This report replaces the `[adv B1]` version, whose per-file line counts and
  `BlockCtx` counts did not match `wc -l` / `grep` at the cited revisions.

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
grep -n -E 'lift_PureMirConverges|LiftStmtsTerminator' $D/*.lean examples/mir/MirVerification.lean

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
(cd examples/wireframe-demo/.anneal && for f in ../anneal/proofs/Proof/WireframeDemo/*.lean; do
  /usr/bin/time -f "%e s $f" anneal-lean-run --mode file --concurrency 1 -- lake env lean "$f"
done)

# 7. Remove the untracked build artifacts before committing.
git status --porcelain   # `examples/*/.anneal/` and `examples/*/Cargo.lock`
