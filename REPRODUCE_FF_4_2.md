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
- No `BlockCtx`, no fuel numeral, and no step, statement, or tactic-round
  count (`iterate k`) in any migrated proof file (Section 6, step 3 greps for
  them). `defaultCfgSteps`
  and `runCfgSteps` are now zero across all seven `Proof/WireframeDemo/*.lean`
  files; the bounded evaluations that remain use `defaultSpecSteps` (on the
  three impure `#[spec]` companions) or the fixed-budget `*FuelFree` wrappers
  inside `Anneal` (Section 2).
- Proof LOC in `Proof/WireframeDemo/*.lean`: `8,009 → 1,421` (−82.3%)
  against the last complete proof corpus `a6bebfc2`, and `4,264 → 1,421`
  (−66.7%) against `0d3242d3` (whose `clamp_payload_window`,
  `frame_total_len`, and `parse_compression_flag` files are 33/33/158-line
  stubs without `verified`, see Section 3). The migration added `+2,972` net
  LOC of shared theory (Section 3.2).
- Measured elaboration heartbeats for the seven proofs fall from `1,388,934`
  to `665,228` thousand (−52.1%) against their `[adv B2]` versions
  (Section 4.2).

## 2. Which lifting API each proof uses

| Proof | Route | `#mir_lift` rules | `#mir_lift_spec` | `forRangeUp` | `SepLogicLenses` | Budget |
| :--- | :--- | :---: | :---: | :---: | :---: | :--- |
| `WireframeDemo/frame_total_len` | `verifyMirNoPanic_of_pureExec` + rules | body | — (companions impure) | — | — | companions: `defaultSpecSteps` |
| `WireframeDemo/clamp_payload_window` | `verifyMirNoPanic_of_pureExec` + rules | body | — (companions impure) | — | — | companions: `defaultSpecSteps` |
| `WireframeDemo/parse_compression_flag` | `verifyMirNoPanic_of_pureExec` + rules | body | — (companions impure) | — | — | `requires`: `defaultSpecSteps` |
| `WireframeDemo/decode_wire_header` | `verifyMirNoPanic_of_pureExec` + rules (`eval_rest`, `cons_eval_norm`) | body | n/a | — | — | none |
| `WireframeDemo/advance_cursor` | `verifyStatefulMir_of_sepLenses` + `LiftLensBlock` | — | n/a | — | yes | none |
| `WireframeDemo/checksum_frame_safe` | `verifyStatefulMirNoPanic_of_wpConverges` + `mirNoCallWpConverges_forRangeUp` + `runCfgToBlock` | — | n/a | yes | — | none |
| `WireframeDemo/checksum_frame_fast` | `verifyStatefulEquivMir_of_wpConverges` + `mirNoCallWpConverges_of_runCfgToBlock` + `safe_noCallWpConverges` | — | n/a | yes (spec) | — | none |
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
16 * #blocks + 80` is derived from the CFG size for impure companion
predicates, and the `*FuelFree` wrappers in
`Anneal.Rustc.V2026_06_01.SymbolicEval` fix the budget inside `Anneal`.
`decode_wire_header` (pure `#mir_lift` rules; `eval_rest` takes each block's
statement count from the block) and `advance_cursor`
(`verifyStatefulMir_of_sepLenses` + `LiftLensBlock`) have no step budget at
all. `checksum_frame_safe` proves its `while i < 4` loop with `forRangeUp` and
`mirNoCallWpConverges_forRangeUp` (lifted to `MirWpConverges` via
`MirWpConverges.of_noCall`); the entry segment, each iteration, and the exit
are discharged by `mirStepsConverges_of_runCfgToBlock` /
`mirNoCallWpConverges_of_runCfgToBlock`, which evaluate until the next entry
into the loop header `bb1` (or the return). `runCfgToBlock` checks `cfgAtBlock`
before every step and stops as soon as it reaches `target`, `.halted`, or
`.faulted`, so its internal recursion bound (`#blocks + 256`) is never reached
and no proof mentions `defaultCfgSteps` or a step count. `checksum_frame_fast`
discharges `verified` via `verifyStatefulEquivMir_of_wpConverges`: it steps
`checksum_frame_fast.body` to return with
`mirNoCallWpConverges_of_runCfgToBlock` and reuses `safe_noCallWpConverges`
from `Proof.WireframeDemo.checksum_frame_safe` for the reference specification
body instead of re-unrolling `checksum_frame_safe.body`.

Known blocker for the remaining companion rows:

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

| Proof | `a6bebfc2` | `0d3242d3` | `[adv B1]` `a6aae5b8` | `[adv A1]` `07b582eb` | `[adv B2]` `ecdf04bf` | `[adv A2]` `fbd40894` | `[adv B3]` `faf8961c` | `[adv A3]` `ceb78044` | `[adv B4]` `2f9ff834` | this revision | vs `a6bebfc2` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `advance_cursor.lean` | 227 | 227 | 171 | 149 | 258 | 231 | 231 | 231 | 231 | 231 | +1.8% |
| `checksum_frame_fast.lean` | 1,592 | 1,592 | 433 | 433 | 433 | 432 | 174 | 174 | 174 | 174 | −89.1% |
| `checksum_frame_safe.lean` | 1,242 | 1,242 | 196 | 196 | 569 | 250 | 275 | 275 | 275 | 275 | −77.9% |
| `clamp_payload_window.lean` | 1,595 | 33 (stub) | 330 | 315 | 315 | 315 | 315 | 270 | 185 | 187 | −88.3% |
| `decode_wire_header.lean` | 979 | 979 | 425 | 425 | 336 | 272 | 272 | 272 | 272 | 272 | −72.2% |
| `frame_total_len.lean` | 1,268 | 33 (stub) | 287 | 261 | 261 | 261 | 259 | 259 | 167 | 169 | −86.7% |
| `parse_compression_flag.lean` | 1,106 | 158 (stub) | 176 | 138 | 138 | 138 | 138 | 138 | 113 | 113 | −89.8% |
| **Total** | **8,009** | **4,264** | **2,018** | **1,917** | **2,310** | **1,899** | **1,664** | **1,619** | **1,417** | **1,421** | **−82.3%** |

Against `0d3242d3` the total falls by `66.7%` (`4,264 → 1,421`). Lines that
mention `BlockCtx`: `111` at `a6bebfc2` (28/26/26/23/8 in `checksum_frame_fast`,
`checksum_frame_safe`, `clamp_payload_window`, `frame_total_len`,
`parse_compression_flag`), `0` now. Lines that mention `defaultCfgSteps` or
`runCfgSteps`: `0` now across all seven files.

### 3.2 Shared theory added by the migration (`0d3242d3 → this revision`)

| Module | `0d3242d3` | now | Δ | Contents |
| :--- | ---: | ---: | ---: | :--- |
| `theory/Anneal/MirLiftCore.lean` | 1,594 | 4,480 | +2,886 | fast evaluators, `wpBlockLinear`, `runCfgSteps`, `eval_n`/`eval_rest`/`cons_eval_norm`, `cfgStepsWP`, `runCfgToBlock` and its `mirStepsConverges`/`mirNoCallWpConverges`/`mirWpConverges` theorems, `#mir_lift_spec` theorems moved from `MirSpecLift.lean` |
| `theory/Anneal/MirLoops.lean` | 651 | 692 | +41 | `mirNoCallWpConverges_forRangeUp` for fuel-free `verifyStatefulEquivMir_of_wpConverges` loop specs |
| `theory/Anneal/SepLogicLenses.lean` | 13,655 | 13,677 | +22 | generalized `LiftLensBlock` and `verifyStatefulMir_of_sepLenses` to `isRuntimeMirPhase body.phase = true` |
| `theory/Anneal/Rustc/V2026_06_01/SymReflect.lean` | 7,125 | 7,301 | +176 | `swap_le_u16_lane`, fixed-budget `*FuelFree` wrappers |
| `theory/Anneal/MirSpecLift.lean` | 139 | — | −139 | removed (never imported by `Anneal`, not in `DOWNSTREAM_TARGETS`) |
| `theory/Anneal/PureMirExec.lean` | 18,475 | 18,461 | −14 | `sup/ff-4` `18c85931` (`I-10`) plus unused-binder fixes |
| **Net** | | | **+2,972** | |

The WireframeDemo proofs shrink by `6,588` lines against `a6bebfc2`; less than
half of that (`2,972` lines, 45%) moved into reusable theory.

### 3.3 Tutor and `MirVerification`

| File | `0d3242d3` | now | Change |
| :--- | ---: | ---: | :--- |
| `FrameTutor/*.lean` (6 files) | 309 | 300 | fuel arguments replaced by fixed-budget `*FuelFree` wrappers |
| `examples/mir/MirVerification.lean` | 1,986 | 2,042 | 6 pure examples lifted with explicit `#mir_lift` rules (+56: each lift spells out its rule loop) |

## 4. Elaboration cost

### 4.1 Wall clock

Wall-clock time of one sequential `lake env lean` per file (Section 6, step 6)
on `cpl-direct-electron-37838` with `anneal-lean-run --mode file
--concurrency 1`, after `cargo-anneal verify` has built the imports. Each file
sets `maxHeartbeats` itself; no file raises it above `800,000`. The host ran
other Lean jobs during every measurement, so differences of a few seconds on
unchanged files are noise; Section 4.2 gives a load-independent measure.

| Proof | `maxHeartbeats` | `[adv B2]` | `[adv A2]` | `[adv B3]` | `[adv A3]` | `[adv B4]` | this revision | Dominated by |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| `advance_cursor.lean` | 400,000 | 2.5 s | 1.5 s | 1.5 s | 3.6 s | 1.6 s | 3.0 s | `verifyStatefulMir_of_sepLenses` + `LiftLensBlock` |
| `checksum_frame_fast.lean` | 800,000 | 56.6 s | 57.1 s | 15.2 s | 18.8 s | 15.7 s | 21.4 s | single `runCfgToBlock` of `checksum_frame_fast.body` (reuses `safe_noCallWpConverges`) |
| `checksum_frame_safe.lean` | 400,000 | 34.4 s | 13.5 s | 12.0 s | 12.5 s | 13.0 s | 11.8 s | four `runCfgToBlock` iterations (about 1.8 s of `dsimp` each) |
| `clamp_payload_window.lean` | 800,000 | 23.2 s | 27.1 s | 27.1 s | 22.2 s | 23.3 s | 22.2 s | companion lemmas |
| `decode_wire_header.lean` | 400,000 | 7.8 s | 4.1 s | 4.1 s | 3.9 s | 4.0 s | 3.7 s | `LiftStmtsTerminator.eval_rest` + `cons_eval_norm` |
| `frame_total_len.lean` | 800,000 | 32.6 s | 38.5 s | 32.5 s | 31.8 s | 33.7 s | 32.4 s | companion lemmas |
| `parse_compression_flag.lean` | 800,000 | 11.4 s | 12.3 s | 12.3 s | 11.5 s | 12.1 s | 11.1 s | `requires` companion lemma |

The `#mir_lift` part is cheap: with the companion lemmas replaced by `sorry`
in a scratch copy, the whole of `frame_total_len.lean`, including `import`
time, elaborates in `1.5 s` (`clamp_payload_window.lean`: `1.4 s`,
`parse_compression_flag.lean`: `3.2 s`), and `decode_wire_header.lean`
elaborates in `3.7 s` (`18.8 s` under `wpBlockLinear` at `[adv A1]`).

### 4.2 Heartbeats

Heartbeats spent elaborating each file's declarations, in thousands (the unit
of `maxHeartbeats`), read with `IO.getNumHeartbeats` before and after the file
body under `Elab.async false` (Section 6, step 7). Heartbeats count small
allocations, so unlike wall clock they do not depend on host load (repeated
runs give identical counts). Every earlier column elaborates that revision's
proof file against the current theory and generated modules. The `a6bebfc2`
proofs were written against that revision's theory and generated modules and
are not measured here.

| Proof | `[adv B2]` | `[adv A3]` | `[adv B4]` | this revision | vs `[adv B2]` |
| :--- | ---: | ---: | ---: | ---: | ---: |
| `advance_cursor.lean` | 5,771 | 5,414 | 5,414 | 5,504 | −4.6% |
| `checksum_frame_fast.lean` | 655,752 | 71,712 | 71,712 | 72,097 | −89.0% |
| `checksum_frame_safe.lean` | 180,914 | 64,596 | 64,596 | 64,596 | −64.3% |
| `clamp_payload_window.lean` | 187,030 | 186,984 | 187,584 | 186,993 | −0.0% |
| `decode_wire_header.lean` | 44,866 | 22,947 | 22,947 | 22,947 | −48.9% |
| `frame_total_len.lean` | 249,768 | 249,760 | 250,113 | 250,106 | +0.1% |
| `parse_compression_flag.lean` | 64,833 | 64,833 | 62,985 | 62,985 | −2.9% |
| **Total** | **1,388,934** | **666,246** | **665,351** | **665,228** | **−52.1%** |

## 5. Changes across passes (`[adv B1]` → `[adv A4]`)

- `advance_cursor`, `checksum_frame_fast`, `clamp_payload_window`,
  `frame_total_len` (`[adv A4]`): the proofs still fixed tactic round counts,
  which contradicted the "no step or statement count" claim in Section 1:
  `iterate 7` (the seven `StorageLive` statements of `advance_cursor`'s
  `bb0`), `iterate 2` (two `dsimp` rounds in `checksum_frame_fast`), and
  `iterate 4` (four companion-unfold rounds in both `wpReq_inversion` lemmas
  and in `clamp_payload_window.ensures_holds`). Each is now a count-free
  `repeat`, which stops when the script makes no more progress, and Section 6
  step 3 greps for `iterate [0-9]+`. The `wpReq_inversion` loops gained a
  comment on what each round does (`1,417 → 1,421` lines), and `SKILL.md`
  recommends `repeat` over `iterate k`.

- `clamp_payload_window`, `frame_total_len`, `parse_compression_flag`,
  `checksum_frame_safe` (`[adv B4]`):
  1. Collapsed the three copies of the ~30-line `dsimp only` unfold list in
     `wpReq_inversion` of `clamp_payload_window.lean` (`270 → 185` lines) and
     `frame_total_len.lean` (`259 → 167` lines) into a single `iterate 4
     (dsimp only [...]; first | ...)` block, and simplified `ensures_holds` in
     `frame_total_len.lean` with `simp (disch := omega)`.
  2. Replaced the four concrete `0`/`1` helper lemmas in
     `parse_compression_flag.lean` with a single `compressionFlagPost_bit`
     lemma and inlined `mirBoolPredicateHolds_of_evalMirSpecBool_true`
     (`138 → 113` lines, `64,833 → 62,985` thousand heartbeats).
  3. Updated two stale comments in `checksum_frame_safe.lean` from
     `mirWpConverges_forRangeUp` to `mirNoCallWpConverges_forRangeUp`, added
     the `iterate` companion-unfold tip to `SKILL.md` (Pattern B) and
     `references/proof-scaling-and-bottlenecks.md`, and tightened Section 6
     greps and `/tmp/hb_*` cleanup in `REPRODUCE_FF_4_2.md`.

- `clamp_payload_window` (`[adv A3]`): `ensures_holds` evaluated its two
  `ret` cases with two copies of a 31-line `dsimp only` list and
  case-specific `Nat.ble` / `Nat.beq` rewrites. One `all_goals` script now
  handles both cases and discharges the comparisons with
  `simp (disch := omega)` (`315 → 270` lines).
- `REPRODUCE_FF_4_2.md` and `SKILL.md` (`[adv A3]`): corrected two `[adv B3]`
  entries below (the `cfgAtBlock` change and the size of the
  `frame_total_len` edit) and the Pattern C reference to
  `checksum_frame_fast.lean`, and added measured heartbeats (Section 4.2,
  Section 6 step 7).

- `checksum_frame_fast`, `checksum_frame_safe`, `MirLiftCore`, `MirLoops`
  (`[adv B3]`):
  1. Changed `cfgAtBlock` in `theory/Anneal/MirLiftCore.lean` to also return
     `true` on `.halted _ _` and `.faulted`, so `runCfgUntilAux` stops at a
     return or fault instead of stepping the absorbing state through the rest
     of its recursion bound, and replaced `defaultCfgSteps body` in
     `runCfgToBlock` with `Nat.add (length body.basicBlocks) 256` so callers
     never include `defaultCfgSteps` in `dsimp only`.
  2. Added `mirNoCallWpConverges_forRangeUp` to `theory/Anneal/MirLoops.lean`
     and `mirNoCallWpConverges_of_cfgStateWP` /
     `mirNoCallWpConverges_of_runCfgToBlock` to
     `theory/Anneal/MirLiftCore.lean`.
  3. Exported `safe_noCallWpConverges` and `frame8_post_holds` from
     `Proof/WireframeDemo/checksum_frame_safe.lean` (`12.0 s`, `275` lines) and
     migrated `Proof/WireframeDemo/checksum_frame_fast.lean` off
     `verifyStatefulEquivMir_of_runCfgSteps` (`57.1 s`, `432` lines) onto
     `verifyStatefulEquivMir_of_wpConverges` +
     `mirNoCallWpConverges_of_runCfgToBlock` + `safe_noCallWpConverges`
     (`15.2 s`, `174` lines), eliminating the duplicate 4-iteration unrolling of
     `checksum_frame_safe.body` and reducing `defaultCfgSteps` / `runCfgSteps`
     occurrences across `Proof/WireframeDemo/*.lean` to `0`.
  4. Removed a duplicated two-line group from a `dsimp only` list in
     `Proof/WireframeDemo/frame_total_len.lean` (`261 → 259` lines).

- `checksum_frame_safe` (`[adv A2]`): the `[adv B2]` loop proof passed exact
  step counts (`29` for the entry, `36` per iteration, `5` for the exit) to
  `mirStepsConverges_of_cfgStepsWP` and `mirWpConverges_of_runCfgSteps_none`,
  which are manual fuel constants. `theory/Anneal/MirLiftCore.lean` now
  provides `runCfgToBlock`, which evaluates until the next entry into a target
  block, a halt, or a fault, with `mirStepsConverges_of_runCfgToBlock` and
  `mirWpConverges_of_runCfgToBlock`. It checks for the target before every
  step, so `dsimp` never evaluates past it. The proof keeps the accumulator
  symbolic, so one `all_goals` script handles all four iterations instead of
  four copies of a 50-line `dsimp only` list, and the structural
  `checksumPrefix` with its bound `checksumPrefix_le` lets `omega` discharge
  every overflow check (`569 → 250` lines; Section 4 for time).
- `decode_wire_header` (`[adv A2]`): `[adv B2]` stated its three lifting lemmas
  as `LiftBlock … 30`, `… 26`, and `… 20` and evaluated blocks with
  `eval_n (n := 13)`, `(n := 2)`, and `(n := 1)`, which are manual budgets.
  The lemmas now conclude `PureMirConverges` and begin with
  `apply lift_PureMirConverges (by rfl)`, so the fuel is inferred, and the new
  `LiftStmtsTerminator.eval_rest` takes each block's statement count from the
  block. The generic `evalPureStmtNorm_assign_local_of_evalRvalue` moved to
  `MirLiftCore`, the two `decode_wireHeader_{0,1}` lemmas merged, and the
  duplicated `b1 = 0` / `b1 = 1` alternatives collapsed (`336 → 272` lines).
- `advance_cursor` (`[adv A2]`): the private `forceEnv` normalizer duplicated
  `forcePureEnv?` (`PureEnv` is `List LocalSlot`); the proof now uses
  `forcePureEnv?` and the new `set?_of_forcePureEnv?` (`258 → 231` lines).
- `checksum_frame_fast` (`[adv A2]`): dropped the `mul_12_16` and `mul_20_16`
  helpers, which `dsimp` does not need to compute `defaultCfgSteps`.
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
  `verifyMirNoPanic_of_pureExec` + `#mir_lift` rules (`7.8 s`, `336` lines).
- `checksum_frame_safe` (`[adv B2]`): added `cfgStepsWP`,
  `wpMirExecStepsSym_of_runCfgSteps`, `mirStepsConverges_of_cfgStepsWP`,
  `mirStepsConverges_of_cfgStepsWP_none`, `mirWpConverges_of_cfgStateWP`, and
  `mirWpConverges_of_runCfgSteps_none` to `theory/Anneal/MirLiftCore.lean` and
  moved `Proof/WireframeDemo/checksum_frame_safe.lean` from whole-loop
  `verifyStatefulMirNoPanic_of_runCfgSteps` unrolling onto `forRangeUp`,
  `checksumLoopInv`, `mirWpConverges_forRangeUp`, and
  `verifyStatefulMirNoPanic_of_wpConverges`, with exact step counts per
  segment (replaced in `[adv A2]`).
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

# 2. No soundness escapes. Expected hits only: the English word "admit" in a
#    `theory/Anneal/PureMirExec.lean` comment (present at `0d3242d3`), and the
#    pre-existing `Assumptions.FrameTutor.pin_magic` axiom of the tutor-ch3
#    lesson on conditional verification, which FF-4.2 does not touch.
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
grep -c -E 'defaultCfgSteps|runCfgSteps' $D/*.lean
grep -c defaultSpecSteps $D/*.lean
#    No fuel numeral, step, statement, or round count (expect no output):
grep -nE 'LiftBlock .* [0-9]+ :=|^\s*[0-9]+ := by|\(n := [0-9]+\)|\brfl [0-9]+\b|iterate [0-9]+' $D/*.lean
grep -n -E 'lift_PureMirConverges|LiftStmtsTerminator|verifyStatefulMir_of_sepLenses|mir(NoCall)?WpConverges_forRangeUp|runCfgToBlock' $D/*.lean examples/mir/MirVerification.lean

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

# 7. Heartbeats per file (Section 4.2): elaborate a /tmp copy that prints
#    IO.getNumHeartbeats before and after the file body, synchronously.
(cd examples/wireframe-demo/.anneal && for f in ../anneal/proofs/Proof/WireframeDemo/*.lean; do
  p=/tmp/hb_$(basename "$f")
  { sed -n '/^import /p' "$f"
    echo 'set_option Elab.async false'
    echo '#eval show IO Unit from do IO.println s!"HB {← IO.getNumHeartbeats}"'
    sed '/^import /d' "$f"
    echo '#eval show IO Unit from do IO.println s!"HB {← IO.getNumHeartbeats}"'
  } > "$p"
  echo "$f: $(anneal-lean-run --mode file --concurrency 1 -- lake env lean "$p" |
    awk '/^HB /{v[n++]=$2} END{print int((v[1]-v[0])/1000)}') thousand heartbeats"
  rm -f "$p"
done)

# 8. Remove the untracked build artifacts before committing.
git status --porcelain   # `examples/*/.anneal/` and `examples/*/Cargo.lock`
