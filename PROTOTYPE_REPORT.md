# Track P Prototype Report: `ws-proto-fuel-free-loop-lifting-and-typed-at-lenses` (`ep1`)

Prototype-only deliverable (Track P, `merge_policy = "no_merge_prototype"`) for the
`PROPOSED_HOLD` Track A workstream `ws-fuel-free-loop-lifting-and-typed-at-lenses`.
Everything here is validated directly against the live signatures of `Anneal.PureMirExec`,
`Anneal.MirLiftCore`, `Anneal.MirFuelFree`, `Anneal.MirLoops`, `Anneal.SepLogicLenses`, and
`Anneal.ByteCodec` (the prototype module imports them; it is not imported by `Anneal.lean`).

**Decision: CONDITIONAL GO**

Proceed with `ws-fuel-free-loop-lifting-and-typed-at-lenses` under the conditions in
[Section 7](#7-decision-rationale-and-conditions): adopt fuel-free range-loop lifting (constant
cost in the trip count: the only family with an *asymptotic* win over `simp`), `TypedAt` field
lenses (linear like byte-list `simp`, with 1.9–3.1× fewer heartbeats), and step-wise single-pass
`setSpine?` / `setPureEnvSlot?` normalization (linear like `List.set` `simp` with 1.14–1.16× fewer
heartbeats, and 2.1–2.6× fewer than the two-pass normalization that the live `evalPureStmtNorm`
performs today, which is itself 1.8–2.2× costlier than `simp`; plain `rfl` and end-of-chain projection
time out from `K = 20`), and apply `forcePureEnv` step-wise rather than as an end-of-chain projection
over an unforced `List.set` tower.

## 1. Deliverables

| File | Contents |
|---|---|
| `theory/Anneal/FuelFreeLoopAndTypedAtLensPrototype.lean` | 306 kernel-checked theorems (0 `sorry`, 0 warnings), each audited by a `#guard_msgs in #print axioms` block (`propext` / `Quot.sound` only) |
| `scripts/bench_fuel_free_lens_scaling_proto.py` | Benchmark harness (`--dry-run`, `--verify-report`, `--update-report`) |
| `scripts/test_bench_fuel_free_lens_scaling_proto.py` | Unit, negative/edge-case, proof-health, axiom-guard, hygiene, isolation, and report-consistency tests |
| `PROTOTYPE_REPORT.md` | This report (tables + embedded JSON receipt are generated and machine-verified) |

## 2. Results by pillar

### Pillar 1 — fuel-free `runCfgToBlock` loop lifting (Sections 1–6)

* **Kleene fuel order and fuel-free convergence.** `evalFuel` (structural on fuel) over a
  deterministic `Step` (`cont` / `done` / `fault`); `evalFuel_mono`, `evalFuel_halted_mono`,
  `evalFuel_faulted_mono`, `evalFuel_halted_deterministic`, and `evalFuel_faulted_ne_halted`
  (a fault under some fuel excludes halting under every fuel). `WpConverges` with
  `WpConverges.of_done/of_cont/mono/deterministic`, `not_wpConverges_of_faulted`, and the
  segment calculus `StepsTo` with `StepsTo.bind_wp`, `StepsTo.trans`, `StepsTo.mono`.
* **Header-targeted stepping.** `TargetOutcome` has four distinct constructors
  (`reached`, `halted`, `stuck`, `outOfFuel`). `runToTarget` takes one mandatory step and then
  searches for the next target state; `runCfgToBlock` derives its ceiling from the CFG
  (`cfg.length`), so call sites contain no step numerals. Soundness:
  `stepsTo_of_runCfgToBlock_reached`, `wpConverges_of_runCfgToBlock_halted`,
  `not_wpConverges_of_runCfgToBlock_stuck`; ceiling monotonicity `runToTarget_mono_bound`.
  **No overshoot** is characterized exactly: `firstHitIn_of_runToTarget_reached` (a `.reached`
  state is the first target re-entry), `FirstHitIn.unique` (that re-entry is unique), and
  `runToTarget_of_firstHitIn` (completeness for every sufficient ceiling). Concrete witnesses:
  `runCfgToBlock_selfLoop_no_overshoot` (a self-looping header stops after exactly one
  iteration), `runCfgToBlock_countUp_iter` (re-entrant multi-block header),
  `runCfgToBlock_stuck_example`, `runToTarget_outOfFuel_vs_reached` (out-of-fuel is
  inconclusive and ceiling-sensitive, never a fault or a halt), and the non-terminating loop
  `infiniteLoopCfg` (`evalFuel_infiniteLoop_outOfFuel`, `not_wpConverges_infiniteLoop`,
  `runToTarget_infiniteLoop_outOfFuel`).
* **`[lo, hi)` loops.** Structural `forRangeUp` with `forRangeUp_induction` and the fuel-free loop
  rule `wpConverges_forRangeUp`; **bridge** `forRangeUp_eq_live` proves it equal to the live
  well-founded `Anneal.MirLoops.forRangeUp` (and `live_forRangeUp_induction` transports
  induction to it).
* **`countUp(n)`.** A five-block CFG with a symbolic accumulator and a back-edge into its loop
  header. `evalFuel_countUp_header` characterizes the exact fuel (`3 (n - i) + 2` from the
  header); `no_uniform_fuel_countUp` proves no constant `F` halts it for every `n`;
  `countUp_wpConverges_all_n` proves total correctness for every symbolic `n` (and accumulator)
  with no fuel numeral in the statement; `selfLoop_wpConverges_all_n` does the same for the
  self-loop.
* **Live bridges.** `mirStep` embeds the trusted `stepMirFn` across both silent `.tau` steps and
  all `MirObsE` observation steps (`.vis (.inr (.inl (.emit _)))`, matching live
  `Anneal.FunctionalTranslation.runMirToBlock`), while root returns halt and external calls/faults
  map conservatively to `.fault`; `mirStepsConverges_of_stepsTo` and
  `mirWpConverges_of_wpConverges` transport generic proofs to the live
  `Anneal.MirFuelFree.MirStepsConverges` / `MirWpConverges`; `mirWpConverges_of_stepsTo_bind`,
  `runMirToBlock` (+ soundness), and `mirWpConverges_forRangeUp` (stated with the live
  `Anneal.MirLoops.forRangeUp`) complete the live API and are exercised end-to-end on the live
  `CapturedMir` loop `Anneal.MirLoops.countToNBody n` (`runMirToBlock_countToN_entry`,
  `runMirToBlock_countToN_iter`, `runMirToBlock_countToN_exit`, and
  `live_countToN_mirWpConverges_all_n`). Direct bridges to the existing live
  `Anneal.FunctionalTranslation.runMirToBlock` (`live_runMirToBlock_stationary_at_target`,
  `runUntilTarget_reached_iff_live_runMirToBlock`, `runMirToBlock_reached_iff_step_and_live`) prove
  why the live stepper is stationary at loop headers (`stmtIdx = 0`) and that the prototype's
  `runMirToBlock` equals one mandatory `mirStep` followed by the live stepper.
  `inferMinFragment_toMirShape` proves, for *every* toy CFG, that the live classifier assigns its
  shape `.pureBoundedLoop` iff it has a back-edge and `.pureLoopFree` otherwise (via
  `hasCfgBackedge_toMirShape`); `inferMinFragment_refShape` shows a local `&mut` borrow lifts a
  shape to `.treeBorrowsLocal`.

### Pillar 2 — `forcePureEnv` slot-list normalization (Section 7)

`forcePureEnv n env` projects the `n`-slot prefix (padding with `default`) by single-pass pattern
matching on `env`; proven: `forcePureEnv_eq_self`, `forcePureEnvD_eq_take_append_replicate`,
`forcePureEnv_ne_self_of_length_ne`, `forcePureEnv_eq_self_iff` (exact length-mismatch
characterization), `getElem?_forcePureEnv`, `length_forcePureEnvD`, `forcePureEnv_set_comm`
(with the necessary side condition; `forcePureEnv_set_comm_counterexample` shows it cannot be
dropped), and `chained_sets_collapse_rfl` (nested symbolic `List.set` updates collapse to a flat
literal by `rfl`, no commutation lemmas). The step-wise form `applySlotUpdatesForced` re-forces the
modified prefix after every update with `setSpine?` (proven equal to `forceSpine? (env.set i v)` via
`setSpine?_eq_forceSpine?_set`, and to the `forcePureEnv` normal form of the update via
`setSpine?_eq_some_forcePureEnv_set`); `applySlotUpdatesForced_eq_forcePureEnv` shows the whole
forced run computes exactly `forcePureEnv` of the unnormalized `List.set` chain, and
`applySlotUpdates_eq_of_forced` makes a single `rfl` prove the whole update sequence
(`slotUpdates_collapse_forced`: 12 updates). Live bridges: `forceSpine?_eq_live` (agrees with
`Anneal.MirLiftCore.forcePureEnv?` on every `PureEnv`), `evalPureStmtNorm_eq_bind_forceSpine?`
(bridges the live `Anneal.MirLiftCore.evalPureStmtNorm` to `evalPureStmt` and `forceSpine?`),
`setPureEnvSlot?` (`setPureEnvSlot?_eq_set?`, `setPureEnvSlot?_eq_live_bind_forcePureEnv?`: a
single-pass `LocalSlot`-constructor-forcing replacement for the two-pass
`(set? env loc s).bind forcePureEnv?` in `Anneal.MirLiftCore.set?_of_forcePureEnv?`),
`forcePureEnvSlots_eq_self`, `forcePureEnvSlots_set?`, `liveSet?_eq_setSpine?`, and
`applySlotUpdatesLive?_eq_forced` / `applySlotUpdatesLive?_oob`. The live normalization itself is
reproduced by `applySlotUpdatesTwoPass` (bounds-checked `Trusted.Sequence.set?` followed by a full
`forceSpine?` pass after every update, i.e. the structure of `evalPureStmtNorm`;
`applySlotUpdatesTwoPass_eq_live?`, soundness `applySlotUpdates_eq_of_twoPass`) and benchmarked as
`live_two_pass_rfl`, so the Track A recommendation compares against what the live code does today.

### Pillar 3 — relational `TypedAt` / `DisjointSlice` lenses (Section 8)

Memory is a list of trusted `AbstractByte`s; reads and writes are the *trusted*
`sliceAbstractBytes` / `writeAbstractBytesAt` (closed forms `sliceAbstractBytes_eq`,
`writeAbstractBytesAt_eq_splice`, `writeAbstractBytesAt_eq_none`, `writeAbstractBytesAt_some_inv`).
`TypedAt c base v mem` is relational (`readTyped` decodes the window to `v`), so padding may hold
arbitrary bytes. Proven: `TypedAt.read_write_same`, `TypedAt.frame_write` and
`TypedAt.frame_writeBytes` (frame rules that never unfold codecs or byte lists),
`writeTyped_eq_none_of_oob` / `writeTyped_isSome_iff` / `not_typedAt_of_oob` (out-of-bounds),
`writeTyped_zero_width` / `typedAt_zero_width_iff` / `zeroWidth_write_read_asymmetry` (`n = 0`),
`DisjointSlice.adjacent` / `TypedAt.frame_write_adjacent` (`base₁ + len₁ = base₂`),
`typedAt_append_encode` (bridge to the live `sliceAbstractBytes_append_encode`), and for the padded
codec `laidOutPair` (live `prod` + `padRight`): `typedAt_laidOutPair_iff`,
`typedAt_laidOutPair_write_fst`, `typedAt_laidOutPair_write_snd`,
`typedAt_laidOutPair_padding_write` (arbitrary padding writes preserve the struct),
`laidOutPair_encode_eq`, `typedAt_laidOutPair_init_padding` (an initialized padding byte is still
typed), `typedAt_of_canonicalAt`, `typedAt_laidOutPair_of_fieldsValid`, and
`typedAt_laidOutPair_applyFieldWrites` (connecting `applyFieldWrites` to whole-struct `TypedAt`
across arbitrary padding bytes). `subplaceFieldLens_disjoint` builds live
`Anneal.FunctionalTranslation.LawfulMutLens` witnesses for both field lenses and a live
`Anneal.SepLogicLenses.IndependentLenses` witness; `subplaceFieldLens_of_borrowSubplace_disjointOn`
bridges live `Anneal.SepLogicLenses.BorrowSubplace.disjointOn` directly to `DisjointSlice`,
`LawfulMutLens`, and `IndependentLenses` (its hypotheses are jointly satisfiable:
`subplaceFieldLens_of_borrowSubplace_disjointOn_nonvacuous`); `structLens_lawful` reuses the live
`prodMutLens_lawful`; `applyFieldWrites_spec` discharges `K` sequential field writes with one lens
law per write.

### Pillar 4 — pre-release `reborrowFootprint` protector specs (Section 9)

Tree Borrows permissions `ReservedFrz`, `ReservedIM`, `Active`, `Frozen`, `Disabled` (embedded
injectively into the live `Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm`:
`ofLiveTreeBorrowPerm?_toLiveTreeBorrowPerm` / `toLiveTreeBorrowPerm_ofLiveTreeBorrowPerm?`) with the
per-location automaton `performTransition`, which is proven **equal to the live trusted automaton**:
on accessed locations (the live model's invariant) `performTransition_accessed_eq_live` shows it
coincides with `Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowNodeAccess` (Miri's per-permission
transition, the `ProtectedDisabled` check, and the foreign-access skip of `Disabled` nodes) for every
access kind, relatedness, protector bit, and permission, and `performTransition_accessed_isSome_eq_live`
matches its UB detection with `treeBorrowTransitionIsUB`; on unaccessed locations
`performTransition_unaccessed_eq_live` shows it is `treeBorrowPermTransition` without the protector
check (Miri's `accessed` guard, which the live model does not represent); `isTagProtected_eq_live` and
`performTransition_entry_eq_live` lift this to live `BorrowEntry` protectors (`isBorrowProtected`),
`nodeAccessRelatedness_visit_eq_live_writer` and `borrowEntryWriteConflicts_eq_live` bridge the live
`parentTag` hierarchy (`isBorrowDescendantOrSelf`, `resolveTreeBorrowWriterTag`,
`treeBorrowWriterRelatedness`, `borrowEntryWriteConflicts`), `restoreCallerProtectors_eq_live`
bridges the live return-path protector pop (`restoreCallerProtectors`), and
`liveBorrowEntryRange_contains_iff` projects entry ranges. On top of it: a well-formed arbitrary-depth
`BorrowTree`, the active
call-id set, two-stage release (`applyReleaseProtector` with `ChildrenVisitMode.skipChildrenOfAccessed`
while the call id is active, then `removeActiveProtector` = `GlobalState.endCall`), and
`TrustedFnSpec` whose `reborrowFootprint : List (ByteRange × Mutability)` (live
`Trusted.Rustc.V2026_06_01.MirAst.Mutability`) is applied before release. Proven:

* `reborrow_return_unique_write_perm`, `reborrow_return_after_callee_write_unique_write_perm`
  (callee writes through child `t_ret` before return),
  `reborrow_return_after_parent_write_unique_write_perm` (callee writes through parent `t_arg`
  before reborrowing `t_ret`), and the negative dual
  `callee_parent_write_after_reborrow_disables_child` (callee writing through parent `t_arg` on
  `subRange` *after* reborrowing `t_ret` disables `t_ret`);
* `split_at_mut_unique_write_perm` for every `mid ≤ len`: release is UB-free, both halves are
  uniquely writable, writing either half preserves the other's permission, after both writes the
  halves are `Active` on disjoint footprints, and a cross-half write through the left slice is UB;
  `split_at_mut_mid_zero` / `split_at_mut_mid_len` cover the boundaries and
  `split_at_mut_rootTree_nonvacuous` shows all hypotheses are satisfiable;
* `split_at_mut_stage2Only_unique_write_perm` and `stage1_vs_stage2Only_two_arg_release_differs`:
  under the live stage-2-only return path (`TrustedFnSpec.runStage2Only`), `split_at_mut` still
  retains `HasUniqueWritePerm` on both halves and rejects cross-half writes, whereas on a UB-free
  two-argument call receiving two-phase `&mut` borrows (`t_arg_x`, `t_arg_y`), Miri's stage-1
  `applyReleaseProtector` marks `t_arg_y` conflicted (`ReservedFrz true`) while stage-2-only release
  leaves `t_arg_y` unconflicted (`ReservedFrz false`). That difference is **unobservable**
  (`stage1_vs_stage2Only_two_arg_release_unobservable`, `stage1_vs_stage2Only_two_arg_release_same_verdicts`):
  after the full stage-1 release and `GlobalState.endCall` the two trees are `LatchEquiv` (they differ
  only in conflict latches of unprotected tags, which never influence a transition:
  `performTransition_unprotected_eraseLatch`), a relation preserved by every tree operation
  (`LatchEquiv.access`, `LatchEquiv.retag`, `LatchEquiv.release`, `LatchEquiv.of_active`) under which
  every access and release has the same UB verdict (`LatchEquiv.noUB_iff`,
  `LatchEquiv.releaseNoUB_iff`); `applyReleaseProtector_read_eraseLatch` is the general lemma that a
  protector-end read only flips conflict latches;
* `trustedSpec_reborrow_equivalence`: for `split_at_mut` and `get_mut` the concrete UB-checked
  callee semantics (`ConcreteCall`: entry retag, `CalleeRun` over `assertLe` / `rawPtr` /
  `reborrow`, return registers, UB-checked release) succeeds with exactly the spec's outcome
  (progress) and every concrete outcome equals it (determinism), so concrete calls inherit the
  spec's `HasUniqueWritePerm` postconditions; `concreteSplitAtMut_requires_mid_le` shows the body
  panics otherwise;
* `same_tag_split_unsound_control`, `overlapping_reborrowFootprint_write_disables_sibling`, and
  `shared_reborrowFootprint_read_ok_write_ub`: `TrustedFnSpec.runNoFootprint` returns both slices
  with the argument tag (allowing UB-free cross-slice aliasing writes), `TrustedFnSpec.run` with
  overlapping `&mut` footprints disables the sibling reference upon writing the overlap byte, and
  `TrustedFnSpec.run` with overlapping shared (`Mutability.not`) footprints keeps both references
  `Frozen` across reads while rejecting writes through either.

## 3. Receipts (latest pass: A2)

```bash
anneal-lean-run --mode file --concurrency 1 -- lake env lean theory/Anneal/FuelFreeLoopAndTypedAtLensPrototype.lean
python3 -B -m unittest scripts/test_bench_fuel_free_lens_scaling_proto.py -v
python3 scripts/bench_fuel_free_lens_scaling_proto.py --dry-run
python3 scripts/bench_fuel_free_lens_scaling_proto.py --verify-report
git diff --name-only 2167b83c9bf782c337d7cec99d54249c52f865c9..HEAD
git status --porcelain
```

All six pass at A2: the Lean file elaborates with no output (0 errors, 0 warnings, 306 axiom guards
passing), the unit suite passes (including the report drift checks
`test_report_theorem_counts_match_source` and `test_report_names_resolve`), `--dry-run` validates
all generated benchmark files in milliseconds, `--verify-report` matches the embedded receipt (whose
`prototype_sha256` pins the exact Lean source measured), the diff contains exactly the four Track P
files, and the tree is clean.

## 4. Benchmark methodology

* **Equivalent obligations.** For each family and `K` the harness builds one statement; the
  variants differ only in the proof term (`validate_generated` and the unit tests assert textual
  statement identity). All statements quantify over symbolic inputs (`Nat` / `UInt8` binders), so
  nothing folds to a closed ground constant.
* **Families.** `local_slots`: `K` updates of an 8-slot frame (`applySlotUpdates`). `struct_fields`:
  `K` writes to the two `u8` fields of a padded struct over trusted bytes (`applyFieldWrites`).
  `loop_trip`: `countUp(K)` total correctness with symbolic accumulator.
* **Variants.** naive `rfl` (elaborator `Meta.whnf` with default smart unfolding) and naive `simp`
  (`List.set` rewriting; byte-list unfolding through the trusted primitives; explicit fuel
  `3 K + 3` evaluated by `simp`) versus the prototype strategy (step-wise `forcePureEnv` forcing;
  `TypedAt` lens laws via `applyFieldWrites_spec`; `runCfgToBlock` + `forRangeUp_induction`, re-proved
  inline per instance so its cost is visible). `local_slots` also carries the ablation
  `ablation_projection_rfl`: the end-of-chain `forcePureEnv` projection (`eq_of_forcePureEnv`)
  checked by `rfl`, isolating whether projection alone avoids the blow-up, and the live baseline
  `live_two_pass_rfl`: the two-pass normalization of the live `evalPureStmtNorm` (bounds-checked
  `Trusted.Sequence.set?`, then a full `forceSpine?` pass after every update;
  `applySlotUpdates_eq_of_twoPass`) checked by `rfl`.
* **Measurement.** The prototype is compiled once into a temporary directory as module
  `FuelFreeProtoBench.Prototype` from the byte-identical source (its SHA-256 is recorded). Each
  (family, variant) file runs through `anneal-lean-run --mode file --concurrency 1 -- lake env lean`,
  starts with a discarded warm-up instance, and wraps every instance in a `#measure` command that
  logs elaboration wall-clock and thread-local heartbeats (`Elab.async false`, which also makes
  `addDecl` run the kernel check synchronously inside the measured window: for `live_two_pass_rfl`
  at K = 30, `debug.skipKernelTC` removes about 160 ms and 181 k heartbeats). A global warm-up run
  is discarded, file order rotates across repetitions, and variant order alternates.
  `maxHeartbeats 200000` turns blow-ups into deterministic timeouts; larger `K` of a timed-out
  variant are recorded as `skipped (censored)`.

## 5. Benchmark results

<!-- BENCH:BEGIN -->

Cells: median elaboration wall-clock / median elaboration kilo-heartbeats (`#measure`, `Elab.async false`), over 3 interleaved repetitions after a discarded warm-up; budget `maxHeartbeats 200000`.

#### `local_slots`

| variant | K = 5 | K = 10 | K = 20 | K = 30 |
|---|---|---|---|---|
| `naive_rfl` | 19 ms / 145 k | 116 ms / 1105 k | timeout (> 200 M hb) | skipped (censored) |
| `naive_simp` | 27 ms / 156 k | 41 ms / 245 k | 72 ms / 423 k | 118 ms / 609 k |
| `ablation_projection_rfl` | 41 ms / 249 k | 256 ms / 2140 k | timeout (> 200 M hb) | skipped (censored) |
| `live_two_pass_rfl` | 42 ms / 287 k | 72 ms / 498 k | 164 ms / 917 k | 217 ms / 1359 k |
| `optimized_forcePureEnv` | 18 ms / 137 k | 29 ms / 214 k | 53 ms / 366 k | 69 ms / 525 k |

#### `struct_fields`

| variant | K = 5 | K = 10 | K = 20 | K = 30 |
|---|---|---|---|---|
| `naive_rfl` | 93 ms / 848 k | 2917 ms / 21109 k | timeout (> 200 M hb) | skipped (censored) |
| `naive_simp` | 62 ms / 409 k | 82 ms / 507 k | 104 ms / 695 k | 127 ms / 889 k |
| `optimized_typedAt_lens` | 17 ms / 133 k | 24 ms / 201 k | 38 ms / 338 k | 59 ms / 475 k |

#### `loop_trip`

| variant | K = 5 | K = 10 | K = 20 | K = 30 |
|---|---|---|---|---|
| `naive_fuel_rfl` | 5403 ms / 56665 k | timeout (> 200 M hb) | skipped (censored) | skipped (censored) |
| `naive_fuel_simp` | 428 ms / 1979 k | 822 ms / 4308 k | 2803 ms / 11172 k | 5791 ms / 21063 k |
| `optimized_runCfgToBlock_forRangeUp` | 35 ms / 158 k | 27 ms / 158 k | 30 ms / 158 k | 32 ms / 158 k |

<details><summary>Embedded JSON receipt (verified by <code>--verify-report</code>)</summary>

```json
{
 "cpu_count": 8,
 "file_wall_ms_median": {
  "local_slots/ablation_projection_rfl": 25156,
  "local_slots/live_two_pass_rfl": 4089,
  "local_slots/naive_rfl": 24852,
  "local_slots/naive_simp": 3637,
  "local_slots/optimized_forcePureEnv": 3690,
  "loop_trip/naive_fuel_rfl": 34908,
  "loop_trip/naive_fuel_simp": 13212,
  "loop_trip/optimized_runCfgToBlock_forRangeUp": 3374,
  "struct_fields/naive_rfl": 33996,
  "struct_fields/naive_simp": 3678,
  "struct_fields/optimized_typedAt_lens": 3075
 },
 "generated_at_utc": "2026-11-13T19:13:30Z",
 "heartbeat_budget": 200000,
 "ks": [
  5,
  10,
  20,
  30
 ],
 "lean_toolchain": "leanprover/lean4:v4.34.1",
 "prototype": "theory/Anneal/FuelFreeLoopAndTypedAtLensPrototype.lean",
 "prototype_compile_ms": 11503,
 "prototype_sha256": "7edfcf744f8f4973d640cbd48830d5a0ccff78068b5e61a0861ed4102ca4a610",
 "repetitions": 3,
 "results": [
  {
   "family": "local_slots",
   "hb_samples": [
    144625,
    144625,
    144625
   ],
   "k": 5,
   "kilo_heartbeats": 145,
   "median_ms": 19,
   "ms_samples": [
    14,
    42,
    19
   ],
   "status": "ok",
   "variant": "naive_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    1104570,
    1104570,
    1104570
   ],
   "k": 10,
   "kilo_heartbeats": 1105,
   "median_ms": 116,
   "ms_samples": [
    109,
    218,
    116
   ],
   "status": "ok",
   "variant": "naive_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [],
   "k": 20,
   "kilo_heartbeats": null,
   "median_ms": null,
   "ms_samples": [],
   "status": "timeout",
   "variant": "naive_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [],
   "k": 30,
   "kilo_heartbeats": null,
   "median_ms": null,
   "ms_samples": [],
   "status": "skipped",
   "variant": "naive_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    155939,
    155939,
    155939
   ],
   "k": 5,
   "kilo_heartbeats": 156,
   "median_ms": 27,
   "ms_samples": [
    20,
    42,
    27
   ],
   "status": "ok",
   "variant": "naive_simp"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    244870,
    244870,
    244870
   ],
   "k": 10,
   "kilo_heartbeats": 245,
   "median_ms": 41,
   "ms_samples": [
    32,
    74,
    41
   ],
   "status": "ok",
   "variant": "naive_simp"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    422880,
    422880,
    422880
   ],
   "k": 20,
   "kilo_heartbeats": 423,
   "median_ms": 72,
   "ms_samples": [
    49,
    141,
    72
   ],
   "status": "ok",
   "variant": "naive_simp"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    609462,
    609462,
    609462
   ],
   "k": 30,
   "kilo_heartbeats": 609,
   "median_ms": 118,
   "ms_samples": [
    118,
    169,
    95
   ],
   "status": "ok",
   "variant": "naive_simp"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    249487,
    249487,
    249487
   ],
   "k": 5,
   "kilo_heartbeats": 249,
   "median_ms": 41,
   "ms_samples": [
    41,
    44,
    31
   ],
   "status": "ok",
   "variant": "ablation_projection_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    2140284,
    2140284,
    2140284
   ],
   "k": 10,
   "kilo_heartbeats": 2140,
   "median_ms": 256,
   "ms_samples": [
    233,
    275,
    256
   ],
   "status": "ok",
   "variant": "ablation_projection_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [],
   "k": 20,
   "kilo_heartbeats": null,
   "median_ms": null,
   "ms_samples": [],
   "status": "timeout",
   "variant": "ablation_projection_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [],
   "k": 30,
   "kilo_heartbeats": null,
   "median_ms": null,
   "ms_samples": [],
   "status": "skipped",
   "variant": "ablation_projection_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    287458,
    287458,
    287458
   ],
   "k": 5,
   "kilo_heartbeats": 287,
   "median_ms": 42,
   "ms_samples": [
    42,
    47,
    41
   ],
   "status": "ok",
   "variant": "live_two_pass_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    498007,
    498007,
    498007
   ],
   "k": 10,
   "kilo_heartbeats": 498,
   "median_ms": 72,
   "ms_samples": [
    87,
    72,
    72
   ],
   "status": "ok",
   "variant": "live_two_pass_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    917320,
    917320,
    917320
   ],
   "k": 20,
   "kilo_heartbeats": 917,
   "median_ms": 164,
   "ms_samples": [
    164,
    172,
    136
   ],
   "status": "ok",
   "variant": "live_two_pass_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    1358640,
    1358640,
    1358640
   ],
   "k": 30,
   "kilo_heartbeats": 1359,
   "median_ms": 217,
   "ms_samples": [
    217,
    434,
    184
   ],
   "status": "ok",
   "variant": "live_two_pass_rfl"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    137212,
    137212,
    137212
   ],
   "k": 5,
   "kilo_heartbeats": 137,
   "median_ms": 18,
   "ms_samples": [
    14,
    21,
    18
   ],
   "status": "ok",
   "variant": "optimized_forcePureEnv"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    214428,
    214428,
    214428
   ],
   "k": 10,
   "kilo_heartbeats": 214,
   "median_ms": 29,
   "ms_samples": [
    22,
    32,
    29
   ],
   "status": "ok",
   "variant": "optimized_forcePureEnv"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    365881,
    365881,
    365881
   ],
   "k": 20,
   "kilo_heartbeats": 366,
   "median_ms": 53,
   "ms_samples": [
    39,
    53,
    57
   ],
   "status": "ok",
   "variant": "optimized_forcePureEnv"
  },
  {
   "family": "local_slots",
   "hb_samples": [
    525001,
    525001,
    525001
   ],
   "k": 30,
   "kilo_heartbeats": 525,
   "median_ms": 69,
   "ms_samples": [
    69,
    69,
    70
   ],
   "status": "ok",
   "variant": "optimized_forcePureEnv"
  },
  {
   "family": "struct_fields",
   "hb_samples": [
    848269,
    848269,
    848269
   ],
   "k": 5,
   "kilo_heartbeats": 848,
   "median_ms": 93,
   "ms_samples": [
    93,
    102,
    91
   ],
   "status": "ok",
   "variant": "naive_rfl"
  },
  {
   "family": "struct_fields",
   "hb_samples": [
    21109483,
    21109483,
    21109483
   ],
   "k": 10,
   "kilo_heartbeats": 21109,
   "median_ms": 2917,
   "ms_samples": [
    2991,
    2860,
    2917
   ],
   "status": "ok",
   "variant": "naive_rfl"
  },
  {
   "family": "struct_fields",
   "hb_samples": [],
   "k": 20,
   "kilo_heartbeats": null,
   "median_ms": null,
   "ms_samples": [],
   "status": "timeout",
   "variant": "naive_rfl"
  },
  {
   "family": "struct_fields",
   "hb_samples": [],
   "k": 30,
   "kilo_heartbeats": null,
   "median_ms": null,
   "ms_samples": [],
   "status": "skipped",
   "variant": "naive_rfl"
  },
  {
   "family": "struct_fields",
   "hb_samples": [
    409139,
    409139,
    409139
   ],
   "k": 5,
   "kilo_heartbeats": 409,
   "median_ms": 62,
   "ms_samples": [
    59,
    77,
    62
   ],
   "status": "ok",
   "variant": "naive_simp"
  },
  {
   "family": "struct_fields",
   "hb_samples": [
    507055,
    507055,
    507055
   ],
   "k": 10,
   "kilo_heartbeats": 507,
   "median_ms": 82,
   "ms_samples": [
    72,
    200,
    82
   ],
   "status": "ok",
   "variant": "naive_simp"
  },
  {
   "family": "struct_fields",
   "hb_samples": [
    695418,
    695418,
    695418
   ],
   "k": 20,
   "kilo_heartbeats": 695,
   "median_ms": 104,
   "ms_samples": [
    104,
    247,
    99
   ],
   "status": "ok",
   "variant": "naive_simp"
  },
  {
   "family": "struct_fields",
   "hb_samples": [
    889104,
    889104,
    889104
   ],
   "k": 30,
   "kilo_heartbeats": 889,
   "median_ms": 127,
   "ms_samples": [
    121,
    135,
    127
   ],
   "status": "ok",
   "variant": "naive_simp"
  },
  {
   "family": "struct_fields",
   "hb_samples": [
    132749,
    132749,
    132749
   ],
   "k": 5,
   "kilo_heartbeats": 133,
   "median_ms": 17,
   "ms_samples": [
    17,
    17,
    17
   ],
   "status": "ok",
   "variant": "optimized_typedAt_lens"
  },
  {
   "family": "struct_fields",
   "hb_samples": [
    201026,
    201026,
    201026
   ],
   "k": 10,
   "kilo_heartbeats": 201,
   "median_ms": 24,
   "ms_samples": [
    22,
    24,
    30
   ],
   "status": "ok",
   "variant": "optimized_typedAt_lens"
  },
  {
   "family": "struct_fields",
   "hb_samples": [
    337759,
    337759,
    337759
   ],
   "k": 20,
   "kilo_heartbeats": 338,
   "median_ms": 38,
   "ms_samples": [
    45,
    36,
    38
   ],
   "status": "ok",
   "variant": "optimized_typedAt_lens"
  },
  {
   "family": "struct_fields",
   "hb_samples": [
    474905,
    474905,
    474905
   ],
   "k": 30,
   "kilo_heartbeats": 475,
   "median_ms": 59,
   "ms_samples": [
    59,
    62,
    56
   ],
   "status": "ok",
   "variant": "optimized_typedAt_lens"
  },
  {
   "family": "loop_trip",
   "hb_samples": [
    56664798,
    56664798,
    56664798
   ],
   "k": 5,
   "kilo_heartbeats": 56665,
   "median_ms": 5403,
   "ms_samples": [
    5387,
    5403,
    11795
   ],
   "status": "ok",
   "variant": "naive_fuel_rfl"
  },
  {
   "family": "loop_trip",
   "hb_samples": [],
   "k": 10,
   "kilo_heartbeats": null,
   "median_ms": null,
   "ms_samples": [],
   "status": "timeout",
   "variant": "naive_fuel_rfl"
  },
  {
   "family": "loop_trip",
   "hb_samples": [],
   "k": 20,
   "kilo_heartbeats": null,
   "median_ms": null,
   "ms_samples": [],
   "status": "skipped",
   "variant": "naive_fuel_rfl"
  },
  {
   "family": "loop_trip",
   "hb_samples": [],
   "k": 30,
   "kilo_heartbeats": null,
   "median_ms": null,
   "ms_samples": [],
   "status": "skipped",
   "variant": "naive_fuel_rfl"
  },
  {
   "family": "loop_trip",
   "hb_samples": [
    1979263,
    1979263,
    1979263
   ],
   "k": 5,
   "kilo_heartbeats": 1979,
   "median_ms": 428,
   "ms_samples": [
    436,
    338,
    428
   ],
   "status": "ok",
   "variant": "naive_fuel_simp"
  },
  {
   "family": "loop_trip",
   "hb_samples": [
    4308047,
    4308047,
    4308047
   ],
   "k": 10,
   "kilo_heartbeats": 4308,
   "median_ms": 822,
   "ms_samples": [
    822,
    820,
    1085
   ],
   "status": "ok",
   "variant": "naive_fuel_simp"
  },
  {
   "family": "loop_trip",
   "hb_samples": [
    11171627,
    11171627,
    11171627
   ],
   "k": 20,
   "kilo_heartbeats": 11172,
   "median_ms": 2803,
   "ms_samples": [
    2803,
    2417,
    2925
   ],
   "status": "ok",
   "variant": "naive_fuel_simp"
  },
  {
   "family": "loop_trip",
   "hb_samples": [
    21063120,
    21063120,
    21063120
   ],
   "k": 30,
   "kilo_heartbeats": 21063,
   "median_ms": 5791,
   "ms_samples": [
    5701,
    5791,
    6628
   ],
   "status": "ok",
   "variant": "naive_fuel_simp"
  },
  {
   "family": "loop_trip",
   "hb_samples": [
    157802,
    157802,
    157802
   ],
   "k": 5,
   "kilo_heartbeats": 158,
   "median_ms": 35,
   "ms_samples": [
    41,
    31,
    35
   ],
   "status": "ok",
   "variant": "optimized_runCfgToBlock_forRangeUp"
  },
  {
   "family": "loop_trip",
   "hb_samples": [
    157755,
    157755,
    157755
   ],
   "k": 10,
   "kilo_heartbeats": 158,
   "median_ms": 27,
   "ms_samples": [
    27,
    26,
    30
   ],
   "status": "ok",
   "variant": "optimized_runCfgToBlock_forRangeUp"
  },
  {
   "family": "loop_trip",
   "hb_samples": [
    157749,
    157749,
    157749
   ],
   "k": 20,
   "kilo_heartbeats": 158,
   "median_ms": 30,
   "ms_samples": [
    38,
    27,
    30
   ],
   "status": "ok",
   "variant": "optimized_runCfgToBlock_forRangeUp"
  },
  {
   "family": "loop_trip",
   "hb_samples": [
    157753,
    157753,
    157753
   ],
   "k": 30,
   "kilo_heartbeats": 158,
   "median_ms": 32,
   "ms_samples": [
    32,
    39,
    28
   ],
   "status": "ok",
   "variant": "optimized_runCfgToBlock_forRangeUp"
  }
 ],
 "schema": "fuel-free-lens-bench/v1"
}
```

</details>

<!-- BENCH:END -->

Measured claims (quoted verbatim from the receipt by `--verify-report`):

- `local_slots/optimized_forcePureEnv` at K = 30: 525 k heartbeats
- `struct_fields/optimized_typedAt_lens` at K = 30: 475 k heartbeats
- `loop_trip/optimized_runCfgToBlock_forRangeUp` at K = 30: 158 k heartbeats

Interpretation (A2 receipt; heartbeats are deterministic and identical to the B1–B2 receipts, while
wall-clock medians are re-measured on the A2 prototype revision on a host that ran about 1.4× slower
than during A1, judging by `loop_trip/naive_fuel_simp` at K = 30):

* **Loops.** The fuel-free proof costs 158 k heartbeats (27–35 ms) at every trip count, while explicit
  fuel under `simp` grows super-linearly from 1979 k to 21063 k heartbeats (about K^1.3; 428 ms →
  5791 ms) and `rfl` needs 56665 k at K = 5 (5403 ms) and times out from K = 10. This is the only
  *asymptotic* separation from `simp`.
* **Struct fields.** The `TypedAt` lens proof (133 k → 475 k heartbeats) and byte-list `simp`
  (409 k → 889 k) are both linear in K; the lens proof needs 1.9–3.1× fewer heartbeats (59 ms vs
  127 ms at K = 30). Byte-level `rfl` grows from 848 k to 21109 k and times out from K = 20.
* **Local slots.** The single-pass forced run (`optimized_forcePureEnv`, 137 k → 525 k, 18 → 69 ms),
  `List.set` `simp` (156 k → 609 k, 27 → 118 ms), and the live two-pass normalization
  (`live_two_pass_rfl`, 287 k → 1359 k, 42 → 217 ms) are all linear: the forced run needs 1.14–1.16×
  fewer heartbeats than `simp` and 2.1–2.6× fewer than the live strategy, which itself needs 1.8–2.2×
  more than `simp`. The forced-run / `simp` wall-clock ratio varies between receipts (about 1.0× in A1,
  1.3× in B2, 1.4–1.7× here), so only the heartbeat ratio is a stable signal. Plain `rfl`
  (145 k → 1105 k) and end-of-chain projection (249 k → 2140 k) both time out from K = 20.

## 6. Track A integration mapping

| Live module | Prototype artifact | Track A action |
|---|---|---|
| `MirFuelFree.lean` / `FunctionalTranslation.lean` | `mirStep`, `mirWpConverges_of_wpConverges`, `mirStepsConverges_of_stepsTo`, `mirWpConverges_of_stepsTo_bind`, `runMirToBlock`, `live_runMirToBlock_stationary_at_target`, `runUntilTarget_reached_iff_live_runMirToBlock`, `runMirToBlock_reached_iff_step_and_live` | Add a mandatory-first-step header wrapper around the existing `Anneal.FunctionalTranslation.runMirToBlock` (which is stationary at `stmtIdx = 0`) with 4-way `TargetOutcome`; reuse `StepsTo` / `FirstHitIn` |
| `MirLoops.lean` | `forRangeUp_eq_live`, `live_forRangeUp_induction`, `wpConverges_forRangeUp`, `mirWpConverges_forRangeUp`, `live_countToN_mirWpConverges_all_n` | Either replace the well-founded `forRangeUp` by the structural one (kernel-reducible; proven equal) or keep both with `forRangeUp_eq_live` as the bridge |
| `PureMirExec.lean` | `toMirShape`, `hasCfgBackedge_toMirShape`, `inferMinFragment_toMirShape`, `inferMinFragment_refShape`, `fragment_levels_strict` | Route Pillar 1 obligations by `inferMinFragment` (`.pureLoopFree` / `.pureBoundedLoop`) and Pillar 4 obligations to `.treeBorrowsLocal` |
| `MirLiftCore.lean` | `forcePureEnv`, `forceSpine?`, `setSpine?`, `setPureEnvSlot?`, `forceSpine?_eq_live`, `evalPureStmtNorm_eq_bind_forceSpine?`, `setPureEnvSlot?_eq_live_bind_forcePureEnv?`, `applySlotUpdatesForced`, `applySlotUpdatesForced_eq_forcePureEnv`, `applySlotUpdatesTwoPass_eq_live?`, `liveSet?_eq_setSpine?`, `applySlotUpdatesLive?_eq_forced` | Replace the two-pass `(set? env loc s).bind forcePureEnv?` of live `set?_of_forcePureEnv?` / `evalPureStmtNorm` (measured as `live_two_pass_rfl`) with single-pass `setPureEnvSlot?` (measured analogue `optimized_forcePureEnv`, 2.1–2.6× fewer heartbeats); add the projection and length-mismatch lemmas |
| `ByteCodec.lean` | `TypedAt`, `readTyped`, `writeTyped`, `DisjointSlice`, `laidOutPair`, `typedAt_append_encode`, `typedAt_laidOutPair_iff`, `typedAt_laidOutPair_write_fst`, `typedAt_laidOutPair_write_snd`, `typedAt_laidOutPair_of_fieldsValid`, `typedAt_laidOutPair_applyFieldWrites` | Host the relational `TypedAt` and frame rules over the trusted byte primitives; add the `laidOutPair` field-projection and `applyFieldWrites` lemmas |
| `SepLogicLenses.lean` | `fieldLens`, `subplaceFieldLens_disjoint`, `subplaceFieldLens_of_borrowSubplace_disjointOn`, `structLens_lawful`, `applyFieldWrites_spec`, Tree Borrows model and `TrustedFnSpec` | Instantiate `IndependentLenses` for byte-addressed fields via `BorrowSubplace.disjointOn`; host `TrustedFnSpec.reborrowFootprint` with the pre-release ordering |
| trusted `MirSemantics` (`Places.lean`, `Terminators.lean`) | `performTransition_accessed_eq_live`, `performTransition_unaccessed_eq_live`, `performTransition_entry_eq_live`, `isTagProtected_eq_live`, `nodeAccessRelatedness_visit_eq_live_writer`, `borrowEntryWriteConflicts_eq_live`, `restoreCallerProtectors_eq_live`, `split_at_mut_stage2Only_unique_write_perm`, `stage1_vs_stage2Only_two_arg_release_differs`, `stage1_vs_stage2Only_two_arg_release_unobservable`, `LatchEquiv.noUB_iff` | Keep these as the conformance check between Pillar 4 and `treeBorrowNodeAccess` / `resolveTreeBorrowWriterTag`; single-reference `split_at_mut`/`get_mut` postconditions already hold under `restoreCallerProtectors`, and the only exhibited stage-1 / stage-2-only difference is unobservable, so adding stage-1 release on return is a fidelity choice (or a proof obligation: observational equivalence), not a demonstrated soundness fix |

## 7. Decision rationale and conditions

**CONDITIONAL GO.** All four pillars are proven end-to-end against the live signatures with
constructive axioms, and the Pillar 4 automaton is now pinned to the trusted Tree Borrows
transition function (Round A1). The measured wins differ in kind: `loop_trip` is the only family in
which the optimized proof is *asymptotically* cheaper than `simp` (constant heartbeats in the trip
count versus super-linear growth); `struct_fields` and `local_slots` are linear under both `simp` and
the optimized strategy, with constant-factor heartbeat savings of 1.9–3.1× and 1.14–1.16×
respectively (the `local_slots` wall-clock ratio varies between receipts, about 1.0–1.7×), and the
single-pass forcing beats the live two-pass normalization by 2.1–2.6×; plain `rfl` is
exponential in every family. Conditions:

1. **`forcePureEnv` must be applied step-wise (`setSpine?` / `forcePureEnv?`), not only at the end
   of an unforced `List.set` chain.** Projection of an already-nested `List.set` chain still incurs
   smart-unfolding blow-up in `Meta.whnf` (row `ablation_projection_rfl`); only forcing the spine at
   each update (`setSpine?` / `applySlotUpdatesForced`, which computes exactly the `forcePureEnv`
   normal form: `applySlotUpdatesForced_eq_forcePureEnv`) achieves linear scaling. The live code
   already normalizes step-wise, but in two passes (`evalPureStmtNorm`), which the `live_two_pass_rfl`
   row shows to be the costliest linear strategy (above `List.set` `simp`); the single-pass form
   (`setSpine?`, and `setPureEnvSlot?` for `PureEnv`) is what earns the 2.1–2.6× saving.
2. **Extend `mirStep` with external call handling when lifting `.fullMir` bodies.** Rounds B1–B2 fixed
   `mirStep` to step across all `MirObs` emissions (`.vis (.inr (.inl (.emit _)))`, both `.switchInt`
   `.event` and `.silent`), bridged to live `Anneal.FunctionalTranslation.runMirToBlock`
   (`runMirToBlock_reached_iff_step_and_live`), and verified live `Anneal.MirLoops.countToNBody n`
   end-to-end; bodies that make external calls still require the full `MirTraceWpConverges` /
   call-spec rules.
3. **Integrate `TrustedFnSpec.reborrowFootprint` with the live `BorrowEntry` table and decide the
   release semantics.** The per-location automaton equals the trusted `treeBorrowNodeAccess` on accessed
   locations (`performTransition_accessed_eq_live`, `performTransition_entry_eq_live`) and the
   `parentTag` / return-protector bookkeeping is bridged (`nodeAccessRelatedness_visit_eq_live_writer`,
   `borrowEntryWriteConflicts_eq_live`, `restoreCallerProtectors_eq_live`). Single-reference
   `split_at_mut` postconditions already hold under the live stage-2-only `restoreCallerProtectors`
   path (`split_at_mut_stage2Only_unique_write_perm`), and the two-argument separation
   (`stage1_vs_stage2Only_two_arg_release_differs`) is a conflict latch on a tag whose protector ends
   with the same call, which is unobservable (`stage1_vs_stage2Only_two_arg_release_unobservable`). No
   observable difference between stage-1 + stage-2 and stage-2-only release is known, so Track A should
   either add stage 1 for Miri fidelity or prove observational equivalence under the function-entry /
   last-in-first-out protector discipline (`LatchEquiv` is the starting point) before wiring
   `TrustedFnSpec.run` into `evalTerminator`.
4. **Keep the constructive-axiom audit.** The core `List.drop_take` uses `Classical.choice`, and
   `omega` inserts `Classical.byContradiction` on non-atomic goals; the prototype avoids both
   (`drop_take_add`, split conjunctions), and Track A should keep a `#guard_msgs` axiom audit.

## 8. Findings and limitations

* **Smart-unfolding blow-up confirmed.** Default `rfl` over nested `List.set` / byte writes / fuel
  unrolling is exponential in the elaborator (see the `naive_rfl` and `naive_fuel_rfl` rows).
* **Live `forRangeUp` is well-founded.** `Anneal.MirLoops.forRangeUp` (`termination_by`) does not
  reduce in the kernel; the structural variant is proven equal (`forRangeUp_eq_live`).
* **Trusted zero-width asymmetry.** `writeAbstractBytesAt` succeeds as a no-op for an empty write
  at *any* offset, while `sliceAbstractBytes` rejects an empty read past the end
  (`zeroWidth_write_read_asymmetry`); Track A specs over zero-sized types must account for it.
* **Relational vs exact typing.** Exact-encoding predicates reject initialized padding; the
  relational `TypedAt` accepts it (`typedAt_laidOutPair_init_padding`), while lens lawfulness
  requires canonical encodings (`CanonicalAt`, `FieldsValid`, bridged to whole-struct `TypedAt` by
  `typedAt_laidOutPair_of_fieldsValid`).
* **Overlapping `reborrowFootprint` vs omitted footprint.** Omitting `reborrowFootprint` aliases the
  parent tag and unsoundly permits cross-slice writes (`same_tag_split_unsound_control`), whereas an
  overlapping `reborrowFootprint` mints sibling tags where writing the overlap byte through one
  sibling disables the other (`overlapping_reborrowFootprint_write_disables_sibling`).
* **Tree Borrows automaton drift (found in Round A1).** Through B1 the prototype's
  `performTransition` disagreed with the trusted `treeBorrowNodeAccess` on two accessed cells (a
  foreign write to a protected `Disabled` location was UB, although Miri's `skip_if_known_noop` and the
  trusted semantics treat it as a no-op; a foreign read of a protected `ReservedIM` succeeded, although
  the trusted semantics fails closed with `.protectedReservedIM`) and deviated from Miri's `accessed`
  guard on two unaccessed cells. A permission bijection cannot detect such drift; the transition-level
  theorems (`performTransition_accessed_eq_live`, `performTransition_unaccessed_eq_live`) now do. No
  Pillar 4 theorem depended on the drifted cells: all re-check unchanged after the fix.
* **Trusted return path has no stage-1 release, without a known observable consequence.** The
  trusted semantics drops callee protectors at return (`restoreCallerProtectors`) without Miri's
  protector-end implicit access; the prototype models both stages (`applyReleaseProtector`,
  `removeActiveProtector`). The only exhibited state difference is unobservable
  (`stage1_vs_stage2Only_two_arg_release_unobservable`). See condition 3.
* **The live slot normalizer is two-pass.** `Anneal.MirLiftCore.evalPureStmtNorm` already forces the
  frame after every statement, but via `(set? env loc s).bind forcePureEnv?`, a second full traversal;
  measured on the same obligations (`live_two_pass_rfl`) it costs more than `List.set` `simp`, while the
  single-pass forms (`setSpine?`, `setPureEnvSlot?`) cost less.
* **Limitations.** Heartbeats are thread-local elaboration heartbeats; wall-clock figures are
  single-host medians. The struct-field optimized proof applies `applyFieldWrites_spec`, which is
  proven once in the prototype module (compile time recorded in the receipt as
  `prototype_compile_ms`).

## 9. Adversarial round log

### Round A0 (Agent A, Model X) — initial implementation

Implemented all five success criteria. Notable self-audit outcomes: removed every
`Classical.choice` dependency (introduced by `List.drop_take`, by `omega` on conjunction goals, and
by `simp` closing a self-loop goal), replaced the probe's end-of-chain `forcePureEnv` by step-wise
forcing after measuring the blow-up, made `TypedAt` relational so padding contents are irrelevant,
stated the `get_mut` / `split_at_mut` results for the true post-`endCall` protector set, proved the
first-hit characterization of `runToTarget` (no overshoot), and added non-vacuity witnesses
(`split_at_mut_rootTree_nonvacuous`, concrete `countUp` / self-loop examples).

### Round B1 (Agent B, Model Y) — critique and fixes against A0 (`9029805b`)

1. **[CRITICAL — Pillar 1 Live MIR Bridge Bug] `mirStep` & `runMirToBlock` faulted on every `.switchInt` loop header in live MIR.**
   In `Trusted.Rustc.V2026_06_01.MirSemantics`, `.switchInt` emits `.vis (.inr (.inl (.emit (.event sc.bits)))) (fun _ => .running s')` (`MirStepNode.emitStep`). A0's `mirStep` matched only `.tau (.running s')` and mapped every `.vis` node to `.fault`, causing `runMirToBlock` to return `.stuck` on every conditional branch and loop in live MIR. Fixed `mirStep` to continue on `.vis (.inr (.inl (.emit (.event _))))` (matching live `Anneal.FunctionalTranslation.runMirToBlock`), updated `stepMirFn_of_mirStep_cont` / `mirStepsConverges_of_stepsTo` / `mirWpConverges_of_evalFuel` via `step_emit`, and proved end-to-end live `CapturedMir` execution on `Anneal.MirLoops.countToNBody n` (`runMirToBlock_countToN_entry`, `runMirToBlock_countToN_iter`, `runMirToBlock_countToN_exit`, `live_countToN_mirWpConverges_all_n`).
2. **[CRITICAL — Pillar 2 Performance & Spec Flaws in `forcePureEnvD` and `applySlotUpdatesForced`.]**
   A0 defined `forcePureEnvD` as `env.headD d :: forcePureEnvD d n env.tail`, duplicating `env` across `headD` and `tail` at every recursion level (causing `ablation_projection_rfl` at `K = 10` to take 14,581 k heartbeats), and defined `applySlotUpdatesForced` using two-pass `forceSpine? (env.set u.1 u.2)` (929 k heartbeats at `K = 30`, 1.5× slower than `naive_simp`'s 609 k). Replaced `forcePureEnvD` with single-match recursion (cutting `ablation_projection_rfl` at `K = 10` by 6.8× to 2,140 k heartbeats), introduced single-pass `setSpine?` + `setSpine?_eq_forceSpine?_set` in `applySlotUpdatesForced` (cutting `optimized_forcePureEnv` at `K = 30` to 525 k heartbeats / 55 ms, beating `naive_simp` at every `K`), and proved the missing length-mismatch characterization (`forcePureEnvD_eq_take_append_replicate`, `forcePureEnv_ne_self_of_length_ne`, `forcePureEnv_eq_self_iff`).
3. **[HIGH — Pillar 1 Missing Non-Terminating Loop Characterization.]**
   Added `infiniteLoopCfg` (`[.goto 0]`) and proved `evalFuel_infiniteLoop_outOfFuel`, `not_wpConverges_infiniteLoop`, and `runToTarget_infiniteLoop_outOfFuel`.
4. **[HIGH — Pillar 3 Missing `FieldsValid` → `laidOutPair` & Live `BorrowSubplace` Bridges.]**
   Proved `typedAt_of_canonicalAt`, `typedAt_laidOutPair_of_fieldsValid` (bridging `FieldsValid` to whole-struct `TypedAt` across arbitrary padding bytes), and `subplaceFieldLens_of_borrowSubplace_disjointOn` (bridging live `Anneal.SepLogicLenses.BorrowSubplace.disjointOn` to `DisjointSlice`, `LawfulMutLens`, and `IndependentLenses`).
5. **[HIGH — Pillar 4 Missing Overlapping `reborrowFootprint`, Parent-Write Variants & Live `TreeBorrowPerm`/`BorrowEntry` Bridges.]**
   Proved `reborrow_return_after_parent_write_unique_write_perm` (callee writes through parent `t_arg` before reborrowing `t_ret`), `callee_parent_write_after_reborrow_disables_child` (negative dual: parent write after reborrowing disables `t_ret`), `overlapping_reborrowFootprint_write_disables_sibling` (overlapping `&mut` footprint ranges disable sibling on write), and the live `TreeBorrowPerm` / `BorrowEntry` bridges (`ofLiveTreeBorrowPerm?_toLiveTreeBorrowPerm`, `toLiveTreeBorrowPerm_ofLiveTreeBorrowPerm?`, `liveBorrowEntryRange_contains_iff`).

### Round A1 (Agent A, Model X) — critique and fixes against B1 (`24a7dddc`)

1. **[HIGH — Pillar 4 automaton drift hidden by a renaming-only live bridge.]** B1's live
   `TreeBorrowPerm` bridge was a constructor bijection (`cases p <;> rfl`) that never compared
   transitions. Comparing `performTransition` cell by cell with the trusted `treeBorrowNodeAccess`
   exposed two disagreements on accessed locations (a foreign write to a protected `Disabled`
   location was UB instead of Miri's `skip_if_known_noop` no-op; a foreign read of a protected
   `ReservedIM` succeeded instead of failing closed like the trusted `.protectedReservedIM`) and two
   deviations from Miri's `accessed` guard on unaccessed locations. Fixed the automaton, replaced the
   `NonAncestorSafe` exclusion of `Active` by the fail-closed protected `ReservedIM`, and proved
   `performTransition_accessed_eq_live`, `performTransition_unaccessed_eq_live`,
   `performTransition_accessed_isSome_eq_live`, `isTagProtected_eq_live`,
   `performTransition_entry_eq_live`, and the regressions `foreign_write_disabled_protected_noop` /
   `protected_reservedIM_foreign_fails_closed`. Every Pillar 4 theorem re-checks unchanged.
2. **[MEDIUM — Pillar 2 optimized variant was disconnected from `forcePureEnv` and from the live slot
   update.]** After B1, `optimized_forcePureEnv` only ran `setSpine?`, with no theorem relating it to
   `forcePureEnv` or to the trusted `Trusted.Sequence.set?` used by `evalPureStmt`. Added
   `setSpine?_eq_some_forcePureEnv_set`, `applySlotUpdatesForced_eq_forcePureEnv`,
   `liveSet?_eq_setSpine?`, `applySlotUpdatesLive?_eq_forced`, and `applySlotUpdatesLive?_oob`.
3. **[MEDIUM — Report overclaims and stale receipts.]** The decision line claimed all three optimized
   strategies "win both asymptotically and by a constant factor over `rfl` and `simp`"; against
   `simp`, `local_slots` and `struct_fields` are linear on both sides (constant-factor wins only) and
   only `loop_trip` wins asymptotically. Section 3 still reported A0's guard count, and Section 6
   presented a hypothetical `evalPureStmtNorm` as if it were a live definition [retracted in Round A2:
   `Anneal.MirLiftCore.evalPureStmtNorm` is live; Round B2 was right]. Corrected the text and
   added drift tests:
   `test_report_theorem_counts_match_source`, `test_report_names_resolve` (every cited identifier must
   resolve to a prototype declaration or to a declaration of the live module it names), and its
   negative self-test `test_report_name_check_detects_invented_names`; `test_tree_borrows_bridge_is_semantic`
   requires the transition-level bridge.
4. **[LOW — Non-vacuity of B1's `BorrowSubplace` bridge.]** Its layout hypothesis quantifies over every
   pair of distinct field indices; `subplaceFieldLens_of_borrowSubplace_disjointOn_nonvacuous` exhibits
   a concrete layout and live `disjointOn` witness.
5. **[LOW — Track A integration gap not reported.]** The trusted return path restores only the caller's
   protector list (`restoreCallerProtectors`) and performs no stage-1 protector-end access; recorded in
   Sections 6–8. Also removed B1's trailing blank lines in the axiom audit and re-measured every
   benchmark on the new prototype revision.

### Round B2 (Agent B, Model Y) — critique and fixes against A1 (`5f7b66e5`)

1. **[HIGH — Pillar 1 Live `runMirToBlock` Stationary-at-Header Flaw & `MirObs.silent` Emission Gap in `mirStep`.]**
   A1's `mirStep` matched only `.vis (.inr (.inl (.emit (.event _)))) k` and mapped `.emit .silent` to `.fault`, diverging from live `Anneal.FunctionalTranslation.runMirToBlock` (`FunctionalTranslation.lean:635`) and `Anneal.MirFuelFree.MirStepsConverges.of_runMirToBlock`. Furthermore, A1's §6 proposed adding a `runMirToBlock` stepper from scratch without bridging to the already-existing live `Anneal.FunctionalTranslation.runMirToBlock`. Generalized `mirStep` to `.vis (.inr (.inl (.emit _))) k`, updated `mirStepsConverges_of_mirStep_cont` / `mirWpConverges_of_mirStep_cont`, and proved `live_runMirToBlock_stationary_at_target`, `runUntilTarget_reached_iff_live_runMirToBlock`, and `runMirToBlock_reached_iff_step_and_live` (showing the live stepper halts in 0 steps when started at `(target, 0)` and that the prototype's `runMirToBlock` is one mandatory `mirStep` followed by the live stepper).
2. **[HIGH — Pillar 2 Factual Error on Live `evalPureStmtNorm` & Missing Constructor-Forcing `setPureEnvSlot?`.]**
   Round A1 claimed `evalPureStmtNorm` was "a hypothetical ... as if it were a live definition" and removed it from §6, overlooking that `Anneal.MirLiftCore.evalPureStmtNorm` (`MirLiftCore.lean:398`), `evalPureStmtsN`, and `set?_of_forcePureEnv?` *are* live definitions in `MirLiftCore.lean`—and that live `forcePureEnv?` also forces `LocalSlot` constructors (`.dead` / `.uninit` / `.init`), whereas `setSpine?` only forced `List.cons`. Added single-pass constructor-forcing `setPureEnvSlot?` and proved `setPureEnvSlot?_eq_set?`, `setPureEnvSlot?_eq_live_bind_forcePureEnv?` (drop-in single-pass replacement for two-pass `(set? env loc s).bind forcePureEnv?`), and `evalPureStmtNorm_eq_bind_forceSpine?`.
3. **[HIGH — Pillar 4 Unbridged Live Hierarchy / Return Path (`restoreCallerProtectors`) & Untested `Mutability.not`.]**
   A1's Condition 3 left open whether `reborrowFootprint` specs hold under the live stage-2-only `restoreCallerProtectors` return path, left the live `parentTag` hierarchy (`isBorrowDescendantOrSelf`, `resolveTreeBorrowWriterTag`, `borrowEntryWriteConflicts`) unbridged, and never tested `Mutability.not` in `TrustedFnSpec.reborrowFootprint`. Proved `split_at_mut_stage2Only_unique_write_perm` (`split_at_mut` retains `HasUniqueWritePerm` and cross-half UB under `TrustedFnSpec.runStage2Only`), `stage1_vs_stage2Only_two_arg_release_differs` (pinpointing the exact UB-free two-argument two-phase borrow scenario where stage-1 release latches `ReservedFrz true` while stage-2-only leaves `ReservedFrz false`), `shared_reborrowFootprint_read_ok_write_ub` (`Mutability.not` shared reborrows), and the live hierarchy/return bridges (`isBorrowDescendantOrSelf_refl`, `nodeAccessRelatedness_visit_eq_live_writer`, `borrowEntryWriteConflicts_eq_live`, `restoreCallerProtectors_eq_live`).
4. **[MEDIUM — Pillar 3 Missing `typedAt_laidOutPair_write_fst` & `applyFieldWrites` → `laidOutPair` Bridge.]**
   Added `typedAt_laidOutPair_write_fst` (symmetric to `typedAt_laidOutPair_write_snd` across intervening padding) and `typedAt_laidOutPair_applyFieldWrites` (proving `K` sequential `fieldLens` writes preserve whole-struct `TypedAt (laidOutPair …)` across arbitrary padding bytes).
5. **[LOW — Audit Test Blind Spots in `test_report_names_resolve` and `test_every_theorem_has_axiom_guard`.]**
   `unresolved_names` previously skipped every unqualified camelCase token without `_` (missing invented names like `"evalPureStmtMagic"`, which also masked live `evalPureStmtNorm`), and `test_every_theorem_has_axiom_guard` matched only plain `^theorem\s+` without rejecting `lemma` or `private`/`protected`/attributed `theorem` declarations. Tightened both tests (`test_report_name_check_detects_invented_names` now checks camelCase tokens).

### Round A2 (Agent A, Model X) — critique and fixes against B2 (`66f9ae90`)

1. **[HIGH — Condition 3 rested on an unobservable difference.]** B2 concluded that two-argument
   conflict latching "requires adding stage-1 release to the trusted return path". The separating
   state in `stage1_vs_stage2Only_two_arg_release_differs` is a `ReservedFrz` conflict latch on a tag
   whose protector ends with the same call, and a latch is inert once its tag is unprotected. Proved
   this formally: `performTransition_unprotected_eraseLatch` (per location), the simulation `LatchEquiv`
   preserved by every tree operation (`LatchEquiv.access`, `LatchEquiv.insert`, `LatchEquiv.retag`,
   `LatchEquiv.release`, `LatchEquiv.of_active`) with equal UB verdicts (`LatchEquiv.noUB_iff`,
   `LatchEquiv.releaseNoUB_iff`), the general read-release lemma `applyReleaseProtector_read_eraseLatch`,
   and `stage1_vs_stage2Only_two_arg_release_unobservable` /
   `stage1_vs_stage2Only_two_arg_release_same_verdicts` for B2's exact scenario
   (full stage-1 release of both arguments, then `GlobalState.endCall`). Condition 3, Section 6, and
   Section 8 now state that no observable stage-1 / stage-2-only difference is known.
2. **[HIGH — The Pillar 2 Track A recommendation was not measured against the live strategy.]** B2
   (correctly) found that live `evalPureStmtNorm` already normalizes step-wise, but recommended replacing
   its two-pass `(set? env loc s).bind forcePureEnv?` with single-pass `setPureEnvSlot?` without any
   receipt. Added `applySlotUpdatesTwoPass` (the live structure over the benchmark's frames;
   `applySlotUpdatesTwoPass_eq_live?`, soundness `applySlotUpdates_eq_of_twoPass`) and the benchmark
   variant `local_slots/live_two_pass_rfl`: 287 k → 1359 k heartbeats for K = 5 → 30, i.e. 1.8–2.2×
   *more* than `List.set` `simp` and 2.1–2.6× more than single-pass forcing, so the replacement is now
   grounded (and the live normalizer is shown to be the costliest linear option). A methodology probe
   confirmed that `#measure` includes kernel checking (`Elab.async false`).
3. **[CORRECTION — my own A1 error.]** A1 claimed `evalPureStmtNorm` was not a live definition; it is
   (`Anneal.MirLiftCore.evalPureStmtNorm`). The A1 entry is annotated as retracted.
4. Tests: `test_live_two_pass_variant_mirrors_live_normalizer` pins the live two-pass structure of the
   new variant, and the required-theorem list covers the new `LatchEquiv` / two-pass results.
