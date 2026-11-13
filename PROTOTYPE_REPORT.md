# Track P Prototype Report: `ws-proto-fuel-free-loop-lifting-and-typed-at-lenses` (`ep1`)

Prototype-only deliverable (Track P, `merge_policy = "no_merge_prototype"`) for the
`PROPOSED_HOLD` Track A workstream `ws-fuel-free-loop-lifting-and-typed-at-lenses`.
Everything here is validated directly against the live signatures of `Anneal.PureMirExec`,
`Anneal.MirLiftCore`, `Anneal.MirFuelFree`, `Anneal.MirLoops`, `Anneal.SepLogicLenses`, and
`Anneal.ByteCodec` (the prototype module imports them; it is not imported by `Anneal.lean`).

**Decision: CONDITIONAL GO**

Proceed with `ws-fuel-free-loop-lifting-and-typed-at-lenses` under the conditions in
[Section 7](#7-decision-rationale-and-conditions): adopt fuel-free range-loop lifting,
`TypedAt` field lenses, and step-wise single-pass `setSpine?` / `forcePureEnv` normalization
(all three now win both asymptotically and by a constant factor over `rfl` and `simp` at every
measured size `K ∈ {5, 10, 20, 30}`), while ensuring `forcePureEnv` is applied step-wise rather
than as an end-of-chain projection over an unforced `List.set` tower.

## 1. Deliverables

| File | Contents |
|---|---|
| `theory/Anneal/FuelFreeLoopAndTypedAtLensPrototype.lean` | 240 kernel-checked theorems (0 `sorry`, 0 warnings), each audited by a `#guard_msgs in #print axioms` block (`propext` / `Quot.sound` only) |
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
  `.switchInt` observation steps (`.vis (.inr (.inl (.emit (.event _))))`, matching live
  `Anneal.FunctionalTranslation.runMirToBlock`), while root returns halt and external calls/faults
  map conservatively to `.fault`; `mirStepsConverges_of_stepsTo` and
  `mirWpConverges_of_wpConverges` transport generic proofs to the live
  `Anneal.MirFuelFree.MirStepsConverges` / `MirWpConverges`; `mirWpConverges_of_stepsTo_bind`,
  `runMirToBlock` (+ soundness), and `mirWpConverges_forRangeUp` (stated with the live
  `Anneal.MirLoops.forRangeUp`) complete the live API and are exercised end-to-end on the live
  `CapturedMir` loop `Anneal.MirLoops.countToNBody n` (`runMirToBlock_countToN_entry`,
  `runMirToBlock_countToN_iter`, `runMirToBlock_countToN_exit`, and
  `live_countToN_mirWpConverges_all_n`). `inferMinFragment_toMirShape` proves, for
  *every* toy CFG, that the live classifier assigns its shape `.pureBoundedLoop` iff it has a
  back-edge and `.pureLoopFree` otherwise (via `hasCfgBackedge_toMirShape`);
  `inferMinFragment_refShape` shows a local `&mut` borrow lifts a shape to `.treeBorrowsLocal`.

### Pillar 2 — `forcePureEnv` slot-list normalization (Section 7)

`forcePureEnv n env` projects the `n`-slot prefix (padding with `default`) by single-pass pattern
matching on `env`; proven: `forcePureEnv_eq_self`, `forcePureEnvD_eq_take_append_replicate`,
`forcePureEnv_ne_self_of_length_ne`, `forcePureEnv_eq_self_iff` (exact length-mismatch
characterization), `getElem?_forcePureEnv`, `length_forcePureEnvD`, `forcePureEnv_set_comm`
(with the necessary side condition; `forcePureEnv_set_comm_counterexample` shows it cannot be
dropped), and `chained_sets_collapse_rfl` (nested symbolic `List.set` updates collapse to a flat
literal by `rfl`, no commutation lemmas). The step-wise form `applySlotUpdatesForced` re-forces the
modified prefix after every update with `setSpine?` (proven equal to `forceSpine? (env.set i v)` via
`setSpine?_eq_forceSpine?_set`); `applySlotUpdates_eq_of_forced` makes a single `rfl`
prove the whole update sequence (`slotUpdates_collapse_forced`: 12 updates). Live bridges:
`forceSpine?_eq_live` (agrees with `Anneal.MirLiftCore.forcePureEnv?` on every `PureEnv`),
`forcePureEnvSlots_eq_self`, and `forcePureEnvSlots_set?` (commutes with the trusted
`Trusted.Sequence.set?` used by `evalPureStmt`).

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
`typedAt_laidOutPair_write_snd`, `typedAt_laidOutPair_padding_write` (arbitrary padding writes
preserve the struct), `laidOutPair_encode_eq`, `typedAt_laidOutPair_init_padding` (an
initialized padding byte is still typed), `typedAt_of_canonicalAt`, and
`typedAt_laidOutPair_of_fieldsValid` (bridging `FieldsValid` to whole-struct `TypedAt` across
arbitrary padding bytes). `subplaceFieldLens_disjoint` builds live
`Anneal.FunctionalTranslation.LawfulMutLens` witnesses for both field lenses and a live
`Anneal.SepLogicLenses.IndependentLenses` witness; `subplaceFieldLens_of_borrowSubplace_disjointOn`
bridges live `Anneal.SepLogicLenses.BorrowSubplace.disjointOn` directly to `DisjointSlice`,
`LawfulMutLens`, and `IndependentLenses`; `structLens_lawful` reuses the live
`prodMutLens_lawful`; `applyFieldWrites_spec` discharges `K` sequential field writes with one lens
law per write.

### Pillar 4 — pre-release `reborrowFootprint` protector specs (Section 9)

Tree Borrows permissions `ReservedFrz`, `ReservedIM`, `Active`, `Frozen`, `Disabled` (bridged
injectively to the live `Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm` via
`ofLiveTreeBorrowPerm?_toLiveTreeBorrowPerm` / `toLiveTreeBorrowPerm_ofLiveTreeBorrowPerm?` and
`BorrowEntry` via `liveBorrowEntryRange_contains_iff`) with the
per-location automaton `performTransition`, a well-formed arbitrary-depth `BorrowTree`, the active
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
* `trustedSpec_reborrow_equivalence`: for `split_at_mut` and `get_mut` the concrete UB-checked
  callee semantics (`ConcreteCall`: entry retag, `CalleeRun` over `assertLe` / `rawPtr` /
  `reborrow`, return registers, UB-checked release) succeeds with exactly the spec's outcome
  (progress) and every concrete outcome equals it (determinism), so concrete calls inherit the
  spec's `HasUniqueWritePerm` postconditions; `concreteSplitAtMut_requires_mid_le` shows the body
  panics otherwise;
* `same_tag_split_unsound_control` and `overlapping_reborrowFootprint_write_disables_sibling`:
  `TrustedFnSpec.runNoFootprint` returns both slices with the argument tag (allowing UB-free
  cross-slice aliasing writes), whereas `TrustedFnSpec.run` with disjoint footprints rejects
  cross-slice writes and `TrustedFnSpec.run` with overlapping `&mut` footprints disables the
  sibling reference upon writing the overlap byte.

## 3. Receipts (pass A0)

```bash
anneal-lean-run --mode file --concurrency 1 -- lake env lean theory/Anneal/FuelFreeLoopAndTypedAtLensPrototype.lean
python3 -B -m unittest scripts/test_bench_fuel_free_lens_scaling_proto.py -v
python3 scripts/bench_fuel_free_lens_scaling_proto.py --dry-run
python3 scripts/bench_fuel_free_lens_scaling_proto.py --verify-report
git diff --name-only 2167b83c9bf782c337d7cec99d54249c52f865c9..HEAD
git status --porcelain
```

All six pass at A0: the Lean file elaborates with no output (0 errors, 0 warnings, 217 axiom guards
passing), the unit suite passes, `--dry-run` validates all generated benchmark files in milliseconds,
`--verify-report` matches the embedded receipt, the diff contains exactly the four Track P files,
and the tree is clean.

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
  checked by `rfl`, isolating whether projection alone avoids the blow-up.
* **Measurement.** The prototype is compiled once into a temporary directory as module
  `FuelFreeProtoBench.Prototype` from the byte-identical source (its SHA-256 is recorded). Each
  (family, variant) file runs through `anneal-lean-run --mode file --concurrency 1 -- lake env lean`,
  starts with a discarded warm-up instance, and wraps every instance in a `#measure` command that
  logs elaboration wall-clock and thread-local heartbeats (`Elab.async false`). A global warm-up run
  is discarded, file order rotates across repetitions, and variant order alternates.
  `maxHeartbeats 200000` turns blow-ups into deterministic timeouts; larger `K` of a timed-out
  variant are recorded as `skipped (censored)`.

## 5. Benchmark results

<!-- BENCH:BEGIN -->

Cells: median elaboration wall-clock / median elaboration kilo-heartbeats (`#measure`, `Elab.async false`), over 3 interleaved repetitions after a discarded warm-up; budget `maxHeartbeats 200000`.

#### `local_slots`

| variant | K = 5 | K = 10 | K = 20 | K = 30 |
|---|---|---|---|---|
| `naive_rfl` | 16 ms / 145 k | 109 ms / 1105 k | timeout (> 200 M hb) | skipped (censored) |
| `naive_simp` | 16 ms / 156 k | 24 ms / 245 k | 48 ms / 423 k | 64 ms / 609 k |
| `ablation_projection_rfl` | 27 ms / 249 k | 193 ms / 2140 k | timeout (> 200 M hb) | skipped (censored) |
| `optimized_forcePureEnv` | 15 ms / 137 k | 22 ms / 214 k | 38 ms / 366 k | 55 ms / 525 k |

#### `struct_fields`

| variant | K = 5 | K = 10 | K = 20 | K = 30 |
|---|---|---|---|---|
| `naive_rfl` | 90 ms / 848 k | 2157 ms / 21109 k | timeout (> 200 M hb) | skipped (censored) |
| `naive_simp` | 55 ms / 409 k | 66 ms / 507 k | 90 ms / 695 k | 113 ms / 889 k |
| `optimized_typedAt_lens` | 15 ms / 133 k | 22 ms / 201 k | 37 ms / 338 k | 50 ms / 475 k |

#### `loop_trip`

| variant | K = 5 | K = 10 | K = 20 | K = 30 |
|---|---|---|---|---|
| `naive_fuel_rfl` | 4747 ms / 56665 k | timeout (> 200 M hb) | skipped (censored) | skipped (censored) |
| `naive_fuel_simp` | 317 ms / 1979 k | 743 ms / 4308 k | 2032 ms / 11172 k | 4186 ms / 21063 k |
| `optimized_runCfgToBlock_forRangeUp` | 21 ms / 158 k | 22 ms / 158 k | 22 ms / 158 k | 23 ms / 158 k |

<details><summary>Embedded JSON receipt (verified by <code>--verify-report</code>)</summary>

```json
{
 "cpu_count": 8,
 "file_wall_ms_median": {
  "local_slots/ablation_projection_rfl": 20219,
  "local_slots/naive_rfl": 20106,
  "local_slots/naive_simp": 2697,
  "local_slots/optimized_forcePureEnv": 2694,
  "loop_trip/naive_fuel_rfl": 28639,
  "loop_trip/naive_fuel_simp": 9824,
  "loop_trip/optimized_runCfgToBlock_forRangeUp": 2639,
  "struct_fields/naive_rfl": 27106,
  "struct_fields/naive_simp": 2947,
  "struct_fields/optimized_typedAt_lens": 2644
 },
 "generated_at_utc": "2026-11-13T16:59:15Z",
 "heartbeat_budget": 200000,
 "ks": [
  5,
  10,
  20,
  30
 ],
 "lean_toolchain": "leanprover/lean4:v4.34.1",
 "prototype": "theory/Anneal/FuelFreeLoopAndTypedAtLensPrototype.lean",
 "prototype_compile_ms": 7793,
 "prototype_sha256": "fe530bc8b5fb341d7dd58835e2106e97c7682bd02bf63d21aab73b8feffd409f",
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
   "median_ms": 16,
   "ms_samples": [
    16,
    13,
    16
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
   "median_ms": 109,
   "ms_samples": [
    112,
    91,
    109
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
   "median_ms": 16,
   "ms_samples": [
    16,
    16,
    17
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
   "median_ms": 24,
   "ms_samples": [
    23,
    24,
    29
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
   "median_ms": 48,
   "ms_samples": [
    42,
    61,
    48
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
   "median_ms": 64,
   "ms_samples": [
    58,
    78,
    64
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
   "median_ms": 27,
   "ms_samples": [
    25,
    27,
    32
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
   "median_ms": 193,
   "ms_samples": [
    193,
    181,
    226
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
    137212,
    137212,
    137212
   ],
   "k": 5,
   "kilo_heartbeats": 137,
   "median_ms": 15,
   "ms_samples": [
    15,
    15,
    13
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
   "median_ms": 22,
   "ms_samples": [
    28,
    21,
    22
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
   "median_ms": 38,
   "ms_samples": [
    41,
    38,
    37
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
   "median_ms": 55,
   "ms_samples": [
    57,
    55,
    53
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
   "median_ms": 90,
   "ms_samples": [
    82,
    90,
    93
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
   "median_ms": 2157,
   "ms_samples": [
    1929,
    2157,
    2278
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
   "median_ms": 55,
   "ms_samples": [
    54,
    59,
    55
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
   "median_ms": 66,
   "ms_samples": [
    66,
    68,
    64
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
   "median_ms": 90,
   "ms_samples": [
    83,
    90,
    92
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
   "median_ms": 113,
   "ms_samples": [
    110,
    113,
    115
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
   "median_ms": 15,
   "ms_samples": [
    14,
    15,
    15
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
   "median_ms": 22,
   "ms_samples": [
    25,
    22,
    22
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
   "median_ms": 37,
   "ms_samples": [
    37,
    39,
    35
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
   "median_ms": 50,
   "ms_samples": [
    50,
    54,
    50
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
   "median_ms": 4747,
   "ms_samples": [
    5364,
    4747,
    4669
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
   "median_ms": 317,
   "ms_samples": [
    317,
    400,
    271
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
   "median_ms": 743,
   "ms_samples": [
    743,
    785,
    676
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
   "median_ms": 2032,
   "ms_samples": [
    1833,
    2042,
    2032
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
   "median_ms": 4186,
   "ms_samples": [
    4186,
    4727,
    3881
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
   "median_ms": 21,
   "ms_samples": [
    20,
    26,
    21
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
   "median_ms": 22,
   "ms_samples": [
    22,
    28,
    21
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
   "median_ms": 22,
   "ms_samples": [
    22,
    28,
    19
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
   "median_ms": 23,
   "ms_samples": [
    23,
    32,
    19
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

Interpretation (B1 receipt):

* **Loops.** The fuel-free proof costs 158 k heartbeats at every trip count, while explicit fuel
  grows from 1979 k to 21063 k (K = 5 → 30) under `simp` and needs 56665 k at K = 5 and times out
  from K = 10 under `rfl`.
* **Struct fields.** The `TypedAt` lens proof (133 k → 475 k) is 1.9–3.1× cheaper than byte-list
  `simp` (409 k → 889 k); byte-level `rfl` grows from 848 k to 21109 k and times out from K = 20.
* **Local slots.** After B1's single-pass `setSpine?` fix (replacing A0's two-pass
  `forceSpine? (env.set ...)` traversal) and single-match `forcePureEnvD`, step-wise
  `optimized_forcePureEnv` scales linearly (137 k → 525 k, 15 ms → 55 ms) and **beats** `naive_simp`
  (156 k → 609 k, 16 ms → 64 ms) at every measured `K ∈ {5, 10, 20, 30}`, while plain `rfl`
  (145 k → 1105 k) and end-of-chain projection (249 k → 2140 k, improved 6.8× at K = 10 by removing
  `headD`/`tail` duplication) both time out from K = 20.

## 6. Track A integration mapping

| Live module | Prototype artifact | Track A action |
|---|---|---|
| `MirFuelFree.lean` | `mirStep`, `mirWpConverges_of_wpConverges`, `mirStepsConverges_of_stepsTo`, `mirWpConverges_of_stepsTo_bind`, `runMirToBlock` | Add a `runMirToBlock`-style header stepper next to `MirStepsConverges.step_emit`; reuse the generic `StepsTo` / `FirstHitIn` lemmas |
| `MirLoops.lean` | `forRangeUp_eq_live`, `live_forRangeUp_induction`, `wpConverges_forRangeUp`, `mirWpConverges_forRangeUp`, `live_countToN_mirWpConverges_all_n` | Either replace the well-founded `forRangeUp` by the structural one (kernel-reducible; proven equal) or keep both with `forRangeUp_eq_live` as the bridge |
| `PureMirExec.lean` | `toMirShape`, `hasCfgBackedge_toMirShape`, `inferMinFragment_toMirShape`, `inferMinFragment_refShape`, `fragment_levels_strict` | Route Pillar 1 obligations by `inferMinFragment` (`.pureLoopFree` / `.pureBoundedLoop`) and Pillar 4 obligations to `.treeBorrowsLocal` |
| `MirLiftCore.lean` | `forcePureEnv`, `forceSpine?`, `setSpine?`, `forceSpine?_eq_live`, `applySlotUpdatesForced`, `forcePureEnvSlots_set?` | Use single-pass `setSpine?` (or `forcePureEnv?`) after each `LiftStmt` step (`evalPureStmtNorm`); add the projection and length-mismatch lemmas |
| `ByteCodec.lean` | `TypedAt`, `readTyped`, `writeTyped`, `DisjointSlice`, `laidOutPair`, `typedAt_append_encode`, `typedAt_laidOutPair_iff`, `typedAt_laidOutPair_of_fieldsValid` | Host the relational `TypedAt` and frame rules over the trusted byte primitives; add the `laidOutPair` field-projection lemmas |
| `SepLogicLenses.lean` | `fieldLens`, `subplaceFieldLens_disjoint`, `subplaceFieldLens_of_borrowSubplace_disjointOn`, `structLens_lawful`, `applyFieldWrites_spec`, Tree Borrows model and `TrustedFnSpec` | Instantiate `IndependentLenses` for byte-addressed fields via `BorrowSubplace.disjointOn`; host `TrustedFnSpec.reborrowFootprint` with the pre-release ordering |

## 7. Decision rationale and conditions

**CONDITIONAL GO.** All four pillars are proven end-to-end against the live signatures with
constructive axioms, and after Round B1's `setSpine?` and `mirStep` fixes, the optimized strategy in
**every** benchmark family (`local_slots`, `struct_fields`, `loop_trip`) dominates both `naive_rfl`
and `naive_simp` at every measured size `K ∈ {5, 10, 20, 30}`. Conditions:

1. **`forcePureEnv` must be applied step-wise (`setSpine?` / `forcePureEnv?`), not only at the end
   of an unforced `List.set` chain.** Projection of an already-nested `List.set` chain still incurs
   smart-unfolding blow-up in `Meta.whnf` (row `ablation_projection_rfl`); only forcing the spine at
   each update (`setSpine?` / `applySlotUpdatesForced`) achieves linear scaling and beats `simp`.
2. **Extend `mirStep` with external call handling when lifting `.fullMir` bodies.** Round B1 fixed
   `mirStep` to step across `.switchInt` observation events (`.vis (.inr (.inl (.emit (.event _))))`)
   and verified live `Anneal.MirLoops.countToNBody n` end-to-end; bodies that make external calls
   still require the full `MirTraceWpConverges` / call-spec rules.
3. **Integrate `TrustedFnSpec.reborrowFootprint` with the live `BorrowEntry` table.** Round B1 added
   the explicit permission bijection (`ofLiveTreeBorrowPerm?_toLiveTreeBorrowPerm`,
   `toLiveTreeBorrowPerm_ofLiveTreeBorrowPerm?`) and `BorrowEntry` range/protector projections;
   Track A must wire `TrustedFnSpec.run` into `evalTerminator` call handling.
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
