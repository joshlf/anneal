# Prototype Evaluation Report — `ws-proto-sparse-retag-index-and-batched-vc-narrow`

- **Prototype Branch**: `refs/heads/prototype/ws-proto-sparse-retag-index-and-batched-vc-narrow/ep1-proto-sparse-retag-index-and-batched-vc-narrow`
- **Base `unstable` Commit SHA**: `1e208d1a9d6cce3326f6330ef2aecf942fe7d39d`
- **Paired Track A Workstream**: `ws-sparse-retag-index-and-batched-vc-narrow`
- **Deliverables** (the only files changed vs. base):
  - `theory/Anneal/SparseRetagAndVcNarrowPrototype.lean`
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean`
  - `PROTOTYPE_REPORT.md`
- **Kernel & Axiom Audit** (bottom of the test file, on the final code): `axiom audit passed: 1753 declarations (242 prototype theorems, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 leaked constants, 0 placeholder uses, 1 conditional test lemmas all discharged, 100% theorem reachability from closed test witnesses)`
  - All theorems depend only on `{propext, Quot.sound}`. The audit's self-tests confirm that it flags
    `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, an elaborated `have _ := @thm` placeholder,
    and a test statement that assumes an undischarged hypothesis. Reachability is computed only
    from *closed* test witnesses (no assumed hypotheses other than bounded membership `x ∈ l`).
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean` starts with `import Anneal` +
    `import Anneal.SparseRetagAndVcNarrowPrototype` and elaborates cleanly (no symbol/instance collisions).
- **Overall Recommendation**: **CONDITIONAL GO** — the four mechanisms are formally sound on the
  prototype models; §5 lists what Track A must still prove or measure (three conditions are only
  partially closed).

---

## 1. What Is Proved (theorem names as they exist in the module)

### Part A — `SparseRetagAttrIndex` (`proofs-rs/lean-miri` PR #68)
- `linearScanRetagAttr` mirrors `lean-miri`'s `CompilerRetagOptions.rustcNoWritable`: frame check
  first, then a left-to-right whole-table scan with an `O(M)` duplicate check per row (`O(M²)` per
  query).
- `prepareSparseRetagIndex` builds `NatBitTrie Bool` once at depth
  `adaptiveRetagTrieDepth D = max 12 (D.log2 + 1)`; `natLowBits_inj_of_lt_pow2`,
  `lt_two_pow_adaptiveRetagTrieDepth`, `adaptiveRetagTrieDepth_bitPath_injective`: every valid key
  `< D` has a unique bit path (only valid, distinct keys are inserted, so leaves hold one key; the
  test suite checks a `D = 5000` table where keys `7` and `4103` collide at depth 12 but not at the
  adaptive depth).
- `lookupSparseRetag_eq_linearScan` (all `definitionCount`, `rows`, `id`; error precedence
  included), `frameAbsent_precedes_malformedTable`, `lookupSparseRetag_cert` /
  `lookupSparseRetag_miss_cert`, `SparseDefPathRetagIndex.get?_insert`.
- Operational overlay `evalFnEntryRetagWithSparseAttr` over `Trusted` `evalStmt`:
  `evalFnEntryRetagWithSparseAttr_eq_linear`, `unusedMalformedTable_demand_local`,
  `evalFnEntryRetagWithSparseAttr_implicitWrites_false`,
  `evalFnEntryRetagWithSparseAttr_rustcNoWritable_true`,
  `applyImplicitWriteUpgrade_of_no_fresh_child` (only the freshly created child is written),
  `fnEntryRetagPerm_mut` (V2026_06_01 creates every `&mut` fn-entry child `.reservedFrz false`), and
  `canary_implicitWrite_treeBorrows_full` (the implicit child write runs the `Trusted` write
  transition: `treeBorrowAncestorsChildAccessUB .write`, `hasProtectedTreeWriteConflict`,
  `invalidateTreeBorrowsAtProj`).

### Part B — `BatchedVcConeNarrowCert` + `hoistTraitImpls` + `@[irreducible] coerceValueAt`
- One Boolean checker per hoisting policy, each a single `decide +kernel`:
  `checkBatchedVcConeNarrowCert` (`hoistTraitImpls fullCallees extra`) and
  `checkBatchedVcConeNarrowCertMask` (`hoistMaskTraitImpls`: hoist only the *dropped* bodies' entries,
  for the `rustc-capture` layout where kept impl bodies carry their own `TraitImplEntry`;
  `hoistMaskTraitImpls_eq_hoistTraitImpls`: it is `hoistTraitImpls` applied to the dropped bodies);
  `BatchedVcConeNarrowCert.ofCheck` / `.ofCheckMask` derive **every** certificate field.
- First-match preservation without `CapturedMir` equality: `checkMaskKeepsFirstMatch` +
  `calleesAgreeOn_selectByMask`; trait-record preservation: `traitFilter_hoist_eq`,
  `traitFilter_hoistMask_eq` (via `checkMaskTraitPartition`).
- `computeBatchedVcNarrowCert` / `collectTraitConeBodies`; `selectByMask_coneMask`.
- Trait-aware congruence: `lookupCallee_eq_of_traitConeAgree`, `evalTerminator_withCalleesAndTraits`,
  `stepMirFn_withCalleesAndTraits`, `coneReach_of_closedInvTrait`.
- Core theorems: `runMirExecBounded_narrow_of_batchedCert`, `wpMirExecSym_narrow_of_batchedCert`,
  `vcMirWithCallees_narrow_of_batchedCert` (contract-aware WP `wpMirExecExt`, with
  `wpMirExecExt_nil_iff`, `wpMirExecExt_of_wpMirExecSym`, `wpMirExecExt_of_run`,
  `post_of_wpMirExecExt_run`).
- `stepMirFn_extCallInCone` / `coneSummary?_eq_of_stepMirFn_extCall`: every external call emitted
  from a cone-safe state targets a cone path, so cone filtering of summaries loses nothing there.
- `canary_externalSummary_vc` (the VC holds with the cone summary, fails without it),
  `canary_coercedExternalSummary_vc` (a contract stated through sealed `coerceValueAt`).
- `coerceValueAt` is `@[irreducible]` (meta-level opacity audit) with `coerceValueAt_u32`,
  `coerceValueAt_bool`, `coerceValueAt_ref`, `coerceValueAt_adt_exact`, `coerceValueAt_idempotent`.

### Part C — `DemandCallerLocationEnv` (`proofs-rs/lean-miri` PR #67 Schema 15)
- `FrameLocMeta` (`callSitePos : Option SourceExpansionPos`), `CallerLocationSite.resolve`
  (`find_closest_untracked_caller_location`, policy of the crate owning the span),
  `resolveCallerLocationAux_eq_topDown`.
- `evalDemandCallerLocation` draws ids from `nextFreshGlobalAndTagId = max nextAllocId nextTag` and
  advances both counters; `evalDemandCallerLocation_borrowAware_spec` /
  `canary_demandLocation_borrowTag_disjoint`: the new pointer is not shadowed by any live borrow tag.
- General theorems over **all** call-site tables, **all** traces and all 8 policies (reads through
  `readLocationFromGlobals`): `evalDemandCallerLocation_spec`, `runDemandCallerLocationTrace_spec`,
  `eagerInitAux_spec`, `demandCallerLocation_bisim_eager`, `demandCallerLocation_no_call_zero_allocs`,
  `eagerCallerLocation_clutter`, `allocRenamingRel_of_readLocations`.
- `evalStmt_pure_memory_eq` / `normalStmtStep_eq_raw_of_pure`: on pure statements over frame-free
  memory, `evalStmt` leaves `Memory` unchanged (so `normalStmtStep`'s frame re-assertion is a no-op).

### Part D — `LazyWriteChain` & total shifts
- `mkLazyWrite w` (static width, `O(1)` per write); `eval_mkLazyWrite`, `eval_mkEagerWrite`,
  `eval_mkLazyRead`.
- Step counts on instrumented copies of the implementations (`mkLazyWriteCounted_fst`,
  `stripShadowedWritesCounted_fst`, `stripShadowedWritesCounted_snd`, `mkEagerWriteCounted_fst`,
  `lazyDistinctChainCounted_fst`, `eagerDistinctChainCounted_fst`, `lazyReadSpineCounted_fst`,
  `mkLazyReadCounted_fst`): `lazyWriteChain_distinctAddrs_steps_eq_N` (`N`),
  `eagerWriteChain_distinctAddrs_steps_quadratic` (`N(N+1)/2`), `mkLazyReadCounted_hit_top`,
  `buildLazyDistinctChain_eq_eager`.
- `bvShlSafe_eq`, `bvLshrSafe_eq`, `bvAshrSafe_eq`, `shiftLeftBitsSafe_eq`,
  `shiftRightUnsignedBitsSafe_eq` (canonical inputs), `arithmeticShrBitsSafe_eq`,
  `canary_wideShift_two_pow_64`.

---

## 2. Benchmarks (measured by `tests/mir/SparseRetagAndVcNarrowProtoTests.lean`)

Methodology: both arms of every comparison use the same mechanism — `decide +kernel` for the
execution/certificate tables, elaborator `rfl` for both VC-discharge arms, and the same `simp only`
script shape for both coercion arms. `IO.getNumHeartbeats` deltas are deterministic; wall-clock
(`IO.monoNanosNow`) is from the final receipt run and is noisy. Optimized arms include their one-time
costs (index preparation, certificate checking, narrowing computation) unless labeled otherwise.

### 2.1 Part A — linear oracle vs. sparse index (`definitionCount = 512`)

| Rows `M` | Linear oracle, 1 query | Sparse: prepare + 1 query | Sparse: prepare + `M` queries |
| :--- | ---: | ---: | ---: |
| 16 | `67,541` hb (`9.6` ms) | `146,852` hb (`22.8` ms) | `438,921` hb (`75.6` ms) |
| 64 | `577,569` hb (`84.0` ms) | `634,328` hb (`109.8` ms) | `1,752,176` hb (`323.0` ms) |
| 128 | `2,117,815` hb (`341.6` ms) | `1,420,921` hb (`249.7` ms) | `3,559,290` hb (`692.5` ms) |
| 256 | `8,147,437` hb (`1,485.2` ms) | `3,226,248` hb (`592.9` ms) | `7,285,268` hb (`1,488.4` ms) |

- The linear oracle's growth approaches 4× per doubling of `M` (3.7× from 64 to 128, 3.8× from 128 to
  256). Including preparation, the sparse index is slower
  for one query at `M = 16` (2.17× the linear cost), roughly even at `M = 64`, and faster at
  `M = 128` (1.49×) and `M = 256` (2.53×).
- All `256` sparse queries at `M = 256` (`7,285,268` hb) cost less than **one**
  linear-oracle query (`8,147,437` hb). (All 256 linear queries were not measured.)

### 2.2 Part B — full callee table vs. certified narrowing (trait call through `TraitImplEntry`)

| Callees `M` | Full table run | Cert check (compute cone + mask, 1 `decide`) | Narrowed run (narrowing computed in-kernel) | Narrowed run (cached narrowed table) |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `562,731` hb (`84.9` ms) | `1,623,911` hb (`226.6` ms) | `588,031` hb (`87.5` ms) | `451,995` hb (`69.3` ms) |
| 64 | `670,407` hb (`97.1` ms) | `2,066,862` hb (`378.5` ms) | `781,843` hb (`274.3` ms) | `452,002` hb (`187.3` ms) |
| 128 | `813,931` hb (`278.5` ms) | `2,657,364` hb (`746.3` ms) | `1,040,244` hb (`160.6` ms) | `451,991` hb (`70.9` ms) |

- The cached arm's literal table is proved equal (`rfl`) to the computed narrowing
  (`cachedNarrow_eq_computed_*`). Steady state at `M = 128`: 1.80× fewer heartbeats than the
  full table; recomputing the narrowing per run is slower than the full table, and the one-time
  certificate costs ~3× a full run.
- VC discharge by elaborator `rfl` (concrete inputs, `M = 128`; this is *not* a symbolic VC):
  full table `3,861,964` hb (`377.1` ms) vs. cached narrowed table `2,160,519` hb (`212.9` ms)
  (1.79×).
- Coercion (`∀ bits`, 16 chained coercions, the same `simp only` script shape): sealed
  `coerceValueAt` rewritten by `coerceValueAt_u32` `257,257` hb (`26.6` ms) vs. a reducible copy
  unfolded by `dsimp`/`simp` `447,062` hb (`36.1` ms) (1.74×).

### 2.3 Part C — eager pre-allocation vs. demand-time `Location` (same trace in both worlds)

| Sites `S` | Eager, non-panicking (8 stmts) | Demand, non-panicking | Eager, panicking (1 invocation) | Demand, panicking |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `129,855` hb (`20.2` ms) | `52,890` hb (`7.1` ms) | `237,094` hb (`35.1` ms) | `196,792` hb (`25.5` ms) |
| 64 | `761,966` hb (`110.2` ms) | `52,886` hb (`6.9` ms) | `394,352` hb (`50.8` ms) | `196,795` hb (`24.5` ms) |
| 128 | `2,507,956` hb (`370.3` ms) | `52,913` hb (`7.1` ms) | `625,521` hb (`81.1` ms) | `196,810` hb (`25.8` ms) |

- Demand cost is independent of `S`; the eager arm materializes `S + 1` globals (checked). Its
  super-linear growth is partly an artifact of the list-based `Memory.globals` model.

### 2.4 Part D — eager vs. lazy distinct-address write chains (`cap = 128`, read of the last write)

| Writes `N` | Eager (`mkEagerWrite`) | Lazy (`mkLazyWrite`) | Proved spine inspections (eager / lazy) |
| :--- | ---: | ---: | ---: |
| 16 | `121,652` hb (`16.4` ms) | `60,061` hb (`6.7` ms) | 136 / 16 |
| 64 | `1,226,882` hb (`196.8` ms) | `113,425` hb (`20.5` ms) | 2080 / 64 |
| 128 | `4,728,542` hb (`906.7` ms) | `183,994` hb (`26.2` ms) | 8256 / 128 |

- Wide-shift canary (`shift = 2^64`, six safe shifts, one `decide +kernel`): `140,110` hb (`9.9` ms).

---

## 3. Canaries (all kernel-checked, all closed — no assumed hypotheses)

- **Part A**: hit/miss certificates on the prepared index; every `RetagAttrErr`; adaptive depth on a
  `D = 5000` table (`test_partA_adaptive_depth`); implicit write activates the fresh child for
  `rustcNoWritable = false` (real `evalStmt` retag) but not under `#[rustc_no_writable]`; `.frozen`
  ancestor ⇒ `.ub`, foreign `.frozen` sibling ⇒ `.disabled`; ZST `&mut ()` retag leaves `borrows`
  untouched (the `[adv A0]` overlay, kept as `applyImplicitWriteUpgradeLegacyA0`, corrupted it).
- **Part B**: `canary_naiveNarrow_breaks_trait_dispatch`,
  `canary_traitDispatch_preserved_under_batchedVcNarrow`, `canary_duplicateShadow_rejected` (the
  `[adv A0]` metadata check, kept as `checkCalleesAgreeOnLegacyA0`, accepts it),
  `canary_externalShadowsInternal_rejected`, `canary_missingTraitImplBody_rejected`,
  `canary_keptBodyWithTraitImpl_accepted` + `test_partB_rustcStyle_narrow_run` (the mask-aware
  certificate preserves the exact result `31`), `canary_externalSummary_vc`,
  `canary_coercedExternalSummary_vc`, `test_partB_extCallInCone` (the real external call of
  `protoExtCallRootMir` from a *proved* cone-safe state).
- **Part C**: `demandCallerLocation_filename_dedup`, `canary_demandLocation_borrowTag_disjoint`,
  `trackCaller_span_owner_policy`, `trackCaller_stops_at_nonTrackCaller_frame`, bisimulation for all
  8 policies on a trace with a repeated site, explicit `AllocRenamingRel`, `test_partC_stmt_pure_memory`.
- **Part D**: OOB fold, same-address collapse, distinct-address `O(1)` stop, top-write read in one
  step, `2^64` shift.

---

## 4. Adversarial History

- `[adv A0]` (agent-a): initial implementation.
- `[adv B1]` (agent-b): made the VC's external summaries non-vacuous; replaced the metadata-only
  callee check with mask narrowing and a single sound checker; added the missing
  `computeBatchedVcNarrowCert`; fixed `nextAllocId` reuse, head-entry corruption in the implicit-write
  overlay, the single-instance bisimulation, implementation-unrelated step theorems, `have _ := @thm`
  reachability placeholders, unfair benchmarks, and report fabrications.
- `[adv A1]` (agent-a): adaptive trie depth; `Trusted` write transition for implicit writes; masked
  hoisting for kept impl bodies; borrow-aware `Location` ids; `stepMirFn_extCallInCone`; pure-statement
  frame theorem; read-step counter.
- `[adv B2]` (agent-b) fixed in A1: test instances that proved `3 = 3` / `7 = 7` to "reach" the
  injectivity theorems; tests whose statements *assumed* the very hypotheses they should discharge
  (`h_safe`, `h_step`, `hstep`, and two of B1's own); a "symbolic VC" benchmark whose `∀ x` was
  never read by the program (now relabeled elaborator-`rfl` discharge on concrete inputs); a
  coercion benchmark comparing a pre-proved lemma against `simp` (now the same `simp` script shape);
  the false claim `fnEntryRetagPerm .mut ty = .cell` and the spec-unfaithful `.cell` exception
  (removed; V2026_08_01 / MiniRust activate every protected `&mut` under implicit writes); the
  overclaimed "GO / all conditions closed". The audit now rejects undischarged conditional tests.

---

## 5. Conditions for Track A Promotion

1. **`allocId` / borrow-tag namespace — partially closed.** A fresh `Location` avoids all live tags
   and tags drawn later from the advanced `nextTag`; the trace-level bisimulation still reads through
   `readLocationFromGlobals`, because statement-level tag monotonicity (`evalStmt` only draws tags
   from `nextTag`) is unproved.
2. **Implicit writes — closed for the overlay's scope.** The fresh child is written with the
   `Trusted` write transition and UB checks; V2026_06_01 has no native implicit writes, so this
   remains an overlay to be reconciled with V2026_08_01's `initProtectedReborrowPerm`.
3. **Statement frame in Part C — partially closed.** Proved for pure statements on frame-free
   memory; for general statements `normalStmtStep` still re-asserts `globals` / `nextAllocId`.
4. **Trie depth — closed** (adaptive depth + bit-path injectivity, concretely exercised at `D = 5000`).
5. **External calls — partially closed.** `stepMirFn_extCallInCone` covers calls emitted from
   cone-safe states; after an external call the answer supplies the memory, so whole-execution use
   of unfiltered summaries remains unproved and the VC keeps filtering summaries by cone.
6. **Hoisting — closed for partitionable layouts.** A cone path whose `TraitImplEntry`s live in both
   kept and dropped bodies still fails closed.
7. **Symbolic payoff — open.** Neither cone narrowing nor coercion sealing has been measured on
   symbolic VCs (§2.2 measures concrete-input discharge only).

### Proposed 2-Episode Track A Plan
1. `ep1`: Part A and Part D into `theory/Anneal/SparseRetagAndVcNarrow.lean` (conditions 2, 4).
2. `ep2`: Part B and Part C (conditions 1, 3, 5–7), exported from `theory/Anneal.lean`, with this
   test suite as the regression gate.
