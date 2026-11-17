# Prototype Evaluation Report — `ws-proto-sparse-retag-index-and-batched-vc-narrow`

- **Prototype Branch**: `refs/heads/prototype/ws-proto-sparse-retag-index-and-batched-vc-narrow/ep1-proto-sparse-retag-index-and-batched-vc-narrow`
- **Base `unstable` Commit SHA**: `1e208d1a9d6cce3326f6330ef2aecf942fe7d39d`
- **Paired Track A Workstream**: `ws-sparse-retag-index-and-batched-vc-narrow`
- **Deliverables** (the only files changed vs. base):
  - `theory/Anneal/SparseRetagAndVcNarrowPrototype.lean`
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean`
  - `PROTOTYPE_REPORT.md`
- **Kernel & Axiom Audit** (bottom of the test file, on the final code): `axiom audit passed: 2061 declarations (336 prototype theorems, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 leaked constants, 0 placeholder uses, 4 conditional test lemmas all discharged, 100% theorem reachability from closed test witnesses)`
  - All theorems depend only on `{propext, Quot.sound}`. The audit's self-tests confirm that it flags
    `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, an elaborated `have _ := @thm` placeholder,
    and a test statement that assumes an undischarged hypothesis. Reachability is computed only
    from *closed* test witnesses (no assumed hypotheses other than bounded membership `x ∈ l`).
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean` starts with `import Anneal` +
    `import Anneal.SparseRetagAndVcNarrowPrototype` and elaborates cleanly (no symbol/instance collisions).
- **Overall Recommendation**: **CONDITIONAL GO**. All four mechanisms are kernel-checked (`0 sorry`,
  `0 Classical.choice`) over `Trusted.Rustc.V2026_06_01` and `Anneal.MirLiftCore`. Conditions 2, 4
  and 6 in §5 are closed. Conditions 1 and 3 are closed only within the statement-trace model.
  Condition 5 (external calls) is closed only per step. Condition 7 (symbolic payoff) is measured
  but pays off only when one certificate is reused by at least 3 VCs.

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
- Three Boolean certificate checkers (each a single `decide +kernel`), all deriving
  `BatchedVcConeNarrowCert`:
  1. `checkBatchedVcConeNarrowCert` + `BatchedVcConeNarrowCert.ofCheck` (`hoistTraitImpls fullCallees extra`
     when kept bodies carry no cone `TraitImplEntry`s),
  2. `checkBatchedVcConeNarrowCertMask` + `BatchedVcConeNarrowCert.ofCheckMask`
     (`hoistMaskTraitImpls`: hoist only the *dropped* bodies' entries when cone traits do not
     straddle kept and dropped bodies; `hoistMaskTraitImpls_eq_hoistTraitImpls`),
  3. `checkBatchedVcConeNarrowCertGeneral` + `BatchedVcConeNarrowCert.ofCheckGeneral`
     (`hoistTraitImpls fullCallees extra` paired with `selectByMask fullCallees mask` for **every**
     keep-mask `mask`, including mixed partitions where the same cone trait has `TraitImplEntry`s in
     both kept and dropped bodies): proved via `collectMatchingTraitImpls_append_of_subset`,
     `TraitFilterCovers`, `hasTraitImplForDefPath_eq_of_traitFilterCovers`,
     `collectMatchingTraitImpls_eq_of_traitFilterCovers`, and `traitFilterCovers_hoist_selectByMask`
     (exploiting `upsertMatchingTraitImpl`'s deduplication by `entry.implPath` without requiring
     `DecidableEq RigidTy`), and witnessed by `canary_mixedTraitPartition_accepted`.
- First-match preservation without `CapturedMir` equality: `checkMaskKeepsFirstMatch` +
  `calleesAgreeOn_selectByMask`; trait-record preservation: `traitFilter_hoist_eq`,
  `traitFilter_hoistMask_eq`, `traitFilterCovers_hoist_selectByMask`.
- `computeBatchedVcNarrowCert` / `collectTraitConeBodies`; `selectByMask_coneMask`.
- Trait-aware congruence: `lookupCallee_eq_of_traitFilterCovers`, `lookupCallee_eq_of_traitConeAgree`,
  `lookupCallee_eq_of_batchedCert`, `evalTerminator_withCalleesAndTraits`,
  `stepMirFn_withCalleesAndTraits`, `coneReach_of_closedInvTrait`.
- Core theorems: `runMirExecBounded_narrow_of_batchedCert`, `wpMirExecSym_narrow_of_batchedCert`,
  `vcMirWithCallees_narrow_of_batchedCert` (contract-aware WP `wpMirExecExt`, with
  `wpMirExecExt_nil_iff`, `wpMirExecExt_of_wpMirExecSym`, `wpMirExecExt_of_run`,
  `post_of_wpMirExecExt_run`).
- External-call cone safety across single and multiple calls:
  `stepMirFn_extCallInCone` / `coneSummary?_eq_of_stepMirFn_extCall` (every external call emitted
  from a cone-safe state targets a cone path), plus `AnsPreservesCodeFrame`,
  `closedInvPoly_resumeExternalCall`, `stepConeSafeTrait_of_resumeExternalCall` (any external answer
  preserving `callees`, `traitImpls`, `activeCallee`, and `CallerBodiesEq` preserves `ClosedInvPoly`
  and `StepConeSafeTrait` across `resumeExternalCall`), and `canary_twoExternalCalls_vc` (2-call
  root body `protoTwoExtCallsRootMir` calling `ext::seed` then `ext::add_twenty`).
  `closedInvPoly_applyUnwindAction`, `closedInvPoly_resumeExternalDivergingCall`,
  `stepConeSafeTrait_of_resumeExternalDivergingCall`, and `canary_divergingExternalCall_coneSafe` extend
  this to diverging external calls (`call ... -> !`, `resumeExternalDivergingCall`). External tail
  calls (`resumeExternalTailCall`) are not covered.
- Cone filtering is conservative (sound): `coneSummary?_mono` and `wpMirExecExt_mono_cone` prove that
  trusting summaries on a larger cone only weakens the contract-aware WP, for all fuel, states,
  contracts and summary environments. The converse (filtering loses nothing) is proved only per
  step: see §5, condition 5.
- `canary_externalSummary_vc`, `canary_coercedExternalSummary_vc`, `canary_twoExternalCalls_vc`.
- Symbolic VC over polymorphic and trait-dispatched calls: `symTrait_vc_narrow_of_lt` (for every
  input `n` with `n + 31 < 2^32`, i.e. the whole non-overflowing `u32` range, `n` flows through
  `sym_poly::<u32>(_1)` (`AddUnchecked(_1, 7)`) and `<Circle as Area>::area(_0)`
  (`AddUnchecked(_1, 24)`) and the root returns `n + 31 : u32`, on the narrowed and the full table),
  its corollary `symTrait_vc_narrow` (`x % 1000`, used by the benchmarks), and the overflow canary
  `symTrait_vc_overflow_fails` (at `n = 4294967290` the first `AddUnchecked` is UB and the VC is false
  on both tables, so the bound cannot be dropped). Supporting lemmas: `wpMirExecExt_step_tau`,
  `wpMirExecExt_step_ret`, `wpMirExecExt_inv_tau`, `not_wpMirExecExt_of_fail`,
  `stepMirState_assign_local`, `evalRvalue_addUnchecked_u32`. A meta-level `isDefEq` audit checks
  that the `Nat.ble` overflow guards do not reduce by `rfl` on a free input.
- `coerceValueAt` is `@[irreducible]` (meta-level opacity audit) with `coerceValueAt_u32`,
  `coerceValueAt_bool`, `coerceValueAt_ref`, `coerceValueAt_adt_exact`, `coerceValueAt_idempotent`.

### Part C — `DemandCallerLocationEnv` (`proofs-rs/lean-miri` PR #67 Schema 15)
- `FrameLocMeta` (`callSitePos : Option SourceExpansionPos`), `CallerLocationSite.resolve`
  (`find_closest_untracked_caller_location`, policy of the crate owning the span),
  `resolveCallerLocationAux_eq_topDown`.
- `evalDemandCallerLocation` draws ids from `nextFreshGlobalAndTagId = max nextAllocId nextTag` and
  advances both counters; `evalDemandCallerLocation_borrowAware_spec` /
  `canary_demandLocation_borrowTag_disjoint`: the new pointer is not shadowed by any live borrow tag.
- General borrow-tag monotonicity and statement memory frame on **arbitrary** `Memory` (with live
  borrows and active protectors):
  - Tag preservation across all `Trusted` borrow transformers: `map_tag_disableLocalBorrows`,
    `map_tag_attachBorrowProtector`, `map_tag_invalidateConflictingBorrows`,
    `map_tag_invalidateConflictingBorrowsAtProj`, `map_tag_invalidateTreeBorrowsAtProj`,
    `map_tag_freezeTreeBorrowsOnReadAtProj`, `map_tag_invalidateDerefWriteBorrows`,
    `map_tag_invalidateDerefWriteBorrowsWithLayouts`.
  - `MemBorrowMonotone`, `isLocalRefOrPureRvalue` (all `isBorrowFreePureRvalue` rvalues plus local
    stack reference creation `Rvalue.ref borrowKind place`), `isBorrowMonotoneStmt` (covering
    `.nop`, `.coverage`, `.constEvalCounter`, `.backwardIncompatibleDropHint`, `.placeMention`,
    `.storageLive`, `.storageDead`, `.deinit`, all `.retag` variants `.fnEntry`/`.default`/`.twoPhase`/`.raw`,
    all `.setDiscriminant` variants, `.intrinsic (.assume _)`, and `.assign` for all
    `isLocalRefOrPureRvalue` rvalues).
  - `evalRvalue_localRefOrPure_borrowMonotone`, `evalStmt_borrowMonotone_frame`,
    `normalStmtStep_eq_raw_of_borrowMonotone` (`normalStmtStep` equals the raw `evalStmt` transition
    for all `isBorrowMonotoneStmt` statements on arbitrary `Memory`), and `normalStmtStep_borrowMonotone`.
- General trace-level theorems over **all** call-site tables, **all** traces, and all 8 policies:
  - Through `readLocationFromGlobals`: `evalDemandCallerLocation_spec`,
    `runDemandCallerLocationTrace_spec`, `eagerInitAux_spec`, `demandCallerLocation_bisim_eager`,
    `demandCallerLocation_no_call_zero_allocs`, `eagerCallerLocation_clutter`,
    `allocRenamingRel_of_readLocations`.
  - Through borrow-aware `readLocationsBorrowAware` (`lookupBorrow` before `lookupGlobalAlloc`) across
    any `traceBorrowMonotone` trace (including traces that mint new stack borrow tags via `Rvalue.ref`
    and `StatementKind.retag` both before and after `caller_location`):
    `runDemandCallerLocationTrace_borrow_monotone`, `eagerInitAux_borrow_monotone`,
    `runEagerCallerLocationTrace_borrow_monotone`, `runDemandCallerLocationTrace_borrowAware_spec`,
    and `demandCallerLocation_bisim_eager_borrowAware` (exercised on `protoBorrowMonotoneTrace` in
    `test_partC_borrowMonotone_and_trace_borrowAware`).

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

Methodology: both arms of every comparison use the same mechanism:
- `decide +kernel` for the execution and certificate tables;
- elaborator `rfl` for both concrete VC-discharge arms;
- the identical step-by-step script (`wpMirExecExt_step_tau` + `stepMirState_assign_local` +
  `evalRvalue_addUnchecked_u32` + `omega`) for both symbolic `∀ x : Nat` VC arms;
- the same `simp only` script shape for both coercion arms.

`IO.getNumHeartbeats` deltas are deterministic. Wall-clock times (`IO.monoNanosNow`) come from the
final receipt run and are noisy. Optimized arms include their one-time costs (index preparation,
certificate checking, narrowing computation) unless labeled otherwise.

### 2.1 Part A — linear oracle vs. sparse index (`definitionCount = 512`)

| Rows `M` | Linear oracle, 1 query | Sparse: prepare + 1 query | Sparse: prepare + `M` queries |
| :--- | ---: | ---: | ---: |
| 16 | `67,541` hb (`9.9` ms) | `146,852` hb (`24.5` ms) | `438,921` hb (`74.6` ms) |
| 64 | `577,569` hb (`82.6` ms) | `634,328` hb (`109.9` ms) | `1,752,176` hb (`314.9` ms) |
| 128 | `2,117,815` hb (`319.8` ms) | `1,420,921` hb (`245.0` ms) | `3,559,290` hb (`697.4` ms) |
| 256 | `8,147,437` hb (`1,454.3` ms) | `3,226,248` hb (`587.1` ms) | `7,285,268` hb (`1,465.8` ms) |

- The linear oracle's cost grows by 3.67× from `M = 64` to `M = 128` and by
  3.85× from `M = 128` to `M = 256`, approaching 4× per doubling.
- Including preparation, the sparse index is slower than the linear oracle for one query at `M = 16`
  (2.17× the linear cost) and roughly even at `M = 64`. It is faster at `M = 128`
  (1.49×) and at `M = 256` (2.53×).
- All `256` sparse queries at `M = 256` (`7,285,268` hb) cost fewer heartbeats
  than **one** linear-oracle query (`8,147,437` hb). (All 256 linear queries were not
  measured.)

### 2.2 Part B — full callee table vs. certified narrowing (trait call through `TraitImplEntry`)

| Callees `M` | Full table run | Cert check (compute cone + mask, 1 `decide`) | Narrowed run (narrowing computed in-kernel) | Narrowed run (cached narrowed table) |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `562,758` hb (`291.6` ms) | `1,623,926` hb (`299.1` ms) | `588,022` hb (`117.4` ms) | `452,005` hb (`81.5` ms) |
| 64 | `670,422` hb (`113.4` ms) | `2,066,840` hb (`353.5` ms) | `781,850` hb (`272.1` ms) | `452,022` hb (`116.4` ms) |
| 128 | `813,906` hb (`209.7` ms) | `2,657,390` hb (`868.8` ms) | `1,040,243` hb (`182.6` ms) | `452,006` hb (`95.8` ms) |

- The cached arm's literal table is proved equal (`rfl`) to the computed narrowing
  (`cachedNarrow_eq_computed_*`).
- Steady state at `M = 128`: the cached narrowed run uses 1.80× fewer heartbeats than the
  full table. Recomputing the narrowing on every run is slower than the full table. The one-time
  certificate costs 3.26× a full run.
- Concrete VC discharge by elaborator `rfl` (`M = 128`; *not* a symbolic VC): full table
  `3,861,409` hb (`535.8` ms) vs. cached narrowed table `2,160,657` hb (`368.7` ms)
  (1.79×).
- Symbolic VC (`∀ x : Nat`, `symTraitRootMir`, `M = 128`, identical tactic script on both arms):

  | Full table | Cached narrowed table | One-time certificate (`PartB_symVC_cert_M128`) |
  | ---: | ---: | ---: |
  | `5,779,767` hb (`839.7` ms) | `4,578,273` hb (`694.5` ms) | `2,681,868` hb (`1,002.1` ms) |

  - Per VC, the narrowed table saves `1,201,494` hb (1.26×).
    `symCachedNarrow_eq_computed_128` proves the cached table is the certified narrowing.
    `test_partB_symVC_transfer_128` turns the narrowed-table proof plus the certificate into the
    full-table VC.
  - The certificate costs 2.23× the per-VC saving. Certifying and proving a single VC
    on the narrowed table therefore costs `7,260,141` hb, versus `5,779,767` hb
    on the full table.
  - Narrowing pays off only when one certificate is shared by at least 3 VCs over the
    same cone.
- Coercion (`∀ bits`, 16 chained coercions, the same `simp only` script shape): sealed
  `coerceValueAt` rewritten by `coerceValueAt_u32` `257,291` hb (`31.0` ms) vs. a reducible copy
  unfolded by `dsimp`/`simp` `447,046` hb (`35.4` ms) (1.74×).

### 2.3 Part C — eager pre-allocation vs. demand-time `Location` (same trace in both worlds)

| Sites `S` | Eager, non-panicking (8 stmts) | Demand, non-panicking | Eager, panicking (1 invocation) | Demand, panicking |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `129,854` hb (`30.2` ms) | `52,890` hb (`9.2` ms) | `237,108` hb (`48.2` ms) | `196,797` hb (`38.0` ms) |
| 64 | `761,966` hb (`131.6` ms) | `52,906` hb (`8.3` ms) | `394,373` hb (`72.2` ms) | `196,799` hb (`37.0` ms) |
| 128 | `2,507,965` hb (`694.1` ms) | `52,912` hb (`12.4` ms) | `625,591` hb (`106.6` ms) | `196,805` hb (`27.1` ms) |

- Demand cost is independent of `S`; the eager arm materializes `S + 1` globals (checked). Its
  super-linear growth is partly an artifact of the list-based `Memory.globals` model.

### 2.4 Part D — eager vs. lazy distinct-address write chains (`cap = 128`, read of the last write)

| Writes `N` | Eager (`mkEagerWrite`) | Lazy (`mkLazyWrite`) | Proved spine inspections (eager / lazy) |
| :--- | ---: | ---: | ---: |
| 16 | `121,677` hb (`17.3` ms) | `60,065` hb (`8.5` ms) | 136 / 16 |
| 64 | `1,226,871` hb (`240.3` ms) | `113,386` hb (`19.1` ms) | 2080 / 64 |
| 128 | `4,728,562` hb (`1,089.0` ms) | `184,036` hb (`47.2` ms) | 8256 / 128 |

- Wide-shift canary (`shift = 2^64`, six safe shifts, one `decide +kernel`): `140,199` hb (`11.3` ms).

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
  `canary_keptBodyWithTraitImpl_accepted` + `test_partB_rustcStyle_narrow_run`,
  `canary_mixedTraitPartition_accepted` + `test_partB_mixed_trait_partition` (mixed keep/drop
  partition where both `checkKeptCarryNoConeTraitImpls` and `checkMaskTraitPartition` are `false`,
  certified by `BatchedVcConeNarrowCert.ofCheckGeneral`), `canary_externalSummary_vc`,
  `canary_coercedExternalSummary_vc`, `test_partB_extCallInCone`,
  `canary_twoExternalCalls_vc` + `test_partB_two_external_calls` (cone safety preserved across
  `resumeExternalCall` to a second external call), `canary_divergingExternalCall_coneSafe` +
  `test_partB_diverging_external_call` (cleanup-pad state after a panicking diverging external call
  is cone-safe; a normal return from it is UB), `test_partB_cone_filter_conservative`,
  `symTrait_vc_narrow` + `test_partB_symbolic_trait_vc` (symbolic `∀ x : Nat` VC over polymorphic +
  trait-dispatched `AddUnchecked` calls), `test_partB_symbolic_vc_range` (largest admissible input
  `2^32 - 32`; overflow canary at `4294967290`), and `test_partB_symVC_transfer_128` (the symbolic VC
  on the full 128-entry table obtained from the narrowed-table proof plus the one-time certificate).
- **Part C**: `demandCallerLocation_filename_dedup`, `canary_demandLocation_borrowTag_disjoint`,
  `trackCaller_span_owner_policy`, `trackCaller_stops_at_nonTrackCaller_frame`, bisimulation for all
  8 policies on a trace with a repeated site, explicit `AllocRenamingRel`,
  `test_partC_stmt_pure_memory`, and `test_partC_borrowMonotone_and_trace_borrowAware` (full
  borrow-aware bisimulation through `readLocationsBorrowAware` across `protoBorrowMonotoneTrace`,
  which mints stack borrows via `Rvalue.ref` and `StatementKind.retag` both before and after
  `caller_location`), and `test_partC_borrowAware_needed` (on that trace an allocator using only
  `nextAllocId` would give the `Location` the live borrow tag `1`).
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
- `[adv B2]` (agent-b): replaced vacuous `3 = 3` / `7 = 7` reachability tests with a `D = 5000`
  adaptive-depth test; discharged all conditional test hypotheses and added `isConditionalThm` to the
  audit; removed the false `.cell` special case in `applyImplicitWriteUpgrade` and proved
  `fnEntryRetagPerm_mut`; relabeled the concrete `rfl` VC and `simp` coercion benchmarks; and
  documented the remaining conditions.
- `[adv A2]` (agent-a):
  1. Proved `collectMatchingTraitImpls_append_of_subset` and `traitFilterCovers_hoist_selectByMask`
     and added `checkBatchedVcConeNarrowCertGeneral` + `BatchedVcConeNarrowCert.ofCheckGeneral` +
     `canary_mixedTraitPartition_accepted`, removing the partitionability restriction on trait hoisting.
  2. Proved `closedInvPoly_resumeExternalCall` and `stepConeSafeTrait_of_resumeExternalCall` under
     `AnsPreservesCodeFrame` and added `canary_twoExternalCalls_vc` over a 2-call external root body.
  3. Added `symTrait_vc_narrow` (`∀ x : Nat`) and `PartB_symVC_{full,narrowCached}_M128` over
     polymorphic + trait-dispatched `AddUnchecked` calls with a meta-level `isDefEq` non-reducibility
     audit.
  4. Proved tag preservation across all `Trusted` borrow transformers, `evalStmt_borrowMonotone_frame`,
     `normalStmtStep_eq_raw_of_borrowMonotone`, `runDemandCallerLocationTrace_borrowAware_spec`, and
     `demandCallerLocation_bisim_eager_borrowAware` on arbitrary `Memory` with live borrows and
     protectors (`test_partC_borrowMonotone_and_trace_borrowAware`).
- `[adv B3]` (agent-b) fixed in A2:
  1. Condition 5 was reported closed, but the A2 lemmas only cover `resumeExternalCall` answers that
     satisfy `AnsPreservesCodeFrame`. The WP quantifies over *all* answers, so no whole-execution
     theorem follows. B3 adds diverging-call coverage, the general conservativity theorem
     `wpMirExecExt_mono_cone`, and restates the condition as partial.
  2. Condition 7 was reported closed at `1.26×`, but the cached narrowed table of the symbolic
     benchmark was never shown to be the narrowing of the 128-entry table, the narrowed proof was
     never transferred back to it, and the certificate cost was left out. B3 adds the certificate
     benchmark (`PartB_symVC_cert_M128`), `symCachedNarrow_eq_computed_128`, and
     `test_partB_symVC_transfer_128`, and reports the break-even.
  3. The symbolic VC covered only inputs `< 1000`. B3 generalizes it to the whole non-overflowing range
     (`symTrait_vc_narrow_of_lt`) and adds an overflow canary showing the obligations are live.
  4. The `protoTwoExtContracts` docstring claimed "adds 20 to its argument"; the contract only relates
     `11` to `31`. The docstring now says so.
  5. The header claimed all B2 gaps were closed. It now lists the open parts.

---

## 5. Conditions for Track A Promotion

1. **`allocId` / borrow-tag namespace: closed within the statement-trace model.**
   - `runDemandCallerLocationTrace_borrowAware_spec` and `demandCallerLocation_bisim_eager_borrowAware`
     prove that returned `Location` pointers, read through `readLocationsBorrowAware` (`lookupBorrow`
     before `lookupGlobalAlloc`) in the final memory, match `CallerLocationSite.resolve` and bisimulate
     the eager world.
   - This holds on every `traceBorrowMonotone` trace, including traces that mint stack borrow tags
     before and after `caller_location`. On `protoBorrowMonotoneTrace` an allocator using only
     `nextAllocId` would hand out id `1`, which is the live `&mut _2` tag
     (`test_partC_borrowAware_needed`).
   - *Residual*:
     - `CallerLocationTraceEvent` has no terminators (calls, returns, drops).
     - `copy_nonoverlapping` and unsizing / fn-ptr cast rvalues are outside `isBorrowMonotoneStmt`.
2. **Implicit writes: closed for the overlay's scope.** The fresh child is written with the
   `Trusted` write transition and UB checks. Reconcile with V2026_08_01's `initProtectedReborrowPerm`
   on schema bump.
3. **Statement frame in Part C: closed for `isBorrowMonotoneStmt` on arbitrary `Memory`.**
   `evalStmt_borrowMonotone_frame` and `normalStmtStep_eq_raw_of_borrowMonotone` cover these
   statements with live borrows and protectors. *Residual*: same as condition 1.
4. **Trie depth: closed** (`adaptiveRetagTrieDepth` + `adaptiveRetagTrieDepth_bitPath_injective`,
   exercised at `D = 5000`).
5. **External calls: partially closed.** What is proved:
   - **Soundness of cone filtering, for every execution:** `wpMirExecExt_mono_cone`.
   - **Losslessness, per step only:**
     - Calls emitted from cone-safe states target the cone (`stepMirFn_extCallInCone`).
     - Cone safety survives `resumeExternalCall` and `resumeExternalDivergingCall` for answers that
       satisfy `AnsPreservesCodeFrame` (`closedInvPoly_resumeExternalCall`,
       `closedInvPoly_resumeExternalDivergingCall`).

   *Residual*:
   - **A whole-execution losslessness theorem is not proved.** `wpMirExecExt` quantifies over
     *all* answers (`∀ ans`), including answers that replace `callees` or `activeCallee`, so the
     invariant can fail after a havoc'd call. This needs `AnsPreservesCodeFrame` in `MirLiftCore`'s
     answer semantics.
   - External tail calls (`resumeExternalTailCall`, which return through the caller frame from a
     torn-down memory) are not covered.

   The VC therefore keeps filtering summaries by cone.
6. **Hoisting: closed.** `checkBatchedVcConeNarrowCertGeneral`, `BatchedVcConeNarrowCert.ofCheckGeneral`
   and `traitFilterCovers_hoist_selectByMask` handle arbitrary keep/drop masks, including mixed trait
   partitions.
7. **Symbolic payoff: measured on the prototype; amortization required.**
   - On `symTrait_vc_narrow` at `M = 128`, the narrowed table needs 1.26× fewer heartbeats
     per VC.
   - The one-time certificate costs 2.23× that saving, so narrowing wins only when at
     least 3 VCs share one certificate.
   - Sealed coercions need 1.74× fewer heartbeats on the `∀ bits` chain.

   *Residual*: benchmark multi-function crate VCs end-to-end under `cargo anneal`, with certificate
   reuse across VCs.

### Proposed 2-Episode Track A Plan
1. `ep1`: Part A and Part D into `theory/Anneal/SparseRetagAndVcNarrow.lean` (conditions 2, 4).
2. `ep2`: Part B and Part C (conditions 1, 3, 5–7), exported from `theory/Anneal.lean`, with this
   test suite as the regression gate.
