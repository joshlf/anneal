# Prototype Evaluation Report — `ws-proto-sparse-retag-index-and-batched-vc-narrow`

- **Prototype Branch**: `refs/heads/prototype/ws-proto-sparse-retag-index-and-batched-vc-narrow/ep1-proto-sparse-retag-index-and-batched-vc-narrow`
- **Base `unstable` Commit SHA**: `1e208d1a9d6cce3326f6330ef2aecf942fe7d39d`
- **Paired Track A Workstream**: `ws-sparse-retag-index-and-batched-vc-narrow`
- **Deliverables** (the only files changed vs. base):
  - `theory/Anneal/SparseRetagAndVcNarrowPrototype.lean`
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean`
  - `PROTOTYPE_REPORT.md`
- **Kernel & Axiom Audit** (bottom of the test file, on the final code): `axiom audit passed: 2025 declarations (325 prototype theorems, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 leaked constants, 0 placeholder uses, 4 conditional test lemmas all discharged, 100% theorem reachability from closed test witnesses)`
  - All theorems depend only on `{propext, Quot.sound}`. The audit's self-tests confirm that it flags
    `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, an elaborated `have _ := @thm` placeholder,
    and a test statement that assumes an undischarged hypothesis. Reachability is computed only
    from *closed* test witnesses (no assumed hypotheses other than bounded membership `x ∈ l`).
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean` starts with `import Anneal` +
    `import Anneal.SparseRetagAndVcNarrowPrototype` and elaborates cleanly (no symbol/instance collisions).
- **Overall Recommendation**: **CONDITIONAL GO** — all four mechanisms are formally verified with
  `0 sorry` and `0 Classical.choice` over `Trusted.Rustc.V2026_06_01` and `Anneal.MirLiftCore`, and
  the `[adv B2]` open gaps (mixed-partition trait hoisting, multi-call external summary cone safety,
  universally quantified symbolic trait-dispatch VC + benchmark, general borrow-monotone statement
  frame on arbitrary `Memory`, and trace-level borrow-aware `Location` bisimulation) are now closed
  in `[adv A2]`; §5 lists the remaining integration items for Track A promotion.

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
- `canary_externalSummary_vc`, `canary_coercedExternalSummary_vc`, `canary_twoExternalCalls_vc`.
- Genuine universally quantified symbolic VC (`symTrait_vc_narrow`, `∀ x : Nat`): symbolic
  `x % 1000` flows through polymorphic `sym_poly::<u32>(_1)` (`AddUnchecked(_1, 7)`) and
  trait-dispatched `<Circle as Area>::area(_0)` (`AddUnchecked(_1, 24)`) to return
  `(x % 1000) + 31 : u32` (backed by `wpMirExecExt_step_tau`, `wpMirExecExt_step_ret`,
  `stepMirState_assign_local`, and `evalRvalue_addUnchecked_u32`; verified non-trivial by a
  meta-level `isDefEq` audit confirming `rfl` cannot reduce `Nat.ble 4294967296 ((x % 1000) + 7)`).
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
    and `Statement.retag` both before and after `caller_location`):
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

Methodology: both arms of every comparison use the exact same mechanism — `decide +kernel` for the
execution/certificate tables, elaborator `rfl` for both concrete VC-discharge arms, the identical
step-by-step symbolic proof script (`wpMirExecExt_step_tau` + `stepMirState_assign_local` +
`evalRvalue_addUnchecked_u32` + `omega`) for both symbolic `∀ x : Nat` VC arms, and the same
`simp only` script shape for both coercion arms. `IO.getNumHeartbeats` deltas are deterministic;
wall-clock (`IO.monoNanosNow`) is from the final receipt run and is noisy.

### 2.1 Part A — linear oracle vs. sparse index (`definitionCount = 512`)

| Rows `M` | Linear oracle, 1 query | Sparse: prepare + 1 query | Sparse: prepare + `M` queries |
| :--- | ---: | ---: | ---: |
| 16 | `67,541` hb (`9.5` ms) | `146,852` hb (`23.4` ms) | `438,921` hb (`74.5` ms) |
| 64 | `577,569` hb (`78.7` ms) | `634,328` hb (`107.5` ms) | `1,752,176` hb (`320.4` ms) |
| 128 | `2,117,815` hb (`311.5` ms) | `1,420,921` hb (`239.2` ms) | `3,559,290` hb (`684.3` ms) |
| 256 | `8,147,437` hb (`1,437.6` ms) | `3,226,248` hb (`594.1` ms) | `7,285,268` hb (`1,462.2` ms) |

- The linear oracle's growth approaches 4× per doubling of `M` (3.7× from 64 to 128, 3.8× from 128 to
  256). Including preparation, the sparse index is slower for one query at `M = 16` (2.17× the
  linear cost), roughly even at `M = 64`, and faster at `M = 128` (1.49×) and `M = 256` (2.53×).
- All `256` sparse queries at `M = 256` (`7,285,268` hb) cost fewer heartbeats than **one**
  linear-oracle query (`8,147,437` hb).

### 2.2 Part B — full callee table vs. certified narrowing (trait call through `TraitImplEntry`)

| Callees `M` | Full table run | Cert check (compute cone + mask, 1 `decide`) | Narrowed run (narrowing computed in-kernel) | Narrowed run (cached narrowed table) |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `562,764` hb (`92.1` ms) | `1,623,910` hb (`262.4` ms) | `588,016` hb (`98.9` ms) | `451,991` hb (`75.3` ms) |
| 64 | `670,401` hb (`105.9` ms) | `2,066,850` hb (`332.1` ms) | `781,830` hb (`130.4` ms) | `451,993` hb (`76.9` ms) |
| 128 | `813,908` hb (`121.7` ms) | `2,657,375` hb (`423.9` ms) | `1,040,216` hb (`172.7` ms) | `451,985` hb (`78.2` ms) |

- The cached arm's literal table is proved equal (`rfl`) to the computed narrowing
  (`cachedNarrow_eq_computed_*`). Steady state at `M = 128`: 1.80× fewer heartbeats than the
  full table; recomputing the narrowing per run is slower than the full table, and the one-time
  certificate costs ~3.3× a full run.
- Concrete VC discharge by elaborator `rfl` (`M = 128`):
  full table `3,861,976` hb (`378.1` ms) vs. cached narrowed table `2,160,819` hb (`220.5` ms)
  (1.79×).
- Universally quantified symbolic VC (`∀ x : Nat`, `symTraitRootMir` calling `sym_poly::<u32>` and
  trait-dispatched `<Circle as Area>::area` with `AddUnchecked` overflow obligations, `M = 128`,
  identical tactic script):
  full table `5,779,471` hb (`710.3` ms) vs. cached narrowed table `4,584,286` hb (`445.0` ms)
  (1.26× fewer heartbeats; saves `1,195,185` hb on a 2-call root body).
- Coercion (`∀ bits`, 16 chained coercions, the same `simp only` script shape): sealed
  `coerceValueAt` rewritten by `coerceValueAt_u32` `257,291` hb (`28.2` ms) vs. a reducible copy
  unfolded by `dsimp`/`simp` `447,108` hb (`36.0` ms) (1.74×).

### 2.3 Part C — eager pre-allocation vs. demand-time `Location` (same trace in both worlds)

| Sites `S` | Eager, non-panicking (8 stmts) | Demand, non-panicking | Eager, panicking (1 invocation) | Demand, panicking |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `129,857` hb (`24.6` ms) | `52,891` hb (`7.4` ms) | `237,093` hb (`38.1` ms) | `196,723` hb (`27.1` ms) |
| 64 | `761,973` hb (`114.4` ms) | `52,907` hb (`9.9` ms) | `394,371` hb (`76.7` ms) | `196,831` hb (`29.3` ms) |
| 128 | `2,507,959` hb (`384.6` ms) | `52,918` hb (`6.9` ms) | `625,514` hb (`83.6` ms) | `196,780` hb (`28.2` ms) |

- Demand cost is independent of `S`; the eager arm materializes `S + 1` globals (checked). Its
  super-linear growth is partly an artifact of the list-based `Memory.globals` model.

### 2.4 Part D — eager vs. lazy distinct-address write chains (`cap = 128`, read of the last write)

| Writes `N` | Eager (`mkEagerWrite`) | Lazy (`mkLazyWrite`) | Proved spine inspections (eager / lazy) |
| :--- | ---: | ---: | ---: |
| 16 | `121,698` hb (`17.2` ms) | `60,065` hb (`7.1` ms) | 136 / 16 |
| 64 | `1,226,840` hb (`191.3` ms) | `113,387` hb (`15.9` ms) | 2080 / 64 |
| 128 | `4,728,554` hb (`921.7` ms) | `184,031` hb (`30.7` ms) | 8256 / 128 |

- Wide-shift canary (`shift = 2^64`, six safe shifts, one `decide +kernel`): `140,173` hb (`15.8` ms).

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
  `resumeExternalCall` to a second external call), `symTrait_vc_narrow` +
  `test_partB_symbolic_trait_vc` (symbolic `∀ x : Nat` VC over polymorphic + trait-dispatched
  `AddUnchecked` calls).
- **Part C**: `demandCallerLocation_filename_dedup`, `canary_demandLocation_borrowTag_disjoint`,
  `trackCaller_span_owner_policy`, `trackCaller_stops_at_nonTrackCaller_frame`, bisimulation for all
  8 policies on a trace with a repeated site, explicit `AllocRenamingRel`,
  `test_partC_stmt_pure_memory`, and `test_partC_borrowMonotone_and_trace_borrowAware` (full
  borrow-aware bisimulation through `readLocationsBorrowAware` across `protoBorrowMonotoneTrace`,
  which mints stack borrows via `Rvalue.ref` and `Statement.retag` both before and after
  `caller_location`).
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

---

## 5. Conditions for Track A Promotion

1. **`allocId` / borrow-tag namespace — closed for `traceBorrowMonotone` traces.**
   `runDemandCallerLocationTrace_borrowAware_spec` and `demandCallerLocation_bisim_eager_borrowAware`
   prove that returned `Location` pointers read through `readLocationsBorrowAware` (`lookupBorrow`
   before `lookupGlobalAlloc`) in the final memory match `CallerLocationSite.resolve` and bisimulate
   the eager world across traces that mint new stack borrow tags both before and after
   `caller_location`. *Track A residual*: extend `isBorrowMonotoneStmt` to `copy_nonoverlapping` and
   unsizing / fn-ptr cast rvalues (`evalUnsizeCoercion`, `evalUnsafeFnPointer`).
2. **Implicit writes — closed for the overlay's scope.** The fresh child is written with the
   `Trusted` write transition and UB checks; reconcile with V2026_08_01's `initProtectedReborrowPerm`
   on schema bump.
3. **Statement frame in Part C — closed for `isBorrowMonotoneStmt` on arbitrary `Memory`.**
   `evalStmt_borrowMonotone_frame` and `normalStmtStep_eq_raw_of_borrowMonotone` cover all
   non-intrinsic statements and all `isLocalRefOrPureRvalue` assignments (including `&_1` / `&mut _1`)
   with live borrows and protectors. *Track A residual*: `copy_nonoverlapping` and unsizing / fn-ptr
   cast rvalues.
4. **Trie depth — closed** (`adaptiveRetagTrieDepth` + `adaptiveRetagTrieDepth_bitPath_injective`,
   exercised at `D = 5000`).
5. **External calls — closed for code-frame-preserving external answers.**
   `closedInvPoly_resumeExternalCall` and `stepConeSafeTrait_of_resumeExternalCall` prove that
   `ClosedInvPoly` and `StepConeSafeTrait` survive `resumeExternalCall` under `AnsPreservesCodeFrame`
   (`canary_twoExternalCalls_vc`). *Track A residual*: thread `AnsPreservesCodeFrame` into
   `MirLiftCore.lean`'s `MirCallContract` so whole-execution `wpMirExecExt` can omit per-site `inCone`
   summary filtering when all contracts preserve the code frame.
6. **Hoisting — closed** (`checkBatchedVcConeNarrowCertGeneral` + `BatchedVcConeNarrowCert.ofCheckGeneral`
   + `traitFilterCovers_hoist_selectByMask` handle arbitrary keep/drop masks including mixed trait
   partitions).
7. **Symbolic payoff — closed on the prototype (`1.26×` on `symTrait_vc_narrow` at `M = 128`,
   `1.74×` on `coerceValueAt`).** *Track A residual*: benchmark end-to-end on production
   `cargo anneal` multi-function crate VCs.

### Proposed 2-Episode Track A Plan
1. `ep1`: Part A and Part D into `theory/Anneal/SparseRetagAndVcNarrow.lean` (conditions 2, 4).
2. `ep2`: Part B and Part C (conditions 1, 3, 5–7), exported from `theory/Anneal.lean`, with this
   test suite as the regression gate.
