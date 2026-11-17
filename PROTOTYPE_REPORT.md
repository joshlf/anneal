# Prototype Evaluation Report — `ws-proto-sparse-retag-index-and-batched-vc-narrow`

- **Prototype Branch**: `refs/heads/prototype/ws-proto-sparse-retag-index-and-batched-vc-narrow/ep1-proto-sparse-retag-index-and-batched-vc-narrow`
- **Base `unstable` Commit SHA**: `1e208d1a9d6cce3326f6330ef2aecf942fe7d39d`
- **Paired Track A Workstream**: `ws-sparse-retag-index-and-batched-vc-narrow`
- **Deliverables** (the only files changed vs. base):
  - `theory/Anneal/SparseRetagAndVcNarrowPrototype.lean`
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean`
  - `PROTOTYPE_REPORT.md`
- **Kernel & Axiom Audit** (bottom of the test file, on the final code): `axiom audit passed: 2261 declarations (388 prototype theorems, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 leaked constants, 0 placeholder uses, 13 conditional test lemmas all discharged, 100% theorem reachability from closed test witnesses)`
  - All theorems depend only on `{propext, Quot.sound}`.
  - The audit's self-tests confirm that it flags:
    - `Classical.choice` reached transitively through current-file constants (rolled-back probe
      declarations);
    - `sorryAx` and `Lean.ofReduceBool`;
    - an elaborated `have _ := @thm` placeholder;
    - a test statement that assumes an undischarged hypothesis.

    It also reports no forbidden axiom for known clean constants.
  - Reachability is computed only from *closed* test witnesses (no assumed hypotheses other than
    bounded membership `x ∈ l`).
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean` starts with `import Anneal` +
    `import Anneal.SparseRetagAndVcNarrowPrototype` and elaborates cleanly (no symbol/instance collisions).
- **Overall Recommendation**: **CONDITIONAL GO**. All four mechanisms are kernel-checked (`0 sorry`,
  `0 Classical.choice`) over `Trusted.Rustc.V2026_06_01` and `Anneal.MirLiftCore`. Status of the §5
  conditions:
  - Conditions 2, 4 and 6 are closed.
  - Conditions 1 and 3 are closed for `isBorrowMonotoneStmt` statements and `isBorrowMonotoneTerminator`
    terminators, including a concrete interprocedural `.call` + `.return_` trace
    (`protoInterprocCallReturnBorrowTrace`, `test_partC_interproc_call_return_trace_borrowAware`) that
    mints stack borrows in both caller (`depth = 0`) and callee (`depth = 1`) and disables the callee
    borrow on `.return_` via `disableFrameBorrows`.
  - Condition 5 is closed per step for all three external-call forms, and whole-execution losslessness
    is proved both for standard `wpMirExecExt` on mixed internal/trait/external cones where internal
    cone calls resolve via `lookupCallee` and external cone calls are summarized
    (`wpMirExecExt_cone_iff_unfiltered_of_mixed_cone`, compatible with `UntrustedAdmissible`,
    `test_partB_mixed_cone_standard_wp_lossless`) and for the code-frame WP `wpMirExecExtCF` with full
    callee/trait/summary narrowing (`wpMirExecExtCF_trait_cone_narrow`,
    `vcMirWithCalleesCF_narrow_of_batchedCert`, `vcMirWithCalleesCF_narrow_unfiltered_of_batchedCert`).
  - Condition 7 is measured: one certificate pays off once at least 3 VCs share it. The
    measured 3-VC batch saves `923,324` hb.

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
  this to diverging external calls (`call ... -> !`, `resumeExternalDivergingCall`), and
  `ansPreservesCodeFrame_withBorrows`, `closedInvPoly_resumeExternalTailCall`,
  `stepConeSafeTrait_of_resumeExternalTailCall`, and `canary_tailExternalCall_coneSafe` extend it to
  external tail calls (`TerminatorKind.tailCall`, `resumeExternalTailCall`).
- Cone filtering: conservative always, lossless only under conditions.
  - **Conservative for every execution** (all fuel, states, contracts, summary environments):
    `coneSummary?_mono`, `wpMirExecExt_mono_cone`.
  - **Step-level external-call safety** (`NodeExtCallSafe`): `nodeExtCallSafe_of_empty_cone`,
    `evalTerminator_extCallSafe`, `stepMirFn_extCallSafe`. Every external call emitted from a
    `ClosedInvPoly` state targets `cone` and resumes into a `ClosedInvPoly` state on any
    `AnsPreservesCodeFrame` answer.
  - **Whole-execution losslessness**, under the stated hypotheses:
    1. `wpMirExecExt_cone_iff_unfiltered_of_summarized` (standard WP, all-external cones). Hypotheses:
       *every* cone path is summarized, and summary contracts imply `AnsPreservesCodeFrame`.
       `summarizedCone_has_no_internal_body` shows that admissible summaries then force an
       all-external cone (`test_partB_summarized_lossless_inapplicable`).
    2. `wpMirExecExt_cone_iff_unfiltered_of_mixed_cone` (standard WP, mixed internal/trait/external
       cones). Hypotheses: `coneCallsResolveOrSummarized c₁ ti₁ extEnv cone root = true` (every call in
       `root` and `coneBodies cone c₁` either resolves internally via `lookupCallee c₁ _ _ _ ti₁` — so
       `evalTerminator` steps internally without emitting a `MirCallE` — or has an external summary in
       `extEnv`) and summary contracts imply `AnsPreservesCodeFrame`. Proved via
       `lookupCallee_nil_indep_layouts`, `extractCalleeTypeArgs_instantiate_of_nil`,
       `callResolvesOrSummarizedAt_instantiate_false`, `termCallsResolveOrSummarized_instantiate_false`,
       `bodyCallsResolveOrSummarized_instantiate_false`, `callResolvesOrSummarizedAt_spec`, and
       `stepExtCallSummarized_of_closedInvPoly`. Compatible with `UntrustedAdmissible` and instantiated
       on both `traitCallRootMir` and the mixed internal+external cone of `protoTailExtRootMir` in
       `test_partB_mixed_cone_standard_wp_lossless`.
    3. `wpMirExecExtCF_cone_iff_unfiltered` + `wpMirExecExtCF_trait_cone_narrow` +
       `vcMirWithCalleesCF_narrow_of_batchedCert` +
       `vcMirWithCalleesCF_narrow_unfiltered_of_batchedCert` (code-frame WP `wpMirExecExtCF`, which
       admits only answers satisfying `AnsPreservesCodeFrame`, including for havoc'd calls). It holds
       for every `extEnv` and every `contracts`. `wpMirExecExt_imp_wpMirExecExtCF` shows this WP is
       *weaker* than the standard one (sound for real executions when external code preserves the code
       frame). `wpMirExecExtCF_trait_cone_narrow` proves full callee/trait/summary narrowing for
       `wpMirExecExtCF` via the `MirCallAns.mapMem (Memory.withCalleesAndTraits ...)` bijection
       (`ansPreservesCodeFrame_mapMem_withCalleesAndTraits`,
       `mirCallAns_mapMem_withCalleesAndTraits_cancel`, `memory_withCalleesAndTraits_inj_of_eq`,
       `applyUnwindAction_mem_withCalleesAndTraits`,
       `invalidateDirectDestWriteBorrows_borrows_withCalleesAndTraits`,
       `resumeExternalCall_withCalleesAndTraits`, `resumeExternalDivergingCall_withCalleesAndTraits`,
       `resumeExternalTailCall_withCalleesAndTraits`), and
       `vcMirWithCalleesCF_narrow_unfiltered_of_batchedCert` relates narrowed cone-filtered
       `vcMirWithCalleesCF` directly to full unfiltered `wpMirExecExtCFUnfiltered`
       (`test_partB_whole_exec_lossless`, `test_partB_cf_wp_weaker`).
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
  - Terminator borrow-tag monotonicity and memory frame across `isBorrowMonotoneTerminator`
    (`.goto`, `.switchInt`, `.unwindResume`, `.unwindTerminate`, `.return_`, `.unreachable`, `.drop`,
    `.assert`, `.tailCall`, diverging `.call`, and `.call` to a constant non-intrinsic function item;
    calls through function pointers and intrinsic calls are excluded):
    `map_tag_disableFrameBorrows`, `map_tag_disableFramesAbove`,
    `map_tag_invalidateDirectDestWriteBorrows`, `invalidateDirectDestWriteBorrows_borrowMonotone`,
    `writeReturnDestination_borrowMonotone`, `unwindFromCallStack_borrowMonotone`,
    `applyUnwindAction_borrowMonotone`, `evalTerminator_borrowMonotone_frame`, `normalTerminatorStep`,
    `normalTerminatorStep_eq_raw_of_borrowMonotone`, and `normalTerminatorStep_borrowMonotone`.
- General trace-level theorems over **all** call-site tables, **all** traces (interleaving
  `.normalStep`, `.terminatorStep`, and `.invokeCallerLocation`), and all 8 policies:
  - Through `readLocationFromGlobals`: `evalDemandCallerLocation_spec`,
    `runDemandCallerLocationTrace_spec`, `eagerInitAux_spec`, `demandCallerLocation_bisim_eager`,
    `demandCallerLocation_no_call_zero_allocs`, `eagerCallerLocation_clutter`,
    `allocRenamingRel_of_readLocations`.
  - Through borrow-aware `readLocationsBorrowAware` (`lookupBorrow` before `lookupGlobalAlloc`) across
    any `traceBorrowMonotone` trace (including traces that mint new stack borrow tags via `Rvalue.ref`
    and `StatementKind.retag` and step terminators via `.terminatorStep` both before and after
    `caller_location`):
    `runDemandCallerLocationTrace_borrow_monotone`, `eagerInitAux_borrow_monotone`,
    `runEagerCallerLocationTrace_borrow_monotone`, `runDemandCallerLocationTrace_borrowAware_spec`,
    and `demandCallerLocation_bisim_eager_borrowAware` (exercised on `protoBorrowMonotoneTrace` in
    `test_partC_borrowMonotone_and_trace_borrowAware`, on `protoGotoDropBorrowTrace` in
    `test_partC_terminator_trace_borrowAware`, and on the interprocedural `.call` + `.return_` trace
    `protoInterprocCallReturnBorrowTrace` in `test_partC_interproc_call_return_trace_borrowAware`, which
    mints caller borrow `tag = 1` at `depth = 0`, pushes a caller frame via `.call`, mints callee
    borrow `tag = 2` at `depth = 1`, invokes `caller_location` inside the callee, and executes
    `.return_` to disable callee `tag = 2` to `.disabled` via `disableFrameBorrows` while preserving
    caller `tag = 1` at `.reservedFrz false`).

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
  `evalRvalue_addUnchecked_u32` + `omega`) for every symbolic `∀ x : Nat` VC arm;
- the same `simp only` script shape for both coercion arms.

`IO.getNumHeartbeats` deltas are deterministic for a fixed file, but they depend on what was
elaborated before them (elaboration caches). The symbolic VC arms therefore run after one
unreported warm-up proof per table and are interleaved (full table, then narrowed table, per VC).
Wall-clock times (`IO.monoNanosNow`) come from the final receipt run and are noisy. Optimized arms
include their one-time costs (index preparation, certificate checking, narrowing computation) unless
labeled otherwise.

### 2.1 Part A — linear oracle vs. sparse index (`definitionCount = 512`)

| Rows `M` | Linear oracle, 1 query | Sparse: prepare + 1 query | Sparse: prepare + `M` queries |
| :--- | ---: | ---: | ---: |
| 16 | `67,541` hb (`9.4` ms) | `146,852` hb (`23.8` ms) | `438,921` hb (`73.6` ms) |
| 64 | `577,569` hb (`80.9` ms) | `634,328` hb (`105.4` ms) | `1,752,176` hb (`317.9` ms) |
| 128 | `2,117,815` hb (`334.6` ms) | `1,420,921` hb (`248.4` ms) | `3,559,290` hb (`698.9` ms) |
| 256 | `8,147,437` hb (`1,641.9` ms) | `3,226,248` hb (`719.6` ms) | `7,285,268` hb (`1,499.8` ms) |

- The linear oracle's cost grows by 3.67× from `M = 64` to `M = 128` and by
  3.85× from `M = 128` to `M = 256`, approaching 4× per doubling.
- Including preparation, the sparse index is slower than the linear oracle for one query at `M = 16`
  (2.17× the linear cost) and roughly even at `M = 64`. It is faster at `M = 128`
  (1.49×) and at `M = 256` (2.53×).
- All `256` sparse queries at `M = 256` (`7,285,268` hb) cost fewer heartbeats
  than **one** linear-oracle query (`8,147,437` hb). (The cost of 256 linear queries
  was not measured.)

### 2.2 Part B — full callee table vs. certified narrowing (trait call through `TraitImplEntry`)

| Callees `M` | Full table run | Cert check (compute cone + mask, 1 `decide`) | Narrowed run (narrowing computed in-kernel) | Narrowed run (cached narrowed table) |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `562,776` hb (`264.0` ms) | `1,623,919` hb (`604.3` ms) | `588,029` hb (`239.6` ms) | `452,013` hb (`202.1` ms) |
| 64 | `670,399` hb (`275.9` ms) | `2,066,860` hb (`786.4` ms) | `781,836` hb (`303.4` ms) | `451,999` hb (`185.2` ms) |
| 128 | `813,914` hb (`292.7` ms) | `2,657,361` hb (`940.2` ms) | `1,040,218` hb (`426.7` ms) | `451,992` hb (`202.6` ms) |

- The cached arm's literal table is proved equal (`rfl`) to the computed narrowing
  (`cachedNarrow_eq_computed_*`).
- Steady state at `M = 128`: the cached narrowed run uses 1.80× fewer heartbeats than the
  full table. Recomputing the narrowing on every run is slower than the full table. The one-time
  certificate costs 3.26× a full run.
- Concrete VC discharge by elaborator `rfl` (`M = 128`; *not* a symbolic VC): full table
  `3,861,907` hb (`1,015.5` ms) vs. cached narrowed table `2,160,516` hb (`554.2` ms)
  (1.79×).
- Symbolic VCs (`∀ x : Nat`, `symTraitRootMir`, `M = 128`, identical tactic script on every arm; the
  three VCs differ in their input range `x % 1000`, `x % 65536`, `x % 1000000`):

  | VC | Full table | Cached narrowed table |
  | :--- | ---: | ---: |
  | `x % 1000` | `5,779,757` hb (`1,307.3` ms) | `4,578,029` hb (`1,061.8` ms) |
  | `x % 65536` | `5,779,869` hb (`1,361.4` ms) | `4,578,098` hb (`1,068.4` ms) |
  | `x % 1000000` | `5,779,690` hb (`1,372.3` ms) | `4,578,005` hb (`1,199.8` ms) |
  | One-time certificate (`PartB_symVC_cert_M128`) | — | `2,681,860` hb (`1,204.0` ms) |

  - **Single VC (`x % 1000`):** the narrowed table saves `1,201,728` hb (1.26×).
    `symCachedNarrow_eq_computed_128` proves the cached table is the certified narrowing.
    `test_partB_symVC_transfer_128` turns the narrowed-table proof plus the certificate into the
    full-table VC. The certificate costs 2.23× this saving, so certifying and proving one
    VC on the narrowed table costs `7,259,889` hb, versus `5,779,757` hb on the
    full table.
  - **Batch of the three measured VCs** (`test_partB_symVC_batch3_transfer_128`, one certificate):
    the certificate plus the three narrowed proofs cost `16,415,992` hb, versus `17,339,316` hb for
    the three full-table proofs, a net saving of `923,324` hb.
  - Break-even: with this certificate and the single-VC saving above, narrowing pays off from
    3 VCs sharing one certificate.
- Coercion (`∀ bits`, 16 chained coercions, the same `simp only` script shape): sealed
  `coerceValueAt` rewritten by `coerceValueAt_u32` `257,237` hb (`71.3` ms) vs. a reducible copy
  unfolded by `dsimp`/`simp` `447,063` hb (`94.5` ms) (1.74×).

### 2.3 Part C — eager pre-allocation vs. demand-time `Location` (same trace in both worlds)

| Sites `S` | Eager, non-panicking (8 stmts) | Demand, non-panicking | Eager, panicking (1 invocation) | Demand, panicking |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `130,093` hb (`23.4` ms) | `53,134` hb (`8.1` ms) | `237,361` hb (`43.0` ms) | `197,037` hb (`28.6` ms) |
| 64 | `762,228` hb (`119.2` ms) | `53,165` hb (`8.0` ms) | `394,645` hb (`61.2` ms) | `197,055` hb (`31.1` ms) |
| 128 | `2,508,214` hb (`896.3` ms) | `53,170` hb (`8.4` ms) | `625,790` hb (`105.2` ms) | `197,008` hb (`48.4` ms) |

- Demand cost is independent of `S`; the eager arm materializes `S + 1` globals (checked). Its
  super-linear growth is partly an artifact of the list-based `Memory.globals` model.

### 2.4 Part D — eager vs. lazy distinct-address write chains (`cap = 128`, read of the last write)

| Writes `N` | Eager (`mkEagerWrite`) | Lazy (`mkLazyWrite`) | Proved spine inspections (eager / lazy) |
| :--- | ---: | ---: | ---: |
| 16 | `121,690` hb (`18.7` ms) | `60,040` hb (`7.0` ms) | 136 / 16 |
| 64 | `1,226,863` hb (`239.2` ms) | `113,394` hb (`20.2` ms) | 2080 / 64 |
| 128 | `4,728,538` hb (`1,208.4` ms) | `184,056` hb (`49.4` ms) | 8256 / 128 |

- Wide-shift canary (`shift = 2^64`, six safe shifts, one `decide +kernel`): `140,141` hb (`13.4` ms).

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
  is cone-safe; a normal return from it is UB), `canary_tailExternalCall_coneSafe` +
  `test_partB_tail_external_call` (caller frame popped by `resumeExternalTailCall` after an external
  tail call resumes in a cone-safe caller state), `test_partB_cone_filter_conservative`,
  `test_partB_whole_exec_lossless` (standard-WP equivalence on the all-external, fully summarized cone
  of `protoTwoExtCallsRootMir` with an extra out-of-cone summary `ext::unrelated`, plus code-frame-WP
  entry equivalence and narrowed-to-unfiltered equivalence via `vcMirWithCalleesCF_narrow_of_batchedCert`
  and `vcMirWithCalleesCF_narrow_unfiltered_of_batchedCert` on `traitCallRootMir`),
  `test_partB_mixed_cone_standard_wp_lossless` (standard-WP equivalence via
  `wpMirExecExt_cone_iff_unfiltered_of_mixed_cone` on `traitCallRootMir` and on the mixed
  internal+external cone of `protoTailExtRootMir` under `checkUntrustedAdmissible = true`),
  `test_partB_summarized_lossless_inapplicable` (the all-external standard-WP theorem's hypothesis is
  false for the trait canary's cone, which contains the internal body `proto::poly`),
  `test_partB_cf_wp_weaker`,
  `symTrait_vc_narrow` +
  `test_partB_symbolic_trait_vc` (symbolic `∀ x : Nat` VC over polymorphic + trait-dispatched
  `AddUnchecked` calls), `test_partB_symbolic_vc_range` (largest admissible input `2^32 - 32`;
  overflow canary at `4294967290`), `test_partB_symVC_transfer_128`, and
  `test_partB_symVC_batch3_transfer_128` (3 symbolic VCs sharing the single `bench_partB_symVC_cert_128`
  certificate transferred to the full 128-entry table; all six table/VC combinations are measured in
  §2.2).
- **Part C**: `demandCallerLocation_filename_dedup`, `canary_demandLocation_borrowTag_disjoint`,
  `trackCaller_span_owner_policy`, `trackCaller_stops_at_nonTrackCaller_frame`, bisimulation for all
  8 policies on a trace with a repeated site, explicit `AllocRenamingRel`,
  `test_partC_stmt_pure_memory`, `test_partC_borrowMonotone_and_trace_borrowAware` (full borrow-aware
  bisimulation through `readLocationsBorrowAware` across `protoBorrowMonotoneTrace`, which mints stack
  borrows via `Rvalue.ref` and `StatementKind.retag` both before and after `caller_location`),
  `test_partC_terminator_trace_borrowAware` (borrow-aware bisimulation and
  `normalTerminatorStep_eq_raw_of_borrowMonotone` across `protoGotoDropBorrowTrace`),
  `test_partC_interproc_call_return_trace_borrowAware` (borrow-aware bisimulation across the
  interprocedural `.call` + `.return_` trace `protoInterprocCallReturnBorrowTrace`, minting stack
  borrows at `depth = 0` and `depth = 1` and disabling the callee borrow on `.return_`), and
  `test_partC_borrowAware_needed` (on `protoBorrowMonotoneTrace` an allocator using only `nextAllocId`
  would give the `Location` the live borrow tag `1`).
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
- `[adv A3]` (agent-a):
  1. Closed external tail calls (`ansPreservesCodeFrame_withBorrows`,
     `closedInvPoly_resumeExternalTailCall`, `stepConeSafeTrait_of_resumeExternalTailCall`,
     `canary_tailExternalCall_coneSafe`, `test_partB_tail_external_call`) and proved unified
     step-level external-call safety (`NodeExtCallSafe`, `nodeExtCallSafe_of_empty_cone`,
     `evalTerminator_extCallSafe`, `stepMirFn_extCallSafe`).
  2. Proved both whole-execution lossless cone-filtering theorems:
     `wpMirExecExt_cone_iff_unfiltered_of_summarized` (on standard `wpMirExecExt` when cone externals
     are summarized and contracts preserve `AnsPreservesCodeFrame`) and
     `wpMirExecExtCF_cone_iff_unfiltered` + `vcMirWithCalleesCF_narrow_unfiltered_of_batchedCert`
     (renamed in B4; whole-execution losslessness across arbitrary `extEnv` and `contracts` when
     external answers preserve `AnsPreservesCodeFrame`, `test_partB_whole_exec_lossless`).
  3. Added terminator borrow-tag monotonicity and memory frame across `isBorrowMonotoneTerminator`
     (`map_tag_disableFrameBorrows`, `map_tag_disableFramesAbove`,
     `map_tag_invalidateDirectDestWriteBorrows`, `invalidateDirectDestWriteBorrows_borrowMonotone`,
     `writeReturnDestination_borrowMonotone`, `unwindFromCallStack_borrowMonotone`,
     `applyUnwindAction_borrowMonotone`, `evalTerminator_borrowMonotone_frame`,
     `normalTerminatorStep`, `normalTerminatorStep_eq_raw_of_borrowMonotone`, `normalTerminatorStep_borrowMonotone`)
     and extended `CallerLocationTraceEvent` with `.terminatorStep` (`test_partC_terminator_trace_borrowAware`).
  4. Added a 3-VC symbolic batch benchmark and transfer theorem at `M = 128`
     (`bench_partB_symVC_narrowCached2_128`, `bench_partB_symVC_narrowCached3_128`,
     `test_partB_symVC_batch3_transfer_128`) demonstrating amortized net heartbeat savings when 3
     symbolic VCs share the single `bench_partB_symVC_cert_128` certificate.
- `[adv B4]` (agent-b) fixed in A3, plus one false claim of its own from B1:
  1. `wpMirExecExt_cone_iff_unfiltered_of_summarized` was described as needing only the *external*
     cone paths to be summarized, but `h_sum` covers every cone path. With admissible summaries this
     forces an all-external cone (`summarizedCone_has_no_internal_body`), so it never applies to the
     trait canary or to any program that calls an internal function
     (`test_partB_summarized_lossless_inapplicable`). The docstring and report now say so.
  2. `vcMirWithCalleesCF_narrow_unfiltered_of_batchedCert` was described as relating the *narrowed*
     callee table to the full unfiltered one. Its statement mentions only the full table, and the
     `vcMirWithCalleesCF` definition it was named after was unused. B4 renames the theorem to
     `wpMirExecExtCF_entry_cone_iff_unfiltered_of_batchedCert`, removes the unused definition, and
     proves `wpMirExecExt_imp_wpMirExecExtCF`, making explicit that the code-frame WP is weaker than
     the standard WP.
  3. The terminator trace was named `protoCallReturnBorrowTrace` and described as interprocedural and
     as stepping terminators that "mint or disable" borrow tags. It executes only `.goto` and `.drop`,
     with no call or return, and those steps change no tag. It is renamed `protoGotoDropBorrowTrace`,
     and its test now also checks that the `.drop` executes.
  4. The report claimed `isBorrowMonotoneTerminator` covers all terminators. It excludes intrinsic
     calls and calls through function pointers.
  5. The 3-VC batch comparison used `3 ×` the full-table cost of the first VC. B4 measures the
     full-table cost of all three VCs (`PartB_symVC_full2_M128`, `PartB_symVC_full3_M128`).
     Heartbeat deltas also turned out to depend on elaboration order:
     - A3's `narrowCached2/3`, run after the certificate, measured about 200K hb above
       `narrowCached`.
     - Full-table arms placed after them measured about 200K hb below `full`.

     B4 adds one unreported warm-up proof per table and interleaves the arms. All three VCs then
     cost the same on each table, within 0.01%.
  6. The report claimed, since B1, that the axiom audit has self-tests for `Classical.choice`,
     `sorryAx` and `Lean.ofReduceBool`. No such self-test existed. B4 adds one: rolled-back probe
     constants reach `Classical.choice` transitively through current-file constants, `sorryAx` and
     `Lean.ofReduceBool` are checked through the imported-constant branch, and a clean-constant check
     guards against false positives.
- `[adv A4]` (agent-a):
  1. Proved standard-WP whole-execution lossless cone filtering on mixed internal/polymorphic/trait/external
     cones (`coneCallsResolveOrSummarized`, `lookupCallee_nil_indep_layouts`,
     `extractCalleeTypeArgs_instantiate_of_nil`, `callResolvesOrSummarizedAt_instantiate_false`,
     `termCallsResolveOrSummarized_instantiate_false`, `bodyCallsResolveOrSummarized_instantiate_false`,
     `callResolvesOrSummarizedAt_spec`, `stepExtCallSummarized_of_closedInvPoly`,
     `wpMirExecExt_cone_iff_unfiltered_of_mixed_cone`), compatible with `UntrustedAdmissible` and
     instantiated on both `traitCallRootMir` and the mixed internal+external cone of
     `protoTailExtRootMir` (`test_partB_mixed_cone_standard_wp_lossless`).
  2. Proved full callee/trait/summary narrowing and narrowed-to-unfiltered equivalence for the
     code-frame WP (`MirCallAns.mapMem`, `ansPreservesCodeFrame_mapMem_withCalleesAndTraits`,
     `mirCallAns_mapMem_withCalleesAndTraits_cancel`, `memory_withCalleesAndTraits_inj_of_eq`,
     `applyUnwindAction_mem_withCalleesAndTraits`,
     `invalidateDirectDestWriteBorrows_borrows_withCalleesAndTraits`,
     `resumeExternalCall_withCalleesAndTraits`, `resumeExternalDivergingCall_withCalleesAndTraits`,
     `resumeExternalTailCall_withCalleesAndTraits`, `wpMirExecExtCF_trait_cone_narrow`,
     `vcMirWithCalleesCF`, `vcMirWithCalleesCF_narrow_of_batchedCert`,
     `vcMirWithCalleesCF_narrow_unfiltered_of_batchedCert`), instantiated in
     `test_partB_whole_exec_lossless`.
  3. Added a concrete interprocedural `.call` + `.return_` borrow-monotone trace
     (`protoInterprocCallReturnBorrowTrace`, `test_partC_interproc_call_return_trace_borrowAware`)
     that mints stack borrows in both caller (`tag = 1`, `depth = 0`) and callee (`tag = 2`,
     `depth = 1`), invokes `caller_location` in both frames, and executes `.return_` to disable the
     callee borrow (`tag = 2` → `.disabled`) via `disableFrameBorrows` while keeping the caller borrow
     active.

---

## 5. Conditions for Track A Promotion

1. **`allocId` / borrow-tag namespace: closed for `traceBorrowMonotone` traces.**
   - `runDemandCallerLocationTrace_borrowAware_spec` and `demandCallerLocation_bisim_eager_borrowAware`
     prove that returned `Location` pointers, read through `readLocationsBorrowAware` (`lookupBorrow`
     before `lookupGlobalAlloc`) in the final memory, match `CallerLocationSite.resolve` and bisimulate
     the eager world.
   - This holds on every trace of `isBorrowMonotoneStmt` statements, `isBorrowMonotoneTerminator`
     terminators, and `caller_location` invocations, including interprocedural `.call` + `.return_`
     traces that mint stack borrows across call frames and disable callee borrows on `.return_`
     (`test_partC_interproc_call_return_trace_borrowAware`).
   - On `protoBorrowMonotoneTrace` an allocator using only `nextAllocId` would hand out id `1`, which
     is the live `&mut _2` tag (`test_partC_borrowAware_needed`).
   - *Residual*:
     - `copy_nonoverlapping`, unsizing / fn-ptr cast rvalues, intrinsic calls and calls through
       function pointers are excluded.
     - The trace runners use a single `localDecls`/`layouts` for statement steps.
2. **Implicit writes: closed for the overlay's scope.** The fresh child is written with the
   `Trusted` write transition and UB checks. Reconcile with V2026_08_01's `initProtectedReborrowPerm`
   on schema bump.
3. **Statement and terminator frame in Part C: closed for `isBorrowMonotoneStmt` and
   `isBorrowMonotoneTerminator` on arbitrary `Memory`.** `evalStmt_borrowMonotone_frame`,
   `normalStmtStep_eq_raw_of_borrowMonotone`, `evalTerminator_borrowMonotone_frame` and
   `normalTerminatorStep_eq_raw_of_borrowMonotone` cover these with live borrows and protectors.
   *Residual*: same as condition 1.
4. **Trie depth: closed** (`adaptiveRetagTrieDepth` + `adaptiveRetagTrieDepth_bitPath_injective`,
   exercised at `D = 5000`).
5. **External calls: closed per step; whole-execution closed for mixed cones with summarized externals
   (standard WP) and for arbitrary `extEnv` with full narrowing under the code-frame WP.** What is
   proved:
   - **Soundness of cone filtering, for every execution:** `wpMirExecExt_mono_cone`.
   - **Step-level safety for all three call forms** (`call`, diverging `call -> !`, `tailCall`):
     `stepMirFn_extCallInCone`, `closedInvPoly_resumeExternalCall`,
     `closedInvPoly_resumeExternalDivergingCall`, `closedInvPoly_resumeExternalTailCall`,
     `stepMirFn_extCallSafe`.
   - **Whole-execution losslessness, standard `wpMirExecExt` on mixed cones:**
     `wpMirExecExt_cone_iff_unfiltered_of_mixed_cone` proves `wpMirExecExt ↔ wpMirExecExtUnfiltered`
     whenever every call in `root` and `coneBodies cone c₁` either resolves internally via
     `lookupCallee c₁ _ _ _ ti₁` or has an external summary in `extEnv`
     (`coneCallsResolveOrSummarized`, compatible with `UntrustedAdmissible`,
     `test_partB_mixed_cone_standard_wp_lossless`), alongside the all-external special case
     `wpMirExecExt_cone_iff_unfiltered_of_summarized` (`summarizedCone_has_no_internal_body`).
   - **Whole-execution losslessness and narrowing, code-frame `wpMirExecExtCF`:**
     `wpMirExecExtCF_cone_iff_unfiltered`, `wpMirExecExtCF_trait_cone_narrow`,
     `vcMirWithCalleesCF_narrow_of_batchedCert`, and
     `vcMirWithCalleesCF_narrow_unfiltered_of_batchedCert` prove both cone-filtering losslessness and
     callee/trait/summary narrowing for every `extEnv` and `contracts` (`test_partB_whole_exec_lossless`).
     This WP is weaker than the standard one (`wpMirExecExt_imp_wpMirExecExtCF`) and is sound for real
     executions when external calls do not replace the linked code frame.

   *Residual*: bake `AnsPreservesCodeFrame` into `MirLiftCore`'s external-call semantics so standard
   `wpMirExecExt` inherits unsummarized havoc losslessness without a separate `CF` variant.
6. **Hoisting: closed.** `checkBatchedVcConeNarrowCertGeneral`, `BatchedVcConeNarrowCert.ofCheckGeneral`
   and `traitFilterCovers_hoist_selectByMask` handle arbitrary keep/drop masks, including mixed trait
   partitions.
7. **Symbolic payoff: measured on the prototype; amortization required.**
   - On `symTrait_vc_narrow` at `M = 128`, the narrowed table needs 1.26× fewer heartbeats
     per VC.
   - The one-time certificate costs 2.23× that saving, so narrowing wins from
     3 VCs per certificate.
   - The measured 3-VC batch (`test_partB_symVC_batch3_transfer_128`) costs `16,415,992` hb with
     narrowing vs. `17,339,316` hb without (net `923,324` hb).
   - Sealed coercions need 1.74× fewer heartbeats on the `∀ bits` chain.

   *Residual*: benchmark multi-function crate VCs end-to-end under `cargo anneal`, with certificate
   reuse across VCs.

### Proposed 2-Episode Track A Plan
1. `ep1`: Part A and Part D into `theory/Anneal/SparseRetagAndVcNarrow.lean` (conditions 2, 4).
2. `ep2`: Part B and Part C (conditions 1, 3, 5–7), exported from `theory/Anneal.lean`, with this
   test suite as the regression gate.
