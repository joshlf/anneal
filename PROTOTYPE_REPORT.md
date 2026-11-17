# Prototype Evaluation Report — `ws-proto-sparse-retag-index-and-batched-vc-narrow`

- **Prototype Branch**: `refs/heads/prototype/ws-proto-sparse-retag-index-and-batched-vc-narrow/ep1-proto-sparse-retag-index-and-batched-vc-narrow`
- **Base `unstable` Commit SHA**: `1e208d1a9d6cce3326f6330ef2aecf942fe7d39d`
- **Paired Track A Workstream**: `ws-sparse-retag-index-and-batched-vc-narrow`
- **Deliverables** (the only files changed vs. base):
  - `theory/Anneal/SparseRetagAndVcNarrowPrototype.lean`
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean`
  - `PROTOTYPE_REPORT.md`
- **Kernel & Axiom Audit** (bottom of the test file, on the final code): `axiom audit passed: 2167 declarations (365 prototype theorems, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 leaked constants, 0 placeholder uses, 10 conditional test lemmas all discharged, 100% theorem reachability from closed test witnesses)`
  - All theorems depend only on `{propext, Quot.sound}`. The audit's self-tests confirm that it flags
    `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, an elaborated `have _ := @thm` placeholder,
    and a test statement that assumes an undischarged hypothesis. Reachability is computed only
    from *closed* test witnesses (no assumed hypotheses other than bounded membership `x ∈ l`).
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean` starts with `import Anneal` +
    `import Anneal.SparseRetagAndVcNarrowPrototype` and elaborates cleanly (no symbol/instance collisions).
- **Overall Recommendation**: **CONDITIONAL GO**. All four mechanisms are kernel-checked (`0 sorry`,
  `0 Classical.choice`) over `Trusted.Rustc.V2026_06_01` and `Anneal.MirLiftCore`. Conditions 2, 4
  and 6 in §5 are closed. Conditions 1 and 3 are closed across all `isBorrowMonotoneStmt` statements
  and all `Terminator`s (`evalTerminator_borrowMonotone_frame`). Condition 5 (external calls) now
  includes external tail calls (`closedInvPoly_resumeExternalTailCall`) and two whole-execution
  lossless cone-filtering theorems (`wpMirExecExt_cone_iff_unfiltered_of_summarized` and
  `wpMirExecExtCF_cone_iff_unfiltered`). Condition 7 (symbolic payoff) is measured and demonstrated
  on a 3-VC batch sharing one certificate (`test_partB_symVC_batch3_transfer_128`).

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
- Cone filtering is conservative AND whole-execution lossless:
  - Conservativity (for all fuel, states, contracts, and summary environments): `coneSummary?_mono`
    and `wpMirExecExt_mono_cone`.
  - Joint step-level external-call safety (`NodeExtCallSafe`): `nodeExtCallSafe_of_empty_cone`,
    `evalTerminator_extCallSafe`, and `stepMirFn_extCallSafe` prove that every external call emitted
    from a `ClosedInvPoly` state targets `cone` AND resumes into a `ClosedInvPoly` state on any
    `AnsPreservesCodeFrame` answer.
  - Whole-execution losslessness (both formulations):
    1. `wpMirExecExt_cone_iff_unfiltered_of_summarized`: when cone paths are summarized in `extEnv`
       and summary contracts imply `AnsPreservesCodeFrame`, cone-filtered `wpMirExecExt` is equivalent
       (`↔`) to unfiltered `wpMirExecExtUnfiltered` for all `fuel` steps.
    2. `wpMirExecExtCF_cone_iff_unfiltered` and `vcMirWithCalleesCF_narrow_unfiltered_of_batchedCert`:
       for code-frame-preserving external answers (`wpMirExecExtCF`), cone filtering is unconditionally
       equivalent (`↔`) to unfiltered `wpMirExecExtCFUnfiltered` across **every** `extEnv` (including
       unsummarized havoc) and **every** `contracts` (`test_partB_whole_exec_lossless`).
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
    `.assert`, `.tailCall`, diverging `.call`, and non-intrinsic `.call`):
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
    `test_partC_borrowMonotone_and_trace_borrowAware` and on `protoCallReturnBorrowTrace` in
    `test_partC_terminator_trace_borrowAware`).

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
| 16 | `67,541` hb (`9.7` ms) | `146,852` hb (`22.8` ms) | `438,921` hb (`73.2` ms) |
| 64 | `577,569` hb (`79.0` ms) | `634,328` hb (`109.8` ms) | `1,752,176` hb (`325.4` ms) |
| 128 | `2,117,815` hb (`320.4` ms) | `1,420,921` hb (`250.0` ms) | `3,559,290` hb (`781.7` ms) |
| 256 | `8,147,437` hb (`1,603.3` ms) | `3,226,248` hb (`810.5` ms) | `7,285,268` hb (`1,734.3` ms) |

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
| 16 | `562,740` hb (`100.9` ms) | `1,623,914` hb (`260.3` ms) | `588,017` hb (`130.2` ms) | `451,995` hb (`93.4` ms) |
| 64 | `670,415` hb (`124.6` ms) | `2,066,843` hb (`361.7` ms) | `781,839` hb (`135.3` ms) | `452,001` hb (`125.2` ms) |
| 128 | `813,904` hb (`136.8` ms) | `2,657,379` hb (`422.7` ms) | `1,040,238` hb (`168.6` ms) | `451,990` hb (`81.1` ms) |

- The cached arm's literal table is proved equal (`rfl`) to the computed narrowing
  (`cachedNarrow_eq_computed_*`).
- Steady state at `M = 128`: the cached narrowed run uses 1.80× fewer heartbeats than the
  full table. Recomputing the narrowing on every run is slower than the full table. The one-time
  certificate costs 3.26× a full run.
- Concrete VC discharge by elaborator `rfl` (`M = 128`; *not* a symbolic VC): full table
  `3,861,419` hb (`377.7` ms) vs. cached narrowed table `2,160,650` hb (`239.8` ms)
  (1.79×).
- Symbolic VC (`∀ x : Nat`, `symTraitRootMir`, `M = 128`, identical tactic script on all arms):

  | Full table (`x % 1000`) | Cached narrowed #1 (`x % 1000`) | Cached narrowed #2 (`x % 65536`) | Cached narrowed #3 (`x % 1000000`) | One-time certificate (`PartB_symVC_cert_M128`) |
  | ---: | ---: | ---: | ---: | ---: |
  | `5,780,402` hb (`592.3` ms) | `4,578,219` hb (`480.4` ms) | `4,775,699` hb (`489.8` ms) | `4,775,828` hb (`515.6` ms) | `2,681,868` hb (`422.0` ms) |

  - Per VC (`x % 1000`), the narrowed table saves `1,202,183` hb (1.26×).
    `symCachedNarrow_eq_computed_128` proves the cached table is the certified narrowing.
    `test_partB_symVC_transfer_128` turns the narrowed-table proof plus the certificate into the
    full-table VC.
  - The certificate costs 2.23× the per-VC saving. Certifying and proving a single VC
    on the narrowed table therefore costs `7,260,087` hb, versus `5,780,402` hb
    on the full table.
  - Narrowing pays off when one certificate is shared by at least 3 VCs over the
    same cone (`test_partB_symVC_batch3_transfer_128`: `1 × cert + narrowCached + narrowCached2 + narrowCached3 = 16,811,614` hb vs. `3 × full = 17,341,206` hb, a net saving of `529,592` hb; or `1 × cert + 3 × narrowCached = 16,416,525` hb, a net saving of `924,681` hb).
- Coercion (`∀ bits`, 16 chained coercions, the same `simp only` script shape): sealed
  `coerceValueAt` rewritten by `coerceValueAt_u32` `257,266` hb (`31.9` ms) vs. a reducible copy
  unfolded by `dsimp`/`simp` `447,044` hb (`39.5` ms) (1.74×).

### 2.3 Part C — eager pre-allocation vs. demand-time `Location` (same trace in both worlds)

| Sites `S` | Eager, non-panicking (8 stmts) | Demand, non-panicking | Eager, panicking (1 invocation) | Demand, panicking |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `130,094` hb (`28.6` ms) | `53,136` hb (`6.8` ms) | `237,358` hb (`32.3` ms) | `197,025` hb (`24.9` ms) |
| 64 | `762,203` hb (`105.6` ms) | `53,157` hb (`7.0` ms) | `394,591` hb (`54.7` ms) | `197,056` hb (`27.7` ms) |
| 128 | `2,508,201` hb (`390.6` ms) | `53,167` hb (`7.7` ms) | `625,839` hb (`82.9` ms) | `197,037` hb (`27.6` ms) |

- Demand cost is independent of `S`; the eager arm materializes `S + 1` globals (checked). Its
  super-linear growth is partly an artifact of the list-based `Memory.globals` model.

### 2.4 Part D — eager vs. lazy distinct-address write chains (`cap = 128`, read of the last write)

| Writes `N` | Eager (`mkEagerWrite`) | Lazy (`mkLazyWrite`) | Proved spine inspections (eager / lazy) |
| :--- | ---: | ---: | ---: |
| 16 | `121,659` hb (`16.8` ms) | `60,093` hb (`7.0` ms) | 136 / 16 |
| 64 | `1,226,877` hb (`185.1` ms) | `113,415` hb (`15.7` ms) | 2080 / 64 |
| 128 | `4,728,561` hb (`888.9` ms) | `184,016` hb (`26.3` ms) | 8256 / 128 |

- Wide-shift canary (`shift = 2^64`, six safe shifts, one `decide +kernel`): `140,183` hb (`10.1` ms).

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
  `test_partB_whole_exec_lossless` (whole-execution equivalence between cone-filtered and unfiltered
  contract-aware WP on `protoTwoExtCallsRootMir` with an extra out-of-cone summary `ext::unrelated`,
  and on `traitCallRootMir` under `wpMirExecExtCF`), `symTrait_vc_narrow` +
  `test_partB_symbolic_trait_vc` (symbolic `∀ x : Nat` VC over polymorphic + trait-dispatched
  `AddUnchecked` calls), `test_partB_symbolic_vc_range` (largest admissible input `2^32 - 32`;
  overflow canary at `4294967290`), `test_partB_symVC_transfer_128`, and
  `test_partB_symVC_batch3_transfer_128` (3 symbolic VCs sharing the single `bench_partB_symVC_cert_128`
  certificate transferred to the full 128-entry table).
- **Part C**: `demandCallerLocation_filename_dedup`, `canary_demandLocation_borrowTag_disjoint`,
  `trackCaller_span_owner_policy`, `trackCaller_stops_at_nonTrackCaller_frame`, bisimulation for all
  8 policies on a trace with a repeated site, explicit `AllocRenamingRel`,
  `test_partC_stmt_pure_memory`, `test_partC_borrowMonotone_and_trace_borrowAware` (full borrow-aware
  bisimulation through `readLocationsBorrowAware` across `protoBorrowMonotoneTrace`, which mints stack
  borrows via `Rvalue.ref` and `StatementKind.retag` both before and after `caller_location`),
  `test_partC_terminator_trace_borrowAware` (borrow-aware bisimulation and `normalTerminatorStep_eq_raw_of_borrowMonotone`
  across `protoCallReturnBorrowTrace`, interleaving `.goto` and `.drop` terminators with `&mut _2`
  borrow creation, `.retag`, and `.invokeCallerLocation`), and `test_partC_borrowAware_needed` (on
  that trace an allocator using only `nextAllocId` would give the `Location` the live borrow tag `1`).
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
     (unconditional whole-execution losslessness across arbitrary `extEnv` and `contracts` when
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

---

## 5. Conditions for Track A Promotion

1. **`allocId` / borrow-tag namespace: closed across `isBorrowMonotoneStmt` statements and all `Terminator`s.**
   - `runDemandCallerLocationTrace_borrowAware_spec` and `demandCallerLocation_bisim_eager_borrowAware`
     prove that returned `Location` pointers, read through `readLocationsBorrowAware` (`lookupBorrow`
     before `lookupGlobalAlloc`) in the final memory, match `CallerLocationSite.resolve` and bisimulate
     the eager world.
   - This holds on every `traceBorrowMonotone` trace (including `.normalStep` statements and
     `.terminatorStep` terminators that mint or disable stack borrow tags before and after
     `caller_location`, exercised on `protoBorrowMonotoneTrace` and `protoCallReturnBorrowTrace`).
     On `protoBorrowMonotoneTrace` an allocator using only `nextAllocId` would hand out id `1`, which
     is the live `&mut _2` tag (`test_partC_borrowAware_needed`).
   - *Residual*: `copy_nonoverlapping` and unsizing / fn-ptr cast rvalues are outside
     `isBorrowMonotoneStmt`.
2. **Implicit writes: closed for the overlay's scope.** The fresh child is written with the
   `Trusted` write transition and UB checks. Reconcile with V2026_08_01's `initProtectedReborrowPerm`
   on schema bump.
3. **Statement and terminator frame in Part C: closed for `isBorrowMonotoneStmt` and `isBorrowMonotoneTerminator` on arbitrary `Memory`.**
   `evalStmt_borrowMonotone_frame`, `normalStmtStep_eq_raw_of_borrowMonotone`,
   `evalTerminator_borrowMonotone_frame`, and `normalTerminatorStep_eq_raw_of_borrowMonotone` cover these statements
   and terminators with live borrows and protectors. *Residual*: same as condition 1.
4. **Trie depth: closed** (`adaptiveRetagTrieDepth` + `adaptiveRetagTrieDepth_bitPath_injective`,
   exercised at `D = 5000`).
5. **External calls: closed for summarized cone externals (`wpMirExecExt`) and code-frame-preserving havoc (`wpMirExecExtCF`).** What is proved:
   - **Soundness of cone filtering, for every execution:** `wpMirExecExt_mono_cone`.
   - **Step-level external-call safety across all 3 call forms (`call`, diverging `call -> !`, `tailCall`):**
     `stepMirFn_extCallInCone`, `closedInvPoly_resumeExternalCall`,
     `closedInvPoly_resumeExternalDivergingCall`, `closedInvPoly_resumeExternalTailCall`, and
     `stepMirFn_extCallSafe`.
   - **Whole-execution losslessness:**
     1. `wpMirExecExt_cone_iff_unfiltered_of_summarized`: when cone paths are summarized in `extEnv`
        and summary contracts imply `AnsPreservesCodeFrame`, cone-filtered `wpMirExecExt` is equivalent
        (`↔`) to unfiltered `wpMirExecExtUnfiltered` for all `fuel` steps.
     2. `wpMirExecExtCF_cone_iff_unfiltered` and `vcMirWithCalleesCF_narrow_unfiltered_of_batchedCert`:
        for code-frame-preserving external answers (`wpMirExecExtCF`), cone filtering is unconditionally
        equivalent (`↔`) to unfiltered `wpMirExecExtCFUnfiltered` across **every** `extEnv` (including
        unsummarized havoc) and **every** `contracts`.

   *Residual*: in unguarded `wpMirExecExt`, an unsummarized (`none`) external call quantifies over
   arbitrary `MirCallAns` values including synthetic answers that overwrite `Memory.callees` or
   `Memory.activeCallee`; Track A should bake `AnsPreservesCodeFrame` into `SymbolicEval.evalNodeWP`
   (as in `evalNodeWPExtCF`) so unsummarized havoc cannot corrupt the linked code table.
6. **Hoisting: closed.** `checkBatchedVcConeNarrowCertGeneral`, `BatchedVcConeNarrowCert.ofCheckGeneral`
   and `traitFilterCovers_hoist_selectByMask` handle arbitrary keep/drop masks, including mixed trait
   partitions.
7. **Symbolic payoff: measured on the prototype; amortized 3-VC batch win demonstrated.**
   - On `symTrait_vc_narrow` at `M = 128`, the narrowed table needs 1.26× fewer heartbeats
     per VC (`4,578,219` hb vs. `5,780,402` hb).
   - The one-time certificate costs `2,681,868` hb (2.23× the single-VC saving), so narrowing breaks
     even at `≥ 3` VCs sharing one certificate (`test_partB_symVC_batch3_transfer_128`: `1 × cert + narrowCached + narrowCached2 + narrowCached3 = 16,811,614` hb vs. `3 × full = 17,341,206` hb, a net saving of `529,592` hb; or `1 × cert + 3 × narrowCached = 16,416,525` hb, a net saving of `924,681` hb).
   - Sealed coercions need 1.74× fewer heartbeats on the `∀ bits` chain.

   *Residual*: benchmark multi-function crate VCs end-to-end under `cargo anneal`, with certificate
   reuse across VCs.

### Proposed 2-Episode Track A Plan
1. `ep1`: Part A and Part D into `theory/Anneal/SparseRetagAndVcNarrow.lean` (conditions 2, 4).
2. `ep2`: Part B and Part C (conditions 1, 3, 5–7), exported from `theory/Anneal.lean`, with this
   test suite as the regression gate.
