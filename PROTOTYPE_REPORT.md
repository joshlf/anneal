# Prototype Evaluation Report — `ws-proto-sparse-retag-index-and-batched-vc-narrow`

- **Prototype Branch**: `refs/heads/prototype/ws-proto-sparse-retag-index-and-batched-vc-narrow/ep1-proto-sparse-retag-index-and-batched-vc-narrow`
- **Base `unstable` Commit SHA**: `1e208d1a9d6cce3326f6330ef2aecf942fe7d39d`
- **Paired Track A Workstream**: `ws-sparse-retag-index-and-batched-vc-narrow`
- **Deliverables** (the only files changed vs. base):
  - `theory/Anneal/SparseRetagAndVcNarrowPrototype.lean`
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean`
  - `PROTOTYPE_REPORT.md`
- **Kernel & Axiom Audit** (bottom of the test file, on the final code): `axiom audit passed: 1733 declarations (241 prototype theorems, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 leaked constants, 0 placeholder uses, 100% theorem reachability)`
  - All theorems depend only on `{propext, Quot.sound}`; the audit's self-tests confirm it flags
    `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, and an elaborated `have _ := @thm` placeholder.
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean` starts with `import Anneal` +
    `import Anneal.SparseRetagAndVcNarrowPrototype` and elaborates cleanly (no symbol/instance collisions).
- **Overall Recommendation**: **GO** — all four mechanisms are formally verified over the real
  `Trusted.Rustc.V2026_06_01` and `Anneal.MirLiftCore` / `Anneal.PureMirExec` stack, and all seven
  Track A integration conditions identified in `[adv B1]` §5 have been closed with kernel proofs and
  canaries in `[adv A1]` (see §4 and §5).

---

## 1. What Is Proved (theorem names as they exist in the module)

### Part A — `SparseRetagAttrIndex` (`proofs-rs/lean-miri` PR #68)
- `linearScanRetagAttr` mirrors `lean-miri`'s `CompilerRetagOptions.rustcNoWritable`: frame check
  first, then a left-to-right whole-table scan with an `O(M)` duplicate check per row (so `O(M²)`
  per query).
- `NatBitTrie (depth : Nat := defaultRetagTrieDepth)` and `adaptiveRetagTrieDepth (definitionCount : Nat) := max defaultRetagTrieDepth (definitionCount.log2 + 1)`:
  `natLowBits_inj_of_lt_pow2`, `lt_two_pow_adaptiveRetagTrieDepth`, and
  `adaptiveRetagTrieDepth_bitPath_injective` prove that `2 ^ adaptiveRetagTrieDepth D > D` for every
  `D > 0` and that every in-bounds `id < definitionCount` has a unique bit path (leaf buckets have
  size `≤ 1`, so lookup is strictly `O(log D)` with zero bucket collisions).
- `prepareSparseRetagIndex` builds the binary radix trie once with adaptive depth
  `adaptiveRetagTrieDepth definitionCount`, caching any table error in `Except`;
  `lookupSparseRetag` checks `.frameAbsent` first.
- `lookupSparseRetag_eq_linearScan`: exact equality with the oracle for **all** `definitionCount`,
  `rows`, `id` (error precedence included); `frameAbsent_precedes_malformedTable`;
  `lookupSparseRetag_cert` / `lookupSparseRetag_miss_cert`; `SparseDefPathRetagIndex.get?_insert`.
- Operational overlay `evalFnEntryRetagWithSparseAttr` over `Trusted` `evalStmt`:
  `evalFnEntryRetagWithSparseAttr_eq_linear`, `unusedMalformedTable_demand_local`,
  `evalFnEntryRetagWithSparseAttr_implicitWrites_false`,
  `evalFnEntryRetagWithSparseAttr_rustcNoWritable_true`,
  `applyImplicitWriteUpgrade_of_no_fresh_child` (the implicit-write upgrade only ever touches the
  child tag freshly created by the retag), `applyImplicitWriteUpgrade_cell_noop` (`.cell` on
  `&mut UnsafeCell<T>` is preserved, never overwritten to `.unique`), and
  `canary_implicitWrite_treeBorrows_full` (ancestor `.frozen` child-write UB check
  `treeBorrowAncestorsChildAccessUB .write`, foreign protector conflict check
  `hasProtectedTreeWriteConflict`, and foreign sibling `.disabled` transitions via
  `invalidateTreeBorrowsAtProj`).

### Part B — `BatchedVcConeNarrowCert` + `hoistTraitImpls` / `hoistMaskTraitImpls` + `@[irreducible] coerceValueAt`
- Boolean checkers `checkBatchedVcConeNarrowCert` and `checkBatchedVcConeNarrowCertMask` (each one
  `decide +kernel`), with `BatchedVcConeNarrowCert.ofCheck` and
  `BatchedVcConeNarrowCert.ofCheckMask` deriving **every** field of the propositional certificate.
  `hoistMaskTraitImpls` + `checkMaskTraitPartition` (`traitFilter_hoistMask_eq`) hoist
  `TraitImplEntry` records ONLY from dropped bodies (`!b`), allowing kept `impl` bodies in
  `rustc-capture` layout to retain their own `TraitImplEntry` without duplicate dispatch records
  (`canary_keptBodyWithTraitImpl_accepted`).
- First-match preservation without `CapturedMir` equality: `checkMaskKeepsFirstMatch` +
  `calleesAgreeOn_selectByMask` (duplicate shadowing included).
- `computeBatchedVcNarrowCert` / `collectTraitConeBodies` compute `(cone, mask, narrowExt)`;
  `selectByMask_coneMask` shows the canonical mask selects exactly `coneBodies`.
- Trait-aware congruence: `resolveCalleeBodyAndArgs?_eq_of_traitConeAgree`,
  `lookupCallee_eq_of_traitConeAgree`, `evalTerminator_withCalleesAndTraits`,
  `stepMirFn_withCalleesAndTraits`, `coneReach_of_closedInvTrait`.
- Reachable external calls stay in the cone: `evalStmt_extCallInCone`,
  `evalTerminator_extCallInCone`, `stepMirFn_extCallInCone`, and
  `coneSummary?_eq_of_stepMirFn_extCall` (`coneSummary? cone extEnv req.defPath = findExternalSummary? extEnv req.defPath`
  for every external call `req` emitted by a cone-safe state).
- Core theorems: `runMirExecBounded_narrow_of_batchedCert`, `wpMirExecSym_narrow_of_batchedCert`,
  `vcMirWithCallees_narrow_of_batchedCert`.
- `vcMirWithCallees` is a contract-aware WP (`wpMirExecExt`): `wpMirExecExt_nil_iff`,
  `wpMirExecExt_of_wpMirExecSym`, `wpMirExecExt_trait_cone_narrow`, `canary_externalSummary_vc`,
  and `canary_coercedExternalSummary_vc` (connecting `@[irreducible] coerceValueAt` and
  `coerceValueAt_u32` directly to `vcMirWithCallees`).
- `coerceValueAt` is `@[irreducible]` (meta-level opacity audit at `.default` vs `.all`) with
  `coerceValueAt_u32`, `coerceValueAt_bool`, `coerceValueAt_ref`, `coerceValueAt_adt_exact`,
  `coerceValueAt_idempotent`.

### Part C — `DemandCallerLocationEnv` (`proofs-rs/lean-miri` PR #67 Schema 15)
- `FrameLocMeta` (`callSitePos : Option SourceExpansionPos`, `isTrackCaller`, `detailPolicy`),
  `CallerLocationSite.resolve` = `find_closest_untracked_caller_location` with the redaction policy of
  the crate owning the resolved span; `resolveCallerLocationAux_eq_topDown` (bottom-up walk = Miri's
  top-down `trackCallerArg` propagation).
- Disjoint global `allocId` / stack borrow `tag` allocation: `evalDemandCallerLocation` draws fresh
  ids from `nextFreshGlobalAndTagId mem = max mem.nextAllocId mem.nextTag` and advances both
  `nextAllocId` and `nextTag` past every materialized allocation; `lookupBorrow_eq_none_of_lt`,
  `evalDemandCallerLocation_borrowAware_spec`, and `canary_demandLocation_borrowTag_disjoint` prove
  that returned `Location` pointers have `lookupBorrow = none` and dereference cleanly through
  `readLocationBorrowAware` (`lookupBorrow` before `lookupGlobalAlloc`, matching `Trusted`
  semantics).
- Statement memory frame theorem: `evalStmt_pure_memory_eq` and `normalStmtStep_eq_raw_of_pure`
  (proved from `Anneal.PureMirExec.evalStmt_toMachineState_eq_withMem_of_frameFree`) prove that on
  pure statements and frame-free memory, `evalStmt` leaves `Memory` (`globals`, `nextAllocId`,
  `nextTag`) unchanged without any artificial field overwrite.
- General theorems over **all** call-site tables, **all** traces and all 8 policies:
  `evalDemandCallerLocation_spec`, `runDemandCallerLocationTrace_spec`, `eagerInitAux_spec`,
  `demandCallerLocation_bisim_eager`, `demandCallerLocation_no_call_zero_allocs`,
  `eagerCallerLocation_clutter`, `allocRenamingRel_of_readLocations`.

### Part D — `LazyWriteChain` & total shifts
- `mkLazyWrite w` checks bounds against the static width `w` in `O(1)`; `eval_mkLazyWrite`,
  `eval_mkEagerWrite`, `eval_mkLazyRead` (all for `symArrayLen arr = w`).
- Step counts are proved on instrumented copies of both write and read implementations
  (`mkLazyWriteCounted_fst`, `stripShadowedWritesCounted_fst`, `stripShadowedWritesCounted_snd`,
  `mkEagerWriteCounted_fst`, `lazyDistinctChainCounted_fst`, `eagerDistinctChainCounted_fst`,
  `lazyReadSpineCounted_fst`, `mkLazyReadCounted_fst`, `mkLazyReadCounted_hit_top`):
  `lazyWriteChain_distinctAddrs_steps_eq_N` (`N`),
  `eagerWriteChain_distinctAddrs_steps_quadratic` (`N(N+1)/2`),
  `mkLazyReadCounted_hit_top` (`1` spine inspection on top-write hit), and
  `buildLazyDistinctChain_eq_eager`.
- `bvShlSafe_eq`, `bvLshrSafe_eq`, `bvAshrSafe_eq`, `shiftLeftBitsSafe_eq` (all inputs),
  `shiftRightUnsignedBitsSafe_eq` (canonical inputs), `arithmeticShrBitsSafe_eq` (all inputs),
  and `canary_wideShift_two_pow_64` (kernel evaluation at `shift = 2^64`).

---

## 2. Benchmarks (measured by `tests/mir/SparseRetagAndVcNarrowProtoTests.lean`)

Methodology: every arm is a theorem discharged by `decide +kernel` (or symbolic elaboration for the
universally quantified symbolic VC and 16-step coercion chain benchmarks); `IO.getNumHeartbeats`
deltas are deterministic across runs, wall-clock (`IO.monoNanosNow`) is from the final receipt run.

### 2.1 Part A — linear oracle vs. sparse index (`definitionCount = 512`)

| Rows `M` | Linear oracle, 1 query | Sparse: prepare + 1 query | Sparse: prepare + `M` queries |
| :--- | ---: | ---: | ---: |
| 16 | `67,532` hb (`9.5` ms) | `146,855` hb (`23.8` ms) | `438,918` hb (`74.7` ms) |
| 64 | `577,582` hb (`82.3` ms) | `634,341` hb (`104.4` ms) | `1,752,173` hb (`310.9` ms) |
| 128 | `2,117,808` hb (`308.6` ms) | `1,420,922` hb (`239.7` ms) | `3,559,282` hb (`655.7` ms) |
| 256 | `8,147,442` hb (`1,942.8` ms) | `3,226,252` hb (`611.2` ms) | `7,285,273` hb (`1,474.5` ms) |

- The linear oracle grows ~4× per doubling of `M` (quadratic per query). Including preparation,
  the sparse index is slower for a single query at `M = 16` (2.17× the linear cost), roughly even
  at `M = 64`, and faster from `M = 128` (1.49×) to `M = 256` (2.53×).
- Answering **all** `M = 256` queries with the sparse index (`7,285,273` hb) costs less than **one**
  linear-oracle query at `M = 256` (`8,147,442` hb).

### 2.2 Part B — full callee table vs. certified narrowing & `@[irreducible] coerceValueAt`

| Callees `M` | Full table run | Cert check (compute cone + mask, 1 `decide`) | Narrowed run (narrowing computed in-kernel) | Narrowed run (cached narrowed table) |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `562,773` hb (`108.0` ms) | `1,623,899` hb (`314.1` ms) | `588,035` hb (`258.9` ms) | `451,983` hb (`189.3` ms) |
| 64 | `670,399` hb (`117.2` ms) | `2,066,861` hb (`317.5` ms) | `781,850` hb (`116.9` ms) | `452,014` hb (`68.5` ms) |
| 128 | `813,918` hb (`110.0` ms) | `2,657,374` hb (`395.3` ms) | `1,040,223` hb (`154.5` ms) | `451,981` hb (`72.2` ms) |

- **Symbolic VC narrowing (`∀ x : Nat, vcMirWithCallees ...` at `M = 128`)**:
  - Full callee table (`fullCallees128`): `4,854,355` hb (`469.9` ms)
  - Narrowed callee table (`[protoPoly, protoCircleArea]` + `[protoAreaEntry]`): `3,148,705` hb (`366.3` ms) — **1.54× fewer heartbeats** (`1,705,650` hb saved per symbolic VC!).
- **16-step chained coercion (`∀ bits : Nat, chainCoerce* 16 (.scalar ⟨bits, 4⟩) = ...`)**:
  - Sealed `@[irreducible] coerceValueAt` via `coerceValueAt_u32` + `coerceValueAt_idempotent`: `95,568` hb (`7.1` ms)
  - Unsealed `coerceValueAtUnsealed` via `dsimp`/`simp`: `447,319` hb (`40.8` ms) — **4.68× fewer heartbeats** (`5.7×` faster wall-clock) when sealed!

### 2.3 Part C — eager pre-allocation vs. demand-time `Location` (same trace in both worlds)

| Sites `S` | Eager, non-panicking (8 stmts) | Demand, non-panicking | Eager, panicking (1 invocation) | Demand, panicking |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `129,852` hb (`19.7` ms) | `52,897` hb (`6.4` ms) | `237,114` hb (`30.9` ms) | `196,824` hb (`23.4` ms) |
| 64 | `761,971` hb (`103.1` ms) | `52,914` hb (`7.3` ms) | `394,365` hb (`53.6` ms) | `196,797` hb (`26.0` ms) |
| 128 | `2,507,962` hb (`364.7` ms) | `52,908` hb (`6.9` ms) | `625,509` hb (`84.4` ms) | `196,784` hb (`26.8` ms) |

- Demand cost is independent of `S` (`~52,908` hb non-panicking, `~196,784` hb panicking); at
  `S = 128`, demand-time reduces non-panicking heartbeats by **47.4×** (`2,507,962` → `52,908` hb).

### 2.4 Part D — eager vs. lazy distinct-address write chains (`cap = 128`, read of the last write)

| Writes `N` | Eager (`mkEagerWrite`) | Lazy (`mkLazyWrite`) | Proved spine inspections (eager / lazy) |
| :--- | ---: | ---: | ---: |
| 16 | `121,640` hb (`17.5` ms) | `60,042` hb (`6.9` ms) | 136 / 16 |
| 64 | `1,226,867` hb (`222.1` ms) | `113,395` hb (`19.4` ms) | 2080 / 64 |
| 128 | `4,728,533` hb (`884.0` ms) | `184,008` hb (`27.2` ms) | 8256 / 128 |

- Wide-shift canary (`shift = 2^64`, all six safe shifts, one `decide +kernel`): `140,214` hb (`10.5` ms).

---

## 3. Canaries (all kernel-checked)

- **Part A**: hit/miss certificates on the prepared index; `.duplicateDefQuery`, `.defIdOutOfBounds`,
  `.attrQueryAbsent`, and `.frameAbsent` overriding a malformed table; adaptive trie depth bit-path
  injectivity (`adaptiveRetagTrieDepth_bitPath_injective`); implicit write activates `.reservedFrz false`
  (`rustcNoWritable = false`) but not under `#[rustc_no_writable]`; `.cell` child on `&mut UnsafeCell<T>`
  preserved (`applyImplicitWriteUpgrade_cell_noop`); `.frozen` parent faults to `.ub` and foreign
  `.frozen` sibling is disabled (`canary_implicitWrite_treeBorrows_full`); ZST `&mut ()` fn-entry
  retag leaves `borrows` untouched (`applyImplicitWriteUpgrade_of_no_fresh_child`).
- **Part B**: `canary_naiveNarrow_breaks_trait_dispatch`; `canary_traitDispatch_preserved_under_batchedVcNarrow`;
  `canary_duplicateShadow_rejected`; `canary_externalShadowsInternal_rejected`;
  `canary_missingTraitImplBody_rejected`; `canary_keptBodyWithTraitImpl_accepted` (kept `rustc-capture`
  `impl` body carrying its own `TraitImplEntry` accepted by `checkBatchedVcConeNarrowCertMask` +
  `hoistMaskTraitImpls`); `canary_externalSummary_vc`; `canary_coercedExternalSummary_vc`
  (`@[irreducible] coerceValueAt` integrated with `vcMirWithCallees`); `coneSummary?_eq_of_stepMirFn_extCall`.
- **Part C**: `demandCallerLocation_filename_dedup` (3 allocations at ids `1..3`, `nextAllocId = 4`,
  `nextTag = 4`), `canary_demandLocation_borrowTag_disjoint` (live stack borrow `tag = 1` does not
  shadow demand `Location` pointer under `readLocationBorrowAware`), `trackCaller_span_owner_policy`,
  `trackCaller_stops_at_nonTrackCaller_frame`, bisimulation for all 8 policies on a trace with a
  repeated site, explicit `AllocRenamingRel` on a distinct-site trace.
- **Part D**: OOB fold, same-address collapse, distinct-address `O(1)` stop, top-write `1`-step read
  forwarding (`mkLazyReadCounted_hit_top`), `2^64` shift (`canary_wideShift_two_pow_64`).

---

## 4. Adversarial History

- `[adv A0]` initial implementation (agent-a).
- `[adv B1]` (agent-b) fixed: `vcMirWithCallees` external-summary non-vacuity (`wpMirExecExt`);
  mask-based `selectByMask` + `checkMaskKeepsFirstMatch` + `BatchedVcConeNarrowCert.ofCheck`;
  `computeBatchedVcNarrowCert`; `evalDemandCallerLocation` `nextAllocId` advancement;
  `applyImplicitWriteUpgrade` child-creation check; general `demandCallerLocation_bisim_eager`;
  instrumented `mkLazyWriteCounted` / `mkEagerWriteCounted` step counters; placeholder detector in
  test audit; uniform `decide +kernel` benchmarks.
- `[adv A1]` (agent-a) resolved all 7 open conditions from `[adv B1]` §5:
  1. **Disjoint `allocId` / borrow-tag allocation**: `evalDemandCallerLocation` draws from
     `nextFreshGlobalAndTagId mem = max mem.nextAllocId mem.nextTag` and advances both `nextAllocId`
     and `nextTag`; proved `lookupBorrow_eq_none_of_lt`, `evalDemandCallerLocation_borrowAware_spec`,
     and `canary_demandLocation_borrowTag_disjoint`.
  2. **Full Tree Borrows implicit-write semantics**: `applyImplicitWriteUpgrade` preserves `.cell`
     (`applyImplicitWriteUpgrade_cell_noop`), checks `treeBorrowAncestorsChildAccessUB .write` and
     `hasProtectedTreeWriteConflict`, and applies `invalidateTreeBorrowsAtProj`
     (`canary_implicitWrite_treeBorrows_full`).
  3. **Pure statement memory frame theorem**: proved `evalStmt_pure_memory_eq` and
     `normalStmtStep_eq_raw_of_pure` from `Anneal.PureMirExec.evalStmt_toMachineState_eq_withMem_of_frameFree`.
  4. **Adaptive trie depth & bit-path injectivity**: parameterized `NatBitTrie` by
     `adaptiveRetagTrieDepth definitionCount = max 12 (definitionCount.log2 + 1)` and proved
     `natLowBits_inj_of_lt_pow2`, `lt_two_pow_adaptiveRetagTrieDepth`, and
     `adaptiveRetagTrieDepth_bitPath_injective`.
  5. **Reachable external calls stay in the cone**: proved `evalStmt_extCallInCone`,
     `evalTerminator_extCallInCone`, `stepMirFn_extCallInCone`, and
     `coneSummary?_eq_of_stepMirFn_extCall`.
  6. **Masked trait hoisting for `rustc-capture` layout**: added `dropByMask`, `hoistMaskTraitImpls`,
     `checkMaskTraitPartition`, `traitFilter_hoistMask_eq`, `checkBatchedVcConeNarrowCertMask`,
     `BatchedVcConeNarrowCert.ofCheckMask`, and `canary_keptBodyWithTraitImpl_accepted`.
  7. **Symbolic VC narrowing & chained `coerceValueAt` benchmarks + VC integration**: added
     `canary_coercedExternalSummary_vc`, `PartB_symVC_full_M128` vs `PartB_symVC_narrowCached_M128`
     (`1.54×` speedup), and 16-step `chainCoerceSealed` vs `chainCoerceUnsealed` (`4.68×` speedup),
     plus `mkLazyReadCounted` / `mkLazyReadCounted_hit_top` in Part D.

---

## 5. Track A Promotion Roadmap (`ws-sparse-retag-index-and-batched-vc-narrow`)

All seven conditions from `[adv B1]` §5 are now resolved in the prototype:
1. **`ep1-sparse-retag-and-safe-shifts`**: Promote Part A (`NatBitTrie` with `adaptiveRetagTrieDepth`,
   `SparseRetagAttrIndex`, `evalFnEntryRetagWithSparseAttr`, and full Tree Borrows
   `applyImplicitWriteUpgrade`) and Part D (`LazyWriteChain` + `bvShiftSafe` / `shiftLeftBitsSafe`)
   into `theory/Anneal/SparseRetagAndVcNarrow.lean`.
2. **`ep2-batched-vc-narrow-and-demand-location`**: Promote Part B (`BatchedVcConeNarrowCert`,
   `hoistMaskTraitImpls`, `BatchedVcConeNarrowCert.ofCheckMask`, `coneSummary?_eq_of_stepMirFn_extCall`,
   and `@[irreducible] coerceValueAt`) and Part C (`DemandCallerLocationEnv` with
   `nextFreshGlobalAndTagId`, `evalDemandCallerLocation_borrowAware_spec`, and
   `demandCallerLocation_bisim_eager`), export from `theory/Anneal.lean`, and wire
   `tests/mir/SparseRetagAndVcNarrowProtoTests.lean` into `lake test`.
