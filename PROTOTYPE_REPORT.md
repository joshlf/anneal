# Prototype Evaluation Report — `ws-proto-sparse-retag-index-and-batched-vc-narrow`

- **Prototype Branch**: `refs/heads/prototype/ws-proto-sparse-retag-index-and-batched-vc-narrow/ep1-proto-sparse-retag-index-and-batched-vc-narrow`
- **Base `unstable` Commit SHA**: `1e208d1a9d6cce3326f6330ef2aecf942fe7d39d`
- **Paired Track A Workstream**: `ws-sparse-retag-index-and-batched-vc-narrow`
- **Deliverables** (the only files changed vs. base):
  - `theory/Anneal/SparseRetagAndVcNarrowPrototype.lean`
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean`
  - `PROTOTYPE_REPORT.md`
- **Kernel & Axiom Audit** (bottom of the test file, on the final code): `axiom audit passed: 1598 declarations (198 prototype theorems, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 leaked constants, 0 placeholder uses, 100% theorem reachability)`
  - All theorems depend only on `{propext, Quot.sound}`; the audit's self-tests confirm it flags
    `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, and an elaborated `have _ := @thm` placeholder.
  - `tests/mir/SparseRetagAndVcNarrowProtoTests.lean` starts with `import Anneal` +
    `import Anneal.SparseRetagAndVcNarrowPrototype` and elaborates cleanly (no symbol/instance collisions).
- **Overall Recommendation**: **CONDITIONAL GO** — the four mechanisms are formally sound on the
  prototype models, but Track A must address the integration conditions in §5 before promotion.

---

## 1. What Is Proved (theorem names as they exist in the module)

### Part A — `SparseRetagAttrIndex` (`proofs-rs/lean-miri` PR #68)
- `linearScanRetagAttr` mirrors `lean-miri`'s `CompilerRetagOptions.rustcNoWritable`: frame check
  first, then a left-to-right whole-table scan with an `O(M)` duplicate check per row (so `O(M²)`
  per query).
- `prepareSparseRetagIndex` builds a binary radix trie (`NatBitTrie Bool`: 12 low key bits, then
  exact-key leaf buckets) once, caching any table error in `Except`; `lookupSparseRetag` checks
  `.frameAbsent` first.
- `lookupSparseRetag_eq_linearScan`: exact equality with the oracle for **all** `definitionCount`,
  `rows`, `id` (error precedence included); `frameAbsent_precedes_malformedTable`;
  `lookupSparseRetag_cert` / `lookupSparseRetag_miss_cert`; `SparseDefPathRetagIndex.get?_insert`.
- Operational overlay `evalFnEntryRetagWithSparseAttr` over `Trusted` `evalStmt`:
  `evalFnEntryRetagWithSparseAttr_eq_linear`, `unusedMalformedTable_demand_local`,
  `evalFnEntryRetagWithSparseAttr_implicitWrites_false`,
  `evalFnEntryRetagWithSparseAttr_rustcNoWritable_true`, and
  `applyImplicitWriteUpgrade_of_no_fresh_child` (the implicit-write upgrade only ever touches the
  child tag freshly created by the retag).

### Part B — `BatchedVcConeNarrowCert` + `hoistTraitImpls` + `@[irreducible] coerceValueAt`
- ONE Boolean checker `checkBatchedVcConeNarrowCert` (one `decide +kernel`), and
  `BatchedVcConeNarrowCert.ofCheck` deriving **every** field of the propositional certificate from
  it. The narrowed environment is determined by the certificate data:
  `narrowCallees := selectByMask fullCallees mask`, `extra₂ := hoistTraitImpls fullCallees extra`.
- First-match preservation without `CapturedMir` equality: `checkMaskKeepsFirstMatch` +
  `calleesAgreeOn_selectByMask` (duplicate shadowing included).
- `computeBatchedVcNarrowCert` / `collectTraitConeBodies` compute `(cone, mask, narrowExt)`;
  `selectByMask_coneMask` shows the canonical mask selects exactly `coneBodies`.
- Trait-aware congruence: `resolveCalleeBodyAndArgs?_eq_of_traitConeAgree`,
  `lookupCallee_eq_of_traitConeAgree`, `evalTerminator_withCalleesAndTraits`,
  `stepMirFn_withCalleesAndTraits`, `coneReach_of_closedInvTrait`.
- Core theorems: `runMirExecBounded_narrow_of_batchedCert`, `wpMirExecSym_narrow_of_batchedCert`,
  `vcMirWithCallees_narrow_of_batchedCert`.
- `vcMirWithCallees` is a contract-aware WP (`wpMirExecExt`): an external call to a cone path with a
  summary only considers answers satisfying the summary's contract. Sanity:
  `wpMirExecExt_nil_iff` (no summaries = `wpMirExecSym`), `wpMirExecExt_of_wpMirExecSym`
  (summaries only weaken obligations), `wpMirExecExt_trait_cone_narrow`.
- `coerceValueAt` is `@[irreducible]` (meta-level opacity audit at `.default` vs `.all`) with
  `coerceValueAt_u32`, `coerceValueAt_bool`, `coerceValueAt_ref`, `coerceValueAt_adt_exact`,
  `coerceValueAt_idempotent`.

### Part C — `DemandCallerLocationEnv` (`proofs-rs/lean-miri` PR #67 Schema 15)
- `FrameLocMeta` (`callSitePos : Option SourceExpansionPos`, `isTrackCaller`, `detailPolicy`),
  `CallerLocationSite.resolve` = `find_closest_untracked_caller_location` with the redaction policy of
  the crate owning the resolved span; `resolveCallerLocationAux_eq_topDown` (bottom-up walk = Miri's
  top-down `trackCallerArg` propagation).
- `evalDemandCallerLocation` draws fresh ids from `Memory.nextAllocId` (the *next fresh* id in
  `Trusted`) and advances it past every allocation; one fresh `Location` per invocation (as in
  lean-miri `EvalCallerLocationConstruction.hook`), filename allocations deduplicated by redacted bytes.
- General theorems over **all** call-site tables, **all** traces and all 8 policies:
  `evalDemandCallerLocation_spec`, `runDemandCallerLocationTrace_spec`, `eagerInitAux_spec`,
  `demandCallerLocation_bisim_eager` (identical `(fileBytes, line, column)` observations in the
  demand and eager worlds, equal to each invoked site's resolved location),
  `demandCallerLocation_no_call_zero_allocs` (non-panicking demand run `=` plain run: same globals,
  same `nextAllocId`), `eagerCallerLocation_clutter` (eager globals `= G₀ + S + #files`),
  `allocRenamingRel_of_readLocations` (explicit renaming; injective iff no site is invoked twice).

### Part D — `LazyWriteChain` & total shifts
- `mkLazyWrite w` checks bounds against the static width `w` in `O(1)`; `eval_mkLazyWrite`,
  `eval_mkEagerWrite`, `eval_mkLazyRead` (all for `symArrayLen arr = w`).
- Step counts are proved on instrumented copies of the implementations (`mkLazyWriteCounted_fst`,
  `stripShadowedWritesCounted_fst`, `stripShadowedWritesCounted_snd`, `mkEagerWriteCounted_fst`,
  `lazyDistinctChainCounted_fst`, `eagerDistinctChainCounted_fst`):
  `lazyWriteChain_distinctAddrs_steps_eq_N` (`N`) and
  `eagerWriteChain_distinctAddrs_steps_quadratic` (`N(N+1)/2`), with
  `buildLazyDistinctChain_eq_eager` (both strategies build the same term).
- `bvShlSafe_eq`, `bvLshrSafe_eq`, `bvAshrSafe_eq`, `shiftLeftBitsSafe_eq` (all inputs),
  `shiftRightUnsignedBitsSafe_eq` (canonical inputs), `arithmeticShrBitsSafe_eq` (all inputs),
  and `canary_wideShift_two_pow_64` (kernel evaluation at `shift = 2^64`).

---

## 2. Benchmarks (measured by `tests/mir/SparseRetagAndVcNarrowProtoTests.lean`)

Methodology: every arm is a theorem discharged by `decide +kernel` (same mechanism for both arms);
`IO.getNumHeartbeats` deltas are deterministic across runs, wall-clock (`IO.monoNanosNow`) is from
the final receipt run and is noisy on the shared capsule. Optimized arms include their one-time
costs (index preparation, certificate checking, narrowing computation) unless labeled otherwise.

### 2.1 Part A — linear oracle vs. sparse index (`definitionCount = 512`)

| Rows `M` | Linear oracle, 1 query | Sparse: prepare + 1 query | Sparse: prepare + `M` queries |
| :--- | ---: | ---: | ---: |
| 16 | `67,528` hb (`10.0` ms) | `143,247` hb (`22.9` ms) | `435,241` hb (`75.1` ms) |
| 64 | `577,578` hb (`80.8` ms) | `616,711` hb (`106.9` ms) | `1,734,251` hb (`320.9` ms) |
| 128 | `2,117,800` hb (`318.2` ms) | `1,370,275` hb (`232.1` ms) | `3,508,010` hb (`679.8` ms) |
| 256 | `8,147,438` hb (`1,541.3` ms) | `3,060,406` hb (`608.4` ms) | `7,118,149` hb (`1,593.1` ms) |

- The linear oracle grows ~4× per doubling of `M` (quadratic per query). Including preparation,
  the sparse index is *slower* for a single query at `M = 16` (2.12× the linear cost),
  roughly even at `M = 64`, and faster from `M = 128` (1.55×) to `M = 256` (2.66×).
- Answering **all** `M = 256` queries with the sparse index (`7,118,149` hb) costs
  less than **one** linear-oracle query at `M = 256` (`8,147,438` hb). (Running all
  256 linear queries was not measured.)

### 2.2 Part B — full callee table vs. certified narrowing (trait call through `TraitImplEntry`)

| Callees `M` | Full table run | Cert check (compute cone + mask, 1 `decide`) | Narrowed run (narrowing computed in-kernel) | Narrowed run (cached narrowed table) |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `562,747` hb (`88.3` ms) | `1,623,908` hb (`251.2` ms) | `588,006` hb (`93.4` ms) | `451,994` hb (`70.5` ms) |
| 64 | `670,415` hb (`102.1` ms) | `2,066,843` hb (`295.5` ms) | `781,821` hb (`132.0` ms) | `451,987` hb (`74.2` ms) |
| 128 | `813,951` hb (`114.5` ms) | `2,657,370` hb (`380.7` ms) | `1,040,205` hb (`148.5` ms) | `451,996` hb (`70.6` ms) |

- The cached arm uses `[protoPoly, protoCircleArea]` / `[protoAreaEntry]`, proved equal (`rfl`) to
  the computed `selectByMask` / `hoistTraitImpls` (`cachedNarrow_eq_computed_*`).
- Concrete execution gains are small: once the narrowed table is cached, a run costs a constant
  ~`451,996` hb vs. `813,951` hb for the full table at `M = 128`
  (1.80×); if narrowing is recomputed per run it is *slower* than the full table, and the
  one-time certificate costs ~3× a full run. The intended payoff of cone narrowing is smaller
  symbolic VCs, which these concrete-execution benchmarks do not measure.
- Coercion micro-benchmark (`∀ bits`, elaborator): sealed `coerceValueAt` via `coerceValueAt_u32`
  `91,292` hb (`5.1` ms) vs. a reducible copy via `rfl` `102,257` hb (`6.6` ms) — no
  material difference at this scale; the benefit of sealing (keeping `whnf` / `simp` from unfolding
  coercions inside large VCs) is not demonstrated here.

### 2.3 Part C — eager pre-allocation vs. demand-time `Location` (same trace in both worlds)

| Sites `S` | Eager, non-panicking (8 stmts) | Demand, non-panicking | Eager, panicking (1 invocation) | Demand, panicking |
| :--- | ---: | ---: | ---: | ---: |
| 16 | `129,716` hb (`19.4` ms) | `52,888` hb (`7.0` ms) | `236,567` hb (`34.2` ms) | `196,075` hb (`25.4` ms) |
| 64 | `761,443` hb (`104.7` ms) | `52,902` hb (`7.0` ms) | `393,487` hb (`54.1` ms) | `196,079` hb (`26.3` ms) |
| 128 | `2,506,927` hb (`363.6` ms) | `52,904` hb (`7.2` ms) | `624,175` hb (`80.7` ms) | `196,117` hb (`26.6` ms) |

- Demand cost is independent of `S`; the non-panicking eager arm must materialize `S + 1` globals
  (checked: `globals.length = S + 1`). Its super-linear growth is partly an artifact of the
  list-based `Memory.globals` model (`globals ++ [alloc]` is `O(|globals|)`).

### 2.4 Part D — eager vs. lazy distinct-address write chains (`cap = 128`, read of the last write)

| Writes `N` | Eager (`mkEagerWrite`) | Lazy (`mkLazyWrite`) | Proved spine inspections (eager / lazy) |
| :--- | ---: | ---: | ---: |
| 16 | `121,642` hb (`16.5` ms) | `60,050` hb (`6.9` ms) | 136 / 16 |
| 64 | `1,226,876` hb (`181.8` ms) | `113,393` hb (`15.5` ms) | 2080 / 64 |
| 128 | `4,728,539` hb (`839.4` ms) | `183,981` hb (`25.7` ms) | 8256 / 128 |

- Wide-shift canary (`shift = 2^64`, all six safe shifts, one `decide +kernel`): `140,152` hb (`9.7` ms).

---

## 3. Canaries (all kernel-checked)

- **Part A**: hit/miss certificates on the prepared index; `.duplicateDefQuery`, `.defIdOutOfBounds`,
  `.attrQueryAbsent`, and `.frameAbsent` overriding a malformed table; implicit write activates the
  fresh child (`rustcNoWritable = false`) but not under `#[rustc_no_writable]`; regression: a
  zero-sized `&mut ()` fn-entry retag (no child created) leaves `borrows` untouched, whereas the
  `[adv A0]` overlay (kept in the test file as `applyImplicitWriteUpgradeLegacyA0`) rewrote the
  unrelated head entry to `.unique`.
- **Part B**: `canary_naiveNarrow_breaks_trait_dispatch` (naive `coneBodies` loses the
  `TraitImplEntry`, `lookupCallee = none`, run stalls; `CallConeClosedPoly` fails closed);
  `canary_traitDispatch_preserved_under_batchedVcNarrow` (narrowed run returns exactly `31`);
  `canary_duplicateShadow_rejected` (same-shape shadow exposing a different body — the `[adv A0]`
  metadata-only check, kept as `checkCalleesAgreeOnLegacyA0`, accepts it);
  `canary_externalShadowsInternal_rejected` (also: summary injected on the narrowed side only);
  `canary_missingTraitImplBody_rejected` (also: kept body carrying a cone `TraitImplEntry`);
  `canary_externalSummary_vc` (the VC holds with the cone summary and is false without it).
- **Part C**: `demandCallerLocation_filename_dedup` (3 allocations, ids `0..2`, `nextAllocId = 3`),
  `trackCaller_span_owner_policy`, `trackCaller_stops_at_nonTrackCaller_frame`, bisimulation for
  all 8 policies on a trace with a repeated site, explicit `AllocRenamingRel` on a distinct-site trace.
- **Part D**: OOB fold, same-address collapse, distinct-address `O(1)` stop, `2^64` shift.

---

## 4. Adversarial History

- `[adv A0]` initial implementation (agent-a).
- `[adv B1]` (agent-b) fixed: `vcMirWithCallees` was vacuous (its external-summary conjunct was
  `x = x`); the batched certificate's callee check compared only metadata (unsound on same-shape
  shadows) and needed hand-proved side fields; `computeBatchedVcNarrowCert` /
  `canary_mirLiftCore_callConeClosedPoly_fails_on_trait_call` were claimed but absent;
  `evalDemandCallerLocation` reused `nextAllocId` (collision with the next allocation);
  `applyImplicitWriteUpgrade` rewrote whatever borrow entry was at the head;
  `demandCallerLocation_bisim_eager` was a single concrete instance; the Part D step theorems were
  closed-form recurrences unrelated to the implementations and `mkLazyWrite` re-walked the spine
  via `symArrayLen` (`O(N)` per write); theorem "reachability" relied on `have _ := @thm`
  placeholders; Part A/B/C benchmarks compared different mechanisms, hand-built indices/tables, or
  identical computations; this report referenced non-existent theorems.

---

## 5. Conditions for Track A Promotion (open items)

1. **`allocId` / borrow-tag namespace**: `Trusted` stores stack-reference tags in
   `ProvenancePtr.allocId` (`ProvenancePtr.tag = allocId`) and resolves pointers through
   `lookupBorrow` before `lookupGlobalAlloc`; demand-time `Location` ids (from `nextAllocId`) can
   coincide with live tags (from `nextTag`). The prototype's theorems read `Location`s through
   `readLocationFromGlobals` only; wiring into `evalTerminator` needs disjoint id ranges.
2. **Implicit-write effects**: the overlay models only the initial `.unique` permission of the
   fresh child, not the foreign-write transitions of an implicit child write
   (`treeBorrowForeignWrite`, ancestor child-write UB), which V2026_08_01 semantics expects.
3. **Statement frame condition in Part C**: `normalStmtStep` keeps `Memory.globals` and
   `nextAllocId` unchanged by construction (V2026_06_01 statements never write them); Track A should
   prove `evalStmt` preserves both instead of re-asserting it.
4. **Trie depth**: `NatBitTrie` routes on 12 low bits; for `definitionCount > 4096` leaf buckets
   hold up to `⌈definitionCount / 4096⌉` keys, so lookups are `O(12 + D/4096)`, not `O(log M)`.
5. **External calls outside the cone** are havoc'd (summaries are trusted only on cone paths);
   proving that reachable external calls stay in the cone would allow unrestricted summary use.
6. **Hoisting restriction**: the certificate fails closed if a *kept* body carries a
   `TraitImplEntry` for a cone path (hoisting would duplicate the dispatch record).
7. **Symbolic payoff of Part B** (VC size) and of `coerceValueAt` sealing remain unmeasured.

### Proposed 2-Episode Track A Plan
1. `ep1`: Part A (+ conditions 2, 4) and Part D into `theory/Anneal/SparseRetagAndVcNarrow.lean`.
2. `ep2`: Part B (+ conditions 5–7) and Part C (+ conditions 1, 3), exported from
   `theory/Anneal.lean`, with this test suite as the regression gate.
