# PROTOTYPE_REPORT — `ws-proto-demand-time-compiler-queries-and-opaque-callee-table`

- **Episode**: `ep1-proto-demand-compiler-queries-and-opaque-callee-table` (Track P, `no_merge_prototype`, strictly off `unstable`)
- **Paired Track A workstream**: `ws-demand-time-compiler-queries-and-opaque-callee-table`
- **Base**: `origin/unstable` @ `86255c4698c28ce695b37e82f5a151896f7f736a`
- **Deliverables (the only `A` entries vs. base)**:
  1. `theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean`
  2. `scripts/bench_opaque_callee_and_query_proto.py`
  3. `scripts/test_bench_opaque_callee_and_query_proto.py`
  4. `PROTOTYPE_REPORT.md`

## 0. Recommendation: **CONDITIONAL GO**

All four research signals were validated in kernel-checked Lean 4 over the real
`Trusted.Rustc.V2026_06_01` / `V2026_08_01` types (0 `sorry`, 0 `Classical.choice`,
0 `Lean.ofReduceBool`, every module constant audited), and the empirical benchmark
shows flat per-step heartbeats for the opaque table against linear growth (and, at
`M = 128`, kernel resource exhaustion) for the concrete-list baseline. The **GO** is
conditional on the four Track A obligations in §9 (certificate emission at capture
time, a trusted `memory.callees` frame lemma, CFI demand carried in the query key,
and cone narrowing that preserves lookup *results* including `flatMapTraitImpls`
contributions); none is a blocker, each has a concrete plan, and each is already
pinned by a theorem or canary here.

## 1. Lean verification inventory (A0)

| item | count |
|---|---|
| `theorem` | 124 |
| `def` | 145 |
| `structure` / `inductive` | 10 / 12 |
| `deriving instance DecidableEq` (real `Trusted` types) | 36 |
| inline `deriving DecidableEq` (prototype types) | 19 |
| `deriving BEq` anywhere | **0** |
| `#guard_msgs` (28 `#print axioms` pins + 4 behaviour pins) | 32 |
| `decide +kernel` canaries (kernel evaluation of the real trusted machine) | 10 |
| bottom-of-file `run_cmd` axiom audit | traverses every module-local constant (≥ 1000 in the prototype namespace plus `deriving` auxiliaries), allows only `[propext, Quot.sound]`, self-tests that it flags `Classical.choice` / `sorryAx` / `Lean.ofReduceBool` |
| `run_meta` opacity witness | `whnf` at default transparency leaves `OpaqueCalleeTable.lookupRaw` / `.lookup` stuck; only `.all` unfolds them |

Every headline theorem's axiom set is pinned (`#guard_msgs (whitespace := lax)`):
all are `[propext]` or `[propext, Quot.sound]`.

## 2. Part A — `@[irreducible]` `OpaqueCalleeTable`, certificates, pruning, cone

**Carrier.** `OpaqueCalleeTable := List CapturedMir`, sealed `@[irreducible]`
together with `ofList` / `toList` / `lookupRaw` / `lookup`. `lookup` is *literally*
the trusted `lookupCallee` on the underlying list, so it inherits the full trusted
semantics (direct monomorphic hits, polymorphic instantiation through
`CapturedMir.instantiate` + `RigidTy.computeLayout`, `TraitImplEntry` override and
default-method resolution over `extraTraitImpls ++ flatMapTraitImpls callees`, and
every miss): `opaqueCalleeTable_lookup_eq_trusted`.

**`O(1)` certificates** (each a single rewrite at the use site):
`lookupCallee_hit_mono` (raw certificate + `typeParamCount = 0`),
`lookupCallee_hit` (resolution certificate + `instantiationLayouts?` certificate ⇒
`some (c.instantiate (eff.zip argLayouts))`; the trusted accumulator loop
`lookupCallee.resolveLayouts` is proven equal to `instantiationLayouts?`),
`lookupCallee_trait_hit` (unique most-specific `TraitImplEntry` winner),
`lookupCallee_miss` / `_miss_direct` / `_miss_arity` / `_miss_uninstantiable`.
Raw certificates are what a capture tool would emit and what the benchmark
measures as `cert_gen`: `lookupRaw_ofList_append_cons_of_skips` splits the table as
`pre ++ c :: post` and discharges all `|pre|` trusted-`stringEq` skips as *one*
Boolean fact by a single kernel evaluation (`decide +kernel`), plus `rfl` for the
hit. Alternatives proven alongside: per-entry steps
(`lookupRaw_ofList_cons_hit` / `lookupRaw_ofList_cons_skip` /
`lookupRaw_ofList_cons_miss`) and, after a one-time duplicate-free check, plain
membership (`lookupRaw_ofList_of_mem_nodup`, no string comparisons at all).

**Pruning is exact w.r.t. the trusted machine.** `stepTerminatorWith` is the trusted
`evalTerminator` with the `.call` / `.tailCall` arms copied verbatim (resolver in
place of `lookupCallee s.memory.callees`) and, when `prune = true`, a literal
`switchInt` discriminant (`ConstValue.scalar (.int si)`, covering literal `bool`)
jumping straight to its taken target. Proven:
`stepTerminatorWith_prune_exact` (pruned = trusted `evalOperand`-driven switch on
*every* terminator), `stepTerminatorWith_list_eq_trusted` (copied arms = trusted
arms), hence `stepBranchPruned_eq_trusted` (a pruned opaque step **is**
`stepMirFn`), `evalWithOpaqueCallees_eq_evalWithListCallees` (exact multi-step
equivalence for all programs, layouts, trait impls, states, fuel), and
`evalWithOpaqueCallees_eq_trusted` (multi-step equality with iterated `stepMirFn`
under the `memory.callees` frame condition).

**Call-cone narrowing.** `demandedKeys` collects the callee-table keys demanded along
the pruned run (dead literal arms and unreachable blocks demand nothing).
`evalWithOpaqueCallees_cone_narrow`: agreement of `narrowTbl` and `fullTbl` on the
demanded keys ⇒ identical results (and `_of_narrow`, stated against the narrowed
run's own keys). Canaries over concrete captured MIR, all discharged by kernel
evaluation of the real trusted machine:
`canary_deadArm_cone_narrow` (panicking `g_dead` only on the dead arm, excluded),
`canary_deadArm_halts` (the run genuinely halts with `[.event 1]`, returning `7`),
`canary_liveArm_required` (dropping the live callee turns the run into an external
call — the hypothesis is necessary), `canary_multi_cone_narrow` (polymorphic
`poly::<u32>` instantiation + `<Circle as Area>::area` trait dispatch), and
`canary_naiveNarrow_breaks_trait_dispatch` (see §8.1).

## 3. Part B — demand-time `CompilerQueryEnv`

`CompilerSchemaVersion` (`v2026_06_01`, `v2026_08_01` = Schema 12; `schema13`) with a
decidable total (hence partial) order `SchemaLe` (`refl`/`trans`/`antisymm`/`total`).
Three-way `QueryResult` (`ok` / `err : QueryErr` / `unsupported : MissingEvidence`).
`CompilerQueryEnv` carries the schema, V2026_06_01 layouts, optional V2026_08_01
layouts (bridged by `bridgeLayoutV08ToV06` / `bridgeTypeLayoutV08ToV06`, lossless by
`bridgeTypeLayout_roundtrip` / `bridgeLayout_roundtrip`), the declared `FnAbi`
table, and optional Schema-13 CFI tags, sync-storage regions, and vtable entries;
every Schema-13 (resp. V08) field is *schema-gated*.

`evalCompilerQuery` covers `layoutOf` (V06 `RigidTy.computeLayout` seeded with the
captured `LayoutTable` entry; V08 `RigidTy.computeLayout` on the bridged type,
bridged back), `abiCompatible` (CFI evidence → CFI type ids → `CallConv` → per-arg
`AbiPassMode` + layout → return ABI → unwinding), `syncStorageGuard`
(`syncStorageRegion_blocks_iff_overlap`: rejects exactly the accesses overlapping a
region of the same allocation), and `vtableMethodLookup`.

Proven: `query_schema12_unsupported_fallback` (stronger than required: *every*
Schema-12 environment, whatever its optional fields hold, answers every
Schema-13-only query with `.unsupported`), `query_schema12_never_ok`,
`query_mono_schema` (every `.ok` / `.err` answer is preserved by every
`EnvExtends`, itself a preorder), `layoutOf_agrees_with_eager` (demand-time V06
`layoutOf` = the eager pre-enumerated catalog on every catalogued type),
`memoLookup_memoize` (`QueryKey`-memoized answers = demand-time answers), plus
decidable canaries for every query family and error.

## 4. End-to-end integration

`dynDispatchStep` chains `UnOp.vtableMethodLookup` (prototype `UnOpExt`, `charon#1611`)
→ `abiCompatible` → `OpaqueCalleeTable.lookup` (through `redirectResolver`) →
`stepBranchPruned`; missing evidence fails closed (`MirStepNode.unsupported`), a CFI
type-id mismatch is the defined CFI trap (`abort`), every other error is UB.
`dynDispatchStep_preserved` proves preservation under `EnvExtends` and call-cone
narrowing simultaneously; the canaries show Schema 12 failing closed
(`dyn_step_schema12_fails_closed`), Schema 13 entering `<Circle as Area>::area`
(`dyn_step_enters_impl`), preservation under a further extension plus narrowing to
the single dispatched body (`dyn_step_preserved`), and the CFI trap (`dyn_cfi_trap`).

## 5. Part C — `DecidableEq` without `BEq`

No prototype type derives or declares `BEq`; every real `Trusted` type the
prototype compares gets `DecidableEq` only (36 `deriving instance`, plus a manual
axiom-free `DecidableEq RigidTy` by Boolean reflection, `rigidTyStructEq_iff`), so
`==` is `instBEqOfDecidableEq` and the core `instLawfulBEq` gives `beq_iff_eq`
(`rigidTy_beq_iff_eq`, `layoutTable_beq_iff_eq`, …; `#synth LawfulBEq DemoKey`
pinned to `instLawfulBEq`). The worked demonstration (`ShadowingDemo`) installs the
structural `BEq` a redundant derivation would add and pins the resulting
`failed to synthesize LawfulBEq DemoKey`.

## 6. Benchmark (`--sizes 4,16,64,128`)

Prototype compiled once into `/tmp` in 34.1 s; median of 3 repetitions per variant; heartbeats are Lean's raw `IO.getNumHeartbeats` deltas around `elabCommand` (elaboration + kernel check, `Elab.async false`), kHb = 1000 heartbeats.

| M | linear_list kHb | opaque_o1 kHb | opaque_pruned kHb | linear_list ms | opaque_o1 ms | opaque_pruned ms | cert_gen live+dead kHb (one-time) |
|---|---|---|---|---|---|---|---|
| 4 | 1997.6 | 117.8 | 88.2 | 369.61 | 28.78 | 18.58 | 1179.0 |
| 16 | 6576.2 | 117.8 | 88.2 | 1227.88 | 20.08 | 12.29 | 4467.9 |
| 64 | 24679.6 | 117.8 | 88.3 | 5070.54 | 18.56 | 12.56 | 17508.8 |
| 128 | 45653.4 ✗ | 117.8 | 88.3 | 9252.91 ✗ | 19.40 | 14.82 | 34128.6 |

✗ `linear_list` at M = 128: Lean rejected the baseline proof (`(kernel) excessive memory consumption detected`); heartbeats / ms are those consumed until the failure.

| variant | heartbeats / callee (LSQ slope) | log-log slope | growth M_min → M_max |
|---|---|---|---|
| `linear_list` | 352489 | 0.909 | 22.85x |
| `opaque_o1` | 0 | 0.000 | 1.00x |
| `opaque_pruned` | 0 | 0.000 | 1.00x |
| `cert_gen_live` | 132888 | 0.942 | 25.97x |
| `cert_gen_dead` | 132892 | 1.007 | 32.74x |

| M | opaque_o1 heartbeat speedup | opaque_pruned heartbeat speedup | opaque_o1 wall speedup | opaque_pruned wall speedup |
|---|---|---|---|---|
| 4 | 17.0x | 22.6x | 12.8x | 19.9x |
| 16 | 55.8x | 74.5x | 61.1x | 99.9x |
| 64 | 209.5x | 279.6x | 273.1x | 403.8x |
| 128 | 387.5x | 517.3x | 476.9x | 624.5x |

**Reading.** `linear_list` grows linearly with the table (log-log slope 0.91; 1998 → 24680 kHb from M = 4 to M = 64, and at M = 128 the kernel exhausts `anneal-lean-run`'s hardware-matched `lean -M` budget — about 2.2 GB on this capsule at measurement time — so the naive proof does not check at all), while `opaque_o1` (117.8 kHb) and `opaque_pruned` (88.3 kHb) are flat (slopes 0.000 / 0.000): 209× / 280× fewer heartbeats than the baseline at M = 64. Pruning saves the dead arm's resolution *and* its certificate (29.5 kHb per step here). The one-time certificate generation (two certificates: 17509 kHb at M = 64, 34129 kHb at M = 128) is linear but amortized: at M = 64 it pays for itself after 1 symbolic step(s) that reuse the certificates.

## 7. Repository `BEq + DecidableEq` audit

| root | `.lean` files | `.rs` files (Lean codegen literals) | occurrences | codegen occurrences | files with occurrences |
|---|---|---|---|---|---|
| `crates/` | 0 | 88 | 0 | 0 | 0 |
| `theory/` | 68 | 0 | 10 | 0 | 3 |
| **total** | 68 | 88 | 10 | 0 | 3 |

Occurrences (each a `deriving` clause / `deriving instance` combining `BEq` with `DecidableEq`):

- `theory/Correspondence/Framework.lean:37` (deriving): `DecidableEq, BEq, Repr, Inhabited`
- `theory/Correspondence/Framework.lean:52` (deriving): `DecidableEq, BEq, Repr`
- `theory/Correspondence/Framework.lean:62` (deriving): `DecidableEq, BEq, Repr`
- `theory/Correspondence/Framework.lean:72` (deriving): `DecidableEq, BEq, Repr`
- `theory/Correspondence/V2026_06_01/L4_TreeBorrows.lean:80` (deriving_instance): `DecidableEq, BEq, Repr` for TreeBorrowPerm
- `theory/Correspondence/V2026_06_01/L4_TreeBorrows.lean:629` (deriving): `DecidableEq, BEq, Repr`
- `theory/Correspondence/V2026_06_01/L4_TreeBorrows.lean:635` (deriving): `DecidableEq, BEq, Repr`
- `theory/Correspondence/V2026_08_01/L4_TreeBorrows.lean:61` (deriving_instance): `DecidableEq, BEq, Repr` for TreeBorrowPerm
- `theory/Correspondence/V2026_08_01/L4_TreeBorrows.lean:611` (deriving): `DecidableEq, BEq, Repr`
- `theory/Correspondence/V2026_08_01/L4_TreeBorrows.lean:617` (deriving): `DecidableEq, BEq, Repr`

## 8. Soundness bugs, corner cases, and insights

### Round A0

1. **Naive call-cone narrowing is unsound** (`canary_naiveNarrow_breaks_trait_dispatch`).
   Keeping every *executed* `DefPath` still breaks `<Circle as Area>::area` dispatch,
   because the dropped, never-called `impl` block body contributed the
   `TraitImplEntry` through `flatMapTraitImpls callees`. Cone narrowing must preserve
   demanded lookup *results* (`demandedKeys` agreement), not reachable `DefPath`s.
2. **Schema-triggered CFI checking is non-monotone** (`autoCfi_breaks_mono`). Auto-
   enabling the CFI check whenever `env.schema = .schema13` changes a supported
   Schema-12 `.ok` into `.err` after a sound upgrade, contradicting
   `query_mono_schema`. The CFI demand is therefore part of the query key
   (`cfiCallSite : Option RigidTy`); Schema 13 is the only schema whose evidence can
   satisfy it. Evidence is checked *before* the ABI because the CFI trap precedes the
   call, and a type-id mismatch is a defined `abort`, not UB.
3. **V2026_08_01 layout material must be optional evidence.** With a mandatory V08
   table, `EnvExtends` (which preserves finite material) could never add V08
   material when a V2026_06_01 producer is upgraded.
4. **`Classical.choice` leaks through `simp`'s `BEq.rfl` on `Nat`**: although `Nat`'s
   `==` is `instBEqOfDecidableEq`, instance resolution picks
   `Std.LawfulBEqOrd.equivBEq.toReflBEq` for `ReflBEq Nat`, which depends on
   `Classical.choice`. Caught by the module audit (twice); fixed with `simp only` +
   `decide_eq_true rfl`. This is an instance-path hazard of the same family as
   cl/1022563952 and Track A's audit must check transitive axioms, not syntax.
5. **Tag-pruned manual `DecidableEq` defeats smart unfolding.** The first
   `DecidableEq RigidTy` (constructor-tag `dite` around a diagonal `match`) was
   axiom-free and kernel-evaluable, but `decide` got stuck on *top-level*
   off-diagonal comparisons (`RigidTy.bool ≠ .uint .u32`). Replaced by Boolean
   reflection with a catch-all (`rigidTyStructEq` + `decidable_of_iff`), pinned by
   `rigidTy_decide_canary`.
6. **Literal pruning generalizes beyond `bool`**: any literal scalar `switchInt`
   discriminant is pruned, and the exactness proof covers all of them.
7. **The module audit must traverse module-local constants, not a namespace.**
   `deriving` generates auxiliaries in the derived types' namespaces
   (`Trusted….Mutability.ofNat_ctorIdx`); a prefix filter would silently skip them.
8. **`O(1)` is per use; certificate generation is linear — and how it is generated
   matters.** The benchmark separates the two (`cert_gen_*`). Three generation
   strategies were measured during A0: a monolithic `rfl` over the list scan
   exhausts the kernel's `lean -M` budget at `M = 128` (like the baseline itself); a
   per-suffix chain with elaborator `decide` on `DefPath` disequality costs
   ≈ 1.05 MHb per skipped entry (3× the baseline's per-entry cost); the final
   single-declaration certificate whose skips are one kernel-evaluated
   `stringEq` fact costs ≈ 0.13 MHb per skipped entry, so generating *both*
   certificates is cheaper than one baseline step and succeeds at `M = 128`.

### Rounds A1–A4

_(appended by later rounds)_

## 9. Integration roadmap for `ws-demand-time-compiler-queries-and-opaque-callee-table`

1. **Table + certificates.** Land `OpaqueCalleeTable` (+ `opaqueCalleeTable_lookup_eq_trusted`)
   next to the symbolic evaluator; have `anneal-rustc-capture` emit, per captured
   callee, a single-declaration `lookupRaw_ofList_append_cons_of_skips` certificate
   (kernel-evaluated `stringEq` skips; or one `Nodup` witness per table plus
   membership certificates via `lookupRaw_ofList_of_mem_nodup`) beside `Mir/<Item>.lean`.
2. **Stepping.** Rewrite callee resolution with `lookupCallee_hit_mono` /
   `lookupCallee_hit` / `lookupCallee_trait_hit` instead of unfolding `findCallee?`;
   use `stepTerminatorWith_litSwitch` (or an equivalent simp lemma stated directly on
   trusted `evalTerminator`, justified by `stepTerminatorWith_prune_exact`).
3. **Frame lemma (condition).** Prove trusted `stepMirFn` preserves `memory.callees`
   and `memory.traitImpls`; this discharges the frame hypothesis of
   `evalWithOpaqueCallees_eq_trusted` for all runs.
4. **Cone narrowing (condition).** Narrow by demanded-key agreement (run the pruned
   evaluator once on the full table, or a static over-approximation that keeps every
   body contributing `TraitImplEntry` records); never by `DefPath` reachability.
5. **Query env (condition).** Wire `CompilerQueryEnv` to lean-miri Schema 12/13
   decoding; keep the CFI demand in the query key, gate V08 layouts and every
   Schema-13 field by schema, and treat `.unsupported` as fail-closed in the stepper.
6. **Bridge commutation.** Upgrade the roundtrip lemmas + cross-dialect canary to a
   general `computeLayout`-commutes-with-bridge theorem.
7. **`BEq` cleanup.** Replace the audited `deriving …, BEq, DecidableEq …` clauses
   (§7) with `DecidableEq` only, and add the scanner to CI.

## 10. Receipts (A0, run fresh after the final edit)

Receipt 1 (`export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"`) precedes every command.

| # | command | exit | result |
|---|---|---|---|
| 2 | `anneal-lean-run --mode file --concurrency 1 -- lake env lean theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean` | 0 | 0 error lines, 0 warning lines, 0 sorry lines, empty output (30 s) |
| 3 | `python3 -B -m unittest -v scripts/test_bench_opaque_callee_and_query_proto.py` | 0 | Ran 36 tests in 63.788s: OK, 0 skips |
| 4 | `python3 tools/anneal-lsp/server/proof_health.py theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean` | 0 | 0 output lines (0 findings) |
| 5 | `python3 -B scripts/bench_opaque_callee_and_query_proto.py --sizes 4,16,64,128 --json` | 0 | JSON with 4 sizes × 3 variants + certificates + repo audit (126 s) |
| 6 | `git status --porcelain`; `git diff --name-status 86255c4698c28ce695b37e82f5a151896f7f736a..HEAD` | 0 | pre-commit: only the 4 deliverables untracked; post-`[adv A0]`-commit: empty status and exactly `A PROTOTYPE_REPORT.md`, `A scripts/bench_opaque_callee_and_query_proto.py`, `A scripts/test_bench_opaque_callee_and_query_proto.py`, `A theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean` |

`scripts/__pycache__` directories: 0.
