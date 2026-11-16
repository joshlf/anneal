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

## 1. Lean verification inventory (updated through B1)

| item | count (A0 → B1) |
|---|---|
| `theorem` | 124 → **175** |
| `def` | 145 → **171** |
| `structure` / `inductive` | 10 / 12 |
| `deriving instance DecidableEq` (real `Trusted` types) | 36 → **74** |
| inline `deriving DecidableEq` (prototype types) | 19 → **21** |
| manual axiom-free Boolean-reflection `DecidableEq` (`RigidTy`, `Value`) | 1 → **2** (`rigidTyStructEq_iff`, `valueStructEq_iff`) |
| `deriving BEq` anywhere | **0** |
| `#guard_msgs` (43 `#print axioms` pins + 4 behaviour pins) | 32 → **47** |
| `decide +kernel` canaries (kernel evaluation of the real trusted machine) | 10 → **22** |
| bottom-of-file `run_cmd` axiom audit | traverses every module-local constant (≥ 1200 in the prototype namespace plus `deriving` auxiliaries, ≥ 115 theorems), allows only `[propext, Quot.sound]`, self-tests that it flags `Classical.choice` / `sorryAx` / `Lean.ofReduceBool` |
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
`lookupCallee_hit_poly` (direct polymorphic or fallback default-method hit stated
purely over `tbl.lookupRaw` and `(traitMatches ...).isEmpty = true`, eliminating raw
`tbl.toList` reduction),
`lookupCallee_trait_hit` (monomorphic `TraitImplEntry` override winner),
`lookupCallee_trait_hit_poly` (polymorphic `TraitImplEntry` override winner with
`c.typeParamCount > 0`),
`lookupCallee_trait_default_hit` (default trait method inheritance when
`winner.implPath = defPath`), and
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
under the `memory.callees` frame condition, concretely instantiated in B1 by
`canary_evalWithOpaqueCallees_eq_trusted` over `initMachineStateWithCallees`, while
`canary_trusted_stepMirFn_requires_linked_callees` shows `initMachineState` with
`callees = []` stalls at `.call` under trusted `stepMirFn`).

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
`poly::<u32>` instantiation + `<Circle as Area>::area` trait dispatch),
`canary_trait_specificity_and_default_inheritance` (two competing `TraitImplEntry`
records — blanket `impl<T> Area for Wrapper<T>` vs. specialized
`impl Area for Wrapper<u32>` — resolved via `filterMostSpecificTraitImpls`, plus
default trait method inheritance for `impl Area for Square`), and
`canary_naiveNarrow_breaks_trait_dispatch` (see §8.1).

## 3. Part B — demand-time `CompilerQueryEnv`

`CompilerSchemaVersion` (`v2026_06_01`, `v2026_08_01` = Schema 12; `schema13`) with a
decidable total (hence partial) order `SchemaLe` (`refl`/`trans`/`antisymm`/`total`).
Three-way `QueryResult` (`ok` / `err : QueryErr` / `unsupported : MissingEvidence`).
`CompilerQueryEnv` carries the schema, V2026_06_01 layouts, optional V2026_08_01
layouts (bridged in both directions by `bridgeLayoutV08ToV06` / `bridgeLayoutV06ToV08`,
`bridgeTypeLayoutV08ToV06` / `bridgeTypeLayoutV06ToV08`, and
`bridgeRigidTyV08ToV06` / `bridgeRigidTyV06ToV08`, lossless in both directions by
`bridgeTypeLayout_roundtrip` / `bridgeTypeLayout_roundtrip_v08`,
`bridgeLayout_roundtrip` / `bridgeLayout_roundtrip_v08`, and
`bridgeRigidTy_roundtrip`), the declared `FnAbi`
table, and optional Schema-13 CFI tags, sync-storage regions, and vtable entries;
every Schema-13 (resp. V08) field is *schema-gated*.

`evalCompilerQuery` covers `layoutOf` (V06 `RigidTy.computeLayout` seeded with the
captured `LayoutTable` entry; V08 `RigidTy.computeLayout` on the bridged type,
bridged back), `abiCompatible` (CFI evidence → CFI type ids → `CallConv` → per-arg
`AbiPassMode` + layout → return ABI → unwinding), `syncStorageGuard`
(`syncStorageRegion_blocks_iff_overlap`: rejects if and only if a non-empty access
`0 < len` overlaps a non-empty region `0 < r.size` of the same allocation;
`syncStorageRegion_blocks_zero_size`: 0-byte regions never block any access), and
`vtableMethodLookup`.

Proven:
- **Universal cross-dialect `computeLayout` commutation (B1)**:
  `computeLayout_bridge_commutes`, `computeLayoutList_bridge_commutes`,
  `computeLayoutV08Bridged_bridgeLayoutV06ToV08`,
  `computeLayoutV08Bridged_eq_computeLayoutV06_bridge`, and `evalLayoutOf_v08_eq_v06`
  prove that V2026_08_01 `RigidTy.computeLayout` commutes with the dialect bridge
  across all 21 `RigidTy` constructors (primitives, pointers, fat pointers, arrays,
  tuples, closures, and ADTs with `fieldLayouts`, unions, and multi-variant enums).
- **Bidirectional ABI compatibility characterizations (B1)**:
  `argAbiMismatch?_eq_none_iff`, `fnAbiMismatch?_eq_none_iff`, and `abiCore_ok_iff`.
- **Fail-closed Schema-12 fallback & schema-gated monotonicity**:
  `query_schema12_unsupported_fallback` (*every* Schema-12 environment, whatever its
  raw optional fields hold, answers every Schema-13-only query with `.unsupported`),
  `query_schema12_never_ok`, and `query_mono_schema` (every `.ok` / `.err` answer is
  preserved by every `EnvExtends` over schema-gated evidence accessors, with
  `EnvExtends.of_raw` and `envExtends_schema12_ignored_fields_canary`).
- **Eager catalog & memoization agreement**:
  `layoutOf_agrees_with_eager` (demand-time V06 `layoutOf` = the eager pre-enumerated
  catalog on every catalogued type) and `memoLookup_memoize` (`QueryKey`-memoized
  answers = demand-time answers).

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

In B1, `demandsDynSite`, `dynDemandStep`, and `evalDynWithOpaqueCallees` add
**demand-gated dynamic dispatch** (`resolveDynTarget` is queried *only* at states
whose active step demands `site.dynKey`):
- `dynDemandStep_preserved` proves single-step preservation where the query
  supportedness hypothesis is required only when `demandsDynSite site body s = true`.
- `canary_dyn_e2e_full_run_schema13` runs the full multi-step execution from `dynInit`
  (`if true { <dyn Area>::area() } else { g_dead() }`) to `.halted 31` on the
  narrowed opaque table.
- `canary_dyn_deadBranch_schema12_succeeds` proves the **Part A + Part B synergy**:
  when `<dyn Area>::area()` sits on the dead branch of `if false`,
  `evalDynWithOpaqueCallees` under Schema 12 (`dynEnv12`, which lacks vtable
  evidence) never demands `vtableMethodLookup` and halts cleanly returning `7` from
  `live_f()`.

## 5. Part C — `DecidableEq` without `BEq`

No prototype type derives or declares `BEq`; every real `Trusted` type in
`Trusted.Rustc.V2026_06_01.{Layout,MirAst,MirSemantics}` and
`Trusted.Rustc.V2026_08_01.{Layout,MirAst}` gets `DecidableEq` only (74
`deriving instance` declarations covering all AST, layout, and machine-state types
including `CapturedMir`, `MachineState`, `Memory`, `StackFrame`, `LocalSlot`,
`BorrowEntry`, `TreeBorrowPerm`, `SavedCallerFrame`, `FnPtrEntry`, `MirCallReq`,
`Outcome`, and `MirExecState`, plus 2 manual axiom-free Boolean-reflection
`DecidableEq` instances for the nested inductives `RigidTy` and `Value` via
`rigidTyStructEq_iff` and `valueStructEq_iff`, and 21 inline `deriving DecidableEq`
prototype types including `StepView` and `RunResult`). Consequently, `==` is always
`instBEqOfDecidableEq` and the core `instLawfulBEq` gives `beq_iff_eq`
(`rigidTy_beq_iff_eq`, `layoutTable_beq_iff_eq`, `capturedMir_beq_iff_eq`,
`machineState_beq_iff_eq`, …; `#synth LawfulBEq DemoKey` pinned to `instLawfulBEq`).
The worked demonstration (`ShadowingDemo`) installs the structural `BEq` a redundant
derivation would add and pins the resulting `failed to synthesize LawfulBEq DemoKey`.

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

### Round B1

1. **Part B Soundness Bug (`SyncStorageRegion.blocks` 0-byte region false positive).**
   In A0, `SyncStorageRegion.blocks` omitted `decide (0 < r.size)` from the second
   overlap disjunct `(decide (offset < r.offset) && decide (r.offset < offset + len))`,
   causing a 0-byte region `⟨allocId, 6, 0⟩` (`[6, 6)`, empty) to falsely block any
   spanning access such as `[0, 12)`. Fixed in `SyncStorageRegion.blocks`, proved
   `syncStorageRegion_blocks_zero_size`, strengthened
   `syncStorageRegion_blocks_iff_overlap` (dropping the redundant `0 < r.size`
   precondition), and added the 0-byte spanning case to `syncStorageGuard_canary`.
2. **Part B `EnvExtends` loophole on ignored raw fields.** A0 defined `EnvExtends` with
   `OptionExtends` on raw ungated fields (`env₁.vtables`, `env₁.cfiTags`,
   `env₁.syncRegions`, `env₁.layoutsV08`) rather than the schema-gated accessors
   (`vtableEvidence?`, `cfiEvidence?`, `syncEvidence?`, `v08Layouts?`). A Schema-12
   environment carrying ignored garbage in a raw Schema-13 field could not extend to a
   valid Schema-13 environment under A0's `EnvExtends`. Fixed by stating `EnvExtends`
   over the schema-gated evidence accessors, proving `EnvExtends.of_raw`, and adding
   `envExtends_schema12_ignored_fields_canary`. Also proved bidirectional `FnAbi` /
   `abiCore` characterizations (`argAbiMismatch?_eq_none_iff`,
   `fnAbiMismatch?_eq_none_iff`, `abiCore_ok_iff`).
3. **Part B universal cross-dialect `computeLayout` commutation (closing A0 Known Gap #1).**
   A0 only proved the one-way `V06 → V08 → V06` roundtrip and an 8-type canary. B1
   adds reverse bridges (`bridgeRigidTyV08ToV06`, `bridgeTypeLayout_roundtrip_v08`,
   `bridgeLayout_roundtrip_v08`, `bridgeRigidTy_roundtrip`) and proves universal
   cross-dialect commutation (`computeLayout_bridge_commutes`,
   `computeLayoutList_bridge_commutes`, `computeLayoutV08Bridged_bridgeLayoutV06ToV08`,
   `computeLayoutV08Bridged_eq_computeLayoutV06_bridge`, `evalLayoutOf_v08_eq_v06`)
   across all 21 `RigidTy` constructors (primitives, pointers, fat pointers, arrays,
   tuples, closures, and ADTs with `fieldLayouts`, unions, and multi-variant enums).
4. **Part A polymorphic/trait `O(1)` certificates and specificity/default-method canaries.**
   In A0, `lookupCallee_hit` left `resolveCalleeBodyAndArgs? tbl.toList` unreduced (so
   `canary_multi_polyKey_agrees` fell back to raw-list `rfl`), `lookupCallee_trait_hit`
   only handled monomorphic overrides (`c.typeParamCount = 0`), default trait method
   inheritance (`winner.implPath = defPath`) had 0 lemmas or canaries,
   `filterMostSpecificTraitImpls` was only tested on a 1-element list, and
   `evalWithOpaqueCallees_eq_trusted` had 0 concrete callers because `canaryInit` used
   `initMachineState` (`callees = []`). B1 proves `lookupCallee_hit_poly` (replacing
   the raw-list `rfl` in `canary_multi_polyKey_agrees`), `lookupCallee_trait_hit_poly`,
   and `lookupCallee_trait_default_hit`; adds
   `canary_trait_specificity_and_default_inheritance` (competing blanket
   `impl<T> Area for Wrapper<T>` vs. specialized `impl Area for Wrapper<u32>` plus
   default trait method inheritance for `impl Area for Square`); and adds
   `canary_evalWithOpaqueCallees_eq_trusted` and
   `canary_trusted_stepMirFn_requires_linked_callees` over
   `initMachineStateWithCallees`.
5. **End-to-end demand-gated dynamic dispatch + dead-branch Schema-12 synergy.**
   A0's `dynDispatchStep` evaluated `resolveDynTarget env site` eagerly before checking
   whether the active state `s` actually demands `site.dynKey`, causing Schema 12 to
   fail with `.unsupported` even when the `dyn` call sits on a pruned dead branch. B1
   adds `demandsDynSite`, `dynDemandStep`, `evalDynWithOpaqueCallees`,
   `dynDemandStep_preserved`, `canary_dyn_e2e_full_run_schema13` (full multi-step run
   from `dynInit` to `.halted 31`), and `canary_dyn_deadBranch_schema12_succeeds`
   (when `<dyn Area>::area()` is on a pruned dead branch `if false`, Schema 12 succeeds
   and halts returning `7`).
6. **Part C complete `DecidableEq` coverage (closing A0 Known Gap #3).**
   B1 proves axiom-free Boolean-reflection `DecidableEq` (without `BEq`) for the
   nested inductive `Value` (`valueStructEq`, `valueStructEq_iff`) and derives
   `DecidableEq` (never `BEq`) for all remaining `Trusted.Rustc.V2026_06_01.{MirAst,MirSemantics}`
   and prototype types (`CapturedMir`, `LocalSlot`, `StackFrame`, `TreeBorrowPerm`,
   `BorrowEntry`, `SavedCallerFrame`, `FnPtrEntry`, `Memory`, `MachineState`,
   `MirCallReq`, `Outcome`, `MirExecState`, `StepView`, `RunResult`), plus
   `capturedMir_beq_iff_eq` and `machineState_beq_iff_eq`.
7. **Part C scanner lexer/parser bugs in `scripts/bench_opaque_callee_and_query_proto.py`.**
   Fixed three bugs in the lexer/parser:
   - `tokenize_lean` failed on the escaped single-quote char literal `'\''` because
     `text.find("'", i + 2)` matched the escaped `'` at `i + 2`, leaving the closing
     `'` unconsumed to corrupt subsequent tokens.
   - `skip_code_until_brace` inside `s!`/`m!`/`f!` string interpolations did not handle
     char literals (`'{'`, `'}'`, `'\''`), raw strings (`r#"{"#`), guillemet
     identifiers (`«{»`), or nested `s!"..."` interpolations, causing any brace inside
     an interpolation hole to desynchronize brace depth and swallow the rest of the
     file.
   - `audit_redundant_beq_decidable_eq_text` had a comment `# skip class arguments in parentheses`
     with no implementation, and did not unwrap parenthesized class/target names such
     as `deriving (BEq), (DecidableEq)` or `deriving Foo (bar), BEq, DecidableEq`.
   All three are fixed and pinned by new unit tests in
   `scripts/test_bench_opaque_callee_and_query_proto.py`.

### Rounds A1–A4

_(appended by later rounds)_

## 9. Integration roadmap for `ws-demand-time-compiler-queries-and-opaque-callee-table`

1. **Table + certificates.** Land `OpaqueCalleeTable` (+ `opaqueCalleeTable_lookup_eq_trusted`)
   next to the symbolic evaluator; have `anneal-rustc-capture` emit, per captured
   callee, a single-declaration `lookupRaw_ofList_append_cons_of_skips` certificate
   (kernel-evaluated `stringEq` skips; or one `Nodup` witness per table plus
   membership certificates via `lookupRaw_ofList_of_mem_nodup`) beside `Mir/<Item>.lean`.
2. **Stepping.** Rewrite callee resolution with `lookupCallee_hit_mono` /
   `lookupCallee_hit_poly` / `lookupCallee_trait_hit` / `lookupCallee_trait_hit_poly` /
   `lookupCallee_trait_default_hit` instead of unfolding `findCallee?`;
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
6. **Bridge commutation (completed in prototype in B1).** Universal cross-dialect
   `computeLayout` commutation (`computeLayout_bridge_commutes`,
   `computeLayoutV08Bridged_eq_computeLayoutV06_bridge`, `evalLayoutOf_v08_eq_v06`) is
   now proven across all 21 `RigidTy` constructors; port into `Trusted` /
   `Correspondence` alongside the query environment.
7. **`BEq` cleanup (completed for `Trusted` + prototype in B1).** All 74 `Trusted`
   AST/layout/machine types and 21 prototype types now have axiom-free `DecidableEq`
   without `BEq`; replace the 10 audited `deriving …, BEq, DecidableEq …` clauses in
   `theory/Correspondence/` (§7) with `DecidableEq` only, and add the scanner to CI.

## 10. Receipts (A0 & B1, run fresh after the final edit)

Receipt 1 (`export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"`) precedes every command.

| # | command | exit | result |
|---|---|---|---|
| 2 | `anneal-lean-run --mode file --concurrency 1 -- lake env lean theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean` | 0 | 0 error lines, 0 warning lines, 0 sorry lines, empty output |
| 3 | `python3 -B -m unittest -v scripts/test_bench_opaque_callee_and_query_proto.py` | 0 | Ran 40 tests: OK, 0 failures, 0 skips |
| 4 | `python3 tools/anneal-lsp/server/proof_health.py theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean` | 0 | 0 output lines (0 findings) |
| 5 | `python3 -B scripts/bench_opaque_callee_and_query_proto.py --sizes 4,16,64,128 --json` | 0 | JSON with 4 sizes × 3 variants + certificates + repo audit |
| 6 | `git status --porcelain`; `git diff --name-status 86255c4698c28ce695b37e82f5a151896f7f736a..HEAD` | 0 | post-`[adv B1]`-commit: empty status and exactly `A PROTOTYPE_REPORT.md`, `A scripts/bench_opaque_callee_and_query_proto.py`, `A scripts/test_bench_opaque_callee_and_query_proto.py`, `A theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean` |

`scripts/__pycache__` directories: 0.
