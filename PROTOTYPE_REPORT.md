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
conditional on the five Track A obligations in §9 (certificate emission at capture
time, a trusted `memory.callees` frame lemma, CFI demand carried in the query key,
cone narrowing that preserves lookup *results* including `flatMapTraitImpls`
contributions, `DecidableEq` instances for `Trusted` types defined once — never
as orphan enumeration derivations, which make a module un-importable next to the
`Anneal` root, §5 — and a `dyn` call-site registry derived from the lowered MIR in
which every virtual call key has a well-formed site, unregistered virtual calls
failing closed, §4); none is a blocker, each has a concrete plan, and each is
already pinned by a theorem, canary, or receipt here.

## 1. Lean verification inventory (updated through A2)

| item | A0 → B1 → A1 → B2 → **A2** (measured on each commit) |
|---|---|
| `theorem` (incl. `@[simp]`) | 124 → 175 → 190 → 213 → **219** |
| `def` | 145 → 171 → 189 → 201 → **207** |
| `structure` / `inductive` | 10 / 12 → 10 / 12 → 11 / 12 → 11 / 12 → **11 / 12** |
| `DecidableEq` for real `Trusted` types | 36 → 74 → 74 → 74 → **74** (65 `deriving instance` + 9 prototype-local `decEqOfCtorIdxProto` instances for the enumeration types, which must not be orphan-derived: §5) |
| inline `deriving DecidableEq` (prototype types) | 19 → 21 → 21 → 21 → **21** |
| manual axiom-free Boolean-reflection `DecidableEq` (`RigidTy`, `Value`) | 1 → 2 → 2 → 2 → **2** (`rigidTyStructEq_iff`, `valueStructEq_iff`) |
| `deriving BEq` anywhere | **0** |
| `#guard_msgs` commands (`#print axioms` pins + `#synth` behaviour pins) | 30 → 45 → 57 → 68 → **72** (68 pins + 4 `#synth` pins on `DemoKey` and the real `TreeBorrowPerm`; B2's report said 65 + 3 and 215 theorems / 28 `decide +kernel`, measured 64 + 4, 213, 29) |
| `decide +kernel` uses (kernel evaluation of the real trusted machine) | 10 → 20 → 24 → 29 → **31** |
| co-import receipt (`import Anneal` + compiled prototype; prototype re-elaborated in the `Anneal` closure) | — → fails (9 duplicate `Trusted.….ofNat`) → ok → ok → **ok** |
| bottom-of-file `run_cmd` axiom & namespace-hygiene audit | traverses every module-local constant (≥ 1400 in the prototype namespace, ≥ 140 theorems), **enforces 0 leaked constants outside `Anneal.DemandCompilerQueryAndOpaqueCalleePrototype`** (`leaked.isEmpty`), allows only `[propext, Quot.sound]`, self-tests that it flags `Classical.choice` / `sorryAx` / `Lean.ofReduceBool` |
| `run_meta` opacity witness | `whnf` at default transparency leaves `OpaqueCalleeTable.lookupRaw` / `.lookup` stuck; only `.all` unfolds them |

Every headline theorem's axiom set is pinned (`#guard_msgs (whitespace := lax)`):
all are `[propext]` or `[propext, Quot.sound]`.

## 2. Part A — `@[irreducible]` `OpaqueCalleeTable`, certificates, pruning, cone

**Carrier.** `OpaqueCalleeTable := List CapturedMir`, sealed `@[irreducible]`
together with `ofList` / `toList` / `lookupRaw` / `traitImpls` / `lookup`. `lookup` is *literally*
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
`lookupCallee_hit_poly` (direct polymorphic or fallback default-method hit for a
concrete first argument, from `tbl.lookupRaw` plus a per-`(defPath, typeArgs)`
`(traitMatches ...).isEmpty = true` certificate — an `O(|trait impls|)` scan of
`flatMapTraitImpls tbl.toList`, generated once like every certificate here),
`lookupCallee_hit_free_poly` and `lookupCallee_hit_free_poly_opaque` (A1/B2: one
per-`defPath` certificate `hasTraitImplForDefPath (extra ++ tbl.traitImpls) defPath = false`,
over `@[irreducible] OpaqueCalleeTable.traitImpls` and independent of `typeArgs`,
rewrites *every* instantiation of a free generic function, including still-generic
`.param` callers, with zero `tbl.toList` occurrences;
`canary_free_poly_param_and_concrete`, `canary_free_poly_opaque_cert`),
`lookupCallee_trait_hit` (monomorphic `TraitImplEntry` override winner),
`lookupCallee_trait_hit_cert` (B2: fully `tbl.toList`-free trait-dispatch certificate
using `collectMatchingTraitImplsWith tbl.lookupRaw (extra ++ tbl.traitImpls)` and step
lemmas `collectMatchingTraitImplsWith_cons_ne_path`,
`collectMatchingTraitImplsWith_cons_ne_args`, and
`collectMatchingTraitImplsWith_cons_hit_mono`, discharging each matching impl via its
`O(1)` `tbl.lookupRaw` certificate instead of calling `findCallee? tbl.toList`;
`canary_trait_cert_no_toList`),
`lookupCallee_trait_hit_poly` (polymorphic `TraitImplEntry` override winner with
`c.typeParamCount > 0`),
`lookupCallee_trait_default_hit` (default trait method inheritance when
`winner.implPath = defPath`), and
`lookupCallee_miss` / `_miss_direct` / `_miss_arity` / `_miss_uninstantiable`.
`O(1)` means a single rewrite per *use*; every certificate (raw `lookupRaw`
skips, trait-match sets `hwin` / `hnoTrait`, `hasTraitImplForDefPath`) is a one-time
kernel evaluation whose cost is linear in the table (measured as `cert_gen` in §6
for the raw ones).
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
`syncStorageRegion_blocks_zero_size`: 0-byte regions never block any access),
`vtableMethodLookup`, and `vtableSupertraitLookup` (B2: supertrait vtable hop
lookup for `charon#1611` chained supertrait coercion).

Proven:
- **Universal cross-dialect `computeLayout` commutation (B1) & layout-table coherence (B2)**:
  `computeLayout_bridge_commutes`, `computeLayoutList_bridge_commutes`,
  `computeLayoutV08Bridged_bridgeLayoutV06ToV08`,
  `computeLayoutV08Bridged_eq_computeLayoutV06_bridge`, and `evalLayoutOf_v08_eq_v06`
  prove that V2026_08_01 `RigidTy.computeLayout` commutes with the dialect bridge
  across all 21 `RigidTy` constructors (primitives, pointers, fat pointers, arrays,
  tuples, closures, and ADTs with `fieldLayouts`, unions, and multi-variant enums).
  B2 adds the decidable cross-dialect coherence predicate `CompilerQueryEnv.isLayoutCoherent`
  (`bridgeLayout_iff_eq`, `isLayoutCoherent_of_schema_v06`), canonical bridged constructor
  `withBridgedV08Layouts` (`withBridgedV08Layouts_isLayoutCoherent`,
  `withBridgedV08Layouts_extends`), `evalLayoutOf_v08_eq_v06_of_coherent`,
  `isLayoutCoherent_preserved_of_v08_present`, and the negative falsification canary
  `incoherence_breaks_dialect_agreement_canary` showing an incoherent V08 table breaks
  V08/V06 `layoutOf` agreement.
- **Bidirectional ABI compatibility characterizations (B1)**:
  `argAbiMismatch?_eq_none_iff`, `fnAbiMismatch?_eq_none_iff`, and `abiCore_ok_iff`.
- **Fail-closed Schema-12 fallback & schema-gated monotonicity**:
  `query_schema12_unsupported_fallback` (*every* Schema-12 environment, whatever its
  raw optional fields hold, answers every Schema-13-only query — including
  `.vtableSupertraitLookup` — with `.unsupported`),
  `query_schema12_never_ok`, and `query_mono_schema` (every `.ok` / `.err` answer across
  all 5 `CompilerQuery` constructors is preserved by every `EnvExtends` over schema-gated
  evidence accessors, with `EnvExtends.of_raw` and `envExtends_schema12_ignored_fields_canary`).
- **Eager catalog & memoization agreement**:
  `layoutOf_agrees_with_eager` (demand-time V06 `layoutOf` = the eager pre-enumerated
  catalog on every catalogued type) and `memoLookup_memoize` (`QueryKey`-memoized
  answers = demand-time answers).

## 4. End-to-end integration

`dynDispatchStep` reads the receiver's vtable pointer from the calling frame
(`DynCallSite.vtablePtr?`: local `vtableLocal` holds `PtrMetadata(recv)` as in the
`charon#1611` lowering; no initialized pointer ⇒ UB) and chains
`UnOp.vtableMethodLookup` (prototype `UnOpExt`; B2's `resolveVTableChain` walks
`supertraitChain : List TraitRef` via `.vtableSupertraitLookup` hops before the
terminal `.vtableMethodLookup`, and since A2 every hop's query is issued by
`UnOpExt.query?`, one `UnOp::VTableMethodLookup` per hop) → `abiCompatible` →
`OpaqueCalleeTable.lookup` (through `redirectResolver`) → `stepBranchPruned`. A site
whose call key is not a virtual call on the trait of the receiver's first vtable is
ill formed (`DynCallSite.wellFormed`) and fails closed
(`dynDispatchStep_of_not_wellFormed`); missing evidence fails closed
(`MirStepNode.unsupported`), a CFI type-id mismatch is the defined CFI trap
(`abort`), every other error is UB. `dynDispatchStep_preserved`
(using `resolveVTableChain_mono` and `resolveDynTarget_mono`)
proves single-step preservation under `EnvExtends` and call-cone narrowing
simultaneously (supportedness only for the receiver pointer actually present).
Canaries: Schema 12 fails closed (`dyn_step_schema12_fails_closed`), Schema 13 enters
`<Circle as Area>::area` (`dyn_step_enters_impl`), a missing receiver is UB
(`dyn_step_missing_receiver_ub`), preservation under a further extension plus
narrowing (`dyn_step_preserved`), and the CFI trap (`dyn_cfi_trap`).

**Demand gating** (B1: `demandsDynSite`, `dynDemandStep`, `evalDynWithOpaqueCallees`)
issues the receiver read and `resolveDynTarget` only at states whose active step
demands `site.dynKey`; since A2 any *other* virtual call (`demandsUnregisteredDyn`)
fails closed (`dynDemandStep_of_unregistered`) instead of reaching the trusted static
resolver, which has no vtable and turns it into an unlinked external call
(`canary_unregistered_dyn_fails_closed`). It adds no other semantics:
`dynDemandStep_eq_dynDispatchStep_of_resolved` (identical to eager dispatch wherever
the eager query resolves on a well-formed site) and
`dynDemandStep_eq_trusted_of_not_demanded` (a step demanding no virtual call *is*
trusted `stepMirFn` under the frame condition).

**Multi-step preservation.** `evalDynWithOpaqueCallees_preserved` and B2's
`evalDynWithOpaqueCallees_preserved_of_narrow` (whose `runVisited` steps only the
*narrowed* table `narrowTbl`, never unfolding `fullTbl`): if every state the
`env₁` / `narrowTbl` run visits satisfies `DynStepPreserved`, the whole run is preserved
under `EnvExtends env₁ env₂` and narrowing; `dynStepPreservedB` is a decidable
per-state certificate (`dynStepPreserved_of_check`,
`evalDynWithOpaqueCallees_preserved_of_check`,
`evalDynWithOpaqueCallees_preserved_of_narrow_check`). Canaries, all through the
narrow-run theorem or kernel evaluation of the real trusted machine:
- `canary_dyn_e2e_full_run_schema13`: `if true { <dyn Area>::area() } else { g_dead() }`
  halts returning `31` on the narrowed table, and the extended + narrowed run equals
  the full run via `evalDynWithOpaqueCallees_preserved_of_narrow_check`.
- `canary_dyn_two_receivers` / `canary_dyn_two_receivers_preserved`: one run reaches
  the *same* `dyn Area` key with a `Circle` and then a `Square` receiver and returns
  `44`; a receiver-independent site returns `31` (wrong); Schema 12 faults
  `.unsupported`; preservation holds over all 10 visited states.
- `canary_dyn_deadBranch_schema12_succeeds` (**Part A + Part B synergy**): with
  `<dyn Area>::area()` on the dead branch of `if false`, Schema 12 (no vtable
  evidence) never demands `vtableMethodLookup` and halts returning `7`; proved equal
  to the Schema-13 full-table run via `evalDynWithOpaqueCallees_preserved_of_narrow_check`.
- `canary_dyn_supertrait_chain` (**B2 `charon#1611` supertrait vtable chaining**,
  rebuilt in A2 on `dynSubRoot` with the rustc call key `(Area::area, [dyn SubArea])`):
  a `dyn SubArea` receiver (vtable `11`) chains `.vtableSupertraitLookup 11 SubArea Area`
  (`→ .ok (.supertraitVTable 7)`) into `.vtableMethodLookup 7 Area 0`
  (`→ .ok ("proto::<impl Area for Circle>::area", [])`), halts returning `31`, and
  is preserved under `EnvExtends` + call-cone narrowing.
- `canary_dyn_site_mismatch_fails_closed` (A2): B2's original pairing — a
  `<dyn Area as Area>::area` key read through the `dyn SubArea` vtable chain — still
  resolves at the vtable level but is ill formed, and the run faults `.unsupported`.
- `canary_unregistered_dyn_fails_closed` (A2): the plain opaque evaluator turns
  `<dyn Area as Area>::area` into an external call to `proto::Area::area`; with a site
  for a different virtual call, `evalDynWithOpaqueCallees` refuses it.

## 5. Part C — `DecidableEq` without `BEq`

No prototype type derives or declares `BEq`; every real `Trusted` type in
`Trusted.Rustc.V2026_06_01.{Layout,MirAst,MirSemantics}` and
`Trusted.Rustc.V2026_08_01.{Layout,MirAst}` gets `DecidableEq` only (74 types: 65
`deriving instance` declarations plus 9 prototype-local `decEqOfCtorIdxProto`
instances for the enumeration types, covering all AST, layout, and machine-state types
including `CapturedMir`, `MachineState`, `Memory`, `StackFrame`, `LocalSlot`,
`BorrowEntry`, `TreeBorrowPerm`, `SavedCallerFrame`, `FnPtrEntry`, `MirCallReq`,
`Outcome`, and `MirExecState`, plus 2 manual axiom-free Boolean-reflection
`DecidableEq` instances for the nested inductives `RigidTy` and `Value` via
`rigidTyStructEq_iff` and `valueStructEq_iff`, and 21 inline `deriving DecidableEq`
prototype types including `StepView` and `RunResult`). Consequently, `==` is always
`instBEqOfDecidableEq` and the core `instLawfulBEq` gives `beq_iff_eq`
(`rigidTy_beq_iff_eq`, `layoutTable_beq_iff_eq`, `capturedMir_beq_iff_eq`,
`machineState_beq_iff_eq`, `treeBorrowPerm_beq_iff_eq`, …; `#synth LawfulBEq DemoKey`
and `#synth LawfulBEq TreeBorrowPerm` pinned to `instLawfulBEq`).
The worked demonstration (`ShadowingDemo`) installs the structural `BEq` a redundant
derivation would add on both `DemoKey` and the real audited `Trusted` type
`TreeBorrowPerm` (`theory/Correspondence/V2026_06_01/L4_TreeBorrows.lean:80`), pinning
the resulting `failed to synthesize LawfulBEq DemoKey` and
`failed to synthesize LawfulBEq TreeBorrowPerm`.

**Orphan instances must not create global names (A1).** Lean's enumeration deriving
handler emits `T.ofNat` / `T.ofNat_ctorIdx` in the *derived type's* namespace.
`Anneal.Rustc.V2026_06_01.TraceCheck` (imported by the `Anneal` root) already derives
`DecidableEq` for `AbiPassMode`, `UintTy`, `IntTy`, `FloatTy`, `Mutability`, `Safety`,
`UnOp`, `BinOp`, and `RetagKind`, so the B1 prototype failed in that closure with
nine `(kernel) constant has already been declared 'Trusted.….ofNat'` errors. These
nine now use `decEqOfCtorIdxProto` (auto-generated `T.ctorIdx` + a prototype-local
left inverse; axiom-free, kernel- and `decide`-evaluable); non-enumeration handlers
name everything hygienically in the current namespace. The benchmark's co-import
receipt compiles `import Anneal` + `import <compiled prototype>` and fails on any
error. Duplicate (non-colliding) `DecidableEq` instances remain for the 51
`V2026_06_01` types that `TraceCheck` also derives (and for `RigidTy` / `Value`,
which `TraceCheck` decides by its own Boolean reflection); `Decidable` is a
subsingleton, so this is harmless for `decide`, but Track A should define each
instance once, in `Trusted`.

## 6. Benchmark (`--sizes 4,16,64,128`)

Prototype compiled once into `/tmp` in 71.8 s; median of 3 repetitions per variant; heartbeats are Lean's raw `IO.getNumHeartbeats` deltas around `elabCommand` (elaboration + kernel check, `Elab.async false`), kHb = 1000 heartbeats. Co-import receipts **ok** (exit 0, 0 errors): `import Anneal` + `import` of the compiled prototype (no duplicate global constants, 4.2 s), and the prototype re-elaborated with `import Anneal` prepended, so its proofs, lazily generated equation lemmas, and bottom-of-file axiom and namespace-hygiene audit all run inside the library's import closure (64.2 s).

| M | linear_list kHb | opaque_o1 kHb | opaque_pruned kHb | linear_list ms | opaque_o1 ms | opaque_pruned ms | cert_gen live+dead kHb (one-time) |
|---|---|---|---|---|---|---|---|
| 4 | 1997.6 | 117.8 | 88.2 | 398.78 | 22.17 | 17.17 | 1179.0 |
| 16 | 6576.2 | 117.8 | 88.2 | 1188.77 | 20.07 | 13.84 | 4467.9 |
| 64 | 24679.6 | 117.8 | 88.3 | 5182.00 | 17.81 | 12.57 | 17508.8 |
| 128 | 45585.5 ✗ | 117.8 | 88.3 | 9144.87 ✗ | 20.10 | 14.75 | 34128.6 |

✗ `linear_list` at M = 128: Lean rejected the baseline proof (`(kernel) excessive memory consumption detected`); heartbeats / ms are those consumed until the failure.

| variant | heartbeats / callee (LSQ slope) | log-log slope | growth M_min → M_max |
|---|---|---|---|
| `linear_list` | 351953 | 0.908 | 22.82x |
| `opaque_o1` | 0 | 0.000 | 1.00x |
| `opaque_pruned` | 0 | 0.000 | 1.00x |
| `cert_gen_live` | 132888 | 0.942 | 25.97x |
| `cert_gen_dead` | 132892 | 1.007 | 32.74x |

| M | opaque_o1 heartbeat speedup | opaque_pruned heartbeat speedup | opaque_o1 wall speedup | opaque_pruned wall speedup |
|---|---|---|---|---|
| 4 | 17.0x | 22.6x | 18.0x | 23.2x |
| 16 | 55.8x | 74.5x | 59.2x | 85.9x |
| 64 | 209.5x | 279.6x | 290.9x | 412.3x |
| 128 | 386.9x | 516.5x | 455.1x | 619.8x |

**Reading (A2 run).** `linear_list` grows linearly with the table (log-log slope 0.91; 1998 → 24680 kHb from M = 4 to M = 64, and at M = 128 the kernel exhausts `anneal-lean-run`'s hardware-matched `lean -M` budget, so the naive proof does not check at all), while `opaque_o1` (117.8 kHb) and `opaque_pruned` (88.3 kHb) are flat (slopes 0.000 / 0.000): 209× / 280× fewer heartbeats than the baseline at M = 64. Pruning saves the dead arm's resolution *and* its certificate (29.5 kHb per step here). The one-time certificate generation (two certificates: 17509 kHb at M = 64, 34129 kHb at M = 128) is linear but amortized: at M = 64 it pays for itself after 1 symbolic step(s) that reuse the certificates.

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

### Round A1

1. **Part C integration blocker: orphan enumeration `deriving instance DecidableEq`
   collides with the `Anneal` library.** Lean's *enumeration* deriving handler emits
   global auxiliaries (`T.ofNat`, `T.ofNat_ctorIdx`) in the derived **`Trusted`**
   type's own namespace, not in the deriving module's namespace (A0 insight 7 saw these
   names but missed the consequence). `theory/Anneal/Rustc/V2026_06_01/TraceCheck.lean`
   — imported by the `Anneal` root (`theory/Anneal.lean:17`) — already derives
   `DecidableEq` for the same types, so compiling the B1 prototype in that import
   closure failed with nine errors, e.g.
   `(kernel) constant has already been declared 'Trusted.Rustc.V2026_06_01.MirAst.Mutability.ofNat'`
   (`AbiPassMode`, `UintTy`, `IntTy`, `FloatTy`, `Mutability`, `Safety`, `UnOp` from A0;
   `BinOp`, `RetagKind` added by B1's 36 → 74 expansion). The prototype could
   therefore never be added to the `Anneal` root or imported next to any module that
   imports it, and B1's roadmap item "port the 74 instances" would have broken the
   library build. Fixed: the nine enumeration types get prototype-local instances
   (`decEqOfCtorIdxProto` over the auto-generated `T.ctorIdx` plus a prototype-local
   left inverse, e.g. `instDecidableEqBinOpProto`); the 65 remaining `deriving
   instance` targets are non-enumerations, whose handler names everything
   hygienically in the current namespace. New receipt: the benchmark compiles a probe
   `import Anneal` + `import <compiled prototype>` and fails unless it elaborates with
   0 errors (`coimport` in the JSON, `test_prototype_coimports_with_anneal_root`),
   plus the static regression test `test_no_enum_deriving_for_trusted_types`.
2. **End-to-end fidelity bug: the vtable pointer was a constant, not the receiver's.**
   B1's `DynCallSite.vtablePtr : ProvenancePtr` was baked into the step function, so
   `UnOp.vtableMethodLookup` never read the machine state and every execution of a
   `dyn` call key dispatched to the same `impl`. In `charon#1611` the operand is the
   receiver's runtime metadata (`PtrMetadata(recv)`, or a supertrait vtable returned
   by a previous lookup). Fixed: `DynCallSite.vtableLocal` names the frame local
   holding the receiver's vtable pointer, `DynCallSite.vtablePtr?` reads it at call
   time (no initialized pointer ⇒ UB, `dyn_step_missing_receiver_ub`), and every
   theorem quantifies over the pointer actually present at `s`.
   `canary_dyn_two_receivers` runs one program that reaches the same `dyn Area` key
   with a `Circle` and then a `Square` receiver and returns `44`; the
   receiver-independent behaviour (`vtableLocal := 1`) returns `31` — wrong — and
   Schema 12 faults `.unsupported` at the first `dyn` call.
3. **Demand gating had no soundness theorem.** B1's `dynDemandStep` was a new
   semantics with no statement relating it to eager dispatch or to the trusted
   machine. Proved `dynDemandStep_eq_dynDispatchStep_of_resolved` (wherever the eager
   step resolves, the demand-gated step is identical, via
   `stepBranchPruned_redirect_of_not_demanded`) and
   `dynDemandStep_eq_trusted_of_not_demanded` (a non-`dyn` step *is* trusted
   `stepMirFn` under the frame condition): gating only removes failures of `dyn` calls
   that are not executed.
4. **Multi-step end-to-end preservation was canary-only.** B1 showed the narrowed /
   extended full run equal to the original only by brute-force kernel evaluation of
   both runs. Proved `evalDynWithOpaqueCallees_preserved` (per-visited-state
   `DynStepPreserved` ⇒ whole-run equality) and a decidable certificate
   (`dynStepPreservedB`, sound by `dynStepPreserved_of_check`,
   `evalDynWithOpaqueCallees_preserved_of_check`); `canary_dyn_e2e_full_run_schema13`
   and `canary_dyn_two_receivers_preserved` (10 visited states, two `dyn` demands with
   different receivers) now go through the theorem.
5. **Part A overclaim: `lookupCallee_hit_poly` is not `tbl.toList`-free.** Its
   `hnoTrait` hypothesis unfolds to
   `collectMatchingTraitImpls tbl.toList (extra ++ flatMapTraitImpls tbl.toList) …`, an
   `O(|trait impls|)` scan (discharged by `decide +kernel` in the canary), so the B1
   report's "stated purely over `tbl.lookupRaw` … eliminating raw `tbl.toList`
   reduction" was false; the certificate is also per `(defPath, typeArgs)` and
   excludes still-generic callers (`.param` first argument). Added
   `collectMatchingTraitImpls_of_no_impl`, `resolve_free_poly`, and
   `lookupCallee_hit_free_poly`: one per-`defPath` certificate
   (`hasTraitImplForDefPath … = false`, independent of `typeArgs`) rewrites *every*
   instantiation, including `.param` callers (`canary_free_poly_param_and_concrete`).
   Trait-dispatch certificates (`hwin`) remain one-time per-key scans; §2 now says so.
6. **Auto-generated equation lemmas are proven by the ambient import closure.**
   Re-elaborating the prototype *inside* the `Anneal.Rustc.V2026_06_01.TraceCheck`
   import closure (part of the `Anneal` root closure; before and after fix 1), the
   module audit flagged `rigidTyStructEq.eq_22`, `rigidTyStructEq.eq_def`, and the
   private matcher lemma `rigidTyStructEq.match_1.eq_22` with `Classical.choice`:
   `simp [rigidTyStructEq]` in `rigidTyStructEq_iff` lazily generates the catch-all
   equation, whose proof uses whatever simp set the importing environment provides —
   axiom-clean in the `Trusted`-only closure, `Classical` in the library closure. No
   headline theorem consumed those lemmas, but a Track A proof unfolding
   `rigidTyStructEq` would have. `rigidTyStructEq_iff` / `rigidTyListStructEq_iff` /
   `valueStructEq_iff` / `valueListStructEq_iff` now unfold each diagonal case with
   `show` (definitional unfolding, no equation lemmas), and the co-import receipt
   re-elaborates the whole prototype in the `Anneal` closure (`reelaborate_probe`), so
   the axiom audit also runs there.
7. **Report staleness.** B1's §6 still showed A0's benchmark numbers and its §1
   counts over-counted (`#guard_msgs`, `decide +kernel`); §1 and §6 are now measured
   on the A1 tree.

### Round B2

1. **Part B / E2E `charon#1611` supertrait vtable chaining (closing A1 Known Gap #8).**
   A1's `VTableMethodEntry` and `VTableMethodLookupOp` only modeled flat 1-hop vtable
   method lookup and could not chain supertrait vtable pointers (`SubArea : Area`,
   where calling `Area::area` on `dyn SubArea` first resolves the supertrait vtable
   pointer for `Area` via `UnOp.vtableMethodLookup` before looking up `Area::area`'s
   slot). B2 extends `VTableMethodEntry` with `supertraits : List (TraitRef × Nat) := []`,
   `CompilerQuery` with `.vtableSupertraitLookup`, `QueryAnswer` with `.supertraitVTable`,
   `QueryErr` with `.vtableSupertraitNotFound`, `evalCompilerQuery` with
   `evalVTableSupertraitLookup` (extending `query_schema12_unsupported_fallback` and
   `query_mono_schema` across all 5 `CompilerQuery` constructors), and
   `VTableMethodLookupOp` with `supertraitChain : List TraitRef := []` resolved by
   `resolveVTableChain` (`resolveVTableChain_mono`, generalized `resolveDynTarget_mono`).
   Pinned by `canary_dyn_supertrait_chain` (`11 (SubArea) → 7 (Area) → <Circle as Area>::area`
   returning `31`, missing supertrait link returning `.err (.vtableSupertraitNotFound …)`,
   and Schema 12 failing closed with `.unsupported .missingVTableEvidence`).
2. **Part B cross-dialect V06/V08 layout-table coherence invariant (closing A1 Known Gap #9).**
   A1 left layout-table coherence informal, requiring callers of `evalLayoutOf_v08_eq_v06`
   to supply `bridgeLayoutV08ToV06 tblV08 = env.layoutsV06` by hand. B2 defines the
   decidable coherence predicate `CompilerQueryEnv.isLayoutCoherent` (`bridgeLayout_iff_eq`,
   `isLayoutCoherent_of_schema_v06`), canonical bridged constructor
   `CompilerQueryEnv.withBridgedV08Layouts` (`withBridgedV08Layouts_isLayoutCoherent`,
   `withBridgedV08Layouts_extends`), `evalLayoutOf_v08_eq_v06_of_coherent`,
   `isLayoutCoherent_preserved_of_v08_present`, and the negative falsification canary
   `incoherence_breaks_dialect_agreement_canary` proving that an incoherent V08 table
   causes V08 and V06 `layoutOf` queries to return different layouts.
3. **Part A `@[irreducible] OpaqueCalleeTable.traitImpls` and `tbl.toList`-free free-generic and trait-dispatch certificates.**
   In A1, `lookupCallee_hit_free_poly` still carried `flatMapTraitImpls tbl.toList` in
   its `hnoImpl` hypothesis, and `lookupCallee_trait_hit`'s `hwin` invoked
   `collectMatchingTraitImpls tbl.toList (extra ++ flatMapTraitImpls tbl.toList)`,
   scanning `tbl.toList` both in `flatMapTraitImpls` and in `findCallee? tbl.toList entry.implPath`.
   B2 seals `OpaqueCalleeTable.traitImpls` (`@[irreducible]`, `traitImpls_ofList`), proves
   `lookupCallee_hit_free_poly_opaque`, defines `collectMatchingTraitImplsWith`
   parameterized by an abstract `lookupRaw` (`collectMatchingTraitImpls_eq_with`), proves
   step lemmas `collectMatchingTraitImplsWith_cons_ne_path`,
   `collectMatchingTraitImplsWith_cons_ne_args`, and
   `collectMatchingTraitImplsWith_cons_hit_mono` (which rewrites each matching impl body
   lookup in `O(1)` via its `tbl.lookupRaw` certificate), and proves the completely
   `tbl.toList`-free `lookupCallee_trait_hit_cert`, pinned by `canary_free_poly_opaque_cert`
   and `canary_trait_cert_no_toList`.
4. **End-to-end narrow-run multi-step preservation (`evalDynWithOpaqueCallees_preserved_of_narrow`).**
   A1's `evalDynWithOpaqueCallees_preserved` and `evalDynWithOpaqueCallees_preserved_of_check`
   computed `runVisited` from the *full*-table run (`dynDemandStep env₁ fullTbl`), forcing
   `decide +kernel` in the E2E canaries to step `dynFullTbl`. B2 proves
   `evalDynWithOpaqueCallees_preserved_of_narrow` and
   `evalDynWithOpaqueCallees_preserved_of_narrow_check`, whose `runVisited` steps only the
   *narrowed* table `narrowTbl`, and updates `canary_dyn_e2e_full_run_schema13`,
   `canary_dyn_deadBranch_schema12_succeeds`, `canary_dyn_two_receivers_preserved`, and
   `canary_dyn_supertrait_chain` to use `_of_narrow_check`.
5. **Part C self-enforcing zero-namespace-leak audit in `run_cmd` and real `TreeBorrowPerm` shadowing proof.**
   A1's bottom-of-file `run_cmd` computed `constants` and `inNamespace` without asserting
   `constants == inNamespace` (`leaked.isEmpty`), so an orphan enumeration `deriving instance`
   leaking `Trusted.….ofNat` would pass the in-file `run_cmd` audit and only fail in the
   external co-import script. Furthermore, `test_no_enum_deriving_for_trusted_types` only
   checked the first target after `for` (`toks[j + 1][1]`), missing comma-separated targets
   like `deriving instance DecidableEq for Foo, Mutability`, and `ShadowingDemo` only
   tested a toy `DemoKey` inductive rather than any real audited `Trusted` type from §7.
   B2 enforces `leaked.isEmpty` (`0` constants outside `Anneal.DemandCompilerQueryAndOpaqueCalleePrototype`)
   and `inNamespace ≥ 1400 && theorems ≥ 140` inside `run_cmd`, updates
   `test_no_enum_deriving_for_trusted_types` to parse all comma-separated targets after `for`
   across all 16 `Trusted` enumeration types, and adds `treeBorrowPerm_beq_iff_eq` +
   `ShadowedTreeBorrowPerm` on the real audited `Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm`.
6. **Part C scanner fixes (`rust_string_literals` & `coimport_check` in `scripts/bench_opaque_callee_and_query_proto.py`).**
   Fixed three bugs in the Python scanner/harness:
   - `rust_string_literals` looped infinitely (`j = 0`) on unclosed `\u{` escape sequences
     because `text.find("}", j + 3)` returned `-1` and `j = -1 + 1 = 0` reset the cursor.
   - `rust_string_literals` stripped `\n` on Rust `\<newline>` string continuations,
     shifting subsequent line numbers in `audit_rust_codegen_text`.
   - `rust_string_literals` did not recognize Rust C-string literals (`c"..."` and `cr#"..."#`),
     and `coimport_check` only checked case-sensitive `"error" in line` while ignoring
     warnings, panics, and sorrys.
   All are fixed and pinned by `test_rust_c_strings_line_continuation_and_unclosed_unicode`
   and `test_b2_headline_theorems_present`.

### Round A2

1. **End-to-end soundness: ill-typed `dyn` sites were accepted.** Nothing tied a
   `DynCallSite`'s call key to the vtable chain it reads. B2's own
   `canary_dyn_supertrait_chain` dispatched a `<dyn Area as Area>::area` call (key
   `[dyn Area]`) through a `dyn SubArea` receiver vtable (chain `[SubArea]`): a
   `dyn Area` call resolved through a vtable of a different trait, and the canary
   "succeeded". Added `dynSelfTrait?` and `DynCallSite.wellFormed` (the call key must
   be a virtual call whose receiver type `dyn D` names the trait of the *first* vtable
   the lookup reads), checked by `dynDispatchStep`, which fails closed
   (`MirStepNode.unsupported`, a configuration error never attributed to the program;
   `dynDispatchStep_of_not_wellFormed`). The supertrait canary is rebuilt on
   `dynSubRoot` with the call key rustc emits, `(Area::area, [dyn SubArea])`
   (`dynSubSite_wellFormed`); `canary_dyn_site_mismatch_fails_closed` shows B2's
   pairing still resolves at the vtable level but now faults `.unsupported`.
2. **End-to-end soundness: unregistered virtual calls fell through to static
   resolution.** `dynDemandStep` handled only `site.dynKey`; every other
   `<dyn T as T>::m` call was stepped by the trusted static resolver, which has no
   vtable. Since `dyn T` has no layout, no body instantiates and the virtual call
   silently became an *unlinked external call* to the trait method's `DefPath`
   (`canary_unregistered_dyn_fails_closed`, first conjunct) — in any program with a
   second virtual call key (another method, another trait). Added
   `demandsUnregisteredDyn`: unregistered virtual calls fail closed
   (`dynDemandStep_of_unregistered`). Classification is by call key (first generic
   argument `dyn D`), so a static call to a generic function instantiated at a `dyn`
   type is refused too — an incompleteness, never unsound (the trusted resolver could
   not instantiate it either); Track A can classify by the lowering's trait-method
   `DefPath` instead; `dynDemandStep_eq_dynDispatchStep_of_resolved`
   and `dynDemandStep_eq_trusted_of_not_demanded` carry the extra hypothesis and
   `dynDemandStep_preserved` covers the new case.
3. **`UnOp.vtableMethodLookup` had become dead code in dispatch.** B2's
   `resolveDynTarget → resolveVTableChain` evaluated `CompilerQuery` constructors
   directly; `UnOpExt.query?` survived only inside a canary, so the end-to-end chain
   no longer went through the `UnOp` the brief requires. `resolveVTableChain` now
   issues every hop through `UnOpExt.query?` — one `UnOp::VTableMethodLookup`
   application per supertrait hop and per final method read, as in `charon#1611` —
   with `resolveVTableChain_mono` re-proved.
4. **Canary docstring drift.** Item 4 of B2's supertrait canary docstring named
   `dynEnv13` / `dynTraitRef` while the statement used `dynSubEnv13` /
   `dynSubTraitRef`; fixed in the rewrite.

### Rounds A3–A4

_(appended by later rounds)_

## 9. Integration roadmap for `ws-demand-time-compiler-queries-and-opaque-callee-table`

1. **Table + certificates.** Land `OpaqueCalleeTable` (+ `opaqueCalleeTable_lookup_eq_trusted`
   and `OpaqueCalleeTable.traitImpls`) next to the symbolic evaluator; have
   `anneal-rustc-capture` emit, per captured callee, a single-declaration
   `lookupRaw_ofList_append_cons_of_skips` certificate (kernel-evaluated `stringEq`
   skips; or one `Nodup` witness per table plus membership certificates via
   `lookupRaw_ofList_of_mem_nodup`) and one per-table `traitImpls_ofList` certificate
   beside `Mir/<Item>.lean`.
2. **Stepping.** Rewrite callee resolution with `lookupCallee_hit_mono` /
   `lookupCallee_hit_free_poly_opaque` / `lookupCallee_hit_poly` /
   `lookupCallee_trait_hit_cert` / `lookupCallee_trait_hit_poly` /
   `lookupCallee_trait_default_hit` instead of unfolding `findCallee?`;
   use `stepTerminatorWith_litSwitch` (or an equivalent simp lemma stated directly on
   trusted `evalTerminator`, justified by `stepTerminatorWith_prune_exact`).
3. **Frame lemma (condition).** Prove trusted `stepMirFn` preserves `memory.callees`
   and `memory.traitImpls`; this discharges the frame hypothesis of
   `evalWithOpaqueCallees_eq_trusted` for all runs.
4. **Cone narrowing (condition).** Narrow by demanded-key agreement (run the pruned
   evaluator once on the full table, or a static over-approximation that keeps every
   body contributing `TraitImplEntry` records); never by `DefPath` reachability. Use
   `evalDynWithOpaqueCallees_preserved_of_narrow_check` so visited-state checks run only
   on the narrowed table.
5. **Query env (condition).** Wire `CompilerQueryEnv` to lean-miri Schema 12/13
   decoding; keep the CFI demand in the query key, gate V08 layouts and every
   Schema-13 field by schema, and treat `.unsupported` as fail-closed in the stepper.
6. **Bridge commutation & layout-table coherence (completed in prototype in B1/B2).**
   Universal cross-dialect `computeLayout` commutation (`computeLayout_bridge_commutes`,
   `computeLayoutV08Bridged_eq_computeLayoutV06_bridge`, `evalLayoutOf_v08_eq_v06`) and
   decidable layout-table coherence (`CompilerQueryEnv.isLayoutCoherent`,
   `withBridgedV08Layouts`, `evalLayoutOf_v08_eq_v06_of_coherent`) are proven across all
   21 `RigidTy` constructors; port into `Trusted` / `Correspondence` alongside the query
   environment.
7. **`DecidableEq` without `BEq`, defined once (condition).** Move `DecidableEq` for
   the 74 `Trusted` AST/layout/machine types *into* `Trusted` (one definition each;
   never orphan-derive an enumeration type, whose deriving handler emits global
   `T.ofNat` names — A1 §8 item 1, now enforced at elaboration time by the B2 `run_cmd`
   `leaked.isEmpty` check), delete the duplicates in
   `Anneal.Rustc.V2026_06_01.TraceCheck`, replace the 10 audited
   `deriving …, BEq, DecidableEq …` clauses in `theory/Correspondence/` (§7) with
   `DecidableEq` only, and add the scanner plus the co-import receipt to CI.
8. **Receiver-driven `dyn` dispatch & supertrait vtable chaining (completed in prototype in A1/B2).**
   Read the vtable pointer from the receiver at call time (`DynCallSite.vtablePtr?`) and
   chain supertrait vtable hops via `.vtableSupertraitLookup` / `resolveVTableChain`
   (`canary_dyn_supertrait_chain`) when lowering `charon#1611` MIR.
9. **`dyn` site registry from the lowered MIR (condition).** Derive one
   `DynCallSite` per virtual call key from the `charon#1611` lowering (receiver local,
   hop chain, caller ABI, CFI type) so that `DynCallSite.wellFormed` holds by
   construction, and generalize the prototype's single registered site to a
   registry; unregistered virtual calls must keep failing closed
   (`dynDemandStep_of_unregistered`), never reach the trusted static resolver.

## 10. Receipts (A2, run fresh after the final edit)

Receipt 1 (`export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"`) precedes every command.

| # | command | exit | result |
|---|---|---|---|
| 2 | `anneal-lean-run --mode file --concurrency 1 -- lake env lean theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean` | 0 | 0 error lines, 0 warning lines, 0 sorry lines, empty output (79 s) |
| 3 | `python3 -B -m unittest -v scripts/test_bench_opaque_callee_and_query_proto.py` | 0 | Ran 47 tests in 160.618s: OK, 0 skips |
| 4 | `python3 tools/anneal-lsp/server/proof_health.py theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean` | 0 | 0 output lines (0 findings) |
| 5 | `python3 -B scripts/bench_opaque_callee_and_query_proto.py --sizes 4,16,64,128 --json` | 0 | JSON with 4 sizes × 3 variants + certificates + co-import receipt `import Anneal` + prototype: ok (exit 0, 0 errors) + repo audit (233 s) |
| 6 | `git status --porcelain`; `git diff --name-status 86255c4698c28ce695b37e82f5a151896f7f736a..HEAD` | 0 | pre-commit: only deliverables modified; post-`[adv A2]`-commit: empty status and exactly `A PROTOTYPE_REPORT.md`, `A scripts/bench_opaque_callee_and_query_proto.py`, `A scripts/test_bench_opaque_callee_and_query_proto.py`, `A theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean` |

`scripts/__pycache__` directories: 0.

Receipts were run twice: a measurement run (whose benchmark JSON fills §6 / §7) and, after these report edits, a verification run on the final tree; both exited `0` on every command.
