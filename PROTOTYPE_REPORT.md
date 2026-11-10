# Prototype Report: Independent MIR Fault-Site Census & Fail-Closed Coverage Reconciler

- **Workstream ID**: `ws-proto-fault-site-coverage-reconciler` (`ep1-prototype-fault-site-census-and-reconciler`)
- **Track**: Track P (`prototype`, isolated from `unstable` and `main`)
- **Target Paired Track A Workstream**: `ws-fault-site-coverage-reconciler`
- **Current Pass**: `[adv B4]` (Round 4 critique & fix of `[adv A3]`)

---

## 0. GO/NO-GO Assessment (`[adv B4]`)

**Recommendation: GO** for the paired Track A workstream `ws-fault-site-coverage-reconciler`, under the preconditions listed below. The prototype shows that an independent census, reconciled fail-closed against the obligation generator's tagged sites, closes the "omitted fault site ⇒ vacuous `VERIFIED`" failure mode. Every step of that argument is kernel-checked against the trusted MIR semantics, except the steps marked *tested* below.

**Kernel-checked** (Lean 4, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `Classical.choice`):
- *One-step census completeness* for the active body (subject or inline callee). It covers every UB exposure, including UB raised inside external-call continuations.
- *Construct precision*: an exact `.ub` characterization for the §2.1 constructs, and no blanket class dump anywhere.
- *Fail-closed reconciliation*: registry gating, partial-site detection, and per-body batches.
- *Multi-step safety along real top-level executions*, including through external calls (`[adv B4]` `MirStepsTop`). It holds for every state reached from `initMachineState` by `stepMirFn` steps and top-level-answered external calls: if that state's next step can expose UB, the faulting site is discharged with an `emittedAndVerified` class.

**Tested, not proved** (Rust):
- Lean ↔ Rust census agreement: 400-body real-emitter fuzz, a 400-`#guard` Lean-evaluated differential, kernel-checked witness parity, and a real `rustc` corpus.
- The strict `Mir/<Item>.lean` scanner (lexer traps, truncation, dialect pinning).
- The native-callee lists, now pinned to the trusted Lean source (`[adv B4]`).

**Preconditions for Track A** (any one failing is a NO-GO for relying on `VERIFIED`):
1. Obligations carry `FaultSite`s computed over the *emitted* (retag-stripped) body (§7.3).
2. Every inline callee body is reconciled as its own batch item, with `CalleeClosure` filled from the exact callee list. Generic callees must satisfy `bodyHasNoParamCallConst` or be supplied instantiated.
3. External-call specs answer at the caller's frame (`MirCallAnsTopFrame`). This is an assumption about the environment, not something checked.
4. Bodies satisfy `cfgTargetsInBounds`. Out-of-bounds targets are still censused (`boundsCheck`), but the trace theorems assume in-bounds CFGs.

**Residual risks**:
- Multi-step traces do not yet follow execution *into* inline callee frames. Each inline step is covered one step at a time by the batch theorem, but no single relation chains caller and callee frames.
- Class-precise attribution exists only for the §2.1 constructs. Elsewhere completeness is existential in the class.

---

## 1. Executive Summary

This Track P prototype builds a defense-in-depth cross-check for Anneal's MIR verification pipeline against the silent false-proof failure mode ("the obligation generator omits a fault site, so the item reports `VERIFIED` vacuously"). Instead of trusting `cargo-anneal`'s obligation generator to enumerate every runtime UB condition, it adds two independent components:

1. **Lean 4 independent fault-site census and completeness proofs** (`theory/Anneal/FaultSiteCensusPrototype.lean`):
   - 12 canonical `MirFaultClass` categories, `FaultSite`, `PropertyStatus`, `PropertyRegistry`.
   - An independent structural walker `censusMirBodyFaultSites (body : CapturedMir) : List FaultSite` over `Trusted.MirAst`, duplicate-free (`censusMirBodyFaultSites_nodup`).
   - Completeness over `Trusted.MirSemantics.stepMirFn` (`stepMirFn_activeBody_fault_in_census`, `stepMirFn_fault_in_census`), over every **one-step UB exposure** including `.faulted .ub` continuations of external calls (`stepMirFn_exposesUb_in_census`, `stepMirFn_extCall_cont_fault_in_census`), over **arbitrary-length intra-frame execution traces** (`MirStepsIntra`, `mirStepsIntra_preserves_validMirPc`, `initMachineState_mirStepsIntra_exposesUb_in_census`, `[adv A2]`), and over **multi-step execution traces across external-call continuations** (`MirStepsWithExtCalls`, `mirStepsWithExtCalls_preserves_validMirPc`, `initMachineState_mirStepsWithExtCalls_exposesUb_in_census`, `[adv A3]`).
   - **Semantic precision & interprocedural PC certificates** (`[adv B1]` + `[adv A1]` + `[adv A2]` + `[adv A3]`):
     - Class-level justification of `BinOp` (`censusBinOpFaultClasses_exact`, `evalScalarBinOp_ub_cause`), `StorageLive`/`StorageDead`/`Return`/`Goto`/borrow `.ub` edges.
     - `[adv A1]` exact `.ub` characterizations and non-overapproximation proofs for unevaluated `Rvalue` assignments (`evalRvalue_eq_unsupported_of_rvalueUnevaluated`, `evalStmt_assign_unevaluated_eq_unsupported`), `PlaceMention` (`evalStmt_placeMention_ub_iff`), unprojected and deref-projected `Deinit` / `Drop` (`evalStmt_deinit_unprojected_ub_iff`, `evalStmt_deinit_deref_eq_unsupported`, `evalTerminator_drop_unprojected_ub_iff`), `CastKind.pointerCoercion "MutToConstPointer"` (`evalRvalue_cast_mutToConstPointer_ub_iff`), and diverging `Call` destination irrelevance (`evalTerminator_diverging_call_exposesUb_destination_irrelevant`).
     - `[adv A1]` / `[adv A3]` interprocedural and external-call `ValidMirPc` preservation across `pushCalleeFrame`, `pushDivergingCalleeFrame`, `enterTailCalleeFrame`, inline `TerminatorKind.return_`, `applyUnwindAction`, `resumeExternalCall`, `resumeExternalDivergingCall`, `resumeExternalTailCall`, and `unwindFromCallStack` (`validMirPc_pushCalleeFrame`, `validMirPc_pushDivergingCalleeFrame`, `validMirPc_enterTailCalleeFrame`, `validMirPc_return_inline`, `validMirPc_applyUnwindAction_top`, `validMirPc_resumeExternalCall`, `validMirPc_resumeExternalDivergingCall`, `resumeExternalTailCall_top_ne_running`, `validMirPc_unwindFromCallStack`, `validMirPc_resumeExternalTailCall`).
     - `[adv A2]` exact `.ub` characterizations and completeness for operands, unprojected local writes, `StatementKind.intrinsic (.assume _)`, and `TerminatorKind.assert` (`evalOperand_unprojected_copy_ub_iff`, `evalOperand_unprojected_move_ub_iff`, `evalOperand_ub_implies_mem_censusOperand`, `writePlaceValue_unprojected_ub_iff`, `evalStmt_intrinsic_assume_ub_iff`, `evalTerminator_assert_cleanup_or_terminate_ub_iff`).
     - `[adv A2]` / `[adv A3]` partial-coverage site rejection, census-append decomposition, registry monotonicity, and multi-step reconciled trace safety (`reconcileFaultCoverageWithRegistry_partial_site_rejected`, `reconcileFaultCoverageWithRegistry_append_verified_iff`, `reconcileFaultCoverageWithRegistry_mono`, `initMachineState_mirStepsIntra_reconciled_safety`, `initMachineState_mirStepsIntra_not_exposesUb_of_empty_census`, `initMachineState_mirStepsWithExtCalls_reconciled_safety`).
     - `[adv B3]` / `[adv A3]` per-body batch reconciliation for a subject plus its inline callees (`CoverageBatch`, `reconcileCoverageBatch`, `reconcileCoverageBatch_nil`, `reconcileCoverageBatch_iff`, `reconcileCoverageBatch_mono`, `stepMirFn_exposesUb_in_batch_discharged`), polymorphic generic-callee instantiation invariance (`censusMirBodyFaultSites_instantiate`, `cfgTargetsInBounds_instantiate`, `validMirPc_instantiate_iff`, `stepMirFn_exposesUb_in_batch_discharged_instantiated`, `[adv A3]`), and a kernel-checked counterexample showing that reconciling appended caller and callee censuses against one shared obligation list is unsound (`witnessCalleeMask_append_masks_batch_rejects`, `witnessCalleeStorage_masked_site_live`).
     - `[adv B4]` semantic multi-step traces through external calls (`stepMirFn_extCall_cont_preserves_validMirPc`, `MirStepsTop`, `mirStepsTop_preserves_validMirPc`, `initMachineState_mirStepsTop_exposesUb_in_census`, `initMachineState_mirStepsTop_reconciled_safety`, `witnessExtCall_mirStepsTop_nonvacuous`). The relation is generated by `stepMirFn` itself, so its safety theorems cover real top-level executions.
   - Fail-closed reconciler theorems and kernel-checked `by decide` witnesses (`0` `sorryAx`, `0` `Lean.ofReduceBool`), with kernel-evaluated **liveness certificates** for every false-proof probe site. `[adv B3]` / `[adv A3]`: every theorem (`208/208`, including `private` ones) is `Classical.choice`-free.
2. **Rust registry, census frontends, fail-closed reconciler and probes** (`crates/cargo-anneal/src/fault_census_proto.rs`):
   - 1-to-1 `MirFaultClass`, `FaultSite`, `PropertyStatus`, `PropertyDescriptor`, `PropertyRegistry`, `ProtoAggregateKind`, `ItemCoverageInput`, `CalleeClosure`, `MultiItemCoverageVerdict`.
   - Three census frontends: `census_mir_fault_sites(&ProtoMirBody)`, `census_ir_captured_mir(&IrCapturedMir)`, and the fail-closed Lean scanners `census_lean_mir_module(&str)` (strict emitter-module grammar with scope-stack and dialect-pinning enforcement) and `census_lean_mir_def(&str, &str)` (named-definition extraction for the witness file).
   - `reconcile_obligation_coverage`, `reconcile_lean_mir_coverage`, and `reconcile_multi_item_coverage`. The last one reconciles each body of a caller/callee batch against its own obligations, recomputes every census from the item's body, checks item labels, and enforces terminator-kind-sensitive native-intrinsic / inline / external callee closure (`is_natively_modeled_converging_call_callee`, `is_natively_modeled_diverging_call_callee`, `reified_fn_def_paths`, `[adv A3]`).
   - The four false-proof probes driven by an independent mock obligation emitter, the registry probe, the randomized emitter differential fuzzer, a real `rustc`-captured corpus test, and the cross-language Lean-to-Rust parity test.

---

## 2. Lean 4 Theorem Inventory (`theory/Anneal/FaultSiteCensusPrototype.lean`)

Every declaration elaborates with **zero `sorryAx`** and **zero `Lean.ofReduceBool`**.

| Category | Declaration(s) | Statement |
| :--- | :--- | :--- |
| Taxonomy | `MirFaultClass.mem_all`, `MirFaultClass.nodup_all`, `MirFaultClass.length_all` | `all` lists exactly the 12 classes, duplicate-free. |
| | `MirFaultClass.toRank_lt_twelve`, `MirFaultClass.ofRank?_toRank`, `MirFaultClass.toRank_injective` | Rank encoding `0..11` with round trip and injectivity. |
| | `MirFaultClass.fromStr?_asStr`, `MirFaultClass.asStr_fromStr?`, `MirFaultClass.asStr_injective` | Canonical `snake_case` names (shared with Rust) round-trip. |
| Registry | `PropertyStatus.isVerified_eq_true_iff`, `PropertyStatus.isVerified_eq_false_iff`, `registryWithStatus_self`, `registryWithStatus_ne` | Registry status semantics and point overrides. |
| Dedup / Nodup | `mem_dedupFaultClasses_iff`, `nodup_dedupFaultClasses`, `censusMirBodyFaultSites_nodup` | Canonical per-site dedup; the whole census is `Nodup`. |
| Membership | `mem_censusStmtsAux_of_get?`, `mem_censusBlockFaultSites_of_stmt`, `mem_censusBlockFaultSites_of_terminator`, `mem_censusBlocksAux_of_get?`, `mem_censusMirBodyFaultSites_of_block` | Structural membership of `(bb, stmt, cls)` sites. |
| Pure constructs never fault | `evalStmt_pure_constructs_ne_ub`, `evalTerminator_pure_constructs_ne_ub`, `evalOperand_constant_non_indirect_ne_ub` | `.nop`/`.coverage`/`.constEvalCounter`/`.backwardIncompatibleDropHint`, `.goto`/`.unwindTerminate`/`.inlineAsm`, and non-`.indirect` constants never return `.ub`. |
| Valid PC / CFG & Interprocedural PC | `ValidMirPc`, `cfgTargetsInBounds`, `validMirPc_initMachineState`, `stepMirFn_preserves_validMirPc`, `validMirPc_pushCalleeFrame`, `validMirPc_pushDivergingCalleeFrame`, `validMirPc_enterTailCalleeFrame`, `validMirPc_return_inline`, `MirStepsIntra`, `mirStepsIntra_preserves_validMirPc`, `validMirPc_applyUnwindAction_top`, `validMirPc_resumeExternalCall`, `validMirPc_resumeExternalDivergingCall`, `resumeExternalTailCall_top_ne_running`, `validMirPc_unwindFromCallStack`, `validMirPc_resumeExternalTailCall`, `MirStepsWithExtCalls`, `mirStepsWithExtCalls_preserves_validMirPc` | Entry PC is valid; intra-frame steps, external-call continuations (`MirStepsWithExtCalls`), unwind propagation over `ValidCallStack`, and interprocedural call/tail-call/inline-return transitions preserve `ValidMirPc`. |
| Construct classification | `evalOperand_ub_implies_mem_censusOperand`, `evalStmt_exposesUb_implies_mem_censusStmt`, `evalTerminator_exposesUb_implies_mem_censusTerminator` (and `.fail .ub` corollaries `evalStmt_ub_implies_mem_censusStmt`, `evalTerminator_ub_implies_mem_censusTerminator`) | Any UB exposure of an operand, statement, or terminator implies a non-empty construct census. |
| Completeness | `stepMirFn_activeBody_exposesUb_in_census`, `stepMirFn_exposesUb_in_census`, `stepMirFn_extCall_cont_fault_in_census`, `stepMirFn_activeBody_fault_in_census`, `stepMirFn_fault_in_census`, `initMachineState_mirStepsIntra_exposesUb_in_census`, `initMachineState_mirStepsWithExtCalls_exposesUb_in_census` | Every UB exposure from a valid PC (active callee, top level, or after any `MirStepsIntra` / `MirStepsWithExtCalls` trace from `initMachineState`) is censused at that PC. |
| Zero-census corollaries | `stepMirFn_not_exposesUb_of_site_uncensused`, `stepMirFn_ne_ub_of_site_uncensused`, `stepMirFn_ne_ub_of_empty_census`, `initMachineState_mirStepsIntra_not_exposesUb_of_empty_census` | An uncensused PC (or a body with empty census along any intra-frame trace from entry) exposes no UB, directly or through any continuation. |
| Reconciler | `mem_unmappedFaultSites_iff`, `mem_unmappedFaultSitesWithRegistry_iff`, `reconcileFaultCoverage_verified_iff`, `reconcileFaultCoverage_unknown_nonempty`, `reconcileFaultCoverageWithRegistry_verified_iff`, `reconcileFaultCoverageWithRegistry_rejects_unemitted`, `reconcileFaultCoverage_mutation_detected`, `reconcileFaultCoverageWithRegistry_partial_site_rejected`, `reconcileFaultCoverageWithRegistry_append_verified_iff`, `reconcileFaultCoverageWithRegistry_mono` | Soundness and completeness of the fail-closed verdict. Non-verified registry classes can never be discharged. Stripping any census site is detected, even when other classes at the same `(bb, stmt)` are discharged. Also: census-append decomposition (a sound composition principle only for censuses of the *same* body, `[adv B3]`) and registry monotonicity. |
| Per-body batch (`[adv B3]` + `[adv A3]`) | `CoverageBatch`, `reconcileCoverageBatch`, `reconcileCoverageBatch_nil`, `CoverageVerdict.isVerified_iff`, `reconcileCoverageBatch_iff`, `reconcileCoverageBatch_mono`, `stepMirFn_exposesUb_in_batch_discharged`, `stepMirFn_exposesUb_in_batch_discharged_instantiated` | A batch verifies iff it is non-empty (`[adv A3]`) and every body reconciles against its *own* obligation list. If the active body `s.memory.activeCallee.getD body` (subject, non-generic inline callee, or generic `calleeBody.instantiate subst`, `[adv A3]`) is in a verified batch with a valid PC, every one-step UB exposure is discharged in that body's own list with an `emittedAndVerified` class. |
| Generic instantiation invariance (`[adv A3]`) | `censusStmtFaultClasses_instantiate`, `censusTerminatorFaultClasses_instantiate`, `censusMirBodyFaultSites_instantiate`, `cfgTargetsInBounds_instantiate`, `validMirPc_instantiate_iff` | `CapturedMir.instantiate subst` preserves statement censuses, terminator censuses (when `bodyHasNoParamCallConst body = true`), full body censuses, `cfgTargetsInBounds`, and `ValidMirPc`. |
| End-to-end bridge | `stepMirFn_fault_in_discharged_of_reconciled`, `stepMirFn_exposesUb_in_discharged_of_reconciled`, `initMachineState_mirStepsIntra_reconciled_safety`, `initMachineState_mirStepsWithExtCalls_reconciled_safety` | A reconciled body discharges (with an `emittedAndVerified` class) every UB exposure at a valid top-level PC and along any `MirStepsIntra` / `MirStepsWithExtCalls` trace from `initMachineState`. |
| Semantic traces through external calls (`[adv B4]`) | `TermStepPreservesPc` (external-call case), `StmtStepPreservesPc` (statements never call), `stepMirFn_extCall_cont_preserves_validMirPc`, `MirStepsTop`, `mirStepsTop_of_mirStepsIntra`, `mirStepsTop_preserves_validMirPc`, `initMachineState_mirStepsTop_exposesUb_in_census`, `initMachineState_mirStepsTop_reconciled_safety`, `witnessExtCall_mirStepsTop_nonvacuous` | `MirStepsTop` is generated by `stepMirFn` itself: intra-frame steps, plus external calls whose continuation keeps running under a top-level answer. Every such continuation resumes at `stmtIdx = 0` of an in-bounds successor block. So census completeness and reconciled safety hold along every real top-level execution from `initMachineState`. A concrete external-call step inhabits the relation (`rfl`). |

### 2.1 Semantic Precision Certificates (`[adv B1]` + `[adv A1]` + `[adv A2]`)

| Declaration | What it proves against `Trusted.MirSemantics` |
| :--- | :--- |
| `evalScalarBinOp_ne_ub_of_census_nil` | Every `BinOp` with census `[]` (wrapping `add`/`sub`/`mul`, flagged `*WithOverflow`, masked `shl`/`shr`, bitwise, comparisons, `cmp`) can never make `evalScalarBinOp` return `.ub`. |
| `BinOpFaultCause`, `evalScalarBinOp_ub_cause` | Class-precise completeness: each `.ub` of `evalScalarBinOp` is explained by a class in `censusBinOpFaultClasses op` *and* its concrete cause. |
| `censusBinOpFaultClasses_exact` (+ `evalScalarBinOp_*_ub_witness`) | For every scalar operator, census `= []` **iff** `evalScalarBinOp` can never fault — no over- and no under-approximation, with concrete faulting inputs (`rfl`) for every non-empty entry. |
| `evalStmt_storageLive_ub_iff`, `evalStmt_storageDead_ub_iff` | Exact edges: fault iff `loc ≥ locals.length` or an active protector protects a borrow of `loc` (`hasProtectedLocalBorrow`). |
| `evalTerminator_unreachable_ub` | `Unreachable` always faults. |
| `evalTerminator_return_root_ub_iff`, `evalTerminator_return_inline_ub_iff` | Root frame: fault iff `_0` is not initialized. Inline frame: additionally iff the caller expected a diverging callee or the write into `caller.destination` faults. |
| `stepMirFn_after_goto_oob_ub` | An out-of-bounds `Goto` steps successfully but makes the *next* `stepMirFn` fault — the reason the census labels that `Goto` site with `.boundsCheck`. |
| `evalRvalue_borrow_nonDeref_ub_iff` | Borrowing (`Ref`/`RawPtr`) a place whose projection does not start with `.deref` faults iff the root local is missing/dead or an `.index` local is uninitialized — justifying the `[.uninitRead]` census. |
| `evalRvalue_eq_unsupported_of_rvalueUnevaluated`, `evalStmt_assign_unevaluated_eq_unsupported` (`[adv A1]`) | Every `Rvalue` with `rvalueUnevaluated rv = true` (`.threadLocalRef`, `.nullaryOp`, `.shallowInitBox`, float casts, `.aggregate (.coroutine _) _`) returns `.unsupported` immediately in `evalRvalue`, so `evalStmt (.assign dst rv)` steps unconditionally to `MirStepNode.unsupported` without inspecting `dst` and emits `[]`. |
| `evalStmt_placeMention_ub_iff` (`[adv A1]`) | `PlaceMention` faults iff `place.local_` is out of bounds/dead or `placeMentionOperandsInit` is false (never dereferencing pointers or checking alignment/bounds/downcasts), matching `[.uninitRead]`. |
| `evalStmt_deinit_unprojected_ub_iff`, `evalStmt_deinit_deref_eq_unsupported`, `evalTerminator_drop_unprojected_ub_iff` (`[adv A1]`) | Unprojected `Deinit`/`Drop` fault iff `loc` is out of bounds or `.dead` (`[.storageLiveProtected]`, succeeding on `.uninit` slots); projected `Deinit`/`Drop` run `readProjectedValue`, which has no `.deref` arm (`Places.lean:1666`: `.deref` returns `.unsupported` immediately). |
| `evalRvalue_cast_mutToConstPointer_ub_iff` (`[adv A1]`) | `CastKind.pointerCoercion "MutToConstPointer"` never faults beyond evaluating its operand (`censusCastKindFaultClasses = []`). |
| `evalTerminator_diverging_call_exposesUb_destination_irrelevant` (`[adv A1]`) | Diverging `TerminatorKind.call` (`target = none`) never writes to `destination` (nor in `resumeExternalDivergingCall`), so `StepNodeExposesUb` is invariant to `destination`. |
| `evalOperand_unprojected_copy_ub_iff`, `evalOperand_unprojected_move_ub_iff`, `evalOperand_ub_implies_mem_censusOperand` (`[adv A2]`) | Unprojected `Operand.copy` and `Operand.move` fault with `.ub` iff the local is out of bounds, `.uninit`, or `.dead` (`[.uninitRead]`), and any `.ub` of `evalOperand` implies `∃ cls ∈ censusOperandFaultClasses op`. |
| `writePlaceValue_unprojected_ub_iff` (`[adv A2]`) | Unprojected `writePlaceValue` faults with `.ub` iff the local is out of bounds or `.dead` (succeeding on both `.uninit` and `.init _`). |
| `evalStmt_intrinsic_assume_ub_iff` (`[adv A2]`) | `StatementKind.intrinsic (.assume op)` faults with `.ub` iff `evalOperand` returns `.ub` or `op` evaluates to a value other than `.scalar ⟨1, 1⟩` (`[.scalarNicheInvalid]`). |
| `evalTerminator_assert_cleanup_or_terminate_ub_iff` (`[adv A2]`) | When `unwind` is `.cleanup _` or `.terminate`, `TerminatorKind.assert` faults with `.ub` iff `evalOperand` on `cond` returns `.ub` or `cond` evaluates to a non-scalar value (`[.scalarNicheInvalid]`). |
| `witness*_site_live` (4 probes + `[adv B3]` `witnessCalleeStorage_masked_site_live`) + `witnessWrappingArith_census_precise` | `stepMirFn witness... (concrete state) = MirStepNode.fail .ub` by kernel evaluation at the exact site each mutant strips, plus non-faulting contrast states and `stepMirFn witnessWrappingArithBody (0, 4) = MirStepNode.unsupported` (`rfl`). |

---

## 3. Construct-to-Fault-Class Matrix (after `[adv A1]`)

`Place read` = `uninitRead :: projection classes`; projection classes: `.deref` → `ptrDerefInvalid, ptrAlignMismatch, treeBorrowsViolation`; `.index` → `boundsCheck, uninitRead`; `.constantIndex`/`.subslice` → `boundsCheck`; `.downcast` → `scalarNicheInvalid`; `.field`/`.opaqueCast`/`.unwrapUnsafeBinder` → `[]`.
`Projected value read` (`readProjectedValue` for `Deinit`/`Drop`, `[adv A1]`) = `.deref`/`.field`/`.opaqueCast`/`.unwrapUnsafeBinder` → `[]`; `.downcast` → `scalarNicheInvalid`; `.subslice` → `boundsCheck`; `.index`/`.constantIndex` → `boundsCheck, scalarNicheInvalid, uninitRead`.
`Place write` = `storageLiveProtected, treeBorrowsViolation` (plus `uninitRead` and projection classes when projected).

| Construct | Census classes | Justification in `Trusted.MirSemantics` |
| :--- | :--- | :--- |
| `.copy p` / `.move p` operand | place read | `evalOperand` reads the place. |
| `.constant c` | `[]`, or `boundsCheck, scalarNicheInvalid, uninitRead` for `.indirect` | `evalOperand_constant_non_indirect_ne_ub`; `.indirect` decodes global bytes. |
| `Use op` / `WrapUnsafeBinder op` | operand + `scalarNicheInvalid` for `copy`/`move` | `validateLoadedValue` rejects invalid `bool` scalars. |
| `BinaryOp op l r` | operands + `censusBinOpFaultClasses op` | `censusBinOpFaultClasses_exact`; `.offset` → `arithOverflow, boundsCheck, ptrDerefInvalid, treeBorrowsViolation`. |
| `UnaryOp .neg` / `.not` / `.ptrMetadata` | operand + `[]` / `scalarNicheInvalid` / `ptrDerefInvalid` | `.neg` wraps; `evalUnaryNot` faults on invalid `bool`; width mismatch for metadata. |
| `Cast .intToInt` / `.pointerExposeProvenance` / `.pointerWithExposedProvenance` / `.pointerCoercion "MutToConstPointer"` | operand only (`[]` for cast kind) | no `.ub` edge beyond the operand (`evalRvalue_cast_mutToConstPointer_ub_iff`, `[adv A1]`). |
| `Cast .floatToInt` / `.floatToFloat` / `.intToFloat` | `[]` | no `evalRvalue` arm (`rvalueUnevaluated = true`, `.unsupported`). |
| `Cast .transmute` / `.subtype` | operand + `scalarNicheInvalid, uninitRead` | `evalByteCast`. |
| `Cast .ptrToPtr` / `.pointerCoercion ("Unsize" \| "ArrayToPointer")` | operand + `boundsCheck, ptrDerefInvalid, ptrAlignMismatch, treeBorrowsViolation, scalarNicheInvalid` | `evalUnsizeCoercion` and `deriveStackElemThinPtr` check Tree Borrows tags (`.disabled`/`.frozen` → `.ub`), bounds, alignment, and pointer validity (`[adv A1]`). |
| `Cast .pointerCoercion ("ReifyFnPointer*" \| "ClosureFnPointer*" \| "UnsafeFnPointer")` / `.fnPtrToPtr` | operand + `ptrDerefInvalid, scalarNicheInvalid, callAbiMismatch` | `evalReifyFnPointer`, `evalUnsafeFnPointer`, and `evalFnPtrToPtr` check callee signature/ABI compatibility (`checkCalleeSig`, `CallConv.rustIntrinsic`, `Safety`) and never check alignment or bounds (`[adv A1]`). |
| `Ref`/`RawPtr p` | `[uninitRead]` unless `p` starts with `.deref`; else `uninitRead, ptrDerefInvalid, ptrAlignMismatch, treeBorrowsViolation` + projection classes | `evalRvalue_borrow_nonDeref_ub_iff`. |
| `Repeat op _` / `Aggregate (non-coroutine) ops` | operands only | no `.ub` beyond operand evaluation. |
| `Aggregate (.coroutine _) _` / `NullaryOp _` / `ThreadLocalRef _` / `ShallowInitBox _ _` | `[]` | no `evalRvalue` arm (`rvalueUnevaluated = true`, `.unsupported`, `[adv A1]`). |
| `Len p` / `Discriminant p` / `CopyForDeref p` | place read + `boundsCheck` / + `scalarNicheInvalid` / place read | `evalPlaceLen` / `evalPlaceDiscriminant` / plain read. |
| `.nop`, `.coverage`, `.constEvalCounter`, `.backwardIncompatibleDropHint` | `[]` | `evalStmt_pure_constructs_ne_ub`. |
| `.storageLive l` / `.storageDead l` | `storageLiveProtected` | `evalStmt_storageLive_ub_iff` / `evalStmt_storageDead_ub_iff`. |
| `.assign dst rv` | `[]` when `rvalueUnevaluated rv = true`; else place write(dst) + rvalue classes | `evalStmt` evaluates `evalRvalue` before inspecting `dst` (`evalStmt_assign_unevaluated_eq_unsupported`, `[adv A1]`). |
| `.retag _ p` | place read + `boundsCheck, ptrDerefInvalid, treeBorrowsViolation` | retag checks pointer shape, permissions, mutability, bounds — never alignment. |
| `.placeMention p` | `uninitRead` | `evalStmt_placeMention_ub_iff`: only checks root/index initialization (`[adv A1]`). |
| `.deinit p` | `storageLiveProtected` (unprojected) or `uninitRead` + projected value read | `evalStmt_deinit_unprojected_ub_iff`, `evalStmt_deinit_deref_eq_unsupported` (`[adv A1]`). |
| `.setDiscriminant p _` | `scalarNicheInvalid, uninitRead` (unprojected) or read + write + `scalarNicheInvalid` | non-aggregate / uninitialized / dead targets. |
| `.intrinsic (.assume op)` | operand + `scalarNicheInvalid` | violated assumption or non-scalar condition. |
| `.intrinsic (.copyNonOverlapping ..)` | operands + `arithOverflow, boundsCheck, ptrDerefInvalid, ptrAlignMismatch, treeBorrowsViolation, scalarNicheInvalid, uninitRead` | `evalCopyNonOverlapping`. |
| `.goto t` | `[]` in bounds, `boundsCheck` out of bounds | `evalTerminator_pure_constructs_ne_ub`, `stepMirFn_after_goto_oob_ub`. |
| `.unwindTerminate` / `.inlineAsm` | `[]` | abort / `.unsupported`. |
| `.unreachable` | `unreachableTerminator` | `evalTerminator_unreachable_ub`. |
| `.unwindResume` | `callAbiMismatch` | `unwindFromCallStack` faults through a `returnUnwind = .unreachable` caller. |
| `.return_` | `treeBorrowsViolation, uninitRead, callAbiMismatch` | `evalTerminator_return_root_ub_iff`, `evalTerminator_return_inline_ub_iff`. |
| `.switchInt d _` | operand + `scalarNicheInvalid` (+ `boundsCheck` if a target is out of bounds) | non-scalar discriminant. |
| `.drop p _ _` | `storageLiveProtected` (unprojected) or `uninitRead` + projected value read (+ `boundsCheck` if target OOB) | `evalTerminator_drop_unprojected_ub_iff` (`[adv A1]`). |
| `.assert c _ _ u` | operand + `scalarNicheInvalid` + (`unreachableTerminator` for `u = .unreachable`, `callAbiMismatch` for `.continue_`, nothing for `.cleanup`/`.terminate`) (+ `boundsCheck` if target OOB) | `applyUnwindAction`. |
| `.call f args dst (some t) u` | operands + place write(dst) + `callAbiMismatch` + callee classes (`censusCalleeDefPathFaultClasses`, or `ptrDerefInvalid` for indirect callees) + `unreachableTerminator` for `u = .unreachable` (+ `boundsCheck` if target OOB) | `resolveCallTarget`, argument evaluation, `checkCalleeTargetCompatible`, intrinsic dispatch, `resumeExternalCall`. |
| `.call f args dst none u` | operands + `callAbiMismatch` + (`unreachableTerminator` if `isUnreachableCallTarget` or `u = .unreachable`, `ptrDerefInvalid` if indirect) (+ `boundsCheck` if unwind target OOB) | diverging calls never write to `dst` and never dispatch `evalDirectRustIntrinsic?` (`evalTerminator_diverging_call_exposesUb_destination_irrelevant`, `[adv A1]`). |
| `.tailCall f args` | operands + `treeBorrowsViolation, uninitRead, storageLiveProtected, callAbiMismatch` (+ `ptrDerefInvalid` for indirect callees) | `evalTailCallTerminator` and `resumeExternalTailCall` destination write into `caller.destination` (`[adv A1]`). |

---

## 4. False-Proof Mutation Probe Results

| Probe | Emitter bug | Baseline | Mutant | Missing sites (Rust = Lean) | Lean liveness certificate |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `CallArgBlindProbe` | call arguments treated as opaque values (deref projections unchecked) | `VERIFIED` | `UNKNOWN(UNSUPPORTED_CONSTRUCT)` | `(0,0,ptr_deref_invalid)`, `(0,0,ptr_align_mismatch)` | `witnessCallArgBlind_call_site_live` (dangling `*_1` argument) |
| `SwitchBreakStripProbe` | `SwitchInt` exploration drops the `otherwise` edge (`bb2` never explored) | `VERIFIED` | `UNKNOWN(..)` | all `bb2` sites: `(2,0,{arith_overflow, div_rem_by_zero, tree_borrows_violation, uninit_read, storage_live_protected})`, `(2,1,{tree_borrows_violation, uninit_read, call_abi_mismatch})` | `witnessSwitchBreakStrip_div_site_live` (`_2 = 0` faults, `_2 = 2` steps) |
| `LoopUpdateOverflowProbe` | overflow obligations skipped in loop-latch blocks | `VERIFIED` | `UNKNOWN(..)` | `(2,0,arith_overflow)` for the latch `AddUnchecked` | `witnessLoopUpdateOverflow_latch_site_live` (`u32::MAX` faults, `7` steps; wrapping `Add` at `(2,1)` carries no `arith_overflow`) |
| `DerefAliasProbe` | deref/alignment/aliasing obligations skipped at dereferencing statements | `VERIFIED` | `UNKNOWN(..)` | `(0,0,ptr_deref_invalid)`, `(0,0,ptr_align_mismatch)`, `(0,0,tree_borrows_violation)` | `witnessDerefAlias_deref_site_live` (dangling `*_2`) |
| `PropertyRegistryUnemittedProbe` | `tree_borrows_violation` marked `UnemittedGap` while `discharged = census` | `VERIFIED` (full registry) | `UNKNOWN(..)` | `(0,0,tree_borrows_violation)`, `(0,1,tree_borrows_violation)`; `unemitted_classes = [TreeBorrowsViolation]` | `witnessDerefAlias_registry_unemitted_rejected` (`by decide`) |
| Callee coordinate mask (`[adv B3]`) | caller and inline-callee censuses appended and reconciled against the *caller's* obligations only | shared list: `VERIFIED` (unsound) | per-body batch: `UNKNOWN(..)` | every callee site: `(0,0,storage_live_protected)`, `(0,1,{tree_borrows_violation, uninit_read, call_abi_mismatch})` | `witnessCalleeMask_append_masks_batch_rejects` (`by decide`), `witnessCalleeStorage_masked_site_live` (the masked callee site faults when the callee is active) |

---

## 5. Adversarial Round History (`[adv A0]` → `[adv B1]` → `[adv A1]` → `[adv B2]` → `[adv A2]` → `[adv B3]` → `[adv A3]` → `[adv B4]`)

### `[adv B1]` findings against `[adv A0]` (fixed in `[adv B1]`)

1. **Class labels were never checked against the semantics.** `stepMirFn_fault_in_census` is existential in the class, so it only needs a non-empty census at the faulting PC; every `[adv A0]` "precision theorem" was an `rfl` restatement of the definition. Consequences found by reading `Trusted.MirSemantics`:
   - *Over-approximation*: wrapping/flagged/masked binops, comparisons and bitwise ops, `Neg`, `IntToInt`/exposed-provenance casts, `NullaryOp`, `ThreadLocalRef`, `ShallowInitBox`, `Repeat`/`Aggregate`, `CopyForDeref`, non-deref borrows, `Retag` alignment, and speculative `Assert` arithmetic labels emitted classes the evaluator can never trigger.
   - *Under-approximation (class level)*: `Use(copy p)` lacked `scalarNicheInvalid` (`validateLoadedValue`), and `BinOp.offset` lacked `treeBorrowsViolation` (disabled-tag check in `evalPtrOffsetBinOp`).
   - Fixed definitions plus the §2.1 certificates (`censusBinOpFaultClasses_exact`, `evalScalarBinOp_ub_cause`, exact edge theorems).
2. **External-call continuations were outside the completeness theorem.** `resumeExternalCall` / `resumeExternalDivergingCall` return `.faulted .ub` *inside* the `MirStepNode.extCall` continuation (destination write, `.unreachable` unwind, normal return of a diverging callee); `stepMirFn` never returns `.fail .ub` for these. Fixed with `StepNodeExposesUb` and the exposure theorems.
3. **`LoopUpdateOverflowProbe` stripped a semantically dead label.** The latch used wrapping `BinOp.add`, which `evalScalarBinOp` can never overflow-fault. The witness now uses `AddUnchecked`, keeps a wrapping accumulator as a precision contrast, and every probe has a liveness certificate.
4. **Probes were set-difference tautologies** (baseline = census) — replaced by the mock emitter (§4).
5. **Lean scanner fail-opens** (each has a regression test in `test_b1_lean_scanner_fail_open_regressions`):
   - constructor heads matched only on the last segment, so `Evil.goto 0` / bare `goto 0` (arbitrary user definitions) were read as `TerminatorKind.goto` — now `check_ctor_qualifier` requires `.ctor` or `Type.ctor` (optionally under a known `Trusted` MIR AST namespace);
   - anything applied to the `body` record (`{..} |> mutate`, `{..}.withBlocks evil`) was ignored — now rejected;
   - duplicate record fields silently overwrote earlier ones — now rejected;
   - unknown string escapes were mangled (`\u0061` became `u0061`), changing callee `DefPath`s such as `core::intrinsics::unreachable` — escapes now follow Lean exactly (`\\ \" \' \n \r \t \xHH \uHHHH`, string gaps, `\{` in interpolations) and fail closed otherwise;
   - only `s!`/`f!` were interpolation prefixes, so `m!"{"def body ..."}"` leaked a decoy definition into the token stream — every `<ident>!"` now lexes as an interpolated string, and comments inside interpolations fail closed;
   - `census_lean_mir_module` now enforces a strict emitter-module grammar (`import`/`namespace`/`section`/`end`/plain `open`/`set_option`/`def name : type := term` only, exactly one `def body : CapturedMir`, no declaration or namespace reusing a MIR AST type name), so syntax extensions (`notation`, `macro_rules`), attributes, `#eval`, instances, shadowing `def TerminatorKind.goto`, hidden `def body : (CapturedMir)` bodies, and brace-carrying strings or `!`-macros inside skipped definitions (where a Lean interpolation such as `throwError "{"..."}"` could desynchronize the token stream) fail closed; the lenient `census_lean_mir_def` keeps handling arbitrary surrounding Lean (comments, raw/interpolated strings, char literals, guillemets) for the witness file.
6. **Rust/Lean parity bugs**: `std::intrinsics::*` was classified as an intrinsic only in Rust; `RigidTy.fnDef`-typed constants with non-zero-sized values lost their callee path (now rejected).
7. **Witness bodies were ill-formed** (`localDecls := []` while mentioning locals `_0.._2`) — all witnesses now declare their locals.
8. **This report** previously cited nonexistent theorems (for example `validMirPc_iff`, `censusStmtFaultClasses_intrinsic_assume`, `censusStmtFaultClasses_not_all_twelve`) and a construct matrix/probe table that contradicted the code; it now reflects the implementation.


### `[adv A1]` critique & repair of `[adv B1]` (fixed in `[adv A1]`)

1. **Unevaluated `Rvalue` over-approximation in `StatementKind.assign` and `Rvalue.aggregate (.coroutine _)`**:
   - In `Trusted.MirSemantics.evalRvalue` (`Places.lean:8243-8855`), five `Rvalue` forms have no evaluation arm and return `.unsupported` immediately without reading any operand: `.threadLocalRef _`, `.nullaryOp _ _`, `.shallowInitBox _ _`, `.cast kind _ _` with `castKindUnevaluated kind = true`, and `.aggregate (.coroutine _) _`.
   - Because `evalStmt` on `StatementKind.assign dst rv` (`Statements.lean:2651-2820`) evaluates `evalRvalue` *before* inspecting `dst` and maps `.unsupported` directly to `MirStepNode.unsupported`, any `StatementKind.assign dst rv` with `rvalueUnevaluated rv = true` steps unconditionally to `MirStepNode.unsupported` and can never fault with `.ub` — even if `dst` is `*_1` or `.dead`.
   - `[adv B1]` missed `.coroutine` in `censusRvalueFaultClasses`, dropped `AggregateKind` in Rust's `ProtoRvalue::Aggregate`, and emitted `censusPlaceWriteFaultClasses dst` on every unevaluated assignment (including statement `(0, 4)` `_1 = NullaryOp.sizeOf u32` in `witnessWrappingArithBody`).
   - *Fix*: Added `aggregateKindUnevaluated`, `rvalueUnevaluated`, `ProtoAggregateKind`, `evalRvalue_eq_unsupported_of_rvalueUnevaluated`, and `evalStmt_assign_unevaluated_eq_unsupported`, and updated `witnessWrappingArithExpectedCensus` and `witnessWrappingArith_census_precise`.
2. **Over-approximation on `StatementKind.placeMention`, `StatementKind.deinit`, and `TerminatorKind.drop`**:
   - `evalStmt (.placeMention place)` (`Statements.lean:2424-2431`) only checks `get? s.frame.locals place.local_` and `placeMentionOperandsInit`; it never dereferences pointers or checks alignment, Tree Borrows, bounds, or downcasts, so its sole fault class is `[.uninitRead]`.
   - Unprojected `evalStmt (.deinit place)` (`Statements.lean:2577-2594`) and `evalTerminator (.drop place target unwind)` (`Terminators.lean:3041-3066`) only fault if `place.local_` is out of bounds or `.dead` (`[.storageLiveProtected]`, succeeding on `.uninit` slots). Projected `deinit`/`drop` call `readProjectedValue`, which has no `.deref` arm (`Places.lean:1666`: `.deref` returns `.unsupported` immediately).
   - *Fix*: Added `censusReadProjectedFaultClasses`, `evalStmt_placeMention_ub_iff`, `evalStmt_deinit_unprojected_ub_iff`, `evalStmt_deinit_deref_eq_unsupported`, and `evalTerminator_drop_unprojected_ub_iff`.
3. **`CastKind` under-approximations and over-approximations**:
   - `[adv B1]` omitted `.treeBorrowsViolation` from `.ptrToPtr` and `.pointerCoercion ("Unsize" | "ArrayToPointer")`, even though `evalUnsizeCoercion` (`Places.lean:6184-6189`) and `deriveStackElemThinPtr` (`Places.lean:6421-6422`) fault with `.ub` on `.disabled`/`.frozen` Tree Borrows tags.
   - `[adv B1]` omitted `.callAbiMismatch` from `.pointerCoercion` (`ReifyFnPointer*`, `ClosureFnPointer*`, `UnsafeFnPointer`) and `.fnPtrToPtr` (`checkCalleeSig`, `CallConv.rustIntrinsic`, `Safety`), and emitted spurious `.boundsCheck`/`.ptrAlignMismatch` on them, while emitting 4 spurious classes on `.pointerCoercion "MutToConstPointer"` (`[]`).
   - *Fix*: Refined `censusCastKindFaultClasses` / `census_cast_kind_fault_classes` and proved `evalRvalue_cast_mutToConstPointer_ub_iff`.
4. **`TerminatorKind.call` (`target = none`), `TerminatorKind.tailCall`, and `censusCalleeDefPathFaultClasses` bugs**:
   - Diverging calls (`target = none`, `Terminators.lean:3172-3246`) never write to `destination` and only dispatch `isUnreachableCallTarget` (never `evalDirectRustIntrinsic?` or `isDirectExactDivTarget`), yet `[adv B1]` emitted `censusPlaceWriteFaultClasses destination` and non-unreachable intrinsic classes on `target = none`.
   - `TerminatorKind.tailCall` (`Terminators.lean:767-800`): `resumeExternalTailCall` writes the returned value to `caller.destination` via `writePlaceValue` when `callStack` is non-empty, which can fault with `.treeBorrowsViolation`, `.uninitRead`, or `.storageLiveProtected` inside `StepNodeExposesUb`, yet `[adv B1]` only emitted `[.callAbiMismatch]`.
   - `censusCalleeDefPathFaultClasses`: `[adv B1]` kept `defPath == "std::intrinsics::exact_div"` (contradicting `isDirectExactDivTarget` in `Terminators.lean:819`), emitted `[.arithOverflow, .boundsCheck]` for `core::intrinsics::arith_offset` even though `evalArithOffset` (`Scalars.lean:2045-2072`) wraps modularly (`[.ptrDerefInvalid, .scalarNicheInvalid]`), and omitted `.arithOverflow`, `.divRemByZero`, `.shiftOverflow`, `.ptrDerefInvalid`, `.unreachableTerminator` from `core::intrinsics::const_eval_select`.
   - *Fix*: Updated `censusCalleeDefPathFaultClasses` and `censusTerminatorFaultClasses` in both Lean and Rust, and proved `evalTerminator_diverging_call_exposesUb_destination_irrelevant`.
5. **Interprocedural `ValidMirPc` preservation**:
   - Added `validMirPc_pushCalleeFrame`, `validMirPc_pushDivergingCalleeFrame`, `validMirPc_enterTailCalleeFrame`, and `validMirPc_return_inline`.
6. **Lean lexer & strict scanner fail-opens in `crates/cargo-anneal/src/fault_census_proto.rs`** (all covered by `test_a1_semantic_precision_and_scanner_regressions`):
   - *Character literals `'...'` lexed as `LeanToken::StrLit("")` and broken `'\''` escape*: `tokenize_lean_source` previously pushed `LeanToken::StrLit(String::new())` for char literals (letting `parse_string()` accept `'a'` as `""`), and for `'\''` stopped at the escaped quote at `i + 2`, leaving a stray `'` in the token stream. Now lexed via `lex_char_literal` into `LeanToken::CharLit(char)`.
   - *`lex_interpolated_string` desync via `'\"'`, `'}'`, `r#"..."#`, nested `<ident>!"..."`, and `«}»`*: Inside `{ ... }` of an interpolated string, `[adv B1]` only handled `"`, `{`, and `}`, allowing `s!"{if c == '"' || c == '}' then ...}"` to desynchronize `census_lean_mir_def`. `lex_interpolated_string` now handles character literals, guillemets, raw strings, and nested `<ident>!"..."` interpolations inside `{ ... }`.
   - *`parse_rvalue` skipped `AggregateKind` with `skip_balanced_expr()`*: Now parsed and validated via `parse_aggregate_kind` + `check_ctor_qualifier`.
   - *`check_strict_mir_module_grammar` accepted arbitrary `import EvilMod`, `open EvilNs`, and `def Sub.body : CapturedMir`*: Now restricts `import` and `open` to `Trusted` namespaces and requires `def body` to be declared with bare name `body`.
   - *Missing required record fields defaulted silently*: `parse_captured_mir`, `parse_basic_block`, `parse_statement`, `parse_terminator`, and `parse_const_scalar` now require all mandatory fields (`defPath`, `phase`, `role`, `argCount`, `localDecls`, `basicBlocks`, `fnAbi`, `layouts`, `allocations`, `isCleanup`, `span`, `bits`, `sizeBytes`, `allocId`, `offsetBytes`) and validate `MirPhaseTag` and `ContractRole` constructors.


### `[adv B2]` critique & repair of `[adv A1]` (lexer/parser traps, differential parity, corpus)

1. **Randomized real-emitter differential fuzz** (`test_b2_randomized_emitter_differential_parity`): 400 deterministic random `IrCapturedMir` bodies covering every IR statement, terminator, rvalue, operand, constant, projection, cast, aggregate and unwind kind plus the classified callee paths, with lexer-trap strings (quotes, backslashes, `\u0061`, braces, `--`, `/-`, `-/`, guillemets, tabs and newlines, a decoy `def body`, `s!`/`m!` interpolations, raw strings, char literals, Unicode, control characters) in spans, paths, debug names, inline-asm templates and `--` comments. Each body is rendered by the real `anneal_rustc_capture::lean_emit::emit_mir_lean_module`; `parse_lean_captured_mir_def` must equal `ProtoMirBody::from_ir_captured_mir` *structurally* (decoded strings included) and `census_lean_mir_module` must equal `census_ir_captured_mir`. The corpus must exercise all 12 classes. Result: `0` divergences.
2. **Cross-language census differential** (`dump_lean_census_differential_corpus`, `#[ignore]`, run with `FAULT_CENSUS_DIFF_DIR=<dir>`): writes one self-checking Lean file containing the prototype, 400 emitted modules, and one `#guard` per module asserting that the Lean `censusMirBodyFaultSites` renders identically to the Rust census of the same IR body. `(cd examples && anneal-lean-run --mode file --concurrency 1 -- lake env lean <dir>/LeanCensusDifferential.lean)` exits `0` (`4990` sites, all 12 classes, about `55 s`); corrupting a single expectation makes it fail.
3. **Emitter robustness findings** (in trusted code, recorded for Track A; the scanner already fails closed or decodes exactly like Lean):
   - `render_mir_module_header` interpolates `def_path` unescaped into a `/-! ... -/` doc comment, so a path containing `-/` closes the comment early.
   - `summarize_basic_block` sanitizes user comments but not generated summaries, so a newline in a `Downcast` variant name (or a thread-local path) escapes the `-- bbN:` line comment.
   - `escape_lean_str` writes multi-byte control characters as one `\xHH` per UTF-8 byte (`U+0085` becomes `\xc2\x85`), which Lean decodes as two code points. The scanner deliberately mirrors Lean, pinned by `test_b2_emitter_escape_and_comment_injection_findings`.
   None of these can arise from `rustc` identifiers or paths.
4. **Dialect pinning**: `[adv A1]` accepted any `open Trusted.*` (and bare `open MirAst`), and `MIR_AST_NAMESPACES` accepted `Trusted.Rustc.V2026_08_01.MirAst.*` constructors. Both have a different type and different semantics from the `V2026_06_01` dialect the census is proved over. Strict modules may now only `open` the emitter's namespaces (`STRICT_MODULE_OPENS`), and constructor qualifiers are pinned to `V2026_06_01`.
5. **Brief §3 Part B.4 compliance**: the witness bodies are now also re-hosted verbatim as the `body` of canonical strict modules and scanned with `census_lean_mir_module` itself. Previously only the lenient `census_lean_mir_def` parsed them.
6. **Truncation** (`test_b2_truncated_real_modules_fail_closed`): every prefix of both real `rustc`-captured tutor modules fails closed until the complete `def body` record is present, and from then on yields exactly the full census.
7. **Report history**: restored the `[adv B1]` findings, semantic subtleties, and known limitations that the `[adv A1]` rewrite dropped.

### `[adv A2]` critique & repair of `[adv B2]` (scope-stack grammar, `ConstOperand`/`Ty` field validation, fuzzer coverage, multi-step trace & multi-item reconciliation)

1. **Unclosed/mismatched `namespace` & nested `namespace Sub def body` fail-open in `check_strict_mir_module_grammar` (`fault_census_proto.rs`)**:
   - In `[adv B2]`, `check_strict_mir_module_grammar` did not maintain a scope stack for `namespace` / `section` / `end`. As a consequence:
     - A truncated `Mir/<Item>.lean` module cut off after `def body : CapturedMir := { ... }` (dropping `def defaultClaim` and `end Mir.FrameTutor.<item>`) was accepted as `Ok(sites)`; in fact, `[adv B2]`'s `test_b2_truncated_real_modules_fail_closed` had to weaken its assertion to `assert!(cut >= body_end)` instead of requiring the full module because prefixes truncated before `end <ModName>` were accepted.
     - A nested `namespace Sub def body : CapturedMir := ... end Sub` inside `namespace Mir.Probe.item` defines `Mir.Probe.item.Sub.body` (not `Mir.Probe.item.body`), yet bypassed the `name == "body"` check because scope nesting depth was not tracked.
     - Mismatched `namespace A ... end B` or stray `end Foo` commands were silently accepted.
   - *Fix*: `check_strict_mir_module_grammar` now maintains an explicit `scope_stack` of open `("namespace" | "section", name)` scopes, requires every `end <name>` to match and pop the top of `scope_stack`, requires `scope_stack.is_empty()` at EOF, and requires `def body : CapturedMir` to appear at `scope_stack.len() == 1 && scope_stack[0].0 == "namespace"`. `test_b2_truncated_real_modules_fail_closed` is tightened so that **every** proper prefix (`cut < module.trim_end().len()`) of both real `rustc`-captured modules fails closed (`accepted == 1`).
2. **`ConstOperand` and `Ty` missing-field fail-opens (`parse_const_operand`, `parse_ty_extract_fn_def`, `parse_captured_mir`)**:
   - In `[adv B2]`, `parse_const_operand` allowed `Operand.constant { val := ConstValue.zeroSized }` (omitting `ty`), and `parse_ty_extract_fn_def` allowed `{ layoutIdx := 0 }` (omitting `kind`) or `{ kind := RigidTy.fnDef "core::intrinsics::unreachable" [] }` (omitting `layoutIdx`), silently defaulting `fn_def_path` to `None` and dropping `UnreachableTerminator` or direct-intrinsic fault classes.
   - Additionally, `parse_captured_mir` and `parse_rigid_ty_extract_fn_def` skipped `localDecls`, `allocations`, `genericParams`, `traitImpls`, and `RigidTy.fnDef` `typeArgs` with `skip_balanced_expr()` instead of `parse_list`, accepting non-inline helper identifiers (`localDecls := externalDecls`).
   - *Fix*: `parse_const_operand` now requires both `ty` and `val`; `parse_ty_extract_fn_def` requires both `kind` and `layoutIdx`; and `localDecls`, `allocations`, `genericParams`, `traitImpls`, and `RigidTy.fnDef` `typeArgs` require inline list syntax via `parse_list`.
3. **`fuzz_captured_mir` statement/retag/aggregate omissions (`fault_census_proto.rs`)**:
   - Despite claiming coverage of every IR statement, `fuzz_captured_mir` in `[adv B2]` omitted `IrStatementKind::ConstEvalCounter` (only generating 11 of 12 `IrStatementKind` variants), hard-coded `IrRetagKind::FnEntry` (omitting `TwoPhase`, `Raw`, `Default`), and hard-coded `IrMutability::Not` in `IrAggregateKind::RawPtr`.
   - *Fix*: `fuzz_captured_mir` and `fuzz_rvalue` now generate `IrStatementKind::ConstEvalCounter`, all 4 `IrRetagKind` variants, and both `IrMutability::Not` and `IrMutability::Mut` in `IrAggregateKind::RawPtr`, verified by `test_a2_scope_stack_const_ty_multi_item_and_fuzz_completeness`.
4. **Operand/place/assume/assert semantic precision, multi-step `MirStepsIntra` trace safety, and multi-item reconciliation (`FaultSiteCensusPrototype.lean` & `fault_census_proto.rs`)**:
   - Added `evalOperand_unprojected_copy_ub_iff`, `evalOperand_unprojected_move_ub_iff`, `evalOperand_ub_implies_mem_censusOperand`, `writePlaceValue_unprojected_ub_iff`, `evalStmt_intrinsic_assume_ub_iff`, and `evalTerminator_assert_cleanup_or_terminate_ub_iff` in Section 5.
   - Added multi-step intra-frame execution relation `MirStepsIntra`, `mirStepsIntra_preserves_validMirPc`, and `initMachineState_mirStepsIntra_exposesUb_in_census` in Section 8, plus `reconcileFaultCoverageWithRegistry_partial_site_rejected`, `reconcileFaultCoverageWithRegistry_append_verified_iff`, `reconcileFaultCoverageWithRegistry_mono`, `initMachineState_mirStepsIntra_reconciled_safety`, and `initMachineState_mirStepsIntra_not_exposesUb_of_empty_census` in Section 9.
   - Added `ItemCoverageInput`, `MultiItemCoverageVerdict`, and `reconcile_multi_item_coverage` in Rust so multi-item / multi-callee batches enforce per-item coordinate isolation (preventing a discharged `(bb, stmt)` in a caller from masking an unmapped `(bb, stmt)` in a callee).

### `[adv B3]` critique & repair of `[adv A2]` (multi-body reconciliation, callee closure, `Classical.choice`)

1. **Shared-list multi-body composition is unsound.** The `[adv A2]` docstring of `reconcileFaultCoverageWithRegistry_append_verified_iff` presented "a caller body combined with an inline callee" as its use case. The lemma itself is true, but `FaultSite` coordinates are body-relative, so reconciling `callerCensus ++ calleeCensus` against the caller's obligations lets caller obligations discharge colliding callee sites.
   - Counterexample (`witnessCalleeMask_append_masks_batch_rejects`, `by decide`): the callee `witnessCalleeStorageBody` (`StorageLive _1; return`) has 4 census sites, and every one of them also occurs in `witnessDerefAliasBody`. The appended census reconciles `.verified` against the caller's list with zero callee obligations.
   - `witnessCalleeStorage_masked_site_live` (`rfl`) shows that the masked site really faults once the callee is the active body of the caller's machine.
   - *Fix*: §9b `CoverageBatch` / `reconcileCoverageBatch` (each body against its own list), `reconcileCoverageBatch_iff`, `reconcileCoverageBatch_mono`, and the interprocedural `stepMirFn_exposesUb_in_batch_discharged`, built on `stepMirFn_activeBody_exposesUb_in_census`. The append lemma's docstring now restricts it to censuses of the same body.
2. **`reconcile_multi_item_coverage` trusted its inputs** (`fault_census_proto.rs`):
   - Items carried a caller-supplied `census`, so `census: vec![]` reconciled `Verified` for any body.
   - Item labels were never compared with the body.
   - There was no closure check: a subject verified alone even when inline callee bodies, which can become `activeCallee`, were never reconciled.
   - The verdict docstring promised "every item non-empty", which was not enforced. That is fine, because an empty census is legitimate.
   - *Fix*: `ItemCoverageInput` now carries `body: ProtoMirBody`, and the reconciler recomputes `census_mir_fault_sites` itself. `ItemCoverageInput::from_lean_module` admits captured modules only through the strict grammar and labels them with the parsed `defPath`.
   - `CalleeClosure { inline_callees, external_callees }` adds three requirements: every inline callee needs a batch item; no callee may be both inline and external; and every direct `Call`/`TailCall` callee must be a batch item, a declared external callee, or a natively modeled intrinsic.
   - Covered by `test_b3_multi_item_batch_coordinate_isolation_and_callee_closure`. It parses the Lean witnesses, mirrors the Lean counterexample, and checks strict-module parity for the new witness.
3. **`Classical.choice` minimization.** The only source was `simp [h]` proving `(s.frame.stmtIdx == length bb.statements) = true` for `Nat` in `stepMirFn_activeBody_exposesUb_in_census` and twice in `stepMirFn_preserves_validMirPc`. Every downstream `stepMirFn_*`, reconciled-safety, and witness theorem inherited it. These steps are now `rw [hEqIdx]; exact decide_eq_true rfl`. Result: all `169` theorems (`144` public and `25` private) depend only on `propext` and `Quot.sound`, up from `147/163`.
4. **Open items handed to later rounds:**
   - `MirStepsIntra` follows only `.step`/`.emitStep`, so every multi-step trace theorem stops at the first call. External calls are `.vis` nodes whose answers carry an arbitrary `memAfter`. Inline calls change `activeCallee`/`callStack`.
   - `lookupCallee` installs generic callees as `calleeBody.instantiate subst`, so a batch over captured generic bodies does not literally contain the active body. Census invariance under `CapturedMir.instantiate` is unproved.

### `[adv A3]` critique & repair of `[adv B3]` (terminator-sensitive intrinsic & callee closure, `CapturedMir.instantiate` invariance, `MirStepsWithExtCalls`, dialect pinning)

1. **`reconcile_multi_item_coverage` rejected all 12 zero-fault native `RustIntrinsicKind` intrinsics and diverging panic hooks while accepting unmodeled `TailCall` / diverging-`Call` intrinsics (`fault_census_proto.rs`)**:
   - In `[adv B3]`, `reconcile_multi_item_coverage` tested whether a direct callee is natively modeled via `!census_callee_def_path_fault_classes(&callee).is_empty()` across all `Call` and `TailCall` terminators indiscriminately:
     - *False rejection*: In `Trusted.MirSemantics.evalTerminator` (`Terminators.lean:835-974, 2445-2542`), **12** of the 25 `RustIntrinsicKind` compiler intrinsics (`ub_checks`, `ctlz`, `cttz`, `ctpop`, `bswap`, `bitreverse`, `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `saturating_add`, `saturating_sub`, `three_way_compare`) on converging `Call` (`target = Some(_)`) and all **37** aborting/unwinding panic hooks (`isAbortingPanicDefPath`, `isUnwindingPanicDefPath`) on diverging `Call` (`target = None`) are evaluated inline without ever faulting with `.ub` or emitting `MirStepNode.extCall`. Because `census_callee_def_path_fault_classes` returns `[]` for them, `[adv B3]` falsely rejected any item calling `core::intrinsics::wrapping_add`, `core::intrinsics::ctpop`, `core::panicking::panic_fmt`, etc.
     - *False acceptance (fail-open)*: Conversely, `evalTailCallTerminator` (`Terminators.lean:2996-3039`) never dispatches native intrinsics at all (every non-inline `TailCall` emits `MirStepNode.extCall`), and diverging `Call` (`target = None`, `Terminators.lean:3218-3246`) never dispatches `isDirectExactDivTarget` or `evalDirectRustIntrinsic?` (so a diverging call to `core::intrinsics::unchecked_add` emits `MirStepNode.extCall`), yet `[adv B3]` accepted both with `CalleeClosure::default()`.
   - *Fix*: Added `is_natively_modeled_converging_call_callee` and `is_natively_modeled_diverging_call_callee`, dispatched per terminator kind in `reconcile_multi_item_coverage` (plus runtime-target closure on `arg[2]` of `core::intrinsics::const_eval_select`).
2. **`reconcile_multi_item_coverage` allowed direct calls to `seen_paths` items not in `closure.inline_callees` and ignored `ReifyFnPointer` targets (`fault_census_proto.rs`)**:
   - In `[adv B3]`, `reconcile_multi_item_coverage` checked `seen_paths.contains(callee.as_str())` instead of `inline_set.contains(callee.as_str())`. A recursive self-call in the subject item (or a call to a second batch item omitted from `closure.inline_callees`) reconciled as `Verified` even when `closure.inline_callees` was empty (`[]`), where `lookupCallee` at runtime returns `.none` and issues an unverified `MirStepNode.extCall`.
   - Furthermore, `direct_callee_def_paths` ignored `RigidTy.fnDef` function items reified into function pointers via `CastKind::PointerCoercion("ReifyFnPointer")` (`evalReifyFnPointer` registers them in `s.memory.fnPtrs` for indirect calls).
   - *Fix*: Direct calls now require `inline_set.contains(callee)` (or `external` / native), duplicate entries in `inline_callees` / `external_callees` are rejected, and all `reified_fn_def_paths(&item.body)` must be classified in `inline_set` or `external`.
3. **Strict-module dialect-pinning gaps (`fault_census_proto.rs`)**:
   - `import` in `check_strict_mir_module_grammar` accepted any `imp.starts_with("Trusted.")` (allowing `import Trusted.Evil` and `import Trusted.Rustc.V2026_08_01.MirAst`), `: CapturedMir` type ascriptions accepted `ty.ends_with(".CapturedMir")` (allowing `Evil.CapturedMir` and `Trusted.Rustc.V2026_08_01.MirAst.CapturedMir`), and multiple sequential top-level `namespace` blocks were accepted.
   - *Fix*: Added `STRICT_MODULE_IMPORTS`, `is_valid_captured_mir_type`, top-level delimiter tracking in `parse_lean_captured_mir_def`, and single top-level `namespace` enforcement.
4. **Empty `CoverageBatch` fail-open, generic `CapturedMir.instantiate` invariance, and multi-step `MirStepsWithExtCalls` safety (`FaultSiteCensusPrototype.lean`)**:
   - In `[adv B3]`, `reconcileCoverageBatch registry []` returned `true` on the empty batch `[]`; it now requires `!batch.isEmpty` (`reconcileCoverageBatch_nil : reconcileCoverageBatch registry [] = false`).
   - Resolved `[adv B3]` Open Item #2 by proving `censusStmtFaultClasses_instantiate`, `censusTerminatorFaultClasses_instantiate`, `censusMirBodyFaultSites_instantiate`, `cfgTargetsInBounds_instantiate`, `validMirPc_instantiate_iff`, and `stepMirFn_exposesUb_in_batch_discharged_instantiated`.
   - Resolved `[adv B3]` Open Item #1 by proving `validMirPc_applyUnwindAction_top`, `validMirPc_resumeExternalCall`, `validMirPc_resumeExternalDivergingCall`, `resumeExternalTailCall_top_ne_running`, `validMirPc_unwindFromCallStack`, `validMirPc_resumeExternalTailCall`, `mirStepsWithExtCalls_preserves_validMirPc`, `initMachineState_mirStepsWithExtCalls_exposesUb_in_census`, and `initMachineState_mirStepsWithExtCalls_reconciled_safety` — all 100% `Classical.choice`-free (`208/208` theorems).

### `[adv B4]` final audit of `[adv A3]` (semantic trace bridge, trusted-list pinning, hygiene, performance)

1. **`MirStepsWithExtCalls` was not connected to `stepMirFn`.**
   - Its external-call constructors accept any call terminator of `body` together with any application of `resumeExternalCall` / `resumeExternalDivergingCall` to arbitrary `localsAfterArgs`. They do not require that `stepMirFn` actually emitted that continuation, nor that the PC sits at the terminator.
   - Its theorems are true of the relation, but nothing showed that real executions stay inside it. Separately, `TermStepPreservesPc` and `StmtStepPreservesPc` mapped every external-call node to `True`, so no existing lemma constrained real continuations.
   - *Fix*:
     - `TermStepPreservesPc` now constrains external-call nodes. Under a top-level answer, a running continuation resumes at `stmtIdx = 0` of a block in the terminator's targets, still at the top-level frame.
     - `StmtStepPreservesPc` now forbids external calls from statements.
     - The existing `evalTerminator_preservesPc` / `evalDirectRustIntrinsic?_preservesPc` proofs were re-checked against the stronger predicates. Only the 7 external-call leaves needed new arguments: `resumeExternalCall_preservesPc`, `resumeExternalDivergingCall_preservesPc`, `resumeExternalTailCall_preservesPc`, and `applyUnwindAction_top_running`. Every `evalStmt` proof went through unchanged, which confirms that statements never call.
     - On top of these: the bridge theorem `stepMirFn_extCall_cont_preserves_validMirPc`, the semantic relation `MirStepsTop` (with `mirStepsTop_of_mirStepsIntra`), `mirStepsTop_preserves_validMirPc`, `initMachineState_mirStepsTop_exposesUb_in_census`, and `initMachineState_mirStepsTop_reconciled_safety`.
     - `witnessExtCall_mirStepsTop_nonvacuous` evaluates a real external call of `witnessExtCallBody` and its top-level `.returned` continuation (`rfl`).
2. **The native-callee lists from `[adv A3]` were hand-copied from the trusted semantics.** A stale entry would let `reconcile_multi_item_coverage` classify an external call as native, which fails open. *Fix*: the lists are now `NATIVE_CONVERGING_CALL_CALLEES` (25) and `NATIVE_DIVERGING_CALL_CALLEES` (39). `test_b4_native_callee_lists_match_trusted_semantics` reads `trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean` with `include_str!` and requires exact set equality with the `stringEq` literals of `classifyRustIntrinsic?` (minus `const_eval_select`) plus `isDirectExactDivTarget`, and of `isUnreachableCallTarget`, `isAbortingPanicDefPath`, and `isUnwindingPanicDefPath`. The `[adv A3]` lists matched exactly.
3. **Report accuracy**: the `[adv A3]` semantic-subtleties entry stated generic-callee census invariance without its `bodyHasNoParamCallConst` hypothesis. This is now corrected.
4. **Audits**:
   - Hygiene: zero internal hostnames, paths, LDAPs, links, or model names in the four files and in every commit message since the base commit. `lib.rs` differs from the base by exactly the `pub mod fault_census_proto;` line.
   - Performance: the Lean file elaborates in about `14 s`. The profiler's hottest single tactic takes `1.4 s`, so no tuning was needed.

### Semantic subtleties (carried from `[adv A0]`, verified in `[adv B1]`–`[adv B4]`)

- `ValidMirPc` is required because an out-of-bounds PC faults without any syntactic site; `stepMirFn_preserves_validMirPc`, `mirStepsIntra_preserves_validMirPc`, `mirStepsWithExtCalls_preserves_validMirPc`, and (`[adv B4]`, over real `stepMirFn` transitions) `mirStepsTop_preserves_validMirPc` keep it invariant for top-level frames with in-bounds CFG targets across intra-frame steps and external-call continuations.
- External-call answers replace the whole `Memory`, so trace theorems assume `MirCallAnsTopFrame ans` (the answer keeps `activeCallee = none` and `callStack = []`); `resumeExternalTailCall` at the top level never resumes the frame.
- `.return_` reads `_0` and, in an inline frame, writes into the *caller's* `destination`, so its classes are attributed to the callee's return site.
- The `.ub` of an out-of-bounds `Goto` happens on the *next* step.
- `stepMirFn body s` executes `s.memory.activeCallee.getD body`, and an inline callee fault is located at the *callee's* body-relative coordinates. Obligation lists therefore cannot be shared across bodies (`[adv B3]`, §9b), and generic inline callees installed as `calleeBody.instantiate subst` preserve their uninstantiated census whenever `bodyHasNoParamCallConst calleeBody = true` (`censusMirBodyFaultSites_instantiate`, `[adv A3]`).

### Known limitations (final, `[adv B4]`)

- Completeness remains existential in the class for constructs outside §2.1 (such as projected deref reads/writes, `copyNonOverlapping`, and complex calls).
- The strict module grammar targets `anneal-rustc-capture` output. It enforces balanced `namespace`/`section`/`end` scopes and rejects anything outside the emitter's command set, `open`s, and constructor namespaces, but it does not model Lean elaboration in general.
- The cross-language differential is a `#guard`-checked experiment over compiled evaluation (not kernel `decide`); kernel-checked parity is limited to the witness bodies.
- Multi-step trace theorems (`MirStepsTop`) cover top-level frames. Inline callee frames are covered one step at a time (`stepMirFn_exposesUb_in_batch_discharged`), but there is no multi-step relation through `pushCalleeFrame` / inline `return_` yet. The per-transition PC lemmas for it exist (`validMirPc_pushCalleeFrame`, `validMirPc_return_inline`).
- `MirCallAnsTopFrame` is an assumption about external-call answers, not something checked.
- The Rust batch API cannot see types, so it cannot check `bodyHasNoParamCallConst` for generic inline callees. The integration must check it on the Lean side or supply instantiated bodies.

---

## 6. Verification Receipts (`[adv B4]`)

All commands run from the repository root with `W = 1`.

1. **Primary command**, exit `0`:
   ```bash
   cargo test --manifest-path crates/cargo-anneal/Cargo.toml --lib fault_census_proto && \
   cargo test --manifest-path crates/cargo-anneal/Cargo.toml fault_census_proto && \
   (cd examples && anneal-lean-run --mode file --concurrency 1 -- lake env lean ../theory/Anneal/FaultSiteCensusPrototype.lean)
   ```
   `20 passed, 0 failed, 1 ignored` (the manual Lean differential harness) on both test targets, `0` Rust warnings, and Lean `0` errors / `0` warnings. Wall clock about `31 s` with warm caches. The Lean file alone takes about `14 s`.
2. **Kernel axiom audit**: a scratch copy with `#print axioms` over all `309` `def`/`abbrev`/`theorem` declarations (`218` theorems, `42` of the declarations `private`), run via `anneal-lean-run --mode file --concurrency 1` outside the worktree. Result: `0` `sorryAx`, `0` `Lean.ofReduceBool`, and **`218/218` theorems `Classical.choice`-free** (depending only on `propext` and `Quot.sound`).
3. **Proof health**: `python3 tools/anneal-lsp/server/proof_health.py theory/Anneal/FaultSiteCensusPrototype.lean` exits `0` with `0` findings. `rustfmt --edition 2021 --check crates/cargo-anneal/src/fault_census_proto.rs` is clean.
4. **Cross-language differential** (`[adv B2]`, optional): `FAULT_CENSUS_DIFF_DIR=<dir> cargo test --manifest-path crates/cargo-anneal/Cargo.toml --lib dump_lean_census_differential_corpus -- --ignored`, then `(cd examples && anneal-lean-run --mode file --concurrency 1 -- lake env lean <dir>/LeanCensusDifferential.lean)`. Exit `0`: `400` `#guard`s, all 12 classes. Re-run in `[adv B4]`: exit `0`, about `71 s` including generation.
5. **Hygiene**: `git status --porcelain` is empty after commit; no commit message since the base commit contains an internal identifier; and `git diff --name-only a5e12e5fac628cc71522b67a1b427e17e2927818..HEAD` ⊆ {`PROTOTYPE_REPORT.md`, `crates/cargo-anneal/src/fault_census_proto.rs`, `crates/cargo-anneal/src/lib.rs`, `theory/Anneal/FaultSiteCensusPrototype.lean`}. There are zero internal hostnames, user paths, LDAPs, CL numbers, or internal model names.

---

## 7. Integration Architecture for Track A (`ws-fault-site-coverage-reconciler`)

1. **Promote the Lean module** to `theory/Anneal/FaultSiteCensus.lean`, importing it from `theory/Anneal.lean` in a coordinated Track A change that also updates the trusted-boundary checker's pinned import list.
2. **Tag obligations with fault sites**: every obligation emitted by `crates/cargo-anneal/src/obligations.rs` should carry the `FaultSite`s it discharges.
3. **Reconcile at verification time**: run `census_ir_captured_mir` on the captured MIR and `census_lean_mir_module` on the generated `Mir/<Item>.lean`, require both censuses to agree, and reconcile against the discharged sites with a stage-aware registry (`PropertyRegistry::realistic_safe_subset_registry()` as the starting point).
   - `[adv B3]` *Coordinate alignment*: obligation sites must be tagged over the **same** body the census runs on. The emitter strips `Retag` statements (`census_ir_captured_mir` uses `strip_retags = true`), so tagging obligations with original `rustc` statement indices shifts every later statement. An obligation for one statement could then discharge a colliding site of another.
   - `[adv B3]` / `[adv A3]` *Multi-body items*: reconcile the subject together with every inline callee body handed to `initMachineStateWithCallees` through `reconcile_multi_item_coverage`. Build each item with `ItemCoverageInput::from_lean_module` and its own obligations. Fill `CalleeClosure::inline_callees` with that exact callee list, and `external_callees` with the callees answered by `#[external_spec]` contracts. Never append censuses across bodies. By `censusMirBodyFaultSites_instantiate` (`[adv A3]`), polymorphic generic inline callees (`calleeBody.instantiate subst`) have the exact same census as `calleeBody` whenever `bodyHasNoParamCallConst calleeBody = true`.
4. **Gate `VERIFIED`** on `CoverageVerdict::Verified`; otherwise downgrade fail-closed to `UNKNOWN(UNSUPPORTED_CONSTRUCT)` with the exact `(bb, stmt, class)` list.
   - `[adv B4]` *Trace-level guarantee*: with `cfgTargetsInBounds body = true` and a verified reconciliation, `initMachineState_mirStepsTop_reconciled_safety` covers every top-level execution through external calls. External `#[external_spec]` contracts must answer at the caller's frame (`MirCallAnsTopFrame`). Track that as an explicit assumption in the external-spec format.
5. **Keep the Lean side authoritative**: Track A should extend §2.1 (class-precise attribution) before relying on per-class discharge for constructs outside it.
