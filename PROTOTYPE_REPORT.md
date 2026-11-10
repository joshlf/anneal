# Prototype Report: Independent MIR Fault-Site Census & Fail-Closed Coverage Reconciler

- **Workstream ID**: `ws-proto-fault-site-coverage-reconciler` (`ep1-prototype-fault-site-census-and-reconciler`)
- **Track**: Track P (`prototype`, isolated from `unstable` and `main`)
- **Target Paired Track A Workstream**: `ws-fault-site-coverage-reconciler`
- **Current Pass**: `[adv A1]` (Round 1 critique & fix of `[adv B1]`)

---

## 1. Executive Summary

This Track P prototype builds a defense-in-depth cross-check for Anneal's MIR verification pipeline against the silent false-proof failure mode ("the obligation generator omits a fault site, so the item reports `VERIFIED` vacuously"). Instead of trusting `cargo-anneal`'s obligation generator to enumerate every runtime UB condition, it adds two independent components:

1. **Lean 4 independent fault-site census and completeness proofs** (`theory/Anneal/FaultSiteCensusPrototype.lean`):
   - 12 canonical `MirFaultClass` categories, `FaultSite`, `PropertyStatus`, `PropertyRegistry`.
   - An independent structural walker `censusMirBodyFaultSites (body : CapturedMir) : List FaultSite` over `Trusted.MirAst`, duplicate-free (`censusMirBodyFaultSites_nodup`).
   - Completeness over `Trusted.MirSemantics.stepMirFn` (`stepMirFn_activeBody_fault_in_census`, `stepMirFn_fault_in_census`) and over every **one-step UB exposure**, including `.faulted .ub` continuations of external calls (`stepMirFn_exposesUb_in_census`, `stepMirFn_extCall_cont_fault_in_census`).
   - **Semantic precision & interprocedural PC certificates** (`[adv B1]` + `[adv A1]`):
     - Class-level justification of `BinOp` (`censusBinOpFaultClasses_exact`, `evalScalarBinOp_ub_cause`), `StorageLive`/`StorageDead`/`Return`/`Goto`/borrow `.ub` edges.
     - `[adv A1]` exact `.ub` characterizations and non-overapproximation proofs for unevaluated `Rvalue` assignments (`evalRvalue_eq_unsupported_of_rvalueUnevaluated`, `evalStmt_assign_unevaluated_eq_unsupported`), `PlaceMention` (`evalStmt_placeMention_ub_iff`), unprojected and deref-projected `Deinit` / `Drop` (`evalStmt_deinit_unprojected_ub_iff`, `evalStmt_deinit_deref_eq_unsupported`, `evalTerminator_drop_unprojected_ub_iff`), `CastKind.pointerCoercion "MutToConstPointer"` (`evalRvalue_cast_mutToConstPointer_ub_iff`), and diverging `Call` destination irrelevance (`evalTerminator_diverging_call_exposesUb_destination_irrelevant`).
     - `[adv A1]` interprocedural `ValidMirPc` preservation across `pushCalleeFrame`, `pushDivergingCalleeFrame`, `enterTailCalleeFrame`, and inline `TerminatorKind.return_` (`validMirPc_pushCalleeFrame`, `validMirPc_pushDivergingCalleeFrame`, `validMirPc_enterTailCalleeFrame`, `validMirPc_return_inline`).
   - Fail-closed reconciler theorems and kernel-checked `by decide` witnesses (`0` `sorryAx`, `0` `Lean.ofReduceBool`), with kernel-evaluated **liveness certificates** for every false-proof probe site.
2. **Rust registry, census frontends, fail-closed reconciler and probes** (`crates/cargo-anneal/src/fault_census_proto.rs`):
   - 1-to-1 `MirFaultClass`, `FaultSite`, `PropertyStatus`, `PropertyDescriptor`, `PropertyRegistry`, `ProtoAggregateKind`.
   - Three census frontends: `census_mir_fault_sites(&ProtoMirBody)`, `census_ir_captured_mir(&IrCapturedMir)`, and the fail-closed Lean scanners `census_lean_mir_module(&str)` (strict emitter-module grammar) and `census_lean_mir_def(&str, &str)` (named-definition extraction for the witness file).
   - `reconcile_obligation_coverage` / `reconcile_lean_mir_coverage`, the four false-proof probes driven by an independent mock obligation emitter, the registry probe, a real `rustc`-captured corpus test, and the cross-language Lean-to-Rust parity test.

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
| Valid PC / CFG & Interprocedural PC | `ValidMirPc`, `cfgTargetsInBounds`, `validMirPc_initMachineState`, `stepMirFn_preserves_validMirPc`, `validMirPc_pushCalleeFrame`, `validMirPc_pushDivergingCalleeFrame`, `validMirPc_enterTailCalleeFrame`, `validMirPc_return_inline` | Entry PC is valid; intra-frame steps with in-bounds CFG targets and interprocedural call/tail-call/inline-return transitions preserve `ValidMirPc`. |
| Construct classification | `evalStmt_exposesUb_implies_mem_censusStmt`, `evalTerminator_exposesUb_implies_mem_censusTerminator` (and `.fail .ub` corollaries `evalStmt_ub_implies_mem_censusStmt`, `evalTerminator_ub_implies_mem_censusTerminator`) | Any UB exposure of a statement/terminator implies a non-empty construct census. |
| Completeness | `stepMirFn_activeBody_exposesUb_in_census`, `stepMirFn_exposesUb_in_census`, `stepMirFn_extCall_cont_fault_in_census`, `stepMirFn_activeBody_fault_in_census`, `stepMirFn_fault_in_census` | Every UB exposure from a valid PC (active callee or top level) is censused at that PC. |
| Zero-census corollaries | `stepMirFn_not_exposesUb_of_site_uncensused`, `stepMirFn_ne_ub_of_site_uncensused`, `stepMirFn_ne_ub_of_empty_census` | An uncensused PC exposes no UB, directly or through any continuation. |
| Reconciler | `mem_unmappedFaultSites_iff`, `mem_unmappedFaultSitesWithRegistry_iff`, `reconcileFaultCoverage_verified_iff`, `reconcileFaultCoverage_unknown_nonempty`, `reconcileFaultCoverageWithRegistry_verified_iff`, `reconcileFaultCoverageWithRegistry_rejects_unemitted`, `reconcileFaultCoverage_mutation_detected` | Soundness/completeness of the fail-closed verdict; non-verified registry classes can never be discharged; stripping any census site is detected. |
| End-to-end bridge | `stepMirFn_fault_in_discharged_of_reconciled`, `stepMirFn_exposesUb_in_discharged_of_reconciled` | A reconciled body discharges (with an `emittedAndVerified` class) every UB exposure at a valid top-level PC. |

### 2.1 Semantic Precision Certificates (`[adv B1]` + `[adv A1]`)

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
| `witness*_site_live` (4 probes) + `witnessWrappingArith_census_precise` | `stepMirFn witness... (concrete state) = MirStepNode.fail .ub` by kernel evaluation at the exact site each mutant strips, plus non-faulting contrast states and `stepMirFn witnessWrappingArithBody (0, 4) = MirStepNode.unsupported` (`rfl`). |

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

---

## 5. Adversarial Round History (`[adv A0]` → `[adv B1]` → `[adv A1]` → `[adv B2]`)

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

### Semantic subtleties (carried from `[adv A0]`, verified in `[adv B1]`)

- `ValidMirPc` is required because an out-of-bounds PC faults without any syntactic site; `stepMirFn_preserves_validMirPc` keeps it invariant for top-level frames with in-bounds CFG targets.
- `.return_` reads `_0` and, in an inline frame, writes into the *caller's* `destination`, so its classes are attributed to the callee's return site.
- The `.ub` of an out-of-bounds `Goto` happens on the *next* step.

### Known limitations (for later rounds)

- Completeness remains existential in the class for constructs outside §2.1; extending class-precise attribution to operand reads, places, calls, and `copyNonOverlapping` is open.
- The strict module grammar targets `anneal-rustc-capture` output. It rejects anything outside the emitter's command set, `open`s, and constructor namespaces, but it does not model Lean elaboration in general.
- The cross-language differential is a `#guard`-checked experiment over compiled evaluation (not kernel `decide`); kernel-checked parity is limited to the witness bodies.

---

## 6. Verification Receipts (`[adv B2]`)

All commands run from the repository root with `W = 1`.

1. **Primary command**, exit `0` (`34.2 s` wall-clock):
   ```bash
   cargo test --manifest-path crates/cargo-anneal/Cargo.toml --lib fault_census_proto && \
   cargo test --manifest-path crates/cargo-anneal/Cargo.toml fault_census_proto && \
   (cd examples && anneal-lean-run --mode file --concurrency 1 -- lake env lean ../theory/Anneal/FaultSiteCensusPrototype.lean)
   ```
   `16 passed, 0 failed, 1 ignored` (the manual Lean differential harness) on both test targets, `0` Rust warnings, and Lean `0` errors / `0` warnings.
2. **Kernel axiom audit**: a scratch copy with `#print axioms` over all `203` public `def`/`theorem` declarations (`125` theorems), run via `anneal-lean-run --mode file --concurrency 1` outside the worktree. Result: `0` `sorryAx`, `0` `Lean.ofReduceBool`, and `113/125` theorems `Classical.choice`-free.
3. **Proof health**: `python3 tools/anneal-lsp/server/proof_health.py theory/Anneal/FaultSiteCensusPrototype.lean` exits `0` with `0` findings.
4. **Cross-language differential** (`[adv B2]`, optional): `FAULT_CENSUS_DIFF_DIR=<dir> cargo test --manifest-path crates/cargo-anneal/Cargo.toml --lib dump_lean_census_differential_corpus -- --ignored`, then `(cd examples && anneal-lean-run --mode file --concurrency 1 -- lake env lean <dir>/LeanCensusDifferential.lean)`. Exit `0`: `400` `#guard`s, `4990` sites, all 12 classes, `55 s`. A corrupted copy exits `1`.
5. **Hygiene**: `git status --porcelain` is empty after commit, and `git diff --name-only a5e12e5fac628cc71522b67a1b427e17e2927818..HEAD` ⊆ {`PROTOTYPE_REPORT.md`, `crates/cargo-anneal/src/fault_census_proto.rs`, `crates/cargo-anneal/src/lib.rs`, `theory/Anneal/FaultSiteCensusPrototype.lean`}. There are zero internal hostnames, user paths, LDAPs, CL numbers, or internal model names.

---

## 7. Integration Architecture for Track A (`ws-fault-site-coverage-reconciler`)

1. **Promote the Lean module** to `theory/Anneal/FaultSiteCensus.lean`, importing it from `theory/Anneal.lean` in a coordinated Track A change that also updates the trusted-boundary checker's pinned import list.
2. **Tag obligations with fault sites**: every obligation emitted by `crates/cargo-anneal/src/obligations.rs` should carry the `FaultSite`s it discharges.
3. **Reconcile at verification time**: run `census_ir_captured_mir` on the captured MIR and `census_lean_mir_module` on the generated `Mir/<Item>.lean`, require both censuses to agree, and reconcile against the discharged sites with a stage-aware registry (`PropertyRegistry::realistic_safe_subset_registry()` as the starting point).
4. **Gate `VERIFIED`** on `CoverageVerdict::Verified`; otherwise downgrade fail-closed to `UNKNOWN(UNSUPPORTED_CONSTRUCT)` with the exact `(bb, stmt, class)` list.
5. **Keep the Lean side authoritative**: Track A should extend §2.1 (class-precise attribution) before relying on per-class discharge for constructs outside it.
