# Prototype Report: Independent MIR Fault-Site Census & Fail-Closed Coverage Reconciler

- **Workstream ID**: `ws-proto-fault-site-coverage-reconciler` (`ep1-prototype-fault-site-census-and-reconciler`)
- **Track**: Track P (`prototype`, isolated from `unstable` and `main`)
- **Target Paired Track A Workstream**: `ws-fault-site-coverage-reconciler`
- **Current Pass**: `[adv B1]` (round 1 adversarial critique & repair of `[adv A0]`)

---

## 1. Executive Summary

This Track P prototype builds a defense-in-depth cross-check for Anneal's MIR verification pipeline against the silent false-proof failure mode ("the obligation generator omits a fault site, so the item reports `VERIFIED` vacuously"). Instead of trusting `cargo-anneal`'s obligation generator to enumerate every runtime UB condition, it adds two independent components:

1. **Lean 4 independent fault-site census and completeness proofs** (`theory/Anneal/FaultSiteCensusPrototype.lean`):
   - 12 canonical `MirFaultClass` categories, `FaultSite`, `PropertyStatus`, `PropertyRegistry`.
   - An independent structural walker `censusMirBodyFaultSites (body : CapturedMir) : List FaultSite` over `Trusted.MirAst`, duplicate-free (`censusMirBodyFaultSites_nodup`).
   - Completeness over `Trusted.MirSemantics.stepMirFn` (`stepMirFn_activeBody_fault_in_census`, `stepMirFn_fault_in_census`), strengthened in `[adv B1]` to every **one-step UB exposure**, including `.faulted .ub` continuations of external calls (`stepMirFn_exposesUb_in_census`, `stepMirFn_extCall_cont_fault_in_census`).
   - `[adv B1]` **semantic precision certificates**: class-level justification of census entries against the trusted evaluator (`censusBinOpFaultClasses_exact`, `evalScalarBinOp_ub_cause`, exact `StorageLive`/`StorageDead`/`Return`/`Goto`/borrow `.ub` edges).
   - Fail-closed reconciler theorems and kernel-checked `by decide` witnesses (`0` `sorryAx`, `0` `Lean.ofReduceBool`), with kernel-evaluated **liveness certificates** for every false-proof probe site.
2. **Rust registry, census frontends, fail-closed reconciler and probes** (`crates/cargo-anneal/src/fault_census_proto.rs`):
   - 1-to-1 `MirFaultClass`, `FaultSite`, `PropertyStatus`, `PropertyDescriptor`, `PropertyRegistry`.
   - Three census frontends: `census_mir_fault_sites(&ProtoMirBody)`, `census_ir_captured_mir(&IrCapturedMir)`, and the fail-closed Lean scanners `census_lean_mir_module(&str)` (strict emitter-module grammar, `[adv B1]`) and `census_lean_mir_def(&str, &str)` (named-definition extraction for the witness file).
   - `reconcile_obligation_coverage` / `reconcile_lean_mir_coverage`, the four false-proof probes driven by an independent mock obligation emitter (`[adv B1]`), the registry probe, a real `rustc`-captured corpus test, and the cross-language Lean-to-Rust parity test.

---

## 2. Lean 4 Theorem Inventory (`theory/Anneal/FaultSiteCensusPrototype.lean`)

Every declaration elaborates with **zero `sorryAx`** and **zero `Lean.ofReduceBool`** (scratch `#print axioms` over all `188` public declarations / `113` public theorems; `101/113` theorems are `Classical.choice`-free — the `12` exceptions are the `stepMirFn_*` theorems that go through `simp`/`omega` over the trusted machine, plus the witness corollary built on them).

| Category | Declaration(s) | Statement |
| :--- | :--- | :--- |
| Taxonomy | `MirFaultClass.mem_all`, `MirFaultClass.nodup_all`, `MirFaultClass.length_all` | `all` lists exactly the 12 classes, duplicate-free. |
| | `MirFaultClass.toRank_lt_twelve`, `MirFaultClass.ofRank?_toRank`, `MirFaultClass.toRank_injective` | Rank encoding `0..11` with round trip and injectivity. |
| | `MirFaultClass.fromStr?_asStr`, `MirFaultClass.asStr_fromStr?`, `MirFaultClass.asStr_injective` | Canonical `snake_case` names (shared with Rust) round-trip. |
| Registry | `PropertyStatus.isVerified_eq_true_iff`, `registryWithStatus_self`, `registryWithStatus_ne` | Registry status semantics and point overrides. |
| Dedup / Nodup | `mem_dedupFaultClasses_iff`, `nodup_dedupFaultClasses`, `censusMirBodyFaultSites_nodup` | Canonical per-site dedup; the whole census is `Nodup`. |
| Membership | `mem_censusStmtsAux_of_get?`, `mem_censusBlockFaultSites_of_stmt`, `mem_censusBlockFaultSites_of_terminator`, `mem_censusBlocksAux_of_get?`, `mem_censusMirBodyFaultSites_of_block` | Structural membership of `(bb, stmt, cls)` sites. |
| Census equations | `censusStmtFaultClasses_nop` / `_coverage` / `_constEvalCounter` / `_dropHint` / `_storageLive` / `_storageDead`; `censusTerminatorFaultClasses_unwindTerminate` / `_inlineAsm` / `_unreachable` / `_unwindResume` / `_return` / `_goto_inBounds` / `_goto_outOfBounds`; `censusBinOpFaultClasses_add` / `_addWithOverflow` / `_addUnchecked` / `_div` / `_shl` / `_shlUnchecked` / `_offset`; `storageLive_strict_subset_all` | `rfl`-level restatements of the census definition (these alone justify nothing semantically — see §2.1). |
| Pure constructs never fault | `evalStmt_pure_constructs_ne_ub`, `evalTerminator_pure_constructs_ne_ub`, `evalOperand_constant_non_indirect_ne_ub` | `.nop`/`.coverage`/`.constEvalCounter`/`.backwardIncompatibleDropHint`, `.goto`/`.unwindTerminate`/`.inlineAsm`, and non-`.indirect` constants never return `.ub`. |
| Valid PC / CFG | `ValidMirPc`, `cfgTargetsInBounds`, `validMirPc_initMachineState`, `stepMirFn_preserves_validMirPc` (+ `evalStmt_preservesPc`, `evalTerminator_preservesPc`) | Entry PC is valid; intra-frame steps of a top-level frame with in-bounds CFG targets preserve `ValidMirPc`. |
| Construct classification | `evalStmt_exposesUb_implies_mem_censusStmt`, `evalTerminator_exposesUb_implies_mem_censusTerminator` (and the `.fail .ub` corollaries `evalStmt_ub_implies_mem_censusStmt`, `evalTerminator_ub_implies_mem_censusTerminator`) | Any UB exposure of a statement/terminator implies a non-empty construct census. |
| Completeness | `stepMirFn_activeBody_exposesUb_in_census`, `stepMirFn_exposesUb_in_census`, `stepMirFn_extCall_cont_fault_in_census`, `stepMirFn_activeBody_fault_in_census`, `stepMirFn_fault_in_census` | Every UB exposure from a valid PC (active callee or top level) is censused at that PC. |
| Zero-census corollaries | `stepMirFn_not_exposesUb_of_site_uncensused`, `stepMirFn_ne_ub_of_site_uncensused`, `stepMirFn_ne_ub_of_empty_census` | An uncensused PC exposes no UB, directly or through any continuation. |
| Reconciler | `mem_unmappedFaultSites_iff`, `mem_unmappedFaultSitesWithRegistry_iff`, `reconcileFaultCoverage_verified_iff`, `reconcileFaultCoverage_unknown_nonempty`, `reconcileFaultCoverageWithRegistry_verified_iff`, `reconcileFaultCoverageWithRegistry_rejects_unemitted`, `reconcileFaultCoverage_mutation_detected` | Soundness/completeness of the fail-closed verdict; non-verified registry classes can never be discharged; stripping any census site is detected. |
| End-to-end bridge | `stepMirFn_fault_in_discharged_of_reconciled`, `stepMirFn_exposesUb_in_discharged_of_reconciled` | A reconciled body discharges (with an `emittedAndVerified` class) every UB exposure at a valid top-level PC. |

### 2.1 `[adv B1]` Semantic Precision Certificates

| Declaration | What it proves against `Trusted.MirSemantics` |
| :--- | :--- |
| `evalScalarBinOp_ne_ub_of_census_nil` | Every `BinOp` with census `[]` (wrapping `add`/`sub`/`mul`, flagged `*WithOverflow`, masked `shl`/`shr`, bitwise, comparisons, `cmp`) can never make `evalScalarBinOp` return `.ub`. |
| `BinOpFaultCause`, `evalScalarBinOp_ub_cause` | Class-precise completeness: each `.ub` of `evalScalarBinOp` is explained by a class in `censusBinOpFaultClasses op` *and* its concrete cause (`.divRemByZero` only for a zero divisor, `.shiftOverflow` only for a distance `≥` the bit width, `.arithOverflow` only for unchecked arithmetic or signed `MIN / -1`). |
| `censusBinOpFaultClasses_exact` (+ `evalScalarBinOp_*_ub_witness`) | For every scalar operator, census `= []` **iff** `evalScalarBinOp` can never fault — no over- and no under-approximation, with concrete faulting inputs (`rfl`) for every non-empty entry. |
| `evalStmt_storageLive_ub_iff`, `evalStmt_storageDead_ub_iff` | Exact edges: fault iff `loc ≥ locals.length` or an active protector protects a borrow of `loc` (`hasProtectedLocalBorrow`). |
| `evalTerminator_unreachable_ub` | `Unreachable` always faults. |
| `evalTerminator_return_root_ub_iff`, `evalTerminator_return_inline_ub_iff` | Root frame: fault iff `_0` is not initialized. Inline frame: additionally iff the caller expected a diverging callee or the write into `caller.destination` faults. |
| `stepMirFn_after_goto_oob_ub` | An out-of-bounds `Goto` steps successfully but makes the *next* `stepMirFn` fault — the reason the census labels that `Goto` site with `.boundsCheck`. |
| `evalRvalue_borrow_nonDeref_ub_iff` | Borrowing (`Ref`/`RawPtr`) a place whose projection does not start with `.deref` faults iff the root local is missing/dead or an `.index` local is uninitialized — justifying the `[.uninitRead]` census. |
| `witness*_site_live` (4 probes) | `stepMirFn witness... (concrete state) = MirStepNode.fail .ub` by kernel evaluation at the exact site each mutant strips, plus a non-faulting contrast state (`ne_fail_ub_of_stepNodeIsTau`). |

---

## 3. Construct-to-Fault-Class Matrix (as implemented after `[adv B1]`)

`Place read` = `uninitRead :: projection classes`; projection classes: `.deref` → `ptrDerefInvalid, ptrAlignMismatch, treeBorrowsViolation`; `.index` → `boundsCheck, uninitRead`; `.constantIndex`/`.subslice` → `boundsCheck`; `.downcast` → `scalarNicheInvalid`; `.field`/`.opaqueCast`/`.unwrapUnsafeBinder` → `[]`. `Place write` = `storageLiveProtected, treeBorrowsViolation` (plus `uninitRead` and projection classes when projected).

| Construct | Census classes | Justification in `Trusted.MirSemantics` |
| :--- | :--- | :--- |
| `.copy p` / `.move p` operand | place read | `evalOperand` reads the place. |
| `.constant c` | `[]`, or `boundsCheck, scalarNicheInvalid, uninitRead` for `.indirect` | `evalOperand_constant_non_indirect_ne_ub`; `.indirect` decodes global bytes. |
| `Use op` / `WrapUnsafeBinder op` | operand + `scalarNicheInvalid` for `copy`/`move` | `validateLoadedValue` rejects invalid `bool` scalars (**class gap fixed in `[adv B1]`**). |
| `BinaryOp op l r` | operands + `censusBinOpFaultClasses op` | `censusBinOpFaultClasses_exact`; `.offset` → `arithOverflow, boundsCheck, ptrDerefInvalid, treeBorrowsViolation` (`evalPtrOffsetBinOp` faults on a disabled tag — **`treeBorrowsViolation` added in `[adv B1]`**). |
| `UnaryOp .neg` / `.not` / `.ptrMetadata` | operand + `[]` / `scalarNicheInvalid` / `ptrDerefInvalid` | `.neg` wraps; `evalUnaryNot` faults on invalid `bool`; width mismatch for metadata. |
| `Cast .intToInt` / `.pointerExposeProvenance` / `.pointerWithExposedProvenance` | operand only | no `.ub` edge beyond the operand. |
| `Cast .floatToInt` / `.floatToFloat` / `.intToFloat` | `[]` | no `evalRvalue` arm (`.unsupported`, operand never read). |
| `Cast .transmute` / `.subtype` | operand + `scalarNicheInvalid, uninitRead` | `evalByteCast`. |
| `Cast .ptrToPtr` / `.pointerCoercion` / `.fnPtrToPtr` | operand + `boundsCheck, ptrDerefInvalid, ptrAlignMismatch, scalarNicheInvalid` | pointer re-typing / reification (kept conservative). |
| `Ref`/`RawPtr p` | `[uninitRead]` unless `p` starts with `.deref`; else `uninitRead, ptrDerefInvalid, ptrAlignMismatch, treeBorrowsViolation` + projection classes | `evalRvalue_borrow_nonDeref_ub_iff`. |
| `Repeat op _` / `Aggregate _ ops` | operands only | no `.ub` beyond operand evaluation. |
| `NullaryOp _` / `ThreadLocalRef _` / `ShallowInitBox _ _` | `[]` | no `evalRvalue` arm (`.unsupported`). |
| `Len p` / `Discriminant p` / `CopyForDeref p` | place read + `boundsCheck` / + `scalarNicheInvalid` / place read | `evalPlaceLen` / `evalPlaceDiscriminant` / plain read. |
| `.nop`, `.coverage`, `.constEvalCounter`, `.backwardIncompatibleDropHint` | `[]` | `evalStmt_pure_constructs_ne_ub`. |
| `.storageLive l` / `.storageDead l` | `storageLiveProtected` | `evalStmt_storageLive_ub_iff` / `evalStmt_storageDead_ub_iff`. |
| `.assign dst rv` | place write(dst) + rvalue classes | `evalRvalue` then the destination write. |
| `.retag _ p` | place read + `boundsCheck, ptrDerefInvalid, treeBorrowsViolation` | retag checks pointer shape, permissions, mutability, bounds — never alignment (**`ptrAlignMismatch` removed in `[adv B1]`**). |
| `.placeMention p` / `.deinit p` | `uninitRead` + projection classes | dead/missing root, uninitialized index operands, projected read. |
| `.setDiscriminant p _` | `scalarNicheInvalid, uninitRead` (unprojected) or read + write + `scalarNicheInvalid` | non-aggregate / uninitialized / dead targets. |
| `.intrinsic (.assume op)` | operand + `scalarNicheInvalid` | violated assumption or non-scalar condition. |
| `.intrinsic (.copyNonOverlapping ..)` | operands + `arithOverflow, boundsCheck, ptrDerefInvalid, ptrAlignMismatch, treeBorrowsViolation, scalarNicheInvalid, uninitRead` | `evalCopyNonOverlapping` (kept conservative). |
| `.goto t` | `[]` in bounds, `boundsCheck` out of bounds | `evalTerminator_pure_constructs_ne_ub`, `stepMirFn_after_goto_oob_ub`. |
| `.unwindTerminate` / `.inlineAsm` | `[]` | abort / `.unsupported`. |
| `.unreachable` | `unreachableTerminator` | `evalTerminator_unreachable_ub`. |
| `.unwindResume` | `callAbiMismatch` | `unwindFromCallStack` faults through a `returnUnwind = .unreachable` caller. |
| `.return_` | `treeBorrowsViolation, uninitRead, callAbiMismatch` | `evalTerminator_return_root_ub_iff`, `evalTerminator_return_inline_ub_iff`. |
| `.switchInt d _` | operand + `scalarNicheInvalid` (+ `boundsCheck` if a target is out of bounds) | non-scalar discriminant. |
| `.drop p _ _` | place read (+ `boundsCheck` for out-of-bounds targets) | dead/missing/uninitialized place. |
| `.assert c _ _ u` | operand + `scalarNicheInvalid` + (`unreachableTerminator` for `u = .unreachable`, `callAbiMismatch` for `.continue_`, nothing for `.cleanup`/`.terminate`) | `applyUnwindAction` (**speculative arithmetic/bounds labels removed in `[adv B1]`**; the trusted AST carries no `AssertKind`). |
| `.call f args dst _ u` | operands + place write(dst) + `callAbiMismatch` + callee classes (`censusCalleeDefPathFaultClasses`, or `ptrDerefInvalid` for indirect callees) + `unreachableTerminator` for `u = .unreachable` | `resolveCallTarget`, argument evaluation, `checkCalleeTargetCompatible`, intrinsic dispatch, and the external-call continuations covered by `stepMirFn_extCall_cont_fault_in_census`. |
| `.tailCall f args` | operands + `callAbiMismatch` (+ `ptrDerefInvalid` for indirect callees) | `evalTailCallTerminator`. |

Callee classes follow `classifyRustIntrinsic?` exactly: only `core::intrinsics::*` paths are intrinsics (`std::intrinsics::*` paths are ordinary callees — **Rust parity bug fixed in `[adv B1]`**).

---

## 4. False-Proof Mutation Probe Results

`[adv B1]` replaced the `[adv A0]` probe harness, which reconciled the census against *itself minus a hard-coded subset* (pure set difference), with an **independent mock obligation emitter** (`mock_emit_obligations`): it explores the CFG from `bb0`, identifies loop latches, and injects one realistic emitter bug per probe. The baseline emitter must reconcile `Verified` against the independent census, and each mutant must be rejected at exactly the sites pinned by the Lean `by decide` witnesses. Each stripped site also has a Lean liveness certificate (a concrete state where `stepMirFn` faults there).

| Probe | Emitter bug | Baseline | Mutant | Missing sites (Rust = Lean) | Lean liveness certificate |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `CallArgBlindProbe` | call arguments treated as opaque values (deref projections unchecked) | `VERIFIED` | `UNKNOWN(UNSUPPORTED_CONSTRUCT)` | `(0,0,ptr_deref_invalid)`, `(0,0,ptr_align_mismatch)` | `witnessCallArgBlind_call_site_live` (dangling `*_1` argument) |
| `SwitchBreakStripProbe` | `SwitchInt` exploration drops the `otherwise` edge (`bb2` never explored) | `VERIFIED` | `UNKNOWN(..)` | all `bb2` sites: `(2,0,{arith_overflow, div_rem_by_zero, tree_borrows_violation, uninit_read, storage_live_protected})`, `(2,1,{tree_borrows_violation, uninit_read, call_abi_mismatch})` | `witnessSwitchBreakStrip_div_site_live` (`_2 = 0` faults, `_2 = 2` steps) |
| `LoopUpdateOverflowProbe` | overflow obligations skipped in loop-latch blocks | `VERIFIED` | `UNKNOWN(..)` | `(2,0,arith_overflow)` for the latch `AddUnchecked` | `witnessLoopUpdateOverflow_latch_site_live` (`u32::MAX` faults, `7` steps; wrapping `Add` at `(2,1)` carries no `arith_overflow`) |
| `DerefAliasProbe` | deref/alignment/aliasing obligations skipped at dereferencing statements | `VERIFIED` | `UNKNOWN(..)` | `(0,0,ptr_deref_invalid)`, `(0,0,ptr_align_mismatch)`, `(0,0,tree_borrows_violation)` | `witnessDerefAlias_deref_site_live` (dangling `*_2`) |
| `PropertyRegistryUnemittedProbe` | `tree_borrows_violation` marked `UnemittedGap` while `discharged = census` | `VERIFIED` (full registry) | `UNKNOWN(..)` | `(0,0,tree_borrows_violation)`, `(0,1,tree_borrows_violation)`; `unemitted_classes = [TreeBorrowsViolation]` | `witnessDerefAlias_registry_unemitted_rejected` (`by decide`) |

---

## 5. Findings, Lexer Traps & Semantic Subtleties (by round)

### `[adv B1]` findings against `[adv A0]` (all fixed in this pass)

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

### Semantic subtleties (carried from `[adv A0]`, verified in `[adv B1]`)

- `ValidMirPc` is required because an out-of-bounds PC faults without any syntactic site; `stepMirFn_preserves_validMirPc` keeps it invariant for top-level frames with in-bounds CFG targets.
- `.return_` reads `_0` and, in an inline frame, writes into the *caller's* `destination`, so its classes are attributed to the callee's return site.
- The `.ub` of an out-of-bounds `Goto` happens on the *next* step.

### Known limitations (for later rounds)

- Completeness remains existential in the class for constructs outside §2.1; extending class-precise attribution to operand reads, places, calls, and `copyNonOverlapping` is open.
- `ProtoRvalue::Aggregate` does not carry its `AggregateKind`, so coroutine aggregates (never evaluated by `evalRvalue`) still contribute operand classes (safe over-approximation).
- The strict module grammar targets `anneal-rustc-capture` output; Lean elaboration-level tricks beyond lexical/grammar checks (for example overloaded `open` resolution) are mitigated, not proven impossible.

---

## 6. Verification Receipts (`[adv B1]`)

All commands run from the repository root with `W = 1`.

1. **Primary command** — exit `0`:
   ```bash
   cargo test --manifest-path crates/cargo-anneal/Cargo.toml --lib fault_census_proto && \
   cargo test --manifest-path crates/cargo-anneal/Cargo.toml fault_census_proto && \
   (cd examples && anneal-lean-run --mode file --concurrency 1 -- lake env lean ../theory/Anneal/FaultSiteCensusPrototype.lean)
   ```
   `12 passed, 0 failed` (library target), `0` Rust warnings, Lean `0` errors / `0` warnings (primary command `18.2 s` wall-clock).
2. **Kernel axiom audit** — scratch copy with `#print axioms` over all `188` public declarations (`113` theorems), run via `anneal-lean-run --mode file --concurrency 1` outside the worktree: `0` `sorryAx`, `0` `Lean.ofReduceBool`, `101/113` theorems `Classical.choice`-free.
3. **Proof health** — `python3 tools/anneal-lsp/server/proof_health.py theory/Anneal/FaultSiteCensusPrototype.lean`: exit `0`, `0` findings.
4. **Hygiene** — `git status --porcelain` empty after commit; `git diff --name-only a5e12e5fac628cc71522b67a1b427e17e2927818..HEAD` ⊆ {`PROTOTYPE_REPORT.md`, `crates/cargo-anneal/src/fault_census_proto.rs`, `crates/cargo-anneal/src/lib.rs`, `theory/Anneal/FaultSiteCensusPrototype.lean`}.

---

## 7. Integration Architecture for Track A (`ws-fault-site-coverage-reconciler`)

1. **Promote the Lean module** to `theory/Anneal/FaultSiteCensus.lean`, importing it from `theory/Anneal.lean` in a coordinated Track A change that also updates the trusted-boundary checker's pinned import list.
2. **Tag obligations with fault sites**: every obligation emitted by `crates/cargo-anneal/src/obligations.rs` should carry the `FaultSite`s it discharges.
3. **Reconcile at verification time**: run `census_ir_captured_mir` on the captured MIR and `census_lean_mir_module` on the generated `Mir/<Item>.lean`, require both censuses to agree, and reconcile against the discharged sites with a stage-aware registry (`PropertyRegistry::realistic_safe_subset_registry()` as the starting point).
4. **Gate `VERIFIED`** on `CoverageVerdict::Verified`; otherwise downgrade fail-closed to `UNKNOWN(UNSUPPORTED_CONSTRUCT)` with the exact `(bb, stmt, class)` list.
5. **Keep the Lean side authoritative**: Track A should extend §2.1 (class-precise attribution) before relying on per-class discharge for constructs outside it.
