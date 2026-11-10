# Prototype Report: Independent MIR Fault-Site Census & Fail-Closed Coverage Reconciler

- **Workstream ID**: `ws-proto-fault-site-coverage-reconciler` (`ep1-prototype-fault-site-census-and-reconciler`)
- **Track**: Track P (`prototype`, isolated from `unstable` and `main`)
- **Target Paired Track A Workstream**: `ws-fault-site-coverage-reconciler`

---

## 1. Executive Summary

This Track P prototype implements and machine-verifies a defense-in-depth architecture for Anneal's MIR verification pipeline that eliminates the silent false-proof failure mode ("bug in `obligations.rs` omits a fault site $\rightarrow$ vacuous `VERIFIED`").

Rather than trusting `cargo-anneal`'s obligation generator to enumerate all runtime Undefined Behavior (UB) conditions, this prototype introduces two independent, cross-checked components:

1. **Lean 4 Independent Syntactic MIR Fault-Site Census & Completeness Proof (`theory/Anneal/FaultSiteCensusPrototype.lean`)**:
   - Formalizes the 12 canonical `MirFaultClass` categories, `FaultSite`, `PropertyStatus`, and `PropertyRegistry`.
   - Defines an independent structural AST walker `censusMirBodyFaultSites (body : CapturedMir) : List FaultSite` directly over `Trusted.MirAst.CapturedMir`.
   - Machine-checks the **Fault-Site Census Completeness Theorem (`stepMirFn_fault_in_census`)** directly over `Trusted.MirSemantics.stepMirFn` (both for general `s.memory.activeCallee.getD body` and top-level `s.memory.activeCallee = none` under valid PC bounds `ValidMirPc`), alongside CFG target-bounds preservation (`stepMirFn_preserves_validMirPc`).
   - Machine-checks **Construct-Level Precision / Non-Overapproximation Theorems** proving that pure MIR statements/terminators emit `[]` and cannot fault with `MirStepNode.fail .ub`, and that each syntactic MIR construct emits only the exact subset of `MirFaultClass` variants justified by `Trusted.MirSemantics`.
   - Machine-checks the fail-closed `CoverageVerdict` and `reconcileFaultCoverage` / `reconcileFaultCoverageWithRegistry` soundness, completeness, unemitted-class rejection, and mutation-detection theorems, backed by compile-time `by decide` witness suites (`0` `sorryAx`, `0` `Lean.ofReduceBool`).

2. **Rust Obligation Property Registry, Fail-Closed Coverage Reconciler & False-Proof Mutation Probes (`crates/cargo-anneal/src/fault_census_proto.rs`)**:
   - Implements the 1-to-1 `MirFaultClass` vocabulary, `FaultSite`, `PropertyStatus`, and `PropertyRegistry` (with stage-aware and full-verified configurations).
   - Implements three independent census frontends:
     - `census_mir_fault_sites(&ProtoMirBody)` over a structured MIR representation mirroring `Trusted.MirAst`.
     - `census_ir_captured_mir(&IrCapturedMir)` directly over `anneal_rustc_capture::mir_ir::IrCapturedMir`.
     - `census_lean_mir_module(&str)` / `census_lean_mir_def(&str, &str)`, a fail-closed recursive-descent lexer/parser for emitted `Mir/<Item>.lean` files that handles line comments (`--`), nested block comments (`/- ... -/`), string literals, raw strings (`r#"..."#`), interpolated strings (`s!"..."`), and guillemet identifiers (`«...»`), rejecting malformed or non-inline definitions fail-closed.
   - Implements `reconcile_obligation_coverage` and `reconcile_lean_mir_coverage`, which return `CoverageVerdict::Verified` if and only if the census succeeds without unsupported constructs, every censused `FaultSite` is present in the discharged obligation set (`census ⊆ discharged`), and every censused `MirFaultClass` has `PropertyStatus::EmittedAndVerified` in `PropertyRegistry`.
   - Validates all **4 False-Proof Mutation Probes** (`CallArgBlindProbe`, `SwitchBreakStripProbe`, `LoopUpdateOverflowProbe`, `DerefAliasProbe`), the `PropertyRegistry` unemitted-class downgrade probe, and a **Cross-Language Lean-to-Rust Witness Parity Test** (`include_str!("../../../theory/Anneal/FaultSiteCensusPrototype.lean")`).

---

## 2. Lean 4 Machine-Checked Theorem Inventory (`theory/Anneal/FaultSiteCensusPrototype.lean`)

All declarations in `theory/Anneal/FaultSiteCensusPrototype.lean` elaborate in the Lean 4 kernel with **zero `sorryAx`** and **zero `Lean.ofReduceBool` (`native_decide`)** (verified over standard axioms `propext`, `Quot.sound`, and `Classical.choice` only).

| Category | Declaration Name | Statement Summary |
| :--- | :--- | :--- |
| **Taxonomy & Canonical Encoding** | `MirFaultClass.mem_all` | Every `c : MirFaultClass` is a member of the 12-element canonical list `MirFaultClass.all`. |
| | `MirFaultClass.nodup_all` | `MirFaultClass.all` is duplicate-free (`List.Nodup`). |
| | `MirFaultClass.ofRank?_toRank` / `toRank_ofRank?` | Exact bijection between `MirFaultClass` and canonical ranks `0..11`. |
| | `MirFaultClass.toRank_injective` | `toRank` is injective. |
| | `MirFaultClass.fromStr?_asStr` / `asStr_fromStr?` / `asStr_injective` | Exact round-trip and injectivity for canonical snake_case identifiers (`arith_overflow`, ..., `unreachable_terminator`). |
| **Deduplication & Structural Nodup** | `mem_dedupFaultClasses` | `c ∈ dedupFaultClasses raw ↔ c ∈ raw`. |
| | `nodup_dedupFaultClasses` | `dedupFaultClasses raw` is strictly duplicate-free in canonical rank order. |
| | `censusStmtFaultSites_nodup` / `censusTerminatorFaultSites_nodup` | Per-statement and per-terminator fault-site lists are duplicate-free. |
| | `censusMirBodyFaultSites_nodup` | For every `body : CapturedMir`, `(censusMirBodyFaultSites body).Nodup`. |
| | `mem_censusMirBodyFaultSites_stmt` / `mem_censusMirBodyFaultSites_term` | Exact structural membership characterizations connecting `(bbIdx, stmtIdx, cls) ∈ censusMirBodyFaultSites body` to `get? body.basicBlocks bbIdx` and `get? bb.statements stmtIdx` or `stmtIdx = length bb.statements`. |
| **Construct Precision & Non-Overapproximation** | `censusStmtFaultClasses_nop` / `_coverage` / `_constEvalCounter` / `_backwardIncompatibleDropHint` | Pure no-fault statements emit `[]` (0 classes). |
| | `evalStmt_nop_ne_ub` / `_coverage_ne_ub` / `_constEvalCounter_ne_ub` / `_backwardIncompatibleDropHint_ne_ub` | Pure no-fault statements never evaluate to `MirStepNode.fail .ub`. |
| | `censusTerminatorFaultClasses_goto_inBounds` / `_unwindTerminate` / `_inlineAsm` | Pure no-fault terminators emit `[]` (0 classes). |
| | `evalTerminator_goto_ne_ub` / `_unwindTerminate_ne_ub` / `_inlineAsm_ne_ub` | Pure no-fault terminators never evaluate to `MirStepNode.fail .ub`. |
| | `censusStmtFaultClasses_storageLive` / `_storageDead` | `.storageLive` and `.storageDead` emit strictly `[.boundsCheck, .storageLiveProtected]` (2 of 12 classes). |
| | `censusStmtFaultClasses_intrinsic_assume` | `.intrinsic (.assume (.copy { localIdx := l, projection := [] }))` emits strictly `[.boundsCheck, .scalarNicheInvalid, .uninitRead]` (3 of 12 classes). |
| | `censusTerminatorFaultClasses_unreachable` | `.unreachable` emits strictly `[.unreachableTerminator]` (1 of 12 classes). |
| | `censusTerminatorFaultClasses_return` | `.return_` emits strictly `[.treeBorrowsViolation, .uninitRead, .callAbiMismatch]` (3 of 12 classes). |
| | `censusStmtFaultClasses_not_all_twelve` | Witness proof that `censusStmtFaultClasses` is strictly narrower than `MirFaultClass.all`. |
| **Valid PC & CFG Target-Bounds Invariance** | `validMirPc_iff` | Decidable reflection `validMirPcDec body frame = true ↔ ValidMirPc body frame`. |
| | `validMirPc_initMachineState` | If `length body.basicBlocks > 0`, `ValidMirPc body (initMachineState body args).frame`. |
| | `stepMirFn_preserves_validMirPc` | If `s.memory.activeCallee = none`, `s.memory.callStack = []`, `cfgTargetsInBounds body = true`, and `ValidMirPc body s.frame`, then any intra-frame step (`MirStepNode.step s'` or `MirStepNode.emitStep obs s'`) preserves `ValidMirPc body s'.frame`. |
| **Fine-Grained Construct Soundness** | `evalStmt_ub_implies_mem_censusStmt` | If `evalStmt activeBody s stmt = MirStepNode.fail .ub`, then `∃ cls ∈ censusStmtFaultClasses stmt, True` with construct-specific class witnesses. |
| | `evalTerminator_ub_implies_mem_censusTerminator` | If `evalTerminator activeBody s term = MirStepNode.fail .ub`, then `∃ cls ∈ censusTerminatorFaultClasses (length activeBody.basicBlocks) term, True` with construct-specific class witnesses. |
| **Fault-Site Census Completeness** | `stepMirFn_activeBody_fault_in_census` | For any `body : CapturedMir` and `s : MachineState` with `ValidMirPc (s.memory.activeCallee.getD body) s.frame`, `stepMirFn body s = MirStepNode.fail .ub → ∃ cls, (s.frame.blockIdx, s.frame.stmtIdx, cls) ∈ censusMirBodyFaultSites (s.memory.activeCallee.getD body)`. |
| | `stepMirFn_fault_in_census` | Top-level specialization (`s.memory.activeCallee = none`): `ValidMirPc body s.frame → stepMirFn body s = MirStepNode.fail .ub → ∃ cls, (s.frame.blockIdx, s.frame.stmtIdx, cls) ∈ censusMirBodyFaultSites body`. |
| | `stepMirFn_ne_ub_of_site_uncensused` | Contrapositive safety corollary: if no `(s.frame.blockIdx, s.frame.stmtIdx, cls)` is in `censusMirBodyFaultSites body`, then `stepMirFn body s ≠ MirStepNode.fail .ub`. |
| | `stepMirFn_ne_ub_of_empty_census` | Whole-body zero-census corollary: if `censusMirBodyFaultSites body = []`, `stepMirFn body s ≠ MirStepNode.fail .ub` at every valid PC. |
| **Fail-Closed Reconciler & Registry Soundness** | `reconcileFaultCoverage_verified_iff` | `reconcileFaultCoverage census discharged = .verified ↔ ∀ site ∈ census, site ∈ discharged`. |
| | `reconcileFaultCoverage_unknown_nonempty` | When `reconcileFaultCoverage census discharged = .unknownUnmappedFaultSites missing`, `missing ≠ []` and `∀ site, site ∈ missing ↔ site ∈ census ∧ site ∉ discharged`. |
| | `reconcileFaultCoverageWithRegistry_verified_iff` | Registry-gated reconciliation returns `.verified` iff every site in `census` is in `discharged` AND has `registry site.faultClass = .emittedAndVerified`. |
| | `reconcileFaultCoverageWithRegistry_rejects_unemitted` | If `site ∈ census` and `registry site.faultClass ≠ .emittedAndVerified`, reconciliation never returns `.verified` (even if `site ∈ discharged`). |
| | `reconcileFaultCoverage_mutation_detected` | Stripping any `site ∈ census` from `discharged'` forces `.unknownUnmappedFaultSites missing` with `site ∈ missing`. |
| | `stepMirFn_fault_in_discharged_of_reconciled` | End-to-end bridge: if `reconcileFaultCoverageWithRegistry registry (censusMirBodyFaultSites body) discharged = .verified`, any runtime `.ub` fault in `stepMirFn body s` occurs at a site `(bb, stmt, cls) ∈ discharged` with `registry cls = .emittedAndVerified`. |

---

## 3. Construct-to-Fault-Class Matrix (`Trusted.MirSemantics` Alignment)

Every syntactic construct in `Trusted.MirAst` is mapped to the exact subset of `MirFaultClass` categories that its operational evaluation in `Trusted.MirSemantics` (`Places.lean`, `Statements.lean`, `Terminators.lean`, `Machine.lean`) can trigger:

| Syntactic Construct | Emitted `MirFaultClass` Subset (in Canonical Rank Order) | Semantic Justification in `Trusted.MirSemantics` |
| :--- | :--- | :--- |
| **Place Projection (`ProjectionElem`)** | | |
| `.deref` | `boundsCheck`, `ptrDerefInvalid`, `ptrAlignMismatch`, `treeBorrowsViolation`, `scalarNicheInvalid`, `uninitRead` | Reads pointer local (`evalPlace` $\rightarrow$ `boundsCheck`, `scalarNicheInvalid`, `uninitRead`), validates pointer provenance/bounds/alignment (`ptrDerefInvalid`, `ptrAlignMismatch`), and checks Tree Borrows read/write access (`treeBorrowsViolation`). |
| `.field idx` / `.downcast idx` / `.subslice f t fl` | `boundsCheck` | Sub-place layout / field / slice bounds resolution in `evalPlace` / `resolvePlaceRef`. |
| `.index idxLocal` | `boundsCheck`, `scalarNicheInvalid`, `uninitRead` | Reads `idxLocal` (`uninitRead`, `scalarNicheInvalid`) and checks array/slice index bounds (`boundsCheck`). |
| `.constantIndex offset minLen fromEnd` | `boundsCheck` | Checks constant index against `minLen` and slice/array length (`boundsCheck`). |
| `.opaqueCast` / `.unwrapUnsafeBinder` | `boundsCheck`, `scalarNicheInvalid` | Validates layout/niche compatibility at cast/unwrap boundary. |
| **Operand (`Operand`)** | | |
| `.copy place` / `.move place` | `censusPlaceReadFaultClasses place` (`boundsCheck`, `scalarNicheInvalid`, `uninitRead` + projection classes) | `evalOperand` evaluates `evalPlace` (`uninitRead`, `scalarNicheInvalid`, `boundsCheck`); `.move` also deinitializes the source place (`writePlaceRaw` $\rightarrow$ `treeBorrowsViolation` if deref). |
| `.constant c` where `c.kind = .zeroSized \| .scalar _ \| .slice _ \| .unevaluated _` | `[]` (0 classes) | Pure immediate constant in `evalConstOperand`; cannot fail with `.ub`. |
| `.constant c` where `c.kind = .indirect allocId offset` | `boundsCheck`, `scalarNicheInvalid`, `uninitRead` | Reads constant bytes from global memory allocation `allocId` at `offset` (`readGlobalAllocBytes`). |
| **Rvalue (`Rvalue`)** | | |
| `.use op` | `Operand` classes | Direct operand evaluation. |
| `.BinaryOp (.add \| .sub \| .mul \| .cmp)` | `Operand` classes | Wrapping arithmetic / comparison; only operand evaluation can fault. |
| `.BinaryOp (.addUnchecked \| .subUnchecked \| .mulUnchecked)` | `arithOverflow` + `Operand` classes | Unchecked signed/unsigned arithmetic faults on overflow (`evalBinOp`). |
| `.BinaryOp (.addWithOverflow \| .subWithOverflow \| .mulWithOverflow)` | `boundsCheck` + `Operand` classes | Checked arithmetic constructs tuple aggregate using destination layout (`boundsCheck`). |
| `.BinaryOp (.div \| .rem)` | `arithOverflow`, `divRemByZero` + `Operand` classes | Faults on divisor `== 0` (`divRemByZero`) or signed `MIN / -1` (`arithOverflow`). |
| `.BinaryOp (.shl \| .shr \| .shlUnchecked \| .shrUnchecked)` | `shiftOverflow` + `Operand` classes | Faults when shift amount $\ge$ bit width or negative (`shiftOverflow`). |
| `.BinaryOp (.offset)` | `boundsCheck`, `ptrDerefInvalid` + `Operand` classes | `inbounds` pointer offset arithmetic (`evalPtrOffset`). |
| `.UnaryOp .neg` | `arithOverflow` + `Operand` classes | Signed negation of `Int.min` faults (`arithOverflow`). |
| `.UnaryOp (.not \| .ptrMetadata)` | `Operand` classes | Bitwise complement / metadata extraction; only operand evaluation can fault. |
| `.NullaryOp .ubChecks` / `.discriminant p` / `.len p` / `.ref _ _ p` / `.addressOf _ p` / `.copyForDeref p` | Place / layout classes (`boundsCheck`, `treeBorrowsViolation`, `scalarNicheInvalid`, `uninitRead`) | Place resolution, discriminant read, or borrow creation. |
| `.cast kind op` / `.repeat op _ _` / `.shallowInitBox op` / `.aggregate kind ops` / `.wrapUnsafeBinder op` | `boundsCheck`, `ptrDerefInvalid`, `scalarNicheInvalid` + `Operand` classes | Layout resolution, scalar niche validation, or box header validation. |
| **Statement (`StatementKind`)** | | |
| `.nop` / `.coverage` / `.constEvalCounter` / `.backwardIncompatibleDropHint _` | `[]` (0 classes) | Pure operational step (`MirStepNode.step s.advanceStmt`); proven never to return `.ub`. |
| `.storageLive loc` / `.storageDead loc` | `boundsCheck`, `storageLiveProtected` | Faults iff `loc >= length s.frame.locals` (`boundsCheck`) or `hasProtectedLocalBorrow s.memory s.frame.frameId loc` holds (`storageLiveProtected`). |
| `.assign lhs rhs` | `PlaceWrite(lhs)` $\cup$ `Rvalue(rhs)` $\cup$ `{boundsCheck, scalarNicheInvalid}` | Evaluates `rhs`, validates destination layout/niche, and writes to `lhs`. |
| `.setDiscriminant place _ _` / `.deinit place` | `PlaceWrite(place)` $\cup$ `{boundsCheck}` | Resolves destination place and updates discriminant/initialization state. |
| `.retag kind place` | `PlaceRead(place)` $\cup$ `PlaceWrite(place)` $\cup$ `{boundsCheck, ptrDerefInvalid, ptrAlignMismatch, treeBorrowsViolation}` | Resolves pointer in `place`, validates alignment/bounds if Box/Ref, and performs Tree Borrows retag (`retagPlace`). |
| `.placeMention place` | `PlaceRef(place)` $\cup$ `{boundsCheck}` | Evaluates place projection without reading value bytes (`evalPlaceRef`). |
| `.intrinsic (.assume op)` | `Operand(op)` $\cup$ `{scalarNicheInvalid}` | Evaluates boolean operand and faults if false (`b = false`) or non-boolean (`scalarNicheInvalid`). |
| `.intrinsic (.copyNonOverlapping src dst count)` | `Operand(src, dst, count)` $\cup$ `{arithOverflow, boundsCheck, ptrDerefInvalid, ptrAlignMismatch, treeBorrowsViolation, uninitRead}` | Validates `count * size` overflow, alignment, non-overlap, source/dest allocation bounds, and Tree Borrows permissions. |
| **Terminator (`TerminatorKind`)** | | |
| `.goto target` (with `target < numBlocks`) | `[]` (0 classes) | Unconditional jump to valid basic block; proven never to return `.ub`. |
| `.goto target` (with `target >= numBlocks`) | `boundsCheck` | Out-of-bounds target causes next step's `get? basicBlocks blockIdx` to fault. |
| `.unwindTerminate` / `.inlineAsm` | `[]` (0 classes) | Terminates with `.panic` or `.unsupported`, never `.ub`. |
| `.unreachable` | `unreachableTerminator` | Always returns `MirStepNode.fail .ub`. |
| `.switchInt discr targets otherwise` | `Operand(discr)` $\cup$ `{boundsCheck, scalarNicheInvalid}` | Evaluates discriminant operand (`uninitRead`, `scalarNicheInvalid`, `boundsCheck`) and branches. |
| `.return_` | `treeBorrowsViolation`, `uninitRead`, `callAbiMismatch` | Reads `_0` (`uninitRead`), checks non-diverging caller ABI (`callAbiMismatch`), and writes `caller.destination` (`treeBorrowsViolation`). |
| `.drop place target` / `.assert cond expected target` | Place / Operand classes $\cup$ `{boundsCheck, treeBorrowsViolation, scalarNicheInvalid}` | Validates place/condition before branching or panicking. |
| `.call func args dest target` / `.tailCall func args` | `Operand(func, args)` $\cup$ `PlaceWrite(dest)` $\cup$ `{boundsCheck, ptrDerefInvalid, ptrAlignMismatch, treeBorrowsViolation, scalarNicheInvalid, uninitRead, storageLiveProtected, callAbiMismatch}` | Evaluates callee and argument operands, validates ABI/signature/intrinsic preconditions (`callAbiMismatch`), and writes destination place. |

---

## 4. False-Proof Mutation Probe Results

All four false-proof mutation probes required by the design specification (plus the `PropertyRegistry` un-emitted class probe) are implemented in both Lean 4 (`by decide` compile-time kernel witnesses) and Rust (`FaultMutationProbe::run_all_false_proof_probes()`):

| Probe | Simulated `obligations.rs` Bug | Baseline Verdict | Mutant Verdict | Missing Fault Sites Pinpointed |
| :--- | :--- | :--- | :--- | :--- |
| **`CallArgBlindProbe`** | Obligation emitter ignores `TerminatorKind::Call` argument / ABI preconditions at `(bb=0, stmt=1)`. | `Verified` | `UnknownUnmappedFaultSite` | `(0, 1, bounds_check)`, `(0, 1, ptr_deref_invalid)`, `(0, 1, ptr_align_mismatch)`, `(0, 1, tree_borrows_violation)`, `(0, 1, scalar_niche_invalid)`, `(0, 1, uninit_read)`, `(0, 1, storage_live_protected)`, `(0, 1, call_abi_mismatch)` |
| **`SwitchBreakStripProbe`** | Emitter strips the `otherwise` arm of a `SwitchInt` terminator, omitting `bb2` (which contains an unchecked addition at `(bb=2, stmt=0)`). | `Verified` | `UnknownUnmappedFaultSite` | `(2, 0, arith_overflow)`, `(2, 0, bounds_check)`, `(2, 0, scalar_niche_invalid)`, `(2, 0, uninit_read)` |
| **`LoopUpdateOverflowProbe`** | Emitter verifies loop header (`bb1`) and body (`bb2`) but drops the back-edge latch increment overflow check at `(bb=3, stmt=0)`. | `Verified` | `UnknownUnmappedFaultSite` | `(3, 0, arith_overflow)` |
| **`DerefAliasProbe`** | Emitter discharges local bounds and initialization at a `*ptr` deref assignment + `.retag` (`bb=0, stmt=0..1`) but omits pointer validity, alignment, and Tree Borrows permissions. | `Verified` | `UnknownUnmappedFaultSite` | `(0, 0, ptr_deref_invalid)`, `(0, 0, ptr_align_mismatch)`, `(0, 0, tree_borrows_violation)`, `(0, 1, ptr_deref_invalid)`, `(0, 1, ptr_align_mismatch)`, `(0, 1, tree_borrows_violation)` |
| **`PropertyRegistryUnemittedProbe`** | Emitter claims all sites are discharged, but `PropertyRegistry` marks `tree_borrows_violation` as `UnemittedGap` (or `UnsupportedFailClosed`). | `Verified` (under full registry) | `UnknownUnmappedFaultSite` | Pinpoints `unemitted_classes: [TreeBorrowsViolation]` and all sites requiring `tree_borrows_violation`. |

---

## 5. Edge Cases, Lexer Traps & Semantic Subtleties Resolved

1. **Out-of-Bounds `ValidMirPc` vs. `stepMirFn` Block Lookup**:
   - In `Trusted.MirSemantics.stepMirFn`, if `get? activeBody.basicBlocks s.frame.blockIdx = none` or `s.frame.stmtIdx > length bb.statements`, `stepMirFn` returns `MirStepNode.fail .ub`.
   - Because an out-of-bounds PC does not correspond to any syntactic block in `activeBody.basicBlocks`, `stepMirFn_fault_in_census` requires `ValidMirPc activeBody s.frame` (`∃ bb, get? activeBody.basicBlocks s.frame.blockIdx = some bb ∧ s.frame.stmtIdx ≤ length bb.statements`), paired with `validMirPc_initMachineState` and `stepMirFn_preserves_validMirPc` (plus static `.goto target` / `.switchInt` / `.drop` / `.assert` / `.call` target-bounds checking in `censusTerminatorFaultClasses`).
2. **`.return_` Subtle UB Edges in `Trusted.MirSemantics.evalTerminator`**:
   - Unlike a naive model where `return` is pure, `Trusted.MirSemantics.evalTerminator` on `.return_` reads `_0` (`get? s.frame.locals 0`, faulting with `.ub` if `_0` is uninitialized or missing) and, when `s.memory.callStack` is non-empty, faults with `.ub` if `caller.isDiverging = true` or if writing the return value to `caller.destination` fails (`writePlaceValue`, which can trigger `treeBorrowsViolation` when `caller.destination` has a `.deref` projection). Our census accurately emits `[.treeBorrowsViolation, .uninitRead, .callAbiMismatch]` for `.return_`.
3. **`.constant` Immediate vs. `.indirect` Global Allocation Reads**:
   - `ConstOperandKind.zeroSized`, `.scalar`, `.slice`, and `.unevaluated` evaluate purely in `evalConstOperand`, whereas `.indirect allocId offset` calls `readGlobalAllocBytes` and can fault with `.ub` if `allocId` is missing, out of bounds, or contains uninitialized bytes. Our census inspects `c.kind` so immediate constants emit `[]` while `.indirect` constants emit `[.boundsCheck, .scalarNicheInvalid, .uninitRead]`.
4. **Fail-Closed `.lean` Lexer & Recursive-Descent Parser (`census_lean_mir_module`)**:
   - `census_lean_mir_module` uses a full Lean 4 lexical scanner that strips `--` line comments and arbitrarily nested `/- ... -/` block comments, skips string literals (`"..."`), raw string literals (`r#"..."#`), and interpolated string literals (`s!"..."`), and unwraps `«...»` guillemet identifiers.
   - Any unrecognized statement/terminator/rvalue/projection constructor, missing `basicBlocks` field, or non-inline helper reference fails closed with `CensusScanError` $\rightarrow$ `CoverageVerdict::UnknownUnmappedFaultSite` rather than silently omitting fault sites.

---

## 6. Verification Receipts

All verification commands pass from the repository root with concurrency $W = 1$:

1. **Rust Unit, Mutation Probe & Cross-Language Parity Tests**:
   ```bash
   cargo test --manifest-path crates/cargo-anneal/Cargo.toml --lib fault_census_proto
   cargo test --manifest-path crates/cargo-anneal/Cargo.toml fault_census_proto
   ```
2. **Lean 4 Kernel Typechecking & Compile-Time `by decide` Witnesses**:
   ```bash
   (cd examples && anneal-lean-run --mode file --concurrency 1 -- lake env lean ../theory/Anneal/FaultSiteCensusPrototype.lean)
   ```
3. **Structural Proof-Health Linter (`0` Findings)**:
   ```bash
   python3 tools/anneal-lsp/server/proof_health.py theory/Anneal/FaultSiteCensusPrototype.lean
   ```
4. **Kernel Axiom Audit**:
   - Verified via `#print axioms` across all 84 theorems and witnesses in `theory/Anneal/FaultSiteCensusPrototype.lean`: only standard axioms (`propext`, `Quot.sound`, `Classical.choice`) are used (`0` `sorryAx`, `0` `Lean.ofReduceBool`, `77/84` declarations completely `Classical.choice`-free).

---

## 7. Integration Architecture for Track A (`ws-fault-site-coverage-reconciler`)

To graduate this prototype into the production Track A workstream `ws-fault-site-coverage-reconciler` on `unstable`:

1. **Promote `FaultSiteCensusPrototype.lean` into `theory/Anneal/FaultSiteCensus.lean`**:
   - Import `Anneal.FaultSiteCensus` in `theory/Anneal.lean` (updating `trusted/audit/check_trusted.py`'s pinned `theory/Anneal.lean` import list in a coordinated Track A commit).
2. **Wire `PropertyRegistry` and `census_ir_captured_mir` into `crates/cargo-anneal/src/obligations.rs` & `verify.rs`**:
   - Tag every emitted proof obligation in `obligations.rs` with its covered `Vec<FaultSite>`.
   - During `cargo anneal verify` / `agent-verify`, run `census_ir_captured_mir(&captured_mir)` (and cross-check `census_lean_mir_def` on the generated `Mir/<Item>.lean` artifact) against the discharged obligation `FaultSite` set using `PropertyRegistry::stage_default()`.
   - Gate the `[VERIFIED]` badge on `CoverageVerdict::Verified`; if any site is unmapped or uses an un-emitted `MirFaultClass`, downgrade the item verdict fail-closed to `UNKNOWN(UNSUPPORTED_CONSTRUCT)` with the exact `(bbIdx, stmtIdx, faultClass)` diagnostic list.
