# Six-Vector `.olean` / Kernel / Interpreter Tamper Fixtures & Reproduction Suite

Deterministic Lean 4.34.1 fixture sources, binary `.olean`/`.ir` compacted-region
mutators, and live BEFORE/AFTER reproduction tests for:

- **V-Q1 (`forgedQuotInfo`)**: Unvalidated `.quotInfo` payloads in `OleanEnvAuditor.lean`
  and `Lean.Kernel.Environment.Replay.replayConstant` (`Replay.lean:129-133`), including
  forged non-canonical name, forged non-`Init.Prelude` origin, forged `QuotKind`, forged
  `levelParams`, and forged `False` type.
- **V-M2 (`forgedExprMData`, `forgedLevelMData`, `forgedNameHash`)**: Forged cached
  metadata bits (`Expr.Data`, `Level.Data`, `Name.hash`) inside real compiled `.olean`
  compacted regions, including clearing `hasFVar`/`hasExprMVar`/`hasLevelMVar`/`looseBVarRange`
  to fool `OleanEnvAuditor.isClosedExpr`, corrupting `approxDepth`/`hash`/`Level.m_data`/
  `Name.hash` to bypass current `OleanEnvAuditor.lean`, and a duplicate-subterm
  `Expr.beq` cache-poisoning regression test.
- **V-U3 (`invalidUtf8Literal`)**: Real compiled `.olean` binaries patched with malformed
  UTF-8 payloads (`ED A0 80` lone surrogate, `E2 82` truncated multi-byte, `C0 80` / `C0 AF`
  overlong encodings, `FF` invalid lead byte, `80` unexpected continuation, embedded NUL,
  mismatched `lean_string_object.m_length`, and malformed `Name.str` UTF-8) proving
  `importModules` and current `OleanEnvAuditor.lean` accept them while the prototype
  validator rejects every case.
- **V-F4 (`kernelFreshCollision`, `lean4#16767`)**: Live Lean 4.34.1 `Kernel.isDefEq`,
  `Kernel.check`, and `Kernel.whnf` capture witnesses using `_kernel_fresh.0` in
  `LocalContext`, plus compiled `.olean` tests with `_kernel_fresh` declaration names
  and binder names.
- **V-S5 (`forbiddenExportAttr`)**: Live Lean 4.34.1 `@[export]` C-symbol binding across
  non-`module` `.olean`, `module` `.olean`/`.olean.private`/`.ir`, forged `.ir` `Lean.exportAttr`
  entry evading `OleanEnvAuditor.lean:1649`'s `getModuleEntries`-only scan, live
  `exportAttr.ext.getState`, `TrustedBoundary.lean`'s compiled-audit gap, and unannotated
  `main` C-symbol exposure.
- **V-N6 (`nanodaNatXorPropextMismatch`, `lean4#16831`)**: Live Lean 4.34.1 axiom closure
  audit of `Nat.xor`, `Nat.bitwise`, `Anneal.NatBitwise` (current `[propext, Quot.sound]`
  status of `unfold_eq` alongside `[]` and `[propext]` theorems, plus post-`zerocopy#4444`
  regime), and second-kernel `primitiveTargets` export-closure parity oracle (`zerocopy#4488`).

## Adversarial Hardening Regressions (Round B1)

`tests/mir/OleanQuotMdataUtf8ProtoTests.lean` Section 11b pins bypasses reproduced live
against the initial validator (each forged artifact was previously reported `ok`):

- **V-F4**: `lean4#16767` capture with an EMPTY `LocalContext` (undeclared
  `_kernel_fresh.0` fvar in the query expression) and with an aliased
  `fvarIdToDecl` key; closed by `validateKernelQuery` (`undeclaredFVar`) and
  map/array-consistent `validateLocalContext` (`malformedLocalContext`).
- **V-Q1 / extra constants**: `constNames[i] ↦ constants[i]` name aliasing and length
  mismatch (`constNameAliasMismatch`), and theorem-over-axiom replacement via
  `importModules` subsumption that launders axioms out of every closure audit
  (`shadowedConstant`).
- **V-U3**: invalid UTF-8 smuggled through `MData` `DataValue.ofSyntax`, including a
  `reprStr` cache-key collision; closed by typed binary/in-memory `Syntax` traversal and
  an injective `syntaxStrictKey`.
- **Binary region**: non-canonical `LeanMPZ` Nats, out-of-range enum/`Bool` scalar
  discriminants (e.g. `DefinitionVal.safety = 7`), unchecked `DataValue` arities, and
  forged `ModuleData.imports` name hashes.

## Adversarial Hardening Regressions (Round A1)

`tests/mir/OleanQuotMdataUtf8ProtoTests.lean` Section 11c and `test_six_vectors.py` pin
bypasses reproduced live against Round B1:

- **V-N6 / Shadowing**: theorem-over-theorem axiom laundering (a later module replacing an
  axiom-dependent theorem with a cyclic self-proof of the same type bypassed
  `benignTheoremDuplicate`) and intra-module duplicate `constNames` (bypassed binary
  validation); closed by `safeReservedTheoremDuplicate` (requiring `isReservedName`,
  non-circularity, and identical `StrictExprKey` dependency closure) plus intra-part /
  intra-module duplicate rejection (`shadowedConstant`).
- **V-S5 / IR-extern**: `IR.Decl.extern` C-symbol stubs and `Lean.externAttr` /
  `implementedByAttr` / `regularInitAttr` / `builtinInitAttr` entries in `.olean` or `.ir`
  with zero `exportAttr`; closed in both binary and in-memory validators
  (`forbiddenExportAttr`).
- **V-U3 / Syntax & Entries**: exponential DoS on unmemoized `validateSyntaxDag` /
  `syntaxStrictKey` (closed via `withPtrEq` `strictSyntaxEq` and `StrictSyntaxKey` DAG
  memoization, verified on a depth-35 shared `Syntax` DAG), cyclic binary `Syntax` bypassing
  a 1-color `seen` set (closed via 3-color DFS), malformed UTF-8 / `LeanClosure` (tag 245)
  hidden inside non-`exportAttr` `ModuleData.entries` such as `Lean.docStringExt` (closed
  via `sweepBinRegionGraph`), and a safe subprocess witness confirming truncated UTF-8
  (`E2 82`) triggers `SIGSEGV` in Lean 4.34.1 `reprStr` after `importModules`.
- **V-F4 / Kernel Query & Binary Bounds**: full `strictLocalDeclEq` (`binderInfo`, `nonDep`,
  `kind`), telescopic `LocalContext` `fvar` scoping & slot-index checks, loose `bvar`/`mvar`
  rejection (`malformedKernelQuery`) and `fuel` propagation in `validateKernelQuery`,
  truncated `ReducibilityHints.regular` `cs_sz` + `LeanMPZ` `_mp_alloc` bounds, and
  independent `.olean*` / `.ir*` compacted-region validation (`validateModuleArtifactParts`).

## Adversarial Hardening Regressions (Round B2)

- **V-N6 / forged axiom cache**: Lean 4.34.1 `#print axioms` / `collectAxioms` never
  traverses imported declarations; it trusts the per-declaration axiom arrays stored in each
  `.olean`'s private `exportedAxiomsExt` entries. Emptying those arrays makes `#print axioms`
  report "does not depend on any axioms" for `useEvil : False := evilAx` and for an honestly
  compiled downstream `theorem downstream : 1 = 2` (live witness in `test_six_vectors.py`).
  Closed by `validateExportedAxiomCache` / `validateEnvModuleFull`, which recompute closures
  from kernel constants (`independentAxiomClosures`) and reject caches that omit axioms
  (`forgedExportedAxioms`).
- **V-U3 / Syntax DoS**: the shallow-hash `StrictSyntaxKey` cache collapsed every node of an
  honest `Syntax` chain into one bucket (cubic time: 160 nodes took 1.5 s); replaced by a
  linear fuel-charged tree walk (fail-closed on oversize / exponential DAGs), an iterative
  byte-injective `ofSyntax` key, and an `MData`-aware `StrictExprKey` hash.

## Adversarial Hardening Regressions (Round A2)

`tests/mir/OleanQuotMdataUtf8ProtoTests.lean` Section 11e pins bypasses reproduced live
against Round B2:

- **V-N6 / Tarjan SCC & `.recInfo` axiom closure**: B2's `independentAxiomClosures`
  permanently cached `#[]` sentinel results on mutual-recursion back-edges (`cycB <-> cycC`,
  accepting a forged empty cache for `cycC`) and omitted `.recInfo.rules` (`r.rhs`) and
  `.ctorInfo.induct`; replaced by iterative Tarjan SCC covering every `ConstantInfo` field,
  plus strict `binExportedAxiomClaims` ctor/name validation across both `.olean*` and `.ir*`,
  and duplicate / foreign-owned `exportedAxiomsExt` entry rejection (`forgedExportedAxioms`).
- **V-U3 / Fail-closed `ofSyntax` equality & O(1) hashing**: B2's `syntaxStrictKey`
  truncation made distinct `>100k`-node `Syntax` chains compare equal (`0xFF == 0xFF`) and
  allocated full byte arrays inside `Hashable.hash`; replaced by fail-closed iterative
  lockstep `strictSyntaxEqIter` (`withPtrEq` fast-path) and bounded-budget
  `syntaxBoundedFingerprint`.

## Adversarial Hardening Regressions (Round B3)

- **V-N6 / module-system false positive**: `module` files store the same `.uniform`
  `exportedAxiomsExt` cache in `.olean`, `.olean.server` and `.olean.private`; the
  round-A2 "any duplicate claim" rule rejected every honest module-system file. Only
  conflicting duplicates are now flagged (every copy is still checked against the
  independent closure).
- **V-U3 / exponential equality**: the round-A2 recursive fallback of
  `strictSyntaxEqIter` re-expanded shared sub-DAGs once per path when the two sides are
  distinct objects (two distinct depth-24 DAGs did not finish within 170 s). Past the
  budget the bounded equality now returns `true`, which is sound because any `Syntax` that
  large already fails validation closed (`auditFuelExhausted`).

## Adversarial Hardening Regressions (Round A3)

`tests/mir/OleanQuotMdataUtf8ProtoTests.lean` Section 11g pins bypasses reproduced live
against Round B3:

- **V-N6 / module deleted `exportedAxiomsExt`**: deleting `exportedAxiomsExt` from part 0
  (`.olean`) of a `module` causes downstream `module` `#print axioms useEvil` to hide
  `evilAx` behind `[useEvil]` while B3 returned `ok=true` (because `.olean.server`/`.private`
  still had claims, or all-empty claims yielded 0 iterations). Closed by per-part decoding
  (`binExportedAxiomClaimsPerPart` / `validateExportedAxiomCachePerPart`) enforcing part-0
  completeness for non-empty axiom closures and zero intra-part duplicates.
- **Multi-part forward pointers**: `validateOleanPartsEx` and `binExportedAxiomClaimsPerPart`
  now restrict part `pIdx` pointer resolution to `parts[0..pIdx]`, rejecting dangling forward
  pointers from `.olean` into `.olean.server`/`.olean.private` (`malformedOleanRegion`).
- **V-S5 / foreign `IR.Decl` hijacking & compiler overrides**: rejects `IR.Decl` entries whose
  `FunId` is not owned by `modName` (`constNames ∪ extraConstNames`) or duplicated within a
  table (`forgedIrDecl`), and audits `CSimp.ext` / `passManagerExt` / `folderExt` across both
  `.olean` and `.ir` (`forbiddenExportAttr`).
- **V-M2 / universe-parameter scoping**: rejects duplicate `levelParams` and unbound
  `Level.param` references in both binary and in-memory validators (`forgedLevelMData`).

## Running the Suite

```bash
anneal-lean-run --mode build -- python3 -B -m unittest discover \
  -s tests/audit_tamper_fixtures/quot_mdata_utf8_proto -p 'test_*.py' -v
```
