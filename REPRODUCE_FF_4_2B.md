<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction & Status Report: FF-4.2b (`adv/ff-4-2b`)

Work unit `FF-4.2b` merges `sup/brief-4` (`087b015b`: BRIEF-0..4, the
`b2341426` pointer-offset semantics, `cargo-anneal`, `anneal-difftest`) into
`sup/ff-4` (`1642f8aa`: FF-1..FF-4.2, the fuel-free lifting theory and the
migrated `WireframeDemo`, `FrameTutor`, and `MirVerification` proofs).

> [!IMPORTANT]
> Status at `[adv B1]`: **100% GREEN** across all Rust tests (`56 passed`),
> `lake build Anneal MirVerification` (including `Anneal.MirLift`),
> `python3 trusted/audit/check_trusted.py --fast` (`PASS`, `40` Trusted modules,
> `9,589` Trusted kernel declarations, `24,294` replayed declarations), and
> both `cargo-anneal verify` suites (`wireframe-demo`: `9 unconditional`,
> `tutor`: `7 unconditional`, `Proof/WireframeDemo/*.lean` untouched at `1,421`
> LOC with zero `BlockCtx` and zero manual `fuel`).

## 1. Merge protocol

A naive `git merge 087b015b` would revert about 80 upstream files, because the
earlier merge `0d5f7b5b` on `sup/ff-4` recorded `bf7334d8` as a parent while
keeping an older tree. The two tips have three merge bases (`bf7334d8`,
`a07cdf2e`, `ab4b6bb7`). `[adv A0]` therefore ran:

```bash
git merge --no-commit --no-ff 087b015b   # records MERGE_HEAD = 087b015b
git read-tree -u --reset 087b015b        # index and tree = 087b015b exactly
git checkout 1642f8aa -- <FF-owned paths of Section 2.2>
# then wrote the three-way results of Section 2.3
```

## 2. Where each file comes from

### 2.1 From `087b015b` (everything not listed below)

This includes every file that `0d5f7b5b` had reverted on the FF side, for
example `FRAMEWORK_PRINCIPLES.md`, `docs/{architecture,design,trust-model}.md`,
`crates/{anneal-mir-instrument,anneal-trace}`, `skills/{skill-authorship,`
`trust-review}`, `REPRODUCE_BRIEF_*.md`, and all of `trusted/lean/` except
the two `Machine.lean` lines below. For each such file the FF tip's blob
equals an older merge-base blob, while `087b015b`'s blob is the newer one.

### 2.2 From `1642f8aa` (owned by FF-1..FF-4.2)

- `REPRODUCE_FF_*.md` (13 files).
- `skills/anneal-prove/SKILL.md` and
  `skills/anneal-prove/references/proof-scaling-and-bottlenecks.md`. The FF
  edits start from `ebe1fad0` (`d98d815d`), the same blob `087b015b` has.
- `theory/Anneal.lean` and `theory/Anneal/{MirFuelFree,MirLift,MirLiftBench,`
  `MirLiftCore,MirLoops,PureMirExec,Scalars,SepLogicLenses}.lean`.
- `examples/wireframe-demo/anneal/proofs/Proof/WireframeDemo/*.lean` and
  `examples/tutor/anneal/proofs/Proof/FrameTutor/*.lean`.
- `trusted/audit/check_trusted.py`: `087b015b`'s blob equals the merge-base
  blob `b37bba38`, so the FF blob is exactly "base plus the FF-1..4
  `DOWNSTREAM_TARGETS`" (`Anneal.Scalars` imports `["Trusted"]`, the six new
  modules, and `Anneal`'s import list).
- `trusted/lean/Trusted/Rustc/{V2026_06_01,V2026_08_01}/MirSemantics/`
  `Machine.lean`: `087b015b`'s file plus the one line
  `traitImpls := body.traitImpls` in `initMachineState`.
- `examples/mir/MirVerification.lean`: the FF file was derived from
  `087b015b`'s blob `ffb073df`, so it already keeps every `087b015b` example
  and adds the FF-4.2 `#mir_lift` / `#mir_lift_spec` migrations.

### 2.3 Three-way merged

- `theory/Anneal/Rustc/V2026_06_01/SymReflect.lean`: `git merge-file` with base
  `5cd697ae` (the FF parent of `1f33681e`), ours `1642f8aa`, theirs
  `087b015b`, clean. The result is `087b015b`'s file (with the
  `needsThinPtrElemResolution` changes) plus `1f33681e`'s
  `traitImpls`/`callees`/`callStack`/`activeCallee` fields in the
  `Memory` literals (needed by the `Machine.lean` line) and `a6aae5b8`'s
  `swap_le_u16_lane` and `*FuelFree` wrappers.
- `tests/mir/SymbolicEvalTests.lean`: base `5cd697ae`, clean. The result is
  `087b015b`'s file (with the `b2341426` regression proofs) plus
  `1f33681e`'s `simp <;> omega` in `reifyAndCallFnPtr_verified`.

## 3. What `087b015b` changes under the FF theory

| Trusted change in `087b015b` | Effect on FF theory |
| :--- | :--- |
| `evalRvalue (.len p)` calls `evalPlaceLen` | purity and `pushBaseStack` lemmas |
| `.cast .ptrToPtr` may call `deriveStackElemThinPtr` (reads and extends `mem.borrows`) | no longer memory-independent |
| pointer `BinOp.offset` calls `evalPtrOffsetBinOp` (reads `mem.borrows`) | no longer memory-independent |
| `.discriminant` calls `evalPlaceDiscriminant`, which checks the layout's variants | purity lemma; the `pureAdtMultiBlockBody` fixture |
| `.wrapUnsafeBinder op` evaluates like `.use op` | purity and `pushBaseStack` lemmas |
| `evalCopyNonOverlappingWithCount` gains two union branches | its `pushBaseStack` lemma |
| `evalTerminator` splits `.call` on the return block first, inlines both call branches, resolves `exact_div` signedness with `resolveIntrinsicIsSigned`, and steps Rust intrinsics directly through `evalDirectRustIntrinsic?` instead of emitting an external call | every proof that unfolds a call step |
| deref reads and writes go through `needsThinPtrElemResolution`, `resolveDerefWriteFullProj`, and `invalidateDerefWriteBorrows … callerLocals` | `SepLogicLenses` deref lemmas, `MirLiftCore` fast evaluators |

## 4. Proof adaptation

### 4.1 Done in `[adv A0]` (`theory/Anneal/PureMirExec.lean`)

- `isPureRvalue` now rejects `.cast .ptrToPtr` and `BinOp.offset` (new
  `isPureBinOp`); no example, theory body, or test uses either in a pure body.
- New lemmas `splitLastDeref?_eq_none_of_pure`, `evalPlaceRead_pure_eq`,
  `evalPlaceLen_pure_eq_withMem`, and `evalPlaceDiscriminant_eq_withMem`;
  `evalRvalue_pure_eq_withMem` handles `.len`, `.discriminant`, and
  `.wrapUnsafeBinder`.
- New `*_pushBaseStack` lemmas for `deriveStackElemThinPtr`,
  `evalUnsizeCoercion`, `evalSliceFatPtrDerefBorrow`,
  `evalGlobalThinPtrDerefBorrow`, `evalPtrOffsetBinOp`, `evalPlaceLen`, and
  `evalPlaceDiscriminant`, used by `evalReifyFnPointer_pushBaseStack` and
  `evalRvalue_pushBaseStack`.
- `evalCopyNonOverlappingWithCount_pushBaseStack`: the four restated copies of
  the body gain `087b015b`'s two union branches (`match (generalizing :=
  false)` keeps `h_wdv_eq` out of the motive).
- `pureModeEnumTy` now uses `layoutIdx := 1`, which has no layout entry.
  Index `0` aliased `u32Layout`, whose `.single 0` variants make every nonzero
  variant index UB under `evalPlaceDiscriminant`, so the arbitrary-variant
  theorem `pureAdtMultiBlock_pureConverges` was false. Statements unchanged.
- New `evalCallTerminatorB` and `evalTerminator_call_eq`
  (`cases targetOpt <;> rfl`): `evalTerminator` on a call, restated to resolve
  the call target before splitting on the return block. Proofs written
  against the old `evalCallTerminator` shape can `simp only
  [evalTerminator_call_eq, evalCallTerminatorB]` and keep their case order.
- `stepMirFn_extCall_aborts_prop` unfolds the intrinsic helpers.

### 4.2 Adversarial critique of `[adv A0]` & fixes in `[adv B1]`

`[adv A0]` (`2109bdec`) executed the merge-base protocol cleanly, but left an
uncompilable tree with six distinct classes of failures that `[adv B1]`
resolved:

1. **12 broken call-step theorems & example proofs in `Anneal.PureMirExec`**:
   Ported `wpMirExecNoCallSym_pushCalleeFrame`,
   `stepMirFn_extCall_aborts_prop`,
   `wpMirExecNoCallSym_pushBaseStack_nil_outer`,
   `PureMirConvergesWithCallees.call_exact_div`,
   `stepMirFn_pureCallee_step_and_replaceRoot`,
   `PureMirModularConverges.{call_modular,call_external_spec,`
   `call_external_spec_sub,call_exact_div,call_modular_resolved,`
   `call_exact_div_pureTarget}`, `sameExceptBorrows_step_noCall`, and the
   downstream modular example proofs to `087b015b`'s `evalTerminator` /
   `evalDirectRustIntrinsic?` / `resolveIntrinsicIsSigned` semantics (adding
   `classifyRustIntrinsic? defPath = none` preconditions on external-call rules
   and `pushBaseStack` commutation across all direct Rust intrinsic families).
2. **`check_trusted.py --fast` 60s child-process timeout on `Anneal.PureMirExec`
   (`85s` -> `51s`)**: Introduced `IsIntrinsicCallFamily` with generic
   scalar/wide-pointer `pushBaseStack` combinators, `evalStmt_assign_eq` +
   `evalAssignDst_nonDeref`, `stepMirFn_eq_ite` (eliminating 2x `MirPhaseTag`
   proof duplication), explicit `TerminatorKind` dispatch in
   `stepMirFn_extCall_aborts_prop`, and `change`-based reduction in
   `evalDirectRustIntrinsic_*`, cutting standalone compile time from `85s` to
   `51s` and `.olean` size from `38 MB` to `32 MB`.
3. **Unported `MirLiftCore`, `MirLift`, and `MirLiftBench` + symbolic
   `activeProtectors` regression**: Ported `evalStmt_assign_of_evalRvalue`,
   `LiftTerminator.evalNodeWP_of`, `evalOperandFast_eq`, `evalRvalueFast_eq`,
   `evalRvalueSymTreeFast_eq`, `MirLift.lean` (`#mir_lift` / `#mir_lift_spec`
   external-call intrinsic guards), and `MirLiftBench.lean`. Preserved
   `hasProtectedWriteConflict mem₁.borrows mem₁.activeProtectors ...` in
   `finishAssignStmtNodeFast` (via `hasProtectedWriteConflict_nil`) so proofs
   with symbolic `activeProtectors` (`WireframeDemo.checksum_frame_safe` and
   `FrameTutor`) verify with zero changes to `examples/`.
4. **5 broken deref subplace theorems & 4 `-DwarningAsError=true` lint errors
   in `Anneal.SepLogicLenses`**: Ported `LiftDerefWrite.{evalStmt_field_eq,`
   `evalStmt_eq,evalStmt_eq_subplace}`,
   `LiftDerefRead.evalOperand_and_freeze_eq_subplace`, and
   `LiftDerefFieldRead.evalOperand_and_freeze_eq_subplace` to
   `needsThinPtrElemResolution` / `resolveDerefWriteFullProj` /
   `invalidateDerefWriteBorrows`, and removed 4 unused
   `ProvenancePtr.offsetBytes` `simp` arguments.
5. **60s child-process timeouts in `FunctionalTranslationTests` (`53s` -> `5s`)
   and `FunctionalTranslationEquivTests` (`-> 17s`)**: Replaced 80-symbol
   `dsimp only` calls (which rebuilt `SimpTheorems` discrimination trees across
   ~400 `087b015b` equation lemmas on every step) with WHNF `rfl` raw-state
   transitions and minimal local-step `dsimp only` lists.
6. **`downstream-audit` foreign-dependency collision in `SymbolicEvalTests`**:
   Both `SymbolicEvalTests` and `PureMirExec`/`MirFuelFree` lazily realized
   `evalOperands.eq_def` and `evalRvalue.eq_28` with module-private
   `_private.<Mod>.0.*` splitter helpers, causing `importModules` in
   `downstream-audit` to overwrite the stored proof bodies with
   `SymbolicEvalTests` helpers. Replaced bare `evalRvalue`/`evalOperands` in
   two `SymbolicEvalTests.lean` `simp only` blocks with six constructor-specific
   `rfl` lemmas (`0` collisions across all `31` downstream targets).

## 5. Receipts at `[adv B1]`

See the `[B1 -> A1]` board post for the verbatim outputs.

| Check | Result |
| :--- | :--- |
| `087b015b` and `1642f8aa` are ancestors of `HEAD` | pass |
| `git diff --stat 087b015b..HEAD -- crates/ docs/ ci/ .github/ .gemini/ Cargo.toml Cargo.lock FRAMEWORK_PRINCIPLES.md FRAMEWORK_PRINCIPLES_DESIGN.md README.md scripts/ theory/Correspondence/` | empty (pass) |
| `git diff 087b015b..HEAD -- trusted/lean/` | only the two `traitImpls := body.traitImpls` lines (pass) |
| `./ci/check_todo.sh` | exit 0 (pass) |
| `cargo test -p cargo-anneal --lib --bins` | 56 passed, 0 failed (pass) |
| `lake build Anneal MirVerification` (and `MirLift`) | pass |
| `python3 trusted/audit/check_trusted.py --fast` | PASS (`40` Trusted modules, `9,589` Trusted decls, `24,294` replayed decls) |
| `cargo-anneal verify` (`wireframe-demo` and `tutor`) | PASS (`9` + `7` unconditional, `0` conditional, kernel replay PASS) |

No `sorry`, `admit`, `sorryAx`, `axiom`, `#[trusted]`, or `native_decide` was
added, and `trusted/` differs from `087b015b` only as the brief allows.

## 6. Reproduction commands

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
cd /home/groupagent-anneal-fuzz-bot/Projects/markdittmer/anneal-wt-ff-4-2b
git merge-base --is-ancestor 087b015b HEAD && echo "087b015b IS ANCESTOR"
git merge-base --is-ancestor 1642f8aa HEAD && echo "1642f8aa IS ANCESTOR"
git diff --stat 087b015b..HEAD -- crates/ docs/ ci/ .github/ .gemini/ \
  Cargo.toml Cargo.lock FRAMEWORK_PRINCIPLES.md \
  FRAMEWORK_PRINCIPLES_DESIGN.md README.md scripts/ theory/Correspondence/
git diff --stat 087b015b..HEAD -- trusted/
./ci/check_todo.sh
anneal-lean-run --mode build --concurrency 1 -- \
  cargo test -p cargo-anneal --lib --bins
(cd examples && anneal-lean-run --mode build --concurrency 1 -- \
  lake build Anneal MirVerification)
(cd examples && anneal-lean-run --mode file --concurrency 1 \
  -- lake env lean ../theory/Anneal/MirLift.lean)
python3 trusted/audit/check_trusted.py --fast
anneal-lean-run --mode build --concurrency 1 -- \
  cargo-anneal verify --manifest-path examples/wireframe-demo/Cargo.toml
anneal-lean-run --mode build --concurrency 1 -- \
  cargo-anneal verify --manifest-path examples/tutor/Cargo.toml
git status --porcelain   # move untracked .anneal/ and Cargo.lock out first
```

## 7. `[diversity-reduced]` 3rd-party audit notice

`anneal-model-policy` assigned `ff42b-a` to Model X `opus-5.5-max`, and
`ff42b-b`'s Model Y slot (`gemini-launch-candidate-high`) to the Reserve
Frontier Pool `gemini-pro-coordinator` at Pass `A0`, because the
`gemini-google-teamfood-wtu-v2` bucket was at 0.0% (below the 15% `P1`
floor). Every pass of this unit (`A0` through `A2`) therefore runs with
reduced cross-family diversity, and the merged result **needs a 3rd-party
(different-model) audit** before it lands. In addition, `opus-5.5-max` fell to
12% (below the `P1` floor) during Pass `A0`.
