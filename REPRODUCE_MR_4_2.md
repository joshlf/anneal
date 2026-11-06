<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproducing `MR-4.2`: `Terminator::Intrinsic` and `Statement::Intrinsic`

This guide lets an independent reviewer check every claim of work unit
`MR-4.2` from a clean checkout of branch `adv/mr-4-2`. Run all commands from
the repository root. Each step lists the command and the output that counts
as a pass. It describes the state after checkpoint `[adv B2]`; later
checkpoints update it.

## What `MR-4.2` adds so far

- **MiniRust interpretation** (`minirust/lean/MiniRustSpec/Interp.lean`):
  - `Terminator::Intrinsic` (`evalIntrinsicTerminator`,
    `spec/lang/step/terminators.md`), its argument loop
    (`evalIntrinsicArgs`), and `Machine::eval_intrinsic` (`evalIntrinsic`,
    `spec/lang/step/intrinsics.md`) for `Exit` (`Machine::exit` with
    `ConcurrentMemory::leak_check`), `Abort`, `Assume`, `PrintStdout`,
    `PrintStderr` (`Machine::eval_print`), `Allocate`, `Deallocate`, full
    `RawEq` (`Machine::load_raw_data` + structural `Type` equality `typeEq`),
    `PointerExposeProvenance` (`IntPtrCast::expose`), and `GetUnwindPayload`.
    `PointerWithExposedProvenance` runs its transcribed argument and
    return-type checks and then reports `Stop.unsupported` (`int2ptr` needs an
    angelic choice), as do the thread, lock, and atomic intrinsics.
  - `unit_value`, `unit_type`, the `throw_abort!`, `throw_machine_stop!`, and
    `throw_memory_leak!` macros (new `Stop.abort`, `Stop.machineStop`, and
    `Stop.memoryLeak`), and `PlaceExpr::Deref` (`derefPlace`), with
    `evalPlace` now threading the machine like upstream `eval_place(&mut self)`
    (`fieldPlace` holds the `PlaceExpr::Field` projection).
- **Anchors** (`minirust/lean/MiniRustSpec/Anchors.lean`): 78 anchors (up from
  61 in `MR-4.1`), including `impl_Machine__load_raw_data` and all structural
  `typeEq` helpers.
- **Translation** (`minirust/lean/MiniRustSpec/Correspondence/Translate.lean`):
  `StatementResult`, `isAssume`, and `translateStmtResult` transcribe
  `minimize`'s `translate_stmt` for
  `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))` (a
  `StatementResult::Intrinsic` with destination `build::unit_place()`), and
  `splitStmts` transcribes `translate_bb`'s statement loop, which ends the open
  block in `Terminator::Intrinsic { intrinsic: IntrinsicOp::Assume, .. }` and
  opens a block with a fresh name. `TerminatorResult`, `buildCountOnes`,
  `buildDivExact`, and `translateRsIntrinsic` transcribe `minimize`'s
  `translate_rs_intrinsic` for `raw_eq`, `ctpop`, `exact_div`, `cold_path`, and
  `abort`. `translateBlocksInProg` allocates fresh names in `minimize`'s order
  (all split blocks of a MIR block, then its terminator's unwind block).
  `unitPtr`, `unitPlace`, and `abortTerminator` transcribe `build::unit_ptr()`,
  `build::unit_place()`, and `build::abort()`. `SegChain` and `SegPc` describe
  the split-block layout and program-point mapping (`translateFnInProg_spec`,
  `translateBlocksInProg_names`), while `stmtReadsOk`, `stmtMoved`, `stmtLocals`,
  and `stmtTupleInit` track `Assume(op)` across `movesOk`, `livenessOk`, and
  `tupleInitOk`. `funcCfgWf` and `progWf` transcribe MiniRust's syntactic
  function and program well-formedness checks (`spec/lang/well-formed.md`).
- **Simulation** (`Relation.lean`, `Lemmas.lean`, `MiniRustEval.lean`,
  `AnnealEval.lean`, `Simulation.lean`, `Run.lean`): the `MR-1.x` and `MR-4.1`
  theorem statements in `Run.lean` are unchanged. `progInFragment`
  (`progStatementOk`) admits `Assume(op)` on any `bool` fragment operand (`copy _j`,
  `move _j`, `copy (_j.1)`, `move (_j.1)`, or `bool` constant), aligning MIR
  `(blockIdx, stmtIdx)` with MiniRust split-block `(next_block, next_stmt)` via
  `SegPc` in both the active frame (`MultiStateRelAt`) and suspended caller
  frames (`CallStackRel`), and `translateFnInProg_funcCfgWf`,
  `translateFn_funcCfgWf`, `mkStartFn_funcCfgWf`, and `translateProg_progWf`
  prove universal CFG and program well-formedness across arbitrary `Assume`
  split chains.
- **Witnesses** (`Correspondence/Witness.lean`): `evalIntrinsic_*` (including
  full `evalIntrinsic_rawEq` and `evalIntrinsic_allocate_deallocate_leak`),
  `evalTerminator_abortTerminator`, and `translateRsIntrinsic_witness` check
  every transcribed `eval_intrinsic` arm and `translate_rs_intrinsic` lowering;
  `assumeSub` (`assumeSub_inFragment`, `assumeSub20_minirust_ret`,
  `assumeSubFalse_minirust_ub_rel`), `assumeTupleCallCaller` (`Assume(move _)` +
  tuple-field projection + `Terminator::Call` across split blocks),
  `assumeMultiFrameCaller`/`assumeChainCallee` (pre-call, multi-split callee,
  and post-call `Assume` chains with `StorageLive`/`StorageDead` spanning splits),
  and `assumeDeadLocal` prove end-to-end correspondence via
  `mirCallWithCallees_ret` and `mirCallWithCallees_ub_rel`; and `assumeMoveReuse`
  + `assumeAfterMove` prove necessity of `stmtMoved` and `stmtReadsOk` on
  `Assume`.
- **Fallback-body calls** (`Correspondence/IntrinsicFallback.lean`): calls to
  `core::intrinsics::{ctlz, cttz, bswap, bitreverse, saturating_add,
  saturating_sub, black_box}` and `u32::{wrapping_shl, wrapping_shr}` resolved
  to hand-written fallback bodies in `callees` are ordinary `MR-4.1` fragment
  calls; each is checked against a pure Lean reference, exhaustively for the
  unary `u8` operations and for `black_box`, and on rows, columns, grids, or
  samples for the others (see the module docstring), and transferred to
  MiniRust by `mirCallWithCallees_ret`. Upstream `minimize` aborts with
  `span_bug!` on the seven intrinsics, so these witnesses relate Anneal to the
  MiniRust program that calls the fallback body, not to `minimize`'s output.
- **Handler correspondence & boundary witnesses**
  (`Correspondence/IntrinsicBoundary.lean`): concrete `ExternalCallHandler`s
  (`coldPathHandler`, `ctpopHandler`, `ubChecksHandler`, `exactDivHandler`)
  proved equivalent under `mirHandledTree` (`handleMirExternalCalls`) to
  `minimize`'s `translateRsIntrinsic` lowerings (`bdColdPath_handled`,
  `bdCtpop_handled`, `bdUbChecksCall_handled`, `bdExactDiv_handled`,
  `exactDivHandler_iff_minirust`), backed by a symbolic
  proof that MiniRust's `IntUnOp::CountOnes` equals unsigned bit-pattern
  popcount across all signed and unsigned `IntType` widths
  (`evalCountOnes_intFromBits`, `evalCountOnes_signedness_indep`); plus Anneal's
  behavior on, and the fragment's rejection of, `Rvalue::NullaryOp(UbChecks)`,
  `CopyNonOverlapping` (`bdCopy2_noUB`), `BinOp::Offset` (`bdOffsetNeg1_noUB`),
  `write_bytes` (`bdWriteBytes_extCall`, `bdWriteBytes_unhandled_fault`),
  type-erased `MirCallReq`s (`bdExactDiv_same_request` versus
  `bdExactDiv_minirust_i32` / `bdExactDiv_minirust_u32`), diverging `abort`
  (`bdAbort_unsupported`), and `core::hint::unreachable_unchecked()`
  (`bdUnreach_anneal_ub`, `bd_minirust_unreachable_ub`).
- **Quotation and pipeline checks**
  (`crates/anneal-minirust-gen/tests/{quotes,pipeline}.rs`):
  `intrinsic_and_assume_quotations_are_pinned` pins 28 verbatim quotations
  across `spec/lang/step/intrinsics.md`, `spec/lang/step/terminators.md`,
  `spec/lang/step/expressions.md`, `spec/lang/well-formed.md`,
  `spec/prelude/main.md`,
  `spec/mem/basic.md`, `spec/mem/intptrcast.md`, and
  `tooling/minimize/src/bb.rs`, with tampered-quote and cross-file
  misattribution rejection; the pipeline test requires 78 anchors, at least
  `291` `[SIMULATION-AUDIT]` and `626` `[WITNESS-AUDIT]` theorems, and that
  every theorem of `IntrinsicFallback.lean` and `IntrinsicBoundary.lean` is
  listed in `Audit.lean`.

## Step 0: environment

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
git log --oneline 4bd29bc7..HEAD   # pass: the MR-4.2 checkpoints so far
git status --porcelain             # pass: no output
git diff --stat 4ed6d2ab..HEAD -- trusted/   # pass: no output
```

## Step 1: repository hygiene

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```

Pass: both exit `0`; the trusted-base audit prints `PASS (40 Trusted modules;
6659 Trusted kernel declarations; ...)`.

## Step 2: anchors and quotations

```bash
cargo test -p anneal-minirust-gen --offline
```

Pass: all `23` tests (`8` unit + `7` pipeline + `8` quotes) pass, including
`anchors_match_generated_items_and_cover_interp` and
`intrinsic_and_assume_quotations_are_pinned`.

## Step 3: Lean proofs and audit

```bash
cd examples
anneal-lean-run --mode build --concurrency 3 --timeout 2400 -- lake build MiniRustSpec 2>&1 | tee /tmp/mr42-build.log
grep -E '\[(ANCHOR|SIMULATION|WITNESS)-AUDIT\]|exhaustively verified' /tmp/mr42-build.log
cd ..
```

Pass: `Build completed successfully`, with:

```text
[ANCHOR-AUDIT] decls=2 axioms=[] sorry_free=true
[SIMULATION-AUDIT] decls=291 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
[WITNESS-AUDIT] decls=626 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
[WITNESS-AUDIT] decls=118 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
[WITNESS-AUDIT] decls=45 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
MiniRustSpec.Audit: exhaustively verified standard axioms for 13336 declarations across all MiniRustSpec.* modules
```

(The second and third `[WITNESS-AUDIT]` lines cover
`Correspondence/IntrinsicFallback.lean` and
`Correspondence/IntrinsicBoundary.lean`. `lake` prints already-built modules
without re-running them; to see the audit lines again after a successful
build, touch `minirust/lean/MiniRustSpec/Audit.lean` first.)

## Step 4: spot checks

- `assumeSub_inFragment`, `assumeSub20_minirust_ret`, and
  `assumeSubFalse_minirust_ub_rel` prove full correspondence (`mirCallWithCallees_ret`
  and `mirCallWithCallees_ub_rel`) for `assumeSub`'s split-block layout (`bbName 0`,
  `bbName 2`, `bbName 3`, `init_bb = bbName 1`), while `assumeSub20_split_point`
  checks that MIR point `(bb0, 1)` matches the start of `bbName 2`.
- `assumeTupleCall10_minirust_ret` and `assumeTupleCallOv_minirust_ub_rel`
  exercise `Assume(move _)` + tuple-field projection + `Terminator::Call` across
  two split blocks; `assumeDeadLocal_minirust_ub_rel` checks dead-local `Assume`
  UB; and `assumeMoveReuse_diverges` + `assumeAfterMove_diverges` prove
  necessity of `stmtMoved` and `stmtReadsOk` on `Assume`.
- `evalIntrinsic_rawEq` and `evalIntrinsic_allocate_deallocate_leak` check full
  `RawEq` (`load_raw_data` + `typeEq`) and `Allocate`/`Deallocate`/`Exit`
  (`Stop.memoryLeak` vs `Stop.machineStop`), alongside `evalIntrinsic_assume`,
  `evalIntrinsic_print`, and `translateRsIntrinsic_witness`.
- `bdColdPath_handled`, `bdCtpop_handled`, `bdExactDiv_handled`,
  `exactDivHandler_iff_minirust`, `evalCountOnes_intFromBits`, and
  `evalCountOnes_signedness_indep` prove `ExternalCallHandler` correspondence
  (`mirHandledTree`) and signedness-invariance of `IntUnOp::CountOnes`.
- `fbCtlz_anneal_all`, `fbCttz_anneal_all`, and `fbBitrev_anneal_all` quantify
  over all `a < 256`; `fbBlackBox_anneal_all` over every argument.

## Known limitations and architecture boundaries

- Unresolved compiler intrinsic calls (`TerminatorKind.call` to a `DefPath`
  outside `callees`, such as `ctpop`, `exact_div`, `cold_path`) emit `MirCallE`
  external calls in Anneal (`MirStepNode.extCall`): `IntrinsicBoundary` relates
  them under `mirHandledTree` (`ExternalCallHandler`), and proves why
  `MirCallReq`'s erased generic types require per-`IntType` handler
  specialization (`exactDivHandler it`) for `exact_div` (`bdExactDiv_same_request`
  vs `bdExactDiv_minirust_i32` / `bdExactDiv_minirust_u32`). Diverging `abort`
  calls (`target = none`) remain `unsupported` in Anneal (`bdAbort_unsupported`).
- `Rvalue::NullaryOp(UbChecks)` (`unsupported` in Anneal, session-fixed `bool`
  constant in `minimize`), `CopyNonOverlapping` (`span_bug!` in `minimize`),
  `arith_offset`/`BinOp::Offset`, `write_bytes`, and `raw_eq` calls operate on
  pointers and remain outside the pointer-free `progInFragment` (`IntrinsicBoundary`
  documents each boundary, while `Interp.lean` fully interprets `IntrinsicOp::RawEq`).
