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
as a pass. It describes the state after checkpoint `[adv A0]`; later
checkpoints update it.

## What `MR-4.2` adds so far

- **MiniRust interpretation** (`minirust/lean/MiniRustSpec/Interp.lean`):
  - `Terminator::Intrinsic` (`evalIntrinsicTerminator`,
    `spec/lang/step/terminators.md`), its argument loop
    (`evalIntrinsicArgs`), and `Machine::eval_intrinsic` (`evalIntrinsic`,
    `spec/lang/step/intrinsics.md`) for `Exit` (`Machine::exit` with
    `ConcurrentMemory::leak_check`), `Abort`, `Assume`, `PrintStdout`,
    `PrintStderr` (`Machine::eval_print`), `Allocate`, `Deallocate`,
    `PointerExposeProvenance` (`IntPtrCast::expose`), and `GetUnwindPayload`.
    `RawEq` and `PointerWithExposedProvenance` run their transcribed argument
    and return-type checks and then report `Stop.unsupported` (`RawEq` needs
    `Type` equality and `load_raw_data`; `int2ptr` needs an angelic choice),
    as do the thread, lock, and atomic intrinsics.
  - `unit_value`, `unit_type`, the `throw_abort!`, `throw_machine_stop!`, and
    `throw_memory_leak!` macros (new `Stop.abort`, `Stop.machineStop`, and
    `Stop.memoryLeak`), and `PlaceExpr::Deref` (`derefPlace`), with
    `evalPlace` now threading the machine like upstream `eval_place(&mut self)`
    (`fieldPlace` holds the `PlaceExpr::Field` projection).
- **Anchors** (`minirust/lean/MiniRustSpec/Anchors.lean`): 78 anchors (up from
  61 in `MR-4.1`).
- **Translation** (`minirust/lean/MiniRustSpec/Correspondence/Translate.lean`):
  `StatementResult`, `isAssume`, and `translateStmtResult` transcribe
  `minimize`'s `translate_stmt` for
  `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))` (a
  `StatementResult::Intrinsic` with destination `build::unit_place()`), and
  `splitStmts` transcribes `translate_bb`'s statement loop, which ends the open
  block in `Terminator::Intrinsic { intrinsic: IntrinsicOp::Assume, .. }` and
  opens a block with a fresh name. `translateBlocksInProg` uses it, so
  `translateFnInProg` allocates fresh names in `minimize`'s order (all split
  blocks of a MIR block, then its terminator's unwind block). `unitPtr`,
  `unitPlace`, and `abortTerminator` transcribe `build::unit_ptr()`,
  `build::unit_place()`, and `build::abort()`. `SegChain` describes the
  resulting layout; `translateFnInProg_spec` now states it for every MIR block,
  and `translateBlocksInProg_names` proves the block names distinct.
- **Simulation**: the `MR-1.x` and `MR-4.1` theorem statements are unchanged.
  `bodyInProgFragment` still requires `statementOk`, so a fragment body has no
  `Assume` statement and `SegChain.eq_last` recovers the one-to-one block
  layout that `multi_step_correspondence` uses.
- **Witnesses** (`Correspondence/Witness.lean`): `evalIntrinsic_*` and
  `evalTerminator_abortTerminator` check every transcribed `eval_intrinsic`
  arm on a concrete machine; `assumeSub` (two `Assume` statements in one MIR
  block, split into three MiniRust blocks) is computed on both sides:
  `assumeSub20_anneal_ret`, `assumeSub20_minirust_direct`, and
  `assumeSub20_split_point` for `(20, true)`, and `assumeSubFalse_ub` for
  `(20, false)`.
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
- **Boundary witnesses** (`Correspondence/IntrinsicBoundary.lean`, 35
  theorems): Anneal's behavior on, and the fragment's rejection of,
  `Rvalue::NullaryOp(UbChecks)` (Anneal `unsupported`; `minimize` emits a
  session-fixed `bool`), `CopyNonOverlapping` (Anneal returns normally even
  for an out-of-bounds two-element copy, `bdCopy2_noUB`; `minimize` aborts with
  `span_bug!`), `BinOp::Offset` (Anneal adds the raw count without scaling or
  bounds checks, `bdOffsetNeg1_noUB`), external calls to
  `core::intrinsics::{write_bytes, raw_eq, cold_path, ctpop, exact_div,
  arith_offset}` (a `MirCallReq` carries no types:
  `bdExactDiv_same_request` versus `bdExactDiv_minirust_i32` /
  `bdExactDiv_minirust_u32`), the diverging `abort` call (`unsupported`), and
  `core::hint::unreachable_unchecked()` (UB on both sides).
- **Quotation and pipeline checks**
  (`crates/anneal-minirust-gen/tests/{quotes,pipeline}.rs`):
  `intrinsic_and_assume_quotations_are_pinned` pins 18 verbatim quotations
  across `spec/lang/step/intrinsics.md`, `spec/lang/step/terminators.md`,
  `spec/lang/step/expressions.md`, `spec/prelude/main.md`,
  `spec/mem/basic.md`, `spec/mem/intptrcast.md`, and
  `tooling/minimize/src/bb.rs`, with tampered-quote and cross-file
  misattribution rejection; the pipeline test requires 78 anchors, at least
  `268` `[SIMULATION-AUDIT]` and `585` `[WITNESS-AUDIT]` theorems, and that
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
[SIMULATION-AUDIT] decls=268 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
[WITNESS-AUDIT] decls=585 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
[WITNESS-AUDIT] decls=118 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
[WITNESS-AUDIT] decls=35 axioms=[propext, Quot.sound] sorry_free=true
MiniRustSpec.Audit: exhaustively verified standard axioms for 12739 declarations across all MiniRustSpec.* modules
```

(The second and third `[WITNESS-AUDIT]` lines cover
`Correspondence/IntrinsicFallback.lean` and
`Correspondence/IntrinsicBoundary.lean`. `lake` prints already-built modules
without re-running them; to see the audit lines again after a successful
build, touch `minirust/lean/MiniRustSpec/Audit.lean` first.)

## Step 4: spot checks

- `assumeSub_translateInProg` spells out the three MiniRust blocks of
  `assumeSub`'s single MIR block (`bbName 0`, `bbName 2`, `bbName 3`, with
  `init_bb = bbName 1`), and `assumeSub20_split_point` shows that MIR point
  `(bb0, 1)` (after the first `Assume`) corresponds to the start of `bbName 2`.
- `assumeSubFalse_ub` shows both semantics raising UB at the first `Assume`
  of `assume_sub(20, false)`, with MiniRust's exact `eval_intrinsic` message.
- `evalIntrinsic_assume` checks the four UB checks of `IntrinsicOp::Assume`;
  `evalIntrinsic_print` checks the exact lines written to `stdout`/`stderr`.
- `progStart_outside_fragment` now shows `build::unit_place()` evaluating to
  the aligned place at address `1`, while `create_frame` still rejects
  `mk_start_fn`'s call for `callerMain` and `cAbiCallee`.
- `fbCtlz_anneal_all`, `fbCttz_anneal_all`, and `fbBitrev_anneal_all` quantify
  over all `a < 256`; `fbBlackBox_anneal_all` over every argument.

## Known limitations (to be lifted in later checkpoints)

- `Assume` statements are outside `progInFragment`: the translation splits
  blocks like `minimize`, but the simulation relation still matches MIR
  `(blk, stmt)` with MiniRust `(bbName blk, stmt)`. A program-point relation
  (`SegChain`-based) is needed to admit them.
- Compiler intrinsics reached through `TerminatorKind.call` to a `DefPath`
  outside `callees` (`ctpop`, `exact_div`, `abort`, `cold_path`, ...) are
  Anneal external calls (`MirStepNode.extCall`), which `MultiStepRel` does not
  relate; `minimize`'s `translate_rs_intrinsic` lowerings of them are not yet
  transcribed. Anneal's `MirCallReq` carries only the `DefPath`, the argument
  values, and the memory, so a handler cannot recover `exact_div`'s
  signedness from the request.
- `Rvalue::NullaryOp(UbChecks)` (unsupported in Anneal, a constant `bool` in
  `minimize`), `CopyNonOverlapping` (`span_bug!` in `minimize`),
  `arith_offset`/`BinOp::Offset`, `write_bytes`, and `raw_eq` are outside the
  fragment, which has no pointers.
