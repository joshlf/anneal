<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproducing `MR-1.3`: arbitrary locals, `StorageLive`/`StorageDead`/`Deinit`, `Operand::Move`, and the init block

This guide lets an independent reviewer check every claim of work unit
`MR-1.3` from a clean checkout of branch `adv/mr-1-3`. Run all commands from
the repository root. Each step lists the command and the output that counts
as a pass.

## What `MR-1.3` adds

- **MiniRust interpretation** (`minirust/lean/MiniRustSpec/Interp.lean`):
  - `Statement::StorageLive` and `Statement::StorageDead` through
    `Machine::try_mutate_cur_frame` and `StackFrame::{storage_live,
    storage_dead}` (`spec/lang/step/statements.md`), and `Statement::Deinit`
    through `ConcurrentMemory::deinit`.
  - `ConcurrentMemory::allocate` and `BasicMemory::allocate`
    (`spec/mem/basic.md`), including `x86_64::valid_size` and
    `Allocation::overlaps`. The daemonic address choice `pick` never has a
    unique solution, so the interpretation commits to one valid resolution
    (`BM.pickAddr`): the first of the candidates `allocCandidate k =
    (k + 1) * 2^32` that passes every test of the upstream predicate
    (`BM.allocAddrOk`, transcribed test by test). When no candidate passes,
    `BM.allocate` reports `Stop.unsupported` instead of inventing an address.
- **Anchors** (`Anchors.lean`): 58 anchors (up from 55), with the new
  `allocate` helpers and `BM.deallocate` listed in the
  `impl_BasicMemory__allocate` anchor.
- **Quotation checks** (`crates/anneal-minirust-gen/tests/quotes.rs`):
  `storage_live_dead_deinit_move_and_init_block_quotations_are_pinned` pins 22
  upstream quotations (`valid_size`, `overlaps`, `allocate` and its `pick`
  predicate, `BM.deallocate` and all six of its UB checks, `CM.allocate`,
  `CM.deallocate`, `try_mutate_cur_frame`, `deinit`, `Deinit`, `storage_live`,
  `storage_dead`, the `StorageLive`/`StorageDead` statements, `deallocAll`'s
  `Return` teardown loop, `minimize`'s `Move` operand, local-type map, and
  storage-statement translations, its `args` / `free_argc` / init-block /
  `blocks.insert` / `ret` setup, and `spec/lang/well-formed.md`'s
  `Function::check_wf` `start_live`, `Statement::Deinit`,
  `Statement::StorageLive`, and `Statement::StorageDead` well-formedness
  rules), verifies every quotation on both the vendored upstream side and the
  Lean side via `extract_quotes`, rejects tampered variants, and rejects file
  misattribution across all 10 `MR-1.3` upstream files.
- **Translation and fragment** (`Correspondence/Translate.lean`):
  - Bodies may declare any number of temporaries (fewer than `2^31` locals).
  - `StorageLive`/`StorageDead` translate to MiniRust's statements;
    `Deinit(_i)` of a root local translates to
    `Statement::Deinit(PlaceExpr::Local(_i))` (an extension: `minimize` has no
    `Deinit` translation). A projected `Deinit` is outside the fragment:
    Anneal reads the projected value and keeps the slot, whereas MiniRust
    writes `Uninit`.
  - `move` operands translate like `copy` (`copyOp`, `copyRv`), as in
    `minimize`. Anneal's root `move` leaves the local uninitialized while
    MiniRust's is a plain load, so `movesOk` rejects any body that reads a
    possibly moved-out local before writing it again (including operand moves on
    projected assignments and `_0` on `Return`) via forward CFG dataflow
    propagation (`movedAtEntry`, propagating moved-out sets across `Goto` and
    `SwitchInt` edges from `[]` at `bb0`).
  - `initBlock`: `StorageLive` of `alwaysStorageLiveLocals` (temporaries
    without storage markers), then `Goto(bb0)`, as `minimize`'s
    `always_storage_live_locals` filter computes. Anneal keeps such a
    temporary dead, so `mentionsOk` requires that the body never mentions
    one.
  - `storageDeadOk`: `StorageDead` only of temporaries (MiniRust's
    well-formedness check rejects it for the return place and the
    arguments).
- **Correspondence** (`Relation.lean`, `MiniRustEval.lean`, `AnnealEval.lean`,
  `Simulation.lean`, `Run.lean`):
  - `LocalsOkA`/`LocalsOk` relate the callee's locals map and allocations to
    Anneal's slots: a local is mapped exactly when its slot is live (or it is
    an allocated init-block temporary), each mapped local owns a distinct
    `Stack` allocation encoding its slot at an aligned address below `2^32`
    or at a first-fit candidate (`AddrClass`), and every live allocation
    above the caller's belongs to a mapped local. `StartRel.addrs` and
    `CtxOk.addrs` constrain only `_0` and the arguments (`i ≤ argCount`), so
    caller contexts need not supply addresses for callee temporaries.
  - `StaleOk` allows MiniRust's bytes to differ from Anneal's slots only for
    locals that Anneal's `move` de-initialized and that `movesOk` keeps unread
    (`movedBefore`), and `StateRel` existentially quantifies the MiniRust view
    of the slots.
  - MiniRust lemmas for `StorageLive` (including the pigeonhole argument that
    a free first-fit candidate below `2^31` exists: `LocalsOkA.free_candidate`,
    `BM_allocate_local`), `StorageDead`, `Deinit`, a dead assignment target,
    the init block (`evalStatement_storageLive_init`), and `Return`'s teardown
    of an arbitrary locals map (`deallocAll_gen`, `killAt_append_dead`,
    `evalReturn_frame`).
  - Anneal lemmas reducing `move` to `copy` plus de-initialization
    (`evalOperand_move`, `evalRvalue_move`, `evalStmt_assign_move`, with the
    locals-parametricity of `evalScalarBinOp` and `evalUnaryNot`), and for
    `StorageLive`, `StorageDead`, and `Deinit`.
  - `step_correspondence` (`mirSimStep`) now covers every statement and
    terminator of the extended fragment, including the dead-local UB cases,
    backed by `stepMovedEntries_spec`, `iterMovedEntries_fixed`,
    `iterMovedEntries_mono`, `iterMovedEntries_eq_of_fixed`,
    `terminatorOk_targets_lt`, `movesOk_of_fixed`, `unionLocals_eq_or_mem_new`,
    `stepMovedEntries_eq_or_strict`, `iterMovedEntries_stabilizes`,
    `statementOk_stmtMoved_lt`, `terminatorOk_termMoved_lt`,
    `movesOk_iff_blockMovesOk`, `stmtMoved_mono`, `termMoved_mono`,
    `stepMovedEntries_least`, `iterMovedEntries_least`, `movedAtEntry_least`,
    `stmtReadsOk_antitone`, `termReadsOk_antitone`, `blockMovesOk_antitone`,
    `movesOk_of_preFixedPoint`, and `movesOk_iff_exists_preFixedPoint`
    (unconditional finite-fuel fixed-point convergence, Knaster–Tarski least
    fixed-point optimality, antitonicity of `blockMovesOk`, Park-induction
    pre-fixed-point soundness and completeness, and exact `blockMovesOk`
    characterization on well-typed CFGs) for the monotone forward CFG dataflow
    `movedAtEntry`; `step_start` runs the
    init block in `initLen body` MiniRust steps; all `Run.lean` theorems
    (`mirSimRun`) are re-proved, with the `*_from_start` step counts
    `initLen body + n`.
- **Witnesses** (`Correspondence/Witness.lean`):
  - `tempMove`: `u32` and `bool` temporaries with storage markers, root
    `move` in a `BinaryOp`, a `Use`, and a `switchInt` discriminant, `Deinit`
    of a moved-from temporary, and an unused temporary that the init block
    allocates; `temp_move(3) = 100` and `temp_move(2) = 6` via `mirCall_ret`,
    `mirCall_noUB`, and `mirCall_progress`, confirmed by direct runs that also
    show every callee allocation dead after the return and `StorageLive`
    reusing a released first-fit address (`tempMove3_minirust_direct`,
    `tempMove2_minirust_direct`).
  - `crossBlockMove`: a 4-block CFG exercising the forward dataflow `movesOk`
    check across `Goto` and `SwitchInt` edges, moving the incoming argument
    `_1` in `bb0`, projected tuple moves `move (_2.0)` and `move (_2.1)` on a
    `(u32, bool)` temporary, carrying live temporaries across block boundaries
    before moving them in later blocks, calling `StorageLive` on already-live
    locals without an intervening `StorageDead`, `Deinit` of a `(u32, bool)`
    tuple local, and idempotent `StorageDead` on an already-dead local
    (`crossBlockMove20_*`, `crossBlockMoveOv_*`, including `mirCall_progress`).
  - `loopTempMove`: a cyclic 4-block loop CFG with two heterogeneous unmarked
    temporaries (`alwaysStorageLiveLocals = [4, 5]`, `initLen = 3`), multi-pass
    back-edge fixpoint convergence of `iterMovedEntries`
    (`loopTempMove_movedAtEntry_multiPass`), per-iteration `StorageLive(_3)`,
    `SwitchInt(move _3)`, `Deinit(_3)`, and `StorageDead(_3)`, live
    re-allocation of `_2`, and idempotent `StorageDead(_2)` on `n = 0`
    (`loopTempMove3_*`, `loopTempMove0_*`, including `mirCall_progress`).
  - `storageLiveArgRet`, `diamondMoveJoin`, `tupleAggCastMove`, and
    `ordBoolCastTempMove`:
    `StorageLive(_1)` and `StorageLive(_0)` re-allocating an argument local and
    the return place from their initial `< 2^32` allocations onto
    `allocCandidate` addresses before `Return` (`storageLiveArgRet5_*`), a
    4-block diamond CFG merging asymmetric moved-out sets (outgoing `[1]` and
    `[2, 1]` joining to `[1, 2]` at `bb3`) across both `SwitchInt` branches
    (`diamondMoveJoinTrue_*`, `diamondMoveJoinFalse_*`), `Operand::Move`
    across `UnaryOp(Neg, move _1)`, `Cast(IntToInt, move _2, u32)`,
    `UnaryOp(Not, move _4)` (self-assign move),
    `Aggregate(Tuple, [move _3, move _4])`, and projected `Use(move (_5.0))`
    (`tupleAggCastMoveNeg5_*`, plus `ctx0_ok_trailing_temp_addrs` verifying
    that `CtxOk.addrs` bounds only `i ≤ argCount`), and `Cast(IntToInt, move _3,
    u32)` from a moved `bool` together with `StorageLive`,
    `BinaryOp(Cmp, move _, move _)`, `Use(move _5)`, `Deinit`, and `StorageDead`
    on a `core::cmp::Ordering` temporary local reusing `_4`'s freed `2^32`
    address and a concrete Park-induction certificate witness
    (`ordBoolCastTempMove_movesOk_by_preFixedPoint`,
    `ordBoolCastTempMoveTrue_*`, `ordBoolCastTempMoveFalse_*`).
  - `deadRead`, `deadAssign`, `deadDeinit`, and `deadPlaceMention`: reading,
    assigning, de-initializing, or mentioning (including projected `_1.0`) a
    temporary after `StorageDead` is UB in both models (`mirCall_ub`,
    `mirCall_steps_error`, `mirCall_outcome`, and direct runs).
  - `moveReuse`, `crossBlockMoveReuse`, `loopBackEdgeReuse`,
    `projAssignMoveReuse`, `projFieldMoveReuse`, `sameRvalueMoveReuse`,
    `moveRetPlace`, and `diamondHalfMoveReuse`: intra-block, cross-block,
    cyclic back-edge, projected-assignment, projected-field-after-root-move,
    intra-rvalue (`readsOk`), `Return`-terminator (`termReadsOk`), and
    one-armed diamond-merge bodies that read a local after moving out of it;
    `movesOk` rejects all eight, and the models disagree on `moveReuse(7)`,
    `loopBackEdgeReuse(1)`, `projFieldMoveReuse(11, true)`,
    `sameRvalueMoveReuse(5)`, `moveRetPlace`, and
    `diamondHalfMoveReuse(false, 7)`.
  - `unmarkedTempAssign`, `storageDeadRet`, `storageDeadArg`,
    `storageDeadArgReadAfter`, and `projectedDeinit`: bodies exercising the
    soundness and well-formedness boundaries of `mentionsOk`, `storageDeadOk`
    (for both `_0` and arguments at `i = argCount`), and projection-free
    `Deinit`, accompanied by concrete execution and UB witnesses.
  - Direct ground-truth checks for `BM.allocate` (`!x86_64.valid_size` UB), all
    six `BM.deallocate` UB diagnostics including exact `AllocationKind`
    formatting across all five `AllocationKind` variants
    (`bm_allocate_and_deallocate_ub_cases`), and
    `evalStatement (.Deinit ..)` / `CM.deinit` on live, dead, out-of-bounds,
    and misaligned targets (`evalStatement_deinit_ok_dead_and_misaligned`).
  - Every pre-existing witness is re-proved against the new relation (the
    `bb0` relations now follow from `step_start`).

## Step 0: environment

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
git log --oneline 2a961564..HEAD   # the [adv A0] .. checkpoints of MR-1.3
git status --porcelain             # pass: no output
```

## Step 1: repository hygiene

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```

Pass: both exit `0` (the marker check finds no unresolved-work markers; the
trusted-base audit prints `PASS`).

## Step 2: anchors and quotations

```bash
cargo test -p anneal-minirust-gen --offline
```

Pass: every test passes, in particular
`anchors_match_generated_items_and_cover_interp` (58 anchors) in
`tests/pipeline.rs` and
`storage_live_dead_deinit_move_and_init_block_quotations_are_pinned` and
`quotations_occur_upstream` in `tests/quotes.rs`.

## Step 3: Lean proofs and audit

```bash
cd examples
anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec 2>&1 | tee /tmp/mr13-build.log
grep -E '\[(ANCHOR|SIMULATION|WITNESS)-AUDIT\]|exhaustively verified' /tmp/mr13-build.log
cd ..
```

Pass: `Build completed successfully`, with:

```text
[ANCHOR-AUDIT] decls=2 axioms=[] sorry_free=true
[SIMULATION-AUDIT] decls=175 axioms=[propext, Classical.choice, Quot.sound] sorry_free=true
[WITNESS-AUDIT] decls=377 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
MiniRustSpec.Audit: exhaustively verified standard axioms for 10390 declarations across all MiniRustSpec.* modules
```

(`lake` prints already-built modules without re-running them; to see the audit
lines again after a successful build, touch
`minirust/lean/MiniRustSpec/Audit.lean` first.)

## Step 4: spot checks

- `inFragment tempMove = true`, `alwaysStorageLiveLocals tempMove = [4]`, and
  `initLen tempMove = 2` are proved by `decide` in `Witness.lean`.
- `tempMove3_minirust_direct` states the full allocation list after the
  return: `live = [true, false, false, false, false, false, false]` and
  addresses `[64, 128, 256, 2^32, 2 * 2^32, 3 * 2^32, 2 * 2^32]`.
- `inFragment crossBlockMove = true`, `crossBlockMove_movedAtEntry`,
  `inFragment loopTempMove = true`, `loopTempMove_movedAtEntry_multiPass`,
  `inFragment storageLiveArgRet = true`, `inFragment diamondMoveJoin = true`,
  `diamondMoveJoin_movedAtEntry`, `inFragment tupleAggCastMove = true`,
  `inFragment ordBoolCastTempMove = true`, and
  `ordBoolCastTempMove_movedAtEntry` are proved by `decide`, showing that
  `movesOk` accepts moving `_1` in `bb0`, propagating live temporaries across `Goto` and `SwitchInt` edges, converging
  across cyclic loop back-edges and diamond merges, moving across `UnaryOp`,
  `Cast(IntToInt)` (both integer and `bool` operands), `Aggregate(Tuple, ..)`,
  and `Ordering` temporaries (`BinaryOp(Cmp, ..)`, `Use`, `Deinit`,
  `StorageDead`), and re-allocating argument/return locals via `StorageLive`.
- `moveReuse_not_inFragment`, `crossBlockMoveReuse_movesOk`,
  `loopBackEdgeReuse_movesOk`, `projAssignMoveReuse_movesOk`,
  `projFieldMoveReuse_movesOk`, `sameRvalueMoveReuse_movesOk`,
  `moveRetPlace_movesOk`, `diamondHalfMoveReuse_movesOk`,
  `unmarkedTempAssign_rejected`, `storageDeadRet_rejected`,
  `storageDeadArg_rejected`, `storageDeadArgReadAfter_rejected`, and
  `projectedDeinit_rejected` are proved by `decide`, so none of the fragment's
  side-conditions is vacuous.

## Known limitations

- `movesOk` is path-insensitive across control-flow merges (`movedAtEntry`
  takes the union of moved-out locals over incoming CFG edges; see
  `minirust/README.md`, Gaps).
- Temporaries without storage markers must be unmentioned.
- Results hold for the first-fit resolution of `pick`.
