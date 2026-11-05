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
  `allocate` helpers listed in the `impl_BasicMemory__allocate` anchor.
- **Quotation checks** (`crates/anneal-minirust-gen/tests/quotes.rs`):
  `storage_live_dead_deinit_move_and_init_block_quotations_are_pinned` pins 15
  upstream quotations (`valid_size`, `overlaps`, `allocate` and its `pick`
  predicate, `try_mutate_cur_frame`, `deinit`, `Deinit`, `storage_live`,
  `storage_dead`, the `StorageLive`/`StorageDead` statements, `minimize`'s
  `Move` operand and storage-statement translations, its init block, and
  `spec/lang/well-formed.md`'s `Statement::StorageDead` restriction),
  rejects tampered variants, and rejects file misattribution.
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
    possibly moved-out local before writing it again via forward CFG dataflow
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
    above the caller's belongs to a mapped local.
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
    terminator of the extended fragment, including the dead-local UB cases;
    `step_start` runs the init block in `initLen body` MiniRust steps; all
    `Run.lean` theorems (`mirSimRun`) are re-proved, with the `*_from_start`
    step counts `initLen body + n`.
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
    (`crossBlockMove20_*`, `crossBlockMoveOv_*`).
  - `deadRead`: reading a temporary after `StorageDead` is UB in both models
    (`mirCall_ub`, `mirCall_steps_error`, `mirCall_outcome`, and direct run).
  - `moveReuse` and `crossBlockMoveReuse`: intra-block and cross-block bodies
    that read a local after moving out of it; `movesOk` rejects both
    (`moveReuse_not_inFragment`, `crossBlockMoveReuse_movesOk`), and the models
    disagree on `moveReuse(7)` (`moveReuse7_anneal_ub`,
    `moveReuse7_minirust_direct`).
  - `unmarkedTempAssign`: a body that assigns to and reads a temporary without
    `StorageLive`/`StorageDead` markers; `mentionsOk` rejects it
    (`unmarkedTempAssign_rejected`), and the models disagree on it because
    `initBlock` allocates `_1` in MiniRust while Anneal starts `_1` dead
    (`unmarkedTempAssign_anneal_ub`, `unmarkedTempAssign_minirust_direct`).
  - Direct ground-truth checks for `BM.allocate` (`!x86_64.valid_size` UB), all
    six `BM.deallocate` UB diagnostics (`bm_allocate_and_deallocate_ub_cases`),
    and `evalStatement (.Deinit ..)` / `CM.deinit` on live, dead, out-of-bounds,
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

Pass: every test passes, in particular `anchors_match_generated_items_and_cover_interp`
(58 anchors) in `tests/pipeline.rs` and
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
[SIMULATION-AUDIT] decls=152 axioms=[propext, Classical.choice, Quot.sound] sorry_free=true
[WITNESS-AUDIT] decls=251 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
MiniRustSpec.Audit: exhaustively verified standard axioms for 10018 declarations across all MiniRustSpec.* modules
```

(`lake` prints already-built modules without re-running them; to see the audit
lines again after a successful build, touch `minirust/lean/MiniRustSpec/Audit.lean`
first.)

## Step 4: spot checks

- `inFragment tempMove = true`, `alwaysStorageLiveLocals tempMove = [4]`, and
  `initLen tempMove = 2` are proved by `decide` in `Witness.lean`.
- `tempMove3_minirust_direct` states the full allocation list after the
  return: `live = [true, false, false, false, false, false, false]` and
  addresses `[64, 128, 256, 2^32, 2 * 2^32, 3 * 2^32, 2 * 2^32]`.
- `inFragment crossBlockMove = true` and `crossBlockMove_movedAtEntry` are
  proved by `decide`, showing that `movesOk` accepts moving `_1` in `bb0` and
  propagating live temporaries across `Goto` and `SwitchInt` edges.
- `moveReuse_not_inFragment`, `crossBlockMoveReuse_movesOk`, and
  `unmarkedTempAssign_rejected` are proved by `decide`, so the fragment check
  is not vacuous for intra-block move reuse, cross-block move reuse, or
  unmarked temporaries.

## Known limitations

- `movesOk` is path-insensitive across control-flow merges (`movedAtEntry` takes
  the union of moved-out locals over incoming CFG edges; see `minirust/README.md`, Gaps).
- Temporaries without storage markers must be unmentioned.
- Results hold for the first-fit resolution of `pick`.
