<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproducing `MR-4.1`: multi-frame `Terminator::Call` & `Return` stack simulation

This guide lets an independent reviewer check every claim of work unit
`MR-4.1` from a clean checkout of branch `adv/mr-4-1`. Run all commands from
the repository root. Each step lists the command and the output that counts
as a pass.

## What `MR-4.1` adds

- **MiniRust interpretation** (`minirust/lean/MiniRustSpec/Interp.lean`):
  - `Constant::{FnPointer, GlobalPointer, VTablePointer,
    PointerWithoutProvenance}` in `evalConstant`
    (`spec/lang/step/expressions.md`) and `Machine::fn_from_ptr`
    (`spec/lang/machine.md:332`).
  - `PtrType::{safe_pointee, meta_kind}` (`spec/mem/pointer.md`),
    `LayoutStrategy::meta_kind`, and `Type::layout` across all nine `Type`
    variants including `Type::Ptr` (thin `8`-byte vs wide `16`-byte pointers)
    and `Type::Array` (`spec/lang/types.md`).
  - `check_abi_compatibility` (`spec/lang/step/terminators.md:71`) across all
    seven sized `Type` variants (`Int`, `Bool`, `Ptr`, `Tuple`, `Array`,
    `Union`, and `Enum` including recursive `Discriminator` comparison).
  - `Machine::prepare_for_inplace_passing`, `Machine::eval_argument` (`ByValue`
    and `InPlace`), `Machine::create_frame` (allocating `func.ret` and
    `func.args`, checking calling convention, return ABI, argument count, and
    per-parameter ABI before storing argument values), `Machine::eval_call`, and
    `Terminator::Call` (`spec/lang/step/terminators.md:138-289`), together with
    multi-frame `Terminator::Return` (`StackPopAction::BackToCaller` and
    `BottomOfStack`, `spec/lang/step/terminators.md:323`).
- **Anchors** (`minirust/lean/MiniRustSpec/Anchors.lean`): 61 anchors (up from
  58 in `MR-1.3`), anchoring every spec-transcribing `def` in `Interp.lean` by
  `rfl` against `MiniRustSpec.Generated.Items.*` (`anchors_ok`,
  `anchors_nodup`).
- **Quotation & pipeline checks**
  (`crates/anneal-minirust-gen/tests/{quotes,pipeline}.rs`):
  `call_return_and_multi_fn_quotations_are_pinned` pins 17 verbatim quotations
  across `spec/mem/pointer.md`, `spec/lang/types.md`,
  `spec/lang/step/expressions.md`, `spec/lang/machine.md`,
  `spec/lang/step/terminators.md`, `tooling/minimize/src/bb.rs`, and
  `tooling/minimize/src/program.rs`, checking upstream matches, tampered-quote
  rejection, cross-file misattribution rejection across all 7 files, and
  `extract_quotes` against `Interp.lean` and `Correspondence/Translate.lean`.
- **Multi-function translation and `progInFragment`**
  (`minirust/lean/MiniRustSpec/Correspondence/Translate.lean`):
  - `fnNameMap`, `translateCallArg` (`Operand::Move => ArgumentExpr::InPlace`,
    `Copy`/`Constant => ArgumentExpr::ByValue`), `translateUnwindAction`
    (`Continue`, `Unreachable`, `Terminate`, `Cleanup`),
    `translateTerminatorInProg`, `translateBlocksInProg`, `translateFnInProg`,
    `mkStartFn`, and `translateProg`.
  - Greatest-fixed-point CFG must-liveness (`liveAtEntry`, `livenessOk`) and
    must-initialized `(Int, bool)` 2-tuple tracking (`tupleInitAtEntry`,
    `tupleInitOk`), ensuring every `Call` return place (`_dst`, `_dst.0`, or
    `_dst.1`) is live and type/projection-compatible when MiniRust runs
    `prepare_for_inplace_passing(ret_place)` prior to argument evaluation.
  - `termReadsOk` checks `readsOk (dst :: mo) argOps` (forbidding `argOps` from
    reading either stale locals in `mo` or `dst`, allowing `_dst ∈ mo` when
    overwriting a root destination `⟨dst, []⟩`, and requiring `!mo.contains dst`
    on projected tuple-field destinations `⟨dst, _ :: _⟩`), while `termMoved`
    clears root `dst` from `mo` without polluting `mo` with
    `ArgumentExpr::InPlace` moves (which write `Uninit` bytes in MiniRust too).
  - `maxStackLocals entry callees < 2^31` bounds worst-case stack-local
    allocations across acyclic static call graphs.
- **Multi-frame stack simulation & run theorems**
  (`Relation.lean`, `Lemmas.lean`, `MiniRustEval.lean`, `AnnealEval.lean`,
  `Simulation.lean`, `Run.lean`):
  - `ProgEnvOk`, `CallerDestRel`, `CallStackRel`, `MultiStateRel`,
    `MultiStartRel`, and `MultiStepRel` (`1 ≤ k` MiniRust steps with
    `Interp.steps k m = .ok m'`, matching `1 + initLen callee` steps on
    `TerminatorKind.call` and `1` step on nested `Return` / root `Return` /
    statements / branches, while `steps_ok_mono` prevents any intermediate error
    at `j < k` from hiding).
  - `multi_step_correspondence`, `multi_step_start`,
    `initMachineStateWithCallees_startRel`, and the full `Run.lean` suite
    `mirCallWithCallees_{ret, ub, noUB, steps_error, progress, progress_any,
    outcome, outcome_any, diverges_steps_ok, diverges_rel}` (preserving all
    single-body `MR-1.1..1.3` theorems with zero regressions).
- **Witnesses & audit** (`Witness.lean`, `Audit.lean`):
  - `callerMain`/`calleePair` (`ByValue` + `InPlace` `(u32, bool)` tuple call,
    `initLen calleePair = 2`, overflow and non-overflow paths, mid-call stack
    depth `3` snapshot, and arbitrary-`n` `mirCallWithCallees_{progress_any,
    outcome_any}`), `projDestCaller` (`_0.0` and `_0.1` projected call
    destinations), `chainEntry -> chainMid -> chainLeaf` (3-deep call stack,
    `Ordering` ABI), `callArgUbCaller`, `calleeDivZeroCaller`, `callMoveReuse`,
    `callSpinCaller` (diverging call/return cycle), `moveReinitByCall` (root
    call destination re-initializing a moved-out local), `condCallMoveJoin`
    (branch-correlated `InPlace` call move across a CFG join), negative boundary
    witnesses (`callDestArgAlias`, `callProjMoveReuse`, `stmtMoveThenCallArg`,
    `recCycleA`/`recCycleB`), and ground-truth `Interp` unit checks.

## Step 0: environment

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
git log --oneline 41bc68d1..HEAD   # the [adv A0] .. checkpoints of MR-4.1
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

Pass: all `22` tests (`8` unit + `7` pipeline + `7` quotes) pass, including
`anchors_match_generated_items_and_cover_interp` (`61` anchors, `>= 213`
`[SIMULATION-AUDIT]` theorems, `>= 479` `[WITNESS-AUDIT]` theorems) in
`tests/pipeline.rs` and `call_return_and_multi_fn_quotations_are_pinned` (`17`
pinned `MR-4.1` quotations) in `tests/quotes.rs`.

## Step 3: Lean proofs and audit

```bash
cd examples
anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec 2>&1 | tee /tmp/mr41-build.log
grep -E '\[(ANCHOR|SIMULATION|WITNESS)-AUDIT\]|exhaustively verified' /tmp/mr41-build.log
cd ..
```

Pass: `Build completed successfully`, with:

```text
[ANCHOR-AUDIT] decls=2 axioms=[] sorry_free=true
[SIMULATION-AUDIT] decls=213 axioms=[propext, Classical.choice, Quot.sound] sorry_free=true
[WITNESS-AUDIT] decls=479 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
MiniRustSpec.Audit: exhaustively verified standard axioms for 11701 declarations across all MiniRustSpec.* modules
```

(`lake` prints already-built modules without re-running them; to see the audit
lines again after a successful build, touch
`minirust/lean/MiniRustSpec/Audit.lean` first.)

## Step 4: spot checks

- `callerCallee_inFragment`, `projDestCaller_inFragment`, `chain3_inFragment`,
  `callArgUb_inFragment`, `calleeDivZero_inFragment`, `callSpin_inFragment`,
  `callMoveReuse_inFragment`, `moveReinitByCall_inFragment`, and
  `condCallMoveJoin_inFragment` are proved `= true` by `decide` in
  `Witness.lean`.
- `callerCallee20_midCall_step5` and `chainNeg5_depth4_step7` inspect live
  mid-call MiniRust machine states (stack depths `3` and `4`, plus `Uninit`
  deinitialization of `InPlace`-moved caller locals) by `decide +kernel`.
- `callDestArgAlias_movesOk`, `callDestArgAlias_rejected`,
  `callProjMoveReuse_rejected`, `stmtMoveThenCallArg_rejected`, and
  `recCycle_rejected` are proved `= false` by `decide`, accompanied by concrete
  execution/UB witnesses demonstrating why each side-condition of
  `progInFragment` is necessary.

## Known limitations

- Direct monomorphic calls over acyclic static call graphs (`maxStackLocals <
  2^31`) only; recursive call cycles, indirect function-pointer or virtual
  calls, and stack unwinding across frames remain outside `progInFragment` (see
  `minirust/README.md`, Gaps).
- Statement/switch `movesOk` remains path-insensitive at CFG joins (whereas
  `Call` `Operand::Move` lowers via `ArgumentExpr::InPlace` and writes `Uninit`
  in both semantics).
