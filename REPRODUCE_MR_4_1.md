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
  `call_return_and_multi_fn_quotations_are_pinned` pins 20 verbatim quotations
  across `spec/mem/pointer.md`, `spec/lang/types.md`,
  `spec/lang/step/expressions.md`, `spec/lang/machine.md`,
  `spec/lang/step/terminators.md`, `tooling/minimize/src/ty.rs`,
  `tooling/minimize/src/bb.rs` (including the call edge's
  `fn_abi_of_instance` / `translate_calling_convention(abi.conv)` source of
  `conv`), and `tooling/minimize/src/program.rs` (including `get_fn_name`'s
  first-reference numbering), checking upstream matches, tampered-quote
  rejection, cross-file misattribution rejection across all 8 files, and
  `extract_quotes` against `Interp.lean` and `Correspondence/Translate.lean`.
- **Multi-function translation and `progInFragment`**
  (`minirust/lean/MiniRustSpec/Correspondence/Translate.lean`):
  - `translateCallConv` (`CallConv.rust => CallingConvention.Rust`,
    `CallConv.c => CallingConvention.C`, rejecting unsupported ABIs per
    `tooling/minimize/src/ty.rs:348`), `fnNameMap` (numbering callees in list
    order, which agrees with `minimize`'s first-reference numbering up to a
    renaming of `FnName`s that the fragment cannot observe), `lookupFnTarget`
    (the call edge carries the callee's own calling convention, as `minimize`
    derives it from `fn_abi_of_instance`),
    `translateCallArg` (`Operand::Move => ArgumentExpr::InPlace`,
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
  - Translation faithfulness lemmas (`translateFnInProg_eq_translateFn_of_no_calls`,
    `translateBlocksInProg_eq_of_no_calls`,
    `translateTerminatorInProg_eq_of_not_call`, `translateUnwindAction_spec`,
    `mkStartFn_spec`, `translateCallConv_eq_some_iff`,
    `lookupFnName_of_lookupFnTarget`, `lookupFnTarget_zipIdx_aux`),
    `multi_step_correspondence`, `multi_step_start`,
    `initMachineStateWithCallees_startRel`, and the full `Run.lean` suite
    `mirCallWithCallees_{ret, ub, ub_rel, noUB, steps_error, progress,
    progress_any, outcome, outcome_any, diverges_steps_ok, diverges_rel}`
    (preserving all single-body `MR-1.1..1.3` theorems with zero regressions),
    where `multi_run_ub_rel` / `mirCallWithCallees_ub_rel` localize forward UB
    to a step taken from a `MultiStateRel`-related machine, which
    `MultiStateRel.not_returnRel` shows is never a `ReturnRel` state (so the
    fault belongs to `entry` or a callee, not to the external caller).
- **Witnesses & audit** (`Witness.lean`, `Audit.lean`):
  - `callerMain`/`calleePair` (`ByValue` + `InPlace` `(u32, bool)` tuple call,
    `initLen calleePair = 2`, overflow and non-overflow paths, mid-call stack
    depth `3` snapshot, and arbitrary-`n` `mirCallWithCallees_{progress_any,
    outcome_any}`), `projDestCaller` (`_0.0` and `_0.1` projected call
    destinations), `chainEntry -> chainMid -> chainLeaf` (3-deep call stack,
    `Ordering` ABI), `cAbiCaller`/`cAbiCallee` (`CallConv.c` ABI),
    `diamondCallEntry -> {diamondMidA, diamondMidB} -> cAbiCallee` (diamond DAG
    call graph mixing `.Rust` and `.C` ABIs and sharing leaf `cAbiCallee`),
    `callArgUbCaller`, `calleeDivZeroCaller`, `calleeRetUninitCaller` (UB on a
    callee's `Return` of an uninitialized `_0`, localized by
    `mirCallWithCallees_ub_rel`), `callMoveReuse`, `callSpinCaller` (diverging
    call/return cycle), `liveCallDestSpinCaller` (divergence inside a callee
    that never returns, stack depth `3` forever), `moveReinitByCall` (root call
    destination re-initializing a moved-out local), `condCallMoveJoin`
    (branch-correlated `InPlace` call move across a CFG join), and ground-truth
    `Interp` unit checks.
  - Necessity witnesses: `deadCallDestSpinCaller` (dead return place, diverging
    callee), `abiArgMismatchCaller` and `abiRetMismatchCaller` (parameter and
    return types), `argCountMismatchCaller` (argument count),
    `callDestArgAlias` (return place read by an argument), and
    `callProjMoveReuse` (projected `move` argument) are rejected by
    `progInFragment` and refute the conclusion of `mirCallWithCallees_noUB`
    (`*_noUB_transfer_fails`: Anneal's tree is `MirNoUBTree`, yet MiniRust
    raises UB before any root return, via `no_returnRel_before`), while
    `uninitProjCallDestCaller` (uninitialized tuple under a projected return
    place) and `stmtMoveThenCallArg` (stale argument after a statement `move`)
    refute the conclusion of `mirCallWithCallees_ub` (`*_ub_transfer_fails`:
    Anneal reaches UB, yet MiniRust never raises UB, via
    `never_ub_of_nonUb_stop`); `deadCallDestSpin_hyps` checks that every other
    hypothesis of `mirCallWithCallees_noUB` holds for `deadCallDestSpinCaller`.
    `deadCallDestCaller` (dead return place with a returning callee, where both
    semantics fault), `recCycleA`/`recCycleB`, and
    `badCallConvCallee`/`badCallConvSysvBody`/`badCallConvCaller` mark the
    remaining boundaries.

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
`anchors_match_generated_items_and_cover_interp` (`61` anchors, `>= 226`
`[SIMULATION-AUDIT]` theorems, `>= 560` `[WITNESS-AUDIT]` theorems) in
`tests/pipeline.rs` and `call_return_and_multi_fn_quotations_are_pinned` (`20`
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
[SIMULATION-AUDIT] decls=226 axioms=[propext, Classical.choice, Quot.sound] sorry_free=true
[WITNESS-AUDIT] decls=560 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
MiniRustSpec.Audit: exhaustively verified standard axioms for 11969 declarations across all MiniRustSpec.* modules
```

(`lake` prints already-built modules without re-running them; to see the audit
lines again after a successful build, touch
`minirust/lean/MiniRustSpec/Audit.lean` first.)

## Step 4: spot checks

- `callerCallee_inFragment`, `projDestCaller_inFragment`, `chain3_inFragment`,
  `callArgUb_inFragment`, `calleeDivZero_inFragment`, `callSpin_inFragment`,
  `callMoveReuse_inFragment`, `moveReinitByCall_inFragment`,
  `condCallMoveJoin_inFragment`, `cAbi_inFragment`, `diamondCall_inFragment`,
  `liveCallDestSpin_inFragment`, and `calleeRetUninit_inFragment` are proved
  `= true` by `decide` in `Witness.lean`.
- `callerCallee20_midCall_step5`, `chainNeg5_depth4_step7`, and
  `liveCallDestSpin_depth3_step20` inspect live mid-call MiniRust machine
  states (stack depths `3`, `4`, and `3`, plus `Uninit` deinitialization of
  `InPlace`-moved caller locals) by `decide +kernel`.
- `deadCallDestSpin_rejected` shows that only `callDestOk`'s liveness conjunct
  rejects `deadCallDestSpinCaller` (`movesOk`, `mentionsOk`, `storageDeadOk`,
  `livenessOk`, and `tupleInitOk` all hold), and
  `deadCallDestSpin_noUB_transfer_fails` shows that admitting it would falsify
  `mirCallWithCallees_noUB`: Anneal runs forever without UB, while MiniRust
  faults with `"access to a dead local"` at step `4`.
- `abiArgMismatch_noUB_transfer_fails`, `abiRetMismatch_noUB_transfer_fails`,
  `argCountMismatch_noUB_transfer_fails`,
  `callDestArgAlias_noUB_transfer_fails`,
  `callProjMoveReuse_noUB_transfer_fails`,
  `uninitProjCallDest_ub_transfer_fails`, and
  `stmtMoveThenCallArg_ub_transfer_fails` refute the conclusions of the
  transfer theorems for the corresponding rejected callers, so none of these
  side-conditions of `progInFragment` is vacuous.

## Known limitations

- Direct monomorphic calls over acyclic static call graphs (`maxStackLocals <
  2^31`) only; recursive call cycles, indirect function-pointer or virtual
  calls, and stack unwinding across frames remain outside `progInFragment` (see
  `minirust/README.md`, Gaps).
- Statement/switch `movesOk` remains path-insensitive at CFG joins (whereas
  `Call` `Operand::Move` lowers via `ArgumentExpr::InPlace` and writes `Uninit`
  in both semantics).
- The single-body forward UB theorems (`run_ub`, `mirCall_ub`) and
  `mirCallWithCallees_ub` do not by themselves locate the UB before the root
  return; `mirCallWithCallees_ub_rel` does for multi-function programs.
- `mkStartFn` calls the entry with `CallingConvention::Rust` (as `minimize`
  does), so an `extern "C"` entry would fault if run from `prog.start`; the
  theorems start at `fEntry.start` and are unaffected.
