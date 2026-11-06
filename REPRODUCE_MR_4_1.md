<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproducing `MR-4.1`: Multi-Frame `Terminator::Call` & `Return` Stack Simulation

This guide lets an independent reviewer check every claim of work unit
`MR-4.1` from a clean checkout of branch `adv/mr-4-1`. Run all commands from
the repository root. Each step lists the command and the output that counts
as a pass.

## What `MR-4.1` adds

- **MiniRust interpretation** (`minirust/lean/MiniRustSpec/Interp.lean`):
  - `Constant::FnPointer` in `eval_constant` and `Machine::fn_from_ptr`.
  - `check_abi_compatibility`.
  - `Machine::prepare_for_inplace_passing`, `Machine::eval_argument` (`ByValue` and `InPlace`), `Machine::create_frame`, `Machine::eval_call`, and `Terminator::Call`.
  - `Terminator::Return` supporting multi-frame stacks (`StackPopAction::BackToCaller`).
- **Anchors** (`Anchors.lean`): 61 anchors (up from 58).
- **Quotation checks** (`crates/anneal-minirust-gen/tests/quotes.rs`):
  `call_return_and_multi_fn_quotations_are_pinned` pins upstream quotations for all new interpretation functions.
- **Translation and fragment** (`Correspondence/Translate.lean`):
  - Translation of `TerminatorKind.call` in Anneal to `Terminator::Call` in MiniRust.
  - Multi-function translation (`translateProgFns`, `translateProg`).
  - `movesOk` properly accounts for `TerminatorKind.call`.
- **Correspondence** (`Relation.lean`, `MiniRustEval.lean`, `AnnealEval.lean`,
  `Simulation.lean`, `Run.lean`):
  - Multi-frame simulation (`CallStackRel`).
  - Handling of `Terminator::Call` step, including `initLen` startup steps for the callee.
- **Witnesses** (`Witness.lean`, `Audit.lean`):
  - Added multi-function witnesses and checks for calls, unwinding, and stack frame invariants.

## Step 0: environment

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
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

Pass: every test passes, including `anchors_match_generated_items_and_cover_interp` (61 anchors) in `tests/pipeline.rs` and `call_return_and_multi_fn_quotations_are_pinned` in `tests/quotes.rs`.

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
[SIMULATION-AUDIT] decls=209 axioms=[propext, Classical.choice, Quot.sound] sorry_free=true
[WITNESS-AUDIT] decls=458 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
MiniRustSpec.Audit: exhaustively verified standard axioms for 11641 declarations across all MiniRustSpec.* modules
```

## Step 4: spot checks

- Call stack UB witnesses are fully proved via `decide`.
