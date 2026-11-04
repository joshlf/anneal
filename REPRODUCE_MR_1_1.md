<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproducing `MR-1.1`: Booleans, comparisons, `!b`, and `SwitchInt` on `bool`

This guide lets an independent reviewer check every claim of work unit
`MR-1.1` from a clean checkout of branch `adv/mr-1-1`. Run all commands from
the repository root. Each step lists the command and the output that counts
as a pass.

## What `MR-1.1` adds

- **MiniRust interpretation** (`minirust/lean/MiniRustSpec/Interp.lean`):
  `CastOp::Transmute` through `Machine::transmute` (encode at the old type,
  decode and `check_value` at the new one; UB on a size mismatch or an
  invalid result such as the byte `2` at `bool`), `BinOp::Rel` with all seven
  `RelOp`s on integers (compared as mathematical integers) and Booleans
  (`false < true`), `RelOp::Cmp` returning `i8`, and `IntType::I8`. MiniRust
  has no Boolean negation, so `UnOp::Int` on a `bool` stays a spec panic.
- **Anchors** (`minirust/lean/MiniRustSpec/Anchors.lean`): the upstream
  items `impl_Machine__transmute` (`spec/lang/representation.md:788`) and
  `impl_Machine__eval_rel_op` (`spec/lang/step/operators.md:320`), pinned by
  token hash and checked by `decide` (41 anchors in total).
- **Quotation checks** (`crates/anneal-minirust-gen/tests/quotes.rs`):
  `bool_comparison_and_transmute_quotations_are_pinned` checks each new
  upstream quotation in its vendored file, rejects a one-token tampering of
  it and a misattribution to another file, and requires the Lean sources to
  keep carrying it. `quotations_occur_upstream` checks every `> "..."`
  quotation in the hand-written Lean against its cited vendored file.
- **Translation** (`Correspondence/Translate.lean`): `bool` locals and
  constants (`Constant::Bool`, only for the bytes `0` and `1`), the
  comparisons `Eq | Ne | Lt | Le | Gt | Ge` on two integers of one type or two
  `bool`s (`BinOp::Rel`), `!b` on a `bool` as `minimize`'s `build::not`
  (`transmute::<bool>(1u8 - transmute::<u8>(b))`), `Cast(CastKind::IntToInt)`
  from a `bool` operand (`CastOp::IntToInt(int_ty)` on `transmute::<u8>(b)`,
  matching `tooling/minimize/src/rvalue.rs`), and `SwitchInt` on a
  `bool` through `transmute::<u8>`, exactly as `tooling/minimize/src/bb.rs`
  does.
- **Correspondence** (`Relation.lean`, `Lemmas.lean`, `MiniRustEval.lean`,
  `AnnealEval.lean`, `Simulation.lean`): each local now has a fragment type
  (`tyOf`: an integer type or `Type::Bool`); an initialized `bool` slot must
  hold `0` or `1` (`ValidBits`), and so must a `bool` argument (`argOk`). The
  single-step theorem `step_correspondence` and everything `Run.lean` derives
  from it (`mirCall_ret`, `mirCall_ub`, `mirCall_noUB`, ...) hold for the
  extended fragment.
- **Witnesses** (`Correspondence/Witness.lean`): `cmpNotSwitch` (signed `<`,
  `==`, `!b`, `b > false`, two `SwitchInt`s on `bool`, four blocks),
  `leNeGe` (`<=`, `!=`, `>=`, a `bool` return place that is also a switch
  scrutinee), `boolCastI8` (`Cast(CastKind::IntToInt)` from `bool` to `i8`
  across both `true` and `false` branches plus `argsOk` rejection of invalid
  `bool` byte `2`), `uninitBool`, `uninitBoolNot`, and `uninitBoolRel` (UB on
  an uninitialized `bool` in `SwitchInt`, `UnaryOp(Not)`, and `BinaryOp(Eq)`
  in both semantics), and ground-truth evaluations of the new operators.
- **Audit** (`minirust/lean/MiniRustSpec/Audit.lean`): `#check_theorem_deps`
  logs `[ANCHOR-AUDIT]`, `[SIMULATION-AUDIT]`, and `[WITNESS-AUDIT]` lines
  ending in `sorry_free=true`, and fails the build on `sorryAx` or any
  non-standard axiom.

Three-way `Cmp` in MIR is not in the translated fragment: `minimize`
transmutes its `i8` result to the `Ordering` enum, and enum types are not
interpreted yet. The interpreted `RelOp::Cmp` itself is covered by
`relCmp_signed`, `relCmp_unsigned`, and `relCmp_bool`.

## Step 0: environment

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
git log --oneline 4ed6d2ab..HEAD   # the [adv A0] .. [adv A4] checkpoints
git status --porcelain             # pass: no output
```

Do not run `lake clean` or delete `examples/.lake`; the build cache is
reused.

## Step 1: repository hygiene

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```

Pass: both exit with status `0`.

## Step 2: generator determinism and verbatim quotation checks

The brief writes this step as
`cargo test --manifest-path minirust/Cargo.toml --offline`, but `minirust/`
has no `Cargo.toml`: the generator and its tests are the workspace crate
`crates/anneal-minirust-gen`. Run it from the workspace root:

```bash
cargo test -p anneal-minirust-gen --offline
```

Pass: every test passes, in particular `quotations_occur_upstream`,
`fabricated_quotations_are_rejected`, and
`bool_comparison_and_transmute_quotations_are_pinned` in `tests/quotes.rs`,
and the determinism, freshness, recount, and tamper-detection tests in
`tests/pipeline.rs`. To check that the checked-in generated Lean is exactly
what the generator produces:

```bash
cargo run -q -p anneal-minirust-gen -- generate --check
```

## Step 3: kernel-check the Lean development

```bash
(cd examples && lake build MiniRustSpec)
```

Pass: `Build completed successfully`, with no `error:` lines and no
`declaration uses 'sorry'` warnings. The build compiles the interpretation,
the anchors (`anchors_ok`, `anchors_nodup` by `decide`), the correspondence
proofs, the witnesses (computed in the kernel by `decide`/`rfl`; no
`native_decide`), and the audit.

## Step 4: inspect the audit receipts

```bash
(cd examples && lake build MiniRustSpec.Audit -v 2>&1 | grep -E '\[(ANCHOR|SIMULATION|WITNESS)-AUDIT\]')
```

If `lake` replays the cached build without printing messages, force the audit
module to be re-elaborated and print its messages directly:

```bash
(cd examples && lake env lean ../minirust/lean/MiniRustSpec/Audit.lean 2>&1 \
  | grep -E '\[(ANCHOR|SIMULATION|WITNESS)-AUDIT\]|MiniRustSpec.Audit: exhaustively')
```

Pass: three lines of the form

```text
[ANCHOR-AUDIT] decls=2 axioms=[] sorry_free=true
[SIMULATION-AUDIT] decls=37 axioms=[propext, Classical.choice, Quot.sound] sorry_free=true
[WITNESS-AUDIT] decls=69 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
```

(the axiom lists contain only `propext`, `Quot.sound`, and
`Classical.choice`; the anchors are decided without any axiom), plus the
exhaustive line
`MiniRustSpec.Audit: exhaustively verified standard axioms for N declarations
across all MiniRustSpec.* modules`.

## Step 5: spot-check the semantics by hand (optional)

The witnesses are ordinary Lean theorems; a reviewer can restate any of them
with a different expected value and watch the kernel reject it. For example,
save the following as a scratch file outside the repository and check it with
`(cd examples && lake env lean /path/to/Scratch.lean)`; it must fail with a
type mismatch, because both semantics return `-1i8` (byte `255`), not `1`:

```lean
import MiniRustSpec.Correspondence.Witness
open MiniRustSpec MiniRustSpec.Interp MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
set_option maxRecDepth 8192 in
example : (Interp.steps 9 cmpNotNeg1MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 1 }, [1]) := rfl
```
