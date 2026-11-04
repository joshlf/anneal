<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproducing `MR-1.1`: Booleans, comparisons, `Cmp`, `!b`, `bool` bitwise ops, `bool` switches

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
  has no Boolean negation, so `UnOp::Int` on a `bool` stays a spec panic. For
  MIR's `Cmp`, whose result is the `core::cmp::Ordering` enum, the
  representation of `Type::Enum` (`decode_discriminant`,
  `encode_discriminant`, `Type::{decode, encode}`, with `decode_discriminant`
  threading the `FnMut` accessor state `s : σ` and evaluating the `fallback`
  continuation only when no child branch matches), of `Type::Tuple` (sized
  tuples as variant data with padding encoded as `Uninit`, and unsized tuple
  layouts), and of `Type::Slice` and `Type::TraitObject` (`Type::layout`
  returning `LayoutStrategy::{Slice, TraitObject}` so the unsized panic
  branches of `LayoutStrategy::{expect_size, expect_align}` are reachable, and
  `Type::{decode, encode}` and `check_value` raising the exact upstream
  `specPanic`s). The recursion over nested types, fields, variants, and
  discriminator trees is structural, so the kernel evaluates it.
- **Anchors** (`minirust/lean/MiniRustSpec/Anchors.lean`): the upstream
  items `impl_Machine__transmute` (`spec/lang/representation.md:788`),
  `impl_Machine__eval_rel_op` (`spec/lang/step/operators.md:320`),
  `impl_Type__decode_4` (tuples, `representation.md:248`),
  `fn_decode_discriminant` (`:353`), `fn_encode_discriminant` (`:377`),
  `impl_Type__decode_7` (enums, `:393`), `impl_Type__decode_8` (slices, `:441`),
  `impl_Type__decode_9` (trait objects, `:450`), and
  `impl_TupleHeadLayout__capped_tail_align` (`spec/lang/types.md:200`),
  pinned by token hash and checked by `decide` (48 anchors in total).
- **Quotation checks** (`crates/anneal-minirust-gen/tests/quotes.rs`):
  `bool_comparison_and_transmute_quotations_are_pinned` and
  `enum_tuple_and_cmp_quotations_are_pinned` check each new upstream
  quotation in its vendored file, reject a one-token tampering of it and a
  misattribution to another file, and require the Lean sources to keep
  carrying it. `quotations_occur_upstream` checks every `> "..."`
  quotation in the hand-written Lean against its cited vendored file.
- **Translation** (`Correspondence/Translate.lean`): `bool` locals and
  constants (`Constant::Bool`, only for the bytes `0` and `1`), the
  comparisons `Eq | Ne | Lt | Le | Gt | Ge` on two integers of one type or two
  `bool`s (`BinOp::Rel`), `!b` on a `bool` as `minimize`'s `build::not`
  (`transmute::<bool>(1u8 - transmute::<u8>(b))`), `BitAnd | BitOr | BitXor`
  on two `bool` operands as `minimize`'s `build::bool_and`, `build::bool_or`,
  and `build::bool_xor` (`boolBitOp`: integer `BitAnd | BitOr | BitXor` on the
  `transmute::<u8>` views, transmuted back to `bool`),
  `Cast(CastKind::IntToInt)` from a `bool` operand (`CastOp::IntToInt(int_ty)`
  on `transmute::<u8>(b)`, matching `tooling/minimize/src/rvalue.rs`),
  `SwitchInt` on a `bool` through `transmute::<u8>`, exactly as
  `tooling/minimize/src/bb.rs` does, and `core::cmp::Ordering` locals with
  `Use(copy _j)` and the three-way comparison `BinaryOp(Cmp, a, b)` on two
  integers of one type or two `bool`s, which `minimize`
  (`tooling/minimize/src/rvalue.rs`) translates to
  `transmute::<Ordering>(BinOp::Rel(RelOp::Cmp, a, b))` (`translateCmp`); the
  translation of `Ordering` (`orderingTy`) is the one-byte enum with a
  directly encoded `i8` tag that `tooling/minimize/src/enums.rs` builds for
  `#[repr(i8)] enum Ordering { Less = -1, Equal = 0, Greater = 1 }`.
- **Correspondence** (`Relation.lean`, `Lemmas.lean`, `MiniRustEval.lean`,
  `AnnealEval.lean`, `Simulation.lean`): each local now has a fragment type
  (`tyOf`: an integer type, `Type::Bool`, or `orderingTy`); an initialized
  `bool` slot must hold `0` or `1`, an initialized `Ordering` slot one of the
  tags `255`, `0`, `1` (`ValidBits`, which for an enum means that the bytes
  decode), and so must the corresponding arguments (`argOk`). Anneal's
  `Cmp` result (`255`, `0`, or `1`) matches MiniRust's transmuted variant
  (`evalScalarBinOp_cmp_int`, `evalScalarBinOp_cmp_bool`,
  `evalValue_translateCmp`). The single-step theorem `step_correspondence`
  and everything `Run.lean` derives from it (`mirCall_ret`, `mirCall_ub`,
  `mirCall_noUB`, ...) hold for the extended fragment.
- **Witnesses** (`Correspondence/Witness.lean`): `cmpNotSwitch` (signed `<`,
  `==`, `!b`, `b > false`, two `SwitchInt`s on `bool`, four blocks),
  `leNeGe` (`<=`, `!=`, `>=`, a `bool` return place that is also a switch
  scrutinee), `boolCastI8` (`Cast(CastKind::IntToInt)` from `bool` to `i8`
  across both `true` and `false` branches plus `argsOk` rejection of invalid
  `bool` byte `2`), `uninitBool`, `uninitBoolNot`, `uninitBoolRel`, and
  `uninitBoolBitAnd` (UB on an uninitialized `bool` in `SwitchInt`,
  `UnaryOp(Not)`, `BinaryOp(Eq)`, and `BinaryOp(BitAnd)` in both semantics),
  `cmpSel` (an `Ordering` return place receiving a signed `i8` `Cmp` or a
  `bool` `Cmp`; the inputs `(-1, 1, true)`, `(7, 7, true)`, and `(0, 0, false)`
  return `Less`, `Equal`, and `Greater` in both semantics), `boolBitOrdUse`
  (exercising `BitAnd`, `BitOr`, and `BitXor` on `bool`, unsigned `u8`
  `255u8.cmp(&1u8) = Greater`, `Use(copy _3)` on an `Ordering` argument local,
  and `argsOk` rejection of invalid `Ordering` tag bytes `2` and `128`),
  `uninitOrdering` (returning an uninitialized `Ordering` is UB in both
  semantics), and ground-truth evaluations of the new operators,
  `decodeDiscriminant` short-circuiting (`decodeDiscriminant_short_circuits`),
  and the enum, tuple, slice, and trait-object representations.
- **Audit** (`minirust/lean/MiniRustSpec/Audit.lean`): `#check_theorem_deps`
  logs `[ANCHOR-AUDIT]`, `[SIMULATION-AUDIT]`, and `[WITNESS-AUDIT]` lines
  ending in `sorry_free=true`, and fails the build on `sorryAx` or any
  non-standard axiom.

An `Ordering` local is written by `Cmp` or `Use(copy _j)` and read by `Use` or
`Return`; the fragment has no `Ordering` constants, `Discriminant`, or
`SwitchInt` on an `Ordering`, and `Type::Enum`/`Type::Tuple` are interpreted
only as representations (no aggregate construction, discriminant statements, or
projections).

## Step 0: environment

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
git log --oneline 4ed6d2ab..HEAD   # the [adv A0] .. [adv A4] checkpoints
git status --porcelain             # pass: no output
```

Do not run `lake clean` or delete `examples/.lake`; the build cache is
reused, and all `lake` / `lean` invocations are wrapped in `anneal-lean-run`.

## Step 1: repository hygiene

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```

Pass: both exit with status `0`.

## Step 2: generator determinism and verbatim quotation checks

```bash
cargo test -p anneal-minirust-gen --offline
```

Pass: every test passes, in particular `quotations_occur_upstream`,
`fabricated_quotations_are_rejected`,
`bool_comparison_and_transmute_quotations_are_pinned`, and
`enum_tuple_and_cmp_quotations_are_pinned` in `tests/quotes.rs`,
and the determinism, freshness, recount, and tamper-detection tests in
`tests/pipeline.rs`. To check that the checked-in generated Lean is exactly
what the generator produces:

```bash
cargo run -q -p anneal-minirust-gen -- generate --check
```

## Step 3: kernel-check the Lean development

```bash
(cd examples && anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec)
```

Pass: `Build completed successfully`, with no `error:` lines and no
`declaration uses 'sorry'` warnings. The build compiles the interpretation,
the anchors (`anchors_ok`, `anchors_nodup` by `decide`), the correspondence
proofs, the witnesses (computed in the kernel by `decide`/`rfl`; no
`native_decide`), and the audit.

## Step 4: inspect the audit receipts

```bash
(cd examples && anneal-lean-run --mode file --concurrency 3 -- lake env lean ../minirust/lean/MiniRustSpec/Audit.lean 2>&1 \
  | grep -E '\[(ANCHOR|SIMULATION|WITNESS)-AUDIT\]|MiniRustSpec.Audit: exhaustively')
```

Pass: four lines of the form

```text
[ANCHOR-AUDIT] decls=2 axioms=[] sorry_free=true
[SIMULATION-AUDIT] decls=51 axioms=[propext, Classical.choice, Quot.sound] sorry_free=true
[WITNESS-AUDIT] decls=128 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
MiniRustSpec.Audit: exhaustively verified standard axioms for 8516 declarations across all MiniRustSpec.* modules
```

(the axiom lists contain only `propext`, `Quot.sound`, and
`Classical.choice`; the anchors are decided without any axiom).

## Step 5: spot-check the semantics by hand (optional)

The witnesses are ordinary Lean theorems; a reviewer can restate any of them
with a different expected value and watch the kernel reject it. For example,
save the following as a scratch file outside the repository and check it with
`(cd examples && anneal-lean-run --mode file --concurrency 3 -- lake env lean /path/to/Scratch.lean)`;
it must fail with a type mismatch, because both semantics return `-1i8` (byte
`255`), not `1`:

```lean
import MiniRustSpec.Correspondence.Witness
open MiniRustSpec MiniRustSpec.Interp MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
set_option maxRecDepth 8192 in
example : (Interp.steps 6 cmpNotNeg1MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 1 }, [1]) := rfl
```

Likewise, `Cmp` on `(-1i8, 1i8)` returns `Less` (byte `255`), so claiming
`Greater` (byte `1`, what an unsigned comparison of the bit patterns would
give) must fail:

```lean
import MiniRustSpec.Correspondence.Witness
open MiniRustSpec MiniRustSpec.Interp MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
set_option maxRecDepth 8192 in
example : (Interp.steps 4 cmpSelLessMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 1 }, [1]) := rfl
```
