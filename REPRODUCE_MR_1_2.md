<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Reproducing `MR-1.2`: Checked integer arithmetic (`Add/Sub/MulWithOverflow`) and `(Int, bool)` 2-tuples

This guide lets an independent reviewer check every claim of work unit
`MR-1.2` from a clean checkout of branch `adv/mr-1-2`. Run all commands from
the repository root. Each step lists the command and the output that counts
as a pass.

## What `MR-1.2` adds

- **MiniRust interpretation** (`minirust/lean/MiniRustSpec/Interp.lean`):
  - `IntType::with_overflow` (`spec/lang/types.md:45`), building `Type::Tuple`
    for `(self, Type::Bool)` with field 0 at offset `0`, field 1 at offset
    `self.size`, and total `TupleHeadLayout` size `2 * self.size` (aligned to
    `self.align` via `Align::align_to`), so any integer type with
    `self.size > 1` has `self.size - 1` trailing padding bytes.
  - `BinOp::IntWithOverflow` with all three `IntBinOpWithOverflow` variants
    (`Add`, `Sub`, `Mul`), transcribed from
    `Machine::eval_int_bin_op_with_overflow` and `Machine::eval_bin_op`
    (`spec/lang/step/operators.md:208,354`): evaluates `res` in mathematical
    `Int`, wraps it with `int_ty.bring_in_bounds(res)` (`res_wrapped`), and
    returns `(Value::Tuple([Value::Int(res_wrapped), Value::Bool(res != res_wrapped)]), int_ty.with_overflow())`.
  - `ValueExpr::Tuple` (`spec/lang/step/expressions.md:72`), evaluating each
    field expression in order (`evalValues`) and returning
    `(Value::Tuple(fields), ty)` (while static WF checks expression types and
    dynamic `check_value` / `Type::encode` validate field count and field values
    against `Type::Tuple` at `typed_store` / `typed_load`).
  - `PlaceExpr::Field` (`spec/lang/step/expressions.md:24`), evaluating the root
    place, indexing `(offset, field_ty)` in `Type::Tuple { sized_fields, unsized_field, sized_head_layout }`
    or `Type::Union { fields, .. }` (supporting both sized fields and an unsized
    tail field via `TupleHeadLayout::full_size_and_align` and
    `LayoutStrategy::compute_size_and_align`), checking in-bounds dereferenceability
    of the entire root tuple/union via `Machine::ptr_offset_inbounds`
    (`ConcurrentMemory::signed_dereferenceable` /
    `BasicMemory::signed_dereferenceable`), offsetting the thin pointer by
    `offset.bytes()`, and widening with `field_ty.layout().is_sized()`.
- **Anchors** (`minirust/lean/MiniRustSpec/Anchors.lean`): 5 new upstream items
  pinned by token hash and checked by `decide` (55 anchors in total, up from 50
  in `MR-1.1`):
  - `impl_IntType__can_represent` (`spec/lang/types.md:27`, containing `IntType::with_overflow`)
  - `impl_TupleHeadLayout__end` (`spec/lang/types.md:166`, containing `TupleHeadLayout::full_size_and_align`)
  - `impl_LayoutStrategy__is_sized` (`spec/lang/types.md:221`, containing `LayoutStrategy::compute_size_and_align`)
  - `impl_Memory_for_BasicMemory__new` (`spec/mem/basic.md:83`, containing `BasicMemory::dereferenceable` and `BasicMemory::signed_dereferenceable`)
  - `impl_Machine__eval_int_bin_op_with_overflow` (`spec/lang/step/operators.md:208`)
- **Quotation checks** (`crates/anneal-minirust-gen/tests/quotes.rs` and
  `tests/pipeline.rs`): `with_overflow_tuple_and_field_quotations_are_pinned`
  pins all 19 new upstream quotations across `Interp.lean` (`spec/lang/types.md`,
  `spec/mem/basic.md`, `spec/mem/concurrent.md`, `spec/lang/step/operators.md`,
  `spec/lang/step/expressions.md`) and `Translate.lean`
  (`tooling/minimize/src/{ty,rvalue,place}.rs`), rejects single-token tampering
  and file misattribution, and checks that `Anchors.lean` contains 55 anchors.
- **Translation** (`Correspondence/Translate.lean`):
  - `(Int, bool)` 2-tuple MIR types (`intBoolTupleOf` / `intBoolTupleTy it`,
    matching `tooling/minimize/src/ty.rs`'s `TyKind::Tuple` translation via
    `build::tuple_ty`), across all 10 `IntType`s (`i8..i128`, `isize`,
    `u8..u128`, `usize`).
  - Field projections `_j.0` and `_j.1` (`PlaceExpr::Field(PlaceExpr::Local(_j), 0)`
    and `PlaceExpr::Field(PlaceExpr::Local(_j), 1)`, matching
    `tooling/minimize/src/place.rs`'s `ProjectionElem::Field`), in both
    `Operand::Copy` (`copy (_j.0)`, `copy (_j.1)`) and `StatementKind::PlaceMention`
    (`PlaceMention(_j)`, `PlaceMention(_j.0)`, `PlaceMention(_j.1)`, matching
    `tooling/minimize/src/bb.rs`).
  - Checked binary operations `BinOp::AddWithOverflow`, `BinOp::SubWithOverflow`,
    and `BinOp::MulWithOverflow` (`translateCheckedBinOp`, matching
    `tooling/minimize/src/rvalue.rs` lines 169-174 and 291-295).
  - Tuple construction `Rvalue::Aggregate(AggregateKind::Tuple, [op0, op1])`
    (`ValueExpr::Tuple`, matching `tooling/minimize/src/rvalue.rs` lines 53-59).
- **Correspondence** (`Relation.lean`, `Lemmas.lean`, `MiniRustEval.lean`,
  `AnnealEval.lean`, `Simulation.lean`, `Run.lean`):
  - Extends `SlotOk`, `argOk`, `declSlotData`, `ReturnRel`, `LocalTy`,
    `opBits`, `opTupleBits`, and `rvTupleBits` to `(Int, bool)` 2-tuple locals
    and return places, proving that MiniRust encodes an initialized `(Int, bool)`
    slot as `tupleBytes it bits b` (`it.size.bytes` little-endian integer bytes
    at offset `0`, the `0`/`1` `bool` byte at offset `it.size.bytes`, and
    `it.size.bytes - 1` trailing `AbstractByte::Uninit` padding bytes) and an
    uninitialized slot as `2 * it.size.bytes` `Uninit` bytes.
  - Proves `evalPlace_field0`, `evalPlace_field1`, `typedLoad_local_tuple_field0`,
    `typedLoad_local_tuple_field0_uninit`, `typedLoad_local_tuple_field1`,
    `typedLoad_local_tuple_field1_uninit`, `evalStatement_placeMention_place`,
    `evalStmt_placeMention_place`, `evalBinOp_intWithOverflow`,
    `evalScalarBinOp_checked`, `evalValue_rvalueTuple`, `evalRvalue_fragTuple`,
    `evalStatement_assignTuple`, and `evalStmt_assignTuple`, establishing exact
    agreement between Anneal's `evalScalarBinOp` and MiniRust's
    `BinOp::IntWithOverflow` on both the wrapped integer result (`res % 2^(8*sz)`)
    and the overflow flag (`!can_represent(res)`) across all signed and unsigned
    integer types.
  - Preserves `step_correspondence` (`mirSimStep`) and all multi-step /
    interaction-tree theorems in `Run.lean` (`mirSimRun`: `run_ret`, `run_ub`,
    `steps_outcome`, `mirNoUB_safe`, `mirCall_ret`, `mirCall_ub`, `mirCall_noUB`,
    `mirCall_diverges_rel`, ...).
- **Witnesses** (`Correspondence/Witness.lean`):
  - `checkedArithI8`: a 5-block signed `i8` program with a `(i8, bool)` local
    `_3` and a `bool` local `_4`, exercising `AddWithOverflow`,
    `SubWithOverflow`, and `MulWithOverflow`, field projections `_3.0` and
    `_3.1` in `Use`, `BinaryOp`, `UnaryOp(Neg)`, and `SwitchInt`, proved both
    via `mirCall_ret` / `MirNoUBTree` and direct `Interp.steps` runs across:
    - no-overflow (`30i8 + 20i8 = (50, false)`, `50 - 1 = (49, false)`,
      `49 * 2 = (98, false) -> 98i8`, `checkedArithOk_*`),
    - `INT_MAX + 1` (`127i8 + 1i8 = (-128i8, true) -> -128i8`,
      `checkedArithAddOv_*`),
    - `INT_MIN - 1` (`-128i8 - 1i8 = (127i8, true) -> 127i8`,
      `checkedArithSubOv_*`),
    - signed multiplication overflow (`64i8 * 2i8 = (-128i8, true) -> -(-128i8) = -128i8`,
      `checkedArithMulOv_*`),
    - plus `argsOk` rejection of an invalid `bool` byte (`2 >= 2`) in a tuple
      argument (`checkedArithInvalidTupleArg_rejected`).
  - `checkedTupleU32`: a 3-block `(u32, u32) -> (u32, bool)` program returning a
    padded 8-byte `(u32, bool)` tuple (3 trailing `AbstractByte::Uninit` padding
    bytes), exercising `PlaceMention(_0)`, `PlaceMention(_0.0)`, and
    `PlaceMention(_0.1)` on the uninitialized tuple return place,
    `SubWithOverflow`, `AddWithOverflow`, `MulWithOverflow`, and
    `Aggregate(Tuple, [copy (_0.0), copy (_0.1)])` across:
    - unsigned `0u32 - 1u32 = (u32::MAX, true)` underflow followed by
      `UINT_MAX + 1` (`u32::MAX + 1u32 = (0u32, true)`,
      `checkedTupleUnderAddOv_*`),
    - unsigned multiplication overflow `65536u32 * 65536u32 = (0u32, true)` and
      `Aggregate(Tuple)` (`checkedTupleMulOv_*`),
    - no-overflow `(10u32, 3u32) -> (21u32, false)` (`checkedTupleOk_*`).
  - `uninitTupleField0` and `uninitTupleField1`: reading `_0.0` or `_0.1` from
    an uninitialized `(u32, bool)` local raises UB in both Anneal and MiniRust
    (`uninitTupleField0_*`, `uninitTupleField1_*`).
  - Ground-truth theorems (`withOverflow_i8_layout`, `withOverflow_u32_layout`,
    `tupleHeadLayout_full_sized_and_slice`, `evalBinOp_addWithOverflow_i8_max`,
    `evalBinOp_subWithOverflow_i8_min`, `evalBinOp_addWithOverflow_u32_max`,
    `evalBinOp_subWithOverflow_u32_zero`, `evalBinOp_mulWithOverflow_i8_min`,
    `evalBinOp_mulWithOverflow_u32`, `ptrOffsetInbounds_ok_and_oob`,
    `evalValue_tuple_and_evalPlace_field`, `evalBinOp_intWithOverflow_nonInt_panics`,
    `evalPlace_field_panics`).

## Step 0: environment

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
git log --oneline 1ed17c0f..HEAD   # the [adv A0] .. [adv A4] checkpoints
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

Pass: all 20 tests pass (`11` in `tests/pipeline.rs`, `9` in `tests/quotes.rs`,
including `with_overflow_tuple_and_field_quotations_are_pinned`).

## Step 3: kernel-check the Lean development

```bash
(cd examples && anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec)
```

Pass: `Build completed successfully`, with no `error:` lines and no
`declaration uses 'sorry'` warnings.

## Step 4: inspect the audit receipts

```bash
(cd examples && anneal-lean-run --mode file --concurrency 3 -- lake env lean ../minirust/lean/MiniRustSpec/Audit.lean 2>&1 \
  | grep -E '\[(ANCHOR|SIMULATION|WITNESS)-AUDIT\]|MiniRustSpec.Audit: exhaustively')
```

Pass: four lines of the form

```text
[ANCHOR-AUDIT] decls=2 axioms=[] sorry_free=true
[SIMULATION-AUDIT] decls=83 axioms=[propext, Classical.choice, Quot.sound] sorry_free=true
[WITNESS-AUDIT] decls=200 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
MiniRustSpec.Audit: exhaustively verified standard axioms for 9216 declarations across all MiniRustSpec.* modules
```
