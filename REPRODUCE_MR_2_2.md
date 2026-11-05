<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction Guide — `MR-2.2`: Padded Tuples & Structs (`TupleFields`, Offset Padding Preservation) & Nested `Field` Projections

This guide provides self-contained, step-by-step commands to independently
reproduce and audit the `MR-2.2` implementation, verbatim upstream MiniRust
specification/translator quote checks, and kernel-checked Lean 4 correspondence
proofs and witnesses.

## 1. Environment Setup

From the repository root (`/usr/local/google/Projects/anneal-workspace/anneal-wt-mr-2-2`):

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
```

## 2. Repository Hygiene & Trusted Base Audit

Verify that the hygiene check and Anneal's trusted-base audit pass:

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```

## 3. Mechanical MiniRust Generator & Verbatim Quote Verification

Run the offline test suite for `anneal-minirust-gen`, which checks:
- Deterministic regeneration of `minirust/lean/MiniRustSpec/Generated/*.lean`
  from the vendored MiniRust specification (`minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/`).
- Every `> "..."` quotation in `minirust/lean/MiniRustSpec/Interp.lean` and
  `minirust/lean/MiniRustSpec/Correspondence/Translate.lean` (including
  `TupleHeadLayout`, `Type::Tuple`, `LayoutStrategy::is_sized`,
  `LayoutStrategy::compute_size_and_align` for `LayoutStrategy::Tuple`,
  `Machine::compute_align`, `Type::layout` for `Type::Tuple` and `Type::Slice`,
  `Type::decode` and `Type::encode` for `Type::Tuple` preserving
  `AbstractByte::Uninit` in padding gaps, `check_value` for `Type::Tuple`,
  `PlaceExpr::Field` with its bounds check, offset computation, and
  `ptr_offset_inbounds`, `build_tuple`, `rs::TyKind::Tuple`, `rs::TyKind::Adt`
  struct layout translation, `smir::ProjectionElem::Field`,
  `smir::Rvalue::Aggregate(Tuple)`, and `smir::Rvalue::Aggregate(Adt)`) against
  the vendored MiniRust specification and `tooling/minimize/src/*.rs`:

```bash
cargo test -p anneal-minirust-gen --offline
```

## 4. Lean 4 Kernel Verification (`MiniRustSpec`)

Compile and kernel-check the full `MiniRustSpec` target (including
`MiniRustSpec.Interp`, `MiniRustSpec.Anchors`,
`MiniRustSpec.Correspondence.Translate`, `MiniRustSpec.Correspondence.Relation`,
`MiniRustSpec.Correspondence.Lemmas`, `MiniRustSpec.Correspondence.MiniRustEval`,
`MiniRustSpec.Correspondence.AnnealEval`, `MiniRustSpec.Correspondence.Simulation`,
`MiniRustSpec.Correspondence.Run`, `MiniRustSpec.Correspondence.Witness`, and
`MiniRustSpec.Audit`):

```bash
cd examples && anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec
```

## 5. Inspecting Anchor, Simulation, and Witness Axiom Audits

`MiniRustSpec/Audit.lean` fails the build unless every declaration of every
`MiniRustSpec.*` module depends only on Lean's standard axioms (`propext`,
`Quot.sound`, `Classical.choice`), and then audits three named groups with
`#audit_group`. Each `[...-AUDIT]` line is computed by that command: it
resolves every listed name, fails unless the name is a theorem whose axiom
closure has no `sorryAx` and only the standard axioms, and reports how many
theorems it checked. The groups are:

- `ANCHOR-AUDIT`: `anchors_ok` and `anchors_nodup` (`MiniRustSpec/Anchors.lean`).
- `SIMULATION-AUDIT`: `step_correspondence`, `initMachineState_startRel`, the
  `mirCall_*` theorems, the `MR-2.1` array lemmas, and the `MR-2.2` tuple and
  nested field projection lemmas (`evalPlace_fieldPath`, `evalPlace_tuplePlace`,
  `typedLoad_tuple_slice`, `typedStore_tuple_slice`, `decode_tupleSpec`,
  `encode_tupleSpec`, `checkValue_tupleSpec`, `evalValue_specOperand`,
  `evalValue_tupleRvalue`, `evalStatement_assign_tuple`,
  `evalStatement_assign_field_scalar`, `evalStatement_placeMention_field`,
  `evalStmt_assign_tuple`, `evalStmt_assign_field_scalar`, `evalRvalue_tuple_frag`,
  `resolveFieldPath_read`, `resolveFieldPath_write`).
- `WITNESS-AUDIT`: every `MR-2.1` array witness theorem and every `MR-2.2`
  tuple/struct witness theorem in `MiniRustSpec/Correspondence/Witness.lean`
  (`paddedStructOps_*`, `nestedTupleOps_*`, `nestedTupleOk_*`,
  `nestedTupleAggUb_*`, `nestedTupleFieldRhsUb_*`, `nestedTupleCopyUninitUb_*`,
  `tuple_encode_decode_place_edge_cases`).

```bash
cd examples && anneal-lean-run --mode file --concurrency 3 -- lake env lean ../minirust/lean/MiniRustSpec/Audit.lean | grep -E '\[(ANCHOR|SIMULATION|WITNESS)-AUDIT\]|exhaustively verified'
```

Expected audit summary lines:

```text
MiniRustSpec.Audit: exhaustively verified standard axioms for 9279 declarations across all MiniRustSpec.* modules
[ANCHOR-AUDIT] decls=2 theorems=2 sorry_free=true standard_axioms_only=true
[SIMULATION-AUDIT] decls=38 theorems=38 sorry_free=true standard_axioms_only=true
[WITNESS-AUDIT] decls=104 theorems=104 sorry_free=true standard_axioms_only=true
```

## 6. What the `MR-2.2` Witnesses Show

Each witness runs both semantics in the kernel (`decide`/`rfl`, no
`native_decide`) and transfers Anneal's outcome to MiniRust through
`mirCall_ret` / `mirCall_ub`:

- `paddedStructOps` (`struct Padded(u8, u32, u16)` with compiler layout
  `[(0, u8), (4, u32), (8, u16)]`, `end = 12`, `align = 4`): exercises
  whole-struct `Use(Copy)` (`_2 = copy _1`), `AggregateKind.adt` struct
  construction (`_1 = Padded(copy _2.0, 0x04030201_u32, copy _2.2)`), scalar
  `ProjectionElem.field` reads (`_2.0`, `_2.2`, `_1.0`, `_1.1`), and an
  in-place scalar field write (`_1.1 = Add(copy _1.1, 0x10_u32)` at byte offset
  `4`). `paddedStructOk_minirust_padding_bytes` proves at the byte level that
  MiniRust preserves `AbstractByte.Uninit` at the inter-field padding offsets
  `1..4` and trailing padding offsets `10..12` across whole-struct `Use(Copy)`,
  `Aggregate(Adt)`, and in-place field mutation while preserving sibling fields
  `_1.0` (offset `0`) and `_1.2` (offsets `8..10`).
- `nestedTupleOps` (`((u8, u32), u16, ())` with inner layout `size = 8, align = 4`,
  unit layout `size = 0, align = 1`, and outer layout `[(0, (u8, u32)), (8, u16), (10, ())]`,
  `end = 12, align = 4`): exercises zero-sized `()` construction
  (`Aggregate(Tuple, [])`) and `Use(Copy)` (`_3 = copy _4.2`), nested
  `Aggregate(Tuple)` construction, in-place whole sub-tuple writes
  (`_4.0 = Aggregate(Tuple, [9u8, copy _1])`), nested in-place scalar field
  writes (`_4.0.1 = Add(copy _4.0.1, 42u32)` at cumulative byte offset `0 + 4 = 4`),
  `PlaceMention` on nested field places (`PlaceMention(_4.0)` and `PlaceMention(_4.0.1)`),
  and nested field reads (`copy _4.0.0`, `copy _4.0.1`).
  `nestedTupleOk_minirust_padding_bytes` proves byte-level preservation of both
  inner padding (`1..4 = .Uninit`) and outer trailing padding (`10..12 = .Uninit`)
  as well as `0`-byte representation of `_3 : ()`. Also proves end-to-end UB
  correspondence across three faulting paths (`nestedTupleAggUb_*`,
  `nestedTupleFieldRhsUb_*`, `nestedTupleCopyUninitUb_*`).
- `tuple_encode_decode_place_edge_cases`: ground-truth checks of `TupleHeadLayout`
  (`capped_tail_align` with `packed_align = none` and `some ⟨2⟩`, `tail_offset`,
  `full_size_and_align`), `Type.layout`, `computeSize`, and `computeAlign` on
  zero-sized `()`, padded `(u8, u32)`, and unsized `Type::Tuple` with a
  `Type::Slice` tail, `Type.encode`, `Type.decode`, and `checkValue` on `()` and
  `(u8, u32)` (including `.Uninit` padding preservation, ignoring arbitrary
  padding bytes on decode, returning `none` when a field byte is `.Uninit`, and
  unsized/length-mismatch/non-Tuple panics and UB), plus `PlaceExpr::Field`
  out-of-bounds field indices (`-1`, `2`, `3`) and non-tuple root panics.
