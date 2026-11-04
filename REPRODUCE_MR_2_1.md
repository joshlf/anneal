<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction Guide — `MR-2.1`: Homogeneous Arrays (`Type::Array`), `Repeat`, `Len`, and `Index`/`ConstantIndex` Projections

This guide provides self-contained, step-by-step commands to independently
reproduce and audit the `MR-2.1` implementation, verbatim upstream MiniRust
specification/translator quote checks, and kernel-checked Lean 4 correspondence
proofs and witnesses.

## 1. Environment Setup

From the repository root (`/usr/local/google/Projects/anneal-workspace/anneal-wt-mr-2-1`):

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
  `Type::Array`, `ValueExpr::Tuple`, `PlaceExpr::Index` with its
  `compute_size` sanity check, `LayoutStrategy::compute_size_and_align`,
  `Machine::compute_size`, `ptr_offset_inbounds`,
  `dereferenceable`, `signed_dereferenceable`, `rs::TyKind::Array`,
  `smir::ProjectionElem::Index`, `smir::Rvalue::Aggregate(Array)`,
  `smir::Rvalue::Repeat`, `smir::Rvalue::Len`, and the `span_bug!` with which
  `minimize` rejects `smir::ProjectionElem::ConstantIndex`) against the vendored
  MiniRust specification and `tooling/minimize/src/*.rs`:

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
  `mirCall_*` theorems, and the array lemmas (`evalPlace_proj`,
  `evalStatement_assign_index`, `evalStmt_assign_index`,
  `writeProjectedValue_proj`, `typedStore_array_elem`, ...).
- `WITNESS-AUDIT`: every `MR-2.1` witness theorem in
  `MiniRustSpec/Correspondence/Witness.lean` (`arrayOps*`, `arraySigned*`,
  `arrayUninitIdx*`, `arrayU32Idx*`, `zeroArray*`).

```bash
cd examples && anneal-lean-run --mode file --concurrency 3 -- lake env lean ../minirust/lean/MiniRustSpec/Audit.lean | grep -E '\[(ANCHOR|SIMULATION|WITNESS)-AUDIT\]|exhaustively verified'
```

Expected audit summary lines:

```text
MiniRustSpec.Audit: exhaustively verified standard axioms for 8179 declarations across all MiniRustSpec.* modules
[ANCHOR-AUDIT] decls=2 theorems=2 sorry_free=true standard_axioms_only=true
[SIMULATION-AUDIT] decls=21 theorems=21 sorry_free=true standard_axioms_only=true
[WITNESS-AUDIT] decls=46 theorems=46 sorry_free=true standard_axioms_only=true
```

## 6. What the Witnesses Show

Each witness runs both semantics in the kernel (`decide`/`rfl`, no
`native_decide`) and transfers Anneal's outcome to MiniRust through
`mirCall_ret` / `mirCall_ub`:

- `arrayOpsI8` (`[i8; 3]`): `Aggregate(Array)`, `Repeat`, whole-array copy,
  `Index` and `ConstantIndex` (from the start and from the end) reads and
  in-place writes, and `Len`; `arrayOpsOk_minirust_inplace_bytes` shows the
  bytes of `_2`'s MiniRust allocation going from `[3, 10, 20]` to
  `[3, 17, 20]` to `[3, 17, 17]`, one element per write. Index `3` raises
  out-of-bounds UB (`arrayOpsOob_*`).
- `arrayU32Idx` (`[u32; 3]`): a write at index `2` lands at byte offset `8`
  (`index * size_of::<u32>()`) and leaves bytes `0..8` unchanged
  (`arrayU32IdxOk_minirust_inplace_bytes`); index `3` raises out-of-bounds UB.
- `arraySignedIdxI8`: a signed `i8` index local (`1i8` succeeds, `-1i8` and
  `2i8` raise UB).
- `arrayUninitIdxI8`: an uninitialized index local raises UB; MiniRust's
  message is the failed `Load` of the index operand
  (`arrayUninitIdx_minirust_direct`), not the bounds check.
- `zeroArrayI8`: `[i8; 0]` construction, copy, and `Len = 0`; indexing at `0`
  raises out-of-bounds UB.
