<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction Guide — `MR-3.1`: Raw Pointers (`PtrType::Raw`, `AddrOf`, `PlaceExpr::Deref`, `BinOp::PtrOffset`, Int/Ptr Casts)

This guide reproduces the `MR-3.1` changes: the MiniRust interpretation of raw
pointers, `minimize`'s translation of raw pointer MIR, kernel-checked runs
of raw pointer programs in both Anneal's MIR semantics and the MiniRust
interpretation, and the extension of the correspondence theorems
(`step_correspondence_N`, `step_correspondence`, `step_start_N`) to the raw
pointer statements that `inFragment` admits; see "Scope" below.

## 1. Environment

From the repository root:

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
```

## 2. Hygiene and trusted base

```bash
./ci/check_todo.sh
python3 trusted/audit/check_trusted.py --fast
```

## 3. Generator, anchors, and quotations

```bash
cargo test -p anneal-minirust-gen --offline
```

Besides regeneration and tamper checks, this runs:

- `tests/pipeline.rs` (`anchors_match_generated_items_and_cover_interp`): each
  of the 72 anchors in `minirust/lean/MiniRustSpec/Anchors.lean` (13 of them new
  for raw pointers: `decode_ptr`, `encode_ptr`, `PointerMetaKind`,
  `PtrType::as_wide_pair`, `PointerMetaKind::{decode_value, encode_as_value}`,
  `Type::decode` for `Type::Ptr`, `ValueExpr::AddrOf`, `PlaceExpr::Deref`,
  `UnOp::GetThinPointer`, `PtrType::safe_pointee`, `IntPtrCast`,
  `Machine::eval_intrinsic` for the provenance intrinsics, and
  `Terminator::Intrinsic`) names an item of the generated model with its line
  and token hash, and every definition after the `Target` section of
  `Interp.lean` is anchored.
- `tests/quotes.rs`: every `>` quotation in the hand-written Lean occurs in
  its cited vendored file, and
  `mr_3_1_pointer_quotations_are_pinned_and_tamper_checked` pins the 34 raw
  pointer quotations of `Interp.lean`, checks that each stops matching once
  altered, and checks that four plausible misreadings of the pointer
  semantics (for example an in-bounds `PtrOffset` that wraps instead) do not
  occur upstream.

## 4. Lean build and axiom audit

```bash
cd examples && anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec
```

The build includes `MiniRustSpec.Correspondence.Pointers` (lemmas about both
semantics' raw pointers), `MiniRustSpec.Correspondence.PointerStep` (the raw
pointer statements in both semantics, on which `step_correspondence_N` rests),
and `MiniRustSpec.Correspondence.PointerWitness` (the witnesses), and fails
unless `MiniRustSpec.Audit` accepts every declaration. Expected audit lines:

```text
[ANCHOR-AUDIT] decls=2 axioms=[] sorry_free=true
[SIMULATION-AUDIT] decls=221 axioms=[propext, Classical.choice, Quot.sound] sorry_free=true
[WITNESS-AUDIT] decls=485 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
[POINTER-AUDIT] decls=200 axioms=[propext, Quot.sound, Classical.choice] sorry_free=true
MiniRustSpec.Audit: exhaustively verified standard axioms for 13771 declarations across all MiniRustSpec.* modules
Build completed successfully (70 jobs).
```

`[POINTER-AUDIT]` covers 37 theorems of `Correspondence/Pointers.lean`, 19 of
`Correspondence/PointerStep.lean`, and the 144 theorems of
`Correspondence/PointerWitness.lean`. `[SIMULATION-AUDIT]` includes
`step_correspondence_N`, `step_start_N`, `steps_outcome_N`,
`mirNoUB_progress_N`, `mirNoUB_diverges_steps_ok_N`, and the `_N` whole-call
correspondence theorems (`mirCall_progress_N`, `mirCall_outcome_N`,
`mirCall_diverges_rel_N`), which preserve `StateRelN` across arbitrary step
counts and depend on the raw pointer lemmas.

## 5. What the witnesses show

Every witness runs both semantics in the kernel (`rfl`, `decide`,
`decide +kernel`; no `native_decide`): Anneal through `runA_sound` or
`faultsA_sound`, MiniRust by stepping the machine that runs `translateFn`'s
output from its start.

| Witness | Anneal | MiniRust |
| --- | --- | --- |
| `ptrRoundTrip` (`&raw mut x`, `*p` read and write, `PtrToPtr`, read through the cast; in the fragment) | returns `6` | returns `6`, also derived by `mirCall_ret` (`mirCall_noUB`, `mirCall_progress_N`) |
| `arrayParamPtr` (disjoint `&raw mut a[-2 of 2]` and `&raw mut a[-1 of 2]` on `a: [u32; 2]`, `Offset(p, 0)`, `move`, `StorageDead`/`Deinit`, deref reads/writes; in the fragment) | returns `19` | returns `19`, also derived by `mirCall_ret` (`mirCall_noUB`, `mirCall_progress_N`) |
| `arrayElemPtr` (`&raw mut a[1]` on a temporary array; outside the fragment) | returns `12` | returns `12` |
| `fieldPtr` (`&raw mut s.1` on `Padded(u8, u32, u16)`; in the fragment) | returns `100` | returns `100`, also derived by `mirCall_ret` (`mirCall_noUB`, `mirCall_progress_N`) |
| `nestedFieldPtr` (disjoint `&raw mut t.0.1` (`u32`, byte offset `4`) and `&raw mut t.1` (`u16`, byte offset `8`) on `t: ((u8, u32), u16, ())`, preserving `.Uninit` padding; in the fragment) | returns `59` | returns `59`, also derived by `mirCall_ret` (`mirCall_noUB`, `mirCall_progress_N`, `nestedFieldPtr_minirust_padding_bytes`) |
| `ptrCountdown` (four-block loop counting `x` down through `&raw mut x`, `*p` read before each `switchInt`, `x` read directly at the end; in the fragment) | returns `3` | returns `3`, also derived by `mirCall_ret` (`mirCall_noUB`, `mirCall_progress_N`) |
| `constBorrowLoop` (fresh `&raw const x` in each loop iteration, read through, then `StorageDead`; in the fragment) | returns `15` | returns `15`, also derived by `mirCall_ret` (`mirCall_noUB`, `mirCall_progress_N`) |
| `repointPtr` (`&raw mut a[0 of 2]` and `&raw mut a[1 of 2]`, an initialized pointer local overwritten with the second pointer and written through; in the fragment) | returns `105` | returns `105`, also derived by `mirCall_ret` (`mirCall_noUB`, `mirCall_progress_N`) |
| `uninitPtrReadUb` (`copy (*_p)` on an uninitialized pointer temporary; in the fragment) | UB | UB: language invariant, also derived by `mirCall_ub` (`mirCall_steps_error`, `mirCall_outcome_N`) |
| `uninitPtrWriteUb` (`(*_p) = copy _1` on an uninitialized pointer temporary; in the fragment) | UB | UB: language invariant, also derived by `mirCall_ub` (`mirCall_steps_error`, `mirCall_outcome_N`) |
| `deadPtrReadUb` (`copy (*_p)` after `StorageDead(_p)` on a pointer temporary; in the fragment) | UB | UB: dead local, also derived by `mirCall_ub` (`mirCall_steps_error`, `mirCall_outcome_N`) |
| `uninitPtrOffsetUb` (`Offset(copy _p, 0)` on an uninitialized pointer temporary; in the fragment) | UB | UB: language invariant, also derived by `mirCall_ub` (`mirCall_steps_error`, `mirCall_outcome_N`) |
| `derefWriteRhsUb` (`(*_p) = copy _uninit` through a valid `*mut` pointer; in the fragment) | UB | UB: language invariant, also derived by `mirCall_ub` (`mirCall_steps_error`, `mirCall_outcome_N`) |
| `derefIdxWriteRhsUb` (`(*_p) = copy _uninit` through a valid `*mut` pointer to `a[1 of 2]`; in the fragment) | UB | UB: language invariant, also derived by `mirCall_ub` (`mirCall_steps_error`, `mirCall_outcome_N`) |
| `dangling` (read after `StorageDead`) | UB | UB: dead allocation |
| `offsetDeref 1` (`*a[0..].offset(1)`) | returns `a[0] = 5` | returns `a[1] = 7` |
| `offsetDeref 2` (read one past the end) | returns `5` | UB: out of bounds |
| `offsetDeref 3` | returns `5` | UB at the offset |
| `offsetDeref usizeMax` | returns `5` | UB: `MulUnchecked` overflow |
| `misaligned` (`u32` read one byte into `x`) | returns `5` | UB: misaligned |
| `exposeTwice` (difference of two exposed addresses of `x`) | returns `65536` | returns `0` |
| `directWrite` (read through `p` after `x = 9`) | UB | returns `9` |
| `frozenWrite` (write through `&raw const x as *mut u32`) | UB | returns `9` |

`translateFn` does not yet translate `PointerExposeProvenance`
(`exposeTwice_translate`), so `exposeTwice_minirust_direct` runs
`exposeTwiceFn`, which spells out `minimize`'s translation (an intrinsic call
terminator followed by a fresh block).

## 6. Scope

`inFragment` admits raw pointers under the borrow discipline that
`minirust/README.md` ("Gaps") describes, and `step_correspondence_N` simulates
`&raw`, pointer copies, `Offset(p, 0)`, and reads and writes through pointers
(`Correspondence/PointerStep.lean`); `ptrRoundTrip`, `arrayParamPtr`,
`fieldPtr`, `nestedFieldPtr`, `ptrCountdown`, `constBorrowLoop`, `repointPtr`,
`uninitPtrReadUb`, `uninitPtrWriteUb`, `deadPtrReadUb`, `uninitPtrOffsetUb`,
`derefWriteRhsUb`, and `derefIdxWriteRhsUb` are in the fragment, `ptrCountdown`
and `constBorrowLoop` with borrows that outlive the entry block or are taken in
a loop. The
rows where Anneal returns a value and MiniRust a different value or UB, or the
reverse, are executions on which the models disagree; a correspondence that
covered them would be false, and each of them, as well as `arrayElemPtr` and
`dangling`, lies outside the fragment (`*_notInFragment`).
