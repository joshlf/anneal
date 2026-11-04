<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# MiniRust in Lean, and a correspondence with Anneal's MIR semantics

This directory holds three things:

1. a pinned, vendored snapshot of the upstream
   [MiniRust](https://github.com/minirust/minirust) specification and a
   **mechanical translation** of it to Lean 4 (`lean/MiniRustSpec/Generated*`),
   produced by `crates/anneal-minirust-gen`;
2. a **ground-truth interpretation** of a small part of MiniRust
   (`lean/MiniRustSpec/Interp.lean`), transcribed from the spec with
   quotations and pinned to the generated model
   (`lean/MiniRustSpec/Anchors.lean`);
3. a **correspondence theorem** between Anneal's trusted MIR semantics
   (`Trusted.Rustc.V2026_06_01`) and that interpretation, with non-vacuity
   witnesses (`lean/MiniRustSpec/Correspondence/`).

## Pins

| What | Pin |
| --- | --- |
| MiniRust commit | `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (2026-07-27, "add some reference corner case tests") |
| MiniRust tarball | `codeload.github.com/minirust/minirust/tar.gz/<commit>`, SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0` |
| MiniRust's own toolchain | `nightly-2026-05-01`, `libspecr` 0.1.41 (from the vendored `rust-toolchain.toml` and `tooling/Cargo.lock`) |
| Anneal MIR dialect | `Trusted.Rustc.V2026_06_01`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)` |
| Lean | `leanprover/lean4:v4.34.1` |

All pins live in `minirust.lock.toml` together with the SHA-256 of every
vendored file. MiniRust's tooling targets a slightly older nightly than
Anneal's MIR dialect. Nothing in the correspondence depends on that nightly:
the theorem is stated against Anneal's Lean model of `rustc`'s MIR, and the
MIR-to-MiniRust translation is a transcription of MiniRust's `minimize`, not a
run of it.

## Layout

| Path | Contents | Edited by hand? |
| --- | --- | --- |
| `minirust.lock.toml` | pins and per-file digests | no (`vendor`) |
| `vendor/<commit>/` | `spec/**` (translated), `tooling/minimize/src/**` (quoted by the correspondence, not translated), licenses, `README.md`, toolchain pins | no (`vendor`) |
| `coverage.json` | translation coverage, per file and in total | no (`generate`) |
| `lean/MiniRustSpec/Generated.lean`, `Generated/` | generated Lean | no (`generate`) |
| `lean/MiniRustSpec/Meta/Syntax.lean` | Lean schema mirroring `syn`'s syntax tree | yes |
| `lean/MiniRustSpec/Meta/LibSpecr.lean` | Lean types for the `libspecr` types the spec uses | yes |
| `lean/MiniRustSpec/Interp.lean` | interpretation of the fragment | yes |
| `lean/MiniRustSpec/Anchors.lean` | pins of every transcribed upstream item | yes |
| `lean/MiniRustSpec/Correspondence/*.lean` | translation, relation, proofs, witnesses | yes |
| `lean/MiniRustSpec/Audit.lean` | build-failing axiom audit | yes |

The Lean library is built from `examples/` (`lakefile.toml` declares
`MiniRustSpec` with `srcDir = "../minirust/lean"`).

## Commands and receipts

```sh
# Check the vendored tree against a downloaded tarball (byte for byte).
cargo run -q -p anneal-minirust-gen -- verify-tarball \
    --tarball /path/to/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed.tar.gz

# Regenerate from scratch and check that nothing changed.
cargo run -q -p anneal-minirust-gen -- generate
git diff --exit-code -- minirust && test -z "$(git status --porcelain minirust)"
cargo run -q -p anneal-minirust-gen -- generate --check

# Build the generated model, the interpretation, the proofs, the witnesses,
# and the axiom audit (which fails on any non-standard axiom).
(cd examples && lake build MiniRustSpec)

# Translator tests: determinism, freshness of the checked-in output,
# independent block/item/opaque-node recounts, tamper detection, and a check
# that every upstream quotation in the hand-written Lean occurs in vendor/.
cargo test -p anneal-minirust-gen

python3 trusted/audit/check_trusted.py
```

`vendor --tarball <path> --commit <sha>` re-creates `vendor/` and the lock file
from a tarball; it is only needed when re-pinning MiniRust.

## The translator

`crates/anneal-minirust-gen` refuses to run unless `vendor/<commit>/` contains
exactly the files listed in the lock file with exactly the listed digests. It
then extracts every fenced ```` ```rust ```` block of every `spec/**/*.md`,
parses it with `syn`, and emits:

* a **deep embedding**: every top-level item becomes one Lean definition of
  type `MiniRustSpec.Syntax.Item`, a term of a schema that mirrors `syn`'s
  syntax tree constructor for constructor. Each file's module ends with
  `items : List SourceItem` recording item name, source line, and the SHA-256
  of the item's token stream. The only lossy constructors are the explicit
  `verbatim`/`tokens`/`AttrMeta.listTokens` ones, and every use of them is
  counted as *opaque* in `coverage.json`;
* a **shallow embedding** of the spec's data types: every `struct`, `enum`,
  and `type` alias becomes a Lean `structure`, `inductive`, or `abbrev`; traits
  become classes of their associated types, and trait impls become instances.
  Function bodies are never translated shallowly. The mapping rules are listed
  in `src/shallow.rs`;
* `Generated/Manifest.lean` (pins and file digests as Lean data) and
  `coverage.json`.

Coverage at the pinned commit (`coverage.json`): 27 spec files, 141 Rust
blocks (all parsed), 250 items (135 `impl`, 39 `enum`, 37 `struct`, 12 `fn`,
11 `type`, 7 `macro`, 6 `use`, 3 `trait`) containing 300 functions and
methods; 47 957 syntax nodes translated structurally and 7 opaquely (99.985%
structural: 26 of 27 spec files have 0 opaque nodes, and the 7 opaque nodes are
exclusively the 7 `macro_rules! throw*` declarative macro bodies in
`spec/prelude/main.md`); 100 of 100 data types shallowly embedded (0 skipped).

The generated model is not executable: the deep embedding is syntax. The
executable meaning of the fragment is `Interp.lean`.

## The interpretation

`Interp.lean` transcribes, against the *generated* types, the specr-lang
functions needed to run the fragment below on `Machine<BasicMemory<x86_64>>`:
`Machine::step` (single enabled thread), `Statement::{Assign, PlaceMention}`,
`PlaceExpr::{Local, Index}` (`Index` on `Type::Array` only, with
`Machine::ptr_offset_inbounds`, `Memory::{dereferenceable,
signed_dereferenceable}`, and the `Machine::compute_size` sanity check),
`ValueExpr::{Constant, Tuple, Load, UnOp, BinOp}` with
`IntUnOp::{Neg, BitNot, CountOnes}` (all 3 `IntUnOp` variants), `CastOp::IntToInt`, and
`IntBinOp::{Add, AddUnchecked, Sub, SubUnchecked, Mul, MulUnchecked, Div, DivExact, Rem, Shl, Shr, ShlUnchecked, ShrUnchecked, BitAnd, BitOr, BitXor}` (all 16 `IntBinOp` variants),
`Terminator::{Goto, Switch, Return, Unreachable}` including
frame teardown and both stack-pop actions, the representation relation for
`Int`, `Bool`, and `Array`, `Type::layout`, `LayoutStrategy::compute_size_and_align`
for `Sized` layouts, `BasicMemory`'s `check_ptr`, `load`, `store`,
`deallocate`, and `dereferenceable`, and `ConcurrentMemory`'s access log and
data-race check.
Every definition quotes the upstream code it transcribes and cites its exact
vendored source file, and `crates/anneal-minirust-gen/tests/quotes.rs` parses
every Lean doc comment (`/-! ... -/` and `/-- ... -/`) and checks each quoted
substring against its cited vendored file (ignoring only whitespace and `//`
comments; `..` marks elided code). Effects are
`Except Stop` with `Stop.ub` (`throw_ub!`), `Stop.deadlock`, `Stop.specPanic`
(a panic in the spec, which upstream calls a spec bug), and
`Stop.unsupported` (outside the interpreted fragment; never silently wrong).

`Anchors.lean` lists the 45 upstream items that `Interp.lean` transcribes,
each with its file path, item name, line, and token hash, and proves by `decide`
that the generated model contains them unchanged (`anchors_ok`) with no
duplicate entries (`anchors_nodup`). Re-pinning MiniRust therefore breaks
the build until every affected transcription is re-reviewed.

## The correspondence

### Programs

`Correspondence/Translate.lean` defines `translateFn`, a transcription of
MiniRust's `minimize` (vendored under `vendor/<commit>/tooling/minimize/src/`,
quoted in the doc comments, quotations checked by `tests/quotes.rs`)
restricted to the fragment checked by `inFragment`:

* the body is `Runtime(PostCleanup)` MIR and declares only the return place
  and the arguments; the return place has integer type (`u8`..`u128`,
  `i8`..`i128`, `usize`, `isize`), and each argument has integer type or is a
  one-dimensional array `[T; N]` of an integer type `T` whose byte size
  `N * size_of::<T>()` is below `2^63`;
* scalar places are an integer local `_j` or one array element `_j[p]`, where
  `p` is `Index(_k)` (`_k` an integer local; a signed `_k` is accepted only
  when `N <= 2^(bits(_k) - 1)`, see the gaps) or
  `ConstantIndex { offset, min_length, from_end }` with `min_length <= N`,
  `offset < 2^63`, and, for `from_end`, `1 <= offset <= N`;
* statements are, for a scalar destination place, `Use(op)`,
  `UnaryOp(Neg | Not, op)`,
  `BinaryOp(Add | Sub | Mul | Div | Rem | BitXor | BitAnd | BitOr | Shl | Shr | AddUnchecked | SubUnchecked | MulUnchecked | ShlUnchecked | ShrUnchecked, opL, opR)`,
  `Cast(CastKind::IntToInt, op, targetTy)`, or (into a `usize` place)
  `Len(_j)` of an array local; for an array destination local `_i : [T; N]`,
  `Use(copy _j)` of an array local of the same type,
  `Aggregate(Array(T), [op; N])`, or `Repeat(op, N)` with `N > 0` (or `N = 0`
  when `op` is a constant); or `PlaceMention(_i)` of an unprojected local `_i`
  (scalar or array); here `op`, `opL`, `opR` are `copy` of a scalar place or
  integer constants (of the destination's type for `Use`, `UnaryOp`, `opL`,
  non-shift `opR`, and array elements, or of any integer type for shift `opR`
  and `Cast(IntToInt)`);
* terminators are `Goto`, `SwitchInt` on any integer fragment operand (`copy`
  of a scalar place, or a constant) with distinct in-range values, `Return`,
  and `Unreachable`; all targets are blocks of the body; no cleanup blocks.

`minimize` translates `Index(_k)` to `PlaceExpr::Index` with index
`Load(_k)`, `Aggregate(Array)` and `Repeat(op, N)` to `ValueExpr::Tuple` (the
latter with `N` copies of `op`), and `Len` of an array to the constant `N`.
Upstream `minimize` rejects `ConstantIndex` (`span_bug!`); `translateFn`
lowers it to `PlaceExpr::Index` with the constant `usize` index `offset` (or
`N - offset` when `from_end`), which is the index MIR defines for it.

### States

`Correspondence/Relation.lean` defines `StateRel body f ctx s m` (for execution
within MIR blocks) and `StartRel body f ctx s mInit` (for entry at `minimize`'s
synthesized `f.start` block without requiring a phantom `bb0` machine): the
MiniRust machine has one enabled thread whose stack is `[caller, callee]`; the
callee runs `f` at the corresponding program point; every MIR local `_i` is a
live MiniRust local pointing to its own `Stack` allocation whose bytes are the
encoding of Anneal's slot (`Uninit` bytes for an uninitialized slot,
little-endian bytes for an initialized scalar, and the concatenated element
encodings for an array, whose slots are always initialized); the caller's
return place is a
live, large-enough, aligned allocation (`CtxOk`); and Anneal's memory has no
borrows, protectors, call stack, or caller-owned referents. `ctx` fixes
everything the callee does not determine: caller frame, unwind payloads, the
allocations below the callee's locals, the locals' addresses (arbitrary,
subject only to alignment and, for arrays, to the whole array lying within
the 64-bit address space, so every MiniRust address choice is covered), and
the caller's continuation.

### Theorems

All proofs are complete; `Audit.lean` fails the build unless each of the
following depends only on `propext`, `Quot.sound`, and `Classical.choice`.

* `step_correspondence` (`Simulation.lean`): for a fragment body, its
  translation, and related states, one step of Anneal's coalgebra
  `stepMirFn body s` and one `Machine::step` satisfy `StepRel`: a silent
  Anneal step and an Anneal branch observation (the `switchInt` leakage tag)
  match a MiniRust step to a related state; an Anneal normal return of `v`
  matches a MiniRust step that pops the callee, writes the encoding of `v`
  to the caller's return place, deallocates every callee local, and continues
  the caller (`ReturnRel`); Anneal UB matches MiniRust UB (`throw_ub!`, never a
  spec panic, deadlock, or unsupported construct); every other Anneal outcome,
  including `unsupported`, is impossible.
* `step_initBlock`, `step_start`, `initMachineState_startRel`
  (`Simulation.lean`): proves for every translated function `f` that
  `initMachineState body args` (with `argsOk body args = true` and `CtxOk body ctx`)
  satisfies `StartRel` at `f.start`, and that `minimize`'s synthesized entry
  block (`f.start = bbName body.basicBlocks.length`) steps in 1 step (`Goto bb0`)
  to `StateRel`.
* `run_ret`, `run_ub`, `run_ret_from_start`, `run_ub_from_start`,
  `mirCall_ret`, `mirCall_ub` (`Run.lean`): lifted to Anneal's interaction
  trees `mirTree body s` and `mirCallTree body args`: if Anneal returns `v` (or
  can reach UB), then MiniRust started either at `bb0` or at `f.start` performs
  the corresponding return (or raises UB) within finitely many steps.
* `steps_error`, `steps_error_from_start`, `mirCall_steps_error` (`Run.lean`):
  conversely, if MiniRust stops with *any* error within `n` steps from
  `StateRel`, `StartRel`, or `mirCallTree body args`, either the error is UB and
  Anneal can reach UB, or MiniRust already completed the callee's return
  (`ReturnRel`, matching an Anneal `ReachesRet`) in `k < n` steps and only
  errored later inside the unmodeled caller frame.
* `mirNoUB_safe`, `mirNoUB_safe_from_start`, `mirCall_noUB`, `runA_noUB`
  (`Run.lean`): if Anneal's interaction tree satisfies `MirNoUBTree`
  (`TreeSafe`), MiniRust never stops with any error (`.ub`, `.specPanic`,
  `.deadlock`, or `.unsupported`) anywhere during the callee's execution.
* `steps_outcome`, `steps_outcome_from_start`, `mirCall_outcome`,
  `mirNoUB_progress`, `mirNoUB_progress_from_start`, `mirCall_progress`,
  `mirNoUB_diverges_steps_ok`, `mirNoUB_diverges_from_start`,
  `mirNoUB_diverges_rel_from_start`, `mirCall_diverges_steps_ok`,
  `mirCall_diverges_rel`, `treeSafe_of_step_inv`, `noRet_of_step_inv`,
  `treeSafe_of_tau_inv`, `noRet_of_tau_inv` (`Run.lean`): total `n`-step
  outcome trichotomy and forward progress for all `n : Nat` (either still
  running in lockstep `StateRel`, already returned via `ReturnRel` in `k ≤ n`
  steps, or stopped with `.ub` matching `FaultNow`), specializing under
  `MirNoUBTree` and non-termination to prove that diverging UB-free loops
  (both silent-step and branch-observing) step forever in lockstep
  `StateRel` + `Reaches`.

### Witnesses

`Correspondence/Witness.lean` discharges every hypothesis for concrete
programs, computing both semantics in the kernel (`decide`/`rfl`, no
`native_decide`):

* `sumTo`, the MIR of a `u32` loop with `switchInt`, wrapping `Add`/`Sub`,
  constants, and `Goto`: Anneal returns `6` for `n = 3`
  (`sumTo_anneal_ret`, `sumTo_noUB`); the initial states are related
  (`sumTo_rel`); the theorem then yields a MiniRust return writing the bytes of
  `6u32` both from `bb0` (`sumTo_minirust_ret`) and from `f.start` via
  `mirCall_ret` (`sumTo_minirust_ret_from_start`), which agrees with direct
  16-step and 17-step runs (`sumTo_minirust_direct`,
  `sumTo_minirust_direct_from_start`).
* `retUninit`, a body returning an uninitialized `_0`: Anneal faults
  (`retUninit_anneal_ub`), hence MiniRust raises UB both from `bb0`
  (`retUninit_minirust_ub`) and from `f.start` via `mirCall_ub`
  (`retUninit_minirust_ub_from_start`), as a direct run confirms
  (`retUninit_minirust_direct`).
* `negMention`, a body exercising `PlaceMention(_0)` (while `_0` is still
  uninitialized), wrapping integer negation `_0 = Neg(copy _1)`, and an
  `Unreachable` terminator on the `_1 == 0` branch: for `_1 = 5`, returns
  `4294967291` (`negMention5_minirust_ret_from_start`, confirmed by
  `negMention5_minirust_direct`); for `_1 = 0`, computes `-0 = 0` and takes
  the `Unreachable` branch to raise UB (`negMention0_minirust_ub_from_start`,
  confirmed by `negMention0_minirust_direct`).
* `signedEdge`, a signed `i8` body exercising two's-complement sign-bit
  decoding (`intFromBits`), `i8::MIN` (`-128i8`, bits `128`) wrapping negation
  (`-(-128i8) = -128i8`), negative `switchInt` branch keys (`-128`, `-1`),
  signed underflow wrapping (`-128i8 + (-1i8) = 127i8`), signed
  negative-by-negative `Mul` (`(-1i8) * (-2i8) = 2i8`), and end-to-end
  `MirNoUBTree` safety transfer (`signedEdgeMin_minirust_noUB`), confirmed by
  direct 5-step runs (`signedEdgeMin_minirust_direct`,
  `signedEdgeOne_minirust_direct`).
* `castBitNot`, a mixed-type (`i8` and `u32`) body exercising `UnaryOp(Not)`
  (`IntUnOp::BitNot`) on both signed `i8` (`!4i8 = -5i8`) and unsigned `u32`
  (`!4294967291u32 = 4u32`), signed-to-unsigned widening `Cast(IntToInt)` with
  two's-complement sign extension (`-5i8 as u32 = 4294967291u32`), and
  unsigned-to-signed narrowing `Cast(IntToInt)` truncation
  (`4294967291u32 as i8 = -5i8`), confirmed via `mirCall_ret`
  (`castBitNot4_minirust_ret_from_start`) and a direct 7-step run
  (`castBitNot4_minirust_direct`).
* `spinLoop`, a diverging `loop {}` body exercising `treeSafe_of_tau_inv`
  (`spinLoop_noUB`), `noRet_of_tau_inv` (`spinLoop_diverges`),
  `mirCall_diverges_steps_ok` (`spinLoop_minirust_steps_ok`), and lockstep
  `mirCall_diverges_rel` (`spinLoop_minirust_diverges_rel`, preserving
  `StateRel` and `Reaches` for all `n : Nat`).
* `divRemI8` and `remOnlyI8`, signed `i8` bodies exercising truncating-toward-zero
  `Div` and `Rem` (`-7i8 / 3i8 = -2i8` and `-7i8 % 3i8 = -1i8`, plus the non-UB
  signed boundary `-128i8 / 1i8 = -128i8`), all four division and remainder UB
  paths (`-7i8 / 0i8`, `-128i8 / -1i8`, `-7i8 % 0i8`, `-128i8 % -1i8` via
  `mirCall_ub` and direct checks of MiniRust's `throw_ub!` messages), and
  converse error soundness (`divByZero_converse_error` via `mirCall_steps_error`).
* `uncheckedArithI8`, a signed `i8` body exercising `MulUnchecked`,
  `SubUnchecked`, and `AddUnchecked` both succeeding at the `i8::MIN` boundary
  (`64i8 * -2i8 = -128i8`, `-128i8 - (-2i8) = -126i8`, `-126i8 + 127i8 = 1i8`
  via `mirCall_ret` and `MirNoUBTree`) and faulting on each operator's signed
  overflow UB (`mirCall_ub`, `mirCall_outcome`, and direct `Interp.steps` checks).
* `branchSpinLoop`, a conditional `while x != 0 {}` loop that emits a visible
  `.emit` branch event on every `switchInt` iteration, proved UB-free via
  `treeSafe_of_step_inv` (`branchSpinLoop1_noUB`), non-terminating via
  `noRet_of_step_inv` (`branchSpinLoop1_diverges`), and lockstep-diverging in
  `StateRel` + `Reaches` via `mirCall_diverges_rel`
  (`branchSpinLoop1_minirust_diverges_rel`).
* `shiftI8` and `shlUncheckedI8`, signed `i8` bodies exercising two's-complement
  arithmetic right shift `Shr` on a negative operand with a negative shift count
  wrapped via `.rem_euclid(8)` (`-64i8 >> -6i8 = -64i8 >> 2 = -16i8`), wrapping
  left shift `Shl` (`-16i8 << -7i8 = -16i8 << 1 = -32i8`), `ShrUnchecked` and
  `ShlUnchecked` on valid shift counts (`shiftOk_minirust_ret_from_start`,
  `shiftOk_noUB`, `shiftOk_minirust_direct`), and all four unchecked-shift UB
  paths (`s >= bits` and `s < 0` for both `ShrUnchecked` and `ShlUnchecked`).
* `bitwiseI8` (plus `countOnes_neg86_i8` and `countOnes_neg1_i8`), a signed `i8`
  body exercising two's-complement `BitAnd`, `BitOr`, and `BitXor` on negative
  operands (`(-86i8) & (-15i8) = -96i8`, `(-96i8) | (-123i8) = -91i8`, and
  `(-91i8) ^ (-59i8) = 96i8`, cancelling infinite leading two's-complement `1`
  bits under `BitXor`), alongside direct ground-truth checks of
  `IntUnOp::CountOnes` returning `u32` on negative `i8` inputs.
* `heteroShiftSwitch`, a mixed-type `(i8, u32, i32)` body exercising
  heterogeneous wrapping `Shr` and `Shl` (`-64i8 >> 258u32 = -16i8` and
  `-16i8 << 257u32 = -32i8` with shift counts `>= 256`), constant-operand
  signed `SwitchInt` (`switchInt(const -1i8)`), and heterogeneous `(i8, i32)`
  `ShrUnchecked` / `ShlUnchecked` (`-32i8 >> 3i32 = -4i8`, `-4i8 << 3i32 = -32i8`),
  plus UB checks at `k = 8i32` (`8 >= i8::BITS` even though `8 < i32::BITS`)
  and `k = -1i32` (`-1 < 0`).
* `uninitOperandUb` (plus `divExact_ok_i8`, `divExact_rem_ub_i8`,
  `divExact_zero_ub_i8`, and `divExact_min_neg1_ub_i8`), a signed `i8` body
  exercising uninitialized-operand UB (`copy _0` before `_0` is initialized) in
  `BinaryOp`, `UnaryOp`, and `SwitchInt` scrutinee positions (`mirCall_ub`,
  `mirCall_steps_error`, and direct checks of MiniRust's `"load at type but the
  data in memory violates the language invariant"` UB), alongside ground-truth
  checks of all four `IntBinOp::DivExact` outcomes.
* `arrayOpsI8`, `arraySignedIdxI8`, `zeroArrayI8`, `arrayUninitIdxI8`,
  `arrayU32Idx`, `arrayConstIdxOobI8`, and `arrayComposeI8`, bodies with
  `[i8; 3]`, `[i8; 2]`, `[i8; 0]`, and `[u32; 3]` arguments exercising
  `Aggregate(Array)`, `Repeat` (including `[const 5i8; 0]`), whole-array copies,
  `PlaceMention` on an array local, `Len`, and `Index` / `ConstantIndex` (from
  the start and from the end) reads and in-place element writes
  (`*_minirust_ret_from_start`, `*_noUB`, direct runs, and byte-level checks
  that each in-place write rewrites exactly the element's bytes at offset
  `index * size_of::<T>()` and leaves its siblings intact:
  `arrayOpsOk_minirust_inplace_bytes`, `arrayOpsOk_minirust_ret_dealloc`,
  `arrayU32IdxOk_minirust_inplace_bytes`),
  projected array operands (`copy _1[proj]`) composed with `SwitchInt`,
  `Repeat`, `Aggregate(Array)`, `UnaryOp(Neg)`, and `Cast(IntToInt)`
  (`arrayComposeOk_*`), plus UB for an out-of-bounds `Index` or `ConstantIndex`
  (`idx >= N`, including every index of `[i8; 0]` and projected `SwitchInt`
  discriminants), a negative signed index, an uninitialized index local,
  faulting array-producing rvalues (`Aggregate(Array)` and `Repeat` with
  uninitialized or out-of-bounds element operands: `arrayComposeAggUb_*`,
  `arrayComposeRepeatUb_*`), and in-place indexed writes with a faulting RHS
  (`arrayComposeRhsUb_*`, `arrayComposeBothUb_*`), each via `mirCall_ub` and a
  direct check of MiniRust's `throw_ub!` message, alongside ground-truth checks
  of `Size.mulInt`, `Type.encode`, `Type.decode`, and `tryMapM`
  (`sizeMulInt_zero_neg`, `array_encode_decode_edge_cases`).

### Gaps

These are deliberate and are the first things to lift:

* **`Operand::Move` is excluded.** `minimize` translates `Move` exactly like
  `Copy`, whereas Anneal de-initializes the moved-from place, so the models
  disagree on later reads of a moved-from local.
* **Only the return place and arguments.** Bodies with other locals need
  `StorageLive`/`StorageDead` (and `minimize`'s init block would allocate
  some of them), which the fragment and the interpretation do not cover.
* **One thread, called from a caller frame.** MiniRust makes it UB for the
  bottom frame of the main thread to return, while Anneal's root body returns
  normally, so the relation places the callee above an arbitrary caller. What
  the caller does after the return is outside the relation. Call setup
  (`Terminator::Call`, argument passing) is not interpreted; witnesses start
  at the callee's entry.
* **Branch observations.** Anneal's `switchInt` emits the scrutinee as a
  visible leakage event; MiniRust has no counterpart, so `StepRel` matches it
  with an ordinary MiniRust step.
* **Integers and integer arrays only.** No `bool` discriminants (`minimize`
  inserts a transmute), no pointers, references, tuples, structs, enums,
  slices, nested arrays, non-integer casts, comparisons, checked arithmetic,
  calls, drops, or assertions. Arrays appear only as arguments (no other
  locals exist) and never as the return place, and a place has at most one
  projection.
* **`Repeat(copy p, 0)` is excluded (while `Repeat(const c, 0)` is included).**
  Anneal evaluates `op` once before replicating it, while `minimize`'s
  `list![op; 0]` never evaluates `op`, so the models disagree when `op` is a
  `copy` that can fault (an uninitialized local or out-of-bounds array index),
  whereas a constant operand never faults in either semantics.
* **Projected `PlaceMention(_j[p])` is excluded (while `PlaceMention(_j)` is included).**
  Anneal's `.placeMention` checks only `place.local_` and ignores
  `place.projection`, whereas MiniRust's `eval_statement(PlaceMention(place))`
  calls `eval_place(place)`, which evaluates index operands and bounds checks on
  `PlaceExpr::Index`.
* **`Len` does not evaluate its place in MiniRust.** `minimize` emits the
  constant `N` (its own `FIXME` notes the place might have UB), while Anneal
  reads the place; this is harmless only because array slots in the fragment
  are always initialized.
* **Evaluation order of `Statement::Assign` (`destination` vs `source`).**
  MiniRust's `eval_statement(Assign { destination, source })` evaluates
  `eval_place(destination)` before `eval_value(source)`, whereas Anneal's
  `evalStmt(.assign dst rv)` evaluates `evalRvalue` before `writeProjectedValue`.
  Because neither expression evaluation mutates memory in the fragment, both
  models raise UB under the exact same conditions (`projIdx = none ∨ rvBits = none`)
  and produce identical stores otherwise (`StepRel.ub'` / `StepRel.tau'`),
  differing only in which UB reason fires first when *both* the destination
  projection and the RHS rvalue fault (`arrayComposeBothUb_*`).
* **Index locals of non-`usize` type.** MIR requires `usize` index locals,
  but the fragment also accepts other integer types. Anneal indexes with the
  raw bit pattern and MiniRust with the decoded value, which agree for
  unsigned types and, for a signed type, as long as `N <= 2^(bits - 1)` (a
  negative index then has a bit pattern `>= N`), which the fragment
  requires.
* **The interpretation is transcribed, not generated.** It is anchored to the
  generated model by token hashes and quotes the spec, but nothing proves it
  equal to the deep embedding, which has no executable semantics.
