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
(cd examples && anneal-lean-run --mode build --concurrency 3 -- lake build MiniRustSpec)

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
`Machine::step` (single enabled thread),
`Statement::{Assign, PlaceMention, StorageLive, StorageDead, Deinit}` (with
`StackFrame::{storage_live, storage_dead}` and `ConcurrentMemory::deinit`),
`PlaceExpr::{Local, Field, Index}` (`Field` indexing `(offset, field_ty)` on
`Type::Tuple` and `Type::Union`, and `Index` on `Type::Array` and `Type::Slice`,
with `Machine::ptr_offset_inbounds`, `Memory::{dereferenceable,
signed_dereferenceable}`, and the `Machine::compute_size` sanity check),
`ValueExpr::{Constant, Load, Tuple, UnOp, BinOp}` (`ValueExpr::Tuple` evaluating
each element or field expression in order and returning `(Value::Tuple(vals),
ty)` for both `Type::Tuple` and `Type::Array`, while `check_value` and
`Type::encode` validate length and element/field values at `typed_store` /
`typed_load`) with
`IntUnOp::{Neg, BitNot, CountOnes}` (all 3 `IntUnOp` variants),
`CastOp::{IntToInt, Transmute}` (both `CastOp` variants; `Transmute` runs
`Machine::transmute`, which encodes the value at the old type and decodes
and checks it at the new one),
`IntBinOp::{Add, AddUnchecked, Sub, SubUnchecked, Mul, MulUnchecked, Div, DivExact, Rem, Shl, Shr, ShlUnchecked, ShrUnchecked, BitAnd, BitOr, BitXor}` (all 16 `IntBinOp` variants),
`BinOp::IntWithOverflow` with `IntBinOpWithOverflow::{Add, Sub, Mul}` (all 3
`IntBinOpWithOverflow` variants, through `Machine::eval_int_bin_op_with_overflow`
and `IntType::with_overflow`, returning `(Value::Int(res_wrapped), Value::Bool(res != res_wrapped))` at `ty.with_overflow()`),
`BinOp::Rel` with `RelOp::{Lt, Gt, Le, Ge, Eq, Ne, Cmp}` (all 7 `RelOp`
variants, through `Machine::eval_rel_op`) on integers, Booleans, and thin
pointers (`comparePtr`, which compares addresses),
`Terminator::{Goto, Switch, Return, Unreachable}` including
frame teardown and both stack-pop actions, the representation relation
(`Type::{decode, encode}`) for `Int`, `Bool`, `Array`, sized `Tuple`, `Union`,
`Enum` (through `decode_discriminant` and `encode_discriminant`), `Slice`, and
`TraitObject`, `check_value` for those types, `Type::layout` (also for unsized
tuples, slices, and trait objects) and `LayoutStrategy::compute_size_and_align`
/ `TupleHeadLayout::full_size_and_align`, `BasicMemory`'s `check_ptr`,
`dereferenceable`, `signed_dereferenceable`, `load`, `store`, `allocate`, and
`deallocate`, and `ConcurrentMemory`'s access log and data-race check.
For raw pointers (MR-3.1) it adds `Type::Ptr` with `PtrType::Raw` (layout,
`decode_ptr` / `encode_ptr` with per-byte provenance fragments, wide pointers
with `PointerMetaKind::ElementCount` metadata, and `check_value`; safe
pointers and vtable metadata are `unsupported` because their checks need the
machine), `ValueExpr::AddrOf` (with `BasicMemory`'s identity `retag_ptr`),
`PlaceExpr::Deref` (whose `aligned` flag makes a load or store through a
misaligned pointer UB), `UnOp::GetThinPointer`, `BinOp::PtrOffset` with both
`inbounds: true` (`Machine::ptr_offset_inbounds`) and `inbounds: false`
(`ptr_offset_wrapping`), `BinOp::PtrOffsetFrom`,
`Constant::PointerWithoutProvenance`, and `Terminator::Intrinsic` for
`IntrinsicOp::{PointerExposeProvenance, PointerWithExposedProvenance}` with
`IntPtrCast::{expose, int2ptr}` (`spec/mem/intptrcast.md`). `int2ptr` predicts
a provenance with the angelic choice `predict`; the interpretation picks the
exposed live allocation whose address range (one-past-the-end included)
contains the address, returns no provenance when there is none, and reports
`Stop.unsupported` when several allocations qualify (`int2ptrProvenance`), so
its successful runs are runs of the spec.
`BasicMemory::allocate` picks the address with the daemonic choice `pick`,
which never has a unique solution; the interpretation commits to one valid
resolution (`BM.pickAddr`): the first multiple of `2^32` in `[2^32, 2^64)`
that satisfies every test of the upstream predicate (`BM.allocAddrOk`), and
reports `Stop.unsupported` when there is none. The recursion over
nested types, array elements, tuple fields, union chunks, enum variants, and
discriminator trees is structural (Lean `mutual` blocks), so the kernel
evaluates it.
MiniRust has no Boolean `!`: `UnOp::Int` on a `Value::Bool` is a spec panic,
as upstream, and `minimize` expresses `!b` with transmutes instead (see below).
Every definition quotes the upstream code it transcribes and cites its exact
vendored source file, and `crates/anneal-minirust-gen/tests/quotes.rs` parses
every Lean doc comment (`/-! ... -/` and `/-- ... -/`) and checks each quoted
substring against its cited vendored file (ignoring only whitespace and `//`
comments; `..` marks elided code). Effects are
`Except Stop` with `Stop.ub` (`throw_ub!`), `Stop.deadlock`, `Stop.specPanic`
(a panic in the spec, which upstream calls a spec bug), and
`Stop.unsupported` (outside the interpreted fragment; never silently wrong).

`Anchors.lean` lists the 72 upstream items that `Interp.lean` transcribes,
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

* the body is `Runtime(PostCleanup)` MIR and declares the return place, the
  arguments, and any number of temporaries (`argCount + 1 <= localDecls.length
  < 2^31`); the return place `_0` has integer type (`u8`..`u128`, `i8`..`i128`,
  `usize`, `isize`), `bool`, `core::cmp::Ordering`, or a 2-tuple `(Int, bool)`,
  each temporary (`argCount < i`) has one of those scalar-family types or a thin
  raw pointer type `*const T` / `*mut T` to an integer pointee `T`
  (`ptrPointeeOf`), and each argument local additionally may be a homogeneous
  one-dimensional integer array `[T; N]` whose byte size `N * size_of::<T>()` is
  below `2^63` or a well-formed nested tuple or single-variant struct
  (`TupleSpec`: `RigidTy::Tuple` or `RigidTy::Adt` with `FieldsShape::Arbitrary`,
  `VariantsShape::Single(0)`, integer leaf fields or `()`, and explicit
  inter-field and trailing padding);
* `StorageLive(_i)` and `StorageDead(_i)` of scalar-family or thin raw pointer
  locals (`StorageDead` only of temporaries, as MiniRust's well-formedness check
  requires), and `Deinit(_i)` of a scalar-family or thin raw pointer root local,
  which `minimize` does not translate and we translate to
  `Statement::Deinit(PlaceExpr::Local(_i))`;
* scalar-family operands may be `copy` or `move` of `_j`, `_j.0`, or `_j.1` (and
  integer operands may also `copy` an array element `_j[p]` or a nested
  tuple/struct scalar field chain `_j.f1...fk`). `minimize` translates `move`
  like `copy`; Anneal's `move` of a root local leaves it uninitialized while
  MiniRust's is a plain load, so `movesOk` rejects any body that reads a
  possibly moved-out local before re-initializing it, propagating moved-out sets
  forward from `[]` at `bb0` across `Goto` and `SwitchInt` edges
  (`movedAtEntry`) and treating `Return` as reading `_0`;
* temporaries without storage markers (`alwaysStorageLiveLocals`, which
  `minimize`'s init block allocates) are never mentioned (`mentionsOk`);
* integer destination places are an integer local `_i`, an array element
  `_i[p]` where `p` is `Index(_k)` (`_k` an integer local; a signed `_k` is
  accepted only when `N <= 2^(bits(_k) - 1)`, see the gaps) or
  `ConstantIndex { offset, min_length, from_end }` (`min_length <= N`,
  `offset < 2^63`, and `1 <= offset <= N` when `from_end`), or a scalar field
  chain `_i.f1...fk` of a `TupleSpec` local; statements assigning to an integer
  place `dst` are `dst = Use(op)`, `dst = UnaryOp(Neg | Not, op)`,
  `dst = BinaryOp(Add | Sub | Mul | Div | Rem | BitXor | BitAnd | BitOr | Shl | Shr | AddUnchecked | SubUnchecked | MulUnchecked | ShlUnchecked | ShrUnchecked, opL, opR)`,
  `dst = Cast(CastKind::IntToInt, op, targetTy)` (from any integer or `bool`
  type, where `minimize` casts `bool` via `transmute::<u8>` followed by
  `CastOp::IntToInt`), or (into a `usize` place) `dst = Len(_j)` of an array
  local;
* for a `bool` `_i`: `_i = Use(op)`, `_i = UnaryOp(Not, op)`, and
  `_i = BinaryOp(BitAnd | BitOr | BitXor, opL, opR)` with `bool` operands, and
  `_i = BinaryOp(Eq | Ne | Lt | Le | Gt | Ge, opL, opR)` with two integer
  operands of one type or two `bool` operands. `minimize` translates the
  comparisons to `BinOp::Rel`, `!b` to `build::not(b)` (a transmute of
  `1u8 - transmute::<u8>(b)` back to `bool`), `BitAnd | BitOr | BitXor` on
  `bool` to `build::bool_and`, `build::bool_or`, and `build::bool_xor`
  (`boolBitOp`: integer `BitAnd | BitOr | BitXor` on the `transmute::<u8>`
  views, transmuted back to `bool`), and a `bool` constant to `Constant::Bool`;
* for a `core::cmp::Ordering` `_i`: `_i = Use(copy _j | move _j)` of an
  `Ordering` local, and the three-way comparison `_i = BinaryOp(Cmp, opL, opR)`
  of two integer operands of one type or two `bool` operands. MiniRust's
  `RelOp::Cmp` returns the `i8` `-1`, `0`, or `1`, and `minimize` transmutes it
  to its translation of `Ordering` (`orderingTy`: a one-byte `Type::Enum` with a
  directly encoded `i8` tag, built as `translate_enum` does for
  `#[repr(i8)] enum Ordering { Less = -1, Equal = 0, Greater = 1 }`), so the
  tag is re-validated by `decode_discriminant`;
* for a 2-tuple `(Int, bool)` `_i`: `_i = Use(copy _j | move _j)` of a
  `(Int, bool)` local of the same type,
  `_i = BinaryOp(AddWithOverflow | SubWithOverflow | MulWithOverflow, opL, opR)`
  with two integer operands `opL`, `opR` of type `Int` (`BinOp::IntWithOverflow`),
  and `_i = Aggregate(AggregateKind::Tuple, [opInt, opBool])` (`ValueExpr::Tuple`
  at `IntType::with_overflow`); field projections `_j.0` and `_j.1` translate to
  `PlaceExpr::Field(PlaceExpr::Local(_j), 0)` and `PlaceExpr::Field(PlaceExpr::Local(_j), 1)`;
* for an array local `_i : [T; N]`: `_i = Use(copy _j)` of an array local of the
  same type, `_i = Aggregate(Array(T), [op_0, .., op_{N-1}])`, or
  `_i = Repeat(op, N)` with `N > 0` (or `N = 0` when `op` is a constant);
* for a layout-backed tuple or single-variant struct place `dst` (`_i` or a
  nested sub-tuple/struct field chain `_i.f1...fk`): `dst = Use(copy p)` of a
  place of the same `TupleSpec`, or
  `dst = Aggregate(Tuple | Adt(_, 0, None), [op_0, .., op_{M-1}])`;
* for a thin raw pointer temporary `_i : *const T` / `*mut T`:
  `_i = &raw const q` / `_i = &raw mut q` of the same mutability, where `q` is a
  borrow target of pointee type `T` (`ptrTargetSpec`: an integer parameter, an
  in-bounds `ConstantIndex` element of an array parameter, or a scalar field
  chain of a `TupleSpec` parameter), `_i = Use(copy _p | move _p)` of a pointer
  local of the same type, `_i = Cast(PtrToPtr, copy _p, _)` of a pointer to `T`
  that does not add mutability, and `_i = BinaryOp(Offset, copy _p, const 0)`;
  an integer local `_i : T` may also be assigned `Use(copy (*_p) | move (*_p))`
  through a pointer `_p` to `T` (`ptrDerefReadOk`), and `(*_p) = rv` writes an
  integer rvalue `rv` of type `T` (checked like an integer destination's
  rvalue) through a `*mut T` local `_p`; every borrowed parameter is subject to
  `ptrAliasingOk` (see the gaps);
* `PlaceMention(p)` on any unprojected local `_i`, `(Int, bool)` field `_i.0` /
  `_i.1`, or `TupleSpec` field chain `_i.f1...fk`;
* terminators are `Goto`, `SwitchInt` on any integer or `bool` fragment operand
  with distinct in-range values (`minimize` switches on `transmute::<u8>(b)` for
  a `bool`), `Return`, and `Unreachable`; all targets are blocks of the body; no
  cleanup blocks.

`minimize` translates `Index(_k)` to `PlaceExpr::Index` with index `Load(_k)`,
field chains `p.f1...fk` to nested `PlaceExpr::Field` projections,
`Aggregate(Array | Tuple | Adt)` and `Repeat(op, N)` to `ValueExpr::Tuple` (the
latter with `N` copies of `op`), and `Len` of an array to the constant `N`.
Upstream `minimize` rejects `ConstantIndex` (`span_bug!`); `translateFn` lowers
it to `PlaceExpr::Index` with the constant `usize` index `offset` (or
`N - offset` when `from_end`), which is the index MIR defines for it.

`translateFn` also transcribes `minimize`'s raw pointer cases, and `inFragment`
admits thin raw pointer temporaries (`*const T` / `*mut T` to integer pointees)
under `ptrAliasingOk` (see the gaps for excluded raw pointer constructs):
`*const T` / `*mut T` become `Type::Ptr(PtrType::Raw { meta_kind })`
(`rawPtrTypeOf`), `&raw const p` / `&raw mut p` on parameter places
(`ptrTargetSpec`: an integer parameter local `_k`, an in-bounds `ConstantIndex`
element of an array parameter, or a scalar field chain of a `TupleSpec`
parameter) become `ValueExpr::AddrOf` at the thin raw pointer type, `*_j`
becomes `PlaceExpr::Deref(Load(_j), T)`, a `PtrToPtr` cast between thin raw
pointers is its operand (admitted by `inFragment` when pointee types match and
mutability is not added), and `Offset(l, r)` becomes
`PtrOffset { inbounds: true }(l, MulUnchecked(r, size_of::<T>()))`
(`ptrOffsetExpr`, admitted by `inFragment` when `r` is the constant `0` via
`zeroOffsetConstOk`). `minimize`'s translation of `PointerExposeProvenance` and
`PointerWithExposedProvenance` casts, which ends the block with an intrinsic
call and continues in a fresh block, is not transcribed (`translateFn` returns
`none`).

### States

`Correspondence/Relation.lean` defines `StateRel body f ctx s m` (for execution
within MIR blocks) and `StartRel body f ctx s mInit` (for entry at `minimize`'s
synthesized `f.start` block without requiring a phantom `bb0` machine), and
`Correspondence/Simulation.lean` defines `StateRelN body f ctx s m` (bundling
`StateRelAt` with `NonScalarLive`, `BorrowsOk`, and `LocalsOk` at
`ctxWithBorrows body ctx s.memory.borrows` so each Anneal borrow tag is tied to
the MiniRust address and provenance of its target place): the
MiniRust machine has one enabled thread whose stack is `[caller, callee]`; the
callee runs `f` at the corresponding program point; a MIR local `_i` is in the
callee's locals map exactly when Anneal's slot is live (or `_i` is a
temporary that the init block allocated), pointing to its own `Stack`
allocation whose bytes are the encoding of a slot (`Uninit` bytes for an
uninitialized slot, little-endian bytes for an initialized scalar, only `0` or
`1` for an initialized `bool`, only the tags `255`, `0`, or `1` for an
initialized `Ordering`, 8-byte `ptrBytes` carrying the target allocation's
provenance and byte address for an initialized thin raw pointer, concatenated
element encodings for an initialized `[T; N]` array, and field encodings placed
at compiler layout offsets with `AbstractByte::Uninit` preserved at all
inter-field and trailing padding bytes for `(Int, bool)` and `TupleSpec`
tuples/structs; `LocalsOk`, with non-scalar array and `TupleSpec` arguments
remaining live and initialized under `StateRelN`); MiniRust's bytes encode
Anneal's slots except for locals that Anneal's `move` de-initialized and that
`movesOk` keeps unread (`StaleOk`, with address-taken locals never moved so
`StaleOk.addrTaken_eq` holds); the caller's return place is a live,
large-enough, aligned allocation and the caller's allocations and initial
argument allocations lie below `2^32`, clear of `BM.pickAddr`'s candidates
(`CtxOk`); and Anneal's memory has no protectors, call stack, or caller-owned
referents, while its borrow table satisfies `BorrowsOk` (empty for all-scalar
bodies). `ctx` fixes everything the callee does not determine: caller frame,
unwind payloads, the allocations below the callee's locals, the addresses of
the return place and the arguments (arbitrary below `2^32`, subject to
alignment and in-bounds size), and the caller's continuation.

### Theorems

All proofs are complete; `Audit.lean` fails the build unless each of the
following depends only on `propext`, `Quot.sound`, and `Classical.choice`.

* `step_correspondence_N`, `step_correspondence` (`Simulation.lean`): for a
  fragment body, its translation, and `StateRelN`-related states (or `StateRel`
  for all-scalar bodies), one step of Anneal's coalgebra
  `stepMirFn body s` and one `Machine::step` satisfy `StepRelN` / `StepRel`: a
  silent Anneal step and an Anneal branch observation (the `switchInt` leakage
  tag) match a MiniRust step to a `StateRelN`-related state; an Anneal normal
  return of `v` matches a MiniRust step that pops the callee, writes the
  encoding of `v` to the caller's return place, deallocates every callee local,
  and continues the caller (`ReturnRel`); Anneal UB matches MiniRust UB
  (`throw_ub!`, never a spec panic, deadlock, or unsupported construct); every
  other Anneal outcome, including `unsupported`, is impossible.
* `iterMovedEntries_stabilizes`, `movesOk_iff_blockMovesOk`,
  `movedAtEntry_least`, `blockMovesOk_antitone`, `movesOk_of_preFixedPoint`,
  `movesOk_iff_exists_preFixedPoint` (`Simulation.lean`): unconditional
  finite-fuel stabilization of forward CFG move propagation (`movedAtEntry`),
  Knaster–Tarski least fixed-point optimality, antitonicity of `blockMovesOk`,
  and Park-induction soundness and completeness for inductive pre-fixed-point
  certificates on well-typed CFGs.
* `step_start_N`, `step_start`, `initMachineState_startRel` (`Simulation.lean`):
  proves for every translated function `f` that `initMachineState body args`
  (with `argsOk body args = true` and `CtxOk body ctx`) satisfies `StartRel` at
  `f.start`, and that `minimize`'s synthesized entry block
  (`f.start = bbName body.basicBlocks.length`: `StorageLive` of each temporary
  of `alwaysStorageLiveLocals`, then `Goto(bb0)`) runs in `initLen body` steps
  to `StateRelN` (and `StateRel`).
* `reaches_rel_N`, `reaches_rel`, `run_ret_N`, `run_ret`, `run_ub_N`, `run_ub`,
  `run_ret_from_start`, `run_ub_from_start`, `mirCall_ret`, `mirCall_ub`
  (`Run.lean`): lifted to Anneal's interaction trees `mirTree body s` and
  `mirCallTree body args`: if Anneal returns `v` (or can reach UB), then
  MiniRust started either at `bb0` or at `f.start` performs the corresponding
  return (or raises UB) within finitely many steps.
* `steps_error_N`, `steps_error`, `steps_error_from_start`,
  `mirCall_steps_error` (`Run.lean`): conversely, if MiniRust stops with *any*
  error within `n` steps from `StateRelN`, `StateRel`, `StartRel`, or
  `mirCallTree body args`, either the error is UB and Anneal can reach UB, or
  MiniRust already completed the callee's return (`ReturnRel`, matching an
  Anneal `ReachesRet`) in `k < n` steps and only errored later inside the
  unmodeled caller frame.
* `mirNoUB_safe_N`, `mirNoUB_safe`, `mirNoUB_safe_from_start`, `mirCall_noUB`,
  `runA_noUB` (`Run.lean`): if Anneal's interaction tree satisfies `MirNoUBTree`
  (`TreeSafe`), MiniRust never stops with any error (`.ub`, `.specPanic`,
  `.deadlock`, or `.unsupported`) anywhere during the callee's execution.
* `steps_outcome_N`, `steps_outcome`, `steps_outcome_N_from_start`,
  `steps_outcome_from_start`, `mirCall_outcome_N`, `mirCall_outcome`,
  `mirNoUB_progress_N`, `mirNoUB_progress`, `mirNoUB_progress_N_from_start`,
  `mirNoUB_progress_from_start`, `mirCall_progress_N`, `mirCall_progress`,
  `mirNoUB_diverges_steps_ok_N`, `mirNoUB_diverges_steps_ok`,
  `mirNoUB_diverges_from_start`, `mirNoUB_diverges_rel_N_from_start`,
  `mirNoUB_diverges_rel_from_start`, `mirCall_diverges_steps_ok`,
  `mirCall_diverges_rel_N`, `mirCall_diverges_rel`, `treeSafe_of_step_inv`,
  `noRet_of_step_inv`, `treeSafe_of_tau_inv`, `noRet_of_tau_inv` (`Run.lean`):
  total `n`-step outcome trichotomy and forward progress for all `n : Nat`
  (either still running in lockstep `StateRelN` / `StateRel`, already returned
  via `ReturnRel` in `k ≤ n` steps, or stopped with `.ub` matching `FaultNow`),
  specializing under `MirNoUBTree` and non-termination to prove that diverging
  UB-free loops (both silent-step and branch-observing) step forever in lockstep
  `StateRelN` / `StateRel` + `Reaches`.

### Witnesses

`Correspondence/Witness.lean` discharges every hypothesis for concrete
programs, computing both semantics in the kernel (`decide`/`rfl`, no
`native_decide`):

* `tempMove`, `crossBlockMove`, `loopTempMove`, `storageLiveArgRet`,
  `diamondMoveJoin`, `tupleAggCastMove`, and `ordBoolCastTempMove` (MR-1.3):
  `tempMove` is
  `fn(x: u32) -> u32 { let y = (x + 1) * 2; if y == 8 { 100 } else { y } }`
  with `u32` and `bool` temporaries, `StorageLive`/`StorageDead`, root `move`
  in a `BinaryOp`, a `Use`, and a `switchInt` discriminant, `Deinit` of a
  moved-from temporary, and an unused temporary `_4` that the init block
  allocates (`tempMove3_*`, `tempMove2_*`, including `StorageLive` reusing the
  first-fit address that `StorageDead` released); `crossBlockMove` is a 4-block
  CFG exercising forward dataflow `movesOk` (`movedAtEntry`) across `Goto` and
  `SwitchInt` edges, moving the incoming argument `_1`, projected tuple moves
  `move (_2.0)` and `move (_2.1)` on a `(u32, bool)` temporary, `StorageLive`
  re-allocating already-live locals, `Deinit` of a `(u32, bool)` tuple, and
  idempotent `StorageDead` (`crossBlockMove20_*`, `crossBlockMoveOv_*`);
  `loopTempMove` is a cyclic 4-block loop CFG with two heterogeneous unmarked
  temporaries (`alwaysStorageLiveLocals = [4, 5]`, `initLen = 3`), multi-pass
  back-edge fixpoint convergence of `iterMovedEntries`, per-iteration
  `StorageLive`/`StorageDead`/`Deinit`/`SwitchInt(move _3)`, live re-allocation
  of `_2`, and idempotent `StorageDead(_2)` on `n = 0` (`loopTempMove3_*`,
  `loopTempMove0_*`); `storageLiveArgRet` re-allocates an argument local `_1`
  and the return place `_0` via `StorageLive` from their initial `< 2^32`
  addresses onto first-fit `allocCandidate` addresses before returning;
  `diamondMoveJoin` merges asymmetric moved-out sets across a 4-block diamond
  CFG (`movedAtEntry` joining outgoing `[1]` and `[2, 1]` to `[1, 2]` at `bb3`)
  while returning a join-initialized temporary (`diamondMoveJoinTrue_*`,
  `diamondMoveJoinFalse_*`); `tupleAggCastMove` exercises `Operand::Move`
  inside `Rvalue::UnaryOp(Neg, move _1)`,
  `Rvalue::Cast(IntToInt, move _2, u32)`, `Rvalue::UnaryOp(Not, move _4)`
  (self-assign move), `Rvalue::Aggregate(Tuple, [move _3, move _4])`, and
  projected field move `Use(move (_5.0))` (`tupleAggCastMoveNeg5_*`, plus
  `ctx0_ok_trailing_temp_addrs` witnessing that `CtxOk.addrs` constrains only
  `i ≤ argCount`); `ordBoolCastTempMove` exercises `Cast(IntToInt, move _3,
  u32)` from a moved `bool`, `SwitchInt(move _4)`, and `StorageLive`,
  `BinaryOp(Cmp, move _, move _)`, `Use(move _5)`, `Deinit`, and `StorageDead`
  on a `core::cmp::Ordering` temporary local reusing `_4`'s freed `2^32` slot,
  together with a concrete Park-induction certificate witness
  (`ordBoolCastTempMove_movesOk_by_preFixedPoint`, `ordBoolCastTempMoveTrue_*`,
  `ordBoolCastTempMoveFalse_*`); `deadRead`, `deadAssign`, `deadDeinit`, and
  `deadPlaceMention` access a local (including projected `PlaceMention(_1.0)`)
  after `StorageDead` (UB in both models via `mirCall_ub`,
  `mirCall_steps_error`, `mirCall_outcome`, and direct runs); `moveReuse`,
  `crossBlockMoveReuse`, `loopBackEdgeReuse`, `projAssignMoveReuse`,
  `projFieldMoveReuse`, `sameRvalueMoveReuse`, `moveRetPlace`, and
  `diamondHalfMoveReuse` read a local after moving out of it — across
  statements, blocks, cyclic back-edges, projected assignments, projected
  field reads after a root tuple move, operands of a single rvalue (`readsOk`),
  `Return` (`termReadsOk`), and one-armed diamond merges — rejected by `movesOk`
  with concrete semantic disagreements (`moveReuse7_*`, `loopBackEdgeReuse1_*`,
  `projFieldMoveReuse_*`, `sameRvalueMoveReuse5_*`, `moveRetPlace_*`,
  `diamondHalfMoveReuseFalse_*`); `unmarkedTempAssign`, `storageDeadRet`,
  `storageDeadArg`, `storageDeadArgReadAfter`, and `projectedDeinit` exercise
  the soundness and well-formedness boundaries of `mentionsOk`, `storageDeadOk`
  (for both `_0` and arguments), and projection-free `Deinit` with concrete
  execution and UB witnesses; and `bm_allocate_and_deallocate_ub_cases` /
  `evalStatement_deinit_ok_dead_and_misaligned` directly verify the UB and
  normal paths of `BM.allocate`, `BM.deallocate` (including exact
  `AllocationKind` diagnostic formatting across all five `AllocationKind`
  variants), and `Statement::Deinit`.

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
* `paddedStructOps` and `nestedTupleOps` (plus
  `tuple_encode_decode_place_edge_cases`), bodies with a padded single-variant
  struct `Padded(u8, u32, u16)` (`offsets = [0, 4, 8]`, `size = 12`,
  `align = 4`) and a nested padded tuple `((u8, u32), u16, ())` (including
  zero-sized `()` at offset `10`), exercising whole-struct and zero-sized field
  `Use(Copy)`, `AggregateKind.adt` and nested `AggregateKind.tuple`
  construction, multi-step `ProjectionElem.field` reads (`copy _4.0.1`),
  in-place sub-tuple writes (`_4.0 = ...`), and in-place scalar field writes
  (`_1.1 = ...`, `_4.0.1 = ...`), with byte-level theorems confirming that
  `AbstractByte::Uninit` is preserved at all inter-field and trailing padding
  offsets (`paddedStructOk_minirust_padding_bytes`,
  `nestedTupleOk_minirust_padding_bytes`), stack frame teardown across
  heterogeneous layouts (`*_minirust_ret_dealloc`), `*_minirust_noUB` and
  `*_minirust_progress`, and UB paths for faulting aggregate operands, faulting
  nested field write RHS, and uninitialized tuple copies (`nestedTuple*Ub_*`).

* `cmpNotSwitch`, an `(i8, i8, bool) -> i8` body that compares integers with
  signed `<` and `==`, negates a `bool` (`!b`, through `build::not`'s
  transmutes), compares `bool`s (`b > false`), and branches with `SwitchInt` on
  `bool` (through the transmute to `u8`) across four blocks: for
  `(-1, 1, false)` both semantics return `-1i8` (`cmpNotNeg1_anneal_ret`,
  `cmpNotNeg1_minirust_ret_from_start`, and the direct 9-step run
  `cmpNotNeg1_minirust_direct`), which an unsigned comparison of the bit
  patterns would get wrong; for `(3, 2, true)` both return `2i8`
  (`cmpNot3_*`).
* `leNeGe`, a `(u8, u8) -> bool` body whose `bool` return place is also the
  `SwitchInt` scrutinee, exercising `<=`, `!=`, `>=`, and `bool` returns
  (`leNeGe250_*` returns `true`, `leNeGe5_*` returns `false`).
* `boolCastI8`, a `bool -> i8` body exercising `Cast(CastKind::IntToInt)` on
  `bool` across both `true` and `false` branches, plus `argsOk` rejection of
  the invalid `bool` byte `2` (`boolCastTrue_*`, `boolCastFalse_*`,
  `boolCastInvalidArg_rejected`).
* `uninitBool`, `uninitBoolNot`, `uninitBoolRel`, `uninitBoolBitAnd`, and
  `uninitBoolBitOrRhs`, whose `SwitchInt`, `UnaryOp(Not)`, `BinaryOp(Eq)`,
  `BinaryOp(BitAnd)` (uninitialized LHS), and `BinaryOp(BitOr)` (`const true`
  LHS, uninitialized RHS — confirming MIR `BitOr` on `bool` does not
  short-circuit) on an uninitialized `bool` are UB in both semantics
  (`uninitBool*_minirust_ub_from_start`, `uninitBool*_minirust_direct`).
* `cmpSel` and `boolBitOrdUse`, `(i8, i8, bool) -> Ordering` and
  `(bool, u8, Ordering) -> Ordering` bodies that switch on `bool` (including
  `PlaceMention(_0)` on the uninitialized `Ordering` return place and
  `build::bool_and`, `build::bool_or`, and `build::bool_xor` in
  `boolBitOrdUse`) and return signed `i8` `Cmp`, unsigned `u8` `Cmp`
  (`255u8.cmp(&1u8) = Greater`), `bool` `Cmp`, or `Use(copy _3)` of an
  `Ordering` argument (`cmpSelLess_*`, `cmpSelEqual_*`, `cmpSelGreater_*`,
  `boolBitOrdUseCmp_*`, `boolBitOrdUseCopy_*`, and `argsOk` rejection of
  invalid `Ordering` tag bytes `2` and `128` in `boolBitOrdInvalidTag_rejected`);
  and `uninitOrdering`, whose return of an uninitialized `Ordering` is UB in
  both semantics (`uninitOrdering_*`).
* `checkedArithI8`, a signed `i8` body with a `(i8, bool)` local `_3` and a
  `bool` local `_4`, exercising `AddWithOverflow`, `SubWithOverflow`, and
  `MulWithOverflow`, field projections `_3.0` and `_3.1` in `Use`, `BinaryOp`,
  `UnaryOp`, and `SwitchInt`, across no-overflow inputs (`checkedArithOk_*`),
  `INT_MAX + 1` (`127i8 + 1i8 = (-128i8, true)`, `checkedArithAddOv_*`),
  `INT_MIN - 1` (`-128i8 - 1i8 = (127i8, true)`, `checkedArithSubOv_*`), and
  signed multiplication overflow (`64i8 * 2i8 = (-128i8, true)`,
  `checkedArithMulOv_*`), plus `argsOk` rejection of an invalid `bool` byte in
  a tuple argument (`checkedArithInvalidTupleArg_rejected`).
* `checkedTupleU32`, a `(u32, u32) -> (u32, bool)` body returning a padded
  8-byte `(u32, bool)` 2-tuple in `_0`, exercising `PlaceMention(_0)`,
  `PlaceMention(_0.0)`, and `PlaceMention(_0.1)` on the uninitialized tuple
  return place, unsigned `0u32 - 1u32 = (u32::MAX, true)`
  underflow followed by `u32::MAX + 1u32 = (0u32, true)` overflow
  (`checkedTupleUnderAddOv_*`), unsigned multiplication overflow
  `65536u32 * 65536u32 = (0u32, true)` and `Aggregate(Tuple, [copy (_0.0), copy (_0.1)])`
  (`checkedTupleMulOv_*`), and no-overflow execution (`checkedTupleOk_*`),
  writing 4-byte `u32` at offset `0`, 1-byte `bool` at offset `4`, and 3
  trailing `AbstractByte::Uninit` padding bytes at offsets `5..8`; plus
  `uninitTupleField0` and `uninitTupleField1`, whose reads of `_0.0` and `_0.1`
  from an uninitialized `(u32, bool)` local raise UB in both semantics (with
  converse error soundness `uninitTupleField0_converse_error` via
  `mirCall_steps_error` and total outcome trichotomy `uninitTupleField1_outcome`
  via `mirCall_outcome`).
* Ground-truth checks of the interpreted operators: signed and unsigned
  `BinOp::Rel`, `RelOp::Cmp` returning `i8`, `bool` ordering, a value-type
  mismatch being a spec panic, `CastOp::Transmute` between `bool` and `u8`
  (including the invalid byte `2` and a size mismatch, both UB),
  `Type::Bool` decoding, `UnOp::Int` on a `bool` being a spec panic
  (`relLt_signed`, ..., `bitNot_bool_panics`), `IntType::with_overflow` layouts
  and encodings on `i8` and `u32`, `TupleHeadLayout::full_size_and_align` and
  `LayoutStrategy::compute_size_and_align` on sized and unsized layouts,
  `BinOp::IntWithOverflow` on `INT_MAX + 1`, `INT_MIN - 1`, `UINT_MAX + 1`,
  `0 - 1`, multiplication overflow, and a non-integer operand (`specPanic`),
  `Machine::ptr_offset_inbounds` in-bounds and out-of-bounds UB,
  `ValueExpr::Tuple`, and `PlaceExpr::Field` (including `Type::Union` field
  projections, `specPanic`s on invalid field indices, missing unsized tail,
  out-of-bounds field offset, and non-projectable types, and
  `IntType::with_overflow` / `BinOp::IntWithOverflow` across `u8`, `i8`, `i16`,
  `u16`, `i32`, `u32`, `i64`, `u64`, `i128`, and `u128`;
  `withOverflow_i8_layout`, ..., `evalPlace_field_union_and_offset_panic`); and of
  the representation of
  enums, tuples, unions, slices, and trait objects: exactly the bytes `0`, `1`,
  `255` are valid at `orderingTy` (`ordering_validTags`), decoding, encoding,
  `check_value`, and transmutes at `orderingTy` (including invalid tags, an
  `Uninit` byte, and `decode_discriminant` short-circuiting before its
  `fallback` continuation in `decodeDiscriminant_short_circuits`), a padded
  `(i8, bool)` tuple whose size rounds up to its alignment and whose padding
  encodes as `Uninit` and is ignored by decoding (`decode_ordering_less`, ...,
  `checkValue_tuple_arity`), `Type::Union` chunk decoding, encoding,
  `check_value`, and `CastOp::Transmute` round-tripping with `paddedPairTy`
  (including UB when an `Uninit` union chunk overlaps a non-padding tuple
  field; `layout_union`, `decode_union`, `encode_union`,
  `checkValue_union_chunk_size`, `checkValue_union_chunk_data`,
  `transmute_union_paddedPair`, `transmute_paddedPair_union`,
  `transmute_union_paddedPair_uninit_ub`), and unsized `Slice`, `TraitObject`,
  and unsized `Tuple` layouts and `specPanic`s (`layout_slice`, ...,
  `checkValue_unsized_panics`).

`Correspondence/PointerWitness.lean` runs raw pointer programs to completion
in both semantics (Anneal by `runA_sound` / `faultsA_sound`, MiniRust by
`decide +kernel` on `minimize`'s translation), on top of the per-construct
lemmas of `Correspondence/Pointers.lean` (MiniRust's thin pointer bytes
`ptrBytes` and their `decode`, `encode`, and `check_value`; Anneal's
`&raw`, `*p`, `Offset`, `PtrToPtr`, and exposure rules) and the
statement-level lemmas of `Correspondence/PointerStep.lean` on which
`step_correspondence_N` rests for raw pointers.

* In the fragment (`*_inFragment`), and proved end to end through
  `mirCall_ret`, `mirCall_noUB`, and `mirCall_progress_N` (returns),
  `mirCall_diverges_steps_ok` and `mirCall_diverges_rel_N` (divergence), or
  `mirCall_ub`, `mirCall_steps_error`, and `mirCall_outcome_N` (UB) besides the
  direct runs, both semantics return the same value on `ptrRoundTrip`
  (`&raw mut x`, a read and a write through the pointer, a `PtrToPtr` cast,
  and a read through the cast pointer; `6` for `x = 5`), `arrayParamPtr`
  (disjoint `&raw mut a[-2 of 2]` and `&raw mut a[-1 of 2]` borrows, that is
  of `a[0]` and `a[1]`, on an array parameter `a: [u32; 2]`, `Offset(p, 0)`,
  `move` and `StorageDead`/`Deinit` on pointer temporaries, and dereference
  reads and writes through both pointers; `19` for `a = [5, 7]`), `fieldPtr`
  (`&raw mut s.1` at byte offset `4` of `Padded`; `100`), `nestedFieldPtr`
  (disjoint `&raw mut t.0.1` at byte offset `4` with pointee `u32` and
  `&raw mut t.1` at byte offset `8` with pointee `u16` on
  `t: ((u8, u32), u16, ())`, preserving `.Uninit` padding; `59`),
  `ptrCountdown` (a four-block loop that counts `x` down through
  `&raw mut x`, reading `*p` before each `switchInt`, then reads `x` directly;
  `3` for `x = 3`), `constBorrowLoop` (a fresh `&raw const x` read through and
  killed by `StorageDead` in each iteration of a loop; `15` for `x = 5`), and
  `repointPtr` (`&raw mut a[0 of 2]` and `&raw mut a[1 of 2]`, a read through
  a copy of the first pointer, then the same initialized pointer local
  overwritten with the second pointer and written through; `105` for
  `a = [5, 7]`); both diverge in lockstep (`StateRelN` + `Reaches`) on
  `ptrSpinLoop` (`_2 = &raw mut _1` in `bb0`, then `PlaceMention(_2)`,
  self-assignment `_2 = Offset(copy _2, const 0_usize)`, `_0 = copy (*_2)`,
  and `(*_2) = copy _0` in `bb1`); and both raise UB on `uninitPtrReadUb` and
  `uninitPtrWriteUb` (reading or writing through an uninitialized pointer
  temporary), `deadPtrReadUb` (reading through a pointer temporary after its
  `StorageDead`), `uninitPtrOffsetUb` (`Offset(copy _p, 0)` on an
  uninitialized pointer temporary), and `derefWriteRhsUb`,
  `derefIdxWriteRhsUb`, and `derefFieldWriteRhsUb` (writing an uninitialized
  rvalue operand through a valid `*mut` pointer to an integer local, to a
  `ConstantIndex` array element, or to a `TupleSpec` scalar field chain).
* Outside the fragment (`*_notInFragment`), both semantics agree on
  `arrayElemPtr` (`&raw mut a[1]` on a temporary array; `12`) and `dangling`
  (UB on a read after `StorageDead` of the borrowed temporary), and they
  disagree on the divergences listed under the gaps: `offsetDeref`
  (`*p.offset(1)` reads `a[1] = 7` in MiniRust and `a[0] = 5` in Anneal;
  `offset(2)` then a read, `offset(3)`, and `offset(usize::MAX)` are UB in
  MiniRust and return `5` in Anneal), `misaligned` (UB in MiniRust only),
  `exposeTwice` (`0` in MiniRust, `65536` in Anneal), and `directWrite` and
  `frozenWrite` (UB in Anneal only).

`Audit.lean` logs `[ANCHOR-AUDIT]`, `[SIMULATION-AUDIT]`, `[WITNESS-AUDIT]`,
and `[POINTER-AUDIT]` lines ending in `sorry_free=true` (via
`#check_theorem_deps`, which also rejects duplicate declaration names and
non-`theorem` constants) and fails the build if any listed declaration depends
on `sorryAx` or a non-standard axiom.

### Gaps

These are deliberate and are the first things to lift:

* **Moves are checked path-insensitively over the CFG.** `movesOk` propagates
  possibly moved-out locals forward from `[]` at `bb0` across `Goto` and
  `SwitchInt` edges (`movedAtEntry`), taking the union at control-flow merges; a
  body that moves out of a local on only one incoming branch and reads it after
  the merge without re-initializing it on that branch is rejected unless branch
  correlation is tracked. Only root moves de-initialize in Anneal; projected
  moves read like copies.
* **Temporaries of the init block are never mentioned.** Anneal keeps a
  temporary without storage markers dead, whereas `minimize`'s init block
  allocates it, so the fragment requires that the body never mentions one.
* **One resolution of the address choice.** `BasicMemory::allocate`'s `pick`
  is resolved by first fit over the multiples of `2^32`; results hold for that
  resolution, which the correspondence fragment cannot observe (it has no
  pointer-to-integer casts or pointer comparisons). The interpretation itself
  can now observe addresses (`PointerExposeProvenance`, `comparePtr`, and
  alignment checks), so pointer witnesses hold for this resolution only.
* **One thread, called from a caller frame.** MiniRust makes it UB for the
  bottom frame of the main thread to return, while Anneal's root body returns
  normally, so the relation places the callee above an arbitrary caller. What
  the caller does after the return is outside the relation. Call setup
  (`Terminator::Call`, argument passing) is not interpreted; witnesses start
  at the callee's entry.
* **Branch observations.** Anneal's `switchInt` emits the scrutinee as a
  visible leakage event; MiniRust has no counterpart, so `StepRel` matches it
  with an ordinary MiniRust step.
* **Scalar-family locals vs. array and `TupleSpec` argument locals.** Scalar
  fragment types (`Int`, `bool`, `Ordering`, and `(Int, bool)` 2-tuples) are
  supported across `_0`, arguments, and temporaries (with
  `StorageLive`/`StorageDead`/`Deinit` and `move`), whereas homogeneous `[T; N]`
  arrays and general nested padded tuples and single-variant structs
  (`TupleSpec`, with integer leaf fields and `()`) appear on argument locals
  that stay live and initialized throughout execution (no `StorageLive`,
  `StorageDead`, `Deinit`, or `move`, and `_0` does not return `[T; N]` or
  general `TupleSpec`). An `Ordering` local is written by `Cmp` or `Use` and
  read by `Use` or `Return` (no `Ordering` constants, `Discriminant`, or
  `SwitchInt` on it); `Type::Enum` (beyond `Ordering`) and `Type::Union` are
  interpreted as representations (layout, `decode`, `encode`, `check_value`)
  without `ValueExpr::{Union, Variant, GetDiscriminant}`,
  `Statement::SetDiscriminant`, or downcast projections. Raw pointers are
  restricted (below); there are no references, slices, nested arrays,
  multi-variant ADTs, other casts, calls, drops, or assertions.
* **`Repeat(copy p, 0)` is excluded (while `Repeat(const c, 0)` is included).**
  Anneal evaluates `op` once before replicating it, while `minimize`'s
  `list![op; 0]` never evaluates `op`, so the models disagree when `op` is a
  `copy` that can fault (an uninitialized local or out-of-bounds array index),
  whereas a constant operand never faults in either semantics.
* **Projected `PlaceMention(_j[p])` is excluded (while `PlaceMention` on `_j`,
  `_j.0`/`_j.1`, and `TupleSpec` field chains `_j.f1...fk` is included).**
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
* **Raw pointers are in the correspondence only under a borrow discipline
  (MR-3.1).** The fragment admits thin raw pointer temporaries to integer
  pointees; `_i = &raw const q` / `&raw mut q` of a parameter `q` that is an
  integer local, an in-bounds `ConstantIndex` element of an array, or a scalar
  field chain of a `TupleSpec` (`ptrTargetSpec`); pointer copies (`copy _p`,
  `move _p`, `PtrToPtr` between equal pointee types that never adds
  mutability, and `Offset(_p, 0)`); reads `copy (*_p)` through any such
  pointer and writes `(*_p) = rv` through `*mut` pointers, both at the pointee
  type; and storage statements on pointer temporaries. `ptrAliasingOk` requires every borrowed
  local to be a parameter that is never written directly, deinitialized,
  storage-cycled, or moved, and, once any `&raw mut` exists, all borrows of
  mutably borrowed locals to happen in an entry block without incoming edges
  at pairwise non-overlapping projections. `StateRelN` relates each Anneal
  borrow tag to the MiniRust address of its target (`BorrowsOk`, and
  `LocalsOk` at `ctxWithBorrows`), and `step_correspondence_N` simulates every
  such statement (`Correspondence/PointerStep.lean`). The fragment excludes
  the forms on which Anneal's model accepts executions that MiniRust, the
  ground truth, rejects or runs differently: a dereference ignores the pointer's
  `offsetBytes`, so reading through `p.offset(n)` reads `p`'s target
  (`offsetDeref 1`), misaligned reads succeed (`misaligned`), and pointers
  past the end of their allocation can be read through (`offsetDeref 2`);
  `Offset` neither scales its count by the pointee size nor checks bounds or
  overflow (`offsetDeref 3`, `offsetDeref usizeMax`); and
  `PointerExposeProvenance` returns `tag * 65536 + offsetBytes` instead of an
  address, so two pointers to one local expose different integers
  (`exposeTwice`), and `PointerWithExposedProvenance` decodes that encoding
  deterministically instead of predicting a provenance. In the other
  direction, Anneal is stricter than `BasicMemory`, which has no aliasing
  model: a direct write to a local disables earlier raw pointers to it
  (`directWrite`), and writing through a `&raw const` pointer is UB
  (`frozenWrite`). `&raw` of an out-of-bounds `ConstantIndex` succeeds in
  Anneal and only faults on use, while MiniRust's `AddrOf` evaluates the place
  and raises UB at once; and since a write through a pointer only requires its
  target local not to be dead, a pointer to a local becomes writable again in
  Anneal after `StorageDead` and `StorageLive`, while in MiniRust it keeps
  pointing to the deallocated storage. Hence the fragment borrows parameters
  only, admits `*p` only on unoffset pointers to integer pointees of matching
  type, and keeps nonzero `Offset` and the exposure casts out.
* **The interpretation is transcribed, not generated.** It is anchored to the
  generated model by token hashes and quotes the spec, but nothing proves it
  equal to the deep embedding, which has no executable semantics.
