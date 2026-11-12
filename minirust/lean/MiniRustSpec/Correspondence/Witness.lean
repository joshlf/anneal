/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Run
import MiniRustSpec.Correspondence.DeinitWindow

/-!
# Non-vacuity witnesses

The correspondence theorems are implications whose hypotheses (`inFragment`,
`translateFn`, `StateRel`, and Anneal reachability facts) could in principle
be unsatisfiable. This module discharges them for concrete programs, and
checks the conclusions against *independent* executions of the MiniRust
interpretation, all by kernel computation (`decide`/`rfl`, no
`native_decide`):

* `sumTo`: the MIR of a `u32` loop computing `n + (n-1) + .. + 1`, with
  `switchInt`, wrapping `Add`/`Sub`, constants, and `Goto`. For `n = 3`:
  - `sumTo_anneal_ret`: Anneal's semantics returns `6` (computed);
  - `sumTo_rel`: the initial states are related;
  - `sumTo_minirust_ret`: hence (by `run_ret`) MiniRust performs a return that
    writes the bytes of `6u32` into the caller's return place;
  - `sumTo_minirust_direct`: running the MiniRust interpretation directly
    (16 steps) produces exactly that return place, so the theorem's
    conclusion agrees with an independent computation.
  - `sumTo_init_step`: the init block that `minimize` prepends steps into the
    related initial machine.
* `retUninit`: the MIR of a function returning an uninitialized `_0`.
  Anneal's semantics faults with UB (`retUninit_anneal_ub`), hence MiniRust
  raises UB (`retUninit_minirust_ub` via `run_ub`, and
  `retUninit_minirust_ub_from_start` via `run_ub_from_start`), which a direct
  computation confirms (`retUninit_minirust_direct`).
* `negMention`: the MIR of a function exercising `PlaceMention(_0)` (while `_0`
  is still uninitialized), wrapping `UnaryOp(Neg)` (`_0 = -_1`), and an
  `Unreachable` branch when `_1 == 0`:
  - for `_1 = 5`: returns `2^32 - 5 = 4294967291` (`negMention5_minirust_ret_from_start`,
    verified against `negMention5_minirust_direct`);
  - for `_1 = 0`: computes `-0 = 0` and takes the `Unreachable` terminator,
    raising UB (`negMention0_minirust_ub_from_start`, verified against
    `negMention0_minirust_direct`).
* `signedEdge`: the MIR of a signed `i8` function exercising two's-complement
  sign-bit decoding (`intFromBits`), `i8::MIN` (`-128i8`, bits `128`) wrapping
  negation (`-(-128i8) = -128i8`), negative `switchInt` branch keys (`-128`,
  `-1`), signed underflow wrapping (`-128i8 + (-1i8) = 127i8`), signed
  negative-by-negative `Mul` (`(-1i8) * (-2i8) = 2i8`), and end-to-end
  `MirNoUBTree` safety transfer (`signedEdgeMin_minirust_noUB`).
* `castBitNot`: mixed-width (`i8` and `u32`) `UnaryOp(Not)` (`BitNot`) and
  signed-widening / unsigned-narrowing `Cast(IntToInt)`.
* `spinLoop`: diverging UB-free loop exercising `mirCall_diverges_steps_ok` and
  lockstep `mirCall_diverges_rel` (`StateRel` + `Reaches` preserved for all `n`).
* `divRemI8` and `remOnlyI8`: signed `i8` truncating-toward-zero `Div` and `Rem`
  (`-7 / 3 = -2`, `-7 % 3 = -1`, `i8::MIN / 1 = -128`) plus all four division
  and remainder UB conditions (`x / 0`, `i8::MIN / -1`, `x % 0`, `i8::MIN % -1`)
  and converse `mirCall_steps_error`.
* `uncheckedArithI8`: signed `i8` `MulUnchecked`, `SubUnchecked`, and
  `AddUnchecked` both succeeding at the `i8::MIN` boundary (`64 * -2 = -128`,
  `-128 - (-2) = -126`, `-126 + 127 = 1`) and triggering each operator's
  signed overflow UB (`mirCall_ub`, `mirCall_outcome`, and direct checks of
  MiniRust's `throw_ub!` messages).
* `branchSpinLoop`: diverging conditional `while x != 0 {}` loop emitting a
  visible `.emit` branch event on every iteration (`treeSafe_of_step_inv`,
  `noRet_of_step_inv`, and `mirCall_diverges_rel`).
* `shiftI8` and `shlUncheckedI8`: signed `i8` `Shr`, `Shl`, `ShrUnchecked`, and
  `ShlUnchecked` including negative shift counts wrapped via `.rem_euclid(8)` and
  all four unchecked-shift UB paths (`s >= bits` and `s < 0`).
* `bitwiseI8` (plus `countOnes_neg86_i8` / `countOnes_neg1_i8`): signed `i8`
  two's-complement `BitAnd`, `BitOr`, and `BitXor` on negative operands
  (including cancellation of infinite leading two's-complement `1` bits under
  `BitXor`), alongside ground-truth checks of `IntUnOp::CountOnes` returning
  `u32` on negative `i8` inputs.
* `heteroShiftSwitch`: mixed-type `(i8, u32)` wrapping `Shr` / `Shl` with shift
  counts `258u32, 257u32 >= 256`, constant-discriminant `SwitchInt` on `-1i8`,
  and heterogeneous `(i8, i32)` `ShrUnchecked` / `ShlUnchecked` both succeeding
  at `k = 3i32` and faulting with UB at `k = 8i32` (`8 >= i8::BITS` even though
  `8 < i32::BITS`) and `k = -1i32` (`-1 < 0`).
* `uninitOperandUb` (plus `divExact_ok_i8`, `divExact_rem_ub_i8`,
  `divExact_zero_ub_i8`, `divExact_min_neg1_ub_i8`): reading an uninitialized
  local (`copy _0` while `_0` is `.uninit`) inside a `BinaryOp` operand, a
  `UnaryOp` operand, and a `SwitchInt` scrutinee (`mirCall_ub`,
  `mirCall_steps_error`, and direct checks of MiniRust's `"load at type but the
  data in memory violates the language invariant"` UB), alongside ground-truth
  checks of all four `IntBinOp::DivExact` outcomes.
* `tempMove`, `crossBlockMove`, `loopTempMove`, `storageLiveArgRet`,
  `diamondMoveJoin`, `tupleAggCastMove`, `deadRead`, `deadAssign`,
  `deadDeinit`, `deadPlaceMention`, `moveReuse`, `crossBlockMoveReuse`,
  `loopBackEdgeReuse`, `projAssignMoveReuse`, `projFieldMoveReuse`,
  `sameRvalueMoveReuse`, `moveRetPlace`, `diamondHalfMoveReuse`,
  `unmarkedTempAssign`, `storageDeadRet`, `storageDeadArg`,
  `storageDeadArgReadAfter`, and `projectedDeinit` (MR-1.3): temporaries with
  `StorageLive`/`StorageDead` (including `StorageLive` on `_0` and argument
  locals), root and projected `move` across `Use`, `UnaryOp`, `BinaryOp`,
  `Cast(IntToInt)`, `Aggregate(Tuple, ..)`, and `SwitchInt` in straight-line,
  branching, diamond join, and cyclic loop CFGs (with multi-pass back-edge
  `movedAtEntry` fixpoint convergence), `Deinit`, multi-local `initBlock`
  allocation of heterogeneous temporaries, first-fit address reuse, dead-local
  UB across reads, `Assign`, `Deinit`, and projected `PlaceMention`, and
  concrete semantic counterexamples showing why `movesOk` (including
  intra-rvalue, projected sibling-field, `Return`, diamond merge, and
  back-edge checks), `mentionsOk`, `storageDeadOk` (for both `_0` and
  arguments), and projection-free `Deinit` are each necessary for soundness.
  Their direct MiniRust runs allocate, so they are checked by `decide +kernel`
  (kernel evaluation; still no `native_decide`).
* `checkedArithI8`, `checkedTupleU32`, `uninitTupleField0`, and
  `uninitTupleField1`: checked integer arithmetic (`AddWithOverflow`,
  `SubWithOverflow`, `MulWithOverflow`), `(Int, bool)` 2-tuple locals and
  return places (including `IntType::with_overflow` trailing `Uninit` padding
  bytes on `(u32, bool)`), `Rvalue::Aggregate(Tuple, ..)` (`ValueExpr::Tuple`),
  and `.0` / `.1` field projections (`PlaceExpr::Field`) across no-overflow and
  overflow boundary inputs (`INT_MAX + 1`, `INT_MIN - 1`, `UINT_MAX + 1`,
  `0 - 1`, and signed/unsigned multiplication overflow), plus UB on reading
  `.0` or `.1` from an uninitialized tuple local.
* `arrayOpsI8`, `arraySignedIdxI8`, and `zeroArrayI8`: fixed-size homogeneous
  arrays (`Type::Array` / `TyKind.array`), `AggregateKind.array`,
  `Rvalue.repeat`, `Rvalue.len`, whole-array `Use(Copy)`, and
  `ProjectionElem.index` / `ProjectionElem.constantIndex` (`fromEnd = false`
  and `fromEnd = true`) for both reads and in-place element writes preserving
  sibling elements, plus out-of-bounds (`idx >= count`), negative signed index
  (`idx < 0`), and zero-length array (`[i8; 0]`) construction, `Len`, and
  indexing UB, with a byte-level check that the in-place writes leave the
  sibling bytes of MiniRust's array allocation intact
  (`arrayOpsOk_minirust_inplace_bytes`).
* `arrayUninitIdxI8`: an index local that is still uninitialized (`_1[_0]`
  before `_0` is written) raises UB on both sides; MiniRust's `Load` of the
  index operand fails the validity invariant before the bounds check.
* `arrayU32Idx`: a multi-byte element type (`[u32; 3]`), so that the byte
  offset `index * elem_size` of `PlaceExpr::Index` is exercised with
  `elem_size = 4` (all other array witnesses use 1-byte `i8` elements, for
  which the offset equals the index): an in-place write at index `2` lands at
  byte offset `8` and leaves the first two elements intact, and index `3`
  raises out-of-bounds UB on both sides.
* `paddedStructOps`: a single-variant struct `Padded(u8, u32, u16)` with
  non-zero inter-field and trailing padding (`offsets = [0, 4, 8]`, `size = 12`,
  `align = 4`), exercising whole-struct `Use(Copy)`, `AggregateKind.adt`
  construction, scalar `ProjectionElem.field` reads (`_1.0`, `_1.1`, `_2.0`,
  `_2.2`), and in-place scalar field writes (`_1.1 = ...` at byte offset `4`),
  with a byte-level theorem (`paddedStructOk_minirust_padding_bytes`) confirming
  that `AbstractByte.Uninit` is preserved at padding offsets `1..4` and `10..12`
  across both whole-struct stores and in-place field mutations.
* `nestedTupleOps` (plus `tuple_encode_decode_place_edge_cases`): a nested
  padded tuple `((u8, u32), u16, ())` (with inner tuple `(u8, u32)` of size `8`,
  align `4` and zero-sized unit tuple `()` of size `0`, align `1` at offset `10`),
  exercising `AggregateKind.tuple`, nested field reads (`copy _4.0.1`,
  `copy _4.0.0`), nested in-place sub-tuple writes (`_4.0 = ...`), nested
  in-place scalar field writes (`_4.0.1 = ...`), zero-sized field `Use(Copy)`
  (`_3 = copy _4.2`), byte-level inner/outer padding preservation
  (`nestedTupleOk_minirust_padding_bytes`), and UB paths for faulting tuple
  aggregate operands, faulting nested field write RHS, and reading an
  uninitialized tuple local.
* `callerMain`/`calleePair`, `projDestCaller`/`negI8Callee`/`flipBoolCallee`,
  `chainEntry`/`chainMid`/`chainLeaf`, `callArgUbCaller`,
  `calleeDivZeroCaller`/`divTenI8Callee`, `callSpinCaller`/`idU32Callee`,
  `callMoveReuse`, `moveReinitByCall`, `condCallMoveJoin`,
  `cAbiCaller`/`cAbiCallee`, `diamondCallEntry`/`diamondMidA`/`diamondMidB`,
  `liveCallDestSpinCaller`/`spinU32Callee`,
  `calleeRetUninitCaller`/`retUninitCallee`, `callDestArgAlias`,
  `callProjMoveReuse`, `stmtMoveThenCallArg`, `recCycleA`/`recCycleB`,
  `badCallConvCaller`, `deadCallDestCaller`, `deadCallDestSpinCaller`,
  `uninitProjCallDestCaller`, `abiArgMismatchCaller`, `abiRetMismatchCaller`,
  and `argCountMismatchCaller`/`const5Callee` (MR-4.1): multi-function
  `translateProg` and `progInFragment` programs exercising `Terminator::Call`
  (`ByValue` and `InPlace` argument passing, `Constant::FnPointer`,
  `fn_from_ptr`, `check_abi_compatibility`, `create_frame` with both
  `CallingConvention::Rust` and `CallingConvention::C`, multi-step
  `Call + initBlock` entry, and `UnwindAction::{Continue, Unreachable,
  Terminate}`), multi-frame `Terminator::Return` (`StackPopAction::BackToCaller`
  into root locals and projected `.0` / `.1` tuple fields, and UB on a callee's
  uninitialized `_0`), 3-deep nested and diamond-shaped call graphs,
  call-argument, post-call `move` reuse, and callee-body UB propagation,
  diverging multi-function executions (`mirCallWithCallees_diverges_rel`,
  including a callee that never returns), soundness counterexamples for
  return-place aliasing, dead and uninitialized return places, argument-type,
  return-type, and argument-count mismatches, projected `move` call arguments,
  pre-call `move` reuse, unsupported calling conventions, and cyclic call graphs
  (where the necessity witnesses also refute the conclusion of
  `mirCallWithCallees_noUB` or `mirCallWithCallees_ub` outright), plus
  ground-truth unit checks of the `MR-4.1` `Interp` definitions and
  `progStart_outside_fragment`, which shows why the theorems start at
  `fEntry.start` under an external caller rather than at `prog.start`.
* `evalIntrinsic_*`, `evalTerminator_abortTerminator`, `translateRsIntrinsic_witness`,
  `assumeSub`, `assumeTupleCallCaller`, `assumeDeadLocal`, `assumeMoveReuse`, and
  `assumeAfterMove` (`MR-4.2`): every transcribed `IntrinsicOp` arm of
  `eval_intrinsic` (`Abort`, `Exit`, `Assume` with each of its UB checks,
  `PrintStdout` and `PrintStderr`, `Allocate` and `Deallocate` with `Heap` leak
  checking, `RawEq` with `load_raw_data` and structural `typeEq`,
  `PointerExposeProvenance`, `PointerWithExposedProvenance`, and
  `GetUnwindPayload`), `build::abort()`, `translateRsIntrinsic`, and full
  multi-function `progInFragment` block-splitting correspondence (`SegPc`,
  `SegChain`) for `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))`
  via `mirCallWithCallees_ret` and `mirCallWithCallees_ub_rel` — across multiple
  `Assume`s in one block (`assumeSub`), `Assume(move _)` + tuple-field
  projection + `Terminator::Call` across split blocks (`assumeTupleCallCaller`),
  dead-local `Assume` UB (`assumeDeadLocal`), and necessity witnesses proving
  that neither `stmtMoved` (`assumeMoveReuse`) nor `stmtReadsOk`
  (`assumeAfterMove`) on `Assume` can be dropped.
* `cmpDiscrSwitch`: `Rvalue::Discriminant` of a `core::cmp::Ordering`
  temporary (`_5 = discriminant(_4)` after `_4 = Cmp(_1, _2)`, then
  `StorageDead(_4)` and a `SwitchInt` on the `i8` tag), in the fragment
  (`cmpDiscrSwitch_inFragment`), translated through `orderingDiscrExpr`
  (`cmpDiscrSwitch_translate`), with Anneal runs for all three outcomes, the
  end-to-end MiniRust return through `mirCall_ret`
  (`cmpDiscrLess_minirust_ret_from_start`), and direct MiniRust runs.
* `paddedDeinitRead` and `paddedRetagRead`: the kernel-computed divergence of a
  projected `Deinit(_1.1)` (Anneal keeps the field readable and returns `99`,
  MiniRust writes `Uninit` and the later load is UB), and the kernel-computed
  Stage-1 agreement on a projected `Retag(_1.1)` of a `u32` field (Stage-1
  Trusted's retag of a typed non-pointer place is a no-op,
  `evalStmt_retag_scalar_noop`, and MiniRust's `Validate` stores back the
  integer it loaded: both return `99`, `paddedRetagRead_stage1_parity`);
  `statementOk` still rejects both (`statementOk_deinit_proj`,
  `statementOk_retag_proj`); both are handled by the separate fragment
  `inFragmentD` (`MiniRustSpec.Correspondence.DeinitWindow`), which rejects
  `paddedDeinitRead` (`paddedDeinitRead_not_inFragmentD`) and admits
  `paddedRetagRead` with an end-to-end correspondence
  (`paddedRetagRead_inFragmentD`, `paddedRetagRead_minirust_ret_from_start`),
  together with a projected `Retag` of a disjoint sibling inside an open
  `Deinit` hole (`paddedDeinitSiblingRetagReinit_minirust_ret_from_start`) and
  the negative control of a `Retag` overlapping the hole
  (`paddedDeinitRetagHole_not_inFragmentD`, `paddedDeinitRetagHole_diverges`).
* `deinitSiblingReinit`: witness #1 for projected `Deinit`
  (`StorageLive(_2); Deinit(_1.1); _2 = copy _1.0; _1.1 = const 42; _0 = copy _1.1;
  StorageDead(_2)` on `Padded(u8, u32, u16)`), admitted by `inFragmentD`
  (`deinitSiblingReinit_inFragmentD`) and rejected by `inFragment`, with the
  end-to-end MiniRust return of `42` through `mirCall_ret_D`
  (`deinitSiblingReinit_minirust_ret_from_start`), a direct MiniRust run showing the
  `Uninit` hole over bytes `4..8` and its re-initialization
  (`deinitSiblingReinit_minirust_direct`).
* `paddedDeinitSiblingReinit`: a projected-`Deinit` window with a sibling read
  through an integer cast and a `BinOp` re-initialization (`_2 = copy _1.0 as u32;
  _1.1 = _2 + 35`), admitted by `inFragmentD` through `castSiblingReadOk` and
  `reinitBinOpOk` (`paddedDeinitSiblingReinit_inFragmentD`), with the end-to-end
  MiniRust return of `42` through `mirCall_ret_D`
  (`paddedDeinitSiblingReinit_minirust_ret_from_start`); `paddedDeinitBinOpDivZero`
  transfers a division-by-zero `BinOp` re-initialization's UB through `mirCall_ub_D`;
  and the negative controls `paddedDeinitHoleBinOp` (a `BinOp` re-initialization
  reading the hole: Anneal returns `100`, MiniRust is UB) and
  `paddedDeinitHoleCastRead` (a cast read of the hole: Anneal returns `99`, MiniRust
  is UB) are rejected by the window check alone.
-/

namespace MiniRustSpec.Correspondence.Witness

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence

/-! ## MIR building blocks -/

def u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def u32Decl : LocalDecl := { mutability := .mut, ty := u32Ty, debugName := none }
def mkStmt (k : StatementKind) : MirAst.Statement := { kind := k, span := "witness" }
def mkTerm (k : TerminatorKind) : MirAst.Terminator := { kind := k, span := "witness" }
def local_ (i : Nat) : Place := { local_ := i, projection := [] }
def constU32 (n : Nat) : Operand := .constant { ty := u32Ty, val := .scalar (.int ⟨n, 4⟩) }

def u32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

@[simp] theorem arrayTypeOf_int (it : IntTy) (l : Nat) :
    arrayTypeOf { kind := .int it, layoutIdx := l } = none := rfl

@[simp] theorem arrayTypeOf_uint (ut : UintTy) (l : Nat) :
    arrayTypeOf { kind := .uint ut, layoutIdx := l } = none := rfl

@[simp] theorem tupleTypeOf_int (layouts : LayoutTable) (it : IntTy) (l : Nat) :
    tupleTypeOf layouts { kind := .int it, layoutIdx := l } = none := rfl

@[simp] theorem tupleTypeOf_uint (layouts : LayoutTable) (ut : UintTy) (l : Nat) :
    tupleTypeOf layouts { kind := .uint ut, layoutIdx := l } = none := rfl

@[simp] theorem tupleTypeOf_array (layouts : LayoutTable) (elem : RigidTy) (len l : Nat) :
    tupleTypeOf layouts { kind := .array elem len, layoutIdx := l } = none := rfl

theorem itOf_uint (m : MirAst.Mutability) (ut : UintTy) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    itOf { mutability := m, ty := { kind := .uint ut, layoutIdx := l }, debugName := n } layouts =
      itOf { mutability := m, ty := { kind := .uint ut, layoutIdx := l }, debugName := n } := rfl

theorem tyOf_uint (m : MirAst.Mutability) (ut : UintTy) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    tyOf { mutability := m, ty := { kind := .uint ut, layoutIdx := l }, debugName := n } layouts =
      tyOf { mutability := m, ty := { kind := .uint ut, layoutIdx := l }, debugName := n } := rfl

private theorem itOf_int (m : MirAst.Mutability) (it : IntTy) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    itOf { mutability := m, ty := { kind := .int it, layoutIdx := l }, debugName := n } layouts =
      itOf { mutability := m, ty := { kind := .int it, layoutIdx := l }, debugName := n } := rfl

private theorem tyOf_int (m : MirAst.Mutability) (it : IntTy) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    tyOf { mutability := m, ty := { kind := .int it, layoutIdx := l }, debugName := n } layouts =
      tyOf { mutability := m, ty := { kind := .int it, layoutIdx := l }, debugName := n } := rfl

private theorem itOf_bool (m : MirAst.Mutability) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    itOf { mutability := m, ty := { kind := .bool, layoutIdx := l }, debugName := n } layouts =
      itOf { mutability := m, ty := { kind := .bool, layoutIdx := l }, debugName := n } := rfl

private theorem tyOf_bool (m : MirAst.Mutability) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    tyOf { mutability := m, ty := { kind := .bool, layoutIdx := l }, debugName := n } layouts =
      tyOf { mutability := m, ty := { kind := .bool, layoutIdx := l }, debugName := n } := rfl

private theorem itOf_ordering (m : MirAst.Mutability) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    itOf { mutability := m, ty := { kind := .adt "core::cmp::Ordering" [], layoutIdx := l },
           debugName := n } layouts =
      itOf { mutability := m, ty := { kind := .adt "core::cmp::Ordering" [], layoutIdx := l },
             debugName := n } := rfl

private theorem tyOf_ordering (m : MirAst.Mutability) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    tyOf { mutability := m, ty := { kind := .adt "core::cmp::Ordering" [], layoutIdx := l },
           debugName := n } layouts =
      tyOf { mutability := m, ty := { kind := .adt "core::cmp::Ordering" [], layoutIdx := l },
             debugName := n } := rfl

private theorem itOf_u32BoolTuple (m : MirAst.Mutability) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    itOf { mutability := m, ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := l },
           debugName := n } layouts =
      itOf { mutability := m, ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := l },
             debugName := n } := rfl

private theorem tyOf_u32BoolTuple (m : MirAst.Mutability) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    tyOf { mutability := m, ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := l },
           debugName := n } layouts =
      tyOf { mutability := m, ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := l },
             debugName := n } := rfl

private theorem itOf_i8BoolTuple (m : MirAst.Mutability) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    itOf { mutability := m, ty := { kind := .tuple [.int .i8, .bool], layoutIdx := l },
           debugName := n } layouts =
      itOf { mutability := m, ty := { kind := .tuple [.int .i8, .bool], layoutIdx := l },
             debugName := n } := rfl

private theorem tyOf_i8BoolTuple (m : MirAst.Mutability) (l : Nat) (n : Option String)
    (layouts : LayoutTable) :
    tyOf { mutability := m, ty := { kind := .tuple [.int .i8, .bool], layoutIdx := l },
           debugName := n } layouts =
      tyOf { mutability := m, ty := { kind := .tuple [.int .i8, .bool], layoutIdx := l },
             debugName := n } := rfl

private theorem itOf_array_int (m : MirAst.Mutability) (it : IntTy) (len l : Nat)
    (n : Option String) (layouts : LayoutTable) :
    itOf { mutability := m, ty := { kind := .array (.int it) len, layoutIdx := l },
           debugName := n } layouts =
      itOf { mutability := m, ty := { kind := .array (.int it) len, layoutIdx := l },
             debugName := n } := rfl

private theorem tyOf_array_int (m : MirAst.Mutability) (it : IntTy) (len l : Nat)
    (n : Option String) (layouts : LayoutTable) :
    tyOf { mutability := m, ty := { kind := .array (.int it) len, layoutIdx := l },
           debugName := n } layouts =
      tyOf { mutability := m, ty := { kind := .array (.int it) len, layoutIdx := l },
             debugName := n } := rfl

private theorem itOf_array_uint (m : MirAst.Mutability) (ut : UintTy) (len l : Nat)
    (n : Option String) (layouts : LayoutTable) :
    itOf { mutability := m, ty := { kind := .array (.uint ut) len, layoutIdx := l },
           debugName := n } layouts =
      itOf { mutability := m, ty := { kind := .array (.uint ut) len, layoutIdx := l },
             debugName := n } := rfl

private theorem tyOf_array_uint (m : MirAst.Mutability) (ut : UintTy) (len l : Nat)
    (n : Option String) (layouts : LayoutTable) :
    tyOf { mutability := m, ty := { kind := .array (.uint ut) len, layoutIdx := l },
           debugName := n } layouts =
      tyOf { mutability := m, ty := { kind := .array (.uint ut) len, layoutIdx := l },
             debugName := n } := rfl

def fnAbi (nargs : Nat) : FnAbi :=
  { args := List.replicate nargs { layout := u32Layout, mode := .direct },
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-! ## `sum_to` -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn sum_to(mut n: u32) -> u32 {
    let mut acc = 0;            // bb0: _0 = const 0_u32; goto -> bb1
    while n != 0 {              // bb1: switchInt(copy _1) -> [0: bb3, otherwise: bb2]
        acc = acc.wrapping_add(n); // bb2: _0 = Add(copy _0, copy _1)
        n = n.wrapping_sub(1);     //      _1 = Sub(copy _1, const 1_u32); goto -> bb1
    }
    acc                         // bb3: return
}
```
(with `acc` living in the return place). -/
def sumTo : CapturedMir where
  defPath := "witness::sum_to"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 0)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 3)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 0)) (.copy (local_ 1)))),
        mkStmt (.assign (local_ 1) (.binaryOp .sub (.copy (local_ 1)) (constU32 1)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem sumTo_inFragment : inFragment sumTo = true := by decide

def u32 : Gen.IntType := ⟨.Unsigned, ⟨4⟩⟩

/-- The MiniRust function `minimize` produces for `sumTo`, spelled out. -/
def sumToFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 0) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[], .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 3)]⟩ (bbName 2),
      .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0))) (.Load (.Local (localName 1)))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 1))) (.Constant (.Int 1) (.Int u32)))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 3, ⟨[], .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem sumTo_translate : translateFn sumTo = some sumToFn := rfl

/-! ## The surrounding MiniRust machine -/

/-- The caller's return place: allocation `0`, at address `64`. -/
def retPtr : Ptr := { addr := 64, provenance := some (⟨0⟩, ()) }

def retAlloc : Gen.Allocation :=
  { data := List.replicate 4 .Uninit, addr := 64, align := ⟨4⟩, kind := .Stack, live := true,
    extra := () }

/-- A caller that holds its return place in its own `_0`. Execution after the
return (in the caller) is outside the correspondence, so its body is empty. -/
def callerFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true

def callerFrame : Frame :=
  { func := callerFn, locals := ⟨[(localName 0, retPtr)]⟩, stack_pop_action := .BottomOfStack,
    next_block := bbName 0, next_stmt := 0, extra := () }

/-- The callee's locals live at addresses `128` (`_0`) and `256` (`_1`). -/
def ctx0 : Ctx :=
  { caller := callerFrame, payloads := [], base := [retAlloc], addrs := [128, 256],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

def emptyProg : Gen.Program :=
  { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩, traits := ⟨[]⟩, vtables := ⟨[]⟩ }

/-- A MiniRust machine running `fn` under caller context `ctx` with Anneal
locals `locals` at the given callee program counter. -/
def machineWithCtx (ctx : Ctx) (body : CapturedMir) (fn : Gen.Function) (locals : List LocalSlot)
    (blk : Gen.BbName) : Mach :=
  { prog := emptyProg,
    mem := { memory := { allocations := ctx.base ++
                           localAllocs ctx (body.localDecls.take (body.argCount + 1)) locals
                             body.layouts,
                         _phantom := {} },
             accesses := [] },
    intptrcast := ⟨⟨[]⟩⟩,
    threads := [thread1 ctx [ctx.caller,
      { calleeFrame fn ctx (body.argCount + 1) 0 0 with next_block := blk }]],
    active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [], global_ptrs := ⟨[]⟩,
    fn_ptrs := ⟨[]⟩, vtable_ptrs := ⟨[]⟩, stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

def machine : CapturedMir → Gen.Function → List LocalSlot → Gen.BbName → Mach :=
  machineWithCtx ctx0

theorem ctx0_ok1 {body : CapturedMir} (h : body.localDecls = [u32Decl]) : CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | _ + 1, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

theorem ctx0_ok2 {body : CapturedMir} (h : body.localDecls = [u32Decl, u32Decl]) : CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 1, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

/-! ## `sum_to(3)` -/

def sumToS0 : MachineState := initMachineState sumTo [.scalar ⟨3, 4⟩]

/-- MiniRust at the start of MIR block `bb0`. -/
def sumToM0 : Mach := machine sumTo sumToFn sumToS0.frame.locals (bbName 0)

/-- MiniRust at the `minimize` init block (the function's `start`). -/
def sumToMInit : Mach := machine sumTo sumToFn sumToS0.frame.locals sumToFn.start

theorem sumTo_init_step : Interp.step sumToMInit = .ok sumToM0 := rfl

/-- `minimize`'s init block (here only `Goto(bb0)`) runs from the entry
relation into the relation at `bb0` (`step_start`). -/
theorem sumTo_rel : StateRel sumTo sumToFn ctx0 sumToS0 sumToM0 := by
  obtain ⟨m0, hm0, hrel⟩ := step_start sumTo_inFragment sumTo_translate
    (initMachineState_startRel sumTo_inFragment ctx0 (ctx0_ok2 rfl) [.scalar ⟨3, 4⟩] (by decide)
      sumToMInit rfl rfl rfl)
  have h : Interp.steps (initLen sumTo) sumToMInit = .ok sumToM0 := rfl
  rw [h] at hm0
  cases hm0
  exact hrel

/-- The branch observations of `sum_to(3)`: the scrutinee of each
`switchInt`. -/
def sumToTrace : List (Event MirEffect) :=
  [3, 2, 1, 0].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

/-- Anneal's semantics of `sum_to(3)` returns `6` (computed by the kernel). -/
theorem sumTo_anneal_ret :
    ReachesRet (mirTree sumTo sumToS0) sumToTrace (.normal (.scalar ⟨6, 4⟩, sumToS0.memory)) :=
  runA_sound sumTo 20 _ _ _ rfl

/-- Anneal's interaction tree for `sum_to(3)` is UB-free (`MirNoUBTree`). -/
theorem sumTo_noUB : MirNoUBTree (mirCallTree sumTo [.scalar ⟨3, 4⟩]) :=
  runA_noUB sumTo 20 _ _ _ rfl

/-- Therefore MiniRust, started from the related machine, performs a return
whose return place holds the little-endian bytes of `6u32`. -/
theorem sumTo_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n sumToM0 = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    run_ret sumTo_inFragment sumTo_translate ctx0 sumToS0 sumToM0 sumTo_rel sumTo_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [sumTo] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- The same return, computed directly by running the MiniRust interpretation
for 16 steps (one per Anneal step). -/
theorem sumTo_minirust_direct :
    (Interp.steps 16 sumToM0).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1]) := rfl

/-- Whole-execution return starting at `f.start` (including `minimize`'s
init block), directly via `mirCall_ret` without any phantom `bb0` machine. -/
theorem sumTo_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n sumToMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret sumTo_inFragment sumTo_translate ctx0 (ctx0_ok2 rfl) [.scalar ⟨3, 4⟩]
      (by decide) sumToMInit rfl rfl rfl sumTo_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [sumTo] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- Direct 17-step run from `f.start` (init block + 16 MIR steps). -/
theorem sumTo_minirust_direct_from_start :
    (Interp.steps 17 sumToMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1]) := rfl

/-! ## Returning an uninitialized `_0` -/

/-- MIR of a function whose only block returns without writing `_0`. -/
def retUninit : CapturedMir where
  defPath := "witness::ret_uninit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl]
  basicBlocks := [{ statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem retUninit_inFragment : inFragment retUninit = true := by decide

def retUninitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[(bbName 0, ⟨[], .Return, .Regular⟩), (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem retUninit_translate : translateFn retUninit = some retUninitFn := rfl

def retUninitS0 : MachineState := initMachineState retUninit []

def retUninitM0 : Mach := machine retUninit retUninitFn retUninitS0.frame.locals (bbName 0)

def retUninitMInit : Mach := machine retUninit retUninitFn retUninitS0.frame.locals retUninitFn.start

theorem retUninit_rel : StateRel retUninit retUninitFn ctx0 retUninitS0 retUninitM0 := by
  obtain ⟨m0, hm0, hrel⟩ := step_start retUninit_inFragment retUninit_translate
    (initMachineState_startRel retUninit_inFragment ctx0 (ctx0_ok1 rfl) [] (by decide)
      retUninitMInit rfl rfl rfl)
  have h : Interp.steps (initLen retUninit) retUninitMInit = .ok retUninitM0 := rfl
  rw [h] at hm0
  cases hm0
  exact hrel

/-- Anneal's semantics of `ret_uninit()` faults (computed by the kernel). -/
theorem retUninit_anneal_ub : ∃ tr u, Reaches (mirTree retUninit retUninitS0) tr u ∧ FaultNow u :=
  faultsA_sound retUninit 1 _ (by decide)

/-- Therefore MiniRust raises UB. -/
theorem retUninit_minirust_ub : ∃ (n : Nat) (msg : String), Interp.steps n retUninitM0 = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := retUninit_anneal_ub
  exact run_ub retUninit_inFragment retUninit_translate ctx0 retUninitS0 retUninitM0 retUninit_rel hr hf

/-- Direct computation: MiniRust's first step is UB. -/
theorem retUninit_minirust_direct :
    ∃ msg, Interp.step retUninitM0 = .error (.ub msg) :=
  ⟨_, rfl⟩

/-- Whole-execution UB starting at `f.start` (including `minimize`'s init
block), directly via `mirCall_ub`. -/
theorem retUninit_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n retUninitMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := retUninit_anneal_ub
  exact mirCall_ub retUninit_inFragment retUninit_translate ctx0 (ctx0_ok1 rfl) []
    (by decide) retUninitMInit rfl rfl rfl hr hf

/-! ## `PlaceMention`, `UnaryOp(Neg)`, and `Unreachable` -/

/-- MIR of a function exercising `PlaceMention(_0)` (while `_0` is still
uninitialized), wrapping integer negation `_0 = Neg(copy _1)`, and an
`Unreachable` terminator on the `_1 == 0` branch. -/
def negMention : CapturedMir where
  defPath := "witness::neg_mention"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.placeMention (local_ 0)),
        mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1))))],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false },
    { statements := [], terminator := mkTerm .unreachable, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem negMention_inFragment : inFragment negMention = true := by decide

def negMentionFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .PlaceMention (.Local (localName 0)),
      .Assign (.Local (localName 0)) (.UnOp (.Int .Neg) (.Load (.Local (localName 1))))],
      .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[], .Return, .Regular⟩),
    (bbName 2, ⟨[], .Unreachable, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem negMention_translate : translateFn negMention = some negMentionFn := rfl

def negMention5S0 : MachineState := initMachineState negMention [.scalar ⟨5, 4⟩]
def negMention5MInit : Mach := machine negMention negMentionFn negMention5S0.frame.locals negMentionFn.start

theorem negMention5_startRel :
    StartRel negMention negMentionFn ctx0 negMention5S0 negMention5MInit :=
  initMachineState_startRel negMention_inFragment ctx0 (ctx0_ok2 rfl) [.scalar ⟨5, 4⟩]
    (by decide) negMention5MInit rfl rfl rfl

def negMention5Trace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 5))), PUnit.unit⟩]

theorem negMention5_anneal_ret :
    ReachesRet (mirTree negMention negMention5S0) negMention5Trace
      (.normal (.scalar ⟨4294967291, 4⟩, negMention5S0.memory)) :=
  runA_sound negMention 10 _ _ _ rfl

theorem negMention5_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n negMention5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 4294967291 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    run_ret_from_start negMention_inFragment negMention_translate ctx0 negMention5S0
      negMention5MInit negMention5_startRel negMention5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [negMention] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem negMention5_minirust_direct :
    (Interp.steps 5 negMention5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 4294967291 }, [1]) := rfl

def negMention0S0 : MachineState := initMachineState negMention [.scalar ⟨0, 4⟩]
def negMention0MInit : Mach := machine negMention negMentionFn negMention0S0.frame.locals negMentionFn.start

theorem negMention0_startRel :
    StartRel negMention negMentionFn ctx0 negMention0S0 negMention0MInit :=
  initMachineState_startRel negMention_inFragment ctx0 (ctx0_ok2 rfl) [.scalar ⟨0, 4⟩]
    (by decide) negMention0MInit rfl rfl rfl

theorem negMention0_anneal_ub :
    ∃ tr u, Reaches (mirTree negMention negMention0S0) tr u ∧ FaultNow u :=
  faultsA_sound negMention 10 _ (by decide)

theorem negMention0_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n negMention0MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := negMention0_anneal_ub
  exact run_ub_from_start negMention_inFragment negMention_translate ctx0 negMention0S0
    negMention0MInit negMention0_startRel hr hf

theorem negMention0_minirust_direct :
    ∃ msg, Interp.steps 5 negMention0MInit = .error (.ub msg) :=
  ⟨_, rfl⟩

/-! ## Signed two's-complement corner cases (`i8::MIN`, negative `switchInt`, `MirNoUBTree`) -/

def i8Ty : Ty := { kind := .int .i8, layoutIdx := 0 }
def i8Decl : LocalDecl := { mutability := .mut, ty := i8Ty, debugName := none }
def i8 : Gen.IntType := ⟨.Signed, ⟨1⟩⟩
def constI8 (bits : Nat) : Operand := .constant { ty := i8Ty, val := .scalar (.int ⟨bits, 1⟩) }

def i8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiI8 (nargs : Nat) : FnAbi :=
  { args := List.replicate nargs { layout := i8Layout, mode := .direct },
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

def retAllocI8 : Gen.Allocation :=
  { data := [.Uninit], addr := 64, align := ⟨1⟩, kind := .Stack, live := true, extra := () }

def callerFnI8 : Gen.Function where
  locals := ⟨[(localName 0, .Int i8)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true

def callerFrameI8 : Frame :=
  { func := callerFnI8, locals := ⟨[(localName 0, retPtr)]⟩, stack_pop_action := .BottomOfStack,
    next_block := bbName 0, next_stmt := 0, extra := () }

def ctxI8 : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8], addrs := [128, 256],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxI8_ok2 {body : CapturedMir} (h : body.localDecls = [i8Decl, i8Decl]) :
    CtxOk body ctxI8 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn signed_edge(x: i8) -> i8 {
    let y = x.wrapping_neg(); // bb0: _0 = Neg(copy _1); switchInt(copy _0) -> [-128i8: bb1, -1i8: bb2, _: bb3]
    match y {
        -128 => y.wrapping_add(-1), // bb1: _0 = Add(copy _0, const -1i8); return  (-> 127i8)
        -1   => y.wrapping_mul(-2), // bb2: _0 = Mul(copy _0, const -2i8); return  (-> 2i8)
        _    => y,                  // bb3: return
    }
}
```
where `-128i8` has bit pattern `128`, `-1i8` has bit pattern `255`, and `-2i8`
has bit pattern `254`. -/
def signedEdge : CapturedMir where
  defPath := "witness::signed_edge"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1))))],
      terminator := mkTerm (.switchInt (.copy (local_ 0))
        { branches := [(128, 1), (255, 2)], otherwise := 3 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 0)) (constI8 255)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .mul (.copy (local_ 0)) (constI8 254)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem signedEdge_inFragment : inFragment signedEdge = true := by decide

def signedEdgeFn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0)) (.UnOp (.Int .Neg) (.Load (.Local (localName 1))))],
      .Switch (.Load (.Local (localName 0))) ⟨[(-128, bbName 1), (-1, bbName 2)]⟩ (bbName 3),
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0))) (.Constant (.Int (-1)) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Mul) (.Load (.Local (localName 0))) (.Constant (.Int (-2)) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem signedEdge_translate : translateFn signedEdge = some signedEdgeFn := rfl

/-- Input `x = -128i8` (`i8::MIN`, bits `128`): `-(-128i8)` overflows signed
`i8` and wraps back to `-128i8`, takes the `-128` `switchInt` arm, and
`-128i8 + (-1i8)` underflows signed `i8` and wraps to `127i8` (`i8::MAX`). -/
def signedEdgeMinS0 : MachineState := initMachineState signedEdge [.scalar ⟨128, 1⟩]
def signedEdgeMinMInit : Mach :=
  machineWithCtx ctxI8 signedEdge signedEdgeFn signedEdgeMinS0.frame.locals signedEdgeFn.start

def signedEdgeMinTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 128))), PUnit.unit⟩]

theorem signedEdgeMin_anneal_ret :
    ReachesRet (mirCallTree signedEdge [.scalar ⟨128, 1⟩]) signedEdgeMinTrace
      (.normal (.scalar ⟨127, 1⟩, signedEdgeMinS0.memory)) :=
  runA_sound signedEdge 10 _ _ _ rfl

theorem signedEdgeMin_noUB : MirNoUBTree (mirCallTree signedEdge [.scalar ⟨128, 1⟩]) :=
  runA_noUB signedEdge 10 _ _ _ rfl

theorem signedEdgeMin_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n signedEdgeMinMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 127 } ∧
      m'.threads = [thread1 ctxI8 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret signedEdge_inFragment signedEdge_translate ctxI8 (ctxI8_ok2 rfl)
      [.scalar ⟨128, 1⟩] (by decide) signedEdgeMinMInit rfl rfl rfl signedEdgeMin_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [signedEdge] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- End-to-end `MirNoUBTree` safety transfer: any error within `n` MiniRust
steps from `f.start` occurs strictly after `k < n` steps at which MiniRust has
already completed the callee's return (`ReturnRel`). -/
theorem signedEdgeMin_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n signedEdgeMinMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k signedEdgeMinMInit = .ok mRet ∧
      ReturnRel signedEdge ctxI8 s' v mRet ∧
      ReachesRet (mirCallTree signedEdge [.scalar ⟨128, 1⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB signedEdge_inFragment signedEdge_translate ctxI8 (ctxI8_ok2 rfl)
    [.scalar ⟨128, 1⟩] (by decide) signedEdgeMinMInit rfl rfl rfl signedEdgeMin_noUB herr

theorem signedEdgeMin_minirust_direct :
    (Interp.steps 5 signedEdgeMinMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 127 }, [1]) := rfl

/-- Input `x = 1i8` (bits `1`): `-(1i8) = -1i8` (bits `255`), takes the `-1`
`switchInt` arm, and `(-1i8) * (-2i8) = 2i8` (bits `2`). -/
def signedEdgeOneS0 : MachineState := initMachineState signedEdge [.scalar ⟨1, 1⟩]
def signedEdgeOneMInit : Mach :=
  machineWithCtx ctxI8 signedEdge signedEdgeFn signedEdgeOneS0.frame.locals signedEdgeFn.start

def signedEdgeOneTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 255))), PUnit.unit⟩]

theorem signedEdgeOne_anneal_ret :
    ReachesRet (mirCallTree signedEdge [.scalar ⟨1, 1⟩]) signedEdgeOneTrace
      (.normal (.scalar ⟨2, 1⟩, signedEdgeOneS0.memory)) :=
  runA_sound signedEdge 10 _ _ _ rfl

theorem signedEdgeOne_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n signedEdgeOneMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 2 } ∧
      m'.threads = [thread1 ctxI8 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret signedEdge_inFragment signedEdge_translate ctxI8 (ctxI8_ok2 rfl)
      [.scalar ⟨1, 1⟩] (by decide) signedEdgeOneMInit rfl rfl rfl signedEdgeOne_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [signedEdge] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem signedEdgeOne_minirust_direct :
    (Interp.steps 5 signedEdgeOneMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 2 }, [1]) := rfl

/-! ## Cross-width `Cast(IntToInt)` (sign-extension & truncation) and `UnaryOp(Not)` (`BitNot`) -/

def fnAbiI8ToU32 : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctx0_ok_u32_i8 {body : CapturedMir} (h : body.localDecls = [u32Decl, i8Decl]) :
    CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 1, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn cast_bitnot(mut x: i8) -> u32 {
    x = !x;                  // bb0: _1 = Not(copy _1)
    let w = x as u32;        //      _0 = Cast(IntToInt, copy _1, u32)
    match x {                //      switchInt(copy _1) -> [-5i8: bb1, otherwise: bb2]
        -5 => {
            let _t = w as i8; // bb1: _1 = Cast(IntToInt, copy _0, i8)
            !w                //      _0 = Not(copy _0); return
        }
        _ => unreachable!(), // bb2: unreachable
    }
}
```
For `x = 4i8` (bits `4`), `!4i8 = -5i8` (bits `251`), sign-extending `-5i8 as u32`
yields `4294967291u32` (`0xFFFFFFFB`), narrowing `4294967291u32 as i8` truncates
back to `-5i8` (bits `251`), and `!4294967291u32 = 4u32`. -/
def castBitNot : CapturedMir where
  defPath := "witness::cast_bitnot"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.unaryOp .not (.copy (local_ 1)))),
        mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 1)) u32Ty))],
      terminator := mkTerm (.switchInt (.copy (local_ 1))
        { branches := [(251, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.cast .intToInt (.copy (local_ 0)) i8Ty)),
        mkStmt (.assign (local_ 0) (.unaryOp .not (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [], terminator := mkTerm .unreachable, isCleanup := false }]
  fnAbi := fnAbiI8ToU32
  layouts := emptyLayoutTable
  allocations := []

theorem castBitNot_inFragment : inFragment castBitNot = true := by decide

def castBitNotFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int i8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1)) (.UnOp (.Int .BitNot) (.Load (.Local (localName 1)))),
      .Assign (.Local (localName 0)) (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 1))))],
      .Switch (.Load (.Local (localName 1))) ⟨[(-5, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 1)) (.UnOp (.Cast (.IntToInt i8)) (.Load (.Local (localName 0)))),
      .Assign (.Local (localName 0)) (.UnOp (.Int .BitNot) (.Load (.Local (localName 0))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Unreachable, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem castBitNot_translate : translateFn castBitNot = some castBitNotFn := rfl

def castBitNot4S0 : MachineState := initMachineState castBitNot [.scalar ⟨4, 1⟩]
def castBitNot4MInit : Mach :=
  machine castBitNot castBitNotFn castBitNot4S0.frame.locals castBitNotFn.start

def castBitNot4Trace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 251))), PUnit.unit⟩]

theorem castBitNot4_anneal_ret :
    ReachesRet (mirCallTree castBitNot [.scalar ⟨4, 1⟩]) castBitNot4Trace
      (.normal (.scalar ⟨4, 4⟩, castBitNot4S0.memory)) :=
  runA_sound castBitNot 10 _ _ _ rfl

theorem castBitNot4_noUB : MirNoUBTree (mirCallTree castBitNot [.scalar ⟨4, 1⟩]) :=
  runA_noUB castBitNot 10 _ _ _ rfl

theorem castBitNot4_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n castBitNot4MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 4 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret castBitNot_inFragment castBitNot_translate ctx0 (ctx0_ok_u32_i8 rfl)
      [.scalar ⟨4, 1⟩] (by decide) castBitNot4MInit rfl rfl rfl castBitNot4_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [castBitNot] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem castBitNot4_minirust_direct :
    (Interp.steps 7 castBitNot4MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 4 }, [1]) := rfl

/-! ## Diverging UB-free loop (`spinLoop`) -/

/-- MIR of a diverging loop `fn spin_loop() -> u32 { loop {} }`. -/
def spinLoop : CapturedMir where
  defPath := "witness::spin_loop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl]
  basicBlocks := [{ statements := [], terminator := mkTerm (.goto 0), isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem spinLoop_inFragment : inFragment spinLoop = true := by decide

def spinLoopFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[(bbName 0, ⟨[], .Goto (bbName 0), .Regular⟩),
              (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem spinLoop_translate : translateFn spinLoop = some spinLoopFn := rfl

def spinLoopS0 : MachineState := initMachineState spinLoop []
def spinLoopMInit : Mach := machine spinLoop spinLoopFn spinLoopS0.frame.locals spinLoopFn.start

theorem spinLoop_step_self :
    ∀ s, s = spinLoopS0 → ∃ s', stepMirFn spinLoop s = .tau (.running s') ∧ s' = spinLoopS0 := by
  rintro s rfl
  exact ⟨spinLoopS0, rfl, rfl⟩

/-- `spinLoop` is UB-free across its infinite interaction tree. -/
theorem spinLoop_noUB : MirNoUBTree (mirCallTree spinLoop []) :=
  treeSafe_of_tau_inv spinLoop_step_self rfl

/-- `spinLoop` never reaches a return outcome. -/
theorem spinLoop_diverges (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet (mirCallTree spinLoop []) tr o :=
  noRet_of_tau_inv spinLoop_step_self rfl tr o

/-- Therefore MiniRust started at `f.start` succeeds for every step count `n : Nat`. -/
theorem spinLoop_minirust_steps_ok (n : Nat) :
    ∃ m', Interp.steps n spinLoopMInit = .ok m' :=
  mirCall_diverges_steps_ok spinLoop_inFragment spinLoop_translate ctx0 (ctx0_ok1 rfl) []
    (by decide) spinLoopMInit rfl rfl rfl spinLoop_noUB spinLoop_diverges n

/-- Stronger lockstep divergence witness via `mirCall_diverges_rel`: for every
`n : Nat`, `initLen spinLoop + n` MiniRust steps from `f.start` stay in `StateRel` with an
Anneal state reachable via `Reaches (mirCallTree spinLoop [])`. -/
theorem spinLoop_minirust_diverges_rel (n : Nat) :
    ∃ s' m' tr, Interp.steps (initLen spinLoop + n) spinLoopMInit = .ok m' ∧
      StateRel spinLoop spinLoopFn ctx0 s' m' ∧
      Reaches (mirCallTree spinLoop []) tr (mirTree spinLoop s') :=
  mirCall_diverges_rel spinLoop_inFragment spinLoop_translate ctx0 (ctx0_ok1 rfl) []
    (by decide) spinLoopMInit rfl rfl rfl spinLoop_noUB spinLoop_diverges n

/-! ## Signed `Div` and `Rem` (truncation toward zero and all 4 UB conditions) -/

def ctxI8_3 : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8], addrs := [128, 256, 384],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxI8_ok3 {body : CapturedMir} (h : body.localDecls = [i8Decl, i8Decl, i8Decl]) :
    CtxOk body ctxI8_3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 2, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn div_rem_i8(mut a: i8, b: i8) -> i8 {
    let q = a / b;   // bb0: _0 = Div(copy _1, copy _2)
    a = a % b;       //      _1 = Rem(copy _1, copy _2)
    match q {        //      switchInt(copy _0) -> [-2i8: bb1, otherwise: bb2]
        -2 => a,     // bb1: _0 = Use(copy _1); return
        _  => q,     // bb2: return
    }
}
```
where `-2i8` has bit pattern `254`. -/
def divRemI8 : CapturedMir where
  defPath := "witness::div_rem_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .div (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 1) (.binaryOp .rem (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm (.switchInt (.copy (local_ 0))
        { branches := [(254, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem divRemI8_inFragment : inFragment divRemI8 = true := by decide

def divRemI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Div) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Rem) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Switch (.Load (.Local (localName 0))) ⟨[(-2, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem divRemI8_translate : translateFn divRemI8 = some divRemI8Fn := rfl

/-- Input `(-7i8, 3i8)` (bits `249`, `3`): truncating division gives `-7 / 3 = -2`
(bits `254`, taking `bb1`), and truncating remainder gives `-7 % 3 = -1`
(bits `255`), returned in `_0`. -/
def divRemNeg7S0 : MachineState := initMachineState divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨3, 1⟩]
def divRemNeg7MInit : Mach :=
  machineWithCtx ctxI8_3 divRemI8 divRemI8Fn divRemNeg7S0.frame.locals divRemI8Fn.start

def divRemNeg7Trace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 254))), PUnit.unit⟩]

theorem divRemNeg7_anneal_ret :
    ReachesRet (mirCallTree divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨3, 1⟩]) divRemNeg7Trace
      (.normal (.scalar ⟨255, 1⟩, divRemNeg7S0.memory)) :=
  runA_sound divRemI8 10 _ _ _ rfl

theorem divRemNeg7_noUB : MirNoUBTree (mirCallTree divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨3, 1⟩]) :=
  runA_noUB divRemI8 10 _ _ _ rfl

theorem divRemNeg7_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n divRemNeg7MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 255 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret divRemI8_inFragment divRemI8_translate ctxI8_3 (ctxI8_ok3 rfl)
      [.scalar ⟨249, 1⟩, .scalar ⟨3, 1⟩] (by decide) divRemNeg7MInit rfl rfl rfl divRemNeg7_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [divRemI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem divRemNeg7_minirust_direct :
    (Interp.steps 6 divRemNeg7MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 255 }, [1]) := rfl

/-- Non-UB signed boundary `(-128i8, 1i8)` (`i8::MIN / 1 = -128i8`, bits `128`). -/
def divRemMinOneS0 : MachineState := initMachineState divRemI8 [.scalar ⟨128, 1⟩, .scalar ⟨1, 1⟩]
def divRemMinOneMInit : Mach :=
  machineWithCtx ctxI8_3 divRemI8 divRemI8Fn divRemMinOneS0.frame.locals divRemI8Fn.start

def divRemMinOneTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 128))), PUnit.unit⟩]

theorem divRemMinOne_anneal_ret :
    ReachesRet (mirCallTree divRemI8 [.scalar ⟨128, 1⟩, .scalar ⟨1, 1⟩]) divRemMinOneTrace
      (.normal (.scalar ⟨128, 1⟩, divRemMinOneS0.memory)) :=
  runA_sound divRemI8 10 _ _ _ rfl

theorem divRemMinOne_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n divRemMinOneMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 128 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret divRemI8_inFragment divRemI8_translate ctxI8_3 (ctxI8_ok3 rfl)
      [.scalar ⟨128, 1⟩, .scalar ⟨1, 1⟩] (by decide) divRemMinOneMInit rfl rfl rfl divRemMinOne_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [divRemI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem divRemMinOne_minirust_direct :
    (Interp.steps 5 divRemMinOneMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 128 }, [1]) := rfl

/-- Division-by-zero UB (`-7i8 / 0i8`) via `mirCall_ub`, `mirCall_steps_error`,
and direct check of MiniRust's `"division by zero"` message. -/
def divByZeroS0 : MachineState := initMachineState divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]
def divByZeroMInit : Mach :=
  machineWithCtx ctxI8_3 divRemI8 divRemI8Fn divByZeroS0.frame.locals divRemI8Fn.start

theorem divByZero_anneal_ub :
    ∃ tr u, Reaches (mirCallTree divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound divRemI8 5 _ (by decide)

theorem divByZero_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n divByZeroMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := divByZero_anneal_ub
  exact mirCall_ub divRemI8_inFragment divRemI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩] (by decide) divByZeroMInit rfl rfl rfl hr hf

theorem divByZero_minirust_direct :
    Interp.steps 2 divByZeroMInit = .error (.ub "division by zero") := rfl

/-- Converse `mirCall_steps_error` witness: MiniRust's 2-step error on
`divByZeroMInit` implies Anneal `mirCallTree` reaches `FaultNow` (or already
returned, which is ruled out on `divByZero`). -/
theorem divByZero_converse_error :
    (∃ msg, Stop.ub "division by zero" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 2 ∧ Interp.steps k divByZeroMInit = .ok mRet ∧
      ReturnRel divRemI8 ctxI8_3 s' v mRet ∧
      ReachesRet (mirCallTree divRemI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error divRemI8_inFragment divRemI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩] (by decide) divByZeroMInit rfl rfl rfl
    divByZero_minirust_direct

/-- Signed division overflow UB (`i8::MIN / -1`, bits `128` and `255`). -/
def divMinNeg1S0 : MachineState := initMachineState divRemI8 [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩]
def divMinNeg1MInit : Mach :=
  machineWithCtx ctxI8_3 divRemI8 divRemI8Fn divMinNeg1S0.frame.locals divRemI8Fn.start

theorem divMinNeg1_anneal_ub :
    ∃ tr u, Reaches (mirCallTree divRemI8 [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound divRemI8 5 _ (by decide)

theorem divMinNeg1_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n divMinNeg1MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := divMinNeg1_anneal_ub
  exact mirCall_ub divRemI8_inFragment divRemI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩] (by decide) divMinNeg1MInit rfl rfl rfl hr hf

theorem divMinNeg1_minirust_direct :
    Interp.steps 2 divMinNeg1MInit = .error (.ub "overflow in division") := rfl

/-- Standalone `Rem` body (`_0 = Rem(copy _1, copy _2); return`) so `Rem`'s own
zero-divisor and `i8::MIN % -1` UB branches execute without `Div` faulting first. -/
def remOnlyI8 : CapturedMir where
  defPath := "witness::rem_only_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .rem (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem remOnlyI8_inFragment : inFragment remOnlyI8 = true := by decide

def remOnlyI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Rem) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem remOnlyI8_translate : translateFn remOnlyI8 = some remOnlyI8Fn := rfl

def remByZeroS0 : MachineState := initMachineState remOnlyI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]
def remByZeroMInit : Mach :=
  machineWithCtx ctxI8_3 remOnlyI8 remOnlyI8Fn remByZeroS0.frame.locals remOnlyI8Fn.start

theorem remByZero_anneal_ub :
    ∃ tr u, Reaches (mirCallTree remOnlyI8 [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound remOnlyI8 5 _ (by decide)

theorem remByZero_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n remByZeroMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := remByZero_anneal_ub
  exact mirCall_ub remOnlyI8_inFragment remOnlyI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨249, 1⟩, .scalar ⟨0, 1⟩] (by decide) remByZeroMInit rfl rfl rfl hr hf

theorem remByZero_minirust_direct :
    Interp.steps 2 remByZeroMInit = .error (.ub "modulus of remainder is zero") := rfl

def remMinNeg1S0 : MachineState := initMachineState remOnlyI8 [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩]
def remMinNeg1MInit : Mach :=
  machineWithCtx ctxI8_3 remOnlyI8 remOnlyI8Fn remMinNeg1S0.frame.locals remOnlyI8Fn.start

theorem remMinNeg1_anneal_ub :
    ∃ tr u, Reaches (mirCallTree remOnlyI8 [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound remOnlyI8 5 _ (by decide)

theorem remMinNeg1_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n remMinNeg1MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := remMinNeg1_anneal_ub
  exact mirCall_ub remOnlyI8_inFragment remOnlyI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩] (by decide) remMinNeg1MInit rfl rfl rfl hr hf

theorem remMinNeg1_minirust_direct :
    Interp.steps 2 remMinNeg1MInit = .error (.ub "overflow in remainder") := rfl

/-! ## Unchecked arithmetic (`MulUnchecked`, `SubUnchecked`, `AddUnchecked`) -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
unsafe fn unchecked_arith_i8(a: i8, b: i8) -> i8 {
    let p = a.unchecked_mul(b);   // bb0: _0 = MulUnchecked(copy _1, copy _2)
    let d = p.unchecked_sub(b);   //      _0 = SubUnchecked(copy _0, copy _2)
    d.unchecked_add(127)          //      _0 = AddUnchecked(copy _0, const 127i8); return
}
```
Exercises all three unchecked operators both succeeding at the `i8::MIN`
boundary and faulting with UB on signed overflow. -/
def uncheckedArithI8 : CapturedMir where
  defPath := "witness::unchecked_arith_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .mulUnchecked (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.binaryOp .subUnchecked (.copy (local_ 0)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.binaryOp .addUnchecked (.copy (local_ 0)) (constI8 127)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem uncheckedArithI8_inFragment : inFragment uncheckedArithI8 = true := by decide

def uncheckedArithI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .MulUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .SubUnchecked) (.Load (.Local (localName 0))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .AddUnchecked) (.Load (.Local (localName 0))) (.Constant (.Int 127) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uncheckedArithI8_translate : translateFn uncheckedArithI8 = some uncheckedArithI8Fn := rfl

/-- Boundary success `(64i8, -2i8)` (bits `64`, `254`):
`64 * -2 = -128` (`i8::MIN`), `-128 - (-2) = -126`, `-126 + 127 = 1`. -/
def uncheckedOkS0 : MachineState := initMachineState uncheckedArithI8 [.scalar ⟨64, 1⟩, .scalar ⟨254, 1⟩]
def uncheckedOkMInit : Mach :=
  machineWithCtx ctxI8_3 uncheckedArithI8 uncheckedArithI8Fn uncheckedOkS0.frame.locals uncheckedArithI8Fn.start

theorem uncheckedOk_anneal_ret :
    ReachesRet (mirCallTree uncheckedArithI8 [.scalar ⟨64, 1⟩, .scalar ⟨254, 1⟩]) []
      (.normal (.scalar ⟨1, 1⟩, uncheckedOkS0.memory)) :=
  runA_sound uncheckedArithI8 10 _ _ _ rfl

theorem uncheckedOk_noUB :
    MirNoUBTree (mirCallTree uncheckedArithI8 [.scalar ⟨64, 1⟩, .scalar ⟨254, 1⟩]) :=
  runA_noUB uncheckedArithI8 10 _ _ _ rfl

theorem uncheckedOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n uncheckedOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 1 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret uncheckedArithI8_inFragment uncheckedArithI8_translate ctxI8_3 (ctxI8_ok3 rfl)
      [.scalar ⟨64, 1⟩, .scalar ⟨254, 1⟩] (by decide) uncheckedOkMInit rfl rfl rfl uncheckedOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [uncheckedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem uncheckedOk_minirust_direct :
    (Interp.steps 5 uncheckedOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 1 }, [1]) := rfl

/-- `MulUnchecked` overflow `(-64i8, -2i8)` (`+128` overflows `i8`). -/
def uncheckedMulUbS0 : MachineState := initMachineState uncheckedArithI8 [.scalar ⟨192, 1⟩, .scalar ⟨254, 1⟩]
def uncheckedMulUbMInit : Mach :=
  machineWithCtx ctxI8_3 uncheckedArithI8 uncheckedArithI8Fn uncheckedMulUbS0.frame.locals uncheckedArithI8Fn.start

theorem uncheckedMulUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨192, 1⟩, .scalar ⟨254, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uncheckedArithI8 5 _ (by decide)

theorem uncheckedMulUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uncheckedMulUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uncheckedMulUb_anneal_ub
  exact mirCall_ub uncheckedArithI8_inFragment uncheckedArithI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨192, 1⟩, .scalar ⟨254, 1⟩] (by decide) uncheckedMulUbMInit rfl rfl rfl hr hf

theorem uncheckedMulUb_minirust_direct :
    Interp.steps 2 uncheckedMulUbMInit = .error (.ub "overflow in unchecked mul") := rfl

/-- `SubUnchecked` overflow `(-64i8, 2i8)` (`-64 * 2 = -128` succeeds, then
`-128 - 2 = -130` overflows `i8`). -/
def uncheckedSubUbS0 : MachineState := initMachineState uncheckedArithI8 [.scalar ⟨192, 1⟩, .scalar ⟨2, 1⟩]
def uncheckedSubUbMInit : Mach :=
  machineWithCtx ctxI8_3 uncheckedArithI8 uncheckedArithI8Fn uncheckedSubUbS0.frame.locals uncheckedArithI8Fn.start

theorem uncheckedSubUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨192, 1⟩, .scalar ⟨2, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uncheckedArithI8 5 _ (by decide)

theorem uncheckedSubUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uncheckedSubUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uncheckedSubUb_anneal_ub
  exact mirCall_ub uncheckedArithI8_inFragment uncheckedArithI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨192, 1⟩, .scalar ⟨2, 1⟩] (by decide) uncheckedSubUbMInit rfl rfl rfl hr hf

theorem uncheckedSubUb_minirust_direct :
    Interp.steps 3 uncheckedSubUbMInit = .error (.ub "overflow in unchecked sub") := rfl

/-- `AddUnchecked` overflow `(10i8, 2i8)` (`10 * 2 = 20`, `20 - 2 = 18`, then
`18 + 127 = 145` overflows `i8`), plus a witness of `mirCall_outcome`. -/
def uncheckedAddUbS0 : MachineState := initMachineState uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]
def uncheckedAddUbMInit : Mach :=
  machineWithCtx ctxI8_3 uncheckedArithI8 uncheckedArithI8Fn uncheckedAddUbS0.frame.locals uncheckedArithI8Fn.start

theorem uncheckedAddUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uncheckedArithI8 5 _ (by decide)

theorem uncheckedAddUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uncheckedAddUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uncheckedAddUb_anneal_ub
  exact mirCall_ub uncheckedArithI8_inFragment uncheckedArithI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩] (by decide) uncheckedAddUbMInit rfl rfl rfl hr hf

theorem uncheckedAddUb_minirust_direct :
    Interp.steps 4 uncheckedAddUbMInit = .error (.ub "overflow in unchecked add") := rfl

theorem uncheckedAddUb_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen uncheckedArithI8 + n) uncheckedAddUbMInit = .ok m' ∧
      StateRel uncheckedArithI8 uncheckedArithI8Fn ctxI8_3 s' m' ∧
      Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]) tr
        (mirTree uncheckedArithI8 s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen uncheckedArithI8 + n ∧
      Interp.steps k uncheckedAddUbMInit = .ok mRet ∧
      ReturnRel uncheckedArithI8 ctxI8_3 s' v mRet ∧
      ReachesRet (mirCallTree uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen uncheckedArithI8 + n) uncheckedAddUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree uncheckedArithI8 [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome uncheckedArithI8_inFragment uncheckedArithI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨10, 1⟩, .scalar ⟨2, 1⟩] (by decide) uncheckedAddUbMInit rfl rfl rfl n

/-! ## Observable-step diverging loop (`branchSpinLoop`) -/

/-- MIR (`Runtime(PostCleanup)`) of a conditional loop
```rust
fn branch_spin_loop(x: u32) -> u32 {
    while x != 0 {}
    x
}
```
Unlike `spinLoop`, every iteration executes a `switchInt` terminator and
emits a visible `.emit` branch event in Anneal's interaction tree, exercising
`treeSafe_of_step_inv` and `noRet_of_step_inv`. -/
def branchSpinLoop : CapturedMir where
  defPath := "witness::branch_spin_loop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1))
        { branches := [(0, 1)], otherwise := 0 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem branchSpinLoop_inFragment : inFragment branchSpinLoop = true := by decide

def branchSpinLoopFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 1)]⟩ (bbName 0), .Regular⟩),
    (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 2
  implicit_writes := true

theorem branchSpinLoop_translate : translateFn branchSpinLoop = some branchSpinLoopFn := rfl

def branchSpinLoop1S0 : MachineState := initMachineState branchSpinLoop [.scalar ⟨1, 4⟩]
def branchSpinLoop1MInit : Mach :=
  machine branchSpinLoop branchSpinLoopFn branchSpinLoop1S0.frame.locals branchSpinLoopFn.start

theorem branchSpinLoop1_step_self :
    ∀ s, s = branchSpinLoop1S0 → SafeContinue branchSpinLoop (· = branchSpinLoop1S0) s := by
  rintro s rfl
  exact Or.inr ⟨.event 1, _, branchSpinLoop1S0, rfl, rfl, rfl⟩

/-- `branchSpinLoop(1)` is UB-free across its infinite interaction tree, even
though every iteration emits a visible `.emit (.event 1)` branch observation. -/
theorem branchSpinLoop1_noUB : MirNoUBTree (mirCallTree branchSpinLoop [.scalar ⟨1, 4⟩]) :=
  treeSafe_of_step_inv branchSpinLoop1_step_self rfl

/-- `branchSpinLoop(1)` never reaches a return outcome along any trace. -/
theorem branchSpinLoop1_diverges (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet (mirCallTree branchSpinLoop [.scalar ⟨1, 4⟩]) tr o :=
  noRet_of_step_inv branchSpinLoop1_step_self rfl tr o

/-- Therefore MiniRust started at `f.start` steps forever in `StateRel` with an
Anneal state reachable via `Reaches` along the growing branch-observation trace. -/
theorem branchSpinLoop1_minirust_diverges_rel (n : Nat) :
    ∃ s' m' tr, Interp.steps (initLen branchSpinLoop + n) branchSpinLoop1MInit = .ok m' ∧
      StateRel branchSpinLoop branchSpinLoopFn ctx0 s' m' ∧
      Reaches (mirCallTree branchSpinLoop [.scalar ⟨1, 4⟩]) tr (mirTree branchSpinLoop s') :=
  mirCall_diverges_rel branchSpinLoop_inFragment branchSpinLoop_translate ctx0 (ctx0_ok2 rfl)
    [.scalar ⟨1, 4⟩] (by decide) branchSpinLoop1MInit rfl rfl rfl
    branchSpinLoop1_noUB branchSpinLoop1_diverges n

/-! ## Wrapping and unchecked shifts (`Shl`, `Shr`, `ShlUnchecked`, `ShrUnchecked`) -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn shift_i8(mut a: i8, s: i8) -> i8 {
    a = a >> -6i8;              // bb0: _1 = Shr(copy _1, const -6i8)   -- (-6).rem_euclid(8) = 2
    a = a << -7i8;              //      _1 = Shl(copy _1, const -7i8)   -- (-7).rem_euclid(8) = 1
    a = unchecked_shr(a, s);    //      _1 = ShrUnchecked(copy _1, copy _2)
    unchecked_shl(a, s)         //      _0 = ShlUnchecked(copy _1, copy _2); return
}
```
where `-6i8` has bit pattern `250` and `-7i8` has bit pattern `249`. -/
def shiftI8 : CapturedMir where
  defPath := "witness::shift_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [{
    statements := [
      mkStmt (.assign (local_ 1) (.binaryOp .shr (.copy (local_ 1)) (constI8 250))),
      mkStmt (.assign (local_ 1) (.binaryOp .shl (.copy (local_ 1)) (constI8 249))),
      mkStmt (.assign (local_ 1) (.binaryOp .shrUnchecked (.copy (local_ 1)) (.copy (local_ 2)))),
      mkStmt (.assign (local_ 0) (.binaryOp .shlUnchecked (.copy (local_ 1)) (.copy (local_ 2))))],
    terminator := mkTerm .return_,
    isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem shiftI8_inFragment : inFragment shiftI8 = true := by decide

def shiftI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int (-6)) (.Int i8))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Shl) (.Load (.Local (localName 1))) (.Constant (.Int (-7)) (.Int i8))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .ShrUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .ShlUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem shiftI8_translate : translateFn shiftI8 = some shiftI8Fn := rfl

/-- Input `(-64i8, 3i8)` (bits `192`, `3`):
`-64i8 >> -6i8 = -64i8 >> 2 = -16i8` (bits `240`),
`-16i8 << -7i8 = -16i8 << 1 = -32i8` (bits `224`),
`unchecked_shr(-32i8, 3i8) = -4i8` (bits `252`),
`unchecked_shl(-4i8, 3i8) = -32i8` (bits `224`). -/
def shiftOkS0 : MachineState := initMachineState shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨3, 1⟩]
def shiftOkMInit : Mach :=
  machineWithCtx ctxI8_3 shiftI8 shiftI8Fn shiftOkS0.frame.locals shiftI8Fn.start

theorem shiftOk_anneal_ret :
    ReachesRet (mirCallTree shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨3, 1⟩]) []
      (.normal (.scalar ⟨224, 1⟩, shiftOkS0.memory)) :=
  runA_sound shiftI8 10 _ _ _ rfl

theorem shiftOk_noUB :
    MirNoUBTree (mirCallTree shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨3, 1⟩]) :=
  runA_noUB shiftI8 10 _ _ _ rfl

theorem shiftOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n shiftOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 224 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret shiftI8_inFragment shiftI8_translate ctxI8_3 (ctxI8_ok3 rfl)
      [.scalar ⟨192, 1⟩, .scalar ⟨3, 1⟩] (by decide) shiftOkMInit rfl rfl rfl shiftOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [shiftI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem shiftOk_minirust_direct :
    (Interp.steps 6 shiftOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 224 }, [1]) := rfl

/-- `ShrUnchecked` UB when `s = 8i8` (`s >= bits`). -/
def shrUncheckedGe8UbS0 : MachineState := initMachineState shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨8, 1⟩]
def shrUncheckedGe8UbMInit : Mach :=
  machineWithCtx ctxI8_3 shiftI8 shiftI8Fn shrUncheckedGe8UbS0.frame.locals shiftI8Fn.start

theorem shrUncheckedGe8Ub_anneal_ub :
    ∃ tr u, Reaches (mirCallTree shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨8, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound shiftI8 6 _ (by decide)

theorem shrUncheckedGe8Ub_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n shrUncheckedGe8UbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := shrUncheckedGe8Ub_anneal_ub
  exact mirCall_ub shiftI8_inFragment shiftI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨192, 1⟩, .scalar ⟨8, 1⟩] (by decide) shrUncheckedGe8UbMInit rfl rfl rfl hr hf

theorem shrUncheckedGe8Ub_minirust_direct :
    Interp.steps 4 shrUncheckedGe8UbMInit = .error (.ub "overflow in unchecked shift") := rfl

/-- `ShrUnchecked` UB when `s = -1i8` (bits `255`, `s < 0`). -/
def shrUncheckedNegUbS0 : MachineState := initMachineState shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨255, 1⟩]
def shrUncheckedNegUbMInit : Mach :=
  machineWithCtx ctxI8_3 shiftI8 shiftI8Fn shrUncheckedNegUbS0.frame.locals shiftI8Fn.start

theorem shrUncheckedNegUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree shiftI8 [.scalar ⟨192, 1⟩, .scalar ⟨255, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound shiftI8 6 _ (by decide)

theorem shrUncheckedNegUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n shrUncheckedNegUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := shrUncheckedNegUb_anneal_ub
  exact mirCall_ub shiftI8_inFragment shiftI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨192, 1⟩, .scalar ⟨255, 1⟩] (by decide) shrUncheckedNegUbMInit rfl rfl rfl hr hf

theorem shrUncheckedNegUb_minirust_direct :
    Interp.steps 4 shrUncheckedNegUbMInit = .error (.ub "overflow in unchecked shift") := rfl

/-- Standalone `ShlUnchecked` body `fn shl_unchecked_i8(a: i8, s: i8) -> i8 { unchecked_shl(a, s) }`
to witness both `s >= 8` and `s < 0` UB on `ShlUnchecked`. -/
def shlUncheckedI8 : CapturedMir where
  defPath := "witness::shl_unchecked_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [{
    statements := [
      mkStmt (.assign (local_ 0) (.binaryOp .shlUnchecked (.copy (local_ 1)) (.copy (local_ 2))))],
    terminator := mkTerm .return_,
    isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem shlUncheckedI8_inFragment : inFragment shlUncheckedI8 = true := by decide

def shlUncheckedI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .ShlUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem shlUncheckedI8_translate : translateFn shlUncheckedI8 = some shlUncheckedI8Fn := rfl

def shlUncheckedGe8UbS0 : MachineState := initMachineState shlUncheckedI8 [.scalar ⟨1, 1⟩, .scalar ⟨8, 1⟩]
def shlUncheckedGe8UbMInit : Mach :=
  machineWithCtx ctxI8_3 shlUncheckedI8 shlUncheckedI8Fn shlUncheckedGe8UbS0.frame.locals shlUncheckedI8Fn.start

theorem shlUncheckedGe8Ub_anneal_ub :
    ∃ tr u, Reaches (mirCallTree shlUncheckedI8 [.scalar ⟨1, 1⟩, .scalar ⟨8, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound shlUncheckedI8 5 _ (by decide)

theorem shlUncheckedGe8Ub_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n shlUncheckedGe8UbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := shlUncheckedGe8Ub_anneal_ub
  exact mirCall_ub shlUncheckedI8_inFragment shlUncheckedI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨1, 1⟩, .scalar ⟨8, 1⟩] (by decide) shlUncheckedGe8UbMInit rfl rfl rfl hr hf

theorem shlUncheckedGe8Ub_minirust_direct :
    Interp.steps 2 shlUncheckedGe8UbMInit = .error (.ub "overflow in unchecked shift") := rfl

def shlUncheckedNegUbS0 : MachineState := initMachineState shlUncheckedI8 [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩]
def shlUncheckedNegUbMInit : Mach :=
  machineWithCtx ctxI8_3 shlUncheckedI8 shlUncheckedI8Fn shlUncheckedNegUbS0.frame.locals shlUncheckedI8Fn.start

theorem shlUncheckedNegUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree shlUncheckedI8 [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound shlUncheckedI8 5 _ (by decide)

theorem shlUncheckedNegUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n shlUncheckedNegUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := shlUncheckedNegUb_anneal_ub
  exact mirCall_ub shlUncheckedI8_inFragment shlUncheckedI8_translate ctxI8_3 (ctxI8_ok3 rfl)
    [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩] (by decide) shlUncheckedNegUbMInit rfl rfl rfl hr hf

theorem shlUncheckedNegUb_minirust_direct :
    Interp.steps 2 shlUncheckedNegUbMInit = .error (.ub "overflow in unchecked shift") := rfl

/-! ## Signed two's-complement bitwise operators (`BitAnd`, `BitOr`, `BitXor`) and `CountOnes` -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn bitwise_i8(mut a: i8, b: i8) -> i8 {
    a = a & b;        // bb0: _1 = BitAnd(copy _1, copy _2)
    a = a | -123i8;   //      _1 = BitOr(copy _1, const -123i8)
    a ^ -59i8         //      _0 = BitXor(copy _1, const -59i8); return
}
```
where `-123i8` has bit pattern `133` (`0x85`) and `-59i8` has bit pattern `197`
(`0xC5`). -/
def bitwiseI8 : CapturedMir where
  defPath := "witness::bitwise_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i8Decl]
  basicBlocks := [{
    statements := [
      mkStmt (.assign (local_ 1) (.binaryOp .bitAnd (.copy (local_ 1)) (.copy (local_ 2)))),
      mkStmt (.assign (local_ 1) (.binaryOp .bitOr (.copy (local_ 1)) (constI8 133))),
      mkStmt (.assign (local_ 0) (.binaryOp .bitXor (.copy (local_ 1)) (constI8 197)))],
    terminator := mkTerm .return_,
    isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

theorem bitwiseI8_inFragment : inFragment bitwiseI8 = true := by decide

def bitwiseI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Int .BitAnd) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .BitOr) (.Load (.Local (localName 1))) (.Constant (.Int (-123)) (.Int i8))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .BitXor) (.Load (.Local (localName 1))) (.Constant (.Int (-59)) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem bitwiseI8_translate : translateFn bitwiseI8 = some bitwiseI8Fn := rfl

/-- Input `(-86i8, -15i8)` (bits `170 = 0xAA`, `241 = 0xF1`):
`(-86i8) & (-15i8) = -96i8` (bits `160 = 0xA0`),
`(-96i8) | (-123i8) = -91i8` (bits `165 = 0xA5`),
`(-91i8) ^ (-59i8) = 96i8` (bits `96 = 0x60`, cancelling the infinite leading
two's-complement `1` bits of both negative `libspecr::Int` operands). -/
def bitwiseNegS0 : MachineState := initMachineState bitwiseI8 [.scalar ⟨170, 1⟩, .scalar ⟨241, 1⟩]
def bitwiseNegMInit : Mach :=
  machineWithCtx ctxI8_3 bitwiseI8 bitwiseI8Fn bitwiseNegS0.frame.locals bitwiseI8Fn.start

theorem bitwiseNeg_anneal_ret :
    ReachesRet (mirCallTree bitwiseI8 [.scalar ⟨170, 1⟩, .scalar ⟨241, 1⟩]) []
      (.normal (.scalar ⟨96, 1⟩, bitwiseNegS0.memory)) :=
  runA_sound bitwiseI8 10 _ _ _ rfl

theorem bitwiseNeg_noUB :
    MirNoUBTree (mirCallTree bitwiseI8 [.scalar ⟨170, 1⟩, .scalar ⟨241, 1⟩]) :=
  runA_noUB bitwiseI8 10 _ _ _ rfl

theorem bitwiseNeg_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n bitwiseNegMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 96 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret bitwiseI8_inFragment bitwiseI8_translate ctxI8_3 (ctxI8_ok3 rfl)
      [.scalar ⟨170, 1⟩, .scalar ⟨241, 1⟩] (by decide) bitwiseNegMInit rfl rfl rfl bitwiseNeg_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [bitwiseI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem bitwiseNeg_minirust_direct :
    (Interp.steps 5 bitwiseNegMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 96 }, [1]) := rfl

/-- Direct ground-truth checks of `IntUnOp::CountOnes` (`eval_count_ones`):
`-86i8` (`0b1010_1010` modulo `2^8`) has `4` ones and `-1i8` (`0b1111_1111`
modulo `2^8`) has `8` ones, both returning `u32`. -/
theorem countOnes_neg86_i8 :
    evalUnOp (.Int .CountOnes) (.Int (-86), .Int i8) = .ok (.Int 4, .Int u32) := rfl

theorem countOnes_neg1_i8 :
    evalUnOp (.Int .CountOnes) (.Int (-1), .Int i8) = .ok (.Int 8, .Int u32) := rfl

/-! ## Heterogeneous shifts (`(i8, u32)`, `(i8, i32)`) and constant-discriminant `SwitchInt` -/

def i32Ty : Ty := { kind := .int .i32, layoutIdx := 0 }
def i32Decl : LocalDecl := { mutability := .mut, ty := i32Ty, debugName := none }
def i32 : Gen.IntType := ⟨.Signed, ⟨4⟩⟩

def i32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiHeteroShift : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct },
             { layout := i32Layout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_hetero {body : CapturedMir}
    (h : body.localDecls = [i8Decl, i8Decl, i32Decl]) : CtxOk body ctxI8_3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 2, hd => simp at hd; subst hd; rw [i32Decl, i32Ty, itOf_int, tyOf_int]; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn hetero_shift_switch(mut x: i8, k: i32) -> i8 {
    x = x >> 258u32;                // bb0: _1 = Shr(copy _1, const 258u32)   -- (i8, u32)
    x = x << 257u32;                //      _1 = Shl(copy _1, const 257u32)   -- (i8, u32)
    match -1i8 {                    //      switchInt(const -1i8) -> [-1i8: bb1, otherwise: bb2]
        -1 => {
            x = unchecked_shr(x, k); // bb1: _1 = ShrUnchecked(copy _1, copy _2) -- (i8, i32)
            unchecked_shl(x, k)      //      _0 = ShlUnchecked(copy _1, copy _2); return
        }
        _ => unreachable!(),        // bb2: unreachable
    }
}
```
exercising unequal `(lhs, rhs)` shift operand types (`(i8, u32)` and `(i8, i32)`)
together with a constant-operand signed `SwitchInt` scrutinee. -/
def heteroShiftSwitch : CapturedMir where
  defPath := "witness::hetero_shift_switch"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, i8Decl, i32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.binaryOp .shr (.copy (local_ 1)) (constU32 258))),
        mkStmt (.assign (local_ 1) (.binaryOp .shl (.copy (local_ 1)) (constU32 257)))],
      terminator := mkTerm (.switchInt (constI8 255)
        { branches := [(255, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.binaryOp .shrUnchecked (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.binaryOp .shlUnchecked (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [], terminator := mkTerm .unreachable, isCleanup := false }]
  fnAbi := fnAbiHeteroShift
  layouts := emptyLayoutTable
  allocations := []

theorem heteroShiftSwitch_inFragment : inFragment heteroShiftSwitch = true := by decide

def heteroShiftSwitchFn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Shr) (.Load (.Local (localName 1))) (.Constant (.Int 258) (.Int u32))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Shl) (.Load (.Local (localName 1))) (.Constant (.Int 257) (.Int u32)))],
      .Switch (.Constant (.Int (-1)) (.Int i8)) ⟨[(-1, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Int .ShrUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .ShlUnchecked) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Unreachable, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem heteroShiftSwitch_translate : translateFn heteroShiftSwitch = some heteroShiftSwitchFn := rfl

/-- Input `(-64i8, 3i32)` (bits `192`, `3`):
`-64i8 >> 258u32 = -64i8 >> 2 = -16i8` (bits `240`, with `258 >= 256`),
`-16i8 << 257u32 = -16i8 << 1 = -32i8` (bits `224`, with `257 >= 256`),
`switchInt(const -1i8)` takes the `-1` arm to `bb1`,
`unchecked_shr(-32i8, 3i32) = -4i8` (bits `252`), and
`unchecked_shl(-4i8, 3i32) = -32i8` (bits `224`). -/
def heteroShiftOkS0 : MachineState :=
  initMachineState heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨3, 4⟩]
def heteroShiftOkMInit : Mach :=
  machineWithCtx ctxI8_3 heteroShiftSwitch heteroShiftSwitchFn
    heteroShiftOkS0.frame.locals heteroShiftSwitchFn.start

def heteroShiftOkTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 255))), PUnit.unit⟩]

theorem heteroShiftOk_anneal_ret :
    ReachesRet (mirCallTree heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨3, 4⟩])
      heteroShiftOkTrace (.normal (.scalar ⟨224, 1⟩, heteroShiftOkS0.memory)) :=
  runA_sound heteroShiftSwitch 10 _ _ _ rfl

theorem heteroShiftOk_noUB :
    MirNoUBTree (mirCallTree heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨3, 4⟩]) :=
  runA_noUB heteroShiftSwitch 10 _ _ _ rfl

theorem heteroShiftOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n heteroShiftOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 224 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret heteroShiftSwitch_inFragment heteroShiftSwitch_translate ctxI8_3
      (ctxI8_ok_hetero rfl) [.scalar ⟨192, 1⟩, .scalar ⟨3, 4⟩] (by decide)
      heteroShiftOkMInit rfl rfl rfl heteroShiftOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [heteroShiftSwitch] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem heteroShiftOk_minirust_direct :
    (Interp.steps 7 heteroShiftOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 224 }, [1]) := rfl

/-- Heterogeneous `ShrUnchecked(i8, i32)` UB when `k = 8i32`: `8 < 32 = i32::BITS`
(in bounds for the RHS type `i32`), but `8 >= 8 = i8::BITS` (out of bounds for
the LHS type `i8`). -/
def heteroShrGe8UbS0 : MachineState :=
  initMachineState heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨8, 4⟩]
def heteroShrGe8UbMInit : Mach :=
  machineWithCtx ctxI8_3 heteroShiftSwitch heteroShiftSwitchFn
    heteroShrGe8UbS0.frame.locals heteroShiftSwitchFn.start

theorem heteroShrGe8Ub_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨8, 4⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound heteroShiftSwitch 8 _ (by decide)

theorem heteroShrGe8Ub_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n heteroShrGe8UbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := heteroShrGe8Ub_anneal_ub
  exact mirCall_ub heteroShiftSwitch_inFragment heteroShiftSwitch_translate ctxI8_3
    (ctxI8_ok_hetero rfl) [.scalar ⟨192, 1⟩, .scalar ⟨8, 4⟩] (by decide)
    heteroShrGe8UbMInit rfl rfl rfl hr hf

theorem heteroShrGe8Ub_minirust_direct :
    Interp.steps 5 heteroShrGe8UbMInit = .error (.ub "overflow in unchecked shift") := rfl

/-- Heterogeneous `ShrUnchecked(i8, i32)` UB when `k = -1i32` (bits `4294967295`
in 32-bit `i32`, negative `< 0`). -/
def heteroShrNegUbS0 : MachineState :=
  initMachineState heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨4294967295, 4⟩]
def heteroShrNegUbMInit : Mach :=
  machineWithCtx ctxI8_3 heteroShiftSwitch heteroShiftSwitchFn
    heteroShrNegUbS0.frame.locals heteroShiftSwitchFn.start

theorem heteroShrNegUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree heteroShiftSwitch [.scalar ⟨192, 1⟩, .scalar ⟨4294967295, 4⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound heteroShiftSwitch 8 _ (by decide)

theorem heteroShrNegUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n heteroShrNegUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := heteroShrNegUb_anneal_ub
  exact mirCall_ub heteroShiftSwitch_inFragment heteroShiftSwitch_translate ctxI8_3
    (ctxI8_ok_hetero rfl) [.scalar ⟨192, 1⟩, .scalar ⟨4294967295, 4⟩] (by decide)
    heteroShrNegUbMInit rfl rfl rfl hr hf

theorem heteroShrNegUb_minirust_direct :
    Interp.steps 5 heteroShrNegUbMInit = .error (.ub "overflow in unchecked shift") := rfl

/-! ## Uninitialized-operand UB (`BinaryOp`, `UnaryOp`, `SwitchInt`) and `IntBinOp::DivExact` -/

/-- Direct ground-truth checks of `IntBinOp::DivExact` (`spec/lang/step/operators.md`)
across all four outcomes on `i8`:
* exact division `-6i8 / 3i8 = -2i8`,
* non-zero remainder UB on `-7i8 / 3i8`,
* division by zero UB on `-6i8 / 0i8`, and
* signed overflow UB on `i8::MIN / -1i8 = -128 / -1`. -/
theorem divExact_ok_i8 :
    evalBinOp (.Int .DivExact) (.Int (-6), .Int i8) (.Int 3, .Int i8) =
      .ok (.Int (-2), .Int i8) := rfl

theorem divExact_rem_ub_i8 :
    evalBinOp (.Int .DivExact) (.Int (-7), .Int i8) (.Int 3, .Int i8) =
      .error (.ub "non-zero remainder in exact division") := rfl

theorem divExact_zero_ub_i8 :
    evalBinOp (.Int .DivExact) (.Int (-6), .Int i8) (.Int 0, .Int i8) =
      .error (.ub "division by zero") := rfl

theorem divExact_min_neg1_ub_i8 :
    evalBinOp (.Int .DivExact) (.Int (-128), .Int i8) (.Int (-1), .Int i8) =
      .error (.ub "overflow in division") := rfl

/-- MIR (`Runtime(PostCleanup)`) of a function that reads an uninitialized local
(`copy _0` before `_0` has been written) in three different positions depending
on `x`:
* `x == 0` (`bb1`): `_0 = Add(copy _0, copy _1)` (uninitialized operand in `BinaryOp`),
* `x == 1` (`bb2`): `_0 = Neg(copy _0)` (uninitialized operand in `UnaryOp`),
* otherwise (`bb3`): `switchInt(copy _0)` (uninitialized scrutinee in `SwitchInt`). -/
def uninitOperandUb : CapturedMir where
  defPath := "witness::uninit_operand_ub"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1))
        { branches := [(0, 1), (1, 2)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 0)) (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 0))
        { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem uninitOperandUb_inFragment : inFragment uninitOperandUb = true := by decide

def uninitOperandUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[],
      .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 1), (1, bbName 2)]⟩ (bbName 3),
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0))) (.Load (.Local (localName 1))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0)) (.UnOp (.Int .Neg) (.Load (.Local (localName 0))))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[],
      .Switch (.Load (.Local (localName 0))) ⟨[(0, bbName 1)]⟩ (bbName 2),
      .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem uninitOperandUb_translate : translateFn uninitOperandUb = some uninitOperandUbFn := rfl

/-- `x = 0i8`: `bb1` reads uninitialized `_0` in `BinaryOp(Add, copy _0, copy _1)`. -/
def uninitBinOpUbS0 : MachineState := initMachineState uninitOperandUb [.scalar ⟨0, 1⟩]
def uninitBinOpUbMInit : Mach :=
  machineWithCtx ctxI8 uninitOperandUb uninitOperandUbFn
    uninitBinOpUbS0.frame.locals uninitOperandUbFn.start

theorem uninitBinOpUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitOperandUb [.scalar ⟨0, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitOperandUb 6 _ (by decide)

theorem uninitBinOpUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBinOpUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBinOpUb_anneal_ub
  exact mirCall_ub uninitOperandUb_inFragment uninitOperandUb_translate ctxI8 (ctxI8_ok2 rfl)
    [.scalar ⟨0, 1⟩] (by decide) uninitBinOpUbMInit rfl rfl rfl hr hf

theorem uninitBinOpUb_minirust_direct :
    Interp.steps 3 uninitBinOpUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- `x = 1i8`: `bb2` reads uninitialized `_0` in `UnaryOp(Neg, copy _0)`. -/
def uninitUnOpUbS0 : MachineState := initMachineState uninitOperandUb [.scalar ⟨1, 1⟩]
def uninitUnOpUbMInit : Mach :=
  machineWithCtx ctxI8 uninitOperandUb uninitOperandUbFn
    uninitUnOpUbS0.frame.locals uninitOperandUbFn.start

theorem uninitUnOpUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitOperandUb [.scalar ⟨1, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitOperandUb 6 _ (by decide)

theorem uninitUnOpUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitUnOpUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitUnOpUb_anneal_ub
  exact mirCall_ub uninitOperandUb_inFragment uninitOperandUb_translate ctxI8 (ctxI8_ok2 rfl)
    [.scalar ⟨1, 1⟩] (by decide) uninitUnOpUbMInit rfl rfl rfl hr hf

theorem uninitUnOpUb_minirust_direct :
    Interp.steps 3 uninitUnOpUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- `x = 2i8`: `bb3` reads uninitialized `_0` as the scrutinee of `SwitchInt(copy _0)`. -/
def uninitSwitchUbS0 : MachineState := initMachineState uninitOperandUb [.scalar ⟨2, 1⟩]
def uninitSwitchUbMInit : Mach :=
  machineWithCtx ctxI8 uninitOperandUb uninitOperandUbFn
    uninitSwitchUbS0.frame.locals uninitOperandUbFn.start

theorem uninitSwitchUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitOperandUb [.scalar ⟨2, 1⟩]) tr u ∧ FaultNow u :=
  faultsA_sound uninitOperandUb 6 _ (by decide)

theorem uninitSwitchUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitSwitchUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitSwitchUb_anneal_ub
  exact mirCall_ub uninitOperandUb_inFragment uninitOperandUb_translate ctxI8 (ctxI8_ok2 rfl)
    [.scalar ⟨2, 1⟩] (by decide) uninitSwitchUbMInit rfl rfl rfl hr hf

theorem uninitSwitchUb_minirust_direct :
    Interp.steps 3 uninitSwitchUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

theorem uninitSwitchUb_converse_error :
    (∃ msg, Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree uninitOperandUb [.scalar ⟨2, 1⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 3 ∧ Interp.steps k uninitSwitchUbMInit = .ok mRet ∧
      ReturnRel uninitOperandUb ctxI8 s' v mRet ∧
      ReachesRet (mirCallTree uninitOperandUb [.scalar ⟨2, 1⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error uninitOperandUb_inFragment uninitOperandUb_translate ctxI8 (ctxI8_ok2 rfl)
    [.scalar ⟨2, 1⟩] (by decide) uninitSwitchUbMInit rfl rfl rfl uninitSwitchUb_minirust_direct

/-! ## Booleans: comparisons, `!`, `switchInt` on `bool`, and `bool` returns -/

def boolTy : Ty := { kind := .bool, layoutIdx := 0 }
def boolDecl : LocalDecl := { mutability := .mut, ty := boolTy, debugName := none }
def constBool (b : Bool) : Operand :=
  .constant { ty := boolTy, val := .scalar (.int ⟨if b then 1 else 0, 1⟩) }
def u8TyW : Ty := { kind := .uint .u8, layoutIdx := 0 }
def u8Decl : LocalDecl := { mutability := .mut, ty := u8TyW, debugName := none }
def constU8 (n : Nat) : Operand := .constant { ty := u8TyW, val := .scalar (.int ⟨n, 1⟩) }
def u8 : Gen.IntType := ⟨.Unsigned, ⟨1⟩⟩

/-- The layout of `bool` (one byte, alignment one); like the other ABI
layouts in this module, the fragment never reads it. -/
def boolLayout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiCmpNot : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct }, { layout := i8Layout, mode := .direct },
      { layout := boolLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- The callee's locals live at addresses `128`, `256`, `384`, and `512`. -/
def ctxI8_4 : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8], addrs := [128, 256, 384, 512],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxI8_ok_cmpNot {body : CapturedMir}
    (h : body.localDecls = [i8Decl, i8Decl, i8Decl, boolDecl]) : CtxOk body ctxI8_4 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 2, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 3, hd => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | _ + 4, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn cmp_not_switch(x: i8, y: i8, mut b: bool) -> i8 {
    b = x < y;               // bb0: _3 = Lt(copy _1, copy _2)
    b = !b;                  //      _3 = Not(copy _3)
    if b { return y; }       //      switchInt(copy _3) -> [0: bb1, otherwise: bb3]
    b = x == -1;             // bb1: _3 = Eq(copy _1, const -1_i8)
    b = b > false;           //      _3 = Gt(copy _3, const false)
    if b { x } else { y }    //      switchInt(copy _3) -> [0: bb3, otherwise: bb2]
}                            // bb2: _0 = copy _1; return    bb3: _0 = copy _2; return
```
For `(x, y) = (-1, 1)` the signed comparison `-1 < 1` holds, so `!b` is
`false`, the first switch takes `bb1`, `-1 == -1` and `true > false` hold, and
the function returns `x = -1` (bits `255`). Comparing the bit patterns
unsigned (`255 < 1`) would instead return `y`. -/
def cmpNotSwitch : CapturedMir where
  defPath := "witness::cmp_not_switch"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [i8Decl, i8Decl, i8Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .lt (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 3) (.unaryOp .not (.copy (local_ 3))))],
      terminator := mkTerm (.switchInt (.copy (local_ 3)) { branches := [(0, 1)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .eq (.copy (local_ 1)) (constI8 255))),
        mkStmt (.assign (local_ 3) (.binaryOp .gt (.copy (local_ 3)) (constBool false)))],
      terminator := mkTerm (.switchInt (.copy (local_ 3)) { branches := [(0, 3)], otherwise := 2 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCmpNot
  layouts := emptyLayoutTable
  allocations := []

theorem cmpNotSwitch_inFragment : inFragment cmpNotSwitch = true := by decide

/-- The MiniRust function `minimize` produces for `cmpNotSwitch`, spelled out:
the comparisons are `BinOp::Rel`, `!b` is `build::not` (a transmute of
`1u8 - transmute::<u8>(b)` back to `bool`), and each `switchInt` on `b`
switches on `transmute::<u8>(b)`. -/
def cmpNotSwitchFn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, .Bool)]⟩
  args := [localName 1, localName 2, localName 3]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.Rel .Lt) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 3))
        (.UnOp (.Cast (.Transmute .Bool))
          (.BinOp (.Int .Sub) (.Constant (.Int 1) (.Int u8))
            (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 3))))))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 3))))
        ⟨[(0, bbName 1)]⟩ (bbName 3), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.Rel .Eq) (.Load (.Local (localName 1))) (.Constant (.Int (-1)) (.Int i8))),
      .Assign (.Local (localName 3))
        (.BinOp (.Rel .Gt) (.Load (.Local (localName 3))) (.Constant (.Bool false) .Bool))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 3))))
        ⟨[(0, bbName 3)]⟩ (bbName 2), .Regular⟩),
    (bbName 2, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 1)))], .Return, .Regular⟩),
    (bbName 3, ⟨[.Assign (.Local (localName 0)) (.Load (.Local (localName 2)))], .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem cmpNotSwitch_translate : translateFn cmpNotSwitch = some cmpNotSwitchFn := rfl

/-- Input `(x, y, b) = (-1i8, 1i8, false)` (bits `255`, `1`, `0`). -/
def cmpNotNeg1Args : List Value := [.scalar ⟨255, 1⟩, .scalar ⟨1, 1⟩, .scalar ⟨0, 1⟩]
def cmpNotNeg1S0 : MachineState := initMachineState cmpNotSwitch cmpNotNeg1Args
def cmpNotNeg1MInit : Mach :=
  machineWithCtx ctxI8_4 cmpNotSwitch cmpNotSwitchFn cmpNotNeg1S0.frame.locals cmpNotSwitchFn.start

/-- The branch observations: the first `switchInt` sees `!(x < y) = false`
(`0`) and the second sees `(x == -1) > false = true` (`1`). -/
def cmpNotNeg1Trace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩, ⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]

/-- Anneal's semantics returns `x = -1i8` (bits `255`), computed by the
kernel. -/
theorem cmpNotNeg1_anneal_ret :
    ReachesRet (mirCallTree cmpNotSwitch cmpNotNeg1Args) cmpNotNeg1Trace
      (.normal (.scalar ⟨255, 1⟩, cmpNotNeg1S0.memory)) :=
  runA_sound cmpNotSwitch 20 _ _ _ rfl

theorem cmpNotNeg1_noUB : MirNoUBTree (mirCallTree cmpNotSwitch cmpNotNeg1Args) :=
  runA_noUB cmpNotSwitch 20 _ _ _ rfl

/-- Therefore (by `mirCall_ret`) MiniRust, started at `minimize`'s entry
block, returns the bytes of `-1i8` to the caller. -/
theorem cmpNotNeg1_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpNotNeg1MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 255 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpNotSwitch_inFragment cmpNotSwitch_translate ctxI8_4 (ctxI8_ok_cmpNot rfl)
      cmpNotNeg1Args (by decide) cmpNotNeg1MInit rfl rfl rfl cmpNotNeg1_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpNotSwitch] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
/-- The same return, computed directly: 9 MiniRust steps (the entry block,
three steps per block for `bb0` and `bb1`, and two for `bb2`). -/
theorem cmpNotNeg1_minirust_direct :
    (Interp.steps 9 cmpNotNeg1MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 255 }, [1]) := rfl

/-- Input `(x, y, b) = (3i8, 2i8, true)`: `3 < 2` fails, so `!b` is `true` and
the first switch returns `y = 2i8` from `bb3`. -/
def cmpNot3Args : List Value := [.scalar ⟨3, 1⟩, .scalar ⟨2, 1⟩, .scalar ⟨1, 1⟩]
def cmpNot3S0 : MachineState := initMachineState cmpNotSwitch cmpNot3Args
def cmpNot3MInit : Mach :=
  machineWithCtx ctxI8_4 cmpNotSwitch cmpNotSwitchFn cmpNot3S0.frame.locals cmpNotSwitchFn.start

theorem cmpNot3_anneal_ret :
    ReachesRet (mirCallTree cmpNotSwitch cmpNot3Args) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨2, 1⟩, cmpNot3S0.memory)) :=
  runA_sound cmpNotSwitch 20 _ _ _ rfl

theorem cmpNot3_noUB : MirNoUBTree (mirCallTree cmpNotSwitch cmpNot3Args) :=
  runA_noUB cmpNotSwitch 20 _ _ _ rfl

theorem cmpNot3_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpNot3MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 2 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpNotSwitch_inFragment cmpNotSwitch_translate ctxI8_4 (ctxI8_ok_cmpNot rfl)
      cmpNot3Args (by decide) cmpNot3MInit rfl rfl rfl cmpNot3_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpNotSwitch] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem cmpNot3_minirust_direct :
    (Interp.steps 6 cmpNot3MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 2 }, [1]) := rfl

/-! ### Returning a `bool` -/

def fnAbiU8ToBool : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct }, { layout := i8Layout, mode := .direct }],
    ret := { layout := boolLayout, mode := .direct }, conv := .rust, canUnwind := false }

def ctxBool : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8], addrs := [128, 256, 384],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxBool_ok {body : CapturedMir} (h : body.localDecls = [boolDecl, u8Decl, u8Decl]) :
    CtxOk body ctxBool where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | 1, hd => simp at hd; subst hd; rw [u8Decl, u8TyW, itOf_uint, tyOf_uint]; decide
    | 2, hd => simp at hd; subst hd; rw [u8Decl, u8TyW, itOf_uint, tyOf_uint]; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [boolDecl, boolTy, itOf_bool]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn le_ne_ge(x: u8, y: u8) -> bool {
    if x <= y { x != y }      // bb0: _0 = Le(copy _1, copy _2);
                              //      switchInt(copy _0) -> [0: bb2, otherwise: bb1]
                              // bb1: _0 = Ne(copy _1, copy _2); return
    else { x >= 200 }         // bb2: _0 = Ge(copy _1, const 200_u8); return
}
```
whose return place `_0` is a `bool` that also serves as the switch scrutinee,
so the return path loads and stores the result at `Type::Bool`. -/
def leNeGe : CapturedMir where
  defPath := "witness::le_ne_ge"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [boolDecl, u8Decl, u8Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .le (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm (.switchInt (.copy (local_ 0)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .ne (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .ge (.copy (local_ 1)) (constU8 200)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU8ToBool
  layouts := emptyLayoutTable
  allocations := []

theorem leNeGe_inFragment : inFragment leNeGe = true := by decide

def leNeGeFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool), (localName 1, .Int u8), (localName 2, .Int u8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Rel .Le) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 0))))
        ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Rel .Ne) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Rel .Ge) (.Load (.Local (localName 1))) (.Constant (.Int 200) (.Int u8)))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem leNeGe_translate : translateFn leNeGe = some leNeGeFn := rfl

/-- Input `(250u8, 7u8)`: `250 <= 7` fails, and `250 >= 200` returns `true`
(byte `1`). -/
def leNeGe250Args : List Value := [.scalar ⟨250, 1⟩, .scalar ⟨7, 1⟩]
def leNeGe250S0 : MachineState := initMachineState leNeGe leNeGe250Args
def leNeGe250MInit : Mach :=
  machineWithCtx ctxBool leNeGe leNeGeFn leNeGe250S0.frame.locals leNeGeFn.start

theorem leNeGe250_anneal_ret :
    ReachesRet (mirCallTree leNeGe leNeGe250Args) [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, leNeGe250S0.memory)) :=
  runA_sound leNeGe 10 _ _ _ rfl

theorem leNeGe250_noUB : MirNoUBTree (mirCallTree leNeGe leNeGe250Args) :=
  runA_noUB leNeGe 10 _ _ _ rfl

theorem leNeGe250_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n leNeGe250MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 1 } ∧
      m'.threads = [thread1 ctxBool [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret leNeGe_inFragment leNeGe_translate ctxBool (ctxBool_ok rfl)
      leNeGe250Args (by decide) leNeGe250MInit rfl rfl rfl leNeGe250_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [leNeGe] at hd; subst hd
  simp [retPtr, ctxBool] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxBool] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem leNeGe250_minirust_direct :
    (Interp.steps 5 leNeGe250MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 1 }, [1]) := rfl

/-- Input `(5u8, 5u8)`: `5 <= 5` holds, and `5 != 5` returns `false`
(byte `0`). -/
def leNeGe5Args : List Value := [.scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩]
def leNeGe5S0 : MachineState := initMachineState leNeGe leNeGe5Args
def leNeGe5MInit : Mach :=
  machineWithCtx ctxBool leNeGe leNeGeFn leNeGe5S0.frame.locals leNeGeFn.start

theorem leNeGe5_anneal_ret :
    ReachesRet (mirCallTree leNeGe leNeGe5Args) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 1⟩, leNeGe5S0.memory)) :=
  runA_sound leNeGe 10 _ _ _ rfl

theorem leNeGe5_noUB : MirNoUBTree (mirCallTree leNeGe leNeGe5Args) :=
  runA_noUB leNeGe 10 _ _ _ rfl

theorem leNeGe5_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n leNeGe5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 0 } ∧
      m'.threads = [thread1 ctxBool [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret leNeGe_inFragment leNeGe_translate ctxBool (ctxBool_ok rfl)
      leNeGe5Args (by decide) leNeGe5MInit rfl rfl rfl leNeGe5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [leNeGe] at hd; subst hd
  simp [retPtr, ctxBool] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxBool] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem leNeGe5_minirust_direct :
    (Interp.steps 5 leNeGe5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 0 }, [1]) := rfl

/-! ### `bool`-to-integer cast (`CastKind::IntToInt` on `Type::Bool`) -/

def fnAbiBoolToI8 : FnAbi :=
  { args := [{ layout := boolLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_boolCast {body : CapturedMir} (h : body.localDecls = [i8Decl, boolDecl]) :
    CtxOk body ctxI8 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn bool_cast_i8(mut b: bool) -> i8 {
    b = !(b == false);         // bb0: _1 = Eq(copy _1, const false); _1 = Not(copy _1);
                               //      switchInt(copy _1) -> [0: bb2, otherwise: bb1]
    if b { b as i8 }           // bb1: _0 = Cast(IntToInt, copy _1, i8); return
    else { b as i8 }           // bb2: _0 = Cast(IntToInt, copy _1, i8); return
}
```
exercising `Cast(CastKind::IntToInt)` on `Type::Bool` (which `minimize` lowers
by transmuting the `bool` to `u8` and then applying `CastOp::IntToInt`). -/
def boolCastI8 : CapturedMir where
  defPath := "witness::bool_cast_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.binaryOp .eq (.copy (local_ 1)) (constBool false))),
        mkStmt (.assign (local_ 1) (.unaryOp .not (.copy (local_ 1))))],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 1)) i8Ty))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 1)) i8Ty))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiBoolToI8
  layouts := emptyLayoutTable
  allocations := []

theorem boolCastI8_inFragment : inFragment boolCastI8 = true := by decide

def boolCastI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Bool)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1))
        (.BinOp (.Rel .Eq) (.Load (.Local (localName 1))) (.Constant (.Bool false) .Bool)),
      .Assign (.Local (localName 1))
        (.UnOp (.Cast (.Transmute .Bool))
          (.BinOp (.Int .Sub) (.Constant (.Int 1) (.Int u8))
            (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1))))))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1))))
        ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt i8))
          (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1)))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt i8))
          (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1)))))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem boolCastI8_translate : translateFn boolCastI8 = some boolCastI8Fn := rfl

/-- An invalid `bool` bit pattern (`2 >= 2`) is rejected by `argsOk`. -/
theorem boolCastInvalidArg_rejected : argsOk boolCastI8 [.scalar ⟨2, 1⟩] = false := rfl

/-- Input `b = true` (byte `1`): `!(true == false) = true`, casts `true as i8 = 1i8`. -/
def boolCastTrueArgs : List Value := [.scalar ⟨1, 1⟩]
def boolCastTrueS0 : MachineState := initMachineState boolCastI8 boolCastTrueArgs
def boolCastTrueMInit : Mach :=
  machineWithCtx ctxI8 boolCastI8 boolCastI8Fn boolCastTrueS0.frame.locals boolCastI8Fn.start

theorem boolCastTrue_anneal_ret :
    ReachesRet (mirCallTree boolCastI8 boolCastTrueArgs) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, boolCastTrueS0.memory)) :=
  runA_sound boolCastI8 15 _ _ _ rfl

theorem boolCastTrue_noUB : MirNoUBTree (mirCallTree boolCastI8 boolCastTrueArgs) :=
  runA_noUB boolCastI8 15 _ _ _ rfl

theorem boolCastTrue_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n boolCastTrueMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 1 } ∧
      m'.threads = [thread1 ctxI8 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret boolCastI8_inFragment boolCastI8_translate ctxI8 (ctxI8_ok_boolCast rfl)
      boolCastTrueArgs (by decide) boolCastTrueMInit rfl rfl rfl boolCastTrue_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [boolCastI8] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem boolCastTrue_minirust_direct :
    (Interp.steps 6 boolCastTrueMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 1 }, [1]) := rfl

/-- Input `b = false` (byte `0`): `!(false == false) = false`, casts `false as i8 = 0i8`. -/
def boolCastFalseArgs : List Value := [.scalar ⟨0, 1⟩]
def boolCastFalseS0 : MachineState := initMachineState boolCastI8 boolCastFalseArgs
def boolCastFalseMInit : Mach :=
  machineWithCtx ctxI8 boolCastI8 boolCastI8Fn boolCastFalseS0.frame.locals boolCastI8Fn.start

theorem boolCastFalse_anneal_ret :
    ReachesRet (mirCallTree boolCastI8 boolCastFalseArgs) [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 1⟩, boolCastFalseS0.memory)) :=
  runA_sound boolCastI8 15 _ _ _ rfl

theorem boolCastFalse_noUB : MirNoUBTree (mirCallTree boolCastI8 boolCastFalseArgs) :=
  runA_noUB boolCastI8 15 _ _ _ rfl

theorem boolCastFalse_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n boolCastFalseMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 0 } ∧
      m'.threads = [thread1 ctxI8 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret boolCastI8_inFragment boolCastI8_translate ctxI8 (ctxI8_ok_boolCast rfl)
      boolCastFalseArgs (by decide) boolCastFalseMInit rfl rfl rfl boolCastFalse_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [boolCastI8] at hd; subst hd
  simp [retPtr, ctxI8] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem boolCastFalse_minirust_direct :
    (Interp.steps 6 boolCastFalseMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 0 }, [1]) := rfl

/-! ### Reading an uninitialized `bool` -/

def fnAbiToBool : FnAbi :=
  { args := [], ret := { layout := boolLayout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR of `fn uninit_bool() -> bool` whose only block switches on the
uninitialized return place `_0`: both semantics raise UB at the load. -/
def uninitBool : CapturedMir where
  defPath := "witness::uninit_bool"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 0)) { branches := [(0, 1)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.unaryOp .not (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToBool
  layouts := emptyLayoutTable
  allocations := []

theorem uninitBool_inFragment : inFragment uninitBool = true := by decide

def uninitBoolFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 0))))
      ⟨[(0, bbName 1)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute .Bool))
          (.BinOp (.Int .Sub) (.Constant (.Int 1) (.Int u8))
            (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 0))))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 2
  implicit_writes := true

theorem uninitBool_translate : translateFn uninitBool = some uninitBoolFn := rfl

def uninitBoolS0 : MachineState := initMachineState uninitBool []
def uninitBoolMInit : Mach :=
  machineWithCtx ctxBool uninitBool uninitBoolFn uninitBoolS0.frame.locals uninitBoolFn.start

theorem ctxBool_ok1 {body : CapturedMir} (h : body.localDecls = [boolDecl]) : CtxOk body ctxBool where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | _ + 1, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [boolDecl, boolTy, itOf_bool]; decide⟩

theorem uninitBool_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitBool []) tr u ∧ FaultNow u :=
  faultsA_sound uninitBool 3 _ (by decide)

theorem uninitBool_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBoolMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBool_anneal_ub
  exact mirCall_ub uninitBool_inFragment uninitBool_translate ctxBool (ctxBool_ok1 rfl) []
    (by decide) uninitBoolMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitBool_minirust_direct :
    Interp.steps 2 uninitBoolMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- MIR of `fn uninit_bool_not() -> bool` whose entry block negates the
uninitialized return place `_0` (`_0 = !copy _0` via `build::not`), faulting
at the load of `_0` before the `u8` transmute. -/
def uninitBoolNot : CapturedMir where
  defPath := "witness::uninit_bool_not"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.unaryOp .not (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToBool
  layouts := emptyLayoutTable
  allocations := []

theorem uninitBoolNot_inFragment : inFragment uninitBoolNot = true := by decide

def uninitBoolNotFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute .Bool))
          (.BinOp (.Int .Sub) (.Constant (.Int 1) (.Int u8))
            (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 0))))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitBoolNot_translate : translateFn uninitBoolNot = some uninitBoolNotFn := rfl

def uninitBoolNotS0 : MachineState := initMachineState uninitBoolNot []
def uninitBoolNotMInit : Mach :=
  machineWithCtx ctxBool uninitBoolNot uninitBoolNotFn uninitBoolNotS0.frame.locals uninitBoolNotFn.start

theorem uninitBoolNot_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitBoolNot []) tr u ∧ FaultNow u :=
  faultsA_sound uninitBoolNot 3 _ (by decide)

theorem uninitBoolNot_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBoolNotMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBoolNot_anneal_ub
  exact mirCall_ub uninitBoolNot_inFragment uninitBoolNot_translate ctxBool (ctxBool_ok1 rfl) []
    (by decide) uninitBoolNotMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitBoolNot_minirust_direct :
    Interp.steps 2 uninitBoolNotMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- MIR of `fn uninit_bool_rel() -> bool` whose entry block compares the
uninitialized return place `_0` (`_0 = Eq(copy _0, const true)`), faulting at
the load of `_0` in `BinOp::Rel`. -/
def uninitBoolRel : CapturedMir where
  defPath := "witness::uninit_bool_rel"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .eq (.copy (local_ 0)) (constBool true)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToBool
  layouts := emptyLayoutTable
  allocations := []

theorem uninitBoolRel_inFragment : inFragment uninitBoolRel = true := by decide

def uninitBoolRelFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Rel .Eq) (.Load (.Local (localName 0))) (.Constant (.Bool true) .Bool))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitBoolRel_translate : translateFn uninitBoolRel = some uninitBoolRelFn := rfl

def uninitBoolRelS0 : MachineState := initMachineState uninitBoolRel []
def uninitBoolRelMInit : Mach :=
  machineWithCtx ctxBool uninitBoolRel uninitBoolRelFn uninitBoolRelS0.frame.locals uninitBoolRelFn.start

theorem uninitBoolRel_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitBoolRel []) tr u ∧ FaultNow u :=
  faultsA_sound uninitBoolRel 3 _ (by decide)

theorem uninitBoolRel_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBoolRelMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBoolRel_anneal_ub
  exact mirCall_ub uninitBoolRel_inFragment uninitBoolRel_translate ctxBool (ctxBool_ok1 rfl) []
    (by decide) uninitBoolRelMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitBoolRel_minirust_direct :
    Interp.steps 2 uninitBoolRelMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-! ## Three-way comparison `Cmp` and `core::cmp::Ordering` -/

def orderingTyW : Ty := { kind := .adt "core::cmp::Ordering" [], layoutIdx := 0 }
def orderingDecl : LocalDecl := { mutability := .mut, ty := orderingTyW, debugName := none }

/-- The ABI of `cmp_sel`. Like the other ABI layouts in this module, the
return layout is never read by the fragment, so the one-byte `i8Layout`
stands in for `Ordering`'s one-byte layout. -/
def fnAbiCmpSel : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct }, { layout := i8Layout, mode := .direct },
      { layout := boolLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_cmpSel {body : CapturedMir}
    (h : body.localDecls = [orderingDecl, i8Decl, i8Decl, boolDecl]) : CtxOk body ctxI8_4 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [orderingDecl, orderingTyW, itOf_ordering, tyOf_ordering]; decide
    | 1, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 2, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 3, hd => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | _ + 4, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [orderingDecl, orderingTyW, itOf_ordering]; decide⟩

/-- MIR (`Runtime(PostCleanup)`, with `Ord::cmp` inlined to `BinOp::Cmp`) of
```rust
fn cmp_sel(x: i8, y: i8, b: bool) -> Ordering {
    if b { x.cmp(&y) }       // bb0: switchInt(copy _3) -> [0: bb2, otherwise: bb1]
                             // bb1: _0 = Cmp(copy _1, copy _2); return
    else { true.cmp(&b) }    // bb2: _0 = Cmp(const true, copy _3); return
}
```
whose `Ordering` return place receives a three-way comparison of two signed
integers or of two `bool`s. `minimize` turns each `Cmp` into a transmute of
MiniRust's `i8` comparison result to `orderingTy` (`translateCmp`), and the
return path loads and stores the result at `orderingTy`. -/
def cmpSel : CapturedMir where
  defPath := "witness::cmp_sel"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [orderingDecl, i8Decl, i8Decl, boolDecl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 3)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .cmp (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .cmp (constBool true) (.copy (local_ 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCmpSel
  layouts := emptyLayoutTable
  allocations := []

theorem cmpSel_inFragment : inFragment cmpSel = true := by decide

/-- The MiniRust function `minimize` produces for `cmpSel`, spelled out: the
return place has type `orderingTy`, each `Cmp` is
`transmute::<orderingTy>(BinOp::Rel(RelOp::Cmp, ..))`, and the `switchInt` on
`b` switches on `transmute::<u8>(b)`. -/
def cmpSelFn : Gen.Function where
  locals := ⟨[(localName 0, orderingTy), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, .Bool)]⟩
  args := [localName 1, localName 2, localName 3]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 3))))
      ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute orderingTy))
          (.BinOp (.Rel .Cmp) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute orderingTy))
          (.BinOp (.Rel .Cmp) (.Constant (.Bool true) .Bool) (.Load (.Local (localName 3)))))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem cmpSel_translate : translateFn cmpSel = some cmpSelFn := rfl

/-- Input `(x, y, b) = (-1, 1, true)`: `(-1).cmp(&1)` is `Less`, whose tag is
the `i8` `-1` (byte `255`). Comparing the bit patterns unsigned (`255 > 1`)
would give `Greater` instead. -/
def cmpSelLessArgs : List Value := [.scalar ⟨255, 1⟩, .scalar ⟨1, 1⟩, .scalar ⟨1, 1⟩]
def cmpSelLessS0 : MachineState := initMachineState cmpSel cmpSelLessArgs
def cmpSelLessMInit : Mach :=
  machineWithCtx ctxI8_4 cmpSel cmpSelFn cmpSelLessS0.frame.locals cmpSelFn.start

theorem cmpSelLess_anneal_ret :
    ReachesRet (mirCallTree cmpSel cmpSelLessArgs) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨255, 1⟩, cmpSelLessS0.memory)) :=
  runA_sound cmpSel 10 _ _ _ rfl

theorem cmpSelLess_noUB : MirNoUBTree (mirCallTree cmpSel cmpSelLessArgs) :=
  runA_noUB cmpSel 10 _ _ _ rfl

theorem cmpSelLess_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpSelLessMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 255 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpSel_inFragment cmpSel_translate ctxI8_4 (ctxI8_ok_cmpSel rfl)
      cmpSelLessArgs (by decide) cmpSelLessMInit rfl rfl rfl cmpSelLess_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpSel] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem cmpSelLess_minirust_direct :
    (Interp.steps 4 cmpSelLessMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 255 }, [1]) := rfl

/-- Input `(7, 7, true)`: `7.cmp(&7)` is `Equal` (byte `0`). -/
def cmpSelEqualArgs : List Value := [.scalar ⟨7, 1⟩, .scalar ⟨7, 1⟩, .scalar ⟨1, 1⟩]
def cmpSelEqualS0 : MachineState := initMachineState cmpSel cmpSelEqualArgs
def cmpSelEqualMInit : Mach :=
  machineWithCtx ctxI8_4 cmpSel cmpSelFn cmpSelEqualS0.frame.locals cmpSelFn.start

theorem cmpSelEqual_anneal_ret :
    ReachesRet (mirCallTree cmpSel cmpSelEqualArgs) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 1⟩, cmpSelEqualS0.memory)) :=
  runA_sound cmpSel 10 _ _ _ rfl

theorem cmpSelEqual_noUB : MirNoUBTree (mirCallTree cmpSel cmpSelEqualArgs) :=
  runA_noUB cmpSel 10 _ _ _ rfl

theorem cmpSelEqual_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpSelEqualMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 0 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpSel_inFragment cmpSel_translate ctxI8_4 (ctxI8_ok_cmpSel rfl)
      cmpSelEqualArgs (by decide) cmpSelEqualMInit rfl rfl rfl cmpSelEqual_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpSel] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem cmpSelEqual_minirust_direct :
    (Interp.steps 4 cmpSelEqualMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 0 }, [1]) := rfl

/-- Input `(0, 0, false)`: `true.cmp(&false)` is `Greater` (byte `1`). -/
def cmpSelGreaterArgs : List Value := [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩]
def cmpSelGreaterS0 : MachineState := initMachineState cmpSel cmpSelGreaterArgs
def cmpSelGreaterMInit : Mach :=
  machineWithCtx ctxI8_4 cmpSel cmpSelFn cmpSelGreaterS0.frame.locals cmpSelFn.start

theorem cmpSelGreater_anneal_ret :
    ReachesRet (mirCallTree cmpSel cmpSelGreaterArgs) [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, cmpSelGreaterS0.memory)) :=
  runA_sound cmpSel 10 _ _ _ rfl

theorem cmpSelGreater_noUB : MirNoUBTree (mirCallTree cmpSel cmpSelGreaterArgs) :=
  runA_noUB cmpSel 10 _ _ _ rfl

theorem cmpSelGreater_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpSelGreaterMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 1 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpSel_inFragment cmpSel_translate ctxI8_4 (ctxI8_ok_cmpSel rfl)
      cmpSelGreaterArgs (by decide) cmpSelGreaterMInit rfl rfl rfl cmpSelGreater_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpSel] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem cmpSelGreater_minirust_direct :
    (Interp.steps 4 cmpSelGreaterMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 1 }, [1]) := rfl

/-! ### Returning an uninitialized `Ordering` -/

def fnAbiToOrdering : FnAbi :=
  { args := [], ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR of `fn uninit_ordering() -> Ordering` that returns without writing its
return place: both semantics raise UB when the return reads `_0` (MiniRust
decodes the `Uninit` byte at `orderingTy` and finds no tag). -/
def uninitOrdering : CapturedMir where
  defPath := "witness::uninit_ordering"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [orderingDecl]
  basicBlocks := [{ statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToOrdering
  layouts := emptyLayoutTable
  allocations := []

theorem uninitOrdering_inFragment : inFragment uninitOrdering = true := by decide

def uninitOrderingFn : Gen.Function where
  locals := ⟨[(localName 0, orderingTy)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[(bbName 0, ⟨[], .Return, .Regular⟩), (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitOrdering_translate : translateFn uninitOrdering = some uninitOrderingFn := rfl

theorem ctxBool_ok_ordering {body : CapturedMir} (h : body.localDecls = [orderingDecl]) :
    CtxOk body ctxBool where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [orderingDecl, orderingTyW, itOf_ordering, tyOf_ordering]; decide
    | _ + 1, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [orderingDecl, orderingTyW, itOf_ordering]; decide⟩

def uninitOrderingS0 : MachineState := initMachineState uninitOrdering []
def uninitOrderingMInit : Mach :=
  machineWithCtx ctxBool uninitOrdering uninitOrderingFn uninitOrderingS0.frame.locals
    uninitOrderingFn.start

theorem uninitOrdering_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitOrdering []) tr u ∧ FaultNow u :=
  faultsA_sound uninitOrdering 3 _ (by decide)

theorem uninitOrdering_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitOrderingMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitOrdering_anneal_ub
  exact mirCall_ub uninitOrdering_inFragment uninitOrdering_translate ctxBool
    (ctxBool_ok_ordering rfl) [] (by decide) uninitOrderingMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitOrdering_minirust_direct :
    Interp.steps 2 uninitOrderingMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-! ### `bool` bitwise `BitAnd`/`BitOr`/`BitXor`, unsigned `u8` `Cmp`, and `Ordering` `Use` -/

theorem ctxI8_ok_boolBitOrdUse {body : CapturedMir}
    (h : body.localDecls = [orderingDecl, boolDecl, u8Decl, orderingDecl]) : CtxOk body ctxI8_4 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [orderingDecl, orderingTyW, itOf_ordering, tyOf_ordering]; decide
    | 1, hd => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | 2, hd => simp at hd; subst hd; rw [u8Decl, u8TyW, itOf_uint, tyOf_uint]; decide
    | 3, hd => simp at hd; subst hd; rw [orderingDecl, orderingTyW, itOf_ordering, tyOf_ordering]; decide
    | _ + 4, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [orderingDecl, orderingTyW, itOf_ordering]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn bool_bit_ord_use(mut a: bool, x: u8, ord_in: Ordering) -> Ordering {
    // bb0: PlaceMention(_0) (while _0: Ordering is still uninitialized);
    a = ((a & true) | false) ^ true; //      _1 = BitAnd(copy _1, const true);
                                     //      _1 = BitOr(copy _1, const false);
                                     //      _1 = BitXor(copy _1, const true);
                                     //      switchInt(copy _1) -> [0: bb2, otherwise: bb1]
    if a { x.cmp(&1u8) }             // bb1: _0 = Cmp(copy _2, const 1u8); return
    else { ord_in }                  // bb2: _0 = Use(copy _3); return
}
```
exercising `PlaceMention(_0)` on an uninitialized `Ordering` local,
`build::bool_and`, `build::bool_or`, and `build::bool_xor` (`boolBitOp`),
unsigned `u8` three-way `Cmp` (`255u8.cmp(&1u8) = Greater`, whereas signed
`-1i8.cmp(&1i8) = Less` in `cmpSel`), and `Use(copy _3)` on an `Ordering`
local. -/
def boolBitOrdUse : CapturedMir where
  defPath := "witness::bool_bit_ord_use"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [orderingDecl, boolDecl, u8Decl, orderingDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.placeMention (local_ 0)),
        mkStmt (.assign (local_ 1) (.binaryOp .bitAnd (.copy (local_ 1)) (constBool true))),
        mkStmt (.assign (local_ 1) (.binaryOp .bitOr (.copy (local_ 1)) (constBool false))),
        mkStmt (.assign (local_ 1) (.binaryOp .bitXor (.copy (local_ 1)) (constBool true)))],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .cmp (.copy (local_ 2)) (constU8 1)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCmpSel
  layouts := emptyLayoutTable
  allocations := []

theorem boolBitOrdUse_inFragment : inFragment boolBitOrdUse = true := by decide

def boolBitOrdUseFn : Gen.Function where
  locals := ⟨[(localName 0, orderingTy), (localName 1, .Bool), (localName 2, .Int u8),
    (localName 3, orderingTy)]⟩
  args := [localName 1, localName 2, localName 3]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .PlaceMention (.Local (localName 0)),
      .Assign (.Local (localName 1))
        (boolBitOp .BitAnd (.Load (.Local (localName 1))) (.Constant (.Bool true) .Bool)),
      .Assign (.Local (localName 1))
        (boolBitOp .BitOr (.Load (.Local (localName 1))) (.Constant (.Bool false) .Bool)),
      .Assign (.Local (localName 1))
        (boolBitOp .BitXor (.Load (.Local (localName 1))) (.Constant (.Bool true) .Bool))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1))))
        ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (translateCmp (.Load (.Local (localName 2))) (.Constant (.Int 1) (.Int u8)))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 3)))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem boolBitOrdUse_translate : translateFn boolBitOrdUse = some boolBitOrdUseFn := rfl

/-- Invalid `Ordering` tag bytes (`2` and `128`, i.e. `-128i8`) are rejected by
`argsOk`. -/
theorem boolBitOrdInvalidTag_rejected :
    argsOk boolBitOrdUse [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩, .scalar ⟨2, 1⟩] = false ∧
      argsOk boolBitOrdUse [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩, .scalar ⟨128, 1⟩] = false :=
  ⟨rfl, rfl⟩

/-- Input `(false, 255u8, Equal)`: `((false & true) | false) ^ true = true`,
takes `bb1`, and unsigned `255u8.cmp(&1u8)` returns `Greater` (byte `1`). -/
def boolBitOrdUseCmpArgs : List Value := [.scalar ⟨0, 1⟩, .scalar ⟨255, 1⟩, .scalar ⟨0, 1⟩]
def boolBitOrdUseCmpS0 : MachineState := initMachineState boolBitOrdUse boolBitOrdUseCmpArgs
def boolBitOrdUseCmpMInit : Mach :=
  machineWithCtx ctxI8_4 boolBitOrdUse boolBitOrdUseFn boolBitOrdUseCmpS0.frame.locals
    boolBitOrdUseFn.start

theorem boolBitOrdUseCmp_anneal_ret :
    ReachesRet (mirCallTree boolBitOrdUse boolBitOrdUseCmpArgs)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, boolBitOrdUseCmpS0.memory)) :=
  runA_sound boolBitOrdUse 15 _ _ _ rfl

theorem boolBitOrdUseCmp_noUB : MirNoUBTree (mirCallTree boolBitOrdUse boolBitOrdUseCmpArgs) :=
  runA_noUB boolBitOrdUse 15 _ _ _ rfl

theorem boolBitOrdUseCmp_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n boolBitOrdUseCmpMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 1 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret boolBitOrdUse_inFragment boolBitOrdUse_translate ctxI8_4
      (ctxI8_ok_boolBitOrdUse rfl) boolBitOrdUseCmpArgs (by decide) boolBitOrdUseCmpMInit
      rfl rfl rfl boolBitOrdUseCmp_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [boolBitOrdUse] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem boolBitOrdUseCmp_minirust_direct :
    (Interp.steps 8 boolBitOrdUseCmpMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 1 }, [1]) := rfl

/-- Input `(true, 255u8, Less)`: `((true & true) | false) ^ true = false`,
takes `bb2`, and `_0 = Use(copy _3)` returns `Less` (byte `255`). -/
def boolBitOrdUseCopyArgs : List Value := [.scalar ⟨1, 1⟩, .scalar ⟨255, 1⟩, .scalar ⟨255, 1⟩]
def boolBitOrdUseCopyS0 : MachineState := initMachineState boolBitOrdUse boolBitOrdUseCopyArgs
def boolBitOrdUseCopyMInit : Mach :=
  machineWithCtx ctxI8_4 boolBitOrdUse boolBitOrdUseFn boolBitOrdUseCopyS0.frame.locals
    boolBitOrdUseFn.start

theorem boolBitOrdUseCopy_anneal_ret :
    ReachesRet (mirCallTree boolBitOrdUse boolBitOrdUseCopyArgs)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨255, 1⟩, boolBitOrdUseCopyS0.memory)) :=
  runA_sound boolBitOrdUse 15 _ _ _ rfl

theorem boolBitOrdUseCopy_noUB : MirNoUBTree (mirCallTree boolBitOrdUse boolBitOrdUseCopyArgs) :=
  runA_noUB boolBitOrdUse 15 _ _ _ rfl

theorem boolBitOrdUseCopy_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n boolBitOrdUseCopyMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 255 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret boolBitOrdUse_inFragment boolBitOrdUse_translate ctxI8_4
      (ctxI8_ok_boolBitOrdUse rfl) boolBitOrdUseCopyArgs (by decide) boolBitOrdUseCopyMInit
      rfl rfl rfl boolBitOrdUseCopy_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [boolBitOrdUse] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem boolBitOrdUseCopy_minirust_direct :
    (Interp.steps 8 boolBitOrdUseCopyMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 255 }, [1]) := rfl

/-- MIR of `fn uninit_bool_bitand() -> bool` whose entry block applies
`BitAnd(copy _0, const true)` (`build::bool_and`) to the uninitialized return
place `_0`, faulting at the load of `_0`. -/
def uninitBoolBitAnd : CapturedMir where
  defPath := "witness::uninit_bool_bitand"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .bitAnd (.copy (local_ 0)) (constBool true)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToBool
  layouts := emptyLayoutTable
  allocations := []

theorem uninitBoolBitAnd_inFragment : inFragment uninitBoolBitAnd = true := by decide

def uninitBoolBitAndFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (boolBitOp .BitAnd (.Load (.Local (localName 0))) (.Constant (.Bool true) .Bool))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitBoolBitAnd_translate : translateFn uninitBoolBitAnd = some uninitBoolBitAndFn := rfl

def uninitBoolBitAndS0 : MachineState := initMachineState uninitBoolBitAnd []
def uninitBoolBitAndMInit : Mach :=
  machineWithCtx ctxBool uninitBoolBitAnd uninitBoolBitAndFn uninitBoolBitAndS0.frame.locals
    uninitBoolBitAndFn.start

theorem uninitBoolBitAnd_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitBoolBitAnd []) tr u ∧ FaultNow u :=
  faultsA_sound uninitBoolBitAnd 3 _ (by decide)

theorem uninitBoolBitAnd_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBoolBitAndMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBoolBitAnd_anneal_ub
  exact mirCall_ub uninitBoolBitAnd_inFragment uninitBoolBitAnd_translate ctxBool (ctxBool_ok1 rfl) []
    (by decide) uninitBoolBitAndMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitBoolBitAnd_minirust_direct :
    Interp.steps 2 uninitBoolBitAndMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- MIR of `fn uninit_bool_bitor_rhs() -> bool` whose entry block applies
`BitOr(const true, copy _0)` (`build::bool_or`) to an initialized LHS `true`
and the uninitialized return place `_0` on the RHS, confirming that MIR
`BinaryOp(BitOr)` on `bool` does not short-circuit and faults when loading the
uninitialized RHS operand `_0`. -/
def uninitBoolBitOrRhs : CapturedMir where
  defPath := "witness::uninit_bool_bitor_rhs"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.binaryOp .bitOr (constBool true) (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiToBool
  layouts := emptyLayoutTable
  allocations := []

theorem uninitBoolBitOrRhs_inFragment : inFragment uninitBoolBitOrRhs = true := by decide

def uninitBoolBitOrRhsFn : Gen.Function where
  locals := ⟨[(localName 0, .Bool)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (boolBitOp .BitOr (.Constant (.Bool true) .Bool) (.Load (.Local (localName 0))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitBoolBitOrRhs_translate : translateFn uninitBoolBitOrRhs = some uninitBoolBitOrRhsFn := rfl

def uninitBoolBitOrRhsS0 : MachineState := initMachineState uninitBoolBitOrRhs []
def uninitBoolBitOrRhsMInit : Mach :=
  machineWithCtx ctxBool uninitBoolBitOrRhs uninitBoolBitOrRhsFn uninitBoolBitOrRhsS0.frame.locals
    uninitBoolBitOrRhsFn.start

theorem uninitBoolBitOrRhs_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitBoolBitOrRhs []) tr u ∧ FaultNow u :=
  faultsA_sound uninitBoolBitOrRhs 3 _ (by decide)

theorem uninitBoolBitOrRhs_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitBoolBitOrRhsMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitBoolBitOrRhs_anneal_ub
  exact mirCall_ub uninitBoolBitOrRhs_inFragment uninitBoolBitOrRhs_translate ctxBool (ctxBool_ok1 rfl) []
    (by decide) uninitBoolBitOrRhsMInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitBoolBitOrRhs_minirust_direct :
    Interp.steps 2 uninitBoolBitOrRhsMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-! ### Ground truth for the interpreted operators

Direct evaluations of the transcribed MiniRust operators, independent of the
correspondence. -/

/-- `BinOp::Rel` compares signed integers by value: `-1i8 < 1i8`. -/
theorem relLt_signed : evalBinOp (.Rel .Lt) (.Int (-1), .Int i8) (.Int 1, .Int i8) =
    .ok (.Bool true, .Bool) := rfl

/-- `BinOp::Rel` compares unsigned integers by value: `255u8 > 1u8`. -/
theorem relGt_unsigned : evalBinOp (.Rel .Gt) (.Int 255, .Int u8) (.Int 1, .Int u8) =
    .ok (.Bool true, .Bool) := rfl

/-- `RelOp::Cmp` returns an `i8`: `-1` for `-1i8 < 1i8`, `1` for
`255u8 > 1u8`, and `0` for equal `bool`s. -/
theorem relCmp_signed : evalBinOp (.Rel .Cmp) (.Int (-1), .Int i8) (.Int 1, .Int i8) =
    .ok (.Int (-1), .Int IntType.I8) := rfl
theorem relCmp_unsigned : evalBinOp (.Rel .Cmp) (.Int 255, .Int u8) (.Int 1, .Int u8) =
    .ok (.Int 1, .Int IntType.I8) := rfl
theorem relCmp_bool : evalBinOp (.Rel .Cmp) (.Bool true, .Bool) (.Bool true, .Bool) =
    .ok (.Int 0, .Int IntType.I8) := rfl

/-- `bool`s compare with `false < true`, and `Le`/`Ge`/`Ne` are the negations
of `Gt`/`Lt`/`Eq`. -/
theorem relLt_bool : evalBinOp (.Rel .Lt) (.Bool false, .Bool) (.Bool true, .Bool) =
    .ok (.Bool true, .Bool) := rfl
theorem relGt_bool : evalBinOp (.Rel .Gt) (.Bool true, .Bool) (.Bool false, .Bool) =
    .ok (.Bool true, .Bool) := rfl
theorem relLe_bool : evalBinOp (.Rel .Le) (.Bool true, .Bool) (.Bool false, .Bool) =
    .ok (.Bool false, .Bool) := rfl
theorem relGe_bool : evalBinOp (.Rel .Ge) (.Bool false, .Bool) (.Bool false, .Bool) =
    .ok (.Bool true, .Bool) := rfl
theorem relEq_bool : evalBinOp (.Rel .Eq) (.Bool false, .Bool) (.Bool false, .Bool) =
    .ok (.Bool true, .Bool) := rfl
theorem relNe_bool : evalBinOp (.Rel .Ne) (.Bool false, .Bool) (.Bool true, .Bool) =
    .ok (.Bool true, .Bool) := rfl
theorem relGe_eq : evalBinOp (.Rel .Ge) (.Int 7, .Int u8) (.Int 7, .Int u8) =
    .ok (.Bool true, .Bool) := rfl
theorem relNe_eq : evalBinOp (.Rel .Ne) (.Int 7, .Int u8) (.Int 7, .Int u8) =
    .ok (.Bool false, .Bool) := rfl

/-- A comparison of mismatched values is a spec panic (an ill-formed program),
not UB. -/
theorem rel_mismatch : evalBinOp (.Rel .Eq) (.Int 1, .Int i8) (.Bool true, .Bool) =
    .error (.specPanic "relational operator on incomparable type or value-type mismatch") := rfl

/-- `CastOp::Transmute` goes through the bytes: `true` becomes `1u8`, `1u8`
becomes `true`, the byte `2` is not a valid `bool`, and transmuting between
types of different sizes is UB. -/
theorem transmute_bool_u8 : evalCastOp (.Transmute (.Int u8)) (.Bool true, .Bool) =
    .ok (.Int 1, .Int u8) := rfl
theorem transmute_u8_bool : evalCastOp (.Transmute .Bool) (.Int 1, .Int u8) =
    .ok (.Bool true, .Bool) := rfl
theorem transmute_u8_bool_invalid : evalCastOp (.Transmute .Bool) (.Int 2, .Int u8) =
    .error (.ub "transmuted value is not valid at new type") := rfl
theorem transmute_size_mismatch :
    evalCastOp (.Transmute .Bool) (.Int 1, .Int ⟨.Unsigned, ⟨2⟩⟩) =
      .error (.ub "transmute between types of different size") := rfl

/-- `Type::Bool` decodes only the bytes `0` and `1`. -/
theorem decode_bool_invalid :
    Type.decode .Bool [.Init 2 none] = .ok none ∧ Type.decode .Bool [.Uninit] = .ok none ∧
      Type.decode .Bool [.Init 1 none] = .ok (some (.Bool true)) := ⟨rfl, rfl, rfl⟩

/-- `UnOp::Int` on a `bool` is a spec panic: MiniRust has no Boolean `!`. -/
theorem bitNot_bool_panics : evalUnOp (.Int .BitNot) (.Bool true, .Bool) =
    .error (.specPanic "non-integer input to integer operation") := rfl

/-- `core::cmp::Ordering`'s discriminator accepts exactly the tags `0`, `1`,
and `255` (the `i8`s `0`, `1`, `-1`) among all one-byte patterns. -/
theorem ordering_validTags : (List.range 256).filter (validBits orderingTy) = [0, 1, 255] := by
  decide +kernel

/-- `Type::decode` at `orderingTy` walks the discriminator: the byte `255` is
the tag `-1` of `Less`, while `2` and `128` (the `i8` `-128`) fall into the
`Invalid` fallback and an `Uninit` byte has no tag. -/
theorem decode_ordering_less :
    Type.decode orderingTy [.Init 255 none] = .ok (some (.Variant (-1) (.Tuple []))) := rfl
theorem decode_ordering_invalid :
    Type.decode orderingTy [.Init 2 none] = .ok none ∧
      Type.decode orderingTy [.Init 128 none] = .ok none ∧
      Type.decode orderingTy [.Uninit] = .ok none := ⟨rfl, rfl, rfl⟩

/-- `Type::encode` at `orderingTy` encodes the variant's empty tuple as one
`Uninit` byte and then writes the tag over it (`encode_discriminant`). -/
theorem encode_ordering_greater :
    Type.encode orderingTy (.Variant 1 (.Tuple [])) = .ok [.Init 1 none] := rfl

/-- `check_value` rejects a discriminant without a variant as UB. -/
theorem checkValue_variant_invalid :
    checkValue (.Variant 2 (.Tuple [])) orderingTy =
      .error (.ub "Value::Variant: invalid discrimant") := rfl

/-- `translateCmp`'s transmute: the `i8` `-1` becomes `Less`, while the `i8`
`2` (which `RelOp::Cmp` never returns) is not a valid `Ordering`. -/
theorem transmute_i8_ordering :
    transmute (.Int (-1)) (.Int IntType.I8) orderingTy = .ok (.Variant (-1) (.Tuple [])) := rfl
theorem transmute_i8_ordering_invalid :
    transmute (.Int 2) (.Int IntType.I8) orderingTy =
      .error (.ub "transmuted value is not valid at new type") := rfl

/-- A padded tuple `(i8, bool)` with the `bool` at offset 2 and alignment 2:
`head_size_and_align` rounds the head size 3 up to 4, `Type::encode` makes
both padding bytes `Uninit`, `Type::decode` ignores them, and `check_value`
rejects a value with the wrong number of fields as UB. -/
def paddedPairTy : Gen.Type := .Tuple [(⟨0⟩, .Int IntType.I8), (⟨2⟩, .Bool)] ⟨⟨3⟩, ⟨2⟩, none⟩ none
theorem layout_paddedPair : Type.layout paddedPairTy = .ok (.Sized ⟨4⟩ ⟨2⟩) := rfl
theorem encode_paddedPair :
    Type.encode paddedPairTy (.Tuple [.Int (-2), .Bool true]) =
      .ok [.Init 254 none, .Uninit, .Init 1 none, .Uninit] := rfl
set_option maxRecDepth 8192 in
theorem decode_paddedPair :
    Type.decode paddedPairTy [.Init 254 none, .Init 7 none, .Init 1 none, .Uninit] =
      .ok (some (.Tuple [.Int (-2), .Bool true])) := rfl
theorem checkValue_tuple_arity :
    checkValue (.Tuple [.Int (-2)]) paddedPairTy =
      .error (.ub "Value::Tuple: invalid number of fields") := rfl

set_option maxRecDepth 8192 in
/-- `decodeDiscriminant` threads the `FnMut` accessor state `s` and evaluates
the `fallback` continuation only when no child branch matches: here a child
branch matches `(-1, 0)` at offset `0`, so the fallback (which would read
out-of-bounds offset `99`) is never invoked and the visited-offset log is
`[0]`. -/
theorem decodeDiscriminant_short_circuits :
    decodeDiscriminant
      (fun (s : List Nat) o sz => do
        let chunk ← subsliceWithLength ([.Init 255 none] : List Byte) o.bytes sz.bytes
        pure (chunk, s ++ [o.bytes]))
      (.Branch ⟨0⟩ IntType.I8
        (.Branch ⟨99⟩ IntType.I8 .Invalid ⟨[]⟩)
        ⟨[((-1, 0), .Known (-1))]⟩)
      [] = .ok (some (-1), [0]) := rfl

/-- Unsized `Type::Slice`, `Type::TraitObject`, and unsized `Type::Tuple`:
`Type.layout` returns `LayoutStrategy::Slice`, `LayoutStrategy::TraitObject`,
or `LayoutStrategy::Tuple`, and `LayoutStrategy.expect_size`,
`LayoutStrategy.expect_align`, `evalCastOp (.Transmute ...)`, `Type.decode`,
`Type.encode`, and `checkValue` raise the exact upstream `specPanic`s from
`spec/lang/types.md` and `spec/lang/representation.md`. -/
theorem layout_slice :
    Type.layout (.Slice .Bool) = .ok (.Slice ⟨1⟩ ⟨1⟩) := rfl
theorem layout_traitObject :
    Type.layout (.TraitObject ⟨⟨0⟩⟩) = .ok (.TraitObject ⟨⟨0⟩⟩) := rfl
theorem layout_unsizedTuple :
    Type.layout (.Tuple [] ⟨⟨1⟩, ⟨1⟩, none⟩ (some (.Slice .Bool))) =
      .ok (.Tuple ⟨⟨1⟩, ⟨1⟩, none⟩ (.Slice ⟨1⟩ ⟨1⟩)) := rfl
theorem expectSize_unsized_panics :
    LayoutStrategy.expect_size (.Slice ⟨1⟩ ⟨1⟩) "WF" =
      .error (.specPanic "expect_size called on unsized type: WF") := by
  simp [LayoutStrategy.expect_size, specPanic]
theorem expectAlign_traitObject_panics :
    LayoutStrategy.expect_align (.TraitObject ⟨⟨0⟩⟩) "WF" =
      .error (.specPanic "expect_align called on unsized type: WF") := by
  simp [LayoutStrategy.expect_align, specPanic]
theorem transmute_unsized_panics :
    evalCastOp (.Transmute .Bool) (.Tuple [], .Slice .Bool) =
      .error (.specPanic "expect_size called on unsized type: WF ensures transmutes are sized") := by
  simp [evalCastOp, Type.layout, LayoutStrategy.expect_size, LayoutStrategy.expect_align, specPanic]
theorem decode_unsized_panics :
    Type.decode (.Slice .Bool) [] =
      .error (.specPanic "decode of Type::Slice") := rfl
theorem encode_unsized_panics :
    Type.encode (.TraitObject ⟨⟨0⟩⟩) (.Tuple []) =
      .error (.specPanic "encode of Type::TraitObject") := rfl
theorem checkValue_unsized_panics :
    checkValue (.Tuple []) (.Slice .Bool) =
      .error (.specPanic "Value: slices cannot be represented as values") := rfl

/-- `Type::Union` with two 1-byte chunks at offsets `0` and `2` and padding at
offsets `1` and `3`: `Type::decode` extracts each chunk's raw `AbstractByte`s
(including `Uninit`) and ignores gap bytes outside `chunks`, `Type::encode`
restores each chunk at its offset and fills gap bytes with `Uninit`, and
`checkValue` rejects a wrong number of chunks or a chunk of wrong byte length
as UB. -/
def unionPaddedTy : Gen.Type :=
  .Union [(⟨0⟩, .Int IntType.I8), (⟨2⟩, .Bool)] [(⟨0⟩, ⟨1⟩), (⟨2⟩, ⟨1⟩)] ⟨4⟩ ⟨2⟩
theorem layout_union : Type.layout unionPaddedTy = .ok (.Sized ⟨4⟩ ⟨2⟩) := rfl
theorem decode_union :
    Type.decode unionPaddedTy [.Init 254 none, .Init 7 none, .Uninit, .Init 9 none] =
      .ok (some (.Union [[.Init 254 none], [.Uninit]])) := rfl
theorem encode_union :
    Type.encode unionPaddedTy (.Union [[.Init 254 none], [.Uninit]]) =
      .ok [.Init 254 none, .Uninit, .Uninit, .Uninit] := rfl
theorem checkValue_union_chunk_size :
    checkValue (.Union [[.Init 254 none]]) unionPaddedTy =
      .error (.ub "Value::Union: invalid chunk size") := rfl
theorem checkValue_union_chunk_data :
    checkValue (.Union [[.Init 254 none], [.Init 1 none, .Init 2 none]]) unionPaddedTy =
      .error (.ub "Value::Union: invalid chunk data") := rfl

set_option maxRecDepth 8192 in
/-- `CastOp::Transmute` between `unionPaddedTy` and `paddedPairTy` (both of size
`4` and alignment `2`, with active fields/chunks at offsets `0` and `2` and
padding/gaps at offsets `1` and `3`): transmuting a union with valid `i8` and
`bool` chunk bytes produces the corresponding tuple (and vice versa), whereas
transmuting a union whose second chunk at offset `2` is `Uninit` raises UB
because `paddedPairTy`'s `bool` field at offset `2` fails `Type::decode`. -/
theorem transmute_union_paddedPair :
    evalCastOp (.Transmute paddedPairTy) (.Union [[.Init 254 none], [.Init 1 none]], unionPaddedTy) =
      .ok (.Tuple [.Int (-2), .Bool true], paddedPairTy) := rfl
set_option maxRecDepth 8192 in
theorem transmute_paddedPair_union :
    evalCastOp (.Transmute unionPaddedTy) (.Tuple [.Int (-2), .Bool true], paddedPairTy) =
      .ok (.Union [[.Init 254 none], [.Init 1 none]], unionPaddedTy) := rfl
set_option maxRecDepth 8192 in
theorem transmute_union_paddedPair_uninit_ub :
    evalCastOp (.Transmute paddedPairTy) (.Union [[.Init 254 none], [.Uninit]], unionPaddedTy) =
      .error (.ub "transmuted value is not valid at new type") := rfl

/-! ## Checked integer arithmetic (`AddWithOverflow`, `SubWithOverflow`, `MulWithOverflow`) and `(Int, bool)` 2-tuples -/

def i8BoolTupleTyW : Ty := { kind := .tuple [.int .i8, .bool], layoutIdx := 0 }
def i8BoolTupleDecl : LocalDecl := { mutability := .mut, ty := i8BoolTupleTyW, debugName := none }
def u32BoolTupleTyW : Ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := 0 }
def u32BoolTupleDecl : LocalDecl := { mutability := .mut, ty := u32BoolTupleTyW, debugName := none }

def field0I8 (i : Nat) : Place := { local_ := i, projection := [.field 0 i8Ty] }
def field0U32 (i : Nat) : Place := { local_ := i, projection := [.field 0 u32Ty] }
def field1 (i : Nat) : Place := { local_ := i, projection := [.field 1 boolTy] }

/-- The callee's 5 locals live at addresses `128`, `256`, `384`, `512`, and `640`. -/
def ctxI8_5 : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8],
    addrs := [128, 256, 384, 512, 640],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxI8_ok_checkedArith {body : CapturedMir}
    (h : body.localDecls = [i8Decl, i8Decl, i8Decl, i8BoolTupleDecl, boolDecl]) :
    CtxOk body ctxI8_5 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 2, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 3, hd => simp at hd; subst hd; rw [i8BoolTupleDecl, i8BoolTupleTyW, itOf_i8BoolTuple, tyOf_i8BoolTuple]; decide
    | 4, hd => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | _ + 5, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

def fnAbiCheckedArithI8 : FnAbi :=
  { args := [{ layout := i8Layout, mode := .direct }, { layout := i8Layout, mode := .direct },
      { layout := i8Layout, mode := .direct }, { layout := boolLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn checked_arith_i8(x: i8, y: i8, mut t: (i8, bool), mut ov: bool) -> i8 {
    t = AddWithOverflow(x, y);                     // bb0: _3 = AddWithOverflow(copy _1, copy _2)
    ov = t.1;                                      //      _4 = Use(copy (_3.1))
    if ov {                                        //      switchInt(copy _4) -> [0: bb1, otherwise: bb3]
        return t.0;                                // bb3: _0 = Use(copy (_3.0)); return
    }
    t = SubWithOverflow(t.0, 1i8);                 // bb1: _3 = SubWithOverflow(copy (_3.0), const 1i8)
    if t.1 {                                       //      switchInt(copy (_3.1)) -> [0: bb2, otherwise: bb3]
        return t.0;
    }
    t = MulWithOverflow(t.0, 2i8);                 // bb2: _3 = MulWithOverflow(copy (_3.0), const 2i8)
    if t.1 {                                       //      switchInt(copy (_3.1)) -> [0: bb3, otherwise: bb4]
        return -t.0;                               // bb4: _0 = Neg(copy (_3.0)); return
    }
    t.0                                            // bb3: _0 = Use(copy (_3.0)); return
}
```
Exercises `AddWithOverflow`, `SubWithOverflow`, and `MulWithOverflow` on signed
`i8`, field projections `_3.0` and `_3.1` in `Rvalue::Use`, `Rvalue::BinaryOp`,
`Rvalue::UnaryOp`, and `TerminatorKind::SwitchInt`, both without overflow and
on `INT_MAX + 1`, `INT_MIN - 1`, and signed multiplication overflow. -/
def checkedArithI8 : CapturedMir where
  defPath := "witness::checked_arith_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 4
  localDecls := [i8Decl, i8Decl, i8Decl, i8BoolTupleDecl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 4) (.use (.copy (field1 3))))],
      terminator := mkTerm (.switchInt (.copy (local_ 4)) { branches := [(0, 1)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .subWithOverflow (.copy (field0I8 3)) (constI8 1)))],
      terminator := mkTerm (.switchInt (.copy (field1 3)) { branches := [(0, 2)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .mulWithOverflow (.copy (field0I8 3)) (constI8 2)))],
      terminator := mkTerm (.switchInt (.copy (field1 3)) { branches := [(0, 3)], otherwise := 4 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (field0I8 3))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy (field0I8 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCheckedArithI8
  layouts := emptyLayoutTable
  allocations := []

theorem checkedArithI8_inFragment : inFragment checkedArithI8 = true := by decide

def checkedArithI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, intBoolTupleTy i8), (localName 4, .Bool)]⟩
  args := [localName 1, localName 2, localName 3, localName 4]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.IntWithOverflow .Add) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 4))
        (.Load (.Field (.Local (localName 3)) 1))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 4))))
        ⟨[(0, bbName 1)]⟩ (bbName 3), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.IntWithOverflow .Sub)
          (.Load (.Field (.Local (localName 3)) 0))
          (.Constant (.Int 1) (.Int i8)))],
      .Switch
        (.UnOp (.Cast (.Transmute (.Int u8)))
          (.Load (.Field (.Local (localName 3)) 1)))
        ⟨[(0, bbName 2)]⟩ (bbName 3), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.IntWithOverflow .Mul)
          (.Load (.Field (.Local (localName 3)) 0))
          (.Constant (.Int 2) (.Int i8)))],
      .Switch
        (.UnOp (.Cast (.Transmute (.Int u8)))
          (.Load (.Field (.Local (localName 3)) 1)))
        ⟨[(0, bbName 3)]⟩ (bbName 4), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0))
        (.Load (.Field (.Local (localName 3)) 0))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[
      .Assign (.Local (localName 0))
        (.UnOp (.Int .Neg)
          (.Load (.Field (.Local (localName 3)) 0)))],
      .Return, .Regular⟩),
    (bbName 5, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 5
  implicit_writes := true

theorem checkedArithI8_translate : translateFn checkedArithI8 = some checkedArithI8Fn := rfl

/-- An invalid `bool` bit pattern (`2 >= 2`) in field 1 of a `(i8, bool)` tuple
argument is rejected by `argsOk`. -/
theorem checkedArithInvalidTupleArg_rejected :
    argsOk checkedArithI8
      [.scalar ⟨30, 1⟩, .scalar ⟨20, 1⟩, .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨2, 1⟩], .scalar ⟨0, 1⟩] =
      false := rfl

/-- No-overflow input `(30i8, 20i8)`:
`30 + 20 = (50, false)`, `50 - 1 = (49, false)`, `49 * 2 = (98, false) -> 98i8`. -/
def checkedArithOkArgs : List Value :=
  [.scalar ⟨30, 1⟩, .scalar ⟨20, 1⟩, .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩], .scalar ⟨0, 1⟩]
def checkedArithOkS0 : MachineState := initMachineState checkedArithI8 checkedArithOkArgs
def checkedArithOkMInit : Mach :=
  machineWithCtx ctxI8_5 checkedArithI8 checkedArithI8Fn checkedArithOkS0.frame.locals
    checkedArithI8Fn.start

def checkedArithOkTrace : List (Event MirEffect) :=
  [0, 0, 0].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

theorem checkedArithOk_anneal_ret :
    ReachesRet (mirCallTree checkedArithI8 checkedArithOkArgs) checkedArithOkTrace
      (.normal (.scalar ⟨98, 1⟩, checkedArithOkS0.memory)) :=
  runA_sound checkedArithI8 20 _ _ _ rfl

theorem checkedArithOk_noUB : MirNoUBTree (mirCallTree checkedArithI8 checkedArithOkArgs) :=
  runA_noUB checkedArithI8 20 _ _ _ rfl

theorem checkedArithOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedArithOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 98 } ∧
      m'.threads = [thread1 ctxI8_5 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedArithI8_inFragment checkedArithI8_translate ctxI8_5
      (ctxI8_ok_checkedArith rfl) checkedArithOkArgs (by decide) checkedArithOkMInit
      rfl rfl rfl checkedArithOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_5] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_5] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedArithOk_minirust_direct :
    (Interp.steps 10 checkedArithOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 98 }, [1]) := rfl

/-- Signed addition overflow (`INT_MAX + 1`): `(127i8, 1i8)` computes
`AddWithOverflow(127i8, 1i8) = (-128i8, true)` (bits `128`, flag `1`),
branches on `_4 = _3.1 = true` to `bb3`, and returns `_3.0 = -128i8`. -/
def checkedArithAddOvArgs : List Value :=
  [.scalar ⟨127, 1⟩, .scalar ⟨1, 1⟩, .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩], .scalar ⟨0, 1⟩]
def checkedArithAddOvS0 : MachineState := initMachineState checkedArithI8 checkedArithAddOvArgs
def checkedArithAddOvMInit : Mach :=
  machineWithCtx ctxI8_5 checkedArithI8 checkedArithI8Fn checkedArithAddOvS0.frame.locals
    checkedArithI8Fn.start

theorem checkedArithAddOv_anneal_ret :
    ReachesRet (mirCallTree checkedArithI8 checkedArithAddOvArgs)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨128, 1⟩, checkedArithAddOvS0.memory)) :=
  runA_sound checkedArithI8 20 _ _ _ rfl

theorem checkedArithAddOv_noUB : MirNoUBTree (mirCallTree checkedArithI8 checkedArithAddOvArgs) :=
  runA_noUB checkedArithI8 20 _ _ _ rfl

theorem checkedArithAddOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedArithAddOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 128 } ∧
      m'.threads = [thread1 ctxI8_5 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedArithI8_inFragment checkedArithI8_translate ctxI8_5
      (ctxI8_ok_checkedArith rfl) checkedArithAddOvArgs (by decide) checkedArithAddOvMInit
      rfl rfl rfl checkedArithAddOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_5] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_5] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedArithAddOv_minirust_direct :
    (Interp.steps 6 checkedArithAddOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 128 }, [1]) := rfl

/-- Signed subtraction underflow (`INT_MIN - 1`): `(-128i8, 0i8)` (bits `128, 0`)
computes `AddWithOverflow(-128i8, 0i8) = (-128i8, false)`, then in `bb1`
`SubWithOverflow(-128i8, 1i8) = (127i8, true)` (bits `127`, flag `1`),
branches on `_3.1 = true` to `bb3`, and returns `_3.0 = 127i8`. -/
def checkedArithSubOvArgs : List Value :=
  [.scalar ⟨128, 1⟩, .scalar ⟨0, 1⟩, .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩], .scalar ⟨0, 1⟩]
def checkedArithSubOvS0 : MachineState := initMachineState checkedArithI8 checkedArithSubOvArgs
def checkedArithSubOvMInit : Mach :=
  machineWithCtx ctxI8_5 checkedArithI8 checkedArithI8Fn checkedArithSubOvS0.frame.locals
    checkedArithI8Fn.start

def checkedArithSubOvTrace : List (Event MirEffect) :=
  [0, 1].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

theorem checkedArithSubOv_anneal_ret :
    ReachesRet (mirCallTree checkedArithI8 checkedArithSubOvArgs) checkedArithSubOvTrace
      (.normal (.scalar ⟨127, 1⟩, checkedArithSubOvS0.memory)) :=
  runA_sound checkedArithI8 20 _ _ _ rfl

theorem checkedArithSubOv_noUB : MirNoUBTree (mirCallTree checkedArithI8 checkedArithSubOvArgs) :=
  runA_noUB checkedArithI8 20 _ _ _ rfl

theorem checkedArithSubOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedArithSubOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 127 } ∧
      m'.threads = [thread1 ctxI8_5 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedArithI8_inFragment checkedArithI8_translate ctxI8_5
      (ctxI8_ok_checkedArith rfl) checkedArithSubOvArgs (by decide) checkedArithSubOvMInit
      rfl rfl rfl checkedArithSubOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_5] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_5] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedArithSubOv_minirust_direct :
    (Interp.steps 8 checkedArithSubOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 127 }, [1]) := rfl

/-- Signed multiplication overflow: `(65i8, 0i8)` computes `65 + 0 = (65, false)`,
`65 - 1 = (64, false)`, and `MulWithOverflow(64i8, 2i8) = (-128i8, true)`
(since `64 * 2 = 128` overflows `i8` and wraps to `-128i8`, bits `128`),
branches to `bb4`, and returns `-(-128i8) = -128i8` (bits `128`). -/
def checkedArithMulOvArgs : List Value :=
  [.scalar ⟨65, 1⟩, .scalar ⟨0, 1⟩, .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩], .scalar ⟨0, 1⟩]
def checkedArithMulOvS0 : MachineState := initMachineState checkedArithI8 checkedArithMulOvArgs
def checkedArithMulOvMInit : Mach :=
  machineWithCtx ctxI8_5 checkedArithI8 checkedArithI8Fn checkedArithMulOvS0.frame.locals
    checkedArithI8Fn.start

def checkedArithMulOvTrace : List (Event MirEffect) :=
  [0, 0, 1].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

theorem checkedArithMulOv_anneal_ret :
    ReachesRet (mirCallTree checkedArithI8 checkedArithMulOvArgs) checkedArithMulOvTrace
      (.normal (.scalar ⟨128, 1⟩, checkedArithMulOvS0.memory)) :=
  runA_sound checkedArithI8 20 _ _ _ rfl

theorem checkedArithMulOv_noUB : MirNoUBTree (mirCallTree checkedArithI8 checkedArithMulOvArgs) :=
  runA_noUB checkedArithI8 20 _ _ _ rfl

theorem checkedArithMulOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedArithMulOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 128 } ∧
      m'.threads = [thread1 ctxI8_5 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedArithI8_inFragment checkedArithI8_translate ctxI8_5
      (ctxI8_ok_checkedArith rfl) checkedArithMulOvArgs (by decide) checkedArithMulOvMInit
      rfl rfl rfl checkedArithMulOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedArithI8] at hd; subst hd
  simp [retPtr, ctxI8_5] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_5] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedArithMulOv_minirust_direct :
    (Interp.steps 10 checkedArithMulOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 128 }, [1]) := rfl

/-! ### Padded `(u32, bool)` 2-tuples, `Aggregate(Tuple)`, `UINT_MAX + 1`, `0 - 1`, and `u32` multiplication overflow -/

/-- Caller return allocation for `(u32, bool)`: size `8` bytes, alignment `4`. -/
def retAllocTupleU32 : Gen.Allocation :=
  { data := List.replicate 8 .Uninit, addr := 64, align := ⟨4⟩, kind := .Stack, live := true,
    extra := () }

def callerFnTupleU32 : Gen.Function where
  locals := ⟨[(localName 0, intBoolTupleTy u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true

def callerFrameTupleU32 : Frame :=
  { func := callerFnTupleU32, locals := ⟨[(localName 0, retPtr)]⟩, stack_pop_action := .BottomOfStack,
    next_block := bbName 0, next_stmt := 0, extra := () }

def ctxTupleU32 : Ctx :=
  { caller := callerFrameTupleU32, payloads := [], base := [retAllocTupleU32],
    addrs := [128, 256, 384],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxTupleU32_ok {body : CapturedMir}
    (h : body.localDecls = [u32BoolTupleDecl, u32Decl, u32Decl]) :
    CtxOk body ctxTupleU32 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [u32BoolTupleDecl, u32BoolTupleTyW, itOf_u32BoolTuple, tyOf_u32BoolTuple]; decide
    | 1, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 2, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocTupleU32, rfl, rfl, rfl, rfl, rfl, by rw [u32BoolTupleDecl, u32BoolTupleTyW, itOf_u32BoolTuple]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn checked_tuple_u32(x: u32, y: u32) -> (u32, bool) {
    // bb0: PlaceMention(_0), PlaceMention(_0.0), PlaceMention(_0.1) (while _0: (u32, bool) is uninit)
    let mut t: (u32, bool) = SubWithOverflow(x, y); // _0 = SubWithOverflow(copy _1, copy _2)
    if t.1 {                                        // switchInt(copy (_0.1)) -> [0: bb1, otherwise: bb2]
        return AddWithOverflow(t.0, 1u32);          // bb2: _0 = AddWithOverflow(copy (_0.0), const 1u32); return
    }
    t = MulWithOverflow(t.0, y);                    // bb1: _0 = MulWithOverflow(copy (_0.0), copy _2)
    (t.0, t.1)                                      //      _0 = Aggregate(Tuple, [copy (_0.0), copy (_0.1)]); return
}
```
Exercises:
* `PlaceMention(_0)`, `PlaceMention(_0.0)`, and `PlaceMention(_0.1)` on the uninitialized `(u32, bool)` return place `_0`;
* unsigned `0u32 - 1u32 = (u32::MAX, true)` underflow followed by `u32::MAX + 1u32 = (0u32, true)` overflow;
* unsigned `65536u32 * 65536u32 = (0u32, true)` multiplication overflow;
* `Rvalue::Aggregate(AggregateKind::Tuple, [copy (_0.0), copy (_0.1)])` (`ValueExpr::Tuple`);
* returning a padded `(u32, bool)` tuple in `_0` (writing 4-byte `u32` at offset `0`, 1-byte `bool` at offset `4`, and 3 trailing `AbstractByte::Uninit` padding bytes at offsets `5..8`). -/
def checkedTupleU32 : CapturedMir where
  defPath := "witness::checked_tuple_u32"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32BoolTupleDecl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.placeMention (local_ 0)),
        mkStmt (.placeMention (field0U32 0)),
        mkStmt (.placeMention (field1 0)),
        mkStmt (.assign (local_ 0) (.binaryOp .subWithOverflow (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm (.switchInt (.copy (field1 0)) { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .mulWithOverflow (.copy (field0U32 0)) (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.aggregate .tuple [.copy (field0U32 0), .copy (field1 0)]))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .addWithOverflow (.copy (field0U32 0)) (constU32 1)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem checkedTupleU32_inFragment : inFragment checkedTupleU32 = true := by decide

def checkedTupleU32Fn : Gen.Function where
  locals := ⟨[(localName 0, intBoolTupleTy u32), (localName 1, .Int u32), (localName 2, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .PlaceMention (.Local (localName 0)),
      .PlaceMention (.Field (.Local (localName 0)) 0),
      .PlaceMention (.Field (.Local (localName 0)) 1),
      .Assign (.Local (localName 0))
        (.BinOp (.IntWithOverflow .Sub) (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Switch
        (.UnOp (.Cast (.Transmute (.Int u8)))
          (.Load (.Field (.Local (localName 0)) 1)))
        ⟨[(0, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.IntWithOverflow .Mul)
          (.Load (.Field (.Local (localName 0)) 0))
          (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.Tuple [
          .Load (.Field (.Local (localName 0)) 0),
          .Load (.Field (.Local (localName 0)) 1)]
          (intBoolTupleTy u32))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.IntWithOverflow .Add)
          (.Load (.Field (.Local (localName 0)) 0))
          (.Constant (.Int 1) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem checkedTupleU32_translate : translateFn checkedTupleU32 = some checkedTupleU32Fn := rfl

/-- Unsigned underflow `0u32 - 1u32 = (4294967295u32, true)` followed by
`UINT_MAX + 1` (`4294967295u32 + 1u32 = (0u32, true)`), returning `(0u32, true)`
encoded as `tupleBytes u32 0 1` (with 3 trailing `Uninit` padding bytes). -/
def checkedTupleUnderAddOvArgs : List Value := [.scalar ⟨0, 4⟩, .scalar ⟨1, 4⟩]
def checkedTupleUnderAddOvS0 : MachineState :=
  initMachineState checkedTupleU32 checkedTupleUnderAddOvArgs
def checkedTupleUnderAddOvMInit : Mach :=
  machineWithCtx ctxTupleU32 checkedTupleU32 checkedTupleU32Fn
    checkedTupleUnderAddOvS0.frame.locals checkedTupleU32Fn.start

theorem checkedTupleUnderAddOv_anneal_ret :
    ReachesRet (mirCallTree checkedTupleU32 checkedTupleUnderAddOvArgs)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.aggregate 0 [.scalar ⟨0, 4⟩, .scalar ⟨1, 1⟩], checkedTupleUnderAddOvS0.memory)) :=
  runA_sound checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleUnderAddOv_noUB :
    MirNoUBTree (mirCallTree checkedTupleU32 checkedTupleUnderAddOvArgs) :=
  runA_noUB checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleUnderAddOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedTupleUnderAddOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocTupleU32 with data := tupleBytes u32 0 1 } ∧
      m'.threads = [thread1 ctxTupleU32 [{ callerFrameTupleU32 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedTupleU32_inFragment checkedTupleU32_translate ctxTupleU32
      (ctxTupleU32_ok rfl) checkedTupleUnderAddOvArgs (by decide) checkedTupleUnderAddOvMInit
      rfl rfl rfl checkedTupleUnderAddOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedTupleU32] at hd; subst hd
  simp [retPtr, ctxTupleU32] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxTupleU32] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedTupleUnderAddOv_minirust_direct :
    (Interp.steps 8 checkedTupleUnderAddOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocTupleU32 with data := tupleBytes u32 0 1 }, [1]) := rfl

/-- Unsigned multiplication overflow `(131072u32, 65536u32)`:
`131072u32 - 65536u32 = (65536u32, false)`, then
`MulWithOverflow(65536u32, 65536u32) = (0u32, true)` (`2^16 * 2^16 = 2^32`),
repackaged via `Aggregate(Tuple, [copy (_0.0), copy (_0.1)])` and returned. -/
def checkedTupleMulOvArgs : List Value := [.scalar ⟨131072, 4⟩, .scalar ⟨65536, 4⟩]
def checkedTupleMulOvS0 : MachineState :=
  initMachineState checkedTupleU32 checkedTupleMulOvArgs
def checkedTupleMulOvMInit : Mach :=
  machineWithCtx ctxTupleU32 checkedTupleU32 checkedTupleU32Fn
    checkedTupleMulOvS0.frame.locals checkedTupleU32Fn.start

theorem checkedTupleMulOv_anneal_ret :
    ReachesRet (mirCallTree checkedTupleU32 checkedTupleMulOvArgs)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.aggregate 0 [.scalar ⟨0, 4⟩, .scalar ⟨1, 1⟩], checkedTupleMulOvS0.memory)) :=
  runA_sound checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleMulOv_noUB :
    MirNoUBTree (mirCallTree checkedTupleU32 checkedTupleMulOvArgs) :=
  runA_noUB checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleMulOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedTupleMulOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocTupleU32 with data := tupleBytes u32 0 1 } ∧
      m'.threads = [thread1 ctxTupleU32 [{ callerFrameTupleU32 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedTupleU32_inFragment checkedTupleU32_translate ctxTupleU32
      (ctxTupleU32_ok rfl) checkedTupleMulOvArgs (by decide) checkedTupleMulOvMInit
      rfl rfl rfl checkedTupleMulOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedTupleU32] at hd; subst hd
  simp [retPtr, ctxTupleU32] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxTupleU32] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedTupleMulOv_minirust_direct :
    (Interp.steps 9 checkedTupleMulOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocTupleU32 with data := tupleBytes u32 0 1 }, [1]) := rfl

/-- No-overflow input `(10u32, 3u32)`: `10 - 3 = (7, false)`, `7 * 3 = (21, false)`,
repackaged via `Aggregate(Tuple)` and returned as `tupleBytes u32 21 0`. -/
def checkedTupleOkArgs : List Value := [.scalar ⟨10, 4⟩, .scalar ⟨3, 4⟩]
def checkedTupleOkS0 : MachineState :=
  initMachineState checkedTupleU32 checkedTupleOkArgs
def checkedTupleOkMInit : Mach :=
  machineWithCtx ctxTupleU32 checkedTupleU32 checkedTupleU32Fn
    checkedTupleOkS0.frame.locals checkedTupleU32Fn.start

theorem checkedTupleOk_anneal_ret :
    ReachesRet (mirCallTree checkedTupleU32 checkedTupleOkArgs)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.aggregate 0 [.scalar ⟨21, 4⟩, .scalar ⟨0, 1⟩], checkedTupleOkS0.memory)) :=
  runA_sound checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleOk_noUB :
    MirNoUBTree (mirCallTree checkedTupleU32 checkedTupleOkArgs) :=
  runA_noUB checkedTupleU32 15 _ _ _ rfl

theorem checkedTupleOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n checkedTupleOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocTupleU32 with data := tupleBytes u32 21 0 } ∧
      m'.threads = [thread1 ctxTupleU32 [{ callerFrameTupleU32 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret checkedTupleU32_inFragment checkedTupleU32_translate ctxTupleU32
      (ctxTupleU32_ok rfl) checkedTupleOkArgs (by decide) checkedTupleOkMInit
      rfl rfl rfl checkedTupleOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [checkedTupleU32] at hd; subst hd
  simp [retPtr, ctxTupleU32] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxTupleU32] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
theorem checkedTupleOk_minirust_direct :
    (Interp.steps 9 checkedTupleOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocTupleU32 with data := tupleBytes u32 21 0 }, [1]) := rfl

/-! ### Reading `.0` or `.1` from an uninitialized `(u32, bool)` tuple local -/

theorem ctxTupleU32_ok1 {body : CapturedMir}
    (h : body.localDecls = [u32BoolTupleDecl]) : CtxOk body ctxTupleU32 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [u32BoolTupleDecl, u32BoolTupleTyW, itOf_u32BoolTuple, tyOf_u32BoolTuple]; decide
    | _ + 1, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocTupleU32, rfl, rfl, rfl, rfl, rfl, by rw [u32BoolTupleDecl, u32BoolTupleTyW, itOf_u32BoolTuple]; decide⟩

/-- MIR of `fn uninit_tuple_field0() -> (u32, bool)` whose entry block reads
`_0.0` from the uninitialized `(u32, bool)` return place `_0`
(`_0 = AddWithOverflow(copy (_0.0), const 1u32)`), raising UB in both Anneal and
MiniRust. -/
def uninitTupleField0 : CapturedMir where
  defPath := "witness::uninit_tuple_field0"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .addWithOverflow (.copy (field0U32 0)) (constU32 1)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem uninitTupleField0_inFragment : inFragment uninitTupleField0 = true := by decide

def uninitTupleField0Fn : Gen.Function where
  locals := ⟨[(localName 0, intBoolTupleTy u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.IntWithOverflow .Add)
          (.Load (.Field (.Local (localName 0)) 0))
          (.Constant (.Int 1) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem uninitTupleField0_translate : translateFn uninitTupleField0 = some uninitTupleField0Fn := rfl

def uninitTupleField0S0 : MachineState := initMachineState uninitTupleField0 []
def uninitTupleField0MInit : Mach :=
  machineWithCtx ctxTupleU32 uninitTupleField0 uninitTupleField0Fn
    uninitTupleField0S0.frame.locals uninitTupleField0Fn.start

theorem uninitTupleField0_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitTupleField0 []) tr u ∧ FaultNow u :=
  faultsA_sound uninitTupleField0 3 _ (by decide)

theorem uninitTupleField0_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitTupleField0MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitTupleField0_anneal_ub
  exact mirCall_ub uninitTupleField0_inFragment uninitTupleField0_translate ctxTupleU32
    (ctxTupleU32_ok1 rfl) [] (by decide) uninitTupleField0MInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitTupleField0_minirust_direct :
    Interp.steps 2 uninitTupleField0MInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

theorem uninitTupleField0_converse_error :
    (∃ msg, Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree uninitTupleField0 []) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 2 ∧ Interp.steps k uninitTupleField0MInit = .ok mRet ∧
      ReturnRel uninitTupleField0 ctxTupleU32 s' v mRet ∧
      ReachesRet (mirCallTree uninitTupleField0 []) tr (.normal (v, mem))) :=
  mirCall_steps_error uninitTupleField0_inFragment uninitTupleField0_translate ctxTupleU32
    (ctxTupleU32_ok1 rfl) [] (by decide) uninitTupleField0MInit rfl rfl rfl
    uninitTupleField0_minirust_direct

/-- MIR of `fn uninit_tuple_field1() -> (u32, bool)` whose entry block switches
on `_0.1` (at offset `4`) from the uninitialized `(u32, bool)` return place
`_0`, raising UB in both Anneal and MiniRust. -/
def uninitTupleField1 : CapturedMir where
  defPath := "witness::uninit_tuple_field1"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32BoolTupleDecl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (field1 0)) { branches := [(0, 1)], otherwise := 1 }),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem uninitTupleField1_inFragment : inFragment uninitTupleField1 = true := by decide

def uninitTupleField1Fn : Gen.Function where
  locals := ⟨[(localName 0, intBoolTupleTy u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[],
      .Switch
        (.UnOp (.Cast (.Transmute (.Int u8)))
          (.Load (.Field (.Local (localName 0)) 1)))
        ⟨[(0, bbName 1)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[], .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 2
  implicit_writes := true

theorem uninitTupleField1_translate : translateFn uninitTupleField1 = some uninitTupleField1Fn := rfl

def uninitTupleField1S0 : MachineState := initMachineState uninitTupleField1 []
def uninitTupleField1MInit : Mach :=
  machineWithCtx ctxTupleU32 uninitTupleField1 uninitTupleField1Fn
    uninitTupleField1S0.frame.locals uninitTupleField1Fn.start

theorem uninitTupleField1_anneal_ub :
    ∃ tr u, Reaches (mirCallTree uninitTupleField1 []) tr u ∧ FaultNow u :=
  faultsA_sound uninitTupleField1 3 _ (by decide)

theorem uninitTupleField1_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n uninitTupleField1MInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := uninitTupleField1_anneal_ub
  exact mirCall_ub uninitTupleField1_inFragment uninitTupleField1_translate ctxTupleU32
    (ctxTupleU32_ok1 rfl) [] (by decide) uninitTupleField1MInit rfl rfl rfl hr hf

set_option maxRecDepth 8192 in
theorem uninitTupleField1_minirust_direct :
    Interp.steps 2 uninitTupleField1MInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

theorem uninitTupleField1_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen uninitTupleField1 + n) uninitTupleField1MInit = .ok m' ∧
      StateRel uninitTupleField1 uninitTupleField1Fn ctxTupleU32 s' m' ∧
      Reaches (mirCallTree uninitTupleField1 []) tr
        (mirTree uninitTupleField1 s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen uninitTupleField1 + n ∧
      Interp.steps k uninitTupleField1MInit = .ok mRet ∧
      ReturnRel uninitTupleField1 ctxTupleU32 s' v mRet ∧
      ReachesRet (mirCallTree uninitTupleField1 []) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen uninitTupleField1 + n) uninitTupleField1MInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree uninitTupleField1 []) tr u ∧ FaultNow u) :=
  mirCall_outcome uninitTupleField1_inFragment uninitTupleField1_translate ctxTupleU32
    (ctxTupleU32_ok1 rfl) [] (by decide) uninitTupleField1MInit rfl rfl rfl n

/-! ### Ground truth for `IntType::with_overflow`, `BinOpIntWithOverflow`, `ValueExpr::Tuple`, and `PlaceExpr::Field` -/

/-- `IntType::with_overflow` layout on `i8` (size `2`, align `1`, no trailing
padding) and on `u32` (size `8`, align `4`, field `0` at offset `0`, field `1`
at offset `4`, and `3` trailing `AbstractByte::Uninit` padding bytes). -/
theorem withOverflow_i8_layout :
    IntType.with_overflow i8 = .ok (intBoolTupleTy i8) ∧
      Type.layout (intBoolTupleTy i8) = .ok (.Sized ⟨2⟩ ⟨1⟩) := ⟨rfl, rfl⟩

theorem withOverflow_u32_layout :
    IntType.with_overflow u32 = .ok (intBoolTupleTy u32) ∧
      Type.layout (intBoolTupleTy u32) = .ok (.Sized ⟨8⟩ ⟨4⟩) ∧
      Type.encode (intBoolTupleTy u32) (.Tuple [.Int 0x01020304, .Bool true]) =
        .ok [.Init 4 none, .Init 3 none, .Init 2 none, .Init 1 none,
             .Init 1 none, .Uninit, .Uninit, .Uninit] := ⟨rfl, rfl, rfl⟩

/-- `TupleHeadLayout::full_size_and_align` and `LayoutStrategy::compute_size_and_align`
handle both `Sized` (`tail = none`) and `Unsized` (`Slice` / `TraitObject`) layouts. -/
theorem tupleHeadLayout_full_sized_and_slice :
    TupleHeadLayout.full_size_and_align ⟨⟨5⟩, ⟨4⟩, none⟩ ⟨0⟩ ⟨1⟩ = (⟨8⟩, ⟨4⟩) ∧
      TupleHeadLayout.full_size_and_align ⟨⟨5⟩, ⟨4⟩, some ⟨2⟩⟩ ⟨6⟩ ⟨2⟩ = (⟨12⟩, ⟨4⟩) ∧
      LayoutStrategy.compute_size_and_align (vtableLookup checkedTupleOkMInit)
        (.Slice ⟨2⟩ ⟨2⟩) (some (.ElementCount 3)) = .ok (⟨6⟩, ⟨2⟩) := ⟨rfl, rfl, rfl⟩

/-- `TupleHeadLayout::{capped_tail_align, tail_offset}` when `packed_align`
genuinely caps `tail_align` (`min 4 1 = 1`, placing the tail at offset `5`
instead of `8`), and `LayoutStrategy::compute_size_and_align` on `Tuple`,
`TraitObject`, mismatched pointer metadata (`specPanic`), and negative slice
count (`specPanic`). -/
theorem cappedTailAlign_and_computeSizeAndAlign_all_branches :
    TupleHeadLayout.capped_tail_align ⟨⟨5⟩, ⟨1⟩, some ⟨1⟩⟩ ⟨4⟩ = ⟨1⟩ ∧
    TupleHeadLayout.tail_offset ⟨⟨5⟩, ⟨1⟩, some ⟨1⟩⟩ ⟨4⟩ = ⟨5⟩ ∧
    TupleHeadLayout.tail_offset ⟨⟨5⟩, ⟨1⟩, none⟩ ⟨4⟩ = ⟨8⟩ ∧
    LayoutStrategy.compute_size_and_align (vtableLookup checkedTupleOkMInit)
      (.Tuple ⟨⟨5⟩, ⟨4⟩, none⟩ (.Slice ⟨2⟩ ⟨2⟩)) (some (.ElementCount 3)) =
      .ok (⟨12⟩, ⟨4⟩) ∧
    LayoutStrategy.compute_size_and_align
      (fun _ : Ptr => .ok { trait_name := ⟨⟨0⟩⟩, size := ⟨24⟩, align := ⟨8⟩, cells := [], methods := ⟨[]⟩ })
      (.TraitObject ⟨⟨0⟩⟩)
      (some (.VTablePointer { addr := 64, provenance := none })) =
      .ok (⟨24⟩, ⟨8⟩) ∧
    LayoutStrategy.compute_size_and_align (vtableLookup checkedTupleOkMInit)
      (.Sized ⟨4⟩ ⟨4⟩) (some (.ElementCount 1)) =
      .error (.specPanic "pointer meta data does not match type") ∧
    LayoutStrategy.compute_size_and_align (vtableLookup checkedTupleOkMInit)
      (.Slice ⟨2⟩ ⟨2⟩) (some (.ElementCount (-1))) =
      .error (.specPanic "Size::from_bytes(count * elem_size.bytes()).unwrap()") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Direct ground-truth evaluations of `evalBinOp (.IntWithOverflow ..)` on
`INT_MAX + 1`, `INT_MIN - 1`, `UINT_MAX + 1`, `0 - 1`, and signed/unsigned
multiplication overflow. -/
theorem evalBinOp_addWithOverflow_i8_max :
    evalBinOp (.IntWithOverflow .Add) (.Int 127, .Int i8) (.Int 1, .Int i8) =
      .ok (.Tuple [.Int (-128), .Bool true], intBoolTupleTy i8) := rfl

theorem evalBinOp_subWithOverflow_i8_min :
    evalBinOp (.IntWithOverflow .Sub) (.Int (-128), .Int i8) (.Int 1, .Int i8) =
      .ok (.Tuple [.Int 127, .Bool true], intBoolTupleTy i8) := rfl

theorem evalBinOp_addWithOverflow_u32_max :
    evalBinOp (.IntWithOverflow .Add) (.Int 4294967295, .Int u32) (.Int 1, .Int u32) =
      .ok (.Tuple [.Int 0, .Bool true], intBoolTupleTy u32) := rfl

theorem evalBinOp_subWithOverflow_u32_zero :
    evalBinOp (.IntWithOverflow .Sub) (.Int 0, .Int u32) (.Int 1, .Int u32) =
      .ok (.Tuple [.Int 4294967295, .Bool true], intBoolTupleTy u32) := rfl

theorem evalBinOp_mulWithOverflow_i8_min :
    evalBinOp (.IntWithOverflow .Mul) (.Int (-128), .Int i8) (.Int (-1), .Int i8) =
      .ok (.Tuple [.Int (-128), .Bool true], intBoolTupleTy i8) := rfl

theorem evalBinOp_mulWithOverflow_u32 :
    evalBinOp (.IntWithOverflow .Mul) (.Int 65536, .Int u32) (.Int 65536, .Int u32) =
      .ok (.Tuple [.Int 0, .Bool true], intBoolTupleTy u32) := rfl

/-- `ptrOffsetInbounds` offsets a valid pointer within its live allocation and
rejects out-of-bounds or negative offsets with UB, and `evalValue` / `evalPlace`
evaluate `ValueExpr::Tuple` and `PlaceExpr::Field` on `(u32, bool)`. -/
theorem ptrOffsetInbounds_ok_and_oob :
    ptrOffsetInbounds checkedTupleOkMInit
      { addr := 384, provenance := some (⟨3⟩, ()) } 4 =
      .ok { addr := 388, provenance := some (⟨3⟩, ()) } ∧
    ptrOffsetInbounds checkedTupleOkMInit
      { addr := 384, provenance := some (⟨3⟩, ()) } 9 =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    ptrOffsetInbounds checkedTupleOkMInit
      { addr := 384, provenance := some (⟨3⟩, ()) } (-1) =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") := ⟨rfl, rfl, rfl⟩

theorem evalValue_tuple_and_evalPlace_field :
    evalValue checkedTupleOkMInit
      (.Tuple [.Constant (.Int 42) (.Int u32), .Constant (.Bool true) .Bool]
        (intBoolTupleTy u32)) =
      .ok ((.Tuple [.Int 42, .Bool true], intBoolTupleTy u32), checkedTupleOkMInit) ∧
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 0)) 0) =
      .ok (({ ptr := { thin_pointer := { addr := 128, provenance := some (⟨1⟩, ()) }, metadata := none },
              aligned := true }, .Int u32), checkedTupleOkMInit) ∧
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 0)) 1) =
      .ok (({ ptr := { thin_pointer := { addr := 132, provenance := some (⟨1⟩, ()) }, metadata := none },
              aligned := true }, .Bool), checkedTupleOkMInit) := ⟨rfl, rfl, rfl⟩

/-- `evalBinOp (.IntWithOverflow ..)` on a non-integer operand and `evalPlace (.Field ..)`
on an out-of-range field index, a missing unsized tail, or a non-projectable
type raise the exact upstream `specPanic`s from `spec/lang/step/{operators,expressions}.md`. -/
theorem evalBinOp_intWithOverflow_nonInt_panics :
    evalBinOp (.IntWithOverflow .Add) (.Bool true, .Bool) (.Bool false, .Bool) =
      .error (.specPanic "non-integer input to integer operation") := rfl

theorem evalPlace_field_panics :
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 0)) 2) =
      .error (.specPanic "field projection to non-existing unsized tail") ∧
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 0)) 3) =
      .error (.specPanic "field projection to invalid field") ∧
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 0)) (-1)) =
      .error (.specPanic "field projection to invalid field") ∧
    evalPlace checkedTupleOkMInit (.Field (.Local (localName 1)) 0) =
      .error (.specPanic "field projection on non-projectable type") := ⟨rfl, rfl, rfl, rfl⟩

/-- `IntType::with_overflow` and `evalBinOp (.IntWithOverflow ..)` across the
remaining integer widths (`u8`, `i16`, `u16`, `i32`, `i64`/`isize`,
`u64`/`usize`, `i128`, `u128`), including 16-byte `(i64, bool)` (`7` trailing
padding bytes) and 32-byte `(u128, bool)` (`15` trailing padding bytes). -/
def i16W : Gen.IntType := ⟨.Signed, ⟨2⟩⟩
def u16W : Gen.IntType := ⟨.Unsigned, ⟨2⟩⟩
def i32W : Gen.IntType := ⟨.Signed, ⟨4⟩⟩
def i64W : Gen.IntType := ⟨.Signed, ⟨8⟩⟩
def u64W : Gen.IntType := ⟨.Unsigned, ⟨8⟩⟩
def i128W : Gen.IntType := ⟨.Signed, ⟨16⟩⟩
def u128W : Gen.IntType := ⟨.Unsigned, ⟨16⟩⟩

theorem evalBinOp_withOverflow_all_widths :
    Type.layout (intBoolTupleTy i64W) = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    Type.layout (intBoolTupleTy u128W) = .ok (.Sized ⟨32⟩ ⟨16⟩) ∧
    evalBinOp (.IntWithOverflow .Add) (.Int 255, .Int u8Ty) (.Int 1, .Int u8Ty) =
      .ok (.Tuple [.Int 0, .Bool true], intBoolTupleTy u8Ty) ∧
    evalBinOp (.IntWithOverflow .Sub) (.Int (-32768), .Int i16W) (.Int 1, .Int i16W) =
      .ok (.Tuple [.Int 32767, .Bool true], intBoolTupleTy i16W) ∧
    evalBinOp (.IntWithOverflow .Add) (.Int 65535, .Int u16W) (.Int 1, .Int u16W) =
      .ok (.Tuple [.Int 0, .Bool true], intBoolTupleTy u16W) ∧
    evalBinOp (.IntWithOverflow .Add) (.Int 2147483647, .Int i32W) (.Int 1, .Int i32W) =
      .ok (.Tuple [.Int (-2147483648), .Bool true], intBoolTupleTy i32W) ∧
    evalBinOp (.IntWithOverflow .Sub)
      (.Int (-9223372036854775808), .Int i64W) (.Int 1, .Int i64W) =
      .ok (.Tuple [.Int 9223372036854775807, .Bool true], intBoolTupleTy i64W) ∧
    evalBinOp (.IntWithOverflow .Add)
      (.Int 18446744073709551615, .Int u64W) (.Int 1, .Int u64W) =
      .ok (.Tuple [.Int 0, .Bool true], intBoolTupleTy u64W) ∧
    evalBinOp (.IntWithOverflow .Sub)
      (.Int (-(2 ^ 127)), .Int i128W) (.Int 1, .Int i128W) =
      .ok (.Tuple [.Int (2 ^ 127 - 1), .Bool true], intBoolTupleTy i128W) ∧
    evalBinOp (.IntWithOverflow .Sub)
      (.Int 0, .Int u128W) (.Int 1, .Int u128W) =
      .ok (.Tuple [.Int (2 ^ 128 - 1), .Bool true], intBoolTupleTy u128W) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `evalPlace (.Field ..)` on `Type::Union` (`unionPaddedTy`, projecting field
`0` at offset `0` with type `.Int i8` and field `1` at offset `2` with type
`.Bool`) and the `offset <= self.compute_size(...)` assertion `specPanic` when a
malformed tuple's field offset (`16`) exceeds the tuple's head size (`8`). -/
def unionFieldTestMach : Mach :=
  machineWithCtx ctxTupleU32 checkedTupleU32
    { checkedTupleU32Fn with
      locals := ⟨[(localName 0, unionPaddedTy),
                  (localName 1, .Tuple [(⟨16⟩, .Int u32)] ⟨⟨8⟩, ⟨4⟩, none⟩ none)]⟩ }
    checkedTupleOkS0.frame.locals (bbName 0)

theorem evalPlace_field_union_and_offset_panic :
    evalPlace unionFieldTestMach (.Field (.Local (localName 0)) 0) =
      .ok (({ ptr := { thin_pointer := { addr := 128, provenance := some (⟨1⟩, ()) }, metadata := none },
              aligned := true }, .Int i8), unionFieldTestMach) ∧
    evalPlace unionFieldTestMach (.Field (.Local (localName 0)) 1) =
      .ok (({ ptr := { thin_pointer := { addr := 130, provenance := some (⟨1⟩, ()) }, metadata := none },
              aligned := true }, .Bool), unionFieldTestMach) ∧
    evalPlace unionFieldTestMach (.Field (.Local (localName 1)) 0) =
      .error (.specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)") :=
  ⟨rfl, rfl, rfl⟩

/-! ## Temporaries, storage markers, `move`, `Deinit`, and the init block

MR-1.3 bodies with temporaries beyond the arguments. `tempMove` exercises
`StorageLive`/`StorageDead` of `u32` and `bool` temporaries, a root `move` in
a `BinaryOp` operand, in a `Use`, and in a `switchInt` discriminant (Anneal
de-initializes the moved-from local; MiniRust's `move` is a plain load, which
`StaleOk` reconciles), `Deinit` of a moved-from local, and a temporary without
storage markers that `minimize`'s init block allocates (`_4`, never
mentioned). Its first-fit stack addresses (`allocCandidate`) show `StorageLive`
reusing the address that `StorageDead` released. `deadRead` reads a local
after `StorageDead` (UB in both models), and `moveReuse` is a body that
`movesOk` rejects because it reads a local after moving out of it. -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn temp_move(x: u32) -> u32 {
    let y = (x + 1) * 2;
    if y == 8 { 100 } else { y }
}
```
with the temporaries spelled out:
```text
bb0: StorageLive(_2); _2 = Add(copy _1, const 1_u32);
     StorageLive(_3); _3 = Mul(move _2, const 2_u32); StorageDead(_2);
     _0 = move _3; Deinit(_3); StorageDead(_3);
     StorageLive(_5); _5 = Eq(copy _0, const 8_u32);
     switchInt(move _5) -> [0: bb1, otherwise: bb2]
bb1: StorageDead(_5); return
bb2: StorageDead(_5); _0 = const 100_u32; return
```
`_4: u32` has no storage markers and no uses. -/
def tempMove : CapturedMir where
  defPath := "witness::temp_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl, u32Decl, u32Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.binaryOp .add (.copy (local_ 1)) (constU32 1))),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.binaryOp .mul (.move (local_ 2)) (constU32 2))),
        mkStmt (.storageDead 2),
        mkStmt (.assign (local_ 0) (.use (.move (local_ 3)))),
        mkStmt (.deinit (local_ 3)),
        mkStmt (.storageDead 3),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.binaryOp .eq (.copy (local_ 0)) (constU32 8)))],
      terminator := mkTerm (.switchInt (.move (local_ 5)) { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [mkStmt (.storageDead 5)], terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.storageDead 5), mkStmt (.assign (local_ 0) (.use (constU32 100)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem tempMove_inFragment : inFragment tempMove = true := by decide

/-- `_4` is the only temporary without storage markers. -/
theorem tempMove_alwaysLive : alwaysStorageLiveLocals tempMove = [4] := by decide

/-- The MiniRust function `minimize` produces for `tempMove`, spelled out:
`move` operands translate like `copy` operands (`Load`), and the init block
`bb3` allocates `_4`. -/
def tempMoveFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, .Int u32), (localName 4, .Int u32), (localName 5, .Bool)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Add) (.Load (.Local (localName 1))) (.Constant (.Int 1) (.Int u32))),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Mul) (.Load (.Local (localName 2))) (.Constant (.Int 2) (.Int u32))),
      .StorageDead (localName 2),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 3))),
      .Deinit (.Local (localName 3)),
      .StorageDead (localName 3),
      .StorageLive (localName 5),
      .Assign (.Local (localName 5))
        (.BinOp (.Rel .Eq) (.Load (.Local (localName 0))) (.Constant (.Int 8) (.Int u32)))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 5))))
        ⟨[(0, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[.StorageDead (localName 5)], .Return, .Regular⟩),
    (bbName 2, ⟨[.StorageDead (localName 5),
      .Assign (.Local (localName 0)) (.Constant (.Int 100) (.Int u32))], .Return, .Regular⟩),
    (bbName 3, ⟨[.StorageLive (localName 4)], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem tempMove_translate : translateFn tempMove = some tempMoveFn := rfl

theorem ctx0_ok_tempMove : CtxOk tempMove ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [tempMove] at hd; subst hd; decide
    | 1, _, hd => simp [tempMove] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [tempMove] at hi
  ret := by
    intro d hd
    simp [tempMove] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-! ### `temp_move(3)`: `y == 8`, returns `100` -/

def tempMove3S0 : MachineState := initMachineState tempMove [.scalar ⟨3, 4⟩]
def tempMove3MInit : Mach := machine tempMove tempMoveFn tempMove3S0.frame.locals tempMoveFn.start

/-- The init block takes two MiniRust steps: `StorageLive(_4)` and
`Goto(bb0)`. -/
theorem tempMove_initLen : initLen tempMove = 2 := by decide

def tempMove3Trace : List (Event MirEffect) := [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]

theorem tempMove3_anneal_ret :
    ReachesRet (mirTree tempMove tempMove3S0) tempMove3Trace
      (.normal (.scalar ⟨100, 4⟩, tempMove3S0.memory)) :=
  runA_sound tempMove 30 _ _ _ rfl

theorem tempMove3_noUB : MirNoUBTree (mirCallTree tempMove [.scalar ⟨3, 4⟩]) :=
  runA_noUB tempMove 30 _ _ _ rfl

theorem tempMove3_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n tempMove3MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 100 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret tempMove_inFragment tempMove_translate ctx0 ctx0_ok_tempMove [.scalar ⟨3, 4⟩]
      (by decide) tempMove3MInit rfl rfl rfl tempMove3_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [tempMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- The same return, computed directly (16 MiniRust steps: the two init-block
steps and one per Anneal step). Every callee allocation is dead afterwards,
including the init block's `_4`; the first-fit addresses show `_4` at
`2^32`, `_2` at `2 * 2^32`, `_3` at `3 * 2^32`, and `_5` reusing `2 * 2^32`
after `StorageDead(_2)`. -/
theorem tempMove3_minirust_direct :
    (Interp.steps 16 tempMove3MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live), m.mem.memory.allocations.map (·.addr))) =
      some (some { retAlloc with data := scalarBytes u32 100 }, [1],
        [true, false, false, false, false, false, false],
        [64, 128, 256, 2 ^ 32, 2 * 2 ^ 32, 3 * 2 ^ 32, 2 * 2 ^ 32]) := by
  decide +kernel

/-! ### `temp_move(2)`: `y == 6`, returns `6` -/

def tempMove2S0 : MachineState := initMachineState tempMove [.scalar ⟨2, 4⟩]
def tempMove2MInit : Mach := machine tempMove tempMoveFn tempMove2S0.frame.locals tempMoveFn.start

def tempMove2Trace : List (Event MirEffect) := [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]

theorem tempMove2_anneal_ret :
    ReachesRet (mirTree tempMove tempMove2S0) tempMove2Trace
      (.normal (.scalar ⟨6, 4⟩, tempMove2S0.memory)) :=
  runA_sound tempMove 30 _ _ _ rfl

theorem tempMove2_noUB : MirNoUBTree (mirCallTree tempMove [.scalar ⟨2, 4⟩]) :=
  runA_noUB tempMove 30 _ _ _ rfl

theorem tempMove3_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen tempMove + n) tempMove3MInit = .ok m' ∧
      StateRel tempMove tempMoveFn ctx0 s' m' ∧
      Reaches (mirCallTree tempMove [.scalar ⟨3, 4⟩]) tr (mirTree tempMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen tempMove + n ∧
      Interp.steps k tempMove3MInit = .ok mRet ∧
      ReturnRel tempMove ctx0 s' v mRet ∧
      ReachesRet (mirCallTree tempMove [.scalar ⟨3, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress tempMove_inFragment tempMove_translate ctx0 ctx0_ok_tempMove [.scalar ⟨3, 4⟩]
    (by decide) tempMove3MInit rfl rfl rfl tempMove3_noUB n

theorem tempMove2_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n tempMove2MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret tempMove_inFragment tempMove_translate ctx0 ctx0_ok_tempMove [.scalar ⟨2, 4⟩]
      (by decide) tempMove2MInit rfl rfl rfl tempMove2_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [tempMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem tempMove2_minirust_direct :
    (Interp.steps 15 tempMove2MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live))) =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1],
        [true, false, false, false, false, false, false]) := by
  decide +kernel

/-! ### Reading a local after `StorageDead` -/

/-- MIR of `StorageLive(_1); _1 = const 5_u32; StorageDead(_1); _0 = copy _1;
return`, which reads the dead temporary `_1`. -/
def deadRead : CapturedMir where
  defPath := "witness::dead_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (constU32 5))),
        mkStmt (.storageDead 1),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem deadRead_inFragment : inFragment deadRead = true := by decide

def deadReadFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .Assign (.Local (localName 1)) (.Constant (.Int 5) (.Int u32)),
      .StorageDead (localName 1),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deadRead_translate : translateFn deadRead = some deadReadFn := rfl

def deadReadS0 : MachineState := initMachineState deadRead []
def deadReadMInit : Mach := machine deadRead deadReadFn deadReadS0.frame.locals deadReadFn.start

theorem deadRead_anneal_ub : ∃ tr u, Reaches (mirTree deadRead deadReadS0) tr u ∧ FaultNow u :=
  faultsA_sound deadRead 10 _ (by decide)

theorem deadRead_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n deadReadMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := deadRead_anneal_ub
  exact mirCall_ub deadRead_inFragment deadRead_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadReadMInit rfl rfl rfl hr hf

/-- Direct computation: the fifth MiniRust step (the init block's `Goto`, then
three statements) raises the UB of loading a dead local. -/
theorem deadRead_minirust_direct :
    (match Interp.steps 5 deadReadMInit with
      | .error (.ub msg) => some msg
      | _ => none) = some "access to a dead local" := by
  decide +kernel

theorem deadRead_steps5_ub :
    Interp.steps 5 deadReadMInit = .error (.ub "access to a dead local") := by
  have h := deadRead_minirust_direct
  revert h
  cases Interp.steps 5 deadReadMInit with
  | ok _ => simp
  | error e => cases e <;> simp

theorem deadRead_converse_error :
    (∃ msg, Stop.ub "access to a dead local" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree deadRead []) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 5 ∧ Interp.steps k deadReadMInit = .ok mRet ∧
      ReturnRel deadRead ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadRead []) tr (.normal (v, mem))) :=
  mirCall_steps_error deadRead_inFragment deadRead_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadReadMInit rfl rfl rfl deadRead_steps5_ub

theorem deadRead_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen deadRead + n) deadReadMInit = .ok m' ∧
      StateRel deadRead deadReadFn ctx0 s' m' ∧
      Reaches (mirCallTree deadRead []) tr (mirTree deadRead s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen deadRead + n ∧
      Interp.steps k deadReadMInit = .ok mRet ∧
      ReturnRel deadRead ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadRead []) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen deadRead + n) deadReadMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree deadRead []) tr u ∧ FaultNow u) :=
  mirCall_outcome deadRead_inFragment deadRead_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadReadMInit rfl rfl rfl n

/-! ### A body that `movesOk` rejects -/

/-- MIR of `StorageLive(_2); _2 = copy _1; _0 = move _2; _0 = copy _2;
StorageDead(_2); return` for `fn(u32) -> u32`: Anneal de-initializes `_2` at
the `move` (so the second read is UB), while MiniRust's `move` is a plain load
(so the second read succeeds). `movesOk` rejects the body, so the
correspondence theorem claims nothing about it. -/
def moveReuse : CapturedMir where
  defPath := "witness::move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 0) (.use (.move (local_ 2)))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 2)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem moveReuse_movesOk : movesOk moveReuse = false := by decide

theorem moveReuse_not_inFragment : inFragment moveReuse = false := by decide

/-- The two models indeed disagree on `moveReuse(7)`: Anneal faults, while
MiniRust's run of the translated body returns `7`. -/
def moveReuseFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.Load (.Local (localName 1))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 2))),
      .StorageDead (localName 2)], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem moveReuse_translate : translateFn moveReuse = some moveReuseFn := rfl

def moveReuse7S0 : MachineState := initMachineState moveReuse [.scalar ⟨7, 4⟩]

theorem moveReuse7_anneal_ub :
    ∃ tr u, Reaches (mirTree moveReuse moveReuse7S0) tr u ∧ FaultNow u :=
  faultsA_sound moveReuse 10 _ (by decide)

theorem moveReuse7_minirust_direct :
    (Interp.steps 7 (machine moveReuse moveReuseFn moveReuse7S0.frame.locals
        moveReuseFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 7 }, [1]) := by
  decide +kernel

/-! ### Cross-block moves, argument moves, projected tuple moves, live re-allocation, and idempotent `StorageDead`

`crossBlockMove` exercises the CFG-aware `movesOk` dataflow analysis across
`Goto` and `SwitchInt` edges:
* moving the incoming function argument `_1` in `bb0`
  (`_2 = AddWithOverflow(move _1, const 10_u32)`), which a block-insensitive
  `movedLocals` check would reject;
* projected tuple moves `move (_2.0)` (in `Use`) and `move (_2.1)` (as a `bool`
  `SwitchInt` discriminant), which leave `_2: (u32, bool)` initialized in both
  models (`opMoved (.move ⟨2, [.field ..]⟩) = none`);
* carrying live temporaries `_2` and `_3` initialized in `bb0` across
  `Goto(bb1)` and `SwitchInt -> [0: bb2, otherwise: bb3]` before moving `_3` in
  `bb1` and `bb2`;
* calling `StorageLive(_1)` and `StorageLive(_3)` on already-live locals without
  an intervening `StorageDead`, exercising `StackFrame::storage_live`'s initial
  `self.storage_dead(mem, local)?` deallocation and clearing their moved marks;
* `Deinit(_2)` on a `(u32, bool)` 2-tuple local;
* idempotent `StorageDead(_2)` on an already-dead local
  (`if let Some(ptr) = self.locals.remove(local)`). -/
def crossBlockMove : CapturedMir where
  defPath := "witness::cross_block_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32BoolTupleDecl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.binaryOp .addWithOverflow (.move (local_ 1)) (constU32 10))),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.use (.move (field0U32 2))))],
      terminator := mkTerm (.goto 1),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (.move (local_ 3)))),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.binaryOp .add (.move (local_ 1)) (constU32 5)))],
      terminator := mkTerm (.switchInt (.move (field1 2)) { branches := [(0, 2)], otherwise := 3 }),
      isCleanup := false },
    { statements := [
        mkStmt (.deinit (local_ 2)),
        mkStmt (.storageDead 2),
        mkStmt (.storageDead 2),
        mkStmt (.assign (local_ 0) (.use (.move (local_ 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_,
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 2),
        mkStmt (.storageDead 3),
        mkStmt (.assign (local_ 0) (.use (constU32 0)))],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem crossBlockMove_inFragment : inFragment crossBlockMove = true := by decide

/-- Forward CFG dataflow `movedAtEntry` for `crossBlockMove`: `bb0` starts with
`[]`, while `bb1`, `bb2`, and `bb3` have `[1]` moved out on entry (`_3` is
initialized in `bb0`, moved in `bb1`, and re-allocated/initialized in `bb1`
before reaching `bb2`). -/
theorem crossBlockMove_movedAtEntry :
    [0, 1, 2, 3].map (movedAtEntry crossBlockMove) = [[], [1], [1], [1]] := by decide

def crossBlockMoveFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, intBoolTupleTy u32), (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2))
        (.BinOp (.IntWithOverflow .Add) (.Load (.Local (localName 1))) (.Constant (.Int 10) (.Int u32))),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3)) (.Load (.Field (.Local (localName 2)) 0))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .StorageLive (localName 1),
      .Assign (.Local (localName 1)) (.Load (.Local (localName 3))),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Add) (.Load (.Local (localName 1))) (.Constant (.Int 5) (.Int u32)))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Field (.Local (localName 2)) 1)))
        ⟨[(0, bbName 2)]⟩ (bbName 3), .Regular⟩),
    (bbName 2, ⟨[
      .Deinit (.Local (localName 2)),
      .StorageDead (localName 2),
      .StorageDead (localName 2),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 3))),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 3, ⟨[
      .StorageDead (localName 2),
      .StorageDead (localName 3),
      .Assign (.Local (localName 0)) (.Constant (.Int 0) (.Int u32))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem crossBlockMove_translate : translateFn crossBlockMove = some crossBlockMoveFn := rfl

theorem ctx0_ok_crossBlockMove : CtxOk crossBlockMove ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [crossBlockMove] at hd; subst hd; decide
    | 1, _, hd => simp [crossBlockMove] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [crossBlockMove] at hi
  ret := by
    intro d hd
    simp [crossBlockMove] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def crossBlockMove20S0 : MachineState := initMachineState crossBlockMove [.scalar ⟨20, 4⟩]
def crossBlockMove20MInit : Mach :=
  machine crossBlockMove crossBlockMoveFn crossBlockMove20S0.frame.locals crossBlockMoveFn.start

theorem crossBlockMove20_anneal_ret :
    ReachesRet (mirTree crossBlockMove crossBlockMove20S0)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨35, 4⟩, crossBlockMove20S0.memory)) :=
  runA_sound crossBlockMove 30 _ _ _ rfl

theorem crossBlockMove20_noUB : MirNoUBTree (mirCallTree crossBlockMove [.scalar ⟨20, 4⟩]) :=
  runA_noUB crossBlockMove 30 _ _ _ rfl

theorem crossBlockMove20_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen crossBlockMove + n) crossBlockMove20MInit = .ok m' ∧
      StateRel crossBlockMove crossBlockMoveFn ctx0 s' m' ∧
      Reaches (mirCallTree crossBlockMove [.scalar ⟨20, 4⟩]) tr (mirTree crossBlockMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen crossBlockMove + n ∧
      Interp.steps k crossBlockMove20MInit = .ok mRet ∧
      ReturnRel crossBlockMove ctx0 s' v mRet ∧
      ReachesRet (mirCallTree crossBlockMove [.scalar ⟨20, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress crossBlockMove_inFragment crossBlockMove_translate ctx0 ctx0_ok_crossBlockMove
    [.scalar ⟨20, 4⟩] (by decide) crossBlockMove20MInit rfl rfl rfl crossBlockMove20_noUB n

theorem crossBlockMove20_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n crossBlockMove20MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 35 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret crossBlockMove_inFragment crossBlockMove_translate ctx0 ctx0_ok_crossBlockMove
      [.scalar ⟨20, 4⟩] (by decide) crossBlockMove20MInit rfl rfl rfl crossBlockMove20_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [crossBlockMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem crossBlockMove20_minirust_direct :
    (Interp.steps 17 crossBlockMove20MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live))) =
      some (some { retAlloc with data := scalarBytes u32 35 }, [1],
        [true, false, false, false, false, false, false]) := by
  decide +kernel

def crossBlockMoveOvS0 : MachineState :=
  initMachineState crossBlockMove [.scalar ⟨4294967290, 4⟩]
def crossBlockMoveOvMInit : Mach :=
  machine crossBlockMove crossBlockMoveFn crossBlockMoveOvS0.frame.locals crossBlockMoveFn.start

theorem crossBlockMoveOv_anneal_ret :
    ReachesRet (mirTree crossBlockMove crossBlockMoveOvS0)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 4⟩, crossBlockMoveOvS0.memory)) :=
  runA_sound crossBlockMove 30 _ _ _ rfl

theorem crossBlockMoveOv_noUB :
    MirNoUBTree (mirCallTree crossBlockMove [.scalar ⟨4294967290, 4⟩]) :=
  runA_noUB crossBlockMove 30 _ _ _ rfl

theorem crossBlockMoveOv_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen crossBlockMove + n) crossBlockMoveOvMInit = .ok m' ∧
      StateRel crossBlockMove crossBlockMoveFn ctx0 s' m' ∧
      Reaches (mirCallTree crossBlockMove [.scalar ⟨4294967290, 4⟩]) tr (mirTree crossBlockMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen crossBlockMove + n ∧
      Interp.steps k crossBlockMoveOvMInit = .ok mRet ∧
      ReturnRel crossBlockMove ctx0 s' v mRet ∧
      ReachesRet (mirCallTree crossBlockMove [.scalar ⟨4294967290, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress crossBlockMove_inFragment crossBlockMove_translate ctx0 ctx0_ok_crossBlockMove
    [.scalar ⟨4294967290, 4⟩] (by decide) crossBlockMoveOvMInit rfl rfl rfl crossBlockMoveOv_noUB n

theorem crossBlockMoveOv_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n crossBlockMoveOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 0 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret crossBlockMove_inFragment crossBlockMove_translate ctx0 ctx0_ok_crossBlockMove
      [.scalar ⟨4294967290, 4⟩] (by decide) crossBlockMoveOvMInit rfl rfl rfl
      crossBlockMoveOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [crossBlockMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem crossBlockMoveOv_minirust_direct :
    (Interp.steps 15 crossBlockMoveOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live))) =
      some (some { retAlloc with data := scalarBytes u32 0 }, [1],
        [true, false, false, false, false, false, false]) := by
  decide +kernel

/-! ### Cross-block move-reuse rejected by `movesOk` -/

/-- A 2-block body that moves `_1` in `bb0` (`_0 = move _1; goto bb1`) and reads
`_1` in `bb1` (`_0 = copy _1; return`): `movedAtEntry` propagates `1` across the
`bb0 → bb1` edge and `movesOk` rejects the body. -/
def crossBlockMoveReuse : CapturedMir where
  defPath := "witness::cross_block_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (.move (local_ 1))))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem crossBlockMoveReuse_movesOk :
    movedAtEntry crossBlockMoveReuse 1 = [1] ∧ movesOk crossBlockMoveReuse = false ∧
    inFragment crossBlockMoveReuse = false := by decide

/-! ### A body that `mentionsOk` rejects (`alwaysStorageLiveLocals` gap) -/

/-- MIR of `_1 = const 9_u32; _0 = copy _1; return` for `fn() -> u32` where the
temporary `_1: u32` has no `StorageLive` or `StorageDead` marker in the body
(`alwaysStorageLiveLocals = [1]`): `minimize`'s `initBlock` emits
`StorageLive(_1)` so MiniRust returns `9`, whereas Anneal's `initMachineState`
starts `_1` in `.dead` and faults with UB on `_1 = const 9_u32`. `mentionsOk`
rejects this body. -/
def unmarkedTempAssign : CapturedMir where
  defPath := "witness::unmarked_temp_assign"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.use (constU32 9))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem unmarkedTempAssign_rejected :
    alwaysStorageLiveLocals unmarkedTempAssign = [1] ∧
    mentionsOk unmarkedTempAssign = false ∧
    inFragment unmarkedTempAssign = false := by decide

def unmarkedTempAssignFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1)) (.Constant (.Int 9) (.Int u32)),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[.StorageLive (localName 1)], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem unmarkedTempAssign_translate :
    translateFn unmarkedTempAssign = some unmarkedTempAssignFn := rfl

def unmarkedTempAssignS0 : MachineState := initMachineState unmarkedTempAssign []

theorem unmarkedTempAssign_anneal_ub :
    ∃ tr u, Reaches (mirTree unmarkedTempAssign unmarkedTempAssignS0) tr u ∧ FaultNow u :=
  faultsA_sound unmarkedTempAssign 10 _ (by decide)

theorem unmarkedTempAssign_minirust_direct :
    (Interp.steps 5 (machine unmarkedTempAssign unmarkedTempAssignFn
        unmarkedTempAssignS0.frame.locals unmarkedTempAssignFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 9 }, [1]) := by
  decide +kernel

/-! ### Direct ground-truth checks for `BM.allocate`, `BM.deallocate`, and
`Statement::Deinit` UB paths -/

/-- `BM.allocate` raises `"asking for a too large allocation"` when
`!x86_64.valid_size(size)` (`size.bytes >= 2^63` or `size.bytes < 0`), and
`BM.deallocate` raises each of the six upstream UB diagnostics from
`spec/mem/basic.md` (provenance `None`, double-free of a dead allocation,
non-zero offset from `alloc.addr`, wrong `AllocationKind` formatting both the
allocation's kind and the requested operation kind across all five
`AllocationKind` variants `Stack`, `Heap`, `Global`, `Function`, and `VTable`,
wrong `Size`, and wrong `Align`). -/
theorem bm_allocate_and_deallocate_ub_cases :
    BM.allocate { tempMove3MInit.mem.memory with allocations := [] } .Stack ⟨2 ^ 63⟩ ⟨1⟩ =
      .error (.ub "asking for a too large allocation") ∧
    BM.deallocate tempMove3MInit.mem.memory { addr := 64, provenance := none } .Stack ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating invalid pointer") ∧
    BM.deallocate
      { tempMove3MInit.mem.memory with allocations := [{ retAlloc with live := false }] }
      { addr := 64, provenance := some (⟨0⟩, ()) } .Stack ⟨4⟩ ⟨4⟩ =
      .error (.ub "double-free") ∧
    BM.deallocate tempMove3MInit.mem.memory
      { addr := 65, provenance := some (⟨0⟩, ()) } .Stack ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating with pointer not to the beginning of its allocation") ∧
    BM.deallocate tempMove3MInit.mem.memory
      { addr := 64, provenance := some (⟨0⟩, ()) } .Heap ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating Stack memory with Heap deallocation operation") ∧
    BM.deallocate
      { tempMove3MInit.mem.memory with allocations := [{ retAlloc with kind := .Global }] }
      { addr := 64, provenance := some (⟨0⟩, ()) } .Function ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating Global memory with Function deallocation operation") ∧
    BM.deallocate
      { tempMove3MInit.mem.memory with allocations := [{ retAlloc with kind := .VTable }] }
      { addr := 64, provenance := some (⟨0⟩, ()) } .Stack ⟨4⟩ ⟨4⟩ =
      .error (.ub "deallocating VTable memory with Stack deallocation operation") ∧
    BM.deallocate tempMove3MInit.mem.memory
      { addr := 64, provenance := some (⟨0⟩, ()) } .Stack ⟨8⟩ ⟨4⟩ =
      .error (.ub "deallocating with incorrect size information") ∧
    BM.deallocate tempMove3MInit.mem.memory
      { addr := 64, provenance := some (⟨0⟩, ()) } .Stack ⟨4⟩ ⟨8⟩ =
      .error (.ub "deallocating with incorrect alignment information") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `evalStatement` for `Statement::Deinit` replaces the bytes of a live local
with `AbstractByte.Uninit`, raises `"access to a dead local"` on a dead local,
and raises `"dereferencing pointer outside the bounds of its allocation"` when
`CM.deinit` stores `size` bytes at an out-of-bounds offset in the local's
allocation (while `CM.deinit` with non-unit alignment raises `"store to a
misaligned pointer"`). -/
def misalignedLocalMach : Mach :=
  { tempMove3MInit with
    threads := [thread1 ctx0 [callerFrame,
      { calleeFrameL tempMoveFn ctx0
          ⟨[(localName 0, localPtr ctx0 0),
            (localName 1, { addr := 257, provenance := some (⟨2⟩, ()) })]⟩ 0 0 with
        next_block := tempMoveFn.start }]] }

theorem evalStatement_deinit_ok_dead_and_misaligned :
    (evalStatement tempMove3MInit (.Deinit (.Local (localName 1)))).toOption.bind
        (fun m => m.mem.memory.allocations[2]?.map (·.data)) =
      some [.Uninit, .Uninit, .Uninit, .Uninit] ∧
    evalStatement tempMove3MInit (.Deinit (.Local (localName 2))) =
      .error (.ub "access to a dead local") ∧
    evalStatement misalignedLocalMach (.Deinit (.Local (localName 1))) =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    CM.deinit tempMove3MInit.mem { addr := 257, provenance := some (⟨2⟩, ()) } ⟨4⟩ ⟨4⟩ =
      .error (.ub "store to a misaligned pointer") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Cyclic loop CFG with multi-pass `movesOk` and multi-local `initBlock`

`loopTempMove` computes `n + (n - 1) + .. + 1` in a 4-block cyclic CFG (`bb0`
entry, `bb1` loop header, `bb2` loop body with back-edge `Goto(bb1)`, `bb3`
exit), exercising:
* two heterogeneous unmarked temporaries `_4: u32` and `_5: i8`
  (`alwaysStorageLiveLocals = [4, 5]`, `initLen = 3`);
* multi-pass fixpoint convergence of `iterMovedEntries`: `bb2` moves out of
  `_2` before jumping back to `bb1` (leaving `_2` live across the back-edge),
  Pass 1 adds `2` to `bb1`'s entry set, Pass 2 propagates `2` forward from
  `bb1` into `bb2` and `bb3`, and `StorageLive(_2)` in `bb2` (re-allocating
  already-live `_2`) / idempotent `StorageDead(_2)` in `bb3` clear the mark;
* per-iteration `StorageLive(_3)`, `SwitchInt(move _3)`, `Deinit(_3)`, and
  `StorageDead(_3)` on the `bool` loop-condition temporary `_3`;
* loop-carried root moves `move _0` and `move _1` re-initialized in `bb2`. -/
def loopTempMove : CapturedMir where
  defPath := "witness::loop_temp_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl, boolDecl, u32Decl, i8Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 0)))],
      terminator := mkTerm (.goto 1),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.binaryOp .gt (.copy (local_ 1)) (constU32 0)))],
      terminator := mkTerm (.switchInt (.move (local_ 3)) { branches := [(0, 3)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.deinit (local_ 3)),
        mkStmt (.storageDead 3),
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.binaryOp .add (.move (local_ 0)) (.copy (local_ 1)))),
        mkStmt (.assign (local_ 0) (.use (.move (local_ 2)))),
        mkStmt (.assign (local_ 1) (.binaryOp .sub (.move (local_ 1)) (constU32 1)))],
      terminator := mkTerm (.goto 1),
      isCleanup := false },
    { statements := [
        mkStmt (.deinit (local_ 3)),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem loopTempMove_inFragment : inFragment loopTempMove = true := by decide

theorem loopTempMove_alwaysLive : alwaysStorageLiveLocals loopTempMove = [4, 5] := by decide

theorem loopTempMove_initLen : initLen loopTempMove = 3 := by decide

/-- Pass 1 of `iterMovedEntries` records `2` at `bb1` from the back-edge
`bb2 → bb1` (`[[], [2], [3], [3]]`), and Pass 2 propagates `2` from `bb1` into
`bb2` and `bb3` (`[[], [2], [2, 3], [2, 3]]`), where it stabilizes. -/
theorem loopTempMove_movedAtEntry_multiPass :
    iterMovedEntries 1 loopTempMove.basicBlocks [] = [[], [2], [3], [3]] ∧
    iterMovedEntries 2 loopTempMove.basicBlocks [] = [[], [2], [2, 3], [2, 3]] ∧
    [0, 1, 2, 3].map (movedAtEntry loopTempMove) = [[], [2], [2, 3], [2, 3]] := by decide

def loopTempMoveFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, .Bool), (localName 4, .Int u32), (localName 5, .Int i8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 0) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.Rel .Gt) (.Load (.Local (localName 1))) (.Constant (.Int 0) (.Int u32)))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 3))))
        ⟨[(0, bbName 3)]⟩ (bbName 2), .Regular⟩),
    (bbName 2, ⟨[
      .Deinit (.Local (localName 3)),
      .StorageDead (localName 3),
      .StorageLive (localName 2),
      .Assign (.Local (localName 2))
        (.BinOp (.Int .Add) (.Load (.Local (localName 0))) (.Load (.Local (localName 1)))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 1))) (.Constant (.Int 1) (.Int u32)))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 3, ⟨[
      .Deinit (.Local (localName 3)),
      .StorageDead (localName 3),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[.StorageLive (localName 4), .StorageLive (localName 5)],
      .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem loopTempMove_translate : translateFn loopTempMove = some loopTempMoveFn := rfl

theorem ctx0_ok_loopTempMove : CtxOk loopTempMove ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [loopTempMove] at hd; subst hd; decide
    | 1, _, hd => simp [loopTempMove] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [loopTempMove] at hi
  ret := by
    intro d hd
    simp [loopTempMove] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def loopTempMove3S0 : MachineState := initMachineState loopTempMove [.scalar ⟨3, 4⟩]
def loopTempMove3MInit : Mach :=
  machine loopTempMove loopTempMoveFn loopTempMove3S0.frame.locals loopTempMoveFn.start

def loopTempMove3Trace : List (Event MirEffect) :=
  [1, 1, 1, 0].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

theorem loopTempMove3_anneal_ret :
    ReachesRet (mirTree loopTempMove loopTempMove3S0) loopTempMove3Trace
      (.normal (.scalar ⟨6, 4⟩, loopTempMove3S0.memory)) :=
  runA_sound loopTempMove 50 _ _ _ rfl

theorem loopTempMove3_noUB : MirNoUBTree (mirCallTree loopTempMove [.scalar ⟨3, 4⟩]) :=
  runA_noUB loopTempMove 50 _ _ _ rfl

theorem loopTempMove3_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen loopTempMove + n) loopTempMove3MInit = .ok m' ∧
      StateRel loopTempMove loopTempMoveFn ctx0 s' m' ∧
      Reaches (mirCallTree loopTempMove [.scalar ⟨3, 4⟩]) tr (mirTree loopTempMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen loopTempMove + n ∧
      Interp.steps k loopTempMove3MInit = .ok mRet ∧
      ReturnRel loopTempMove ctx0 s' v mRet ∧
      ReachesRet (mirCallTree loopTempMove [.scalar ⟨3, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress loopTempMove_inFragment loopTempMove_translate ctx0 ctx0_ok_loopTempMove
    [.scalar ⟨3, 4⟩] (by decide) loopTempMove3MInit rfl rfl rfl loopTempMove3_noUB n

theorem loopTempMove3_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n loopTempMove3MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 6 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret loopTempMove_inFragment loopTempMove_translate ctx0 ctx0_ok_loopTempMove
      [.scalar ⟨3, 4⟩] (by decide) loopTempMove3MInit rfl rfl rfl loopTempMove3_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [loopTempMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem loopTempMove3_minirust_direct :
    (Interp.steps 42 loopTempMove3MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.all (fun a => a.addr == 64 || !a.live))) =
      some (some { retAlloc with data := scalarBytes u32 6 }, [1], true) := by
  decide +kernel

def loopTempMove0S0 : MachineState := initMachineState loopTempMove [.scalar ⟨0, 4⟩]
def loopTempMove0MInit : Mach :=
  machine loopTempMove loopTempMoveFn loopTempMove0S0.frame.locals loopTempMoveFn.start

theorem loopTempMove0_anneal_ret :
    ReachesRet (mirTree loopTempMove loopTempMove0S0)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 4⟩, loopTempMove0S0.memory)) :=
  runA_sound loopTempMove 20 _ _ _ rfl

theorem loopTempMove0_noUB : MirNoUBTree (mirCallTree loopTempMove [.scalar ⟨0, 4⟩]) :=
  runA_noUB loopTempMove 20 _ _ _ rfl

theorem loopTempMove0_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen loopTempMove + n) loopTempMove0MInit = .ok m' ∧
      StateRel loopTempMove loopTempMoveFn ctx0 s' m' ∧
      Reaches (mirCallTree loopTempMove [.scalar ⟨0, 4⟩]) tr (mirTree loopTempMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen loopTempMove + n ∧
      Interp.steps k loopTempMove0MInit = .ok mRet ∧
      ReturnRel loopTempMove ctx0 s' v mRet ∧
      ReachesRet (mirCallTree loopTempMove [.scalar ⟨0, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress loopTempMove_inFragment loopTempMove_translate ctx0 ctx0_ok_loopTempMove
    [.scalar ⟨0, 4⟩] (by decide) loopTempMove0MInit rfl rfl rfl loopTempMove0_noUB n

theorem loopTempMove0_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n loopTempMove0MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 0 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret loopTempMove_inFragment loopTempMove_translate ctx0 ctx0_ok_loopTempMove
      [.scalar ⟨0, 4⟩] (by decide) loopTempMove0MInit rfl rfl rfl loopTempMove0_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [loopTempMove] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem loopTempMove0_minirust_direct :
    (Interp.steps 12 loopTempMove0MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live))) =
      some (some { retAlloc with data := scalarBytes u32 0 }, [1],
        [true, false, false, false, false, false]) := by
  decide +kernel

/-! ### Cyclic back-edge move-reuse separating multi-pass from 1-pass -/

/-- `bb0` initializes `_2 = 99`, `bb1` branches to `bb2` or `bb3`, `bb2` moves
`_2` and loops back to `bb1`, and `bb3` reads `copy _2`: a single forward pass
leaves `bb3`'s entry set empty (`[]`), whereas Pass 2 propagates `2` along
`bb2 → bb1 → bb3` and `movesOk` rejects the body. On `_1 = 1`, Anneal faults
with UB in `bb3` while MiniRust returns `99`. -/
def loopBackEdgeReuse : CapturedMir where
  defPath := "witness::loop_back_edge_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (constU32 99)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 3)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.move (local_ 2)))),
        mkStmt (.assign (local_ 1) (.use (constU32 0)))],
      terminator := mkTerm (.goto 1), isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 2)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem loopBackEdgeReuse_movesOk :
    (iterMovedEntries 1 loopBackEdgeReuse.basicBlocks []).getD 3 [] = [] ∧
    movedAtEntry loopBackEdgeReuse 3 = [2] ∧
    movesOk loopBackEdgeReuse = false ∧
    inFragment loopBackEdgeReuse = false := by decide

def loopBackEdgeReuseFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.Constant (.Int 99) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[],
      .Switch (.Load (.Local (localName 1))) ⟨[(0, bbName 3)]⟩ (bbName 2), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 1)) (.Constant (.Int 0) (.Int u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 2))),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem loopBackEdgeReuse_translate :
    translateFn loopBackEdgeReuse = some loopBackEdgeReuseFn := rfl

def loopBackEdgeReuse1S0 : MachineState := initMachineState loopBackEdgeReuse [.scalar ⟨1, 4⟩]

theorem loopBackEdgeReuse1_anneal_ub :
    ∃ tr u, Reaches (mirTree loopBackEdgeReuse loopBackEdgeReuse1S0) tr u ∧ FaultNow u :=
  faultsA_sound loopBackEdgeReuse 20 _ (by decide)

theorem loopBackEdgeReuse1_minirust_direct :
    (Interp.steps 12 (machine loopBackEdgeReuse loopBackEdgeReuseFn
        loopBackEdgeReuse1S0.frame.locals loopBackEdgeReuseFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) := by
  decide +kernel

/-! ### Dead-local UB for `Assign`, `Deinit`, and projected `PlaceMention` -/

/-- Assigning to `_1` after `StorageDead(_1)` raises UB in both models. -/
def deadAssign : CapturedMir where
  defPath := "witness::dead_assign"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.storageDead 1),
        mkStmt (.assign (local_ 1) (.use (constU32 5)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem deadAssign_inFragment : inFragment deadAssign = true := by decide

def deadAssignFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .StorageDead (localName 1),
      .Assign (.Local (localName 1)) (.Constant (.Int 5) (.Int u32))], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deadAssign_translate : translateFn deadAssign = some deadAssignFn := rfl

def deadAssignS0 : MachineState := initMachineState deadAssign []
def deadAssignMInit : Mach := machine deadAssign deadAssignFn deadAssignS0.frame.locals deadAssignFn.start

theorem deadAssign_anneal_ub : ∃ tr u, Reaches (mirTree deadAssign deadAssignS0) tr u ∧ FaultNow u :=
  faultsA_sound deadAssign 10 _ (by decide)

theorem deadAssign_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n deadAssignMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := deadAssign_anneal_ub
  exact mirCall_ub deadAssign_inFragment deadAssign_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadAssignMInit rfl rfl rfl hr hf

theorem deadAssign_minirust_direct :
    (match Interp.steps 4 deadAssignMInit with
      | .error (.ub msg) => some msg
      | _ => none) = some "access to a dead local" := by
  decide +kernel

theorem deadAssign_steps4_ub :
    Interp.steps 4 deadAssignMInit = .error (.ub "access to a dead local") := by
  have h := deadAssign_minirust_direct
  revert h
  cases Interp.steps 4 deadAssignMInit with
  | ok _ => simp
  | error e => cases e <;> simp

theorem deadAssign_converse_error :
    (∃ msg, Stop.ub "access to a dead local" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree deadAssign []) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 4 ∧ Interp.steps k deadAssignMInit = .ok mRet ∧
      ReturnRel deadAssign ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadAssign []) tr (.normal (v, mem))) :=
  mirCall_steps_error deadAssign_inFragment deadAssign_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadAssignMInit rfl rfl rfl deadAssign_steps4_ub

theorem deadAssign_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen deadAssign + n) deadAssignMInit = .ok m' ∧
      StateRel deadAssign deadAssignFn ctx0 s' m' ∧
      Reaches (mirCallTree deadAssign []) tr (mirTree deadAssign s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen deadAssign + n ∧
      Interp.steps k deadAssignMInit = .ok mRet ∧
      ReturnRel deadAssign ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadAssign []) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen deadAssign + n) deadAssignMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree deadAssign []) tr u ∧ FaultNow u) :=
  mirCall_outcome deadAssign_inFragment deadAssign_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadAssignMInit rfl rfl rfl n

/-- `Deinit(_1)` after `StorageDead(_1)` raises UB in both models. -/
def deadDeinit : CapturedMir where
  defPath := "witness::dead_deinit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (constU32 5))),
        mkStmt (.storageDead 1),
        mkStmt (.deinit (local_ 1))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem deadDeinit_inFragment : inFragment deadDeinit = true := by decide

def deadDeinitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .Assign (.Local (localName 1)) (.Constant (.Int 5) (.Int u32)),
      .StorageDead (localName 1),
      .Deinit (.Local (localName 1))], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deadDeinit_translate : translateFn deadDeinit = some deadDeinitFn := rfl

def deadDeinitS0 : MachineState := initMachineState deadDeinit []
def deadDeinitMInit : Mach := machine deadDeinit deadDeinitFn deadDeinitS0.frame.locals deadDeinitFn.start

theorem deadDeinit_anneal_ub : ∃ tr u, Reaches (mirTree deadDeinit deadDeinitS0) tr u ∧ FaultNow u :=
  faultsA_sound deadDeinit 10 _ (by decide)

theorem deadDeinit_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n deadDeinitMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := deadDeinit_anneal_ub
  exact mirCall_ub deadDeinit_inFragment deadDeinit_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadDeinitMInit rfl rfl rfl hr hf

theorem deadDeinit_minirust_direct :
    (match Interp.steps 5 deadDeinitMInit with
      | .error (.ub msg) => some msg
      | _ => none) = some "access to a dead local" := by
  decide +kernel

theorem deadDeinit_steps5_ub :
    Interp.steps 5 deadDeinitMInit = .error (.ub "access to a dead local") := by
  have h := deadDeinit_minirust_direct
  revert h
  cases Interp.steps 5 deadDeinitMInit with
  | ok _ => simp
  | error e => cases e <;> simp

theorem deadDeinit_converse_error :
    (∃ msg, Stop.ub "access to a dead local" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree deadDeinit []) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 5 ∧ Interp.steps k deadDeinitMInit = .ok mRet ∧
      ReturnRel deadDeinit ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadDeinit []) tr (.normal (v, mem))) :=
  mirCall_steps_error deadDeinit_inFragment deadDeinit_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadDeinitMInit rfl rfl rfl deadDeinit_steps5_ub

theorem deadDeinit_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen deadDeinit + n) deadDeinitMInit = .ok m' ∧
      StateRel deadDeinit deadDeinitFn ctx0 s' m' ∧
      Reaches (mirCallTree deadDeinit []) tr (mirTree deadDeinit s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen deadDeinit + n ∧
      Interp.steps k deadDeinitMInit = .ok mRet ∧
      ReturnRel deadDeinit ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadDeinit []) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen deadDeinit + n) deadDeinitMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree deadDeinit []) tr u ∧ FaultNow u) :=
  mirCall_outcome deadDeinit_inFragment deadDeinit_translate ctx0 (ctx0_ok2 rfl) []
    (by decide) deadDeinitMInit rfl rfl rfl n

/-- Projected `PlaceMention(_1.0)` on `_1: (u32, bool)` after `StorageDead(_1)`
raises UB in both models. -/
theorem ctx0_ok_u32_tuple {body : CapturedMir}
    (h : body.localDecls = [u32Decl, u32BoolTupleDecl]) : CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 1, hd => simp at hd; subst hd; rw [u32BoolTupleDecl, u32BoolTupleTyW, itOf_u32BoolTuple, tyOf_u32BoolTuple]; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

def deadPlaceMention : CapturedMir where
  defPath := "witness::dead_place_mention"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.storageDead 1),
        mkStmt (.placeMention (field0U32 1))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem deadPlaceMention_inFragment : inFragment deadPlaceMention = true := by decide

def deadPlaceMentionFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, intBoolTupleTy u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 1),
      .StorageDead (localName 1),
      .PlaceMention (.Field (.Local (localName 1)) 0)], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deadPlaceMention_translate :
    translateFn deadPlaceMention = some deadPlaceMentionFn := rfl

def deadPlaceMentionS0 : MachineState := initMachineState deadPlaceMention []
def deadPlaceMentionMInit : Mach :=
  machine deadPlaceMention deadPlaceMentionFn deadPlaceMentionS0.frame.locals
    deadPlaceMentionFn.start

theorem deadPlaceMention_anneal_ub :
    ∃ tr u, Reaches (mirTree deadPlaceMention deadPlaceMentionS0) tr u ∧ FaultNow u :=
  faultsA_sound deadPlaceMention 10 _ (by decide)

theorem deadPlaceMention_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n deadPlaceMentionMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := deadPlaceMention_anneal_ub
  exact mirCall_ub deadPlaceMention_inFragment deadPlaceMention_translate ctx0
    (ctx0_ok_u32_tuple rfl) [] (by decide) deadPlaceMentionMInit rfl rfl rfl hr hf

theorem deadPlaceMention_minirust_direct :
    (match Interp.steps 4 deadPlaceMentionMInit with
      | .error (.ub msg) => some msg
      | _ => none) = some "access to a dead local" := by
  decide +kernel

theorem deadPlaceMention_steps4_ub :
    Interp.steps 4 deadPlaceMentionMInit = .error (.ub "access to a dead local") := by
  have h := deadPlaceMention_minirust_direct
  revert h
  cases Interp.steps 4 deadPlaceMentionMInit with
  | ok _ => simp
  | error e => cases e <;> simp

theorem deadPlaceMention_converse_error :
    (∃ msg, Stop.ub "access to a dead local" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree deadPlaceMention []) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 4 ∧ Interp.steps k deadPlaceMentionMInit = .ok mRet ∧
      ReturnRel deadPlaceMention ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadPlaceMention []) tr (.normal (v, mem))) :=
  mirCall_steps_error deadPlaceMention_inFragment deadPlaceMention_translate ctx0
    (ctx0_ok_u32_tuple rfl) [] (by decide) deadPlaceMentionMInit rfl rfl rfl
    deadPlaceMention_steps4_ub

theorem deadPlaceMention_outcome (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen deadPlaceMention + n) deadPlaceMentionMInit = .ok m' ∧
      StateRel deadPlaceMention deadPlaceMentionFn ctx0 s' m' ∧
      Reaches (mirCallTree deadPlaceMention []) tr (mirTree deadPlaceMention s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen deadPlaceMention + n ∧
      Interp.steps k deadPlaceMentionMInit = .ok mRet ∧
      ReturnRel deadPlaceMention ctx0 s' v mRet ∧
      ReachesRet (mirCallTree deadPlaceMention []) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen deadPlaceMention + n) deadPlaceMentionMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree deadPlaceMention []) tr u ∧ FaultNow u) :=
  mirCall_outcome deadPlaceMention_inFragment deadPlaceMention_translate ctx0
    (ctx0_ok_u32_tuple rfl) [] (by decide) deadPlaceMentionMInit rfl rfl rfl n

/-! ### Boundary counterexamples (`storageDeadOk`, `Deinit`, `stmtMoved`,
`readsOk`, `termReadsOk`) -/

/-- `StorageDead(_0); return` is ill-formed in MiniRust (`storageDeadOk` fails):
Anneal faults with `.ub` on returning a dead `_0`, whereas MiniRust's
`evalReturn` indexes `frame.locals[frame.func.ret]` and hits `Stop.specPanic`.
-/
def storageDeadRet : CapturedMir where
  defPath := "witness::storage_dead_ret"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageDead 0)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem storageDeadRet_rejected :
    storageDeadOk storageDeadRet = false ∧ inFragment storageDeadRet = false := by decide

def storageDeadRetFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.StorageDead (localName 0)], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem storageDeadRet_translate :
    translateFn storageDeadRet = some storageDeadRetFn := rfl

def storageDeadRetS0 : MachineState := initMachineState storageDeadRet []

theorem storageDeadRet_anneal_ub :
    ∃ tr u, Reaches (mirTree storageDeadRet storageDeadRetS0) tr u ∧ FaultNow u :=
  faultsA_sound storageDeadRet 5 _ (by decide)

theorem storageDeadRet_minirust_panics :
    (match Interp.steps 3 (machine storageDeadRet storageDeadRetFn storageDeadRetS0.frame.locals
        storageDeadRetFn.start) with
      | .error (.specPanic msg) => some msg
      | _ => none) =
      some "map index: missing key (frame.locals[frame.func.ret])" := by
  decide +kernel

/-- `Deinit(_1.0); _0 = copy (_1.0); return` on `_1: (u32, bool)` is rejected by
`statementOk`: Anneal's projected `Deinit` checks `_1.0` and leaves `_1`
initialized (returning `42`), whereas MiniRust overwrites `_1.0` with `Uninit`
bytes so the subsequent load raises UB. -/
def projectedDeinit : CapturedMir where
  defPath := "witness::projected_deinit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.deinit (field0U32 1)),
        mkStmt (.assign (local_ 0) (.use (.copy (field0U32 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem projectedDeinit_rejected :
    statementOk projectedDeinit.localDecls (mkStmt (.deinit (field0U32 1))) = false ∧
    inFragment projectedDeinit = false := by decide

def projectedDeinitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, intBoolTupleTy u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Deinit (.Field (.Local (localName 1)) 0),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 0))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem projectedDeinit_translate :
    translateFn projectedDeinit = some projectedDeinitFn := rfl

def projectedDeinitArgs : List Value := [.aggregate 0 [.scalar ⟨42, 4⟩, .scalar ⟨1, 1⟩]]
def projectedDeinitS0 : MachineState := initMachineState projectedDeinit projectedDeinitArgs

theorem projectedDeinit_anneal_ret :
    ReachesRet (mirTree projectedDeinit projectedDeinitS0) []
      (.normal (.scalar ⟨42, 4⟩, projectedDeinitS0.memory)) :=
  runA_sound projectedDeinit 10 _ _ _ rfl

theorem projectedDeinit_minirust_ub :
    (match Interp.steps 3 (machine projectedDeinit projectedDeinitFn projectedDeinitS0.frame.locals
        projectedDeinitFn.start) with
      | .error (.ub msg) => some msg
      | _ => none) =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- `_2.0 = Use(move _1); _0 = Use(copy _1); return`: `stmtMoved` tracks operand
moves on projected assignments without clearing `_2`, so `movesOk` rejects the
subsequent read of `_1` even when inspected standalone. -/
def projAssignMoveReuse : CapturedMir where
  defPath := "witness::proj_assign_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (field0U32 2) (.use (.move (local_ 1)))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem projAssignMoveReuse_movesOk :
    movesOk projAssignMoveReuse = false ∧ inFragment projAssignMoveReuse = false := by decide

/-- `_0 = BinaryOp(Add, move _1, copy _1); return` for `fn(u32) -> u32`:
`readsOk` threads `moveOut` left-to-right across the operands of a single
rvalue (`readsOk (moveOut mo op) ops`), so moving `_1` in the first operand and
reading `_1` in the second operand of the same statement is rejected by
`movesOk`. On input `5`, Anneal faults with `.ub` on the second operand
`copy _1`, whereas MiniRust loads `_1` twice and returns `10`. -/
def sameRvalueMoveReuse : CapturedMir where
  defPath := "witness::same_rvalue_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.move (local_ 1)) (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem sameRvalueMoveReuse_movesOk :
    readsOk [] (rvOperands (.binaryOp .add (.move (local_ 1)) (.copy (local_ 1)))) = false ∧
    movesOk sameRvalueMoveReuse = false ∧
    inFragment sameRvalueMoveReuse = false := by decide

def sameRvalueMoveReuseFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 1))) (.Load (.Local (localName 1))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem sameRvalueMoveReuse_translate :
    translateFn sameRvalueMoveReuse = some sameRvalueMoveReuseFn := rfl

def sameRvalueMoveReuse5S0 : MachineState := initMachineState sameRvalueMoveReuse [.scalar ⟨5, 4⟩]

theorem sameRvalueMoveReuse5_anneal_ub :
    ∃ tr u, Reaches (mirTree sameRvalueMoveReuse sameRvalueMoveReuse5S0) tr u ∧ FaultNow u :=
  faultsA_sound sameRvalueMoveReuse 5 _ (by decide)

theorem sameRvalueMoveReuse5_minirust_direct :
    (Interp.steps 3 (machine sameRvalueMoveReuse sameRvalueMoveReuseFn
        sameRvalueMoveReuse5S0.frame.locals sameRvalueMoveReuseFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 10 }, [1]) := by
  decide +kernel

/-- `_0 = const 10_u32; StorageLive(_1); _1 = Use(move _0); StorageDead(_1);`
`return` for `fn() -> u32`: every statement satisfies `stmtReadsOk`, but
`termReadsOk` on `.return_` requires `!mo.contains 0` because `Return` reads the
return place `_0`. Anneal de-initializes `_0` at `move _0` and faults with `.ub`
at `return`, whereas MiniRust's `evalReturn` loads the still-present bytes of
`_0` and returns `10`. -/
def moveRetPlace : CapturedMir where
  defPath := "witness::move_ret_place"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.use (constU32 10))),
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (.move (local_ 0)))),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem moveRetPlace_movesOk :
    termReadsOk [0] (mkTerm .return_) = false ∧
    movesOk moveRetPlace = false ∧
    inFragment moveRetPlace = false := by decide

def moveRetPlaceFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0)) (.Constant (.Int 10) (.Int u32)),
      .StorageLive (localName 1),
      .Assign (.Local (localName 1)) (.Load (.Local (localName 0))),
      .StorageDead (localName 1)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem moveRetPlace_translate : translateFn moveRetPlace = some moveRetPlaceFn := rfl

def moveRetPlaceS0 : MachineState := initMachineState moveRetPlace []

theorem moveRetPlace_anneal_ub :
    ∃ tr u, Reaches (mirTree moveRetPlace moveRetPlaceS0) tr u ∧ FaultNow u :=
  faultsA_sound moveRetPlace 10 _ (by decide)

theorem moveRetPlace_minirust_direct :
    (Interp.steps 6 (machine moveRetPlace moveRetPlaceFn
        moveRetPlaceS0.frame.locals moveRetPlaceFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 10 }, [1]) := by
  decide +kernel

/-! ### `StorageLive` on argument and return locals, `StorageDead` on an
argument, and CFG diamond merges -/

/-- `fn(x: u32) -> u32` exercising `StorageLive(_1)` on an argument local and
`StorageLive(_0)` on the return place (both permitted by MiniRust's
well-formedness check in `spec/lang/well-formed.md` and by `statementOk`).
`StorageLive(_1)` and `StorageLive(_0)` deallocate the caller-range (`< 2^32`)
initial allocations at `256` and `128`, re-allocate fresh `Uninit` stack
allocations at `2 * 2^32` and `3 * 2^32`, clear `1` from `mo` (`stmtMoved`),
and allow `Return` to copy `_0` from its re-allocated `3 * 2^32` slot and tear
down the shuffled `locals` map. -/
def storageLiveArgRet : CapturedMir where
  defPath := "witness::storage_live_arg_ret"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (.move (local_ 1)))),
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.binaryOp .add (.copy (local_ 2)) (constU32 10))),
        mkStmt (.storageLive 0),
        mkStmt (.assign (local_ 0) (.binaryOp .mul (.move (local_ 1)) (constU32 2))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem storageLiveArgRet_inFragment : inFragment storageLiveArgRet = true := by decide

def storageLiveArgRetFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.Load (.Local (localName 1))),
      .StorageLive (localName 1),
      .Assign (.Local (localName 1))
        (.BinOp (.Int .Add) (.Load (.Local (localName 2))) (.Constant (.Int 10) (.Int u32))),
      .StorageLive (localName 0),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Mul) (.Load (.Local (localName 1))) (.Constant (.Int 2) (.Int u32))),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem storageLiveArgRet_translate :
    translateFn storageLiveArgRet = some storageLiveArgRetFn := rfl

theorem ctx0_ok_u32_3 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, u32Decl, u32Decl])
    (ha : body.argCount = 1 := by rfl) : CtxOk body ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd; rw [h] at hd; rw [ha] at hi
    match i, hd, hi with
    | 0, hd, _ => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 1, hd, _ => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | _ + 2, _, hi => omega
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

def storageLiveArgRet5S0 : MachineState :=
  initMachineState storageLiveArgRet [.scalar ⟨5, 4⟩]
def storageLiveArgRet5MInit : Mach :=
  machine storageLiveArgRet storageLiveArgRetFn
    storageLiveArgRet5S0.frame.locals storageLiveArgRetFn.start

theorem storageLiveArgRet5_anneal_ret :
    ReachesRet (mirTree storageLiveArgRet storageLiveArgRet5S0) []
      (.normal (.scalar ⟨30, 4⟩, storageLiveArgRet5S0.memory)) :=
  runA_sound storageLiveArgRet 20 _ _ _ rfl

theorem storageLiveArgRet5_noUB :
    MirNoUBTree (mirCallTree storageLiveArgRet [.scalar ⟨5, 4⟩]) :=
  runA_noUB storageLiveArgRet 20 _ _ _ rfl

theorem storageLiveArgRet5_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen storageLiveArgRet + n) storageLiveArgRet5MInit = .ok m' ∧
      StateRel storageLiveArgRet storageLiveArgRetFn ctx0 s' m' ∧
      Reaches (mirCallTree storageLiveArgRet [.scalar ⟨5, 4⟩]) tr
        (mirTree storageLiveArgRet s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen storageLiveArgRet + n ∧
      Interp.steps k storageLiveArgRet5MInit = .ok mRet ∧
      ReturnRel storageLiveArgRet ctx0 s' v mRet ∧
      ReachesRet (mirCallTree storageLiveArgRet [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress storageLiveArgRet_inFragment storageLiveArgRet_translate ctx0
    (ctx0_ok_u32_3 rfl) [.scalar ⟨5, 4⟩] (by decide) storageLiveArgRet5MInit
    rfl rfl rfl storageLiveArgRet5_noUB n

theorem storageLiveArgRet5_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n storageLiveArgRet5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 30 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret storageLiveArgRet_inFragment storageLiveArgRet_translate ctx0
      (ctx0_ok_u32_3 rfl) [.scalar ⟨5, 4⟩] (by decide) storageLiveArgRet5MInit
      rfl rfl rfl storageLiveArgRet5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [storageLiveArgRet] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem storageLiveArgRet5_minirust_direct :
    (Interp.steps 9 storageLiveArgRet5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live), m.mem.memory.allocations.map (·.addr))) =
      some (some { retAlloc with data := scalarBytes u32 30 }, [1],
        [true, false, false, false, false, false],
        [64, 128, 256, 2 ^ 32, 2 * 2 ^ 32, 3 * 2 ^ 32]) := by
  decide +kernel

/-- `_0 = Use(copy _1); StorageDead(_1); return` for `fn(u32) -> u32`:
`statementOk` accepts `StorageDead(_1)` because `_1` is an in-range local, while
`storageDeadOk` rejects it at the exact upper boundary `i = argCount` (`1 ≤ 1`),
matching MiniRust's well-formedness rejection of `StorageDead` on `func.args`.
-/
def storageDeadArg : CapturedMir where
  defPath := "witness::storage_dead_arg"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem storageDeadArg_rejected :
    statementOk storageDeadArg.localDecls (mkStmt (.storageDead 1)) = true ∧
    storageDeadOk storageDeadArg = false ∧
    inFragment storageDeadArg = false := by decide

def storageDeadArgFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1))),
      .StorageDead (localName 1)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem storageDeadArg_translate :
    translateFn storageDeadArg = some storageDeadArgFn := rfl

def storageDeadArg5S0 : MachineState :=
  initMachineState storageDeadArg [.scalar ⟨5, 4⟩]

theorem storageDeadArg5_anneal_ret :
    ReachesRet (mirTree storageDeadArg storageDeadArg5S0) []
      (.normal (.scalar ⟨5, 4⟩, storageDeadArg5S0.memory)) :=
  runA_sound storageDeadArg 10 _ _ _ rfl

theorem storageDeadArg5_minirust_direct :
    (Interp.steps 4 (machine storageDeadArg storageDeadArgFn
        storageDeadArg5S0.frame.locals storageDeadArgFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length),
          m.mem.memory.allocations.map (·.live))) =
      some (some { retAlloc with data := scalarBytes u32 5 }, [1],
        [true, false, false]) := by
  decide +kernel

/-- `StorageDead(_1); _0 = Use(copy _1); return` for `fn(u32) -> u32`:
rejected by `storageDeadOk = false` (`1 ≤ argCount`), and reading `_1` after
`StorageDead(_1)` faults with UB in both Anneal (`storageDeadArgReadAfter5_anneal_ub`)
and MiniRust (`storageDeadArgReadAfter5_minirust_ub`, raising
`"access to a dead local"`). -/
def storageDeadArgReadAfter : CapturedMir where
  defPath := "witness::storage_dead_arg_read_after"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageDead 1),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem storageDeadArgReadAfter_rejected :
    storageDeadOk storageDeadArgReadAfter = false ∧
    inFragment storageDeadArgReadAfter = false := by decide

def storageDeadArgReadAfterFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageDead (localName 1),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem storageDeadArgReadAfter_translate :
    translateFn storageDeadArgReadAfter = some storageDeadArgReadAfterFn := rfl

def storageDeadArgReadAfter5S0 : MachineState :=
  initMachineState storageDeadArgReadAfter [.scalar ⟨5, 4⟩]

theorem storageDeadArgReadAfter5_anneal_ub :
    ∃ tr u, Reaches (mirTree storageDeadArgReadAfter storageDeadArgReadAfter5S0) tr u ∧
      FaultNow u :=
  faultsA_sound storageDeadArgReadAfter 10 _ (by decide)

theorem storageDeadArgReadAfter5_minirust_ub :
    (match Interp.steps 3 (machine storageDeadArgReadAfter storageDeadArgReadAfterFn
        storageDeadArgReadAfter5S0.frame.locals storageDeadArgReadAfterFn.start) with
      | .error (.ub msg) => some msg
      | _ => none) = some "access to a dead local" := by
  decide +kernel

/-- Caller context placing `_0`, `_1`, and `_2` at distinct non-zero addresses
`128`, `256`, and `384` below `2^32` for two-argument `(bool, u32) -> u32`
diamond witnesses. -/
def ctx0_2 : Ctx := { ctx0 with addrs := [128, 256, 384] }

theorem ctx0_2_ok_bool_u32 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, boolDecl, u32Decl, u32Decl])
    (ha : body.argCount = 2 := by rfl) : CtxOk body ctx0_2 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd; rw [h] at hd; rw [ha] at hi
    match i, hd, hi with
    | 0, hd, _ => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 1, hd, _ => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | 2, hd, _ => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | _ + 3, _, hi => omega
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

/-- A 4-block diamond CFG `fn(flag: bool, x: u32) -> u32` accepted by
`inFragment = true`: `bb0` branches via `SwitchInt(move _1)` to `bb1` (which
moves `_2` into `_3 = move _2 + 1` and re-initializes `_2 = 10`, leaving
outgoing set `[1]`) and `bb2` (which moves `_2` into `_3 = move _2 * 2` without
re-initializing `_2`, leaving outgoing set `[2, 1]`). At the merge block `bb3`,
`movedAtEntry` converges to `[1, 2]`, and `bb3` safely returns `move _3`
without reading `_2`. -/
def diamondMoveJoin : CapturedMir where
  defPath := "witness::diamond_move_join"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, boolDecl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 3)],
      terminator := mkTerm (.switchInt (.move (local_ 1))
        { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .add (.move (local_ 2)) (constU32 1))),
        mkStmt (.assign (local_ 2) (.use (constU32 10)))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.binaryOp .mul (.move (local_ 2)) (constU32 2)))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.move (local_ 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem diamondMoveJoin_inFragment : inFragment diamondMoveJoin = true := by decide

theorem diamondMoveJoin_movedAtEntry :
    [0, 1, 2, 3].map (movedAtEntry diamondMoveJoin) = [[], [1], [1], [1, 2]] := by decide

def diamondMoveJoinFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Bool),
    (localName 2, .Int u32), (localName 3, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.StorageLive (localName 3)],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1))))
        ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Add) (.Load (.Local (localName 2))) (.Constant (.Int 1) (.Int u32))),
      .Assign (.Local (localName 2)) (.Constant (.Int 10) (.Int u32))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Mul) (.Load (.Local (localName 2))) (.Constant (.Int 2) (.Int u32)))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 3))),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem diamondMoveJoin_translate :
    translateFn diamondMoveJoin = some diamondMoveJoinFn := rfl

def diamondMoveJoinTrueArgs : List Value := [.scalar ⟨1, 1⟩, .scalar ⟨7, 4⟩]
def diamondMoveJoinTrueS0 : MachineState :=
  initMachineState diamondMoveJoin diamondMoveJoinTrueArgs
def diamondMoveJoinTrueMInit : Mach :=
  machineWithCtx ctx0_2 diamondMoveJoin diamondMoveJoinFn
    diamondMoveJoinTrueS0.frame.locals diamondMoveJoinFn.start

theorem diamondMoveJoinTrue_anneal_ret :
    ReachesRet (mirTree diamondMoveJoin diamondMoveJoinTrueS0)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨8, 4⟩, diamondMoveJoinTrueS0.memory)) :=
  runA_sound diamondMoveJoin 20 _ _ _ rfl

theorem diamondMoveJoinTrue_noUB :
    MirNoUBTree (mirCallTree diamondMoveJoin diamondMoveJoinTrueArgs) :=
  runA_noUB diamondMoveJoin 20 _ _ _ rfl

theorem diamondMoveJoinTrue_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen diamondMoveJoin + n) diamondMoveJoinTrueMInit = .ok m' ∧
      StateRel diamondMoveJoin diamondMoveJoinFn ctx0_2 s' m' ∧
      Reaches (mirCallTree diamondMoveJoin diamondMoveJoinTrueArgs) tr
        (mirTree diamondMoveJoin s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen diamondMoveJoin + n ∧
      Interp.steps k diamondMoveJoinTrueMInit = .ok mRet ∧
      ReturnRel diamondMoveJoin ctx0_2 s' v mRet ∧
      ReachesRet (mirCallTree diamondMoveJoin diamondMoveJoinTrueArgs) tr
        (.normal (v, mem))) :=
  mirCall_progress diamondMoveJoin_inFragment diamondMoveJoin_translate ctx0_2
    (ctx0_2_ok_bool_u32 rfl) diamondMoveJoinTrueArgs (by decide)
    diamondMoveJoinTrueMInit rfl rfl rfl diamondMoveJoinTrue_noUB n

theorem diamondMoveJoinTrue_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n diamondMoveJoinTrueMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 8 } ∧
      m'.threads = [thread1 ctx0_2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret diamondMoveJoin_inFragment diamondMoveJoin_translate ctx0_2
      (ctx0_2_ok_bool_u32 rfl) diamondMoveJoinTrueArgs (by decide)
      diamondMoveJoinTrueMInit rfl rfl rfl diamondMoveJoinTrue_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [diamondMoveJoin] at hd; subst hd
  simp [retPtr, ctx0_2, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0_2, ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem diamondMoveJoinTrue_minirust_direct :
    (Interp.steps 9 diamondMoveJoinTrueMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 8 }, [1]) := by
  decide +kernel

def diamondMoveJoinFalseArgs : List Value := [.scalar ⟨0, 1⟩, .scalar ⟨7, 4⟩]
def diamondMoveJoinFalseS0 : MachineState :=
  initMachineState diamondMoveJoin diamondMoveJoinFalseArgs
def diamondMoveJoinFalseMInit : Mach :=
  machineWithCtx ctx0_2 diamondMoveJoin diamondMoveJoinFn
    diamondMoveJoinFalseS0.frame.locals diamondMoveJoinFn.start

theorem diamondMoveJoinFalse_anneal_ret :
    ReachesRet (mirTree diamondMoveJoin diamondMoveJoinFalseS0)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨14, 4⟩, diamondMoveJoinFalseS0.memory)) :=
  runA_sound diamondMoveJoin 20 _ _ _ rfl

theorem diamondMoveJoinFalse_noUB :
    MirNoUBTree (mirCallTree diamondMoveJoin diamondMoveJoinFalseArgs) :=
  runA_noUB diamondMoveJoin 20 _ _ _ rfl

theorem diamondMoveJoinFalse_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen diamondMoveJoin + n) diamondMoveJoinFalseMInit = .ok m' ∧
      StateRel diamondMoveJoin diamondMoveJoinFn ctx0_2 s' m' ∧
      Reaches (mirCallTree diamondMoveJoin diamondMoveJoinFalseArgs) tr
        (mirTree diamondMoveJoin s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen diamondMoveJoin + n ∧
      Interp.steps k diamondMoveJoinFalseMInit = .ok mRet ∧
      ReturnRel diamondMoveJoin ctx0_2 s' v mRet ∧
      ReachesRet (mirCallTree diamondMoveJoin diamondMoveJoinFalseArgs) tr
        (.normal (v, mem))) :=
  mirCall_progress diamondMoveJoin_inFragment diamondMoveJoin_translate ctx0_2
    (ctx0_2_ok_bool_u32 rfl) diamondMoveJoinFalseArgs (by decide)
    diamondMoveJoinFalseMInit rfl rfl rfl diamondMoveJoinFalse_noUB n

theorem diamondMoveJoinFalse_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n diamondMoveJoinFalseMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 14 } ∧
      m'.threads = [thread1 ctx0_2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret diamondMoveJoin_inFragment diamondMoveJoin_translate ctx0_2
      (ctx0_2_ok_bool_u32 rfl) diamondMoveJoinFalseArgs (by decide)
      diamondMoveJoinFalseMInit rfl rfl rfl diamondMoveJoinFalse_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [diamondMoveJoin] at hd; subst hd
  simp [retPtr, ctx0_2, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0_2, ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem diamondMoveJoinFalse_minirust_direct :
    (Interp.steps 8 diamondMoveJoinFalseMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 14 }, [1]) := by
  decide +kernel

/-- A 4-block diamond CFG where only `bb2` moves out of `_2` while `bb1` leaves
`_2` intact, and the merge block `bb3` reads `copy _2`: `movedAtEntry` unions
`[]` and `[2]` to `[2]` at `bb3`, so `movesOk` rejects the body. On
`(false, 7)`, Anneal faults with `.ub` at `copy _2` in `bb3`, whereas MiniRust
loads the stale `7` and returns `14`. -/
def diamondHalfMoveReuse : CapturedMir where
  defPath := "witness::diamond_half_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, boolDecl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 3)],
      terminator := mkTerm (.switchInt (.copy (local_ 1))
        { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 3) (.use (constU32 1)))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 3) (.use (.move (local_ 2))))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.move (local_ 3)) (.copy (local_ 2)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem diamondHalfMoveReuse_movesOk :
    [0, 1, 2, 3].map (movedAtEntry diamondHalfMoveReuse) = [[], [], [], [2]] ∧
    movesOk diamondHalfMoveReuse = false ∧
    inFragment diamondHalfMoveReuse = false := by decide

def diamondHalfMoveReuseFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Bool),
    (localName 2, .Int u32), (localName 3, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[.StorageLive (localName 3)],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Local (localName 1))))
        ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[.Assign (.Local (localName 3)) (.Constant (.Int 1) (.Int u32))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 2, ⟨[.Assign (.Local (localName 3)) (.Load (.Local (localName 2)))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 3))) (.Load (.Local (localName 2)))),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem diamondHalfMoveReuse_translate :
    translateFn diamondHalfMoveReuse = some diamondHalfMoveReuseFn := rfl

def diamondHalfMoveReuseFalseS0 : MachineState :=
  initMachineState diamondHalfMoveReuse [.scalar ⟨0, 1⟩, .scalar ⟨7, 4⟩]

theorem diamondHalfMoveReuseFalse_anneal_ub :
    ∃ tr u, Reaches (mirTree diamondHalfMoveReuse diamondHalfMoveReuseFalseS0) tr u ∧
      FaultNow u :=
  faultsA_sound diamondHalfMoveReuse 15 _ (by decide)

theorem diamondHalfMoveReuseFalse_minirust_direct :
    (Interp.steps 8 (machineWithCtx ctx0_2 diamondHalfMoveReuse diamondHalfMoveReuseFn
        diamondHalfMoveReuseFalseS0.frame.locals diamondHalfMoveReuseFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 14 }, [1]) := by
  decide +kernel

/-- Caller context for `tupleAggCastMove` and `projFieldMoveReuse`. -/
def ctx0_tupleAggCastMove : Ctx :=
  { ctx0 with addrs := [128, 256, 384, 512, 640, 768] }

theorem ctx0_ok_tupleAggCastMove {body : CapturedMir}
    (h : body.localDecls = [u32Decl, i8Decl, i8Decl, u32Decl, boolDecl, u32BoolTupleDecl]) :
    CtxOk body ctx0_tupleAggCastMove where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 1, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 2, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 3, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 4, hd => simp at hd; subst hd; rw [boolDecl, boolTy, itOf_bool, tyOf_bool]; decide
    | 5, hd => simp at hd; subst hd; rw [u32BoolTupleDecl, u32BoolTupleTyW, itOf_u32BoolTuple, tyOf_u32BoolTuple]; decide
    | _ + 6, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

/-- `tupleAggCastMove`: `fn(x: i8) -> u32` exercising `Operand::Move` across
`Rvalue::UnaryOp(Neg, move _1)` on `i8`, `Rvalue::Cast(IntToInt, move _2, u32)`
from `i8` to `u32`, `Rvalue::UnaryOp(Not, move _4)` on `bool` (self-assign
move), `Rvalue::Aggregate(Tuple, [move _3, move _4])` constructing a `(u32, bool)`
tuple from two moved operands, and `Rvalue::Use(move (_5.0))` projected field
move followed by `StorageDead(_5)`. -/
def tupleAggCastMove : CapturedMir where
  defPath := "witness::tuple_agg_cast_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, i8Decl, i8Decl, u32Decl, boolDecl, u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.unaryOp .neg (.move (local_ 1)))),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.cast .intToInt (.move (local_ 2)) u32Ty)),
        mkStmt (.storageDead 2),
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.binaryOp .gt (.copy (local_ 3)) (constU32 0))),
        mkStmt (.assign (local_ 4) (.unaryOp .not (.move (local_ 4)))),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.aggregate .tuple [.move (local_ 3), .move (local_ 4)])),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 4),
        mkStmt (.assign (local_ 0) (.use (.move (field0U32 5)))),
        mkStmt (.storageDead 5)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem tupleAggCastMove_inFragment : inFragment tupleAggCastMove = true := by decide

/-- `CtxOk.addrs` constrains only `_0` and the arguments (`i ≤ body.argCount`),
so unaligned (`257`) or `≥ 2^32` (`2^40`) trailing entries in `ctx.addrs` at
temporary indices `i > argCount` remain valid caller contexts. -/
theorem ctx0_ok_trailing_temp_addrs :
    CtxOk tupleAggCastMove { ctx0 with addrs := [128, 256, 257, 2 ^ 40] } where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [tupleAggCastMove] at hd; subst hd; decide
    | 1, _, hd => simp [tupleAggCastMove] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [tupleAggCastMove] at hi
  ret := by
    intro d hd; simp [tupleAggCastMove] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def tupleAggCastMoveFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, .Int u32), (localName 4, .Bool), (localName 5, intBoolTupleTy u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Assign (.Local (localName 2)) (.UnOp (.Int .Neg) (.Load (.Local (localName 1)))),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 2)))),
      .StorageDead (localName 2),
      .StorageLive (localName 4),
      .Assign (.Local (localName 4))
        (.BinOp (.Rel .Gt) (.Load (.Local (localName 3))) (.Constant (.Int 0) (.Int u32))),
      .Assign (.Local (localName 4)) (boolNot (.Load (.Local (localName 4)))),
      .StorageLive (localName 5),
      .Assign (.Local (localName 5))
        (.Tuple [.Load (.Local (localName 3)), .Load (.Local (localName 4))]
          (intBoolTupleTy u32)),
      .StorageDead (localName 3),
      .StorageDead (localName 4),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 5)) 0)),
      .StorageDead (localName 5)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem tupleAggCastMove_translate :
    translateFn tupleAggCastMove = some tupleAggCastMoveFn := rfl

def tupleAggCastMoveNeg5Args : List Value := [.scalar ⟨251, 1⟩]
def tupleAggCastMoveNeg5S0 : MachineState :=
  initMachineState tupleAggCastMove tupleAggCastMoveNeg5Args
def tupleAggCastMoveNeg5MInit : Mach :=
  machineWithCtx ctx0_tupleAggCastMove tupleAggCastMove tupleAggCastMoveFn
    tupleAggCastMoveNeg5S0.frame.locals tupleAggCastMoveFn.start

theorem tupleAggCastMoveNeg5_anneal_ret :
    ReachesRet (mirTree tupleAggCastMove tupleAggCastMoveNeg5S0) []
      (.normal (.scalar ⟨5, 4⟩, tupleAggCastMoveNeg5S0.memory)) :=
  runA_sound tupleAggCastMove 25 _ _ _ rfl

theorem tupleAggCastMoveNeg5_noUB :
    MirNoUBTree (mirCallTree tupleAggCastMove tupleAggCastMoveNeg5Args) :=
  runA_noUB tupleAggCastMove 25 _ _ _ rfl

theorem tupleAggCastMoveNeg5_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen tupleAggCastMove + n) tupleAggCastMoveNeg5MInit = .ok m' ∧
      StateRel tupleAggCastMove tupleAggCastMoveFn ctx0_tupleAggCastMove s' m' ∧
      Reaches (mirCallTree tupleAggCastMove tupleAggCastMoveNeg5Args) tr
        (mirTree tupleAggCastMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen tupleAggCastMove + n ∧
      Interp.steps k tupleAggCastMoveNeg5MInit = .ok mRet ∧
      ReturnRel tupleAggCastMove ctx0_tupleAggCastMove s' v mRet ∧
      ReachesRet (mirCallTree tupleAggCastMove tupleAggCastMoveNeg5Args) tr
        (.normal (v, mem))) :=
  mirCall_progress tupleAggCastMove_inFragment tupleAggCastMove_translate ctx0_tupleAggCastMove
    (ctx0_ok_tupleAggCastMove rfl) tupleAggCastMoveNeg5Args (by decide)
    tupleAggCastMoveNeg5MInit rfl rfl rfl tupleAggCastMoveNeg5_noUB n

theorem tupleAggCastMoveNeg5_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n tupleAggCastMoveNeg5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 5 } ∧
      m'.threads = [thread1 ctx0_tupleAggCastMove
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret tupleAggCastMove_inFragment tupleAggCastMove_translate ctx0_tupleAggCastMove
      (ctx0_ok_tupleAggCastMove rfl) tupleAggCastMoveNeg5Args (by decide)
      tupleAggCastMoveNeg5MInit rfl rfl rfl tupleAggCastMoveNeg5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [tupleAggCastMove] at hd; subst hd
  simp [retPtr, ctx0_tupleAggCastMove, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0_tupleAggCastMove, ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem tupleAggCastMoveNeg5_minirust_direct :
    (Interp.steps 16 tupleAggCastMoveNeg5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?,
          m.mem.memory.allocations.map (·.live),
          m.mem.memory.allocations.map (·.addr),
          m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 5 },
        [true, false, false, false, false, false, false],
        [64, 128, 256, 2 ^ 32, 2 * 2 ^ 32, 2 ^ 32, 3 * 2 ^ 32],
        [1]) := by
  decide +kernel

/-- Projected field read after root tuple move (`projFieldMoveReuse`):
moving out of the root tuple `_3` (`_4 = Use(move _3)`) deinitializes `_3` in
Anneal's `evalOperand` (`s.frame.locals[3] := .uninit`), so subsequently
reading the projected field `_3.0` (`_0 = Use(copy (_3.0))`) faults with `.ub`
in Anneal while succeeding in MiniRust (which translates `move _3` to
`Load(Local(_3))` without deinitializing `_3`). `movesOk` rejects
`projFieldMoveReuse` because `opMoved (.move (local_ 3)) = some 3` marks local
`3` moved out and `opRead (.copy (field0U32 3)) = some 3` detects the projected
read of `3`. -/
def projFieldMoveReuse : CapturedMir where
  defPath := "witness::proj_field_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, boolDecl, u32BoolTupleDecl, u32BoolTupleDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.aggregate .tuple [.move (local_ 1), .move (local_ 2)])),
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.use (.move (local_ 3)))),
        mkStmt (.assign (local_ 0) (.use (.copy (field0U32 3)))),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem projFieldMoveReuse_movesOk :
    movesOk projFieldMoveReuse = false ∧
    inFragment projFieldMoveReuse = false := by decide

def projFieldMoveReuseFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Bool),
    (localName 3, intBoolTupleTy u32), (localName 4, intBoolTupleTy u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.Tuple [.Load (.Local (localName 1)), .Load (.Local (localName 2))]
          (intBoolTupleTy u32)),
      .StorageLive (localName 4),
      .Assign (.Local (localName 4)) (.Load (.Local (localName 3))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 3)) 0)),
      .StorageDead (localName 4),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem projFieldMoveReuse_translate :
    translateFn projFieldMoveReuse = some projFieldMoveReuseFn := rfl

def projFieldMoveReuseS0 : MachineState :=
  initMachineState projFieldMoveReuse [.scalar ⟨11, 4⟩, .scalar ⟨1, 1⟩]

theorem projFieldMoveReuse_anneal_ub :
    ∃ tr u, Reaches (mirTree projFieldMoveReuse projFieldMoveReuseS0) tr u ∧
      FaultNow u :=
  faultsA_sound projFieldMoveReuse 15 _ (by decide)

theorem projFieldMoveReuse_minirust_direct :
    (Interp.steps 9 (machineWithCtx ctx0_tupleAggCastMove projFieldMoveReuse projFieldMoveReuseFn
        projFieldMoveReuseS0.frame.locals projFieldMoveReuseFn.start)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 11 }, [1]) := by
  decide +kernel

/-! ## `ord_bool_cast_temp_move`: `Ordering` temporaries & moved-`bool` cast -/

/-- `ordBoolCastTempMove`: `fn(a: i8, b: i8, flag: bool) -> Ordering` exercising
`Rvalue::Cast(IntToInt, move _3, u32)` from a moved `bool` parameter (`boolToU8`
followed by `IntToInt`), `SwitchInt(move _4)` on the cast temporary, explicit
`StorageLive(_5)` / `BinaryOp(Cmp, move _, move _)` / `Use(move _5)` /
`Deinit(_5)` / `StorageDead(_5)` on a `core::cmp::Ordering` (`Type::Enum`)
temporary local reusing `_4`'s freed `2^32` address, and `ctxI8_4` directly
(`addrs` of length `4 = argCount + 1` with `6` total `localDecls`). -/
def ordBoolCastTempMove : CapturedMir where
  defPath := "witness::ord_bool_cast_temp_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [orderingDecl, i8Decl, i8Decl, boolDecl, u32Decl, orderingDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.cast .intToInt (.move (local_ 3)) u32Ty))],
      terminator := mkTerm (.switchInt (.move (local_ 4))
        { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 4),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.binaryOp .cmp (.move (local_ 1)) (.move (local_ 2))))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [
        mkStmt (.storageDead 4),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.binaryOp .cmp (.move (local_ 2)) (.move (local_ 1))))],
      terminator := mkTerm (.goto 3),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.move (local_ 5)))),
        mkStmt (.deinit (local_ 5)),
        mkStmt (.storageDead 5)],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbiCmpSel
  layouts := emptyLayoutTable
  allocations := []

theorem ctxI8_ok_ordBoolCastTempMove : CtxOk ordBoolCastTempMove ctxI8_4 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [ordBoolCastTempMove] at hd; subst hd; decide
    | 1, _, hd => simp [ordBoolCastTempMove] at hd; subst hd; decide
    | 2, _, hd => simp [ordBoolCastTempMove] at hd; subst hd; decide
    | 3, _, hd => simp [ordBoolCastTempMove] at hd; subst hd; decide
    | _ + 4, hi, _ => simp [ordBoolCastTempMove] at hi
  ret := by
    intro d hd; simp [ordBoolCastTempMove] at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem ordBoolCastTempMove_inFragment : inFragment ordBoolCastTempMove = true := by decide

theorem ordBoolCastTempMove_movedAtEntry :
    [0, 1, 2, 3].map (movedAtEntry ordBoolCastTempMove) =
      [[], [3, 4], [3, 4], [3, 1, 2]] := by decide

/-- Concrete Park-induction witness for `movesOk_of_preFixedPoint` using a
strictly over-approximating inductive pre-fixed point `[[5], [3, 4, 5],
[3, 4, 5], [1, 2, 3]]` (which marks `_5` moved out on entry to `bb0`, unlike
the least fixed point `movedAtEntry`). -/
theorem ordBoolCastTempMove_movesOk_by_preFixedPoint :
    movesOk ordBoolCastTempMove = true := by
  let cert : List (List Nat) := [[5], [3, 4, 5], [3, 4, 5], [1, 2, 3]]
  apply movesOk_of_preFixedPoint (by decide) (by decide) cert
  · intro src dst bb hbb hdst htgt j hj
    have hsrc : src < 4 := by
      have := (List.getElem?_eq_some_iff.mp hbb).1
      simpa [ordBoolCastTempMove] using this
    have hdst' : dst < 4 := by simpa [ordBoolCastTempMove] using hdst
    revert bb hbb htgt j hj
    rcases (by omega : src = 0 ∨ src = 1 ∨ src = 2 ∨ src = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : dst = 0 ∨ dst = 1 ∨ dst = 2 ∨ dst = 3) with rfl | rfl | rfl | rfl <;>
    (intro bb hbb; simp [ordBoolCastTempMove] at hbb; subst hbb; decide)
  · intro blk bb hbb
    have hblk : blk < 4 := by
      have := (List.getElem?_eq_some_iff.mp hbb).1
      simpa [ordBoolCastTempMove] using this
    revert bb hbb
    rcases (by omega : blk = 0 ∨ blk = 1 ∨ blk = 2 ∨ blk = 3) with rfl | rfl | rfl | rfl <;>
    (intro bb hbb; simp [ordBoolCastTempMove] at hbb; subst hbb; decide)

def ordBoolCastTempMoveFn : Gen.Function where
  locals := ⟨[(localName 0, orderingTy), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, .Bool), (localName 4, .Int u32), (localName 5, orderingTy)]⟩
  args := [localName 1, localName 2, localName 3]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 4),
      .Assign (.Local (localName 4))
        (.UnOp (.Cast (.IntToInt u32)) (boolToU8 (.Load (.Local (localName 3)))))],
      .Switch (.Load (.Local (localName 4))) ⟨[(0, bbName 2)]⟩ (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .StorageDead (localName 4),
      .StorageLive (localName 5),
      .Assign (.Local (localName 5))
        (translateCmp (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 2, ⟨[
      .StorageDead (localName 4),
      .StorageLive (localName 5),
      .Assign (.Local (localName 5))
        (translateCmp (.Load (.Local (localName 2))) (.Load (.Local (localName 1))))],
      .Goto (bbName 3), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 5))),
      .Deinit (.Local (localName 5)),
      .StorageDead (localName 5)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem ordBoolCastTempMove_translate :
    translateFn ordBoolCastTempMove = some ordBoolCastTempMoveFn := rfl

def ordBoolCastTempMoveTrueArgs : List Value :=
  [.scalar ⟨251, 1⟩, .scalar ⟨3, 1⟩, .scalar ⟨1, 1⟩]
def ordBoolCastTempMoveTrueS0 : MachineState :=
  initMachineState ordBoolCastTempMove ordBoolCastTempMoveTrueArgs
def ordBoolCastTempMoveTrueMInit : Mach :=
  machineWithCtx ctxI8_4 ordBoolCastTempMove ordBoolCastTempMoveFn
    ordBoolCastTempMoveTrueS0.frame.locals ordBoolCastTempMoveFn.start

theorem ordBoolCastTempMoveTrue_anneal_ret :
    ReachesRet (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveTrueArgs)
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨255, 1⟩, ordBoolCastTempMoveTrueS0.memory)) :=
  runA_sound ordBoolCastTempMove 20 _ _ _ rfl

theorem ordBoolCastTempMoveTrue_noUB :
    MirNoUBTree (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveTrueArgs) :=
  runA_noUB ordBoolCastTempMove 20 _ _ _ rfl

theorem ordBoolCastTempMoveTrue_progress (n : Nat) :
    (∃ s' m' tr,
      Interp.steps (initLen ordBoolCastTempMove + n) ordBoolCastTempMoveTrueMInit = .ok m' ∧
      StateRel ordBoolCastTempMove ordBoolCastTempMoveFn ctxI8_4 s' m' ∧
      Reaches (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveTrueArgs) tr
        (mirTree ordBoolCastTempMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen ordBoolCastTempMove + n ∧
      Interp.steps k ordBoolCastTempMoveTrueMInit = .ok mRet ∧
      ReturnRel ordBoolCastTempMove ctxI8_4 s' v mRet ∧
      ReachesRet (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveTrueArgs) tr
        (.normal (v, mem))) :=
  mirCall_progress ordBoolCastTempMove_inFragment ordBoolCastTempMove_translate ctxI8_4
    ctxI8_ok_ordBoolCastTempMove ordBoolCastTempMoveTrueArgs (by decide)
    ordBoolCastTempMoveTrueMInit rfl rfl rfl ordBoolCastTempMoveTrue_noUB n

theorem ordBoolCastTempMoveTrue_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n ordBoolCastTempMoveTrueMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 255 } ∧
      m'.threads = [thread1 ctxI8_4
        [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret ordBoolCastTempMove_inFragment ordBoolCastTempMove_translate ctxI8_4
      ctxI8_ok_ordBoolCastTempMove ordBoolCastTempMoveTrueArgs (by decide)
      ordBoolCastTempMoveTrueMInit rfl rfl rfl ordBoolCastTempMoveTrue_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [ordBoolCastTempMove] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem ordBoolCastTempMoveTrue_minirust_direct :
    (Interp.steps 12 ordBoolCastTempMoveTrueMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?,
          m.mem.memory.allocations.map (·.live),
          m.mem.memory.allocations.map (·.addr),
          m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 255 },
        [true, false, false, false, false, false, false],
        [64, 128, 256, 384, 512, 2 ^ 32, 2 ^ 32],
        [1]) := by
  decide +kernel

def ordBoolCastTempMoveFalseArgs : List Value :=
  [.scalar ⟨251, 1⟩, .scalar ⟨3, 1⟩, .scalar ⟨0, 1⟩]
def ordBoolCastTempMoveFalseS0 : MachineState :=
  initMachineState ordBoolCastTempMove ordBoolCastTempMoveFalseArgs
def ordBoolCastTempMoveFalseMInit : Mach :=
  machineWithCtx ctxI8_4 ordBoolCastTempMove ordBoolCastTempMoveFn
    ordBoolCastTempMoveFalseS0.frame.locals ordBoolCastTempMoveFn.start

theorem ordBoolCastTempMoveFalse_anneal_ret :
    ReachesRet (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveFalseArgs)
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, ordBoolCastTempMoveFalseS0.memory)) :=
  runA_sound ordBoolCastTempMove 20 _ _ _ rfl

theorem ordBoolCastTempMoveFalse_noUB :
    MirNoUBTree (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveFalseArgs) :=
  runA_noUB ordBoolCastTempMove 20 _ _ _ rfl

theorem ordBoolCastTempMoveFalse_progress (n : Nat) :
    (∃ s' m' tr,
      Interp.steps (initLen ordBoolCastTempMove + n) ordBoolCastTempMoveFalseMInit = .ok m' ∧
      StateRel ordBoolCastTempMove ordBoolCastTempMoveFn ctxI8_4 s' m' ∧
      Reaches (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveFalseArgs) tr
        (mirTree ordBoolCastTempMove s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen ordBoolCastTempMove + n ∧
      Interp.steps k ordBoolCastTempMoveFalseMInit = .ok mRet ∧
      ReturnRel ordBoolCastTempMove ctxI8_4 s' v mRet ∧
      ReachesRet (mirCallTree ordBoolCastTempMove ordBoolCastTempMoveFalseArgs) tr
        (.normal (v, mem))) :=
  mirCall_progress ordBoolCastTempMove_inFragment ordBoolCastTempMove_translate ctxI8_4
    ctxI8_ok_ordBoolCastTempMove ordBoolCastTempMoveFalseArgs (by decide)
    ordBoolCastTempMoveFalseMInit rfl rfl rfl ordBoolCastTempMoveFalse_noUB n

theorem ordBoolCastTempMoveFalse_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n ordBoolCastTempMoveFalseMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 1 } ∧
      m'.threads = [thread1 ctxI8_4
        [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret ordBoolCastTempMove_inFragment ordBoolCastTempMove_translate ctxI8_4
      ctxI8_ok_ordBoolCastTempMove ordBoolCastTempMoveFalseArgs (by decide)
      ordBoolCastTempMoveFalseMInit rfl rfl rfl ordBoolCastTempMoveFalse_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [ordBoolCastTempMove] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem ordBoolCastTempMoveFalse_minirust_direct :
    (Interp.steps 12 ordBoolCastTempMoveFalseMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?,
          m.mem.memory.allocations.map (·.live),
          m.mem.memory.allocations.map (·.addr),
          m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 1 },
        [true, false, false, false, false, false, false],
        [64, 128, 256, 384, 512, 2 ^ 32, 2 ^ 32],
        [1]) := by
  decide +kernel

/-! ## Multi-function `Terminator::Call` & `Return` stack witnesses (`MR-4.1`) -/

/-- Extract `some msg` when an `Interp` computation stops with `.error (.ub msg)`. -/
def ubMsg? {α : Type} : Interp α → Option String
  | .error (.ub msg) => some msg
  | _ => none

private theorem eq_error_ub_of_ubMsg? {α : Type} {x : Interp α} {msg : String}
    (h : ubMsg? x = some msg) : x = .error (.ub msg) := by
  cases x with
  | ok _ => simp [ubMsg?] at h
  | error e =>
    cases e <;> simp [ubMsg?] at h ⊢
    exact h

/-- Direct-call function-item constant operand (`TyKind.fnDef dp []` with
`MirConstVal.zeroSized`), recognized by both `Translate.extractFnDefPath` and
`MirSemantics.extractCalleeDefPath?`. -/
def fnDefOp (dp : String) : Operand :=
  .constant { ty := { kind := .fnDef dp [], layoutIdx := 0 }, val := .zeroSized }

/-- Root caller context with `retA` at allocation index `0` (address `64`) and
`fnAllocs nFns` (`AllocationKind::Function` allocations at addresses `16 + k`
for `0 ≤ k < nFns`) at indices `1 .. nFns`, plus root locals at `addrs`. -/
def ctxWithFns (caller : Frame) (retA : Gen.Allocation) (nFns : Nat)
    (addrs : List Int) : Ctx :=
  { caller := caller, payloads := [], base := retA :: fnAllocs nFns,
    addrs := addrs, nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

/-- Multi-function MiniRust machine running `fEntry` from `prog` under caller
context `rootCtx` with `fnPtrMap 1 nFns` and initial Anneal locals `locals` at
`blk`. -/
def multiMachineWithCtx (rootCtx : Ctx) (prog : Gen.Program) (nFns : Nat)
    (entry : CapturedMir) (fEntry : Gen.Function) (locals : List LocalSlot)
    (blk : Gen.BbName) : Mach :=
  { prog := prog,
    mem := { memory := { allocations := rootCtx.base ++
                           localAllocs rootCtx
                             (entry.localDecls.take (entry.argCount + 1)) locals,
                         _phantom := {} },
             accesses := [] },
    intptrcast := ⟨⟨[]⟩⟩,
    threads := [thread1 rootCtx [rootCtx.caller,
      { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := blk }]],
    active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [], global_ptrs := ⟨[]⟩,
    fn_ptrs := fnPtrMap 1 nFns, vtable_ptrs := ⟨[]⟩, stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

/-! ### `callerMain` invoking `calleePair` (`ByValue` + `InPlace` args & `Call + initBlock`) -/

def tupleU32Layout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiCalleePair : FnAbi :=
  { args := [{ layout := u32Layout, mode := .direct },
      { layout := tupleU32Layout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn callee_pair(a: u32, pair: (u32, bool)) -> u32 {
    // unmarked _4: i8 allocated by callee initBlock (initLen = 2)
    let mut k: u32;             // bb0: StorageLive(_3); _3 = const 7_u32
    if pair.1 {                 //      switchInt(copy (_2.1)) -> [0: bb1, otherwise: bb2]
        a.wrapping_sub(k)       // bb2: _0 = Sub(copy _1, move _3); Deinit(_3); StorageDead(_3); return
    } else {
        pair.0.wrapping_add(k)  // bb1: _0 = Add(copy (_2.0), move _3); Deinit(_3); StorageDead(_3); return
    }
}
```
Having both an unmentioned unmarked local (`_4 : i8`, allocated in `calleePair`'s
`initBlock`, so `initLen calleePair = 2`) and a `StorageLive` local (`_3 : u32`)
makes entering `calleePair` take `3` MiniRust steps (`Terminator::Call` plus
`StorageLive(_4)` plus `Goto(bb0)`) for one Anneal `.tau` call step. -/
def calleePair : CapturedMir where
  defPath := "witness::callee_pair"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32BoolTupleDecl, u32Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.use (constU32 7)))],
      terminator := mkTerm (.switchInt (.copy (field1 2)) { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (field0U32 2)) (.move (local_ 3)))),
        mkStmt (.deinit (local_ 3)),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 1)) (.move (local_ 3)))),
        mkStmt (.deinit (local_ 3)),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCalleePair
  layouts := emptyLayoutTable
  allocations := []

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn caller_main(x: u32, y: u32) -> u32 {
    let pair = AddWithOverflow(x, y);   // bb0: StorageLive(_3); StorageLive(_4); _3 = AddWithOverflow(copy _1, copy _2)
    let r = callee_pair(x, move pair);  //      _4 = Call(callee_pair, [copy _1, move _3]) -> [return: bb1, unwind: continue]
    r.wrapping_add(x)                   // bb1: _0 = Add(move _4, copy _1); StorageDead(_4); StorageDead(_3); return
}
```
Passes `_1` by value (`ArgumentExpr::ByValue`, leaving `_1` live for `bb1`) and
`_3 : (u32, bool)` in place (`ArgumentExpr::InPlace`, deinitializing `_3` to
`Uninit` bytes in MiniRust memory before entering `calleePair`). -/
def callerMain : CapturedMir where
  defPath := "witness::caller_main"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32Decl, u32BoolTupleDecl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 3) (.binaryOp .addWithOverflow (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm (.call (fnDefOp "witness::callee_pair")
        [.copy (local_ 1), .move (local_ 3)] (local_ 4) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.move (local_ 4)) (.copy (local_ 1)))),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem callerCallee_inFragment : progInFragment callerMain [calleePair] = true := by decide

theorem calleePair_initLen : initLen calleePair = 2 := rfl

def callerMainFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, intBoolTupleTy u32), (localName 4, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3),
      .StorageLive (localName 4),
      .Assign (.Local (localName 3))
        (.BinOp (.IntWithOverflow .Add) (.Load (.Local (localName 1)))
          (.Load (.Local (localName 2))))],
      .Call (fnPtrExpr (fnName 1)) .Rust
        [.ByValue (.Load (.Local (localName 1))), .InPlace (.Local (localName 3))]
        (.Local (localName 4)) (some (bbName 1)) (some (bbName 3)), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 4))) (.Load (.Local (localName 1)))),
      .StorageDead (localName 4),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 2, ⟨[], .Goto (bbName 0), .Regular⟩),
    (bbName 3, ⟨[], .ResumeUnwind, .Cleanup⟩)]⟩
  start := bbName 2
  implicit_writes := true

def calleePairFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, intBoolTupleTy u32), (localName 3, .Int u32), (localName 4, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3),
      .Assign (.Local (localName 3)) (.Constant (.Int 7) (.Int u32))],
      .Switch (.UnOp (.Cast (.Transmute (.Int u8))) (.Load (.Field (.Local (localName 2)) 1)))
        ⟨[(0, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Field (.Local (localName 2)) 0))
          (.Load (.Local (localName 3)))),
      .Deinit (.Local (localName 3)),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 1))) (.Load (.Local (localName 3)))),
      .Deinit (.Local (localName 3)),
      .StorageDead (localName 3)],
      .Return, .Regular⟩),
    (bbName 3, ⟨[.StorageLive (localName 4)], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

def callerCalleeProg : Gen.Program where
  functions := ⟨[(fnName 0, callerMainFn), (fnName 1, calleePairFn), (fnName 2, mkStartFn 0)]⟩
  start := fnName 2
  globals := ⟨[]⟩
  vtables := ⟨[]⟩
  traits := ⟨[]⟩

theorem callerCallee_translate :
    translateProg callerMain [calleePair] = some callerCalleeProg := rfl

theorem callerMain_translateInProg :
    translateFnInProg (fnNameMap callerMain [calleePair]) callerMain = some callerMainFn := rfl

def ctxCallerMain : Ctx :=
  ctxWithFns callerFrame retAlloc 2 [128, 256, 384]

theorem ctxCallerMain_ok : CtxOk callerMain ctxCallerMain where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [callerMain] at hd; subst hd; decide
    | 1, _, hd => simp [callerMain] at hd; subst hd; decide
    | 2, _, hd => simp [callerMain] at hd; subst hd; decide
    | _ + 3, hi, _ => simp [callerMain] at hi
  ret := by
    intro d hd; simp [callerMain] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- Non-overflow call `(20u32, 5u32)`: `AddWithOverflow(20, 5) = (25, false)`,
`calleePair(20, (25, false)) = 25 + 7 = 32`, and `callerMain` returns
`32 + 20 = 52u32`. -/
def callerCallee20Args : List Value := [.scalar ⟨20, 4⟩, .scalar ⟨5, 4⟩]

def callerCallee20S0 : MachineState :=
  initMachineStateWithCallees callerMain callerCallee20Args [calleePair]

def callerCallee20MInit : Mach :=
  multiMachineWithCtx ctxCallerMain callerCalleeProg 2 callerMain callerMainFn
    callerCallee20S0.frame.locals callerMainFn.start

theorem callerCallee20_anneal_ret :
    ReachesRet (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair])
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨52, 4⟩,
        { callerCallee20S0.memory with activeCallee := some callerMain })) :=
  runA_sound callerMain 25 _ _ _ rfl

theorem callerCallee20_noUB :
    MirNoUBTree (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) :=
  runA_noUB callerMain 25 _ _ _ rfl

theorem callerCallee20_progress (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps (initLen callerMain + n) callerCallee20MInit = .ok m0 ∧
      Interp.steps (initLen callerMain + n + d) callerCallee20MInit = .ok m' ∧
      MultiStateRel callerMain [calleePair] callerCalleeProg ctxCallerMain s' m' ∧
      Reaches (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (mirTree callerMain s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen callerMain + n ∧
      Interp.steps k callerCallee20MInit = .ok mRet ∧
      ReturnRel callerMain ctxCallerMain s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (.normal (v, mem))) :=
  mirCallWithCallees_progress callerCallee_inFragment callerCallee_translate
    callerMain_translateInProg ctxCallerMain ctxCallerMain_ok callerCallee20Args (by decide)
    callerCallee20MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callerCallee20_noUB n

theorem callerCallee20_progress_any (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps n callerCallee20MInit = .ok m0 ∧
      Interp.steps (n + d) callerCallee20MInit = .ok m' ∧
      MultiStateRel callerMain [calleePair] callerCalleeProg ctxCallerMain s' m' ∧
      Reaches (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (mirTree callerMain s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧
      Interp.steps k callerCallee20MInit = .ok mRet ∧
      ReturnRel callerMain ctxCallerMain s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (.normal (v, mem))) :=
  mirCallWithCallees_progress_any callerCallee_inFragment callerCallee_translate
    callerMain_translateInProg ctxCallerMain ctxCallerMain_ok callerCallee20Args (by decide)
    callerCallee20MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callerCallee20_noUB n

theorem callerCallee20_outcome_any (n : Nat) :
    (∃ d s' m0 m' tr, Interp.steps n callerCallee20MInit = .ok m0 ∧
      Interp.steps (n + d) callerCallee20MInit = .ok m' ∧
      MultiStateRel callerMain [calleePair] callerCalleeProg ctxCallerMain s' m' ∧
      Reaches (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (mirTree callerMain s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n ∧
      Interp.steps k callerCallee20MInit = .ok mRet ∧
      ReturnRel callerMain ctxCallerMain s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr
        (.normal (v, mem))) ∨
    (∃ msg, Interp.steps n callerCallee20MInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTreeWithCallees callerMain callerCallee20Args [calleePair]) tr u ∧
        FaultNow u) :=
  mirCallWithCallees_outcome_any callerCallee_inFragment callerCallee_translate
    callerMain_translateInProg ctxCallerMain ctxCallerMain_ok callerCallee20Args (by decide)
    callerCallee20MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl n

theorem callerCallee20_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n callerCallee20MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 52 } ∧
      m'.threads = [thread1 ctxCallerMain
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret callerCallee_inFragment callerCallee_translate
      callerMain_translateInProg ctxCallerMain ctxCallerMain_ok callerCallee20Args (by decide)
      callerCallee20MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      callerCallee20_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [callerMain] at hd; subst hd
  simp [retPtr, ctxCallerMain, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallerMain, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- Mid-call snapshot right after `Terminator::Call` (step `5`, before
`calleePair`'s 2-step `initBlock` completes): the thread stack has depth `3`
(`[callerFrame, callerMainFn, calleePairFn]`), and `callerMain`'s moved tuple
local `_3` (allocation `6`) has been deinitialized to 8 `Uninit` bytes by
`ArgumentExpr::InPlace`. -/
theorem callerCallee20_midCall_step5 :
    (Interp.steps 5 callerCallee20MInit).toOption.map
        (fun m => (m.threads.map (·.stack.length),
          (m.mem.memory.allocations[6]?).map (·.data))) =
      some ([3], some (List.replicate 8 .Uninit)) := by
  decide +kernel

theorem callerCallee20_minirust_direct :
    (Interp.steps 18 callerCallee20MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 52 }, [1]) := by
  decide +kernel

/-- Overflow call `(u32::MAX, 5u32)`: `AddWithOverflow(4294967295, 5) = (4, true)`,
`calleePair` takes `bb2` (`4294967295 - 7 = 4294967288`), and `callerMain`
returns `4294967288.wrapping_add(4294967295) = 4294967287u32`. -/
def callerCalleeOvArgs : List Value := [.scalar ⟨4294967295, 4⟩, .scalar ⟨5, 4⟩]

def callerCalleeOvS0 : MachineState :=
  initMachineStateWithCallees callerMain callerCalleeOvArgs [calleePair]

def callerCalleeOvMInit : Mach :=
  multiMachineWithCtx ctxCallerMain callerCalleeProg 2 callerMain callerMainFn
    callerCalleeOvS0.frame.locals callerMainFn.start

theorem callerCalleeOv_anneal_ret :
    ReachesRet (mirCallTreeWithCallees callerMain callerCalleeOvArgs [calleePair])
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨4294967287, 4⟩,
        { callerCalleeOvS0.memory with activeCallee := some callerMain })) :=
  runA_sound callerMain 25 _ _ _ rfl

theorem callerCalleeOv_noUB :
    MirNoUBTree (mirCallTreeWithCallees callerMain callerCalleeOvArgs [calleePair]) :=
  runA_noUB callerMain 25 _ _ _ rfl

theorem callerCalleeOv_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n callerCalleeOvMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? =
        some { retAlloc with data := scalarBytes u32 4294967287 } ∧
      m'.threads = [thread1 ctxCallerMain
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret callerCallee_inFragment callerCallee_translate
      callerMain_translateInProg ctxCallerMain ctxCallerMain_ok callerCalleeOvArgs (by decide)
      callerCalleeOvMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      callerCalleeOv_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [callerMain] at hd; subst hd
  simp [retPtr, ctxCallerMain, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallerMain, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem callerCalleeOv_minirust_direct :
    (Interp.steps 18 callerCalleeOvMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 4294967287 }, [1]) := by
  decide +kernel

/-! ### Projected tuple-field call destinations & sequential multi-call reuse -/

def fnAbiBool1 : FnAbi :=
  { args := [{ layout := boolLayout, mode := .direct }],
    ret := { layout := boolLayout, mode := .direct }, conv := .rust, canUnwind := false }

def negI8Callee : CapturedMir where
  defPath := "witness::neg_i8_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

def flipBoolCallee : CapturedMir where
  defPath := "witness::flip_bool_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [boolDecl, boolDecl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.unaryOp .not (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiBool1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller writing sequential call results into projected fields `_0.0`
(`CallerDestRel.field0`, `UnwindAction.unreachable`, preserving `_0.1`) and
`_0.1` (`CallerDestRel.field1`, `UnwindAction.terminate`, preserving `_0.0`) of
an initialized `(i8, bool)` return local `_0`. -/
def projDestCaller : CapturedMir where
  defPath := "witness::proj_dest_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8BoolTupleDecl, i8Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .addWithOverflow (.copy (local_ 1)) (constI8 1)))],
      terminator := mkTerm (.call (fnDefOp "witness::neg_i8_callee")
        [.copy (local_ 1)] (field0I8 0) (some 1) .unreachable),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (.copy (field1 0))))],
      terminator := mkTerm (.call (fnDefOp "witness::flip_bool_callee")
        [.copy (local_ 2)] (field1 0) (some 2) .terminate),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem projDestCaller_inFragment :
    progInFragment projDestCaller [negI8Callee, flipBoolCallee] = true := by decide

def retAllocTupleI8 : Gen.Allocation :=
  { data := List.replicate 2 .Uninit, addr := 64, align := ⟨1⟩, kind := .Stack, live := true,
    extra := () }

def callerFnTupleI8 : Gen.Function where
  locals := ⟨[(localName 0, intBoolTupleTy i8)]⟩
  args := []
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[]⟩
  start := bbName 0
  implicit_writes := true

def callerFrameTupleI8 : Frame :=
  { func := callerFnTupleI8, locals := ⟨[(localName 0, retPtr)]⟩,
    stack_pop_action := .BottomOfStack, next_block := bbName 0, next_stmt := 0, extra := () }

def ctxProjDest : Ctx :=
  ctxWithFns callerFrameTupleI8 retAllocTupleI8 3 [128, 256]

theorem ctxProjDest_ok : CtxOk projDestCaller ctxProjDest where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [projDestCaller] at hd; subst hd; decide
    | 1, _, hd => simp [projDestCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [projDestCaller] at hi
  ret := by
    intro d hd; simp [projDestCaller] at hd; subst hd
    exact ⟨0, retAllocTupleI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

def projDestProg : Gen.Program :=
  (translateProg projDestCaller [negI8Callee, flipBoolCallee]).getD emptyProg

def projDestCallerFn : Gen.Function :=
  (translateFnInProg (fnNameMap projDestCaller [negI8Callee, flipBoolCallee])
    projDestCaller).getD callerFnTupleI8

theorem projDest_translate :
    translateProg projDestCaller [negI8Callee, flipBoolCallee] = some projDestProg := rfl

theorem projDestCaller_translateInProg :
    translateFnInProg (fnNameMap projDestCaller [negI8Callee, flipBoolCallee]) projDestCaller =
      some projDestCallerFn := rfl

/-- Input `127i8`: `AddWithOverflow(127i8, 1i8) = (-128i8, true)`,
`negI8Callee(127i8)` overwrites `_0.0` with `-127i8` (bits `129`) while leaving
`_0.1 = true`, and `flipBoolCallee(true)` overwrites `_0.1` with `false` while
leaving `_0.0 = -127i8`. -/
def projDest127Args : List Value := [.scalar ⟨127, 1⟩]

def projDest127S0 : MachineState :=
  initMachineStateWithCallees projDestCaller projDest127Args [negI8Callee, flipBoolCallee]

def projDest127MInit : Mach :=
  multiMachineWithCtx ctxProjDest projDestProg 3 projDestCaller projDestCallerFn
    projDest127S0.frame.locals projDestCallerFn.start

theorem projDest127_anneal_ret :
    ReachesRet
      (mirCallTreeWithCallees projDestCaller projDest127Args [negI8Callee, flipBoolCallee]) []
      (.normal (.aggregate 0 [.scalar ⟨129, 1⟩, .scalar ⟨0, 1⟩],
        { projDest127S0.memory with activeCallee := some projDestCaller })) :=
  runA_sound projDestCaller 25 _ _ _ rfl

theorem projDest127_noUB :
    MirNoUBTree
      (mirCallTreeWithCallees projDestCaller projDest127Args [negI8Callee, flipBoolCallee]) :=
  runA_noUB projDestCaller 25 _ _ _ rfl

theorem projDest127_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n projDest127MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? =
        some { retAllocTupleI8 with data := scalarBytes i8 129 ++ scalarBytes u8 0 } ∧
      m'.threads = [thread1 ctxProjDest
        [{ callerFrameTupleI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret projDestCaller_inFragment projDest_translate
      projDestCaller_translateInProg ctxProjDest ctxProjDest_ok projDest127Args (by decide)
      projDest127MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      projDest127_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [projDestCaller] at hd; subst hd
  simp [retPtr, ctxProjDest, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxProjDest, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem projDest127_minirust_direct :
    (Interp.steps 13 projDest127MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocTupleI8 with data := scalarBytes i8 129 ++ scalarBytes u8 0 },
        [1]) := by
  decide +kernel

/-! ### 3-deep nested call stack & `Ordering` enum ABI (`chainEntry -> chainMid -> chainLeaf`) -/

def chainLeaf : CapturedMir where
  defPath := "witness::chain_leaf"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [orderingDecl, i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .cmp (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 2
  layouts := emptyLayoutTable
  allocations := []

def chainMid : CapturedMir where
  defPath := "witness::chain_mid"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [orderingDecl, i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.unaryOp .neg (.copy (local_ 1))))],
      terminator := mkTerm (.call (fnDefOp "witness::chain_leaf")
        [.copy (local_ 1), .move (local_ 2)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

def chainEntry : CapturedMir where
  defPath := "witness::chain_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [orderingDecl, i8Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::chain_mid")
        [.move (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem chain3_inFragment :
    progInFragment chainEntry [chainMid, chainLeaf] = true := by decide

theorem chain3_maxStackLocals :
    maxStackLocals chainEntry [chainMid, chainLeaf] = some 8 := rfl

def ctxChainEntry : Ctx :=
  ctxWithFns callerFrameI8 retAllocI8 3 [128, 256]

theorem ctxChainEntry_ok : CtxOk chainEntry ctxChainEntry where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [chainEntry] at hd; subst hd; decide
    | 1, _, hd => simp [chainEntry] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [chainEntry] at hi
  ret := by
    intro d hd; simp [chainEntry] at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

def chain3Prog : Gen.Program :=
  (translateProg chainEntry [chainMid, chainLeaf]).getD emptyProg

def chainEntryFn : Gen.Function :=
  (translateFnInProg (fnNameMap chainEntry [chainMid, chainLeaf]) chainEntry).getD callerFn

theorem chain3_translate :
    translateProg chainEntry [chainMid, chainLeaf] = some chain3Prog := rfl

theorem chainEntry_translateInProg :
    translateFnInProg (fnNameMap chainEntry [chainMid, chainLeaf]) chainEntry =
      some chainEntryFn := rfl

/-- Input `-5i8` (bits `251`): `chainEntry(-5)` calls `chainMid(-5)`, which
computes `-(-5) = 5` and calls `chainLeaf(-5, 5)`, returning `Ordering::Less`
(`-1i8`, byte `255`) back through all three frames. -/
def chainNeg5Args : List Value := [.scalar ⟨251, 1⟩]

def chainNeg5S0 : MachineState :=
  initMachineStateWithCallees chainEntry chainNeg5Args [chainMid, chainLeaf]

def chainNeg5MInit : Mach :=
  multiMachineWithCtx ctxChainEntry chain3Prog 3 chainEntry chainEntryFn
    chainNeg5S0.frame.locals chainEntryFn.start

theorem chainNeg5_anneal_ret :
    ReachesRet (mirCallTreeWithCallees chainEntry chainNeg5Args [chainMid, chainLeaf]) []
      (.normal (.scalar ⟨255, 1⟩,
        { chainNeg5S0.memory with activeCallee := some chainEntry })) :=
  runA_sound chainEntry 25 _ _ _ rfl

theorem chainNeg5_noUB :
    MirNoUBTree (mirCallTreeWithCallees chainEntry chainNeg5Args [chainMid, chainLeaf]) :=
  runA_noUB chainEntry 25 _ _ _ rfl

theorem chainNeg5_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n chainNeg5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 255 } ∧
      m'.threads = [thread1 ctxChainEntry
        [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret chain3_inFragment chain3_translate
      chainEntry_translateInProg ctxChainEntry ctxChainEntry_ok chainNeg5Args (by decide)
      chainNeg5MInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      chainNeg5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [chainEntry] at hd; subst hd
  simp [retPtr, ctxChainEntry, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxChainEntry, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- At step `7`, all three translated functions (`chainEntryFn`, `chainMidFn`,
and `chainLeafFn`) are live on the MiniRust call stack above `callerFrameI8`
(stack depth `4`). -/
theorem chainNeg5_depth4_step7 :
    (Interp.steps 7 chainNeg5MInit).toOption.map (fun m => m.threads.map (·.stack.length)) =
      some [4] := by
  decide +kernel

theorem chainNeg5_minirust_direct :
    (Interp.steps 11 chainNeg5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 255 }, [1]) := by
  decide +kernel

/-! ### Multi-frame UB propagation (call-argument UB and callee-body UB) -/

def idU32Callee : CapturedMir where
  defPath := "witness::id_u32_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller passing an uninitialized local `copy _1` as a call argument to
`idU32Callee`: both semantics raise UB during argument evaluation before
entering `idU32Callee`. -/
def callArgUbCaller : CapturedMir where
  defPath := "witness::call_arg_ub_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 1)],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem callArgUb_inFragment :
    progInFragment callArgUbCaller [idU32Callee] = true := by decide

def ctxCallArgUb : Ctx :=
  ctxWithFns callerFrame retAlloc 2 [128]

theorem ctxCallArgUb_ok : CtxOk callArgUbCaller ctxCallArgUb where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [callArgUbCaller] at hd; subst hd; decide
    | _ + 1, hi, _ => simp [callArgUbCaller] at hi
  ret := by
    intro d hd; simp [callArgUbCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def callArgUbProg : Gen.Program :=
  (translateProg callArgUbCaller [idU32Callee]).getD emptyProg

def callArgUbCallerFn : Gen.Function :=
  (translateFnInProg (fnNameMap callArgUbCaller [idU32Callee]) callArgUbCaller).getD callerFn

theorem callArgUb_translate :
    translateProg callArgUbCaller [idU32Callee] = some callArgUbProg := rfl

theorem callArgUbCaller_translateInProg :
    translateFnInProg (fnNameMap callArgUbCaller [idU32Callee]) callArgUbCaller =
      some callArgUbCallerFn := rfl

def callArgUbS0 : MachineState :=
  initMachineStateWithCallees callArgUbCaller [] [idU32Callee]

def callArgUbMInit : Mach :=
  multiMachineWithCtx ctxCallArgUb callArgUbProg 2 callArgUbCaller callArgUbCallerFn
    callArgUbS0.frame.locals callArgUbCallerFn.start

theorem callArgUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr u ∧ FaultNow u :=
  faultsA_sound callArgUbCaller 5 _ (by decide)

theorem callArgUb_minirust_ub :
    ∃ (n : Nat) (msg : String), Interp.steps n callArgUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := callArgUb_anneal_ub
  exact mirCallWithCallees_ub callArgUb_inFragment callArgUb_translate
    callArgUbCaller_translateInProg ctxCallArgUb ctxCallArgUb_ok [] (by decide)
    callArgUbMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf

theorem callArgUb_minirust_direct :
    Interp.steps 3 callArgUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

theorem callArgUb_converse_error :
    (∃ msg,
      Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr u ∧
        FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 3 ∧ Interp.steps k callArgUbMInit = .ok mRet ∧
      ReturnRel callArgUbCaller ctxCallArgUb s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr
        (.normal (v, mem))) :=
  mirCallWithCallees_steps_error callArgUb_inFragment callArgUb_translate
    callArgUbCaller_translateInProg ctxCallArgUb ctxCallArgUb_ok [] (by decide)
    callArgUbMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callArgUb_minirust_direct

theorem callArgUb_outcome :
    (∃ d s' m0 m' tr, Interp.steps (initLen callArgUbCaller + 1) callArgUbMInit = .ok m0 ∧
      Interp.steps (initLen callArgUbCaller + 1 + d) callArgUbMInit = .ok m' ∧
      MultiStateRel callArgUbCaller [idU32Callee] callArgUbProg ctxCallArgUb s' m' ∧
      Reaches (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr
        (mirTree callArgUbCaller s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen callArgUbCaller + 1 ∧
      Interp.steps k callArgUbMInit = .ok mRet ∧
      ReturnRel callArgUbCaller ctxCallArgUb s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr
        (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (initLen callArgUbCaller + 1) callArgUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTreeWithCallees callArgUbCaller [] [idU32Callee]) tr u ∧
        FaultNow u) :=
  mirCallWithCallees_outcome callArgUb_inFragment callArgUb_translate
    callArgUbCaller_translateInProg ctxCallArgUb ctxCallArgUb_ok [] (by decide)
    callArgUbMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl 1

/-- Callee faulting with division-by-zero inside a pushed stack frame. -/
def divTenI8Callee : CapturedMir where
  defPath := "witness::div_ten_i8_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .div (constI8 10) (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

def calleeDivZeroCaller : CapturedMir where
  defPath := "witness::callee_div_zero_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::div_ten_i8_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem calleeDivZero_inFragment :
    progInFragment calleeDivZeroCaller [divTenI8Callee] = true := by decide

def ctxCalleeDivZero : Ctx :=
  ctxWithFns callerFrameI8 retAllocI8 2 [128, 256]

theorem ctxCalleeDivZero_ok : CtxOk calleeDivZeroCaller ctxCalleeDivZero where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [calleeDivZeroCaller] at hd; subst hd; decide
    | 1, _, hd => simp [calleeDivZeroCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [calleeDivZeroCaller] at hi
  ret := by
    intro d hd; simp [calleeDivZeroCaller] at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

def calleeDivZeroProg : Gen.Program :=
  (translateProg calleeDivZeroCaller [divTenI8Callee]).getD emptyProg

def calleeDivZeroCallerFn : Gen.Function :=
  (translateFnInProg (fnNameMap calleeDivZeroCaller [divTenI8Callee])
    calleeDivZeroCaller).getD callerFn

theorem calleeDivZero_translate :
    translateProg calleeDivZeroCaller [divTenI8Callee] = some calleeDivZeroProg := rfl

theorem calleeDivZeroCaller_translateInProg :
    translateFnInProg (fnNameMap calleeDivZeroCaller [divTenI8Callee]) calleeDivZeroCaller =
      some calleeDivZeroCallerFn := rfl

def calleeDivZeroArgs : List Value := [.scalar ⟨0, 1⟩]

def calleeDivZeroS0 : MachineState :=
  initMachineStateWithCallees calleeDivZeroCaller calleeDivZeroArgs [divTenI8Callee]

def calleeDivZeroMInit : Mach :=
  multiMachineWithCtx ctxCalleeDivZero calleeDivZeroProg 2 calleeDivZeroCaller
    calleeDivZeroCallerFn calleeDivZeroS0.frame.locals calleeDivZeroCallerFn.start

theorem calleeDivZero_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees calleeDivZeroCaller calleeDivZeroArgs [divTenI8Callee]) tr u ∧
      FaultNow u :=
  faultsA_sound calleeDivZeroCaller 10 _ (by decide)

theorem calleeDivZero_minirust_ub :
    ∃ (n : Nat) (msg : String), Interp.steps n calleeDivZeroMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := calleeDivZero_anneal_ub
  exact mirCallWithCallees_ub calleeDivZero_inFragment calleeDivZero_translate
    calleeDivZeroCaller_translateInProg ctxCalleeDivZero ctxCalleeDivZero_ok calleeDivZeroArgs
    (by decide) calleeDivZeroMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf

theorem calleeDivZero_minirust_direct :
    Interp.steps 4 calleeDivZeroMInit = .error (.ub "division by zero") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

theorem calleeDivZero_converse_error :
    (∃ msg, Stop.ub "division by zero" = .ub msg ∧
      ∃ tr u, Reaches
        (mirCallTreeWithCallees calleeDivZeroCaller calleeDivZeroArgs [divTenI8Callee]) tr u ∧
        FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 4 ∧ Interp.steps k calleeDivZeroMInit = .ok mRet ∧
      ReturnRel calleeDivZeroCaller ctxCalleeDivZero s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees calleeDivZeroCaller calleeDivZeroArgs [divTenI8Callee])
        tr (.normal (v, mem))) :=
  mirCallWithCallees_steps_error calleeDivZero_inFragment calleeDivZero_translate
    calleeDivZeroCaller_translateInProg ctxCalleeDivZero ctxCalleeDivZero_ok calleeDivZeroArgs
    (by decide) calleeDivZeroMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    calleeDivZero_minirust_direct

/-! ### Diverging multi-function call loop (`callSpinCaller` calling `idU32Callee`) -/

/-- Diverging caller `StorageLive(_2); loop { _2 = copy _1; _1 = id_u32_callee(move _2); }`:
the static call graph `callSpinCaller -> idU32Callee` is acyclic, and each
iteration pushes and pops `idU32Callee` cleanly without unbounded stack growth. -/
def callSpinCaller : CapturedMir where
  defPath := "witness::call_spin_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2)],
      terminator := mkTerm (.goto 1),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2) (.use (.copy (local_ 1))))],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.move (local_ 2)] (local_ 1) (some 1) .continue_),
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callSpin_inFragment :
    progInFragment callSpinCaller [idU32Callee] = true := by decide

def ctxCallSpin : Ctx :=
  ctxWithFns callerFrame retAlloc 2 [128, 256]

theorem ctxCallSpin_ok : CtxOk callSpinCaller ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [callSpinCaller] at hd; subst hd; decide
    | 1, _, hd => simp [callSpinCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [callSpinCaller] at hi
  ret := by
    intro d hd; simp [callSpinCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def callSpinProg : Gen.Program :=
  (translateProg callSpinCaller [idU32Callee]).getD emptyProg

def callSpinCallerFn : Gen.Function :=
  (translateFnInProg (fnNameMap callSpinCaller [idU32Callee]) callSpinCaller).getD callerFn

theorem callSpin_translate :
    translateProg callSpinCaller [idU32Callee] = some callSpinProg := rfl

theorem callSpinCaller_translateInProg :
    translateFnInProg (fnNameMap callSpinCaller [idU32Callee]) callSpinCaller =
      some callSpinCallerFn := rfl

def callSpinArgs : List Value := [.scalar ⟨0, 4⟩]

def callSpinS0 : MachineState :=
  initMachineStateWithCallees callSpinCaller callSpinArgs [idU32Callee]

private def nextSpinState (s : MachineState) : MachineState :=
  match stepMirFn callSpinCaller s with
  | .tau (.running s') => s'
  | _ => s

private def callSpinS1 : MachineState := nextSpinState callSpinS0

private def callSpinS2 : MachineState := nextSpinState callSpinS1

private def callSpinS3 : MachineState := nextSpinState callSpinS2

private def callSpinS4 : MachineState := nextSpinState callSpinS3

private def callSpinS5 : MachineState := nextSpinState callSpinS4

private def callSpinS6 : MachineState := nextSpinState callSpinS5

private def callSpinS7 : MachineState := nextSpinState callSpinS6

/-- Eight-state silent-step invariant for `callSpinCaller`:
`S0 -> S1 -> S2 -> S3` on entry (`activeCallee = none`), entering the 4-state
call/return cycle `S4 -> S5 -> S6 -> S7 -> S4`. -/
def CallSpinInv (s : MachineState) : Prop :=
  s = callSpinS0 ∨ s = callSpinS1 ∨ s = callSpinS2 ∨ s = callSpinS3 ∨
  s = callSpinS4 ∨ s = callSpinS5 ∨ s = callSpinS6 ∨ s = callSpinS7

private theorem callSpin_step (s : MachineState) (h : CallSpinInv s) :
    ∃ s', stepMirFn callSpinCaller s = .tau (.running s') ∧ CallSpinInv s' := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨callSpinS1, rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨callSpinS2, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨callSpinS3, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · exact ⟨callSpinS4, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  · exact ⟨callSpinS5, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  · exact ⟨callSpinS6, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
  · exact ⟨callSpinS7, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))⟩
  · exact ⟨callSpinS4, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩

def callSpinMInit : Mach :=
  multiMachineWithCtx ctxCallSpin callSpinProg 2 callSpinCaller callSpinCallerFn
    callSpinS0.frame.locals callSpinCallerFn.start

theorem callSpin_noUB :
    MirNoUBTree (mirCallTreeWithCallees callSpinCaller callSpinArgs [idU32Callee]) :=
  treeSafe_of_tau_inv callSpin_step (Or.inl rfl)

theorem callSpin_noRet (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet (mirCallTreeWithCallees callSpinCaller callSpinArgs [idU32Callee]) tr o :=
  noRet_of_tau_inv callSpin_step (Or.inl rfl) tr o

theorem callSpin_minirust_diverges (n : Nat) :
    ∃ m', Interp.steps n callSpinMInit = .ok m' :=
  mirCallWithCallees_diverges_steps_ok callSpin_inFragment callSpin_translate
    callSpinCaller_translateInProg ctxCallSpin ctxCallSpin_ok callSpinArgs (by decide)
    callSpinMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callSpin_noUB callSpin_noRet n

theorem callSpin_minirust_diverges_rel (n : Nat) :
    ∃ d s' m0 m' tr, Interp.steps (initLen callSpinCaller + n) callSpinMInit = .ok m0 ∧
      Interp.steps (initLen callSpinCaller + n + d) callSpinMInit = .ok m' ∧
      MultiStateRel callSpinCaller [idU32Callee] callSpinProg ctxCallSpin s' m' ∧
      Reaches (mirCallTreeWithCallees callSpinCaller callSpinArgs [idU32Callee]) tr
        (mirTree callSpinCaller s') :=
  mirCallWithCallees_diverges_rel callSpin_inFragment callSpin_translate
    callSpinCaller_translateInProg ctxCallSpin ctxCallSpin_ok callSpinArgs (by decide)
    callSpinMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callSpin_noUB callSpin_noRet n

/-! ### Soundness-boundary counterexamples (`progInFragment = false`) -/

/-- Counterexample 1 (`_1 = idU32Callee(copy _1)`): return place `_1` aliases
argument `copy _1`. Anneal evaluates `copy _1` before writing `_1` on return and
succeeds, whereas MiniRust's `Terminator::Call` runs
`prepare_for_inplace_passing(_1)` (writing `Uninit`) BEFORE `eval_argument`
loads `_1`, faulting with UB! `callTerminatorOk` rightly rejects this. -/
def callDestArgAlias : CapturedMir where
  defPath := "witness::call_dest_arg_alias"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (local_ 1)] (local_ 1) (some 1) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callDestArgAlias_movesOk : movesOk callDestArgAlias = false := by decide

theorem callDestArgAlias_rejected :
    progInFragment callDestArgAlias [idU32Callee] = false := by decide

def callDestArgAliasProg : Gen.Program :=
  (translateProg callDestArgAlias [idU32Callee]).getD emptyProg

def callDestArgAliasFn : Gen.Function :=
  (translateFnInProg (fnNameMap callDestArgAlias [idU32Callee]) callDestArgAlias).getD callerFn

theorem callDestArgAlias_translate :
    translateProg callDestArgAlias [idU32Callee] = some callDestArgAliasProg := rfl

def callDestArgAliasS0 : MachineState :=
  initMachineStateWithCallees callDestArgAlias [.scalar ⟨7, 4⟩] [idU32Callee]

def callDestArgAliasMInit : Mach :=
  multiMachineWithCtx ctxCallerMain callDestArgAliasProg 2 callDestArgAlias callDestArgAliasFn
    callDestArgAliasS0.frame.locals callDestArgAliasFn.start

theorem callDestArgAlias_anneal_ret :
    ReachesRet (mirCallTreeWithCallees callDestArgAlias [.scalar ⟨7, 4⟩] [idU32Callee]) []
      (.normal (.scalar ⟨7, 4⟩,
        { callDestArgAliasS0.memory with activeCallee := some callDestArgAlias })) :=
  runA_sound callDestArgAlias 10 _ _ _ rfl

theorem callDestArgAlias_minirust_ub :
    Interp.steps 2 callDestArgAliasMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

/-- Counterexample 2 (`_2 = idU32Callee(move (_1.0)); _0 = copy (_1.0)`):
projected `move (_1.0)` in a call argument leaves `_1` intact in Anneal's
`evalOperand` (which only deinitializes root moves), whereas MiniRust translates
`Operand::Move(_1.0)` to `ArgumentExpr::InPlace (.Field (.Local _1) 0)` and
deinitializes `_1.0`, faulting when `bb1` reads `copy (_1.0)`! `callArgOk`
rightly restricts `Operand::Move` call arguments to root locals. -/
def callProjMoveReuse : CapturedMir where
  defPath := "witness::call_proj_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32BoolTupleDecl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2)],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.move (field0U32 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (field0U32 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callProjMoveReuse_rejected :
    progInFragment callProjMoveReuse [idU32Callee] = false := by decide

def callProjMoveReuseProg : Gen.Program :=
  (translateProg callProjMoveReuse [idU32Callee]).getD emptyProg

def callProjMoveReuseFn : Gen.Function :=
  (translateFnInProg (fnNameMap callProjMoveReuse [idU32Callee]) callProjMoveReuse).getD callerFn

theorem callProjMoveReuse_translate :
    translateProg callProjMoveReuse [idU32Callee] = some callProjMoveReuseProg := rfl

def callProjMoveReuseArgs : List Value := [.aggregate 0 [.scalar ⟨9, 4⟩, .scalar ⟨1, 1⟩]]

def callProjMoveReuseS0 : MachineState :=
  initMachineStateWithCallees callProjMoveReuse callProjMoveReuseArgs [idU32Callee]

def callProjMoveReuseMInit : Mach :=
  multiMachineWithCtx ctxCallerMain callProjMoveReuseProg 2 callProjMoveReuse
    callProjMoveReuseFn callProjMoveReuseS0.frame.locals callProjMoveReuseFn.start

theorem callProjMoveReuse_anneal_ret :
    ReachesRet
      (mirCallTreeWithCallees callProjMoveReuse callProjMoveReuseArgs [idU32Callee]) []
      (.normal (.scalar ⟨9, 4⟩,
        { callProjMoveReuseS0.memory with activeCallee := some callProjMoveReuse })) :=
  runA_sound callProjMoveReuse 10 _ _ _ rfl

theorem callProjMoveReuse_minirust_ub :
    Interp.steps 7 callProjMoveReuseMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

/-- Post-call root-`move` reuse (`StorageLive(_2); _2 = idU32Callee(move _1);
_0 = copy _1`): because `ArgumentExpr::InPlace` writes `Uninit` to `_1` in
MiniRust just as `evalOperand` sets `_1` to `.uninit` in Anneal (`_1` is not
stale!), `callMoveReuse` is IN `progInFragment`, and BOTH forward UB transfer
(`mirCallWithCallees_ub`) and converse error soundness
(`mirCallWithCallees_steps_error`) apply on `bb1`'s `copy _1`. -/
def callMoveReuse : CapturedMir where
  defPath := "witness::call_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2)],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.move (local_ 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem callMoveReuse_inFragment :
    progInFragment callMoveReuse [idU32Callee] = true := by decide

theorem callMoveReuse_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees callMoveReuse [.scalar ⟨7, 4⟩] [idU32Callee]) tr u ∧ FaultNow u :=
  faultsA_sound callMoveReuse 10 _ (by decide)

def callMoveReuseProg : Gen.Program :=
  (translateProg callMoveReuse [idU32Callee]).getD emptyProg

def callMoveReuseFn : Gen.Function :=
  (translateFnInProg (fnNameMap callMoveReuse [idU32Callee]) callMoveReuse).getD callerFn

theorem callMoveReuse_translate :
    translateProg callMoveReuse [idU32Callee] = some callMoveReuseProg := rfl

theorem callMoveReuse_translateInProg :
    translateFnInProg (fnNameMap callMoveReuse [idU32Callee]) callMoveReuse =
      some callMoveReuseFn := rfl

def callMoveReuseMInit : Mach :=
  multiMachineWithCtx ctxCallSpin callMoveReuseProg 2 callMoveReuse callMoveReuseFn
    (initMachineStateWithCallees callMoveReuse [.scalar ⟨7, 4⟩] [idU32Callee]).frame.locals
    callMoveReuseFn.start

theorem ctxCallMoveReuse_ok : CtxOk callMoveReuse ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [callMoveReuse] at hd; subst hd; decide
    | 1, _, hd => simp [callMoveReuse] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [callMoveReuse] at hi
  ret := by
    intro d hd; simp [callMoveReuse] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem callMoveReuse_minirust_ub :
    ∃ (n : Nat) (msg : String), Interp.steps n callMoveReuseMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := callMoveReuse_anneal_ub
  exact mirCallWithCallees_ub callMoveReuse_inFragment callMoveReuse_translate
    callMoveReuse_translateInProg ctxCallSpin ctxCallMoveReuse_ok
    [.scalar ⟨7, 4⟩] (by decide) callMoveReuseMInit
    (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf

theorem callMoveReuse_minirust_direct :
    Interp.steps 7 callMoveReuseMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

theorem callMoveReuse_converse_error :
    (∃ msg,
      Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u,
        Reaches (mirCallTreeWithCallees callMoveReuse [.scalar ⟨7, 4⟩] [idU32Callee]) tr u ∧
          FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 7 ∧ Interp.steps k callMoveReuseMInit = .ok mRet ∧
      ReturnRel callMoveReuse ctxCallSpin s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callMoveReuse [.scalar ⟨7, 4⟩] [idU32Callee]) tr
        (.normal (v, mem))) :=
  mirCallWithCallees_steps_error callMoveReuse_inFragment callMoveReuse_translate
    callMoveReuse_translateInProg ctxCallSpin ctxCallMoveReuse_ok
    [.scalar ⟨7, 4⟩] (by decide) callMoveReuseMInit
    (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    callMoveReuse_minirust_direct

/-- Root-destination call re-initialization (`StorageLive(_2); _2 = move _1;
_1 = idU32Callee(copy _2); _0 = copy _1; StorageDead(_2); Return`): `_1` is
moved out by `_2 = move _1` (entering `mo`), then completely overwritten by the
root destination of `_1 = idU32Callee(copy _2)` (`termMoved` clears `_1` from
`mo`, and `termReadsOk` allows `_1 ∈ mo` on root destinations `⟨dst, []⟩`). -/
def moveReinitByCall : CapturedMir where
  defPath := "witness::move_reinit_by_call"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (.move (local_ 1))))],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (local_ 2)] (local_ 1) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem moveReinitByCall_inFragment :
    progInFragment moveReinitByCall [idU32Callee] = true := by decide

def moveReinitByCallProg : Gen.Program :=
  (translateProg moveReinitByCall [idU32Callee]).getD emptyProg

def moveReinitByCallFn : Gen.Function :=
  (translateFnInProg (fnNameMap moveReinitByCall [idU32Callee]) moveReinitByCall).getD callerFn

theorem moveReinitByCall_translate :
    translateProg moveReinitByCall [idU32Callee] = some moveReinitByCallProg := rfl

theorem moveReinitByCall_translateInProg :
    translateFnInProg (fnNameMap moveReinitByCall [idU32Callee]) moveReinitByCall =
      some moveReinitByCallFn := rfl

def moveReinitByCallS0 : MachineState :=
  initMachineStateWithCallees moveReinitByCall [.scalar ⟨55, 4⟩] [idU32Callee]

def moveReinitByCallMInit : Mach :=
  multiMachineWithCtx ctxCallSpin moveReinitByCallProg 2 moveReinitByCall moveReinitByCallFn
    moveReinitByCallS0.frame.locals moveReinitByCallFn.start

theorem ctxMoveReinitByCall_ok : CtxOk moveReinitByCall ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [moveReinitByCall] at hd; subst hd; decide
    | 1, _, hd => simp [moveReinitByCall] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [moveReinitByCall] at hi
  ret := by
    intro d hd; simp [moveReinitByCall] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem moveReinitByCall_anneal_ret :
    ReachesRet (mirCallTreeWithCallees moveReinitByCall [.scalar ⟨55, 4⟩] [idU32Callee]) []
      (.normal (.scalar ⟨55, 4⟩,
        { moveReinitByCallS0.memory with activeCallee := some moveReinitByCall })) :=
  runA_sound moveReinitByCall 20 _ _ _ rfl

theorem moveReinitByCall_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n moveReinitByCallMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 55 } ∧
      m'.threads = [thread1 ctxCallSpin
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret moveReinitByCall_inFragment moveReinitByCall_translate
      moveReinitByCall_translateInProg ctxCallSpin ctxMoveReinitByCall_ok
      [.scalar ⟨55, 4⟩] (by decide) moveReinitByCallMInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      moveReinitByCall_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [moveReinitByCall] at hd; subst hd
  simp [retPtr, ctxCallSpin, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallSpin, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem moveReinitByCall_minirust_direct :
    (Interp.steps 10 moveReinitByCallMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 55 }, [1]) := by
  decide +kernel

/-- Branch-correlated `Call` `move` across a CFG join:
```rust
fn cond_call_move_join(flag: u32, x: u32) -> u32 {
    let y = if flag != 0 { id_u32_callee(move x) } else { 0 };
    if flag != 0 { y } else { x }
}
```
On `bb1` (`flag != 0`), `move _2` is lowered via `ArgumentExpr::InPlace` (writing
`Uninit` in MiniRust too, so `_2` is not stale!), allowing `bb5` (`flag == 0`)
after the join block `bb3` to read `copy _2` cleanly in `progInFragment`. -/
def condCallMoveJoin : CapturedMir where
  defPath := "witness::cond_call_move_join"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 3)],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 2)], otherwise := 1 }),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.move (local_ 2)] (local_ 3) (some 3) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 3) (.use (constU32 0)))],
      terminator := mkTerm (.goto 3), isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1)) { branches := [(0, 5)], otherwise := 4 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 2)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem condCallMoveJoin_inFragment :
    progInFragment condCallMoveJoin [idU32Callee] = true := by decide

def condCallMoveJoinProg : Gen.Program :=
  (translateProg condCallMoveJoin [idU32Callee]).getD emptyProg

def condCallMoveJoinFn : Gen.Function :=
  (translateFnInProg (fnNameMap condCallMoveJoin [idU32Callee]) condCallMoveJoin).getD callerFn

theorem condCallMoveJoin_translate :
    translateProg condCallMoveJoin [idU32Callee] = some condCallMoveJoinProg := rfl

theorem condCallMoveJoin_translateInProg :
    translateFnInProg (fnNameMap condCallMoveJoin [idU32Callee]) condCallMoveJoin =
      some condCallMoveJoinFn := rfl

theorem ctxCondCallMoveJoin_ok : CtxOk condCallMoveJoin ctxCallerMain where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [condCallMoveJoin] at hd; subst hd; decide
    | 1, _, hd => simp [condCallMoveJoin] at hd; subst hd; decide
    | 2, _, hd => simp [condCallMoveJoin] at hd; subst hd; decide
    | _ + 3, hi, _ => simp [condCallMoveJoin] at hi
  ret := by
    intro d hd; simp [condCallMoveJoin] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def condCallMoveJoin1Args : List Value := [.scalar ⟨1, 4⟩, .scalar ⟨42, 4⟩]

def condCallMoveJoin1S0 : MachineState :=
  initMachineStateWithCallees condCallMoveJoin condCallMoveJoin1Args [idU32Callee]

def condCallMoveJoin1MInit : Mach :=
  multiMachineWithCtx ctxCallerMain condCallMoveJoinProg 2 condCallMoveJoin condCallMoveJoinFn
    condCallMoveJoin1S0.frame.locals condCallMoveJoinFn.start

theorem condCallMoveJoin1_anneal_ret :
    ReachesRet (mirCallTreeWithCallees condCallMoveJoin condCallMoveJoin1Args [idU32Callee])
      [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩,
        ⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨42, 4⟩,
        { condCallMoveJoin1S0.memory with activeCallee := some condCallMoveJoin })) :=
  runA_sound condCallMoveJoin 25 _ _ _ rfl

theorem condCallMoveJoin1_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n condCallMoveJoin1MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads = [thread1 ctxCallerMain
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret condCallMoveJoin_inFragment condCallMoveJoin_translate
      condCallMoveJoin_translateInProg ctxCallerMain ctxCondCallMoveJoin_ok
      condCallMoveJoin1Args (by decide) condCallMoveJoin1MInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      condCallMoveJoin1_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [condCallMoveJoin] at hd; subst hd
  simp [retPtr, ctxCallerMain, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallerMain, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

def condCallMoveJoin0Args : List Value := [.scalar ⟨0, 4⟩, .scalar ⟨99, 4⟩]

def condCallMoveJoin0S0 : MachineState :=
  initMachineStateWithCallees condCallMoveJoin condCallMoveJoin0Args [idU32Callee]

def condCallMoveJoin0MInit : Mach :=
  multiMachineWithCtx ctxCallerMain condCallMoveJoinProg 2 condCallMoveJoin condCallMoveJoinFn
    condCallMoveJoin0S0.frame.locals condCallMoveJoinFn.start

theorem condCallMoveJoin0_anneal_ret :
    ReachesRet (mirCallTreeWithCallees condCallMoveJoin condCallMoveJoin0Args [idU32Callee])
      [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩,
        ⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨99, 4⟩, condCallMoveJoin0S0.memory)) :=
  runA_sound condCallMoveJoin 25 _ _ _ rfl

theorem condCallMoveJoin0_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n condCallMoveJoin0MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 99 } ∧
      m'.threads = [thread1 ctxCallerMain
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret condCallMoveJoin_inFragment condCallMoveJoin_translate
      condCallMoveJoin_translateInProg ctxCallerMain ctxCondCallMoveJoin_ok
      condCallMoveJoin0Args (by decide) condCallMoveJoin0MInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      condCallMoveJoin0_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [condCallMoveJoin] at hd; subst hd
  simp [retPtr, ctxCallerMain, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallerMain, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem condCallMoveJoin_minirust_direct :
    (Interp.steps 11 condCallMoveJoin1MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (Interp.steps 9 condCallMoveJoin0MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- Counterexample 3 (`StorageLive(_2); _2 = move _1; _0 = idU32Callee(copy _1)`):
passing a local that was moved out in an earlier statement (leaving stale bytes
in MiniRust!) as a call argument is rejected by `termReadsOk` / `movesOk` (and
`progInFragment`). -/
def stmtMoveThenCallArg : CapturedMir where
  defPath := "witness::stmt_move_then_call_arg"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.use (.move (local_ 1))))],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem stmtMoveThenCallArg_movesOk : movesOk stmtMoveThenCallArg = false := by decide

theorem stmtMoveThenCallArg_rejected :
    progInFragment stmtMoveThenCallArg [idU32Callee] = false := by decide

/-- Counterexample 4: mutual recursion `recCycleA -> recCycleB -> recCycleA` is
rejected by `maxStackLocals = none` (`progInFragment = false`). -/
def recCycleA : CapturedMir where
  defPath := "witness::rec_cycle_a"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::rec_cycle_b")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

def recCycleB : CapturedMir where
  defPath := "witness::rec_cycle_b"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::rec_cycle_a")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem recCycle_maxStackLocals :
    maxStackLocals recCycleA [recCycleB, recCycleA] = none := rfl

theorem recCycle_rejected :
    progInFragment recCycleA [recCycleB, recCycleA] = false := by decide

/-! ### Ground-truth `Interp` unit checks for `MR-4.1` spec items -/

/-- `Type.layout` on `Ptr` (thin `FnPtr`, thin sized `Ref`, wide `Slice` `Ref`,
and `Raw (.VTablePointer _)`) and `Array` (`[u32; 3]`, `3 * 4 = 12` bytes, align `4`). -/
def sizedU32Pointee : Gen.PointeeInfo :=
  { layout := .Sized ⟨4⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Sized [],
    freeze := true, unpin := true }

def sliceU32Pointee : Gen.PointeeInfo :=
  { layout := .Slice ⟨4⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Slice [],
    freeze := true, unpin := true }

theorem layout_ptr_and_array_mr41 :
    Type.layout (.Ptr .FnPtr) = .ok (.Sized ⟨8⟩ ⟨8⟩) ∧
    Type.layout (.Ptr (.Ref .Immutable sizedU32Pointee)) = .ok (.Sized ⟨8⟩ ⟨8⟩) ∧
    Type.layout (.Ptr (.Ref .Immutable sliceU32Pointee)) = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    Type.layout (.Ptr (.Raw (.VTablePointer ⟨⟨0⟩⟩))) = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    Type.layout (.Array (.Int u32) 3) = .ok (.Sized ⟨12⟩ ⟨4⟩) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `evalConstant` on `FnPointer`, `GlobalPointer` (with offset),
`VTablePointer`, and `PointerWithoutProvenance`, plus `fnFromPtr` on valid thin
function pointers, wide pointers (UB), unmapped thin pointers (UB), and
non-pointer values (UB). -/
def constTestMach : Mach :=
  { callerCallee20MInit with
    prog := { callerCalleeProg with
              globals := ⟨[(⟨⟨0⟩⟩, { bytes := [some 1, some 2], relocations := [], align := ⟨2⟩ })]⟩ },
    global_ptrs := ⟨[(⟨⟨0⟩⟩, { addr := 32, provenance := some (⟨99⟩, ()) })]⟩,
    vtable_ptrs := ⟨[(⟨⟨0⟩⟩, { addr := 48, provenance := some (⟨98⟩, ()) })]⟩ }

theorem evalConstant_and_fnFromPtr_mr41 :
    evalConstant constTestMach (.FnPointer (fnName 1)) =
      .ok (.Ptr ⟨fnPtrAt 1 1, none⟩) ∧
    evalConstant constTestMach (.GlobalPointer ⟨⟨⟨0⟩⟩, ⟨1⟩⟩) =
      .ok (.Ptr ⟨{ addr := 33, provenance := some (⟨99⟩, ()) }, none⟩) ∧
    evalConstant constTestMach (.VTablePointer ⟨⟨0⟩⟩) =
      .ok (.Ptr ⟨{ addr := 48, provenance := some (⟨98⟩, ()) }, none⟩) ∧
    evalConstant constTestMach (.PointerWithoutProvenance 4096) =
      .ok (.Ptr ⟨{ addr := 4096, provenance := none }, none⟩) ∧
    fnFromPtr constTestMach (.Ptr ⟨fnPtrAt 1 1, none⟩) = .ok calleePairFn ∧
    fnFromPtr constTestMach (.Ptr ⟨fnPtrAt 1 1, some (.ElementCount 2)⟩) =
      .error (.ub "invalid pointer for function lookup") ∧
    fnFromPtr constTestMach (.Ptr ⟨{ addr := 999, provenance := none }, none⟩) =
      .error (.ub "invalid pointer for function lookup") ∧
    fnFromPtr constTestMach (.Int 0) =
      .error (.ub "trying to look up a function based on a non-pointer value") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `checkAbiCompatibility` across `Int`, `Bool`, `Ptr`, `Tuple` (including
unsized tuple `specPanic`), `Array`, `Union`, and `Enum` (`orderingTy`
`Branch` `Discriminator`, variant mismatch, and tagger mismatch). -/
def sampleUnionA : Gen.Type :=
  .Union [(⟨0⟩, .Int u32), (⟨0⟩, .Bool)] [(⟨0⟩, ⟨4⟩)] ⟨4⟩ ⟨4⟩

def sampleUnionBadChunks : Gen.Type :=
  .Union [(⟨0⟩, .Int u32), (⟨0⟩, .Bool)] [(⟨0⟩, ⟨2⟩)] ⟨4⟩ ⟨4⟩

def orderingBadTagger : Gen.Type :=
  match orderingTy with
  | .Enum ⟨(-1, v) :: rest⟩ dTy discr sz al =>
    .Enum ⟨(-1, { v with tagger := ⟨[(⟨0⟩, (u8, 42))]⟩ }) :: rest⟩ dTy discr sz al
  | t => t

theorem checkAbiCompatibility_all_variants_mr41 :
    checkAbiCompatibility (.Int u32) (.Int u32) = .ok true ∧
    checkAbiCompatibility (.Int u32) (.Int i8) = .ok false ∧
    checkAbiCompatibility .Bool .Bool = .ok true ∧
    checkAbiCompatibility (.Ptr .FnPtr) (.Ptr (.Raw .None)) = .ok true ∧
    checkAbiCompatibility (.Ptr .FnPtr) (.Ptr (.Raw .ElementCount)) = .ok false ∧
    checkAbiCompatibility (intBoolTupleTy u32) (intBoolTupleTy u32) = .ok true ∧
    checkAbiCompatibility (intBoolTupleTy u32) (intBoolTupleTy i8) = .ok false ∧
    checkAbiCompatibility (.Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ (some (.Array (.Int u8) 0))) unitTy =
      .error (.specPanic "wf ensures all arugments are sized") ∧
    checkAbiCompatibility (.Array (.Int u32) 4) (.Array (.Int u32) 4) = .ok true ∧
    checkAbiCompatibility (.Array (.Int u32) 4) (.Array (.Int u32) 5) = .ok false ∧
    checkAbiCompatibility sampleUnionA sampleUnionA = .ok true ∧
    checkAbiCompatibility sampleUnionA sampleUnionBadChunks = .ok false ∧
    checkAbiCompatibility orderingTy orderingTy = .ok true ∧
    checkAbiCompatibility orderingTy orderingBadTagger = .ok false ∧
    checkAbiCompatibility orderingTy .Bool = .ok false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `createFrame` ABI-violation UB paths (calling convention mismatch, return
type mismatch, argument count mismatch, and argument type mismatch). -/
theorem createFrame_ub_mr41 :
    createFrame callerCallee20MInit calleePairFn
      (.BackToCaller (some (bbName 1)) none retPtr) .C (.Int u32) [] =
      .error (.ub "call ABI violation: calling conventions are not the same") ∧
    createFrame callerCallee20MInit calleePairFn
      (.BackToCaller (some (bbName 1)) none retPtr) .Rust .Bool [] =
      .error (.ub "call ABI violation: return types are not compatible") ∧
    createFrame callerCallee20MInit calleePairFn
      (.BackToCaller (some (bbName 1)) none retPtr) .Rust (.Int u32) [] =
      .error (.ub "call ABI violation: number of arguments does not agree") ∧
    createFrame callerCallee20MInit calleePairFn
      (.BackToCaller (some (bbName 1)) none retPtr) .Rust (.Int u32)
      [(.Bool true, .Bool), (.Bool false, .Bool)] =
      .error (.ub "call ABI violation: argument types are not compatible") :=
  ⟨eq_error_ub_of_ubMsg? (by decide +kernel),
   eq_error_ub_of_ubMsg? (by decide +kernel),
   eq_error_ub_of_ubMsg? (by decide +kernel),
   eq_error_ub_of_ubMsg? (by decide +kernel)⟩

def retNoNextBlockMach : Mach :=
  let m := multiMachineWithCtx
    { ctxWithFns callerFrame retAlloc 1 [128, 256] with nextBlock := bbName 7 }
    emptyProg 1 idU32Callee
    ((translateFn idU32Callee).getD callerFn)
    [.init (.scalar ⟨11, 4⟩), .init (.scalar ⟨11, 4⟩)]
    (bbName 0)
  let t0 := m.threads[0]?.getD (thread1 ctx0 [])
  let fTop := (t0.stack.getLast?.getD callerFrame)
  { m with threads := [{ t0 with stack := [callerFrame,
      { fTop with next_stmt := 1, stack_pop_action := .BackToCaller none none retPtr }] }] }

def retBottomOfStackMach : Mach :=
  let m := multiMachineWithCtx
    (ctxWithFns callerFrame retAlloc 1 [128, 256])
    emptyProg 1 idU32Callee
    ((translateFn idU32Callee).getD callerFn)
    [.init (.scalar ⟨11, 4⟩), .init (.scalar ⟨11, 4⟩)]
    (bbName 0)
  let t0 := m.threads[0]?.getD (thread1 ctx0 [])
  let fTop := (t0.stack.getLast?.getD callerFrame)
  { m with threads := [{ t0 with stack := [
      { fTop with next_stmt := 1, stack_pop_action := .BottomOfStack }] }] }

/-- `evalReturn` UB paths (`next_block = none` and `BottomOfStack` on thread `0`). -/
theorem evalReturn_missingNextBlock_and_bottomOfStack_ub :
    evalReturn retNoNextBlockMach =
      .error (.ub "return from a function where caller did not specify next block") ∧
    evalReturn retBottomOfStackMach =
      .error (.ub "the start function must not return") :=
  ⟨eq_error_ub_of_ubMsg? (by decide +kernel),
   eq_error_ub_of_ubMsg? (by decide +kernel)⟩

/-! ### Pass `B3` hardening witnesses: `CallConv.c` (`extern "C"`), unsupported-ABI rejection,
dead / uninitialized-tuple return-place counterexamples, and diamond call DAG -/

/-- `extern "C"` single-parameter `u32 -> u32` ABI (`Layout.CallConv.c`). -/
def fnAbiC1 : FnAbi :=
  { (fnAbi 1) with conv := .c }

/-- `extern "C"` callee `cAbiCallee(x: u32) -> u32 { x + 10 }`: exercises
`translateCallConv .c = some .C` in both `translateFn` and `translateFnInProg`. -/
def cAbiCallee : CapturedMir where
  defPath := "witness::c_abi_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 1)) (constU32 10)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiC1
  layouts := emptyLayoutTable
  allocations := []

/-- Rust-ABI caller invoking `extern "C"` `cAbiCallee` (`CallingConvention.C` on
the `Terminator::Call` edge while the caller itself has `CallingConvention.Rust`). -/
def cAbiCaller : CapturedMir where
  defPath := "witness::c_abi_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::c_abi_callee")
        [.move (local_ 1)] (local_ 0) (some 1) .unreachable),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem cAbiCallee_conv :
    (translateFn cAbiCallee).map (·.calling_convention) = some .C ∧
    (translateFnInProg (fnNameMap cAbiCaller [cAbiCallee]) cAbiCallee).map
      (·.calling_convention) = some .C ∧
    (translateFnInProg (fnNameMap cAbiCaller [cAbiCallee]) cAbiCaller).map
      (·.calling_convention) = some .Rust :=
  ⟨rfl, rfl, rfl⟩

theorem cAbi_inFragment :
    progInFragment cAbiCaller [cAbiCallee] = true := by decide

def cAbiProg : Gen.Program :=
  (translateProg cAbiCaller [cAbiCallee]).getD emptyProg

def cAbiCallerFn : Gen.Function :=
  (translateFnInProg (fnNameMap cAbiCaller [cAbiCallee]) cAbiCaller).getD callerFn

theorem cAbi_translate :
    translateProg cAbiCaller [cAbiCallee] = some cAbiProg := rfl

theorem cAbiCaller_translateInProg :
    translateFnInProg (fnNameMap cAbiCaller [cAbiCallee]) cAbiCaller = some cAbiCallerFn := rfl

theorem ctxCAbiCaller_ok : CtxOk cAbiCaller ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [cAbiCaller] at hd; subst hd; decide
    | 1, _, hd => simp [cAbiCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [cAbiCaller] at hi
  ret := by
    intro d hd; simp [cAbiCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def cAbi32Args : List Value := [.scalar ⟨32, 4⟩]

def cAbi32S0 : MachineState :=
  initMachineStateWithCallees cAbiCaller cAbi32Args [cAbiCallee]

def cAbi32MInit : Mach :=
  multiMachineWithCtx ctxCallSpin cAbiProg 2 cAbiCaller cAbiCallerFn
    cAbi32S0.frame.locals cAbiCallerFn.start

theorem cAbi32_anneal_ret :
    ReachesRet (mirCallTreeWithCallees cAbiCaller cAbi32Args [cAbiCallee]) []
      (.normal (.scalar ⟨42, 4⟩,
        { cAbi32S0.memory with activeCallee := some cAbiCaller })) :=
  runA_sound cAbiCaller 20 _ _ _ rfl

theorem cAbi32_noUB :
    MirNoUBTree (mirCallTreeWithCallees cAbiCaller cAbi32Args [cAbiCallee]) :=
  runA_noUB cAbiCaller 20 _ _ _ rfl

theorem cAbi32_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cAbi32MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads = [thread1 ctxCallSpin
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret cAbi_inFragment cAbi_translate
      cAbiCaller_translateInProg ctxCallSpin ctxCAbiCaller_ok
      cAbi32Args (by decide) cAbi32MInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      cAbi32_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cAbiCaller] at hd; subst hd
  simp [retPtr, ctxCallSpin, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallSpin, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem cAbi32_minirust_direct :
    (Interp.steps 6 cAbi32MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) := by
  decide +kernel

/-- Rejection of unsupported calling conventions (`Layout.CallConv.rustIntrinsic`
and `Layout.CallConv.other "sysv64"`): `translateCallConv = none`, so both
single-function (`translateFn`, `inFragment`) and multi-function
(`callTerminatorOk`, `translateProg`, `progInFragment`) checks reject them. -/
def badCallConvCallee : CapturedMir :=
  { idU32Callee with
    defPath := "witness::bad_call_conv_callee",
    fnAbi := { (fnAbi 1) with conv := .rustIntrinsic } }

def badCallConvSysvBody : CapturedMir :=
  { idU32Callee with
    defPath := "witness::bad_sysv_body",
    fnAbi := { (fnAbi 1) with conv := .other "sysv64" } }

def badCallConvCaller : CapturedMir where
  defPath := "witness::bad_call_conv_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::bad_call_conv_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem badCallConv_rejected :
    translateCallConv .rustIntrinsic = none ∧
    translateCallConv (.other "sysv64") = none ∧
    translateFn badCallConvCallee = none ∧
    inFragment badCallConvCallee = false ∧
    translateFn badCallConvSysvBody = none ∧
    inFragment badCallConvSysvBody = false ∧
    callTerminatorOk [badCallConvCallee] badCallConvCaller 0
      (mkTerm (.call (fnDefOp "witness::bad_call_conv_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_)) = false ∧
    progInFragment badCallConvCaller [badCallConvCallee] = false ∧
    translateProg badCallConvCaller [badCallConvCallee] = none :=
  ⟨rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, rfl⟩

/-- Dead return place
(`StorageLive(_2); StorageDead(_2); _2 = idU32Callee(copy _1)`):
in MiniRust, `Terminator::Call` evaluates the return place `_2` and runs
`prepare_for_inplace_passing` BEFORE argument evaluation or callee entry,
faulting on step 4 (after `initBlock` `Goto(bb0)`, `StorageLive(_2)`, and
`StorageDead(_2)`) with `"access to a dead local"` before `idU32Callee` is ever
entered, whereas Anneal enters `idU32Callee` and faults only when `Return`
writes the dead `_2`. Both semantics fault here, so this caller alone does not
show that the check is necessary; `deadCallDestSpinCaller` replaces
`idU32Callee` with a diverging callee, for which Anneal never faults.
`callDestOk` requires `lv.contains dst` and rejects this caller. -/
def deadCallDestCaller : CapturedMir where
  defPath := "witness::dead_call_dest_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2), mkStmt (.storageDead 2)],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (local_ 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 0)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem deadCallDest_rejected :
    callDestOk deadCallDestCaller.localDecls (mustLiveBefore deadCallDestCaller 0 2)
      (tupleInitBefore deadCallDestCaller 0 2) u32Decl (local_ 2) = false ∧
    progInFragment deadCallDestCaller [idU32Callee] = false := by
  decide

def deadCallDestProg : Gen.Program :=
  (translateProg deadCallDestCaller [idU32Callee]).getD emptyProg

def deadCallDestFn : Gen.Function :=
  (translateFnInProg (fnNameMap deadCallDestCaller [idU32Callee]) deadCallDestCaller).getD callerFn

theorem deadCallDest_translate :
    translateProg deadCallDestCaller [idU32Callee] = some deadCallDestProg := rfl

def deadCallDestS0 : MachineState :=
  initMachineStateWithCallees deadCallDestCaller [.scalar ⟨7, 4⟩] [idU32Callee]

def deadCallDestMInit : Mach :=
  multiMachineWithCtx ctxCallSpin deadCallDestProg 2 deadCallDestCaller deadCallDestFn
    deadCallDestS0.frame.locals deadCallDestFn.start

theorem deadCallDest_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees deadCallDestCaller [.scalar ⟨7, 4⟩] [idU32Callee]) tr u ∧
      FaultNow u :=
  faultsA_sound deadCallDestCaller 10 _ (by decide)

theorem deadCallDest_minirust_ub_before_callee :
    Interp.steps 4 deadCallDestMInit =
      .error (.ub "access to a dead local") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

/-- Counterexample 6 (`StorageLive(_2); _2.0 = negI8Callee(copy _1); _0 = copy (_2.0);
StorageDead(_2); Return` where `_2 : (i8, bool)` is live but uninitialized):
when `negI8Callee(5i8)` returns `-5i8`, Anneal's `writePlaceValue` faults with UB
because projected field assignment into `.uninit` local `_2` is forbidden in
Anneal's value-slot model (`uninitProjCallDest_anneal_ub`), whereas MiniRust's
byte-level stack allocation writes `[-5i8]` to byte `0` of `_2` and returns
`-5i8` (`251`) cleanly (`uninitProjCallDest_minirust_ret`)! Thus `ti.contains dst`
(`tupleInitOk`) in `callDestOk` is strictly required for forward UB soundness. -/
def uninitProjCallDestCaller : CapturedMir where
  defPath := "witness::uninit_proj_call_dest_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl, i8BoolTupleDecl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2)],
      terminator := mkTerm (.call (fnDefOp "witness::neg_i8_callee")
        [.copy (local_ 1)] (field0I8 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (field0I8 2)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem uninitProjCallDest_rejected :
    (mustLiveBefore uninitProjCallDestCaller 0 1).contains 2 = true ∧
    (tupleInitBefore uninitProjCallDestCaller 0 1).contains 2 = false ∧
    callDestOk uninitProjCallDestCaller.localDecls (mustLiveBefore uninitProjCallDestCaller 0 1)
      (tupleInitBefore uninitProjCallDestCaller 0 1) i8Decl (field0I8 2) = false ∧
    progInFragment uninitProjCallDestCaller [negI8Callee] = false := by
  decide

def uninitProjCallDestProg : Gen.Program :=
  (translateProg uninitProjCallDestCaller [negI8Callee]).getD emptyProg

def uninitProjCallDestFn : Gen.Function :=
  (translateFnInProg (fnNameMap uninitProjCallDestCaller [negI8Callee])
    uninitProjCallDestCaller).getD callerFnI8

theorem uninitProjCallDest_translate :
    translateProg uninitProjCallDestCaller [negI8Callee] = some uninitProjCallDestProg := rfl

def uninitProjCallDestS0 : MachineState :=
  initMachineStateWithCallees uninitProjCallDestCaller [.scalar ⟨5, 1⟩] [negI8Callee]

def uninitProjCallDestMInit : Mach :=
  multiMachineWithCtx ctxCalleeDivZero uninitProjCallDestProg 2 uninitProjCallDestCaller
    uninitProjCallDestFn uninitProjCallDestS0.frame.locals uninitProjCallDestFn.start

theorem uninitProjCallDest_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees uninitProjCallDestCaller [.scalar ⟨5, 1⟩] [negI8Callee]) tr u ∧
      FaultNow u :=
  faultsA_sound uninitProjCallDestCaller 15 _ (by decide)

theorem uninitProjCallDest_minirust_ret :
    (Interp.steps 9 uninitProjCallDestMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 251 }, [1]) := by
  decide +kernel

/-- Diamond call-graph DAG (`diamondCallEntry -> diamondMidA -> cAbiCallee` and
`diamondCallEntry -> diamondMidB -> cAbiCallee`) mixing `.Rust` (`diamondCallEntry`,
`diamondMidA`) and `.C` (`diamondMidB`, `cAbiCallee`) calling conventions across
shared leaf `cAbiCallee`. -/
def diamondMidA : CapturedMir where
  defPath := "witness::diamond_mid_a"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::c_abi_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

def diamondMidB : CapturedMir where
  defPath := "witness::diamond_mid_b"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.binaryOp .add (.copy (local_ 1)) (constU32 1)))],
      terminator := mkTerm (.call (fnDefOp "witness::c_abi_callee")
        [.move (local_ 2)] (local_ 0) (some 1) .terminate),
      isCleanup := false },
    { statements := [mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiC1
  layouts := emptyLayoutTable
  allocations := []

def diamondCallEntry : CapturedMir where
  defPath := "witness::diamond_call_entry"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2), mkStmt (.storageLive 3)],
      terminator := mkTerm (.call (fnDefOp "witness::diamond_mid_a")
        [.copy (local_ 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::diamond_mid_b")
        [.move (local_ 1)] (local_ 3) (some 2) .unreachable),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.binaryOp .add (.move (local_ 2)) (.move (local_ 3)))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem diamondCall_inFragment :
    progInFragment diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee] = true := by
  decide

theorem diamondCall_maxStackLocals :
    maxStackLocals diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee] = some 9 := rfl

def ctxDiamondCall : Ctx :=
  ctxWithFns callerFrame retAlloc 4 [128, 256]

theorem ctxDiamondCall_ok : CtxOk diamondCallEntry ctxDiamondCall where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [diamondCallEntry] at hd; subst hd; decide
    | 1, _, hd => simp [diamondCallEntry] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [diamondCallEntry] at hi
  ret := by
    intro d hd; simp [diamondCallEntry] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def diamondCallProg : Gen.Program :=
  (translateProg diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee]).getD emptyProg

def diamondCallEntryFn : Gen.Function :=
  (translateFnInProg (fnNameMap diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee])
    diamondCallEntry).getD callerFn

theorem diamondCall_translate :
    translateProg diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee] =
      some diamondCallProg := rfl

theorem diamondCallEntry_translateInProg :
    translateFnInProg (fnNameMap diamondCallEntry [diamondMidA, diamondMidB, cAbiCallee])
      diamondCallEntry = some diamondCallEntryFn := rfl

def diamondCall5Args : List Value := [.scalar ⟨5, 4⟩]

def diamondCall5S0 : MachineState :=
  initMachineStateWithCallees diamondCallEntry diamondCall5Args
    [diamondMidA, diamondMidB, cAbiCallee]

def diamondCall5MInit : Mach :=
  multiMachineWithCtx ctxDiamondCall diamondCallProg 4 diamondCallEntry diamondCallEntryFn
    diamondCall5S0.frame.locals diamondCallEntryFn.start

theorem diamondCall5_anneal_ret :
    ReachesRet
      (mirCallTreeWithCallees diamondCallEntry diamondCall5Args
        [diamondMidA, diamondMidB, cAbiCallee]) []
      (.normal (.scalar ⟨31, 4⟩,
        { diamondCall5S0.memory with activeCallee := some diamondCallEntry })) :=
  runA_sound diamondCallEntry 35 _ _ _ rfl

theorem diamondCall5_noUB :
    MirNoUBTree
      (mirCallTreeWithCallees diamondCallEntry diamondCall5Args
        [diamondMidA, diamondMidB, cAbiCallee]) :=
  runA_noUB diamondCallEntry 35 _ _ _ rfl

theorem diamondCall5_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n diamondCall5MInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 31 } ∧
      m'.threads = [thread1 ctxDiamondCall
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret diamondCall_inFragment diamondCall_translate
      diamondCallEntry_translateInProg ctxDiamondCall ctxDiamondCall_ok
      diamondCall5Args (by decide) diamondCall5MInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
      diamondCall5_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [diamondCallEntry] at hd; subst hd
  simp [retPtr, ctxDiamondCall, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxDiamondCall, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem diamondCall5_minirust_direct :
    (Interp.steps 24 diamondCall5MInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 31 }, [1]) := by
  decide +kernel

/-! ### Pass `A3` necessity witnesses for `progInFragment`'s call checks

Each rejected caller below refutes the conclusion of a transfer theorem: either
of `mirCallWithCallees_noUB` (Anneal's tree is `MirNoUBTree`, yet MiniRust stops
with UB before any root return) or of `mirCallWithCallees_ub` (Anneal reaches
UB, yet MiniRust never raises UB). So each conjunct of `progInFragment` that
rejects it (`callDestOk`'s liveness, tuple-initialization, and return-type
checks, `callArgsOk`'s parameter types, `callTerminatorOk`'s argument count and
return-place and argument disjointness, root-only `move` call arguments, and
`termReadsOk`) is necessary. `deadCallDestSpin_hyps` checks that every other
hypothesis of `mirCallWithCallees_noUB` holds for `deadCallDestSpinCaller`. -/

/-- `ReturnRel` pops MiniRust's active thread back to the single external caller
frame, so it holds at none of the first `n` steps when every one of them leaves
a stack whose length is not `1`. -/
theorem no_returnRel_before {entry : CapturedMir} {ctx : Ctx} {mInit : Mach} {n : Nat}
    (hdepth : (List.range n).all (fun k =>
      (Interp.steps k mInit).toOption.map (fun m => m.threads.map (·.stack.length)) !=
        some [1]) = true)
    {k : Nat} {s' : MachineState} {v : Value} {mRet : Mach}
    (hk : k < n) (hsteps : Interp.steps k mInit = .ok mRet) :
    ¬ ReturnRel entry ctx s' v mRet := by
  rintro ⟨_, _, _, _, _, _, _, _, hthr, _, _⟩
  have hk' := List.all_eq_true.mp hdepth k (List.mem_range.mpr hk)
  simp [hsteps, Except.toOption, hthr, thread1] at hk'

/-- Whether an `Interp` result is a `Stop.ub`. -/
def isUbStop {α : Type} : Interp α → Bool
  | .error (.ub _) => true
  | _ => false

/-- Whether an `Interp` result is a stop other than `Stop.ub`. -/
def isNonUbStop {α : Type} : Interp α → Bool
  | .error (.ub _) => false
  | .error _ => true
  | .ok _ => false

/-- If MiniRust raises no UB in its first `N` steps and stops with a non-UB
error at step `N` (for instance a `specPanic` in the witnesses' external caller
frame, whose `callerFn` has no blocks, right after the root return), it never
raises UB: `Interp.steps` propagates an error unchanged. -/
theorem never_ub_of_nonUb_stop {m : Mach} {N : Nat}
    (hpre : (List.range N).all (fun k => !isUbStop (Interp.steps k m)) = true)
    (hstop : isNonUbStop (Interp.steps N m) = true) :
    ¬ ∃ (n : Nat) (msg : String), Interp.steps n m = .error (.ub msg) := by
  rintro ⟨n, msg, h⟩
  by_cases hn : n < N
  · have hk := List.all_eq_true.mp hpre n (List.mem_range.mpr hn)
    rw [h] at hk
    simp [isUbStop] at hk
  · obtain ⟨j, rfl⟩ : ∃ j, n = N + j := ⟨n - N, by omega⟩
    cases hN : Interp.steps N m with
    | ok mN => rw [hN] at hstop; simp [isNonUbStop] at hstop
    | error e =>
      rw [steps_add, hN, error_bind] at h
      injection h with he
      subst he
      simp [hN, isNonUbStop] at hstop

/-- `callDestArgAlias` (`_1 = idU32Callee(copy _1)`) refutes the conclusion of
`mirCallWithCallees_noUB` (at `n = 2`): Anneal returns without UB, while
MiniRust's `prepare_for_inplace_passing` uninitializes `_1` before the argument
load. -/
theorem callDestArgAlias_noUB :
    MirNoUBTree (mirCallTreeWithCallees callDestArgAlias [.scalar ⟨7, 4⟩] [idU32Callee]) :=
  runA_noUB callDestArgAlias 10 _ _ _ rfl

theorem callDestArgAlias_noUB_transfer_fails :
    MirNoUBTree (mirCallTreeWithCallees callDestArgAlias [.scalar ⟨7, 4⟩] [idU32Callee]) ∧
    Interp.steps 2 callDestArgAliasMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    ¬ ∃ k s' mRet tr v mem, k < 2 ∧ Interp.steps k callDestArgAliasMInit = .ok mRet ∧
      ReturnRel callDestArgAlias ctxCallerMain s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callDestArgAlias [.scalar ⟨7, 4⟩] [idU32Callee])
        tr (.normal (v, mem)) :=
  ⟨callDestArgAlias_noUB, callDestArgAlias_minirust_ub,
    fun ⟨_, _, _, _, _, _, hk, hsteps, hret, _⟩ =>
      no_returnRel_before (mInit := callDestArgAliasMInit) (n := 2) (by decide +kernel)
        hk hsteps hret⟩

/-- `callProjMoveReuse` (`_2 = idU32Callee(move (_1.0)); _0 = copy (_1.0)`)
refutes the conclusion of `mirCallWithCallees_noUB` (at `n = 7`). -/
theorem callProjMoveReuse_noUB :
    MirNoUBTree
      (mirCallTreeWithCallees callProjMoveReuse callProjMoveReuseArgs [idU32Callee]) :=
  runA_noUB callProjMoveReuse 10 _ _ _ rfl

theorem callProjMoveReuse_noUB_transfer_fails :
    MirNoUBTree
      (mirCallTreeWithCallees callProjMoveReuse callProjMoveReuseArgs [idU32Callee]) ∧
    Interp.steps 7 callProjMoveReuseMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    ¬ ∃ k s' mRet tr v mem, k < 7 ∧ Interp.steps k callProjMoveReuseMInit = .ok mRet ∧
      ReturnRel callProjMoveReuse ctxCallerMain s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees callProjMoveReuse callProjMoveReuseArgs [idU32Callee])
        tr (.normal (v, mem)) :=
  ⟨callProjMoveReuse_noUB, callProjMoveReuse_minirust_ub,
    fun ⟨_, _, _, _, _, _, hk, hsteps, hret, _⟩ =>
      no_returnRel_before (mInit := callProjMoveReuseMInit) (n := 7) (by decide +kernel)
        hk hsteps hret⟩

/-- `uninitProjCallDestCaller` refutes the conclusion of
`mirCallWithCallees_ub`: Anneal faults when `Return` writes `_2.0` into the
uninitialized tuple `_2`, while MiniRust returns `-5i8` at step `9` and then
stops with a `specPanic` in the external caller frame, never raising UB. -/
theorem uninitProjCallDest_ub_transfer_fails :
    (∃ tr u, Reaches
      (mirCallTreeWithCallees uninitProjCallDestCaller [.scalar ⟨5, 1⟩] [negI8Callee]) tr u ∧
      FaultNow u) ∧
    ¬ ∃ (n : Nat) (msg : String), Interp.steps n uninitProjCallDestMInit = .error (.ub msg) :=
  ⟨uninitProjCallDest_anneal_ub,
    never_ub_of_nonUb_stop (N := 10) (by decide +kernel) (by decide +kernel)⟩

/-- Diverging callee `fn spin_u32_callee(x: u32) -> u32 { loop {} }`. -/
def spinU32Callee : CapturedMir where
  defPath := "witness::spin_u32_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [{ statements := [], terminator := mkTerm (.goto 0), isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Live return place, diverging callee
(`StorageLive(_2); _2 = spinU32Callee(copy _1); _0 = copy _2; StorageDead(_2)`):
in `progInFragment`, and both semantics run forever without UB, MiniRust in
lockstep with a 3-frame stack (`liveCallDestSpin_depth3_step20`). -/
def liveCallDestSpinCaller : CapturedMir where
  defPath := "witness::live_call_dest_spin_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2)],
      terminator := mkTerm (.call (fnDefOp "witness::spin_u32_callee")
        [.copy (local_ 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 2)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem liveCallDestSpin_inFragment :
    progInFragment liveCallDestSpinCaller [spinU32Callee] = true := by decide

def liveCallDestSpinProg : Gen.Program :=
  (translateProg liveCallDestSpinCaller [spinU32Callee]).getD emptyProg

def liveCallDestSpinFn : Gen.Function :=
  (translateFnInProg (fnNameMap liveCallDestSpinCaller [spinU32Callee])
    liveCallDestSpinCaller).getD callerFn

theorem liveCallDestSpin_translate :
    translateProg liveCallDestSpinCaller [spinU32Callee] = some liveCallDestSpinProg := rfl

theorem liveCallDestSpin_translateInProg :
    translateFnInProg (fnNameMap liveCallDestSpinCaller [spinU32Callee]) liveCallDestSpinCaller =
      some liveCallDestSpinFn := rfl

def callDestSpinArgs : List Value := [.scalar ⟨7, 4⟩]

def liveCallDestSpinS0 : MachineState :=
  initMachineStateWithCallees liveCallDestSpinCaller callDestSpinArgs [spinU32Callee]

def liveCallDestSpinMInit : Mach :=
  multiMachineWithCtx ctxCallSpin liveCallDestSpinProg 2 liveCallDestSpinCaller
    liveCallDestSpinFn liveCallDestSpinS0.frame.locals liveCallDestSpinFn.start

theorem ctxLiveCallDestSpin_ok : CtxOk liveCallDestSpinCaller ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [liveCallDestSpinCaller] at hd; subst hd; decide
    | 1, _, hd => simp [liveCallDestSpinCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [liveCallDestSpinCaller] at hi
  ret := by
    intro d hd; simp [liveCallDestSpinCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

private def nextLiveSpinState (s : MachineState) : MachineState :=
  match stepMirFn liveCallDestSpinCaller s with
  | .tau (.running s') => s'
  | _ => s

private def liveCallDestSpinS1 : MachineState := nextLiveSpinState liveCallDestSpinS0

private def liveCallDestSpinS2 : MachineState := nextLiveSpinState liveCallDestSpinS1

/-- Three-state silent-step invariant: `StorageLive(_2)`, the call, and the
callee's `Goto(bb0)` self-loop. -/
def LiveCallDestSpinInv (s : MachineState) : Prop :=
  s = liveCallDestSpinS0 ∨ s = liveCallDestSpinS1 ∨ s = liveCallDestSpinS2

private theorem liveCallDestSpin_step (s : MachineState) (h : LiveCallDestSpinInv s) :
    ∃ s', stepMirFn liveCallDestSpinCaller s = .tau (.running s') ∧
      LiveCallDestSpinInv s' := by
  rcases h with rfl | rfl | rfl
  · exact ⟨liveCallDestSpinS1, rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨liveCallDestSpinS2, rfl, Or.inr (Or.inr rfl)⟩
  · exact ⟨liveCallDestSpinS2, rfl, Or.inr (Or.inr rfl)⟩

theorem liveCallDestSpin_noUB :
    MirNoUBTree
      (mirCallTreeWithCallees liveCallDestSpinCaller callDestSpinArgs [spinU32Callee]) :=
  treeSafe_of_tau_inv liveCallDestSpin_step (Or.inl rfl)

theorem liveCallDestSpin_noRet (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet
      (mirCallTreeWithCallees liveCallDestSpinCaller callDestSpinArgs [spinU32Callee]) tr o :=
  noRet_of_tau_inv liveCallDestSpin_step (Or.inl rfl) tr o

theorem liveCallDestSpin_minirust_diverges (n : Nat) :
    ∃ m', Interp.steps n liveCallDestSpinMInit = .ok m' :=
  mirCallWithCallees_diverges_steps_ok liveCallDestSpin_inFragment liveCallDestSpin_translate
    liveCallDestSpin_translateInProg ctxCallSpin ctxLiveCallDestSpin_ok callDestSpinArgs
    (by decide) liveCallDestSpinMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    liveCallDestSpin_noUB liveCallDestSpin_noRet n

theorem liveCallDestSpin_minirust_diverges_rel (n : Nat) :
    ∃ d s' m0 m' tr,
      Interp.steps (initLen liveCallDestSpinCaller + n) liveCallDestSpinMInit = .ok m0 ∧
      Interp.steps (initLen liveCallDestSpinCaller + n + d) liveCallDestSpinMInit = .ok m' ∧
      MultiStateRel liveCallDestSpinCaller [spinU32Callee] liveCallDestSpinProg ctxCallSpin s' m' ∧
      Reaches (mirCallTreeWithCallees liveCallDestSpinCaller callDestSpinArgs [spinU32Callee])
        tr (mirTree liveCallDestSpinCaller s') :=
  mirCallWithCallees_diverges_rel liveCallDestSpin_inFragment liveCallDestSpin_translate
    liveCallDestSpin_translateInProg ctxCallSpin ctxLiveCallDestSpin_ok callDestSpinArgs
    (by decide) liveCallDestSpinMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    liveCallDestSpin_noUB liveCallDestSpin_noRet n

theorem liveCallDestSpin_depth3_step20 :
    (Interp.steps 20 liveCallDestSpinMInit).toOption.map
        (fun m => m.threads.map (·.stack.length)) = some [3] := by
  decide +kernel

/-- Necessity of `callDestOk`'s liveness check (`lv.contains dst`): the same
caller as `liveCallDestSpinCaller` with one extra `StorageDead(_2)` before the
call. Every other per-body check passes (`deadCallDestSpin_rejected`), and
`livenessOk` itself holds (`liveAtEntry` is a valid post-fixed point that simply
does not contain `_2` at the call), so only `callDestOk` rejects it. Anneal
pushes `spinU32Callee` without inspecting `_2` and runs forever without UB,
whereas MiniRust's `prepare_for_inplace_passing` faults on the dead `_2` at
step 4 (`deadCallDestSpin_noUB_transfer_fails`). -/
def deadCallDestSpinCaller : CapturedMir where
  defPath := "witness::dead_call_dest_spin_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2), mkStmt (.storageDead 2)],
      terminator := mkTerm (.call (fnDefOp "witness::spin_u32_callee")
        [.copy (local_ 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 0)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem deadCallDestSpin_rejected :
    (mustLiveBefore deadCallDestSpinCaller 0 2).contains 2 = false ∧
    callDestOk deadCallDestSpinCaller.localDecls (mustLiveBefore deadCallDestSpinCaller 0 2)
      (tupleInitBefore deadCallDestSpinCaller 0 2) u32Decl (local_ 2) = false ∧
    movesOk deadCallDestSpinCaller = true ∧ mentionsOk deadCallDestSpinCaller = true ∧
    storageDeadOk deadCallDestSpinCaller = true ∧ livenessOk deadCallDestSpinCaller = true ∧
    tupleInitOk deadCallDestSpinCaller = true ∧
    progInFragment deadCallDestSpinCaller [spinU32Callee] = false := by
  decide

def deadCallDestSpinProg : Gen.Program :=
  (translateProg deadCallDestSpinCaller [spinU32Callee]).getD emptyProg

def deadCallDestSpinFn : Gen.Function :=
  (translateFnInProg (fnNameMap deadCallDestSpinCaller [spinU32Callee])
    deadCallDestSpinCaller).getD callerFn

def deadCallDestSpinS0 : MachineState :=
  initMachineStateWithCallees deadCallDestSpinCaller callDestSpinArgs [spinU32Callee]

def deadCallDestSpinMInit : Mach :=
  multiMachineWithCtx ctxCallSpin deadCallDestSpinProg 2 deadCallDestSpinCaller
    deadCallDestSpinFn deadCallDestSpinS0.frame.locals deadCallDestSpinFn.start

theorem ctxDeadCallDestSpin_ok : CtxOk deadCallDestSpinCaller ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [deadCallDestSpinCaller] at hd; subst hd; decide
    | 1, _, hd => simp [deadCallDestSpinCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [deadCallDestSpinCaller] at hi
  ret := by
    intro d hd; simp [deadCallDestSpinCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- Every hypothesis of `mirCallWithCallees_noUB` other than `hfrag` holds for
`deadCallDestSpinCaller` (the remaining `hthreads`, `hactive`, and `hallocs`
hold by `rfl` for `multiMachineWithCtx`). -/
theorem deadCallDestSpin_hyps :
    translateProg deadCallDestSpinCaller [spinU32Callee] = some deadCallDestSpinProg ∧
    translateFnInProg (fnNameMap deadCallDestSpinCaller [spinU32Callee])
      deadCallDestSpinCaller = some deadCallDestSpinFn ∧
    CtxOk deadCallDestSpinCaller ctxCallSpin ∧
    argsOk deadCallDestSpinCaller callDestSpinArgs = true ∧
    ProgEnvOk deadCallDestSpinProg (fnNameMap deadCallDestSpinCaller [spinU32Callee])
      deadCallDestSpinMInit :=
  ⟨rfl, rfl, ctxDeadCallDestSpin_ok, by decide, progEnvOk_fnPtrMap rfl rfl (by decide)⟩

private def nextDeadSpinState (s : MachineState) : MachineState :=
  match stepMirFn deadCallDestSpinCaller s with
  | .tau (.running s') => s'
  | _ => s

private def deadCallDestSpinS1 : MachineState := nextDeadSpinState deadCallDestSpinS0

private def deadCallDestSpinS2 : MachineState := nextDeadSpinState deadCallDestSpinS1

private def deadCallDestSpinS3 : MachineState := nextDeadSpinState deadCallDestSpinS2

/-- Four-state silent-step invariant: `StorageLive(_2)`, `StorageDead(_2)`, the
call (which Anneal performs without reading the dead `_2`), and the callee's
`Goto(bb0)` self-loop. -/
def DeadCallDestSpinInv (s : MachineState) : Prop :=
  s = deadCallDestSpinS0 ∨ s = deadCallDestSpinS1 ∨ s = deadCallDestSpinS2 ∨
    s = deadCallDestSpinS3

private theorem deadCallDestSpin_step (s : MachineState) (h : DeadCallDestSpinInv s) :
    ∃ s', stepMirFn deadCallDestSpinCaller s = .tau (.running s') ∧
      DeadCallDestSpinInv s' := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨deadCallDestSpinS1, rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨deadCallDestSpinS2, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨deadCallDestSpinS3, rfl, Or.inr (Or.inr (Or.inr rfl))⟩
  · exact ⟨deadCallDestSpinS3, rfl, Or.inr (Or.inr (Or.inr rfl))⟩

theorem deadCallDestSpin_noUB :
    MirNoUBTree
      (mirCallTreeWithCallees deadCallDestSpinCaller callDestSpinArgs [spinU32Callee]) :=
  treeSafe_of_tau_inv deadCallDestSpin_step (Or.inl rfl)

theorem deadCallDestSpin_noRet (tr : List (Event MirEffect)) (o : MirOutcome) :
    ¬ ReachesRet
      (mirCallTreeWithCallees deadCallDestSpinCaller callDestSpinArgs [spinU32Callee]) tr o :=
  noRet_of_tau_inv deadCallDestSpin_step (Or.inl rfl) tr o

theorem deadCallDestSpin_minirust_ub :
    Interp.steps 4 deadCallDestSpinMInit = .error (.ub "access to a dead local") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

/-- The conclusion of `mirCallWithCallees_noUB` (instantiated at `n = 4`) fails
for `deadCallDestSpinCaller`, although its tree is `MirNoUBTree`. -/
theorem deadCallDestSpin_noUB_transfer_fails :
    MirNoUBTree
      (mirCallTreeWithCallees deadCallDestSpinCaller callDestSpinArgs [spinU32Callee]) ∧
    Interp.steps 4 deadCallDestSpinMInit = .error (.ub "access to a dead local") ∧
    ¬ ∃ k s' mRet tr v mem, k < 4 ∧ Interp.steps k deadCallDestSpinMInit = .ok mRet ∧
      ReturnRel deadCallDestSpinCaller ctxCallSpin s' v mRet ∧
      ReachesRet
        (mirCallTreeWithCallees deadCallDestSpinCaller callDestSpinArgs [spinU32Callee])
        tr (.normal (v, mem)) :=
  ⟨deadCallDestSpin_noUB, deadCallDestSpin_minirust_ub,
    fun ⟨_, _, _, tr, _, _, _, _, _, hret⟩ => deadCallDestSpin_noRet tr _ hret⟩

/-- Identity callee `fn id_i8_callee(x: i8) -> i8 { x }`. -/
def idI8Callee : CapturedMir where
  defPath := "witness::id_i8_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, i8Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

/-- Necessity of `callArgsOk`'s parameter-type check: passing the `u32` local
`_1` to `idI8Callee`'s `i8` parameter. Anneal's `initLocals` stores the argument
value without consulting the parameter type, so the call returns `7` without
UB, whereas MiniRust's `create_frame` finds
`check_abi_compatibility(u32, i8) = false` and faults at step 2. -/
def abiArgMismatchCaller : CapturedMir where
  defPath := "witness::abi_arg_mismatch_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::id_i8_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiI8 1
  layouts := emptyLayoutTable
  allocations := []

theorem abiArgMismatch_rejected :
    callArgsOk abiArgMismatchCaller.layouts abiArgMismatchCaller.localDecls [i8Decl] [.copy (local_ 1)] = false ∧
    progInFragment abiArgMismatchCaller [idI8Callee] = false := by
  decide

def abiArgMismatchProg : Gen.Program :=
  (translateProg abiArgMismatchCaller [idI8Callee]).getD emptyProg

def abiArgMismatchFn : Gen.Function :=
  (translateFnInProg (fnNameMap abiArgMismatchCaller [idI8Callee])
    abiArgMismatchCaller).getD callerFnI8

theorem abiArgMismatch_translate :
    translateProg abiArgMismatchCaller [idI8Callee] = some abiArgMismatchProg := rfl

def abiArgMismatchArgs : List Value := [.scalar ⟨7, 4⟩]

def abiArgMismatchS0 : MachineState :=
  initMachineStateWithCallees abiArgMismatchCaller abiArgMismatchArgs [idI8Callee]

def abiArgMismatchMInit : Mach :=
  multiMachineWithCtx ctxCalleeDivZero abiArgMismatchProg 2 abiArgMismatchCaller
    abiArgMismatchFn abiArgMismatchS0.frame.locals abiArgMismatchFn.start

theorem abiArgMismatch_anneal_ret :
    ReachesRet (mirCallTreeWithCallees abiArgMismatchCaller abiArgMismatchArgs [idI8Callee]) []
      (.normal (.scalar ⟨7, 4⟩,
        { abiArgMismatchS0.memory with activeCallee := some abiArgMismatchCaller })) :=
  runA_sound abiArgMismatchCaller 10 _ _ _ rfl

theorem abiArgMismatch_noUB :
    MirNoUBTree (mirCallTreeWithCallees abiArgMismatchCaller abiArgMismatchArgs [idI8Callee]) :=
  runA_noUB abiArgMismatchCaller 10 _ _ _ rfl

theorem abiArgMismatch_minirust_ub :
    Interp.steps 2 abiArgMismatchMInit =
      .error (.ub "call ABI violation: argument types are not compatible") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

/-- The conclusion of `mirCallWithCallees_noUB` (at `n = 2`) fails for
`abiArgMismatchCaller`: MiniRust's stack still has the entry frame at steps `0`
and `1`, so no `ReturnRel` precedes the UB. -/
theorem abiArgMismatch_noUB_transfer_fails :
    MirNoUBTree (mirCallTreeWithCallees abiArgMismatchCaller abiArgMismatchArgs [idI8Callee]) ∧
    Interp.steps 2 abiArgMismatchMInit =
      .error (.ub "call ABI violation: argument types are not compatible") ∧
    ¬ ∃ k s' mRet tr v mem, k < 2 ∧ Interp.steps k abiArgMismatchMInit = .ok mRet ∧
      ReturnRel abiArgMismatchCaller ctxCalleeDivZero s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees abiArgMismatchCaller abiArgMismatchArgs [idI8Callee])
        tr (.normal (v, mem)) :=
  ⟨abiArgMismatch_noUB, abiArgMismatch_minirust_ub,
    fun ⟨_, _, _, _, _, _, hk, hsteps, hret, _⟩ =>
      no_returnRel_before (mInit := abiArgMismatchMInit) (n := 2) (by decide +kernel)
        hk hsteps hret⟩

/-- Necessity of `callDestOk`'s return-type check: writing `idI8Callee`'s `i8`
result into the `u32` return place `_0`. Anneal's `writePlaceValue` replaces the
root slot without consulting its type, so the call returns `5` without UB,
whereas MiniRust's `create_frame` finds `check_abi_compatibility(u32, i8) =
false` for the return types and faults at step 2. -/
def abiRetMismatchCaller : CapturedMir where
  defPath := "witness::abi_ret_mismatch_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, i8Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::id_i8_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem abiRetMismatch_rejected :
    callDestOk abiRetMismatchCaller.localDecls (mustLiveBefore abiRetMismatchCaller 0 0)
      (tupleInitBefore abiRetMismatchCaller 0 0) i8Decl (local_ 0) = false ∧
    progInFragment abiRetMismatchCaller [idI8Callee] = false := by
  decide

def abiRetMismatchProg : Gen.Program :=
  (translateProg abiRetMismatchCaller [idI8Callee]).getD emptyProg

def abiRetMismatchFn : Gen.Function :=
  (translateFnInProg (fnNameMap abiRetMismatchCaller [idI8Callee])
    abiRetMismatchCaller).getD callerFn

theorem abiRetMismatch_translate :
    translateProg abiRetMismatchCaller [idI8Callee] = some abiRetMismatchProg := rfl

def abiRetMismatchArgs : List Value := [.scalar ⟨5, 1⟩]

def abiRetMismatchS0 : MachineState :=
  initMachineStateWithCallees abiRetMismatchCaller abiRetMismatchArgs [idI8Callee]

def abiRetMismatchMInit : Mach :=
  multiMachineWithCtx ctxCallSpin abiRetMismatchProg 2 abiRetMismatchCaller
    abiRetMismatchFn abiRetMismatchS0.frame.locals abiRetMismatchFn.start

theorem abiRetMismatch_anneal_ret :
    ReachesRet (mirCallTreeWithCallees abiRetMismatchCaller abiRetMismatchArgs [idI8Callee]) []
      (.normal (.scalar ⟨5, 1⟩,
        { abiRetMismatchS0.memory with activeCallee := some abiRetMismatchCaller })) :=
  runA_sound abiRetMismatchCaller 10 _ _ _ rfl

theorem abiRetMismatch_noUB :
    MirNoUBTree (mirCallTreeWithCallees abiRetMismatchCaller abiRetMismatchArgs [idI8Callee]) :=
  runA_noUB abiRetMismatchCaller 10 _ _ _ rfl

theorem abiRetMismatch_minirust_ub :
    Interp.steps 2 abiRetMismatchMInit =
      .error (.ub "call ABI violation: return types are not compatible") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

/-- The conclusion of `mirCallWithCallees_noUB` (at `n = 2`) fails for
`abiRetMismatchCaller`. -/
theorem abiRetMismatch_noUB_transfer_fails :
    MirNoUBTree (mirCallTreeWithCallees abiRetMismatchCaller abiRetMismatchArgs [idI8Callee]) ∧
    Interp.steps 2 abiRetMismatchMInit =
      .error (.ub "call ABI violation: return types are not compatible") ∧
    ¬ ∃ k s' mRet tr v mem, k < 2 ∧ Interp.steps k abiRetMismatchMInit = .ok mRet ∧
      ReturnRel abiRetMismatchCaller ctxCallSpin s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees abiRetMismatchCaller abiRetMismatchArgs [idI8Callee])
        tr (.normal (v, mem)) :=
  ⟨abiRetMismatch_noUB, abiRetMismatch_minirust_ub,
    fun ⟨_, _, _, _, _, _, hk, hsteps, hret, _⟩ =>
      no_returnRel_before (mInit := abiRetMismatchMInit) (n := 2) (by decide +kernel)
        hk hsteps hret⟩

/-- Callee ignoring its parameter (`fn const5_callee(_x: u32) -> u32 { 5 }`). -/
def const5Callee : CapturedMir where
  defPath := "witness::const5_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 5)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Necessity of `callTerminatorOk`'s argument-count check: calling the unary
`const5Callee` with no arguments. Anneal's `initLocals` leaves the missing
parameter `_1` dead, which `const5Callee` never reads, so the call returns `5`
without UB, whereas MiniRust's `create_frame` faults at step 2 because
`func.args.len() != caller_args.len()`. -/
def argCountMismatchCaller : CapturedMir where
  defPath := "witness::arg_count_mismatch_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::const5_callee") [] (local_ 0) (some 1)
        .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

theorem argCountMismatch_rejected :
    callTerminatorOk [const5Callee] argCountMismatchCaller 0
      (mkTerm (.call (fnDefOp "witness::const5_callee") [] (local_ 0) (some 1) .continue_)) =
      false ∧
    progInFragment argCountMismatchCaller [const5Callee] = false := by
  decide

def argCountMismatchProg : Gen.Program :=
  (translateProg argCountMismatchCaller [const5Callee]).getD emptyProg

def argCountMismatchFn : Gen.Function :=
  (translateFnInProg (fnNameMap argCountMismatchCaller [const5Callee])
    argCountMismatchCaller).getD callerFn

theorem argCountMismatch_translate :
    translateProg argCountMismatchCaller [const5Callee] = some argCountMismatchProg := rfl

def argCountMismatchS0 : MachineState :=
  initMachineStateWithCallees argCountMismatchCaller [] [const5Callee]

def argCountMismatchMInit : Mach :=
  multiMachineWithCtx ctxCallSpin argCountMismatchProg 2 argCountMismatchCaller
    argCountMismatchFn argCountMismatchS0.frame.locals argCountMismatchFn.start

theorem argCountMismatch_anneal_ret :
    ReachesRet (mirCallTreeWithCallees argCountMismatchCaller [] [const5Callee]) []
      (.normal (.scalar ⟨5, 4⟩,
        { argCountMismatchS0.memory with activeCallee := some argCountMismatchCaller })) :=
  runA_sound argCountMismatchCaller 10 _ _ _ rfl

theorem argCountMismatch_noUB :
    MirNoUBTree (mirCallTreeWithCallees argCountMismatchCaller [] [const5Callee]) :=
  runA_noUB argCountMismatchCaller 10 _ _ _ rfl

theorem argCountMismatch_minirust_ub :
    Interp.steps 2 argCountMismatchMInit =
      .error (.ub "call ABI violation: number of arguments does not agree") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

/-- The conclusion of `mirCallWithCallees_noUB` (at `n = 2`) fails for
`argCountMismatchCaller`. -/
theorem argCountMismatch_noUB_transfer_fails :
    MirNoUBTree (mirCallTreeWithCallees argCountMismatchCaller [] [const5Callee]) ∧
    Interp.steps 2 argCountMismatchMInit =
      .error (.ub "call ABI violation: number of arguments does not agree") ∧
    ¬ ∃ k s' mRet tr v mem, k < 2 ∧ Interp.steps k argCountMismatchMInit = .ok mRet ∧
      ReturnRel argCountMismatchCaller ctxCallSpin s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees argCountMismatchCaller [] [const5Callee])
        tr (.normal (v, mem)) :=
  ⟨argCountMismatch_noUB, argCountMismatch_minirust_ub,
    fun ⟨_, _, _, _, _, _, hk, hsteps, hret, _⟩ =>
      no_returnRel_before (mInit := argCountMismatchMInit) (n := 2) (by decide +kernel)
        hk hsteps hret⟩

/-! ### Pre-call statement `move` passed as a call argument

`stmtMoveThenCallArg`
(`StorageLive(_2); _2 = move _1; _0 = idU32Callee(copy _1)`)
disagrees in the forward direction: Anneal faults reading the moved-out `_1`,
while MiniRust (whose statement `move` is a plain `Load`) passes the stale `7`
and returns it, so `termReadsOk`'s `readsOk (dst :: mo) argOps` is necessary
for `mirCallWithCallees_ub`. -/

def stmtMoveThenCallArgProg : Gen.Program :=
  (translateProg stmtMoveThenCallArg [idU32Callee]).getD emptyProg

def stmtMoveThenCallArgFn : Gen.Function :=
  (translateFnInProg (fnNameMap stmtMoveThenCallArg [idU32Callee])
    stmtMoveThenCallArg).getD callerFn

theorem stmtMoveThenCallArg_translate :
    translateProg stmtMoveThenCallArg [idU32Callee] = some stmtMoveThenCallArgProg := rfl

def stmtMoveThenCallArgArgs : List Value := [.scalar ⟨7, 4⟩]

def stmtMoveThenCallArgS0 : MachineState :=
  initMachineStateWithCallees stmtMoveThenCallArg stmtMoveThenCallArgArgs [idU32Callee]

def stmtMoveThenCallArgMInit : Mach :=
  multiMachineWithCtx ctxCallSpin stmtMoveThenCallArgProg 2 stmtMoveThenCallArg
    stmtMoveThenCallArgFn stmtMoveThenCallArgS0.frame.locals stmtMoveThenCallArgFn.start

theorem stmtMoveThenCallArg_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees stmtMoveThenCallArg stmtMoveThenCallArgArgs [idU32Callee]) tr u ∧
      FaultNow u :=
  faultsA_sound stmtMoveThenCallArg 10 _ (by decide)

theorem stmtMoveThenCallArg_minirust_ret :
    (Interp.steps 8 stmtMoveThenCallArgMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 7 }, [1]) := by
  decide +kernel

/-- The conclusion of `mirCallWithCallees_ub` fails for `stmtMoveThenCallArg`:
Anneal reaches UB, but MiniRust returns `7` at step `8` and then stops with a
`specPanic` in the external caller frame, never raising UB. -/
theorem stmtMoveThenCallArg_ub_transfer_fails :
    (∃ tr u, Reaches
      (mirCallTreeWithCallees stmtMoveThenCallArg stmtMoveThenCallArgArgs [idU32Callee]) tr u ∧
      FaultNow u) ∧
    ¬ ∃ (n : Nat) (msg : String), Interp.steps n stmtMoveThenCallArgMInit = .error (.ub msg) :=
  ⟨stmtMoveThenCallArg_anneal_ub,
    never_ub_of_nonUb_stop (N := 9) (by decide +kernel) (by decide +kernel)⟩

/-! ### Callee `Return` UB in a pushed frame (`StackPopAction::BackToCaller`) -/

/-- Callee returning its uninitialized `_0`
(`fn ret_uninit_callee(x: u32) -> u32` whose only block is `return`). -/
def retUninitCallee : CapturedMir where
  defPath := "witness::ret_uninit_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [{ statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller `_0 = retUninitCallee(copy _1)`: in `progInFragment`, and both
semantics fault on the callee's `Return` (Anneal reads the `.uninit` `_0`;
MiniRust's `typed_load` of the callee's `_0` decodes `Uninit` bytes) before
`StackPopAction::BackToCaller` writes the caller's return place. -/
def calleeRetUninitCaller : CapturedMir where
  defPath := "witness::callee_ret_uninit_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::ret_uninit_callee")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem calleeRetUninit_inFragment :
    progInFragment calleeRetUninitCaller [retUninitCallee] = true := by decide

def calleeRetUninitProg : Gen.Program :=
  (translateProg calleeRetUninitCaller [retUninitCallee]).getD emptyProg

def calleeRetUninitFn : Gen.Function :=
  (translateFnInProg (fnNameMap calleeRetUninitCaller [retUninitCallee])
    calleeRetUninitCaller).getD callerFn

theorem calleeRetUninit_translate :
    translateProg calleeRetUninitCaller [retUninitCallee] = some calleeRetUninitProg := rfl

theorem calleeRetUninit_translateInProg :
    translateFnInProg (fnNameMap calleeRetUninitCaller [retUninitCallee]) calleeRetUninitCaller =
      some calleeRetUninitFn := rfl

def calleeRetUninitArgs : List Value := [.scalar ⟨3, 4⟩]

def calleeRetUninitMInit : Mach :=
  multiMachineWithCtx ctxCallSpin calleeRetUninitProg 2 calleeRetUninitCaller calleeRetUninitFn
    (initMachineStateWithCallees calleeRetUninitCaller calleeRetUninitArgs
      [retUninitCallee]).frame.locals
    calleeRetUninitFn.start

theorem ctxCalleeRetUninit_ok : CtxOk calleeRetUninitCaller ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [calleeRetUninitCaller] at hd; subst hd; decide
    | 1, _, hd => simp [calleeRetUninitCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [calleeRetUninitCaller] at hi
  ret := by
    intro d hd; simp [calleeRetUninitCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem calleeRetUninit_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees calleeRetUninitCaller calleeRetUninitArgs [retUninitCallee]) tr u ∧
      FaultNow u :=
  faultsA_sound calleeRetUninitCaller 10 _ (by decide)

theorem calleeRetUninit_minirust_ub :
    ∃ (n : Nat) (msg : String), Interp.steps n calleeRetUninitMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := calleeRetUninit_anneal_ub
  exact mirCallWithCallees_ub calleeRetUninit_inFragment calleeRetUninit_translate
    calleeRetUninit_translateInProg ctxCallSpin ctxCalleeRetUninit_ok calleeRetUninitArgs
    (by decide) calleeRetUninitMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf

/-- The callee-`Return` fault is localized (`mirCallWithCallees_ub_rel`):
MiniRust reaches in `n` steps a machine still `MultiStateRel`-related to Anneal,
no intermediate step `k ≤ n` satisfies `ReturnRel`, and the very next step
(`n + 1`) raises UB. -/
theorem calleeRetUninit_minirust_ub_rel :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n calleeRetUninitMInit = .ok mLast ∧
      MultiStateRel calleeRetUninitCaller [retUninitCallee] calleeRetUninitProg ctxCallSpin
        sLast mLast ∧
      (∀ s' v, ¬ ReturnRel calleeRetUninitCaller ctxCallSpin s' v mLast) ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) calleeRetUninitMInit = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k calleeRetUninitMInit = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := calleeRetUninit_anneal_ub
  obtain ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩ :=
    mirCallWithCallees_ub_rel calleeRetUninit_inFragment calleeRetUninit_translate
      calleeRetUninit_translateInProg ctxCallSpin ctxCalleeRetUninit_ok calleeRetUninitArgs
      (by decide) calleeRetUninitMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf
  exact ⟨n, sLast, mLast, msg, hsteps, hrel, fun _ _ => hrel.not_returnRel, hstep, hsteps1, hno⟩

theorem calleeRetUninit_minirust_direct :
    Interp.steps 4 calleeRetUninitMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  eq_error_ub_of_ubMsg? (by decide +kernel)

theorem calleeRetUninit_converse_error :
    (∃ msg,
      Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u,
        Reaches (mirCallTreeWithCallees calleeRetUninitCaller calleeRetUninitArgs
          [retUninitCallee]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 4 ∧ Interp.steps k calleeRetUninitMInit = .ok mRet ∧
      ReturnRel calleeRetUninitCaller ctxCallSpin s' v mRet ∧
      ReachesRet (mirCallTreeWithCallees calleeRetUninitCaller calleeRetUninitArgs
        [retUninitCallee]) tr (.normal (v, mem))) :=
  mirCallWithCallees_steps_error calleeRetUninit_inFragment calleeRetUninit_translate
    calleeRetUninit_translateInProg ctxCallSpin ctxCalleeRetUninit_ok calleeRetUninitArgs
    (by decide) calleeRetUninitMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl
    calleeRetUninit_minirust_direct

/-! ### Pass `B4`: localized single-body and multi-function UB witnesses, and
fixed-point convergence witnesses -/

/-- Single-body localized UB from `f.start` (`mirCall_ub_rel`) on `retUninit`:
MiniRust steps to a `StateRel`-related state `mLast` with `¬ ReturnRel` at every
prefix step `k ≤ n`, and the next step (`n + 1`) raises UB. -/
theorem retUninit_minirust_ub_rel_from_start :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n retUninitMInit = .ok mLast ∧
      StateRel retUninit retUninitFn ctx0 sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) retUninitMInit = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k retUninitMInit = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := retUninit_anneal_ub
  exact mirCall_ub_rel retUninit_inFragment retUninit_translate ctx0 (ctx0_ok1 rfl) []
    (by decide) retUninitMInit rfl rfl rfl hr hf

/-- Single-body localized UB from `f.start` (`run_ub_rel_from_start`) on
`negMention` with input `0` (branching into `Terminator::Unreachable`). -/
theorem negMention0_minirust_ub_rel_from_start :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n negMention0MInit = .ok mLast ∧
      StateRel negMention negMentionFn ctx0 sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) negMention0MInit = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k negMention0MInit = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := negMention0_anneal_ub
  exact run_ub_rel_from_start negMention_inFragment negMention_translate ctx0 negMention0S0
    negMention0MInit negMention0_startRel hr hf

/-- Multi-function localized UB (`mirCallWithCallees_ub_rel`) on
`calleeDivZeroCaller` faulting inside `divTenI8Callee`, with prefix-wide
`¬ ReturnRel` across every intermediate step `k ≤ n`. -/
theorem calleeDivZero_minirust_ub_rel :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n calleeDivZeroMInit = .ok mLast ∧
      MultiStateRel calleeDivZeroCaller [divTenI8Callee] calleeDivZeroProg ctxCalleeDivZero
        sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) calleeDivZeroMInit = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k calleeDivZeroMInit = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := calleeDivZero_anneal_ub
  exact mirCallWithCallees_ub_rel calleeDivZero_inFragment calleeDivZero_translate
    calleeDivZeroCaller_translateInProg ctxCalleeDivZero ctxCalleeDivZero_ok calleeDivZeroArgs
    (by decide) calleeDivZeroMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf

/-- Multi-function localized UB (`mirCallWithCallees_ub_rel`) on
`callArgUbCaller` faulting during call-argument evaluation. -/
theorem callArgUb_minirust_ub_rel :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n callArgUbMInit = .ok mLast ∧
      MultiStateRel callArgUbCaller [idU32Callee] callArgUbProg ctxCallArgUb sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) callArgUbMInit = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k callArgUbMInit = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := callArgUb_anneal_ub
  exact mirCallWithCallees_ub_rel callArgUb_inFragment callArgUb_translate
    callArgUbCaller_translateInProg ctxCallArgUb ctxCallArgUb_ok [] (by decide)
    callArgUbMInit (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf

/-- Multi-function localized UB (`mirCallWithCallees_ub_rel`) on
`callMoveReuse` faulting in caller `bb1` after a completed callee return. -/
theorem callMoveReuse_minirust_ub_rel :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n callMoveReuseMInit = .ok mLast ∧
      MultiStateRel callMoveReuse [idU32Callee] callMoveReuseProg ctxCallSpin sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) callMoveReuseMInit = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k callMoveReuseMInit = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := callMoveReuse_anneal_ub
  exact mirCallWithCallees_ub_rel callMoveReuse_inFragment callMoveReuse_translate
    callMoveReuse_translateInProg ctxCallSpin ctxCallMoveReuse_ok
    [.scalar ⟨7, 4⟩] (by decide) callMoveReuseMInit
    (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf

/-- Unconditional fixed-point stabilization of `iterLiveEntries` and
`livenessOk_eq_true` on `projDestCaller` and `deadCallDestSpinCaller`. -/
theorem projDestCaller_liveness_stabilizes :
    (let fuel := projDestCaller.basicBlocks.length * (projDestCaller.localDecls.length + 1)
     stepLiveEntries projDestCaller
       (iterLiveEntries fuel projDestCaller (initLiveEntries projDestCaller)) =
     iterLiveEntries fuel projDestCaller (initLiveEntries projDestCaller)) ∧
    livenessOk projDestCaller = true ∧
    (let fuel :=
       deadCallDestSpinCaller.basicBlocks.length *
         (deadCallDestSpinCaller.localDecls.length + 1)
     stepLiveEntries deadCallDestSpinCaller
       (iterLiveEntries fuel deadCallDestSpinCaller (initLiveEntries deadCallDestSpinCaller)) =
     iterLiveEntries fuel deadCallDestSpinCaller (initLiveEntries deadCallDestSpinCaller)) ∧
    livenessOk deadCallDestSpinCaller = true :=
  ⟨iterLiveEntries_stabilizes (body := projDestCaller) (by decide),
   livenessOk_eq_true (body := projDestCaller) (by decide),
   iterLiveEntries_stabilizes (body := deadCallDestSpinCaller) (by decide),
   livenessOk_eq_true (body := deadCallDestSpinCaller) (by decide)⟩

/-- Unconditional fixed-point stabilization of `iterTupleInitEntries` and
`tupleInitOk_eq_true` on `projDestCaller` and `uninitProjCallDestCaller`. -/
theorem projDestCaller_tupleInit_stabilizes :
    (let fuel := projDestCaller.basicBlocks.length * (projDestCaller.localDecls.length + 1)
     stepTupleInitEntries projDestCaller
       (iterTupleInitEntries fuel projDestCaller (initTupleEntries projDestCaller)) =
     iterTupleInitEntries fuel projDestCaller (initTupleEntries projDestCaller)) ∧
    tupleInitOk projDestCaller = true ∧
    (let fuel :=
       uninitProjCallDestCaller.basicBlocks.length *
         (uninitProjCallDestCaller.localDecls.length + 1)
     stepTupleInitEntries uninitProjCallDestCaller
       (iterTupleInitEntries fuel uninitProjCallDestCaller
         (initTupleEntries uninitProjCallDestCaller)) =
     iterTupleInitEntries fuel uninitProjCallDestCaller
       (initTupleEntries uninitProjCallDestCaller)) ∧
    tupleInitOk uninitProjCallDestCaller = true :=
  ⟨iterTupleInitEntries_stabilizes projDestCaller,
   tupleInitOk_eq_true projDestCaller,
   iterTupleInitEntries_stabilizes uninitProjCallDestCaller,
   tupleInitOk_eq_true uninitProjCallDestCaller⟩

/-- Greatest post-fixed-point optimality of `liveAtEntry` instantiated on
`projDestCaller` (`[[0, 1], [0, 1], [0, 1, 2]]` is a post-fixed point). -/
theorem projDestCaller_liveAtEntry_greatest {dst : Nat}
    (hdst : dst < projDestCaller.basicBlocks.length) :
    ∀ i ∈ ([[0, 1], [0, 1], [0, 1, 2]] : List (List Nat)).getD dst [],
      i ∈ liveAtEntry projDestCaller dst :=
  liveAtEntry_greatest
    (by decide)
    (fun d hd hne i hi => by
      have hd' : d < 3 := by simpa [projDestCaller] using hd
      revert i hi
      rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl <;> decide)
    (fun s d bb hbb hd ht i hi => by
      have hs : s < 3 := by
        have := (List.getElem?_eq_some_iff.mp hbb).1
        simpa [projDestCaller] using this
      have hd' : d < 3 := by simpa [projDestCaller] using hd
      revert bb hbb ht i hi
      rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl <;>
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;>
      (intro bb hbb; simp [projDestCaller] at hbb; subst hbb; decide))
    hdst

/-- Greatest post-fixed-point optimality of `tupleInitAtEntry` instantiated on
`projDestCaller` (`[[], [0], [0]]` is a post-fixed point). -/
theorem projDestCaller_tupleInitAtEntry_greatest {dst : Nat}
    (hdst : dst < projDestCaller.basicBlocks.length) :
    ∀ i ∈ ([[], [0], [0]] : List (List Nat)).getD dst [],
      i ∈ tupleInitAtEntry projDestCaller dst :=
  tupleInitAtEntry_greatest
    (by decide)
    (fun d hd hne i hi => by
      have hd' : d < 3 := by simpa [projDestCaller] using hd
      revert i hi
      rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl <;> decide)
    (fun s d bb hbb hd ht i hi => by
      have hs : s < 3 := by
        have := (List.getElem?_eq_some_iff.mp hbb).1
        simpa [projDestCaller] using this
      have hd' : d < 3 := by simpa [projDestCaller] using hd
      revert bb hbb ht i hi
      rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl <;>
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;>
      (intro bb hbb; simp [projDestCaller] at hbb; subst hbb; decide))
    hdst

/-! ### `prog.start` versus the external caller -/

/-- Whether an `Interp` result is a `Stop.unsupported`. -/
def isUnsupportedStop {α : Type} : Interp α → Bool
  | .error (.unsupported _) => true
  | _ => false

/-- The translation of the `extern "C"` callee `cAbiCallee`. -/
def cAbiCalleeFn : Gen.Function :=
  (translateFnInProg (fnNameMap cAbiCaller [cAbiCallee]) cAbiCallee).getD callerFn

/-- The dangling, aligned pointer behind `build::unit_place()`. -/
def unitPlacePtr : Ptr := { addr := 1, provenance := none }

/-- Why the correspondence starts at `fEntry.start` under an external `rootCtx`
rather than at `prog.start`. `mkStartFn`'s first block evaluates
`build::unit_place()`, a `PlaceExpr::Deref` of the dangling raw pointer at
address `1`; since `MR-4.2` transcribes `PlaceExpr::Deref`, this yields the
aligned zero-sized place of type `unit_type()` without touching memory. But the
`Terminator::Call` that block performs (Rust calling convention, no arguments, a
`()` return place, as in `minimize`'s `mk_start_fn`) fails `create_frame` for
an entry such as `callerMain`, which returns `u32`, and for any `extern "C"`
entry such as `cAbiCallee`. `rootCtx` instead supplies the entry's arguments
and a return place of its own type (`CtxOk`). -/
theorem progStart_outside_fragment :
    evalPlace callerCallee20MInit buildUnitPlace =
      .ok (({ ptr := { thin_pointer := unitPlacePtr, metadata := none }, aligned := true },
        unitTy), callerCallee20MInit) ∧
    createFrame callerCallee20MInit callerMainFn
      (.BackToCaller (some (bbName 1)) (some (bbName 2)) unitPlacePtr) .Rust unitTy [] =
      .error (.ub "call ABI violation: return types are not compatible") ∧
    createFrame callerCallee20MInit cAbiCalleeFn
      (.BackToCaller (some (bbName 1)) (some (bbName 2)) unitPlacePtr) .Rust unitTy [] =
      .error (.ub "call ABI violation: calling conventions are not the same") :=
  ⟨rfl, eq_error_ub_of_ubMsg? (by decide +kernel), eq_error_ub_of_ubMsg? (by decide +kernel)⟩

/-! ## `MR-4.2`: intrinsics

Ground-truth checks of the transcribed `Machine::eval_intrinsic`
(`evalIntrinsic`), `Terminator::Intrinsic` (`evalTerminator`), and
`translateRsIntrinsic` (`tooling/minimize/src/bb.rs`) on concrete machines, plus
end-to-end correspondence and dataflow necessity witnesses for `Assume`
statements (`StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))`):
`minimize` ends the current MiniRust block at every `Assume` in a
`Terminator::Intrinsic` of `IntrinsicOp::Assume` whose next block is fresh
(`translateStmtResult`, `splitStmts`), and `progInFragment` (`progStatementOk`)
connects arbitrary multi-`Assume` block chains (`SegPc`, `SegChain`) to
`mirCallWithCallees_ret` and `mirCallWithCallees_ub_rel`. -/

/-! ### `Machine::eval_intrinsic` on a concrete machine -/

/-- The integer of a `Value::Int`. -/
def intOfVal? : Val → Option Int
  | .Int i => some i
  | _ => none

/-- The Boolean of a `Value::Bool`. -/
def boolOfVal? : Val → Option Bool
  | .Bool b => some b
  | _ => none

/-- Whether an `Interp` result is `Stop.memoryLeak`. -/
def isMemoryLeakStop {α : Type} : Interp α → Bool
  | .error .memoryLeak => true
  | _ => false

/-- Whether an `Interp` result is `Stop.machineStop`. -/
def isMachineStop {α : Type} : Interp α → Bool
  | .error .machineStop => true
  | _ => false

/-- Whether a MiniRust value is `unit_value()` (`Value::Tuple(list![])`). -/
def isUnitValue : Val → Bool
  | .Tuple [] => true
  | _ => false

/-- `IntrinsicOp::Abort` throws `TerminationInfo::Abort`; `IntrinsicOp::Exit`
runs the leak check, which passes on a machine without live `Heap`
allocations, and then throws `TerminationInfo::MachineStop`. -/
theorem evalIntrinsic_abort_exit :
    evalIntrinsic callerCallee20MInit .Abort [] Interp.unitType = .error .abort ∧
    evalIntrinsic callerCallee20MInit .Exit [] Interp.unitType = .error .machineStop :=
  ⟨rfl, rfl⟩

/-- `IntrinsicOp::Assume` returns `unit_value()` on `true` and raises each of
its four UB checks: a violated condition, a non-Boolean argument, a wrong
argument count, and a return type other than `unit_type()`. -/
theorem evalIntrinsic_assume :
    evalIntrinsic callerCallee20MInit .Assume [(.Bool true, .Bool)] Interp.unitType =
      .ok (Interp.unitValue, callerCallee20MInit) ∧
    evalIntrinsic callerCallee20MInit .Assume [(.Bool false, .Bool)] Interp.unitType =
      .error (.ub "`Assume` intrinsic called on condition that is violated") ∧
    evalIntrinsic callerCallee20MInit .Assume [(.Int 1, .Int u8Ty)] Interp.unitType =
      .error (.ub "invalid argument for `Assume` intrinsic: not a Boolean") ∧
    evalIntrinsic callerCallee20MInit .Assume [] Interp.unitType =
      .error (.ub "invalid number of arguments for `Assume` intrinsic") ∧
    evalIntrinsic callerCallee20MInit .Assume [(.Bool true, .Bool), (.Bool true, .Bool)]
        Interp.unitType =
      .error (.ub "invalid number of arguments for `Assume` intrinsic") ∧
    evalIntrinsic callerCallee20MInit .Assume [(.Bool true, .Bool)] .Bool =
      .error (.ub "invalid return type for `Assume` intrinsic") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `IntrinsicOp::PrintStdout` and `IntrinsicOp::PrintStderr` append one line
per integer or Boolean argument to their stream, reject any other value with
UB, and check the `unit_type()` return type first. -/
theorem evalIntrinsic_print :
    (evalIntrinsic callerCallee20MInit .PrintStdout
        [(.Int (-7), .Int i32W), (.Bool true, .Bool)] Interp.unitType).toOption.map
        (fun r => (isUnitValue r.1, r.2.stdout.written, r.2.stderr.written)) =
      some (true, ["-7\n", "true\n"], []) ∧
    (evalIntrinsic callerCallee20MInit .PrintStderr [(.Int 42, .Int u32)]
        Interp.unitType).toOption.map
        (fun r => (r.2.stdout.written, r.2.stderr.written)) =
      some ([], ["42\n"]) ∧
    evalIntrinsic callerCallee20MInit .PrintStdout [(Interp.unitValue, Interp.unitType)]
        Interp.unitType =
      .error (.ub "unsupported value for printing") ∧
    evalIntrinsic callerCallee20MInit .PrintStdout [] .Bool =
      .error (.ub "invalid return type for `PrintStdout` intrinsic") := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl⟩

/-- `IntrinsicOp::RawEq` rejects non-pointer arguments, wrong argument counts,
and non-`bool` return types with UB; `IntrinsicOp::PointerWithExposedProvenance`
turns an integer into a thin raw pointer at that address (with no provenance,
since nothing is exposed yet; `IntPtrCast::int2ptr`), while a non-integer
argument is UB. -/
theorem evalIntrinsic_rawEq_withExposed :
    evalIntrinsic callerCallee20MInit .RawEq
      [(.Int 1, .Int u8Ty), (.Int 1, .Int u8Ty)] .Bool =
      .error (.ub "invalid first argument to `RawEq` intrinsic: not a pointer") ∧
    evalIntrinsic callerCallee20MInit .RawEq [(.Int 1, .Int u8Ty)] .Bool =
      .error (.ub "invalid number of arguments for `RawEq` intrinsic") ∧
    evalIntrinsic callerCallee20MInit .RawEq [(.Int 1, .Int u8Ty), (.Int 1, .Int u8Ty)]
        (.Int u8Ty) =
      .error (.ub "invalid return type for `RawEq` intrinsic") ∧
    (evalIntrinsic callerCallee20MInit .PointerWithExposedProvenance
      [(.Int 64, .Int u64W)] (.Ptr (.Raw .None))).toOption.map (·.1) =
      some (.Ptr ⟨⟨64, none⟩, none⟩) ∧
    evalIntrinsic callerCallee20MInit .PointerWithExposedProvenance
        [(.Bool true, .Bool)] (.Ptr (.Raw .None)) =
      .error (.ub "invalid argument for `PointerWithExposedProvenance` intrinsic: not an integer") :=
  ⟨eq_error_ub_of_ubMsg? (by decide +kernel), rfl, rfl, rfl, rfl⟩

/-- Concrete machine with four 4-byte `Stack` allocations (`42u32`, `42u32`,
`99u32`, and 4 `Uninit` bytes) for testing `IntrinsicOp::RawEq` and
`Machine::load_raw_data`. -/
def rawEqMach : Mach :=
  { callerCallee20MInit with
    mem := { memory := {
      allocations := [
        { data := scalarBytes u32 42, addr := 128, align := ⟨4⟩, kind := .Stack, live := true, extra := () },
        { data := scalarBytes u32 42, addr := 256, align := ⟨4⟩, kind := .Stack, live := true, extra := () },
        { data := scalarBytes u32 99, addr := 384, align := ⟨4⟩, kind := .Stack, live := true, extra := () },
        { data := List.replicate 4 .Uninit, addr := 512, align := ⟨4⟩, kind := .Stack, live := true, extra := () }],
      _phantom := {} }, accesses := [] } }

def rawEqPtr (id : Nat) (addr : Int) : Val :=
  .Ptr ⟨⟨addr, some (⟨id⟩, ())⟩, none⟩

def sizedU32RefTy : Gen.Type := .Ptr (.Ref .Immutable sizedU32Pointee)

/-- Full `IntrinsicOp::RawEq` semantics (`spec/lang/step/intrinsics.md`):
compares initialized byte sequences of two sized references (`42u32 == 42u32` is
`true`, `42u32 == 99u32` is `false`), raises UB when any byte is `Uninit`,
raises UB when the two argument types differ (`typeEq`), and raises UB when the
pointer type is `.Raw` rather than `.Ref`. -/
theorem evalIntrinsic_rawEq :
    (evalIntrinsic rawEqMach .RawEq
      [(rawEqPtr 0 128, sizedU32RefTy), (rawEqPtr 1 256, sizedU32RefTy)] .Bool).toOption.bind
        (fun r => boolOfVal? r.1) = some true ∧
    (evalIntrinsic rawEqMach .RawEq
      [(rawEqPtr 0 128, sizedU32RefTy), (rawEqPtr 2 384, sizedU32RefTy)] .Bool).toOption.bind
        (fun r => boolOfVal? r.1) = some false ∧
    evalIntrinsic rawEqMach .RawEq
      [(rawEqPtr 0 128, sizedU32RefTy), (rawEqPtr 3 512, sizedU32RefTy)] .Bool =
      .error (.ub "invalid argument to `RawEq` intrinsic: byte is uninitialized") ∧
    evalIntrinsic rawEqMach .RawEq
      [(rawEqPtr 0 128, sizedU32RefTy), (rawEqPtr 1 256, .Ptr (.Raw .None))] .Bool =
      .error (.ub "invalid arguments to `RawEq` intrinsic: types of arguments are not identical") ∧
    evalIntrinsic rawEqMach .RawEq
      [(rawEqPtr 0 128, .Ptr (.Raw .None)), (rawEqPtr 1 256, .Ptr (.Raw .None))] .Bool =
      .error (.ub "invalid argument to `RawEq` intrinsic: not a reference") :=
  ⟨by decide +kernel, by decide +kernel,
   eq_error_ub_of_ubMsg? (by decide +kernel),
   eq_error_ub_of_ubMsg? (by decide +kernel),
   eq_error_ub_of_ubMsg? (by decide +kernel)⟩

/-- `IntrinsicOp::Allocate`, `IntrinsicOp::Deallocate`, and `IntrinsicOp::Exit`
(`ConcurrentMemory::leak_check`): allocating 4 `Heap` bytes and exiting without
deallocating throws `Stop.memoryLeak`, whereas deallocating with matching size
and alignment and then exiting throws `Stop.machineStop`; negative size,
non-power-of-two alignment, and size mismatch on `Deallocate` raise UB. -/
theorem evalIntrinsic_allocate_deallocate_leak :
    isMemoryLeakStop (do
      let (_, m1) ← evalIntrinsic callerCallee20MInit .Allocate
        [(.Int 4, .Int u64W), (.Int 4, .Int u64W)] (.Ptr (.Raw .None))
      evalIntrinsic m1 .Exit [] Interp.unitType) = true ∧
    isMachineStop (do
      let (p, m1) ← evalIntrinsic callerCallee20MInit .Allocate
        [(.Int 4, .Int u64W), (.Int 4, .Int u64W)] (.Ptr (.Raw .None))
      let (_, m2) ← evalIntrinsic m1 .Deallocate
        [(p, .Ptr (.Raw .None)), (.Int 4, .Int u64W), (.Int 4, .Int u64W)] Interp.unitType
      evalIntrinsic m2 .Exit [] Interp.unitType) = true ∧
    evalIntrinsic callerCallee20MInit .Allocate
      [(.Int (-1), .Int u64W), (.Int 4, .Int u64W)] (.Ptr (.Raw .None)) =
      .error (.ub "invalid size for `Allocate` intrinsic: negative size") ∧
    evalIntrinsic callerCallee20MInit .Allocate
      [(.Int 4, .Int u64W), (.Int 3, .Int u64W)] (.Ptr (.Raw .None)) =
      .error (.ub "invalid alignment for `Allocate` intrinsic: not a power of 2") ∧
    (do
      let (p, m1) ← evalIntrinsic callerCallee20MInit .Allocate
        [(.Int 4, .Int u64W), (.Int 4, .Int u64W)] (.Ptr (.Raw .None))
      evalIntrinsic m1 .Deallocate
        [(p, .Ptr (.Raw .None)), (.Int 8, .Int u64W), (.Int 4, .Int u64W)] Interp.unitType) =
      .error (.ub "deallocating with incorrect size information") :=
  ⟨by decide +kernel, by decide +kernel, rfl, rfl, eq_error_ub_of_ubMsg? (by decide +kernel)⟩

/-- `IntrinsicOp::PointerExposeProvenance` returns the address of a thin
pointer at `usize` and records its provenance as exposed. -/
theorem evalIntrinsic_exposeProvenance :
    (evalIntrinsic callerCallee20MInit .PointerExposeProvenance
        [(.Ptr ⟨⟨128, some (⟨3⟩, ())⟩, none⟩, .Ptr (.Raw .None))] (.Int u64W)).toOption.map
        (fun r => (intOfVal? r.1, r.2.intptrcast.exposed.elems.map (·.1._0))) =
      some (some 128, [3]) ∧
    evalIntrinsic callerCallee20MInit .PointerExposeProvenance
        [(.Ptr ⟨⟨128, some (⟨3⟩, ())⟩, none⟩, .Ptr (.Raw .None))] (.Int u32) =
      .error (.ub "invalid return type for `PointerExposeProvenance` intrinsic") :=
  ⟨by decide +kernel, rfl⟩

/-- `IntrinsicOp::GetUnwindPayload` on a thread with an empty payload stack is
UB. -/
theorem evalIntrinsic_getUnwindPayload_empty :
    evalIntrinsic callerCallee20MInit .GetUnwindPayload [] (.Ptr (.Raw .None)) =
      .error (.ub "GetUnwindPayload: the payload stack is empty") := rfl

/-- The `Terminator::Intrinsic` that `build::abort()` produces stores nothing
and throws `TerminationInfo::Abort`: `unit_place()` evaluates without touching
memory, and `IntrinsicOp::Abort` never returns. -/
theorem evalTerminator_abortTerminator :
    evalTerminator callerCallee20MInit abortTerminator = .error .abort := rfl

/-- `translateRsIntrinsic` (`tooling/minimize/src/bb.rs`) lowers `"raw_eq"` to
`Terminator::Intrinsic(.RawEq, ...)`, `"ctpop"` to `UnOp::Int(.CountOnes)` +
`Goto`, `"exact_div"` to `BinOp::Int(.DivExact)` + `Goto`, `"cold_path"` to a
no-op `Goto`, `"abort"` to `build::abort()`, and rejects unmodeled fallback
intrinsics (`"ctlz"`). -/
theorem translateRsIntrinsic_witness :
    translateRsIntrinsic decls .raw_eq [.copy (local_ 1), .copy (local_ 2)]
        (local_ 0) (some 1) =
      some ⟨[], .Intrinsic .RawEq
        [.Load (.Local (localName 1)), .Load (.Local (localName 2))]
        (.Local (localName 0)) (some (bbName 1))⟩ ∧
    translateRsIntrinsic decls .ctpop [.copy (local_ 1)] (local_ 0) (some 1) =
      some ⟨[.Assign (.Local (localName 0)) (buildCountOnes (.Load (.Local (localName 1))))],
        .Goto (bbName 1)⟩ ∧
    translateRsIntrinsic decls .exact_div [.copy (local_ 1), .copy (local_ 2)]
        (local_ 0) (some 1) =
      some ⟨[.Assign (.Local (localName 0))
        (buildDivExact (.Load (.Local (localName 1))) (.Load (.Local (localName 2))))],
        .Goto (bbName 1)⟩ ∧
    translateRsIntrinsic decls .cold_path [] (local_ 0) (some 1) =
      some ⟨[], .Goto (bbName 1)⟩ ∧
    translateRsIntrinsic decls .abort [] (local_ 0) none =
      some ⟨[], abortTerminator⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### `Assume` statements and `minimize`'s block splitting -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn assume_sub(x: u32, b: bool) -> u32 {
    unsafe { core::intrinsics::assume(b) }; // bb0: assume(copy _2)
    let r = x.wrapping_sub(1);               //      _0 = Sub(copy _1, const 1_u32)
    unsafe { core::intrinsics::assume(b) }; //      assume(copy _2)
    r                                        //      return
}
```
with `r` living in the return place. rustc's `LowerIntrinsics` MIR pass turns
each `assume(b)` call into the statement
`StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(copy _2))`. -/
def assumeSub : CapturedMir where
  defPath := "witness::assume_sub"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.intrinsic (.assume (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 1)) (constU32 1))),
        mkStmt (.intrinsic (.assume (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

/-- The MiniRust function `minimize` produces for `assumeSub`: `translate_bb`
ends `bb0` at each `Assume` in a `Terminator::Intrinsic` whose next block is a
fresh name (`bbName 2`, then `bbName 3`, after `init_bb = bbName 1`), and the
`return` lands in the block that is still open. -/
def assumeSubFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Bool)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[], .Intrinsic .Assume [.Load (.Local (localName 2))] unitPlace
      (some (bbName 2)), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 1))) (.Constant (.Int 1) (.Int u32)))],
      .Intrinsic .Assume [.Load (.Local (localName 2))] unitPlace (some (bbName 3)), .Regular⟩),
    (bbName 3, ⟨[], .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def assumeSubProg : Gen.Program where
  functions := ⟨[(fnName 0, assumeSubFn), (fnName 1, mkStartFn 0)]⟩
  start := fnName 1
  globals := ⟨[]⟩
  vtables := ⟨[]⟩
  traits := ⟨[]⟩

theorem assumeSub_translate : translateProg assumeSub [] = some assumeSubProg := rfl

theorem assumeSub_translateInProg :
    translateFnInProg (fnNameMap assumeSub []) assumeSub = some assumeSubFn := rfl

/-- `progInFragment` (`progStatementOk`) admits `Assume` statements and connects
their split-block translation (`SegPc`, `SegChain`) to the multi-function
correspondence theorems. -/
theorem assumeSub_inFragment : progInFragment assumeSub [] = true := by decide

def ctxAssumeSub : Ctx := ctxWithFns callerFrame retAlloc 1 [128, 256, 384]

theorem ctxAssumeSub_ok : CtxOk assumeSub ctxAssumeSub where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [assumeSub] at hd; subst hd; decide
    | 1, _, hd => simp [assumeSub] at hd; subst hd; decide
    | 2, _, hd => simp [assumeSub] at hd; subst hd; decide
    | _ + 3, hi, _ => simp [assumeSub] at hi
  ret := by
    intro d hd; simp [assumeSub] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def assumeSubArgs (x : Nat) (b : Bool) : List Value :=
  [.scalar ⟨x, 4⟩, .scalar ⟨if b then 1 else 0, 1⟩]

def assumeSubS0 (x : Nat) (b : Bool) : MachineState :=
  initMachineStateWithCallees assumeSub (assumeSubArgs x b) []

def assumeSubMInit (x : Nat) (b : Bool) : Mach :=
  multiMachineWithCtx ctxAssumeSub assumeSubProg 1 assumeSub assumeSubFn
    (assumeSubS0 x b).frame.locals assumeSubFn.start

/-- `runA` returns the scalar `⟨bits, size⟩`. -/
def runsToScalar (body : CapturedMir) (fuel : Nat) (s : MachineState) (bits size : Nat) : Bool :=
  match runA body fuel s with
  | some (_, .normal (.scalar sc, _)) => sc.bits == bits && sc.sizeBytes == size
  | _ => false

/-- A passing `runsToScalar` check is a UB-free return of `⟨bits, size⟩`
(`runA_sound`, `runA_noUB`). -/
theorem runsToScalar_sound {body : CapturedMir} {fuel : Nat} {s : MachineState}
    {bits size : Nat} (h : runsToScalar body fuel s bits size = true) :
    (∃ tr mem, ReachesRet (mirTree body s) tr (.normal (.scalar ⟨bits, size⟩, mem))) ∧
      MirNoUBTree (mirTree body s) := by
  unfold runsToScalar at h
  split at h
  · rename_i tr sc mem hrun
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
    obtain ⟨hb, hs⟩ := h
    have hsc : sc = ⟨bits, size⟩ := by cases sc; simp_all
    subst hsc
    exact ⟨⟨tr, mem, runA_sound body fuel _ _ _ hrun⟩, runA_noUB body fuel _ _ _ hrun⟩
  · exact absurd h Bool.false_ne_true

/-- With `b = true`, Anneal's `assume_sub(20, true)` steps over both `Assume`
statements and returns `19u32` without UB. -/
theorem assumeSub20_anneal_ret :
    (∃ tr mem, ReachesRet (mirCallTreeWithCallees assumeSub (assumeSubArgs 20 true) []) tr
      (.normal (.scalar ⟨19, 4⟩, mem))) ∧
    MirNoUBTree (mirCallTreeWithCallees assumeSub (assumeSubArgs 20 true) []) :=
  runsToScalar_sound (fuel := 10) (by decide)

/-- End-to-end correspondence transfer (`mirCallWithCallees_ret`) for
`assume_sub(20, true)` across two `Assume` block splits in one MIR basic block. -/
theorem assumeSub20_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n (assumeSubMInit 20 true) = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 19 } ∧
      m'.threads = [thread1 ctxAssumeSub
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨⟨tr, mem, hanneal⟩, _⟩ := assumeSub20_anneal_ret
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret assumeSub_inFragment assumeSub_translate
      assumeSub_translateInProg ctxAssumeSub ctxAssumeSub_ok
      (assumeSubArgs 20 true) (by decide) (assumeSubMInit 20 true)
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hanneal
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [assumeSub] at hd; subst hd
  simp [retPtr, ctxAssumeSub, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxAssumeSub, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- MiniRust runs the translation of `assume_sub(20, true)` from `start` in
`5` steps (the init block's `Goto`, the first `Terminator::Intrinsic`, the
`Sub` assignment in `bbName 2`, the second `Terminator::Intrinsic`, and
`Return`), writing the bytes of `19u32` into the caller's return place. -/
theorem assumeSub20_minirust_direct :
    (Interp.steps 5 (assumeSubMInit 20 true)).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 19 }, [1]) := by
  decide +kernel

/-- One Anneal step over the first `Assume` moves from MIR program point
`(bb0, 1)`; the matching MiniRust step (after the init block) lands at the
start of the fresh block `bbName 2`. -/
theorem assumeSub20_split_point :
    (match stepMirFn assumeSub (assumeSubS0 20 true) with
      | .tau (.running s') => some (s'.frame.blockIdx, s'.frame.stmtIdx)
      | _ => none) = some (0, 1) ∧
    (Interp.steps 2 (assumeSubMInit 20 true)).toOption.map
        (fun m => m.threads.map (fun t => t.stack.getLast?.map
          (fun fr => (fr.next_block, fr.next_stmt)))) =
      some [some (bbName 2, 0)] := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- With `b = false`, Anneal's `assume_sub(20, false)` faults (`FaultNow`), and
`mirCallWithCallees_ub_rel` transfers that fault to MiniRust strictly before any
root return. -/
theorem assumeSubFalse_anneal_ub :
    ∃ tr u, Reaches (mirCallTreeWithCallees assumeSub (assumeSubArgs 20 false) []) tr u ∧
      FaultNow u :=
  faultsA_sound assumeSub 5 _ (by decide)

theorem assumeSubFalse_minirust_ub_rel :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n (assumeSubMInit 20 false) = .ok mLast ∧
      MultiStateRel assumeSub [] assumeSubProg ctxAssumeSub sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) (assumeSubMInit 20 false) = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k (assumeSubMInit 20 false) = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := assumeSubFalse_anneal_ub
  obtain ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩ :=
    mirCallWithCallees_ub_rel assumeSub_inFragment assumeSub_translate
      assumeSub_translateInProg ctxAssumeSub ctxAssumeSub_ok
      (assumeSubArgs 20 false) (by decide) (assumeSubMInit 20 false)
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf
  exact ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩

/-- Direct confirmation on `b = false`: Anneal's first step is `MirStepNode.fail .ub`,
and MiniRust's second step (the first `Terminator::Intrinsic`) throws the
`Assume` UB of `eval_intrinsic`. -/
theorem assumeSubFalse_ub :
    stepMirFn assumeSub (assumeSubS0 20 false) = MirStepNode.fail .ub ∧
    Interp.steps 2 (assumeSubMInit 20 false) =
      .error (.ub "`Assume` intrinsic called on condition that is violated") :=
  ⟨rfl, eq_error_ub_of_ubMsg? (by decide +kernel)⟩

/-! ### Multi-frame `Assume` + tuple projection + `Call` (`assumeTupleCallCaller`)
and `Assume` dataflow soundness / necessity witnesses -/

/-- Multi-function caller exercising `Assume(move _3)` inside a split block
before a `TerminatorKind.call` to `idU32Callee`, followed by a second split
block on return (`bb1` containing `Assume(const true)`):
```rust
fn assume_tuple_call(x: u32) -> u32 {
    let pair = AddWithOverflow(x, 5);   // bb0: StorageLive(_2); StorageLive(_3); _2 = AddWithOverflow(_1, 5)
    let ok = !pair.1;                   //      _3 = Not(copy (_2.1))
    unsafe { assume(move ok) };         //      assume(move _3)          [splits bb0 -> bbName 3]
    StorageDead(_3);                    //      StorageDead(_3)
    let r = id_u32_callee(pair.0);      //      _0 = Call(id_u32_callee, [copy (_2.0)]) -> bb1
    unsafe { assume(true) };            // bb1: assume(const true)       [splits bb1 -> bbName 4]
    StorageDead(_2);                    //      StorageDead(_2)
    r                                   //      return
}
```
-/
def assumeTupleCallCaller : CapturedMir where
  defPath := "witness::assume_tuple_call"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, u32BoolTupleDecl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 2) (.binaryOp .addWithOverflow (.copy (local_ 1)) (constU32 5))),
        mkStmt (.assign (local_ 3) (.unaryOp .not (.copy (field1 2)))),
        mkStmt (.intrinsic (.assume (.move (local_ 3)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm (.call (fnDefOp "witness::id_u32_callee")
        [.copy (field0U32 2)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.intrinsic (.assume (.constant { ty := boolDecl.ty, val := .scalar (.int ⟨1, 1⟩) }))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem assumeTupleCall_inFragment :
    progInFragment assumeTupleCallCaller [idU32Callee] = true := by decide

def assumeTupleCallProg : Gen.Program :=
  (translateProg assumeTupleCallCaller [idU32Callee]).getD emptyProg

def assumeTupleCallFn : Gen.Function :=
  (translateFnInProg (fnNameMap assumeTupleCallCaller [idU32Callee])
    assumeTupleCallCaller).getD callerFn

theorem assumeTupleCall_translate :
    translateProg assumeTupleCallCaller [idU32Callee] = some assumeTupleCallProg := rfl

theorem assumeTupleCall_translateInProg :
    translateFnInProg (fnNameMap assumeTupleCallCaller [idU32Callee]) assumeTupleCallCaller =
      some assumeTupleCallFn := rfl

theorem ctxAssumeTupleCall_ok : CtxOk assumeTupleCallCaller ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [assumeTupleCallCaller] at hd; subst hd; decide
    | 1, _, hd => simp [assumeTupleCallCaller] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [assumeTupleCallCaller] at hi
  ret := by
    intro d hd; simp [assumeTupleCallCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def assumeTupleCallMInit (x : Nat) : Mach :=
  multiMachineWithCtx ctxCallSpin assumeTupleCallProg 2 assumeTupleCallCaller assumeTupleCallFn
    (initMachineStateWithCallees assumeTupleCallCaller [.scalar ⟨x, 4⟩] [idU32Callee]).frame.locals
    assumeTupleCallFn.start

theorem assumeTupleCall10_anneal_ret :
    (∃ tr mem, ReachesRet (mirCallTreeWithCallees assumeTupleCallCaller [.scalar ⟨10, 4⟩] [idU32Callee]) tr
      (.normal (.scalar ⟨15, 4⟩, mem))) ∧
    MirNoUBTree (mirCallTreeWithCallees assumeTupleCallCaller [.scalar ⟨10, 4⟩] [idU32Callee]) :=
  runsToScalar_sound (fuel := 15) (by decide)

theorem assumeTupleCall10_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n (assumeTupleCallMInit 10) = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 15 } ∧
      m'.threads = [thread1 ctxCallSpin
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨⟨tr, mem, hanneal⟩, _⟩ := assumeTupleCall10_anneal_ret
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret assumeTupleCall_inFragment assumeTupleCall_translate
      assumeTupleCall_translateInProg ctxCallSpin ctxAssumeTupleCall_ok
      [.scalar ⟨10, 4⟩] (by decide) (assumeTupleCallMInit 10)
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hanneal
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [assumeTupleCallCaller] at hd; subst hd
  simp [retPtr, ctxCallSpin, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallSpin, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem assumeTupleCallOv_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees assumeTupleCallCaller [.scalar ⟨4294967295, 4⟩] [idU32Callee]) tr u ∧
      FaultNow u :=
  faultsA_sound assumeTupleCallCaller 10 _ (by decide)

theorem assumeTupleCallOv_minirust_ub_rel :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n (assumeTupleCallMInit 4294967295) = .ok mLast ∧
      MultiStateRel assumeTupleCallCaller [idU32Callee] assumeTupleCallProg ctxCallSpin sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) (assumeTupleCallMInit 4294967295) = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k (assumeTupleCallMInit 4294967295) = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := assumeTupleCallOv_anneal_ub
  obtain ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩ :=
    mirCallWithCallees_ub_rel assumeTupleCall_inFragment assumeTupleCall_translate
      assumeTupleCall_translateInProg ctxCallSpin ctxAssumeTupleCall_ok
      [.scalar ⟨4294967295, 4⟩] (by decide) (assumeTupleCallMInit 4294967295)
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf
  exact ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩

 

/-! ## Multi-frame `Assume` chains & `funcCfgWf`/`progWf` (`assumeMultiFrameCaller`) -/

/-- Callee with two distinct `Assume` statements (`x > 0` and `x < 10`) whose
`StorageLive`/`StorageDead` scopes straddle both `Assume` basic-block splits,
splitting `bb0` into three MiniRust basic blocks before returning `x + 1`. -/
def assumeChainCallee : CapturedMir where
  defPath := "witness::assume_chain_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, boolDecl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.binaryOp .gt (.copy (local_ 1)) (constU32 0))),
        mkStmt (.intrinsic (.assume (.move (local_ 2)))),
        mkStmt (.storageDead 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.binaryOp .lt (.copy (local_ 1)) (constU32 10))),
        mkStmt (.intrinsic (.assume (.move (local_ 3)))),
        mkStmt (.storageDead 3),
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 1)) (constU32 1)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller exercising `Assume` before `TerminatorKind.call`, a multi-split
callee frame (`assumeChainCallee`), and `Assume` in the post-call continuation
block `bb1` before returning `(x + 1) * 2`. -/
def assumeMultiFrameCaller : CapturedMir where
  defPath := "witness::assume_multi_frame_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, boolDecl, boolDecl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.binaryOp .lt (.copy (local_ 1)) (constU32 100))),
        mkStmt (.intrinsic (.assume (.move (local_ 3)))),
        mkStmt (.storageDead 3),
        mkStmt (.storageLive 4)],
      terminator := mkTerm (.call (fnDefOp "witness::assume_chain_callee")
        [.copy (local_ 1)] (local_ 4) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.intrinsic (.assume (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.binaryOp .mul (.move (local_ 4)) (constU32 2))),
        mkStmt (.storageDead 4)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem assumeMultiFrame_inFragment :
    progInFragment assumeMultiFrameCaller [assumeChainCallee] = true := by decide

def assumeMultiFrameProg : Gen.Program :=
  (translateProg assumeMultiFrameCaller [assumeChainCallee]).getD emptyProg

def assumeMultiFrameFn : Gen.Function :=
  (translateFnInProg (fnNameMap assumeMultiFrameCaller [assumeChainCallee])
    assumeMultiFrameCaller).getD callerFn

def assumeChainCalleeFn : Gen.Function :=
  (translateFnInProg (fnNameMap assumeMultiFrameCaller [assumeChainCallee])
    assumeChainCallee).getD callerFn

theorem assumeMultiFrame_translate :
    translateProg assumeMultiFrameCaller [assumeChainCallee] = some assumeMultiFrameProg := rfl

theorem assumeMultiFrame_translateInProg :
    translateFnInProg (fnNameMap assumeMultiFrameCaller [assumeChainCallee])
      assumeMultiFrameCaller = some assumeMultiFrameFn := rfl

theorem assumeChainCallee_translateInProg :
    translateFnInProg (fnNameMap assumeMultiFrameCaller [assumeChainCallee])
      assumeChainCallee = some assumeChainCalleeFn := rfl

theorem assumeMultiFrame_prog_wf :
    progWf assumeMultiFrameProg = true :=
  translateProg_progWf assumeMultiFrame_inFragment assumeMultiFrame_translate

theorem assumeMultiFrame_func_wf_caller :
    funcCfgWf assumeMultiFrameFn = true :=
  translateFnInProg_funcCfgWf (callees := [assumeChainCallee])
    (by decide) assumeMultiFrame_translateInProg

theorem assumeMultiFrame_func_wf_callee :
    funcCfgWf assumeChainCalleeFn = true :=
  translateFnInProg_funcCfgWf (callees := [assumeChainCallee])
    (by decide) assumeChainCallee_translateInProg

theorem ctxAssumeMultiFrame_ok : CtxOk assumeMultiFrameCaller ctxCallerMain where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [assumeMultiFrameCaller] at hd; subst hd; decide
    | 1, _, hd => simp [assumeMultiFrameCaller] at hd; subst hd; decide
    | 2, _, hd => simp [assumeMultiFrameCaller] at hd; subst hd; decide
    | _ + 3, hi, _ => simp [assumeMultiFrameCaller] at hi
  ret := by
    intro d hd; simp [assumeMultiFrameCaller] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def assumeMultiFrameArgs (x : Nat) (postOk : Bool) : List Value :=
  [.scalar ⟨x, 4⟩, .scalar ⟨if postOk then 1 else 0, 1⟩]

def assumeMultiFrameMInit (x : Nat) (postOk : Bool) : Mach :=
  multiMachineWithCtx ctxCallerMain assumeMultiFrameProg 2 assumeMultiFrameCaller assumeMultiFrameFn
    (initMachineStateWithCallees assumeMultiFrameCaller (assumeMultiFrameArgs x postOk)
      [assumeChainCallee]).frame.locals
    assumeMultiFrameFn.start

/-- `(5, true)` passes pre-call `Assume(5 < 100)`, both split-block `Assume`s in
`assumeChainCallee` (`5 > 0`, `5 < 10`), and post-call `Assume(true)`, returning
`(5 + 1) * 2 = 12u32`. -/
theorem assumeMultiFrame5_anneal_ret :
    (∃ tr mem, ReachesRet
      (mirCallTreeWithCallees assumeMultiFrameCaller (assumeMultiFrameArgs 5 true)
        [assumeChainCallee]) tr (.normal (.scalar ⟨12, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees assumeMultiFrameCaller (assumeMultiFrameArgs 5 true)
        [assumeChainCallee]) :=
  runsToScalar_sound (fuel := 25) (by decide)

theorem assumeMultiFrame5_minirust_ret :
    ∃ (n : Nat) (m' : Mach), Interp.steps n (assumeMultiFrameMInit 5 true) = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 12 } ∧
      m'.threads = [thread1 ctxCallerMain
        [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨⟨tr, mem, hanneal⟩, _⟩ := assumeMultiFrame5_anneal_ret
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCallWithCallees_ret assumeMultiFrame_inFragment assumeMultiFrame_translate
      assumeMultiFrame_translateInProg ctxCallerMain ctxAssumeMultiFrame_ok
      (assumeMultiFrameArgs 5 true) (by decide) (assumeMultiFrameMInit 5 true)
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hanneal
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [assumeMultiFrameCaller] at hd; subst hd
  simp [retPtr, ctxCallerMain, ctxWithFns] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxCallerMain, ctxWithFns] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- `(100, true)` raises UB in the caller's pre-call `Assume(100 < 100)` before
entering `assumeChainCallee`. -/
theorem assumeMultiFramePreUb_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees assumeMultiFrameCaller (assumeMultiFrameArgs 100 true)
        [assumeChainCallee]) tr u ∧
      FaultNow u :=
  faultsA_sound assumeMultiFrameCaller 10 _ (by decide)

theorem assumeMultiFramePreUb_minirust_ub_rel :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n (assumeMultiFrameMInit 100 true) = .ok mLast ∧
      MultiStateRel assumeMultiFrameCaller [assumeChainCallee] assumeMultiFrameProg ctxCallerMain
        sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) (assumeMultiFrameMInit 100 true) = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k (assumeMultiFrameMInit 100 true) = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := assumeMultiFramePreUb_anneal_ub
  obtain ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩ :=
    mirCallWithCallees_ub_rel assumeMultiFrame_inFragment assumeMultiFrame_translate
      assumeMultiFrame_translateInProg ctxCallerMain ctxAssumeMultiFrame_ok
      (assumeMultiFrameArgs 100 true) (by decide) (assumeMultiFrameMInit 100 true)
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf
  exact ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩

/-- `(10, true)` passes the caller's pre-call `Assume` and the callee's first
`Assume(10 > 0)`, then raises UB at the callee's second `Assume(10 < 10)` in the
split continuation block while the caller's frame is suspended on the stack. -/
theorem assumeMultiFrameCalleeSeg2Ub_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees assumeMultiFrameCaller (assumeMultiFrameArgs 10 true)
        [assumeChainCallee]) tr u ∧
      FaultNow u :=
  faultsA_sound assumeMultiFrameCaller 20 _ (by decide)

theorem assumeMultiFrameCalleeSeg2Ub_minirust_ub_rel :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n (assumeMultiFrameMInit 10 true) = .ok mLast ∧
      MultiStateRel assumeMultiFrameCaller [assumeChainCallee] assumeMultiFrameProg ctxCallerMain
        sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) (assumeMultiFrameMInit 10 true) = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k (assumeMultiFrameMInit 10 true) = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := assumeMultiFrameCalleeSeg2Ub_anneal_ub
  obtain ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩ :=
    mirCallWithCallees_ub_rel assumeMultiFrame_inFragment assumeMultiFrame_translate
      assumeMultiFrame_translateInProg ctxCallerMain ctxAssumeMultiFrame_ok
      (assumeMultiFrameArgs 10 true) (by decide) (assumeMultiFrameMInit 10 true)
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf
  exact ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩

/-- `(5, false)` completes `assumeChainCallee(5) == 6` across all three callee
segments and raises UB at the caller's post-call `Assume(false)` in `bb1`. -/
theorem assumeMultiFramePostUb_anneal_ub :
    ∃ tr u, Reaches
      (mirCallTreeWithCallees assumeMultiFrameCaller (assumeMultiFrameArgs 5 false)
        [assumeChainCallee]) tr u ∧
      FaultNow u :=
  faultsA_sound assumeMultiFrameCaller 25 _ (by decide)

theorem assumeMultiFramePostUb_minirust_ub_rel :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n (assumeMultiFrameMInit 5 false) = .ok mLast ∧
      MultiStateRel assumeMultiFrameCaller [assumeChainCallee] assumeMultiFrameProg ctxCallerMain
        sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) (assumeMultiFrameMInit 5 false) = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k (assumeMultiFrameMInit 5 false) = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := assumeMultiFramePostUb_anneal_ub
  obtain ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩ :=
    mirCallWithCallees_ub_rel assumeMultiFrame_inFragment assumeMultiFrame_translate
      assumeMultiFrame_translateInProg ctxCallerMain ctxAssumeMultiFrame_ok
      (assumeMultiFrameArgs 5 false) (by decide) (assumeMultiFrameMInit 5 false)
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf
  exact ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩

/-- Necessity witness for `livenessOk` on `StatementKind.intrinsic (.assume op)`:
reading a local after `StorageDead(_2)` raises UB in both Anneal (`evalOperand`
sees `.dead`) and MiniRust (`evalPlace` dereferences a deallocated local). Note
that `livenessOk` permits reading a `StorageDead` local so long as its allocation
is still dead on all incoming paths, and both semantics step in lockstep to UB. -/
def assumeDeadLocal : CapturedMir where
  defPath := "witness::assume_dead_local"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageDead 2),
        mkStmt (.intrinsic (.assume (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

theorem assumeDeadLocal_inFragment : progInFragment assumeDeadLocal [] = true := by decide

def assumeDeadLocalProg : Gen.Program := (translateProg assumeDeadLocal []).getD emptyProg

def assumeDeadLocalFn : Gen.Function :=
  (translateFnInProg (fnNameMap assumeDeadLocal []) assumeDeadLocal).getD callerFn

theorem assumeDeadLocal_translate : translateProg assumeDeadLocal [] = some assumeDeadLocalProg := rfl

theorem assumeDeadLocal_translateInProg :
    translateFnInProg (fnNameMap assumeDeadLocal []) assumeDeadLocal = some assumeDeadLocalFn := rfl

theorem ctxAssumeDeadLocal_ok : CtxOk assumeDeadLocal ctxCallSpin where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [assumeDeadLocal] at hd; subst hd; decide
    | 1, _, hd => simp [assumeDeadLocal] at hd; subst hd; decide
    | _ + 2, hi, _ => simp [assumeDeadLocal] at hi
  ret := by
    intro d hd; simp [assumeDeadLocal] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def assumeDeadLocalMInit : Mach :=
  multiMachineWithCtx ctxCallSpin assumeDeadLocalProg 1 assumeDeadLocal assumeDeadLocalFn
    (initMachineStateWithCallees assumeDeadLocal [.scalar ⟨7, 4⟩] []).frame.locals
    assumeDeadLocalFn.start

theorem assumeDeadLocal_anneal_ub :
    ∃ tr u, Reaches (mirCallTreeWithCallees assumeDeadLocal [.scalar ⟨7, 4⟩] []) tr u ∧
      FaultNow u :=
  faultsA_sound assumeDeadLocal 6 _ (by decide)

theorem assumeDeadLocal_minirust_ub_rel :
    ∃ (n : Nat) (sLast : MachineState) (mLast : Mach) (msg : String),
      Interp.steps n assumeDeadLocalMInit = .ok mLast ∧
      MultiStateRel assumeDeadLocal [] assumeDeadLocalProg ctxCallSpin sLast mLast ∧
      Interp.step mLast = .error (.ub msg) ∧
      Interp.steps (n + 1) assumeDeadLocalMInit = .error (.ub msg) ∧
      (∀ k ≤ n, ∀ mk, Interp.steps k assumeDeadLocalMInit = .ok mk →
        ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mk) := by
  obtain ⟨tr, u, hr, hf⟩ := assumeDeadLocal_anneal_ub
  obtain ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩ :=
    mirCallWithCallees_ub_rel assumeDeadLocal_inFragment assumeDeadLocal_translate
      assumeDeadLocal_translateInProg ctxCallSpin ctxAssumeDeadLocal_ok
      [.scalar ⟨7, 4⟩] (by decide) assumeDeadLocalMInit
      (progEnvOk_fnPtrMap rfl rfl (by decide)) rfl rfl rfl hr hf
  exact ⟨n, sLast, mLast, msg, hsteps, hrel, hstep, hsteps1, hno⟩

/-- Necessity of `stmtMoved` on `Assume` (`Assume(move _2); _0 = copy _1; _3 = copy _2`):
Anneal's `evalOperand` moves out of `_2` on `Assume(move _2)`, so reading `_2`
afterwards faults with UB, whereas MiniRust's `ValueExpr::Load` in
`Terminator::Intrinsic` leaves `_2`'s bytes initialized and returns `7u32`.
`movesOk` (and `progInFragment`) must therefore record `moveOut mo op` on
`StatementKind.intrinsic (.assume op)`. -/
def assumeMoveReuse : CapturedMir where
  defPath := "witness::assume_move_reuse"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, boolDecl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.intrinsic (.assume (.move (local_ 2)))),
        mkStmt (.assign (local_ 3) (.use (.copy (local_ 2)))),
        mkStmt (.storageDead 3),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem assumeMoveReuse_rejected :
    movesOk assumeMoveReuse = false ∧ progInFragment assumeMoveReuse [] = false :=
  ⟨by decide, by decide⟩

def assumeMoveReuseProg : Gen.Program := (translateProg assumeMoveReuse []).getD emptyProg

def assumeMoveReuseFn : Gen.Function :=
  (translateFnInProg (fnNameMap assumeMoveReuse []) assumeMoveReuse).getD callerFn

def assumeMoveReuseMInit : Mach :=
  multiMachineWithCtx ctxAssumeSub assumeMoveReuseProg 1 assumeMoveReuse assumeMoveReuseFn
    (initMachineStateWithCallees assumeMoveReuse (assumeSubArgs 7 true) []).frame.locals
    assumeMoveReuseFn.start

theorem assumeMoveReuse_diverges :
    (∃ tr u, Reaches (mirCallTreeWithCallees assumeMoveReuse (assumeSubArgs 7 true) []) tr u ∧
      FaultNow u) ∧
    (Interp.steps 7 assumeMoveReuseMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 7 }, [1]) :=
  ⟨faultsA_sound assumeMoveReuse 6 _ (by decide), by decide +kernel⟩

/-- Necessity of `stmtReadsOk` on `Assume` (`_3 = move _2; Assume(copy _2)`):
moving `_2` in a prior statement leaves stale `true` bytes in MiniRust's local
allocation, so MiniRust passes `Terminator::Intrinsic(.Assume)` and returns
`7u32` while Anneal faults with UB on `Assume(copy _2)`. `movesOk` (and
`progInFragment`) must therefore check `!mo.contains b` on `Assume`'s operand. -/
def assumeAfterMove : CapturedMir where
  defPath := "witness::assume_after_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, boolDecl, boolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.use (.move (local_ 2)))),
        mkStmt (.intrinsic (.assume (.copy (local_ 2)))),
        mkStmt (.storageDead 3),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem assumeAfterMove_rejected :
    movesOk assumeAfterMove = false ∧ progInFragment assumeAfterMove [] = false :=
  ⟨by decide, by decide⟩

def assumeAfterMoveProg : Gen.Program := (translateProg assumeAfterMove []).getD emptyProg

def assumeAfterMoveFn : Gen.Function :=
  (translateFnInProg (fnNameMap assumeAfterMove []) assumeAfterMove).getD callerFn

def assumeAfterMoveMInit : Mach :=
  multiMachineWithCtx ctxAssumeSub assumeAfterMoveProg 1 assumeAfterMove assumeAfterMoveFn
    (initMachineStateWithCallees assumeAfterMove (assumeSubArgs 7 true) []).frame.locals
    assumeAfterMoveFn.start

theorem assumeAfterMove_diverges :
    (∃ tr u, Reaches (mirCallTreeWithCallees assumeAfterMove (assumeSubArgs 7 true) []) tr u ∧
      FaultNow u) ∧
    (Interp.steps 7 assumeAfterMoveMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 7 }, [1]) :=
  ⟨faultsA_sound assumeAfterMove 6 _ (by decide), by decide +kernel⟩

/-! ## Homogeneous arrays (`Type::Array`), `Repeat`, `Len`, and `Index`/`ConstantIndex` projections -/

def usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
def usizeDecl : LocalDecl := { mutability := .mut, ty := usizeTy, debugName := none }
def constUsize (n : Nat) : Operand := .constant { ty := usizeTy, val := .scalar (.int ⟨n, 8⟩) }

def arrI8_3Ty : Ty := { kind := .array (.int .i8) 3, layoutIdx := 0 }
def arrI8_3Decl : LocalDecl := { mutability := .mut, ty := arrI8_3Ty, debugName := none }

def arrI8_2Ty : Ty := { kind := .array (.int .i8) 2, layoutIdx := 0 }
def arrI8_2Decl : LocalDecl := { mutability := .mut, ty := arrI8_2Ty, debugName := none }

def arrI8_0Ty : Ty := { kind := .array (.int .i8) 0, layoutIdx := 0 }
def arrI8_0Decl : LocalDecl := { mutability := .mut, ty := arrI8_0Ty, debugName := none }

def usizeLayout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def arrI8_3Layout : TypeLayout :=
  { size := { bytes := 3 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def arrI8_2Layout : TypeLayout :=
  { size := { bytes := 2 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def arrI8_0Layout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiArrayOps : FnAbi :=
  { args := [{ layout := arrI8_3Layout, mode := .direct },
             { layout := arrI8_3Layout, mode := .direct },
             { layout := i8Layout, mode := .direct },
             { layout := usizeLayout, mode := .direct },
             { layout := usizeLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

def ctxI8_6 : Ctx :=
  { caller := callerFrameI8, payloads := [], base := [retAllocI8],
    addrs := [128, 256, 384, 512, 640, 768],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxI8_ok_arrayOps {body : CapturedMir}
    (h : body.localDecls = [i8Decl, arrI8_3Decl, arrI8_3Decl, i8Decl, usizeDecl, usizeDecl]) :
    CtxOk body ctxI8_6 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [arrI8_3Decl, arrI8_3Ty, itOf_array_int, tyOf_array_int]; decide
    | 2, hd => simp at hd; subst hd; rw [arrI8_3Decl, arrI8_3Ty, itOf_array_int, tyOf_array_int]; decide
    | 3, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 4, hd => simp at hd; subst hd; rw [usizeDecl, usizeTy, itOf_uint, tyOf_uint]; decide
    | 5, hd => simp at hd; subst hd; rw [usizeDecl, usizeTy, itOf_uint, tyOf_uint]; decide
    | _ + 6, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

def placeIdx (i idxLocal : Nat) : Place :=
  { local_ := i, projection := [.index idxLocal] }

def placeConstIdx (i offset minLen : Nat) (fromEnd : Bool) : Place :=
  { local_ := i, projection := [.constantIndex offset minLen fromEnd] }

/-- MIR (`Runtime(PostCleanup)`) of a function exercising homogeneous `[i8; 3]`
arrays across all six `MR-2.1` constructs:
1. `_1 = [copy _3, 10i8, 20i8]` (`Rvalue.aggregate (.array i8Ty)`),
2. `_2 = [5i8; 3]` (`Rvalue.repeat`),
3. `_2 = copy _1` (whole-array `Rvalue.use (.copy _1)`),
4. `_2[_4] = Add(copy _2[_4], 7i8)` (`ProjectionElem.index` read and in-place write),
5. `_2[-1 of 3] = Sub(copy _2[-1 of 3], copy _2[0 of 3])`
   (`ProjectionElem.constantIndex` with `fromEnd = true` and `fromEnd = false`,
   both read and in-place write),
6. `_5 = Len(_2)` (`Rvalue.len`), cast to `i8`, and summed with all three
   elements `_2[_4]`, `_2[-1 of 3]`, and `_2[0 of 3]` to verify that in-place
   indexed writes preserve sibling elements. -/
def arrayOpsI8 : CapturedMir where
  defPath := "witness::array_ops_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 5
  localDecls := [i8Decl, arrI8_3Decl, arrI8_3Decl, i8Decl, usizeDecl, usizeDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1)
          (.aggregate (.array i8Ty) [.copy (local_ 3), constI8 10, constI8 20])),
        mkStmt (.assign (local_ 2) (.repeat (constI8 5) 3)),
        mkStmt (.assign (local_ 2) (.use (.copy (local_ 1)))),
        mkStmt (.assign (placeIdx 2 4)
          (.binaryOp .add (.copy (placeIdx 2 4)) (constI8 7))),
        mkStmt (.assign (placeConstIdx 2 1 3 true)
          (.binaryOp .sub (.copy (placeConstIdx 2 1 3 true)) (.copy (placeConstIdx 2 0 3 false)))),
        mkStmt (.assign (local_ 5) (.len (local_ 2))),
        mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 5)) i8Ty)),
        mkStmt (.assign (local_ 0)
          (.binaryOp .add (.copy (local_ 0)) (.copy (placeIdx 2 4)))),
        mkStmt (.assign (local_ 0)
          (.binaryOp .add (.copy (local_ 0)) (.copy (placeConstIdx 2 1 3 true)))),
        mkStmt (.assign (local_ 0)
          (.binaryOp .add (.copy (local_ 0)) (.copy (placeConstIdx 2 0 3 false))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArrayOps
  layouts := emptyLayoutTable
  allocations := []

theorem arrayOpsI8_inFragment : inFragment arrayOpsI8 = true := by decide

def arrayOpsI8Fn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int i8),
    (localName 1, .Array (.Int i8) 3),
    (localName 2, .Array (.Int i8) 3),
    (localName 3, .Int i8),
    (localName 4, .Int usizeIt),
    (localName 5, .Int usizeIt)]⟩
  args := [localName 1, localName 2, localName 3, localName 4, localName 5]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Local (localName 3)),
          .Constant (.Int 10) (.Int i8),
          .Constant (.Int 20) (.Int i8)] (.Array (.Int i8) 3)),
      .Assign (.Local (localName 2))
        (.Tuple [
          .Constant (.Int 5) (.Int i8),
          .Constant (.Int 5) (.Int i8),
          .Constant (.Int 5) (.Int i8)] (.Array (.Int i8) 3)),
      .Assign (.Local (localName 2)) (.Load (.Local (localName 1))),
      .Assign (.Index (.Local (localName 2)) (.Load (.Local (localName 4))))
        (.BinOp (.Int .Add)
          (.Load (.Index (.Local (localName 2)) (.Load (.Local (localName 4)))))
          (.Constant (.Int 7) (.Int i8))),
      .Assign (.Index (.Local (localName 2)) (.Constant (.Int 2) (.Int usizeIt)))
        (.BinOp (.Int .Sub)
          (.Load (.Index (.Local (localName 2)) (.Constant (.Int 2) (.Int usizeIt))))
          (.Load (.Index (.Local (localName 2)) (.Constant (.Int 0) (.Int usizeIt))))),
      .Assign (.Local (localName 5)) (.Constant (.Int 3) (.Int usizeIt)),
      .Assign (.Local (localName 0)) (.UnOp (.Cast (.IntToInt i8)) (.Load (.Local (localName 5)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add)
          (.Load (.Local (localName 0)))
          (.Load (.Index (.Local (localName 2)) (.Load (.Local (localName 4)))))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add)
          (.Load (.Local (localName 0)))
          (.Load (.Index (.Local (localName 2)) (.Constant (.Int 2) (.Int usizeIt))))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add)
          (.Load (.Local (localName 0)))
          (.Load (.Index (.Local (localName 2)) (.Constant (.Int 0) (.Int usizeIt)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arrayOpsI8_translate : translateFn arrayOpsI8 = some arrayOpsI8Fn := rfl

def initArrI8_3 : Value := .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩]

def arrayOpsOkArgs : List Value :=
  [initArrI8_3, initArrI8_3, .scalar ⟨3, 1⟩, .scalar ⟨1, 8⟩, .scalar ⟨0, 8⟩]

/-- Input `_3 = 3i8`, `_4 = 1usize`:
* `_1 = [3, 10, 20]`, `_2 = [5, 5, 5]`, then `_2 = copy _1 = [3, 10, 20]`;
* `_2[1] = _2[1] + 7 = 17`, so `_2 = [3, 17, 20]`;
* `_2[2] = _2[2] - _2[0] = 20 - 3 = 17`, so `_2 = [3, 17, 17]`;
* `_5 = Len(_2) = 3usize`, and `_0 = 3 + 17 + 17 + 3 = 40i8`. -/
def arrayOpsOkS0 : MachineState := initMachineState arrayOpsI8 arrayOpsOkArgs
def arrayOpsOkMInit : Mach :=
  machineWithCtx ctxI8_6 arrayOpsI8 arrayOpsI8Fn arrayOpsOkS0.frame.locals arrayOpsI8Fn.start

theorem arrayOpsOk_anneal_ret :
    ReachesRet (mirCallTree arrayOpsI8 arrayOpsOkArgs) []
      (.normal (.scalar ⟨40, 1⟩, arrayOpsOkS0.memory)) :=
  runA_sound arrayOpsI8 16 _ _ _ rfl

theorem arrayOpsOk_noUB :
    MirNoUBTree (mirCallTree arrayOpsI8 arrayOpsOkArgs) :=
  runA_noUB arrayOpsI8 16 _ _ _ rfl

theorem arrayOpsOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n arrayOpsOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 40 } ∧
      m'.threads = [thread1 ctxI8_6 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret arrayOpsI8_inFragment arrayOpsI8_translate ctxI8_6
      (ctxI8_ok_arrayOps rfl) arrayOpsOkArgs (by decide)
      arrayOpsOkMInit rfl rfl rfl arrayOpsOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [arrayOpsI8] at hd; subst hd
  simp [retPtr, ctxI8_6] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_6] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem arrayOpsOk_minirust_direct :
    (Interp.steps 12 arrayOpsOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 40 }, [1]) := rfl

/-- Byte-level view of the in-place element writes of `arrayOpsI8` on the
input of `arrayOpsOkArgs`. MiniRust's allocation `3` is `_2`'s (after the
caller's return allocation and those of `_0` and `_1`). After step `4`
(`_2 = copy _1`) it holds the bytes of `[3, 10, 20]`; step `5`
(`_2[_4] = _2[_4] + 7`) rewrites only the byte at offset `1`, giving
`[3, 17, 20]`; step `6` (`_2[-1 of 3] = _2[-1 of 3] - _2[0 of 3]`) rewrites
only the byte at offset `2`, giving `[3, 17, 17]`. Each store leaves the
sibling bytes before and after the written element unchanged. -/
theorem arrayOpsOk_minirust_inplace_bytes :
    [4, 5, 6].map (fun k => (Interp.steps k arrayOpsOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[3]?).map (·.data))) =
      [some (some (scalarBytes i8 3 ++ scalarBytes i8 10 ++ scalarBytes i8 20)),
       some (some (scalarBytes i8 3 ++ scalarBytes i8 17 ++ scalarBytes i8 20)),
       some (some (scalarBytes i8 3 ++ scalarBytes i8 17 ++ scalarBytes i8 17))] := rfl

/-- On `Terminator::Return` at step `12` of `arrayOpsI8`, `evalReturn` calls
`storageDead` on every callee local (`_0`..`_5`, allocations `1..=6`), verifying
`BM.deallocate` against each local's layout (`size = 3, align = 1` for the two
`[i8; 3]` array locals `_1` and `_2` at allocations `2` and `3`) and marking all
six callee stack allocations `live = false` while keeping the caller's return
allocation `0` `live = true`. -/
theorem arrayOpsOk_minirust_ret_dealloc :
    (Interp.steps 12 arrayOpsOkMInit).toOption.map
        (fun m => m.mem.memory.allocations.map (fun a => (a.live, a.data.length))) =
      some [(true, 1), (false, 1), (false, 3), (false, 3), (false, 1), (false, 8), (false, 8)] := rfl

/-- Out-of-bounds `Index` (`_4 = 3usize >= 3`) on `arrayOpsI8`: raises UB on
`_2[_4]`. -/
def arrayOpsOobArgs : List Value :=
  [initArrI8_3, initArrI8_3, .scalar ⟨3, 1⟩, .scalar ⟨3, 8⟩, .scalar ⟨0, 8⟩]

def arrayOpsOobS0 : MachineState := initMachineState arrayOpsI8 arrayOpsOobArgs
def arrayOpsOobMInit : Mach :=
  machineWithCtx ctxI8_6 arrayOpsI8 arrayOpsI8Fn arrayOpsOobS0.frame.locals arrayOpsI8Fn.start

theorem arrayOpsOob_anneal_ub :
    ∃ tr u, Reaches (mirCallTree arrayOpsI8 arrayOpsOobArgs) tr u ∧ FaultNow u :=
  faultsA_sound arrayOpsI8 8 _ (by decide)

theorem arrayOpsOob_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayOpsOobMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayOpsOob_anneal_ub
  exact mirCall_ub arrayOpsI8_inFragment arrayOpsI8_translate ctxI8_6
    (ctxI8_ok_arrayOps rfl) arrayOpsOobArgs (by decide)
    arrayOpsOobMInit rfl rfl rfl hr hf

theorem arrayOpsOob_minirust_direct :
    Interp.steps 5 arrayOpsOobMInit = .error (.ub "access to out-of-bounds index") := rfl

theorem arrayOpsOob_converse_error :
    (∃ msg, Stop.ub "access to out-of-bounds index" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree arrayOpsI8 arrayOpsOobArgs) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 5 ∧ Interp.steps k arrayOpsOobMInit = .ok mRet ∧
      ReturnRel arrayOpsI8 ctxI8_6 s' v mRet ∧
      ReachesRet (mirCallTree arrayOpsI8 arrayOpsOobArgs) tr (.normal (v, mem))) :=
  mirCall_steps_error arrayOpsI8_inFragment arrayOpsI8_translate ctxI8_6
    (ctxI8_ok_arrayOps rfl) arrayOpsOobArgs (by decide)
    arrayOpsOobMInit rfl rfl rfl arrayOpsOob_minirust_direct

/-! ## Signed index local (`i8`), negative index UB (`idx < 0`), and in-place write UB -/

def fnAbiArraySignedIdx : FnAbi :=
  { args := [{ layout := arrI8_2Layout, mode := .direct },
             { layout := i8Layout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_arraySignedIdx {body : CapturedMir}
    (h : body.localDecls = [i8Decl, arrI8_2Decl, i8Decl]) : CtxOk body ctxI8_3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [arrI8_2Decl, arrI8_2Ty, itOf_array_int, tyOf_array_int]; decide
    | 2, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of a function that indexes `[i8; 2]` with a
signed `i8` index local `_2` in both an in-place write `_1[_2] = const 99i8`
and a read `_0 = copy _1[_2]`. -/
def arraySignedIdxI8 : CapturedMir where
  defPath := "witness::array_signed_idx_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, arrI8_2Decl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (placeIdx 1 2) (.use (constI8 99))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeIdx 1 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArraySignedIdx
  layouts := emptyLayoutTable
  allocations := []

theorem arraySignedIdxI8_inFragment : inFragment arraySignedIdxI8 = true := by decide

def arraySignedIdxI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Array (.Int i8) 2), (localName 2, .Int i8)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Index (.Local (localName 1)) (.Load (.Local (localName 2))))
        (.Constant (.Int 99) (.Int i8)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arraySignedIdxI8_translate : translateFn arraySignedIdxI8 = some arraySignedIdxI8Fn := rfl

def initArrI8_2 : Value := .aggregate 0 [.scalar ⟨11, 1⟩, .scalar ⟨22, 1⟩]

/-- Signed index `_2 = 1i8`: writes `_1[1] = 99i8` and returns `99i8`. -/
def arraySignedIdxOkS0 : MachineState :=
  initMachineState arraySignedIdxI8 [initArrI8_2, .scalar ⟨1, 1⟩]
def arraySignedIdxOkMInit : Mach :=
  machineWithCtx ctxI8_3 arraySignedIdxI8 arraySignedIdxI8Fn
    arraySignedIdxOkS0.frame.locals arraySignedIdxI8Fn.start

theorem arraySignedIdxOk_anneal_ret :
    ReachesRet (mirCallTree arraySignedIdxI8 [initArrI8_2, .scalar ⟨1, 1⟩]) []
      (.normal (.scalar ⟨99, 1⟩, arraySignedIdxOkS0.memory)) :=
  runA_sound arraySignedIdxI8 8 _ _ _ rfl

theorem arraySignedIdxOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n arraySignedIdxOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 99 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret arraySignedIdxI8_inFragment arraySignedIdxI8_translate ctxI8_3
      (ctxI8_ok_arraySignedIdx rfl) [initArrI8_2, .scalar ⟨1, 1⟩] (by decide)
      arraySignedIdxOkMInit rfl rfl rfl arraySignedIdxOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [arraySignedIdxI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem arraySignedIdxOk_minirust_direct :
    (Interp.steps 4 arraySignedIdxOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 99 }, [1]) := rfl

/-- Negative signed index `_2 = -1i8` (bits `255` in `i8`): raises UB on the
in-place element write `_1[_2] = 99i8`. -/
def arraySignedNegUbS0 : MachineState :=
  initMachineState arraySignedIdxI8 [initArrI8_2, .scalar ⟨255, 1⟩]
def arraySignedNegUbMInit : Mach :=
  machineWithCtx ctxI8_3 arraySignedIdxI8 arraySignedIdxI8Fn
    arraySignedNegUbS0.frame.locals arraySignedIdxI8Fn.start

theorem arraySignedNegUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arraySignedIdxI8 [initArrI8_2, .scalar ⟨255, 1⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arraySignedIdxI8 6 _ (by decide)

theorem arraySignedNegUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arraySignedNegUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arraySignedNegUb_anneal_ub
  exact mirCall_ub arraySignedIdxI8_inFragment arraySignedIdxI8_translate ctxI8_3
    (ctxI8_ok_arraySignedIdx rfl) [initArrI8_2, .scalar ⟨255, 1⟩] (by decide)
    arraySignedNegUbMInit rfl rfl rfl hr hf

theorem arraySignedNegUb_minirust_direct :
    Interp.steps 2 arraySignedNegUbMInit = .error (.ub "access to out-of-bounds index") := rfl

/-- Out-of-bounds positive signed index `_2 = 2i8` (`2 >= 2`): raises UB on the
in-place element write `_1[_2] = 99i8`. -/
def arraySignedOobUbS0 : MachineState :=
  initMachineState arraySignedIdxI8 [initArrI8_2, .scalar ⟨2, 1⟩]
def arraySignedOobUbMInit : Mach :=
  machineWithCtx ctxI8_3 arraySignedIdxI8 arraySignedIdxI8Fn
    arraySignedOobUbS0.frame.locals arraySignedIdxI8Fn.start

theorem arraySignedOobUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arraySignedIdxI8 [initArrI8_2, .scalar ⟨2, 1⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arraySignedIdxI8 6 _ (by decide)

theorem arraySignedOobUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arraySignedOobUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arraySignedOobUb_anneal_ub
  exact mirCall_ub arraySignedIdxI8_inFragment arraySignedIdxI8_translate ctxI8_3
    (ctxI8_ok_arraySignedIdx rfl) [initArrI8_2, .scalar ⟨2, 1⟩] (by decide)
    arraySignedOobUbMInit rfl rfl rfl hr hf

theorem arraySignedOobUb_minirust_direct :
    Interp.steps 2 arraySignedOobUbMInit = .error (.ub "access to out-of-bounds index") := rfl

/-! ## Zero-length array `[i8; 0]` construction, `Len`, and out-of-bounds indexing at `0` -/

def fnAbiZeroArray : FnAbi :=
  { args := [{ layout := arrI8_0Layout, mode := .direct },
             { layout := usizeLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_zeroArray {body : CapturedMir}
    (h : body.localDecls = [i8Decl, arrI8_0Decl, usizeDecl]) : CtxOk body ctxI8_3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [arrI8_0Decl, arrI8_0Ty, itOf_array_int, tyOf_array_int]; decide
    | 2, hd => simp at hd; subst hd; rw [usizeDecl, usizeTy, itOf_uint, tyOf_uint]; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of a function exercising a zero-length array
`[i8; 0]` (`_1`):
* in `bb0`, constructs `_1 = []` via `Rvalue.aggregate (.array i8Ty) []` and
  copies `_1 = copy _1` via `Rvalue.use (.copy _1)`, then switches on `_2`;
* when `_2 == 0` (`bb1`), constructs `_1 = [5i8; 0]` via
  `Rvalue.repeat (constI8 5) 0`, computes `_2 = Len(_1)` (`= 0usize`), casts to
  `0i8`, and returns;
* when `_2 != 0` (`bb2`), sets `_2 = 0usize` and attempts to read `_1[_2]` at
  index `0`, raising out-of-bounds UB (`0 >= 0`). -/
def zeroArrayI8 : CapturedMir where
  defPath := "witness::zero_array_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, arrI8_0Decl, usizeDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.array i8Ty) [])),
        mkStmt (.assign (local_ 1) (.use (.copy (local_ 1))))],
      terminator := mkTerm (.switchInt (.copy (local_ 2))
        { branches := [(0, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.repeat (constI8 5) 0)),
        mkStmt (.assign (local_ 2) (.len (local_ 1))),
        mkStmt (.assign (local_ 0) (.cast .intToInt (.copy (local_ 2)) i8Ty))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2) (.use (constUsize 0))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeIdx 1 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiZeroArray
  layouts := emptyLayoutTable
  allocations := []

theorem zeroArrayI8_inFragment : inFragment zeroArrayI8 = true := by decide

def zeroArrayI8Fn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int i8),
    (localName 1, .Array (.Int i8) 0),
    (localName 2, .Int usizeIt)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 1)) (.Tuple [] (.Array (.Int i8) 0)),
      .Assign (.Local (localName 1)) (.Load (.Local (localName 1)))],
      .Switch (.Load (.Local (localName 2))) ⟨[(0, bbName 1)]⟩ (bbName 2), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 1)) (.Tuple [] (.Array (.Int i8) 0)),
      .Assign (.Local (localName 2)) (.Constant (.Int 0) (.Int usizeIt)),
      .Assign (.Local (localName 0)) (.UnOp (.Cast (.IntToInt i8)) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 2)) (.Constant (.Int 0) (.Int usizeIt)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2)))))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 3
  implicit_writes := true

theorem zeroArrayI8_translate : translateFn zeroArrayI8 = some zeroArrayI8Fn := rfl

def initArrI8_0 : Value := .aggregate 0 []

/-- `_2 = 0usize`: constructs `[i8; 0]`, repeats `[5i8; 0]`, reads `Len(_1) = 0`,
and returns `0i8`. -/
def zeroArrayOkS0 : MachineState :=
  initMachineState zeroArrayI8 [initArrI8_0, .scalar ⟨0, 8⟩]
def zeroArrayOkMInit : Mach :=
  machineWithCtx ctxI8_3 zeroArrayI8 zeroArrayI8Fn
    zeroArrayOkS0.frame.locals zeroArrayI8Fn.start

def zeroArrayOkTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]

theorem zeroArrayOk_anneal_ret :
    ReachesRet (mirCallTree zeroArrayI8 [initArrI8_0, .scalar ⟨0, 8⟩])
      zeroArrayOkTrace (.normal (.scalar ⟨0, 1⟩, zeroArrayOkS0.memory)) :=
  runA_sound zeroArrayI8 12 _ _ _ rfl

theorem zeroArrayOk_noUB :
    MirNoUBTree (mirCallTree zeroArrayI8 [initArrI8_0, .scalar ⟨0, 8⟩]) :=
  runA_noUB zeroArrayI8 12 _ _ _ rfl

theorem zeroArrayOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n zeroArrayOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 0 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret zeroArrayI8_inFragment zeroArrayI8_translate ctxI8_3
      (ctxI8_ok_zeroArray rfl) [initArrI8_0, .scalar ⟨0, 8⟩] (by decide)
      zeroArrayOkMInit rfl rfl rfl zeroArrayOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [zeroArrayI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem zeroArrayOk_minirust_direct :
    (Interp.steps 8 zeroArrayOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 0 }, [1]) := rfl

/-- `_2 = 1usize`: takes `bb2` and indexes `[i8; 0]` at `0usize`, raising
out-of-bounds UB (`0 >= 0`). -/
def zeroArrayIdxUbS0 : MachineState :=
  initMachineState zeroArrayI8 [initArrI8_0, .scalar ⟨1, 8⟩]
def zeroArrayIdxUbMInit : Mach :=
  machineWithCtx ctxI8_3 zeroArrayI8 zeroArrayI8Fn
    zeroArrayIdxUbS0.frame.locals zeroArrayI8Fn.start

theorem zeroArrayIdxUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree zeroArrayI8 [initArrI8_0, .scalar ⟨1, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound zeroArrayI8 10 _ (by decide)

theorem zeroArrayIdxUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n zeroArrayIdxUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := zeroArrayIdxUb_anneal_ub
  exact mirCall_ub zeroArrayI8_inFragment zeroArrayI8_translate ctxI8_3
    (ctxI8_ok_zeroArray rfl) [initArrI8_0, .scalar ⟨1, 8⟩] (by decide)
    zeroArrayIdxUbMInit rfl rfl rfl hr hf

theorem zeroArrayIdxUb_minirust_direct :
    Interp.steps 6 zeroArrayIdxUbMInit = .error (.ub "access to out-of-bounds index") := rfl

/-! ## Uninitialized index local (`_1[_0]` while `_0` is still `.uninit`) -/

def fnAbiArrayUninitIdx : FnAbi :=
  { args := [{ layout := arrI8_2Layout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_arrayUninitIdx {body : CapturedMir}
    (h : body.localDecls = [i8Decl, arrI8_2Decl]) : CtxOk body ctxI8 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [arrI8_2Decl, arrI8_2Ty, itOf_array_int, tyOf_array_int]; decide
    | _ + 2, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of a function that indexes `[i8; 2]` with the
return place `_0` as the index local before `_0` is ever written: first in the
in-place element write `_1[_0] = const 7_i8`, then in the read
`_0 = copy _1[_0]`. MiniRust evaluates the destination place first, so the
`Load` of the index operand `_0` fails the validity invariant before the
bounds check or the store happen; Anneal's projection finds `_0` `.uninit`
and faults. -/
def arrayUninitIdxI8 : CapturedMir where
  defPath := "witness::array_uninit_idx_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, arrI8_2Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (placeIdx 1 0) (.use (constI8 7))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeIdx 1 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArrayUninitIdx
  layouts := emptyLayoutTable
  allocations := []

theorem arrayUninitIdxI8_inFragment : inFragment arrayUninitIdxI8 = true := by decide

def arrayUninitIdxI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Array (.Int i8) 2)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Index (.Local (localName 1)) (.Load (.Local (localName 0))))
        (.Constant (.Int 7) (.Int i8)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Local (localName 1)) (.Load (.Local (localName 0)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arrayUninitIdxI8_translate :
    translateFn arrayUninitIdxI8 = some arrayUninitIdxI8Fn := rfl

def arrayUninitIdxS0 : MachineState := initMachineState arrayUninitIdxI8 [initArrI8_2]
def arrayUninitIdxMInit : Mach :=
  machineWithCtx ctxI8 arrayUninitIdxI8 arrayUninitIdxI8Fn
    arrayUninitIdxS0.frame.locals arrayUninitIdxI8Fn.start

theorem arrayUninitIdx_anneal_ub :
    ∃ tr u, Reaches (mirCallTree arrayUninitIdxI8 [initArrI8_2]) tr u ∧ FaultNow u :=
  faultsA_sound arrayUninitIdxI8 6 _ (by decide)

theorem arrayUninitIdx_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayUninitIdxMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayUninitIdx_anneal_ub
  exact mirCall_ub arrayUninitIdxI8_inFragment arrayUninitIdxI8_translate ctxI8
    (ctxI8_ok_arrayUninitIdx rfl) [initArrI8_2] (by decide)
    arrayUninitIdxMInit rfl rfl rfl hr hf

/-- The UB is the failed `Load` of the uninitialized index operand, not the
bounds check (`"access to out-of-bounds index"`). -/
theorem arrayUninitIdx_minirust_direct :
    Interp.steps 2 arrayUninitIdxMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-! ## Multi-byte elements (`[u32; 3]`): byte offset `index * elem_size` -/

def arrU32_3Ty : Ty := { kind := .array (.uint .u32) 3, layoutIdx := 0 }
def arrU32_3Decl : LocalDecl := { mutability := .mut, ty := arrU32_3Ty, debugName := none }

def arrU32_3Layout : TypeLayout :=
  { size := { bytes := 12 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiArrayU32Idx : FnAbi :=
  { args := [{ layout := arrU32_3Layout, mode := .direct },
             { layout := usizeLayout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- The callee's locals live at addresses `128` (`_0`), `256` (`_1`, twelve
bytes), and `384` (`_2`). -/
def ctxU32_3 : Ctx := { ctx0 with addrs := [128, 256, 384] }

theorem ctxU32_ok_arrayU32Idx {body : CapturedMir}
    (h : body.localDecls = [u32Decl, arrU32_3Decl, usizeDecl]) : CtxOk body ctxU32_3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [u32Decl, u32Ty, itOf_uint, tyOf_uint]; decide
    | 1, hd => simp at hd; subst hd; rw [arrU32_3Decl, arrU32_3Ty, itOf_array_uint, tyOf_array_uint]; decide
    | 2, hd => simp at hd; subst hd; rw [usizeDecl, usizeTy, itOf_uint, tyOf_uint]; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by rw [u32Decl, u32Ty, itOf_uint]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of a function that writes
`const 0x04030201_u32` into `_1[_2]` of a `[u32; 3]` argument and returns
`_1[_2] + _1[0 of 3]`. -/
def arrayU32Idx : CapturedMir where
  defPath := "witness::array_u32_idx"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, arrU32_3Decl, usizeDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (placeIdx 1 2) (.use (constU32 0x04030201))),
        mkStmt (.assign (local_ 0)
          (.binaryOp .add (.copy (placeIdx 1 2)) (.copy (placeConstIdx 1 0 3 false))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArrayU32Idx
  layouts := emptyLayoutTable
  allocations := []

theorem arrayU32Idx_inFragment : inFragment arrayU32Idx = true := by decide

def arrayU32IdxFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Array (.Int u32) 3),
    (localName 2, .Int usizeIt)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Index (.Local (localName 1)) (.Load (.Local (localName 2))))
        (.Constant (.Int 0x04030201) (.Int u32)),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add)
          (.Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2)))))
          (.Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arrayU32Idx_translate : translateFn arrayU32Idx = some arrayU32IdxFn := rfl

def initArrU32_3 : Value := .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩]

/-- Index `_2 = 2usize`: `_1 = [10, 20, 0x04030201]`, returning
`0x04030201 + 10 = 0x0403020b`. -/
def arrayU32IdxOkS0 : MachineState :=
  initMachineState arrayU32Idx [initArrU32_3, .scalar ⟨2, 8⟩]
def arrayU32IdxOkMInit : Mach :=
  machineWithCtx ctxU32_3 arrayU32Idx arrayU32IdxFn arrayU32IdxOkS0.frame.locals
    arrayU32IdxFn.start

theorem arrayU32IdxOk_anneal_ret :
    ReachesRet (mirCallTree arrayU32Idx [initArrU32_3, .scalar ⟨2, 8⟩]) []
      (.normal (.scalar ⟨0x0403020b, 4⟩, arrayU32IdxOkS0.memory)) :=
  runA_sound arrayU32Idx 8 _ _ _ rfl

theorem arrayU32IdxOk_noUB :
    MirNoUBTree (mirCallTree arrayU32Idx [initArrU32_3, .scalar ⟨2, 8⟩]) :=
  runA_noUB arrayU32Idx 8 _ _ _ rfl

theorem arrayU32IdxOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n arrayU32IdxOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 0x0403020b } ∧
      m'.threads = [thread1 ctxU32_3 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret arrayU32Idx_inFragment arrayU32Idx_translate ctxU32_3
      (ctxU32_ok_arrayU32Idx rfl) [initArrU32_3, .scalar ⟨2, 8⟩] (by decide)
      arrayU32IdxOkMInit rfl rfl rfl arrayU32IdxOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [arrayU32Idx] at hd; subst hd
  simp [retPtr, ctxU32_3, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxU32_3, ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem arrayU32IdxOk_minirust_direct :
    (Interp.steps 4 arrayU32IdxOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 0x0403020b }, [1]) := rfl

/-- Byte-level view of the in-place write: MiniRust's allocation `2` is `_1`'s
(after the caller's return allocation and `_0`'s). Before step `2` it holds
the little-endian bytes of `[10, 20, 30]`; step `2` (`_1[_2] = 0x04030201`
with `_2 = 2`) rewrites exactly bytes `8..12` (`2 * size_of::<u32>()`) to
`01 02 03 04`, leaving bytes `0..8` (elements `0` and `1`) unchanged. -/
theorem arrayU32IdxOk_minirust_inplace_bytes :
    [1, 2].map (fun k => (Interp.steps k arrayU32IdxOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[2]?).map (·.data))) =
      [some (some (scalarBytes u32 10 ++ scalarBytes u32 20 ++ scalarBytes u32 30)),
       some (some (scalarBytes u32 10 ++ scalarBytes u32 20 ++
         [.Init 1 none, .Init 2 none, .Init 3 none, .Init 4 none]))] := rfl

/-- Index `_2 = 3usize` (`3 >= 3`): out-of-bounds UB on the in-place write. -/
def arrayU32IdxOobS0 : MachineState :=
  initMachineState arrayU32Idx [initArrU32_3, .scalar ⟨3, 8⟩]
def arrayU32IdxOobMInit : Mach :=
  machineWithCtx ctxU32_3 arrayU32Idx arrayU32IdxFn arrayU32IdxOobS0.frame.locals
    arrayU32IdxFn.start

theorem arrayU32IdxOob_anneal_ub :
    ∃ tr u, Reaches (mirCallTree arrayU32Idx [initArrU32_3, .scalar ⟨3, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayU32Idx 6 _ (by decide)

theorem arrayU32IdxOob_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayU32IdxOobMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayU32IdxOob_anneal_ub
  exact mirCall_ub arrayU32Idx_inFragment arrayU32Idx_translate ctxU32_3
    (ctxU32_ok_arrayU32Idx rfl) [initArrU32_3, .scalar ⟨3, 8⟩] (by decide)
    arrayU32IdxOobMInit rfl rfl rfl hr hf

theorem arrayU32IdxOob_minirust_direct :
    Interp.steps 2 arrayU32IdxOobMInit = .error (.ub "access to out-of-bounds index") := rfl

/-! ## Out-of-bounds `ConstantIndex` (`fromEnd = false, offset >= count`), `PlaceMention` on an array local, and `Interp` representation checks -/

/-- MIR (`Runtime(PostCleanup)`) of a function that executes `PlaceMention(_1)`
on a `[i8; 2]` array local and then attempts to read `_1[2 of 2]`
(`ProjectionElem.constantIndex 2 2 false`, where `fromEnd = false` and
`offset = 2 >= 2`), raising out-of-bounds UB in both Anneal and MiniRust. -/
def arrayConstIdxOobI8 : CapturedMir where
  defPath := "witness::array_const_idx_oob_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [i8Decl, arrI8_2Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.placeMention (local_ 1)),
        mkStmt (.assign (local_ 0) (.use (.copy (placeConstIdx 1 2 2 false))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArrayUninitIdx
  layouts := emptyLayoutTable
  allocations := []

theorem arrayConstIdxOobI8_inFragment : inFragment arrayConstIdxOobI8 = true := by decide

def arrayConstIdxOobI8Fn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Array (.Int i8) 2)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .PlaceMention (.Local (localName 1)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Local (localName 1)) (.Constant (.Int 2) (.Int usizeIt))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem arrayConstIdxOobI8_translate :
    translateFn arrayConstIdxOobI8 = some arrayConstIdxOobI8Fn := rfl

def arrayConstIdxOobS0 : MachineState := initMachineState arrayConstIdxOobI8 [initArrI8_2]
def arrayConstIdxOobMInit : Mach :=
  machineWithCtx ctxI8 arrayConstIdxOobI8 arrayConstIdxOobI8Fn
    arrayConstIdxOobS0.frame.locals arrayConstIdxOobI8Fn.start

theorem arrayConstIdxOob_anneal_ub :
    ∃ tr u, Reaches (mirCallTree arrayConstIdxOobI8 [initArrI8_2]) tr u ∧ FaultNow u :=
  faultsA_sound arrayConstIdxOobI8 6 _ (by decide)

theorem arrayConstIdxOob_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayConstIdxOobMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayConstIdxOob_anneal_ub
  exact mirCall_ub arrayConstIdxOobI8_inFragment arrayConstIdxOobI8_translate ctxI8
    (ctxI8_ok_arrayUninitIdx rfl) [initArrI8_2] (by decide)
    arrayConstIdxOobMInit rfl rfl rfl hr hf

theorem arrayConstIdxOob_minirust_direct :
    Interp.steps 3 arrayConstIdxOobMInit = .error (.ub "access to out-of-bounds index") := rfl

/-- `Size::ZERO * -1 = Size::ZERO` (`Size::from_bytes(0 * -1).unwrap()`), whereas
multiplying a non-zero `Size` by `-1` panics with a negative byte count. -/
theorem sizeMulInt_zero_neg :
    Size.mulInt ⟨0⟩ (-1) = .ok ⟨0⟩ ∧
    Size.mulInt ⟨1⟩ (-1) = .error (.specPanic "Size * Int: negative byte count") :=
  ⟨rfl, rfl⟩

/-- `Type.encode` on `Type::Array` checks `assert_eq!(values.len(), count)`
before encoding elements or computing `elem.layout()` (so an empty 0-length
array succeeds without querying `elem.layout()`), and `Type.decode` on
`Type::Array` short-circuits left-to-right via `tryMapM` on the first `.Uninit`
element chunk. -/
theorem array_encode_decode_edge_cases :
    checkValue (.Tuple []) (.Array (.Slice (.Int i8)) 0) = .ok () ∧
    checkValue (.Tuple []) (.Array (.Int i8) 1) =
      .error (.ub "Value::Tuple: invalid number of elements") ∧
    checkValue (.Tuple [.Int 200]) (.Array (.Int i8) 1) =
      .error (.ub "Value::Int: invalid integer value") ∧
    Type.encode (.Array (.Slice (.Int i8)) 2) (.Tuple []) =
      .error (.specPanic "encode: Type::Array length mismatch") ∧
    Type.encode (.Array (.Slice (.Int i8)) 0) (.Tuple []) = .ok [] ∧
    Type.decode (.Array (.Int i8) 2) [.Uninit, .Init 5 none] = .ok none ∧
    Type.decode (.Array (.Int i8) 2) [.Init 1 none] =
      .error (.specPanic "decode of Type::Array with invalid length") ∧
    Type.decode (.Array (.Int i8) (-1)) [] =
      .error (.specPanic "Size * Int: negative byte count") ∧
    Type.decode (.Array (.Array (.Int i8) 0) (-1)) [] = .ok (some (.Tuple [])) ∧
    (tryMapM (fun x : Nat =>
      if x = 0 then (.ok none : Interp (Option Val))
      else .error (.specPanic "unreachable")) [0, 1] : Interp (Option (List Val))) =
      .ok none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Projected array operands across `SwitchInt`/`Repeat`/`Aggregate`/`UnaryOp`/`Cast`, faulting array rvalues, and faulting in-place write RHS -/

def fnAbiArrayCompose : FnAbi :=
  { args := [{ layout := arrI8_2Layout, mode := .direct },
             { layout := usizeLayout, mode := .direct }],
    ret := { layout := i8Layout, mode := .direct }, conv := .rust, canUnwind := false }

theorem ctxI8_ok_arrayCompose {body : CapturedMir}
    (h : body.localDecls = [i8Decl, arrI8_2Decl, usizeDecl]) : CtxOk body ctxI8_3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd
    match i, hd with
    | 0, hd => simp at hd; subst hd; rw [i8Decl, i8Ty, itOf_int, tyOf_int]; decide
    | 1, hd => simp at hd; subst hd; rw [arrI8_2Decl, arrI8_2Ty, itOf_array_int, tyOf_array_int]; decide
    | 2, hd => simp at hd; subst hd; rw [usizeDecl, usizeTy, itOf_uint, tyOf_uint]; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; simp at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by rw [i8Decl, i8Ty, itOf_int]; decide⟩

/-- MIR (`Runtime(PostCleanup)`) of a function exercising projected array
element operands (`copy _1[proj]`) across `SwitchInt`, `Repeat`,
`Aggregate(Array)`, `UnaryOp(Neg)`, and `Cast(IntToInt)`, as well as the UB
branches of `evalStatement_assign_array` (`Aggregate` and `Repeat` with a
faulting operand) and `evalStatement_assign_index` (in-place indexed write with
a faulting RHS, and when both destination projection and RHS fault):
* `bb0`: `SwitchInt(copy _1[_2])` branches on `10 -> bb1`, `20 -> bb2`,
  `30 -> bb3`, `40 -> bb4`, `otherwise -> bb5` (and faults in `bb0` if `_2 >= 2`);
* `bb1`: `_1 = Repeat(copy _1[_2], 2)`,
  `_1 = Aggregate(Array(i8), [copy _1[0 of 2], const 20i8])`,
  `_1[_2] = UnaryOp(Neg, copy _1[-1 of 2])`,
  `_0 = Cast(IntToInt, copy _1[0 of 2], i8Ty)`, then `Return`;
* `bb2`: `_1 = Aggregate(Array(i8), [copy _1[0 of 2], copy _0])` (faults on
  uninitialized `_0` in element `1`);
* `bb3`: `_1 = Repeat(copy _1[2 of 2], 2)` (faults on out-of-bounds
  `ConstantIndex` `2 >= 2`);
* `bb4`: `_1[0 of 2] = BinaryOp(Div, copy _1[0 of 2], const 0i8)` (valid
  destination index `0`, faulting RHS division by zero);
* `bb5`: `_1[2 of 2] = BinaryOp(Div, copy _1[0 of 2], const 0i8)` (both
  destination projection `2 >= 2` and RHS division by zero fault). -/
def arrayComposeI8 : CapturedMir where
  defPath := "witness::array_compose_i8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [i8Decl, arrI8_2Decl, usizeDecl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (placeIdx 1 2))
        { branches := [(10, 1), (20, 2), (30, 3), (40, 4)], otherwise := 5 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.repeat (.copy (placeIdx 1 2)) 2)),
        mkStmt (.assign (local_ 1)
          (.aggregate (.array i8Ty) [.copy (placeConstIdx 1 0 2 false), constI8 20])),
        mkStmt (.assign (placeIdx 1 2)
          (.unaryOp .neg (.copy (placeConstIdx 1 1 2 true)))),
        mkStmt (.assign (local_ 0)
          (.cast .intToInt (.copy (placeConstIdx 1 0 2 false)) i8Ty))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1)
          (.aggregate (.array i8Ty) [.copy (placeConstIdx 1 0 2 false), .copy (local_ 0)]))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.repeat (.copy (placeConstIdx 1 2 2 false)) 2))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (placeConstIdx 1 0 2 false)
          (.binaryOp .div (.copy (placeConstIdx 1 0 2 false)) (constI8 0)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (placeConstIdx 1 2 2 false)
          (.binaryOp .div (.copy (placeConstIdx 1 0 2 false)) (constI8 0)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiArrayCompose
  layouts := emptyLayoutTable
  allocations := []

theorem arrayComposeI8_inFragment : inFragment arrayComposeI8 = true := by decide

def arrayComposeI8Fn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int i8),
    (localName 1, .Array (.Int i8) 2),
    (localName 2, .Int usizeIt)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[],
      .Switch (.Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2)))))
        ⟨[(10, bbName 1), (20, bbName 2), (30, bbName 3), (40, bbName 4)]⟩ (bbName 5),
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2)))),
          .Load (.Index (.Local (localName 1)) (.Load (.Local (localName 2))))]
          (.Array (.Int i8) 2)),
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))),
          .Constant (.Int 20) (.Int i8)] (.Array (.Int i8) 2)),
      .Assign (.Index (.Local (localName 1)) (.Load (.Local (localName 2))))
        (.UnOp (.Int .Neg)
          (.Load (.Index (.Local (localName 1)) (.Constant (.Int 1) (.Int usizeIt))))),
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt i8))
          (.Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt)))))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))),
          .Load (.Local (localName 0))] (.Array (.Int i8) 2))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Index (.Local (localName 1)) (.Constant (.Int 2) (.Int usizeIt))),
          .Load (.Index (.Local (localName 1)) (.Constant (.Int 2) (.Int usizeIt)))]
          (.Array (.Int i8) 2))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[
      .Assign (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt)))
        (.BinOp (.Int .Div)
          (.Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))))
          (.Constant (.Int 0) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 5, ⟨[
      .Assign (.Index (.Local (localName 1)) (.Constant (.Int 2) (.Int usizeIt)))
        (.BinOp (.Int .Div)
          (.Load (.Index (.Local (localName 1)) (.Constant (.Int 0) (.Int usizeIt))))
          (.Constant (.Int 0) (.Int i8)))],
      .Return, .Regular⟩),
    (bbName 6, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 6
  implicit_writes := true

theorem arrayComposeI8_translate : translateFn arrayComposeI8 = some arrayComposeI8Fn := rfl

def initArrCompose10_20 : Value := .aggregate 0 [.scalar ⟨10, 1⟩, .scalar ⟨20, 1⟩]

/-- `_1 = [10i8, 20i8]`, `_2 = 0usize`: switches on `_1[0] = 10` to `bb1`,
repeats `_1[0]` into `[10, 10]`, rebuilds `[10, 20]`, negates `_1[-1 of 2] = 20`
into `_1[0] = -20i8` (bits `236`), casts `_1[0]` to `i8`, and returns `-20i8`. -/
def arrayComposeOkS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose10_20, .scalar ⟨0, 8⟩]
def arrayComposeOkMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeOkS0.frame.locals arrayComposeI8Fn.start

def arrayComposeOkTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 10))), PUnit.unit⟩]

theorem arrayComposeOk_anneal_ret :
    ReachesRet (mirCallTree arrayComposeI8 [initArrCompose10_20, .scalar ⟨0, 8⟩])
      arrayComposeOkTrace (.normal (.scalar ⟨236, 1⟩, arrayComposeOkS0.memory)) :=
  runA_sound arrayComposeI8 12 _ _ _ rfl

theorem arrayComposeOk_noUB :
    MirNoUBTree (mirCallTree arrayComposeI8 [initArrCompose10_20, .scalar ⟨0, 8⟩]) :=
  runA_noUB arrayComposeI8 12 _ _ _ rfl

theorem arrayComposeOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n arrayComposeOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes i8 236 } ∧
      m'.threads = [thread1 ctxI8_3 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
      (ctxI8_ok_arrayCompose rfl) [initArrCompose10_20, .scalar ⟨0, 8⟩] (by decide)
      arrayComposeOkMInit rfl rfl rfl arrayComposeOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [arrayComposeI8] at hd; subst hd
  simp [retPtr, ctxI8_3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem arrayComposeOk_minirust_direct :
    (Interp.steps 7 arrayComposeOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes i8 236 }, [1]) := rfl

/-- `_1 = [10i8, 20i8]`, `_2 = 1usize`: switches on `_1[1] = 20` to `bb2` and
faults when `Aggregate(Array)` evaluates its second operand `copy _0` while `_0`
is `.uninit` (`evalStatement_assign_array` UB branch). -/
def arrayComposeAggUbS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose10_20, .scalar ⟨1, 8⟩]
def arrayComposeAggUbMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeAggUbS0.frame.locals arrayComposeI8Fn.start

theorem arrayComposeAggUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arrayComposeI8 [initArrCompose10_20, .scalar ⟨1, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayComposeI8 8 _ (by decide)

theorem arrayComposeAggUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayComposeAggUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayComposeAggUb_anneal_ub
  exact mirCall_ub arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
    (ctxI8_ok_arrayCompose rfl) [initArrCompose10_20, .scalar ⟨1, 8⟩] (by decide)
    arrayComposeAggUbMInit rfl rfl rfl hr hf

theorem arrayComposeAggUb_minirust_direct :
    Interp.steps 3 arrayComposeAggUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

/-- `_1 = [30i8, 20i8]`, `_2 = 0usize`: switches on `_1[0] = 30` to `bb3` and
faults when `Repeat(copy _1[2 of 2], 2)` evaluates its out-of-bounds
`ConstantIndex` operand (`evalStatement_assign_array` UB branch). -/
def initArrCompose30_20 : Value := .aggregate 0 [.scalar ⟨30, 1⟩, .scalar ⟨20, 1⟩]

def arrayComposeRepeatUbS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose30_20, .scalar ⟨0, 8⟩]
def arrayComposeRepeatUbMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeRepeatUbS0.frame.locals arrayComposeI8Fn.start

theorem arrayComposeRepeatUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arrayComposeI8 [initArrCompose30_20, .scalar ⟨0, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayComposeI8 8 _ (by decide)

theorem arrayComposeRepeatUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayComposeRepeatUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayComposeRepeatUb_anneal_ub
  exact mirCall_ub arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
    (ctxI8_ok_arrayCompose rfl) [initArrCompose30_20, .scalar ⟨0, 8⟩] (by decide)
    arrayComposeRepeatUbMInit rfl rfl rfl hr hf

theorem arrayComposeRepeatUb_minirust_direct :
    Interp.steps 3 arrayComposeRepeatUbMInit =
      .error (.ub "access to out-of-bounds index") := rfl

/-- `_1 = [40i8, 20i8]`, `_2 = 0usize`: switches on `_1[0] = 40` to `bb4` and
faults on the RHS division by zero in `_1[0 of 2] = Div(copy _1[0 of 2], 0i8)`
while the destination projection `_1[0 of 2]` is in-bounds (`projIdx = some 0`,
`rvBits = none` in `evalStatement_assign_index`). -/
def initArrCompose40_20 : Value := .aggregate 0 [.scalar ⟨40, 1⟩, .scalar ⟨20, 1⟩]

def arrayComposeRhsUbS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose40_20, .scalar ⟨0, 8⟩]
def arrayComposeRhsUbMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeRhsUbS0.frame.locals arrayComposeI8Fn.start

theorem arrayComposeRhsUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arrayComposeI8 [initArrCompose40_20, .scalar ⟨0, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayComposeI8 8 _ (by decide)

theorem arrayComposeRhsUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayComposeRhsUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayComposeRhsUb_anneal_ub
  exact mirCall_ub arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
    (ctxI8_ok_arrayCompose rfl) [initArrCompose40_20, .scalar ⟨0, 8⟩] (by decide)
    arrayComposeRhsUbMInit rfl rfl rfl hr hf

theorem arrayComposeRhsUb_minirust_direct :
    Interp.steps 3 arrayComposeRhsUbMInit = .error (.ub "division by zero") := rfl

/-- `_1 = [50i8, 20i8]`, `_2 = 0usize`: takes `otherwise` (`bb5`) where both the
destination projection `_1[2 of 2]` (`2 >= 2`) and the RHS `Div(..., 0i8)` fault
(`projIdx = none` and `rvBits = none`). Anneal faults on `evalRvalue` first and
MiniRust faults on `eval_place(destination)` first, so both raise UB. -/
def initArrCompose50_20 : Value := .aggregate 0 [.scalar ⟨50, 1⟩, .scalar ⟨20, 1⟩]

def arrayComposeBothUbS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose50_20, .scalar ⟨0, 8⟩]
def arrayComposeBothUbMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeBothUbS0.frame.locals arrayComposeI8Fn.start

theorem arrayComposeBothUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arrayComposeI8 [initArrCompose50_20, .scalar ⟨0, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayComposeI8 8 _ (by decide)

theorem arrayComposeBothUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayComposeBothUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayComposeBothUb_anneal_ub
  exact mirCall_ub arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
    (ctxI8_ok_arrayCompose rfl) [initArrCompose50_20, .scalar ⟨0, 8⟩] (by decide)
    arrayComposeBothUbMInit rfl rfl rfl hr hf

theorem arrayComposeBothUb_minirust_direct :
    Interp.steps 3 arrayComposeBothUbMInit =
      .error (.ub "access to out-of-bounds index") := rfl

/-- `_1 = [10i8, 20i8]`, `_2 = 2usize`: faults in `bb0` when `SwitchInt`
evaluates its out-of-bounds projected discriminant `copy _1[_2]` (`2 >= 2`). -/
def arrayComposeSwitchOobUbS0 : MachineState :=
  initMachineState arrayComposeI8 [initArrCompose10_20, .scalar ⟨2, 8⟩]
def arrayComposeSwitchOobUbMInit : Mach :=
  machineWithCtx ctxI8_3 arrayComposeI8 arrayComposeI8Fn
    arrayComposeSwitchOobUbS0.frame.locals arrayComposeI8Fn.start

theorem arrayComposeSwitchOobUb_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree arrayComposeI8 [initArrCompose10_20, .scalar ⟨2, 8⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound arrayComposeI8 6 _ (by decide)

theorem arrayComposeSwitchOobUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n arrayComposeSwitchOobUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := arrayComposeSwitchOobUb_anneal_ub
  exact mirCall_ub arrayComposeI8_inFragment arrayComposeI8_translate ctxI8_3
    (ctxI8_ok_arrayCompose rfl) [initArrCompose10_20, .scalar ⟨2, 8⟩] (by decide)
    arrayComposeSwitchOobUbMInit rfl rfl rfl hr hf

theorem arrayComposeSwitchOobUb_minirust_direct :
    Interp.steps 2 arrayComposeSwitchOobUbMInit =
      .error (.ub "access to out-of-bounds index") := rfl

/-! ## Padded single-variant struct `Padded(u8, u32, u16)` (`TupleFields`, `.Uninit` padding preservation, and scalar `Field` reads/writes) -/

def u16Ty : Ty := { kind := .uint .u16, layoutIdx := 0 }
def u16Decl : LocalDecl := { mutability := .mut, ty := u16Ty, debugName := none }
def u16 : Gen.IntType := ⟨.Unsigned, ⟨2⟩⟩
def constU16 (n : Nat) : Operand := .constant { ty := u16Ty, val := .scalar (.int ⟨n, 2⟩) }

def placeField (loc : Nat) (projs : List (Nat × Ty)) : Place :=
  { local_ := loc, projection := projs.map (fun (f, t) => .field f t) }

/-- Compiler layout for `struct Padded(u8, u32, u16)`:
- field `0` (`u8`, 1 byte) at offset `0`
- padding bytes `1..4` (`3` bytes of `AbstractByte.Uninit`)
- field `1` (`u32`, 4 bytes) at offset `4`
- field `2` (`u16`, 2 bytes) at offset `8`
- trailing padding bytes `10..12` (`2` bytes of `AbstractByte.Uninit`)
- total `size = 12`, `align = 4`. -/
def paddedStructLayout : TypeLayout :=
  { size := { bytes := 12 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }, { bytes := 8 }] [0, 1, 2],
    variants := .single 0, isUninhabited := false, fieldLayouts := [0, 0, 0] }

def paddedLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [paddedStructLayout] }

def paddedStructTy : Ty :=
  { kind := .adt "witness::Padded" [.uint .u8, .uint .u32, .uint .u16], layoutIdx := 0 }

def paddedStructDecl : LocalDecl :=
  { mutability := .mut, ty := paddedStructTy, debugName := none }

def paddedMiniRustTy : Gen.Type :=
  .Tuple [(⟨0⟩, .Int u8), (⟨4⟩, .Int u32), (⟨8⟩, .Int u16)]
    { «end» := ⟨12⟩, align := ⟨4⟩, packed_align := none } none

def fnAbiPaddedStruct : FnAbi :=
  { args := [{ layout := paddedStructLayout, mode := .direct },
             { layout := paddedStructLayout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

def ctxPadded3 : Ctx :=
  { caller := callerFrame, payloads := [], base := [retAlloc], addrs := [128, 256, 512],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxPadded3_ok {body : CapturedMir}
    (h : body.localDecls = [u32Decl, paddedStructDecl, paddedStructDecl])
    (hlay : body.layouts = paddedLayouts) : CtxOk body ctxPadded3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd; rw [hlay]
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | _ + 3, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; rw [hlay]; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR (`Runtime(PostCleanup)`) of
```rust
struct Padded(u8, u32, u16);

fn padded_struct_ops(mut s: Padded, mut copy_s: Padded) -> u32 {
    copy_s = s;                                      // _2 = Use(copy _1)
    s = Padded(copy_s.0, 0x04030201, copy_s.2);      // _1 = Aggregate(Adt, [copy _2.0, const 0x04030201_u32, copy _2.2])
    s.1 = s.1.wrapping_add(0x10);                    // _1.1 = Add(copy _1.1, const 0x10_u32)
    let a = s.0 as u32;                              // _0 = Cast(IntToInt, copy _1.0, u32)
    a.wrapping_add(s.1)                              // _0 = Add(copy _0, copy _1.1)
}
```
exercising whole-struct `Use(Copy)`, `AggregateKind.adt` construction,
`ProjectionElem.field` reads (`_2.0`, `_2.2`, `_1.0`, `_1.1`), and in-place
scalar field writes (`_1.1 = ...` at byte offset `4`) while preserving sibling
fields (`_1.0` at offset `0` and `_1.2` at offset `8..10`) and `AbstractByte.Uninit`
padding bytes at `1..4` and `10..12`. -/
def paddedStructOps : CapturedMir where
  defPath := "witness::padded_struct_ops"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, paddedStructDecl, paddedStructDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 1)
          (.aggregate (.adt "witness::Padded" 0 none)
            [.copy (placeField 2 [(0, u8TyW)]),
             constU32 0x04030201,
             .copy (placeField 2 [(2, u16Ty)])])),
        mkStmt (.assign (placeField 1 [(1, u32Ty)])
          (.binaryOp .add (.copy (placeField 1 [(1, u32Ty)])) (constU32 0x10))),
        mkStmt (.assign (local_ 0)
          (.cast .intToInt (.copy (placeField 1 [(0, u8TyW)])) u32Ty)),
        mkStmt (.assign (local_ 0)
          (.binaryOp .add (.copy (placeField 1 [(1, u32Ty)])) (.copy (local_ 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedStruct
  layouts := paddedLayouts
  allocations := []

theorem paddedStructOps_inFragment : inFragment paddedStructOps = true := by decide

def paddedStructOpsFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32),
    (localName 1, paddedMiniRustTy),
    (localName 2, paddedMiniRustTy)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Assign (.Local (localName 2)) (.Load (.Local (localName 1))),
      .Assign (.Local (localName 1))
        (.Tuple [
          .Load (.Field (.Local (localName 2)) 0),
          .Constant (.Int 0x04030201) (.Int u32),
          .Load (.Field (.Local (localName 2)) 2)] paddedMiniRustTy),
      .Assign (.Field (.Local (localName 1)) 1)
        (.BinOp (.Int .Add)
          (.Load (.Field (.Local (localName 1)) 1))
          (.Constant (.Int 0x10) (.Int u32))),
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Field (.Local (localName 1)) 0))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add)
          (.Load (.Field (.Local (localName 1)) 1))
          (.Load (.Local (localName 0))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem paddedStructOps_translate : translateFn paddedStructOps = some paddedStructOpsFn := rfl

def initPaddedStruct : Value :=
  .aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨99, 4⟩, .scalar ⟨0x0605, 2⟩]

def initPaddedStruct2 : Value :=
  .aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0, 4⟩, .scalar ⟨0, 2⟩]

def paddedArgs : List Value := [initPaddedStruct, initPaddedStruct2]

def paddedStructOkS0 : MachineState := initMachineState paddedStructOps paddedArgs
def paddedStructOkMInit : Mach :=
  machineWithCtx ctxPadded3 paddedStructOps paddedStructOpsFn
    paddedStructOkS0.frame.locals paddedStructOpsFn.start

theorem paddedStructOk_anneal_ret :
    ReachesRet (mirCallTree paddedStructOps paddedArgs) []
      (.normal (.scalar ⟨0x04030218, 4⟩, paddedStructOkS0.memory)) :=
  runA_sound paddedStructOps 10 _ _ _ rfl

theorem paddedStructOk_noUB :
    MirNoUBTree (mirCallTree paddedStructOps paddedArgs) :=
  runA_noUB paddedStructOps 10 _ _ _ rfl

theorem paddedStructOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n paddedStructOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 0x04030218 } ∧
      m'.threads = [thread1 ctxPadded3 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret paddedStructOps_inFragment paddedStructOps_translate ctxPadded3
      (ctxPadded3_ok rfl rfl) paddedArgs (by decide)
      paddedStructOkMInit rfl rfl rfl paddedStructOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [paddedStructOps] at hd; subst hd
  simp [retPtr, ctxPadded3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxPadded3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem paddedStructOk_minirust_direct :
    (Interp.steps 7 paddedStructOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 0x04030218 }, [1]) := rfl

/-- Byte-level proof that MiniRust preserves `AbstractByte.Uninit` at the
inter-field padding offsets `1..4` and trailing padding offsets `10..12` across:
- step `2` (`_2 = Use(copy _1)`: allocation `3` for `_2` receives `(7u8, 99u32, 0x0605u16)`
  with `.Uninit` at `1..4` and `10..12`),
- step `3` (`_1 = Aggregate(Adt, ...)`: allocation `2` for `_1` receives
  `(7u8, 0x04030201u32, 0x0605u16)` with `.Uninit` at `1..4` and `10..12`), and
- step `4` (`_1.1 = Add(copy _1.1, 0x10u32)`: in-place write at offset `4` updates
  bytes `4..8` to `0x11 0x02 0x03 0x04` while leaving field `0` (`byte 0 = 7`),
  inter-field padding (`bytes 1..4 = .Uninit`), field `2` (`bytes 8..10 = 0x05 0x06`),
  and trailing padding (`bytes 10..12 = .Uninit`) untouched). -/
theorem paddedStructOk_minirust_padding_bytes :
    ((Interp.steps 2 paddedStructOkMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[3]?).map (·.data))) =
      some [.Init 7 none, .Uninit, .Uninit, .Uninit,
            .Init 99 none, .Init 0 none, .Init 0 none, .Init 0 none,
            .Init 5 none, .Init 6 none, .Uninit, .Uninit] ∧
    ((Interp.steps 3 paddedStructOkMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[2]?).map (·.data))) =
      some [.Init 7 none, .Uninit, .Uninit, .Uninit,
            .Init 1 none, .Init 2 none, .Init 3 none, .Init 4 none,
            .Init 5 none, .Init 6 none, .Uninit, .Uninit] ∧
    ((Interp.steps 4 paddedStructOkMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[2]?).map (·.data))) =
      some [.Init 7 none, .Uninit, .Uninit, .Uninit,
            .Init 0x11 none, .Init 2 none, .Init 3 none, .Init 4 none,
            .Init 5 none, .Init 6 none, .Uninit, .Uninit] :=
  ⟨rfl, rfl, rfl⟩

/-- On `Terminator::Return` at step `7` of `paddedStructOps`, `evalReturn` calls
`storageDead` on every callee local (`_0`..`_2`, allocations `1..=3`), verifying
`BM.deallocate` against each local's layout (`size = 12, align = 4` for the two
`Padded(u8, u32, u16)` struct locals `_1` and `_2` at allocations `2` and `3`)
and marking all three callee stack allocations `live = false` while keeping the
caller's return allocation `0` `live = true`. -/
theorem paddedStructOk_minirust_ret_dealloc :
    (Interp.steps 7 paddedStructOkMInit).toOption.map
        (fun m => m.mem.memory.allocations.map (fun a => (a.live, a.data.length))) =
      some [(true, 4), (false, 4), (false, 12), (false, 12)] := rfl

theorem paddedStructOk_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n paddedStructOkMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k paddedStructOkMInit = .ok mRet ∧
      ReturnRel paddedStructOps ctxPadded3 s' v mRet ∧
      ReachesRet (mirCallTree paddedStructOps paddedArgs) tr (.normal (v, mem)) :=
  mirCall_noUB paddedStructOps_inFragment paddedStructOps_translate ctxPadded3
    (ctxPadded3_ok rfl rfl) paddedArgs (by decide) paddedStructOkMInit rfl rfl rfl
    paddedStructOk_noUB herr

theorem paddedStructOk_minirust_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (n + 1) paddedStructOkMInit = .ok m' ∧
      StateRel paddedStructOps paddedStructOpsFn ctxPadded3 s' m' ∧
      Reaches (mirCallTree paddedStructOps paddedArgs) tr (mirTree paddedStructOps s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n + 1 ∧ Interp.steps k paddedStructOkMInit = .ok mRet ∧
      ReturnRel paddedStructOps ctxPadded3 s' v mRet ∧
      ReachesRet (mirCallTree paddedStructOps paddedArgs) tr (.normal (v, mem))) :=
  by simpa only [show initLen paddedStructOps = 1 from rfl, Nat.add_comm 1 n] using
    mirCall_progress paddedStructOps_inFragment paddedStructOps_translate ctxPadded3
      (ctxPadded3_ok rfl rfl) paddedArgs (by decide) paddedStructOkMInit rfl rfl rfl
      paddedStructOk_noUB n

/-! ## Nested padded tuples `((u8, u32), u16, ())`, zero-sized `()`, nested `Field` projections (`_4.0.1`), and tuple UB paths -/

def innerTupleLayout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1],
    variants := .single 0, isUninhabited := false, fieldLayouts := [0, 0] }

def unitTupleLayout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [] [],
    variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def outerTupleLayout : TypeLayout :=
  { size := { bytes := 12 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }, { bytes := 10 }] [0, 1, 2],
    variants := .single 0, isUninhabited := false, fieldLayouts := [1, 0, 2] }

def nestedLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [unitTupleLayout, innerTupleLayout, unitTupleLayout, outerTupleLayout] }

def innerTupleKind : RigidTy := .tuple [.uint .u8, .uint .u32]
def innerTupleTy : Ty := { kind := innerTupleKind, layoutIdx := 1 }
def innerTupleDecl : LocalDecl := { mutability := .mut, ty := innerTupleTy, debugName := none }

def unitTupleKind : RigidTy := .tuple []
def unitTupleTy : Ty := { kind := unitTupleKind, layoutIdx := 2 }
def unitTupleDecl : LocalDecl := { mutability := .mut, ty := unitTupleTy, debugName := none }

def outerTupleKind : RigidTy := .tuple [innerTupleKind, .uint .u16, unitTupleKind]
def outerTupleTy : Ty := { kind := outerTupleKind, layoutIdx := 3 }
def outerTupleDecl : LocalDecl := { mutability := .mut, ty := outerTupleTy, debugName := none }

def innerMiniRustTy : Gen.Type :=
  .Tuple [(⟨0⟩, .Int u8), (⟨4⟩, .Int u32)]
    { «end» := ⟨8⟩, align := ⟨4⟩, packed_align := none } none

def unitMiniRustTy : Gen.Type :=
  .Tuple [] { «end» := ⟨0⟩, align := ⟨1⟩, packed_align := none } none

def outerMiniRustTy : Gen.Type :=
  .Tuple [(⟨0⟩, innerMiniRustTy), (⟨8⟩, .Int u16), (⟨10⟩, unitMiniRustTy)]
    { «end» := ⟨12⟩, align := ⟨4⟩, packed_align := none } none

def ctxNested5 : Ctx :=
  { caller := callerFrame, payloads := [], base := [retAlloc],
    addrs := [128, 256, 384, 512, 640],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

theorem ctxNested5_ok {body : CapturedMir}
    (h : body.localDecls = [u32Decl, u32Decl, innerTupleDecl, unitTupleDecl, outerTupleDecl])
    (hlay : body.layouts = nestedLayouts) : CtxOk body ctxNested5 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d _ hd; rw [h] at hd; rw [hlay]
    match i, hd with
    | 0, hd => simp at hd; subst hd; decide
    | 1, hd => simp at hd; subst hd; decide
    | 2, hd => simp at hd; subst hd; decide
    | 3, hd => simp at hd; subst hd; decide
    | 4, hd => simp at hd; subst hd; decide
    | _ + 5, hd => simp at hd
  ret := by
    intro d hd; rw [h] at hd; rw [hlay]; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

def fnAbiNested : FnAbi :=
  { args := [{ layout := u32Layout, mode := .direct },
             { layout := innerTupleLayout, mode := .direct },
             { layout := unitTupleLayout, mode := .ignore },
             { layout := outerTupleLayout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- MIR (`Runtime(PostCleanup)`) of a function exercising nested padded tuples
`((u8, u32), u16, ())`, zero-sized `()`, nested `Field` projections (`_4.0.1`),
in-place sub-tuple writes (`_4.0 = ...`), in-place nested scalar writes
(`_4.0.1 = ...`), and three tuple/field UB paths:
* `bb0`: `SwitchInt(copy _1)` branches on `0 -> bb1`, `1 -> bb2`, `2 -> bb3`,
  `otherwise -> bb4`;
* `bb1` (`_1 = 0`):
  - `_3 = Aggregate(Tuple, [])` (constructs zero-sized `()`);
  - `_2 = Aggregate(Tuple, [const 3_u8, const 100_u32])` (constructs `(u8, u32)`);
  - `_4 = Aggregate(Tuple, [copy _2, const 500_u16, copy _3])` (constructs nested `((u8, u32), u16, ())`);
  - `_4.0 = Aggregate(Tuple, [const 9_u8, copy _1])` (in-place whole sub-tuple write into field `0` of `_4`);
  - `_4.0.1 = BinaryOp(Add, copy _4.0.1, const 42_u32)` (in-place nested scalar field write at byte offset `0 + 4 = 4`);
  - `_3 = Use(copy _4.2)` (`Use(Copy)` of zero-sized `()` field at offset `10`);
  - `_0 = Cast(IntToInt, copy _4.0.0, u32Ty)` (`_0 = 9u32`);
  - `_0 = BinaryOp(Add, copy _0, copy _4.0.1)` (`_0 = 9 + 42 = 51u32`);
  - `Return`;
* `bb2` (`_1 = 1`): `_2 = Aggregate(Tuple, [const 1_u8, copy _0])` (faults when
  evaluating uninitialized operand `copy _0` inside `Aggregate(Tuple)`);
* `bb3` (`_1 = 2`): constructs `_2` and then executes
  `_2.1 = BinaryOp(Div, copy _1, const 0_u32)` (faults on division by zero in
  the RHS of an in-place field assignment);
* `bb4` (`otherwise`): `_4.0 = Aggregate(Tuple, [copy _4.0.0, copy _0])` (faults
  when evaluating uninitialized operand `copy _0` in an in-place sub-tuple
  assignment `_4.0 = ...`). -/
def nestedTupleOps : CapturedMir where
  defPath := "witness::nested_tuple_ops"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 4
  localDecls := [u32Decl, u32Decl, innerTupleDecl, unitTupleDecl, outerTupleDecl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 1))
        { branches := [(0, 1), (1, 2), (2, 3)], otherwise := 4 }),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 3) (.aggregate .tuple [])),
        mkStmt (.assign (local_ 2) (.aggregate .tuple [constU8 3, constU32 100])),
        mkStmt (.assign (local_ 4)
          (.aggregate .tuple [.copy (local_ 2), constU16 500, .copy (local_ 3)])),
        mkStmt (.assign (placeField 4 [(0, innerTupleTy)])
          (.aggregate .tuple [constU8 9, .copy (local_ 1)])),
        mkStmt (.assign (placeField 4 [(0, innerTupleTy), (1, u32Ty)])
          (.binaryOp .add
            (.copy (placeField 4 [(0, innerTupleTy), (1, u32Ty)]))
            (constU32 42))),
        mkStmt (.assign (local_ 3) (.use (.copy (placeField 4 [(2, unitTupleTy)])))),
        mkStmt (.placeMention (placeField 4 [(0, innerTupleTy)])),
        mkStmt (.placeMention (placeField 4 [(0, innerTupleTy), (1, u32Ty)])),
        mkStmt (.assign (local_ 0)
          (.cast .intToInt (.copy (placeField 4 [(0, innerTupleTy), (0, u8TyW)])) u32Ty)),
        mkStmt (.assign (local_ 0)
          (.binaryOp .add (.copy (local_ 0))
            (.copy (placeField 4 [(0, innerTupleTy), (1, u32Ty)]))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2) (.aggregate .tuple [constU8 1, .copy (local_ 0)]))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 2) (.aggregate .tuple [constU8 1, constU32 10])),
        mkStmt (.assign (placeField 2 [(1, u32Ty)])
          (.binaryOp .div (.copy (local_ 1)) (constU32 0)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (placeField 4 [(0, innerTupleTy)])
          (.aggregate .tuple
            [.copy (placeField 4 [(0, innerTupleTy), (0, u8TyW)]), .copy (local_ 0)]))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiNested
  layouts := nestedLayouts
  allocations := []

theorem nestedTupleOps_inFragment : inFragment nestedTupleOps = true := by decide

def nestedTupleOpsFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32),
    (localName 1, .Int u32),
    (localName 2, innerMiniRustTy),
    (localName 3, unitMiniRustTy),
    (localName 4, outerMiniRustTy)]⟩
  args := [localName 1, localName 2, localName 3, localName 4]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[],
      .Switch (.Load (.Local (localName 1)))
        ⟨[(0, bbName 1), (1, bbName 2), (2, bbName 3)]⟩ (bbName 4),
      .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 3)) (.Tuple [] unitMiniRustTy),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 3) (.Int u8), .Constant (.Int 100) (.Int u32)] innerMiniRustTy),
      .Assign (.Local (localName 4))
        (.Tuple [
          .Load (.Local (localName 2)),
          .Constant (.Int 500) (.Int u16),
          .Load (.Local (localName 3))] outerMiniRustTy),
      .Assign (.Field (.Local (localName 4)) 0)
        (.Tuple [.Constant (.Int 9) (.Int u8), .Load (.Local (localName 1))] innerMiniRustTy),
      .Assign (.Field (.Field (.Local (localName 4)) 0) 1)
        (.BinOp (.Int .Add)
          (.Load (.Field (.Field (.Local (localName 4)) 0) 1))
          (.Constant (.Int 42) (.Int u32))),
      .Assign (.Local (localName 3)) (.Load (.Field (.Local (localName 4)) 2)),
      .PlaceMention (.Field (.Local (localName 4)) 0),
      .PlaceMention (.Field (.Field (.Local (localName 4)) 0) 1),
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt u32))
          (.Load (.Field (.Field (.Local (localName 4)) 0) 0))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add)
          (.Load (.Local (localName 0)))
          (.Load (.Field (.Field (.Local (localName 4)) 0) 1)))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 1) (.Int u8), .Load (.Local (localName 0))] innerMiniRustTy)],
      .Return, .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 1) (.Int u8), .Constant (.Int 10) (.Int u32)] innerMiniRustTy),
      .Assign (.Field (.Local (localName 2)) 1)
        (.BinOp (.Int .Div) (.Load (.Local (localName 1))) (.Constant (.Int 0) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[
      .Assign (.Field (.Local (localName 4)) 0)
        (.Tuple [
          .Load (.Field (.Field (.Local (localName 4)) 0) 0),
          .Load (.Local (localName 0))] innerMiniRustTy)],
      .Return, .Regular⟩),
    (bbName 5, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 5
  implicit_writes := true

theorem nestedTupleOps_translate : translateFn nestedTupleOps = some nestedTupleOpsFn := rfl

def initInnerTuple : Value := .aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨2, 4⟩]
def initUnitTuple : Value := .aggregate 0 []
def initOuterTuple : Value := .aggregate 0 [initInnerTuple, .scalar ⟨10, 2⟩, initUnitTuple]
def nestedArgs (sel : Nat) : List Value :=
  [.scalar ⟨sel, 4⟩, initInnerTuple, initUnitTuple, initOuterTuple]

/-- `_1 = 0u32`: executes `bb1` and returns `9 + 42 = 51u32`. -/
def nestedTupleOkS0 : MachineState := initMachineState nestedTupleOps (nestedArgs 0)
def nestedTupleOkMInit : Mach :=
  machineWithCtx ctxNested5 nestedTupleOps nestedTupleOpsFn
    nestedTupleOkS0.frame.locals nestedTupleOpsFn.start

def nestedTupleOkTrace : List (Event MirEffect) :=
  [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]

theorem nestedTupleOk_anneal_ret :
    ReachesRet (mirCallTree nestedTupleOps (nestedArgs 0)) nestedTupleOkTrace
      (.normal (.scalar ⟨51, 4⟩, nestedTupleOkS0.memory)) :=
  runA_sound nestedTupleOps 20 _ _ _ rfl

theorem nestedTupleOk_noUB :
    MirNoUBTree (mirCallTree nestedTupleOps (nestedArgs 0)) :=
  runA_noUB nestedTupleOps 20 _ _ _ rfl

theorem nestedTupleOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n nestedTupleOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 51 } ∧
      m'.threads = [thread1 ctxNested5 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret nestedTupleOps_inFragment nestedTupleOps_translate ctxNested5
      (ctxNested5_ok rfl rfl) (nestedArgs 0) (by decide)
      nestedTupleOkMInit rfl rfl rfl nestedTupleOk_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [nestedTupleOps] at hd; subst hd
  simp [retPtr, ctxNested5] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxNested5] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem nestedTupleOk_minirust_direct :
    (Interp.steps 13 nestedTupleOkMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 51 }, [1]) := rfl

/-- Byte-level proof on `nestedTupleOps` (`_1 = 0u32`): MiniRust allocation `5`
is `_4 : ((u8, u32), u16, ())` (`12` bytes, `align = 4`) and allocation `4` is
`_3 : ()` (`0` bytes, `align = 1`):
- after step `5` (`_4 = Aggregate(Tuple, [copy _2, 500u16, copy _3])`), `_4` holds
  `(3u8, 100u32)` at `0..8` (with inner padding `1..4 = .Uninit`), `500u16`
  (`0xF4, 0x01`) at `8..10`, `()` at `10..10`, and outer trailing padding
  `10..12 = .Uninit`;
- after step `6` (`_4.0 = Aggregate(Tuple, [9u8, copy _1])`), bytes `0..8` are
  updated to `(9u8, 0u32)` with inner padding `1..4 = .Uninit` while field `1`
  (`500u16` at `8..10`) and outer trailing padding (`10..12 = .Uninit`) remain
  untouched;
- after step `7` (`_4.0.1 = Add(copy _4.0.1, 42u32)`), bytes `4..8` become
  `42u32` while `_4.0.0` (`byte 0 = 9`), inner padding `1..4 = .Uninit`, field `1`
  (`8..10 = 500u16`), and outer trailing padding `10..12 = .Uninit` are preserved;
- allocation `4` (`_3 : ()`) has `data = []` (`0` bytes) throughout. -/
theorem nestedTupleOk_minirust_padding_bytes :
    ((Interp.steps 5 nestedTupleOkMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[5]?).map (·.data))) =
      some [.Init 3 none, .Uninit, .Uninit, .Uninit,
            .Init 100 none, .Init 0 none, .Init 0 none, .Init 0 none,
            .Init 0xF4 none, .Init 0x01 none, .Uninit, .Uninit] ∧
    ((Interp.steps 6 nestedTupleOkMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[5]?).map (·.data))) =
      some [.Init 9 none, .Uninit, .Uninit, .Uninit,
            .Init 0 none, .Init 0 none, .Init 0 none, .Init 0 none,
            .Init 0xF4 none, .Init 0x01 none, .Uninit, .Uninit] ∧
    ((Interp.steps 7 nestedTupleOkMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[5]?).map (·.data))) =
      some [.Init 9 none, .Uninit, .Uninit, .Uninit,
            .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none,
            .Init 0xF4 none, .Init 0x01 none, .Uninit, .Uninit] ∧
    ((Interp.steps 8 nestedTupleOkMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[4]?).map (·.data))) =
      some [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- On `Terminator::Return` at step `13` of `nestedTupleOps`, `evalReturn` calls
`storageDead` on every callee local (`_0`..`_4`, allocations `1..=5`), verifying
`BM.deallocate` against each local's layout (`size = 8, align = 4` for
`_2 : (u8, u32)`, `size = 0, align = 1` for `_3 : ()`, and `size = 12, align = 4`
for `_4 : ((u8, u32), u16, ())`) and marking all five callee stack allocations
`live = false` while keeping the caller's return allocation `0` `live = true`. -/
theorem nestedTupleOk_minirust_ret_dealloc :
    (Interp.steps 13 nestedTupleOkMInit).toOption.map
        (fun m => m.mem.memory.allocations.map (fun a => (a.live, a.data.length))) =
      some [(true, 4), (false, 4), (false, 4), (false, 8), (false, 0), (false, 12)] := rfl

theorem nestedTupleOk_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n nestedTupleOkMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k nestedTupleOkMInit = .ok mRet ∧
      ReturnRel nestedTupleOps ctxNested5 s' v mRet ∧
      ReachesRet (mirCallTree nestedTupleOps (nestedArgs 0)) tr (.normal (v, mem)) :=
  mirCall_noUB nestedTupleOps_inFragment nestedTupleOps_translate ctxNested5
    (ctxNested5_ok rfl rfl) (nestedArgs 0) (by decide) nestedTupleOkMInit rfl rfl rfl
    nestedTupleOk_noUB herr

theorem nestedTupleOk_minirust_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (n + 1) nestedTupleOkMInit = .ok m' ∧
      StateRel nestedTupleOps nestedTupleOpsFn ctxNested5 s' m' ∧
      Reaches (mirCallTree nestedTupleOps (nestedArgs 0)) tr (mirTree nestedTupleOps s')) ∨
    (∃ k s' mRet tr v mem, k ≤ n + 1 ∧ Interp.steps k nestedTupleOkMInit = .ok mRet ∧
      ReturnRel nestedTupleOps ctxNested5 s' v mRet ∧
      ReachesRet (mirCallTree nestedTupleOps (nestedArgs 0)) tr (.normal (v, mem))) :=
  by simpa only [show initLen nestedTupleOps = 1 from rfl, Nat.add_comm 1 n] using
    mirCall_progress nestedTupleOps_inFragment nestedTupleOps_translate ctxNested5
      (ctxNested5_ok rfl rfl) (nestedArgs 0) (by decide) nestedTupleOkMInit rfl rfl rfl
      nestedTupleOk_noUB n

/-- `_1 = 1u32`: branches to `bb2` and faults when `Aggregate(Tuple)` evaluates
its second operand `copy _0` while `_0` is `.uninit`. -/
def nestedTupleAggUbS0 : MachineState := initMachineState nestedTupleOps (nestedArgs 1)
def nestedTupleAggUbMInit : Mach :=
  machineWithCtx ctxNested5 nestedTupleOps nestedTupleOpsFn
    nestedTupleAggUbS0.frame.locals nestedTupleOpsFn.start

theorem nestedTupleAggUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree nestedTupleOps (nestedArgs 1)) tr u ∧ FaultNow u :=
  faultsA_sound nestedTupleOps 8 _ (by decide)

theorem nestedTupleAggUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n nestedTupleAggUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := nestedTupleAggUb_anneal_ub
  exact mirCall_ub nestedTupleOps_inFragment nestedTupleOps_translate ctxNested5
    (ctxNested5_ok rfl rfl) (nestedArgs 1) (by decide)
    nestedTupleAggUbMInit rfl rfl rfl hr hf

theorem nestedTupleAggUb_minirust_direct :
    Interp.steps 3 nestedTupleAggUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

theorem nestedTupleAggUb_converse_error :
    (∃ msg, Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree nestedTupleOps (nestedArgs 1)) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 3 ∧ Interp.steps k nestedTupleAggUbMInit = .ok mRet ∧
      ReturnRel nestedTupleOps ctxNested5 s' v mRet ∧
      ReachesRet (mirCallTree nestedTupleOps (nestedArgs 1)) tr (.normal (v, mem))) :=
  mirCall_steps_error nestedTupleOps_inFragment nestedTupleOps_translate ctxNested5
    (ctxNested5_ok rfl rfl) (nestedArgs 1) (by decide)
    nestedTupleAggUbMInit rfl rfl rfl nestedTupleAggUb_minirust_direct

/-- `_1 = 2u32`: branches to `bb3` and faults on division by zero in the RHS of
`_2.1 = Div(copy _1, const 0_u32)`. -/
def nestedTupleFieldRhsUbS0 : MachineState := initMachineState nestedTupleOps (nestedArgs 2)
def nestedTupleFieldRhsUbMInit : Mach :=
  machineWithCtx ctxNested5 nestedTupleOps nestedTupleOpsFn
    nestedTupleFieldRhsUbS0.frame.locals nestedTupleOpsFn.start

theorem nestedTupleFieldRhsUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree nestedTupleOps (nestedArgs 2)) tr u ∧ FaultNow u :=
  faultsA_sound nestedTupleOps 8 _ (by decide)

theorem nestedTupleFieldRhsUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n nestedTupleFieldRhsUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := nestedTupleFieldRhsUb_anneal_ub
  exact mirCall_ub nestedTupleOps_inFragment nestedTupleOps_translate ctxNested5
    (ctxNested5_ok rfl rfl) (nestedArgs 2) (by decide)
    nestedTupleFieldRhsUbMInit rfl rfl rfl hr hf

theorem nestedTupleFieldRhsUb_minirust_direct :
    Interp.steps 4 nestedTupleFieldRhsUbMInit = .error (.ub "division by zero") := rfl

theorem nestedTupleFieldRhsUb_converse_error :
    (∃ msg, Stop.ub "division by zero" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree nestedTupleOps (nestedArgs 2)) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 4 ∧ Interp.steps k nestedTupleFieldRhsUbMInit = .ok mRet ∧
      ReturnRel nestedTupleOps ctxNested5 s' v mRet ∧
      ReachesRet (mirCallTree nestedTupleOps (nestedArgs 2)) tr (.normal (v, mem))) :=
  mirCall_steps_error nestedTupleOps_inFragment nestedTupleOps_translate ctxNested5
    (ctxNested5_ok rfl rfl) (nestedArgs 2) (by decide)
    nestedTupleFieldRhsUbMInit rfl rfl rfl nestedTupleFieldRhsUb_minirust_direct

/-- `_1 = 3u32`: branches to `bb4` and faults when `_4.0 = Aggregate(Tuple, [copy _4.0.0, copy _0])`
evaluates its uninitialized second operand `copy _0`. -/
def nestedTupleCopyUninitUbS0 : MachineState := initMachineState nestedTupleOps (nestedArgs 3)
def nestedTupleCopyUninitUbMInit : Mach :=
  machineWithCtx ctxNested5 nestedTupleOps nestedTupleOpsFn
    nestedTupleCopyUninitUbS0.frame.locals nestedTupleOpsFn.start

theorem nestedTupleCopyUninitUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree nestedTupleOps (nestedArgs 3)) tr u ∧ FaultNow u :=
  faultsA_sound nestedTupleOps 8 _ (by decide)

theorem nestedTupleCopyUninitUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n nestedTupleCopyUninitUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := nestedTupleCopyUninitUb_anneal_ub
  exact mirCall_ub nestedTupleOps_inFragment nestedTupleOps_translate ctxNested5
    (ctxNested5_ok rfl rfl) (nestedArgs 3) (by decide)
    nestedTupleCopyUninitUbMInit rfl rfl rfl hr hf

theorem nestedTupleCopyUninitUb_minirust_direct :
    Interp.steps 3 nestedTupleCopyUninitUbMInit =
      .error (.ub "load at type but the data in memory violates the language invariant") := rfl

theorem nestedTupleCopyUninitUb_converse_error :
    (∃ msg, Stop.ub "load at type but the data in memory violates the language invariant" = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree nestedTupleOps (nestedArgs 3)) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < 3 ∧ Interp.steps k nestedTupleCopyUninitUbMInit = .ok mRet ∧
      ReturnRel nestedTupleOps ctxNested5 s' v mRet ∧
      ReachesRet (mirCallTree nestedTupleOps (nestedArgs 3)) tr (.normal (v, mem))) :=
  mirCall_steps_error nestedTupleOps_inFragment nestedTupleOps_translate ctxNested5
    (ctxNested5_ok rfl rfl) (nestedArgs 3) (by decide)
    nestedTupleCopyUninitUbMInit rfl rfl rfl nestedTupleCopyUninitUb_minirust_direct

def unsizedSliceTupleTy : Gen.Type :=
  .Tuple [(⟨0⟩, .Int u8)]
    { «end» := ⟨1⟩, align := ⟨4⟩, packed_align := none }
    (some (.Slice (.Int u32)))

/-- Ground-truth representation, layout, and place-evaluation edge cases for
`Type::Tuple`, `TupleHeadLayout`, and `PlaceExpr::Field`:
- zero-sized `()` layout, `encode`, `decode`, and `checkValue`;
- `TupleHeadLayout` (`capped_tail_align` with `packed_align = none` and
  `packed_align = some ⟨2⟩`, `tail_offset`, and `full_size_and_align`) and
  unsized `Type::Tuple` with a `Type::Slice` tail (`Type.layout`, `computeSize`,
  `computeAlign`);
- `Type.encode` and `Type.decode` on padded `(u8, u32)` preserving `.Uninit`
  padding bytes at `1..4`, ignoring arbitrary padding bytes on decode,
  returning `none` when a field byte is `.Uninit`, and panicking on unsized
  fields, length mismatches, or non-Tuple values;
- `checkValue` on `Type::Tuple` panicking on unsized fields and raising UB on
  field-count mismatch or invalid field values;
- `PlaceExpr::Field` out-of-bounds field indices (`-1`, `2`, and `3` on a
  2-field tuple) and non-tuple root raising `.specPanic`. -/
theorem tuple_encode_decode_place_edge_cases :
    Type.layout unitMiniRustTy = .ok (.Sized ⟨0⟩ ⟨1⟩) ∧
    Type.encode unitMiniRustTy (.Tuple []) = .ok [] ∧
    Type.decode unitMiniRustTy [] = .ok (some (.Tuple [])) ∧
    checkValue (.Tuple []) unitMiniRustTy = .ok () ∧
    TupleHeadLayout.capped_tail_align { «end» := ⟨1⟩, align := ⟨4⟩, packed_align := none } ⟨4⟩ = ⟨4⟩ ∧
    TupleHeadLayout.capped_tail_align { «end» := ⟨1⟩, align := ⟨2⟩, packed_align := some ⟨2⟩ } ⟨4⟩ = ⟨2⟩ ∧
    TupleHeadLayout.tail_offset { «end» := ⟨1⟩, align := ⟨4⟩, packed_align := none } ⟨4⟩ = ⟨4⟩ ∧
    TupleHeadLayout.full_size_and_align { «end» := ⟨1⟩, align := ⟨4⟩, packed_align := none } ⟨6⟩ ⟨2⟩ =
      (⟨8⟩, ⟨4⟩) ∧
    Type.layout unsizedSliceTupleTy =
      .ok (.Tuple { «end» := ⟨1⟩, align := ⟨4⟩, packed_align := none } (.Slice ⟨4⟩ ⟨4⟩)) ∧
    (Type.layout unsizedSliceTupleTy >>= fun l =>
      computeSize nestedTupleOkMInit l (some (.ElementCount 3))) =
      .ok ⟨16⟩ ∧
    (Type.layout unsizedSliceTupleTy >>= fun l =>
      computeAlign nestedTupleOkMInit l (some (.ElementCount 3))) =
      .ok ⟨4⟩ ∧
    Type.encode innerMiniRustTy (.Tuple [.Int 7, .Int 0x04030201]) =
      .ok [.Init 7 none, .Uninit, .Uninit, .Uninit,
           .Init 1 none, .Init 2 none, .Init 3 none, .Init 4 none] ∧
    Type.decode innerMiniRustTy
      [.Init 7 none, .Init 99 none, .Uninit, .Init 88 none,
       .Init 1 none, .Init 2 none, .Init 3 none, .Init 4 none] =
      .ok (some (.Tuple [.Int 7, .Int 0x04030201])) ∧
    Type.decode innerMiniRustTy
      [.Init 7 none, .Uninit, .Uninit, .Uninit,
       .Init 1 none, .Uninit, .Init 3 none, .Init 4 none] =
      .ok none ∧
    Type.encode unsizedSliceTupleTy (.Tuple [.Int 7]) =
      .error (.specPanic "encode of Type::Tuple with unsized field") ∧
    Type.encode innerMiniRustTy (.Tuple [.Int 7]) =
      .error (.specPanic "assertion failed: values.len() == sized_fields.len()") ∧
    Type.encode innerMiniRustTy (.Int 7) =
      .error (.specPanic "encode: Type::Tuple with a non-Tuple value") ∧
    Type.decode unsizedSliceTupleTy [.Init 7 none] =
      .error (.specPanic "decode of Type::Tuple with unsized field") ∧
    Type.decode innerMiniRustTy [.Init 7 none] =
      .error (.specPanic "decode of Type::Tuple with invalid length") ∧
    checkValue (.Tuple [.Int 7]) unsizedSliceTupleTy =
      .error (.specPanic "Value: unsized structs cannot be represented as values") ∧
    checkValue (.Tuple [.Int 7]) innerMiniRustTy =
      .error (.ub "Value::Tuple: invalid number of fields") ∧
    checkValue (.Tuple [.Int 300, .Int 0]) innerMiniRustTy =
      .error (.ub "Value::Int: invalid integer value") ∧
    Interp.evalPlace nestedTupleOkMInit (.Field (.Local (localName 2)) (-1)) =
      .error (.specPanic "field projection to invalid field") ∧
    Interp.evalPlace nestedTupleOkMInit (.Field (.Local (localName 2)) 2) =
      .error (.specPanic "field projection to non-existing unsized tail") ∧
    Interp.evalPlace nestedTupleOkMInit (.Field (.Local (localName 2)) 3) =
      .error (.specPanic "field projection to invalid field") ∧
    Interp.evalPlace nestedTupleOkMInit (.Field (.Local (localName 0)) 0) =
      .error (.specPanic "field projection on non-projectable type") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `Rvalue::Discriminant` of an `Ordering` temporary in a `SwitchInt` body -/

/-- MIR (`Runtime(PostCleanup)`) of
```rust
fn cmp_discr_switch(x: i8, y: i8, _b: bool) -> i8 {
    let o = x.cmp(&y);                 // StorageLive(_4); _4 = Cmp(copy _1, copy _2)
    let d = discriminant(o) as i8;     // StorageLive(_5); _5 = discriminant(_4); StorageDead(_4)
    match d {                          // switchInt(copy _5) -> [255: bb1, 0: bb2, otherwise: bb3]
        -1 => -10,                     // bb1: _0 = const -10_i8; return
        0 => 0,                        // bb2: _0 = const 0_i8; return
        _ => d,                        // bb3: _0 = copy _5; return
    }
}
```
whose `_5 = discriminant(_4)` reads the `i8` tag of the `core::cmp::Ordering`
temporary `_4` (`Rvalue::Discriminant`, lowered by `orderingDiscrExpr` to
`transmute::<i8>(load _4)`), after which `_4` is dead and the `SwitchInt` on
`_5` dispatches on the tag. -/
def cmpDiscrSwitch : CapturedMir where
  defPath := "witness::cmp_discr_switch"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [i8Decl, i8Decl, i8Decl, boolDecl, orderingDecl, i8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.binaryOp .cmp (.copy (local_ 1)) (.copy (local_ 2)))),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.discriminant (local_ 4))),
        mkStmt (.storageDead 4)],
      terminator := mkTerm (.switchInt (.copy (local_ 5))
        { branches := [(255, 1), (0, 2)], otherwise := 3 }),
      isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (constI8 246)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [mkStmt (.assign (local_ 0) (.use (constI8 0)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 5)))),
        mkStmt (.storageDead 5)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiCmpSel
  layouts := emptyLayoutTable
  allocations := []

theorem cmpDiscrSwitch_inFragment : inFragment cmpDiscrSwitch = true := by decide

/-- The `Discriminant` statement is a fragment statement precisely through the
`Rvalue::Discriminant` case of `rvalueOk` (an `i8` destination and an
`Ordering` local without a layout entry). -/
theorem cmpDiscrSwitch_discriminant_statementOk :
    statementOk cmpDiscrSwitch.localDecls (mkStmt (.assign (local_ 5) (.discriminant (local_ 4))))
        cmpDiscrSwitch.layouts = true ∧
      rvalueOk cmpDiscrSwitch.layouts cmpDiscrSwitch.localDecls IntType.I8
        (.discriminant (local_ 4)) = true ∧
      rvalueOk cmpDiscrSwitch.layouts cmpDiscrSwitch.localDecls u8
        (.discriminant (local_ 4)) = false ∧
      rvalueOk cmpDiscrSwitch.layouts cmpDiscrSwitch.localDecls IntType.I8
        (.discriminant (local_ 5)) = false := by
  decide

/-- **`Rvalue::Discriminant` is admitted only on unprojected `Ordering` locals
(`rvalueOk_discriminant_nonOrdering`, `rvalueOk_discriminant_proj`)**: MiniRust's
`ValueExpr::GetDiscriminant` is well-formed only at `Type::Enum`
(`spec/lang/well-formed.md`), and `core::cmp::Ordering` is the fragment's only enum. So the
discriminant of a unit, scalar, tuple, or array local (which Anneal's `evalPlaceDiscriminant`
evaluates to `0`) has no well-formed MiniRust counterpart and stays outside the fragment, as
does every projected discriminant place. -/
theorem rvalueOk_discriminant_nonOrdering (layouts : LayoutTable) (decls : List LocalDecl)
    (it : Gen.IntType) {j : Nat} {d : LocalDecl} (hd : decls[j]? = some d)
    (hno : isOrderingTy d.ty = false) :
    rvalueOk layouts decls it (.discriminant ⟨j, []⟩) = false := by
  simp [rvalueOk, hd, hno]

/-- See `rvalueOk_discriminant_nonOrdering`. -/
theorem rvalueOk_discriminant_proj (layouts : LayoutTable) (decls : List LocalDecl)
    (it : Gen.IntType) (j : Nat) (pe : ProjectionElem) (rest : List ProjectionElem) :
    rvalueOk layouts decls it (.discriminant ⟨j, pe :: rest⟩) = false := by
  simp [rvalueOk]

/-- The MiniRust function `minimize` produces for `cmpDiscrSwitch`, spelled
out, with `Rvalue::Discriminant` lowered to `transmute::<i8>` of the load of the
`Ordering` local (`orderingDiscrExpr`). -/
def cmpDiscrSwitchFn : Gen.Function where
  locals := ⟨[(localName 0, .Int i8), (localName 1, .Int i8), (localName 2, .Int i8),
    (localName 3, .Bool), (localName 4, orderingTy), (localName 5, .Int i8)]⟩
  args := [localName 1, localName 2, localName 3]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 4),
      .Assign (.Local (localName 4))
        (translateCmp (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
      .StorageLive (localName 5),
      .Assign (.Local (localName 5)) (orderingDiscrExpr (.Load (.Local (localName 4)))),
      .StorageDead (localName 4)],
      .Switch (.Load (.Local (localName 5))) ⟨[(-1, bbName 1), (0, bbName 2)]⟩ (bbName 3),
      .Regular⟩),
    (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int (-10)) (.Int i8))],
      .Return, .Regular⟩),
    (bbName 2, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 0) (.Int i8))],
      .Return, .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 0)) (.Load (.Local (localName 5))),
      .StorageDead (localName 5)],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem cmpDiscrSwitch_translate : translateFn cmpDiscrSwitch = some cmpDiscrSwitchFn := rfl

theorem ctxI8_ok_cmpDiscrSwitch : CtxOk cmpDiscrSwitch ctxI8_4 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    match i, hi, hd with
    | 0, _, hd => simp [cmpDiscrSwitch] at hd; subst hd; decide
    | 1, _, hd => simp [cmpDiscrSwitch] at hd; subst hd; decide
    | 2, _, hd => simp [cmpDiscrSwitch] at hd; subst hd; decide
    | 3, _, hd => simp [cmpDiscrSwitch] at hd; subst hd; decide
    | _ + 4, hi, _ => simp [cmpDiscrSwitch] at hi
  ret := by
    intro d hd; simp [cmpDiscrSwitch] at hd; subst hd
    exact ⟨0, retAllocI8, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- Input `(x, y) = (-1, 1)`: `(-1).cmp(&1)` is `Less`, whose discriminant is
the `i8` `-1` (byte `255`), so the `SwitchInt` (which emits the event `255`,
the discriminant's bit pattern) takes `bb1` and returns `-10` (byte `246`). -/
def cmpDiscrLessArgs : List Value := [.scalar ⟨255, 1⟩, .scalar ⟨1, 1⟩, .scalar ⟨0, 1⟩]
def cmpDiscrLessS0 : MachineState := initMachineState cmpDiscrSwitch cmpDiscrLessArgs
def cmpDiscrLessMInit : Mach :=
  machineWithCtx ctxI8_4 cmpDiscrSwitch cmpDiscrSwitchFn cmpDiscrLessS0.frame.locals
    cmpDiscrSwitchFn.start

theorem cmpDiscrLess_anneal_ret :
    ReachesRet (mirCallTree cmpDiscrSwitch cmpDiscrLessArgs) [⟨.inr (.inl (.emit (.event 255))), PUnit.unit⟩]
      (.normal (.scalar ⟨246, 1⟩, cmpDiscrLessS0.memory)) :=
  runA_sound cmpDiscrSwitch 20 _ _ _ rfl

theorem cmpDiscrLess_noUB : MirNoUBTree (mirCallTree cmpDiscrSwitch cmpDiscrLessArgs) :=
  runA_noUB cmpDiscrSwitch 20 _ _ _ rfl

/-- End to end, through the correspondence theorem (`mirCall_ret`): MiniRust
returns the byte `246` as well. -/
theorem cmpDiscrLess_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n cmpDiscrLessMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAllocI8 with data := scalarBytes u8 246 } ∧
      m'.threads = [thread1 ctxI8_4 [{ callerFrameI8 with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret cmpDiscrSwitch_inFragment cmpDiscrSwitch_translate ctxI8_4 ctxI8_ok_cmpDiscrSwitch
      cmpDiscrLessArgs (by decide) cmpDiscrLessMInit rfl rfl rfl cmpDiscrLess_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [cmpDiscrSwitch] at hd; subst hd
  simp [retPtr, ctxI8_4] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxI8_4] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

set_option maxRecDepth 8192 in
/-- Direct computation of the same MiniRust run (the init block's `Goto`, the
five statements of `bb0`, the `Switch`, `bb1`'s assignment, and `Return`). -/
theorem cmpDiscrLess_minirust_direct :
    (Interp.steps 9 cmpDiscrLessMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 246 }, [1]) := rfl

/-- Input `(7, 7)`: `Equal`, discriminant `0`, `bb2`, returns `0`. -/
def cmpDiscrEqualArgs : List Value := [.scalar ⟨7, 1⟩, .scalar ⟨7, 1⟩, .scalar ⟨1, 1⟩]
def cmpDiscrEqualS0 : MachineState := initMachineState cmpDiscrSwitch cmpDiscrEqualArgs

theorem cmpDiscrEqual_anneal_ret :
    ReachesRet (mirCallTree cmpDiscrSwitch cmpDiscrEqualArgs) [⟨.inr (.inl (.emit (.event 0))), PUnit.unit⟩]
      (.normal (.scalar ⟨0, 1⟩, cmpDiscrEqualS0.memory)) :=
  runA_sound cmpDiscrSwitch 20 _ _ _ rfl

/-- Input `(2, 1)`: `Greater`, discriminant `1`, the `otherwise` block `bb3`
returns the discriminant itself. -/
def cmpDiscrGreaterArgs : List Value := [.scalar ⟨2, 1⟩, .scalar ⟨1, 1⟩, .scalar ⟨0, 1⟩]
def cmpDiscrGreaterS0 : MachineState := initMachineState cmpDiscrSwitch cmpDiscrGreaterArgs

theorem cmpDiscrGreater_anneal_ret :
    ReachesRet (mirCallTree cmpDiscrSwitch cmpDiscrGreaterArgs) [⟨.inr (.inl (.emit (.event 1))), PUnit.unit⟩]
      (.normal (.scalar ⟨1, 1⟩, cmpDiscrGreaterS0.memory)) :=
  runA_sound cmpDiscrSwitch 20 _ _ _ rfl

def cmpDiscrGreaterMInit : Mach :=
  machineWithCtx ctxI8_4 cmpDiscrSwitch cmpDiscrSwitchFn cmpDiscrGreaterS0.frame.locals
    cmpDiscrSwitchFn.start

set_option maxRecDepth 8192 in
/-- MiniRust returns the discriminant `1` (byte `1`) through the `otherwise`
block, which reads `_5` after the `Ordering` temporary `_4` is dead. -/
theorem cmpDiscrGreater_minirust_direct :
    (Interp.steps 10 cmpDiscrGreaterMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAllocI8 with data := scalarBytes u8 1 }, [1]) := rfl

/-! ## Projected `Deinit` and `Retag` outside the fragment (kernel-checked witnesses)

`statementOk` admits `Deinit` and `Retag` only on unprojected locals
(`statementOk_deinit_proj`, `statementOk_retag_proj`). The two witnesses below
compute, inside the kernel, how each projected form behaves in Anneal's MIR
semantics and in MiniRust on a fragment `Padded(u8, u32, u16)` argument:

* `Deinit(_1.1)` diverges: Anneal only checks that `_1` is initialized and
  `_1.1` readable and keeps the slot, so a later read of `_1.1` returns the old
  field, whereas MiniRust's `Statement::Deinit` writes `Uninit` over bytes
  `4..8` and the later read is UB.
* `Retag(_1.1)` agrees under Stage-1 Trusted: Stage-1 Trusted's `Retag` of a
  place whose type is known and is neither a reference nor a raw pointer is a
  no-op step (`evalStmt_retag_scalar_noop`; only a place of unknown type still
  requires a pointer, `evalStmt_retag_scalar_ub`), and MiniRust's
  `Statement::Validate` loads the `u32`, retags it as the identity (`retag_val`
  on `Value::Int`), and stores it back, so both return `99`
  (`paddedRetagRead_stage1_parity`). `inFragmentD` (`DeinitWindow.lean`) admits
  projected `Retag` on `TupleSpec` scalar fields both in hole-free states
  (`paddedRetagRead_inFragmentD`, `paddedRetagRead_minirust_ret_from_start`) and
  on disjoint sibling fields while a `Deinit` hole is open
  (`paddedDeinitSiblingRetagReinit_minirust_ret_from_start`), while rejecting
  any projected `Retag` overlapping an open `Deinit` hole
  (`paddedDeinitRetagHole_not_inFragmentD`, `paddedDeinitRetagHole_diverges`). -/

/-- `statementOk` rejects every projected `Deinit`. -/
theorem statementOk_deinit_proj (decls : List LocalDecl) (i : Nat) (pe : ProjectionElem)
    (rest : List ProjectionElem) (span : String) (layouts : LayoutTable) :
    statementOk decls ⟨.deinit ⟨i, pe :: rest⟩, span⟩ layouts = false := rfl

/-- `statementOk` rejects every projected `Retag`. -/
theorem statementOk_retag_proj (decls : List LocalDecl) (kind : RetagKind) (i : Nat)
    (pe : ProjectionElem) (rest : List ProjectionElem) (span : String) (layouts : LayoutTable) :
    statementOk decls ⟨.retag kind ⟨i, pe :: rest⟩, span⟩ layouts = false := rfl

/-- Stage-1 Anneal's `Retag` of a place of unknown type (`placeTy = none`, e.g.
an undeclared local) that evaluates to a scalar faults: without a type, Stage-1
Trusted requires the retagged value to be a pointer. On typed non-pointer places
the retag is a no-op (`evalStmt_retag_scalar_noop`). -/
theorem evalStmt_retag_scalar_ub (s : MachineState) (decls : List LocalDecl)
    (layouts : LayoutTable) (k : RetagKind) (place : Place) (span : String)
    (sc : ScalarInt) (L : List LocalSlot)
    (h : evalOperand s.frame.locals (.copy place) s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals decls = .ok (.scalar sc) L)
    (hUntyped : placeTy decls layouts place = none) :
    evalStmt s ⟨.retag k place, span⟩ decls layouts = MirStepNode.fail .ub := by
  simp [evalStmt, h, hUntyped]

/-- **Stage-1 scalar `Retag` is a no-op (`evalStmt_retag_scalar_noop`)**: Stage-1
Anneal's `Retag` (of any kind) of a place whose type is known and is neither a
reference nor a raw pointer — every projected place of the fragment holds such a
scalar: a tuple/struct or `(Int, bool)` scalar field, an array element, or an
integer pointee `*_p` — that evaluates to a scalar steps to the next statement
with the frame its read leaves and the memory unchanged, exactly as MiniRust's
`Statement::Validate` of an integer place stores back the integer it loaded
(`retagVal_int_id`). -/
theorem evalStmt_retag_scalar_noop (s : MachineState) (decls : List LocalDecl)
    (layouts : LayoutTable) (k : RetagKind) (place : Place) (span : String)
    (sc : ScalarInt) (L : List LocalSlot) {ty : Ty}
    (h : evalOperand s.frame.locals (.copy place) s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals decls = .ok (.scalar sc) L)
    (hTy : placeTy decls layouts place = some ty)
    (hNotPtr : ∀ m inner, ty.kind ≠ .ref m inner ∧ ty.kind ≠ .rawPtr m inner) :
    evalStmt s ⟨.retag k place, span⟩ decls layouts = MirStepNode.step (advanceStmt s L) := by
  simp only [evalStmt, h]
  split
  · rename_i m inner l heq
    rw [hTy] at heq; cases heq; exact absurd rfl (hNotPtr m inner).2
  · rename_i m pointee l heq
    rw [hTy] at heq; cases heq; exact absurd rfl (hNotPtr m pointee).1
  · rename_i heq; rw [hTy] at heq; nomatch heq
  · rfl

/-- Anneal's `Deinit` of a projected place whose root is initialized and whose
projected value is readable keeps every slot (it steps to the next statement
with the same `locals`), whereas MiniRust's `Statement::Deinit` overwrites the
projected bytes with `Uninit` (`paddedDeinitRead_minirust_ub`). -/
theorem evalStmt_deinit_proj_keeps (s : MachineState) (decls : List LocalDecl)
    (layouts : LayoutTable) (i : Nat) (pe : ProjectionElem) (rest : List ProjectionElem)
    (span : String) (rootVal v : Value)
    (hs : s.frame.locals[i]? = some (.init rootVal))
    (hr : readProjectedValue s.frame.locals rootVal (pe :: rest) = .ok v) :
    evalStmt s ⟨.deinit ⟨i, pe :: rest⟩, span⟩ decls layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) := by
  simp [evalStmt, Trusted.Sequence.get?, hs, hr]

/-- The ABI of a function with one `Padded(u8, u32, u16)` argument returning
`u32`. -/
def fnAbiPaddedOne : FnAbi :=
  { args := [{ layout := paddedStructLayout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- The callee's `_0: u32` and `_1: Padded` live at addresses `128` and `256`. -/
def ctxPadded2 : Ctx :=
  { caller := callerFrame, payloads := [], base := [retAlloc], addrs := [128, 256],
    nextBlock := bbName 7, unwindBlock := none, retPtr := retPtr }

/-- MIR of
```rust
fn padded_deinit_read(mut s: Padded) -> u32 {
    Deinit(s.1);   // bb0: Deinit(_1.1)
    s.1            //      _0 = copy _1.1; return
}
``` -/
def paddedDeinitRead : CapturedMir where
  defPath := "witness::padded_deinit_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)]))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

/-- `paddedDeinitRead` without its projected `Deinit`. -/
def paddedReadOnly : CapturedMir where
  defPath := "witness::padded_deinit_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)]))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

/-- The fragment rejects the body because of (and only because of) its
projected `Deinit`: the body without it is in the fragment. -/
theorem paddedDeinitRead_not_inFragment :
    inFragment paddedDeinitRead = false ∧
      statementOk paddedDeinitRead.localDecls (mkStmt (.deinit (placeField 1 [(1, u32Ty)])))
        paddedDeinitRead.layouts = false ∧
      inFragment paddedReadOnly = true := by
  decide

/-- `minimize`'s translation, which `translateFn` still produces: the
projected `Deinit` becomes MiniRust's `Statement::Deinit` of the field place. -/
def paddedDeinitReadFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Deinit (.Field (.Local (localName 1)) 1),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem paddedDeinitRead_translate :
    translateFn paddedDeinitRead = some paddedDeinitReadFn := rfl

def paddedDeinitReadArgs : List Value := [initPaddedStruct]
def paddedDeinitReadS0 : MachineState := initMachineState paddedDeinitRead paddedDeinitReadArgs
def paddedDeinitReadMInit : Mach :=
  machineWithCtx ctxPadded2 paddedDeinitRead paddedDeinitReadFn paddedDeinitReadS0.frame.locals
    paddedDeinitReadFn.start

/-- Anneal's projected `Deinit` keeps `_1` initialized: the function returns
the old field `99` (computed by the kernel). -/
theorem paddedDeinitRead_anneal_ret :
    ReachesRet (mirCallTree paddedDeinitRead paddedDeinitReadArgs) []
      (.normal (.scalar ⟨99, 4⟩, paddedDeinitReadS0.memory)) :=
  runA_sound paddedDeinitRead 10 _ _ _ rfl

/-- MiniRust's `Deinit(_1.1)` overwrites exactly bytes `4..8` of `_1` with
`Uninit` (keeping field `0`, field `2`, and the padding), and the following
load of `_1.1` is UB (computed by the kernel). -/
theorem paddedDeinitRead_minirust_ub :
    ((Interp.steps 2 paddedDeinitReadMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[2]?).map (·.data))) =
      some [.Init 7 none, .Uninit, .Uninit, .Uninit,
            .Uninit, .Uninit, .Uninit, .Uninit,
            .Init 5 none, .Init 6 none, .Uninit, .Uninit] ∧
    ∃ msg, Interp.steps 3 paddedDeinitReadMInit = .error (.ub msg) :=
  ⟨rfl, _, rfl⟩

/-- MIR of
```rust
fn padded_retag_read(mut s: Padded) -> u32 {
    Retag(s.1);    // bb0: Retag(_1.1)
    s.1            //      _0 = copy _1.1; return
}
``` -/
def paddedRetagRead : CapturedMir where
  defPath := "witness::padded_retag_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.retag .default (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)]))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

theorem paddedRetagRead_not_inFragment :
    inFragment paddedRetagRead = false ∧
      statementOk paddedRetagRead.localDecls (mkStmt (.retag .default (placeField 1 [(1, u32Ty)])))
        paddedRetagRead.layouts = false := by
  decide

def paddedRetagReadFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Validate (.Field (.Local (localName 1)) 1) false,
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem paddedRetagRead_translate :
    translateFn paddedRetagRead = some paddedRetagReadFn := rfl

def paddedRetagReadS0 : MachineState := initMachineState paddedRetagRead paddedDeinitReadArgs
def paddedRetagReadMInit : Mach :=
  machineWithCtx ctxPadded2 paddedRetagRead paddedRetagReadFn paddedRetagReadS0.frame.locals
    paddedRetagReadFn.start

/-- Stage-1 Anneal's `Retag(_1.1)` of the `u32` field of the initial state is a
no-op step: the field reads `99` and its declared type `u32` is neither a
reference nor a raw pointer (`evalStmt_retag_scalar_noop`). -/
theorem paddedRetagRead_retag_noop :
    evalStmt paddedRetagReadS0 (mkStmt (.retag .default (placeField 1 [(1, u32Ty)])))
        paddedRetagRead.localDecls paddedRetagRead.layouts =
      MirStepNode.step (advanceStmt paddedRetagReadS0 paddedRetagReadS0.frame.locals) :=
  evalStmt_retag_scalar_noop _ _ _ _ _ _ ⟨99, 4⟩ _ (ty := u32Ty) rfl rfl
    (fun m inner => ⟨fun h => (by cases h), fun h => (by cases h)⟩)

/-- **Stage-1 Anneal's `Retag(_1.1)` is a no-op (`paddedRetagRead_anneal_noop`)**:
the function returns the field `99` (computed by the kernel). -/
theorem paddedRetagRead_anneal_noop :
    ReachesRet (mirCallTree paddedRetagRead paddedDeinitReadArgs) []
      (.normal (.scalar ⟨99, 4⟩, paddedRetagReadS0.memory)) :=
  runA_sound paddedRetagRead 10 _ _ _ rfl

/-- MiniRust's `retag_val` is the identity on `Value::Int`
("(Value::Int(..) | Value::Bool(..) | Value::Union(..), _) => val"), so
`Statement::Validate` of an integer place stores back the integer it loaded. -/
theorem retagVal_int_id (m : Mach) (fnEntry : Bool) (i : Int) (ty : Gen.Type) :
    retagVal m fnEntry (.Int i) ty = .ok (.Int i) := by
  simp [retagVal]

/-- After `4` MiniRust steps of `paddedRetagReadFn` (the init block's `Goto`,
`Validate(_1.1)`, the load of `_1.1`, and `Return`), the callee frame is
popped and the caller's return place holds `99`. -/
def paddedRetagReadMiniRustRet : Bool :=
  match Interp.steps 4 paddedRetagReadMInit with
  | .ok m => m.threads.map (·.stack.length) == [1] &&
      (m.mem.memory.allocations[0]?.map (·.data)) == some (scalarBytes u32 99)
  | .error _ => false

/-- MiniRust's `Validate(_1.1)` succeeds and the function returns `99`
(computed by the kernel; `Validate` goes through `retagVal`, which the
elaborator does not unfold, so the check runs in the kernel). -/
theorem paddedRetagRead_minirust_ret : paddedRetagReadMiniRustRet = true := by
  decide +kernel

/-- **Stage-1 `paddedRetagRead` parity (`paddedRetagRead_stage1_parity`)**: Stage-1
Anneal and MiniRust agree on the projected `Retag(_1.1)` of a `u32` field — both
return `99` (`paddedRetagRead_anneal_noop`, `paddedRetagRead_minirust_ret`). -/
theorem paddedRetagRead_stage1_parity :
    ReachesRet (mirCallTree paddedRetagRead paddedDeinitReadArgs) []
        (.normal (.scalar ⟨99, 4⟩, paddedRetagReadS0.memory)) ∧
      paddedRetagReadMiniRustRet = true :=
  ⟨paddedRetagRead_anneal_noop, paddedRetagRead_minirust_ret⟩

/-! ### Projected `Deinit`, sibling read, and re-initialization (`paddedDeinitSiblingReinit`)

When a projected `Deinit(_1.1)` on `Padded(u8, u32, u16)` is followed by reading
the unaffected sibling field `_1.0`, re-initializing `_1.1 = _2 + 35`, and then
reading `_1.1`, Anneal and MiniRust agree on every step and both return `42`:
* After `Deinit(_1.1)` (`steps 2`), bytes `4..8` of `_1` are `Uninit` while
  sibling fields `_1.0` (`7`) and `_1.2` (`0x0605`) are preserved;
* Reading sibling `_1.0` (`steps 3`) loads `7` without touching the `Uninit`
  hole in `_1.1`;
* Writing `_1.1 = 7 + 35` (`steps 4`) refills bytes `4..8` with `scalarBytes u32 42`;
* Reading `_0 = copy _1.1` and returning (`steps 6`) returns `42` in both
  Anneal (`paddedDeinitSiblingReinit_anneal_ret`) and MiniRust
  (`paddedDeinitSiblingReinit_minirust_ret`). -/

/-- MIR of
```rust
fn padded_deinit_sibling_reinit(mut s: Padded) -> u32 {
    Deinit(s.1);
    let a = s.0 as u32;
    s.1 = a + 35;
    s.1
}
``` -/
def paddedDeinitSiblingReinit : CapturedMir where
  defPath := "witness::padded_deinit_sibling_reinit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (local_ 2) (.cast .intToInt (.copy (placeField 1 [(0, u8TyW)])) u32Ty)),
        mkStmt (.assign (placeField 1 [(1, u32Ty)])
          (.binaryOp .add (.copy (local_ 2)) (constU32 35))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)])))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

theorem paddedDeinitSiblingReinit_not_inFragment :
    inFragment paddedDeinitSiblingReinit = false := by decide

def paddedDeinitSiblingReinitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy), (localName 2, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Deinit (.Field (.Local (localName 1)) 1),
      .Assign (.Local (localName 2))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Field (.Local (localName 1)) 0))),
      .Assign (.Field (.Local (localName 1)) 1)
        (.BinOp (.Int .Add) (.Load (.Local (localName 2)))
          (.Constant (.Int 35) (.Int u32))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1)),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem paddedDeinitSiblingReinit_translate :
    translateFn paddedDeinitSiblingReinit = some paddedDeinitSiblingReinitFn := rfl

def paddedDeinitSiblingReinitS0 : MachineState :=
  initMachineState paddedDeinitSiblingReinit paddedDeinitReadArgs

def paddedDeinitSiblingReinitMInit : Mach :=
  machineWithCtx ctxPadded3 paddedDeinitSiblingReinit paddedDeinitSiblingReinitFn
    paddedDeinitSiblingReinitS0.frame.locals paddedDeinitSiblingReinitFn.start

/-- Anneal evaluates `paddedDeinitSiblingReinit` to `.scalar ⟨42, 4⟩`. -/
theorem paddedDeinitSiblingReinit_anneal_ret :
    ReachesRet (mirCallTree paddedDeinitSiblingReinit paddedDeinitReadArgs) []
      (.normal (.scalar ⟨42, 4⟩, paddedDeinitSiblingReinitS0.memory)) :=
  runA_sound paddedDeinitSiblingReinit 12 _ _ _ rfl

/-- Anneal evaluation of `paddedDeinitSiblingReinit` has no UB. -/
theorem paddedDeinitSiblingReinit_noUB :
    MirNoUBTree (mirCallTree paddedDeinitSiblingReinit paddedDeinitReadArgs) :=
  runA_noUB paddedDeinitSiblingReinit 12 _ _ _ rfl

/-- In MiniRust:
1. After `Deinit(_1.1)` (`steps 3`), bytes `4..8` of `_1` are `Uninit` while
   sibling fields `_1.0` (`7`) and `_1.2` (`[5, 6]`) remain initialized;
2. Reading sibling `_1.0` (`steps 4`) stores `7` into `_2`;
3. Re-initializing `_1.1 = _2 + 35` (`steps 5`) writes `scalarBytes u32 42` into
   bytes `4..8` of `_1`;
4. After `Return` (`steps 8`), the callee frame is popped and the caller's
   return allocation holds `scalarBytes u32 42`. -/
theorem paddedDeinitSiblingReinit_minirust_ret :
    ((Interp.steps 3 paddedDeinitSiblingReinitMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[2]?).map (·.data))) =
      some [.Init 7 none, .Uninit, .Uninit, .Uninit,
            .Uninit, .Uninit, .Uninit, .Uninit,
            .Init 5 none, .Init 6 none, .Uninit, .Uninit] ∧
    ((Interp.steps 4 paddedDeinitSiblingReinitMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[3]?).map (·.data))) =
      some (scalarBytes u32 7) ∧
    ((Interp.steps 5 paddedDeinitSiblingReinitMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[2]?).map (·.data))) =
      some [.Init 7 none, .Uninit, .Uninit, .Uninit,
            .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none,
            .Init 5 none, .Init 6 none, .Uninit, .Uninit] ∧
    ((Interp.steps 8 paddedDeinitSiblingReinitMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[0]?).map (·.data))) =
      some (scalarBytes u32 42) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Witness #1: `Deinit(_1.1)`, a disjoint sibling read, and re-initialization by a constant

On `Padded(u8, u32, u16)` (`u8` at `0`, `u32` at `4..8`, `u16` at `8..10`, size `12`):
`Deinit(_1.1)` opens the hole `(1, [.field 1 u32])` (bytes `4..8`); while it is open the body
reads the disjoint sibling `_1.0` (byte `0`) into the `u8` temporary `_2`, then closes the hole
with `_1.1 = const 42_u32` (same byte range, scalar leaf) and reads `_1.1`. `inFragmentD`
admits the body (`deinitSiblingReinit_inFragmentD`), the old `inFragment` rejects it
(`deinitSiblingReinit_not_inFragment`), Anneal returns `42`
(`deinitSiblingReinit_anneal_ret`), and running MiniRust directly from `f.start` returns `42`
too, with bytes `4..8` of `_1` `Uninit` right after the `Deinit` while byte `0` keeps
field `0` (`deinitSiblingReinit_minirust_direct`, `deinitSiblingReinit_minirust_ret_direct`). -/

/-- MIR of
```rust
fn deinit_sibling_reinit(mut s: Padded) -> u32 {
    let t: u8;      // StorageLive(_2)
    Deinit(s.1);    // Deinit(_1.1)
    t = s.0;        // _2 = copy _1.0
    s.1 = 42;       // _1.1 = const 42_u32
    s.1             // _0 = copy _1.1; StorageDead(_2); return
}
``` -/
def deinitSiblingReinit : CapturedMir where
  defPath := "witness::deinit_sibling_reinit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl, u8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (local_ 2) (.use (.copy (placeField 1 [(0, u8TyW)])))),
        mkStmt (.assign (placeField 1 [(1, u32Ty)]) (.use (constU32 42))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)])))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

/-- The projected-`Deinit` fragment admits the body. -/
theorem deinitSiblingReinit_inFragmentD : inFragmentD deinitSiblingReinit = true := by decide

/-- The old fragment rejects the body (`statementOk_deinit_proj`). -/
theorem deinitSiblingReinit_not_inFragment : inFragment deinitSiblingReinit = false := by decide

/-- `minimize`'s translation: the projected `Deinit` becomes MiniRust's `Statement::Deinit`
of the field place. -/
def deinitSiblingReinitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy),
    (localName 2, .Int Witness.u8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Deinit (.Field (.Local (localName 1)) 1),
      .Assign (.Local (localName 2)) (.Load (.Field (.Local (localName 1)) 0)),
      .Assign (.Field (.Local (localName 1)) 1) (.Constant (.Int 42) (.Int u32)),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1)),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deinitSiblingReinit_translate :
    translateFn deinitSiblingReinit = some deinitSiblingReinitFn := rfl

/-- `ctxPadded2` (callee `_0: u32` at `128`, `_1: Padded` at `256`) is well formed for a
body whose locals are `_0: u32`, the argument `_1: Padded`, and a `u8` temporary `_2`
(temporaries get no caller address). -/
theorem ctxPadded2_ok_u8 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, paddedStructDecl, u8Decl])
    (hlay : body.layouts = paddedLayouts) (hac : body.argCount = 1) : CtxOk body ctxPadded2 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd; rw [h] at hd; rw [hlay]; rw [hac] at hi
    match i, hi, hd with
    | 0, _, hd => simp at hd; subst hd; decide
    | 1, _, hd => simp at hd; subst hd; decide
    | _ + 2, hi, _ => omega
  ret := by
    intro d hd; rw [h] at hd; rw [hlay]; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem deinitSiblingReinit_ctxOk : CtxOk deinitSiblingReinit ctxPadded2 :=
  ctxPadded2_ok_u8 rfl rfl rfl

def deinitSiblingReinitArgs : List Value := [initPaddedStruct]

theorem deinitSiblingReinit_argsOk : argsOk deinitSiblingReinit deinitSiblingReinitArgs = true := by
  decide

def deinitSiblingReinitS0 : MachineState :=
  initMachineState deinitSiblingReinit deinitSiblingReinitArgs

def deinitSiblingReinitMInit : Mach :=
  machineWithCtx ctxPadded2 deinitSiblingReinit deinitSiblingReinitFn
    deinitSiblingReinitS0.frame.locals deinitSiblingReinitFn.start

/-- `hthreads` of `mirCall_ret`. -/
theorem deinitSiblingReinitMInit_threads :
    deinitSiblingReinitMInit.threads =
      [thread1 ctxPadded2 [ctxPadded2.caller,
        { calleeFrame deinitSiblingReinitFn ctxPadded2 (deinitSiblingReinit.argCount + 1) 0 0 with
            next_block := deinitSiblingReinitFn.start }]] := rfl

/-- `hactive` of `mirCall_ret`. -/
theorem deinitSiblingReinitMInit_active : deinitSiblingReinitMInit.active_thread = 0 := rfl

/-- `hallocs` of `mirCall_ret`. -/
theorem deinitSiblingReinitMInit_allocs :
    deinitSiblingReinitMInit.mem.memory.allocations =
      ctxPadded2.base ++ localAllocs ctxPadded2
        (deinitSiblingReinit.localDecls.take (deinitSiblingReinit.argCount + 1))
        (initMachineState deinitSiblingReinit deinitSiblingReinitArgs).frame.locals
        deinitSiblingReinit.layouts := rfl

/-- Anneal returns `42` (computed by the kernel). -/
theorem deinitSiblingReinit_anneal_ret :
    ReachesRet (mirCallTree deinitSiblingReinit deinitSiblingReinitArgs) []
      (.normal (.scalar ⟨42, 4⟩, deinitSiblingReinitS0.memory)) :=
  runA_sound deinitSiblingReinit 12 _ _ _ rfl

/-- Anneal's execution has no UB. -/
theorem deinitSiblingReinit_anneal_noUB :
    MirNoUBTree (mirCallTree deinitSiblingReinit deinitSiblingReinitArgs) :=
  runA_noUB deinitSiblingReinit 12 _ _ _ rfl

/-- The erased body (projected `Deinit` replaced by `PlaceMention`) is in the old fragment
and Anneal returns the same `42` on it. -/
theorem deinitSiblingReinit_erased :
    inFragment (eraseDeinit deinitSiblingReinit) = true ∧
      ReachesRet (mirCallTree (eraseDeinit deinitSiblingReinit) deinitSiblingReinitArgs) []
        (.normal (.scalar ⟨42, 4⟩, deinitSiblingReinitS0.memory)) :=
  ⟨by decide, runA_sound (eraseDeinit deinitSiblingReinit) 12 _ _ _ rfl⟩

/-- Running MiniRust directly from `f.start` (computed by the kernel):
1. after `Deinit(_1.1)` (`steps 3`: init `Goto`, `StorageLive(_2)`, `Deinit`), bytes `4..8`
   of `_1` (allocation `2`) are `Uninit` while byte `0` keeps field `0` (`7`) and bytes
   `8..10` keep field `2` (`0x0605`);
2. the sibling read `_2 = copy _1.0` (`steps 4`) stores `7` into `_2` (allocation `3`);
3. `_1.1 = const 42_u32` (`steps 5`) refills bytes `4..8` with `scalarBytes u32 42`;
4. after `Return` (`steps 8`) the callee frame is popped and the caller's return place
   (allocation `0`) holds `scalarBytes u32 42`. -/
theorem deinitSiblingReinit_minirust_direct :
    ((Interp.steps 3 deinitSiblingReinitMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[2]?).map (·.data))) =
      some [.Init 7 none, .Uninit, .Uninit, .Uninit,
            .Uninit, .Uninit, .Uninit, .Uninit,
            .Init 5 none, .Init 6 none, .Uninit, .Uninit] ∧
    ((Interp.steps 4 deinitSiblingReinitMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[3]?).map (·.data))) =
      some [.Init 7 none] ∧
    ((Interp.steps 5 deinitSiblingReinitMInit).toOption.bind
      (fun m => (m.mem.memory.allocations[2]?).map (·.data))) =
      some [.Init 7 none, .Uninit, .Uninit, .Uninit,
            .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none,
            .Init 5 none, .Init 6 none, .Uninit, .Uninit] ∧
    ((Interp.steps 8 deinitSiblingReinitMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length)))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The shape `mirCall_ret` yields for this body, computed directly: after `8` MiniRust
steps the caller continues at `bbName 7` and its return place holds `42`. -/
theorem deinitSiblingReinit_minirust_ret_direct :
    ∃ m', Interp.steps 8 deinitSiblingReinitMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads =
        [thread1 ctxPadded2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] :=
  ⟨_, rfl, rfl, rfl⟩

/-- The hole `(1, [.field 1 u32])` is open exactly before statement `2` (the sibling read)
and statement `3` (the re-initialization), and closed before the terminator. -/
theorem deinitSiblingReinit_holeAt :
    (List.range 7).map (holeAt deinitSiblingReinit 0) =
      [none, none, some (1, [.field 1 u32Ty]), some (1, [.field 1 u32Ty]), none, none, none] :=
  rfl

/-- `ReturnRel` (the conclusion of `mirCall_ret`), computed directly: `8` MiniRust steps
from `f.start` perform the return of `42`. -/
theorem deinitSiblingReinit_minirust_returnRel :
    ∃ m', Interp.steps 8 deinitSiblingReinitMInit = .ok m' ∧
      ReturnRel deinitSiblingReinit ctxPadded2 deinitSiblingReinitS0 (.scalar ⟨42, 4⟩) m' := by
  refine ⟨_, rfl, 0, retAlloc, u32Decl, _, rfl, ⟨rfl, ?_⟩, rfl, rfl, rfl, rfl, ?_⟩
  · show (42 : Nat) < 2 ^ (8 * 4); decide
  · decide

/-- Negative control: reading the hole (`paddedDeinitRead`: `Deinit(_1.1); _0 = copy _1.1`,
where Anneal returns `99` and MiniRust is UB) is rejected by the window check alone. -/
theorem paddedDeinitRead_not_inFragmentD :
    inFragment (eraseDeinit paddedDeinitRead) = true ∧
      deinitWindowOk paddedDeinitRead = false ∧ inFragmentD paddedDeinitRead = false := by
  decide

/-- `ctxPadded2` (callee `_0: u32` at `128`, `_1: Padded` at `256`) is well formed for a 2-local
body with `[u32Decl, paddedStructDecl]`. -/
theorem ctxPadded2_ok_u32 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, paddedStructDecl])
    (hlay : body.layouts = paddedLayouts) (hac : body.argCount = 1) : CtxOk body ctxPadded2 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd; rw [h] at hd; rw [hlay]; rw [hac] at hi
    match i, hi, hd with
    | 0, _, hd => simp at hd; subst hd; decide
    | 1, _, hd => simp at hd; subst hd; decide
    | _ + 2, hi, _ => omega
  ret := by
    intro d hd; rw [h] at hd; rw [hlay]; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- **`paddedRetagRead` is admitted by `inFragmentD`**: `eraseDeinit` lowers projected `Retag(_1.1)`
to `PlaceMention(_1.1)`, `deinitWindowOk` checks `deinitTargetOk` on `_1.1` (`u32`, `4 > 0` bytes),
and Stage-1 Anneal's no-op (`evalStmt_retag_field`) matches MiniRust's `Validate(_1.1)`
(`evalStatement_validate_field_any`), while `statementOk` alone still rejects projected `Retag`
(`paddedRetagRead_not_inFragment`). -/
theorem paddedRetagRead_inFragmentD :
    inFragment (eraseDeinit paddedRetagRead) = true ∧
      deinitWindowOk paddedRetagRead = true ∧ inFragmentD paddedRetagRead = true := by
  decide

theorem paddedRetagRead_ctxOk : CtxOk paddedRetagRead ctxPadded2 :=
  ctxPadded2_ok_u32 rfl rfl rfl

theorem paddedRetagRead_argsOk : argsOk paddedRetagRead paddedDeinitReadArgs = true := by
  decide

theorem paddedRetagRead_anneal_noUB :
    MirNoUBTree (mirCallTree paddedRetagRead paddedDeinitReadArgs) :=
  runA_noUB paddedRetagRead 10 _ _ _ rfl

/-- **End-to-end correspondence through `mirCall_ret_D` for `paddedRetagRead`**: Anneal's return of
`99` (`paddedRetagRead_anneal_noop`) yields a MiniRust execution from `f.start` that pops the callee
frame and stores `99` into the caller's return place (matching `paddedRetagRead_minirust_ret`). -/
theorem paddedRetagRead_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n paddedRetagReadMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 99 } ∧
      m'.threads =
        [thread1 ctxPadded2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret_D paddedRetagRead_inFragmentD.2.2 paddedRetagRead_translate
      ctxPadded2 paddedRetagRead_ctxOk paddedDeinitReadArgs
      paddedRetagRead_argsOk paddedRetagReadMInit rfl rfl rfl
      paddedRetagRead_anneal_noop
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [paddedRetagRead] at hd; subst hd
  simp [retPtr, ctxPadded2] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxPadded2] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem paddedRetagRead_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n paddedRetagReadMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k paddedRetagReadMInit = .ok mRet ∧
      ReturnRel paddedRetagRead ctxPadded2 s' v mRet ∧
      ReachesRet (mirCallTree paddedRetagRead paddedDeinitReadArgs) tr
        (.normal (v, mem)) :=
  mirCall_noUB_D paddedRetagRead_inFragmentD.2.2 paddedRetagRead_translate
    ctxPadded2 paddedRetagRead_ctxOk paddedDeinitReadArgs
    paddedRetagRead_argsOk paddedRetagReadMInit rfl rfl rfl
    paddedRetagRead_anneal_noUB herr

/-- MIR of `Deinit(_1.1); Retag(_1.0); _1.1 = const 42_u32; _0 = copy _1.1`: a projected `Retag`
on the disjoint sibling field `_1.0` (byte `0`) while `_1.1` (bytes `4..8`) is an open `Deinit`
hole. -/
def paddedDeinitSiblingRetagReinit : CapturedMir where
  defPath := "witness::padded_deinit_sibling_retag_reinit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.retag .default (placeField 1 [(0, u8TyW)])),
        mkStmt (.assign (placeField 1 [(1, u32Ty)]) (.use (constU32 42))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)]))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

def paddedDeinitSiblingRetagReinitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Deinit (.Field (.Local (localName 1)) 1),
      .Validate (.Field (.Local (localName 1)) 0) false,
      .Assign (.Field (.Local (localName 1)) 1) (.Constant (.Int 42) (.Int u32)),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem paddedDeinitSiblingRetagReinit_translate :
    translateFn paddedDeinitSiblingRetagReinit = some paddedDeinitSiblingRetagReinitFn := rfl

theorem paddedDeinitSiblingRetagReinit_inFragmentD :
    siblingRetagOk paddedDeinitSiblingRetagReinit 1 [.field 1 u32Ty] [.field 0 u8TyW] = true ∧
      inFragment (eraseDeinit paddedDeinitSiblingRetagReinit) = true ∧
      deinitWindowOk paddedDeinitSiblingRetagReinit = true ∧
      inFragmentD paddedDeinitSiblingRetagReinit = true := by
  decide

def paddedDeinitSiblingRetagReinitS0 : MachineState :=
  initMachineState paddedDeinitSiblingRetagReinit paddedDeinitReadArgs

def paddedDeinitSiblingRetagReinitMInit : Mach :=
  machineWithCtx ctxPadded2 paddedDeinitSiblingRetagReinit paddedDeinitSiblingRetagReinitFn
    paddedDeinitSiblingRetagReinitS0.frame.locals paddedDeinitSiblingRetagReinitFn.start

theorem paddedDeinitSiblingRetagReinit_anneal_ret :
    ReachesRet (mirCallTree paddedDeinitSiblingRetagReinit paddedDeinitReadArgs) []
      (.normal (.scalar ⟨42, 4⟩, paddedDeinitSiblingRetagReinitS0.memory)) :=
  runA_sound paddedDeinitSiblingRetagReinit 12 _ _ _ rfl

/-- **End-to-end correspondence through `mirCall_ret_D` for disjoint sibling `Retag` inside an open
`Deinit` hole (`paddedDeinitSiblingRetagReinit_minirust_ret_from_start`).** -/
theorem paddedDeinitSiblingRetagReinit_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n paddedDeinitSiblingRetagReinitMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads =
        [thread1 ctxPadded2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret_D paddedDeinitSiblingRetagReinit_inFragmentD.2.2.2
      paddedDeinitSiblingRetagReinit_translate ctxPadded2 (ctxPadded2_ok_u32 rfl rfl rfl)
      paddedDeinitReadArgs (by decide) paddedDeinitSiblingRetagReinitMInit rfl rfl rfl
      paddedDeinitSiblingRetagReinit_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [paddedDeinitSiblingRetagReinit] at hd; subst hd
  simp [retPtr, ctxPadded2] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxPadded2] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- Negative control for projected `Retag` overlapping an open `Deinit` hole:
`Deinit(_1.1); Retag(_1.1); _1.1 = const 42_u32; _0 = copy _1.1`. Even though `_1.1` is
re-initialized before `_0 = copy _1.1`, `Retag(_1.1)` runs while `_1.1` is `Uninit`: `eraseDeinit`
is in `inFragment`, but `siblingRetagOk` (`[4, 8)` vs `[4, 8)`) rejects the overlapping `Retag`. -/
def paddedDeinitRetagHole : CapturedMir where
  defPath := "witness::padded_deinit_retag_hole"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.retag .default (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (placeField 1 [(1, u32Ty)]) (.use (constU32 42))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)]))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

def paddedDeinitRetagHoleFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Deinit (.Field (.Local (localName 1)) 1),
      .Validate (.Field (.Local (localName 1)) 1) false,
      .Assign (.Field (.Local (localName 1)) 1) (.Constant (.Int 42) (.Int u32)),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem paddedDeinitRetagHole_not_inFragmentD :
    translateFn paddedDeinitRetagHole = some paddedDeinitRetagHoleFn ∧
      siblingRetagOk paddedDeinitRetagHole 1 [.field 1 u32Ty] [.field 1 u32Ty] = false ∧
      inFragment (eraseDeinit paddedDeinitRetagHole) = true ∧
      deinitWindowOk paddedDeinitRetagHole = false ∧
      inFragmentD paddedDeinitRetagHole = false :=
  ⟨rfl, by decide, by decide, by decide, by decide⟩

def paddedDeinitRetagHoleS0 : MachineState :=
  initMachineState paddedDeinitRetagHole paddedDeinitReadArgs

def paddedDeinitRetagHoleMInit : Mach :=
  machineWithCtx ctxPadded2 paddedDeinitRetagHole paddedDeinitRetagHoleFn
    paddedDeinitRetagHoleS0.frame.locals paddedDeinitRetagHoleFn.start

/-- **Overlapping `Retag(_1.1)` on an open `Deinit(_1.1)` hole diverges (`paddedDeinitRetagHole_diverges`)**:
Stage-1 Anneal returns `42` (because `Deinit(_1.1)` keeps `_1` initialized and `Retag(_1.1)` is a
no-op), whereas MiniRust's `Validate(_1.1)` at step `3` faults with UB loading the `Uninit` bytes
`4..8`, justifying `siblingRetagOk`'s disjointness requirement. -/
theorem paddedDeinitRetagHole_diverges :
    ReachesRet (mirCallTree paddedDeinitRetagHole paddedDeinitReadArgs) []
      (.normal (.scalar ⟨42, 4⟩, paddedDeinitRetagHoleS0.memory)) ∧
    ∃ msg, Interp.steps 3 paddedDeinitRetagHoleMInit = .error (.ub msg) :=
  ⟨runA_sound paddedDeinitRetagHole 12 _ _ _ rfl, _, rfl⟩

/-- **The committed `paddedDeinitSiblingReinit` is admitted by `inFragmentD`** (its window
check used to fail): its open-hole window is the sibling read through an integer cast
`_2 = Cast(IntToInt, copy _1.0, u32)` (`castSiblingReadOk`: the `u8` field `_1.0` at byte `0` is
disjoint from the hole `4..8`) followed by the re-initialization `_1.1 = Add(copy _2, const 35_u32)`
(`reinitBinOpOk`), while the old fragment still rejects the body
(`paddedDeinitSiblingReinit_not_inFragment`). -/
theorem paddedDeinitSiblingReinit_inFragmentD :
    inFragment (eraseDeinit paddedDeinitSiblingReinit) = true ∧
      deinitWindowOk paddedDeinitSiblingReinit = true ∧
      inFragmentD paddedDeinitSiblingReinit = true := by
  decide

/-- The two window statements of `paddedDeinitSiblingReinit` pass exactly the new window rules,
and the hole `(1, [.field 1 u32])` is open exactly before them. -/
theorem paddedDeinitSiblingReinit_window_rules :
    castSiblingReadOk paddedDeinitSiblingReinit 1 2 [.field 1 u32Ty] [.field 0 u8TyW] u32Ty = true ∧
    reinitBinOpOk paddedDeinitSiblingReinit 1 2 [.field 1 u32Ty] .add
      { ty := u32Ty, val := .scalar (.int ⟨35, 4⟩) } = true ∧
    (List.range 7).map (holeAt paddedDeinitSiblingReinit 0) =
      [none, none, some (1, [.field 1 u32Ty]), some (1, [.field 1 u32Ty]), none, none, none] :=
  ⟨by decide, by decide, rfl⟩

/-- `ctxPadded3` (callee `_0: u32` at `128`, `_1: Padded` at `256`) is well formed for a body whose
locals are `_0: u32`, the argument `_1: Padded`, and a `u32` temporary `_2` (temporaries get no
caller address). -/
theorem ctxPadded3_ok_u32 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, paddedStructDecl, u32Decl])
    (hlay : body.layouts = paddedLayouts) (hac : body.argCount = 1) : CtxOk body ctxPadded3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd; rw [h] at hd; rw [hlay]; rw [hac] at hi
    match i, hi, hd with
    | 0, _, hd => simp at hd; subst hd; decide
    | 1, _, hd => simp at hd; subst hd; decide
    | _ + 2, hi, _ => omega
  ret := by
    intro d hd; rw [h] at hd; rw [hlay]; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem paddedDeinitSiblingReinit_ctxOk : CtxOk paddedDeinitSiblingReinit ctxPadded3 :=
  ctxPadded3_ok_u32 rfl rfl rfl

theorem paddedDeinitSiblingReinit_argsOk :
    argsOk paddedDeinitSiblingReinit paddedDeinitReadArgs = true := by
  decide

/-- **End to end through `mirCall_ret_D` for `paddedDeinitSiblingReinit` (`castSiblingReadOk` and
`reinitBinOpOk`).** Anneal's return of `42` (`paddedDeinitSiblingReinit_anneal_ret`) gives, by the
projected-`Deinit` correspondence, a MiniRust run from `f.start` that pops the callee frame and
leaves `42` in the caller's return place (agreeing with the direct computation
`paddedDeinitSiblingReinit_minirust_ret`). -/
theorem paddedDeinitSiblingReinit_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n paddedDeinitSiblingReinitMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads =
        [thread1 ctxPadded3 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret_D paddedDeinitSiblingReinit_inFragmentD.2.2 paddedDeinitSiblingReinit_translate
      ctxPadded3 paddedDeinitSiblingReinit_ctxOk paddedDeinitReadArgs
      paddedDeinitSiblingReinit_argsOk paddedDeinitSiblingReinitMInit rfl rfl rfl
      paddedDeinitSiblingReinit_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [paddedDeinitSiblingReinit] at hd; subst hd
  simp [retPtr, ctxPadded3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxPadded3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- **End-to-end UB-freedom through `mirCall_noUB_D` for `paddedDeinitSiblingReinit`.** Since
`mirCallTree paddedDeinitSiblingReinit` is UB-free (`paddedDeinitSiblingReinit_noUB`), any MiniRust
error at step `n` would imply an earlier return. -/
theorem paddedDeinitSiblingReinit_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n paddedDeinitSiblingReinitMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k paddedDeinitSiblingReinitMInit = .ok mRet ∧
      ReturnRel paddedDeinitSiblingReinit ctxPadded3 s' v mRet ∧
      ReachesRet (mirCallTree paddedDeinitSiblingReinit paddedDeinitReadArgs) tr
        (.normal (v, mem)) :=
  mirCall_noUB_D paddedDeinitSiblingReinit_inFragmentD.2.2 paddedDeinitSiblingReinit_translate
    ctxPadded3 paddedDeinitSiblingReinit_ctxOk paddedDeinitReadArgs
    paddedDeinitSiblingReinit_argsOk paddedDeinitSiblingReinitMInit rfl rfl rfl
    paddedDeinitSiblingReinit_noUB herr

/-- **End to end through `mirCall_ret_D`.** Anneal's return of `42`
(`deinitSiblingReinit_anneal_ret`) gives, by the projected-`Deinit` correspondence, a MiniRust
run from `f.start` that pops the callee frame and leaves `42` in the caller's return place
(agreeing with the direct computation `deinitSiblingReinit_minirust_ret_direct`). -/
theorem deinitSiblingReinit_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n deinitSiblingReinitMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads =
        [thread1 ctxPadded2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret_D deinitSiblingReinit_inFragmentD deinitSiblingReinit_translate ctxPadded2
      deinitSiblingReinit_ctxOk deinitSiblingReinitArgs deinitSiblingReinit_argsOk
      deinitSiblingReinitMInit rfl rfl rfl deinitSiblingReinit_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [deinitSiblingReinit] at hd; subst hd
  simp [retPtr, ctxPadded2] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxPadded2] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

/-- **End-to-end UB-freedom through `mirCall_noUB_D`.** Since `mirCallTree deinitSiblingReinit` is
UB-free (`deinitSiblingReinit_anneal_noUB`), any MiniRust error at step `n` would imply an earlier
return. -/
theorem deinitSiblingReinit_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n deinitSiblingReinitMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k deinitSiblingReinitMInit = .ok mRet ∧
      ReturnRel deinitSiblingReinit ctxPadded2 s' v mRet ∧
      ReachesRet (mirCallTree deinitSiblingReinit deinitSiblingReinitArgs) tr (.normal (v, mem)) :=
  mirCall_noUB_D deinitSiblingReinit_inFragmentD deinitSiblingReinit_translate ctxPadded2
    deinitSiblingReinit_ctxOk deinitSiblingReinitArgs deinitSiblingReinit_argsOk
    deinitSiblingReinitMInit rfl rfl rfl deinitSiblingReinit_anneal_noUB herr

/-- **End-to-end forward progress through `mirCall_progress_D`.** At every step `initLen + n` from
`f.start`, MiniRust either is in a `StateRelD`-related state or has already returned. -/
theorem deinitSiblingReinit_minirust_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (initLen deinitSiblingReinit + n) deinitSiblingReinitMInit = .ok m' ∧
      StateRelD deinitSiblingReinit deinitSiblingReinitFn ctxPadded2 s' m' ∧
      Reaches (mirCallTree deinitSiblingReinit deinitSiblingReinitArgs) tr
        (mirTree deinitSiblingReinit s')) ∨
    (∃ k s' mRet tr v mem, k ≤ initLen deinitSiblingReinit + n ∧
      Interp.steps k deinitSiblingReinitMInit = .ok mRet ∧
      ReturnRel deinitSiblingReinit ctxPadded2 s' v mRet ∧
      ReachesRet (mirCallTree deinitSiblingReinit deinitSiblingReinitArgs) tr (.normal (v, mem))) :=
  mirCall_progress_D deinitSiblingReinit_inFragmentD deinitSiblingReinit_translate ctxPadded2
    deinitSiblingReinit_ctxOk deinitSiblingReinitArgs deinitSiblingReinit_argsOk
    deinitSiblingReinitMInit rfl rfl rfl deinitSiblingReinit_anneal_noUB n

/-- `ctxPadded2` is well formed for a body whose locals are `_0: u32`, `_1: Padded`, `_2: u8`,
and `_3: u32` (with `argCount = 1`). -/
theorem ctxPadded2_ok_u8_u32 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, paddedStructDecl, u8Decl, u32Decl])
    (hlay : body.layouts = paddedLayouts) (hac : body.argCount = 1) : CtxOk body ctxPadded2 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd; rw [h] at hd; rw [hlay]; rw [hac] at hi
    match i, hi, hd with
    | 0, _, hd => simp at hd; subst hd; decide
    | 1, _, hd => simp at hd; subst hd; decide
    | _ + 2, hi, _ => omega
  ret := by
    intro d hd; rw [h] at hd; rw [hlay]; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR of a body exercising `reinitCopyOk` (`_1.1 = copy _3`) and live sibling-read consumption:
```rust
fn deinit_sibling_copy_reinit(mut s: Padded) -> u32 {
    let t: u8;          // StorageLive(_2)
    let r: u32;         // StorageLive(_3)
    r = s.1 + 1;        // _3 = Add(copy _1.1, const 1_u32)  (= 100)
    Deinit(s.1);        // Deinit(_1.1)                      [opens hole (1, [.field 1 u32])]
    t = s.0;            // _2 = copy _1.0                    [siblingReadOk: _2 = 7_u8]
    s.1 = r;            // _1.1 = copy _3                    [reinitCopyOk: closes hole with 100]
    r = t as u32;       // _3 = Cast(IntToInt, copy _2, u32) [sibling read _2 = 7 flows to _3]
    s.1 + r             // _0 = Add(copy _1.1, copy _3) = 107; StorageDead(_3); StorageDead(_2); return
}
```
Unlike `deinitSiblingReinit` (where `_2 = copy _1.0` is never read and `_1.1` is re-initialized by
a constant), here the hole `_1.1` is re-initialized by copying local `_3` (`reinitCopyOk`), and the
sibling value read from `_1.0` while the hole was open is cast and added into the returned result
`100 + 7 = 107`. -/
def deinitSiblingCopyReinit : CapturedMir where
  defPath := "witness::deinit_sibling_copy_reinit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl, u8Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.binaryOp .add (.copy (placeField 1 [(1, u32Ty)])) (constU32 1))),
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (local_ 2) (.use (.copy (placeField 1 [(0, u8TyW)])))),
        mkStmt (.assign (placeField 1 [(1, u32Ty)]) (.use (.copy (local_ 3)))),
        mkStmt (.assign (local_ 3) (.cast .intToInt (.copy (local_ 2)) u32Ty)),
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (placeField 1 [(1, u32Ty)])) (.copy (local_ 3)))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

theorem deinitSiblingCopyReinit_inFragmentD : inFragmentD deinitSiblingCopyReinit = true := by
  decide

theorem deinitSiblingCopyReinit_not_inFragment : inFragment deinitSiblingCopyReinit = false := by
  decide

def deinitSiblingCopyReinitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy),
    (localName 2, .Int Witness.u8), (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Add) (.Load (.Field (.Local (localName 1)) 1)) (.Constant (.Int 1) (.Int u32))),
      .Deinit (.Field (.Local (localName 1)) 1),
      .Assign (.Local (localName 2)) (.Load (.Field (.Local (localName 1)) 0)),
      .Assign (.Field (.Local (localName 1)) 1) (.Load (.Local (localName 3))),
      .Assign (.Local (localName 3))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Field (.Local (localName 1)) 1)) (.Load (.Local (localName 3)))),
      .StorageDead (localName 3),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deinitSiblingCopyReinit_translate :
    translateFn deinitSiblingCopyReinit = some deinitSiblingCopyReinitFn := rfl

theorem deinitSiblingCopyReinit_ctxOk : CtxOk deinitSiblingCopyReinit ctxPadded2 :=
  ctxPadded2_ok_u8_u32 rfl rfl rfl

def deinitSiblingCopyReinitArgs : List Value := [initPaddedStruct]

theorem deinitSiblingCopyReinit_argsOk :
    argsOk deinitSiblingCopyReinit deinitSiblingCopyReinitArgs = true := by decide

def deinitSiblingCopyReinitS0 : MachineState :=
  initMachineState deinitSiblingCopyReinit deinitSiblingCopyReinitArgs

def deinitSiblingCopyReinitMInit : Mach :=
  machineWithCtx ctxPadded2 deinitSiblingCopyReinit deinitSiblingCopyReinitFn
    deinitSiblingCopyReinitS0.frame.locals deinitSiblingCopyReinitFn.start

theorem deinitSiblingCopyReinit_anneal_ret :
    ReachesRet (mirCallTree deinitSiblingCopyReinit deinitSiblingCopyReinitArgs) []
      (.normal (.scalar ⟨107, 4⟩, deinitSiblingCopyReinitS0.memory)) :=
  runA_sound deinitSiblingCopyReinit 16 _ _ _ rfl

theorem deinitSiblingCopyReinit_anneal_noUB :
    MirNoUBTree (mirCallTree deinitSiblingCopyReinit deinitSiblingCopyReinitArgs) :=
  runA_noUB deinitSiblingCopyReinit 16 _ _ _ rfl

/-- **End-to-end return through `mirCall_ret_D` for `deinitSiblingCopyReinit` (`reinitCopyOk` and
live sibling read).** Anneal's return of `107` (`100 + 7`) gives a MiniRust run from `f.start` that
pops the callee frame and leaves `107` in the caller's return place. -/
theorem deinitSiblingCopyReinit_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n deinitSiblingCopyReinitMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 107 } ∧
      m'.threads =
        [thread1 ctxPadded2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret_D deinitSiblingCopyReinit_inFragmentD deinitSiblingCopyReinit_translate ctxPadded2
      deinitSiblingCopyReinit_ctxOk deinitSiblingCopyReinitArgs deinitSiblingCopyReinit_argsOk
      deinitSiblingCopyReinitMInit rfl rfl rfl deinitSiblingCopyReinit_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [deinitSiblingCopyReinit] at hd; subst hd
  simp [retPtr, ctxPadded2] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxPadded2] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem deinitSiblingCopyReinit_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n deinitSiblingCopyReinitMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k deinitSiblingCopyReinitMInit = .ok mRet ∧
      ReturnRel deinitSiblingCopyReinit ctxPadded2 s' v mRet ∧
      ReachesRet (mirCallTree deinitSiblingCopyReinit deinitSiblingCopyReinitArgs) tr
        (.normal (v, mem)) :=
  mirCall_noUB_D deinitSiblingCopyReinit_inFragmentD deinitSiblingCopyReinit_translate ctxPadded2
    deinitSiblingCopyReinit_ctxOk deinitSiblingCopyReinitArgs deinitSiblingCopyReinit_argsOk
    deinitSiblingCopyReinitMInit rfl rfl rfl deinitSiblingCopyReinit_anneal_noUB herr

/-- MIR of an `inFragmentD` body that executes a projected-`Deinit` window (`Deinit(_1.1)`,
sibling read `_2 = copy _1.0`, re-initialization `_1.1 = const 42_u32`) and then faults with
division by zero (`_0 = Div(copy _1.1, const 0_u32)`), exercising `mirCall_ub_D`. -/
def deinitSiblingReinitUb : CapturedMir where
  defPath := "witness::deinit_sibling_reinit_ub"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl, u8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (local_ 2) (.use (.copy (placeField 1 [(0, u8TyW)])))),
        mkStmt (.assign (placeField 1 [(1, u32Ty)]) (.use (constU32 42))),
        mkStmt (.assign (local_ 0) (.binaryOp .div (.copy (placeField 1 [(1, u32Ty)])) (constU32 0))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

theorem deinitSiblingReinitUb_inFragmentD : inFragmentD deinitSiblingReinitUb = true := by decide

def deinitSiblingReinitUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy),
    (localName 2, .Int Witness.u8)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Deinit (.Field (.Local (localName 1)) 1),
      .Assign (.Local (localName 2)) (.Load (.Field (.Local (localName 1)) 0)),
      .Assign (.Field (.Local (localName 1)) 1) (.Constant (.Int 42) (.Int u32)),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Div) (.Load (.Field (.Local (localName 1)) 1)) (.Constant (.Int 0) (.Int u32))),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deinitSiblingReinitUb_translate :
    translateFn deinitSiblingReinitUb = some deinitSiblingReinitUbFn := rfl

theorem deinitSiblingReinitUb_ctxOk : CtxOk deinitSiblingReinitUb ctxPadded2 :=
  ctxPadded2_ok_u8 rfl rfl rfl

def deinitSiblingReinitUbS0 : MachineState :=
  initMachineState deinitSiblingReinitUb deinitSiblingReinitArgs

def deinitSiblingReinitUbMInit : Mach :=
  machineWithCtx ctxPadded2 deinitSiblingReinitUb deinitSiblingReinitUbFn
    deinitSiblingReinitUbS0.frame.locals deinitSiblingReinitUbFn.start

theorem deinitSiblingReinitUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree deinitSiblingReinitUb deinitSiblingReinitArgs) tr u ∧
      FaultNow u :=
  faultsA_sound deinitSiblingReinitUb 12 _ (by decide)

/-- **End-to-end UB transfer through `mirCall_ub_D`.** Since `mirCallTree deinitSiblingReinitUb`
faults with UB (`deinitSiblingReinitUb_anneal_ub`), MiniRust started at `f.start` raises UB after
finitely many steps. -/
theorem deinitSiblingReinitUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n deinitSiblingReinitUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := deinitSiblingReinitUb_anneal_ub
  exact mirCall_ub_D deinitSiblingReinitUb_inFragmentD deinitSiblingReinitUb_translate ctxPadded2
    deinitSiblingReinitUb_ctxOk deinitSiblingReinitArgs (by decide)
    deinitSiblingReinitUbMInit rfl rfl rfl hr hf

/-- `ctxPadded2` is well formed for a body whose locals are `_0: u32`, `_1: Padded`, `_2: u8`,
`_3: u32`, and `_4: u32` (with `argCount = 1`). -/
theorem ctxPadded2_ok_u8_u32_u32 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, paddedStructDecl, u8Decl, u32Decl, u32Decl])
    (hlay : body.layouts = paddedLayouts) (hac : body.argCount = 1) : CtxOk body ctxPadded2 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd; rw [h] at hd; rw [hlay]; rw [hac] at hi
    match i, hi, hd with
    | 0, _, hd => simp at hd; subst hd; decide
    | 1, _, hd => simp at hd; subst hd; decide
    | _ + 2, hi, _ => omega
  ret := by
    intro d hd; rw [h] at hd; rw [hlay]; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR of a 4-statement open-hole window exercising `siblingReadOk`, `localCopyWindowOk`, and
`reinitCopyOk` together:
```rust
fn deinit_sibling_relay_reinit(mut s: Padded) -> u32 {
    let t: u8;          // StorageLive(_2)
    let q: u32;         // StorageLive(_3)
    let r: u32;         // StorageLive(_4)
    q = s.1 + 1;        // _3 = Add(copy _1.1, const 1_u32)  (= 100)
    Deinit(s.1);        // Deinit(_1.1)                      [opens hole (1, [.field 1 u32])]
    t = s.0;            // _2 = copy _1.0                    [siblingReadOk: _2 = 7_u8]
    r = q;              // _4 = copy _3                      [localCopyWindowOk: _4 = 100_u32]
    s.1 = r;            // _1.1 = copy _4                    [reinitCopyOk: closes hole with 100]
    q = t as u32;       // _3 = Cast(IntToInt, copy _2, u32) [sibling read _2 = 7 flows to _3]
    s.1 + q             // _0 = Add(copy _1.1, copy _3) = 107; StorageDead(_4.._2); return
}
```
While the hole `(1, [.field 1 u32])` is open, both a disjoint sibling read (`_2 = copy _1.0`) and a
hole-independent local-to-local copy (`_4 = copy _3`) execute before `_1.1 = copy _4` closes the
hole from `_4`. Both values computed while the hole was open (`_2 = 7` and `_4 = 100`) flow into the
returned value `100 + 7 = 107`. -/
def deinitSiblingRelayReinit : CapturedMir where
  defPath := "witness::deinit_sibling_relay_reinit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl, u8Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 3) (.binaryOp .add (.copy (placeField 1 [(1, u32Ty)])) (constU32 1))),
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (local_ 2) (.use (.copy (placeField 1 [(0, u8TyW)])))),
        mkStmt (.assign (local_ 4) (.use (.copy (local_ 3)))),
        mkStmt (.assign (placeField 1 [(1, u32Ty)]) (.use (.copy (local_ 4)))),
        mkStmt (.assign (local_ 3) (.cast .intToInt (.copy (local_ 2)) u32Ty)),
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (placeField 1 [(1, u32Ty)])) (.copy (local_ 3)))),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

theorem deinitSiblingRelayReinit_inFragmentD : inFragmentD deinitSiblingRelayReinit = true := by
  decide

theorem deinitSiblingRelayReinit_not_inFragment : inFragment deinitSiblingRelayReinit = false := by
  decide

def deinitSiblingRelayReinitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy),
    (localName 2, .Int Witness.u8), (localName 3, .Int u32), (localName 4, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .StorageLive (localName 4),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Add) (.Load (.Field (.Local (localName 1)) 1)) (.Constant (.Int 1) (.Int u32))),
      .Deinit (.Field (.Local (localName 1)) 1),
      .Assign (.Local (localName 2)) (.Load (.Field (.Local (localName 1)) 0)),
      .Assign (.Local (localName 4)) (.Load (.Local (localName 3))),
      .Assign (.Field (.Local (localName 1)) 1) (.Load (.Local (localName 4))),
      .Assign (.Local (localName 3))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 2)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Field (.Local (localName 1)) 1)) (.Load (.Local (localName 3)))),
      .StorageDead (localName 4),
      .StorageDead (localName 3),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deinitSiblingRelayReinit_translate :
    translateFn deinitSiblingRelayReinit = some deinitSiblingRelayReinitFn := rfl

theorem deinitSiblingRelayReinit_ctxOk : CtxOk deinitSiblingRelayReinit ctxPadded2 :=
  ctxPadded2_ok_u8_u32_u32 rfl rfl rfl

def deinitSiblingRelayReinitArgs : List Value := [initPaddedStruct]

theorem deinitSiblingRelayReinit_argsOk :
    argsOk deinitSiblingRelayReinit deinitSiblingRelayReinitArgs = true := by decide

def deinitSiblingRelayReinitS0 : MachineState :=
  initMachineState deinitSiblingRelayReinit deinitSiblingRelayReinitArgs

def deinitSiblingRelayReinitMInit : Mach :=
  machineWithCtx ctxPadded2 deinitSiblingRelayReinit deinitSiblingRelayReinitFn
    deinitSiblingRelayReinitS0.frame.locals deinitSiblingRelayReinitFn.start

theorem deinitSiblingRelayReinit_anneal_ret :
    ReachesRet (mirCallTree deinitSiblingRelayReinit deinitSiblingRelayReinitArgs) []
      (.normal (.scalar ⟨107, 4⟩, deinitSiblingRelayReinitS0.memory)) :=
  runA_sound deinitSiblingRelayReinit 19 _ _ _ rfl

theorem deinitSiblingRelayReinit_anneal_noUB :
    MirNoUBTree (mirCallTree deinitSiblingRelayReinit deinitSiblingRelayReinitArgs) :=
  runA_noUB deinitSiblingRelayReinit 19 _ _ _ rfl

/-- The hole `(1, [.field 1 u32])` stays open across the 3-statement window (`_2 = copy _1.0`,
`_4 = copy _3`, `_1.1 = copy _4` at indices `5`, `6`, `7`) and closes at index `8`. -/
theorem deinitSiblingRelayReinit_holeAt :
    (List.range 14).map (holeAt deinitSiblingRelayReinit 0) =
      [none, none, none, none, none,
       some (1, [.field 1 u32Ty]), some (1, [.field 1 u32Ty]), some (1, [.field 1 u32Ty]),
       none, none, none, none, none, none] :=
  rfl

/-- **End-to-end return through `mirCall_ret_D` for `deinitSiblingRelayReinit` (`siblingReadOk` +
`localCopyWindowOk` + `reinitCopyOk`).** Anneal's return of `107` (`100 + 7`) gives a MiniRust run
from `f.start` that pops the callee frame and leaves `107` in the caller's return place. -/
theorem deinitSiblingRelayReinit_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n deinitSiblingRelayReinitMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 107 } ∧
      m'.threads =
        [thread1 ctxPadded2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret_D deinitSiblingRelayReinit_inFragmentD deinitSiblingRelayReinit_translate ctxPadded2
      deinitSiblingRelayReinit_ctxOk deinitSiblingRelayReinitArgs deinitSiblingRelayReinit_argsOk
      deinitSiblingRelayReinitMInit rfl rfl rfl deinitSiblingRelayReinit_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [deinitSiblingRelayReinit] at hd; subst hd
  simp [retPtr, ctxPadded2] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxPadded2] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem deinitSiblingRelayReinit_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n deinitSiblingRelayReinitMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k deinitSiblingRelayReinitMInit = .ok mRet ∧
      ReturnRel deinitSiblingRelayReinit ctxPadded2 s' v mRet ∧
      ReachesRet (mirCallTree deinitSiblingRelayReinit deinitSiblingRelayReinitArgs) tr
        (.normal (v, mem)) :=
  mirCall_noUB_D deinitSiblingRelayReinit_inFragmentD deinitSiblingRelayReinit_translate ctxPadded2
    deinitSiblingRelayReinit_ctxOk deinitSiblingRelayReinitArgs deinitSiblingRelayReinit_argsOk
    deinitSiblingRelayReinitMInit rfl rfl rfl deinitSiblingRelayReinit_anneal_noUB herr

/-! ### New window rules: a UB transfer and negative controls

`paddedDeinitBinOpDivZero` re-initializes the hole by a division by zero (`reinitBinOpOk` admits
the statement; both machines fault), and `mirCall_ub_D` transfers Anneal's fault to MiniRust.
`paddedDeinitHoleBinOp` and `paddedDeinitHoleCastRead` read the hole itself inside the window (as a
`BinOp` operand and through a cast); Anneal reads the stale field while MiniRust's load of the
`Uninit` bytes is UB, and the window check alone rejects both (their erasures are in the old
fragment). -/

/-- MIR of
```rust
fn padded_deinit_binop_div_zero(mut s: Padded) -> u32 {
    let a: u32;          // StorageLive(_2)
    Deinit(s.1);         // Deinit(_1.1)                      [opens hole (1, [.field 1 u32])]
    a = s.0 as u32;      // _2 = Cast(IntToInt, copy _1.0, u32) [castSiblingReadOk]
    s.1 = a / 0;         // _1.1 = Div(copy _2, const 0_u32)    [reinitBinOpOk: division by zero]
    s.1                  // _0 = copy _1.1; StorageDead(_2); return
}
``` -/
def paddedDeinitBinOpDivZero : CapturedMir where
  defPath := "witness::padded_deinit_binop_div_zero"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (local_ 2) (.cast .intToInt (.copy (placeField 1 [(0, u8TyW)])) u32Ty)),
        mkStmt (.assign (placeField 1 [(1, u32Ty)])
          (.binaryOp .div (.copy (local_ 2)) (constU32 0))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)])))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

theorem paddedDeinitBinOpDivZero_inFragmentD : inFragmentD paddedDeinitBinOpDivZero = true := by
  decide

def paddedDeinitBinOpDivZeroFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy), (localName 2, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Deinit (.Field (.Local (localName 1)) 1),
      .Assign (.Local (localName 2))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Field (.Local (localName 1)) 0))),
      .Assign (.Field (.Local (localName 1)) 1)
        (.BinOp (.Int .Div) (.Load (.Local (localName 2))) (.Constant (.Int 0) (.Int u32))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1)),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem paddedDeinitBinOpDivZero_translate :
    translateFn paddedDeinitBinOpDivZero = some paddedDeinitBinOpDivZeroFn := rfl

def paddedDeinitBinOpDivZeroS0 : MachineState :=
  initMachineState paddedDeinitBinOpDivZero paddedDeinitReadArgs

def paddedDeinitBinOpDivZeroMInit : Mach :=
  machineWithCtx ctxPadded3 paddedDeinitBinOpDivZero paddedDeinitBinOpDivZeroFn
    paddedDeinitBinOpDivZeroS0.frame.locals paddedDeinitBinOpDivZeroFn.start

/-- Anneal faults on the division by zero (computed by the kernel). -/
theorem paddedDeinitBinOpDivZero_anneal_ub :
    ∃ tr u, Reaches (mirCallTree paddedDeinitBinOpDivZero paddedDeinitReadArgs) tr u ∧
      FaultNow u :=
  faultsA_sound paddedDeinitBinOpDivZero 12 _ (by decide)

/-- **End-to-end UB transfer through `mirCall_ub_D` for a `BinOp` re-initialization of the hole.**
Since Anneal faults (`paddedDeinitBinOpDivZero_anneal_ub`), MiniRust started at `f.start` raises UB
after finitely many steps (the `intBinEval = none` branch of `step_window_reinit_binop`). -/
theorem paddedDeinitBinOpDivZero_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n paddedDeinitBinOpDivZeroMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := paddedDeinitBinOpDivZero_anneal_ub
  exact mirCall_ub_D paddedDeinitBinOpDivZero_inFragmentD paddedDeinitBinOpDivZero_translate
    ctxPadded3 (ctxPadded3_ok_u32 rfl rfl rfl) paddedDeinitReadArgs (by decide)
    paddedDeinitBinOpDivZeroMInit rfl rfl rfl hr hf

/-- The direct MiniRust run agrees: the fifth step (init `Goto`, `StorageLive(_2)`, `Deinit`, the
cast read, and the division) is UB (computed by the kernel). -/
theorem paddedDeinitBinOpDivZero_minirust_ub_direct :
    ∃ msg, Interp.steps 5 paddedDeinitBinOpDivZeroMInit = .error (.ub msg) :=
  ⟨_, rfl⟩

/-- MIR of
```rust
fn padded_deinit_hole_binop(mut s: Padded) -> u32 {
    Deinit(s.1);         // Deinit(_1.1)
    s.1 = s.1 + 1;       // _1.1 = Add(copy _1.1, const 1_u32)   [reads the hole]
    s.1                  // _0 = copy _1.1; return
}
``` -/
def paddedDeinitHoleBinOp : CapturedMir where
  defPath := "witness::padded_deinit_hole_binop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (placeField 1 [(1, u32Ty)])
          (.binaryOp .add (.copy (placeField 1 [(1, u32Ty)])) (constU32 1))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)]))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

/-- Negative control: the `BinOp` re-initialization reads the hole, so `reinitBinOpOk` (which needs
a bare local `copy _q` with `q ≠ t`) does not apply and the window check alone rejects the body. -/
theorem paddedDeinitHoleBinOp_not_inFragmentD :
    inFragment (eraseDeinit paddedDeinitHoleBinOp) = true ∧
      deinitWindowOk paddedDeinitHoleBinOp = false ∧ inFragmentD paddedDeinitHoleBinOp = false := by
  decide

def paddedDeinitHoleBinOpFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .Deinit (.Field (.Local (localName 1)) 1),
      .Assign (.Field (.Local (localName 1)) 1)
        (.BinOp (.Int .Add) (.Load (.Field (.Local (localName 1)) 1))
          (.Constant (.Int 1) (.Int u32))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem paddedDeinitHoleBinOp_translate :
    translateFn paddedDeinitHoleBinOp = some paddedDeinitHoleBinOpFn := rfl

def paddedDeinitHoleBinOpS0 : MachineState :=
  initMachineState paddedDeinitHoleBinOp paddedDeinitReadArgs

def paddedDeinitHoleBinOpMInit : Mach :=
  machineWithCtx ctxPadded2 paddedDeinitHoleBinOp paddedDeinitHoleBinOpFn
    paddedDeinitHoleBinOpS0.frame.locals paddedDeinitHoleBinOpFn.start

/-- The divergence the window check prevents (computed by the kernel): Anneal's projected `Deinit`
keeps `_1.1 = 99`, so Anneal returns `100`, whereas MiniRust's `BinOp` loads the `Uninit` hole and
the third step (init `Goto`, `Deinit`, the re-initialization) is UB. -/
theorem paddedDeinitHoleBinOp_diverges :
    ReachesRet (mirCallTree paddedDeinitHoleBinOp paddedDeinitReadArgs) []
        (.normal (.scalar ⟨100, 4⟩, paddedDeinitHoleBinOpS0.memory)) ∧
      ∃ msg, Interp.steps 3 paddedDeinitHoleBinOpMInit = .error (.ub msg) :=
  ⟨runA_sound paddedDeinitHoleBinOp 10 _ _ _ rfl, _, rfl⟩

/-- MIR of
```rust
fn padded_deinit_hole_cast_read(mut s: Padded) -> u32 {
    let a: u32;          // StorageLive(_2)
    Deinit(s.1);         // Deinit(_1.1)
    a = s.1 as u32;      // _2 = Cast(IntToInt, copy _1.1, u32)   [reads the hole]
    s.1 = a;             // _1.1 = copy _2
    s.1                  // _0 = copy _1.1; StorageDead(_2); return
}
``` -/
def paddedDeinitHoleCastRead : CapturedMir where
  defPath := "witness::padded_deinit_hole_cast_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (local_ 2) (.cast .intToInt (.copy (placeField 1 [(1, u32Ty)])) u32Ty)),
        mkStmt (.assign (placeField 1 [(1, u32Ty)]) (.use (.copy (local_ 2)))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)])))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

/-- Negative control: the cast reads the hole's own bytes, so `castSiblingReadOk`'s disjointness
check fails and the window check alone rejects the body. -/
theorem paddedDeinitHoleCastRead_not_inFragmentD :
    inFragment (eraseDeinit paddedDeinitHoleCastRead) = true ∧
      castSiblingReadOk paddedDeinitHoleCastRead 1 2 [.field 1 u32Ty] [.field 1 u32Ty] u32Ty =
        false ∧
      deinitWindowOk paddedDeinitHoleCastRead = false ∧
      inFragmentD paddedDeinitHoleCastRead = false := by
  decide

def paddedDeinitHoleCastReadFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy), (localName 2, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .Deinit (.Field (.Local (localName 1)) 1),
      .Assign (.Local (localName 2))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Field (.Local (localName 1)) 1))),
      .Assign (.Field (.Local (localName 1)) 1) (.Load (.Local (localName 2))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1)),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem paddedDeinitHoleCastRead_translate :
    translateFn paddedDeinitHoleCastRead = some paddedDeinitHoleCastReadFn := rfl

def paddedDeinitHoleCastReadS0 : MachineState :=
  initMachineState paddedDeinitHoleCastRead paddedDeinitReadArgs

def paddedDeinitHoleCastReadMInit : Mach :=
  machineWithCtx ctxPadded3 paddedDeinitHoleCastRead paddedDeinitHoleCastReadFn
    paddedDeinitHoleCastReadS0.frame.locals paddedDeinitHoleCastReadFn.start

/-- The divergence the disjointness check prevents (computed by the kernel): Anneal reads the stale
`_1.1 = 99` through the cast and returns `99`, whereas MiniRust's cast loads the `Uninit` hole and
the fourth step (init `Goto`, `StorageLive(_2)`, `Deinit`, the cast read) is UB. -/
theorem paddedDeinitHoleCastRead_diverges :
    ReachesRet (mirCallTree paddedDeinitHoleCastRead paddedDeinitReadArgs) []
        (.normal (.scalar ⟨99, 4⟩, paddedDeinitHoleCastReadS0.memory)) ∧
      ∃ msg, Interp.steps 4 paddedDeinitHoleCastReadMInit = .error (.ub msg) :=
  ⟨runA_sound paddedDeinitHoleCastRead 12 _ _ _ rfl, _, rfl⟩

/-- `ctxPadded3` is well formed for a body whose locals are `_0: u32`, `_1: Padded`, `_2: u32`,
and `_3: u32` (with `argCount = 1`). -/
theorem ctxPadded3_ok_u32_u32 {body : CapturedMir}
    (h : body.localDecls = [u32Decl, paddedStructDecl, u32Decl, u32Decl])
    (hlay : body.layouts = paddedLayouts) (hac : body.argCount = 1) : CtxOk body ctxPadded3 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd; rw [h] at hd; rw [hlay]; rw [hac] at hi
    match i, hi, hd with
    | 0, _, hd => simp at hd; subst hd; decide
    | 1, _, hd => simp at hd; subst hd; decide
    | _ + 2, hi, _ => omega
  ret := by
    intro d hd; rw [h] at hd; rw [hlay]; simp at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- MIR of a 3-statement open-hole window exercising `castSiblingReadOk`, `binOpWindowOk`
(a hole-independent integer binary operation into a temporary local while the hole stays open), and
`reinitBinOpOk` together:
```rust
fn deinit_sibling_binop_window_reinit(mut s: Padded) -> u32 {
    let a: u32;          // StorageLive(_2)
    let b: u32;          // StorageLive(_3)
    Deinit(s.1);         // Deinit(_1.1)                      [opens hole (1, [.field 1 u32])]
    a = s.0 as u32;      // _2 = Cast(IntToInt, copy _1.0, u32) [castSiblingReadOk: _2 = 7_u32]
    b = a + 10;          // _3 = Add(copy _2, const 10_u32)   [binOpWindowOk: _3 = 17_u32]
    s.1 = b + 25;        // _1.1 = Add(copy _3, const 25_u32) [reinitBinOpOk: closes hole with 42]
    s.1                  // _0 = copy _1.1; StorageDead(_3, _2); return
}
``` -/
def deinitSiblingBinOpWindowReinit : CapturedMir where
  defPath := "witness::deinit_sibling_binop_window_reinit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, paddedStructDecl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.deinit (placeField 1 [(1, u32Ty)])),
        mkStmt (.assign (local_ 2) (.cast .intToInt (.copy (placeField 1 [(0, u8TyW)])) u32Ty)),
        mkStmt (.assign (local_ 3) (.binaryOp .add (.copy (local_ 2)) (constU32 10))),
        mkStmt (.assign (placeField 1 [(1, u32Ty)]) (.binaryOp .add (.copy (local_ 3)) (constU32 25))),
        mkStmt (.assign (local_ 0) (.use (.copy (placeField 1 [(1, u32Ty)])))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiPaddedOne
  layouts := paddedLayouts
  allocations := []

theorem deinitSiblingBinOpWindowReinit_inFragmentD :
    inFragmentD deinitSiblingBinOpWindowReinit = true := by decide

theorem deinitSiblingBinOpWindowReinit_not_inFragment :
    inFragment deinitSiblingBinOpWindowReinit = false := by decide

theorem deinitSiblingBinOpWindowReinit_window_rules :
    castSiblingReadOk deinitSiblingBinOpWindowReinit 1 2 [.field 1 u32Ty] [.field 0 u8TyW]
      u32Ty = true ∧
    binOpWindowOk deinitSiblingBinOpWindowReinit 1 3 2 .add
      { ty := u32Ty, val := .scalar (.int ⟨10, 4⟩) } = true ∧
    reinitBinOpOk deinitSiblingBinOpWindowReinit 1 3 [.field 1 u32Ty] .add
      { ty := u32Ty, val := .scalar (.int ⟨25, 4⟩) } = true ∧
    (List.range 10).map (holeAt deinitSiblingBinOpWindowReinit 0) =
      [none, none, none,
       some (1, [.field 1 u32Ty]), some (1, [.field 1 u32Ty]), some (1, [.field 1 u32Ty]),
       none, none, none, none] :=
  ⟨by decide, by decide, by decide, rfl⟩

def deinitSiblingBinOpWindowReinitFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, paddedMiniRustTy),
    (localName 2, .Int u32), (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .Deinit (.Field (.Local (localName 1)) 1),
      .Assign (.Local (localName 2))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Field (.Local (localName 1)) 0))),
      .Assign (.Local (localName 3))
        (.BinOp (.Int .Add) (.Load (.Local (localName 2))) (.Constant (.Int 10) (.Int u32))),
      .Assign (.Field (.Local (localName 1)) 1)
        (.BinOp (.Int .Add) (.Load (.Local (localName 3))) (.Constant (.Int 25) (.Int u32))),
      .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1)),
      .StorageDead (localName 3),
      .StorageDead (localName 2)],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem deinitSiblingBinOpWindowReinit_translate :
    translateFn deinitSiblingBinOpWindowReinit = some deinitSiblingBinOpWindowReinitFn := rfl

theorem deinitSiblingBinOpWindowReinit_ctxOk : CtxOk deinitSiblingBinOpWindowReinit ctxPadded3 :=
  ctxPadded3_ok_u32_u32 rfl rfl rfl

theorem deinitSiblingBinOpWindowReinit_argsOk :
    argsOk deinitSiblingBinOpWindowReinit paddedDeinitReadArgs = true := by decide

def deinitSiblingBinOpWindowReinitS0 : MachineState :=
  initMachineState deinitSiblingBinOpWindowReinit paddedDeinitReadArgs

def deinitSiblingBinOpWindowReinitMInit : Mach :=
  machineWithCtx ctxPadded3 deinitSiblingBinOpWindowReinit deinitSiblingBinOpWindowReinitFn
    deinitSiblingBinOpWindowReinitS0.frame.locals deinitSiblingBinOpWindowReinitFn.start

theorem deinitSiblingBinOpWindowReinit_anneal_ret :
    ReachesRet (mirCallTree deinitSiblingBinOpWindowReinit paddedDeinitReadArgs) []
      (.normal (.scalar ⟨42, 4⟩, deinitSiblingBinOpWindowReinitS0.memory)) :=
  runA_sound deinitSiblingBinOpWindowReinit 14 _ _ _ rfl

theorem deinitSiblingBinOpWindowReinit_anneal_noUB :
    MirNoUBTree (mirCallTree deinitSiblingBinOpWindowReinit paddedDeinitReadArgs) :=
  runA_noUB deinitSiblingBinOpWindowReinit 14 _ _ _ rfl

/-- **End-to-end return through `mirCall_ret_D` for `deinitSiblingBinOpWindowReinit`
(`castSiblingReadOk` + `binOpWindowOk` + `reinitBinOpOk`).** Anneal's return of `42` (`7 + 10 + 25`)
gives a MiniRust run from `f.start` that pops the callee frame and leaves `42` in the caller's
return place. -/
theorem deinitSiblingBinOpWindowReinit_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n deinitSiblingBinOpWindowReinitMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads =
        [thread1 ctxPadded3 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret_D deinitSiblingBinOpWindowReinit_inFragmentD
      deinitSiblingBinOpWindowReinit_translate ctxPadded3 deinitSiblingBinOpWindowReinit_ctxOk
      paddedDeinitReadArgs deinitSiblingBinOpWindowReinit_argsOk
      deinitSiblingBinOpWindowReinitMInit rfl rfl rfl deinitSiblingBinOpWindowReinit_anneal_ret
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [deinitSiblingBinOpWindowReinit] at hd; subst hd
  simp [retPtr, ctxPadded3] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctxPadded3] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem deinitSiblingBinOpWindowReinit_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n deinitSiblingBinOpWindowReinitMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k deinitSiblingBinOpWindowReinitMInit = .ok mRet ∧
      ReturnRel deinitSiblingBinOpWindowReinit ctxPadded3 s' v mRet ∧
      ReachesRet (mirCallTree deinitSiblingBinOpWindowReinit paddedDeinitReadArgs) tr
        (.normal (v, mem)) :=
  mirCall_noUB_D deinitSiblingBinOpWindowReinit_inFragmentD
    deinitSiblingBinOpWindowReinit_translate ctxPadded3 deinitSiblingBinOpWindowReinit_ctxOk
    paddedDeinitReadArgs deinitSiblingBinOpWindowReinit_argsOk
    deinitSiblingBinOpWindowReinitMInit rfl rfl rfl deinitSiblingBinOpWindowReinit_anneal_noUB herr

end MiniRustSpec.Correspondence.Witness
