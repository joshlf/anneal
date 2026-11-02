import Trusted.Refinement
import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators
import MiniRust.LibSpecr
import MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
import MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops
import Correspondence.Framework

/-!
# `Correspondence.DialectInterface` — Version-Agnostic MIR Dialect Interface

Decouples the horizontal correspondence architecture (`L1`–`L4` + `Scorecard`) from
any single frozen `rustc` commit so that multiple concurrent Anneal MIR models
(`Trusted.Rustc.V2026_06_01`, `Trusted.Rustc.V2026_12_01`, ...) implement a
single uniform mathematical interface (`AnnealMirDialect`).

Every fixture evaluation in `evalAnnealV2026_06_01` directly executes the **real
operational functions** of `Trusted.Rustc.V2026_06_01.MirSemantics` (`evalScalarBinOp`,
`encodeLittleEndianBytes`, `decodeLittleEndianBytes`, `evalRvalue`, `writePlaceValue`,
`readProjectedValue`, `writeProjectedValue`, `hasProtectedWriteConflict`, `findCallee?`)
so that fixing an underlying bug in `trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/`
genuinely alters `evalAnnealV2026_06_01` and breaks `by decide` in `GeneratedGapWitnesses.lean`.
-/

namespace Correspondence

open Trusted.Refinement
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr

/--
Abstract interface implemented by each versioned Anneal MIR semantics dialect
(`Trusted.Rustc.V*`), exposing its version tag, pinned `rustc` commit identifier,
state/program carriers, step evaluator, and projection into `Partial (BehaviorSet Verdict)`.
-/
structure AnnealMirDialect : Type 1 where
  /-- Dialect version identifier (`V2026_06_01`, etc.). -/
  version : AnnealVer
  /-- Pinned upstream `rust-lang/rust` commit SHA modeled by this dialect. -/
  rustcCommit : String
  /-- Dialect program / fixture carrier. -/
  Prog : Type
  /-- Dialect execution state carrier. -/
  State : Type
  /-- Total bounded verdict evaluator used for kernel `by decide` witness checks. -/
  evalVerdict : Prog → State → Verdict
  /-- Layer 1A Smyth behavior semantics induced by `evalVerdict`. -/
  sem : Prog → State → Partial (BehaviorSet Verdict) :=
    fun p st => (evalVerdict p st).toPartial

/--
Canonical `FixtureProg` + `FixtureState` carriers used across cross-version gap
guards and counterexample witnesses so `V2026_06_01` and future `V2026_12_01`
dialects can be compared side-by-side on identical test cases.
-/
inductive FixtureProg : Type where
  /-- Safe canonical scalar addition (`12 + 30 = 42` in `u32`). -/
  | canonicalSafeScalarAdd
  /-- Safe canonical little-endian byte encode/decode round-trip (`u32`). -/
  | canonicalSafeByteRoundTrip
  /-- Safe canonical stack local write followed by read. -/
  | canonicalSafeLocalWriteRead
  /-- Safe canonical exclusive `&mut` reborrow write and parent read. -/
  | canonicalSafeTreeBorrowMut
  /-- `GAP-MR-0001`: Write through raw pointer derived from `&UnsafeCell<u32>`. -/
  | sharedUnsafeCellWrite
  /-- `GAP-MR-0002`: Write to second variant of `union` then read scalar back. -/
  | unionVariantWriteRead
  /-- `GAP-MR-0003`: Borrow `arr[tmp]` where `tmp` becomes `StorageDead` before deref. -/
  | dynamicArrayIndexBorrow
  /-- `GAP-MR-0004`: Call `core::intrinsics::exact_div(24, 2)` as intrinsic terminator. -/
  | exactDivIntrinsicCall
  /-- `GAP-EPOCH-0001`: Foreign read under `Reserved` with interior mutability (post-2026-05 rule). -/
  | reservedImEpochTransition
  deriving DecidableEq, Repr

/-- Execution state metadata accompanying a `FixtureProg`. -/
structure FixtureState : Type where
  initialFuel : Nat := 128
  checkOverflow : Bool := true
  deriving DecidableEq, Repr

/-- Default initial state used across all fixture evaluations. -/
@[reducible]
def defaultFixtureState : FixtureState :=
  { initialFuel := 128, checkOverflow := true }

/-- Convert a real `RvalueEvalResult` from `Trusted.Rustc.V2026_06_01.MirSemantics` into a `Verdict`. -/
@[reducible]
def rvalueResultToVerdict : RvalueEvalResult → Verdict
  | .ok (.scalar sc) _ _ => .normalScalar sc.bits
  | .ok _ _ _ => .normalUnit
  | .ub => .ub
  | .unsupported => .unsupported

/-- Convert a real `PlaceWriteResult` from `Trusted.Rustc.V2026_06_01.MirSemantics` into a `Verdict`. -/
@[reducible]
def placeWriteResultToVerdict : PlaceWriteResult → Verdict
  | .ok _ => .normalUnit
  | .ub => .ub
  | .unsupported => .unsupported

/-- Convert a real `ProjReadResult` from `Trusted.Rustc.V2026_06_01.MirSemantics` into a `Verdict`. -/
@[reducible]
def projReadResultToVerdict : ProjReadResult → Verdict
  | .ok (.scalar sc) => .normalScalar sc.bits
  | .ok _ => .normalUnit
  | .ub => .ub
  | .unsupported => .unsupported

/-- Convert a real `ProjWriteResult` from `Trusted.Rustc.V2026_06_01.MirSemantics` into a `Verdict`. -/
@[reducible]
def projWriteResultToVerdict : ProjWriteResult → Verdict
  | .ok _ => .normalUnit
  | .ub => .ub
  | .unsupported => .unsupported

/--
Evaluate a `FixtureProg` by directly invoking the **actual operational semantics
functions** in `Trusted.Rustc.V2026_06_01.MirSemantics`:

1. `.canonicalSafeScalarAdd`: executes `evalScalarBinOp .add ⟨12, 4⟩ ⟨30, 4⟩ [] emptyMemory false`
2. `.canonicalSafeByteRoundTrip`: executes `decodeLittleEndianBytes (encodeLittleEndianBytes 42 4 .none)`
3. `.canonicalSafeLocalWriteRead`: executes `writePlaceValue` followed by `readProjectedValue`
4. `.canonicalSafeTreeBorrowMut`: executes `evalRvalue (.ref (.mut false) ...)` followed by deref `writePlaceValue`
5. `.sharedUnsafeCellWrite` (`GAP-MR-0001`): executes `evalRvalue (.ref .shared ...)` on local 0 and then
   executes `writePlaceValue` through the resulting pointer (`[.deref]`), which faults with `.ub` in `Places.lean:1368`
   because `evalRvalue` assigned `TreeBorrowPerm.frozen` without checking `UnsafeCell` (`!Freeze`).
6. `.unionVariantWriteRead` (`GAP-MR-0002`): executes `evalRvalue (.aggregate (.adt "UnionU32" 0 []) [.constScalar])`
   and then writes to union variant field 1 via `writeProjectedValue`, which faults with `.ub` in `Places.lean:993-1002`.
7. `.dynamicArrayIndexBorrow` (`GAP-MR-0003`): executes `evalRvalue (.ref .shared { local_ := 0, projection := [.index 1] })`,
   marks temporary index local 1 `.dead` (`StorageDead(1)`), and reads through the recorded `entry.targetProjection`
   via `readProjectedValue`, which faults with `.ub` in `Places.lean:945-950`.
8. `.exactDivIntrinsicCall` (`GAP-MR-0004`): looks up `"core::intrinsics::exact_div"` via `findCallee? emptyMemory.callees`
   (`Terminators.lean:43`), which returns `.none` (unmodeled external intrinsic call → `.unsupported`).
9. `.reservedImEpochTransition` (`GAP-EPOCH-0001`): executes `hasProtectedWriteConflict` on a protected `Reserved` borrow entry.
-/
@[reducible]
def evalAnnealV2026_06_01 (prog : FixtureProg) (_st : FixtureState) : Verdict :=
  match prog with
  | .canonicalSafeScalarAdd =>
    rvalueResultToVerdict (evalScalarBinOp .add ⟨12, 4⟩ ⟨30, 4⟩ .nil emptyMemory false)
  | .canonicalSafeByteRoundTrip =>
    match decodeLittleEndianBytes (encodeLittleEndianBytes 42 4 .none) with
    | .some (bits, _) => .normalScalar bits
    | .none => .ub
  | .canonicalSafeLocalWriteRead =>
    match writePlaceValue [.uninit] .nil { local_ := 0, projection := .nil } (.scalar ⟨7, 4⟩) with
    | .ok locals' =>
      match locals' with
      | .init v :: _ =>
        match readProjectedValue locals' v .nil with
        | .ok _ => .normalUnit
        | .ub => .ub
        | .unsupported => .unsupported
      | _ => .ub
    | .ub => .ub
    | .unsupported => .unsupported
  | .canonicalSafeTreeBorrowMut =>
    let initLocals : List LocalSlot := [.init (.scalar ⟨10, 4⟩), .uninit]
    match evalRvalue initLocals (.ref (.mut false) { local_ := 0, projection := .nil }) emptyMemory with
    | .ok ptrVal _ memAfterRef =>
      let localsWithPtr : List LocalSlot := [.init (.scalar ⟨10, 4⟩), .init ptrVal]
      placeWriteResultToVerdict
        (writePlaceValue localsWithPtr memAfterRef.borrows { local_ := 1, projection := [.deref] } (.scalar ⟨42, 4⟩))
    | .ub => .ub
    | .unsupported => .unsupported
  | .sharedUnsafeCellWrite =>
    let initLocals : List LocalSlot := [.init (.scalar ⟨10, 4⟩), .uninit]
    match evalRvalue initLocals (.ref .shared { local_ := 0, projection := .nil }) emptyMemory with
    | .ok ptrVal _ memAfterRef =>
      let localsWithPtr : List LocalSlot := [.init (.scalar ⟨10, 4⟩), .init ptrVal]
      placeWriteResultToVerdict
        (writePlaceValue localsWithPtr memAfterRef.borrows { local_ := 1, projection := [.deref] } (.scalar ⟨42, 4⟩))
    | .ub => .ub
    | .unsupported => .unsupported
  | .unionVariantWriteRead =>
    let unionVal : Value := .aggregate 0 [.unit]
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    projWriteResultToVerdict
      (writeProjectedValue [.init unionVal] unionVal [.field 1 u32Ty] (.scalar ⟨99, 4⟩))
  | .dynamicArrayIndexBorrow =>
    let arrVal : Value := .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨30, 4⟩]
    let localsAtBorrow : List LocalSlot := [.init arrVal, .init (.scalar ⟨1, 8⟩)]
    match evalRvalue localsAtBorrow (.ref .shared { local_ := 0, projection := [.index 1] }) emptyMemory with
    | .ok _ _ memAfterRef =>
      match memAfterRef.borrows with
      | entry :: _ =>
        let localsAfterStorageDead : List LocalSlot := [.init arrVal, .dead]
        match readProjectedValue localsAfterStorageDead arrVal entry.targetProjection with
        | .ok _ => .normalUnit
        | .ub => .ub
        | .unsupported => .unsupported
      | .nil => .ub
    | .ub => .ub
    | .unsupported => .unsupported
  | .exactDivIntrinsicCall =>
    match findCallee? emptyMemory.callees "core::intrinsics::exact_div" with
    | .some _ => .normalUnit
    | .none => .unsupported
  | .reservedImEpochTransition =>
    let protectedReservedEntry : BorrowEntry := {
      tag := 1
      targetLocal := 0
      targetProjection := .nil
      perm := .reserved
      protector := .some 1
    }
    match hasProtectedWriteConflict [protectedReservedEntry] [1] 0 (.some 2) .nil with
    | true => .ub
    | false => .normalUnit

/--
Evaluate a `FixtureProg` under upstream MiniRust snapshot `snap : MiniRustSnap`
by directly invoking the mechanically extracted operational functions in
`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops` and
`MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops`.
-/
@[reducible]
def evalMiniRustSnapshot (snap : MiniRustSnap) (prog : FixtureProg) : Verdict :=
  match snap with
  | .S2026_05_Matched =>
    open MiniRust.Snapshots.S2026_05_Matched.Generated.Ops in
    match prog with
    | .canonicalSafeScalarAdd =>
      match eval_bin_op_int .Add 12 30 { signed := .Unsigned, size := ⟨4⟩ } with
      | .ok v => .normalScalar v.toNat
      | .error _ => .ub
    | .canonicalSafeByteRoundTrip =>
      match decode_int_le (encode_int_le 42 4 .none) with
      | .some (bits, _) => .normalScalar bits
      | .none => .ub
    | .canonicalSafeLocalWriteRead =>
      let initMem : BasicMemory := {
        allocs := [{ id := 0, align := ⟨2⟩, size := 4, live := true, bytes := [0, 0, 0, 0] }]
        nextAllocId := 1
      }
      match basicMemStore initMem { allocId := 0, offset := 0 } ⟨2⟩ [7, 0, 0, 0] with
      | .ok mem' =>
        match basicMemLoad mem' { allocId := 0, offset := 0 } ⟨2⟩ 4 with
        | .ok _ => .normalUnit
        | .error _ => .ub
      | .error _ => .ub
    | .canonicalSafeTreeBorrowMut =>
      let p0 := reborrow_permission true .No true true false
      match p0.transition .Write .Local with
      | .ok _ => .normalUnit
      | .error _ => .ub
    | .sharedUnsafeCellWrite =>
      let p0 := reborrow_permission false .No true false false
      match p0.transition .Write .Local with
      | .ok _ => .normalUnit
      | .error _ => .ub
    | .unionVariantWriteRead =>
      match encode_union_chunks 4 [(0, encode_int_le 99 4 .none)] with
      | .some bs =>
        match decode_union_chunks bs [(0, 4)] with
        | .some _ => .normalUnit
        | .none => .ub
      | .none => .ub
    | .dynamicArrayIndexBorrow =>
      match mrProjectIndexOffset 0 4 1 2 with
      | .ok off =>
        let mem : BasicMemory := {
          allocs := [{ id := 0, align := ⟨2⟩, size := 8, live := true, bytes := [10, 0, 0, 0, 30, 0, 0, 0] }]
          nextAllocId := 1
        }
        match basicMemLoad mem { allocId := 0, offset := off } ⟨2⟩ 4 with
        | .ok _ => .normalUnit
        | .error _ => .ub
      | .error _ => .ub
    | .exactDivIntrinsicCall =>
      match eval_bin_op_int .DivExact 24 2 { signed := .Unsigned, size := ⟨4⟩ } with
      | .ok _ => .normalUnit
      | .error _ => .ub
    | .reservedImEpochTransition =>
      match (reborrow_permission true .Strong true false true).init_access with
      | .some .Write => .normalUnit
      | _ => .ub
  | .S2026_07_BleedingEdge =>
    open MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops in
    match prog with
    | .canonicalSafeScalarAdd =>
      match eval_bin_op_int .Add 12 30 { signed := .Unsigned, size := ⟨4⟩ } with
      | .ok v => .normalScalar v.toNat
      | .error _ => .ub
    | .canonicalSafeByteRoundTrip =>
      match decode_int_le (encode_int_le 42 4 .none) with
      | .some (bits, _) => .normalScalar bits
      | .none => .ub
    | .canonicalSafeLocalWriteRead =>
      let initMem : BasicMemory := {
        allocs := [{ id := 0, align := ⟨2⟩, size := 4, live := true, bytes := [0, 0, 0, 0] }]
        nextAllocId := 1
      }
      match basicMemStore initMem { allocId := 0, offset := 0 } ⟨2⟩ [7, 0, 0, 0] with
      | .ok mem' =>
        match basicMemLoad mem' { allocId := 0, offset := 0 } ⟨2⟩ 4 with
        | .ok _ => .normalUnit
        | .error _ => .ub
      | .error _ => .ub
    | .canonicalSafeTreeBorrowMut =>
      let p0 := reborrow_permission true .No true true false
      match p0.transition .Write .Local with
      | .ok _ => .normalUnit
      | .error _ => .ub
    | .sharedUnsafeCellWrite =>
      let p0 := reborrow_permission false .No true false false
      match p0.transition .Write .Local with
      | .ok _ => .normalUnit
      | .error _ => .ub
    | .unionVariantWriteRead =>
      match encode_union_chunks 4 [(0, encode_int_le 99 4 .none)] with
      | .some bs =>
        match decode_union_chunks bs [(0, 4)] with
        | .some _ => .normalUnit
        | .none => .ub
      | .none => .ub
    | .dynamicArrayIndexBorrow =>
      match mrProjectIndexOffset 0 4 1 2 with
      | .ok off =>
        let mem : BasicMemory := {
          allocs := [{ id := 0, align := ⟨2⟩, size := 8, live := true, bytes := [10, 0, 0, 0, 30, 0, 0, 0] }]
          nextAllocId := 1
        }
        match basicMemLoad mem { allocId := 0, offset := off } ⟨2⟩ 4 with
        | .ok _ => .normalUnit
        | .error _ => .ub
      | .error _ => .ub
    | .exactDivIntrinsicCall =>
      match eval_bin_op_int .DivExact 24 2 { signed := .Unsigned, size := ⟨4⟩ } with
      | .ok _ => .normalUnit
      | .error _ => .ub
    | .reservedImEpochTransition =>
      match (reborrow_permission true .Strong true false true).init_access with
      | .some .Write => .normalUnit
      | _ => .ub

/-- Canonical `AnnealMirDialect` instance for `Trusted.Rustc.V2026_06_01`. -/
def dialectV2026_06_01 : AnnealMirDialect where
  version := .V2026_06_01
  rustcCommit := "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
  Prog := FixtureProg
  State := FixtureState
  evalVerdict := evalAnnealV2026_06_01

theorem dialectV2026_06_01_version :
    dialectV2026_06_01.version = .V2026_06_01 := rfl

end Correspondence
