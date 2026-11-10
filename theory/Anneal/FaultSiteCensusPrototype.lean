import Trusted

namespace Anneal.FaultSiteCensusPrototype

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
# Track P Prototype: Independent MIR Fault-Site Census & Coverage Reconciler

This module implements the Lean 4 side of the Track P prototype for independent
MIR fault-site enumeration and fail-closed obligation coverage reconciliation:

1. **12 Canonical `MirFaultClass` Categories**:
   Enumerates the 12 runtime undefined-behavior classes modeled by
   `Trusted.MirSemantics`, with rank bijections (`0..11`) and canonical
   `snake_case` string conversions matching Rust's `MirFaultClass` 1-to-1.
2. **`FaultSite`, `PropertyStatus`, and `PropertyRegistry`**:
   Models per-site fault coordinates `(blockIdx, stmtIdx, faultClass)` and
   per-class verification status (`emittedAndVerified`, `unsupportedFailClosed`,
   `unemittedGap`).
3. **Construct-Precise Syntactic Census (`censusMirBodyFaultSites`)**:
   Walks `CapturedMir` basic blocks, statements, rvalues, places, operands, and
   terminators structurally without consulting `cargo-anneal`'s obligation
   generator, emitting duplicate-free canonically ordered `FaultSite` records
   (`censusMirBodyFaultSites_nodup`).
4. **Census Completeness & Construct Precision Theorems**:
   - `validMirPc_initMachineState` and `stepMirFn_preserves_validMirPc`
   - `stepMirFn_activeBody_fault_in_census` and `stepMirFn_fault_in_census`
   - Construct-level precision theorems proving that pure constructs (`.nop`,
     `.coverage`, `.constEvalCounter`, `.backwardIncompatibleDropHint`,
     in-bounds `.goto`, `.unwindTerminate`, `.inlineAsm`, non-indirect constants)
     emit `[]` and cannot fault with `.ub`, and that faulting constructs only
     emit their semantically justified subset of `MirFaultClass`.
   - Zero-census UB-freedom corollaries (`stepMirFn_ne_ub_of_site_uncensused`,
     `stepMirFn_ne_ub_of_empty_census`).
5. **Fail-Closed Coverage Reconciler & Witness Suite**:
   - `reconcileFaultCoverage` and `reconcileFaultCoverageWithRegistry`
   - `reconcileFaultCoverage_verified_iff`, `reconcileFaultCoverage_unknown_nonempty`,
     `reconcileFaultCoverageWithRegistry_rejects_unemitted`, and
     `reconcileFaultCoverage_mutation_detected`
   - Compile-time kernel-checked `by decide` witnesses covering pure no-op MIR
     and all 4 false-proof mutation probe scenarios (`0` `native_decide`).
-/

/-! ## 1. Canonical `MirFaultClass` Enumeration & Bijections -/

/--
The 12 canonical runtime undefined-behavior fault classes in `Runtime(PostCleanup)`
MIR execution (`Trusted.MirSemantics`).
-/
inductive MirFaultClass : Type where
  /-- Signed or unsigned integer arithmetic overflow (`AddUnchecked`, `SubUnchecked`,
      `MulUnchecked`, checked arithmetic assertion, `Neg` on `INT_MIN`, or byte-count
      multiplication overflow). -/
  | arithOverflow : MirFaultClass
  /-- Division or remainder by zero (`Div`, `Rem`, `exact_div`, `unchecked_div`,
      `unchecked_rem`). -/
  | divRemByZero : MirFaultClass
  /-- Bit-shift distance out of range (`Shl`, `Shr`, `ShlUnchecked`, `ShrUnchecked`,
      `unchecked_shl`, `unchecked_shr`). -/
  | shiftOverflow : MirFaultClass
  /-- Out-of-bounds array, slice, pointer-offset, global allocation, or CFG block
      index (`Index`, `ConstantIndex`, `Subslice`, `BinOp.offset`, `arith_offset`). -/
  | boundsCheck : MirFaultClass
  /-- Null, dangling, out-of-bounds, overlapping, or invalid-provenance pointer
      dereference or `copy_nonoverlapping` (`ProjectionElem.deref`, `Retag`). -/
  | ptrDerefInvalid : MirFaultClass
  /-- Misaligned pointer dereference, `copy_nonoverlapping`, or cast (`isAlignedOffset`). -/
  | ptrAlignMismatch : MirFaultClass
  /-- Tree Borrows permission violation (`.disabled` read/write, `.frozen` write,
      or active function-entry protector write conflict). -/
  | treeBorrowsViolation : MirFaultClass
  /-- Invalid scalar bit pattern, enum discriminant, bool/char validity, or
      violated `assume` condition (`WrappingRange`, `SetDiscriminant`, `Transmute`). -/
  | scalarNicheInvalid : MirFaultClass
  /-- Reading an uninitialized or dead local slot or uninitialized memory bytes. -/
  | uninitRead : MirFaultClass
  /-- Deallocating or overwriting a dead/out-of-bounds local or a local protected
      by an active function-entry protector (`StorageLive`, `StorageDead`). -/
  | storageLiveProtected : MirFaultClass
  /-- Indirect function-pointer signature/ABI mismatch, arity mismatch, invalid
      unwind ABI (`UnwindAction.unreachable`), or returning from a diverging call. -/
  | callAbiMismatch : MirFaultClass
  /-- Reaching `TerminatorKind.unreachable` or an unreachable intrinsic call. -/
  | unreachableTerminator : MirFaultClass
  deriving DecidableEq, Repr, BEq, Inhabited

instance : LawfulBEq MirFaultClass where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | nomatch h
  rfl {a} := by cases a <;> rfl

namespace MirFaultClass

/-- Complete duplicate-free list of all 12 `MirFaultClass` constructors in rank order. -/
def all : List MirFaultClass :=
  [ .arithOverflow
  , .divRemByZero
  , .shiftOverflow
  , .boundsCheck
  , .ptrDerefInvalid
  , .ptrAlignMismatch
  , .treeBorrowsViolation
  , .scalarNicheInvalid
  , .uninitRead
  , .storageLiveProtected
  , .callAbiMismatch
  , .unreachableTerminator
  ]

/-- `MirFaultClass.all` has exactly 12 elements. -/
@[simp]
theorem length_all : all.length = 12 := rfl

/-- Every `MirFaultClass` belongs to `MirFaultClass.all`. -/
@[simp]
theorem mem_all (c : MirFaultClass) : c ∈ all := by
  cases c <;> decide

/-- `MirFaultClass.all` is duplicate-free. -/
theorem nodup_all : all.Nodup := by
  decide

/-- 0-based canonical rank (`0..11`) of a `MirFaultClass`. -/
def toRank : MirFaultClass → Nat
  | .arithOverflow => 0
  | .divRemByZero => 1
  | .shiftOverflow => 2
  | .boundsCheck => 3
  | .ptrDerefInvalid => 4
  | .ptrAlignMismatch => 5
  | .treeBorrowsViolation => 6
  | .scalarNicheInvalid => 7
  | .uninitRead => 8
  | .storageLiveProtected => 9
  | .callAbiMismatch => 10
  | .unreachableTerminator => 11

/-- Partial inverse of `toRank` for ranks `0..11`. -/
def ofRank? : Nat → Option MirFaultClass
  | 0 => some .arithOverflow
  | 1 => some .divRemByZero
  | 2 => some .shiftOverflow
  | 3 => some .boundsCheck
  | 4 => some .ptrDerefInvalid
  | 5 => some .ptrAlignMismatch
  | 6 => some .treeBorrowsViolation
  | 7 => some .scalarNicheInvalid
  | 8 => some .uninitRead
  | 9 => some .storageLiveProtected
  | 10 => some .callAbiMismatch
  | 11 => some .unreachableTerminator
  | _ => none

/-- Every rank is strictly less than 12. -/
theorem toRank_lt_twelve (c : MirFaultClass) : c.toRank < 12 := by
  cases c <;> decide

/-- Round-trip identity `ofRank? (toRank c) = some c`. -/
@[simp]
theorem ofRank?_toRank (c : MirFaultClass) : ofRank? c.toRank = some c := by
  cases c <;> rfl

/-- `toRank` is injective. -/
theorem toRank_injective {c₁ c₂ : MirFaultClass} (h : c₁.toRank = c₂.toRank) :
    c₁ = c₂ := by
  have hOpt : ofRank? c₁.toRank = ofRank? c₂.toRank := congrArg ofRank? h
  rw [ofRank?_toRank, ofRank?_toRank] at hOpt
  injection hOpt

/-- Canonical `snake_case` identifier shared 1-to-1 with Rust's `MirFaultClass::as_str`. -/
def asStr : MirFaultClass → String
  | .arithOverflow => "arith_overflow"
  | .divRemByZero => "div_rem_by_zero"
  | .shiftOverflow => "shift_overflow"
  | .boundsCheck => "bounds_check"
  | .ptrDerefInvalid => "ptr_deref_invalid"
  | .ptrAlignMismatch => "ptr_align_mismatch"
  | .treeBorrowsViolation => "tree_borrows_violation"
  | .scalarNicheInvalid => "scalar_niche_invalid"
  | .uninitRead => "uninit_read"
  | .storageLiveProtected => "storage_live_protected"
  | .callAbiMismatch => "call_abi_mismatch"
  | .unreachableTerminator => "unreachable_terminator"

/-- Parse a canonical `snake_case` string into a `MirFaultClass`. -/
def fromStr? (s : String) : Option MirFaultClass :=
  all.find? (fun c => c.asStr == s)

/-- Round-trip identity `fromStr? (asStr c) = some c`. -/
@[simp]
theorem fromStr?_asStr (c : MirFaultClass) : fromStr? c.asStr = some c := by
  cases c <;> decide

/-- `asStr` is injective. -/
theorem asStr_injective {c₁ c₂ : MirFaultClass} (h : c₁.asStr = c₂.asStr) :
    c₁ = c₂ := by
  have hOpt : fromStr? c₁.asStr = fromStr? c₂.asStr := congrArg fromStr? h
  rw [fromStr?_asStr, fromStr?_asStr] at hOpt
  injection hOpt

/-- Inverse round-trip: if `fromStr? s = some c`, then `c.asStr = s`. -/
theorem asStr_fromStr? {s : String} {c : MirFaultClass}
    (h : fromStr? s = some c) : c.asStr = s := by
  have hBeq := @List.find?_some MirFaultClass (fun x => x.asStr == s) c all h
  exact beq_iff_eq.mp hBeq

end MirFaultClass

/-! ## 2. `FaultSite`, `PropertyStatus`, and `PropertyRegistry` -/

/--
A potential runtime UB fault site inside a `CapturedMir` body, identified by:
- `blockIdx : BasicBlockIdx` (0-based basic block index),
- `stmtIdx : Nat` (`0 .. statements.length - 1` for statements,
  `statements.length` for the block's terminator), and
- `faultClass : MirFaultClass`.
-/
abbrev FaultSite : Type := BasicBlockIdx × Nat × MirFaultClass

/-- Project the basic-block index from a `FaultSite`. -/
@[reducible]
def FaultSite.blockIdx (site : FaultSite) : BasicBlockIdx := site.1

/-- Project the statement/terminator index from a `FaultSite`. -/
@[reducible]
def FaultSite.stmtIdx (site : FaultSite) : Nat := site.2.1

/-- Project the `MirFaultClass` from a `FaultSite`. -/
@[reducible]
def FaultSite.faultClass (site : FaultSite) : MirFaultClass := site.2.2

/-- Dot-notation projection for `site.blockIdx` on `FaultSite` tuples. -/
@[reducible]
def _root_.Prod.blockIdx (site : FaultSite) : BasicBlockIdx := site.1

/-- Dot-notation projection for `site.stmtIdx` on `FaultSite` tuples. -/
@[reducible]
def _root_.Prod.stmtIdx (site : FaultSite) : Nat := site.2.1

/-- Dot-notation projection for `site.faultClass` on `FaultSite` tuples. -/
@[reducible]
def _root_.Prod.faultClass (site : FaultSite) : MirFaultClass := site.2.2

/--
Verification support status of a `MirFaultClass` in `cargo-anneal`'s
`PropertyRegistry`.
-/
inductive PropertyStatus : Type where
  /-- Obligations for this fault class are emitted by `cargo-anneal` and checked
      in the Lean 4 kernel. -/
  | emittedAndVerified : PropertyStatus
  /-- The construct or fault class is explicitly marked unsupported and fails
      closed (`UNKNOWN(UNSUPPORTED_CONSTRUCT)`). -/
  | unsupportedFailClosed : PropertyStatus
  /-- The obligation generator does not yet emit obligations for this fault
      class; any occurrence in a subject's census must fail closed. -/
  | unemittedGap : PropertyStatus
  deriving DecidableEq, Repr, BEq, Inhabited

instance : LawfulBEq PropertyStatus where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | nomatch h
  rfl {a} := by cases a <;> rfl

/-- True iff the `PropertyStatus` is `.emittedAndVerified`. -/
@[reducible]
def PropertyStatus.isVerified : PropertyStatus → Bool
  | .emittedAndVerified => true
  | _ => false

@[simp]
theorem PropertyStatus.isVerified_eq_true_iff (st : PropertyStatus) :
    st.isVerified = true ↔ st = .emittedAndVerified := by
  cases st <;> decide

/--
Total mapping from each `MirFaultClass` to its `PropertyStatus` in the
verification pipeline.
-/
abbrev PropertyRegistry : Type := MirFaultClass → PropertyStatus

/-- Registry in which all 12 `MirFaultClass` categories are emitted and verified. -/
def allVerifiedRegistry : PropertyRegistry :=
  fun _ => .emittedAndVerified

/-- Fail-closed empty registry in which all 12 classes are marked `.unemittedGap`. -/
def unemittedRegistry : PropertyRegistry :=
  fun _ => .unemittedGap

/-- Override a single `MirFaultClass` entry in `reg`. -/
def registryWithStatus
    (reg : PropertyRegistry) (cls : MirFaultClass) (status : PropertyStatus) :
    PropertyRegistry :=
  fun c => if c = cls then status else reg c

@[simp]
theorem registryWithStatus_self
    (reg : PropertyRegistry) (cls : MirFaultClass) (status : PropertyStatus) :
    registryWithStatus reg cls status cls = status := by
  simp [registryWithStatus]

@[simp]
theorem registryWithStatus_ne
    (reg : PropertyRegistry) (cls c : MirFaultClass) (status : PropertyStatus)
    (hNe : c ≠ cls) :
    registryWithStatus reg cls status c = reg c := by
  simp [registryWithStatus, hNe]

/-! ## 3. Construct-Precise Syntactic MIR Fault-Site Census -/

/--
Deduplicate and canonically order a list of `MirFaultClass` values by filtering
`MirFaultClass.all` (`0..11`).
-/
def dedupFaultClasses (raw : List MirFaultClass) : List MirFaultClass :=
  MirFaultClass.all.filter (fun c => raw.contains c)

/-- Membership in `dedupFaultClasses raw` is equivalent to membership in `raw`. -/
@[simp]
theorem mem_dedupFaultClasses_iff (raw : List MirFaultClass) (c : MirFaultClass) :
    c ∈ dedupFaultClasses raw ↔ c ∈ raw := by
  simp [dedupFaultClasses, List.mem_filter, MirFaultClass.mem_all]

/-- `dedupFaultClasses raw` is always duplicate-free. -/
theorem nodup_dedupFaultClasses (raw : List MirFaultClass) :
    (dedupFaultClasses raw).Nodup := by
  exact MirFaultClass.nodup_all.filter _

@[simp]
theorem dedupFaultClasses_nil : dedupFaultClasses [] = [] := rfl

/--
Fault classes that can be triggered by evaluating a single `ProjectionElem`
along a place projection path.
-/
def censusProjectionElemFaultClasses : ProjectionElem → List MirFaultClass
  | .deref => [.ptrDerefInvalid, .ptrAlignMismatch, .treeBorrowsViolation]
  | .field _ _ => []
  | .index _ => [.boundsCheck, .uninitRead]
  | .constantIndex _ _ _ => [.boundsCheck]
  | .subslice _ _ _ => [.boundsCheck]
  | .downcast _ _ => [.scalarNicheInvalid]
  | .opaqueCast _ => []
  | .unwrapUnsafeBinder _ => []

/--
Fault classes that can be triggered when reading from `place : Place`
(`evalPlaceRead`, `evalOperand (.copy place)`, `evalOperand (.move place)`).
-/
def censusPlaceReadFaultClasses (place : Place) : List MirFaultClass :=
  .uninitRead :: (place.projection.flatMap censusProjectionElemFaultClasses)

/--
Fault classes that can be triggered when writing to `place : Place`
(`writePlaceValue`, `evalPlaceWrite`, `StatementKind.assign`).
-/
def censusPlaceWriteFaultClasses (place : Place) : List MirFaultClass :=
  match place.projection with
  | [] => [.storageLiveProtected, .treeBorrowsViolation]
  | projs =>
    [.storageLiveProtected, .treeBorrowsViolation, .uninitRead] ++
      projs.flatMap censusProjectionElemFaultClasses

/--
Fault classes that can be triggered when creating a reference or raw pointer to
`place : Place` (`Rvalue.ref`, `Rvalue.rawPtr`).
-/
def censusPlaceRefFaultClasses (place : Place) : List MirFaultClass :=
  [.uninitRead, .ptrDerefInvalid, .ptrAlignMismatch, .treeBorrowsViolation] ++
    place.projection.flatMap censusProjectionElemFaultClasses

/--
Fault classes that can be triggered by evaluating a `ConstValue` in
`evalOperand (.constant c)`.

In `Trusted.MirSemantics.evalOperand`, `.zeroSized`, `.scalar`, `.slice`, and
`.unevaluated` never return `.ub`; only `.indirect allocId offset` can return
`.ub` when the global allocation slice is out of bounds or fails byte decoding.
-/
def censusConstValueFaultClasses : ConstValue → List MirFaultClass
  | .indirect _ _ => [.boundsCheck, .scalarNicheInvalid, .uninitRead]
  | _ => []

/--
Fault classes that can be triggered by evaluating an `Operand`.
-/
def censusOperandFaultClasses : Operand → List MirFaultClass
  | .copy place => censusPlaceReadFaultClasses place
  | .move place => censusPlaceReadFaultClasses place
  | .constant c => censusConstValueFaultClasses c.val

/--
Fault classes that can be triggered by a `BinOp` in `evalRvalue (.binaryOp op lhs rhs)`
(excluding the operand evaluations of `lhs` and `rhs` themselves).
-/
def censusBinOpFaultClasses : BinOp → List MirFaultClass
  | .add | .sub | .mul
  | .addUnchecked | .subUnchecked | .mulUnchecked
  | .addWithOverflow | .subWithOverflow | .mulWithOverflow =>
    [.arithOverflow]
  | .div | .rem =>
    [.arithOverflow, .divRemByZero]
  | .shl | .shr | .shlUnchecked | .shrUnchecked =>
    [.shiftOverflow]
  | .offset =>
    [.arithOverflow, .boundsCheck, .ptrDerefInvalid]
  | .bitXor | .bitAnd | .bitOr
  | .eq | .lt | .le | .ne | .ge | .gt | .cmp =>
    [.scalarNicheInvalid]

/--
Fault classes that can be triggered by a `UnOp` in `evalRvalue (.unaryOp op val)`.
-/
def censusUnOpFaultClasses : UnOp → List MirFaultClass
  | .neg => [.arithOverflow]
  | .not => [.scalarNicheInvalid]
  | .ptrMetadata => [.ptrDerefInvalid]

/--
Fault classes that can be triggered by a `NullOp` in `evalRvalue (.nullaryOp op ty)`.
-/
def censusNullOpFaultClasses : NullOp → List MirFaultClass
  | .sizeOf | .alignOf | .offsetOf _ => [.scalarNicheInvalid]
  | .ubChecks | .contractChecks => []

/--
Fault classes that can be triggered by a `CastKind` in `evalRvalue (.cast kind op ty)`.
-/
def censusCastKindFaultClasses : CastKind → List MirFaultClass
  | .intToInt | .floatToInt | .floatToFloat | .intToFloat =>
    [.scalarNicheInvalid]
  | .transmute | .subtype =>
    [.scalarNicheInvalid, .uninitRead]
  | .pointerExposeProvenance | .pointerWithExposedProvenance
  | .pointerCoercion _ | .ptrToPtr | .fnPtrToPtr =>
    [.boundsCheck, .ptrDerefInvalid, .ptrAlignMismatch, .scalarNicheInvalid]

/--
Fault classes that can be triggered by evaluating an `Rvalue`.
-/
def censusRvalueFaultClasses : Rvalue → List MirFaultClass
  | .use op => censusOperandFaultClasses op
  | .repeat op _ => censusOperandFaultClasses op ++ [.scalarNicheInvalid]
  | .ref _ place => censusPlaceRefFaultClasses place
  | .threadLocalRef _ => [.ptrDerefInvalid]
  | .rawPtr _ place => censusPlaceRefFaultClasses place
  | .len place => censusPlaceReadFaultClasses place ++ [.boundsCheck]
  | .cast kind op _ => censusOperandFaultClasses op ++ censusCastKindFaultClasses kind
  | .binaryOp op lhs rhs =>
    censusOperandFaultClasses lhs ++
      censusOperandFaultClasses rhs ++
      censusBinOpFaultClasses op
  | .nullaryOp op _ => censusNullOpFaultClasses op
  | .unaryOp op val => censusOperandFaultClasses val ++ censusUnOpFaultClasses op
  | .discriminant place => censusPlaceReadFaultClasses place ++ [.scalarNicheInvalid]
  | .aggregate _ ops =>
    (ops.flatMap censusOperandFaultClasses) ++ [.scalarNicheInvalid]
  | .shallowInitBox op _ =>
    censusOperandFaultClasses op ++ [.ptrDerefInvalid, .ptrAlignMismatch]
  | .copyForDeref place =>
    censusPlaceReadFaultClasses place ++ [.ptrDerefInvalid]
  | .wrapUnsafeBinder op _ =>
    censusOperandFaultClasses op ++ [.scalarNicheInvalid]

/--
Fault classes that can be triggered by a `NonDivergingIntrinsic`.
-/
def censusIntrinsicFaultClasses : NonDivergingIntrinsic → List MirFaultClass
  | .assume op =>
    censusOperandFaultClasses op ++ [.scalarNicheInvalid]
  | .copyNonOverlapping src dst count =>
    censusOperandFaultClasses src ++
      censusOperandFaultClasses dst ++
      censusOperandFaultClasses count ++
      [ .arithOverflow
      , .boundsCheck
      , .ptrDerefInvalid
      , .ptrAlignMismatch
      , .treeBorrowsViolation
      , .scalarNicheInvalid
      , .uninitRead
      ]

/--
Canonically ordered, duplicate-free list of `MirFaultClass` categories that a
`StatementKind` can trigger under `Trusted.MirSemantics.evalStmt`.
-/
def censusStmtFaultClasses (kind : StatementKind) : List MirFaultClass :=
  let raw : List MirFaultClass :=
    match kind with
    | .nop => []
    | .coverage => []
    | .constEvalCounter => []
    | .backwardIncompatibleDropHint _ => []
    | .storageLive _ => [.storageLiveProtected]
    | .storageDead _ => [.storageLiveProtected]
    | .placeMention place =>
      .uninitRead :: (place.projection.flatMap censusProjectionElemFaultClasses)
    | .deinit place =>
      .uninitRead :: (place.projection.flatMap censusProjectionElemFaultClasses)
    | .retag _ place =>
      censusPlaceReadFaultClasses place ++
        [.boundsCheck, .ptrDerefInvalid, .ptrAlignMismatch, .treeBorrowsViolation]
    | .setDiscriminant place _ =>
      match place.projection with
      | [] => [.scalarNicheInvalid, .uninitRead]
      | _ =>
        censusPlaceReadFaultClasses place ++
          censusPlaceWriteFaultClasses place ++
          [.scalarNicheInvalid]
    | .intrinsic intr => censusIntrinsicFaultClasses intr
    | .assign dst rv =>
      censusPlaceWriteFaultClasses dst ++ censusRvalueFaultClasses rv
  dedupFaultClasses raw

/--
Successor basic-block indices targeted by an `UnwindAction`.
-/
def unwindTargets : UnwindAction → List BasicBlockIdx
  | .cleanup cleanupBb => [cleanupBb]
  | _ => []

/--
All intra-procedural successor basic-block indices syntactically targeted by a
`TerminatorKind`.
-/
def terminatorTargets : TerminatorKind → List BasicBlockIdx
  | .goto target => [target]
  | .switchInt _ targets => targets.otherwise :: targets.branches.map Prod.snd
  | .unwindResume => []
  | .unwindTerminate => []
  | .return_ => []
  | .unreachable => []
  | .drop _ target unwind => target :: unwindTargets unwind
  | .call _ _ _ (some targetBb) unwind => targetBb :: unwindTargets unwind
  | .call _ _ _ none unwind => unwindTargets unwind
  | .tailCall _ _ => []
  | .assert _ _ target unwind => target :: unwindTargets unwind
  | .inlineAsm _ targets unwind => targets ++ unwindTargets unwind

/--
Additional fault classes contributed by a direct call target `defPath` in
`TerminatorKind.call` (such as inline Rust compiler intrinsics or
`unreachable_unchecked`).
-/
def censusCalleeDefPathFaultClasses (defPath : DefPath) : List MirFaultClass :=
  if isUnreachableCallTarget defPath then
    [.unreachableTerminator]
  else if defPath == "core::intrinsics::exact_div" ||
          defPath == "std::intrinsics::exact_div" then
    [.arithOverflow, .divRemByZero]
  else
    match classifyRustIntrinsic? defPath with
    | some .arithOffset => [.arithOverflow, .boundsCheck, .ptrDerefInvalid]
    | some .uncheckedAdd | some .uncheckedSub | some .uncheckedMul => [.arithOverflow]
    | some .uncheckedDiv | some .uncheckedRem => [.arithOverflow, .divRemByZero]
    | some .uncheckedShl | some .uncheckedShr => [.shiftOverflow]
    | some .ctlzNonzero | some .cttzNonzero => [.scalarNicheInvalid]
    | some .sizeOfVal | some .alignOfVal => [.arithOverflow, .ptrDerefInvalid, .scalarNicheInvalid]
    | some .constEvalSelect => [.callAbiMismatch, .scalarNicheInvalid]
    | _ => []

/--
Canonically ordered, duplicate-free list of `MirFaultClass` categories that a
`TerminatorKind` can trigger under `Trusted.MirSemantics.evalTerminator` (plus
out-of-bounds CFG target checks against `numBlocks = length body.basicBlocks`).
-/
def censusTerminatorFaultClasses
    (numBlocks : Nat) (kind : TerminatorKind) : List MirFaultClass :=
  let targetOob : List MirFaultClass :=
    if (terminatorTargets kind).any (fun t => decide (numBlocks ≤ t)) then
      [.boundsCheck]
    else
      []
  let raw : List MirFaultClass :=
    match kind with
    | .goto _ => targetOob
    | .unwindTerminate => []
    | .inlineAsm _ _ _ => []
    | .unreachable => [.unreachableTerminator]
    | .unwindResume => [.callAbiMismatch]
    | .return_ => [.uninitRead, .treeBorrowsViolation, .callAbiMismatch]
    | .switchInt discr _ =>
      censusOperandFaultClasses discr ++ [.scalarNicheInvalid] ++ targetOob
    | .drop place _ _ =>
      censusPlaceReadFaultClasses place ++ targetOob
    | .assert cond _ _ unwind =>
      let unwindClasses :=
        match unwind with
        | .unreachable =>
          [.arithOverflow, .divRemByZero, .shiftOverflow, .boundsCheck, .unreachableTerminator]
        | _ => [.callAbiMismatch]
      censusOperandFaultClasses cond ++ [.scalarNicheInvalid] ++ unwindClasses ++ targetOob
    | .call func args destination _ unwind =>
      let calleeClasses :=
        match extractCalleeDefPath? func with
        | some defPath => censusCalleeDefPathFaultClasses defPath
        | none => [.ptrDerefInvalid]
      let unwindClasses :=
        match unwind with
        | .unreachable => [.unreachableTerminator]
        | _ => []
      censusOperandFaultClasses func ++
        (args.flatMap censusOperandFaultClasses) ++
        censusPlaceWriteFaultClasses destination ++
        [.callAbiMismatch] ++
        calleeClasses ++
        unwindClasses ++
        targetOob
    | .tailCall func args =>
      let calleeClasses :=
        match extractCalleeDefPath? func with
        | some _ => []
        | none => [.ptrDerefInvalid]
      censusOperandFaultClasses func ++
        (args.flatMap censusOperandFaultClasses) ++
        [.callAbiMismatch] ++
        calleeClasses
  dedupFaultClasses raw

/--
Enumerate all `FaultSite` entries for statement `stmtIdx` inside basic block
`blockIdx`.
-/
def censusStmtFaultSites
    (blockIdx : BasicBlockIdx) (stmtIdx : Nat) (stmt : Statement) :
    List FaultSite :=
  (censusStmtFaultClasses stmt.kind).map (fun cls => (blockIdx, stmtIdx, cls))

/--
Enumerate all `FaultSite` entries for the terminator at `stmtIdx = length bb.statements`
inside basic block `blockIdx`.
-/
def censusTerminatorFaultSites
    (numBlocks : Nat) (blockIdx : BasicBlockIdx) (stmtIdx : Nat) (term : Terminator) :
    List FaultSite :=
  (censusTerminatorFaultClasses numBlocks term.kind).map (fun cls => (blockIdx, stmtIdx, cls))

/--
Enumerate all `FaultSite` entries for a list of statements starting at `stmtIdx`
inside basic block `blockIdx`.
-/
def censusStmtsAux
    (blockIdx : BasicBlockIdx) (stmtIdx : Nat) : List Statement → List FaultSite
  | [] => []
  | stmt :: rest =>
    censusStmtFaultSites blockIdx stmtIdx stmt ++
      censusStmtsAux blockIdx (stmtIdx + 1) rest

/--
Enumerate all `FaultSite` entries (statements followed by the terminator at
`stmtIdx = length bb.statements`) for basic block `blockIdx`.
-/
def censusBlockFaultSites
    (numBlocks : Nat) (blockIdx : BasicBlockIdx) (bb : BasicBlockData) :
    List FaultSite :=
  censusStmtsAux blockIdx 0 bb.statements ++
    censusTerminatorFaultSites numBlocks blockIdx (length bb.statements) bb.terminator

/--
Enumerate all `FaultSite` entries across a list of basic blocks starting at
`blockIdx`.
-/
def censusBlocksAux
    (numBlocks : Nat) (blockIdx : BasicBlockIdx) :
    List BasicBlockData → List FaultSite
  | [] => []
  | bb :: rest =>
    censusBlockFaultSites numBlocks blockIdx bb ++
      censusBlocksAux numBlocks (blockIdx + 1) rest

/--
Independent syntactic fault-site census of a `CapturedMir` body.
-/
def censusMirBodyFaultSites (body : CapturedMir) : List FaultSite :=
  censusBlocksAux (length body.basicBlocks) 0 body.basicBlocks

/-! ## 4. Duplicate-Freeness (`Nodup`) of `censusMirBodyFaultSites` -/

private theorem nodup_map_of_injective {α β : Type} (f : α → β)
    (hInj : ∀ x y, f x = f y → x = y) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => .nil
  | x :: xs, .cons hNotMem hTail =>
    .cons
      (fun y hMem hEq => by
        rcases List.mem_map.mp hMem with ⟨x', hMem', rfl⟩
        exact hNotMem x' hMem' (hInj x x' hEq))
      (nodup_map_of_injective f hInj hTail)

private theorem nodup_append_of_disjoint {α : Type} :
    ∀ {xs ys : List α},
      xs.Nodup → ys.Nodup → (∀ x, x ∈ xs → x ∈ ys → False) → (xs ++ ys).Nodup
  | [], _, _, hYs, _ => hYs
  | x :: xs, ys, .cons hNotXs hXs, hYs, hDisj =>
    .cons
      (fun y hMem hEq => by
        subst hEq
        rcases List.mem_append.mp hMem with hInXs | hInYs
        · exact hNotXs x hInXs rfl
        · exact hDisj x (List.Mem.head xs) hInYs)
      (nodup_append_of_disjoint hXs hYs (fun z hInXs hInYs =>
        hDisj z (List.Mem.tail x hInXs) hInYs))

private theorem nodup_map_site (blockIdx stmtIdx : Nat) {cs : List MirFaultClass}
    (hNodup : cs.Nodup) :
    (cs.map (fun cls => (blockIdx, stmtIdx, cls))).Nodup := by
  refine nodup_map_of_injective (fun cls => (blockIdx, stmtIdx, cls)) ?_ hNodup
  intro c₁ c₂ hEq
  injection hEq with _ hTail
  injection hTail

private theorem mem_censusStmtFaultSites_coords
    {blockIdx stmtIdx : Nat} {stmt : Statement} {site : FaultSite}
    (hMem : site ∈ censusStmtFaultSites blockIdx stmtIdx stmt) :
    site.1 = blockIdx ∧ site.2.1 = stmtIdx := by
  simp only [censusStmtFaultSites, List.mem_map] at hMem
  rcases hMem with ⟨cls, _, rfl⟩
  exact ⟨rfl, rfl⟩

private theorem mem_censusTerminatorFaultSites_coords
    {numBlocks blockIdx stmtIdx : Nat} {term : Terminator} {site : FaultSite}
    (hMem : site ∈ censusTerminatorFaultSites numBlocks blockIdx stmtIdx term) :
    site.1 = blockIdx ∧ site.2.1 = stmtIdx := by
  simp only [censusTerminatorFaultSites, List.mem_map] at hMem
  rcases hMem with ⟨cls, _, rfl⟩
  exact ⟨rfl, rfl⟩

private theorem mem_censusStmtsAux_coords
    (blockIdx : BasicBlockIdx) :
    ∀ (stmts : List Statement) (baseIdx : Nat) (site : FaultSite),
      site ∈ censusStmtsAux blockIdx baseIdx stmts →
      site.1 = blockIdx ∧ baseIdx ≤ site.2.1 ∧ site.2.1 < baseIdx + length stmts
  | [], _, _, hMem => by nomatch hMem
  | stmt :: rest, baseIdx, site, hMem => by
    simp only [censusStmtsAux, List.mem_append] at hMem
    have hLen : length (stmt :: rest) = length rest + 1 := rfl
    rcases hMem with hHead | hTail
    · rcases mem_censusStmtFaultSites_coords hHead with ⟨hB, hS⟩
      refine ⟨hB, by omega, ?_⟩
      rw [hLen]; omega
    · rcases mem_censusStmtsAux_coords blockIdx rest (baseIdx + 1) site hTail with
        ⟨hB, hGe, hLt⟩
      refine ⟨hB, by omega, ?_⟩
      rw [hLen]; omega

private theorem nodup_censusStmtsAux (blockIdx : BasicBlockIdx) :
    ∀ (stmts : List Statement) (baseIdx : Nat),
      (censusStmtsAux blockIdx baseIdx stmts).Nodup
  | [], _ => .nil
  | stmt :: rest, baseIdx => by
    simp only [censusStmtsAux]
    refine nodup_append_of_disjoint ?_ (nodup_censusStmtsAux blockIdx rest (baseIdx + 1)) ?_
    · exact nodup_map_site blockIdx baseIdx (nodup_dedupFaultClasses _)
    · intro site hHead hTail
      have hS₁ := (mem_censusStmtFaultSites_coords hHead).2
      have hS₂ := (mem_censusStmtsAux_coords blockIdx rest (baseIdx + 1) site hTail).2.1
      omega

private theorem mem_censusBlockFaultSites_blockIdx
    {numBlocks blockIdx : Nat} {bb : BasicBlockData} {site : FaultSite}
    (hMem : site ∈ censusBlockFaultSites numBlocks blockIdx bb) :
    site.1 = blockIdx := by
  simp only [censusBlockFaultSites, List.mem_append] at hMem
  rcases hMem with hStmts | hTerm
  · exact (mem_censusStmtsAux_coords blockIdx bb.statements 0 site hStmts).1
  · exact (mem_censusTerminatorFaultSites_coords hTerm).1

private theorem nodup_censusBlockFaultSites
    (numBlocks : Nat) (blockIdx : BasicBlockIdx) (bb : BasicBlockData) :
    (censusBlockFaultSites numBlocks blockIdx bb).Nodup := by
  simp only [censusBlockFaultSites]
  refine nodup_append_of_disjoint (nodup_censusStmtsAux blockIdx bb.statements 0) ?_ ?_
  · exact nodup_map_site blockIdx (length bb.statements) (nodup_dedupFaultClasses _)
  · intro site hStmts hTerm
    have hLt := (mem_censusStmtsAux_coords blockIdx bb.statements 0 site hStmts).2.2
    have hEq := (mem_censusTerminatorFaultSites_coords hTerm).2
    omega

private theorem mem_censusBlocksAux_blockIdx_ge
    (numBlocks : Nat) :
    ∀ (bbs : List BasicBlockData) (baseIdx : Nat) (site : FaultSite),
      site ∈ censusBlocksAux numBlocks baseIdx bbs →
      baseIdx ≤ site.1
  | [], _, _, hMem => by nomatch hMem
  | bb :: rest, baseIdx, site, hMem => by
    simp only [censusBlocksAux, List.mem_append] at hMem
    rcases hMem with hHead | hTail
    · have hB : site.1 = baseIdx := mem_censusBlockFaultSites_blockIdx hHead
      rw [hB]
      exact Nat.le_refl baseIdx
    · have hGe : baseIdx + 1 ≤ site.1 :=
        mem_censusBlocksAux_blockIdx_ge numBlocks rest (baseIdx + 1) site hTail
      exact Nat.le_of_succ_le hGe

private theorem nodup_censusBlocksAux (numBlocks : Nat) :
    ∀ (bbs : List BasicBlockData) (baseIdx : Nat),
      (censusBlocksAux numBlocks baseIdx bbs).Nodup
  | [], _ => .nil
  | bb :: rest, baseIdx => by
    simp only [censusBlocksAux]
    refine nodup_append_of_disjoint
      (nodup_censusBlockFaultSites numBlocks baseIdx bb)
      (nodup_censusBlocksAux numBlocks rest (baseIdx + 1)) ?_
    intro site hHead hTail
    have hB₁ : site.1 = baseIdx := mem_censusBlockFaultSites_blockIdx hHead
    have hB₂ : baseIdx + 1 ≤ site.1 :=
      mem_censusBlocksAux_blockIdx_ge numBlocks rest (baseIdx + 1) site hTail
    rw [hB₁] at hB₂
    exact Nat.not_succ_le_self baseIdx hB₂

/--
Every fault-site list produced by `censusMirBodyFaultSites body` is strictly
duplicate-free (`Nodup`).
-/
theorem censusMirBodyFaultSites_nodup (body : CapturedMir) :
    (censusMirBodyFaultSites body).Nodup :=
  nodup_censusBlocksAux (length body.basicBlocks) body.basicBlocks 0

/-! ## 5. Construct-Level Precision & Non-Overapproximation Theorems -/

@[simp]
theorem censusStmtFaultClasses_nop :
    censusStmtFaultClasses .nop = [] := rfl

@[simp]
theorem censusStmtFaultClasses_coverage :
    censusStmtFaultClasses .coverage = [] := rfl

@[simp]
theorem censusStmtFaultClasses_constEvalCounter :
    censusStmtFaultClasses .constEvalCounter = [] := rfl

@[simp]
theorem censusStmtFaultClasses_dropHint (place : Place) :
    censusStmtFaultClasses (.backwardIncompatibleDropHint place) = [] := rfl

@[simp]
theorem censusStmtFaultClasses_storageLive (loc : Local) :
    censusStmtFaultClasses (.storageLive loc) = [.storageLiveProtected] := rfl

@[simp]
theorem censusStmtFaultClasses_storageDead (loc : Local) :
    censusStmtFaultClasses (.storageDead loc) = [.storageLiveProtected] := rfl

@[simp]
theorem censusTerminatorFaultClasses_unwindTerminate (numBlocks : Nat) :
    censusTerminatorFaultClasses numBlocks .unwindTerminate = [] := rfl

@[simp]
theorem censusTerminatorFaultClasses_inlineAsm
    (numBlocks : Nat) (template : String) (targets : List BasicBlockIdx) (unwind : UnwindAction) :
    censusTerminatorFaultClasses numBlocks (.inlineAsm template targets unwind) = [] := rfl

@[simp]
theorem censusTerminatorFaultClasses_unreachable (numBlocks : Nat) :
    censusTerminatorFaultClasses numBlocks .unreachable = [.unreachableTerminator] := rfl

@[simp]
theorem censusTerminatorFaultClasses_unwindResume (numBlocks : Nat) :
    censusTerminatorFaultClasses numBlocks .unwindResume = [.callAbiMismatch] := rfl

@[simp]
theorem censusTerminatorFaultClasses_return (numBlocks : Nat) :
    censusTerminatorFaultClasses numBlocks .return_ =
      [.treeBorrowsViolation, .uninitRead, .callAbiMismatch] := rfl

theorem censusTerminatorFaultClasses_goto_inBounds
    (numBlocks : Nat) (target : BasicBlockIdx) (hIn : target < numBlocks) :
    censusTerminatorFaultClasses numBlocks (.goto target) = [] := by
  have hNotLe : ¬ (numBlocks ≤ target) := Nat.not_le_of_lt hIn
  simp [censusTerminatorFaultClasses, terminatorTargets, hNotLe]

theorem censusTerminatorFaultClasses_goto_outOfBounds
    (numBlocks : Nat) (target : BasicBlockIdx) (hOob : numBlocks ≤ target) :
    censusTerminatorFaultClasses numBlocks (.goto target) = [.boundsCheck] := by
  simp [censusTerminatorFaultClasses, terminatorTargets, hOob]
  rfl

@[simp]
theorem censusBinOpFaultClasses_add :
    censusBinOpFaultClasses .add = [.arithOverflow] := rfl

@[simp]
theorem censusBinOpFaultClasses_div :
    censusBinOpFaultClasses .div = [.arithOverflow, .divRemByZero] := rfl

@[simp]
theorem censusBinOpFaultClasses_shl :
    censusBinOpFaultClasses .shl = [.shiftOverflow] := rfl

@[simp]
theorem censusBinOpFaultClasses_offset :
    censusBinOpFaultClasses .offset = [.arithOverflow, .boundsCheck, .ptrDerefInvalid] := rfl

/--
Non-overapproximation witness: `StorageLive` only emits `[.storageLiveProtected]`
(1 of 12 classes) and never emits arithmetic, division, or shift fault classes.
-/
theorem storageLive_strict_subset_all (loc : Local) :
    (censusStmtFaultClasses (.storageLive loc)).length < MirFaultClass.all.length ∧
    MirFaultClass.arithOverflow ∉ censusStmtFaultClasses (.storageLive loc) ∧
    MirFaultClass.divRemByZero ∉ censusStmtFaultClasses (.storageLive loc) := by
  dsimp only [censusStmtFaultClasses]
  decide

/--
Pure no-fault statements never evaluate to `MirStepNode.fail .ub` in `evalStmt`.
-/
theorem evalStmt_pure_constructs_ne_ub
    (s : MachineState) (span : String) (place : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt s ⟨.nop, span⟩ localDecls layouts ≠ MirStepNode.fail .ub ∧
    evalStmt s ⟨.coverage, span⟩ localDecls layouts ≠ MirStepNode.fail .ub ∧
    evalStmt s ⟨.constEvalCounter, span⟩ localDecls layouts ≠ MirStepNode.fail .ub ∧
    evalStmt s ⟨.backwardIncompatibleDropHint place, span⟩ localDecls layouts ≠
      MirStepNode.fail .ub := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> nomatch h

/--
Pure no-fault terminators (`.goto`, `.unwindTerminate`, `.inlineAsm`) never
evaluate to `MirStepNode.fail .ub` in `evalTerminator`.
-/
theorem evalTerminator_pure_constructs_ne_ub
    (s : MachineState) (span : String) (target : BasicBlockIdx)
    (template : String) (targets : List BasicBlockIdx) (unwind : UnwindAction)
    (currentBody : Option CapturedMir) :
    evalTerminator s ⟨.goto target, span⟩ currentBody ≠ MirStepNode.fail .ub ∧
    evalTerminator s ⟨.unwindTerminate, span⟩ currentBody ≠ MirStepNode.fail .ub ∧
    evalTerminator s ⟨.inlineAsm template targets unwind, span⟩ currentBody ≠
      MirStepNode.fail .ub := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> nomatch h

/--
Evaluating a constant operand whose value is not `.indirect` emits `[]` in
`censusOperandFaultClasses` and never returns `.ub` in `evalOperand`.
-/
theorem evalOperand_constant_non_indirect_ne_ub
    (locals : List LocalSlot) (c : ConstOperand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (hNonIndirect : ∀ allocId offset, c.val ≠ .indirect allocId offset) :
    censusOperandFaultClasses (.constant c) = [] ∧
    evalOperand locals (.constant c) borrows globals layouts callerLocals ≠ .ub := by
  rcases c with ⟨ty, val⟩
  cases val with
  | zeroSized =>
    refine ⟨rfl, ?_⟩
    intro h; nomatch h
  | scalar cs =>
    cases cs with
    | int s =>
      refine ⟨rfl, ?_⟩
      intro h; nomatch h
    | ptr p sz =>
      refine ⟨rfl, ?_⟩
      intro h; nomatch h
  | slice cs lenMeta =>
    cases cs with
    | int s =>
      refine ⟨rfl, ?_⟩
      intro h
      dsimp only [evalOperand, evalConstValue] at h
      nomatch h
    | ptr p sz =>
      refine ⟨rfl, ?_⟩
      intro h
      dsimp only [evalOperand, evalConstValue] at h
      nomatch h
  | unevaluated path =>
    refine ⟨rfl, ?_⟩
    intro h; nomatch h
  | indirect allocId offset =>
    exact False.elim (hNonIndirect allocId offset rfl)

/-! ## 6. Census Membership Lemmas & Completeness over `stepMirFn` -/

/--
If `cls ∈ censusStmtFaultClasses stmt.kind` and `get? bb.statements stmtIdx = some stmt`,
then `(blockIdx, stmtIdx, cls) ∈ censusStmtsAux blockIdx 0 bb.statements`.
-/
theorem mem_censusStmtsAux_of_get?
    (blockIdx : BasicBlockIdx) :
    ∀ (stmts : List Statement) (baseIdx idx : Nat) (stmt : Statement) (cls : MirFaultClass),
      get? stmts idx = some stmt →
      cls ∈ censusStmtFaultClasses stmt.kind →
      (blockIdx, baseIdx + idx, cls) ∈ censusStmtsAux blockIdx baseIdx stmts
  | [], _, idx, _, _, hGet, _ => by
    cases idx <;> nomatch hGet
  | hd :: tl, baseIdx, 0, stmt, cls, hGet, hCls => by
    change some hd = some stmt at hGet
    injection hGet with hEq
    subst hEq
    simp only [Nat.add_zero, censusStmtsAux, List.mem_append]
    left
    simp only [censusStmtFaultSites, List.mem_map]
    exact ⟨cls, hCls, rfl⟩
  | hd :: tl, baseIdx, n + 1, stmt, cls, hGet, hCls => by
    change get? tl n = some stmt at hGet
    simp only [censusStmtsAux, List.mem_append]
    right
    have ih := mem_censusStmtsAux_of_get? blockIdx tl (baseIdx + 1) n stmt cls hGet hCls
    have hAdd : baseIdx + 1 + n = baseIdx + (n + 1) := by omega
    rw [hAdd] at ih
    exact ih

/--
If `get? bb.statements stmtIdx = some stmt` and `cls ∈ censusStmtFaultClasses stmt.kind`,
then `(blockIdx, stmtIdx, cls) ∈ censusBlockFaultSites numBlocks blockIdx bb`.
-/
theorem mem_censusBlockFaultSites_of_stmt
    (numBlocks : Nat) (blockIdx : BasicBlockIdx) (bb : BasicBlockData)
    (stmtIdx : Nat) (stmt : Statement) (cls : MirFaultClass)
    (hStmt : get? bb.statements stmtIdx = some stmt)
    (hCls : cls ∈ censusStmtFaultClasses stmt.kind) :
    (blockIdx, stmtIdx, cls) ∈ censusBlockFaultSites numBlocks blockIdx bb := by
  simp only [censusBlockFaultSites, List.mem_append]
  left
  have h := mem_censusStmtsAux_of_get? blockIdx bb.statements 0 stmtIdx stmt cls hStmt hCls
  simpa using h

/--
If `cls ∈ censusTerminatorFaultClasses numBlocks bb.terminator.kind`, then
`(blockIdx, length bb.statements, cls) ∈ censusBlockFaultSites numBlocks blockIdx bb`.
-/
theorem mem_censusBlockFaultSites_of_terminator
    (numBlocks : Nat) (blockIdx : BasicBlockIdx) (bb : BasicBlockData)
    (cls : MirFaultClass)
    (hCls : cls ∈ censusTerminatorFaultClasses numBlocks bb.terminator.kind) :
    (blockIdx, length bb.statements, cls) ∈ censusBlockFaultSites numBlocks blockIdx bb := by
  simp only [censusBlockFaultSites, List.mem_append]
  right
  simp only [censusTerminatorFaultSites, List.mem_map]
  exact ⟨cls, hCls, rfl⟩

/--
If `get? bbs idx = some bb` and `site ∈ censusBlockFaultSites numBlocks (baseIdx + idx) bb`,
then `site ∈ censusBlocksAux numBlocks baseIdx bbs`.
-/
theorem mem_censusBlocksAux_of_get?
    (numBlocks : Nat) :
    ∀ (bbs : List BasicBlockData) (baseIdx idx : Nat) (bb : BasicBlockData) (site : FaultSite),
      get? bbs idx = some bb →
      site ∈ censusBlockFaultSites numBlocks (baseIdx + idx) bb →
      site ∈ censusBlocksAux numBlocks baseIdx bbs
  | [], _, idx, _, _, hGet, _ => by
    cases idx <;> nomatch hGet
  | hd :: tl, baseIdx, 0, bb, site, hGet, hSite => by
    change some hd = some bb at hGet
    injection hGet with hEq
    subst hEq
    simp only [Nat.add_zero] at hSite
    simp only [censusBlocksAux, List.mem_append]
    exact Or.inl hSite
  | hd :: tl, baseIdx, n + 1, bb, site, hGet, hSite => by
    change get? tl n = some bb at hGet
    simp only [censusBlocksAux, List.mem_append]
    right
    have hAdd : baseIdx + 1 + n = baseIdx + (n + 1) := by omega
    rw [← hAdd] at hSite
    exact mem_censusBlocksAux_of_get? numBlocks tl (baseIdx + 1) n bb site hGet hSite

/--
If `get? body.basicBlocks blockIdx = some bb` and
`site ∈ censusBlockFaultSites (length body.basicBlocks) blockIdx bb`, then
`site ∈ censusMirBodyFaultSites body`.
-/
theorem mem_censusMirBodyFaultSites_of_block
    (body : CapturedMir) (blockIdx : BasicBlockIdx) (bb : BasicBlockData) (site : FaultSite)
    (hBb : get? body.basicBlocks blockIdx = some bb)
    (hSite : site ∈ censusBlockFaultSites (length body.basicBlocks) blockIdx bb) :
    site ∈ censusMirBodyFaultSites body := by
  have hSite' : site ∈ censusBlockFaultSites (length body.basicBlocks) (0 + blockIdx) bb := by
    simpa using hSite
  exact mem_censusBlocksAux_of_get?
    (length body.basicBlocks) body.basicBlocks 0 blockIdx bb site hBb hSite'

/--
Statement-level census completeness: whenever `evalStmt` faults with
`MirStepNode.fail .ub`, `censusStmtFaultClasses stmt.kind` contains at least one
justifying `MirFaultClass` for `stmt.kind`.
-/
theorem evalStmt_ub_implies_mem_censusStmt
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hUb : evalStmt s stmt localDecls layouts = MirStepNode.fail .ub) :
    ∃ cls : MirFaultClass, cls ∈ censusStmtFaultClasses stmt.kind := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | nop => nomatch hUb
  | coverage => nomatch hUb
  | constEvalCounter => nomatch hUb
  | backwardIncompatibleDropHint _ => nomatch hUb
  | storageLive _ =>
    exact ⟨.storageLiveProtected, by dsimp only [censusStmtFaultClasses]; decide⟩
  | storageDead _ =>
    exact ⟨.storageLiveProtected, by dsimp only [censusStmtFaultClasses]; decide⟩
  | placeMention place =>
    refine ⟨.uninitRead, ?_⟩
    simp [censusStmtFaultClasses]
  | deinit place =>
    refine ⟨.uninitRead, ?_⟩
    simp [censusStmtFaultClasses]
  | retag _ place =>
    refine ⟨.uninitRead, ?_⟩
    simp [censusStmtFaultClasses, censusPlaceReadFaultClasses]
  | setDiscriminant place _ =>
    refine ⟨.scalarNicheInvalid, ?_⟩
    cases hProj : place.projection <;> simp [censusStmtFaultClasses, hProj]
  | intrinsic intr =>
    cases intr with
    | assume op =>
      refine ⟨.scalarNicheInvalid, ?_⟩
      simp [censusStmtFaultClasses, censusIntrinsicFaultClasses]
    | copyNonOverlapping src dst count =>
      refine ⟨.ptrDerefInvalid, ?_⟩
      simp [censusStmtFaultClasses, censusIntrinsicFaultClasses]
  | assign dst rv =>
    refine ⟨.storageLiveProtected, ?_⟩
    cases hProj : dst.projection <;>
      simp [censusStmtFaultClasses, censusPlaceWriteFaultClasses, hProj]

/--
Terminator-level census completeness: whenever `evalTerminator` faults with
`MirStepNode.fail .ub`, `censusTerminatorFaultClasses numBlocks term.kind`
contains at least one justifying `MirFaultClass` for `term.kind`.
-/
theorem evalTerminator_ub_implies_mem_censusTerminator
    (numBlocks : Nat) (s : MachineState) (term : Terminator)
    (currentBody : Option CapturedMir)
    (hUb : evalTerminator s term currentBody = MirStepNode.fail .ub) :
    ∃ cls : MirFaultClass, cls ∈ censusTerminatorFaultClasses numBlocks term.kind := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto _ => nomatch hUb
  | unwindTerminate => nomatch hUb
  | inlineAsm _ _ _ => nomatch hUb
  | unreachable =>
    exact ⟨.unreachableTerminator, by dsimp only [censusTerminatorFaultClasses]; decide⟩
  | unwindResume =>
    exact ⟨.callAbiMismatch, by dsimp only [censusTerminatorFaultClasses]; decide⟩
  | return_ =>
    exact ⟨.uninitRead, by dsimp only [censusTerminatorFaultClasses]; decide⟩
  | switchInt discr targets =>
    refine ⟨.scalarNicheInvalid, ?_⟩
    simp [censusTerminatorFaultClasses]
  | drop place target unwind =>
    refine ⟨.uninitRead, ?_⟩
    simp [censusTerminatorFaultClasses, censusPlaceReadFaultClasses]
  | assert cond expected target unwind =>
    refine ⟨.scalarNicheInvalid, ?_⟩
    simp [censusTerminatorFaultClasses]
  | call func args destination target unwind =>
    refine ⟨.callAbiMismatch, ?_⟩
    simp [censusTerminatorFaultClasses]
  | tailCall func args =>
    refine ⟨.callAbiMismatch, ?_⟩
    simp [censusTerminatorFaultClasses]

/-! ## 7. Valid PC Bounds (`ValidMirPc`), CFG Invariance, and `stepMirFn_fault_in_census` -/

/--
A stack-frame program counter `(frame.blockIdx, frame.stmtIdx)` is in bounds for
`body : CapturedMir` when `frame.blockIdx` names a basic block `bb` of
`body.basicBlocks` and `frame.stmtIdx ≤ length bb.statements` (pointing either to
a statement `< length bb.statements` or to the block's terminator at
`length bb.statements`).
-/
def ValidMirPc (body : CapturedMir) (frame : StackFrame) : Prop :=
  ∃ bb : BasicBlockData,
    get? body.basicBlocks frame.blockIdx = some bb ∧
    frame.stmtIdx ≤ length bb.statements

/--
Executable CFG well-formedness check verifying that `body.basicBlocks` is
non-empty and every syntactic successor block index in every basic block's
terminator is `< length body.basicBlocks`.
-/
def cfgTargetsInBounds (body : CapturedMir) : Bool :=
  let numBlocks := length body.basicBlocks
  decide (0 < numBlocks) &&
    body.basicBlocks.all (fun bb =>
      (terminatorTargets bb.terminator.kind).all (fun t => decide (t < numBlocks)))

/--
Helper: if `idx < length xs`, then `∃ x, get? xs idx = some x`.
-/
theorem exists_get?_of_lt_length {α : Type} :
    ∀ (xs : List α) (idx : Nat), idx < length xs → ∃ x, get? xs idx = some x
  | [], _, hLt => by nomatch hLt
  | hd :: _, 0, _ => ⟨hd, rfl⟩
  | _ :: tl, n + 1, hLt => by
    have hLt' : n < length tl := Nat.lt_of_succ_lt_succ hLt
    exact exists_get?_of_lt_length tl n hLt'

/--
Helper: if `get? xs idx = some x`, then `idx < length xs` and `x ∈ xs`.
-/
theorem lt_length_and_mem_of_get? {α : Type} :
    ∀ (xs : List α) (idx : Nat) (x : α),
      get? xs idx = some x → idx < length xs ∧ x ∈ xs
  | [], idx, _, hGet => by cases idx <;> nomatch hGet
  | hd :: tl, 0, x, hGet => by
    change some hd = some x at hGet
    injection hGet with hEq
    subst hEq
    exact ⟨Nat.zero_lt_succ _, List.Mem.head tl⟩
  | hd :: tl, n + 1, x, hGet => by
    change get? tl n = some x at hGet
    rcases lt_length_and_mem_of_get? tl n x hGet with ⟨hLt, hMem⟩
    exact ⟨Nat.succ_lt_succ hLt, List.Mem.tail hd hMem⟩

/--
Helper: if `get? xs idx = none`, then `length xs ≤ idx`.
-/
theorem length_le_of_get?_eq_none {α : Type} :
    ∀ (xs : List α) (idx : Nat), get? xs idx = none → length xs ≤ idx
  | [], _, _ => Nat.zero_le _
  | _ :: _, 0, hNone => by nomatch hNone
  | _ :: tl, n + 1, hNone => by
    change get? tl n = none at hNone
    exact Nat.succ_le_succ (length_le_of_get?_eq_none tl n hNone)

/--
Entry state PC validity: when `0 < length body.basicBlocks`, `initMachineState body args`
starts at `(blockIdx := 0, stmtIdx := 0)`, which satisfies `ValidMirPc body`.
-/
theorem validMirPc_initMachineState
    (body : CapturedMir) (args : List Value)
    (hNonEmpty : 0 < length body.basicBlocks) :
    ValidMirPc body (initMachineState body args).frame := by
  rcases exists_get?_of_lt_length body.basicBlocks 0 hNonEmpty with ⟨bb0, hBb0⟩
  exact ⟨bb0, hBb0, Nat.zero_le _⟩

/--
General Fault-Site Census Completeness Theorem over the active body
(`s.memory.activeCallee.getD body`): whenever `stepMirFn body s` faults with
`MirStepNode.fail .ub` from a valid program counter `ValidMirPc`, the active
program counter `(s.frame.blockIdx, s.frame.stmtIdx, cls)` is present in
`censusMirBodyFaultSites (s.memory.activeCallee.getD body)` for some
`cls : MirFaultClass`.
-/
theorem stepMirFn_activeBody_fault_in_census
    (body : CapturedMir) (s : MachineState)
    (hPc : ValidMirPc (s.memory.activeCallee.getD body) s.frame)
    (hUb : stepMirFn body s = MirStepNode.fail .ub) :
    ∃ cls : MirFaultClass,
      (s.frame.blockIdx, s.frame.stmtIdx, cls) ∈
        censusMirBodyFaultSites (s.memory.activeCallee.getD body) := by
  dsimp only [stepMirFn] at hUb
  generalize s.memory.activeCallee.getD body = currentBody at hPc hUb ⊢
  rcases hPc with ⟨bb, hBb, hStmtLe⟩
  cases hPhase : currentBody.phase with
  | other tag =>
    rw [hPhase] at hUb
    nomatch hUb
  | runtimePostCleanup =>
    rw [hPhase, hBb] at hUb
    dsimp only at hUb
    cases hGetStmt : get? bb.statements s.frame.stmtIdx with
    | some stmt =>
      rw [hGetStmt] at hUb
      rcases evalStmt_ub_implies_mem_censusStmt s stmt currentBody.localDecls
          currentBody.layouts hUb with ⟨cls, hCls⟩
      refine ⟨cls, ?_⟩
      exact mem_censusMirBodyFaultSites_of_block currentBody s.frame.blockIdx bb
        (s.frame.blockIdx, s.frame.stmtIdx, cls) hBb
        (mem_censusBlockFaultSites_of_stmt (length currentBody.basicBlocks)
          s.frame.blockIdx bb s.frame.stmtIdx stmt cls hGetStmt hCls)
    | none =>
      rw [hGetStmt] at hUb
      have hGe : length bb.statements ≤ s.frame.stmtIdx :=
        length_le_of_get?_eq_none bb.statements s.frame.stmtIdx hGetStmt
      have hEqIdx : s.frame.stmtIdx = length bb.statements :=
        Nat.le_antisymm hStmtLe hGe
      have hBeq : (s.frame.stmtIdx == length bb.statements) = true := by
        simp [hEqIdx]
      rw [hBeq] at hUb
      dsimp only [ite_true] at hUb
      rcases evalTerminator_ub_implies_mem_censusTerminator
          (length currentBody.basicBlocks) s bb.terminator (some currentBody) hUb with
        ⟨cls, hCls⟩
      refine ⟨cls, ?_⟩
      rw [hEqIdx]
      exact mem_censusMirBodyFaultSites_of_block currentBody s.frame.blockIdx bb
        (s.frame.blockIdx, length bb.statements, cls) hBb
        (mem_censusBlockFaultSites_of_terminator (length currentBody.basicBlocks)
          s.frame.blockIdx bb cls hCls)
  | runtimeOptimized =>
    rw [hPhase, hBb] at hUb
    dsimp only at hUb
    cases hGetStmt : get? bb.statements s.frame.stmtIdx with
    | some stmt =>
      rw [hGetStmt] at hUb
      rcases evalStmt_ub_implies_mem_censusStmt s stmt currentBody.localDecls
          currentBody.layouts hUb with ⟨cls, hCls⟩
      refine ⟨cls, ?_⟩
      exact mem_censusMirBodyFaultSites_of_block currentBody s.frame.blockIdx bb
        (s.frame.blockIdx, s.frame.stmtIdx, cls) hBb
        (mem_censusBlockFaultSites_of_stmt (length currentBody.basicBlocks)
          s.frame.blockIdx bb s.frame.stmtIdx stmt cls hGetStmt hCls)
    | none =>
      rw [hGetStmt] at hUb
      have hGe : length bb.statements ≤ s.frame.stmtIdx :=
        length_le_of_get?_eq_none bb.statements s.frame.stmtIdx hGetStmt
      have hEqIdx : s.frame.stmtIdx = length bb.statements :=
        Nat.le_antisymm hStmtLe hGe
      have hBeq : (s.frame.stmtIdx == length bb.statements) = true := by
        simp [hEqIdx]
      rw [hBeq] at hUb
      dsimp only [ite_true] at hUb
      rcases evalTerminator_ub_implies_mem_censusTerminator
          (length currentBody.basicBlocks) s bb.terminator (some currentBody) hUb with
        ⟨cls, hCls⟩
      refine ⟨cls, ?_⟩
      rw [hEqIdx]
      exact mem_censusMirBodyFaultSites_of_block currentBody s.frame.blockIdx bb
        (s.frame.blockIdx, length bb.statements, cls) hBb
        (mem_censusBlockFaultSites_of_terminator (length currentBody.basicBlocks)
          s.frame.blockIdx bb cls hCls)

/--
Top-Level Fault-Site Census Completeness Theorem (`stepMirFn_fault_in_census`):
for any top-level state (`s.memory.activeCallee = none`) with a valid program
counter `ValidMirPc body s.frame`, if `stepMirFn body s = MirStepNode.fail .ub`,
then `(s.frame.blockIdx, s.frame.stmtIdx, cls) ∈ censusMirBodyFaultSites body`
for some `cls : MirFaultClass`.
-/
theorem stepMirFn_fault_in_census
    (body : CapturedMir) (s : MachineState)
    (hTop : s.memory.activeCallee = none)
    (hPc : ValidMirPc body s.frame)
    (hUb : stepMirFn body s = MirStepNode.fail .ub) :
    ∃ cls : MirFaultClass,
      (s.frame.blockIdx, s.frame.stmtIdx, cls) ∈ censusMirBodyFaultSites body := by
  have hPcActive : ValidMirPc (s.memory.activeCallee.getD body) s.frame := by
    simpa [hTop] using hPc
  have hActive := stepMirFn_activeBody_fault_in_census body s hPcActive hUb
  simpa [hTop] using hActive

/--
Zero-Census UB-Freedom at a Program Counter (`stepMirFn_ne_ub_of_site_uncensused`):
if `ValidMirPc body s.frame`, `s.memory.activeCallee = none`, and no fault class
at `(s.frame.blockIdx, s.frame.stmtIdx)` is in `censusMirBodyFaultSites body`,
then `stepMirFn body s` cannot fault with `MirStepNode.fail .ub`.
-/
theorem stepMirFn_ne_ub_of_site_uncensused
    (body : CapturedMir) (s : MachineState)
    (hTop : s.memory.activeCallee = none)
    (hPc : ValidMirPc body s.frame)
    (hUncensused : ∀ cls : MirFaultClass,
      (s.frame.blockIdx, s.frame.stmtIdx, cls) ∉ censusMirBodyFaultSites body) :
    stepMirFn body s ≠ MirStepNode.fail .ub := by
  intro hUb
  rcases stepMirFn_fault_in_census body s hTop hPc hUb with ⟨cls, hMem⟩
  exact hUncensused cls hMem

/--
Zero-Census UB-Freedom for a Pure Body (`stepMirFn_ne_ub_of_empty_census`):
if `censusMirBodyFaultSites body = []`, `s.memory.activeCallee = none`, and
`ValidMirPc body s.frame`, then `stepMirFn body s ≠ MirStepNode.fail .ub`.
-/
theorem stepMirFn_ne_ub_of_empty_census
    (body : CapturedMir) (s : MachineState)
    (hTop : s.memory.activeCallee = none)
    (hPc : ValidMirPc body s.frame)
    (hEmpty : censusMirBodyFaultSites body = []) :
    stepMirFn body s ≠ MirStepNode.fail .ub := by
  apply stepMirFn_ne_ub_of_site_uncensused body s hTop hPc
  intro cls
  rw [hEmpty]
  intro hMem
  nomatch hMem

/-! ## 8. PC Preservation Across Statements and Intra-Frame Terminators -/

/--
Goal-directed step predicate for `evalStmt`: holds when any `.tau (.running s')`
transition advances `stmtIdx` by `1` in the same `blockIdx`, and forbids
`.vis (.inr (.inl (.emit _))) _` (`MirStepNode.emitStep`).
-/
@[reducible]
def StmtStepPreservesPc (s : MachineState) : MirStepNode → Prop
  | .tau (.running s') =>
    s'.frame.blockIdx = s.frame.blockIdx ∧
    s'.frame.stmtIdx = s.frame.stmtIdx + 1
  | .vis (.inr (.inl (.emit _))) _ => False
  | _ => True

private theorem commitCopyDstPlaceWrite_preservesPc
    (s : MachineState) (dstPlace : Place) (dstTargetLocal : LocalIdx)
    (dstTag : Nat) (locals₃ : List LocalSlot) (newVal : Value) :
    StmtStepPreservesPc s
      (commitCopyDstPlaceWrite s dstPlace dstTargetLocal dstTag locals₃ newVal) := by
  dsimp only [commitCopyDstPlaceWrite]
  split
  · exact ⟨rfl, rfl⟩
  · trivial
  · split
    · trivial
    · split
      · trivial
      · trivial
      · exact ⟨rfl, rfl⟩

private theorem evalCopySingleDirect_preservesPc
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (locals₃ : List LocalSlot) :
    StmtStepPreservesPc s
      (evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        srcEntry dstEntry locals₃) := by
  dsimp only [evalCopySingleDirect]
  split
  · trivial
  · split
    · split
      · trivial
      · trivial
      · split
        · trivial
        · split
          · exact ⟨rfl, rfl⟩
          · trivial
          · split
            · trivial
            · split
              · trivial
              · trivial
              · exact ⟨rfl, rfl⟩
    · trivial

private theorem evalCopyUnionBytes_preservesPc
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo)
    (n : Nat) (locals₃ : List LocalSlot) :
    StmtStepPreservesPc s
      (evalCopyUnionBytes s src dst localDecls layouts srcPtr dstPtr
        srcEntry dstEntry srcUnionOpt dstUnionOpt n locals₃) := by
  dsimp only [evalCopyUnionBytes]
  split
  · trivial
  · split
    · trivial
    · trivial
    · split
      · split
        · trivial
        · trivial
        · split
          · trivial
          · split
            · trivial
            · split
              · trivial
              · exact ⟨rfl, rfl⟩
      · split
        · trivial
        · split
          · trivial
          · trivial
          · split
            · split
              · split
                · trivial
                · split
                  · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                  · trivial
              · trivial
            · trivial
          · split
            · trivial
            · split
              · split
                · split
                  · trivial
                  · split
                    · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                    · trivial
                · trivial
              · trivial
            · split
              · split
                · split
                  · trivial
                  · split
                    · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                    · trivial
                · split
                  · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                  · trivial
              · split
                · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                · trivial

private theorem evalCopyNonOverlappingPermOk_preservesPc
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    StmtStepPreservesPc s
      (evalCopyNonOverlappingPermOk s src dst localDecls layouts srcPtr dstPtr
        srcEntry dstEntry countBits locals₃) := by
  dsimp only [evalCopyNonOverlappingPermOk]
  split
  · exact evalCopyUnionBytes_preservesPc s src dst localDecls layouts
      srcPtr dstPtr srcEntry dstEntry _ _ countBits locals₃
  · split
    · exact evalCopySingleDirect_preservesPc s src dst localDecls layouts
        srcPtr dstPtr srcEntry dstEntry locals₃
    · split
      · split
        · split
          · split
            · split
              · trivial
              · split
                · trivial
                · split
                  · trivial
                  · split
                    · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                    · split
                      · split
                        · split
                          · split
                            · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                            · split
                              · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                              · trivial
                          · split
                            · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                            · trivial
                        · split
                          · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                          · trivial
                      · split
                        · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                        · trivial
            · trivial
          · split
            · trivial
            · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
        · split
          · trivial
          · split
            · trivial
            · split
              · trivial
              · split
                · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                · split
                  · split
                    · split
                      · split
                        · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                        · split
                          · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                          · trivial
                      · split
                        · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                        · trivial
                    · split
                      · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                      · trivial
                  · split
                    · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                    · trivial
        · split
          · split
            · trivial
            · split
              · trivial
              · split
                · trivial
                · split
                  · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                  · split
                    · split
                      · split
                        · split
                          · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                          · split
                            · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                            · trivial
                        · split
                          · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                          · trivial
                      · split
                        · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                        · trivial
                    · split
                      · exact commitCopyDstPlaceWrite_preservesPc s _ _ _ _ _
                      · trivial
          · trivial
        · trivial
      · trivial

/--
Every `evalStmt` evaluation satisfies `StmtStepPreservesPc s`.
-/
theorem evalStmt_preservesPc
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    StmtStepPreservesPc s (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | nop | coverage | constEvalCounter | backwardIncompatibleDropHint _ =>
    exact ⟨rfl, rfl⟩
  | placeMention place =>
    dsimp only [evalStmt]
    split
    · trivial
    · trivial
    · split
      · exact ⟨rfl, rfl⟩
      · trivial
  | storageLive loc =>
    dsimp only [evalStmt]
    split
    · split
      · split
        · exact ⟨rfl, rfl⟩
        · split
          · trivial
          · exact ⟨rfl, rfl⟩
      · trivial
    · trivial
  | storageDead loc =>
    dsimp only [evalStmt]
    split
    · split
      · split
        · exact ⟨rfl, rfl⟩
        · split
          · trivial
          · exact ⟨rfl, rfl⟩
      · trivial
    · trivial
  | deinit p =>
    dsimp only [evalStmt]
    split
    · split
      · trivial
      · split
        · exact ⟨rfl, rfl⟩
        · trivial
      · trivial
    · split
      · split
        · exact ⟨rfl, rfl⟩
        · trivial
        · trivial
      · trivial
  | retag retagKind place =>
    dsimp only [evalStmt]
    split
    · split
      · split
        · split
          · trivial
          · split <;> exact ⟨rfl, rfl⟩
        · split
          · split
            · exact ⟨rfl, rfl⟩
            · trivial
          · split
            · exact ⟨rfl, rfl⟩
            · trivial
      · trivial
    · trivial
    · trivial
  | intrinsic intr =>
    cases intr with
    | assume op =>
      dsimp only [evalStmt]
      split
      · split
        · exact ⟨rfl, rfl⟩
        · trivial
      · trivial
      · trivial
      · trivial
    | copyNonOverlapping src dst count =>
      dsimp only [evalStmt, evalCopyNonOverlapping]
      split
      · trivial
      · trivial
      · split
        · trivial
        · trivial
        · split
          · trivial
          · trivial
          · dsimp only [evalCopyNonOverlappingWithCount]
            split
            · exact ⟨rfl, rfl⟩
            · split
              · split
                · split
                  · trivial
                  · trivial
                  · trivial
                  · exact evalCopyNonOverlappingPermOk_preservesPc s src dst
                      localDecls layouts _ _ _ _ _ _
                · trivial
              · trivial
          · trivial
  | setDiscriminant p variantIdx =>
    dsimp only [evalStmt]
    split
    · split
      · split
        · exact ⟨rfl, rfl⟩
        · trivial
      · trivial
      · trivial
      · trivial
      · trivial
    · split
      · split
        · exact ⟨rfl, rfl⟩
        · trivial
        · trivial
      · trivial
      · trivial
      · trivial
  | assign dst rv =>
    dsimp only [evalStmt]
    split
    · split
      · split
        · trivial
        · split
          · split
            · exact ⟨rfl, rfl⟩
            · split
              · trivial
              · exact ⟨rfl, rfl⟩
          · trivial
        · trivial
      · split
        · exact ⟨rfl, rfl⟩
        · split
          · trivial
          · split
            · exact ⟨rfl, rfl⟩
            · trivial
            · trivial
        · trivial
      · split
        · split
          · split
            · split
              · exact ⟨rfl, rfl⟩
              · split
                · trivial
                · exact ⟨rfl, rfl⟩
            · trivial
          · trivial
          · trivial
        · split
          · split
            · split
              · split
                · exact ⟨rfl, rfl⟩
                · split
                  · trivial
                  · exact ⟨rfl, rfl⟩
              · trivial
            · trivial
            · trivial
          · trivial
        · trivial
        · trivial
    · trivial
    · trivial

/--
Every `MirStepNode.step s'` or `MirStepNode.emitStep obs s'` transition produced
by `evalStmt` advances `stmtIdx` by `1` within the same `blockIdx`.
-/
theorem evalStmt_step_or_emit_frame
    (s s' : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hStep : evalStmt s stmt localDecls layouts = MirStepNode.step s' ∨
             ∃ obs, evalStmt s stmt localDecls layouts = MirStepNode.emitStep obs s') :
    s'.frame.blockIdx = s.frame.blockIdx ∧
    s'.frame.stmtIdx = s.frame.stmtIdx + 1 := by
  have hPres := evalStmt_preservesPc s stmt localDecls layouts
  rcases hStep with hS | ⟨obs, hE⟩
  · rw [hS] at hPres
    exact hPres
  · cases obs with
    | silent =>
      rw [hE] at hPres
      exact hPres
    | event tag =>
      rw [hE] at hPres
      exact False.elim hPres

/--
Every `MirStepNode.step s'` transition produced by `evalStmt` advances `stmtIdx`
by `1` within the same `blockIdx`.
-/
theorem evalStmt_step_frame
    (s s' : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hStep : evalStmt s stmt localDecls layouts = MirStepNode.step s') :
    s'.frame.blockIdx = s.frame.blockIdx ∧
    s'.frame.stmtIdx = s.frame.stmtIdx + 1 :=
  evalStmt_step_or_emit_frame s s' stmt localDecls layouts (Or.inl hStep)

/--
Helper: `lookupSwitchTarget val branches otherwise` is always in
`otherwise :: branches.map Prod.snd`.
-/
theorem lookupSwitchTarget_mem
    (val : Nat) :
    ∀ (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx),
      lookupSwitchTarget val branches otherwise ∈ otherwise :: branches.map Prod.snd
  | [], otherwise => List.Mem.head []
  | (bVal, target) :: rest, otherwise => by
    dsimp only [lookupSwitchTarget]
    cases Nat.beq val bVal with
    | true =>
      exact List.Mem.tail otherwise (List.Mem.head (rest.map Prod.snd))
    | false =>
      rcases List.mem_cons.mp (lookupSwitchTarget_mem val rest otherwise) with hEq | hTail
      · rw [hEq]
        exact List.Mem.head _
      · exact List.Mem.tail otherwise (List.Mem.tail target hTail)

/--
Goal-directed step predicate for `evalTerminator`: holds when any intra-frame
`MirStepNode.step s'` or `MirStepNode.emitStep obs s'` (`s'.memory.activeCallee = none`)
resets `s'.frame.stmtIdx = 0` and jumps to `s'.frame.blockIdx ∈ targets`.
-/
@[reducible]
def TermStepPreservesPc (targets : List BasicBlockIdx) : MirStepNode → Prop
  | .tau (.running s') =>
    s'.memory.activeCallee = none →
      s'.frame.stmtIdx = 0 ∧ s'.frame.blockIdx ∈ targets
  | .vis (.inr (.inl _)) k =>
    match k PUnit.unit with
    | .running s' =>
      s'.memory.activeCallee = none →
        s'.frame.stmtIdx = 0 ∧ s'.frame.blockIdx ∈ targets
    | _ => True
  | _ => True

private theorem termStepPreservesPc_mono
    {t₁ t₂ : List BasicBlockIdx} {node : MirStepNode}
    (hSub : ∀ b ∈ t₁, b ∈ t₂)
    (hPres : TermStepPreservesPc t₁ node) :
    TermStepPreservesPc t₂ node := by
  cases node with
  | ret _ => trivial
  | tau next =>
    cases next with
    | running s' =>
      intro hIntra
      rcases hPres hIntra with ⟨hZ, hMem⟩
      exact ⟨hZ, hSub _ hMem⟩
    | halted _ => trivial
    | faulted _ => trivial
  | vis eff k =>
    rcases eff with _ | ⟨_ | _⟩
    · trivial
    · dsimp only [TermStepPreservesPc] at hPres ⊢
      split
      · rename_i s' hEq
        rw [hEq] at hPres
        intro hIntra
        rcases hPres hIntra with ⟨hZ, hMem⟩
        exact ⟨hZ, hSub _ hMem⟩
      · trivial
    · trivial

private theorem writeIntrinsicReturn_preservesPc
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (retVal : Value) :
    TermStepPreservesPc [targetBb]
      (writeIntrinsicReturn s locals' destination targetBb retVal) := by
  dsimp only [writeIntrinsicReturn]
  split
  · intro _; exact ⟨rfl, List.Mem.head []⟩
  · trivial
  · trivial

private theorem writeIntrinsicScalarResult_preservesPc
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (resOpt : Option ScalarInt) :
    TermStepPreservesPc [targetBb]
      (writeIntrinsicScalarResult s locals' destination targetBb resOpt) := by
  dsimp only [writeIntrinsicScalarResult]
  cases resOpt with
  | some sc => exact writeIntrinsicReturn_preservesPc s locals' destination targetBb (.scalar sc)
  | none => trivial

private theorem intrinsicUnresolvedLayoutStep_preservesPc
    (targets : List BasicBlockIdx) (ty : RigidTy) :
    TermStepPreservesPc targets (intrinsicUnresolvedLayoutStep ty) := by
  dsimp only [intrinsicUnresolvedLayoutStep]
  split <;> trivial

private theorem intrinsicWidePointeeStep_preservesPc
    (targets : List BasicBlockIdx) (ty : RigidTy) :
    TermStepPreservesPc targets (intrinsicWidePointeeStep ty) := by
  dsimp only [intrinsicWidePointeeStep]
  split <;> trivial

private theorem intrinsicMissingPointeeStep_preservesPc
    (targets : List BasicBlockIdx) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand) :
    TermStepPreservesPc targets
      (intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps) := by
  dsimp only [intrinsicMissingPointeeStep]
  split
  · split <;> trivial
  · trivial

private theorem evalNonSelectIntrinsicCall_preservesPc
    (kind : RustIntrinsicKind) (s : MachineState) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    TermStepPreservesPc [targetBb]
      (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb) := by
  cases kind with
  | ubChecks =>
    dsimp only [evalNonSelectIntrinsicCall]
    split
    · exact writeIntrinsicReturn_preservesPc s _ _ targetBb _
    · trivial
  | arithOffset =>
    dsimp only [evalNonSelectIntrinsicCall]
    split
    · split
      · trivial
      · split
        · split
          · split
            · exact writeIntrinsicReturn_preservesPc s _ _ targetBb _
            · trivial
          · exact intrinsicUnresolvedLayoutStep_preservesPc [targetBb] _
        · exact intrinsicMissingPointeeStep_preservesPc [targetBb] _ _ _
    · trivial
  | ctlz | ctlzNonzero | cttz | cttzNonzero | ctpop | bswap | bitreverse
  | wrappingAdd | wrappingSub | wrappingMul =>
    dsimp only [evalNonSelectIntrinsicCall]
    split
    · exact writeIntrinsicScalarResult_preservesPc s _ _ targetBb _
    · trivial
  | saturatingAdd | saturatingSub | uncheckedShl | uncheckedAdd
  | uncheckedSub | uncheckedMul | uncheckedDiv | uncheckedRem | threeWayCompare =>
    dsimp only [evalNonSelectIntrinsicCall]
    split
    · split
      · exact writeIntrinsicScalarResult_preservesPc s _ _ targetBb _
      · trivial
    · trivial
  | uncheckedShr =>
    dsimp only [evalNonSelectIntrinsicCall]
    split
    · split
      · exact writeIntrinsicScalarResult_preservesPc s _ _ targetBb _
      · trivial
    · trivial
  | sizeOfVal =>
    dsimp only [evalNonSelectIntrinsicCall]
    split
    · split
      · split
        · split
          · trivial
          · split
            · exact writeIntrinsicScalarResult_preservesPc s _ _ targetBb _
            · exact intrinsicUnresolvedLayoutStep_preservesPc [targetBb] _
        · trivial
      · split
        · split
          · trivial
          · exact writeIntrinsicScalarResult_preservesPc s _ _ targetBb _
        · trivial
      · split
        · split <;> trivial
        · trivial
      · split
        · split
          · trivial
          · split
            · trivial
            · split
              · split
                · trivial
                · exact writeIntrinsicReturn_preservesPc s _ _ targetBb _
              · exact intrinsicUnresolvedLayoutStep_preservesPc [targetBb] _
        · split
          · trivial
          · exact intrinsicWidePointeeStep_preservesPc [targetBb] _
        · trivial
      · split
        · trivial
        · exact intrinsicMissingPointeeStep_preservesPc [targetBb] _ _ _
    · trivial
  | alignOfVal =>
    dsimp only [evalNonSelectIntrinsicCall]
    split
    · split
      · split
        · split
          · trivial
          · split
            · split
              · exact writeIntrinsicReturn_preservesPc s _ _ targetBb _
              · trivial
            · exact intrinsicUnresolvedLayoutStep_preservesPc [targetBb] _
        · trivial
      · split
        · split
          · trivial
          · split
            · exact writeIntrinsicReturn_preservesPc s _ _ targetBb _
            · trivial
        · trivial
      · split
        · split <;> trivial
        · trivial
      · split
        · split
          · trivial
          · split
            · trivial
            · split
              · exact writeIntrinsicReturn_preservesPc s _ _ targetBb _
              · exact intrinsicUnresolvedLayoutStep_preservesPc [targetBb] _
        · split
          · trivial
          · exact intrinsicWidePointeeStep_preservesPc [targetBb] _
        · trivial
      · split
        · trivial
        · exact intrinsicMissingPointeeStep_preservesPc [targetBb] _ _ _
    · trivial
  | constEvalSelect => trivial

private theorem applyUnwindAction_root_preservesPc
    (s : MachineState) (localsAfterArgs : List LocalSlot) (unwind : UnwindAction)
    (hStack : s.memory.callStack = []) :
    TermStepPreservesPc (unwindTargets unwind)
      (match applyUnwindAction s localsAfterArgs s.memory unwind with
       | .running nextState => MirStepNode.step nextState
       | .halted out => MirStepNode.retOutcome out
       | .faulted fk => MirStepNode.fail fk) := by
  cases unwind with
  | unreachable => trivial
  | terminate => trivial
  | continue_ =>
    dsimp only [applyUnwindAction]
    rw [hStack]
    trivial
  | cleanup cleanupBb =>
    dsimp only [applyUnwindAction]
    intro _
    exact ⟨rfl, List.Mem.head []⟩

private theorem evalDirectRustIntrinsic?_preservesPc
    (s : MachineState) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand) (argVals : List Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (unwind : UnwindAction) (stepNode : MirStepNode)
    (hStack : s.memory.callStack = [])
    (hSome : evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb unwind = some stepNode) :
    TermStepPreservesPc (targetBb :: unwindTargets unwind) stepNode := by
  have hSubHead : ∀ b ∈ [targetBb], b ∈ targetBb :: unwindTargets unwind := by
    intro b hMem; cases hMem with | head => exact List.Mem.head _ | tail _ h => nomatch h
  have hSubTail : ∀ b ∈ unwindTargets unwind, b ∈ targetBb :: unwindTargets unwind := by
    intro b hMem; exact List.Mem.tail targetBb hMem
  dsimp only [evalDirectRustIntrinsic?] at hSome
  split at hSome
  · nomatch hSome
  · injection hSome with hNode
    rw [← hNode]
    split
    · split
      · trivial
      · split
        · trivial
        · split
          · split
            · trivial
            · split
              · trivial
              · intro hIntra; nomatch hIntra
          · split
            · trivial
            · split
              · split
                · split
                  · trivial
                  · exact termStepPreservesPc_mono hSubHead
                      (writeIntrinsicScalarResult_preservesPc s _ _ targetBb _)
                · trivial
              · split
                · trivial
                · exact termStepPreservesPc_mono hSubHead
                    (evalNonSelectIntrinsicCall_preservesPc _ s _ _ _ _ _ _ _ targetBb)
                · split
                  · trivial
                  · split
                    · trivial
                    · split
                      · exact termStepPreservesPc_mono hSubTail
                          (applyUnwindAction_root_preservesPc s locals' unwind hStack)
                      · trivial
    · trivial
  · injection hSome with hNode
    rw [← hNode]
    exact termStepPreservesPc_mono hSubHead
      (evalNonSelectIntrinsicCall_preservesPc _ s _ _ _ _ _ _ _ targetBb)

/--
Every `evalTerminator` evaluation from a root call stack (`s.memory.callStack = []`)
satisfies `TermStepPreservesPc (terminatorTargets term.kind)`.
-/
theorem evalTerminator_preservesPc
    (body : CapturedMir) (s : MachineState) (term : Terminator)
    (hStack : s.memory.callStack = []) :
    TermStepPreservesPc (terminatorTargets term.kind)
      (evalTerminator s term (some body)) := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target =>
    intro _; exact ⟨rfl, List.Mem.head []⟩
  | switchInt discr targets =>
    dsimp only [evalTerminator]
    split
    · intro _
      exact ⟨rfl, lookupSwitchTarget_mem _ targets.branches targets.otherwise⟩
    · trivial
    · trivial
    · trivial
  | unwindResume =>
    dsimp only [evalTerminator]
    rw [hStack]
    trivial
  | unwindTerminate => trivial
  | return_ =>
    dsimp only [evalTerminator]
    rw [hStack]
    split <;> trivial
  | unreachable => trivial
  | inlineAsm _ _ _ => trivial
  | drop place target unwind =>
    dsimp only [evalTerminator]
    split
    · trivial
    · trivial
    · split
      · split
        · intro _; exact ⟨rfl, List.Mem.head _⟩
        · trivial
      · split
        · split
          · intro _; exact ⟨rfl, List.Mem.head _⟩
          · trivial
          · trivial
        · trivial
  | assert cond expected target unwind =>
    dsimp only [evalTerminator]
    split
    · split
      · intro _; exact ⟨rfl, List.Mem.head _⟩
      · exact termStepPreservesPc_mono (fun b h => List.Mem.tail target h)
          (applyUnwindAction_root_preservesPc s _ unwind hStack)
    · trivial
    · trivial
    · trivial
  | tailCall func argOps =>
    dsimp only [evalTerminator, evalTailCallTerminator]
    split
    · trivial
    · trivial
    · split
      · trivial
      · trivial
      · split
        · split
          · trivial
          · intro hIntra; nomatch hIntra
        · trivial
  | call func argOps destination target unwind =>
    cases target with
    | none =>
      dsimp only [evalTerminator]
      split
      · trivial
      · trivial
      · split
        · trivial
        · trivial
        · split
          · split
            · trivial
            · intro hIntra; nomatch hIntra
          · split
            · split
              · trivial
              · split
                · trivial
                · split
                  · exact applyUnwindAction_root_preservesPc s _ unwind hStack
                  · trivial
            · trivial
    | some targetBb =>
      dsimp only [evalTerminator]
      split
      · trivial
      · trivial
      · split
        · trivial
        · trivial
        · split
          · split
            · trivial
            · intro hIntra; nomatch hIntra
          · split
            · split
              · split
                · trivial
                · split
                  · split
                    · intro _; exact ⟨rfl, List.Mem.head _⟩
                    · trivial
                    · trivial
                  · trivial
              · trivial
            · split
              · trivial
              · cases hDir : evalDirectRustIntrinsic? s (some body) _ _ _ argOps _ _ destination targetBb unwind with
                | some stepNode =>
                  exact evalDirectRustIntrinsic?_preservesPc s (some body) _ _ _
                    argOps _ _ destination targetBb unwind stepNode hStack hDir
                | none => trivial

/--
Every intra-frame transition (`MirStepNode.step s'` or `MirStepNode.emitStep obs s'`
with `s'.memory.activeCallee = none` from `s.memory.callStack = []`) of
`evalTerminator` resets `s'.frame.stmtIdx = 0` and jumps to a `blockIdx` in
`terminatorTargets term.kind`.
-/
theorem evalTerminator_intraFrame_step_frame
    (body : CapturedMir) (s s' : MachineState) (term : Terminator)
    (hStack : s.memory.callStack = [])
    (hIntra : s'.memory.activeCallee = none)
    (hStep : evalTerminator s term (some body) = MirStepNode.step s' ∨
             ∃ obs, evalTerminator s term (some body) = MirStepNode.emitStep obs s') :
    s'.frame.stmtIdx = 0 ∧ s'.frame.blockIdx ∈ terminatorTargets term.kind := by
  have hPres := evalTerminator_preservesPc body s term hStack
  rcases hStep with hS | ⟨obs, hE⟩
  · rw [hS] at hPres
    exact hPres hIntra
  · cases obs with
    | silent =>
      rw [hE] at hPres
      exact hPres hIntra
    | event tag =>
      rw [hE] at hPres
      exact hPres hIntra

/--
CFG Target-Bounds Invariance Theorem (`stepMirFn_preserves_validMirPc`):
when `s.memory.activeCallee = none`, `s.memory.callStack = []`, and
`cfgTargetsInBounds body = true`, any intra-frame transition
(`MirStepNode.step s'` or `MirStepNode.emitStep obs s'` with
`s'.memory.activeCallee = none`) from a state satisfying `ValidMirPc body s.frame`
preserves `ValidMirPc body s'.frame`.
-/
theorem stepMirFn_preserves_validMirPc
    (body : CapturedMir) (s s' : MachineState)
    (hTop : s.memory.activeCallee = none)
    (hStack : s.memory.callStack = [])
    (hIntra : s'.memory.activeCallee = none)
    (hCfg : cfgTargetsInBounds body = true)
    (hPc : ValidMirPc body s.frame)
    (hStep : stepMirFn body s = MirStepNode.step s' ∨
             ∃ obs, stepMirFn body s = MirStepNode.emitStep obs s') :
    ValidMirPc body s'.frame := by
  dsimp only [stepMirFn] at hStep
  rw [hTop] at hStep
  dsimp only [Option.getD] at hStep
  rcases hPc with ⟨bb, hBb, hStmtLe⟩
  cases hPhase : body.phase with
  | other tag =>
    rw [hPhase] at hStep
    rcases hStep with hS | ⟨obs, hE⟩
    · nomatch hS
    · cases obs <;> nomatch hE
  | runtimePostCleanup =>
    rw [hPhase, hBb] at hStep
    dsimp only at hStep
    cases hGetStmt : get? bb.statements s.frame.stmtIdx with
    | some stmt =>
      rw [hGetStmt] at hStep
      have hLt : s.frame.stmtIdx < length bb.statements :=
        (lt_length_and_mem_of_get? bb.statements s.frame.stmtIdx stmt hGetStmt).1
      rcases evalStmt_step_or_emit_frame s s' stmt body.localDecls body.layouts hStep with
        ⟨hBlk, hIdx⟩
      refine ⟨bb, ?_, ?_⟩
      · rw [hBlk]; exact hBb
      · rw [hIdx]; exact Nat.succ_le_of_lt hLt
    | none =>
      rw [hGetStmt] at hStep
      have hGe : length bb.statements ≤ s.frame.stmtIdx :=
        length_le_of_get?_eq_none bb.statements s.frame.stmtIdx hGetStmt
      have hEqIdx : s.frame.stmtIdx = length bb.statements :=
        Nat.le_antisymm hStmtLe hGe
      have hBeq : (s.frame.stmtIdx == length bb.statements) = true := by
        simp [hEqIdx]
      rw [hBeq] at hStep
      dsimp only [ite_true] at hStep
      rcases evalTerminator_intraFrame_step_frame body s s' bb.terminator hStack hIntra hStep with
        ⟨hStmtZero, hTargetMem⟩
      have hBbMem : bb ∈ body.basicBlocks :=
        (lt_length_and_mem_of_get? body.basicBlocks s.frame.blockIdx bb hBb).2
      unfold cfgTargetsInBounds at hCfg
      rcases Bool.and_eq_true_iff.mp hCfg with ⟨_, hAllBbs⟩
      have hBbOk : (terminatorTargets bb.terminator.kind).all
          (fun t => decide (t < length body.basicBlocks)) = true :=
        (List.all_eq_true.mp hAllBbs) bb hBbMem
      have hTargetLt : s'.frame.blockIdx < length body.basicBlocks :=
        of_decide_eq_true ((List.all_eq_true.mp hBbOk) s'.frame.blockIdx hTargetMem)
      rcases exists_get?_of_lt_length body.basicBlocks s'.frame.blockIdx hTargetLt with
        ⟨bb', hBb'⟩
      refine ⟨bb', hBb', ?_⟩
      rw [hStmtZero]
      exact Nat.zero_le _
  | runtimeOptimized =>
    rw [hPhase, hBb] at hStep
    dsimp only at hStep
    cases hGetStmt : get? bb.statements s.frame.stmtIdx with
    | some stmt =>
      rw [hGetStmt] at hStep
      have hLt : s.frame.stmtIdx < length bb.statements :=
        (lt_length_and_mem_of_get? bb.statements s.frame.stmtIdx stmt hGetStmt).1
      rcases evalStmt_step_or_emit_frame s s' stmt body.localDecls body.layouts hStep with
        ⟨hBlk, hIdx⟩
      refine ⟨bb, ?_, ?_⟩
      · rw [hBlk]; exact hBb
      · rw [hIdx]; exact Nat.succ_le_of_lt hLt
    | none =>
      rw [hGetStmt] at hStep
      have hGe : length bb.statements ≤ s.frame.stmtIdx :=
        length_le_of_get?_eq_none bb.statements s.frame.stmtIdx hGetStmt
      have hEqIdx : s.frame.stmtIdx = length bb.statements :=
        Nat.le_antisymm hStmtLe hGe
      have hBeq : (s.frame.stmtIdx == length bb.statements) = true := by
        simp [hEqIdx]
      rw [hBeq] at hStep
      dsimp only [ite_true] at hStep
      rcases evalTerminator_intraFrame_step_frame body s s' bb.terminator hStack hIntra hStep with
        ⟨hStmtZero, hTargetMem⟩
      have hBbMem : bb ∈ body.basicBlocks :=
        (lt_length_and_mem_of_get? body.basicBlocks s.frame.blockIdx bb hBb).2
      unfold cfgTargetsInBounds at hCfg
      rcases Bool.and_eq_true_iff.mp hCfg with ⟨_, hAllBbs⟩
      have hBbOk : (terminatorTargets bb.terminator.kind).all
          (fun t => decide (t < length body.basicBlocks)) = true :=
        (List.all_eq_true.mp hAllBbs) bb hBbMem
      have hTargetLt : s'.frame.blockIdx < length body.basicBlocks :=
        of_decide_eq_true ((List.all_eq_true.mp hBbOk) s'.frame.blockIdx hTargetMem)
      rcases exists_get?_of_lt_length body.basicBlocks s'.frame.blockIdx hTargetLt with
        ⟨bb', hBb'⟩
      refine ⟨bb', hBb', ?_⟩
      rw [hStmtZero]
      exact Nat.zero_le _

/-! ## 9. Fail-Closed Coverage Reconciler & Soundness/Completeness Proofs -/

/--
Fail-closed outcome of reconciling a MIR body's independent fault-site census
against the obligation generator's discharged fault sites.
-/
inductive CoverageVerdict : Type where
  /-- Every fault site in `census` was discharged and has status `.emittedAndVerified`
      in the `PropertyRegistry`. -/
  | verified : CoverageVerdict
  /-- One or more fault sites in `census` were either omitted from `discharged`
      or belong to an un-emitted / unsupported `MirFaultClass` in `PropertyRegistry`
      (`UNKNOWN(UNSUPPORTED_CONSTRUCT)`). -/
  | unknownUnmappedFaultSites (missing : List FaultSite) : CoverageVerdict
  deriving DecidableEq, Repr, Inhabited

/--
Compute the list of fault sites in `census` missing from `discharged`.
-/
def unmappedFaultSites (census discharged : List FaultSite) : List FaultSite :=
  census.filter (fun site => !discharged.contains site)

/--
Reconcile `census` against `discharged` (under `allVerifiedRegistry`).
-/
def reconcileFaultCoverage (census discharged : List FaultSite) : CoverageVerdict :=
  match unmappedFaultSites census discharged with
  | [] => .verified
  | missing => .unknownUnmappedFaultSites missing

/--
Compute the list of fault sites in `census` that are either absent from
`discharged` or whose `faultClass` does not have `.emittedAndVerified` status in
`registry`.
-/
def unmappedFaultSitesWithRegistry
    (registry : PropertyRegistry) (census discharged : List FaultSite) :
    List FaultSite :=
  census.filter (fun site =>
    !(discharged.contains site && (registry site.faultClass).isVerified))

/--
Registry-gated fail-closed fault-coverage reconciler.
-/
def reconcileFaultCoverageWithRegistry
    (registry : PropertyRegistry) (census discharged : List FaultSite) :
    CoverageVerdict :=
  match unmappedFaultSitesWithRegistry registry census discharged with
  | [] => .verified
  | missing => .unknownUnmappedFaultSites missing

@[simp]
theorem mem_unmappedFaultSites_iff
    (census discharged : List FaultSite) (site : FaultSite) :
    site ∈ unmappedFaultSites census discharged ↔
      site ∈ census ∧ site ∉ discharged := by
  simp [unmappedFaultSites, List.mem_filter]

@[simp]
theorem PropertyStatus.isVerified_eq_false_iff (st : PropertyStatus) :
    st.isVerified = false ↔ st ≠ .emittedAndVerified := by
  cases st <;> decide

@[simp]
theorem mem_unmappedFaultSitesWithRegistry_iff
    (registry : PropertyRegistry) (census discharged : List FaultSite) (site : FaultSite) :
    site ∈ unmappedFaultSitesWithRegistry registry census discharged ↔
      site ∈ census ∧ (site ∉ discharged ∨ registry site.faultClass ≠ .emittedAndVerified) := by
  simp [unmappedFaultSitesWithRegistry, List.mem_filter]

/--
Soundness and completeness of `reconcileFaultCoverage`:
`reconcileFaultCoverage census discharged = .verified` if and only if every
`site ∈ census` belongs to `discharged`.
-/
theorem reconcileFaultCoverage_verified_iff
    (census discharged : List FaultSite) :
    reconcileFaultCoverage census discharged = .verified ↔
      ∀ site ∈ census, site ∈ discharged := by
  unfold reconcileFaultCoverage
  cases hUnm : unmappedFaultSites census discharged with
  | nil =>
    simp only [true_iff]
    intro site hInCensus
    cases hContains : discharged.contains site with
    | true => exact List.contains_iff_mem.mp hContains
    | false =>
      have hNotDis : site ∉ discharged := by
        intro hIn
        have hTrue : discharged.contains site = true := List.contains_iff_mem.mpr hIn
        rw [hContains] at hTrue
        nomatch hTrue
      have hMem : site ∈ unmappedFaultSites census discharged :=
        (mem_unmappedFaultSites_iff census discharged site).mpr ⟨hInCensus, hNotDis⟩
      rw [hUnm] at hMem
      nomatch hMem
  | cons hd tl =>
    simp only [reduceCtorEq, false_iff]
    intro hAll
    have hMem : hd ∈ unmappedFaultSites census discharged := by
      rw [hUnm]
      exact List.Mem.head tl
    rcases (mem_unmappedFaultSites_iff census discharged hd).mp hMem with ⟨hC, hNotD⟩
    exact hNotD (hAll hd hC)

/--
Whenever `reconcileFaultCoverage census discharged` returns
`.unknownUnmappedFaultSites missing`, `missing` is non-empty and contains
precisely the fault sites in `census` missing from `discharged`.
-/
theorem reconcileFaultCoverage_unknown_nonempty
    (census discharged missing : List FaultSite)
    (hVerdict : reconcileFaultCoverage census discharged = .unknownUnmappedFaultSites missing) :
    missing ≠ [] ∧
    ∀ site : FaultSite, site ∈ missing ↔ site ∈ census ∧ site ∉ discharged := by
  unfold reconcileFaultCoverage at hVerdict
  cases hUnm : unmappedFaultSites census discharged with
  | nil =>
    rw [hUnm] at hVerdict
    nomatch hVerdict
  | cons hd tl =>
    rw [hUnm] at hVerdict
    injection hVerdict with hEq
    subst hEq
    refine ⟨by simp, ?_⟩
    intro site
    rw [← hUnm]
    exact mem_unmappedFaultSites_iff census discharged site

/--
Soundness and completeness of `reconcileFaultCoverageWithRegistry`:
returns `.verified` if and only if every `site ∈ census` is in `discharged` AND
its `faultClass` has status `.emittedAndVerified` in `registry`.
-/
theorem reconcileFaultCoverageWithRegistry_verified_iff
    (registry : PropertyRegistry) (census discharged : List FaultSite) :
    reconcileFaultCoverageWithRegistry registry census discharged = .verified ↔
      ∀ site ∈ census,
        site ∈ discharged ∧ registry site.faultClass = .emittedAndVerified := by
  unfold reconcileFaultCoverageWithRegistry
  cases hUnm : unmappedFaultSitesWithRegistry registry census discharged with
  | nil =>
    simp only [true_iff]
    intro site hInCensus
    have hNotMem : site ∉ unmappedFaultSitesWithRegistry registry census discharged := by
      rw [hUnm]; intro h; nomatch h
    rw [mem_unmappedFaultSitesWithRegistry_iff] at hNotMem
    have hBoth : ¬ (site ∉ discharged ∨ registry site.faultClass ≠ .emittedAndVerified) :=
      fun hOr => hNotMem ⟨hInCensus, hOr⟩
    have hInDis : site ∈ discharged := by
      cases hContains : discharged.contains site with
      | true => exact List.contains_iff_mem.mp hContains
      | false =>
        have hNotD : site ∉ discharged := by
          intro hIn
          have hTrue : discharged.contains site = true := List.contains_iff_mem.mpr hIn
          rw [hContains] at hTrue
          nomatch hTrue
        exact False.elim (hBoth (Or.inl hNotD))
    have hRegOk : registry site.faultClass = .emittedAndVerified := by
      cases hR : registry site.faultClass with
      | emittedAndVerified => rfl
      | unsupportedFailClosed =>
        have hNe : registry site.faultClass ≠ .emittedAndVerified := by
          rw [hR]; intro h; nomatch h
        exact False.elim (hBoth (Or.inr hNe))
      | unemittedGap =>
        have hNe : registry site.faultClass ≠ .emittedAndVerified := by
          rw [hR]; intro h; nomatch h
        exact False.elim (hBoth (Or.inr hNe))
    exact ⟨hInDis, hRegOk⟩
  | cons hd tl =>
    simp only [reduceCtorEq, false_iff]
    intro hAll
    have hMem : hd ∈ unmappedFaultSitesWithRegistry registry census discharged := by
      rw [hUnm]; exact List.Mem.head tl
    rcases (mem_unmappedFaultSitesWithRegistry_iff registry census discharged hd).mp hMem with
      ⟨hC, hNotD | hNotReg⟩
    · exact hNotD (hAll hd hC).1
    · exact hNotReg (hAll hd hC).2

/--
Un-emitted / unsupported class rejection theorem
(`reconcileFaultCoverageWithRegistry_rejects_unemitted`):
if `site ∈ census` and `registry site.faultClass ≠ .emittedAndVerified`, then
`reconcileFaultCoverageWithRegistry registry census discharged` NEVER returns
`.verified`, even if `site ∈ discharged`.
-/
theorem reconcileFaultCoverageWithRegistry_rejects_unemitted
    (registry : PropertyRegistry) (census discharged : List FaultSite)
    (site : FaultSite)
    (hInCensus : site ∈ census)
    (hUnemitted : registry site.faultClass ≠ .emittedAndVerified) :
    reconcileFaultCoverageWithRegistry registry census discharged ≠ .verified := by
  intro hVer
  have hAll := (reconcileFaultCoverageWithRegistry_verified_iff registry census discharged).mp hVer
  exact hUnemitted (hAll site hInCensus).2

/--
Mutation Monotonicity / Probe Detection Theorem (`reconcileFaultCoverage_mutation_detected`):
if `site ∈ census` and a mutated obligation generator strips `site` from
`discharged'` (`site ∉ discharged'`), `reconcileFaultCoverage census discharged'`
returns `.unknownUnmappedFaultSites missing` with `site ∈ missing`.
-/
theorem reconcileFaultCoverage_mutation_detected
    (census discharged' : List FaultSite) (site : FaultSite)
    (hInCensus : site ∈ census)
    (hStripped : site ∉ discharged') :
    ∃ missing : List FaultSite,
      reconcileFaultCoverage census discharged' = .unknownUnmappedFaultSites missing ∧
      site ∈ missing := by
  have hMem : site ∈ unmappedFaultSites census discharged' :=
    (mem_unmappedFaultSites_iff census discharged' site).mpr ⟨hInCensus, hStripped⟩
  unfold reconcileFaultCoverage
  cases hUnm : unmappedFaultSites census discharged' with
  | nil =>
    rw [hUnm] at hMem
    nomatch hMem
  | cons hd tl =>
    refine ⟨hd :: tl, rfl, ?_⟩
    rw [← hUnm]
    exact hMem

/--
End-to-End Reconciled Fault-Coverage Theorem (`stepMirFn_fault_in_discharged_of_reconciled`):
when `reconcileFaultCoverageWithRegistry registry (censusMirBodyFaultSites body) discharged = .verified`,
any top-level `.ub` fault of `stepMirFn body s` from a valid program counter
`ValidMirPc body s.frame` is guaranteed to be present in `discharged` with
`registry cls = .emittedAndVerified`.
-/
theorem stepMirFn_fault_in_discharged_of_reconciled
    (registry : PropertyRegistry) (body : CapturedMir)
    (discharged : List FaultSite) (s : MachineState)
    (hVer : reconcileFaultCoverageWithRegistry registry
      (censusMirBodyFaultSites body) discharged = .verified)
    (hTop : s.memory.activeCallee = none)
    (hPc : ValidMirPc body s.frame)
    (hUb : stepMirFn body s = MirStepNode.fail .ub) :
    ∃ cls : MirFaultClass,
      (s.frame.blockIdx, s.frame.stmtIdx, cls) ∈ discharged ∧
      registry cls = .emittedAndVerified := by
  rcases stepMirFn_fault_in_census body s hTop hPc hUb with ⟨cls, hInCensus⟩
  have hAll :=
    (reconcileFaultCoverageWithRegistry_verified_iff
      registry (censusMirBodyFaultSites body) discharged).mp hVer
  rcases hAll (s.frame.blockIdx, s.frame.stmtIdx, cls) hInCensus with ⟨hInDis, hReg⟩
  exact ⟨cls, hInDis, hReg⟩

/-! ## 10. Compile-Time Kernel-Checked Witness Bodies & 4 False-Proof Mutation Probes (`0` `native_decide`) -/

/-- Default dummy ABI used by synthetic witness `CapturedMir` bodies. -/
def dummyWitnessFnAbi : FnAbi :=
  { args := List.nil
  , ret :=
      { layout :=
          { size := { bytes := 4 }
          , align := { bytes := 4 }
          , backendRepr :=
              (BackendRepr.scalar
                (ScalarLayout.initialized
                  (PrimitiveKind.int 32 false)
                  { start := 0, end_ := 4294967295 }))
          , fields := FieldsShape.primitive
          , variants := (VariantsShape.single 0)
          , isUninhabited := false
          }
      , mode := AbiPassMode.direct
      }
  , conv := CallConv.rust
  , canUnwind := false
  }

/--
Witness 0: Pure zero-fault MIR body (`witnessPureNoopBody`) containing `.nop`,
`.coverage`, `.constEvalCounter`, `.backwardIncompatibleDropHint`, and an
in-bounds `.goto 0` terminator.
-/
def witnessPureNoopBody : CapturedMir :=
  { defPath := "proto::witness_pure_noop"
  , phase := MirPhaseTag.runtimePostCleanup
  , role := ContractRole.subject
  , argCount := 0
  , localDecls :=
      (List.cons
        { mutability := Mutability.mut
        , ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 0 }
        , debugName := Option.none
        }
        List.nil)
  , basicBlocks :=
      (List.cons
        { statements :=
            (List.cons
              { kind := StatementKind.nop, span := "proto.rs:1:1" }
              (List.cons
                { kind := StatementKind.coverage, span := "proto.rs:1:2" }
                (List.cons
                  { kind := StatementKind.constEvalCounter, span := "proto.rs:1:3" }
                  (List.cons
                    { kind :=
                        (StatementKind.backwardIncompatibleDropHint
                          { local_ := 0, projection := List.nil })
                    , span := "proto.rs:1:4"
                    }
                    List.nil))))
        , terminator := { kind := (TerminatorKind.goto 0), span := "proto.rs:1:5" }
        , isCleanup := false
        }
        List.nil)
  , fnAbi := dummyWitnessFnAbi
  , layouts := emptyLayoutTable
  , allocations := List.nil
  }

/-- `witnessPureNoopBody` has zero fault sites (`[]`) and valid CFG targets. -/
theorem witnessPureNoopBody_census_empty :
    censusMirBodyFaultSites witnessPureNoopBody = [] ∧
    cfgTargetsInBounds witnessPureNoopBody = true := by
  decide

/--
By `stepMirFn_ne_ub_of_empty_census`, `witnessPureNoopBody` can never fault with
`MirStepNode.fail .ub` at any valid program counter.
-/
theorem witnessPureNoopBody_stepMirFn_ne_ub
    (s : MachineState)
    (hTop : s.memory.activeCallee = none)
    (hPc : ValidMirPc witnessPureNoopBody s.frame) :
    stepMirFn witnessPureNoopBody s ≠ MirStepNode.fail .ub :=
  stepMirFn_ne_ub_of_empty_census witnessPureNoopBody s hTop hPc
    witnessPureNoopBody_census_empty.1

/--
Witness 1 (`CallArgBlindProbe`): `TerminatorKind.call` passing a dereferenced
pointer argument `Operand.copy { local_ := 1, projection := [.deref] }` into a
callee `proto::callee_u32`.
-/
def witnessCallArgBlindBody : CapturedMir :=
  { defPath := "proto::witness_call_arg_blind"
  , phase := MirPhaseTag.runtimePostCleanup
  , role := ContractRole.subject
  , argCount := 1
  , localDecls :=
      (List.cons
        { mutability := Mutability.mut
        , ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }
        , debugName := Option.none
        }
        (List.cons
          { mutability := Mutability.not
          , ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 0 }
          , debugName := (Option.some "arg_ptr")
          }
          List.nil))
  , basicBlocks :=
      (List.cons
        { statements := List.nil
        , terminator :=
            { kind :=
                (TerminatorKind.call
                  (Operand.constant
                    { ty := { kind := (RigidTy.fnDef "proto::callee_u32" List.nil), layoutIdx := 0 }
                    , val := ConstValue.zeroSized
                    })
                  (List.cons
                    (Operand.copy
                      { local_ := 1
                      , projection := (List.cons ProjectionElem.deref List.nil)
                      })
                    List.nil)
                  { local_ := 0, projection := List.nil }
                  (Option.some 1)
                  UnwindAction.continue_)
            , span := "proto.rs:10:5"
            }
        , isCleanup := false
        }
        (List.cons
          { statements := List.nil
          , terminator := { kind := TerminatorKind.return_, span := "proto.rs:11:5" }
          , isCleanup := false
          }
          List.nil))
  , fnAbi := dummyWitnessFnAbi
  , layouts := emptyLayoutTable
  , allocations := List.nil
  }

/-- Expected fault-site census for `witnessCallArgBlindBody`. -/
def witnessCallArgBlindExpectedCensus : List FaultSite :=
  [ (0, 0, .ptrDerefInvalid)
  , (0, 0, .ptrAlignMismatch)
  , (0, 0, .treeBorrowsViolation)
  , (0, 0, .uninitRead)
  , (0, 0, .storageLiveProtected)
  , (0, 0, .callAbiMismatch)
  , (1, 0, .treeBorrowsViolation)
  , (1, 0, .uninitRead)
  , (1, 0, .callAbiMismatch)
  ]

/-- Mutated discharged set for `CallArgBlindProbe` (drops call-arg deref/align checks). -/
def witnessCallArgBlindMutantDischarged : List FaultSite :=
  [ (0, 0, .treeBorrowsViolation)
  , (0, 0, .uninitRead)
  , (0, 0, .storageLiveProtected)
  , (0, 0, .callAbiMismatch)
  , (1, 0, .treeBorrowsViolation)
  , (1, 0, .uninitRead)
  , (1, 0, .callAbiMismatch)
  ]

theorem witnessCallArgBlind_probe_verified_and_detected :
    censusMirBodyFaultSites witnessCallArgBlindBody = witnessCallArgBlindExpectedCensus ∧
    reconcileFaultCoverage
      (censusMirBodyFaultSites witnessCallArgBlindBody)
      witnessCallArgBlindExpectedCensus = .verified ∧
    reconcileFaultCoverage
      (censusMirBodyFaultSites witnessCallArgBlindBody)
      witnessCallArgBlindMutantDischarged =
        .unknownUnmappedFaultSites
          [(0, 0, .ptrDerefInvalid), (0, 0, .ptrAlignMismatch)] := by
  decide

/--
Witness 2 (`SwitchBreakStripProbe`): `TerminatorKind.switchInt` in `bb0`
branching to `bb1` (safe constant assignment) and `bb2` (unchecked division
`BinOp.div` at `(2, 0)`).
-/
def witnessSwitchBreakStripBody : CapturedMir :=
  { defPath := "proto::witness_switch_break_strip"
  , phase := MirPhaseTag.runtimePostCleanup
  , role := ContractRole.subject
  , argCount := 2
  , localDecls := List.nil
  , basicBlocks :=
      (List.cons
        { statements := List.nil
        , terminator :=
            { kind :=
                (TerminatorKind.switchInt
                  (Operand.copy { local_ := 1, projection := List.nil })
                  { branches := (List.cons (0, 1) List.nil), otherwise := 2 })
            , span := "proto.rs:20:5"
            }
        , isCleanup := false
        }
        (List.cons
          { statements :=
              (List.cons
                { kind :=
                    (StatementKind.assign
                      { local_ := 0, projection := List.nil }
                      (Rvalue.use
                        (Operand.constant
                          { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }
                          , val := (ConstValue.scalar (ConstScalar.int { bits := 42, sizeBytes := 4 }))
                          })))
                , span := "proto.rs:21:9"
                }
                List.nil)
          , terminator := { kind := TerminatorKind.return_, span := "proto.rs:21:15" }
          , isCleanup := false
          }
          (List.cons
            { statements :=
                (List.cons
                  { kind :=
                      (StatementKind.assign
                        { local_ := 0, projection := List.nil }
                        (Rvalue.binaryOp
                          BinOp.div
                          (Operand.copy { local_ := 1, projection := List.nil })
                          (Operand.copy { local_ := 2, projection := List.nil })))
                  , span := "proto.rs:22:9"
                  }
                  List.nil)
            , terminator := { kind := TerminatorKind.return_, span := "proto.rs:22:15" }
            , isCleanup := false
            }
            List.nil)))
  , fnAbi := dummyWitnessFnAbi
  , layouts := emptyLayoutTable
  , allocations := List.nil
  }

/-- Expected fault-site census for `witnessSwitchBreakStripBody`. -/
def witnessSwitchBreakStripExpectedCensus : List FaultSite :=
  [ (0, 0, .scalarNicheInvalid)
  , (0, 0, .uninitRead)
  , (1, 0, .treeBorrowsViolation)
  , (1, 0, .storageLiveProtected)
  , (1, 1, .treeBorrowsViolation)
  , (1, 1, .uninitRead)
  , (1, 1, .callAbiMismatch)
  , (2, 0, .arithOverflow)
  , (2, 0, .divRemByZero)
  , (2, 0, .treeBorrowsViolation)
  , (2, 0, .uninitRead)
  , (2, 0, .storageLiveProtected)
  , (2, 1, .treeBorrowsViolation)
  , (2, 1, .uninitRead)
  , (2, 1, .callAbiMismatch)
  ]

/-- Mutated discharged set for `SwitchBreakStripProbe` (strips `bb2` branch). -/
def witnessSwitchBreakStripMutantDischarged : List FaultSite :=
  (witnessSwitchBreakStripExpectedCensus.filter (fun s => s.1 != 2))

theorem witnessSwitchBreakStrip_probe_verified_and_detected :
    censusMirBodyFaultSites witnessSwitchBreakStripBody = witnessSwitchBreakStripExpectedCensus ∧
    reconcileFaultCoverage
      (censusMirBodyFaultSites witnessSwitchBreakStripBody)
      witnessSwitchBreakStripExpectedCensus = .verified ∧
    reconcileFaultCoverage
      (censusMirBodyFaultSites witnessSwitchBreakStripBody)
      witnessSwitchBreakStripMutantDischarged =
        .unknownUnmappedFaultSites
          [ (2, 0, .arithOverflow)
          , (2, 0, .divRemByZero)
          , (2, 0, .treeBorrowsViolation)
          , (2, 0, .uninitRead)
          , (2, 0, .storageLiveProtected)
          , (2, 1, .treeBorrowsViolation)
          , (2, 1, .uninitRead)
          , (2, 1, .callAbiMismatch)
          ] := by
  decide

/--
Witness 3 (`LoopUpdateOverflowProbe`): Loop CFG (`bb0` entry -> `bb1` header ->
`bb2` latch with `_1 = BinOp.add (copy _1) (const 1)` back-edge to `bb1`, or
exit to `bb3` return).
-/
def witnessLoopUpdateOverflowBody : CapturedMir :=
  { defPath := "proto::witness_loop_update_overflow"
  , phase := MirPhaseTag.runtimePostCleanup
  , role := ContractRole.subject
  , argCount := 1
  , localDecls := List.nil
  , basicBlocks :=
      (List.cons
        { statements := List.nil
        , terminator := { kind := (TerminatorKind.goto 1), span := "proto.rs:30:5" }
        , isCleanup := false
        }
        (List.cons
          { statements := List.nil
          , terminator :=
              { kind :=
                  (TerminatorKind.switchInt
                    (Operand.copy { local_ := 1, projection := List.nil })
                    { branches := (List.cons (0, 3) List.nil), otherwise := 2 })
              , span := "proto.rs:31:5"
              }
          , isCleanup := false
          }
          (List.cons
            { statements :=
                (List.cons
                  { kind :=
                      (StatementKind.assign
                        { local_ := 1, projection := List.nil }
                        (Rvalue.binaryOp
                          BinOp.add
                          (Operand.copy { local_ := 1, projection := List.nil })
                          (Operand.constant
                            { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }
                            , val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 }))
                            })))
                  , span := "proto.rs:32:9"
                  }
                  List.nil)
            , terminator := { kind := (TerminatorKind.goto 1), span := "proto.rs:32:20" }
            , isCleanup := false
            }
            (List.cons
              { statements := List.nil
              , terminator := { kind := TerminatorKind.return_, span := "proto.rs:33:5" }
              , isCleanup := false
              }
              List.nil))))
  , fnAbi := dummyWitnessFnAbi
  , layouts := emptyLayoutTable
  , allocations := List.nil
  }

/-- Expected fault-site census for `witnessLoopUpdateOverflowBody`. -/
def witnessLoopUpdateOverflowExpectedCensus : List FaultSite :=
  [ (1, 0, .scalarNicheInvalid)
  , (1, 0, .uninitRead)
  , (2, 0, .arithOverflow)
  , (2, 0, .treeBorrowsViolation)
  , (2, 0, .uninitRead)
  , (2, 0, .storageLiveProtected)
  , (3, 0, .treeBorrowsViolation)
  , (3, 0, .uninitRead)
  , (3, 0, .callAbiMismatch)
  ]

/--
Mutated discharged set for `LoopUpdateOverflowProbe`: discharges the local read/write
obligations at latch `(2, 0)` but drops `(2, 0, .arithOverflow)`!
-/
def witnessLoopUpdateOverflowMutantDischarged : List FaultSite :=
  witnessLoopUpdateOverflowExpectedCensus.filter (fun s => s != (2, 0, .arithOverflow))

theorem witnessLoopUpdateOverflow_probe_verified_and_detected :
    censusMirBodyFaultSites witnessLoopUpdateOverflowBody = witnessLoopUpdateOverflowExpectedCensus ∧
    reconcileFaultCoverage
      (censusMirBodyFaultSites witnessLoopUpdateOverflowBody)
      witnessLoopUpdateOverflowExpectedCensus = .verified ∧
    reconcileFaultCoverage
      (censusMirBodyFaultSites witnessLoopUpdateOverflowBody)
      witnessLoopUpdateOverflowMutantDischarged =
        .unknownUnmappedFaultSites [(2, 0, .arithOverflow)] := by
  decide

/--
Witness 4 (`DerefAliasProbe`): Pointer dereference write `*_1 = copy (*_2)` at
`(0, 0)` exercising `ptrDerefInvalid`, `ptrAlignMismatch`, and
`treeBorrowsViolation`.
-/
def witnessDerefAliasBody : CapturedMir :=
  { defPath := "proto::witness_deref_alias"
  , phase := MirPhaseTag.runtimePostCleanup
  , role := ContractRole.subject
  , argCount := 2
  , localDecls := List.nil
  , basicBlocks :=
      (List.cons
        { statements :=
            (List.cons
              { kind :=
                  (StatementKind.assign
                    { local_ := 1
                    , projection := (List.cons ProjectionElem.deref List.nil)
                    }
                    (Rvalue.use
                      (Operand.copy
                        { local_ := 2
                        , projection := (List.cons ProjectionElem.deref List.nil)
                        })))
              , span := "proto.rs:40:5"
              }
              List.nil)
        , terminator := { kind := TerminatorKind.return_, span := "proto.rs:41:5" }
        , isCleanup := false
        }
        List.nil)
  , fnAbi := dummyWitnessFnAbi
  , layouts := emptyLayoutTable
  , allocations := List.nil
  }

/-- Expected fault-site census for `witnessDerefAliasBody`. -/
def witnessDerefAliasExpectedCensus : List FaultSite :=
  [ (0, 0, .ptrDerefInvalid)
  , (0, 0, .ptrAlignMismatch)
  , (0, 0, .treeBorrowsViolation)
  , (0, 0, .uninitRead)
  , (0, 0, .storageLiveProtected)
  , (0, 1, .treeBorrowsViolation)
  , (0, 1, .uninitRead)
  , (0, 1, .callAbiMismatch)
  ]

/--
Mutated discharged set for `DerefAliasProbe`: omits pointer dereference,
alignment, and Tree Borrows aliasing obligations at `(0, 0)`.
-/
def witnessDerefAliasMutantDischarged : List FaultSite :=
  [ (0, 0, .uninitRead)
  , (0, 0, .storageLiveProtected)
  , (0, 1, .treeBorrowsViolation)
  , (0, 1, .uninitRead)
  , (0, 1, .callAbiMismatch)
  ]

theorem witnessDerefAlias_probe_verified_and_detected :
    censusMirBodyFaultSites witnessDerefAliasBody = witnessDerefAliasExpectedCensus ∧
    reconcileFaultCoverage
      (censusMirBodyFaultSites witnessDerefAliasBody)
      witnessDerefAliasExpectedCensus = .verified ∧
    reconcileFaultCoverage
      (censusMirBodyFaultSites witnessDerefAliasBody)
      witnessDerefAliasMutantDischarged =
        .unknownUnmappedFaultSites
          [ (0, 0, .ptrDerefInvalid)
          , (0, 0, .ptrAlignMismatch)
          , (0, 0, .treeBorrowsViolation)
          ] := by
  decide

/--
Compile-time `by decide` witness for `PropertyRegistry` un-emitted class
rejection: marking `.treeBorrowsViolation` as `.unemittedGap` causes
`reconcileFaultCoverageWithRegistry` to reject `witnessDerefAliasBody` even when
`discharged` equals the full `witnessDerefAliasExpectedCensus`.
-/
theorem witnessDerefAlias_registry_unemitted_rejected :
    let reg := registryWithStatus allVerifiedRegistry .treeBorrowsViolation .unemittedGap
    reconcileFaultCoverageWithRegistry reg
      (censusMirBodyFaultSites witnessDerefAliasBody)
      witnessDerefAliasExpectedCensus =
        .unknownUnmappedFaultSites
          [(0, 0, .treeBorrowsViolation), (0, 1, .treeBorrowsViolation)] := by
  decide

end Anneal.FaultSiteCensusPrototype
