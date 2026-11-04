import Trusted.Refinement
import Trusted.Effect
import Trusted.ITree
import Trusted.MirAst
import Trusted.MirSemantics

namespace Trusted.VerificationResult

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.MirAst
open Trusted.MirSemantics

/-!
Trusted verification gate types (`Claim`, `VerificationResult`, `StatefulClaim`,
`StatefulVerificationResult`, `ModularClaim`, `ModularVerificationResult`,
`TraceClaim`, `TraceVerificationResult`, `TotalClaim`, and
`TotalVerificationResult`) over MIR interaction trees (`mirTree`), checked by
the Lean 4 kernel and audited by `trusted/audit/check_trusted.py` (`#100`,
`#102`, `#103`).

Because `mirTree` models unresolved external calls through `MirCallE`, the
default `Claim` and `StatefulClaim` gates leave external calls unconstrained: a
proof of `VerificationResult` or `StatefulVerificationResult` must hold across
all possible external-call answers `MirCallAns` (including distinct answers
across consecutive calls, mutated memories, and unwinding). Explicit rely
assumptions on external callees are stated via `ModularClaim` as predicates on
`ExternalCallHandler`s interpreted through `ITree.interp`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "It is the programmer’s responsibility when writing unsafe code to ensure that
> any safe code interacting with the unsafe code cannot trigger these
> behaviors. unsafe code that satisfies this property for any safe client is
> called sound; if unsafe code can be misused by safe code to exhibit
> undefined behavior, it is unsound."
-/

/-- Cryptographic and toolchain identity of a verified compilation unit. -/
structure ArtifactIdentity : Type where
  /-- Crate-qualified `DefId` path of the verified item. -/
  defPath : DefPath
  /-- Recorded MIR dialect tag (e.g., `"V2026_06_01"`). -/
  mirDialect : String
  /-- SHA-256 hex digest of the generated `Mir/<Item>.lean` module. -/
  mirModuleSha256 : String
  deriving DecidableEq, Repr

/--
Initial `MachineState` for `body` with incoming `args` and initial `Memory`
`mem`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L368>

> "At any point during the execution of a function, each local is either
> allocated or unallocated. Except as noted below, all locals except function
> parameters are initially unallocated."
-/
def initMachineStateWithMemory
    (body : CapturedMir) (args : List Value) (mem : Memory) : MachineState :=
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals := initLocals body args
    }
    memory := mem
  }

/--
Populate `mem.callees` with `defaultCallees` when `defaultCallees` is
non-empty, preserving `mem` definitionally when `defaultCallees` is `[]`.

Reference (The Rust Reference, "Call expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/call-expr.html>

> "A call expression calls a function. It consists of an expression called the
> called function operand, followed by a parenthesized comma-separated list of
> expression operands called the argument operands."
-/
def Memory.withDefaultCallees
    (mem : Memory) (defaultCallees : List CapturedMir) : Memory :=
  match defaultCallees with
  | [] => mem
  | _ :: _ => { mem with callees := defaultCallees }

/--
Initial `MachineState` for `body` with incoming `args`, initial `Memory` `mem`,
and default callee table `callees`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L368>

> "At any point during the execution of a function, each local is either
> allocated or unallocated. Except as noted below, all locals except function
> parameters are initially unallocated."
-/
def initMachineStateWithMemoryAndCallees
    (body : CapturedMir)
    (args : List Value)
    (mem : Memory)
    (callees : List CapturedMir := .nil) : MachineState :=
  initMachineStateWithMemory body args (Memory.withDefaultCallees mem callees)

/--
Fundamental coinductive interaction tree of `body` on `args` with linked
callee table `callees`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1203>

> "Block ends with the call of a function."
-/
def mirCallTreeWithCallees
    (body : CapturedMir)
    (args : List Value)
    (callees : List CapturedMir := .nil) :
    ITree MirEffect MirOutcome :=
  mirTree body (initMachineStateWithCallees body args callees)

/-- Fundamental coinductive interaction tree of `body` from `(args, mem)`. -/
def mirStatefulTree
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    ITree MirEffect MirOutcome :=
  mirTree body (initMachineStateWithMemory body args mem)

/--
Fundamental coinductive interaction tree of `body` from `(args, mem)` with
default callee table `callees`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1203>

> "Block ends with the call of a function."
-/
def mirStatefulTreeWithCallees
    (body : CapturedMir)
    (args : List Value)
    (mem : Memory)
    (callees : List CapturedMir := .nil) :
    ITree MirEffect MirOutcome :=
  mirTree body (initMachineStateWithMemoryAndCallees body args mem callees)

/-! ## 1. Stateless Partial-Correctness Claims (`Claim`, `VerificationResult`) -/

/--
Smyth `Partial` behavior of `body` on `args` with linked `callees`, projected
from `mirCallTreeWithCallees`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def MirExecPartialWithCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) :=
  (mirCallTreeWithCallees body args callees).toPartial

/--
Smyth `Partial` behavior of `body` on `args`, projected from `mirCallTree`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def MirExecPartial (body : CapturedMir) (args : List Value) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) :=
  MirExecPartialWithCallees body .nil args

/--
Stateless partial contract separating `safetyPre` (`.defined`) from `pre` and
`post` (`.val`).
-/
def MirContractSpec
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop)
    (args : List Value) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) where
  defined := safetyPre args
  val _ outPair :=
    pre args →
      ∀ retVal mem', outPair.2 = .normal (retVal, mem') → post args retVal

/--
Pointwise Smyth refinement claim with linked `callees` and separate `safetyPre`
and `pre`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def MirContractHoldsWithSafetyAndCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirExecPartialWithCallees body callees ≤ MirContractSpec safetyPre pre post

/-- Pointwise Smyth refinement claim with separate `safetyPre` and `pre`. -/
def MirContractHoldsWithSafety
    (body : CapturedMir)
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirContractHoldsWithSafetyAndCallees body .nil safetyPre pre post

/--
Pointwise Smyth refinement claim with linked `callees` (`safetyPre := pre`).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def MirContractHoldsWithCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirContractHoldsWithSafetyAndCallees body callees pre pre post

/-- Pointwise Smyth refinement claim (`safetyPre := pre`). -/
def MirContractHolds
    (body : CapturedMir)
    (pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirContractHoldsWithCallees body .nil pre post

/--
Companion boolean contract helper predicate with linked `callees`: on `args`,
`specBody` is `TreeSafe` and every normal return yields `true`
(`.scalar ⟨1, 1⟩`).

Reference (The Rust Reference, "Boolean type"):
<https://doc.rust-lang.org/1.98.0/reference/types/boolean.html>

> "The value false has the bit pattern 0x00 and the value true has the bit
> pattern 0x01. It is undefined behavior for an object with the boolean type to
> have any other bit pattern."
-/
def MirBoolPredicateHoldsWithCallees
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value) : Prop :=
  MirContractHoldsWithCallees
    specBody
    callees
    (· = args)
    (fun _ ret => ret = .scalar { bits := 1, sizeBytes := 1 })

/--
Companion boolean contract helper predicate: on `args`, `specBody` is `TreeSafe`
and every normal return yields `true` (`.scalar ⟨1, 1⟩`).

Reference (The Rust Reference, "Boolean type"):
<https://doc.rust-lang.org/1.98.0/reference/types/boolean.html>

> "The value false has the bit pattern 0x00 and the value true has the bit
> pattern 0x01. It is undefined behavior for an object with the boolean type to
> have any other bit pattern."
-/
def MirBoolPredicateHolds (specBody : CapturedMir) (args : List Value) : Prop :=
  MirBoolPredicateHoldsWithCallees specBody .nil args

/-- Stateless verification claim for a captured Rust item. -/
structure Claim : Type 1 where
  body : CapturedMir
  pre : List Value → Prop
  post : List Value → Value → Prop
  callees : List CapturedMir := .nil

/-- Proposition denoted by `c : Claim`. -/
def Claim.holds (c : Claim) : Prop :=
  MirContractHoldsWithCallees c.body c.callees c.pre c.post

/-- Audited kernel verification certificate for `c : Claim`. -/
structure VerificationResult (c : Claim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its stateless contract. -/
class ItemSpec (defId : String) : Type 1 where
  pre : List Value → Prop := fun _ => True
  post : List Value → Value → Prop := fun _ _ => True

/-- Typeclass packaging a kernel-checked `VerificationResult c` for `defId`. -/
class ItemProof (defId : String) (c : Claim) : Prop where
  verified : VerificationResult c

/-! ## 2. Stateful Partial-Correctness Claims (`StatefulClaim`, `StatefulVerificationResult`) -/

/--
Smyth `Partial` stateful behavior with linked `callees`, projected from
`mirStatefulTreeWithCallees`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def MirStatefulExecPartialWithCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value)
    (mem : Memory) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) :=
  (mirStatefulTreeWithCallees body args mem callees).toPartial

/-- Smyth `Partial` stateful behavior projected from `mirStatefulTree`. -/
def MirStatefulExecPartial
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) :=
  MirStatefulExecPartialWithCallees body .nil args mem

/-- Stateful partial contract separating `safetyPre` from `pre` and `post`. -/
def MirStatefulContractSpec
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (args : List Value) (mem : Memory) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) where
  defined := safetyPre args mem
  val _ outPair :=
    pre args mem →
      ∀ retVal mem',
        outPair.2 = .normal (retVal, mem') → post args mem retVal mem'

/--
Pointwise stateful Smyth refinement with linked `callees` and separate
`safetyPre` and `pre`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def MirStatefulContractHoldsWithSafetyAndCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Prop :=
  MirStatefulExecPartialWithCallees body callees ≤
    MirStatefulContractSpec safetyPre pre post

/-- Pointwise stateful Smyth refinement with separate `safetyPre` and `pre`. -/
def MirStatefulContractHoldsWithSafety
    (body : CapturedMir)
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Prop :=
  MirStatefulContractHoldsWithSafetyAndCallees body .nil safetyPre pre post

/--
Pointwise stateful Smyth refinement with linked `callees` (`safetyPre := pre`).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def MirStatefulContractHoldsWithCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Prop :=
  MirStatefulContractHoldsWithSafetyAndCallees body callees pre pre post

/-- Pointwise stateful Smyth refinement (`safetyPre := pre`). -/
def MirStatefulContractHolds
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Prop :=
  MirStatefulContractHoldsWithCallees body .nil pre post

/-- Stateful verification claim over `(args, mem)`. -/
structure StatefulClaim : Type 1 where
  body : CapturedMir
  pre : List Value → Memory → Prop
  post : List Value → Memory → Value → Memory → Prop
  callees : List CapturedMir := .nil

/-- Proposition denoted by `c : StatefulClaim`. -/
def StatefulClaim.holds (c : StatefulClaim) : Prop :=
  MirStatefulContractHoldsWithCallees c.body c.callees c.pre c.post

/-- Audited kernel verification certificate for `c : StatefulClaim`. -/
structure StatefulVerificationResult (c : StatefulClaim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its stateful contract. -/
class StatefulItemSpec (defId : String) : Type 1 where
  pre : List Value → Memory → Prop := fun _ _ => True
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Typeclass packaging a `StatefulVerificationResult c` for `defId`. -/
class StatefulItemProof (defId : String) (c : StatefulClaim) : Prop where
  verified : StatefulVerificationResult c

/-! ## 3. Modular Rely–Guarantee Claims (`ModularClaim`, `ModularVerificationResult`) -/

/-- Closed MIR effect remaining once `MirCallE` is handled. -/
abbrev MirClosedEffect : Effect.{0} := SumE MirFailE MirObsE

/-- Handler interpreting external `MirCallReq` calls into `MirClosedEffect`. -/
abbrev ExternalCallHandler : Type :=
  MirCallReq → ITree MirClosedEffect MirCallAns

/-- Lift an `ExternalCallHandler` across `MirEffect`. -/
def handleMirExternalCalls (h : ExternalCallHandler) :
    (i : MirEffect.I) → ITree MirClosedEffect (MirEffect.O i)
  | .inl (.fail fk) => ITree.fail (E := MirClosedEffect) fk
  | .inr (.inl (.emit obs)) => ITree.emit (E := MirClosedEffect) obs
  | .inr (.inr (.call req)) => h req

/--
Interpret external calls in `mirStatefulTreeWithCallees body args mem callees`
with `h`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1203>

> "Block ends with the call of a function."
-/
def mirHandledTreeWithCallees
    (body : CapturedMir)
    (args : List Value)
    (mem : Memory)
    (callees : List CapturedMir)
    (h : ExternalCallHandler) :
    ITree MirClosedEffect MirOutcome :=
  ITree.interp
    (handleMirExternalCalls h)
    (mirStatefulTreeWithCallees body args mem callees)

/-- Interpret external calls in `mirStatefulTree body args mem` with `h`. -/
def mirHandledTree
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (h : ExternalCallHandler) :
    ITree MirClosedEffect MirOutcome :=
  mirHandledTreeWithCallees body args mem .nil h

/-- Contract specification over `MirClosedEffect`. -/
def MirClosedStatefulContractSpec
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (args : List Value) (mem : Memory) :
    Partial (BehaviorSet (List (Event MirClosedEffect) × MirOutcome)) where
  defined := safetyPre args mem
  val _ outPair :=
    pre args mem →
      ∀ retVal mem',
        outPair.2 = .normal (retVal, mem') → post args mem retVal mem'

/-- Rely–guarantee call contract over `MirCallReq` and `MirCallAns`. -/
structure MirCallContract : Type where
  pre : MirCallReq → Prop := fun _ => True
  post : MirCallReq → MirCallAns → Prop := fun _ _ => True

/--
Pointee kinds whose references and raw pointers are wide (fat) pointers in the
operational value model, carried as
`Value.aggregate 0 [Value.ptr p sz, metadata]` (see the `.ref` / `.rawPtr` cases
of `encodeValueToBytes` and `decodeValueFromBytes`): slices `[T]`, string
slices `str`, and trait objects `dyn Trait`.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types
>     - Pointers to slices and `str` also store the number of elements.
>     - Pointers to trait objects also store a pointer to a vtable."
-/
def rigidTyIsWidePointee : RigidTy → Bool
  | .slice _ => true
  | .str => true
  | .dynamic _ => true
  | _ => false

/--
Pointee kinds that are statically `Sized` (or extern `foreign` types, which are
unsized but use thin pointers), so that references and raw pointers to them are
always thin pointers. Generic parameters, aliases, ADTs (which may have an
unsized tail field), non-empty tuples, and unrendered `.other` types may be
either thin or wide.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Structs may contain a DST as the last field; this makes the struct itself a
> DST."
-/
def rigidTyIsThinPointee : RigidTy → Bool
  | .bool => true
  | .char => true
  | .int _ => true
  | .uint _ => true
  | .float _ => true
  | .never => true
  | .array _ _ => true
  | .ref _ _ => true
  | .rawPtr _ _ => true
  | .fnDef _ _ => true
  | .fnPtr _ _ _ _ => true
  | .closure _ _ => true
  | .foreign _ => true
  | .tuple .nil => true
  | _ => false

/--
Validity of a thin pointer, reference, or function-pointer `Value`: either a
provenance-carrying `Value.ptr` or a provenance-free address scalar (as produced
for dangling-but-aligned references to zero-sized constants and integer-valued
raw pointers).

Reference (The Rust Reference, "Pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

> "Raw pointers are pointers without safety or liveness guarantees."
-/
def thinPointerValueValid (v : Value) : Prop :=
  Or (∃ p sz, v = .ptr p sz) (∃ sv, v = .scalar sv)

/--
Validity of a wide pointer `Value` to an unsized `pointee`: a data pointer
paired with a 64-bit `usize` length metadata scalar (`len < scalarModulus 8`)
for slices and `str`, or with thin-pointer vtable metadata for `dyn Trait`.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Pointers to slices and `str` also store the number of elements."
-/
def widePointerValueValid (pointee : RigidTy) (v : Value) : Prop :=
  match pointee with
  | .dynamic _ =>
    ∃ p sz metadata,
      And (thinPointerValueValid metadata)
        (v = .aggregate 0 (.ptr p sz :: metadata :: .nil))
  | _ =>
    ∃ p sz len,
      And (len < scalarModulus 8)
        (v = .aggregate 0 (.ptr p sz :: .scalar { bits := len, sizeBytes := 8 } :: .nil))

/--
Validity of a reference or raw-pointer `Value` whose pointee is `pointee`:
wide for slices, `str`, and `dyn Trait`; thin for statically `Sized` (and
`foreign`) pointees; and either thin or wide when the pointee may be unsized
(generic parameters, aliases, ADTs with a possibly unsized tail, and non-empty
tuples).

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types"
-/
def pointerValueValid (pointee : RigidTy) (v : Value) : Prop :=
  match rigidTyIsWidePointee pointee with
  | true => widePointerValueValid pointee v
  | false =>
    match rigidTyIsThinPointee pointee with
    | true => thinPointerValueValid v
    | false =>
      Or (thinPointerValueValid v)
        (∃ p sz metadata,
          And (thinPointerValueValid metadata)
            (v = .aggregate 0 (.ptr p sz :: metadata :: .nil)))

/--
Pointwise element validity predicate over a tuple's `List RigidTy` field types
and `List Value` runtime field values.

Reference (The Rust Reference, "Tuple types"):
<https://doc.rust-lang.org/1.98.0/reference/types/tuple.html>

> "Tuple types are a family of structural types for heterogeneous lists of
> other types."
-/
@[reducible]
def valuesMatchElemPred (P : RigidTy → Value → Prop) :
    List RigidTy → List Value → Prop
  | .nil, .nil => True
  | ty :: tys, v :: vs => And (P ty v) (valuesMatchElemPred P tys vs)
  | _, _ => False

/--
Homogeneous element validity predicate over an array's `List Value` elements.

Reference (The Rust Reference, "Array types"):
<https://doc.rust-lang.org/1.98.0/reference/types/array.html>

> "An array is a fixed-size sequence of `N` elements of type `T`."
-/
@[reducible]
def valuesAllSatisfyPred (P : Value → Prop) : List Value → Prop
  | .nil => True
  | v :: vs => And (P v) (valuesAllSatisfyPred P vs)

/--
Whether every `RigidTy` in a list of tuple field types admits `Value.unit`
(so the composite tuple is zero-sized and may be represented by `Value.unit`).
-/
@[reducible]
def typesAllAdmitUnit (P : RigidTy → Value → Prop) : List RigidTy → Prop
  | .nil => True
  | ty :: tys => And (P ty .unit) (typesAllAdmitUnit P tys)

/--
Fuel-bounded recursive runtime `Value` validity predicate against a `RigidTy`,
an optional top-level `layoutIdx` in `layouts`, and `LayoutTable`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Producing an invalid value. Producing a value happens any time a value is
> assigned to or read from a place, passed to a function/primitive operation or
> returned from a function/primitive operation."
-/
def valueValidForRigidTy :
    Nat →
    Trusted.Rustc.V2026_06_01.Layout.LayoutTable →
    Option Nat →
    RigidTy →
    Value →
    Prop
  | 0, _, _, _, _ => True
  | _ + 1, _, _, .bool, v =>
    ∃ b : Nat, b < 2 ∧ v = .scalar { bits := b, sizeBytes := 1 }
  | _ + 1, _, _, .char, v =>
    ∃ cp : Nat,
      (cp < 0xD800 ∨ (0xE000 ≤ cp ∧ cp ≤ 0x10FFFF)) ∧
      v = .scalar { bits := cp, sizeBytes := 4 }
  | _ + 1, _, _, .int w, v =>
    match intCastTargetBytes (.int w) with
    | .some bytes =>
      ∃ bits : Nat,
        bits < scalarModulus bytes ∧
        v = .scalar { bits := bits, sizeBytes := bytes }
    | .none => ∃ sv, v = .scalar sv
  | _ + 1, _, _, .uint w, v =>
    match intCastTargetBytes (.uint w) with
    | .some bytes =>
      ∃ bits : Nat,
        bits < scalarModulus bytes ∧
        v = .scalar { bits := bits, sizeBytes := bytes }
    | .none => ∃ sv, v = .scalar sv
  | _ + 1, _, _, .float _, v => ∃ sv, v = .scalar sv
  | _ + 1, _, _, .never, _ => False
  | _ + 1, _, _, .tuple .nil, v => Or (v = .unit) (v = .aggregate 0 .nil)
  | fuel + 1, layouts, _, .tuple (elemTy :: restTys), v =>
    Or
      (v = .unit ∧
        typesAllAdmitUnit
          (valueValidForRigidTy fuel layouts .none)
          (elemTy :: restTys))
      (∃ fields,
        v = .aggregate 0 fields ∧
        Trusted.Sequence.length fields = Trusted.Sequence.length (elemTy :: restTys) ∧
        valuesMatchElemPred
          (valueValidForRigidTy fuel layouts .none)
          (elemTy :: restTys)
          fields)
  | fuel + 1, layouts, _, .array elemTy len, v =>
    Or
      (v = .unit ∧
        (len = 0 ∨ valueValidForRigidTy fuel layouts .none elemTy .unit))
      (∃ elems,
        v = .aggregate 0 elems ∧
        Trusted.Sequence.length elems = len ∧
        valuesAllSatisfyPred
          (valueValidForRigidTy fuel layouts .none elemTy)
          elems)
  | _ + 1, _, _, .ref _ pointee, v => pointerValueValid pointee v
  | _ + 1, _, _, .rawPtr _ pointee, v => pointerValueValid pointee v
  | _ + 1, _, _, .fnPtr _ _ _ _, v => thinPointerValueValid v
  | _ + 1, _, _, .fnDef _ _, v => Or (v = .unit) (v = .aggregate 0 .nil)
  | _ + 1, _, _, .closure _ _, v =>
    Or (v = .unit) (∃ vIdx fields, v = .aggregate vIdx fields)
  | _ + 1, layouts, optLayoutIdx, .adt defPath _, _ =>
    match stringEq defPath "core::convert::Infallible" with
    | true => False
    | false =>
      match optLayoutIdx with
      | .some layoutIdx =>
        match Trusted.Sequence.get? layouts.entries layoutIdx with
        | .some layout =>
          match layout.isUninhabited with
          | true => False
          | false => True
        | .none => True
      | .none => True
  | _ + 1, _, _, .param _ _, _ => True
  | _ + 1, _, _, .alias _ _, _ => True
  | _ + 1, _, _, .slice _, _ => True
  | _ + 1, _, _, .str, _ => True
  | _ + 1, _, _, .dynamic _, _ => True
  | _ + 1, _, _, .foreign _, _ => True
  | _ + 1, _, _, .other _, _ => True

/--
Well-typed runtime `Value` validity predicate against a captured MIR `Ty` and
`LayoutTable`, used to type the arguments and return value of default
`#[external_spec]` call contracts.

The predicate must never be stronger than the operational value model: it is
assumed of external return values, so an over-strong case would exclude real
callee behaviors and make modular claims vacuous. It therefore accepts every
representation that `MirSemantics` can produce for a valid value of `ty`:
- `bool` is `0` or `1` of width `1`, `char` is a Unicode scalar value of width
  `4`, and integers have the width of their type (`intCastTargetBytes`) with
  in-range bits;
- `()` and function items are `Value.unit` or the empty aggregate;
- references and raw pointers follow `pointerValueValid` (wide `[ptr, meta]`
  aggregates for slices, `str`, and `dyn Trait`), and function pointers are
  thin pointers;
- tuples and arrays are `Value.unit` (zero-sized constants) or aggregates of the
  declared arity whose elements recursively satisfy `valueValidForRigidTy`;
- ADTs with an uninhabited layout have no valid value;
- `!` has no valid value; and
- generic parameters, aliases, unsized types (which are never passed or returned
  by value), floats' bit patterns, and unrendered `.other` types are not
  further constrained.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Producing an invalid value. Producing a value happens any time a value is
> assigned to or read from a place, passed to a function/primitive operation or
> returned from a function/primitive operation."
>
> "The following is a non-exhaustive list of invalid values:
> - A `bool` that isn't 0 or 1.
> - A `char` that is a surrogate or above `char::MAX`.
> - A `!`."
-/
def valueValidForTy
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (ty : Ty)
    (v : Value) : Prop :=
  valueValidForRigidTy 8 layouts (.some ty.layoutIdx) ty.kind v

/--
Return-local layout and type validity predicate for local `_0` (`decl`) under
`layouts`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L369-L370>

> "The first local is the return value pointer, followed by `arg_count` locals
> for the function arguments, followed by any user-declared variables and
> temporaries."
-/
def valueValidForReturnDecl
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (decl : LocalDecl)
    (retVal : Value) : Prop :=
  valueValidForTy layouts decl.ty retVal

/--
Return-type and layout validity predicate for a captured callee or
`#[external_spec]` sidecar `calleeBody`, constraining `retVal` against return
local `_0` (`calleeBody.localDecls[0]`) and `calleeBody.layouts`. A body without
locals (never produced by `anneal-rustc-capture`) imposes no constraint.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L369-L370>

> "The first local is the return value pointer, followed by `arg_count` locals
> for the function arguments, followed by any user-declared variables and
> temporaries."
-/
def retMatchesCalleeReturnTy
    (calleeBody : CapturedMir) (retVal : Value) : Prop :=
  match calleeBody.localDecls with
  | retDecl :: _ => valueValidForReturnDecl calleeBody.layouts retDecl retVal
  | .nil => True

/--
Pointwise validity of incoming argument values `args` against parameter local
declarations `paramDecls` (locals `_1..=_argCount`) under `layouts`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L369-L370>

> "The first local is the return value pointer, followed by `arg_count` locals
> for the function arguments, followed by any user-declared variables and
> temporaries."
-/
def argsValidForParamDecls
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable) :
    List LocalDecl → List Value → Prop
  | decl :: decls, arg :: args =>
    And (valueValidForTy layouts decl.ty arg) (argsValidForParamDecls layouts decls args)
  | _, _ => True

/--
Argument-type and layout validity predicate for a captured callee or
`#[external_spec]` sidecar `calleeBody`, constraining each argument in `args`
against the corresponding parameter local of `calleeBody`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Producing a value happens any time a value is assigned to or read from a
> place, passed to a function/primitive operation or returned from a
> function/primitive operation."
-/
def argsMatchCalleeParamTys
    (calleeBody : CapturedMir) (args : List Value) : Prop :=
  match calleeBody.localDecls with
  | _ :: paramDecls => argsValidForParamDecls calleeBody.layouts paramDecls args
  | .nil => True

/--
Frame condition relating the `Memory` at an external call site (`before`) to the
`Memory` handed back by the callee (`after`). An external callee returns (or
unwinds) to the same suspended call stack, active body, active caller
protectors, and immutable callee code table, and it keeps every existing
reified function-pointer entry (it may only prepend fresh entries, as
`internFnPtr` does). It may mutate global and caller-owned referent state,
the Tree Borrows tag table (a write through an argument reference changes tag
permissions, and reborrows inside the callee push tags), and the fresh
allocation, tag, and protector counters, so those are left unconstrained.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L812-L853>

> "/// Returns from the function.
> ///
> /// Like function calls, the exact semantics of returns in Rust are unclear.
> /// Returning very likely at least assigns the value currently in the return
> /// place (`_0`) to the place specified in the associated `Call` terminator
> /// in the calling function, as if assigned via `dest = move _0`."
-/
def callFramePreserved (before after : Memory) : Prop :=
  And (after.callees = before.callees)
    (And (after.callStack = before.callStack)
      (And (after.activeCallee = before.activeCallee)
        (And (after.activeProtectors = before.activeProtectors)
          (∃ fresh, after.fnPtrs = List.append fresh before.fnPtrs))))

/--
Whether the target of a captured `#[external_spec]` `sidecarBody` may unwind
(`MirCallAns.panicked`), as recorded in `sidecarBody.fnAbi.canUnwind`.
`anneal-rustc-capture` copies the calling convention and unwind capability of
the resolved target into the sidecar's `fnAbi` (`FnAbi::can_unwind` from
`tcx.fn_abi_of_instance`, which is `false` for `extern "C"` and other nounwind
ABIs, for `-C panic=abort`, and for `#[rustc_nounwind]` items, and `true` for
`extern "Rust"` and `extern "C-unwind"`). The calling convention alone does not
decide this: `extern "C"` and `extern "C-unwind"` share `CallConv.c`.

Reference (The Rust Reference, "External blocks - ABI"):
<https://doc.rust-lang.org/1.98.0/reference/items/external-blocks.html#abi>

> "The strings that end with `-unwind` ... are the same as the corresponding ABI
> strings without `-unwind`, except that they allow the called function to
> safely unwind the stack (for example, via a Rust panic or a C++ exception)
> through the foreign frame into the caller's frame."
-/
@[reducible]
def sidecarTargetCanUnwind (sidecarBody : CapturedMir) : Bool :=
  sidecarBody.fnAbi.canUnwind

/--
Well-typed modular `MirCallContract` for an `#[external_spec(for = <target>)]`
declaration with canonical target path `targetDefPath` and captured signature
sidecar `sidecarBody`.

The precondition requires the target path, the argument arity, the
argument-type validity of every argument (`argsMatchCalleeParamTys`), and the
optional `requires` clause `extraPre`. The postcondition assumes only what holds
of every Rust or FFI callee with that signature: a normal return yields a value
satisfying the return type and layout (`retMatchesCalleeReturnTy`) and the
optional `ensures` clause `extraPost`, with arbitrary heap mutation but the same
call frame (`callFramePreserved`); unwinding is permitted when the target ABI
can unwind (`sidecarTargetCanUnwind sidecarBody = true`, preserving the call
frame) and forbidden for nounwind ABIs (`extern "C"`); and aborting is
unconstrained. It does not assume that the callee leaves memory unchanged or
that a Rust `fn` never panics, since neither follows from a signature or from
`requires`/`ensures` clauses over arguments and return values.

Reference (The Rust Reference, "Call expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/call-expr.html>

> "A call expression calls a function. It consists of an expression called the
> called function operand, followed by a parenthesized comma-separated list of
> expression operands called the argument operands."

Reference (The Rust Reference, "External blocks - ABI"):
<https://doc.rust-lang.org/1.98.0/reference/items/external-blocks.html#abi>

> "By default external blocks assume that the library they are calling uses
> the standard C ABI on the specific platform."
-/
def externalSpecCallContract
    (targetDefPath : DefPath)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True) :
    MirCallContract where
  pre req :=
    And (req.defPath = targetDefPath)
      (And (Trusted.Sequence.length req.args = sidecarBody.argCount)
        (And (argsMatchCalleeParamTys sidecarBody req.args)
          (extraPre req.args)))
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      And (callFramePreserved req.memory memAfter)
        (And (retMatchesCalleeReturnTy sidecarBody retVal)
          (extraPost req.args retVal))
    | .panicked memAfter =>
      match sidecarTargetCanUnwind sidecarBody with
      | true => callFramePreserved req.memory memAfter
      | false => False
    | .aborted => True

/--
Semantic rely predicate stating that an `ExternalCallHandler` `h` implements
`C : MirCallContract` over `MirClosedEffect`: for every request satisfying
`C.pre req`, `h req` is `TreeSafe` and every normal return satisfies
`C.post req ans`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "It is the programmer’s responsibility when writing unsafe code to ensure that
> any safe code interacting with the unsafe code cannot trigger these
> behaviors. unsafe code that satisfies this property for any safe client is
> called sound; if unsafe code can be misused by safe code to exhibit
> undefined behavior, it is unsound."
-/
def MirCallContract.holdsOn
    (C : MirCallContract) (h : ExternalCallHandler) : Prop :=
  ∀ req : MirCallReq,
    C.pre req →
    TreeSafe (h req) ∧
    ∀ tr ans, ReachesRet (h req) tr ans → C.post req ans

/-- Modular claim parameterized by an explicit rely predicate `envAssumed`. -/
structure ModularClaim : Type 1 where
  body : CapturedMir
  envAssumed : ExternalCallHandler → Prop
  pre : List Value → Memory → Prop
  post : List Value → Memory → Value → Memory → Prop
  callees : List CapturedMir := .nil

/-- Proposition denoted by `c : ModularClaim`. -/
def ModularClaim.holds (c : ModularClaim) : Prop :=
  ∀ h : ExternalCallHandler,
    c.envAssumed h →
      (fun args mem =>
        (mirHandledTreeWithCallees c.body args mem c.callees h).toPartial) ≤
        MirClosedStatefulContractSpec c.pre c.pre c.post

/-- Audited kernel verification certificate for `c : ModularClaim`. -/
structure ModularVerificationResult (c : ModularClaim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its modular contract. -/
class ModularItemSpec (defId : String) : Type 1 where
  envAssumed : ExternalCallHandler → Prop := fun _ => True
  pre : List Value → Memory → Prop := fun _ _ => True
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Typeclass packaging a `ModularVerificationResult c` for `defId`. -/
class ModularItemProof (defId : String) (c : ModularClaim) : Prop where
  verified : ModularVerificationResult c

/-! ## 4. Trace-Aware Claims (`TraceClaim`, `TraceVerificationResult`) -/

/-- Trace-aware contract predicating on completed `List (Event MirEffect)`. -/
def MirTraceContractSpec
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → List (Event MirEffect) → MirOutcome → Prop)
    (args : List Value) (mem : Memory) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) where
  defined := pre args mem
  val _ outPair := post args mem outPair.1 outPair.2

/-- Trace-aware verification claim. -/
structure TraceClaim : Type 1 where
  body : CapturedMir
  pre : List Value → Memory → Prop
  post : List Value → Memory → List (Event MirEffect) → MirOutcome → Prop
  callees : List CapturedMir := .nil

/-- Proposition denoted by `c : TraceClaim`. -/
def TraceClaim.holds (c : TraceClaim) : Prop :=
  MirStatefulExecPartialWithCallees c.body c.callees ≤
    MirTraceContractSpec c.pre c.post

/-- Audited kernel verification certificate for `c : TraceClaim`. -/
structure TraceVerificationResult (c : TraceClaim) : Prop where
  proof : c.holds

/-! ## 5. Total-Correctness Claims (`TotalClaim`, `TotalVerificationResult`) -/

/--
Total-correctness claim requiring UB-freedom (`TreeSafe`), reactive productivity
(`Productive`), absence of silent divergence (`¬ MayDiverge`), absence of
panics or aborts, and postcondition satisfaction on all returns.
-/
structure TotalClaim : Type 1 where
  body : CapturedMir
  pre : List Value → Memory → Prop
  post : List Value → Memory → Value → Memory → Prop
  callees : List CapturedMir := .nil

/-- Proposition denoted by `c : TotalClaim`. -/
def TotalClaim.holds (c : TotalClaim) : Prop :=
  ∀ args mem,
    c.pre args mem →
      let t := mirStatefulTreeWithCallees c.body args mem c.callees
      TreeSafe t ∧
      Productive t ∧
      ¬ MayDiverge t ∧
      ∀ tr out,
        ReachesRet t tr out →
          ∃ retVal mem',
            out = .normal (retVal, mem') ∧ c.post args mem retVal mem'

/-- Audited kernel verification certificate for `c : TotalClaim`. -/
structure TotalVerificationResult (c : TotalClaim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its total-correctness contract. -/
class TotalItemSpec (defId : String) : Type 1 where
  pre : List Value → Memory → Prop := fun _ _ => True
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Typeclass packaging a `TotalVerificationResult c` for `defId`. -/
class TotalItemProof (defId : String) (c : TotalClaim) : Prop where
  verified : TotalVerificationResult c

/-! ## 6. Program-to-Program Behavioral Refinement Claims (`StatefulEquivClaim`, `StatefulEquivVerificationResult`) -/

/--
Effect handler silencing internal `MirObsE` (`switchInt` branch-tag step
observations) into `.ret PUnit.unit` while preserving all `MirFailE` faults
(undefined behavior, panics, and aborts) and unresolved external `MirCallE`
calls.

Silencing `MirObsE` compares programs by their external call/return behavior,
heap mutations, and UB/panic safety rather than internal CFG branching
structure (`switchInt`), matching Rust's observable-behavior equivalence model.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def silenceMirObs : (i : MirEffect.I) → ITree MirEffect (MirEffect.O i)
  | .inl (.fail fk) => ITree.fail (E := MirEffect) fk
  | .inr (.inl _) => .ret PUnit.unit
  | .inr (.inr (.call req)) =>
    ITree.trigger (E := MirEffect) (.inr (.inr (.call req)))

/--
Branch-observation-erased stateful interaction tree of `body` from `(args, mem)`
with linked `callees`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1185-L1190>

> "Block ends with testing the value of an operand and jumping depending on its
> value."
-/
def mirObsErasedStatefulTreeWithCallees
    (body : CapturedMir)
    (args : List Value)
    (mem : Memory)
    (callees : List CapturedMir := .nil) :
    ITree MirEffect MirOutcome :=
  ITree.interp
    silenceMirObs
    (mirStatefulTreeWithCallees body args mem callees)

/--
Branch-observation-erased stateful interaction tree of `body` from `(args, mem)`,
enabling Smyth `Partial` behavioral comparison across optimizations that alter
internal CFG branching structure (such as loop unrolling or word-lane
vectorization) while preserving external `MirCallE` events, memory outcomes, and
UB/panic faults.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1185-L1190>

> "Block ends with testing the value of an operand and jumping depending on its
> value."
-/
def mirObsErasedStatefulTree
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    ITree MirEffect MirOutcome :=
  mirObsErasedStatefulTreeWithCallees body args mem .nil

/--
Pointwise Smyth behavioral refinement from candidate implementation `implBody`
(with `implCallees`) to reference specification `specBody` (with `specCallees`)
under `pre` over branch-observation-erased execution.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "It is the programmer’s responsibility when writing unsafe code to ensure that
> any safe code interacting with the unsafe code cannot trigger these
> behaviors. unsafe code that satisfies this property for any safe client is
> called sound; if unsafe code can be misused by safe code to exhibit
> undefined behavior, it is unsound."
-/
def RefinesStatefulMirWithCallees
    (implBody : CapturedMir)
    (implCallees : List CapturedMir)
    (specBody : CapturedMir)
    (specCallees : List CapturedMir)
    (pre : List Value → Memory → Prop) : Prop :=
  ∀ args mem,
    pre args mem →
      (mirObsErasedStatefulTreeWithCallees implBody args mem implCallees).toPartial ≤
        (mirObsErasedStatefulTreeWithCallees specBody args mem specCallees).toPartial

/--
Pointwise Smyth behavioral refinement from candidate implementation `implBody`
to reference specification implementation `specBody` under `pre` over
branch-observation-erased execution (`mirObsErasedStatefulTree`): whenever
`pre args mem` holds and `specBody` is UB-free on `(args, mem)`, `implBody`
is also UB-free (`TreeSafe`) and every completed external-call trace and outcome
of `implBody` is permitted by `specBody`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "It is the programmer’s responsibility when writing unsafe code to ensure that
> any safe code interacting with the unsafe code cannot trigger these
> behaviors. unsafe code that satisfies this property for any safe client is
> called sound; if unsafe code can be misused by safe code to exhibit
> undefined behavior, it is unsound."
-/
def RefinesStatefulMir
    (implBody specBody : CapturedMir)
    (pre : List Value → Memory → Prop) : Prop :=
  RefinesStatefulMirWithCallees implBody .nil specBody .nil pre

/--
Program-to-program total behavioral equivalence and refinement claim pairing a
candidate `implBody` (such as an `unsafe` optimization) against a frozen
reference `specBody` (such as an existing safe Rust implementation): under
`pre`, `implBody` satisfies total correctness (`TotalClaim.holds`: UB-free,
productive, non-divergent, non-panicking, and satisfying `post`) and refines
`specBody` in the Smyth `Partial` order (`RefinesStatefulMir`).
-/
structure StatefulEquivClaim : Type 1 where
  implBody : CapturedMir
  specBody : CapturedMir
  pre : List Value → Memory → Prop
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True
  implCallees : List CapturedMir := .nil
  specCallees : List CapturedMir := .nil

/-- Proposition denoted by `c : StatefulEquivClaim`. -/
def StatefulEquivClaim.holds (c : StatefulEquivClaim) : Prop :=
  RefinesStatefulMirWithCallees
    c.implBody c.implCallees c.specBody c.specCallees c.pre ∧
  ({ body := c.implBody
     pre := c.pre
     post := c.post
     callees := c.implCallees } : TotalClaim).holds

/-- Audited kernel verification certificate for `c : StatefulEquivClaim`. -/
structure StatefulEquivVerificationResult (c : StatefulEquivClaim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its reference `specBody` and contract. -/
class StatefulEquivItemSpec (defId : String) : Type 1 where
  specBody : CapturedMir
  pre : List Value → Memory → Prop := fun _ _ => True
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Typeclass packaging a `StatefulEquivVerificationResult c` for `defId`. -/
class StatefulEquivItemProof (defId : String) (c : StatefulEquivClaim) : Prop where
  verified : StatefulEquivVerificationResult c

/-! ## 7. Scoped UB-Exception Claims (`UbExceptionClaim`, `UbExceptionVerificationResult`) -/

/--
Scoped verification-exception claim for a captured Rust item that is known to
potentially exhibit undefined behavior outside a restricted subdomain
`strictSafetyPre` (for example, an intentional zero-copy `&[u8]` borrow over a
concurrently mutable hardware or pager VMO where `strictSafetyPre` requires the
VMO to be exclusively owned/trusted, while callers invoke it across a broader
precondition `pre`).

Unlike an unconstrained `axiom` asserting `StatefulVerificationResult` (which
would assert `TreeSafe` on inputs where `mirStatefulTree` deterministically
steps to `.fail .ub`, introducing `False` into the Lean kernel),
`UbExceptionClaim` is proved **constructively with zero axioms** by
establishing two obligations:
1. **Strict Safety on `pre ∧ strictSafetyPre`**: Under the restricted
   subdomain `c.pre args mem ∧ c.strictSafetyPre args mem`, `c.body` is
   completely UB-free (`TreeSafe`) and every normal return satisfies `c.post`
   (`MirStatefulContractHoldsWithSafety`).
2. **Normal-Return Postcondition Across All `pre`**: Across the full caller
   precondition `c.pre args mem` (even when `¬ c.strictSafetyPre args mem`
   and a UB fault may occur), every non-faulting normal return
   `ReachesRet (mirStatefulTree c.body args mem) tr (.normal (retVal, mem'))`
   still satisfies `c.post args mem retVal mem'` (and no `.fail .unsupported`
   is reached under `mirUbWaivedWP`).

`TrustedBoundary.lean` treats `UbExceptionVerificationResult` as an explicit
conditional verification exception (gated behind `--allow-assumptions` /
`--allow-ub-exceptions` and surfaced in the audit summary). Callers isolate
themselves from the exempted callee's potential `.fail .ub` by verifying
against `c.callContract.holdsOn` via `ModularVerificationResult` and linking
via `linkUbExceptionCallee`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "It is the programmer’s responsibility when writing unsafe code to ensure that
> any safe code interacting with the unsafe code cannot trigger these
> behaviors. unsafe code that satisfies this property for any safe client is
> called sound; if unsafe code can be misused by safe code to exhibit
> undefined behavior, it is unsound."
-/
structure UbExceptionClaim : Type 1 where
  body : CapturedMir
  pre : List Value → Memory → Prop
  strictSafetyPre : List Value → Memory → Prop := fun _ _ => False
  post : List Value → Memory → Value → Memory → Prop
  callees : List CapturedMir := .nil

/-- Proposition denoted by `c : UbExceptionClaim`. -/
def UbExceptionClaim.holds (c : UbExceptionClaim) : Prop :=
  MirStatefulContractHoldsWithSafetyAndCallees
    c.body
    c.callees
    (fun args mem => c.pre args mem ∧ c.strictSafetyPre args mem)
    c.pre
    c.post ∧
  ∀ args mem,
    c.pre args mem →
    ∀ tr retVal mem',
      ReachesRet
        (mirStatefulTreeWithCallees c.body args mem c.callees)
        tr
        (.normal (retVal, mem')) →
      c.post args mem retVal mem'

/--
Modular call contract exported by `c : UbExceptionClaim` to callers: callers
must establish `c.pre req.args req.memory` at the call site and may rely on
`c.post req.args req.memory retVal mem'` upon normal return.
-/
def UbExceptionClaim.callContract (c : UbExceptionClaim) : MirCallContract where
  pre req := req.defPath = c.body.defPath ∧ c.pre req.args req.memory
  post req ans :=
    ∃ retVal mem',
      ans = .returned retVal mem' ∧
      c.post req.args req.memory retVal mem'

/-- Audited kernel verification certificate for `c : UbExceptionClaim`. -/
structure UbExceptionVerificationResult (c : UbExceptionClaim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its scoped UB-exception contract. -/
class UbExceptionItemSpec (defId : String) : Type 1 where
  pre : List Value → Memory → Prop := fun _ _ => True
  strictSafetyPre : List Value → Memory → Prop := fun _ _ => False
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Typeclass packaging a `UbExceptionVerificationResult c` for `defId`. -/
class UbExceptionItemProof (defId : String) (c : UbExceptionClaim) : Prop where
  verified : UbExceptionVerificationResult c

/-! ## 8. Specification Non-Vacuity Obligations (`NonVacuousPre`, `NonVacuousStatefulPre`) -/

/-- Witness obligation asserting that a stateless precondition `pre` is satisfiable. -/
def NonVacuousPre (pre : List Value → Prop) : Prop :=
  ∃ args, pre args

/-- Witness obligation asserting that a stateful precondition `pre` is satisfiable. -/
def NonVacuousStatefulPre (pre : List Value → Memory → Prop) : Prop :=
  ∃ args mem, pre args mem

/-! ## 9. Whole-Crate Verification Rollup (`CrateItemEntry`, `CrateClaim`, `CrateVerificationResult`) -/

/-- Per-item entry in a whole-crate verification rollup manifest. -/
structure CrateItemEntry : Type 1 where
  /-- Cryptographic and toolchain identity of the captured Rust item. -/
  identity : ArtifactIdentity
  /-- Kernel-checked per-item verification certificate proposition (`Verify.<Item>.verified`'s type). -/
  certificate : Prop

/-- Whole-crate claim bundling every captured Rust item in a compilation unit. -/
structure CrateClaim : Type 1 where
  /-- Crate name recorded by `rustc-capture` in `CaptureManifest.json`. -/
  crateName : String
  /-- Recorded MIR dialect tag (e.g., `"V2026_06_01"`). -/
  mirDialect : String
  /-- Exhaustive list of captured Rust items and their verification certificates. -/
  items : List CrateItemEntry

/-- Conjunction asserting that every `CrateItemEntry` certificate in `items` holds. -/
def AllCrateItemsHold : List CrateItemEntry → Prop
  | [] => True
  | item :: rest => item.certificate ∧ AllCrateItemsHold rest

/-- Proposition denoted by `c : CrateClaim`: the crate has at least one
verified item and every captured item's kernel certificate holds. -/
def CrateClaim.holds (c : CrateClaim) : Prop :=
  c.items ≠ [] ∧ AllCrateItemsHold c.items

/-- Audited whole-crate verification certificate checked by `TrustedBoundary.lean`. -/
structure CrateVerificationResult (c : CrateClaim) : Prop where
  proof : c.holds

end Trusted.VerificationResult
