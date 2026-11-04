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
Well-typed runtime `Value` validity predicate against a captured MIR `Ty` and
`LayoutTable`, constraining scalar bit-widths and bit-bounds, boolean bit
patterns (`0` or `1`), Unicode scalar values (`char`), pointer/reference
metadata, and aggregate field arities.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Producing an invalid value. Producing a value happens any time a value is
> assigned to or read from a place, passed to a function/primitive operation or
> returned from a function/primitive operation."
-/
def valueValidForTy
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (ty : Ty)
    (v : Value) : Prop :=
  let byteSz :=
    match Trusted.Sequence.get? layouts.entries ty.layoutIdx with
    | .some layout => layout.size.bytes
    | .none =>
      match tyScalarBytes ty with
      | .some sz => sz
      | .none => 0
  match ty.kind with
  | .bool =>
    ∃ b : Nat, b < 2 ∧ v = .scalar { bits := b, sizeBytes := 1 }
  | .char =>
    ∃ cp : Nat,
      (cp < 0xD800 ∨ (0xE000 ≤ cp ∧ cp ≤ 0x10FFFF)) ∧
      v = .scalar { bits := cp, sizeBytes := 4 }
  | .int _ =>
    ∃ bits : Nat,
      bits < scalarModulus byteSz ∧
      v = .scalar { bits := bits, sizeBytes := byteSz }
  | .uint _ =>
    ∃ bits : Nat,
      bits < scalarModulus byteSz ∧
      v = .scalar { bits := bits, sizeBytes := byteSz }
  | .float _ =>
    ∃ bits : Nat,
      bits < scalarModulus byteSz ∧
      v = .scalar { bits := bits, sizeBytes := byteSz }
  | .rawPtr _ _ =>
    ∃ ptr sz, v = .ptr ptr sz
  | .ref _ _ =>
    ∃ ptr sz, v = .ptr ptr sz
  | .tuple elemTys =>
    match elemTys with
    | .nil => v = .unit
    | _ :: _ =>
      ∃ fields,
        v = .aggregate 0 fields ∧
        Trusted.Sequence.length fields = Trusted.Sequence.length elemTys
  | .array _ len =>
    ∃ fields,
      v = .aggregate 0 fields ∧
      Trusted.Sequence.length fields = len
  | .slice _ =>
    ∃ ptr sz, v = .ptr ptr sz
  | .str =>
    ∃ ptr sz, v = .ptr ptr sz
  | .fnDef _ _ => v = .unit
  | .fnPtr _ _ _ _ =>
    ∃ ptr sz, v = .ptr ptr sz
  | .closure _ _ =>
    (byteSz = 0 ∧ v = .unit) ∨
    (∃ vIdx fields, v = .aggregate vIdx fields)
  | .adt _ _ =>
    (byteSz = 0 ∧ v = .unit) ∨
    (∃ bits,
      bits < scalarModulus byteSz ∧
      v = .scalar { bits := bits, sizeBytes := byteSz }) ∨
    (∃ ptr sz, v = .ptr ptr sz) ∨
    (∃ vIdx fields, v = .aggregate vIdx fields)
  | .param _ _ =>
    (byteSz = 0 ∧ v = .unit) ∨
    (∃ bits,
      bits < scalarModulus byteSz ∧
      v = .scalar { bits := bits, sizeBytes := byteSz }) ∨
    (∃ ptr sz, v = .ptr ptr sz) ∨
    (∃ vIdx fields, v = .aggregate vIdx fields)
  | .alias _ _ =>
    (byteSz = 0 ∧ v = .unit) ∨
    (∃ bits,
      bits < scalarModulus byteSz ∧
      v = .scalar { bits := bits, sizeBytes := byteSz }) ∨
    (∃ ptr sz, v = .ptr ptr sz) ∨
    (∃ vIdx fields, v = .aggregate vIdx fields)
  | .dynamic _ =>
    ∃ ptr sz, v = .ptr ptr sz
  | .foreign _ =>
    ∃ ptr sz, v = .ptr ptr sz
  | .never => False
  | .other _ => False

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
local `_0` (`calleeBody.localDecls[0]`) and `calleeBody.layouts`.

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
  | .nil => False

/--
Well-typed modular `MirCallContract` for an `#[external_spec(for = <target>)]`
declaration with canonical target path `targetDefPath` and captured signature
sidecar `sidecarBody`, enforcing argument arity and return-type/layout validity
(`retMatchesCalleeReturnTy sidecarBody retVal`) alongside optional `extraPre`
and `extraPost` clauses.

Reference (The Rust Reference, "Call expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/call-expr.html>

> "A call expression calls a function. It consists of an expression called the
> called function operand, followed by a parenthesized comma-separated list of
> expression operands called the argument operands."
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
        (extraPre req.args))
  post req ans :=
    ∃ retVal,
      And (ans = .returned retVal req.memory)
        (And (retMatchesCalleeReturnTy sidecarBody retVal)
          (extraPost req.args retVal))

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
