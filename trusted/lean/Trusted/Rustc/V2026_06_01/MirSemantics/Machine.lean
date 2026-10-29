import Trusted.Refinement
import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.Eval

namespace Trusted.Rustc.V2026_06_01.MirSemantics

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst

/-!
Interaction-tree operational unfolding (`stepMirFn`, `stepMirState`, `mirTree`,
`mirCallTree`, `MirLang`, and `MirNoUBTree`) for `CapturedMir` (`#88`, `#100`,
`#102`, `#103`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L17-L56>

> "pub enum MirPhase {
>     Built,
>     Analysis(AnalysisPhase),
>     Runtime(RuntimePhase),
> }"

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/

/-- Initial `MachineState` for a `CapturedMir` body with argument values `args`. -/
def initMachineState (body : CapturedMir) (args : List Value) : MachineState :=
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals := initLocalsAux 0 body.localDecls args
    }
    memory := {
      nextAllocId := length body.allocations
      globals := body.allocations
      borrows := []
      nextTag := 1
      callees := []
      callStack := []
      activeCallee := none
    }
  }

/--
Initial `MachineState` for a `CapturedMir` body with argument values `args` and
available callee bodies `callees` for inline `TerminatorKind.call` resolution.

Reference (The Rust Reference, "Call expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/call-expr.html>

> "A call expression calls a function. It consists of an expression with a
> function type or a type that implements one of the Fn, FnMut, or FnOnce
> traits, followed by a parenthesized comma-separated list of argument
> expressions. If the function eventually returns, then the expression
> completes."
-/
def initMachineStateWithCallees
    (body : CapturedMir)
    (args : List Value)
    (callees : List CapturedMir) :
    MachineState :=
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals := initLocalsAux 0 body.localDecls args
    }
    memory := {
      nextAllocId := length body.allocations
      globals := body.allocations
      borrows := []
      nextTag := 1
      callees := callees
      callStack := []
      activeCallee := none
    }
  }

/--
One-step MIR coalgebra transition from an active `MachineState`.

When `s.memory.activeCallee` is `some callee`, execution steps within `callee`;
otherwise it steps within `body`. If the active body's `phase` is `.other _`,
stepping immediately fails closed with `MirStepNode.unsupported`.
-/
def stepMirFn (body : CapturedMir) (s : MachineState) : MirStepNode :=
  let currentBody := s.memory.activeCallee.getD body
  match currentBody.phase with
  | .other _ => MirStepNode.unsupported
  | _ =>
    match get? currentBody.basicBlocks s.frame.blockIdx with
    | none => MirStepNode.fail .ub
    | some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | some stmt => evalStmt s stmt currentBody.localDecls currentBody.layouts
      | none =>
        if s.frame.stmtIdx == length bb.statements then
          evalTerminator s bb.terminator (some currentBody)
        else
          MirStepNode.fail .ub

/-- Total `ITreeF` coalgebra step over `MirExecState`. -/
def stepMirState (body : CapturedMir) : MirExecState → MirStepNode
  | .running s => stepMirFn body s
  | .halted out => .ret out
  | .faulted fk => MirStepNode.fail fk

/-- Fundamental coinductive interaction tree of `body` unfolded from `s`. -/
def mirTree (body : CapturedMir) (s : MachineState) :
    ITree MirEffect MirOutcome :=
  ITree.cofix (stepMirState body) (.running s)

/-- Fundamental coinductive interaction tree of `body` invoked with `args`. -/
def mirCallTree (body : CapturedMir) (args : List Value) :
    ITree MirEffect MirOutcome :=
  mirTree body (initMachineState body args)

/-- Parameterized program pairing a `CapturedMir` body with input `args`. -/
structure MirCallInstance : Type where
  /-- Captured MIR body. -/
  body : CapturedMir
  /-- Incoming argument values for locals `_1..=_argCount`. -/
  args : List Value

/-- Layer 1A `Language` packaging `mirCallTree` via `ITree.lang`. -/
def MirLang : Language :=
  ITree.lang (fun (body : CapturedMir) (args : List Value) =>
    mirCallTree body args)

/-- All-prefix safety predicate on a MIR interaction tree (`TreeSafe`). -/
def MirNoUBTree (t : ITree MirEffect MirOutcome) : Prop :=
  TreeSafe t

end Trusted.Rustc.V2026_06_01.MirSemantics
