import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Terminators
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Places

namespace Trusted.Rustc.V2026_06_01.MirSemantics

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst

/-!
Small-step interaction-tree execution of basic-block `Terminator`s
(`lookupSwitchTarget`, `findCallee?`, `extractCalleeDefPath?`, `evalTerminator`)
for `Runtime(PostCleanup)` MIR at `rustc 1.98.0-nightly (14210df0e 2026-05-31)`
(`#88`, `#100`, `#102`).
-/

/--
Look up target basic block in `SwitchTargets` by matching `val` against explicit
branches, falling back to `otherwise`.
-/
def lookupSwitchTarget
    (val : Nat) :
    List (Nat × BasicBlockIdx) → BasicBlockIdx → BasicBlockIdx
  | .nil, otherwise => otherwise
  | (branchVal, target) :: rest, otherwise =>
    match Nat.beq val branchVal with
    | true => target
    | false => lookupSwitchTarget val rest otherwise

/--
Look up a callee `CapturedMir` body in `callees` by its canonical `DefPath`.
-/
def findCallee? : List CapturedMir → DefPath → Option CapturedMir
  | .nil, _ => .none
  | body :: rest, defPath =>
    match stringEq body.defPath defPath with
    | true => .some body
    | false => findCallee? rest defPath

/--
Extract the target `DefPath` from a constant function-item `Operand` in
`TerminatorKind.call` or `TerminatorKind.tailCall`.

Reference (The Rust Reference, "Function item types"):
<https://doc.rust-lang.org/1.98.0/reference/types/function-item.html>

> "When referred to, a function item, or the constructor of a tuple-like struct
> or enum variant, yields a zero-sized value of its function item type. That
> type uniquely identifies the function"
-/
def extractCalleeDefPath? : Operand → Option DefPath
  | .constant c =>
    match c.ty.kind with
    | .fnDef defPath _ => .some defPath
    | _ =>
      match c.val with
      | .unevaluated defPath => .some defPath
      | _ => .none
  | _ => .none

/--
Extract the monomorphized generic `typeArgs` from a constant function-item
`Operand` (`RigidTy.fnDef defPath typeArgs`), or `.nil` otherwise.

Reference (The Rust Reference, "Function item types"):
<https://doc.rust-lang.org/1.98.0/reference/types/function-item.html>

> "When referred to, a function item, or the constructor of a tuple-like struct
> or enum variant, yields a zero-sized value of its function item type. That
> type uniquely identifies the function"
-/
def extractCalleeTypeArgs : Operand → List RigidTy
  | .constant c =>
    match c.ty.kind with
    | .fnDef _ typeArgs => typeArgs
    | _ => .nil
  | _ => .nil

/--
Extract the target `(defPath, typeArgs)` pair from a direct constant
function-item `Operand`.

Reference (The Rust Reference, "Function item types"):
<https://doc.rust-lang.org/1.98.0/reference/types/function-item.html>

> "When referred to, a function item, or the constructor of a tuple-like struct
> or enum variant, yields a zero-sized value of its function item type. That
> type uniquely identifies the function"
-/
def extractCallee? (op : Operand) : Option (DefPath × List RigidTy) :=
  match extractCalleeDefPath? op with
  | .some defPath => .some (defPath, extractCalleeTypeArgs op)
  | .none => .none

/--
Resolved call target metadata for a direct function-item (`RigidTy.fnDef`) or
indirect function-pointer (`RigidTy.fnPtr`) call in `TerminatorKind.call` and
`TerminatorKind.tailCall`.

Reference (The Rust Reference, "Call expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/call-expr.html>

> "A call expression calls a function. It consists of an expression with a
> function type or a type that implements one of the Fn, FnMut, or FnOnce
> traits, followed by a parenthesized comma-separated list of argument
> expressions."
-/
structure ResolvedCallTarget : Type where
  /-- Canonical `DefPath` of the resolved callee. -/
  defPath : DefPath
  /-- Monomorphized generic type arguments (`RigidTy.fnDef defPath typeArgs`). -/
  typeArgs : List RigidTy := .nil
  /-- Optional function-pointer signature (`RigidTy.fnPtr inputs output safety abi`)
      when invoked indirectly through a reified function pointer. -/
  fnSig : Option RigidTy := .none
  /-- True when resolved indirectly via a runtime `Value.ptr` function pointer. -/
  isIndirect : Bool := false

/--
Outcome of resolving the `func : Operand` of a `TerminatorKind.call` or
`TerminatorKind.tailCall`.
-/
inductive CallTargetResult : Type where
  /-- `func` resolved to `target` with updated caller `locals'`. -/
  | ok (target : ResolvedCallTarget) (locals' : List LocalSlot) : CallTargetResult
  /-- Evaluating `func` or validating its function-pointer provenance, arity, or
      ABI signature triggered undefined behavior. -/
  | ub : CallTargetResult
  /-- Evaluating `func` encountered an unmodeled construct. -/
  | unsupported : CallTargetResult

/--
Test whether a function pointer's reified `Safety` (`sigSafety`) is compatible
with the call site's declared function-pointer `Safety` (`callerSafety`).

Because a safe function pointer (`Safety.safe`) coerces to an `unsafe` function
pointer (`Safety.unsafe_`) via `PointerCoercion::UnsafeFnPointer`, `.safe` is
compatible with both `.safe` and `.unsafe_`; an `.unsafe_` function pointer is
compatible only with an `.unsafe_` call-site signature.

Reference (The Rust Reference, "Type coercions"):
<https://doc.rust-lang.org/1.98.0/reference/type-coercions.html#coercion-types>

> "* Safe function pointer types to `unsafe` function pointer types"
-/
@[reducible]
def safetyCompatible : Safety → Safety → Bool
  | .safe, _ => true
  | .unsafe_, .unsafe_ => true
  | .unsafe_, .safe => false

/--
Test whether a reified `FnPtrEntry` signature is compatible with a call site's
argument count `argCount` and optional declared `func` operand type
`callerFuncTyOpt`.

Checks that:
1. If `fnEntry.fnSig` is `.some (.fnPtr sigInputs _ _ sigAbi)`,
   `sigAbi != .rustIntrinsic` and `length sigInputs == argCount`.
2. If `callerFuncTyOpt` is
   `.some { kind := .fnPtr callerInputs callerOutput callerSafety callerAbi, .. }`,
   `callerAbi != .rustIntrinsic`, `length callerInputs == argCount`, and (when
   `fnEntry.fnSig` is present) `callerInputs`, `callerOutput`, `callerAbi`, and
   `safetyCompatible sigSafety callerSafety` match `fnEntry.fnSig`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Calling a function with the wrong call ABI or unwinding from a function
>   with the wrong unwind ABI."
-/
def fnEntryCompatibleWithCallSite
    (fnEntry : FnPtrEntry)
    (argCount : Nat)
    (callerFuncTyOpt : Option Ty) :
    Bool :=
  let entryArityOk :=
    match fnEntry.fnSig with
    | .none => true
    | .some (.fnPtr sigInputs _ _ sigAbi) =>
      Bool.and
        (Bool.not (callConvEq sigAbi .rustIntrinsic))
        (Nat.beq (length sigInputs) argCount)
    | .some _ => false
  let callerSigOk :=
    match callerFuncTyOpt with
    | .none => true
    | .some { kind := .fnPtr callerInputs callerOutput callerSafety callerAbi, .. } =>
      Bool.and
        (Bool.not (callConvEq callerAbi .rustIntrinsic))
        (Bool.and
          (Nat.beq (length callerInputs) argCount)
          (match fnEntry.fnSig with
           | .none => true
           | .some (.fnPtr sigInputs sigOutput sigSafety sigAbi) =>
             Bool.and
               (Nat.beq (length callerInputs) (length sigInputs))
               (Bool.and
                 (callConvEq callerAbi sigAbi)
                 (Bool.and
                   (safetyCompatible sigSafety callerSafety)
                   (Bool.and
                     (rigidTyListEq callerInputs sigInputs)
                     (rigidTyEq callerOutput sigOutput))))
           | .some _ => false))
    | .some _ => false
  Bool.and entryArityOk callerSigOk

/--
Resolve the target function `(defPath, typeArgs, fnSig)` of a direct or indirect
`TerminatorKind.call` / `TerminatorKind.tailCall` operand `func`.

- When `extractCalleeDefPath? func` is `.some defPath`, resolves directly without
  mutating `s.frame.locals`.
- Otherwise evaluates `func` via `evalOperand`:
  - If `func` evaluates to `.ptr ptrVal 8` at `offsetBytes == 0`, not aliasing any
    stack borrow in `s.memory.borrows`, and registered in `s.memory.fnPtrs` with
    compatible signature and arity (`fnEntryCompatibleWithCallSite`), resolves to
    the indirect target `fnEntry`.
  - If `func` evaluates to a zero-sized `.unit` / `.aggregate 0 .nil` whose
    `operandTy` is a function item (`extractFnItemTarget?`), resolves to that
    function item.
  - Otherwise faults with `CallTargetResult.ub`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L841-L853>

> "Call {
>     func: Operand<'tcx>,
>     args: Box<[Spanned<Operand<'tcx>>]>,
>     destination: Place<'tcx>,
>     target: Option<BasicBlock>,
>     unwind: UnwindAction,
>     call_source: CallSource,
>     fn_span: Span,
> },"
-/
@[simp]
def resolveCallTarget
    (s : MachineState)
    (func : Operand)
    (argCount : Nat)
    (bodyLocalDecls : List LocalDecl := .nil)
    (bodyLayouts : LayoutTable := emptyLayoutTable) :
    CallTargetResult :=
  match extractCalleeDefPath? func with
  | .some defPath =>
    .ok
      { defPath := defPath
        typeArgs := extractCalleeTypeArgs func
        fnSig := .none
        isIndirect := false }
      s.frame.locals
  | .none =>
    match
      evalOperand
        s.frame.locals
        func
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
    with
    | .ub => .ub
    | .unsupported => .unsupported
    | .ok (.ptr ptrVal sz) localsAfterFunc =>
      match
        Bool.and
          (Nat.beq sz 8)
          (Bool.and
            (Nat.beq ptrVal.offsetBytes 0)
            (match lookupBorrow s.memory.borrows ptrVal.tag with
             | .some _ => false
             | .none => true))
      with
      | false => .ub
      | true =>
        match lookupFnPtr s.memory.fnPtrs ptrVal.allocId with
        | .none => .ub
        | .some fnEntry =>
          let callerFuncTyOpt := operandTy bodyLocalDecls bodyLayouts func
          match fnEntryCompatibleWithCallSite fnEntry argCount callerFuncTyOpt with
          | true =>
            .ok
              { defPath := fnEntry.defPath
                typeArgs := fnEntry.typeArgs
                fnSig := fnEntry.fnSig
                isIndirect := true }
              localsAfterFunc
          | false => .ub
    | .ok .unit localsAfterFunc =>
      match extractFnItemTarget? (operandTy bodyLocalDecls bodyLayouts func) with
      | .some (defPath, typeArgs) =>
        .ok
          { defPath := defPath
            typeArgs := typeArgs
            fnSig := .none
            isIndirect := false }
          localsAfterFunc
      | .none => .ub
    | .ok (.aggregate 0 .nil) localsAfterFunc =>
      match extractFnItemTarget? (operandTy bodyLocalDecls bodyLayouts func) with
      | .some (defPath, typeArgs) =>
        .ok
          { defPath := defPath
            typeArgs := typeArgs
            fnSig := .none
            isIndirect := false }
          localsAfterFunc
      | .none => .ub
    | .ok _ _ => .ub

/--
Alias for `resolveCallTarget` preserving compatibility with `BRIEF-2.2`'s
`resolveCallee?` interface.
-/
@[simp]
def resolveCallee? := resolveCallTarget

/--
Validate that a linked `calleeBody : CapturedMir` in `s.memory.callees` is
compatible with `target` and `argCount` on an indirect function-pointer call.

For direct calls (`target.isIndirect == false`), reduces definitionally to
`true`.
For indirect calls (`target.isIndirect == true`), checks that
`calleeBody.fnAbi.conv != .rustIntrinsic`, `calleeBody.argCount == argCount`,
and that `target.fnSig` (when present) matches `calleeBody.argCount`,
`calleeBody.fnAbi.conv`, and `calleeLocalDeclsCompatible` on
`calleeBody.localDecls`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Calling a function with the wrong call ABI or unwinding from a function
>   with the wrong unwind ABI."
-/
def checkCalleeTargetCompatible
    (target : ResolvedCallTarget)
    (calleeBody : CapturedMir)
    (argCount : Nat) :
    Bool :=
  match target.isIndirect with
  | false => true
  | true =>
    Bool.and
      (Bool.not (callConvEq calleeBody.fnAbi.conv .rustIntrinsic))
      (Bool.and
        (Nat.beq calleeBody.argCount argCount)
        (match target.fnSig with
         | .none => true
         | .some (.fnPtr sigInputs sigOut _ sigAbi) =>
           Bool.and
             (Nat.beq (length sigInputs) calleeBody.argCount)
             (Bool.and
               (callConvEq sigAbi calleeBody.fnAbi.conv)
               (calleeLocalDeclsCompatible
                 calleeBody.localDecls
                 calleeBody.argCount
                 sigInputs
                 sigOut))
         | .some _ => false))

/--
Direct calls (`isIndirect = false`) are unconditionally compatible with their
resolved `calleeBody`.
-/
@[simp]
theorem checkCalleeTargetCompatible_direct
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (fnSig : Option RigidTy)
    (calleeBody : CapturedMir)
    (argCount : Nat) :
    checkCalleeTargetCompatible
      { defPath := defPath, typeArgs := typeArgs, fnSig := fnSig, isIndirect := false }
      calleeBody
      argCount = true :=
  rfl

/--
Restore the caller frame's active function-entry lifetime protectors upon
popping `caller` from `Memory.callStack`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L276-L287>

> "pub enum RetagKind {
>     /// The initial retag of arguments when entering a function.
>     FnEntry,"
-/
@[simp]
def restoreCallerProtectors (caller : SavedCallerFrame) : List Nat :=
  match caller.callerProtector with
  | .some protId => protId :: caller.calleeProtectors
  | .none => caller.calleeProtectors

/--
Push a `SavedCallerFrame` onto `s.memory.callStack` and enter `calleeBody` at
basic block `0` with `initLocals calleeBody argVals`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L841-L853>

> "Call {
>     func: Operand<'tcx>,
>     args: Box<[Spanned<Operand<'tcx>>]>,
>     destination: Place<'tcx>,
>     target: Option<BasicBlock>,
>     unwind: UnwindAction,
>     call_source: CallSource,
>     fn_span: Span,
> },"
-/
@[simp]
def pushCalleeFrame
    (s : MachineState)
    (callerBody : CapturedMir)
    (localsAfterArgs : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (calleeBody : CapturedMir)
    (argVals : List Value)
    (unwind : UnwindAction := .continue_) :
    MachineState :=
  let savedCaller : SavedCallerFrame := {
    callerBody := callerBody
    frame := { s.frame with locals := localsAfterArgs }
    destination := destination
    returnTarget := targetBb
    calleeProtectors := s.memory.activeProtectors
    returnUnwind := unwind
    isDiverging := false
  }
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals := initLocals calleeBody argVals
    }
    memory := {
      s.memory with
      callStack := savedCaller :: s.memory.callStack
      activeCallee := .some calleeBody
    }
  }

/--
Push a diverging `SavedCallerFrame` (`isDiverging := true`, `returnUnwind := unwind`)
onto `s.memory.callStack` and enter `calleeBody` at basic block `0` with
`initLocals calleeBody argVals` for a diverging `TerminatorKind.call`
(`target = .none`).

If `calleeBody` later executes `TerminatorKind.return_`, execution faults with
`MirStepNode.fail .ub`; if `calleeBody` unwinds, execution pops `savedCaller`
and dispatches `unwind : UnwindAction` in `callerBody`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L841-L853>

> "Call {
>     func: Operand<'tcx>,
>     args: Box<[Spanned<Operand<'tcx>>]>,
>     destination: Place<'tcx>,
>     target: Option<BasicBlock>,
>     unwind: UnwindAction,
>     call_source: CallSource,
>     fn_span: Span,
> },"
-/
@[simp]
def pushDivergingCalleeFrame
    (s : MachineState)
    (callerBody : CapturedMir)
    (localsAfterArgs : List LocalSlot)
    (destination : Place)
    (unwind : UnwindAction)
    (calleeBody : CapturedMir)
    (argVals : List Value) :
    MachineState :=
  let savedCaller : SavedCallerFrame := {
    callerBody := callerBody
    frame := { s.frame with locals := localsAfterArgs }
    destination := destination
    returnTarget := 0
    calleeProtectors := s.memory.activeProtectors
    returnUnwind := unwind
    isDiverging := true
  }
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals := initLocals calleeBody argVals
    }
    memory := {
      s.memory with
      callStack := savedCaller :: s.memory.callStack
      activeCallee := .some calleeBody
    }
  }

/--
Enter `calleeBody` at basic block `0` for a `TerminatorKind.tailCall` without
pushing a caller frame onto `mem.callStack`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L855-L865>

> "TailCall {
>     func: Operand<'tcx>,
>     args: Box<[Spanned<Operand<'tcx>>]>,
>     fn_span: Span,
> },"
-/
@[simp]
def enterTailCalleeFrame
    (mem : Memory)
    (calleeBody : CapturedMir)
    (argVals : List Value) :
    MachineState :=
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals := initLocals calleeBody argVals
    }
    memory := {
      mem with
      activeCallee := .some calleeBody
    }
  }

/--
Unwind out of the active frame by popping caller frames from `callStack` until a
caller frame catches the unwind (`.cleanup cleanupBb`), aborts (`.terminate`),
faults on an impossible unwind ABI (`.unreachable`), or reaches the root frame
(`callStack = .nil`, halting with `.halted .panic`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L714-L722>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L964-L980>

> "/// Indicates that the landing pad is finished and that the process should
> /// continue unwinding.
> UnwindResume,"
>
> "pub enum UnwindAction {
>     Continue,
>     Unreachable,
>     Terminate(UnwindTerminateReason),
>     Cleanup(BasicBlock),
> }"
-/
@[simp]
def unwindFromCallStack : List SavedCallerFrame → Memory → MirExecState
  | .nil, _ => .halted .panic
  | caller :: restStack, memAfter =>
    let memCaller : Memory := {
      memAfter with
      callStack := restStack
      activeCallee := .some caller.callerBody
      activeProtectors := restoreCallerProtectors caller
    }
    match caller.returnUnwind with
    | .unreachable => .faulted .ub
    | .terminate => .halted .abort
    | .continue_ => unwindFromCallStack restStack memCaller
    | .cleanup cleanupBb =>
      .running {
        frame := {
          caller.frame with
          blockIdx := cleanupBb
          stmtIdx := 0
        }
        memory := memCaller
      }

/--
Resolve an unwinding outcome according to the call or assertion `UnwindAction`.

When `unwind` is `.continue_`, propagates the unwind up `memAfter.callStack` via
`unwindFromCallStack` (popping caller frames and restoring lifetime protectors,
or halting with `.halted .panic` at the root frame).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L964-L980>

> "pub enum UnwindAction {
>     Continue,
>     Unreachable,
>     Terminate(UnwindTerminateReason),
>     Cleanup(BasicBlock),
> }"
-/
def applyUnwindAction
    (s : MachineState)
    (localsAfterArgs : List LocalSlot)
    (memAfter : Memory)
    (unwind : UnwindAction) :
    MirExecState :=
  match unwind with
  | .unreachable => .faulted .ub
  | .terminate => .halted .abort
  | .continue_ => unwindFromCallStack memAfter.callStack memAfter
  | .cleanup cleanupBb =>
    .running {
      frame := {
        s.frame with
        blockIdx := cleanupBb
        stmtIdx := 0
        locals := localsAfterArgs
      }
      memory := memAfter
    }

/--
Resume after an external `TerminatorKind.call` response `ans : MirCallAns`,
writing `retVal` to `destination` and updating `Memory` on normal return, or
dispatching `unwind` / `.abort` on abnormal return.
-/
def resumeExternalCall
    (s : MachineState)
    (localsAfterArgs : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (ans : MirCallAns) :
    MirExecState :=
  match ans with
  | .returned retVal memAfter =>
    match
      writePlaceValue
        localsAfterArgs
        memAfter.borrows
        destination
        retVal
    with
    | .ok updatedLocals =>
      .running {
        frame := {
          s.frame with
          blockIdx := targetBb
          stmtIdx := 0
          locals := updatedLocals
        }
        memory := memAfter
      }
    | .ub => .faulted .ub
    | .unsupported => .faulted .unsupported
  | .panicked memAfter =>
    applyUnwindAction s localsAfterArgs memAfter unwind
  | .aborted => .halted .abort

/--
Resume after an external diverging `TerminatorKind.call` (`target = .none`)
response `ans : MirCallAns`.

Because a diverging call has no return target (`!` return type), a normal return
(`MirCallAns.returned`) is immediate undefined behavior (`.faulted .ub`), an
unwind (`MirCallAns.panicked memAfter`) dispatches `applyUnwindAction`, and an
abort (`MirCallAns.aborted`) halts with `.halted .abort`.

Reference (The Rust Reference, "Never type"):
<https://doc.rust-lang.org/1.98.0/reference/types/never.html>

> "The never type `!` is a type with no values, representing the result of
> computations that never complete."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Producing an invalid value ... A value of the `!` type is invalid."
-/
def resumeExternalDivergingCall
    (s : MachineState)
    (localsAfterArgs : List LocalSlot)
    (unwind : UnwindAction)
    (ans : MirCallAns) :
    MirExecState :=
  match ans with
  | .returned _ _ => .faulted .ub
  | .panicked memAfter =>
    applyUnwindAction s localsAfterArgs memAfter unwind
  | .aborted => .halted .abort

/--
Resume after an external `TerminatorKind.tailCall` response `ans : MirCallAns`.
-/
def resumeExternalTailCall (ans : MirCallAns) : MirExecState :=
  match ans with
  | .returned retVal memAfter =>
    match memAfter.callStack with
    | .nil => .halted (.normal (retVal, memAfter))
    | caller :: restStack =>
      match caller.isDiverging with
      | true => .faulted .ub
      | false =>
        match
          writePlaceValue
            caller.frame.locals
            memAfter.borrows
            caller.destination
            retVal
        with
        | .ok updatedCallerLocals =>
          let restoredProtectors := restoreCallerProtectors caller
          .running {
            frame := {
              caller.frame with
              blockIdx := caller.returnTarget
              stmtIdx := 0
              locals := updatedCallerLocals
            }
            memory := {
              memAfter with
              callStack := restStack
              activeCallee := .some caller.callerBody
              activeProtectors := restoredProtectors
            }
          }
        | .ub => .faulted .ub
        | .unsupported => .faulted .unsupported
  | .panicked memAfter =>
    unwindFromCallStack memAfter.callStack memAfter
  | .aborted => .halted .abort

/--
Extract `localDecls` from an optional active `CapturedMir` body, defaulting to
`.nil` when `currentBody = .none`.
-/
@[simp]
def bodyLocalDeclsOf : Option CapturedMir → List LocalDecl
  | .some b => b.localDecls
  | .none => .nil

/--
Test whether a resolved call `target` is a direct call to the inline-modeled
compiler intrinsic `core::intrinsics::exact_div`.
-/
@[simp]
def isDirectExactDivTarget (target : ResolvedCallTarget) : Bool :=
  match target.isIndirect with
  | true => false
  | false => stringEq target.defPath "core::intrinsics::exact_div"

/--
Enumeration of `CallConv.rustIntrinsic` compiler intrinsics executed inline
inside `core` (`BRIEF-1.3`).

Reference (`compiler/rustc_middle/src/ty/intrinsic.rs` and
`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>

> "Compiler intrinsics."
-/
inductive RustIntrinsicKind : Type where
  /-- `core::intrinsics::ub_checks` runtime UB-check enablement query. -/
  | ubChecks : RustIntrinsicKind
  /-- `core::intrinsics::const_eval_select` runtime function dispatch. -/
  | constEvalSelect : RustIntrinsicKind
  /-- `core::intrinsics::arith_offset` wrapping signed pointer offset. -/
  | arithOffset : RustIntrinsicKind
  /-- `core::intrinsics::ctlz` leading-zero bit count. -/
  | ctlz : RustIntrinsicKind
  /-- `core::intrinsics::ctlz_nonzero` non-zero leading-zero bit count. -/
  | ctlzNonzero : RustIntrinsicKind
  /-- `core::intrinsics::cttz` trailing-zero bit count. -/
  | cttz : RustIntrinsicKind
  /-- `core::intrinsics::cttz_nonzero` non-zero trailing-zero bit count. -/
  | cttzNonzero : RustIntrinsicKind
  /-- `core::intrinsics::ctpop` population count. -/
  | ctpop : RustIntrinsicKind
  /-- `core::intrinsics::bswap` byte-order reversal. -/
  | bswap : RustIntrinsicKind
  /-- `core::intrinsics::bitreverse` bit-order reversal. -/
  | bitreverse : RustIntrinsicKind
  /-- `core::intrinsics::wrapping_add` modular addition. -/
  | wrappingAdd : RustIntrinsicKind
  /-- `core::intrinsics::wrapping_sub` modular subtraction. -/
  | wrappingSub : RustIntrinsicKind
  /-- `core::intrinsics::wrapping_mul` modular multiplication. -/
  | wrappingMul : RustIntrinsicKind
  /-- `core::intrinsics::saturating_add` saturating addition. -/
  | saturatingAdd : RustIntrinsicKind
  /-- `core::intrinsics::saturating_sub` saturating subtraction. -/
  | saturatingSub : RustIntrinsicKind
  /-- `core::intrinsics::unchecked_shl` unchecked left shift. -/
  | uncheckedShl : RustIntrinsicKind
  /-- `core::intrinsics::unchecked_shr` unchecked right shift. -/
  | uncheckedShr : RustIntrinsicKind
  /-- `core::intrinsics::unchecked_add` unchecked addition. -/
  | uncheckedAdd : RustIntrinsicKind
  /-- `core::intrinsics::unchecked_sub` unchecked subtraction. -/
  | uncheckedSub : RustIntrinsicKind
  /-- `core::intrinsics::unchecked_mul` unchecked multiplication. -/
  | uncheckedMul : RustIntrinsicKind
  /-- `core::intrinsics::unchecked_div` unchecked division. -/
  | uncheckedDiv : RustIntrinsicKind
  /-- `core::intrinsics::unchecked_rem` unchecked remainder. -/
  | uncheckedRem : RustIntrinsicKind
  /-- `core::intrinsics::three_way_compare` three-way scalar comparison. -/
  | threeWayCompare : RustIntrinsicKind
  /-- `core::intrinsics::size_of_val` dynamic or static pointee byte size. -/
  | sizeOfVal : RustIntrinsicKind
  /-- `core::intrinsics::min_align_of_val` dynamic or static pointee alignment. -/
  | minAlignOfVal : RustIntrinsicKind

/--
Classify a canonical `DefPath` into a `RustIntrinsicKind` when it names one of
the `core::intrinsics::*` compiler intrinsics modeled inline in `evalTerminator`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>

> "Compiler intrinsics."
-/
@[reducible]
def classifyRustIntrinsic? (defPath : DefPath) : Option RustIntrinsicKind :=
  match stringEq defPath "core::intrinsics::ub_checks" with
  | true => .some .ubChecks
  | false =>
    match stringEq defPath "core::intrinsics::const_eval_select" with
    | true => .some .constEvalSelect
    | false =>
      match stringEq defPath "core::intrinsics::arith_offset" with
      | true => .some .arithOffset
      | false =>
        match stringEq defPath "core::intrinsics::ctlz" with
        | true => .some .ctlz
        | false =>
          match stringEq defPath "core::intrinsics::ctlz_nonzero" with
          | true => .some .ctlzNonzero
          | false =>
            match stringEq defPath "core::intrinsics::cttz" with
            | true => .some .cttz
            | false =>
              match stringEq defPath "core::intrinsics::cttz_nonzero" with
              | true => .some .cttzNonzero
              | false =>
                match stringEq defPath "core::intrinsics::ctpop" with
                | true => .some .ctpop
                | false =>
                  match stringEq defPath "core::intrinsics::bswap" with
                  | true => .some .bswap
                  | false =>
                    match stringEq defPath "core::intrinsics::bitreverse" with
                    | true => .some .bitreverse
                    | false =>
                      match stringEq defPath "core::intrinsics::wrapping_add" with
                      | true => .some .wrappingAdd
                      | false =>
                        match stringEq defPath "core::intrinsics::wrapping_sub" with
                        | true => .some .wrappingSub
                        | false =>
                          match stringEq defPath "core::intrinsics::wrapping_mul" with
                          | true => .some .wrappingMul
                          | false =>
                            match stringEq defPath "core::intrinsics::saturating_add" with
                            | true => .some .saturatingAdd
                            | false =>
                              match stringEq defPath "core::intrinsics::saturating_sub" with
                              | true => .some .saturatingSub
                              | false =>
                                match stringEq defPath "core::intrinsics::unchecked_shl" with
                                | true => .some .uncheckedShl
                                | false =>
                                  match stringEq defPath "core::intrinsics::unchecked_shr" with
                                  | true => .some .uncheckedShr
                                  | false =>
                                    match stringEq defPath "core::intrinsics::unchecked_add" with
                                    | true => .some .uncheckedAdd
                                    | false =>
                                      match stringEq defPath "core::intrinsics::unchecked_sub" with
                                      | true => .some .uncheckedSub
                                      | false =>
                                        match stringEq defPath "core::intrinsics::unchecked_mul" with
                                        | true => .some .uncheckedMul
                                        | false =>
                                          match stringEq defPath "core::intrinsics::unchecked_div" with
                                          | true => .some .uncheckedDiv
                                          | false =>
                                            match stringEq defPath "core::intrinsics::unchecked_rem" with
                                            | true => .some .uncheckedRem
                                            | false =>
                                              match stringEq defPath "core::intrinsics::three_way_compare" with
                                              | true => .some .threeWayCompare
                                              | false =>
                                                match stringEq defPath "core::intrinsics::size_of_val" with
                                                | true => .some .sizeOfVal
                                                | false =>
                                                  match
                                                    Bool.or
                                                      (stringEq defPath "core::intrinsics::min_align_of_val")
                                                      (stringEq defPath "core::intrinsics::align_of_val")
                                                  with
                                                  | true => .some .minAlignOfVal
                                                  | false => .none

/--
Return `.some true` for signed integer `RigidTy.int _`, `.some false` for
unsigned integer `RigidTy.uint _`, and `.none` otherwise.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The signed two's complement integer types consist of: ... i8, i16, i32, i64,
> i128, isize"
-/
@[reducible]
def rigidTyIsSigned : RigidTy → Option Bool
  | .int _ => .some true
  | .uint _ => .some false
  | _ => .none

/--
Resolve whether the primary scalar operand of a `CallConv.rustIntrinsic` call is
signed, consulting the first monomorphized type argument in `target.typeArgs`
when present and falling back to `operandIsSigned` on the first argument operand.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The signed two's complement integer types consist of: ... i8, i16, i32, i64,
> i128, isize"
-/
@[reducible]
def resolveIntrinsicIsSigned
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand) :
    Bool :=
  match target.typeArgs with
  | firstTy :: _ =>
    match rigidTyIsSigned firstTy with
    | .some b => b
    | .none =>
      match argOps with
      | lhsOp :: _ => operandIsSigned bodyLocalDecls lhsOp bodyLayouts
      | .nil => false
  | .nil =>
    match argOps with
    | lhsOp :: _ => operandIsSigned bodyLocalDecls lhsOp bodyLayouts
    | .nil => false

/--
Resolve whether the shift-count operand (`rhs`, type parameter `U`) of
`unchecked_shl<T, U>` or `unchecked_shr<T, U>` is a signed integer type,
consulting `operandTy` on the second operand first and falling back to the
second (or sole) type argument in `target.typeArgs`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1955-L1972>

> "pub const unsafe fn unchecked_shl<T: Copy, U: Copy>(x: T, y: U) -> T;"
-/
@[reducible]
def resolveIntrinsicShiftSigned
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand) :
    Bool :=
  match argOps with
  | _ :: rhsOp :: _ =>
    match operandTy bodyLocalDecls bodyLayouts rhsOp with
    | .some ty =>
      match rigidTyIsSigned ty.kind with
      | .some b => b
      | .none =>
        match target.typeArgs with
        | _ :: secondTy :: _ =>
          match rigidTyIsSigned secondTy with
          | .some b => b
          | .none => false
        | firstTy :: .nil =>
          match rigidTyIsSigned firstTy with
          | .some b => b
          | .none => false
        | .nil => false
    | .none =>
      match target.typeArgs with
      | _ :: secondTy :: _ =>
        match rigidTyIsSigned secondTy with
        | .some b => b
        | .none => false
      | firstTy :: .nil =>
        match rigidTyIsSigned firstTy with
        | .some b => b
        | .none => false
      | .nil => false
  | _ =>
    match target.typeArgs with
    | _ :: secondTy :: _ =>
      match rigidTyIsSigned secondTy with
      | .some b => b
      | .none => false
    | firstTy :: .nil =>
      match rigidTyIsSigned firstTy with
      | .some b => b
      | .none => false
    | .nil => false

/--
Look up a `TypeLayout` for `ty : RigidTy` by scanning `localDecls` for a
declaration with `rigidTyEq decl.ty.kind ty`, falling back to index `0` of
`layouts` for `.adt` and `.closure` types when `localDecls` has no direct
declaration of type `ty`.

Reference (`compiler/rustc_middle/src/ty/layout.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/layout.rs#L706-L712>

> "fn layout_of(&self, ty: Ty<'tcx>) -> Self::LayoutOfResult"
-/
@[reducible]
def findDeclLayoutForRigidTy
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : RigidTy) :
    Option TypeLayout :=
  match localDecls with
  | .nil =>
    match ty with
    | .adt _ _ => LayoutTable.lookup layouts 0
    | .closure _ _ => LayoutTable.lookup layouts 0
    | _ => .none
  | decl :: rest =>
    match rigidTyEq decl.ty.kind ty with
    | true =>
      match LayoutTable.lookup layouts decl.ty.layoutIdx with
      | .some l => .some l
      | .none => findDeclLayoutForRigidTy rest layouts ty
    | false => findDeclLayoutForRigidTy rest layouts ty

/--
Determine the static byte size of a sized `RigidTy` on a 64-bit target for
`arith_offset` and `size_of_val`, returning `.none` for unsized types (`.slice`,
`.str`, `.dynamic`, `.foreign`) or unresolvable ADTs.

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."
-/
@[reducible]
def intrinsicRigidTyByteSize
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : RigidTy) :
    Option Nat :=
  match rigidTyKindByteSize ty with
  | .some sz => .some sz
  | .none =>
    match ty with
    | .never => .some 0
    | .float .f16 => .some 2
    | .float .f32 => .some 4
    | .float .f64 => .some 8
    | .float .f128 => .some 16
    | .array elemKind n =>
      match findDeclLayoutForRigidTy localDecls layouts elemKind with
      | .some l => .some (Nat.mul l.size.bytes n)
      | .none =>
        match findDeclLayoutForRigidTy localDecls layouts ty with
        | .some l => .some l.size.bytes
        | .none => .none
    | .tuple ks =>
      match findDeclLayoutForRigidTy localDecls layouts ty with
      | .some l => .some l.size.bytes
      | .none => tupleFieldsByteSize ks
    | _ =>
      match findDeclLayoutForRigidTy localDecls layouts ty with
      | .some l => .some l.size.bytes
      | .none => .none

/--
Compute the ABI byte alignment of a `RigidTy` when determined directly by its
primitive or pointer constructor on a 64-bit target.

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The alignment of a value specifies what addresses are valid to store the
> value at. A value of alignment `n` must only be stored at an address that is a
> multiple of `n`."
-/
@[reducible]
def intrinsicRigidTyKindAlign : RigidTy → Option Nat
  | .bool => .some 1
  | .char => .some 4
  | .never => .some 1
  | .uint w => intCastTargetBytes (.uint w)
  | .int w => intCastTargetBytes (.int w)
  | .float .f16 => .some 2
  | .float .f32 => .some 4
  | .float .f64 => .some 8
  | .float .f128 => .some 16
  | .tuple .nil => .some 1
  | .fnDef _ _ => .some 1
  | .fnPtr _ _ _ _ => .some 8
  | .ref _ _ => .some 8
  | .rawPtr _ _ => .some 8
  | .array elemKind _ =>
    match elemKind with
    | .bool => .some 1
    | .char => .some 4
    | .never => .some 1
    | .uint w => intCastTargetBytes (.uint w)
    | .int w => intCastTargetBytes (.int w)
    | .float .f16 => .some 2
    | .float .f32 => .some 4
    | .float .f64 => .some 8
    | .float .f128 => .some 16
    | .tuple .nil => .some 1
    | .fnDef _ _ => .some 1
    | .fnPtr _ _ _ _ => .some 8
    | .ref _ _ => .some 8
    | .rawPtr _ _ => .some 8
    | _ => .none
  | _ => .none

/--
Compute the maximum ABI alignment across a list of `RigidTy` tuple elements when
each element has a known primitive alignment.

Reference (The Rust Reference, "Tuple types"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#tuple-layout>

> "Tuples do not have any guarantees about their layout, other than that the
> alignment of the tuple is at least the maximum alignment of its fields."
-/
@[reducible]
def tupleFieldsAlign : List RigidTy → Option Nat
  | .nil => .some 1
  | k :: rest =>
    match intrinsicRigidTyKindAlign k, tupleFieldsAlign rest with
    | .some a, .some restA =>
      match Nat.ble a restA with
      | true => .some restA
      | false => .some a
    | _, _ => .none

/--
Determine the ABI byte alignment of a sized `RigidTy` on a 64-bit target for
`min_align_of_val`, validating that any `LayoutTable` entry alignment is a
positive power of two.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2282-L2293>

> "pub const unsafe fn min_align_of_val<T: ?Sized>(val: *const T) -> usize;"
-/
@[reducible]
def intrinsicRigidTyAlign
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : RigidTy) :
    Option Nat :=
  match intrinsicRigidTyKindAlign ty with
  | .some a => .some a
  | .none =>
    match ty with
    | .array elemKind _ =>
      match findDeclLayoutForRigidTy localDecls layouts elemKind with
      | .some l =>
        match Align.isPowerOfTwoBytes l.align with
        | true => .some l.align.bytes
        | false => .none
      | .none =>
        match findDeclLayoutForRigidTy localDecls layouts ty with
        | .some l =>
          match Align.isPowerOfTwoBytes l.align with
          | true => .some l.align.bytes
          | false => .none
        | .none => .none
    | .tuple ks =>
      match findDeclLayoutForRigidTy localDecls layouts ty with
      | .some l =>
        match Align.isPowerOfTwoBytes l.align with
        | true => .some l.align.bytes
        | false => .none
      | .none => tupleFieldsAlign ks
    | _ =>
      match findDeclLayoutForRigidTy localDecls layouts ty with
      | .some l =>
        match Align.isPowerOfTwoBytes l.align with
        | true => .some l.align.bytes
        | false => .none
      | .none => .none

/--
Resolve the pointee `RigidTy` `T` for pointer-parameterized intrinsics
(`arith_offset<T>`, `size_of_val<T>`, `min_align_of_val<T>`), consulting
`target.typeArgs` first and falling back to the pointee type of the first pointer
operand in `argOps`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2268-L2293>

> "pub const unsafe fn size_of_val<T: ?Sized>(val: *const T) -> usize;"
-/
@[reducible]
def resolveIntrinsicPointeeTy?
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand) :
    Option RigidTy :=
  match target.typeArgs with
  | pointeeTy :: _ => .some pointeeTy
  | .nil =>
    match argOps with
    | ptrOp :: _ =>
      match operandTy bodyLocalDecls bodyLayouts ptrOp with
      | .some { kind := .rawPtr _ pointeeTy, .. } => .some pointeeTy
      | .some { kind := .ref _ pointeeTy, .. } => .some pointeeTy
      | _ => .none
    | .nil => .none

/--
Unpack the tuple argument `arg : ARG` of `core::intrinsics::const_eval_select`
into a list of individual call argument `Value`s.

Accepts `Value.aggregate 0 fieldVals` (n-ary tuple) and `Value.unit` (0-tuple
`()`), returning `.none` (which faults with `.ub`) for any non-tuple value.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2665-L2680>

> "pub const unsafe fn const_eval_select<ARG: Tuple, F, G, RET>(
>     arg: ARG,
>     called_in_const: F,
>     called_at_rt: G,
> ) -> RET;"
-/
@[reducible]
def unpackConstEvalSelectArgs? : Value → Option (List Value)
  | .aggregate 0 fieldVals => .some fieldVals
  | .unit => .some .nil
  | _ => .none

/--
Resolve the runtime target function `called_at_rt : G` (the 3rd argument) of
`core::intrinsics::const_eval_select(arg, called_in_const, called_at_rt)`:
- Direct constant function item on `rtFnOp` (`extractCalleeDefPath? rtFnOp`),
- Zero-sized function item (`Value.unit` or `Value.aggregate 0 .nil`) whose
  `DefPath` is carried by `operandTy bodyLocalDecls bodyLayouts rtFnOp` or by
  the 3rd type argument `G` in `target.typeArgs`, or
- Reified 8-byte function pointer (`Value.ptr ptrVal 8` at offset `0`, not
  aliasing any stack borrow in `s.memory.borrows`, and compatible with
  `unpackedArgCount`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2665-L2680>

> "pub const unsafe fn const_eval_select<ARG: Tuple, F, G, RET>(
>     arg: ARG,
>     called_in_const: F,
>     called_at_rt: G,
> ) -> RET;"
-/
@[reducible]
def resolveConstEvalSelectTarget?
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (rtFnOpOpt : Option Operand)
    (rtFnVal : Value)
    (unpackedArgCount : Nat) :
    Option ResolvedCallTarget :=
  let directFromOp : Option ResolvedCallTarget :=
    match rtFnOpOpt with
    | .some rtFnOp =>
      match extractCalleeDefPath? rtFnOp with
      | .some defPath =>
        .some
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs rtFnOp
            fnSig := .none
            isIndirect := false }
      | .none => .none
    | .none => .none
  match directFromOp with
  | .some resolved => .some resolved
  | .none =>
    let fallbackFnItemTarget? : Option (DefPath × List RigidTy) :=
      match rtFnOpOpt with
      | .some rtFnOp =>
        match extractFnItemTarget? (operandTy bodyLocalDecls bodyLayouts rtFnOp) with
        | .some pair => .some pair
        | .none =>
          match get? target.typeArgs 2 with
          | .some (.fnDef defPath typeArgs) => .some (defPath, typeArgs)
          | .some (.closure defPath typeArgs) => .some (defPath, typeArgs)
          | _ => .none
      | .none =>
        match get? target.typeArgs 2 with
        | .some (.fnDef defPath typeArgs) => .some (defPath, typeArgs)
        | .some (.closure defPath typeArgs) => .some (defPath, typeArgs)
        | _ => .none
    match rtFnVal with
    | .unit =>
      match fallbackFnItemTarget? with
      | .some (defPath, typeArgs) =>
        .some
          { defPath := defPath
            typeArgs := typeArgs
            fnSig := .none
            isIndirect := false }
      | .none => .none
    | .aggregate 0 .nil =>
      match fallbackFnItemTarget? with
      | .some (defPath, typeArgs) =>
        .some
          { defPath := defPath
            typeArgs := typeArgs
            fnSig := .none
            isIndirect := false }
      | .none => .none
    | .ptr ptrVal sz =>
      match
        Bool.and
          (Nat.beq sz 8)
          (Bool.and
            (Nat.beq ptrVal.offsetBytes 0)
            (match lookupBorrow s.memory.borrows ptrVal.tag with
             | .some _ => false
             | .none => true))
      with
      | false => .none
      | true =>
        match lookupFnPtr s.memory.fnPtrs ptrVal.allocId with
        | .none => .none
        | .some fnEntry =>
          let callerFuncTyOpt :=
            match rtFnOpOpt with
            | .some rtFnOp => operandTy bodyLocalDecls bodyLayouts rtFnOp
            | .none => .none
          match fnEntryCompatibleWithCallSite fnEntry unpackedArgCount callerFuncTyOpt with
          | true =>
            .some
              { defPath := fnEntry.defPath
                typeArgs := fnEntry.typeArgs
                fnSig := fnEntry.fnSig
                isIndirect := true }
          | false => .none
    | _ => .none

/--
Write an inline compiler intrinsic's return value `retVal` to `destination` and
advance to `targetBb` at `stmtIdx := 0`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L841-L853>

> "Call {
>     func: Operand<'tcx>,
>     args: Box<[Spanned<Operand<'tcx>>]>,
>     destination: Place<'tcx>,
>     target: Option<BasicBlock>,"
-/
@[reducible]
def writeIntrinsicReturn
    (s : MachineState)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (retVal : Value) :
    MirStepNode :=
  match writePlaceValue locals' s.memory.borrows destination retVal with
  | .ok updatedLocals =>
    MirStepNode.step {
      frame := {
        s.frame with
        blockIdx := targetBb
        stmtIdx := 0
        locals := updatedLocals
      }
      memory := s.memory
    }
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported

/--
Write an optional scalar intrinsic result `resOpt` to `destination` and advance
to `targetBb`, or fault with `MirStepNode.fail .ub` when `resOpt = .none`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list."
-/
@[reducible]
def writeIntrinsicScalarResult
    (s : MachineState)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (resOpt : Option ScalarInt) :
    MirStepNode :=
  match resOpt with
  | .some sc => writeIntrinsicReturn s locals' destination targetBb (.scalar sc)
  | .none => MirStepNode.fail .ub

/--
Evaluate a value-returning `RustIntrinsicKind` (all variants except
`.constEvalSelect`) from evaluated argument values `argVals`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>

> "Compiler intrinsics."
-/
@[reducible]
def evalNonSelectIntrinsicCall
    (kind : RustIntrinsicKind)
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    MirStepNode :=
  match kind with
  | .ubChecks =>
    match argVals with
    | .nil => writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 1⟩)
    | _ => MirStepNode.fail .ub
  | .arithOffset =>
    match argVals with
    | .ptr ptrVal ptrSz :: .scalar countSc :: .nil =>
      match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
      | .some pointeeTy =>
        match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
        | .some elemSz =>
          match evalArithOffset ptrVal ptrSz countSc elemSz with
          | .some retPtrVal =>
            writeIntrinsicReturn s locals' destination targetBb (.ptr retPtrVal 8)
          | .none => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | _ => MirStepNode.fail .ub
  | .ctlz =>
    match argVals with
    | .scalar sc :: .nil =>
      writeIntrinsicScalarResult s locals' destination targetBb (evalCtlz sc)
    | _ => MirStepNode.fail .ub
  | .ctlzNonzero =>
    match argVals with
    | .scalar sc :: .nil =>
      writeIntrinsicScalarResult s locals' destination targetBb (evalCtlzNonzero sc)
    | _ => MirStepNode.fail .ub
  | .cttz =>
    match argVals with
    | .scalar sc :: .nil =>
      writeIntrinsicScalarResult s locals' destination targetBb (evalCttz sc)
    | _ => MirStepNode.fail .ub
  | .cttzNonzero =>
    match argVals with
    | .scalar sc :: .nil =>
      writeIntrinsicScalarResult s locals' destination targetBb (evalCttzNonzero sc)
    | _ => MirStepNode.fail .ub
  | .ctpop =>
    match argVals with
    | .scalar sc :: .nil =>
      writeIntrinsicScalarResult s locals' destination targetBb (evalCtpop sc)
    | _ => MirStepNode.fail .ub
  | .bswap =>
    match argVals with
    | .scalar sc :: .nil =>
      writeIntrinsicScalarResult s locals' destination targetBb (evalBswap sc)
    | _ => MirStepNode.fail .ub
  | .bitreverse =>
    match argVals with
    | .scalar sc :: .nil =>
      writeIntrinsicScalarResult s locals' destination targetBb (evalBitreverse sc)
    | _ => MirStepNode.fail .ub
  | .wrappingAdd =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      writeIntrinsicScalarResult s locals' destination targetBb (evalWrappingAdd lhs rhs)
    | _ => MirStepNode.fail .ub
  | .wrappingSub =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      writeIntrinsicScalarResult s locals' destination targetBb (evalWrappingSub lhs rhs)
    | _ => MirStepNode.fail .ub
  | .wrappingMul =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      writeIntrinsicScalarResult s locals' destination targetBb (evalWrappingMul lhs rhs)
    | _ => MirStepNode.fail .ub
  | .saturatingAdd =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      let isSigned := resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps
      writeIntrinsicScalarResult s locals' destination targetBb
        (evalSaturatingAdd lhs rhs isSigned)
    | _ => MirStepNode.fail .ub
  | .saturatingSub =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      let isSigned := resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps
      writeIntrinsicScalarResult s locals' destination targetBb
        (evalSaturatingSub lhs rhs isSigned)
    | _ => MirStepNode.fail .ub
  | .uncheckedShl =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      let rhsSigned :=
        resolveIntrinsicShiftSigned target bodyLocalDecls bodyLayouts argOps
      writeIntrinsicScalarResult s locals' destination targetBb
        (evalUncheckedShl lhs rhs rhsSigned)
    | _ => MirStepNode.fail .ub
  | .uncheckedShr =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      let lhsSigned :=
        resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps
      let rhsSigned :=
        resolveIntrinsicShiftSigned target bodyLocalDecls bodyLayouts argOps
      writeIntrinsicScalarResult s locals' destination targetBb
        (evalUncheckedShr lhs rhs lhsSigned rhsSigned)
    | _ => MirStepNode.fail .ub
  | .uncheckedAdd =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      let isSigned := resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps
      writeIntrinsicScalarResult s locals' destination targetBb
        (evalUncheckedAdd lhs rhs isSigned)
    | _ => MirStepNode.fail .ub
  | .uncheckedSub =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      let isSigned := resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps
      writeIntrinsicScalarResult s locals' destination targetBb
        (evalUncheckedSub lhs rhs isSigned)
    | _ => MirStepNode.fail .ub
  | .uncheckedMul =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      let isSigned := resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps
      writeIntrinsicScalarResult s locals' destination targetBb
        (evalUncheckedMul lhs rhs isSigned)
    | _ => MirStepNode.fail .ub
  | .uncheckedDiv =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      let isSigned := resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps
      writeIntrinsicScalarResult s locals' destination targetBb
        (evalUncheckedDiv lhs rhs isSigned)
    | _ => MirStepNode.fail .ub
  | .uncheckedRem =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      let isSigned := resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps
      writeIntrinsicScalarResult s locals' destination targetBb
        (evalUncheckedRem lhs rhs isSigned)
    | _ => MirStepNode.fail .ub
  | .threeWayCompare =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      let isSigned := resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps
      writeIntrinsicScalarResult s locals' destination targetBb
        (evalThreeWayCompare lhs rhs isSigned)
    | _ => MirStepNode.fail .ub
  | .sizeOfVal =>
    match argVals with
    | ptrArgVal :: .nil =>
      match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
      | .some (.slice elemTy) =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true =>
            match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy with
            | .some elemSz =>
              writeIntrinsicScalarResult s locals' destination targetBb
                (evalSliceSizeOfVal elemSz lenSc)
            | .none => MirStepNode.fail .ub
        | _ => MirStepNode.fail .ub
      | .some .str =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true =>
            writeIntrinsicScalarResult s locals' destination targetBb
              (evalSliceSizeOfVal 1 lenSc)
        | _ => MirStepNode.fail .ub
      | .some pointeeTy =>
        match ptrArgVal with
        | .ptr _ ptrSz =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true =>
            match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
            | .some sz =>
              match Nat.ble 9223372036854775808 sz with
              | true => MirStepNode.fail .ub
              | false =>
                writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨sz, 8⟩)
            | .none => MirStepNode.fail .ub
        | _ => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | _ => MirStepNode.fail .ub
  | .minAlignOfVal =>
    match argVals with
    | ptrArgVal :: .nil =>
      match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
      | .some (.slice elemTy) =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
          match Bool.and (Nat.beq ptrSz 8) (Nat.beq lenSc.sizeBytes 8) with
          | false => MirStepNode.fail .ub
          | true =>
            match intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy with
            | .some alignBytes =>
              writeIntrinsicReturn s locals' destination targetBb
                (.scalar ⟨alignBytes, 8⟩)
            | .none => MirStepNode.fail .ub
        | _ => MirStepNode.fail .ub
      | .some .str =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
          match Bool.and (Nat.beq ptrSz 8) (Nat.beq lenSc.sizeBytes 8) with
          | false => MirStepNode.fail .ub
          | true =>
            writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 8⟩)
        | _ => MirStepNode.fail .ub
      | .some pointeeTy =>
        match ptrArgVal with
        | .ptr _ ptrSz =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true =>
            match intrinsicRigidTyAlign bodyLocalDecls bodyLayouts pointeeTy with
            | .some alignBytes =>
              writeIntrinsicReturn s locals' destination targetBb
                (.scalar ⟨alignBytes, 8⟩)
            | .none => MirStepNode.fail .ub
        | _ => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | _ => MirStepNode.fail .ub
  | .constEvalSelect => MirStepNode.fail .ub

/--
Dispatch a direct (`target.isIndirect = false`) call to a `CallConv.rustIntrinsic`
compiler intrinsic in `evalTerminator` when `classifyRustIntrinsic? target.defPath`
returns `.some kind`.

Returns `.none` when `target.defPath` is not an inline-modeled intrinsic so
`evalTerminator` falls through to `MirStepNode.extCall`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>

> "Compiler intrinsics."
-/
@[reducible]
def evalDirectRustIntrinsic?
    (s : MachineState)
    (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction) :
    Option MirStepNode :=
  match classifyRustIntrinsic? target.defPath with
  | .none => .none
  | .some .constEvalSelect =>
    .some
      (match argVals with
       | tupleArgVal :: _ :: rtFnVal :: .nil =>
         match unpackConstEvalSelectArgs? tupleArgVal with
         | .none => MirStepNode.fail .ub
         | .some unpackedArgs =>
           let rtFnOpOpt :=
             match argOps with
             | _ :: _ :: rtOp :: _ => .some rtOp
             | _ => .none
           match
             resolveConstEvalSelectTarget?
               s
               target
               bodyLocalDecls
               bodyLayouts
               rtFnOpOpt
               rtFnVal
               (length unpackedArgs)
           with
           | .none => MirStepNode.fail .ub
           | .some rtTarget =>
             match findCallee? s.memory.callees rtTarget.defPath with
             | .some calleeBody =>
               match
                 Bool.and
                   (Nat.beq calleeBody.argCount (length unpackedArgs))
                   (Bool.and
                     (Bool.not (callConvEq calleeBody.fnAbi.conv .rustIntrinsic))
                     (checkCalleeTargetCompatible rtTarget calleeBody (length unpackedArgs)))
               with
               | false => MirStepNode.fail .ub
               | true =>
                 match currentBody with
                 | .none => MirStepNode.unsupported
                 | .some callerBody =>
                   MirStepNode.step
                     (pushCalleeFrame
                       s
                       callerBody
                       locals'
                       destination
                       targetBb
                       calleeBody
                       unpackedArgs
                       unwind)
             | .none =>
               match rtTarget.isIndirect with
               | true =>
                 MirStepNode.extCall
                   { defPath := rtTarget.defPath, args := unpackedArgs, memory := s.memory }
                   (resumeExternalCall s locals' destination targetBb unwind)
               | false =>
                 match isDirectExactDivTarget rtTarget with
                 | true =>
                   match unpackedArgs with
                   | .scalar lhs :: .scalar rhs :: .nil =>
                     let isSigned :=
                       resolveIntrinsicIsSigned rtTarget bodyLocalDecls bodyLayouts .nil
                     writeIntrinsicScalarResult
                       s
                       locals'
                       destination
                       targetBb
                       (evalExactDiv lhs rhs isSigned)
                   | _ => MirStepNode.fail .ub
                 | false =>
                   match classifyRustIntrinsic? rtTarget.defPath with
                   | .some .constEvalSelect => MirStepNode.fail .ub
                   | .some rtKind =>
                     evalNonSelectIntrinsicCall
                       rtKind
                       s
                       rtTarget
                       bodyLocalDecls
                       bodyLayouts
                       .nil
                       unpackedArgs
                       locals'
                       destination
                       targetBb
                   | .none =>
                     MirStepNode.extCall
                       { defPath := rtTarget.defPath, args := unpackedArgs, memory := s.memory }
                       (resumeExternalCall s locals' destination targetBb unwind)
       | _ => MirStepNode.fail .ub)
  | .some kind =>
    .some
      (evalNonSelectIntrinsicCall
        kind
        s
        target
        bodyLocalDecls
        bodyLayouts
        argOps
        argVals
        locals'
        destination
        targetBb)

/--
Test whether `defPath` is an unreachable hint or intrinsic
(`"core::hint::unreachable_unchecked"` or `"core::intrinsics::unreachable"`),
reaching which is immediate undefined behavior (`MirStepNode.fail .ub`).

Reference (`library/core/src/hint.rs` and `library/core/src/intrinsics/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/hint.rs#L112-L120>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1867-L1873>

> "/// Informs the compiler that the site which is calling this function is not
> /// reachable, possibly enabling further optimizations.
> ///
> /// # Safety
> ///
> /// Reaching this function is *Undefined Behavior*."
-/
@[simp]
def isUnreachableCallTarget (defPath : DefPath) : Bool :=
  Bool.or
    (stringEq defPath "core::hint::unreachable_unchecked")
    (stringEq defPath "core::intrinsics::unreachable")

/--
Test whether `defPath` is a non-unwinding (aborting) panic or abort entrypoint
in `core` (`"core::panicking::panic_nounwind"`,
`"core::panicking::panic_nounwind_fmt"`,
`"core::panicking::panic_nounwind_fmt::panic_impl"`,
`"core::panicking::panic_nounwind_nobacktrace"`,
`"core::panicking::panic_in_cleanup"`,
`"core::panicking::panic_cannot_unwind"`,
`"core::panicking::panic_misaligned_pointer_dereference"`,
`"core::panicking::panic_null_pointer_dereference"`,
`"core::panicking::panic_invalid_enum_construction"`, or
`"core::intrinsics::abort"`).

Reference (`library/core/src/panicking.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/panicking.rs#L218-L234>

> "/// Like `panic`, but without unwinding and track_caller to reduce the impact
> /// on codesize on the caller.
> #[rustc_nounwind]
> pub const fn panic_nounwind(expr: &'static str) -> !"
-/
@[simp]
def isAbortingPanicDefPath (defPath : DefPath) : Bool :=
  Bool.or
    (stringEq defPath "core::panicking::panic_nounwind")
    (Bool.or
      (stringEq defPath "core::panicking::panic_nounwind_fmt")
      (Bool.or
        (stringEq defPath "core::panicking::panic_nounwind_fmt::panic_impl")
        (Bool.or
          (stringEq defPath "core::panicking::panic_nounwind_nobacktrace")
          (Bool.or
            (stringEq defPath "core::panicking::panic_in_cleanup")
            (Bool.or
              (stringEq defPath "core::panicking::panic_cannot_unwind")
              (Bool.or
                (stringEq defPath "core::panicking::panic_misaligned_pointer_dereference")
                (Bool.or
                  (stringEq defPath "core::panicking::panic_null_pointer_dereference")
                  (Bool.or
                    (stringEq defPath "core::panicking::panic_invalid_enum_construction")
                    (stringEq defPath "core::intrinsics::abort")))))))))

/--
Test whether `defPath` is a standard unwinding panic entrypoint in `core`
(`"core::panicking::panic"`, `"core::panicking::panic_fmt"`,
`"core::panicking::panic_fmt::panic_impl"`,
`"core::panicking::const_panic_fmt"`,
`"core::panicking::assert_failed"`, `"core::panicking::assert_failed_inner"`,
`"core::panicking::assert_matches_failed"`,
`"core::slice::index::slice_index_fail"`,
`"core::panicking::panic_bounds_check"`, `"core::panicking::panic_explicit"`,
`"core::panicking::panic_display"`, `"core::panicking::panic_str_2015"`,
`"core::panicking::unreachable_display"`, `"core::option::unwrap_failed"`,
`"core::option::expect_failed"`, `"core::result::unwrap_failed"`, or
`"core::panicking::panic_const::*"`).

Reference (`library/core/src/panicking.rs` and `library/core/src/slice/index.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/panicking.rs#L139-L154>

> "/// The underlying implementation of core's `panic!` macro when no formatting is used.
> #[cold]
> #[track_caller]
> pub const fn panic(expr: &'static str) -> !"
-/
@[simp]
def isUnwindingPanicDefPath (defPath : DefPath) : Bool :=
  Bool.or
    (stringEq defPath "core::panicking::panic")
    (Bool.or
      (stringEq defPath "core::panicking::panic_fmt")
      (Bool.or
        (stringEq defPath "core::panicking::panic_fmt::panic_impl")
        (Bool.or
          (stringEq defPath "core::panicking::const_panic_fmt")
          (Bool.or
            (stringEq defPath "core::panicking::assert_failed")
            (Bool.or
              (stringEq defPath "core::panicking::assert_failed_inner")
              (Bool.or
                (stringEq defPath "core::panicking::assert_matches_failed")
                (Bool.or
                  (stringEq defPath "core::slice::index::slice_index_fail")
                  (Bool.or
                    (stringEq defPath "core::panicking::panic_bounds_check")
                    (Bool.or
                      (stringEq defPath "core::panicking::panic_explicit")
                      (Bool.or
                        (stringEq defPath "core::panicking::panic_display")
                        (Bool.or
                          (stringEq defPath "core::panicking::panic_str_2015")
                          (Bool.or
                            (stringEq defPath "core::panicking::unreachable_display")
                            (Bool.or
                              (stringEq defPath "core::option::unwrap_failed")
                              (Bool.or
                                (stringEq defPath "core::option::expect_failed")
                                (Bool.or
                                  (stringEq defPath "core::result::unwrap_failed")
                                  (Bool.or
                                    (stringEq defPath "core::panicking::panic_const::panic_const_add_overflow")
                                    (Bool.or
                                      (stringEq defPath "core::panicking::panic_const::panic_const_sub_overflow")
                                      (Bool.or
                                        (stringEq defPath "core::panicking::panic_const::panic_const_mul_overflow")
                                        (Bool.or
                                          (stringEq defPath "core::panicking::panic_const::panic_const_div_overflow")
                                          (Bool.or
                                            (stringEq defPath "core::panicking::panic_const::panic_const_rem_overflow")
                                            (Bool.or
                                              (stringEq defPath "core::panicking::panic_const::panic_const_neg_overflow")
                                              (Bool.or
                                                (stringEq defPath "core::panicking::panic_const::panic_const_shr_overflow")
                                                (Bool.or
                                                  (stringEq defPath "core::panicking::panic_const::panic_const_shl_overflow")
                                                  (Bool.or
                                                    (stringEq defPath "core::panicking::panic_const::panic_const_div_by_zero")
                                                    (stringEq defPath "core::panicking::panic_const::panic_const_rem_by_zero")))))))))))))))))))))))))

/--
Execute a basic-block `Terminator` from state `s`.

Supports `.goto`, `.return_` (both root-frame termination and interprocedural
return to `Memory.callStack`), `.unreachable`, `.switchInt`, `.assert`, `.drop`,
`.call`, and `.tailCall`. When `.call` targets the compiler intrinsic
`core::intrinsics::exact_div`, execution evaluates `evalExactDiv` inline; when
`.call` or `.tailCall` targets any other `defPath` without a transparent body in
`s.memory.callees`, execution emits a `MirCallE` effect interaction carrying
`(defPath, argVals, s.memory)`.

Reference (`core::intrinsics::exact_div`, Rust 1.98.0 standard library):
<https://doc.rust-lang.org/1.98.0/core/intrinsics/fn.exact_div.html>

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1932-L1939>

> "/// Performs an exact division, resulting in undefined behavior where
> /// `x % y != 0` or `y == 0` or `x == T::MIN && y == -1`
> ///
> /// This intrinsic does not have a stable counterpart.
> #[rustc_intrinsic_const_stable_indirect]
> #[rustc_nounwind]
> #[rustc_intrinsic]
> pub const unsafe fn exact_div<T: Copy>(x: T, y: T) -> T;"

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L812-L853>

> "/// Returns from the function. ...
> Return,
> ...
> /// Drop the `Place`
> Drop {
>     place: Place<'tcx>,
>     target: BasicBlock,
>     unwind: UnwindAction,
>     replace: bool,
>     drop: Option<BasicBlock>,
>     async_fut: Option<Local>,
> },
>
> /// Block ends with the call of a function.
> Call {
>     func: Operand<'tcx>,
>     args: Box<[Spanned<Operand<'tcx>>]>,
>     destination: Place<'tcx>,
>     target: Option<BasicBlock>,
>     unwind: UnwindAction,
>     call_source: CallSource,
>     fn_span: Span,
> },"
-/
def evalTerminator
    (s : MachineState)
    (term : Terminator)
    (currentBody : Option CapturedMir := .none) :
    MirStepNode :=
  match term.kind with
  | .goto target =>
    MirStepNode.step {
      s with
      frame := { s.frame with blockIdx := target, stmtIdx := 0 }
    }
  | .switchInt discr targets =>
    let bodyLayouts : LayoutTable :=
      match currentBody with
      | .some b => b.layouts
      | .none => emptyLayoutTable
    match
      evalOperand
        s.frame.locals
        discr
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
    with
    | .ok (.scalar sc) locals' =>
      let target :=
        lookupSwitchTarget sc.bits targets.branches targets.otherwise
      MirStepNode.emitStep (.event sc.bits) {
        s with
        frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
      }
    | .ok _ _ => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | .unwindResume =>
    match unwindFromCallStack s.memory.callStack s.memory with
    | .running nextState => MirStepNode.step nextState
    | .halted out => MirStepNode.retOutcome out
    | .faulted fk => MirStepNode.fail fk
  | .unwindTerminate => MirStepNode.retOutcome .abort
  | .return_ =>
    match get? s.frame.locals 0 with
    | .some (.init retVal) =>
      match s.memory.callStack with
      | .nil => MirStepNode.retNormal retVal s.memory
      | caller :: restStack =>
        match caller.isDiverging with
        | true => MirStepNode.fail .ub
        | false =>
          match
            writePlaceValue
              caller.frame.locals
              s.memory.borrows
              caller.destination
              retVal
          with
          | .ok updatedCallerLocals =>
            let restoredProtectors := restoreCallerProtectors caller
            MirStepNode.step {
              frame := {
                caller.frame with
                blockIdx := caller.returnTarget
                stmtIdx := 0
                locals := updatedCallerLocals
              }
              memory := {
                s.memory with
                callStack := restStack
                activeCallee := .some caller.callerBody
                activeProtectors := restoredProtectors
              }
            }
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .unreachable => MirStepNode.fail .ub
  | .drop place target _ =>
    match get? s.frame.locals place.local_ with
    | .none => MirStepNode.fail .ub
    | .some .dead => MirStepNode.fail .ub
    | .some slot =>
      match place.projection with
      | .nil =>
        match set? s.frame.locals place.local_ .uninit with
        | .some locals' =>
          MirStepNode.step {
            s with
            frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
          }
        | .none => MirStepNode.fail .ub
      | _ :: _ =>
        match slot with
        | .init rootVal =>
          match readProjectedValue s.frame.locals rootVal place.projection with
          | .ok _ =>
            MirStepNode.step {
              s with
              frame := { s.frame with blockIdx := target, stmtIdx := 0 }
            }
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
        | _ => MirStepNode.fail .ub
  | .call func argOps destination (.some targetBb) unwind =>
    let bodyLocalDecls := bodyLocalDeclsOf currentBody
    let bodyLayouts : LayoutTable :=
      match currentBody with
      | .some b => b.layouts
      | .none => emptyLayoutTable
    match
      resolveCallTarget
        s
        func
        (length argOps)
        bodyLocalDecls
        bodyLayouts
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok target localsAfterFunc =>
      match
        evalOperands
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok argVals locals' =>
        match findCallee? s.memory.callees target.defPath with
        | .some calleeBody =>
          match checkCalleeTargetCompatible target calleeBody (length argVals) with
          | false => MirStepNode.fail .ub
          | true =>
            match currentBody with
            | .none => MirStepNode.unsupported
            | .some callerBody =>
              MirStepNode.step
                (pushCalleeFrame
                  s
                  callerBody
                  locals'
                  destination
                  targetBb
                  calleeBody
                  argVals
                  unwind)
        | .none =>
          match isDirectExactDivTarget target with
          | true =>
            match argVals with
            | .scalar lhs :: .scalar rhs :: .nil =>
              let isSigned :=
                resolveIntrinsicIsSigned
                  target
                  bodyLocalDecls
                  bodyLayouts
                  argOps
              match evalExactDiv lhs rhs isSigned with
              | .some retScalar =>
                match writePlaceValue locals' s.memory.borrows destination (.scalar retScalar) with
                | .ok updatedLocals =>
                  MirStepNode.step {
                    frame := {
                      s.frame with
                      blockIdx := targetBb
                      stmtIdx := 0
                      locals := updatedLocals
                    }
                    memory := s.memory
                  }
                | .ub => MirStepNode.fail .ub
                | .unsupported => MirStepNode.unsupported
              | .none => MirStepNode.fail .ub
            | _ => MirStepNode.fail .ub
          | false =>
            match target.isIndirect with
            | true =>
              MirStepNode.extCall
                { defPath := target.defPath, args := argVals, memory := s.memory }
                (resumeExternalCall s locals' destination targetBb unwind)
            | false =>
              match
                evalDirectRustIntrinsic?
                  s
                  currentBody
                  target
                  bodyLocalDecls
                  bodyLayouts
                  argOps
                  argVals
                  locals'
                  destination
                  targetBb
                  unwind
              with
              | .some stepNode => stepNode
              | .none =>
                MirStepNode.extCall
                  { defPath := target.defPath, args := argVals, memory := s.memory }
                  (resumeExternalCall s locals' destination targetBb unwind)
  -- Diverging call (`target == Option.none`, return type `!`):
  | .call func argOps destination .none unwind =>
    let bodyLocalDecls := bodyLocalDeclsOf currentBody
    let bodyLayouts : LayoutTable :=
      match currentBody with
      | .some b => b.layouts
      | .none => emptyLayoutTable
    match
      resolveCallTarget
        s
        func
        (length argOps)
        bodyLocalDecls
        bodyLayouts
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok target localsAfterFunc =>
      match
        evalOperands
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok argVals locals' =>
        match findCallee? s.memory.callees target.defPath with
        | .some calleeBody =>
          match checkCalleeTargetCompatible target calleeBody (length argVals) with
          | false => MirStepNode.fail .ub
          | true =>
            match currentBody with
            | .none => MirStepNode.unsupported
            | .some callerBody =>
              MirStepNode.step
                (pushDivergingCalleeFrame
                  s
                  callerBody
                  locals'
                  destination
                  unwind
                  calleeBody
                  argVals)
        | .none =>
          match target.isIndirect with
          | false =>
            match isUnreachableCallTarget target.defPath with
            | true => MirStepNode.fail .ub
            | false =>
              match isAbortingPanicDefPath target.defPath with
              | true => MirStepNode.retOutcome .abort
              | false =>
                match isUnwindingPanicDefPath target.defPath with
                | true =>
                  match applyUnwindAction s locals' s.memory unwind with
                  | .running nextState => MirStepNode.step nextState
                  | .halted out => MirStepNode.retOutcome out
                  | .faulted fk => MirStepNode.fail fk
                | false =>
                  MirStepNode.extCall
                    { defPath := target.defPath, args := argVals, memory := s.memory }
                    (resumeExternalDivergingCall s locals' unwind)
          | true =>
            MirStepNode.extCall
              { defPath := target.defPath, args := argVals, memory := s.memory }
              (resumeExternalDivergingCall s locals' unwind)
  | .tailCall func argOps =>
    let bodyLocalDecls := bodyLocalDeclsOf currentBody
    let bodyLayouts : LayoutTable :=
      match currentBody with
      | .some b => b.layouts
      | .none => emptyLayoutTable
    match
      resolveCallTarget
        s
        func
        (length argOps)
        bodyLocalDecls
        bodyLayouts
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok target localsAfterFunc =>
      match
        evalOperands
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok argVals _ =>
        match findCallee? s.memory.callees target.defPath with
        | .some calleeBody =>
          match checkCalleeTargetCompatible target calleeBody (length argVals) with
          | false => MirStepNode.fail .ub
          | true =>
            MirStepNode.step (enterTailCalleeFrame s.memory calleeBody argVals)
        | .none =>
          MirStepNode.extCall
            { defPath := target.defPath, args := argVals, memory := s.memory }
            resumeExternalTailCall
  | .assert cond expected target unwind =>
    let bodyLayouts : LayoutTable :=
      match currentBody with
      | .some b => b.layouts
      | .none => emptyLayoutTable
    match
      evalOperand
        s.frame.locals
        cond
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
    with
    | .ok (.scalar sc) locals' =>
      let expectedBit := match expected with | true => 1 | false => 0
      match Nat.beq sc.bits expectedBit with
      | true =>
        MirStepNode.step {
          s with
          frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
        }
      | false =>
        match applyUnwindAction s locals' s.memory unwind with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk
    | .ok _ _ => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | _ => MirStepNode.unsupported

end Trusted.Rustc.V2026_06_01.MirSemantics
