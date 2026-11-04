import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Rustc.V2026_08_01.Layout
import Trusted.Rustc.V2026_08_01.MirAst.Types
import Trusted.Rustc.V2026_08_01.MirAst.Places
import Trusted.Rustc.V2026_08_01.MirAst.Terminators
import Trusted.Rustc.V2026_08_01.MirAst.Body
import Trusted.Rustc.V2026_08_01.MirSemantics.State
import Trusted.Rustc.V2026_08_01.MirSemantics.Scalars
import Trusted.Rustc.V2026_08_01.MirSemantics.Places

namespace Trusted.Rustc.V2026_08_01.MirSemantics

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst

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

mutual
/--
Match a potentially parametric pattern `pat : RigidTy` from a `TraitImplEntry`
header (`TraitRef.args`) against a call-site type argument `arg : RigidTy`,
accumulating `(paramIdx, boundTy)` bindings in `subst` and enforcing equality
when the same `RigidTy.param` index occurs multiple times (rejecting mismatched
diagonal instantiations such as `Pair<u32, u64>` against `Pair<T, T>`).

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation, except
> that the optional generic parameters are followed by a trait, followed by the
> keyword `for`, followed by the implementing type."
-/
def matchRigidTy (pat arg : RigidTy) (subst : List (Nat × RigidTy)) : Option (List (Nat × RigidTy)) :=
  match pat with
  | .param pIdx _ =>
    let rec lookupSubst (idx : Nat) : List (Nat × RigidTy) → Option RigidTy
      | .nil => Option.none
      | (k, v) :: rest => if k == idx then Option.some v else lookupSubst idx rest
    match lookupSubst pIdx subst with
    | Option.some existing => if rigidTyEq existing arg then Option.some subst else Option.none
    | Option.none => Option.some ((pIdx, arg) :: subst)
  | .tuple pFields =>
    match arg with
    | .tuple aFields => matchRigidTyList pFields aFields subst
    | _ => Option.none
  | .array pElem pLen =>
    match arg with
    | .array aElem aLen =>
      if pLen == aLen then matchRigidTy pElem aElem subst else Option.none
    | _ => Option.none
  | .slice pElem =>
    match arg with
    | .slice aElem => matchRigidTy pElem aElem subst
    | _ => Option.none
  | .ref pMut pPointee =>
    match arg with
    | .ref aMut aPointee =>
      if mutabilityEq pMut aMut then matchRigidTy pPointee aPointee subst else Option.none
    | _ => Option.none
  | .rawPtr pMut pPointee =>
    match arg with
    | .rawPtr aMut aPointee =>
      if mutabilityEq pMut aMut then matchRigidTy pPointee aPointee subst else Option.none
    | _ => Option.none
  | .adt pDefPath pArgs =>
    match arg with
    | .adt aDefPath aArgs =>
      if stringEq pDefPath aDefPath then matchRigidTyList pArgs aArgs subst else Option.none
    | _ => Option.none
  | .fnDef pDefPath pArgs =>
    match arg with
    | .fnDef aDefPath aArgs =>
      if stringEq pDefPath aDefPath then matchRigidTyList pArgs aArgs subst else Option.none
    | _ => Option.none
  | .fnPtr pIns pOut pSaf pAbi =>
    match arg with
    | .fnPtr aIns aOut aSaf aAbi =>
      if Bool.and (safetyEq pSaf aSaf) (callConvEq pAbi aAbi) then
        match matchRigidTyList pIns aIns subst with
        | Option.some s => matchRigidTy pOut aOut s
        | Option.none => Option.none
      else
        Option.none
    | _ => Option.none
  | .closure pDefPath pUpvars =>
    match arg with
    | .closure aDefPath aUpvars =>
      if stringEq pDefPath aDefPath then matchRigidTyList pUpvars aUpvars subst else Option.none
    | _ => Option.none
  | .alias pDefPath pArgs =>
    match arg with
    | .alias aDefPath aArgs =>
      if stringEq pDefPath aDefPath then matchRigidTyList pArgs aArgs subst else Option.none
    | _ => Option.none
  | _ =>
    if rigidTyEq pat arg then Option.some subst else Option.none

/--
Pointwise pattern matching of `pats : List RigidTy` against `args : List RigidTy`,
threading parameter bindings `subst`.

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation, except
> that the optional generic parameters are followed by a trait, followed by the
> keyword `for`, followed by the implementing type."
-/
def matchRigidTyList (pats args : List RigidTy) (subst : List (Nat × RigidTy)) : Option (List (Nat × RigidTy)) :=
  match pats, args with
  | .nil, .nil => Option.some subst
  | p :: ps, a :: as =>
    match matchRigidTy p a subst with
    | Option.some s => matchRigidTyList ps as s
    | Option.none => Option.none
  | _, _ => Option.none
end

/--
Extract the `count` generic type arguments of an `impl` method body in canonical
parameter-index order `0 .. count - 1` from pattern-matching substitution `subst`.

Reference (The Rust Reference, "Generic parameters"):
<https://doc.rust-lang.org/1.98.0/reference/items/generics.html>

> "Functions, type aliases, structs, enumerations, unions, traits, and
> implementations may be parameterized by types, constants, and lifetimes."
-/
def extractImplTypeArgs (subst : List (Nat × RigidTy)) (count : Nat) : Option (List RigidTy) :=
  if subst.length != count then
    Option.none
  else
    let rec loop : Nat → List RigidTy → Option (List RigidTy)
      | 0, acc => Option.some acc
      | i + 1, acc =>
        let rec lookupSubst (idx : Nat) : List (Nat × RigidTy) → Option RigidTy
          | .nil => Option.none
          | (k, v) :: rest => if k == idx then Option.some v else lookupSubst idx rest
        match lookupSubst i subst with
        | Option.some t => loop i (t :: acc)
        | Option.none => Option.none
    loop count .nil

/--
Resolve a direct or indirect call target `(defPath, typeArgs)` against `callees`
and registered `TraitImplEntry` tables (`extraTraitImpls` and `c.traitImpls`),
instantiating polymorphic `CapturedMir` bodies via `CapturedMir.instantiate`
using `callerLayouts`.

Reference (The Rust Reference, "Call expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/call-expr.html>

> "A call expression calls a function. It consists of an expression with a
> function type or a type that implements one of the Fn, FnMut, or FnOnce
> traits, followed by a parenthesized comma-separated list of argument
> expressions."
-/
def lookupCallee (callees : List CapturedMir) (callerLayouts : LayoutTable) (defPath : DefPath) (typeArgs : List RigidTy) (extraTraitImpls : List TraitImplEntry := .nil) : Option CapturedMir :=
  let directMatchOpt := match findCallee? callees defPath with
    | Option.some c => Option.some (c, typeArgs)
    | Option.none =>
      match typeArgs with
      | .nil => Option.none
      | .param _ _ :: _ => Option.none
      | _ =>
        let rec flatMapTraitImpls : List CapturedMir → List TraitImplEntry
          | .nil => .nil
          | c :: cs => c.traitImpls ++ flatMapTraitImpls cs
        let allTraitImpls := extraTraitImpls ++ flatMapTraitImpls callees
        let rec findImpl : List TraitImplEntry → Option (CapturedMir × List RigidTy)
          | .nil => Option.none
          | entry :: rest =>
            if stringEq entry.traitRef.defPath defPath then
              match matchRigidTyList entry.traitRef.args typeArgs .nil with
              | Option.some subst =>
                match findCallee? callees entry.implPath with
                | Option.some c =>
                  match extractImplTypeArgs subst c.typeParamCount with
                  | Option.some implTypeArgs => Option.some (c, implTypeArgs)
                  | Option.none => findImpl rest
                | Option.none => findImpl rest
              | Option.none => findImpl rest
            else
              findImpl rest
        findImpl allTraitImpls
  match directMatchOpt with
  | Option.none => Option.none
  | Option.some (calleeBody, effectiveTypeArgs) =>
    if calleeBody.typeParamCount == 0 && effectiveTypeArgs.isEmpty then
      Option.some calleeBody
    else if effectiveTypeArgs.length != calleeBody.typeParamCount then
      Option.none
    else
      let rec resolveLayouts : List RigidTy → List TypeLayout → Option (List TypeLayout)
        | .nil, acc => Option.some acc.reverse
        | argTy :: rest, acc =>
          match RigidTy.computeLayout callerLayouts.pointerBits callerLayouts.entries .nil Option.none argTy with
          | Option.some l => resolveLayouts rest (l :: acc)
          | Option.none =>
            match argTy with
            | .param idx _ =>
              match callerLayouts.lookup idx with
              | Option.some l => resolveLayouts rest (l :: acc)
              | Option.none => Option.none
            | _ => Option.none
      match resolveLayouts effectiveTypeArgs .nil with
      | Option.some argLayouts =>
        let subst : TypeSubst := effectiveTypeArgs.zip argLayouts
        Option.some (calleeBody.instantiate subst)
      | Option.none => Option.none
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
    (argVals : List Value) :
    MachineState :=
  let savedCaller : SavedCallerFrame := {
    callerBody := callerBody
    frame := { s.frame with locals := localsAfterArgs }
    destination := destination
    returnTarget := targetBb
    calleeProtectors := s.memory.activeProtectors
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
Resolve an unwinding outcome according to the call or assertion `UnwindAction`.

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
  | .continue_ => .halted .panic
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
Resume after an external `TerminatorKind.tailCall` response `ans : MirCallAns`.
-/
def resumeExternalTailCall (ans : MirCallAns) : MirExecState :=
  match ans with
  | .returned retVal memAfter =>
    match memAfter.callStack with
    | .nil => .halted (.normal (retVal, memAfter))
    | caller :: restStack =>
      match
        writePlaceValue
          caller.frame.locals
          memAfter.borrows
          caller.destination
          retVal
      with
      | .ok updatedCallerLocals =>
        let restoredProtectors :=
          match caller.callerProtector with
          | .some protId => protId :: caller.calleeProtectors
          | .none => caller.calleeProtectors
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
  | .panicked _ => .halted .panic
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
def evalCallTerminator (s : MachineState) (func : Operand) (argOps : List Operand) (destination : Place) (target : Option BasicBlockIdx) (unwind : UnwindAction) (currentBody : Option CapturedMir) : MirStepNode :=
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
  | .ok resolvedTarget localsAfterFunc =>
    match target with
    | .none =>
      match stringEq resolvedTarget.defPath "core::hint::unreachable_unchecked" with
      | true => MirStepNode.fail .ub
      | false => MirStepNode.unsupported
    | .some targetBb =>
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
        match lookupCallee s.memory.callees bodyLayouts resolvedTarget.defPath resolvedTarget.typeArgs s.memory.traitImpls with
        | .some calleeBody =>
          match checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) with
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
                  argVals)
        | .none =>
          match isDirectExactDivTarget resolvedTarget with
          | true =>
            match argVals with
            | .scalar lhs :: .scalar rhs :: .nil =>
              let isSigned :=
                match argOps with
                | lhsOp :: _ =>
                  operandIsSigned
                    bodyLocalDecls
                    lhsOp
                    bodyLayouts
                | .nil => false
              match evalExactDiv lhs rhs locals' s.memory isSigned with
              | .ok retVal localsAfter memAfter =>
                match writePlaceValue localsAfter memAfter.borrows destination retVal with
                | .ok updatedLocals =>
                  MirStepNode.step {
                    frame := {
                      s.frame with
                      blockIdx := targetBb
                      stmtIdx := 0
                      locals := updatedLocals
                    }
                    memory := memAfter
                  }
                | .ub => MirStepNode.fail .ub
                | .unsupported => MirStepNode.unsupported
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
            | _ => MirStepNode.unsupported
          | false =>
            MirStepNode.extCall
              { defPath := resolvedTarget.defPath, typeArgs := resolvedTarget.typeArgs, args := argVals, memory := s.memory }
              (resumeExternalCall s locals' destination targetBb unwind)

/--
Evaluate a `TerminatorKind.tailCall` terminator, resolving direct or indirect
function targets and polymorphic/trait-method callees via `lookupCallee`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L855-L868>

> "/// Block ends with the call of a function, which is a tail call."
-/
def evalTailCallTerminator (s : MachineState) (func : Operand) (argOps : List Operand) (currentBody : Option CapturedMir) : MirStepNode :=
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
      match lookupCallee s.memory.callees bodyLayouts target.defPath target.typeArgs s.memory.traitImpls with
      | .some calleeBody =>
        match checkCalleeTargetCompatible target calleeBody (length argVals) with
        | false => MirStepNode.fail .ub
        | true =>
          MirStepNode.step (enterTailCalleeFrame s.memory calleeBody argVals)
      | .none =>
        MirStepNode.extCall
          { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
          resumeExternalTailCall

/--
Evaluate basic-block `Terminator` `term` in `s`, producing the next
`MirStepNode` transition.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L812-L853>

> "/// Returns from the function. ...
> Return,
> ...
> /// Block ends with the call of a function.
> Call { ... },"
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
  | .return_ =>
    match get? s.frame.locals 0 with
    | .some (.init retVal) =>
      match s.memory.callStack with
      | .nil => MirStepNode.retNormal retVal s.memory
      | caller :: restStack =>
        match
          writePlaceValue
            caller.frame.locals
            s.memory.borrows
            caller.destination
            retVal
        with
        | .ok updatedCallerLocals =>
          let restoredProtectors :=
            match caller.callerProtector with
            | .some protId => protId :: caller.calleeProtectors
            | .none => caller.calleeProtectors
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
  | .call func argOps destination target unwind =>
    evalCallTerminator s func argOps destination target unwind currentBody
  | .tailCall func argOps =>
    evalTailCallTerminator s func argOps currentBody
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

end Trusted.Rustc.V2026_08_01.MirSemantics
