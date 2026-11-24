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
import Trusted.Rustc.V2026_06_01.MirSemantics.Statements

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
Construct a `TypeSubst` mapping each layout entry at index `idx` in a caller's
`LayoutTable.entries` to `(.param idx "", layout)` so `RigidTy.computeLayout`
can compute layouts of both bare `.param idx _` and compound type arguments
containing `.param idx _` (such as `(T, u32)`, `[T; N]`, or `Wrapper<T>`).

Reference (`compiler/rustc_middle/src/ty/sty.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/sty.rs#L282-L285>

> "pub struct ParamTy {
>     pub index: u32,
>     pub name: Symbol,
> }"
-/
def callerParamSubst (idx : Nat) : List TypeLayout → TypeSubst
  | .nil => .nil
  | l :: ls => (.param idx "", l) :: callerParamSubst (idx + 1) ls

/--
Resolve a direct or indirect call target `(defPath, typeArgs)` against `callees`
and registered `TraitImplEntry` tables (`extraTraitImpls` and `c.traitImpls`),
instantiating polymorphic `CapturedMir` bodies via `CapturedMir.instantiate`
using `callerLayouts`.

Reference (The Rust Reference, "Call expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/call-expr.html>

> "A call expression calls a function. The syntax of a call expression is an
> expression, called the function operand, followed by a parenthesized
> comma-separated list of expression, called the argument operands."
-/
def lookupCallee
    (callees : List CapturedMir)
    (callerLayouts : LayoutTable)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (extraTraitImpls : List TraitImplEntry := .nil) :
    Option CapturedMir :=
  match resolveCalleeBodyAndArgs? callees defPath typeArgs extraTraitImpls with
  | Option.none => Option.none
  | Option.some (calleeBody, effectiveTypeArgs) =>
    if calleeBody.typeParamCount == 0 && effectiveTypeArgs.isEmpty then
      Option.some calleeBody
    else if effectiveTypeArgs.length != calleeBody.typeParamCount then
      Option.none
    else
      let rec resolveLayouts :
          List RigidTy → List TypeLayout → Option (List TypeLayout)
        | .nil, acc => Option.some acc.reverse
        | argTy :: rest, acc =>
          match
            allParamsInCallerLayouts
              (length callerLayouts.entries)
              argTy
          with
          | false => Option.none
          | true =>
            match
              RigidTy.computeLayout
                callerLayouts.pointerBits
                callerLayouts.entries
                (callerParamSubst 0 callerLayouts.entries)
                Option.none
                argTy
            with
            | Option.some l => resolveLayouts rest (l :: acc)
            | Option.none => Option.none
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

> "A call expression calls a function. The syntax of a call expression is an
> expression, called the function operand, followed by a parenthesized
> comma-separated list of expression, called the argument operands."
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
- Otherwise evaluates `func` via `evalOperandWithBodyCast` (`evalOperand` with
  erased declarations, except that a moved place starting with
  `ProjectionElem.opaqueCast` is evaluated with `bodyLocalDecls`,
  `DIV-TR-OPAQUECAST-ROOT-DISPATCH`):
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
      evalOperandWithBodyCast
        s.frame.locals
        func
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        bodyLocalDecls
        s.memory.callStack
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
                 target.typeArgs
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
Test whether deallocating the locals `0 .. nLocals - 1` of the frame at depth
`depth` (the frame teardown of `TerminatorKind.return_` or of a tail call)
conflicts with an active function-entry protector: some borrow of such a local
is protected by `activeProtectors` and its permission prevents deallocation
(`preventsDeallocation`, so a protected `.cell` or `.disabled` tag does not
block; `DIV-MR-TB-FNENTRY-LOCAL-DEALLOC`, `DIV-MR-TB-UNSAFECELL-PROTECTED-IM`).
The check runs before the returning frame's protectors are released.
Definitionally `false` when no protector is active.

Reference (MiniRust `spec/mem/tree_borrows/memory.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/memory.md#L209-L215>

> "// Check that allocation is not strongly protected.
> if extra.root.contains_strong_protector_preventing_deallocation() {
>     throw_ub!("Tree Borrows: deallocating strongly protected allocation")
> }"

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L373>

> "At any point during the execution of a function, each local is either
> allocated or unallocated."
-/
def hasFrameDeallocProtectorConflict
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (depth nLocals : Nat) :
    Bool :=
  match activeProtectors with
  | .nil => false
  | _ :: _ =>
    match borrows with
    | .nil => false
    | entry :: rest =>
      match
        Bool.and
          (Bool.and
            (Nat.beq entry.targetFrameDepth depth)
            (Nat.blt entry.targetLocal nLocals))
          (Bool.and
            (isBorrowProtected activeProtectors entry)
            (preventsDeallocation entry.perm))
      with
      | true => true
      | false => hasFrameDeallocProtectorConflict rest activeProtectors depth nLocals

/--
Disable every borrow of a local `0 .. nLocals - 1` of the frame at depth `depth`
(`perm := .disabled`, `allocDead := true`): the frame's locals are deallocated
when it returns (or is replaced by a tail call), so every tag minted from them
becomes dangling (`DIV-MR-TB-FNENTRY-LOCAL-DEALLOC`). Borrows of other frames,
and caller-owned referents of the root frame (`targetLocal ≥ nLocals`), are
unchanged.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L373>

> "At any point during the execution of a function, each local is either
> allocated or unallocated."
-/
def disableFrameBorrows
    (borrows : List BorrowEntry)
    (depth nLocals : Nat) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | entry :: rest =>
    match
      Bool.and
        (Nat.beq entry.targetFrameDepth depth)
        (Nat.blt entry.targetLocal nLocals)
    with
    | true =>
      { entry with perm := .disabled, allocDead := true } ::
        disableFrameBorrows rest depth nLocals
    | false => entry :: disableFrameBorrows rest depth nLocals

/--
Disable every borrow of a local of a frame deeper than `depth`
(`targetFrameDepth > depth`): used when unwinding pops every frame above the
caller frame at depth `depth` that catches the unwind, so tags minted from the
popped frames' locals become dangling.
-/
def disableFramesAbove
    (borrows : List BorrowEntry)
    (depth : Nat) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | entry :: rest =>
    match Nat.blt depth entry.targetFrameDepth with
    | true =>
      { entry with perm := .disabled, allocDead := true } :: disableFramesAbove rest depth
    | false => entry :: disableFramesAbove rest depth

/--
Write the returned value `retVal` to the caller's `destination` after the callee
frame was popped (`caller` is the active frame with locals `callerLocals`, and
`mem` already has the caller's `callStack` and restored protectors): the write
behaves like the assignment `destination = move _0` in the caller. A whole
local or a field projection of the caller is written with the protector check
(`hasProtectedWriteConflict`) and the foreign-write transition
(`invalidateConflictingBorrows` / `invalidateConflictingBorrowsAtProj`) scoped
to the caller's depth `length mem.callStack`; a projection into an
uninitialized local writes into its default field shell
(`uninitFieldWriteShell?`); a dereferencing destination goes through
`evalPlaceWrite` and `invalidateDerefWriteBorrowsWithLayouts`, or
`foreignFrameDerefWrite` when it targets another frame.

A destination that is a pure `ProjectionElem.opaqueCast` chain
(`(_l as OpaqueTy) = call …`, `DIV-TR-OPAQUECAST-ROOT-DISPATCH`) names the whole
local: it takes the whole-local write (allowed on a live `.uninit` `_l`) after
validating `retVal` against the cast type `placeTy localDecls layouts dst` when
`localDecls` is non-empty. A cast chain followed by further projections
(`(_l as OpaqueTy).f`) takes the projected arm, whose field shell for an
uninitialized local is keyed on the cast type (`uninitFieldWriteShell?`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1148-L1150>

> "///  - [`OpaqueCast`](ProjectionElem::OpaqueCast): This projection changes the place's type to the
> ///    given one, and makes no other changes. A `OpaqueCast` projection on any type other than an
> ///    opaque type from the current crate is not well-formed."

Justification for the cast arm: the cast "changes the place's type to the given
one, and makes no other changes", so the return value is assigned to the local
itself, "as if assigned via `dest = move _0`", at the cast type.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L812-L819>

> "/// Returns from the function.
> ///
> /// Like function calls, the exact semantics of returns in Rust are unclear.
> /// Returning very likely at least assigns the value currently in the return
> /// place (`_0`) to the place specified in the associated `Call` terminator
> /// in the calling function, as if assigned via `dest = move _0`."
-/
def writeReturnDestination
    (callerLocals : List LocalSlot)
    (mem : Memory)
    (dst : Place)
    (retVal : Value)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    FrameWriteResult :=
  let depth := length mem.callStack
  match dst.projection, stripLeadingOpaqueCast dst.projection with
  | .nil, _ =>
    match get? callerLocals dst.local_ with
    | .some .dead => .ub
    | .some _ =>
      match
        hasProtectedWriteConflict
          mem.borrows
          mem.activeProtectors
          dst.local_
          .none
          .nil
          0
          0
          depth
      with
      | true => .ub
      | false =>
        match set? callerLocals dst.local_ (.init retVal) with
        | .some locals' =>
          .ok locals'
            { mem with
              borrows := invalidateConflictingBorrows mem.borrows dst.local_ .none depth }
        | .none => .ub
    | .none => .ub
  | .deref :: restProj, _ =>
    match
      evalPlaceWrite
        callerLocals
        mem.borrows
        dst
        retVal
        mem.activeProtectors
        localDecls
        layouts
        mem.callStack
    with
    | .ok locals' =>
      match
        Bool.or
          (derefWriteTreeUB callerLocals mem.borrows dst)
          (derefWriteUnionProtectorUB
            localDecls
            layouts
            callerLocals
            mem.borrows
            mem.activeProtectors
            dst
            restProj
            mem.callStack)
      with
      | true => .ub
      | false =>
        .ok locals'
          { mem with
            borrows :=
              invalidateDerefWriteBorrowsWithLayouts
                localDecls
                layouts
                callerLocals
                mem.borrows
                dst
                restProj
                mem.callStack }
    | .ub => foreignFrameDerefWrite callerLocals mem dst restProj retVal localDecls layouts
    | .unsupported => .unsupported
  | .opaqueCast _ :: _, .nil =>
    let tyValid :=
      match localDecls with
      | .nil => true
      | _ :: _ => validateValueForTy? layouts (placeTy localDecls layouts dst) retVal
    match tyValid with
    | false => .ub
    | true =>
        match get? callerLocals dst.local_ with
        | .some .dead => .ub
        | .some _ =>
          match
            hasProtectedWriteConflict
              mem.borrows
              mem.activeProtectors
              dst.local_
              .none
              .nil
              0
              0
              depth
          with
          | true => .ub
          | false =>
            match set? callerLocals dst.local_ (.init retVal) with
            | .some locals' =>
              .ok locals'
                { mem with
                  borrows := invalidateConflictingBorrows mem.borrows dst.local_ .none depth }
            | .none => .ub
        | .none => .ub
  | proj :: rest, _ =>
    let resolvedLocalProj :=
      resolveBorrowWriteLocalProj localDecls layouts callerLocals dst.local_ (proj :: rest)
    match
      hasProtectedWriteConflict
        mem.borrows
        mem.activeProtectors
        dst.local_
        .none
        resolvedLocalProj
        0
        0
        depth
    with
    | true => .ub
    | false =>
      let rootOpt : Option Value :=
        match get? callerLocals dst.local_ with
        | .some (.init rootVal) =>
          ensureNestedFieldShells
            rootVal
            (proj :: rest)
            localDecls
            layouts
            (placeTy localDecls layouts { local_ := dst.local_, projection := .nil })
        | .some .uninit => uninitFieldWriteShell? localDecls layouts dst.local_ proj rest
        | _ => .none
      match rootOpt with
      | .none => .ub
      | .some rootVal =>
        match
          writeProjectedForLocal
            callerLocals
            localDecls
            layouts
            dst.local_
            rootVal
            (proj :: rest)
            retVal
        with
        | .ok rootVal' =>
          match set? callerLocals dst.local_ (.init rootVal') with
          | .some locals' =>
            .ok locals'
              { mem with
                borrows :=
                  invalidateConflictingBorrowsAtProj
                    mem.borrows
                    dst.local_
                    .none
                    resolvedLocalProj
                    0
                    0
                    depth }
          | .none => .ub
        | .ub => .ub
        | .unsupported => .unsupported

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
Narrow the unwind action of the caller frame that a tail callee returns into
(`DIV-LM-TAILCALL-NOUNWIND-UNWIND`).

Modeled property and scope (`Runtime` MIR at `rustc` commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`): `stk` is `Memory.callStack` when a
`TerminatorKind.tailCall` replaces the active frame, whose head (when present)
is the `SavedCallerFrame` holding the return continuation inherited by the tail
callee, and `canUnwind` is the callee's `FnAbi::can_unwind`
(`CapturedMir.fnAbi.canUnwind`). When the callee cannot unwind, the inherited
`returnUnwind` becomes `UnwindAction.unreachable`, so `unwindFromCallStack`
faults with `.faulted .ub` when an unwind reaches that caller frame. For
`canUnwind = true` the result is `stk` itself (definitionally), and with an
empty `stk` (the modular root, whose continuation is not represented) the
narrowing is recorded in `Memory.rootUnwindCeiling` by `enterTailCalleeFrame`.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Calling a function with the wrong call ABI, or unwinding past a stack frame
> that does not allow unwinding (e.g. by calling a "C-unwind" function imported
> or transmuted as a "C" function or function pointer)."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L826-L835>

> "/// Semantically tail calls consists of two actions:
> /// - pop of the current stack frame
> /// - a call to the `func`, with the return address of the **current** caller
> ///   - so that a `return` inside `func` returns to the caller of the caller
> ///     of the function that is currently being executed
> ///
> /// Note that in difference with [`Call`] this is missing
> /// - `destination` (because it's always the return place)
> /// - `target` (because it's always taken from the current stack frame)
> /// - `unwind` (because it's always taken from the current stack frame)"

Reference (`compiler/rustc_const_eval/src/interpret/call.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_const_eval/src/interpret/call.rs#L391-L399>

> "if !callee_fn_abi.can_unwind {
>     // The callee cannot unwind, so force the `Unreachable` unwind handling.
>     match &mut cont {
>         ReturnContinuation::Stop { .. } => {}
>         ReturnContinuation::Goto { unwind, .. } => {
>             *unwind = mir::UnwindAction::Unreachable;
>         }
>     }
> }"

Justification: the tail callee's frame takes its `unwind` action "from the
current stack frame", i.e. from the `SavedCallerFrame` at the head of `stk`, and
the quoted interpreter passage replaces it by `Unreachable` when the callee's
ABI cannot unwind; unwinding into that caller is then "unwinding past a stack
frame that does not allow unwinding", which the Reference lists as undefined
behavior. Only the head is narrowed: deeper frames keep the unwind actions of
their own pending calls.

Modeling assumptions: the narrowing overwrites the head's `returnUnwind` in
place, which is sound because the replaced activation was the only frame that
could return or unwind through it; the interpreter passage is supplied compiler
behavior rather than a stable-documentation guarantee.
-/
@[reducible]
def narrowCallStackForTailCallee
    (stk : List SavedCallerFrame)
    (canUnwind : Bool) :
    List SavedCallerFrame :=
  match canUnwind with
  | true => stk
  | false =>
    match stk with
    | .nil => .nil
    | top :: rest => { top with returnUnwind := .unreachable } :: rest

/--
Enter `calleeBody` at basic block `0` for a `TerminatorKind.tailCall` without
pushing a caller frame onto `mem.callStack`, narrowing the inherited unwind
action when `calleeBody` cannot unwind (`DIV-LM-TAILCALL-NOUNWIND-UNWIND`):
`callStack := narrowCallStackForTailCallee mem.callStack calleeBody.fnAbi.canUnwind`
and, at the modular root (`mem.callStack = .nil`),
`rootUnwindCeiling := mem.rootUnwindCeiling && calleeBody.fnAbi.canUnwind`
(`enterTailCalleeFrame_rootUnwindCeiling`). For an unwinding callee
(`calleeBody.fnAbi.canUnwind = true`) both fields are definitionally unchanged.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L855-L865>

> "TailCall {
>     func: Operand<'tcx>,
>     args: Box<[Spanned<Operand<'tcx>>]>,
>     fn_span: Span,
> },"

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Calling a function with the wrong call ABI, or unwinding past a stack frame
> that does not allow unwinding (e.g. by calling a "C-unwind" function imported
> or transmuted as a "C" function or function pointer)."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L826-L835>

> "/// Semantically tail calls consists of two actions:
> /// - pop of the current stack frame
> /// - a call to the `func`, with the return address of the **current** caller
> ///   - so that a `return` inside `func` returns to the caller of the caller
> ///     of the function that is currently being executed
> ///
> /// Note that in difference with [`Call`] this is missing
> /// - `destination` (because it's always the return place)
> /// - `target` (because it's always taken from the current stack frame)
> /// - `unwind` (because it's always taken from the current stack frame)"

Reference (`compiler/rustc_const_eval/src/interpret/call.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_const_eval/src/interpret/call.rs#L391-L399>

> "if !callee_fn_abi.can_unwind {
>     // The callee cannot unwind, so force the `Unreachable` unwind handling.
>     match &mut cont {
>         ReturnContinuation::Stop { .. } => {}
>         ReturnContinuation::Goto { unwind, .. } => {
>             *unwind = mir::UnwindAction::Unreachable;
>         }
>     }
> }"

Justification: see `narrowCallStackForTailCallee` and `Memory.rootUnwindCeiling`.
`calleeBody.fnAbi.canUnwind` is the captured `FnAbi::can_unwind` of the callee
instance, the same field the quoted interpreter passage tests.

Modeling assumptions: caller-owned referents of the root frame are relocated by
`relocateRootCallerReferents` in `evalTailCallTerminator` before this function
is called; this function does not move any slot.
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
      callStack := narrowCallStackForTailCallee mem.callStack calleeBody.fnAbi.canUnwind
      activeCallee := .some calleeBody
      rootUnwindCeiling :=
        match calleeBody.fnAbi.canUnwind with
        | true => mem.rootUnwindCeiling
        | false =>
          match mem.callStack with
          | .nil => false
          | _ :: _ => mem.rootUnwindCeiling
    }
  }

/--
`enterTailCalleeFrame` updates the root unwind ceiling exactly as
`mem.rootUnwindCeiling && calleeBody.fnAbi.canUnwind` at the modular root and
leaves it unchanged inside an inline callee frame.
-/
theorem enterTailCalleeFrame_rootUnwindCeiling
    (mem : Memory)
    (calleeBody : CapturedMir)
    (argVals : List Value) :
    (enterTailCalleeFrame mem calleeBody argVals).memory.rootUnwindCeiling =
      match mem.callStack with
      | .nil => Bool.and mem.rootUnwindCeiling calleeBody.fnAbi.canUnwind
      | _ :: _ => mem.rootUnwindCeiling := by
  cases hU : calleeBody.fnAbi.canUnwind <;> cases hS : mem.callStack <;>
    cases hC : mem.rootUnwindCeiling <;>
    simp [enterTailCalleeFrame, hU, hS, hC]

/--
An unwinding tail callee leaves the call stack and the root unwind ceiling
unchanged: the state is the pre-repair `{ mem with activeCallee := .some calleeBody }`.
-/
theorem enterTailCalleeFrame_of_canUnwind
    (mem : Memory)
    (calleeBody : CapturedMir)
    (argVals : List Value)
    (hUnwind : calleeBody.fnAbi.canUnwind = true) :
    enterTailCalleeFrame mem calleeBody argVals =
      { frame := {
          blockIdx := 0
          stmtIdx := 0
          locals := initLocals calleeBody argVals
        }
        memory := { mem with activeCallee := .some calleeBody } } := by
  simp [enterTailCalleeFrame, narrowCallStackForTailCallee, hUnwind]

/--
Unwind out of the active frame by popping caller frames from `callStack` until a
caller frame catches the unwind (`.cleanup cleanupBb`), aborts (`.terminate`),
faults on an impossible unwind ABI (`.unreachable`), or reaches the root frame
(`callStack = .nil`): there the unwind escapes into the unmodeled caller of the
root function and halts with `.halted .panic` while `memAfter.rootUnwindCeiling`
is `true`, and faults with `.faulted .ub` once a tail call replaced the root
activation by a callee that cannot unwind (`Memory.rootUnwindCeiling = false`,
`DIV-LM-TAILCALL-NOUNWIND-UNWIND`).

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Calling a function with the wrong call ABI, or unwinding past a stack frame
> that does not allow unwinding (e.g. by calling a "C-unwind" function imported
> or transmuted as a "C" function or function pointer)."

Justification for the root arm: see `Memory.rootUnwindCeiling`. A `false` ceiling
records that the activation now running at the root inherited an `Unreachable`
unwind action in every calling context, so the escaping unwind is the quoted
undefined behavior; a `true` ceiling keeps the modular-root convention and does
not assert that the root's caller tolerates unwinding.

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
  | .nil, memAfter =>
    match memAfter.rootUnwindCeiling with
    | true => .halted .panic
    | false => .faulted .ub
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
        memory := {
          memCaller with
          borrows := disableFramesAbove memCaller.borrows (length restStack)
        }
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
Update `mem.borrows` after a direct (non-deref) destination write to `dst` in
the active frame (`depth = length mem.callStack`), leaving `mem` syntactically
unchanged when `mem.borrows = .nil` or `dst.projection = .deref :: _`.
-/
@[reducible]
def invalidateDirectDestWriteBorrows
    (mem : Memory)
    (locals : List LocalSlot)
    (dst : Place) :
    Memory :=
  match mem.borrows with
  | .nil => mem
  | bHead :: bTail =>
    let borrows := bHead :: bTail
    let depth := length mem.callStack
    match dst.projection with
    | .nil =>
      { mem with borrows := invalidateConflictingBorrows borrows dst.local_ .none depth }
    | .deref :: _ => mem
    | proj :: rest =>
      let resolvedLocalProj :=
        match resolveBorrowProjectionElems locals (proj :: rest) with
        | .some rp => rp
        | .none => proj :: rest
      { mem with
        borrows :=
          invalidateConflictingBorrowsAtProj
            borrows
            dst.local_
            .none
            resolvedLocalProj
            0
            0
            depth }

/--
Resume after an external `TerminatorKind.call` response `ans : MirCallAns`,
writing `retVal` to `destination` and updating `Memory` on normal return, or
dispatching `unwind` / `.abort` on abnormal return.

The answer memory keeps the caller's root unwind ceiling
(`rootUnwindCeiling := s.memory.rootUnwindCeiling`): a non-tail call pushes and
pops its own frame, so it cannot change the unwind action inherited by the root
activation (`Memory.rootUnwindCeiling`, `DIV-LM-TAILCALL-NOUNWIND-UNWIND`), and
the external answer is not constrained on that field.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Calling a function with the wrong call ABI, or unwinding past a stack frame
> that does not allow unwinding (e.g. by calling a "C-unwind" function imported
> or transmuted as a "C" function or function pointer)."

Modeling assumption: the external callee's answer memory `memAns` is trusted
for the heap, borrow, and call-stack state it reports, exactly as before; only
the root unwind ceiling is restored from `s.memory`.
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
  | .returned retVal memAns =>
    let memAfter : Memory :=
      { memAns with rootUnwindCeiling := s.memory.rootUnwindCeiling }
    match destination.projection with
    | .deref :: restProj =>
      match
        evalPlaceWrite
          localsAfterArgs
          memAfter.borrows
          destination
          retVal
          memAfter.activeProtectors
          .nil
          emptyLayoutTable
          memAfter.callStack
      with
      | .ok updatedLocals =>
        match derefWriteTreeUB localsAfterArgs memAfter.borrows destination with
        | true => .faulted .ub
        | false =>
          let borrows' :=
            invalidateDerefWriteBorrows
              localsAfterArgs
              memAfter.borrows
              destination
              restProj
              memAfter.callerLocals
              memAfter.callStack
          .running {
            frame := {
              s.frame with
              blockIdx := targetBb
              stmtIdx := 0
              locals := updatedLocals
            }
            memory := { memAfter with borrows := borrows' }
          }
      | .ub =>
        match foreignFrameDerefWrite localsAfterArgs memAfter destination restProj retVal with
        | .ok updatedLocals mem' =>
          .running {
            frame := {
              s.frame with
              blockIdx := targetBb
              stmtIdx := 0
              locals := updatedLocals
            }
            memory := mem'
          }
        | .ub => .faulted .ub
        | .unsupported => .faulted .unsupported
      | .unsupported => .faulted .unsupported
    | _ =>
      match
        evalPlaceWrite
          localsAfterArgs
          memAfter.borrows
          destination
          retVal
          memAfter.activeProtectors
          .nil
          emptyLayoutTable
          memAfter.callStack
      with
      | .ok updatedLocals =>
        .running {
          frame := {
            s.frame with
            blockIdx := targetBb
            stmtIdx := 0
            locals := updatedLocals
          }
          memory := {
            memAfter with
            borrows :=
              (invalidateDirectDestWriteBorrows memAfter localsAfterArgs destination).borrows
          }
        }
      | .ub => .faulted .ub
      | .unsupported => .faulted .unsupported
  | .panicked memAns =>
    applyUnwindAction
      s
      localsAfterArgs
      { memAns with rootUnwindCeiling := s.memory.rootUnwindCeiling }
      unwind
  | .aborted => .halted .abort

/--
Resume after an external diverging `TerminatorKind.call` (`target = .none`)
response `ans : MirCallAns`.

Because a diverging call has no return target (`!` return type), a normal return
(`MirCallAns.returned`) is immediate undefined behavior (`.faulted .ub`), an
unwind (`MirCallAns.panicked memAns`) dispatches `applyUnwindAction` on the
answer memory with the caller's root unwind ceiling restored
(`rootUnwindCeiling := s.memory.rootUnwindCeiling`, see `resumeExternalCall`),
and an abort (`MirCallAns.aborted`) halts with `.halted .abort`.

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
  | .panicked memAns =>
    applyUnwindAction
      s
      localsAfterArgs
      { memAns with rootUnwindCeiling := s.memory.rootUnwindCeiling }
      unwind
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
        let restoredProtectors := restoreCallerProtectors caller
        let callerMem : Memory := {
          memAfter with
          callStack := restStack
          activeCallee := .some caller.callerBody
          activeProtectors := restoredProtectors
        }
        match
          writeReturnDestination
            caller.frame.locals
            callerMem
            caller.destination
            retVal
            caller.callerBody.localDecls
            caller.callerBody.layouts
        with
        | .ok updatedCallerLocals mem' =>
          .running {
            frame := {
              caller.frame with
              blockIdx := caller.returnTarget
              stmtIdx := 0
              locals := updatedCallerLocals
            }
            memory := mem'
          }
        | .ub => .faulted .ub
        | .unsupported => .faulted .unsupported
  | .panicked memAfter =>
    unwindFromCallStack memAfter.callStack memAfter
  | .aborted => .halted .abort

/--
Membership of `name` in a list of ABI strings (`stringEq` on each entry).
-/
@[reducible]
def abiNameIn (name : String) : List String → Bool
  | .nil => false
  | candidate :: rest =>
    match stringEq name candidate with
    | true => true
    | false => abiNameIn name rest

/--
Whether a function called through calling convention `conv` can unwind, when the
captured `CallConv` decides it (`DIV-LM-TAILCALL-NOUNWIND-UNWIND`, external
callees): `.some true` when it certainly may unwind, `.some false` when it
certainly cannot, and `.none` when the captured convention does not decide.

Modeled property and scope (`rustc` commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `-C panic=unwind`, no function
`DefId`): `fn_can_unwind(tcx, None, abi)` over the ABI string that
`trusted/rustc-capture` records in `CallConv` (`ExternAbi::Rust` as
`CallConv.rust`, `ExternAbi::C { .. }` as `CallConv.c`, every other ABI as
`CallConv.other abi.as_str()`).

Reference (The Rust Reference 1.98.0, "External blocks", ABI):
<https://doc.rust-lang.org/1.98.0/reference/items/external-blocks.html#abi>

> "The strings that end with `-unwind` ... are the same as the corresponding ABI
> strings without `-unwind`, except that they allow the called function to
> safely unwind the stack (for example, via a Rust panic or a C++ exception)
> through the foreign frame into the caller's frame."

Reference (`compiler/rustc_middle/src/ty/layout.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/layout.rs#L1268-L1296>

> "use ExternAbi::*;
> match abi {
>     C { unwind }
>     | System { unwind }
>     | Cdecl { unwind }
>     | Stdcall { unwind }
>     | Fastcall { unwind }
>     | Vectorcall { unwind }
>     | Thiscall { unwind }
>     | Aapcs { unwind }
>     | Win64 { unwind }
>     | SysV64 { unwind } => unwind,
>     PtxKernel
>     | Msp430Interrupt
>     | X86Interrupt
>     | GpuKernel
>     | EfiApi
>     | AvrInterrupt
>     | AvrNonBlockingInterrupt
>     | CmseNonSecureCall
>     | CmseNonSecureEntry
>     | Custom
>     | RiscvInterruptM
>     | RiscvInterruptS
>     | RustInvalid
>     | Swift
>     | Unadjusted => false,
>     Rust | RustCall | RustCold | RustPreserveNone => tcx.sess.panic_strategy().unwinds(),
> }"

Reference (`compiler/rustc_abi/src/extern_abi.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/extern_abi.rs#L177-L181>

> "C { unwind: false } =><= "C",
> C { unwind: true } =><= "C-unwind",
> Rust =><= "Rust",
> Swift =><= "Swift",
> Aapcs { unwind: false } =><= "aapcs","

Justification: each `.some true` name is an ABI whose `unwind` flag is `true` in
the quoted `abi_impls!` table or a Rust ABI under `-C panic=unwind`; each
`.some false` name is an ABI whose arm in the quoted `match` is `unwind = false`
or the literal `false`. The answer is used only in the stated direction:
`.some false` licenses the undefined-behavior verdict for an unwind out of the
callee, `.some true` keeps the unwind, and `.none` licenses neither.

Modeling assumptions and unsupported behavior: `CallConv.c` stands for both
`"C"` (cannot unwind) and `"C-unwind"` (can unwind) because the capture lowers
`ExternAbi::C { .. }` to it, and `CallConv.rustIntrinsic` and unknown names are
not classified, so all three are `.none` (fail closed in
`resumeExternalTailCallWithAbi`). A `-C panic=abort` build, `#[rustc_nounwind]`,
and `-Z panic-in-drop=abort` only make more callees non-unwinding; they are
outside this table and are treated as "may unwind".
-/
@[reducible]
def callConvCanUnwind? : CallConv → Option Bool
  | .rust => .some true
  | .c => .none
  | .rustIntrinsic => .none
  | .other name =>
    match
      abiNameIn name
        ("C-unwind" :: "system-unwind" :: "cdecl-unwind" :: "stdcall-unwind" ::
          "fastcall-unwind" :: "vectorcall-unwind" :: "thiscall-unwind" ::
          "aapcs-unwind" :: "win64-unwind" :: "sysv64-unwind" :: "Rust" ::
          "rust-call" :: "rust-cold" :: "rust-preserve-none" :: .nil)
    with
    | true => .some true
    | false =>
      match
        abiNameIn name
          ("system" :: "cdecl" :: "stdcall" :: "fastcall" :: "vectorcall" ::
            "thiscall" :: "aapcs" :: "win64" :: "sysv64" :: "ptx-kernel" ::
            "msp430-interrupt" :: "x86-interrupt" :: "gpu-kernel" :: "efiapi" ::
            "avr-interrupt" :: "avr-non-blocking-interrupt" ::
            "cmse-nonsecure-call" :: "cmse-nonsecure-entry" :: "custom" ::
            "riscv-interrupt-m" :: "riscv-interrupt-s" :: "rust-invalid" ::
            "Swift" :: "unadjusted" :: .nil)
      with
      | true => .some false
      | false => .none

/--
Whether an external (out-of-table) tail callee resolved as `target` can unwind,
as far as the model knows (`DIV-LM-TAILCALL-NOUNWIND-UNWIND`): `.some true` for a
direct function-item callee (`target.isIndirect = false`), and
`callConvCanUnwind?` of the function-pointer ABI for an indirect callee (the
reified signature `target.fnSig`, else the call site's declared operand type
`callerFuncTyOpt`), `.none` when neither carries a function-pointer type.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Calling a function with the wrong call ABI, or unwinding past a stack frame
> that does not allow unwinding (e.g. by calling a "C-unwind" function imported
> or transmuted as a "C" function or function pointer)."

Justification: for an indirect callee, `resolveCallTarget` already requires the
call-site ABI and the reified signature ABI to agree
(`fnEntryCompatibleWithCallSite`), so either one names the ABI of the function
pointer through which the callee is entered; `callConvCanUnwind?` then gives the
unwind capability of that ABI in the stated one-directional sense.

Modeling assumptions and unsupported behavior: a direct function-item callee
keeps the pre-repair behavior (its unwind is propagated), because the ABI of an
out-of-table function item is not part of `RigidTy.fnDef`; this is a documented
fail-open residual for direct external tail callees declared with a
non-unwinding ABI.
-/
@[reducible]
def externalTargetCanUnwind
    (target : ResolvedCallTarget)
    (callerFuncTyOpt : Option Ty) :
    Option Bool :=
  match target.isIndirect with
  | false => .some true
  | true =>
    match target.fnSig with
    | .some (.fnPtr _ _ _ sigAbi) => callConvCanUnwind? sigAbi
    | _ =>
      match callerFuncTyOpt with
      | .some { kind := .fnPtr _ _ _ callerAbi, .. } => callConvCanUnwind? callerAbi
      | _ => .none

/--
Resume after an external `TerminatorKind.tailCall` response `ans : MirCallAns`
when the tail call was made with root unwind ceiling `rootCeiling`
(`s.memory.rootUnwindCeiling` of the tail-calling state) into a callee whose
unwind capability is `extUnwind` (`externalTargetCanUnwind`).

- The answer memory keeps `rootUnwindCeiling := rootCeiling` (the external
  answer is not constrained on that field), and a normal return or an unwind out
  of a callee that may unwind (`extUnwind = .some true`) then behaves as
  `resumeExternalTailCall`.
- An unwind out of a callee that certainly cannot unwind
  (`extUnwind = .some false`) is undefined behavior (`.faulted .ub`) at every
  call-stack depth: inside an inline callee the inherited caller frame's unwind
  action is narrowed to `UnwindAction.unreachable`, and at the modular root the
  root unwind ceiling is narrowed to `false`
  (`narrowCallStackForTailCallee`, `Memory.rootUnwindCeiling`).
- When the captured ABI does not decide (`extUnwind = .none`, e.g. `CallConv.c`
  for both `"C"` and `"C-unwind"`), an unwind keeps only the verdict that holds
  under both readings: `.faulted .ub` when the unwinding reading also faults
  with `.ub`, and `.faulted .unsupported` otherwise (fail closed).

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Calling a function with the wrong call ABI, or unwinding past a stack frame
> that does not allow unwinding (e.g. by calling a "C-unwind" function imported
> or transmuted as a "C" function or function pointer)."

Reference (`compiler/rustc_const_eval/src/interpret/call.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_const_eval/src/interpret/call.rs#L391-L399>

> "if !callee_fn_abi.can_unwind {
>     // The callee cannot unwind, so force the `Unreachable` unwind handling.
>     match &mut cont {
>         ReturnContinuation::Stop { .. } => {}
>         ReturnContinuation::Goto { unwind, .. } => {
>             *unwind = mir::UnwindAction::Unreachable;
>         }
>     }
> }"

Justification: a callee that cannot unwind is entered with unwind action
`Unreachable` in every calling context, so an unwind out of it is the quoted
undefined behavior regardless of the caller frames; a callee that may unwind
inherits the tail caller's continuation unchanged, which is
`resumeExternalTailCall` on the unchanged ceiling. For the undecided case the
model reports undefined behavior only when both readings do, so it never turns
a permitted unwind into undefined behavior, and it never propagates an unwind
that one reading forbids.

Modeling assumptions and unsupported behavior: see `callConvCanUnwind?` and
`externalTargetCanUnwind`; `.faulted .unsupported` marks the undecided unwind.
-/
def resumeExternalTailCallWithAbi
    (rootCeiling : Bool)
    (extUnwind : Option Bool)
    (ans : MirCallAns) :
    MirExecState :=
  match ans with
  | .returned retVal memAns =>
    resumeExternalTailCall
      (.returned retVal { memAns with rootUnwindCeiling := rootCeiling })
  | .panicked memAns =>
    match extUnwind with
    | .some false => .faulted .ub
    | .some true =>
      resumeExternalTailCall
        (.panicked { memAns with rootUnwindCeiling := rootCeiling })
    | .none =>
      match
        resumeExternalTailCall
          (.panicked { memAns with rootUnwindCeiling := rootCeiling })
      with
      | .faulted .ub => .faulted .ub
      | _ => .faulted .unsupported
  | .aborted => .halted .abort

/--
Whether `entry` is a live borrow of a caller-owned referent of the root frame
whose locals are `0 .. nOld - 1` (`DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`):
its allocation is live (`allocDead = false`), it targets the root frame
(`targetFrameDepth = 0`), and its target slot lies past the root frame's own
locals (`nOld ≤ targetLocal`), i.e. in `Memory.callerLocals`.

Reference (The Rust Reference 1.98.0, "Pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

> "Shared references point to memory which is owned by some other value."
> "Mutable references point to memory which is owned by some other value."

Justification: the memory a reference or raw-pointer argument of the root
function points to is owned by the root's caller, so it is not deallocated when
the root activation is replaced by a tail callee. The model addresses such
referents as depth-`0` slots past the root frame; a borrow whose allocation was
deallocated (`allocDead = true`, set together with `perm := .disabled` by
`disableFrameBorrows`, `disableFramesAbove`, and `disableLocalBorrows`) is a
dangling borrow of a former root-frame local, not a caller referent, even when
its slot index is past a later, narrower root frame.

Modeling assumption: every transition that sets `allocDead := true` also sets
`perm := .disabled`, so an unshifted dead borrow that comes to alias a callee
local still faults on every access.
-/
@[reducible]
def isRootCallerReferentBorrow (nOld : Nat) (entry : BorrowEntry) : Bool :=
  Bool.and
    (Bool.not entry.allocDead)
    (Bool.and (Nat.beq entry.targetFrameDepth 0) (Nat.ble nOld entry.targetLocal))

/--
Whether `borrows` contains a live caller-owned referent borrow of the root frame
with `nOld` locals (`isRootCallerReferentBorrow`).
-/
def hasAnyRootCallerReferent : List BorrowEntry → Nat → Bool
  | .nil, _ => false
  | entry :: rest, nOld =>
    match isRootCallerReferentBorrow nOld entry with
    | true => true
    | false => hasAnyRootCallerReferent rest nOld

/--
Shift the target slot of every live caller-owned referent borrow of the root
frame with `nOld` locals (`isRootCallerReferentBorrow`) by `delta` slots,
leaving tags, permissions, protectors, parent links, projections, and byte
ranges unchanged.
-/
def shiftRootCallerReferentBorrows
    (borrows : List BorrowEntry)
    (nOld delta : Nat) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | entry :: rest =>
    match isRootCallerReferentBorrow nOld entry with
    | true =>
      { entry with targetLocal := Nat.add entry.targetLocal delta } ::
        shiftRootCallerReferentBorrows rest nOld delta
    | false => entry :: shiftRootCallerReferentBorrows rest nOld delta

/--
`n` copies of `slot`.
-/
@[reducible]
def replicateLocalSlots : Nat → LocalSlot → List LocalSlot
  | .zero, _ => .nil
  | .succ n, slot => slot :: replicateLocalSlots n slot

/--
Concatenate two `LocalSlot` lists.
-/
@[reducible]
def appendLocalSlots : List LocalSlot → List LocalSlot → List LocalSlot
  | .nil, ys => ys
  | x :: xs, ys => x :: appendLocalSlots xs ys

/--
Relocate the caller-owned referents of the root frame when a root tail call
replaces a frame of `nOld` locals by a wider frame of `nNew` locals
(`DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`).

Modeled property and scope: at the modular root (`callStack = .nil`) the memory
behind incoming reference and raw-pointer arguments is owned by the root's
caller and stays allocated across a `TerminatorKind.tailCall`; the model
addresses it as depth-`0` slots `targetLocal ≥ length locals` backed by
`Memory.callerLocals` (`foreignFrameSlot?`). A wider tail callee's own locals
`nOld .. nNew - 1` would otherwise occupy those slot indices, so the callee's
frame would shadow the referents (and a later frame teardown would disable
their borrows). When `nNew > nOld` and a live referent borrow exists, every such
borrow's `targetLocal` is shifted by `delta = nNew - nOld`, and
`Memory.callerLocals` is padded with `delta` leading `.dead` slots when it is
indexed directly at `targetLocal` (`length callerLocals > nOld`), so the shifted
index reads the same slot. When `callerLocals` is no longer than the old frame
(`length callerLocals ≤ nOld`), no slot is reachable directly at
`targetLocal ≥ nOld`; the `copy_nonoverlapping` paths then use the frame-relative
index `targetLocal - length locals`, which the shift preserves
(`(targetLocal + delta) - nNew = targetLocal - nOld`), so `callerLocals` is left
unchanged. When `nNew ≤ nOld` or no live referent borrow exists, `mem` is
returned unchanged (definitionally, by evaluating the two tests).

Reference (The Rust Reference 1.98.0, "Pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

> "Shared references point to memory which is owned by some other value."
> "Mutable references point to memory which is owned by some other value."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L826-L830>

> "/// Semantically tail calls consists of two actions:
> /// - pop of the current stack frame
> /// - a call to the `func`, with the return address of the **current** caller
> ///   - so that a `return` inside `func` returns to the caller of the caller
> ///     of the function that is currently being executed"

Justification: popping the current stack frame deallocates that frame's locals
only; memory "owned by some other value" outside the frame is unaffected, so a
pointer argument forwarded to the tail callee must still reach its referent.
The relocation changes only the model's slot addressing of referents: borrow
tags (pointer provenance), permissions, protectors, and parent links are
untouched, so aliasing and Tree Borrows state are preserved.

Modeling assumptions and unsupported behavior: `BorrowEntry`,
`activeFrameSlot?`, `foreignFrameSlot?`, and `foreignFrameTarget?` are unchanged;
a referent's `callerLocals` index and its synthetic address (keyed on
`targetLocal`) change across a widening root tail call; a `callerLocals` list
that mixes directly indexed and frame-relative referents is not supported.
-/
def relocateRootCallerReferents
    (mem : Memory)
    (nOld nNew : Nat) :
    Memory :=
  match Nat.blt nOld nNew with
  | false => mem
  | true =>
    match hasAnyRootCallerReferent mem.borrows nOld with
    | false => mem
    | true =>
      let delta := Nat.sub nNew nOld
      { mem with
        borrows := shiftRootCallerReferentBorrows mem.borrows nOld delta
        callerLocals :=
          match Nat.blt nOld (length mem.callerLocals) with
          | true => appendLocalSlots (replicateLocalSlots delta .dead) mem.callerLocals
          | false => mem.callerLocals }

/--
No borrow, no caller-owned referent borrow.
-/
@[simp]
theorem hasAnyRootCallerReferent_nil (nOld : Nat) :
    hasAnyRootCallerReferent .nil nOld = false :=
  rfl

/--
`relocateRootCallerReferents` is the identity when the new frame is not wider.
-/
theorem relocateRootCallerReferents_not_wider
    (mem : Memory)
    (nOld nNew : Nat)
    (hLe : Nat.blt nOld nNew = false) :
    relocateRootCallerReferents mem nOld nNew = mem := by
  simp [relocateRootCallerReferents, hLe]

/--
`relocateRootCallerReferents` is the identity when no live caller-owned referent
borrow exists.
-/
theorem relocateRootCallerReferents_no_referents
    (mem : Memory)
    (nOld nNew : Nat)
    (hNone : hasAnyRootCallerReferent mem.borrows nOld = false) :
    relocateRootCallerReferents mem nOld nNew = mem := by
  unfold relocateRootCallerReferents
  cases Nat.blt nOld nNew <;> simp [hNone]

/--
Memory in which an in-table tail callee with `nCallee` locals is entered, given
the tail-calling frame's call stack `callStack`, the memory after the frame
teardown `memAfterTeardown`, and the torn-down frame's local count `nLocals`
(`DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`): at the modular root
(`callStack = .nil`) the caller-owned referents are relocated past the callee's
frame (`relocateRootCallerReferents memAfterTeardown nLocals nCallee`); inside
an inline callee frame the memory is `memAfterTeardown` unchanged.

Reference (The Rust Reference 1.98.0, "Pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

> "Shared references point to memory which is owned by some other value."
> "Mutable references point to memory which is owned by some other value."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L826-L830>

> "/// Semantically tail calls consists of two actions:
> /// - pop of the current stack frame
> /// - a call to the `func`, with the return address of the **current** caller
> ///   - so that a `return` inside `func` returns to the caller of the caller
> ///     of the function that is currently being executed"

Justification: see `relocateRootCallerReferents`. Only the root frame addresses
caller-owned referents as slots past its own locals (`foreignFrameSlot?` falls
back to `Memory.callerLocals` only at depth `0`), so only a tail call that
replaces the root frame can shadow them; a tail call inside an inline callee
frame replaces a frame whose locals no other frame's slot indices depend on.

Modeling assumption: the relocation runs after the frame teardown
(`disableFrameBorrows`), so borrows of the popped frame's own locals are already
dead and are not relocated.
-/
def tailCalleeEntryMemory
    (callStack : List SavedCallerFrame)
    (memAfterTeardown : Memory)
    (nLocals nCallee : Nat) :
    Memory :=
  match callStack with
  | .nil => relocateRootCallerReferents memAfterTeardown nLocals nCallee
  | _ :: _ => memAfterTeardown

/--
At the modular root the tail callee is entered in the relocated memory.
-/
@[simp]
theorem tailCalleeEntryMemory_nil
    (memAfterTeardown : Memory)
    (nLocals nCallee : Nat) :
    tailCalleeEntryMemory .nil memAfterTeardown nLocals nCallee =
      relocateRootCallerReferents memAfterTeardown nLocals nCallee :=
  rfl

/--
Inside an inline callee frame the tail callee is entered in the torn-down
memory unchanged.
-/
@[simp]
theorem tailCalleeEntryMemory_cons
    (caller : SavedCallerFrame)
    (restStack : List SavedCallerFrame)
    (memAfterTeardown : Memory)
    (nLocals nCallee : Nat) :
    tailCalleeEntryMemory (caller :: restStack) memAfterTeardown nLocals nCallee =
      memAfterTeardown :=
  rfl

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

Every variant except `.constEvalSelect`, `.copyNonOverlapping`, and
`.writeBytes` is value-returning: its result depends only on the argument
values and is written to the call destination (`evalNonSelectIntrinsicCall`).
`.copyNonOverlapping` and `.writeBytes` are the call forms of the memory
intrinsics, which read and write memory through their pointer arguments and
return `()` (`evalCopyNonOverlappingCall`, `evalWriteBytesCall`).

Reference (`compiler/rustc_middle/src/ty/intrinsic.rs` and
`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L3019-L3028>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L3041-L3050>

> "Compiler intrinsics."

> "/// This is an accidentally-stable alias to [`ptr::copy_nonoverlapping`]; use that instead.
> ...
> pub const unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize);"

> "/// This is an accidentally-stable alias to [`ptr::write_bytes`]; use that instead.
> ...
> pub const unsafe fn write_bytes<T>(dst: *mut T, val: u8, count: usize);"
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
  /-- `core::intrinsics::align_of_val` dynamic or static pointee alignment. -/
  | alignOfVal : RustIntrinsicKind
  /-- `core::intrinsics::copy_nonoverlapping` call form: copy `count` elements
  between non-overlapping regions (`evalCopyNonOverlappingCall`). -/
  | copyNonOverlapping : RustIntrinsicKind
  /-- `core::intrinsics::write_bytes` call form: set the bytes of `count`
  elements to a byte value (`evalWriteBytesCall`). -/
  | writeBytes : RustIntrinsicKind

/--
Classify a canonical `DefPath` into a `RustIntrinsicKind` when it names one of
the `core::intrinsics::*` compiler intrinsics modeled inline in `evalTerminator`.

Only the canonical `core::intrinsics::*` paths are recognized. In particular the
`core::ptr::copy_nonoverlapping` and `core::ptr::write_bytes` wrappers are
ordinary functions (with their own `ub_checks` precondition assertions) and are
called like any other callee.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L3019-L3022>

> "Compiler intrinsics."

> "/// This is an accidentally-stable alias to [`ptr::copy_nonoverlapping`]; use that instead.
> // Note (intentionally not in the doc comment): `ptr::copy_nonoverlapping` adds some extra
> // debug assertions; if you are writing compiler tests or code inside the standard library
> // that wants to avoid those debug assertions, directly call this intrinsic instead."
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
                                                  match stringEq defPath "core::intrinsics::align_of_val" with
                                                  | true => .some .alignOfVal
                                                  | false =>
                                                    match stringEq defPath "core::intrinsics::copy_nonoverlapping" with
                                                    | true => .some .copyNonOverlapping
                                                    | false =>
                                                      match stringEq defPath "core::intrinsics::write_bytes" with
                                                      | true => .some .writeBytes
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
Return the signedness of an intrinsic's integer type parameter: `.some true`
for `RigidTy.int _`, `.some false` for `RigidTy.uint _`, `.some false` for
`char` when `allowChar = true`, and `.none` for every other type.

The arithmetic, saturating, shift, and exact-division intrinsics accept only
integer types, and `three_way_compare` also accepts `char`, whose values compare
as unsigned code points. Returning `.none` for any other type lets callers step
to `MirStepNode.unsupported` instead of guessing a signedness: an unsigned guess
for a signed type changes both the overflow conditions and the results.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The signed two's complement integer types consist of: ... i8, i16, i32, i64,
> i128, isize"

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1827-L1837>

> "/// Does a three-way comparison between the two arguments,
> /// which must be of character or integer (signed or unsigned) type."
-/
@[reducible]
def intrinsicIntSignedness? (allowChar : Bool) : RigidTy → Option Bool
  | .int _ => .some true
  | .uint _ => .some false
  | .char =>
    match allowChar with
    | true => .some false
    | false => .none
  | _ => .none

/--
Resolve the signedness of the primary type parameter `T` of a
`CallConv.rustIntrinsic` call with `intrinsicIntSignedness? allowChar`. The first
monomorphized type argument in `target.typeArgs` is authoritative when present;
otherwise the type of the first argument operand is used, or the type of the
second argument operand when `sameRhsTy = true` (for homogeneous binary
intrinsics `f<T>(x: T, y: T)` whose first operand is untyped). Returns `.none`,
which callers turn into `MirStepNode.unsupported`, when none of these sources
names an accepted type.

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
    (argOps : List Operand)
    (allowChar : Bool := false)
    (sameRhsTy : Bool := true) :
    Option Bool :=
  match target.typeArgs with
  | firstTy :: _ => intrinsicIntSignedness? allowChar firstTy
  | .nil =>
    match argOps with
    | lhsOp :: restOps =>
      match operandTy bodyLocalDecls bodyLayouts lhsOp with
      | .some ty => intrinsicIntSignedness? allowChar ty.kind
      | .none =>
        match sameRhsTy, restOps with
        | true, rhsOp :: _ =>
          match operandTy bodyLocalDecls bodyLayouts rhsOp with
          | .some ty => intrinsicIntSignedness? allowChar ty.kind
          | .none => .none
        | _, _ => .none
    | .nil => .none

/--
Resolve the signedness of the shift-count type parameter `U` of
`unchecked_shl<T, U>` or `unchecked_shr<T, U>`. The second monomorphized type
argument in `target.typeArgs` is authoritative when present; otherwise the type
of the second argument operand is used. Returns `.none`, which callers turn into
`MirStepNode.unsupported`, when neither source names an integer type.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1962-L1981>

> "/// Performs an unchecked left shift, resulting in undefined behavior when
> /// `y < 0` or `y >= N`, where N is the width of T in bits.
> ...
> pub const unsafe fn unchecked_shl<T: Copy, U: Copy>(x: T, y: U) -> T;"
-/
@[reducible]
def resolveIntrinsicShiftSigned
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand) :
    Option Bool :=
  match target.typeArgs with
  | _ :: shiftTy :: _ => intrinsicIntSignedness? false shiftTy
  | _ =>
    match argOps with
    | _ :: rhsOp :: _ =>
      match operandTy bodyLocalDecls bodyLayouts rhsOp with
      | .some ty => intrinsicIntSignedness? false ty.kind
      | .none => .none
    | _ => .none

/--
Step for a pointer intrinsic whose pointee or slice element type `ty` has no
size or alignment the model can resolve. Every caller needs a sized `ty`:
`arith_offset::<T>` and slice elements require `T: Sized`, and `size_of_val` and
`align_of_val` reach this step only with a thin pointer, after dispatching
`[T]`, `str`, `dyn Trait`, extern-type tails (`intrinsicTailIsExtern`), and wide
pointers (`intrinsicWidePointeeStep`). An unsized `ty` (including an array or
tuple containing an unsized component) is therefore ill-typed and faults with
`.ub`. A sized `ty` without a `LayoutTable` entry, such as an ADT that no local
of the body has as its type, is a well-typed program the model cannot evaluate,
so it steps to `MirStepNode.unsupported` rather than guessing a layout.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Most types have a fixed size that is known at compile time and implement the
> trait `Sized`. A type with a size that is known only at run-time is called a
> dynamically sized type (DST) or, informally, an unsized type."
-/
@[reducible]
def intrinsicUnresolvedLayoutStep (ty : RigidTy) : MirStepNode :=
  match isUnsizedRigidTy 8 ty with
  | true => MirStepNode.fail .ub
  | false => MirStepNode.unsupported

/--
Return the last element of `ks` when every preceding element is sized
(`isUnsized k = false`), or `.none` when `ks` is empty or has an unsized prefix
element.

A tuple can be unsized only through its last element; a tuple with an unsized
non-last field (such as `([u8], [u8])` or `([u8], ExternType)`) is ill-formed
and cannot be a valid dynamically sized type.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Structs may contain a DST as the last field; this makes the struct itself a
> DST."
-/
@[reducible]
def intrinsicLastRigidTy? (isUnsized : RigidTy → Bool) : List RigidTy → Option RigidTy
  | .nil => .none
  | k :: .nil => .some k
  | k :: rest =>
    match isUnsized k with
    | true => .none
    | false => intrinsicLastRigidTy? isUnsized rest

/--
Fuel-bounded check for whether the unsized tail of `ty` may be an extern type:
`ty` is `.foreign` itself, or `ty` is a tuple whose prefix fields are sized and
whose last element's tail may be an extern type. Exhausting `fuel` answers
`true`, so the caller steps to `MirStepNode.unsupported` rather than computing a
layout.

`rustc` passes pointers to extern-type tails as thin pointers, and `core`
documents that `size_of_val` and `align_of_val` on such a value are always safe
to call but may panic or return a wrong value. The model cannot tell which, so `size_of_val`
and `align_of_val` step to `MirStepNode.unsupported` for these pointees; the
CTFE interpreter likewise reports an unsupported operation ("`extern type` does
not have known layout"). An ADT whose last field is an extern type is not
detected here because `RigidTy.adt` does not record its fields; for such an ADT
the model returns the size of a `LayoutTable` entry if one exists, one of the
"wrong value" outcomes that the documentation permits.

Reference (`library/core/src/mem/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/mem/mod.rs#L412-L435>

> "///     - an (unstable) [extern type], then this function is always safe to
> ///       call, but may panic or otherwise return the wrong value, as the
> ///       extern type's layout is not known. This is the same behavior as
> ///       [`size_of_val`] on a reference to a type with an extern type tail."

Reference (`library/core/src/mem/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/mem/mod.rs#L560-L579>

> "///     - an (unstable) [extern type], then this function is always safe to
> ///       call, but may panic or otherwise return the wrong value, as the
> ///       extern type's layout is not known. This is the same behavior as
> ///       [`align_of_val`] on a reference to a type with an extern type tail."
-/
@[reducible]
def intrinsicTailIsExtern : Nat → RigidTy → Bool
  | .zero, _ => true
  | .succ fuel', ty =>
    match ty with
    | .foreign _ => true
    | .tuple ks =>
      match intrinsicLastRigidTy? (isUnsizedRigidTy fuel') ks with
      | .some k => intrinsicTailIsExtern fuel' k
      | .none => false
    | _ => false

/--
Fuel-bounded check for whether `ty` may be a dynamically sized type whose
pointers are wide (`Value.aggregate 0 [.ptr p 8, metadata]`): a slice, `str`,
or `dyn Trait`; an ADT, whose fields `RigidTy.adt` does not record; an
unrecognized `.other` type; or a tuple whose prefix fields are sized and whose
last element may be one. Exhausting `fuel` answers `true`.

`size_of_val` and `align_of_val` dispatch top-level `[T]`, `str`, and
`dyn Trait` pointees themselves. When they receive a wide pointer to any other
pointee, a well-typed program can only be passing a struct or tuple that ends
in an unsized field. `rustc` computes the size and alignment of such a value
from the offsets of its statically sized fields and the metadata of its tail,
which the model does not track, so the step is `MirStepNode.unsupported`. A
wide pointer to a type that cannot end in an unsized field, such as `u64` or a
tuple with an unsized non-last field, is malformed and faults with `.ub`.

Reference (`library/core/src/mem/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/mem/mod.rs#L412-L435>

> "/// - If `T` is `Sized`, this function is always safe to call.
> /// - If the unsized tail of `T` is:
> ///     - a [slice], then the length of the slice tail must be an initialized
> ///       integer, and the size of the *entire value*
> ///       (dynamic tail length + statically sized prefix) must fit in `isize`."
-/
@[reducible]
def intrinsicTailMayBeUnsized : Nat → RigidTy → Bool
  | .zero, _ => true
  | .succ fuel', ty =>
    match ty with
    | .slice _ => true
    | .str => true
    | .dynamic _ => true
    | .adt _ _ => true
    | .other _ => true
    | .tuple ks =>
      match intrinsicLastRigidTy? (isUnsizedRigidTy fuel') ks with
      | .some k => intrinsicTailMayBeUnsized fuel' k
      | .none => false
    | _ => false

/--
Check whether `metaVal` is a well-formed wide-pointer metadata component: a
scalar length (`.scalar _`, for slice-tailed DSTs) or an 8-byte vtable pointer
(`.ptr _ 8`, for `dyn Trait` or trait-object-tailed DSTs). Any other `Value`
(such as `.unit`, `.aggregate _ _`, or a non-64-bit pointer) is malformed and
faults with `.ub`.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html#r-dynamic-sized.pointer-types>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types
>
> * Pointers to slices and `str` also store the number of elements.
> * Pointers to trait objects also store a pointer to a vtable."
-/
@[reducible]
def isValidWidePtrMetaVal : Value → Bool
  | .scalar _ => true
  | .ptr _ ptrSz => Nat.beq ptrSz 8
  | _ => false

/--
Check whether `ptrArgVal` has the runtime value representation of a valid thin
or wide pointer argument (`*const T` for some `T: ?Sized`) on a 64-bit target:
either an 8-byte thin pointer (`.ptr _ 8`) or a 2-field wide pointer
(`.aggregate 0 [.ptr _ 8, metaVal]`) with well-formed metadata
(`isValidWidePtrMetaVal metaVal`). Any other `Value` (such as `.scalar _`,
`.unit`, a non-64-bit pointer, or a wide pointer with malformed metadata) cannot
represent `*const T` for any `T: ?Sized` and faults with `.ub` even when the
pointee type `T` is unknown.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html#r-dynamic-sized.pointer-types>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types
>
> * Pointers to slices and `str` also store the number of elements.
> * Pointers to trait objects also store a pointer to a vtable."
-/
@[reducible]
def isValidIntrinsicPtrArgVal : Value → Bool
  | .ptr _ ptrSz => Nat.beq ptrSz 8
  | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
    Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal)
  | _ => false

/--
Step for `size_of_val` or `align_of_val` when the pointer argument is a
well-formed wide pointer but the pointee `ty` is not `[T]`, `str`, or
`dyn Trait`: `MirStepNode.unsupported` when `intrinsicTailMayBeUnsized` admits a
custom dynamically sized type, and `MirStepNode.fail .ub` otherwise.

Reference (`library/core/src/mem/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/mem/mod.rs#L412-L435>

> "/// - If the unsized tail of `T` is:
> ///     - a [slice], then the length of the slice tail must be an initialized
> ///       integer, and the size of the *entire value*
> ///       (dynamic tail length + statically sized prefix) must fit in `isize`."
-/
@[reducible]
def intrinsicWidePointeeStep (ty : RigidTy) : MirStepNode :=
  match intrinsicTailMayBeUnsized 8 ty with
  | true => MirStepNode.unsupported
  | false => MirStepNode.fail .ub

/--
Resolve the pointee `RigidTy` `T` for pointer-parameterized intrinsics
(`arith_offset<T>`, `size_of_val<T>`, `align_of_val<T>`), consulting
`target.typeArgs` first and falling back to the pointee type of the first pointer
operand in `argOps`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2850-L2861>

> "pub const unsafe fn size_of_val<T: ?Sized>(ptr: *const T) -> usize;"
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
Step for `arith_offset`, `size_of_val`, or `align_of_val` when
`resolveIntrinsicPointeeTy?` finds no pointee type: `MirStepNode.fail .ub` when
the first argument operand has a known type that is not a pointer (an
ill-typed call), and `MirStepNode.unsupported` when no operand type is known
(no `argOps`, or an operand that `operandTy` cannot type). An unknown pointee
leaves the stride, size, or alignment undetermined, so the call is a program
the model cannot evaluate rather than one it can show to be undefined.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2850-L2861>

> "pub const unsafe fn size_of_val<T: ?Sized>(ptr: *const T) -> usize;"
-/
@[reducible]
def intrinsicMissingPointeeStep
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand) :
    MirStepNode :=
  match argOps with
  | ptrOp :: _ =>
    match operandTy bodyLocalDecls bodyLayouts ptrOp with
    | .some _ => MirStepNode.fail .ub
    | .none => MirStepNode.unsupported
  | .nil => MirStepNode.unsupported

/--
Check whether every element of `ks` satisfies `pred`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2400-L2408>

> "#[rustc_intrinsic]
> pub const fn const_eval_select<ARG: Tuple, F, G, RET>(
>     _arg: ARG,
>     _called_in_const: F,
>     _called_at_rt: G,
> ) -> RET"
-/
@[reducible]
def allZeroSizedUnitElemTys (pred : RigidTy → Bool) : List RigidTy → Bool
  | .nil => true
  | k :: rest =>
    match pred k with
    | true => allZeroSizedUnitElemTys pred rest
    | false => false

/--
Test whether `ty` is an inhabited zero-sized `RigidTy` that can be represented
by `Value.unit` when unpacking a `ConstValue.zeroSized` tuple argument in
`const_eval_select` (excluding uninhabited `.never` and positive-size scalars or
pointers).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2400-L2408>

> "#[rustc_intrinsic]
> pub const fn const_eval_select<ARG: Tuple, F, G, RET>(
>     _arg: ARG,
>     _called_in_const: F,
>     _called_at_rt: G,
> ) -> RET"
-/
@[reducible]
def isZeroSizedUnitElemTy : Nat → RigidTy → Bool
  | .zero, _ => false
  | .succ fuel', ty =>
    match ty with
    | .tuple ks => allZeroSizedUnitElemTys (isZeroSizedUnitElemTy fuel') ks
    | .fnDef _ _ => true
    | .array _ .zero => true
    | .array elemTy (.succ _) => isZeroSizedUnitElemTy fuel' elemTy
    | _ => false

/--
Unpack the tuple argument `arg : ARG` of `core::intrinsics::const_eval_select`
into a list of individual call argument `Value`s.

Accepts `Value.aggregate 0 fieldVals` (when `tupleTyOpt` is `.none` or `.some
(.tuple elemTys)` of matching length) and `Value.unit` (for `()` or a tuple of
inhabited zero-sized fields), returning `.none` (which faults with `.ub`) for
any non-tuple value, non-tuple `ARG` type, or arity mismatch.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2400-L2408>

> "#[rustc_intrinsic]
> pub const fn const_eval_select<ARG: Tuple, F, G, RET>(
>     _arg: ARG,
>     _called_in_const: F,
>     _called_at_rt: G,
> ) -> RET"
-/
@[reducible]
def unpackConstEvalSelectArgs?
    (tupleVal : Value)
    (tupleTyOpt : Option RigidTy := .none) :
    Option (List Value) :=
  match tupleVal with
  | .aggregate 0 fieldVals =>
    match tupleTyOpt with
    | .none => .some fieldVals
    | .some (.tuple elemTys) =>
      match Nat.beq (length fieldVals) (length elemTys) with
      | true => .some fieldVals
      | false => .none
    | .some _ => .none
  | .unit =>
    match tupleTyOpt with
    | .none => .some .nil
    | .some (.tuple elemTys) =>
      match allZeroSizedUnitElemTys (isZeroSizedUnitElemTy 8) elemTys with
      | true => .some (replicateValue (length elemTys) .unit)
      | false => .none
    | .some _ => .none
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
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2400-L2408>

> "#[rustc_intrinsic]
> pub const fn const_eval_select<ARG: Tuple, F, G, RET>(
>     _arg: ARG,
>     _called_in_const: F,
>     _called_at_rt: G,
> ) -> RET"
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
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L800-L814>

> "Call {
> ...
>     func: Operand<'tcx>,
> ...
>     args: Box<[Spanned<Operand<'tcx>>]>,
> ...
>     destination: Place<'tcx>,
> ...
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
  match destination.projection with
  | .deref :: restProj =>
    match
      evalPlaceWrite
        locals'
        s.memory.borrows
        destination
        retVal
        s.memory.activeProtectors
        .nil
        emptyLayoutTable
        s.memory.callStack
    with
    | .ok updatedLocals =>
      match derefWriteTreeUB locals' s.memory.borrows destination with
      | true => MirStepNode.fail .ub
      | false =>
        let borrows' :=
          invalidateDerefWriteBorrows
            locals'
            s.memory.borrows
            destination
            restProj
            s.memory.callerLocals
            s.memory.callStack
        MirStepNode.step {
          frame := {
            s.frame with
            blockIdx := targetBb
            stmtIdx := 0
            locals := updatedLocals
          }
          memory := { s.memory with borrows := borrows' }
        }
    | .ub =>
      match foreignFrameDerefWrite locals' s.memory destination restProj retVal with
      | .ok updatedLocals mem' =>
        MirStepNode.step {
          frame := {
            s.frame with
            blockIdx := targetBb
            stmtIdx := 0
            locals := updatedLocals
          }
          memory := mem'
        }
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
    | .unsupported => MirStepNode.unsupported
  | _ =>
    match
      writePlaceValue
        locals'
        s.memory.borrows
        destination
        retVal
        (callStack := s.memory.callStack)
    with
    | .ok updatedLocals =>
      MirStepNode.step {
        frame := {
          s.frame with
          blockIdx := targetBb
          stmtIdx := 0
          locals := updatedLocals
        }
        memory := invalidateDirectDestWriteBorrows s.memory locals' destination
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
`.constEvalSelect`, `.copyNonOverlapping`, and `.writeBytes`) from evaluated
argument values `argVals`.

`evalDirectRustIntrinsic?` dispatches the call-form memory intrinsics
`.copyNonOverlapping` and `.writeBytes` to `evalCopyNonOverlappingCall` and
`evalWriteBytesCall` before reaching this function. They reach it only as the
runtime function of `core::intrinsics::const_eval_select`, where their
memory effect is not modeled and the call is `MirStepNode.unsupported`.

Malformed argument lists and values fault with `.ub`. An intrinsic whose result
depends on the signedness of an integer type parameter steps to
`MirStepNode.unsupported` when `resolveIntrinsicIsSigned` or
`resolveIntrinsicShiftSigned` cannot determine it, rather than assuming an
unsigned type.

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
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
        | .some pointeeTy =>
          match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
          | .some elemSz =>
            match evalArithOffset ptrVal ptrSz countSc elemSz with
            | .some retPtrVal =>
              writeIntrinsicReturn s locals' destination targetBb (.ptr retPtrVal 8)
            | .none => MirStepNode.fail .ub
          | .none => intrinsicUnresolvedLayoutStep pointeeTy
        | .none => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
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
      match resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps with
      | .some isSigned =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalSaturatingAdd lhs rhs isSigned)
      | .none => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .saturatingSub =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      match resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps with
      | .some isSigned =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalSaturatingSub lhs rhs isSigned)
      | .none => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .uncheckedShl =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      match resolveIntrinsicShiftSigned target bodyLocalDecls bodyLayouts argOps with
      | .some rhsSigned =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalUncheckedShl lhs rhs rhsSigned)
      | .none => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .uncheckedShr =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      match
        resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps (sameRhsTy := false),
        resolveIntrinsicShiftSigned target bodyLocalDecls bodyLayouts argOps
      with
      | .some lhsSigned, .some rhsSigned =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalUncheckedShr lhs rhs lhsSigned rhsSigned)
      | _, _ => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .uncheckedAdd =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      match resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps with
      | .some isSigned =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalUncheckedAdd lhs rhs isSigned)
      | .none => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .uncheckedSub =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      match resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps with
      | .some isSigned =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalUncheckedSub lhs rhs isSigned)
      | .none => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .uncheckedMul =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      match resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps with
      | .some isSigned =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalUncheckedMul lhs rhs isSigned)
      | .none => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .uncheckedDiv =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      match resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps with
      | .some isSigned =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalUncheckedDiv lhs rhs isSigned)
      | .none => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .uncheckedRem =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      match resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps with
      | .some isSigned =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalUncheckedRem lhs rhs isSigned)
      | .none => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .threeWayCompare =>
    match argVals with
    | .scalar lhs :: .scalar rhs :: .nil =>
      match resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps (allowChar := true) with
      | .some isSigned =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalThreeWayCompare lhs rhs isSigned)
      | .none => MirStepNode.unsupported
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
            | .none => intrinsicUnresolvedLayoutStep elemTy
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
      -- The size of a `dyn Trait` value is read from its vtable, which the
      -- model does not track; malformed non-wide pointers still fault with `.ub`.
      | .some (.dynamic _) =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
          match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
          | false => MirStepNode.fail .ub
          | true => MirStepNode.unsupported
        | _ => MirStepNode.fail .ub
      | .some pointeeTy =>
        match ptrArgVal with
        | .ptr _ ptrSz =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true =>
            match intrinsicTailIsExtern 8 pointeeTy with
            | true => MirStepNode.unsupported
            | false =>
              match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
              | .some sz =>
                match Nat.ble (signedHalfModulus 8) sz with
                | true => MirStepNode.fail .ub
                | false =>
                  writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨sz, 8⟩)
              | .none => intrinsicUnresolvedLayoutStep pointeeTy
        | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
          match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
          | false => MirStepNode.fail .ub
          | true => intrinsicWidePointeeStep pointeeTy
        | _ => MirStepNode.fail .ub
      | .none =>
        match isValidIntrinsicPtrArgVal ptrArgVal with
        | false => MirStepNode.fail .ub
        | true => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
    | _ => MirStepNode.fail .ub
  | .alignOfVal =>
    match argVals with
    | ptrArgVal :: .nil =>
      match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
      -- `align_of_val` has the same safety conditions as `size_of_val`: the
      -- slice's total size must fit in `isize` even though only the element
      -- alignment is returned.
      | .some (.slice elemTy) =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true =>
            match
              intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy,
              intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy
            with
            | .some elemSz, .some alignBytes =>
              match evalSliceSizeOfVal elemSz lenSc with
              | .some _ =>
                writeIntrinsicReturn s locals' destination targetBb
                  (.scalar ⟨alignBytes, 8⟩)
              | .none => MirStepNode.fail .ub
            | _, _ => intrinsicUnresolvedLayoutStep elemTy
        | _ => MirStepNode.fail .ub
      | .some .str =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true =>
            match evalSliceSizeOfVal 1 lenSc with
            | .some _ =>
              writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 8⟩)
            | .none => MirStepNode.fail .ub
        | _ => MirStepNode.fail .ub
      -- The alignment of a `dyn Trait` value is read from its vtable, which the
      -- model does not track; malformed non-wide pointers still fault with `.ub`.
      | .some (.dynamic _) =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
          match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
          | false => MirStepNode.fail .ub
          | true => MirStepNode.unsupported
        | _ => MirStepNode.fail .ub
      | .some pointeeTy =>
        match ptrArgVal with
        | .ptr _ ptrSz =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true =>
            match intrinsicTailIsExtern 8 pointeeTy with
            | true => MirStepNode.unsupported
            | false =>
              match intrinsicRigidTyAlign bodyLocalDecls bodyLayouts pointeeTy with
              | .some alignBytes =>
                writeIntrinsicReturn s locals' destination targetBb
                  (.scalar ⟨alignBytes, 8⟩)
              | .none => intrinsicUnresolvedLayoutStep pointeeTy
        | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
          match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
          | false => MirStepNode.fail .ub
          | true => intrinsicWidePointeeStep pointeeTy
        | _ => MirStepNode.fail .ub
      | .none =>
        match isValidIntrinsicPtrArgVal ptrArgVal with
        | false => MirStepNode.fail .ub
        | true => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
    | _ => MirStepNode.fail .ub
  | .copyNonOverlapping => MirStepNode.unsupported
  | .writeBytes => MirStepNode.unsupported
  | .constEvalSelect => MirStepNode.fail .ub

/--
Test whether `kind` is parameterized by the pointee type `T` of its first
pointer argument (`arith_offset<T>`, `size_of_val<T>`, `align_of_val<T>`)
rather than by the value type of its first argument.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L899-L916>

> "pub const unsafe fn arith_offset<T>(dst: *const T, offset: isize) -> *const T;"
-/
@[reducible]
def isPtrPointeeIntrinsicKind : RustIntrinsicKind → Bool
  | .arithOffset => true
  | .sizeOfVal => true
  | .alignOfVal => true
  | _ => false

/--
Supply type arguments for a runtime intrinsic target `rtTarget` of
`const_eval_select` whose callee constant carries none (`rtTarget.typeArgs =
[]`), using the element types `elemTys` of `const_eval_select`'s first type
argument `ARG = .tuple elemTys`:
- for `arith_offset`, `size_of_val`, and `align_of_val` (`isPtrPointee = true`),
  the pointee `T` of the first element `*const T`, `*mut T`, or `&T`;
- for the value intrinsics (`isPtrPointee = false`), `elemTys` itself.

The bound `G: FnOnce<ARG, Output = RET>` makes `ARG` the tuple of the parameter
types of `called_at_rt`. Each value intrinsic modeled here is generic exactly
over the types of its leading parameters, in order (`T` of `exact_div(x: T, y:
T)`, `T` and `U` of `unchecked_shl(x: T, y: U)`), and each pointer intrinsic is
generic only over the pointee of its first parameter (`T` of
`arith_offset(dst: *const T, offset: isize)`). These element types are
therefore the instantiation that `rtTarget` omits; trailing extras, such as the
second `T` of `exact_div`, are ignored by `resolveIntrinsicIsSigned`. Captured
MIR always carries a callee's generic arguments, and `rustc` replaces every
`const_eval_select` call with a direct call to `called_at_rt` before
`optimized_mir` (`remap_mir_for_const_eval_select` in `inner_optimized_mir`), so
this fallback only affects hand-built MIR.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2400-L2408>

> "#[rustc_intrinsic]
> pub const fn const_eval_select<ARG: Tuple, F, G, RET>(
>     _arg: ARG,
>     _called_in_const: F,
>     _called_at_rt: G,
> ) -> RET
> where
>     G: FnOnce<ARG, Output = RET>,
>     F: const FnOnce<ARG, Output = RET>;"

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1962-L1971>

> "pub const unsafe fn unchecked_shl<T: Copy, U: Copy>(x: T, y: U) -> T;"

Reference (`compiler/rustc_mir_transform/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_mir_transform/src/lib.rs#L798-L799>

> "    let body = tcx.mir_drops_elaborated_and_const_checked(did).steal();
>     let mut body = remap_mir_for_const_eval_select(tcx, body, hir::Constness::NotConst);"
-/
@[reducible]
def withConstEvalSelectIntrinsicTypeArgs
    (rtTarget : ResolvedCallTarget)
    (tupleTyOpt : Option RigidTy)
    (isPtrPointee : Bool) :
    ResolvedCallTarget :=
  match rtTarget.typeArgs with
  | _ :: _ => rtTarget
  | .nil =>
    match tupleTyOpt with
    | .some (.tuple elemTys) =>
      match isPtrPointee with
      | false => { rtTarget with typeArgs := elemTys }
      | true =>
        match elemTys with
        | .rawPtr _ pointeeTy :: _ => { rtTarget with typeArgs := pointeeTy :: .nil }
        | .ref _ pointeeTy :: _ => { rtTarget with typeArgs := pointeeTy :: .nil }
        | _ => rtTarget
    | _ => rtTarget

/--
Construct synthetic zero-sized constant `Operand`s carrying the element types
`elemTys` of a `const_eval_select` argument tuple `ARG = .tuple elemTys`.

These operands exist only so that `operandTy` can type the runtime target's
arguments during signedness and pointee resolution in
`evalNonSelectIntrinsicCall`. They are never evaluated, and their `.zeroSized`
values and `layoutIdx := 0` do not describe the runtime arguments, which come
from the unpacked tuple value.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2400-L2408>

> "#[rustc_intrinsic]
> pub const fn const_eval_select<ARG: Tuple, F, G, RET>(
>     _arg: ARG,
>     _called_in_const: F,
>     _called_at_rt: G,
> ) -> RET"
-/
@[reducible]
def rigidTysToZeroSizedOps : List RigidTy → List Operand
  | .nil => .nil
  | ty :: rest =>
    .constant { ty := { kind := ty, layoutIdx := 0 }, val := .zeroSized } ::
      rigidTysToZeroSizedOps rest

/--
Extract synthetic argument `Operand`s from `const_eval_select`'s first type
argument `tupleTyOpt` (`ARG = .tuple elemTys`), or `.nil` when `tupleTyOpt` is
absent. Passing these operands to `evalNonSelectIntrinsicCall` ensures that
`intrinsicMissingPointeeStep` observes the known first-argument type from `ARG`
(and faults with `MirStepNode.fail .ub` when `ARG` passes a non-pointer type to
`arith_offset`, `size_of_val`, or `align_of_val`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2400-L2408>

> "#[rustc_intrinsic]
> pub const fn const_eval_select<ARG: Tuple, F, G, RET>(
>     _arg: ARG,
>     _called_in_const: F,
>     _called_at_rt: G,
> ) -> RET"
-/
@[reducible]
def constEvalSelectTupleArgOps : Option RigidTy → List Operand
  | .some (.tuple elemTys) => rigidTysToZeroSizedOps elemTys
  | _ => .nil

/--
Test whether `defPath` is an unreachable hint or intrinsic
(`"core::hint::unreachable_unchecked"`, `"std::hint::unreachable_unchecked"`, or
`"core::intrinsics::unreachable"`), reaching which is immediate undefined
behavior (`MirStepNode.fail .ub`).

Reference (`library/core/src/hint.rs` and `library/core/src/intrinsics/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L373-L384>

> "/// Informs the optimizer that this point in the code is not reachable,
> /// enabling further optimizations.
> ...
> #[rustc_intrinsic]
> pub const unsafe fn unreachable() -> !;"
-/
@[simp]
def isUnreachableCallTarget (defPath : DefPath) : Bool :=
  Bool.or
    (stringEq defPath "core::hint::unreachable_unchecked")
    (Bool.or
      (stringEq defPath "std::hint::unreachable_unchecked")
      (stringEq defPath "core::intrinsics::unreachable"))

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
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/panicking.rs#L217-L226>

> "/// Like `panic`, but without unwinding and track_caller to reduce the impact
> /// on codesize on the caller.
> ...
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
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/panicking.rs#L130-L138>

> "/// The underlying implementation of core's `panic!` macro when no formatting
> /// is used.
> ...
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
Complete a call-form memory intrinsic (`RustIntrinsicKind.copyNonOverlapping`,
`RustIntrinsicKind.writeBytes`) whose memory effect `node` was computed by the
statement-level semantics: on `MirStepNode.step s'`, keep the frame
locals and memory of `s'` and write the intrinsic's `()` return value
(`Value.unit`) to `destination`, continuing at `targetBb`
(`writeIntrinsicReturn`); faults and unsupported nodes propagate unchanged.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L800-L814>

> "Call {
> ...
>     destination: Place<'tcx>,
> ...
>     target: Option<BasicBlock>,"
-/
@[reducible]
def finishMemIntrinsicCall
    (s : MachineState)
    (node : MirStepNode)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    MirStepNode :=
  match node with
  | .tau (.running s') =>
    writeIntrinsicReturn { s with memory := s'.memory } s'.frame.locals destination targetBb .unit
  | other => other

/--
Evaluate a direct call `copy_nonoverlapping::<T>(src, dst, count)` whose
argument operands `argOps` evaluated to `argVals` (with frame `locals'`).

The memory effect is the statement form
`StatementKind.intrinsic (.copyNonOverlapping src dst count)`
(`evalCopyNonOverlappingWithCount`, in `Statements.lean`) after checking that
`count` is a `usize`-width scalar (`countSc.sizeBytes == layoutPointerBytes
bodyLayouts`): the same pointer, Tree Borrows permission, frame, overlap
(`projectionsOverlap`), and typed or byte-level copy checks on the same source
and destination operands. The call then writes `()` to `destination` and
continues at `targetBb` (`finishMemIntrinsicCall`). An argument list that is not
two values and a `usize`-width scalar `count` faults with `.ub` (calling a
function with ABI-incompatible arguments).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L3019-L3028>

> "/// This is an accidentally-stable alias to [`ptr::copy_nonoverlapping`]; use that instead.
> ...
> pub const unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize);"

Reference (`core::ptr::copy_nonoverlapping` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L439-L465>

> "/// Copies `count * size_of::<T>()` bytes from `src` to `dst`. The source
> /// and destination must *not* overlap.
> ...
> /// # Safety
> ///
> /// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `src` must be [valid] for reads of `count * size_of::<T>()` bytes or that number must be 0.
> ///
> /// * `dst` must be [valid] for writes of `count * size_of::<T>()` bytes or that number must be 0.
> ///
> /// * Both `src` and `dst` must be properly aligned.
> ///
> /// * The region of memory beginning at `src` with a size of `count *
> ///   size_of::<T>()` bytes must *not* overlap with the region of memory
> ///   beginning at `dst` with the same size."
-/
def evalCopyNonOverlappingCall
    (s : MachineState)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    MirStepNode :=
  match argOps, argVals with
  | srcOp :: dstOp :: _ :: .nil, srcVal :: dstVal :: .scalar countSc :: .nil =>
    match Nat.beq countSc.sizeBytes (layoutPointerBytes bodyLayouts) with
    | false => MirStepNode.fail .ub
    | true =>
      finishMemIntrinsicCall
        s
        (evalCopyNonOverlappingWithCount
          s
          srcOp
          dstOp
          bodyLocalDecls
          bodyLayouts
          srcVal
          dstVal
          countSc.bits
          locals')
        destination
        targetBb
  | _, _ => MirStepNode.fail .ub

/--
Bit pattern of `n` little-endian bytes all equal to `byte % 256` (the value of a
`T`-sized memory region after `write_bytes(dst, byte, 1)`).

Reference (`core::ptr::write_bytes` documentation, `library/core/src/ptr/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L646-L650>

> "/// Sets `count * size_of::<T>()` bytes of memory starting at `dst` to
> /// `val`.
> ///
> /// `write_bytes` is similar to C's [`memset`], but sets `count *
> /// size_of::<T>()` bytes to `val`."
-/
def writeBytesFillBits (byte : Nat) : Nat → Nat
  | .zero => 0
  | .succ n => Nat.add (Nat.mod byte 256) (Nat.mul 256 (writeBytesFillBits byte n))

/--
Outcome of the machine-state-independent part of a
`write_bytes::<T>(dst, val, count)` call (`writeBytesAction`), consumed by
`evalWriteBytesCall`: a fault (`.fault kind`; `FailureKind.unsupported` is the
fail-closed `MirStepNode.unsupported`), no memory effect (`.noWrite`, when
`count * size_of::<T>() = 0`), or a store of the whole element value `newVal`
at the destination sub-place `dstPlace` (`.store`).

Reference (`core::ptr::write_bytes` documentation, `library/core/src/ptr/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L646-L650>

> "/// Sets `count * size_of::<T>()` bytes of memory starting at `dst` to
> /// `val`."
-/
inductive WriteBytesAction : Type where
  /-- The call faults with `kind` (`.unsupported` when the shape is not modeled). -/
  | fault (kind : FailureKind) : WriteBytesAction
  /-- Zero bytes are written: memory is unchanged. -/
  | noWrite : WriteBytesAction
  /-- Store `newVal` (one whole `T` element) at `dstPlace`, the sub-place of
  local `dstTargetLocal` that the Tree Borrows tag `dstTag` points to. -/
  | store (dstPlace : Place) (dstTargetLocal : LocalIdx) (dstTag : Nat) (newVal : Value) :
      WriteBytesAction

/--
Address-level alignment of the destination of a `write_bytes::<T>` call whose
`dst` pointer `dstPtr` carries the active-frame Tree Borrows entry `dstEntry`:
whether the address `addr(dstEntry.targetLocal, dstEntry.targetProjection) +
dstPtr.offsetBytes` is a multiple of `elemAlign = align_of::<T>()` in every
valid placement of the target local, checked by `checkTargetPlaceAlignWalk`
(the walk used for dereferences, `checkTargetPlaceAlign`) from the target
local's declared type in `bodyLocalDecls`.

The type of the target place alone does not determine this: a field of a
`#[repr(packed)]` / `#[repr(packed(N))]` struct can sit at an offset that is not
a multiple of its type's alignment, so `&raw mut packed.field` is a misaligned
pointer even though the field's type is aligned. Every enclosing container
whose exact alignment (`tyExactByteAlign?`) is below `elemAlign` makes the
address possibly misaligned, and so does an exact byte offset that is not a
multiple of `elemAlign`.

An element alignment of at most `1` is always satisfied. A target local
without a declaration skips the check, as in `checkTargetPlaceAlign`
(unreachable from `writeBytesAction`, which first resolves the target place's
type through that declaration).

Reference (The Rust Reference, "The alignment modifiers"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#the-alignment-modifiers>

> "The align and packed modifiers can be used to respectively raise or lower
> the alignment of structs and unions. packed may also alter the padding
> between fields (although it will not alter the padding inside of any
> field)."

> "The alignments of each field, for the purpose of positioning fields, is the
> smaller of the specified alignment and the alignment of the field’s type."

> "References to unaligned fields are not allowed because it is undefined
> behavior."

Reference (`core::ptr::write_bytes` documentation, `library/core/src/ptr/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L656-L666>

> "/// * `dst` must be properly aligned."
-/
def writeBytesDstAddrAligned
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (dstEntry : BorrowEntry)
    (dstPtr : ProvenancePtr)
    (elemAlign : Nat) :
    Bool :=
  match Nat.ble elemAlign 1, get? bodyLocalDecls dstEntry.targetLocal with
  | true, _ => true
  | false, .some rootDecl =>
    checkTargetPlaceAlignWalk
      bodyLocalDecls
      bodyLayouts
      elemAlign
      dstPtr.offsetBytes
      (.some rootDecl.ty)
      .none
      .none
      dstEntry.targetProjection
  | false, .none => true

/--
Validate a direct call `write_bytes::<T>(dst, val, count)` whose arguments
evaluated to `argVals`, against the Tree Borrows `borrows` and the active frame
depth `frameDepth`. The element type `T` is the single type argument in
`target.typeArgs`, or else the pointee type of the `dst` operand.

Checks, in order:
1. `dst` is a thin pointer of the target width, `val` is a `u8` scalar, and
   `count` is a `usize` scalar; otherwise `.ub` (malformed arguments).
2. `T` must be known (else unsupported) with a known size and alignment;
   otherwise an unsized `T` is `.ub` and any other unresolved layout is
   unsupported (as `intrinsicUnresolvedLayoutStep`).
3. `count * size_of::<T>() <= isize::MAX`, else `.ub`: no allocation is valid
   for writes of more bytes.
4. `dst` must carry a Tree Borrows tag of the active frame whose permission
   allows writes (`.frozen` / `.disabled` are `.ub`); an untracked pointer or a
   caller-frame target is unsupported (alignment and validity unknown).
5. Alignment: the tag's target place must have an alignment that is a multiple
   of `align_of::<T>()` (else unsupported); `dst`'s byte offset must be a
   multiple of `align_of::<T>()` and the address it denotes must be aligned
   at the address level (`writeBytesDstAddrAligned`, which rejects pointers to
   misaligned fields of `#[repr(packed)]` structs), else `.ub` (misaligned),
   even when no byte is written.
6. Zero bytes (`count * size_of::<T>() = 0`) leave memory unchanged
   (`.noWrite`): every non-null pointer is valid for a zero-sized write.
7. A write whose destination is a whole local (an allocation of its own) and
   that extends past the end of that local is `.ub`: the pointer is not
   dereferenceable for `count * size_of::<T>()` bytes.
8. One element (`count = 1`) at offset `0` of a place of type `T`, where `T` is
   a primitive scalar type and the filled value `writeBytesFillBits val
   (size_of::<T>())` satisfies `validateValueForTy?` for `T`, stores that scalar
   (`.store`). When `T` is `bool` or `char` and the repeated byte pattern is not
   a valid bit representation of `T` (e.g. `2` in a `bool` or `0xFF` repeated in
   a `char`), `write_bytes` itself is not immediate UB in Rust unless the bytes
   are subsequently read at type `T`, whereas Anneal's non-union local slots
   store typed `Value`s without re-validating root locals on `Operand.copy`;
   `writeBytesAction` therefore fails closed with `.fault .unsupported` rather
   than either misreporting immediate `.ub` or storing an unvalidated typed
   scalar.
9. Every other shape (multi-element writes, aggregate `T`, interior offsets,
   bit-invalid `bool`/`char` fills, and writes past the end of a sub-place) is
   unsupported.

Reference (`core::ptr::write_bytes` documentation, `library/core/src/ptr/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L656-L666>

> "/// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `dst` must be [valid] for writes of `count * size_of::<T>()` bytes.
> ///
> /// * `dst` must be properly aligned.
> ///
> /// Note that even if the effectively copied size (`count * size_of::<T>()`) is
> /// `0`, the pointer must be properly aligned.
> ///
> /// Additionally, note that changing `*dst` in this way can easily lead to undefined behavior (UB)
> /// later if the written bytes are not a valid representation of some `T`."

Reference (The Rust Reference, "Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."

> "- A bool value must be false (0) or true (1)."

> "- A char value must not be a surrogate (i.e., must not be in the range
> 0xD800..=0xDFFF) and must be equal to or less than char::MAX."

Reference (`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L19-L25>

> "//! * For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes.
> //!   The following points are only concerned with non-zero-sized accesses.
> //! * For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that
> //!   the pointer be *dereferenceable*. The [provenance] of the pointer is used to determine which
> //!   [allocation] it is derived from; a pointer is dereferenceable if the memory range of the given
> //!   size starting at the pointer is entirely contained within the bounds of that allocation. Note
> //!   that in Rust, every (stack-allocated) variable is considered a separate allocation."

Reference (The Rust Reference, "Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "A value of alignment n must only be stored at an address that is a multiple
> of n."
-/
def writeBytesAction
    (borrows : List BorrowEntry)
    (frameDepth : Nat)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value) :
    WriteBytesAction :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | .ptr dstPtr dstSz :: .scalar valSc :: .scalar countSc :: .nil =>
    match
      Bool.and (Nat.beq dstSz ptrBytes)
        (Bool.and (Nat.beq valSc.sizeBytes 1)
          (Bool.and (Nat.blt valSc.bits 256) (Nat.beq countSc.sizeBytes ptrBytes)))
    with
    | false => .fault .ub
    | true =>
      let elemTyOpt : Option RigidTy :=
        match target.typeArgs with
        | elemTy :: .nil => .some elemTy
        | .nil =>
          match argOps with
          | dstOp :: _ =>
            match operandPointeeTy bodyLocalDecls bodyLayouts dstOp with
            | .some pt => .some pt.kind
            | .none => .none
          | .nil => .none
        | _ :: _ :: _ => .none
      match elemTyOpt with
      | .none => .fault .unsupported
      | .some elemTy =>
        match
          intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy,
          intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy
        with
        | .some elemSize, .some elemAlign =>
          let byteCount := Nat.mul countSc.bits elemSize
          match Nat.ble byteCount (Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1) with
          | false => .fault .ub
          | true =>
            match lookupBorrow borrows dstPtr.tag with
            | .none => .fault .unsupported
            | .some dstEntry =>
              match dstEntry.perm with
              | .frozen => .fault .ub
              | .disabled => .fault .ub
              | _ =>
                match Nat.beq dstEntry.targetFrameDepth frameDepth with
                | false => .fault .unsupported
                | true =>
                  let dstPlace : Place :=
                    { local_ := dstEntry.targetLocal, projection := dstEntry.targetProjection }
                  match placeTyResolved bodyLocalDecls bodyLayouts dstPlace with
                  | .none => .fault .unsupported
                  | .some dstPlaceTy =>
                    match intrinsicRigidTyAlign bodyLocalDecls bodyLayouts dstPlaceTy.kind with
                    | .none => .fault .unsupported
                    | .some placeAlign =>
                      match
                        Bool.and (Bool.not (Nat.beq elemAlign 0))
                          (Nat.beq (Nat.mod placeAlign elemAlign) 0)
                      with
                      | false => .fault .unsupported
                      | true =>
                        match Nat.beq (Nat.mod dstPtr.offsetBytes elemAlign) 0 with
                        | false => .fault .ub
                        | true =>
                          match
                            writeBytesDstAddrAligned bodyLocalDecls bodyLayouts dstEntry dstPtr
                              elemAlign
                          with
                          | false => .fault .ub
                          | true =>
                            match Nat.beq byteCount 0 with
                            | true => .noWrite
                            | false =>
                              let rootOutOfBounds : Bool :=
                                match dstEntry.targetProjection with
                                | .nil =>
                                  match
                                    intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts
                                      dstPlaceTy.kind
                                  with
                                  | .some placeSize =>
                                    Nat.blt placeSize (Nat.add dstPtr.offsetBytes byteCount)
                                  | .none => false
                                | _ :: _ => false
                              match rootOutOfBounds with
                              | true => .fault .ub
                              | false =>
                                match
                                  Bool.and (Nat.beq countSc.bits 1)
                                    (Bool.and (Nat.beq dstPtr.offsetBytes 0)
                                      (Bool.and (rigidTyEq dstPlaceTy.kind elemTy)
                                        (isPrimitiveScalarKind elemTy)))
                                with
                                | true =>
                                  let fillVal : Value :=
                                    .scalar ⟨writeBytesFillBits valSc.bits elemSize, elemSize⟩
                                  match
                                    validateValueForTy? bodyLayouts (.some dstPlaceTy) fillVal
                                  with
                                  | true =>
                                    .store dstPlace dstEntry.targetLocal dstPtr.tag fillVal
                                  | false => .fault .unsupported
                                | false => .fault .unsupported
        | _, _ =>
          match isUnsizedRigidTy 8 elemTy with
          | true => .fault .ub
          | false => .fault .unsupported
  | _ => .fault .ub

/--
Tree Borrows write check and permission transition for a non-zero `write_bytes`
store to `(dstTag, dstEntry)` in `Runtime(PostCleanup)` MIR (Rust 1.98.0, paired
with Anneal's Tree Borrows aliasing model; mirrors the write phase of
`Statements.borrowsAfterCopySingleDirect`):
1. Rejects `.frozen`, `.disabled`, and protected conflicted two-phase
   reservations (`.reservedFrz true` with `isBorrowProtected activeProtectors
   dstEntry = true`).
2. Checks ancestor child-write permissions across multi-tag borrow trees
   (`treeBorrowAncestorsChildAccessUB .write`), rejecting writes through tags
   reborrowed from `.frozen` or `.disabled` ancestors.
3. Checks active function-entry lifetime protectors on overlapping foreign
   borrows (`hasProtectedTreeWriteConflict` / `hasProtectedWriteConflict`),
   rejecting writes that would disable a protected borrow (`noalias` violation).
4. Applies the projection- and byte-range-aware Tree Borrows write transition
   (`invalidateTreeBorrowsAtProj` / `invalidateConflictingBorrowsAtProj` /
   `invalidateConflictingBorrows`), activating two-phase reservations on the
   written tag and disabling overlapping foreign borrows without clobbering
   disjoint sibling sub-place borrows.
Returns `.none` on any Tree Borrows undefined behavior.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/perms.rs` and `tree.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/perms.rs#L179-L198>
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/tree.rs#L157-L159>

> "ReservedFrz { conflicted: true } if protected => return None,
> ReservedFrz { .. } | ReservedIM | Unique => Unique,
> Frozen | Disabled => return None,"

> "if protected && self.accessed && transition.produces_disabled() {
>     return Err(TransitionError::ProtectedDisabled(old_perm));
> }"
-/
def borrowsAfterWriteBytes
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (dstTag : Nat)
    (dstEntry : BorrowEntry) :
    Option (List BorrowEntry) :=
  let childWriteUB : Bool :=
    match dstEntry.perm with
    | .frozen | .disabled => true
    | .reservedFrz true => isBorrowProtected activeProtectors dstEntry
    | _ => false
  match childWriteUB with
  | true => .none
  | false =>
    let ancWriteUB : Bool :=
      match borrows with
      | _ :: _ :: _ =>
        treeBorrowAncestorsChildAccessUB .write borrows dstEntry.parentTag
      | _ => false
    match ancWriteUB with
    | true => .none
    | false =>
      let protConflict : Bool :=
        match activeProtectors with
        | .nil => false
        | _ :: _ =>
          match borrows with
          | b₁ :: b₂ :: restBorrows =>
            let allBorrows := b₁ :: b₂ :: restBorrows
            hasProtectedTreeWriteConflict
              allBorrows
              allBorrows
              activeProtectors
              dstEntry.targetLocal
              (.some dstTag)
              dstEntry.targetProjection
              dstEntry.rangeOffset
              dstEntry.rangeLen
              dstEntry.targetFrameDepth
          | _ =>
            hasProtectedWriteConflict
              borrows
              activeProtectors
              dstEntry.targetLocal
              (.some dstTag)
              dstEntry.targetProjection
              dstEntry.rangeOffset
              dstEntry.rangeLen
              dstEntry.targetFrameDepth
      match protConflict with
      | true => .none
      | false =>
        let borrows' : List BorrowEntry :=
          match borrows with
          | .nil => .nil
          | single :: .nil =>
            let b := single :: .nil
            match dstEntry.targetProjection with
            | .nil =>
              match Nat.beq dstEntry.rangeLen 0 with
              | true =>
                invalidateConflictingBorrows
                  b
                  dstEntry.targetLocal
                  (.some dstTag)
                  dstEntry.targetFrameDepth
              | false =>
                invalidateConflictingBorrowsAtProj
                  b
                  dstEntry.targetLocal
                  (.some dstTag)
                  .nil
                  dstEntry.rangeOffset
                  dstEntry.rangeLen
                  dstEntry.targetFrameDepth
            | pHead :: pTail =>
              invalidateConflictingBorrowsAtProj
                b
                dstEntry.targetLocal
                (.some dstTag)
                (pHead :: pTail)
                dstEntry.rangeOffset
                dstEntry.rangeLen
                dstEntry.targetFrameDepth
          | b₁ :: b₂ :: restBorrows =>
            let allBorrows := b₁ :: b₂ :: restBorrows
            invalidateTreeBorrowsAtProj
              allBorrows
              allBorrows
              dstEntry.targetLocal
              (.some dstTag)
              dstEntry.targetProjection
              dstEntry.rangeOffset
              dstEntry.rangeLen
              dstEntry.targetFrameDepth
        .some borrows'

/--
Commit a non-zero single-element `write_bytes` store of `newVal` to `dstPlace`
through Tree Borrows tag `dstTag` in active-frame `locals₃`: runs the Tree
Borrows ancestor, active-protector, and sub-place invalidation transition
(`borrowsAfterWriteBytes`), writes `newVal` to `dstPlace` (`writePlaceValue`),
and advances `s` (`advanceStmt`). Missing borrow entries fail closed with
`MirStepNode.unsupported`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def commitWriteBytesDstPlaceWrite
    (s : MachineState)
    (dstPlace : Place)
    (dstTag : Nat)
    (locals₃ : List LocalSlot)
    (newVal : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match lookupBorrow s.memory.borrows dstTag with
  | .none => MirStepNode.unsupported
  | .some dstEntry =>
    match
      borrowsAfterWriteBytes
        s.memory.borrows
        s.memory.activeProtectors
        dstTag
        dstEntry
    with
    | .none => MirStepNode.fail .ub
    | .some borrows' =>
      match
        writePlaceValue
          locals₃
          s.memory.borrows
          dstPlace
          newVal
          localDecls
          layouts
      with
      | .ok locals₄ =>
        MirStepNode.step
          (advanceStmt
            s
            locals₄
            { s.memory with borrows := borrows' })
      | .unsupported => MirStepNode.unsupported
      | .ub => MirStepNode.fail .ub

/--
Evaluate a direct call `write_bytes::<T>(dst, val, count)` whose argument
operands `argOps` evaluated to `argVals` (with frame `locals'`): validate it
against the current Tree Borrows state and active frame (`writeBytesAction`),
then fault, leave memory unchanged, or store the filled element at the
destination sub-place through `commitWriteBytesDstPlaceWrite` (enforcing Tree
Borrows ancestor permissions, active function-entry protectors, and sub-place
borrow invalidation). The call then writes `()` to `destination` and continues
at `targetBb` (`writeIntrinsicReturn`, `finishMemIntrinsicCall`).

Reference (`core::ptr::write_bytes` documentation, `library/core/src/ptr/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L646-L650>

> "/// Sets `count * size_of::<T>()` bytes of memory starting at `dst` to
> /// `val`.
> ///
> /// `write_bytes` is similar to C's [`memset`], but sets `count *
> /// size_of::<T>()` bytes to `val`."
-/
def evalWriteBytesCall
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
  match
    writeBytesAction
      s.memory.borrows
      (length s.memory.callStack)
      target
      bodyLocalDecls
      bodyLayouts
      argOps
      argVals
  with
  | .fault kind => MirStepNode.fail kind
  | .noWrite => writeIntrinsicReturn s locals' destination targetBb .unit
  | .store dstPlace _ dstTag newVal =>
    finishMemIntrinsicCall
      s
      (commitWriteBytesDstPlaceWrite
        s
        dstPlace
        dstTag
        locals'
        newVal
        bodyLocalDecls
        bodyLayouts)
      destination
      targetBb

/--
Dispatch a direct (`target.isIndirect = false`) call to a
`CallConv.rustIntrinsic` compiler intrinsic in `evalTerminator` when
`classifyRustIntrinsic? target.defPath` returns `.some kind`: the runtime
dispatch of `const_eval_select`, the call-form memory intrinsics
(`evalCopyNonOverlappingCall`, `evalWriteBytesCall`), or a value-returning
intrinsic (`evalNonSelectIntrinsicCall`).

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
         let tupleTyOpt :=
           match target.typeArgs with
           | firstTy :: _ => .some firstTy
           | .nil => .none
         match unpackConstEvalSelectArgs? tupleArgVal tupleTyOpt with
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
             match lookupCallee s.memory.callees bodyLayouts rtTarget.defPath rtTarget.typeArgs s.memory.traitImpls with
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
                   { defPath := rtTarget.defPath, typeArgs := rtTarget.typeArgs, args := unpackedArgs, memory := s.memory }
                   (resumeExternalCall s locals' destination targetBb unwind)
               | false =>
                 let selectArgOps := constEvalSelectTupleArgOps tupleTyOpt
                 match isDirectExactDivTarget rtTarget with
                 | true =>
                   match unpackedArgs with
                   | .scalar lhs :: .scalar rhs :: .nil =>
                     let rtTarget' :=
                       withConstEvalSelectIntrinsicTypeArgs rtTarget tupleTyOpt false
                     match resolveIntrinsicIsSigned rtTarget' bodyLocalDecls bodyLayouts selectArgOps with
                     | .none => MirStepNode.unsupported
                     | .some isSigned =>
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
                     let rtTarget' :=
                       withConstEvalSelectIntrinsicTypeArgs
                         rtTarget
                         tupleTyOpt
                         (isPtrPointeeIntrinsicKind rtKind)
                     evalNonSelectIntrinsicCall
                       rtKind
                       s
                       rtTarget'
                       bodyLocalDecls
                       bodyLayouts
                       selectArgOps
                       unpackedArgs
                       locals'
                       destination
                       targetBb
                   | .none =>
                     match isUnreachableCallTarget rtTarget.defPath with
                     | true => MirStepNode.fail .ub
                     | false =>
                       match isAbortingPanicDefPath rtTarget.defPath with
                       | true => MirStepNode.retOutcome .abort
                       | false =>
                         match isUnwindingPanicDefPath rtTarget.defPath with
                         | true =>
                           match applyUnwindAction s locals' s.memory unwind with
                           | .running nextState => MirStepNode.step nextState
                           | .halted out => MirStepNode.retOutcome out
                           | .faulted fk => MirStepNode.fail fk
                         | false =>
                           MirStepNode.extCall
                             { defPath := rtTarget.defPath, typeArgs := rtTarget.typeArgs, args := unpackedArgs, memory := s.memory }
                             (resumeExternalCall s locals' destination targetBb unwind)
       | _ => MirStepNode.fail .ub)
  | .some .copyNonOverlapping =>
    .some
      (evalCopyNonOverlappingCall
        s
        bodyLocalDecls
        bodyLayouts
        argOps
        argVals
        locals'
        destination
        targetBb)
  | .some .writeBytes =>
    .some
      (evalWriteBytesCall
        s
        target
        bodyLocalDecls
        bodyLayouts
        argOps
        argVals
        locals'
        destination
        targetBb)
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
      match
        evalOperandsWithBodyCast
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          bodyLocalDecls
          s.memory.callStack
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
                (pushDivergingCalleeFrame
                  s
                  callerBody
                  locals'
                  destination
                  unwind
                  calleeBody
                  argVals)
        | .none =>
          match resolvedTarget.isIndirect with
          | false =>
            match isUnreachableCallTarget resolvedTarget.defPath with
            | true => MirStepNode.fail .ub
            | false =>
              match isAbortingPanicDefPath resolvedTarget.defPath with
              | true => MirStepNode.retOutcome .abort
              | false =>
                match isUnwindingPanicDefPath resolvedTarget.defPath with
                | true =>
                  match applyUnwindAction s locals' s.memory unwind with
                  | .running nextState => MirStepNode.step nextState
                  | .halted out => MirStepNode.retOutcome out
                  | .faulted fk => MirStepNode.fail fk
                | false =>
                  MirStepNode.extCall
                    { defPath := resolvedTarget.defPath, typeArgs := resolvedTarget.typeArgs, args := argVals, memory := s.memory }
                    (resumeExternalDivergingCall s locals' unwind)
          | true =>
            MirStepNode.extCall
              { defPath := resolvedTarget.defPath, typeArgs := resolvedTarget.typeArgs, args := argVals, memory := s.memory }
              (resumeExternalDivergingCall s locals' unwind)
    | .some targetBb =>
      match
        evalOperandsWithBodyCast
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          bodyLocalDecls
          s.memory.callStack
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
                  argVals
                  unwind)
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
              match evalExactDiv lhs rhs isSigned with
              | .some retScalar =>
                writeIntrinsicReturn s locals' destination targetBb (.scalar retScalar)
              | .none => MirStepNode.fail .ub
            | _ => MirStepNode.unsupported
          | false =>
            MirStepNode.extCall
              { defPath := resolvedTarget.defPath, typeArgs := resolvedTarget.typeArgs, args := argVals, memory := s.memory }
              (resumeExternalCall s locals' destination targetBb unwind)

/--
Evaluate a `TerminatorKind.tailCall` terminator, resolving direct or indirect
function targets and polymorphic/trait-method callees via `lookupCallee`.

- Function and argument operands are evaluated by `evalOperandWithBodyCast` /
  `evalOperandsWithBodyCast` (`DIV-TR-OPAQUECAST-ROOT-DISPATCH`).
- For an in-table callee entered from the modular root
  (`s.memory.callStack = .nil`), the caller-owned referents of the root frame
  are relocated past the callee's frame before it is entered
  (`tailCalleeEntryMemory`, i.e.
  `relocateRootCallerReferents memAfterTeardown nLocals (length (initLocals calleeBody argVals))`,
  `DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`); inside an inline callee frame
  no relocation is needed.
- `enterTailCalleeFrame` narrows the inherited unwind action for a callee that
  cannot unwind (`DIV-LM-TAILCALL-NOUNWIND-UNWIND`).
- An external (out-of-table) callee is resumed by
  `resumeExternalTailCallWithAbi` with the tail-calling state's root unwind
  ceiling and the callee's unwind capability (`externalTargetCanUnwind`).

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Calling a function with the wrong call ABI, or unwinding past a stack frame
> that does not allow unwinding (e.g. by calling a "C-unwind" function imported
> or transmuted as a "C" function or function pointer)."

Reference (The Rust Reference 1.98.0, "Pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

> "Shared references point to memory which is owned by some other value."
> "Mutable references point to memory which is owned by some other value."

Justification: see `relocateRootCallerReferents`, `enterTailCalleeFrame`, and
`resumeExternalTailCallWithAbi`. The frame teardown (`disableFrameBorrows`) runs
first, so only borrows of memory owned outside the popped frame are relocated.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L823-L839>

> "/// Tail call.
> ///
> /// Roughly speaking this is a chimera of [`Call`] and [`Return`], with some caveats.
> ...
> TailCall {"
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
      evalOperandsWithBodyCast
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        bodyLocalDecls
        s.memory.callStack
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok argVals _ =>
      let depth := length s.memory.callStack
      let nLocals := length s.frame.locals
      match
        hasFrameDeallocProtectorConflict
          s.memory.borrows
          s.memory.activeProtectors
          depth
          nLocals
      with
      | true => MirStepNode.fail .ub
      | false =>
        let memAfterTeardown : Memory :=
          { s.memory with borrows := disableFrameBorrows s.memory.borrows depth nLocals }
        match lookupCallee s.memory.callees bodyLayouts target.defPath target.typeArgs s.memory.traitImpls with
        | .some calleeBody =>
          match checkCalleeTargetCompatible target calleeBody (length argVals) with
          | false => MirStepNode.fail .ub
          | true =>
            MirStepNode.step
              (enterTailCalleeFrame
                (tailCalleeEntryMemory
                  s.memory.callStack
                  memAfterTeardown
                  nLocals
                  (length (initLocals calleeBody argVals)))
                calleeBody
                argVals)
        | .none =>
          MirStepNode.extCall
            { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals,
              memory := memAfterTeardown }
            (resumeExternalTailCallWithAbi
              s.memory.rootUnwindCeiling
              (externalTargetCanUnwind target (operandTy bodyLocalDecls bodyLayouts func)))

/--
Evaluate basic-block `Terminator` `term` in `s`, producing the next
`MirStepNode` transition.

Opaque-cast root dispatch (`DIV-TR-OPAQUECAST-ROOT-DISPATCH`): the
`TerminatorKind.switchInt` discriminant, the `TerminatorKind.assert` condition,
and `TerminatorKind.call` / `TerminatorKind.tailCall` function and argument
operands are evaluated by `evalOperandWithBodyCast` / `evalOperandsWithBodyCast`
(a moved pure `ProjectionElem.opaqueCast` chain de-initializes its local and is
validated against the cast type; every other operand evaluates as before), and
`TerminatorKind.drop` of a pure cast chain `(_l as T)` takes the whole-local arm
(`stripLeadingOpaqueCast place.projection = .nil`). A cast chain followed by
further projections takes the projected arm unchanged.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1148-L1150>

> "///  - [`OpaqueCast`](ProjectionElem::OpaqueCast): This projection changes the place's type to the
> ///    given one, and makes no other changes. A `OpaqueCast` projection on any type other than an
> ///    opaque type from the current crate is not well-formed."

Justification: the cast "changes the place's type to the given one, and makes no
other changes", so a terminator addressing `(_l as T)` addresses the whole
local `_l`.

- `TerminatorKind.return_`: fails closed with `MirStepNode.fail .ub` whenever
  `_0` is `.dead`, `.uninit`, or `.init retVal` with
  `valueContainsUninit retVal = true` (rejecting both leaf `.uninit` and
  partially initialized aggregates containing `.uninit`).
- `TerminatorKind.drop`: enforces live storage (`LocalSlot.dead` -> `.ub`),
  marks bare `place.projection = .nil` locals `.uninit`, and deinitializes
  projected `place.projection = proj :: rest` sub-places to `Value.uninit` via
  `deinitProjectedForLocal` (or `deinitTailOk` when the root local is already
  live `.uninit`), rejecting projected drops through initialized unions with
  `.unsupported`.

Modeling note (`agent_docs/trusted-rust.md`): After drop elaboration on types
without custom drop glue (or in lowered MIR), `TerminatorKind.drop` marks the
dropped place uninitialized in our operational model (matching `StatementKind.deinit`
and `Anneal.Mir.AdtAndControl.evalLoweredTerminator`), whereas `rustc` `14210df0e`
treats post-elaboration `Drop` on types without drop glue as a runtime nop.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution are “valid”, and producing an invalid value is hence immediate UB."
>
> "- A `struct`, tuple, and array requires all fields/elements to be valid at their respective type."
>
> "Note: Uninitialized memory is also implicitly invalid for any type that has a restricted set of valid values. In other words, the only cases in which reading uninitialized memory is permitted are inside `union`s and in “padding” (the gaps between the fields of a type)."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L724-L800>

> "/// Returns from the function.
> ...
> Return,
> ...
> /// After drop elaboration: `Drop` terminators are a complete nop for types that have no drop
> /// glue. For other types, `Drop` terminators behave exactly like a call to
> /// `core::mem::drop_glue` with a reference to the given place.
> ...
> Drop {
>     place: Place<'tcx>,
>     target: BasicBlock,
>     unwind: UnwindAction,
>     replace: bool,
>     /// Cleanup to be done if the coroutine is dropped at this suspend point (for async drop).
>     drop: Option<BasicBlock>,
>     /// Prepared async future local (for async drop)
>     async_fut: Option<Local>,
> },
> ...
> /// Roughly speaking, evaluates the `func` operand and the arguments, and starts execution of
> /// the referred to function.
> ...
> Call {"
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
      evalOperandWithBodyCast
        s.frame.locals
        discr
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        (bodyLocalDeclsOf currentBody)
        s.memory.callStack
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
      let depth := length s.memory.callStack
      let nLocals := length s.frame.locals
      match
        hasFrameDeallocProtectorConflict
          s.memory.borrows
          s.memory.activeProtectors
          depth
          nLocals
      with
      | true => MirStepNode.fail .ub
      | false =>
        let borrows₁ := disableFrameBorrows s.memory.borrows depth nLocals
        match s.memory.callStack with
        | .nil =>
          match valueContainsUninit retVal with
          | true => MirStepNode.fail .ub
          | false => MirStepNode.retNormal retVal { s.memory with borrows := borrows₁ }
        | caller :: restStack =>
          match caller.isDiverging with
          | true => MirStepNode.fail .ub
          | false =>
            match valueContainsUninit retVal with
            | true => MirStepNode.fail .ub
            | false =>
              let restoredProtectors := restoreCallerProtectors caller
              let callerMem : Memory := {
                s.memory with
                borrows := borrows₁
                callStack := restStack
                activeCallee := .some caller.callerBody
                activeProtectors := restoredProtectors
              }
              match
                writeReturnDestination
                  caller.frame.locals
                  callerMem
                  caller.destination
                  retVal
                  caller.callerBody.localDecls
                  caller.callerBody.layouts
              with
              | .ok updatedCallerLocals mem' =>
                MirStepNode.step {
                  frame := {
                    caller.frame with
                    blockIdx := caller.returnTarget
                    stmtIdx := 0
                    locals := updatedCallerLocals
                  }
                  memory := mem'
                }
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .unreachable => MirStepNode.fail .ub
  | .drop place target _ =>
    let bodyLocalDecls := bodyLocalDeclsOf currentBody
    let bodyLayouts : LayoutTable :=
      match currentBody with
      | .some b => b.layouts
      | .none => emptyLayoutTable
    let depth := length s.memory.callStack
    match get? s.frame.locals place.local_ with
    | .none => MirStepNode.fail .ub
    | .some .dead => MirStepNode.fail .ub
    | .some slot =>
      match place.projection, stripLeadingOpaqueCast place.projection with
      | .nil, _ =>
        match set? s.frame.locals place.local_ .uninit with
        | .some locals' =>
          match s.memory.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrows s.memory.borrows place.local_ .none depth
            MirStepNode.step {
              s with
              frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
              memory := { s.memory with borrows := borrows' }
            }
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                s.memory.borrows
                (protHead :: protTail)
                place.local_
                .none
                .nil
                0
                0
                depth
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrows s.memory.borrows place.local_ .none depth
              MirStepNode.step {
                s with
                frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
                memory := { s.memory with borrows := borrows' }
              }
        | .none => MirStepNode.fail .ub
      | .opaqueCast _ :: _, .nil =>
        match set? s.frame.locals place.local_ .uninit with
        | .some locals' =>
          match s.memory.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrows s.memory.borrows place.local_ .none depth
            MirStepNode.step {
              s with
              frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
              memory := { s.memory with borrows := borrows' }
            }
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                s.memory.borrows
                (protHead :: protTail)
                place.local_
                .none
                .nil
                0
                0
                depth
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrows s.memory.borrows place.local_ .none depth
              MirStepNode.step {
                s with
                frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
                memory := { s.memory with borrows := borrows' }
              }
        | .none => MirStepNode.fail .ub
      | proj :: rest, _ =>
        let resolvedLocalProj :=
          resolveBorrowWriteLocalProj
            bodyLocalDecls
            bodyLayouts
            s.frame.locals
            place.local_
            (proj :: rest)
        match slot with
        | .init rootVal =>
          match
            deinitProjectedForLocal
              s.frame.locals
              bodyLocalDecls
              bodyLayouts
              place.local_
              rootVal
              (proj :: rest)
          with
          | .ok rootVal' =>
            match set? s.frame.locals place.local_ (.init rootVal') with
            | .some locals' =>
              match s.memory.activeProtectors with
              | .nil =>
                let borrows' :=
                  invalidateConflictingBorrowsAtProj
                    s.memory.borrows
                    place.local_
                    .none
                    resolvedLocalProj
                    0
                    0
                    depth
                MirStepNode.step {
                  s with
                  frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
                  memory := { s.memory with borrows := borrows' }
                }
              | protHead :: protTail =>
                match
                  hasProtectedWriteConflict
                    s.memory.borrows
                    (protHead :: protTail)
                    place.local_
                    .none
                    resolvedLocalProj
                    0
                    0
                    depth
                with
                | true => MirStepNode.fail .ub
                | false =>
                  let borrows' :=
                    invalidateConflictingBorrowsAtProj
                      s.memory.borrows
                      place.local_
                      .none
                      resolvedLocalProj
                      0
                      0
                      depth
                  MirStepNode.step {
                    s with
                    frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
                    memory := { s.memory with borrows := borrows' }
                  }
            | .none => MirStepNode.fail .ub
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
        | .uninit =>
          match
            deinitTailOk
              s.frame.locals
              bodyLocalDecls
              bodyLayouts
              (placeTy bodyLocalDecls bodyLayouts { local_ := place.local_, projection := .nil })
              (proj :: rest)
          with
          | true =>
            match s.memory.activeProtectors with
            | .nil =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  s.memory.borrows
                  place.local_
                  .none
                  resolvedLocalProj
                  0
                  0
                  depth
              MirStepNode.step {
                s with
                frame := { s.frame with blockIdx := target, stmtIdx := 0 }
                memory := { s.memory with borrows := borrows' }
              }
            | protHead :: protTail =>
              match
                hasProtectedWriteConflict
                  s.memory.borrows
                  (protHead :: protTail)
                  place.local_
                  .none
                  resolvedLocalProj
                  0
                  0
                  depth
              with
              | true => MirStepNode.fail .ub
              | false =>
                let borrows' :=
                  invalidateConflictingBorrowsAtProj
                    s.memory.borrows
                    place.local_
                    .none
                    resolvedLocalProj
                    0
                    0
                    depth
                MirStepNode.step {
                  s with
                  frame := { s.frame with blockIdx := target, stmtIdx := 0 }
                  memory := { s.memory with borrows := borrows' }
                }
          | false =>
            match projectionHasDeref (proj :: rest) with
            | true => MirStepNode.unsupported
            | false => MirStepNode.fail .ub
        | .dead => MirStepNode.fail .ub
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
        evalOperandsWithBodyCast
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          bodyLocalDecls
          s.memory.callStack
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok argVals locals' =>
        match lookupCallee s.memory.callees bodyLayouts target.defPath target.typeArgs s.memory.traitImpls with
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
              match
                resolveIntrinsicIsSigned
                  target
                  bodyLocalDecls
                  bodyLayouts
                  argOps
              with
              | .none => MirStepNode.unsupported
              | .some isSigned =>
                match evalExactDiv lhs rhs isSigned with
                | .some retScalar =>
                  writeIntrinsicReturn s locals' destination targetBb (.scalar retScalar)
                | .none => MirStepNode.fail .ub
            | _ => MirStepNode.fail .ub
          | false =>
            match target.isIndirect with
            | true =>
              MirStepNode.extCall
                { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
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
                  { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
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
        evalOperandsWithBodyCast
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          bodyLocalDecls
          s.memory.callStack
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok argVals locals' =>
        match lookupCallee s.memory.callees bodyLayouts target.defPath target.typeArgs s.memory.traitImpls with
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
          -- A diverging call to `core::intrinsics::const_eval_select` (one whose
          -- `called_at_rt` returns `!`) is not unpacked here; like any other
          -- unlinked callee it becomes an external call, which constrains
          -- nothing. Captured MIR never contains one, because `rustc` replaces
          -- every `const_eval_select` call with a direct call to `called_at_rt`
          -- before `optimized_mir` (`withConstEvalSelectIntrinsicTypeArgs`).
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
                    { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
                    (resumeExternalDivergingCall s locals' unwind)
          | true =>
            MirStepNode.extCall
              { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
              (resumeExternalDivergingCall s locals' unwind)
  | .tailCall func argOps =>
    evalTailCallTerminator s func argOps currentBody
  | .assert cond expected target unwind =>
    let bodyLayouts : LayoutTable :=
      match currentBody with
      | .some b => b.layouts
      | .none => emptyLayoutTable
    match
      evalOperandWithBodyCast
        s.frame.locals
        cond
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        (bodyLocalDeclsOf currentBody)
        s.memory.callStack
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
