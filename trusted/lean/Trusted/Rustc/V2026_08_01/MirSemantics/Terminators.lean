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
import Trusted.Rustc.V2026_08_01.MirSemantics.Statements

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
validating `retVal` against the cast type `placeTyResolved localDecls layouts dst`
when `localDecls` is non-empty. A cast chain followed by further projections
(`(_l as OpaqueTy).f`) takes the projected arm with local `dst.local_`
re-declared at the cast type (`eraseLeadingOpaqueCastDecls`, `uninitFieldWriteShell?`).

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
      | _ :: _ => validateValueForTy? layouts (placeTyResolved localDecls layouts dst) retVal
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
    let decls' :=
      eraseLeadingOpaqueCastDecls localDecls layouts dst.local_ (proj :: rest)
    let resolvedLocalProj :=
      resolveBorrowWriteLocalProj decls' layouts callerLocals dst.local_ (proj :: rest)
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
        | .some (.init rootVal) => .some (ensureNestedFieldShells rootVal (proj :: rest))
        | .some .uninit => uninitFieldWriteShell? localDecls layouts dst.local_ proj rest
        | _ => .none
      match rootOpt with
      | .none => .ub
      | .some rootVal =>
        match
          writeProjectedForLocal
            callerLocals
            decls'
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
`resumeExternalTailCallWithAbi`). By contrast, `CallConv.other "C"` unambiguously
names `ExternAbi::C { unwind: false }` (the `"C"` entry in the quoted
`extern_abi.rs` passage) and maps to `.some false`. A `-C panic=abort` build,
`#[rustc_nounwind]`, and `-Z panic-in-drop=abort` only make more callees
non-unwinding; they are outside this table and are treated as "may unwind".
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
          ("C" :: "system" :: "cdecl" :: "stdcall" :: "fastcall" :: "vectorcall" ::
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
  /-- `core::intrinsics::align_of_val` dynamic or static pointee alignment. -/
  | alignOfVal : RustIntrinsicKind
  /-- `core::intrinsics::copy_nonoverlapping` call form: copy `count` elements
  between non-overlapping regions (`evalCopyNonOverlappingCall`). -/
  | copyNonOverlapping : RustIntrinsicKind
  /-- `core::intrinsics::write_bytes` call form: set the bytes of `count`
  elements to a byte value (`evalWriteBytesCall`). -/
  | writeBytes : RustIntrinsicKind
  /-- `core::intrinsics::copy` call form: overlapping `memmove` copy of `count`
  elements (`evalCopyCall`). -/
  | copy : RustIntrinsicKind
  /-- `core::intrinsics::compare_bytes` unsigned lexicographic byte comparison
  (`evalCompareBytesCall`). -/
  | compareBytes : RustIntrinsicKind
  /-- `core::intrinsics::raw_eq` raw bytewise equality of two `&T` referents
  (`evalRawEqCall`). -/
  | rawEq : RustIntrinsicKind
  /-- `core::intrinsics::typed_swap_nonoverlapping` typed non-overlapping swap
  with validity enforcement and padding reset (`evalTypedSwapNonOverlappingCall`). -/
  | typedSwapNonOverlapping : RustIntrinsicKind
  /-- `core::intrinsics::ptr_offset_from` signed element distance within an
  allocation (`evalPtrOffsetFromCall ... false`). -/
  | ptrOffsetFrom : RustIntrinsicKind
  /-- `core::intrinsics::ptr_offset_from_unsigned` non-negative element distance
  within an allocation (`evalPtrOffsetFromCall ... true`). -/
  | ptrOffsetFromUnsigned : RustIntrinsicKind
  /-- `core::intrinsics::ptr_mask` strict-provenance pointer address masking
  (`evalPtrMaskCall`). -/
  | ptrMask : RustIntrinsicKind
  /-- `core::intrinsics::black_box` optimization-barrier identity with typed
  value validity checking (`evalBlackBoxCall`). -/
  | blackBox : RustIntrinsicKind

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
                                                  match stringEq defPath "core::intrinsics::align_of_val" with
                                                  | true => .some .alignOfVal
                                                  | false =>
                                                    match stringEq defPath "core::intrinsics::copy_nonoverlapping" with
                                                    | true => .some .copyNonOverlapping
                                                    | false =>
                                                      match stringEq defPath "core::intrinsics::write_bytes" with
                                                      | true => .some .writeBytes
                                                      | false =>
                                                        match stringEq defPath "core::intrinsics::copy" with
                                                        | true => .some .copy
                                                        | false =>
                                                          match stringEq defPath "core::intrinsics::compare_bytes" with
                                                          | true => .some .compareBytes
                                                          | false =>
                                                            match stringEq defPath "core::intrinsics::raw_eq" with
                                                            | true => .some .rawEq
                                                            | false =>
                                                              match stringEq defPath "core::intrinsics::typed_swap_nonoverlapping" with
                                                              | true => .some .typedSwapNonOverlapping
                                                              | false =>
                                                                match stringEq defPath "core::intrinsics::ptr_offset_from" with
                                                                | true => .some .ptrOffsetFrom
                                                                | false =>
                                                                  match stringEq defPath "core::intrinsics::ptr_offset_from_unsigned" with
                                                                  | true => .some .ptrOffsetFromUnsigned
                                                                  | false =>
                                                                    match stringEq defPath "core::intrinsics::ptr_mask" with
                                                                    | true => .some .ptrMask
                                                                    | false =>
                                                                      match stringEq defPath "core::intrinsics::black_box" with
                                                                      | true => .some .blackBox
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
`.constEvalSelect`) from evaluated argument values `argVals`.

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
  | .copy => MirStepNode.unsupported
  | .compareBytes => MirStepNode.unsupported
  | .rawEq => MirStepNode.unsupported
  | .typedSwapNonOverlapping => MirStepNode.unsupported
  | .ptrOffsetFrom => MirStepNode.unsupported
  | .ptrOffsetFromUnsigned => MirStepNode.unsupported
  | .ptrMask => MirStepNode.unsupported
  | .blackBox => MirStepNode.unsupported
  | .constEvalSelect => MirStepNode.fail .ub

/--
Test whether `kind` is parameterized by the pointee type `T` of its first
pointer argument (`arith_offset<T>`, `size_of_val<T>`, `align_of_val<T>`,
`copy<T>`, `raw_eq<T>`, `typed_swap_nonoverlapping<T>`, `ptr_offset_from<T>`,
`ptr_offset_from_unsigned<T>`, `ptr_mask<T>`) rather than by the value type of
its first argument.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L899-L916>

> "pub const unsafe fn arith_offset<T>(dst: *const T, offset: isize) -> *const T;"

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, signatures of the core memory and
pointer intrinsics whose generic parameter `T` is the pointee of the first
parameter):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L954>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2272-L2278>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2318>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2569>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L3039>

> "pub fn ptr_mask<T>(ptr: *const T, mask: usize) -> *const T;"
> "pub const unsafe fn ptr_offset_from<T>(ptr: *const T, base: *const T) -> isize;"
> "pub const unsafe fn ptr_offset_from_unsigned<T>(ptr: *const T, base: *const T) -> usize;"
> "pub const unsafe fn raw_eq<T>(a: &T, b: &T) -> bool;"
> "pub const unsafe fn typed_swap_nonoverlapping<T>(x: *mut T, y: *mut T) {"
> "pub const unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize);"

`compare_bytes` is not generic and `black_box<T>(dummy: T)` is generic over the
value type of its first parameter, so both return `false`:
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2337>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2345>

> "pub const unsafe fn compare_bytes(left: *const u8, right: *const u8, bytes: usize) -> i32;"
> "pub const fn black_box<T>(dummy: T) -> T;"
-/
@[reducible]
def isPtrPointeeIntrinsicKind : RustIntrinsicKind → Bool
  | .arithOffset => true
  | .sizeOfVal => true
  | .alignOfVal => true
  | .copy => true
  | .rawEq => true
  | .typedSwapNonOverlapping => true
  | .ptrOffsetFrom => true
  | .ptrOffsetFromUnsigned => true
  | .ptrMask => true
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

/-!
## Eight Core Memory and Pointer Intrinsics

Ground operational semantics for `core::intrinsics::{copy, compare_bytes,
raw_eq, typed_swap_nonoverlapping, ptr_offset_from, ptr_offset_from_unsigned,
ptr_mask, black_box}`, matching `rustc 1.98.0-nightly (14210df0e 2026-05-31)`
and the Rust Reference 1.98.0.
-/

/--
Layout- and protector-aware return-value destination write for inline compiler
intrinsics:
- A diverging call (`targetOpt = .none`) to a returning intrinsic faults with
  `MirStepNode.fail .ub` once the intrinsic itself has completed without
  faulting or hitting `.unsupported`.
- On `targetOpt = .some targetBb`, validates `retVal` against `destination`'s
  declared type for bare whole-local writes (`destination.projection = .nil`
  when `bodyLocalDecls` is non-empty) and delegates to `writeReturnDestination`,
  giving exact parity with normal `TerminatorKind.return_` call-return writes:
  `.deref` writes with `bodyLocalDecls`/`bodyLayouts`, `derefWriteTreeUB`,
  `derefWriteUnionProtectorUB`, `invalidateDerefWriteBorrowsWithLayouts`, and
  `foreignFrameDerefWrite`; pure `.opaqueCast` whole-local writes; and
  projected direct writes including field-by-field initialization of `.uninit`
  locals (`uninitFieldWriteShell?`), nested field shells,
  `eraseLeadingOpaqueCastDecls`, `hasProtectedWriteConflict`, and
  union-truncated `resolveBorrowWriteLocalProj` borrow invalidation.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L800-L814>

> "Call {
> ...
>     destination: Place<'tcx>,
> ...
>     target: Option<BasicBlock>,"

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def writeIntrinsicReturnWithProtectors
    (s : MachineState)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx)
    (retVal : Value) :
    MirStepNode :=
  match targetOpt with
  | .none => MirStepNode.fail .ub
  | .some targetBb =>
    let nilTyValid : Bool :=
      match destination.projection, bodyLocalDecls with
      | .nil, _ :: _ =>
        validateValueForTy? bodyLayouts (placeTy bodyLocalDecls bodyLayouts destination) retVal
      | _, _ => true
    match nilTyValid with
    | false => MirStepNode.fail .ub
    | true =>
      match
        writeReturnDestination
          locals'
          s.memory
          destination
          retVal
          bodyLocalDecls
          bodyLayouts
      with
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

/--
Resolve the pointee `Ty` (preserving a consistent `layoutIdx` from the first
pointer operand only when its `TypeLayout` is a consistent pointer layout with
an explicit pointee entry matching `elemTy`, never adopting synthetic
`layoutIdx = 0` from `pointeeTyOf` or `const_eval_select` `.zeroSized` dummy
operands) for pointer-parameterized memory intrinsics
(`typed_swap_nonoverlapping<T>`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2569>

> "pub const unsafe fn typed_swap_nonoverlapping<T>(x: *mut T, y: *mut T) {"
-/
def resolveIntrinsicPointeeFullTy
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (elemTy : RigidTy) :
    Ty :=
  match argOps with
  | ptrOp :: _ =>
    match ptrOp with
    | .constant { val := .zeroSized, .. } =>
      { kind := elemTy, layoutIdx := unresolvedLayoutIdx bodyLayouts }
    | _ =>
      match operandTyResolved bodyLocalDecls bodyLayouts ptrOp with
      | .some ptrTy =>
        match pointeeTyOf ptrTy with
        | .some pt =>
          match rigidTyEq pt.kind elemTy with
          | false => { kind := elemTy, layoutIdx := unresolvedLayoutIdx bodyLayouts }
          | true =>
            match LayoutTable.lookup bodyLayouts ptrTy.layoutIdx with
            | .some ptrLayout =>
              match isConsistentPtrLayout bodyLayouts ptrLayout, ptrLayout.fieldLayouts with
              | true, ptLayoutIdx :: .nil =>
                { kind := elemTy, layoutIdx := ptLayoutIdx }
              | _, _ => { kind := elemTy, layoutIdx := unresolvedLayoutIdx bodyLayouts }
            | .none => { kind := elemTy, layoutIdx := unresolvedLayoutIdx bodyLayouts }
        | .none => { kind := elemTy, layoutIdx := unresolvedLayoutIdx bodyLayouts }
      | .none => { kind := elemTy, layoutIdx := unresolvedLayoutIdx bodyLayouts }
  | .nil => { kind := elemTy, layoutIdx := unresolvedLayoutIdx bodyLayouts }

/--
Check alignment on both pointer arguments of a two-pointer intrinsic without
letting `.unsupported` on the first pointer mask definite `.ub` on the second.
-/
def checkPtrPairAligned
    (s : MachineState)
    (locals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (ptrA ptrB : Value)
    (reqAlign : Nat)
    (nonZeroAccess : Bool) :
    MemOpRes Unit :=
  match
    checkPtrArgAligned s locals bodyLocalDecls bodyLayouts ptrA reqAlign nonZeroAccess,
    checkPtrArgAligned s locals bodyLocalDecls bodyLayouts ptrB reqAlign nonZeroAccess
  with
  | .ub, _ => .ub
  | _, .ub => .ub
  | .unsupported, _ => .unsupported
  | _, .unsupported => .unsupported
  | .ok (), .ok () => .ok ()

/--
Apply an exact-range Tree Borrows read transition for endpoint `ep` over
`[ep.effOff, ep.effOff + accessLen)`, returning `.some mem.borrows` for global
endpoints and `.none` on Tree Borrows UB.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def endpointBorrowsAfterRead
    (mem : Memory)
    (ep : ResolvedMemEndpoint)
    (accessLen : Nat) :
    Option (List BorrowEntry) :=
  match ep.borrow? with
  | .none => .some mem.borrows
  | .some (tag, entry) =>
    borrowsAfterReadAccess
      mem.borrows
      mem.activeProtectors
      ep.targetDecls
      ep.targetLayouts
      tag
      entry
      ep.effOff
      accessLen

/--
Apply an exact-range Tree Borrows write transition for endpoint `ep` over
`[ep.effOff, ep.effOff + accessLen)`, returning `.some mem.borrows` for global
endpoints and `.none` on Tree Borrows UB.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def endpointBorrowsAfterWrite
    (mem : Memory)
    (ep : ResolvedMemEndpoint)
    (accessLen : Nat) :
    Option (List BorrowEntry) :=
  match ep.borrow? with
  | .none => .some mem.borrows
  | .some (tag, entry) =>
    borrowsAfterWriteAccess
      mem.borrows
      mem.activeProtectors
      ep.targetDecls
      ep.targetLayouts
      tag
      entry
      ep.effOff
      accessLen

/--
Lexicographically compare two equal-length `List UInt8` slices as unsigned
bytes, returning two's-complement 32-bit `i32` bits: `0xFFFFFFFF` (`-1`) if
`left < right`, `0` if equal, or `1` if `left > right`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2320-L2323>

> "/// Lexicographically compare `[left, left + bytes)` and `[right, right + bytes)`
> /// as unsigned bytes, returning negative if `left` is less, zero if all the
> /// bytes match, or positive if `left` is greater."
-/
def compareUnsignedBytesI32 : List UInt8 → List UInt8 → Nat
  | .nil, .nil => 0
  | a :: as, b :: bs =>
    let an := a.toBitVec.toNat
    let bn := b.toBitVec.toNat
    match Nat.blt an bn with
    | true => 4294967295
    | false =>
      match Nat.blt bn an with
      | true => 1
      | false => compareUnsignedBytesI32 as bs
  | _, _ => 0

/--
Evaluate a direct call to `core::intrinsics::copy<T>(src: *const T, dst: *mut T,
count: usize) -> ()` (overlapping `memmove`):
1. Rejects malformed argument lists or non-thin/wrong-width pointer arguments
   with `.ub` before undetermined layouts or provenance-carrying counts.
2. Unsized `T` or undetermined layout/alignment (`rigidTyLayoutDeterminedAux`,
   `exactRigidTyByteSize?`, `exactRigidTyAlign?`) fails closed `.unsupported`.
3. For ZST `T` (`size_of::<T>() == 0`), `0 * count == 0` for every `count`
   (including provenance-carrying `usize` counts): checks alignment of `src` and
   `dst` even at 0 bytes (null allowed at 0 bytes) and returns `()`.
4. For non-ZST `T`, checks alignment before failing closed on provenance counts,
   enforces `count * size_of::<T>() <= isize::MAX`, permits aligned null
   pointers when `byteCount == 0`, and for `byteCount > 0` requires non-null
   aligned live pointers and executes `evalCopyMemory` (atomic read-snapshot of
   source `AbstractByte`s preserving provenance and `.uninit`, exact-range Tree
   Borrows read-then-write on post-read `borrows₁`, and round-trip-guarded
   commit).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L3030-L3039>

> "/// This is an accidentally-stable alias to [`ptr::copy`]; use that instead.
> ...
> pub const unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize);"

Reference (`core::ptr::copy` documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L554-L589>

> "/// Copies `count * size_of::<T>()` bytes from `src` to `dst`. The source
> /// and destination may overlap.
> ...
> /// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `src` must be [valid] for reads of `count * size_of::<T>()` bytes or that number must be 0.
> ///
> /// * `dst` must be [valid] for writes of `count * size_of::<T>()` bytes or that number must be 0,
> ///   and `dst` must remain valid even when `src` is read for `count * size_of::<T>()` bytes. (This
> ///   means if the memory ranges overlap, the `dst` pointer must not be invalidated by `src` reads.)
> ///
> /// * Both `src` and `dst` must be properly aligned.
> ...
> /// Note that even if the effectively copied size (`count * size_of::<T>()`) is
> /// `0`, the pointers must be properly aligned."
-/
def evalCopyCall
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  let isizeMax := Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1
  match argVals with
  | srcVal :: dstVal :: countVal :: .nil =>
    match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
    | .none =>
      match
        isNullThinPtr s.memory ptrBytes srcVal,
        isNullThinPtr s.memory ptrBytes dstVal,
        decodeUsizeArg? s.memory ptrBytes countVal
      with
      | .none, _, _ => MirStepNode.fail .ub
      | _, .none, _ => MirStepNode.fail .ub
      | _, _, .ub => MirStepNode.fail .ub
      | _, _, _ => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
    | .some elemTy =>
      match isUnsizedRigidTy 8 elemTy with
      | true => MirStepNode.unsupported
      | false =>
        match
          isNullThinPtr s.memory ptrBytes srcVal,
          isNullThinPtr s.memory ptrBytes dstVal,
          decodeUsizeArg? s.memory ptrBytes countVal
        with
        | .none, _, _ => MirStepNode.fail .ub
        | _, .none, _ => MirStepNode.fail .ub
        | _, _, .ub => MirStepNode.fail .ub
        | .some srcNull, .some dstNull, countRes =>
          match
            rigidTyLayoutDeterminedAux bodyLocalDecls bodyLayouts true 8 elemTy,
            exactRigidTyByteSize? bodyLocalDecls bodyLayouts elemTy,
            exactRigidTyAlign? bodyLocalDecls bodyLayouts elemTy
          with
          | true, .some elemSize, .some elemAlign =>
            match Nat.beq elemSize 0 with
            | true =>
              match
                checkPtrPairAligned s locals' bodyLocalDecls bodyLayouts srcVal dstVal elemAlign false
              with
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
              | .ok () =>
                writeIntrinsicReturnWithProtectors
                  s bodyLocalDecls bodyLayouts locals' destination targetOpt .unit
            | false =>
              match countRes with
              | .ub => MirStepNode.fail .ub
              | .unsupported =>
                match
                  checkPtrPairAligned s locals' bodyLocalDecls bodyLayouts srcVal dstVal elemAlign false
                with
                | .ub => MirStepNode.fail .ub
                | _ => MirStepNode.unsupported
              | .ok count =>
                let byteCount := Nat.mul count elemSize
                match Nat.ble byteCount isizeMax with
                | false => MirStepNode.fail .ub
                | true =>
                  match Nat.beq byteCount 0 with
                  | true =>
                    match
                      checkPtrPairAligned s locals' bodyLocalDecls bodyLayouts srcVal dstVal elemAlign false
                    with
                    | .ub => MirStepNode.fail .ub
                    | .unsupported => MirStepNode.unsupported
                    | .ok () =>
                      writeIntrinsicReturnWithProtectors
                        s bodyLocalDecls bodyLayouts locals' destination targetOpt .unit
                  | false =>
                    match Bool.or srcNull dstNull with
                    | true => MirStepNode.fail .ub
                    | false =>
                      match
                        checkPtrPairAligned s locals' bodyLocalDecls bodyLayouts srcVal dstVal elemAlign true
                      with
                      | .ub => MirStepNode.fail .ub
                      | .unsupported => MirStepNode.unsupported
                      | .ok () =>
                        match srcVal, dstVal with
                        | .ptr srcPtr _, .ptr dstPtr _ =>
                          match
                            evalCopyMemory
                              s locals' bodyLocalDecls bodyLayouts srcPtr dstPtr byteCount
                          with
                          | .ub => MirStepNode.fail .ub
                          | .unsupported => MirStepNode.unsupported
                          | .ok (locals₂, mem₂) =>
                            writeIntrinsicReturnWithProtectors
                              { s with memory := mem₂ }
                              bodyLocalDecls
                              bodyLayouts
                              locals₂
                              destination
                              targetOpt
                              .unit
                        | _, _ => MirStepNode.fail .ub
          | _, _, _ => MirStepNode.unsupported
  | _ => MirStepNode.fail .ub

/--
Evaluate a direct call to `core::intrinsics::compare_bytes(left: *const u8,
right: *const u8, bytes: usize) -> i32`:
1. Validates both `left` and `right` as non-null thin pointers BEFORE failing
   closed on provenance-carrying `bytes` counts (null is UB even at `bytes = 0`
   per `core::ptr#safety`: "A [null] pointer is *never* valid for
   reads/writes").
2. Enforces `bytes <= isize::MAX`; at `bytes = 0`, returns `0i32`.
3. For `bytes > 0`, resolves live endpoints for `left` then `right`, checks
   bounds and Tree Borrows tag windows, reads full `[off, off + bytes)` slices,
   applies exact-range Tree Borrows read transitions, eagerly checks `.uninit`
   across each full slice BEFORE checking provenance (`stripProvenanceBytes`),
   and returns `-1`/`0`/`1` as `i32`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2320-L2337>

> "/// Lexicographically compare `[left, left + bytes)` and `[right, right + bytes)`
> /// as unsigned bytes, returning negative if `left` is less, zero if all the
> /// bytes match, or positive if `left` is greater.
> ...
> /// `left` and `right` must each be [valid] for reads of `bytes` bytes.
> ///
> /// Note that this applies to the whole range, not just until the first byte
> /// that differs.  That allows optimizations that can read in large chunks.
> ...
> pub const unsafe fn compare_bytes(left: *const u8, right: *const u8, bytes: usize) -> i32;"

Reference (`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L18-L20>

> "//! * A [null] pointer is *never* valid for reads/writes.
> //! * For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes."
-/
def evalCompareBytesCall
    (s : MachineState)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  let isizeMax := Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1
  match argVals with
  | leftVal :: rightVal :: lenVal :: .nil =>
    match
      isNullThinPtr s.memory ptrBytes leftVal,
      isNullThinPtr s.memory ptrBytes rightVal
    with
    | .some false, .some false =>
      match decodeUsizeArg? s.memory ptrBytes lenVal with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok byteCount =>
        match Nat.ble byteCount isizeMax with
        | false => MirStepNode.fail .ub
        | true =>
          match Nat.beq byteCount 0 with
          | true =>
            writeIntrinsicReturnWithProtectors
              s bodyLocalDecls bodyLayouts locals' destination targetOpt (.scalar ⟨0, 4⟩)
          | false =>
            match leftVal, rightVal with
            | .ptr leftPtr _, .ptr rightPtr _ =>
              match resolveLiveMemEndpoint s locals' bodyLocalDecls bodyLayouts leftPtr with
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
              | .ok leftEp =>
                match Nat.ble (Nat.add leftEp.effOff byteCount) leftEp.allocSize with
                | false => MirStepNode.fail .ub
                | true =>
                  match resolveLiveMemEndpoint s locals' bodyLocalDecls bodyLayouts rightPtr with
                  | .ub => MirStepNode.fail .ub
                  | .unsupported => MirStepNode.unsupported
                  | .ok rightEp0 =>
                    match Nat.ble (Nat.add rightEp0.effOff byteCount) rightEp0.allocSize with
                    | false => MirStepNode.fail .ub
                    | true =>
                      match endpointAccessCheck leftEp byteCount with
                      | .ub => MirStepNode.fail .ub
                      | .unsupported => MirStepNode.unsupported
                      | .ok () =>
                        match endpointBorrowsAfterRead s.memory leftEp byteCount with
                        | .none => MirStepNode.fail .ub
                        | .some borrows₁ =>
                          let mem₁ : Memory := { s.memory with borrows := borrows₁ }
                          match
                            resolveLiveMemEndpoint
                              { s with memory := mem₁ } locals' bodyLocalDecls bodyLayouts rightPtr
                          with
                          | .ub => MirStepNode.fail .ub
                          | .unsupported => MirStepNode.unsupported
                          | .ok rightEp =>
                            match endpointAccessCheck rightEp byteCount with
                            | .ub => MirStepNode.fail .ub
                            | .unsupported => MirStepNode.unsupported
                            | .ok () =>
                              match endpointBorrowsAfterRead mem₁ rightEp byteCount with
                              | .none => MirStepNode.fail .ub
                              | .some borrows₂ =>
                                let mem₂ : Memory := { mem₁ with borrows := borrows₂ }
                                match readRootAbstractBytes s.memory leftEp with
                                | .none => MirStepNode.unsupported
                                | .some leftRootBytes =>
                                  match sliceAbstractBytes leftRootBytes leftEp.effOff byteCount with
                                  | .none => MirStepNode.fail .ub
                                  | .some leftSlice =>
                                    match readRootAbstractBytes mem₂ rightEp with
                                    | .none => MirStepNode.unsupported
                                    | .some rightRootBytes =>
                                      match
                                        sliceAbstractBytes rightRootBytes rightEp.effOff byteCount
                                      with
                                      | .none => MirStepNode.fail .ub
                                      | .some rightSlice =>
                                        match
                                          stripProvenanceBytes mem₂ leftSlice,
                                          stripProvenanceBytes mem₂ rightSlice
                                        with
                                        | .ub, _ => MirStepNode.fail .ub
                                        | _, .ub => MirStepNode.fail .ub
                                        | .unsupported, _ => MirStepNode.unsupported
                                        | _, .unsupported => MirStepNode.unsupported
                                        | .ok leftRaw, .ok rightRaw =>
                                          let cmpBits := compareUnsignedBytesI32 leftRaw rightRaw
                                          writeIntrinsicReturnWithProtectors
                                            { s with memory := mem₂ }
                                            bodyLocalDecls
                                            bodyLayouts
                                            locals'
                                            destination
                                            targetOpt
                                            (.scalar ⟨cmpBits, 4⟩)
            | _, _ => MirStepNode.fail .ub
    | _, _ => MirStepNode.fail .ub
  | _ => MirStepNode.fail .ub

/--
Evaluate a direct call to `core::intrinsics::raw_eq<T>(a: &T, b: &T) -> bool`:
1. Unsized `T` fails closed `.unsupported`.
2. Rejects malformed/null pointer arguments and layout-uninhabited `T` (for
   both ZST and non-ZST `T`, while `&!` is layout-inhabited so `raw_eq::<&!>`
   proceeds) with `.ub` BEFORE failing closed on undetermined layout/alignment.
3. Checks alignment of `a` and `b` against `align_of::<T>()`; ZST returns `true`.
4. For `size_of::<T>() > 0`, resolves live endpoints, checks bounds and Tree
   Borrows tag windows, applies exact-range Tree Borrows read transitions,
   eagerly checks `.uninit` (including padding!) across each full slice BEFORE
   provenance (`stripProvenanceBytes`), and returns `bool` bytewise equality.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2293-L2318>

> "/// Determines whether the raw bytes of the two values are equal.
> ...
> /// Since this works by comparing the underlying bytes, the actual `T` is
> /// not particularly important.  It will be used for its size and alignment,
> /// but any validity restrictions will be ignored, not enforced.
> ///
> /// # Safety
> ///
> /// It's UB to call this if any of the *bytes* in `*a` or `*b` are uninitialized.
> /// Note that this is a stricter criterion than just the *values* being
> /// fully-initialized: if `T` has padding, it's UB to call this intrinsic.
> ...
> pub const unsafe fn raw_eq<T>(a: &T, b: &T) -> bool;"
-/
def evalRawEqCall
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  let isizeMax := Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1
  match argVals with
  | aVal :: bVal :: .nil =>
    match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
    | .none =>
      match
        isNullThinPtr s.memory ptrBytes aVal,
        isNullThinPtr s.memory ptrBytes bVal
      with
      | .some false, .some false =>
        intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
      | _, _ => MirStepNode.fail .ub
    | .some elemTy =>
      match isUnsizedRigidTy 8 elemTy with
      | true => MirStepNode.unsupported
      | false =>
        match
          isNullThinPtr s.memory ptrBytes aVal,
          isNullThinPtr s.memory ptrBytes bVal
        with
        | .some false, .some false =>
          match isUninhabitedRigidTy bodyLocalDecls bodyLayouts 8 elemTy with
          | true => MirStepNode.fail .ub
          | false =>
            match
              rigidTyLayoutDeterminedAux bodyLocalDecls bodyLayouts true 8 elemTy,
              exactRigidTyByteSize? bodyLocalDecls bodyLayouts elemTy,
              exactRigidTyAlign? bodyLocalDecls bodyLayouts elemTy
            with
            | true, .some elemSize, .some elemAlign =>
              let isZero := Nat.beq elemSize 0
              match
                checkPtrPairAligned
                  s locals' bodyLocalDecls bodyLayouts aVal bVal elemAlign (Bool.not isZero)
              with
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
              | .ok () =>
                match isZero with
                | true =>
                  writeIntrinsicReturnWithProtectors
                    s bodyLocalDecls bodyLayouts locals' destination targetOpt (.scalar ⟨1, 1⟩)
                | false =>
                  match Nat.ble elemSize isizeMax with
                  | false => MirStepNode.fail .ub
                  | true =>
                    match aVal, bVal with
                    | .ptr aPtr _, .ptr bPtr _ =>
                        match resolveLiveMemEndpoint s locals' bodyLocalDecls bodyLayouts aPtr with
                        | .ub => MirStepNode.fail .ub
                        | .unsupported => MirStepNode.unsupported
                        | .ok aEp =>
                          match Nat.ble (Nat.add aEp.effOff elemSize) aEp.allocSize with
                          | false => MirStepNode.fail .ub
                          | true =>
                            match resolveLiveMemEndpoint s locals' bodyLocalDecls bodyLayouts bPtr with
                            | .ub => MirStepNode.fail .ub
                            | .unsupported => MirStepNode.unsupported
                            | .ok bEp0 =>
                              match Nat.ble (Nat.add bEp0.effOff elemSize) bEp0.allocSize with
                              | false => MirStepNode.fail .ub
                              | true =>
                                match endpointAccessCheck aEp elemSize with
                                | .ub => MirStepNode.fail .ub
                                | .unsupported => MirStepNode.unsupported
                                | .ok () =>
                                  match endpointBorrowsAfterRead s.memory aEp elemSize with
                                  | .none => MirStepNode.fail .ub
                                  | .some borrows₁ =>
                                    let mem₁ : Memory := { s.memory with borrows := borrows₁ }
                                    match
                                      resolveLiveMemEndpoint
                                        { s with memory := mem₁ }
                                        locals' bodyLocalDecls bodyLayouts bPtr
                                    with
                                    | .ub => MirStepNode.fail .ub
                                    | .unsupported => MirStepNode.unsupported
                                    | .ok bEp =>
                                      match endpointAccessCheck bEp elemSize with
                                      | .ub => MirStepNode.fail .ub
                                      | .unsupported => MirStepNode.unsupported
                                      | .ok () =>
                                        match endpointBorrowsAfterRead mem₁ bEp elemSize with
                                        | .none => MirStepNode.fail .ub
                                        | .some borrows₂ =>
                                          let mem₂ : Memory := { mem₁ with borrows := borrows₂ }
                                          match readRootAbstractBytes s.memory aEp with
                                          | .none => MirStepNode.unsupported
                                          | .some aRootBytes =>
                                            match sliceAbstractBytes aRootBytes aEp.effOff elemSize with
                                            | .none => MirStepNode.fail .ub
                                            | .some aSlice =>
                                              match readRootAbstractBytes mem₂ bEp with
                                              | .none => MirStepNode.unsupported
                                              | .some bRootBytes =>
                                                match
                                                  sliceAbstractBytes bRootBytes bEp.effOff elemSize
                                                with
                                                | .none => MirStepNode.fail .ub
                                                | .some bSlice =>
                                                  match
                                                    stripProvenanceBytes mem₂ aSlice,
                                                    stripProvenanceBytes mem₂ bSlice
                                                  with
                                                  | .ub, _ => MirStepNode.fail .ub
                                                  | _, .ub => MirStepNode.fail .ub
                                                  | .unsupported, _ => MirStepNode.unsupported
                                                  | _, .unsupported => MirStepNode.unsupported
                                                  | .ok aRaw, .ok bRaw =>
                                                    let eqBit :=
                                                      match listByteEq aRaw bRaw with
                                                      | true => 1
                                                      | false => 0
                                                    writeIntrinsicReturnWithProtectors
                                                      { s with memory := mem₂ }
                                                      bodyLocalDecls
                                                      bodyLayouts
                                                      locals'
                                                      destination
                                                      targetOpt
                                                      (.scalar ⟨eqBit, 1⟩)
                      | _, _ => MirStepNode.fail .ub
            | _, _, _ => MirStepNode.unsupported
        | _, _ => MirStepNode.fail .ub
  | _ => MirStepNode.fail .ub

/--
Read both root abstract-byte images for `typed_swap_nonoverlapping`, validate
both `elemSize`-byte slices against `elemTyFull` using `TypedValidity.combine`
(so definite `.ub` in either slice is never masked by `.unsupported` in the
other), and reset padding bytes in both slices before commit.
-/
def readValidateAndPrepareSwapSlices
    (memX memY : Memory)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (elemTyFull : Ty)
    (xEp yEp : ResolvedMemEndpoint)
    (elemSize : Nat) :
    MemOpRes ((List AbstractByte × List AbstractByte) × (List AbstractByte × List AbstractByte)) :=
  let xPair : MemOpRes (List AbstractByte × List AbstractByte) :=
    match readRootAbstractBytes memX xEp with
    | .none => .unsupported
    | .some xRootBytes =>
      match sliceAbstractBytes xRootBytes xEp.effOff elemSize with
      | .none => .ub
      | .some xSlice => .ok (xRootBytes, xSlice)
  let yPair : MemOpRes (List AbstractByte × List AbstractByte) :=
    match readRootAbstractBytes memY yEp with
    | .none => .unsupported
    | .some yRootBytes =>
      match sliceAbstractBytes yRootBytes yEp.effOff elemSize with
      | .none => .ub
      | .some ySlice => .ok (yRootBytes, ySlice)
  let xValRes : TypedValidity :=
    match xPair with
    | .ub => .ub
    | .unsupported => .unsupported
    | .ok (_, xSlice) =>
      validateTypedBytes memX bodyLocalDecls bodyLayouts defaultCodecFuel elemTyFull xSlice
  let yValRes : TypedValidity :=
    match yPair with
    | .ub => .ub
    | .unsupported => .unsupported
    | .ok (_, ySlice) =>
      validateTypedBytes memY bodyLocalDecls bodyLayouts defaultCodecFuel elemTyFull ySlice
  match TypedValidity.combine xValRes fun _ => yValRes with
  | .ub => .ub
  | .unsupported => .unsupported
  | .valid =>
    match xPair, yPair with
    | .ok (xRootBytes, xSlice), .ok (yRootBytes, ySlice) =>
      match
        resetTypedPaddingBytes defaultCodecFuel bodyLocalDecls bodyLayouts elemTyFull xSlice,
        resetTypedPaddingBytes defaultCodecFuel bodyLocalDecls bodyLayouts elemTyFull ySlice
      with
      | .some xStored, .some yStored => .ok ((xRootBytes, xStored), (yRootBytes, yStored))
      | _, _ => .unsupported
    | _, _ => .unsupported


/--
Evaluate a direct call to `core::intrinsics::typed_swap_nonoverlapping<T>(x:
*mut T, y: *mut T) -> ()`:
1. Unsized `T` fails closed `.unsupported`.
2. Rejects malformed/null pointer arguments (even for ZST `T` per `ptr#safety`)
   and layout-uninhabited `T` with `.ub` BEFORE failing closed on undetermined
   layout/alignment.
3. Checks alignment of `x` and `y` against `align_of::<T>()`; ZST is a no-op.
4. For `size_of::<T>() > 0`, resolves live endpoints and checks tag windows,
   enforces container-first disjointness (`AllocKey.beq` + `rangesDisjoint`,
   permitting disjoint elements of the same container while rejecting any byte
   overlap as `.ub`), executes exact-range Tree Borrows transitions in order
   `read(x) -> read(y) -> write(x) -> write(y)`, validates both values via
   3-way `validateTypedBytes`, resets all inter-field/trailing/common-union
   padding to `.uninit` on BOTH stack locals and globals via
   `resetTypedPaddingBytes`, and commits atomically via
   `commitRootAbstractBytes` (single-buffer commit when `x` and `y` share the
   same root allocation).

Capture-plane invariant: `evalTerminator` consults `lookupCallee` before
`evalDirectRustIntrinsic?`; `core::intrinsics::typed_swap_nonoverlapping` has an
untyped MIR fallback body in `libcore` (calling `ptr::swap_nonoverlapping`
without typed validity checks). Soundness depends on `rustc-capture`'s
`should_capture_non_local_callee` excluding all `tcx.is_intrinsic` bodies so no
fallback body for `typed_swap_nonoverlapping` is ever populated in
`Memory.callees`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2545-L2573>

> "/// Non-overlapping *typed* swap of a single value.
> ...
> /// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * Both `x` and `y` must be [valid] for both reads and writes.
> ///
> /// * Both `x` and `y` must be properly aligned.
> ///
> /// * The region of memory beginning at `x` must *not* overlap with the region of memory
> ///   beginning at `y`.
> ///
> /// * The memory pointed by `x` and `y` must both contain values of type `T`.
> ...
> pub const unsafe fn typed_swap_nonoverlapping<T>(x: *mut T, y: *mut T) {"
-/
def evalTypedSwapNonOverlappingCall
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  let isizeMax := Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1
  match argVals with
  | xVal :: yVal :: .nil =>
    match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
    | .none =>
      match
        isNullThinPtr s.memory ptrBytes xVal,
        isNullThinPtr s.memory ptrBytes yVal
      with
      | .some false, .some false =>
        intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
      | _, _ => MirStepNode.fail .ub
    | .some elemTy =>
      match isUnsizedRigidTy 8 elemTy with
      | true => MirStepNode.unsupported
      | false =>
        match
          isNullThinPtr s.memory ptrBytes xVal,
          isNullThinPtr s.memory ptrBytes yVal
        with
        | .some false, .some false =>
          match isUninhabitedRigidTy bodyLocalDecls bodyLayouts 8 elemTy with
          | true => MirStepNode.fail .ub
          | false =>
            match
              rigidTyLayoutDeterminedAux bodyLocalDecls bodyLayouts true 8 elemTy,
              exactRigidTyByteSize? bodyLocalDecls bodyLayouts elemTy,
              exactRigidTyAlign? bodyLocalDecls bodyLayouts elemTy
            with
            | true, .some elemSize, .some elemAlign =>
              let isZero := Nat.beq elemSize 0
              match
                checkPtrPairAligned
                  s locals' bodyLocalDecls bodyLayouts xVal yVal elemAlign (Bool.not isZero)
              with
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
              | .ok () =>
                match isZero with
                | true =>
                  writeIntrinsicReturnWithProtectors
                    s bodyLocalDecls bodyLayouts locals' destination targetOpt .unit
                | false =>
                  match Nat.ble elemSize isizeMax with
                  | false => MirStepNode.fail .ub
                  | true =>
                    match xVal, yVal with
                    | .ptr xPtr _, .ptr yPtr _ =>
                      match resolveLiveMemEndpoint s locals' bodyLocalDecls bodyLayouts xPtr with
                      | .ub => MirStepNode.fail .ub
                      | .unsupported => MirStepNode.unsupported
                      | .ok xEp =>
                        match Nat.ble (Nat.add xEp.effOff elemSize) xEp.allocSize with
                        | false => MirStepNode.fail .ub
                        | true =>
                          let xWritable : Bool :=
                            match xEp.globalAlloc? with
                            | .some g => match g.mutability with | .mut => true | .not => false
                            | .none => true
                          match xWritable with
                          | false => MirStepNode.fail .ub
                          | true =>
                            match resolveLiveMemEndpoint s locals' bodyLocalDecls bodyLayouts yPtr with
                            | .ub => MirStepNode.fail .ub
                            | .unsupported => MirStepNode.unsupported
                            | .ok yEp0 =>
                              match Nat.ble (Nat.add yEp0.effOff elemSize) yEp0.allocSize with
                              | false => MirStepNode.fail .ub
                              | true =>
                                let yWritable : Bool :=
                                  match yEp0.globalAlloc? with
                                  | .some g =>
                                    match g.mutability with | .mut => true | .not => false
                                  | .none => true
                                match yWritable with
                                | false => MirStepNode.fail .ub
                                | true =>
                                  let sameAlloc := AllocKey.beq xEp.allocKey yEp0.allocKey
                                  match
                                    Bool.and sameAlloc
                                      (Bool.not
                                        (rangesDisjoint
                                          xEp.effOff elemSize yEp0.effOff elemSize))
                                  with
                                  | true => MirStepNode.fail .ub
                                  | false =>
                                    match endpointAccessCheck xEp elemSize with
                                    | .ub => MirStepNode.fail .ub
                                    | .unsupported => MirStepNode.unsupported
                                    | .ok () =>
                                      match endpointAccessCheck yEp0 elemSize with
                                      | .ub => MirStepNode.fail .ub
                                      | .unsupported => MirStepNode.unsupported
                                      | .ok () =>
                                        match endpointBorrowsAfterRead s.memory xEp elemSize with
                                        | .none => MirStepNode.fail .ub
                                        | .some borrows₁ =>
                                          let mem₁ : Memory := { s.memory with borrows := borrows₁ }
                                          match
                                            resolveLiveMemEndpoint
                                              { s with memory := mem₁ }
                                              locals' bodyLocalDecls bodyLayouts yPtr
                                          with
                                          | .ub => MirStepNode.fail .ub
                                          | .unsupported => MirStepNode.unsupported
                                          | .ok yEp₁ =>
                                            match endpointAccessCheck yEp₁ elemSize with
                                            | .ub => MirStepNode.fail .ub
                                            | .unsupported => MirStepNode.unsupported
                                            | .ok () =>
                                              match endpointBorrowsAfterRead mem₁ yEp₁ elemSize with
                                              | .none => MirStepNode.fail .ub
                                              | .some borrows₂ =>
                                                let mem₂ : Memory :=
                                                  { mem₁ with borrows := borrows₂ }
                                                match
                                                  resolveLiveMemEndpoint
                                                    { s with memory := mem₂ }
                                                    locals' bodyLocalDecls bodyLayouts xPtr
                                                with
                                                | .ub => MirStepNode.fail .ub
                                                | .unsupported => MirStepNode.unsupported
                                                | .ok xEp₂ =>
                                                  match endpointAccessCheck xEp₂ elemSize with
                                                  | .ub => MirStepNode.fail .ub
                                                  | .unsupported => MirStepNode.unsupported
                                                  | .ok () =>
                                                    match
                                                      endpointBorrowsAfterWrite
                                                        mem₂ xEp₂ elemSize
                                                    with
                                                    | .none => MirStepNode.fail .ub
                                                    | .some borrows₃ =>
                                                      let mem₃ : Memory :=
                                                        { mem₂ with borrows := borrows₃ }
                                                      match
                                                        resolveLiveMemEndpoint
                                                          { s with memory := mem₃ }
                                                          locals' bodyLocalDecls bodyLayouts yPtr
                                                      with
                                                      | .ub => MirStepNode.fail .ub
                                                      | .unsupported => MirStepNode.unsupported
                                                      | .ok yEp₃ =>
                                                        match
                                                          endpointAccessCheck yEp₃ elemSize
                                                        with
                                                        | .ub => MirStepNode.fail .ub
                                                        | .unsupported => MirStepNode.unsupported
                                                        | .ok () =>
                                                          match
                                                            endpointBorrowsAfterWrite
                                                              mem₃ yEp₃ elemSize
                                                          with
                                                          | .none => MirStepNode.fail .ub
                                                          | .some borrows₄ =>
                                                            let mem₄ : Memory :=
                                                              { mem₃ with borrows := borrows₄ }
                                                            let elemTyFull :=
                                                              resolveIntrinsicPointeeFullTy
                                                                bodyLocalDecls bodyLayouts
                                                                argOps elemTy
                                                            match
                                                              readValidateAndPrepareSwapSlices
                                                                s.memory mem₁
                                                                bodyLocalDecls bodyLayouts
                                                                elemTyFull xEp yEp₁ elemSize
                                                            with
                                                            | .ub => MirStepNode.fail .ub
                                                            | .unsupported =>
                                                              MirStepNode.unsupported
                                                            | .ok ((xRootBytes, xStored),
                                                                   (yRootBytes, yStored)) =>
                                                                  match sameAlloc with
                                                                  | true =>
                                                                    match
                                                                      writeAbstractBytesAt
                                                                        xRootBytes
                                                                        xEp₂.effOff
                                                                        yStored
                                                                    with
                                                                    | .none => MirStepNode.fail .ub
                                                                    | .some patched1 =>
                                                                      match
                                                                        writeAbstractBytesAt
                                                                          patched1
                                                                          yEp₃.effOff
                                                                          xStored
                                                                      with
                                                                      | .none =>
                                                                        MirStepNode.fail .ub
                                                                      | .some patched2 =>
                                                                        match
                                                                          commitRootAbstractBytes
                                                                            mem₄ locals' xEp₂
                                                                            patched2
                                                                        with
                                                                        | .ub =>
                                                                          MirStepNode.fail .ub
                                                                        | .unsupported =>
                                                                          MirStepNode.unsupported
                                                                        | .ok (localsF, memF) =>
                                                                          writeIntrinsicReturnWithProtectors
                                                                            { s with
                                                                              memory := memF }
                                                                            bodyLocalDecls
                                                                            bodyLayouts
                                                                            localsF
                                                                            destination
                                                                            targetOpt
                                                                            .unit
                                                                  | false =>
                                                                    match
                                                                      writeAbstractBytesAt
                                                                        xRootBytes
                                                                        xEp₂.effOff
                                                                        yStored
                                                                    with
                                                                    | .none => MirStepNode.fail .ub
                                                                    | .some xPatched =>
                                                                      match
                                                                        commitRootAbstractBytes
                                                                          mem₄ locals' xEp₂
                                                                          xPatched
                                                                      with
                                                                      | .ub => MirStepNode.fail .ub
                                                                      | .unsupported =>
                                                                        MirStepNode.unsupported
                                                                      | .ok (locals₁, mem₄') =>
                                                                        match
                                                                          writeAbstractBytesAt
                                                                            yRootBytes
                                                                            yEp₃.effOff
                                                                            xStored
                                                                        with
                                                                        | .none =>
                                                                          MirStepNode.fail .ub
                                                                        | .some yPatched =>
                                                                          match
                                                                            commitRootAbstractBytes
                                                                              mem₄' locals₁ yEp₃
                                                                              yPatched
                                                                          with
                                                                          | .ub =>
                                                                            MirStepNode.fail .ub
                                                                          | .unsupported =>
                                                                            MirStepNode.unsupported
                                                                          | .ok (localsF, memF) =>
                                                                            writeIntrinsicReturnWithProtectors
                                                                              { s with
                                                                                memory := memF }
                                                                              bodyLocalDecls
                                                                              bodyLayouts
                                                                              localsF
                                                                              destination
                                                                              targetOpt
                                                                              .unit
                    | _, _ => MirStepNode.fail .ub
            | _, _, _ => MirStepNode.unsupported
        | _, _ => MirStepNode.fail .ub
  | _ => MirStepNode.fail .ub

/--
Resolve the effective byte offsets `(ptrOff, baseOff)` of `ptrVal` and `baseVal`
for `core::intrinsics::ptr_offset_from` / `ptr_offset_from_unsigned`:
- Same-address fast path (equal provenance-free addresses in either integer or
  unbacked `allocId = 0` encoding, identical `(allocId, offsetBytes)`, or equal
  effective offsets in the same live allocation) returns `.ok (0, 0)` without
  requiring liveness or in-bounds checks.
- Non-zero distance requires both pointers to derive from the same live
  allocation with both offsets in `[0, allocSize]` (including one-past-end),
  independent of Tree Borrows permissions (`DIV-LM-D6-OFFSET-DISABLED-TAG`).
- Distinct dead tags of the same root local with empty (or transparent-only)
  projections fault `.ub` when their pointer offsets differ mod `2^W`, and fail
  closed `.unsupported` when equal (storage generation is not recorded).
  Modeling choice: Anneal models allocations in a non-reusing symbolic address
  space (aligned with `lean-miri`'s `offsetIsAddr = false`), so two dead tags
  cannot accidentally resolve to the same runtime address via stack-slot reuse
  when their offsets differ; when their offsets are equal, the two dead tags
  may still stem from the same or different generations, so the check fails
  closed `.unsupported`. Dead tags carrying non-empty projections ALWAYS fail
  closed `.unsupported` without calling `borrowPlaceByteOffset?`: after a frame
  pop or tail call, the same `(targetFrameDepth, targetLocal)` may name an
  unrelated local of a later callee (e.g. a tuple where the dead frame held a
  union), so reading current declarations could fabricate distinct field
  offsets and falsely report `.ub` on equal-address dangling pointers.
- Provenance tags are resolved in `s.memory.borrows` BEFORE `AllocId`s are
  resolved in `s.memory.globals` (matching `resolveLiveMemEndpoint` and
  `Places.ptrAddress?`), because stack tags and captured global `AllocId`s share
  one numeric namespace (modeling choice). A stack pointer and a global pointer
  never share an allocation, so mixing them at distinct addresses is `.ub`.

Reference (`core::ptr::const_ptr::<impl *const T>::offset_from` documentation,
`library/core/src/ptr/const_ptr.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L545-L552>

> "/// If any of the following conditions are violated, the result is Undefined Behavior:
> ///
> /// * `self` and `origin` must either
> ///
> ///   * point to the same address, or
> ///   * both be [derived from][crate::ptr#provenance] a pointer to the same [allocation], and the memory range between
> ///     the two pointers must be in bounds of that object."
-/
def resolvePtrOffsetFromOffsets
    (s : MachineState)
    (locals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (ptrVal baseVal : Value) :
    MemOpRes (Nat × Nat) :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  let modW := scalarModulus ptrBytes
  let intAddrOf : Value → Option Nat := fun v =>
    match v with
    | .scalar sc =>
      match Bool.and (Nat.beq sc.sizeBytes ptrBytes) (Nat.blt sc.bits modW) with
      | true => .some sc.bits
      | false => .none
    | .ptr p sz =>
      match Bool.and (Nat.beq sz ptrBytes)
        (Bool.and (Nat.beq p.allocId 0)
          (Bool.and (Bool.not (isBackedPtr s.memory p)) (Nat.blt p.offsetBytes modW))) with
      | true => .some p.offsetBytes
      | false => .none
    | _ => .none
  match intAddrOf ptrVal, intAddrOf baseVal with
  | .some a1, .some a2 =>
    match Nat.beq a1 a2 with
    | true => .ok (0, 0)
    | false => .ub
  | .some _, .none => .ub
  | .none, .some _ => .ub
  | .none, .none =>
    match ptrVal, baseVal with
    | .ptr p1 sz1, .ptr p2 sz2 =>
      match Bool.and (Nat.beq sz1 ptrBytes) (Nat.beq sz2 ptrBytes) with
      | false => .ub
      | true =>
        match
          Bool.or
            (Bool.and (Nat.beq p1.allocId 0) (Bool.not (isBackedPtr s.memory p1)))
            (Bool.and (Nat.beq p2.allocId 0) (Bool.not (isBackedPtr s.memory p2)))
        with
        | true => .ub
        | false =>
          match Bool.and (Nat.beq p1.allocId p2.allocId) (Nat.beq p1.offsetBytes p2.offsetBytes) with
        | true => .ok (0, 0)
        | false =>
          match
            lookupBorrow s.memory.borrows p1.tag,
            lookupBorrow s.memory.borrows p2.tag
          with
          | .some e1, .some e2 =>
            match
              Bool.and
                (Nat.beq e1.targetFrameDepth e2.targetFrameDepth)
                (Nat.beq e1.targetLocal e2.targetLocal)
            with
            | false => .ub
            | true =>
              match e1.allocDead, e2.allocDead with
              | true, true =>
                match Nat.beq e1.tag e2.tag with
                | true => .ub
                | false =>
                  match
                    stripTransparentProjections e1.targetProjection,
                    stripTransparentProjections e2.targetProjection
                  with
                  | .nil, .nil =>
                    let modW := scalarModulus ptrBytes
                    match Nat.beq (Nat.mod p1.offsetBytes modW) (Nat.mod p2.offsetBytes modW) with
                    | false => .ub
                    | true => .unsupported
                  | _, _ => .unsupported
              | true, false => .ub
              | false, true => .ub
              | false, false =>
                match
                  borrowPlaceByteOffset?
                    locals s.memory.callerLocals bodyLocalDecls bodyLayouts e1 s.memory.callStack,
                  borrowPlaceByteOffset?
                    locals s.memory.callerLocals bodyLocalDecls bodyLayouts e2 s.memory.callStack
                with
                | .some po1, .some po2 =>
                  let eff1 := Nat.add po1 p1.offsetBytes
                  let eff2 := Nat.add po2 p2.offsetBytes
                  match Nat.beq eff1 eff2 with
                  | true => .ok (0, 0)
                  | false =>
                    match
                      readFrameLocalSlot
                        locals s.memory.callStack s.memory.callerLocals
                        e1.targetFrameDepth e1.targetLocal
                    with
                    | .none => .ub
                    | .some .dead => .ub
                    | .some slot =>
                      let (targetDecls, targetLayouts) : List LocalDecl × LayoutTable :=
                        match
                          frameLocalDeclsAndLayoutsAtDepth
                            s.memory.callStack bodyLocalDecls bodyLayouts e1.targetFrameDepth
                        with
                        | .some pair => pair
                        | .none =>
                          foreignFrameDeclsAndLayouts
                            s.memory.callStack bodyLayouts e1.targetFrameDepth e1.targetLocal
                      let rootTy? : Option Ty :=
                        match get? targetDecls e1.targetLocal with
                        | .some decl => .some decl.ty
                        | .none => .none
                      let allocSize? : Option Nat :=
                        match rootTy? with
                        | .some rTy => exactTyByteSize? targetDecls targetLayouts rTy
                        | .none =>
                          match slot with
                          | .init rootVal =>
                            match untypedValueHasExactByteImage defaultCodecFuel rootVal with
                            | true => valueDefaultByteSize rootVal
                            | false => .none
                          | _ => .none
                      match allocSize? with
                      | .none => .unsupported
                      | .some allocSize =>
                        match Bool.and (Nat.ble eff1 allocSize) (Nat.ble eff2 allocSize) with
                        | true => .ok (eff1, eff2)
                        | false => .ub
                | _, _ => .unsupported
          | .some _, .none => .ub
          | .none, .some _ => .ub
          | .none, .none =>
            match
              lookupGlobalAlloc s.memory.globals p1.allocId,
              lookupGlobalAlloc s.memory.globals p2.allocId
            with
            | .some g1, .some g2 =>
              match Nat.beq g1.allocId g2.allocId with
              | false => .ub
              | true =>
                match Nat.beq p1.offsetBytes p2.offsetBytes with
                | true => .ok (0, 0)
                | false =>
                  let gSize := length g1.bytes
                  match Bool.and (Nat.ble p1.offsetBytes gSize) (Nat.ble p2.offsetBytes gSize) with
                  | true => .ok (p1.offsetBytes, p2.offsetBytes)
                  | false => .ub
            | _, _ => .ub
    | _, _ => .ub

/--
Compute the element-scaled signed (`unsigned = false`, `isize`) or unsigned
(`unsigned = true`, `usize`) pointer distance `(ptrOff - baseOff) / elemSize`,
rejecting ZST (`elemSize == 0`), oversized `elemSize > isize::MAX`,
out-of-range byte distance (`|dist| > isize::MAX`, which rejects `isize::MIN`
as UB), negative distance when `unsigned = true`, and non-exact divisibility.

Reference (`library/core/src/ptr/const_ptr.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L553-L574>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L665-L679>

> "/// * The distance between the pointers, in bytes, must be an exact multiple
> ///   of the size of `T`.
> ///
> /// As a consequence, the absolute distance between the pointers, in bytes, computed on
> /// mathematical integers (without \"wrapping around\"), cannot overflow an `isize`."

> "/// - The distance between the pointers must be non-negative (`self >= origin`)
> ...
> /// Importantly, despite the return type of this method being able to represent
> /// a larger offset, it's still *not permitted* to pass pointers which differ
> /// by more than `isize::MAX` *bytes*."
-/
def evalPtrOffsetFromDistance
    (ptrBytes : Nat)
    (unsigned : Bool)
    (elemSize ptrOff baseOff : Nat) :
    Option ScalarInt :=
  let modW := scalarModulus ptrBytes
  let isizeMax := Nat.sub (Nat.div modW 2) 1
  match Bool.or (Nat.beq elemSize 0) (Bool.not (Nat.ble elemSize isizeMax)) with
  | true => .none
  | false =>
    match Nat.ble baseOff ptrOff with
    | true =>
      let dist := Nat.sub ptrOff baseOff
      match Bool.and (Nat.ble dist isizeMax) (Nat.beq (Nat.mod dist elemSize) 0) with
      | true => .some ⟨Nat.div dist elemSize, ptrBytes⟩
      | false => .none
    | false =>
      match unsigned with
      | true => .none
      | false =>
        let negDist := Nat.sub baseOff ptrOff
        match Bool.and (Nat.ble negDist isizeMax) (Nat.beq (Nat.mod negDist elemSize) 0) with
        | true =>
          let q := Nat.div negDist elemSize
          .some ⟨Nat.sub modW q, ptrBytes⟩
        | false => .none

/--
Evaluate a direct call to `core::intrinsics::ptr_offset_from<T>(ptr, base) ->
isize` (`unsigned = false`) or `core::intrinsics::ptr_offset_from_unsigned<T>(
ptr, base) -> usize` (`unsigned = true`). Uses `withAlign := false` when gating
`T`'s structural size because element alignment is never required.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2268-L2278>

> "pub const unsafe fn ptr_offset_from<T>(ptr: *const T, base: *const T) -> isize;"
> "pub const unsafe fn ptr_offset_from_unsigned<T>(ptr: *const T, base: *const T) -> usize;"
-/
def evalPtrOffsetFromCall
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx)
    (unsigned : Bool) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  let isizeMax := Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1
  match argVals with
  | ptrVal :: baseVal :: .nil =>
    match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
    | .none =>
      match
        isNullThinPtr s.memory ptrBytes ptrVal,
        isNullThinPtr s.memory ptrBytes baseVal
      with
      | .none, _ => MirStepNode.fail .ub
      | _, .none => MirStepNode.fail .ub
      | _, _ => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
    | .some elemTy =>
      match isUnsizedRigidTy 8 elemTy with
      | true => MirStepNode.unsupported
      | false =>
        match
          isNullThinPtr s.memory ptrBytes ptrVal,
          isNullThinPtr s.memory ptrBytes baseVal
        with
        | .none, _ => MirStepNode.fail .ub
        | _, .none => MirStepNode.fail .ub
        | .some _, .some _ =>
          match
            rigidTyLayoutDeterminedAux bodyLocalDecls bodyLayouts false 8 elemTy,
            exactRigidTyByteSize? bodyLocalDecls bodyLayouts elemTy
          with
          | true, .some elemSize =>
            match Bool.or (Nat.beq elemSize 0) (Bool.not (Nat.ble elemSize isizeMax)) with
            | true => MirStepNode.fail .ub
            | false =>
              match
                resolvePtrOffsetFromOffsets s locals' bodyLocalDecls bodyLayouts ptrVal baseVal
              with
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
              | .ok (ptrOff, baseOff) =>
                match evalPtrOffsetFromDistance ptrBytes unsigned elemSize ptrOff baseOff with
                | .none => MirStepNode.fail .ub
                | .some retSc =>
                  writeIntrinsicReturnWithProtectors
                    s bodyLocalDecls bodyLayouts locals' destination targetOpt (.scalar retSc)
          | _, _ => MirStepNode.unsupported
  | _ => MirStepNode.fail .ub

/--
Resolve `(allocAlign, placeOff)` for a provenance-carrying `ProvenancePtr` `p`
for alignment-invariant symbolic `ptr_mask`: returns `.some (align, placeOff)`
only when the root allocation's alignment is a validated positive power of two
(using `exactRootAllocAlign?` for stack allocations and `Align.isPowerOfTwoBytes`
for global allocations).

Resolution order and liveness (modeling choices, not documented Rust
guarantees):
- `p.tag` is looked up in `s.memory.borrows` BEFORE `p.allocId` is looked up in
  `s.memory.globals`, matching `resolveLiveMemEndpoint`, `checkPtrArgAligned`,
  and `Places.ptrAddress?`. Stack provenance tags (`1, 2, ...`) and captured
  global `AllocId`s share one numeric namespace, so a globals-first lookup could
  attribute a global's alignment to a colliding stack tag.
- A borrow whose allocation is deallocated (`entry.allocDead = true`, set by
  `StorageDead` and by frame teardown) yields `.none`: after a frame pop the same
  `(targetFrameDepth, targetLocal)` may name a local of a different callee whose
  declaration (and hence alignment) is unrelated to the dead allocation.

The symbolic-base criterion relies on the allocation's base address being a
multiple of its alignment.

Reference (The Rust Reference 1.98.0, "Type Layout — Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The alignment of a value specifies what addresses are valid to store the value at. A value of alignment n must only be stored at an address that is a multiple of n."
-/
def resolvePtrAllocAlignAndPlaceOff
    (s : MachineState)
    (locals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (p : ProvenancePtr) :
    Option (Nat × Nat) :=
  match lookupBorrow s.memory.borrows p.tag with
  | .some entry =>
    match entry.allocDead with
    | true => .none
    | false =>
      match
        borrowPlaceByteOffset?
          locals s.memory.callerLocals bodyLocalDecls bodyLayouts entry s.memory.callStack
      with
      | .none => .none
      | .some placeOff =>
        let (targetDecls, targetLayouts) : List LocalDecl × LayoutTable :=
          match
            frameLocalDeclsAndLayoutsAtDepth
              s.memory.callStack bodyLocalDecls bodyLayouts entry.targetFrameDepth
          with
          | .some pair => pair
          | .none =>
            foreignFrameDeclsAndLayouts
              s.memory.callStack bodyLayouts entry.targetFrameDepth entry.targetLocal
        match get? targetDecls entry.targetLocal with
        | .none => .none
        | .some rootDecl =>
          match exactRootAllocAlign? targetDecls targetLayouts rootDecl.ty with
          | .some rootAlign => .some (rootAlign, placeOff)
          | .none => .none
  | .none =>
    match lookupGlobalAlloc s.memory.globals p.allocId with
    | .some gAlloc =>
      match Align.isPowerOfTwoBytes gAlloc.align with
      | true => .some (gAlloc.align.bytes, 0)
      | false => .none
    | .none => .none

/--
Evaluate a direct call to `core::intrinsics::ptr_mask<T>(ptr: *const T, mask:
usize) -> *const T`:
- Computes `ptr.with_addr(ptr.addr() & mask)`, preserving `ProvenancePtr`
  (`allocId` / `tag`) WITHOUT modifying `Memory.exposedAllocIds` (per strict
  provenance / `ucg#630` / `rust#166220`).
- Integer pointers (`.scalar` or unbacked `allocId = 0`) mask directly.
- Provenance-carrying thin pointers succeed on the universal identity mask
  `mask == 2^W - 1` even when `allocAlign` is unknown, and in symbolic-base mode
  succeed whenever `(2^W - 1) - mask < allocAlign` (guaranteeing base-address
  invariance `(baseAddr + relOff) & mask = baseAddr + (relOff & mask)` for every
  `allocAlign`-aligned base address) and `relOff & mask >= placeOff`, failing
  closed `.unsupported` otherwise.
- Wide pointers and provenance-carrying `usize` masks fail closed `.unsupported`
  after validating malformed pointer/mask arguments as `.ub`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L944-L954>

> "/// Masks out bits of the pointer according to a mask.
> ///
> /// Note that, unlike most intrinsics, this is safe to call;
> /// it does not require an `unsafe` block.
> /// Therefore, implementations must not require the user to uphold
> /// any safety invariants.
> ...
> pub fn ptr_mask<T>(ptr: *const T, mask: usize) -> *const T;"

Reference (`library/core/src/ptr/const_ptr.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L489-L494>

> "/// Masks out bits of the pointer according to a mask.
> ///
> /// This is convenience for `ptr.map_addr(|a| a & mask)`.
> ///
> /// For non-`Sized` pointees this operation changes only the data pointer,
> /// leaving the metadata untouched."
-/
def evalPtrMaskCall
    (s : MachineState)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  let ptrBits := Nat.mul 8 ptrBytes
  let modW := scalarModulus ptrBytes
  let allOnes := Nat.sub modW 1
  match argVals with
  | ptrVal :: maskVal :: .nil =>
    match ptrVal with
    | .aggregate 0 (dVal :: mVal :: .nil) =>
      match
        isNullThinPtr s.memory ptrBytes dVal,
        isValidWidePtrMetaValForWidth s.memory ptrBytes mVal,
        decodeUsizeArg? s.memory ptrBytes maskVal
      with
      | .none, _, _ => MirStepNode.fail .ub
      | _, false, _ => MirStepNode.fail .ub
      | _, _, .ub => MirStepNode.fail .ub
      | .some _, true, _ => MirStepNode.unsupported
    | .scalar sc =>
      match Bool.and (Nat.beq sc.sizeBytes ptrBytes) (Nat.blt sc.bits modW) with
      | false => MirStepNode.fail .ub
      | true =>
        match decodeUsizeArg? s.memory ptrBytes maskVal with
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
        | .ok maskBits =>
          let masked := bitwiseAndBits ptrBits sc.bits maskBits
          writeIntrinsicReturnWithProtectors
            s bodyLocalDecls bodyLayouts locals' destination targetOpt (.scalar ⟨masked, ptrBytes⟩)
    | .ptr p sz =>
      match Nat.beq sz ptrBytes with
      | false => MirStepNode.fail .ub
      | true =>
        let isUnbackedInt :=
          Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr s.memory p))
        match Bool.and isUnbackedInt (Bool.not (Nat.blt p.offsetBytes modW)) with
        | true => MirStepNode.fail .ub
        | false =>
          match decodeUsizeArg? s.memory ptrBytes maskVal with
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
          | .ok maskBits =>
            let maskW := Nat.mod maskBits modW
            match isUnbackedInt with
            | true =>
              let masked := bitwiseAndBits ptrBits p.offsetBytes maskW
              writeIntrinsicReturnWithProtectors
                s bodyLocalDecls bodyLayouts locals' destination targetOpt
                (.ptr { allocId := 0, offsetBytes := masked } ptrBytes)
            | false =>
              match Bool.and (Nat.beq maskW allOnes) (Nat.blt p.offsetBytes modW) with
              | true =>
                writeIntrinsicReturnWithProtectors
                  s bodyLocalDecls bodyLayouts locals' destination targetOpt (.ptr p ptrBytes)
              | false =>
                match resolvePtrAllocAlignAndPlaceOff s locals' bodyLocalDecls bodyLayouts p with
                | .none => MirStepNode.unsupported
                | .some (allocAlign, placeOff) =>
                  let relOff := Nat.add placeOff p.offsetBytes
                  match
                    Bool.and
                      (Nat.ble allocAlign (signedHalfModulus ptrBytes))
                      (Bool.and
                        (Nat.blt (Nat.sub allOnes maskW) allocAlign)
                        (Nat.blt relOff modW))
                  with
                  | false => MirStepNode.unsupported
                  | true =>
                    let maskedRel := bitwiseAndBits ptrBits relOff maskW
                    match Nat.blt maskedRel placeOff with
                    | true => MirStepNode.unsupported
                    | false =>
                      let newOff := Nat.sub maskedRel placeOff
                      writeIntrinsicReturnWithProtectors
                        s bodyLocalDecls bodyLayouts locals' destination targetOpt
                        (.ptr { p with offsetBytes := newOff } ptrBytes)
    | _ => MirStepNode.fail .ub
  | _ => MirStepNode.fail .ub

/--
Resolve the `Ty` of `black_box<T>(dummy: T)` preserving any resolved field
`layoutIdx` from `operandTyResolved` on `dummyOp` when consistent with
`target.typeArgs` (stripping synthetic `layoutIdx = 0` on `.zeroSized`
constants such as `const_eval_select` dummy operands so unrelated `entries[0]`
layouts are never adopted).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2339-L2345>

> "pub const fn black_box<T>(dummy: T) -> T;"
-/
def resolveBlackBoxTy?
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand) :
    Option Ty :=
  let opTy? : Option Ty :=
    match argOps with
    | dummyOp :: _ =>
      match dummyOp with
      | .constant { ty := cTy, val := .zeroSized } =>
        match Nat.beq cTy.layoutIdx 0 with
        | true => .some { kind := cTy.kind, layoutIdx := unresolvedLayoutIdx bodyLayouts }
        | false => .some cTy
      | _ => operandTyResolved bodyLocalDecls bodyLayouts dummyOp
    | .nil => .none
  match target.typeArgs with
  | argTy :: _ =>
    match opTy? with
    | .some opTy =>
      match rigidTyEq opTy.kind argTy with
      | true => .some opTy
      | false => .some { kind := argTy, layoutIdx := unresolvedLayoutIdx bodyLayouts }
    | .none => .some { kind := argTy, layoutIdx := unresolvedLayoutIdx bodyLayouts }
  | .nil => opTy?

/--
Evaluate a direct call to `core::intrinsics::black_box<T>(dummy: T) -> T`:
validates `dummy` against `T` via 3-way `validateBlackBoxValue` (rejecting
invalid `bool`/`char`, wrong-width or out-of-range scalars, null thin/wide
references and `fn()`, uninhabited-pointee `&!`, null `dyn` vtables, and
oversized slice lengths as `.ub`, and failing closed `.unsupported` on unknown
or unsized `T`, char-shaped surrogates in layout scalars, scalar provenance, and
unvalidated multi-variant enums), then writes `dummy` unchanged to `destination`
via `writeIntrinsicReturnWithProtectors`.

Reference (`library/core/src/intrinsics/mod.rs` and `library/core/src/hint.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2339-L2345>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/hint.rs#L315-L321>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/hint.rs#L486>

> "pub const fn black_box<T>(dummy: T) -> T;"

> "/// An identity function that *__hints__* to the compiler to be maximally pessimistic about what
> /// `black_box` could do."

> "/// During constant evaluation, `black_box` is treated as a no-op."
-/
def evalBlackBoxCall
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  match argVals with
  | dummyVal :: .nil =>
    match resolveBlackBoxTy? target bodyLocalDecls bodyLayouts argOps with
    | .none => MirStepNode.unsupported
    | .some dummyTy =>
      match
        validateBlackBoxValue
          s.memory bodyLocalDecls bodyLayouts defaultCodecFuel dummyTy dummyVal
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .valid =>
        writeIntrinsicReturnWithProtectors
          s bodyLocalDecls bodyLayouts locals' destination targetOpt dummyVal
  | _ => MirStepNode.fail .ub

/--
Dispatch the 8 core memory & pointer intrinsics (`copy`, `compare_bytes`,
`raw_eq`, `typed_swap_nonoverlapping`, `ptr_offset_from`,
`ptr_offset_from_unsigned`, `ptr_mask`, `black_box`), returning `.none` for all
other `RustIntrinsicKind` variants so `evalDirectRustIntrinsic?` and
`const_eval_select` fall through to existing evaluators.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>

> "Compiler intrinsics."
-/
@[reducible]
def evalCoreMemPtrIntrinsicCall?
    (kind : RustIntrinsicKind)
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    Option MirStepNode :=
  match kind with
  | .copy =>
    .some
      (evalCopyCall
        s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt)
  | .compareBytes =>
    .some
      (evalCompareBytesCall
        s bodyLocalDecls bodyLayouts argVals locals' destination targetOpt)
  | .rawEq =>
    .some
      (evalRawEqCall
        s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt)
  | .typedSwapNonOverlapping =>
    .some
      (evalTypedSwapNonOverlappingCall
        s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt)
  | .ptrOffsetFrom =>
    .some
      (evalPtrOffsetFromCall
        s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt false)
  | .ptrOffsetFromUnsigned =>
    .some
      (evalPtrOffsetFromCall
        s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt true)
  | .ptrMask =>
    .some
      (evalPtrMaskCall
        s bodyLocalDecls bodyLayouts argVals locals' destination targetOpt)
  | .blackBox =>
    .some
      (evalBlackBoxCall
        s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt)
  | _ => .none

/--
Convert a normal return step `.tau (.running _)` of a returning intrinsic called
through a diverging MIR call terminator (`target = .none`) into immediate
undefined behavior (`MirStepNode.fail .ub`), while preserving `.unsupported` and
other faults/outcomes unchanged.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L800-L814>

> "Call {
> ...
>     target: Option<BasicBlock>,"
-/
@[reducible]
def divergingCallReturnStep : MirStepNode → MirStepNode
  | .tau (.running _) => MirStepNode.fail .ub
  | other => other

/--
Dispatch a direct diverging MIR call (`target = .none`) to an inline-modeled
compiler intrinsic:
- `core::intrinsics::const_eval_select` fails closed `MirStepNode.unsupported`
  because its runtime callee `called_at_rt` may validly diverge (`-> !`).
- The 8 core memory & pointer intrinsics execute with `targetOpt = .none`
  (preserving `.unsupported` / `.fail .ub` and faulting `.fail .ub` upon normal
  return).
- `exact_div`, `copy_nonoverlapping`, `write_bytes`, and all other returning
  intrinsics execute and turn any normal return step `.tau (.running _)` into
  `MirStepNode.fail .ub` via `divergingCallReturnStep` while preserving
  `.unsupported` and faults.
- Non-intrinsic `DefPath`s return `.none` so `evalTerminator` falls through to
  `MirStepNode.extCall`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L800-L814>

> "Call {
> ...
>     target: Option<BasicBlock>,"
-/
@[reducible]
def evalDivergingRustIntrinsic?
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place) :
    Option MirStepNode :=
  match isDirectExactDivTarget target with
  | true =>
    .some
      (match argVals with
       | .scalar lhs :: .scalar rhs :: .nil =>
         match resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps with
         | .none => MirStepNode.unsupported
         | .some isSigned =>
           match evalExactDiv lhs rhs locals' s.memory isSigned with
           | .ok _ _ _ => MirStepNode.fail .ub
           | .ub => MirStepNode.fail .ub
           | .unsupported => MirStepNode.unsupported
       | _ => MirStepNode.fail .ub)
  | false =>
    match classifyRustIntrinsic? target.defPath with
    | .none => .none
    | .some .constEvalSelect => .some MirStepNode.unsupported
    | .some .copyNonOverlapping =>
      .some
        (divergingCallReturnStep
          (evalCopyNonOverlappingCall
            s bodyLocalDecls bodyLayouts argOps argVals locals' destination 0))
    | .some .writeBytes =>
      .some
        (divergingCallReturnStep
          (evalWriteBytesCall
            s target bodyLocalDecls bodyLayouts argOps argVals locals' destination 0))
    | .some kind =>
      match
        evalCoreMemPtrIntrinsicCall?
          kind s target bodyLocalDecls bodyLayouts argOps argVals locals' destination .none
      with
      | .some stepNode => .some stepNode
      | .none =>
        .some
          (divergingCallReturnStep
            (evalNonSelectIntrinsicCall
              kind s target bodyLocalDecls bodyLayouts argOps argVals locals' destination 0))

/--
Dispatch a direct (`target.isIndirect = false`) call to a
`CallConv.rustIntrinsic` compiler intrinsic in `evalTerminator` when
`classifyRustIntrinsic? target.defPath` returns `.some kind`: the runtime
dispatch of `const_eval_select`, the call-form memory intrinsics
(`evalCopyNonOverlappingCall`, `evalWriteBytesCall`), the 8 core memory &
pointer intrinsics (`evalCoreMemPtrIntrinsicCall?`), or a value-returning
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
                       match evalExactDiv lhs rhs locals' s.memory isSigned with
                       | .ok retVal _ _ =>
                         writeIntrinsicReturn s locals' destination targetBb retVal
                       | .ub => MirStepNode.fail .ub
                       | .unsupported => MirStepNode.unsupported
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
                     match
                       evalCoreMemPtrIntrinsicCall?
                         rtKind
                         s
                         rtTarget'
                         bodyLocalDecls
                         bodyLayouts
                         selectArgOps
                         unpackedArgs
                         locals'
                         destination
                         (.some targetBb)
                     with
                     | .some stepNode => stepNode
                     | .none =>
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
      (match
         evalCoreMemPtrIntrinsicCall?
           kind
           s
           target
           bodyLocalDecls
           bodyLayouts
           argOps
           argVals
           locals'
           destination
           (.some targetBb)
       with
       | .some stepNode => stepNode
       | .none =>
         evalNonSelectIntrinsicCall
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
              match evalExactDiv lhs rhs locals' s.memory isSigned with
              | .ok retVal localsAfter memAfter =>
                writeIntrinsicReturn { s with memory := memAfter } localsAfter destination targetBb retVal
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

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L724-L800>

> "/// Returns from the function.
> ...
> Return,
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
        | .nil => MirStepNode.retNormal retVal { s.memory with borrows := borrows₁ }
        | caller :: restStack =>
          match caller.isDiverging with
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
    match get? s.frame.locals place.local_ with
    | .none => MirStepNode.fail .ub
    | .some .dead => MirStepNode.fail .ub
    | .some slot =>
      match place.projection, stripLeadingOpaqueCast place.projection with
      | .nil, _ =>
        match set? s.frame.locals place.local_ .uninit with
        | .some locals' =>
          MirStepNode.step {
            s with
            frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
          }
        | .none => MirStepNode.fail .ub
      | .opaqueCast _ :: _, .nil =>
        match set? s.frame.locals place.local_ .uninit with
        | .some locals' =>
          MirStepNode.step {
            s with
            frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
          }
        | .none => MirStepNode.fail .ub
      | _ :: _, _ =>
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
                match evalExactDiv lhs rhs locals' s.memory isSigned with
                | .ok retVal localsAfter memAfter =>
                  writeIntrinsicReturn { s with memory := memAfter } localsAfter destination targetBb retVal
                | .ub => MirStepNode.fail .ub
                | .unsupported => MirStepNode.unsupported
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
          -- `called_at_rt` returns `!`) fails closed with `MirStepNode.unsupported`
          -- inside `evalDivergingRustIntrinsic?`, while diverging calls to
          -- returning intrinsics turn normal returns into `MirStepNode.fail .ub`.
          -- Captured MIR never contains `const_eval_select`, because `rustc`
          -- replaces it with a direct call to `called_at_rt` before `optimized_mir`.
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
                  match
                    evalDivergingRustIntrinsic?
                      s
                      target
                      bodyLocalDecls
                      bodyLayouts
                      argOps
                      argVals
                      locals'
                      destination
                  with
                  | .some stepNode => stepNode
                  | .none =>
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

end Trusted.Rustc.V2026_08_01.MirSemantics
