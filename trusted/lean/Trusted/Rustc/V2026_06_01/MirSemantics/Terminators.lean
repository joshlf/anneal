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
        (callStack := s.memory.callStack)
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
  match dst.projection with
  | .nil =>
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
  | .deref :: restProj =>
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
  | proj :: rest =>
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

Every variant except `.constEvalSelect` and the memory intrinsics is
value-returning: its result depends only on the argument values and is written
to the call destination (`evalNonSelectIntrinsicCall`). `.copyNonOverlapping`
and `.writeBytes` are the call forms of the memory intrinsics, which read and
write memory through their pointer arguments and return `()`
(`evalCopyNonOverlappingCall`, `evalWriteBytesCall`). The seven volatile memory
intrinsics (`.unalignedVolatileLoad`, `.unalignedVolatileStore`,
`.volatileLoad`, `.volatileStore`, `.volatileCopyNonOverlappingMemory`,
`.volatileCopyMemory`, `.volatileSetMemory`; `isVolatileMemIntrinsicKind`) load
from or store to memory through their pointer arguments
(`evalVolatileMemIntrinsicCall`: `evalRawPtrLoadCall`, `evalRawPtrStoreCall`,
`evalVolatileCopyMemoryCall`, `evalVolatileSetMemoryCall`).

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

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the volatile intrinsics):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L26-L31>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L956-L1022>

> "//! # Volatiles
> //!
> //! The volatile intrinsics provide operations intended to act on I/O
> //! memory, which are guaranteed to not be reordered by the compiler
> //! across other volatile intrinsics. See [`read_volatile`][ptr::read_volatile]
> //! and [`write_volatile`][ptr::write_volatile]."

> "pub unsafe fn volatile_copy_nonoverlapping_memory<T>(dst: *mut T, src: *const T, count: usize);"

> "pub unsafe fn volatile_copy_memory<T>(dst: *mut T, src: *const T, count: usize);"

> "pub unsafe fn volatile_set_memory<T>(dst: *mut T, val: u8, count: usize);"

> "pub unsafe fn volatile_load<T>(src: *const T) -> T;"

> "pub unsafe fn volatile_store<T>(dst: *mut T, val: T);"

> "pub unsafe fn unaligned_volatile_load<T>(src: *const T) -> T;"

> "pub unsafe fn unaligned_volatile_store<T>(dst: *mut T, val: T);"

Modeling choice: the guarantee that volatile operations are not reordered or
elided concerns compilation; the model executes them as ordinary steps.
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
  /-- `core::intrinsics::unaligned_volatile_load`: volatile load through a
  pointer that need not be aligned (`evalRawPtrLoadCall`). -/
  | unalignedVolatileLoad : RustIntrinsicKind
  /-- `core::intrinsics::unaligned_volatile_store`: volatile store through a
  pointer that need not be aligned (`evalRawPtrStoreCall`). -/
  | unalignedVolatileStore : RustIntrinsicKind
  /-- `core::intrinsics::volatile_load`: volatile load through an aligned
  pointer (`evalRawPtrLoadCall`). -/
  | volatileLoad : RustIntrinsicKind
  /-- `core::intrinsics::volatile_store`: volatile store through an aligned
  pointer (`evalRawPtrStoreCall`). -/
  | volatileStore : RustIntrinsicKind
  /-- `core::intrinsics::volatile_copy_nonoverlapping_memory`: volatile copy of
  `count` elements between non-overlapping regions, with arguments `(dst, src,
  count)` (`evalVolatileCopyMemoryCall`). -/
  | volatileCopyNonOverlappingMemory : RustIntrinsicKind
  /-- `core::intrinsics::volatile_copy_memory`: volatile copy of `count`
  elements between possibly overlapping regions, with arguments `(dst, src,
  count)` (`evalVolatileCopyMemoryCall`). -/
  | volatileCopyMemory : RustIntrinsicKind
  /-- `core::intrinsics::volatile_set_memory`: volatile fill of `count`
  elements with a byte value (`evalVolatileSetMemoryCall`). -/
  | volatileSetMemory : RustIntrinsicKind

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

The seven volatile memory intrinsics are recognized at their canonical
`core::intrinsics::*` paths. Their `core::ptr` counterparts
(`core::ptr::read_volatile`, `core::ptr::write_volatile`,
`core::ptr::read_unaligned`, `core::ptr::write_unaligned`) are ordinary
functions and are not classified here (`evalUnlinkedPtrAccessCall?` models a
direct call to one of them only when no body is linked).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L956-L1022>

> "pub unsafe fn volatile_copy_nonoverlapping_memory<T>(dst: *mut T, src: *const T, count: usize);"

> "pub unsafe fn volatile_copy_memory<T>(dst: *mut T, src: *const T, count: usize);"

> "pub unsafe fn volatile_set_memory<T>(dst: *mut T, val: u8, count: usize);"

> "pub unsafe fn volatile_load<T>(src: *const T) -> T;"

> "pub unsafe fn volatile_store<T>(dst: *mut T, val: T);"

> "pub unsafe fn unaligned_volatile_load<T>(src: *const T) -> T;"

> "pub unsafe fn unaligned_volatile_store<T>(dst: *mut T, val: T);"
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
                                                        match stringEq defPath "core::intrinsics::unaligned_volatile_load" with
                                                        | true => .some .unalignedVolatileLoad
                                                        | false =>
                                                          match stringEq defPath "core::intrinsics::unaligned_volatile_store" with
                                                          | true => .some .unalignedVolatileStore
                                                          | false =>
                                                            match stringEq defPath "core::intrinsics::volatile_load" with
                                                            | true => .some .volatileLoad
                                                            | false =>
                                                              match stringEq defPath "core::intrinsics::volatile_store" with
                                                              | true => .some .volatileStore
                                                              | false =>
                                                                match stringEq defPath "core::intrinsics::volatile_copy_nonoverlapping_memory" with
                                                                | true => .some .volatileCopyNonOverlappingMemory
                                                                | false =>
                                                                  match stringEq defPath "core::intrinsics::volatile_copy_memory" with
                                                                  | true => .some .volatileCopyMemory
                                                                  | false =>
                                                                    match stringEq defPath "core::intrinsics::volatile_set_memory" with
                                                                    | true => .some .volatileSetMemory
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
Complete a call-form memory intrinsic (`RustIntrinsicKind.copyNonOverlapping`,
`RustIntrinsicKind.writeBytes`, and the tracked stack case of
`RustIntrinsicKind.volatileCopyNonOverlappingMemory` /
`RustIntrinsicKind.volatileCopyMemory`) whose memory effect `node` was computed
by the statement-level semantics: on `MirStepNode.step s'`, keep the frame
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
Runtime shape of a thin raw-pointer argument (`*const T` / `*mut T` with
`T: Sized`) of the raw-pointer memory accesses modeled inline
(`evalRawPtrLoadCall`, `evalRawPtrStoreCall`, `evalVolatileCopyMemoryCall`,
`evalVolatileSetMemoryCall`): a pointer value carrying a provenance slot
(`Value.ptr ptr ptrBytes`), or a provenance-less address
(`Value.scalar ⟨addr, ptrBytes⟩`, as produced by `ptr::null`,
`ptr::without_provenance`, and unexposed integer-to-pointer casts).

Reference (`core::ptr::read_volatile` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2040-L2050>

> "/// - Volatile operations, however, may also be used to access memory that is _outside_ of any Rust
> ///   allocation. In this use-case, the pointer does *not* have to be [valid] for reads. This is
> ///   typically used for CPU and peripheral registers that must be accessed via an I/O memory
> ///   mapping, most commonly at fixed addresses reserved by the hardware. These often have special
> ///   semantics associated to their manipulation, and cannot be used as general purpose memory.
> ///   Here, any address value is possible, including 0 and [`usize::MAX`], so long as the semantics
> ///   of such a read are well-defined by the target hardware. The provenance of the pointer is
> ///   irrelevant, and it can be created with [`without_provenance`]. The access must not trap. It
> ///   can cause side-effects, but those must not affect Rust-allocated memory in any way. This
> ///   access is still not considered [atomic], and as such it cannot be used for inter-thread
> ///   synchronization."

Modeling choice: the two constructors are Anneal's two runtime representations
of a thin pointer; the quoted passage only establishes that a pointer without
provenance is a meaningful argument of a volatile access.
-/
inductive RawPtrArg : Type where
  /-- A pointer value with provenance slot `ptr` (`Value.ptr ptr ptrBytes`). -/
  | prov (ptr : ProvenancePtr) : RawPtrArg
  /-- A provenance-less address `addr` (`Value.scalar ⟨addr, ptrBytes⟩`). -/
  | addr (addr : Nat) : RawPtrArg

/--
Classify the evaluated value of a thin raw-pointer argument on a target whose
pointers are `ptrBytes` wide: `Value.ptr ptr ptrBytes` is `.prov ptr`, and a
`ptrBytes`-wide scalar is the provenance-less address `.addr bits`. Every other
value (`.unit`, a wide-pointer aggregate, `.uninit`, or a pointer or scalar of
another width) is not a thin pointer and yields `.none`, which callers turn
into `MirStepNode.fail .ub`: the intrinsics modeled here take `*const T` /
`*mut T` with `T: Sized`, so any other argument value is a call with an
ABI-incompatible argument.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html#r-dynamic-sized.pointer-types>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types
>
> * Pointers to slices and `str` also store the number of elements.
> * Pointers to trait objects also store a pointer to a vtable."
-/
@[reducible]
def rawPtrArgOfValue? (ptrBytes : Nat) : Value → Option RawPtrArg
  | .ptr ptr sz =>
    match Nat.beq sz ptrBytes with
    | true => .some (.prov ptr)
    | false => .none
  | .scalar sc =>
    match Nat.beq sc.sizeBytes ptrBytes with
    | true => .some (.addr sc.bits)
    | false => .none
  | _ => .none

/--
Test whether a thin raw-pointer argument is the null pointer: the
provenance-less address `0`, or a pointer value with `allocId = 0` (no
provenance) at offset `0`.

Reference (`core::ptr` module documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L18-L20>

> "//! * A [null] pointer is *never* valid for reads/writes.
> //! * For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes.
> //!   The following points are only concerned with non-zero-sized accesses."

Modeling choice: `allocId = 0` is Anneal's encoding of a `Value.ptr` without
provenance, whose `offsetBytes` is then its address.
-/
@[reducible]
def rawPtrArgIsNull : RawPtrArg → Bool
  | .prov ptr => Bool.and (Nat.beq ptr.allocId 0) (Nat.beq ptr.offsetBytes 0)
  | .addr addr => Nat.beq addr 0

/--
What a thin raw-pointer argument points to, for a non-zero-sized access:
- `.stack ptr entry`: a stack local tracked by the Tree Borrows entry `entry` of
  the pointer's tag (memory inside a Rust allocation);
- `.global ptr alloc`: the captured global allocation `alloc` (memory inside a
  Rust allocation);
- `.outside`: a pointer without provenance (a provenance-less address, or a
  pointer value with `allocId = 0`), which is derived from no Rust allocation;
- `.untracked`: a pointer whose provenance names an allocation the model does
  not track (neither a borrow entry nor a captured global).

Reference (`core::ptr` module documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L21-L25>

> "//! * For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that
> //!   the pointer be *dereferenceable*. The [provenance] of the pointer is used to determine which
> //!   [allocation] it is derived from; a pointer is dereferenceable if the memory range of the given
> //!   size starting at the pointer is entirely contained within the bounds of that allocation. Note
> //!   that in Rust, every (stack-allocated) variable is considered a separate allocation."

Modeling choice: the split into tracked and untracked allocations is Anneal's.
An `.untracked` pointer may be valid (for example heap memory returned by an
external call), so accesses through it are unsupported rather than undefined
behavior.
-/
inductive RawPtrTarget : Type where
  /-- A stack local tracked by the borrow entry `entry` of `ptr`'s tag. -/
  | stack (ptr : ProvenancePtr) (entry : BorrowEntry) : RawPtrTarget
  /-- The captured global allocation `alloc`. -/
  | global (ptr : ProvenancePtr) (alloc : CapturedAllocation) : RawPtrTarget
  /-- A pointer without provenance: it is derived from no Rust allocation. -/
  | outside : RawPtrTarget
  /-- A pointer into an allocation the model does not track. -/
  | untracked : RawPtrTarget

/--
Resolve what the thin raw-pointer argument `arg` points to (`RawPtrTarget`): a
Tree Borrows entry for its tag in `borrows` (`lookupBorrow`) takes precedence
over a captured global allocation in `globals` (`lookupGlobalAlloc`), as in
`evalPlaceRead`; a pointer with neither is `.outside` when it has no provenance
(`.addr _`, or `allocId = 0`) and `.untracked` otherwise.

Reference (`core::ptr` module documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L21-L25>

> "//! * For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that
> //!   the pointer be *dereferenceable*. The [provenance] of the pointer is used to determine which
> //!   [allocation] it is derived from; a pointer is dereferenceable if the memory range of the given
> //!   size starting at the pointer is entirely contained within the bounds of that allocation. Note
> //!   that in Rust, every (stack-allocated) variable is considered a separate allocation."
-/
@[reducible]
def classifyRawPtrTarget
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) :
    RawPtrArg → RawPtrTarget
  | .addr _ => .outside
  | .prov ptr =>
    match lookupBorrow borrows ptr.tag with
    | .some entry => .stack ptr entry
    | .none =>
      match lookupGlobalAlloc globals ptr.allocId with
      | .some alloc => .global ptr alloc
      | .none =>
        match Nat.beq ptr.allocId 0 with
        | true => .outside
        | false => .untracked

/--
Element type `T`, `size_of::<T>()`, and `align_of::<T>()` of a raw-pointer
memory access (`.ok`), or the fault with which the call steps when they cannot
be determined (`.fault`).

Reference (The Rust Reference, "Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "A value of alignment n must only be stored at an address that is a multiple
> of n."
-/
inductive RawPtrElemLayout : Type where
  /-- The element type `elemTy` with its byte `size` and alignment `align`. -/
  | ok (elemTy : Ty) (size align : Nat) : RawPtrElemLayout
  /-- The call faults with `kind` (`.unsupported` when `T` is not resolved). -/
  | fault (kind : FailureKind) : RawPtrElemLayout

/--
Resolve the element type `T` of a raw-pointer memory access `f::<T>(ptr, ..)`
whose first parameter is `*const T` or `*mut T`, with its size and alignment
(`intrinsicRigidTyByteSize`, `intrinsicRigidTyAlign`).

`T` is the single type argument in `target.typeArgs`, or else the pointee type
of the first argument operand (`operandPointeeTy`); with neither (or with more
than one type argument, which none of these functions has) the call is
unsupported. Every function dispatched here declares `T` without `?Sized`, so
an unsized `T` (`isUnsizedRigidTy`) is an ill-typed call and faults with `.ub`;
a sized `T` whose size or alignment the model cannot resolve (a generic or
opaque type, or an ADT without a `LayoutTable` entry) is unsupported, as in
`intrinsicUnresolvedLayoutStep`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L994-L1005>

> "/// Performs a volatile load from the `src` pointer.
> ///
> /// The stabilized version of this intrinsic is [`core::ptr::read_volatile`].
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_load<T>(src: *const T) -> T;
> /// Performs a volatile store to the `dst` pointer.
> ///
> /// The stabilized version of this intrinsic is [`core::ptr::write_volatile`].
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_store<T>(dst: *mut T, val: T);"

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Most types have a fixed size that is known at compile time and implement the
> trait `Sized`. A type with a size that is known only at run-time is called a
> dynamically sized type (DST) or, informally, an unsized type."
-/
def resolveRawPtrElemLayout
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand) :
    RawPtrElemLayout :=
  let elemTyOpt : Option Ty :=
    match target.typeArgs with
    | elemKind :: .nil =>
      .some { kind := elemKind, layoutIdx := synthKindLayoutIdx bodyLayouts elemKind }
    | .nil =>
      match argOps with
      | ptrOp :: _ => operandPointeeTy bodyLocalDecls bodyLayouts ptrOp
      | .nil => .none
    | _ :: _ :: _ => .none
  match elemTyOpt with
  | .none => .fault .unsupported
  | .some rawElemTy =>
    let elemTy := resolveTyWithLocalDecls bodyLocalDecls bodyLayouts rawElemTy
    match isUnsizedRigidTy 8 elemTy.kind with
    | true => .fault .ub
    | false =>
      match
        intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy.kind,
        intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy.kind
      with
      | .some size, .some align => .ok elemTy size align
      | _, _ => .fault .unsupported

/--
Frame-qualified local slots, slot, `LocalDecl`s, and `LayoutTable` of the local
`loc` of the stack frame at depth `depth` of `callStack`: the active frame
(`depth = length callStack`, slots `locals'`, declarations `bodyLocalDecls`) or
a suspended caller frame (`savedFrameAtDepth?`, with its saved slots and its
body's declarations).
Returning the owning frame's full slot list alongside the slot ensures any
`ProjectionElem.index` projection on `entry.targetProjection` reads its index
local from the owning frame rather than the active callee frame.
Returns `.none` when no such frame is live, when the frame has no slot `loc`,
or when the target is a caller-owned referent slot of the root frame
(`Memory.callerLocals`), whose declarations are not in scope; callers treat
`.none` as unsupported.

Reference (`core::ptr` module documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L24-L25>

> "//!   size starting at the pointer is entirely contained within the bounds of that allocation. Note
> //!   that in Rust, every (stack-allocated) variable is considered a separate allocation."
-/
def rawPtrTargetFrame?
    (callStack : List SavedCallerFrame)
    (locals' : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (depth loc : Nat) :
    Option (List LocalSlot × LocalSlot × List LocalDecl × LayoutTable) :=
  match Nat.beq depth (length callStack) with
  | true =>
    match get? locals' loc with
    | .some slot => .some (locals', slot, bodyLocalDecls, bodyLayouts)
    | .none => .none
  | false =>
    match savedFrameAtDepth? callStack depth with
    | .some sf =>
      match get? sf.frame.locals loc with
      | .some slot => .some (sf.frame.locals, slot, sf.callerBody.localDecls, sf.callerBody.layouts)
      | .none => .none
    | .none => .none

/--
Decide whether the thin raw-pointer argument `arg`, which points to `tgt`
(`classifyRawPtrTarget`), is aligned to `reqAlign` bytes in every execution:
`.some true` (aligned), `.some false` (misaligned: undefined behavior for an
access that requires alignment), or `.none` (the model cannot decide; callers
step to `MirStepNode.unsupported`).

- `reqAlign ≤ 1` is always satisfied.
- A provenance-less address is aligned iff it is a multiple of `reqAlign`; so
  is the address `offsetBytes` of a pointer value without provenance
  (`allocId = 0`, `tgt = .outside`).
- A pointer into an untracked allocation (`tgt = .untracked`) has unknown base
  address alignment, so it always returns `.none` when `reqAlign > 1` rather
  than falsely faulting on a nonzero offset from an unknown base.
- A pointer into a captured global allocation (`tgt = .global _ alloc`) returns
  `.none` when `alloc.align.bytes = 0` (unknown alignment), `.some false` when
  `1 ≤ alloc.align.bytes < reqAlign`, and otherwise checks
  `ptr.offsetBytes % reqAlign = 0` (matching `checkGlobalAllocAlign`).
- A pointer tracked by a Tree Borrows entry (`tgt = .stack _ entry`) checks
  `addr(entry.targetLocal, entry.targetProjection) + ptr.offsetBytes` rather
  than `ptr.offsetBytes` alone, so a pointer offset back to an aligned boundary
  from an unaligned sub-place (for example `(&raw const s.unaligned_byte).add(3)`
  inside an `align(4)` struct) is not falsely rejected. It returns `.some false`
  when `checkTargetPlaceAlignWalk` proves misalignment (including misaligned
  fields of `#[repr(packed)]` structs), `.some true` when the root local's exact
  alignment is at least `reqAlign` (`tyExactByteAlign?`) and the combined offset
  `relOff + ptr.offsetBytes` (`projectionChainByteOffset?`) is a multiple of
  `reqAlign`, and `.none` otherwise.

Reference (The Rust Reference, "Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "A value of alignment n must only be stored at an address that is a multiple
> of n."

Reference (`core::ptr` module documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L52-L59>

> "//! ## Alignment
> //!
> //! Valid raw pointers as defined above are not necessarily properly aligned (where
> //! "proper" alignment is defined by the pointee type, i.e., `*const T` must be
> //! aligned to `align_of::<T>()`). However, most functions require their
> //! arguments to be properly aligned, and will explicitly state
> //! this requirement in their documentation. Notable exceptions to this are
> //! [`read_unaligned`] and [`write_unaligned`]."

Modeling choice: Rust's requirement is about the run-time address. Allocation
addresses are chosen nondeterministically, so the model requires alignment in
every placement of the allocation; a pointer that is misaligned in some
placement makes some execution undefined.
-/
def rawPtrTargetAligned?
    (callStack : List SavedCallerFrame)
    (locals' : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (reqAlign : Nat)
    (arg : RawPtrArg)
    (tgt : RawPtrTarget) :
    Option Bool :=
  match Nat.ble reqAlign 1 with
  | true => .some true
  | false =>
    match arg with
    | .addr addr => .some (Nat.beq (Nat.mod addr reqAlign) 0)
    | .prov ptr =>
      match tgt with
      | .outside => .some (Nat.beq (Nat.mod ptr.offsetBytes reqAlign) 0)
      | .untracked => .none
      | .global _ alloc =>
        match Nat.beq alloc.align.bytes 0 with
        | true => .none
        | false =>
          match Nat.ble reqAlign alloc.align.bytes with
          | false => .some false
          | true => .some (Nat.beq (Nat.mod ptr.offsetBytes reqAlign) 0)
      | .stack _ entry =>
        match
          rawPtrTargetFrame?
            callStack
            locals'
            bodyLocalDecls
            bodyLayouts
            entry.targetFrameDepth
            entry.targetLocal
        with
        | .none => .none
        | .some (_, slot, targetDecls, targetLayouts) =>
          match get? targetDecls entry.targetLocal with
          | .none => .none
          | .some rootDecl =>
            let rootValOpt : Option Value :=
              match slot with
              | .init v => .some v
              | _ => .none
            match
              checkTargetPlaceAlignWalk
                targetDecls
                targetLayouts
                reqAlign
                ptr.offsetBytes
                (.some rootDecl.ty)
                rootValOpt
                .none
                entry.targetProjection
            with
            | false => .some false
            | true =>
              match tyExactByteAlign? targetDecls targetLayouts rootDecl.ty with
              | .none => .none
              | .some encAlign =>
                match Nat.ble reqAlign encAlign with
                | false => .some false
                | true =>
                  match
                    projectionChainByteOffset?
                      targetLayouts
                      (.some rootDecl.ty)
                      rootValOpt
                      .none
                      0
                      targetDecls
                      (normalizeSubsliceProjections
                        (stripTransparentProjections entry.targetProjection))
                  with
                  | .none => .none
                  | .some relOff =>
                    .some (Nat.beq (Nat.mod (Nat.add relOff ptr.offsetBytes) reqAlign) 0)

/--
Resolution of the stack place a tracked raw pointer accesses
(`resolveRawPtrStackTarget`): the owning frame's slots `targetLocals`,
`LocalDecl`s, `LayoutTable`, root local type `rootTy`, the type `placeTy` and
byte size `placeSize` of the borrow entry's target place, and the target
local's `slot` (`.ok`); or the fault with which the access steps (`.fault`).

Reference (`core::ptr` module documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L48-L50>

> "//! We say that a pointer is "dangling" if it is not valid for any non-zero-sized accesses. This
> //! means out-of-bounds pointers, pointers to freed memory, null pointers, and pointers created with
> //! [`NonNull::dangling`] are all dangling."
-/
inductive RawPtrStackTarget : Type where
  /-- The access is within the live target place of type `placeTy` and byte size
  `placeSize` inside root local type `rootTy`. -/
  | ok
      (targetLocals : List LocalSlot)
      (targetDecls : List LocalDecl)
      (targetLayouts : LayoutTable)
      (rootTy : Ty)
      (placeTy : Ty)
      (placeSize : Nat)
      (slot : LocalSlot) :
      RawPtrStackTarget
  /-- The access faults with `kind`. -/
  | fault (kind : FailureKind) : RawPtrStackTarget

/--
Resolve a non-zero-sized access of `accessBytes` bytes at byte offset
`offsetBytes` through a raw pointer whose tag has the Tree Borrows entry
`entry`, for a read (`isWrite = false`) or a write (`isWrite = true`).

Checks, in order:
1. A deallocated target (`entry.allocDead`) is `.ub`: the pointer is dangling.
2. A `.disabled` tag, or a `.frozen` tag for a write, is `.ub` (the child
   access is forbidden by Tree Borrows).
3. A byte-ranged entry (`entry.rangeLen ≠ 0`) is unsupported.
4. The target local must be a slot of a live frame with declarations in scope
   (`rawPtrTargetFrame?`, else unsupported); a `.dead` slot is `.ub`.
5. The root local declaration and the type and size of the entry's target place
   must resolve (else unsupported), and the accessed range `[offsetBytes,
   offsetBytes + accessBytes)` must lie within that place. A range that leaves
   a whole local (`entry.targetProjection = []`) leaves its allocation and is
   `.ub`; a range that leaves a sub-place may still be inside the allocation,
   where the Tree Borrows range of `entry` no longer covers it, so it is
   unsupported.

Reference (`core::ptr` module documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L21-L25>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L48-L50>

> "//! * For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that
> //!   the pointer be *dereferenceable*. The [provenance] of the pointer is used to determine which
> //!   [allocation] it is derived from; a pointer is dereferenceable if the memory range of the given
> //!   size starting at the pointer is entirely contained within the bounds of that allocation. Note
> //!   that in Rust, every (stack-allocated) variable is considered a separate allocation."

> "//! We say that a pointer is "dangling" if it is not valid for any non-zero-sized accesses. This
> //! means out-of-bounds pointers, pointers to freed memory, null pointers, and pointers created with
> //! [`NonNull::dangling`] are all dangling."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Modeling choice: restricting the access to the entry's target place
(conditions 3 and 5) is Anneal's. It ensures `entry`'s Tree Borrows provenance
covers every accessed byte, while `borrowsAfterRawPtrAccess` tracks byte-level
overlap against foreign borrows on the same local.
-/
def resolveRawPtrStackTarget
    (callStack : List SavedCallerFrame)
    (locals' : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (entry : BorrowEntry)
    (offsetBytes accessBytes : Nat)
    (isWrite : Bool) :
    RawPtrStackTarget :=
  match entry.allocDead with
  | true => .fault .ub
  | false =>
    let permFault : Bool :=
      match entry.perm, isWrite with
      | .disabled, _ => true
      | .frozen, true => true
      | _, _ => false
    match permFault with
    | true => .fault .ub
    | false =>
      match Nat.beq entry.rangeLen 0 with
      | false => .fault .unsupported
      | true =>
        match
          rawPtrTargetFrame?
            callStack
            locals'
            bodyLocalDecls
            bodyLayouts
            entry.targetFrameDepth
            entry.targetLocal
        with
        | .none => .fault .unsupported
        | .some (_, .dead, _, _) => .fault .ub
        | .some (targetLocals, slot, targetDecls, targetLayouts) =>
          match get? targetDecls entry.targetLocal with
          | .none => .fault .unsupported
          | .some rootDecl =>
            let rootTy := resolveTyWithLocalDecls targetDecls targetLayouts rootDecl.ty
            match
              placeTyResolved
                targetDecls
                targetLayouts
                { local_ := entry.targetLocal, projection := entry.targetProjection }
            with
            | .none => .fault .unsupported
            | .some placeTy =>
              match tyByteSize targetDecls targetLayouts placeTy with
              | .none => .fault .unsupported
              | .some placeSize =>
                match Nat.ble (Nat.add offsetBytes accessBytes) placeSize with
                | true =>
                  .ok targetLocals targetDecls targetLayouts rootTy placeTy placeSize slot
                | false =>
                  match entry.targetProjection with
                  | .nil => .fault .ub
                  | _ :: _ => .fault .unsupported

/--
Fault of a typed load of `elemKind` that meets uninitialized memory: `.ub`
when `elemKind` is a primitive scalar or thin pointer type, whose values are
never uninitialized, and `.unsupported` for every other type (a `union` or a
type with padding may legally hold uninitialized bytes, which the typed value
representation cannot always express).

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "- An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer must be initialized, i.e., must not be obtained from uninitialized memory."

> "Note: Uninitialized memory is also implicitly invalid for any type that has a restricted set of valid values. In other words, the only cases in which reading uninitialized memory is permitted are inside `union`s and in “padding” (the gaps between the fields of a type)."
-/
@[reducible]
def rawPtrUninitFault (elemKind : RigidTy) : FailureKind :=
  match Bool.or (isPrimitiveScalarKind elemKind) (isThinPtrKind elemKind) with
  | true => .ub
  | false => .unsupported

/--
Test whether every byte of `bytes` is initialized and carries no provenance.

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."
-/
@[reducible]
def rawPtrBytesAllPlainInit : List AbstractByte → Bool
  | .nil => true
  | .init _ .none :: rest => rawPtrBytesAllPlainInit rest
  | _ :: _ => false

/--
Test whether some byte of `bytes` is uninitialized.

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "Note: Uninitialized memory is also implicitly invalid for any type that has a restricted set of valid values. In other words, the only cases in which reading uninitialized memory is permitted are inside `union`s and in “padding” (the gaps between the fields of a type)."
-/
@[reducible]
def rawPtrBytesAnyUninit : List AbstractByte → Bool
  | .nil => false
  | .uninit :: _ => true
  | .init _ _ :: rest => rawPtrBytesAnyUninit rest

/--
Test whether some initialized byte of `bytes` carries pointer provenance.

Reading bytes that carry pointer provenance at an integer or non-pointer type is
not undefined behavior in Rust (the result depends on the pointer's runtime
address), so the model must fail closed with `MirStepNode.unsupported` rather
than discarding provenance and returning an invented numeric address.

Reference (`core::ptr` module documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L157-L161>

> "//! A pointer value in Rust semantically contains the following information:
> //!
> //! * The **address** it points to, which can be represented by a `usize`.
> //! * The **provenance** it has, defining the memory it has permission to access. Provenance can be
> //!   absent, in which case the pointer does not have permission to access any memory."
-/
@[reducible]
def rawPtrBytesAnyProv : List AbstractByte → Bool
  | .nil => false
  | .init _ (.some _) :: _ => true
  | _ :: rest => rawPtrBytesAnyProv rest

/--
Test whether every byte of `bytes` is initialized with the exact provenance pair
`(allocId, tag)`. Used when decoding a thin pointer from bytes so both `allocId`
and Tree Borrows `tag` are preserved and mixed-provenance byte sequences fail
closed.

Reference (`core::ptr` module documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L157-L161>

> "//! A pointer value in Rust semantically contains the following information:
> //!
> //! * The **address** it points to, which can be represented by a `usize`.
> //! * The **provenance** it has, defining the memory it has permission to access. Provenance can be
> //!   absent, in which case the pointer does not have permission to access any memory."
-/
@[reducible]
def rawPtrBytesUniformProv (allocId tag : Nat) : List AbstractByte → Bool
  | .nil => true
  | .init _ (.some (a, t)) :: rest =>
    match Bool.and (Nat.beq a allocId) (Nat.beq t tag) with
    | true => rawPtrBytesUniformProv allocId tag rest
    | false => false
  | _ :: _ => false

/--
Fault of a typed load of `elemKind` whose bytes `bytes` do not decode
(`decodeTypedValueFromBytes = .none`):
- for a primitive scalar type, `.ub` when a byte is uninitialized or when every
  byte is initialized without provenance (the bytes are then an invalid bit
  pattern, such as `2` for `bool`), and `.unsupported` when a byte carries
  pointer provenance (reading it at integer type is not undefined behavior,
  but the result is not modeled);
- for a thin pointer type, `.ub` when a byte is uninitialized and `.unsupported`
  otherwise;
- `.unsupported` for every other type, whose decoder is partial.

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."

> "- A bool value must be false (0) or true (1)."

> "Note: Uninitialized memory is also implicitly invalid for any type that has a restricted set of valid values. In other words, the only cases in which reading uninitialized memory is permitted are inside `union`s and in “padding” (the gaps between the fields of a type)."
-/
@[reducible]
def rawPtrDecodeFault (elemKind : RigidTy) (bytes : List AbstractByte) : FailureKind :=
  match isPrimitiveScalarKind elemKind with
  | true =>
    match Bool.or (rawPtrBytesAnyUninit bytes) (rawPtrBytesAllPlainInit bytes) with
    | true => .ub
    | false => .unsupported
  | false =>
    match Bool.and (isThinPtrKind elemKind) (rawPtrBytesAnyUninit bytes) with
    | true => .ub
    | false => .unsupported

/--
Byte width of an integer `RigidTy` on a target with `ptrBytes`-wide pointers.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The usize type is an unsigned integer type with the same number of bits as the platform’s pointer type. It can represent every memory address in the process."
>
> "The isize type is a signed two’s complement integer type with the same number of bits as the platform’s pointer type."
-/
@[reducible]
def rawPtrIntByteWidth (ptrBytes : Nat) : RigidTy → Option Nat
  | .uint .u8 | .int .i8 => .some 1
  | .uint .u16 | .int .i16 => .some 2
  | .uint .u32 | .int .i32 => .some 4
  | .uint .u64 | .int .i64 => .some 8
  | .uint .u128 | .int .i128 => .some 16
  | .uint .usize | .int .isize => .some ptrBytes
  | _ => .none

/--
Byte width of an IEEE floating-point `FloatTy` (`f16`..`f128`).

Reference (The Rust Reference, "Floating-Point Types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#floating-point-types>

> "The IEEE 754-2008 “binary32” and “binary64” floating-point types are f32 and f64, respectively."
-/
@[reducible]
def rawPtrFloatByteWidth : FloatTy → Nat
  | .f16 => 2
  | .f32 => 4
  | .f64 => 8
  | .f128 => 16

/--
Check a validity predicate `check` on every element value of an array at element
type `elemTy`.

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."
-/
@[reducible]
def rawPtrAllValuesValid?
    (check : Ty → Value → Bool)
    (elemTy : Ty) :
    List Value → Bool
  | .nil => true
  | v :: vs =>
    match check elemTy v with
    | true => rawPtrAllValuesValid? check elemTy vs
    | false => false

/--
Check a validity predicate `check` elementwise across tuple field types `ks`,
optional layout indices `fls`, and runtime field values `vs`.

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."
-/
@[reducible]
def rawPtrTupleFieldsValid?
    (check : Ty → Value → Bool)
    (layouts : LayoutTable) :
    List RigidTy → List LayoutIdx → List Value → Bool
  | .nil, _, .nil => true
  | k :: ks, fl :: fls, v :: vs =>
    match check { kind := k, layoutIdx := fl } v with
    | true => rawPtrTupleFieldsValid? check layouts ks fls vs
    | false => false
  | k :: ks, .nil, v :: vs =>
    match check { kind := k, layoutIdx := synthKindLayoutIdx layouts k } v with
    | true => rawPtrTupleFieldsValid? check layouts ks .nil vs
    | false => false
  | _, _, _ => false

/--
Fuel-bounded structural validity check of runtime `Value` `v` against static
type `ty` for raw-pointer loads and stores: rejects uninhabited types (`.never`
or `tyIsUninhabited`), invalid `bool` / `char` bit patterns, scalar width
mismatches, null references and function pointers, and invalid elements inside
tuples and fixed-length arrays, as well as ABI-mismatched value shapes (such as
a scalar passed at `()` or an aggregate type).

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."

> "- A bool value must be false (0) or true (1)."

> "- A char value must not be a surrogate (i.e., must not be in the range
> 0xD800..=0xDFFF) and must be equal to or less than char::MAX."

Reference (The Rust Reference, "Never type"):
<https://doc.rust-lang.org/1.98.0/reference/types/never.html>

> "The never type ! is a type with no values, representing the result of computations that never complete."

Modeling choice: ADTs whose `TypeLayout` fixes a single variant require matching
variant index, while multi-variant enums and unions are accepted at aggregate
shape so valid enums and unions are never falsely rejected.
-/
def rawPtrValueValid? : Nat → LayoutTable → Ty → Value → Bool
  | .zero, _, _, _ => true
  | .succ fuel', layouts, ty, v =>
    let ptrBytes := layoutPointerBytes layouts
    match tyIsUninhabited layouts ty with
    | true => false
    | false =>
      match ty.kind with
      | .never => false
      | .bool =>
        match v with
        | .scalar sc => Bool.and (Nat.beq sc.sizeBytes 1) (Nat.ble sc.bits 1)
        | _ => false
      | .char =>
        match v with
        | .scalar sc => Bool.and (Nat.beq sc.sizeBytes 4) (isValidCharCode sc.bits)
        | _ => false
      | .int w =>
        match rawPtrIntByteWidth ptrBytes (.int w), v with
        | .some expected, .scalar sc => Nat.beq sc.sizeBytes expected
        | _, _ => false
      | .uint w =>
        match rawPtrIntByteWidth ptrBytes (.uint w), v with
        | .some expected, .scalar sc => Nat.beq sc.sizeBytes expected
        | _, _ => false
      | .float fk =>
        match v with
        | .scalar sc => Nat.beq sc.sizeBytes (rawPtrFloatByteWidth fk)
        | _ => false
      | .rawPtr _ pointee =>
        match pointee with
        | .slice _ | .str | .dynamic _ =>
          match v with
          | .aggregate 0 (dataVal :: metaVal :: .nil) =>
            Bool.and
              (match rawPtrArgOfValue? ptrBytes dataVal with
               | .some _ => true
               | .none => false)
              (isValidWidePtrMetaVal metaVal)
          | _ => false
        | _ =>
          match rawPtrArgOfValue? ptrBytes v with
          | .some _ => true
          | .none => false
      | .ref _ pointee =>
        match pointee with
        | .slice _ | .str | .dynamic _ =>
          match v with
          | .aggregate 0 (dataVal :: metaVal :: .nil) =>
            match rawPtrArgOfValue? ptrBytes dataVal with
            | .some arg =>
              Bool.and (Bool.not (rawPtrArgIsNull arg)) (isValidWidePtrMetaVal metaVal)
            | .none => false
          | _ => false
        | _ =>
          match rawPtrArgOfValue? ptrBytes v with
          | .some arg => Bool.not (rawPtrArgIsNull arg)
          | .none => false
      | .fnPtr _ _ _ _ =>
        match rawPtrArgOfValue? ptrBytes v with
        | .some arg => Bool.not (rawPtrArgIsNull arg)
        | .none => false
      | .tuple .nil | .fnDef _ _ =>
        match v with
        | .unit => true
        | .aggregate 0 .nil => true
        | _ => false
      | .tuple (k :: ks) =>
        match v with
        | .aggregate 0 fields =>
          let fieldLays : List LayoutIdx :=
            match LayoutTable.lookup layouts ty.layoutIdx with
            | .some l =>
              match Nat.beq (length l.fieldLayouts) (length (k :: ks)) with
              | true => l.fieldLayouts
              | false => .nil
            | .none => .nil
          rawPtrTupleFieldsValid? (rawPtrValueValid? fuel' layouts) layouts (k :: ks) fieldLays fields
        | _ => false
      | .array _ .zero =>
        match v with
        | .aggregate 0 .nil => true
        | .unit => true
        | _ => false
      | .array elemK (.succ n) =>
        match v with
        | .aggregate 0 elems =>
          let elemLayIdx : LayoutIdx :=
            match LayoutTable.lookup layouts ty.layoutIdx with
            | .some { fieldLayouts := flIdx :: _, .. } => flIdx
            | _ => synthKindLayoutIdx layouts elemK
          Bool.and
            (Nat.beq (length elems) (.succ n))
            (rawPtrAllValuesValid? (rawPtrValueValid? fuel' layouts)
              { kind := elemK, layoutIdx := elemLayIdx } elems)
        | _ => false
      | .adt _ _ =>
        match v with
        | .aggregate varIdx _ =>
          match LayoutTable.lookup layouts ty.layoutIdx with
          | .some { variants := .single expectedVar, .. } => Nat.beq varIdx expectedVar
          | _ => true
        | .unit =>
          match LayoutTable.lookup layouts ty.layoutIdx with
          | .some l => Nat.beq l.size.bytes 0
          | .none => false
        | .scalar sc =>
          match LayoutTable.lookup layouts ty.layoutIdx with
          | .some { fields := .primitive, size := sz, backendRepr := .scalar (.initialized _ vr), .. } =>
            Bool.and (Nat.beq sc.sizeBytes sz.bytes) (wrappingRangeContains vr sc.bits)
          | .some { fields := .primitive, size := sz, .. } => Nat.beq sc.sizeBytes sz.bytes
          | _ => false
        | .ptr _ pSz =>
          match LayoutTable.lookup layouts ty.layoutIdx with
          | .some { fields := .primitive, size := sz, .. } => Nat.beq pSz sz.bytes
          | _ => false
        | _ => false
      | _ => true

/--
Encode the value `v` of a place of type `ty` to its byte representation, as
`decodeSubValueAtByteOffset?` does: scalars and thin pointers by their untyped
little-endian encoding, and aggregates by `encodeTypedValueToBytes` at the
layout-faithful type `resolveFaithfulAggregateTy?` finds (else `.none`). A
`Value.unit` occupies no bytes, and `Value.uninit` has no byte encoding here.

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."
-/
def rawPtrEncodeValue?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty) :
    Value → Option (List AbstractByte)
  | .unit => .some .nil
  | .scalar sc => encodeUntypedValueToBytes defaultCodecFuel (.scalar sc)
  | .ptr p sz => encodeUntypedValueToBytes defaultCodecFuel (.ptr p sz)
  | .aggregate varIdx fields =>
    match resolveFaithfulAggregateTy? localDecls layouts ty varIdx fields with
    | .some resolvedTy =>
      encodeTypedValueToBytes layouts resolvedTy (.aggregate varIdx fields)
    | .none => .none
  | .uninit => .none

/--
Outcome of loading a typed value through a tracked raw pointer
(`loadRawPtrStackValue`): the loaded value (`.ok`) or a fault (`.fault`).

Reference (`core::ptr::read` documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L1596>

> "/// * `src` must point to a properly initialized value of type `T`."
-/
inductive RawPtrLoadResult : Type where
  /-- The loaded value. -/
  | ok (val : Value) : RawPtrLoadResult
  /-- The load faults with `kind`. -/
  | fault (kind : FailureKind) : RawPtrLoadResult

/--
Decode `bytes` as a thin pointer (`isThinPtrKind elemKind = true`) of width
`ptrBytes` without forging provenance or discarding Tree Borrows tags:
- uninitialized bytes fault with `.ub` (raw pointers, references, and function
  pointers must be initialized in Rust 1.98.0);
- all-plain bytes (no provenance) decode to the provenance-less address
  `Value.scalar ⟨bits, ptrBytes⟩` for `.rawPtr`, to `.ub` on address `0` for
  `.ref` / `.fnPtr`, and to `.unsupported` on non-zero address for `.ref` /
  `.fnPtr`;
- bytes carrying one uniform provenance `(allocId, tag)` decode to
  `Value.ptr { allocId, offsetBytes := bits } ptrBytes` (where `allocId` is the
  pointer's Tree Borrows tag), rejecting null (`allocId = 0 ∧ bits = 0`) for
  `.ref` / `.fnPtr`;
- mixed-provenance or wrong-length byte sequences fail closed with
  `.unsupported`.

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "- An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer must be initialized, i.e., must not be obtained from uninitialized memory."

Reference (`core::ptr` module documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L157-L161>

> "//! A pointer value in Rust semantically contains the following information:
> //!
> //! * The **address** it points to, which can be represented by a `usize`.
> //! * The **provenance** it has, defining the memory it has permission to access. Provenance can be
> //!   absent, in which case the pointer does not have permission to access any memory."
-/
def rawPtrDecodeThinPtr
    (ptrBytes : Nat)
    (elemKind : RigidTy)
    (bytes : List AbstractByte) :
    RawPtrLoadResult :=
  match Nat.beq (length bytes) ptrBytes with
  | false => .fault .unsupported
  | true =>
    match rawPtrBytesAnyUninit bytes with
    | true => .fault .ub
    | false =>
      match bytes with
      | .init _ .none :: _ =>
        match rawPtrBytesAllPlainInit bytes, decodeLittleEndianBytes bytes with
        | true, .some (bits, _) =>
          match elemKind with
          | .rawPtr _ _ => .ok (.scalar ⟨bits, ptrBytes⟩)
          | .ref _ _ | .fnPtr _ _ _ _ =>
            match Nat.beq bits 0 with
            | true => .fault .ub
            | false => .fault .unsupported
          | _ => .fault .unsupported
        | _, _ => .fault .unsupported
      | .init _ (.some (allocId, tag)) :: _ =>
        match rawPtrBytesUniformProv allocId tag bytes, decodeLittleEndianBytes bytes with
        | true, .some (bits, _) =>
          let isNonNullKind : Bool :=
            match elemKind with
            | .ref _ _ | .fnPtr _ _ _ _ => true
            | _ => false
          match Bool.and isNonNullKind (Bool.and (Nat.beq allocId 0) (Nat.beq bits 0)) with
          | true => .fault .ub
          | false =>
            .ok (.ptr { allocId := allocId, offsetBytes := bits } ptrBytes)
        | _, _ => .fault .unsupported
      | _ => .fault .unsupported

/--
Decode `bytes` at `elemTy` for a raw-pointer load from either a stack local or
a captured global allocation:
- thin pointers use `rawPtrDecodeThinPtr` (preserving provenance/tag and never
  forging an `allocId` from plain integer bytes);
- non-thin-pointer types fail closed with `.unsupported` whenever any byte
  carries pointer provenance (reading pointer bytes as integers or byte arrays
  depends on the pointer's runtime address and must never return an invented
  `0`);
- all other byte sequences decode via `decodeTypedValueFromBytes`, checking
  initialization (`valueContainsUninit`) and structural validity
  (`rawPtrValueValid?`) and classifying decode failure via `rawPtrDecodeFault`.

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."

> "Note: Uninitialized memory is also implicitly invalid for any type that has a restricted set of valid values. In other words, the only cases in which reading uninitialized memory is permitted are inside `union`s and in “padding” (the gaps between the fields of a type)."
-/
def rawPtrDecodeBytes
    (bodyLayouts : LayoutTable)
    (elemTy : Ty)
    (bytes : List AbstractByte) :
    RawPtrLoadResult :=
  match isThinPtrKind elemTy.kind with
  | true => rawPtrDecodeThinPtr (layoutPointerBytes bodyLayouts) elemTy.kind bytes
  | false =>
    match rawPtrBytesAnyProv bytes with
    | true => .fault .unsupported
    | false =>
      match decodeTypedValueFromBytes defaultCodecFuel bodyLayouts elemTy bytes with
      | .none => .fault (rawPtrDecodeFault elemTy.kind bytes)
      | .some v =>
        match valueContainsUninit v with
        | true => .fault (rawPtrUninitFault elemTy.kind)
        | false =>
          match rawPtrValueValid? 16 bodyLayouts elemTy v with
          | true => .ok v
          | false => .fault .ub

/--
Load a value of type `elemTy` (of `accessBytes > 0` bytes) at byte offset
`offsetBytes` of the target place of `entry`, whose type is `placeTy` and whose
local has slot `slot` in owning-frame slots `targetLocals` (as resolved by
`resolveRawPtrStackTarget`).

- An uninitialized target local faults with `rawPtrUninitFault`.
- When the access covers the target place exactly at its own type
  (`offsetBytes = 0` and `placeTy` is `elemTy`), the value is the place's value
  (`readProjectedForLocal` using `targetLocals`). This path does not depend on
  the place's address, so it serves unaligned places such as a field of a
  `#[repr(packed)]` struct.
- Otherwise the place's value is encoded to bytes (`rawPtrEncodeValue?`), the
  accessed bytes are sliced out, and they are decoded at `elemTy`
  (`rawPtrDecodeBytes`): a load at an interior byte offset or at another type.
- The loaded value must be fully initialized (`valueContainsUninit`, else
  `rawPtrUninitFault`) and valid for `elemTy` (`rawPtrValueValid?`, else
  `.ub`).

Reference (`core::ptr::read_unaligned` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L1737-L1748>

> "/// Reads the value from `src` without moving it. This leaves the
> /// memory in `src` unchanged.
> ///
> /// Unlike [`read`], `read_unaligned` works with unaligned pointers.
> ///
> /// # Safety
> ///
> /// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `src` must be [valid] for reads.
> ///
> /// * `src` must point to a properly initialized value of type `T`."

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."

Modeling choice: the typed value representation and its byte codec are
Anneal's. Shapes they cannot express are unsupported, never a successful load.
-/
def loadRawPtrStackValue
    (targetLocals : List LocalSlot)
    (bodyLayouts : LayoutTable)
    (targetDecls : List LocalDecl)
    (targetLayouts : LayoutTable)
    (entry : BorrowEntry)
    (offsetBytes accessBytes : Nat)
    (placeTy elemTy : Ty)
    (slot : LocalSlot) :
    RawPtrLoadResult :=
  match slot with
  | .dead => .fault .ub
  | .uninit => .fault (rawPtrUninitFault elemTy.kind)
  | .init rootVal =>
    let baseRes : ProjReadResult :=
      match entry.targetProjection with
      | .nil => .ok rootVal
      | pHead :: pTail =>
        readProjectedForLocal
          targetLocals
          targetDecls
          targetLayouts
          entry.targetLocal
          rootVal
          (pHead :: pTail)
    match baseRes with
    | .ub => .fault .ub
    | .unsupported => .fault .unsupported
    | .ok baseVal =>
      match Bool.and (Nat.beq offsetBytes 0) (rigidTyEq placeTy.kind elemTy.kind) with
      | true =>
        match valueContainsUninit baseVal with
        | true => .fault (rawPtrUninitFault elemTy.kind)
        | false =>
          match rawPtrValueValid? 16 bodyLayouts elemTy baseVal with
          | true => .ok baseVal
          | false => .fault .ub
      | false =>
        match rawPtrEncodeValue? targetDecls targetLayouts placeTy baseVal with
        | .none => .fault .unsupported
        | .some baseBytes =>
          match sliceAbstractBytes baseBytes offsetBytes accessBytes with
          | .none => .fault .unsupported
          | .some accessed => rawPtrDecodeBytes bodyLayouts elemTy accessed

/--
Structural equality on `TreeBorrowPerm` values. Used to detect foreign Tree
Borrows transitions that are guaranteed no-ops regardless of byte overlap.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def rawPtrTreeBorrowPermEq : TreeBorrowPerm → TreeBorrowPerm → Bool
  | .cell, .cell => true
  | .reservedFrz c₁, .reservedFrz c₂ =>
    match c₁, c₂ with
    | true, true => true
    | false, false => true
    | _, _ => false
  | .reservedIM, .reservedIM => true
  | .unique, .unique => true
  | .frozen, .frozen => true
  | .disabled, .disabled => true
  | _, _ => false

/--
Outcome of applying a byte-range-aware Tree Borrows access to a borrow list
(`borrowsAfterRawPtrAccess`, `borrowsAfterRawPtrCopy`): updated borrow list
(`.ok`) or a fault (`.fault .ub` on aliasing / protector UB, `.fault
.unsupported` when byte overlap against a conflicting foreign borrow cannot be
decided).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
inductive RawPtrBorrowResult : Type where
  /-- Updated Tree Borrows list after the access. -/
  | ok (borrows' : List BorrowEntry) : RawPtrBorrowResult
  /-- The access faults with `kind`. -/
  | fault (kind : FailureKind) : RawPtrBorrowResult

/--
Decide whether foreign borrow entry `b` on the same `(targetFrameDepth,
targetLocal)` overlaps a raw-pointer access of `accessBytes > 0` bytes at
`offsetBytes` inside `entry.targetProjection` (of byte size `placeSize`):
`.some true` (definitely overlaps), `.some false` (definitely disjoint), or
`.none` (byte range undecidable).

When `accessBytes < placeSize` (a strict sub-range access through a container
pointer) or `b.rangeLen ≠ 0`, both the accessed interval and `b`'s interval are
resolved to byte ranges within the root local so disjoint sibling/child borrows
are never falsely invalidated or flagged as protector UB.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Modeling choice: byte-interval overlap resolution uses Anneal's
`projectionChainByteOffset?` and `tyByteSize` helpers and returns `.none` (fail
closed when the transition matters) if either interval cannot be computed.
-/
def rawPtrEntryOverlapsAccess
    (targetDecls : List LocalDecl)
    (targetLayouts : LayoutTable)
    (rootTy : Ty)
    (rootValOpt : Option Value)
    (entry : BorrowEntry)
    (offsetBytes accessBytes placeSize : Nat)
    (b : BorrowEntry) :
    Option Bool :=
  let fullPlace : Bool :=
    Bool.and (Nat.beq offsetBytes 0) (Nat.beq accessBytes placeSize)
  match Nat.beq b.rangeLen 0, b.targetProjection with
  | true, .nil => .some true
  | true, _ :: _ =>
    match fullPlace with
    | true => .some (projectionsOverlap b.targetProjection entry.targetProjection)
    | false =>
      match projectionsOverlap b.targetProjection entry.targetProjection with
      | false => .some false
      | true =>
        let entryBaseOpt :=
          projectionChainByteOffset?
            targetLayouts
            (.some rootTy)
            rootValOpt
            .none
            0
            targetDecls
            (normalizeSubsliceProjections
              (stripTransparentProjections entry.targetProjection))
        let bBaseOpt :=
          projectionChainByteOffset?
            targetLayouts
            (.some rootTy)
            rootValOpt
            .none
            0
            targetDecls
            (normalizeSubsliceProjections
              (stripTransparentProjections b.targetProjection))
        let bSizeOpt : Option Nat :=
          match
            placeTyResolved
              targetDecls
              targetLayouts
              { local_ := b.targetLocal, projection := b.targetProjection }
          with
          | .some bPlaceTy => tyByteSize targetDecls targetLayouts bPlaceTy
          | .none => .none
        match entryBaseOpt, bBaseOpt, bSizeOpt with
        | .some entryBase, .some bBase, .some bSize =>
          .some (byteRangesOverlapBool (Nat.add entryBase offsetBytes) accessBytes bBase bSize)
        | _, _, _ => .none
  | false, _ =>
    let entryBaseOpt :=
      projectionChainByteOffset?
        targetLayouts
        (.some rootTy)
        rootValOpt
        .none
        0
        targetDecls
        (normalizeSubsliceProjections
          (stripTransparentProjections entry.targetProjection))
    match entryBaseOpt with
    | .some entryBase =>
      .some
        (byteRangesOverlapBool
          (Nat.add entryBase offsetBytes)
          accessBytes
          b.rangeOffset
          b.rangeLen)
    | .none => .none

/--
Apply a single Tree Borrows read or write access through `accessTag` (whose
borrow entry is `entry`) across the suffix `bs` of `allBorrows`, preserving
list length on `.ok`.

- Ancestor-or-self entries (`isBorrowDescendantOrSelf allBorrows accessTag
  b.tag = true`) undergo `treeBorrowNodeAccess accessKind .localAccess` with
  protector status `isBorrowProtected activeProtectors b` (catching `.disabled`
  on read/write, `.frozen` on write, and protected `.reservedFrz true` on write
  across the entire ancestor chain, and activating reservations on write).
- Foreign entries on the same `(targetFrameDepth, targetLocal)` undergo
  `treeBorrowNodeAccess accessKind .foreignAccess` iff they overlap the accessed
  byte range (`rawPtrEntryOverlapsAccess`); guaranteed no-op transitions skip
  overlap resolution, and undecidable non-noop overlaps fail closed with
  `.unsupported` while still letting any definite `.ub` later in `bs` win.

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
def rawPtrBorrowStepList
    (allBorrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (accessKind : TreeBorrowAccessKind)
    (targetDecls : List LocalDecl)
    (targetLayouts : LayoutTable)
    (rootTy : Ty)
    (rootValOpt : Option Value)
    (accessTag : Nat)
    (entry : BorrowEntry)
    (offsetBytes accessBytes placeSize : Nat) :
    List BorrowEntry → RawPtrBorrowResult
  | .nil => .ok .nil
  | b :: rest =>
    match
      Bool.and
        (Nat.beq b.targetFrameDepth entry.targetFrameDepth)
        (Nat.beq b.targetLocal entry.targetLocal)
    with
    | false =>
      match
        rawPtrBorrowStepList
          allBorrows activeProtectors accessKind targetDecls targetLayouts rootTy rootValOpt
          accessTag entry offsetBytes accessBytes placeSize rest
      with
      | .ok rest' => .ok (b :: rest')
      | .fault kind => .fault kind
    | true =>
      let isProt := isBorrowProtected activeProtectors b
      match isBorrowDescendantOrSelf allBorrows accessTag b.tag with
      | true =>
        let tr := treeBorrowNodeAccess accessKind .localAccess b.perm isProt
        match treeBorrowTransitionIsUB tr with
        | true => .fault .ub
        | false =>
          let b' := applyTreeBorrowTransition b tr
          match
            rawPtrBorrowStepList
              allBorrows activeProtectors accessKind targetDecls targetLayouts rootTy rootValOpt
              accessTag entry offsetBytes accessBytes placeSize rest
          with
          | .ok rest' => .ok (b' :: rest')
          | .fault kind => .fault kind
      | false =>
        let tr := treeBorrowNodeAccess accessKind .foreignAccess b.perm isProt
        let isNoop : Bool :=
          match tr with
          | .transition p' => rawPtrTreeBorrowPermEq p' b.perm
          | _ => false
        match isNoop with
        | true =>
          match
            rawPtrBorrowStepList
              allBorrows activeProtectors accessKind targetDecls targetLayouts rootTy rootValOpt
              accessTag entry offsetBytes accessBytes placeSize rest
          with
          | .ok rest' => .ok (b :: rest')
          | .fault kind => .fault kind
        | false =>
          match
            rawPtrEntryOverlapsAccess
              targetDecls targetLayouts rootTy rootValOpt entry offsetBytes accessBytes placeSize b
          with
          | .some false =>
            match
              rawPtrBorrowStepList
                allBorrows activeProtectors accessKind targetDecls targetLayouts rootTy rootValOpt
                accessTag entry offsetBytes accessBytes placeSize rest
            with
            | .ok rest' => .ok (b :: rest')
            | .fault kind => .fault kind
          | .some true =>
            match treeBorrowTransitionIsUB tr with
            | true => .fault .ub
            | false =>
              let b' := applyTreeBorrowTransition b tr
              match
                rawPtrBorrowStepList
                  allBorrows activeProtectors accessKind targetDecls targetLayouts rootTy rootValOpt
                  accessTag entry offsetBytes accessBytes placeSize rest
              with
              | .ok rest' => .ok (b' :: rest')
              | .fault kind => .fault kind
          | .none =>
            match
              rawPtrBorrowStepList
                allBorrows activeProtectors accessKind targetDecls targetLayouts rootTy rootValOpt
                accessTag entry offsetBytes accessBytes placeSize rest
            with
            | .fault .ub => .fault .ub
            | _ => .fault .unsupported

/--
Byte-range-aware Tree Borrows check and permission transition for a raw-pointer
read (`accessKind = .read`) or write (`accessKind = .write`) of `accessBytes`
bytes at `offsetBytes` within `entry`'s target place (of size `placeSize`).

Reference (`core::ptr::read_volatile` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2032-L2038>

> "/// - When a volatile operation is used for memory inside an [allocation], it behaves exactly like
> ///   [`read`], except for the additional guarantee that it won't be elided or reordered (see
> ///   above). This implies that the operation will actually access memory and not e.g. be lowered to
> ///   reusing data from a previous read. Other than that, all the usual rules for memory accesses
> ///   apply (including provenance).  In particular, just like in C, whether an operation is volatile
> ///   has no bearing whatsoever on questions involving concurrent accesses from multiple threads.
> ///   Volatile accesses behave exactly like non-atomic accesses in that regard."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Modeling choice: Tree Borrows is Anneal's aliasing model; the Reference does
not fix the aliasing rules.
-/
@[reducible]
def borrowsAfterRawPtrAccess
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (accessKind : TreeBorrowAccessKind)
    (targetDecls : List LocalDecl)
    (targetLayouts : LayoutTable)
    (rootTy : Ty)
    (rootValOpt : Option Value)
    (accessTag : Nat)
    (entry : BorrowEntry)
    (offsetBytes accessBytes placeSize : Nat) :
    RawPtrBorrowResult :=
  rawPtrBorrowStepList
    borrows
    activeProtectors
    accessKind
    targetDecls
    targetLayouts
    rootTy
    rootValOpt
    accessTag
    entry
    offsetBytes
    accessBytes
    placeSize
    borrows

/--
Two-phase Tree Borrows read-then-write check and transition for a volatile copy
(`volatile_copy_nonoverlapping_memory` or `volatile_copy_memory`) of `byteCount`
bytes from `(srcPtr, srcEntry)` to `(dstPtr, dstEntry)`: first applies the
source read (`borrowsAfterRawPtrAccess .read`), then looks up `dstPtr.tag` in
the post-read borrow state and applies the destination write
(`borrowsAfterRawPtrAccess .write`). If the source read freezes or conflicts a
protected destination tag, the destination write faults with `.ub`.

Reference (`core::ptr::copy` documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L575-L580>

> "/// * `src` must be [valid] for reads of `count * size_of::<T>()` bytes or that number must be 0.
> ///
> /// * `dst` must be [valid] for writes of `count * size_of::<T>()` bytes or that number must be 0,
> ///   and `dst` must remain valid even when `src` is read for `count * size_of::<T>()` bytes. (This
> ///   means if the memory ranges overlap, the `dst` pointer must not be invalidated by `src` reads.)"
-/
def borrowsAfterRawPtrCopy
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (srcDecls : List LocalDecl)
    (srcLayouts : LayoutTable)
    (srcRootTy : Ty)
    (srcRootValOpt : Option Value)
    (srcPtr : ProvenancePtr)
    (srcEntry : BorrowEntry)
    (srcPlaceSize : Nat)
    (dstDecls : List LocalDecl)
    (dstLayouts : LayoutTable)
    (dstRootTy : Ty)
    (dstRootValOpt : Option Value)
    (dstPtr : ProvenancePtr)
    (dstPlaceSize : Nat)
    (byteCount : Nat) :
    RawPtrBorrowResult :=
  match
    borrowsAfterRawPtrAccess
      borrows
      activeProtectors
      .read
      srcDecls
      srcLayouts
      srcRootTy
      srcRootValOpt
      srcPtr.tag
      srcEntry
      srcPtr.offsetBytes
      byteCount
      srcPlaceSize
  with
  | .fault kind => .fault kind
  | .ok borrows1 =>
    match lookupBorrow borrows1 dstPtr.tag with
    | .none => .fault .unsupported
    | .some dstEntry1 =>
      borrowsAfterRawPtrAccess
        borrows1
        activeProtectors
        .write
        dstDecls
        dstLayouts
        dstRootTy
        dstRootValOpt
        dstPtr.tag
        dstEntry1
        dstPtr.offsetBytes
        byteCount
        dstPlaceSize

/--
Construct the canonical unique `Value` of an inhabited zero-sized type `elemTy`
by decoding zero bytes via `decodeTypedValueFromBytes`: `Value.unit` for `()`
and function items, `Value.aggregate 0 .nil` for `[T; 0]`, nested `.aggregate`
tuples/arrays of ZSTs (preserving field/element projections), and
`Value.aggregate variantIdx .nil` for unit structs. Returns `.none`, which
callers treat as unsupported, when the codec has no value of `elemTy` over zero
bytes.

Reference (`core::ptr::read_volatile` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2052>

> "/// Note that volatile memory operations where T is a zero-sized type are noops and may be ignored."

Modeling choice: callers use this function only for an inhabited `elemTy` of
size `0`, which has exactly one value; its `Value` representation is Anneal's.
-/
@[reducible]
def rawPtrZstValue? (bodyLayouts : LayoutTable) (elemTy : Ty) : Option Value :=
  decodeTypedValueFromBytes defaultCodecFuel bodyLayouts elemTy .nil

/--
Outcome of the machine-state-independent part of a raw-pointer memory access
call (`rawPtrLoadAction`, `rawPtrStoreAction`, `volatileCopyWithinLocalAction`),
consumed by `finishRawPtrCallAction`:
- `.fault kind`: the call faults (`FailureKind.unsupported` is the fail-closed
  `MirStepNode.unsupported`);
- `.ret retVal`: the call returns `retVal` and leaves memory unchanged (a
  zero-sized access, or a load from a global allocation);
- `.retBorrows borrows' retVal`: a load through a tracked stack pointer returns
  `retVal` with the Tree Borrows state `borrows'`;
- `.retStack borrows' locals₄ callStack' callerLocals' retVal`: a store through
  a tracked stack pointer returns `retVal` with the Tree Borrows state
  `borrows'` and the updated frame slots (`writeFrameLocalSlot`).

Reference (`core::ptr::read_volatile` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2032-L2038>

> "/// - When a volatile operation is used for memory inside an [allocation], it behaves exactly like
> ///   [`read`], except for the additional guarantee that it won't be elided or reordered (see
> ///   above). This implies that the operation will actually access memory and not e.g. be lowered to
> ///   reusing data from a previous read. Other than that, all the usual rules for memory accesses
> ///   apply (including provenance).  In particular, just like in C, whether an operation is volatile
> ///   has no bearing whatsoever on questions involving concurrent accesses from multiple threads.
> ///   Volatile accesses behave exactly like non-atomic accesses in that regard."

Modeling choice: the split of a call into a state-independent action and its
commit is Anneal's; the quoted passage establishes only that an access inside
an allocation is an ordinary memory access.
-/
inductive RawPtrCallAction : Type where
  /-- The call faults with `kind`. -/
  | fault (kind : FailureKind) : RawPtrCallAction
  /-- The call returns `retVal`; memory is unchanged. -/
  | ret (retVal : Value) : RawPtrCallAction
  /-- The call returns `retVal` with Tree Borrows state `borrows'`. -/
  | retBorrows (borrows' : List BorrowEntry) (retVal : Value) : RawPtrCallAction
  /-- The call returns `retVal` with Tree Borrows state `borrows'`, active-frame
  slots `locals₄`, call stack `callStack'`, and caller referents
  `callerLocals'`. -/
  | retStack
      (borrows' : List BorrowEntry)
      (locals₄ : List LocalSlot)
      (callStack' : List SavedCallerFrame)
      (callerLocals' : List LocalSlot)
      (retVal : Value) :
      RawPtrCallAction

/--
Complete a raw-pointer memory access call from its `RawPtrCallAction`: fault,
or install the action's memory components in `s` and write the returned value
to `destination`, continuing at `targetBb` (`writeIntrinsicReturn`).

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
def finishRawPtrCallAction
    (s : MachineState)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    RawPtrCallAction → MirStepNode
  | .fault kind => MirStepNode.fail kind
  | .ret retVal => writeIntrinsicReturn s locals' destination targetBb retVal
  | .retBorrows borrows' retVal =>
    writeIntrinsicReturn
      { s with memory := { s.memory with borrows := borrows' } }
      locals'
      destination
      targetBb
      retVal
  | .retStack borrows' locals₄ callStack' callerLocals' retVal =>
    writeIntrinsicReturn
      { s with
        memory :=
          { s.memory with
            borrows := borrows'
            callStack := callStack'
            callerLocals := callerLocals' } }
      locals₄
      destination
      targetBb
      retVal

/--
Compute the `RawPtrCallAction` of a typed load `f::<T>(src) -> T` through the
raw pointer `src`, from the Tree Borrows state `borrows`, the global allocations
`globals`, the call stack `callStack`, the active protectors
`activeProtectors`, and the active frame's slots `locals'`:
- `isVolatile = true, requiresAlign = true`: `core::intrinsics::volatile_load`
  and an unlinked `core::ptr::read_volatile`;
- `isVolatile = true, requiresAlign = false`:
  `core::intrinsics::unaligned_volatile_load`;
- `isVolatile = false, requiresAlign = false`: an unlinked
  `core::ptr::read_unaligned`.

Checks, in order:
1. The argument list must be one thin pointer (`rawPtrArgOfValue?`), else
   `.ub`; `T` must resolve (`resolveRawPtrElemLayout`).
2. Alignment (`rawPtrTargetAligned?`): `align_of::<T>()` when `requiresAlign`,
   else `1`. A misaligned pointer is `.ub` even when `T` is zero-sized; an
   undecidable alignment is unsupported.
3. A non-volatile load through a null pointer is `.ub`, even when `T` is
   zero-sized: a null pointer is never valid for reads.
4. An uninhabited `T` (`tyIsUninhabited`) is `.ub`: the load would produce a
   value of a type that has none.
5. A zero-sized `T` reads no memory: the result is the unique value of `T`
   (`rawPtrZstValue?`), and no Tree Borrows access happens.
6. Otherwise (`size_of::<T>() > 0`), by `classifyRawPtrTarget`:
   - `.outside` (no provenance): a non-volatile load is `.ub` (the pointer is
     not dereferenceable for any byte); a volatile load may be a load from
     memory outside all Rust allocations, whose result the hardware defines, so
     it is unsupported.
   - `.untracked`: unsupported.
   - `.global`: a range past the end of the allocation is `.ub`; otherwise the
     value is decoded from the allocation's bytes (`evalGlobalDerefRead`) and
     must be initialized and valid for `T`.
   - `.stack`: the target place is resolved and bounds-checked
     (`resolveRawPtrStackTarget`), the value is loaded
     (`loadRawPtrStackValue`), and the Tree Borrows read transition is applied
     (`borrowsAfterRawPtrRead`).
7. The action returns the loaded value; `evalRawPtrLoadCall` writes it to the
   call destination (`finishRawPtrCallAction`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L994-L999>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1007-L1014>

> "/// Performs a volatile load from the `src` pointer.
> ///
> /// The stabilized version of this intrinsic is [`core::ptr::read_volatile`].
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_load<T>(src: *const T) -> T;"

> "/// Performs a volatile load from the `src` pointer
> /// The pointer is not required to be aligned.
> ///
> /// This intrinsic does not have a stable counterpart.
> #[rustc_intrinsic]
> #[rustc_nounwind]
> #[rustc_diagnostic_item = "intrinsics_unaligned_volatile_load"]
> pub unsafe fn unaligned_volatile_load<T>(src: *const T) -> T;"

Reference (`core::ptr::read_volatile` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2032-L2052>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2079-L2090>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2111-L2124>

> "/// - When a volatile operation is used for memory inside an [allocation], it behaves exactly like
> ///   [`read`], except for the additional guarantee that it won't be elided or reordered (see
> ///   above). This implies that the operation will actually access memory and not e.g. be lowered to
> ///   reusing data from a previous read. Other than that, all the usual rules for memory accesses
> ///   apply (including provenance).  In particular, just like in C, whether an operation is volatile
> ///   has no bearing whatsoever on questions involving concurrent accesses from multiple threads.
> ///   Volatile accesses behave exactly like non-atomic accesses in that regard.
> ///
> /// - Volatile operations, however, may also be used to access memory that is _outside_ of any Rust
> ///   allocation. In this use-case, the pointer does *not* have to be [valid] for reads. This is
> ///   typically used for CPU and peripheral registers that must be accessed via an I/O memory
> ///   mapping, most commonly at fixed addresses reserved by the hardware. These often have special
> ///   semantics associated to their manipulation, and cannot be used as general purpose memory.
> ///   Here, any address value is possible, including 0 and [`usize::MAX`], so long as the semantics
> ///   of such a read are well-defined by the target hardware. The provenance of the pointer is
> ///   irrelevant, and it can be created with [`without_provenance`]. The access must not trap. It
> ///   can cause side-effects, but those must not affect Rust-allocated memory in any way. This
> ///   access is still not considered [atomic], and as such it cannot be used for inter-thread
> ///   synchronization.
> ///
> /// Note that volatile memory operations where T is a zero-sized type are noops and may be ignored."

> "/// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `src` must be either [valid] for reads, or `T` must be a ZST, or `src` must point to memory
> ///   outside of all Rust allocations and reading from that memory must:
> ///   - not trap, and
> ///   - not cause any memory inside a Rust allocation to be modified.
> ///
> /// * `src` must be properly aligned.
> ///
> /// * Reading from `src` must produce a properly initialized value of type `T`.
> ///
> /// Note that even if `T` has size `0`, the pointer must be properly aligned."

> "pub unsafe fn read_volatile<T>(src: *const T) -> T {
>     // SAFETY: the caller must uphold the safety contract for `volatile_load`.
>     unsafe {
>         ub_checks::assert_unsafe_precondition!(
>             check_language_ub,
>             "ptr::read_volatile requires that the pointer argument is aligned",
>             (
>                 addr: *const () = src as *const (),
>                 align: usize = align_of::<T>(),
>             ) => ub_checks::maybe_is_aligned(addr, align)
>         );
>         intrinsics::volatile_load(src)
>     }
> }"

Reference (`core::ptr::read_unaligned` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L1737-L1748>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L18-L20>

> "/// Reads the value from `src` without moving it. This leaves the
> /// memory in `src` unchanged.
> ///
> /// Unlike [`read`], `read_unaligned` works with unaligned pointers.
> ///
> /// # Safety
> ///
> /// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `src` must be [valid] for reads.
> ///
> /// * `src` must point to a properly initialized value of type `T`."

> "//! * A [null] pointer is *never* valid for reads/writes.
> //! * For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes.
> //!   The following points are only concerned with non-zero-sized accesses."

Reference (The Rust Reference, "Never type"):
<https://doc.rust-lang.org/1.98.0/reference/types/never.html>

> "The never type ! is a type with no values, representing the result of computations that never complete."

Modeling choices and scope:
- The documentation states the safety contract of `read_volatile` and
  `read_unaligned`, and that `volatile_load` is the intrinsic behind
  `read_volatile`. The contract of `unaligned_volatile_load` is taken to be
  that of `volatile_load` without the alignment requirement, as its
  documentation ("The pointer is not required to be aligned.") indicates.
- A load from memory outside all Rust allocations is never executed: its
  result is defined by the hardware, so every such load, and every load
  through an untracked allocation, is unsupported. It is never reported as
  undefined behavior once the pointer is aligned.
- Volatile loads are modeled as silent steps; the guarantee that they are not
  elided or reordered concerns compilation and is not modeled.
- For an unlinked `core::ptr::read_volatile`, a misaligned pointer is `.ub`
  although the function's `check_language_ub` precondition would abort when
  UB checks are enabled; the abort is one behavior of the undefined call.
- For an unlinked `core::ptr::read_unaligned`, the model applies the documented
  contract (`src` valid for reads). The function's body copies
  `size_of::<T>()` bytes with `copy_nonoverlapping`, so executing a linked body
  can accept a null `src` when `T` is zero-sized; rejecting it here is the
  stricter of the two.
-/
def rawPtrLoadAction
    (isVolatile requiresAlign : Bool)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame)
    (activeProtectors : List Nat)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot) :
    RawPtrCallAction :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | srcVal :: .nil =>
    match rawPtrArgOfValue? ptrBytes srcVal with
    | .none => .fault .ub
    | .some srcArg =>
      match resolveRawPtrElemLayout target bodyLocalDecls bodyLayouts argOps with
      | .fault kind => .fault kind
      | .ok elemTy size align =>
        let reqAlign : Nat :=
          match requiresAlign with
          | true => align
          | false => 1
        let srcTgt := classifyRawPtrTarget borrows globals srcArg
        match
          rawPtrTargetAligned? callStack locals' bodyLocalDecls bodyLayouts reqAlign srcArg srcTgt
        with
        | .some false => .fault .ub
        | .none => .fault .unsupported
        | .some true =>
          match Bool.and (Bool.not isVolatile) (rawPtrArgIsNull srcArg) with
          | true => .fault .ub
          | false =>
            match tyIsUninhabited bodyLayouts elemTy with
            | true => .fault .ub
            | false =>
              match Nat.beq size 0 with
              | true =>
                match rawPtrZstValue? bodyLayouts elemTy with
                | .some zstVal => .ret zstVal
                | .none => .fault .unsupported
              | false =>
                match srcTgt with
                | .outside =>
                  match isVolatile with
                  | true => .fault .unsupported
                  | false => .fault .ub
                | .untracked => .fault .unsupported
                | .global ptr alloc =>
                  match Nat.ble (Nat.add ptr.offsetBytes size) (length alloc.bytes) with
                  | false => .fault .ub
                  | true =>
                    match globalAllocSliceToAbstractBytes alloc ptr.offsetBytes size with
                    | .none => .fault .unsupported
                    | .some absBytes =>
                      match rawPtrDecodeBytes bodyLayouts elemTy absBytes with
                      | .fault kind => .fault kind
                      | .ok v => .ret v
                | .stack ptr entry =>
                  match
                    resolveRawPtrStackTarget
                      callStack
                      locals'
                      bodyLocalDecls
                      bodyLayouts
                      entry
                      ptr.offsetBytes
                      size
                      false
                  with
                  | .fault kind => .fault kind
                  | .ok targetLocals targetDecls targetLayouts rootTy placeTy placeSize slot =>
                    let rootValOpt : Option Value :=
                      match slot with
                      | .init rv => .some rv
                      | _ => .none
                    match
                      borrowsAfterRawPtrAccess
                        borrows
                        activeProtectors
                        .read
                        targetDecls
                        targetLayouts
                        rootTy
                        rootValOpt
                        ptr.tag
                        entry
                        ptr.offsetBytes
                        size
                        placeSize
                    with
                    | .fault kind => .fault kind
                    | .ok borrows' =>
                      match
                        loadRawPtrStackValue
                          targetLocals
                          bodyLayouts
                          targetDecls
                          targetLayouts
                          entry
                          ptr.offsetBytes
                          size
                          placeTy
                          elemTy
                          slot
                      with
                      | .fault kind => .fault kind
                      | .ok v => .retBorrows borrows' v
  | _ => .fault .ub

/--
Evaluate a typed load `f::<T>(src) -> T` through the raw pointer `src`
(`core::intrinsics::volatile_load`, `core::intrinsics::unaligned_volatile_load`,
or an unlinked `core::ptr::read_volatile` / `core::ptr::read_unaligned`): the
`RawPtrCallAction` of `rawPtrLoadAction` on the current memory, completed by
`finishRawPtrCallAction` (fault, or write the loaded value to `destination` and
continue at `targetBb`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L994-L999>

> "/// Performs a volatile load from the `src` pointer.
> ///
> /// The stabilized version of this intrinsic is [`core::ptr::read_volatile`].
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_load<T>(src: *const T) -> T;"
-/
def evalRawPtrLoadCall
    (isVolatile requiresAlign : Bool)
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
  finishRawPtrCallAction
    s
    locals'
    destination
    targetBb
    (rawPtrLoadAction
      isVolatile
      requiresAlign
      s.memory.borrows
      s.memory.globals
      s.memory.callStack
      s.memory.activeProtectors
      target
      bodyLocalDecls
      bodyLayouts
      argOps
      argVals
      locals')

/--
Fault of storing the argument value `val` at type `elemTy`, or `.none` when
`val` is a storable value of `elemTy`:
- a value containing `Value.uninit` faults with `rawPtrUninitFault`;
- a value failing `rawPtrValueValid?` (invalid `bool`/`char` bits including
  inside tuples/arrays, null `&T`/`fn()`, uninhabited `T`, scalar width
  mismatch, or ABI-incompatible value shape) is `.ub`.

Reference (The Rust Reference, "Behavior considered undefined — Invalid
values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."

> "- A bool value must be false (0) or true (1)."

> "- A char value must not be a surrogate (i.e., must not be in the range
> 0xD800..=0xDFFF) and must be equal to or less than char::MAX."
-/
def rawPtrStoreValueFault?
    (bodyLayouts : LayoutTable)
    (elemTy : Ty)
    (val : Value) :
    Option FailureKind :=
  match valueContainsUninit val with
  | true => .some (rawPtrUninitFault elemTy.kind)
  | false =>
    match rawPtrValueValid? 16 bodyLayouts elemTy val with
    | true => .none
    | false => .some .ub

/--
Outcome of storing a typed value through a tracked raw pointer
(`storeRawPtrStackValue`): the target local's new slot (`.ok`) or a fault
(`.fault`).

Reference (`core::ptr::write` documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L1826-L1827>

> "/// Overwrites a memory location with the given value without reading or
> /// dropping the old value."
-/
inductive RawPtrStoreResult : Type where
  /-- The target local's slot after the store. -/
  | ok (slot' : LocalSlot) : RawPtrStoreResult
  /-- The store faults with `kind`. -/
  | fault (kind : FailureKind) : RawPtrStoreResult

/--
Decode the bytes `bytes` at the type `ty` of the aggregate value `oldVal` they
replace: at the layout-faithful type `resolveFaithfulAggregateTy?` finds for
`oldVal` (the type `rawPtrEncodeValue?` encodes it at). Returns `.none` for a
non-aggregate `oldVal`, for an aggregate without a layout-faithful type, when
any byte carries pointer provenance (so provenance is never silently discarded
into an integer or tag-stripped pointer), and for bytes that are not a valid
value of that type.

Reference (`core::ptr::copy` documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L566-L567>

> "/// The copy is "untyped" in the sense that data may be uninitialized or otherwise violate the
> /// requirements of `T`. The initialization state is preserved exactly."

Modeling choice: a typed slot holds only valid values of its type, so bytes
that do not decode make the store/copy/set unsupported rather than undefined
behavior.
-/
def rawPtrDecodeAggregate?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty)
    (oldVal : Value)
    (bytes : List AbstractByte) :
    Option Value :=
  match rawPtrBytesAnyProv bytes with
  | true => .none
  | false =>
    match oldVal with
    | .aggregate varIdx fields =>
      match resolveFaithfulAggregateTy? localDecls layouts ty varIdx fields with
      | .some resolvedTy =>
        match decodeTypedValueFromBytes defaultCodecFuel layouts resolvedTy bytes with
        | .some newVal =>
          match rawPtrValueValid? 16 layouts resolvedTy newVal with
          | true => .some newVal
          | false => .none
        | .none => .none
      | .none => .none
    | _ => .none

/--
Splice `patchBytes` at byte offset `offsetBytes` into the existing value
`oldVal` of a stack place of type `placeTy`, returning the decoded replacement
`Value` or `.none` (fail-closed unsupported):
- scalars require all-plain-init merged bytes and valid scalar bits for
  `placeTy` (`rawPtrValueValid?`, so writing invalid `bool`/`char` bits or
  pointer provenance into a typed scalar slot fails closed rather than
  corrupting the slot);
- thin pointers decode via `rawPtrDecodeThinPtr` (preserving `(allocId, tag)`
  and never forging an `allocId` from plain integer bytes);
- aggregates encode via `rawPtrEncodeValue?`, splice, and decode via
  `rawPtrDecodeAggregate?`.

Reference (`core::ptr::write_bytes` documentation, `library/core/src/ptr/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L665-L667>

> "/// Additionally, note that changing `*dst` in this way can easily lead to undefined behavior (UB)
> /// later if the written bytes are not a valid representation of some `T`. For instance, the
> /// following is an **incorrect** use of this function:"

Modeling choice: a typed slot holds only valid values of its declared type;
writing bytes that violate `placeTy`'s validity invariant (which is not itself
UB in Rust until read at `placeTy`) fails closed as `.unsupported`.
-/
def rawPtrSpliceBytesIntoPlace?
    (targetDecls : List LocalDecl)
    (targetLayouts : LayoutTable)
    (placeTy : Ty)
    (oldVal : Value)
    (offsetBytes : Nat)
    (patchBytes : List AbstractByte) :
    Option Value :=
  let ptrBytes := layoutPointerBytes targetLayouts
  match oldVal with
  | .uninit => .none
  | .unit =>
    match Bool.and (Nat.beq offsetBytes 0) (Nat.beq (length patchBytes) 0) with
    | true => .some .unit
    | false => .none
  | .scalar oldSc =>
    let oldBytes := encodeLittleEndianBytes oldSc.bits oldSc.sizeBytes .none
    match writeAbstractBytesAt oldBytes offsetBytes patchBytes with
    | .none => .none
    | .some mergedBytes =>
      match isThinPtrKind placeTy.kind with
      | true =>
        match rawPtrDecodeThinPtr ptrBytes placeTy.kind mergedBytes with
        | .ok v => .some v
        | .fault _ => .none
      | false =>
        match rawPtrBytesAllPlainInit mergedBytes, decodeLittleEndianBytes mergedBytes with
        | true, .some (mergedBits, _) =>
          let cand : Value := .scalar ⟨mergedBits, oldSc.sizeBytes⟩
          match rawPtrValueValid? 16 targetLayouts placeTy cand with
          | true => .some cand
          | false => .none
        | _, _ => .none
  | .ptr _ pSz =>
    match Nat.beq pSz ptrBytes with
    | false => .none
    | true =>
      match encodeUntypedValueToBytes defaultCodecFuel oldVal with
      | .none => .none
      | .some oldBytes =>
        match writeAbstractBytesAt oldBytes offsetBytes patchBytes with
        | .none => .none
        | .some mergedBytes =>
          match rawPtrDecodeThinPtr ptrBytes placeTy.kind mergedBytes with
          | .ok v => .some v
          | .fault _ => .none
  | .aggregate _ _ =>
    match rawPtrEncodeValue? targetDecls targetLayouts placeTy oldVal with
    | .none => .none
    | .some oldBytes =>
      match writeAbstractBytesAt oldBytes offsetBytes patchBytes with
      | .none => .none
      | .some mergedBytes =>
        rawPtrDecodeAggregate? targetDecls targetLayouts placeTy oldVal mergedBytes

/--
Splice `patchBytes` at byte offset `offsetBytes` into the target place of
`entry` (whose type is `placeTy`, byte size `placeSize`, and owning local has
`slot` in owning-frame slots `targetLocals`), returning the target local's new
slot or a fault (`.ub` on `.dead`, `.unsupported` when the slot cannot hold the
resulting bytes).

Reference (`core::ptr::write_unaligned` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L1937-L1940>

> "/// Overwrites a memory location with the given value without reading or
> /// dropping the old value.
> ///
> /// Unlike [`write()`], the pointer may be unaligned."
-/
def writeRawPtrBytesToStackSlot
    (targetLocals : List LocalSlot)
    (targetDecls : List LocalDecl)
    (targetLayouts : LayoutTable)
    (entry : BorrowEntry)
    (offsetBytes placeSize : Nat)
    (placeTy : Ty)
    (slot : LocalSlot)
    (patchBytes : List AbstractByte) :
    RawPtrStoreResult :=
  match slot with
  | .dead => .fault .ub
  | .uninit =>
    match
      entry.targetProjection,
      Bool.and (Nat.beq offsetBytes 0) (Nat.beq (length patchBytes) placeSize)
    with
    | .nil, true =>
      match rawPtrDecodeBytes targetLayouts placeTy patchBytes with
      | .ok v => .ok (.init v)
      | .fault _ => .fault .unsupported
    | _, _ => .fault .unsupported
  | .init rootVal =>
    let writeBack : Value → RawPtrStoreResult := fun newPlaceVal =>
      match entry.targetProjection with
      | .nil => .ok (.init newPlaceVal)
      | pHead :: pTail =>
        match
          writeProjectedForLocal
            targetLocals
            targetDecls
            targetLayouts
            entry.targetLocal
            rootVal
            (pHead :: pTail)
            newPlaceVal
        with
        | .ok rootVal' => .ok (.init rootVal')
        | .ub => .fault .ub
        | .unsupported => .fault .unsupported
    let oldRes : ProjReadResult :=
      match entry.targetProjection with
      | .nil => .ok rootVal
      | pHead :: pTail =>
        readProjectedForLocal
          targetLocals
          targetDecls
          targetLayouts
          entry.targetLocal
          rootVal
          (pHead :: pTail)
    match oldRes with
    | .ok oldVal =>
      match
        rawPtrSpliceBytesIntoPlace?
          targetDecls targetLayouts placeTy oldVal offsetBytes patchBytes
      with
      | .some newPlaceVal => writeBack newPlaceVal
      | .none => .fault .unsupported
    | _ => .fault .unsupported

/--
Store the value `val` of type `elemTy` at byte offset `offsetBytes` of the
target place of `entry`, whose type is `placeTy`, byte size `placeSize`, and
whose local has slot `slot` in owning-frame slots `targetLocals` (as resolved
by `resolveRawPtrStackTarget`), returning the local's new slot.

- When the store covers the target place exactly at its own type
  (`offsetBytes = 0` and `placeTy` is `elemTy`), `val` replaces the place's
  value (`writeProjectedForLocal` using `targetLocals`, or the whole slot for a
  whole local, which may be uninitialized). This path does not depend on the
  place's address, so it serves unaligned places such as a field of a
  `#[repr(packed)]` struct.
- Otherwise (an interior byte offset or another type) `val` is encoded to bytes
  (`rawPtrEncodeValue?`) and spliced into the place via
  `writeRawPtrBytesToStackSlot`. When the place has no byte encoding, or the
  resulting bytes are not a valid value of the place's type, the store is
  unsupported: the typed slot cannot hold them, although the store itself is
  not undefined behavior.

Reference (`core::ptr::write_unaligned` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L1937-L1956>

> "/// Overwrites a memory location with the given value without reading or
> /// dropping the old value.
> ///
> /// Unlike [`write()`], the pointer may be unaligned.
> ///
> /// `write_unaligned` does not drop the contents of `dst`. This is safe, but it
> /// could leak allocations or resources, so care should be taken not to overwrite
> /// an object that should be dropped.
> ///
> /// Additionally, it does not drop `src`. Semantically, `src` is moved into the
> /// location pointed to by `dst`.
> ///
> /// This is appropriate for initializing uninitialized memory, or overwriting
> /// memory that has previously been read with [`read_unaligned`].
> ///
> /// # Safety
> ///
> /// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `dst` must be [valid] for writes."

Modeling choice: the typed value representation and its byte codec are
Anneal's. Shapes they cannot express are unsupported, never a successful store.
-/
def storeRawPtrStackValue
    (targetLocals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (targetDecls : List LocalDecl)
    (targetLayouts : LayoutTable)
    (entry : BorrowEntry)
    (offsetBytes placeSize : Nat)
    (placeTy elemTy : Ty)
    (slot : LocalSlot)
    (val : Value) :
    RawPtrStoreResult :=
  let isDirect : Bool :=
    Bool.and (Nat.beq offsetBytes 0) (rigidTyEq placeTy.kind elemTy.kind)
  match isDirect with
  | true =>
    match slot with
    | .dead => .fault .ub
    | .uninit =>
      match entry.targetProjection with
      | .nil => .ok (.init val)
      | _ :: _ => .fault .unsupported
    | .init rootVal =>
      match entry.targetProjection with
      | .nil => .ok (.init val)
      | pHead :: pTail =>
        match
          writeProjectedForLocal
            targetLocals
            targetDecls
            targetLayouts
            entry.targetLocal
            rootVal
            (pHead :: pTail)
            val
        with
        | .ok rootVal' => .ok (.init rootVal')
        | .ub => .fault .ub
        | .unsupported => .fault .unsupported
  | false =>
    match rawPtrEncodeValue? bodyLocalDecls bodyLayouts elemTy val with
    | .none => .fault .unsupported
    | .some patchBytes =>
      writeRawPtrBytesToStackSlot
        targetLocals
        targetDecls
        targetLayouts
        entry
        offsetBytes
        placeSize
        placeTy
        slot
        patchBytes

/--
Compute the `RawPtrCallAction` of a typed store `f::<T>(dst, val)` through the
raw pointer `dst`, from the Tree Borrows state `borrows`, the global allocations
`globals`, the call stack `callStack`, the root frame's caller referents
`callerLocals`, the active protectors `activeProtectors`, and the active
frame's slots `locals'`:
- `isVolatile = true, requiresAlign = true`: `core::intrinsics::volatile_store`
  and an unlinked `core::ptr::write_volatile`;
- `isVolatile = true, requiresAlign = false`:
  `core::intrinsics::unaligned_volatile_store`;
- `isVolatile = false, requiresAlign = false`: an unlinked
  `core::ptr::write_unaligned`.

Checks, in order:
1. The argument list must be a thin pointer (`rawPtrArgOfValue?`) and a value,
   else `.ub`; `T` must resolve (`resolveRawPtrElemLayout`).
2. Alignment (`rawPtrTargetAligned?`): `align_of::<T>()` when `requiresAlign`,
   else `1`. A misaligned pointer is `.ub` even when `T` is zero-sized; an
   undecidable alignment is unsupported.
3. A non-volatile store through a null pointer is `.ub`, even when `T` is
   zero-sized: a null pointer is never valid for writes.
4. An uninhabited `T` (`tyIsUninhabited`) is `.ub`, even when `T` is
   zero-sized: passing a value of an uninhabited type is immediate UB.
5. `val` must be a storable value of `T` (`rawPtrStoreValueFault?`).
6. A zero-sized `T` writes no memory, and no Tree Borrows access happens.
7. Otherwise (`size_of::<T>() > 0`), by `classifyRawPtrTarget`:
   - `.outside` (no provenance): a non-volatile store is `.ub`; a volatile
     store may be a store to memory outside all Rust allocations, whose effect
     the hardware defines, so it is unsupported.
   - `.untracked`: unsupported.
   - `.global`: a store to an immutable allocation, or past the end of the
     allocation, is `.ub`; a store to a mutable global is unsupported.
   - `.stack`: the target place is resolved and bounds-checked
     (`resolveRawPtrStackTarget`), the byte-range-aware Tree Borrows write
     check and transition are applied (`borrowsAfterRawPtrAccess .write`:
     ancestor permissions, active protectors, and invalidation of overlapping
     foreign borrows without clobbering disjoint sibling/child borrows), the new
     slot is computed (`storeRawPtrStackValue`), and the slot is committed to
     its frame (`writeFrameLocalSlot`).
8. The action returns `()`; `evalRawPtrStoreCall` writes it to the call
   destination (`finishRawPtrCallAction`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1000-L1005>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1015-L1022>

> "/// Performs a volatile store to the `dst` pointer.
> ///
> /// The stabilized version of this intrinsic is [`core::ptr::write_volatile`].
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_store<T>(dst: *mut T, val: T);"

> "/// Performs a volatile store to the `dst` pointer.
> /// The pointer is not required to be aligned.
> ///
> /// This intrinsic does not have a stable counterpart.
> #[rustc_intrinsic]
> #[rustc_nounwind]
> #[rustc_diagnostic_item = "intrinsics_unaligned_volatile_store"]
> pub unsafe fn unaligned_volatile_store<T>(dst: *mut T, val: T);"

Reference (`core::ptr::write_volatile` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2134-L2155>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2182-L2191>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2213-L2226>

> "/// - When a volatile operation is used for memory inside an [allocation], it behaves exactly like
> ///   [`write`][write()], except for the additional guarantee that it won't be elided or reordered
> ///   (see above). This implies that the operation will actually access memory and not e.g. be
> ///   lowered to a register access. Other than that, all the usual rules for memory accesses apply
> ///   (including provenance). In particular, just like in C, whether an operation is volatile has no
> ///   bearing whatsoever on questions involving concurrent access from multiple threads. Volatile
> ///   accesses behave exactly like non-atomic accesses in that regard.
> ///
> /// - Volatile operations, however, may also be used to access memory that is _outside_ of any Rust
> ///   allocation. In this use-case, the pointer does *not* have to be [valid] for writes. This is
> ///   typically used for CPU and peripheral registers that must be accessed via an I/O memory
> ///   mapping, most commonly at fixed addresses reserved by the hardware. These often have special
> ///   semantics associated to their manipulation, and cannot be used as general purpose memory.
> ///   Here, any address value is possible, including 0 and [`usize::MAX`], so long as the semantics
> ///   of such a write are well-defined by the target hardware. The provenance of the pointer is
> ///   irrelevant, and it can be created with [`without_provenance`]. The access must not trap. It
> ///   can cause side-effects, but those must not affect Rust-allocated memory in any way. This
> ///   access is still not considered [atomic], and as such it cannot be used for inter-thread
> ///   synchronization.
> ///
> /// Note that volatile memory operations on zero-sized types (e.g., if a zero-sized type is passed
> /// to `write_volatile`) are noops and may be ignored."

> "/// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `dst` must be either [valid] for writes, or `T` must be a ZST, or `dst` must point to memory
> ///   outside of all Rust allocations and writing to that memory must:
> ///   - not trap, and
> ///   - not cause any memory inside a Rust allocation to be modified.
> ///
> /// * `dst` must be properly aligned.
> ///
> /// Note that even if `T` has size `0`, the pointer must be properly aligned."

> "pub unsafe fn write_volatile<T>(dst: *mut T, src: T) {
>     // SAFETY: the caller must uphold the safety contract for `volatile_store`.
>     unsafe {
>         ub_checks::assert_unsafe_precondition!(
>             check_language_ub,
>             "ptr::write_volatile requires that the pointer argument is aligned",
>             (
>                 addr: *mut () = dst as *mut (),
>                 align: usize = align_of::<T>(),
>             ) => ub_checks::maybe_is_aligned(addr, align)
>         );
>         intrinsics::volatile_store(dst, src);
>     }
> }"

Reference (`core::ptr::write_unaligned` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L1952-L1956>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L18-L20>

> "/// # Safety
> ///
> /// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `dst` must be [valid] for writes."

> "//! * A [null] pointer is *never* valid for reads/writes.
> //! * For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes.
> //!   The following points are only concerned with non-zero-sized accesses."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (The Rust Reference, "Never type"):
<https://doc.rust-lang.org/1.98.0/reference/types/never.html>

> "The never type ! is a type with no values, representing the result of computations that never complete."

Modeling choices and scope:
- The documentation states the safety contract of `write_volatile` and
  `write_unaligned`, and that `volatile_store` is the intrinsic behind
  `write_volatile`. The contract of `unaligned_volatile_store` is taken to be
  that of `volatile_store` without the alignment requirement, as its
  documentation ("The pointer is not required to be aligned.") indicates.
- A store to memory outside all Rust allocations is never executed: its effect
  is defined by the hardware, so every such store, every store through an
  untracked allocation, and every store to a mutable global is unsupported. It
  is never reported as undefined behavior once the pointer is aligned.
- Volatile stores are modeled as silent steps; the guarantee that they are not
  elided or reordered concerns compilation and is not modeled.
- For an unlinked `core::ptr::write_volatile`, a misaligned pointer is `.ub`
  although the function's `check_language_ub` precondition would abort when
  UB checks are enabled; the abort is one behavior of the undefined call.
- For an unlinked `core::ptr::write_unaligned`, the model applies the
  documented contract (`dst` valid for writes), which is stricter than
  executing the function's body for a null `dst` and a zero-sized `T`.
-/
def rawPtrStoreAction
    (isVolatile requiresAlign : Bool)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (activeProtectors : List Nat)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot) :
    RawPtrCallAction :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | dstVal :: val :: .nil =>
    match rawPtrArgOfValue? ptrBytes dstVal with
    | .none => .fault .ub
    | .some dstArg =>
      match resolveRawPtrElemLayout target bodyLocalDecls bodyLayouts argOps with
      | .fault kind => .fault kind
      | .ok elemTy size align =>
        let reqAlign : Nat :=
          match requiresAlign with
          | true => align
          | false => 1
        let dstTgt := classifyRawPtrTarget borrows globals dstArg
        match
          rawPtrTargetAligned? callStack locals' bodyLocalDecls bodyLayouts reqAlign dstArg dstTgt
        with
        | .some false => .fault .ub
        | .none => .fault .unsupported
        | .some true =>
          match Bool.and (Bool.not isVolatile) (rawPtrArgIsNull dstArg) with
          | true => .fault .ub
          | false =>
            match tyIsUninhabited bodyLayouts elemTy with
            | true => .fault .ub
            | false =>
              match rawPtrStoreValueFault? bodyLayouts elemTy val with
              | .some kind => .fault kind
              | .none =>
                match Nat.beq size 0 with
                | true => .ret .unit
                | false =>
                  match dstTgt with
                  | .outside =>
                    match isVolatile with
                    | true => .fault .unsupported
                    | false => .fault .ub
                  | .untracked => .fault .unsupported
                  | .global ptr alloc =>
                    match
                      mutabilityEq alloc.mutability .not,
                      Nat.ble (Nat.add ptr.offsetBytes size) (length alloc.bytes)
                    with
                    | false, true => .fault .unsupported
                    | _, _ => .fault .ub
                  | .stack ptr entry =>
                    match
                      resolveRawPtrStackTarget
                        callStack
                        locals'
                        bodyLocalDecls
                        bodyLayouts
                        entry
                        ptr.offsetBytes
                        size
                        true
                    with
                    | .fault kind => .fault kind
                    | .ok targetLocals targetDecls targetLayouts rootTy placeTy placeSize slot =>
                      let rootValOpt : Option Value :=
                        match slot with
                        | .init rv => .some rv
                        | _ => .none
                      match
                        borrowsAfterRawPtrAccess
                          borrows
                          activeProtectors
                          .write
                          targetDecls
                          targetLayouts
                          rootTy
                          rootValOpt
                          ptr.tag
                          entry
                          ptr.offsetBytes
                          size
                          placeSize
                      with
                      | .fault kind => .fault kind
                      | .ok borrows' =>
                        match
                          storeRawPtrStackValue
                            targetLocals
                            bodyLocalDecls
                            bodyLayouts
                            targetDecls
                            targetLayouts
                            entry
                            ptr.offsetBytes
                            placeSize
                            placeTy
                            elemTy
                            slot
                            val
                        with
                        | .fault kind => .fault kind
                        | .ok slot' =>
                          match
                            writeFrameLocalSlot
                              locals'
                              callStack
                              callerLocals
                              entry.targetFrameDepth
                              entry.targetLocal
                              slot'
                          with
                          | .none => .fault .unsupported
                          | .some (locals₄, callStack', callerLocals') =>
                            .retStack borrows' locals₄ callStack' callerLocals' .unit
  | _ => .fault .ub

/--
Evaluate a typed store `f::<T>(dst, val)` through the raw pointer `dst`
(`core::intrinsics::volatile_store`,
`core::intrinsics::unaligned_volatile_store`, or an unlinked
`core::ptr::write_volatile` / `core::ptr::write_unaligned`): the
`RawPtrCallAction` of `rawPtrStoreAction` on the current memory, completed by
`finishRawPtrCallAction` (fault, or install the updated memory, write `()` to
`destination`, and continue at `targetBb`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1000-L1005>

> "/// Performs a volatile store to the `dst` pointer.
> ///
> /// The stabilized version of this intrinsic is [`core::ptr::write_volatile`].
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_store<T>(dst: *mut T, val: T);"
-/
def evalRawPtrStoreCall
    (isVolatile requiresAlign : Bool)
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
  finishRawPtrCallAction
    s
    locals'
    destination
    targetBb
    (rawPtrStoreAction
      isVolatile
      requiresAlign
      s.memory.borrows
      s.memory.globals
      s.memory.callStack
      s.memory.callerLocals
      s.memory.activeProtectors
      target
      bodyLocalDecls
      bodyLayouts
      argOps
      argVals
      locals')

/--
Construct a list of `n` initialized provenance-less `AbstractByte`s equal to
`b`, used to build the byte patch of `volatile_set_memory`.

Reference (`core::ptr::write_bytes` documentation, `library/core/src/ptr/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L646-L650>

> "/// Sets `count * size_of::<T>()` bytes of memory starting at `dst` to
> /// `val`.
> ///
> /// `write_bytes` is similar to C's [`memset`], but sets `count *
> /// size_of::<T>()` bytes to `val`."
-/
@[reducible]
def rawPtrReplicateInitByte (b : UInt8) : Nat → List AbstractByte
  | .zero => .nil
  | .succ k => .init b .none :: rawPtrReplicateInitByte b k

/--
Compute the `RawPtrCallAction` of `volatile_copy_nonoverlapping_memory::<T>(dst,
src, count)` (`nonOverlapping = true`) or `volatile_copy_memory::<T>(dst, src,
count)` (`nonOverlapping = false`) for `byteCount = count * size_of::<T>() > 0`
bytes when both `src` and `dst` are tracked stack pointers.

Handles both cross-local / cross-frame copies and same-local (disjoint or
overlapping) copies uniformly in byte space:
1. Resolves both `srcEntry` (for read) and `dstEntry` (for write) with
   `resolveRawPtrStackTarget` (checking `allocDead`, child permissions,
   `rangeLen = 0`, live frame, `.dead` slot, and place bounds).
2. When `nonOverlapping = true` and both entries target the same
   `(targetFrameDepth, targetLocal)`, checks byte-range overlap in the root
   local (`byteRangesOverlapBool`): overlapping ranges fault with `.ub`,
   disjoint ranges (even sharing the same pointer tag) are permitted, and
   undecidable overlapping projections fail closed with `.unsupported`.
3. Applies the two-phase byte-range-aware Tree Borrows read-then-write
   transition (`borrowsAfterRawPtrCopy`: checks source read UB, applies foreign
   read transitions, checks destination write UB including protected
   `.reservedFrz true`, and invalidates only overlapping foreign borrows).
4. Reads the source value/bytes BEFORE modifying the destination (preserving
   `memmove` semantics on overlapping ranges): uses a direct value copy only
   when `count = 1`, both offsets are `0`, and both places exactly match
   `elemTy` and `byteCount`, and otherwise encodes `src`, slices `byteCount`
   bytes at `srcPtr.offsetBytes`, and splices them into `dst` via
   `writeRawPtrBytesToStackSlot` (failing closed `.unsupported` on `.uninit`
   source or unrepresentable destination bytes, never falsely reporting `.ub`
   on an untyped copy).

Reference (`core::ptr::copy_nonoverlapping` and `core::ptr::copy` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L455-L465>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L563-L567>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L575-L581>

> "/// Behavior is undefined if any of the following conditions are violated:
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

> "/// Copying takes place as if the bytes were copied from `src`
> /// to a temporary array and then copied from the array to `dst`.
> ///
> /// The copy is "untyped" in the sense that data may be uninitialized or otherwise violate the
> /// requirements of `T`. The initialization state is preserved exactly."

> "/// * `src` must be [valid] for reads of `count * size_of::<T>()` bytes or that number must be 0.
> ///
> /// * `dst` must be [valid] for writes of `count * size_of::<T>()` bytes or that number must be 0,
> ///   and `dst` must remain valid even when `src` is read for `count * size_of::<T>()` bytes. (This
> ///   means if the memory ranges overlap, the `dst` pointer must not be invalidated by `src` reads.)
> ///
> /// * Both `src` and `dst` must be properly aligned."

Modeling choice: `volatile_copy_memory` is documented only as the volatile
`llvm.memmove` (see `evalVolatileCopyMemoryCall`); inside Rust allocations the
model gives it the semantics of `core::ptr::copy`, the documented `memmove`.
-/
def volatileCopyStackAction
    (nonOverlapping : Bool)
    (borrows : List BorrowEntry)
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (activeProtectors : List Nat)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (locals' : List LocalSlot)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (elemTy : Ty)
    (count byteCount : Nat) :
    RawPtrCallAction :=
  match
    resolveRawPtrStackTarget
      callStack locals' bodyLocalDecls bodyLayouts srcEntry srcPtr.offsetBytes byteCount false
  with
  | .fault kind => .fault kind
  | .ok srcLocals srcDecls srcLayouts srcRootTy srcPlaceTy srcPlaceSize srcSlot =>
    match
      resolveRawPtrStackTarget
        callStack locals' bodyLocalDecls bodyLayouts dstEntry dstPtr.offsetBytes byteCount true
    with
    | .fault kind => .fault kind
    | .ok dstLocals dstDecls dstLayouts dstRootTy dstPlaceTy dstPlaceSize dstSlot =>
      let srcRootValOpt : Option Value :=
        match srcSlot with
        | .init v => .some v
        | _ => .none
      let dstRootValOpt : Option Value :=
        match dstSlot with
        | .init v => .some v
        | _ => .none
      let sameLocal : Bool :=
        Bool.and
          (Nat.beq srcEntry.targetFrameDepth dstEntry.targetFrameDepth)
          (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
      let overlapFault : Option FailureKind :=
        match Bool.and nonOverlapping sameLocal with
        | false => .none
        | true =>
          let srcBaseOpt :=
            projectionChainByteOffset?
              srcLayouts
              (.some srcRootTy)
              srcRootValOpt
              .none
              0
              srcDecls
              (normalizeSubsliceProjections
                (stripTransparentProjections srcEntry.targetProjection))
          let dstBaseOpt :=
            projectionChainByteOffset?
              dstLayouts
              (.some dstRootTy)
              dstRootValOpt
              .none
              0
              dstDecls
              (normalizeSubsliceProjections
                (stripTransparentProjections dstEntry.targetProjection))
          match srcBaseOpt, dstBaseOpt with
          | .some srcBase, .some dstBase =>
            match
              byteRangesOverlapBool
                (Nat.add srcBase srcPtr.offsetBytes)
                byteCount
                (Nat.add dstBase dstPtr.offsetBytes)
                byteCount
            with
            | true => .some .ub
            | false => .none
          | _, _ =>
            match projectionsOverlap srcEntry.targetProjection dstEntry.targetProjection with
            | false => .none
            | true => .some .unsupported
      match overlapFault with
      | .some kind => .fault kind
      | .none =>
        match
          borrowsAfterRawPtrCopy
            borrows
            activeProtectors
            srcDecls
            srcLayouts
            srcRootTy
            srcRootValOpt
            srcPtr
            srcEntry
            srcPlaceSize
            dstDecls
            dstLayouts
            dstRootTy
            dstRootValOpt
            dstPtr
            dstPlaceSize
            byteCount
        with
        | .fault kind => .fault kind
        | .ok borrows' =>
          match srcSlot with
          | .dead => .fault .ub
          | .uninit => .fault .unsupported
          | .init srcRootVal =>
            let srcBaseRes : ProjReadResult :=
              match srcEntry.targetProjection with
              | .nil => .ok srcRootVal
              | pHead :: pTail =>
                readProjectedForLocal
                  srcLocals
                  srcDecls
                  srcLayouts
                  srcEntry.targetLocal
                  srcRootVal
                  (pHead :: pTail)
            match srcBaseRes with
            | .ub => .fault .ub
            | .unsupported => .fault .unsupported
            | .ok srcBaseVal =>
              let isDirectWholeCopy : Bool :=
                Bool.and
                  (Nat.beq count 1)
                  (Bool.and
                    (Nat.beq srcPtr.offsetBytes 0)
                    (Bool.and
                      (Nat.beq dstPtr.offsetBytes 0)
                      (Bool.and
                        (Nat.beq byteCount srcPlaceSize)
                        (Bool.and
                          (Nat.beq byteCount dstPlaceSize)
                          (Bool.and
                            (rigidTyEq srcPlaceTy.kind elemTy.kind)
                            (rigidTyEq dstPlaceTy.kind elemTy.kind))))))
              let dstRes : RawPtrStoreResult :=
                match isDirectWholeCopy with
                | true =>
                  match srcBaseVal with
                  | .uninit => .fault .unsupported
                  | _ =>
                    match dstSlot with
                    | .dead => .fault .ub
                    | .uninit =>
                      match dstEntry.targetProjection with
                      | .nil => .ok (.init srcBaseVal)
                      | _ :: _ => .fault .unsupported
                    | .init dstRootVal =>
                      match dstEntry.targetProjection with
                      | .nil => .ok (.init srcBaseVal)
                      | pHead :: pTail =>
                        match
                          writeProjectedForLocal
                            dstLocals
                            dstDecls
                            dstLayouts
                            dstEntry.targetLocal
                            dstRootVal
                            (pHead :: pTail)
                            srcBaseVal
                        with
                        | .ok dstRootVal' => .ok (.init dstRootVal')
                        | .ub => .fault .ub
                        | .unsupported => .fault .unsupported
                | false =>
                  match rawPtrEncodeValue? srcDecls srcLayouts srcPlaceTy srcBaseVal with
                  | .none => .fault .unsupported
                  | .some srcBytes =>
                    match sliceAbstractBytes srcBytes srcPtr.offsetBytes byteCount with
                    | .none => .fault .unsupported
                    | .some copied =>
                      writeRawPtrBytesToStackSlot
                        dstLocals
                        dstDecls
                        dstLayouts
                        dstEntry
                        dstPtr.offsetBytes
                        dstPlaceSize
                        dstPlaceTy
                        dstSlot
                        copied
              match dstRes with
              | .fault kind => .fault kind
              | .ok dstSlot' =>
                match
                  writeFrameLocalSlot
                    locals'
                    callStack
                    callerLocals
                    dstEntry.targetFrameDepth
                    dstEntry.targetLocal
                    dstSlot'
                with
                | .none => .fault .unsupported
                | .some (locals₄, callStack', callerLocals') =>
                  .retStack borrows' locals₄ callStack' callerLocals' .unit

/--
Plan of a volatile copy call (`volatileCopyPlan`), executed by
`evalVolatileCopyMemoryCall`:
- `.fault kind`: the call faults;
- `.noCopy`: no byte is copied (`count * size_of::<T>() = 0`);
- `.copyStack srcPtr dstPtr srcEntry dstEntry elemTy count byteCount`: copy
  `byteCount = count * size_of::<T>()` bytes from the tracked stack place of
  `srcEntry` to that of `dstEntry` (with `srcPtr`, the second argument of the
  intrinsic, first and `dstPtr`, the first argument, second).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L969>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L979>

> "pub unsafe fn volatile_copy_nonoverlapping_memory<T>(dst: *mut T, src: *const T, count: usize);"

> "pub unsafe fn volatile_copy_memory<T>(dst: *mut T, src: *const T, count: usize);"
-/
inductive VolatileCopyPlan : Type where
  /-- The call faults with `kind`. -/
  | fault (kind : FailureKind) : VolatileCopyPlan
  /-- Zero bytes are copied: memory is unchanged. -/
  | noCopy : VolatileCopyPlan
  /-- Copy `byteCount` bytes (`count` elements of `elemTy`) from `srcPtr`/`srcEntry`
  to `dstPtr`/`dstEntry`. -/
  | copyStack
      (srcPtr dstPtr : ProvenancePtr)
      (srcEntry dstEntry : BorrowEntry)
      (elemTy : Ty)
      (count byteCount : Nat) :
      VolatileCopyPlan

/--
Plan a direct call `volatile_copy_nonoverlapping_memory::<T>(dst, src,
count)` or `volatile_copy_memory::<T>(dst, src, count)` as a
`VolatileCopyPlan`, which `evalVolatileCopyMemoryCall` executes (applying
overlap rejection when `nonOverlapping = true`). Both take the destination
first: the argument order `(dst, src, count)` is the opposite of
`copy_nonoverlapping(src, dst, count)`.

Checks, in order:
1. The argument list must be two thin pointers (`rawPtrArgOfValue?`) and a
   `usize`-width scalar `count`, else `.ub`; `T` must resolve
   (`resolveRawPtrElemLayout`).
2. `count * size_of::<T>()` must not exceed `isize::MAX`, else `.ub`.
3. Both `dst` and `src` must be aligned to `align_of::<T>()`
   (`rawPtrTargetAligned?`): a misaligned pointer is `.ub` even when no byte is
   copied, and an undecidable alignment is unsupported.
4. Zero bytes (`count = 0` or a zero-sized `T`) leave memory unchanged.
5. Otherwise both pointers must be tracked stack pointers
   (`classifyRawPtrTarget`). A destination in an immutable global, or either
   endpoint past the end of a global allocation, is `.ub`; every other pair
   that is not two tracked stack pointers (no provenance, an untracked
   allocation, or an in-bounds global) is unsupported, since a volatile copy
   may access memory outside all Rust allocations.
6. For tracked stack pointers, `volatileCopyStackAction` executes the copy in
   byte space with exact `allocDead`, bounds, overlap, and Tree Borrows checks.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L956-L979>

> "/// Equivalent to the appropriate `llvm.memcpy.p0i8.0i8.*` intrinsic, with
> /// a size of `count` * `size_of::<T>()` and an alignment of `align_of::<T>()`.
> ///
> /// This intrinsic does not have a stable counterpart.
> /// # Safety
> ///
> /// The safety requirements are consistent with [`copy_nonoverlapping`]
> /// while the read and write behaviors are volatile,
> /// which means it will not be optimized out unless `_count` or `size_of::<T>()` is equal to zero.
> ///
> /// [`copy_nonoverlapping`]: ptr::copy_nonoverlapping
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_copy_nonoverlapping_memory<T>(dst: *mut T, src: *const T, count: usize);
> /// Equivalent to the appropriate `llvm.memmove.p0i8.0i8.*` intrinsic, with
> /// a size of `count * size_of::<T>()` and an alignment of `align_of::<T>()`.
> ///
> /// The volatile parameter is set to `true`, so it will not be optimized out
> /// unless size is equal to zero.
> ///
> /// This intrinsic does not have a stable counterpart.
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_copy_memory<T>(dst: *mut T, src: *const T, count: usize);"

Reference (`core::ptr::copy_nonoverlapping` documentation,
`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L455-L465>

> "/// Behavior is undefined if any of the following conditions are violated:
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

Reference (`core::ptr::copy` documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L588-L589>

> "/// Note that even if the effectively copied size (`count * size_of::<T>()`) is
> /// `0`, the pointers must be properly aligned."

Modeling choices and scope:
- `volatile_copy_nonoverlapping_memory` is documented to have the safety
  requirements of `copy_nonoverlapping`. `volatile_copy_memory` is documented
  only as the volatile `llvm.memmove`; the model gives it the requirements of
  `core::ptr::copy`, the documented `memmove`.
- The bound `count * size_of::<T>() <= isize::MAX` is checked for every
  pointer: no Rust allocation is larger, and the model does not execute
  copies outside Rust allocations.
- Volatile copies are modeled as silent steps; the guarantee that they are not
  optimized out concerns compilation and is not modeled.
-/
def volatileCopyPlan
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot) :
    VolatileCopyPlan :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | dstVal :: srcVal :: .scalar countSc :: .nil =>
    match
      Nat.beq countSc.sizeBytes ptrBytes,
      rawPtrArgOfValue? ptrBytes dstVal,
      rawPtrArgOfValue? ptrBytes srcVal
    with
    | true, .some dstArg, .some srcArg =>
      match resolveRawPtrElemLayout target bodyLocalDecls bodyLayouts argOps with
      | .fault kind => .fault kind
      | .ok elemTy size align =>
        let byteCount := Nat.mul countSc.bits size
        match Nat.ble (signedHalfModulus ptrBytes) byteCount with
        | true => .fault .ub
        | false =>
          let dstTgt := classifyRawPtrTarget borrows globals dstArg
          let srcTgt := classifyRawPtrTarget borrows globals srcArg
          match
            rawPtrTargetAligned? callStack locals' bodyLocalDecls bodyLayouts align dstArg dstTgt,
            rawPtrTargetAligned? callStack locals' bodyLocalDecls bodyLayouts align srcArg srcTgt
          with
          | .some false, _ => .fault .ub
          | _, .some false => .fault .ub
          | .some true, .some true =>
            match Nat.beq byteCount 0 with
            | true => .noCopy
            | false =>
              match dstTgt, srcTgt with
              | .stack dstPtr dstEntry, .stack srcPtr srcEntry =>
                .copyStack srcPtr dstPtr srcEntry dstEntry elemTy countSc.bits byteCount
              | .global dstPtr dstAlloc, _ =>
                match
                  mutabilityEq dstAlloc.mutability .not,
                  Nat.ble (Nat.add dstPtr.offsetBytes byteCount) (length dstAlloc.bytes)
                with
                | false, true =>
                  match srcTgt with
                  | .global srcPtr srcAlloc =>
                    match Nat.ble (Nat.add srcPtr.offsetBytes byteCount) (length srcAlloc.bytes) with
                    | true => .fault .unsupported
                    | false => .fault .ub
                  | _ => .fault .unsupported
                | _, _ => .fault .ub
              | _, .global srcPtr srcAlloc =>
                match Nat.ble (Nat.add srcPtr.offsetBytes byteCount) (length srcAlloc.bytes) with
                | true => .fault .unsupported
                | false => .fault .ub
              | _, _ => .fault .unsupported
          | _, _ => .fault .unsupported
    | _, _, _ => .fault .ub
  | _ => .fault .ub

/--
Evaluate a direct call `volatile_copy_nonoverlapping_memory::<T>(dst, src,
count)` (`nonOverlapping = true`) or `volatile_copy_memory::<T>(dst, src,
count)` (`nonOverlapping = false`) by executing its `VolatileCopyPlan`
(`volatileCopyPlan` on the current memory):
- `.fault`: fault;
- `.noCopy`: write `()` to `destination` and continue at `targetBb`;
- `.copyStack`: `volatileCopyStackAction`, completed by `finishRawPtrCallAction`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L969>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L979>

> "pub unsafe fn volatile_copy_nonoverlapping_memory<T>(dst: *mut T, src: *const T, count: usize);"

> "pub unsafe fn volatile_copy_memory<T>(dst: *mut T, src: *const T, count: usize);"
-/
def evalVolatileCopyMemoryCall
    (nonOverlapping : Bool)
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
    volatileCopyPlan
      s.memory.borrows
      s.memory.globals
      s.memory.callStack
      target
      bodyLocalDecls
      bodyLayouts
      argOps
      argVals
      locals'
  with
  | .fault kind => MirStepNode.fail kind
  | .noCopy => writeIntrinsicReturn s locals' destination targetBb .unit
  | .copyStack srcPtr dstPtr srcEntry dstEntry elemTy count byteCount =>
    finishRawPtrCallAction
      s
      locals'
      destination
      targetBb
      (volatileCopyStackAction
        nonOverlapping
        s.memory.borrows
        s.memory.callStack
        s.memory.callerLocals
        s.memory.activeProtectors
        bodyLocalDecls
        bodyLayouts
        locals'
        srcPtr
        dstPtr
        srcEntry
        dstEntry
        elemTy
        count
        byteCount)

/--
Compute the `RawPtrCallAction` of `volatile_set_memory::<T>(dst, val, count)`
for `byteCount = count * size_of::<T>() > 0` bytes on a tracked stack pointer
`dstPtr` with entry `dstEntry`:
1. Resolves `dstEntry` with `resolveRawPtrStackTarget` (checking `allocDead`,
   child write permission, `rangeLen = 0`, live frame, `.dead` slot, and place
   bounds).
2. Applies byte-range-aware Tree Borrows write checks and transitions
   (`borrowsAfterRawPtrAccess .write`).
3. Constructs `byteCount` copies of `valByte` (`rawPtrReplicateInitByte`) and
   splices them into the destination stack place (`writeRawPtrBytesToStackSlot`),
   failing closed with `.unsupported` if the resulting bytes violate the typed
   slot's validity invariant (never reporting `.ub` on the set itself).
4. Commits the updated slot via `writeFrameLocalSlot`.

Reference (`core::ptr::write_bytes` documentation, `library/core/src/ptr/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L656-L667>

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
> /// later if the written bytes are not a valid representation of some `T`. For instance, the
> /// following is an **incorrect** use of this function:"
-/
def volatileSetStackAction
    (borrows : List BorrowEntry)
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (activeProtectors : List Nat)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (locals' : List LocalSlot)
    (dstPtr : ProvenancePtr)
    (dstEntry : BorrowEntry)
    (valByte byteCount : Nat) :
    RawPtrCallAction :=
  match
    resolveRawPtrStackTarget
      callStack locals' bodyLocalDecls bodyLayouts dstEntry dstPtr.offsetBytes byteCount true
  with
  | .fault kind => .fault kind
  | .ok dstLocals dstDecls dstLayouts dstRootTy dstPlaceTy dstPlaceSize dstSlot =>
    let dstRootValOpt : Option Value :=
      match dstSlot with
      | .init v => .some v
      | _ => .none
    match
      borrowsAfterRawPtrAccess
        borrows
        activeProtectors
        .write
        dstDecls
        dstLayouts
        dstRootTy
        dstRootValOpt
        dstPtr.tag
        dstEntry
        dstPtr.offsetBytes
        byteCount
        dstPlaceSize
    with
    | .fault kind => .fault kind
    | .ok borrows' =>
      let patchBytes := rawPtrReplicateInitByte (UInt8.ofNat valByte) byteCount
      match
        writeRawPtrBytesToStackSlot
          dstLocals
          dstDecls
          dstLayouts
          dstEntry
          dstPtr.offsetBytes
          dstPlaceSize
          dstPlaceTy
          dstSlot
          patchBytes
      with
      | .fault kind => .fault kind
      | .ok dstSlot' =>
        match
          writeFrameLocalSlot
            locals'
            callStack
            callerLocals
            dstEntry.targetFrameDepth
            dstEntry.targetLocal
            dstSlot'
        with
        | .none => .fault .unsupported
        | .some (locals₄, callStack', callerLocals') =>
          .retStack borrows' locals₄ callStack' callerLocals' .unit

/--
Plan of a `volatile_set_memory` call (`volatileSetPlan`), executed by
`evalVolatileSetMemoryCall`: a fault (`.fault kind`), no memory effect
(`.noWrite`, when `count * size_of::<T>() = 0`), or a byte fill of a tracked
stack pointer (`.setStack`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L986-L992>

> "/// The safety requirements are consistent with [`write_bytes`] while the write behavior is volatile,
> /// which means it will not be optimized out unless `_count` or `size_of::<T>()` is equal to zero.
> ///
> /// [`write_bytes`]: ptr::write_bytes
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_set_memory<T>(dst: *mut T, val: u8, count: usize);"
-/
inductive VolatileSetPlan : Type where
  /-- The call faults with `kind`. -/
  | fault (kind : FailureKind) : VolatileSetPlan
  /-- Zero bytes are written: memory is unchanged. -/
  | noWrite : VolatileSetPlan
  /-- Fill `byteCount` bytes at tracked stack pointer `(dstPtr, dstEntry)` with
  `valByte`. -/
  | setStack
      (dstPtr : ProvenancePtr)
      (dstEntry : BorrowEntry)
      (valByte byteCount : Nat) :
      VolatileSetPlan

/--
Plan a direct call `volatile_set_memory::<T>(dst, val, count)` as a
`VolatileSetPlan`, which `evalVolatileSetMemoryCall` executes.

Checks, in order:
1. The argument list must be a thin pointer (`rawPtrArgOfValue?`), a `u8`
   scalar `val`, and a `usize`-width scalar `count`, else `.ub`; `T` must
   resolve (`resolveRawPtrElemLayout`).
2. `count * size_of::<T>()` must not exceed `isize::MAX`, else `.ub`.
3. `dst` must be aligned to `align_of::<T>()` (`rawPtrTargetAligned?`): a
   misaligned pointer is `.ub` even when no byte is written, and an undecidable
   alignment is unsupported.
4. Zero bytes (`count = 0` or a zero-sized `T`) leave memory unchanged.
5. Otherwise, by `classifyRawPtrTarget`: a tracked stack pointer executes
   `volatileSetStackAction` (checking `allocDead`, `rangeLen = 0`, bounds, and
   byte-range-aware Tree Borrows); a destination in an immutable global or past
   the end of a global is `.ub`; every other pointer (no provenance, an
   untracked allocation, or an in-bounds mutable global) is unsupported, since
   a volatile store may access memory outside all Rust allocations.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L980-L992>

> "/// Equivalent to the appropriate `llvm.memset.p0i8.*` intrinsic, with a
> /// size of `count * size_of::<T>()` and an alignment of `align_of::<T>()`.
> ///
> /// This intrinsic does not have a stable counterpart.
> /// # Safety
> ///
> /// The safety requirements are consistent with [`write_bytes`] while the write behavior is volatile,
> /// which means it will not be optimized out unless `_count` or `size_of::<T>()` is equal to zero.
> ///
> /// [`write_bytes`]: ptr::write_bytes
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_set_memory<T>(dst: *mut T, val: u8, count: usize);"

Reference (`core::ptr::write_bytes` documentation, `library/core/src/ptr/mod.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L656-L663>

> "/// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `dst` must be [valid] for writes of `count * size_of::<T>()` bytes.
> ///
> /// * `dst` must be properly aligned.
> ///
> /// Note that even if the effectively copied size (`count * size_of::<T>()`) is
> /// `0`, the pointer must be properly aligned."

Modeling choices and scope:
- A zero-byte volatile set is a no-op for every aligned pointer, including a
  pointer without provenance; `volatileSetStackAction` is consulted for a
  non-zero byte count through a tracked stack pointer.
- Volatile stores are modeled as silent steps; the guarantee that they are not
  optimized out concerns compilation and is not modeled.
-/
def volatileSetPlan
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot) :
    VolatileSetPlan :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | dstVal :: .scalar valSc :: .scalar countSc :: .nil =>
    match
      Bool.and (Nat.beq valSc.sizeBytes 1)
        (Bool.and (Nat.blt valSc.bits 256) (Nat.beq countSc.sizeBytes ptrBytes)),
      rawPtrArgOfValue? ptrBytes dstVal
    with
    | true, .some dstArg =>
      match resolveRawPtrElemLayout target bodyLocalDecls bodyLayouts argOps with
      | .fault kind => .fault kind
      | .ok _ size align =>
        let byteCount := Nat.mul countSc.bits size
        match Nat.ble (signedHalfModulus ptrBytes) byteCount with
        | true => .fault .ub
        | false =>
          let dstTgt := classifyRawPtrTarget borrows globals dstArg
          match
            rawPtrTargetAligned? callStack locals' bodyLocalDecls bodyLayouts align dstArg dstTgt
          with
          | .some false => .fault .ub
          | .none => .fault .unsupported
          | .some true =>
            match Nat.beq byteCount 0 with
            | true => .noWrite
            | false =>
              match dstTgt with
              | .stack dstPtr dstEntry => .setStack dstPtr dstEntry valSc.bits byteCount
              | .global dstPtr dstAlloc =>
                match
                  mutabilityEq dstAlloc.mutability .not,
                  Nat.ble (Nat.add dstPtr.offsetBytes byteCount) (length dstAlloc.bytes)
                with
                | false, true => .fault .unsupported
                | _, _ => .fault .ub
              | .outside => .fault .unsupported
              | .untracked => .fault .unsupported
    | _, _ => .fault .ub
  | _ => .fault .ub

/--
Evaluate a direct call `volatile_set_memory::<T>(dst, val, count)` by executing
its `VolatileSetPlan` (`volatileSetPlan` on the current memory): fault, write
`()` to `destination` without a memory effect, or fill bytes into the tracked
stack target (`volatileSetStackAction`, completed by `finishRawPtrCallAction`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L986-L992>

> "/// The safety requirements are consistent with [`write_bytes`] while the write behavior is volatile,
> /// which means it will not be optimized out unless `_count` or `size_of::<T>()` is equal to zero.
> ///
> /// [`write_bytes`]: ptr::write_bytes
> #[rustc_intrinsic]
> #[rustc_nounwind]
> pub unsafe fn volatile_set_memory<T>(dst: *mut T, val: u8, count: usize);"
-/
def evalVolatileSetMemoryCall
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
    volatileSetPlan
      s.memory.borrows
      s.memory.globals
      s.memory.callStack
      target
      bodyLocalDecls
      bodyLayouts
      argOps
      argVals
      locals'
  with
  | .fault kind => MirStepNode.fail kind
  | .noWrite => writeIntrinsicReturn s locals' destination targetBb .unit
  | .setStack dstPtr dstEntry valByte byteCount =>
    finishRawPtrCallAction
      s
      locals'
      destination
      targetBb
      (volatileSetStackAction
        s.memory.borrows
        s.memory.callStack
        s.memory.callerLocals
        s.memory.activeProtectors
        bodyLocalDecls
        bodyLayouts
        locals'
        dstPtr
        dstEntry
        valByte
        byteCount)

/--
Test whether `kind` is one of the seven volatile memory intrinsics
(`core::intrinsics::{unaligned_volatile_load, unaligned_volatile_store,
volatile_load, volatile_store, volatile_copy_nonoverlapping_memory,
volatile_copy_memory, volatile_set_memory}`), which
`evalDirectRustIntrinsic?` dispatches to `evalVolatileMemIntrinsicCall`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L26-L31>

> "//! # Volatiles
> //!
> //! The volatile intrinsics provide operations intended to act on I/O
> //! memory, which are guaranteed to not be reordered by the compiler
> //! across other volatile intrinsics. See [`read_volatile`][ptr::read_volatile]
> //! and [`write_volatile`][ptr::write_volatile]."
-/
@[reducible]
def isVolatileMemIntrinsicKind : RustIntrinsicKind → Bool
  | .unalignedVolatileLoad => true
  | .unalignedVolatileStore => true
  | .volatileLoad => true
  | .volatileStore => true
  | .volatileCopyNonOverlappingMemory => true
  | .volatileCopyMemory => true
  | .volatileSetMemory => true
  | _ => false

/--
Evaluate a direct call to the volatile memory intrinsic `kind`
(`isVolatileMemIntrinsicKind kind = true`) on evaluated arguments:
- `unaligned_volatile_load` / `volatile_load`: `evalRawPtrLoadCall`, volatile,
  with required alignment `1` / `align_of::<T>()`;
- `unaligned_volatile_store` / `volatile_store`: `evalRawPtrStoreCall`,
  volatile, with required alignment `1` / `align_of::<T>()`;
- `volatile_copy_nonoverlapping_memory` / `volatile_copy_memory`:
  `evalVolatileCopyMemoryCall`, non-overlapping / possibly overlapping;
- `volatile_set_memory`: `evalVolatileSetMemoryCall`.

Every other `kind` is `MirStepNode.unsupported`; `evalDirectRustIntrinsic?`
never passes one.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L956-L1022>

> "pub unsafe fn volatile_copy_nonoverlapping_memory<T>(dst: *mut T, src: *const T, count: usize);"

> "pub unsafe fn volatile_copy_memory<T>(dst: *mut T, src: *const T, count: usize);"

> "pub unsafe fn volatile_set_memory<T>(dst: *mut T, val: u8, count: usize);"

> "pub unsafe fn volatile_load<T>(src: *const T) -> T;"

> "pub unsafe fn volatile_store<T>(dst: *mut T, val: T);"

> "/// Performs a volatile load from the `src` pointer
> /// The pointer is not required to be aligned."

> "/// Performs a volatile store to the `dst` pointer.
> /// The pointer is not required to be aligned."
-/
@[reducible]
def evalVolatileMemIntrinsicCall
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
  | .unalignedVolatileLoad =>
    evalRawPtrLoadCall true false s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb
  | .unalignedVolatileStore =>
    evalRawPtrStoreCall true false s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb
  | .volatileLoad =>
    evalRawPtrLoadCall true true s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb
  | .volatileStore =>
    evalRawPtrStoreCall true true s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb
  | .volatileCopyNonOverlappingMemory =>
    evalVolatileCopyMemoryCall true s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb
  | .volatileCopyMemory =>
    evalVolatileCopyMemoryCall false s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb
  | .volatileSetMemory =>
    evalVolatileSetMemoryCall s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb
  | _ => MirStepNode.unsupported

/--
Evaluate a direct (`target.isIndirect = false`) call to one of the four
`core::ptr` raw-pointer access functions when no body for it is linked in
`Memory.callees`: `core::ptr::read_unaligned` and `core::ptr::write_unaligned`
(non-volatile, alignment `1`), and `core::ptr::read_volatile` and
`core::ptr::write_volatile` (volatile, alignment `align_of::<T>()`), with the
semantics of `evalRawPtrLoadCall` and `evalRawPtrStoreCall`. Returns `.none`
for every other `DefPath`, so the call remains an external call.

When a body is linked, `evalTerminator` executes it instead (`lookupCallee`
takes precedence): `read_volatile` and `write_volatile` call the
`volatile_load` and `volatile_store` intrinsics, and `read_unaligned` and
`write_unaligned` copy bytes with `copy_nonoverlapping`.

Reference (`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L1812-L1824>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2014-L2023>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2111-L2124>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2213-L2226>

> "pub const unsafe fn read_unaligned<T>(src: *const T) -> T {
>     let mut tmp = MaybeUninit::<T>::uninit();
>     // SAFETY: the caller must guarantee that `src` is valid for reads.
>     // `src` cannot overlap `tmp` because `tmp` was just allocated on
>     // the stack as a separate allocation.
>     //
>     // Also, since we just wrote a valid value into `tmp`, it is guaranteed
>     // to be properly initialized.
>     unsafe {
>         copy_nonoverlapping(src as *const u8, tmp.as_mut_ptr() as *mut u8, size_of::<T>());
>         tmp.assume_init()
>     }
> }"

> "pub const unsafe fn write_unaligned<T>(dst: *mut T, src: T) {
>     // SAFETY: the caller must guarantee that `dst` is valid for writes.
>     // `dst` cannot overlap `src` because the caller has mutable access
>     // to `dst` while `src` is owned by this function.
>     unsafe {
>         copy_nonoverlapping((&raw const src) as *const u8, dst as *mut u8, size_of::<T>());
>         // We are calling the intrinsic directly to avoid function calls in the generated code.
>         intrinsics::forget(src);
>     }
> }"

> "pub unsafe fn read_volatile<T>(src: *const T) -> T {
>     // SAFETY: the caller must uphold the safety contract for `volatile_load`.
>     unsafe {
>         ub_checks::assert_unsafe_precondition!(
>             check_language_ub,
>             "ptr::read_volatile requires that the pointer argument is aligned",
>             (
>                 addr: *const () = src as *const (),
>                 align: usize = align_of::<T>(),
>             ) => ub_checks::maybe_is_aligned(addr, align)
>         );
>         intrinsics::volatile_load(src)
>     }
> }"

> "pub unsafe fn write_volatile<T>(dst: *mut T, src: T) {
>     // SAFETY: the caller must uphold the safety contract for `volatile_store`.
>     unsafe {
>         ub_checks::assert_unsafe_precondition!(
>             check_language_ub,
>             "ptr::write_volatile requires that the pointer argument is aligned",
>             (
>                 addr: *mut () = dst as *mut (),
>                 align: usize = align_of::<T>(),
>             ) => ub_checks::maybe_is_aligned(addr, align)
>         );
>         intrinsics::volatile_store(dst, src);
>     }
> }"

Modeling choice: only the canonical `core::ptr::*` paths are recognized
(`rustc` prints a re-exported `std::ptr::*` item by its defining crate's
path). These functions are ordinary Rust functions, not intrinsics, so they are
not `RustIntrinsicKind`s; modeling an unlinked call by the function's
documented contract replaces an unconstrained external call.
-/
@[reducible]
def evalUnlinkedPtrAccessCall?
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    Option MirStepNode :=
  match stringEq target.defPath "core::ptr::read_unaligned" with
  | true =>
    .some
      (evalRawPtrLoadCall false false s target bodyLocalDecls bodyLayouts argOps argVals
        locals' destination targetBb)
  | false =>
    match stringEq target.defPath "core::ptr::write_unaligned" with
    | true =>
      .some
        (evalRawPtrStoreCall false false s target bodyLocalDecls bodyLayouts argOps argVals
          locals' destination targetBb)
    | false =>
      match stringEq target.defPath "core::ptr::read_volatile" with
      | true =>
        .some
          (evalRawPtrLoadCall true true s target bodyLocalDecls bodyLayouts argOps argVals
            locals' destination targetBb)
      | false =>
        match stringEq target.defPath "core::ptr::write_volatile" with
        | true =>
          .some
            (evalRawPtrStoreCall true true s target bodyLocalDecls bodyLayouts argOps argVals
              locals' destination targetBb)
        | false => .none

/--
Evaluate a value-returning `RustIntrinsicKind` (all variants except
`.constEvalSelect` and the memory intrinsics `.copyNonOverlapping`,
`.writeBytes`, and the seven volatile memory intrinsics of
`isVolatileMemIntrinsicKind`) from evaluated argument values `argVals`.

`evalDirectRustIntrinsic?` dispatches the call-form memory intrinsics
`.copyNonOverlapping` and `.writeBytes` to `evalCopyNonOverlappingCall` and
`evalWriteBytesCall`, and the volatile memory intrinsics to
`evalVolatileMemIntrinsicCall`, before reaching this function. The memory
intrinsics reach it only as the runtime function of
`core::intrinsics::const_eval_select`, where their memory effect is not modeled
and the call is `MirStepNode.unsupported` (fail closed). Captured MIR never
contains such a call: `rustc` replaces every `const_eval_select` call with a
direct call to its runtime function before `optimized_mir`
(`withConstEvalSelectIntrinsicTypeArgs`).

Malformed argument lists and values fault with `.ub`. An intrinsic whose result
depends on the signedness of an integer type parameter steps to
`MirStepNode.unsupported` when `resolveIntrinsicIsSigned` or
`resolveIntrinsicShiftSigned` cannot determine it, rather than assuming an
unsigned type.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>

> "Compiler intrinsics."

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the volatile intrinsics):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L26-L31>

> "//! # Volatiles
> //!
> //! The volatile intrinsics provide operations intended to act on I/O
> //! memory, which are guaranteed to not be reordered by the compiler
> //! across other volatile intrinsics. See [`read_volatile`][ptr::read_volatile]
> //! and [`write_volatile`][ptr::write_volatile]."
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
  | .unalignedVolatileLoad => MirStepNode.unsupported
  | .unalignedVolatileStore => MirStepNode.unsupported
  | .volatileLoad => MirStepNode.unsupported
  | .volatileStore => MirStepNode.unsupported
  | .volatileCopyNonOverlappingMemory => MirStepNode.unsupported
  | .volatileCopyMemory => MirStepNode.unsupported
  | .volatileSetMemory => MirStepNode.unsupported
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
Dispatch a direct (`target.isIndirect = false`) call to a
`CallConv.rustIntrinsic` compiler intrinsic in `evalTerminator` when
`classifyRustIntrinsic? target.defPath` returns `.some kind`: the runtime
dispatch of `const_eval_select`, the call-form memory intrinsics
(`evalCopyNonOverlappingCall`, `evalWriteBytesCall`), a volatile memory
intrinsic (`isVolatileMemIntrinsicKind`, `evalVolatileMemIntrinsicCall`), or a
value-returning intrinsic (`evalNonSelectIntrinsicCall`).

When `target.defPath` is not an intrinsic, a direct call to one of the four
`core::ptr` raw-pointer access functions without a linked body
(`core::ptr::read_unaligned`, `core::ptr::write_unaligned`,
`core::ptr::read_volatile`, `core::ptr::write_volatile`) is evaluated inline
(`evalUnlinkedPtrAccessCall?`). `evalTerminator` consults this function only
after `lookupCallee` found no body for the callee.

Returns `.none` for every other `target.defPath`, so `evalTerminator` falls
through to `MirStepNode.extCall`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>

> "Compiler intrinsics."

Reference (`core::ptr::read_volatile`, `library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L2111-L2124>

> "pub unsafe fn read_volatile<T>(src: *const T) -> T {
>     // SAFETY: the caller must uphold the safety contract for `volatile_load`.
>     unsafe {
>         ub_checks::assert_unsafe_precondition!(
>             check_language_ub,
>             "ptr::read_volatile requires that the pointer argument is aligned",
>             (
>                 addr: *const () = src as *const (),
>                 align: usize = align_of::<T>(),
>             ) => ub_checks::maybe_is_aligned(addr, align)
>         );
>         intrinsics::volatile_load(src)
>     }
> }"
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
  | .none =>
    evalUnlinkedPtrAccessCall?
      s
      target
      bodyLocalDecls
      bodyLayouts
      argOps
      argVals
      locals'
      destination
      targetBb
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
  | .some .unalignedVolatileLoad =>
    .some
      (evalVolatileMemIntrinsicCall
        .unalignedVolatileLoad
        s
        target
        bodyLocalDecls
        bodyLayouts
        argOps
        argVals
        locals'
        destination
        targetBb)
  | .some .unalignedVolatileStore =>
    .some
      (evalVolatileMemIntrinsicCall
        .unalignedVolatileStore
        s
        target
        bodyLocalDecls
        bodyLayouts
        argOps
        argVals
        locals'
        destination
        targetBb)
  | .some .volatileLoad =>
    .some
      (evalVolatileMemIntrinsicCall
        .volatileLoad
        s
        target
        bodyLocalDecls
        bodyLayouts
        argOps
        argVals
        locals'
        destination
        targetBb)
  | .some .volatileStore =>
    .some
      (evalVolatileMemIntrinsicCall
        .volatileStore
        s
        target
        bodyLocalDecls
        bodyLayouts
        argOps
        argVals
        locals'
        destination
        targetBb)
  | .some .volatileCopyNonOverlappingMemory =>
    .some
      (evalVolatileMemIntrinsicCall
        .volatileCopyNonOverlappingMemory
        s
        target
        bodyLocalDecls
        bodyLayouts
        argOps
        argVals
        locals'
        destination
        targetBb)
  | .some .volatileCopyMemory =>
    .some
      (evalVolatileMemIntrinsicCall
        .volatileCopyMemory
        s
        target
        bodyLocalDecls
        bodyLayouts
        argOps
        argVals
        locals'
        destination
        targetBb)
  | .some .volatileSetMemory =>
    .some
      (evalVolatileMemIntrinsicCall
        .volatileSetMemory
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
        evalOperands
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          (callStack := s.memory.callStack)
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
        evalOperands
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          (callStack := s.memory.callStack)
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
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        (callStack := s.memory.callStack)
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
            MirStepNode.step (enterTailCalleeFrame memAfterTeardown calleeBody argVals)
        | .none =>
          MirStepNode.extCall
            { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals,
              memory := memAfterTeardown }
            resumeExternalTailCall

/--
Evaluate basic-block `Terminator` `term` in `s`, producing the next
`MirStepNode` transition.

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
      evalOperand
        s.frame.locals
        discr
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        (callStack := s.memory.callStack)
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
      match place.projection with
      | .nil =>
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
      | proj :: rest =>
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
        evalOperands
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          (callStack := s.memory.callStack)
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
        evalOperands
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          (callStack := s.memory.callStack)
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
      evalOperand
        s.frame.locals
        cond
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        (callStack := s.memory.callStack)
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
