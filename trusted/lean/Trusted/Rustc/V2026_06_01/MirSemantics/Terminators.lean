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

/-!
## Inline intrinsic calls

`evalTerminator` evaluates a `TerminatorKind.call` of the following
`core::intrinsics` items inline, in one step, when no transparent body for the
item is available: `exact_div` (handled directly in `evalTerminator`), the
integer bit intrinsics (`IntegerBitIntrinsic`), `rotate_left`, `rotate_right`,
`saturating_add`, `saturating_sub`, `write_bytes`, and `arith_offset` (along
with its `wrapping_offset` alias). Each returns to `target` with `stmtIdx := 0`,
as a returning call does.
-/

/--
Map the canonical `DefPath` of a one-operand integer bit intrinsic to its
`IntegerBitIntrinsic`.
-/
def integerBitIntrinsicOfPath? (defPath : DefPath) : Option IntegerBitIntrinsic :=
  match stringEq defPath "core::intrinsics::ctpop" with
  | true => .some .ctpop
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
  match stringEq defPath "core::intrinsics::bswap" with
  | true => .some .bswap
  | false =>
  match stringEq defPath "core::intrinsics::bitreverse" with
  | true => .some .bitreverse
  | false => .none

/--
Byte width of an operand whose declared type is a primitive integer type
(`u8`..`u128`, `usize`, `i8`..`i128`, `isize`), and `.none` for every other
operand type.
-/
def integerOperandBytes?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    Option Nat :=
  match operandTy localDecls layouts op with
  | .some ty => intCastTargetBytes ty.kind
  | .none => .none

/--
Byte size of the pointee `T` of an operand of type `*const T`, `*mut T`, `&T`,
or `&mut T`, resolved directly from `pointeeTy.kind` via `rigidTyKindByteSize`
(never consulting `LayoutTable.lookup` on `pointeeTyOf`'s synthetic placeholder
`layoutIdx := 0`).
-/
def operandPointeeBytes?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    Option Nat :=
  match operandTy localDecls layouts op with
  | .some ptrTy =>
    match pointeeTyOf ptrTy with
    | .some pointeeTy => rigidTyKindByteSize pointeeTy.kind
    | .none => .none
  | .none => .none

/--
Step to block `targetBb` (statement `0`) with `locals` and `mem`, the
continuation of a returning intrinsic call.
-/
def intrinsicReturnTo
    (s : MachineState)
    (targetBb : BasicBlockIdx)
    (locals : List LocalSlot)
    (mem : Memory) :
    MirStepNode :=
  MirStepNode.step {
    frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := locals }
    memory := mem
  }

/--
Write the return value `retVal` of an intrinsic call to `destination` and step
to `targetBb`; writing to a dead or otherwise invalid destination is undefined
behavior, exactly as for `exact_div`.
-/
def intrinsicWriteReturn
    (s : MachineState)
    (locals : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (retVal : Value) :
    MirStepNode :=
  match writePlaceValue locals s.memory.borrows destination retVal with
  | .ok updatedLocals => intrinsicReturnTo s targetBb updatedLocals s.memory
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported

/--
Largest byte count of a Rust value or memory access on a 64-bit target,
`isize::MAX = 2^63 - 1`.

Reference (`core::ptr::write_bytes`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.write_bytes.html>

> "`dst` must be valid for writes of `count * size_of::<T>()` bytes."

Reference (`core::ptr`, \"Allocation\", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/index.html#allocation>

> "For any allocation with base address, size, and a set of addresses, the
> following are guaranteed: ... The size of an allocation is at most
> `isize::MAX` bytes."

An access of more than `isize::MAX` bytes therefore cannot lie inside any
allocation, so such a `write_bytes` is undefined behavior.
-/
@[reducible]
def isizeMaxBytes : Nat := 9223372036854775807

/--
Fill `byteCount` little-endian bytes with the byte `byte`:
`∑_{i < byteCount} byte * 256^i`.
-/
def repeatByteBits (byte : Nat) : Nat → Nat
  | .zero => 0
  | .succ k => Nat.add byte (Nat.mul 256 (repeatByteBits byte k))

/--
Evaluate `core::intrinsics::write_bytes::<T>(dst, val, count)` on the
evaluated arguments `dstVal` (a pointer carrying provenance `.ptr dstPtr _` or
an 8-byte provenance-free address `.scalar addr`), `val`, and `count`.

1. `count * size_of::<T>()` bytes are written; a byte count above
   `isize::MAX` is undefined behavior.
2. A zero byte count writes nothing (even when `dstVal` carries no provenance
   or names a dead or out-of-bounds local).
3. Otherwise `dstVal` must carry a borrow tag (`dstVal = .ptr dstPtr _`) that
   names a live declared local and permits writes (neither `.frozen` nor
   `.disabled`, matching `writePlaceValue`), and for a root-local borrow the
   written range
   `[dstPtr.offsetBytes, dstPtr.offsetBytes + count * size_of::<T>())` must lie
   inside that local; every violation (including a provenance-free address or a
   dead local on a projected borrow) is undefined behavior.
4. The fill is supported for a root local of integer type, whose every byte
   pattern is a valid value. The byte `val` replaces the written bytes of the
   local's little-endian representation. When the local is uninitialized and
   the write covers only part of it, the local stays uninitialized, because a
   partially initialized integer has no `Value`; every later read of it is
   undefined behavior, as it is in Rust.
5. The write invalidates the conflicting borrows of the local, as a write
   through `dstPtr` does (`invalidateConflictingBorrows`). Like rustc's
   interpreter, which evaluates `write_bytes` without writing its `()` return
   value, the call leaves `destination` unchanged.

Reference (`core::ptr::write_bytes`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.write_bytes.html>

> "Sets `count * size_of::<T>()` bytes of memory starting at `dst` to `val`."
>
> "Behavior is undefined if any of the following conditions are violated:
>
> - `dst` must be valid for writes of `count * size_of::<T>()` bytes.
> - `dst` must be properly aligned.
>
> Note that even if the effectively copied size (`count * size_of::<T>()`) is
> `0`, the pointer must be properly aligned."

Modeling gap: Anneal's pointers carry no address, so this evaluation does not
check alignment; rustc's interpreter (`write_bytes_intrinsic`) does not check
it either.
-/
def evalWriteBytesCall
    (s : MachineState)
    (dstOp : Operand)
    (dstVal : Value)
    (val count : ScalarInt)
    (locals' : List LocalSlot)
    (targetBb : BasicBlockIdx)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    MirStepNode :=
  let dstPtr? : Option (Option ProvenancePtr) :=
    match dstVal with
    | .ptr dstPtr _ => .some (.some dstPtr)
    | .scalar addr =>
      match Nat.beq addr.sizeBytes 8 with
      | true => .some .none
      | false => .none
    | _ => .none
  match dstPtr?, operandPointeeBytes? localDecls layouts dstOp with
  | .some maybePtr, .some elemBytes =>
    let total := Nat.mul count.bits elemBytes
    match Nat.ble total isizeMaxBytes with
    | false => MirStepNode.fail .ub
    | true =>
      match Nat.beq total 0 with
      | true => intrinsicReturnTo s targetBb locals' s.memory
      | false =>
        match maybePtr with
        | .none => MirStepNode.fail .ub
        | .some dstPtr =>
          match lookupBorrow s.memory.borrows dstPtr.tag with
          | .none => MirStepNode.fail .ub
          | .some entry =>
            match entry.perm with
            | .frozen => MirStepNode.fail .ub
            | .disabled => MirStepNode.fail .ub
            | _ =>
              match get? locals' entry.targetLocal, get? localDecls entry.targetLocal with
              | .none, _ => MirStepNode.fail .ub
              | .some .dead, _ => MirStepNode.fail .ub
              | _, .none => MirStepNode.fail .ub
              | .some slot, .some decl =>
                match entry.targetProjection with
                | _ :: _ => MirStepNode.unsupported
                | .nil =>
                  match intCastTargetBytes decl.ty.kind with
                  | .none => MirStepNode.unsupported
                  | .some targetBytes =>
                    match Nat.ble (Nat.add dstPtr.offsetBytes total) targetBytes with
                    | false => MirStepNode.fail .ub
                    | true =>
                      let off := dstPtr.offsetBytes
                      let fill := repeatByteBits (Nat.mod val.bits 256) total
                      let newSlot? : Option LocalSlot :=
                        match slot with
                        | .dead => .none
                        | .uninit =>
                          match Bool.and (Nat.beq off 0) (Nat.beq total targetBytes) with
                          | true => .some (.init (.scalar ⟨fill, targetBytes⟩))
                          | false => .some .uninit
                        | .init (.scalar sc) =>
                          let lowMod := scalarModulus off
                          let highMod := scalarModulus (Nat.add off total)
                          let old := wrapScalarBits sc.bits (scalarModulus targetBytes)
                          .some (.init (.scalar ⟨
                            Nat.add (Nat.mod old lowMod)
                              (Nat.add (Nat.mul fill lowMod)
                                (Nat.mul (Nat.div old highMod) highMod)),
                            targetBytes⟩))
                        | .init _ => .none
                      match newSlot? with
                      | .none => MirStepNode.fail .ub
                      | .some newSlot =>
                        match set? locals' entry.targetLocal newSlot with
                        | .none => MirStepNode.fail .ub
                        | .some locals'' =>
                          intrinsicReturnTo s targetBb locals''
                            { s.memory with
                              borrows :=
                                invalidateConflictingBorrows
                                  s.memory.borrows
                                  entry.targetLocal
                                  (.some dstPtr.tag) }
  | _, _ => MirStepNode.unsupported

/--
Evaluate `core::intrinsics::arith_offset::<T>(ptr, count)`: offset `ptr` by
`count * size_of::<T>()` bytes with two's-complement wrapping, keeping its
provenance and requiring neither a live allocation nor an in-bounds result.

`count : isize` is the 8-byte two's-complement pattern `count.bits`, so the
byte offset `count * size_of::<T>()` modulo `2^64` is
`count.bits * size_of::<T>()` modulo `2^64`. For a pointer carrying a borrow
tag the offset is added to `offsetBytes`, and for an address without provenance
(`.scalar`) to the address itself; both wrap modulo `2^64`.

Reference (`core::intrinsics::arith_offset`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/intrinsics/fn.arith_offset.html>

> "Calculates the offset from a pointer, potentially wrapping."
>
> "Unlike the `offset` intrinsic, this intrinsic does not restrict the
> resulting pointer to point into or at the end of an allocated object, and it
> wraps with two's complement arithmetic. The resulting value is not
> necessarily valid to be used to actually access memory."
-/
def evalArithOffsetCall
    (s : MachineState)
    (ptrOp : Operand)
    (ptrVal count : Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    MirStepNode :=
  match operandPointeeBytes? localDecls layouts ptrOp, count with
  | .some elemBytes, .scalar countSc =>
    match Nat.beq countSc.sizeBytes 8 with
    | false => MirStepNode.unsupported
    | true =>
      let delta := Nat.mul countSc.bits elemBytes
      let addrModulus := scalarModulus 8
      match ptrVal with
      | .ptr p sz =>
        intrinsicWriteReturn s locals' destination targetBb
          (.ptr { p with offsetBytes := Nat.mod (Nat.add p.offsetBytes delta) addrModulus } sz)
      | .scalar addr =>
        match Nat.beq addr.sizeBytes 8 with
        | false => MirStepNode.unsupported
        | true =>
          intrinsicWriteReturn s locals' destination targetBb
            (.scalar ⟨Nat.mod (Nat.add addr.bits delta) addrModulus, 8⟩)
      | _ => MirStepNode.fail .ub
  | _, _ => MirStepNode.unsupported

/--
Evaluate a call to one of the inline intrinsics other than `exact_div` on the
evaluated arguments `argVals` (with `locals'` after evaluating them), or return
`.none` when `defPath` names none of them.

Integer intrinsics require operands of integer type whose values have the
type's width, and `rotate_left` / `rotate_right` a `u32` shift amount; other
argument shapes fail closed with `MirStepNode.unsupported`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs>

> "pub const fn rotate_left<T: Copy>(x: T, shift: u32) -> T"
>
> "pub const fn saturating_add<T: Copy>(a: T, b: T) -> T;"
>
> "pub const fn saturating_sub<T: Copy>(a: T, b: T) -> T;"
>
> "pub const unsafe fn write_bytes<T>(dst: *mut T, val: u8, count: usize);"
>
> "pub const unsafe fn arith_offset<T>(dst: *const T, offset: isize) -> *const T;"
-/
def evalInlineIntrinsicCall?
    (s : MachineState)
    (defPath : DefPath)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Option MirStepNode :=
  match integerBitIntrinsicOfPath? defPath with
  | .some op =>
    .some
      (match argOps, argVals with
      | xOp :: .nil, .scalar x :: .nil =>
        match integerOperandBytes? localDecls layouts xOp with
        | .some n =>
          match Nat.beq x.sizeBytes n with
          | true =>
            match evalIntegerBitIntrinsic op x with
            | .some r => intrinsicWriteReturn s locals' destination targetBb (.scalar r)
            | .none => MirStepNode.fail .ub
          | false => MirStepNode.unsupported
        | .none => MirStepNode.unsupported
      | _, _ => MirStepNode.unsupported)
  | .none =>
  let rotateOrSaturating? : Option (Bool × Bool) :=
    match stringEq defPath "core::intrinsics::rotate_left" with
    | true => .some (true, true)
    | false =>
    match stringEq defPath "core::intrinsics::rotate_right" with
    | true => .some (true, false)
    | false =>
    match stringEq defPath "core::intrinsics::saturating_add" with
    | true => .some (false, true)
    | false =>
    match stringEq defPath "core::intrinsics::saturating_sub" with
    | true => .some (false, false)
    | false => .none
  match rotateOrSaturating? with
  | .some (isRotate, flag) =>
    .some
      (match argOps, argVals with
      | lhsOp :: _ :: .nil, .scalar a :: .scalar b :: .nil =>
        match integerOperandBytes? localDecls layouts lhsOp with
        | .some n =>
          match Nat.beq a.sizeBytes n with
          | false => MirStepNode.unsupported
          | true =>
            match isRotate with
            | true =>
              match Nat.beq b.sizeBytes 4 with
              | true => intrinsicWriteReturn s locals' destination targetBb (.scalar (evalRotate flag a b))
              | false => MirStepNode.unsupported
            | false =>
              match
                evalSaturatingArith flag a b locals' s.memory
                  (operandIsSigned localDecls lhsOp layouts)
              with
              | .ok retVal localsAfter _ =>
                intrinsicWriteReturn s localsAfter destination targetBb retVal
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
        | .none => MirStepNode.unsupported
      | _, _ => MirStepNode.unsupported)
  | .none =>
  match stringEq defPath "core::intrinsics::write_bytes" with
  | true =>
    .some
      (match argOps, argVals with
      | dstOp :: _ :: _ :: .nil, dstVal :: .scalar val :: .scalar count :: .nil =>
        evalWriteBytesCall s dstOp dstVal val count locals' targetBb localDecls layouts
      | _, _ => MirStepNode.unsupported)
  | false =>
  let isOffsetPath : Bool :=
    Bool.or
      (Bool.or
        (stringEq defPath "core::intrinsics::arith_offset")
        (stringEq defPath "core::intrinsics::wrapping_offset"))
      (Bool.or
        (stringEq defPath "std::intrinsics::arith_offset")
        (stringEq defPath "std::intrinsics::wrapping_offset"))
  match isOffsetPath with
  | true =>
    .some
      (match argOps, argVals with
      | ptrOp :: _ :: .nil, ptrVal :: count :: .nil =>
        evalArithOffsetCall s ptrOp ptrVal count locals' destination targetBb localDecls layouts
      | _, _ => MirStepNode.unsupported)
  | false => .none

/--
Execute a basic-block `Terminator` from state `s`.

Supports `.goto`, `.return_` (both root-frame termination and interprocedural
return to `Memory.callStack`), `.unreachable`, `.switchInt`, `.assert`, `.drop`,
`.call` (including inline evaluation of `core::intrinsics::exact_div` via
`evalScalarExactDiv` and of the intrinsics of `evalInlineIntrinsicCall?`), and
`.tailCall`. When `.call` or `.tailCall` targets a
`defPath` without a transparent body in `s.memory.callees` (other than inline
intrinsics), execution emits a `MirCallE` effect interaction carrying
`(defPath, argVals, s.memory)`.

Reference (`core::intrinsics::exact_div`, Rust 1.98.0, and
`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://doc.rust-lang.org/1.98.0/core/intrinsics/fn.exact_div.html>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1932-L1939>

> "/// Performs an exact division, resulting in undefined behavior where
> /// `x % y != 0` or `y == 0` or `x == T::MIN && y == -1`"

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
  let bodyLayouts : LayoutTable :=
    match currentBody with
    | .some b => b.layouts
    | .none => emptyLayoutTable
  match term.kind with
  | .goto target =>
    MirStepNode.step {
      s with
      frame := { s.frame with blockIdx := target, stmtIdx := 0 }
    }
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
  | .call func argOps destination (.some targetBb) unwind =>
    match extractCalleeDefPath? func with
    | .none => MirStepNode.unsupported
    | .some defPath =>
      match
        evalOperands
          s.frame.locals
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok argVals locals' =>
        match findCallee? s.memory.callees defPath with
        | .some calleeBody =>
          match currentBody with
          | .none => MirStepNode.unsupported
          | .some callerBody =>
            let savedCaller : SavedCallerFrame := {
              callerBody := callerBody
              frame := { s.frame with locals := locals' }
              destination := destination
              returnTarget := targetBb
              calleeProtectors := s.memory.activeProtectors
            }
            MirStepNode.step {
              frame := {
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
        | .none =>
          match stringEq defPath "core::intrinsics::exact_div" with
          | true =>
            match argVals with
            | .scalar lhs :: .scalar rhs :: .nil =>
              let isSigned :=
                match argOps with
                | lhsOp :: _ =>
                  operandIsSigned
                    (match currentBody with
                    | .some b => b.localDecls
                    | .none => .nil)
                    lhsOp
                    bodyLayouts
                | .nil => false
              match evalScalarExactDiv lhs rhs locals' s.memory isSigned with
              | .ok retVal localsAfter memAfter =>
                match
                  writePlaceValue
                    localsAfter
                    memAfter.borrows
                    destination
                    retVal
                with
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
            match
              evalInlineIntrinsicCall? s defPath argOps argVals locals' destination targetBb
                (match currentBody with
                | .some b => b.localDecls
                | .none => .nil)
                bodyLayouts
            with
            | .some node => node
            | .none =>
              MirStepNode.extCall
                { defPath := defPath, args := argVals, memory := s.memory }
                (resumeExternalCall s locals' destination targetBb unwind)
  -- Diverging call (`target == Option.none`, return type `!`):
  -- `core::hint::unreachable_unchecked` (`library/core/src/hint.rs` at commit
  -- `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and The Rust Reference 1.98.0,
  -- "Behavior considered undefined",
  -- <https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>):
  -- "Informs the compiler that this point in the code is not reachable,
  -- enabling further optimizations. Reaching this function is completely
  -- undefined behavior."
  | .call func _ _ .none _ =>
    match extractCalleeDefPath? func with
    | .some "core::hint::unreachable_unchecked" => MirStepNode.fail .ub
    | _ => MirStepNode.unsupported
  | .tailCall func argOps =>
    match extractCalleeDefPath? func with
    | .none => MirStepNode.unsupported
    | .some defPath =>
      match
        evalOperands
          s.frame.locals
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok argVals _ =>
        match findCallee? s.memory.callees defPath with
        | .some calleeBody =>
          MirStepNode.step {
            frame := {
              blockIdx := 0
              stmtIdx := 0
              locals := initLocals calleeBody argVals
            }
            memory := {
              s.memory with
              activeCallee := .some calleeBody
            }
          }
        | .none =>
          MirStepNode.extCall
            { defPath := defPath, args := argVals, memory := s.memory }
            resumeExternalTailCall
  | .switchInt discr targets =>
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
  | .assert cond expected target unwind =>
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
