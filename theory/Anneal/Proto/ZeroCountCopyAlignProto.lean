/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted

/-!
# Prototype: zero-count / zero-byte `copy_nonoverlapping` alignment and null guard

Track-P prototype (`ws-proto-tcb-zero-count-copy-align-and-null-guard`, never
merged) for the paired TCB fix `ws-tcb-zero-count-copy-align-and-null-guard`.

## The bug

`Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingWithCount`
(`Statements.lean:3538-3550`, byte-identical in `V2026_08_01`) returns
`MirStepNode.step (advanceStmt s locals₃)` whenever `countBits = 0`, *before*
inspecting `srcVal` / `dstVal`. It therefore accepts null, misaligned, and even
non-pointer (`u32` scalar) operands, all of which Rust (`core::ptr::copy_nonoverlapping`
"must be properly aligned even when the copied size is `0`") and `lean-miri`
(`Intrinsics.copyWith`, which runs `checkAlign` on both pointers before the
zero-length `memCopy`) reject. Conversely, a ZST copy with `count > 0`
(`copy_nonoverlapping::<()>(dangling, dangling, 5)`, zero bytes) falls into the
`countBits ≠ 0` branch and spuriously faults on provenance-free dangling
pointers. Separately, the statement-level `evalCopyNonOverlapping` never checks
`countSc.sizeBytes = ptrBytes` (the terminator-level `evalCopyNonOverlappingCall`
does).

## The prototype fix

* `resolveCopyElemLayout` resolves the common pointee `T` (`elemSize`,
  `elemAlign`), fail-closed `.unsupported` on conflicting/unresolved pointees,
  `.ub` on unsized `T`, and `.unsupported` on a non-power-of-two alignment
  (malformed `LayoutTable`).
* `evalCopyNonOverlappingWithCountProto` checks `count * elemSize ≤ isize::MAX`
  first and then gates the **zero-byte** fast path on `totalBytes = 0`
  (covering both `count = 0` and ZST `elemSize = 0`). Non-zero-byte copies with
  a resolved, non-overflowing layout, and every `count ≠ 0` copy whose layout is
  not resolved, are delegated *unchanged* to the legacy
  `evalCopyNonOverlappingWithCount`, so the fix's blast radius is exactly the
  zero-byte fragment (+ the overflow guard).
* The zero-byte fragment validates each pointer through a `ZeroPtrView`
  (`malformed` / `unresolvedAddr` / `resolved addr alignKnowledge`) and a
  policy-parametric decision `ZeroPtrView.decide`:
  - `ZeroCountNullPolicy.rejectNull` (default): additionally rejects address `0`
    (mod `2^(8·ptrBytes)`, so wrapped addresses are caught);
  - `ZeroCountNullPolicy.allowRawIntrinsicNull`: exactly `lean-miri`'s raw
    `Intrinsics.copyWith` (and Rust 1.98 `core::ptr::ub_checks`, whose
    `maybe_is_aligned_and_not_null(ptr, align, is_zst)` waives the null check for
    zero-sized copies).
* On success the step is a pure no-op: `MirStepNode.step (advanceStmt s locals₃)`
  (no slot read/write, no Tree Borrows access, no overlap check).

Everything is defined over `Trusted.Rustc.V2026_06_01`; `V2026_08_01` shares the
byte-identical `evalCopyNonOverlapping*` definitions (see the prototype report).
-/

namespace Anneal.Proto.ZeroCountCopyAlign

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Policies, outcomes, and helper predicates -/

/-- Null-pointer policy for zero-byte `copy_nonoverlapping`.

* `rejectNull` (default): address `0` is `.ub` even for zero bytes. This is a
  conservative (sound-for-verification) strengthening: it is the pre-relaxation
  `core::ptr` `ub_checks` contract and is retained so that `.runtimeOptimized`
  MIR (where `-C debug-assertions=no` strips `core::ptr`'s inline `ub_checks`)
  is still checked at least as strictly as the documented library contract.
* `allowRawIntrinsicNull`: the raw `lean-miri` `Intrinsics.copyWith` semantics
  (`checkAndDerefPtr` returns `.ok none` for size `0` without resolving the
  address), which also coincides with Rust 1.98 `ub_checks`
  (`maybe_is_aligned_and_not_null(ptr, align, is_zst := true)`). -/
inductive ZeroCountNullPolicy : Type where
  | rejectNull
  | allowRawIntrinsicNull
  deriving DecidableEq, Repr

/-- Three-valued fail-closed outcome of a zero-byte check. -/
inductive ZeroCheck : Type where
  | ok
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Left-biased sequential composition (models check order: the first failing
check determines the outcome). -/
@[reducible]
def ZeroCheck.andThen : ZeroCheck → ZeroCheck → ZeroCheck
  | .ok, r => r
  | .ub, _ => .ub
  | .unsupported, _ => .unsupported

/-- Map a `ZeroCheck` to the corresponding no-op MIR step. -/
@[reducible]
def ZeroCheck.toStep (s : MachineState) (locals₃ : List LocalSlot) : ZeroCheck → MirStepNode
  | .ok => MirStepNode.step (advanceStmt s locals₃)
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported

/-- Whether `addr` denotes the null address on a `ptrBytes`-byte target
(`addr ≡ 0 (mod 2^(8·ptrBytes))`, so a canonical address that wraps to `0` is
null too). -/
@[reducible]
def isNullAddr (ptrBytes addr : Nat) : Bool :=
  Nat.beq (Nat.mod addr (scalarModulus ptrBytes)) 0

/-- `isize::MAX` on a `ptrBytes`-byte target. -/
@[reducible]
def isizeMaxBytes (ptrBytes : Nat) : Nat :=
  Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1

/-- Whether `n` is a positive power of two (Rust's `Align` invariant), via the
`Trusted` helper `Align.isPowerOfTwoBytes`. -/
@[reducible]
def isPowTwoAlign (n : Nat) : Bool :=
  Align.isPowerOfTwoBytes { bytes := n }

/-! ## 2. Pointer views and the policy-parametric decision -/

/-- Abstract view of one `copy_nonoverlapping` pointer operand on the zero-byte
fragment. -/
inductive ZeroPtrView : Type where
  /-- Not a thin pointer of the target width (`.unit`, `.aggregate`, `.uninit`,
      wrong-width or out-of-range `.scalar`, wrong-width `.ptr`): `.ub`. -/
  | malformed
  /-- Provenance pointer whose canonical address is unresolvable
      (`ptrAddress? = none`): fail closed. -/
  | unresolvedAddr
  /-- Canonical address `addr` with alignment knowledge `aligned`:
      `some true` (aligned), `some false` (misaligned), `none` (unknown, e.g.
      under-aligned backing allocation). -/
  | resolved (addr : Nat) (aligned : Option Bool)
  deriving DecidableEq, Repr

/-- Policy-parametric zero-byte decision for one pointer view. Check order:
shape (`.ub`), address resolution (`.unsupported`), null under `.rejectNull`
(`.ub`), then alignment (`.ub` if misaligned, `.unsupported` if unknown). -/
@[reducible]
def ZeroPtrView.decide (policy : ZeroCountNullPolicy) (ptrBytes : Nat) :
    ZeroPtrView → ZeroCheck
  | .malformed => .ub
  | .unresolvedAddr => .unsupported
  | .resolved addr aligned =>
    match policy, isNullAddr ptrBytes addr with
    | .rejectNull, true => .ub
    | _, _ =>
      match aligned with
      | .some true => .ok
      | .some false => .ub
      | .none => .unsupported

/-- Alignment knowledge for a provenance pointer `p` whose tag resolves to the
stack `BorrowEntry` `entry` (mirrors `Terminators.writeBytesAction:3823-3845`):

1. `elemAlign ≤ 1`: trivially aligned.
2. Resolve the target frame's `(localDecls, layouts)` at
   `entry.targetFrameDepth` (`frameLocalDeclsAndLayoutsAtDepth`: active frame
   or saved caller frame); a returned frame, missing root decl, unresolved place
   type, or unresolved place alignment is unknown (`none`).
3. The backing place's alignment must be a non-zero multiple of `elemAlign`
   (else unknown: the canonical `65536`-byte virtual page base of
   `borrowBaseAddress?` is a modelling artifact, not a real alignment
   guarantee, so `&raw mut u8_local as *mut u64` must not pass).
4. Otherwise aligned iff `p.offsetBytes % elemAlign = 0` and
   `checkTargetPlaceAlignWalk` accepts (catches misaligned `#[repr(packed)]`
   fields). -/
def stackBorrowAlignKnown
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (elemAlign : Nat)
    (p : ProvenancePtr)
    (entry : BorrowEntry) :
    Option Bool :=
  match Nat.ble elemAlign 1 with
  | true => .some true
  | false =>
    match
      frameLocalDeclsAndLayoutsAtDepth s.memory.callStack localDecls layouts
        entry.targetFrameDepth
    with
    | .none => .none
    | .some (decls, lays) =>
      match get? decls entry.targetLocal with
      | .none => .none
      | .some rootDecl =>
        match
          placeTyResolved decls lays
            { local_ := entry.targetLocal, projection := entry.targetProjection }
        with
        | .none => .none
        | .some placeTy =>
          match intrinsicRigidTyAlign decls lays placeTy.kind with
          | .none => .none
          | .some placeAlign =>
            match
              Bool.and (Bool.not (Nat.beq placeAlign 0))
                (Nat.beq (Nat.mod placeAlign elemAlign) 0)
            with
            | false => .none
            | true =>
              .some
                (Bool.and (Nat.beq (Nat.mod p.offsetBytes elemAlign) 0)
                  (checkTargetPlaceAlignWalk decls lays elemAlign p.offsetBytes
                    (.some rootDecl.ty) .none .none entry.targetProjection))

/-- Alignment knowledge for a provenance pointer into the global allocation
`g`: the base is only guaranteed `g.align.bytes`-aligned. -/
@[reducible]
def globalAllocAlignKnown (g : CapturedAllocation) (elemAlign : Nat) (p : ProvenancePtr) :
    Option Bool :=
  match Nat.ble elemAlign 1 with
  | true => .some true
  | false =>
    match
      Bool.and (Bool.not (Nat.beq g.align.bytes 0))
        (Nat.beq (Nat.mod g.align.bytes elemAlign) 0)
    with
    | false => .none
    | true => .some (Nat.beq (Nat.mod p.offsetBytes elemAlign) 0)

/-- Alignment knowledge for a function pointer or an unbacked synthetic
`ProvenancePtr`: a misaligned offset is `.ub`; otherwise unknown base alignment
is fail-closed whenever `elemAlign > 1`. -/
@[reducible]
def unbackedAlignKnown (elemAlign : Nat) (p : ProvenancePtr) : Option Bool :=
  match Nat.beq (Nat.mod p.offsetBytes elemAlign) 0 with
  | false => .some false
  | true =>
    match Nat.ble elemAlign 1 with
    | true => .some true
    | false => .none

/-- Compute the `ZeroPtrView` of one evaluated pointer operand `v`. -/
def zeroPtrView
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (elemAlign : Nat) :
    Value → ZeroPtrView
  | .scalar sc =>
    let ptrBytes := layoutPointerBytes layouts
    match
      Bool.and (Nat.beq sc.sizeBytes ptrBytes) (Nat.blt sc.bits (scalarModulus ptrBytes))
    with
    | false => .malformed
    | true => .resolved sc.bits (.some (Nat.beq (Nat.mod sc.bits elemAlign) 0))
  | .ptr p sz =>
    let ptrBytes := layoutPointerBytes layouts
    match Nat.beq sz ptrBytes with
    | false => .malformed
    | true =>
      match lookupBorrow s.memory.borrows p.tag with
      | .some entry =>
        match
          ptrAddress? s.frame.locals s.memory.borrows s.memory.callerLocals localDecls layouts
            ptrBytes p s.memory.callStack
        with
        | .none => .unresolvedAddr
        | .some addr =>
          .resolved addr (stackBorrowAlignKnown s localDecls layouts elemAlign p entry)
      | .none =>
        let addr := Nat.add (Nat.mul p.allocId 65536) p.offsetBytes
        match lookupGlobalAlloc s.memory.globals p.allocId with
        | .some g => .resolved addr (globalAllocAlignKnown g elemAlign p)
        | .none => .resolved addr (unbackedAlignKnown elemAlign p)
  | .unit => .malformed
  | .aggregate _ _ => .malformed
  | .uninit => .malformed

/-- Zero-byte check of one pointer operand (the six corner cases). -/
@[reducible]
def checkZeroCountCopyPtr
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (elemAlign : Nat)
    (v : Value) :
    ZeroCheck :=
  ZeroPtrView.decide policy (layoutPointerBytes layouts) (zeroPtrView s localDecls layouts elemAlign v)

/-- Zero-byte precheck of both operands, `src` first (as `Intrinsics.copyWith`). -/
@[reducible]
def zeroByteCopyPrecheck
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (elemAlign : Nat)
    (srcVal dstVal : Value) :
    ZeroCheck :=
  ZeroCheck.andThen
    (checkZeroCountCopyPtr policy s localDecls layouts elemAlign srcVal)
    (checkZeroCountCopyPtr policy s localDecls layouts elemAlign dstVal)

/-! ## 3. Element layout resolution -/

/-- Outcome of resolving the common pointee `T` of a `copy_nonoverlapping`. -/
inductive CopyElemLayout : Type where
  | ok (elemSize elemAlign : Nat)
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Whether the two statically known pointee types cannot be confirmed to be a
common `T`: they disagree on (`tyByteSize`-based) size, or they are not
structurally equal (`rigidTyEq`) and disagree on intrinsic size/alignment or
either side's intrinsic size/alignment is unresolved. Structurally equal
pointees never conflict on their own (so an unsized `[u8]` / `[u8]` pair still
reaches the `.ub` unsized check). Prevents synthetic MIR `*const u8 → *mut u64` from
bypassing `dst`'s alignment requirement. -/
@[reducible]
def copyPointeeLayoutsConflict
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtOpt dstPtOpt : Option Ty) :
    Bool :=
  match srcPtOpt, dstPtOpt with
  | .some sp, .some dp =>
    match rigidTyEq sp.kind dp.kind, copyPointeeSizesConflict localDecls layouts srcPtOpt dstPtOpt with
    | true, false => false
    | _, true => true
    | false, false =>
      match
        intrinsicRigidTyByteSize localDecls layouts sp.kind,
        intrinsicRigidTyByteSize localDecls layouts dp.kind,
        intrinsicRigidTyAlign localDecls layouts sp.kind,
        intrinsicRigidTyAlign localDecls layouts dp.kind
      with
      | .some a, .some b, .some c, .some d =>
        Bool.not (Bool.and (Nat.beq a b) (Nat.beq c d))
      | _, _, _, _ => true
  | _, _ => false

/-- Resolve `(elemSize, elemAlign)` for `copy_nonoverlapping::<T>(src, dst, _)`.
Unresolved size/alignment or a non-power-of-two alignment (incl. `0`) is `.ub`
for an unsized `T` (as `Terminators.writeBytesAction:3880`) and `.unsupported`
otherwise (corner case 6). -/
def resolveCopyElemLayout
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (src dst : Operand) :
    CopyElemLayout :=
  let srcPtOpt := operandPointeeTy localDecls layouts src
  let dstPtOpt := operandPointeeTy localDecls layouts dst
  match copyPointeeLayoutsConflict localDecls layouts srcPtOpt dstPtOpt with
  | true => .unsupported
  | false =>
    match copyEffectivePointee? srcPtOpt dstPtOpt with
    | .none => .unsupported
    | .some elemTy =>
      match
        intrinsicRigidTyByteSize localDecls layouts elemTy.kind,
        intrinsicRigidTyAlign localDecls layouts elemTy.kind
      with
      | .some elemSize, .some elemAlign =>
        match isPowTwoAlign elemAlign with
        | true => .ok elemSize elemAlign
        | false =>
          match isUnsizedRigidTy 8 elemTy.kind with
          | true => .ub
          | false => .unsupported
      | _, _ =>
        match isUnsizedRigidTy 8 elemTy.kind with
        | true => .ub
        | false => .unsupported

/-! ## 4. Prototype evaluators -/

/-- Zero-byte `copy_nonoverlapping` (after layout resolution and the overflow
check): validate both pointers and, on success, step as a pure no-op. -/
@[reducible]
def evalCopyNonOverlappingZeroCountProto
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (elemAlign : Nat)
    (srcVal dstVal : Value)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  ZeroCheck.toStep s locals₃
    (zeroByteCopyPrecheck policy s localDecls layouts elemAlign srcVal dstVal)

/-- Prototype replacement for `evalCopyNonOverlappingWithCount`. -/
def evalCopyNonOverlappingWithCountProto
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcVal dstVal : Value)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  match resolveCopyElemLayout localDecls layouts src dst with
  | .ok elemSize elemAlign =>
    match Nat.ble (Nat.mul countBits elemSize) (isizeMaxBytes (layoutPointerBytes layouts)) with
    | false => MirStepNode.fail .ub
    | true =>
      match Nat.beq (Nat.mul countBits elemSize) 0 with
      | true =>
        evalCopyNonOverlappingZeroCountProto policy s localDecls layouts elemAlign srcVal dstVal
          locals₃
      | false =>
        evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits
          locals₃
  | .ub =>
    match Nat.beq countBits 0 with
    | true => MirStepNode.fail .ub
    | false =>
      evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits locals₃
  | .unsupported =>
    match Nat.beq countBits 0 with
    | true => MirStepNode.unsupported
    | false =>
      evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits locals₃

/-- Whether `countSc` is a well-formed `usize` on a `ptrBytes`-byte target. -/
@[reducible]
def countScalarWellFormed (ptrBytes : Nat) (countSc : ScalarInt) : Bool :=
  Bool.and (Nat.beq countSc.sizeBytes ptrBytes) (Nat.blt countSc.bits (scalarModulus ptrBytes))

/-- Prototype replacement for statement-level `evalCopyNonOverlapping`, adding
the missing `countSc.sizeBytes = ptrBytes ∧ countSc.bits < 2^(8·ptrBytes)`
check. -/
def evalCopyNonOverlappingProto
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (src dst count : Operand)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match
    evalOperand s.frame.locals src s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls s.memory.callStack
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok srcVal locals₁ =>
    match
      evalOperand locals₁ dst s.memory.borrows s.memory.globals layouts
        s.memory.callerLocals localDecls s.memory.callStack
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok dstVal locals₂ =>
      match
        evalOperand locals₂ count s.memory.borrows s.memory.globals layouts
          s.memory.callerLocals localDecls s.memory.callStack
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok (.scalar countSc) locals₃ =>
        match countScalarWellFormed (layoutPointerBytes layouts) countSc with
        | false => MirStepNode.fail .ub
        | true =>
          evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
            countSc.bits locals₃
      | .ok _ _ => MirStepNode.fail .ub

/-- Prototype replacement for `Terminators.evalCopyNonOverlappingCall`: the
only change is calling `evalCopyNonOverlappingWithCountProto` (and checking the
count range); i.e. the terminator path inherits the statement fix
automatically once `evalCopyNonOverlappingWithCount` is patched. -/
def evalCopyNonOverlappingCallProto
    (policy : ZeroCountNullPolicy)
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
    match countScalarWellFormed (layoutPointerBytes bodyLayouts) countSc with
    | false => MirStepNode.fail .ub
    | true =>
      finishMemIntrinsicCall s
        (evalCopyNonOverlappingWithCountProto policy s srcOp dstOp bodyLocalDecls bodyLayouts
          srcVal dstVal countSc.bits locals')
        destination targetBb
  | _, _ => MirStepNode.fail .ub

/-- Prototype `evalStmt`: only `copy_nonoverlapping` is rerouted. -/
def evalStmtProto
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (stmt : Statement)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match stmt.kind with
  | .intrinsic (.copyNonOverlapping src dst count) =>
    evalCopyNonOverlappingProto policy s src dst count localDecls layouts
  | _ => evalStmt s stmt localDecls layouts

/-- The `copy_nonoverlapping` statement (operands and active body) that
`stepMirFn body s` would execute next, if any (`none` for a `.other` phase, a
missing block, a terminator position, or any other statement kind). -/
def nextCopyNonOverlapping? (body : CapturedMir) (s : MachineState) :
    Option (Operand × Operand × Operand × CapturedMir) :=
  match (s.memory.activeCallee.getD body).phase with
  | .other _ => none
  | _ =>
    match get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => none
    | some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | none => none
      | some stmt =>
        match stmt.kind with
        | .intrinsic (.copyNonOverlapping src dst count) =>
          some (src, dst, count, s.memory.activeCallee.getD body)
        | _ => none

/-- Prototype `stepMirFn`: reroutes exactly the next `copy_nonoverlapping`
statement through `evalCopyNonOverlappingProto` and is `Machine.stepMirFn`
otherwise (so it executes every other statement and terminator identically). -/
def stepMirFnProto (policy : ZeroCountNullPolicy) (body : CapturedMir) (s : MachineState) :
    MirStepNode :=
  match nextCopyNonOverlapping? body s with
  | some (src, dst, count, cb) =>
    evalCopyNonOverlappingProto policy s src dst count cb.localDecls cb.layouts
  | none => stepMirFn body s

/-! ## 5. Structural theorems (blast radius) -/

theorem ble_true_of_le {a b : Nat} (h : a ≤ b) : Nat.ble a b = true :=
  Nat.ble_eq_true_of_le h

theorem ble_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hh : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hh) (Nat.not_le.mpr h)

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hh : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hh) h

theorem blt_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

theorem fail_ne_step (k : Trusted.Effect.FailureKind) (s : MachineState) :
    MirStepNode.fail k ≠ MirStepNode.step s := by
  intro h
  simp only [MirStepNode.fail, MirStepNode.step] at h
  cases h

theorem unsupported_ne_step (s : MachineState) :
    MirStepNode.unsupported ≠ MirStepNode.step s :=
  fail_ne_step _ s

theorem step_inj {s s' : MachineState} (h : MirStepNode.step s = MirStepNode.step s') :
    s = s' := by
  simp only [MirStepNode.step] at h
  injection h with h1
  injection h1

/-- `evalStmtProto` coincides with `evalStmt` on every non-`copy_nonoverlapping`
statement. -/
theorem evalStmtProto_eq_of_not_copy
    (policy : ZeroCountNullPolicy) (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h : ∀ src dst count, stmt.kind ≠ .intrinsic (.copyNonOverlapping src dst count)) :
    evalStmtProto policy s stmt localDecls layouts = evalStmt s stmt localDecls layouts := by
  unfold evalStmtProto
  split
  · rename_i src dst count hk
    exact absurd hk (h src dst count)
  · rfl

/-- `stepMirFnProto` coincides with `stepMirFn` whenever the next step is not
a `copy_nonoverlapping` statement. -/
theorem stepMirFnProto_eq_of_not_copy
    (policy : ZeroCountNullPolicy) (body : CapturedMir) (s : MachineState)
    (h : nextCopyNonOverlapping? body s = none) :
    stepMirFnProto policy body s = stepMirFn body s := by
  unfold stepMirFnProto
  rw [h]

/-- When the next step is a `copy_nonoverlapping`, the legacy `stepMirFn`
executes exactly the legacy `evalCopyNonOverlapping` on the same operands, and
`stepMirFnProto` its prototype replacement. -/
theorem stepMirFn_eq_of_copy
    (body : CapturedMir) (s : MachineState) (src dst count : Operand) (cb : CapturedMir)
    (h : nextCopyNonOverlapping? body s = some (src, dst, count, cb)) :
    stepMirFn body s = evalCopyNonOverlapping s src dst count cb.localDecls cb.layouts := by
  unfold nextCopyNonOverlapping? at h
  unfold stepMirFn
  dsimp only
  split at h
  · cases h
  · rename_i hph
    split at h
    · cases h
    · rename_i bb hbb
      split at h
      · cases h
      · rename_i stmt hstmt
        split at h
        · rename_i s0 d0 c0 hk
          cases h
          split
          · rename_i nm hnm
            exact absurd hnm (hph nm)
          · rw [hbb]
            dsimp only
            rw [hstmt]
            dsimp only
            unfold evalStmt
            rw [hk]
        · cases h

/-- Non-zero-byte copies with a resolved, non-overflowing layout are delegated
unchanged to the legacy `evalCopyNonOverlappingWithCount`. -/
theorem evalCopyNonOverlappingWithCountProto_nonzero
    (policy : ZeroCountNullPolicy) (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hfit : countBits * elemSize ≤ isizeMaxBytes (layoutPointerBytes layouts))
    (hnz : countBits * elemSize ≠ 0) :
    evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ =
      evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits
        locals₃ := by
  have hfit' : Nat.ble (Nat.mul countBits elemSize) (isizeMaxBytes (layoutPointerBytes layouts)) =
      true := ble_true_of_le hfit
  have hnz' : Nat.beq (Nat.mul countBits elemSize) 0 = false := beq_false_of_ne hnz
  unfold evalCopyNonOverlappingWithCountProto
  rw [hl]
  dsimp only
  rw [hfit', hnz']

/-- Non-zero-count copies whose layout does not resolve are delegated unchanged
to the legacy evaluator. -/
theorem evalCopyNonOverlappingWithCountProto_unresolved_nonzero_count
    (policy : ZeroCountNullPolicy) (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits : Nat) (locals₃ : List LocalSlot)
    (hl : ∀ a b, resolveCopyElemLayout localDecls layouts src dst ≠ .ok a b)
    (hc : countBits ≠ 0) :
    evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ =
      evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits
        locals₃ := by
  unfold evalCopyNonOverlappingWithCountProto
  split
  · rename_i a b heq
    exact absurd heq (hl a b)
  · rw [beq_false_of_ne hc]
  · rw [beq_false_of_ne hc]

/-- The zero-byte fragment (`count * elemSize = 0`) is exactly the precheck
followed by a pure no-op step. -/
theorem evalCopyNonOverlappingWithCountProto_zero
    (policy : ZeroCountNullPolicy) (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hz : countBits * elemSize = 0) :
    evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ =
      ZeroCheck.toStep s locals₃
        (zeroByteCopyPrecheck policy s localDecls layouts elemAlign srcVal dstVal) := by
  have hz' : Nat.mul countBits elemSize = 0 := hz
  unfold evalCopyNonOverlappingWithCountProto
  rw [hl]
  dsimp only
  rw [hz', ble_true_of_le (Nat.zero_le _)]

/-- Unresolved / unsized pointee on a zero-count copy fails closed. -/
theorem evalCopyNonOverlappingWithCountProto_zero_count_unresolved
    (policy : ZeroCountNullPolicy) (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (locals₃ : List LocalSlot) :
    (resolveCopyElemLayout localDecls layouts src dst = .unsupported →
      evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal 0
        locals₃ = MirStepNode.unsupported) ∧
    (resolveCopyElemLayout localDecls layouts src dst = .ub →
      evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal 0
        locals₃ = MirStepNode.fail .ub) := by
  refine ⟨fun hl => ?_, fun hl => ?_⟩ <;>
    (unfold evalCopyNonOverlappingWithCountProto; rw [hl])

/-! ## 6. Null-policy refinement -/

/-- Per-view refinement: `.rejectNull` is never more permissive than
`.allowRawIntrinsicNull`, and they differ only on a null address, where
`.rejectNull` reports `.ub`. -/
theorem ZeroPtrView.decide_refines (ptrBytes : Nat) (v : ZeroPtrView) :
    (ZeroPtrView.decide .rejectNull ptrBytes v = .ok →
      ZeroPtrView.decide .allowRawIntrinsicNull ptrBytes v = .ok) ∧
    (ZeroPtrView.decide .rejectNull ptrBytes v ≠
        ZeroPtrView.decide .allowRawIntrinsicNull ptrBytes v →
      ZeroPtrView.decide .rejectNull ptrBytes v = .ub ∧
        ∃ addr al, v = .resolved addr al ∧ isNullAddr ptrBytes addr = true) := by
  cases v with
  | malformed => exact ⟨id, fun h => absurd rfl h⟩
  | unresolvedAddr => exact ⟨id, fun h => absurd rfl h⟩
  | resolved addr al =>
    cases hn : isNullAddr ptrBytes addr
    · have e : ZeroPtrView.decide .rejectNull ptrBytes (.resolved addr al) =
          ZeroPtrView.decide .allowRawIntrinsicNull ptrBytes (.resolved addr al) := by
        simp only [ZeroPtrView.decide, hn]
      exact ⟨fun h => by rw [← e]; exact h, fun h => absurd e h⟩
    · have e : ZeroPtrView.decide .rejectNull ptrBytes (.resolved addr al) = .ub := by
        simp only [ZeroPtrView.decide, hn]
      exact ⟨fun h => (by rw [e] at h; cases h), fun _ => ⟨e, addr, al, rfl, hn⟩⟩

/-- `.rejectNull` ⊑ `.allowRawIntrinsicNull` on the two-pointer precheck. -/
theorem zeroByteCopyPrecheck_refines
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (elemAlign : Nat) (srcVal dstVal : Value)
    (h : zeroByteCopyPrecheck .rejectNull s localDecls layouts elemAlign srcVal dstVal = .ok) :
    zeroByteCopyPrecheck .allowRawIntrinsicNull s localDecls layouts elemAlign srcVal dstVal =
      .ok := by
  unfold zeroByteCopyPrecheck checkZeroCountCopyPtr at *
  generalize zeroPtrView s localDecls layouts elemAlign srcVal = vs at *
  generalize zeroPtrView s localDecls layouts elemAlign dstVal = vd at *
  generalize layoutPointerBytes layouts = pb at *
  cases hs : ZeroPtrView.decide .rejectNull pb vs <;> rw [hs] at h
  · rw [(ZeroPtrView.decide_refines pb vs).1 hs]
    exact (ZeroPtrView.decide_refines pb vd).1 h
  · cases h
  · cases h

/-- **Soundness refinement**: whenever the default `.rejectNull` prototype steps
to `s'`, so does `.allowRawIntrinsicNull`, to the same post-state. -/
theorem evalCopyNonOverlappingWithCountProto_rejectNull_refines
    (s s' : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits : Nat) (locals₃ : List LocalSlot)
    (h : evalCopyNonOverlappingWithCountProto .rejectNull s src dst localDecls layouts srcVal
        dstVal countBits locals₃ = MirStepNode.step s') :
    evalCopyNonOverlappingWithCountProto .allowRawIntrinsicNull s src dst localDecls layouts
        srcVal dstVal countBits locals₃ = MirStepNode.step s' := by
  unfold evalCopyNonOverlappingWithCountProto at *
  cases hl : resolveCopyElemLayout localDecls layouts src dst with
  | ub => rw [hl] at h; exact h
  | unsupported => rw [hl] at h; exact h
  | ok sz al =>
    rw [hl] at h
    dsimp only at h ⊢
    cases hb : Nat.ble (Nat.mul countBits sz) (isizeMaxBytes (layoutPointerBytes layouts)) <;>
      rw [hb] at h
    · exact h
    · cases hz : Nat.beq (Nat.mul countBits sz) 0 <;> rw [hz] at h
      · exact h
      · unfold evalCopyNonOverlappingZeroCountProto at *
        cases hp : zeroByteCopyPrecheck .rejectNull s localDecls layouts al srcVal dstVal <;>
          rw [hp] at h
        · rw [zeroByteCopyPrecheck_refines _ _ _ _ _ _ hp]
          exact h
        · exact absurd h (fail_ne_step _ _)
        · exact absurd h (unsupported_ne_step _)

/-- On the zero-byte fragment, a successful prototype step is the pure no-op
`advanceStmt s locals₃` (memory and locals untouched; no Tree Borrows access). -/
theorem evalCopyNonOverlappingWithCountProto_zero_noop
    (policy : ZeroCountNullPolicy) (s s' : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hz : countBits * elemSize = 0)
    (h : evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ = MirStepNode.step s') :
    s' = advanceStmt s locals₃ ∧ s'.memory = s.memory := by
  rw [evalCopyNonOverlappingWithCountProto_zero policy s src dst localDecls layouts srcVal dstVal
    countBits elemSize elemAlign locals₃ hl hz] at h
  cases hp : zeroByteCopyPrecheck policy s localDecls layouts elemAlign srcVal dstVal <;>
    rw [hp] at h
  · have := step_inj h
    subst this
    exact ⟨rfl, rfl⟩
  · exact absurd h (fail_ne_step _ _)
  · exact absurd h (unsupported_ne_step _)


/-! ## 7. Standalone reference models (`lean-miri` and `core::ptr`)

Resolved-integer abstractions of the check order of
`lean-miri/vendor/Miri/Interpreter/Intrinsics.lean:143-158` (`copyWith`) with
`Miri/Memory/Access.lean:134-153` (`checkAndDerefPtr`: size `0` returns
`.ok none` before any provenance resolution, so address `0` is accepted) and
of Rust's `core::ptr::copy_nonoverlapping` (`ub_checks` precondition followed by
the intrinsic). -/

/-- Outcome of the reference models. -/
inductive RefCopyOutcome : Type where
  | ub
  | noop
  | access (bytes : Nat)
  deriving DecidableEq, Repr

/-- `lean-miri` `Intrinsics.copyWith` on resolved addresses: (1) count read,
(2) `computeSizeInBytes` against `isize::MAX`, (3) `checkAlign source`,
(4) `checkAlign dest`, (5) `memCopy` (zero bytes: `checkAndDerefPtr` returns
`none`, no resolution, no null check). -/
@[reducible]
def miriCopyWithRef (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat) :
    RefCopyOutcome :=
  match Nat.ble (Nat.mul countBits elemSize) (isizeMaxBytes ptrBytes) with
  | false => .ub
  | true =>
    match Nat.beq (Nat.mod srcAddr elemAlign) 0 with
    | false => .ub
    | true =>
      match Nat.beq (Nat.mod dstAddr elemAlign) 0 with
      | false => .ub
      | true =>
        match Nat.beq (Nat.mul countBits elemSize) 0 with
        | true => .noop
        | false => .access (Nat.mul countBits elemSize)

/-- `core::ptr::ub_checks::maybe_is_aligned_and_not_null(ptr, align, is_zst)`.
`zeroSizeWaivesNull = true` is the Rust 1.98 definition
(`maybe_is_aligned(ptr, align) && (is_zst || !ptr.is_null())`);
`zeroSizeWaivesNull = false` is the strict (pre-relaxation) contract that
`.rejectNull` implements. -/
@[reducible]
def ubChecksAlignedAndNotNull
    (zeroSizeWaivesNull : Bool) (ptrBytes addr align : Nat) (isZst : Bool) : Bool :=
  Bool.and (Nat.beq (Nat.mod addr align) 0)
    (Bool.or (Bool.and isZst zeroSizeWaivesNull) (Bool.not (isNullAddr ptrBytes addr)))

/-- `core::ptr::copy_nonoverlapping` = `ub_checks` precondition (with
`zero_size := count == 0 || size == 0`) followed by the intrinsic
(`miriCopyWithRef`). The overlap precondition is vacuous for zero bytes and is
not modelled. -/
@[reducible]
def corePtrCopyRef
    (zeroSizeWaivesNull : Bool) (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat) :
    RefCopyOutcome :=
  match
    Bool.and
      (ubChecksAlignedAndNotNull zeroSizeWaivesNull ptrBytes srcAddr elemAlign
        (Bool.or (Nat.beq countBits 0) (Nat.beq elemSize 0)))
      (ubChecksAlignedAndNotNull zeroSizeWaivesNull ptrBytes dstAddr elemAlign
        (Bool.or (Nat.beq countBits 0) (Nat.beq elemSize 0)))
  with
  | false => .ub
  | true => miriCopyWithRef ptrBytes countBits elemSize elemAlign srcAddr dstAddr

/-- The prototype's zero-byte decision on resolved views, as a reference
outcome (`none` = fail-closed `.unsupported`). Non-zero-byte copies are outside
the fragment (`access`). -/
@[reducible]
def protoFragment (policy : ZeroCountNullPolicy) (ptrBytes countBits elemSize : Nat)
    (srcV dstV : ZeroPtrView) : Option RefCopyOutcome :=
  match Nat.ble (Nat.mul countBits elemSize) (isizeMaxBytes ptrBytes) with
  | false => .some .ub
  | true =>
    match Nat.beq (Nat.mul countBits elemSize) 0 with
    | false => .some (.access (Nat.mul countBits elemSize))
    | true =>
      match ZeroCheck.andThen (ZeroPtrView.decide policy ptrBytes srcV)
          (ZeroPtrView.decide policy ptrBytes dstV) with
      | .ok => .some .noop
      | .ub => .some .ub
      | .unsupported => .none

/-- Address-exact view (alignment knowledge = actual address alignment), as
produced for every dangling `.scalar` pointer and as Miri computes it. -/
@[reducible]
def exactView (elemAlign addr : Nat) : ZeroPtrView :=
  .resolved addr (.some (Nat.beq (Nat.mod addr elemAlign) 0))

/-- `.scalar` dangling pointers produce exactly the address-exact view. -/
theorem zeroPtrView_scalar
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (elemAlign bits : Nat)
    (hlt : bits < scalarModulus (layoutPointerBytes layouts)) :
    zeroPtrView s localDecls layouts elemAlign (.scalar ⟨bits, layoutPointerBytes layouts⟩) =
      exactView elemAlign bits := by
  unfold zeroPtrView
  dsimp only
  rw [Nat.beq_refl, blt_true_of_lt hlt]
  rfl

/-- The zero-byte fragment (`count * elemSize = 0`) of `protoFragment`. -/
theorem protoFragment_zero (policy : ZeroCountNullPolicy) (ptrBytes countBits elemSize : Nat)
    (srcV dstV : ZeroPtrView) (hz : countBits * elemSize = 0) :
    protoFragment policy ptrBytes countBits elemSize srcV dstV =
      match ZeroCheck.andThen (ZeroPtrView.decide policy ptrBytes srcV)
          (ZeroPtrView.decide policy ptrBytes dstV) with
      | .ok => .some .noop
      | .ub => .some .ub
      | .unsupported => .none := by
  have hz' : Nat.mul countBits elemSize = 0 := hz
  unfold protoFragment
  rw [hz', ble_true_of_le (Nat.zero_le _)]

/-- **Equivalence 1** (`.allowRawIntrinsicNull` ≡ `lean-miri`
`Intrinsics.copyWith`) on the resolved zero-byte fragment. -/
theorem protoFragment_allowRaw_eq_miri
    (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat)
    (hz : countBits * elemSize = 0) :
    protoFragment .allowRawIntrinsicNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr) =
      .some (miriCopyWithRef ptrBytes countBits elemSize elemAlign srcAddr dstAddr) := by
  have hz' : Nat.mul countBits elemSize = 0 := hz
  rw [protoFragment_zero _ _ _ _ _ _ hz]
  unfold miriCopyWithRef
  rw [hz', ble_true_of_le (Nat.zero_le _)]
  unfold exactView
  cases Nat.beq (Nat.mod srcAddr elemAlign) 0 <;> cases Nat.beq (Nat.mod dstAddr elemAlign) 0 <;>
    rfl

/-- **Equivalence 2** (`.allowRawIntrinsicNull` ≡ Rust 1.98
`core::ptr::copy_nonoverlapping`, i.e. `ub_checks` with the zero-size null
waiver, followed by the intrinsic) on the resolved zero-byte fragment. -/
theorem protoFragment_allowRaw_eq_corePtr
    (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat)
    (hz : countBits * elemSize = 0) :
    protoFragment .allowRawIntrinsicNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr) =
      .some (corePtrCopyRef true ptrBytes countBits elemSize elemAlign srcAddr dstAddr) := by
  have hzs : Bool.or (Nat.beq countBits 0) (Nat.beq elemSize 0) = true := by
    cases countBits with
    | zero => rfl
    | succ c =>
      cases elemSize with
      | zero => cases Nat.beq (c + 1) 0 <;> rfl
      | succ e => exact absurd hz (Nat.mul_ne_zero (Nat.succ_ne_zero c) (Nat.succ_ne_zero e))
  have hz' : Nat.mul countBits elemSize = 0 := hz
  rw [protoFragment_allowRaw_eq_miri _ _ _ _ _ _ hz]
  unfold corePtrCopyRef ubChecksAlignedAndNotNull miriCopyWithRef
  rw [hzs, hz', ble_true_of_le (Nat.zero_le _)]
  cases Nat.beq (Nat.mod srcAddr elemAlign) 0 <;> cases Nat.beq (Nat.mod dstAddr elemAlign) 0 <;>
    rfl

/-- **Equivalence 3** (`.rejectNull` ≡ strict `core::ptr::copy_nonoverlapping`
contract, `ub_checks` without the zero-size null waiver, followed by the
intrinsic) on the resolved zero-byte fragment, including null rejection for
`u8` / `()` (`elemAlign = 1`). -/
theorem protoFragment_rejectNull_eq_corePtrStrict
    (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat)
    (hz : countBits * elemSize = 0) :
    protoFragment .rejectNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr) =
      .some (corePtrCopyRef false ptrBytes countBits elemSize elemAlign srcAddr dstAddr) := by
  have hz' : Nat.mul countBits elemSize = 0 := hz
  rw [protoFragment_zero _ _ _ _ _ _ hz]
  unfold corePtrCopyRef ubChecksAlignedAndNotNull miriCopyWithRef exactView ZeroPtrView.decide
  rw [hz', ble_true_of_le (Nat.zero_le _)]
  dsimp only
  cases isNullAddr ptrBytes srcAddr <;> cases isNullAddr ptrBytes dstAddr <;>
    cases Nat.beq (Nat.mod srcAddr elemAlign) 0 <;> cases Nat.beq (Nat.mod dstAddr elemAlign) 0 <;>
    cases Bool.or (Nat.beq countBits 0) (Nat.beq elemSize 0) <;> rfl

/-- **Overflow agreement**: when `count * elemSize > isize::MAX`, the prototype
and `lean-miri` both report `.ub` (for every view / address). -/
theorem protoFragment_overflow_eq_miri
    (policy : ZeroCountNullPolicy)
    (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat) (srcV dstV : ZeroPtrView)
    (hov : isizeMaxBytes ptrBytes < countBits * elemSize) :
    protoFragment policy ptrBytes countBits elemSize srcV dstV = .some .ub ∧
      miriCopyWithRef ptrBytes countBits elemSize elemAlign srcAddr dstAddr = .ub := by
  have hb : Nat.ble (Nat.mul countBits elemSize) (isizeMaxBytes ptrBytes) = false :=
    ble_false_of_lt hov
  unfold protoFragment miriCopyWithRef
  rw [hb]
  exact ⟨rfl, rfl⟩

/-- **Sole difference** between the two policies on the resolved zero-byte
fragment: an address `≡ 0`, where `.rejectNull` reports `.ub` and
`lean-miri` / Rust 1.98 accept. -/
theorem protoFragment_policy_difference
    (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat)
    (hz : countBits * elemSize = 0)
    (hne : protoFragment .rejectNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr) ≠
      protoFragment .allowRawIntrinsicNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr)) :
    protoFragment .rejectNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr) = .some .ub ∧
      (isNullAddr ptrBytes srcAddr = true ∨ isNullAddr ptrBytes dstAddr = true) := by
  revert hne
  rw [protoFragment_zero _ _ _ _ _ _ hz, protoFragment_zero _ _ _ _ _ _ hz]
  unfold exactView
  cases hs : isNullAddr ptrBytes srcAddr <;> cases hd : isNullAddr ptrBytes dstAddr <;>
    cases Nat.beq (Nat.mod srcAddr elemAlign) 0 <;> cases Nat.beq (Nat.mod dstAddr elemAlign) 0 <;>
    simp [ZeroPtrView.decide, hs, hd, ZeroCheck.andThen]

end Anneal.Proto.ZeroCountCopyAlign
