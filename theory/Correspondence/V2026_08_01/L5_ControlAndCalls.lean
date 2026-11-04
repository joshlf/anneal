import Trusted.Rustc.V2026_08_01.MirSemantics.Statements
import Trusted.Rustc.V2026_08_01.MirSemantics.Terminators
import MiniRust.LibSpecr
import MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops
import Correspondence.Framework
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses

namespace Correspondence.V2026_08_01.L5_ControlAndCalls

open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics
open MiniRust.LibSpecr
open MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops
open Correspondence

/-!
Horizontal Correspondence Slice L5: Control Flow, Terminators, and Procedure Calls
(`Trusted.Rustc.V2026_08_01.MirSemantics.Statements` and
`Trusted.Rustc.V2026_08_01.MirSemantics.Terminators` vs. mechanically extracted
`MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops`).

Every theorem in this module universally quantifies (`∀`) over real Anneal TCB
machine states, statements, terminators, and call stacks and proves exact
equational correspondence against the mechanically generated MiniRust operational
definitions in `MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops`, including
inline evaluation of `"core::intrinsics::exact_div"` in `evalTerminator`
(`mir_evalTerminator_exact_div_intrinsic_corresponds`).
-/

/-- Project an Anneal `StackFrame`'s program-counter coordinates (`blockIdx` and
`stmtIdx`) into MiniRust's mechanically extracted `MrStackFrame` record
(`spec/lang/machine.md:30-34`). -/
def toMrStackFrame (frame : StackFrame) : MrStackFrame :=
  { blockIdx := frame.blockIdx, stmtIdx := frame.stmtIdx }

/-! ## 1. Statement Program Counter & Local Lifecycle Correspondence -/

/-- Universal correspondence between Anneal's `advanceStmt` helper and MiniRust's
statement program-counter increment `Generated.Ops.mrAdvanceStmtPc`. -/
theorem mir_advanceStmt_corresponds
    (s : MachineState) (locals' : List LocalSlot) (mem' : Memory) :
    (advanceStmt s locals' mem').frame.stmtIdx = mrAdvanceStmtPc s.frame.stmtIdx ∧
    (advanceStmt s locals' mem').frame.blockIdx = s.frame.blockIdx ∧
    (advanceStmt s locals' mem').frame.locals = locals' ∧
    (advanceStmt s locals' mem').memory = mem' ∧
    toMrStackFrame (advanceStmt s locals' mem').frame =
      { toMrStackFrame s.frame with stmtIdx := mrAdvanceStmtPc s.frame.stmtIdx } := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Universal correspondence for no-op and instrumentation statements
(`.nop`, `.coverage`, and `.constEvalCounter`). -/
theorem mir_evalStmt_nop_coverage_constEvalCounter
    (s : MachineState) (span : String) :
    evalStmt s ⟨.nop, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    evalStmt s ⟨.coverage, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    evalStmt s ⟨.constEvalCounter, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    (advanceStmt s s.frame.locals).frame.stmtIdx = mrAdvanceStmtPc s.frame.stmtIdx := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Universal characterization of `StatementKind.placeMention`. -/
theorem mir_evalStmt_placeMention_dead_is_ub
    (s : MachineState) (place : Place) (span : String) :
    (get? s.frame.locals place.local_ = .none →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.fail .ub) ∧
    (get? s.frame.locals place.local_ = .some .dead →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.fail .ub) ∧
    (get? s.frame.locals place.local_ = .some .uninit →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals)) ∧
    (∀ v : Value, get? s.frame.locals place.local_ = .some (.init v) →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; simp [evalStmt, h]
  · intro h; simp [evalStmt, h]
  · intro h; simp [evalStmt, h]
  · intro v h; simp [evalStmt, h]

/-- Universal characterization of `StatementKind.storageLive`,
`StatementKind.storageDead`, and protected-tag write conflict checking in `evalStmt`. -/
theorem mir_evalStmt_storageLive_and_storageDead
    (s : MachineState) (loc : Local) (slot : LocalSlot)
    (localsUninit localsDead : List LocalSlot) (span : String) :
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .uninit = .some localsUninit →
      evalStmt s ⟨.storageLive loc, span⟩ = MirStepNode.step (advanceStmt s localsUninit)) ∧
    (get? s.frame.locals loc = .none →
      evalStmt s ⟨.storageLive loc, span⟩ = MirStepNode.fail .ub) ∧
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .dead = .some localsDead →
      evalStmt s ⟨.storageDead loc, span⟩ = MirStepNode.step (advanceStmt s localsDead)) ∧
    (get? s.frame.locals loc = .none →
      evalStmt s ⟨.storageDead loc, span⟩ = MirStepNode.fail .ub) ∧
    (∀ (rv : Rvalue) (val : Value) (locals₁ locals₂ : List LocalSlot) (mem₁ : Memory)
       (protHead : Nat) (protTail : List Nat),
      evalRvalue s.frame.locals rv s.memory = .ok val locals₁ mem₁ →
      get? locals₁ loc = .some .uninit →
      set? locals₁ loc (.init val) = .some locals₂ →
      mem₁.activeProtectors = protHead :: protTail →
      hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) loc .none .nil = true →
      evalStmt s ⟨.assign ⟨loc, .nil⟩ rv, span⟩ = MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hGet hSet; simp [evalStmt, hGet, hSet]
  · intro hGet; simp [evalStmt, hGet]
  · intro hGet hSet; simp [evalStmt, hGet, hSet]
  · intro hGet; simp [evalStmt, hGet]
  · intro rv val locals₁ locals₂ mem₁ protHead protTail hEval hGet hSet hProt hConflict
    simp [evalStmt, hEval, hGet, hSet, hProt, hConflict]

/-! ## 2. Terminator Dispatch, Unwinding, Call-Stack, and `exact_div` Intrinsic Correspondence -/

/-- Universal proof by structural induction on `branches : List (Nat × BasicBlockIdx)`
that Anneal's `lookupSwitchTarget` is identical to `Generated.Ops.mrLookupSwitchTarget`. -/
theorem mir_lookupSwitchTarget_corresponds
    (val : Nat) (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx) :
    lookupSwitchTarget val branches otherwise =
      mrLookupSwitchTarget val branches otherwise := by
  induction branches with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨branchVal, targetBb⟩
    cases h : Nat.beq val branchVal <;>
      simp [lookupSwitchTarget, mrLookupSwitchTarget, h, ih]

/-- Reflexivity of `listByteEq` over arbitrary byte sequences. -/
theorem listByteEq_refl (xs : List UInt8) : listByteEq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp [listByteEq, Nat.beq_refl, ih]

/-- Reflexivity of `stringEq` over arbitrary `String` values. -/
theorem stringEq_refl (s : String) : stringEq s s = true :=
  listByteEq_refl s.toByteArray.data.toList

/-- Universal proof by induction on `callees : List CapturedMir` that Anneal's
`findCallee?` corresponds to `Generated.Ops.mrFindCalleeById`. -/
theorem mir_findCallee_corresponds
    (callees : List CapturedMir) (defPath : String) :
    findCallee? callees defPath =
      callees.find? (fun body => stringEq body.defPath defPath) ∧
    (∀ (body : CapturedMir) (rest : List CapturedMir),
      body.defPath = defPath →
      findCallee? (body :: rest) defPath = .some body) ∧
    (∀ (body : CapturedMir) (rest : List (String × CapturedMir)),
      body.defPath = defPath →
      mrFindCalleeById ((body.defPath, body) :: rest) defPath = .some body) ∧
    (∀ (body : CapturedMir) (rest : List CapturedMir),
      stringEq body.defPath defPath = false →
      findCallee? (body :: rest) defPath = findCallee? rest defPath) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · induction callees with
    | nil => rfl
    | cons body rest ih =>
      cases h : stringEq body.defPath defPath <;>
        simp [findCallee?, List.find?, h, ih]
  · intro body rest hEq
    subst hEq
    simp [findCallee?, stringEq_refl]
  · intro body rest hEq
    subst hEq
    simp [mrFindCalleeById]
  · intro body rest hNe
    simp [findCallee?, hNe]

/-- Universal characterization of `applyUnwindAction` across all four `UnwindAction`
constructors, paired with `Generated.Ops.mrApplyUnwindAction`. -/
theorem mir_applyUnwindAction_characterization
    (s : MachineState) (localsAfter : List LocalSlot) (memAfter : Memory)
    (bb : BasicBlockIdx) :
    (applyUnwindAction s localsAfter memAfter .unreachable = .faulted .ub ∧
      mrApplyUnwindAction none false true = .faultUb) ∧
    (applyUnwindAction s localsAfter memAfter .terminate = .halted .abort ∧
      mrApplyUnwindAction none true false = .abort) ∧
    (applyUnwindAction s localsAfter memAfter .continue_ =
        unwindFromCallStack memAfter.callStack memAfter ∧
      (memAfter.callStack = .nil →
        applyUnwindAction s localsAfter memAfter .continue_ = .halted .panic) ∧
      mrApplyUnwindAction none false false = .panic) ∧
    (applyUnwindAction s localsAfter memAfter (.cleanup bb) =
      .running
        { frame := { s.frame with blockIdx := bb, stmtIdx := 0, locals := localsAfter }
          memory := memAfter } ∧
      mrApplyUnwindAction (some bb) false false = .cleanup bb ∧
      toMrStackFrame { s.frame with blockIdx := bb, stmtIdx := 0, locals := localsAfter } =
        MrStackFrame.jump_to_block (toMrStackFrame s.frame) bb) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, ?_, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  intro hNil
  simp [applyUnwindAction, hNil]

/-- Universal correspondence for `TerminatorKind.goto`. -/
theorem mir_evalTerminator_goto_corresponds
    (s : MachineState) (target : BasicBlockIdx) (span : String)
    (currentBody : Option CapturedMir) :
    evalTerminator s ⟨.goto target, span⟩ currentBody =
      MirStepNode.step { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } } ∧
    toMrStackFrame { s.frame with blockIdx := target, stmtIdx := 0 } =
      MrStackFrame.jump_to_block (toMrStackFrame s.frame) target := by
  exact ⟨rfl, rfl⟩

/-- Universal correspondence for `TerminatorKind.unreachable`. -/
theorem mir_evalTerminator_unreachable_is_ub
    (s : MachineState) (span : String) (currentBody : Option CapturedMir) :
    evalTerminator s ⟨.unreachable, span⟩ currentBody = MirStepNode.fail .ub := by
  rfl

/-- Universal characterization of `TerminatorKind.return_`. -/
theorem mir_evalTerminator_return_root_and_caller
    (s : MachineState) (span : String) (currentBody : Option CapturedMir) :
    (∀ retVal : Value,
      get? s.frame.locals 0 = .some (.init retVal) →
      s.memory.callStack = .nil →
      evalTerminator s ⟨.return_, span⟩ currentBody = MirStepNode.retNormal retVal s.memory) ∧
    (∀ (retVal : Value) (caller : SavedCallerFrame) (restStack : List SavedCallerFrame)
       (updatedCallerLocals : List LocalSlot),
      get? s.frame.locals 0 = .some (.init retVal) →
      s.memory.callStack = caller :: restStack →
      caller.isDiverging = false →
      caller.callerProtector = .none →
      writePlaceValue caller.frame.locals s.memory.borrows caller.destination retVal =
        .ok updatedCallerLocals →
      evalTerminator s ⟨.return_, span⟩ currentBody =
        MirStepNode.step
          { frame :=
              { caller.frame with
                blockIdx := caller.returnTarget
                stmtIdx := 0
                locals := updatedCallerLocals }
            memory :=
              { s.memory with
                callStack := restStack
                activeCallee := .some caller.callerBody
                activeProtectors := caller.calleeProtectors } } ∧
      toMrStackFrame
          { caller.frame with
            blockIdx := caller.returnTarget
            stmtIdx := 0
            locals := updatedCallerLocals } =
        MrStackFrame.jump_to_block (toMrStackFrame caller.frame) caller.returnTarget) ∧
    (∀ (retVal : Value) (caller : SavedCallerFrame) (restStack : List SavedCallerFrame),
      get? s.frame.locals 0 = .some (.init retVal) →
      s.memory.callStack = caller :: restStack →
      caller.isDiverging = true →
      evalTerminator s ⟨.return_, span⟩ currentBody = MirStepNode.fail .ub) ∧
    (get? s.frame.locals 0 = .some .uninit →
      evalTerminator s ⟨.return_, span⟩ currentBody = MirStepNode.fail .ub) ∧
    (get? s.frame.locals 0 = .some .dead →
      evalTerminator s ⟨.return_, span⟩ currentBody = MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro retVal hRet hStack
    simp [evalTerminator, hRet, hStack]
  · intro retVal caller restStack updatedCallerLocals hRet hStack hDiv hProt hWrite
    refine ⟨?_, rfl⟩
    simp [evalTerminator, hRet, hStack, hDiv, hProt, hWrite]
  · intro retVal caller restStack hRet hStack hDiv
    simp [evalTerminator, hRet, hStack, hDiv]
  · intro hUninit
    simp [evalTerminator, hUninit]
  · intro hDead
    simp [evalTerminator, hDead]

/-- Universal characterization of `TerminatorKind.assert`. -/
theorem mir_evalTerminator_assert_corresponds
    (s : MachineState) (cond : Operand) (expected : Bool)
    (target : BasicBlockIdx) (unwind : UnwindAction) (span : String)
    (currentBody : Option CapturedMir)
    (sc : ScalarInt) (locals' : List LocalSlot)
    (hEval :
      evalOperand
        s.frame.locals
        cond
        s.memory.borrows
        s.memory.globals
        (match currentBody with | .some b => b.layouts | .none => emptyLayoutTable)
        s.memory.callerLocals = .ok (.scalar sc) locals') :
    let expectedBit := match expected with | true => 1 | false => 0
    (Nat.beq sc.bits expectedBit = true →
      evalTerminator s ⟨.assert cond expected target unwind, span⟩ currentBody =
        MirStepNode.step
          { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } } ∧
      toMrStackFrame { blockIdx := target, stmtIdx := 0, locals := locals' } =
        MrStackFrame.jump_to_block (toMrStackFrame s.frame) target) ∧
    (Nat.beq sc.bits expectedBit = false →
      evalTerminator s ⟨.assert cond expected target unwind, span⟩ currentBody =
        match applyUnwindAction s locals' s.memory unwind with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro hMatch
    refine ⟨?_, rfl⟩
    cases expected <;> cases currentBody <;>
      simp only [evalTerminator] at hEval ⊢ <;>
      simp [hEval, hMatch]
  · intro hMismatch
    cases expected <;> cases currentBody <;>
      simp only [evalTerminator] at hEval ⊢ <;>
      simp [hEval, hMismatch] <;>
      cases applyUnwindAction s locals' s.memory unwind <;> rfl

/-- Universal characterization of `TerminatorKind.call` for transparent callees and
`"core::hint::unreachable_unchecked"` / `"core::intrinsics::unreachable"`. -/
theorem mir_evalTerminator_call_transparent_and_unreachable_unchecked
    (s : MachineState) (func : Operand) (argOps : List Operand)
    (destination : Place) (unwind : UnwindAction) (span : String)
    (currentBody : Option CapturedMir) :
    (extractCalleeDefPath? func = .some "core::hint::unreachable_unchecked" →
      findCallee? s.memory.callees "core::hint::unreachable_unchecked" = .none →
      evalTerminator s ⟨.call func .nil destination .none unwind, span⟩ currentBody =
        MirStepNode.fail .ub) ∧
    (extractCalleeDefPath? func = .some "core::intrinsics::unreachable" →
      findCallee? s.memory.callees "core::intrinsics::unreachable" = .none →
      evalTerminator s ⟨.call func .nil destination .none unwind, span⟩ currentBody =
        MirStepNode.fail .ub) ∧
    (∀ (defPath : DefPath) (targetBb : BasicBlockIdx)
       (calleeBody callerBody : CapturedMir)
       (argVals : List Value) (locals' : List LocalSlot),
      extractCalleeDefPath? func = .some defPath →
      currentBody = .some callerBody →
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals' →
      findCallee? s.memory.callees defPath = .some calleeBody →
      let savedCaller : SavedCallerFrame :=
        { callerBody := callerBody
          frame := { s.frame with locals := locals' }
          destination := destination
          returnTarget := targetBb
          calleeProtectors := s.memory.activeProtectors
          returnUnwind := unwind
          isDiverging := false }
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ currentBody =
        MirStepNode.step
          { frame :=
              { blockIdx := 0
                stmtIdx := 0
                locals := initLocals calleeBody argVals }
            memory :=
              { s.memory with
                callStack := savedCaller :: s.memory.callStack
                activeCallee := .some calleeBody } }) := by
  have hUnreach1 : isUnreachableCallTarget "core::hint::unreachable_unchecked" = true := by decide
  have hUnreach2 : isUnreachableCallTarget "core::intrinsics::unreachable" = true := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro hUnreach hFind
    simp only [evalTerminator, resolveCallTarget, hUnreach, evalOperands, hFind, hUnreach1]
  · intro hUnreach hFind
    simp only [evalTerminator, resolveCallTarget, hUnreach, evalOperands, hFind, hUnreach2]
  · intro defPath targetBb calleeBody callerBody argVals locals' hFunc hCurr hArgs hFind
    dsimp only
    subst hCurr
    simp [evalTerminator, hFunc, hArgs, hFind]

/--
**Theorem L5.11 (`mir_evalTerminator_exact_div_intrinsic_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for inline
`"core::intrinsics::exact_div"` intrinsic call dispatch in
`Trusted.Rustc.V2026_08_01.MirSemantics.evalTerminator`, for every pair of
scalar arguments `lhs rhs : ScalarInt` at locals `1` and `2` of an otherwise
empty machine state and every target basic block `targetBb`:
1. Unsigned (`typeArgs = [u32]`): when
   `evalExactDiv lhs rhs locals emptyMemory false` returns
   `.ok retVal locals emptyMemory`, `evalTerminator` writes `retVal` to local `0`
   and steps to `targetBb` with `stmtIdx := 0`; when it returns `.ub` (zero
   divisor, non-zero remainder, or zero-width or mismatched-width operands),
   `evalTerminator` faults with `MirStepNode.fail .ub`;
2. Signed (`typeArgs = [i32]`): the same two clauses hold with
   `isSigned = true`, where `evalExactDiv` also faults on `MIN / -1`;
3. Untyped (`typeArgs = []`, no operand types): the signedness of `T` is
   unknown, so `evalTerminator` steps to `MirStepNode.unsupported` instead of
   assuming an unsigned division.
-/
theorem mir_evalTerminator_exact_div_intrinsic_corresponds
    (lhs rhs : ScalarInt) (targetBb : BasicBlockIdx) (unwind : UnwindAction) (span : String) :
    let uFnTy : Ty := { kind := .fnDef "core::intrinsics::exact_div" [.uint .u32], layoutIdx := 0 }
    let uFuncOp : Operand := .constant { ty := uFnTy, val := .zeroSized }
    let untypedFnTy : Ty := { kind := .fnDef "core::intrinsics::exact_div" .nil, layoutIdx := 0 }
    let untypedFuncOp : Operand := .constant { ty := untypedFnTy, val := .zeroSized }
    let sFnTy : Ty := { kind := .fnDef "core::intrinsics::exact_div" [.int .i32], layoutIdx := 0 }
    let sFuncOp : Operand := .constant { ty := sFnTy, val := .zeroSized }
    let argOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init (.scalar lhs), .init (.scalar rhs)]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    (∀ retVal : Value,
      evalExactDiv lhs rhs locals emptyMemory false = .ok retVal locals emptyMemory →
      evalTerminator s ⟨.call uFuncOp argOps dest (.some targetBb) unwind, span⟩ .none =
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init retVal, .init (.scalar lhs), .init (.scalar rhs)]
          }
          memory := emptyMemory
        }) ∧
    (evalExactDiv lhs rhs locals emptyMemory false = .ub →
      evalTerminator s ⟨.call uFuncOp argOps dest (.some targetBb) unwind, span⟩ .none =
        MirStepNode.fail .ub) ∧
    (∀ retVal : Value,
      evalExactDiv lhs rhs locals emptyMemory true = .ok retVal locals emptyMemory →
      evalTerminator s ⟨.call sFuncOp argOps dest (.some targetBb) unwind, span⟩ .none =
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init retVal, .init (.scalar lhs), .init (.scalar rhs)]
          }
          memory := emptyMemory
        }) ∧
    (evalExactDiv lhs rhs locals emptyMemory true = .ub →
      evalTerminator s ⟨.call sFuncOp argOps dest (.some targetBb) unwind, span⟩ .none =
        MirStepNode.fail .ub) ∧
    evalTerminator s ⟨.call untypedFuncOp argOps dest (.some targetBb) unwind, span⟩ .none =
      MirStepNode.unsupported := by
  dsimp only
  have hStr : stringEq "core::intrinsics::exact_div" "core::intrinsics::exact_div" = true := by
    decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro retVal hExact
    unfold emptyMemory at hExact
    unfold evalTerminator
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, hStr,
      hExact, writePlaceValue, set?]
  · intro hUb
    unfold emptyMemory at hUb
    unfold evalTerminator
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, hStr, hUb]
  · intro retVal hExact
    unfold emptyMemory at hExact
    unfold evalTerminator
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, hStr,
      hExact, writePlaceValue, set?]
  · intro hUb
    unfold emptyMemory at hUb
    unfold evalTerminator
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, hStr, hUb]
  · unfold evalTerminator
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, hStr, resolveIntrinsicIsSigned,
      operandTy, placeTy]

/-- Universal correspondence of `TerminatorKind.switchInt`. -/
theorem evalTerminator_switchInt_agrees_with_generated
    (s : MachineState) (discr : Operand) (targets : SwitchTargets)
    (span : String) (currentBody : Option CapturedMir) :
    let bodyLayouts := match currentBody with | .some b => b.layouts | .none => emptyLayoutTable
    (∀ (sc : ScalarInt) (locals' : List LocalSlot),
      evalOperand s.frame.locals discr s.memory.borrows s.memory.globals bodyLayouts s.memory.callerLocals =
        .ok (.scalar sc) locals' →
      let target := mrLookupSwitchTarget sc.bits targets.branches targets.otherwise
      evalTerminator s ⟨.switchInt discr targets, span⟩ currentBody =
        MirStepNode.emitStep (.event sc.bits)
          { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } } ∧
      toMrStackFrame { blockIdx := target, stmtIdx := 0, locals := locals' } =
        MrStackFrame.jump_to_block (toMrStackFrame s.frame) target) ∧
    (evalOperand s.frame.locals discr s.memory.borrows s.memory.globals bodyLayouts s.memory.callerLocals = .ub →
      evalTerminator s ⟨.switchInt discr targets, span⟩ currentBody = MirStepNode.fail .ub) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro sc locals' hEval
    refine ⟨?_, rfl⟩
    rw [← mir_lookupSwitchTarget_corresponds sc.bits targets.branches targets.otherwise]
    cases currentBody <;>
      simp only [evalTerminator] at hEval ⊢ <;>
      simp [hEval]
  · intro hUb
    cases currentBody <;>
      simp only [evalTerminator] at hUb ⊢ <;>
      simp [hUb]

/-! ## 3. Function-Item Reification (`ReifyFnPointer`), `fnPtrToPtr`, and Indirect `FnPtr` Calls (`BRIEF-1.1`) -/

/--
Universal characterization of `CastKind.pointerCoercion "ReifyFnPointer"`,
`CastKind.fnPtrToPtr`, `CastKind.ptrToPtr`, and `CastKind.pointerExposeProvenance`
in `evalRvalue`:
1. Reifying a zero-sized `.fnDef defPath typeArgs` constant operand into a
   `.fnPtr sigInputs sigOut sigSafety sigAbi` target type allocates the canonical
   function-pointer entry `{ allocId := fnPtrAllocBase, defPath, typeArgs, fnSig }`
   in `emptyMemory.fnPtrs` and returns
   `.ptr { allocId := fnPtrAllocBase, offsetBytes := 0 } 8`.
2. Explicit safety-tagged coercions (`"ReifyFnPointer(Safe)"` and
   `"ReifyFnPointer(Unsafe)"`) succeed when the target `fnPtr` safety matches
   and fault with `.ub` on a safety mismatch or `.rustIntrinsic` ABI.
3. Casting a registered function pointer via `CastKind.fnPtrToPtr` to a thin raw
   pointer, then via `CastKind.ptrToPtr`, and then exposing its address via
   `CastKind.pointerExposeProvenance` yields the deterministic exposed scalar
   address `allocId * 65536`.
4. Applying `CastKind.fnPtrToPtr` to an unregistered pointer faults with
   `EvalResult.ub`.
-/
theorem mir_evalRvalue_reifyFnPointer_and_fnPtrToPtr_chain
    (locals : List LocalSlot)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (sigInputs : List RigidTy)
    (sigOut : RigidTy)
    (sigSafety : Safety)
    (sigAbi : CallConv)
    (hNotIntrinsic : callConvEq sigAbi .rustIntrinsic = false) :
    let fnItemTy : Ty := { kind := .fnDef defPath typeArgs, layoutIdx := 0 }
    let fnPtrKind : RigidTy := .fnPtr sigInputs sigOut sigSafety sigAbi
    let fnPtrTy : Ty := { kind := fnPtrKind, layoutIdx := 0 }
    let safeFnPtrKind : RigidTy := .fnPtr sigInputs sigOut .safe sigAbi
    let safeFnPtrTy : Ty := { kind := safeFnPtrKind, layoutIdx := 0 }
    let unsafeFnPtrKind : RigidTy := .fnPtr sigInputs sigOut .unsafe_ sigAbi
    let unsafeFnPtrTy : Ty := { kind := unsafeFnPtrKind, layoutIdx := 0 }
    let intrinsicFnPtrTy : Ty :=
      { kind := .fnPtr sigInputs sigOut sigSafety .rustIntrinsic, layoutIdx := 0 }
    let rawConstUnitTy : Ty := { kind := .rawPtr .not (.tuple .nil), layoutIdx := 0 }
    let rawMutUnitTy : Ty := { kind := .rawPtr .mut (.tuple .nil), layoutIdx := 0 }
    let usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
    let fnConstOp : Operand := .constant { ty := fnItemTy, val := .zeroSized }
    let expectedEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := defPath
        typeArgs := typeArgs
        fnSig := .some fnPtrKind }
    let expectedSafeEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := defPath
        typeArgs := typeArgs
        fnSig := .some safeFnPtrKind }
    let expectedPtr : ProvenancePtr := { allocId := fnPtrAllocBase, offsetBytes := 0 }
    let memAfterReify : Memory := { emptyMemory with fnPtrs := [expectedEntry] }
    let memAfterSafeReify : Memory := { emptyMemory with fnPtrs := [expectedSafeEntry] }
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer") fnConstOp fnPtrTy)
        emptyMemory =
      .ok (.ptr expectedPtr 8) locals memAfterReify) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer(Safe)") fnConstOp safeFnPtrTy)
        emptyMemory =
      .ok (.ptr expectedPtr 8) locals memAfterSafeReify) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer(Safe)") fnConstOp unsafeFnPtrTy)
        emptyMemory =
      .ub) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer(Unsafe)") fnConstOp safeFnPtrTy)
        emptyMemory =
      .ub) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer") fnConstOp intrinsicFnPtrTy)
        emptyMemory =
      .ub) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast .fnPtrToPtr (.copy ⟨0, .nil⟩) rawConstUnitTy)
        memAfterReify =
      .ok (.ptr expectedPtr 8) [.init (.ptr expectedPtr 8)] memAfterReify) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast .ptrToPtr (.copy ⟨0, .nil⟩) rawMutUnitTy)
        memAfterReify =
      .ok (.ptr expectedPtr 8) [.init (.ptr expectedPtr 8)] memAfterReify) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast .pointerExposeProvenance (.copy ⟨0, .nil⟩) usizeTy)
        memAfterReify =
      .ok
        (.scalar { bits := fnPtrAllocBase * 65536, sizeBytes := 8 })
        [.init (.ptr expectedPtr 8)]
        memAfterReify) ∧
    (evalRvalue
        [.init (.ptr { allocId := 0, offsetBytes := 0 } 8)]
        (.cast .fnPtrToPtr (.copy ⟨0, .nil⟩) rawConstUnitTy)
        emptyMemory =
      .ub) := by
  have hReify1 : isReifyFnPointerCoercion "ReifyFnPointer" = true := by decide
  have hReify2 : isReifyFnPointerCoercion "ReifyFnPointer(Safe)" = true := by decide
  have hReify3 : isReifyFnPointerCoercion "ReifyFnPointer(Unsafe)" = true := by decide
  have hNeUnsafe1 : stringEq "ReifyFnPointer" "UnsafeFnPointer" = false := by decide
  have hNeUnsafe2 : stringEq "ReifyFnPointer(Safe)" "UnsafeFnPointer" = false := by decide
  have hNeUnsafe3 : stringEq "ReifyFnPointer(Unsafe)" "UnsafeFnPointer" = false := by decide
  have hSafeCompat1 :
      reifyCoercionSafetyCompatible "ReifyFnPointer" sigSafety = true := by
    cases sigSafety <;> rfl
  have hSafeCompat2 :
      reifyCoercionSafetyCompatible "ReifyFnPointer(Safe)" .safe = true := by decide
  have hSafeCompat3 :
      reifyCoercionSafetyCompatible "ReifyFnPointer(Safe)" .unsafe_ = false := by decide
  have hSafeCompat4 :
      reifyCoercionSafetyCompatible "ReifyFnPointer(Unsafe)" .safe = false := by decide
  have hNotClosure1 : isClosureFnPointerCoercion "ReifyFnPointer" = false := by decide
  have hNotClosure2 : isClosureFnPointerCoercion "ReifyFnPointer(Safe)" = false := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [evalRvalue, evalReifyFnPointer, hReify1, hNeUnsafe1, hNotIntrinsic,
      hSafeCompat1, hNotClosure1, extractReifyCoercionTarget?, extractFnItemTarget?,
      emptyMemory, checkCalleeSig, findFnPtrEntry?, nextFnPtrAllocId, evalOperand, evalConstValue]
  · simp [evalRvalue, evalReifyFnPointer, hReify2, hNeUnsafe2, hNotIntrinsic,
      hSafeCompat2, hNotClosure2, extractReifyCoercionTarget?, extractFnItemTarget?,
      emptyMemory, checkCalleeSig, findFnPtrEntry?, nextFnPtrAllocId, evalOperand, evalConstValue]
  · simp [evalRvalue, evalReifyFnPointer, hReify2, hNeUnsafe2, hNotIntrinsic,
      hSafeCompat3, evalOperand, evalConstValue]
  · simp [evalRvalue, evalReifyFnPointer, hReify3, hNeUnsafe3, hNotIntrinsic,
      hSafeCompat4, evalOperand, evalConstValue]
  · simp [evalRvalue, evalReifyFnPointer, hReify1, hNeUnsafe1,
      evalOperand, evalConstValue]
  · simp [evalRvalue, evalFnPtrToPtr, evalOperand, get?, readProjectedValue,
      isThinRawPtrTy, emptyMemory, lookupBorrow, lookupFnPtr, hNotIntrinsic]
  · simp [evalRvalue, evalOperand, get?, readProjectedValue]
  · simp [evalRvalue, evalOperand, get?, readProjectedValue]
  · simp [evalRvalue, evalFnPtrToPtr, evalOperand, get?, readProjectedValue,
      isThinRawPtrTy, emptyMemory, lookupBorrow, isFnPtrAllocId, fnPtrAllocBase]

/--
Universal characterization of `checkCalleeSig`, `PointerCoercion::ClosureFnPointer`,
`PointerCoercion::UnsafeFnPointer`, and `safetyCompatible` in `evalRvalue` and
`fnEntryCompatibleWithCallSite`:
1. Reifying a function item when `checkCalleeSig mem.callees defPath sigInputs sigOut sigAbi = false`
   faults with `RvalueEvalResult.ub`.
2. Applying `"ClosureFnPointer(Safe)"` to a non-capturing closure
   (`.closure defPath .nil`) succeeds, while applying `"ClosureFnPointer(Safe)"`
   to a `.fnDef` or `"ReifyFnPointer"` to a `.closure` faults with `.ub`.
3. Applying `CastKind.pointerCoercion "UnsafeFnPointer"` to a registered safe
   function pointer (`Safety.safe`) produces the same `ProvenancePtr` at the
   matching `Safety.unsafe_` signature, whereas applying `"UnsafeFnPointer"` to
   a `.safe` target signature faults with `RvalueEvalResult.ub`.
4. An `.unsafe_` `FnPtrEntry` is rejected by `fnEntryCompatibleWithCallSite` when
   the call-site operand has `Safety.safe`.
-/
theorem mir_evalRvalue_reifyFnPointer_callee_sig_and_unsafeFnPointer_corresponds
    (locals : List LocalSlot)
    (mem : Memory)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (sigInputs : List RigidTy)
    (sigOut : RigidTy)
    (sigSafety : Safety)
    (sigAbi : CallConv)
    (hNotIntrinsic : callConvEq sigAbi .rustIntrinsic = false) :
    let fnItemTy : Ty := { kind := .fnDef defPath typeArgs, layoutIdx := 0 }
    let fnConstOp : Operand := .constant { ty := fnItemTy, val := .zeroSized }
    let closureTy : Ty := { kind := .closure defPath .nil, layoutIdx := 0 }
    let closureConstOp : Operand := .constant { ty := closureTy, val := .zeroSized }
    let fnPtrTy : Ty := { kind := .fnPtr sigInputs sigOut sigSafety sigAbi, layoutIdx := 0 }
    let safeFnKind : RigidTy := .fnPtr [.uint .u64] (.uint .u64) .safe .rust
    let unsafeFnKind : RigidTy := .fnPtr [.uint .u64] (.uint .u64) .unsafe_ .rust
    let safeFnTy : Ty := { kind := safeFnKind, layoutIdx := 0 }
    let unsafeFnTy : Ty := { kind := unsafeFnKind, layoutIdx := 0 }
    let safeEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := defPath
        typeArgs := .nil
        fnSig := .some safeFnKind }
    let unsafeEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := defPath
        typeArgs := .nil
        fnSig := .some unsafeFnKind }
    let intrinsicEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := defPath
        typeArgs := .nil
        fnSig := .some (.fnPtr [.uint .u64] (.uint .u64) .safe .rustIntrinsic) }
    let rawConstUnitTy : Ty := { kind := .rawPtr .not (.tuple .nil), layoutIdx := 0 }
    let expectedPtr : ProvenancePtr := { allocId := fnPtrAllocBase, offsetBytes := 0 }
    let memWithSafe : Memory := { emptyMemory with fnPtrs := [safeEntry] }
    let memWithIntrinsic : Memory := { emptyMemory with fnPtrs := [intrinsicEntry] }
    (checkCalleeSig mem.callees defPath sigInputs sigOut sigAbi = false →
      evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer") fnConstOp fnPtrTy)
        mem = .ub) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ClosureFnPointer(Safe)") closureConstOp safeFnTy)
        emptyMemory =
      .ok (.ptr expectedPtr 8) locals memWithSafe) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ClosureFnPointer(Safe)") fnConstOp safeFnTy)
        emptyMemory =
      .ub) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer") closureConstOp safeFnTy)
        emptyMemory =
      .ub) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast (.pointerCoercion "UnsafeFnPointer") (.copy ⟨0, .nil⟩) unsafeFnTy)
        memWithSafe =
      .ok (.ptr expectedPtr 8) [.init (.ptr expectedPtr 8)] memWithSafe) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast (.pointerCoercion "UnsafeFnPointer") (.copy ⟨0, .nil⟩) safeFnTy)
        memWithSafe =
      .ub) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast .fnPtrToPtr (.copy ⟨0, .nil⟩) rawConstUnitTy)
        memWithIntrinsic =
      .ub) ∧
    (fnEntryCompatibleWithCallSite unsafeEntry 1 (.some safeFnTy) = false) := by
  have hReify : isReifyFnPointerCoercion "ReifyFnPointer" = true := by decide
  have hClosureSafe : isReifyFnPointerCoercion "ClosureFnPointer(Safe)" = true := by decide
  have hReifyUnsafe : isReifyFnPointerCoercion "UnsafeFnPointer" = true := by decide
  have hEqUnsafe : stringEq "UnsafeFnPointer" "UnsafeFnPointer" = true := by decide
  have hNeUnsafeClosure : stringEq "ClosureFnPointer(Safe)" "UnsafeFnPointer" = false := by decide
  have hSafeCompat :
      reifyCoercionSafetyCompatible "ReifyFnPointer" sigSafety = true := by
    cases sigSafety <;> rfl
  have hSafeCompatClosure :
      reifyCoercionSafetyCompatible "ClosureFnPointer(Safe)" .safe = true := by decide
  have hNotClosure : isClosureFnPointerCoercion "ReifyFnPointer" = false := by decide
  have hIsClosureSafe : isClosureFnPointerCoercion "ClosureFnPointer(Safe)" = true := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hSigFalse
    have hNeUnsafe : stringEq "ReifyFnPointer" "UnsafeFnPointer" = false := by decide
    simp [evalRvalue, evalReifyFnPointer, hReify, hNeUnsafe, hNotIntrinsic,
      hSafeCompat, hNotClosure, extractReifyCoercionTarget?, extractFnItemTarget?,
      hSigFalse, evalOperand, evalConstValue]
  · simp [evalRvalue, evalReifyFnPointer, hClosureSafe, hNeUnsafeClosure,
      hSafeCompatClosure, hIsClosureSafe, extractReifyCoercionTarget?,
      emptyMemory, checkCalleeSig, findFnPtrEntry?, nextFnPtrAllocId,
      evalOperand, evalConstValue, callConvEq]
  · simp [evalRvalue, evalReifyFnPointer, hClosureSafe, hNeUnsafeClosure,
      hSafeCompatClosure, hIsClosureSafe, extractReifyCoercionTarget?,
      evalOperand, evalConstValue, callConvEq]
  · have hNeUnsafe : stringEq "ReifyFnPointer" "UnsafeFnPointer" = false := by decide
    have hSafeCompatReifySafe :
        reifyCoercionSafetyCompatible "ReifyFnPointer" .safe = true := by decide
    simp [evalRvalue, evalReifyFnPointer, hReify, hNeUnsafe,
      hSafeCompatReifySafe, hNotClosure, extractReifyCoercionTarget?, extractFnItemTarget?,
      evalOperand, evalConstValue, callConvEq]
  · simp [evalRvalue, evalReifyFnPointer, hReifyUnsafe, hEqUnsafe, evalUnsafeFnPointer,
      evalOperand, get?, readProjectedValue, emptyMemory, lookupBorrow,
      lookupFnPtr, callConvEq, rigidTyListEq, rigidTyEq,
      rigidTyListEqAux, rigidTyEqAux, uintTyEq]
  · simp [evalRvalue, evalReifyFnPointer, hReifyUnsafe, hEqUnsafe, evalUnsafeFnPointer,
      evalOperand, get?, readProjectedValue]
  · simp [evalRvalue, evalFnPtrToPtr, evalOperand, get?, readProjectedValue,
      isThinRawPtrTy, emptyMemory, lookupBorrow, lookupFnPtr, callConvEq]
  · rfl

/--
Universal proof that dereferencing a reified function pointer (`PlaceElem.deref`)
as data memory in `evalOperand` or `writePlaceValue` faults with `.ub` when
`ptrVal.allocId` is not backed by a global allocation in `s.memory.globals`
(and not a live stack borrow in `s.memory.borrows`).
-/
theorem mir_fnPtr_data_deref_is_ub
    (ptrVal : ProvenancePtr)
    (mem : Memory)
    (writeVal : Value)
    (hNoBorrow : lookupBorrow mem.borrows ptrVal.tag = .none)
    (hNoGlobal : lookupGlobalAlloc mem.globals ptrVal.allocId = .none) :
    let locals : List LocalSlot := [.init (.ptr ptrVal 8)]
    let derefPlace : Place := { local_ := 0, projection := [.deref] }
    evalOperand locals (.copy derefPlace) mem.borrows mem.globals emptyLayoutTable mem.callerLocals = .ub ∧
    writePlaceValue locals mem.borrows derefPlace writeVal = .ub := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simp [evalOperand, get?, hNoBorrow, hNoGlobal]
  · simp [writePlaceValue, get?, hNoBorrow]

/--
Universal characterization of indirect `TerminatorKind.call` and
`TerminatorKind.tailCall` through a function pointer (`BRIEF-1.1`):
1. When `func` evaluates to `.ptr ptrVal 8` with `ptrVal.offsetBytes = 0`, no stack
   borrow on `ptrVal.tag`, and `lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry`
   compatible with the call site (`fnEntryCompatibleWithCallSite = true`):
   - If `findCallee? s.memory.callees fnEntry.defPath = .some calleeBody` and
     `checkCalleeTargetCompatible` holds, `TerminatorKind.call` pushes a
     `SavedCallerFrame` and enters `calleeBody` at block `0` via `pushCalleeFrame`,
     and `TerminatorKind.tailCall` enters `calleeBody` at block `0` via
     `enterTailCalleeFrame`.
   - If `findCallee? s.memory.callees fnEntry.defPath = .none`, `TerminatorKind.call`
     and `TerminatorKind.tailCall` emit `MirStepNode.extCall` targeting
     `fnEntry.defPath`.
2. When `func` evaluates to an unregistered pointer (`lookupFnPtr = .none`), a
   non-zero offset pointer, a stack borrow data pointer, a scalar, or a function
   pointer with incompatible signature/arity, both `TerminatorKind.call` and
   `TerminatorKind.tailCall` fault with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_indirect_call_and_tailCall_corresponds
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (callerBody calleeBody : CapturedMir)
    (ptrVal : ProvenancePtr)
    (fnEntry : FnPtrEntry)
    (localsAfterFunc locals' : List Value → List LocalSlot)
    (argVals : List Value)
    (hNoDirect : extractCalleeDefPath? func = .none)
    (hEvalFunc :
      evalOperand
        s.frame.locals
        func
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok (.ptr ptrVal 8) (localsAfterFunc argVals))
    (hOffsetZero : ptrVal.offsetBytes = 0)
    (hNoBorrow : lookupBorrow s.memory.borrows ptrVal.tag = .none) :
    let callerFuncTyOpt := operandTy callerBody.localDecls callerBody.layouts func
    let resolvedTarget : ResolvedCallTarget :=
      { defPath := fnEntry.defPath
        typeArgs := fnEntry.typeArgs
        fnSig := fnEntry.fnSig
        isIndirect := true }
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps) callerFuncTyOpt = true →
      evalOperands
        (localsAfterFunc argVals)
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals (locals' argVals) →
      findCallee? s.memory.callees fnEntry.defPath = .some calleeBody →
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.step
          (pushCalleeFrame s callerBody (locals' argVals) destination targetBb calleeBody argVals unwind) ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.step
          (pushDivergingCalleeFrame s callerBody (locals' argVals) destination unwind calleeBody argVals) ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.step (enterTailCalleeFrame s.memory calleeBody argVals)) ∧
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps) callerFuncTyOpt = true →
      evalOperands
        (localsAfterFunc argVals)
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals (locals' argVals) →
      findCallee? s.memory.callees fnEntry.defPath = .none →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := fnEntry.defPath, args := argVals, memory := s.memory }
          (resumeExternalCall s (locals' argVals) destination targetBb unwind) ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := fnEntry.defPath, args := argVals, memory := s.memory }
          (resumeExternalDivergingCall s (locals' argVals) unwind) ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := fnEntry.defPath, args := argVals, memory := s.memory }
          resumeExternalTailCall) ∧
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .none →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps) callerFuncTyOpt = false →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps) callerFuncTyOpt = true →
      evalOperands
        (localsAfterFunc argVals)
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals (locals' argVals) →
      findCallee? s.memory.callees fnEntry.defPath = .some calleeBody →
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = false →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hLookup hCompatSite hArgs hFind hCompatBody
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, bodyLocalDeclsOf, resolveCallTarget,
        hNoDirect, hEvalFunc, hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFind,
        hCompatBody, Nat.beq_refl, Bool.and_self]
  · intro hLookup hCompatSite hArgs hFindNone
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, bodyLocalDeclsOf, isDirectExactDivTarget, resolveCallTarget,
        hNoDirect, hEvalFunc, hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFindNone,
        Nat.beq_refl, Bool.and_self]
  · intro hLookupNone
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookupNone, Nat.beq_refl, Bool.and_self]
  · intro hLookup hCompatFalse
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, bodyLocalDeclsOf, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookup, hCompatFalse, Nat.beq_refl, Bool.and_self]
  · intro hLookup hCompatSite hArgs hFind hCompatBodyFalse
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, bodyLocalDeclsOf, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFind, hCompatBodyFalse,
        Nat.beq_refl, Bool.and_self]

/--
Universal proof that indirect `TerminatorKind.call` and `TerminatorKind.tailCall`
fault with `MirStepNode.fail .ub` when the function-pointer operand evaluates to
a pointer with a non-zero byte offset (`ptrVal.offsetBytes = n + 1`) or a
live stack borrow data pointer (`lookupBorrow s.memory.borrows ptrVal.tag = .some bEntry`).
-/
theorem mir_evalTerminator_indirect_call_nonZeroOffset_or_borrow_is_ub
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (callerBody : CapturedMir)
    (ptrVal : ProvenancePtr)
    (n : Nat)
    (bEntry : BorrowEntry)
    (localsAfterFunc : List LocalSlot)
    (hNoDirect : extractCalleeDefPath? func = .none)
    (hEvalFunc :
      evalOperand
        s.frame.locals
        func
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok (.ptr ptrVal 8) localsAfterFunc) :
    (ptrVal.offsetBytes = n + 1 →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (ptrVal.offsetBytes = 0 →
      lookupBorrow s.memory.borrows ptrVal.tag = .some bEntry →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) := by
  refine ⟨?_, ?_⟩
  · intro hNonZero
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [evalTerminator, resolveCallTarget, hNoDirect, hEvalFunc, hNonZero, Nat.beq]
  · intro hOffsetZero hBorrow
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [evalTerminator, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hBorrow]

/-! ## 4. Diverging Calls (`target = .none`) and Unwind Cleanup Terminators (`BRIEF-1.2`) -/

/--
Universal characterization of diverging `TerminatorKind.call` (`target = .none`)
argument evaluation order, UB propagation, and unreachable call targets
(`"core::hint::unreachable_unchecked"` and `"core::intrinsics::unreachable"`):
1. If resolving `func` via `resolveCallTarget` faults with `.ub`, the diverging
   call faults with `MirStepNode.fail .ub`.
2. If evaluating `argOps` left-to-right via `evalOperands` faults with `.ub`
   (e.g., reading a `.dead` or `.uninit` local), the diverging call faults with
   `MirStepNode.fail .ub` before dispatching the callee or panic entrypoint.
3. For any `argOps` whose left-to-right evaluation succeeds (`.ok argVals locals'`),
   calling `"core::hint::unreachable_unchecked"` or `"core::intrinsics::unreachable"`
   with `target = .none` faults with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_diverging_call_args_and_unreachable
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (span : String)
    (callerBody : CapturedMir) :
    (resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts = .ub →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (∀ (target : ResolvedCallTarget) (localsAfterFunc : List LocalSlot),
      resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
        .ok target localsAfterFunc →
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ub →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (∀ (argVals : List Value) (locals' : List LocalSlot),
      extractCalleeDefPath? func = .some "core::hint::unreachable_unchecked" →
      findCallee? s.memory.callees "core::hint::unreachable_unchecked" = .none →
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals' →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (∀ (argVals : List Value) (locals' : List LocalSlot),
      extractCalleeDefPath? func = .some "core::intrinsics::unreachable" →
      findCallee? s.memory.callees "core::intrinsics::unreachable" = .none →
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals' →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (∀ (target : ResolvedCallTarget) (localsAfterFunc : List LocalSlot)
       (argVals : List Value) (locals' : List LocalSlot),
      resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
        .ok target localsAfterFunc →
      target.isIndirect = true →
      findCallee? s.memory.callees target.defPath = .none →
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals' →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := target.defPath, args := argVals, memory := s.memory }
          (resumeExternalDivergingCall s locals' unwind)) := by
  have hUnreach1 : isUnreachableCallTarget "core::hint::unreachable_unchecked" = true := by decide
  have hUnreach2 : isUnreachableCallTarget "core::intrinsics::unreachable" = true := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hResolveUb
    simp only [evalTerminator, bodyLocalDeclsOf, hResolveUb]
  · intro target localsAfterFunc hResolveOk hArgsUb
    simp only [evalTerminator, bodyLocalDeclsOf, hResolveOk, hArgsUb]
  · intro argVals locals' hFunc hFind hArgsOk
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgsOk, hFind, hUnreach1]
  · intro argVals locals' hFunc hFind hArgsOk
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgsOk, hFind, hUnreach2]
  · intro target localsAfterFunc argVals locals' hResolveOk hIndirect hFind hArgsOk
    simp only [evalTerminator, bodyLocalDeclsOf, hResolveOk, hArgsOk, hFind, hIndirect]

/--
Universal characterization of diverging `TerminatorKind.call` (`target = .none`)
when the target callee is linked in `s.memory.callees`:
1. Calling a linked `calleeBody` (`findCallee? s.memory.callees target.defPath = .some calleeBody`
   with `checkCalleeTargetCompatible = true`)
   pushes a diverging `SavedCallerFrame` (`isDiverging = true`, `returnUnwind = unwind`)
   via `pushDivergingCalleeFrame` and enters `calleeBody` at block `0`.
2. If that diverging `calleeBody` subsequently attempts to return normally via
   `TerminatorKind.return_` from ANY local slot state `calleeLocals` (whether `_0`
   is `.uninit`, `.dead`, `.none`, or `.init retVal`) or via an external
   `TerminatorKind.tailCall` receiving `MirCallAns.returned`, execution faults
   with `MirStepNode.fail .ub` (`.faulted .ub`).
3. If that diverging `calleeBody` unwinds via `TerminatorKind.unwindResume` (or
   `applyUnwindAction ... .continue_`), execution pops the diverging caller frame,
   restores `callerBody` and `restoreCallerProtectors`, and applies the caller's
   `unwind : UnwindAction` (`.cleanup cleanupBb`, `.terminate`, `.unreachable`, or
   `.continue_`).
-/
theorem mir_evalTerminator_diverging_call_linked_callee_corresponds
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (span : String)
    (callerBody calleeBody : CapturedMir)
    (defPath : DefPath)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (hFunc : extractCalleeDefPath? func = .some defPath)
    (hArgs :
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals')
    (hFind : findCallee? s.memory.callees defPath = .some calleeBody) :
    let enteredState :=
      pushDivergingCalleeFrame s callerBody locals' destination unwind calleeBody argVals
    (evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
      MirStepNode.step enteredState) ∧
    (∀ (calleeLocals : List LocalSlot),
      evalTerminator
        { enteredState with frame := { enteredState.frame with locals := calleeLocals } }
        ⟨.return_, span⟩
        (.some calleeBody) = MirStepNode.fail .ub) ∧
    (∀ (retVal : Value),
      resumeExternalTailCall (.returned retVal enteredState.memory) = .faulted .ub) ∧
    (∀ (cleanupBb : BasicBlockIdx),
      unwind = .cleanup cleanupBb →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.step
          { frame :=
              { s.frame with
                blockIdx := cleanupBb
                stmtIdx := 0
                locals := locals' }
            memory :=
              { s.memory with
                callStack := s.memory.callStack
                activeCallee := .some callerBody
                activeProtectors := s.memory.activeProtectors } }) ∧
    (unwind = .terminate →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.retOutcome .abort) ∧
    (unwind = .unreachable →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.fail .ub) ∧
    (unwind = .continue_ →
      s.memory.callStack = .nil →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.retOutcome .panic) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [evalTerminator, resolveCallTarget, hFunc, hArgs, hFind,
      checkCalleeTargetCompatible]
  · intro calleeLocals
    unfold evalTerminator pushDivergingCalleeFrame
    dsimp only
    cases get? calleeLocals 0 with
    | none => rfl
    | some slot0 =>
      cases slot0 <;> rfl
  · intro retVal
    simp [resumeExternalTailCall, pushDivergingCalleeFrame]
  · intro cleanupBb hUnwind
    subst hUnwind
    simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack, restoreCallerProtectors]
  · intro hUnwind
    subst hUnwind
    simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack]
  · intro hUnwind
    subst hUnwind
    simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack]
  · intro hUnwind hRoot
    subst hUnwind
    simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack, hRoot]

/--
Universal characterization of diverging `TerminatorKind.call` (`target = .none`)
for standard panic entrypoints when unlinked (`findCallee? = .none`):
1. Calling any non-unwinding panic/abort entrypoint (`isAbortingPanicDefPath`:
   `"core::panicking::panic_nounwind"`, `"core::panicking::panic_nounwind_fmt"`,
   `"core::panicking::panic_nounwind_fmt::panic_impl"`,
   `"core::panicking::panic_nounwind_nobacktrace"`,
   `"core::panicking::panic_in_cleanup"`, `"core::panicking::panic_cannot_unwind"`,
   `"core::panicking::panic_misaligned_pointer_dereference"`,
   `"core::panicking::panic_null_pointer_dereference"`,
   `"core::panicking::panic_invalid_enum_construction"`, or
   `"core::intrinsics::abort"`) halts immediately with
   `MirStepNode.retOutcome .abort` under any `unwind : UnwindAction`.
2. Calling any standard unwinding panic entrypoint (`isUnwindingPanicDefPath`:
   `"core::panicking::panic"`, `"core::panicking::panic_fmt"`,
   `"core::panicking::panic_fmt::panic_impl"`, `"core::panicking::const_panic_fmt"`,
   `"core::panicking::assert_failed"`, `"core::panicking::assert_failed_inner"`,
   `"core::panicking::assert_matches_failed"`,
   `"core::slice::index::slice_index_fail"`,
   `"core::panicking::panic_bounds_check"`, `"core::panicking::panic_explicit"`,
   `"core::panicking::panic_display"`, `"core::panicking::panic_str_2015"`,
   `"core::panicking::unreachable_display"`, `"core::option::unwrap_failed"`,
   `"core::option::expect_failed"`, `"core::result::unwrap_failed"`, or any
   `"core::panicking::panic_const::*"` arithmetic overflow/zero-division hook)
   evaluates `argOps` to `locals'` and dispatches
   `applyUnwindAction s locals' s.memory unwind`:
   - under `.continue_` at the root frame (`s.memory.callStack = .nil`), halts with
     `MirStepNode.retOutcome .panic`;
   - under `.continue_` in a nested frame (`s.memory.callStack = caller :: restStack`
     with `caller.returnUnwind = .cleanup cleanupBb`), pops `caller` and jumps to
     `cleanupBb` in `caller.frame`;
   - under `.cleanup cleanupBb`, jumps to `cleanupBb` with `stmtIdx = 0` and
     `locals = locals'`;
   - under `.terminate`, halts with `MirStepNode.retOutcome .abort`; and
   - under `.unreachable`, faults with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_diverging_call_panic_entrypoints
    (s : MachineState)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (cleanupBb : BasicBlockIdx)
    (span : String)
    (callerBody : CapturedMir)
    (caller : SavedCallerFrame)
    (restStack : List SavedCallerFrame)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (hArgs :
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals') :
    let mkFnOp (p : DefPath) : Operand :=
      .constant { ty := { kind := .fnDef p .nil, layoutIdx := 0 }, val := .zeroSized }
    (∀ pAbort : DefPath,
      (pAbort = "core::panicking::panic_nounwind" ∨
       pAbort = "core::panicking::panic_nounwind_fmt" ∨
       pAbort = "core::panicking::panic_nounwind_fmt::panic_impl" ∨
       pAbort = "core::panicking::panic_nounwind_nobacktrace" ∨
       pAbort = "core::panicking::panic_in_cleanup" ∨
       pAbort = "core::panicking::panic_cannot_unwind" ∨
       pAbort = "core::panicking::panic_misaligned_pointer_dereference" ∨
       pAbort = "core::panicking::panic_null_pointer_dereference" ∨
       pAbort = "core::panicking::panic_invalid_enum_construction" ∨
       pAbort = "core::intrinsics::abort") →
      findCallee? s.memory.callees pAbort = .none →
      evalTerminator
        s
        ⟨.call (mkFnOp pAbort) argOps destination .none unwind, span⟩
        (.some callerBody) = MirStepNode.retOutcome .abort) ∧
    (∀ p : DefPath,
      (p = "core::panicking::panic" ∨
       p = "core::panicking::panic_fmt" ∨
       p = "core::panicking::panic_fmt::panic_impl" ∨
       p = "core::panicking::const_panic_fmt" ∨
       p = "core::panicking::assert_failed" ∨
       p = "core::panicking::assert_failed_inner" ∨
       p = "core::panicking::assert_matches_failed" ∨
       p = "core::slice::index::slice_index_fail" ∨
       p = "core::panicking::panic_bounds_check" ∨
       p = "core::panicking::panic_explicit" ∨
       p = "core::panicking::panic_display" ∨
       p = "core::panicking::panic_str_2015" ∨
       p = "core::panicking::unreachable_display" ∨
       p = "core::option::unwrap_failed" ∨
       p = "core::option::expect_failed" ∨
       p = "core::result::unwrap_failed" ∨
       p = "core::panicking::panic_const::panic_const_add_overflow" ∨
       p = "core::panicking::panic_const::panic_const_sub_overflow" ∨
       p = "core::panicking::panic_const::panic_const_mul_overflow" ∨
       p = "core::panicking::panic_const::panic_const_div_overflow" ∨
       p = "core::panicking::panic_const::panic_const_rem_overflow" ∨
       p = "core::panicking::panic_const::panic_const_neg_overflow" ∨
       p = "core::panicking::panic_const::panic_const_shr_overflow" ∨
       p = "core::panicking::panic_const::panic_const_shl_overflow" ∨
       p = "core::panicking::panic_const::panic_const_div_by_zero" ∨
       p = "core::panicking::panic_const::panic_const_rem_by_zero") →
      findCallee? s.memory.callees p = .none →
      (s.memory.callStack = .nil →
        evalTerminator s ⟨.call (mkFnOp p) argOps destination .none .continue_, span⟩ (.some callerBody) =
          MirStepNode.retOutcome .panic) ∧
      (s.memory.callStack = caller :: restStack →
        caller.returnUnwind = .cleanup cleanupBb →
        evalTerminator s ⟨.call (mkFnOp p) argOps destination .none .continue_, span⟩ (.some callerBody) =
          MirStepNode.step
            { frame := { caller.frame with blockIdx := cleanupBb, stmtIdx := 0 }
              memory :=
                { s.memory with
                  callStack := restStack
                  activeCallee := .some caller.callerBody
                  activeProtectors := restoreCallerProtectors caller } }) ∧
      (evalTerminator s ⟨.call (mkFnOp p) argOps destination .none (.cleanup cleanupBb), span⟩ (.some callerBody) =
        MirStepNode.step
          { frame := { s.frame with blockIdx := cleanupBb, stmtIdx := 0, locals := locals' }
            memory := s.memory }) ∧
      (evalTerminator s ⟨.call (mkFnOp p) argOps destination .none .terminate, span⟩ (.some callerBody) =
        MirStepNode.retOutcome .abort) ∧
      (evalTerminator s ⟨.call (mkFnOp p) argOps destination .none .unreachable, span⟩ (.some callerBody) =
        MirStepNode.fail .ub)) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro pAbort hpAbort hFindNone
    have hpAbortFlags :
        isUnreachableCallTarget pAbort = false ∧
        isAbortingPanicDefPath pAbort = true := by
      rcases hpAbort with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rcases hpAbortFlags with ⟨hNotUnreach, hAbort⟩
    simp only [evalTerminator, resolveCallTarget, extractCalleeDefPath?,
      extractCalleeTypeArgs, hArgs, hFindNone, hNotUnreach, hAbort]
  · intro p hp hFindNone
    have hpFlags :
        isUnreachableCallTarget p = false ∧
        isAbortingPanicDefPath p = false ∧
        isUnwindingPanicDefPath p = true := by
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rcases hpFlags with ⟨hNotUnreach, hNotAbort, hUnwindPanic⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hRoot
      simp only [evalTerminator, resolveCallTarget, extractCalleeDefPath?,
        extractCalleeTypeArgs, hArgs, hNotUnreach, hFindNone, hNotAbort, hUnwindPanic,
        applyUnwindAction, hRoot, unwindFromCallStack]
    · intro hStack hCallerUnwind
      simp only [evalTerminator, resolveCallTarget, extractCalleeDefPath?,
        extractCalleeTypeArgs, hArgs, hNotUnreach, hFindNone, hNotAbort, hUnwindPanic,
        applyUnwindAction, hStack, unwindFromCallStack, hCallerUnwind]
    · simp only [evalTerminator, resolveCallTarget, extractCalleeDefPath?,
        extractCalleeTypeArgs, hArgs, hNotUnreach, hFindNone, hNotAbort, hUnwindPanic,
        applyUnwindAction]
    · simp only [evalTerminator, resolveCallTarget, extractCalleeDefPath?,
        extractCalleeTypeArgs, hArgs, hNotUnreach, hFindNone, hNotAbort, hUnwindPanic,
        applyUnwindAction]
    · simp only [evalTerminator, resolveCallTarget, extractCalleeDefPath?,
        extractCalleeTypeArgs, hArgs, hNotUnreach, hFindNone, hNotAbort, hUnwindPanic,
        applyUnwindAction]

/--
Universal characterization of external diverging calls (`target = .none`) and
`resumeExternalDivergingCall`:
1. When `target.defPath` is not an unreachable target, not in `s.memory.callees`,
   and not an inline panic entrypoint, `evalTerminator` emits `MirStepNode.extCall`
   with continuation `resumeExternalDivergingCall s locals' unwind`.
2. If the external call returns normally (`MirCallAns.returned retVal memAfter`),
   `resumeExternalDivergingCall` faults with `.faulted .ub`.
3. If the external call unwinds (`MirCallAns.panicked memAfter`),
   `resumeExternalDivergingCall` transitions via
   `applyUnwindAction s locals' memAfter unwind`.
4. If the external call aborts (`MirCallAns.aborted`),
   `resumeExternalDivergingCall` halts with `.halted .abort`.
-/
theorem mir_evalTerminator_diverging_call_external_corresponds
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (span : String)
    (callerBody : CapturedMir)
    (defPath : DefPath)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (hFunc : extractCalleeDefPath? func = .some defPath)
    (hNotUnreach : isUnreachableCallTarget defPath = false)
    (hFindNone : findCallee? s.memory.callees defPath = .none)
    (hNotAbort : isAbortingPanicDefPath defPath = false)
    (hNotPanic : isUnwindingPanicDefPath defPath = false)
    (hArgs :
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals') :
    (evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
      MirStepNode.extCall
        { defPath := defPath, args := argVals, memory := s.memory }
        (resumeExternalDivergingCall s locals' unwind)) ∧
    (∀ (retVal : Value) (memAfter : Memory),
      resumeExternalDivergingCall s locals' unwind (.returned retVal memAfter) = .faulted .ub) ∧
    (∀ (memAfter : Memory),
      resumeExternalDivergingCall s locals' unwind (.panicked memAfter) =
        applyUnwindAction s locals' memAfter unwind) ∧
    (resumeExternalDivergingCall s locals' unwind .aborted = .halted .abort) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [evalTerminator, resolveCallTarget, hFunc, hArgs,
      hNotUnreach, hFindNone, hNotAbort, hNotPanic]
  · intro retVal memAfter
    rfl
  · intro memAfter
    rfl
  · rfl

/--
Universal characterization of `TerminatorKind.unwindResume` and
`TerminatorKind.unwindTerminate` across root and nested call-stack frames:
1. `TerminatorKind.unwindTerminate` halts immediately with
   `MirStepNode.retOutcome .abort`.
2. At the root frame (`s.memory.callStack = .nil`), `TerminatorKind.unwindResume`
   halts with `MirStepNode.retOutcome .panic`.
3. When `s.memory.callStack = caller :: restStack`:
   - If `caller.returnUnwind = .cleanup cleanupBb`, `TerminatorKind.unwindResume`
     pops `caller`, restores `caller.callerBody` and `restoreCallerProtectors caller`,
     and jumps to `cleanupBb` in `caller.frame`.
   - If `caller.returnUnwind = .terminate`, `TerminatorKind.unwindResume` halts with
     `MirStepNode.retOutcome .abort`.
   - If `caller.returnUnwind = .unreachable`, `TerminatorKind.unwindResume` faults
     with `MirStepNode.fail .ub`.
   - If `caller.returnUnwind = .continue_` and `restStack = grandCaller :: restStack₂`
     with `grandCaller.returnUnwind = .cleanup grandCleanupBb`, `TerminatorKind.unwindResume`
     transitively pops both `caller` and `grandCaller` and jumps to `grandCleanupBb`
     in `grandCaller.frame`.
-/
theorem mir_evalTerminator_unwindResume_and_unwindTerminate_corresponds
    (s : MachineState)
    (span : String)
    (currentBody : Option CapturedMir)
    (caller grandCaller : SavedCallerFrame)
    (restStack restStack₂ : List SavedCallerFrame)
    (cleanupBb grandCleanupBb : BasicBlockIdx) :
    (evalTerminator s ⟨.unwindTerminate, span⟩ currentBody = MirStepNode.retOutcome .abort) ∧
    (s.memory.callStack = .nil →
      evalTerminator s ⟨.unwindResume, span⟩ currentBody = MirStepNode.retOutcome .panic) ∧
    (s.memory.callStack = caller :: restStack →
      caller.returnUnwind = .cleanup cleanupBb →
      evalTerminator s ⟨.unwindResume, span⟩ currentBody =
        MirStepNode.step
          { frame := { caller.frame with blockIdx := cleanupBb, stmtIdx := 0 }
            memory :=
              { s.memory with
                callStack := restStack
                activeCallee := .some caller.callerBody
                activeProtectors := restoreCallerProtectors caller } }) ∧
    (s.memory.callStack = caller :: restStack →
      caller.returnUnwind = .terminate →
      evalTerminator s ⟨.unwindResume, span⟩ currentBody = MirStepNode.retOutcome .abort) ∧
    (s.memory.callStack = caller :: restStack →
      caller.returnUnwind = .unreachable →
      evalTerminator s ⟨.unwindResume, span⟩ currentBody = MirStepNode.fail .ub) ∧
    (s.memory.callStack = caller :: grandCaller :: restStack₂ →
      caller.returnUnwind = .continue_ →
      grandCaller.returnUnwind = .cleanup grandCleanupBb →
      evalTerminator s ⟨.unwindResume, span⟩ currentBody =
        MirStepNode.step
          { frame := { grandCaller.frame with blockIdx := grandCleanupBb, stmtIdx := 0 }
            memory :=
              { s.memory with
                callStack := restStack₂
                activeCallee := .some grandCaller.callerBody
                activeProtectors := restoreCallerProtectors grandCaller } }) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro hNil
    simp [evalTerminator, hNil]
  · intro hStack hUnwind
    simp [evalTerminator, hStack, hUnwind]
  · intro hStack hUnwind
    simp [evalTerminator, hStack, hUnwind]
  · intro hStack hUnwind
    simp [evalTerminator, hStack, hUnwind]
  · intro hStack hUnwind1 hUnwind2
    simp [evalTerminator, hStack, hUnwind1, hUnwind2]

/--
Universal characterization of interprocedural unwind propagation out of a
non-diverging linked callee (`pushCalleeFrame`, `target = .some targetBb`) and
external call/tail-call continuation handlers (`resumeExternalCall` and
`resumeExternalTailCall`):
1. When a caller invokes a linked `calleeBody` via `pushCalleeFrame` with
   `unwind : UnwindAction` and `calleeBody` unwinds via `TerminatorKind.unwindResume`
   OR via a failing `TerminatorKind.assert` with `.continue_`, execution pops
   the saved caller frame, restores `callerBody` and `s.memory.activeProtectors`,
   and dispatches the caller's `unwind` (`.cleanup cleanupBb`, `.terminate`,
   `.unreachable`, or `.continue_`).
2. `resumeExternalCall` on `.panicked memAfter` transitions via
   `applyUnwindAction s locals' memAfter unwind` and on `.aborted` halts with
   `.halted .abort`.
3. `resumeExternalTailCall` on `.panicked memAfter` unwinds via
   `unwindFromCallStack memAfter.callStack memAfter` and on `.aborted` halts
   with `.halted .abort`.
-/
theorem mir_evalTerminator_callee_unwind_and_external_resume_corresponds
    (s : MachineState)
    (destination : Place)
    (targetBb cleanupBb assertTargetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (callerBody calleeBody : CapturedMir)
    (argVals : List Value)
    (locals' calleeLocalsAfterCond : List LocalSlot)
    (cond : Operand) :
    let enteredState :=
      pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind
    (unwind = .cleanup cleanupBb →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.step
          { frame :=
              { s.frame with
                blockIdx := cleanupBb
                stmtIdx := 0
                locals := locals' }
            memory :=
              { s.memory with
                callStack := s.memory.callStack
                activeCallee := .some callerBody
                activeProtectors := s.memory.activeProtectors } }) ∧
    (unwind = .terminate →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.retOutcome .abort) ∧
    (unwind = .unreachable →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.fail .ub) ∧
    (unwind = .continue_ →
      s.memory.callStack = .nil →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.retOutcome .panic) ∧
    (unwind = .cleanup cleanupBb →
      evalOperand
        enteredState.frame.locals
        cond
        enteredState.memory.borrows
        enteredState.memory.globals
        calleeBody.layouts
        enteredState.memory.callerLocals =
          .ok (.scalar { bits := 0, sizeBytes := 1 }) calleeLocalsAfterCond →
      evalTerminator
        enteredState
        ⟨.assert cond true assertTargetBb .continue_, span⟩
        (.some calleeBody) =
        MirStepNode.step
          { frame :=
              { s.frame with
                blockIdx := cleanupBb
                stmtIdx := 0
                locals := locals' }
            memory :=
              { s.memory with
                callStack := s.memory.callStack
                activeCallee := .some callerBody
                activeProtectors := s.memory.activeProtectors } }) ∧
    (∀ memAfter : Memory,
      resumeExternalCall s locals' destination targetBb unwind (.panicked memAfter) =
        applyUnwindAction s locals' memAfter unwind ∧
      resumeExternalCall s locals' destination targetBb unwind .aborted = .halted .abort ∧
      resumeExternalTailCall (.panicked memAfter) =
        unwindFromCallStack memAfter.callStack memAfter ∧
      resumeExternalTailCall .aborted = .halted .abort) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hUnwind
    subst hUnwind
    simp [evalTerminator, pushCalleeFrame, unwindFromCallStack, restoreCallerProtectors]
  · intro hUnwind
    subst hUnwind
    simp [evalTerminator, pushCalleeFrame, unwindFromCallStack]
  · intro hUnwind
    subst hUnwind
    simp [evalTerminator, pushCalleeFrame, unwindFromCallStack]
  · intro hUnwind hNil
    subst hUnwind
    simp [evalTerminator, pushCalleeFrame, unwindFromCallStack, hNil]
  · intro hUnwind hCond
    subst hUnwind
    simp only [evalTerminator, hCond]
    rfl
  · intro memAfter
    exact ⟨rfl, rfl, rfl, rfl⟩

/--
Universal 4-way partition theorem for unlinked direct diverging calls (`target = .none`,
`findCallee? s.memory.callees defPath = .none`) and multi-step interprocedural
cleanup-and-`unwindResume` chains:
1. For every `defPath : DefPath` with `extractCalleeDefPath? func = .some defPath`
   and `findCallee? s.memory.callees defPath = .none`:
   - `isUnreachableCallTarget defPath = true` steps to `MirStepNode.fail .ub`;
   - `isUnreachableCallTarget defPath = false ∧ isAbortingPanicDefPath defPath = true`
     steps to `MirStepNode.retOutcome .abort`;
   - `isUnreachableCallTarget defPath = false ∧ isAbortingPanicDefPath defPath = false ∧ isUnwindingPanicDefPath defPath = true`
     dispatches `applyUnwindAction s locals' s.memory unwind`; and
   - when all three predicates are `false`, emits `MirStepNode.extCall` with
     `resumeExternalDivergingCall s locals' unwind`.
2. When `callerBody` invokes a linked diverging `calleeBody` (`pushDivergingCalleeFrame`)
   with `unwind = .cleanup callerCleanupBb`, and `calleeBody` catches an internal
   panic at `calleeCleanupBb` (`applyUnwindAction ... (.cleanup calleeCleanupBb)`)
   before executing `TerminatorKind.unwindResume` at `calleeCleanupBb`, execution
   pops `calleeBody`'s frame, restores `callerBody` and `s.memory.activeProtectors`,
   lands at `callerCleanupBb` in `callerBody`, and from `callerCleanupBb` a
   subsequent `TerminatorKind.unwindResume` (at root `s.memory.callStack = .nil`)
   halts with `MirStepNode.retOutcome .panic` while `TerminatorKind.unwindTerminate`
   halts with `MirStepNode.retOutcome .abort`.
-/
theorem mir_evalTerminator_diverging_call_partition_and_cleanup_chain
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (callerCleanupBb calleeCleanupBb : BasicBlockIdx)
    (span : String)
    (callerBody calleeBody : CapturedMir)
    (defPath : DefPath)
    (argVals : List Value)
    (locals' calleeLocalsAfterPanic : List LocalSlot)
    (calleeActiveProtectors : List Nat)
    (hFunc : extractCalleeDefPath? func = .some defPath)
    (hArgs :
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals') :
    let s₁ :=
      pushDivergingCalleeFrame
        s
        callerBody
        locals'
        destination
        (.cleanup callerCleanupBb)
        calleeBody
        argVals
    let memInCallee : Memory :=
      { s₁.memory with activeProtectors := calleeActiveProtectors }
    let s₂ : MachineState :=
      { frame :=
          { s₁.frame with
            blockIdx := calleeCleanupBb
            stmtIdx := 0
            locals := calleeLocalsAfterPanic }
        memory := memInCallee }
    let s₃ : MachineState :=
      { frame :=
          { s.frame with
            blockIdx := callerCleanupBb
            stmtIdx := 0
            locals := locals' }
        memory :=
          { s.memory with
            callStack := s.memory.callStack
            activeCallee := .some callerBody
            activeProtectors := s.memory.activeProtectors } }
    (findCallee? s.memory.callees defPath = .none →
      isUnreachableCallTarget defPath = true →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (findCallee? s.memory.callees defPath = .none →
      isUnreachableCallTarget defPath = false →
      isAbortingPanicDefPath defPath = true →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.retOutcome .abort) ∧
    (findCallee? s.memory.callees defPath = .none →
      isUnreachableCallTarget defPath = false →
      isAbortingPanicDefPath defPath = false →
      isUnwindingPanicDefPath defPath = true →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        match applyUnwindAction s locals' s.memory unwind with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) ∧
    (findCallee? s.memory.callees defPath = .none →
      isUnreachableCallTarget defPath = false →
      isAbortingPanicDefPath defPath = false →
      isUnwindingPanicDefPath defPath = false →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := defPath, args := argVals, memory := s.memory }
          (resumeExternalDivergingCall s locals' unwind)) ∧
    (applyUnwindAction s₁ calleeLocalsAfterPanic memInCallee (.cleanup calleeCleanupBb) =
      .running s₂ ∧
     evalTerminator s₂ ⟨.unwindResume, span⟩ (.some calleeBody) =
      MirStepNode.step s₃ ∧
     (s.memory.callStack = .nil →
       evalTerminator s₃ ⟨.unwindResume, span⟩ (.some callerBody) =
         MirStepNode.retOutcome .panic) ∧
     evalTerminator s₃ ⟨.unwindTerminate, span⟩ (.some callerBody) =
       MirStepNode.retOutcome .abort) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hFindNone hUnreach
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgs, hFindNone, hUnreach]
  · intro hFindNone hNotUnreach hAbort
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgs, hFindNone, hNotUnreach, hAbort]
  · intro hFindNone hNotUnreach hNotAbort hPanic
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgs, hFindNone,
      hNotUnreach, hNotAbort, hPanic]
    cases applyUnwindAction s locals' s.memory unwind <;> rfl
  · intro hFindNone hNotUnreach hNotAbort hNotPanic
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgs, hFindNone,
      hNotUnreach, hNotAbort, hNotPanic]
  · refine ⟨rfl, ?_, ?_, rfl⟩
    · simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack, restoreCallerProtectors]
    · intro hNil
      simp [evalTerminator, unwindFromCallStack, hNil]

/-! ## 5. `CallConv.rustIntrinsic` Compiler Intrinsics Executed Inside `core` (`BRIEF-1.3`) -/

/--
Helper constructing a direct `TerminatorKind.call` to `defPath` with generic
type arguments `typeArgs` and operand list `argOps`.
-/
def mkIntrinsicCallTerm
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (argOps : List Operand)
    (dest : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction := .continue_)
    (span : String := "") :
    Terminator :=
  let fnTy : Ty := { kind := .fnDef defPath typeArgs, layoutIdx := 0 }
  let funcOp : Operand := .constant { ty := fnTy, val := .zeroSized }
  ⟨.call funcOp argOps dest (.some targetBb) unwind, span⟩

/--
**Theorem L5.19 (`mir_evalTerminator_ub_checks_intrinsic_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for
`"core::intrinsics::ub_checks"` in `V2026_08_01`:
1. Calling `"core::intrinsics::ub_checks"` with zero arguments writes boolean
   `true` (`Value.scalar ⟨1, 1⟩`) to `destination` and steps to `targetBb`;
2. Calling `"core::intrinsics::ub_checks"` with any non-empty argument list
   faults with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_ub_checks_intrinsic_corresponds
    (argVal : Value)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init argVal]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let okTerm := mkIntrinsicCallTerm "core::intrinsics::ub_checks" .nil .nil dest targetBb unwind span
    let badTerm :=
      mkIntrinsicCallTerm
        "core::intrinsics::ub_checks"
        .nil
        [.copy { local_ := 1, projection := .nil }]
        dest
        targetBb
        unwind
        span
    evalTerminator s okTerm .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := [.init (.scalar ⟨1, 1⟩), .init argVal]
        }
        memory := emptyMemory
      } ∧
    evalTerminator s badTerm .none = MirStepNode.fail .ub := by
  dsimp only
  have h : classifyRustIntrinsic? "core::intrinsics::ub_checks" = .some .ubChecks := rfl
  have hEx : stringEq "core::intrinsics::ub_checks" "core::intrinsics::exact_div" = false := rfl
  refine ⟨?_, ?_⟩
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, emptyMemory,
      findCallee?, isDirectExactDivTarget, evalDirectRustIntrinsic?, h, hEx,
      evalNonSelectIntrinsicCall, writeIntrinsicReturn,
      writePlaceValue, get?, set?]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]

/--
**Theorem L5.20 (`mir_evalTerminator_const_eval_select_intrinsic_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for
`"core::intrinsics::const_eval_select"` in `V2026_08_01`:
1. When `arg_0` is a tuple `Value.aggregate 0 unpackedArgs` and `arg_2` resolves
   to a linked `calleeBody` with matching `argCount = length unpackedArgs` and
   non-intrinsic ABI, `evalTerminator` pushes `calleeBody` onto `s.memory.callStack`
   with `initLocals calleeBody unpackedArgs`;
2. When `arg_0` is `Value.unit` (0-tuple `()`) and `arg_2` resolves to a 0-arg
   linked `calleeBody`, `evalTerminator` pushes `calleeBody` with
   `initLocals calleeBody .nil`;
3. When `arg_2` resolves to an unlinked unreachable or panic target,
   `evalTerminator` dispatches to `MirStepNode.fail .ub`
   (`core::hint::unreachable_unchecked`), `MirStepNode.retOutcome .abort`
   (`core::panicking::panic_nounwind`), or `applyUnwindAction`
   (`core::panicking::panic`) rather than falling through to `extCall`;
4. When `arg_0` is not a tuple (`Value.scalar sc`) or `calleeBody.argCount` does
   not match `length unpackedArgs`, `evalTerminator` faults with
   `MirStepNode.fail .ub`;
5. When `arg_0` is `Value.unit` and `ARG` is a tuple of inhabited zero-sized
   fields such as `((), ())`, `unpackConstEvalSelectArgs?` yields one
   `Value.unit` per field, and it rejects non-tuple `ARG`, non-ZST tuple
   elements (`(u32,)`), uninhabited elements (`(!,)`), or mismatched `.aggregate`
   tuple arities with `.none`.
-/
theorem mir_evalTerminator_const_eval_select_intrinsic_corresponds
    (v1 v2 : Value)
    (sc : ScalarInt)
    (callerBody calleeBody2 calleeBody0 : CapturedMir)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (hPath2 : calleeBody2.defPath = "core::rt_callee_2")
    (hArgs2 : calleeBody2.argCount = 2)
    (hConv2 : calleeBody2.fnAbi.conv = .rust)
    (hPath0 : calleeBody0.defPath = "core::rt_callee_0")
    (hArgs0 : calleeBody0.argCount = 0)
    (hConv0 : calleeBody0.fnAbi.conv = .rust) :
    let dest : Place := { local_ := 0, projection := .nil }
    let constFnOp : Operand :=
      .constant { ty := { kind := .fnDef "core::ct_callee" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtFnOp2 : Operand :=
      .constant { ty := { kind := .fnDef "core::rt_callee_2" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtFnOp0 : Operand :=
      .constant { ty := { kind := .fnDef "core::rt_callee_0" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtFnOpUnreach : Operand :=
      .constant { ty := { kind := .fnDef "core::hint::unreachable_unchecked" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtFnOpNounwind : Operand :=
      .constant { ty := { kind := .fnDef "core::panicking::panic_nounwind" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtFnOpPanic : Operand :=
      .constant { ty := { kind := .fnDef "core::panicking::panic" .nil, layoutIdx := 0 }, val := .zeroSized }
    let argOps2 : List Operand := [
      .copy { local_ := 1, projection := .nil },
      constFnOp,
      rtFnOp2
    ]
    let argOps0 : List Operand := [
      .copy { local_ := 2, projection := .nil },
      constFnOp,
      rtFnOp0
    ]
    let argOpsUnreach : List Operand := [
      .copy { local_ := 2, projection := .nil },
      constFnOp,
      rtFnOpUnreach
    ]
    let argOpsNounwind : List Operand := [
      .copy { local_ := 2, projection := .nil },
      constFnOp,
      rtFnOpNounwind
    ]
    let argOpsPanic : List Operand := [
      .copy { local_ := 2, projection := .nil },
      constFnOp,
      rtFnOpPanic
    ]
    let argOpsBadTuple : List Operand := [
      .copy { local_ := 3, projection := .nil },
      constFnOp,
      rtFnOp2
    ]
    let argOpsArityMismatch : List Operand := [
      .copy { local_ := 1, projection := .nil },
      constFnOp,
      rtFnOp0
    ]
    let locals : List LocalSlot := [
      .uninit,
      .init (.aggregate 0 [v1, v2]),
      .init .unit,
      .init (.scalar sc)
    ]
    let mem : Memory := { emptyMemory with callees := [calleeBody2, calleeBody0] }
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := mem
    }
    let term2 := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOps2 dest targetBb unwind span
    let term0 := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOps0 dest targetBb unwind span
    let termUnreach := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOpsUnreach dest targetBb unwind span
    let termNounwind := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOpsNounwind dest targetBb unwind span
    let termPanic := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOpsPanic dest targetBb unwind span
    let termBadTuple := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOpsBadTuple dest targetBb unwind span
    let termBadArity := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOpsArityMismatch dest targetBb unwind span
    evalTerminator s term2 (.some callerBody) =
      MirStepNode.step (pushCalleeFrame s callerBody locals dest targetBb calleeBody2 [v1, v2] unwind) ∧
    evalTerminator s term0 (.some callerBody) =
      MirStepNode.step (pushCalleeFrame s callerBody locals dest targetBb calleeBody0 .nil unwind) ∧
    evalTerminator s termUnreach (.some callerBody) = MirStepNode.fail .ub ∧
    evalTerminator s termNounwind (.some callerBody) = MirStepNode.retOutcome .abort ∧
    evalTerminator s termPanic (.some callerBody) =
      (match applyUnwindAction s locals mem unwind with
       | .running nextState => MirStepNode.step nextState
       | .halted out => MirStepNode.retOutcome out
       | .faulted fk => MirStepNode.fail fk) ∧
    evalTerminator s termBadTuple (.some callerBody) = MirStepNode.fail .ub ∧
    evalTerminator s termBadArity (.some callerBody) = MirStepNode.fail .ub ∧
    unpackConstEvalSelectArgs? .unit (.some (.tuple [.tuple .nil, .tuple .nil])) = .some [.unit, .unit] ∧
    unpackConstEvalSelectArgs? .unit (.some (.uint .u32)) = .none ∧
    unpackConstEvalSelectArgs? .unit (.some (.tuple [.uint .u32])) = .none ∧
    unpackConstEvalSelectArgs? .unit (.some (.tuple [.never])) = .none ∧
    unpackConstEvalSelectArgs? (.aggregate 0 [v1, v2]) (.some (.uint .u32)) = .none ∧
    unpackConstEvalSelectArgs? (.aggregate 0 [v1, v2]) (.some (.tuple [.uint .u32])) = .none := by
  dsimp only
  have hFindSel2 : stringEq calleeBody2.defPath "core::intrinsics::const_eval_select" = false := by
    rw [hPath2]; rfl
  have hFindSel0 : stringEq calleeBody0.defPath "core::intrinsics::const_eval_select" = false := by
    rw [hPath0]; rfl
  have hMatch2 : stringEq calleeBody2.defPath "core::rt_callee_2" = true := by
    rw [hPath2]; rfl
  have hMiss20 : stringEq calleeBody2.defPath "core::rt_callee_0" = false := by
    rw [hPath2]; rfl
  have hMatch0 : stringEq calleeBody0.defPath "core::rt_callee_0" = true := by
    rw [hPath0]; rfl
  have hMiss2U : stringEq calleeBody2.defPath "core::hint::unreachable_unchecked" = false := by
    rw [hPath2]; rfl
  have hMiss0U : stringEq calleeBody0.defPath "core::hint::unreachable_unchecked" = false := by
    rw [hPath0]; rfl
  have hMiss2N : stringEq calleeBody2.defPath "core::panicking::panic_nounwind" = false := by
    rw [hPath2]; rfl
  have hMiss0N : stringEq calleeBody0.defPath "core::panicking::panic_nounwind" = false := by
    rw [hPath0]; rfl
  have hMiss2P : stringEq calleeBody2.defPath "core::panicking::panic" = false := by
    rw [hPath2]; rfl
  have hMiss0P : stringEq calleeBody0.defPath "core::panicking::panic" = false := by
    rw [hPath0]; rfl
  have hKind : classifyRustIntrinsic? "core::intrinsics::const_eval_select" = .some .constEvalSelect := rfl
  have hEx : stringEq "core::intrinsics::const_eval_select" "core::intrinsics::exact_div" = false := rfl
  have hKindU : classifyRustIntrinsic? "core::hint::unreachable_unchecked" = .none := rfl
  have hExU : stringEq "core::hint::unreachable_unchecked" "core::intrinsics::exact_div" = false := rfl
  have hKindN : classifyRustIntrinsic? "core::panicking::panic_nounwind" = .none := rfl
  have hExN : stringEq "core::panicking::panic_nounwind" "core::intrinsics::exact_div" = false := rfl
  have hKindP : classifyRustIntrinsic? "core::panicking::panic" = .none := rfl
  have hExP : stringEq "core::panicking::panic" "core::intrinsics::exact_div" = false := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, emptyMemory, get?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, unpackConstEvalSelectArgs?, resolveConstEvalSelectTarget?,
      hMatch2, hArgs2, hConv2, callConvEq, length]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, emptyMemory, get?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, resolveConstEvalSelectTarget?, hMiss20, hMatch0, hArgs0, hConv0,
      callConvEq, length]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, emptyMemory, get?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, resolveConstEvalSelectTarget?,
      hMiss2U, hMiss0U, hKindU, hExU]
    rfl
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, emptyMemory, get?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, resolveConstEvalSelectTarget?,
      hMiss2N, hMiss0N, hKindN, hExN]
    rfl
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, emptyMemory, get?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, resolveConstEvalSelectTarget?,
      hMiss2P, hMiss0P, hKindP, hExP]
    rfl
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, get?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, get?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, unpackConstEvalSelectArgs?, resolveConstEvalSelectTarget?,
      hMiss20, hMatch0, hArgs0, hConv0, callConvEq, length]

/--
**Theorem L5.21 (`mir_evalTerminator_arith_offset_intrinsic_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for
`"core::intrinsics::arith_offset"` in `V2026_08_01`:
1. For any 8-byte `ProvenancePtr` `ptrVal`, any 8-byte `isize` scalar `countSc`,
   and `T = u32` (4 bytes), `evalTerminator` preserves `ptrVal.allocId` and
   `ptrVal.tag` and updates `offsetBytes` via `evalArithOffset ptrVal 8 countSc 4`;
2. Negative signed `isize` offset `-2` (`2^64 - 2`) on `T = u32` subtracts `8`
   bytes modulo `2^64`;
3. Non-pointer first argument, non-8-byte `countSc`, or unsized pointee type
   (`.slice (.uint .u8)` or compound `.tuple [.uint .u32, .slice (.uint .u8)]`)
   faults with `MirStepNode.fail .ub`, while a sized
   pointee without a resolvable layout (an ADT `test::Foo` that no local has as
   its type) steps to `MirStepNode.unsupported` instead of borrowing an
   unrelated layout;
4. For the padded tuple `T = (u32, u8)` with no `LayoutTable` entry, the stride
   is the padded size `8`, not the field sum `5`: `evalTerminator` updates
   `offsetBytes` via `evalArithOffset ptrVal 8 countSc 8`;
5. Static sizes resolve through nested floats, arrays, and tuples: `[f64; 4]` is
   `32`, `((u32, u32), f64)` is `16`, `(u32, u8)` is `8`, `[(u32, u8); 2]` is
   `16`, `((u32, u8), u8)` is `12` (inner padding is not reused), and a 12-field
   tuple of `u8` is `12` (tuple arity does not consume the nesting fuel).
-/
theorem mir_evalTerminator_arith_offset_intrinsic_corresponds
    (ptrVal : ProvenancePtr)
    (countSc : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let argOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init (.ptr ptrVal 8), .init (.scalar countSc)]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let okTerm := mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.uint .u32] argOps dest targetBb unwind span
    let paddedTerm :=
      mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.tuple [.uint .u32, .uint .u8]]
        argOps dest targetBb unwind span
    let unsizedTerm :=
      mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.slice (.uint .u8)] argOps dest targetBb unwind span
    let compoundUnsizedTerm :=
      mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.tuple [.uint .u32, .slice (.uint .u8)]]
        argOps dest targetBb unwind span
    let adtTerm :=
      mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.adt "test::Foo" .nil]
        argOps dest targetBb unwind span
    let u8x12 : RigidTy :=
      .tuple [.uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8,
        .uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8]
    (∀ newPtr : ProvenancePtr,
      evalArithOffset ptrVal 8 countSc 4 = .some newPtr →
      evalTerminator s okTerm .none =
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init (.ptr newPtr 8), .init (.ptr ptrVal 8), .init (.scalar countSc)]
          }
          memory := emptyMemory
        }) ∧
    (evalArithOffset ptrVal 8 countSc 4 = .none →
      evalTerminator s okTerm .none = MirStepNode.fail .ub) ∧
    (∀ newPtr : ProvenancePtr,
      evalArithOffset ptrVal 8 countSc 8 = .some newPtr →
      evalTerminator s paddedTerm .none =
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init (.ptr newPtr 8), .init (.ptr ptrVal 8), .init (.scalar countSc)]
          }
          memory := emptyMemory
        }) ∧
    evalTerminator s unsizedTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s compoundUnsizedTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s adtTerm .none = MirStepNode.unsupported ∧
    evalArithOffset { allocId := 7, offsetBytes := 20 } 8 ⟨18446744073709551614, 8⟩ 4 =
      .some { allocId := 7, offsetBytes := 12 } ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable (.array (.float .f64) 4) = .some 32 ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.tuple [.uint .u32, .uint .u32], .float .f64]) = .some 16 ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.uint .u32, .uint .u8]) = .some 8 ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable (.array (.tuple [.uint .u32, .uint .u8]) 2) = .some 16 ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.tuple [.uint .u32, .uint .u8], .uint .u8]) = .some 12 ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable u8x12 = .some 12 := by
  dsimp only
  have hKind : classifyRustIntrinsic? "core::intrinsics::arith_offset" = .some .arithOffset := rfl
  have hEx : stringEq "core::intrinsics::arith_offset" "core::intrinsics::exact_div" = false := rfl
  have hPadSz : intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.uint .u32, .uint .u8]) = .some 8 := rfl
  have hCalc :
      evalTerminator
        { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ptrVal 8), .init (.scalar countSc)] },
          memory := emptyMemory }
        (mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.uint .u32]
          [.copy { local_ := 1, projection := .nil }, .copy { local_ := 2, projection := .nil }]
          { local_ := 0, projection := .nil } targetBb unwind span)
        .none =
      (match evalArithOffset ptrVal 8 countSc 4 with
       | .some retPtrVal =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [.init (.ptr retPtrVal 8), .init (.ptr ptrVal 8), .init (.scalar countSc)]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) := by
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hKind, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intCastTargetBytes, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalArithOffset ptrVal 8 countSc 4 <;> rfl
  have hCalcPad :
      evalTerminator
        { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ptrVal 8), .init (.scalar countSc)] },
          memory := emptyMemory }
        (mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.tuple [.uint .u32, .uint .u8]]
          [.copy { local_ := 1, projection := .nil }, .copy { local_ := 2, projection := .nil }]
          { local_ := 0, projection := .nil } targetBb unwind span)
        .none =
      (match evalArithOffset ptrVal 8 countSc 8 with
       | .some retPtrVal =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [.init (.ptr retPtrVal 8), .init (.ptr ptrVal 8), .init (.scalar countSc)]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) := by
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hKind, hEx, evalNonSelectIntrinsicCall, hPadSz,
      writeIntrinsicReturn, writePlaceValue, set?]
    cases evalArithOffset ptrVal 8 countSc 8 <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro newPtr hOk
    rw [hCalc, hOk]
  · intro hNone
    rw [hCalc, hNone]
  · intro newPtr hOk
    rw [hCalcPad, hOk]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hKind, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, findDeclLayoutForRigidTy,
      intrinsicUnresolvedLayoutStep]
  · have hUnsizedSz :
        intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.uint .u32, .slice (.uint .u8)]) = .none :=
      rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hKind, hEx, evalNonSelectIntrinsicCall, hUnsizedSz,
      intrinsicUnresolvedLayoutStep]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hKind, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux,
      findDeclLayoutForRigidTy, intrinsicUnresolvedLayoutStep]

/--
**Theorem L5.22 (`mir_evalTerminator_bit_intrinsics_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for the bit-manipulation
intrinsics (`ctlz`, `ctlz_nonzero`, `cttz`, `cttz_nonzero`, `ctpop`, `bswap`,
`bitreverse`) in `V2026_08_01`.
-/
theorem mir_evalTerminator_bit_intrinsics_corresponds
    (sc : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let argOps : List Operand := [.copy { local_ := 1, projection := .nil }]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init (.scalar sc)]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let mkCall (name : DefPath) := mkIntrinsicCallTerm name .nil argOps dest targetBb unwind span
    let mkExpected (resOpt : Option ScalarInt) : MirStepNode :=
      match resOpt with
      | .some ret =>
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init (.scalar ret), .init (.scalar sc)]
          }
          memory := emptyMemory
        }
      | .none => MirStepNode.fail .ub
    evalTerminator s (mkCall "core::intrinsics::ctlz") .none = mkExpected (evalCtlz sc) ∧
    evalTerminator s (mkCall "core::intrinsics::ctlz_nonzero") .none = mkExpected (evalCtlzNonzero sc) ∧
    evalTerminator s (mkCall "core::intrinsics::cttz") .none = mkExpected (evalCttz sc) ∧
    evalTerminator s (mkCall "core::intrinsics::cttz_nonzero") .none = mkExpected (evalCttzNonzero sc) ∧
    evalTerminator s (mkCall "core::intrinsics::ctpop") .none = mkExpected (evalCtpop sc) ∧
    evalTerminator s (mkCall "core::intrinsics::bswap") .none = mkExpected (evalBswap sc) ∧
    evalTerminator s (mkCall "core::intrinsics::bitreverse") .none = mkExpected (evalBitreverse sc) ∧
    evalCtlzNonzero ⟨0, 4⟩ = .none ∧
    evalCttzNonzero ⟨0, 8⟩ = .none ∧
    evalCtlz ⟨0, 1⟩ = .some ⟨8, 4⟩ ∧
    evalCttz ⟨0, 2⟩ = .some ⟨16, 4⟩ ∧
    evalCtpop ⟨0xF0F0, 2⟩ = .some ⟨8, 4⟩ ∧
    evalBswap ⟨0x12345678, 4⟩ = .some ⟨0x78563412, 4⟩ ∧
    evalBitreverse ⟨0x80, 1⟩ = .some ⟨0x01, 1⟩ := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::ctlz" = .some .ctlz := rfl
    have hEx : stringEq "core::intrinsics::ctlz" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalCtlz sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::ctlz_nonzero" = .some .ctlzNonzero := rfl
    have hEx : stringEq "core::intrinsics::ctlz_nonzero" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalCtlzNonzero sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::cttz" = .some .cttz := rfl
    have hEx : stringEq "core::intrinsics::cttz" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalCttz sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::cttz_nonzero" = .some .cttzNonzero := rfl
    have hEx : stringEq "core::intrinsics::cttz_nonzero" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalCttzNonzero sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::ctpop" = .some .ctpop := rfl
    have hEx : stringEq "core::intrinsics::ctpop" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalCtpop sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::bswap" = .some .bswap := rfl
    have hEx : stringEq "core::intrinsics::bswap" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalBswap sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::bitreverse" = .some .bitreverse := rfl
    have hEx : stringEq "core::intrinsics::bitreverse" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalBitreverse sc <;> rfl

/--
**Theorem L5.23 (`mir_evalTerminator_wrapping_saturating_unchecked_intrinsics_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for wrapping, saturating,
and unchecked arithmetic and shift intrinsics (`wrapping_add`, `wrapping_sub`,
`wrapping_mul`, `saturating_add`, `saturating_sub`, `unchecked_shl`,
`unchecked_shr`, `unchecked_add`, `unchecked_sub`, `unchecked_mul`,
`unchecked_div`, `unchecked_rem`) in `V2026_08_01`.
-/
theorem mir_evalTerminator_wrapping_saturating_unchecked_intrinsics_corresponds
    (lhs rhs : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let argOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init (.scalar lhs), .init (.scalar rhs)]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let mkCall (name : DefPath) (tyArgs : List RigidTy) :=
      mkIntrinsicCallTerm name tyArgs argOps dest targetBb unwind span
    let mkExpected (resOpt : Option ScalarInt) : MirStepNode :=
      match resOpt with
      | .some ret =>
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init (.scalar ret), .init (.scalar lhs), .init (.scalar rhs)]
          }
          memory := emptyMemory
        }
      | .none => MirStepNode.fail .ub
    evalTerminator s (mkCall "core::intrinsics::wrapping_add" .nil) .none =
      mkExpected (evalWrappingAdd lhs rhs) ∧
    evalTerminator s (mkCall "core::intrinsics::wrapping_sub" .nil) .none =
      mkExpected (evalWrappingSub lhs rhs) ∧
    evalTerminator s (mkCall "core::intrinsics::wrapping_mul" .nil) .none =
      mkExpected (evalWrappingMul lhs rhs) ∧
    evalTerminator s (mkCall "core::intrinsics::saturating_add" [.int .i32]) .none =
      mkExpected (evalSaturatingAdd lhs rhs true) ∧
    evalTerminator s (mkCall "core::intrinsics::saturating_sub" [.uint .u32]) .none =
      mkExpected (evalSaturatingSub lhs rhs false) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_shl" [.uint .u32, .int .i32]) .none =
      mkExpected (evalUncheckedShl lhs rhs true) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_shr" [.int .i32, .uint .u32]) .none =
      mkExpected (evalUncheckedShr lhs rhs true false) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_add" [.int .i32]) .none =
      mkExpected (evalUncheckedAdd lhs rhs true) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_sub" [.uint .u32]) .none =
      mkExpected (evalUncheckedSub lhs rhs false) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_mul" [.int .i16]) .none =
      mkExpected (evalUncheckedMul lhs rhs true) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_div" [.int .i32]) .none =
      mkExpected (evalUncheckedDiv lhs rhs true) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_rem" [.int .i32]) .none =
      mkExpected (evalUncheckedRem lhs rhs true) ∧
    evalUncheckedAdd ⟨255, 1⟩ ⟨1, 1⟩ false = .none ∧
    evalUncheckedSub ⟨0, 1⟩ ⟨1, 1⟩ false = .none ∧
    evalUncheckedDiv ⟨128, 1⟩ ⟨255, 1⟩ true = .none ∧
    evalUncheckedRem ⟨128, 1⟩ ⟨255, 1⟩ true = .none ∧
    evalUncheckedShl ⟨1, 4⟩ ⟨32, 4⟩ false = .none ∧
    evalUncheckedShr ⟨1, 4⟩ ⟨255, 1⟩ false true = .none := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::wrapping_add" = .some .wrappingAdd := rfl
    have hEx : stringEq "core::intrinsics::wrapping_add" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalWrappingAdd lhs rhs <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::wrapping_sub" = .some .wrappingSub := rfl
    have hEx : stringEq "core::intrinsics::wrapping_sub" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalWrappingSub lhs rhs <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::wrapping_mul" = .some .wrappingMul := rfl
    have hEx : stringEq "core::intrinsics::wrapping_mul" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalWrappingMul lhs rhs <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::saturating_add" = .some .saturatingAdd := rfl
    have hEx : stringEq "core::intrinsics::saturating_add" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalSaturatingAdd lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::saturating_sub" = .some .saturatingSub := rfl
    have hEx : stringEq "core::intrinsics::saturating_sub" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalSaturatingSub lhs rhs false <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_shl" = .some .uncheckedShl := rfl
    have hEx : stringEq "core::intrinsics::unchecked_shl" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedShl lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_shr" = .some .uncheckedShr := rfl
    have hEx : stringEq "core::intrinsics::unchecked_shr" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedShr lhs rhs true false <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_add" = .some .uncheckedAdd := rfl
    have hEx : stringEq "core::intrinsics::unchecked_add" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedAdd lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_sub" = .some .uncheckedSub := rfl
    have hEx : stringEq "core::intrinsics::unchecked_sub" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedSub lhs rhs false <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_mul" = .some .uncheckedMul := rfl
    have hEx : stringEq "core::intrinsics::unchecked_mul" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedMul lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_div" = .some .uncheckedDiv := rfl
    have hEx : stringEq "core::intrinsics::unchecked_div" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedDiv lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_rem" = .some .uncheckedRem := rfl
    have hEx : stringEq "core::intrinsics::unchecked_rem" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedRem lhs rhs true <;> rfl

/--
**Theorem L5.24 (`mir_evalTerminator_comparison_and_layout_intrinsics_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for
`"core::intrinsics::three_way_compare"`, `"core::intrinsics::size_of_val"`, and
`"core::intrinsics::align_of_val"` in `V2026_08_01`:
1. `three_way_compare` evaluates `evalThreeWayCompare lhs rhs isSigned` and
   returns `Ordering::Less` (`⟨255, 1⟩`), `Ordering::Equal` (`⟨0, 1⟩`), or
   `Ordering::Greater` (`⟨1, 1⟩`);
2. `size_of_val` and `align_of_val` compute static size/alignment for sized
   thin pointers and dynamic byte size `elemSz * len` / element alignment for
   slice and `str` fat pointers `Value.aggregate 0 [.ptr p 8, .scalar lenSc]`,
   faulting with `MirStepNode.fail .ub` when `elemSz * len > isize::MAX` (for
   `align_of_val` as well as `size_of_val`, since both share the safety
   conditions of `size_of_val_raw`) or when pointer metadata is malformed;
3. `size_of_val::<(u32, u8)>` on a thin pointer returns the padded size `8`;
   `evalSliceSizeOfVal 4 ⟨2^61, 8⟩` faults (`2^63 = isize::MAX + 1` bytes) while
   `evalSliceSizeOfVal 1 ⟨isize::MAX, 8⟩` succeeds; `[(u32, u64); 2]` and the
   9-field tuple `(u8, u8, u8, u8, u8, u8, u8, u8, u64)` have alignment `8`;
4. `size_of_val` and `align_of_val` on `dyn Trait` with a valid wide pointer
   step to `MirStepNode.unsupported` (because dynamic size and alignment live in
   the vtable), whereas passing a thin pointer to `size_of_val::<dyn Trait>` or
   `align_of_val::<dyn Trait>` faults with `MirStepNode.fail .ub`; `size_of_val`
   on an ADT without a resolvable layout steps to `MirStepNode.unsupported`; and
   `findDeclLayoutForRigidTy` resolves layouts by matching a local's type, never
   by position;
5. `size_of_val` and `align_of_val` step to `MirStepNode.unsupported` rather
   than faulting on well-typed custom dynamically sized types the model cannot
   size: a wide pointer to an ADT (`test::SliceTail`) or to a tuple with a
   slice tail (`(u32, [u8])`), and a thin pointer to an extern type
   (`test::Opaque`) or to a tuple with an extern-type tail; a thin pointer to
   the slice-tailed tuple and a wide pointer to `u64` remain malformed and
   fault with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_comparison_and_layout_intrinsics_corresponds
    (lhs rhs : ScalarInt)
    (ptrVal : ProvenancePtr)
    (lenSc : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let cmpOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let thinOps : List Operand := [.copy { local_ := 3, projection := .nil }]
    let fatOps : List Operand := [.copy { local_ := 4, projection := .nil }]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [
      .uninit,
      .init (.scalar lhs),
      .init (.scalar rhs),
      .init (.ptr ptrVal 8),
      .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
    ]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let cmpTerm := mkIntrinsicCallTerm "core::intrinsics::three_way_compare" [.int .i32] cmpOps dest targetBb unwind span
    let szSizedTerm := mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.uint .u64] thinOps dest targetBb unwind span
    let szSliceTerm := mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.slice (.uint .u32)] fatOps dest targetBb unwind span
    let alignSizedTerm := mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.uint .u128] thinOps dest targetBb unwind span
    let alignSliceTerm := mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.slice (.uint .u32)] fatOps dest targetBb unwind span
    let badSizedWithFatTerm := mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.uint .u64] fatOps dest targetBb unwind span
    let szPaddedTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.tuple [.uint .u32, .uint .u8]]
        thinOps dest targetBb unwind span
    let szDynTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.dynamic "core::fmt::Debug"]
        fatOps dest targetBb unwind span
    let alignDynTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.dynamic "core::fmt::Debug"]
        fatOps dest targetBb unwind span
    let badDynThinSzTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.dynamic "core::fmt::Debug"]
        thinOps dest targetBb unwind span
    let badDynThinAlignTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.dynamic "core::fmt::Debug"]
        thinOps dest targetBb unwind span
    let szAdtTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.adt "test::Foo" .nil]
        thinOps dest targetBb unwind span
    let alignStrTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.str] fatOps dest targetBb unwind span
    let szAdtDstTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.adt "test::SliceTail" .nil]
        fatOps dest targetBb unwind span
    let alignTupleDstTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val"
        [.tuple [.uint .u32, .slice (.uint .u8)]] fatOps dest targetBb unwind span
    let szExternTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.foreign "test::Opaque"]
        thinOps dest targetBb unwind span
    let alignExternTailTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val"
        [.tuple [.uint .u8, .foreign "test::Opaque"]] thinOps dest targetBb unwind span
    let badTupleDstThinTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val"
        [.tuple [.uint .u32, .slice (.uint .u8)]] thinOps dest targetBb unwind span
    let badAlignSizedWithFatTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.uint .u64] fatOps dest targetBb unwind span
    let u8Layout : TypeLayout :=
      { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory,
        fields := .primitive, variants := .single 0, isUninhabited := false }
    let u8Decls : List LocalDecl :=
      [{ mutability := .mut, ty := { kind := .uint .u8, layoutIdx := 0 }, debugName := none }]
    let u8Table : LayoutTable := { emptyLayoutTable with entries := [u8Layout] }
    evalTerminator s cmpTerm .none =
      (match evalThreeWayCompare lhs rhs true with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [
               .init (.scalar ret),
               .init (.scalar lhs),
               .init (.scalar rhs),
               .init (.ptr ptrVal 8),
               .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
             ]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s szSizedTerm .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := [
            .init (.scalar ⟨8, 8⟩),
            .init (.scalar lhs),
            .init (.scalar rhs),
            .init (.ptr ptrVal 8),
            .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
          ]
        }
        memory := emptyMemory
      } ∧
    evalTerminator s szSliceTerm .none =
      (match evalSliceSizeOfVal 4 lenSc with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [
               .init (.scalar ret),
               .init (.scalar lhs),
               .init (.scalar rhs),
               .init (.ptr ptrVal 8),
               .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
             ]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s alignSizedTerm .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := [
            .init (.scalar ⟨16, 8⟩),
            .init (.scalar lhs),
            .init (.scalar rhs),
            .init (.ptr ptrVal 8),
            .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
          ]
        }
        memory := emptyMemory
      } ∧
    evalTerminator s alignSliceTerm .none =
      (match evalSliceSizeOfVal 4 lenSc with
       | .some _ =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [
               .init (.scalar ⟨4, 8⟩),
               .init (.scalar lhs),
               .init (.scalar rhs),
               .init (.ptr ptrVal 8),
               .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
             ]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s badSizedWithFatTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s szPaddedTerm .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := [
            .init (.scalar ⟨8, 8⟩),
            .init (.scalar lhs),
            .init (.scalar rhs),
            .init (.ptr ptrVal 8),
            .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
          ]
        }
        memory := emptyMemory
      } ∧
    evalSliceSizeOfVal 4 ⟨2305843009213693952, 8⟩ = .none ∧
    evalSliceSizeOfVal 1 ⟨9223372036854775807, 8⟩ = .some ⟨9223372036854775807, 8⟩ ∧
    intrinsicRigidTyAlign .nil emptyLayoutTable (.array (.tuple [.uint .u32, .uint .u64]) 2) = .some 8 ∧
    intrinsicRigidTyAlign .nil emptyLayoutTable
      (.tuple [.uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8,
        .uint .u8, .uint .u8, .uint .u64]) = .some 8 ∧
    evalTerminator s szDynTerm .none = MirStepNode.unsupported ∧
    evalTerminator s alignDynTerm .none = MirStepNode.unsupported ∧
    evalTerminator s badDynThinSzTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s badDynThinAlignTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s szAdtTerm .none = MirStepNode.unsupported ∧
    findDeclLayoutForRigidTy u8Decls u8Table (.uint .u8) = .some u8Layout ∧
    findDeclLayoutForRigidTy u8Decls u8Table (.adt "test::Foo" .nil) = .none ∧
    evalTerminator s alignStrTerm .none =
      (match evalSliceSizeOfVal 1 lenSc with
       | .some _ =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [
               .init (.scalar ⟨1, 8⟩),
               .init (.scalar lhs),
               .init (.scalar rhs),
               .init (.ptr ptrVal 8),
               .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
             ]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s szAdtDstTerm .none = MirStepNode.unsupported ∧
    evalTerminator s alignTupleDstTerm .none = MirStepNode.unsupported ∧
    evalTerminator s szExternTerm .none = MirStepNode.unsupported ∧
    evalTerminator s alignExternTailTerm .none = MirStepNode.unsupported ∧
    evalTerminator s badTupleDstThinTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s badAlignSizedWithFatTerm .none = MirStepNode.fail .ub := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::three_way_compare" = .some .threeWayCompare := rfl
    have hEx : stringEq "core::intrinsics::three_way_compare" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalThreeWayCompare lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intCastTargetBytes, writeIntrinsicReturn, writePlaceValue, set?]
    rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intCastTargetBytes, writeIntrinsicScalarResult, writeIntrinsicReturn,
      writePlaceValue, set?]
    cases evalSliceSizeOfVal 4 lenSc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyAlign, intrinsicRigidTyAlignAux, intrinsicRigidTyKindAlign,
      intCastTargetBytes, writeIntrinsicReturn, writePlaceValue, set?]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intrinsicRigidTyAlign, intrinsicRigidTyAlignAux, intrinsicRigidTyKindAlign,
      intCastTargetBytes, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalSliceSizeOfVal 4 lenSc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    have hPadSz :
        intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.uint .u32, .uint .u8]) = .some 8 :=
      rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall, hPadSz,
      writeIntrinsicReturn, writePlaceValue, set?]
    rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux,
      findDeclLayoutForRigidTy, intrinsicUnresolvedLayoutStep]

  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicReturn, writePlaceValue, set?]
    cases evalSliceSizeOfVal 1 lenSc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicWidePointeeStep]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicWidePointeeStep]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    have hSz :
        intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.uint .u32, .slice (.uint .u8)]) =
          .none :=
      rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall, hSz,
      intrinsicUnresolvedLayoutStep]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicWidePointeeStep]

/--
**Theorem L5.25 (`mir_evalTerminator_align_of_val_rejects_oversized_slices`)**:
Concrete instance of the `align_of_val` slice-size check in L5.24. For a wide
pointer whose length metadata is `2^61`, `align_of_val::<[u32]>` faults with
`MirStepNode.fail .ub`, because the slice would span `2^63` bytes, one more than
`isize::MAX`; `align_of_val::<str>` on the same pointer returns `1`, because
`2^61` bytes fit in `isize`.
-/
theorem mir_evalTerminator_align_of_val_rejects_oversized_slices
    (ptrVal : ProvenancePtr)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let fatOps : List Operand := [.copy { local_ := 1, projection := .nil }]
    let dest : Place := { local_ := 0, projection := .nil }
    let fatPtr : Value := .aggregate 0 [.ptr ptrVal 8, .scalar ⟨2305843009213693952, 8⟩]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init fatPtr] }
      memory := emptyMemory
    }
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.slice (.uint .u32)]
          fatOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.str]
          fatOps dest targetBb unwind span) .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := [.init (.scalar ⟨1, 8⟩), .init fatPtr]
        }
        memory := emptyMemory
      } := by
  dsimp only
  have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
  have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
  have hBig : evalSliceSizeOfVal 4 ⟨2305843009213693952, 8⟩ = .none := rfl
  have hFit :
      evalSliceSizeOfVal 1 ⟨2305843009213693952, 8⟩ = .some ⟨2305843009213693952, 8⟩ :=
    rfl
  refine ⟨?_, ?_⟩
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intrinsicRigidTyAlign, intrinsicRigidTyAlignAux, intrinsicRigidTyKindAlign,
      intCastTargetBytes, hBig]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall, hFit,
      writeIntrinsicReturn, writePlaceValue, set?]

/--
**Theorem L5.26 (`mir_evalTerminator_intrinsic_signedness_fails_closed`)**:
Signedness resolution for the integer intrinsics accepts exactly the types each
intrinsic is defined for and never guesses:
1. `three_way_compare::<char>` compares as unsigned
   (`evalThreeWayCompare lhs rhs false`), because `core` documents that its
   arguments "must be of character or integer (signed or unsigned) type";
2. `saturating_add::<char>` steps to `MirStepNode.unsupported`, because `char`
   is not an integer type;
3. `unchecked_shl::<u32>` without a second type argument or operand types steps
   to `MirStepNode.unsupported`, because the signedness of the shift count `U`
   decides whether a count with its top bit set is negative.
-/
theorem mir_evalTerminator_intrinsic_signedness_fails_closed
    (lhs rhs : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let argOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init (.scalar lhs), .init (.scalar rhs)]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::three_way_compare" [.char]
          argOps dest targetBb unwind span) .none =
      (match evalThreeWayCompare lhs rhs false with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [.init (.scalar ret), .init (.scalar lhs), .init (.scalar rhs)]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::saturating_add" [.char]
          argOps dest targetBb unwind span) .none =
      MirStepNode.unsupported ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::unchecked_shl" [.uint .u32]
          argOps dest targetBb unwind span) .none =
      MirStepNode.unsupported := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::three_way_compare" = .some .threeWayCompare := rfl
    have hEx : stringEq "core::intrinsics::three_way_compare" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalThreeWayCompare lhs rhs false <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::saturating_add" = .some .saturatingAdd := rfl
    have hEx : stringEq "core::intrinsics::saturating_add" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_shl" = .some .uncheckedShl := rfl
    have hEx : stringEq "core::intrinsics::unchecked_shl" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, findCallee?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicShiftSigned, operandTy, placeTy]

end Correspondence.V2026_08_01.L5_ControlAndCalls
