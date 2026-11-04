import Trusted.Rustc.V2026_08_01.MirSemantics.Statements
import Trusted.Rustc.V2026_08_01.MirSemantics.Terminators
import Trusted.Rustc.V2026_08_01.MirSemantics.Machine
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
      lookupCallee s.memory.callees (match currentBody with | .some b => b.layouts | .none => emptyLayoutTable) "core::hint::unreachable_unchecked" (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      evalTerminator s ⟨.call func .nil destination .none unwind, span⟩ currentBody =
        MirStepNode.fail .ub) ∧
    (extractCalleeDefPath? func = .some "core::intrinsics::unreachable" →
      lookupCallee s.memory.callees (match currentBody with | .some b => b.layouts | .none => emptyLayoutTable) "core::intrinsics::unreachable" (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
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
      lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .some calleeBody →
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
    cases currentBody <;>
      simp only [evalTerminator, evalCallTerminator, resolveCallTarget, hUnreach, evalOperands, hUnreach1] at hFind ⊢ <;>
      simp [hFind]
  · intro hUnreach hFind
    cases currentBody <;>
      simp only [evalTerminator, evalCallTerminator, resolveCallTarget, hUnreach, evalOperands, hUnreach2] at hFind ⊢ <;>
      simp [hFind]
  · intro defPath targetBb calleeBody callerBody argVals locals' hFunc hCurr hArgs hFind
    dsimp only
    subst hCurr
    simp [evalTerminator, evalCallTerminator, hFunc, hArgs, hFind]

/--
**Theorem L5.11 (`mir_evalTerminator_exact_div_intrinsic_corresponds`)**:
Universal correspondence for inline `"core::intrinsics::exact_div"` intrinsic call
dispatch in `Trusted.Rustc.V2026_08_01.MirSemantics.evalTerminator`:
For EVERY machine state `s` with `s.memory.callees = .nil`, EVERY pair of scalar
arguments `lhs rhs : ScalarInt` at locals `1` and `2`, and EVERY target basic block `targetBb`:
1. When `evalExactDiv lhs rhs s.frame.locals s.memory false` succeeds with `.ok retVal s.frame.locals s.memory`
   and `writePlaceValue s.frame.locals s.memory.borrows destination retVal = .ok updatedLocals`,
   `evalTerminator` steps inline to `targetBb` with `stmtIdx := 0` and `locals := updatedLocals`
   (`MrStackFrame.jump_to_block`);
2. When `evalExactDiv lhs rhs s.frame.locals s.memory false = .ub` (divisor zero or non-zero remainder),
   `evalTerminator` faults with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_exact_div_intrinsic_corresponds
    (lhs rhs : ScalarInt) (targetBb : BasicBlockIdx) (unwind : UnwindAction) (span : String) :
    let fnTy : Ty := { kind := .fnDef "core::intrinsics::exact_div" .nil, layoutIdx := 0 }
    let funcOp : Operand := .constant { ty := fnTy, val := .zeroSized }
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
      evalTerminator s ⟨.call funcOp argOps dest (.some targetBb) unwind, span⟩ .none =
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init retVal, .init (.scalar lhs), .init (.scalar rhs)]
          }
          memory := emptyMemory
        }) ∧
    (evalExactDiv lhs rhs locals emptyMemory false = .ub →
      evalTerminator s ⟨.call funcOp argOps dest (.some targetBb) unwind, span⟩ .none =
        MirStepNode.fail .ub) := by
  dsimp only
  have hStr : stringEq "core::intrinsics::exact_div" "core::intrinsics::exact_div" = true := by
    decide
  refine ⟨?_, ?_⟩
  · intro retVal hExact
    unfold emptyMemory at hExact
    unfold evalTerminator
    simp [evalCallTerminator, resolveCallTarget, isDirectExactDivTarget, extractCalleeDefPath?,
      extractCalleeTypeArgs, findCallee?, resolveCalleeBodyAndArgs?, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, lookupCallee, hStr, operandIsSigned, operandTy,
      placeTy, hExact, writePlaceValue, set?]
  · intro hUb
    unfold emptyMemory at hUb
    unfold evalTerminator
    simp [evalCallTerminator, resolveCallTarget, isDirectExactDivTarget, extractCalleeDefPath?,
      extractCalleeTypeArgs, findCallee?, resolveCalleeBodyAndArgs?, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, lookupCallee, hStr, operandIsSigned, operandTy,
      placeTy, hUb]

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
  · simp [evalRvalue, evalOperand, get?, readProjectedValue, isThinRawPtrTy]
  · simp [evalRvalue, evalOperand, get?, readProjectedValue]
  · simp [evalRvalue, evalFnPtrToPtr, evalOperand, get?, readProjectedValue,
      isThinRawPtrTy, emptyMemory, lookupBorrow, isFnPtrAllocId, fnPtrAllocBase]

/--
Universal characterization of `checkCalleeSig`, `PointerCoercion::ClosureFnPointer`,
`PointerCoercion::UnsafeFnPointer`, and `safetyCompatible` in `evalRvalue` and
`fnEntryCompatibleWithCallSite`:
1. Reifying a function item when `checkCalleeSig mem.callees defPath sigInputs sigOut sigAbi typeArgs = false`
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
    (checkCalleeSig mem.callees defPath sigInputs sigOut sigAbi typeArgs mem.traitImpls = false →
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
   - If `lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs s.memory.traitImpls = .some calleeBody` and
     `checkCalleeTargetCompatible` holds, `TerminatorKind.call` pushes a
     `SavedCallerFrame` and enters `calleeBody` at block `0` via `pushCalleeFrame`,
     and `TerminatorKind.tailCall` enters `calleeBody` at block `0` via
     `enterTailCalleeFrame`.
   - If `lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs s.memory.traitImpls = .none`, `TerminatorKind.call`
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
      lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs s.memory.traitImpls = .some calleeBody →
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
      lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs s.memory.traitImpls = .none →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs, args := argVals, memory := s.memory }
          (resumeExternalCall s (locals' argVals) destination targetBb unwind) ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs, args := argVals, memory := s.memory }
          (resumeExternalDivergingCall s (locals' argVals) unwind) ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs, args := argVals, memory := s.memory }
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
      lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs s.memory.traitImpls = .some calleeBody →
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
      simp only [evalTerminator, evalCallTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        hNoDirect, hEvalFunc, hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFind,
        hCompatBody, Nat.beq_refl, Bool.and_self] <;> rfl
  · intro hLookup hCompatSite hArgs hFindNone
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, evalCallTerminator, evalTailCallTerminator, bodyLocalDeclsOf, isDirectExactDivTarget, resolveCallTarget,
        hNoDirect, hEvalFunc, hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFindNone,
        Nat.beq_refl, Bool.and_self] <;> rfl
  · intro hLookupNone
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, evalCallTerminator, evalTailCallTerminator, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookupNone, Nat.beq_refl, Bool.and_self] <;> rfl
  · intro hLookup hCompatFalse
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, evalCallTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookup, hCompatFalse, Nat.beq_refl, Bool.and_self] <;> rfl
  · intro hLookup hCompatSite hArgs hFind hCompatBodyFalse
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, evalCallTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFind, hCompatBodyFalse,
        Nat.beq_refl, Bool.and_self] <;> rfl

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
      simp [evalTerminator, evalCallTerminator, evalTailCallTerminator, resolveCallTarget, hNoDirect, hEvalFunc, hNonZero, Nat.beq]
  · intro hOffsetZero hBorrow
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [evalTerminator, evalCallTerminator, evalTailCallTerminator, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hBorrow]

/-! ## 4. End-to-End Theorems for Polymorphic Calls and Trait Methods -/

/-- Concrete `u32` layout computed by `RigidTy.computeLayout` on 64-bit targets. -/
private def polyU32Layout : TypeLayout :=
  { size := ⟨4⟩
    align := ⟨4⟩
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Concrete `u64` / `usize` layout computed by `RigidTy.computeLayout` on 64-bit targets. -/
private def polyU64Layout : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨8⟩
    backendRepr := .scalar (.initialized (.int 64 false) ⟨0, 18446744073709551615⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Body statement `_0 = copy _1` for `polyIdCallee`. -/
private def polyIdAssignStmt : Statement :=
  { kind := .assign ⟨0, .nil⟩ (.use (.copy ⟨1, .nil⟩)), span := "id" }

/-- Polymorphic identity callee `fn id<T>(x: T) -> T` (`typeParamCount = 1`). -/
private def polyIdCallee : CapturedMir :=
  { defPath := "test::id"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 1
    localDecls :=
      [ { mutability := .mut, ty := { kind := .param 0 "T", layoutIdx := 0 }, debugName := .none },
        { mutability := .not, ty := { kind := .param 0 "T", layoutIdx := 0 }, debugName := .some "x" } ]
    basicBlocks :=
      [ { statements := [polyIdAssignStmt]
          terminator := { kind := .return_, span := "id" }
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := polyU32Layout, mode := .direct }]
        ret := { layout := polyU32Layout, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := emptyLayoutTable
    allocations := .nil
    typeParamCount := 1
    genericParams := [{ idx := 0, name := "T" }]
    traitImpls := .nil }

/-- Monomorphic identity callee `fn mono_id(x: u32) -> u32` (`typeParamCount = 0`). -/
private def monoIdCallee : CapturedMir :=
  { polyIdCallee with
    defPath := "test::mono_id"
    localDecls :=
      [ { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := .none },
        { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := .some "x" } ]
    typeParamCount := 0
    genericParams := .nil }

/-- Polymorphic trait-impl body `impl<T> MyTrait for Range<T>` (`typeParamCount = 1`). -/
private def rangeTraitImplCallee : CapturedMir :=
  { polyIdCallee with
    defPath := "test::<impl MyTrait<T> for Range<T>>::check" }

/-- Two-parameter trait-impl body `impl<A, B> BiTrait<B> for Wrapper<A>` (`typeParamCount = 2`). -/
private def biTraitImplCallee : CapturedMir :=
  { polyIdCallee with
    defPath := "test::<impl BiTrait<B> for Wrapper<A>>::combine"
    argCount := 2
    localDecls :=
      [ { mutability := .mut, ty := { kind := .param 0 "A", layoutIdx := 0 }, debugName := .none },
        { mutability := .not, ty := { kind := .param 0 "A", layoutIdx := 0 }, debugName := .some "a" },
        { mutability := .not, ty := { kind := .param 1 "B", layoutIdx := 0 }, debugName := .some "b" } ]
    typeParamCount := 2
    genericParams := [{ idx := 0, name := "A" }, { idx := 1, name := "B" }] }

theorem mir_evalTerminator_direct_generic_function_call
    (s : MachineState)
    (func : Operand)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (callerBody instCallee : CapturedMir)
    (hExtractDef : extractCalleeDefPath? func = .some defPath)
    (hExtractArgs : extractCalleeTypeArgs func = typeArgs)
    (hArgs :
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals')
    (hLookup :
      lookupCallee s.memory.callees callerBody.layouts defPath typeArgs s.memory.traitImpls =
        .some instCallee) :
    let callerInitLocals : List LocalSlot :=
      [ .uninit,
        .init (.scalar ⟨42, 4⟩),
        .uninit,
        .init (.scalar ⟨99, 8⟩),
        .uninit ]
    let callerState0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := callerInitLocals }
        memory := { emptyMemory with callees := [polyIdCallee] } }
    let callU32Op : Operand :=
      .constant { ty := { kind := .fnDef "test::id" [.uint .u32], layoutIdx := 0 }, val := .zeroSized }
    let callU64Op : Operand :=
      .constant { ty := { kind := .fnDef "test::id" [.uint .u64], layoutIdx := 0 }, val := .zeroSized }
    let instU32 := polyIdCallee.instantiate [(.uint .u32, polyU32Layout)]
    let instU64 := polyIdCallee.instantiate [(.uint .u64, polyU64Layout)]
    let sCallee32 :=
      pushCalleeFrame callerState0 monoIdCallee callerInitLocals ⟨2, .nil⟩ 1 instU32 [.scalar ⟨42, 4⟩]
    let sCallee32AfterStmt :=
      advanceStmt sCallee32 [.init (.scalar ⟨42, 4⟩), .init (.scalar ⟨42, 4⟩)] sCallee32.memory
    let localsAfter32 : List LocalSlot :=
      [ .uninit,
        .init (.scalar ⟨42, 4⟩),
        .init (.scalar ⟨42, 4⟩),
        .init (.scalar ⟨99, 8⟩),
        .uninit ]
    let callerState1 : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := 0, locals := localsAfter32 }
        memory :=
          { emptyMemory with
            callees := [polyIdCallee]
            activeCallee := .some monoIdCallee } }
    let sCallee64 :=
      pushCalleeFrame callerState1 monoIdCallee localsAfter32 ⟨4, .nil⟩ 2 instU64 [.scalar ⟨99, 8⟩]
    let sCallee64AfterStmt :=
      advanceStmt sCallee64 [.init (.scalar ⟨99, 8⟩), .init (.scalar ⟨99, 8⟩)] sCallee64.memory
    let localsAfter64 : List LocalSlot :=
      [ .uninit,
        .init (.scalar ⟨42, 4⟩),
        .init (.scalar ⟨42, 4⟩),
        .init (.scalar ⟨99, 8⟩),
        .init (.scalar ⟨99, 8⟩) ]
    let callerState2 : MachineState :=
      { frame := { blockIdx := 2, stmtIdx := 0, locals := localsAfter64 }
        memory :=
          { emptyMemory with
            callees := [polyIdCallee]
            activeCallee := .some monoIdCallee } }
    (evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
      MirStepNode.step
        (pushCalleeFrame s callerBody locals' destination targetBb instCallee argVals unwind) ∧
     evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
      MirStepNode.step (enterTailCalleeFrame s.memory instCallee argVals)) ∧
    lookupCallee [polyIdCallee] emptyLayoutTable "test::id" [.uint .u32] .nil =
      .some instU32 ∧
    lookupCallee [polyIdCallee] emptyLayoutTable "test::id" [.uint .u64] .nil =
      .some instU64 ∧
    instU32.typeParamCount = 0 ∧
    instU32.localDecls =
      [ { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := .none },
        { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := .some "x" } ] ∧
    evalTerminator
        callerState0
        ⟨.call callU32Op [.copy ⟨1, .nil⟩] ⟨2, .nil⟩ (.some 1) .continue_, "call_u32"⟩
        (.some monoIdCallee) =
      MirStepNode.step sCallee32 ∧
    evalStmt sCallee32 polyIdAssignStmt = MirStepNode.step sCallee32AfterStmt ∧
    evalTerminator sCallee32AfterStmt ⟨.return_, "id"⟩ (.some instU32) =
      MirStepNode.step callerState1 ∧
    get? callerState1.frame.locals 2 = .some (.init (.scalar ⟨42, 4⟩)) ∧
    evalTerminator
        callerState1
        ⟨.call callU64Op [.copy ⟨3, .nil⟩] ⟨4, .nil⟩ (.some 2) .continue_, "call_u64"⟩
        (.some monoIdCallee) =
      MirStepNode.step sCallee64 ∧
    evalStmt sCallee64 polyIdAssignStmt = MirStepNode.step sCallee64AfterStmt ∧
    evalTerminator sCallee64AfterStmt ⟨.return_, "id"⟩ (.some instU64) =
      MirStepNode.step callerState2 ∧
    get? callerState2.frame.locals 2 = .some (.init (.scalar ⟨42, 4⟩)) ∧
    get? callerState2.frame.locals 4 = .some (.init (.scalar ⟨99, 8⟩)) ∧
    lookupCallee [polyIdCallee] emptyLayoutTable "test::id" .nil .nil = .none ∧
    lookupCallee [polyIdCallee] emptyLayoutTable "test::id" [.uint .u32, .uint .u64] .nil = .none ∧
    lookupCallee [monoIdCallee] emptyLayoutTable "test::mono_id" [.uint .u32] .nil = .none := by
  dsimp only
  refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [evalTerminator, evalCallTerminator, resolveCallTarget, checkCalleeTargetCompatible,
      hExtractDef, hExtractArgs, hArgs, hLookup]
  · simp [evalTerminator, evalTailCallTerminator, resolveCallTarget, checkCalleeTargetCompatible,
      hExtractDef, hExtractArgs, hArgs, hLookup]

theorem mir_evalTerminator_trait_method_dispatch
    (s : MachineState) :
    let monoImplEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::MyTrait::compute"
            args := [.uint .u32] }
        implPath := "test::mono_id" }
    let rangeImplEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::MyTrait::check"
            args := [.adt "Range" [.param 0 "T"], .param 0 "T"] }
        implPath := "test::<impl MyTrait<T> for Range<T>>::check" }
    let diagImplEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::PairTrait::eq_pair"
            args := [.adt "Pair" [.param 0 "T", .param 0 "T"]] }
        implPath := "test::<impl MyTrait<T> for Range<T>>::check" }
    let outOfOrderEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::BiTrait::combine"
            args := [.param 1 "B", .adt "Wrapper" [.param 0 "A"]] }
        implPath := "test::<impl BiTrait<B> for Wrapper<A>>::combine" }
    let methodGenericEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::Convert::convert"
            args := [.adt "Wrapper" [.param 0 "A"]] }
        implPath := "test::<impl BiTrait<B> for Wrapper<A>>::combine" }
    let callerLayoutsWithT : LayoutTable :=
      { emptyLayoutTable with entries := [polyU32Layout] }
    let calleeWithTraitImpl : CapturedMir :=
      { rangeTraitImplCallee with traitImpls := [rangeImplEntry] }
    let defaultCheckCallee : CapturedMir :=
      { polyIdCallee with defPath := "test::MyTrait::check" }
    let badArityRangeCallee : CapturedMir :=
      { rangeTraitImplCallee with typeParamCount := 2 }
    let blanketComputeEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::MyTrait::compute"
            args := [.param 0 "T"] }
        implPath := "test::id" }
    let leftPairEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::PairTrait::eq_pair"
            args := [.adt "Pair" [.param 0 "T", .uint .u32]] }
        implPath := "test::id" }
    let rightPairEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::PairTrait::eq_pair"
            args := [.adt "Pair" [.uint .u32, .param 0 "T"]] }
        implPath := "test::<impl MyTrait<T> for Range<T>>::check" }
    lookupCallee [monoIdCallee] emptyLayoutTable
      "test::MyTrait::compute" [.uint .u32] [monoImplEntry] =
      .some monoIdCallee ∧
    lookupCallee [polyIdCallee, monoIdCallee] emptyLayoutTable
      "test::MyTrait::compute" [.uint .u32] [blanketComputeEntry, monoImplEntry] =
      .some monoIdCallee ∧
    lookupCallee [polyIdCallee, monoIdCallee] emptyLayoutTable
      "test::MyTrait::compute" [.uint .u32] [monoImplEntry, blanketComputeEntry] =
      .some monoIdCallee ∧
    lookupCallee [polyIdCallee, monoIdCallee] emptyLayoutTable
      "test::MyTrait::compute" [.uint .u32] [blanketComputeEntry, monoImplEntry, monoImplEntry] =
      .some monoIdCallee ∧
    lookupCallee [polyIdCallee, rangeTraitImplCallee] emptyLayoutTable
      "test::PairTrait::eq_pair" [.adt "Pair" [.uint .u32, .uint .u32]] [leftPairEntry, rightPairEntry] =
      .none ∧
    lookupCallee [polyIdCallee, rangeTraitImplCallee] emptyLayoutTable
      "test::PairTrait::eq_pair" [.adt "Pair" [.uint .u32, .uint .u32]] [rightPairEntry, leftPairEntry] =
      .none ∧
    lookupCallee [rangeTraitImplCallee] emptyLayoutTable
      "test::MyTrait::check" [.adt "Range" [.uint .usize], .uint .usize] [rangeImplEntry] =
      .some (rangeTraitImplCallee.instantiate [(.uint .usize, polyU64Layout)]) ∧
    lookupCallee [defaultCheckCallee, rangeTraitImplCallee] emptyLayoutTable
      "test::MyTrait::check" [.adt "Range" [.uint .usize], .uint .usize] [rangeImplEntry] =
      .some (rangeTraitImplCallee.instantiate [(.uint .usize, polyU64Layout)]) ∧
    lookupCallee [defaultCheckCallee] emptyLayoutTable
      "test::MyTrait::check" [.adt "Range" [.uint .usize], .uint .usize] [rangeImplEntry] =
      .none ∧
    lookupCallee [defaultCheckCallee, badArityRangeCallee] emptyLayoutTable
      "test::MyTrait::check" [.adt "Range" [.uint .usize], .uint .usize] [rangeImplEntry] =
      .none ∧
    lookupCallee [defaultCheckCallee, rangeTraitImplCallee] emptyLayoutTable
      "test::MyTrait::check" [.uint .u32] [rangeImplEntry] =
      .some (defaultCheckCallee.instantiate [(.uint .u32, polyU32Layout)]) ∧
    lookupCallee [calleeWithTraitImpl] emptyLayoutTable
      "test::MyTrait::check" [.adt "Range" [.uint .usize], .uint .usize] .nil =
      .some (calleeWithTraitImpl.instantiate [(.uint .usize, polyU64Layout)]) ∧
    lookupCallee [rangeTraitImplCallee] emptyLayoutTable
      "test::PairTrait::eq_pair" [.adt "Pair" [.uint .u32, .uint .u32]] [diagImplEntry] =
      .some (rangeTraitImplCallee.instantiate [(.uint .u32, polyU32Layout)]) ∧
    lookupCallee [rangeTraitImplCallee] emptyLayoutTable
      "test::PairTrait::eq_pair" [.adt "Pair" [.uint .u32, .uint .u64]] [diagImplEntry] =
      .none ∧
    lookupCallee [biTraitImplCallee] emptyLayoutTable
      "test::BiTrait::combine" [.uint .u64, .adt "Wrapper" [.uint .u32]] [outOfOrderEntry] =
      .some (biTraitImplCallee.instantiate [(.uint .u32, polyU32Layout), (.uint .u64, polyU64Layout)]) ∧
    lookupCallee [biTraitImplCallee] emptyLayoutTable
      "test::Convert::convert" [.adt "Wrapper" [.uint .u32], .uint .u64] [methodGenericEntry] =
      .some (biTraitImplCallee.instantiate [(.uint .u32, polyU32Layout), (.uint .u64, polyU64Layout)]) ∧
    lookupCallee [biTraitImplCallee] emptyLayoutTable
      "test::Convert::convert" [.adt "Wrapper" [.uint .u32], .uint .u64, .uint .u32] [methodGenericEntry] =
      .none ∧
    lookupCallee [polyIdCallee] callerLayoutsWithT
      "test::id" [.adt "Wrapper" [.param 0 "T"]] .nil =
      .some (polyIdCallee.instantiate
        [(.adt "Wrapper" [.param 0 "T"], { polyU32Layout with fields := .arbitrary [⟨0⟩] [0] })]) ∧
    lookupCallee [polyIdCallee] emptyLayoutTable
      "test::id" [.adt "Wrapper" [.param 0 "T"]] .nil =
      .none ∧
    lookupCallee [polyIdCallee] emptyLayoutTable
      "test::id" [.ref .not (.param 0 "T")] .nil =
      .none ∧
    lookupCallee [polyIdCallee] emptyLayoutTable
      "test::id" [.rawPtr .not (.param 0 "T")] .nil =
      .none ∧
    lookupCallee [polyIdCallee] emptyLayoutTable
      "test::id" [.fnPtr [.param 0 "T"] (.uint .u32) .safe .rust] .nil =
      .none ∧
    lookupCallee [polyIdCallee] emptyLayoutTable
      "test::id" [.fnDef "f" [.param 0 "T"]] .nil =
      .none ∧
    matchRigidTy (.fnPtr [.param 0 "T"] (.param 0 "T") .safe .rust)
      (.fnPtr [.uint .u32] (.uint .u32) .safe .rust) .nil =
      .some [(0, .uint .u32)] ∧
    matchRigidTy (.alias "Proj" [.param 0 "T"])
      (.alias "Proj" [.uint .u32]) .nil =
      .some [(0, .uint .u32)] ∧
    s.frame.blockIdx = s.frame.blockIdx := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mir_evalTerminator_inherited_default_and_subject_traitImpls_dispatch :
    let blanketDescribeEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::Describe::describe"
            args := [.param 0 "T"] }
        implPath := "test::id" }
    let u32InheritsDefaultEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::Describe::describe"
            args := [.uint .u32] }
        implPath := "test::Describe::describe" }
    let defaultDescribeCallee : CapturedMir :=
      { polyIdCallee with defPath := "test::Describe::describe" }
    let monoImplEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::MyTrait::compute"
            args := [.uint .u32] }
        implPath := "test::mono_id" }
    let defaultComputeCallee : CapturedMir :=
      { polyIdCallee with defPath := "test::MyTrait::compute" }
    let computeU32Op : Operand :=
      .constant
        { ty := { kind := .fnDef "test::MyTrait::compute" [.uint .u32], layoutIdx := 0 }
          val := .zeroSized }
    let callComputeTerm : Terminator :=
      ⟨.call computeU32Op [.copy ⟨1, .nil⟩] ⟨0, .nil⟩ (.some 1) .continue_, "call_compute"⟩
    let subjectBody : CapturedMir :=
      { monoIdCallee with
        defPath := "test::subject"
        basicBlocks :=
          [ { statements := .nil, terminator := callComputeTerm, isCleanup := false },
            { statements := .nil, terminator := { kind := .return_, span := "subject" }, isCleanup := false } ]
        traitImpls := [monoImplEntry] }
    let s0 : MachineState :=
      initMachineStateWithCallees subjectBody [.scalar ⟨42, 4⟩] [defaultComputeCallee, monoIdCallee]
    let rangeImplEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::MyTrait::check"
            args := [.adt "Range" [.param 0 "T"], .param 0 "T"] }
        implPath := "test::<impl MyTrait<T> for Range<T>>::check" }
    let instRangeImplEntry : TraitImplEntry :=
      rangeImplEntry.instantiate [(.uint .usize, polyU64Layout)]
    lookupCallee [defaultDescribeCallee, polyIdCallee] emptyLayoutTable
      "test::Describe::describe" [.uint .u32] [blanketDescribeEntry, u32InheritsDefaultEntry] =
      .some (defaultDescribeCallee.instantiate [(.uint .u32, polyU32Layout)]) ∧
    lookupCallee [defaultDescribeCallee, polyIdCallee] emptyLayoutTable
      "test::Describe::describe" [.uint .u32] [u32InheritsDefaultEntry, blanketDescribeEntry] =
      .some (defaultDescribeCallee.instantiate [(.uint .u32, polyU32Layout)]) ∧
    lookupCallee [defaultDescribeCallee, polyIdCallee] emptyLayoutTable
      "test::Describe::describe" [.uint .u64] [blanketDescribeEntry, u32InheritsDefaultEntry] =
      .some (polyIdCallee.instantiate [(.uint .u64, polyU64Layout)]) ∧
    lookupCallee [defaultDescribeCallee, polyIdCallee] emptyLayoutTable
      "test::Describe::describe" [.uint .u32] [blanketDescribeEntry] =
      .some (polyIdCallee.instantiate [(.uint .u32, polyU32Layout)]) ∧
    lookupCallee [polyIdCallee] emptyLayoutTable
      "test::Describe::describe" [.uint .u32] [blanketDescribeEntry, u32InheritsDefaultEntry] =
      .none ∧
    lookupCallee [rangeTraitImplCallee] emptyLayoutTable
      "test::MyTrait::check" [.adt "Range" [.uint .usize], .uint .usize]
      [instRangeImplEntry, rangeImplEntry] =
      .some (rangeTraitImplCallee.instantiate [(.uint .usize, polyU64Layout)]) ∧
    s0.memory.traitImpls = [monoImplEntry] ∧
    stepMirFn subjectBody s0 =
      MirStepNode.step
        (pushCalleeFrame s0 subjectBody s0.frame.locals ⟨0, .nil⟩ 1 monoIdCallee [.scalar ⟨42, 4⟩]) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mir_evalTerminator_uninstantiated_trait_method_extCall
    (s : MachineState)
    (func : Operand)
    (traitMethodDefPath : DefPath)
    (paramIdx : Nat)
    (paramName : String)
    (restTypeArgs : List RigidTy)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (callerBody : CapturedMir)
    (hExtractDef : extractCalleeDefPath? func = .some traitMethodDefPath)
    (hExtractArgs : extractCalleeTypeArgs func = .param paramIdx paramName :: restTypeArgs)
    (hNotInCallees : findCallee? s.memory.callees traitMethodDefPath = .none)
    (hNotExactDiv : stringEq traitMethodDefPath "core::intrinsics::exact_div" = false)
    (hArgs :
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals') :
    let typeArgs := .param paramIdx paramName :: restTypeArgs
    let defaultCheckCallee : CapturedMir :=
      { polyIdCallee with defPath := "test::MyTrait::check" }
    let rangeImplEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::MyTrait::check"
            args := [.adt "Range" [.param 0 "T"], .param 0 "T"] }
        implPath := "test::<impl MyTrait<T> for Range<T>>::check" }
    let callerLayoutsWithT : LayoutTable :=
      { emptyLayoutTable with entries := [polyU32Layout] }
    lookupCallee s.memory.callees callerBody.layouts traitMethodDefPath typeArgs s.memory.traitImpls = .none ∧
    evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
      MirStepNode.extCall
        { defPath := traitMethodDefPath, typeArgs := typeArgs, args := argVals, memory := s.memory }
        (resumeExternalCall s locals' destination targetBb unwind) ∧
    evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
      MirStepNode.extCall
        { defPath := traitMethodDefPath, typeArgs := typeArgs, args := argVals, memory := s.memory }
        resumeExternalTailCall ∧
    lookupCallee [monoIdCallee] emptyLayoutTable
      "test::MyTrait::check" [.adt "Wrapper" [.param 0 "T"]] .nil = .none ∧
    lookupCallee [defaultCheckCallee, rangeTraitImplCallee] callerLayoutsWithT
      "test::MyTrait::check" [.param 0 "Self"] [rangeImplEntry] = .none ∧
    lookupCallee [defaultCheckCallee, rangeTraitImplCallee] callerLayoutsWithT
      "test::MyTrait::check" [.adt "Wrapper" [.param 0 "T"]] [rangeImplEntry] = .none := by
  dsimp only
  have hLookupNone :
      lookupCallee s.memory.callees callerBody.layouts traitMethodDefPath
        (.param paramIdx paramName :: restTypeArgs) s.memory.traitImpls = .none := by
    simp [lookupCallee, resolveCalleeBodyAndArgs?, hNotInCallees]
  refine ⟨hLookupNone, ?_, ?_, rfl, rfl, rfl⟩
  · simp [evalTerminator, evalCallTerminator, resolveCallTarget, isDirectExactDivTarget,
      hExtractDef, hExtractArgs, hArgs, hLookupNone, hNotExactDiv]
  · simp [evalTerminator, evalTailCallTerminator, resolveCallTarget,
      hExtractDef, hExtractArgs, hArgs, hLookupNone]

theorem mir_evalTerminator_indirect_polymorphic_fnptr_call
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (argVals : List Value)
    (localsAfterFunc locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (callerBody : CapturedMir)
    (ptrVal : ProvenancePtr)
    (hNoDirect : extractCalleeDefPath? func = .none)
    (hEvalFunc :
      evalOperand
        s.frame.locals
        func
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok (.ptr ptrVal 8) localsAfterFunc)
    (hOffsetZero : ptrVal.offsetBytes = 0)
    (hNoBorrow : lookupBorrow s.memory.borrows ptrVal.tag = .none)
    (hArgs :
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals')
    (hArgOpsLen : length argOps = 1)
    (hArgValsLen : length argVals = 1) :
    let instU32Callee := polyIdCallee.instantiate [(.uint .u32, polyU32Layout)]
    let u32FnSig : RigidTy := .fnPtr [.uint .u32] (.uint .u32) .safe .rust
    let u64FnSig : RigidTy := .fnPtr [.uint .u64] (.uint .u64) .safe .rust
    let usizeFnSig : RigidTy := .fnPtr [.uint .usize] (.uint .usize) .safe .rust
    let idU32Op : Operand :=
      .constant { ty := { kind := .fnDef "test::id" [.uint .u32], layoutIdx := 0 }, val := .zeroSized }
    let idUnboundParamOp : Operand :=
      .constant { ty := { kind := .fnDef "test::id" [.param 0 "T"], layoutIdx := 0 }, val := .zeroSized }
    let traitCheckOp : Operand :=
      .constant
        { ty :=
            { kind := .fnDef "test::MyTrait::check" [.adt "Range" [.uint .usize], .uint .usize]
              layoutIdx := 0 }
          val := .zeroSized }
    let rangeImplEntry : TraitImplEntry :=
      { traitRef :=
          { defPath := "test::MyTrait::check"
            args := [.adt "Range" [.param 0 "T"], .param 0 "T"] }
        implPath := "test::<impl MyTrait<T> for Range<T>>::check" }
    let memWithPolyCallee : Memory := { emptyMemory with callees := [polyIdCallee] }
    let memWithTraitCallee : Memory :=
      { emptyMemory with callees := [rangeTraitImplCallee], traitImpls := [rangeImplEntry] }
    let expectedPolyEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := "test::id"
        typeArgs := [.uint .u32]
        fnSig := .some u32FnSig }
    let expectedTraitEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := "test::MyTrait::check"
        typeArgs := [.adt "Range" [.uint .usize], .uint .usize]
        fnSig := .some usizeFnSig }
    let goodTarget : ResolvedCallTarget :=
      { defPath := "test::id"
        typeArgs := [.uint .u32]
        fnSig := .some u32FnSig
        isIndirect := true }
    let badTarget : ResolvedCallTarget :=
      { defPath := "test::id"
        typeArgs := [.uint .u32]
        fnSig := .some u64FnSig
        isIndirect := true }
    checkCalleeSig [polyIdCallee] "test::id" [.uint .u32] (.uint .u32) .rust [.uint .u32] = true ∧
    checkCalleeSig [polyIdCallee] "test::id" [.uint .u64] (.uint .u64) .rust [.uint .u32] = false ∧
    checkCalleeSig [polyIdCallee] "test::id" [.uint .u32] (.uint .u32) .rust .nil = false ∧
    checkCalleeSig [monoIdCallee] "test::mono_id" [.uint .u32] (.uint .u32) .rust [.uint .u32] = false ∧
    checkCalleeSig [rangeTraitImplCallee] "test::MyTrait::check" [.uint .usize] (.uint .usize) .rust
      [.adt "Range" [.uint .usize], .uint .usize] [rangeImplEntry] = true ∧
    checkCalleeSig [rangeTraitImplCallee] "test::MyTrait::check" [.uint .u32] (.uint .u32) .rust
      [.adt "Range" [.uint .usize], .uint .usize] [rangeImplEntry] = false ∧
    evalRvalue
        .nil
        (.cast (.pointerCoercion "ReifyFnPointer") idU32Op { kind := u32FnSig, layoutIdx := 0 })
        memWithPolyCallee =
      .ok
        (.ptr { allocId := fnPtrAllocBase, offsetBytes := 0 } 8)
        .nil
        { memWithPolyCallee with fnPtrs := [expectedPolyEntry] } ∧
    evalRvalue
        .nil
        (.cast (.pointerCoercion "ReifyFnPointer") idU32Op { kind := u64FnSig, layoutIdx := 0 })
        memWithPolyCallee =
      .ub ∧
    evalRvalue
        .nil
        (.cast (.pointerCoercion "ReifyFnPointer") idUnboundParamOp { kind := u32FnSig, layoutIdx := 0 })
        memWithPolyCallee =
      .ub ∧
    evalRvalue
        .nil
        (.cast (.pointerCoercion "ReifyFnPointer") traitCheckOp { kind := usizeFnSig, layoutIdx := 0 })
        memWithTraitCallee =
      .ok
        (.ptr { allocId := fnPtrAllocBase, offsetBytes := 0 } 8)
        .nil
        { memWithTraitCallee with fnPtrs := [expectedTraitEntry] } ∧
    evalRvalue
        .nil
        (.cast (.pointerCoercion "ReifyFnPointer") traitCheckOp { kind := u32FnSig, layoutIdx := 0 })
        memWithTraitCallee =
      .ub ∧
    checkCalleeTargetCompatible goodTarget instU32Callee 1 = true ∧
    checkCalleeTargetCompatible badTarget instU32Callee 1 = false ∧
    (∀ fnEntry : FnPtrEntry,
      lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntry.defPath = "test::id" →
      fnEntry.typeArgs = [.uint .u32] →
      fnEntry.fnSig = .some u64FnSig →
      fnEntryCompatibleWithCallSite fnEntry 1 (operandTy callerBody.localDecls callerBody.layouts func) = true →
      lookupCallee s.memory.callees callerBody.layouts "test::id" [.uint .u32] s.memory.traitImpls =
        .some instU32Callee →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) := by
  dsimp only
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro fnEntry hLookupPtr hDef hTypeArgs hSig hCompatSite hLookupCallee
  have hCompatBodyFalse :
      checkCalleeTargetCompatible
        { defPath := "test::id"
          typeArgs := [.uint .u32]
          fnSig := .some (.fnPtr [.uint .u64] (.uint .u64) .safe .rust)
          isIndirect := true }
        (polyIdCallee.instantiate [(.uint .u32, polyU32Layout)])
        1 = false := rfl
  refine ⟨?_, ?_⟩
  · simp only [evalTerminator, evalCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      hNoDirect, hEvalFunc, hOffsetZero, hNoBorrow, hLookupPtr, hArgOpsLen, hCompatSite,
      hArgs, hDef, hTypeArgs, hSig, hArgValsLen, hLookupCallee, hCompatBodyFalse,
      Nat.beq_refl, Bool.and_self]
  · simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
      hNoDirect, hEvalFunc, hOffsetZero, hNoBorrow, hLookupPtr, hArgOpsLen, hCompatSite,
      hArgs, hDef, hTypeArgs, hSig, hArgValsLen, hLookupCallee, hCompatBodyFalse,
      Nat.beq_refl, Bool.and_self]

/-! ## 5. Diverging Calls (`target = .none`) and Unwind Cleanup Terminators (`BRIEF-1.2`) -/

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
      lookupCallee s.memory.callees callerBody.layouts "core::hint::unreachable_unchecked" (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
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
      lookupCallee s.memory.callees callerBody.layouts "core::intrinsics::unreachable" (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
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
      lookupCallee s.memory.callees callerBody.layouts target.defPath target.typeArgs s.memory.traitImpls = .none →
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals' →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
          (resumeExternalDivergingCall s locals' unwind)) := by
  have hUnreach1 : isUnreachableCallTarget "core::hint::unreachable_unchecked" = true := by decide
  have hUnreach2 : isUnreachableCallTarget "core::intrinsics::unreachable" = true := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hResolveUb
    simp only [evalTerminator, evalCallTerminator, bodyLocalDeclsOf, hResolveUb]
  · intro target localsAfterFunc hResolveOk hArgsUb
    simp only [evalTerminator, evalCallTerminator, bodyLocalDeclsOf, hResolveOk, hArgsUb]
  · intro argVals locals' hFunc hFind hArgsOk
    simp only [evalTerminator, evalCallTerminator, resolveCallTarget, hFunc, hArgsOk, hFind, hUnreach1]
  · intro argVals locals' hFunc hFind hArgsOk
    simp only [evalTerminator, evalCallTerminator, resolveCallTarget, hFunc, hArgsOk, hFind, hUnreach2]
  · intro target localsAfterFunc argVals locals' hResolveOk hIndirect hFind hArgsOk
    simp only [evalTerminator, evalCallTerminator, bodyLocalDeclsOf, hResolveOk, hArgsOk, hFind, hIndirect]

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
    (hFind : lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .some calleeBody) :
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
  · simp only [evalTerminator, evalCallTerminator, resolveCallTarget, hFunc, hArgs, hFind,
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
    simp only [evalTerminator, evalCallTerminator, lookupCallee, resolveCalleeBodyAndArgs?,
      resolveCallTarget, extractCalleeDefPath?, extractCalleeTypeArgs, hArgs, hFindNone,
      hNotUnreach, hAbort]
  · intro p hp hFindNone
    have hpFlags :
        isUnreachableCallTarget p = false ∧
        isAbortingPanicDefPath p = false ∧
        isUnwindingPanicDefPath p = true := by
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rcases hpFlags with ⟨hNotUnreach, hNotAbort, hUnwindPanic⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hRoot
      simp only [evalTerminator, evalCallTerminator, lookupCallee, resolveCalleeBodyAndArgs?,
        resolveCallTarget, extractCalleeDefPath?, extractCalleeTypeArgs, hArgs, hNotUnreach,
        hFindNone, hNotAbort, hUnwindPanic, applyUnwindAction, hRoot, unwindFromCallStack]
    · intro hStack hCallerUnwind
      simp only [evalTerminator, evalCallTerminator, lookupCallee, resolveCalleeBodyAndArgs?,
        resolveCallTarget, extractCalleeDefPath?, extractCalleeTypeArgs, hArgs, hNotUnreach,
        hFindNone, hNotAbort, hUnwindPanic, applyUnwindAction, hStack, unwindFromCallStack,
        hCallerUnwind]
    · simp only [evalTerminator, evalCallTerminator, lookupCallee, resolveCalleeBodyAndArgs?,
        resolveCallTarget, extractCalleeDefPath?, extractCalleeTypeArgs, hArgs, hNotUnreach,
        hFindNone, hNotAbort, hUnwindPanic, applyUnwindAction]
    · simp only [evalTerminator, evalCallTerminator, lookupCallee, resolveCalleeBodyAndArgs?,
        resolveCallTarget, extractCalleeDefPath?, extractCalleeTypeArgs, hArgs, hNotUnreach,
        hFindNone, hNotAbort, hUnwindPanic, applyUnwindAction]
    · simp only [evalTerminator, evalCallTerminator, lookupCallee, resolveCalleeBodyAndArgs?,
        resolveCallTarget, extractCalleeDefPath?, extractCalleeTypeArgs, hArgs, hNotUnreach,
        hFindNone, hNotAbort, hUnwindPanic, applyUnwindAction]

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
    (hFindNone : lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .none)
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
        { defPath := defPath, typeArgs := extractCalleeTypeArgs func, args := argVals, memory := s.memory }
        (resumeExternalDivergingCall s locals' unwind)) ∧
    (∀ (retVal : Value) (memAfter : Memory),
      resumeExternalDivergingCall s locals' unwind (.returned retVal memAfter) = .faulted .ub) ∧
    (∀ (memAfter : Memory),
      resumeExternalDivergingCall s locals' unwind (.panicked memAfter) =
        applyUnwindAction s locals' memAfter unwind) ∧
    (resumeExternalDivergingCall s locals' unwind .aborted = .halted .abort) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [evalTerminator, evalCallTerminator, resolveCallTarget, hFunc, hArgs,
      hNotUnreach, hFindNone, hNotAbort, hNotPanic]
  · intro retVal memAfter
    rfl
  · intro memAfter
    rfl
  · rfl

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
    (lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      isUnreachableCallTarget defPath = true →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      isUnreachableCallTarget defPath = false →
      isAbortingPanicDefPath defPath = true →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.retOutcome .abort) ∧
    (lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      isUnreachableCallTarget defPath = false →
      isAbortingPanicDefPath defPath = false →
      isUnwindingPanicDefPath defPath = true →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        match applyUnwindAction s locals' s.memory unwind with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) ∧
    (lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      isUnreachableCallTarget defPath = false →
      isAbortingPanicDefPath defPath = false →
      isUnwindingPanicDefPath defPath = false →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := defPath, typeArgs := extractCalleeTypeArgs func, args := argVals, memory := s.memory }
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
    simp only [evalTerminator, evalCallTerminator, resolveCallTarget, hFunc, hArgs, hFindNone, hUnreach]
  · intro hFindNone hNotUnreach hAbort
    simp only [evalTerminator, evalCallTerminator, resolveCallTarget, hFunc, hArgs, hFindNone, hNotUnreach, hAbort]
  · intro hFindNone hNotUnreach hNotAbort hPanic
    simp only [evalTerminator, evalCallTerminator, resolveCallTarget, hFunc, hArgs, hFindNone,
      hNotUnreach, hNotAbort, hPanic]
    cases applyUnwindAction s locals' s.memory unwind <;> rfl
  · intro hFindNone hNotUnreach hNotAbort hNotPanic
    simp only [evalTerminator, evalCallTerminator, resolveCallTarget, hFunc, hArgs, hFindNone,
      hNotUnreach, hNotAbort, hNotPanic]
  · refine ⟨rfl, ?_, ?_, rfl⟩
    · simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack, restoreCallerProtectors]
    · intro hNil
      simp [evalTerminator, unwindFromCallStack, hNil]

end Correspondence.V2026_08_01.L5_ControlAndCalls
