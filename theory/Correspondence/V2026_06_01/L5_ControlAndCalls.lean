import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators
import MiniRust.LibSpecr
import MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
import Correspondence.Framework
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses

namespace Correspondence.V2026_06_01.L5_ControlAndCalls

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr
open MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
open Correspondence

/-!
Horizontal Correspondence Slice L5: Control Flow, Terminators, and Procedure Calls
(`Trusted.Rustc.V2026_06_01.MirSemantics.Statements` and
`Trusted.Rustc.V2026_06_01.MirSemantics.Terminators` vs. mechanically extracted
`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops`).

Every theorem in this module universally quantifies (`∀`) over real Anneal TCB
machine states, statements, terminators, and call stacks and proves exact
equational correspondence against the mechanically generated MiniRust operational
definitions in `MiniRust.Snapshots.S2026_05_Matched.Generated.Ops`
(`spec/lang/machine.md` and `spec/lang/step/terminators.md`).
-/

/-- Project an Anneal `StackFrame`'s program-counter coordinates (`blockIdx` and
`stmtIdx`) into MiniRust's mechanically extracted `MrStackFrame` record
(`spec/lang/machine.md:30-34`). -/
def toMrStackFrame (frame : StackFrame) : MrStackFrame :=
  { blockIdx := frame.blockIdx, stmtIdx := frame.stmtIdx }

/-! ## 1. Statement Program Counter & Local Lifecycle Correspondence -/

/-- Universal correspondence between Anneal's `advanceStmt` helper
(`Statements.lean:36-38`) and MiniRust's statement program-counter increment
`Generated.Ops.mrAdvanceStmtPc` (`spec/lang/machine.md:185-223`):
`advanceStmt s locals' mem'` increments `s.frame.stmtIdx` by `1` while
preserving `blockIdx`, updating `locals` to `locals'`, and updating `memory` to
`mem'`. -/
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
(`Statements.lean:774-776`): `.nop`, `.coverage`, and `.constEvalCounter` step
deterministically to `advanceStmt s s.frame.locals` with `stmtIdx` incremented
according to `Generated.Ops.mrAdvanceStmtPc`. -/
theorem mir_evalStmt_nop_coverage_constEvalCounter
    (s : MachineState) (span : String) :
    evalStmt s ⟨.nop, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    evalStmt s ⟨.coverage, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    evalStmt s ⟨.constEvalCounter, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    (advanceStmt s s.frame.locals).frame.stmtIdx = mrAdvanceStmtPc s.frame.stmtIdx := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Universal characterization of `StatementKind.placeMention`
(`Statements.lean:783-787` vs. `spec/lang/step/statements.md`): mentioning an
out-of-bounds or `.dead` local faults with `MirStepNode.fail .ub`, whereas
mentioning a live (`.uninit` or `.init`) local advances the statement program
counter without mutating locals or memory. -/
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
`StatementKind.storageDead`, and protected-tag write conflict checking in
`evalStmt` (`Statements.lean:821-941`):
1. `.storageLive loc` transitions an in-bounds slot to `.uninit` (or faults with
   `.ub` if `loc` is out of bounds);
2. `.storageDead loc` transitions an in-bounds slot to `.dead` (or faults with
   `.ub` if `loc` is out of bounds); and
3. Writing to a root local when `hasProtectedWriteConflict` is `true` faults
   immediately with `MirStepNode.fail .ub`. -/
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

/-! ## 2. Terminator Dispatch, Unwinding, and Call-Stack Correspondence -/

/-- Universal proof by structural induction on `branches : List (Nat × BasicBlockIdx)`
that Anneal's `lookupSwitchTarget` (`Terminators.lean:31-38`) is identical to
MiniRust's mechanically extracted `Generated.Ops.mrLookupSwitchTarget`
(`spec/lang/step/terminators.md:38-45`) for all `val`, `branches`, and `otherwise`. -/
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

/-- Reflexivity of `listByteEq` over arbitrary byte sequences (`State.lean:557`). -/
theorem listByteEq_refl (xs : List UInt8) : listByteEq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp [listByteEq, Nat.beq_refl, ih]

/-- Reflexivity of `stringEq` over arbitrary `String` values (`State.lean:568`). -/
theorem stringEq_refl (s : String) : stringEq s s = true :=
  listByteEq_refl s.toByteArray.data.toList

/-- Universal proof by induction on `callees : List CapturedMir` that Anneal's
`findCallee?` (`Terminators.lean:43-49`) returns the first captured MIR body
whose `defPath` matches `defPath`, corresponding to MiniRust's callee table
lookup `Generated.Ops.mrFindCalleeById` (`spec/lang/machine.md:321-337`). -/
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

/-- Universal characterization of `applyUnwindAction` (`Terminators.lean:85-96`)
across all four `UnwindAction` constructors (`.unreachable`, `.terminate`,
`.continue_`, `.cleanup bb`), paired with the corresponding outcomes of
MiniRust's mechanically extracted `Generated.Ops.mrApplyUnwindAction`
(`spec/lang/step/terminators.md:385-455`). -/
theorem mir_applyUnwindAction_characterization
    (s : MachineState) (localsAfter : List LocalSlot) (memAfter : Memory)
    (bb : BasicBlockIdx) :
    (applyUnwindAction s localsAfter memAfter .unreachable = .faulted .ub ∧
      mrApplyUnwindAction none false true = .faultUb) ∧
    (applyUnwindAction s localsAfter memAfter .terminate = .halted .abort ∧
      mrApplyUnwindAction none true false = .abort) ∧
    (applyUnwindAction s localsAfter memAfter .continue_ = .halted .panic ∧
      mrApplyUnwindAction none false false = .panic) ∧
    (applyUnwindAction s localsAfter memAfter (.cleanup bb) =
      .running
        { frame := { s.frame with blockIdx := bb, stmtIdx := 0, locals := localsAfter }
          memory := memAfter } ∧
      mrApplyUnwindAction (some bb) false false = .cleanup bb ∧
      toMrStackFrame { s.frame with blockIdx := bb, stmtIdx := 0, locals := localsAfter } =
        MrStackFrame.jump_to_block (toMrStackFrame s.frame) bb) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Universal correspondence for `TerminatorKind.goto` (`Terminators.lean:231-235`
vs. `Generated.Ops.MrStackFrame.jump_to_block` at `spec/lang/step/terminators.md:20-30`):
`evalTerminator s ⟨.goto target, span⟩ currentBody` jumps to `target` with
`stmtIdx := 0`, matching `MrStackFrame.jump_to_block`. -/
theorem mir_evalTerminator_goto_corresponds
    (s : MachineState) (target : BasicBlockIdx) (span : String)
    (currentBody : Option CapturedMir) :
    evalTerminator s ⟨.goto target, span⟩ currentBody =
      MirStepNode.step { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } } ∧
    toMrStackFrame { s.frame with blockIdx := target, stmtIdx := 0 } =
      MrStackFrame.jump_to_block (toMrStackFrame s.frame) target := by
  exact ⟨rfl, rfl⟩

/-- Universal correspondence for `TerminatorKind.unreachable`
(`Terminators.lean:271` vs. `spec/lang/step/terminators.md:53-56`): reaching an
`.unreachable` terminator immediately faults with `MirStepNode.fail .ub`. -/
theorem mir_evalTerminator_unreachable_is_ub
    (s : MachineState) (span : String) (currentBody : Option CapturedMir) :
    evalTerminator s ⟨.unreachable, span⟩ currentBody = MirStepNode.fail .ub := by
  rfl

/-- Universal characterization of `TerminatorKind.return_` (`Terminators.lean:236-270`
vs. `spec/lang/step/terminators.md:323-373`) across both root-frame return
(`callStack = []`, corresponding to `StackPopAction.BottomOfStack`) and
interprocedural caller-frame return (`callStack = caller :: restStack`,
corresponding to `StackPopAction.BackToCaller` and `MrStackFrame.jump_to_block`),
as well as faulting with `MirStepNode.fail .ub` when `_0` is `.uninit` or `.dead`. -/
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
    (get? s.frame.locals 0 = .some .uninit →
      evalTerminator s ⟨.return_, span⟩ currentBody = MirStepNode.fail .ub) ∧
    (get? s.frame.locals 0 = .some .dead →
      evalTerminator s ⟨.return_, span⟩ currentBody = MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro retVal hRet hStack
    simp [evalTerminator, hRet, hStack]
  · intro retVal caller restStack updatedCallerLocals hRet hStack hProt hWrite
    refine ⟨?_, rfl⟩
    simp [evalTerminator, hRet, hStack, hProt, hWrite]
  · intro hUninit
    simp [evalTerminator, hUninit]
  · intro hDead
    simp [evalTerminator, hDead]

/-- Universal characterization of `TerminatorKind.assert` (`Terminators.lean:407-432`):
when `cond` evaluates to scalar `sc`, matching `expectedBit` jumps to `target`
via `MrStackFrame.jump_to_block`, whereas mismatching `expectedBit` dispatches
`applyUnwindAction s locals' s.memory unwind`. -/
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

/-- Universal characterization of `TerminatorKind.call` (`Terminators.lean:298-353`
vs. `spec/lang/step/terminators.md:179-289`):
1. Calling `"core::hint::unreachable_unchecked"` with `target = .none` immediately
   faults with `MirStepNode.fail .ub`; and
2. Calling a transparent callee `calleeBody` found via `findCallee?` pushes a
   `SavedCallerFrame` onto `s.memory.callStack` and initializes the new frame at
   `blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals`. -/
theorem mir_evalTerminator_call_transparent_and_unreachable_unchecked
    (s : MachineState) (func : Operand) (argOps : List Operand)
    (destination : Place) (unwind : UnwindAction) (span : String)
    (currentBody : Option CapturedMir) :
    (extractCalleeDefPath? func = .some "core::hint::unreachable_unchecked" →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ currentBody =
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
          calleeProtectors := s.memory.activeProtectors }
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
  refine ⟨?_, ?_⟩
  · intro hUnreach
    have hStr : stringEq "core::hint::unreachable_unchecked" "core::hint::unreachable_unchecked" = true := by decide
    simp [evalTerminator, evalCallTerminator, resolveCallTarget, hUnreach, hStr]
  · intro defPath targetBb calleeBody callerBody argVals locals' hFunc hCurr hArgs hFind
    dsimp only
    subst hCurr
    simp [evalTerminator, evalCallTerminator, hFunc, hArgs, hFind]

/-- Universal correspondence of `TerminatorKind.switchInt` (`Terminators.lean:387-406`
vs. `Generated.Ops.mrLookupSwitchTarget` at `spec/lang/step/terminators.md:32-49`):
when `evalOperand` evaluates `discr` to `.ok (.scalar sc) locals'`, `evalTerminator`
branches to `Generated.Ops.mrLookupSwitchTarget sc.bits targets.branches targets.otherwise`
with `stmtIdx := 0` (`MrStackFrame.jump_to_block`), and when `evalOperand` returns
`.ub`, `evalTerminator` faults with `MirStepNode.fail .ub`. -/
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
          (pushCalleeFrame s callerBody (locals' argVals) destination targetBb calleeBody argVals) ∧
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
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs, args := argVals, memory := s.memory }
          resumeExternalTailCall) ∧
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .none →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps) callerFuncTyOpt = false →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
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
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hLookup hCompatSite hArgs hFind hCompatBody
    refine ⟨?_, ?_⟩ <;>
      simp only [evalTerminator, evalCallTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        hNoDirect, hEvalFunc, hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFind,
        hCompatBody, Nat.beq_refl, Bool.and_self] <;> rfl
  · intro hLookup hCompatSite hArgs hFindNone
    refine ⟨?_, ?_⟩ <;>
      simp only [evalTerminator, evalCallTerminator, evalTailCallTerminator, bodyLocalDeclsOf, isDirectExactDivTarget, resolveCallTarget,
        hNoDirect, hEvalFunc, hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFindNone,
        Nat.beq_refl, Bool.and_self] <;> rfl
  · intro hLookupNone
    refine ⟨?_, ?_⟩ <;>
      simp only [evalTerminator, evalCallTerminator, evalTailCallTerminator, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookupNone, Nat.beq_refl, Bool.and_self] <;> rfl
  · intro hLookup hCompatFalse
    refine ⟨?_, ?_⟩ <;>
      simp only [evalTerminator, evalCallTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookup, hCompatFalse, Nat.beq_refl, Bool.and_self] <;> rfl
  · intro hLookup hCompatSite hArgs hFind hCompatBodyFalse
    refine ⟨?_, ?_⟩ <;>
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
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (ptrVal.offsetBytes = 0 →
      lookupBorrow s.memory.borrows ptrVal.tag = .some bEntry →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) := by
  refine ⟨?_, ?_⟩
  · intro hNonZero
    refine ⟨?_, ?_⟩ <;>
      simp [evalTerminator, evalCallTerminator, evalTailCallTerminator, resolveCallTarget, hNoDirect, hEvalFunc, hNonZero, Nat.beq]
  · intro hOffsetZero hBorrow
    refine ⟨?_, ?_⟩ <;>
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
      [ { statements := []
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

/--
End-to-end characterization of direct polymorphic function calls (`.call` and
`.tailCall`) and `typeArgs` arity checking in `lookupCallee`:
1. Universal `.call` and `.tailCall` stepping when `lookupCallee` instantiates a
   polymorphic callee `polyCallee` with `typeArgs`;
2. Concrete instantiation of `polyIdCallee` (`id<T>`) at `typeArgs = [.uint .u32]`
   produces a monomorphized body (`typeParamCount = 0`) whose return and argument
   locals have `kind = .uint .u32`; and
3. Arity mismatches (calling `id<T>` with `[]` or `[u32, u64]`, or calling
   monomorphic `monoIdCallee` with `[u32]`) cleanly return `lookupCallee = .none`.
-/
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
    (evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
      MirStepNode.step
        (pushCalleeFrame s callerBody locals' destination targetBb instCallee argVals) ∧
     evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
      MirStepNode.step (enterTailCalleeFrame s.memory instCallee argVals)) ∧
    lookupCallee [polyIdCallee] emptyLayoutTable "test::id" [.uint .u32] .nil =
      .some (polyIdCallee.instantiate [(.uint .u32, polyU32Layout)]) ∧
    (polyIdCallee.instantiate [(.uint .u32, polyU32Layout)]).typeParamCount = 0 ∧
    (polyIdCallee.instantiate [(.uint .u32, polyU32Layout)]).localDecls =
      [ { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := .none },
        { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := .some "x" } ] ∧
    lookupCallee [polyIdCallee] emptyLayoutTable "test::id" .nil .nil = .none ∧
    lookupCallee [polyIdCallee] emptyLayoutTable "test::id" [.uint .u32, .uint .u64] .nil = .none ∧
    lookupCallee [monoIdCallee] emptyLayoutTable "test::mono_id" [.uint .u32] .nil = .none := by
  refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [evalTerminator, evalCallTerminator, resolveCallTarget, checkCalleeTargetCompatible,
      hExtractDef, hExtractArgs, hArgs, hLookup]
  · simp [evalTerminator, evalTailCallTerminator, resolveCallTarget, checkCalleeTargetCompatible,
      hExtractDef, hExtractArgs, hArgs, hLookup]

/--
End-to-end characterization of concrete trait-method resolution and pattern
matching in `lookupCallee`:
1. Concrete `Self` (`Range<usize>`) dispatches `(traitMethodDefPath, typeArgs)`
   to the matching `TraitImplEntry` (both via `s.memory.traitImpls` and via
   `c.traitImpls` on a body in `callees`) and instantiates its generic parameter;
2. Diagonal trait implementations (`impl<T> PairTrait for Pair<T, T>`) accept
   matching `Pair<u32, u32>` and reject mismatched `Pair<u32, u64>`;
3. Out-of-order and nested generic parameters (`[.param 1 "B", .adt "Wrapper" [.param 0 "A"]]`)
   are extracted in canonical parameter index order `[0, 1]`;
4. Trait methods with method-level generic parameters (`Convert::convert`)
   match `entry.traitRef.args` as a prefix of `typeArgs` and append trailing
   method-level type arguments when their total count matches `c.typeParamCount`;
5. `resolveLayouts` resolves compound type arguments containing `RigidTy.param`
   (such as `Wrapper<T>`) against `callerLayouts` when `T` is in `callerLayouts`; and
6. `matchRigidTy` structurally matches `.fnPtr` and `.alias` patterns.
-/
theorem mir_evalTerminator_trait_method_dispatch
    (s : MachineState) :
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
    lookupCallee [rangeTraitImplCallee] emptyLayoutTable
      "test::MyTrait::check" [.adt "Range" [.uint .usize], .uint .usize] [rangeImplEntry] =
      .some (rangeTraitImplCallee.instantiate [(.uint .usize, polyU64Layout)]) ∧
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
    matchRigidTy (.fnPtr [.param 0 "T"] (.param 0 "T") .safe .rust)
      (.fnPtr [.uint .u32] (.uint .u32) .safe .rust) .nil =
      .some [(0, .uint .u32)] ∧
    matchRigidTy (.alias "Proj" [.param 0 "T"])
      (.alias "Proj" [.uint .u32]) .nil =
      .some [(0, .uint .u32)] ∧
    s.frame.blockIdx = s.frame.blockIdx := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Universal theorem that when `Self` in a trait-method call `(traitMethodDefPath, typeArgs)`
is an uninstantiated `RigidTy.param paramIdx paramName` (`typeArgs = .param paramIdx paramName :: restArgs`),
`lookupCallee` returns `.none` (even when `s.memory.traitImpls` or `s.memory.callees`
contain trait implementations) and both `TerminatorKind.call` and `TerminatorKind.tailCall`
step to `MirStepNode.extCall` carrying `typeArgs` in `MirCallReq`. Also verifies
that a compound `Self` containing a nested `.param` returns `.none` when no
generic implementation matches.
-/
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
      "test::MyTrait::check" [.adt "Wrapper" [.param 0 "T"]] .nil = .none := by
  dsimp only
  have hLookupNone :
      lookupCallee s.memory.callees callerBody.layouts traitMethodDefPath
        (.param paramIdx paramName :: restTypeArgs) s.memory.traitImpls = .none := by
    simp [lookupCallee, hNotInCallees]
  refine ⟨hLookupNone, ?_, ?_, rfl⟩
  · simp [evalTerminator, evalCallTerminator, resolveCallTarget, isDirectExactDivTarget,
      hExtractDef, hExtractArgs, hArgs, hLookupNone, hNotExactDiv]
  · simp [evalTerminator, evalTailCallTerminator, resolveCallTarget,
      hExtractDef, hExtractArgs, hArgs, hLookupNone]

/--
End-to-end characterization of indirect `FnPtr` calls (`TerminatorKind.call` and
`TerminatorKind.tailCall`) to polymorphic functions and trait methods:
1. When an indirect `FnPtrEntry` targets `polyIdCallee` (`id<T>`) with
   `typeArgs = [.uint .u32]` and compatible signature `fn(u32) -> u32`,
   `lookupCallee` instantiates `polyIdCallee` to `u32`, `checkCalleeTargetCompatible`
   succeeds (`true`), and both `.call` and `.tailCall` step into the instantiated
   `calleeBody`;
2. When an indirect `FnPtrEntry` targets `polyIdCallee` with `typeArgs = [.uint .u32]`
   (instantiating to `fn(u32) -> u32`) but carries a mismatched signature
   `fn(u64) -> u64`, `checkCalleeTargetCompatible` rejects the instantiated
   callee (`false`) and both `.call` and `.tailCall` fault with `MirStepNode.fail .ub`.
-/
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
    let goodTarget : ResolvedCallTarget :=
      { defPath := "test::id"
        typeArgs := [.uint .u32]
        fnSig := .some (.fnPtr [.uint .u32] (.uint .u32) .safe .rust)
        isIndirect := true }
    let badTarget : ResolvedCallTarget :=
      { defPath := "test::id"
        typeArgs := [.uint .u32]
        fnSig := .some (.fnPtr [.uint .u64] (.uint .u64) .safe .rust)
        isIndirect := true }
    checkCalleeTargetCompatible goodTarget instU32Callee 1 = true ∧
    checkCalleeTargetCompatible badTarget instU32Callee 1 = false ∧
    (∀ fnEntry : FnPtrEntry,
      lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntry.defPath = "test::id" →
      fnEntry.typeArgs = [.uint .u32] →
      fnEntry.fnSig = .some (.fnPtr [.uint .u64] (.uint .u64) .safe .rust) →
      fnEntryCompatibleWithCallSite fnEntry 1 (operandTy callerBody.localDecls callerBody.layouts func) = true →
      lookupCallee s.memory.callees callerBody.layouts "test::id" [.uint .u32] s.memory.traitImpls =
        .some instU32Callee →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) := by
  dsimp only
  refine ⟨rfl, rfl, ?_⟩
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

end Correspondence.V2026_06_01.L5_ControlAndCalls
