import Trusted
import Anneal
import Mir.WireframeDemo.checksum_frame_safe
import Specs.WireframeDemo.checksum_frame_safe
import Obligations.WireframeDemo.checksum_frame_safe

namespace Proof.WireframeDemo.checksum_frame_safe

set_option linter.all false
set_option maxRecDepth 200000
set_option maxHeartbeats 200000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.ITreeWP
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.checksum_frame_safe

/-!
Kernel-checked stateful proof for `wireframe_demo::checksum_frame_safe`
(Journey 4 baseline).

Proves across all `256^8 = 2^64` 8-byte `&[u8; 8]` frames that the four-iteration
`while i < 4` loop executes all eight array bounds checks without panic or
Undefined Behavior, leaves `Memory` unmodified, and returns
`bigEndianWordSum4 b0 b1 b2 b3 b4 b5 b6 b7`.
-/

private structure Hold (P : Prop) : Prop where
  val : P

private structure BlockCtx where
  localDecls : List LocalDecl
  layouts : LayoutTable
  body : CapturedMir

private theorem get?_append_cons {α : Type u} (pfx rest : List α) (x : α) :
    get? (pfx ++ (x :: rest)) (length pfx) = some x := by
  simp [get?, length]

private theorem get?_length_none {α : Type u} (xs : List α) :
    get? xs (length xs) = none := by
  simp [get?, length]

private theorem length_append_singleton {α : Type u} (pfx : List α) (x : α) :
    length (pfx ++ [x]) = Nat.add (length pfx) 1 := by
  simp [length]

private theorem scalarModulus_1 : scalarModulus 1 = 256 := rfl
private theorem scalarModulus_2 : scalarModulus 2 = 65536 := rfl
private theorem scalarModulus_4 : scalarModulus 4 = 4294967296 := rfl
private theorem scalarModulus_8 : scalarModulus 8 = 18446744073709551616 := rfl
private theorem mul_1_8 : Nat.mul 1 8 = 8 := rfl
private theorem mul_2_8 : Nat.mul 2 8 = 16 := rfl
private theorem mul_4_8 : Nat.mul 4 8 = 32 := rfl
private theorem mul_8_8 : Nat.mul 8 8 = 64 := rfl
private theorem mul_0_2 : Nat.mul 0 2 = 0 := rfl
private theorem mul_1_2 : Nat.mul 1 2 = 2 := rfl
private theorem mul_2_2 : Nat.mul 2 2 = 4 := rfl
private theorem mul_3_2 : Nat.mul 3 2 = 6 := rfl

private theorem wrap8_0 : wrapScalarBits 0 18446744073709551616 = 0 := rfl
private theorem wrap8_1 : wrapScalarBits 1 18446744073709551616 = 1 := rfl
private theorem wrap8_2 : wrapScalarBits 2 18446744073709551616 = 2 := rfl
private theorem wrap8_3 : wrapScalarBits 3 18446744073709551616 = 3 := rfl
private theorem wrap8_4 : wrapScalarBits 4 18446744073709551616 = 4 := rfl
private theorem wrap8_5 : wrapScalarBits 5 18446744073709551616 = 5 := rfl
private theorem wrap8_6 : wrapScalarBits 6 18446744073709551616 = 6 := rfl
private theorem wrap8_7 : wrapScalarBits 7 18446744073709551616 = 7 := rfl
private theorem wrap4_8 : wrapScalarBits 8 4294967296 = 8 := rfl

private theorem get?_frame8CallerLocals (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    get? (frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7) frame8SlotIdx =
      some (.init (frame8Value b0 b1 b2 b3 b4 b5 b6 b7)) := rfl

private theorem get?Internal_frame8CallerLocals (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    List.get?Internal (frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7) 69 =
      some (.init (frame8Value b0 b1 b2 b3 b4 b5 b6 b7)) := rfl

private theorem readProjectedValue_nil (locals : List LocalSlot) (v : Value) :
    readProjectedValue locals v [] = .ok v := rfl

private theorem readProjectedValue_field
    (locals : List LocalSlot) (vIdx : Nat) (fields : List Value)
    (idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    readProjectedValue locals (.aggregate vIdx fields) (.field idx ty :: rest) =
      match get? fields idx with
      | .some fieldVal => readProjectedValue locals fieldVal rest
      | .none => .ub := rfl

private theorem readProjectedValue_index
    (locals : List LocalSlot) (fields : List Value)
    (idxLocal : Local) (rest : List ProjectionElem) :
    readProjectedValue locals (.aggregate 0 fields) (.index idxLocal :: rest) =
      match get? locals idxLocal with
      | .some (.init (.scalar sc)) =>
        match get? fields sc.bits with
        | .some elemVal => readProjectedValue locals elemVal rest
        | .none => .ub
      | _ => .ub := rfl

private theorem isBorrowProtected_nil (entry : BorrowEntry) :
    isBorrowProtected .nil entry = false := by
  unfold isBorrowProtected
  cases entry.protector <;> rfl

private theorem hasProtectedWriteConflict_nil
    (borrows : List BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat) :
    hasProtectedWriteConflict borrows .nil targetLocal writerTag writeProj writeRangeOff writeRangeLen = false := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    unfold hasProtectedWriteConflict
    rw [isBorrowProtected_nil]
    dsimp only [Bool.and]
    cases Nat.beq entry.targetLocal targetLocal <;>
      cases borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen <;>
      exact ih

private def evalOperandFallback (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) : PlaceReadResult :=
  evalOperand locals op borrows globals layouts callerLocals

private def evalDerefGlobalFallback
    (globals : List CapturedAllocation) (ptrVal : ProvenancePtr) (sz : Nat)
    (locals : List LocalSlot) (restProj : List ProjectionElem) : PlaceReadResult :=
  match lookupGlobalAlloc globals ptrVal.allocId with
  | .some alloc =>
    match readGlobalScalar alloc ptrVal.offsetBytes sz with
    | .some sc =>
      match readProjectedValue locals (.scalar sc) restProj with
      | .ok fieldVal => .ok fieldVal locals
      | .ub => .ub
      | .unsupported => .unsupported
    | .none => .ub
  | .none => .ub

private def evalOperandFast (ctx : BlockCtx) (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) : PlaceReadResult :=
  match op with
  | .constant c =>
    match c.val with
    | .indirect _ _ => evalOperandFallback locals (.constant c) borrows globals ctx.layouts callerLocals
    | .slice _ _ => evalOperandFallback locals (.constant c) borrows globals ctx.layouts callerLocals
    | cv =>
      match evalConstValue cv with
      | .some v => .ok v locals
      | .none => .unsupported
  | .copy p =>
    match p.projection with
    | .deref :: restProj =>
      match get? locals p.local_ with
      | .some (.init (.ptr ptrVal sz)) =>
        match lookupBorrow borrows ptrVal.tag with
        | .some entry =>
          match entry.perm with
          | .disabled => .ub
          | _ =>
            match get? locals entry.targetLocal with
            | .some (.init targetRootVal) =>
              let fullProj :=
                match entry.targetProjection with
                | .nil => restProj
                | ph :: pt => ph :: appendProjections pt restProj
              match readProjectedValue locals targetRootVal fullProj with
              | .ok fieldVal => .ok fieldVal locals
              | .ub => .ub
              | .unsupported => .unsupported
            | .some _ => .ub
            | .none =>
              match get? callerLocals entry.targetLocal with
              | .some (.init targetRootVal) =>
                let fullProj :=
                  match entry.targetProjection with
                  | .nil => restProj
                  | ph :: pt => ph :: appendProjections pt restProj
                match readProjectedValue locals targetRootVal fullProj with
                | .ok fieldVal => .ok fieldVal locals
                | .ub => .ub
                | .unsupported => .unsupported
              | _ => .ub
        | .none => evalDerefGlobalFallback globals ptrVal sz locals restProj
      | _ => .ub
    | _ =>
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue locals rootVal p.projection with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
  | .move p =>
    match p.projection with
    | .nil =>
      match get? locals p.local_ with
      | .some (.init v) =>
        match set? locals p.local_ .uninit with
        | .some locals' => .ok v locals'
        | .none => .ub
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
    | .field idx ty :: rest =>
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue locals rootVal (.field idx ty :: rest) with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
    | _ => evalOperandFallback locals (.move p) borrows globals ctx.layouts callerLocals

private theorem evalOperandFast_eq (ctx : BlockCtx) (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) :
    evalOperandFast ctx locals op borrows globals callerLocals =
      evalOperand locals op borrows globals ctx.layouts callerLocals := by
  cases op with
  | constant c =>
    rcases c with ⟨ty, val⟩
    cases val with
    | scalar _ => rfl
    | zeroSized => rfl
    | slice sc _ => cases sc <;> rfl
    | indirect _ _ => rfl
    | unevaluated => rfl
  | copy p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil => rfl
    | cons hd _ => cases hd <;> rfl
  | move p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil => rfl
    | cons hd _ => cases hd <;> rfl

private def evalRvalueFallback (locals : List LocalSlot) (rv : Rvalue)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) : RvalueEvalResult :=
  evalRvalue locals rv mem localDecls layouts

private def evalRvalueFast
    (ctx : BlockCtx) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    RvalueEvalResult :=
  match rv with
  | .use op =>
    match evalOperandFast ctx locals op mem.borrows mem.globals mem.callerLocals with
    | .ok v locals' => .ok v locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast ck op targetTy =>
    match ck with
    | .intToInt =>
      match evalOperandFast ctx locals op mem.borrows mem.globals mem.callerLocals with
      | .ok (.scalar sc) locals' =>
        match Nat.beq sc.sizeBytes 0 with
        | true => .unsupported
        | false =>
          match intCastTargetBytes targetTy.kind with
          | .some targetBytes =>
            let modulus := scalarModulus targetBytes
            let castedBits :=
              match operandIsSigned ctx.localDecls op ctx.layouts with
              | false => wrapScalarBits sc.bits modulus
              | true =>
                match Nat.ble targetBytes sc.sizeBytes with
                | true => wrapScalarBits sc.bits modulus
                | false => signExtendBits sc.bits sc.sizeBytes targetBytes
            .ok (.scalar ⟨castedBits, targetBytes⟩) locals' mem
          | .none => .unsupported
      | .ok _ _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | _ => evalRvalueFallback locals (.cast ck op targetTy) mem ctx.localDecls ctx.layouts
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandFast ctx locals lhsOp mem.borrows mem.globals mem.callerLocals with
    | .ok lhsVal locals₁ =>
      match evalOperandFast ctx locals₁ rhsOp mem.borrows mem.globals mem.callerLocals with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          let isSigned := operandIsSigned ctx.localDecls lhsOp ctx.layouts
          evalScalarBinOp op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            .ok (.ptr { ptrVal with offsetBytes := Nat.add ptrVal.offsetBytes offsetSc.bits } sz) locals₂ mem
          | _ => .unsupported
        | _, _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .unaryOp uop op =>
    match uop with
    | .not =>
      match evalOperandFast ctx locals op mem.borrows mem.globals mem.callerLocals with
      | .ok (.scalar sc) locals' =>
        evalUnaryNot sc (operandTy ctx.localDecls ctx.layouts op) locals' mem
      | .ok _ _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | _ => evalRvalueFallback locals (.unaryOp uop op) mem ctx.localDecls ctx.layouts
  | _ => evalRvalueFallback locals rv mem ctx.localDecls ctx.layouts

private theorem evalRvalueFast_eq
    (ctx : BlockCtx) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    evalRvalueFast ctx locals rv mem =
      evalRvalue locals rv mem ctx.localDecls ctx.layouts := by
  cases rv with
  | use op =>
    dsimp only [evalRvalueFast, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals op mem.borrows mem.globals ctx.layouts mem.callerLocals <;> rfl
  | cast ck op targetTy =>
    cases ck with
    | intToInt =>
      dsimp only [evalRvalueFast, evalRvalue]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals ctx.layouts mem.callerLocals with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | _ => rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueFast, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals lhsOp mem.borrows mem.globals ctx.layouts mem.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [evalOperandFast_eq]
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals ctx.layouts mem.callerLocals <;> rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalueFast, evalRvalue]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals ctx.layouts mem.callerLocals with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | neg => rfl
    | ptrMetadata => rfl
  | _ => rfl

private def finishAssignStmtNodeFast
    (s : MachineState) (dst : Place) : RvalueEvalResult → MirStepNode
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok val locals₁ mem₁ =>
    match dst.projection with
    | .nil =>
      match get? locals₁ dst.local_ with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? locals₁ dst.local_ (.init val) with
        | .some locals₂ =>
          match hasProtectedWriteConflict mem₁.borrows mem₁.activeProtectors dst.local_ .none .nil with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' := invalidateConflictingBorrows mem₁.borrows dst.local_ .none
            MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | _ => finishAssignStmtNode s dst (.ok val locals₁ mem₁)

private theorem finishAssignStmtNodeFast_eq
    (s : MachineState) (dst : Place) (res : RvalueEvalResult) :
    finishAssignStmtNodeFast s dst res = finishAssignStmtNode s dst res := by
  cases res with
  | ub => rfl
  | unsupported => rfl
  | ok val locals₁ mem₁ =>
    rcases dst with ⟨loc, proj⟩
    cases proj with
    | nil =>
      dsimp only [finishAssignStmtNodeFast, finishAssignStmtNode]
      cases get? locals₁ loc with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | uninit =>
          dsimp only
          cases set? locals₁ loc (.init val) with
          | none => rfl
          | some locals₂ =>
            cases mem₁.activeProtectors with
            | nil =>
              dsimp only
              rw [hasProtectedWriteConflict_nil]
            | cons _ _ => rfl
        | init _ =>
          dsimp only
          cases set? locals₁ loc (.init val) with
          | none => rfl
          | some locals₂ =>
            cases mem₁.activeProtectors with
            | nil =>
              dsimp only
              rw [hasProtectedWriteConflict_nil]
            | cons _ _ => rfl
    | cons _ _ => rfl

private def evalStmtFallback (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  evalStmt s stmt localDecls layouts

private def evalStmtFast
    (ctx : BlockCtx) (s : MachineState) (stmt : Statement) : MirStepNode :=
  match stmt.kind with
  | .assign dst rv =>
    finishAssignStmtNodeFast s dst
      (evalRvalueFast ctx s.frame.locals rv s.memory)
  | .storageLive loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .uninit with
      | .some locals' => MirStepNode.step (advanceStmt s locals')
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .storageDead loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .dead with
      | .some locals' => MirStepNode.step (advanceStmt s locals')
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .nop => MirStepNode.step (advanceStmt s s.frame.locals)
  | _ => evalStmtFallback s stmt ctx.localDecls ctx.layouts

private theorem evalStmtFast_eq
    (ctx : BlockCtx) (s : MachineState) (stmt : Statement) :
    evalStmtFast ctx s stmt =
      evalStmt s stmt ctx.localDecls ctx.layouts := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    show finishAssignStmtNodeFast s dst (evalRvalueFast ctx s.frame.locals rv s.memory) = _
    rw [finishAssignStmtNodeFast_eq, evalRvalueFast_eq]
    dsimp only [finishAssignStmtNode, evalStmt]
    cases evalRvalue s.frame.locals rv s.memory ctx.localDecls ctx.layouts <;> rfl
  | _ => rfl

private def lookupBlock (ctx : BlockCtx) (idx : Nat) : Option BasicBlockData :=
  get? ctx.body.basicBlocks idx

private inductive CfgExecState where
  | running
      (ok : Bool)
      (cur : Option (Nat × Nat × List Statement × Terminator))
      (s : MachineState)
  | halted (ok : Bool) (out : MirOutcome)
  | faulted

private def cfgOk : CfgExecState → Bool
  | .running ok _ _ => ok
  | .halted ok _ => ok
  | .faulted => false

private def cfgStateWP (post : MirOutcome → Prop) : CfgExecState → Prop
  | .halted ok out => ok = true ∧ post out
  | _ => False

private def stepNodeToCfg
    (ok : Bool)
    (nextCur : Option (Nat × Nat × List Statement × Terminator)) :
    MirStepNode → CfgExecState
  | .ret out => .halted ok out
  | .tau (.running s') => .running ok nextCur s'
  | .tau (.halted out) => .halted ok out
  | .tau (.faulted _) => .faulted
  | .vis (.inr (.inl _)) k =>
    match k PUnit.unit with
    | .running s' => .running ok nextCur s'
    | .halted out => .halted ok out
    | .faulted _ => .faulted
  | .vis _ _ => .faulted

private def evalTerminatorCfg
    (ctx : BlockCtx) (ok : Bool) (s : MachineState)
    (term : Terminator) : CfgExecState :=
  match term.kind with
  | .goto target =>
    .running ok .none { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } }
  | .return_ =>
    match s.memory.callStack with
    | .nil =>
      match get? s.frame.locals 0 with
      | .some (.init retVal) => .halted ok (.normal (retVal, s.memory))
      | _ => .faulted
    | _ :: _ => .faulted
  | .switchInt discr targets =>
    match evalOperandFast ctx s.frame.locals discr s.memory.borrows s.memory.globals s.memory.callerLocals with
    | .ok (.scalar sc) locals' =>
      let target := lookupSwitchTarget sc.bits targets.branches targets.otherwise
      .running ok .none { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }
    | _ => .faulted
  | .assert cond expected target _ =>
    match evalOperandFast ctx s.frame.locals cond s.memory.borrows s.memory.globals s.memory.callerLocals with
    | .ok (.scalar sc) locals' =>
      let expectedBit := match expected with | true => 1 | false => 0
      .running (Bool.and ok (Nat.beq sc.bits expectedBit)) .none
        { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }
    | _ => .faulted
  | _ => .faulted

private def dispatchBlockCfg
    (ok : Bool) (s : MachineState) (ctx : BlockCtx) :
    Option BasicBlockData → CfgExecState
  | .none => .faulted
  | .some { statements := [], terminator := term, isCleanup := _ } =>
    evalTerminatorCfg ctx ok s term
  | .some { statements := stmt :: rest, terminator := term, isCleanup := _ } =>
    stepNodeToCfg ok (.some (s.frame.blockIdx, 1, rest, term)) (evalStmtFast ctx s stmt)

private def stepCfgState (ctx : BlockCtx) : CfgExecState → CfgExecState
  | .halted ok out => .halted ok out
  | .faulted => .faulted
  | .running ok cur s =>
    match s.memory.activeCallee with
    | .some _ => .faulted
    | .none =>
      match cur with
      | .none =>
        match Nat.beq s.frame.stmtIdx 0 with
        | false => .faulted
        | true => dispatchBlockCfg ok s ctx (lookupBlock ctx s.frame.blockIdx)
      | .some (blockIdx, stmtIdx, [], term) =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => .faulted
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => .faulted
          | true => evalTerminatorCfg ctx ok s term
      | .some (blockIdx, stmtIdx, stmt :: rest, term) =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => .faulted
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => .faulted
          | true =>
            stepNodeToCfg ok
              (.some (blockIdx, Nat.add stmtIdx 1, rest, term))
              (evalStmtFast ctx s stmt)

private def runCfgSteps (ctx : BlockCtx) (cfg : CfgExecState) : Nat → CfgExecState
  | 0 => cfg
  | fuel' + 1 => stepCfgState ctx (runCfgSteps ctx cfg fuel')

private theorem runCfgSteps_step (ctx : BlockCtx) (cfg : CfgExecState) (fuel : Nat) :
    runCfgSteps ctx cfg (fuel + 1) = runCfgSteps ctx (stepCfgState ctx cfg) fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel' ih =>
    change stepCfgState ctx (runCfgSteps ctx cfg (fuel' + 1)) =
      stepCfgState ctx (runCfgSteps ctx (stepCfgState ctx cfg) fuel')
    rw [ih]

private theorem runCfgSteps_halted (ctx : BlockCtx) (ok : Bool) (out : MirOutcome) (fuel : Nat) :
    runCfgSteps ctx (.halted ok out) fuel = .halted ok out := by
  induction fuel with
  | zero => rfl
  | succ fuel' ih =>
    dsimp only [runCfgSteps]
    rw [ih]
    rfl

private def CurValid (ctx : BlockCtx) :
    Option (Nat × Nat × List Statement × Terminator) → Prop
  | .none => True
  | .some (bIdx, sIdx, stmts, term) =>
    ∃ bb pfx,
      get? ctx.body.basicBlocks bIdx = some bb ∧
      sIdx = length pfx ∧
      bb.statements = pfx ++ stmts ∧
      term = bb.terminator

private def CfgValid (ctx : BlockCtx) : CfgExecState → MirExecState → Prop
  | .running _ cur s, st => st = .running s ∧ CurValid ctx cur
  | .halted _ out, st => st = .halted out
  | .faulted, _ => True

private theorem cfgOk_stepNodeToCfg_false
    (nextCur : Option (Nat × Nat × List Statement × Terminator))
    (node : MirStepNode) :
    cfgOk (stepNodeToCfg false nextCur node) = false := by
  cases node with
  | ret _ => rfl
  | tau st' => cases st' <;> rfl
  | vis i k =>
    rcases i with f | (e | c)
    · rfl
    · dsimp only [stepNodeToCfg, cfgOk]
      cases k PUnit.unit <;> rfl
    · rfl

private theorem cfgOk_evalTerminatorCfg_false
    (ctx : BlockCtx) (s : MachineState) (term : Terminator) :
    cfgOk (evalTerminatorCfg ctx false s term) = false := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto _ => rfl
  | return_ =>
    dsimp only [evalTerminatorCfg]
    cases s.memory.callStack with
    | cons _ _ => rfl
    | nil =>
      cases get? s.frame.locals 0 with
      | none => rfl
      | some slot => cases slot <;> rfl
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg]
    cases evalOperandFast ctx s.frame.locals discr s.memory.borrows s.memory.globals s.memory.callerLocals with
    | ok v _ => cases v <;> rfl
    | _ => rfl
  | assert cond expected target unwind =>
    dsimp only [evalTerminatorCfg]
    cases evalOperandFast ctx s.frame.locals cond s.memory.borrows s.memory.globals s.memory.callerLocals with
    | ok v _ => cases v <;> rfl
    | _ => rfl
  | _ => rfl

private theorem cfgOk_dispatchBlockCfg_false
    (s : MachineState) (ctx : BlockCtx) (bbOpt : Option BasicBlockData) :
    cfgOk (dispatchBlockCfg false s ctx bbOpt) = false := by
  cases bbOpt with
  | none => rfl
  | some bb =>
    rcases bb with ⟨stmts, term, isCleanup⟩
    cases stmts with
    | nil => exact cfgOk_evalTerminatorCfg_false ctx s term
    | cons stmt rest => exact cfgOk_stepNodeToCfg_false _ _

private theorem cfgOk_stepCfgState_false
    (ctx : BlockCtx) (cfg : CfgExecState) (h : cfgOk cfg = false) :
    cfgOk (stepCfgState ctx cfg) = false := by
  cases cfg with
  | faulted => rfl
  | halted ok out => exact h
  | running ok cur s =>
    change ok = false at h
    subst h
    cases h_ac : s.memory.activeCallee with
    | some _ =>
      dsimp only [stepCfgState]
      rw [h_ac]
      rfl
    | none =>
      cases cur with
      | none =>
        dsimp only [stepCfgState]
        rw [h_ac]
        dsimp only
        cases Nat.beq s.frame.stmtIdx 0 with
        | false => rfl
        | true => exact cfgOk_dispatchBlockCfg_false s ctx _
      | some tup =>
        rcases tup with ⟨bIdx, sIdx, stmts, term⟩
        cases stmts with
        | nil =>
          dsimp only [stepCfgState]
          rw [h_ac]
          dsimp only
          cases Nat.beq s.frame.blockIdx bIdx with
          | false => rfl
          | true =>
            cases Nat.beq s.frame.stmtIdx sIdx with
            | false => rfl
            | true => exact cfgOk_evalTerminatorCfg_false ctx s term
        | cons stmt rest =>
          dsimp only [stepCfgState]
          rw [h_ac]
          dsimp only
          cases Nat.beq s.frame.blockIdx bIdx with
          | false => rfl
          | true =>
            cases Nat.beq s.frame.stmtIdx sIdx with
            | false => rfl
            | true => exact cfgOk_stepNodeToCfg_false _ _

private theorem cfgOk_of_runCfgSteps_true
    (ctx : BlockCtx) (fuel : Nat) (cfg : CfgExecState)
    (h : cfgOk (runCfgSteps ctx cfg fuel) = true) :
    cfgOk cfg = true := by
  cases h_ok : cfgOk cfg with
  | true => rfl
  | false =>
    have h_false : ∀ n, cfgOk (runCfgSteps ctx cfg n) = false := by
      intro n
      induction n with
      | zero => exact h_ok
      | succ fuel' ih =>
        dsimp only [runCfgSteps]
        exact cfgOk_stepCfgState_false ctx (runCfgSteps ctx cfg fuel') ih
    have h_f := h_false fuel
    rw [h] at h_f
    nomatch h_f

private def stepNodeWP (ctx : BlockCtx) (post : MirOutcome → Prop) (fuel : Nat)
    (node : MirStepNode) : Prop :=
  match node with
  | .ret out => post out
  | .tau st' =>
    wpCoalBounded fuel mirDefaultWP (stepMirState ctx.body) (fun out _ => post out) st' PUnit.unit
  | .vis i k =>
    mirDefaultWP.wp i
      (fun o s' =>
        wpCoalBounded fuel mirDefaultWP (stepMirState ctx.body) (fun out _ => post out) (k o) s')
      PUnit.unit

private theorem wpCoalBounded_succ_eq
    (ctx : BlockCtx) (post : MirOutcome → Prop) (fuel : Nat) (st : MirExecState) :
    wpCoalBounded (fuel + 1) mirDefaultWP (stepMirState ctx.body)
      (fun out _ => post out) st PUnit.unit =
    stepNodeWP ctx post fuel (stepMirState ctx.body st) := by
  unfold wpCoalBounded stepNodeWP
  cases stepMirState ctx.body st <;> rfl

private theorem wpCoalBounded_stepNodeToCfg
    (ctx : BlockCtx) (post : MirOutcome → Prop) (fuel' : Nat)
    (nextCur : Option (Nat × Nat × List Statement × Terminator))
    (node : MirStepNode)
    (h_cur : CurValid ctx nextCur)
    (h_ok : cfgOk (stepNodeToCfg true nextCur node) = true)
    (ih : ∀ cfg' st', CfgValid ctx cfg' st' →
      cfgStateWP post (runCfgSteps ctx cfg' fuel') →
      wpCoalBounded (fuel' + 1) mirDefaultWP (stepMirState ctx.body) (fun out _ => post out) st' PUnit.unit)
    (h_wp : cfgStateWP post (runCfgSteps ctx (stepNodeToCfg true nextCur node) fuel')) :
    stepNodeWP ctx post (fuel' + 1) node := by
  cases node with
  | ret out =>
    dsimp only [stepNodeToCfg] at h_wp
    rw [runCfgSteps_halted] at h_wp
    exact h_wp.2
  | tau st' =>
    cases st' with
    | running s' =>
      exact ih (.running true nextCur s') (.running s') ⟨rfl, h_cur⟩ h_wp
    | halted out =>
      exact ih (.halted true out) (.halted out) rfl h_wp
    | faulted _ => nomatch h_ok
  | vis i k =>
    rcases i with f | (e | c)
    · nomatch h_ok
    · cases e
      dsimp only [stepNodeToCfg] at h_ok h_wp
      cases h_k : k PUnit.unit with
      | running s' =>
        rw [h_k] at h_wp
        have h_res := ih (.running true nextCur s') (.running s') ⟨rfl, h_cur⟩ h_wp
        rw [← h_k] at h_res
        exact h_res
      | halted out =>
        rw [h_k] at h_wp
        have h_res := ih (.halted true out) (.halted out) rfl h_wp
        rw [← h_k] at h_res
        exact h_res
      | faulted _ =>
        rw [h_k] at h_ok
        nomatch h_ok
    · nomatch h_ok

private theorem wpCoalBounded_evalTerminatorCfg
    (ctx : BlockCtx) (post : MirOutcome → Prop) (fuel' : Nat)
    (s : MachineState) (term : Terminator)
    (h_lay : ctx.layouts = ctx.body.layouts)
    (h_ok : cfgOk (evalTerminatorCfg ctx true s term) = true)
    (ih : ∀ cfg' st', CfgValid ctx cfg' st' →
      cfgStateWP post (runCfgSteps ctx cfg' fuel') →
      wpCoalBounded (fuel' + 1) mirDefaultWP (stepMirState ctx.body) (fun out _ => post out) st' PUnit.unit)
    (h_wp : cfgStateWP post (runCfgSteps ctx (evalTerminatorCfg ctx true s term) fuel')) :
    stepNodeWP ctx post (fuel' + 1) (evalTerminator s term (some ctx.body)) := by
  rcases term with ⟨kind, span⟩
  revert h_ok h_wp
  cases kind with
  | goto target =>
    intro _ h_wp
    exact ih (.running true .none { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
      (.running { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
      ⟨rfl, trivial⟩ h_wp
  | return_ =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    cases s.memory.callStack with
    | cons _ _ => rintro ⟨⟩ _
    | nil =>
      dsimp only
      cases get? s.frame.locals 0 with
      | none => rintro ⟨⟩ _
      | some slot =>
        cases slot with
        | dead => rintro ⟨⟩ _
        | uninit => rintro ⟨⟩ _
        | init retVal =>
          intro _ h_wp
          dsimp only [stepNodeWP, MirStepNode.retNormal] at h_wp ⊢
          rw [runCfgSteps_halted] at h_wp
          exact h_wp.2
  | switchInt discr targets =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    rw [evalOperandFast_eq, h_lay]
    cases evalOperand s.frame.locals discr s.memory.borrows s.memory.globals ctx.body.layouts s.memory.callerLocals with
    | ub => rintro ⟨⟩ _
    | unsupported => rintro ⟨⟩ _
    | ok v locals' =>
      cases v with
      | scalar sc =>
        dsimp only [stepNodeWP, MirStepNode.step]
        intro _ h_wp
        exact ih
          (.running true .none
            { s with frame := { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise, stmtIdx := 0, locals := locals' } })
          (.running
            { s with frame := { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise, stmtIdx := 0, locals := locals' } })
          ⟨rfl, trivial⟩ h_wp
      | _ => rintro ⟨⟩ _
  | assert cond expected target unwind =>
    dsimp only [evalTerminatorCfg, evalTerminator]
    rw [evalOperandFast_eq, h_lay]
    cases evalOperand s.frame.locals cond s.memory.borrows s.memory.globals ctx.body.layouts s.memory.callerLocals with
    | ub => rintro ⟨⟩ _
    | unsupported => rintro ⟨⟩ _
    | ok v locals' =>
      cases v with
      | scalar sc =>
        cases expected <;>
        · dsimp only [cfgOk, Bool.and]
          intro h_ok h_wp
          rw [h_ok] at h_wp ⊢
          dsimp only [stepNodeWP, MirStepNode.step] at h_wp ⊢
          exact ih
            (.running true .none { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })
            (.running { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })
            ⟨rfl, trivial⟩ h_wp
      | _ => rintro ⟨⟩ _
  | _ => rintro ⟨⟩ _

private theorem wpCoalBounded_of_runCfgSteps
    (ctx : BlockCtx) (post : MirOutcome → Prop)
    (h_ld : ctx.localDecls = ctx.body.localDecls)
    (h_lay : ctx.layouts = ctx.body.layouts)
    (h_phase : ctx.body.phase = .runtimeOptimized) :
    ∀ (fuel : Nat) (cfg : CfgExecState) (st : MirExecState),
      CfgValid ctx cfg st →
      cfgStateWP post (runCfgSteps ctx cfg fuel) →
      wpCoalBounded (fuel + 1) mirDefaultWP (stepMirState ctx.body)
        (fun out _ => post out) st PUnit.unit := by
  intro fuel
  induction fuel with
  | zero =>
    intro cfg st h_valid h_wp
    dsimp only [runCfgSteps] at h_wp
    cases cfg with
    | running _ _ _ => exact False.elim h_wp
    | faulted => exact False.elim h_wp
    | halted ok out =>
      change st = .halted out at h_valid
      subst h_valid
      exact h_wp.2
  | succ fuel' ih =>
    intro cfg st h_valid h_wp
    rw [runCfgSteps_step] at h_wp
    have h_ok1 : cfgOk (stepCfgState ctx cfg) = true :=
      cfgOk_of_runCfgSteps_true ctx fuel' (stepCfgState ctx cfg)
        (by
          cases h_end : runCfgSteps ctx (stepCfgState ctx cfg) fuel' with
          | halted ok out =>
            rw [h_end] at h_wp
            exact h_wp.1
          | running _ _ _ =>
            rw [h_end] at h_wp
            exact False.elim h_wp
          | faulted =>
            rw [h_end] at h_wp
            exact False.elim h_wp)
    have h_ok0 : cfgOk cfg = true := by
      cases h_c : cfgOk cfg with
      | true => rfl
      | false =>
        rw [cfgOk_stepCfgState_false ctx cfg h_c] at h_ok1
        nomatch h_ok1
    cases cfg with
    | faulted => nomatch h_ok0
    | halted ok out =>
      change st = .halted out at h_valid
      subst h_valid
      change ok = true at h_ok0
      subst h_ok0
      dsimp only [stepCfgState] at h_wp
      rw [runCfgSteps_halted] at h_wp
      exact h_wp.2
    | running ok cur s =>
      change ok = true at h_ok0
      subst h_ok0
      rcases h_valid with ⟨rfl, h_cur⟩
      dsimp only [stepCfgState] at h_ok1 h_wp
      cases h_ac : s.memory.activeCallee with
      | some _ =>
        rw [h_ac] at h_ok1
        nomatch h_ok1
      | none =>
        rw [h_ac] at h_ok1 h_wp
        dsimp only at h_ok1 h_wp
        rw [wpCoalBounded_succ_eq]
        dsimp only [stepMirState, stepMirFn]
        rw [h_ac]
        dsimp only [Option.getD]
        rw [h_phase]
        dsimp only
        cases cur with
        | none =>
          cases h_si : Nat.beq s.frame.stmtIdx 0 with
          | false =>
            rw [h_si] at h_ok1
            nomatch h_ok1
          | true =>
            rw [h_si] at h_ok1 h_wp
            dsimp only [lookupBlock] at h_ok1 h_wp
            have h_si_eq : s.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_si
            cases h_bb : get? ctx.body.basicBlocks s.frame.blockIdx with
            | none =>
              rw [h_bb] at h_ok1
              nomatch h_ok1
            | some bb =>
              rw [h_bb] at h_ok1 h_wp
              rcases bb with ⟨stmts, term, isCleanup⟩
              rw [h_si_eq]
              cases stmts with
              | nil =>
                dsimp only [dispatchBlockCfg, get?, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, length, BEq.beq, instBEqOfDecidableEq, Nat.decEq, instDecidableEqNat, decide] at h_ok1 h_wp ⊢
                exact wpCoalBounded_evalTerminatorCfg ctx post fuel' s term h_lay h_ok1 ih h_wp
              | cons stmt rest =>
                dsimp only [dispatchBlockCfg, get?, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal] at h_ok1 h_wp ⊢
                rw [← h_ld, ← h_lay, ← evalStmtFast_eq ctx s stmt]
                exact wpCoalBounded_stepNodeToCfg ctx post fuel'
                  (.some (s.frame.blockIdx, 1, rest, term))
                  (evalStmtFast ctx s stmt)
                  ⟨⟨stmt :: rest, term, isCleanup⟩, [stmt], h_bb, rfl, rfl, rfl⟩
                  h_ok1 ih h_wp
        | some tup =>
          rcases tup with ⟨blockIdx, stmtIdx, stmts, term⟩
          rcases h_cur with ⟨bb, pfx, h_bb, rfl, h_stmts, rfl⟩
          cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
          | false =>
            cases stmts <;> (dsimp only at h_ok1; rw [h_bi] at h_ok1; nomatch h_ok1)
          | true =>
            have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
            cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
            | false =>
              cases stmts <;> (dsimp only at h_ok1; rw [h_bi, h_si] at h_ok1; nomatch h_ok1)
            | true =>
              have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
              rw [h_bi_eq, h_bb, h_si_eq]
              dsimp only
              cases stmts with
              | nil =>
                dsimp only at h_ok1 h_wp
                rw [h_bi, h_si] at h_ok1 h_wp
                have h_eq : bb.statements = pfx := by simpa using h_stmts
                rw [← h_eq, get?_length_none]
                dsimp only
                have h_beq : (length bb.statements == length bb.statements) = true :=
                  beq_self_eq_true _
                rw [h_beq, if_pos rfl]
                exact wpCoalBounded_evalTerminatorCfg ctx post fuel' s bb.terminator h_lay h_ok1 ih h_wp
              | cons stmt rest =>
                dsimp only at h_ok1 h_wp
                rw [h_bi, h_si] at h_ok1 h_wp
                rw [h_stmts, get?_append_cons]
                dsimp only
                rw [← h_ld, ← h_lay, ← evalStmtFast_eq ctx s stmt]
                exact wpCoalBounded_stepNodeToCfg ctx post fuel'
                  (.some (blockIdx, Nat.add (length pfx) 1, rest, bb.terminator))
                  (evalStmtFast ctx s stmt)
                  ⟨bb, pfx ++ [stmt], h_bb, (length_append_singleton pfx stmt).symm,
                    by simp [h_stmts, List.append_assoc], rfl⟩
                  h_ok1 ih h_wp

private def dummyBB : BasicBlockData :=
  { statements := [], terminator := { kind := .unreachable, span := "" }, isCleanup := false }

private def safeBB0 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 0).getD dummyBB
private def safeBB1 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 1).getD dummyBB
private def safeBB2 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 2).getD dummyBB
private def safeBB3 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 3).getD dummyBB
private def safeBB4 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 4).getD dummyBB
private def safeBB5 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 5).getD dummyBB
private def safeBB6 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 6).getD dummyBB
private def safeBB7 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 7).getD dummyBB
private def safeBB8 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 8).getD dummyBB
private def safeBB9 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 9).getD dummyBB
private def safeBB10 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 10).getD dummyBB
private def safeBB11 : BasicBlockData :=
  (get? Mir.WireframeDemo.checksum_frame_safe.body.basicBlocks 11).getD dummyBB

private def safeCtx : BlockCtx :=
  { localDecls := Mir.WireframeDemo.checksum_frame_safe.body.localDecls
    layouts := Mir.WireframeDemo.checksum_frame_safe.body.layouts
    body := Mir.WireframeDemo.checksum_frame_safe.body }

private theorem safeCtx_localDecls :
    safeCtx.localDecls = Mir.WireframeDemo.checksum_frame_safe.body.localDecls := rfl
private theorem safeCtx_layouts :
    safeCtx.layouts = Mir.WireframeDemo.checksum_frame_safe.body.layouts := rfl
private theorem safeCtx_body_localDecls :
    safeCtx.body.localDecls = Mir.WireframeDemo.checksum_frame_safe.body.localDecls := rfl
private theorem safeCtx_body_argCount :
    safeCtx.body.argCount = 1 := rfl
private theorem safeCtx_body_layouts :
    safeCtx.body.layouts = Mir.WireframeDemo.checksum_frame_safe.body.layouts := rfl
private theorem safeCtx_phase :
    safeCtx.body.phase = .runtimeOptimized := rfl
private theorem safeCtx_bb1 :
    lookupBlock safeCtx 1 = some safeBB1 := rfl
private theorem safeCtx_bb2 :
    lookupBlock safeCtx 2 = some safeBB2 := rfl
private theorem safeCtx_bb3 :
    lookupBlock safeCtx 3 = some safeBB3 := rfl
private theorem safeCtx_bb4 :
    lookupBlock safeCtx 4 = some safeBB4 := rfl
private theorem safeCtx_bb5 :
    lookupBlock safeCtx 5 = some safeBB5 := rfl
private theorem safeCtx_bb6 :
    lookupBlock safeCtx 6 = some safeBB6 := rfl
private theorem safeCtx_bb7 :
    lookupBlock safeCtx 7 = some safeBB7 := rfl
private theorem safeCtx_bb8 :
    lookupBlock safeCtx 8 = some safeBB8 := rfl
private theorem safeCtx_bb9 :
    lookupBlock safeCtx 9 = some safeBB9 := rfl
private theorem safeCtx_bb10 :
    lookupBlock safeCtx 10 = some safeBB10 := rfl
private theorem safeCtx_bb11 :
    lookupBlock safeCtx 11 = some safeBB11 := rfl

private theorem cfgStateWP_of_eq
    {post : MirOutcome → Prop} {cfg : CfgExecState} {out : MirOutcome}
    (h_eq : cfg = .halted true out) (h_post : post out) :
    cfgStateWP post cfg := by
  rw [h_eq]
  exact ⟨rfl, h_post⟩

private theorem verifySafeCfgSteps
    (fuel : Nat)
    (h_wp : ∀ args mem,
      Obligations.WireframeDemo.checksum_frame_safe.statefulClaim.pre args mem →
      ∃ retVal,
        runCfgSteps safeCtx
          (.running true (.some (0, 0, safeBB0.statements, safeBB0.terminator))
            (initMachineStateWithMemory safeCtx.body args mem))
          fuel = .halted true (.normal (retVal, mem)) ∧
        Obligations.WireframeDemo.checksum_frame_safe.statefulClaim.post args mem retVal mem) :
    StatefulVerificationResult Obligations.WireframeDemo.checksum_frame_safe.statefulClaim := by
  refine verifyStatefulMirNoPanicSym
    Obligations.WireframeDemo.checksum_frame_safe.statefulClaim (fuel + 1) ?_
  intro args mem h_pre
  rcases h_wp args mem h_pre with ⟨retVal, h_eq, h_post⟩
  change wpMirSym (fuel + 1) safeCtx.body
    (initMachineStateWithMemory safeCtx.body args mem)
    (mirNormalPost (Obligations.WireframeDemo.checksum_frame_safe.statefulClaim.post args mem))
  unfold wpMirSym
  rw [wpMirExecSym_eq_wpCoalBounded]
  exact wpCoalBounded_of_runCfgSteps safeCtx
    (mirNormalPost (Obligations.WireframeDemo.checksum_frame_safe.statefulClaim.post args mem))
    rfl rfl rfl fuel
    (.running true (.some (0, 0, safeBB0.statements, safeBB0.terminator))
      (initMachineStateWithMemory safeCtx.body args mem))
    (.running (initMachineStateWithMemory safeCtx.body args mem))
    ⟨rfl, ⟨safeBB0, [], rfl, rfl, rfl, rfl⟩⟩
    (cfgStateWP_of_eq h_eq h_post)

/-- Universal stateful verification certificate for `checksum_frame_safe`. -/
theorem verified :
    StatefulVerificationResult Obligations.WireframeDemo.checksum_frame_safe.statefulClaim := by
  refine verifySafeCfgSteps 185 ?_
  intro args mem h_pre
  rcases h_pre with
    ⟨_, b0, b1, b2, b3, b4, b5, b6, b7,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
      rfl, h_callee, h_stack, h_borrows, h_caller⟩
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees,
      callStack, activeCallee, activeProtectors, nextProtector, callerLocals⟩
  dsimp at h_callee h_stack h_borrows h_caller
  subst h_callee h_stack h_borrows h_caller
  refine ⟨.scalar ⟨bigEndianWordSum4 b0 b1 b2 b3 b4 b5 b6 b7, 4⟩, ?_, ?_⟩
  · dsimp only [
      Mir.WireframeDemo.checksum_frame_safe.layouts,
      Mir.WireframeDemo.checksum_frame_safe.body,
      safeCtx_localDecls, safeCtx_layouts, safeCtx_body_localDecls, safeCtx_body_argCount, safeCtx_body_layouts, safeCtx_phase,
      safeCtx_bb1, safeCtx_bb2, safeCtx_bb3, safeCtx_bb4, safeCtx_bb5,
      safeCtx_bb6, safeCtx_bb7, safeCtx_bb8, safeCtx_bb9, safeCtx_bb10, safeCtx_bb11,
      safeBB0, safeBB1, safeBB2, safeBB3, safeBB4, safeBB5,
      safeBB6, safeBB7, safeBB8, safeBB9, safeBB10, safeBB11,
      runCfgSteps, stepCfgState, dispatchBlockCfg, stepNodeToCfg, evalTerminatorCfg,
      evalStmtFast, finishAssignStmtNodeFast, advanceStmt,
      evalRvalueFast,
      evalOperandFast, evalConstValue,
      evalScalarBinOp, evalUnaryNot,
      operandIsSigned, operandTy, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
      intCastTargetBytes, shiftLeftBits, shiftRightUnsignedBits, scalarPow2_eight,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8, mul_0_2, mul_1_2, mul_2_2, mul_3_2,
      wrap8_0, wrap8_1, wrap8_2, wrap8_3, wrap8_4, wrap8_5, wrap8_6, wrap8_7, wrap4_8,
      get?_frame8CallerLocals, get?Internal_frame8CallerLocals,
      lookupSwitchTarget, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal,
      initMachineStateWithMemory, initLocals, initLocalsAux,
      rootFrame8Ptr, frame8Value, sharedFrame8Borrow, frame8SlotIdx,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
      projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
      byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
      isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
      invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
      boolToScalar,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.mod, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    have h_wb0 : wrapScalarBits b0 4294967296 = b0 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb1 : wrapScalarBits b1 4294967296 = b1 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb2 : wrapScalarBits b2 4294967296 = b2 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb3 : wrapScalarBits b3 4294967296 = b3 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb4 : wrapScalarBits b4 4294967296 = b4 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb5 : wrapScalarBits b5 4294967296 = b5 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb6 : wrapScalarBits b6 4294967296 = b6 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb7 : wrapScalarBits b7 4294967296 = b7 := wrapScalarBits_eq_of_lt (by omega)
    have h_or0 : bitwiseOrBits 32 (wrapScalarBits (b0 * 256) 4294967296) b1 = b0 * 256 + b1 := by
      rw [wrapScalarBits_eq_of_lt (by omega)]
      exact bitwiseOrBits_32_mul256_add (by omega) hb1
    have h_or1 : bitwiseOrBits 32 (wrapScalarBits (b2 * 256) 4294967296) b3 = b2 * 256 + b3 := by
      rw [wrapScalarBits_eq_of_lt (by omega)]
      exact bitwiseOrBits_32_mul256_add (by omega) hb3
    have h_or2 : bitwiseOrBits 32 (wrapScalarBits (b4 * 256) 4294967296) b5 = b4 * 256 + b5 := by
      rw [wrapScalarBits_eq_of_lt (by omega)]
      exact bitwiseOrBits_32_mul256_add (by omega) hb5
    have h_or3 : bitwiseOrBits 32 (wrapScalarBits (b6 * 256) 4294967296) b7 = b6 * 256 + b7 := by
      rw [wrapScalarBits_eq_of_lt (by omega)]
      exact bitwiseOrBits_32_mul256_add (by omega) hb7
    simp only [Nat.add_eq, Nat.mul_eq,
      h_wb0, h_wb1, h_wb2, h_wb3, h_wb4, h_wb5, h_wb6, h_wb7,
      h_or0, h_or1, h_or2, h_or3]
    have h_ovf1 : Nat.ble 4294967296 (0 + (b0 * 256 + b1)) = false := by
      cases hq : Nat.ble 4294967296 (0 + (b0 * 256 + b1))
      · rfl
      · have := Nat.le_of_ble_eq_true hq; omega
    have h_w1 : wrapScalarBits (0 + (b0 * 256 + b1)) 4294967296 = b0 * 256 + b1 := by
      rw [Nat.zero_add]; exact wrapScalarBits_eq_of_lt (by omega)
    have h_ovf2 : Nat.ble 4294967296 (b0 * 256 + b1 + (b2 * 256 + b3)) = false := by
      cases hq : Nat.ble 4294967296 (b0 * 256 + b1 + (b2 * 256 + b3))
      · rfl
      · have := Nat.le_of_ble_eq_true hq; omega
    have h_w2 :
        wrapScalarBits (b0 * 256 + b1 + (b2 * 256 + b3)) 4294967296 =
          (b0 * 256 + b1) + (b2 * 256 + b3) :=
      wrapScalarBits_eq_of_lt (by omega)
    have h_ovf3 :
        Nat.ble 4294967296 ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5)) = false := by
      cases hq : Nat.ble 4294967296 ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5))
      · rfl
      · have := Nat.le_of_ble_eq_true hq; omega
    have h_w3 :
        wrapScalarBits ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5)) 4294967296 =
          (b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) :=
      wrapScalarBits_eq_of_lt (by omega)
    have h_ovf4 :
        Nat.ble 4294967296
          ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7)) = false := by
      cases hq :
        Nat.ble 4294967296
          ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7))
      · rfl
      · have := Nat.le_of_ble_eq_true hq; omega
    have h_w4 :
        wrapScalarBits
          ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7))
          4294967296 =
          (b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7) :=
      wrapScalarBits_eq_of_lt (by omega)
    simp only [h_ovf1, h_w1, h_ovf2, h_w2, h_ovf3, h_w3, h_ovf4, h_w4]
    rfl
  · refine ⟨trivial, rfl, ?_⟩
    intro b0' b1' b2' b3' b4' b5' b6' b7' _ h_caller_eq
    dsimp only at h_caller_eq
    have h_slot :
        List.get?Internal (frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7) 69 =
          List.get?Internal (frame8CallerLocals b0' b1' b2' b3' b4' b5' b6' b7') 69 := by
      rw [h_caller_eq]
    rw [get?Internal_frame8CallerLocals, get?Internal_frame8CallerLocals] at h_slot
    dsimp [frame8Value] at h_slot
    injection h_slot with h_init
    injection h_init with h_agg
    injection h_agg with _ h_elems
    injection h_elems with e0 r1
    injection r1 with e1 r2
    injection r2 with e2 r3
    injection r3 with e3 r4
    injection r4 with e4 r5
    injection r5 with e5 r6
    injection r6 with e6 r7
    injection r7 with e7 _
    injection e0 with s0; injection s0 with q0 _
    injection e1 with s1; injection s1 with q1 _
    injection e2 with s2; injection s2 with q2 _
    injection e3 with s3; injection s3 with q3 _
    injection e4 with s4; injection s4 with q4 _
    injection e5 with s5; injection s5 with q5 _
    injection e6 with s6; injection s6 with q6 _
    injection e7 with s7; injection s7 with q7 _
    subst q0 q1 q2 q3 q4 q5 q6 q7
    rfl

end Proof.WireframeDemo.checksum_frame_safe
