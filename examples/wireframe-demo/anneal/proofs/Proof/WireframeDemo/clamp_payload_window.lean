import Trusted
import Anneal
import Mir.WireframeDemo.clamp_payload_window
import Obligations.WireframeDemo.clamp_payload_window

namespace Proof.WireframeDemo.clamp_payload_window

set_option linter.all false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

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

private theorem readProjectedValue_nil (locals : List LocalSlot) (v : Value) :
    readProjectedValue locals v [] = .ok v := rfl

private theorem readProjectedValue_field
    (locals : List LocalSlot) (vIdx : Nat) (fields : List Value)
    (idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    readProjectedValue locals (.aggregate vIdx fields) (.field idx ty :: rest) =
      match get? fields idx with
      | .some fieldVal => readProjectedValue locals fieldVal rest
      | .none => .ub := rfl

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

private def evalOperandsFast
    (ctx : BlockCtx) (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) : OperandsEvalResult :=
  match ops with
  | .nil => .ok .nil locals
  | op :: rest =>
    match evalOperandFast ctx locals op borrows globals callerLocals with
    | .ok v locals₁ =>
      match evalOperandsFast ctx locals₁ rest borrows globals callerLocals with
      | .ok vs locals₂ => .ok (v :: vs) locals₂
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported

private theorem evalOperandsFast_eq
    (ctx : BlockCtx) (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) :
    evalOperandsFast ctx locals ops borrows globals callerLocals =
      evalOperands locals ops borrows globals ctx.layouts callerLocals := by
  induction ops generalizing locals with
  | nil => rfl
  | cons op rest ih =>
    change
      (match evalOperandFast ctx locals op borrows globals callerLocals with
       | .ok v locals₁ =>
         match evalOperandsFast ctx locals₁ rest borrows globals callerLocals with
         | .ok vs locals₂ => OperandsEvalResult.ok (v :: vs) locals₂
         | .ub => OperandsEvalResult.ub
         | .unsupported => OperandsEvalResult.unsupported
       | .ub => OperandsEvalResult.ub
       | .unsupported => OperandsEvalResult.unsupported) =
      (match evalOperand locals op borrows globals ctx.layouts callerLocals with
       | .ok v locals₁ =>
         match evalOperands locals₁ rest borrows globals ctx.layouts callerLocals with
         | .ok vs locals₂ => OperandsEvalResult.ok (v :: vs) locals₂
         | .ub => OperandsEvalResult.ub
         | .unsupported => OperandsEvalResult.unsupported
       | .ub => OperandsEvalResult.ub
       | .unsupported => OperandsEvalResult.unsupported)
    rw [evalOperandFast_eq]
    cases evalOperand locals op borrows globals ctx.layouts callerLocals with
    | ok v locals₁ =>
      dsimp only
      rw [ih locals₁]
    | ub => rfl
    | unsupported => rfl

private def bitwiseAndBitsFast (numBits a b : Nat) : Nat :=
  match Nat.beq numBits 8, Nat.beq b 1 with
  | true, true => a % 2
  | _, _ => bitwiseAndBits numBits a b

private theorem bitwiseAndBitsFast_eq (numBits a b : Nat) :
    bitwiseAndBitsFast numBits a b = bitwiseAndBits numBits a b := by
  unfold bitwiseAndBitsFast
  cases h1 : Nat.beq numBits 8 with
  | false => rfl
  | true =>
    cases h2 : Nat.beq b 1 with
    | false => rfl
    | true =>
      rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
      exact (bitwiseAndBits_8_1 a).symm

private def evalRvalueFallback (locals : List LocalSlot) (rv : Rvalue)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) : RvalueEvalResult :=
  evalRvalue locals rv mem localDecls layouts

private def evalRvalueSymTreeFast
    (ctx : BlockCtx) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    SymTree RvalueEvalResult :=
  match rv with
  | .use op =>
    match evalOperandFast ctx locals op mem.borrows mem.globals mem.callerLocals with
    | .ok v locals' => .leaf (.ok v locals' mem)
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
  | .ref bk p =>
    match bk, p.projection with
    | .shared, .nil =>
      match get? locals p.local_ with
      | .none => .leaf .ub
      | .some .dead => .leaf .ub
      | .some _ =>
        let tag := mem.nextTag
        let entry : BorrowEntry := {
          tag := tag
          targetLocal := p.local_
          targetProjection := .nil
          perm := .frozen
        }
        let mem' := {
          mem with
          borrows := entry :: mem.borrows
          nextTag := Nat.add tag 1
        }
        .leaf (.ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem')
    | _, _ => .leaf (evalRvalueFallback locals (.ref bk p) mem ctx.localDecls ctx.layouts)
  | .aggregate ak ops =>
    match ak with
    | .tuple =>
      match evalOperandsFast ctx locals ops mem.borrows mem.globals mem.callerLocals with
      | .ok vals locals' => .leaf (.ok (.aggregate 0 vals) locals' mem)
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | _ => .leaf (evalRvalueFallback locals (.aggregate ak ops) mem ctx.localDecls ctx.layouts)
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandFast ctx locals lhsOp mem.borrows mem.globals mem.callerLocals with
    | .ok lhsVal locals₁ =>
      match evalOperandFast ctx locals₁ rhsOp mem.borrows mem.globals mem.callerLocals with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          match op with
          | .bitAnd =>
            .branch (Nat.beq lhs.sizeBytes 0) (.leaf .unsupported)
              (.branch (Nat.beq lhs.sizeBytes rhs.sizeBytes)
                (.leaf (.ok (.scalar ⟨bitwiseAndBitsFast (Nat.mul lhs.sizeBytes 8) lhs.bits rhs.bits, lhs.sizeBytes⟩) locals₂ mem))
                (.leaf .unsupported))
          | .eq => evalScalarBinOpSymTree .eq lhs rhs locals₂ mem false
          | .ne => evalScalarBinOpSymTree .ne lhs rhs locals₂ mem false
          | _ =>
            let isSigned := operandIsSigned ctx.localDecls lhsOp ctx.layouts
            evalScalarBinOpSymTree op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            .leaf (.ok (.ptr { ptrVal with offsetBytes := Nat.add ptrVal.offsetBytes offsetSc.bits } sz) locals₂ mem)
          | _ => .leaf .unsupported
        | _, _ => .leaf .unsupported
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
  | .unaryOp uop op =>
    match uop with
    | .not =>
      match evalOperandFast ctx locals op mem.borrows mem.globals mem.callerLocals with
      | .ok (.scalar sc) locals' =>
        evalUnaryNotSymTree sc (operandTy ctx.localDecls ctx.layouts op) locals' mem
      | .ok _ _ => .leaf .unsupported
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | _ => .leaf (evalRvalueFallback locals (.unaryOp uop op) mem ctx.localDecls ctx.layouts)
  | _ => .leaf (evalRvalueFallback locals rv mem ctx.localDecls ctx.layouts)

private theorem evalRvalueSymTreeFast_eq
    (ctx : BlockCtx) (locals : List LocalSlot) (rv : Rvalue) (mem : Memory) :
    evalRvalueSymTreeFast ctx locals rv mem =
      evalRvalueSymTree locals rv mem ctx.localDecls ctx.layouts := by
  cases rv with
  | use op =>
    dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals op mem.borrows mem.globals ctx.layouts mem.callerLocals <;> rfl
  | ref bk p =>
    cases bk with
    | shared =>
      rcases p with ⟨loc, proj⟩
      cases proj with
      | nil =>
        dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
        cases get? locals loc with
        | none => rfl
        | some slot => cases slot <;> rfl
      | cons hd _ =>
        cases hd <;> rfl
    | _ => rfl
  | aggregate ak ops =>
    cases ak with
    | tuple =>
      dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
      rw [evalOperandsFast_eq]
      cases evalOperands locals ops mem.borrows mem.globals ctx.layouts mem.callerLocals <;> rfl
    | _ => rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree]
    rw [evalOperandFast_eq]
    cases evalOperand locals lhsOp mem.borrows mem.globals ctx.layouts mem.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [evalOperandFast_eq]
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals ctx.layouts mem.callerLocals with
      | ub => rfl
      | unsupported => rfl
      | ok v₂ locals₂ =>
        cases v with
        | scalar lhs =>
          cases v₂ with
          | scalar rhs =>
            cases op <;> simp only [evalScalarBinOpSymTree, bitwiseAndBitsFast_eq]
          | _ => rfl
        | _ => cases v₂ <;> rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree]
      rw [evalOperandFast_eq]
      cases evalOperand locals op mem.borrows mem.globals ctx.layouts mem.callerLocals with
      | ok v _ => cases v <;> rfl
      | _ => rfl
    | neg => rfl
    | ptrMetadata => rfl
  | _ => rfl

private def evalStmtFallback (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  evalStmt s stmt localDecls layouts

private def finishAssignSymTree (s : MachineState) (dst : Place) :
    SymTree RvalueEvalResult → SymTree MirStepNode
  | .leaf res => .leaf (finishAssignStmtNode s dst res)
  | .branch c t1 t2 => .branch c (finishAssignSymTree s dst t1) (finishAssignSymTree s dst t2)

private theorem finishAssignSymTree_eq (s : MachineState) (dst : Place)
    (t : SymTree RvalueEvalResult) :
    finishAssignSymTree s dst t =
      t.bind (fun res => .leaf (finishAssignStmtNode s dst res)) := by
  induction t with
  | leaf _ => rfl
  | branch _ _ _ ih1 ih2 =>
    dsimp only [finishAssignSymTree, SymTree.bind]
    rw [ih1, ih2]

private def evalStmtSymTreeFast
    (ctx : BlockCtx) (s : MachineState) (stmt : Statement) : SymTree MirStepNode :=
  match stmt.kind with
  | .assign dst rv =>
    finishAssignSymTree s dst
      (evalRvalueSymTreeFast ctx s.frame.locals rv s.memory)
  | .storageLive loc =>
    .leaf
      (match get? s.frame.locals loc with
       | .some _ =>
         match set? s.frame.locals loc .uninit with
         | .some locals' => MirStepNode.step (advanceStmt s locals')
         | .none => MirStepNode.fail .ub
       | .none => MirStepNode.fail .ub)
  | .storageDead loc =>
    .leaf
      (match get? s.frame.locals loc with
       | .some _ =>
         match set? s.frame.locals loc .dead with
         | .some locals' => MirStepNode.step (advanceStmt s locals')
         | .none => MirStepNode.fail .ub
       | .none => MirStepNode.fail .ub)
  | .nop => .leaf (MirStepNode.step (advanceStmt s s.frame.locals))
  | _ => .leaf (evalStmtFallback s stmt ctx.localDecls ctx.layouts)

private theorem evalStmtSymTreeFast_eq
    (ctx : BlockCtx) (s : MachineState) (stmt : Statement) :
    evalStmtSymTreeFast ctx s stmt =
      evalStmtSymTree s stmt ctx.localDecls ctx.layouts := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    show finishAssignSymTree s dst (evalRvalueSymTreeFast ctx s.frame.locals rv s.memory) =
      (evalRvalueSymTree s.frame.locals rv s.memory ctx.localDecls ctx.layouts).bind _
    rw [finishAssignSymTree_eq, evalRvalueSymTreeFast_eq]
  | _ => rfl

private def evalTerminatorFallback (s : MachineState) (term : Terminator)
    (currentBody : CapturedMir) : SymTree MirStepNode :=
  evalTerminatorSymTree s term currentBody

private def evalTerminatorSymTreeFast
    (ctx : BlockCtx) (s : MachineState) (term : Terminator) : SymTree MirStepNode :=
  match term.kind with
  | .goto target =>
    .leaf (MirStepNode.step { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
  | .return_ =>
    match s.memory.callStack with
    | .nil =>
      match get? s.frame.locals 0 with
      | .some (.init retVal) => .leaf (MirStepNode.retNormal retVal s.memory)
      | _ => .leaf (MirStepNode.fail .ub)
    | _ :: _ => evalTerminatorFallback s term ctx.body
  | .switchInt discr targets =>
    match evalOperandFast ctx s.frame.locals discr s.memory.borrows s.memory.globals s.memory.callerLocals with
    | .ok (.scalar sc) locals' =>
      (lookupSwitchTargetTree sc.bits targets.branches targets.otherwise).bind
        (fun target =>
          .leaf (.vis (.inr (.inl (.emit (.event sc.bits))))
            (fun _ => .running { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })))
    | .ok _ _ => .leaf (MirStepNode.fail .ub)
    | .ub => .leaf (MirStepNode.fail .ub)
    | .unsupported => .leaf MirStepNode.unsupported
  | .assert cond expected target unwind =>
    match evalOperandFast ctx s.frame.locals cond s.memory.borrows s.memory.globals s.memory.callerLocals with
    | .ok (.scalar sc) locals' =>
      let expectedBit := match expected with | true => 1 | false => 0
      .branch (Nat.beq sc.bits expectedBit)
        (.leaf (MirStepNode.step { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }))
        (.leaf
          (match applyUnwindAction s locals' s.memory unwind with
          | .running nextState => MirStepNode.step nextState
          | .halted out => .ret out
          | .faulted fk => MirStepNode.fail fk))
    | _ => evalTerminatorFallback s term ctx.body
  | _ => evalTerminatorFallback s term ctx.body

private theorem evalTerminatorSymTreeFast_eq
    (ctx : BlockCtx) (s : MachineState) (term : Terminator)
    (h_lay : ctx.layouts = ctx.body.layouts) :
    evalTerminatorSymTreeFast ctx s term =
      evalTerminatorSymTree s term ctx.body := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | return_ =>
    show evalTerminatorSymTreeFast ctx s { kind := .return_, span := span } =
      evalTerminatorSymTree s { kind := .return_, span := span } ctx.body
    unfold evalTerminatorSymTreeFast evalTerminatorFallback evalTerminatorSymTree evalTerminator
    dsimp only
    cases s.memory.callStack with
    | nil =>
      cases get? s.frame.locals 0 with
      | none => rfl
      | some slot => cases slot <;> rfl
    | cons _ _ => rfl
  | switchInt discr targets =>
    show evalTerminatorSymTreeFast ctx s { kind := .switchInt discr targets, span := span } =
      evalTerminatorSymTree s { kind := .switchInt discr targets, span := span } ctx.body
    unfold evalTerminatorSymTreeFast evalTerminatorSymTree
    dsimp only
    rw [evalOperandFast_eq, h_lay]
    rfl
  | assert cond expected target unwind =>
    unfold evalTerminatorSymTreeFast evalTerminatorFallback evalTerminatorSymTree
    dsimp only
    rw [evalOperandFast_eq, h_lay]
    cases evalOperand s.frame.locals cond s.memory.borrows s.memory.globals ctx.body.layouts s.memory.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok v _ => cases v <;> rfl
  | _ => rfl

private def stepMirSymTreeFast (ctx : BlockCtx) (s : MachineState) : SymTree MirStepNode :=
  match s.memory.activeCallee with
  | .some _ => stepMirSymTree ctx.body s
  | .none =>
    match ctx.body.phase with
    | .other _ => .leaf MirStepNode.unsupported
    | _ =>
      match get? ctx.body.basicBlocks s.frame.blockIdx with
      | none => .leaf (MirStepNode.fail .ub)
      | some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | some stmt =>
          evalStmtSymTreeFast ctx s stmt
        | none =>
          if s.frame.stmtIdx == length bb.statements then
            evalTerminatorSymTreeFast ctx s bb.terminator
          else
            .leaf (MirStepNode.fail .ub)

private theorem stepMirSymTreeFast_eq (ctx : BlockCtx) (s : MachineState)
    (h_ld : ctx.localDecls = ctx.body.localDecls)
    (h_lay : ctx.layouts = ctx.body.layouts) :
    stepMirSymTreeFast ctx s = stepMirSymTree ctx.body s := by
  unfold stepMirSymTreeFast stepMirSymTree
  cases s.memory.activeCallee with
  | some _ => rfl
  | none =>
    dsimp only [Option.getD]
    cases ctx.body.phase with
    | other _ => rfl
    | _ =>
      all_goals
        dsimp only
        cases get? ctx.body.basicBlocks s.frame.blockIdx with
        | none => rfl
        | some bb =>
          dsimp only
          cases get? bb.statements s.frame.stmtIdx with
          | some stmt =>
            dsimp only
            rw [evalStmtSymTreeFast_eq, h_ld, h_lay]
          | none =>
            dsimp only
            split
            · exact evalTerminatorSymTreeFast_eq ctx s bb.terminator h_lay
            · rfl

private def wpExecGen (zeroVal : Prop) (ctx : BlockCtx) (post : MirOutcome → Prop) :
    Nat → MirExecState → Prop
  | 0, _ => zeroVal
  | _ + 1, .halted out => post out
  | _ + 1, .faulted _ => False
  | fuel' + 1, .running s =>
    evalSymNodeTree (wpExecGen zeroVal ctx post fuel') post (stepMirSymTreeFast ctx s)

private theorem wpMirExecSym_eq_gen
    (fuel : Nat) (ctx : BlockCtx) (st : MirExecState) (post : MirOutcome → Prop)
    (h_ld : ctx.localDecls = ctx.body.localDecls)
    (h_lay : ctx.layouts = ctx.body.layouts) :
    wpMirExecSym fuel ctx.body st post = wpExecGen False ctx post fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    have h_fn : (fun st' => wpMirExecSym fuel' ctx.body st' post) = wpExecGen False ctx post fuel' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, wpExecGen]
      rw [h_fn, stepMirSymTreeFast_eq ctx s h_ld h_lay]
    | halted out =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, wpExecGen]
    | faulted fk =>
      cases fk <;>
        dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, MirStepNode.fail, wpExecGen]

private theorem wpMirExecOrExhaustedSym_eq_gen
    (fuel : Nat) (ctx : BlockCtx) (st : MirExecState) (post : MirOutcome → Prop)
    (h_ld : ctx.localDecls = ctx.body.localDecls)
    (h_lay : ctx.layouts = ctx.body.layouts) :
    wpMirExecOrExhaustedSym fuel ctx.body st post = wpExecGen True ctx post fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    have h_fn :
        (fun st' => wpMirExecOrExhaustedSym fuel' ctx.body st' post) = wpExecGen True ctx post fuel' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      dsimp only [wpMirExecOrExhaustedSym, stepMirExecSymTree, wpExecGen]
      rw [h_fn, stepMirSymTreeFast_eq ctx s h_ld h_lay]
    | halted out =>
      dsimp only [wpMirExecOrExhaustedSym, stepMirExecSymTree, evalSymNodeTree, wpExecGen]
    | faulted fk =>
      cases fk <;>
        dsimp only [wpMirExecOrExhaustedSym, stepMirExecSymTree, evalSymNodeTree,
          MirStepNode.fail, wpExecGen]

private def wpExecFallback (zeroVal : Prop) (ctx : BlockCtx) (post : MirOutcome → Prop)
    (fuel : Nat) (st : MirExecState) : Prop :=
  wpExecGen zeroVal ctx post fuel st

private def lookupBlock (ctx : BlockCtx) (idx : Nat) : Option BasicBlockData :=
  get? ctx.body.basicBlocks idx

private def dispatchBlock
    (fallback : Prop)
    (s : MachineState)
    (ctx : BlockCtx)
    (post : MirOutcome → Prop)
    (kNone : MirExecState → Prop)
    (kSome : Nat → List Statement → Terminator → MirExecState → Prop) :
    Option BasicBlockData → Prop
  | .none => fallback
  | .some { statements := [], terminator := term, isCleanup := _ } =>
    evalSymNodeTree kNone post (evalTerminatorSymTreeFast ctx s term)
  | .some { statements := stmt :: rest, terminator := term, isCleanup := _ } =>
    evalSymNodeTree (kSome s.frame.blockIdx rest term) post (evalStmtSymTreeFast ctx s stmt)

private def wpCfgStep
    (zeroVal : Prop) (ctx : BlockCtx) (post : MirOutcome → Prop) :
    Nat → Option (Nat × Nat × List Statement × Terminator) → MirExecState → Prop
  | 0, _, _ => zeroVal
  | _ + 1, _, .halted out => post out
  | _ + 1, _, .faulted _ => False
  | fuel' + 1, .none, .running s =>
      match s.memory.activeCallee with
      | .some _ => wpExecFallback zeroVal ctx post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.stmtIdx 0 with
        | false => wpExecFallback zeroVal ctx post (fuel' + 1) (.running s)
        | true =>
          dispatchBlock
            False
            s ctx post
            (wpCfgStep zeroVal ctx post fuel' .none)
            (fun bIdx rest term => wpCfgStep zeroVal ctx post fuel' (.some (bIdx, 1, rest, term)))
            (lookupBlock ctx s.frame.blockIdx)
  | fuel' + 1, .some (blockIdx, stmtIdx, [], term), .running s =>
      match s.memory.activeCallee with
      | .some _ => wpExecFallback zeroVal ctx post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => wpExecFallback zeroVal ctx post (fuel' + 1) (.running s)
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => wpExecFallback zeroVal ctx post (fuel' + 1) (.running s)
          | true =>
            evalSymNodeTree
              (wpCfgStep zeroVal ctx post fuel' .none)
              post
              (evalTerminatorSymTreeFast ctx s term)
  | fuel' + 1, .some (blockIdx, stmtIdx, stmt :: rest, term), .running s =>
      match s.memory.activeCallee with
      | .some _ => wpExecFallback zeroVal ctx post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => wpExecFallback zeroVal ctx post (fuel' + 1) (.running s)
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => wpExecFallback zeroVal ctx post (fuel' + 1) (.running s)
          | true =>
            evalSymNodeTree
              (wpCfgStep zeroVal ctx post fuel' (.some (blockIdx, Nat.add stmtIdx 1, rest, term)))
              post
              (evalStmtSymTreeFast ctx s stmt)

private abbrev wpBlockLinear
    (zeroVal : Prop) (ctx : BlockCtx)
    (term : Terminator) (post : MirOutcome → Prop)
    (blockIdx stmtIdx fuel : Nat)
    (stmts : List Statement) (locals : List LocalSlot) (mem : Memory) : Prop :=
  wpCfgStep zeroVal ctx post fuel (.some (blockIdx, stmtIdx, stmts, term))
    (.running { frame := { blockIdx := blockIdx, stmtIdx := stmtIdx, locals := locals }, memory := mem })

private theorem wpCfgStep_eq
    (zeroVal : Prop) (ctx : BlockCtx)
    (post : MirOutcome → Prop)
    (h_ld : ctx.localDecls = ctx.body.localDecls)
    (h_lay : ctx.layouts = ctx.body.layouts)
    (h_phase : ctx.body.phase = .runtimeOptimized) :
    ∀ (fuel : Nat) (cur : Option (Nat × Nat × List Statement × Terminator))
      (st : MirExecState),
      (∀ bIdx sIdx stmts term,
        cur = .some (bIdx, sIdx, stmts, term) →
        ∃ bb pfx,
          get? ctx.body.basicBlocks bIdx = some bb ∧
          sIdx = length pfx ∧
          bb.statements = pfx ++ stmts ∧
          term = bb.terminator) →
      wpExecGen zeroVal ctx post fuel st =
        wpCfgStep zeroVal ctx post fuel cur st := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel' ih =>
    intro cur st h_cur
    cases st with
    | halted _ =>
      cases cur with
      | none => rfl
      | some tup => rcases tup with ⟨_, _, stmts, _⟩; cases stmts <;> rfl
    | faulted _ =>
      cases cur with
      | none => rfl
      | some tup => rcases tup with ⟨_, _, stmts, _⟩; cases stmts <;> rfl
    | running s =>
      cases cur with
      | none =>
        dsimp only [wpCfgStep, wpExecFallback]
        cases h_ac : s.memory.activeCallee with
        | some _ => rfl
        | none =>
          dsimp only
          cases h_si : Nat.beq s.frame.stmtIdx 0 with
          | false => rfl
          | true =>
            dsimp only [lookupBlock]
            have h_si_eq : s.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_si
            dsimp only [wpExecGen, stepMirSymTreeFast]
            rw [h_ac]
            dsimp only
            rw [h_phase]
            dsimp only
            cases h_bb : get? ctx.body.basicBlocks s.frame.blockIdx with
            | none =>
              dsimp only [evalSymNodeTree, MirStepNode.fail, dispatchBlock]
            | some bb =>
              rcases bb with ⟨stmts, term, isCleanup⟩
              dsimp only
              rw [h_si_eq]
              cases stmts with
              | nil =>
                dsimp only [dispatchBlock, get?, length, BEq.beq, instBEqOfDecidableEq, Nat.decEq, instDecidableEqNat, decide]
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                exact ih .none st' (fun _ _ _ _ h => nomatch h)
              | cons stmt rest =>
                dsimp only [dispatchBlock, get?]
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                refine ih (.some (s.frame.blockIdx, 1, rest, term)) st' ?_
                intro bIdx sIdx stmts' term' h_some
                injection h_some with h_tup
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup with ⟨rfl, h_tup2⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup2 with ⟨rfl, h_tup3⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup3 with ⟨rfl, rfl⟩
                exact ⟨⟨stmt :: rest, term, isCleanup⟩, [stmt], h_bb, rfl, rfl, rfl⟩
      | some tup =>
        rcases tup with ⟨blockIdx, stmtIdx, stmts, term⟩
        rcases h_cur blockIdx stmtIdx stmts term rfl with ⟨bb, pfx, h_bb, rfl, h_stmts, rfl⟩
        cases stmts with
        | nil =>
          dsimp only [wpCfgStep, wpExecFallback]
          cases h_ac : s.memory.activeCallee with
          | some _ => rfl
          | none =>
            dsimp only
            cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
            | false => rfl
            | true =>
              dsimp only
              cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
              | false => rfl
              | true =>
                dsimp only
                have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
                have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
                have h_eq : bb.statements = pfx := by simpa using h_stmts
                subst h_eq
                dsimp only [wpExecGen, stepMirSymTreeFast]
                rw [h_ac]
                dsimp only
                rw [h_phase]
                dsimp only
                rw [h_bi_eq, h_bb]
                dsimp only
                rw [h_si_eq, get?_length_none]
                dsimp only
                have h_beq : (length bb.statements == length bb.statements) = true :=
                  beq_self_eq_true _
                rw [h_beq]
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                exact ih .none st' (fun _ _ _ _ h => nomatch h)
        | cons stmt rest =>
          dsimp only [wpCfgStep, wpExecFallback]
          cases h_ac : s.memory.activeCallee with
          | some _ => rfl
          | none =>
            dsimp only
            cases h_bi : Nat.beq s.frame.blockIdx blockIdx with
            | false => rfl
            | true =>
              dsimp only
              cases h_si : Nat.beq s.frame.stmtIdx (length pfx) with
              | false => rfl
              | true =>
                dsimp only
                have h_bi_eq : s.frame.blockIdx = blockIdx := Nat.eq_of_beq_eq_true h_bi
                have h_si_eq : s.frame.stmtIdx = length pfx := Nat.eq_of_beq_eq_true h_si
                dsimp only [wpExecGen, stepMirSymTreeFast]
                rw [h_ac]
                dsimp only
                rw [h_phase]
                dsimp only
                rw [h_bi_eq, h_bb]
                dsimp only
                rw [h_si_eq, h_stmts, get?_append_cons]
                dsimp only
                apply congrArg (fun k => evalSymNodeTree k post _)
                funext st'
                refine ih (.some (blockIdx, Nat.add (length pfx) 1, rest, bb.terminator)) st' ?_
                intro bIdx sIdx stmts' term' h_some
                injection h_some with h_tup
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup with ⟨rfl, h_tup2⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup2 with ⟨rfl, h_tup3⟩
                rcases Prod.mk.injEq _ _ _ _ ▸ h_tup3 with ⟨rfl, rfl⟩
                refine ⟨bb, pfx ++ [stmt], h_bb, ?_, by simp [h_stmts, List.append_assoc], rfl⟩
                exact (length_append_singleton pfx stmt).symm

private theorem wpStartBlock0_eq
    (zeroVal : Prop) (ctx : BlockCtx) (bb : BasicBlockData)
    (post : MirOutcome → Prop) (fuel : Nat) (args : List Value)
    (h_ld : ctx.localDecls = ctx.body.localDecls)
    (h_lay : ctx.layouts = ctx.body.layouts)
    (h_phase : ctx.body.phase = .runtimeOptimized)
    (h_bb : get? ctx.body.basicBlocks 0 = some bb) :
    wpExecGen zeroVal ctx post fuel (.running (initMachineState ctx.body args)) =
      wpBlockLinear zeroVal ctx bb.terminator post
        0 0 fuel bb.statements (initLocalsAux 0 ctx.body.localDecls args)
        (initMachineState ctx.body args).memory := by
  refine wpCfgStep_eq zeroVal ctx post h_ld h_lay h_phase fuel
    (.some (0, 0, bb.statements, bb.terminator))
    (.running (initMachineState ctx.body args)) ?_
  intro bIdx sIdx stmts term h_some
  injection h_some with h_tup
  rcases Prod.mk.injEq _ _ _ _ ▸ h_tup with ⟨rfl, h_tup2⟩
  rcases Prod.mk.injEq _ _ _ _ ▸ h_tup2 with ⟨rfl, h_tup3⟩
  rcases Prod.mk.injEq _ _ _ _ ▸ h_tup3 with ⟨rfl, rfl⟩
  exact ⟨bb, [], h_bb, rfl, rfl, rfl⟩

private def boolTruePost : MirOutcome → Prop :=
  fun out =>
    ∀ retVal mem',
      out = .normal (retVal, mem') →
      retVal = .scalar { bits := 1, sizeBytes := 1 }

private theorem boolTruePost_normal_one (mem' : Memory) :
    boolTruePost (.normal (.scalar { bits := 1, sizeBytes := 1 }, mem')) := by
  intro retVal _ h
  injection h with hp
  injection hp with hv _
  exact hv.symm

private theorem mirBoolPredicateHolds_of_wpMirSym_true
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h : wpMirSym fuel specBody (initMachineState specBody args) boolTruePost) :
    MirBoolPredicateHolds specBody args :=
  (mirBoolPredicateHolds_iff_dwlp specBody args).2 (dwlp_of_wpMirSym h)


private def dummyBB : BasicBlockData :=
  { statements := [], terminator := { kind := .unreachable, span := "" }, isCleanup := false }


private def ensBB0 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.basicBlocks 0).getD dummyBB
private def ensBB1 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.basicBlocks 1).getD dummyBB
private def ensBB2 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.basicBlocks 2).getD dummyBB
private def ensBB3 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.basicBlocks 3).getD dummyBB
private def ensBB4 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.basicBlocks 4).getD dummyBB
private def ensBB5 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.basicBlocks 5).getD dummyBB
private def ensBB6 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.basicBlocks 6).getD dummyBB

private def ensCtx : BlockCtx :=
  { localDecls := Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.localDecls
    layouts := Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.layouts
    body := Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body }

private theorem ensCtx_localDecls :
    ensCtx.localDecls = Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.localDecls := rfl
private theorem ensCtx_layouts :
    ensCtx.layouts = Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.layouts := rfl
private theorem ensCtx_body_layouts :
    ensCtx.body.layouts = Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.layouts := rfl
private theorem ensCtx_phase :
    ensCtx.body.phase = .runtimeOptimized := rfl
private theorem ensCtx_bb1 :
    lookupBlock ensCtx 1 = some ensBB1 := rfl
private theorem ensCtx_bb2 :
    lookupBlock ensCtx 2 = some ensBB2 := rfl
private theorem ensCtx_bb3 :
    lookupBlock ensCtx 3 = some ensBB3 := rfl
private theorem ensCtx_bb4 :
    lookupBlock ensCtx 4 = some ensBB4 := rfl
private theorem ensCtx_bb5 :
    lookupBlock ensCtx 5 = some ensBB5 := rfl
private theorem ensCtx_bb6 :
    lookupBlock ensCtx 6 = some ensBB6 := rfl

private theorem hold_mirBool_ensures
    (fuel : Nat) (args : List Value)
    (h : Hold
      (wpBlockLinear False ensCtx ensBB0.terminator
        boolTruePost 0 0 fuel ensBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body.localDecls args)
        emptyMemory)) :
    Hold
      (MirBoolPredicateHolds
        Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body args) := by
  refine ⟨mirBoolPredicateHolds_of_wpMirSym_true fuel _ args ?_⟩
  unfold wpMirSym
  change wpMirExecSym fuel ensCtx.body (MirExecState.running (initMachineState ensCtx.body args)) boolTruePost
  rw [wpMirExecSym_eq_gen fuel ensCtx _ _ rfl rfl,
      wpStartBlock0_eq False ensCtx ensBB0 _ fuel args rfl rfl rfl rfl]
  exact h.val

private theorem mod_1_2 : 1 % 2 = 1 := rfl
private theorem bitwiseAndBits_8_1_0 : bitwiseAndBits 8 1 0 = 0 := rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
private theorem ensures_holds (b1 b2 ret : Nat)
    (h_ret : (b1 ≤ b2 ∧ ret = b1) ∨ (b2 < b1 ∧ ret = b2)) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body
      [.scalar { bits := b1, sizeBytes := 2 },
       .scalar { bits := b2, sizeBytes := 2 },
       .scalar { bits := ret, sizeBytes := 2 }] := by
  apply Hold.val
  refine hold_mirBool_ensures 110 _ ?_
  dsimp only [
    Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
    Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
    ensCtx_localDecls, ensCtx_layouts, ensCtx_body_layouts, ensCtx_phase,
    ensBB0,
    wpBlockLinear, wpCfgStep, dispatchBlock, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast,
    evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
    operandIsSigned, operandTy, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
    scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
    mul_1_8, mul_2_8, mul_4_8, mul_8_8,
    evalTerminatorSymTreeFast,
    lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initLocalsAux, emptyMemory,
    readProjectedValue_nil, readProjectedValue_field,
    ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
    projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
    byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
    isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
    invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
    boolToScalar,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  rcases h_ret with ⟨h_le, h_eq⟩ | ⟨h_gt, h_eq⟩
  · have h_ble12 : Nat.ble b1 b2 = true := Nat.ble_eq_true_of_le h_le
    have h_ble11 : Nat.ble b1 b1 = true := Nat.ble_eq_true_of_le (Nat.le_refl b1)
    have h_beq11 : Nat.beq b1 b1 = true := Nat.beq_refl b1
    rw [h_eq, h_ble12]
    dsimp only [
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
      ensCtx_localDecls, ensCtx_layouts, ensCtx_body_layouts, ensCtx_phase,
      ensCtx_bb1, ensBB1,
      wpCfgStep, dispatchBlock, evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast,
      evalOperandFast, evalOperandsFast, evalConstValue,
      evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
      operandIsSigned, operandTy, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8,
      evalTerminatorSymTreeFast,
      lookupSwitchTargetTree, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      readProjectedValue_nil, readProjectedValue_field,
      ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
      projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
      byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
      isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
      invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
      boolToScalar,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    rw [h_ble11]
    dsimp only [
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
      ensCtx_localDecls, ensCtx_layouts, ensCtx_body_layouts, ensCtx_phase,
      ensCtx_bb2, ensBB2,
      wpCfgStep, dispatchBlock, evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast,
      evalOperandFast, evalOperandsFast, evalConstValue,
      evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8,
      evalTerminatorSymTreeFast,
      lookupSwitchTargetTree, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      readProjectedValue_nil, readProjectedValue_field,
      ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
      projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
      byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
      isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
      invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
      boolToScalar,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    rw [h_beq11]
    dsimp only [
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
      ensCtx_localDecls, ensCtx_layouts, ensCtx_body_layouts, ensCtx_phase,
      ensCtx_bb4, ensBB4, ensCtx_bb6, ensBB6,
      wpCfgStep, dispatchBlock, evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast,
      evalOperandFast, evalOperandsFast, evalConstValue,
      evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8,
      evalTerminatorSymTreeFast,
      lookupSwitchTargetTree, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      readProjectedValue_nil, readProjectedValue_field,
      ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
      projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
      byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
      isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
      invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
      boolToScalar,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    exact ⟨boolTruePost_normal_one _⟩
  · have h_ble22 : Nat.ble b2 b2 = true := Nat.ble_eq_true_of_le (Nat.le_refl b2)
    have h_ble21 : Nat.ble b2 b1 = true := Nat.ble_eq_true_of_le (Nat.le_of_lt h_gt)
    have h_beq21 : Nat.beq b2 b1 = false := by
      cases h : Nat.beq b2 b1
      · rfl
      · have := Nat.eq_of_beq_eq_true h; omega
    have h_beq22 : Nat.beq b2 b2 = true := Nat.beq_refl b2
    rw [h_eq, h_ble22]
    dsimp only [
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
      ensCtx_localDecls, ensCtx_layouts, ensCtx_body_layouts, ensCtx_phase,
      ensCtx_bb1, ensBB1,
      wpCfgStep, dispatchBlock, evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast,
      evalOperandFast, evalOperandsFast, evalConstValue,
      evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
      operandIsSigned, operandTy, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8,
      evalTerminatorSymTreeFast,
      lookupSwitchTargetTree, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      readProjectedValue_nil, readProjectedValue_field,
      ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
      projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
      byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
      isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
      invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
      boolToScalar,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    rw [h_ble21]
    dsimp only [
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
      ensCtx_localDecls, ensCtx_layouts, ensCtx_body_layouts, ensCtx_phase,
      ensCtx_bb2, ensBB2,
      wpCfgStep, dispatchBlock, evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast,
      evalOperandFast, evalOperandsFast, evalConstValue,
      evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8,
      evalTerminatorSymTreeFast,
      lookupSwitchTargetTree, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      readProjectedValue_nil, readProjectedValue_field,
      ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
      projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
      byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
      isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
      invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
      boolToScalar,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    rw [h_beq21]
    dsimp only [
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
      ensCtx_localDecls, ensCtx_layouts, ensCtx_body_layouts, ensCtx_phase,
      ensCtx_bb5, ensBB5, ensCtx_bb6, ensBB6,
      wpCfgStep, dispatchBlock, evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast,
      evalOperandFast, evalOperandsFast, evalConstValue,
      evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8,
      evalTerminatorSymTreeFast,
      lookupSwitchTargetTree, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      readProjectedValue_nil, readProjectedValue_field,
      ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
      projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
      byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
      isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
      invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
      boolToScalar,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    rw [h_beq22]
    exact ⟨boolTruePost_normal_one _⟩

private def reqBB0 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.basicBlocks 0).getD dummyBB
private def reqBB1 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.basicBlocks 1).getD dummyBB
private def reqBB2 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.basicBlocks 2).getD dummyBB
private def reqBB3 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.basicBlocks 3).getD dummyBB

private def reqCtx : BlockCtx :=
  { localDecls := Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.localDecls
    layouts := Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.layouts
    body := Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body }

private theorem reqCtx_localDecls :
    reqCtx.localDecls = Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.localDecls := rfl
private theorem reqCtx_layouts :
    reqCtx.layouts = Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.layouts := rfl
private theorem reqCtx_body_layouts :
    reqCtx.body.layouts = Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.layouts := rfl
private theorem reqCtx_phase :
    reqCtx.body.phase = .runtimeOptimized := rfl
private theorem reqCtx_bb1 :
    lookupBlock reqCtx 1 = some reqBB1 := rfl
private theorem reqCtx_bb2 :
    lookupBlock reqCtx 2 = some reqBB2 := rfl
private theorem reqCtx_bb3 :
    lookupBlock reqCtx 3 = some reqBB3 := rfl

private theorem holdBoolReq_of_mirBoolPredicateHolds
    (fuel : Nat) (args : List Value)
    (h : MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body args) :
    Hold
      (wpBlockLinear True reqCtx reqBB0.terminator
        (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
        0 0 fuel reqBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.localDecls args)
        emptyMemory) := by
  refine ⟨?_⟩
  change wpBlockLinear True reqCtx reqBB0.terminator _ 0 0 fuel reqBB0.statements
    (initLocalsAux 0 reqCtx.body.localDecls args) (initMachineState reqCtx.body args).memory
  rw [← wpStartBlock0_eq True reqCtx reqBB0 _ fuel args rfl rfl rfl rfl,
      ← wpMirExecOrExhaustedSym_eq_gen fuel reqCtx _ _ rfl rfl]
  exact holdBoolMirSym_of_mirBoolPredicateHolds fuel _ args h

private theorem hold_mirBool_req
    (fuel : Nat) (args : List Value)
    (h : Hold
      (wpBlockLinear False reqCtx reqBB0.terminator
        boolTruePost 0 0 fuel reqBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.localDecls args)
        emptyMemory)) :
    Hold
      (MirBoolPredicateHolds
        Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body args) := by
  refine ⟨mirBoolPredicateHolds_of_wpMirSym_true fuel _ args ?_⟩
  unfold wpMirSym
  change wpMirExecSym fuel reqCtx.body (MirExecState.running (initMachineState reqCtx.body args)) boolTruePost
  rw [wpMirExecSym_eq_gen fuel reqCtx _ _ rfl rfl,
      wpStartBlock0_eq False reqCtx reqBB0 _ fuel args rfl rfl rfl rfl]
  exact h.val

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
private theorem wpReq_inversion (v1 v2 : Value) :
    Hold
      (wpBlockLinear True reqCtx reqBB0.terminator
        (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
        0 0 40 reqBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body.localDecls
          [v1, v2])
        emptyMemory) →
    ∃ b1 b2 : Nat,
      v1 = .scalar { bits := b1, sizeBytes := 2 } ∧
      v2 = .scalar { bits := b2, sizeBytes := 2 } ∧
      b1 ≤ 65535 ∧ b2 ≤ 1024 := by
  dsimp only [
    Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.layouts,
    Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body,
    reqCtx_localDecls, reqCtx_layouts, reqCtx_body_layouts, reqCtx_phase,
    reqBB0,
    wpBlockLinear, wpCfgStep, dispatchBlock, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast,
    evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
    operandIsSigned, operandTy, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
    scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
    mul_1_8, mul_2_8, mul_4_8, mul_8_8,
    evalTerminatorSymTreeFast,
    lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initLocalsAux, emptyMemory, mirSafePost,
    readProjectedValue_nil, readProjectedValue_field,
    ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
    projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
    byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
    isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
    invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
    boolToScalar,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  rcases v1 with _ | ⟨b1, sz1⟩ | ⟨p1, psz1⟩ | ⟨vid1, flds1⟩
  · intro h; exact False.elim h.val
  · dsimp only [finishAssignSymTree, evalSymNodeTree]
    cases h_sz1_0 : Nat.beq sz1 0 with
    | true =>
      intro h; exact False.elim h.val
    | false =>
      cases h_sz1_2 : Nat.beq sz1 2 with
      | false =>
        intro h; exact False.elim h.val
      | true =>
        cases h_ble1 : Nat.ble b1 65535 with
        | false =>
          dsimp only [
            Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.layouts,
            Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body,
            reqCtx_localDecls, reqCtx_layouts, reqCtx_body_layouts, reqCtx_phase,
            reqCtx_bb2, reqCtx_bb3,
            reqBB2, reqBB3,
            wpBlockLinear, wpCfgStep, dispatchBlock, evalSymNodeTree,
            evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
            evalRvalueSymTreeFast,
            evalOperandFast, evalOperandsFast, evalConstValue,
            evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
            scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
            mul_1_8, mul_2_8, mul_4_8, mul_8_8,
            evalTerminatorSymTreeFast,
            lookupSwitchTargetTree, applyUnwindAction,
            MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
            mirSafePost,
            readProjectedValue_nil, readProjectedValue_field,
            ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
            projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
            byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
            isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
            invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
            boolToScalar,
            GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
            HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
            List.replicate, List.append, List.length, List.set, List.map, Option.getD,
            get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
            ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
            Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
          intro h
          rcases h with ⟨h_val⟩
          injection h_val with h_sc
          injection h_sc with h_bits _
          nomatch h_bits
        | true =>
          dsimp only [
            Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.layouts,
            Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body,
            reqCtx_localDecls, reqCtx_layouts, reqCtx_body_layouts, reqCtx_phase,
            reqCtx_bb1,
            reqBB1,
            wpBlockLinear, wpCfgStep, dispatchBlock, evalSymNodeTree,
            evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
            evalRvalueSymTreeFast,
            evalOperandFast, evalOperandsFast, evalConstValue,
            evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
            operandIsSigned, operandTy, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
            scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
            mul_1_8, mul_2_8, mul_4_8, mul_8_8,
            evalTerminatorSymTreeFast,
            lookupSwitchTargetTree, applyUnwindAction,
            MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
            mirSafePost,
            readProjectedValue_nil, readProjectedValue_field,
            ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
            projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
            byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
            isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
            invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
            boolToScalar,
            GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
            HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
            List.replicate, List.append, List.length, List.set, List.map, Option.getD,
            get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
            ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
            Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
          rcases v2 with _ | ⟨b2, sz2⟩ | ⟨p2, psz2⟩ | ⟨vid2, flds2⟩
          · intro h; exact False.elim h.val
          · dsimp only [finishAssignSymTree, evalSymNodeTree]
            cases h_sz2_0 : Nat.beq sz2 0 with
            | true =>
              intro h; exact False.elim h.val
            | false =>
              cases h_sz2_2 : Nat.beq sz2 2 with
              | false =>
                intro h; exact False.elim h.val
              | true =>
                cases h_ble2 : Nat.ble b2 1024 with
                | false =>
                  dsimp only [
                    Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.layouts,
                    Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body,
                    reqCtx_localDecls, reqCtx_layouts, reqCtx_body_layouts, reqCtx_phase,
                    reqCtx_bb2, reqCtx_bb3,
                    reqBB2, reqBB3,
                    wpBlockLinear, wpCfgStep, dispatchBlock, evalSymNodeTree,
                    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
                    evalRvalueSymTreeFast,
                    evalOperandFast, evalOperandsFast, evalConstValue,
                    evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
                    scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
                    mul_1_8, mul_2_8, mul_4_8, mul_8_8,
                    evalTerminatorSymTreeFast,
                    lookupSwitchTargetTree, applyUnwindAction,
                    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
                    mirSafePost,
                    readProjectedValue_nil, readProjectedValue_field,
                    ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
                    projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
                    byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
                    isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
                    invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
                    boolToScalar,
                    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
                    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
                    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
                    get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
                    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
                    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
                  intro h
                  rcases h with ⟨h_val⟩
                  injection h_val with h_sc
                  injection h_sc with h_bits _
                  nomatch h_bits
                | true =>
                  intro _
                  exact ⟨b1, b2,
                    by rw [Nat.eq_of_beq_eq_true h_sz1_2],
                    by rw [Nat.eq_of_beq_eq_true h_sz2_2],
                    Nat.le_of_ble_eq_true h_ble1,
                    Nat.le_of_ble_eq_true h_ble2⟩
          · intro h; exact False.elim h.val
          · intro h; exact False.elim h.val
  · intro h; exact False.elim h.val
  · intro h; exact False.elim h.val

private def clampBB0 : BasicBlockData :=
  (get? Mir.WireframeDemo.clamp_payload_window.body.basicBlocks 0).getD dummyBB
private def clampBB1 : BasicBlockData :=
  (get? Mir.WireframeDemo.clamp_payload_window.body.basicBlocks 1).getD dummyBB
private def clampBB2 : BasicBlockData :=
  (get? Mir.WireframeDemo.clamp_payload_window.body.basicBlocks 2).getD dummyBB
private def clampBB3 : BasicBlockData :=
  (get? Mir.WireframeDemo.clamp_payload_window.body.basicBlocks 3).getD dummyBB

private def clampCtx : BlockCtx :=
  { localDecls := Mir.WireframeDemo.clamp_payload_window.body.localDecls
    layouts := Mir.WireframeDemo.clamp_payload_window.body.layouts
    body := Mir.WireframeDemo.clamp_payload_window.body }

private theorem clampCtx_localDecls :
    clampCtx.localDecls = Mir.WireframeDemo.clamp_payload_window.body.localDecls := rfl
private theorem clampCtx_layouts :
    clampCtx.layouts = Mir.WireframeDemo.clamp_payload_window.body.layouts := rfl
private theorem clampCtx_body_layouts :
    clampCtx.body.layouts = Mir.WireframeDemo.clamp_payload_window.body.layouts := rfl
private theorem clampCtx_phase :
    clampCtx.body.phase = .runtimeOptimized := rfl
private theorem clampCtx_bb1 :
    lookupBlock clampCtx 1 = some clampBB1 := rfl
private theorem clampCtx_bb2 :
    lookupBlock clampCtx 2 = some clampBB2 := rfl
private theorem clampCtx_bb3 :
    lookupBlock clampCtx 3 = some clampBB3 := rfl

private theorem hold_wpClamp_full
    (fuel : Nat) (args : List Value) (post : MirOutcome → Prop)
    (h : Hold
      (wpBlockLinear False clampCtx clampBB0.terminator
        post 0 0 fuel clampBB0.statements
        (initLocalsAux 0 Mir.WireframeDemo.clamp_payload_window.body.localDecls args)
        emptyMemory)) :
    Hold (wpMirSym fuel Mir.WireframeDemo.clamp_payload_window.body
      (initMachineState Mir.WireframeDemo.clamp_payload_window.body args) post) := by
  refine ⟨?_⟩
  unfold wpMirSym
  change wpMirExecSym fuel clampCtx.body (MirExecState.running (initMachineState clampCtx.body args)) post
  rw [wpMirExecSym_eq_gen fuel clampCtx _ _ rfl rfl,
      wpStartBlock0_eq False clampCtx clampBB0 _ fuel args rfl rfl rfl rfl]
  exact h.val

/-- Universal verification certificate for `clamp_payload_window` across all
`requested : u16` and `max_window ≤ 1024`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.clamp_payload_window.claim := by
  refine verifyMirNoPanicSym _ 12 ?_
  intro args h_pre
  rcases h_pre with ⟨h_len, h_req⟩
  rcases args with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · nomatch h_len
  · nomatch h_len
  · rcases wpReq_inversion v1 v2 (holdBoolReq_of_mirBoolPredicateHolds 40 [v1, v2] h_req) with
      ⟨b1, b2, hv1, hv2, _hb1, _hb2⟩
    subst hv1; subst hv2
    apply Hold.val
    refine hold_wpClamp_full 12 _ _ ?_
    dsimp only [
      Mir.WireframeDemo.clamp_payload_window.layouts,
      Mir.WireframeDemo.clamp_payload_window.body,
      clampCtx_localDecls, clampCtx_layouts, clampCtx_body_layouts, clampCtx_phase,
      clampCtx_bb1, clampCtx_bb2, clampCtx_bb3,
      clampBB0, clampBB1, clampBB2, clampBB3,
      wpBlockLinear, wpCfgStep, dispatchBlock, evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast,
      evalOperandFast, evalOperandsFast, evalConstValue,
      evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
      operandIsSigned, operandTy, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8,
      evalTerminatorSymTreeFast,
      lookupSwitchTargetTree, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      initLocalsAux, emptyMemory, mirNormalPost,
      Obligations.WireframeDemo.clamp_payload_window.claim,
      Obligations.WireframeDemo.clamp_payload_window.defaultSpec,
      Obligations.WireframeDemo.clamp_payload_window.defaultPost,
      ItemSpec.post,
      readProjectedValue_nil, readProjectedValue_field,
      ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
      projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
      byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
      isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
      invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
      boolToScalar,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    cases h_ble : Nat.ble b1 b2 with
    | true =>
      exact ⟨ensures_holds b1 b2 b1 (Or.inl ⟨Nat.le_of_ble_eq_true h_ble, rfl⟩)⟩
    | false =>
      have h_gt : b2 < b1 := by
        have hnot : ¬ b1 ≤ b2 := fun hle => by
          rw [Nat.ble_eq_true_of_le hle] at h_ble
          nomatch h_ble
        omega
      exact ⟨ensures_holds b1 b2 b2 (Or.inr ⟨h_gt, rfl⟩)⟩
  · nomatch h_len

/-- Non-vacuity witness confirming `clamp_payload_window`'s `requires` contract
is satisfiable (`requested = 512`, `max_window = 1024`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.clamp_payload_window.rustRequires a := by
  refine ⟨[.scalar { bits := 512, sizeBytes := 2 }, .scalar { bits := 1024, sizeBytes := 2 }], ⟨rfl, ?_⟩⟩
  apply Hold.val
  refine hold_mirBool_req 40 _ ?_
  dsimp only [
    Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.layouts,
    Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body,
    reqCtx_localDecls, reqCtx_layouts, reqCtx_body_layouts, reqCtx_phase,
    reqCtx_bb1, reqCtx_bb2, reqCtx_bb3,
    reqBB0, reqBB1, reqBB2, reqBB3,
    wpBlockLinear, wpCfgStep, dispatchBlock, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast,
    evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
    operandIsSigned, operandTy, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
    scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
    mul_1_8, mul_2_8, mul_4_8, mul_8_8,
    evalTerminatorSymTreeFast,
    lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initLocalsAux, emptyMemory,
    readProjectedValue_nil, readProjectedValue_field,
    ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
    projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
    byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
    isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
    invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
    boolToScalar,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.ble, Nat.beq, Bool.and, Bool.or,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  exact ⟨boolTruePost_normal_one _⟩

end Proof.WireframeDemo.clamp_payload_window
