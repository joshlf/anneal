import Trusted
import Anneal
import Mir.WireframeDemo.frame_total_len
import Obligations.WireframeDemo.frame_total_len

namespace Proof.WireframeDemo.frame_total_len

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

private def wpBlockStep
    (zeroVal : Prop) (ctx : BlockCtx)
    (term : Terminator) (post : MirOutcome → Prop)
    (blockIdx : Nat) :
    Nat → Nat → List Statement → MirExecState → Prop
  | 0, _, _, _ => zeroVal
  | _ + 1, _, _, .halted out => post out
  | _ + 1, _, _, .faulted _ => False
  | fuel' + 1, stmtIdx, stmts, .running s =>
      match s.memory.activeCallee with
      | .some _ => wpExecGen zeroVal ctx post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => wpExecGen zeroVal ctx post (fuel' + 1) (.running s)
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => wpExecGen zeroVal ctx post (fuel' + 1) (.running s)
          | true =>
            match stmts with
            | [] =>
              evalSymNodeTree (wpExecGen zeroVal ctx post fuel') post
                (evalTerminatorSymTreeFast ctx s term)
            | stmt :: rest =>
              evalSymNodeTree
                (wpBlockStep zeroVal ctx term post blockIdx
                  fuel' (Nat.add stmtIdx 1) rest)
                post
                (evalStmtSymTreeFast ctx s stmt)

private abbrev wpBlockLinear
    (zeroVal : Prop) (ctx : BlockCtx)
    (term : Terminator) (post : MirOutcome → Prop)
    (blockIdx stmtIdx fuel : Nat)
    (stmts : List Statement) (locals : List LocalSlot) (mem : Memory) : Prop :=
  wpBlockStep zeroVal ctx term post blockIdx fuel stmtIdx stmts
    (.running { frame := { blockIdx := blockIdx, stmtIdx := stmtIdx, locals := locals }, memory := mem })

private theorem wpBlockStep_eq
    (zeroVal : Prop) (ctx : BlockCtx) (bb : BasicBlockData)
    (post : MirOutcome → Prop) (blockIdx : Nat)
    (h_ld : ctx.localDecls = ctx.body.localDecls)
    (h_lay : ctx.layouts = ctx.body.layouts)
    (h_phase : ctx.body.phase = .runtimeOptimized)
    (h_bb : get? ctx.body.basicBlocks blockIdx = some bb)
    (fuel : Nat) (pfx stmts : List Statement) (st : MirExecState)
    (h_stmts : bb.statements = pfx ++ stmts) :
    wpExecGen zeroVal ctx post fuel st =
      wpBlockStep zeroVal ctx bb.terminator post
        blockIdx fuel (length pfx) stmts st := by
  induction fuel generalizing pfx stmts st with
  | zero => rfl
  | succ fuel' ih =>
    cases st with
    | halted _ => rfl
    | faulted _ => rfl
    | running s =>
      dsimp only [wpBlockStep]
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
            cases stmts with
            | nil =>
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
              rfl
            | cons stmt rest =>
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
              have h_ih :=
                ih (pfx ++ [stmt]) rest st' (by simp [h_stmts, List.append_assoc])
              rw [length_append_singleton] at h_ih
              exact h_ih

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
        (initMachineState ctx.body args).memory :=
  wpBlockStep_eq zeroVal ctx bb post 0 h_ld h_lay h_phase h_bb fuel [] bb.statements
    (.running (initMachineState ctx.body args)) rfl

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
  (get? Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body.basicBlocks 0).getD dummyBB

private def ensBB1 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body.basicBlocks 1).getD dummyBB

private def ensCtx : BlockCtx :=
  { localDecls := Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body.localDecls
    layouts := Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body.layouts
    body := Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body }

private theorem ensCtx_localDecls :
    ensCtx.localDecls = Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body.localDecls := rfl
private theorem ensCtx_layouts :
    ensCtx.layouts = Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body.layouts := rfl
private theorem ensCtx_body_layouts :
    ensCtx.body.layouts = Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body.layouts := rfl
private theorem ensCtx_phase :
    ensCtx.body.phase = .runtimeOptimized := rfl
private theorem ensCtx_bb1 :
    get? ensCtx.body.basicBlocks 1 = some ensBB1 := rfl
private theorem ens_init_mem (args : List Value) :
    (initMachineState Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body args).memory = emptyMemory := rfl

private theorem hold_mirBool_ensures
    (fuel : Nat) (args : List Value)
    (h : Hold
      (wpBlockLinear False ensCtx ensBB0.terminator
        boolTruePost 0 0 fuel ensBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body.localDecls args)
        emptyMemory)) :
    Hold
      (MirBoolPredicateHolds
        Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body args) := by
  refine ⟨mirBoolPredicateHolds_of_wpMirSym_true fuel _ args ?_⟩
  unfold wpMirSym
  change wpMirExecSym fuel ensCtx.body (MirExecState.running (initMachineState ensCtx.body args)) boolTruePost
  rw [wpMirExecSym_eq_gen fuel ensCtx _ _ rfl rfl,
      wpStartBlock0_eq False ensCtx ensBB0 _ fuel args rfl rfl rfl rfl]
  exact h.val

private theorem mod_1_2 : 1 % 2 = 1 := rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
private theorem ensures_holds (b1 b2 : Nat) (hb1 : b1 ≤ 16) (hb2 : b2 ≤ 1024) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body
      [.scalar { bits := b1, sizeBytes := 2 },
       .scalar { bits := b2, sizeBytes := 2 },
       .scalar { bits := Nat.add b1 b2, sizeBytes := 2 }] := by
  apply Hold.val
  refine hold_mirBool_ensures 80 _ ?_
  dsimp only [
    Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.layouts,
    Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body,
    ensCtx_localDecls, ensCtx_layouts, ensCtx_body_layouts, ensCtx_phase, ensCtx_bb1, ens_init_mem,
    ensBB0, ensBB1,
    wpBlockLinear, wpBlockStep, wpExecGen, stepMirSymTreeFast, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast,
    evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, evalUnaryNotSymTree,
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
  have h_lt : Nat.add b1 b2 < 65536 := by
    rw [Nat.add_eq]
    omega
  have h_ble : Nat.ble 65536 (Nat.add b1 b2) = false := by
    cases h : Nat.ble 65536 (Nat.add b1 b2)
    · rfl
    · have := Nat.le_of_ble_eq_true h
      omega
  have h_wrap : wrapScalarBits (Nat.add b1 b2) 65536 = Nat.add b1 b2 := by
    unfold wrapScalarBits
    rw [h_ble]
  have h_beq : Nat.beq (Nat.add b1 b2) (Nat.add b1 b2) = true :=
    Nat.beq_refl (Nat.add b1 b2)
  rw [h_ble, h_wrap, h_beq]
  exact ⟨boolTruePost_normal_one _⟩

private def reqBB0 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.basicBlocks 0).getD dummyBB
private def reqBB1 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.basicBlocks 1).getD dummyBB
private def reqBB2 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.basicBlocks 2).getD dummyBB
private def reqBB3 : BasicBlockData :=
  (get? Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.basicBlocks 3).getD dummyBB

private def reqCtx : BlockCtx :=
  { localDecls := Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.localDecls
    layouts := Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.layouts
    body := Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body }

private theorem reqCtx_localDecls :
    reqCtx.localDecls = Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.localDecls := rfl
private theorem reqCtx_layouts :
    reqCtx.layouts = Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.layouts := rfl
private theorem reqCtx_body_layouts :
    reqCtx.body.layouts = Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.layouts := rfl
private theorem reqCtx_phase :
    reqCtx.body.phase = .runtimeOptimized := rfl
private theorem reqCtx_bb1 :
    get? reqCtx.body.basicBlocks 1 = some reqBB1 := rfl
private theorem reqCtx_bb2 :
    get? reqCtx.body.basicBlocks 2 = some reqBB2 := rfl
private theorem reqCtx_bb3 :
    get? reqCtx.body.basicBlocks 3 = some reqBB3 := rfl

private theorem holdBoolReq_of_mirBoolPredicateHolds
    (fuel : Nat) (args : List Value)
    (h : MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body args) :
    Hold
      (wpBlockLinear True reqCtx reqBB0.terminator
        (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
        0 0 fuel reqBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.localDecls args)
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
          Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.localDecls args)
        emptyMemory)) :
    Hold
      (MirBoolPredicateHolds
        Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body args) := by
  refine ⟨mirBoolPredicateHolds_of_wpMirSym_true fuel _ args ?_⟩
  unfold wpMirSym
  change wpMirExecSym fuel reqCtx.body (MirExecState.running (initMachineState reqCtx.body args)) boolTruePost
  rw [wpMirExecSym_eq_gen fuel reqCtx _ _ rfl rfl,
      wpStartBlock0_eq False reqCtx reqBB0 _ fuel args rfl rfl rfl rfl]
  exact h.val

private theorem bitwiseAndBits_8_1_0 : bitwiseAndBits 8 1 0 = 0 := rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
private theorem wpReq_inversion (v1 v2 : Value) :
    Hold
      (wpBlockLinear True reqCtx reqBB0.terminator
        (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
        0 0 40 reqBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body.localDecls
          [v1, v2])
        emptyMemory) →
    ∃ b1 b2 : Nat,
      v1 = .scalar { bits := b1, sizeBytes := 2 } ∧
      v2 = .scalar { bits := b2, sizeBytes := 2 } ∧
      b1 ≤ 16 ∧ b2 ≤ 1024 := by
  dsimp only [
    Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.layouts,
    Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body,
    reqCtx_localDecls, reqCtx_layouts, reqCtx_body_layouts, reqCtx_phase,
    reqCtx_bb1, reqCtx_bb2, reqCtx_bb3,
    reqBB0, reqBB1, reqBB2, reqBB3,
    wpBlockLinear, wpBlockStep, wpExecGen, stepMirSymTreeFast, evalSymNodeTree,
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
        cases h_ble1 : Nat.ble b1 16 with
        | false =>
          dsimp only [
            Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.layouts,
            Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body,
            reqCtx_localDecls, reqCtx_layouts, reqCtx_body_layouts, reqCtx_phase,
            reqCtx_bb1, reqCtx_bb2, reqCtx_bb3,
            reqBB0, reqBB1, reqBB2, reqBB3,
            wpBlockLinear, wpBlockStep, wpExecGen, stepMirSymTreeFast, evalSymNodeTree,
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
          intro h
          rcases h with ⟨h_val⟩
          injection h_val with h_sc
          injection h_sc with h_bits _
          nomatch h_bits
        | true =>
          dsimp only [
            Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.layouts,
            Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body,
            reqCtx_localDecls, reqCtx_layouts, reqCtx_body_layouts, reqCtx_phase,
            reqCtx_bb1, reqCtx_bb2, reqCtx_bb3,
            reqBB0, reqBB1, reqBB2, reqBB3,
            wpBlockLinear, wpBlockStep, wpExecGen, stepMirSymTreeFast, evalSymNodeTree,
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
                    Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.layouts,
                    Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body,
                    reqCtx_localDecls, reqCtx_layouts, reqCtx_body_layouts, reqCtx_phase,
                    reqCtx_bb1, reqCtx_bb2, reqCtx_bb3,
                    reqBB0, reqBB1, reqBB2, reqBB3,
                    wpBlockLinear, wpBlockStep, wpExecGen, stepMirSymTreeFast, evalSymNodeTree,
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

private def ftlBB0 : BasicBlockData :=
  (get? Mir.WireframeDemo.frame_total_len.body.basicBlocks 0).getD dummyBB
private def ftlBB1 : BasicBlockData :=
  (get? Mir.WireframeDemo.frame_total_len.body.basicBlocks 1).getD dummyBB

private def ftlCtx : BlockCtx :=
  { localDecls := Mir.WireframeDemo.frame_total_len.body.localDecls
    layouts := Mir.WireframeDemo.frame_total_len.body.layouts
    body := Mir.WireframeDemo.frame_total_len.body }

private theorem ftlCtx_localDecls :
    ftlCtx.localDecls = Mir.WireframeDemo.frame_total_len.body.localDecls := rfl
private theorem ftlCtx_layouts :
    ftlCtx.layouts = Mir.WireframeDemo.frame_total_len.body.layouts := rfl
private theorem ftlCtx_body_layouts :
    ftlCtx.body.layouts = Mir.WireframeDemo.frame_total_len.body.layouts := rfl
private theorem ftlCtx_phase :
    ftlCtx.body.phase = .runtimeOptimized := rfl
private theorem ftlCtx_bb1 :
    get? ftlCtx.body.basicBlocks 1 = some ftlBB1 := rfl

private theorem hold_wpFtl_full
    (fuel : Nat) (args : List Value) (post : MirOutcome → Prop)
    (h : Hold
      (wpBlockLinear False ftlCtx ftlBB0.terminator
        post 0 0 fuel ftlBB0.statements
        (initLocalsAux 0 Mir.WireframeDemo.frame_total_len.body.localDecls args)
        emptyMemory)) :
    Hold (wpMirSym fuel Mir.WireframeDemo.frame_total_len.body
      (initMachineState Mir.WireframeDemo.frame_total_len.body args) post) := by
  refine ⟨?_⟩
  unfold wpMirSym
  change wpMirExecSym fuel ftlCtx.body (MirExecState.running (initMachineState ftlCtx.body args)) post
  rw [wpMirExecSym_eq_gen fuel ftlCtx _ _ rfl rfl,
      wpStartBlock0_eq False ftlCtx ftlBB0 _ fuel args rfl rfl rfl rfl]
  exact h.val

/-- Universal verification certificate for `frame_total_len` across all valid
header and payload lengths (`0 ≤ header_len ≤ 16`, `0 ≤ payload_len ≤ 1024`). -/
theorem verified : VerificationResult Obligations.WireframeDemo.frame_total_len.claim := by
  refine verifyMirNoPanicSym _ 10 ?_
  intro args h_pre
  rcases h_pre with ⟨h_len, h_req⟩
  rcases args with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · nomatch h_len
  · nomatch h_len
  · rcases wpReq_inversion v1 v2 (holdBoolReq_of_mirBoolPredicateHolds 40 [v1, v2] h_req) with
      ⟨b1, b2, hv1, hv2, hb1, hb2⟩
    subst hv1; subst hv2
    apply Hold.val
    refine hold_wpFtl_full 10 _ _ ?_
    dsimp only [
      Mir.WireframeDemo.frame_total_len.layouts,
      Mir.WireframeDemo.frame_total_len.body,
      ftlCtx_localDecls, ftlCtx_layouts, ftlCtx_body_layouts, ftlCtx_phase, ftlCtx_bb1,
      ftlBB0, ftlBB1,
      wpBlockLinear, wpBlockStep, wpExecGen, stepMirSymTreeFast, evalSymNodeTree,
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
      Obligations.WireframeDemo.frame_total_len.claim,
      Obligations.WireframeDemo.frame_total_len.defaultSpec,
      Obligations.WireframeDemo.frame_total_len.defaultPost,
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
    have h_lt : Nat.add b1 b2 < 65536 := by
      rw [Nat.add_eq]
      omega
    have h_ble : Nat.ble 65536 (Nat.add b1 b2) = false := by
      cases h : Nat.ble 65536 (Nat.add b1 b2)
      · rfl
      · have := Nat.le_of_ble_eq_true h
        omega
    have h_wrap : wrapScalarBits (Nat.add b1 b2) 65536 = Nat.add b1 b2 := by
      unfold wrapScalarBits
      rw [h_ble]
    rw [h_ble, h_wrap]
    exact ⟨ensures_holds b1 b2 hb1 hb2⟩
  · nomatch h_len

/-- Non-vacuity witness confirming `frame_total_len`'s `requires` contract is
satisfiable (`header_len = 4`, `payload_len = 128`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.frame_total_len.rustRequires a := by
  refine ⟨[.scalar { bits := 4, sizeBytes := 2 }, .scalar { bits := 128, sizeBytes := 2 }], ⟨rfl, ?_⟩⟩
  apply Hold.val
  refine hold_mirBool_req 40 _ ?_
  dsimp only [
    Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.layouts,
    Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body,
    reqCtx_localDecls, reqCtx_layouts, reqCtx_body_layouts, reqCtx_phase,
    reqCtx_bb1, reqCtx_bb2, reqCtx_bb3,
    reqBB0, reqBB1, reqBB2, reqBB3,
    wpBlockLinear, wpBlockStep, wpExecGen, stepMirSymTreeFast, evalSymNodeTree,
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

end Proof.WireframeDemo.frame_total_len
