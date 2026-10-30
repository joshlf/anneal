import Trusted
import Anneal
import Mir.WireframeDemo.parse_compression_flag
import Specs.WireframeDemo.parse_compression_flag
import Obligations.WireframeDemo.parse_compression_flag

namespace Proof.WireframeDemo.parse_compression_flag

set_option linter.all false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.parse_compression_flag

/-!
Kernel-checked review proof for `wireframe_demo::parse_compression_flag`
(Journey 3B, `#125`).

Verifies `refineSafeSpec` (`MirContractHoldsWithSafety`):
1. Safe `parse_compression_flag` executes without Undefined Behavior across all
   `256` `u8` inputs (`0..=255`), including values `2..=255` outside `requires`.
2. Whenever `rustRequires` holds (`(flags_byte & 1) == flags_byte`, i.e. `0` or
   `1`), both the Rust `#[anneal_spec::spec]` `ensures` clause and
   `compressionFlagPost` hold.
3. `rustRequires` is provably non-vacuous (`nonVacuousRequires`).
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

private def evalOperandFast (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) : PlaceReadResult :=
  match op with
  | .constant c =>
    match c.val with
    | .indirect _ _ => evalOperandFallback locals (.constant c) borrows globals layouts callerLocals
    | .slice _ _ => evalOperandFallback locals (.constant c) borrows globals layouts callerLocals
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
    | _ => evalOperandFallback locals (.move p) borrows globals layouts callerLocals

private theorem evalOperandFast_eq (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) :
    evalOperandFast locals op borrows globals layouts callerLocals =
      evalOperand locals op borrows globals layouts callerLocals := by
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
    cases proj <;> rfl

private def evalOperandsFast
    (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) : OperandsEvalResult :=
  match ops with
  | .nil => .ok .nil locals
  | op :: rest =>
    match evalOperandFast locals op borrows globals layouts callerLocals with
    | .ok v locals₁ =>
      match evalOperandsFast locals₁ rest borrows globals layouts callerLocals with
      | .ok vs locals₂ => .ok (v :: vs) locals₂
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported

private theorem evalOperandsFast_eq
    (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) :
    evalOperandsFast locals ops borrows globals layouts callerLocals =
      evalOperands locals ops borrows globals layouts callerLocals := by
  induction ops generalizing locals with
  | nil => rfl
  | cons op rest ih =>
    change
      (match evalOperandFast locals op borrows globals layouts callerLocals with
       | .ok v locals₁ =>
         match evalOperandsFast locals₁ rest borrows globals layouts callerLocals with
         | .ok vs locals₂ => OperandsEvalResult.ok (v :: vs) locals₂
         | .ub => OperandsEvalResult.ub
         | .unsupported => OperandsEvalResult.unsupported
       | .ub => OperandsEvalResult.ub
       | .unsupported => OperandsEvalResult.unsupported) =
      (match evalOperand locals op borrows globals layouts callerLocals with
       | .ok v locals₁ =>
         match evalOperands locals₁ rest borrows globals layouts callerLocals with
         | .ok vs locals₂ => OperandsEvalResult.ok (v :: vs) locals₂
         | .ub => OperandsEvalResult.ub
         | .unsupported => OperandsEvalResult.unsupported
       | .ub => OperandsEvalResult.ub
       | .unsupported => OperandsEvalResult.unsupported)
    rw [evalOperandFast_eq]
    cases evalOperand locals op borrows globals layouts callerLocals with
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
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : SymTree RvalueEvalResult :=
  match rv with
  | .use op =>
    match evalOperandFast locals op mem.borrows mem.globals layouts mem.callerLocals with
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
    | _, _ => .leaf (evalRvalueFallback locals (.ref bk p) mem localDecls layouts)
  | .aggregate ak ops =>
    match ak with
    | .tuple =>
      match evalOperandsFast locals ops mem.borrows mem.globals layouts mem.callerLocals with
      | .ok vals locals' => .leaf (.ok (.aggregate 0 vals) locals' mem)
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | _ => .leaf (evalRvalueFallback locals (.aggregate ak ops) mem localDecls layouts)
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandFast locals lhsOp mem.borrows mem.globals layouts mem.callerLocals with
    | .ok lhsVal locals₁ =>
      match evalOperandFast locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          let isSigned := operandIsSigned localDecls lhsOp layouts
          match op with
          | .bitAnd =>
            .branch (Nat.beq lhs.sizeBytes 0) (.leaf .unsupported)
              (.branch (Nat.beq lhs.sizeBytes rhs.sizeBytes)
                (.leaf (.ok (.scalar ⟨bitwiseAndBitsFast (Nat.mul lhs.sizeBytes 8) lhs.bits rhs.bits, lhs.sizeBytes⟩) locals₂ mem))
                (.leaf .unsupported))
          | _ => evalScalarBinOpSymTree op lhs rhs locals₂ mem isSigned
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
      match evalOperandFast locals op mem.borrows mem.globals layouts mem.callerLocals with
      | .ok (.scalar sc) locals' =>
        evalUnaryNotSymTree sc (operandTy localDecls layouts op) locals' mem
      | .ok _ _ => .leaf .unsupported
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | _ => .leaf (evalRvalueFallback locals (.unaryOp uop op) mem localDecls layouts)
  | _ => .leaf (evalRvalueFallback locals rv mem localDecls layouts)

private theorem evalRvalueSymTreeFast_eq
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalueSymTreeFast locals rv mem localDecls layouts =
      evalRvalueSymTree locals rv mem localDecls layouts := by
  cases rv with
  | use op =>
    dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree, evalRvalue]
    rw [evalOperandFast_eq]
    cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals <;> rfl
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
      cases evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals <;> rfl
    | _ => rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree]
    rw [evalOperandFast_eq]
    cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [evalOperandFast_eq]
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals with
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
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
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
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : SymTree MirStepNode :=
  match stmt.kind with
  | .assign dst rv =>
    finishAssignSymTree s dst
      (evalRvalueSymTreeFast s.frame.locals rv s.memory localDecls layouts)
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
  | _ => .leaf (evalStmtFallback s stmt localDecls layouts)

private theorem evalStmtSymTreeFast_eq
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmtSymTreeFast s stmt localDecls layouts =
      evalStmtSymTree s stmt localDecls layouts := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    show finishAssignSymTree s dst (evalRvalueSymTreeFast s.frame.locals rv s.memory localDecls layouts) =
      (evalRvalueSymTree s.frame.locals rv s.memory localDecls layouts).bind _
    rw [finishAssignSymTree_eq, evalRvalueSymTreeFast_eq]
  | _ => rfl

private def evalTerminatorFallback (s : MachineState) (term : Terminator)
    (currentBody : CapturedMir) : SymTree MirStepNode :=
  evalTerminatorSymTree s term currentBody

private def evalTerminatorSymTreeFast
    (s : MachineState) (term : Terminator) (currentBody : CapturedMir) : SymTree MirStepNode :=
  match term.kind with
  | .goto target =>
    .leaf (MirStepNode.step { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } })
  | .return_ =>
    match s.memory.callStack with
    | .nil =>
      match get? s.frame.locals 0 with
      | .some (.init retVal) => .leaf (MirStepNode.retNormal retVal s.memory)
      | _ => .leaf (MirStepNode.fail .ub)
    | _ :: _ => evalTerminatorFallback s term currentBody
  | .switchInt discr targets =>
    match evalOperandFast s.frame.locals discr s.memory.borrows s.memory.globals currentBody.layouts s.memory.callerLocals with
    | .ok (.scalar sc) locals' =>
      (lookupSwitchTargetTree sc.bits targets.branches targets.otherwise).bind
        (fun target =>
          .leaf (.vis (.inr (.inl (.emit (.event sc.bits))))
            (fun _ => .running { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } })))
    | .ok _ _ => .leaf (MirStepNode.fail .ub)
    | .ub => .leaf (MirStepNode.fail .ub)
    | .unsupported => .leaf MirStepNode.unsupported
  | .assert cond expected target unwind =>
    match evalOperandFast s.frame.locals cond s.memory.borrows s.memory.globals currentBody.layouts s.memory.callerLocals with
    | .ok (.scalar sc) locals' =>
      let expectedBit := match expected with | true => 1 | false => 0
      .branch (Nat.beq sc.bits expectedBit)
        (.leaf (MirStepNode.step { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }))
        (.leaf
          (match applyUnwindAction s locals' s.memory unwind with
          | .running nextState => MirStepNode.step nextState
          | .halted out => .ret out
          | .faulted fk => MirStepNode.fail fk))
    | _ => evalTerminatorFallback s term currentBody
  | _ => evalTerminatorFallback s term currentBody

private theorem evalTerminatorSymTreeFast_eq
    (s : MachineState) (term : Terminator) (currentBody : CapturedMir) :
    evalTerminatorSymTreeFast s term currentBody =
      evalTerminatorSymTree s term currentBody := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | return_ =>
    show evalTerminatorSymTreeFast s { kind := .return_, span := span } currentBody =
      evalTerminatorSymTree s { kind := .return_, span := span } currentBody
    unfold evalTerminatorSymTreeFast evalTerminatorFallback evalTerminatorSymTree evalTerminator
    dsimp only
    cases s.memory.callStack with
    | nil =>
      cases get? s.frame.locals 0 with
      | none => rfl
      | some slot => cases slot <;> rfl
    | cons _ _ => rfl
  | switchInt discr targets =>
    show evalTerminatorSymTreeFast s { kind := .switchInt discr targets, span := span } currentBody =
      evalTerminatorSymTree s { kind := .switchInt discr targets, span := span } currentBody
    unfold evalTerminatorSymTreeFast evalTerminatorSymTree
    dsimp only
    rw [evalOperandFast_eq]
    rfl
  | assert cond expected target unwind =>
    unfold evalTerminatorSymTreeFast evalTerminatorFallback evalTerminatorSymTree
    dsimp only
    rw [evalOperandFast_eq]
    cases evalOperand s.frame.locals cond s.memory.borrows s.memory.globals currentBody.layouts s.memory.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok v _ => cases v <;> rfl
  | _ => rfl

private def wpExecGen (zeroVal : Prop) (body : CapturedMir) (post : MirOutcome → Prop)
    (fuel : Nat) (st : MirExecState) : Prop :=
  match fuel with
  | 0 => zeroVal
  | fuel' + 1 =>
    match st with
    | .running s =>
      evalSymNodeTree (wpExecGen zeroVal body post fuel') post (stepMirSymTree body s)
    | .halted out => post out
    | .faulted _ => False

private theorem wpMirExecSym_eq_gen
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) (post : MirOutcome → Prop) :
    wpMirExecSym fuel body st post = wpExecGen False body post fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    have h_fn : (fun st' => wpMirExecSym fuel' body st' post) = wpExecGen False body post fuel' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, wpExecGen]
      rw [h_fn]
    | halted out =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, wpExecGen]
    | faulted fk =>
      cases fk <;>
        dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, MirStepNode.fail, wpExecGen]

private theorem wpMirExecOrExhaustedSym_eq_gen
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) (post : MirOutcome → Prop) :
    wpMirExecOrExhaustedSym fuel body st post = wpExecGen True body post fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    have h_fn :
        (fun st' => wpMirExecOrExhaustedSym fuel' body st' post) = wpExecGen True body post fuel' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      dsimp only [wpMirExecOrExhaustedSym, stepMirExecSymTree, wpExecGen]
      rw [h_fn]
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
      | .some _ => wpExecGen zeroVal ctx.body post (fuel' + 1) (.running s)
      | .none =>
        match Nat.beq s.frame.blockIdx blockIdx with
        | false => wpExecGen zeroVal ctx.body post (fuel' + 1) (.running s)
        | true =>
          match Nat.beq s.frame.stmtIdx stmtIdx with
          | false => wpExecGen zeroVal ctx.body post (fuel' + 1) (.running s)
          | true =>
            match stmts with
            | [] =>
              evalSymNodeTree (wpExecGen zeroVal ctx.body post fuel') post
                (evalTerminatorSymTreeFast s term ctx.body)
            | stmt :: rest =>
              evalSymNodeTree
                (wpBlockStep zeroVal ctx term post blockIdx
                  fuel' (Nat.add stmtIdx 1) rest)
                post
                (evalStmtSymTreeFast s stmt ctx.localDecls ctx.layouts)

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
    wpExecGen zeroVal ctx.body post fuel st =
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
              dsimp only [wpExecGen, stepMirSymTree]
              rw [h_ac]
              dsimp only [Option.getD]
              rw [h_phase]
              dsimp only
              rw [h_bi_eq, h_bb]
              dsimp only
              rw [h_si_eq, get?_length_none]
              dsimp only
              have h_beq : (length bb.statements == length bb.statements) = true :=
                beq_self_eq_true _
              rw [h_beq, evalTerminatorSymTreeFast_eq]
              rfl
            | cons stmt rest =>
              dsimp only [wpExecGen, stepMirSymTree]
              rw [h_ac]
              dsimp only [Option.getD]
              rw [h_phase]
              dsimp only
              rw [h_bi_eq, h_bb]
              dsimp only
              rw [h_si_eq, h_stmts, get?_append_cons]
              dsimp only
              rw [h_ld, h_lay, evalStmtSymTreeFast_eq]
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
    wpExecGen zeroVal ctx.body post fuel (.running (initMachineState ctx.body args)) =
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

private def reqBB0 : BasicBlockData :=
  match Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body.basicBlocks with
  | bb :: _ => bb
  | [] => { statements := [], terminator := { kind := .unreachable, span := "" }, isCleanup := false }

private def ensBB0 : BasicBlockData :=
  match Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body.basicBlocks with
  | bb :: _ => bb
  | [] => { statements := [], terminator := { kind := .unreachable, span := "" }, isCleanup := false }

private def parseBB0 : BasicBlockData :=
  match Mir.WireframeDemo.parse_compression_flag.body.basicBlocks with
  | bb :: _ => bb
  | [] => { statements := [], terminator := { kind := .unreachable, span := "" }, isCleanup := false }

private def reqCtx : BlockCtx :=
  { localDecls := Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body.localDecls
    layouts := Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body.layouts
    body := Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body }

private def ensCtx : BlockCtx :=
  { localDecls := Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body.localDecls
    layouts := Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body.layouts
    body := Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body }

private def parseCtx : BlockCtx :=
  { localDecls := Mir.WireframeDemo.parse_compression_flag.body.localDecls
    layouts := Mir.WireframeDemo.parse_compression_flag.body.layouts
    body := Mir.WireframeDemo.parse_compression_flag.body }

private theorem hold_mirBool_ensures
    (fuel : Nat) (args : List Value)
    (h : Hold
      (wpBlockLinear False ensCtx ensBB0.terminator
        boolTruePost 0 0 fuel ensBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body.localDecls args)
        (initMachineState
          Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body args).memory)) :
    Hold
      (MirBoolPredicateHolds
        Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body args) := by
  refine ⟨mirBoolPredicateHolds_of_wpMirSym_true fuel _ args ?_⟩
  unfold wpMirSym
  change wpMirExecSym fuel ensCtx.body (MirExecState.running (initMachineState ensCtx.body args)) boolTruePost
  rw [wpMirExecSym_eq_gen, wpStartBlock0_eq False ensCtx ensBB0 _ fuel args rfl rfl rfl rfl]
  exact h.val

private theorem hold_mirBool_req
    (fuel : Nat) (args : List Value)
    (h : Hold
      (wpBlockLinear False reqCtx reqBB0.terminator
        boolTruePost 0 0 fuel reqBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body.localDecls args)
        (initMachineState
          Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body args).memory)) :
    Hold
      (MirBoolPredicateHolds
        Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body args) := by
  refine ⟨mirBoolPredicateHolds_of_wpMirSym_true fuel _ args ?_⟩
  unfold wpMirSym
  change wpMirExecSym fuel reqCtx.body (MirExecState.running (initMachineState reqCtx.body args)) boolTruePost
  rw [wpMirExecSym_eq_gen, wpStartBlock0_eq False reqCtx reqBB0 _ fuel args rfl rfl rfl rfl]
  exact h.val

private theorem hold_wpParse_full
    (fuel : Nat) (args : List Value) (post : MirOutcome → Prop)
    (h : Hold
      (wpBlockLinear False parseCtx parseBB0.terminator
        post 0 0 fuel parseBB0.statements
        (initLocalsAux 0 Mir.WireframeDemo.parse_compression_flag.body.localDecls args)
        (initMachineState Mir.WireframeDemo.parse_compression_flag.body args).memory)) :
    Hold (wpMirSym fuel Mir.WireframeDemo.parse_compression_flag.body
      (initMachineState Mir.WireframeDemo.parse_compression_flag.body args) post) := by
  refine ⟨?_⟩
  unfold wpMirSym
  change wpMirExecSym fuel parseCtx.body (MirExecState.running (initMachineState parseCtx.body args)) post
  rw [wpMirExecSym_eq_gen, wpStartBlock0_eq False parseCtx parseBB0 _ fuel args rfl rfl rfl rfl]
  exact h.val

private theorem holdBoolReq_of_mirBoolPredicateHolds
    (fuel : Nat) (args : List Value)
    (h : MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body args) :
    Hold
      (wpBlockLinear True reqCtx reqBB0.terminator
        (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
        0 0 fuel reqBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body.localDecls args)
        (initMachineState
          Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body args).memory) := by
  refine ⟨?_⟩
  change wpBlockLinear True reqCtx reqBB0.terminator _ 0 0 fuel reqBB0.statements
    (initLocalsAux 0 reqCtx.body.localDecls args) (initMachineState reqCtx.body args).memory
  rw [← wpStartBlock0_eq True reqCtx reqBB0 _ fuel args rfl rfl rfl rfl, ← wpMirExecOrExhaustedSym_eq_gen]
  exact holdBoolMirSym_of_mirBoolPredicateHolds fuel _ args h

private theorem bitwiseAndBits_one_one : bitwiseAndBits 8 1 1 = 1 := rfl
private theorem bitwiseAndBits_one_zero : bitwiseAndBits 8 1 0 = 0 := rfl

private theorem eq_zero_or_one_of_mod2_eq (b : Nat) (h : b % 2 = b) : b = 0 ∨ b = 1 := by
  omega

private theorem beq_mod2_zero_of_odd (b : Nat) (h : b % 2 = 1) : Nat.beq (b % 2) 0 = false := by
  rw [h]; rfl

private theorem beq_mod2_zero_of_not_odd (b : Nat) (h : ¬ (b % 2 = 1)) :
    Nat.beq (b % 2) 0 = true := by
  have hm : b % 2 = 0 := by omega
  rw [hm]; rfl

private theorem eq_one_of_zero_or_one_and_odd (b : Nat) (h : b = 0 ∨ b = 1) (ho : b % 2 = 1) :
    b = 1 := by
  omega

private theorem eq_zero_of_zero_or_one_and_not_odd
    (b : Nat) (h : b = 0 ∨ b = 1) (ho : ¬ (b % 2 = 1)) : b = 0 := by
  omega

private theorem wpReq_imp_zero_or_one (b : Nat) :
    Hold
      (wpBlockLinear True reqCtx reqBB0.terminator
        (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
        0 0 28 reqBB0.statements
        (initLocalsAux 0
          Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body.localDecls
          [.scalar { bits := b, sizeBytes := 1 }])
        (initMachineState
          Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body
          [.scalar { bits := b, sizeBytes := 1 }]).memory) →
    b = 0 ∨ b = 1 := by
  dsimp only [Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body,
    reqBB0, wpBlockLinear, wpBlockStep, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast,
    evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, evalUnaryNotSymTree,
    evalTerminatorSymTreeFast,
    lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineState, initLocals, initLocalsAux, emptyMemory,
    readProjectedValue_nil, readProjectedValue_field,
    ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
    projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
    byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
    isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
    invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
    mirSafePost,
    boolToScalar,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or,
    bitwiseAndBits_one_one, bitwiseAndBits_one_zero,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  intro h_hold
  cases h_eq : Nat.beq (b % 2) b with
  | false =>
    rw [h_eq] at h_hold
    rcases h_hold with ⟨h_val⟩
    injection h_val with h_sc
    injection h_sc with h_bits _
    nomatch h_bits
  | true =>
    exact eq_zero_or_one_of_mod2_eq b (Nat.eq_of_beq_eq_true h_eq)

private theorem rustRequires_imp_zero_or_one (b : Nat)
    (h_req : Obligations.WireframeDemo.parse_compression_flag.rustRequires
      [.scalar { bits := b, sizeBytes := 1 }]) :
    b = 0 ∨ b = 1 :=
  wpReq_imp_zero_or_one b (holdBoolReq_of_mirBoolPredicateHolds 28 _ h_req.2)

private theorem mul_one_eight : Nat.mul 1 8 = 8 := rfl

private theorem ensures_holds_one :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
      [.scalar { bits := 1, sizeBytes := 1 }, .scalar { bits := 1, sizeBytes := 1 }] := by
  apply Hold.val
  refine hold_mirBool_ensures 70 _ ?_
  dsimp only [Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body,
    ensBB0, wpBlockLinear, wpBlockStep, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast,
    evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, evalUnaryNotSymTree,
    evalTerminatorSymTreeFast,
    lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineState, initLocals, initLocalsAux, emptyMemory,
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
    get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or,
    bitwiseAndBits_one_one, bitwiseAndBits_one_zero,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  exact ⟨boolTruePost_normal_one _⟩

private theorem ensures_holds_zero :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
      [.scalar { bits := 0, sizeBytes := 1 }, .scalar { bits := 0, sizeBytes := 1 }] := by
  apply Hold.val
  refine hold_mirBool_ensures 70 _ ?_
  dsimp only [Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body,
    ensBB0, wpBlockLinear, wpBlockStep, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast,
    evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, evalUnaryNotSymTree,
    evalTerminatorSymTreeFast,
    lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineState, initLocals, initLocalsAux, emptyMemory,
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
    get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or,
    bitwiseAndBits_one_one, bitwiseAndBits_one_zero,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  exact ⟨boolTruePost_normal_one _⟩

private theorem ensures_holds_of_eq_one (b : Nat) (hb1 : b = 1) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
      [.scalar { bits := b, sizeBytes := 1 }, .scalar { bits := 1, sizeBytes := 1 }] :=
  @Eq.ndrec Nat 1
    (fun x =>
      MirBoolPredicateHolds
        Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
        [.scalar { bits := x, sizeBytes := 1 }, .scalar { bits := 1, sizeBytes := 1 }])
    ensures_holds_one b hb1.symm

private theorem ensures_holds_of_eq_zero (b : Nat) (hb0 : b = 0) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
      [.scalar { bits := b, sizeBytes := 1 }, .scalar { bits := 0, sizeBytes := 1 }] :=
  @Eq.ndrec Nat 0
    (fun x =>
      MirBoolPredicateHolds
        Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
        [.scalar { bits := x, sizeBytes := 1 }, .scalar { bits := 0, sizeBytes := 1 }])
    ensures_holds_zero b hb0.symm

private theorem compressionFlagPost_one (b : Nat) (hb1 : b = 1) :
    compressionFlagPost
      [.scalar { bits := b, sizeBytes := 1 }]
      (.scalar { bits := 1, sizeBytes := 1 }) := by
  subst hb1
  intro b' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with h_bits _
  subst h_bits
  rfl

private theorem compressionFlagPost_zero (b : Nat) (hb0 : b = 0) :
    compressionFlagPost
      [.scalar { bits := b, sizeBytes := 1 }]
      (.scalar { bits := 0, sizeBytes := 1 }) := by
  subst hb0
  intro b' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with h_bits _
  subst h_bits
  rfl

/-- Total-safety + functional verification certificate for `parse_compression_flag`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.parse_compression_flag.claim := by
  refine verifyMirNoPanicSym _ 6 ?_
  intro args h_pre
  apply Hold.val
  rcases h_pre with ⟨b, _hb, h_args⟩
  rw [h_args]
  have h_mul18 : Nat.mul 1 8 = 8 := rfl
  refine hold_wpParse_full 6 _ _ ?_
  dsimp only [Mir.WireframeDemo.parse_compression_flag.body,
    parseBB0, wpBlockLinear, wpBlockStep, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast,
    evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, evalUnaryNotSymTree,
    evalTerminatorSymTreeFast,
    lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineState, initLocals, initLocalsAux, emptyMemory,
    readProjectedValue_nil, readProjectedValue_field,
    invalidateConflictingBorrows, mirNormalPost, boolToScalar,
    Obligations.WireframeDemo.parse_compression_flag.claim,
    Obligations.WireframeDemo.parse_compression_flag.refineSafeSpec,
    Obligations.WireframeDemo.parse_compression_flag.rustEnsures,
    Obligations.WireframeDemo.parse_compression_flag.defaultPost,
    ItemSpec.post,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or,
    bitwiseAndBits_one_one, bitwiseAndBits_one_zero,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  by_cases h_odd : b % 2 = 1
  · rw [beq_mod2_zero_of_odd b h_odd]
    exact ⟨fun h_req_pair =>
      let hb1 : b = 1 :=
        eq_one_of_zero_or_one_and_odd b
          (rustRequires_imp_zero_or_one b h_req_pair.1) h_odd
      ⟨ensures_holds_of_eq_one b hb1, compressionFlagPost_one b hb1⟩⟩
  · rw [beq_mod2_zero_of_not_odd b h_odd]
    exact ⟨fun h_req_pair =>
      let hb0 : b = 0 :=
        eq_zero_of_zero_or_one_and_not_odd b
          (rustRequires_imp_zero_or_one b h_req_pair.1) h_odd
      ⟨ensures_holds_of_eq_zero b hb0, compressionFlagPost_zero b hb0⟩⟩

/-- Non-vacuity witness confirming `parse_compression_flag`'s functional
`rustRequires` contract is satisfiable (`flags_byte = 1`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.parse_compression_flag.rustRequires a := by
  refine ⟨[.scalar { bits := 1, sizeBytes := 1 }], ⟨rfl, ?_⟩⟩
  apply Hold.val
  refine hold_mirBool_req 28 _ ?_
  dsimp only [Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body,
    reqBB0, wpBlockLinear, wpBlockStep, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast,
    evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, evalUnaryNotSymTree,
    evalTerminatorSymTreeFast,
    lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineState, initLocals, initLocalsAux, emptyMemory,
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
    get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or,
    bitwiseAndBits_one_one, bitwiseAndBits_one_zero,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  exact ⟨boolTruePost_normal_one _⟩

end Proof.WireframeDemo.parse_compression_flag
