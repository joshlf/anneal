import Trusted
import Anneal
import Mir.WireframeDemo.decode_wire_header
import Specs.WireframeDemo.decode_wire_header
import Obligations.WireframeDemo.decode_wire_header

namespace Proof.WireframeDemo.decode_wire_header

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.decode_wire_header

/-!
Kernel-checked proof for repaired `wireframe_demo::decode_wire_header` (Journey 2).

Proves across all `256^4 = 2^32` 4-byte `[u8; 4]` inputs that guarding
`raw[0] == 1` and `raw[1] <= 1` before `core::mem::transmute::<[u8; 4], WireHeader>(raw)`
eliminates all bit-validity Undefined Behavior on `WireHeader::compressed: bool`
and returns `decodedPayloadLen b0 b1 b2 b3`.
-/

private structure Hold (P : Prop) : Prop where
  val : P

private def HoldCont (k : MirExecState → Prop) (st : MirExecState) : Prop := k st

private theorem readProjectedValue_nil (locals : List LocalSlot) (val : Value) :
    readProjectedValue locals val [] = .ok val := rfl

private theorem readProjectedValue_field (locals : List LocalSlot)
    (v : Nat) (fields : List Value) (idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    readProjectedValue locals (.aggregate v fields) (.field idx ty :: rest) =
      match get? fields idx with
      | .some fieldVal => readProjectedValue locals fieldVal rest
      | .none => .ub := rfl

private theorem readProjectedValue_index (locals : List LocalSlot)
    (fields : List Value) (idxLocal : LocalIdx) (rest : List ProjectionElem) :
    readProjectedValue locals (.aggregate 0 fields) (.index idxLocal :: rest) =
      match get? locals idxLocal with
      | .some (.init (.scalar sc)) =>
        match get? fields sc.bits with
        | .some elemVal => readProjectedValue locals elemVal rest
        | .none => .ub
      | _ => .ub := rfl

private def evalOperandFallback (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) : OperandEvalResult :=
  evalOperand locals op borrows globals layouts callerLocals

private def evalOperandFast (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) : OperandEvalResult :=
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
    | .deref :: _ => evalOperandFallback locals (.copy p) borrows globals layouts callerLocals
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
  | .cast .transmute op targetTy =>
    .leaf (evalByteCast locals op targetTy mem localDecls layouts)
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandFast locals lhsOp mem.borrows mem.globals layouts mem.callerLocals with
    | .ok lhsVal locals₁ =>
      match evalOperandFast locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          let isSigned := operandIsSigned localDecls lhsOp layouts
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
  | .unaryOp .not op =>
    match evalOperandFast locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.scalar sc) locals' =>
      evalUnaryNotSymTree sc (operandTy localDecls layouts op) locals' mem
    | .ok _ _ => .leaf .unsupported
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
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
  | cast ck _ _ => cases ck <;> rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueSymTreeFast, evalRvalueSymTree]
    rw [evalOperandFast_eq]
    cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [evalOperandFast_eq]
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals <;> rfl
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

private def evalStmtSymTreeFast
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : SymTree MirStepNode :=
  match stmt.kind with
  | .assign dst rv =>
    (evalRvalueSymTreeFast s.frame.locals rv s.memory localDecls layouts).bind
      (fun res => .leaf (finishAssignStmtNode s dst res))
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
    show (evalRvalueSymTreeFast s.frame.locals rv s.memory localDecls layouts).bind _ =
      (evalRvalueSymTree s.frame.locals rv s.memory localDecls layouts).bind _
    rw [evalRvalueSymTreeFast_eq]
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

private def stepMirFast (rootBody : CapturedMir) (s : MachineState) : SymTree MirStepNode :=
  let currentBody := s.memory.activeCallee.getD rootBody
  match currentBody.phase with
  | .other _ => .leaf MirStepNode.unsupported
  | _ =>
    match get? currentBody.basicBlocks s.frame.blockIdx with
    | .none => .leaf (MirStepNode.fail .ub)
    | .some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | .some stmt => evalStmtSymTreeFast s stmt currentBody.localDecls currentBody.layouts
      | .none =>
        if s.frame.stmtIdx == length bb.statements then
          evalTerminatorSymTreeFast s bb.terminator currentBody
        else
          .leaf (MirStepNode.fail .ub)

private theorem stepMirFast_eq (rootBody : CapturedMir) (s : MachineState) :
    stepMirFast rootBody s = stepMirSymTree rootBody s := by
  dsimp only [stepMirFast, stepMirSymTree]
  cases (s.memory.activeCallee.getD rootBody).phase with
  | other _ => rfl
  | _ =>
    dsimp only
    cases get? (s.memory.activeCallee.getD rootBody).basicBlocks s.frame.blockIdx with
    | none => rfl
    | some bb =>
      dsimp only
      cases get? bb.statements s.frame.stmtIdx with
      | some stmt => exact evalStmtSymTreeFast_eq _ _ _ _
      | none =>
        dsimp only
        split
        · exact evalTerminatorSymTreeFast_eq _ _ _
        · rfl

private def wpDecodeFast (post : MirOutcome → Prop) :
    Nat → MirExecState → Prop
  | 0, _ => False
  | fuel' + 1, .running s =>
    evalSymNodeTree (wpDecodeFast post fuel') post
      (stepMirFast Mir.WireframeDemo.decode_wire_header.body s)
  | _ + 1, .halted out => post out
  | _ + 1, .faulted _ => False

private def wpDecodeCont
    (cont : MirExecState → Prop)
    (post : MirOutcome → Prop) :
    Nat → MirExecState → Prop
  | 0, st => cont st
  | fuel' + 1, .running s =>
    evalSymNodeTree (wpDecodeCont cont post fuel') post
      (stepMirFast Mir.WireframeDemo.decode_wire_header.body s)
  | _ + 1, .halted out => post out
  | _ + 1, .faulted _ => False

private theorem wpDecodeFast_split
    (post : MirOutcome → Prop)
    (f1 f2 : Nat) (st : MirExecState) :
    wpDecodeFast post (f1 + f2) st =
      wpDecodeCont (HoldCont (wpDecodeFast post f2)) post f1 st := by
  induction f1 generalizing st with
  | zero => simp only [Nat.zero_add]; rfl
  | succ f1' ih =>
    rw [Nat.succ_add]
    have h_fn :
        wpDecodeFast post (f1' + f2) =
          wpDecodeCont (HoldCont (wpDecodeFast post f2)) post f1' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      show evalSymNodeTree (wpDecodeFast post (f1' + f2)) post
          (stepMirFast Mir.WireframeDemo.decode_wire_header.body s) =
        evalSymNodeTree (wpDecodeCont (HoldCont (wpDecodeFast post f2)) post f1') post
          (stepMirFast Mir.WireframeDemo.decode_wire_header.body s)
      rw [h_fn]
    | halted _ => rfl
    | faulted _ => rfl

private theorem wpMirExecSym_decode_eq
    (fuel : Nat) (st : MirExecState) (post : MirOutcome → Prop) :
    wpMirExecSym fuel Mir.WireframeDemo.decode_wire_header.body st post =
      wpDecodeFast post fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    have h_fn :
        (fun st' => wpMirExecSym fuel' Mir.WireframeDemo.decode_wire_header.body st' post) =
          wpDecodeFast post fuel' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, wpDecodeFast]
      rw [h_fn, stepMirFast_eq]
    | halted out =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, wpDecodeFast]
    | faulted fk =>
      cases fk <;>
        dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, MirStepNode.fail, wpDecodeFast]

private theorem decode_wireHeader_0 (b2 b3 : UInt8) :
    decodeValueFromBytes defaultCodecFuel
      Mir.WireframeDemo.decode_wire_header.layouts
      { kind := .adt "wireframe_demo::WireHeader" [], layoutIdx := 5 }
      [.init 1 none, .init (UInt8.ofNat 0) none, .init b2 none, .init b3 none] =
    match
      (match
        (match
          (match
            decodeScalarLayoutBytes
              (ScalarLayout.initialized (.int 16 false) { start := 0, end_ := 65535 })
              [.init b2 none, .init b3 none]
           with
           | none => none
           | some v => some [v])
         with
         | some vs => some (.scalar { bits := 0, sizeBytes := 1 } :: vs)
         | none => none)
       with
       | some vs => some (.scalar { bits := 1, sizeBytes := 1 } :: vs)
       | none => none)
    with
    | some vals => some (.aggregate 0 vals)
    | none => none := rfl

private theorem decode_wireHeader_1 (b2 b3 : UInt8) :
    decodeValueFromBytes defaultCodecFuel
      Mir.WireframeDemo.decode_wire_header.layouts
      { kind := .adt "wireframe_demo::WireHeader" [], layoutIdx := 5 }
      [.init 1 none, .init (UInt8.ofNat 1) none, .init b2 none, .init b3 none] =
    match
      (match
        (match
          (match
            decodeScalarLayoutBytes
              (ScalarLayout.initialized (.int 16 false) { start := 0, end_ := 65535 })
              [.init b2 none, .init b3 none]
           with
           | none => none
           | some v => some [v])
         with
         | some vs => some (.scalar { bits := 1, sizeBytes := 1 } :: vs)
         | none => none)
       with
       | some vs => some (.scalar { bits := 1, sizeBytes := 1 } :: vs)
       | none => none)
    with
    | some vals => some (.aggregate 0 vals)
    | none => none := rfl

private theorem evalByteCast_wireHeader
    (b1 b2 b3 : Nat) (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (l0 : LocalSlot) (restLocals : List LocalSlot) (mem : Memory) :
    evalByteCast
      (l0 :: .init (rawHeaderValue 1 b1 b2 b3) :: restLocals)
      (.copy { local_ := 1, projection := [] })
      { kind := .adt "wireframe_demo::WireHeader" [], layoutIdx := 5 }
      mem
      Mir.WireframeDemo.decode_wire_header.body.localDecls
      Mir.WireframeDemo.decode_wire_header.layouts =
    .ok
      (.aggregate 0
        [ .scalar { bits := 1, sizeBytes := 1 }
        , .scalar { bits := b1, sizeBytes := 1 }
        , .scalar { bits := b2 + 256 * b3, sizeBytes := 2 } ])
      (l0 :: .init (rawHeaderValue 1 b1 b2 b3) :: restLocals)
      mem := by
  let rawBits :=
    Nat.add (UInt8.ofNat b2).toBitVec.toNat
      (Nat.mul 256 (Nat.add (UInt8.ofNat b3).toBitVec.toNat 0))
  have h_ble : Nat.ble rawBits 65535 = true :=
    Nat.ble_eq_true_of_le (by dsimp [rawBits]; omega)
  have h_val : rawBits = b2 + 256 * b3 := by
    dsimp [rawBits]
    omega
  have h_u16 :
      decodeScalarLayoutBytes
        (ScalarLayout.initialized (.int 16 false) { start := 0, end_ := 65535 })
        [.init (UInt8.ofNat b2) none, .init (UInt8.ofNat b3) none] =
      some (.scalar { bits := b2 + 256 * b3, sizeBytes := 2 }) := by
    change
      (match Nat.ble rawBits 65535 with
       | false => Option.none
       | true => Option.some (Value.scalar { bits := rawBits, sizeBytes := 2 })) = _
    rw [h_ble, h_val]
  have h_enc :
      encodeValueToBytes defaultCodecFuel
        Mir.WireframeDemo.decode_wire_header.layouts
        { kind := .array (.uint .u8) 4, layoutIdx := 1 }
        (rawHeaderValue 1 b1 b2 b3) =
      some
        [ .init 1 none
        , .init (UInt8.ofNat b1) none
        , .init (UInt8.ofNat b2) none
        , .init (UInt8.ofNat b3) none ] := rfl
  have h_dst :
      rigidTyByteSize Mir.WireframeDemo.decode_wire_header.layouts
        { kind := .adt "wireframe_demo::WireHeader" [], layoutIdx := 5 } = some 4 := rfl
  have h_src :
      rigidTyByteSize Mir.WireframeDemo.decode_wire_header.layouts
        { kind := .array (.uint .u8) 4, layoutIdx := 1 } = some 4 := rfl
  have h_op :
      operandTy Mir.WireframeDemo.decode_wire_header.body.localDecls
        Mir.WireframeDemo.decode_wire_header.layouts
        (.copy { local_ := 1, projection := [] }) =
      some { kind := .array (.uint .u8) 4, layoutIdx := 1 } := rfl
  unfold evalByteCast
  dsimp only [evalOperand, readProjectedValue, get?,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal]
  rw [h_dst, h_op]
  dsimp only
  rw [h_src, h_enc]
  dsimp only [length, List.length, Nat.beq]
  rcases hb1 with rfl | rfl
  · rw [decode_wireHeader_0, h_u16]
  · rw [decode_wireHeader_1, h_u16]

private theorem evalByteCast_wireHeader_any
    (b1 b2 b3 : Nat) (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (l0 : LocalSlot) (restLocals : List LocalSlot) (mem : Memory)
    (decls : List LocalDecl) (lyts : LayoutTable)
    (hd : decls = Mir.WireframeDemo.decode_wire_header.body.localDecls)
    (hl : lyts = Mir.WireframeDemo.decode_wire_header.layouts) :
    evalByteCast
      (l0 ::
        .init
          (.aggregate 0
            [ .scalar { bits := 1, sizeBytes := 1 }
            , .scalar { bits := b1, sizeBytes := 1 }
            , .scalar { bits := b2, sizeBytes := 1 }
            , .scalar { bits := b3, sizeBytes := 1 } ]) ::
        restLocals)
      (.copy { local_ := 1, projection := [] })
      { kind := .adt "wireframe_demo::WireHeader" [], layoutIdx := 5 }
      mem decls lyts =
    .ok
      (.aggregate 0
        [ .scalar { bits := 1, sizeBytes := 1 }
        , .scalar { bits := b1, sizeBytes := 1 }
        , .scalar { bits := b2 + 256 * b3, sizeBytes := 2 } ])
      (l0 ::
        .init
          (.aggregate 0
            [ .scalar { bits := 1, sizeBytes := 1 }
            , .scalar { bits := b1, sizeBytes := 1 }
            , .scalar { bits := b2, sizeBytes := 1 }
            , .scalar { bits := b3, sizeBytes := 1 } ]) ::
        restLocals)
      mem := by
  subst hd hl
  exact evalByteCast_wireHeader b1 b2 b3 hb1 hb2 hb3 l0 restLocals mem

private theorem hold_wpDecode_start
    (f1 f2 : Nat) (args : List Value) (post : MirOutcome → Prop)
    (h : Hold (wpDecodeCont (HoldCont (wpDecodeFast post f2)) post f1
      (.running (initMachineState Mir.WireframeDemo.decode_wire_header.body args)))) :
    Hold (wpMirSym (f1 + f2) Mir.WireframeDemo.decode_wire_header.body
      (initMachineState Mir.WireframeDemo.decode_wire_header.body args) post) := by
  refine ⟨?_⟩
  unfold wpMirSym
  rw [wpMirExecSym_decode_eq, wpDecodeFast_split]
  exact h.val

private theorem hold_wpDecode_step
    (f1 f2 : Nat) (st : MirExecState) (post : MirOutcome → Prop)
    (h : Hold (wpDecodeCont (HoldCont (wpDecodeFast post f2)) post f1 st)) :
    Hold (HoldCont (wpDecodeFast post (f1 + f2)) st) := by
  refine ⟨?_⟩
  unfold HoldCont
  rw [wpDecodeFast_split]
  exact h.val

private theorem hold_wpDecode_full
    (f : Nat) (args : List Value) (post : MirOutcome → Prop)
    (h : Hold (wpDecodeFast post f
      (.running (initMachineState Mir.WireframeDemo.decode_wire_header.body args)))) :
    Hold (wpMirSym f Mir.WireframeDemo.decode_wire_header.body
      (initMachineState Mir.WireframeDemo.decode_wire_header.body args) post) := by
  refine ⟨?_⟩
  unfold wpMirSym
  rw [wpMirExecSym_decode_eq]
  exact h.val

set_option linter.unusedSimpArgs false in
private theorem wp_valid_header
    (b1 b2 b3 : Nat) (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 < 256) (hb3 : b3 < 256) :
    Hold
      (wpMirSym 35 Mir.WireframeDemo.decode_wire_header.body
        (initMachineState Mir.WireframeDemo.decode_wire_header.body [rawHeaderValue 1 b1 b2 b3])
        (mirNormalPost fun retVal _ =>
          Obligations.WireframeDemo.decode_wire_header.claim.post [rawHeaderValue 1 b1 b2 b3] retVal)) := by
  have h_c : b1 ≤ 1 := by omega
  rcases hb1 with rfl | rfl
  all_goals
    refine hold_wpDecode_start 23 12 _ _ ?_
    dsimp only [Obligations.WireframeDemo.decode_wire_header.claim,
      Mir.WireframeDemo.decode_wire_header.body,
      Mir.WireframeDemo.decode_wire_header.layouts,
      rawHeaderValue,
      wpDecodeCont, stepMirFast, evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
      evalScalarBinOpSymTree, evalTerminatorSymTreeFast,
      lookupSwitchTargetTree,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, emptyMemory,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      writePlaceValue,
      operandIsSigned, operandTy, placeTy, resolveProjectedTy, tyIsSigned,
      invalidateConflictingBorrows, mirNormalPost,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    refine hold_wpDecode_step 1 11 _ _ ?_
    dsimp only [wpDecodeCont, stepMirFast, evalSymNodeTree,
      Mir.WireframeDemo.decode_wire_header.body,
      Mir.WireframeDemo.decode_wire_header.layouts,
      evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      List.length, List.set, Option.getD,
      get?, set?, length, Nat.add, Nat.beq,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  · rw [evalByteCast_wireHeader_any 0 b2 b3 (Or.inl rfl) hb2 hb3]; rotate_left; exact rfl; exact rfl
    dsimp only [HoldCont, wpDecodeFast, stepMirFast, evalSymNodeTree,
      Mir.WireframeDemo.decode_wire_header.body,
      Mir.WireframeDemo.decode_wire_header.layouts,
      evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
      evalScalarBinOpSymTree, evalTerminatorSymTreeFast,
      lookupSwitchTargetTree,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      writePlaceValue,
      operandIsSigned, operandTy, placeTy, resolveProjectedTy, tyIsSigned,
      invalidateConflictingBorrows, mirNormalPost,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      List.length, List.set, Option.getD,
      get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    cases h_len : Nat.ble (b2 + 256 * b3) 1024
    · dsimp only [evalSymNodeTree, wpDecodeFast, stepMirFast,
        Mir.WireframeDemo.decode_wire_header.body,
        Mir.WireframeDemo.decode_wire_header.layouts,
        evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
        evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
        evalTerminatorSymTreeFast, lookupSwitchTargetTree,
        MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
        readProjectedValue_nil, readProjectedValue_field,
        invalidateConflictingBorrows, mirNormalPost,
        GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
        List.length, List.set, Option.getD,
        get?, set?, length, Nat.add, Nat.beq,
        ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
        Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq,
        ItemSpec.post,
        Obligations.WireframeDemo.decode_wire_header.claim,
        Obligations.WireframeDemo.decode_wire_header.refineSpec,
        Obligations.WireframeDemo.decode_wire_header.rustEnsures,
        Obligations.WireframeDemo.decode_wire_header.defaultPost,
        rawHeaderPost]
      refine ⟨⟨trivial, ?_⟩⟩
      intro b0' b1' b2' b3' _ _ _ _ h_eq
      injection h_eq with h_hd _
      injection h_hd with _ h_f
      injection h_f with h0 h_f1
      injection h_f1 with h1 h_f2
      injection h_f2 with h2 h_f3
      injection h_f3 with h3 _
      injection h0 with h0'; injection h0' with hb0_eq _
      injection h1 with h1'; injection h1' with hb1_eq _
      injection h2 with h2'; injection h2' with hb2_eq _
      injection h3 with h3'; injection h3' with hb3_eq _
      subst hb0_eq hb1_eq hb2_eq hb3_eq
      have h_nle1024 : ¬ (b2 + 256 * b3 ≤ 1024) := by
        intro hc
        have ht := Nat.ble_eq_true_of_le hc
        rw [h_len] at ht
        contradiction
      dsimp only [decodedPayloadLen]
      simp only [h_c, h_nle1024, decide_true, decide_false, BEq.beq, Nat.beq,
        Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
    · dsimp only [evalSymNodeTree, wpDecodeFast, stepMirFast,
        Mir.WireframeDemo.decode_wire_header.body,
        Mir.WireframeDemo.decode_wire_header.layouts,
        evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
        evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
        evalTerminatorSymTreeFast, lookupSwitchTargetTree,
        MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
        readProjectedValue_nil, readProjectedValue_field,
        invalidateConflictingBorrows, mirNormalPost,
        GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
        List.length, List.set, Option.getD,
        get?, set?, length, Nat.add, Nat.beq,
        ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
        Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq,
        ItemSpec.post,
        Obligations.WireframeDemo.decode_wire_header.claim,
        Obligations.WireframeDemo.decode_wire_header.refineSpec,
        Obligations.WireframeDemo.decode_wire_header.rustEnsures,
        Obligations.WireframeDemo.decode_wire_header.defaultPost,
        rawHeaderPost]
      refine ⟨⟨trivial, ?_⟩⟩
      intro b0' b1' b2' b3' _ _ _ _ h_eq
      injection h_eq with h_hd _
      injection h_hd with _ h_f
      injection h_f with h0 h_f1
      injection h_f1 with h1 h_f2
      injection h_f2 with h2 h_f3
      injection h_f3 with h3 _
      injection h0 with h0'; injection h0' with hb0_eq _
      injection h1 with h1'; injection h1' with hb1_eq _
      injection h2 with h2'; injection h2' with hb2_eq _
      injection h3 with h3'; injection h3' with hb3_eq _
      subst hb0_eq hb1_eq hb2_eq hb3_eq
      have h_le1024 : b2 + 256 * b3 ≤ 1024 := Nat.le_of_ble_eq_true h_len
      dsimp only [decodedPayloadLen]
      simp only [h_c, h_le1024, decide_true, BEq.beq, Nat.beq, Bool.and_self, ↓reduceIte]
  · rw [evalByteCast_wireHeader_any 1 b2 b3 (Or.inr rfl) hb2 hb3]; rotate_left; exact rfl; exact rfl
    dsimp only [HoldCont, wpDecodeFast, stepMirFast, evalSymNodeTree,
      Mir.WireframeDemo.decode_wire_header.body,
      Mir.WireframeDemo.decode_wire_header.layouts,
      evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
      evalScalarBinOpSymTree, evalTerminatorSymTreeFast,
      lookupSwitchTargetTree,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      writePlaceValue,
      operandIsSigned, operandTy, placeTy, resolveProjectedTy, tyIsSigned,
      invalidateConflictingBorrows, mirNormalPost,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      List.length, List.set, Option.getD,
      get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    cases h_len : Nat.ble (b2 + 256 * b3) 1024
    · dsimp only [evalSymNodeTree, wpDecodeFast, stepMirFast,
        Mir.WireframeDemo.decode_wire_header.body,
        Mir.WireframeDemo.decode_wire_header.layouts,
        evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
        evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
        evalTerminatorSymTreeFast, lookupSwitchTargetTree,
        MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
        readProjectedValue_nil, readProjectedValue_field,
        invalidateConflictingBorrows, mirNormalPost,
        GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
        List.length, List.set, Option.getD,
        get?, set?, length, Nat.add, Nat.beq,
        ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
        Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq,
        ItemSpec.post,
        Obligations.WireframeDemo.decode_wire_header.claim,
        Obligations.WireframeDemo.decode_wire_header.refineSpec,
        Obligations.WireframeDemo.decode_wire_header.rustEnsures,
        Obligations.WireframeDemo.decode_wire_header.defaultPost,
        rawHeaderPost]
      refine ⟨⟨trivial, ?_⟩⟩
      intro b0' b1' b2' b3' _ _ _ _ h_eq
      injection h_eq with h_hd _
      injection h_hd with _ h_f
      injection h_f with h0 h_f1
      injection h_f1 with h1 h_f2
      injection h_f2 with h2 h_f3
      injection h_f3 with h3 _
      injection h0 with h0'; injection h0' with hb0_eq _
      injection h1 with h1'; injection h1' with hb1_eq _
      injection h2 with h2'; injection h2' with hb2_eq _
      injection h3 with h3'; injection h3' with hb3_eq _
      subst hb0_eq hb1_eq hb2_eq hb3_eq
      have h_nle1024 : ¬ (b2 + 256 * b3 ≤ 1024) := by
        intro hc
        have ht := Nat.ble_eq_true_of_le hc
        rw [h_len] at ht
        contradiction
      dsimp only [decodedPayloadLen]
      simp only [h_c, h_nle1024, decide_true, decide_false, BEq.beq, Nat.beq,
        Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
    · dsimp only [evalSymNodeTree, wpDecodeFast, stepMirFast,
        Mir.WireframeDemo.decode_wire_header.body,
        Mir.WireframeDemo.decode_wire_header.layouts,
        evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
        evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
        evalTerminatorSymTreeFast, lookupSwitchTargetTree,
        MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
        readProjectedValue_nil, readProjectedValue_field,
        invalidateConflictingBorrows, mirNormalPost,
        GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
        List.length, List.set, Option.getD,
        get?, set?, length, Nat.add, Nat.beq,
        ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
        Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq,
        ItemSpec.post,
        Obligations.WireframeDemo.decode_wire_header.claim,
        Obligations.WireframeDemo.decode_wire_header.refineSpec,
        Obligations.WireframeDemo.decode_wire_header.rustEnsures,
        Obligations.WireframeDemo.decode_wire_header.defaultPost,
        rawHeaderPost]
      refine ⟨⟨trivial, ?_⟩⟩
      intro b0' b1' b2' b3' _ _ _ _ h_eq
      injection h_eq with h_hd _
      injection h_hd with _ h_f
      injection h_f with h0 h_f1
      injection h_f1 with h1 h_f2
      injection h_f2 with h2 h_f3
      injection h_f3 with h3 _
      injection h0 with h0'; injection h0' with hb0_eq _
      injection h1 with h1'; injection h1' with hb1_eq _
      injection h2 with h2'; injection h2' with hb2_eq _
      injection h3 with h3'; injection h3' with hb3_eq _
      subst hb0_eq hb1_eq hb2_eq hb3_eq
      have h_le1024 : b2 + 256 * b3 ≤ 1024 := Nat.le_of_ble_eq_true h_len
      dsimp only [decodedPayloadLen]
      simp only [h_c, h_le1024, decide_true, BEq.beq, Nat.beq, Bool.and_self, ↓reduceIte]

set_option linter.unusedSimpArgs false in
private theorem wp_invalid_b1 (b1' b2 b3 : Nat) :
    Hold
      (wpMirSym 35 Mir.WireframeDemo.decode_wire_header.body
        (initMachineState Mir.WireframeDemo.decode_wire_header.body [rawHeaderValue 1 (b1' + 1 + 1) b2 b3])
        (mirNormalPost fun retVal _ =>
          Obligations.WireframeDemo.decode_wire_header.claim.post [rawHeaderValue 1 (b1' + 1 + 1) b2 b3] retVal)) := by
  have h_c : ¬ (b1' + 1 + 1 ≤ 1) := by omega
  refine hold_wpDecode_full 35 _ _ ?_
  dsimp only [Obligations.WireframeDemo.decode_wire_header.claim,
    Mir.WireframeDemo.decode_wire_header.body,
    Mir.WireframeDemo.decode_wire_header.layouts,
    rawHeaderValue,
    wpDecodeFast, stepMirFast, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
    evalScalarBinOpSymTree, evalTerminatorSymTreeFast,
    lookupSwitchTargetTree,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, emptyMemory,
    readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
    writePlaceValue,
    operandIsSigned, operandTy, placeTy, resolveProjectedTy, tyIsSigned,
    invalidateConflictingBorrows, mirNormalPost,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq,
    ItemSpec.post,
    Obligations.WireframeDemo.decode_wire_header.refineSpec,
    Obligations.WireframeDemo.decode_wire_header.rustEnsures,
    Obligations.WireframeDemo.decode_wire_header.defaultPost,
    rawHeaderPost]
  refine ⟨⟨trivial, ?_⟩⟩
  intro b0' b1'' b2' b3' _ _ _ _ h_eq
  injection h_eq with h_hd _
  injection h_hd with _ h_f
  injection h_f with h0 h_f1
  injection h_f1 with h1 _
  injection h0 with h0'; injection h0' with hb0_eq _
  injection h1 with h1'; injection h1' with hb1_eq _
  subst hb0_eq
  rw [← hb1_eq]
  dsimp only [decodedPayloadLen]
  simp only [h_c, decide_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

set_option linter.unusedSimpArgs false in
private theorem wp_invalid_b0 (b0 b1 b2 b3 : Nat) (h_v1 : b0 ≠ 1) :
    Hold
      (wpMirSym 35 Mir.WireframeDemo.decode_wire_header.body
        (initMachineState Mir.WireframeDemo.decode_wire_header.body [rawHeaderValue b0 b1 b2 b3])
        (mirNormalPost fun retVal _ =>
          Obligations.WireframeDemo.decode_wire_header.claim.post [rawHeaderValue b0 b1 b2 b3] retVal)) := by
  rcases b0 with _ | _ | b0'
  · refine hold_wpDecode_full 35 _ _ ?_
    dsimp only [Obligations.WireframeDemo.decode_wire_header.claim,
      Mir.WireframeDemo.decode_wire_header.body,
      Mir.WireframeDemo.decode_wire_header.layouts,
      rawHeaderValue,
      wpDecodeFast, stepMirFast, evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
      evalScalarBinOpSymTree, evalTerminatorSymTreeFast,
      lookupSwitchTargetTree,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, emptyMemory,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      writePlaceValue,
      operandIsSigned, operandTy, placeTy, resolveProjectedTy, tyIsSigned,
      invalidateConflictingBorrows, mirNormalPost,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq,
      ItemSpec.post,
      Obligations.WireframeDemo.decode_wire_header.refineSpec,
      Obligations.WireframeDemo.decode_wire_header.rustEnsures,
      Obligations.WireframeDemo.decode_wire_header.defaultPost,
      rawHeaderPost]
    refine ⟨⟨trivial, ?_⟩⟩
    intro b0'' b1' b2' b3' _ _ _ _ h_eq
    injection h_eq with h_hd _
    injection h_hd with _ h_f
    injection h_f with h0 _
    injection h0 with h0'; injection h0' with hb0_eq _
    subst hb0_eq
    rfl
  · exact False.elim (h_v1 rfl)
  · refine hold_wpDecode_full 35 _ _ ?_
    dsimp only [Obligations.WireframeDemo.decode_wire_header.claim,
      Mir.WireframeDemo.decode_wire_header.body,
      Mir.WireframeDemo.decode_wire_header.layouts,
      rawHeaderValue,
      wpDecodeFast, stepMirFast, evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
      evalScalarBinOpSymTree, evalTerminatorSymTreeFast,
      lookupSwitchTargetTree,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, emptyMemory,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      writePlaceValue,
      operandIsSigned, operandTy, placeTy, resolveProjectedTy, tyIsSigned,
      invalidateConflictingBorrows, mirNormalPost,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq,
      ItemSpec.post,
      Obligations.WireframeDemo.decode_wire_header.refineSpec,
      Obligations.WireframeDemo.decode_wire_header.rustEnsures,
      Obligations.WireframeDemo.decode_wire_header.defaultPost,
      rawHeaderPost]
    refine ⟨⟨trivial, ?_⟩⟩
    intro b0'' b1' b2' b3' _ _ _ _ h_eq
    injection h_eq with h_hd _
    injection h_hd with _ h_f
    injection h_f with h0 _
    injection h0 with h0'; injection h0' with hb0_eq _
    rw [← hb0_eq]
    have h_beq_f : (b0' + 1 + 1 == 1) = false := rfl
    dsimp only [decodedPayloadLen]
    simp only [h_beq_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Universal verification certificate for repaired `decode_wire_header`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.decode_wire_header.claim := by
  refine verifyMirNoPanicSym _ 35 ?_
  intro args h_pre
  apply Hold.val
  rcases h_pre with ⟨_, b0, b1, b2, b3, hb0, hb1, hb2, hb3, h_args⟩
  rw [h_args]
  by_cases h_v1 : b0 = 1
  · subst h_v1
    by_cases h_c : b1 ≤ 1
    · exact wp_valid_header b1 b2 b3 (by omega) hb2 hb3
    · rcases b1 with _ | _ | b1'
      · omega
      · omega
      · exact wp_invalid_b1 b1' b2 b3
  · exact wp_invalid_b0 b0 b1 b2 b3 h_v1

end Proof.WireframeDemo.decode_wire_header
