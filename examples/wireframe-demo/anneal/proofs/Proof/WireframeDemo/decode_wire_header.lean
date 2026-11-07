import Trusted
import Anneal
import Mir.WireframeDemo.decode_wire_header
import Specs.WireframeDemo.decode_wire_header
import Obligations.WireframeDemo.decode_wire_header

namespace Proof.WireframeDemo.decode_wire_header

set_option linter.all false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.PureMirExec
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.decode_wire_header

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

private theorem evalByteCastAfterOperand_wireHeader
    (b1 b2 b3 : Nat) (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (locals' : List LocalSlot) (mem : Memory) :
    evalByteCastAfterOperand
      Mir.WireframeDemo.decode_wire_header.body
      (.copy { local_ := 1, projection := [] })
      { kind := .adt "wireframe_demo::WireHeader" [], layoutIdx := 5 }
      (.aggregate 0
        [ .scalar { bits := 1, sizeBytes := 1 }
        , .scalar { bits := b1, sizeBytes := 1 }
        , .scalar { bits := b2, sizeBytes := 1 }
        , .scalar { bits := b3, sizeBytes := 1 } ])
      locals' mem =
    .ok
      (.aggregate 0
        [ .scalar { bits := 1, sizeBytes := 1 }
        , .scalar { bits := b1, sizeBytes := 1 }
        , .scalar { bits := b2 + 256 * b3, sizeBytes := 2 } ])
      locals' mem := by
  let rawBits :=
    Nat.add (UInt8.ofNat b2).toBitVec.toNat
      (Nat.mul 256 (Nat.add (UInt8.ofNat b3).toBitVec.toNat 0))
  have h_ble : Nat.ble rawBits 65535 = true :=
    Nat.ble_eq_true_of_le (by dsimp [rawBits]; omega)
  have h_val : rawBits = b2 + 256 * b3 := by
    dsimp [rawBits]; omega
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
        (.aggregate 0
          [ .scalar { bits := 1, sizeBytes := 1 }
          , .scalar { bits := b1, sizeBytes := 1 }
          , .scalar { bits := b2, sizeBytes := 1 }
          , .scalar { bits := b3, sizeBytes := 1 } ]) =
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
  have h_lay :
      Mir.WireframeDemo.decode_wire_header.body.layouts =
        Mir.WireframeDemo.decode_wire_header.layouts := rfl
  unfold evalByteCastAfterOperand
  rw [h_lay, h_dst, h_op]
  dsimp only
  rw [h_src, h_enc]
  dsimp only [length, List.length, Nat.beq]
  rcases hb1 with rfl | rfl
  · rw [decode_wireHeader_0, h_u16]
  · rw [decode_wireHeader_1, h_u16]

private theorem evalByteCastAfterOperand_wireHeader_any
    (b1 b2 b3 : Nat) (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 < 256) (hb3 : b3 < 256)
    {locals' : List LocalSlot} {mem : Memory}
    {body : CapturedMir}
    (h_decls : body.localDecls = Mir.WireframeDemo.decode_wire_header.body.localDecls := by rfl)
    (h_layouts : body.layouts = Mir.WireframeDemo.decode_wire_header.layouts := by rfl) :
    evalByteCastAfterOperand
      body
      (.copy { local_ := 1, projection := [] })
      { kind := .adt "wireframe_demo::WireHeader" [], layoutIdx := 5 }
      (.aggregate 0
        [ .scalar { bits := 1, sizeBytes := 1 }
        , .scalar { bits := b1, sizeBytes := 1 }
        , .scalar { bits := b2, sizeBytes := 1 }
        , .scalar { bits := b3, sizeBytes := 1 } ])
      locals' mem =
    .ok
      (.aggregate 0
        [ .scalar { bits := 1, sizeBytes := 1 }
        , .scalar { bits := b1, sizeBytes := 1 }
        , .scalar { bits := b2 + 256 * b3, sizeBytes := 2 } ])
      locals' mem := by
  have h_eq :
      evalByteCastAfterOperand body (.copy { local_ := 1, projection := [] })
        { kind := .adt "wireframe_demo::WireHeader" [], layoutIdx := 5 }
        (.aggregate 0
          [ .scalar { bits := 1, sizeBytes := 1 }
          , .scalar { bits := b1, sizeBytes := 1 }
          , .scalar { bits := b2, sizeBytes := 1 }
          , .scalar { bits := b3, sizeBytes := 1 } ])
        locals' mem =
      evalByteCastAfterOperand Mir.WireframeDemo.decode_wire_header.body
        (.copy { local_ := 1, projection := [] })
        { kind := .adt "wireframe_demo::WireHeader" [], layoutIdx := 5 }
        (.aggregate 0
          [ .scalar { bits := 1, sizeBytes := 1 }
          , .scalar { bits := b1, sizeBytes := 1 }
          , .scalar { bits := b2, sizeBytes := 1 }
          , .scalar { bits := b3, sizeBytes := 1 } ])
        locals' mem := by
    unfold evalByteCastAfterOperand
    rw [h_decls, h_layouts]
    rfl
  rw [h_eq]
  exact evalByteCastAfterOperand_wireHeader b1 b2 b3 hb1 hb2 hb3 locals' mem

private theorem wp_valid_header
    (b1 b2 b3 : Nat) (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 < 256) (hb3 : b3 < 256) :
    Hold
      (wpBlockLinear False Mir.WireframeDemo.decode_wire_header.body
        (entryBB Mir.WireframeDemo.decode_wire_header.body).terminator
        (mirNormalPost
          (fun retVal _ =>
            Obligations.WireframeDemo.decode_wire_header.claim.post
              [rawHeaderValue 1 b1 b2 b3] retVal))
        0 0 (defaultSpecSteps Mir.WireframeDemo.decode_wire_header.body)
        (entryBB Mir.WireframeDemo.decode_wire_header.body).statements
        (initLocalsAux 0 Mir.WireframeDemo.decode_wire_header.body.localDecls
          [rawHeaderValue 1 b1 b2 b3])
        (initMachineState Mir.WireframeDemo.decode_wire_header.body
          [rawHeaderValue 1 b1 b2 b3]).memory) := by
  have h_c : b1 ≤ 1 := by omega
  (rcases hb1 with rfl | rfl <;>
    dsimp only [
      Obligations.WireframeDemo.decode_wire_header.claim,
      Mir.WireframeDemo.decode_wire_header.body,
      Mir.WireframeDemo.decode_wire_header.layouts, rawHeaderValue,
      defaultSpecSteps, entryBB, dummyBB, lookupBlock,
      wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
      stepMirSymTreeFast, evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
      finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
      evalConstValue, evalScalarBinOpSymTree, evalTerminatorSymTreeFast,
      lookupSwitchTargetTree, MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, emptyMemory,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      writePlaceValue, operandIsSigned, operandTy, sharedBorrowPerm, rigidTyIsFreeze,
      stringEq, tyIsFreeze, placeTy, resolveProjectedTy, tyIsSigned,
      invalidateConflictingBorrows, mirNormalPost,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]) <;>
  (first
    | rw [evalByteCastAfterOperand_wireHeader_any 0 b2 b3 (Or.inl rfl) hb2 hb3]
    | rw [evalByteCastAfterOperand_wireHeader_any 1 b2 b3 (Or.inr rfl) hb2 hb3]) <;>
  (dsimp only [
      Mir.WireframeDemo.decode_wire_header.body,
      Mir.WireframeDemo.decode_wire_header.layouts,
      lookupBlock, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
      stepMirSymTreeFast, evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
      finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
      evalConstValue, evalScalarBinOpSymTree, evalTerminatorSymTreeFast,
      lookupSwitchTargetTree, MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      writePlaceValue, operandIsSigned, operandTy, sharedBorrowPerm, rigidTyIsFreeze,
      stringEq, tyIsFreeze, placeTy, resolveProjectedTy, tyIsSigned,
      invalidateConflictingBorrows, mirNormalPost,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      List.length, List.set, Option.getD,
      get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
   cases h_len : Nat.ble (b2 + 256 * b3) 1024 <;>
   · dsimp only [
       Mir.WireframeDemo.decode_wire_header.body,
       Mir.WireframeDemo.decode_wire_header.layouts,
       lookupBlock, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
       stepMirSymTreeFast, evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
       finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
       evalConstValue, evalTerminatorSymTreeFast, lookupSwitchTargetTree,
       MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
       readProjectedValue_nil, readProjectedValue_field,
       invalidateConflictingBorrows, mirNormalPost,
       GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
       List.length, List.set, Option.getD,
       get?, set?, length, Nat.add, Nat.mul, Nat.beq,
       ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
       Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq,
       ItemSpec.post, Obligations.WireframeDemo.decode_wire_header.claim,
       Obligations.WireframeDemo.decode_wire_header.refineSpec,
       Obligations.WireframeDemo.decode_wire_header.rustEnsures,
       Obligations.WireframeDemo.decode_wire_header.defaultPost, rawHeaderPost]
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
     first
     | (have h_nle1024 : ¬ (b2 + 256 * b3 ≤ 1024) := by
          intro hc; have ht := Nat.ble_eq_true_of_le hc; rw [h_len] at ht; contradiction
        dsimp only [decodedPayloadLen]
        simp only [h_c, h_nle1024, decide_true, decide_false, BEq.beq, Nat.beq,
          Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte])
     | (have h_le1024 : b2 + 256 * b3 ≤ 1024 := Nat.le_of_ble_eq_true h_len
        dsimp only [decodedPayloadLen]
        simp only [h_c, h_le1024, decide_true, BEq.beq, Nat.beq, Bool.and_self, ↓reduceIte]))

private theorem wp_invalid_b1 (b1' b2 b3 : Nat) :
    Hold
      (wpBlockLinear False Mir.WireframeDemo.decode_wire_header.body
        (entryBB Mir.WireframeDemo.decode_wire_header.body).terminator
        (mirNormalPost
          (fun retVal _ =>
            Obligations.WireframeDemo.decode_wire_header.claim.post
              [rawHeaderValue 1 (b1' + 1 + 1) b2 b3] retVal))
        0 0 (defaultSpecSteps Mir.WireframeDemo.decode_wire_header.body)
        (entryBB Mir.WireframeDemo.decode_wire_header.body).statements
        (initLocalsAux 0 Mir.WireframeDemo.decode_wire_header.body.localDecls
          [rawHeaderValue 1 (b1' + 1 + 1) b2 b3])
        (initMachineState Mir.WireframeDemo.decode_wire_header.body
          [rawHeaderValue 1 (b1' + 1 + 1) b2 b3]).memory) := by
  have h_c : ¬ (b1' + 1 + 1 ≤ 1) := by omega
  dsimp only [
    Obligations.WireframeDemo.decode_wire_header.claim,
    Mir.WireframeDemo.decode_wire_header.body,
    Mir.WireframeDemo.decode_wire_header.layouts,
    rawHeaderValue,
    defaultSpecSteps, entryBB, dummyBB, lookupBlock,
    wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
    stepMirSymTreeFast, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast, evalOperandFast, evalConstValue,
    evalScalarBinOpSymTree, evalTerminatorSymTreeFast,
    lookupSwitchTargetTree,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, emptyMemory,
    readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
    writePlaceValue,
    operandIsSigned, operandTy, sharedBorrowPerm, rigidTyIsFreeze, stringEq,
    tyIsFreeze, placeTy, resolveProjectedTy, tyIsSigned,
    invalidateConflictingBorrows, mirNormalPost,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
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

private theorem wp_invalid_b0 (b0 b1 b2 b3 : Nat) (h_v1 : b0 ≠ 1) :
    Hold
      (wpBlockLinear False Mir.WireframeDemo.decode_wire_header.body
        (entryBB Mir.WireframeDemo.decode_wire_header.body).terminator
        (mirNormalPost
          (fun retVal _ =>
            Obligations.WireframeDemo.decode_wire_header.claim.post
              [rawHeaderValue b0 b1 b2 b3] retVal))
        0 0 (defaultSpecSteps Mir.WireframeDemo.decode_wire_header.body)
        (entryBB Mir.WireframeDemo.decode_wire_header.body).statements
        (initLocalsAux 0 Mir.WireframeDemo.decode_wire_header.body.localDecls
          [rawHeaderValue b0 b1 b2 b3])
        (initMachineState Mir.WireframeDemo.decode_wire_header.body
          [rawHeaderValue b0 b1 b2 b3]).memory) := by
  have h_cases : b0 = 0 ∨ ∃ b0', b0 = b0' + 1 + 1 := by
    rcases b0 with _ | _ | b0'
    · exact Or.inl rfl
    · exact False.elim (h_v1 rfl)
    · exact Or.inr ⟨b0', rfl⟩
  rcases h_cases with rfl | ⟨b0', rfl⟩ <;>
  · dsimp only [
      Obligations.WireframeDemo.decode_wire_header.claim,
      Mir.WireframeDemo.decode_wire_header.body,
      Mir.WireframeDemo.decode_wire_header.layouts, rawHeaderValue,
      defaultSpecSteps, entryBB, dummyBB, lookupBlock,
      wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
      stepMirSymTreeFast, evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
      finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
      evalConstValue, evalScalarBinOpSymTree, evalTerminatorSymTreeFast,
      lookupSwitchTargetTree, MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux, emptyMemory,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      writePlaceValue, operandIsSigned, operandTy, sharedBorrowPerm, rigidTyIsFreeze,
      stringEq, tyIsFreeze, placeTy, resolveProjectedTy, tyIsSigned,
      invalidateConflictingBorrows, mirNormalPost,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq,
      ItemSpec.post, Obligations.WireframeDemo.decode_wire_header.refineSpec,
      Obligations.WireframeDemo.decode_wire_header.rustEnsures,
      Obligations.WireframeDemo.decode_wire_header.defaultPost, rawHeaderPost]
    refine ⟨⟨trivial, ?_⟩⟩
    intro b0'' b1' b2' b3' _ _ _ _ h_eq
    injection h_eq with h_hd _
    injection h_hd with _ h_f
    injection h_f with h0 _
    injection h0 with h0'; injection h0' with hb0_eq _
    rw [← hb0_eq]
    first
    | rfl
    | (have h_beq_f : (b0' + 1 + 1 == 1) = false := rfl
       dsimp only [decodedPayloadLen]
       simp only [h_beq_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte])

/-- Universal verification certificate for repaired `decode_wire_header`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.decode_wire_header.claim := by
  refine verifyMirNoPanic_of_blockLinear _ rfl rfl rfl ?_
  intro args h_pre
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
