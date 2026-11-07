import Trusted
import Anneal
import Mir.WireframeDemo.decode_wire_header
import Specs.WireframeDemo.decode_wire_header
import Obligations.WireframeDemo.decode_wire_header

namespace Proof.WireframeDemo.decode_wire_header

set_option maxRecDepth 8192
set_option maxHeartbeats 400000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.PureMirExec
open Anneal.MirLiftCore
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

private theorem post_of_val_eq (b0 b1 b2 b3 v : Nat)
    (hv : v = decodedPayloadLen b0 b1 b2 b3) :
    Obligations.WireframeDemo.decode_wire_header.claim.post
      [rawHeaderValue b0 b1 b2 b3]
      (.scalar { bits := v, sizeBytes := 2 }) := by
  subst hv
  refine ⟨trivial, ?_⟩
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
  rfl

private theorem evalPureStmtNorm_assign_local_of_evalRvalue
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat}
    {env env' : PureEnv} {dstLoc : Local} {rv : Rvalue} {span : String}
    {val : Value} {oldSlot : LocalSlot}
    (h_pure : isPureStatement (.assign { local_ := dstLoc, projection := [] } rv) = true)
    (h_rv : evalRvalue env rv emptyMemory body.localDecls body.layouts = .ok val env emptyMemory)
    (h_get : get? env dstLoc = some oldSlot)
    (h_live : oldSlot ≠ .dead)
    (h_set : (set? env dstLoc (.init val)).bind forcePureEnv? = some env') :
    evalPureStmtNorm body bbIdx stmtIdx env
      { kind := .assign { local_ := dstLoc, projection := [] } rv, span := span } = some env' := by
  dsimp only [evalPureStmtNorm, evalPureStmt]
  rw [h_pure]
  dsimp only [↓reduceIte, evalStmt, PureState.toMachineState]
  rw [h_rv]
  dsimp only [emptyMemory]
  rw [h_get]
  cases oldSlot with
  | dead => exact False.elim (h_live rfl)
  | uninit | init _ =>
    dsimp only
    cases hSet : set? env dstLoc (.init val) with
    | none => rw [hSet] at h_set; nomatch h_set
    | some locals₂ =>
      rw [hSet] at h_set
      exact h_set

private theorem lift_valid_header
    (b1 b2 b3 : Nat) (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 < 256) (hb3 : b3 < 256) :
    LiftBlock Mir.WireframeDemo.decode_wire_header.body 0
      (initPureEnv Mir.WireframeDemo.decode_wire_header.body [rawHeaderValue 1 b1 b2 b3])
      (Obligations.WireframeDemo.decode_wire_header.claim.post [rawHeaderValue 1 b1 b2 b3])
      30 := by
  rcases hb1 with rfl | rfl <;>
  · -- bb0 -> bb1 -> bb3 -> bb4 -> bb6
    apply LiftBlock.of_lookup rfl
    refine LiftStmtsTerminator.eval_n (n := 13) rfl (Or.inr rfl) rfl ?_
    refine LiftStmtsTerminator.term_assert ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
    apply LiftBlock.of_lookup rfl
    refine LiftStmtsTerminator.eval_n (n := 2) rfl (Or.inr rfl) rfl ?_
    refine LiftStmtsTerminator.term_switchInt (target := 3) ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
    apply LiftBlock.of_lookup rfl
    refine LiftStmtsTerminator.eval_n (n := 2) rfl (Or.inr rfl) rfl ?_
    refine LiftStmtsTerminator.term_assert ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
    apply LiftBlock.of_lookup rfl
    refine LiftStmtsTerminator.eval_n (n := 2) rfl (Or.inr rfl) rfl ?_
    refine LiftStmtsTerminator.term_switchInt (target := 6) ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
    -- bb6: stmt 0 (`_10 = copy _1 as WireHeader (Transmute)`)
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.cons_eval_norm rfl (Or.inr rfl) rfl
    · first
      | exact evalPureStmtNorm_assign_local_of_evalRvalue rfl
          (evalByteCastAfterOperand_wireHeader 0 b2 b3 (Or.inl rfl) hb2 hb3 _ _)
          rfl (fun h => nomatch h) rfl
      | exact evalPureStmtNorm_assign_local_of_evalRvalue rfl
          (evalByteCastAfterOperand_wireHeader 1 b2 b3 (Or.inr rfl) hb2 hb3 _ _)
          rfl (fun h => nomatch h) rfl
    · -- bb6: stmts 1..2 (`_12 = copy (_10.2); _11 = Gt(move _12, const 1024_u16)`)
      refine LiftStmtsTerminator.eval_n (n := 2) rfl (Or.inr rfl) rfl ?_
      cases h_len : Nat.ble (b2 + 256 * b3) 1024
      · -- payload_len > 1024: bb6 -> bb7 -> bb9
        have h_nle1024 : ¬ (b2 + 256 * b3 ≤ 1024) := by
          intro hc; have ht := Nat.ble_eq_true_of_le hc; rw [h_len] at ht; contradiction
        refine LiftStmtsTerminator.term_switchInt (target := 7) ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
        apply LiftBlock.of_lookup rfl
        refine LiftStmtsTerminator.eval_n (n := 1) rfl (Or.inr rfl) rfl ?_
        refine LiftStmtsTerminator.term_goto ?_ (Or.inr rfl) ?_ ?_; (· rfl); (· rfl)
        apply LiftBlock.of_lookup rfl
        first
        | (refine LiftStmtsTerminator.term_return ?_ (Or.inr rfl) ?_ rfl
            (post_of_val_eq 1 0 b2 b3 0 (by
              dsimp only [decodedPayloadLen]
              simp only [h_nle1024, decide_true, decide_false, BEq.beq,
                Bool.and_false, Bool.false_eq_true, ↓reduceIte])); (· rfl); (· rfl))
        | (refine LiftStmtsTerminator.term_return ?_ (Or.inr rfl) ?_ rfl
            (post_of_val_eq 1 1 b2 b3 0 (by
              dsimp only [decodedPayloadLen]
              simp only [h_nle1024, decide_true, decide_false, BEq.beq,
                Bool.and_false, Bool.false_eq_true, ↓reduceIte])); (· rfl); (· rfl))
      · -- payload_len ≤ 1024: bb6 -> bb8 -> bb9
        have h_le1024 : b2 + 256 * b3 ≤ 1024 := Nat.le_of_ble_eq_true h_len
        refine LiftStmtsTerminator.term_switchInt (target := 8) ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
        apply LiftBlock.of_lookup rfl
        refine LiftStmtsTerminator.eval_n (n := 1) rfl (Or.inr rfl) rfl ?_
        refine LiftStmtsTerminator.term_goto ?_ (Or.inr rfl) ?_ ?_; (· rfl); (· rfl)
        apply LiftBlock.of_lookup rfl
        first
        | (refine LiftStmtsTerminator.term_return ?_ (Or.inr rfl) ?_ rfl
            (post_of_val_eq 1 0 b2 b3 (b2 + 256 * b3) (by
              dsimp only [decodedPayloadLen]; simp only [h_le1024, decide_true]; rfl)); (· rfl); (· rfl))
        | (refine LiftStmtsTerminator.term_return ?_ (Or.inr rfl) ?_ rfl
            (post_of_val_eq 1 1 b2 b3 (b2 + 256 * b3) (by
              dsimp only [decodedPayloadLen]; simp only [h_le1024, decide_true]; rfl)); (· rfl); (· rfl))

private theorem lift_invalid_b1 (b1' b2 b3 : Nat) :
    LiftBlock Mir.WireframeDemo.decode_wire_header.body 0
      (initPureEnv Mir.WireframeDemo.decode_wire_header.body [rawHeaderValue 1 (b1' + 1 + 1) b2 b3])
      (Obligations.WireframeDemo.decode_wire_header.claim.post [rawHeaderValue 1 (b1' + 1 + 1) b2 b3])
      26 := by
  have h_c : ¬ (b1' + 1 + 1 ≤ 1) := by omega
  -- bb0 -> bb1 -> bb3 -> bb4 -> bb5 -> bb9
  apply LiftBlock.of_lookup rfl
  refine LiftStmtsTerminator.eval_n (n := 13) rfl (Or.inr rfl) rfl ?_
  refine LiftStmtsTerminator.term_assert ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
  apply LiftBlock.of_lookup rfl
  refine LiftStmtsTerminator.eval_n (n := 2) rfl (Or.inr rfl) rfl ?_
  refine LiftStmtsTerminator.term_switchInt (target := 3) ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
  apply LiftBlock.of_lookup rfl
  refine LiftStmtsTerminator.eval_n (n := 2) rfl (Or.inr rfl) rfl ?_
  refine LiftStmtsTerminator.term_assert ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
  apply LiftBlock.of_lookup rfl
  refine LiftStmtsTerminator.eval_n (n := 2) rfl (Or.inr rfl) rfl ?_
  refine LiftStmtsTerminator.term_switchInt (target := 5) ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
  apply LiftBlock.of_lookup rfl
  refine LiftStmtsTerminator.eval_n (n := 1) rfl (Or.inr rfl) rfl ?_
  refine LiftStmtsTerminator.term_goto ?_ (Or.inr rfl) ?_ ?_; (· rfl); (· rfl)
  apply LiftBlock.of_lookup rfl
  refine LiftStmtsTerminator.term_return ?_ (Or.inr rfl) ?_ rfl
    (post_of_val_eq 1 (b1' + 1 + 1) b2 b3 0 (by
      dsimp only [decodedPayloadLen]
      simp only [h_c, decide_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte])); (· rfl); (· rfl)

private theorem lift_invalid_b0 (b0 b1 b2 b3 : Nat) (h_v1 : b0 ≠ 1) :
    LiftBlock Mir.WireframeDemo.decode_wire_header.body 0
      (initPureEnv Mir.WireframeDemo.decode_wire_header.body [rawHeaderValue b0 b1 b2 b3])
      (Obligations.WireframeDemo.decode_wire_header.claim.post [rawHeaderValue b0 b1 b2 b3])
      20 := by
  have h_cases : b0 = 0 ∨ ∃ b0', b0 = b0' + 1 + 1 := by
    rcases b0 with _ | _ | b0'
    · exact Or.inl rfl
    · exact False.elim (h_v1 rfl)
    · exact Or.inr ⟨b0', rfl⟩
  rcases h_cases with rfl | ⟨b0', rfl⟩ <;>
  · -- bb0 -> bb1 -> bb2 -> bb9
    apply LiftBlock.of_lookup rfl
    refine LiftStmtsTerminator.eval_n (n := 13) rfl (Or.inr rfl) rfl ?_
    refine LiftStmtsTerminator.term_assert ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
    apply LiftBlock.of_lookup rfl
    refine LiftStmtsTerminator.eval_n (n := 2) rfl (Or.inr rfl) rfl ?_
    refine LiftStmtsTerminator.term_switchInt (target := 2) ?_ (Or.inr rfl) ?_ rfl ?_ ?_; (· rfl); (· rfl); (· rfl)
    apply LiftBlock.of_lookup rfl
    refine LiftStmtsTerminator.eval_n (n := 1) rfl (Or.inr rfl) rfl ?_
    refine LiftStmtsTerminator.term_goto ?_ (Or.inr rfl) ?_ ?_; (· rfl); (· rfl)
    apply LiftBlock.of_lookup rfl
    refine LiftStmtsTerminator.term_return ?_ (Or.inr rfl) ?_ rfl
      (post_of_val_eq _ b1 b2 b3 0 (by
        first
        | rfl
        | (have h_beq_f : (b0' + 1 + 1 == 1) = false := rfl
           dsimp only [decodedPayloadLen]
           simp only [h_beq_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte]))); (· rfl); (· rfl)

/-- Universal verification certificate for `decode_wire_header` via `MirLiftCore`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.decode_wire_header.claim := by
  refine verifyMirNoPanic_of_pureExec _ rfl ?_
  intro args h_pre
  rcases h_pre with ⟨_, b0, b1, b2, b3, hb0, hb1, hb2, hb3, h_args⟩
  rw [h_args]
  by_cases h_v1 : b0 = 1
  · subst h_v1
    by_cases h_c : b1 ≤ 1
    · exact lift_PureMirConverges rfl (lift_valid_header b1 b2 b3 (by omega) hb2 hb3)
    · rcases b1 with _ | _ | b1'
      · omega
      · omega
      · exact lift_PureMirConverges rfl (lift_invalid_b1 b1' b2 b3)
  · exact lift_PureMirConverges rfl (lift_invalid_b0 b0 b1 b2 b3 h_v1)

end Proof.WireframeDemo.decode_wire_header
