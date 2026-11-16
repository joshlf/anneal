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
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.SepLogicLenses
open Specs.WireframeDemo.decode_wire_header

/-!
`decode_wire_header` via `MirLiftCore` join sharing. CFG: `bb0 → bb1 → {bb3, bb2}`,
`bb3 → bb4 → {bb6, bb5}`, `bb6 → {bb8, bb7}`, and the exits `bb2`, `bb5`, `bb7`,
`bb8` all `goto bb9` (`return`). `lift_path` is a single postcondition-parametric
`LiftBlockToJoin` path from `bb0` to `bb9` over symbolic header bytes (split only at
the three `switchInt` guards), and `verified` proves `bb9` once under `RetInv`.
-/

/-- The trusted `transmute` of the `[1, b1, b2, b3] : [u8; 4]` header into
`WireHeader { version, flag, payload_len }` (byte-cast through
`encodeByteCastSourceBytes` / `decodeTypedValueFromBytes`); the `bool` flag byte
`b1` is a valid `bool` image only for `b1 ≤ 1`. -/
private theorem evalByteCastAfterOperand_wireHeader
    (b1 b2 b3 : Nat) (hb1 : b1 ≤ 1) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (locals' : List LocalSlot) (mem : Memory) :
    evalByteCastAfterOperand Mir.WireframeDemo.decode_wire_header.body
      (.copy { local_ := 1, projection := [] })
      { kind := .adt "wireframe_demo::WireHeader" [], layoutIdx := 5 }
      (rawHeaderValue 1 b1 b2 b3) locals' mem =
    .ok (.aggregate 0 [.scalar { bits := 1, sizeBytes := 1 }, .scalar { bits := b1, sizeBytes := 1 },
      .scalar { bits := b2 + 256 * b3, sizeBytes := 2 }]) locals' mem := by
  have h_b1 : decodeScalarLayoutBytesNoForge
      (ScalarLayout.initialized (.int 8 false) { start := 0, end_ := 1 })
      [.init (UInt8.ofNat b1) none] = some (.scalar { bits := b1, sizeBytes := 1 }) :=
    match b1, hb1 with | 0, _ => rfl | 1, _ => rfl | _ + 2, h => nomatch h
  conv => lhs; whnf
  show (match (match (match (match decodeScalarLayoutBytesNoForge
        (ScalarLayout.initialized (.int 8 false) { start := 0, end_ := 1 })
        [.init (UInt8.ofNat b1) none] with
      | none => none
      | some v1 => match (match decodeScalarLayoutBytesNoForge
          (ScalarLayout.initialized (.int 16 false) { start := 0, end_ := 65535 })
          [.init (UInt8.ofNat b2) none, .init (UInt8.ofNat b3) none] with
          | none => none | some v => some [v]) with
        | some vs => some (v1 :: vs) | none => none) with
      | some vs => some (.scalar { bits := 1, sizeBytes := 1 } :: vs) | none => none) with
    | some vals => some (Value.aggregate 0 vals) | none => none) with
    | some v' => RvalueEvalResult.ok v' locals' mem | none => .ub) = _
  rw [h_b1, decodeScalarLayoutBytesNoForge_u16_le b2 b3 hb2 hb3]

/-- Return-join invariant shared by every path into `bb9`: slot `_0` holds a
value satisfying the claim postcondition. -/
private abbrev RetInv (args : List Value) (env : PureEnv) : Prop :=
  ∃ v, get? env 0 = some (.init v) ∧
    Obligations.WireframeDemo.decode_wire_header.claim.post args v

/-- Every exit block (`bb2`, `bb5`, `bb7`, `bb8`) stores the specified payload
length, in `Prop`-guard form, into `_0` before jumping to `bb9`. -/
private theorem retInv_of {b0 b1 b2 b3 v : Nat} {env : PureEnv}
    (hv : v = if b0 = 1 ∧ b1 ≤ 1 ∧ b2 + 256 * b3 ≤ 1024 then b2 + 256 * b3 else 0)
    (h_get : get? env 0 = some (.init (.scalar { bits := v, sizeBytes := 2 }))) :
    RetInv [rawHeaderValue b0 b1 b2 b3] env := by
  refine ⟨_, h_get, trivial, fun b0' b1' b2' b3' _ _ _ _ h_eq => ?_⟩
  simp only [rawHeaderValue, List.cons.injEq, Value.aggregate.injEq, Value.scalar.injEq,
    ScalarInt.mk.injEq, and_true, true_and] at h_eq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h_eq
  subst hv
  simp only [decodedPayloadLen, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]

private theorem ready : checkMirLiftReady Mir.WireframeDemo.decode_wire_header.body = true := rfl

private theorem lift_path (b0 b1 b2 b3 : Nat) (hb2 : b2 < 256) (hb3 : b3 < 256) :
    LiftBlockToJoin Mir.WireframeDemo.decode_wire_header.body 0
      (initPureEnv Mir.WireframeDemo.decode_wire_header.body [rawHeaderValue b0 b1 b2 b3]) 9
      (RetInv [rawHeaderValue b0 b1 b2 b3]) := by
  have hr := ready
  -- bb0 (`0 < 4` bounds check) -> bb1 (`raw[0] != 1`) -> {bb3, early exit bb2}
  refine LiftBlockToJoin.of_lookup (by rfl)
    (LiftStmtsToJoin.eval_rest_checked_ready hr (by rfl) (by rfl)
      (LiftStmtsToJoin.term_assert_ready hr (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (liftBlock_switchInt_diamond_toJoin (thenBb := 3) (elseBb := 2) (b0 = 1)
          hr (by rfl) (by rfl) (by rfl) (by rfl) ?_ fun h =>
            ⟨by rw [Bool.eq_false_iff.mpr (h ∘ Nat.eq_of_beq_eq_true)]; rfl,
              liftBlock_goto_toJoin hr (by rfl) (by rfl) rfl
                (LiftBlockToJoin.refl (retInv_of (ite_eq_right fun hc => h hc.1).symm rfl))⟩)))
  intro h
  subst h
  refine ⟨rfl, ?_⟩
  -- bb3 (`1 < 4` bounds check) -> bb4 (`raw[1] > 1`) -> {bb6, early exit bb5}
  refine LiftBlockToJoin.of_lookup (by rfl)
    (LiftStmtsToJoin.eval_rest_checked_ready hr (by rfl) (by rfl)
      (LiftStmtsToJoin.term_assert_ready hr (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (liftBlock_switchInt_diamond_toJoin (thenBb := 6) (elseBb := 5) (b1 ≤ 1)
          hr (by rfl) (by rfl) (by rfl) (by rfl) ?_ fun h =>
            ⟨by rw [nat_ble_eq_false_of_not_le h]; rfl, liftBlock_goto_toJoin hr (by rfl) (by rfl) rfl
              (LiftBlockToJoin.refl (retInv_of (ite_eq_right fun hc => h hc.2.1).symm rfl))⟩)))
  intro h1
  refine ⟨by rw [Nat.ble_eq_true_of_le h1]; rfl, ?_⟩
  -- bb6: `_10 = transmute raw`, `_12 = _10.2`, `_11 = _12 > 1024` -> {bb8, bb7}
  refine LiftBlockToJoin.of_lookup (by rfl) ?_
  refine LiftStmtsToJoin.cons_eval_checked_ready hr (by rfl) rfl
    ((evalPureStmtChecked_eq_evalPureStmtNorm _ _ _ _ _).trans
      (evalPureStmtNorm_assign_local_of_setSpineChecked? rfl
        (evalByteCastAfterOperand_wireHeader b1 b2 b3 h1 hb2 hb3 _ _)
        rfl (fun h => nomatch h) rfl))
    (LiftStmtsToJoin.eval_rest_checked_ready hr (by rfl) (by rfl)
      (LiftStmtsToJoin.term_switchInt_cases_ready (thenBb := 8) (elseBb := 7)
        hr (by rfl) (by rfl) (by rfl) (by rfl) (b2 + 256 * b3 ≤ 1024) ?_ ?_))
  · intro h
    exact ⟨by rw [Nat.ble_eq_true_of_le h]; rfl, liftBlock_goto_toJoin hr (by rfl) (by rfl) rfl
      (LiftBlockToJoin.refl (retInv_of (ite_eq_left ⟨rfl, h1, h⟩).symm rfl))⟩
  · intro h
    exact ⟨by rw [nat_ble_eq_false_of_not_le h]; rfl, liftBlock_goto_toJoin hr (by rfl) (by rfl) rfl
      (LiftBlockToJoin.refl (retInv_of (ite_eq_right fun hc => h hc.2.2).symm rfl))⟩

/-- Universal verification certificate for `decode_wire_header` via `MirLiftCore`
join sharing: one postcondition-parametric entry-to-`bb9` path (`lift_path`) and a
single proof of the shared return block `bb9` under `RetInv`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.decode_wire_header.claim := by
  refine verifyMirNoPanic_of_mirLiftReady_toJoin _ 9 RetInv ready ?_ ?_
  · intro args h_pre
    rcases h_pre with ⟨_, b0, b1, b2, b3, _, _, hb2, hb3, rfl⟩
    exact lift_path b0 b1 b2 b3 hb2 hb3
  · intro args _ env ⟨_, h_get, h_post⟩
    exact LiftBlockConverges.of_lookup (by rfl)
      (LiftStmtsConverges.term_return_ready ready (by rfl) rfl rfl h_get h_post)

end Proof.WireframeDemo.decode_wire_header
