import Trusted
import Anneal
import Mir.FuchsiaUsercopy.fidl_chunk_padding_len
import Obligations.FuchsiaUsercopy.fidl_chunk_padding_len
import Specs.FuchsiaUsercopy.fidl_chunk_padding_len

namespace Proof.FuchsiaUsercopy.fidl_chunk_padding_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.fidl_chunk_padding_len.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨es, len, h_es, h_len, rfl⟩, rfl⟩
  -- `pre` admits 12 concrete `(es, len)` pairs; each one runs the same
  -- straight-line path, and every overflow / zero-divisor `assert` holds.
  rcases h_es with rfl | rfl | rfl <;> rcases h_len with rfl | rfl | rfl | rfl <;>
  · apply lift_PureMirConverges rfl
    -- bb0: `_4 = MulWithOverflow(copy _1, copy _2); assert(!_4.1) -> bb1`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    -- bb1: `_3 = move (_4.0); _7 = AddWithOverflow(copy _3, const 7); assert(!_7.1) -> bb2`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    -- bb2: `_6 = move (_7.0); _8 = Eq(const 8, const 0); assert(!_8) -> bb3`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    -- bb3: `_5 = Div(move _6, const 8); _10 = MulWithOverflow(copy _5, const 8); assert(!_10.1) -> bb4`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    -- bb4: `_9 = move (_10.0); _12 = SubWithOverflow(copy _9, copy _3); assert(!_12.1) -> bb5`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    -- bb5: `_11 = move (_12.0); _0 = (copy _3, copy _11); return`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    rintro _ _ ⟨⟩
    exact ⟨rfl, by decide, by decide⟩

end Proof.FuchsiaUsercopy.fidl_chunk_padding_len
