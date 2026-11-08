import Trusted
import Anneal
import Mir.FuchsiaUsercopy.fidl_chunk_padding_len
import Obligations.FuchsiaUsercopy.fidl_chunk_padding_len
import Specs.FuchsiaUsercopy.fidl_chunk_padding_len

namespace Proof.FuchsiaUsercopy.fidl_chunk_padding_len

open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore

theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.fidl_chunk_padding_len.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨es, len, h_es, h_len, rfl⟩, rfl⟩
  -- `pre` admits 12 concrete `(es, len)` pairs; each one runs the same
  -- straight-line path, and every overflow / zero-divisor `assert` holds.
  rcases h_es with rfl | rfl | rfl <;> rcases h_len with rfl | rfl | rfl | rfl <;>
  · apply lift_PureMirConverges rfl
    -- bb0..bb4 each end in an `assert` that holds for these inputs: bb0
    -- (`es * len`), bb1 (`+ 7`), bb3 (`/ 8 * 8`), and bb4 (`- (es * len)`)
    -- check for overflow, and bb2 checks the constant divisor `8 != 0`.
    repeat
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
