import Trusted
import Anneal.MirLiftCore
import Mir.FxfsPlatformPager.mapped_vmo_aligned_len
import Obligations.FxfsPlatformPager.mapped_vmo_aligned_len
import Specs.FxfsPlatformPager.mapped_vmo_aligned_len

namespace Proof.FxfsPlatformPager.mapped_vmo_aligned_len

open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore

theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.mapped_vmo_aligned_len.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨_, _, rfl | rfl | rfl, rfl | rfl, rfl⟩, rfl⟩ <;>
  · apply lift_PureMirConverges rfl
    repeat
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      first
      | apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
      | apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
      | apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
      | apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    rintro _ _ ⟨⟩
    rfl

end Proof.FxfsPlatformPager.mapped_vmo_aligned_len
