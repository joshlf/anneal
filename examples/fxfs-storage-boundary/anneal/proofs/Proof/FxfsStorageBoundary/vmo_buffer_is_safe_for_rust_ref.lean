import Trusted
import Anneal.MirLiftCore
import Mir.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
import Obligations.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
import Specs.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref

namespace Proof.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref

open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨_, -, rfl⟩, rfl⟩
  apply lift_PureMirConverges rfl
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ ⟨⟩
  rfl

end Proof.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
