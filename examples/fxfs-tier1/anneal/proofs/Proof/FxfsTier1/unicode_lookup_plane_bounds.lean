import Trusted
import Anneal.MirLiftCore
import Mir.FxfsTier1.unicode_lookup_plane_bounds
import Obligations.FxfsTier1.unicode_lookup_plane_bounds
import Specs.FxfsTier1.unicode_lookup_plane_bounds

namespace Proof.FxfsTier1.unicode_lookup_plane_bounds

open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore

/-- Proof that `unicode_lookup_plane_bounds` (`fxfs/unicode/src/lookup.rs:50-75`) is free of
    Undefined Behavior (`BinOp.shr`, `BinOp.subUnchecked`) and returns `Some((plane_start, len))`. -/
theorem verified :
    StatefulVerificationResult Obligations.FxfsTier1.unicode_lookup_plane_bounds.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨rfl, rfl⟩
  apply lift_PureMirConverges rfl
  repeat (
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    first
    | apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
    | apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  )
  rfl

end Proof.FxfsTier1.unicode_lookup_plane_bounds
