import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Anneal.PureMirExec
import Anneal.MirLiftCore
import Mir.FxfsTier1.unicode_lookup_plane_bounds
import Obligations.FxfsTier1.unicode_lookup_plane_bounds
import Specs.FxfsTier1.unicode_lookup_plane_bounds

namespace Proof.FxfsTier1.unicode_lookup_plane_bounds

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Specs.FxfsTier1.unicode_lookup_plane_bounds

/-- Proof that `unicode_lookup_plane_bounds` (`fxfs/unicode/src/lookup.rs:50-75`) is free of
    Undefined Behavior (`BinOp.shr`, `BinOp.subUnchecked`) and returns `Some((plane_start, len))`. -/
theorem verified :
    StatefulVerificationResult Obligations.FxfsTier1.unicode_lookup_plane_bounds.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ (by decide)
    (fun args mem h_pre => by rcases h_pre with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩)
    (fun args mem h_pre => ?_)
  rcases h_pre with ⟨rfl, rfl⟩
  apply lift_PureMirConverges (by decide)
  repeat (
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
  )
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rfl

end Proof.FxfsTier1.unicode_lookup_plane_bounds
