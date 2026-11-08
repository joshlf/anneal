import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Anneal.PureMirExec
import Anneal.MirLiftCore
import Mir.FxfsTier1.fletcher64_step
import Obligations.FxfsTier1.fletcher64_step
import Specs.FxfsTier1.fletcher64_step

namespace Proof.FxfsTier1.fletcher64_step

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Specs.FxfsTier1.fletcher64_step

/-- Proof that `fletcher64_step` (`fxfs/src/checksum.rs:21-38`) is free of Undefined Behavior
    and panics (`BinOp.addWithOverflow`, `BinOp.rem`) and returns the Fletcher-64 accumulator pair. -/
theorem verified :
    StatefulVerificationResult Obligations.FxfsTier1.fletcher64_step.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ (by decide)
    (fun args mem h_pre => by rcases h_pre with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩)
    (fun args mem h_pre => ?_)
  rcases h_pre with ⟨rfl, rfl⟩
  apply lift_PureMirConverges (by decide)
  repeat (
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
  )
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rfl

end Proof.FxfsTier1.fletcher64_step
