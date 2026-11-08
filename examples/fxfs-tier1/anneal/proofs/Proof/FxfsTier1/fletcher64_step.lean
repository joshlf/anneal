import Trusted
import Anneal.MirLiftCore
import Mir.FxfsTier1.fletcher64_step
import Obligations.FxfsTier1.fletcher64_step
import Specs.FxfsTier1.fletcher64_step

namespace Proof.FxfsTier1.fletcher64_step

open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore

/-- Proof that `fletcher64_step` (`fxfs/src/checksum.rs:21-38`) is free of Undefined Behavior
    and panics (`BinOp.addWithOverflow`, `BinOp.rem`) and returns the Fletcher-64 accumulator pair. -/
theorem verified :
    StatefulVerificationResult Obligations.FxfsTier1.fletcher64_step.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨rfl, rfl⟩
  apply lift_PureMirConverges rfl
  repeat (
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    first
    | apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  )
  rfl

end Proof.FxfsTier1.fletcher64_step
