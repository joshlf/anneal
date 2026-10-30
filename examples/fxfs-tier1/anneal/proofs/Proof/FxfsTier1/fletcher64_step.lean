import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FxfsTier1.fletcher64_step
import Obligations.FxfsTier1.fletcher64_step
import Specs.FxfsTier1.fletcher64_step

namespace Proof.FxfsTier1.fletcher64_step

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FxfsTier1.fletcher64_step

/-- Proof that `fletcher64_step` (`fxfs/src/checksum.rs:21-38`) is free of Undefined Behavior
    and panics (`BinOp.addWithOverflow`, `BinOp.rem`) and returns the Fletcher-64 accumulator pair. -/
theorem verified :
    StatefulVerificationResult Obligations.FxfsTier1.fletcher64_step.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FxfsTier1.fletcher64_step.statefulClaim 28 ?_
  intro args mem h_pre
  rcases h_pre with ⟨rfl, rfl⟩
  rfl

end Proof.FxfsTier1.fletcher64_step
