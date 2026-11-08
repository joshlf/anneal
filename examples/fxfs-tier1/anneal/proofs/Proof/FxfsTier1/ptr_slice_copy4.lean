import Trusted
import Anneal.MirFuelFree
import Anneal.MirLiftCore
import Mir.FxfsTier1.ptr_slice_copy4
import Obligations.FxfsTier1.ptr_slice_copy4
import Specs.FxfsTier1.ptr_slice_copy4

namespace Proof.FxfsTier1.ptr_slice_copy4

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Specs.FxfsTier1.ptr_slice_copy4

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsTier1.ptr_slice_copy4.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_wpConverges
    Obligations.FxfsTier1.ptr_slice_copy4.statefulClaim ?_
  rintro args mem ⟨rfl, rfl⟩
  exact MirWpConverges.of_runMirBounded
    (fuel := defaultCfgSteps Mir.FxfsTier1.ptr_slice_copy4.body)
    rfl
    ⟨rfl, rfl⟩

end Proof.FxfsTier1.ptr_slice_copy4
