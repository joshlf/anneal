import Trusted
import Anneal.MirLiftCore
import Mir.FxfsTier1.ptr_slice_copy4
import Obligations.FxfsTier1.ptr_slice_copy4
import Specs.FxfsTier1.ptr_slice_copy4

namespace Proof.FxfsTier1.ptr_slice_copy4

open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsTier1.ptr_slice_copy4.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_wpConverges _ ?_
  rintro _ _ ⟨rfl, rfl⟩
  exact MirWpConverges.of_runMirBounded
    (fuel := defaultCfgSteps Mir.FxfsTier1.ptr_slice_copy4.body)
    rfl
    ⟨rfl, rfl⟩

end Proof.FxfsTier1.ptr_slice_copy4
