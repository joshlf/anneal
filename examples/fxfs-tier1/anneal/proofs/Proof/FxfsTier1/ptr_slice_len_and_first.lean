import Trusted
import Anneal.MirLiftCore
import Mir.FxfsTier1.ptr_slice_len_and_first
import Obligations.FxfsTier1.ptr_slice_len_and_first
import Specs.FxfsTier1.ptr_slice_len_and_first

namespace Proof.FxfsTier1.ptr_slice_len_and_first

open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsTier1.ptr_slice_len_and_first.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_wpConverges _ ?_
  rintro _ _ ⟨rfl, rfl⟩
  exact MirWpConverges.of_runMirBounded
    (fuel := defaultCfgSteps Mir.FxfsTier1.ptr_slice_len_and_first.body)
    rfl
    rfl

end Proof.FxfsTier1.ptr_slice_len_and_first
