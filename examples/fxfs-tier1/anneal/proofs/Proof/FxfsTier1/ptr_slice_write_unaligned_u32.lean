import Trusted
import Anneal.MirLiftCore
import Mir.FxfsTier1.ptr_slice_write_unaligned_u32
import Obligations.FxfsTier1.ptr_slice_write_unaligned_u32
import Specs.FxfsTier1.ptr_slice_write_unaligned_u32

namespace Proof.FxfsTier1.ptr_slice_write_unaligned_u32

open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsTier1.ptr_slice_write_unaligned_u32.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_wpConverges _ ?_
  rintro _ _ ⟨rfl, rfl⟩
  exact MirWpConverges.of_runMirBounded
    (fuel := defaultCfgSteps Mir.FxfsTier1.ptr_slice_write_unaligned_u32.body)
    rfl
    ⟨rfl, rfl⟩

end Proof.FxfsTier1.ptr_slice_write_unaligned_u32
