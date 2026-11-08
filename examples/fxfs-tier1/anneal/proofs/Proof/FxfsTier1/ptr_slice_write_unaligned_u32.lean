import Trusted
import Anneal.MirFuelFree
import Anneal.MirLiftCore
import Mir.FxfsTier1.ptr_slice_write_unaligned_u32
import Obligations.FxfsTier1.ptr_slice_write_unaligned_u32
import Specs.FxfsTier1.ptr_slice_write_unaligned_u32

namespace Proof.FxfsTier1.ptr_slice_write_unaligned_u32

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Specs.FxfsTier1.ptr_slice_write_unaligned_u32

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsTier1.ptr_slice_write_unaligned_u32.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_wpConverges
    Obligations.FxfsTier1.ptr_slice_write_unaligned_u32.statefulClaim ?_
  rintro args mem ⟨rfl, rfl⟩
  exact MirWpConverges.of_runMirBounded
    (fuel := defaultCfgSteps Mir.FxfsTier1.ptr_slice_write_unaligned_u32.body)
    rfl
    ⟨rfl, rfl⟩

end Proof.FxfsTier1.ptr_slice_write_unaligned_u32
