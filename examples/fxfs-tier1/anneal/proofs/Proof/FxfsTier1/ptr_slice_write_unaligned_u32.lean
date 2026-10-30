import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Mir.FxfsTier1.ptr_slice_write_unaligned_u32
import Obligations.FxfsTier1.ptr_slice_write_unaligned_u32
import Specs.FxfsTier1.ptr_slice_write_unaligned_u32

namespace Proof.FxfsTier1.ptr_slice_write_unaligned_u32

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Specs.FxfsTier1.ptr_slice_write_unaligned_u32

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsTier1.ptr_slice_write_unaligned_u32.statefulClaim := by
  refine verifyStatefulMirBounded Obligations.FxfsTier1.ptr_slice_write_unaligned_u32.statefulClaim 24 ?_
  intro args mem h_pre
  rcases h_pre with ⟨rfl, rfl⟩
  intro retVal mem' h_out
  injection h_out with h_pair
  injection h_pair with h_ret h_mem
  subst h_ret h_mem
  exact ⟨rfl, rfl⟩

end Proof.FxfsTier1.ptr_slice_write_unaligned_u32
