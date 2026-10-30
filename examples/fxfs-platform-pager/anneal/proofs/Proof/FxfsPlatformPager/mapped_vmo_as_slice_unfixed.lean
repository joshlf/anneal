import Trusted
import Anneal
import Mir.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
import Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
import Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

namespace Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower

set_option maxHeartbeats 10000000 in
theorem verified : UbExceptionVerificationResult Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim := by
  refine verifyUbExceptionMirBounded
    Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim 20 ?_ ?_
  · intro args mem h_pre h_strict
    rcases h_pre with ⟨mapped_len, pb, h_ml, _, rfl, rfl⟩
    rcases h_strict with ⟨_, h_eq⟩
    injection h_eq with _ ht1
    injection ht1 with _ ht2
    injection ht2 with h_pb_head _
    injection h_pb_head with h_pb_sc
    injection h_pb_sc with h_pb_bits _
    subst h_pb_bits
    conv => whnf
    intro retVal mem' h_out
    injection h_out with h_pair
    injection h_pair with h_ret h_mem
    subst h_ret h_mem
    refine ⟨rfl, ?_⟩
    intro ml' pb' h_args
    injection h_args with h1 _
  · intro args mem h_pre
    rcases h_pre with ⟨mapped_len, pb, h_ml, h_pb, rfl, rfl⟩
    rcases h_pb with rfl | rfl
    · conv => whnf
      intro retVal mem' h_out
      injection h_out with h_pair
      injection h_pair with h_ret h_mem
      subst h_ret h_mem
      refine ⟨rfl, ?_⟩
      intro ml' pb' h_args
      injection h_args with h1 _
    · conv => whnf
      trivial

end Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
