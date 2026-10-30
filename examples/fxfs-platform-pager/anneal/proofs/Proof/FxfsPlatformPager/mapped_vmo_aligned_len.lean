import Trusted
import Anneal
import Mir.FxfsPlatformPager.mapped_vmo_aligned_len
import Obligations.FxfsPlatformPager.mapped_vmo_aligned_len
import Specs.FxfsPlatformPager.mapped_vmo_aligned_len

namespace Proof.FxfsPlatformPager.mapped_vmo_aligned_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.mapped_vmo_aligned_len.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FxfsPlatformPager.mapped_vmo_aligned_len.statefulClaim 30 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨len, ps, h_len, h_ps, rfl⟩, rfl⟩
  rcases h_len with rfl | rfl | rfl <;>
    rcases h_ps with rfl | rfl
  all_goals (
    conv => whnf
    intro len' ps' h_eq
    injection h_eq with h1 h_t1
    injection h_t1 with h2 _
    injection h1 with hs1
    injection h2 with hs2
    cases hs1; cases hs2
    rfl
  )

end Proof.FxfsPlatformPager.mapped_vmo_aligned_len
