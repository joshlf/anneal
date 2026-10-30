import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FxfsPlatformPager.pager_query_vmo_stats_assume_init
import Obligations.FxfsPlatformPager.pager_query_vmo_stats_assume_init
import Specs.FxfsPlatformPager.pager_query_vmo_stats_assume_init

namespace Proof.FxfsPlatformPager.pager_query_vmo_stats_assume_init

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.pager_query_vmo_stats_assume_init.statefulClaim := by
  refine verifyStatefulMirBounded Obligations.FxfsPlatformPager.pager_query_vmo_stats_assume_init.statefulClaim 35 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨ok, rw_val, h_ok, h_rw, h_args⟩, h_mem⟩
  have h1 : ok = 0 ∨ ok = 1 := by omega
  have h2 : rw_val = 0 ∨ rw_val = 1 := by omega
  clear h_ok h_rw
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    { subst h_args; subst h_mem
      intro retVal mem' h_out
      injection h_out with h_pair
      injection h_pair with h_ret _
      exact h_ret.symm }

end Proof.FxfsPlatformPager.pager_query_vmo_stats_assume_init
