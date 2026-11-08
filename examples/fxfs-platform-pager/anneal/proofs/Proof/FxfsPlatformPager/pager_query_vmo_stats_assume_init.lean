import Trusted
import Anneal
import Mir.FxfsPlatformPager.pager_query_vmo_stats_assume_init
import Obligations.FxfsPlatformPager.pager_query_vmo_stats_assume_init
import Specs.FxfsPlatformPager.pager_query_vmo_stats_assume_init

namespace Proof.FxfsPlatformPager.pager_query_vmo_stats_assume_init

open Trusted.VerificationResult
open Anneal.MirFuelFree

theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.pager_query_vmo_stats_assume_init.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_wpConverges _ ?_
  rintro _ _ ⟨⟨ok, rw_val, h_ok, h_rw, rfl⟩, rfl⟩
  -- bb2 takes raw pointers to `_2` and `_3` and copies through them, so the
  -- body is not pure. `pre` admits four concrete `(status_ok, rw)` pairs, and
  -- each run steps deterministically to `return`: bb1 returns `None`, and bb2
  -- returns `Some(rw == 1)`.
  rcases (by omega : ok = 0 ∨ ok = 1) with rfl | rfl <;>
    rcases (by omega : rw_val = 0 ∨ rw_val = 1) with rfl | rfl <;>
  · refine MirWpConverges.step ?_
    repeat refine MirExecWpConverges.step ?_
    exact rfl

end Proof.FxfsPlatformPager.pager_query_vmo_stats_assume_init
