import Trusted
import Anneal.MirFuelFree
import Mir.FxfsPlatformPager.pager_query_vmo_stats_assume_init
import Obligations.FxfsPlatformPager.pager_query_vmo_stats_assume_init
import Specs.FxfsPlatformPager.pager_query_vmo_stats_assume_init

namespace Proof.FxfsPlatformPager.pager_query_vmo_stats_assume_init

open Trusted.VerificationResult
open Anneal.MirFuelFree

theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.pager_query_vmo_stats_assume_init.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_wpConverges _ ?_
  rintro _ _ ⟨⟨ok, rw_val, h_ok, h_rw, rfl⟩, rfl⟩
  -- `bb2` takes raw pointers to `_2` and `_3` and copies through them, so
  -- `checkPureMir` is `false`; step the concrete `(status_ok, rw)` cases
  -- directly on `MachineState`.
  match ok, rw_val, h_ok, h_rw with
  | 0, _, _, _ | 1, 0, _, _ | 1, 1, _, _ =>
    refine MirWpConverges.step ?_
    repeat refine MirExecWpConverges.step ?_
    exact rfl

end Proof.FxfsPlatformPager.pager_query_vmo_stats_assume_init
