import Trusted
import Anneal
import Mir.FxfsPlatformPager.weak_node_downcast_type_check
import Obligations.FxfsPlatformPager.weak_node_downcast_type_check
import Specs.FxfsPlatformPager.weak_node_downcast_type_check

namespace Proof.FxfsPlatformPager.weak_node_downcast_type_check

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.weak_node_downcast_type_check.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FxfsPlatformPager.weak_node_downcast_type_check.statefulClaim 100 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨vt, tt, pnn, h_vt, h_tt, h_pnn, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (try dsimp at *; try simp_all; try omega)

end Proof.FxfsPlatformPager.weak_node_downcast_type_check
