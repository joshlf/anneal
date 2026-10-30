import Trusted
import Anneal
import Mir.FxfsPlatformPager.pager_dirty_batch_split_lengths
import Obligations.FxfsPlatformPager.pager_dirty_batch_split_lengths
import Specs.FxfsPlatformPager.pager_dirty_batch_split_lengths

namespace Proof.FxfsPlatformPager.pager_dirty_batch_split_lengths

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 1000000 in
theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.pager_dirty_batch_split_lengths.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FxfsPlatformPager.pager_dirty_batch_split_lengths.statefulClaim 30 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨rs, re, cs, _, _, h_rs, h_re, h_cs, rfl⟩, rfl⟩
  rcases h_rs with rfl | rfl <;>
    rcases h_re with rfl | rfl <;>
    rcases h_cs with rfl | rfl
  all_goals (
    conv => whnf
    intro rs' re' cs' h_eq
    injection h_eq with h1 h_t1
    injection h_t1 with h2 h_t2
    injection h_t2 with h3 _
    injection h1 with hs1
    injection h2 with hs2
    injection h3 with hs3
    cases hs1; cases hs2; cases hs3
    rfl
  )

end Proof.FxfsPlatformPager.pager_dirty_batch_split_lengths
