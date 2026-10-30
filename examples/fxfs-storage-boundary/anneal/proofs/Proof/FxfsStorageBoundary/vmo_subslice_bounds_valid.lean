import Trusted
import Anneal
import Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid
import Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid
import Specs.FxfsStorageBoundary.vmo_subslice_bounds_valid

namespace Proof.FxfsStorageBoundary.vmo_subslice_bounds_valid

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid.statefulClaim 100 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨base, len, s, e, h_se, h_el, h_bound, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (dsimp at *; try simp_all; try omega)
  all_goals (
    intro base' len' s' e' h_eq
    injection h_eq with h_head1 h_tail1
    injection h_tail1 with h_head2 h_tail2
    injection h_tail2 with h_head3 h_tail3
    injection h_tail3 with h_head4 _
    injection h_head1 with h_s1
    injection h_head2 with h_s2
    injection h_head3 with h_s3
    injection h_head4 with h_s4
    cases h_s1; cases h_s2; cases h_s3; cases h_s4
    congr 1; congr 1; omega
  )

end Proof.FxfsStorageBoundary.vmo_subslice_bounds_valid
