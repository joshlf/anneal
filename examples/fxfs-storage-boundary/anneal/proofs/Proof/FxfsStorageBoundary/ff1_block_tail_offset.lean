import Trusted
import Anneal
import Mir.FxfsStorageBoundary.ff1_block_tail_offset
import Obligations.FxfsStorageBoundary.ff1_block_tail_offset
import Specs.FxfsStorageBoundary.ff1_block_tail_offset

namespace Proof.FxfsStorageBoundary.ff1_block_tail_offset

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.ff1_block_tail_offset.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FxfsStorageBoundary.ff1_block_tail_offset.statefulClaim 100 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨d, h_d, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (dsimp at *; try simp_all; try omega)
  all_goals (
    intro d' h_eq
    injection h_eq with h_head _
    injection h_head with h_s1
    cases h_s1
    congr 1; congr 1; omega
  )

end Proof.FxfsStorageBoundary.ff1_block_tail_offset
