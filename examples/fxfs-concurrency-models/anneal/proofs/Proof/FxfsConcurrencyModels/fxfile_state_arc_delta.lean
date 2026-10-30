import Trusted
import Anneal
import Mir.FxfsConcurrencyModels.fxfile_state_arc_delta
import Obligations.FxfsConcurrencyModels.fxfile_state_arc_delta
import Specs.FxfsConcurrencyModels.fxfile_state_arc_delta

namespace Proof.FxfsConcurrencyModels.fxfile_state_arc_delta

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified :
    StatefulVerificationResult
      Obligations.FxfsConcurrencyModels.fxfile_state_arc_delta.statefulClaim := by
  refine verifyStatefulMirNoPanicSym
    Obligations.FxfsConcurrencyModels.fxfile_state_arc_delta.statefulClaim 100 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨old_b, new_b, tomb_b, h_old, h_new, h_tomb, rfl⟩, rfl⟩
  rcases (by omega : old_b = 0 ∨ old_b = 1) with rfl | rfl <;>
    rcases (by omega : new_b = 0 ∨ new_b = 1) with rfl | rfl <;>
    rcases (by omega : tomb_b = 0 ∨ tomb_b = 1) with rfl | rfl
  all_goals (
    conv => whnf
    intro old_b' new_b' tomb_b' h_eq
    injection h_eq with h1 h_t1
    injection h_t1 with h2 h_t2
    injection h_t2 with h3 _
    injection h1 with hs1
    injection h2 with hs2
    injection h3 with hs3
    cases hs1; cases hs2; cases hs3
    exact ⟨rfl, rfl⟩
  )

end Proof.FxfsConcurrencyModels.fxfile_state_arc_delta
