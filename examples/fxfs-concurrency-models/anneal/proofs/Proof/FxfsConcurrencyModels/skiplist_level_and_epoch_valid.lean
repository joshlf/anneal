import Trusted
import Anneal
import Mir.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
import Obligations.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
import Specs.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

namespace Proof.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

set_option maxHeartbeats 10000000 in
theorem verified :
    StatefulVerificationResult
      Obligations.FxfsConcurrencyModels.skiplist_level_and_epoch_valid.statefulClaim := by
  refine verifyStatefulMirNoPanicSym
    Obligations.FxfsConcurrencyModels.skiplist_level_and_epoch_valid.statefulClaim 100 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨lvl, max_lvl, readers, h_lvl, h_max, h_readers, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (try dsimp [expectedSkiplistRet] at *; try simp_all [expectedSkiplistRet]; try omega)

end Proof.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
