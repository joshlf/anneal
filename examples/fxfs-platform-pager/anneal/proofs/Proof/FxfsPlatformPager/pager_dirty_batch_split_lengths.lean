import Trusted
import Anneal
import Mir.FxfsPlatformPager.pager_dirty_batch_split_lengths
import Obligations.FxfsPlatformPager.pager_dirty_batch_split_lengths
import Specs.FxfsPlatformPager.pager_dirty_batch_split_lengths

namespace Proof.FxfsPlatformPager.pager_dirty_batch_split_lengths

open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore

theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.pager_dirty_batch_split_lengths.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨rs, re, cs, -, -, h_rs, h_re, h_cs, rfl⟩, rfl⟩
  -- `pre` admits eight concrete `(rs, re, cs)` triples. Each run follows the
  -- branches its inputs select through `goto`s and `switchInt`s until bb9
  -- returns.
  rcases h_rs with rfl | rfl <;> rcases h_re with rfl | rfl <;>
    rcases h_cs with rfl | rfl <;>
  · apply lift_PureMirConverges rfl
    repeat
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      first
      | apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
      | apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    -- bb9: `StorageDead(_8); _0 = (copy _6, move _7); StorageDead(_6); return`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    rintro _ _ _ ⟨⟩
    rfl

end Proof.FxfsPlatformPager.pager_dirty_batch_split_lengths
