import Trusted
import Anneal
import Mir.FuchsiaUsercopy.assume_initialized_until_split_len
import Obligations.FuchsiaUsercopy.assume_initialized_until_split_len
import Specs.FuchsiaUsercopy.assume_initialized_until_split_len

namespace Proof.FuchsiaUsercopy.assume_initialized_until_split_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.assume_initialized_until_split_len.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FuchsiaUsercopy.assume_initialized_until_split_len.statefulClaim 20 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨buf_len, init_until, h_le, h_lt, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (dsimp at *; try simp_all; try omega)
  all_goals (
    intro bl' iu' h_eq
    injection h_eq with h1 ht1
    injection ht1 with h2 _
    injection h1 with hs1
    injection h2 with hs2
    cases hs1; cases hs2
    refine ⟨?_, by omega⟩
    congr 1; congr 1; congr 1; congr 1; congr 1; omega
  )

end Proof.FuchsiaUsercopy.assume_initialized_until_split_len
