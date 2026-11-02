import Trusted
import Anneal
import Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Specs.FuchsiaUsercopy.hermetic_copy_bytes_copied

namespace Proof.FuchsiaUsercopy.hermetic_copy_bytes_copied

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied.statefulClaim 20 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨base, count, unread, h_bu, h_uc, h_un_lt, h_c_lt, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (dsimp at *; try simp_all; try omega)
  all_goals (
    intro base' count' unread' h_eq
    injection h_eq with h1 ht1
    injection ht1 with h2 ht2
    injection ht2 with h3 _
    injection h1 with hs1
    injection h2 with hs2
    injection h3 with hs3
    cases hs1; cases hs2; cases hs3
    refine ⟨?_, by omega⟩
    congr 1; congr 1; omega
  )

end Proof.FuchsiaUsercopy.hermetic_copy_bytes_copied
