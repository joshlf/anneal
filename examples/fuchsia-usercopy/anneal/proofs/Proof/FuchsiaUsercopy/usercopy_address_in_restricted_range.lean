import Trusted
import Anneal
import Mir.FuchsiaUsercopy.usercopy_address_in_restricted_range
import Obligations.FuchsiaUsercopy.usercopy_address_in_restricted_range
import Specs.FuchsiaUsercopy.usercopy_address_in_restricted_range

namespace Proof.FuchsiaUsercopy.usercopy_address_in_restricted_range

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.usercopy_address_in_restricted_range.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FuchsiaUsercopy.usercopy_address_in_restricted_range.statefulClaim 30 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨addr, rs, re, h_rs_re, h_addr_lt, h_re_lt, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (dsimp at *; try simp_all; try omega)
  all_goals (
    intro addr' rs' re' h_eq
    injection h_eq with h1 ht1
    injection ht1 with h2 ht2
    injection ht2 with h3 _
    injection h1 with hs1
    injection h2 with hs2
    injection h3 with hs3
    cases hs1; cases hs2; cases hs3
    try (
      have h_cond : addr ≠ 0 ∧ rs ≤ addr ∧ addr < re := by omega
      simp [h_cond]
      omega
    )
    try (
      have h_ncond : ¬ (addr ≠ 0 ∧ rs ≤ addr ∧ addr < re) := by omega
      simp [h_ncond]
    )
  )

end Proof.FuchsiaUsercopy.usercopy_address_in_restricted_range
