import Trusted
import Anneal
import Mir.FuchsiaUsercopy.hermetic_copy_stub
import Obligations.FuchsiaUsercopy.hermetic_copy_stub
import Specs.FuchsiaUsercopy.hermetic_copy_stub

namespace Proof.FuchsiaUsercopy.hermetic_copy_stub

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : UbExceptionVerificationResult Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim := by
  refine verifyUbExceptionMirSym
    Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim 20 ?_ ?_
  · intro args mem h_pre h_strict
    rcases h_pre with ⟨count, fo, v, h_fo, h_c, _, rfl, rfl⟩
    rcases h_strict with ⟨_, _, h_eq⟩
    have hv_bits : v = 1 := by
      injection h_eq with _ ht1
      injection ht1 with _ ht2
      injection ht2 with hv_head _
      injection hv_head with hv_sc
      injection hv_sc with hv_b _
    subst hv_bits
    (repeat' ((conv => whnf); split))
    all_goals (conv => whnf)
    all_goals (dsimp at *; try simp_all; try omega)
    all_goals (
      refine ⟨rfl, ?_⟩
      intro c' fo' v' h_args
      injection h_args with h1 ht1
      injection ht1 with h2 _
      injection h1 with hs1
      injection h2 with hs2
      cases hs1; cases hs2
      exact ⟨rfl, h_fo⟩
    )
  · intro args mem h_pre
    rcases h_pre with ⟨count, fo, v, h_fo, h_c, h_v, rfl, rfl⟩
    rcases h_v with rfl | rfl
    · conv => whnf
      trivial
    · (repeat' ((conv => whnf); split))
      all_goals (conv => whnf)
      all_goals (dsimp at *; try simp_all; try omega)
      all_goals (
        refine ⟨rfl, ?_⟩
        intro c' fo' v' h_args
        injection h_args with h1 ht1
        injection ht1 with h2 _
        injection h1 with hs1
        injection h2 with hs2
        cases hs1; cases hs2
        exact ⟨rfl, h_fo⟩
      )

end Proof.FuchsiaUsercopy.hermetic_copy_stub
