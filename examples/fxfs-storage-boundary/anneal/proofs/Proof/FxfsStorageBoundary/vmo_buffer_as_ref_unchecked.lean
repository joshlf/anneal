import Trusted
import Anneal
import Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
import Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
import Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

namespace Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : UbExceptionVerificationResult Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim := by
  refine verifyUbExceptionMirSym
    Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim 20 ?_ ?_
  · intro args mem h_pre h_strict
    rcases h_pre with ⟨vmo_size, offset, len, t, h_off, h_len, h_vmo, _, rfl, rfl⟩
    rcases h_strict with ⟨_, _, _, h_eq⟩
    have ht_bits : t = 1 := by
      injection h_eq with _ ht1
      injection ht1 with _ ht2
      injection ht2 with _ ht3
      injection ht3 with ht_head _
      injection ht_head with ht_sc
      injection ht_sc with ht_b _
    subst ht_bits
    (repeat' ((conv => whnf); split))
    all_goals (conv => whnf)
    all_goals (dsimp at *; try simp_all; try omega)
    all_goals (
      refine ⟨rfl, ?_⟩
      intro vs' off' l' t' h_args
      injection h_args with _ ht1
      injection ht1 with h2 ht2
      injection ht2 with h3 _
      injection h2 with hs2
      injection h3 with hs3
      cases hs2; cases hs3
      congr 1; congr 1; omega
    )
  · intro args mem h_pre
    rcases h_pre with ⟨vmo_size, offset, len, t, h_off, h_len, h_vmo, h_t, rfl, rfl⟩
    rcases h_t with rfl | rfl
    · conv => whnf
      trivial
    · (repeat' ((conv => whnf); split))
      all_goals (conv => whnf)
      all_goals (dsimp at *; try simp_all; try omega)
      all_goals (
        refine ⟨rfl, ?_⟩
        intro vs' off' l' t' h_args
        injection h_args with _ ht1
        injection ht1 with h2 ht2
        injection ht2 with h3 _
        injection h2 with hs2
        injection h3 with hs3
        cases hs2; cases hs3
        congr 1; congr 1; omega
      )

end Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
