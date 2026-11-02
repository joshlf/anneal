import Trusted
import Anneal
import Mir.FuchsiaUsercopy.atomic_load_u32_unpack
import Obligations.FuchsiaUsercopy.atomic_load_u32_unpack
import Specs.FuchsiaUsercopy.atomic_load_u32_unpack

namespace Proof.FuchsiaUsercopy.atomic_load_u32_unpack

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.atomic_load_u32_unpack.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FuchsiaUsercopy.atomic_load_u32_unpack.statefulClaim 20 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨v, h_v_lt, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (dsimp at *; try simp_all; try omega)
  all_goals (
    intro v' h_eq
    injection h_eq with h1 _
    injection h1 with hs1
    cases hs1
    try (
      have h_z : v / 4294967296 = 0 := by omega
      have h_mod : v % 4294967296 = v := by omega
      simp [h_z, h_mod]
    )
    try (
      have h_nz : ¬ (v / 4294967296 = 0) := by omega
      simp [h_nz]
    )
  )

end Proof.FuchsiaUsercopy.atomic_load_u32_unpack
