import Trusted
import Anneal
import Mir.FuchsiaUsercopy.fidl_pointer_is_encoded_present
import Obligations.FuchsiaUsercopy.fidl_pointer_is_encoded_present
import Specs.FuchsiaUsercopy.fidl_pointer_is_encoded_present

namespace Proof.FuchsiaUsercopy.fidl_pointer_is_encoded_present

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.fidl_pointer_is_encoded_present.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FuchsiaUsercopy.fidl_pointer_is_encoded_present.statefulClaim 30 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨enc, h_enc, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (dsimp at *; try simp_all; try omega)
  all_goals (
    intro enc' h_eq
    injection h_eq with h1 _
    injection h1 with hs1
    cases hs1
    try (have he0 : enc = 0 := by omega; simp [he0])
    try (have hem : enc = 18446744073709551615 := by omega; simp [hem])
    try (have hen : enc ≠ 0 ∧ enc ≠ 18446744073709551615 := by omega; simp [hen.1, hen.2])
  )

end Proof.FuchsiaUsercopy.fidl_pointer_is_encoded_present
