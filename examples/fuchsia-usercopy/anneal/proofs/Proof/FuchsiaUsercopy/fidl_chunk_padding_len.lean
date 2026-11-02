import Trusted
import Anneal
import Mir.FuchsiaUsercopy.fidl_chunk_padding_len
import Obligations.FuchsiaUsercopy.fidl_chunk_padding_len
import Specs.FuchsiaUsercopy.fidl_chunk_padding_len

namespace Proof.FuchsiaUsercopy.fidl_chunk_padding_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 2000000 in
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.fidl_chunk_padding_len.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FuchsiaUsercopy.fidl_chunk_padding_len.statefulClaim 30 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨es, len, h_es, h_len, rfl⟩, rfl⟩
  rcases h_es with rfl | rfl | rfl <;>
    rcases h_len with rfl | rfl | rfl | rfl
  all_goals (
    conv => whnf
    intro es' len' h_eq
    injection h_eq with h1 ht1
    injection ht1 with h2 _
    injection h1 with hs1
    injection h2 with hs2
    cases hs1; cases hs2
    refine ⟨rfl, by decide, by decide⟩
  )

end Proof.FuchsiaUsercopy.fidl_chunk_padding_len
