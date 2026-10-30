import Trusted
import Anneal
import Mir.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
import Obligations.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
import Specs.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref

namespace Proof.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref.statefulClaim 100 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨t, h_t, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (try simp_all; try omega)

end Proof.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
