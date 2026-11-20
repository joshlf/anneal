import Trusted
import Anneal.MirLiftCore
import Mir.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
import Obligations.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
import Specs.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref

namespace Proof.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref

open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_wpConverges _ ?_
  rintro _ _ ⟨⟨t, h_t, rfl⟩, rfl⟩
  -- `copy _1` validates the `bool` scalar, so split `t < 2` into its two
  -- concrete values before running the single-block CFG.
  obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
  all_goals exact mirWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, by rintro _ ⟨⟩; rfl⟩

end Proof.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
