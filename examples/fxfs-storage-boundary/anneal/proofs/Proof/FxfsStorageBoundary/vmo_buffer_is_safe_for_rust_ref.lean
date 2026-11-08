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
  rintro _ _ ⟨⟨_, -, rfl⟩, rfl⟩
  exact mirWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, by rintro _ ⟨⟩; rfl⟩

end Proof.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
