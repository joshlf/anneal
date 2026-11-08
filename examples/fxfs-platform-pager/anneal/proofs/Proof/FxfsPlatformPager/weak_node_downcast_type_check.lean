import Trusted
import Anneal.MirLiftCore
import Mir.FxfsPlatformPager.weak_node_downcast_type_check
import Obligations.FxfsPlatformPager.weak_node_downcast_type_check
import Specs.FxfsPlatformPager.weak_node_downcast_type_check

namespace Proof.FxfsPlatformPager.weak_node_downcast_type_check

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec

theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.weak_node_downcast_type_check.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_wpConverges _ ?_
  rintro _ _ ⟨⟨vt, tt, pnn, -, -, h_pnn, rfl⟩, rfl⟩
  match pnn, h_pnn with
  | 0, _ => exact mirWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, by rintro _ _ _ ⟨⟩; simp⟩
  | 1, _ =>
    exact mirWpConverges_of_runCfgToBlock _ _ rfl 0 _
      ⟨rfl, by rintro _ _ _ ⟨⟩; cases h : Nat.beq vt tt <;> simp_all [boolToScalar]⟩

end Proof.FxfsPlatformPager.weak_node_downcast_type_check
