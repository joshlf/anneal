import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FxfsTier1.unicode_lookup_plane_bounds
import Obligations.FxfsTier1.unicode_lookup_plane_bounds
import Specs.FxfsTier1.unicode_lookup_plane_bounds

namespace Proof.FxfsTier1.unicode_lookup_plane_bounds

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FxfsTier1.unicode_lookup_plane_bounds

/-- Proof that `unicode_lookup_plane_bounds` (`fxfs/unicode/src/lookup.rs:50-75`) is free of
    Undefined Behavior (`BinOp.shr`, `BinOp.subUnchecked`) and returns `Some((plane_start, len))`. -/
theorem verified :
    StatefulVerificationResult Obligations.FxfsTier1.unicode_lookup_plane_bounds.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FxfsTier1.unicode_lookup_plane_bounds.statefulClaim 28 ?_
  intro args mem h_pre
  rcases h_pre with ⟨rfl, rfl⟩
  rfl

end Proof.FxfsTier1.unicode_lookup_plane_bounds
