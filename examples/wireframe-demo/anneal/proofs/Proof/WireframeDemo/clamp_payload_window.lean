import Trusted
import Anneal
import Mir.WireframeDemo.clamp_payload_window
import Obligations.WireframeDemo.clamp_payload_window

namespace Proof.WireframeDemo.clamp_payload_window

set_option linter.all false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval


open Anneal.PureMirExec

private theorem wpReq_inversion (v1 v2 : Value) :
    MirBoolPredicateHolds Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body [v1, v2] →
    ∃ b1 b2 : Nat,
      v1 = .scalar { bits := b1, sizeBytes := 2 } ∧
      v2 = .scalar { bits := b2, sizeBytes := 2 } ∧
      b1 ≤ 65535 ∧ b2 ≤ 1024 := by
  mir_lift_spec
  rintro ⟨h1, h2, h3, h4⟩; exact ⟨_, _, h1, h2, h3, h4⟩


