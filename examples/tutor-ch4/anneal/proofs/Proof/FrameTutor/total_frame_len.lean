import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.total_frame_len
import Obligations.FrameTutor.total_frame_len

namespace Proof.FrameTutor.total_frame_len

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
Unconditional proof for `frame_tutor::total_frame_len`.

Discharges `Obligations.FrameTutor.total_frame_len.claim` directly against the
generated `defaultSpec` using `dischargeRustEq2U8` without a `Specs` override.
-/

theorem verified : VerificationResult Obligations.FrameTutor.total_frame_len.claim :=
  dischargeRustEq2U8
    Obligations.FrameTutor.total_frame_len.claim
    16
    64
    Mir.FrameTutor.__anodized_fn_requires_total_frame_len.body
    Mir.FrameTutor.__anodized_fn_ensures_total_frame_len.body
    1
    2

end Proof.FrameTutor.total_frame_len
