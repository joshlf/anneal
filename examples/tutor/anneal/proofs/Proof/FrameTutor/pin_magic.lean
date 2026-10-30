import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.pin_magic
import Obligations.FrameTutor.pin_magic

namespace Proof.FrameTutor.pin_magic

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
Unconditional proof for `frame_tutor::pin_magic`.

Discharges `Obligations.FrameTutor.pin_magic.claim` directly against the
generated `defaultSpec` using `dischargeRustEqU32` without a `Specs` override.
-/

theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim :=
  dischargeRustEqU32
    Obligations.FrameTutor.pin_magic.claim
    4
    64
    Mir.FrameTutor.__anodized_fn_requires_pin_magic.body
    Mir.FrameTutor.__anodized_fn_ensures_pin_magic.body
    7

end Proof.FrameTutor.pin_magic
