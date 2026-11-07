-- @anneal-def-id: frame_tutor::advance_offset
import Trusted
import Anneal
import Mir.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Verify.FrameTutor.advance_offset

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `frame_tutor::advance_offset`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Low-priority fallback `ItemProof` instance attempting bounded
    `WP` discharge when no authored `Proof.FrameTutor.advance_offset` module exists on
    disk. -/
instance (priority := low) defaultProof :
    ItemProof "frame_tutor::advance_offset" Obligations.FrameTutor.advance_offset.claim where
  verified := by
    first
      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeRustPinnedContractAuto
          Obligations.FrameTutor.advance_offset.claim 64 64 Option.none Option.none
      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.verifyByWP Obligations.FrameTutor.advance_offset.claim 64 (by
          intro _ _
          first
          | simp; try omega
          | exact True.intro)

/-- Kernel-checked verification certificate for `frame_tutor::advance_offset`. -/
theorem verified : VerificationResult Obligations.FrameTutor.advance_offset.claim :=
  (inferInstance : ItemProof "frame_tutor::advance_offset" Obligations.FrameTutor.advance_offset.claim).verified

/-- Proposition verified by `Verify.FrameTutor.advance_offset.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := VerificationResult Obligations.FrameTutor.advance_offset.claim

end Verify.FrameTutor.advance_offset
