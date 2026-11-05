-- @anneal-def-id: frame_tutor::magic_version
import Trusted
import Anneal
import Mir.FrameTutor.magic_version
import Obligations.FrameTutor.magic_version

namespace Verify.FrameTutor.magic_version

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `frame_tutor::magic_version`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Low-priority fallback `ItemProof` instance attempting bounded
    `WP` discharge when no authored `Proof.FrameTutor.magic_version` module exists on
    disk. -/
instance (priority := low) defaultProof :
    ItemProof "frame_tutor::magic_version" Obligations.FrameTutor.magic_version.claim where
  verified := by
    first
      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeRustPinnedContractAuto
          Obligations.FrameTutor.magic_version.claim 64 64 Option.none Option.none
      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.verifyByWP Obligations.FrameTutor.magic_version.claim 64 (by
          intro _ _
          first
          | simp; try omega
          | exact True.intro)

/-- Kernel-checked verification certificate for `frame_tutor::magic_version`. -/
theorem verified : VerificationResult Obligations.FrameTutor.magic_version.claim :=
  (inferInstance : ItemProof "frame_tutor::magic_version" Obligations.FrameTutor.magic_version.claim).verified

/-- Proposition verified by `Verify.FrameTutor.magic_version.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := VerificationResult Obligations.FrameTutor.magic_version.claim

end Verify.FrameTutor.magic_version
