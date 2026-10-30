import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.advance_offset
import Specs.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Proof.FrameTutor.advance_offset

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FrameTutor.advance_offset

/-!
Unconditional safe-function proof for `frame_tutor::advance_offset` (`#100`,
`#125`).

Imports `Specs.FrameTutor.advance_offset` so
`Obligations.FrameTutor.advance_offset.claim` synthesizes the `refineSafeSpec`
instance, then discharges `VerificationResult` across both cases of
`advanceOffsetSafetyDomain` via `verifyByWPSafe`:
- At `offset = 2` (`Or.inl h2`), `wpMirSym 16` reduces to normal return
  `.scalar ⟨6, 1⟩` and `mirBoolPredicateHolds_of_wp_bounded` establishes
  `rustEnsures` alongside `ret = .scalar ⟨6, 1⟩`.
- At `offset = 255` (`Or.inr h255`), `255 + 4` overflows `u8` and
  `wpMirSym 16` with `mirSafePost` reduces `.panic` (`TerminationKind.panic`)
  to `True`, satisfied via `True.intro` because unwinding/panicking is defined
  behavior rather than Undefined Behavior.

Finally, `advance_offset_holds_with_safety` unpacks `verified.proof` via
`mirContractHoldsWithSafety_iff_mirContractHolds_imp` into an explicit
`MirContractHoldsWithSafety` refinement between `MirExecPartial` and
`MirContractSpec`.
-/

theorem verified : VerificationResult Obligations.FrameTutor.advance_offset.claim :=
  verifyByWPSafe
    Obligations.FrameTutor.advance_offset.claim
    16
    (by
      intro args h_safe
      cases h_safe with
      | inl h2 =>
        subst h2
        exact fun _ =>
          And.intro
            (mirBoolPredicateHolds_of_wp_bounded
              128
              Mir.FrameTutor.__anodized_fn_ensures_advance_offset.body
              (List.cons (.scalar { bits := 2, sizeBytes := 1 })
                (List.cons (.scalar { bits := 6, sizeBytes := 1 }) List.nil))
              rfl)
            rfl
      | inr h255 =>
        subst h255
        exact True.intro)

/-- Direct `MirContractHoldsWithSafety` corollary for `frame_tutor::advance_offset`:
    `MirExecPartial Mir.FrameTutor.advance_offset.body` refines `MirContractSpec`
    with `safetyPre := advanceOffsetSafetyDomain` (`.defined`) and the functional
    `rustRequires` / `rustEnsures` contract inside `.val` (`#125`). -/
theorem advance_offset_holds_with_safety :
    MirContractHoldsWithSafety
      Mir.FrameTutor.advance_offset.body
      advanceOffsetSafetyDomain
      (fun args =>
        And
          (Obligations.FrameTutor.advance_offset.rustRequires args)
          (args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil))
      (fun args ret =>
        And
          (Obligations.FrameTutor.advance_offset.rustEnsures args ret)
          (ret = .scalar { bits := 6, sizeBytes := 1 })) :=
  (mirContractHoldsWithSafety_iff_mirContractHolds_imp
    Mir.FrameTutor.advance_offset.body
    advanceOffsetSafetyDomain
    (fun args =>
      And
        (Obligations.FrameTutor.advance_offset.rustRequires args)
        (args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil))
    (fun args ret =>
      And
        (Obligations.FrameTutor.advance_offset.rustEnsures args ret)
        (ret = .scalar { bits := 6, sizeBytes := 1 }))).2
    verified.proof

end Proof.FrameTutor.advance_offset
