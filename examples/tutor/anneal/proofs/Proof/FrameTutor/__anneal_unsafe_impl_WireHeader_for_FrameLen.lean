import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen
import Obligations.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen

namespace Proof.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.BitValidity
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
Unconditional proof for `frame_tutor::__anneal_unsafe_impl_WireHeader_for_FrameLen`.

Discharges the synthetic `#[anneal_spec::unsafe_impl(true)]` witness obligation
via `verifyByWP`, and proves the companion `Anneal.BitValidity` layout theorems
(`IsUnaligned`, `IsFromBytes`, `IsIntoBytes`, `IsFromZeros`) for `FrameLen(u8)`.
-/

theorem verified :
    VerificationResult
      Obligations.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen.claim :=
  verifyByWP
    Obligations.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen.claim
    8
    (fun _ _ => True.intro)

@[reducible]
def frameLenLayoutTable : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries :=
    {
      size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 })
      fields := .arbitrary ({ bytes := 0 } :: .nil) (0 :: .nil)
      variants := .single 0
      isUninhabited := false
    } ::
    .nil
}

@[reducible]
def frameLenTy : Ty := {
  kind := .adt "frame_tutor::FrameLen" (.uint .u8 :: .nil)
  layoutIdx := 0
}

theorem frameLen_isUnaligned :
    IsUnaligned frameLenLayoutTable frameLenTy :=
  checkUnaligned_sound frameLenLayoutTable frameLenTy rfl

theorem frameLen_isFromBytes :
    IsFromBytes frameLenLayoutTable frameLenTy :=
  checkFromBytes_sound frameLenLayoutTable frameLenTy rfl

theorem frameLen_isIntoBytes :
    IsIntoBytes frameLenLayoutTable frameLenTy :=
  checkIntoBytes_sound frameLenLayoutTable frameLenTy rfl

theorem frameLen_isFromZeros :
    IsFromZeros frameLenLayoutTable frameLenTy :=
  checkFromZeros_sound frameLenLayoutTable frameLenTy rfl

end Proof.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen
