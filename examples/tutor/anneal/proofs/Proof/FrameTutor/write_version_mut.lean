import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.write_version_mut
import Specs.FrameTutor.write_version_mut
import Obligations.FrameTutor.write_version_mut

namespace Proof.FrameTutor.write_version_mut

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FrameTutor.write_version_mut

/-!
Unconditional stateful proof for `frame_tutor::write_version_mut`.

Discharges `StatefulVerificationResult` against
`Specs.FrameTutor.write_version_mut` using `dischargeStatefulEq`, and pairs the
result with a footprint-aware `Anneal.SepLogic` (`BorrowToken`) ownership
witness for the `.active` mutable borrow tag.
-/

theorem verified :
    StatefulVerificationResult
      Obligations.FrameTutor.write_version_mut.statefulClaim :=
  dischargeStatefulEq
    Obligations.FrameTutor.write_version_mut.statefulClaim
    16
    (List.cons (.ptr { allocId := 1, offsetBytes := 0 } 1)
      (List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil))
    writeVersionMem
    (fun _ _ h_pre => h_pre)
    ⟨rfl, rfl⟩

def writeVersionRawPtr : RawPtrVal where
  allocId := 2
  offset := 0
  tag := 1

def writeVersionPartialHeap : PartialHeap where
  state := writeVersionMem
  footprint := { addrs := List.nil, tags := List.cons 1 List.nil }

theorem writeVersion_borrowToken :
    BorrowToken writeVersionRawPtr .active writeVersionPartialHeap :=
  ⟨⟨writeVersionBorrow, rfl, rfl, rfl⟩, rfl⟩

end Proof.FrameTutor.write_version_mut
