import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FxfsTier1.ptr_slice_len_and_first
import Obligations.FxfsTier1.ptr_slice_len_and_first
import Specs.FxfsTier1.ptr_slice_len_and_first

namespace Proof.FxfsTier1.ptr_slice_len_and_first

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FxfsTier1.ptr_slice_len_and_first

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsTier1.ptr_slice_len_and_first.statefulClaim :=
  dischargeStatefulEq
    Obligations.FxfsTier1.ptr_slice_len_and_first.statefulClaim
    16
    [.ptr { allocId := 1, offsetBytes := 0 } 8]
    (bufMem 10 20 30 40)
    (fun _ _ h_pre => h_pre)
    rfl

end Proof.FxfsTier1.ptr_slice_len_and_first
