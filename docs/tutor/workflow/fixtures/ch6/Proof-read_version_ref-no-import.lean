import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.read_version_ref
import Obligations.FrameTutor.read_version_ref

namespace Proof.FrameTutor.read_version_ref

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
The committed proof with `import Specs.FrameTutor.read_version_ref` removed, so
`Obligations.FrameTutor.read_version_ref.statefulClaim` would fall back to the
low-priority `defaultStatefulSpec`. `cargo anneal agent-verify` rejects the
missing import before running Lake.
-/

theorem verified :
    StatefulVerificationResult
      Obligations.FrameTutor.read_version_ref.statefulClaim :=
  dischargeStatefulEq
    Obligations.FrameTutor.read_version_ref.statefulClaim
    16
    (List.cons (.ptr { allocId := 1, offsetBytes := 0 } 1) List.nil)
    emptyMemory
    (fun _ _ h_pre => h_pre)
    rfl

end Proof.FrameTutor.read_version_ref
