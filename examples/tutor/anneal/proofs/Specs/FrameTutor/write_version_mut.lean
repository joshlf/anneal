import Trusted
import Mir.FrameTutor.write_version_mut
import Obligations.FrameTutor.write_version_mut

namespace Specs.FrameTutor.write_version_mut

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-!
Stateful specification for `frame_tutor::write_version_mut` (`#100`, `#125`).

Models an `.active` Tree Borrows `BorrowEntry` (`tag = 1`, `targetLocal = 2`,
`protector = .some 1`, `rangeOffset = 0`, `rangeLen = 1`) in `Memory.borrows`
with active function-entry protector `1` in `Memory.activeProtectors`. Under
this precondition (`.defined` of `MirStatefulContractSpec`), `*hdr = ver; *hdr`
overwrites the target byte in place with `2_u8`, preserves the `.active`
borrow entry in `mem'`, and returns `.scalar { bits := 2, sizeBytes := 1 }`
without triggering Undefined Behavior.
-/

def writeVersionBorrow : BorrowEntry where
  tag := 1
  perm := .active
  targetLocal := 2
  targetProjection := List.nil
  protector := .some 1
  rangeOffset := 0
  rangeLen := 1

def writeVersionMem : Memory :=
  { emptyMemory with
    borrows := List.cons writeVersionBorrow List.nil
    nextTag := 2
    activeProtectors := List.cons 1 List.nil
    nextProtector := 2 }

instance : StatefulItemSpec "frame_tutor::write_version_mut" where
  pre args mem :=
    And
      (args =
        List.cons (.ptr { allocId := 1, offsetBytes := 0 } 1)
          (List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil))
      (mem = writeVersionMem)
  post _ _ ret mem' :=
    And
      (ret = .scalar { bits := 2, sizeBytes := 1 })
      (mem' = writeVersionMem)

end Specs.FrameTutor.write_version_mut
