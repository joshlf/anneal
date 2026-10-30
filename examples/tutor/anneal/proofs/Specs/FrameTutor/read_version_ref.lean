import Trusted
import Mir.FrameTutor.read_version_ref
import Obligations.FrameTutor.read_version_ref

namespace Specs.FrameTutor.read_version_ref

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-!
Stateful specification for `frame_tutor::read_version_ref` (`#100`, `#125`).

Models a 1-byte read-only allocation (`allocId = 1`, byte value `1`) in
`Memory.globals` and requires `hdr` to point to offset `0` of that allocation
so that `*hdr` evaluates to `1_u8` without undefined behavior. Because
`read_version_ref` is `unsafe fn`, this pointer-validity precondition populates
`.defined` of `MirStatefulContractSpec` via `StatefulItemSpec`.
-/

def versionAlloc : CapturedAllocation where
  allocId := 1
  bytes := List.cons (.some (UInt8.ofNat 1)) List.nil
  relocations := List.nil
  align := { bytes := 1 }
  mutability := .not

def versionMem : Memory :=
  { emptyMemory with
    globals := List.cons versionAlloc List.nil }

instance : StatefulItemSpec "frame_tutor::read_version_ref" where
  pre args mem :=
    And
      (args = List.cons (.ptr { allocId := 1, offsetBytes := 0 } 1) List.nil)
      (mem = versionMem)
  post _ _ ret _ :=
    ret = .scalar { bits := 1, sizeBytes := 1 }

end Specs.FrameTutor.read_version_ref
