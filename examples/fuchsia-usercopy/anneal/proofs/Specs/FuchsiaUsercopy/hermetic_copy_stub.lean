-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FuchsiaUsercopy.hermetic_copy_stub
import Obligations.FuchsiaUsercopy.hermetic_copy_stub

namespace Specs.FuchsiaUsercopy.hermetic_copy_stub

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Caller-facing precondition across all 64-bit `(count, fault_offset)` with
    `fault_offset <= count` and any `normal_mode_dest_valid : bool` (`v = 0` or `v = 1`). -/
def pre (args : List Value) (mem : Memory) : Prop :=
  ∃ (count fault_offset v : Nat),
    fault_offset ≤ count ∧
    count < 18446744073709551616 ∧
    (v = 0 ∨ v = 1) ∧
    args =
      [ .scalar { bits := count, sizeBytes := 8 }
      , .scalar { bits := fault_offset, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ] ∧
    mem = emptyMemory

/-- Strict-safety subdomain where `hermetic_copy_stub` is 100% UB-free (`TreeSafe`):
    `normal_mode_dest_valid == true` (`v = 1`, i.e. the Starnix normal-mode destination
    buffer is valid and only the restricted-mode source address can page-fault). -/
def strictSafetyPre (args : List Value) (_ : Memory) : Prop :=
  ∃ (count fault_offset : Nat),
    args =
      [ .scalar { bits := count, sizeBytes := 8 }
      , .scalar { bits := fault_offset, sizeBytes := 8 }
      , .scalar { bits := 1, sizeBytes := 1 } ]

/-- Normal-return postcondition across all `pre`: returns `fault_offset <= count`
    and preserves `mem`. -/
def post (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  mem' = mem ∧
  ∀ (count fault_offset v : Nat),
    args =
      [ .scalar { bits := count, sizeBytes := 8 }
      , .scalar { bits := fault_offset, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ] →
    ret = .scalar { bits := fault_offset, sizeBytes := 8 } ∧
    fault_offset ≤ count

instance : UbExceptionItemSpec "fuchsia_usercopy::hermetic_copy_stub" where
  pre := pre
  strictSafetyPre := strictSafetyPre
  post := post

end Specs.FuchsiaUsercopy.hermetic_copy_stub
