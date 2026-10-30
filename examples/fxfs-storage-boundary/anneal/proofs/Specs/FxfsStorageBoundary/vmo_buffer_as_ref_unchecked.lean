-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
import Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

namespace Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Caller-facing precondition across all 64-bit `(vmo_size, offset, len)` with
    `offset <= vmo_size` and `len <= vmo_size - offset` and any `trusted : bool`
    (`t = 0` or `t = 1`). -/
def pre (args : List Value) (mem : Memory) : Prop :=
  ∃ (vmo_size offset len t : Nat),
    offset ≤ vmo_size ∧
    len ≤ vmo_size - offset ∧
    vmo_size < 18446744073709551616 ∧
    (t = 0 ∨ t = 1) ∧
    args =
      [ .scalar { bits := vmo_size, sizeBytes := 8 }
      , .scalar { bits := offset, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := t, sizeBytes := 1 } ] ∧
    mem = emptyMemory

/-- Strict-safety subdomain where `vmo_buffer_as_ref_unchecked` is 100% UB-free
    (`TreeSafe`): `trusted == true` (`t = 1`). -/
def strictSafetyPre (args : List Value) (_ : Memory) : Prop :=
  ∃ (vmo_size offset len : Nat),
    args =
      [ .scalar { bits := vmo_size, sizeBytes := 8 }
      , .scalar { bits := offset, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := 1, sizeBytes := 1 } ]

/-- Normal-return postcondition across all `pre`: returns `offset + len` and
    preserves `mem`. -/
def post (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  mem' = mem ∧
  ∀ (vmo_size offset len t : Nat),
    args =
      [ .scalar { bits := vmo_size, sizeBytes := 8 }
      , .scalar { bits := offset, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := t, sizeBytes := 1 } ] →
    ret = .scalar { bits := offset + len, sizeBytes := 8 }

instance : UbExceptionItemSpec "fxfs_storage_boundary::vmo_buffer_as_ref_unchecked" where
  pre := pre
  strictSafetyPre := strictSafetyPre
  post := post

end Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
