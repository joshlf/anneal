-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
import Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

namespace Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Caller-facing precondition across all 64-bit `mapped_len`, valid non-null
    pointer (`ptr_non_null == true`, i.e. `1`), and any `pager_backed : bool`
    (`pb = 0` or `pb = 1`). -/
def pre (args : List Value) (mem : Memory) : Prop :=
  ∃ (mapped_len pb : Nat),
    mapped_len < 18446744073709551616 ∧
    (pb = 0 ∨ pb = 1) ∧
    args =
      [ .scalar { bits := mapped_len, sizeBytes := 8 }
      , .scalar { bits := 1, sizeBytes := 1 }
      , .scalar { bits := pb, sizeBytes := 1 } ] ∧
    mem = emptyMemory

/-- Strict-safety subdomain where `mapped_vmo_as_slice_unfixed` is 100% UB-free
    (`TreeSafe`): `pager_backed == false` (`pb = 0`). -/
def strictSafetyPre (args : List Value) (_ : Memory) : Prop :=
  ∃ (mapped_len : Nat),
    args =
      [ .scalar { bits := mapped_len, sizeBytes := 8 }
      , .scalar { bits := 1, sizeBytes := 1 }
      , .scalar { bits := 0, sizeBytes := 1 } ]

/-- Normal-return postcondition across all `pre`: returns `mapped_len` and
    preserves `mem`. -/
def post (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  mem' = mem ∧
  ∀ (mapped_len pb : Nat),
    args =
      [ .scalar { bits := mapped_len, sizeBytes := 8 }
      , .scalar { bits := 1, sizeBytes := 1 }
      , .scalar { bits := pb, sizeBytes := 1 } ] →
    ret = .scalar { bits := mapped_len, sizeBytes := 8 }

instance : UbExceptionItemSpec "fxfs_platform_pager::mapped_vmo_as_slice_unfixed" where
  pre := pre
  strictSafetyPre := strictSafetyPre
  post := post

end Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
