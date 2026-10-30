-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FxfsPlatformPager.layer_pager_read_unfixed
import Obligations.FxfsPlatformPager.layer_pager_read_unfixed
import Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
import Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

namespace Specs.FxfsPlatformPager.layer_pager_read_unfixed

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition across all 64-bit `(mapped_len, read_offset, read_len)`,
    any `ptr_non_null : bool` (`pnn = 0` or `pnn = 1`), and any
    `pager_backed : bool` (`pb = 0` or `pb = 1`, including pager-backed VMOs). -/
def pre (args : List Value) (mem : Memory) : Prop :=
  ∃ (mapped_len pnn pb read_offset read_len : Nat),
    mapped_len < 18446744073709551616 ∧
    read_offset < 18446744073709551616 ∧
    read_len < 18446744073709551616 ∧
    (pnn = 0 ∨ pnn = 1) ∧
    (pb = 0 ∨ pb = 1) ∧
    args =
      [ .scalar { bits := mapped_len, sizeBytes := 8 }
      , .scalar { bits := pnn, sizeBytes := 1 }
      , .scalar { bits := pb, sizeBytes := 1 }
      , .scalar { bits := read_offset, sizeBytes := 8 }
      , .scalar { bits := read_len, sizeBytes := 8 } ] ∧
    mem = emptyMemory

/-- Exact postcondition: returns `Some(read_offset + read_len)` when
    `pnn == 1 ∧ read_offset <= mapped_len ∧ read_len <= mapped_len - read_offset`,
    and `None` otherwise. -/
def post (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  mem' = mem ∧
  ∀ (mapped_len pnn pb read_offset read_len : Nat),
    args =
      [ .scalar { bits := mapped_len, sizeBytes := 8 }
      , .scalar { bits := pnn, sizeBytes := 1 }
      , .scalar { bits := pb, sizeBytes := 1 }
      , .scalar { bits := read_offset, sizeBytes := 8 }
      , .scalar { bits := read_len, sizeBytes := 8 } ] →
    if pnn = 1 ∧ read_offset ≤ mapped_len ∧ read_len ≤ mapped_len - read_offset then
      ret = .aggregate 1 [ .scalar { bits := read_offset + read_len, sizeBytes := 8 } ]
    else
      ret = .aggregate 0 []

instance : ModularItemSpec "fxfs_platform_pager::layer_pager_read_unfixed" where
  envAssumed :=
    Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim.callContract.holdsOn
  pre := pre
  post := post

end Specs.FxfsPlatformPager.layer_pager_read_unfixed
