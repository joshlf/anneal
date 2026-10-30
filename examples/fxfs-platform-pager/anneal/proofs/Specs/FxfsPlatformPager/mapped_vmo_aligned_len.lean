-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FxfsPlatformPager.mapped_vmo_aligned_len
import Obligations.FxfsPlatformPager.mapped_vmo_aligned_len

namespace Specs.FxfsPlatformPager.mapped_vmo_aligned_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Precondition over representative `(len, page_size)` inputs covering all three branches
    (`page_size == 0`, `len % page_size == 0`, and `len % page_size != 0`)
    of `fxfs_platform::fuchsia::layer_pager::MappedVmo::new`. -/
def pre (args : List Value) : Prop :=
  ∃ (len ps : Nat),
    (len = 0 ∨ len = 1 ∨ len = 2) ∧
    (ps = 0 ∨ ps = 2) ∧
    args =
      [ .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := ps, sizeBytes := 8 } ]

/-- Exact postcondition for `mapped_vmo_aligned_len`:
    - returns `None` (`.aggregate 0 []`) when `ps == 0`,
    - returns `Some(len)` (`.aggregate 1 [...]`) when `ps > 0` and `len % ps == 0`,
    - returns `Some(len + (ps - len % ps))` when `ps > 0` and `len % ps != 0`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (len ps : Nat),
    args =
      [ .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := ps, sizeBytes := 8 } ] →
    if ps = 0 then
      ret = .aggregate 0 []
    else if len % ps = 0 then
      ret = .aggregate 1 [ .scalar { bits := len, sizeBytes := 8 } ]
    else
      ret = .aggregate 1 [ .scalar { bits := len + (ps - len % ps), sizeBytes := 8 } ]

instance : ItemSpec "fxfs_platform_pager::mapped_vmo_aligned_len" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_platform_pager::mapped_vmo_aligned_len" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsPlatformPager.mapped_vmo_aligned_len
