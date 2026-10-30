-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FxfsPlatformPager.pager_query_vmo_stats_assume_init
import Obligations.FxfsPlatformPager.pager_query_vmo_stats_assume_init

namespace Specs.FxfsPlatformPager.pager_query_vmo_stats_assume_init

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Precondition over `status_ok : bool` (`ok < 2`) and `raw_modified_word : u32`
    (`rw < 2`, i.e. `0` or `ZX_PAGER_VMO_STATS_MODIFIED = 1`) modeling
    `fxfs_platform::fuchsia::pager::Pager::query_vmo_stats`. -/
def pre (args : List Value) : Prop :=
  ∃ (ok rw : Nat),
    ok < 2 ∧
    rw < 2 ∧
    args =
      [ .scalar { bits := ok, sizeBytes := 1 }
      , .scalar { bits := rw, sizeBytes := 4 } ]

/-- Exact postcondition:
    - when `status_ok == false` (`ok = 0`), returns `None` (`.aggregate 0 []`) without calling `assume_init()`,
    - when `status_ok == true` (`ok = 1`), initializes `MaybeUninit<u32>` and returns `Some(rw == 1)`
      (`.aggregate 1 [ .scalar { bits := rw, sizeBytes := 1 } ]`). -/
def post (args : List Value) (ret : Value) : Prop :=
  match args with
  | [ .scalar { bits := ok, sizeBytes := 1 }
    , .scalar { bits := rw, sizeBytes := 4 } ] =>
    if ok = 0 then
      ret = .aggregate 0 []
    else
      ret = .aggregate 1 [ .scalar { bits := rw, sizeBytes := 1 } ]
  | _ => False

instance : ItemSpec "fxfs_platform_pager::pager_query_vmo_stats_assume_init" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_platform_pager::pager_query_vmo_stats_assume_init" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsPlatformPager.pager_query_vmo_stats_assume_init
