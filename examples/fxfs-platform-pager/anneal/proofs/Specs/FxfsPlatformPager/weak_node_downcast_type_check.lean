-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FxfsPlatformPager.weak_node_downcast_type_check
import Obligations.FxfsPlatformPager.weak_node_downcast_type_check

namespace Specs.FxfsPlatformPager.weak_node_downcast_type_check

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over `(vtable_type_id, target_type_id, ptr_non_null)`
    modeling `fxfs_platform::fuchsia::node::WeakNode::upgrade_and_downcast_node`. -/
def pre (args : List Value) : Prop :=
  ∃ (vt tt pnn : Nat),
    vt < 18446744073709551616 ∧
    tt < 18446744073709551616 ∧
    pnn < 2 ∧
    args =
      [ .scalar { bits := vt, sizeBytes := 8 }
      , .scalar { bits := tt, sizeBytes := 8 }
      , .scalar { bits := pnn, sizeBytes := 1 } ]

/-- Exact postcondition: returns `true` (`1`) iff `ptr_non_null` is `true` (`1`)
    and `vtable_type_id == target_type_id`, preventing unsound `Weak::from_raw` downcasts. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (vt tt pnn : Nat),
    args =
      [ .scalar { bits := vt, sizeBytes := 8 }
      , .scalar { bits := tt, sizeBytes := 8 }
      , .scalar { bits := pnn, sizeBytes := 1 } ] →
    ret = .scalar { bits := if pnn = 1 ∧ vt = tt then 1 else 0, sizeBytes := 1 }

instance : ItemSpec "fxfs_platform_pager::weak_node_downcast_type_check" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_platform_pager::weak_node_downcast_type_check" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsPlatformPager.weak_node_downcast_type_check
