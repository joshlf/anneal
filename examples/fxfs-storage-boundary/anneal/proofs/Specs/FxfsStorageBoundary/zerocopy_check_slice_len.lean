import Trusted
import Mir.FxfsStorageBoundary.zerocopy_check_slice_len
import Obligations.FxfsStorageBoundary.zerocopy_check_slice_len

namespace Specs.FxfsStorageBoundary.zerocopy_check_slice_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over an arbitrary demonic serialized `byte_len < 2^64`
    and non-ZST `elem_size = size_of::<T::Inner>() > 0` (`0 < elem_size < 2^64`). -/
def pre (args : List Value) : Prop :=
  ∃ (bl es : Nat),
    0 < es ∧
    bl < 18446744073709551616 ∧
    es < 18446744073709551616 ∧
    args =
      [ .scalar { bits := bl, sizeBytes := 8 }
      , .scalar { bits := es, sizeBytes := 8 } ]

/-- Exact postcondition: `ret == (byte_len - (byte_len % elem_size)) / elem_size`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (bl es : Nat),
    args =
      [ .scalar { bits := bl, sizeBytes := 8 }
      , .scalar { bits := es, sizeBytes := 8 } ] →
    ret = .scalar { bits := (bl - (bl % es)) / es, sizeBytes := 8 }

instance : ItemSpec "fxfs_storage_boundary::zerocopy_check_slice_len" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_storage_boundary::zerocopy_check_slice_len" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsStorageBoundary.zerocopy_check_slice_len
