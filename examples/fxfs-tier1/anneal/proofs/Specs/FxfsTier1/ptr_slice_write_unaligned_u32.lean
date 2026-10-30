import Trusted
import Mir.FxfsTier1.ptr_slice_write_unaligned_u32
import Obligations.FxfsTier1.ptr_slice_write_unaligned_u32

namespace Specs.FxfsTier1.ptr_slice_write_unaligned_u32

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

def dstBorrow : BorrowEntry where
  tag := 1
  targetLocal := 12
  targetProjection := List.nil
  perm := .active

def dstMem (d0 d1 d2 d3 : Nat) : Memory :=
  { emptyMemory with
    borrows := [dstBorrow]
    nextTag := 2
    callerLocals :=
      List.replicate 12 LocalSlot.uninit ++
      [ LocalSlot.init
          (.aggregate 0
            [ .scalar ⟨d0, 1⟩
            , .scalar ⟨d1, 1⟩
            , .scalar ⟨d2, 1⟩
            , .scalar ⟨d3, 1⟩ ]) ] }

instance : StatefulItemSpec "fxfs_tier1::ptr_slice_write_unaligned_u32" where
  pre args mem :=
    args =
      [ .ptr { allocId := 1, offsetBytes := 0 } 8
      , .scalar ⟨4, 8⟩
      , .scalar ⟨0x04030201, 4⟩ ] ∧
    mem = dstMem 0 0 0 0
  post _ _ ret mem' :=
    ret = .scalar { bits := 1, sizeBytes := 1 } ∧
    get? mem'.callerLocals 12 =
      .some
        (LocalSlot.init
          (.aggregate 0
            [ .scalar ⟨1, 1⟩
            , .scalar ⟨2, 1⟩
            , .scalar ⟨3, 1⟩
            , .scalar ⟨4, 1⟩ ]))

end Specs.FxfsTier1.ptr_slice_write_unaligned_u32
