import Trusted
import Mir.FxfsTier1.ptr_slice_read_unaligned_u32
import Obligations.FxfsTier1.ptr_slice_read_unaligned_u32

namespace Specs.FxfsTier1.ptr_slice_read_unaligned_u32

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

def bufBorrow : BorrowEntry where
  tag := 1
  targetLocal := 12
  targetProjection := List.nil
  perm := .frozen

def bufMem (b0 b1 b2 b3 : Nat) : Memory :=
  { emptyMemory with
    borrows := [bufBorrow]
    nextTag := 2
    callerLocals :=
      List.replicate 12 LocalSlot.uninit ++
      [LocalSlot.init
        (.aggregate 0
          [ .scalar ⟨b0, 1⟩
          , .scalar ⟨b1, 1⟩
          , .scalar ⟨b2, 1⟩
          , .scalar ⟨b3, 1⟩ ])] }

instance : StatefulItemSpec "fxfs_tier1::ptr_slice_read_unaligned_u32" where
  pre args mem :=
    args = [.ptr { allocId := 1, offsetBytes := 0 } 8] ∧
    mem = bufMem 1 2 3 4
  post _ _ ret _ :=
    ret = .scalar { bits := 67305985, sizeBytes := 4 }

end Specs.FxfsTier1.ptr_slice_read_unaligned_u32
