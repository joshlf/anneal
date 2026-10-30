import Trusted
import Mir.FxfsTier1.ptr_slice_copy4
import Obligations.FxfsTier1.ptr_slice_copy4

namespace Specs.FxfsTier1.ptr_slice_copy4

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

def srcBorrow : BorrowEntry where
  tag := 1
  targetLocal := 12
  targetProjection := List.nil
  perm := .frozen

def dstBorrow : BorrowEntry where
  tag := 2
  targetLocal := 13
  targetProjection := List.nil
  perm := .active

def copyMem (b0 b1 b2 b3 d0 d1 d2 d3 : Nat) : Memory :=
  { emptyMemory with
    borrows := [srcBorrow, dstBorrow]
    nextTag := 3
    callerLocals :=
      List.replicate 12 LocalSlot.uninit ++
      [ LocalSlot.init
          (.aggregate 0
            [ .scalar ⟨b0, 1⟩
            , .scalar ⟨b1, 1⟩
            , .scalar ⟨b2, 1⟩
            , .scalar ⟨b3, 1⟩ ])
      , LocalSlot.init
          (.aggregate 0
            [ .scalar ⟨d0, 1⟩
            , .scalar ⟨d1, 1⟩
            , .scalar ⟨d2, 1⟩
            , .scalar ⟨d3, 1⟩ ]) ] }

instance : StatefulItemSpec "fxfs_tier1::ptr_slice_copy4" where
  pre args mem :=
    args =
      [ .ptr { allocId := 1, offsetBytes := 0 } 8
      , .ptr { allocId := 2, offsetBytes := 0 } 8 ] ∧
    mem = copyMem 10 20 30 40 0 0 0 0
  post _ _ ret mem' :=
    ret = .scalar { bits := 4, sizeBytes := 8 } ∧
    get? mem'.callerLocals 13 =
      .some
        (LocalSlot.init
          (.aggregate 0
            [ .scalar ⟨10, 1⟩
            , .scalar ⟨20, 1⟩
            , .scalar ⟨30, 1⟩
            , .scalar ⟨40, 1⟩ ]))

end Specs.FxfsTier1.ptr_slice_copy4
