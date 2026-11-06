import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

theorem evalByteCast_ok
    {sc : MirAst.ScalarInt} (locals : List LocalSlot) (mem : Memory)
    (srcTy dstTy : Ty) 
    (hsz : rigidTyByteSize emptyLayoutTable srcTy = rigidTyByteSize emptyLayoutTable dstTy) :
    evalByteCast locals (.constant ⟨srcTy, .scalar (.int sc)⟩) dstTy mem [] emptyLayoutTable =
        .ok (.scalar sc) locals mem := by
  unfold evalByteCast
  simp only [hsz]
  -- actually wait, does evalByteCast change the bits based on bool? 
  sorry
