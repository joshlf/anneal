import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

theorem evalCast_intToInt_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : LeanMiriSpec.Correspondence.ScalarRel sc msc) (locals : List LocalSlot) (mem : Memory)
    (srcTy dstTy : Ty) (destPlace : Miri.Interpreter.RuntimePlace LeanMiriSpec.Correspondence.AnnealProv)
    (hsrc : srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k))
    (hdst : dstTy.kind = .bool ∨ (∃ k, dstTy.kind = .int k) ∨ (∃ k, dstTy.kind = .uint k))
    (hsz : rigidTyByteSize emptyLayoutTable srcTy = rigidTyByteSize emptyLayoutTable dstTy)
    (h_dest : destPlace.layout = LeanMiriSpec.Correspondence.translateTy dstTy emptyLayoutTable) :
    ∃ sc' msc',
      evalByteCast locals (.constant ⟨srcTy, .scalar (.int sc)⟩) dstTy mem [] emptyLayoutTable =
        .ok (.scalar sc') locals mem ∧
      Miri.Interpreter.Cast.cast (LeanMiriSpec.Correspondence.annealCastHooks emptyLayoutTable) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), LeanMiriSpec.Correspondence.translateTy srcTy emptyLayoutTable⟩ .IntToInt
        (LeanMiriSpec.Correspondence.encodeTyId dstTy) destPlace =
        .ok () ∧
      LeanMiriSpec.Correspondence.ScalarRel sc' msc' := by
  refine ⟨sc, msc, ?_, ?_, hrel⟩
  · unfold evalByteCast
    dsimp
    sorry
  · sorry
