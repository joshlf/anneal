import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Simulation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace LeanMiriSpec.Correspondence

private theorem decode_of_scalarRel {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (kind : Miri.MIR.IntegerKind) :
    Miri.Interpreter.IntegerOps.decode ⟨msc, ⟨translateSizeBytes sc.sizeBytes, kind⟩⟩ =
      .ok (decodeBitsInt kind.signed sc.sizeBytes sc.bits) := by
  unfold Miri.Interpreter.IntegerOps.decode
  unfold Miri.Memory.ScalarInt.toUInt Miri.Memory.ScalarInt.toBits Miri.Memory.ScalarInt.toInt
  have h1 : msc.size == translateSizeBytes sc.sizeBytes := by
    rw [hrel.size_eq]; exact BEq.rfl
  simp only [h1, ↓reduceIte, Except.mapError]
  have h2 : msc.data = BitVec.ofNat 128 sc.bits := hrel.data_eq
  rw [h2]
  have h3 : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
    apply bitVec_ofNat_toNat_of_valid hrel.validBytes hrel.canonical
  rw [h3]
  cases kind.signed
  · rfl
  · dsimp
    sorry

end LeanMiriSpec.Correspondence
