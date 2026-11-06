import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

private theorem toBits_rfl (msc : Miri.Memory.ScalarInt) : msc.toBits msc.size = .ok msc.data := by
  unfold Miri.Memory.ScalarInt.toBits Miri.Memory.ScalarInt.size Miri.Memory.ScalarInt.data
  simp [bne_self_eq_false, pure, Except.pure]

private theorem toUInt_rfl (msc : Miri.Memory.ScalarInt) : msc.toUInt msc.size = .ok msc.data := by
  unfold Miri.Memory.ScalarInt.toUInt
  exact toBits_rfl msc

private theorem toInt_ok (msc : Miri.Memory.ScalarInt) :
  ∃ v, msc.toInt msc.size = .ok v := by
  unfold Miri.Memory.ScalarInt.toInt
  have hbits := toBits_rfl msc
  simp only [hbits, bind, Except.bind, Except.mapError]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

private theorem decode_ok (msc : Miri.Memory.ScalarInt) (k : Miri.MIR.IntegerKind) :
  ∃ v, Miri.Interpreter.IntegerOps.decode ⟨msc, ⟨msc.size, k⟩⟩ = .ok v := by
  unfold Miri.Interpreter.IntegerOps.decode
  cases k <;> dsimp
  · have hu := toUInt_rfl msc
    simp [hu, bind, Except.bind, Except.mapError, pure, Except.pure]
    exact ⟨_, rfl⟩
  · rcases toInt_ok msc with ⟨v, hv⟩
    simp [hv, bind, Except.bind, Except.mapError, pure, Except.pure]
    exact ⟨_, rfl⟩

