import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

private theorem toBits_ok (msc : Miri.Memory.ScalarInt) (sz : Miri.ABI.Size) (hsz : sz == msc.size) :
  ∃ v, msc.toBits sz = .ok v := by
  unfold Miri.Memory.ScalarInt.toBits
  have h_eq : sz = msc.size := beq_iff_eq.mp hsz
  subst h_eq
  unfold Miri.Memory.ScalarInt.size
  simp only [bne_self_eq_false, pure, Except.pure]
  exact ⟨_, rfl⟩

private theorem toUInt_ok (msc : Miri.Memory.ScalarInt) (sz : Miri.ABI.Size) (hsz : sz == msc.size) :
  ∃ v, msc.toUInt sz = .ok v := by
  unfold Miri.Memory.ScalarInt.toUInt
  exact toBits_ok msc sz hsz

private theorem toInt_ok (msc : Miri.Memory.ScalarInt) (sz : Miri.ABI.Size) (hsz : sz == msc.size) :
  ∃ v, msc.toInt sz = .ok v := by
  unfold Miri.Memory.ScalarInt.toInt
  rcases toBits_ok msc sz hsz with ⟨bits, hbits⟩
  simp only [hbits, bind, Except.bind, Except.mapError]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

private theorem decode_ok (msc : Miri.Memory.ScalarInt) (sz : Miri.ABI.Size) (k : Miri.MIR.IntegerKind) (hsz : sz == msc.size) :
  ∃ v, Miri.Interpreter.IntegerOps.decode ⟨msc, ⟨sz, k⟩⟩ = .ok v := by
  unfold Miri.Interpreter.IntegerOps.decode
  dsimp [Miri.MIR.IntegerType.signed]
  cases k.signed <;> dsimp
  · rcases toUInt_ok msc sz hsz with ⟨v, hv⟩
    simp only [hv, bind, Except.bind, Except.mapError]
    exact ⟨_, rfl⟩
  · rcases toInt_ok msc sz hsz with ⟨v, hv⟩
    simp only [hv, bind, Except.bind, Except.mapError]
    exact ⟨_, rfl⟩

