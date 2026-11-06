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

theorem evalBinOp_cmp_simulation
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool)
    (kind : Miri.MIR.IntegerKind)
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes) :
    ∃ sc'' msc'',
      evalScalarBinOp .cmp sc₁ sc₂ locals mem isSigned =
        .ok (.scalar sc'') locals mem ∧
      Miri.Interpreter.IntegerOps.binary .Cmp
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
        .ok (.ordering msc'') ∧ True := by
  have hbeq0 : sc₁.sizeBytes.beq 0 = false := by
    rcases hrel₁.validBytes with h|h|h|h|h <;> { rw [h]; rfl }
  have hbeq_eq : sc₁.sizeBytes.beq sc₂.sizeBytes = true := by
    rw [hsz, Nat.beq_refl]
  have heval : ∃ sc'', evalScalarBinOp .cmp sc₁ sc₂ locals mem isSigned = .ok (.scalar sc'') locals mem := by
    unfold evalScalarBinOp
    simp only [hbeq0, hbeq_eq]
    cases isSigned
    · split <;> try split <;> exact ⟨_, rfl⟩
    · split <;> try split <;> exact ⟨_, rfl⟩
  rcases heval with ⟨sc'', heval⟩
  
  have hsz1 : msc₁.size = translateSizeBytes sc₁.sizeBytes := hrel₁.size_eq
  have hsz2 : msc₂.size = translateSizeBytes sc₂.sizeBytes := hrel₂.size_eq
  
  have hmiri : ∃ msc'', Miri.Interpreter.IntegerOps.binary .Cmp ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩ ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ = .ok (.ordering msc'') := by
    unfold Miri.Interpreter.IntegerOps.binary
    unfold Miri.Interpreter.IntegerOps.decode
    rw [← hsz1, ← hsz2]
    dsimp [Miri.MIR.IntegerType.signed]
    cases kind.signed
    · have hu1 := toUInt_rfl msc₁
      have hu2 := toUInt_rfl msc₂
      simp only [hu1, hu2, bind, Except.bind, Except.mapError]
      exact ⟨_, rfl⟩
    · rcases toInt_ok msc₁ with ⟨v1, hv1⟩
      rcases toInt_ok msc₂ with ⟨v2, hv2⟩
      simp only [hv1, hv2, bind, Except.bind, Except.mapError]
      exact ⟨_, rfl⟩
      
  rcases hmiri with ⟨msc'', hmiri⟩
  exact ⟨sc'', msc'', heval, hmiri, trivial⟩
