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

private theorem toInt_ok (msc : Miri.Memory.ScalarInt) 
  (hsz : msc.size = translateSizeBytes 1 ∨ msc.size = translateSizeBytes 2 ∨ 
         msc.size = translateSizeBytes 4 ∨ msc.size = translateSizeBytes 8 ∨ 
         msc.size = translateSizeBytes 16) :
  ∃ v, msc.toInt msc.size = .ok v := by
  rcases hsz with h1 | h2 | h4 | h8 | h16
  · unfold Miri.Memory.ScalarInt.toInt; rw [toBits_rfl msc, h1]; simp [translateSizeBytes]; exact ⟨_, rfl⟩
  · unfold Miri.Memory.ScalarInt.toInt; rw [toBits_rfl msc, h2]; simp [translateSizeBytes]; exact ⟨_, rfl⟩
  · unfold Miri.Memory.ScalarInt.toInt; rw [toBits_rfl msc, h4]; simp [translateSizeBytes]; exact ⟨_, rfl⟩
  · unfold Miri.Memory.ScalarInt.toInt; rw [toBits_rfl msc, h8]; simp [translateSizeBytes]; exact ⟨_, rfl⟩
  · unfold Miri.Memory.ScalarInt.toInt; rw [toBits_rfl msc, h16]; simp [translateSizeBytes]; exact ⟨_, rfl⟩

private theorem decode_ok (msc : Miri.Memory.ScalarInt) (k : Miri.MIR.IntegerKind) 
  (hsz : msc.size = translateSizeBytes 1 ∨ msc.size = translateSizeBytes 2 ∨ 
         msc.size = translateSizeBytes 4 ∨ msc.size = translateSizeBytes 8 ∨ 
         msc.size = translateSizeBytes 16) :
  ∃ v, Miri.Interpreter.IntegerOps.decode ⟨msc, ⟨msc.size, k⟩⟩ = .ok v := by
  unfold Miri.Interpreter.IntegerOps.decode
  have hkind : (⟨msc.size, k⟩ : Miri.Interpreter.IntegerType).signed = k.signed := rfl
  rw [hkind]
  cases hk : k.signed <;> dsimp
  · have hu := toUInt_rfl msc
    simp [hu, bind, Except.bind, Except.mapError, pure, Except.pure]
  · rcases toInt_ok msc hsz with ⟨v, hv⟩
    simp [hv, Except.mapError]

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
    · split <;> (try split) <;> (try split) <;> exact ⟨_, rfl⟩
    · split <;> (try split) <;> (try split) <;> exact ⟨_, rfl⟩
  rcases heval with ⟨sc'', heval⟩
  
  have hsz1 : msc₁.size = translateSizeBytes sc₁.sizeBytes := hrel₁.size_eq
  have hsz2 : msc₂.size = translateSizeBytes sc₂.sizeBytes := hrel₂.size_eq
  have hv1_cond : msc₁.size = translateSizeBytes 1 ∨ msc₁.size = translateSizeBytes 2 ∨ msc₁.size = translateSizeBytes 4 ∨ msc₁.size = translateSizeBytes 8 ∨ msc₁.size = translateSizeBytes 16 := by
    rcases hrel₁.validBytes with h|h|h|h|h <;> rw [hsz1, h] <;> simp
  have hv2_cond : msc₂.size = translateSizeBytes 1 ∨ msc₂.size = translateSizeBytes 2 ∨ msc₂.size = translateSizeBytes 4 ∨ msc₂.size = translateSizeBytes 8 ∨ msc₂.size = translateSizeBytes 16 := by
    rcases hrel₂.validBytes with h|h|h|h|h <;> rw [hsz2, h] <;> simp
  
  rcases decode_ok msc₁ kind hv1_cond with ⟨v1, hd1⟩
  rcases decode_ok msc₂ kind hv2_cond with ⟨v2, hd2⟩
  
  have h_size_eq : msc₁.size = msc₂.size := by rw [hsz1, hsz2, hsz]
  have h_type_eq : ({ size := msc₁.size, kind := kind } : Miri.Interpreter.IntegerType) = ({ size := msc₂.size, kind := kind } : Miri.Interpreter.IntegerType) := by
    rw [h_size_eq]
  have h_neq : (({ size := msc₁.size, kind := kind } : Miri.Interpreter.IntegerType) != ({ size := msc₂.size, kind := kind } : Miri.Interpreter.IntegerType)) = false := by
    rw [h_type_eq, bne_self_eq_false]
  
  have hmiri : ∃ msc'', Miri.Interpreter.IntegerOps.binary .Cmp ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩ ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ = .ok (.ordering msc'') := by
    rw [← hsz1, ← hsz2]
    unfold Miri.Interpreter.IntegerOps.binary
    simp [hd1, hd2, h_neq, bind, Except.bind, pure, Except.pure]

  rcases hmiri with ⟨msc'', hmiri⟩
  exact ⟨sc'', msc'', heval, hmiri, trivial⟩
