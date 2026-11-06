import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

theorem evalBinOp_cmp_simulation
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : LeanMiriSpec.Correspondence.ScalarRel sc₁ msc₁) (hrel₂ : LeanMiriSpec.Correspondence.ScalarRel sc₂ msc₂)
    (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool)
    (kind : Miri.MIR.IntegerKind)
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes) :
    ∃ sc'' msc'',
      evalScalarBinOp .cmp sc₁ sc₂ locals mem isSigned =
        .ok (.scalar sc'') locals mem ∧
      Miri.Interpreter.IntegerOps.binary .Cmp
        ⟨msc₁, ⟨LeanMiriSpec.Correspondence.translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨LeanMiriSpec.Correspondence.translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
        .ok (.ordering msc'') ∧ True := by
  have hbeq0 : sc₁.sizeBytes.beq 0 = false := by
    rcases hrel₁.validBytes with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hbeq_eq : sc₁.sizeBytes.beq sc₂.sizeBytes = true := by
    rw [hsz, Nat.beq_refl]
  have heval : ∃ sc'', evalScalarBinOp .cmp sc₁ sc₂ locals mem isSigned = .ok (.scalar sc'') locals mem := by
    unfold evalScalarBinOp
    simp only [hbeq0, hbeq_eq, Bool.false_eq_true, ↓reduceIte]
    cases isSigned
    · split; exact ⟨_, rfl⟩; split; exact ⟨_, rfl⟩; exact ⟨_, rfl⟩
    · split; exact ⟨_, rfl⟩; split; exact ⟨_, rfl⟩; exact ⟨_, rfl⟩
  have hmiri : ∃ msc'', Miri.Interpreter.IntegerOps.binary .Cmp ⟨msc₁, ⟨LeanMiriSpec.Correspondence.translateSizeBytes sc₁.sizeBytes, kind⟩⟩ ⟨msc₂, ⟨LeanMiriSpec.Correspondence.translateSizeBytes sc₂.sizeBytes, kind⟩⟩ = .ok (.ordering msc'') := by
    unfold Miri.Interpreter.IntegerOps.binary
    dsimp
    exact ⟨_, rfl⟩
  rcases heval with ⟨sc'', heval⟩
  rcases hmiri with ⟨msc'', hmiri⟩
  exact ⟨sc'', msc'', heval, hmiri, trivial⟩
