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

private theorem test_eval2
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (kind : Miri.MIR.IntegerKind)
    (h1 : sc₁.sizeBytes = 1) (h2 : sc₂.sizeBytes = 1)
    (hsz1 : msc₁.size = translateSizeBytes 1)
    (hsz2 : msc₂.size = translateSizeBytes 1) :
    ∃ msc'', Miri.Interpreter.IntegerOps.binary .Cmp
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
        .ok (.ordering msc'') := by
  unfold Miri.Interpreter.IntegerOps.binary
  unfold Miri.Interpreter.IntegerOps.decode
  rw [h1, h2]
  have hbits1 := toBits_rfl msc₁
  have hbits2 := toBits_rfl msc₂
  unfold Miri.Memory.ScalarInt.toUInt Miri.Memory.ScalarInt.toInt
  rw [← hsz1, ← hsz2]
  rw [hbits1, hbits2]
  rw [hsz1, hsz2]
  simp [translateSizeBytes, bind, Except.bind, Except.mapError, pure, Except.pure]
  cases kind <;> { simp; exact ⟨_, rfl⟩ }

