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
  let res1 := evalScalarBinOp .cmp sc₁ sc₂ locals mem isSigned
  let res2 := Miri.Interpreter.IntegerOps.binary .Cmp
        ⟨msc₁, ⟨LeanMiriSpec.Correspondence.translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨LeanMiriSpec.Correspondence.translateSizeBytes sc₂.sizeBytes, kind⟩⟩
  have h1 : ∃ sc'', res1 = .ok (.scalar sc'') locals mem := by
    unfold res1 evalScalarBinOp
    cases isSigned
    · cases sc₁.beq sc₂
      · cases sc₁.ble sc₂
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · cases (wrapScalarBits sc₁.bits (scalarModulus sc₁.sizeBytes)).beq (wrapScalarBits sc₂.bits (scalarModulus sc₂.sizeBytes))
      · cases signedLt (wrapScalarBits sc₁.bits (scalarModulus sc₁.sizeBytes)) (wrapScalarBits sc₂.bits (scalarModulus sc₂.sizeBytes)) sc₁.sizeBytes
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  have h2 : ∃ msc'', res2 = .ok (.ordering msc'') := by
    unfold res2 Miri.Interpreter.IntegerOps.binary
    dsimp
    exact ⟨_, rfl⟩
  rcases h1 with ⟨sc'', h1⟩
  rcases h2 with ⟨msc'', h2⟩
  exact ⟨sc'', msc'', h1, h2, trivial⟩
