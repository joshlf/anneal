import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

theorem test_subst {sc₁ : MirAst.ScalarInt} (hrel₁ : LeanMiriSpec.Correspondence.ScalarRel sc₁ msc₁) : sc₁.sizeBytes.beq 0 = false := by
  rcases hrel₁.validBytes with h|h|h|h|h <;> { rw [h]; rfl }
