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

private theorem test_eval1 (msc : Miri.Memory.ScalarInt) (hsz : msc.size = translateSizeBytes 1) :
  ∃ v, msc.toInt msc.size = .ok v := by
  unfold Miri.Memory.ScalarInt.toInt
  have hbits := toBits_rfl msc
  rw [hbits]
  rw [hsz]
  simp [translateSizeBytes]
  exact ⟨_, rfl⟩
