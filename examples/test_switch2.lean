import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

theorem step_terminator_switchInt_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : LeanMiriSpec.Correspondence.ScalarRel sc msc) (locals : List LocalSlot) (mem : Memory)
    (ty : Ty) (targets : SwitchTargets) :
    ∃ bb : BasicBlockIdx,
      lookupSwitchTarget sc.bits targets.branches targets.otherwise = bb ∧
      (bb = (LeanMiriSpec.Correspondence.translateSwitchTargets targets).otherwise ∨ (∃ c, bb = c)) := by
  refine ⟨lookupSwitchTarget sc.bits targets.branches targets.otherwise, rfl, ?_⟩
  right
  exact ⟨_, rfl⟩
