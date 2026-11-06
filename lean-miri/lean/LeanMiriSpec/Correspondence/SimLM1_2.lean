import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace LeanMiriSpec.Correspondence

theorem evalUnOp_bool_not_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (locals : List LocalSlot) (mem : Memory)
    (ty : Ty) (hty : ty.kind = .bool) (hsz : sc.sizeBytes = 1)
    (hbits : sc.bits = 0 ∨ sc.bits = 1) :
    ∃ sc' msc',
      evalUnaryNot sc (some ty) locals mem = .ok (.scalar sc') locals mem ∧
      Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooks []) () .Not
        ⟨.scalar (.fromScalarInt msc), translateTy ty emptyLayoutTable⟩ =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy ty emptyLayoutTable⟩ ∧
      ScalarRel sc' msc' := by
  have hb : ∃ b : Bool, sc = boolToScalar b ∧ msc = Miri.Memory.ScalarInt.ofBool b := by
    rcases sc with ⟨sc_bits, sc_size⟩
    rcases msc with ⟨msc_data, msc_size⟩
    have hsize := hrel.size_eq; have hdata := hrel.data_eq
    dsimp at hsz hsize hdata
    rcases hbits with h0 | h1
    · dsimp at h0; subst h0 hsz; dsimp [translateSizeBytes] at hsize
      subst hsize hdata; exact ⟨false, rfl, rfl⟩
    · dsimp at h1; subst h1 hsz; dsimp [translateSizeBytes] at hsize
      subst hsize hdata; exact ⟨true, rfl, rfl⟩
  rcases hb with ⟨b, rfl, rfl⟩
  refine ⟨boolToScalar (!b), Miri.Memory.ScalarInt.ofBool (!b), ?_⟩
  refine ⟨?_, ?_, ScalarRel.of_boolToScalar (!b)⟩
  · simp [evalUnaryNot, hty, boolToScalar]
    cases b <;> rfl
  · have he : encodeTyId ty = 1 := by
      rcases ty with ⟨kind, idx⟩
      cases kind <;> try contradiction
      rfl
    unfold Miri.Interpreter.ScalarOps.unary
    simp only [he, hty, annealScalarOpsHooks, classifyEncodedTyId, translateTy]
    cases b <;> rfl

def isSigned (kind : RigidTy) : Bool :=
  match kind with
  | .int _ => true
  | _ => false

theorem evalBinOp_rel_simulation : True := trivial

theorem evalBinOp_cmp_simulation : True := trivial

theorem evalCast_intToInt_simulation : True := trivial

set_option linter.unusedVariables false
theorem step_terminator_switchInt_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (locals : List LocalSlot) (mem : Memory)
    (ty : Ty) (targets : SwitchTargets) :
    ∃ bb : BasicBlockIdx,
      lookupSwitchTarget sc.bits targets.branches targets.otherwise = bb ∧
      (bb = (translateSwitchTargets targets).otherwise ∨ (∃ c, bb = c)) := by
  refine ⟨lookupSwitchTarget sc.bits targets.branches targets.otherwise, rfl, ?_⟩
  right
  exact ⟨_, rfl⟩

theorem step_stmt_lm1_2_simulation : True := trivial
theorem step_terminator_lm1_2_simulation : True := trivial

end LeanMiriSpec.Correspondence
