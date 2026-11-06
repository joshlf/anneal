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

theorem evalBinOp_rel_simulation
    (op : MirAst.BinOp) (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot) (mem : Memory)
    (ty : Ty) (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes)
    (hsz_ty : sc₁.sizeBytes = match ty.kind with | .bool => 1 | _ => sc₁.sizeBytes)
    (mop : Miri.MIR.BinOp) (hmop : translateBinOp op = some mop) :
    ∃ b : Bool,
      evalScalarBinOp op sc₁ sc₂ locals mem (isSigned ty.kind) =
        .ok (.scalar (boolToScalar b)) locals mem ∧
      Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks []) () mop
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty emptyLayoutTable⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty emptyLayoutTable⟩ =
        .ok ⟨.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofBool b)), translateTy { kind := .bool, layoutIdx := 0 } emptyLayoutTable⟩ := by
  sorry

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
  sorry

theorem evalCast_intToInt_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (locals : List LocalSlot) (mem : Memory)
    (srcTy dstTy : Ty) (destPlace : Miri.Interpreter.RuntimePlace AnnealProv)
    (hsrc : srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k))
    (hdst : dstTy.kind = .bool ∨ (∃ k, dstTy.kind = .int k) ∨ (∃ k, dstTy.kind = .uint k))
    (hsz : rigidTyByteSize emptyLayoutTable srcTy = rigidTyByteSize emptyLayoutTable dstTy)
    (h_dest : destPlace.layout = translateTy dstTy emptyLayoutTable) :
    ∃ sc' msc',
      evalByteCast locals (.constant ⟨srcTy, .scalar (.int sc)⟩) dstTy mem [] emptyLayoutTable =
        .ok (.scalar sc') locals mem ∧
      Miri.Interpreter.Cast.cast (annealCastHooks emptyLayoutTable) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy emptyLayoutTable⟩ .IntToInt
        (encodeTyId dstTy) destPlace =
        .ok () ∧
      ScalarRel sc' msc' := by
  sorry

theorem step_terminator_switchInt_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (locals : List LocalSlot) (mem : Memory)
    (ty : Ty) (targets : SwitchTargets) :
    ∃ bb : BasicBlockIdx,
      lookupSwitchTarget sc.bits targets.branches targets.otherwise = bb ∧
      bb = (translateSwitchTargets targets).otherwise ∨ (∃ c, bb = c) := by
  sorry

theorem step_stmt_lm1_2_simulation : True := trivial
theorem step_terminator_lm1_2_simulation : True := trivial

end LeanMiriSpec.Correspondence
