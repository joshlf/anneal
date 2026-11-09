import re

file_path = "lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean"
with open(file_path, 'r') as f:
    content = f.read()

start = "theorem step_intrinsic_copyNonOverlapping_uninit_src_divergence"
end = "theorem step_intrinsic_copyNonOverlapping_perm_divergence"

idx1 = content.find(start)
idx2 = content.find(end)

old_body = content[idx1:idx2]

new_sig = """theorem step_intrinsic_copyNonOverlapping_uninit_src_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
    {srcPtr dstPtr : ProvenancePtr} {countSc : MirAst.ScalarInt}
    {e_s e_d : AllocMapEntry} {decl_s decl_d : LocalDecl} {srcBytes dstBytes : Nat}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hsrcDecl : get? body.localDecls srcIdx = some srcDecl)
    (hsrcTy : srcDecl.ty.kind = .rawPtr srcMut pointeeTy.kind)
    (hsrcImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf srcIdx)
    (hdstDecl : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut pointeeTy.kind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    (hpt : CopyPointee body.layouts pointeeTy.kind ptId elemBytes elemAlign)
    (hsrc_val : get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)))
    (hdst_val : get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)))
    (hoff0_s : srcPtr.offsetBytes = 0)
    (hoff0_d : dstPtr.offsetBytes = 0)
    (hcnt_pre : WriteBytesScalarPreVal s.frame.locals countOp countSc)
    (hcount_pos : 0 < countSc.bits * elemBytes)
    (hcount_max : countSc.bits * elemBytes ≤ isizeMaxBytes)
    (he_s : e_s ∈ allocMap) (het_s : e_s.tag = srcPtr.tag)
    (he_d : e_d ∈ allocMap) (het_d : e_d.tag = dstPtr.tag)
    (hdecl_s : get? body.localDecls e_s.localIdx = some decl_s)
    (hdecl_d : get? body.localDecls e_d.localIdx = some decl_d)
    (hcompat : CopyTargetCompatible decl_s decl_d pointeeTy.kind)
    (hsrcBytes : rigidTyByteSize body.layouts decl_s.ty = some srcBytes)
    (hdstBytes : rigidTyByteSize body.layouts decl_d.ty = some dstBytes)
    (hsrc_in_bounds : srcPtr.offsetBytes + countSc.bits * elemBytes ≤ srcBytes)
    (hdst_in_bounds : dstPtr.offsetBytes + countSc.bits * elemBytes ≤ dstBytes)
    (huninit_s : get? s.frame.locals e_s.localIdx = some .uninit)
    (hdst_live : get? s.frame.locals e_d.localIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  have hsrc_live : get? s.frame.locals e_s.localIdx ≠ some .dead := by
    rw [huninit_s]; nofun
  by_cases hcnt1 : countSc.bits = 1
  · have hsrc_tgt : ∀ decl_s', get? body.localDecls e_s.localIdx = some decl_s' → decl_s'.ty.kind = pointeeTy.kind := sorry
    have hdst_tgt : ∀ decl_d', get? body.localDecls e_d.localIdx = some decl_d' → decl_d'.ty.kind = pointeeTy.kind := sorry
    obtain ⟨⟨stepBody, hbody, ha_eq⟩, hm_ok⟩ := copyDivergence_core hstate hphase hbb hstmt
      hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
      hsrc_val hdst_val hoff0_s hoff0_d hcnt_pre hcnt1 he_s het_s he_d het_d
      hsrc_tgt hdst_tgt hsrc_live hdst_live (Or.inl huninit_s)
    refine ⟨?_, hm_ok⟩
    have hbody_ub : stepBody = MirStepNode.fail .ub := by
      rcases hbody with rfl | ⟨srcBytes', dstBytes', rfl⟩
      · exact evalCopySingleDirect_uninit_src_ub huninit_s
      · exact evalCopyRootIntScalars_uninit_src_ub huninit_s
    rw [ha_eq, hbody_ub]
    cases e_s.perm <;> cases e_d.perm <;> rfl
  · -- Manual proof for countSc.bits > 1
    sorry

"""

content = content.replace(old_body, new_sig)
with open(file_path, 'w') as f:
    f.write(content)
