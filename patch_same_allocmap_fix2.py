import re

file_path = "lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean"
with open(file_path, 'r') as f:
    content = f.read()

start = "theorem step_intrinsic_copyNonOverlapping_simulation_same_allocMap"
end = "theorem step_intrinsic_copyNonOverlapping_simulation\n"
idx1 = content.find(start)
idx2 = content.find(end)

old_body = content[idx1:idx2]

new_body = """theorem step_intrinsic_copyNonOverlapping_simulation_same_allocMap
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
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
    (htgt_compat : ∀ srcPtr dstPtr e_s e_d decl_s decl_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      0 < elemBytes →
      CopyTargetCompatible decl_s decl_d pointeeTy.kind)
    {srcPtr dstPtr : ProvenancePtr} {countSc : ScalarVal}
    {e_s e_d : AllocMapEntry} {decl_s decl_d : LocalDecl} {srcBytes dstBytes : Nat}
    (hsrcPtr : get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)))
    (hdstPtr : get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)))
    (hcountSc : WriteBytesScalarPreVal s.frame.locals countOp countSc)
    (hcount_pos : 0 < countSc.bits * elemBytes)
    (hcount_max : countSc.bits * elemBytes ≤ isizeMaxBytes)
    (hes_in : e_s ∈ allocMap) (hes_tag : e_s.tag = srcPtr.tag)
    (hed_in : e_d ∈ allocMap) (hed_tag : e_d.tag = dstPtr.tag)
    (hdecl_s : get? body.localDecls e_s.localIdx = some decl_s)
    (hdecl_d : get? body.localDecls e_d.localIdx = some decl_d)
    (hsrcBytes : rigidTyByteSize body.layouts decl_s.ty = some srcBytes)
    (hdstBytes : rigidTyByteSize body.layouts decl_d.ty = some dstBytes)
    (hsrcOOB : srcPtr.offsetBytes + countSc.bits * elemBytes ≤ srcBytes)
    (hdstOOB : dstPtr.offsetBytes + countSc.bits * elemBytes ≤ dstBytes)
    (hdead_s : get? s.frame.locals e_s.localIdx ≠ some .dead)
    (hdead_d : get? s.frame.locals e_d.localIdx ≠ some .dead)
    (hlive_ok : e_s.perm ≠ .disabled ∧
        get? s.frame.locals e_s.localIdx ≠ some .uninit ∧
        ((dstPtr.offsetBytes = 0 ∧ countSc.bits * elemBytes = dstBytes) ∨
          get? s.frame.locals e_d.localIdx ≠ some .uninit) ∧
        (∀ x ∈ allocMap, x.localIdx = e_d.localIdx →
          (x.tag = dstPtr.tag ∧ x.perm = .active) ∨ (x.tag ≠ dstPtr.tag ∧ x.perm = .disabled))) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hexp := step_intrinsic_copyNonOverlapping_simulation_explicit hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt htgt_compat
    (fun srcPtr' dstPtr' countSc' e_s' e_d' decl_s' decl_d' srcBytes' dstBytes' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 =>
      have hes_eq : e_s' = e_s := sorry
      have hed_eq : e_d' = e_d := sorry
      have hsrc_eq : srcPtr' = srcPtr := sorry
      have hdst_eq : dstPtr' = dstPtr := sorry
      have hcnt_eq : countSc' = countSc := sorry
      have hsz_eq : dstBytes' = dstBytes := sorry
      have hperm_s : e_s'.perm ≠ .disabled := by rw [hes_eq]; exact hlive_ok.1
      have hinit_s : get? s.frame.locals e_s'.localIdx ≠ some .uninit := by
        rw [hes_eq]; exact hlive_ok.2.1
      have hperm_d : e_d'.perm = .active ∨ e_d'.perm = .reserved := Or.inl (by
        rw [hed_eq]
        have ⟨h, _⟩ := hlive_ok.2.2.2 e_d hed_in rfl
        exact h)
      have hinit_d : (dstPtr'.offsetBytes = 0 ∧ countSc'.bits * elemBytes = dstBytes') ∨ get? s.frame.locals e_d'.localIdx ≠ some .uninit := by
        rw [hdst_eq, hed_eq, hcnt_eq, hsz_eq]
        exact hlive_ok.2.2.1
      ⟨hperm_s, hperm_d, hinit_s, hinit_d⟩)
  have heq : copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes = allocMap := by
    unfold copyNextAllocMap writeBytesNextAllocMap
    have hsc_eq : writeBytesScalarVal? s.frame.locals countOp = some countSc := sorry
    simp only [hsc_eq, hdstPtr, ↓reduceIte]
    by_cases hzero : countSc.bits * elemBytes = 0
    · simp [hzero]
    · simp only [hzero, ↓reduceIte]
      have hfind : lookupAllocMapByTag allocMap dstPtr.tag = some e_d := sorry
      simp only [hfind, ↓reduceIte]
      unfold updateAllocMapOnWrite
      apply list_map_id
      intro e he
      unfold AllocMapEntry.updateOnWrite AllocMapEntry.toBorrowEntry updateBorrowPerm
      cases hlocal : Nat.beq e.localIdx e_d.localIdx <;> dsimp only
      · rfl
      · cases htag : Nat.beq e.tag dstPtr.tag <;> dsimp only
        · rfl
        · have heq_local : e.localIdx = e_d.localIdx := Nat.eq_of_beq_eq_true hlocal
          have hneq_tag : e.tag ≠ dstPtr.tag := fun h => by rw [h, Nat.beq_self_eq_true] at htag; contradiction
          have ⟨_, h_dis⟩ := hlive_ok.2.2.2 e he heq_local
          have hd : e.perm = .disabled := h_dis hneq_tag
          rw [hd]
          rfl
  rw [heq] at hexp
  exact hexp

"""
content = content.replace(old_body, new_body)
with open(file_path, 'w') as f:
    f.write(content)
