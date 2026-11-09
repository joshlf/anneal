import re

file_path = "lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean"
with open(file_path, 'r') as f:
    content = f.read()

old_sig = """    (hlive_ok : ∀ srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      countSc.bits * elemBytes ≤ isizeMaxBytes →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      rigidTyByteSize body.layouts decl_s.ty = some srcBytes →
      rigidTyByteSize body.layouts decl_d.ty = some dstBytes →
      srcPtr.offsetBytes + countSc.bits * elemBytes ≤ srcBytes →
      dstPtr.offsetBytes + countSc.bits * elemBytes ≤ dstBytes →
      get? s.frame.locals e_s.localIdx ≠ some .dead →
      get? s.frame.locals e_d.localIdx ≠ some .dead →
      e_s.perm ≠ .disabled ∧
        get? s.frame.locals e_s.localIdx ≠ some .uninit ∧
        ((dstPtr.offsetBytes = 0 ∧ countSc.bits * elemBytes = dstBytes) ∨
          get? s.frame.locals e_d.localIdx ≠ some .uninit) ∧
        (∀ x ∈ allocMap, x.localIdx = e_d.localIdx →
          (x.tag = dstPtr.tag ∧ x.perm = .active) ∨ (x.tag ≠ dstPtr.tag ∧ x.perm = .disabled))) :"""

new_sig = """    {srcPtr dstPtr : ProvenancePtr} {countSc : ScalarVal}
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
          (x.tag = dstPtr.tag ∧ x.perm = .active) ∨ (x.tag ≠ dstPtr.tag ∧ x.perm = .disabled))) :"""

old_body = """  have hexp := step_intrinsic_copyNonOverlapping_simulation_explicit hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt htgt_compat
    (fun srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 =>
      have ⟨hperm_s, hinit_s, hinit_d, h_active⟩ := hlive_ok srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      have hperm_d : e_d.perm = .active ∨ e_d.perm = .reserved := Or.inl (by
        have ⟨h, _⟩ := h_active e_d h7 rfl; exact h)
      ⟨hperm_s, hperm_d, hinit_s, hinit_d⟩)
  have heq : copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes = allocMap := by
    unfold copyNextAllocMap writeBytesNextAllocMap
    rcases hsc : writeBytesScalarVal? s.frame.locals countOp with _ | countSc
    · rfl
    · by_cases hzero : countSc.bits * elemBytes = 0
      · simp [hzero]
      · simp only [hzero, ↓reduceIte]
        match hget : get? s.frame.locals dstIdx with
        | some (.init (.ptr dstPtr 8)) =>
          match hfind : lookupAllocMapByTag allocMap dstPtr.tag with
          | none => rfl
          | some e_d =>
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
                -- We must prove e.perm = .disabled using `hstate` and `he` and `e_d`
                sorry
        | none => rfl
        | some .uninit => rfl
        | some .dead => rfl
        | some (.init (.scalar _)) => rfl
  rw [heq] at hexp
  exact hexp"""

new_body = """  have hexp := step_intrinsic_copyNonOverlapping_simulation_explicit hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt htgt_compat
    (fun srcPtr' dstPtr' countSc' e_s' e_d' decl_s' decl_d' srcBytes' dstBytes' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 =>
      have hsrc_eq : srcPtr' = srcPtr := by simp [hsrcPtr] at h1; exact h1
      have hdst_eq : dstPtr' = dstPtr := by simp [hdstPtr] at h2; exact h2
      have hcnt_eq : countSc' = countSc := by
        unfold WriteBytesScalarPreVal writeBytesScalarVal? at hcountSc h3
        revert hcountSc h3
        cases get? s.frame.locals countOp.local_ <;> intro h1 h2 <;> (try contradiction)
        cases h : _ <;> rw [h] at h1 h2 <;> (try contradiction)
        cases h_1 : _ <;> rw [h_1] at h1 h2 <;> (try contradiction)
        cases h_2 : _ <;> rw [h_2] at h1 h2 <;> (try contradiction)
        subst h1
        exact h2.symm
      have ⟨hperm_s, hinit_s, hinit_d, h_active⟩ := hlive_ok
      have hed_eq : e_d' = e_d := by
        have ht : e_d'.tag = e_d.tag := by rw [h8, hdst_eq, ←hed_tag]
        -- allocMap tags are unique
        have hn := hstate.allocMap_rel.tags_nodup
        exact AllocMapEntry.eq_of_tag_eq hn h7 hed_in ht
      have hes_eq : e_s' = e_s := by
        have ht : e_s'.tag = e_s.tag := by rw [h6, hsrc_eq, ←hes_tag]
        have hn := hstate.allocMap_rel.tags_nodup
        exact AllocMapEntry.eq_of_tag_eq hn h5 hes_in ht
      have hperm_d : e_d'.perm = .active ∨ e_d'.perm = .reserved := Or.inl (by
        rw [hed_eq]
        have ⟨h, _⟩ := h_active e_d hed_in rfl
        exact h)
      ⟨by rw [hes_eq]; exact hperm_s, hperm_d, by rw [hes_eq]; exact hinit_s, by rw [hed_eq]; exact hinit_d⟩)
  have heq : copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes = allocMap := by
    unfold copyNextAllocMap writeBytesNextAllocMap
    have hsc_eq : writeBytesScalarVal? s.frame.locals countOp = some countSc := hcountSc
    simp only [hsc_eq, hdstPtr, Option.some.injEq, ↓reduceIte]
    by_cases hzero : countSc.bits * elemBytes = 0
    · simp [hzero]
    · simp only [hzero, ↓reduceIte]
      have hfind : lookupAllocMapByTag allocMap dstPtr.tag = some e_d :=
        lookupAllocMapByTag_eq_some hstate.allocMap_rel.tags_nodup hed_in hed_tag
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
          rw [h_dis hneq_tag]
  rw [heq] at hexp
  exact hexp"""

if old_sig in content and old_body in content:
    content = content.replace(old_sig, new_sig)
    content = content.replace(old_body, new_body)
    with open(file_path, 'w') as f:
        f.write(content)
    print("Patched successfully")
else:
    print("Could not find old_sig or old_body")
