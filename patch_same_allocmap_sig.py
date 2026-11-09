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

new_sig = """    {srcPtr dstPtr : Pointer} {countSc : ScalarVal}
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

content = content.replace(old_sig, new_sig)

old_body = """  have hexp := step_intrinsic_copyNonOverlapping_simulation_explicit hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt htgt_compat
    (fun srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 =>
      have ⟨hperm_s, hinit_s, hinit_d, h_active⟩ := hlive_ok srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      have hperm_d : e_d.perm = .active ∨ e_d.perm = .reserved := Or.inl (by
        have ⟨h, _⟩ := h_active e_d h7 rfl; exact h)
      ⟨hperm_s, hperm_d, hinit_s, hinit_d⟩)
  have heq : copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes = allocMap := by
    unfold copyNextAllocMap writeBytesNextAllocMap
    rcases writeBytesScalarVal? s.frame.locals countOp with _ | countSc
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
            have hid : (fun e => AllocMapEntry.updateOnWrite e e_d.localIdx (some dstPtr.tag)) = id := by
              funext e
              unfold AllocMapEntry.updateOnWrite AllocMapEntry.toBorrowEntry updateBorrowPerm
              dsimp only
              cases Nat.beq e.localIdx e_d.localIdx <;> dsimp only
              · rfl
              · cases Nat.beq e.tag dstPtr.tag <;> dsimp only
                · rfl
                · -- Need e.perm = .disabled when e.tag != dstPtr.tag
                  -- How to extract this from hlive_ok?
                  -- We can just leave `sorry` for now and I will manually prove it via hstate.tags_nodup.
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
      have heq_srcPtr : srcPtr' = srcPtr := by simp [hsrcPtr] at h1; exact h1
      have heq_dstPtr : dstPtr' = dstPtr := by simp [hdstPtr] at h2; exact h2
      have ⟨hperm_s, hinit_s, hinit_d, h_active⟩ := hlive_ok
      have hperm_d : e_d'.perm = .active ∨ e_d'.perm = .reserved := Or.inl (by
        have heq_ed : e_d' = e_d := by
          subst heq_dstPtr
          -- We know e_d' ∈ allocMap and e_d'.tag = dstPtr.tag
          -- and e_d ∈ allocMap and e_d.tag = dstPtr.tag.
          -- Wait, we can just apply h_active to e_d'!
          have ⟨h_act, _⟩ := h_active e_d' h8 rfl
          exact h_act
        -- Wait, if I just use h_active on e_d', I get what I need:
        have ⟨h_act, _⟩ := h_active e_d' h8 rfl
        exact h_act)
      -- Wait, I also need to prove e_s'.perm != .disabled.
      -- But e_s' might not be e_s? It is, because tags are unique per allocMap, but I don't want to prove that here.
      -- Let's just use `sorry` for `hexp`'s proof of `hlive_ok` properties for now and fix it, OR
      -- Just revert my idea! `step_intrinsic_copyNonOverlapping_simulation_explicit` DOES quantify over them because the execution engine *discovers* them!
      sorry)"""

# I will just write a leaner lean script to prove heq using `hstate` and `tags_nodup` instead!
