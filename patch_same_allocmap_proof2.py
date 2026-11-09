import re

file_path = "lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean"
with open(file_path, 'r') as f:
    content = f.read()

old_proof = """  have hexp := step_intrinsic_copyNonOverlapping_simulation_explicit hstate hphase hbb hstmt
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

new_proof = """  have hexp := step_intrinsic_copyNonOverlapping_simulation_explicit hstate hphase hbb hstmt
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
        match hdst : get? s.frame.locals dstIdx with
        | some (.init (.ptr dstPtr 8)) =>
          match hsrc : get? s.frame.locals srcIdx with
          | some (.init (.ptr srcPtr 8)) =>
            match hfind_d : lookupAllocMapByTag allocMap dstPtr.tag with
            | none => rfl
            | some e_d =>
              match hfind_s : lookupAllocMapByTag allocMap srcPtr.tag with
              | none => rfl
              | some e_s =>
                match hdecl_s : get? body.localDecls e_s.localIdx, hdecl_d : get? body.localDecls e_d.localIdx with
                | some decl_s, some decl_d =>
                  match hs_bytes : rigidTyByteSize body.layouts decl_s.ty, hd_bytes : rigidTyByteSize body.layouts decl_d.ty with
                  | some srcBytes, some dstBytes =>
                    by_cases hoob : srcPtr.offsetBytes + countSc.bits * elemBytes ≤ srcBytes ∧ dstPtr.offsetBytes + countSc.bits * elemBytes ≤ dstBytes
                    · unfold updateAllocMapOnWrite
                      apply list_map_id
                      intro e he
                      unfold AllocMapEntry.updateOnWrite updateBorrowPerm
                      cases hlocal : Nat.beq e.localIdx e_d.localIdx <;> dsimp only
                      · rfl
                      · cases htag : Nat.beq e.tag dstPtr.tag <;> dsimp only
                        · rfl
                        · have heq_local : e.localIdx = e_d.localIdx := Nat.eq_of_beq_eq_true hlocal
                          have hneq_tag : e.tag ≠ dstPtr.tag := fun h => by rw [h, Nat.beq_self_eq_true] at htag; contradiction
                          have h_in_d : e_d ∈ allocMap := lookupAllocMapByTag_some hfind_d
                          have h_tag_d : e_d.tag = dstPtr.tag := lookupAllocMapByTag_some_tag hfind_d
                          have h_in_s : e_s ∈ allocMap := lookupAllocMapByTag_some hfind_s
                          have h_tag_s : e_s.tag = srcPtr.tag := lookupAllocMapByTag_some_tag hfind_s
                          have hpreval : WriteBytesScalarPreVal s.frame.locals countOp countSc := by
                            unfold WriteBytesScalarPreVal writeBytesScalarVal? at hsc
                            revert hsc
                            cases get? s.frame.locals countOp.local_ <;> intro hsc <;> (try contradiction)
                            cases h : _ <;> rw [h] at hsc <;> (try contradiction)
                            cases h2 : _ <;> rw [h2] at hsc <;> (try contradiction)
                            cases h3 : _ <;> rw [h3] at hsc <;> (try contradiction)
                            sorry
                          sorry
                    · rfl
                  | _, _ => rfl
                | _, _ => rfl
              | none =>
                -- wait, this match structure is getting crazy, and I have to handle all `none` cases and `hoob` cases with `rfl`!
                -- but wait, if any of them fails, DOES the goal actually just solve with `rfl`?
                -- No, because in `heq`, we just need to prove `updateAllocMapOnWrite ... = id`.
                sorry
          | _ =>
            -- if hsrc is not `.init (.ptr ...)`, then we still need to prove it's `rfl`? NO, wait!
            -- if hsrc is not `.init (.ptr ...)`, we still get `updateAllocMapOnWrite` in the goal!!
            -- because `copyNextAllocMap` ONLY pattern matches on `dstPtr`!
            sorry
        | none => rfl
        | some .uninit => rfl
        | some .dead => rfl
        | some (.init (.scalar _)) => rfl
  rw [heq] at hexp
  exact hexp"""

content = content.replace(old_proof, new_proof)
with open(file_path, 'w') as f:
    f.write(content)
