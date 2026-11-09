import re

file_path = "lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean"
with open(file_path, 'r') as f:
    content = f.read()

old_proof = """  have heq : copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes = allocMap := by
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

new_proof = """  have heq : copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes = allocMap := by
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

content = content.replace(old_proof, new_proof)
with open(file_path, 'w') as f:
    f.write(content)
