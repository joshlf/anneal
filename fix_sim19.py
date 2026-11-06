import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

replacement = """                      have hlt_decl : localId < body.localDecls.length := by
                        rw [← hfr6.af_locals_len]; exact hlt_af
                      have ⟨decl, h_decl_eq⟩ := List_get_eq_some_of_lt_storage hlt_decl
                      
                      have h_slot_ex : ∃ slot, get? s.frame.locals localId = some slot := List_get_eq_some_of_lt_storage hlt_af
                      rcases h_slot_ex with ⟨slot, h_slot_eq⟩
                      
                      have h_mls_eq : topFrame6.locals[localId]? = some (topFrame6.locals[localId]'hlt_mf) := Array.getElem?_eq_getElem topFrame6.locals localId hlt_mf
                      
                      have h_loc_orig := hfr6.locals_rel localId decl slot (topFrame6.locals[localId]'hlt_mf) h_decl_eq h_slot_eq h_mls_eq
                      
                      -- h_loc_orig is LocalRel m6.machine decl body.layouts slot (topFrame6.locals[localId]'hlt_mf)
                      -- We substitute h_loc_val to get LocalRel for immediate uninit
                      have h_loc_imm : LocalRel m6.machine decl body.layouts slot ⟨.live (.immediate .uninit), topFrame6.locals[localId]'hlt_mf |>.layout⟩ := by
                        rw [← h_loc_val]
                        exact h_loc_orig
                      
                      -- From this we know slot = .uninit
                      have h_slot_uninit : slot = .uninit := by
                        cases h_loc_imm with
                        | immediate _ _ _ _ himm =>
                          cases himm with
                          | inl h1 => exact h1.1
                          | inr h2 =>
                            rcases h2 with ⟨v, _, himm_rel⟩
                            cases himm_rel
                        | dead _ h => contradiction
                        | indirect _ _ _ _ _ _ => contradiction
                        
                      -- Now construct LocalRel.indirect for the updated frame
                      have h_local_rel : LocalRel m10.machine decl body.layouts slot ⟨.live (.indirect allocated.mplace), topFrame6.locals[localId]'hlt_mf |>.layout⟩ := by
                        refine LocalRel.indirect slot allocated.mplace (topFrame6.locals[localId]'hlt_mf |>.layout) ?_ ?_ ?_
                        · -- cache layout same
                          intro l hl
                          cases h_loc_imm with
                          | immediate _ _ _ h_cache _ => exact h_cache l hl
                        · -- not dead
                          rw [h_slot_uninit]; decide
                        · -- MemPlaceRel
                          rw [h_slot_uninit]
                          refine MemPlaceRel.mk id Miri.Memory.BorTag.one 0 0 ⟨Miri.Memory.MiriMemoryKind.stack, allocation.withExtra none⟩ (Or.inr rfl) rfl rfl ?_ (Or.inr rfl) (by decide) rfl rfl ?_ ?_ ?_
                          · -- live_lookup
                            -- m10.machine = m6.machine with id pushed
                            -- we know m10.machine.memory.live is mem_new.live.push (id, ...)
                            sorry
                          · -- aligned_ptr
                            sorry
                          · -- in_bounds
                            sorry
                          · -- uninit_consistent
                            sorry

                      have h_frame_new_rel := FrameRel_update_local_storage hfr6 h_decl_eq slot ⟨.live (.indirect allocated.mplace), topFrame6.locals[localId]'hlt_mf |>.layout⟩ h_local_rel
                      
                      -- wait, frame_new IS exactly topFrame6 with setLocalOperand
                      have h_frame_new_eq : frame_new = { topFrame6 with locals := topFrame6.locals.set localId { topFrame6.locals[localId]'hlt_mf with value := .live (.indirect allocated.mplace) } hlt_mf } := by
                        sorry
                      
                      -- and s.frame.locals is NOT changed because s.frame.locals.set localId slot is a no-op!
                      have h_s_frame_eq : { s.frame with locals := s.frame.locals.set localId slot } = s.frame := by
                        sorry
                        
                      sorry"""

content = content.replace(
    """                      have h_decl_eq : get? body.localDecls localId = some decl := by
                        -- wait, decl is NOT in scope! We just use body.localDecls.get?
                        sorry
                      trace_state
                      sorry""",
    replacement
)

with open(path, "w") as f:
    f.write(content)
