874:theorem forceAllocation_preserves_StateRel
875-    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
876-    (hstate : StateRel body s m)
877-    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
878-    (hframes : m.stack.frames = #[topFrame])
879-    (loc : Local)
880-    (place : Miri.Interpreter.RuntimePlace AnnealProv)
881-    (m' : AnnealStepState)
882-    (mplace : Miri.Interpreter.MPlaceTy AnnealProv)
883-    (hforce : Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) () place m = .ok mplace m') :
884-    StateRel body s m' := by
885-  unfold Miri.Interpreter.forceAllocation at hforce
886-  cases hpref : place.ref with
887-  | «local» frameIndex localId offset identity =>
888-    rw [hpref] at hforce
889-    dsimp only at hforce
890-    rw [Miri.Interpreter.requireCurrent_eq] at hforce
891-    rw [Miri.Interpreter.checkLocalIdentity_debugOff (off := rfl)] at hforce
892-    have ⟨res_req, m1, h_require, hforce1⟩ := split_bind hforce
893-    have ⟨a_req, s_req, h_fidx, h_req2⟩ := split_bind h_require
894-    dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.frameIndex, get, EStateM.get, StateT.get] at h_fidx
895-    injection h_fidx with _ hs_req; subst s_req
896-    split at h_req2 <;> try contradiction
897-    dsimp [pure, EStateM.pure] at h_req2
898-    injection h_req2 with _ hm1; subst m1
899-    have ⟨res_check, m2, h_check, hforce2⟩ := split_bind hforce1
900-    dsimp [pure, EStateM.pure] at h_check
901-    injection h_check with _ hm2; subst m2
902-    
903-    have ⟨res_frame, m3, h_frame, hforce3⟩ := split_bind hforce2
904-    unfold Miri.Interpreter.PlaceHooks.getFrame at h_frame
905-    have ⟨a_frame_state, s_frame_state, h_frame_get, h_frame_match⟩ := split_bind h_frame
906-    dsimp [get, EStateM.get, StateT.get] at h_frame_get
907-    injection h_frame_get with h_a hs_frame
908-    subst a_frame_state s_frame_state
909-    
910-    unfold Miri.Interpreter.Stack.currentFrame? at h_frame_match
911-    rw [hframes] at h_frame_match
912-    dsimp [Array.back?] at h_frame_match
913-    dsimp [pure, EStateM.pure] at h_frame_match
914-    injection h_frame_match with h_res_frame hm3; subst m3
915-    
916-    have ⟨old, m4, h_lift, hforce4⟩ := split_bind hforce3
917-    
918-    cases h_op : res_frame.getLocalOperand localId
919-    · rw [h_op] at h_lift
920-      -- if error, stackLift evaluates to error, which contradicts ok
921-      revert h_lift
922-      intro h_lift
923-      contradiction
924-    · rw [h_op] at h_lift
