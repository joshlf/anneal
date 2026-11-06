commit 048ecb2422eb9d330e8b2e8ed5f8fbf78c66f96c
Author: Mark Dittmer <markdittmer@google.com>
Date:   Fri Nov 6 19:47:17 2026 +0000

    [adv A2] Extract layout and memory write lemmas for move/allocation simulation

diff --git a/lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean b/lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean
index 1e2b46d2..716193ad 100644
--- a/lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean
+++ b/lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean
@@ -9,6 +9,14 @@ open Trusted.Rustc.V2026_06_01.Layout
 open Trusted.Rustc.V2026_06_01.MirAst
 open Trusted.Rustc.V2026_06_01.MirSemantics
 
+theorem split_bind {α β σ E} {x : EStateM E σ α} {f : α → EStateM E σ β} {m m' : σ} {b : β}
+  (h : EStateM.bind x f m = EStateM.Result.ok b m') : ∃ a m1, x m = EStateM.Result.ok a m1 ∧ f a m1 = EStateM.Result.ok b m' := by
+  cases hx : x m with
+  | error e m1 => rw [EStateM.bind, hx] at h; contradiction
+  | ok a m1 => rw [EStateM.bind, hx] at h; exact ⟨a, m1, rfl, h⟩
+
+
+
 theorem translateBody_basicBlocks_getElem? (body : CapturedMir) (i : Nat) :
     (translateBody body).basicBlocks[i]? =
       (get? body.basicBlocks i).map translateBasicBlockData := by
@@ -758,150 +766,85 @@ theorem evalOperand_move_simulation
     StepRel body m
       (stepMirFn body s)
       (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
-  exact sorry
-
-theorem split_bind {α β σ E} {x : EStateM E σ α} {f : α → EStateM E σ β} {m m' : σ} {b : β}
-  (h : EStateM.bind x f m = EStateM.Result.ok b m') : ∃ a m1, x m = EStateM.Result.ok a m1 ∧ f a m1 = EStateM.Result.ok b m' := by
-  cases hx : x m with
-  | error e m1 => rw [EStateM.bind, hx] at h; contradiction
-  | ok a m1 => rw [EStateM.bind, hx] at h; exact ⟨a, m1, rfl, h⟩
+  rcases hstate with ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller, hdisj⟩
+  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
+  simp only [hbb, hstmt]
+  have hwt' := hwt topFrame hframes
+  cases hwt' with
+  | assignMove _ dstDecl _ srcDecl _ hdst hsrc hproj hty =>
+    have hlt_body_src : srcPlace.local_ < body.localDecls.length := List_get_eq_some_length_storage hsrc
+    have hlt_af_src : srcPlace.local_ < s.frame.locals.length := by
+      rw [hfr.af_locals_len]; exact hlt_body_src
+    have hlt_mf_src : srcPlace.local_ < topFrame.locals.size := by
+      rw [hfr.mf_locals_size]; exact hlt_body_src
+    have ⟨slot_src, hslot_src⟩ := List_get_eq_some_of_lt_storage hlt_af_src
+    have ⟨mls_src, hmls_src⟩ := Array_get_eq_some_of_lt_storage hlt_mf_src
+    
+    have hlt_body_dst : dstIdx < body.localDecls.length := List_get_eq_some_length_storage hdst
+    have hlt_af_dst : dstIdx < s.frame.locals.length := by
+      rw [hfr.af_locals_len]; exact hlt_body_dst
+    have hlt_mf_dst : dstIdx < topFrame.locals.size := by
+      rw [hfr.mf_locals_size]; exact hlt_body_dst
+    have ⟨slot_dst, hslot_dst⟩ := List_get_eq_some_of_lt_storage hlt_af_dst
+    have ⟨mls_dst, hmls_dst⟩ := Array_get_eq_some_of_lt_storage hlt_mf_dst
+    
+    cases h_slot_src_eq : slot_src with
+    | init v => sorry
+    | uninit => sorry
+    | dead => sorry
+
+theorem LocalRel_cacheLayout {mach decl layouts slot value} {lay : Miri.Interpreter.LocalLayout} :
+  lay = translateTy decl.ty layouts →
+  LocalRel mach decl layouts slot value →
+  LocalRel mach decl layouts slot { value with layout := some lay } := by
+  intro hl hrel
+  cases hrel
+  · apply LocalRel.dead
+    intro l hl_some
+    cases hl_some
+    exact hl
+  · apply LocalRel.immediate
+    · intro l hl_some
+      cases hl_some
+      exact hl
+    · assumption
+  · apply LocalRel.indirect
+    · intro l hl_some
+      cases hl_some
+      exact hl
+    · assumption
+    · assumption
+
+theorem FrameRel_cacheLayout {body mach af mf} {idx : Nat} {lay : Miri.Interpreter.LocalLayout}
+  (hrel : FrameRel body mach af mf)
+  {decl_cached : LocalDecl}
+  (hdecl : get? body.localDecls idx = some decl_cached)
+  (hlay : lay = translateTy decl_cached.ty body.layouts)
+  (hlt : idx < mf.locals.size) :
+  FrameRel body mach af (cacheFrameLocalLayout mf idx hlt lay) := by
+  cases hrel with | mk body_eq loc_eq af_locals_len mf_locals_len h_locs =>
+  apply FrameRel.mk
+  · exact body_eq
+  · exact loc_eq
+  · exact af_locals_len
+  · unfold cacheFrameLocalLayout; dsimp; rw [Array.size_set]; exact mf_locals_len
+  · intro i decl_i slot mls_i h_decl_i h_slot_i h_mls_i
+    unfold cacheFrameLocalLayout at h_mls_i; dsimp at h_mls_i
+    rw [Array.getElem?_set] at h_mls_i
+    split at h_mls_i
+    next heq =>
+      subst i
+      rw [hdecl] at h_decl_i
+      cases h_decl_i
+      have h_mls_idx : mf.locals[idx]? = some (mf.locals[idx]'hlt) := by
+        apply Array.getElem?_eq_getElem
+      have h_loc := h_locs idx decl_cached slot (mf.locals[idx]'hlt) hdecl h_slot_i h_mls_idx
+      injection h_mls_i with heq_mls
+      subst mls_i
+      apply LocalRel_cacheLayout hlay h_loc
+    next hneq =>
+      exact h_locs i decl_i slot mls_i h_decl_i h_slot_i h_mls_i
 
-theorem MemPlaceRel_update {mach1 mach2 : AnnealMachine} {ty layouts optVal mp} :
-  (∀ x, x ∈ mach1.memory.live.toList → x ∈ mach2.memory.live.toList) →
-  mach1.addresses = mach2.addresses →
-  MemPlaceRel mach1 ty layouts optVal mp →
-  MemPlaceRel mach2 ty layouts optVal mp := by
-  intro h_live h_addr h_rel
-  cases h_rel with | mk allocId tag baseAddr relOffset localAlloc ptr_prov no_misalign thin_meta live_lookup base_lookup addr_no_overflow ptr_addr_eq mut_alloc aligned_ptr in_bounds uninit_consistent =>
-    apply MemPlaceRel.mk <;> try assumption
-    · apply h_live; assumption
-    · dsimp [AnnealMachine.lookupBaseAddr] at *
-      rw [← h_addr]; assumption
-
-theorem LocalRel_update {mach1 mach2 : AnnealMachine} {decl layouts slot mls} :
-  (∀ x, x ∈ mach1.memory.live.toList → x ∈ mach2.memory.live.toList) →
-  mach1.addresses = mach2.addresses →
-  LocalRel mach1 decl layouts slot mls →
-  LocalRel mach2 decl layouts slot mls := by
-  intro h_live h_addr h_rel
-  cases h_rel with
-  | dead cachedLayout h_layout =>
-    exact LocalRel.dead cachedLayout h_layout
-  | immediate slot imm cachedLayout h_layout h_imm =>
-    exact LocalRel.immediate slot imm cachedLayout h_layout h_imm
-  | indirect slot mp cachedLayout h_layout h_not_dead h_mem =>
-    apply LocalRel.indirect slot mp cachedLayout h_layout h_not_dead
-    apply MemPlaceRel_update h_live h_addr h_mem
-
-theorem FrameRel_update {body mach1 mach2 af mf} :
-  (∀ x, x ∈ mach1.memory.live.toList → x ∈ mach2.memory.live.toList) →
-  mach1.addresses = mach2.addresses →
-  FrameRel body mach1 af mf →
-  FrameRel body mach2 af mf := by
-  intro h_live h_addr h_rel
-  cases h_rel with | mk h1 h2 h3 h4 h5 =>
-  apply FrameRel.mk h1 h2 h3 h4
-  intro i decl slot mls h_decl h_slot h_mls
-  apply LocalRel_update h_live h_addr
-  exact h5 i decl slot mls h_decl h_slot h_mls
-
-theorem reserveAllocId_live {Prov Extra MachineKind} (s : Miri.Memory.MemoryState Prov Extra MachineKind) :
-  (Miri.Memory.MemoryState.reserveAllocId s).fst.live = s.live := by
-  dsimp [Miri.Memory.MemoryState.reserveAllocId]
-  split
-  · rfl
-  · split
-    · rfl
-    · split
-      · dsimp [Id.run]; split <;> rfl
-      · split
-        · dsimp [Id.run]; split <;> rfl
-        · dsimp [Id.run]; split <;> rfl
-
-theorem StateRel_allocateStack {body s m layout a m_new} :
-  StateRel body s m →
-  (annealPlaceHooks body.localDecls body.layouts).allocateStack () layout m = EStateM.Result.ok a m_new →
-  StateRel body s m_new := by
-  intro h h_alloc
-  unfold Miri.Interpreter.PlaceHooks.allocateStack at h_alloc
-  dsimp [annealPlaceHooks] at h_alloc
-  cases h_try : Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi Miri.Memory.AllocInit.Uninit (fun _ _ => none) <;> rw [h_try] at h_alloc <;> try contradiction
-  have ⟨alloc_bound, m1, h_pure, h_alloc1⟩ := split_bind h_alloc
-  have ⟨state, m2, h_get, h_alloc2⟩ := split_bind h_alloc1
-  cases h_res : (Miri.Memory.MemoryState.reserveAllocId state.machine.memory).snd <;> rw [h_res] at h_alloc2 <;> try contradiction
-  have ⟨id_bound, m3, h_pure2, h_alloc3⟩ := split_bind h_alloc2
-  have ⟨_, m4, h_set, h_alloc4⟩ := split_bind h_alloc3
-  dsimp [pure, EStateM.pure] at h_pure
-  injection h_pure with _ hm1; subst m1
-  dsimp [get, EStateM.get, StateT.get] at h_get
-  injection h_get with hs_eq hm2; subst state m2
-  dsimp [set, EStateM.set, StateT.set] at h_set
-  injection h_set with _ hm4; subst m4
-  dsimp [pure, EStateM.pure] at h_alloc4
-  injection h_alloc4 with _ hm_new; subst m_new
-  cases h with | mk top frames cont ret f_rel active call bor prot call_l alloc_d =>
-  apply StateRel.mk top
-  · exact frames
-  · exact cont
-  · exact ret
-  · apply FrameRel_update (mach1 := m.machine)
-    · intro x h_in
-      dsimp
-      rw [reserveAllocId_live]
-      rw [Array.toList_push]
-      apply List.mem_append_left
-      exact h_in
-    · exact rfl
-    · exact f_rel
-  · exact active
-  · exact call
-  · exact bor
-  · exact prot
-  · exact call_l
-  · exact alloc_d
-
-theorem StateRel_setFrame {body s m frame w m_new} :
-  StateRel body s m →
-  (annealPlaceHooks body.localDecls body.layouts).setFrame frame m = EStateM.Result.ok w m_new →
-  FrameRel body m_new.machine s.frame frame →
-  frame.returnContinuation = Miri.Interpreter.ReturnContinuation.stop false →
-  (∃ retLay, frame.returnPlace = Miri.Interpreter.RuntimeStackPlace.frameLocal 0 0 none retLay frame.localsIdentity) →
-  MemoryAllocDisjoint frame →
-  StateRel body s m_new := by
-  intro hs h_set h_frel h_cont h_ret h_disj
-  cases hs with | mk top frames cont ret f_rel active call bor prot call_l alloc_d =>
-  unfold Miri.Interpreter.PlaceHooks.setFrame at h_set
-  dsimp [annealPlaceHooks] at h_set
-  have ⟨state, m2, h_get, h_set1⟩ := split_bind h_set
-  dsimp [get, EStateM.get, StateT.get] at h_get
-  injection h_get with hs_eq hm2; subst state m2
-  split at h_set1
-  next h_idx =>
-    dsimp [set, EStateM.set, StateT.set] at h_set1
-    injection h_set1 with _ hm_new; subst m_new
-    apply StateRel.mk frame
-    · dsimp
-      revert h_idx
-      rw [frames]
-      intro h _ _
-      rfl
-    · exact h_cont
-    · exact h_ret
-    · exact h_frel
-    · exact active
-    · exact call
-    · exact bor
-    · exact prot
-    · exact call_l
-    · exact h_disj
-  next =>
-    contradiction
-
-theorem StateRel_writeMemoryNoValidate {body s m value mplace w m_new} :
-  StateRel body s m →
-  (annealPlaceHooks body.localDecls body.layouts).writeMemoryNoValidate () value mplace m = EStateM.Result.ok w m_new →
-  StateRel body s m_new := by
-  sorry
 
 theorem forceAllocation_preserves_StateRel
     {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
@@ -914,7 +857,129 @@ theorem forceAllocation_preserves_StateRel
     (mplace : Miri.Interpreter.MPlaceTy AnnealProv)
     (hforce : Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) () place m = .ok mplace m') :
     StateRel body s m' := by
-  exact sorry
+  unfold Miri.Interpreter.forceAllocation at hforce
+  cases hpref : place.ref with
+  | «local» frameIndex localId offset identity =>
+    rw [hpref] at hforce
+    dsimp only at hforce
+    rw [Miri.Interpreter.requireCurrent_eq] at hforce
+    rw [Miri.Interpreter.checkLocalIdentity_debugOff (off := rfl)] at hforce
+    have ⟨res_req, m1, h_require, hforce1⟩ := split_bind hforce
+    have ⟨a_req, s_req, h_fidx, h_req2⟩ := split_bind h_require
+    dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.frameIndex, get, EStateM.get, StateT.get] at h_fidx
+    injection h_fidx with _ hs_req; subst s_req
+    split at h_req2 <;> try contradiction
+    dsimp [pure, EStateM.pure] at h_req2
+    injection h_req2 with _ hm1; subst m1
+    have ⟨res_check, m2, h_check, hforce2⟩ := split_bind hforce1
+    dsimp [pure, EStateM.pure] at h_check
+    injection h_check with _ hm2; subst m2
+    
+    have ⟨res_frame, m3, h_frame, hforce3⟩ := split_bind hforce2
+    unfold Miri.Interpreter.PlaceHooks.getFrame at h_frame
+    have ⟨a_frame_state, s_frame_state, h_frame_get, h_frame_match⟩ := split_bind h_frame
+    dsimp [get, EStateM.get, StateT.get] at h_frame_get
+    injection h_frame_get with h_a hs_frame
+    subst a_frame_state s_frame_state
+    
+    unfold Miri.Interpreter.Stack.currentFrame? at h_frame_match
+    rw [hframes] at h_frame_match
+    dsimp [Array.back?] at h_frame_match
+    dsimp [pure, EStateM.pure] at h_frame_match
+    injection h_frame_match with h_res_frame hm3; subst m3
+    
+    have ⟨old, m4, h_lift, hforce4⟩ := split_bind hforce3
+    
+    cases h_op : res_frame.getLocalOperand localId
+    · rw [h_op] at h_lift
+      -- if error, stackLift evaluates to error, which contradicts ok
+      revert h_lift
+      intro h_lift
+      contradiction
+    · rw [h_op] at h_lift
+      dsimp [pure, EStateM.pure] at h_lift
+      injection h_lift with h_old hm4; subst m4
+      cases h_old_match : old with
+      | indirect mplace_old =>
+        rw [h_old_match] at hforce4
+        dsimp only at hforce4
+        have ⟨whole, m5, h_pure, hforce5⟩ := split_bind hforce4
+        dsimp [pure, EStateM.pure] at h_pure
+        injection h_pure with _ hm5; subst m5
+        cases h_off : offset <;> rw [h_off] at hforce5 <;> dsimp only at hforce5
+        · dsimp [bind, StateT.bind, EStateM.bind, pure, EStateM.pure] at hforce5
+          injection hforce5 with _ hm_eq
+          subst hm_eq
+          exact hstate
+        · have ⟨whole2, m6, h_mem_off, hforce6⟩ := split_bind hforce5
+          dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.memoryOffset] at h_mem_off
+          dsimp [throw, EStateM.throw] at h_mem_off
+          contradiction
+      | immediate val =>
+        rw [h_old_match] at hforce4
+        dsimp only at hforce4
+        unfold Miri.Interpreter.placeLayoutOfLocal at hforce4
+        have ⟨layout, m5, h_layout, hforce5⟩ := split_bind hforce4
+        
+        -- Now h_layout is the execution of placeLayoutOfLocal
+        have hstate5 : StateRel body s m5 := by
+          sorry
+        
+        split at hforce5
+        · dsimp [throw, EStateM.throw] at hforce5
+          contradiction
+        · dsimp [pure, EStateM.pure] at hforce5
+          have ⟨allocated, m6, h_alloc, hforce6⟩ := split_bind hforce5
+          
+          cases hval : val with
+          | uninit =>
+            rw [hval] at hforce6
+            dsimp only at hforce6
+            have ⟨res_after, m7, h_after, hforce7⟩ := split_bind hforce6
+            dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.afterLocalMovedToMemory, pure, EStateM.pure] at h_after
+            injection h_after with _ hm7; subst m7
+            
+            have ⟨res_f2, m8, h_f2, hforce8⟩ := split_bind hforce7
+            unfold Miri.Interpreter.PlaceHooks.getFrame at h_f2
+            have ⟨state_get, m_get, h_get, h_get_rest⟩ := split_bind h_f2
+            dsimp [get, EStateM.get, StateT.get] at h_get
+            injection h_get with _ hm_get; subst m_get state_get
+            have hrel6 := StateRel_allocateStack hstate5 h_alloc
+            rcases hrel6 with ⟨_, hframes6, _⟩
+            
+            unfold Miri.Interpreter.Stack.currentFrame? at h_get_rest
+            rw [hframes6] at h_get_rest
+            dsimp [Array.back?] at h_get_rest
+            dsimp [pure, EStateM.pure] at h_get_rest
+            injection h_get_rest with hm8_frame hm8; subst m8 res_f2
+            
+            have ⟨res_sl, m9, h_sl, hforce9⟩ := split_bind hforce8
+            simp only [hframes6, Array.size_toArray, List.length_singleton, Nat.reduceSub, Array.getElem_toArray, List.get_singleton] at h_sl
+            
+            cases h_set_op : (topFrame.setLocalOperand localId (Miri.Interpreter.Operand.indirect allocated.mplace)) with
+            | error e =>
+              rw [h_set_op] at h_sl
+              -- we can prove contradiction since it is a failure
+              sorry
+            | ok frame_new => sorry
+          | scalar sc =>
+            rw [hval] at hforce6
+            dsimp only at hforce6
+            trace_state; sorry
+          | scalarPair sc1 sc2 =>
+            rw [hval] at hforce6
+            dsimp only at hforce6
+            trace_state; sorry
+  | memory mplace_mem =>
+    rw [hpref] at hforce
+    dsimp only at hforce
+    have ⟨whole, m1, h_pure, hforce_rest⟩ := split_bind hforce
+    dsimp [pure, EStateM.pure] at h_pure hforce_rest
+    injection h_pure with hwhole hm1
+    subst m1
+    injection hforce_rest with hmplace hm_eq
+    subst m'
+    exact hstate
 
 end LeanMiriSpec.Correspondence
 
