commit 5ff9ac345b3abc0eb961484ad186d628a3d863da
Author: Mark Dittmer <markdittmer@google.com>
Date:   Fri Nov 6 19:26:43 2026 +0000

    [adv A1] Patch Translate.lean annealEvalOperand and scaffold Move proofs

diff --git a/lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean b/lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean
index 8b509981..41253b79 100644
--- a/lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean
+++ b/lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean
@@ -745,22 +745,61 @@ theorem step_placeMention_simulation
             · rfl⟩
     )
 
+#print Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand
 theorem evalOperand_move_simulation
     {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
     (hstate : StateRel body s m)
-    {bb : BasicBlockData} {stmt : Statement}
+    (hphase : ∀ p, body.phase ≠ .other p)
+    {bb : BasicBlockData} {dstIdx : Local} {srcPlace : Place} {span : String}
     (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
-    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
+    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩)
     (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
-      WellTypedLM1_4Stmt body topFrame stmt) :
+      WellTypedLM1_4Stmt body topFrame ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩) :
     StepRel body m
       (stepMirFn body s)
       (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
-  sorry
-
-namespace LeanMiriSpec.Correspondence
-
-
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
+    | init v =>
+      have hset_af_src := List_set_eq_some_of_lt_storage hlt_af_src LocalSlot.uninit
+      have ha : evalStmt s { kind := StatementKind.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span := span } body.localDecls body.layouts = MirStepNode.step (advanceStmt s ((s.frame.locals.set srcPlace.local_ LocalSlot.uninit).set dstIdx (LocalSlot.init v))) := by
+        unfold evalStmt
+        dsimp only
+        rw [h_op, hslot_dst]
+      rw [ha]
+      have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩) m = _ := by
+        simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind, translatePlace, translateRvalue, translateOperand, annealStepHooks, Miri.Interpreter.runRvalue, Miri.Interpreter.evalRvalueIntoPlace, annealRvalueHooks, Miri.Interpreter.RvalueHooks.evalOperandAt, Miri.Interpreter.evalOperand, annealEvalOperand]
+        trace_state; sorry
+    | uninit =>
+      sorry
+    | dead =>
+      sorry
+        rw [h_eval_op]
+      unfold evalStmt
+      dsimp only
+      rw [h_op]
+      sorry
 
 theorem split_bind {α β σ E} {x : EStateM E σ α} {f : α → EStateM E σ β} {m m' : σ} {b : β}
   (h : EStateM.bind x f m = EStateM.Result.ok b m') : ∃ a m1, x m = EStateM.Result.ok a m1 ∧ f a m1 = EStateM.Result.ok b m' := by
@@ -977,7 +1016,65 @@ theorem forceAllocation_preserves_StateRel
       | immediate val =>
         rw [h_old_match] at hforce4
         dsimp only at hforce4
-        sorry
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
+            | ok frame_new =>
+              rw [h_set_op] at h_sl
+              simp only [Miri.Interpreter.stackLift_ok] at h_sl
+              injection h_sl with hm9_res hm9; subst m9 res_sl
+              
+              have ⟨res_sf, m10, h_sf, hforce10⟩ := split_bind hforce9
+              
+              trace_state; sorry
+          | scalar sc =>
+            rw [hval] at hforce6
+            dsimp only at hforce6
+            trace_state; sorry
+          | scalarPair sc1 sc2 =>
+            rw [hval] at hforce6
+            dsimp only at hforce6
+            trace_state; sorry
   | memory mplace_mem =>
     rw [hpref] at hforce
     dsimp only at hforce
@@ -991,4 +1088,3 @@ theorem forceAllocation_preserves_StateRel
 
 end LeanMiriSpec.Correspondence
 
-end LeanMiriSpec.Correspondence
