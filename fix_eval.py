import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean") as f:
    text = f.read()

proof = """
    have h_getElem_src? := Array.getElem?_eq_getElem hlt_mf_src
    have heq_mls_src : topFrame.locals[srcPlace.local_]'hlt_mf_src = mls_src := by
      have h_tmp := hmls_src
      rw [h_getElem_src?] at h_tmp
      exact Option.some.inj h_tmp
    have hrel_src := hfr.locals_rel _ _ _ _ hsrc hslot_src hmls_src

    cases h_slot_src_eq : slot_src with
    | dead =>
      apply StepRel.ub_iff.mpr
      constructor
      · unfold evalStmt; dsimp only; rw [hslot_src, h_slot_src_eq]; rfl
      · cases hrel_src with
        | dead _ h_dead =>
          have h_val : mls_src.value = .dead := h_dead
          simp only [Miri.Interpreter.Step.step, Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind, translatePlace, translateRvalue]
          unfold annealStepHooks annealRvalueHooks annealEvalPlace annealEvalOperand annealResolveAndCacheLocalLayout Miri.Interpreter.runRvalue
          dsimp only [stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, EStateM.bind, pure, Except.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, StateT.get, Miri.Interpreter.Frame.getOrCacheLocalLayout]
          have h_proj : ((List.map translateProjectionElem []).toArray.isEmpty) = true := rfl
          simp only [h_proj, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
          unfold annealReadImmediate
          simp only [h_val, heq_mls_src, bind, Except.bind, EStateM.bind, pure, Except.pure, EStateM.pure, ↓reduceIte, ↓reduceDIte]
          rfl
        | immediate _ _ _ _ h_imm =>
          cases h_imm with
          | inl h => rcases h with ⟨h1, h2⟩; rw [h1] at h_slot_src_eq; contradiction
          | inr h => rcases h with ⟨v, h1, h2⟩; rw [h1] at h_slot_src_eq; contradiction
        | indirect _ _ _ _ h_ind =>
          cases h_ind with
          | inl h => rcases h with ⟨h1, h2⟩; rw [h1] at h_slot_src_eq; contradiction
          | inr h => rcases h with ⟨v, h1, h2⟩; rw [h1] at h_slot_src_eq; contradiction

    | uninit =>
      apply StepRel.ub_iff.mpr
      constructor
      · unfold evalStmt; dsimp only; rw [hslot_src, h_slot_src_eq]; rfl
      · cases hrel_src with
        | immediate _ _ _ _ h_imm =>
          cases h_imm with
          | inl h =>
            rcases h with ⟨h1, h2⟩
            have h_val : mls_src.value = .live (.immediate .uninit) := by rw [h2]; rfl
            simp only [Miri.Interpreter.Step.step, Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind, translatePlace, translateRvalue]
            unfold annealStepHooks annealRvalueHooks annealEvalPlace annealEvalOperand annealResolveAndCacheLocalLayout Miri.Interpreter.runRvalue
            dsimp only [stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, EStateM.bind, pure, Except.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, StateT.get, Miri.Interpreter.Frame.getOrCacheLocalLayout]
            have h_proj : ((List.map translateProjectionElem []).toArray.isEmpty) = true := rfl
            simp only [h_proj, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
            unfold annealReadImmediate
            simp only [h_val, heq_mls_src, bind, Except.bind, EStateM.bind, pure, Except.pure, EStateM.pure, ↓reduceIte, ↓reduceDIte]
            rfl
          | inr h => rcases h with ⟨v, h1, h2⟩; rw [h1] at h_slot_src_eq; contradiction
        | dead => contradiction
        | indirect _ _ _ _ h_ind =>
          cases h_ind with
          | inl h =>
            rcases h with ⟨h1, h2, h3⟩
            have h_val : mls_src.value = .live (.indirect h2) := by rfl
            -- for uninit indirect, we can prove it evaluates to ub because the read fails
            sorry
          | inr h => rcases h with ⟨v, h1, h2⟩; rw [h1] at h_slot_src_eq; contradiction

    | init v => sorry
"""

# Replace the cases h_slot_src_eq
text = re.sub(r"cases h_slot_src_eq : slot_src with.*?    \| dead => sorry\n", proof, text, flags=re.DOTALL)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(text)
