with open('lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean', 'r') as f:
    text = f.read()

old_simp = """  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hsliceS, hmul, hsliceD, hshapeS.provenanceMap_eq, hprov_prep, huninitS, hmask_prep]
  dsimp only [bind, Except.bind, pure, Except.pure]
  simp only [Miri.Memory.InitCopy.noBytesInit, Bool.false_eq_true, ↓reduceIte]
  have hendD := copyRange_endExclusive hltD"""
new_simp = """  simp only [bind, Except.bind, pure, Except.pure, hsliceS, hmul, hsliceD, hshapeS.provenanceMap_eq, hprov_prep, huninitS, hmask_prep]
  simp only [bind, Except.bind, pure, Except.pure, Miri.Memory.InitCopy.noBytesInit, Bool.false_eq_true, ↓reduceIte]
  have hendD := copyRange_endExclusive hltD"""
text = text.replace(old_simp, new_simp)

old_rw = """  rw [hts, hcopy] at heq
  exact ⟨_, heq⟩"""
new_rw = """  rw [hts] at heq
  rw [hcopy] at heq
  exact ⟨_, heq⟩"""
text = text.replace(old_rw, new_rw)

with open('lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean', 'w') as f:
    f.write(text)
