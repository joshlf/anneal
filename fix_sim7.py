with open('lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean', 'r') as f:
    text = f.read()

split_bind_text = '''theorem split_bind {α β σ E} {x : EStateM E σ α} {f : α → EStateM E σ β} {m m' : σ} {b : β}
  (h : EStateM.bind x f m = EStateM.Result.ok b m') : ∃ a m1, x m = EStateM.Result.ok a m1 ∧ f a m1 = EStateM.Result.ok b m' := by
  cases hx : x m with
  | error e m1 => rw [EStateM.bind, hx] at h; contradiction
  | ok a m1 => rw [EStateM.bind, hx] at h; exact ⟨a, m1, rfl, h⟩

'''
text = text.replace('open Trusted.Rustc.V2026_06_01.MirSemantics', 'open Trusted.Rustc.V2026_06_01.MirSemantics\n\n' + split_bind_text)

with open('lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean', 'w') as f:
    f.write(text)
