import LeanMiriSpec.Correspondence.CopyLM4_2

open MirSemantics

def list_map_id {α : Type} (l : List α) (f : α → α) (h : ∀ x ∈ l, f x = x) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.mem_cons] at *
    rw [h head (Or.inl rfl), ih]
    intro x hx
    exact h x (Or.inr hx)
