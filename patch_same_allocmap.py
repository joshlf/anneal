import re

file_path = "lean-miri/lean/LeanMiriSpec/Correspondence/CopyLM4_2.lean"
with open(file_path, 'r') as f:
    content = f.read()

# I want to add list_map_id right before step_intrinsic_copyNonOverlapping_simulation_same_allocMap
if "def list_map_id" not in content:
    idx = content.find("theorem step_intrinsic_copyNonOverlapping_simulation_same_allocMap")
    
    list_map_id_str = """
def list_map_id {α : Type} (l : List α) (f : α → α) (h : ∀ x ∈ l, f x = x) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.mem_cons] at *
    rw [h head (Or.inl rfl), ih]
    intro x hx
    exact h x (Or.inr hx)

"""
    content = content[:idx] + list_map_id_str + content[idx:]
    with open(file_path, 'w') as f:
        f.write(content)
