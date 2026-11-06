import LeanMiriSpec.Correspondence.Relation
open LeanMiriSpec.Correspondence

theorem disjoint_empty (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (h_no_ind : ∀ (k : Nat) lay mp, tf.locals[k]? ≠ some ({ value := Miri.Interpreter.LocalValue.live (Miri.Interpreter.Operand.indirect mp), layout := lay } : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)) :
    MemoryAllocDisjoint tf := by
  intro i j mplace_i mplace_j lay_i lay_j hneq hi hj
  have h1 := h_no_ind i (some lay_i) mplace_i
  contradiction
