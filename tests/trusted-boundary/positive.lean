prelude
import Init.NotationExtra

namespace Outside

private def helper (n : Nat) : Nat := n

structure Box where
  value : Nat

opaque sealed : Box := Box.mk (helper 7)

@[simp] theorem helper_eq (n : Nat) : Eq (helper n) n := by rfl

noncomputable def chosen : Nat := Classical.choice ⟨0⟩
theorem extensionality (p q : Prop) (h : p ↔ q) : Eq p q := propext h
theorem quotient_sound (r : Nat → Nat → Prop) (a b : Nat) (h : r a b) :
    Eq (Quot.mk r a) (Quot.mk r b) := Quot.sound h

class Wrap (α : Type) where
  wrap : α → Nat

instance : Wrap Nat := ⟨helper⟩
def inferred : Nat := Wrap.wrap (α := Nat) 3

instance : Coe Box Nat := ⟨Box.value⟩
def coerced (b : Box) : Nat := b

inductive Indexed : Nat → Type where
  | zero : Indexed 0
  | succ {n : Nat} : Indexed n → Indexed (n + 1)

mutual
  inductive Left where
    | mk : Right → Left
  inductive Right where
    | mk : Left → Right
end

inductive Tree where
  | node : List Tree → Tree

def matched (n : Nat) : Nat :=
  match n with
  | 0 => helper 0
  | k + 1 => helper k

def sampleList : List Nat := [1, 2, 3]
def sampleExists : Prop := ∃ n : Nat, sampleList[0]? = some n

end Outside

open Outside in
def wrapped : Box := Box.mk 4
