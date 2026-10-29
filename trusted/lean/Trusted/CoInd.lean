namespace Trusted.CoInd

/-!
Polynomial functors (`PFunctor`) and coinductive M-types (`CoInd`) constructed
as projective limits of finite approximations (Avigad–Carneiro–Hudon) using
only Lean's standard axioms (`propext` and `Quot.sound`).

While Lean 4.34.1 provides native `coinductive_fixpoint` for `Prop`-valued
predicates and relations, `ITree E R` itself is a `Type`-valued greatest fixed
point whose constructors carry continuations `E.O i → ITree E R`. `CoInd P`
furnishes that `Type`-valued terminal coalgebra with exact `@[simp]` unfolding
laws (`unfold_fold`, `fold_unfold`, `unfold_cofix`) and extensional equality
via finite approximations (`approx_eq`).
-/

universe u v

/-- A polynomial container `X ↦ Σ a : A, B a → X`. -/
structure PFunctor : Type (u + 1) where
  /-- Node head shapes. -/
  A : Type u
  /-- Child arity / branching index for head `a`. -/
  B : A → Type u

/-- Apply `P` to carrier `X`. -/
structure PFunctor.Obj (P : PFunctor.{u}) (X : Type v) : Type (max u v) where
  /-- Node head tag. -/
  head : P.A
  /-- Child continuation indexed by `P.B head`. -/
  child : P.B head → X

/-- Functorial action of `P` on `f : X → Y`. -/
def PFunctor.map (P : PFunctor.{u}) {X : Type v} {Y : Type _}
    (f : X → Y) (x : P.Obj X) : P.Obj Y :=
  ⟨x.head, fun b => f (x.child b)⟩

/-- Depth-`n` finite truncation of `P`'s terminal coalgebra. -/
def Approx (P : PFunctor.{u}) : Nat → Type u
  | 0 => PUnit
  | n + 1 => P.Obj (Approx P n)

/-- Project a depth-`(n + 1)` approximation down to depth `n`. -/
def Approx.trunc {P : PFunctor.{u}} :
    {n : Nat} → Approx P (n + 1) → Approx P n
  | 0, _ => PUnit.unit
  | _ + 1, x => ⟨x.head, fun b => trunc (x.child b)⟩

/--
Coinductive M-type (terminal coalgebra) of `P`: projective-limit towers of
finite approximations.
-/
structure CoInd (P : PFunctor.{u}) : Type u where
  /-- Finite truncation at each depth `n`. -/
  approx : (n : Nat) → Approx P n
  /-- Projective coherence between adjacent truncation depths. -/
  coherent : ∀ n, Approx.trunc (approx (n + 1)) = approx n

namespace CoInd

@[ext]
theorem approx_eq {P : PFunctor.{u}} {x y : CoInd P}
    (h : ∀ n, x.approx n = y.approx n) : x = y := by
  cases x; cases y; simp only [mk.injEq]; exact funext h

theorem head_eq {P : PFunctor.{u}} (x : CoInd P) :
    ∀ n, (x.approx (n + 1)).head = (x.approx 1).head
  | 0 => rfl
  | n + 1 => by
    have h := congrArg PFunctor.Obj.head (x.coherent (n + 1))
    exact h.trans (head_eq x n)

/-- Construct `CoInd P` from one unfolded layer. -/
def fold {P : PFunctor.{u}} (v : P.Obj (CoInd P)) : CoInd P where
  approx
    | 0 => PUnit.unit
    | n + 1 => ⟨v.head, fun b => (v.child b).approx n⟩
  coherent
    | 0 => by cases v; rfl
    | n + 1 => by
      dsimp [Approx.trunc]
      congr
      funext b
      exact (v.child b).coherent n

private def childApprox {P : PFunctor.{u}} (x : CoInd P)
    (b : P.B (x.approx 1).head) : (n : Nat) → Approx P n
  | 0 => PUnit.unit
  | n + 1 => (x.approx (n + 2)).child ((head_eq x (n + 1)).symm ▸ b)

private theorem childCoherent {P : PFunctor.{u}} (x : CoInd P)
    (b : P.B (x.approx 1).head) (n : Nat) :
    Approx.trunc (childApprox x b (n + 1)) = childApprox x b n := by
  cases n with
  | zero =>
    cases childApprox x b 0
    rfl
  | succ k =>
    dsimp [childApprox]
    have hEq : ∀ {a₀ : P.A} (b₀ : P.B a₀)
        (y : P.Obj (Approx P (k + 2))) (z : P.Obj (Approx P (k + 1)))
        (hy : Approx.trunc y = z)
        (h₁ : y.head = a₀) (h₂ : z.head = a₀),
        Approx.trunc (y.child (h₁.symm ▸ b₀)) = z.child (h₂.symm ▸ b₀) := by
      intro a₀ b₀ y z hy h₁ h₂
      subst hy
      cases h₁
      have : h₂ = rfl := Subsingleton.elim _ _
      subst this
      rfl
    exact hEq b (x.approx (k + 3)) (x.approx (k + 2))
      (x.coherent (k + 2)) (head_eq x (k + 2)) (head_eq x (k + 1))

/-- Destruct one layer of `x : CoInd P`. -/
def unfold {P : PFunctor.{u}} (x : CoInd P) : P.Obj (CoInd P) where
  head := (x.approx 1).head
  child b := ⟨childApprox x b, childCoherent x b⟩

@[simp]
theorem unfold_fold {P : PFunctor.{u}} (v : P.Obj (CoInd P)) :
    unfold (fold v) = v := by
  cases v with | mk a f =>
  dsimp [unfold, fold]
  congr
  funext b
  apply approx_eq
  intro n
  cases n <;> rfl

@[simp]
theorem fold_unfold {P : PFunctor.{u}} (x : CoInd P) :
    fold (unfold x) = x := by
  apply approx_eq
  intro n
  cases n with
  | zero => cases x.approx 0; rfl
  | succ k =>
    cases k with
    | zero =>
      have hObj : ∀ (z : P.Obj (Approx P 0)),
          (⟨z.head, fun _ => PUnit.unit⟩ : P.Obj (Approx P 0)) = z := by
        intro ⟨_, _⟩; rfl
      exact hObj (x.approx 1)
    | succ k' =>
      have hObj : ∀ {a₀ : P.A} (z : P.Obj (Approx P (k' + 1)))
          (hz : z.head = a₀),
          (⟨a₀, fun b => z.child (hz.symm ▸ b)⟩ : P.Obj (Approx P (k' + 1))) =
            z := by
        intro a₀ ⟨a, ch⟩ hz
        cases hz
        rfl
      exact hObj (x.approx (k' + 2)) (head_eq x (k' + 1))

private def cofixApprox {P : PFunctor.{u}} {X : Type v}
    (step : X → P.Obj X) : (n : Nat) → X → Approx P n
  | 0, _ => PUnit.unit
  | n + 1, s => ⟨(step s).head, fun b => cofixApprox step n ((step s).child b)⟩

private theorem cofixCoherent {P : PFunctor.{u}} {X : Type v}
    (step : X → P.Obj X) :
    ∀ n (s : X),
      Approx.trunc (cofixApprox step (n + 1) s) = cofixApprox step n s
  | 0, _ => rfl
  | n + 1, s => by
    dsimp [cofixApprox, Approx.trunc]
    congr
    funext b
    exact cofixCoherent step n ((step s).child b)

/-- Terminal coalgebra anamorphism: unfold `step : X → P.Obj X` into `CoInd P`. -/
def cofix {P : PFunctor.{u}} {X : Type v}
    (step : X → P.Obj X) (s₀ : X) : CoInd P :=
  ⟨fun n => cofixApprox step n s₀, fun n => cofixCoherent step n s₀⟩

@[simp]
theorem unfold_cofix {P : PFunctor.{u}} {X : Type v}
    (step : X → P.Obj X) (s : X) :
    unfold (cofix step s) = P.map (cofix step) (step s) := by
  dsimp [unfold, cofix, cofixApprox, PFunctor.map]
  congr
  funext b
  apply approx_eq
  intro n
  cases n <;> rfl

end CoInd

end Trusted.CoInd
