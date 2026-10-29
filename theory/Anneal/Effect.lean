import Trusted

namespace Anneal.Effect

open Trusted.Effect

/-!
Derived open-effect algebra (`Subeffect.comp`, `EffectHom`, and fault/inhabited
transport lemmas) built on `Trusted.Effect` (`#100`, `#103`).
-/

universe u

/-- Explicit transitive composition of subeffect inclusions `E₁ -< E₂ -< E₃`. -/
@[instance_reducible]
def Subeffect.comp (E₁ E₂ E₃ : Effect.{u})
    [s₁₂ : Subeffect E₁ E₂] [s₂₃ : Subeffect E₂ E₃] : Subeffect E₁ E₃ where
  injReq i := s₂₃.injReq (s₁₂.injReq i)
  projAns i o := s₁₂.projAns i (s₂₃.projAns (s₁₂.injReq i) o)
  injAns i o := s₂₃.injAns (s₁₂.injReq i) (s₁₂.injAns i o)

theorem Subeffect.comp_lawful (E₁ E₂ E₃ : Effect.{u})
    [s₁₂ : Subeffect E₁ E₂] [s₂₃ : Subeffect E₂ E₃]
    [FaultEffect E₁] [FaultEffect E₂] [FaultEffect E₃]
    [l₁₂ : LawfulSubeffect E₁ E₂] [l₂₃ : LawfulSubeffect E₂ E₃] :
    @LawfulSubeffect E₁ E₃ (Subeffect.comp E₁ E₂ E₃) _ _ :=
  letI := Subeffect.comp E₁ E₂ E₃
  { projAns_injAns := fun i o =>
      (congrArg (s₁₂.projAns i) (l₂₃.projAns_injAns (s₁₂.injReq i) (s₁₂.injAns i o))).trans
        (l₁₂.projAns_injAns i o)
    injAns_projAns := fun i o =>
      (congrArg (s₂₃.injAns (s₁₂.injReq i)) (l₁₂.injAns_projAns i (s₂₃.projAns (s₁₂.injReq i) o))).trans
        (l₂₃.injAns_projAns (s₁₂.injReq i) o)
    injReq_inj := fun h => l₁₂.injReq_inj (l₂₃.injReq_inj h)
    isFault_injReq := fun i =>
      (l₂₃.isFault_injReq (s₁₂.injReq i)).trans (l₁₂.isFault_injReq i) }

/--
Container morphism between open effect signatures `E₁ → E₂` (covariant on
requests, contravariant on answers). Every `Subeffect E₁ E₂` induces an
`EffectHom E₁ E₂`.
-/
structure EffectHom (E₁ E₂ : Effect.{u}) : Type u where
  onReq : E₁.I → E₂.I
  onAns : (i : E₁.I) → E₂.O (onReq i) → E₁.O i

namespace EffectHom

/-- Identity effect morphism. -/
def id (E : Effect.{u}) : EffectHom E E :=
  ⟨fun i => i, fun _ o => o⟩

/-- Compose `f : E₁ → E₂` with `g : E₂ → E₃`. -/
def comp {E₁ E₂ E₃ : Effect.{u}}
    (g : EffectHom E₂ E₃) (f : EffectHom E₁ E₂) : EffectHom E₁ E₃ :=
  ⟨fun i => g.onReq (f.onReq i), fun i o => f.onAns i (g.onAns (f.onReq i) o)⟩

/-- Induced morphism from `[Subeffect Sub Sup]`. -/
def ofSubeffect (Sub Sup : Effect.{u}) [Subeffect Sub Sup] :
    EffectHom Sub Sup :=
  ⟨Subeffect.injReq, Subeffect.projAns⟩

/-- Universal coproduct pairing `(E₁ → E₃) → (E₂ → E₃) → (SumE E₁ E₂ → E₃)`. -/
def sum {E₁ E₂ E₃ : Effect.{u}}
    (f₁ : EffectHom E₁ E₃) (f₂ : EffectHom E₂ E₃) :
    EffectHom (SumE E₁ E₂) E₃ where
  onReq := Sum.elim f₁.onReq f₂.onReq
  onAns
    | .inl i₁, o => f₁.onAns i₁ o
    | .inr i₂, o => f₂.onAns i₂ o

end EffectHom

end Anneal.Effect
