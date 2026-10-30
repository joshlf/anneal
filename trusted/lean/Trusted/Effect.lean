namespace Trusted.Effect

/-!
Open effect signatures, ownership disciplines, fault classification, and
extensible effect-row combinators for Layer 1B of Anneal's interaction-tree
architecture (`#100`, `#103`).

An `Effect` specifies an open dialogue interface `(I, O)` where `I` is the type
of requests and `O i` is the dependent type of answers for `i : I`. Output
observations (`ObsE`), operational faults (`FailE`), demonic environment
nondeterminism (`PickE`), angelic prover witnesses (`WitnessE`), state
operations (`StateE`), and external calls (`CallE`) are all ordinary `Effect`
values composed horizontally via `SumE` and injected polymorphically via
`Subeffect`.

`FaultEffect` separates operational faults (`FailE`, which act as the Smyth top
element `⊤`) from empty demonic choices (`PickE PEmpty`, i.e. `stuck`, which
act as the miraculous bottom element `⊥`), even though both have uninhabited
answer types.
-/

universe u v

/-- Who selects the answer `o : E.O i` to request `i : E.I`. -/
inductive ChoiceKind : Type where
  /-- Universal branching: the environment chooses `o : E.O i`. -/
  | demonic
  /-- Existential branching: the prover exhibits a witness `o : E.O i`. -/
  | angelic
  deriving DecidableEq, Repr, Inhabited

/-- Defined halting outcomes of a terminating execution (distinct from UB). -/
inductive Outcome (Val : Type u) : Type u where
  /-- Normal completion yielding `val`. -/
  | normal (val : Val)
  /-- Defined unwinding / panic without a normal return value. -/
  | panic
  /-- Defined immediate process termination without unwinding. -/
  | abort
  deriving DecidableEq, Repr

/-- Map `f` over a normal outcome payload, preserving `panic` and `abort`. -/
def Outcome.map {Val₁ : Type u} {Val₂ : Type v}
    (f : Val₁ → Val₂) : Outcome Val₁ → Outcome Val₂
  | .normal v => .normal (f v)
  | .panic => .panic
  | .abort => .abort

/-- Operational fault categories emitted via `FailE FailureKind`. -/
inductive FailureKind : Type where
  /-- Undefined behavior: the program violated an operational precondition. -/
  | ub
  /-- Unmodeled construct: fail-closed semantic boundary. -/
  | unsupported
  /-- Step budget exhausted during bounded evaluation. -/
  | outOfFuel
  deriving DecidableEq, Repr, Inhabited

/-- Open polynomial container of effect requests `I` and dependent answers `O`. -/
structure Effect : Type (u + 1) where
  /-- Request / operation type emitted by the computation. -/
  I : Type u
  /-- Answer / response type returned for each request. -/
  O : I → Type u

/-- Completed `(request, answer)` interaction event. -/
structure Event (E : Effect.{u}) : Type u where
  /-- Emitted request. -/
  req : E.I
  /-- Environment or witness answer. -/
  ans : E.O req

/-- Quantifier ownership discipline for each operation of `E`. -/
class EffectOwner (E : Effect.{u}) where
  /-- Whether `i` is answered demonically or angelically. -/
  owner : E.I → ChoiceKind := fun _ => .demonic

/--
Classification of requests in `E` that represent immediate operational faults
(undefined behavior or unsupported constructs) rather than genuine dialogue.
-/
class FaultEffect (E : Effect.{u}) where
  /-- Holds when emitting `i` is an operational fault (`⊤` in Smyth order). -/
  isFault : E.I → Prop := fun _ => False

/--
Excludes miraculous empty non-fault interactions (`stuck`): every non-fault
request of `E` admits at least one possible answer.
-/
class InhabitedDemonic (E : Effect.{u}) [FaultEffect E] : Prop where
  /-- Every non-fault request has a nonempty answer type. -/
  nonempty_of_nonFault : ∀ i : E.I, ¬ FaultEffect.isFault (E := E) i →
    Nonempty (E.O i)

/-! ## Standard Open-Effect Building Blocks -/

/-- Pure effect with no operations (`EmptyE`). -/
def EmptyE : Effect.{u} where
  I := PEmpty
  O := PEmpty.elim

instance : EffectOwner EmptyE.{u} where
  owner := PEmpty.elim

instance : FaultEffect EmptyE.{u} where
  isFault := PEmpty.elim

instance : InhabitedDemonic EmptyE.{u} where
  nonempty_of_nonFault i := PEmpty.elim i

/-- Coproduct (row sum) of two open effect signatures `E₁ ⊕ E₂`. -/
def SumE (E₁ E₂ : Effect.{u}) : Effect.{u} where
  I := E₁.I ⊕ E₂.I
  O := Sum.elim E₁.O E₂.O

instance [EffectOwner E₁] [EffectOwner E₂] : EffectOwner (SumE E₁ E₂) where
  owner := Sum.elim EffectOwner.owner EffectOwner.owner

instance [FaultEffect E₁] [FaultEffect E₂] : FaultEffect (SumE E₁ E₂) where
  isFault := Sum.elim FaultEffect.isFault FaultEffect.isFault

instance [FaultEffect E₁] [FaultEffect E₂]
    [InhabitedDemonic E₁] [InhabitedDemonic E₂] :
    InhabitedDemonic (SumE E₁ E₂) where
  nonempty_of_nonFault
    | .inl i₁, h => InhabitedDemonic.nonempty_of_nonFault (E := E₁) i₁ h
    | .inr i₂, h => InhabitedDemonic.nonempty_of_nonFault (E := E₂) i₂ h

/-- Request wrapper for operational faults `FailE Err`. -/
inductive FailReq (Err : Type u) : Type u where
  | fail (err : Err)
  deriving DecidableEq, Repr

/-- Operational fault effect (`O _ = PEmpty`, `isFault _ = True`). -/
def FailE (Err : Type u) : Effect.{u} where
  I := FailReq Err
  O _ := PEmpty

instance {Err : Type u} : EffectOwner (FailE Err) where
  owner _ := .angelic

instance {Err : Type u} : FaultEffect (FailE Err) where
  isFault _ := True

instance {Err : Type u} : InhabitedDemonic (FailE Err) where
  nonempty_of_nonFault _ h := False.elim (h trivial)

/-- Request wrapper for output observations `ObsE Ev`. -/
inductive ObsReq (Ev : Type u) : Type u where
  | emit (ev : Ev)
  deriving DecidableEq, Repr

/-- Output observation effect (`O _ = PUnit`, `isFault _ = False`). -/
def ObsE (Ev : Type u) : Effect.{u} where
  I := ObsReq Ev
  O _ := PUnit

instance {Ev : Type u} : EffectOwner (ObsE Ev) where
  owner _ := .demonic

instance {Ev : Type u} : FaultEffect (ObsE Ev) where
  isFault _ := False

instance {Ev : Type u} : InhabitedDemonic (ObsE Ev) where
  nonempty_of_nonFault _ _ := ⟨PUnit.unit⟩

/-- Request wrapper for demonic nondeterministic choice `PickE α`. -/
inductive PickReq (α : Type u) : Type u where
  | pick
  deriving DecidableEq, Repr

/-- Demonic nondeterministic choice (`PickE α` / `DemonicE α`). -/
def PickE (α : Type u) : Effect.{u} where
  I := PickReq α
  O _ := α

abbrev DemonicE (α : Type u) : Effect.{u} := PickE α

instance {α : Type u} : EffectOwner (PickE α) where
  owner _ := .demonic

instance {α : Type u} : FaultEffect (PickE α) where
  isFault _ := False

instance {α : Type u} [h : Nonempty α] : InhabitedDemonic (PickE α) where
  nonempty_of_nonFault _ _ := h

/-- Request wrapper for angelic prover witnesses `WitnessE α`. -/
inductive WitnessReq (α : Type u) : Type u where
  | witness
  deriving DecidableEq, Repr

/-- Angelic nondeterministic witness selection (`WitnessE α` / `AngelicE α`). -/
def WitnessE (α : Type u) : Effect.{u} where
  I := WitnessReq α
  O _ := α

abbrev AngelicE (α : Type u) : Effect.{u} := WitnessE α

instance {α : Type u} : EffectOwner (WitnessE α) where
  owner _ := .angelic

instance {α : Type u} : FaultEffect (WitnessE α) where
  isFault _ := False

instance {α : Type u} [h : Nonempty α] : InhabitedDemonic (WitnessE α) where
  nonempty_of_nonFault _ _ := h

/-- Request wrapper for external / unlinked procedure calls `CallE Req Ans`. -/
inductive CallReq (Req : Type u) : Type u where
  | call (req : Req)
  deriving DecidableEq, Repr

/-- External / FFI call effect with dependent response type `Ans`. -/
def CallE (Req : Type u) (Ans : Req → Type u) : Effect.{u} where
  I := CallReq Req
  O | .call r => Ans r

instance {Req : Type u} {Ans : Req → Type u} :
    EffectOwner (CallE Req Ans) where
  owner _ := .demonic

instance {Req : Type u} {Ans : Req → Type u} :
    FaultEffect (CallE Req Ans) where
  isFault _ := False

instance {Req : Type u} {Ans : Req → Type u} [h : ∀ r, Nonempty (Ans r)] :
    InhabitedDemonic (CallE Req Ans) where
  nonempty_of_nonFault | .call r, _ => h r

/-- Mutable state request (`get` or `put s`). -/
inductive StateReq (S : Type u) : Type u where
  | get
  | put (s : S)
  deriving DecidableEq, Repr

/-- Mutable state effect `StateE S`. -/
def StateE (S : Type u) : Effect.{u} where
  I := StateReq S
  O
    | .get => S
    | .put _ => PUnit

instance {S : Type u} : EffectOwner (StateE S) where
  owner _ := .demonic

instance {S : Type u} : FaultEffect (StateE S) where
  isFault _ := False

instance {S : Type u} [h : Nonempty S] : InhabitedDemonic (StateE S) where
  nonempty_of_nonFault
    | .get, _ => h
    | .put _, _ => ⟨PUnit.unit⟩

/-! ## Open Effect Inclusion (`Subeffect`, `LawfulSubeffect`) -/

/--
Direct summand inclusion `Sub -< Sup`, embedding requests of `Sub` into `Sup`
with an isomorphism between `Sup.O (injReq i)` and `Sub.O i`.
-/
class Subeffect (Sub Sup : Effect.{u}) where
  /-- Inject a subeffect request into `Sup`. -/
  injReq : Sub.I → Sup.I
  /-- Project a `Sup` answer back to `Sub`. -/
  projAns : (i : Sub.I) → Sup.O (injReq i) → Sub.O i
  /-- Embed a `Sub` answer into `Sup`. -/
  injAns : (i : Sub.I) → Sub.O i → Sup.O (injReq i)

/-- Lift a completed `Event Sub` into `Event Sup`. -/
def Subeffect.liftEvent {Sub Sup : Effect.{u}} [Subeffect Sub Sup]
    (ev : Event Sub) : Event Sup :=
  ⟨Subeffect.injReq ev.req, Subeffect.injAns ev.req ev.ans⟩

/-- Well-behaved subeffect embedding preserving answers and fault status. -/
class LawfulSubeffect (Sub Sup : Effect.{u})
    [Subeffect Sub Sup] [FaultEffect Sub] [FaultEffect Sup] : Prop where
  projAns_injAns : ∀ (i : Sub.I) (o : Sub.O i),
    Subeffect.projAns (Sup := Sup) i (Subeffect.injAns i o) = o
  injAns_projAns : ∀ (i : Sub.I) (o : Sup.O (Subeffect.injReq i)),
    Subeffect.injAns i (Subeffect.projAns (Sup := Sup) i o) = o
  injReq_inj : ∀ {i₁ i₂ : Sub.I},
    Subeffect.injReq (Sup := Sup) i₁ = Subeffect.injReq i₂ → i₁ = i₂
  isFault_injReq : ∀ i : Sub.I,
    FaultEffect.isFault (Subeffect.injReq (Sup := Sup) i) ↔
      FaultEffect.isFault i

instance (priority := 90) instSubeffectRefl (E : Effect.{u}) :
    Subeffect E E where
  injReq i := i
  projAns _ o := o
  injAns _ o := o

instance (priority := 90) instLawfulSubeffectRefl (E : Effect.{u})
    [FaultEffect E] : LawfulSubeffect E E where
  projAns_injAns _ _ := rfl
  injAns_projAns _ _ := rfl
  injReq_inj h := h
  isFault_injReq _ := Iff.rfl

instance (priority := 100) instSubeffectSumLeft (E₁ E₂ : Effect.{u}) :
    Subeffect E₁ (SumE E₁ E₂) where
  injReq := Sum.inl
  projAns _ o := o
  injAns _ o := o

instance (priority := 100) instLawfulSubeffectSumLeft (E₁ E₂ : Effect.{u})
    [FaultEffect E₁] [FaultEffect E₂] :
    LawfulSubeffect E₁ (SumE E₁ E₂) where
  projAns_injAns _ _ := rfl
  injAns_projAns _ _ := rfl
  injReq_inj h := Sum.inl.inj h
  isFault_injReq _ := Iff.rfl

instance (priority := 80) instSubeffectSumRight (E E₁ E₂ : Effect.{u})
    [Subeffect E E₂] : Subeffect E (SumE E₁ E₂) where
  injReq i := .inr (Subeffect.injReq (Sup := E₂) i)
  projAns i o := Subeffect.projAns (Sup := E₂) i o
  injAns i o := Subeffect.injAns (Sup := E₂) i o

instance (priority := 80) instLawfulSubeffectSumRight (E E₁ E₂ : Effect.{u})
    [Subeffect E E₂] [FaultEffect E] [FaultEffect E₁] [FaultEffect E₂]
    [LawfulSubeffect E E₂] :
    LawfulSubeffect E (SumE E₁ E₂) where
  projAns_injAns := LawfulSubeffect.projAns_injAns (Sub := E) (Sup := E₂)
  injAns_projAns := LawfulSubeffect.injAns_projAns (Sub := E) (Sup := E₂)
  injReq_inj h :=
    LawfulSubeffect.injReq_inj (Sub := E) (Sup := E₂) (Sum.inr.inj h)
  isFault_injReq := LawfulSubeffect.isFault_injReq (Sub := E) (Sup := E₂)

end Trusted.Effect
