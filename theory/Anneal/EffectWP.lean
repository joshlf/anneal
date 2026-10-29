import Trusted
import Anneal.Effect

namespace Anneal.EffectWP

open Trusted.Effect
open Anneal.Effect

/-!
Open Dijkstra predicate-transformer algebras (`StateEffectWP` and `EffectWP`)
over extensible effect signatures (`#100`, `#103`; cf. `AeneasVerif/aeneas#1180`,
`#1344`).

Each effect signature `E : Effect` carries a modular one-step monotone predicate
transformer `StateEffectWP S E` interpreting requests `i : E.I` and continuation
postconditions `Q : E.O i → S → Prop` over logical state `S`. Monotonicity is
bundled directly in `StateEffectWP` and registered with Lean's
`@[partial_fixpoint_monotone]` machinery so both `coinductive_fixpoint` (`DWLP`)
and `inductive_fixpoint` (`DWP`) work natively over open effect rows.

Horizontal composition (`StateEffectWP.sum`) combines transformers across
`SumE E₁ E₂` while preserving Dijkstra's healthiness laws (`Conjunctive`,
`ExcludedMiracle`, `Disjunctive`) and operational adequacy (`PureSoundWP`).
-/

universe u v

/--
Monotone stateful one-step Dijkstra predicate transformer for an open effect
signature `E : Effect.{u}` over logical state `S : Type u`.
-/
structure StateEffectWP (S : Type u) (E : Effect.{u}) : Type (u + 1) where
  /-- One-step transformer for request `i`, continuation `Q`, and state `s`. -/
  wp : (i : E.I) → (E.O i → S → Prop) → S → Prop
  /-- Continuation monotonicity healthiness law. -/
  mono : ∀ {i : E.I} {P Q : E.O i → S → Prop} {s : S},
    (∀ o s', P o s' → Q o s') → wp i P s → wp i Q s

/-- Stateless one-step Dijkstra predicate transformer for `E : Effect.{u}`. -/
abbrev EffectWP (E : Effect.{u}) : Type (u + 1) :=
  StateEffectWP PUnit.{u + 1} E

/-- Construct a stateless `EffectWP E` from a pure monotone transformer. -/
def EffectWP.mkPure {E : Effect.{u}}
    (f : (i : E.I) → (E.O i → Prop) → Prop)
    (hf : ∀ {i : E.I} {P Q : E.O i → Prop}, (∀ o, P o → Q o) → f i P → f i Q) :
    EffectWP E where
  wp i Q _ := f i (fun o => Q o PUnit.unit)
  mono h := hf (fun o => h o PUnit.unit)

@[partial_fixpoint_monotone]
theorem StateEffectWP.monotone_ind {S : Type u} {E : Effect.{u}}
    (ewp : StateEffectWP S E) {α : Type v} [Lean.Order.PartialOrder α]
    (i : E.I) (s : S)
    (f : α → E.O i → S → Lean.Order.ImplicationOrder)
    (hf : Lean.Order.monotone f) :
    @Lean.Order.monotone _ _ _ Lean.Order.ImplicationOrder.instOrder
      (fun x => ewp.wp i (f x) s) :=
  fun x y hxy h => ewp.mono (fun o s' ho => hf x y hxy o s' ho) h

@[partial_fixpoint_monotone]
theorem StateEffectWP.monotone_coind {S : Type u} {E : Effect.{u}}
    (ewp : StateEffectWP S E) {α : Type v} [Lean.Order.PartialOrder α]
    (i : E.I) (s : S)
    (f : α → E.O i → S → Lean.Order.ReverseImplicationOrder)
    (hf : Lean.Order.monotone f) :
    @Lean.Order.monotone _ _ _ Lean.Order.ReverseImplicationOrder.instOrder
      (fun x => ewp.wp i (f x) s) :=
  fun x y hxy h => ewp.mono (fun o s' ho => hf x y hxy o s' ho) h

/-! ## 1. Dijkstra Healthiness & Operational Soundness Typeclasses -/

/--
Positive conjunctivity (`wp i P ∧ wp i Q → wp i (P ∧ Q)`), characteristic of
deterministic and demonic (`∀`) effect interpretations.
-/
class StateEffectWP.Conjunctive
    {S : Type u} {E : Effect.{u}} (ewp : StateEffectWP S E) : Prop where
  conj : ∀ {i : E.I} {P Q : E.O i → S → Prop} {s : S},
    ewp.wp i P s → ewp.wp i Q s → ewp.wp i (fun o s' => P o s' ∧ Q o s') s

/--
Dijkstra's Law of the Excluded Miracle (`¬ wp i False`), ruling out miraculous
empty demonic choices (`stuck` / `⊥`) in total-correctness proofs.
-/
class StateEffectWP.ExcludedMiracle
    {S : Type u} {E : Effect.{u}} (ewp : StateEffectWP S E) : Prop where
  no_miracle : ∀ {i : E.I} {s : S}, ¬ ewp.wp i (fun _ _ => False) s

/--
Positive disjunctivity (`wp i (P ∨ Q) → wp i P ∨ wp i Q`), characteristic of
deterministic and angelic (`∃`) effect interpretations.
-/
class StateEffectWP.Disjunctive
    {S : Type u} {E : Effect.{u}} (ewp : StateEffectWP S E) : Prop where
  disj : ∀ {i : E.I} {P Q : E.O i → S → Prop} {s : S},
    ewp.wp i (fun o s' => P o s' ∨ Q o s') s → ewp.wp i P s ∨ ewp.wp i Q s

/--
Operational adequacy for stateless `EffectWP E`: satisfying `ewp.wp i Q ()`
guarantees `¬ FaultEffect.isFault i` and `∀ o, Q o ()`.
-/
class PureSoundWP
    {E : Effect.{u}} [FaultEffect E] (ewp : EffectWP E) : Prop where
  sound : ∀ {i : E.I} {Q : E.O i → PUnit.{u + 1} → Prop},
    ewp.wp i Q PUnit.unit →
    ¬ FaultEffect.isFault i ∧ ∀ o : E.O i, Q o PUnit.unit

/--
Operational adequacy for event-trace `StateEffectWP (List (Event E)) E`:
satisfying `ewp.wp i Q tr` guarantees `¬ FaultEffect.isFault i` and establishes
`Q o (tr ++ [⟨i, o⟩])` for every answer `o : E.O i`.
-/
class TraceSoundWP
    {E : Effect.{u}} [FaultEffect E]
    (ewp : StateEffectWP (List (Event E)) E) : Prop where
  sound : ∀ {i : E.I} {Q : E.O i → List (Event E) → Prop} {tr : List (Event E)},
    ewp.wp i Q tr →
    ¬ FaultEffect.isFault i ∧ ∀ o : E.O i, Q o (tr ++ [⟨i, o⟩])

/--
Ambient conjunctive stateless `EffectWP E` enabling typeclass-driven `Std.Do.WP`
and `Std.Do.Triple` (`⦃P⦄ prog ⦃Q⦄`) specifications over `ITree E`.
-/
class PureEffectWP (E : Effect.{u}) : Type (u + 1) where
  ewp : EffectWP E
  conj : StateEffectWP.Conjunctive ewp

attribute [instance] PureEffectWP.conj

/-! ## 2. Modular Coproduct Composition Across `SumE` -/

/-- Combine predicate transformers horizontally across `SumE E₁ E₂`. -/
def StateEffectWP.sum {S : Type u} {E₁ E₂ : Effect.{u}}
    (w₁ : StateEffectWP S E₁) (w₂ : StateEffectWP S E₂) :
    StateEffectWP S (SumE E₁ E₂) where
  wp
    | .inl i₁, Q, s => w₁.wp i₁ Q s
    | .inr i₂, Q, s => w₂.wp i₂ Q s
  mono {i} _ _ _ h_imp h_wp :=
    match i with
    | .inl _ => w₁.mono h_imp h_wp
    | .inr _ => w₂.mono h_imp h_wp

instance {S : Type u} {E₁ E₂ : Effect.{u}}
    (w₁ : StateEffectWP S E₁) (w₂ : StateEffectWP S E₂)
    [h₁ : StateEffectWP.Conjunctive w₁] [h₂ : StateEffectWP.Conjunctive w₂] :
    StateEffectWP.Conjunctive (w₁.sum w₂) where
  conj {i} _ _ _ hp hq :=
    match i with
    | .inl _ => h₁.conj hp hq
    | .inr _ => h₂.conj hp hq

instance {S : Type u} {E₁ E₂ : Effect.{u}}
    (w₁ : StateEffectWP S E₁) (w₂ : StateEffectWP S E₂)
    [h₁ : StateEffectWP.ExcludedMiracle w₁]
    [h₂ : StateEffectWP.ExcludedMiracle w₂] :
    StateEffectWP.ExcludedMiracle (w₁.sum w₂) where
  no_miracle {i} _ :=
    match i with
    | .inl _ => h₁.no_miracle
    | .inr _ => h₂.no_miracle

instance {S : Type u} {E₁ E₂ : Effect.{u}}
    (w₁ : StateEffectWP S E₁) (w₂ : StateEffectWP S E₂)
    [h₁ : StateEffectWP.Disjunctive w₁] [h₂ : StateEffectWP.Disjunctive w₂] :
    StateEffectWP.Disjunctive (w₁.sum w₂) where
  disj {i} _ _ _ hpq :=
    match i with
    | .inl _ => h₁.disj hpq
    | .inr _ => h₂.disj hpq

instance {E₁ E₂ : Effect.{u}} [FaultEffect E₁] [FaultEffect E₂]
    (w₁ : EffectWP E₁) (w₂ : EffectWP E₂)
    [h₁ : PureSoundWP w₁] [h₂ : PureSoundWP w₂] :
    PureSoundWP (w₁.sum w₂) where
  sound {i} _ h_wp :=
    match i with
    | .inl _ => h₁.sound h_wp
    | .inr _ => h₂.sound h_wp

instance {E₁ E₂ : Effect.{u}} [p₁ : PureEffectWP E₁] [p₂ : PureEffectWP E₂] :
    PureEffectWP (SumE E₁ E₂) where
  ewp := p₁.ewp.sum p₂.ewp
  conj := inferInstance

/-! ## 3. Canonical Transformers for Standard Open Effects -/

/-- Predicate transformer for `EmptyE`. -/
def emptyWP (S : Type u) : StateEffectWP S EmptyE.{u} where
  wp i := PEmpty.elim i
  mono {i} := PEmpty.elim i

instance (S : Type u) : StateEffectWP.Conjunctive (emptyWP S) where
  conj {i} := PEmpty.elim i

instance (S : Type u) : StateEffectWP.ExcludedMiracle (emptyWP S) where
  no_miracle {i} := PEmpty.elim i

instance (S : Type u) : StateEffectWP.Disjunctive (emptyWP S) where
  disj {i} := PEmpty.elim i

instance : PureSoundWP (emptyWP PUnit.{u + 1}) where
  sound {i} := PEmpty.elim i

instance : PureEffectWP EmptyE.{u} where
  ewp := emptyWP PUnit.{u + 1}
  conj := inferInstance

/--
Smyth fault transformer for `FailE Err`: every fault evaluates to `False`,
forcing proofs to show fault branches are unreachable.
-/
def failWP (S : Type u) (Err : Type u) : StateEffectWP S (FailE Err) where
  wp _ _ _ := False
  mono _ h := False.elim h

instance (S Err : Type u) : StateEffectWP.Conjunctive (failWP S Err) where
  conj h _ := False.elim h

instance (S Err : Type u) : StateEffectWP.ExcludedMiracle (failWP S Err) where
  no_miracle h := h

instance (S Err : Type u) : StateEffectWP.Disjunctive (failWP S Err) where
  disj h := False.elim h

instance (Err : Type u) : PureSoundWP (failWP PUnit.{u + 1} Err) where
  sound h := False.elim h

instance (Err : Type u) : PureEffectWP (FailE Err) where
  ewp := failWP PUnit.{u + 1} Err
  conj := inferInstance

/-- Trace-ignoring transformer for `ObsE Obs` leaving logical state unchanged. -/
def obsIgnoreWP (S : Type u) (Obs : Type u) : StateEffectWP S (ObsE Obs) where
  wp _ Q s := Q PUnit.unit s
  mono h_imp h_wp := h_imp PUnit.unit _ h_wp

instance (S Obs : Type u) : StateEffectWP.Conjunctive (obsIgnoreWP S Obs) where
  conj hp hq := ⟨hp, hq⟩

instance (S Obs : Type u) :
    StateEffectWP.ExcludedMiracle (obsIgnoreWP S Obs) where
  no_miracle h := h

instance (S Obs : Type u) : StateEffectWP.Disjunctive (obsIgnoreWP S Obs) where
  disj h := h

instance (Obs : Type u) : PureSoundWP (obsIgnoreWP PUnit.{u + 1} Obs) where
  sound h_wp := ⟨fun hf => hf, fun _ => h_wp⟩

instance (Obs : Type u) : PureEffectWP (ObsE Obs) where
  ewp := obsIgnoreWP PUnit.{u + 1} Obs
  conj := inferInstance

/-- Trace-accumulating transformer for `ObsE Obs` over `List Obs`. -/
def obsTraceWP (Obs : Type u) : StateEffectWP (List Obs) (ObsE Obs) where
  wp
    | .emit obs, Q, tr => Q PUnit.unit (tr ++ [obs])
  mono {i} _ _ _ h_imp h_wp :=
    match i with
    | .emit _ => h_imp PUnit.unit _ h_wp

instance (Obs : Type u) : StateEffectWP.Conjunctive (obsTraceWP Obs) where
  conj {i} _ _ _ hp hq := match i with | .emit _ => ⟨hp, hq⟩

instance (Obs : Type u) : StateEffectWP.ExcludedMiracle (obsTraceWP Obs) where
  no_miracle {i} _ h := match i with | .emit _ => h

instance (Obs : Type u) : StateEffectWP.Disjunctive (obsTraceWP Obs) where
  disj {i} _ _ _ h := match i with | .emit _ => h

/--
Demonic choice transformer for `PickE α` (`DemonicE α`): requires `Nonempty α`
together with universal satisfaction `∀ o : α, Q o s`.

Requiring `Nonempty α` enforces `ExcludedMiracle` so `ITree.stuck`
(`PickE PEmpty`) evaluates to `False` rather than vacuously `True`.
-/
def pickWP (S : Type u) (α : Type u) : StateEffectWP S (PickE α) where
  wp _ Q s := Nonempty α ∧ ∀ o : α, Q o s
  mono h_imp h_wp := ⟨h_wp.1, fun o => h_imp o _ (h_wp.2 o)⟩

abbrev demonicWP (S : Type u) (α : Type u) : StateEffectWP S (DemonicE α) :=
  pickWP S α

instance (S α : Type u) : StateEffectWP.Conjunctive (pickWP S α) where
  conj hp hq := ⟨hp.1, fun o => ⟨hp.2 o, hq.2 o⟩⟩

instance (S α : Type u) : StateEffectWP.ExcludedMiracle (pickWP S α) where
  no_miracle h_wp := let ⟨o⟩ := h_wp.1; h_wp.2 o

instance (α : Type u) : PureSoundWP (pickWP PUnit.{u + 1} α) where
  sound h_wp := ⟨fun hf => hf, h_wp.2⟩

instance (α : Type u) : PureEffectWP (PickE α) where
  ewp := pickWP PUnit.{u + 1} α
  conj := inferInstance

/-- Demonic choice over `Bool` is not disjunctive (`∀` does not distribute over `∨`). -/
theorem not_disjunctive_pickBool :
    ¬ StateEffectWP.Disjunctive (pickWP PUnit.{1} Bool) := by
  intro h_disj
  have h_or : (pickWP PUnit.{1} Bool).wp .pick
      (fun b _ => b = true ∨ b = false) PUnit.unit :=
    ⟨⟨true⟩, fun | true => .inl rfl | false => .inr rfl⟩
  rcases h_disj.disj h_or with ht | hf
  · exact Bool.noConfusion (ht.2 false)
  · exact Bool.noConfusion (hf.2 true)

/--
Angelic witness transformer for `WitnessE α` (`AngelicE α`): requires a concrete
witness `o : α` establishing `Q o s`.
-/
def witnessWP (S : Type u) (α : Type u) : StateEffectWP S (WitnessE α) where
  wp _ Q s := ∃ o : α, Q o s
  mono h_imp | ⟨o, ho⟩ => ⟨o, h_imp o _ ho⟩

abbrev angelicWP (S : Type u) (α : Type u) : StateEffectWP S (AngelicE α) :=
  witnessWP S α

instance (S α : Type u) : StateEffectWP.ExcludedMiracle (witnessWP S α) where
  no_miracle | ⟨_, h⟩ => h

instance (S α : Type u) : StateEffectWP.Disjunctive (witnessWP S α) where
  disj
    | ⟨o, .inl hp⟩ => .inl ⟨o, hp⟩
    | ⟨o, .inr hq⟩ => .inr ⟨o, hq⟩

/-- Angelic choice over `Bool` is not conjunctive (`∃` does not distribute over `∧`). -/
theorem not_conjunctive_witnessBool :
    ¬ StateEffectWP.Conjunctive (witnessWP PUnit.{1} Bool) := by
  intro h_conj
  have ht : (witnessWP PUnit.{1} Bool).wp .witness (fun b _ => b = true) PUnit.unit :=
    ⟨true, rfl⟩
  have hf : (witnessWP PUnit.{1} Bool).wp .witness (fun b _ => b = false) PUnit.unit :=
    ⟨false, rfl⟩
  rcases h_conj.conj ht hf with ⟨_, h₁, h₂⟩
  exact Bool.noConfusion (h₁.symm.trans h₂)

/-- Exact state-passing transformer for `StateE S` over logical state `S`. -/
def stateWP (S : Type u) : StateEffectWP S (StateE S) where
  wp
    | .get, Q, s => Q s s
    | .put s', Q, _ => Q PUnit.unit s'
  mono {op} _ _ _ h_imp h_wp :=
    match op with
    | .get => h_imp _ _ h_wp
    | .put _ => h_imp _ _ h_wp

instance (S : Type u) : StateEffectWP.Conjunctive (stateWP S) where
  conj {op} _ _ _ hp hq := match op with | .get => ⟨hp, hq⟩ | .put _ => ⟨hp, hq⟩

instance (S : Type u) : StateEffectWP.ExcludedMiracle (stateWP S) where
  no_miracle {op} _ h := match op with | .get => h | .put _ => h

instance (S : Type u) : StateEffectWP.Disjunctive (stateWP S) where
  disj {op} _ _ _ h := match op with | .get => h | .put _ => h

/--
Impure-by-default unconstrained demonic transformer for external calls
`CallE Req Resp`: requires `Q resp s` for every possible response `resp`.
-/
def unconstrainedCallWP (S : Type u) (Req : Type u) (Resp : Req → Type u) :
    StateEffectWP S (CallE Req Resp) where
  wp
    | .call req, Q, s => ∀ resp : Resp req, Q resp s
  mono {i} _ _ _ h_imp h_wp :=
    match i with
    | .call _ => fun resp => h_imp resp _ (h_wp resp)

instance (S Req : Type u) (Resp : Req → Type u) :
    StateEffectWP.Conjunctive (unconstrainedCallWP S Req Resp) where
  conj {i} _ _ _ hp hq :=
    match i with
    | .call _ => fun resp => ⟨hp resp, hq resp⟩

instance (S Req : Type u) (Resp : Req → Type u)
    [h_ne : ∀ r : Req, Nonempty (Resp r)] :
    StateEffectWP.ExcludedMiracle (unconstrainedCallWP S Req Resp) where
  no_miracle {i} _ h_wp :=
    match i with
    | .call r => let ⟨resp⟩ := h_ne r; h_wp resp

instance (Req : Type u) (Resp : Req → Type u) :
    PureSoundWP (unconstrainedCallWP PUnit.{u + 1} Req Resp) where
  sound {i} _ h_wp :=
    match i with
    | .call _ => ⟨fun hf => hf, h_wp⟩

instance (Req : Type u) (Resp : Req → Type u) :
    PureEffectWP (CallE Req Resp) where
  ewp := unconstrainedCallWP PUnit.{u + 1} Req Resp
  conj := inferInstance

/-- Relational pre/post specification for external `CallE Req Resp` calls. -/
structure CallContract (Req : Type u) (Resp : Req → Type u) : Type u where
  /-- Caller precondition required at the call site. -/
  pre : Req → Prop
  /-- Rely guarantee relating the call request and callee response. -/
  post : (req : Req) → Resp req → Prop

/-- Contract-guided transformer for `CallE Req Resp`. -/
def contractCallWP (S : Type u) {Req : Type u} {Resp : Req → Type u}
    (C : CallContract Req Resp) : StateEffectWP S (CallE Req Resp) where
  wp
    | .call req, Q, s => C.pre req ∧ ∀ resp : Resp req, C.post req resp → Q resp s
  mono {i} _ _ _ h_imp h_wp :=
    match i with
    | .call _ => ⟨h_wp.1, fun resp hp => h_imp resp _ (h_wp.2 resp hp)⟩

instance (S : Type u) {Req : Type u} {Resp : Req → Type u}
    (C : CallContract Req Resp) :
    StateEffectWP.Conjunctive (contractCallWP S C) where
  conj {i} _ _ _ hp hq :=
    match i with
    | .call _ => ⟨hp.1, fun resp hpost => ⟨hp.2 resp hpost, hq.2 resp hpost⟩⟩

/--
Universal trace-recording transformer for any open effect `E` with
`[FaultEffect E]`: rejects fault requests (`¬ FaultEffect.isFault i`) and
appends `⟨i, o⟩` onto `List (Event E)`.
-/
def eventTraceWP (E : Effect.{u}) [FaultEffect E] :
    StateEffectWP (List (Event E)) E where
  wp i Q tr :=
    ¬ FaultEffect.isFault i ∧ ∀ o : E.O i, Q o (tr ++ [⟨i, o⟩])
  mono h_imp h_wp := ⟨h_wp.1, fun o => h_imp o _ (h_wp.2 o)⟩

instance (E : Effect.{u}) [FaultEffect E] :
    StateEffectWP.Conjunctive (eventTraceWP E) where
  conj hp hq := ⟨hp.1, fun o => ⟨hp.2 o, hq.2 o⟩⟩

instance (E : Effect.{u}) [FaultEffect E] :
    TraceSoundWP (eventTraceWP E) where
  sound h_wp := h_wp

end Anneal.EffectWP
