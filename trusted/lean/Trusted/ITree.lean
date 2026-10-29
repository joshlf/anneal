import Trusted.Refinement
import Trusted.CoInd
import Trusted.Effect

namespace Trusted.ITree

open Trusted.Refinement
open Trusted.CoInd
open Trusted.Effect

/-!
Fundamental coinductive interaction trees (`ITree E R`), monadic combinators,
effect handlers (`interp`, `interpState`), and denotational projections into
Layer 1A's Smyth `Partial` domain (`toPartial`, `toPrefixPartial`, `#100`,
`#103`).

Only definitions needed to state root semantics and `VerificationResult`
claims live here in `trusted/lean/`. All bisimulations (`StrongBisim`, `Eutt`),
the 2×2 Smyth refinement lattice (`WeakRef`, `TotalWeakRef`, `WeakSim`,
`WeakCSim`), `LawfulMonad`, temporal/stream liveness modalities, `EnvStrategy`,
`BridgeContract`, and Dijkstra weakest-precondition calculi (`DWLP`, `DWP`)
live outside the trusted base in `theory/Anneal/`.
-/

universe u

/-- One-layer polynomial functor shape of an interaction tree. -/
inductive ITreeF (E : Effect.{u}) (R : Type u) (X : Type u) : Type u where
  /-- Pure termination returning `r : R`. -/
  | ret (r : R)
  /-- Silent internal computation step continuing at `t : X`. -/
  | tau (t : X)
  /-- Visible interaction emitting `i : E.I` and branching on `o : E.O i`. -/
  | vis (i : E.I) (k : E.O i → X)

/-- Map `f` across child continuations of `ITreeF`. -/
def ITreeF.map {E : Effect.{u}} {R X Y : Type u}
    (f : X → Y) : ITreeF E R X → ITreeF E R Y
  | .ret r => .ret r
  | .tau t => .tau (f t)
  | .vis i k => .vis i (fun o => f (k o))

private inductive ITreeHead (E : Effect.{u}) (R : Type u) : Type u where
  | ret (r : R)
  | tau
  | vis (i : E.I)

/-- Polynomial container encoding `ITreeF E R`. -/
def ITreeP (E : Effect.{u}) (R : Type u) : PFunctor.{u} where
  A := ITreeHead E R
  B
    | .ret _ => PEmpty
    | .tau => PUnit
    | .vis i => E.O i

private def toObj {E : Effect.{u}} {R X : Type u} :
    ITreeF E R X → (ITreeP E R).Obj X
  | .ret r => ⟨.ret r, PEmpty.elim⟩
  | .tau t => ⟨.tau, fun _ => t⟩
  | .vis i k => ⟨.vis i, k⟩

private def ofObj {E : Effect.{u}} {R X : Type u} :
    (ITreeP E R).Obj X → ITreeF E R X
  | ⟨.ret r, _⟩ => .ret r
  | ⟨.tau, ch⟩ => .tau (ch PUnit.unit)
  | ⟨.vis i, ch⟩ => .vis i ch

/--
Coinductive interaction tree over open effect signature `E` and return type `R`.
-/
def ITree (E : Effect.{u}) (R : Type u) : Type u :=
  CoInd (ITreeP E R)

namespace ITree

/-- Observe one unfolded `ITreeF` layer of `t`. -/
def observe {E : Effect.{u}} {R : Type u} (t : ITree E R) :
    ITreeF E R (ITree E R) :=
  ofObj (CoInd.unfold t)

/-- Fold one `ITreeF` layer into `ITree E R`. -/
def fold {E : Effect.{u}} {R : Type u}
    (node : ITreeF E R (ITree E R)) : ITree E R :=
  CoInd.fold (toObj node)

/-- Terminal leaf returning `r`. -/
def ret {E : Effect.{u}} {R : Type u} (r : R) : ITree E R :=
  fold (.ret r)

/-- Silent internal transition `.tau t`. -/
def tau {E : Effect.{u}} {R : Type u} (t : ITree E R) : ITree E R :=
  fold (.tau t)

/-- Visible effect interaction `.vis i k`. -/
def vis {E : Effect.{u}} {R : Type u}
    (i : E.I) (k : E.O i → ITree E R) : ITree E R :=
  fold (.vis i k)

/-- Unfold a coalgebra `step : S → ITreeF E R S` from initial state `s`. -/
def cofix {E : Effect.{u}} {R S : Type u}
    (step : S → ITreeF E R S) (s : S) : ITree E R :=
  CoInd.cofix (fun x => toObj (step x)) s

@[simp]
theorem observe_fold {E : Effect.{u}} {R : Type u}
    (node : ITreeF E R (ITree E R)) :
    (fold node).observe = node := by
  dsimp [observe, fold]
  rw [CoInd.unfold_fold]
  cases node <;> rfl

@[simp]
theorem fold_observe {E : Effect.{u}} {R : Type u} (t : ITree E R) :
    fold t.observe = t := by
  have h : toObj (ofObj (CoInd.unfold t)) = CoInd.unfold t := by
    rcases CoInd.unfold t with ⟨hd, ch⟩
    cases hd with
    | ret r =>
      dsimp [toObj, ofObj]
      congr; funext x; exact PEmpty.elim x
    | tau => rfl
    | vis i => rfl
  exact (congrArg CoInd.fold h).trans (CoInd.fold_unfold t)

@[simp]
theorem observe_ret {E : Effect.{u}} {R : Type u} (r : R) :
    (ret (E := E) r).observe = .ret r :=
  observe_fold (.ret r)

@[simp]
theorem observe_tau {E : Effect.{u}} {R : Type u} (t : ITree E R) :
    (tau t).observe = .tau t :=
  observe_fold (.tau t)

@[simp]
theorem observe_vis {E : Effect.{u}} {R : Type u}
    (i : E.I) (k : E.O i → ITree E R) :
    (vis i k).observe = .vis i k :=
  observe_fold (.vis i k)

@[simp]
theorem observe_cofix {E : Effect.{u}} {R S : Type u}
    (step : S → ITreeF E R S) (s : S) :
    (cofix step s).observe = (step s).map (cofix step) := by
  dsimp [observe, cofix]
  rw [CoInd.unfold_cofix]
  cases step s <;> rfl

/-! ## Monadic Combinators, Loops, and Effect Handlers -/

/-- Silent infinite loop (`cofix (fun _ => .tau ()) ()`). -/
def spin {E : Effect.{u}} {R : Type u} : ITree E R :=
  cofix (fun _ : PUnit => .tau PUnit.unit) PUnit.unit

/-- Coinductive monadic bind `t >>= k`. -/
def bind {E : Effect.{u}} {R S : Type u}
    (t : ITree E R) (k : R → ITree E S) : ITree E S :=
  cofix
    (fun st : ITree E R ⊕ ITree E S =>
      match st with
      | .inl cur =>
        match cur.observe with
        | .ret r => (k r).observe.map .inr
        | .tau cur' => .tau (.inl cur')
        | .vis i c => .vis i (fun o => .inl (c o))
      | .inr out => out.observe.map .inr)
    (.inl t)

/-- Functorial map across return values. -/
def map {E : Effect.{u}} {R S : Type u}
    (f : R → S) (t : ITree E R) : ITree E S :=
  t.bind (fun r => ret (f r))

instance {E : Effect.{u}} : Monad (ITree E) where
  pure := ret
  bind := bind
  map := map

/-- Perform a single effect request `i : E.I` and return its answer. -/
def trigger {E : Effect.{u}} (i : E.I) : ITree E (E.O i) :=
  vis i ret

/-- Perform a subeffect request `i : Sub.I` inside any larger effect `E`. -/
def triggerSub {Sub E : Effect.{u}} [Subeffect Sub E]
    (i : Sub.I) : ITree E (Sub.O i) :=
  vis (Subeffect.injReq i) (fun o => ret (Subeffect.projAns i o))

/-- Emit an operational fault `err : Err` through `FailE Err -< E`. -/
def fail {Err : Type u} {E : Effect.{u}} {R : Type u}
    [Subeffect (FailE Err) E] (err : Err) : ITree E R := do
  let ans ← triggerSub (Sub := FailE Err) (E := E) (.fail err)
  PEmpty.elim ans

/-- Emit a visible observation `ev : Ev` through `ObsE Ev -< E`. -/
def emit {Ev : Type u} {E : Effect.{u}}
    [Subeffect (ObsE Ev) E] (ev : Ev) : ITree E PUnit :=
  triggerSub (Sub := ObsE Ev) (E := E) (.emit ev)

/-- Demonically choose a value in `α` through `PickE α -< E`. -/
def pick {α : Type u} {E : Effect.{u}}
    [Subeffect (PickE α) E] : ITree E α :=
  triggerSub (Sub := PickE α) (E := E) .pick

/-- Miraculous deadlock (`pick` from `PEmpty`, acting as `⊥` in Smyth order). -/
def stuck {E : Effect.{u}} {R : Type u}
    [Subeffect (PickE PEmpty) E] : ITree E R := do
  let ans ← pick (α := PEmpty) (E := E)
  PEmpty.elim ans

/-- Angelically choose a witness in `α` through `WitnessE α -< E`. -/
def witness {α : Type u} {E : Effect.{u}}
    [Subeffect (WitnessE α) E] : ITree E α :=
  triggerSub (Sub := WitnessE α) (E := E) .witness

/--
Coinductive tail-recursive iteration (`ITree.iter`): runs `body i`, looping via
`.tau` on `.inl next` and returning `r` on `.inr r`.
-/
def iter {E : Effect.{u}} {I R : Type u}
    (body : I → ITree E (I ⊕ R)) (init : I) : ITree E R :=
  cofix
    (fun cur : ITree E (I ⊕ R) =>
      match cur.observe with
      | .ret (.inr r) => .ret r
      | .ret (.inl next) => .tau (body next)
      | .tau cur' => .tau cur'
      | .vis i k => .vis i k)
    (body init)

/-- Internal coalgebra carrier for `ITree.interp`. -/
abbrev InterpCarrier (E₁ E₂ : Effect.{u}) (R : Type u) : Type u :=
  ITree E₁ R ⊕ (Σ i : E₁.I, ITree E₂ (E₁.O i) × (E₁.O i → ITree E₁ R))

/-- Coalgebra step for `ITree.interp`, guarding handler re-entry with `.tau`. -/
def interpStep {E₁ E₂ : Effect.{u}} {R : Type u}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i)) :
    InterpCarrier E₁ E₂ R → ITreeF E₂ R (InterpCarrier E₁ E₂ R)
  | .inl t =>
    match t.observe with
    | .ret r => .ret r
    | .tau t' => .tau (.inl t')
    | .vis i k =>
      match (h i).observe with
      | .ret o => .tau (.inl (k o))
      | .tau u' => .tau (.inr ⟨i, u', k⟩)
      | .vis j k₂ => .vis j (fun o₂ => .inr ⟨i, k₂ o₂, k⟩)
  | .inr ⟨i, u, k⟩ =>
    match u.observe with
    | .ret o => .tau (.inl (k o))
    | .tau u' => .tau (.inr ⟨i, u', k⟩)
    | .vis j k₂ => .vis j (fun o₂ => .inr ⟨i, k₂ o₂, k⟩)

/-- Interpret every request of `E₁` into an `ITree E₂` computation via `h`. -/
def interp {E₁ E₂ : Effect.{u}} {R : Type u}
    (h : (i : E₁.I) → ITree E₂ (E₁.O i)) (t : ITree E₁ R) : ITree E₂ R :=
  cofix (interpStep h) (.inl t)

/-- Internal coalgebra carrier for stateful `ITree.interpState`. -/
abbrev InterpStateCarrier (E₁ E₂ : Effect.{u}) (S R : Type u) : Type u :=
  (ITree E₁ R × S) ⊕
    (Σ i : E₁.I, ITree E₂ (E₁.O i × S) × (E₁.O i → ITree E₁ R))

/-- Coalgebra step for `ITree.interpState`. -/
def interpStateStep {E₁ E₂ : Effect.{u}} {S R : Type u}
    (h : (i : E₁.I) → S → ITree E₂ (E₁.O i × S)) :
    InterpStateCarrier E₁ E₂ S R →
      ITreeF E₂ (R × S) (InterpStateCarrier E₁ E₂ S R)
  | .inl (t, s) =>
    match t.observe with
    | .ret r => .ret (r, s)
    | .tau t' => .tau (.inl (t', s))
    | .vis i k =>
      match (h i s).observe with
      | .ret (o, s') => .tau (.inl (k o, s'))
      | .tau u' => .tau (.inr ⟨i, u', k⟩)
      | .vis j k₂ => .vis j (fun o₂ => .inr ⟨i, k₂ o₂, k⟩)
  | .inr ⟨i, u, k⟩ =>
    match u.observe with
    | .ret (o, s') => .tau (.inl (k o, s'))
    | .tau u' => .tau (.inr ⟨i, u', k⟩)
    | .vis j k₂ => .vis j (fun o₂ => .inr ⟨i, k₂ o₂, k⟩)

/-- Interpret `E₁` into `E₂` while threading handler state `s : S`. -/
def interpState {E₁ E₂ : Effect.{u}} {S R : Type u}
    (h : (i : E₁.I) → S → ITree E₂ (E₁.O i × S))
    (t : ITree E₁ R) (s : S) : ITree E₂ (R × S) :=
  cofix (interpStateStep h) (.inl (t, s))

end ITree

/-! ## Labeled Reachability, Divergence, Productivity, and Layer 1A Projections -/

/-- Reflexive-transitive closure of silent `.tau` transitions. -/
inductive TauStar {E : Effect.{u}} {R : Type u} :
    ITree E R → ITree E R → Prop where
  | refl (t : ITree E R) : TauStar t t
  | step {t t' u : ITree E R} :
      t.observe = .tau t' → TauStar t' u → TauStar t u

/-- `t` can reach a fault request (`FaultEffect.isFault i`) via silent `.tau`s. -/
def FaultNow {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : Prop :=
  ∃ t' i k, TauStar t t' ∧ t'.observe = .vis i k ∧ FaultEffect.isFault i

/-- `t` reaches a non-fault visible request with an uninhabited answer type. -/
def StuckNow {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : Prop :=
  ∃ t' i k,
    TauStar t t' ∧ t'.observe = .vis i k ∧ ¬ FaultEffect.isFault i ∧
      (E.O i → False)

/-- Finite labeled `(req, ans)` transition reachability over `ITree E R`. -/
inductive Reaches {E : Effect.{u}} {R : Type u} [FaultEffect E] :
    ITree E R → List (Event E) → ITree E R → Prop where
  | refl (t : ITree E R) : Reaches t [] t
  | tau {t t' u : ITree E R} {tr : List (Event E)} :
      t.observe = .tau t' → Reaches t' tr u → Reaches t tr u
  | vis {t u : ITree E R} {i : E.I} {k : E.O i → ITree E R}
      {tr : List (Event E)} :
      t.observe = .vis i k →
      ¬ FaultEffect.isFault i →
      (o : E.O i) →
      Reaches (k o) tr u →
      Reaches t (⟨i, o⟩ :: tr) u

/-- `t` reaches `.ret r` along completed interaction trace `tr`. -/
def ReachesRet {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) (tr : List (Event E)) (r : R) : Prop :=
  ∃ u, Reaches t tr u ∧ u.observe = .ret r

/-- All-prefix UB-freedom: no reachable residual of `t` faults. -/
def TreeSafe {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : Prop :=
  ∀ tr u, Reaches t tr u → ¬ FaultNow u

/-- Coinductive silent divergence predicate (`t` steps via `.tau` forever). -/
def Diverges {E : Effect.{u}} {R : Type u} (t : ITree E R) : Prop :=
  match t.observe with
  | .tau t' => Diverges t'
  | _ => False
coinductive_fixpoint

/-- `MayDiverge t` holds when some reachable residual of `t` silently diverges. -/
def MayDiverge {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : Prop :=
  ∃ tr u, Reaches t tr u ∧ Diverges u

/--
Reactive productivity: every reachable residual of `t` stabilizes to a `.ret`
or `.vis` node after finitely many silent `.tau` steps.
-/
def Productive {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : Prop :=
  ∀ tr u, Reaches t tr u →
    ∃ u', TauStar u u' ∧ ∀ w, u'.observe ≠ .tau w

/-- Frontier status of a finite interaction-tree execution prefix. -/
inductive TreePrefixOutcome (R : Type u) : Type u where
  | running
  | ret (r : R)
  | fault
  deriving DecidableEq, Repr

/-- `.running` and `.ret _` are safe; `.fault` is `False`. -/
def TreePrefixOutcome.isSafe {R : Type u} : TreePrefixOutcome R → Prop
  | .running => True
  | .ret _ => True
  | .fault => False

/-- Finite execution prefix pairing a completed event trace with its status. -/
structure TreePrefix (E : Effect.{u}) (R : Type u) : Type u where
  trace : List (Event E)
  outcome : TreePrefixOutcome R

/-- Raw finite execution prefix set of `t`. -/
def HasTreePrefix {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : BehaviorSet (TreePrefix E R) :=
  fun p =>
    match p.outcome with
    | .running => ∃ u, Reaches t p.trace u
    | .ret r => ReachesRet t p.trace r
    | .fault => ∃ u, Reaches t p.trace u ∧ FaultNow u

/--
Prefix-preserving UB-closed behavior set of `t` (CompCert `Goes_wrong` / Vellvm
`model_UB` closure), using Lean's standard `List.IsPrefix` (`<+:`):
a fault after `tr₀ <+: p.trace` admits every extension `p` while preserving
non-faulting prefixes prior to `tr₀`.
-/
def UBClosedPrefixes {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : BehaviorSet (TreePrefix E R) :=
  fun p =>
    HasTreePrefix t p ∨ ∃ tr₀, tr₀ <+: p.trace ∧ HasTreePrefix t ⟨tr₀, .fault⟩

/-- Canonical downward-closed safety specification on `TreePrefix E R`. -/
def TreeNoUBSpec (E : Effect.{u}) (R : Type u) :
    Spec (BehaviorSet (TreePrefix E R)) :=
  BehaviorSet.allSpec (fun p => p.outcome.isSafe)

/--
Project `t` into Layer 1A's Smyth `Partial` domain over completed
`(trace, returnValue)` pairs.
-/
def ITree.toPartial {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : Partial (BehaviorSet (List (Event E) × R)) where
  defined := TreeSafe t
  val _ out := ReachesRet t out.1 out.2

/--
Project `t` into Layer 1A's Smyth `Partial` domain over all finite execution
prefixes `TreePrefix E R`.
-/
def ITree.toPrefixPartial {E : Effect.{u}} {R : Type u} [FaultEffect E]
    (t : ITree E R) : Partial (BehaviorSet (TreePrefix E R)) where
  defined := TreeSafe t
  val _ := HasTreePrefix t

/-- Package a parameterized `ITree` semantics as a Layer 1A `Language`. -/
def ITree.lang {Prog Query R : Type} {E : Effect.{0}} [FaultEffect E]
    (sem : Prog → Query → ITree E R) : Language where
  Prog := Prog
  Query := Query
  Out := List (Event E) × R
  sem p q := (sem p q).toPartial

/-- Package a parameterized `ITree` prefix semantics as a Layer 1A `Language`. -/
def ITree.prefixLang {Prog Query R : Type} {E : Effect.{0}} [FaultEffect E]
    (sem : Prog → Query → ITree E R) : Language where
  Prog := Prog
  Query := Query
  Out := TreePrefix E R
  sem p q := (sem p q).toPrefixPartial

end Trusted.ITree
