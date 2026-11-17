import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.EffectWP
import Anneal.ITreeWP
import Anneal.Scalars
import Anneal.Memory
import Anneal.UnsafeObligations
import Anneal.SepLogic
import Anneal.Rustc.V2026_06_01.Lower

namespace Anneal.Rustc.V2026_06_01.SymbolicEval

open Trusted.Refinement
open Trusted.Sequence
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Scalars
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower

/-!
Single-pass continuation-passing symbolic MIR evaluator, bidirectional `#[spec]`
boolean companion (`MirBoolPredicateHolds`) combinators, bounded undefined-behavior
refutation combinators, and non-vacuity witness helpers for
`Trusted.Rustc.V2026_06_01` (`#100`, `#102`, `#103`, `#125`).

1. **Coinductive Completeness of `DWLP mirDefaultWP`**:
   `dwlp_mirDefaultWP_iff` establishes exact soundness and completeness between
   `DWLP mirDefaultWP t` and `(TreeSafe t ∧ ∀ tr out, ReachesRet t tr out → post out)`,
   yielding bidirectional `DWLP` characterizations of `MirContractHoldsWithSafety`,
   `MirContractHolds`, `MirBoolPredicateHolds`, and `MirStatefulContractHoldsWithSafety`.
2. **Single-Pass CPS Symbolic MIR Evaluator (`wpMirSym`, `wpMirOrExhaustedSym`)**:
   Pushes the verification continuation directly through symbolic scalar
   comparisons, checked/unchecked arithmetic branches, `UnOp.not`, `SwitchInt`
   dispatch tables, and `Assert` overflow guards so straight-line and branching
   MIR bodies reduce in a single pass without re-evaluating shared prefixes.
3. **Certificate & `#[spec]` Discharge Combinators**:
   Ergonomic combinators for `VerificationResult` (`verifyMirSym`,
   `verifyMirSafeSym`, `verifyMirNoPanicSym`), `TotalVerificationResult`
   (`verifyTotalMirSym`), `StatefulVerificationResult` (`verifyStatefulMirSym`,
   `verifyStatefulMirNoPanicSym`), `MirBoolPredicateHolds`
   (`mirBoolPredicateHolds_of_wpMirSym`, `holdBoolMirSym_of_mirBoolPredicateHolds`,
   `mirBoolPredicateHolds_iff_wpMirBoolSym`), and pinned/symbolic scalar specs.
4. **Bounded UB Refutation & Non-Vacuity Combinators**:
   `reachesFaultBounded`, `refuteClaimByBoundedUB`,
   `refuteStatefulClaimByBoundedUB`, `refuteTotalClaimByBoundedUB`,
   `proveNonVacuousPre`, `proveNonVacuousStatefulPre`, and
   `proveNonVacuousBoolSpecPre`.
5. **Safe Panics Across Uninterpreted External Calls**:
   `reachesModularSafePanicExecBounded` and
   `verifyModularSafePanicMirBounded` certify a body that panics after an
   uninterpreted external call with a `ModularVerificationResult` under the
   frame-preserving rely contract `framePreservingCallContract`, and
   `refuteTotalClaimByBoundedPanicAcrossCalls` refutes its `TotalClaim` along an
   explicit answer to each external call.
-/

/-! ## 1. Coinductive Completeness of `DWLP mirDefaultWP` & Contract Equivalences -/

/--
Soundness and coinductive completeness of `DWLP mirDefaultWP`: `DWLP mirDefaultWP`
holds on `t` if and only if `t` is all-prefix UB-free (`TreeSafe t`) and every
reachable return value satisfies `post`.
-/
theorem dwlp_mirDefaultWP_iff
    (t : ITree MirEffect MirOutcome) (post : MirOutcome → Prop) :
    DWLP mirDefaultWP t (fun out _ => post out) PUnit.unit ↔
      (TreeSafe t ∧ ∀ tr out, ReachesRet t tr out → post out) := by
  refine ⟨dwlp_pure_adequacy, fun h => ?_⟩
  refine DWLP.coinduct
    (fun x _ => TreeSafe x ∧ ∀ tr out, ReachesRet x tr out → post out)
    ?_ h
  intro x _ ⟨h_safe, h_ret⟩
  cases h_obs : x.observe with
  | ret out =>
    exact h_ret [] out ⟨x, Reaches.refl x, h_obs⟩
  | tau x' =>
    refine ⟨?_, ?_⟩
    · intro tr u h_reach
      exact h_safe tr u (Reaches.tau h_obs h_reach)
    · intro tr out ⟨u, h_reach, h_u⟩
      exact h_ret tr out ⟨u, Reaches.tau h_obs h_reach, h_u⟩
  | vis i k =>
    rcases i with f | (e | c)
    · exfalso
      exact h_safe [] x (Reaches.refl x)
        ⟨x, .inl f, k, TauStar.refl x, h_obs, trivial⟩
    · cases e
      refine ⟨?_, ?_⟩
      · intro tr u h_reach
        exact h_safe (⟨.inr (.inl (.emit _)), PUnit.unit⟩ :: tr) u
          (Reaches.vis h_obs False.elim PUnit.unit h_reach)
      · intro tr out ⟨u, h_reach, h_u⟩
        exact h_ret (⟨.inr (.inl (.emit _)), PUnit.unit⟩ :: tr) out
          ⟨u, Reaches.vis h_obs False.elim PUnit.unit h_reach, h_u⟩
    · cases c
      intro ans
      refine ⟨?_, ?_⟩
      · intro tr u h_reach
        exact h_safe (⟨.inr (.inr (.call _)), ans⟩ :: tr) u
          (Reaches.vis h_obs False.elim ans h_reach)
      · intro tr out ⟨u, h_reach, h_u⟩
        exact h_ret (⟨.inr (.inr (.call _)), ans⟩ :: tr) out
          ⟨u, Reaches.vis h_obs False.elim ans h_reach, h_u⟩

/-- Exact `DWLP mirDefaultWP` characterization of `MirContractHoldsWithSafety`. -/
theorem mirContractHoldsWithSafety_iff_dwlp
    (body : CapturedMir)
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop) :
    MirContractHoldsWithSafety body safetyPre pre post ↔
      ∀ args : List Value,
        safetyPre args →
        DWLP mirDefaultWP (mirCallTree body args)
          (fun out _ =>
            pre args →
              ∀ retVal mem', out = .normal (retVal, mem') → post args retVal)
          PUnit.unit := by
  constructor
  · intro h args h_safe
    rcases h args h_safe with ⟨h_tree_safe, h_val⟩
    exact (dwlp_mirDefaultWP_iff _ _).2
      ⟨h_tree_safe, fun tr out h_ret h_pre retVal mem' h_out =>
        h_val (tr, out) h_ret h_pre retVal mem' h_out⟩
  · intro h args h_safe
    have h_adeq := (dwlp_mirDefaultWP_iff _ _).1 (h args h_safe)
    exact ⟨h_adeq.1, fun outPair h_ret h_pre retVal mem' h_out =>
      h_adeq.2 outPair.1 outPair.2 h_ret h_pre retVal mem' h_out⟩

/-- Exact `DWLP mirDefaultWP` characterization of `MirContractHolds`. -/
theorem mirContractHolds_iff_dwlp
    (body : CapturedMir)
    (pre : List Value → Prop)
    (post : List Value → Value → Prop) :
    MirContractHolds body pre post ↔
      ∀ args : List Value,
        pre args →
        DWLP mirDefaultWP (mirCallTree body args)
          (fun out _ =>
            ∀ retVal mem', out = .normal (retVal, mem') → post args retVal)
          PUnit.unit := by
  rw [MirContractHolds, MirContractHoldsWithCallees, ← MirContractHoldsWithSafety,
    mirContractHoldsWithSafety_iff_dwlp]
  constructor
  · intro h args h_pre
    exact DWLP.mono (fun _ _ hf => hf h_pre) (h args h_pre)
  · intro h args h_pre
    exact DWLP.mono (fun _ _ hf _ => hf) (h args h_pre)

/--
Equivalence between two-precondition `MirContractHoldsWithSafety` (`safetyPre` in
`.defined`, `pre` guarding `post` in `.val`) and single-precondition
`MirContractHolds` with guarded postcondition `fun args ret => pre args → post args ret`.
-/
theorem mirContractHoldsWithSafety_iff_mirContractHolds_imp
    (body : CapturedMir)
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop) :
    MirContractHoldsWithSafety body safetyPre pre post ↔
      MirContractHolds body safetyPre (fun args ret => pre args → post args ret) := by
  rw [mirContractHoldsWithSafety_iff_dwlp, mirContractHolds_iff_dwlp]
  constructor
  · intro h args h_safe
    exact DWLP.mono
      (fun _ _ hf retVal mem' h_out h_pre => hf h_pre retVal mem' h_out)
      (h args h_safe)
  · intro h args h_safe
    exact DWLP.mono
      (fun _ _ hf h_pre retVal mem' h_out => hf retVal mem' h_out h_pre)
      (h args h_safe)

/-- Exact `DWLP mirDefaultWP` characterization of `MirContractHoldsWithSafetyAndCallees`. -/
theorem mirContractHoldsWithSafetyAndCallees_iff_dwlp
    (body : CapturedMir)
    (callees : List CapturedMir)
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop) :
    MirContractHoldsWithSafetyAndCallees body callees safetyPre pre post ↔
      ∀ args : List Value,
        safetyPre args →
        DWLP mirDefaultWP (mirCallTreeWithCallees body args callees)
          (fun out _ =>
            pre args →
              ∀ retVal mem', out = .normal (retVal, mem') → post args retVal)
          PUnit.unit := by
  constructor
  · intro h args h_safe
    rcases h args h_safe with ⟨h_tree_safe, h_val⟩
    exact (dwlp_mirDefaultWP_iff _ _).2
      ⟨h_tree_safe, fun tr out h_ret h_pre retVal mem' h_out =>
        h_val (tr, out) h_ret h_pre retVal mem' h_out⟩
  · intro h args h_safe
    have h_adeq := (dwlp_mirDefaultWP_iff _ _).1 (h args h_safe)
    exact ⟨h_adeq.1, fun outPair h_ret h_pre retVal mem' h_out =>
      h_adeq.2 outPair.1 outPair.2 h_ret h_pre retVal mem' h_out⟩

/-- Exact `DWLP mirDefaultWP` characterization of `MirContractHoldsWithCallees`. -/
theorem mirContractHoldsWithCallees_iff_dwlp
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Prop)
    (post : List Value → Value → Prop) :
    MirContractHoldsWithCallees body callees pre post ↔
      ∀ args : List Value,
        pre args →
        DWLP mirDefaultWP (mirCallTreeWithCallees body args callees)
          (fun out _ =>
            ∀ retVal mem', out = .normal (retVal, mem') → post args retVal)
          PUnit.unit := by
  rw [MirContractHoldsWithCallees, mirContractHoldsWithSafetyAndCallees_iff_dwlp]
  constructor
  · intro h args h_pre
    exact DWLP.mono (fun _ _ hf => hf h_pre) (h args h_pre)
  · intro h args h_pre
    exact DWLP.mono (fun _ _ hf _ => hf) (h args h_pre)

/--
Equivalence between two-precondition `MirContractHoldsWithSafetyAndCallees` and
single-precondition `MirContractHoldsWithCallees` with guarded postcondition.
-/
theorem mirContractHoldsWithSafetyAndCallees_iff_mirContractHoldsWithCallees_imp
    (body : CapturedMir)
    (callees : List CapturedMir)
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop) :
    MirContractHoldsWithSafetyAndCallees body callees safetyPre pre post ↔
      MirContractHoldsWithCallees body callees safetyPre
        (fun args ret => pre args → post args ret) := by
  rw [mirContractHoldsWithSafetyAndCallees_iff_dwlp, mirContractHoldsWithCallees_iff_dwlp]
  constructor
  · intro h args h_safe
    exact DWLP.mono
      (fun _ _ hf retVal mem' h_out h_pre => hf h_pre retVal mem' h_out)
      (h args h_safe)
  · intro h args h_safe
    exact DWLP.mono
      (fun _ _ hf h_pre retVal mem' h_out => hf retVal mem' h_out h_pre)
      (h args h_safe)

/-- Exact `DWLP mirDefaultWP` characterization of `MirBoolPredicateHoldsWithCallees`. -/
theorem mirBoolPredicateHoldsWithCallees_iff_dwlp
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value) :
    MirBoolPredicateHoldsWithCallees specBody callees args ↔
      DWLP mirDefaultWP (mirCallTreeWithCallees specBody args callees)
        (fun out _ =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 })
        PUnit.unit := by
  rw [MirBoolPredicateHoldsWithCallees, mirContractHoldsWithCallees_iff_dwlp]
  exact ⟨fun h => h args rfl, fun h _ h_eq => h_eq ▸ h⟩

/-- Exact `DWLP mirDefaultWP` characterization of `MirBoolPredicateHolds`. -/
theorem mirBoolPredicateHolds_iff_dwlp
    (specBody : CapturedMir) (args : List Value) :
    MirBoolPredicateHolds specBody args ↔
      DWLP mirDefaultWP (mirCallTree specBody args)
        (fun out _ =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 })
        PUnit.unit :=
  mirBoolPredicateHoldsWithCallees_iff_dwlp specBody .nil args

/-- Exact `DWLP mirDefaultWP` characterization of `MirStatefulContractHoldsWithSafetyAndCallees`. -/
theorem mirStatefulContractHoldsWithSafetyAndCallees_iff_dwlp
    (body : CapturedMir)
    (callees : List CapturedMir)
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) :
    MirStatefulContractHoldsWithSafetyAndCallees body callees safetyPre pre post ↔
      ∀ (args : List Value) (mem : Memory),
        safetyPre args mem →
        DWLP mirDefaultWP (mirStatefulTreeWithCallees body args mem callees)
          (fun out _ =>
            pre args mem →
              ∀ retVal mem',
                out = .normal (retVal, mem') → post args mem retVal mem')
          PUnit.unit := by
  constructor
  · intro h args mem h_safe
    rcases h args mem h_safe with ⟨h_tree_safe, h_val⟩
    exact (dwlp_mirDefaultWP_iff _ _).2
      ⟨h_tree_safe, fun tr out h_ret h_pre retVal mem' h_out =>
        h_val (tr, out) h_ret h_pre retVal mem' h_out⟩
  · intro h args mem h_safe
    have h_adeq := (dwlp_mirDefaultWP_iff _ _).1 (h args mem h_safe)
    exact ⟨h_adeq.1, fun outPair h_ret h_pre retVal mem' h_out =>
      h_adeq.2 outPair.1 outPair.2 h_ret h_pre retVal mem' h_out⟩

/-- Exact `DWLP mirDefaultWP` characterization of `MirStatefulContractHoldsWithCallees`. -/
theorem mirStatefulContractHoldsWithCallees_iff_dwlp
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) :
    MirStatefulContractHoldsWithCallees body callees pre post ↔
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        DWLP mirDefaultWP (mirStatefulTreeWithCallees body args mem callees)
          (fun out _ =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → post args mem retVal mem')
          PUnit.unit := by
  rw [MirStatefulContractHoldsWithCallees,
    mirStatefulContractHoldsWithSafetyAndCallees_iff_dwlp]
  constructor
  · intro h args mem h_pre
    exact DWLP.mono (fun _ _ hf => hf h_pre) (h args mem h_pre)
  · intro h args mem h_pre
    exact DWLP.mono (fun _ _ hf _ => hf) (h args mem h_pre)

/--
Equivalence between two-precondition `MirStatefulContractHoldsWithSafetyAndCallees`
and single-precondition `MirStatefulContractHoldsWithCallees` with guarded
postcondition.
-/
theorem mirStatefulContractHoldsWithSafetyAndCallees_iff_mirStatefulContractHoldsWithCallees_imp
    (body : CapturedMir)
    (callees : List CapturedMir)
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) :
    MirStatefulContractHoldsWithSafetyAndCallees body callees safetyPre pre post ↔
      MirStatefulContractHoldsWithCallees body callees safetyPre
        (fun args mem ret mem' => pre args mem → post args mem ret mem') := by
  rw [mirStatefulContractHoldsWithSafetyAndCallees_iff_dwlp,
    mirStatefulContractHoldsWithCallees_iff_dwlp]
  constructor
  · intro h args mem h_safe
    exact DWLP.mono
      (fun _ _ hf retVal mem' h_out h_pre => hf h_pre retVal mem' h_out)
      (h args mem h_safe)
  · intro h args mem h_safe
    exact DWLP.mono
      (fun _ _ hf h_pre retVal mem' h_out => hf retVal mem' h_out h_pre)
      (h args mem h_safe)

/-- Exact `DWLP mirDefaultWP` characterization of `MirStatefulContractHoldsWithSafety`. -/
theorem mirStatefulContractHoldsWithSafety_iff_dwlp
    (body : CapturedMir)
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) :
    MirStatefulContractHoldsWithSafety body safetyPre pre post ↔
      ∀ (args : List Value) (mem : Memory),
        safetyPre args mem →
        DWLP mirDefaultWP (mirStatefulTree body args mem)
          (fun out _ =>
            pre args mem →
              ∀ retVal mem',
                out = .normal (retVal, mem') → post args mem retVal mem')
          PUnit.unit := by
  constructor
  · intro h args mem h_safe
    rcases h args mem h_safe with ⟨h_tree_safe, h_val⟩
    exact (dwlp_mirDefaultWP_iff _ _).2
      ⟨h_tree_safe, fun tr out h_ret h_pre retVal mem' h_out =>
        h_val (tr, out) h_ret h_pre retVal mem' h_out⟩
  · intro h args mem h_safe
    have h_adeq := (dwlp_mirDefaultWP_iff _ _).1 (h args mem h_safe)
    exact ⟨h_adeq.1, fun outPair h_ret h_pre retVal mem' h_out =>
      h_adeq.2 outPair.1 outPair.2 h_ret h_pre retVal mem' h_out⟩

/-- Exact `DWLP mirDefaultWP` characterization of `MirStatefulContractHolds`. -/
theorem mirStatefulContractHolds_iff_dwlp
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) :
    MirStatefulContractHolds body pre post ↔
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        DWLP mirDefaultWP (mirStatefulTree body args mem)
          (fun out _ =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → post args mem retVal mem')
          PUnit.unit := by
  rw [MirStatefulContractHolds, MirStatefulContractHoldsWithCallees,
    ← MirStatefulContractHoldsWithSafety, mirStatefulContractHoldsWithSafety_iff_dwlp]
  constructor
  · intro h args mem h_pre
    exact DWLP.mono (fun _ _ hf => hf h_pre) (h args mem h_pre)
  · intro h args mem h_pre
    exact DWLP.mono (fun _ _ hf _ => hf) (h args mem h_pre)

/--
Equivalence between two-precondition `MirStatefulContractHoldsWithSafety` and
single-precondition `MirStatefulContractHolds` with guarded postcondition.
-/
theorem mirStatefulContractHoldsWithSafety_iff_mirStatefulContractHolds_imp
    (body : CapturedMir)
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) :
    MirStatefulContractHoldsWithSafety body safetyPre pre post ↔
      MirStatefulContractHolds body safetyPre
        (fun args mem ret mem' => pre args mem → post args mem ret mem') := by
  rw [mirStatefulContractHoldsWithSafety_iff_dwlp, mirStatefulContractHolds_iff_dwlp]
  constructor
  · intro h args mem h_safe
    exact DWLP.mono
      (fun _ _ hf retVal mem' h_out h_pre => hf h_pre retVal mem' h_out)
      (h args mem h_safe)
  · intro h args mem h_safe
    exact DWLP.mono
      (fun _ _ hf h_pre retVal mem' h_out => hf retVal mem' h_out h_pre)
      (h args mem h_safe)

/-! ## 2. Outcome Postcondition Projections (`mirSafePost`, `mirNormalPost`) -/

/--
Partial-correctness outcome predicate: requires `Q retVal mem'` on normal return
and accepts defined unwinding/abort outcomes (`True`) without permitting UB.
-/
@[reducible]
def mirSafePost (Q : Value → Memory → Prop) : MirOutcome → Prop
  | .normal (retVal, mem') => Q retVal mem'
  | .panic => True
  | .abort => True

/--
Panic-forbidding / total-correctness outcome predicate: requires normal return
satisfying `Q retVal mem'` and rejects `.panic` and `.abort` (`False`).
-/
@[reducible]
def mirNormalPost (Q : Value → Memory → Prop) : MirOutcome → Prop
  | .normal (retVal, mem') => Q retVal mem'
  | .panic => False
  | .abort => False

theorem mirSafePost_iff_forall_normal
    (Q : Value → Memory → Prop) (out : MirOutcome) :
    mirSafePost Q out ↔
      (∀ retVal mem', out = .normal (retVal, mem') → Q retVal mem') := by
  cases out with
  | normal p =>
    rcases p with ⟨retVal, mem'⟩
    simp [mirSafePost]
  | panic =>
    simp [mirSafePost]
  | abort =>
    simp [mirSafePost]

theorem mirNormalPost_iff_exists_normal
    (Q : Value → Memory → Prop) (out : MirOutcome) :
    mirNormalPost Q out ↔
      (∃ retVal mem', out = .normal (retVal, mem') ∧ Q retVal mem') := by
  cases out with
  | normal p =>
    rcases p with ⟨retVal, mem'⟩
    constructor
    · intro h
      exact ⟨retVal, mem', rfl, h⟩
    · rintro ⟨_, _, heq, h⟩
      cases heq
      exact h
  | panic =>
    simp [mirNormalPost]
  | abort =>
    simp [mirNormalPost]

theorem mirNormalPost_imp_mirSafePost
    {Q : Value → Memory → Prop} {out : MirOutcome}
    (h : mirNormalPost Q out) :
    mirSafePost Q out := by
  cases out with
  | normal p =>
    rcases p with ⟨_, _⟩
    exact h
  | panic => exact False.elim h
  | abort => exact False.elim h

/-! ## 3. Single-Pass CPS Symbolic MIR Evaluator (`SymTree`, `stepMirSymCont`, `wpMirSym`) -/

/--
Finite symbolic decision tree over operational results `α`, pushing symbolic
boolean conditions (`Nat.beq`, `Nat.ble`, overflow flags, `SwitchInt` guards,
and `Assert` checks) to the outer constructor level so top-down WHNF (`whnf` /
`split`) reduces straight-line and branching MIR steps in a single pass without
unfolding continuation lambdas over abstract states.
-/
inductive SymTree (α : Type u) : Type u where
  | leaf (val : α) : SymTree α
  | branch (cond : Bool) (onTrue onFalse : SymTree α) : SymTree α

/-- Monadic composition of symbolic decision trees. -/
def SymTree.bind (t : SymTree α) (f : α → SymTree β) : SymTree β :=
  match t with
  | .leaf a => f a
  | .branch c t1 t2 => .branch c (t1.bind f) (t2.bind f)

/-- Concrete evaluation of a `SymTree α` down to `α`. -/
def SymTree.eval : SymTree α → α
  | .leaf a => a
  | .branch true t1 _ => t1.eval
  | .branch false _ t2 => t2.eval

/-- Continuation-passing `Prop` interpretation of `SymTree α`. -/
def SymTree.run (t : SymTree α) (k : α → Prop) : Prop :=
  match t with
  | .leaf a => k a
  | .branch c t1 t2 =>
    match c with
    | true => t1.run k
    | false => t2.run k

theorem SymTree.bind_eval (t : SymTree α) (f : α → SymTree β) :
    (t.bind f).eval = (f t.eval).eval := by
  induction t with
  | leaf _ => rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

theorem SymTree.run_eq_eval (t : SymTree α) (k : α → Prop) :
    t.run k = k t.eval := by
  induction t with
  | leaf _ => rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/-- Direct `Prop`-valued node evaluator matching `mirDefaultWP` on `MirStepNode`. -/
@[reducible]
def evalNodeWP
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr (.call _))) k => ∀ ans : MirCallAns, cont (k ans)

theorem evalNodeWP_eq
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (node : MirStepNode) :
    evalNodeWP cont post node =
      match node with
      | .ret out => post out
      | .tau st' => cont st'
      | .vis i k => mirDefaultWP.wp i (fun o _ => cont (k o)) PUnit.unit := by
  cases node with
  | ret _ => rfl
  | tau _ => rfl
  | vis i _ =>
    rcases i with f | (e | c)
    · cases f; rfl
    · cases e; rfl
    · cases c; rfl

/-- Structural `Prop`-valued evaluator over `SymTree MirStepNode`. -/
def evalSymNodeTree
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr (.call _))) k) => ∀ ans : MirCallAns, cont (k ans)
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTree cont post t1
    | false => evalSymNodeTree cont post t2

theorem evalSymNodeTree_eq
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (tree : SymTree MirStepNode) :
    evalSymNodeTree cont post tree = evalNodeWP cont post tree.eval := by
  induction tree with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c)
      · cases f; rfl
      · cases e; rfl
      · cases c; rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/--
Decision-tree symbolic `evalScalarBinOp`: splits every symbolic width check,
overflow flag, and comparison boolean into `SymTree.branch` so each leaf carries
concrete boolean/overflow bit values into downstream `SwitchInt` and `Assert`
terminators.
-/
def evalScalarBinOpSymTree
    (op : BinOp)
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory)
    (isSigned : Bool) : SymTree RvalueEvalResult :=
  .branch (Nat.beq lhs.sizeBytes 0) (.leaf .unsupported) (
    let sz := lhs.sizeBytes
    let numBits := Nat.mul sz 8
    let modulus := scalarModulus sz
    let a := lhs.bits
    let b := rhs.bits
    match op with
    | .shl =>
      .branch (Nat.beq rhs.sizeBytes 0) (.leaf .unsupported) (
        let shift := Nat.mod b numBits
        .leaf (.ok (.scalar ⟨shiftLeftBits a shift modulus, sz⟩) locals mem))
    | .shlUnchecked =>
      .branch (Nat.beq rhs.sizeBytes 0) (.leaf .unsupported)
        (.branch (Nat.ble numBits b)
          (.leaf .ub)
          (.leaf (.ok (.scalar ⟨shiftLeftBits a b modulus, sz⟩) locals mem)))
    | .shr =>
      .branch (Nat.beq rhs.sizeBytes 0) (.leaf .unsupported) (
        let shift := Nat.mod b numBits
        let shifted :=
          match isSigned with
          | false => wrapScalarBits (shiftRightUnsignedBits a shift) modulus
          | true => arithmeticShrBits a sz shift
        .leaf (.ok (.scalar ⟨shifted, sz⟩) locals mem))
    | .shrUnchecked =>
      .branch (Nat.beq rhs.sizeBytes 0) (.leaf .unsupported)
        (.branch (Nat.ble numBits b)
          (.leaf .ub) (
            let shifted :=
              match isSigned with
              | false => wrapScalarBits (shiftRightUnsignedBits a b) modulus
              | true => arithmeticShrBits a sz b
            .leaf (.ok (.scalar ⟨shifted, sz⟩) locals mem)))
    | _ =>
      .branch (Nat.beq lhs.sizeBytes rhs.sizeBytes)
        (match op with
        | .add =>
          let sum := Nat.add a b
          .leaf (.ok (.scalar ⟨wrapScalarBits sum modulus, sz⟩) locals mem)
        | .addUnchecked =>
          let sum := Nat.add a b
          match isSigned with
          | false =>
            .branch (Nat.ble modulus sum)
              (.leaf .ub)
              (.leaf (.ok (.scalar ⟨sum, sz⟩) locals mem))
          | true =>
            .branch (signedOverflowAdd a b sz)
              (.leaf .ub)
              (.leaf (.ok (.scalar ⟨wrapScalarBits sum modulus, sz⟩) locals mem))
        | .addWithOverflow =>
          let sum := Nat.add a b
          let wrapped : ScalarInt := ⟨wrapScalarBits sum modulus, sz⟩
          match isSigned with
          | false =>
            .branch (Nat.ble modulus sum)
              (.leaf (.ok (.aggregate 0 (.scalar wrapped :: .scalar ⟨1, 1⟩ :: .nil)) locals mem))
              (.leaf (.ok (.aggregate 0 (.scalar wrapped :: .scalar ⟨0, 1⟩ :: .nil)) locals mem))
          | true =>
            .branch (signedOverflowAdd a b sz)
              (.leaf (.ok (.aggregate 0 (.scalar wrapped :: .scalar ⟨1, 1⟩ :: .nil)) locals mem))
              (.leaf (.ok (.aggregate 0 (.scalar wrapped :: .scalar ⟨0, 1⟩ :: .nil)) locals mem))
        | .sub =>
          .branch (Nat.ble b a)
            (.leaf (.ok (.scalar ⟨wrapScalarBits (Nat.sub a b) modulus, sz⟩) locals mem)) (
              let wrappedDiff :=
                wrapScalarBits
                  (Nat.sub (Nat.add modulus (wrapScalarBits a modulus))
                    (wrapScalarBits b modulus))
                  modulus
              .leaf (.ok (.scalar ⟨wrappedDiff, sz⟩) locals mem))
        | .subUnchecked =>
          match isSigned with
          | false =>
            .branch (Nat.ble b a) (
              let diff := Nat.sub a b
              .branch (Nat.ble modulus diff)
                (.leaf .ub)
                (.leaf (.ok (.scalar ⟨diff, sz⟩) locals mem)))
              (.leaf .ub)
          | true =>
            .branch (signedOverflowSub a b sz)
              (.leaf .ub) (
                let ca := wrapScalarBits a modulus
                let cb := wrapScalarBits b modulus
                let wrappedDiff :=
                  match Nat.ble cb ca with
                  | true => wrapScalarBits (Nat.sub ca cb) modulus
                  | false => wrapScalarBits (Nat.sub (Nat.add modulus ca) cb) modulus
                .leaf (.ok (.scalar ⟨wrappedDiff, sz⟩) locals mem))
        | .subWithOverflow =>
          match isSigned with
          | false =>
            .branch (Nat.ble b a) (
              let diff := wrapScalarBits (Nat.sub a b) modulus
              .leaf (.ok (.aggregate 0 (.scalar ⟨diff, sz⟩ :: .scalar ⟨0, 1⟩ :: .nil)) locals mem)) (
              let wrappedDiff :=
                wrapScalarBits
                  (Nat.sub (Nat.add modulus (wrapScalarBits a modulus))
                    (wrapScalarBits b modulus))
                  modulus
              .leaf (.ok
                (.aggregate 0 (.scalar ⟨wrappedDiff, sz⟩ :: .scalar ⟨1, 1⟩ :: .nil))
                locals mem))
          | true =>
            let ca := wrapScalarBits a modulus
            let cb := wrapScalarBits b modulus
            let wrappedDiff :=
              match Nat.ble cb ca with
              | true => wrapScalarBits (Nat.sub ca cb) modulus
              | false => wrapScalarBits (Nat.sub (Nat.add modulus ca) cb) modulus
            .branch (signedOverflowSub a b sz)
              (.leaf (.ok (.aggregate 0 (.scalar ⟨wrappedDiff, sz⟩ :: .scalar ⟨1, 1⟩ :: .nil)) locals mem))
              (.leaf (.ok (.aggregate 0 (.scalar ⟨wrappedDiff, sz⟩ :: .scalar ⟨0, 1⟩ :: .nil)) locals mem))
        | .mul =>
          let prod := Nat.mul a b
          .leaf (.ok (.scalar ⟨wrapScalarBits prod modulus, sz⟩) locals mem)
        | .mulUnchecked =>
          let prod := Nat.mul a b
          match isSigned with
          | false =>
            .branch (Nat.ble modulus prod)
              (.leaf .ub)
              (.leaf (.ok (.scalar ⟨prod, sz⟩) locals mem))
          | true =>
            .branch (signedOverflowMul a b sz)
              (.leaf .ub)
              (.leaf (.ok (.scalar ⟨wrapScalarBits prod modulus, sz⟩) locals mem))
        | .mulWithOverflow =>
          let prod := Nat.mul a b
          let wrapped : ScalarInt := ⟨wrapScalarBits prod modulus, sz⟩
          match isSigned with
          | false =>
            .branch (Nat.ble modulus prod)
              (.leaf (.ok (.aggregate 0 (.scalar wrapped :: .scalar ⟨1, 1⟩ :: .nil)) locals mem))
              (.leaf (.ok (.aggregate 0 (.scalar wrapped :: .scalar ⟨0, 1⟩ :: .nil)) locals mem))
          | true =>
            .branch (signedOverflowMul a b sz)
              (.leaf (.ok (.aggregate 0 (.scalar wrapped :: .scalar ⟨1, 1⟩ :: .nil)) locals mem))
              (.leaf (.ok (.aggregate 0 (.scalar wrapped :: .scalar ⟨0, 1⟩ :: .nil)) locals mem))
        | .div =>
          .branch (Nat.beq b 0) (.leaf .ub)
            (match isSigned with
            | false =>
              .leaf (.ok (.scalar ⟨wrapScalarBits (Nat.div a b) modulus, sz⟩) locals mem)
            | true => .leaf (evalSignedDiv a b sz locals mem))
        | .rem =>
          .branch (Nat.beq b 0) (.leaf .ub)
            (match isSigned with
            | false =>
              .leaf (.ok (.scalar ⟨wrapScalarBits (Nat.mod a b) modulus, sz⟩) locals mem)
            | true => .leaf (evalSignedRem a b sz locals mem))
        | .bitAnd =>
          .leaf (.ok (.scalar ⟨bitwiseAndBits numBits a b, sz⟩) locals mem)
        | .bitOr =>
          .leaf (.ok (.scalar ⟨bitwiseOrBits numBits a b, sz⟩) locals mem)
        | .bitXor =>
          .leaf (.ok (.scalar ⟨bitwiseXorBits numBits a b, sz⟩) locals mem)
        | .eq =>
          .branch (Nat.beq a b)
            (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
            (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
        | .ne =>
          .branch (Nat.beq a b)
            (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
            (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
        | .lt =>
          match isSigned with
          | false =>
            .branch (Nat.ble b a)
              (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
              (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
          | true =>
            .branch (signedLt a b sz)
              (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
              (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
        | .le =>
          match isSigned with
          | false =>
            .branch (Nat.ble a b)
              (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
              (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
          | true =>
            .branch (signedLe a b sz)
              (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
              (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
        | .gt =>
          match isSigned with
          | false =>
            .branch (Nat.ble a b)
              (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
              (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
          | true =>
            .branch (signedLt b a sz)
              (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
              (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
        | .ge =>
          match isSigned with
          | false =>
            .branch (Nat.ble b a)
              (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
              (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
          | true =>
            .branch (signedLe b a sz)
              (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
              (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
        | .cmp =>
          match isSigned with
          | false =>
            .branch (Nat.beq a b)
              (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
              (.branch (Nat.ble a b)
                (.leaf (.ok (.scalar ⟨255, 1⟩) locals mem))
                (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem)))
          | true =>
            let ca := wrapScalarBits a modulus
            let cb := wrapScalarBits b modulus
            .branch (Nat.beq ca cb)
              (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
              (.branch (signedLt ca cb sz)
                (.leaf (.ok (.scalar ⟨255, 1⟩) locals mem))
                (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem)))
        | _ => .leaf .unsupported)
        (.leaf .unsupported))

theorem evalScalarBinOpSymTree_eval
    (op : BinOp)
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory)
    (isSigned : Bool) :
    (evalScalarBinOpSymTree op lhs rhs locals mem isSigned).eval =
      evalScalarBinOp op lhs rhs locals mem isSigned := by
  dsimp only [evalScalarBinOpSymTree, evalScalarBinOp]
  cases Nat.beq lhs.sizeBytes 0 with
  | true => rfl
  | false =>
    dsimp only [SymTree.eval]
    cases op with
    | shl =>
      dsimp only
      cases Nat.beq rhs.sizeBytes 0 <;> rfl
    | shlUnchecked =>
      dsimp only
      cases Nat.beq rhs.sizeBytes 0 with
      | true => rfl
      | false =>
        dsimp only [SymTree.eval]
        cases Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits <;> rfl
    | shr =>
      dsimp only
      cases Nat.beq rhs.sizeBytes 0 <;> rfl
    | shrUnchecked =>
      dsimp only
      cases Nat.beq rhs.sizeBytes 0 with
      | true => rfl
      | false =>
        dsimp only [SymTree.eval]
        cases Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits <;> rfl
    | add | mul | bitAnd | bitOr | bitXor | offset =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes <;> rfl
    | eq | ne =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases Nat.beq lhs.bits rhs.bits <;> rfl
    | lt =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble rhs.bits lhs.bits <;> rfl
        | true =>
          dsimp only
          cases signedLt lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | le =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble lhs.bits rhs.bits <;> rfl
        | true =>
          dsimp only
          cases signedLe lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | gt =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble lhs.bits rhs.bits <;> rfl
        | true =>
          dsimp only
          cases signedLt rhs.bits lhs.bits lhs.sizeBytes <;> rfl
    | ge =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble rhs.bits lhs.bits <;> rfl
        | true =>
          dsimp only
          cases signedLe rhs.bits lhs.bits lhs.sizeBytes <;> rfl
    | sub =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases Nat.ble rhs.bits lhs.bits <;> rfl
    | addUnchecked =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.add lhs.bits rhs.bits) <;> rfl
        | true =>
          dsimp only
          cases signedOverflowAdd lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | addWithOverflow =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.add lhs.bits rhs.bits) <;> rfl
        | true =>
          dsimp only
          cases signedOverflowAdd lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | subUnchecked =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble rhs.bits lhs.bits with
          | false => rfl
          | true =>
            dsimp only [SymTree.eval]
            cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.sub lhs.bits rhs.bits) <;> rfl
        | true =>
          dsimp only
          cases signedOverflowSub lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | subWithOverflow =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble rhs.bits lhs.bits <;> rfl
        | true =>
          dsimp only
          cases signedOverflowSub lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | mulUnchecked =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.mul lhs.bits rhs.bits) <;> rfl
        | true =>
          dsimp only
          cases signedOverflowMul lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | mulWithOverflow =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.mul lhs.bits rhs.bits) <;> rfl
        | true =>
          dsimp only
          cases signedOverflowMul lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | div | rem =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases Nat.beq rhs.bits 0 with
        | true => rfl
        | false =>
          dsimp only [SymTree.eval]
          cases isSigned <;> rfl
    | cmp =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.beq lhs.bits rhs.bits with
          | true => rfl
          | false =>
            dsimp only [SymTree.eval]
            cases Nat.ble lhs.bits rhs.bits <;> rfl
        | true =>
          dsimp only
          cases Nat.beq (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
              (wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes)) with
          | true => rfl
          | false =>
            dsimp only [SymTree.eval]
            cases signedLt (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
              (wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes)) lhs.sizeBytes <;> rfl

/-- Continuation-passing symbolic `evalScalarBinOp`. -/
def evalScalarBinOpSymCont
    (op : BinOp)
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory)
    (isSigned : Bool)
    (k : RvalueEvalResult → Prop) : Prop :=
  (evalScalarBinOpSymTree op lhs rhs locals mem isSigned).run k

theorem evalScalarBinOpSymCont_eq
    (op : BinOp)
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory)
    (isSigned : Bool)
    (k : RvalueEvalResult → Prop) :
    evalScalarBinOpSymCont op lhs rhs locals mem isSigned k =
      k (evalScalarBinOp op lhs rhs locals mem isSigned) := by
  rw [evalScalarBinOpSymCont, SymTree.run_eq_eval, evalScalarBinOpSymTree_eval]

/-- Decision-tree symbolic `evalUnaryNot`. -/
def evalUnaryNotSymTree
    (sc : ScalarInt)
    (optTy : Option Ty)
    (locals : List LocalSlot)
    (mem : Memory) : SymTree RvalueEvalResult :=
  match optTy with
  | .some ty =>
    match ty.kind with
    | .bool =>
      .branch (Nat.beq sc.sizeBytes 1)
        (.branch (Nat.beq sc.bits 0)
          (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
          (.branch (Nat.beq sc.bits 1)
            (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem))
            (.leaf .ub)))
        (.leaf .ub)
    | _ => .leaf (evalUnaryNot sc (.some ty) locals mem)
  | .none =>
    .branch (Nat.beq sc.sizeBytes 0) (.leaf .unsupported)
      (.branch (Nat.beq sc.sizeBytes 1)
        (.branch (Nat.beq sc.bits 0)
          (.leaf (.ok (.scalar ⟨1, 1⟩) locals mem))
          (.branch (Nat.beq sc.bits 1)
            (.leaf (.ok (.scalar ⟨0, 1⟩) locals mem)) (
              let modulus := scalarModulus 1
              let canonical := wrapScalarBits sc.bits modulus
              let comp := Nat.sub (Nat.sub modulus 1) canonical
              .leaf (.ok (.scalar ⟨comp, 1⟩) locals mem)))) (
          let modulus := scalarModulus sc.sizeBytes
          let canonical := wrapScalarBits sc.bits modulus
          let comp := Nat.sub (Nat.sub modulus 1) canonical
          .leaf (.ok (.scalar ⟨comp, sc.sizeBytes⟩) locals mem)))

theorem evalUnaryNotSymTree_eval
    (sc : ScalarInt)
    (optTy : Option Ty)
    (locals : List LocalSlot)
    (mem : Memory) :
    (evalUnaryNotSymTree sc optTy locals mem).eval =
      evalUnaryNot sc optTy locals mem := by
  cases optTy with
  | some ty =>
    rcases ty with ⟨kind, layoutIdx⟩
    cases kind with
    | bool =>
      dsimp only [evalUnaryNotSymTree, evalUnaryNot]
      cases Nat.beq sc.sizeBytes 1 with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases Nat.beq sc.bits 0 with
        | true => rfl
        | false =>
          dsimp only [SymTree.eval]
          cases Nat.beq sc.bits 1 <;> rfl
    | _ => rfl
  | none =>
    dsimp only [evalUnaryNotSymTree, evalUnaryNot]
    cases Nat.beq sc.sizeBytes 0 with
    | true => rfl
    | false =>
      dsimp only [SymTree.eval]
      cases Nat.beq sc.sizeBytes 1 with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        cases Nat.beq sc.bits 0 with
        | true => rfl
        | false =>
          dsimp only [SymTree.eval]
          cases Nat.beq sc.bits 1 <;> rfl

/-- Continuation-passing symbolic `evalUnaryNot`. -/
def evalUnaryNotSymCont
    (sc : ScalarInt)
    (optTy : Option Ty)
    (locals : List LocalSlot)
    (mem : Memory)
    (k : RvalueEvalResult → Prop) : Prop :=
  (evalUnaryNotSymTree sc optTy locals mem).run k

theorem evalUnaryNotSymCont_eq
    (sc : ScalarInt)
    (optTy : Option Ty)
    (locals : List LocalSlot)
    (mem : Memory)
    (k : RvalueEvalResult → Prop) :
    evalUnaryNotSymCont sc optTy locals mem k =
      k (evalUnaryNot sc optTy locals mem) := by
  rw [evalUnaryNotSymCont, SymTree.run_eq_eval, evalUnaryNotSymTree_eval]

theorem SymTree.eval_branch_leaf (c : Bool) (x y : α) :
    (SymTree.branch c (.leaf x) (.leaf y)).eval =
      match c with
      | true => x
      | false => y := by
  cases c <;> rfl

/-- Helper for the final bounds check of `evalBinOpOffsetSymTree`. -/
def finishBinOpOffsetSymTree
    (ptrVal : ProvenancePtr)
    (ptrSizeBytes : Nat)
    (allocBoundOpt : Option Nat)
    (locals₂ : List LocalSlot)
    (mem : Memory)
    (newOffset : Nat)
    (expectedPtrBytes : Nat := 8) :
    SymTree RvalueEvalResult :=
  .branch
    (match allocBoundOpt with
     | .none =>
       Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) ptrVal.offsetBytes)
     | .some bound =>
       Bool.or
         (Bool.and
           (Nat.beq bound 0)
           (Bool.and
             (Nat.beq newOffset ptrVal.offsetBytes)
             (Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) ptrVal.offsetBytes))))
         (Bool.and
           (Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) bound))
           (Bool.and
             (Nat.ble ptrVal.offsetBytes bound)
             (Nat.ble newOffset bound))))
    (.leaf (.ok (.ptr { ptrVal with offsetBytes := newOffset } ptrSizeBytes) locals₂ mem))
    (.leaf .ub)

theorem finishBinOpOffsetSymTree_eval
    (ptrVal : ProvenancePtr)
    (ptrSizeBytes : Nat)
    (allocBoundOpt : Option Nat)
    (locals₂ : List LocalSlot)
    (mem : Memory)
    (newOffset : Nat)
    (expectedPtrBytes : Nat) :
    (finishBinOpOffsetSymTree ptrVal ptrSizeBytes allocBoundOpt locals₂ mem newOffset expectedPtrBytes).eval =
      match
        (match allocBoundOpt with
         | .none =>
           Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) ptrVal.offsetBytes)
         | .some bound =>
           Bool.or
             (Bool.and
               (Nat.beq bound 0)
               (Bool.and
                 (Nat.beq newOffset ptrVal.offsetBytes)
                 (Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) ptrVal.offsetBytes))))
             (Bool.and
               (Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) bound))
               (Bool.and
                 (Nat.ble ptrVal.offsetBytes bound)
                 (Nat.ble newOffset bound))))
      with
      | true => .ok (.ptr { ptrVal with offsetBytes := newOffset } ptrSizeBytes) locals₂ mem
      | false => .ub :=
  SymTree.eval_branch_leaf _ _ _

/-- Decision-tree symbolic `evalBinOpOffset` returning `RvalueEvalResult`. -/
def evalBinOpOffsetSymTree
    (ptrVal : ProvenancePtr)
    (ptrSizeBytes : Nat)
    (offsetSc : ScalarInt)
    (elemStride : Nat)
    (allocBoundOpt : Option Nat)
    (locals₂ : List LocalSlot)
    (mem : Memory)
    (expectedPtrBytes : Nat := 8) :
    SymTree RvalueEvalResult :=
  .branch
    (Bool.and (Nat.beq ptrSizeBytes expectedPtrBytes) (Nat.beq offsetSc.sizeBytes expectedPtrBytes))
    (let modulus := scalarModulus expectedPtrBytes
     let halfMod := signedHalfModulus expectedPtrBytes
     let offsetBits := wrapScalarBits offsetSc.bits modulus
     .branch (isSignedNegative offsetBits expectedPtrBytes)
       (let countMag := Nat.sub modulus offsetBits
        let byteDelta := Nat.mul countMag elemStride
        .branch
          (Bool.and
            (Bool.not (Nat.ble halfMod byteDelta))
            (Nat.ble byteDelta ptrVal.offsetBytes))
          (finishBinOpOffsetSymTree ptrVal ptrSizeBytes allocBoundOpt locals₂ mem
            (Nat.sub ptrVal.offsetBytes byteDelta) expectedPtrBytes)
          (.leaf .ub))
       (let byteDelta := Nat.mul offsetBits elemStride
        .branch (Nat.ble halfMod byteDelta)
          (.leaf .ub)
          (let candidate := Nat.add ptrVal.offsetBytes byteDelta
           .branch (Nat.ble halfMod candidate)
             (.leaf .ub)
             (finishBinOpOffsetSymTree ptrVal ptrSizeBytes allocBoundOpt locals₂ mem
               candidate expectedPtrBytes))))
    (.leaf .ub)

theorem evalBinOpOffsetSymTree_eval
    (ptrVal : ProvenancePtr)
    (ptrSizeBytes : Nat)
    (offsetSc : ScalarInt)
    (elemStride : Nat)
    (allocBoundOpt : Option Nat)
    (locals₂ : List LocalSlot)
    (mem : Memory)
    (expectedPtrBytes : Nat := 8) :
    (evalBinOpOffsetSymTree ptrVal ptrSizeBytes offsetSc elemStride allocBoundOpt locals₂ mem expectedPtrBytes).eval =
      match evalBinOpOffset ptrVal ptrSizeBytes offsetSc elemStride allocBoundOpt expectedPtrBytes with
      | .some newPtrVal => .ok (.ptr newPtrVal ptrSizeBytes) locals₂ mem
      | .none => .ub := by
  unfold evalBinOpOffsetSymTree evalBinOpOffset SymTree.eval
  cases Bool.and (Nat.beq ptrSizeBytes expectedPtrBytes) (Nat.beq offsetSc.sizeBytes expectedPtrBytes) with
  | false => rfl
  | true =>
    dsimp only [SymTree.eval]
    cases isSignedNegative (wrapScalarBits offsetSc.bits (scalarModulus expectedPtrBytes)) expectedPtrBytes with
    | true =>
      dsimp only [SymTree.eval]
      cases Bool.and
        (Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes)
          (Nat.mul (Nat.sub (scalarModulus expectedPtrBytes) (wrapScalarBits offsetSc.bits (scalarModulus expectedPtrBytes))) elemStride)))
        (Nat.ble
          (Nat.mul (Nat.sub (scalarModulus expectedPtrBytes) (wrapScalarBits offsetSc.bits (scalarModulus expectedPtrBytes))) elemStride)
          ptrVal.offsetBytes) with
      | false => rfl
      | true =>
        dsimp only [SymTree.eval]
        rw [finishBinOpOffsetSymTree_eval]
        cases allocBoundOpt with
        | none =>
          dsimp only
          cases Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) ptrVal.offsetBytes) <;> rfl
        | some bound =>
          dsimp only
          cases
            Bool.or
              (Bool.and
                (Nat.beq bound 0)
                (Bool.and
                  (Nat.beq
                    (Nat.sub ptrVal.offsetBytes
                      (Nat.mul
                        (Nat.sub (scalarModulus expectedPtrBytes)
                          (wrapScalarBits offsetSc.bits (scalarModulus expectedPtrBytes)))
                        elemStride))
                    ptrVal.offsetBytes)
                  (Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) ptrVal.offsetBytes))))
              (Bool.and
                (Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) bound))
                (Bool.and
                  (Nat.ble ptrVal.offsetBytes bound)
                  (Nat.ble
                    (Nat.sub ptrVal.offsetBytes
                      (Nat.mul
                        (Nat.sub (scalarModulus expectedPtrBytes)
                          (wrapScalarBits offsetSc.bits (scalarModulus expectedPtrBytes)))
                        elemStride))
                    bound))) <;> rfl
    | false =>
      dsimp only [SymTree.eval]
      cases Nat.ble (signedHalfModulus expectedPtrBytes)
        (Nat.mul (wrapScalarBits offsetSc.bits (scalarModulus expectedPtrBytes)) elemStride) with
      | true => rfl
      | false =>
        dsimp only [SymTree.eval]
        cases Nat.ble (signedHalfModulus expectedPtrBytes)
          (Nat.add ptrVal.offsetBytes
            (Nat.mul (wrapScalarBits offsetSc.bits (scalarModulus expectedPtrBytes)) elemStride)) with
        | true => rfl
        | false =>
          dsimp only [SymTree.eval]
          rw [finishBinOpOffsetSymTree_eval]
          cases allocBoundOpt with
          | none =>
            dsimp only
            cases Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) ptrVal.offsetBytes) <;> rfl
          | some bound =>
            dsimp only
            cases
              Bool.or
                (Bool.and
                  (Nat.beq bound 0)
                  (Bool.and
                    (Nat.beq
                      (Nat.add ptrVal.offsetBytes
                        (Nat.mul (wrapScalarBits offsetSc.bits (scalarModulus expectedPtrBytes)) elemStride))
                      ptrVal.offsetBytes)
                    (Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) ptrVal.offsetBytes))))
                (Bool.and
                  (Bool.not (Nat.ble (signedHalfModulus expectedPtrBytes) bound))
                  (Bool.and
                    (Nat.ble ptrVal.offsetBytes bound)
                    (Nat.ble
                      (Nat.add ptrVal.offsetBytes
                        (Nat.mul (wrapScalarBits offsetSc.bits (scalarModulus expectedPtrBytes)) elemStride))
                      bound))) <;> rfl

/-- Decision-tree symbolic `evalPtrOffsetBinOp`.

Pointer arithmetic checks allocation bounds only and is independent of the Tree
Borrows permission of `ptrVal.tag` (`DIV-LM-D6-OFFSET-DISABLED-TAG`), so this
mirror has no `.disabled`-tag early UB. -/
def evalPtrOffsetBinOpSymTree
    (locals₂ : List LocalSlot)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (lhsOp : Operand)
    (ptrVal : ProvenancePtr)
    (sz : Nat)
    (offsetSc : ScalarInt) :
    SymTree RvalueEvalResult :=
  match pointeeElemByteStride localDecls layouts lhsOp with
  | .none => .leaf .ub
  | .some elemStride =>
    evalBinOpOffsetSymTree
      ptrVal
      sz
      offsetSc
      elemStride
      (ptrAllocByteBound? locals₂ mem localDecls layouts ptrVal)
      locals₂
      mem
      (layoutPointerBytes layouts)

theorem evalPtrOffsetBinOpSymTree_eval
    (locals₂ : List LocalSlot)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (lhsOp : Operand)
    (ptrVal : ProvenancePtr)
    (sz : Nat)
    (offsetSc : ScalarInt) :
    (evalPtrOffsetBinOpSymTree locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc).eval =
      evalPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc := by
  unfold evalPtrOffsetBinOpSymTree evalPtrOffsetBinOp
  cases pointeeElemByteStride localDecls layouts lhsOp with
  | none => rfl
  | some elemStride =>
    exact evalBinOpOffsetSymTree_eval ptrVal sz offsetSc elemStride _ locals₂ mem (layoutPointerBytes layouts)

/-- Decision-tree symbolic `evalRvalue`. -/
def evalRvalueSymTree
    (locals : List LocalSlot)
    (rv : Rvalue)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) : SymTree RvalueEvalResult :=
  match rv with
  | .binaryOp op lhsOp rhsOp =>
    match evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | .ok lhsVal locals₁ =>
      match evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          match op with
          | .offset =>
            .leaf (evalScalarPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp lhs rhs)
          | _ =>
            let isSigned := operandIsSigned localDecls lhsOp layouts
            evalScalarBinOpSymTree op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            evalPtrOffsetBinOpSymTree locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc
          | _ =>
            match isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
            | true =>
              match
                ptrAddressScalar?
                  locals₂
                  mem.borrows
                  mem.callerLocals
                  localDecls
                  layouts
                  (layoutPointerBytes layouts)
                  ptrVal
                  sz
                  mem.callStack
              with
              | .some lhsAddrSc =>
                evalScalarBinOpSymTree op lhsAddrSc offsetSc locals₂ mem false
              | .none => .leaf .unsupported
            | false => .leaf .unsupported
        | .scalar lhsSc, .ptr ptrVal sz =>
          match isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
          | true =>
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                localDecls
                layouts
                (layoutPointerBytes layouts)
                ptrVal
                sz
                mem.callStack
            with
            | .some rhsAddrSc =>
              evalScalarBinOpSymTree op lhsSc rhsAddrSc locals₂ mem false
            | .none => .leaf .unsupported
          | false => .leaf .unsupported
        | .ptr lhsPtr lhsSz, .ptr rhsPtr rhsSz =>
          match isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
          | true =>
            let ptrBytes := layoutPointerBytes layouts
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                localDecls
                layouts
                ptrBytes
                lhsPtr
                lhsSz
                mem.callStack,
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                localDecls
                layouts
                ptrBytes
                rhsPtr
                rhsSz
                mem.callStack
            with
            | .some lhsAddrSc, .some rhsAddrSc =>
              evalScalarBinOpSymTree op lhsAddrSc rhsAddrSc locals₂ mem false
            | _, _ => .leaf .unsupported
          | false => .leaf .unsupported
        | .aggregate lhsVar lhsFields, .aggregate rhsVar rhsFields =>
          .leaf
            (evalWidePtrAggregateRelBinOp
              op
              lhsOp
              lhsVar
              lhsFields
              rhsVar
              rhsFields
              locals₂
              mem
              localDecls
              layouts)
        | _, _ => .leaf .unsupported
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
  | .unaryOp .not op =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | .ok (.scalar sc) locals' =>
      evalUnaryNotSymTree sc (operandTy localDecls layouts op) locals' mem
    | .ok _ _ => .leaf .unsupported
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
  | _ => .leaf (evalRvalue locals rv mem localDecls layouts)

theorem evalRvalueSymTree_eval
    (locals : List LocalSlot)
    (rv : Rvalue)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    (evalRvalueSymTree locals rv mem localDecls layouts).eval =
      evalRvalue locals rv mem localDecls layouts := by
  cases rv with
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalueSymTree, evalRvalue]
    cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | ub => rfl
    | unsupported => rfl
    | ok lhsVal locals₁ =>
      dsimp only
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok rhsVal locals₂ =>
        dsimp only
        cases lhsVal with
        | scalar lhs =>
          cases rhsVal with
          | scalar rhs =>
            cases op with
            | offset => rfl
            | _ =>
              dsimp only
              exact evalScalarBinOpSymTree_eval _ lhs rhs locals₂ mem _
          | ptr ptrVal sz =>
            cases isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
            | false => rfl
            | true =>
              dsimp only
              cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
              | none => rfl
              | some rhsAddrSc =>
                exact evalScalarBinOpSymTree_eval op lhs rhsAddrSc locals₂ mem false
          | _ => rfl
        | ptr ptrVal sz =>
          cases rhsVal with
          | scalar offsetSc =>
            dsimp only
            cases op with
            | offset =>
              exact evalPtrOffsetBinOpSymTree_eval locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc
            | _ =>
              cases isPtrRelationalBinOp _ localDecls layouts lhsOp rhsOp with
              | false => rfl
              | true =>
                dsimp only
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
                | none => rfl
                | some lhsAddrSc =>
                  exact evalScalarBinOpSymTree_eval _ lhsAddrSc offsetSc locals₂ mem false
          | ptr rhsPtr rhsSz =>
            dsimp only
            cases isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
            | false => rfl
            | true =>
              dsimp only
              cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
              | none =>
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) rhsPtr rhsSz mem.callStack <;> rfl
              | some lhsAddrSc =>
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) rhsPtr rhsSz mem.callStack with
                | none => rfl
                | some rhsAddrSc =>
                  exact evalScalarBinOpSymTree_eval op lhsAddrSc rhsAddrSc locals₂ mem false
          | _ => rfl
        | aggregate lhsVar lhsFields =>
          cases rhsVal <;> rfl
        | _ => rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalueSymTree, evalRvalue]
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok v locals' =>
        cases v with
        | scalar sc => exact evalUnaryNotSymTree_eval sc _ locals' mem
        | _ => rfl
    | neg => rfl
    | ptrMetadata => rfl
  | _ => rfl

/-- Continuation-passing symbolic `evalRvalue`. -/
def evalRvalueSymCont
    (locals : List LocalSlot)
    (rv : Rvalue)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (k : RvalueEvalResult → Prop) : Prop :=
  (evalRvalueSymTree locals rv mem localDecls layouts).run k

theorem evalRvalueSymCont_eq
    (locals : List LocalSlot)
    (rv : Rvalue)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (k : RvalueEvalResult → Prop) :
    evalRvalueSymCont locals rv mem localDecls layouts k =
      k (evalRvalue locals rv mem localDecls layouts) := by
  rw [evalRvalueSymCont, SymTree.run_eq_eval, evalRvalueSymTree_eval]

/-- Direct `MirStepNode` completion of `StatementKind.assign dst rv`. -/
def finishAssignStmtNode
    (s : MachineState)
    (dst : Place)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult → MirStepNode
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok val locals₁ mem₁ =>
    match dst.projection with
    | .nil =>
      match get? locals₁ dst.local_ with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? locals₁ dst.local_ (.init val) with
        | .some locals₂ =>
          match mem₁.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrows
                mem₁.borrows dst.local_ .none (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                mem₁.borrows
                (protHead :: protTail)
                dst.local_
                .none
                .nil
                0
                0
                (length mem₁.callStack)
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrows
                  mem₁.borrows dst.local_ .none (length mem₁.callStack)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | .deref :: restProj =>
      match
        evalPlaceWrite
          locals₁
          mem₁.borrows
          dst
          val
          mem₁.activeProtectors
          localDecls
          layouts
          mem₁.callStack
      with
      | .ok locals₂ =>
        match
          Bool.or
            (derefWriteTreeUB locals₁ mem₁.borrows dst)
            (derefWriteUnionProtectorUB
              localDecls
              layouts
              locals₁
              mem₁.borrows
              mem₁.activeProtectors
              dst
              restProj
              mem₁.callStack)
        with
        | true => MirStepNode.fail .ub
        | false =>
          let borrows' :=
            invalidateDerefWriteBorrowsWithLayouts
              localDecls
              layouts
              locals₁
              mem₁.borrows
              dst
              restProj
              mem₁.callStack
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .ub =>
        match mem₁.callStack with
        | .nil =>
          match mem₁.callerLocals with
          | .nil => MirStepNode.fail .ub
          | _ :: _ =>
            match
              evalCallerPlaceWrite
                locals₁
                mem₁.callerLocals
                mem₁.borrows
                dst
                val
                mem₁.activeProtectors
            with
            | .ok callerLocals' =>
              match derefWriteTreeUB locals₁ mem₁.borrows dst with
              | true => MirStepNode.fail .ub
              | false =>
                let borrows' :=
                  invalidateDerefWriteBorrows
                    locals₁
                    mem₁.borrows
                    dst
                    restProj
                    mem₁.callerLocals
                MirStepNode.step
                  (advanceStmt
                    s
                    locals₁
                    { mem₁ with
                      borrows := borrows'
                      callerLocals := callerLocals' })
            | .ub => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported
        | _ :: _ =>
          evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts
      | .unsupported => MirStepNode.unsupported
    | proj :: rest =>
      match get? locals₁ dst.local_ with
      | .some (.init rootVal) =>
        match
          writeProjectedForLocal
            locals₁
            localDecls
            layouts
            dst.local_
            (ensureNestedFieldShells rootVal (proj :: rest))
            (proj :: rest)
            val
        with
        | .ok rootVal' =>
          match set? locals₁ dst.local_ (.init rootVal') with
          | .some locals₂ =>
            let resolvedLocalProj :=
              resolveBorrowWriteLocalProj
                localDecls
                layouts
                locals₁
                dst.local_
                (proj :: rest)
            match mem₁.activeProtectors with
            | .nil =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  mem₁.borrows
                  dst.local_
                  .none
                  resolvedLocalProj
                  0
                  0
                  (length mem₁.callStack)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
            | protHead :: protTail =>
              match
                hasProtectedWriteConflict
                  mem₁.borrows
                  (protHead :: protTail)
                  dst.local_
                  .none
                  resolvedLocalProj
                  0
                  0
                  (length mem₁.callStack)
              with
              | true => MirStepNode.fail .ub
              | false =>
                let borrows' :=
                  invalidateConflictingBorrowsAtProj
                    mem₁.borrows
                    dst.local_
                    .none
                    resolvedLocalProj
                    0
                    0
                    (length mem₁.callStack)
                MirStepNode.step
                  (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | .none => MirStepNode.fail .ub
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
      | .some .uninit =>
        match uninitFieldWriteShell? localDecls layouts dst.local_ proj rest with
        | .some rootVal =>
          match
            writeProjectedForLocal
              locals₁
              localDecls
              layouts
              dst.local_
              rootVal
              (proj :: rest)
              val
          with
          | .ok rootVal' =>
            match set? locals₁ dst.local_ (.init rootVal') with
            | .some locals₂ =>
              let resolvedLocalProj :=
                resolveBorrowWriteLocalProj
                  localDecls
                  layouts
                  locals₁
                  dst.local_
                  (proj :: rest)
              match mem₁.activeProtectors with
              | .nil =>
                let borrows' :=
                  invalidateConflictingBorrowsAtProj
                    mem₁.borrows
                    dst.local_
                    .none
                    resolvedLocalProj
                    0
                    0
                    (length mem₁.callStack)
                MirStepNode.step
                  (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
              | protHead :: protTail =>
                match
                  hasProtectedWriteConflict
                    mem₁.borrows
                    (protHead :: protTail)
                    dst.local_
                    .none
                    resolvedLocalProj
                    0
                    0
                    (length mem₁.callStack)
                with
                | true => MirStepNode.fail .ub
                | false =>
                  let borrows' :=
                    invalidateConflictingBorrowsAtProj
                      mem₁.borrows
                      dst.local_
                      .none
                      resolvedLocalProj
                      0
                      0
                      (length mem₁.callStack)
                  MirStepNode.step
                    (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
            | .none => MirStepNode.fail .ub
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
        | .none => MirStepNode.fail .ub
      | .some .dead => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub

/-- Decision-tree symbolic `evalStmt`. -/
def evalStmtSymTree
    (s : MachineState)
    (stmt : Statement)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) : SymTree MirStepNode :=
  match stmt.kind with
  | .assign dst rv =>
    (evalRvalueSymTree s.frame.locals rv s.memory localDecls layouts).bind
      (fun res => .leaf (finishAssignStmtNode s dst localDecls layouts res))
  | _ => .leaf (evalStmt s stmt localDecls layouts)

theorem evalStmtSymTree_eval
    (s : MachineState)
    (stmt : Statement)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    (evalStmtSymTree s stmt localDecls layouts).eval =
      evalStmt s stmt localDecls layouts := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    dsimp only [evalStmtSymTree, evalStmt]
    rw [SymTree.bind_eval, evalRvalueSymTree_eval]
    cases evalRvalue s.frame.locals rv s.memory localDecls layouts <;> rfl
  | _ => rfl

/-- Continuation-passing symbolic `evalStmt`. -/
def evalStmtSymCont
    (s : MachineState)
    (stmt : Statement)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (cont : MirExecState → Prop)
    (post : MirOutcome → Prop) : Prop :=
  (evalStmtSymTree s stmt localDecls layouts).run (evalNodeWP cont post)

theorem evalStmtSymCont_eq
    (s : MachineState)
    (stmt : Statement)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (cont : MirExecState → Prop)
    (post : MirOutcome → Prop) :
    evalStmtSymCont s stmt localDecls layouts cont post =
      evalNodeWP cont post (evalStmt s stmt localDecls layouts) := by
  rw [evalStmtSymCont, SymTree.run_eq_eval, evalStmtSymTree_eval]

/-- Decision-tree symbolic `lookupSwitchTarget`. -/
def lookupSwitchTargetTree
    (val : Nat)
    (branches : List (Nat × BasicBlockIdx))
    (otherwise : BasicBlockIdx) : SymTree BasicBlockIdx :=
  match branches with
  | .nil => .leaf otherwise
  | (branchVal, target) :: rest =>
    .branch (Nat.beq val branchVal)
      (.leaf target)
      (lookupSwitchTargetTree val rest otherwise)

theorem lookupSwitchTargetTree_eval
    (val : Nat)
    (branches : List (Nat × BasicBlockIdx))
    (otherwise : BasicBlockIdx) :
    (lookupSwitchTargetTree val branches otherwise).eval =
      lookupSwitchTarget val branches otherwise := by
  induction branches with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨branchVal, target⟩
    dsimp only [lookupSwitchTargetTree, lookupSwitchTarget]
    cases Nat.beq val branchVal with
    | true => rfl
    | false => exact ih

/-- Continuation-passing `lookupSwitchTarget`. -/
def lookupSwitchTargetCont
    (val : Nat)
    (branches : List (Nat × BasicBlockIdx))
    (otherwise : BasicBlockIdx)
    (k : BasicBlockIdx → Prop) : Prop :=
  (lookupSwitchTargetTree val branches otherwise).run k

theorem lookupSwitchTargetCont_eq
    (val : Nat)
    (branches : List (Nat × BasicBlockIdx))
    (otherwise : BasicBlockIdx)
    (k : BasicBlockIdx → Prop) :
    lookupSwitchTargetCont val branches otherwise k =
      k (lookupSwitchTarget val branches otherwise) := by
  rw [lookupSwitchTargetCont, SymTree.run_eq_eval, lookupSwitchTargetTree_eval]

/-- Decision-tree symbolic `evalTerminator`. -/
def evalTerminatorSymTree
    (s : MachineState)
    (term : Terminator)
    (currentBody : CapturedMir) : SymTree MirStepNode :=
  match term.kind with
  | .switchInt discr targets =>
    match
      evalOperand
        s.frame.locals
        discr
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        (callStack := s.memory.callStack)
    with
    | .ok (.scalar sc) locals' =>
      (lookupSwitchTargetTree sc.bits targets.branches targets.otherwise).bind
        (fun target =>
          .leaf
            (.vis (.inr (.inl (.emit (.event sc.bits))))
              (fun _ =>
                .running {
                  s with
                  frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
                })))
    | .ok _ _ => .leaf (MirStepNode.fail .ub)
    | .ub => .leaf (MirStepNode.fail .ub)
    | .unsupported => .leaf MirStepNode.unsupported
  | .assert cond expected target unwind =>
    match
      evalOperand
        s.frame.locals
        cond
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        (callStack := s.memory.callStack)
    with
    | .ok (.scalar sc) locals' =>
      let expectedBit := match expected with | true => 1 | false => 0
      .branch (Nat.beq sc.bits expectedBit)
        (.leaf
          (MirStepNode.step {
            s with
            frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
          }))
        (.leaf
          (match applyUnwindAction s locals' s.memory unwind with
          | .running nextState => MirStepNode.step nextState
          | .halted out => .ret out
          | .faulted fk => MirStepNode.fail fk))
    | .ok _ _ => .leaf (MirStepNode.fail .ub)
    | .ub => .leaf (MirStepNode.fail .ub)
    | .unsupported => .leaf MirStepNode.unsupported
  | _ => .leaf (evalTerminator s term (some currentBody))

theorem evalTerminatorSymTree_eval
    (s : MachineState)
    (term : Terminator)
    (currentBody : CapturedMir) :
    (evalTerminatorSymTree s term currentBody).eval =
      evalTerminator s term (some currentBody) := by
  rcases term with ⟨kind, span⟩
  cases kind with
  | switchInt discr targets =>
    dsimp only [evalTerminatorSymTree, evalTerminator]
    cases evalOperand s.frame.locals discr s.memory.borrows s.memory.globals currentBody.layouts s.memory.callerLocals
        (callStack := s.memory.callStack) with
    | ub => rfl
    | unsupported => rfl
    | ok v locals' =>
      cases v with
      | scalar sc =>
        dsimp only
        rw [SymTree.bind_eval, lookupSwitchTargetTree_eval]
        rfl
      | _ => rfl
  | assert cond expected target unwind =>
    dsimp only [evalTerminatorSymTree, evalTerminator]
    cases evalOperand s.frame.locals cond s.memory.borrows s.memory.globals currentBody.layouts s.memory.callerLocals
        (callStack := s.memory.callStack) with
    | ub => rfl
    | unsupported => rfl
    | ok v locals' =>
      cases v with
      | scalar sc =>
        dsimp only
        cases Nat.beq sc.bits (match expected with | true => 1 | false => 0) <;> rfl
      | _ => rfl
  | _ => rfl

/-- Continuation-passing symbolic `evalTerminator`. -/
def evalTerminatorSymCont
    (s : MachineState)
    (term : Terminator)
    (currentBody : CapturedMir)
    (cont : MirExecState → Prop)
    (post : MirOutcome → Prop) : Prop :=
  (evalTerminatorSymTree s term currentBody).run (evalNodeWP cont post)

theorem evalTerminatorSymCont_eq
    (s : MachineState)
    (term : Terminator)
    (currentBody : CapturedMir)
    (cont : MirExecState → Prop)
    (post : MirOutcome → Prop) :
    evalTerminatorSymCont s term currentBody cont post =
      evalNodeWP cont post (evalTerminator s term (some currentBody)) := by
  rw [evalTerminatorSymCont, SymTree.run_eq_eval, evalTerminatorSymTree_eval]

/-- One-step decision-tree symbolic MIR transition from `MachineState`. -/
def stepMirSymTree
    (body : CapturedMir)
    (s : MachineState) : SymTree MirStepNode :=
  let currentBody := s.memory.activeCallee.getD body
  match currentBody.phase with
  | .other _ => .leaf MirStepNode.unsupported
  | _ =>
    match get? currentBody.basicBlocks s.frame.blockIdx with
    | none => .leaf (MirStepNode.fail .ub)
    | some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | some stmt =>
        evalStmtSymTree s stmt currentBody.localDecls currentBody.layouts
      | none =>
        if s.frame.stmtIdx == length bb.statements then
          evalTerminatorSymTree s bb.terminator currentBody
        else
          .leaf (MirStepNode.fail .ub)

theorem stepMirSymTree_eval
    (body : CapturedMir)
    (s : MachineState) :
    (stepMirSymTree body s).eval = stepMirFn body s := by
  dsimp only [stepMirSymTree, stepMirFn]
  cases (s.memory.activeCallee.getD body).phase with
  | other _ => rfl
  | _ =>
    all_goals
      dsimp only
      cases get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
      | none => rfl
      | some bb =>
        dsimp only
        cases get? bb.statements s.frame.stmtIdx with
        | some stmt =>
          exact evalStmtSymTree_eval s stmt _ _
        | none =>
          dsimp only
          split
          · exact evalTerminatorSymTree_eval s bb.terminator _
          · rfl

/-- One-step continuation-passing symbolic MIR transition from `MachineState`. -/
def stepMirSymCont
    (body : CapturedMir)
    (s : MachineState)
    (cont : MirExecState → Prop)
    (post : MirOutcome → Prop) : Prop :=
  (stepMirSymTree body s).run (evalNodeWP cont post)

theorem stepMirSymCont_eq
    (body : CapturedMir)
    (s : MachineState)
    (cont : MirExecState → Prop)
    (post : MirOutcome → Prop) :
    stepMirSymCont body s cont post =
      evalNodeWP cont post (stepMirFn body s) := by
  rw [stepMirSymCont, SymTree.run_eq_eval, stepMirSymTree_eval]

/-- One-step decision-tree symbolic MIR transition from `MirExecState`. -/
def stepMirExecSymTree
    (body : CapturedMir)
    (st : MirExecState) : SymTree MirStepNode :=
  match st with
  | .running s => stepMirSymTree body s
  | .halted out => .leaf (.ret out)
  | .faulted fk => .leaf (MirStepNode.fail fk)

theorem stepMirExecSymTree_eval
    (body : CapturedMir)
    (st : MirExecState) :
    (stepMirExecSymTree body st).eval = stepMirState body st := by
  cases st with
  | running s => exact stepMirSymTree_eval body s
  | halted _ => rfl
  | faulted _ => rfl

/-- One-step continuation-passing symbolic MIR transition from `MirExecState`. -/
def stepMirExecSymCont
    (body : CapturedMir)
    (st : MirExecState)
    (cont : MirExecState → Prop)
    (post : MirOutcome → Prop) : Prop :=
  (stepMirExecSymTree body st).run (evalNodeWP cont post)

theorem stepMirExecSymCont_eq
    (body : CapturedMir)
    (st : MirExecState)
    (cont : MirExecState → Prop)
    (post : MirOutcome → Prop) :
    stepMirExecSymCont body st cont post =
      evalNodeWP cont post (stepMirState body st) := by
  rw [stepMirExecSymCont, SymTree.run_eq_eval, stepMirExecSymTree_eval]

/--
Single-pass fuel-bounded symbolic WP over `MirExecState`: evaluates to `False`
on fuel exhaustion (`0`) or fault, and `post out` on halted outcomes.
-/
def wpMirExecSym
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTree
      (fun st' => wpMirExecSym fuel' body st' post)
      post
      (stepMirExecSymTree body st)

/--
Single-pass fuel-bounded symbolic WP over `MachineState`, propositionally
identical to `wpMirBounded` while avoiding exponential prefix re-evaluation on
symbolic branches.
-/
def wpMirSym
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecSym fuel body (.running s) post

theorem wpMirExecSym_eq_wpCoalBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) :
    wpMirExecSym fuel body st post =
      wpCoalBounded fuel mirDefaultWP (stepMirState body)
        (fun out _ => post out) st PUnit.unit := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    unfold wpMirExecSym wpCoalBounded
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
    cases stepMirState body st with
    | ret _ => rfl
    | tau st' => exact ih st'
    | vis i k =>
      dsimp only []
      congr 1
      funext o u
      cases u
      exact ih (k o)

/-- Exact equality between single-pass `wpMirSym` and `Lower.wpMirBounded`. -/
theorem wpMirSym_eq_wpMirBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) :
    wpMirSym fuel body s post = wpMirBounded fuel body s post :=
  wpMirExecSym_eq_wpCoalBounded fuel body (.running s) post

/-- Total-correctness (`DWP mirDefaultWP`) soundness of `wpMirSym`. -/
theorem dwp_of_wpMirSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : wpMirSym fuel body s post) :
    DWP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit := by
  rw [wpMirSym_eq_wpMirBounded] at h
  exact dwp_cofix_of_wpCoalBounded fuel h

/-- Partial-correctness (`DWLP mirDefaultWP`) soundness of `wpMirSym`. -/
theorem dwlp_of_wpMirSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : wpMirSym fuel body s post) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  (dwp_of_wpMirSym h).toDWLP

theorem wpMirExecSym_mono
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirExecSym fuel body st P) :
    wpMirExecSym fuel body st Q := by
  rw [wpMirExecSym_eq_wpCoalBounded] at h ⊢
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpCoalBounded at h ⊢
    cases h_st : stepMirState body st with
    | ret out =>
      simp only [h_st] at h ⊢
      exact h_imp out h
    | tau st' =>
      simp only [h_st] at h ⊢
      exact ih h
    | vis i k =>
      simp only [h_st] at h ⊢
      exact mirDefaultWP.mono (fun _ _ hw => ih hw) h

theorem wpMirSym_mono
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirSym fuel body s P) :
    wpMirSym fuel body s Q :=
  wpMirExecSym_mono h_imp h

/--
Dual fuel-bounded symbolic evaluator (`0 => True`) for sound precondition
inversion of `DWLP mirDefaultWP` and `MirBoolPredicateHolds` hypotheses.
-/
def wpMirExecOrExhaustedSym
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => True
  | fuel' + 1 =>
    evalSymNodeTree
      (fun st' => wpMirExecOrExhaustedSym fuel' body st' post)
      post
      (stepMirExecSymTree body st)

/-- Dual fuel-bounded symbolic evaluator over `MachineState`. -/
def wpMirOrExhaustedSym
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecOrExhaustedSym fuel body (.running s) post

/--
Necessity / inversion bridge: every `DWLP mirDefaultWP` hypothesis implies
`wpMirExecOrExhaustedSym` at any finite fuel budget `fuel`.
-/
theorem wpMirExecOrExhaustedSym_of_dwlp
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop)
    (h_dwlp :
      DWLP mirDefaultWP (ITree.cofix (stepMirState body) st)
        (fun out _ => post out) PUnit.unit) :
    wpMirExecOrExhaustedSym fuel body st post := by
  induction fuel generalizing st with
  | zero => exact True.intro
  | succ fuel' ih =>
    unfold wpMirExecOrExhaustedSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
    rw [DWLP.unfold_eq, ITree.observe_cofix] at h_dwlp
    cases h_step : stepMirState body st with
    | ret out =>
      rw [h_step] at h_dwlp
      dsimp only [ITreeF.map] at h_dwlp ⊢
      exact h_dwlp
    | tau st' =>
      rw [h_step] at h_dwlp
      dsimp only [ITreeF.map] at h_dwlp ⊢
      exact ih st' h_dwlp
    | vis i k =>
      rw [h_step] at h_dwlp
      dsimp only [ITreeF.map] at h_dwlp ⊢
      exact mirDefaultWP.mono (fun o _ hd => ih (k o) hd) h_dwlp

theorem wpMirOrExhaustedSym_of_dwlp
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop)
    (h_dwlp :
      DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit) :
    wpMirOrExhaustedSym fuel body s post :=
  wpMirExecOrExhaustedSym_of_dwlp fuel body (.running s) post h_dwlp

/--
When `body` terminates within `fuel` steps (`wpMirExecSym fuel body st (fun _ => True)`),
the dual `wpMirExecOrExhaustedSym` coincides with `wpMirExecSym`.
-/
theorem wpMirExecSym_of_wpMirExecOrExhaustedSym
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {post : MirOutcome → Prop}
    (h_term : wpMirExecSym fuel body st (fun _ => True))
    (h_hold : wpMirExecOrExhaustedSym fuel body st post) :
    wpMirExecSym fuel body st post := by
  induction fuel generalizing st with
  | zero => exact False.elim h_term
  | succ fuel' ih =>
    unfold wpMirExecSym at h_term ⊢
    unfold wpMirExecOrExhaustedSym at h_hold
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h_term h_hold ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      rw [h_step] at h_term h_hold
      dsimp only [] at h_term h_hold ⊢
      exact h_hold
    | tau st' =>
      rw [h_step] at h_term h_hold
      dsimp only [] at h_term h_hold ⊢
      exact ih h_term h_hold
    | vis i k =>
      rw [h_step] at h_term h_hold
      dsimp only [] at h_term h_hold ⊢
      rcases i with f | (e | c)
      · exact False.elim h_term
      · cases e
        exact ih h_term h_hold
      · cases c
        intro ans
        exact ih (h_term ans) (h_hold ans)

theorem wpMirSym_of_wpMirOrExhaustedSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h_term : wpMirSym fuel body s (fun _ => True))
    (h_hold : wpMirOrExhaustedSym fuel body s post) :
    wpMirSym fuel body s post :=
  wpMirExecSym_of_wpMirExecOrExhaustedSym h_term h_hold

/-! ## 4. `@[simp]` Lemmas for One-Pass Branch & Scalar Collapsing -/

@[simp]
theorem bool_match_same (b : Bool) (P : Prop) :
    (match b with | true => P | false => P) ↔ P := by
  cases b <;> simp

@[simp]
theorem bool_match_false_left (b : Bool) (P : Prop) :
    (match b with | true => False | false => P) ↔ (b = false ∧ P) := by
  cases b <;> simp

@[simp]
theorem bool_match_false_right (b : Bool) (P : Prop) :
    (match b with | true => P | false => False) ↔ (b = true ∧ P) := by
  cases b <;> simp

@[simp]
theorem bool_match_true_left (b : Bool) (P : Prop) :
    (match b with | true => True | false => P) ↔ (b = false → P) := by
  cases b <;> simp

@[simp]
theorem bool_match_true_right (b : Bool) (P : Prop) :
    (match b with | true => P | false => True) ↔ (b = true → P) := by
  cases b <;> simp

theorem bool_match_prop_iff (b : Bool) (P Q : Prop) :
    (match b with | true => P | false => Q) ↔
      ((b = true → P) ∧ (b = false → Q)) := by
  cases b <;> simp

@[simp]
theorem boolToScalar_true :
    boolToScalar true = { bits := 1, sizeBytes := 1 } := rfl

@[simp]
theorem boolToScalar_false :
    boolToScalar false = { bits := 0, sizeBytes := 1 } := rfl

@[simp]
theorem boolToScalar_sizeBytes (b : Bool) :
    (boolToScalar b).sizeBytes = 1 := by
  cases b <;> rfl

@[simp]
theorem boolToScalar_bits_beq_zero (b : Bool) :
    Nat.beq (boolToScalar b).bits 0 = !b := by
  cases b <;> rfl

@[simp]
theorem boolToScalar_bits_beq_one (b : Bool) :
    Nat.beq (boolToScalar b).bits 1 = b := by
  cases b <;> rfl

@[simp]
theorem boolToScalar_eq_true_iff (b : Bool) :
    Value.scalar (boolToScalar b) = Value.scalar { bits := 1, sizeBytes := 1 } ↔
      b = true := by
  cases b <;> simp

@[simp]
theorem boolToScalar_eq_false_iff (b : Bool) :
    Value.scalar (boolToScalar b) = Value.scalar { bits := 0, sizeBytes := 1 } ↔
      b = false := by
  cases b <;> simp

@[simp]
theorem scalarModulus_zero : scalarModulus 0 = 1 := rfl

@[simp]
theorem scalarModulus_one : scalarModulus 1 = 256 := rfl

@[simp]
theorem scalarModulus_two : scalarModulus 2 = 65536 := rfl

@[simp]
theorem scalarModulus_four : scalarModulus 4 = 4294967296 := rfl

@[simp]
theorem scalarModulus_eight : scalarModulus 8 = 18446744073709551616 := rfl

@[simp]
theorem nat_ble_eq_true_iff (a b : Nat) :
    Nat.ble a b = true ↔ a ≤ b :=
  Iff.of_eq Nat.ble_eq

@[simp]
theorem nat_ble_eq_false_iff (a b : Nat) :
    Nat.ble a b = false ↔ b < a := by
  cases h : Nat.ble a b with
  | true =>
    have hle : a ≤ b := Eq.mp Nat.ble_eq h
    exact ⟨(fun hf => nomatch hf), fun hlt => absurd hlt (Nat.not_lt.2 hle)⟩
  | false =>
    have hnle : ¬ a ≤ b := fun hle => by
      rw [Eq.mpr Nat.ble_eq hle] at h
      nomatch h
    exact ⟨fun _ => Nat.lt_of_not_le hnle, fun _ => rfl⟩

@[simp]
theorem wrapScalarBits_eq_mod (val modulus : Nat) :
    wrapScalarBits val modulus = val % modulus := by
  unfold wrapScalarBits
  cases h : Nat.ble modulus val
  · exact (Nat.mod_eq_of_lt ((nat_ble_eq_false_iff modulus val).1 h)).symm
  · rfl

@[simp]
theorem nat_beq_eq_true_iff (a b : Nat) :
    Nat.beq a b = true ↔ a = b :=
  Iff.of_eq Nat.beq_eq

@[simp]
theorem nat_beq_eq_false_iff (a b : Nat) :
    Nat.beq a b = false ↔ a ≠ b := by
  cases h : Nat.beq a b with
  | true =>
    have heq : a = b := Eq.mp Nat.beq_eq h
    exact ⟨(fun hf => nomatch hf), fun hne => absurd heq hne⟩
  | false =>
    have hne : a ≠ b := fun heq => by
      rw [Eq.mpr Nat.beq_eq heq] at h
      nomatch h
    exact ⟨fun _ => hne, fun _ => rfl⟩

@[simp]
theorem wrapScalarBits_of_lt {val modulus : Nat} (h : val < modulus) :
    wrapScalarBits val modulus = val := by
  unfold wrapScalarBits
  rw [(nat_ble_eq_false_iff modulus val).2 h]

theorem wrapScalarBits_of_ble_false
    (val modulus : Nat) (h : Nat.ble modulus val = false) :
    wrapScalarBits val modulus = val := by
  unfold wrapScalarBits
  rw [h]

/-! ## 5. Computable Fast-Path Checkers & Bidirectional `MirBoolPredicateHolds` -/

/--
Computable bounded boolean checker for `MirBoolPredicateHolds`: returns `true`
when `specBody` halts normally with `true` (`.scalar ⟨1, 1⟩`) or unwinds safely
within `fuel` steps without external calls or faults.
-/
def checkMirBoolExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret (.normal (.scalar { bits := 1, sizeBytes := 1 }, _)) => true
    | .ret (.normal _) => false
    | .ret .panic => true
    | .ret .abort => true
    | .tau st' => checkMirBoolExecBounded fuel' body st'
    | .vis (.inl _) _ => false
    | .vis (.inr (.inl _)) k => checkMirBoolExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr _)) _ => false

/--
Computable bounded boolean checker for `MirBoolPredicateHoldsWithCallees`:
returns `true` when `specBody` halts normally with `true` (`.scalar ⟨1, 1⟩`) or
unwinds safely within `fuel` steps with linked `callees`.
-/
def checkMirBoolWithCalleesBounded
    (fuel : Nat)
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value) : Bool :=
  checkMirBoolExecBounded
    fuel
    specBody
    (.running (initMachineStateWithCallees specBody args callees))

/-- Computable bounded boolean checker for `MirBoolPredicateHolds specBody args`. -/
def checkMirBoolBounded
    (fuel : Nat) (specBody : CapturedMir) (args : List Value) : Bool :=
  checkMirBoolWithCalleesBounded fuel specBody .nil args

private theorem wpCoalBounded_of_checkMirBoolExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h : checkMirBoolExecBounded fuel body st = true) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body)
      (fun out _ =>
        ∀ retVal mem',
          out = .normal (retVal, mem') →
          retVal = .scalar { bits := 1, sizeBytes := 1 })
      st PUnit.unit := by
  induction fuel generalizing st with
  | zero => nomatch h
  | succ fuel' ih =>
    unfold checkMirBoolExecBounded at h
    unfold wpCoalBounded
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h ⊢
      cases out with
      | normal p =>
        rcases p with ⟨retVal, mem'⟩
        cases retVal with
        | scalar sc =>
          rcases sc with ⟨bits, sz⟩
          cases bits with
          | zero => nomatch h
          | succ b' =>
            cases b' with
            | zero =>
              cases sz with
              | zero => nomatch h
              | succ s' =>
                cases s' with
                | zero =>
                  intro r m h_eq
                  injection h_eq with h_pair
                  injection h_pair with h_r _
                  exact h_r.symm
                | succ _ => nomatch h
            | succ _ => nomatch h
        | _ => nomatch h
      | panic => intro _ _ h_eq; nomatch h_eq
      | abort => intro _ _ h_eq; nomatch h_eq
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih st' h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · nomatch h
      · cases e
        exact ih (k PUnit.unit) h
      · nomatch h

/--
Discharge `MirBoolPredicateHoldsWithCallees specBody callees args` on concrete
inputs by kernel `rfl`
(`checkMirBoolWithCalleesBounded fuel specBody callees args = true`).
-/
theorem mirBoolPredicateHoldsWithCallees_of_checkBounded
    (fuel : Nat)
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value)
    (h :
      checkMirBoolWithCalleesBounded fuel specBody callees args = true := by
        rfl) :
    MirBoolPredicateHoldsWithCallees specBody callees args :=
  mirBoolPredicateHoldsWithCallees_of_bounded fuel specBody callees args
    (wpCoalBounded_of_checkMirBoolExecBounded fuel specBody _ h)

/--
Discharge `MirBoolPredicateHolds specBody args` on concrete inputs by kernel
`rfl` (`checkMirBoolBounded fuel specBody args = true`).
-/
theorem mirBoolPredicateHolds_of_checkBounded
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h : checkMirBoolBounded fuel specBody args = true := by rfl) :
    MirBoolPredicateHolds specBody args :=
  mirBoolPredicateHoldsWithCallees_of_checkBounded fuel specBody .nil args h

/-- Compatibility alias used by Tutor proof modules (`rfl`-discharged). -/
abbrev mirBoolPredicateHolds_of_wp_bounded :=
  @mirBoolPredicateHolds_of_checkBounded

/--
Single-pass symbolic sufficiency proposition for `MirBoolPredicateHoldsWithCallees`:
`specBody` executes with linked `callees` within `fuel` steps without UB and
returns `true` (`.scalar ⟨1, 1⟩`) on every normal return path.
-/
def wpMirBoolWithCalleesSym
    (fuel : Nat)
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value) : Prop :=
  wpMirSym fuel specBody (initMachineStateWithCallees specBody args callees)
    (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))

/--
Single-pass symbolic necessity / inversion proposition for
`MirBoolPredicateHoldsWithCallees`: at any finite `fuel`,
`MirBoolPredicateHoldsWithCallees specBody callees args` unfolds into a pure
`Prop` formula over `args`.
-/
def holdBoolMirWithCalleesSym
    (fuel : Nat)
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value) : Prop :=
  wpMirOrExhaustedSym fuel specBody
    (initMachineStateWithCallees specBody args callees)
    (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))

/-- Prove `MirBoolPredicateHoldsWithCallees specBody callees args` from symbolic `wpMirBoolWithCalleesSym`. -/
theorem mirBoolPredicateHoldsWithCallees_of_wpMirSym
    (fuel : Nat)
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value)
    (h : wpMirBoolWithCalleesSym fuel specBody callees args) :
    MirBoolPredicateHoldsWithCallees specBody callees args := by
  have h' :
      wpMirSym fuel specBody (initMachineStateWithCallees specBody args callees)
        (fun out =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 }) :=
    wpMirSym_mono (fun out ho => (mirSafePost_iff_forall_normal _ out).1 ho) h
  rw [wpMirSym_eq_wpMirBounded] at h'
  exact mirBoolPredicateHoldsWithCallees_of_bounded fuel specBody callees args h'

/--
Invert a `MirBoolPredicateHoldsWithCallees specBody callees args` hypothesis into
a single-pass symbolic `holdBoolMirWithCalleesSym` formula.
-/
theorem holdBoolMirWithCalleesSym_of_mirBoolPredicateHoldsWithCallees
    (fuel : Nat)
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value)
    (h : MirBoolPredicateHoldsWithCallees specBody callees args) :
    holdBoolMirWithCalleesSym fuel specBody callees args := by
  have h_dwlp := (mirBoolPredicateHoldsWithCallees_iff_dwlp specBody callees args).1 h
  have h_safe :
      DWLP mirDefaultWP (mirCallTreeWithCallees specBody args callees)
        (fun out _ =>
          mirSafePost
            (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }) out)
        PUnit.unit :=
    DWLP.mono
      (fun out _ ho => (mirSafePost_iff_forall_normal _ out).2 ho)
      h_dwlp
  exact wpMirOrExhaustedSym_of_dwlp fuel specBody
    (initMachineStateWithCallees specBody args callees) _ h_safe

/--
Exact equivalence between `MirBoolPredicateHoldsWithCallees specBody callees args`
and single-pass symbolic `wpMirBoolWithCalleesSym fuel specBody callees args`
whenever `specBody` terminates without UB within `fuel` steps on `args`.
-/
theorem mirBoolPredicateHoldsWithCallees_iff_wpMirBoolWithCalleesSym
    (fuel : Nat)
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value)
    (h_term :
      wpMirSym fuel specBody
        (initMachineStateWithCallees specBody args callees)
        (fun _ => True)) :
    MirBoolPredicateHoldsWithCallees specBody callees args ↔
      wpMirBoolWithCalleesSym fuel specBody callees args :=
  ⟨fun h =>
    wpMirSym_of_wpMirOrExhaustedSym h_term
      (holdBoolMirWithCalleesSym_of_mirBoolPredicateHoldsWithCallees
        fuel specBody callees args h),
   mirBoolPredicateHoldsWithCallees_of_wpMirSym fuel specBody callees args⟩

/--
Single-pass symbolic sufficiency proposition for `MirBoolPredicateHolds`:
`specBody` executes within `fuel` steps without UB and returns `true`
(`.scalar ⟨1, 1⟩`) on every normal return path.
-/
def wpMirBoolSym
    (fuel : Nat) (specBody : CapturedMir) (args : List Value) : Prop :=
  wpMirBoolWithCalleesSym fuel specBody .nil args

/--
Single-pass symbolic necessity / inversion proposition for `MirBoolPredicateHolds`:
at any finite `fuel`, `MirBoolPredicateHolds specBody args` unfolds into a pure
`Prop` formula over `args`.
-/
def holdBoolMirSym
    (fuel : Nat) (specBody : CapturedMir) (args : List Value) : Prop :=
  holdBoolMirWithCalleesSym fuel specBody .nil args

/-- Prove `MirBoolPredicateHolds specBody args` from symbolic `wpMirBoolSym`. -/
theorem mirBoolPredicateHolds_of_wpMirSym
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h : wpMirBoolSym fuel specBody args) :
    MirBoolPredicateHolds specBody args :=
  mirBoolPredicateHoldsWithCallees_of_wpMirSym fuel specBody .nil args h

/--
Invert a `MirBoolPredicateHolds specBody args` hypothesis (such as a `#[spec]`
`requires` clause) into a single-pass symbolic `holdBoolMirSym` formula.
-/
theorem holdBoolMirSym_of_mirBoolPredicateHolds
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h : MirBoolPredicateHolds specBody args) :
    holdBoolMirSym fuel specBody args :=
  holdBoolMirWithCalleesSym_of_mirBoolPredicateHoldsWithCallees
    fuel specBody .nil args h

/--
Exact equivalence between `MirBoolPredicateHolds specBody args` and single-pass
symbolic `wpMirBoolSym fuel specBody args` whenever `specBody` terminates
without UB within `fuel` steps on `args`.
-/
theorem mirBoolPredicateHolds_iff_wpMirBoolSym
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h_term :
      wpMirSym fuel specBody (initMachineState specBody args) (fun _ => True)) :
    MirBoolPredicateHolds specBody args ↔ wpMirBoolSym fuel specBody args :=
  mirBoolPredicateHoldsWithCallees_iff_wpMirBoolWithCalleesSym
    fuel specBody .nil args h_term

/-! ## 6. Certificate Discharge Combinators (`Claim`, `TotalClaim`, `StatefulClaim`) -/

/--
Discharge a stateless `VerificationResult c` via single-pass symbolic evaluation
(`mirSafePost`: panics/unwinds are safe defined behavior; normal returns must
satisfy `c.post args retVal`).
-/
theorem verifyMirSafeSym
    (c : Claim) (fuel : Nat)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        wpMirSym fuel c.body
          (initMachineStateWithCallees c.body args c.callees)
          (mirSafePost (fun retVal _ => c.post args retVal))) :
    VerificationResult c := by
  refine verifyMirBounded c fuel (fun args h_pre => ?_)
  rw [← wpMirSym_eq_wpMirBounded]
  exact wpMirSym_mono
    (fun out ho => (mirSafePost_iff_forall_normal _ out).1 ho)
    (h_wp args h_pre)

/-- Primary alias for `verifyMirSafeSym`. -/
abbrev verifyMirSym := @verifyMirSafeSym

/-- Compatibility alias for Tutor / scaffold safe-panic proofs. -/
abbrev verifyByWPSafe := @verifyMirSafeSym

/--
Discharge a stateless `VerificationResult c` via panic-forbidding single-pass
symbolic evaluation (`mirNormalPost`: requires normal return satisfying `c.post`
and rejects `.panic` / `.abort` as well as UB).
-/
theorem verifyMirNoPanicSym
    (c : Claim) (fuel : Nat)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        wpMirSym fuel c.body
          (initMachineStateWithCallees c.body args c.callees)
          (mirNormalPost (fun retVal _ => c.post args retVal))) :
    VerificationResult c :=
  verifyMirSafeSym c fuel (fun args h_pre =>
    wpMirSym_mono (fun _ => mirNormalPost_imp_mirSafePost) (h_wp args h_pre))

/-- Compatibility alias for Tutor / scaffold panic-forbidding proofs. -/
abbrev verifyByWP := @verifyMirNoPanicSym

/--
Discharge a stateless `VerificationResult c` when `c.pre args` pins `args` to
`expectedArgs`.
-/
theorem dischargeStatelessEq
    (c : Claim)
    (fuel : Nat)
    (expectedArgs : List Value)
    (h_pre : ∀ args : List Value, c.pre args → args = expectedArgs)
    (h_eval :
      wpMirSym fuel c.body
        (initMachineStateWithCallees c.body expectedArgs c.callees)
        (mirNormalPost (fun retVal _ => c.post expectedArgs retVal))) :
    VerificationResult c :=
  verifyMirNoPanicSym c fuel (fun args hp => by
    rw [h_pre args hp]
    exact h_eval)

/--
Discharge a total-correctness `TotalVerificationResult c` via single-pass
symbolic evaluation (`mirNormalPost`: establishes `TreeSafe`, `Productive`,
`¬ MayDiverge`, absence of panics/aborts, and `c.post` on all returns).
-/
theorem verifyTotalMirSym
    (c : TotalClaim) (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirSym fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (mirNormalPost (c.post args mem))) :
    TotalVerificationResult c := by
  refine verifyTotalMirBounded c fuel (fun args mem h_pre => ?_)
  rw [← wpMirSym_eq_wpMirBounded]
  exact wpMirSym_mono
    (fun out ho => (mirNormalPost_iff_exists_normal _ out).1 ho)
    (h_wp args mem h_pre)

/--
Discharge a stateful `StatefulVerificationResult c` via single-pass symbolic
evaluation (`mirSafePost`).
-/
theorem verifyStatefulMirSym
    (c : StatefulClaim) (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirSym fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (mirSafePost (c.post args mem))) :
    StatefulVerificationResult c := by
  refine verifyStatefulMirBounded c fuel (fun args mem h_pre => ?_)
  rw [← wpMirSym_eq_wpMirBounded]
  exact wpMirSym_mono
    (fun out ho => (mirSafePost_iff_forall_normal _ out).1 ho)
    (h_wp args mem h_pre)

/--
Discharge a stateful `StatefulVerificationResult c` via panic-forbidding
single-pass symbolic evaluation (`mirNormalPost`).
-/
theorem verifyStatefulMirNoPanicSym
    (c : StatefulClaim) (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirSym fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (mirNormalPost (c.post args mem))) :
    StatefulVerificationResult c :=
  verifyStatefulMirSym c fuel (fun args mem h_pre =>
    wpMirSym_mono (fun _ => mirNormalPost_imp_mirSafePost) (h_wp args mem h_pre))

/--
Discharge a stateful `StatefulVerificationResult c` when `c.pre args mem` pins
`args` and `mem` to `(expectedArgs, expectedMem)`.
-/
theorem dischargeStatefulEq
    (c : StatefulClaim)
    (fuel : Nat)
    (expectedArgs : List Value)
    (expectedMem : Memory)
    (h_pre :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem → args = expectedArgs ∧ mem = expectedMem)
    (h_eval :
      wpMirSym fuel c.body
        (initMachineStateWithMemoryAndCallees c.body expectedArgs expectedMem c.callees)
        (mirNormalPost (c.post expectedArgs expectedMem))) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanicSym c fuel (fun args mem hp => by
    rcases h_pre args mem hp with ⟨rfl, rfl⟩
    exact h_eval)

/-! ## 7. Well-Typed Symbolic Scalar & Pinned `#[spec]` Combinators -/

/-- Canonical 1-argument unsigned scalar domain of byte width `width`. -/
def WellTypedScalarArg1 (width : Nat) (args : List Value) : Prop :=
  ∃ b : Nat,
    b < scalarModulus width ∧
      args = [.scalar { bits := b, sizeBytes := width }]

/-- Canonical 2-argument unsigned scalar domain of byte widths `(w1, w2)`. -/
def WellTypedScalarArg2 (w1 w2 : Nat) (args : List Value) : Prop :=
  ∃ b1 b2 : Nat,
    b1 < scalarModulus w1 ∧
      b2 < scalarModulus w2 ∧
      args =
        [ .scalar { bits := b1, sizeBytes := w1 }
        , .scalar { bits := b2, sizeBytes := w2 } ]

/-- Verify a 1-argument scalar function across all canonical `width`-byte inputs. -/
theorem verifyWellTypedScalarArg1
    (c : Claim) (fuel width : Nat)
    (h_pre : ∀ args : List Value, c.pre args → WellTypedScalarArg1 width args)
    (h_sym :
      ∀ b : Nat,
        b < scalarModulus width →
        c.pre [.scalar { bits := b, sizeBytes := width }] →
        wpMirSym fuel c.body
          (initMachineStateWithCallees c.body
            [.scalar { bits := b, sizeBytes := width }]
            c.callees)
          (mirNormalPost
            (fun retVal _ =>
              c.post [.scalar { bits := b, sizeBytes := width }] retVal))) :
    VerificationResult c :=
  verifyMirNoPanicSym c fuel (fun args hp => by
    rcases h_pre args hp with ⟨b, hb, rfl⟩
    exact h_sym b hb hp)

/-- Safe-panic variant of `verifyWellTypedScalarArg1`. -/
theorem verifyWellTypedSafeScalarArg1
    (c : Claim) (fuel width : Nat)
    (h_pre : ∀ args : List Value, c.pre args → WellTypedScalarArg1 width args)
    (h_sym :
      ∀ b : Nat,
        b < scalarModulus width →
        c.pre [.scalar { bits := b, sizeBytes := width }] →
        wpMirSym fuel c.body
          (initMachineStateWithCallees c.body
            [.scalar { bits := b, sizeBytes := width }]
            c.callees)
          (mirSafePost
            (fun retVal _ =>
              c.post [.scalar { bits := b, sizeBytes := width }] retVal))) :
    VerificationResult c :=
  verifyMirSafeSym c fuel (fun args hp => by
    rcases h_pre args hp with ⟨b, hb, rfl⟩
    exact h_sym b hb hp)

/-- Verify a 2-argument scalar function across all canonical `(w1, w2)` inputs. -/
theorem verifyWellTypedScalarArg2
    (c : Claim) (fuel w1 w2 : Nat)
    (h_pre : ∀ args : List Value, c.pre args → WellTypedScalarArg2 w1 w2 args)
    (h_sym :
      ∀ b1 b2 : Nat,
        b1 < scalarModulus w1 →
        b2 < scalarModulus w2 →
        c.pre
          [ .scalar { bits := b1, sizeBytes := w1 }
          , .scalar { bits := b2, sizeBytes := w2 } ] →
        wpMirSym fuel c.body
          (initMachineStateWithCallees c.body
            [ .scalar { bits := b1, sizeBytes := w1 }
            , .scalar { bits := b2, sizeBytes := w2 } ]
            c.callees)
          (mirNormalPost
            (fun retVal _ =>
              c.post
                [ .scalar { bits := b1, sizeBytes := w1 }
                , .scalar { bits := b2, sizeBytes := w2 } ]
                retVal))) :
    VerificationResult c :=
  verifyMirNoPanicSym c fuel (fun args hp => by
    rcases h_pre args hp with ⟨b1, b2, hb1, hb2, rfl⟩
    exact h_sym b1 b2 hb1 hb2 hp)

/--
Computable check that `subjectBody` evaluates on `args` with `callees` within
`subjectFuel` steps to a normal return value `retVal` for which
`checkMirBoolWithCalleesBounded specFuel ensBody callees (args ++ [retVal])`
holds.
-/
def checkMirRustPinnedSpecWithCallees
    (subjectFuel specFuel : Nat)
    (subjectBody ensBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value) : Bool :=
  let rec loop (fuel : Nat) (st : MirExecState) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match stepMirState subjectBody st with
      | .ret (.normal (retVal, _)) =>
        checkMirBoolWithCalleesBounded specFuel ensBody callees (args ++ [retVal])
      | .ret .panic => false
      | .ret .abort => false
      | .tau st' => loop fuel' st'
      | .vis (.inl _) _ => false
      | .vis (.inr (.inl _)) k => loop fuel' (k PUnit.unit)
      | .vis (.inr (.inr _)) _ => false
  loop subjectFuel (.running (initMachineStateWithCallees subjectBody args callees))

/--
Computable check that `body` evaluates on `args` within `fuel` steps to a normal
return value `retVal` for which `checkMirBoolBounded specFuel ensBody (args ++ [retVal])`
holds.
-/
def checkMirRustPinnedSpec
    (subjectFuel specFuel : Nat)
    (subjectBody ensBody : CapturedMir)
    (args : List Value) : Bool :=
  checkMirRustPinnedSpecWithCallees subjectFuel specFuel subjectBody ensBody .nil args

theorem wpMirBounded_of_checkMirRustPinnedSpecWithCallees
    (subjectFuel specFuel : Nat)
    (subjectBody ensBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value)
    (h_ok :
      checkMirRustPinnedSpecWithCallees
        subjectFuel specFuel subjectBody ensBody callees args = true) :
    wpMirBounded subjectFuel subjectBody
      (initMachineStateWithCallees subjectBody args callees)
      (fun out =>
        ∀ retVal mem',
          out = .normal (retVal, mem') →
          MirBoolPredicateHoldsWithCallees ensBody callees (args ++ [retVal])) := by
  unfold checkMirRustPinnedSpecWithCallees at h_ok
  unfold wpMirBounded
  suffices ∀ (fuel : Nat) (st : MirExecState),
      checkMirRustPinnedSpecWithCallees.loop
        specFuel subjectBody ensBody callees args fuel st = true →
      wpCoalBounded fuel mirDefaultWP (stepMirState subjectBody)
        (fun out _ =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            MirBoolPredicateHoldsWithCallees ensBody callees (args ++ [retVal]))
        st PUnit.unit from
    this subjectFuel _ h_ok
  intro fuel
  induction fuel with
  | zero => intro _ h; nomatch h
  | succ fuel' ih =>
    intro st h
    unfold checkMirRustPinnedSpecWithCallees.loop at h
    unfold wpCoalBounded
    cases h_step : stepMirState subjectBody st with
    | ret out =>
      simp only [h_step] at h ⊢
      cases out with
      | normal p =>
        rcases p with ⟨rv, m⟩
        intro retVal mem' h_eq
        injection h_eq with h_pair
        cases h_pair
        exact mirBoolPredicateHoldsWithCallees_of_checkBounded specFuel ensBody
          callees (args ++ [rv]) h
      | panic => nomatch h
      | abort => nomatch h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih st' h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · nomatch h
      · cases e
        exact ih (k PUnit.unit) h
      · nomatch h

theorem wpMirBounded_of_checkMirRustPinnedSpec
    (subjectFuel specFuel : Nat)
    (subjectBody ensBody : CapturedMir)
    (args : List Value)
    (h_ok :
      checkMirRustPinnedSpec subjectFuel specFuel subjectBody ensBody args = true) :
    wpMirBounded subjectFuel subjectBody (initMachineState subjectBody args)
      (fun out =>
        ∀ retVal mem',
          out = .normal (retVal, mem') →
          MirBoolPredicateHolds ensBody (args ++ [retVal])) :=
  wpMirBounded_of_checkMirRustPinnedSpecWithCallees
    subjectFuel specFuel subjectBody ensBody .nil args h_ok

/-! ## 8. Bounded UB Counterexample / Claim Refutation & Non-Vacuity Witnesses -/

/--
Computable bounded fault detector over `MirExecState`: returns `true` when
`body` reaches an immediate operational fault (`MirFailE`: `.ub` or
`.unsupported`) within `fuel` steps along `.tau` and `MirObsE` transitions.
-/
def reachesFaultExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret _ => false
    | .tau st' => reachesFaultExecBounded fuel' body st'
    | .vis (.inl _) _ => true
    | .vis (.inr (.inl _)) k => reachesFaultExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr _)) _ => false

/-- Computable bounded fault detector starting from `s : MachineState`. -/
def reachesFaultBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Bool :=
  reachesFaultExecBounded fuel body (.running s)

private theorem treeSafe_of_observe_tau
    {t t' : ITree MirEffect MirOutcome}
    (h_obs : t.observe = .tau t')
    (h_safe : TreeSafe t) :
    TreeSafe t' :=
  fun tr u h_reach => h_safe tr u (Reaches.tau h_obs h_reach)

private theorem treeSafe_of_observe_obs
    {t : ITree MirEffect MirOutcome}
    {ev : ObsReq MirObs}
    {k : PUnit → ITree MirEffect MirOutcome}
    (h_obs : t.observe = .vis (.inr (.inl ev)) k)
    (h_safe : TreeSafe t) :
    TreeSafe (k PUnit.unit) :=
  fun tr u h_reach =>
    h_safe (⟨.inr (.inl ev), PUnit.unit⟩ :: tr) u
      (Reaches.vis h_obs False.elim PUnit.unit h_reach)

/--
Soundness of `reachesFaultExecBounded`: if `reachesFaultExecBounded fuel body st`
returns `true`, then `ITree.cofix (stepMirState body) st` is provably NOT
`TreeSafe`.
-/
theorem reachesFaultExecBounded_not_treeSafe
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_fault : reachesFaultExecBounded fuel body st = true) :
    ¬ TreeSafe (ITree.cofix (stepMirState body) st) := by
  induction fuel generalizing st with
  | zero => nomatch h_fault
  | succ fuel' ih =>
    intro h_safe
    unfold reachesFaultExecBounded at h_fault
    have h_obs :
        (ITree.cofix (stepMirState body) st).observe =
          (stepMirState body st).map (ITree.cofix (stepMirState body)) :=
      ITree.observe_cofix (stepMirState body) st
    cases h_step : stepMirState body st with
    | ret _ =>
      simp only [h_step] at h_fault
      nomatch h_fault
    | tau st' =>
      simp only [h_step] at h_fault
      rw [h_step] at h_obs
      dsimp only [ITreeF.map] at h_obs
      exact ih st' h_fault (treeSafe_of_observe_tau h_obs h_safe)
    | vis i k =>
      rcases i with f | (e | c)
      · rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        exact h_safe [] (ITree.cofix (stepMirState body) st)
          (Reaches.refl _)
          ⟨_, .inl f, _, TauStar.refl _, h_obs, trivial⟩
      · simp only [h_step] at h_fault
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        exact ih (k PUnit.unit) h_fault (treeSafe_of_observe_obs h_obs h_safe)
      · simp only [h_step] at h_fault
        nomatch h_fault

/--
If `reachesFaultBounded fuel body s = true`, then `mirTree body s` violates
`TreeSafe` (exhibits reachable Undefined Behavior or an unsupported fault).
-/
theorem reachesFaultBounded_not_treeSafe
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (h_fault : reachesFaultBounded fuel body s = true) :
    ¬ TreeSafe (mirTree body s) :=
  reachesFaultExecBounded_not_treeSafe fuel body (.running s) h_fault

/--
Refute `MirContractHoldsWithSafetyAndCallees` by exhibiting a concrete input
`args` in `safetyPre` whose bounded execution hits a fault within `fuel` steps.
-/
theorem refuteMirContractWithSafetyAndCalleesByBoundedUB
    {body : CapturedMir}
    {callees : List CapturedMir}
    {safetyPre pre : List Value → Prop}
    {post : List Value → Value → Prop}
    (fuel : Nat)
    (args : List Value)
    (h_safe_pre : safetyPre args)
    (h_ub :
      reachesFaultBounded fuel body
        (initMachineStateWithCallees body args callees) = true := by
      rfl) :
    ¬ MirContractHoldsWithSafetyAndCallees body callees safetyPre pre post := by
  intro h_holds
  rcases h_holds args h_safe_pre with ⟨h_tree_safe, _⟩
  exact reachesFaultBounded_not_treeSafe fuel body
    (initMachineStateWithCallees body args callees) h_ub h_tree_safe

/--
Refute `MirContractHoldsWithSafety` by exhibiting a concrete input `args` in
`safetyPre` whose bounded execution hits a fault within `fuel` steps.
-/
theorem refuteMirContractWithSafetyByBoundedUB
    {body : CapturedMir}
    {safetyPre pre : List Value → Prop}
    {post : List Value → Value → Prop}
    (fuel : Nat)
    (args : List Value)
    (h_safe_pre : safetyPre args)
    (h_ub :
      reachesFaultBounded fuel body (initMachineState body args) = true := by
      rfl) :
    ¬ MirContractHoldsWithSafety body safetyPre pre post :=
  refuteMirContractWithSafetyAndCalleesByBoundedUB fuel args h_safe_pre h_ub

/--
Refute a stateless `c : Claim` (`¬ c.holds`) by exhibiting a concrete input
`args` satisfying `c.pre args` whose bounded execution hits a fault within
`fuel` steps.
-/
theorem refuteClaimByBoundedUB
    (c : Claim)
    (fuel : Nat)
    (args : List Value)
    (h_pre : c.pre args)
    (h_ub :
      reachesFaultBounded fuel c.body
        (initMachineStateWithCallees c.body args c.callees) = true := by
      rfl) :
    ¬ c.holds :=
  refuteMirContractWithSafetyAndCalleesByBoundedUB fuel args h_pre h_ub

/--
Refute a stateful `c : StatefulClaim` (`¬ c.holds`) by exhibiting a concrete
`(args, mem)` satisfying `c.pre args mem` whose bounded execution hits a fault
within `fuel` steps.
-/
theorem refuteStatefulClaimByBoundedUB
    (c : StatefulClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (h_ub :
      reachesFaultBounded fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) = true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  rcases h_holds args mem h_pre with ⟨h_tree_safe, _⟩
  exact reachesFaultBounded_not_treeSafe fuel c.body
    (initMachineStateWithMemoryAndCallees c.body args mem c.callees) h_ub h_tree_safe

/--
Refute a total-correctness `c : TotalClaim` (`¬ c.holds`) by exhibiting a
concrete `(args, mem)` satisfying `c.pre args mem` whose bounded execution hits
a fault within `fuel` steps.
-/
theorem refuteTotalClaimByBoundedUB
    (c : TotalClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (h_ub :
      reachesFaultBounded fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) = true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  have h_tree_safe := (h_holds args mem h_pre).1
  exact reachesFaultBounded_not_treeSafe fuel c.body
    (initMachineStateWithMemoryAndCallees c.body args mem c.callees) h_ub h_tree_safe

/-- Package a concrete argument list `args` as a non-vacuity witness (`∃ a, pre a`). -/
theorem proveNonVacuousPre
    {pre : List Value → Prop}
    (args : List Value)
    (h_pre : pre args) :
    ∃ a : List Value, pre a :=
  ⟨args, h_pre⟩

/--
Package a concrete `(args, mem)` pair as a stateful non-vacuity witness
(`∃ a m, pre a m`).
-/
theorem proveNonVacuousStatefulPre
    {pre : List Value → Memory → Prop}
    (args : List Value)
    (mem : Memory)
    (h_pre : pre args mem) :
    ∃ (a : List Value) (m : Memory), pre a m :=
  ⟨args, mem, h_pre⟩

/--
Prove non-vacuity of a generated `#[spec(requires: ...)]` precondition
(`length args = argCount ∧ MirBoolPredicateHolds reqBody args`) from a concrete
witness `args` checked by `rfl`.
-/
theorem proveNonVacuousBoolSpecPre
    (fuel argCount : Nat)
    (reqBody : CapturedMir)
    (args : List Value)
    (h_len : Trusted.Sequence.length args = argCount := by rfl)
    (h_req : checkMirBoolBounded fuel reqBody args = true := by rfl) :
    ∃ a : List Value,
      Trusted.Sequence.length a = argCount ∧ MirBoolPredicateHolds reqBody a :=
  ⟨args, h_len, mirBoolPredicateHolds_of_checkBounded fuel reqBody args h_req⟩

/-! ## 9. Single-Pass Call-Free Symbolic Program-to-Program Equivalence (`verifyStatefulEquivMirSym`) -/

/-- Direct `Prop`-valued node evaluator matching `mirNoCallWP` on `MirStepNode`. -/
@[reducible]
def evalNodeNoCallWP
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr _)) _ => False

theorem evalNodeNoCallWP_eq
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (node : MirStepNode) :
    evalNodeNoCallWP cont post node =
      match node with
      | .ret out => post out
      | .tau st' => cont st'
      | .vis i k => mirNoCallWP.wp i (fun o _ => cont (k o)) PUnit.unit := by
  cases node with
  | ret _ => rfl
  | tau _ => rfl
  | vis i _ =>
    rcases i with f | (e | c)
    · cases f; rfl
    · cases e; rfl
    · cases c; rfl

/-- Structural `Prop`-valued call-free evaluator over `SymTree MirStepNode`. -/
def evalSymNodeTreeNoCall
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr _)) _) => False
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeNoCall cont post t1
    | false => evalSymNodeTreeNoCall cont post t2

theorem evalSymNodeTreeNoCall_eq
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (t : SymTree MirStepNode) :
    evalSymNodeTreeNoCall cont post t = evalNodeNoCallWP cont post t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c) <;> rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/-- Call-free single-pass fuel-bounded symbolic WP over `MirExecState`. -/
def wpMirExecNoCallSym
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeNoCall
      (fun st' => wpMirExecNoCallSym fuel' body st' post)
      post
      (stepMirExecSymTree body st)

/-- Call-free single-pass fuel-bounded symbolic WP over `MachineState`. -/
def wpMirNoCallSym
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecNoCallSym fuel body (.running s) post

theorem wpMirExecNoCallSym_eq_wpCoalBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) :
    wpMirExecNoCallSym fuel body st post =
      wpCoalBounded fuel mirNoCallWP (stepMirState body)
        (fun out _ => post out) st PUnit.unit := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    unfold wpMirExecNoCallSym wpCoalBounded
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
    cases stepMirState body st with
    | ret _ => rfl
    | tau st' => exact ih st'
    | vis i k =>
      rcases i with f | (e | c)
      · cases f; rfl
      · cases e; exact ih (k PUnit.unit)
      · cases c; rfl

/-- Exact equality between single-pass `wpMirNoCallSym` and `Lower.wpMirNoCallBounded`. -/
theorem wpMirNoCallSym_eq_wpMirNoCallBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) :
    wpMirNoCallSym fuel body s post = wpMirNoCallBounded fuel body s post :=
  wpMirExecNoCallSym_eq_wpCoalBounded fuel body (.running s) post

/--
Discharge a program-to-program behavioral equivalence and total-correctness
`StatefulEquivVerificationResult c` via single-pass symbolic evaluation of both
candidate `c.implBody` and reference `c.specBody` against `model`.
-/
theorem verifyStatefulEquivMirSym
    (c : StatefulEquivClaim)
    (implFuel specFuel : Nat)
    (model : List Value → Memory → Value × Memory)
    (h_impl :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirNoCallSym implFuel c.implBody
          (initMachineStateWithMemoryAndCallees c.implBody args mem c.implCallees)
          (fun out =>
            out = .normal (model args mem) ∧
            c.post args mem (model args mem).1 (model args mem).2))
    (h_spec :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirNoCallSym specFuel c.specBody
          (initMachineStateWithMemoryAndCallees c.specBody args mem c.specCallees)
          (fun out => out = .normal (model args mem))) :
    StatefulEquivVerificationResult c := by
  refine verifyStatefulEquivMirBounded c implFuel specFuel model
    (fun args mem h_pre => ?_)
    (fun args mem h_pre => ?_)
  · rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
    exact h_impl args mem h_pre
  · rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
    exact h_spec args mem h_pre


/-! ## 14. Single-Pass Symbolic Evaluators for Scoped UB Exceptions & Modular Call Contracts -/

/-- Direct `Prop`-valued node evaluator matching `mirUbWaivedWP` on `MirStepNode`. -/
@[reducible]
def evalNodeUbWaivedWP
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl f) _ => isWaivedUbFailReq f
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr (.call _))) k => ∀ ans : MirCallAns, cont (k ans)

theorem evalNodeUbWaivedWP_eq
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (node : MirStepNode) :
    evalNodeUbWaivedWP cont post node =
      match node with
      | .ret out => post out
      | .tau st' => cont st'
      | .vis i k => mirUbWaivedWP.wp i (fun o _ => cont (k o)) PUnit.unit := by
  cases node with
  | ret _ => rfl
  | tau _ => rfl
  | vis i _ =>
    rcases i with f | (e | c)
    · cases f; rfl
    · cases e; rfl
    · cases c; rfl

/-- Structural `Prop`-valued UB-waived evaluator over `SymTree MirStepNode`. -/
def evalSymNodeTreeUbWaived
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl f) _) => isWaivedUbFailReq f
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr (.call _))) k) => ∀ ans : MirCallAns, cont (k ans)
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeUbWaived cont post t1
    | false => evalSymNodeTreeUbWaived cont post t2

theorem evalSymNodeTreeUbWaived_eq
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (t : SymTree MirStepNode) :
    evalSymNodeTreeUbWaived cont post t = evalNodeUbWaivedWP cont post t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c)
      · cases f; rfl
      · cases e; rfl
      · cases c; rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/-- Single-pass fuel-bounded UB-waived symbolic WP over `MirExecState`. -/
def wpMirExecUbWaivedSym
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeUbWaived
      (fun st' => wpMirExecUbWaivedSym fuel' body st' post)
      post
      (stepMirExecSymTree body st)

/-- Single-pass fuel-bounded UB-waived symbolic WP over `MachineState`. -/
def wpMirUbWaivedSym
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecUbWaivedSym fuel body (.running s) post

theorem wpMirExecUbWaivedSym_eq_wpCoalBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) :
    wpMirExecUbWaivedSym fuel body st post =
      wpCoalBounded fuel mirUbWaivedWP (stepMirState body)
        (fun out _ => post out) st PUnit.unit := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    unfold wpMirExecUbWaivedSym wpCoalBounded
    rw [evalSymNodeTreeUbWaived_eq, stepMirExecSymTree_eval, evalNodeUbWaivedWP_eq]
    cases stepMirState body st with
    | ret _ => rfl
    | tau st' => exact ih st'
    | vis i k =>
      rcases i with f | (e | c)
      · cases f; rfl
      · cases e; exact ih (k PUnit.unit)
      · cases c
        dsimp only []
        congr 1
        funext ans u
        cases u
        exact ih (k ans)

/-- Exact equality between single-pass `wpMirUbWaivedSym` and `Lower.wpMirUbWaivedBounded`. -/
theorem wpMirUbWaivedSym_eq_wpMirUbWaivedBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) :
    wpMirUbWaivedSym fuel body s post = wpMirUbWaivedBounded fuel body s post :=
  wpMirExecUbWaivedSym_eq_wpCoalBounded fuel body (.running s) post

/--
Discharge a `UbExceptionVerificationResult c` via single-pass symbolic evaluation
(`wpMirSym` on the strict safety domain `c.pre ∧ c.strictSafetyPre`, and
`wpMirUbWaivedSym` across `c.pre`).
-/
theorem verifyUbExceptionMirSym
    (c : UbExceptionClaim)
    (fuel : Nat)
    (h_strict :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        c.strictSafetyPre args mem →
        wpMirSym fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              c.post args mem retVal mem'))
    (h_waived :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirUbWaivedSym fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              c.post args mem retVal mem')) :
    UbExceptionVerificationResult c := by
  refine verifyUbExceptionMirBounded c fuel
    (fun args mem h_pre h_sp => ?_)
    (fun args mem h_pre => ?_)
  · rw [← wpMirSym_eq_wpMirBounded]
    exact h_strict args mem h_pre h_sp
  · rw [← wpMirUbWaivedSym_eq_wpMirUbWaivedBounded]
    exact h_waived args mem h_pre

/-- Direct `Prop`-valued node evaluator matching `mirModularWP contract.toCallContract`. -/
@[reducible]
def evalNodeModularWP
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr (.call req))) k =>
    contract.pre req ∧
      ∀ ans : MirCallAns, contract.post req ans → cont (k ans)

theorem evalNodeModularWP_eq
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (node : MirStepNode) :
    evalNodeModularWP contract cont post node =
      match node with
      | .ret out => post out
      | .tau st' => cont st'
      | .vis i k =>
        (mirModularWP contract.toCallContract).wp i
          (fun o _ => cont (k o)) PUnit.unit := by
  cases node with
  | ret _ => rfl
  | tau _ => rfl
  | vis i _ =>
    rcases i with f | (e | c)
    · cases f; rfl
    · cases e; rfl
    · cases c; rfl

/-- Structural `Prop`-valued modular call-contract evaluator over `SymTree MirStepNode`. -/
def evalSymNodeTreeModular
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr (.call req))) k) =>
    contract.pre req ∧
      ∀ ans : MirCallAns, contract.post req ans → cont (k ans)
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeModular contract cont post t1
    | false => evalSymNodeTreeModular contract cont post t2

theorem evalSymNodeTreeModular_eq
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (t : SymTree MirStepNode) :
    evalSymNodeTreeModular contract cont post t =
      evalNodeModularWP contract cont post t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c) <;> rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/-- Single-pass fuel-bounded modular symbolic WP over `MirExecState`. -/
def wpMirExecModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeModular contract
      (fun st' => wpMirExecModularSym contract fuel' body st' post)
      post
      (stepMirExecSymTree body st)

/-- Single-pass fuel-bounded modular symbolic WP over `MachineState`. -/
def wpMirModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecModularSym contract fuel body (.running s) post

theorem wpMirExecModularSym_eq_wpCoalBounded
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) :
    wpMirExecModularSym contract fuel body st post =
      wpCoalBounded fuel (mirModularWP contract.toCallContract)
        (stepMirState body) (fun out _ => post out) st PUnit.unit := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    unfold wpMirExecModularSym wpCoalBounded
    rw [evalSymNodeTreeModular_eq, stepMirExecSymTree_eval, evalNodeModularWP_eq]
    cases stepMirState body st with
    | ret _ => rfl
    | tau st' => exact ih st'
    | vis i k =>
      rcases i with f | (e | c)
      · cases f; rfl
      · cases e; exact ih (k PUnit.unit)
      · rcases c with ⟨req⟩
        dsimp only []
        simp only [ih]

/--
Discharge a `ModularVerificationResult` with linked `callees` for `body` under
`contract.holdsOn` via single-pass symbolic evaluation (`wpMirModularSym`).
-/
theorem verifyModularContractWithCalleesMirSym
    (contract : MirCallContract)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirModularSym contract fuel body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post
        callees := callees } := by
  refine verifyModularContractWithCalleesMirBounded contract body callees pre post fuel
    (fun args mem h_pre => ?_)
  rw [wpMirModularBounded, ← wpMirExecModularSym_eq_wpCoalBounded]
  exact h_wp args mem h_pre

/--
Discharge a `ModularVerificationResult` for `body` under `contract.holdsOn` via
single-pass symbolic evaluation (`wpMirModularSym`).
-/
theorem verifyModularContractMirSym
    (contract : MirCallContract)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirModularSym contract fuel body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post } :=
  verifyModularContractWithCalleesMirSym contract body .nil pre post fuel h_wp

/--
Overwrite the call-frame components (`callees`, `callStack`, `activeCallee`,
and `activeProtectors`) of `after : Memory` with those of `before : Memory` so
post-call symbolic evaluation can reduce concrete caller frame fields by WHNF
even when `after` is a universally quantified symbolic memory.
-/
@[reducible, simp]
def restoreCallFrame (before after : Memory) : Memory :=
  { after with
    callees := before.callees
    callStack := before.callStack
    activeCallee := before.activeCallee
    activeProtectors := before.activeProtectors }

theorem restoreCallFrame_eq_of_callFramePreserved
    {before after : Memory}
    (h : callFramePreserved before after) :
    restoreCallFrame before after = after := by
  rcases h with ⟨h1, h2, h3, h4, _⟩
  cases after
  dsimp only [restoreCallFrame] at h1 h2 h3 h4 ⊢
  subst h1 h2 h3 h4
  rfl

/--
Project `restoreCallFrame before` across a `MirCallAns` response.
-/
@[reducible, simp]
def _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.restoreFrame
    (before : Memory) : MirCallAns → MirCallAns
  | .returned retVal memAfter =>
    .returned retVal (restoreCallFrame before memAfter)
  | .panicked memAfter =>
    .panicked (restoreCallFrame before memAfter)
  | .aborted => .aborted

/--
Frame-preservation predicate on a `MirCallAns` response relative to `before`.
-/
@[reducible, simp]
def _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.framePreserved
    (before : Memory) : MirCallAns → Prop
  | .returned _ memAfter => callFramePreserved before memAfter
  | .panicked memAfter => callFramePreserved before memAfter
  | .aborted => True

theorem _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.restoreFrame_eq_of_framePreserved
    {before : Memory} {ans : MirCallAns}
    (h : ans.framePreserved before) :
    ans.restoreFrame before = ans := by
  cases ans with
  | returned retVal memAfter =>
    dsimp only [MirCallAns.restoreFrame, MirCallAns.framePreserved] at h ⊢
    rw [restoreCallFrame_eq_of_callFramePreserved h]
  | panicked memAfter =>
    dsimp only [MirCallAns.restoreFrame, MirCallAns.framePreserved] at h ⊢
    rw [restoreCallFrame_eq_of_callFramePreserved h]
  | aborted => rfl

/--
Every `externalSpecCallContract` guarantees `ans.framePreserved req.memory` on
every call answer `ans` permitted by its postcondition.
-/
theorem externalSpecCallContract_framePreserved
    (targetDefPath : DefPath)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ∀ (req : MirCallReq) (ans : MirCallAns),
      (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).post req ans →
      ans.framePreserved req.memory := by
  intro req ans h_post
  cases ans with
  | returned retVal memAfter =>
    exact h_post.1
  | panicked memAfter =>
    dsimp only [externalSpecCallContract] at h_post
    cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at h_post
    · exact False.elim h_post
    · exact h_post
  | aborted => trivial

/--
Frame-restoring node evaluator for modular call contracts: substitutes
`ans.restoreFrame req.memory` into the post-call continuation `k` so all
subsequent statements, blocks, inlined `callees`, and `return_` transitions in
the caller frame reduce by WHNF without manual `rw` on `memAfter`.
-/
@[reducible]
def evalNodeFrameModularWP
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr (.call req))) k =>
    contract.pre req ∧
      ∀ ans : MirCallAns,
        contract.post req ans → cont (k (ans.restoreFrame req.memory))

/--
Structural `Prop`-valued frame-restoring modular evaluator over
`SymTree MirStepNode`.
-/
def evalSymNodeTreeFrameModular
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr (.call req))) k) =>
    contract.pre req ∧
      ∀ ans : MirCallAns,
        contract.post req ans → cont (k (ans.restoreFrame req.memory))
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeFrameModular contract cont post t1
    | false => evalSymNodeTreeFrameModular contract cont post t2

theorem evalSymNodeTreeFrameModular_eq
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (t : SymTree MirStepNode) :
    evalSymNodeTreeFrameModular contract cont post t =
      evalNodeFrameModularWP contract cont post t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c) <;> rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/--
Single-pass fuel-bounded frame-restoring modular symbolic WP over `MirExecState`.
-/
def wpMirExecFrameModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeFrameModular contract
      (fun st' => wpMirExecFrameModularSym contract fuel' body st' post)
      post
      (stepMirExecSymTree body st)

/--
Single-pass fuel-bounded frame-restoring modular symbolic WP over `MachineState`.
-/
def wpMirFrameModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecFrameModularSym contract fuel body (.running s) post

/--
Soundness of `wpMirExecFrameModularSym`: for any `contract` whose postcondition
implies `ans.framePreserved req.memory`, `wpMirExecFrameModularSym` implies
`wpMirExecModularSym`.
-/
theorem wpMirExecModularSym_of_wpMirExecFrameModularSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.framePreserved req.memory)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop)
    (h : wpMirExecFrameModularSym contract fuel body st post) :
    wpMirExecModularSym contract fuel body st post := by
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpMirExecFrameModularSym at h
    unfold wpMirExecModularSym
    rw [evalSymNodeTreeFrameModular_eq] at h
    rw [evalSymNodeTreeModular_eq]
    cases h_ev : (stepMirExecSymTree body st).eval with
    | ret out =>
      rw [h_ev] at h
      exact h
    | tau st' =>
      rw [h_ev] at h
      exact ih st' h
    | vis i k =>
      rw [h_ev] at h
      rcases i with f | (e | c)
      · cases f; exact False.elim h
      · cases e; exact ih (k PUnit.unit) h
      · rcases c with ⟨req⟩
        dsimp only [evalNodeFrameModularWP, evalNodeModularWP] at h ⊢
        refine ⟨h.1, fun ans h_post => ?_⟩
        have h_eq : ans.restoreFrame req.memory = ans :=
          MirCallAns.restoreFrame_eq_of_framePreserved (h_frame req ans h_post)
        have h_cont := h.2 ans h_post
        rw [h_eq] at h_cont
        exact ih (k ans) h_cont

/--
Discharge a `ModularVerificationResult` with linked `callees` via frame-restoring
single-pass symbolic evaluation (`wpMirFrameModularSym`).
-/
theorem verifyModularFrameContractWithCalleesMirSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.framePreserved req.memory)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym contract fuel body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post
        callees := callees } :=
  verifyModularContractWithCalleesMirSym contract body callees pre post fuel
    (fun args mem h_pre =>
      wpMirExecModularSym_of_wpMirExecFrameModularSym
        contract h_frame fuel body _ _ (h_wp args mem h_pre))

/--
Discharge a `ModularVerificationResult` without extra `callees` via
frame-restoring single-pass symbolic evaluation (`wpMirFrameModularSym`).
-/
theorem verifyModularFrameContractMirSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.framePreserved req.memory)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym contract fuel body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post } :=
  verifyModularFrameContractWithCalleesMirSym
    contract h_frame body .nil pre post fuel h_wp

/--
Discharge a `ModularVerificationResult` with linked `callees` for a caller
invoking an `#[external_spec]` target (`externalSpecCallContract`), using
frame-restoring `wpMirFrameModularSym` so post-call execution steps by `whnf`
without manual frame-preservation rewrites.
-/
theorem verifyExternalSpecWithCalleesMirSym
    (targetDefPath : DefPath)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym
          (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)
          fuel
          body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed :=
          (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).holdsOn
        pre := pre
        post := post
        callees := callees } :=
  verifyModularFrameContractWithCalleesMirSym
    (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)
    (externalSpecCallContract_framePreserved targetDefPath sidecarBody extraPre extraPost)
    body callees pre post fuel h_wp

/--
Discharge a `ModularVerificationResult` for a caller invoking an
`#[external_spec]` target (`externalSpecCallContract`), using frame-restoring
`wpMirFrameModularSym`.
-/
theorem verifyExternalSpecMirSym
    (targetDefPath : DefPath)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameModularSym
          (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)
          fuel
          body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed :=
          (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).holdsOn
        pre := pre
        post := post } :=
  verifyExternalSpecWithCalleesMirSym
    targetDefPath sidecarBody extraPre extraPost body .nil pre post fuel h_wp

theorem restoreCallerMemoryFrame_eq_of_callFrameAndTraitsPreserved
    {before after : Memory}
    (h : callFrameAndTraitsPreserved before after) :
    restoreCallerMemoryFrame before after = after := by
  rcases h with ⟨⟨h1, h2, h3, h4, _⟩, h5⟩
  cases after
  dsimp only [restoreCallerMemoryFrame] at h1 h2 h3 h4 h5 ⊢
  subst h1 h2 h3 h4 h5
  rfl

/--
Project `restoreCallerMemoryFrame before` across a `MirCallAns` response,
restoring both the caller frame fields and `before.traitImpls` so post-call
polymorphic and trait-method calls in `before.callees` reduce by WHNF.
-/
@[reducible, simp]
def _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.restoreFrameAndTraits
    (before : Memory) : MirCallAns → MirCallAns
  | .returned retVal memAfter =>
    .returned retVal (restoreCallerMemoryFrame before memAfter)
  | .panicked memAfter =>
    .panicked (restoreCallerMemoryFrame before memAfter)
  | .aborted => .aborted

/--
Frame-and-`traitImpls` preservation predicate on a `MirCallAns` response
relative to `before`.
-/
@[reducible, simp]
def _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.frameAndTraitsPreserved
    (before : Memory) : MirCallAns → Prop
  | .returned _ memAfter => callFrameAndTraitsPreserved before memAfter
  | .panicked memAfter => callFrameAndTraitsPreserved before memAfter
  | .aborted => True

theorem _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.restoreFrameAndTraits_eq_of_frameAndTraitsPreserved
    {before : Memory} {ans : MirCallAns}
    (h : ans.frameAndTraitsPreserved before) :
    ans.restoreFrameAndTraits before = ans := by
  cases ans with
  | returned retVal memAfter =>
    dsimp only [MirCallAns.restoreFrameAndTraits, MirCallAns.frameAndTraitsPreserved] at h ⊢
    rw [restoreCallerMemoryFrame_eq_of_callFrameAndTraitsPreserved h]
  | panicked memAfter =>
    dsimp only [MirCallAns.restoreFrameAndTraits, MirCallAns.frameAndTraitsPreserved] at h ⊢
    rw [restoreCallerMemoryFrame_eq_of_callFrameAndTraitsPreserved h]
  | aborted => rfl

/--
Every `polyExternalSpecCallContract` guarantees
`ans.frameAndTraitsPreserved req.memory` on every call answer `ans` permitted by
its postcondition.
-/
theorem polyExternalSpecCallContract_frameAndTraitsPreserved
    (targetDefPath : DefPath)
    (expectedTypeArgs : List RigidTy)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ∀ (req : MirCallReq) (ans : MirCallAns),
      (polyExternalSpecCallContract
        targetDefPath expectedTypeArgs sidecarBody extraPre extraPost).post req ans →
      ans.frameAndTraitsPreserved req.memory := by
  intro req ans h_post
  cases ans with
  | returned retVal memAfter =>
    exact h_post.1
  | panicked memAfter =>
    dsimp only [polyExternalSpecCallContract] at h_post
    cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at h_post
    · exact False.elim h_post
    · exact h_post
  | aborted => trivial

/--
Frame-and-`traitImpls`-restoring node evaluator for modular call contracts:
substitutes `ans.restoreFrameAndTraits req.memory` into the post-call
continuation `k` so all subsequent statements, blocks, polymorphic/trait-method
inlined `callees`, and `return_` transitions in the caller frame reduce by WHNF.
-/
@[reducible]
def evalNodeFrameAndTraitsModularWP
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    MirStepNode → Prop
  | .ret out => post out
  | .tau st' => cont st'
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl _)) k => cont (k PUnit.unit)
  | .vis (.inr (.inr (.call req))) k =>
    contract.pre req ∧
      ∀ ans : MirCallAns,
        contract.post req ans → cont (k (ans.restoreFrameAndTraits req.memory))

/--
Structural `Prop`-valued frame-and-`traitImpls`-restoring modular evaluator over
`SymTree MirStepNode`.
-/
def evalSymNodeTreeFrameAndTraitsModular
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post out
  | .leaf (.tau st') => cont st'
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl _)) k) => cont (k PUnit.unit)
  | .leaf (.vis (.inr (.inr (.call req))) k) =>
    contract.pre req ∧
      ∀ ans : MirCallAns,
        contract.post req ans → cont (k (ans.restoreFrameAndTraits req.memory))
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeFrameAndTraitsModular contract cont post t1
    | false => evalSymNodeTreeFrameAndTraitsModular contract cont post t2

theorem evalSymNodeTreeFrameAndTraitsModular_eq
    (contract : MirCallContract)
    (cont : MirExecState → Prop) (post : MirOutcome → Prop)
    (t : SymTree MirStepNode) :
    evalSymNodeTreeFrameAndTraitsModular contract cont post t =
      evalNodeFrameAndTraitsModularWP contract cont post t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c) <;> rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/--
Single-pass fuel-bounded frame-and-`traitImpls`-restoring modular symbolic WP
over `MirExecState`.
-/
def wpMirExecFrameAndTraitsModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeFrameAndTraitsModular contract
      (fun st' => wpMirExecFrameAndTraitsModularSym contract fuel' body st' post)
      post
      (stepMirExecSymTree body st)

/--
Single-pass fuel-bounded frame-and-`traitImpls`-restoring modular symbolic WP
over `MachineState`.
-/
def wpMirFrameAndTraitsModularSym
    (contract : MirCallContract)
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirExecFrameAndTraitsModularSym contract fuel body (.running s) post

/--
Soundness of `wpMirExecFrameAndTraitsModularSym`: for any `contract` whose
postcondition implies `ans.frameAndTraitsPreserved req.memory`,
`wpMirExecFrameAndTraitsModularSym` implies `wpMirExecModularSym`.
-/
theorem wpMirExecModularSym_of_wpMirExecFrameAndTraitsModularSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.frameAndTraitsPreserved req.memory)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (post : MirOutcome → Prop)
    (h : wpMirExecFrameAndTraitsModularSym contract fuel body st post) :
    wpMirExecModularSym contract fuel body st post := by
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpMirExecFrameAndTraitsModularSym at h
    unfold wpMirExecModularSym
    rw [evalSymNodeTreeFrameAndTraitsModular_eq] at h
    rw [evalSymNodeTreeModular_eq]
    cases h_ev : (stepMirExecSymTree body st).eval with
    | ret out =>
      rw [h_ev] at h
      exact h
    | tau st' =>
      rw [h_ev] at h
      exact ih st' h
    | vis i k =>
      rw [h_ev] at h
      rcases i with f | (e | c)
      · cases f; exact False.elim h
      · cases e; exact ih (k PUnit.unit) h
      · rcases c with ⟨req⟩
        dsimp only [evalNodeFrameAndTraitsModularWP, evalNodeModularWP] at h ⊢
        refine ⟨h.1, fun ans h_post => ?_⟩
        have h_eq : ans.restoreFrameAndTraits req.memory = ans :=
          MirCallAns.restoreFrameAndTraits_eq_of_frameAndTraitsPreserved (h_frame req ans h_post)
        have h_cont := h.2 ans h_post
        rw [h_eq] at h_cont
        exact ih (k ans) h_cont

/--
Discharge a `ModularVerificationResult` with linked `callees` via
frame-and-`traitImpls`-restoring single-pass symbolic evaluation
(`wpMirFrameAndTraitsModularSym`).
-/
theorem verifyModularFrameAndTraitsContractWithCalleesMirSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.frameAndTraitsPreserved req.memory)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameAndTraitsModularSym contract fuel body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post
        callees := callees } :=
  verifyModularContractWithCalleesMirSym contract body callees pre post fuel
    (fun args mem h_pre =>
      wpMirExecModularSym_of_wpMirExecFrameAndTraitsModularSym
        contract h_frame fuel body _ _ (h_wp args mem h_pre))

/--
Discharge a `ModularVerificationResult` without extra `callees` via
frame-and-`traitImpls`-restoring single-pass symbolic evaluation
(`wpMirFrameAndTraitsModularSym`).
-/
theorem verifyModularFrameAndTraitsContractMirSym
    (contract : MirCallContract)
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.frameAndTraitsPreserved req.memory)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameAndTraitsModularSym contract fuel body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post } :=
  verifyModularFrameAndTraitsContractWithCalleesMirSym
    contract h_frame body .nil pre post fuel h_wp

/--
Discharge a `ModularVerificationResult` with linked `callees` for a caller
invoking a polymorphic `#[external_spec]` target
(`polyExternalSpecCallContract`), using `wpMirFrameAndTraitsModularSym` so
subsequent polymorphic and trait-method calls in `callees` reduce by WHNF.
-/
theorem verifyPolyExternalSpecWithCalleesMirSym
    (targetDefPath : DefPath)
    (expectedTypeArgs : List RigidTy)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameAndTraitsModularSym
          (polyExternalSpecCallContract
            targetDefPath expectedTypeArgs sidecarBody extraPre extraPost)
          fuel
          body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed :=
          (polyExternalSpecCallContract
            targetDefPath expectedTypeArgs sidecarBody extraPre extraPost).holdsOn
        pre := pre
        post := post
        callees := callees } :=
  verifyModularFrameAndTraitsContractWithCalleesMirSym
    (polyExternalSpecCallContract
      targetDefPath expectedTypeArgs sidecarBody extraPre extraPost)
    (polyExternalSpecCallContract_frameAndTraitsPreserved
      targetDefPath expectedTypeArgs sidecarBody extraPre extraPost)
    body callees pre post fuel h_wp

/--
Discharge a `ModularVerificationResult` for a caller invoking a polymorphic
`#[external_spec]` target (`polyExternalSpecCallContract`), using
`wpMirFrameAndTraitsModularSym`.
-/
theorem verifyPolyExternalSpecMirSym
    (targetDefPath : DefPath)
    (expectedTypeArgs : List RigidTy)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        wpMirFrameAndTraitsModularSym
          (polyExternalSpecCallContract
            targetDefPath expectedTypeArgs sidecarBody extraPre extraPost)
          fuel
          body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              post args mem retVal mem')) :
    ModularVerificationResult
      { body := body
        envAssumed :=
          (polyExternalSpecCallContract
            targetDefPath expectedTypeArgs sidecarBody extraPre extraPost).holdsOn
        pre := pre
        post := post } :=
  verifyPolyExternalSpecWithCalleesMirSym
    targetDefPath expectedTypeArgs sidecarBody extraPre extraPost body .nil pre post fuel h_wp

/--
Single-pass symbolic caller–callee linking theorem with `callerCallees` and
`calleeCallees` under `C.holdsOn` via `wpMirNoCallSym`.
-/
theorem linkVerifiedContractMirCalleeWithCalleesSym
    {C : MirCallContract}
    {callerBody : CapturedMir}
    {callerCallees : List CapturedMir}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (h_caller :
      ModularVerificationResult
        { body := callerBody
          envAssumed := C.holdsOn
          pre := pre
          post := post
          callees := callerCallees })
    (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir)
    (calleeFuel : Nat)
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        wpMirNoCallSym calleeFuel calleeBody
          (enterExternalCalleeState calleeBody req.args req.memory calleeCallees)
          (fun out => C.post req (outcomeToRestoredCallAns req.memory out)))
    (h_fallback :
      ∀ req : MirCallReq,
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  linkVerifiedContractMirCalleeWithCalleesBounded
    h_caller calleeBody calleeCallees calleeFuel fallback
    (fun req h_eq h_pre => by
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      exact h_callee req h_eq h_pre)
    h_fallback

/--
Polymorphic single-pass symbolic caller–callee linking theorem with
`callerCallees` and `calleeCallees` under `C.holdsOn` via `wpMirNoCallSym`.
-/
theorem linkVerifiedPolyContractMirCalleeWithCalleesSym
    {C : MirCallContract}
    {callerBody : CapturedMir}
    {callerCallees : List CapturedMir}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (h_caller :
      ModularVerificationResult
        { body := callerBody
          envAssumed := C.holdsOn
          pre := pre
          post := post
          callees := callerCallees })
    (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir)
    (calleeFuel : Nat)
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        wpMirNoCallSym calleeFuel
          (instantiateCalleeForReq
            calleeBody callerBody.layouts req callerBody.traitImpls)
          (enterExternalCalleeState
            (instantiateCalleeForReq
              calleeBody callerBody.layouts req callerBody.traitImpls)
            req.args
            req.memory
            calleeCallees)
          (fun out => C.post req (outcomeToRestoredCallAns req.memory out)))
    (h_fallback :
      ∀ req : MirCallReq,
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkPolyCalleeWithCalleesHandler
          calleeBody callerBody.layouts calleeCallees fallback
          callerBody.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  linkVerifiedPolyContractMirCalleeWithCalleesBounded
    h_caller calleeBody calleeCallees calleeFuel fallback
    (fun req h_eq h_pre => by
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      exact h_callee req h_eq h_pre)
    h_fallback

/--
Trait-method or polymorphic single-pass symbolic caller–callee linking theorem
with `callerCallees` and `calleeCallees` under `C.holdsOn` via `wpMirNoCallSym`.
-/
theorem linkVerifiedTraitOrPolyContractMirCalleeWithCalleesSym
    {C : MirCallContract}
    {callerBody : CapturedMir}
    {callerCallees : List CapturedMir}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (h_caller :
      ModularVerificationResult
        { body := callerBody
          envAssumed := C.holdsOn
          pre := pre
          post := post
          callees := callerCallees })
    (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir)
    (calleeFuel : Nat)
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ (req : MirCallReq) (instBody : CapturedMir),
        lookupCallee
          [calleeBody]
          callerBody.layouts
          req.defPath
          req.typeArgs
          callerBody.traitImpls = .some instBody →
        C.pre req →
        wpMirNoCallSym calleeFuel instBody
          (enterExternalCalleeState instBody req.args req.memory calleeCallees)
          (fun out => C.post req (outcomeToRestoredCallAns req.memory out)))
    (h_fallback :
      ∀ req : MirCallReq,
        lookupCallee
          [calleeBody]
          callerBody.layouts
          req.defPath
          req.typeArgs
          callerBody.traitImpls = .none →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkTraitOrPolyCalleeWithCalleesHandler
          calleeBody callerBody.layouts calleeCallees fallback
          callerBody.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  linkVerifiedTraitOrPolyContractMirCalleeWithCalleesBounded
    h_caller calleeBody calleeCallees calleeFuel fallback
    (fun req instBody h_lk h_pre => by
      rw [← wpMirNoCallSym_eq_wpMirNoCallBounded]
      exact h_callee req instBody h_lk h_pre)
    h_fallback

/-! ## 15. `O(1)` Block & Callee Lookup Context Lemmas, Indirect `FnPtr` & Diverging Call Stepping, and Polymorphic Claim Combinators -/

/--
`O(1)` active callee normalization hypothesis (`ActiveCalleeCtx s body instBody`):
records that `s.memory.activeCallee.getD body = instBody`, avoiding repeated
evaluation and WHNF unrolling of `.getD` and `CapturedMir.instantiate` across steps.
-/
def ActiveCalleeCtx (s : MachineState) (body instBody : CapturedMir) : Prop :=
  s.memory.activeCallee.getD body = instBody

theorem ActiveCalleeCtx.init {body args callees} :
  ActiveCalleeCtx (initMachineStateWithCallees body args callees) body body := by unfold ActiveCalleeCtx; cases callees <;> rfl

theorem ActiveCalleeCtx.initMem {body args mem callees} :
  ActiveCalleeCtx (initMachineStateWithMemoryAndCallees body args mem callees) body (mem.activeCallee.getD body) := by unfold ActiveCalleeCtx; cases callees <;> rfl


theorem stepMirSymTree_of_activeCalleeCtx
    {body instBody : CapturedMir}
    {s : MachineState}
    (h_ctx : ActiveCalleeCtx s body instBody) :
    stepMirSymTree body s =
      match instBody.phase with
      | .other _ => .leaf MirStepNode.unsupported
      | _ =>
        match get? instBody.basicBlocks s.frame.blockIdx with
        | none => .leaf (MirStepNode.fail .ub)
        | some bb =>
          match get? bb.statements s.frame.stmtIdx with
          | some stmt =>
            evalStmtSymTree s stmt instBody.localDecls instBody.layouts
          | none =>
            if s.frame.stmtIdx == length bb.statements then
              evalTerminatorSymTree s bb.terminator instBody
            else .leaf (MirStepNode.fail .ub) := by
  unfold stepMirSymTree
  rw [h_ctx]

/--
`O(1)` basic-block lookup context hypothesis (`BlockCtx body idx bb`): records
that basic block `idx` in `body.basicBlocks` is `bb`, avoiding repeated linear
list traversal of `body.basicBlocks` during symbolic execution.
-/
def BlockCtx (body : CapturedMir) (idx : BasicBlockIdx) (bb : BasicBlockData) : Prop :=
  get? body.basicBlocks idx = .some bb

theorem get?_basicBlocks_of_blockCtx
    {body : CapturedMir} {idx : BasicBlockIdx} {bb : BasicBlockData}
    (h : BlockCtx body idx bb) :
    get? body.basicBlocks idx = .some bb :=
  h

/--
`O(1)` callee lookup context hypothesis
(`CalleeCtx callees callerLayouts defPath typeArgs extraTraitImpls resolvedBody`):
records that `lookupCallee` resolves `(defPath, typeArgs)` to `resolvedBody`,
avoiding repeated `CapturedMir.instantiate` and `TraitImplEntry` searches across
multi-frame `s.memory.callees` steps.
-/
def CalleeCtx
    (callees : List CapturedMir)
    (callerLayouts : LayoutTable)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (extraTraitImpls : List TraitImplEntry)
    (resolvedBody : CapturedMir) : Prop :=
  lookupCallee callees callerLayouts defPath typeArgs extraTraitImpls =
    .some resolvedBody

theorem lookupCallee_eq_of_calleeCtx
    {callees : List CapturedMir}
    {callerLayouts : LayoutTable}
    {defPath : DefPath}
    {typeArgs : List RigidTy}
    {extraTraitImpls : List TraitImplEntry}
    {resolvedBody : CapturedMir}
    (h : CalleeCtx callees callerLayouts defPath typeArgs extraTraitImpls resolvedBody) :
    lookupCallee callees callerLayouts defPath typeArgs extraTraitImpls =
      .some resolvedBody :=
  h

/--
Step `stepMirSymTree` in `O(1)` at statement `stmt` using a `BlockCtx`
hypothesis on the active body `s.memory.activeCallee.getD body`.
-/
theorem stepMirSymTree_stmt_of_blockCtx
    (body instBody : CapturedMir)
    (s : MachineState)
    (bb : BasicBlockData)
    (stmt : Statement)
    (h_ctx : ActiveCalleeCtx s body instBody)
    (h_phase : instBody.phase = .runtimeOptimized)
    (h_bb : BlockCtx instBody s.frame.blockIdx bb)
    (h_stmt : get? bb.statements s.frame.stmtIdx = .some stmt) :
    stepMirSymTree body s =
      evalStmtSymTree s stmt instBody.localDecls instBody.layouts := by
  unfold stepMirSymTree
  rw [h_ctx]
  dsimp only []
  rw [h_phase, h_bb]
  dsimp only []
  rw [h_stmt]

/--
Step `stepMirSymTree` in `O(1)` at terminator `bb.terminator` using a `BlockCtx`
hypothesis when `s.frame.stmtIdx == length bb.statements`.
-/
theorem stepMirSymTree_term_of_blockCtx
    (body instBody : CapturedMir)
    (s : MachineState)
    (bb : BasicBlockData)
    (h_ctx : ActiveCalleeCtx s body instBody)
    (h_phase : instBody.phase = .runtimeOptimized)
    (h_bb : BlockCtx instBody s.frame.blockIdx bb)
    (h_none : get? bb.statements s.frame.stmtIdx = .none)
    (h_end : (s.frame.stmtIdx == length bb.statements) = true) :
    stepMirSymTree body s =
      evalTerminatorSymTree s bb.terminator instBody := by
  unfold stepMirSymTree
  rw [h_ctx]
  dsimp only []
  rw [h_phase, h_bb]
  dsimp only []
  rw [h_none, h_end]
  rfl

/--
Direct `resolveCallTarget` reduction for a constant `RigidTy.fnDef defPath typeArgs`
operand.
-/
@[simp]
theorem resolveCallTarget_const_fnDef
    (s : MachineState)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (layoutIdx : LayoutIdx)
    (val : ConstValue)
    (argCount : Nat)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) :
    resolveCallTarget
      s
      (.constant { ty := { kind := .fnDef defPath typeArgs, layoutIdx := layoutIdx }, val := val })
      argCount
      bodyLocalDecls
      bodyLayouts =
    .ok
      { defPath := defPath
        typeArgs := typeArgs
        fnSig := .none
        isIndirect := false }
      s.frame.locals :=
  rfl

/--
Indirect `resolveCallTarget` reduction for a runtime `Value.ptr` function pointer
registered in `s.memory.fnPtrs`.
-/
theorem resolveCallTarget_indirect_fnPtr
    (s : MachineState)
    (func : Operand)
    (argCount : Nat)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (ptrVal : ProvenancePtr)
    (localsAfterFunc : List LocalSlot)
    (fnEntry : FnPtrEntry)
    (h_nonConst : extractCalleeDefPath? func = .none)
    (h_eval :
      evalOperand
        s.frame.locals
        func
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        (callStack := s.memory.callStack) =
      .ok (.ptr ptrVal 8) localsAfterFunc)
    (h_off : ptrVal.offsetBytes = 0)
    (h_noBorrow : lookupBorrow s.memory.borrows ptrVal.tag = .none)
    (h_fnPtr : lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry)
    (h_compat :
      fnEntryCompatibleWithCallSite
        fnEntry
        argCount
        (operandTy bodyLocalDecls bodyLayouts func) = true) :
    resolveCallTarget s func argCount bodyLocalDecls bodyLayouts =
      .ok
        { defPath := fnEntry.defPath
          typeArgs := fnEntry.typeArgs
          fnSig := fnEntry.fnSig
          isIndirect := true }
        localsAfterFunc := by
  unfold resolveCallTarget
  rw [h_nonConst, h_eval]
  dsimp only []
  rw [h_off, h_noBorrow]
  dsimp only [Nat.beq, Bool.and]
  rw [h_fnPtr]
  dsimp only []
  rw [h_compat]

/--
`evalTerminatorSymTree` for an unreachable basic-block terminator
(`TerminatorKind.unreachable`) reduces directly to `.leaf (MirStepNode.fail .ub)`.
-/
@[simp]
theorem evalTerminatorSymTree_unreachable_eq_ub
    (s : MachineState)
    (span : String)
    (currentBody : CapturedMir) :
    evalTerminatorSymTree s { kind := .unreachable, span := span } currentBody =
      .leaf (MirStepNode.fail .ub) :=
  rfl

theorem evalTerminatorSymTree_call_extCall
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        (callStack := s.memory.callStack) =
      .ok argVals locals')
    (h_indirect : resolvedTarget.isIndirect = false)
    (h_callee :
      lookupCallee
        s.memory.callees
        currentBody.layouts
        resolvedTarget.defPath
        resolvedTarget.typeArgs
        s.memory.traitImpls = .none)
    (_h_unreachable : isUnreachableCallTarget resolvedTarget.defPath = false)
    (_h_abort : isAbortingPanicDefPath resolvedTarget.defPath = false)
    (_h_unwind : isUnwindingPanicDefPath resolvedTarget.defPath = false)
    (h_exactDiv : isDirectExactDivTarget resolvedTarget = false)
    (h_intrinsic :
      evalDirectRustIntrinsic?
        s (some currentBody) resolvedTarget currentBody.localDecls
        currentBody.layouts argOps argVals locals' destination targetBb unwind = .none) :
    evalTerminatorSymTree
      s
      { kind := .call func argOps destination (.some targetBb) unwind, span := span }
      currentBody =
    .leaf
      (MirStepNode.extCall
        { defPath := resolvedTarget.defPath, typeArgs := resolvedTarget.typeArgs, args := argVals, memory := s.memory }
        (resumeExternalCall s locals' destination targetBb unwind)) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [h_callee]
  dsimp only []
  rw [h_exactDiv, h_indirect, h_intrinsic]
/--
`evalTerminatorSymTree` for a normal inlined call (`target = .some targetBb`)
resolved via `CalleeCtx`.
-/
theorem evalTerminatorSymTree_call_inlined_of_calleeCtx
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (calleeBody : CapturedMir)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        (callStack := s.memory.callStack) =
      .ok argVals locals')
    (h_callee :
      CalleeCtx
        s.memory.callees
        currentBody.layouts
        resolvedTarget.defPath
        resolvedTarget.typeArgs
        s.memory.traitImpls
        calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true) :
    evalTerminatorSymTree
      s
      { kind := .call func argOps destination (.some targetBb) unwind, span := span }
      currentBody =
    .leaf
      (MirStepNode.step
        (pushCalleeFrame
          s currentBody locals' destination targetBb calleeBody argVals unwind)) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [lookupCallee_eq_of_calleeCtx h_callee]
  dsimp only []
  rw [h_compat]

/--
`evalTerminatorSymTree` for an inlined tail call (`TerminatorKind.tailCall`)
resolved via `CalleeCtx`.

A tail call deallocates the caller's frame before entering the callee: the
semantics faults with `.ub` when an active protector still guards a tag that
targets a local of the returning frame (`hasFrameDeallocProtectorConflict`; that
branch is `evalTerminatorSymTree_tailCall_deallocConflict`), and otherwise
disables every borrow of the returning frame (`disableFrameBorrows`) in the
memory handed to the callee. `h_noDeallocConflict` selects the non-faulting
branch, which the semantics requires for the step to succeed.
-/
theorem evalTerminatorSymTree_tailCall_inlined_of_calleeCtx
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (calleeBody : CapturedMir)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        (callStack := s.memory.callStack) =
      .ok argVals locals')
    (h_callee :
      CalleeCtx
        s.memory.callees
        currentBody.layouts
        resolvedTarget.defPath
        resolvedTarget.typeArgs
        s.memory.traitImpls
        calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true)
    (h_noDeallocConflict :
      hasFrameDeallocProtectorConflict
        s.memory.borrows
        s.memory.activeProtectors
        (length s.memory.callStack)
        (length s.frame.locals) = false) :
    evalTerminatorSymTree
      s
      { kind := .tailCall func argOps, span := span }
      currentBody =
    .leaf
      (MirStepNode.step
        (enterTailCalleeFrame
          { s.memory with
            borrows :=
              disableFrameBorrows
                s.memory.borrows
                (length s.memory.callStack)
                (length s.frame.locals) }
          calleeBody argVals)) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [h_noDeallocConflict]
  dsimp only []
  rw [lookupCallee_eq_of_calleeCtx h_callee]
  dsimp only []
  rw [h_compat]

/--
`evalTerminatorSymTree` for a tail call (`TerminatorKind.tailCall`) whose
returning frame still has a local guarded by an active protector
(`hasFrameDeallocProtectorConflict`): deallocating the frame is undefined
behavior, so the step faults with `.ub` whatever the callee resolves to.
-/
theorem evalTerminatorSymTree_tailCall_deallocConflict
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        (callStack := s.memory.callStack) =
      .ok argVals locals')
    (h_deallocConflict :
      hasFrameDeallocProtectorConflict
        s.memory.borrows
        s.memory.activeProtectors
        (length s.memory.callStack)
        (length s.frame.locals) = true) :
    evalTerminatorSymTree
      s
      { kind := .tailCall func argOps, span := span }
      currentBody =
    .leaf (MirStepNode.fail .ub) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [h_deallocConflict]

/--
`evalTerminatorSymTree` for a diverging (`target = .none`) inlined call resolved
via `CalleeCtx`.
-/
theorem evalTerminatorSymTree_diverging_call_inlined_of_calleeCtx
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (calleeBody : CapturedMir)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        (callStack := s.memory.callStack) =
      .ok argVals locals')
    (h_callee :
      CalleeCtx
        s.memory.callees
        currentBody.layouts
        resolvedTarget.defPath
        resolvedTarget.typeArgs
        s.memory.traitImpls
        calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true) :
    evalTerminatorSymTree
      s
      { kind := .call func argOps destination .none unwind, span := span }
      currentBody =
    .leaf
      (MirStepNode.step
        (pushDivergingCalleeFrame
          s currentBody locals' destination unwind calleeBody argVals)) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [lookupCallee_eq_of_calleeCtx h_callee]
  dsimp only []
  rw [h_compat]

/--
`evalTerminatorSymTree` for an unresolved diverging (`target = .none`) external
call (neither an unreachable hint nor a built-in panic entrypoint) reduces to
`MirStepNode.extCall` with `resumeExternalDivergingCall`.
-/
theorem evalTerminatorSymTree_diverging_extCall
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (span : String)
    (currentBody : CapturedMir)
    (resolvedTarget : ResolvedCallTarget)
    (localsAfterFunc : List LocalSlot)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (h_res :
      resolveCallTarget
        s func (length argOps) currentBody.localDecls currentBody.layouts =
      .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        currentBody.layouts
        s.memory.callerLocals
        (callStack := s.memory.callStack) =
      .ok argVals locals')
    (h_none :
      lookupCallee
        s.memory.callees
        currentBody.layouts
        resolvedTarget.defPath
        resolvedTarget.typeArgs
        s.memory.traitImpls =
      .none)
    (h_not_unreach : isUnreachableCallTarget resolvedTarget.defPath = false)
    (h_not_abort : isAbortingPanicDefPath resolvedTarget.defPath = false)
    (h_not_unwind : isUnwindingPanicDefPath resolvedTarget.defPath = false) :
    evalTerminatorSymTree
      s
      { kind := .call func argOps destination .none unwind, span := span }
      currentBody =
    .leaf
      (MirStepNode.extCall
        { defPath := resolvedTarget.defPath
          typeArgs := resolvedTarget.typeArgs
          args := argVals
          memory := s.memory }
        (resumeExternalDivergingCall s locals' unwind)) := by
  dsimp only [evalTerminatorSymTree, evalTerminator, evalCallTerminator, bodyLocalDeclsOf]
  rw [h_res]
  dsimp only []
  rw [h_args]
  dsimp only []
  rw [h_none]
  dsimp only []
  cases resolvedTarget.isIndirect
  · dsimp only []
    rw [h_not_unreach, h_not_abort, h_not_unwind]
  · rfl

/--
Verify a universally quantified polymorphic stateless claim
`∀ typeArgs, typeArgs.length = polyBody.typeParamCount → VerificationResult (claimFor typeArgs)`
via single-pass symbolic evaluation (`verifyMirSafeSym`).
-/
theorem verifyPolyMirSym
    (polyBody : CapturedMir)
    (claimFor : TypeSubst → Claim)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (s : MachineState),
          s = initMachineStateWithCallees
            (claimFor typeArgs).body args (claimFor typeArgs).callees →
          (claimFor typeArgs).pre args →
          ActiveCalleeCtx s (claimFor typeArgs).body (claimFor typeArgs).body →
          wpMirSym fuel (claimFor typeArgs).body s
            (mirSafePost (fun retVal _ => (claimFor typeArgs).post args retVal))) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      VerificationResult (claimFor typeArgs) :=
  fun typeArgs h_len => verifyMirSafeSym (claimFor typeArgs) fuel (fun args h_pre => h_wp typeArgs h_len args _ rfl h_pre ActiveCalleeCtx.init)

/--
Panic-forbidding variant of `verifyPolyMirSym` (`mirNormalPost`).
-/
theorem verifyPolyMirNoPanicSym
    (polyBody : CapturedMir)
    (claimFor : TypeSubst → Claim)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (s : MachineState),
          s = initMachineStateWithCallees
            (claimFor typeArgs).body args (claimFor typeArgs).callees →
          (claimFor typeArgs).pre args →
          ActiveCalleeCtx s (claimFor typeArgs).body (claimFor typeArgs).body →
          wpMirSym fuel (claimFor typeArgs).body s
            (mirNormalPost (fun retVal _ => (claimFor typeArgs).post args retVal))) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      VerificationResult (claimFor typeArgs) :=
  fun typeArgs h_len => verifyMirNoPanicSym (claimFor typeArgs) fuel (fun args h_pre => h_wp typeArgs h_len args _ rfl h_pre ActiveCalleeCtx.init)

/--
Verify a universally quantified polymorphic stateful claim
`∀ typeArgs, typeArgs.length = polyBody.typeParamCount → StatefulVerificationResult (statefulClaimFor typeArgs)`
via single-pass symbolic evaluation (`verifyStatefulMirSym`).
-/
theorem verifyPolyStatefulMirSym
    (polyBody : CapturedMir)
    (statefulClaimFor : TypeSubst → StatefulClaim)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory) (s : MachineState),
          s = initMachineStateWithMemoryAndCallees
            (statefulClaimFor typeArgs).body args mem (statefulClaimFor typeArgs).callees →
          (statefulClaimFor typeArgs).pre args mem →
          ActiveCalleeCtx s (statefulClaimFor typeArgs).body (mem.activeCallee.getD (statefulClaimFor typeArgs).body) →
          wpMirSym fuel (statefulClaimFor typeArgs).body s
            (mirSafePost ((statefulClaimFor typeArgs).post args mem))) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      StatefulVerificationResult (statefulClaimFor typeArgs) :=
  fun typeArgs h_len =>
    verifyStatefulMirSym (statefulClaimFor typeArgs) fuel (fun args mem h_pre => h_wp typeArgs h_len args mem _ rfl h_pre ActiveCalleeCtx.initMem)

/--
Panic-forbidding variant of `verifyPolyStatefulMirSym` (`mirNormalPost`).
-/
theorem verifyPolyStatefulMirNoPanicSym
    (polyBody : CapturedMir)
    (statefulClaimFor : TypeSubst → StatefulClaim)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory) (s : MachineState),
          s = initMachineStateWithMemoryAndCallees
            (statefulClaimFor typeArgs).body args mem (statefulClaimFor typeArgs).callees →
          (statefulClaimFor typeArgs).pre args mem →
          ActiveCalleeCtx s (statefulClaimFor typeArgs).body (mem.activeCallee.getD (statefulClaimFor typeArgs).body) →
          wpMirSym fuel (statefulClaimFor typeArgs).body s
            (mirNormalPost ((statefulClaimFor typeArgs).post args mem))) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      StatefulVerificationResult (statefulClaimFor typeArgs) :=
  fun typeArgs h_len =>
    verifyStatefulMirNoPanicSym (statefulClaimFor typeArgs) fuel (fun args mem h_pre => h_wp typeArgs h_len args mem _ rfl h_pre ActiveCalleeCtx.initMem)

/--
Verify a universally quantified polymorphic total-correctness claim
`∀ typeArgs, typeArgs.length = polyBody.typeParamCount → TotalVerificationResult (totalClaimFor typeArgs)`
via single-pass symbolic evaluation (`verifyTotalMirSym`).
-/
theorem verifyPolyTotalMirSym
    (polyBody : CapturedMir)
    (totalClaimFor : TypeSubst → TotalClaim)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory) (s : MachineState),
          s = initMachineStateWithMemoryAndCallees
            (totalClaimFor typeArgs).body args mem (totalClaimFor typeArgs).callees →
          (totalClaimFor typeArgs).pre args mem →
          ActiveCalleeCtx s (totalClaimFor typeArgs).body (mem.activeCallee.getD (totalClaimFor typeArgs).body) →
          wpMirSym fuel (totalClaimFor typeArgs).body s
            (mirNormalPost ((totalClaimFor typeArgs).post args mem))) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      TotalVerificationResult (totalClaimFor typeArgs) :=
  fun typeArgs h_len =>
    verifyTotalMirSym (totalClaimFor typeArgs) fuel (fun args mem h_pre => h_wp typeArgs h_len args mem _ rfl h_pre ActiveCalleeCtx.initMem)

/--
Verify a universally quantified polymorphic scoped UB-exception claim
`∀ typeArgs, typeArgs.length = polyBody.typeParamCount → UbExceptionVerificationResult (ubExceptionClaimFor typeArgs)`
via single-pass symbolic evaluation (`verifyUbExceptionMirSym`).
-/
theorem verifyPolyUbExceptionMirSym
    (polyBody : CapturedMir)
    (ubExceptionClaimFor : TypeSubst → UbExceptionClaim)
    (fuel : Nat)
    (h_strict :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory) (s : MachineState),
          s = initMachineStateWithMemoryAndCallees
            (ubExceptionClaimFor typeArgs).body args mem (ubExceptionClaimFor typeArgs).callees →
          (ubExceptionClaimFor typeArgs).pre args mem →
          (ubExceptionClaimFor typeArgs).strictSafetyPre args mem →
          ActiveCalleeCtx s (ubExceptionClaimFor typeArgs).body (mem.activeCallee.getD (ubExceptionClaimFor typeArgs).body) →
          wpMirSym fuel (ubExceptionClaimFor typeArgs).body s
            (fun out =>
              ∀ retVal mem', out = .normal (retVal, mem') →
                (ubExceptionClaimFor typeArgs).post args mem retVal mem'))
    (h_waived :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory),
          (ubExceptionClaimFor typeArgs).pre args mem →
          wpMirUbWaivedSym fuel (ubExceptionClaimFor typeArgs).body
            (initMachineStateWithMemoryAndCallees
              (ubExceptionClaimFor typeArgs).body
              args
              mem
              (ubExceptionClaimFor typeArgs).callees)
            (fun out =>
              ∀ retVal mem', out = .normal (retVal, mem') →
                (ubExceptionClaimFor typeArgs).post args mem retVal mem')) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      UbExceptionVerificationResult (ubExceptionClaimFor typeArgs) :=
  fun typeArgs h_len =>
    verifyUbExceptionMirSym
      (ubExceptionClaimFor typeArgs)
      fuel
      (fun args mem h_pre h_strict_pre => h_strict typeArgs h_len args mem _ rfl h_pre h_strict_pre ActiveCalleeCtx.initMem)
      (h_waived typeArgs h_len)

/--
Verify a universally quantified polymorphic modular claim
`∀ typeArgs, typeArgs.length = polyBody.typeParamCount → ModularVerificationResult ...`
via single-pass symbolic evaluation (`verifyModularContractWithCalleesMirSym`).
-/
theorem verifyPolyModularMirSym
    (polyBody : CapturedMir)
    (contractFor : TypeSubst → MirCallContract)
    (bodyFor : TypeSubst → CapturedMir)
    (calleesFor : TypeSubst → List CapturedMir)
    (preFor : TypeSubst → List Value → Memory → Prop)
    (postFor : TypeSubst → List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory),
          preFor typeArgs args mem →
          wpMirModularSym (contractFor typeArgs) fuel (bodyFor typeArgs)
            (initMachineStateWithMemoryAndCallees
              (bodyFor typeArgs) args mem (calleesFor typeArgs))
            (fun out =>
              ∀ retVal mem', out = .normal (retVal, mem') →
                postFor typeArgs args mem retVal mem')) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      ModularVerificationResult
        { body := bodyFor typeArgs
          envAssumed := (contractFor typeArgs).holdsOn
          pre := preFor typeArgs
          post := postFor typeArgs
          callees := calleesFor typeArgs } :=
  fun typeArgs h_len =>
    verifyModularContractWithCalleesMirSym
      (contractFor typeArgs)
      (bodyFor typeArgs)
      (calleesFor typeArgs)
      (preFor typeArgs)
      (postFor typeArgs)
      fuel
      (h_wp typeArgs h_len)

/--
Verify a universally quantified polymorphic modular claim via
frame-and-`traitImpls`-restoring symbolic evaluation
(`wpMirFrameAndTraitsModularSym`).
-/
theorem verifyPolyModularFrameAndTraitsMirSym
    (polyBody : CapturedMir)
    (contractFor : TypeSubst → MirCallContract)
    (h_frame :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (req : MirCallReq) (ans : MirCallAns),
          (contractFor typeArgs).post req ans →
          ans.frameAndTraitsPreserved req.memory)
    (bodyFor : TypeSubst → CapturedMir)
    (calleesFor : TypeSubst → List CapturedMir)
    (preFor : TypeSubst → List Value → Memory → Prop)
    (postFor : TypeSubst → List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ (typeArgs : TypeSubst),
        typeArgs.length = polyBody.typeParamCount →
        ∀ (args : List Value) (mem : Memory),
          preFor typeArgs args mem →
          wpMirFrameAndTraitsModularSym (contractFor typeArgs) fuel (bodyFor typeArgs)
            (initMachineStateWithMemoryAndCallees
              (bodyFor typeArgs) args mem (calleesFor typeArgs))
            (fun out =>
              ∀ retVal mem', out = .normal (retVal, mem') →
                postFor typeArgs args mem retVal mem')) :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = polyBody.typeParamCount →
      ModularVerificationResult
        { body := bodyFor typeArgs
          envAssumed := (contractFor typeArgs).holdsOn
          pre := preFor typeArgs
          post := postFor typeArgs
          callees := calleesFor typeArgs } :=
  fun typeArgs h_len =>
    verifyModularFrameAndTraitsContractWithCalleesMirSym
      (contractFor typeArgs)
      (h_frame typeArgs h_len)
      (bodyFor typeArgs)
      (calleesFor typeArgs)
      (preFor typeArgs)
      (postFor typeArgs)
      fuel
      (h_wp typeArgs h_len)

/-! ## 10. Differential Testing Outcome Classifiers & Strict UB / Panic Refutation Combinators -/

/--
Fine-grained bounded execution verdict for differential testing against Miri.

Unlike `reachesFaultExecBounded` (which conflates `FailureKind.ub` and
`FailureKind.unsupported`), `MirDiffVerdict` separates genuine Undefined
Behavior (`.ub`) from fail-closed unmodeled constructs (`.unsupported`),
unresolved external calls (`.externalCall`), safe unwinding (`.panic`),
process abort (`.abort`), normal termination (`.normal`), and fuel exhaustion
(`.outOfFuel`).
-/
inductive MirDiffVerdict : Type where
  | normal (retVal : Value) (mem : Memory)
  | panic
  | abort
  | ub
  | unsupported
  | externalCall (defPath : DefPath)
  | outOfFuel

/--
Decidable, printable projection of `MirDiffVerdict` for `#eval` reporting and
equality checks in differential test suites.
-/
inductive MirDiffTag : Type where
  | normalUnit
  | normalScalar (bits : Nat) (sizeBytes : Nat)
  | normalOther
  | panic
  | abort
  | ub
  | unsupported
  | externalCall (defPath : DefPath)
  | outOfFuel
  deriving DecidableEq, Repr

/-- Project a `MirDiffVerdict` to its body-independent `MirDiffTag`. -/
def MirDiffVerdict.toTag : MirDiffVerdict → MirDiffTag
  | .normal .unit _ => .normalUnit
  | .normal (.scalar sc) _ => .normalScalar sc.bits sc.sizeBytes
  | .normal _ _ => .normalOther
  | .panic => .panic
  | .abort => .abort
  | .ub => .ub
  | .unsupported => .unsupported
  | .externalCall defPath => .externalCall defPath
  | .outOfFuel => .outOfFuel

/--
Return `true` when every variant in `variants` has an empty `FieldsShape`
(`.arbitrary [] _`).
-/
def allVariantsFieldless : List FieldsShape → Bool
  | .nil => true
  | .arbitrary .nil _ :: rest => allVariantsFieldless rest
  | _ :: _ => false

/--
Return `true` when return local `_0` in `body.localDecls` can represent a
scalar-backed enum (`RigidTy.adt`, generic `RigidTy.param`, or an omitted
`localDecls` table).

Rejects zero-element arrays (`[T; 0]`), empty tuples (`()`), and other non-ADT
types that construct `.aggregate 0 []` in MIR so they are never misclassified
as scalar-represented enums if `body.fnAbi.ret.layout` differs.
-/
def returnLocalAllowsScalarEnum (body : CapturedMir) : Bool :=
  match get? body.localDecls 0 with
  | .none => true
  | .some decl0 =>
    match decl0.ty.kind with
    | .adt _ _ => true
    | .param _ _ => true
    | _ => false

/--
Return the cardinality of inclusive wrap-around range `r` within `[0, modulus)`,
or `.none` when either endpoint lies outside `[0, modulus)`.
-/
def wrappingRangeCount (r : WrappingRange) (modulus : Nat) : Option Nat :=
  match
    Bool.and
      (Nat.ble (.succ r.start) modulus)
      (Nat.ble (.succ r.end_) modulus)
  with
  | false => .none
  | true =>
    match Nat.ble r.start r.end_ with
    | true => .some (Nat.add (Nat.sub r.end_ r.start) 1)
    | false => .some (Nat.add (Nat.add (Nat.sub modulus r.start) r.end_) 1)

/--
Resolve the concrete positive-sized return `TypeLayout` of `body`.

Consults return local `_0` in `body.layouts` first. When `_0` resolves to a
concrete zero-sized layout (`l.size.bytes = 0` and
`TypeLayout.isParamPlaceholder l = false`), returns `.none` without falling back
to `body.fnAbi.ret.layout` so concrete zero-sized return types stay zero-sized.
Falls back to `body.fnAbi.ret.layout` only when `_0` is absent from
`body.localDecls`, missing from `body.layouts`, or still an uninstantiated
parametric placeholder slot.
-/
def resolveReturnLayout? (body : CapturedMir) : Option TypeLayout :=
  let fallbackFnAbi : Option TypeLayout :=
    match body.fnAbi.ret.layout.size.bytes with
    | _ + 1 => .some body.fnAbi.ret.layout
    | 0 => .none
  match get? body.localDecls 0 with
  | .some decl0 =>
    match LayoutTable.lookup body.layouts decl0.ty.layoutIdx with
    | .some l =>
      match l.size.bytes with
      | _ + 1 => .some l
      | 0 =>
        match TypeLayout.isParamPlaceholder l with
        | true => fallbackFnAbi
        | false => .none
    | .none => fallbackFnAbi
  | .none => fallbackFnAbi

/--
Validate that candidate bit pattern `bits` fits in `[0, modulus)` and satisfies
`ScalarInt.inRange` for `sz` bytes under `validRange`.
-/
def validateScalarEnumCandidate
    (bits sz modulus : Nat) (validRange : WrappingRange) :
    Option (Nat × Nat) :=
  match
    Bool.and
      (Nat.ble (.succ bits) modulus)
      (ScalarInt.inRange { bits := bits, sizeBytes := sz } validRange)
  with
  | true => .some (bits, sz)
  | false => .none

/--
Compute the candidate unsigned discriminant bit pattern of `variantIdx` for a
validated `sz`-byte integer scalar return layout (`modulus = scalarModulus sz`).

Because `CapturedMir` records `TypeLayout` without `AdtDef` per-variant
discriminants, `VariantsShape.multiple` determines each variant's bit pattern
only when:

1. Every variant has an empty `FieldsShape` (`allVariantsFieldless`), excluding
   niche-encoded payload enums such as `Option<bool>` or `Option<OnlyZero>`
   whose fieldless variant uses a displaced niche tag.
2. `wrappingRangeCount validRange modulus` equals `variantShapes.length`,
   excluding gapped explicit-discriminant enums (`A = 1, B = 5`) while unifying
   zero-based enums (`0..=k-1`), `rustc`-captured single-variant `#[repr(int)]`
   enums (`c..=c` with one `VariantsShape.multiple` entry), non-zero contiguous
   enums (`a..=a+k-1`), and negative-start signed contiguous enums such as
   `core::cmp::Ordering` (`255..=1` for `i8`) via
   `wrapScalarBits (validRange.start + variantIdx) modulus`. Non-monotonic
   permutations of a contiguous range (`High = 2, Mid = 1, Low = 0`) share the
   same `TypeLayout` as ascending order until `CapturedMir` captures `AdtDef`
   discriminants.
3. Full-width signed `0..=modulus-1` ranges are excluded because wrapping
   normalization erases whether variant `0` starts at `0` or `-2^(8*sz - 1)`.
-/
def scalarEnumCandidateBits?
    (body : CapturedMir)
    (retLayout : TypeLayout)
    (sz modulus : Nat)
    (isSigned : Bool)
    (validRange : WrappingRange)
    (variantIdx : VariantIdx) :
    Option Nat :=
  match retLayout.variants with
  | .multiple _ _ (vHead :: vTail) =>
    let variantShapes := vHead :: vTail
    let numVariants := length variantShapes
    let rangeMatchesCount :=
      match wrappingRangeCount validRange modulus with
      | .some cnt => Nat.beq cnt numVariants
      | .none => false
    let nonAmbiguousSignedFull :=
      Bool.not
        (Bool.and
          isSigned
          (Bool.and
            (Nat.beq validRange.start 0)
            (Nat.beq validRange.end_ (Nat.sub modulus 1))))
    let ok :=
      Bool.and
        (Nat.ble (.succ variantIdx) numVariants)
        (Bool.and
          (allVariantsFieldless variantShapes)
          (Bool.and rangeMatchesCount nonAmbiguousSignedFull))
    match ok with
    | true => .some (wrapScalarBits (Nat.add validRange.start variantIdx) modulus)
    | false => .none
  | .multiple _ _ .nil =>
    match wrappingRangeCount validRange modulus with
    | .none => .none
    | .some _ =>
      let isOrdering :=
        match get? body.localDecls 0 with
        | .some { ty := { kind := .adt defPath _, .. }, .. } =>
          Bool.and
            (stringEq defPath "core::cmp::Ordering")
            (Bool.and
              (Nat.beq sz 1)
              (Bool.and
                (Nat.beq validRange.start 255)
                (Nat.beq validRange.end_ 1)))
        | _ => false
      match isOrdering with
      | true =>
        match variantIdx with
        | 0 => .some 255
        | 1 => .some 0
        | 2 => .some 1
        | _ => .none
      | false =>
        match Bool.and (Bool.not isSigned) (Nat.beq validRange.start 0) with
        | true => .some variantIdx
        | false => .none
  | .single expectedIdx =>
    match
      retLayout.fields,
      Nat.beq variantIdx expectedIdx,
      Nat.beq validRange.start validRange.end_
    with
    | .arbitrary .nil _, true, true => .some validRange.start
    | _, _, _ => .none
  | .empty => .none

/--
Compute the unsigned `(bits, sizeBytes)` scalar representation of a fieldless
enum return value `.aggregate variantIdx []` when `body`'s return layout uses
`BackendRepr.scalar (ScalarLayout.initialized (.int (8 * sz) _) validRange)`
with `1 ≤ sz ≤ 16`.

MIR execution preserves fieldless enum values as `Value.aggregate variantIdx []`
so `Rvalue.discriminant` can inspect their variant index, whereas Miri's
differential runner observes the return place's `BackendRepr::Scalar` bit
pattern. This helper bridges that representation at function return while
keeping zero-sized types, payload-bearing aggregates, niche-encoded payload
enums, and gapped explicit-discriminant enums classified as `.none`.
-/
def scalarEnumReturnTag?
    (body : CapturedMir) (variantIdx : VariantIdx) : Option (Nat × Nat) :=
  match returnLocalAllowsScalarEnum body, resolveReturnLayout? body with
  | true, .some retLayout =>
    match
      retLayout.isUninhabited,
      retLayout.size.bytes,
      retLayout.backendRepr
    with
    | false, sz@(_ + 1), .scalar (.initialized (.int primBits isSigned) validRange) =>
      match Bool.and (Nat.ble sz 16) (Nat.beq primBits (Nat.mul sz 8)) with
      | false => .none
      | true =>
        let modulus := scalarModulus sz
        match
          scalarEnumCandidateBits?
            body retLayout sz modulus isSigned validRange variantIdx
        with
        | .some candidateBits =>
          validateScalarEnumCandidate candidateBits sz modulus validRange
        | .none => .none
    | _, _, _ => .none
  | _, _ => .none

/--
Project a `MirDiffVerdict` to its decidable `MirDiffTag` using `body`'s return
layout metadata so scalar-represented fieldless enums report `.normalScalar`
matching Miri's `BackendRepr::Scalar` runner.
-/
def MirDiffVerdict.toTagWithBody
    (body : CapturedMir) (v : MirDiffVerdict) : MirDiffTag :=
  match v with
  | .normal (.aggregate variantIdx .nil) _ =>
    match scalarEnumReturnTag? body variantIdx with
    | .some (bits, sz) => .normalScalar bits sz
    | .none => .normalOther
  | _ => v.toTag

/--
Evaluate `body` from `st : MirExecState` for up to `fuel` steps, classifying the
terminal outcome or fault into a `MirDiffVerdict`.
-/
def evalMirDiffExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : MirDiffVerdict :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret (.normal (retVal, mem)) => .normal retVal mem
    | .ret .panic => .panic
    | .ret .abort => .abort
    | .tau st' => evalMirDiffExecBounded fuel' body st'
    | .vis (.inl (.fail .ub)) _ => .ub
    | .vis (.inl (.fail .unsupported)) _ => .unsupported
    | .vis (.inl (.fail .outOfFuel)) _ => .outOfFuel
    | .vis (.inr (.inl _)) k => evalMirDiffExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) _ => .externalCall req.defPath

/--
Evaluate `body` starting from `s : MachineState` for up to `fuel` steps and
return its `MirDiffVerdict`.
-/
def evalMirDiffBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : MirDiffVerdict :=
  evalMirDiffExecBounded fuel body (.running s)

/--
Evaluate `body` starting from `s : MachineState` for up to `fuel` steps and
return its decidable `MirDiffTag`.
-/
def evalMirDiffTagBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : MirDiffTag :=
  (evalMirDiffBounded fuel body s).toTagWithBody body

/--
Return the active statement or terminator source span of `st` in `body` (or
`"none"` when not running or when the span is empty or `"<dummy>"`).
-/
def activeMirSpan (body : CapturedMir) (st : MirExecState) : String :=
  let raw :=
    match st with
    | .running s =>
      let cur :=
        match s.memory.activeCallee with
        | .some callee => callee
        | .none => body
      match get? cur.basicBlocks s.frame.blockIdx with
      | .some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | .some stmt => stmt.span
        | .none => bb.terminator.span
      | .none => "none"
    | _ => "none"
  match Bool.or (stringEq raw "") (stringEq raw "<dummy>") with
  | true => "none"
  | false => raw

/--
Evaluate `body` from `st : MirExecState` for up to `fuel` steps and return both
its `MirDiffTag` (via `MirDiffVerdict.toTagWithBody`) and the active fault or
unwind source span (`"none"` on normal return).
-/
def probeMirDiffExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) :
    MirDiffTag × String :=
  match fuel with
  | 0 => (.outOfFuel, activeMirSpan body st)
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret (.normal (retVal, mem)) =>
      ((MirDiffVerdict.normal retVal mem).toTagWithBody body, "none")
    | .ret .panic => (.panic, activeMirSpan body st)
    | .ret .abort => (.abort, activeMirSpan body st)
    | .tau st' => probeMirDiffExecBounded fuel' body st'
    | .vis (.inl (.fail .ub)) _ => (.ub, activeMirSpan body st)
    | .vis (.inl (.fail .unsupported)) _ => (.unsupported, activeMirSpan body st)
    | .vis (.inl (.fail .outOfFuel)) _ => (.outOfFuel, activeMirSpan body st)
    | .vis (.inr (.inl _)) k =>
      probeMirDiffExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) _ =>
      (.externalCall req.defPath, activeMirSpan body st)

/--
Evaluate `body` starting from `s : MachineState` for up to `fuel` steps and
return its `(MirDiffTag, span)` pair.
-/
def probeMirDiffBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) :
    MirDiffTag × String :=
  probeMirDiffExecBounded fuel body (.running s)

/--
`probeMirDiffExecBounded` always agrees in its tag projection with
`(evalMirDiffExecBounded fuel body st).toTagWithBody body`.
-/
theorem probeMirDiffExecBounded_fst_eq_toTagWithBody
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) :
    (probeMirDiffExecBounded fuel body st).1 =
      (evalMirDiffExecBounded fuel body st).toTagWithBody body := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    unfold probeMirDiffExecBounded evalMirDiffExecBounded
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal p =>
        rcases p with ⟨retVal, mem⟩
        rfl
      | panic => rfl
      | abort => rfl
    | tau st' => exact ih st'
    | vis i k =>
      rcases i with f | (e | c)
      · rcases f with ⟨fk⟩
        cases fk <;> rfl
      · cases e
        exact ih (k PUnit.unit)
      · rcases c with ⟨req⟩
        rfl

/--
`probeMirDiffBounded` always agrees in its tag projection with
`evalMirDiffTagBounded`.
-/
theorem probeMirDiffBounded_fst_eq_evalMirDiffTagBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) :
    (probeMirDiffBounded fuel body s).1 =
      evalMirDiffTagBounded fuel body s :=
  probeMirDiffExecBounded_fst_eq_toTagWithBody fuel body (.running s)

/--
Computable bounded strict-UB detector over `MirExecState`: returns `true` only
when `body` reaches an explicit Undefined Behavior fault (`FailureKind.ub`)
within `fuel` steps along `.tau` and `MirObsE` transitions.

Crucially, `reachesStrictUBExecBounded` returns `false` on
`FailureKind.unsupported`, ensuring that differential tests against Miri `fail/`
suites never mistake an unimplemented MIR feature for a successful UB detection.
-/
def reachesStrictUBExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret _ => false
    | .tau st' => reachesStrictUBExecBounded fuel' body st'
    | .vis (.inl (.fail .ub)) _ => true
    | .vis (.inl (.fail .unsupported)) _ => false
    | .vis (.inl (.fail .outOfFuel)) _ => false
    | .vis (.inr (.inl _)) k =>
      reachesStrictUBExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr _)) _ => false

/-- Computable bounded strict-UB detector starting from `s : MachineState`. -/
def reachesStrictUBBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Bool :=
  reachesStrictUBExecBounded fuel body (.running s)

/--
Every strict-UB detection (`reachesStrictUBExecBounded`) is also a fault
detection (`reachesFaultExecBounded`).
-/
theorem reachesFaultExecBounded_of_reachesStrictUBExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_ub : reachesStrictUBExecBounded fuel body st = true) :
    reachesFaultExecBounded fuel body st = true := by
  induction fuel generalizing st with
  | zero => nomatch h_ub
  | succ fuel' ih =>
    unfold reachesStrictUBExecBounded at h_ub
    unfold reachesFaultExecBounded
    cases h_step : stepMirState body st with
    | ret _ =>
      simp only [h_step] at h_ub
      nomatch h_ub
    | tau st' =>
      simp only [h_step] at h_ub ⊢
      exact ih st' h_ub
    | vis i k =>
      rcases i with f | (e | c)
      · rfl
      · simp only [h_step] at h_ub ⊢
        exact ih (k PUnit.unit) h_ub
      · simp only [h_step] at h_ub
        nomatch h_ub

/--
If `reachesStrictUBBounded fuel body s = true`, then `mirTree body s` violates
`TreeSafe` by reaching `FailureKind.ub`.
-/
theorem reachesStrictUBBounded_not_treeSafe
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (h_ub : reachesStrictUBBounded fuel body s = true) :
    ¬ TreeSafe (mirTree body s) :=
  reachesFaultBounded_not_treeSafe fuel body s
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded fuel body (.running s) h_ub)

/--
Refute a stateless `c : Claim` (`¬ c.holds`) by exhibiting a concrete input
`args` satisfying `c.pre args` whose bounded execution specifically hits
`FailureKind.ub` (and not `.unsupported`) within `fuel` steps.
-/
theorem refuteClaimByStrictUB
    (c : Claim)
    (fuel : Nat)
    (args : List Value)
    (h_pre : c.pre args)
    (h_ub :
      reachesStrictUBBounded fuel c.body
        (initMachineStateWithCallees c.body args c.callees) = true := by
      rfl) :
    ¬ c.holds :=
  refuteClaimByBoundedUB c fuel args h_pre
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded
      fuel c.body (.running (initMachineStateWithCallees c.body args c.callees)) h_ub)

/--
Refute a stateful `c : StatefulClaim` (`¬ c.holds`) by exhibiting a concrete
`(args, mem)` satisfying `c.pre args mem` whose bounded execution specifically
hits `FailureKind.ub` (and not `.unsupported`) within `fuel` steps.
-/
theorem refuteStatefulClaimByStrictUB
    (c : StatefulClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (h_ub :
      reachesStrictUBBounded fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) = true := by
      rfl) :
    ¬ c.holds :=
  refuteStatefulClaimByBoundedUB c fuel args mem h_pre
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded
      fuel c.body (.running (initMachineStateWithMemoryAndCallees c.body args mem c.callees)) h_ub)

/--
Refute a total-correctness `c : TotalClaim` (`¬ c.holds`) by exhibiting a
concrete `(args, mem)` satisfying `c.pre args mem` whose bounded execution
specifically hits `FailureKind.ub` (and not `.unsupported`) within `fuel` steps.
-/
theorem refuteTotalClaimByStrictUB
    (c : TotalClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (h_ub :
      reachesStrictUBBounded fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) = true := by
      rfl) :
    ¬ c.holds :=
  refuteTotalClaimByBoundedUB c fuel args mem h_pre
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded
      fuel c.body (.running (initMachineStateWithMemoryAndCallees c.body args mem c.callees)) h_ub)

/--
Computable bounded panic detector over `MirExecState`: returns `true` when
`body` reaches `.ret .panic` within `fuel` steps along `.tau` and `MirObsE`
transitions without hitting any fault.
-/
def reachesPanicExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret .panic => true
    | .ret (.normal _) => false
    | .ret .abort => false
    | .tau st' => reachesPanicExecBounded fuel' body st'
    | .vis (.inl _) _ => false
    | .vis (.inr (.inl _)) k => reachesPanicExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr _)) _ => false

/-- Computable bounded panic detector starting from `s : MachineState`. -/
def reachesPanicBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Bool :=
  reachesPanicExecBounded fuel body (.running s)

/--
Soundness of `reachesPanicExecBounded`: if `reachesPanicExecBounded fuel body st`
returns `true`, then `ITree.cofix (stepMirState body) st` reaches `.ret .panic`
along some finite event trace `tr`.
-/
theorem reachesPanicExecBounded_reachesRet
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_panic : reachesPanicExecBounded fuel body st = true) :
    ∃ tr, ReachesRet (ITree.cofix (stepMirState body) st) tr .panic := by
  induction fuel generalizing st with
  | zero => nomatch h_panic
  | succ fuel' ih =>
    unfold reachesPanicExecBounded at h_panic
    have h_obs :
        (ITree.cofix (stepMirState body) st).observe =
          (stepMirState body st).map (ITree.cofix (stepMirState body)) :=
      ITree.observe_cofix (stepMirState body) st
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal _ =>
        simp only [h_step] at h_panic
        nomatch h_panic
      | panic =>
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        exact ⟨[], _, Reaches.refl _, h_obs⟩
      | abort =>
        simp only [h_step] at h_panic
        nomatch h_panic
    | tau st' =>
      simp only [h_step] at h_panic
      rw [h_step] at h_obs
      dsimp only [ITreeF.map] at h_obs
      rcases ih st' h_panic with ⟨tr, u, h_reach, h_u⟩
      exact ⟨tr, u, Reaches.tau h_obs h_reach, h_u⟩
    | vis i k =>
      rcases i with f | (e | c)
      · simp only [h_step] at h_panic
        nomatch h_panic
      · simp only [h_step] at h_panic
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        rcases ih (k PUnit.unit) h_panic with ⟨tr, u, h_reach, h_u⟩
        exact ⟨⟨.inr (.inl e), PUnit.unit⟩ :: tr, u,
          Reaches.vis h_obs False.elim PUnit.unit h_reach, h_u⟩
      · simp only [h_step] at h_panic
        nomatch h_panic

/--
If `reachesPanicBounded fuel body s = true`, then `mirTree body s` reaches
`.ret .panic` along some finite event trace `tr`.
-/
theorem reachesPanicBounded_reachesRet
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (h_panic : reachesPanicBounded fuel body s = true) :
    ∃ tr, ReachesRet (mirTree body s) tr .panic :=
  reachesPanicExecBounded_reachesRet fuel body (.running s) h_panic

/--
Refute a total-correctness `c : TotalClaim` (`¬ c.holds`) by exhibiting a
concrete `(args, mem)` satisfying `c.pre args mem` whose bounded execution
cleanly unwinds to `.ret .panic` within `fuel` steps.
-/
theorem refuteTotalClaimByBoundedPanic
    (c : TotalClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (h_panic :
      reachesPanicBounded fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) = true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  rcases reachesPanicBounded_reachesRet fuel c.body
    (initMachineStateWithMemoryAndCallees c.body args mem c.callees) h_panic with ⟨tr, h_ret⟩
  rcases (h_holds args mem h_pre).2.2.2 tr .panic h_ret with
    ⟨_, _, h_eq, _⟩
  nomatch h_eq

/--
If `reachesPanicExecBounded fuel body st = true`, then `wpCoalBounded` holds
under `mirDefaultWP` with vacuous normal-return postcondition
`(∀ retVal mem', out = .normal (retVal, mem') → False)`, certifying that the
panic execution path is completely UB-free (`TreeSafe`).
-/
theorem wpCoalBounded_of_reachesPanicExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_panic : reachesPanicExecBounded fuel body st = true) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body)
      (fun out _ => ∀ retVal mem', out = .normal (retVal, mem') → False)
      st PUnit.unit := by
  induction fuel generalizing st with
  | zero => nomatch h_panic
  | succ fuel' ih =>
    unfold reachesPanicExecBounded at h_panic
    unfold wpCoalBounded
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal _ =>
        simp only [h_step] at h_panic
        nomatch h_panic
      | panic =>
        intro _ _ h_eq
        nomatch h_eq
      | abort =>
        simp only [h_step] at h_panic
        nomatch h_panic
    | tau st' =>
      simp only [h_step] at h_panic ⊢
      exact ih st' h_panic
    | vis i k =>
      rcases i with f | (e | c)
      · simp only [h_step] at h_panic
        nomatch h_panic
      · simp only [h_step] at h_panic ⊢
        cases e
        exact ih (k PUnit.unit) h_panic
      · simp only [h_step] at h_panic
        nomatch h_panic

/--
If `reachesPanicBounded fuel body s = true`, then `wpMirBounded` holds with
postcondition `∀ retVal mem', out = .normal (retVal, mem') → False`.
-/
theorem wpMirBounded_of_reachesPanicBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (h_panic : reachesPanicBounded fuel body s = true) :
    wpMirBounded fuel body s
      (fun out => ∀ retVal mem', out = .normal (retVal, mem') → False) :=
  wpCoalBounded_of_reachesPanicExecBounded fuel body (.running s) h_panic

/--
Certify a Miri `panic` test at `(args, mem)`: proves both
1. `StatefulVerificationResult` with `post := False` (certifying that execution
   unwinds without Undefined Behavior and never returns normally), and
2. `¬ TotalClaim.holds` (refuting total correctness because execution panics).
-/
theorem verifySafePanicMirPointBounded
    (body : CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_panic :
      reachesPanicBounded fuel body
        (initMachineStateWithMemory body args mem) = true := by
      rfl) :
    StatefulVerificationResult
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ _ _ => False } ∧
    ¬ ({ body := body
         pre := fun a m => a = args ∧ m = mem
         post := fun _ _ _ _ => True } : TotalClaim).holds := by
  refine ⟨?_, ?_⟩
  · refine verifyStatefulMirBounded _ fuel ?_
    rintro a m ⟨rfl, rfl⟩
    exact wpMirBounded_of_reachesPanicBounded fuel body
      (initMachineStateWithMemory body a m) h_panic
  · exact refuteTotalClaimByBoundedPanic
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ _ _ => True }
      fuel args mem ⟨rfl, rfl⟩ h_panic

/-! ### Safe Panics Across Uninterpreted External Calls -/

/--
Frame-preserving rely contract for the external calls of a modular safe-panic
certificate (`verifyModularSafePanicMirBounded`). It places no requirement on a
call request, and it assumes only that the callee returns or unwinds to the
same call frame (`callFramePreserved`) or aborts. It assumes nothing about the
returned value or about the rest of the post-call memory.

A `StatefulVerificationResult` cannot certify a body that panics after an
uninterpreted external call: `mirDefaultWP` lets that call return any answer,
including one whose memory carries a corrupted call stack or callee table, and
the caller can then fault. This contract rules out exactly those answers.

`TrustedBoundary.checkStatementOrigins` rejects a `Verify.*` certificate whose
statement mentions an `Anneal.*` constant, so generated certificates spell out
this structure with `Trusted.*` constants only. That spelling and this
definition agree by unfolding.
-/
def framePreservingCallContract : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ memAfter => callFramePreserved req.memory memAfter
    | .panicked memAfter => callFramePreserved req.memory memAfter
    | .aborted => True

/--
Every answer that `framePreservingCallContract` permits preserves the caller's
call frame, so `wpMirFrameModularSym` may restore that frame after the call.
-/
theorem framePreservingCallContract_framePreserved :
    ∀ (req : MirCallReq) (ans : MirCallAns),
      framePreservingCallContract.post req ans →
        ans.framePreserved req.memory := by
  intro req ans h_post
  cases ans <;> exact h_post

/--
`framePreservingCallContract` is satisfiable, so a certificate that assumes it
is not vacuous: the handler under which every external call returns `retVal`
and leaves memory unchanged implements it.
-/
theorem framePreservingCallContract_holdsOn_returnUnchanged (retVal : Value) :
    framePreservingCallContract.holdsOn
      (fun req => ITree.ret (.returned retVal req.memory)) :=
  holdsOn_of_envSatisfiesContract _ _ fun _ _ _ h_post =>
    DWLP.ret (h_post _ ⟨rfl, rfl, rfl, rfl, [], rfl⟩)

/--
Answers to the uninterpreted external calls along one execution path: the
`n`-th external call on the path returns `(answers n).1` or unwinds, in both
cases with post-call memory `(answers n).2` under the caller's restored call
frame.
-/
abbrev MirCallAnswerStream : Type := Nat → Value × Memory

/-- Prepend `answer` to `answers`. -/
def MirCallAnswerStream.cons
    (answer : Value × Memory) (answers : MirCallAnswerStream) :
    MirCallAnswerStream
  | 0 => answer
  | n + 1 => answers n

/-- Answer stream that returns `()` with `emptyMemory` at every call. -/
def MirCallAnswerStream.unitEmpty : MirCallAnswerStream :=
  fun _ => (.unit, emptyMemory)

/--
Computable bounded modular safe-panic checker over `MirExecState`: returns
`true` when every execution path from `st` stops within `fuel` steps at
`.ret .panic` or `.ret .abort`, without faulting and without returning
normally.

Unlike `reachesPanicExecBounded`, which stops at the first uninterpreted
external call `req`, it continues past the call on all three kinds of answer:
the callee returns `(answers 0).1`, the callee unwinds, or the callee aborts.
The returned and unwound branches resume with post-call memory
`restoreCallFrame req.memory (answers 0).2`, and every branch passes the rest of
the stream to later calls.

Proving `∀ answers, reachesModularSafePanicExecBounded fuel body answers st =
true` by kernel evaluation with `answers` free shows that no path inspects a
returned value or the non-frame part of a post-call memory. Such a proof yields
the modular certificate of
`wpMirExecFrameModularSym_of_reachesModularSafePanicExecBounded`, which covers
every answer that `framePreservingCallContract` permits.

Every branch carries the full remaining `fuel`, so a body with `n` reachable
external calls evaluates up to `3 ^ n` paths.
-/
def reachesModularSafePanicExecBounded
    (fuel : Nat)
    (body : CapturedMir)
    (answers : MirCallAnswerStream)
    (st : MirExecState) :
    Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret .panic => true
    | .ret .abort => true
    | .ret (.normal _) => false
    | .tau st' => reachesModularSafePanicExecBounded fuel' body answers st'
    | .vis (.inl _) _ => false
    | .vis (.inr (.inl _)) k =>
      reachesModularSafePanicExecBounded fuel' body answers (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) k =>
      let rest : MirCallAnswerStream := fun n => answers (n + 1)
      let memAfter := restoreCallFrame req.memory (answers 0).2
      Bool.and
        (reachesModularSafePanicExecBounded fuel' body rest
          (k (.returned (answers 0).1 memAfter)))
        (Bool.and
          (reachesModularSafePanicExecBounded fuel' body rest
            (k (.panicked memAfter)))
          (reachesModularSafePanicExecBounded fuel' body rest (k .aborted)))

/--
Soundness of `reachesModularSafePanicExecBounded`: if it returns `true` on every
answer stream, then the frame-restoring modular weakest precondition under
`framePreservingCallContract` holds with the vacuous normal-return
postcondition, so no answer that the contract permits leads to a fault or to a
normal return.

At an external call, the weakest precondition quantifies over each permitted
answer `ans` and resumes with `ans.restoreFrame req.memory`. The proof
instantiates the stream so that its head is the value and memory of `ans`,
which reproduces exactly that continuation; this is why the checker must
succeed on every stream rather than on one.
-/
theorem wpMirExecFrameModularSym_of_reachesModularSafePanicExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_check :
      ∀ answers : MirCallAnswerStream,
        reachesModularSafePanicExecBounded fuel body answers st = true) :
    wpMirExecFrameModularSym framePreservingCallContract fuel body st
      (fun out => ∀ retVal mem', out = .normal (retVal, mem') → False) := by
  induction fuel generalizing st with
  | zero => nomatch h_check MirCallAnswerStream.unitEmpty
  | succ fuel ih =>
    unfold wpMirExecFrameModularSym
    rw [evalSymNodeTreeFrameModular_eq, stepMirExecSymTree_eval]
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal _ =>
        have h := h_check MirCallAnswerStream.unitEmpty
        unfold reachesModularSafePanicExecBounded at h
        simp only [h_step] at h
        nomatch h
      | panic => intro _ _ h_eq; nomatch h_eq
      | abort => intro _ _ h_eq; nomatch h_eq
    | tau st' =>
      refine ih st' (fun answers => ?_)
      have h := h_check answers
      unfold reachesModularSafePanicExecBounded at h
      simp only [h_step] at h
      exact h
    | vis i k =>
      rcases i with f | (e | c)
      · have h := h_check MirCallAnswerStream.unitEmpty
        unfold reachesModularSafePanicExecBounded at h
        simp only [h_step] at h
        nomatch h
      · cases e
        refine ih (k PUnit.unit) (fun answers => ?_)
        have h := h_check answers
        unfold reachesModularSafePanicExecBounded at h
        simp only [h_step] at h
        exact h
      · rcases c with ⟨req⟩
        refine ⟨trivial, fun ans _ => ?_⟩
        cases ans with
        | returned retVal memAfter =>
          refine ih _ (fun answers => ?_)
          have h :=
            h_check (MirCallAnswerStream.cons (retVal, memAfter) answers)
          unfold reachesModularSafePanicExecBounded at h
          simp only [h_step, Bool.and_eq_true] at h
          exact h.1
        | panicked memAfter =>
          refine ih _ (fun answers => ?_)
          have h := h_check (MirCallAnswerStream.cons (.unit, memAfter) answers)
          unfold reachesModularSafePanicExecBounded at h
          simp only [h_step, Bool.and_eq_true] at h
          exact h.2.1
        | aborted =>
          refine ih _ (fun answers => ?_)
          have h :=
            h_check (MirCallAnswerStream.cons (.unit, emptyMemory) answers)
          unfold reachesModularSafePanicExecBounded at h
          simp only [h_step, Bool.and_eq_true] at h
          exact h.2.2

/--
Computable bounded panic detector across external calls over `MirExecState`:
returns `true` when the execution path from `st` in which every uninterpreted
external call `req` answers `pick req` reaches `.ret .panic` within `fuel` steps
without faulting.

Unlike `reachesPanicExecBounded`, it does not stop at an external call. The
interaction tree constrains no answer, so the path it follows is a genuine path
of the tree for every `pick`.
-/
def reachesPanicAcrossCallsExecBounded
    (pick : MirCallReq → MirCallAns)
    (fuel : Nat)
    (body : CapturedMir)
    (st : MirExecState) :
    Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret .panic => true
    | .ret (.normal _) => false
    | .ret .abort => false
    | .tau st' => reachesPanicAcrossCallsExecBounded pick fuel' body st'
    | .vis (.inl _) _ => false
    | .vis (.inr (.inl _)) k =>
      reachesPanicAcrossCallsExecBounded pick fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) k =>
      reachesPanicAcrossCallsExecBounded pick fuel' body (k (pick req))

/--
Computable bounded panic detector across external calls starting from
`s : MachineState`.
-/
def reachesPanicAcrossCallsBounded
    (pick : MirCallReq → MirCallAns)
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Bool :=
  reachesPanicAcrossCallsExecBounded pick fuel body (.running s)

/--
Closed instance of both hypotheses of `verifyModularSafePanicMirBounded` from
`s : MachineState`, which `rfl` and `decide` can compute: the modular checker on
the answer stream `MirCallAnswerStream.unitEmpty`, and the panic detector on the
path where every external call returns `()` with unchanged memory.

Those hypotheses imply this check (`reachesModularSafePanicBounded_of_forall`),
so a `false` result shows that `verifyModularSafePanicMirBounded` cannot certify
`body` from `s` at this `fuel`. A `known_anneal_bug_ratchet` for a Miri `panic`
test requires such a result, so it fails to build once the certificate applies,
but it can still record a body that aborts or faults instead of panicking.
-/
def reachesModularSafePanicBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Bool :=
  Bool.and
    (reachesModularSafePanicExecBounded fuel body MirCallAnswerStream.unitEmpty
      (.running s))
    (reachesPanicAcrossCallsBounded (fun req => .returned .unit req.memory)
      fuel body s)

/--
The hypotheses of `verifyModularSafePanicMirBounded` imply their closed instance
`reachesModularSafePanicBounded`.
-/
theorem reachesModularSafePanicBounded_of_forall
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (h_modular :
      ∀ answers : MirCallAnswerStream,
        reachesModularSafePanicExecBounded fuel body answers (.running s) =
          true)
    (h_panic :
      ∀ retVal : Value,
        reachesPanicAcrossCallsBounded (fun req => .returned retVal req.memory)
          fuel body s = true) :
    reachesModularSafePanicBounded fuel body s = true := by
  unfold reachesModularSafePanicBounded
  rw [h_modular, h_panic]
  rfl

/--
Soundness of `reachesPanicAcrossCallsExecBounded`: if it returns `true`, then
`ITree.cofix (stepMirState body) st` reaches `.ret .panic` along a finite trace
whose external-call events carry the answers `pick` chose.
-/
theorem reachesPanicAcrossCallsExecBounded_reachesRet
    (pick : MirCallReq → MirCallAns)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_panic : reachesPanicAcrossCallsExecBounded pick fuel body st = true) :
    ∃ tr, ReachesRet (ITree.cofix (stepMirState body) st) tr .panic := by
  induction fuel generalizing st with
  | zero => nomatch h_panic
  | succ fuel' ih =>
    unfold reachesPanicAcrossCallsExecBounded at h_panic
    have h_obs :
        (ITree.cofix (stepMirState body) st).observe =
          (stepMirState body st).map (ITree.cofix (stepMirState body)) :=
      ITree.observe_cofix (stepMirState body) st
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal _ =>
        simp only [h_step] at h_panic
        nomatch h_panic
      | panic =>
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        exact ⟨[], _, Reaches.refl _, h_obs⟩
      | abort =>
        simp only [h_step] at h_panic
        nomatch h_panic
    | tau st' =>
      simp only [h_step] at h_panic
      rw [h_step] at h_obs
      dsimp only [ITreeF.map] at h_obs
      rcases ih st' h_panic with ⟨tr, u, h_reach, h_u⟩
      exact ⟨tr, u, Reaches.tau h_obs h_reach, h_u⟩
    | vis i k =>
      rcases i with f | (e | c)
      · simp only [h_step] at h_panic
        nomatch h_panic
      · simp only [h_step] at h_panic
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        rcases ih (k PUnit.unit) h_panic with ⟨tr, u, h_reach, h_u⟩
        exact ⟨⟨.inr (.inl e), PUnit.unit⟩ :: tr, u,
          Reaches.vis h_obs False.elim PUnit.unit h_reach, h_u⟩
      · rcases c with ⟨req⟩
        simp only [h_step] at h_panic
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        rcases ih (k (pick req)) h_panic with ⟨tr, u, h_reach, h_u⟩
        exact ⟨⟨.inr (.inr (.call req)), pick req⟩ :: tr, u,
          Reaches.vis h_obs False.elim (pick req) h_reach, h_u⟩

/--
Refute a total-correctness `c : TotalClaim` (`¬ c.holds`) by exhibiting a
concrete `(args, mem)` satisfying `c.pre args mem` whose bounded execution
unwinds to `.ret .panic` within `fuel` steps when each uninterpreted external
call `req` answers `pick req`. Like `refuteTotalClaimByBoundedPanic`, it assumes
nothing about external callees: `TotalClaim.holds` constrains every path of the
interaction tree, including the one that `pick` selects.
-/
theorem refuteTotalClaimByBoundedPanicAcrossCalls
    (c : TotalClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (pick : MirCallReq → MirCallAns)
    (h_panic :
      reachesPanicAcrossCallsBounded pick fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) =
          true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  rcases reachesPanicAcrossCallsExecBounded_reachesRet pick fuel c.body _ h_panic
    with ⟨tr, h_ret⟩
  rcases (h_holds args mem h_pre).2.2.2 tr .panic h_ret with ⟨_, _, h_eq, _⟩
  nomatch h_eq

/--
Certify a Miri `panic` test whose execution passes through uninterpreted
external calls, with linked `callees`, at `(args, mem)`. It proves both
1. `ModularVerificationResult` with `post := False` under
   `framePreservingCallContract.holdsOn`: for every external-call handler that
   returns or unwinds to the caller's call frame (or aborts), execution never
   faults and never returns normally; and
2. `¬ TotalClaim.holds`, refuting total correctness.

`h_modular` discharges the first conjunct
(`wpMirExecFrameModularSym_of_reachesModularSafePanicExecBounded`). `h_panic`
discharges the second: for every returned value, the path on which each
external call returns that value and leaves memory unchanged unwinds to
`.ret .panic` (`refuteTotalClaimByBoundedPanicAcrossCalls`).

A body that panics without an external call satisfies both hypotheses as well,
but `verifySafePanicMirPointBounded` certifies it with the stronger-looking
`StatefulVerificationResult`, which quantifies over every call answer.
-/
theorem verifyModularSafePanicMirBounded
    (body : CapturedMir)
    (callees : List CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_modular :
      ∀ answers : MirCallAnswerStream,
        reachesModularSafePanicExecBounded fuel body answers
          (.running (initMachineStateWithMemoryAndCallees body args mem callees)) =
            true := by
      intro _; rfl)
    (h_panic :
      ∀ retVal : Value,
        reachesPanicAcrossCallsBounded (fun req => .returned retVal req.memory)
          fuel body (initMachineStateWithMemoryAndCallees body args mem callees) =
            true := by
      intro _; rfl) :
    ModularVerificationResult
      { body := body
        envAssumed := framePreservingCallContract.holdsOn
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ _ _ => False
        callees := callees } ∧
    ¬ ({ body := body
         pre := fun a m => a = args ∧ m = mem
         post := fun _ _ _ _ => True
         callees := callees } : TotalClaim).holds := by
  refine ⟨?_, ?_⟩
  · refine verifyModularFrameContractWithCalleesMirSym
      framePreservingCallContract framePreservingCallContract_framePreserved
      body callees _ _ fuel ?_
    rintro a m ⟨rfl, rfl⟩
    exact wpMirExecFrameModularSym_of_reachesModularSafePanicExecBounded
      fuel body _ h_modular
  · exact refuteTotalClaimByBoundedPanicAcrossCalls
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ _ _ => True
        callees := callees }
      fuel args mem ⟨rfl, rfl⟩ (fun req => .returned .unit req.memory)
      (h_panic .unit)

/--
If `(evalMirDiffExecBounded fuel body st).toTag = .normalUnit`, then
`wpCoalBounded` holds under `mirDefaultWP` with postcondition `.normal (.unit, mem')`.
-/
theorem wpCoalBounded_of_evalMirDiffExecBounded_normalUnit
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_ok : (evalMirDiffExecBounded fuel body st).toTag = .normalUnit) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body)
      (fun out _ => ∃ retVal mem', out = .normal (retVal, mem') ∧ retVal = .unit)
      st PUnit.unit := by
  induction fuel generalizing st with
  | zero => nomatch h_ok
  | succ fuel' ih =>
    unfold evalMirDiffExecBounded at h_ok
    unfold wpCoalBounded
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal p =>
        rcases p with ⟨rv, m⟩
        simp only [h_step] at h_ok ⊢
        cases rv with
        | unit => exact ⟨.unit, m, rfl, rfl⟩
        | scalar _ => nomatch h_ok
        | ptr _ _ => nomatch h_ok
        | aggregate _ _ => nomatch h_ok
      | panic =>
        simp only [h_step] at h_ok
        nomatch h_ok
      | abort =>
        simp only [h_step] at h_ok
        nomatch h_ok
    | tau st' =>
      simp only [h_step] at h_ok ⊢
      exact ih st' h_ok
    | vis i k =>
      rcases i with f | (e | c)
      · rcases f with ⟨fk⟩
        cases fk <;> (simp only [h_step, MirDiffVerdict.toTag] at h_ok; nomatch h_ok)
      · simp only [h_step] at h_ok ⊢
        cases e
        exact ih (k PUnit.unit) h_ok
      · rcases c with ⟨req⟩
        simp only [h_step, MirDiffVerdict.toTag] at h_ok
        nomatch h_ok

/--
If `(evalMirDiffExecBounded fuel body st).toTag = .normalScalar bits sizeBytes`,
then `wpCoalBounded` holds under `mirDefaultWP` with postcondition
`.normal (.scalar ⟨bits, sizeBytes⟩, mem')`.
-/
theorem wpCoalBounded_of_evalMirDiffExecBounded_normalScalar
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (bits sizeBytes : Nat)
    (h_ok :
      (evalMirDiffExecBounded fuel body st).toTag =
        .normalScalar bits sizeBytes) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body)
      (fun out _ =>
        ∃ retVal mem',
          out = .normal (retVal, mem') ∧
          retVal = .scalar { bits := bits, sizeBytes := sizeBytes })
      st PUnit.unit := by
  induction fuel generalizing st with
  | zero => nomatch h_ok
  | succ fuel' ih =>
    unfold evalMirDiffExecBounded at h_ok
    unfold wpCoalBounded
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal p =>
        rcases p with ⟨rv, m⟩
        simp only [h_step] at h_ok ⊢
        cases rv with
        | unit => nomatch h_ok
        | scalar sc =>
          rcases sc with ⟨b, sz⟩
          dsimp only [MirDiffVerdict.toTag] at h_ok
          injection h_ok with h_b h_sz
          subst h_b
          subst h_sz
          exact ⟨.scalar { bits := b, sizeBytes := sz }, m, rfl, rfl⟩
        | ptr _ _ => nomatch h_ok
        | aggregate _ _ => nomatch h_ok
      | panic =>
        simp only [h_step] at h_ok
        nomatch h_ok
      | abort =>
        simp only [h_step] at h_ok
        nomatch h_ok
    | tau st' =>
      simp only [h_step] at h_ok ⊢
      exact ih st' h_ok
    | vis i k =>
      rcases i with f | (e | c)
      · rcases f with ⟨fk⟩
        cases fk <;> (simp only [h_step, MirDiffVerdict.toTag] at h_ok; nomatch h_ok)
      · simp only [h_step] at h_ok ⊢
        cases e
        exact ih (k PUnit.unit) h_ok
      · rcases c with ⟨req⟩
        simp only [h_step, MirDiffVerdict.toTag] at h_ok
        nomatch h_ok

/--
`MirDiffVerdict.toTagWithBody` produces `.normalUnit` only when `v.toTag` is
already `.normalUnit`, because scalar-represented fieldless enum refinement maps
`.normal (.aggregate _ []) _` solely to `.normalScalar` or `.normalOther`.
-/
theorem MirDiffVerdict.toTag_eq_normalUnit_of_toTagWithBody
    (body : CapturedMir) (v : MirDiffVerdict)
    (h : v.toTagWithBody body = .normalUnit) :
    v.toTag = .normalUnit := by
  cases v with
  | normal rv mem =>
    cases rv with
    | unit => rfl
    | scalar _ => nomatch h
    | ptr _ _ => nomatch h
    | aggregate varIdx fields =>
      cases fields with
      | nil =>
        dsimp only [MirDiffVerdict.toTagWithBody] at h
        cases h_tag : scalarEnumReturnTag? body varIdx with
        | none =>
          rw [h_tag] at h
          nomatch h
        | some pair =>
          rcases pair with ⟨bits, sz⟩
          rw [h_tag] at h
          nomatch h
      | cons _ _ => nomatch h
  | panic => nomatch h
  | abort => nomatch h
  | ub => nomatch h
  | unsupported => nomatch h
  | externalCall _ => nomatch h
  | outOfFuel => nomatch h

/--
Certify a Miri `pass` test returning `()` at `(args, mem)`: proves
`TotalVerificationResult` via `evalMirDiffTagBounded ... = .normalUnit`.
-/
theorem verifyTotalMirUnitPointBounded
    (body : CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_ok :
      evalMirDiffTagBounded fuel body
        (initMachineStateWithMemory body args mem) = .normalUnit := by
      rfl) :
    TotalVerificationResult
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ retVal _ => retVal = .unit } := by
  refine verifyTotalMirBounded _ fuel ?_
  rintro a m ⟨rfl, rfl⟩
  exact wpCoalBounded_of_evalMirDiffExecBounded_normalUnit
    fuel body (.running (initMachineStateWithMemory body a m))
    (MirDiffVerdict.toTag_eq_normalUnit_of_toTagWithBody body _ h_ok)

/--
Certify a Miri `pass` test returning `.scalar ⟨bits, sizeBytes⟩` at
`(args, mem)`: proves `TotalVerificationResult` via
`(evalMirDiffBounded ...).toTag = .normalScalar bits sizeBytes`.
-/
theorem verifyTotalMirScalarPointBounded
    (body : CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (bits sizeBytes : Nat)
    (h_ok :
      (evalMirDiffBounded fuel body
        (initMachineStateWithMemory body args mem)).toTag =
          .normalScalar bits sizeBytes := by
      rfl) :
    TotalVerificationResult
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ retVal _ =>
          retVal = .scalar { bits := bits, sizeBytes := sizeBytes } } := by
  refine verifyTotalMirBounded _ fuel ?_
  rintro a m ⟨rfl, rfl⟩
  exact wpCoalBounded_of_evalMirDiffExecBounded_normalScalar
    fuel body (.running (initMachineStateWithMemory body a m))
    bits sizeBytes h_ok

/--
Soundness of `validateScalarEnumCandidate`: any `.some (outBits, outSz)` result
preserves `(bits, sz)` and establishes `bits < modulus` together with
`ScalarInt.inRange`.
-/
theorem validateScalarEnumCandidate_spec
    (bits sz modulus : Nat) (validRange : WrappingRange) (outBits outSz : Nat)
    (h :
      validateScalarEnumCandidate bits sz modulus validRange =
        .some (outBits, outSz)) :
    outBits = bits ∧
    outSz = sz ∧
    bits < modulus ∧
    ScalarInt.inRange { bits := bits, sizeBytes := sz } validRange = true := by
  unfold validateScalarEnumCandidate at h
  cases h_ble : Nat.ble (.succ bits) modulus with
  | false =>
    simp only [h_ble, Bool.false_and] at h
    nomatch h
  | true =>
    cases h_in :
        ScalarInt.inRange { bits := bits, sizeBytes := sz } validRange with
    | false =>
      simp only [h_ble, h_in, Bool.and_false] at h
      nomatch h
    | true =>
      simp only [h_ble, h_in, Bool.and_true] at h
      injection h with h_pair
      injection h_pair with h_b h_sz
      exact ⟨h_b.symm, h_sz.symm, Eq.mp Nat.ble_eq h_ble, rfl⟩

/--
Soundness of `scalarEnumReturnTag?`: whenever `scalarEnumReturnTag? body
variantIdx = .some (bits, sizeBytes)`, the return local permits a scalar-backed
enum, `1 ≤ sizeBytes ≤ 16`, `bits < scalarModulus sizeBytes`, and `body`'s
resolved return layout is an inhabited `sizeBytes`-byte integer
`BackendRepr.scalar (ScalarLayout.initialized (.int (sizeBytes * 8) _)
validRange)` containing `bits`.
-/
theorem scalarEnumReturnTag?_spec
    (body : CapturedMir) (variantIdx bits sizeBytes : Nat)
    (h : scalarEnumReturnTag? body variantIdx = .some (bits, sizeBytes)) :
    returnLocalAllowsScalarEnum body = true ∧
    0 < sizeBytes ∧
    sizeBytes ≤ 16 ∧
    bits < scalarModulus sizeBytes ∧
    ∃ retLayout isSigned validRange,
      resolveReturnLayout? body = .some retLayout ∧
      retLayout.isUninhabited = false ∧
      retLayout.size.bytes = sizeBytes ∧
      retLayout.backendRepr =
        .scalar
          (.initialized (.int (Nat.mul sizeBytes 8) isSigned) validRange) ∧
      ScalarInt.inRange
        { bits := bits, sizeBytes := sizeBytes } validRange = true := by
  unfold scalarEnumReturnTag? at h
  cases h_local : returnLocalAllowsScalarEnum body with
  | false =>
    simp only [h_local] at h
    nomatch h
  | true =>
    cases h_ret : resolveReturnLayout? body with
    | none =>
      simp only [h_local, h_ret] at h
      nomatch h
    | some retLayout =>
      simp only [h_local, h_ret] at h
      cases h_uninh : retLayout.isUninhabited with
      | true =>
        simp only [h_uninh] at h
        nomatch h
      | false =>
        cases h_sz : retLayout.size.bytes with
        | zero =>
          simp only [h_uninh, h_sz] at h
          nomatch h
        | succ szPred =>
          cases h_repr : retLayout.backendRepr with
          | memory =>
            simp only [h_uninh, h_sz, h_repr] at h
            nomatch h
          | scalarPair _ _ =>
            simp only [h_uninh, h_sz, h_repr] at h
            nomatch h
          | scalar sl =>
            cases sl with
            | union _ =>
              simp only [h_uninh, h_sz, h_repr] at h
              nomatch h
            | initialized pk validRange =>
              cases pk with
              | float _ =>
                simp only [h_uninh, h_sz, h_repr] at h
                nomatch h
              | pointer _ =>
                simp only [h_uninh, h_sz, h_repr] at h
                nomatch h
              | int primBits isSigned =>
                simp only [h_uninh, h_sz, h_repr] at h
                cases h_w : Nat.ble (.succ szPred) 16 with
                | false =>
                  simp only [h_w, Bool.false_and] at h
                  nomatch h
                | true =>
                  cases h_p : Nat.beq primBits (Nat.mul (.succ szPred) 8) with
                  | false =>
                    simp only [h_w, h_p, Bool.and_false] at h
                    nomatch h
                  | true =>
                    simp only [h_w, h_p, Bool.and_true] at h
                    cases h_cand :
                        scalarEnumCandidateBits?
                          body
                          retLayout
                          (.succ szPred)
                          (scalarModulus (.succ szPred))
                          isSigned
                          validRange
                          variantIdx with
                    | none =>
                      simp only [h_cand] at h
                      nomatch h
                    | some candBits =>
                      simp only [h_cand] at h
                      rcases validateScalarEnumCandidate_spec
                        candBits (.succ szPred) (scalarModulus (.succ szPred))
                        validRange bits sizeBytes h with
                        ⟨rfl, rfl, h_lt_mod, h_in⟩
                      have h_prim : primBits = Nat.mul (.succ szPred) 8 :=
                        Nat.eq_of_beq_eq_true h_p
                      subst h_prim
                      exact
                        ⟨ rfl
                        , Nat.zero_lt_succ szPred
                        , Eq.mp Nat.ble_eq h_w
                        , h_lt_mod
                        , ⟨retLayout, isSigned, validRange,
                            rfl, h_uninh, h_sz, h_repr, h_in⟩ ⟩

/--
Inversion lemma for `MirDiffVerdict.toTagWithBody`: a `.normalScalar bits
sizeBytes` tag arises only from a `.normal` return carrying either `.scalar
⟨bits, sizeBytes⟩` or a fieldless enum `.aggregate variantIdx []` whose
`scalarEnumReturnTag?` resolves to `(bits, sizeBytes)`.
-/
theorem MirDiffVerdict.eq_normal_of_toTagWithBody_normalScalar
    (body : CapturedMir) (v : MirDiffVerdict) (bits sizeBytes : Nat)
    (h : v.toTagWithBody body = .normalScalar bits sizeBytes) :
    ∃ retVal mem,
      v = .normal retVal mem ∧
      (retVal = .scalar { bits := bits, sizeBytes := sizeBytes } ∨
        ∃ variantIdx,
          retVal = .aggregate variantIdx .nil ∧
          scalarEnumReturnTag? body variantIdx = .some (bits, sizeBytes)) := by
  cases v with
  | normal rv mem =>
    cases rv with
    | unit => nomatch h
    | scalar sc =>
      rcases sc with ⟨b, sz⟩
      dsimp only [MirDiffVerdict.toTagWithBody, MirDiffVerdict.toTag] at h
      injection h with h_b h_sz
      subst h_b
      subst h_sz
      exact ⟨.scalar { bits := b, sizeBytes := sz }, mem, rfl, Or.inl rfl⟩
    | ptr _ _ => nomatch h
    | aggregate varIdx fields =>
      cases fields with
      | nil =>
        dsimp only [MirDiffVerdict.toTagWithBody] at h
        cases h_tag : scalarEnumReturnTag? body varIdx with
        | none =>
          rw [h_tag] at h
          nomatch h
        | some pair =>
          rcases pair with ⟨b, sz⟩
          rw [h_tag] at h
          injection h with h_b h_sz
          subst h_b
          subst h_sz
          exact
            ⟨.aggregate varIdx .nil, mem, rfl, Or.inr ⟨varIdx, rfl, h_tag⟩⟩
      | cons _ _ => nomatch h
  | panic => nomatch h
  | abort => nomatch h
  | ub => nomatch h
  | unsupported => nomatch h
  | externalCall _ => nomatch h
  | outOfFuel => nomatch h

/--
If `(evalMirDiffExecBounded fuel body st).toTagWithBody body = .normalScalar
bits sizeBytes`, then `wpCoalBounded` holds under `mirDefaultWP` with a normal
return carrying either `.scalar ⟨bits, sizeBytes⟩` or a scalar-represented
fieldless enum `.aggregate variantIdx []` with `scalarEnumReturnTag? body
variantIdx = .some (bits, sizeBytes)`.
-/
theorem wpCoalBounded_of_evalMirDiffExecBounded_toTagWithBody_normalScalar
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (bits sizeBytes : Nat)
    (h_ok :
      (evalMirDiffExecBounded fuel body st).toTagWithBody body =
        .normalScalar bits sizeBytes) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body)
      (fun out _ =>
        ∃ retVal mem',
          out = .normal (retVal, mem') ∧
          (retVal = .scalar { bits := bits, sizeBytes := sizeBytes } ∨
            ∃ variantIdx,
              retVal = .aggregate variantIdx .nil ∧
              scalarEnumReturnTag? body variantIdx =
                .some (bits, sizeBytes)))
      st PUnit.unit := by
  induction fuel generalizing st with
  | zero => nomatch h_ok
  | succ fuel' ih =>
    unfold evalMirDiffExecBounded at h_ok
    unfold wpCoalBounded
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal p =>
        rcases p with ⟨rv, m⟩
        simp only [h_step] at h_ok ⊢
        rcases MirDiffVerdict.eq_normal_of_toTagWithBody_normalScalar
          body (.normal rv m) bits sizeBytes h_ok with
          ⟨rv', m', h_eq, h_post⟩
        injection h_eq with h_rv h_m
        subst h_rv
        subst h_m
        exact ⟨rv, m, rfl, h_post⟩
      | panic =>
        simp only [h_step] at h_ok
        nomatch h_ok
      | abort =>
        simp only [h_step] at h_ok
        nomatch h_ok
    | tau st' =>
      simp only [h_step] at h_ok ⊢
      exact ih st' h_ok
    | vis i k =>
      rcases i with f | (e | c)
      · rcases f with ⟨fk⟩
        cases fk <;>
          (simp only [h_step, MirDiffVerdict.toTagWithBody,
            MirDiffVerdict.toTag] at h_ok; nomatch h_ok)
      · simp only [h_step] at h_ok ⊢
        cases e
        exact ih (k PUnit.unit) h_ok
      · rcases c with ⟨req⟩
        simp only [h_step, MirDiffVerdict.toTagWithBody,
          MirDiffVerdict.toTag] at h_ok
        nomatch h_ok

/--
Certify a Miri `pass` test reporting `MIRI_PASS:scalar:<bits>:<sizeBytes>` via
`evalMirDiffTagBounded`, covering both primitive `.scalar` returns and
scalar-represented fieldless enum `.aggregate variantIdx []` returns.
-/
theorem verifyTotalMirDiffScalarPointBounded
    (body : CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (bits sizeBytes : Nat)
    (h_ok :
      evalMirDiffTagBounded fuel body
        (initMachineStateWithMemory body args mem) =
          .normalScalar bits sizeBytes := by
      rfl) :
    TotalVerificationResult
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ retVal _ =>
          retVal = .scalar { bits := bits, sizeBytes := sizeBytes } ∨
            ∃ variantIdx,
              retVal = .aggregate variantIdx .nil ∧
              scalarEnumReturnTag? body variantIdx =
                .some (bits, sizeBytes) } := by
  refine verifyTotalMirBounded _ fuel ?_
  rintro a m ⟨rfl, rfl⟩
  exact wpCoalBounded_of_evalMirDiffExecBounded_toTagWithBody_normalScalar
    fuel body (.running (initMachineStateWithMemory body a m))
    bits sizeBytes h_ok

/--
Certify a Miri `fail` (Undefined Behavior) test at `(args, mem)`: proves that
both `StatefulClaim.holds` and `TotalClaim.holds` are refuted by reaching
`FailureKind.ub` (and specifically NOT `FailureKind.unsupported`).
-/
theorem refuteMirPointByStrictUB
    (body : CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_ub :
      reachesStrictUBBounded fuel body
        (initMachineStateWithMemory body args mem) = true := by
      rfl) :
    ¬ ({ body := body
         pre := fun a m => a = args ∧ m = mem
         post := fun _ _ _ _ => True } : StatefulClaim).holds ∧
    ¬ ({ body := body
         pre := fun a m => a = args ∧ m = mem
         post := fun _ _ _ _ => True } : TotalClaim).holds :=
  ⟨refuteStatefulClaimByStrictUB _ fuel args mem ⟨rfl, rfl⟩ h_ub,
   refuteTotalClaimByStrictUB _ fuel args mem ⟨rfl, rfl⟩ h_ub⟩

/-!
## Signature & Polymorphic Obligation Adapter Lemmas and Kernel Checks
-/

/--
For a 1-argument `CapturedMir` body with `localDecls = retDecl :: d1 :: rest`,
`argsMatchSignature body [a] mem` reduces to `body.argCount = 1` and
`valueMatchesTyAndLayout defaultSignatureFuel body d1.ty d1.ty.layoutIdx a mem`.
-/
@[simp]
theorem argsMatchSignature_singleton
    (body : CapturedMir)
    (retDecl d1 : LocalDecl)
    (rest : List LocalDecl)
    (a : Value)
    (mem : Memory)
    (hDecls : body.localDecls = retDecl :: d1 :: rest)
    (hArgCount : body.argCount = 1) :
    Trusted.VerificationResult.argsMatchSignature body [a] mem ↔
      Trusted.VerificationResult.valueMatchesTyAndLayout
        Trusted.VerificationResult.defaultSignatureFuel
        body d1.ty d1.ty.layoutIdx a mem := by
  simp [Trusted.VerificationResult.argsMatchSignature, hDecls, hArgCount]

section SignatureValidationTests

open Trusted.VerificationResult

@[reducible]
private def testLayoutU32 : TypeLayout :=
  { size := ⟨4⟩
    align := ⟨4⟩
    backendRepr :=
      .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

@[reducible]
private def testLayoutBool : TypeLayout :=
  { size := ⟨1⟩
    align := ⟨1⟩
    backendRepr :=
      .scalar (.initialized (.int 8 false) ⟨0, 1⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

@[reducible]
private def testLayoutChar : TypeLayout :=
  { size := ⟨4⟩
    align := ⟨4⟩
    backendRepr :=
      .scalar (.initialized (.int 32 false) ⟨0, 1114111⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

@[reducible]
private def testLayoutRefU32 : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨8⟩
    backendRepr :=
      .scalar (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [0] }

@[reducible]
private def testLayoutSliceU32 : TypeLayout :=
  { size := ⟨16⟩
    align := ⟨8⟩
    backendRepr :=
      .scalarPair
        (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩)
        (.initialized (.int 64 false) ⟨0, 18446744073709551615⟩)
    fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [0] }

@[reducible]
private def testLayoutArrayU32x2 : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨4⟩
    backendRepr := .memory
    fields := .array ⟨4⟩ 2
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [0] }

@[reducible]
private def testLayoutTupleU32Bool : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨4⟩
    backendRepr :=
      .scalarPair
        (.initialized (.int 32 false) ⟨0, 4294967295⟩)
        (.initialized (.int 8 false) ⟨0, 1⟩)
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [0, 1] }

@[reducible]
private def testLayoutOptionU32 : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨4⟩
    backendRepr :=
      .scalarPair
        (.initialized (.int 32 false) ⟨0, 1⟩)
        (.initialized (.int 32 false) ⟨0, 4294967295⟩)
    fields := .arbitrary [⟨0⟩] [0]
    variants :=
      .multiple
        (.initialized (.int 32 false) ⟨0, 1⟩)
        0
        [.arbitrary [] [], .arbitrary [⟨4⟩] [0]]
    isUninhabited := false }

@[reducible]
private def testLayoutResultU32Bool : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨4⟩
    backendRepr :=
      .scalarPair
        (.initialized (.int 32 false) ⟨0, 1⟩)
        (.initialized (.int 32 false) ⟨0, 4294967295⟩)
    fields := .arbitrary [⟨0⟩] [0]
    variants :=
      .multiple
        (.initialized (.int 32 false) ⟨0, 1⟩)
        0
        [.arbitrary [⟨4⟩] [0], .arbitrary [⟨4⟩] [0]]
    isUninhabited := false }

@[reducible]
private def testLayoutFnPtr : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨8⟩
    backendRepr :=
      .scalar (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

@[reducible]
private def testLayoutPlaceholder : TypeLayout :=
  { size := ⟨0⟩
    align := ⟨0⟩
    backendRepr := .memory
    fields := .primitive
    variants := .empty
    isUninhabited := false }

@[reducible]
private def testLayoutTable : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ testLayoutU32
      , testLayoutBool
      , testLayoutChar
      , testLayoutRefU32
      , testLayoutSliceU32
      , testLayoutArrayU32x2
      , testLayoutTupleU32Bool
      , testLayoutOptionU32
      , testLayoutResultU32Bool
      , testLayoutFnPtr
      , testLayoutPlaceholder
      ] }

@[reducible]
private def mkTestBody (argTy retTy : Ty) (tParams : Nat := 0) : CapturedMir :=
  { defPath := "test::item"
    phase := .runtimeOptimized
    role := .subject
    argCount := 1
    localDecls :=
      [ { mutability := .mut, ty := retTy, debugName := .none }
      , { mutability := .not, ty := argTy, debugName := .none }
      ]
    basicBlocks := []
    fnAbi :=
      { args := []
        ret := { layout := testLayoutU32, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := testLayoutTable
    allocations := []
    typeParamCount := tParams }

@[reducible]
private def testLiveMem8 : Memory :=
  { emptyMemory with
    globals :=
      [ { allocId := 1
          bytes :=
            [ .some 1, .some 0, .some 0, .some 0
            , .some 2, .some 0, .some 0, .some 0 ]
          relocations := []
          align := ⟨4⟩
          mutability := .mut } ]
    borrows :=
      [ { tag := 2
          targetLocal := 0
          targetProjection := []
          perm := .active } ]
    callerLocals :=
      [ .init (.scalar ⟨77, 4⟩) ] }

/-- Valid `bool`, `char`, and `u32` scalars satisfy `argsMatchSignature`, while
invalid `bool` (`2`), surrogate `char` (`0xD800`), and oversized `u32` bit
patterns are rejected. -/
theorem sig_scalars_validated :
    argsMatchSignature
      (mkTestBody ⟨.bool, 1⟩ ⟨.bool, 1⟩) [.scalar ⟨1, 1⟩] emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.bool, 1⟩ ⟨.bool, 1⟩) [.scalar ⟨2, 1⟩] emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.char, 2⟩ ⟨.char, 2⟩) [.scalar ⟨0x41, 4⟩] emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.char, 2⟩ ⟨.char, 2⟩) [.scalar ⟨0xD800, 4⟩] emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.uint .u32, 0⟩ ⟨.uint .u32, 0⟩)
      [.scalar ⟨42, 4⟩] emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.uint .u32, 0⟩ ⟨.uint .u32, 0⟩)
      [.scalar ⟨42, 1⟩] emptyMemory := by
  dsimp [emptyMemory]; decide

/-- Thin references `&u32` and `&mut u32` require a live, aligned allocation in
`mem.globals` or `mem.borrows`; unallocated or misaligned pointers are rejected. -/
theorem sig_thin_ref_validated :
    argsMatchSignature
      (mkTestBody ⟨.ref .not (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨1, 0⟩ 8]
      testLiveMem8 ∧
    argsMatchSignature
      (mkTestBody ⟨.ref .mut (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨2, 0⟩ 8]
      testLiveMem8 ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨1, 2⟩ 8]
      testLiveMem8 ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨77, 0⟩ 8]
      testLiveMem8 := by
  dsimp [emptyMemory]; decide

/-- Wide slices `&[u32]` require a 2-field aggregate `(dataPtr, len)` backed by
a live allocation of at least `len * 4` bytes with `len * 4 <= maxIsizeBytes`. -/
theorem sig_wide_slice_validated :
    argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]]
      testLiveMem8 ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨3, 8⟩]]
      testLiveMem8 ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨0x4000000000000000, 8⟩]]
      testLiveMem8 := by
  dsimp [emptyMemory]; decide

/-- Fixed-size arrays `[u32; 2]`, tuples `(u32, bool)`, `Option<u32>`,
`Result<u32, bool>`, raw pointers `*const u32`, and `FnPtr` are structurally
constrained by `argsMatchSignature` and `retMatchesSignature`. -/
theorem sig_composites_and_adts_validated :
    argsMatchSignature
      (mkTestBody ⟨.array (.uint .u32) 2, 5⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩]]
      emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.array (.uint .u32) 2, 5⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.scalar ⟨10, 4⟩]]
      emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.tuple [.uint .u32, .bool], 6⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨1, 1⟩]]
      emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.tuple [.uint .u32, .bool], 6⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨2, 1⟩]]
      emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.adt "core::option::Option" [.uint .u32], 7⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 []]
      emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.adt "core::option::Option" [.uint .u32], 7⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 1 [.scalar ⟨99, 4⟩]]
      emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.adt "core::option::Option" [.uint .u32], 7⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 2 []]
      emptyMemory ∧
    retMatchesSignature
      (mkTestBody
        ⟨.uint .u32, 0⟩
        ⟨.adt "core::result::Result" [.uint .u32, .bool], 8⟩)
      (.aggregate 0 [.scalar ⟨7, 4⟩])
      emptyMemory ∧
    retMatchesSignature
      (mkTestBody
        ⟨.uint .u32, 0⟩
        ⟨.adt "core::result::Result" [.uint .u32, .bool], 8⟩)
      (.aggregate 1 [.scalar ⟨1, 1⟩])
      emptyMemory ∧
    ¬ retMatchesSignature
      (mkTestBody
        ⟨.uint .u32, 0⟩
        ⟨.adt "core::result::Result" [.uint .u32, .bool], 8⟩)
      (.aggregate 1 [.scalar ⟨2, 1⟩])
      emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.rawPtr .not (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨1, 0⟩ 8]
      emptyMemory ∧
    argsMatchSignature
      (mkTestBody
        ⟨.fnPtr [.uint .u32] (.uint .u32) .safe .rust, 9⟩
        ⟨.uint .u32, 0⟩)
      [.ptr ⟨99, 0⟩ 8]
      testLiveMem8 ∧
    ¬ argsMatchSignature
      (mkTestBody
        ⟨.fnPtr [.uint .u32] (.uint .u32) .safe .rust, 9⟩
        ⟨.uint .u32, 0⟩)
      [.ptr ⟨99, 4⟩ 8]
      testLiveMem8 := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    TypeLayout.isParamPlaceholder,
    wrappingRangeContains,
    primitiveKindByteWidth,
    scalarLayoutByteWidth,
    alignUp,
    maxNat
  ]

/-- Uninstantiated `RigidTy.param` is rejected (`False`), while instantiating
`polyBody` via `CapturedMir.instantiate` computes the concrete `TypeLayout` and
validates arguments and return values against the substituted type. -/
theorem sig_polymorphic_instantiate_validated :
    let polyBody := mkTestBody ⟨.param 0 "T", 10⟩ ⟨.param 0 "T", 10⟩ 1
    let subst : TypeSubst := [(.uint .u32, testLayoutU32)]
    ¬ argsMatchSignature polyBody [.scalar ⟨42, 4⟩] emptyMemory ∧
    argsMatchSignature
      (polyBody.instantiate subst)
      [.scalar ⟨42, 4⟩]
      emptyMemory ∧
    retMatchesSignature
      (polyBody.instantiate subst)
      (.scalar ⟨42, 4⟩)
      emptyMemory ∧
    ¬ argsMatchSignature
      (polyBody.instantiate subst)
      [.scalar ⟨1, 1⟩]
      emptyMemory := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    TypeLayout.isParamPlaceholder,
    wrappingRangeContains,
    primitiveKindByteWidth,
    scalarLayoutByteWidth,
    alignUp,
    maxNat,
    Trusted.Sequence.get?,
    Trusted.Sequence.length,
    UintTy.byteWidth,
    UintTy.bitWidth,
    IntTy.byteWidth,
    IntTy.bitWidth,
    FloatTy.byteWidth,
    appendTypeLayouts,
    setTypeLayoutAt,
    lookupFieldLayouts,
    computeArbitraryFieldsAux,
    computeUnionSizeAndAlign,
    computeAggregateBackendRepr,
    tagScalarByteWidth,
    recomputeVariantShapesAux,
    TypeLayout.recomputeFromFieldLayouts,
    Trusted.Rustc.V2026_06_01.Layout.substitutePlaceholderEntries,
    Trusted.Rustc.V2026_06_01.Layout.recomputeEntriesWith,
    LayoutTable.appendParamLayouts,
    LayoutTable.lookup,
    TypeSubst.lookup,
    TypeSubst.layouts,
    TypeSubst.length,
    RigidTy.instantiate,
    RigidTy.instantiateList,
    RigidTy.hasSubstParam,
    RigidTy.hasSubstParamList,
    RigidTy.isCompoundSubstParam,
    RigidTy.isTrivialZst,
    RigidTy.computeLayout,
    RigidTy.computeLayoutList,
    Trusted.Rustc.V2026_06_01.Layout.LayoutTable.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.LayoutTable.instantiate,
    Ty.instantiate,
    ConstOperand.instantiate,
    TraitRef.instantiate,
    TraitImplEntry.instantiate,
    TraitImplEntry.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.Place.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.AggregateKind.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Rvalue.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.NonDivergingIntrinsic.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.StatementKind.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Terminator.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.LocalDecl.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.LocalDecl.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.appendTys,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.Place.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.AggregateKind.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Rvalue.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.NonDivergingIntrinsic.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.StatementKind.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Terminator.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.LocalDecl.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.collectBodyTys,
    Trusted.Rustc.V2026_06_01.MirAst.hasNonParamTyAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.hasCompoundParamTyAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.substituteTyParamLayoutsAux,
    Trusted.Rustc.V2026_06_01.MirAst.recomputeTyCompoundLayoutsAux,
    Trusted.Rustc.V2026_06_01.MirAst.hasNonParamDeclAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.hasCompoundParamDeclAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.substituteDeclParamLayoutsAux,
    Trusted.Rustc.V2026_06_01.MirAst.recomputeDeclCompoundLayoutsAux,
    LayoutTable.instantiateForBody,
    LayoutTable.instantiateForDecls,
    Trusted.Rustc.V2026_06_01.MirAst.ArgAbi.recomputeMode,
    Trusted.Rustc.V2026_06_01.MirAst.ArgAbi.instantiateForDecl,
    Trusted.Rustc.V2026_06_01.MirAst.ArgAbi.instantiateListForDecls,
    Trusted.Rustc.V2026_06_01.MirAst.FnAbi.instantiate,
    dropGenericParams,
    CapturedMir.instantiate
  ]

/-- Sub-borrows into composite caller locals (`targetProjection != []` or
nonzero `offsetBytes`) and offset slice borrows (`&arr[1..3]`) check both the
lower (`entry.rangeOffset ≤ p.offsetBytes`) and upper
(`p.offsetBytes + size ≤ entry.rangeOffset + entry.rangeLen`) sub-range bounds
as well as array element byte capacity. -/
theorem sig_subborrow_and_slice_offset_validated :
    let subBorrowMem : Memory :=
      { emptyMemory with
        borrows :=
          [ { tag := 3
              targetLocal := 0
              targetProjection := [.index 1]
              perm := .active
              rangeOffset := 4
              rangeLen := 4 }
          , { tag := 4
              targetLocal := 0
              targetProjection := []
              perm := .frozen
              rangeOffset := 0
              rangeLen := 8 } ]
        callerLocals :=
          [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩]) ] }
    argsMatchSignature
      (mkTestBody ⟨.ref .mut (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨3, 4⟩ 8]
      subBorrowMem ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .mut (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨3, 0⟩ 8]
      subBorrowMem ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .mut (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨3, 8⟩ 8]
      subBorrowMem ∧
    argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨4, 4⟩ 8, .scalar ⟨1, 8⟩]]
      subBorrowMem ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨3, 0⟩ 8, .scalar ⟨2, 8⟩]]
      subBorrowMem ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨4, 4⟩ 8, .scalar ⟨2, 8⟩]]
      subBorrowMem := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    TypeLayout.isParamPlaceholder,
    wrappingRangeContains,
    primitiveKindByteWidth,
    scalarLayoutByteWidth,
    alignUp,
    maxNat
  ]

end SignatureValidationTests


set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-!
## Section 1 — Append-Only `SymTable` GVN & Monotone Evaluation
-/

/-- Symbolic value identifier indexing into an append-only `SymTable`. -/
abbrev SymId := Nat

/-- Concrete environment mapping symbolic input variable indices to 64-bit scalar words. -/
abbrev SymEnv := Nat → Nat

/-- 64-bit word modulus $2^{64}$ used for bounded modular arithmetic operations. -/
def word64Modulus : Nat := 18446744073709551616

/-- Unary symbolic operations in `SymNode`. -/
inductive SymOp1 where
  | id
  | boolNot
  | wrappingNeg64
  | maskLow32
  | xorConst (mask : Nat)
  | addConst (delta : Nat)
  deriving DecidableEq

/-- Binary symbolic operations in `SymNode`. -/
inductive SymOp2 where
  | add
  | sub
  | mul
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | eq
  | lt
  | le
  deriving DecidableEq

/-- Hash-consed symbolic DAG node. Child operands reference earlier `SymId` (`Nat`)
    entries in the append-only `SymTable`. -/
inductive SymNode where
  | const (val : Nat)
  | var (inputIdx : Nat)
  | op1 (op : SymOp1) (arg : Nat)
  | op2 (op : SymOp2) (lhs rhs : Nat)
  | ite (cond thenBr elseBr : Nat)
  deriving DecidableEq

/-- Reduce a natural number to a 64-bit machine word (`v mod 2^64`). Every value produced by
    `SymNode` / `ExprTree` / MIR evaluation is passed through `wrap64` (or is a `0`/`1` flag),
    so all symbolic and concrete values are genuine `u64` words (`evalSymId_lt_word64`). -/
def wrap64 (v : Nat) : Nat := v % word64Modulus

theorem wrap64_lt (v : Nat) : wrap64 v < word64Modulus :=
  Nat.mod_lt v (by decide)

/-- Concrete evaluation of unary operations (`u64` wrapping semantics). -/
def evalSymOp1 (op : SymOp1) (v : Nat) : Nat :=
  match op with
  | .id => v
  | .boolNot => if v == 0 then 1 else 0
  | .wrappingNeg64 => (word64Modulus - (v % word64Modulus)) % word64Modulus
  | .maskLow32 => v % 4294967296
  | .xorConst mask => wrap64 (Nat.xor v mask)
  | .addConst delta => wrap64 (v + delta)

/-- Concrete evaluation of binary operations with Rust `u64` `wrapping_*` semantics
    (`add`/`sub`/`mul`/`shl` wrap modulo `2^64`; `sub` is `wrapping_sub`, **not** truncated
    `Nat` subtraction; shift amounts are masked to `b % 64` like Rust's `wrapping_shl`). -/
def evalSymOp2 (op : SymOp2) (a b : Nat) : Nat :=
  match op with
  | .add => wrap64 (a + b)
  | .sub => wrap64 (a + (word64Modulus - b % word64Modulus))
  | .mul => wrap64 (a * b)
  | .bitAnd => wrap64 (Nat.land a b)
  | .bitOr => wrap64 (Nat.lor a b)
  | .bitXor => wrap64 (Nat.xor a b)
  | .shl => wrap64 (Nat.shiftLeft a (b % 64))
  | .shr => wrap64 (Nat.shiftRight a (b % 64))
  | .eq => if a == b then 1 else 0
  | .lt => if decide (a < b) then 1 else 0
  | .le => if decide (a ≤ b) then 1 else 0

/-- Non-vacuity witnesses for `u64` wrapping semantics (`u64::MAX + 1 = 0`,
    `3.wrapping_sub(5) = 2^64 - 2`, `(2^63) << 1 = 0`). -/
theorem evalSymOp2_wrapping_witness :
    evalSymOp2 .add 18446744073709551615 1 = 0 ∧
      evalSymOp2 .sub 3 5 = 18446744073709551614 ∧
      evalSymOp2 .shl 9223372036854775808 1 = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- Boolean check that all child `SymId`s in a `SymNode` are strictly below `bound`. -/
def validNodeB (bound : Nat) : SymNode → Bool
  | .const _ => true
  | .var _ => true
  | .op1 _ a => decide (a < bound)
  | .op2 _ a b => decide (a < bound) && decide (b < bound)
  | .ite c t e => decide (c < bound) && decide (t < bound) && decide (e < bound)

/-- Propositional well-formedness of a `SymNode` at table bound `bound`: every
    child `SymId` is strictly less than `bound`, enforcing a strict topological DAG. -/
def ValidNode (bound : Nat) (node : SymNode) : Prop :=
  match node with
  | .const _ => True
  | .var _ => True
  | .op1 _ a => a < bound
  | .op2 _ a b => a < bound ∧ b < bound
  | .ite c t e => c < bound ∧ t < bound ∧ e < bound

theorem validNode_iff_validNodeB (bound : Nat) (node : SymNode) :
    ValidNode bound node ↔ validNodeB bound node = true := by
  cases node with
  | const _ => simp [ValidNode, validNodeB]
  | var _ => simp [ValidNode, validNodeB]
  | op1 _ a => simp [ValidNode, validNodeB]
  | op2 _ a b => simp [ValidNode, validNodeB, Bool.and_eq_true]
  | ite c t e => simp [ValidNode, validNodeB, Bool.and_eq_true, and_assoc]

theorem ValidNode.mono {b₁ b₂ : Nat} {node : SymNode} (h : ValidNode b₁ node) (hle : b₁ ≤ b₂) :
    ValidNode b₂ node := by
  cases node with
  | const _ => trivial
  | var _ => trivial
  | op1 _ a =>
    exact Nat.lt_of_lt_of_le h hle
  | op2 _ a b =>
    exact ⟨Nat.lt_of_lt_of_le h.1 hle, Nat.lt_of_lt_of_le h.2 hle⟩
  | ite c t e =>
    exact ⟨Nat.lt_of_lt_of_le h.1 hle, Nat.lt_of_lt_of_le h.2.1 hle, Nat.lt_of_lt_of_le h.2.2 hle⟩

/-- Append-only Global Value Numbering (`SymTable`) table storing `SymNode`s in
    topological creation order. -/
structure SymTable where
  nodes : List SymNode := []
  deriving DecidableEq

/-- A `SymTable` is valid when every node at index `idx` only references strictly
    earlier `SymId`s `< idx`. -/
def ValidTable (tbl : SymTable) : Prop :=
  ∀ (idx : Nat) (node : SymNode), tbl.nodes[idx]? = some node → ValidNode idx node

theorem ValidTable.empty : ValidTable { nodes := [] } := by
  intro idx node h
  simp at h

/-- Structural monotonicity (`Extends`): `tbl₂` extends `tbl₁` when every index
    valid in `tbl₁` maps to the exact same `SymNode` in `tbl₂`. -/
def SymTable.Extends (tbl₁ tbl₂ : SymTable) : Prop :=
  ∀ (idx : Nat) (node : SymNode), tbl₁.nodes[idx]? = some node → tbl₂.nodes[idx]? = some node

theorem SymTable.Extends.refl (tbl : SymTable) : tbl.Extends tbl := by
  intro idx node h
  exact h

theorem SymTable.Extends.trans {tbl₁ tbl₂ tbl₃ : SymTable}
    (h₁₂ : tbl₁.Extends tbl₂) (h₂₃ : tbl₂.Extends tbl₃) :
    tbl₁.Extends tbl₃ := by
  intro idx node h
  exact h₂₃ idx node (h₁₂ idx node h)

theorem getElem?_append_left_of_some {α : Type} {xs ys : List α} {idx : Nat} {v : α}
    (h : xs[idx]? = some v) :
    (xs ++ ys)[idx]? = some v := by
  have hlt : idx < xs.length := by
    cases hlt' : decide (idx < xs.length) with
    | true => exact of_decide_eq_true hlt'
    | false =>
      have hge : xs.length ≤ idx := Nat.le_of_not_lt (of_decide_eq_false hlt')
      rw [List.getElem?_eq_none hge] at h
      cases h
  rw [List.getElem?_append_left hlt]
  exact h

theorem SymTable.extends_append (tbl : SymTable) (extra : List SymNode) :
    tbl.Extends { nodes := tbl.nodes ++ extra } := by
  intro idx node h
  exact getElem?_append_left_of_some h

theorem SymTable.Extends.length_le {tbl₁ tbl₂ : SymTable}
    (hExt : tbl₁.Extends tbl₂) : tbl₁.nodes.length ≤ tbl₂.nodes.length := by
  cases h : tbl₁.nodes.length with
  | zero => exact Nat.zero_le _
  | succ k =>
    have hlt : k < tbl₁.nodes.length := by omega
    have hSome : tbl₁.nodes[k]? = some tbl₁.nodes[k] := List.getElem?_eq_getElem hlt
    have hSome₂ := hExt k tbl₁.nodes[k] hSome
    cases hlt₂ : decide (k < tbl₂.nodes.length) with
    | true =>
      have hk : k < tbl₂.nodes.length := of_decide_eq_true hlt₂
      omega
    | false =>
      have hge : tbl₂.nodes.length ≤ k := Nat.le_of_not_lt (of_decide_eq_false hlt₂)
      rw [List.getElem?_eq_none hge] at hSome₂
      cases hSome₂

/-- Evaluate a single `SymNode` given an evaluator `evalChild` for child `SymId`s. -/
def evalSymNodeWith (evalChild : SymId → Nat) (env : SymEnv) : SymNode → Nat
  | .const v => wrap64 v
  | .var idx => wrap64 (env idx)
  | .op1 op a => evalSymOp1 op (evalChild a)
  | .op2 op a b => evalSymOp2 op (evalChild a) (evalChild b)
  | .ite c t e => if evalChild c != 0 then evalChild t else evalChild e

/-- Fuel-bounded structural evaluation of a `SymId` in `tbl`.
    `evalSymId tbl env id` sets `fuel = id + 1`, which depends ONLY on `id`
    and NOT on `tbl.nodes.length`. Because every valid node at `idx` only references
    children `< idx`, `id + 1` steps of fuel always suffice and `evalSymId_mono` holds
    directly across table extensions without fuel-shifting boilerplate. -/
def evalSymIdAux (tbl : SymTable) (env : SymEnv) : Nat → SymId → Nat
  | 0, _ => 0
  | fuel + 1, id =>
    match tbl.nodes[id]? with
    | none => 0
    | some node => evalSymNodeWith (evalSymIdAux tbl env fuel) env node

/-- Evaluate `id : SymId` in `tbl` under concrete input environment `env`. -/
def evalSymId (tbl : SymTable) (env : SymEnv) (id : SymId) : Nat :=
  evalSymIdAux tbl env (id + 1) id

/-- Monotonicity of `evalSymIdAux` across `SymTable.Extends`. -/
theorem evalSymIdAux_mono {tbl₁ tbl₂ : SymTable} (hValid : ValidTable tbl₁)
    (hExt : tbl₁.Extends tbl₂) (env : SymEnv) :
    ∀ (fuel : Nat) (id : SymId),
      id < tbl₁.nodes.length →
      evalSymIdAux tbl₁ env fuel id = evalSymIdAux tbl₂ env fuel id
  | 0, _, _ => rfl
  | fuel + 1, id, hlt => by
    have hSome₁ : tbl₁.nodes[id]? = some tbl₁.nodes[id] := List.getElem?_eq_getElem hlt
    have hSome₂ : tbl₂.nodes[id]? = some tbl₁.nodes[id] := hExt id tbl₁.nodes[id] hSome₁
    have hNodeValid : ValidNode id tbl₁.nodes[id] := hValid id tbl₁.nodes[id] hSome₁
    dsimp [evalSymIdAux]
    rw [hSome₁, hSome₂]
    dsimp
    cases hNode : tbl₁.nodes[id] with
    | const v => rfl
    | var idx => rfl
    | op1 op a =>
      rw [hNode] at hNodeValid
      dsimp [ValidNode] at hNodeValid
      dsimp [evalSymNodeWith]
      rw [evalSymIdAux_mono hValid hExt env fuel a (Nat.lt_trans hNodeValid hlt)]
    | op2 op a b =>
      rw [hNode] at hNodeValid
      dsimp [ValidNode] at hNodeValid
      dsimp [evalSymNodeWith]
      rw [evalSymIdAux_mono hValid hExt env fuel a (Nat.lt_trans hNodeValid.1 hlt)]
      rw [evalSymIdAux_mono hValid hExt env fuel b (Nat.lt_trans hNodeValid.2 hlt)]
    | ite c t e =>
      rw [hNode] at hNodeValid
      dsimp [ValidNode] at hNodeValid
      dsimp [evalSymNodeWith]
      rw [evalSymIdAux_mono hValid hExt env fuel c (Nat.lt_trans hNodeValid.1 hlt)]
      rw [evalSymIdAux_mono hValid hExt env fuel t (Nat.lt_trans hNodeValid.2.1 hlt)]
      rw [evalSymIdAux_mono hValid hExt env fuel e (Nat.lt_trans hNodeValid.2.2 hlt)]

/-- **Core Monotonicity Theorem (`evalSymId_mono`)**:
    Extending an append-only `SymTable` preserves the concrete evaluation of every
    previously allocated `SymId`. -/
theorem evalSymId_mono {tbl₁ tbl₂ : SymTable} (hValid : ValidTable tbl₁)
    (hExt : tbl₁.Extends tbl₂) (env : SymEnv) {id : SymId}
    (hlt : id < tbl₁.nodes.length) :
    evalSymId tbl₁ env id = evalSymId tbl₂ env id :=
  evalSymIdAux_mono hValid hExt env (id + 1) id hlt

/-- Fuel-sufficiency theorem: in a `ValidTable`, any fuel `> id` evaluates `id`
    to the exact same value. -/
theorem evalSymIdAux_fuel_irrel {tbl : SymTable} (hValid : ValidTable tbl) (env : SymEnv) :
    ∀ (bound id fuel₁ fuel₂ : Nat),
      id < bound →
      id < tbl.nodes.length →
      id < fuel₁ →
      id < fuel₂ →
      evalSymIdAux tbl env fuel₁ id = evalSymIdAux tbl env fuel₂ id
  | 0, _, _, _, hltB, _, _, _ => by omega
  | bound + 1, id, fuel₁, fuel₂, hltB, hltLen, hltF₁, hltF₂ => by
    cases fuel₁ with
    | zero => omega
    | succ f₁ =>
      cases fuel₂ with
      | zero => omega
      | succ f₂ =>
        have hSome : tbl.nodes[id]? = some tbl.nodes[id] := List.getElem?_eq_getElem hltLen
        have hNodeValid : ValidNode id tbl.nodes[id] := hValid id tbl.nodes[id] hSome
        dsimp [evalSymIdAux]
        rw [hSome]
        dsimp
        cases hNode : tbl.nodes[id] with
        | const v => rfl
        | var idx => rfl
        | op1 op a =>
          rw [hNode] at hNodeValid
          have ha : a < id := hNodeValid
          dsimp [evalSymNodeWith]
          rw [evalSymIdAux_fuel_irrel hValid env bound a f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]
        | op2 op a b =>
          rw [hNode] at hNodeValid
          have ha : a < id := hNodeValid.1
          have hb : b < id := hNodeValid.2
          dsimp [evalSymNodeWith]
          rw [evalSymIdAux_fuel_irrel hValid env bound a f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]
          rw [evalSymIdAux_fuel_irrel hValid env bound b f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]
        | ite c t e =>
          rw [hNode] at hNodeValid
          have hc : c < id := hNodeValid.1
          have ht : t < id := hNodeValid.2.1
          have he : e < id := hNodeValid.2.2
          dsimp [evalSymNodeWith]
          rw [evalSymIdAux_fuel_irrel hValid env bound c f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]
          rw [evalSymIdAux_fuel_irrel hValid env bound t f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]
          rw [evalSymIdAux_fuel_irrel hValid env bound e f₁ f₂
            (by omega) (by omega) (by omega) (by omega)]

theorem evalSymIdAux_eq_evalSymId {tbl : SymTable} (hValid : ValidTable tbl)
    (env : SymEnv) {id fuel : Nat} (hltLen : id < tbl.nodes.length) (hltFuel : id < fuel) :
    evalSymIdAux tbl env fuel id = evalSymId tbl env id :=
  evalSymIdAux_fuel_irrel hValid env (id + 1) id fuel (id + 1)
    (Nat.lt_succ_self id) hltLen hltFuel (Nat.lt_succ_self id)

/-- Unfolding equation for `evalSymId` at any valid index `id` in `tbl`. -/
theorem evalSymId_eq_evalSymNodeWith {tbl : SymTable} (hValid : ValidTable tbl)
    (env : SymEnv) {id : Nat} {node : SymNode}
    (hLookup : tbl.nodes[id]? = some node) :
    evalSymId tbl env id = evalSymNodeWith (evalSymId tbl env) env node := by
  have hltLen : id < tbl.nodes.length := by
    cases h : decide (id < tbl.nodes.length) with
    | true => exact of_decide_eq_true h
    | false =>
      rw [List.getElem?_eq_none (Nat.le_of_not_lt (of_decide_eq_false h))] at hLookup
      cases hLookup
  have hNodeValid : ValidNode id node := hValid id node hLookup
  change evalSymIdAux tbl env (id + 1) id = evalSymNodeWith (evalSymId tbl env) env node
  dsimp [evalSymIdAux]
  rw [hLookup]
  dsimp
  cases node with
  | const v => rfl
  | var idx => rfl
  | op1 op a =>
    dsimp [ValidNode] at hNodeValid
    dsimp [evalSymNodeWith]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid hltLen) hNodeValid]
  | op2 op a b =>
    dsimp [ValidNode] at hNodeValid
    dsimp [evalSymNodeWith]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid.1 hltLen) hNodeValid.1]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid.2 hltLen) hNodeValid.2]
  | ite c t e =>
    dsimp [ValidNode] at hNodeValid
    dsimp [evalSymNodeWith]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid.1 hltLen) hNodeValid.1]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid.2.1 hltLen) hNodeValid.2.1]
    rw [evalSymIdAux_eq_evalSymId hValid env (Nat.lt_trans hNodeValid.2.2 hltLen) hNodeValid.2.2]

theorem evalSymOp1_lt_word64 (op : SymOp1) {v : Nat} (hv : v < word64Modulus) :
    evalSymOp1 op v < word64Modulus := by
  cases op with
  | id => exact hv
  | boolNot =>
    dsimp only [evalSymOp1]
    split <;> decide
  | wrappingNeg64 => exact Nat.mod_lt _ (by decide)
  | maskLow32 =>
    dsimp only [evalSymOp1]
    have h := Nat.mod_lt v (show 4294967296 > 0 by decide)
    have h2 : (4294967296 : Nat) < word64Modulus := by decide
    omega
  | xorConst _ => exact wrap64_lt _
  | addConst _ => exact wrap64_lt _

theorem evalSymOp2_lt_word64 (op : SymOp2) (a b : Nat) : evalSymOp2 op a b < word64Modulus := by
  cases op <;> first
    | exact wrap64_lt _
    | (dsimp only [evalSymOp2]; split <;> decide)

/-- **`u64` Word Invariant (`evalSymId_lt_word64`)**: every `SymId` evaluates to a genuine
    64-bit word (`< 2^64`) in every table, environment and fuel. -/
theorem evalSymIdAux_lt_word64 (tbl : SymTable) (env : SymEnv) :
    ∀ (fuel : Nat) (id : SymId), evalSymIdAux tbl env fuel id < word64Modulus
  | 0, _ => by
    dsimp only [evalSymIdAux]
    decide
  | fuel + 1, id => by
    dsimp only [evalSymIdAux]
    split
    · decide
    · rename_i node _
      cases node with
      | const v => exact wrap64_lt v
      | var i => exact wrap64_lt (env i)
      | op1 op a => exact evalSymOp1_lt_word64 op (evalSymIdAux_lt_word64 tbl env fuel a)
      | op2 op a b => exact evalSymOp2_lt_word64 op _ _
      | ite c t e =>
        dsimp only [evalSymNodeWith]
        split
        · exact evalSymIdAux_lt_word64 tbl env fuel t
        · exact evalSymIdAux_lt_word64 tbl env fuel e

theorem evalSymId_lt_word64 (tbl : SymTable) (env : SymEnv) (id : SymId) :
    evalSymId tbl env id < word64Modulus :=
  evalSymIdAux_lt_word64 tbl env (id + 1) id

/-- Search `nodes` for an existing occurrence of `target`, returning its index if present. -/
def findNodeIdxAux (target : SymNode) (offset : Nat) : List SymNode → Option Nat
  | [] => none
  | n :: rest =>
    if n == target then
      some offset
    else
      findNodeIdxAux target (offset + 1) rest

def findNodeIdx (nodes : List SymNode) (target : SymNode) : Option Nat :=
  findNodeIdxAux target 0 nodes

theorem findNodeIdxAux_spec (target : SymNode) :
    ∀ (nodes : List SymNode) (offset idx : Nat),
      findNodeIdxAux target offset nodes = some idx →
      offset ≤ idx ∧ idx < offset + nodes.length ∧ nodes[idx - offset]? = some target
  | [], _, _, h => by cases h
  | n :: rest, offset, idx, h => by
    dsimp [findNodeIdxAux] at h
    split at h
    · rename_i hEq
      injection h with hIdx
      subst hIdx
      have hTarget : n = target := of_decide_eq_true hEq
      subst hTarget
      refine ⟨Nat.le_refl offset, by dsimp; omega, ?_⟩
      rw [Nat.sub_self]
      rfl
    · have ih := findNodeIdxAux_spec target rest (offset + 1) idx h
      refine ⟨by omega, by dsimp; omega, ?_⟩
      have hSub : idx - offset = (idx - (offset + 1)) + 1 := by omega
      rw [hSub]
      exact ih.2.2

theorem findNodeIdx_spec {nodes : List SymNode} {target : SymNode} {idx : Nat}
    (h : findNodeIdx nodes target = some idx) :
    idx < nodes.length ∧ nodes[idx]? = some target := by
  have hSpec := findNodeIdxAux_spec target nodes 0 idx h
  refine ⟨by omega, ?_⟩
  have hSub : idx - 0 = idx := Nat.sub_zero idx
  rw [← hSub]
  exact hSpec.2.2

theorem findNodeIdxAux_complete (target : SymNode) :
    ∀ (nodes : List SymNode) (offset i : Nat),
      nodes[i]? = some target →
      ∃ idx, findNodeIdxAux target offset nodes = some idx
  | [], _, _, h => by simp at h
  | n :: rest, offset, i, h => by
    dsimp [findNodeIdxAux]
    split
    · exact ⟨offset, rfl⟩
    · rename_i hNe
      cases i with
      | zero =>
        simp at h
        subst h
        exact False.elim (hNe (decide_eq_true rfl))
      | succ i' =>
        simp at h
        exact findNodeIdxAux_complete target rest (offset + 1) i' h

theorem findNodeIdx_complete {nodes : List SymNode} {target : SymNode} {i : Nat}
    (h : nodes[i]? = some target) :
    ∃ idx, findNodeIdx nodes target = some idx :=
  findNodeIdxAux_complete target nodes 0 i h

/-- Raw hash-consed interning without algebraic peephole rules: returns an existing
    `SymId` if `node` is already in `tbl.nodes`, or appends `node` at `tbl.nodes.length`. -/
def internRawNode (tbl : SymTable) (node : SymNode) : SymId × SymTable :=
  match findNodeIdx tbl.nodes node with
  | some idx => (idx, tbl)
  | none => (tbl.nodes.length, { nodes := tbl.nodes ++ [node] })

/-- Commutative binary operators: their operands are put in canonical `SymId` order before
    hash-consing, so `x + y` and `y + x` share one `SymId`. -/
def SymOp2.isComm : SymOp2 → Bool
  | .add | .mul | .bitAnd | .bitOr | .bitXor | .eq => true
  | _ => false

theorem evalSymOp2_comm {op : SymOp2} (hComm : op.isComm = true) (x y : Nat) :
    evalSymOp2 op x y = evalSymOp2 op y x := by
  cases op with
  | add => show wrap64 (x + y) = wrap64 (y + x); rw [Nat.add_comm]
  | mul => show wrap64 (x * y) = wrap64 (y * x); rw [Nat.mul_comm]
  | bitAnd =>
    show wrap64 (Nat.land x y) = wrap64 (Nat.land y x)
    rw [show Nat.land x y = Nat.land y x from Nat.and_comm x y]
  | bitOr =>
    show wrap64 (Nat.lor x y) = wrap64 (Nat.lor y x)
    rw [show Nat.lor x y = Nat.lor y x from Nat.or_comm x y]
  | bitXor =>
    show wrap64 (Nat.xor x y) = wrap64 (Nat.xor y x)
    rw [show Nat.xor x y = Nat.xor y x from Nat.xor_comm x y]
  | eq =>
    show (if decide (x = y) = true then 1 else 0) = (if decide (y = x) = true then 1 else 0)
    by_cases h : x = y
    · subst h
      rfl
    · rw [decide_eq_false h, decide_eq_false (Ne.symm h)]
  | sub => cases hComm
  | shl => cases hComm
  | shr => cases hComm
  | lt => cases hComm
  | le => cases hComm

/-- Table-independent algebraic peephole rewrite of a binary node (`peepholeOp2`):
    duplicate-operand folds `x & x ↦ x`, `x | x ↦ x`, `x ^ x ↦ 0`, `x - x ↦ 0`, `x < x ↦ 0`,
    `x == x ↦ 1`, `x ≤ x ↦ 1`, and canonical operand order for commutative operators.
    `.inl x` reuses an existing `SymId`; `.inr node'` hash-conses `node'`. -/
def peepholeOp2 (op : SymOp2) (a b : SymId) : SymId ⊕ SymNode :=
  if a = b then
    match op with
    | .bitAnd | .bitOr => .inl a
    | .bitXor | .sub | .lt => .inr (.const 0)
    | .eq | .le => .inr (.const 1)
    | _ => .inr (.op2 op a b)
  else if op.isComm && decide (b < a) then .inr (.op2 op b a)
  else .inr (.op2 op a b)

/-- **Peephole Soundness (`peepholeOp2_sound`)**: every rewrite preserves the `u64` value of the
    binary node for any child valuation `f` whose operand `a` is a 64-bit word. -/
theorem peepholeOp2_sound (op : SymOp2) (a b : SymId) (f : SymId → Nat) (env : SymEnv)
    (ha : f a < word64Modulus) :
    match peepholeOp2 op a b with
    | .inl x => f x = evalSymOp2 op (f a) (f b)
    | .inr node' => evalSymNodeWith f env node' = evalSymOp2 op (f a) (f b) := by
  unfold peepholeOp2
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left (rfl : a = a)]
    have hmod : f a % word64Modulus = f a := Nat.mod_eq_of_lt ha
    cases op with
    | add => rfl
    | mul => rfl
    | shl => rfl
    | shr => rfl
    | bitAnd =>
      show f a = wrap64 (Nat.land (f a) (f a))
      rw [show Nat.land (f a) (f a) = f a from Nat.and_self (f a)]
      exact hmod.symm
    | bitOr =>
      show f a = wrap64 (Nat.lor (f a) (f a))
      rw [show Nat.lor (f a) (f a) = f a from Nat.or_self (f a)]
      exact hmod.symm
    | bitXor =>
      show wrap64 0 = wrap64 (Nat.xor (f a) (f a))
      rw [show Nat.xor (f a) (f a) = 0 from Nat.xor_self (f a)]
    | sub =>
      show wrap64 0 = wrap64 (f a + (word64Modulus - f a % word64Modulus))
      rw [hmod, Nat.add_sub_cancel' (Nat.le_of_lt ha)]
      show 0 % word64Modulus = word64Modulus % word64Modulus
      rw [Nat.mod_self]
      rfl
    | lt =>
      show wrap64 0 = (if decide (f a < f a) = true then 1 else 0)
      rw [decide_eq_false (Nat.lt_irrefl (f a))]
      rfl
    | eq =>
      show wrap64 1 = (if decide (f a = f a) = true then 1 else 0)
      rw [decide_eq_true rfl]
      rfl
    | le =>
      show wrap64 1 = (if decide (f a ≤ f a) = true then 1 else 0)
      rw [decide_eq_true (Nat.le_refl (f a))]
      rfl
  · rw [ite_eq_right hab]
    by_cases hc : (op.isComm && decide (b < a)) = true
    · rw [ite_eq_left hc]
      have hComm : op.isComm = true := by
        cases h : op.isComm
        · rw [h] at hc
          cases hc
        · rfl
      exact evalSymOp2_comm hComm (f b) (f a)
    · rw [ite_eq_right hc]
      rfl

theorem peepholeOp2_valid {bound : Nat} {op : SymOp2} {a b : SymId}
    (h : ValidNode bound (.op2 op a b)) :
    match peepholeOp2 op a b with
    | .inl x => x < bound
    | .inr node' => ValidNode bound node' := by
  have ha : a < bound := h.1
  have hb : b < bound := h.2
  unfold peepholeOp2
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left (rfl : a = a)]
    cases op <;> first | exact ha | exact (⟨ha, ha⟩ : a < bound ∧ a < bound) | trivial
  · rw [ite_eq_right hab]
    by_cases hc : (op.isComm && decide (b < a)) = true
    · rw [ite_eq_left hc]
      exact (⟨hb, ha⟩ : b < bound ∧ a < bound)
    · rw [ite_eq_right hc]
      exact (⟨ha, hb⟩ : a < bound ∧ b < bound)

/-- Lookup-first binary interning: reuse an existing occurrence of the node verbatim, otherwise
    apply `peepholeOp2` and hash-cons the result. -/
def internOp2 (tbl : SymTable) (op : SymOp2) (a b : SymId) : SymId × SymTable :=
  match findNodeIdx tbl.nodes (.op2 op a b) with
  | some idx => (idx, tbl)
  | none =>
    match peepholeOp2 op a b with
    | .inl x => (x, tbl)
    | .inr node' => internRawNode tbl node'

theorem findNodeIdxAux_append_none (target x : SymNode) (hx : x ≠ target) :
    ∀ (nodes : List SymNode) (offset : Nat),
      findNodeIdxAux target offset nodes = none →
      findNodeIdxAux target offset (nodes ++ [x]) = none
  | [], offset, _ => by
    dsimp [findNodeIdxAux]
    have hne : (x == target) = false := by
      cases h : (x == target)
      · rfl
      · exact absurd (of_decide_eq_true h) hx
    rw [hne]
    rfl
  | n :: rest, offset, h => by
    dsimp [findNodeIdxAux] at h ⊢
    split at h
    · cases h
    · rename_i hn
      rw [ite_eq_right hn]
      exact findNodeIdxAux_append_none target x hx rest (offset + 1) h

theorem findNodeIdxAux_append_self (x : SymNode) :
    ∀ (nodes : List SymNode) (offset : Nat),
      findNodeIdxAux x offset nodes = none →
      findNodeIdxAux x offset (nodes ++ [x]) = some (offset + nodes.length)
  | [], offset, _ => by
    dsimp [findNodeIdxAux]
    rw [show (x == x) = true from decide_eq_true rfl]
    rfl
  | n :: rest, offset, h => by
    dsimp [findNodeIdxAux] at h ⊢
    split at h
    · cases h
    · rename_i hn
      rw [ite_eq_right hn, findNodeIdxAux_append_self x rest (offset + 1) h]
      congr 1
      omega

/-- Hash-consed GVN node interning with sound algebraic canonicalization:
    - Folds idempotent conditional branches `ite c x x ↦ x`, identity unary ops
      `op1 .id x ↦ x`, and zero-offset wrapping additions `op1 (.addConst 0) x ↦ x`
      (whose soundness in `internNode_eval` relies on the `u64` word bound
      `evalSymId_lt_word64 : evalSymId tbl env x < 2^64`) directly to existing `SymId` `x`
      without allocating a new node.
    - Interns binary nodes through `internOp2`: an existing occurrence is reused verbatim
      (lookup first), otherwise the table-independent `peepholeOp2` rewrite applies
      duplicate-operand folds (`x & x ↦ x`, `x | x ↦ x`, `x ^ x ↦ 0`, `x - x ↦ 0`,
      `x < x ↦ 0`, `x == x ↦ 1`, `x ≤ x ↦ 1`) and canonical commutative operand order.
    - Deduplicates any previously interned `SymNode` via `findNodeIdx`. -/
def internNode (tbl : SymTable) (node : SymNode) : SymId × SymTable :=
  match node with
  | .ite _ t e =>
    if t == e then
      (t, tbl)
    else
      internRawNode tbl node
  | .op1 .id a => (a, tbl)
  | .op1 (.xorConst mask) a =>
    if mask == 0 then
      (a, tbl)
    else
      internRawNode tbl node
  | .op1 (.addConst delta) a =>
    if delta == 0 then
      (a, tbl)
    else
      internRawNode tbl node
  | .op2 op a b => internOp2 tbl op a b
  | _ => internRawNode tbl node

theorem internRawNode_extends (tbl : SymTable) (node : SymNode) :
    tbl.Extends (internRawNode tbl node).2 := by
  dsimp [internRawNode]
  cases findNodeIdx tbl.nodes node with
  | some _ => exact SymTable.Extends.refl tbl
  | none => exact SymTable.extends_append tbl [node]

theorem internOp2_extends (tbl : SymTable) (op : SymOp2) (a b : SymId) :
    tbl.Extends (internOp2 tbl op a b).2 := by
  unfold internOp2
  split
  · exact SymTable.Extends.refl tbl
  · split
    · exact SymTable.Extends.refl tbl
    · exact internRawNode_extends tbl _

/-- **Monotone Extension Theorem (`internNode_extends`)**:
    `internNode` only appends to `tbl` (or leaves `tbl` unchanged on a GVN hit / fold). -/
theorem internNode_extends (tbl : SymTable) (node : SymNode) :
    tbl.Extends (internNode tbl node).2 := by
  unfold internNode
  cases node with
  | ite c t e =>
    dsimp
    split
    · exact SymTable.Extends.refl tbl
    · exact internRawNode_extends tbl (.ite c t e)
  | op1 op a =>
    cases op <;> dsimp
    · exact SymTable.Extends.refl tbl
    · exact internRawNode_extends tbl (.op1 .boolNot a)
    · exact internRawNode_extends tbl (.op1 .wrappingNeg64 a)
    · exact internRawNode_extends tbl (.op1 .maskLow32 a)
    · rename_i mask
      split
      · exact SymTable.Extends.refl tbl
      · exact internRawNode_extends tbl (.op1 (.xorConst mask) a)
    · rename_i delta
      split
      · exact SymTable.Extends.refl tbl
      · exact internRawNode_extends tbl (.op1 (.addConst delta) a)
  | const v => exact internRawNode_extends tbl (.const v)
  | var idx => exact internRawNode_extends tbl (.var idx)
  | op2 op a b => exact internOp2_extends tbl op a b

theorem internRawNode_valid {tbl : SymTable} {node : SymNode}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length node) :
    ValidTable (internRawNode tbl node).2 ∧
      (internRawNode tbl node).1 < (internRawNode tbl node).2.nodes.length := by
  dsimp [internRawNode]
  cases hFind : findNodeIdx tbl.nodes node with
  | some idx =>
    have hSpec := findNodeIdx_spec hFind
    exact ⟨hValid, hSpec.1⟩
  | none =>
    refine ⟨?_, ?_⟩
    · intro idx n hGet
      cases hlt : decide (idx < tbl.nodes.length) with
      | true =>
        have hlt' : idx < tbl.nodes.length := of_decide_eq_true hlt
        rw [List.getElem?_append_left hlt'] at hGet
        exact hValid idx n hGet
      | false =>
        have hge : tbl.nodes.length ≤ idx := Nat.le_of_not_lt (of_decide_eq_false hlt)
        rw [List.getElem?_append_right hge] at hGet
        cases hDiff : idx - tbl.nodes.length with
        | zero =>
          rw [hDiff] at hGet
          simp at hGet
          subst hGet
          have hIdxEq : idx = tbl.nodes.length := by omega
          rw [hIdxEq]
          exact hNode
        | succ k =>
          rw [hDiff] at hGet
          simp at hGet
    · simp

theorem internOp2_valid {tbl : SymTable} {op : SymOp2} {a b : SymId}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length (.op2 op a b)) :
    ValidTable (internOp2 tbl op a b).2 ∧
      (internOp2 tbl op a b).1 < (internOp2 tbl op a b).2.nodes.length := by
  unfold internOp2
  split
  · rename_i idx hFind
    exact ⟨hValid, (findNodeIdx_spec hFind).1⟩
  · have hPV := peepholeOp2_valid hNode
    split
    · rename_i x hP
      rw [hP] at hPV
      exact ⟨hValid, hPV⟩
    · rename_i node' hP
      rw [hP] at hPV
      exact internRawNode_valid hValid hPV

/-- **Table Validity Preservation (`internNode_valid`)**:
    Interning any node whose children are `< tbl.nodes.length` preserves `ValidTable`
    and returns a valid `SymId < tbl'.nodes.length`. -/
theorem internNode_valid {tbl : SymTable} {node : SymNode}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length node) :
    ValidTable (internNode tbl node).2 ∧
      (internNode tbl node).1 < (internNode tbl node).2.nodes.length := by
  unfold internNode
  cases node with
  | ite c t e =>
    dsimp [ValidNode] at hNode
    dsimp
    split
    · exact ⟨hValid, hNode.2.1⟩
    · exact internRawNode_valid hValid hNode
  | op1 op a =>
    dsimp [ValidNode] at hNode
    cases op <;> dsimp
    · exact ⟨hValid, hNode⟩
    · exact internRawNode_valid hValid hNode
    · exact internRawNode_valid hValid hNode
    · exact internRawNode_valid hValid hNode
    · split
      · exact ⟨hValid, hNode⟩
      · exact internRawNode_valid hValid hNode
    · split
      · exact ⟨hValid, hNode⟩
      · exact internRawNode_valid hValid hNode
  | const v => exact internRawNode_valid hValid hNode
  | var idx => exact internRawNode_valid hValid hNode
  | op2 op a b => exact internOp2_valid hValid hNode

theorem internRawNode_eval {tbl : SymTable} {node : SymNode}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length node) (env : SymEnv) :
    let res := internRawNode tbl node
    evalSymId res.2 env res.1 = evalSymNodeWith (evalSymId tbl env) env node := by
  dsimp [internRawNode]
  cases hFind : findNodeIdx tbl.nodes node with
  | some idx =>
    have hSpec := findNodeIdx_spec hFind
    exact evalSymId_eq_evalSymNodeWith hValid env hSpec.2
  | none =>
    have hValid' := (internRawNode_valid hValid hNode).1
    dsimp [internRawNode] at hValid'
    rw [hFind] at hValid'
    dsimp at hValid'
    have hExt : tbl.Extends { nodes := tbl.nodes ++ [node] } := SymTable.extends_append tbl [node]
    have hLookupNew : (tbl.nodes ++ [node])[tbl.nodes.length]? = some node := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [evalSymId_eq_evalSymNodeWith hValid' env hLookupNew]
    cases node with
    | const v => rfl
    | var idx => rfl
    | op1 op a =>
      dsimp [ValidNode] at hNode
      dsimp [evalSymNodeWith]
      rw [← evalSymId_mono hValid hExt env hNode]
    | op2 op a b =>
      dsimp [ValidNode] at hNode
      dsimp [evalSymNodeWith]
      rw [← evalSymId_mono hValid hExt env hNode.1]
      rw [← evalSymId_mono hValid hExt env hNode.2]
    | ite c t e =>
      dsimp [ValidNode] at hNode
      dsimp [evalSymNodeWith]
      rw [← evalSymId_mono hValid hExt env hNode.1]
      rw [← evalSymId_mono hValid hExt env hNode.2.1]
      rw [← evalSymId_mono hValid hExt env hNode.2.2]

theorem internOp2_eval {tbl : SymTable} {op : SymOp2} {a b : SymId}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length (.op2 op a b)) (env : SymEnv) :
    evalSymId (internOp2 tbl op a b).2 env (internOp2 tbl op a b).1 =
      evalSymOp2 op (evalSymId tbl env a) (evalSymId tbl env b) := by
  unfold internOp2
  split
  · rename_i idx hFind
    exact evalSymId_eq_evalSymNodeWith hValid env (findNodeIdx_spec hFind).2
  · have hPS := peepholeOp2_sound op a b (evalSymId tbl env) env (evalSymId_lt_word64 tbl env a)
    have hPV := peepholeOp2_valid hNode
    split
    · rename_i x hP
      rw [hP] at hPS
      exact hPS
    · rename_i node' hP
      rw [hP] at hPS hPV
      rw [internRawNode_eval hValid hPV env]
      exact hPS

/-- **Evaluation Soundness of `internNode` (`internNode_eval`)**:
    Evaluating the `SymId` returned by `internNode tbl node` in the resulting table
    equals evaluating `node` over `evalSymId tbl env` (including when `ite c x x ↦ x`
    or `op1 .id x ↦ x` folds to an existing `SymId`). -/
theorem internNode_eval {tbl : SymTable} {node : SymNode}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length node) (env : SymEnv) :
    let res := internNode tbl node
    evalSymId res.2 env res.1 = evalSymNodeWith (evalSymId tbl env) env node := by
  unfold internNode
  cases node with
  | ite c t e =>
    dsimp
    split
    · rename_i hCond
      have hEqTE : t = e := of_decide_eq_true hCond
      subst hEqTE
      dsimp [evalSymNodeWith]
      cases (evalSymId tbl env c != 0) <;> rfl
    · exact internRawNode_eval hValid hNode env
  | op1 op a =>
    cases op <;> dsimp
    · dsimp [evalSymNodeWith, evalSymOp1]
    · exact internRawNode_eval hValid hNode env
    · exact internRawNode_eval hValid hNode env
    · exact internRawNode_eval hValid hNode env
    · rename_i mask
      split
      · rename_i hZero
        have hMask : mask = 0 := of_decide_eq_true hZero
        subst hMask
        dsimp [evalSymNodeWith, evalSymOp1, wrap64]
        rw [Nat.xor_zero]
        exact (Nat.mod_eq_of_lt (evalSymId_lt_word64 tbl env a)).symm
      · exact internRawNode_eval hValid hNode env
    · rename_i delta
      split
      · rename_i hZero
        have hDelta : delta = 0 := of_decide_eq_true hZero
        subst hDelta
        dsimp [evalSymNodeWith, evalSymOp1, wrap64]
        exact (Nat.mod_eq_of_lt (evalSymId_lt_word64 tbl env a)).symm
      · exact internRawNode_eval hValid hNode env
  | const v => exact internRawNode_eval hValid hNode env
  | var idx => exact internRawNode_eval hValid hNode env
  | op2 op a b => exact internOp2_eval hValid hNode env

/-- Non-vacuity witness for `addConst 0` and `xorConst 0` peephole folding: interning
    `.op1 (.addConst 0) 0` and `.op1 (.xorConst 0) 0` folds directly to `SymId 0` without
    growing `tbl.nodes`, relying on `evalSymId_lt_word64` for `wrap64` soundness. -/
theorem internNode_addConst0_peephole_witness :
    internNode { nodes := [.var 0] } (.op1 (.addConst 0) 0) = (0, { nodes := [.var 0] }) ∧
      internNode { nodes := [.var 0] } (.op1 (.xorConst 0) 0) = (0, { nodes := [.var 0] }) :=
  ⟨rfl, rfl⟩

/-- **GVN Deduplication Theorem (`internNode_dedup`)**:
    Re-interning a `node` that was just interned returns the exact same `SymId`
    and leaves `tbl` (and `tbl.nodes.length`) completely unchanged. -/
theorem internRawNode_dedup (tbl : SymTable) (node : SymNode) :
    let res₁ := internRawNode tbl node
    internRawNode res₁.2 node = res₁ ∧
      (internRawNode res₁.2 node).2.nodes.length = res₁.2.nodes.length := by
  dsimp [internRawNode]
  cases hFind : findNodeIdx tbl.nodes node with
  | some idx =>
    dsimp
    rw [hFind]
    exact ⟨rfl, rfl⟩
  | none =>
    dsimp
    have hLookupApp : (tbl.nodes ++ [node])[tbl.nodes.length]? = some node := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rcases findNodeIdx_complete hLookupApp with ⟨idx, hFindApp⟩
    have hSpec := findNodeIdx_spec hFindApp
    rw [hFindApp]
    have hIdxEq : idx = tbl.nodes.length := by
      cases hlt : decide (idx < tbl.nodes.length) with
      | true =>
        have hlt' : idx < tbl.nodes.length := of_decide_eq_true hlt
        have hInOld : tbl.nodes[idx]? = some node := by
          have hGet := hSpec.2
          rw [List.getElem?_append_left hlt'] at hGet
          exact hGet
        rcases findNodeIdx_complete hInOld with ⟨idx₀, hFind₀⟩
        rw [hFind] at hFind₀
        cases hFind₀
      | false =>
        have hge : tbl.nodes.length ≤ idx := Nat.le_of_not_lt (of_decide_eq_false hlt)
        have hLen : (tbl.nodes ++ [node]).length = tbl.nodes.length + 1 := by simp
        have hlt' := hSpec.1
        omega
    subst hIdxEq
    exact ⟨rfl, rfl⟩

theorem internOp2_dedup (tbl : SymTable) (op : SymOp2) (a b : SymId) :
    internOp2 (internOp2 tbl op a b).2 op a b = internOp2 tbl op a b := by
  cases hFind : findNodeIdx tbl.nodes (.op2 op a b) with
  | some idx =>
    have h1 : internOp2 tbl op a b = (idx, tbl) := by
      unfold internOp2
      rw [hFind]
    rw [h1]
    exact h1
  | none =>
    cases hP : peepholeOp2 op a b with
    | inl x =>
      have h1 : internOp2 tbl op a b = (x, tbl) := by
        unfold internOp2
        rw [hFind, hP]
      rw [h1]
      exact h1
    | inr node' =>
      have h1 : internOp2 tbl op a b = internRawNode tbl node' := by
        unfold internOp2
        rw [hFind, hP]
      rw [h1]
      cases hRaw : findNodeIdx tbl.nodes node' with
      | some j =>
        have hR : internRawNode tbl node' = (j, tbl) := by
          unfold internRawNode
          rw [hRaw]
        rw [hR]
        show internOp2 tbl op a b = (j, tbl)
        rw [h1, hR]
      | none =>
        have hR : internRawNode tbl node' =
            (tbl.nodes.length, { nodes := tbl.nodes ++ [node'] }) := by
          unfold internRawNode
          rw [hRaw]
        rw [hR]
        by_cases hEq : node' = .op2 op a b
        · subst hEq
          have hSelf := findNodeIdxAux_append_self (.op2 op a b) tbl.nodes 0 hFind
          unfold internOp2
          dsimp only
          rw [show findNodeIdx (tbl.nodes ++ [SymNode.op2 op a b]) (.op2 op a b) =
            some tbl.nodes.length from by
              unfold findNodeIdx
              rw [hSelf, Nat.zero_add]]
        · have hNone := findNodeIdxAux_append_none (.op2 op a b) node' hEq tbl.nodes 0 hFind
          unfold internOp2
          dsimp only
          rw [show findNodeIdx (tbl.nodes ++ [node']) (.op2 op a b) = none from hNone, hP]
          have hD := (internRawNode_dedup tbl node').1
          rw [hR] at hD
          exact hD

theorem internNode_dedup (tbl : SymTable) (node : SymNode) :
    let res₁ := internNode tbl node
    internNode res₁.2 node = res₁ ∧
      (internNode res₁.2 node).2.nodes.length = res₁.2.nodes.length := by
  dsimp
  cases node with
  | ite c t e =>
    cases hEq : (t == e) with
    | true =>
      have hStep : internNode tbl (.ite c t e) = (t, tbl) := by
        dsimp [internNode]
        rw [hEq]
        rfl
      rw [hStep]
      dsimp
      rw [hStep]
      exact ⟨rfl, rfl⟩
    | false =>
      have hStep₁ : internNode tbl (.ite c t e) = internRawNode tbl (.ite c t e) := by
        dsimp [internNode]
        rw [hEq]
        rfl
      have hStep₂ : internNode (internRawNode tbl (.ite c t e)).2 (.ite c t e) =
          internRawNode (internRawNode tbl (.ite c t e)).2 (.ite c t e) := by
        dsimp [internNode]
        rw [hEq]
        rfl
      rw [hStep₁, hStep₂]
      exact internRawNode_dedup tbl (.ite c t e)
  | op1 op a =>
    cases op <;> dsimp [internNode]
    · exact ⟨rfl, rfl⟩
    · exact internRawNode_dedup tbl (.op1 .boolNot a)
    · exact internRawNode_dedup tbl (.op1 .wrappingNeg64 a)
    · exact internRawNode_dedup tbl (.op1 .maskLow32 a)
    · rename_i mask
      cases hZero : (mask == 0) with
      | true => exact ⟨rfl, rfl⟩
      | false => exact internRawNode_dedup tbl (.op1 (.xorConst mask) a)
    · rename_i delta
      cases hZero : (delta == 0) with
      | true => exact ⟨rfl, rfl⟩
      | false => exact internRawNode_dedup tbl (.op1 (.addConst delta) a)
  | const v => exact internRawNode_dedup tbl (.const v)
  | var idx => exact internRawNode_dedup tbl (.var idx)
  | op2 op a b =>
    exact ⟨internOp2_dedup tbl op a b,
      congrArg (fun r => r.2.nodes.length) (internOp2_dedup tbl op a b)⟩

theorem internRawNode_tbl_of_mem {tbl : SymTable} {node : SymNode} {i : Nat}
    (hAt : tbl.nodes[i]? = some node) : (internRawNode tbl node).2 = tbl := by
  rcases findNodeIdx_complete hAt with ⟨idx, hFind⟩
  dsimp only [internRawNode]
  rw [hFind]

theorem internOp2_tbl_of_mem {tbl : SymTable} {op : SymOp2} {a b : SymId} {i : Nat}
    (hAt : tbl.nodes[i]? = some (.op2 op a b)) : (internOp2 tbl op a b).2 = tbl := by
  rcases findNodeIdx_complete hAt with ⟨idx, hFind⟩
  unfold internOp2
  rw [hFind]

theorem internNode_tbl_of_mem {tbl : SymTable} {node : SymNode} {i : Nat}
    (hAt : tbl.nodes[i]? = some node) : (internNode tbl node).2 = tbl := by
  unfold internNode
  cases node with
  | ite c t e =>
    dsimp only
    split
    · rfl
    · exact internRawNode_tbl_of_mem hAt
  | op1 op a =>
    cases op <;> dsimp only <;>
      first | rfl | exact internRawNode_tbl_of_mem hAt |
        (split <;> first | rfl | exact internRawNode_tbl_of_mem hAt)
  | const v => exact internRawNode_tbl_of_mem hAt
  | var idx => exact internRawNode_tbl_of_mem hAt
  | op2 op a b => exact internOp2_tbl_of_mem hAt

/-- **Strong GVN Deduplication (`internNode_dedup_existing`)**: interning ANY node that already
    occurs anywhere in a valid table (not just the most recently interned one) leaves the
    table — hence `tbl.nodes.length` — unchanged and returns a `SymId` that denotes the same
    value as the existing occurrence under every `env`. -/
theorem internNode_dedup_existing {tbl : SymTable} {node : SymNode} {i : Nat}
    (hValid : ValidTable tbl) (hAt : tbl.nodes[i]? = some node) :
    (internNode tbl node).2 = tbl ∧
      ∀ env, evalSymId tbl env (internNode tbl node).1 = evalSymId tbl env i := by
  have hLt : i < tbl.nodes.length := by
    cases h : decide (i < tbl.nodes.length) with
    | true => exact of_decide_eq_true h
    | false =>
      rw [List.getElem?_eq_none (Nat.le_of_not_lt (of_decide_eq_false h))] at hAt
      cases hAt
  have hNode : ValidNode tbl.nodes.length node := (hValid i node hAt).mono (Nat.le_of_lt hLt)
  have hTbl := internNode_tbl_of_mem hAt
  refine ⟨hTbl, fun env => ?_⟩
  have h1 := internNode_eval hValid hNode env
  dsimp only at h1
  rw [hTbl] at h1
  rw [h1, evalSymId_eq_evalSymNodeWith hValid env hAt]

/-- Six interning steps over `[x₀, x₁]` exercising every peephole class. -/
def peepholeDemo : List SymId × SymTable :=
  let t₀ : SymTable := { nodes := [.var 0, .var 1] }
  let r₁ := internNode t₀ (.op2 .add 1 0)
  let r₂ := internNode r₁.2 (.op2 .add 0 1)
  let r₃ := internNode r₂.2 (.op2 .bitXor 0 0)
  let r₄ := internNode r₃.2 (.op2 .sub 0 0)
  let r₅ := internNode r₄.2 (.op2 .bitAnd 1 1)
  let r₆ := internNode r₅.2 (.op2 .eq 0 0)
  ([r₁.1, r₂.1, r₃.1, r₄.1, r₅.1, r₆.1], r₆.2)

/-- **Peephole GVN Witness (`peepholeOp2_witness`)**: `x₁ + x₀` and `x₀ + x₁` share one
    `SymId` (canonical commutative order); `x₀ ^ x₀` and `x₀ - x₀` fold to one shared constant
    `0`; `x₁ & x₁` folds to `x₁` without allocating; `x₀ == x₀` folds to the constant `1`. -/
theorem peepholeOp2_witness :
    peepholeDemo = ([2, 2, 3, 3, 1, 4],
      { nodes := [.var 0, .var 1, .op2 .add 0 1, .const 0, .const 1] }) := by
  decide +kernel

/-- Key structural freshness lemma: in any `ValidTable tbl`, every existing node at
    `idx < tbl.nodes.length` satisfies `ValidNode (tbl.nodes.length - 1) node`.
    Therefore, any node that references the newest `SymId` (`last = tbl.nodes.length - 1`)
    cannot already appear anywhere in `tbl.nodes`! -/
theorem findNodeIdx_eq_none_of_not_valid_last {tbl : SymTable} {node : SymNode}
    (hValid : ValidTable tbl)
    (hNotValid : ¬ ValidNode (tbl.nodes.length - 1) node) :
    findNodeIdx tbl.nodes node = none := by
  cases hFind : findNodeIdx tbl.nodes node with
  | none => rfl
  | some idx =>
    have hSpec := findNodeIdx_spec hFind
    have hNodeValid : ValidNode idx node := hValid idx node hSpec.2
    have hLe : idx ≤ tbl.nodes.length - 1 := by omega
    exact False.elim (hNotValid (hNodeValid.mono hLe))

/-!
### 1.1 $k$-Step Diamond Expression Scaling (`2 * k + 1` DAG Nodes vs. `4 * 2^k - 3` Tree Nodes)
-/

/-- Naive unshared symbolic expression AST produced by direct substitution without GVN. -/
inductive ExprTree where
  | const (val : Nat)
  | var (inputIdx : Nat)
  | op1 (op : SymOp1) (arg : ExprTree)
  | op2 (op : SymOp2) (lhs rhs : ExprTree)
  | ite (cond thenBr elseBr : ExprTree)
  deriving DecidableEq

/-- Concrete evaluation of a `ExprTree`. -/
def ExprTree.eval (env : SymEnv) : ExprTree → Nat
  | .const v => wrap64 v
  | .var idx => wrap64 (env idx)
  | .op1 op a => evalSymOp1 op (a.eval env)
  | .op2 op a b => evalSymOp2 op (a.eval env) (b.eval env)
  | .ite c t e => if c.eval env != 0 then t.eval env else e.eval env

/-- Total AST node count of a `ExprTree`. -/
def ExprTree.nodeCount : ExprTree → Nat
  | .const _ => 1
  | .var _ => 1
  | .op1 _ a => 1 + a.nodeCount
  | .op2 _ a b => 1 + a.nodeCount + b.nodeCount
  | .ite c t e => 1 + c.nodeCount + t.nodeCount + e.nodeCount

/-- Build the $k$-step diamond expression `x_{i+1} = add(xor(x_i, i+1), xor(x_i, i+1))`
    by naive tree substitution (`ExprTree`), duplicating `x_i` across both arms at each step. -/
def buildDiamondTree : Nat → ExprTree
  | 0 => .var 0
  | i + 1 =>
    let prev := buildDiamondTree i
    let br := ExprTree.op1 (.xorConst (i + 1)) prev
    ExprTree.op2 .add br br

/-- Build the exact same $k$-step diamond expression via `SymTable` GVN (`internNode`),
    where both branches of diamond `i + 1` intern `.op1 (.xorConst (i + 1)) prevId` and
    join via `.op2 .add leftId rightId`. -/
def buildDiamondGvn : Nat → Nat × SymTable
  | 0 => (0, { nodes := [.var 0] })
  | i + 1 =>
    let (prevId, tbl₀) := buildDiamondGvn i
    let xorNode := SymNode.op1 (.xorConst (i + 1)) prevId
    let (leftId, tbl₁) := internNode tbl₀ xorNode
    let (rightId, tbl₂) := internNode tbl₁ xorNode
    internNode tbl₂ (.op2 .add leftId rightId)

/-- Exponential $O(2^k)$ node blowup of naive tree substitution:
    `(buildDiamondTree k).nodeCount + 3 = 4 * 2^k`. -/
theorem buildDiamondTree_nodeCount (k : Nat) :
    (buildDiamondTree k).nodeCount + 3 = 4 * (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ i ih =>
    dsimp [buildDiamondTree, ExprTree.nodeCount]
    rw [Nat.pow_succ]
    omega

/-- **Universal $k$-Step Diamond GVN Theorem (`buildDiamondGvn_spec`)**:
    For every `k : Nat`, `buildDiamondGvn k` produces a valid `SymTable` with:
    1. Root `SymId = 2 * k`,
    2. Exact linear table size `2 * k + 1` (vs. `4 * 2^k - 3` for `buildDiamondTree k`), and
    3. Identical concrete evaluation `evalSymId tbl env rootId = (buildDiamondTree k).eval env`
       for all input environments `env : SymEnv`. -/
theorem buildDiamondGvn_spec (k : Nat) :
    let (rootId, tbl) := buildDiamondGvn k
    ValidTable tbl ∧
      rootId = 2 * k ∧
      tbl.nodes.length = 2 * k + 1 ∧
      ∀ env : SymEnv, evalSymId tbl env rootId = (buildDiamondTree k).eval env := by
  induction k with
  | zero =>
    refine ⟨?_, rfl, rfl, fun _ => rfl⟩
    intro idx node hGet
    cases idx with
    | zero =>
      dsimp [buildDiamondGvn] at hGet
      injection hGet with hEq
      subst hEq
      trivial
    | succ k' =>
      dsimp [buildDiamondGvn] at hGet
      cases hGet
  | succ i ih =>
    rcases hPrev : buildDiamondGvn i with ⟨prevId, tbl₀⟩
    rw [hPrev] at ih
    rcases ih with ⟨hValid₀, hPrevId, hLen₀, hEval₀⟩
    dsimp [buildDiamondGvn]
    rw [hPrev]
    dsimp
    let xorNode := SymNode.op1 (.xorConst (i + 1)) prevId
    have hXorValid₀ : ValidNode tbl₀.nodes.length xorNode := by
      dsimp [ValidNode, xorNode]
      omega
    have hXorNotValidLast : ¬ ValidNode (tbl₀.nodes.length - 1) xorNode := by
      dsimp [ValidNode, xorNode]
      intro hContra
      omega
    have hFindXor : findNodeIdx tbl₀.nodes xorNode = none :=
      findNodeIdx_eq_none_of_not_valid_last hValid₀ hXorNotValidLast
    have hStep₁ : internNode tbl₀ xorNode = (tbl₀.nodes.length, { nodes := tbl₀.nodes ++ [xorNode] }) := by
      dsimp [internNode, xorNode, internRawNode]
      rw [hFindXor]
    have hDedup := (internNode_dedup tbl₀ xorNode).1
    have hValid₁ : ValidTable (internNode tbl₀ xorNode).2 :=
      (internNode_valid hValid₀ hXorValid₀).1
    have hEval₁ : ∀ env, evalSymId (internNode tbl₀ xorNode).2 env (internNode tbl₀ xorNode).1 =
        evalSymOp1 (.xorConst (i + 1)) (evalSymId tbl₀ env prevId) := by
      intro env
      exact internNode_eval hValid₀ hXorValid₀ env
    rw [hDedup]
    rw [hStep₁] at hValid₁ hEval₁ ⊢
    dsimp at hValid₁ hEval₁ ⊢
    let leftId := tbl₀.nodes.length
    let tbl₁ : SymTable := { nodes := tbl₀.nodes ++ [xorNode] }
    have hLen₁ : tbl₁.nodes.length = 2 * i + 2 := by
      dsimp [tbl₁]
      rw [List.length_append, hLen₀]
      rfl
    let addNode := SymNode.op2 .add leftId leftId
    have hAddValid₁ : ValidNode tbl₁.nodes.length addNode := by
      dsimp [ValidNode, addNode, leftId]
      exact ⟨by omega, by omega⟩
    have hAddNotValidLast : ¬ ValidNode (tbl₁.nodes.length - 1) addNode := by
      dsimp [ValidNode, addNode, leftId]
      intro hContra
      have hContra₁ := hContra.1
      omega
    have hFindAdd : findNodeIdx tbl₁.nodes addNode = none :=
      findNodeIdx_eq_none_of_not_valid_last hValid₁ hAddNotValidLast
    have hStep₃ : internNode tbl₁ addNode = (tbl₁.nodes.length, { nodes := tbl₁.nodes ++ [addNode] }) := by
      show internOp2 tbl₁ .add leftId leftId = _
      unfold internOp2
      rw [hFindAdd]
      dsimp only [peepholeOp2]
      rw [ite_eq_left (rfl : leftId = leftId)]
      dsimp only
      unfold internRawNode
      rw [hFindAdd]
    have hValid₃ : ValidTable (internNode tbl₁ addNode).2 :=
      (internNode_valid hValid₁ hAddValid₁).1
    have hEval₃ : ∀ env, evalSymId (internNode tbl₁ addNode).2 env (internNode tbl₁ addNode).1 =
        evalSymOp2 .add (evalSymId tbl₁ env leftId) (evalSymId tbl₁ env leftId) := by
      intro env
      exact internNode_eval hValid₁ hAddValid₁ env
    rw [hStep₃] at hValid₃ hEval₃ ⊢
    dsimp at hValid₃ hEval₃ ⊢
    refine ⟨hValid₃, by omega, ?_, ?_⟩
    · rw [List.length_append, hLen₁]
      dsimp
      omega
    · intro env
      rw [hEval₃ env]
      rw [hEval₁ env]
      rw [hEval₀ env]
      rfl

/-- Concrete non-vacuity witness for `k = 6` diamond steps:
    `SymTable` GVN uses `13` nodes (`2 * 6 + 1`) whereas `ExprTree` uses `253` nodes
    (`4 * 2^6 - 3`), and both evaluate to the exact same value on input `x₀ = 42`. -/
theorem diamond6_gvn_vs_tree_witness :
    (buildDiamondGvn 6).2.nodes.length = 13 ∧
      (buildDiamondTree 6).nodeCount = 253 ∧
      evalSymId (buildDiamondGvn 6).2 (fun _ => 42) (buildDiamondGvn 6).1 =
        (buildDiamondTree 6).eval (fun _ => 42) :=
  ⟨rfl, rfl, rfl⟩

/-- GVN-intern a naive `ExprTree` into `tbl` bottom-up (hash-consing every subtree). -/
def internTree : SymTable → ExprTree → SymId × SymTable
  | tbl, .const v => internNode tbl (.const v)
  | tbl, .var i => internNode tbl (.var i)
  | tbl, .op1 op a =>
    match internTree tbl a with
    | (ia, t₁) => internNode t₁ (.op1 op ia)
  | tbl, .op2 op a b =>
    match internTree tbl a with
    | (ia, t₁) =>
      match internTree t₁ b with
      | (ib, t₂) => internNode t₂ (.op2 op ia ib)
  | tbl, .ite c t e =>
    match internTree tbl c with
    | (ic, t₁) =>
      match internTree t₁ t with
      | (it, t₂) =>
        match internTree t₂ e with
        | (ie, t₃) => internNode t₃ (.ite ic it ie)

theorem internNode_spec {tbl : SymTable} {node : SymNode} (hValid : ValidTable tbl)
    (hNode : ValidNode tbl.nodes.length node) :
    ValidTable (internNode tbl node).2 ∧ tbl.Extends (internNode tbl node).2 ∧
      (internNode tbl node).1 < (internNode tbl node).2.nodes.length ∧
      ∀ env, evalSymId (internNode tbl node).2 env (internNode tbl node).1 =
        evalSymNodeWith (evalSymId tbl env) env node :=
  ⟨(internNode_valid hValid hNode).1, internNode_extends tbl node,
    (internNode_valid hValid hNode).2, fun env => internNode_eval hValid hNode env⟩

/-- **Tree Interning Soundness (`internTree_spec`)**: GVN-interning ANY `ExprTree` preserves
    `ValidTable`, only extends the table, and yields a `SymId` denoting exactly the tree. -/
theorem internTree_spec : ∀ (t : ExprTree) (tbl : SymTable), ValidTable tbl →
    ValidTable (internTree tbl t).2 ∧ tbl.Extends (internTree tbl t).2 ∧
      (internTree tbl t).1 < (internTree tbl t).2.nodes.length ∧
      ∀ env, evalSymId (internTree tbl t).2 env (internTree tbl t).1 = t.eval env
  | .const v, tbl, hValid => by
    rcases internNode_spec (node := .const v) hValid trivial with ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, fun env => h4 env⟩
  | .var i, tbl, hValid => by
    rcases internNode_spec (node := .var i) hValid trivial with ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, fun env => h4 env⟩
  | .op1 op a, tbl, hValid => by
    rcases internTree_spec a tbl hValid with ⟨hV₁, hE₁, hLt₁, hEv₁⟩
    rcases hA : internTree tbl a with ⟨ia, t₁⟩
    rw [hA] at hV₁ hE₁ hLt₁ hEv₁
    rcases internNode_spec (node := .op1 op ia) hV₁ hLt₁ with ⟨h1, h2, h3, h4⟩
    simp only [internTree, hA]
    refine ⟨h1, hE₁.trans h2, h3, fun env => ?_⟩
    rw [h4 env]
    simp only [evalSymNodeWith, ExprTree.eval, hEv₁ env]
  | .op2 op a b, tbl, hValid => by
    rcases internTree_spec a tbl hValid with ⟨hV₁, hE₁, hLt₁, hEv₁⟩
    rcases hA : internTree tbl a with ⟨ia, t₁⟩
    rw [hA] at hV₁ hE₁ hLt₁ hEv₁
    rcases internTree_spec b t₁ hV₁ with ⟨hV₂, hE₂, hLt₂, hEv₂⟩
    rcases hB : internTree t₁ b with ⟨ib, t₂⟩
    rw [hB] at hV₂ hE₂ hLt₂ hEv₂
    have hIa : ia < t₂.nodes.length := Nat.lt_of_lt_of_le hLt₁ hE₂.length_le
    rcases internNode_spec (node := .op2 op ia ib) hV₂ ⟨hIa, hLt₂⟩ with ⟨h1, h2, h3, h4⟩
    simp only [internTree, hA, hB]
    refine ⟨h1, (hE₁.trans hE₂).trans h2, h3, fun env => ?_⟩
    rw [h4 env]
    simp only [evalSymNodeWith, ExprTree.eval]
    rw [← evalSymId_mono hV₁ hE₂ env hLt₁, hEv₁ env, hEv₂ env]
  | .ite c t e, tbl, hValid => by
    rcases internTree_spec c tbl hValid with ⟨hV₁, hE₁, hLt₁, hEv₁⟩
    rcases hC : internTree tbl c with ⟨ic, t₁⟩
    rw [hC] at hV₁ hE₁ hLt₁ hEv₁
    rcases internTree_spec t t₁ hV₁ with ⟨hV₂, hE₂, hLt₂, hEv₂⟩
    rcases hT : internTree t₁ t with ⟨it, t₂⟩
    rw [hT] at hV₂ hE₂ hLt₂ hEv₂
    rcases internTree_spec e t₂ hV₂ with ⟨hV₃, hE₃, hLt₃, hEv₃⟩
    rcases hE : internTree t₂ e with ⟨ie, t₃⟩
    rw [hE] at hV₃ hE₃ hLt₃ hEv₃
    have hIc : ic < t₃.nodes.length :=
      Nat.lt_of_lt_of_le hLt₁ (Nat.le_trans hE₂.length_le hE₃.length_le)
    have hIt : it < t₃.nodes.length := Nat.lt_of_lt_of_le hLt₂ hE₃.length_le
    rcases internNode_spec (node := .ite ic it ie) hV₃ ⟨hIc, hIt, hLt₃⟩ with ⟨h1, h2, h3, h4⟩
    simp only [internTree, hC, hT, hE]
    refine ⟨h1, ((hE₁.trans hE₂).trans hE₃).trans h2, h3, fun env => ?_⟩
    rw [h4 env]
    simp only [evalSymNodeWith, ExprTree.eval]
    rw [← evalSymId_mono hV₁ (hE₂.trans hE₃) env hLt₁, ← evalSymId_mono hV₂ hE₃ env hLt₂,
      hEv₁ env, hEv₂ env, hEv₃ env]

/-!
## Section 2 — Raw vs. Canonical MIR State (`CanonLocals` + Borrow-Dirtied Generations) & Spine Forcing
-/

/-- Local variable index in a MIR body. -/
abbrev LocalId := Nat

/-- Polymorphic MIR local slot parameterized by the payload type `Val` (`Nat` for
    concrete values or `SymId` for symbolic GVN value references):
    - `.dead gen`: storage is dead; `gen` is the next generation counter to assign.
    - `.uninit gen`: storage is live (`StorageLive`), value not yet initialized.
    - `.live val gen borrowed loanTarget`: holds initialized value `val` at generation
      `gen`, where `borrowed == true` iff a reference (`Rvalue.ref` / `retagBorrow`) has
      been taken to this incarnation, and `loanTarget` optionally tracks `(targetLocal,
      expectedGen)` when this local itself holds a reference. -/
inductive Slot (Val : Type) where
  | dead (gen : Nat := 0)
  | uninit (gen : Nat := 0)
  | live (val : Val) (gen : Nat := 0) (borrowed : Bool := false)
      (loanTarget : Option (LocalId × Nat) := none)
  deriving DecidableEq

/-- Extract the generation counter of a `Slot`. -/
def Slot.gen {Val : Type} : Slot Val → Nat
  | .dead g => g
  | .uninit g => g
  | .live _ g _ _ => g

/-- Borrow-dirtied generation transition (`c19b8fce8`): ending or restarting a slot's
    storage lifetime increments `gen` **if and only if** the current incarnation was
    borrowed (`borrowed == true`). Unborrowed temporaries preserve `gen` unchanged! -/
def Slot.nextGenOnEnd {Val : Type} : Slot Val → Nat
  | .dead g => g
  | .uninit g => g
  | .live _ g false _ => g
  | .live _ g true _ => g + 1

/-- `StorageDead` transition on a single slot. -/
def Slot.kill {Val : Type} (s : Slot Val) : Slot Val :=
  .dead s.nextGenOnEnd

/-- `StorageLive` transition on a single slot. -/
def Slot.reborn {Val : Type} (s : Slot Val) : Slot Val :=
  .uninit s.nextGenOnEnd

/-- Assign a scalar/symbolic value `v` (with optional loan metadata) into a slot,
    preserving its current `gen` and `borrowed` flag if already live. -/
def Slot.writeVal {Val : Type} (s : Slot Val) (v : Val)
    (loanTarget : Option (LocalId × Nat) := none) : Slot Val :=
  match s with
  | .live _ g b _ => .live v g b loanTarget
  | .uninit g | .dead g => .live v g false loanTarget

/-- Universal temporal safety lemma: killing or rebirthing a borrowed slot
    (`.live v g true loan`) strictly advances its generation to `g + 1`. -/
theorem Slot.kill_or_reborn_borrowed_bumps_gen {Val : Type} (v : Val) (g : Nat)
    (loan : Option (LocalId × Nat)) :
    (Slot.live v g true loan).kill.gen = g + 1 ∧
      (Slot.live v g true loan).reborn.gen = g + 1 :=
  ⟨rfl, rfl⟩

/-- Universal unborrowed temporary round-trip identity: `StorageLive -> Assign ->
    StorageDead` on any unborrowed `.dead g` slot returns to `.dead g` by `rfl`. -/
theorem Slot.unborrowed_roundtrip_rfl {Val : Type} (v : Val) (g : Nat) :
    (((Slot.dead g).reborn).writeVal v none).kill = Slot.dead g :=
  rfl

/-- `Slot.kill` is idempotent on all slots. -/
theorem Slot.kill_idempotent {Val : Type} (s : Slot Val) :
    s.kill.kill = s.kill := by
  cases s with
  | dead g => rfl
  | uninit g => rfl
  | live v g b loan =>
    cases b <;> rfl

/-- Normalize a slot against a join-point liveness bit `isLive`: live locals keep their
    slot unchanged; dead locals (`isLive = false`) are killed via `Slot.kill` (which
    preserves their borrow-dirtied generation counter while pruning dead values). -/
def normalizeSlotForMask {Val : Type} (isLive : Bool) (s : Slot Val) : Slot Val :=
  if isLive then s else s.kill

theorem normalizeSlotForMask_idempotent {Val : Type} (isLive : Bool) (s : Slot Val) :
    normalizeSlotForMask isLive (normalizeSlotForMask isLive s) =
      normalizeSlotForMask isLive s := by
  cases isLive with
  | true => rfl
  | false => exact Slot.kill_idempotent s

/-- History-dependent `RawState`: models an uncanonicalized association-list write log
    where out-of-order updates and branch-local `StorageLive`/`StorageDead` events
    leave path-dependent history in `writeLog`. -/
structure RawState (Val : Type) where
  numLocals : Nat
  writeLog : List (LocalId × Slot Val) := []
  deriving DecidableEq

/-- Look up the most recent slot for `loc` in a `RawState` write log. -/
def RawState.getSlot {Val : Type} (st : RawState Val) (loc : LocalId) : Slot Val :=
  match st.writeLog.find? (fun entry => entry.1 == loc) with
  | some (_, s) => s
  | none => .dead 0

def RawState.putSlot {Val : Type} (st : RawState Val) (loc : LocalId) (s : Slot Val) : RawState Val :=
  { st with writeLog := (loc, s) :: st.writeLog }

def RawState.storageLive {Val : Type} (st : RawState Val) (loc : LocalId) : RawState Val :=
  st.putSlot loc (st.getSlot loc).reborn

def RawState.storageDead {Val : Type} (st : RawState Val) (loc : LocalId) : RawState Val :=
  st.putSlot loc (st.getSlot loc).kill

def RawState.assign {Val : Type} (st : RawState Val) (loc : LocalId) (v : Val) : RawState Val :=
  st.putSlot loc ((st.getSlot loc).writeVal v none)

/-- Write-log well-formedness: every logged write targets an in-bounds local `< numLocals`. -/
def RawWriteLogWF {Val : Type} : Nat → List (LocalId × Slot Val) → Prop
  | _, [] => True
  | n, (loc, _) :: rest => loc < n ∧ RawWriteLogWF n rest

/-- A `RawState` is well-formed (`RawState.WF`) when all entries in `writeLog` satisfy
    `loc < st.numLocals`. -/
def RawState.WF {Val : Type} (st : RawState Val) : Prop :=
  RawWriteLogWF st.numLocals st.writeLog

theorem RawState.putSlot_wf {Val : Type} {st : RawState Val} {loc : LocalId} {s : Slot Val}
    (hWF : st.WF) (hLt : loc < st.numLocals) : (st.putSlot loc s).WF :=
  ⟨hLt, hWF⟩

theorem RawState.storageLive_wf {Val : Type} {st : RawState Val} {loc : LocalId}
    (hWF : st.WF) (hLt : loc < st.numLocals) : (st.storageLive loc).WF :=
  ⟨hLt, hWF⟩

theorem RawState.storageDead_wf {Val : Type} {st : RawState Val} {loc : LocalId}
    (hWF : st.WF) (hLt : loc < st.numLocals) : (st.storageDead loc).WF :=
  ⟨hLt, hWF⟩

theorem RawState.assign_wf {Val : Type} {st : RawState Val} {loc : LocalId} {v : Val}
    (hWF : st.WF) (hLt : loc < st.numLocals) : (st.assign loc v).WF :=
  ⟨hLt, hWF⟩

theorem find?_eq_none_of_rawWriteLogWF {Val : Type} (n loc : Nat) (hGe : n ≤ loc) :
    ∀ (log : List (LocalId × Slot Val)),
      RawWriteLogWF n log →
      log.find? (fun entry => entry.1 == loc) = none
  | [], _ => rfl
  | (l, _) :: rest, ⟨hLt, hRest⟩ => by
    have hNe : (l == loc) = false :=
      beq_eq_false_iff_ne.2 (Nat.ne_of_lt (Nat.lt_of_lt_of_le hLt hGe))
    dsimp [List.find?]
    rw [hNe]
    exact find?_eq_none_of_rawWriteLogWF n loc hGe rest hRest

/-- Any well-formed `RawState` returns `.dead 0` for every out-of-bounds local `loc ≥ numLocals`. -/
theorem RawState.getSlot_of_ge_numLocals {Val : Type} {st : RawState Val} {loc : LocalId}
    (hWF : st.WF) (hGe : st.numLocals ≤ loc) :
    st.getSlot loc = .dead 0 := by
  dsimp [RawState.getSlot]
  rw [find?_eq_none_of_rawWriteLogWF st.numLocals loc hGe st.writeLog hWF]

/-- Canonical MIR local state (`CanonState` / `CanonLocals`): a dense, strictly index-ordered
    list of `Slot Val` entries (where index `i` is local `i`) with dead locals pruned to
    `.dead gen`. -/
structure CanonState (Val : Type) where
  slots : List (Slot Val)
  deriving DecidableEq

/-- Canonical MIR local store alias (`CanonLocals`). -/
abbrev CanonLocals (Val : Type) := CanonState Val

/-- Spine-preserving list update at index `idx`. -/
def setSlotAt {Val : Type} : List (Slot Val) → Nat → Slot Val → List (Slot Val)
  | [], _, _ => []
  | _ :: xs, 0, s => s :: xs
  | x :: xs, i + 1, s => x :: setSlotAt xs i s

/-- Total slot lookup in a canonical slot list. -/
def getSlotAt {Val : Type} : List (Slot Val) → Nat → Slot Val
  | [], _ => .dead 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getSlotAt xs i

def CanonState.getSlot {Val : Type} (st : CanonState Val) (loc : LocalId) : Slot Val :=
  getSlotAt st.slots loc

def CanonState.setSlot {Val : Type} (st : CanonState Val) (loc : LocalId) (s : Slot Val) :
    CanonState Val :=
  { slots := setSlotAt st.slots loc s }

theorem getSlotAt_eq_getElem? {Val : Type} :
    ∀ (slots : List (Slot Val)) (i : Nat),
      i < slots.length →
      slots[i]? = some (getSlotAt slots i)
  | [], _, hlt => by simp at hlt
  | x :: _, 0, _ => rfl
  | _ :: xs, i + 1, hlt => by
    dsimp [getSlotAt]
    exact getSlotAt_eq_getElem? xs i (by dsimp at hlt; omega)

/-- Build the canonical slot list for indices `offset .. offset + mask.length - 1`
    from a slot lookup function `lookup`. -/
def buildCanonSlotsAux {Val : Type} (lookup : LocalId → Slot Val) (offset : Nat) :
    List Bool → List (Slot Val)
  | [] => []
  | isLive :: rest =>
    normalizeSlotForMask isLive (lookup offset) ::
      buildCanonSlotsAux lookup (offset + 1) rest

/-- Canonicalize a `RawState` against a join-point `liveMask : List Bool`. -/
def canonicalize {Val : Type} (liveMask : List Bool) (raw : RawState Val) : CanonState Val :=
  { slots := buildCanonSlotsAux raw.getSlot 0 liveMask }

/-- Re-canonicalize an already-canonical `CanonState` against `liveMask`. -/
def canonicalizeCanon {Val : Type} (liveMask : List Bool) (st : CanonState Val) : CanonState Val :=
  { slots := buildCanonSlotsAux st.getSlot 0 liveMask }

/-- Live-restricted denotation of a `RawState` under `liveMask`. -/
def denoteRaw {Val : Type} (liveMask : List Bool) (raw : RawState Val) (loc : LocalId) : Slot Val :=
  match liveMask[loc]? with
  | some isLive => normalizeSlotForMask isLive (raw.getSlot loc)
  | none => .dead 0

/-- Live-restricted denotation of a `CanonState` under `liveMask`. -/
def denoteCanon {Val : Type} (liveMask : List Bool) (st : CanonState Val) (loc : LocalId) : Slot Val :=
  match liveMask[loc]? with
  | some isLive => normalizeSlotForMask isLive (st.getSlot loc)
  | none => .dead 0

/-- Two `RawState`s are live-equivalent at `liveMask` when every in-bounds local `i` has
    (1) the **identical slot** (value, generation, borrow flag, loan) when `liveMask[i] = true`,
    and (2) the **identical borrow-dirtied post-generation** `nextGenOnEnd` when
    `liveMask[i] = false` — values, initialization status and write history of dead locals are
    ignored. (Stated semantically, independently of `normalizeSlotForMask`/`canonicalize`.) -/
def LiveEquiv {Val : Type} (liveMask : List Bool) (raw₁ raw₂ : RawState Val) : Prop :=
  ∀ i isLive, liveMask[i]? = some isLive →
    (isLive = true → raw₁.getSlot i = raw₂.getSlot i) ∧
      (isLive = false → (raw₁.getSlot i).nextGenOnEnd = (raw₂.getSlot i).nextGenOnEnd)

/-- Normalized slots agree iff they agree as live slots (live) or agree on their
    borrow-dirtied post-generation (dead). -/
theorem normalizeSlotForMask_eq_iff {Val : Type} (isLive : Bool) (s₁ s₂ : Slot Val) :
    normalizeSlotForMask isLive s₁ = normalizeSlotForMask isLive s₂ ↔
      ((isLive = true → s₁ = s₂) ∧
        (isLive = false → s₁.nextGenOnEnd = s₂.nextGenOnEnd)) := by
  cases isLive with
  | true =>
    constructor
    · intro h
      exact ⟨(fun _ => h), (fun h' => by cases h')⟩
    · intro h
      exact h.1 rfl
  | false =>
    constructor
    · intro h
      refine ⟨(fun h' => by cases h'), (fun _ => ?_)⟩
      have h' : Slot.dead s₁.nextGenOnEnd = Slot.dead s₂.nextGenOnEnd := h
      injection h'
    · intro h
      show Slot.dead s₁.nextGenOnEnd = Slot.dead s₂.nextGenOnEnd
      rw [h.2 rfl]

theorem buildCanonSlotsAux_length {Val : Type} (lookup : LocalId → Slot Val) :
    ∀ (mask : List Bool) (offset : Nat),
      (buildCanonSlotsAux lookup offset mask).length = mask.length
  | [], _ => rfl
  | _ :: rest, offset => by
    dsimp [buildCanonSlotsAux]
    rw [buildCanonSlotsAux_length lookup rest (offset + 1)]

theorem getSlotAt_buildCanonSlotsAux {Val : Type} (lookup : LocalId → Slot Val) :
    ∀ (mask : List Bool) (offset idx : Nat) (isLive : Bool),
      mask[idx]? = some isLive →
      getSlotAt (buildCanonSlotsAux lookup offset mask) idx =
        normalizeSlotForMask isLive (lookup (offset + idx))
  | [], _, _, _, h => by simp at h
  | b :: rest, offset, 0, isLive, h => by
    simp at h
    subst h
    rfl
  | b :: rest, offset, idx + 1, isLive, h => by
    simp at h
    dsimp [buildCanonSlotsAux, getSlotAt]
    rw [getSlotAt_buildCanonSlotsAux lookup rest (offset + 1) idx isLive h]
    have hAdd : offset + 1 + idx = offset + (idx + 1) := by omega
    rw [hAdd]

theorem getSlot_canonicalize {Val : Type} (liveMask : List Bool) (raw : RawState Val)
    {loc : LocalId} {isLive : Bool} (hMask : liveMask[loc]? = some isLive) :
    (canonicalize liveMask raw).getSlot loc =
      normalizeSlotForMask isLive (raw.getSlot loc) := by
  dsimp [canonicalize, CanonState.getSlot]
  rw [getSlotAt_buildCanonSlotsAux raw.getSlot liveMask 0 loc isLive hMask]
  rw [Nat.zero_add]

/-- **Canonical Denotation Soundness (`denoteCanon_canonicalize`)**:
    Canonicalizing `raw` under `liveMask` preserves its exact live-restricted denotation
    at every local variable `loc : LocalId`. -/
theorem denoteCanon_canonicalize {Val : Type} (liveMask : List Bool) (raw : RawState Val)
    (loc : LocalId) :
    denoteCanon liveMask (canonicalize liveMask raw) loc =
      denoteRaw liveMask raw loc := by
  dsimp [denoteCanon, denoteRaw]
  cases hMask : liveMask[loc]? with
  | none => rfl
  | some isLive =>
    rw [getSlot_canonicalize liveMask raw hMask]
    exact normalizeSlotForMask_idempotent isLive (raw.getSlot loc)

theorem buildCanonSlotsAux_congr {Val : Type} (f₁ f₂ : LocalId → Slot Val) :
    ∀ (mask : List Bool) (offset : Nat),
      (∀ i isLive, mask[i]? = some isLive →
        normalizeSlotForMask isLive (f₁ (offset + i)) =
          normalizeSlotForMask isLive (f₂ (offset + i))) →
      buildCanonSlotsAux f₁ offset mask = buildCanonSlotsAux f₂ offset mask
  | [], _, _ => rfl
  | isLive :: rest, offset, hEq => by
    dsimp [buildCanonSlotsAux]
    have hHead : normalizeSlotForMask isLive (f₁ offset) =
        normalizeSlotForMask isLive (f₂ offset) := by
      have h0 := hEq 0 isLive rfl
      rw [Nat.add_zero] at h0
      exact h0
    rw [hHead]
    congr 1
    apply buildCanonSlotsAux_congr f₁ f₂ rest (offset + 1)
    intro i b hRest
    have hSucc := hEq (i + 1) b hRest
    have hAdd : offset + 1 + i = offset + (i + 1) := by omega
    rw [hAdd]
    exact hSucc

/-- **Canonicalization Idempotence (`canonicalize_idempotent`)**:
    Re-canonicalizing an already-canonicalized state under `liveMask` is a no-op. -/
theorem canonicalize_idempotent {Val : Type} (liveMask : List Bool) (raw : RawState Val) :
    canonicalizeCanon liveMask (canonicalize liveMask raw) =
      canonicalize liveMask raw := by
  dsimp [canonicalizeCanon, canonicalize]
  congr 1
  apply buildCanonSlotsAux_congr _ raw.getSlot liveMask 0
  intro i isLive hMask
  rw [Nat.zero_add]
  change normalizeSlotForMask isLive ((canonicalize liveMask raw).getSlot i) =
    normalizeSlotForMask isLive (raw.getSlot i)
  rw [getSlot_canonicalize liveMask raw hMask]
  exact normalizeSlotForMask_idempotent isLive (raw.getSlot i)

/-- **Canonical Completeness & Soundness (`canonicalize_eq_iff_live_equiv`)**:
    Two `RawState`s canonicalize to the **exact same syntactic `CanonState`** if and only
    if they are `LiveEquiv` under `liveMask`. -/
theorem canonicalize_eq_of_live_equiv {Val : Type} {liveMask : List Bool}
    {raw₁ raw₂ : RawState Val} (hEquiv : LiveEquiv liveMask raw₁ raw₂) :
    canonicalize liveMask raw₁ = canonicalize liveMask raw₂ := by
  dsimp [canonicalize]
  congr 1
  apply buildCanonSlotsAux_congr raw₁.getSlot raw₂.getSlot liveMask 0
  intro i isLive hMask
  rw [Nat.zero_add]
  exact (normalizeSlotForMask_eq_iff isLive _ _).2 (hEquiv i isLive hMask)

theorem live_equiv_of_canonicalize_eq {Val : Type} {liveMask : List Bool}
    {raw₁ raw₂ : RawState Val}
    (hEq : canonicalize liveMask raw₁ = canonicalize liveMask raw₂) :
    LiveEquiv liveMask raw₁ raw₂ := by
  intro i isLive hMask
  refine (normalizeSlotForMask_eq_iff isLive _ _).1 ?_
  have h1 := getSlot_canonicalize liveMask raw₁ hMask
  have h2 := getSlot_canonicalize liveMask raw₂ hMask
  rw [hEq] at h1
  rw [← h1, ← h2]

theorem canonicalize_eq_iff_live_equiv {Val : Type} (liveMask : List Bool)
    (raw₁ raw₂ : RawState Val) :
    canonicalize liveMask raw₁ = canonicalize liveMask raw₂ ↔
      LiveEquiv liveMask raw₁ raw₂ :=
  ⟨live_equiv_of_canonicalize_eq, canonicalize_eq_of_live_equiv⟩


/-!
### 2.1 Negative Theorem: Asymmetric Diamond Branches Defeat Raw State Syntactic Join
-/

/-- Initial raw state for a 3-local MIR body (`_0` return, `_1` live accum, `_2` branch-local temp):
    `_0` and `_1` start `.live 10 0 false none`, `_2` starts `.dead 0`. -/
def diamondRawInit : RawState Nat :=
  ((({ numLocals := 3, writeLog := [] } : RawState Nat).assign 0 10).assign 1 20)

/-- Left diamond branch: writes `_0 := 100`, then `_1 := 200`, and uses temporary `_2`
    (`StorageLive(_2); _2 := 999; StorageDead(_2)`). -/
def rawAfterLeft : RawState Nat :=
  let st₁ := (diamondRawInit.assign 0 100).assign 1 200
  (((st₁.storageLive 2).assign 2 999).storageDead 2)

/-- Right diamond branch: writes `_1 := 200` first, then `_0 := 100`, without touching `_2`. -/
def rawAfterRight : RawState Nat :=
  (diamondRawInit.assign 1 200).assign 0 100

/-- Join-point liveness mask at the diamond merge: `_0` and `_1` are live, `_2` is dead. -/
def diamondLiveMask : List Bool := [true, true, false]

/-- **Negative Theorem (`raw_asymmetric_diamond_Syntactic_ne_yet_canon_eq`)**:
    Asymmetric `if/else` diamond branches (out-of-order writes to live locals `_0, _1`
    plus a branch-local unborrowed temporary `_2` in the left branch) produce:
    1. Syntactically **distinct** raw states (`rawAfterLeft ≠ rawAfterRight`), which
       defeats any join cache or structural equality check on raw history-dependent states,
    2. Yet **identical** live-restricted denotations (`denoteRaw diamondLiveMask rawAfterLeft =
       denoteRaw diamondLiveMask rawAfterRight`), and
    3. Syntactically **identical** canonical states (`canonicalize diamondLiveMask rawAfterLeft =
       canonicalize diamondLiveMask rawAfterRight`)! -/
theorem raw_asymmetric_diamond_syntactic_ne_yet_canon_eq :
    rawAfterLeft ≠ rawAfterRight ∧
      (∀ loc, denoteRaw diamondLiveMask rawAfterLeft loc =
        denoteRaw diamondLiveMask rawAfterRight loc) ∧
      canonicalize diamondLiveMask rawAfterLeft =
        canonicalize diamondLiveMask rawAfterRight := by
  refine ⟨by decide, ?_, rfl⟩
  · intro loc
    rw [← denoteCanon_canonicalize diamondLiveMask rawAfterLeft loc]
    rw [← denoteCanon_canonicalize diamondLiveMask rawAfterRight loc]
    rfl

/-- Strengthened negative witness: the two raw states are **observationally identical on every
    local** (including the dead temporary `_2` and all out-of-range locals) — the
    `rawAfterLeft ≠ rawAfterRight` failure is purely syntactic write-history. -/
theorem raw_asymmetric_diamond_pointwise_eq (loc : LocalId) :
    rawAfterLeft.getSlot loc = rawAfterRight.getSlot loc := by
  rcases loc with _ | _ | _ | n <;> rfl

/-- All three diamond raw states (`diamondRawInit`, `rawAfterLeft`, `rawAfterRight`) satisfy
    `RawState.WF` (`loc < numLocals = 3` for every entry in `writeLog`). -/
theorem diamondRawStates_wf :
    diamondRawInit.WF ∧ rawAfterLeft.WF ∧ rawAfterRight.WF := by
  dsimp [diamondRawInit, rawAfterLeft, rawAfterRight, RawState.WF, RawWriteLogWF,
    RawState.assign, RawState.storageLive, RawState.storageDead, RawState.putSlot]
  repeat first | refine ⟨?_, ?_⟩ | decide | trivial


/-!
### 2.2 CPS Spine Forcing (`forceList`, `forceCanonState`)
-/

/-- Continuation-passing **spine** evaluator (`c19b8fce8` `forceList`): pattern-matches every
    cons cell of the list before invoking continuation `k` on the reconstructed spine
    (elements are passed through untouched; see `forceSlotsAux` for element forcing). -/
def forceListAux {α β : Type} : List α → (List α → β) → β
  | [], k => k []
  | x :: xs, k =>
    forceListAux xs (fun xs' => k (x :: xs'))

def forceList {α : Type} (xs : List α) : List α :=
  forceListAux xs (fun ys => ys)

/-- CPS constructor forcing of a single slot: matches the slot's head constructor (and
    re-binds its fields) before invoking `k`, so `k` never receives a pending slot thunk. -/
def forceSlot {Val β : Type} (s : Slot Val) (k : Slot Val → β) : β :=
  match s with
  | .dead g => k (.dead g)
  | .uninit g => k (.uninit g)
  | .live v g b loan => k (.live v g b loan)

/-- Spine **and element** CPS forcing of a slot list (`c19b8fce8` `forceLocals` analogue):
    every cons cell and every slot's head constructor is matched before `k` runs on the
    reconstructed list, so no `setSlotAt` / `buildCanonSlotsAux` redex survives into `k`. -/
def forceSlotsAux {Val β : Type} : List (Slot Val) → (List (Slot Val) → β) → β
  | [], k => k []
  | s :: rest, k => forceSlot s (fun s' => forceSlotsAux rest (fun rest' => k (s' :: rest')))

/-- Force the slot spine and every slot constructor of a `CanonState` before invoking `k`.
    Applied by `symEvalCfgGvn` at every block boundary and by `mergeJoinStates` after every
    join. (With closed `SymId` payloads the symbolic states never contain free variables, so
    this is defence-in-depth against the `hasFVar` WHNF-cache bypass rather than a
    load-bearing optimization in this prototype.) -/
def forceCanonState {Val β : Type} (st : CanonState Val) (k : CanonState Val → β) : β :=
  forceSlotsAux st.slots (fun slots' => k { slots := slots' })

/-- **CPS Spine-Forcing Equivalence (`forceListAux_eq`)**:
    `forceListAux xs k` is propositionally equal to `k xs` for every list `xs` and
    continuation `k`. -/
theorem forceListAux_eq {α β : Type} :
    ∀ (xs : List α) (k : List α → β),
      forceListAux xs k = k xs
  | [], _ => rfl
  | x :: xs, k => by
    dsimp [forceListAux]
    rw [forceListAux_eq xs (fun xs' => k (x :: xs'))]

theorem forceList_eq {α : Type} (xs : List α) :
    forceList xs = xs :=
  forceListAux_eq xs (fun ys => ys)

theorem forceSlot_eq {Val β : Type} (s : Slot Val) (k : Slot Val → β) :
    forceSlot s k = k s := by
  cases s <;> rfl

theorem forceSlotsAux_eq {Val β : Type} :
    ∀ (ss : List (Slot Val)) (k : List (Slot Val) → β), forceSlotsAux ss k = k ss
  | [], _ => rfl
  | s :: rest, k => by
    dsimp only [forceSlotsAux]
    rw [forceSlot_eq]
    exact forceSlotsAux_eq rest (fun rest' => k (s :: rest'))

theorem forceCanonState_eq {Val β : Type} (st : CanonState Val) (k : CanonState Val → β) :
    forceCanonState st k = k st := by
  dsimp [forceCanonState]
  rw [forceSlotsAux_eq st.slots (fun slots' => k { slots := slots' })]


/-!
## Section 3 — Compositional Join-Point Cut (`mergeJoinStates`, `wpJoinBlock_sound`, `wpCfgSymGvn_sound`)
-/

/-- Evaluate a symbolic `Slot SymId` to a concrete `Slot Nat` under `tbl` and `env`. -/
def evalSymSlot (tbl : SymTable) (env : SymEnv) : Slot SymId → Slot Nat
  | .dead g => .dead g
  | .uninit g => .uninit g
  | .live symId g borrowed loan => .live (evalSymId tbl env symId) g borrowed loan

/-- Evaluate a symbolic `CanonState SymId` to a concrete `CanonState Nat`. -/
def evalSymCanonState (tbl : SymTable) (env : SymEnv) (st : CanonState SymId) : CanonState Nat :=
  { slots := st.slots.map (evalSymSlot tbl env) }

theorem getSlotAt_map_evalSymSlot (tbl : SymTable) (env : SymEnv) :
    ∀ (slots : List (Slot SymId)) (loc : LocalId),
      getSlotAt (slots.map (evalSymSlot tbl env)) loc =
        evalSymSlot tbl env (getSlotAt slots loc)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, loc + 1 => getSlotAt_map_evalSymSlot tbl env xs loc

theorem evalSymCanonState_getSlot (tbl : SymTable) (env : SymEnv)
    (st : CanonState SymId) (loc : LocalId) :
    (evalSymCanonState tbl env st).getSlot loc =
      evalSymSlot tbl env (st.getSlot loc) :=
  getSlotAt_map_evalSymSlot tbl env st.slots loc

/-- Well-formedness of a symbolic `Slot SymId` at `SymTable` bound `bound`. -/
def ValidSymSlot (bound : Nat) : Slot SymId → Prop
  | .dead _ => True
  | .uninit _ => True
  | .live symId _ _ _ => symId < bound

theorem ValidSymSlot.mono {b₁ b₂ : Nat} {s : Slot SymId}
    (h : ValidSymSlot b₁ s) (hle : b₁ ≤ b₂) : ValidSymSlot b₂ s := by
  cases s with
  | dead _ => trivial
  | uninit _ => trivial
  | live symId _ _ _ => exact Nat.lt_of_lt_of_le h hle

theorem evalSymSlot_mono {tbl₁ tbl₂ : SymTable} (hValid : ValidTable tbl₁)
    (hExt : tbl₁.Extends tbl₂) (env : SymEnv) {s : Slot SymId}
    (hSlot : ValidSymSlot tbl₁.nodes.length s) :
    evalSymSlot tbl₁ env s = evalSymSlot tbl₂ env s := by
  cases s with
  | dead g => rfl
  | uninit g => rfl
  | live symId g b loan =>
    dsimp [evalSymSlot]
    rw [evalSymId_mono hValid hExt env hSlot]

/-- Merge two canonical symbolic slots `(sT, sF)` under branch condition `condId` in `tbl`.
    Returns `some (mergedSlot, tbl')` when the slot shapes/generations/loans agree at the
    join point (the canonical live-pruned invariant), interning `.ite condId idT idF`
    (which automatically folds `ite condId id id ↦ id` without allocating a node when
    both branches hold the same `SymId`). -/
def mergeJoinSlot (tbl : SymTable) (condId : Nat) (sT sF : Slot SymId) :
    Option (Slot SymId × SymTable) :=
  match sT, sF with
  | .dead gT, .dead gF =>
    if gT == gF then some (.dead gT, tbl) else none
  | .uninit gT, .uninit gF =>
    if gT == gF then some (.uninit gT, tbl) else none
  | .live idT gT bT loanT, .live idF gF bF loanF =>
    if gT == gF && bT == bF && decide (loanT = loanF) then
      let (mergedId, tbl') := internNode tbl (.ite condId idT idF)
      some (.live mergedId gT bT loanT, tbl')
    else
      none
  | _, _ => none

theorem mergeJoinSlot_spec {tbl : SymTable} {condId : Nat} {sT sF sM : Slot SymId}
    {tbl' : SymTable}
    (hValid : ValidTable tbl)
    (hCond : condId < tbl.nodes.length)
    (hValidT : ValidSymSlot tbl.nodes.length sT)
    (hValidF : ValidSymSlot tbl.nodes.length sF)
    (hMerge : mergeJoinSlot tbl condId sT sF = some (sM, tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      ValidSymSlot tbl'.nodes.length sM ∧
      ∀ env : SymEnv,
        evalSymSlot tbl' env sM =
          (if evalSymId tbl env condId != 0 then
            evalSymSlot tbl env sT
          else
            evalSymSlot tbl env sF) := by
  cases sT with
  | dead gT =>
    cases sF with
    | dead gF =>
      dsimp [mergeJoinSlot] at hMerge
      split at hMerge
      · rename_i hEq
        injection hMerge with hPair
        injection hPair with hSM hTbl
        subst hSM hTbl
        have hg : gT = gF := of_decide_eq_true hEq
        subst hg
        refine ⟨hValid, SymTable.Extends.refl tbl, trivial, ?_⟩
        intro env
        cases (evalSymId tbl env condId != 0) <;> rfl
      · cases hMerge
    | uninit _ => cases hMerge
    | live _ _ _ _ => cases hMerge
  | uninit gT =>
    cases sF with
    | dead _ => cases hMerge
    | uninit gF =>
      dsimp [mergeJoinSlot] at hMerge
      split at hMerge
      · rename_i hEq
        injection hMerge with hPair
        injection hPair with hSM hTbl
        subst hSM hTbl
        have hg : gT = gF := of_decide_eq_true hEq
        subst hg
        refine ⟨hValid, SymTable.Extends.refl tbl, trivial, ?_⟩
        intro env
        cases (evalSymId tbl env condId != 0) <;> rfl
      · cases hMerge
    | live _ _ _ _ => cases hMerge
  | live idT gT bT loanT =>
    cases sF with
    | dead _ => cases hMerge
    | uninit _ => cases hMerge
    | live idF gF bF loanF =>
      dsimp [mergeJoinSlot] at hMerge
      split at hMerge
      · rename_i hEqAll
        simp [Bool.and_eq_true] at hEqAll
        rcases hEqAll with ⟨⟨hg, hb⟩, hloan⟩
        subst hg hb hloan
        injection hMerge with hPair
        injection hPair with hSM hTbl
        subst hSM hTbl
        have hIteValid : ValidNode tbl.nodes.length (.ite condId idT idF) :=
          ⟨hCond, hValidT, hValidF⟩
        have hIntValid := internNode_valid hValid hIteValid
        have hIntExt := internNode_extends tbl (.ite condId idT idF)
        refine ⟨hIntValid.1, hIntExt, hIntValid.2, ?_⟩
        intro env
        dsimp [evalSymSlot]
        have hIntEval := internNode_eval hValid hIteValid env
        rw [hIntEval]
        dsimp [evalSymNodeWith]
        cases (evalSymId tbl env condId != 0) <;> rfl
      · cases hMerge

/-- Merge two lists of canonical symbolic slots pointwise in `tbl`. -/
def mergeJoinSlots (tbl : SymTable) (condId : Nat) :
    List (Slot SymId) → List (Slot SymId) → Option (List (Slot SymId) × SymTable)
  | [], [] => some ([], tbl)
  | sT :: restT, sF :: restF =>
    match mergeJoinSlot tbl condId sT sF with
    | none => none
    | some (sM, tbl₁) =>
      match mergeJoinSlots tbl₁ condId restT restF with
      | none => none
      | some (restM, tbl₂) => some (sM :: restM, tbl₂)
  | _, _ => none

/-- Merge two canonical symbolic states `(stT, stF)` under branch condition `condId`
    and apply CPS spine forcing (`forceCanonState`) to the merged state. -/
def mergeJoinStates (tbl : SymTable) (condId : Nat)
    (stT stF : CanonState SymId) : Option (CanonState SymId × SymTable) :=
  match mergeJoinSlots tbl condId stT.slots stF.slots with
  | none => none
  | some (slotsM, tbl') =>
    forceCanonState { slots := slotsM } (fun forced => some (forced, tbl'))

/-- Pointwise validity of a list of symbolic slots at `SymTable` bound `bound`. -/
def ValidSymSlots (bound : Nat) : List (Slot SymId) → Prop
  | [] => True
  | s :: rest => ValidSymSlot bound s ∧ ValidSymSlots bound rest

theorem ValidSymSlots.mono {b₁ b₂ : Nat} :
    ∀ {slots : List (Slot SymId)}, ValidSymSlots b₁ slots → b₁ ≤ b₂ → ValidSymSlots b₂ slots
  | [], _, _ => trivial
  | _ :: _, ⟨hHead, hTail⟩, hle =>
    ⟨hHead.mono hle, ValidSymSlots.mono hTail hle⟩

theorem map_evalSymSlot_mono {tbl₁ tbl₂ : SymTable} (hValid : ValidTable tbl₁)
    (hExt : tbl₁.Extends tbl₂) (env : SymEnv) :
    ∀ {slots : List (Slot SymId)},
      ValidSymSlots tbl₁.nodes.length slots →
      slots.map (evalSymSlot tbl₁ env) = slots.map (evalSymSlot tbl₂ env)
  | [], _ => rfl
  | s :: rest, ⟨hHead, hTail⟩ => by
    simp only [List.map_cons]
    rw [evalSymSlot_mono hValid hExt env hHead]
    rw [map_evalSymSlot_mono hValid hExt env hTail]

/-- Well-formedness of a symbolic `CanonState SymId` at `SymTable` bound `bound`. -/
def ValidSymCanonState (bound : Nat) (st : CanonState SymId) : Prop :=
  ValidSymSlots bound st.slots

theorem evalSymCanonState_mono {tbl₁ tbl₂ : SymTable} (hValid : ValidTable tbl₁)
    (hExt : tbl₁.Extends tbl₂) (env : SymEnv) {st : CanonState SymId}
    (hSt : ValidSymCanonState tbl₁.nodes.length st) :
    evalSymCanonState tbl₁ env st = evalSymCanonState tbl₂ env st := by
  dsimp [evalSymCanonState]
  rw [map_evalSymSlot_mono hValid hExt env hSt]

theorem mergeJoinSlots_spec {condId : Nat} :
    ∀ (slotsT slotsF : List (Slot SymId)) (tbl : SymTable)
      (slotsM : List (Slot SymId)) (tbl' : SymTable),
      ValidTable tbl →
      condId < tbl.nodes.length →
      ValidSymSlots tbl.nodes.length slotsT →
      ValidSymSlots tbl.nodes.length slotsF →
      mergeJoinSlots tbl condId slotsT slotsF = some (slotsM, tbl') →
      ValidTable tbl' ∧
        tbl.Extends tbl' ∧
        ValidSymSlots tbl'.nodes.length slotsM ∧
        ∀ env : SymEnv,
          slotsM.map (evalSymSlot tbl' env) =
            (if evalSymId tbl env condId != 0 then
              slotsT.map (evalSymSlot tbl env)
            else
              slotsF.map (evalSymSlot tbl env))
  | [], [], tbl, slotsM, tbl', hValid, _, _, _, hMerge => by
    injection hMerge with hPair
    injection hPair with hS hT
    subst hS hT
    refine ⟨hValid, SymTable.Extends.refl tbl, trivial, ?_⟩
    intro env
    cases (evalSymId tbl env condId != 0) <;> rfl
  | [], _ :: _, _, _, _, _, _, _, _, hMerge => by cases hMerge
  | _ :: _, [], _, _, _, _, _, _, _, hMerge => by cases hMerge
  | sT :: restT, sF :: restF, tbl, slotsM, tbl', hValid, hCond,
    ⟨hHeadT, hTailT⟩, ⟨hHeadF, hTailF⟩, hMerge => by
    dsimp [mergeJoinSlots] at hMerge
    cases hStep₁ : mergeJoinSlot tbl condId sT sF with
    | none =>
      rw [hStep₁] at hMerge
      cases hMerge
    | some pair₁ =>
      rcases pair₁ with ⟨sM, tbl₁⟩
      rw [hStep₁] at hMerge
      dsimp at hMerge
      have hSpec₁ := mergeJoinSlot_spec hValid hCond hHeadT hHeadF hStep₁
      rcases hSpec₁ with ⟨hValid₁, hExt₁, hValidSM, hEvalSM⟩
      have hLenLe₁ : tbl.nodes.length ≤ tbl₁.nodes.length := hExt₁.length_le
      have hCond₁ : condId < tbl₁.nodes.length := Nat.lt_of_lt_of_le hCond hLenLe₁
      have hTailT₁ : ValidSymSlots tbl₁.nodes.length restT := hTailT.mono hLenLe₁
      have hTailF₁ : ValidSymSlots tbl₁.nodes.length restF := hTailF.mono hLenLe₁
      cases hStep₂ : mergeJoinSlots tbl₁ condId restT restF with
      | none =>
        rw [hStep₂] at hMerge
        cases hMerge
      | some pair₂ =>
        rcases pair₂ with ⟨restM, tbl₂⟩
        rw [hStep₂] at hMerge
        dsimp at hMerge
        injection hMerge with hPair
        injection hPair with hSM hTbl
        subst hSM hTbl
        have hSpec₂ := mergeJoinSlots_spec restT restF tbl₁ restM tbl₂
          hValid₁ hCond₁ hTailT₁ hTailF₁ hStep₂
        rcases hSpec₂ with ⟨hValid₂, hExt₂, hValidRestM, hEvalRestM⟩
        have hLenLe₂ : tbl₁.nodes.length ≤ tbl₂.nodes.length := hExt₂.length_le
        refine ⟨hValid₂, hExt₁.trans hExt₂, ⟨hValidSM.mono hLenLe₂, hValidRestM⟩, ?_⟩
        intro env
        simp only [List.map_cons]
        rw [← evalSymSlot_mono hValid₁ hExt₂ env hValidSM]
        rw [hEvalSM env, hEvalRestM env]
        rw [← evalSymId_mono hValid hExt₁ env hCond]
        rw [← map_evalSymSlot_mono hValid hExt₁ env hTailT]
        rw [← map_evalSymSlot_mono hValid hExt₁ env hTailF]
        cases (evalSymId tbl env condId != 0) <;> rfl

/-- **Compositional Join-Point Merge Theorem (`mergeJoinStates_eval`)**:
    When two canonical symbolic post-states `(stT, stF)` merge under branch condition
    `condId` in `tbl` via `mergeJoinStates tbl condId stT stF = some (stM, tbl')`,
    `tbl'` is a valid monotone extension of `tbl` and evaluating the single merged
    state `stM` in `tbl'` under any concrete `env` equals `evalSymCanonState tbl env stT`
    when `evalSymId tbl env condId != 0` and `evalSymCanonState tbl env stF` otherwise! -/
theorem mergeJoinStates_eval {tbl : SymTable} {condId : Nat}
    {stT stF stM : CanonState SymId} {tbl' : SymTable}
    (hValid : ValidTable tbl)
    (hCond : condId < tbl.nodes.length)
    (hValidT : ValidSymCanonState tbl.nodes.length stT)
    (hValidF : ValidSymCanonState tbl.nodes.length stF)
    (hMerge : mergeJoinStates tbl condId stT stF = some (stM, tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      ValidSymCanonState tbl'.nodes.length stM ∧
      ∀ env : SymEnv,
        evalSymCanonState tbl' env stM =
          (if evalSymId tbl env condId != 0 then
            evalSymCanonState tbl env stT
          else
            evalSymCanonState tbl env stF) := by
  dsimp [mergeJoinStates] at hMerge
  cases hSlots : mergeJoinSlots tbl condId stT.slots stF.slots with
  | none =>
    rw [hSlots] at hMerge
    cases hMerge
  | some pair =>
    rcases pair with ⟨slotsM, tbl₁⟩
    rw [hSlots] at hMerge
    change forceCanonState { slots := slotsM } (fun forced => some (forced, tbl₁)) =
      some (stM, tbl') at hMerge
    rw [forceCanonState_eq] at hMerge
    injection hMerge with hPair
    injection hPair with hStM hTbl
    subst hStM hTbl
    have hSpec := mergeJoinSlots_spec stT.slots stF.slots tbl slotsM tbl₁
      hValid hCond hValidT hValidF hSlots
    rcases hSpec with ⟨hValid₁, hExt₁, hValidM, hEvalM⟩
    refine ⟨hValid₁, hExt₁, hValidM, ?_⟩
    intro env
    dsimp [evalSymCanonState]
    rw [hEvalM env]
    cases (evalSymId tbl env condId != 0) <;> rfl

/-- Identical slots merge to themselves without allocating any node (for any condition). -/
theorem mergeJoinSlot_self (tbl : SymTable) (condId : Nat) (s : Slot SymId) :
    mergeJoinSlot tbl condId s s = some (s, tbl) := by
  have hNat : ∀ n : Nat, (n == n) = true := fun n => decide_eq_true rfl
  cases s with
  | dead g =>
    dsimp only [mergeJoinSlot]
    rw [hNat g]
    rfl
  | uninit g =>
    dsimp only [mergeJoinSlot]
    rw [hNat g]
    rfl
  | live id g b loan =>
    dsimp only [mergeJoinSlot]
    have hb : (b == b) = true := decide_eq_true rfl
    have hl : decide (loan = loan) = true := decide_eq_true rfl
    rw [hNat g, hb, hl]
    dsimp only [internNode]
    rw [hNat id]
    rfl

theorem mergeJoinSlots_self (tbl : SymTable) (condId : Nat) :
    ∀ (ss : List (Slot SymId)), mergeJoinSlots tbl condId ss ss = some (ss, tbl)
  | [] => rfl
  | s :: rest => by
    dsimp only [mergeJoinSlots]
    rw [mergeJoinSlot_self]
    dsimp only
    rw [mergeJoinSlots_self tbl condId rest]

/-- **Join Sharing (`mergeJoinSlots_shared`)**: every slot position on which the two branch
    states agree is returned *unchanged* by the merge — the very same `SymId`, with no `ite`
    node allocated for it. -/
theorem mergeJoinSlots_shared {condId : Nat} :
    ∀ (slotsT slotsF : List (Slot SymId)) (tbl : SymTable) (slotsM : List (Slot SymId))
      (tbl' : SymTable),
      mergeJoinSlots tbl condId slotsT slotsF = some (slotsM, tbl') →
      ∀ i, getSlotAt slotsT i = getSlotAt slotsF i → getSlotAt slotsM i = getSlotAt slotsT i
  | [], [], tbl, slotsM, tbl', hMerge, i, _ => by
    injection hMerge with hPair
    injection hPair with hS _
    subst hS
    rfl
  | [], _ :: _, _, _, _, hMerge, _, _ => by cases hMerge
  | _ :: _, [], _, _, _, hMerge, _, _ => by cases hMerge
  | sT :: restT, sF :: restF, tbl, slotsM, tbl', hMerge, i, hEq => by
    dsimp only [mergeJoinSlots] at hMerge
    cases hStep₁ : mergeJoinSlot tbl condId sT sF with
    | none => rw [hStep₁] at hMerge; cases hMerge
    | some pair₁ =>
      rcases pair₁ with ⟨sM, tbl₁⟩
      rw [hStep₁] at hMerge
      dsimp only at hMerge
      cases hStep₂ : mergeJoinSlots tbl₁ condId restT restF with
      | none => rw [hStep₂] at hMerge; cases hMerge
      | some pair₂ =>
        rcases pair₂ with ⟨restM, tbl₂⟩
        rw [hStep₂] at hMerge
        dsimp only at hMerge
        injection hMerge with hPair
        injection hPair with hS _
        subst hS
        cases i with
        | zero =>
          have hEq' : sT = sF := hEq
          subst hEq'
          rw [mergeJoinSlot_self] at hStep₁
          injection hStep₁ with h
          injection h with h1 _
          subst h1
          rfl
        | succ j =>
          exact mergeJoinSlots_shared restT restF tbl₁ restM tbl₂ hStep₂ j hEq

/-- State-level join sharing: locals identical in both branch states stay shared verbatim. -/
theorem mergeJoinStates_shared {tbl : SymTable} {condId : Nat} {stT stF stM : CanonState SymId}
    {tbl' : SymTable} (hMerge : mergeJoinStates tbl condId stT stF = some (stM, tbl'))
    (loc : LocalId) (hEq : stT.getSlot loc = stF.getSlot loc) :
    stM.getSlot loc = stT.getSlot loc := by
  dsimp only [mergeJoinStates] at hMerge
  cases hSlots : mergeJoinSlots tbl condId stT.slots stF.slots with
  | none => rw [hSlots] at hMerge; cases hMerge
  | some pair =>
    rcases pair with ⟨slotsM, tbl₁⟩
    rw [hSlots] at hMerge
    dsimp only at hMerge
    rw [forceCanonState_eq] at hMerge
    injection hMerge with hPair
    injection hPair with hStM _
    subst hStM
    exact mergeJoinSlots_shared stT.slots stF.slots tbl slotsM tbl₁ hSlots loc hEq

/-- Merging a state with itself is the identity and allocates nothing. -/
theorem mergeJoinStates_self (tbl : SymTable) (condId : Nat) (st : CanonState SymId) :
    mergeJoinStates tbl condId st st = some (st, tbl) := by
  dsimp only [mergeJoinStates]
  rw [mergeJoinSlots_self]
  dsimp only
  rw [forceCanonState_eq]

/-!
### 3.2 First-Order MIR CFG Syntax & Mask-Free Concrete Semantics (`execCfg`)

**Trust boundary.** The concrete operational semantics `execCfg` below is the plain
multi-block MIR semantics (`goto` / `switchInt` / `ret` / `unreachable`) over the *unpruned*
dense local state: it never consults liveness masks or join points. Join-point liveness masks
are *untrusted hints* (`JoinHints`) consumed only by the symbolic evaluator `symEvalCfgGvn`;
every soundness theorem below quantifies over **all** hints, so a wrong (too-aggressive) mask
can only make symbolic verification *fail*, never make it unsound.
-/

/-- Basic block identifier in a MIR CFG. -/
abbrev BlockId := Nat

/-- First-order MIR right-hand-side expression (`MirRvalue`). -/
inductive MirRvalue where
  | const (val : Nat)
  | use (src : LocalId)
  | op1 (op : SymOp1) (src : LocalId)
  | op2 (op : SymOp2) (lhs rhs : LocalId)
  | derefRef (ptr : LocalId)

/-- First-order MIR statement (`MirStmt`) covering scalar assignment, storage lifecycle
    (`storageLive` / `storageDead`), assertions (`assert`), borrow creation (`retagBorrow`,
    which marks `target` as `borrowed = true` and records `(target, gen)` in `dst`'s
    `loanTarget`), and indirect write-through-reference (`storeRef ptr rv`, i.e., `*ptr := rv`,
    which checks temporal borrow-generation validity `curGen == expGen` and updates the
    aliased referent `target` in place; the write bumps the referent's generation, which
    invalidates every *other* outstanding loan, and re-validates the writer's own loan). -/
inductive MirStmt where
  | assign (dst : LocalId) (rv : MirRvalue)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | assert (cond : LocalId)
  | retagBorrow (dst target : LocalId)
  | storeRef (ptr : LocalId) (rv : MirRvalue)

/-- First-order MIR block terminator (`MirTerm`). A *diamond* is an ordinary
    `switchInt discr thenBb elseBb` whose two arm blocks both end in `goto joinBb`. -/
inductive MirTerm where
  | goto (target : BlockId)
  | switchInt (discr : LocalId) (thenBb elseBb : BlockId)
  | ret (retLoc : LocalId)
  | unreachable

/-- A basic block in the MIR CFG. -/
structure MirBlock where
  stmts : List MirStmt := []
  term : MirTerm := .unreachable

/-- A MIR Control-Flow Graph indexed by `BlockId`. -/
structure MirCfg where
  blocks : List MirBlock := []

/-- Untrusted join-point liveness hints: `hints j = some mask` asks the symbolic evaluator to
    merge diamonds joining at block `j` after pruning every local `i` with `mask[i] = false`
    (`hints j = none` makes it path-split instead). The concrete semantics never reads hints. -/
abbrev JoinHints := BlockId → Option (List Bool)

/-- Concrete execution outcome of a MIR CFG:
    - `.ret val`: normal return with concrete `u64` value `val`.
    - `.fault`: UB / assertion failure / read of a dead-or-uninitialized local / write to a
      dead (`StorageDead`) or undeclared local / dangling-borrow generation mismatch /
      `unreachable` / missing block.
    - `.outOfFuel`: step fuel exhausted. -/
inductive ExecOutcome where
  | ret (val : Nat)
  | fault
  | outOfFuel
  deriving DecidableEq

/-- Read a live concrete scalar from `st` at `loc`, returning `none` if the slot is dead,
    uninitialized, **or holds a loan**: a reference is not a scalar, and in this untyped slot model
    a pointer slot's value is only the snapshot of its referent taken at borrow time, so reading
    it as a scalar (`use`, `op1`/`op2`, `assert`, `switchInt`, `ret`) would expose stale data.
    References are consumed only through `derefRef` / `storeRef`. -/
def readConcreteScalar (st : CanonState Nat) (loc : LocalId) : Option Nat :=
  match st.getSlot loc with
  | .live v _ _ none => some v
  | _ => none

/-- Concrete evaluation of a `MirRvalue` in `st : CanonState Nat` (constants are reduced to
    `u64` words). `.derefRef ptr` checks that `ptr` holds an active `loanTarget = some (target,
    expGen)` AND that `target` is currently a scalar slot `.live targetVal curGen true none` with
    `curGen == expGen` (temporal borrow-generation check; dereferencing a reference-to-reference
    is rejected so an inner reference slot's borrow-time snapshot is never read as a scalar). -/
def evalConcreteRvalue (st : CanonState Nat) : MirRvalue → Option Nat
  | .const v => some (wrap64 v)
  | .use src => readConcreteScalar st src
  | .op1 op src =>
    match readConcreteScalar st src with
    | some v => some (evalSymOp1 op v)
    | none => none
  | .op2 op lhs rhs =>
    match readConcreteScalar st lhs, readConcreteScalar st rhs with
    | some a, some b => some (evalSymOp2 op a b)
    | _, _ => none
  | .derefRef ptr =>
    match st.getSlot ptr with
    | .live _ _ _ (some (target, expGen)) =>
      match st.getSlot target with
      | .live targetVal curGen true none =>
        if curGen == expGen then some targetVal else none
      | _ => none
    | _ => none

/-- Faulting slot write: assigning into a **dead** slot (`StorageDead`, never `StorageLive`d,
    or an undeclared / out-of-range local) is MIR UB and returns `none`; writing an `uninit`
    slot initializes it (`borrowed := false`). Overwriting an *unborrowed* `live` slot keeps its
    generation; overwriting a **borrowed** `live` slot through its owner invalidates every
    outstanding loan (Stacked Borrows pops, and Tree Borrows disables, all references derived
    from a parent that is written) by bumping the generation and clearing `borrowed`. -/
def Slot.writeVal? {Val : Type} (s : Slot Val) (v : Val)
    (loanTarget : Option (LocalId × Nat)) : Option (Slot Val) :=
  match s with
  | .dead _ => none
  | .uninit g => some (.live v g false loanTarget)
  | .live _ g false _ => some (.live v g false loanTarget)
  | .live _ g true _ => some (.live v (g + 1) false loanTarget)

/-- Owner-read transition on a slot: reading a local directly through its owner succeeds and
    preserves its value and `loanTarget`, but if the slot was currently borrowed (`borrowed =
    true`), the owner read invalidates outstanding loans to this slot by bumping its
    generation to `g + 1` and clearing `borrowed := false`. On unborrowed slots this is the
    identity.

    Aliasing discipline: every loan is treated as a **unique** (`&mut`) loan, as in Stacked
    Borrows, where a read through the parent pops all `Unique` items above it. This is stricter
    than Tree Borrows, where a foreign read merely *freezes* an `Active` loan (later reads through
    it stay legal) and leaves a `Reserved` one usable; the model is therefore sound but
    incomplete for programs that keep reading through a loan after an owner read, and for shared
    (`&`) borrows in general. Applied to every direct read of a local in `assign`, `storeRef`,
    `assert`, and the `switchInt` discriminant (a `ret` read ends execution, so it needs none). -/
def Slot.ownerRead {Val : Type} : Slot Val → Slot Val
  | .live v g true loan => .live v (g + 1) false loan
  | s => s

/-- Apply `Slot.ownerRead` to `loc` in `st`. -/
def CanonState.ownerReadLoc {Val : Type} (st : CanonState Val) (loc : LocalId) : CanonState Val :=
  st.setSlot loc (st.getSlot loc).ownerRead

/-- Apply `CanonState.ownerReadLoc` to all locals directly read by `rv`. -/
def CanonState.ownerReadRvalue {Val : Type} (st : CanonState Val) : MirRvalue → CanonState Val
  | .const _ => st
  | .use src => st.ownerReadLoc src
  | .op1 _ src => st.ownerReadLoc src
  | .op2 _ lhs rhs => (st.ownerReadLoc lhs).ownerReadLoc rhs
  | .derefRef ptr => st.ownerReadLoc ptr

/-- Re-validate the loan held by a pointer slot at generation `g` (used after a write through
    that pointer bumps its target's generation). Non-`live` slots are left unchanged. -/
def Slot.retarget {Val : Type} (target g : Nat) : Slot Val → Slot Val
  | .live pv pg pb _ => .live pv pg pb (some (target, g))
  | s => s

/-- Write-through-reference effect on the state: perform an owner read on `ptr` (invalidating
    any loan to the pointer variable `ptr` itself), set the referent `target` to its new value at
    the bumped generation `g`, then re-validate the writer `ptr`'s own loan at `g`. -/
def CanonState.storeThrough {Val : Type} (st : CanonState Val) (ptr target : LocalId)
    (v : Val) (g : Nat) (targetLoan : Option (LocalId × Nat)) : CanonState Val :=
  let st₁ := (st.ownerReadLoc ptr).setSlot target (.live v g true targetLoan)
  st₁.setSlot ptr ((st₁.getSlot ptr).retarget target g)

/-- Concrete execution of a single `MirStmt`. Returns `none` on any fault, including writes
    to dead locals, storage statements on undeclared locals, and uses of loans invalidated by
    earlier owner reads, owner writes, re-borrows of the same target, writes through another
    loan, or `StorageDead`. -/
def execStmt (st : CanonState Nat) : MirStmt → Option (CanonState Nat)
  | .assign dst rv =>
    match evalConcreteRvalue st rv with
    | none => none
    | some v =>
      let st₀ := st.ownerReadRvalue rv
      match (st₀.getSlot dst).writeVal? v none with
      | none => none
      | some s' => some (st₀.setSlot dst s')
  | .storageLive loc =>
    if loc < st.slots.length then some (st.setSlot loc (st.getSlot loc).reborn) else none
  | .storageDead loc =>
    if loc < st.slots.length then some (st.setSlot loc (st.getSlot loc).kill) else none
  | .assert cond =>
    match readConcreteScalar st cond with
    | some v => if v != 0 then some (st.ownerReadLoc cond) else none
    | none => none
  | .retagBorrow dst target =>
    match st.getSlot target with
    | .live targetVal g b targetLoan =>
      -- Unique-loan (Stacked Borrows `&mut`) discipline: re-borrowing an already-borrowed
      -- target invalidates every earlier loan to it (generation bump `g ↦ g + 1`); the new
      -- loan is issued at the resulting generation.
      let g' := if b then g + 1 else g
      match ((st.setSlot target (.live targetVal g' true targetLoan)).getSlot dst).writeVal?
          targetVal (some (target, g')) with
      | none => none
      | some s' => some ((st.setSlot target (.live targetVal g' true targetLoan)).setSlot dst s')
    | _ => none
  | .storeRef ptr rv =>
    match evalConcreteRvalue st rv with
    | none => none
    | some v =>
      let st₀ := st.ownerReadRvalue rv
      match st₀.getSlot ptr with
      | .live _ _ _ (some (target, expGen)) =>
        match st₀.getSlot target with
        | .live _ curGen true none =>
          if curGen == expGen then
            some (st₀.storeThrough ptr target v (curGen + 1) none)
          else
            none
        | _ => none
      | _ => none

/-- Concrete execution of a statement list. -/
def execStmts (st : CanonState Nat) : List MirStmt → Option (CanonState Nat)
  | [] => some st
  | stmt :: rest =>
    match execStmt st stmt with
    | some st' => execStmts st' rest
    | none => none

/-- Mask-free concrete operational semantics of a multi-block `MirCfg` with step fuel `fuel`
    (one unit per executed basic block). -/
def execCfg (cfg : MirCfg) : Nat → BlockId → CanonState Nat → ExecOutcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, bb, st =>
    match cfg.blocks[bb]? with
    | none => .fault
    | some blk =>
      match execStmts st blk.stmts with
      | none => .fault
      | some st₁ =>
        match blk.term with
        | .goto target => execCfg cfg fuel target st₁
        | .switchInt discr thenBb elseBb =>
          match readConcreteScalar st₁ discr with
          | none => .fault
          | some v =>
            -- Reading the discriminant is an owner read (invalidates loans to `discr`).
            let st₂ := st₁.ownerReadLoc discr
            if v != 0 then execCfg cfg fuel thenBb st₂ else execCfg cfg fuel elseBb st₂
        | .ret retLoc =>
          match readConcreteScalar st₁ retLoc with
          | some v => .ret v
          | none => .fault
        | .unreachable => .fault

/-- Commutativity of `setSlotAt` with `List.map`. -/
theorem map_setSlotAt {Val₁ Val₂ : Type} (f : Slot Val₁ → Slot Val₂) :
    ∀ (slots : List (Slot Val₁)) (loc : Nat) (s : Slot Val₁),
      (setSlotAt slots loc s).map f = setSlotAt (slots.map f) loc (f s)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, s => by
    simp only [setSlotAt, List.map_cons]
    rw [map_setSlotAt f xs i s]

theorem evalSymCanonState_setSlot (tbl : SymTable) (env : SymEnv)
    (st : CanonState SymId) (loc : LocalId) (s : Slot SymId) :
    evalSymCanonState tbl env (st.setSlot loc s) =
      (evalSymCanonState tbl env st).setSlot loc (evalSymSlot tbl env s) := by
  dsimp [evalSymCanonState, CanonState.setSlot]
  rw [map_setSlotAt]

theorem evalSymSlot_reborn (tbl : SymTable) (env : SymEnv) (s : Slot SymId) :
    evalSymSlot tbl env s.reborn = (evalSymSlot tbl env s).reborn := by
  cases s with
  | dead g => rfl
  | uninit g => rfl
  | live _ g b _ => cases b <;> rfl

theorem evalSymSlot_kill (tbl : SymTable) (env : SymEnv) (s : Slot SymId) :
    evalSymSlot tbl env s.kill = (evalSymSlot tbl env s).kill := by
  cases s with
  | dead g => rfl
  | uninit g => rfl
  | live _ g b _ => cases b <;> rfl

theorem evalSymSlot_writeVal (tbl : SymTable) (env : SymEnv) (s : Slot SymId)
    (symId : Nat) (loan : Option (LocalId × Nat)) :
    evalSymSlot tbl env (s.writeVal symId loan) =
      (evalSymSlot tbl env s).writeVal (evalSymId tbl env symId) loan := by
  cases s <;> rfl

theorem ValidSymSlots_getSlotAt {bound : Nat} :
    ∀ {slots : List (Slot SymId)} (loc : LocalId),
      ValidSymSlots bound slots →
      ValidSymSlot bound (getSlotAt slots loc)
  | [], _, _ => trivial
  | _ :: _, 0, ⟨hHead, _⟩ => hHead
  | _ :: _, loc + 1, ⟨_, hTail⟩ => ValidSymSlots_getSlotAt loc hTail

theorem ValidSymCanonState.getSlot {bound : Nat} {st : CanonState SymId}
    (hSt : ValidSymCanonState bound st) (loc : LocalId) :
    ValidSymSlot bound (st.getSlot loc) :=
  ValidSymSlots_getSlotAt loc hSt

theorem ValidSymSlots_setSlotAt {bound : Nat} :
    ∀ {slots : List (Slot SymId)} (loc : LocalId) {s : Slot SymId},
      ValidSymSlots bound slots →
      ValidSymSlot bound s →
      ValidSymSlots bound (setSlotAt slots loc s)
  | [], _, _, _, _ => trivial
  | _ :: _, 0, _, ⟨_, hTail⟩, hS => ⟨hS, hTail⟩
  | _ :: _, loc + 1, _, ⟨hHead, hTail⟩, hS =>
    ⟨hHead, ValidSymSlots_setSlotAt loc hTail hS⟩

theorem ValidSymCanonState.setSlot {bound : Nat} {st : CanonState SymId}
    {loc : LocalId} {s : Slot SymId}
    (hSt : ValidSymCanonState bound st) (hS : ValidSymSlot bound s) :
    ValidSymCanonState bound (st.setSlot loc s) :=
  ValidSymSlots_setSlotAt loc hSt hS

theorem map_buildCanonSlotsAux (tbl : SymTable) (env : SymEnv)
    (st : CanonState SymId) :
    ∀ (mask : List Bool) (offset : Nat),
      (buildCanonSlotsAux st.getSlot offset mask).map (evalSymSlot tbl env) =
        buildCanonSlotsAux (evalSymCanonState tbl env st).getSlot offset mask
  | [], _ => rfl
  | isLive :: restMask, offset => by
    simp only [buildCanonSlotsAux, List.map_cons]
    rw [map_buildCanonSlotsAux tbl env st restMask (offset + 1)]
    rw [evalSymCanonState_getSlot]
    cases isLive with
    | true => rfl
    | false =>
      dsimp [normalizeSlotForMask]
      rw [evalSymSlot_kill]

theorem evalSymCanonState_canonicalizeCanon (tbl : SymTable) (env : SymEnv)
    (liveMask : List Bool) (st : CanonState SymId) :
    evalSymCanonState tbl env (canonicalizeCanon liveMask st) =
      canonicalizeCanon liveMask (evalSymCanonState tbl env st) := by
  unfold canonicalizeCanon
  dsimp [evalSymCanonState]
  rw [map_buildCanonSlotsAux tbl env st liveMask 0]
  rfl

theorem ValidSymSlots_buildCanonSlotsAux {bound : Nat} {st : CanonState SymId}
    (hSt : ValidSymCanonState bound st) :
    ∀ (mask : List Bool) (offset : Nat),
      ValidSymSlots bound (buildCanonSlotsAux st.getSlot offset mask)
  | [], _ => trivial
  | isLive :: restMask, offset => by
    dsimp [buildCanonSlotsAux]
    refine ⟨?_, ValidSymSlots_buildCanonSlotsAux hSt restMask (offset + 1)⟩
    cases isLive with
    | true => exact hSt.getSlot offset
    | false => trivial

theorem ValidSymCanonState.canonicalizeCanon {bound : Nat} {st : CanonState SymId}
    (hSt : ValidSymCanonState bound st) (liveMask : List Bool) :
    ValidSymCanonState bound (canonicalizeCanon liveMask st) :=
  ValidSymSlots_buildCanonSlotsAux hSt liveMask 0

/-- Read a live symbolic `SymId` from `st` at `loc` (a slot holding a loan is not a scalar; see
    `readConcreteScalar`). -/
def readSymScalar (st : CanonState SymId) (loc : LocalId) : Option Nat :=
  match st.getSlot loc with
  | .live symId _ _ none => some symId
  | _ => none

theorem readSymScalar_spec {tbl : SymTable} {st : CanonState SymId} {loc : LocalId}
    (env : SymEnv) (hSt : ValidSymCanonState tbl.nodes.length st) :
    match readSymScalar st loc with
    | none => readConcreteScalar (evalSymCanonState tbl env st) loc = none
    | some symId =>
      symId < tbl.nodes.length ∧
        readConcreteScalar (evalSymCanonState tbl env st) loc =
          some (evalSymId tbl env symId) := by
  have hSlot := hSt.getSlot loc
  dsimp [readSymScalar, readConcreteScalar]
  rw [evalSymCanonState_getSlot]
  cases hGet : st.getSlot loc with
  | dead g => rfl
  | uninit g => rfl
  | live symId g b loan =>
    rw [hGet] at hSlot
    cases loan with
    | none => exact ⟨hSlot, rfl⟩
    | some _ => rfl

/-- Symbolic GVN evaluation of a `MirRvalue` in `(st, tbl)`.
    Interns constants and unary/binary expressions into `tbl`, and verifies borrow
    liveness and generation agreement `(curGen == expGen)` on `.derefRef ptr`. -/
def evalSymRvalue (st : CanonState SymId) (tbl : SymTable) :
    MirRvalue → Option (Nat × SymTable)
  | .const v => some (internNode tbl (.const v))
  | .use src =>
    match readSymScalar st src with
    | some symId => some (symId, tbl)
    | none => none
  | .op1 op src =>
    match readSymScalar st src with
    | some srcId => some (internNode tbl (.op1 op srcId))
    | none => none
  | .op2 op lhs rhs =>
    match readSymScalar st lhs, readSymScalar st rhs with
    | some lhsId, some rhsId => some (internNode tbl (.op2 op lhsId rhsId))
    | _, _ => none
  | .derefRef ptr =>
    match st.getSlot ptr with
    | .live _ _ _ (some (target, expGen)) =>
      match st.getSlot target with
      | .live targetSymId curGen true none =>
        if curGen == expGen then some (targetSymId, tbl) else none
      | _ => none
    | _ => none

theorem evalSymRvalue_sound {st : CanonState SymId} {tbl : SymTable}
    {rv : MirRvalue} {resId : Nat} {tbl' : SymTable}
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hEval : evalSymRvalue st tbl rv = some (resId, tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      resId < tbl'.nodes.length ∧
      ∀ env : SymEnv,
        evalConcreteRvalue (evalSymCanonState tbl env st) rv =
          some (evalSymId tbl' env resId) := by
  cases rv with
  | const v =>
    dsimp [evalSymRvalue] at hEval
    injection hEval with hPair
    have hId : resId = (internNode tbl (.const v)).1 := by rw [hPair]
    have hTbl : tbl' = (internNode tbl (.const v)).2 := by rw [hPair]
    subst hId hTbl
    have hNode : ValidNode tbl.nodes.length (.const v) := trivial
    have hV := internNode_valid hValid hNode
    have hE := internNode_extends tbl (.const v)
    refine ⟨hV.1, hE, hV.2, ?_⟩
    intro env
    dsimp [evalConcreteRvalue]
    have hEv := internNode_eval hValid hNode env
    rw [hEv]
    rfl
  | use src =>
    dsimp [evalSymRvalue] at hEval
    cases hRead : readSymScalar st src with
    | none =>
      rw [hRead] at hEval
      cases hEval
    | some symId =>
      rw [hRead] at hEval
      injection hEval with hPair
      injection hPair with hId hTbl
      subst hId hTbl
      refine ⟨hValid, SymTable.Extends.refl tbl, ?_, ?_⟩
      · have hSpec := readSymScalar_spec (fun _ => 0) hSt (loc := src)
        rw [hRead] at hSpec
        exact hSpec.1
      · intro env
        have hSpec := readSymScalar_spec env hSt (loc := src)
        rw [hRead] at hSpec
        dsimp [evalConcreteRvalue]
        exact hSpec.2
  | op1 op src =>
    dsimp [evalSymRvalue] at hEval
    cases hRead : readSymScalar st src with
    | none =>
      rw [hRead] at hEval
      cases hEval
    | some srcId =>
      rw [hRead] at hEval
      injection hEval with hPair
      have hId : resId = (internNode tbl (.op1 op srcId)).1 := by rw [hPair]
      have hTbl : tbl' = (internNode tbl (.op1 op srcId)).2 := by rw [hPair]
      subst hId hTbl
      have hSrcLt : srcId < tbl.nodes.length := by
        have hSpec := readSymScalar_spec (fun _ => 0) hSt (loc := src)
        rw [hRead] at hSpec
        exact hSpec.1
      have hNode : ValidNode tbl.nodes.length (.op1 op srcId) := hSrcLt
      have hV := internNode_valid hValid hNode
      have hE := internNode_extends tbl (.op1 op srcId)
      refine ⟨hV.1, hE, hV.2, ?_⟩
      intro env
      have hSpec := readSymScalar_spec env hSt (loc := src)
      rw [hRead] at hSpec
      dsimp [evalConcreteRvalue]
      rw [hSpec.2]
      have hEv := internNode_eval hValid hNode env
      rw [hEv]
      rfl
  | op2 op lhs rhs =>
    dsimp [evalSymRvalue] at hEval
    cases hL : readSymScalar st lhs with
    | none =>
      rw [hL] at hEval
      cases hEval
    | some lhsId =>
      rw [hL] at hEval
      cases hR : readSymScalar st rhs with
      | none =>
        rw [hR] at hEval
        cases hEval
      | some rhsId =>
        rw [hR] at hEval
        injection hEval with hPair
        have hId : resId = (internNode tbl (.op2 op lhsId rhsId)).1 := by rw [hPair]
        have hTbl : tbl' = (internNode tbl (.op2 op lhsId rhsId)).2 := by rw [hPair]
        subst hId hTbl
        have hLhsLt : lhsId < tbl.nodes.length := by
          have hSpec := readSymScalar_spec (fun _ => 0) hSt (loc := lhs)
          rw [hL] at hSpec
          exact hSpec.1
        have hRhsLt : rhsId < tbl.nodes.length := by
          have hSpec := readSymScalar_spec (fun _ => 0) hSt (loc := rhs)
          rw [hR] at hSpec
          exact hSpec.1
        have hNode : ValidNode tbl.nodes.length (.op2 op lhsId rhsId) := ⟨hLhsLt, hRhsLt⟩
        have hV := internNode_valid hValid hNode
        have hE := internNode_extends tbl (.op2 op lhsId rhsId)
        refine ⟨hV.1, hE, hV.2, ?_⟩
        intro env
        have hSpecL := readSymScalar_spec env hSt (loc := lhs)
        have hSpecR := readSymScalar_spec env hSt (loc := rhs)
        rw [hL] at hSpecL
        rw [hR] at hSpecR
        dsimp [evalConcreteRvalue]
        rw [hSpecL.2, hSpecR.2]
        have hEv := internNode_eval hValid hNode env
        rw [hEv]
        rfl
  | derefRef ptr =>
    dsimp [evalSymRvalue] at hEval
    cases hPtr : st.getSlot ptr with
    | dead _ => rw [hPtr] at hEval; cases hEval
    | uninit _ => rw [hPtr] at hEval; cases hEval
    | live ptrId ptrG ptrB ptrLoan =>
      rw [hPtr] at hEval
      cases ptrLoan with
      | none => cases hEval
      | some pair =>
        rcases pair with ⟨target, expGen⟩
        dsimp at hEval
        cases hTgt : st.getSlot target with
        | dead _ => rw [hTgt] at hEval; cases hEval
        | uninit _ => rw [hTgt] at hEval; cases hEval
        | live targetSymId curGen targetB targetLoan =>
          rw [hTgt] at hEval
          cases targetB with
          | false => cases hEval
          | true =>
            cases targetLoan with
            | some _ => cases hEval
            | none =>
              dsimp at hEval
              split at hEval
              · rename_i hGenEq
                injection hEval with hPair
                injection hPair with hId hTbl
                subst hId hTbl
                have hTgtSlot := hSt.getSlot target
                rw [hTgt] at hTgtSlot
                refine ⟨hValid, SymTable.Extends.refl tbl, hTgtSlot, ?_⟩
                intro env
                dsimp [evalConcreteRvalue]
                rw [evalSymCanonState_getSlot, hPtr]
                dsimp [evalSymSlot]
                rw [evalSymCanonState_getSlot, hTgt]
                dsimp [evalSymSlot]
                rw [hGenEq]
                rfl
              · cases hEval

/-- Active branch path condition `Option (SymId × Bool)`:
    - `none`: no active branch assumption,
    - `some (brId, true)`: inside a `then` arm where `(evalSymId tbl env brId != 0) = true`,
    - `some (brId, false)`: inside an `else` arm where `(evalSymId tbl env brId != 0) = false`. -/
abbrev PathCond := Option (SymId × Bool)

/-- Well-formedness of a `PathCond` against a table size `bound`. -/
def PathCondValid (bound : Nat) : PathCond → Prop
  | none => True
  | some (brId, _) => brId < bound

theorem PathCondValid.mono {b₁ b₂ : Nat} {pc : PathCond} (h : PathCondValid b₁ pc)
    (hLe : b₁ ≤ b₂) : PathCondValid b₂ pc := by
  cases pc with
  | none => trivial
  | some p => exact Nat.lt_of_lt_of_le h hLe

/-- Semantic meaning of `pc : PathCond` in `(tbl, env)`. -/
def PathCondHolds (tbl : SymTable) (env : SymEnv) : PathCond → Prop
  | none => True
  | some (brId, polarity) => (evalSymId tbl env brId != 0) = polarity

theorem PathCondHolds.mono {tbl tbl' : SymTable} {env : SymEnv} {pc : PathCond}
    (hValid : ValidTable tbl) (hExt : tbl.Extends tbl')
    (hPcValid : PathCondValid tbl.nodes.length pc)
    (hPc : PathCondHolds tbl env pc) :
    PathCondHolds tbl' env pc := by
  cases pc with
  | none => trivial
  | some p =>
    rcases p with ⟨brId, pol⟩
    dsimp [PathCondHolds] at hPc ⊢
    rw [← evalSymId_mono hValid hExt env hPcValid]
    exact hPc

/-- Sound GVN-backed non-zero condition recognizer for `MirStmt.assert`:
    recognizes non-zero constants (`.const v` with `v != 0`), negated zero constants
    (`.op1 .boolNot argId` where `argId` is `.const v` with `wrap64 v == 0`, e.g.,
    `!(x < x)`, `!(x - x)`, `!(x ^ x)` after `peepholeOp2`), as well as reflexive
    GVN equality/inequality nodes (`.op2 .eq a b` or `.op2 .le a b` where `a == b`). -/
def isProvablyNonZero (tbl : SymTable) (condId : Nat) : Bool :=
  match tbl.nodes[condId]? with
  | some (.const v) => wrap64 v != 0
  | some (.op1 .boolNot argId) =>
    match tbl.nodes[argId]? with
    | some (.const v) => wrap64 v == 0
    | _ => false
  | some (.op2 .eq a b) => a == b
  | some (.op2 .le a b) => a == b
  | _ => false

/-- Branch-condition-aware non-zero recognizer (`isProvablyNonZeroUnder`):
    extends `isProvablyNonZero` with path-sensitive discharge under an enclosing `switchInt`
    branch condition `pc`:
    - In the `then` arm (`pc = some (brId, true)`), `condId == brId` is provably non-zero.
    - In the `else` arm (`pc = some (brId, false)`), any `condId` interned as
      `.op1 .boolNot argId` with `argId == brId` is provably non-zero (`1`). -/
def isProvablyNonZeroUnder (tbl : SymTable) (pc : PathCond) (condId : Nat) : Bool :=
  if isProvablyNonZero tbl condId then
    true
  else
    match pc with
    | none => false
    | some (brId, true) => condId == brId
    | some (brId, false) =>
      match tbl.nodes[condId]? with
      | some (.op1 .boolNot argId) => argId == brId
      | _ => false

theorem isProvablyNonZero_sound {tbl : SymTable} {condId : Nat}
    (hValid : ValidTable tbl) (hOk : isProvablyNonZero tbl condId = true)
    (env : SymEnv) :
    (evalSymId tbl env condId != 0) = true := by
  dsimp [isProvablyNonZero] at hOk
  cases hLookup : tbl.nodes[condId]? with
  | none =>
    rw [hLookup] at hOk
    cases hOk
  | some node =>
    rw [hLookup] at hOk
    have hEval := evalSymId_eq_evalSymNodeWith hValid env hLookup
    cases node with
    | const v =>
      dsimp at hOk
      rw [hEval]
      dsimp [evalSymNodeWith]
      exact hOk
    | var _ =>
      dsimp at hOk
      cases hOk
    | op1 op argId =>
      cases op <;> dsimp at hOk <;> try cases hOk
      cases hArg : tbl.nodes[argId]? with
      | none => rw [hArg] at hOk; cases hOk
      | some argNode =>
        rw [hArg] at hOk
        cases argNode with
        | const v =>
          dsimp at hOk
          have hEvalArg := evalSymId_eq_evalSymNodeWith hValid env hArg
          rw [hEval]
          dsimp [evalSymNodeWith]
          rw [hEvalArg]
          dsimp [evalSymNodeWith, evalSymOp1]
          rw [hOk]
          rfl
        | var _ => cases hOk
        | op1 _ _ => cases hOk
        | op2 _ _ _ => cases hOk
        | ite _ _ _ => cases hOk
    | ite _ _ _ =>
      dsimp at hOk
      cases hOk
    | op2 op a b =>
      cases op <;> dsimp at hOk <;> try cases hOk
      · have hab : a = b := of_decide_eq_true hOk
        subst hab
        rw [hEval]
        dsimp [evalSymNodeWith, evalSymOp2]
        have hRefl : (evalSymId tbl env a == evalSymId tbl env a) = true :=
          decide_eq_true rfl
        rw [hRefl]
        rfl
      · have hab : a = b := of_decide_eq_true hOk
        subst hab
        rw [hEval]
        dsimp [evalSymNodeWith, evalSymOp2]
        have hRefl : decide (evalSymId tbl env a ≤ evalSymId tbl env a) = true :=
          decide_eq_true (Nat.le_refl _)
        rw [hRefl]
        rfl

/-- **Path-Sensitive Assertion Soundness (`isProvablyNonZeroUnder_sound`)**:
    Whenever `PathCondHolds tbl env pc` holds, `isProvablyNonZeroUnder tbl pc condId = true`
    guarantees `(evalSymId tbl env condId != 0) = true`. -/
theorem isProvablyNonZeroUnder_sound {tbl : SymTable} {pc : PathCond} {condId : Nat}
    {env : SymEnv} (hValid : ValidTable tbl) (hPc : PathCondHolds tbl env pc)
    (hOk : isProvablyNonZeroUnder tbl pc condId = true) :
    (evalSymId tbl env condId != 0) = true := by
  dsimp [isProvablyNonZeroUnder] at hOk
  cases hBase : isProvablyNonZero tbl condId with
  | true => exact isProvablyNonZero_sound hValid hBase env
  | false =>
    rw [hBase] at hOk
    dsimp at hOk
    cases pc with
    | none => cases hOk
    | some p =>
      rcases p with ⟨brId, pol⟩
      cases pol with
      | true =>
        dsimp at hOk
        have hEq : condId = brId := of_decide_eq_true hOk
        subst hEq
        exact hPc
      | false =>
        dsimp at hOk
        cases hLookup : tbl.nodes[condId]? with
        | none => rw [hLookup] at hOk; cases hOk
        | some node =>
          rw [hLookup] at hOk
          have hEval := evalSymId_eq_evalSymNodeWith hValid env hLookup
          cases node with
          | const _ => cases hOk
          | var _ => cases hOk
          | op2 _ _ _ => cases hOk
          | ite _ _ _ => cases hOk
          | op1 op argId =>
            cases op <;> dsimp at hOk <;> try cases hOk
            have hArgEq : argId = brId := of_decide_eq_true hOk
            subst hArgEq
            rw [hEval]
            dsimp [evalSymNodeWith, evalSymOp1]
            dsimp [PathCondHolds] at hPc
            have hZero : evalSymId tbl env argId = 0 := bne_eq_false_iff_eq.1 hPc
            rw [hZero]
            rfl

theorem evalSymSlot_writeVal? (tbl : SymTable) (env : SymEnv) (s : Slot SymId)
    (symId : Nat) (loan : Option (LocalId × Nat)) :
    (s.writeVal? symId loan).map (evalSymSlot tbl env) =
      (evalSymSlot tbl env s).writeVal? (evalSymId tbl env symId) loan := by
  cases s with
  | dead _ => rfl
  | uninit _ => rfl
  | live _ _ b _ => cases b <;> rfl

theorem ValidSymSlot.writeVal? {bound : Nat} {s s' : Slot SymId} {symId : Nat}
    {loan : Option (LocalId × Nat)} (hW : s.writeVal? symId loan = some s')
    (hId : symId < bound) : ValidSymSlot bound s' := by
  cases s with
  | dead _ => cases hW
  | uninit _ =>
    injection hW with h
    subst h
    exact hId
  | live _ _ b _ =>
    cases b <;> (injection hW with h; subst h; exact hId)

theorem evalSymCanonState_length (tbl : SymTable) (env : SymEnv) (st : CanonState SymId) :
    (evalSymCanonState tbl env st).slots.length = st.slots.length := by
  simp [evalSymCanonState]

theorem evalSymSlot_ownerRead (tbl : SymTable) (env : SymEnv) (s : Slot SymId) :
    evalSymSlot tbl env s.ownerRead = (evalSymSlot tbl env s).ownerRead := by
  cases s with
  | dead _ => rfl
  | uninit _ => rfl
  | live _ _ b _ => cases b <;> rfl

theorem ValidSymSlot.ownerRead {bound : Nat} {s : Slot SymId} (h : ValidSymSlot bound s) :
    ValidSymSlot bound s.ownerRead := by
  cases s with
  | dead _ => trivial
  | uninit _ => trivial
  | live _ _ b _ => cases b <;> exact h

theorem evalSymCanonState_ownerReadLoc (tbl : SymTable) (env : SymEnv) (st : CanonState SymId)
    (loc : LocalId) :
    evalSymCanonState tbl env (st.ownerReadLoc loc) =
      (evalSymCanonState tbl env st).ownerReadLoc loc := by
  dsimp only [CanonState.ownerReadLoc]
  rw [evalSymCanonState_setSlot, evalSymSlot_ownerRead, evalSymCanonState_getSlot]

theorem ValidSymCanonState.ownerReadLoc {bound : Nat} {st : CanonState SymId}
    (h : ValidSymCanonState bound st) (loc : LocalId) :
    ValidSymCanonState bound (st.ownerReadLoc loc) :=
  h.setSlot (h.getSlot loc).ownerRead

theorem evalSymCanonState_ownerReadRvalue (tbl : SymTable) (env : SymEnv) (st : CanonState SymId)
    (rv : MirRvalue) :
    evalSymCanonState tbl env (st.ownerReadRvalue rv) =
      (evalSymCanonState tbl env st).ownerReadRvalue rv := by
  cases rv <;> dsimp only [CanonState.ownerReadRvalue] <;>
    repeat rw [evalSymCanonState_ownerReadLoc]

theorem ValidSymCanonState.ownerReadRvalue {bound : Nat} {st : CanonState SymId}
    (h : ValidSymCanonState bound st) (rv : MirRvalue) :
    ValidSymCanonState bound (st.ownerReadRvalue rv) := by
  cases rv <;> dsimp only [CanonState.ownerReadRvalue]
  · exact h
  · exact h.ownerReadLoc _
  · exact h.ownerReadLoc _
  · exact (h.ownerReadLoc _).ownerReadLoc _
  · exact h.ownerReadLoc _

theorem evalSymSlot_retarget (tbl : SymTable) (env : SymEnv) (target g : Nat) (s : Slot SymId) :
    evalSymSlot tbl env (s.retarget target g) = (evalSymSlot tbl env s).retarget target g := by
  cases s <;> rfl

theorem ValidSymSlot.retarget {bound : Nat} {s : Slot SymId} (h : ValidSymSlot bound s)
    (target g : Nat) : ValidSymSlot bound (s.retarget target g) := by
  cases s <;> exact h

theorem evalSymCanonState_storeThrough (tbl : SymTable) (env : SymEnv) (st : CanonState SymId)
    (ptr target : LocalId) (symId : SymId) (g : Nat) (loan : Option (LocalId × Nat)) :
    evalSymCanonState tbl env (st.storeThrough ptr target symId g loan) =
      (evalSymCanonState tbl env st).storeThrough ptr target (evalSymId tbl env symId) g loan := by
  dsimp only [CanonState.storeThrough]
  rw [evalSymCanonState_setSlot, evalSymSlot_retarget, ← evalSymCanonState_getSlot,
    evalSymCanonState_setSlot, evalSymCanonState_ownerReadLoc]
  rfl

theorem ValidSymCanonState.storeThrough {bound : Nat} {st : CanonState SymId}
    (h : ValidSymCanonState bound st) {ptr target : LocalId} {symId : SymId}
    (hId : symId < bound) (g : Nat) (loan : Option (LocalId × Nat)) :
    ValidSymCanonState bound (st.storeThrough ptr target symId g loan) := by
  dsimp only [CanonState.storeThrough]
  have h₁ : ValidSymCanonState bound
      ((st.ownerReadLoc ptr).setSlot target (.live symId g true loan)) :=
    (h.ownerReadLoc ptr).setSlot hId
  exact h₁.setSlot ((h₁.getSlot ptr).retarget target g)

/-- Symbolic execution of a single `MirStmt` in `(st, tbl)` under optional branch path
    condition `pc` (mirrors `execStmt`'s faults, including `.storeRef` temporal borrow checks
    and owner-read loan invalidation). -/
def symExecStmt (st : CanonState SymId) (tbl : SymTable)
    (stmt : MirStmt) (pc : PathCond := none) : Option (CanonState SymId × SymTable) :=
  match stmt with
  | .assign dst rv =>
    match evalSymRvalue st tbl rv with
    | none => none
    | some (symId, tbl') =>
      let st₀ := st.ownerReadRvalue rv
      match (st₀.getSlot dst).writeVal? symId none with
      | none => none
      | some s' => some (st₀.setSlot dst s', tbl')
  | .storageLive loc =>
    if loc < st.slots.length then some (st.setSlot loc (st.getSlot loc).reborn, tbl) else none
  | .storageDead loc =>
    if loc < st.slots.length then some (st.setSlot loc (st.getSlot loc).kill, tbl) else none
  | .assert cond =>
    match readSymScalar st cond with
    | some condId =>
      if isProvablyNonZeroUnder tbl pc condId then some (st.ownerReadLoc cond, tbl) else none
    | none => none
  | .retagBorrow dst target =>
    match st.getSlot target with
    | .live targetSymId g b targetLoan =>
      let g' := if b then g + 1 else g
      match ((st.setSlot target (.live targetSymId g' true targetLoan)).getSlot dst).writeVal?
          targetSymId (some (target, g')) with
      | none => none
      | some s' =>
        some ((st.setSlot target (.live targetSymId g' true targetLoan)).setSlot dst s', tbl)
    | _ => none
  | .storeRef ptr rv =>
    match evalSymRvalue st tbl rv with
    | none => none
    | some (symId, tbl') =>
      let st₀ := st.ownerReadRvalue rv
      match st₀.getSlot ptr with
      | .live _ _ _ (some (target, expGen)) =>
        match st₀.getSlot target with
        | .live _ curGen true none =>
          if curGen == expGen then
            some (st₀.storeThrough ptr target symId (curGen + 1) none, tbl')
          else
            none
        | _ => none
      | _ => none

/-- **Path-Sensitive Single-Statement Simulation (`symExecStmt_under_sound`)**: a successful
    symbolic step under path condition `pc` is matched, under every `env` satisfying
    `PathCondHolds tbl env pc`, by the identical concrete step on the evaluated state. -/
theorem symExecStmt_under_sound {st st' : CanonState SymId} {tbl tbl' : SymTable}
    {stmt : MirStmt} {pc : PathCond}
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hExec : symExecStmt st tbl stmt pc = some (st', tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      ValidSymCanonState tbl'.nodes.length st' ∧
      ∀ env : SymEnv,
        PathCondHolds tbl env pc →
        execStmt (evalSymCanonState tbl env st) stmt =
          some (evalSymCanonState tbl' env st') := by
  cases stmt with
  | assign dst rv =>
    dsimp only [symExecStmt] at hExec
    cases hRv : evalSymRvalue st tbl rv with
    | none =>
      rw [hRv] at hExec
      cases hExec
    | some pair =>
      rcases pair with ⟨symId, tbl₁⟩
      rw [hRv] at hExec
      dsimp only at hExec
      cases hW : ((st.ownerReadRvalue rv).getSlot dst).writeVal? symId none with
      | none =>
        rw [hW] at hExec
        cases hExec
      | some s' =>
        rw [hW] at hExec
        injection hExec with hPair
        injection hPair with hSt' hTbl'
        subst hSt' hTbl'
        rcases evalSymRvalue_sound hValid hSt hRv with ⟨hValid₁, hExt₁, hSymIdLt, hEvalRv⟩
        have hLenLe : tbl.nodes.length ≤ tbl₁.nodes.length := hExt₁.length_le
        have hSt₁ : ValidSymCanonState tbl₁.nodes.length (st.ownerReadRvalue rv) :=
          ValidSymSlots.mono (hSt.ownerReadRvalue rv) hLenLe
        refine ⟨hValid₁, hExt₁, hSt₁.setSlot (ValidSymSlot.writeVal? hW hSymIdLt), ?_⟩
        intro env _
        dsimp only [execStmt]
        rw [hEvalRv env]
        dsimp only
        rw [evalSymCanonState_mono hValid hExt₁ env hSt, ← evalSymCanonState_ownerReadRvalue,
          evalSymCanonState_getSlot, ← evalSymSlot_writeVal?, hW]
        dsimp only [Option.map]
        rw [evalSymCanonState_setSlot]
  | storageLive loc =>
    dsimp only [symExecStmt] at hExec
    split at hExec
    · rename_i hLt
      injection hExec with hPair
      injection hPair with hSt' hTbl'
      subst hSt' hTbl'
      refine ⟨hValid, SymTable.Extends.refl tbl, hSt.setSlot trivial, ?_⟩
      intro env _
      dsimp only [execStmt]
      rw [evalSymCanonState_length, ite_eq_left hLt, evalSymCanonState_setSlot,
        evalSymCanonState_getSlot, evalSymSlot_reborn]
    · cases hExec
  | storageDead loc =>
    dsimp only [symExecStmt] at hExec
    split at hExec
    · rename_i hLt
      injection hExec with hPair
      injection hPair with hSt' hTbl'
      subst hSt' hTbl'
      refine ⟨hValid, SymTable.Extends.refl tbl, hSt.setSlot trivial, ?_⟩
      intro env _
      dsimp only [execStmt]
      rw [evalSymCanonState_length, ite_eq_left hLt, evalSymCanonState_setSlot,
        evalSymCanonState_getSlot, evalSymSlot_kill]
    · cases hExec
  | assert cond =>
    dsimp only [symExecStmt] at hExec
    cases hRead : readSymScalar st cond with
    | none =>
      rw [hRead] at hExec
      cases hExec
    | some condId =>
      rw [hRead] at hExec
      dsimp only at hExec
      split at hExec
      · rename_i hNz
        injection hExec with hPair
        injection hPair with hSt' hTbl'
        subst hSt' hTbl'
        refine ⟨hValid, SymTable.Extends.refl tbl, hSt.ownerReadLoc cond, ?_⟩
        intro env hPc
        have hSpec := readSymScalar_spec env hSt (loc := cond)
        rw [hRead] at hSpec
        dsimp only [execStmt]
        rw [hSpec.2]
        dsimp only
        rw [isProvablyNonZeroUnder_sound hValid hPc hNz, evalSymCanonState_ownerReadLoc]
        rfl
      · cases hExec
  | retagBorrow dst target =>
    dsimp only [symExecStmt] at hExec
    cases hTgt : st.getSlot target with
    | dead _ => rw [hTgt] at hExec; cases hExec
    | uninit _ => rw [hTgt] at hExec; cases hExec
    | live targetSymId g targetB targetLoan =>
      rw [hTgt] at hExec
      dsimp only at hExec
      generalize hg' : (if targetB = true then g + 1 else g) = g' at hExec
      cases hW : ((st.setSlot target (.live targetSymId g' true targetLoan)).getSlot dst).writeVal?
          targetSymId (some (target, g')) with
      | none =>
        rw [hW] at hExec
        cases hExec
      | some s' =>
        rw [hW] at hExec
        injection hExec with hPair
        injection hPair with hSt' hTbl'
        subst hSt' hTbl'
        have hTgtValid : targetSymId < tbl.nodes.length := by
          have hSlot := hSt.getSlot target
          rw [hTgt] at hSlot
          exact hSlot
        have hSt₁ := hSt.setSlot (loc := target) (s := .live targetSymId g' true targetLoan)
          hTgtValid
        refine ⟨hValid, SymTable.Extends.refl tbl,
          hSt₁.setSlot (ValidSymSlot.writeVal? hW hTgtValid), ?_⟩
        intro env _
        have hSetEq : (evalSymCanonState tbl env st).setSlot target
            (.live (evalSymId tbl env targetSymId) g' true targetLoan) =
            evalSymCanonState tbl env (st.setSlot target (.live targetSymId g' true targetLoan)) :=
          (evalSymCanonState_setSlot tbl env st target (.live targetSymId g' true targetLoan)).symm
        dsimp only [execStmt]
        rw [evalSymCanonState_getSlot, hTgt]
        dsimp only [evalSymSlot]
        rw [hg', hSetEq, evalSymCanonState_getSlot, ← evalSymSlot_writeVal?, hW]
        dsimp only [Option.map]
        exact congrArg some (evalSymCanonState_setSlot tbl env _ dst s').symm
  | storeRef ptr rv =>
    dsimp only [symExecStmt] at hExec
    cases hRv : evalSymRvalue st tbl rv with
    | none => rw [hRv] at hExec; cases hExec
    | some pair =>
      rcases pair with ⟨symId, tbl₁⟩
      rw [hRv] at hExec
      dsimp only at hExec
      cases hPtr : (st.ownerReadRvalue rv).getSlot ptr with
      | dead _ => rw [hPtr] at hExec; cases hExec
      | uninit _ => rw [hPtr] at hExec; cases hExec
      | live ptrId ptrG ptrB ptrLoan =>
        rw [hPtr] at hExec
        cases ptrLoan with
        | none => cases hExec
        | some lPair =>
          rcases lPair with ⟨target, expGen⟩
          dsimp only at hExec
          cases hTgt : (st.ownerReadRvalue rv).getSlot target with
          | dead _ => rw [hTgt] at hExec; cases hExec
          | uninit _ => rw [hTgt] at hExec; cases hExec
          | live targetSymId curGen targetB targetLoan =>
            rw [hTgt] at hExec
            cases targetB with
            | false => cases hExec
            | true =>
              cases targetLoan with
              | some _ => cases hExec
              | none =>
                dsimp only at hExec
                split at hExec
                · rename_i hGenEq
                  injection hExec with hPair
                  injection hPair with hSt' hTbl'
                  subst hSt' hTbl'
                  rcases evalSymRvalue_sound hValid hSt hRv with
                    ⟨hValid₁, hExt₁, hSymIdLt, hEvalRv⟩
                  have hSt₁ : ValidSymCanonState tbl₁.nodes.length (st.ownerReadRvalue rv) :=
                    ValidSymSlots.mono (hSt.ownerReadRvalue rv) hExt₁.length_le
                  refine ⟨hValid₁, hExt₁, hSt₁.storeThrough hSymIdLt (curGen + 1) none, ?_⟩
                  intro env _
                  dsimp only [execStmt]
                  rw [hEvalRv env]
                  dsimp only
                  rw [← evalSymCanonState_ownerReadRvalue, evalSymCanonState_getSlot, hPtr]
                  dsimp only [evalSymSlot]
                  rw [evalSymCanonState_getSlot, hTgt]
                  dsimp only [evalSymSlot]
                  rw [ite_eq_left hGenEq, evalSymCanonState_storeThrough,
                    evalSymCanonState_mono hValid hExt₁ env (hSt.ownerReadRvalue rv)]
                · cases hExec

/-- **Exact single-statement simulation (`symExecStmt_sound`)** for `pc = none`. -/
theorem symExecStmt_sound {st st' : CanonState SymId} {tbl tbl' : SymTable}
    {stmt : MirStmt}
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hExec : symExecStmt st tbl stmt = some (st', tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      ValidSymCanonState tbl'.nodes.length st' ∧
      ∀ env : SymEnv,
        execStmt (evalSymCanonState tbl env st) stmt =
          some (evalSymCanonState tbl' env st') := by
  rcases symExecStmt_under_sound hValid hSt hExec with ⟨hV, hE, hS, hEv⟩
  exact ⟨hV, hE, hS, fun env => hEv env trivial⟩

/-- Symbolic execution of a list of `MirStmt`s in `(st, tbl)` under optional branch path
    condition `pc`. -/
def symExecStmts (st : CanonState SymId) (tbl : SymTable) :
    List MirStmt → (pc : PathCond := none) → Option (CanonState SymId × SymTable)
  | [], _ => some (st, tbl)
  | stmt :: rest, pc =>
    match symExecStmt st tbl stmt pc with
    | some (st₁, tbl₁) => symExecStmts st₁ tbl₁ rest pc
    | none => none

theorem symExecStmts_under_sound :
    ∀ (stmts : List MirStmt) {st st' : CanonState SymId} {tbl tbl' : SymTable} {pc : PathCond},
      ValidTable tbl →
      ValidSymCanonState tbl.nodes.length st →
      symExecStmts st tbl stmts pc = some (st', tbl') →
      PathCondValid tbl.nodes.length pc →
      ValidTable tbl' ∧
        tbl.Extends tbl' ∧
        ValidSymCanonState tbl'.nodes.length st' ∧
        ∀ env : SymEnv,
          PathCondHolds tbl env pc →
          execStmts (evalSymCanonState tbl env st) stmts =
            some (evalSymCanonState tbl' env st')
  | [], _, _, tbl, _, _, hValid, hSt, hExec, _ => by
    dsimp [symExecStmts] at hExec
    injection hExec with hPair
    injection hPair with hSt' hTbl'
    subst hSt' hTbl'
    exact ⟨hValid, SymTable.Extends.refl tbl, hSt, fun _ _ => rfl⟩
  | stmt :: rest, st, st', tbl, tbl', pc, hValid, hSt, hExec, hPcValid => by
    dsimp [symExecStmts] at hExec
    cases hStep₁ : symExecStmt st tbl stmt pc with
    | none =>
      rw [hStep₁] at hExec
      cases hExec
    | some pair₁ =>
      rcases pair₁ with ⟨st₁, tbl₁⟩
      rw [hStep₁] at hExec
      rcases symExecStmt_under_sound hValid hSt hStep₁ with ⟨hValid₁, hExt₁, hSt₁, hEval₁⟩
      have hPcValid₁ : PathCondValid tbl₁.nodes.length pc := hPcValid.mono hExt₁.length_le
      rcases symExecStmts_under_sound rest hValid₁ hSt₁ hExec hPcValid₁ with
        ⟨hValid₂, hExt₂, hSt₂, hEval₂⟩
      refine ⟨hValid₂, hExt₁.trans hExt₂, hSt₂, ?_⟩
      intro env hPc
      dsimp [execStmts]
      rw [hEval₁ env hPc]
      exact hEval₂ env (PathCondHolds.mono hValid hExt₁ hPcValid hPc)

theorem symExecStmts_sound
    (stmts : List MirStmt) {st st' : CanonState SymId} {tbl tbl' : SymTable}
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hExec : symExecStmts st tbl stmts = some (st', tbl')) :
    ValidTable tbl' ∧
      tbl.Extends tbl' ∧
      ValidSymCanonState tbl'.nodes.length st' ∧
      ∀ env : SymEnv,
        execStmts (evalSymCanonState tbl env st) stmts =
          some (evalSymCanonState tbl' env st') := by
  rcases symExecStmts_under_sound stmts hValid hSt hExec trivial with ⟨hV, hE, hS, hEv⟩
  exact ⟨hV, hE, hS, fun env => hEv env trivial⟩

/-!
### 3.3 Join-Point Pruning Refinement (`SlotRefines` / `StateRefines`)

The symbolic evaluator prunes dead locals at joins (`joinCanon`), so the states it tracks are
*more dead* than the concrete (unpruned) state: every abstract slot either equals the concrete
slot or is the concrete slot's `kill` (dead, same borrow-dirtied generation). Every concrete
operation is monotone w.r.t. this refinement (`execStmts_refines`), which is what lets the
untrusted liveness mask stay outside the trusted concrete semantics.
-/

/-- Slot refinement: abstract slot `a` equals concrete slot `c`, or is its join-point prune `c.kill`. -/
def SlotRefines (a c : Slot Nat) : Prop := a = c ∨ a = c.kill

/-- Pointwise slot-list refinement (forces equal lengths). -/
def SlotsRefine : List (Slot Nat) → List (Slot Nat) → Prop
  | [], [] => True
  | a :: as, c :: cs => SlotRefines a c ∧ SlotsRefine as cs
  | _, _ => False

/-- State refinement between an abstract (join-pruned) and a concrete `CanonState Nat`. -/
def StateRefines (a c : CanonState Nat) : Prop := SlotsRefine a.slots c.slots

theorem SlotsRefine.refl : ∀ (cs : List (Slot Nat)), SlotsRefine cs cs
  | [] => trivial
  | _ :: cs => ⟨Or.inl rfl, SlotsRefine.refl cs⟩

theorem StateRefines.refl (c : CanonState Nat) : StateRefines c c :=
  SlotsRefine.refl c.slots

theorem SlotsRefine.length_eq : ∀ {as cs : List (Slot Nat)}, SlotsRefine as cs →
    as.length = cs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [SlotsRefine.length_eq h]
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

theorem StateRefines.length_eq {a c : CanonState Nat} (h : StateRefines a c) :
    a.slots.length = c.slots.length :=
  SlotsRefine.length_eq h

theorem Slot.kill_reborn {Val : Type} (s : Slot Val) : s.kill.reborn = s.reborn := rfl

/-- A non-dead abstract slot refines only itself. -/
theorem SlotRefines.eq_of_not_dead {a c : Slot Nat} (h : SlotRefines a c)
    (hNot : ∀ g, a ≠ .dead g) : c = a := by
  rcases h with h | h
  · exact h.symm
  · exact absurd h (hNot c.nextGenOnEnd)

theorem SlotsRefine.getSlotAt : ∀ {as cs : List (Slot Nat)} (loc : LocalId),
    SlotsRefine as cs → SlotRefines (getSlotAt as loc) (getSlotAt cs loc)
  | [], [], _, _ => Or.inl rfl
  | _ :: _, _ :: _, 0, ⟨h, _⟩ => h
  | _ :: _, _ :: _, loc + 1, ⟨_, h⟩ => SlotsRefine.getSlotAt loc h
  | [], _ :: _, _, h => False.elim h
  | _ :: _, [], _, h => False.elim h

theorem StateRefines.getSlot {a c : CanonState Nat} (h : StateRefines a c) (loc : LocalId) :
    SlotRefines (a.getSlot loc) (c.getSlot loc) :=
  SlotsRefine.getSlotAt loc h

theorem SlotsRefine.setSlotAt : ∀ {as cs : List (Slot Nat)} (loc : LocalId) {a c : Slot Nat},
    SlotsRefine as cs → SlotRefines a c → SlotsRefine (setSlotAt as loc a) (setSlotAt cs loc c)
  | [], [], _, _, _, _, _ => trivial
  | _ :: _, _ :: _, 0, _, _, ⟨_, hT⟩, hS => ⟨hS, hT⟩
  | _ :: _, _ :: _, loc + 1, _, _, ⟨hH, hT⟩, hS => ⟨hH, SlotsRefine.setSlotAt loc hT hS⟩
  | [], _ :: _, _, _, _, h, _ => False.elim h
  | _ :: _, [], _, _, _, h, _ => False.elim h

theorem StateRefines.setSlot {a c : CanonState Nat} {loc : LocalId} {sa sc : Slot Nat}
    (h : StateRefines a c) (hS : SlotRefines sa sc) :
    StateRefines (a.setSlot loc sa) (c.setSlot loc sc) :=
  SlotsRefine.setSlotAt loc h hS

theorem readConcreteScalar_refines {a c : CanonState Nat} (h : StateRefines a c)
    {loc : LocalId} {v : Nat} (hRead : readConcreteScalar a loc = some v) :
    readConcreteScalar c loc = some v := by
  unfold readConcreteScalar at hRead ⊢
  have hS := h.getSlot loc
  cases hA : a.getSlot loc with
  | dead g => rw [hA] at hRead; cases hRead
  | uninit g => rw [hA] at hRead; cases hRead
  | live v' g b l =>
    rw [hA] at hRead hS
    rw [hS.eq_of_not_dead (by intro _ hh; cases hh)]
    exact hRead

theorem evalConcreteRvalue_refines {a c : CanonState Nat} (h : StateRefines a c)
    {rv : MirRvalue} {v : Nat} (hEval : evalConcreteRvalue a rv = some v) :
    evalConcreteRvalue c rv = some v := by
  cases rv with
  | const n => exact hEval
  | use src => exact readConcreteScalar_refines h hEval
  | op1 op src =>
    dsimp only [evalConcreteRvalue] at hEval ⊢
    cases hR : readConcreteScalar a src with
    | none => rw [hR] at hEval; cases hEval
    | some x =>
      rw [hR] at hEval
      rw [readConcreteScalar_refines h hR]
      exact hEval
  | op2 op lhs rhs =>
    dsimp only [evalConcreteRvalue] at hEval ⊢
    cases hL : readConcreteScalar a lhs with
    | none => rw [hL] at hEval; cases hEval
    | some x =>
      cases hR : readConcreteScalar a rhs with
      | none => rw [hL, hR] at hEval; cases hEval
      | some y =>
        rw [hL, hR] at hEval
        rw [readConcreteScalar_refines h hL, readConcreteScalar_refines h hR]
        exact hEval
  | derefRef ptr =>
    dsimp only [evalConcreteRvalue] at hEval ⊢
    have hP := h.getSlot ptr
    cases hPtr : a.getSlot ptr with
    | dead _ => rw [hPtr] at hEval; cases hEval
    | uninit _ => rw [hPtr] at hEval; cases hEval
    | live pv pg pb pl =>
      rw [hPtr] at hEval hP
      rw [hP.eq_of_not_dead (by intro _ hh; cases hh)]
      cases pl with
      | none => cases hEval
      | some pair =>
        rcases pair with ⟨target, expGen⟩
        dsimp only at hEval ⊢
        have hT := h.getSlot target
        cases hTgt : a.getSlot target with
        | dead _ => rw [hTgt] at hEval; cases hEval
        | uninit _ => rw [hTgt] at hEval; cases hEval
        | live tv tg tb tl =>
          rw [hTgt] at hEval hT
          rw [hT.eq_of_not_dead (by intro _ hh; cases hh)]
          exact hEval

theorem writeVal?_refines {a c : Slot Nat} (h : SlotRefines a c) {v : Nat}
    {l : Option (LocalId × Nat)} {a' : Slot Nat} (hW : a.writeVal? v l = some a') :
    c.writeVal? v l = some a' := by
  have hc : c = a := h.eq_of_not_dead (by
    intro g hg
    subst hg
    cases hW)
  rw [hc]
  exact hW

theorem Slot.ownerRead_kill {Val : Type} (s : Slot Val) : s.ownerRead.kill = s.kill := by
  cases s with
  | dead _ => rfl
  | uninit _ => rfl
  | live _ _ b _ => cases b <;> rfl

theorem SlotRefines.ownerRead {a c : Slot Nat} (h : SlotRefines a c) :
    SlotRefines a.ownerRead c.ownerRead := by
  rcases h with h | h
  · subst h
    exact Or.inl rfl
  · subst h
    exact Or.inr (Slot.ownerRead_kill c).symm

theorem StateRefines.ownerReadLoc {a c : CanonState Nat} (h : StateRefines a c) (loc : LocalId) :
    StateRefines (a.ownerReadLoc loc) (c.ownerReadLoc loc) :=
  h.setSlot (h.getSlot loc).ownerRead

theorem StateRefines.ownerReadRvalue {a c : CanonState Nat} (h : StateRefines a c) (rv : MirRvalue) :
    StateRefines (a.ownerReadRvalue rv) (c.ownerReadRvalue rv) := by
  cases rv <;> dsimp only [CanonState.ownerReadRvalue]
  · exact h
  · exact h.ownerReadLoc _
  · exact h.ownerReadLoc _
  · exact (h.ownerReadLoc _).ownerReadLoc _
  · exact h.ownerReadLoc _

theorem SlotRefines.retarget {a c : Slot Nat} (h : SlotRefines a c) (target g : Nat) :
    SlotRefines (a.retarget target g) (c.retarget target g) := by
  rcases h with h | h
  · subst h
    exact Or.inl rfl
  · subst h
    cases c with
    | dead _ => exact Or.inr rfl
    | uninit _ => exact Or.inr rfl
    | live pv pg pb pl => exact Or.inr (by cases pb <;> rfl)

theorem StateRefines.storeThrough {a c : CanonState Nat} (h : StateRefines a c)
    (ptr target : LocalId) (v g : Nat) (loan : Option (LocalId × Nat)) :
    StateRefines (a.storeThrough ptr target v g loan) (c.storeThrough ptr target v g loan) := by
  dsimp only [CanonState.storeThrough]
  have h₁ : StateRefines ((a.ownerReadLoc ptr).setSlot target (.live v g true loan))
      ((c.ownerReadLoc ptr).setSlot target (.live v g true loan)) :=
    (h.ownerReadLoc ptr).setSlot (Or.inl rfl)
  exact h₁.setSlot ((h₁.getSlot ptr).retarget target g)

/-- **Refinement Monotonicity of a Concrete Step (`execStmt_refines`)**: if a statement succeeds
    on the (more-dead) abstract state, it succeeds on every refined concrete state, and the
    results remain related. -/
theorem execStmt_refines {a c : CanonState Nat} (h : StateRefines a c) {stmt : MirStmt}
    {a' : CanonState Nat} (hExec : execStmt a stmt = some a') :
    ∃ c', execStmt c stmt = some c' ∧ StateRefines a' c' := by
  cases stmt with
  | assign dst rv =>
    dsimp only [execStmt] at hExec ⊢
    cases hRv : evalConcreteRvalue a rv with
    | none => rw [hRv] at hExec; cases hExec
    | some v =>
      rw [hRv] at hExec
      rw [evalConcreteRvalue_refines h hRv]
      dsimp only at hExec ⊢
      have h₀ : StateRefines (a.ownerReadRvalue rv) (c.ownerReadRvalue rv) :=
        h.ownerReadRvalue rv
      cases hW : ((a.ownerReadRvalue rv).getSlot dst).writeVal? v none with
      | none => rw [hW] at hExec; cases hExec
      | some s' =>
        rw [hW] at hExec
        rw [writeVal?_refines (h₀.getSlot dst) hW]
        injection hExec with hA'
        subst hA'
        exact ⟨_, rfl, h₀.setSlot (Or.inl rfl)⟩
  | storageLive loc =>
    dsimp only [execStmt] at hExec ⊢
    rw [← h.length_eq]
    split at hExec
    · rename_i hLt
      injection hExec with hA'
      subst hA'
      refine ⟨_, ite_eq_left hLt, h.setSlot ?_⟩
      rcases h.getSlot loc with hS | hS
      · rw [hS]
        exact Or.inl rfl
      · rw [hS, Slot.kill_reborn]
        exact Or.inl rfl
    · cases hExec
  | storageDead loc =>
    dsimp only [execStmt] at hExec ⊢
    rw [← h.length_eq]
    split at hExec
    · rename_i hLt
      injection hExec with hA'
      subst hA'
      refine ⟨_, ite_eq_left hLt, h.setSlot ?_⟩
      rcases h.getSlot loc with hS | hS
      · rw [hS]
        exact Or.inl rfl
      · rw [hS, Slot.kill_idempotent]
        exact Or.inl rfl
    · cases hExec
  | assert cond =>
    dsimp only [execStmt] at hExec ⊢
    cases hR : readConcreteScalar a cond with
    | none => rw [hR] at hExec; cases hExec
    | some v =>
      rw [hR] at hExec
      rw [readConcreteScalar_refines h hR]
      dsimp only at hExec ⊢
      split at hExec
      · rename_i hNz
        injection hExec with hA'
        subst hA'
        exact ⟨c.ownerReadLoc cond, ite_eq_left hNz, h.ownerReadLoc cond⟩
      · cases hExec
  | retagBorrow dst target =>
    dsimp only [execStmt] at hExec ⊢
    have hT := h.getSlot target
    cases hTgt : a.getSlot target with
    | dead _ => rw [hTgt] at hExec; cases hExec
    | uninit _ => rw [hTgt] at hExec; cases hExec
    | live tv g b tl =>
      rw [hTgt] at hExec hT
      rw [hT.eq_of_not_dead (by intro _ hh; cases hh)]
      dsimp only at hExec ⊢
      generalize (if b = true then g + 1 else g) = g' at hExec ⊢
      have h₁ : StateRefines (a.setSlot target (.live tv g' true tl))
          (c.setSlot target (.live tv g' true tl)) := h.setSlot (Or.inl rfl)
      cases hW : ((a.setSlot target (.live tv g' true tl)).getSlot dst).writeVal? tv
          (some (target, g')) with
      | none => rw [hW] at hExec; cases hExec
      | some s' =>
        rw [hW] at hExec
        rw [writeVal?_refines (h₁.getSlot dst) hW]
        injection hExec with hA'
        subst hA'
        exact ⟨_, rfl, h₁.setSlot (Or.inl rfl)⟩
  | storeRef ptr rv =>
    dsimp only [execStmt] at hExec ⊢
    cases hRv : evalConcreteRvalue a rv with
    | none => rw [hRv] at hExec; cases hExec
    | some v =>
      rw [hRv] at hExec
      rw [evalConcreteRvalue_refines h hRv]
      dsimp only at hExec ⊢
      have h₀ : StateRefines (a.ownerReadRvalue rv) (c.ownerReadRvalue rv) :=
        h.ownerReadRvalue rv
      have hP := h₀.getSlot ptr
      cases hPtr : (a.ownerReadRvalue rv).getSlot ptr with
      | dead _ => rw [hPtr] at hExec; cases hExec
      | uninit _ => rw [hPtr] at hExec; cases hExec
      | live pv pg pb pl =>
        rw [hPtr] at hExec hP
        rw [hP.eq_of_not_dead (by intro _ hh; cases hh)]
        cases pl with
        | none => cases hExec
        | some lPair =>
          rcases lPair with ⟨target, expGen⟩
          dsimp only at hExec ⊢
          have hT := h₀.getSlot target
          cases hTgt : (a.ownerReadRvalue rv).getSlot target with
          | dead _ => rw [hTgt] at hExec; cases hExec
          | uninit _ => rw [hTgt] at hExec; cases hExec
          | live tv curGen tb tl =>
            rw [hTgt] at hExec hT
            rw [hT.eq_of_not_dead (by intro _ hh; cases hh)]
            cases tb with
            | false => cases hExec
            | true =>
              cases tl with
              | some _ => cases hExec
              | none =>
                dsimp only at hExec ⊢
                split at hExec
                · rename_i hGenEq
                  injection hExec with hA'
                  subst hA'
                  exact ⟨_, ite_eq_left hGenEq, h₀.storeThrough ptr target v (curGen + 1) none⟩
                · cases hExec

theorem execStmts_refines : ∀ (stmts : List MirStmt) {a c a' : CanonState Nat},
    StateRefines a c → execStmts a stmts = some a' →
    ∃ c', execStmts c stmts = some c' ∧ StateRefines a' c'
  | [], a, c, a', h, hExec => by
    dsimp only [execStmts] at hExec
    injection hExec with hA'
    subst hA'
    exact ⟨c, rfl, h⟩
  | stmt :: rest, a, c, a', h, hExec => by
    dsimp only [execStmts] at hExec ⊢
    cases hS : execStmt a stmt with
    | none => rw [hS] at hExec; cases hExec
    | some a₁ =>
      rw [hS] at hExec
      dsimp only at hExec
      rcases execStmt_refines h hS with ⟨c₁, hC₁, hR₁⟩
      rw [hC₁]
      exact execStmts_refines rest hR₁ hExec

/-- Length-preserving join-point pruning of a dense slot list against a liveness mask: slot
    `i` is kept when `mask[i] = true` (or when the mask is shorter than the slot list) and
    replaced by `Slot.kill` (dead, keeping its borrow-dirtied generation) when
    `mask[i] = false`. -/
def pruneSlots {Val : Type} : List Bool → List (Slot Val) → List (Slot Val)
  | [], ss => ss
  | _ :: _, [] => []
  | b :: bs, s :: ss => normalizeSlotForMask b s :: pruneSlots bs ss

/-- Join-point canonicalization of a dense `CanonState` (`CanonLocals` pruning). -/
def joinCanon {Val : Type} (mask : List Bool) (st : CanonState Val) : CanonState Val :=
  { slots := pruneSlots mask st.slots }

theorem pruneSlots_idempotent {Val : Type} : ∀ (mask : List Bool) (ss : List (Slot Val)),
    pruneSlots mask (pruneSlots mask ss) = pruneSlots mask ss
  | [], _ => rfl
  | _ :: _, [] => rfl
  | b :: bs, s :: ss => by
    simp only [pruneSlots]
    rw [normalizeSlotForMask_idempotent, pruneSlots_idempotent bs ss]

/-- `joinCanon` is idempotent (re-pruning a pruned state is a no-op). -/
theorem joinCanon_idempotent {Val : Type} (mask : List Bool) (st : CanonState Val) :
    joinCanon mask (joinCanon mask st) = joinCanon mask st := by
  dsimp only [joinCanon]
  rw [pruneSlots_idempotent]

theorem SlotRefines.normalize {a c : Slot Nat} (h : SlotRefines a c) (b : Bool) :
    SlotRefines (normalizeSlotForMask b a) c := by
  cases b with
  | true => exact h
  | false =>
    rcases h with h | h
    · subst h
      exact Or.inr rfl
    · subst h
      exact Or.inr (Slot.kill_idempotent c)

theorem pruneSlots_refines : ∀ (mask : List Bool) {as cs : List (Slot Nat)},
    SlotsRefine as cs → SlotsRefine (pruneSlots mask as) cs
  | [], _, _, h => h
  | _ :: _, [], [], _ => trivial
  | b :: bs, _ :: _, _ :: _, ⟨hH, hT⟩ => ⟨hH.normalize b, pruneSlots_refines bs hT⟩
  | _ :: _, [], _ :: _, h => False.elim h
  | _ :: _, _ :: _, [], h => False.elim h

/-- Pruning dead locals keeps a refined state refined (the abstract side only gets deader). -/
theorem StateRefines.joinCanon {a c : CanonState Nat} (h : StateRefines a c) (mask : List Bool) :
    StateRefines (joinCanon mask a) c :=
  pruneSlots_refines mask h

theorem map_pruneSlots (tbl : SymTable) (env : SymEnv) :
    ∀ (mask : List Bool) (ss : List (Slot SymId)),
      (pruneSlots mask ss).map (evalSymSlot tbl env) =
        pruneSlots mask (ss.map (evalSymSlot tbl env))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | b :: bs, s :: ss => by
    simp only [pruneSlots, List.map_cons]
    rw [map_pruneSlots tbl env bs ss]
    cases b with
    | true => rfl
    | false =>
      dsimp [normalizeSlotForMask]
      rw [evalSymSlot_kill]

theorem evalSymCanonState_joinCanon (tbl : SymTable) (env : SymEnv) (mask : List Bool)
    (st : CanonState SymId) :
    evalSymCanonState tbl env (joinCanon mask st) =
      joinCanon mask (evalSymCanonState tbl env st) := by
  dsimp only [evalSymCanonState, joinCanon]
  rw [map_pruneSlots]

theorem ValidSymSlots_pruneSlots {bound : Nat} : ∀ (mask : List Bool) {ss : List (Slot SymId)},
    ValidSymSlots bound ss → ValidSymSlots bound (pruneSlots mask ss)
  | [], _, h => h
  | _ :: _, [], _ => trivial
  | b :: bs, _ :: _, ⟨hH, hT⟩ => by
    refine ⟨?_, ValidSymSlots_pruneSlots bs hT⟩
    cases b with
    | true => exact hH
    | false => trivial

theorem ValidSymCanonState.joinCanon {bound : Nat} {st : CanonState SymId}
    (h : ValidSymCanonState bound st) (mask : List Bool) :
    ValidSymCanonState bound (joinCanon mask st) :=
  ValidSymSlots_pruneSlots mask h

/-!
### 3.4 Compositional Diamond Join (`symExecDiamondJoin`, `wpJoinBlock_sound`)
-/

/-- `goto` target of an arm block, if its terminator is a `goto`. -/
def armGoto? (blk : MirBlock) : Option BlockId :=
  match blk.term with
  | .goto j => some j
  | _ => none

theorem armGoto?_spec {blk : MirBlock} {j : BlockId} (h : armGoto? blk = some j) :
    blk.term = .goto j := by
  unfold armGoto? at h
  split at h
  · rename_i j' hTerm
    injection h with hj
    subst hj
    exact hTerm
  · cases h

/-- Recognize a `switchInt` diamond: both arm blocks exist and end in `goto` the same join
    block. Returns `(thenStmts, elseStmts, joinBb)`. -/
def matchDiamond (cfg : MirCfg) (thenBb elseBb : BlockId) :
    Option (List MirStmt × List MirStmt × BlockId) :=
  match cfg.blocks[thenBb]?, cfg.blocks[elseBb]? with
  | some tBlk, some eBlk =>
    match armGoto? tBlk, armGoto? eBlk with
    | some jT, some jF => if jT = jF then some (tBlk.stmts, eBlk.stmts, jT) else none
    | _, _ => none
  | _, _ => none

theorem matchDiamond_spec {cfg : MirCfg} {thenBb elseBb joinBb : BlockId}
    {thenStmts elseStmts : List MirStmt}
    (h : matchDiamond cfg thenBb elseBb = some (thenStmts, elseStmts, joinBb)) :
    ∃ tBlk eBlk, cfg.blocks[thenBb]? = some tBlk ∧ cfg.blocks[elseBb]? = some eBlk ∧
      tBlk.stmts = thenStmts ∧ eBlk.stmts = elseStmts ∧
      tBlk.term = .goto joinBb ∧ eBlk.term = .goto joinBb := by
  unfold matchDiamond at h
  split at h
  · rename_i tBlk eBlk hT hE
    split at h
    · rename_i jT jF hjT hjF
      split at h
      · rename_i hj
        subst hj
        injection h with h1
        injection h1 with hS1 h2
        injection h2 with hS2 hJ
        subst hS1 hS2 hJ
        exact ⟨tBlk, eBlk, hT, hE, rfl, rfl, armGoto?_spec hjT, armGoto?_spec hjF⟩
      · cases h
    · cases h
  · cases h

/-- Diamond merge plan: a recognized diamond whose join block carries a liveness hint. -/
def diamondMergePlan (cfg : MirCfg) (hints : JoinHints) (thenBb elseBb : BlockId) :
    Option (List MirStmt × List MirStmt × BlockId × List Bool) :=
  match matchDiamond cfg thenBb elseBb with
  | some (thenStmts, elseStmts, joinBb) =>
    match hints joinBb with
    | some mask => some (thenStmts, elseStmts, joinBb, mask)
    | none => none
  | none => none

theorem diamondMergePlan_spec {cfg : MirCfg} {hints : JoinHints} {thenBb elseBb joinBb : BlockId}
    {thenStmts elseStmts : List MirStmt} {mask : List Bool}
    (h : diamondMergePlan cfg hints thenBb elseBb = some (thenStmts, elseStmts, joinBb, mask)) :
    matchDiamond cfg thenBb elseBb = some (thenStmts, elseStmts, joinBb) := by
  unfold diamondMergePlan at h
  split at h
  · rename_i tS eS j hM
    split at h
    · injection h with h1
      injection h1 with hS1 h2
      injection h2 with hS2 h3
      injection h3 with hJ _
      subst hS1 hS2 hJ
      exact hM
    · cases h
  · cases h

/-- Execute both diamond arms symbolically from `(st, tbl)` under their respective branch
    path conditions (`some (condId, true)` for `thenStmts`, `some (condId, false)` for
    `elseStmts`), prune both post-states with the (untrusted) join mask, and merge them into
    ONE continuation state under `condId`. -/
def symExecDiamondJoin (st : CanonState SymId) (tbl : SymTable) (condId : SymId)
    (thenStmts elseStmts : List MirStmt) (mask : List Bool) :
    Option (CanonState SymId × SymTable) :=
  match symExecStmts st tbl thenStmts (some (condId, true)) with
  | none => none
  | some (stT, tbl₁) =>
    match symExecStmts st tbl₁ elseStmts (some (condId, false)) with
    | none => none
    | some (stF, tbl₂) => mergeJoinStates tbl₂ condId (joinCanon mask stT) (joinCanon mask stF)

/-- Alias for `symExecDiamondJoin` (`wpJoinDiamond`). -/
abbrev wpJoinDiamond := @symExecDiamondJoin

/-- **Compositional Join-Point Soundness (`wpJoinBlock_sound`)**: the single merged state
    `stM` produced by `symExecDiamondJoin` soundly abstracts — via `StateRefines` — the
    concrete post-state of whichever arm the concrete (mask-free) execution takes, from every
    concrete state refined by the evaluated entry state. The join continuation can therefore
    be analyzed **once**, from `stM`. -/
theorem wpJoinBlock_sound {st stM : CanonState SymId} {tbl tblM : SymTable} {condId : SymId}
    {thenStmts elseStmts : List MirStmt} {mask : List Bool}
    (hValid : ValidTable tbl) (hSt : ValidSymCanonState tbl.nodes.length st)
    (hCond : condId < tbl.nodes.length)
    (hJoin : symExecDiamondJoin st tbl condId thenStmts elseStmts mask = some (stM, tblM)) :
    ValidTable tblM ∧ tbl.Extends tblM ∧ ValidSymCanonState tblM.nodes.length stM ∧
      ∀ (env : SymEnv) (cst : CanonState Nat),
        StateRefines (evalSymCanonState tbl env st) cst →
        ∃ cst', execStmts cst (if evalSymId tbl env condId != 0 then thenStmts else elseStmts) =
            some cst' ∧
          StateRefines (evalSymCanonState tblM env stM) cst' := by
  unfold symExecDiamondJoin at hJoin
  cases hThen : symExecStmts st tbl thenStmts (some (condId, true)) with
  | none => rw [hThen] at hJoin; cases hJoin
  | some pT =>
    rcases pT with ⟨stT, tbl₁⟩
    rw [hThen] at hJoin
    dsimp only at hJoin
    rcases symExecStmts_under_sound thenStmts hValid hSt hThen hCond with
      ⟨hValid₁, hExt₁, hStT, hEvalT⟩
    have hSt₁ : ValidSymCanonState tbl₁.nodes.length st := ValidSymSlots.mono hSt hExt₁.length_le
    have hCond₁ : condId < tbl₁.nodes.length := Nat.lt_of_lt_of_le hCond hExt₁.length_le
    cases hElse : symExecStmts st tbl₁ elseStmts (some (condId, false)) with
    | none => rw [hElse] at hJoin; cases hJoin
    | some pF =>
      rcases pF with ⟨stF, tbl₂⟩
      rw [hElse] at hJoin
      dsimp only at hJoin
      rcases symExecStmts_under_sound elseStmts hValid₁ hSt₁ hElse hCond₁ with
        ⟨hValid₂, hExt₂, hStF, hEvalF⟩
      have hExt₀₂ : tbl.Extends tbl₂ := hExt₁.trans hExt₂
      have hCond₂ : condId < tbl₂.nodes.length := Nat.lt_of_lt_of_le hCond hExt₀₂.length_le
      have hStTc : ValidSymCanonState tbl₂.nodes.length (joinCanon mask stT) :=
        ValidSymSlots.mono (hStT.joinCanon mask) hExt₂.length_le
      have hStFc : ValidSymCanonState tbl₂.nodes.length (joinCanon mask stF) :=
        hStF.joinCanon mask
      rcases mergeJoinStates_eval hValid₂ hCond₂ hStTc hStFc hJoin with
        ⟨hValidM, hExtM, hStM, hEvalM⟩
      refine ⟨hValidM, hExt₀₂.trans hExtM, hStM, ?_⟩
      intro env cst hR
      rw [hEvalM env, ← evalSymId_mono hValid hExt₀₂ env hCond]
      cases hB : (evalSymId tbl env condId != 0) with
      | true =>
        rcases execStmts_refines thenStmts hR (hEvalT env hB) with ⟨cT, hCT, hRT⟩
        refine ⟨cT, by rw [ite_eq_left rfl]; exact hCT, ?_⟩
        rw [ite_eq_left rfl, ← evalSymCanonState_mono hValid₁ hExt₂ env (hStT.joinCanon mask),
          evalSymCanonState_joinCanon]
        exact hRT.joinCanon mask
      | false =>
        have hR₁ : StateRefines (evalSymCanonState tbl₁ env st) cst := by
          rw [← evalSymCanonState_mono hValid hExt₁ env hSt]
          exact hR
        have hB₁ : PathCondHolds tbl₁ env (some (condId, false)) := by
          dsimp [PathCondHolds]
          rw [← evalSymId_mono hValid hExt₁ env hCond]
          exact hB
        rcases execStmts_refines elseStmts hR₁ (hEvalF env hB₁) with ⟨cF, hCF, hRF⟩
        refine ⟨cF, by rw [ite_eq_right Bool.false_ne_true]; exact hCF, ?_⟩
        rw [ite_eq_right Bool.false_ne_true, evalSymCanonState_joinCanon]
        exact hRF.joinCanon mask

/-!
### 3.5 Single-Continuation Symbolic CFG Evaluator (`symEvalCfgGvn`) & End-to-End Soundness
-/

/-- Constant-folded branch condition: `some b` iff `condId` is interned as a constant. -/
def constCond? (tbl : SymTable) (condId : SymId) : Option Bool :=
  match tbl.nodes[condId]? with
  | some (.const v) => some (wrap64 v != 0)
  | _ => none

theorem constCond?_sound {tbl : SymTable} {condId : SymId} {b : Bool} (hValid : ValidTable tbl)
    (h : constCond? tbl condId = some b) (env : SymEnv) :
    (evalSymId tbl env condId != 0) = b := by
  unfold constCond? at h
  split at h
  · rename_i v hNode
    injection h with hb
    subst hb
    rw [evalSymId_eq_evalSymNodeWith hValid env hNode]
    rfl
  · cases h

/-- Combine the explorations of both successors of a *path-split* (non-merged) `switchInt`,
    threading the append-only table from the `then` exploration into the `else` one. -/
def combineSplit (resT : Option (List SymId × SymTable))
    (resF : SymTable → Option (List SymId × SymTable)) : Option (List SymId × SymTable) :=
  match resT with
  | none => none
  | some (retsT, tblT) =>
    match resF tblT with
    | none => none
    | some (retsF, tblF) => some (retsT ++ retsF, tblF)

theorem combineSplit_eq_some {resT : Option (List SymId × SymTable)}
    {resF : SymTable → Option (List SymId × SymTable)} {rets : List SymId} {tbl' : SymTable}
    (h : combineSplit resT resF = some (rets, tbl')) :
    ∃ retsT tblT retsF, resT = some (retsT, tblT) ∧ resF tblT = some (retsF, tbl') ∧
      rets = retsT ++ retsF := by
  unfold combineSplit at h
  cases hT : resT with
  | none => rw [hT] at h; cases h
  | some pT =>
    rcases pT with ⟨retsT, tblT⟩
    rw [hT] at h
    dsimp only at h
    cases hF : resF tblT with
    | none => rw [hF] at h; cases h
    | some pF =>
      rcases pF with ⟨retsF, tblF⟩
      rw [hF] at h
      dsimp only at h
      injection h with h1
      injection h1 with hR hTb
      subst hR hTb
      exact ⟨retsT, tblT, retsF, rfl, hF, rfl⟩

/-- Single-continuation compositional symbolic GVN evaluator for multi-block `MirCfg`s.
    Returns the list of returned `SymId`s (one per explored path) in the final append-only
    table. At a symbolic `switchInt` whose arms form a diamond with a hinted join block, both
    arms are executed, pruned with the join mask (`joinCanon`), merged (`mergeJoinStates`,
    GVN + `ite c v v ↦ v`), and the join continuation is evaluated **once** (consuming one
    extra unit of fuel for the arm block, exactly as the concrete execution does). Without a
    hint it path-splits. CPS spine forcing (`forceCanonState`) is applied at every block. -/
def symEvalCfgGvn (cfg : MirCfg) (hints : JoinHints) :
    Nat → BlockId → CanonState SymId → SymTable → (pc : PathCond := none) →
      Option (List SymId × SymTable)
  | 0, _, _, _, _ => none
  | fuel + 1, bb, st, tbl, pc =>
    match cfg.blocks[bb]? with
    | none => none
    | some blk =>
      match symExecStmts st tbl blk.stmts pc with
      | none => none
      | some (st₀, tbl₁) =>
        forceCanonState st₀ fun st₁ =>
        match blk.term with
        | .goto target => symEvalCfgGvn cfg hints fuel target st₁ tbl₁ pc
        | .switchInt discr thenBb elseBb =>
          match readSymScalar st₁ discr with
          | none => none
          | some condId =>
            let st₂ := st₁.ownerReadLoc discr
            match constCond? tbl₁ condId with
            | some b =>
              if b then symEvalCfgGvn cfg hints fuel thenBb st₂ tbl₁ pc
              else symEvalCfgGvn cfg hints fuel elseBb st₂ tbl₁ pc
            | none =>
              match diamondMergePlan cfg hints thenBb elseBb with
              | some (thenStmts, elseStmts, joinBb, mask) =>
                match fuel with
                | 0 => none
                | f + 1 =>
                  match symExecDiamondJoin st₂ tbl₁ condId thenStmts elseStmts mask with
                  | none => none
                  | some (stM, tblM) => symEvalCfgGvn cfg hints f joinBb stM tblM pc
              | none =>
                combineSplit (symEvalCfgGvn cfg hints fuel thenBb st₂ tbl₁ (some (condId, true)))
                  (fun tblT => symEvalCfgGvn cfg hints fuel elseBb st₂ tblT (some (condId, false)))
        | .ret retLoc =>
          match readSymScalar st₁ retLoc with
          | some retSymId => some ([retSymId], tbl₁)
          | none => none
        | .unreachable => none

/-- Path-sensitive soundness obligation for a symbolic CFG result `(rets, tbl')` under `pc`. -/
def CfgResultSoundUnder (cfg : MirCfg) (fuel : Nat) (bb : BlockId) (st : CanonState SymId)
    (tbl : SymTable) (pc : PathCond) (rets : List SymId) (tbl' : SymTable) : Prop :=
  ValidTable tbl' ∧ tbl.Extends tbl' ∧ (∀ r ∈ rets, r < tbl'.nodes.length) ∧
    ∀ (env : SymEnv) (cst : CanonState Nat),
      PathCondHolds tbl env pc →
      StateRefines (evalSymCanonState tbl env st) cst →
      ∃ r ∈ rets, execCfg cfg fuel bb cst = .ret (evalSymId tbl' env r)

/-- Soundness obligation for a symbolic CFG result `(rets, tbl')` from `(bb, st, tbl)`: the
    final table is a valid extension, every returned `SymId` is allocated, and from **every**
    concrete state refined by the evaluated entry state, the mask-free concrete execution with
    the same fuel returns (no fault, no fuel exhaustion) the value of some returned `SymId`. -/
def CfgResultSound (cfg : MirCfg) (fuel : Nat) (bb : BlockId) (st : CanonState SymId)
    (tbl : SymTable) (rets : List SymId) (tbl' : SymTable) : Prop :=
  ValidTable tbl' ∧ tbl.Extends tbl' ∧ (∀ r ∈ rets, r < tbl'.nodes.length) ∧
    ∀ (env : SymEnv) (cst : CanonState Nat),
      StateRefines (evalSymCanonState tbl env st) cst →
      ∃ r ∈ rets, execCfg cfg fuel bb cst = .ret (evalSymId tbl' env r)

/-- **Path-Sensitive Symbolic CFG Soundness (`symEvalCfgGvn_under_sound`)**, for every
    (untrusted) `hints` and active branch path condition `pc`. -/
theorem symEvalCfgGvn_under_sound (cfg : MirCfg) (hints : JoinHints) :
    ∀ (fuel : Nat) (bb : BlockId) (st : CanonState SymId) (tbl : SymTable) (pc : PathCond)
      (rets : List SymId) (tbl' : SymTable),
      ValidTable tbl →
      ValidSymCanonState tbl.nodes.length st →
      PathCondValid tbl.nodes.length pc →
      symEvalCfgGvn cfg hints fuel bb st tbl pc = some (rets, tbl') →
      CfgResultSoundUnder cfg fuel bb st tbl pc rets tbl'
  | 0, _, _, _, _, _, _, _, _, _, hEval => by cases hEval
  | fuel + 1, bb, st, tbl, pc, rets, tbl', hValid, hSt, hPcValid, hEval => by
    rw [symEvalCfgGvn] at hEval
    cases hBlk : cfg.blocks[bb]? with
    | none => rw [hBlk] at hEval; cases hEval
    | some blk =>
      rw [hBlk] at hEval
      dsimp only at hEval
      cases hStmts : symExecStmts st tbl blk.stmts pc with
      | none => rw [hStmts] at hEval; cases hEval
      | some pair₁ =>
        rcases pair₁ with ⟨st₁, tbl₁⟩
        rw [hStmts] at hEval
        dsimp only at hEval
        rw [forceCanonState_eq] at hEval
        rcases symExecStmts_under_sound blk.stmts hValid hSt hStmts hPcValid with
          ⟨hValid₁, hExt₁, hSt₁, hEvalStmts⟩
        have hPcValid₁ : PathCondValid tbl₁.nodes.length pc := hPcValid.mono hExt₁.length_le
        have hPrefix : ∀ env cst, PathCondHolds tbl env pc →
            StateRefines (evalSymCanonState tbl env st) cst →
            ∃ c₁, execStmts cst blk.stmts = some c₁ ∧
              StateRefines (evalSymCanonState tbl₁ env st₁) c₁ ∧
              PathCondHolds tbl₁ env pc :=
          fun env _ hPc hR =>
            let ⟨c₁, hC₁, hR₁⟩ := execStmts_refines blk.stmts hR (hEvalStmts env hPc)
            ⟨c₁, hC₁, hR₁, PathCondHolds.mono hValid hExt₁ hPcValid hPc⟩
        cases hTerm : blk.term with
        | goto target =>
          rw [hTerm] at hEval
          rcases symEvalCfgGvn_under_sound cfg hints fuel target st₁ tbl₁ pc rets tbl'
            hValid₁ hSt₁ hPcValid₁ hEval with ⟨hV', hE', hLt', hEv'⟩
          refine ⟨hV', hExt₁.trans hE', hLt', ?_⟩
          intro env cst hPc hR
          rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
          rcases hEv' env c₁ hPc₁ hR₁ with ⟨r, hr, hExec⟩
          refine ⟨r, hr, ?_⟩
          dsimp only [execCfg]
          rw [hBlk]
          dsimp only
          rw [hC₁]
          dsimp only
          rw [hTerm]
          exact hExec
        | switchInt discr thenBb elseBb =>
          rw [hTerm] at hEval
          dsimp only at hEval
          cases hDiscr : readSymScalar st₁ discr with
          | none => rw [hDiscr] at hEval; cases hEval
          | some condId =>
            rw [hDiscr] at hEval
            dsimp only at hEval
            have hCondLt : condId < tbl₁.nodes.length := by
              have hSpec := readSymScalar_spec (fun _ => 0) hSt₁ (loc := discr)
              rw [hDiscr] at hSpec
              exact hSpec.1
            -- Reading the discriminant is an owner read: both successors start from `st₂`.
            have hSt₂ : ValidSymCanonState tbl₁.nodes.length (st₁.ownerReadLoc discr) :=
              hSt₁.ownerReadLoc discr
            have hR₂ : ∀ env c₁, StateRefines (evalSymCanonState tbl₁ env st₁) c₁ →
                StateRefines (evalSymCanonState tbl₁ env (st₁.ownerReadLoc discr))
                  (c₁.ownerReadLoc discr) := by
              intro env c₁ hR₁
              rw [evalSymCanonState_ownerReadLoc]
              exact hR₁.ownerReadLoc discr
            have hStepC : ∀ env cst c₁, execStmts cst blk.stmts = some c₁ →
                StateRefines (evalSymCanonState tbl₁ env st₁) c₁ →
                execCfg cfg (fuel + 1) bb cst =
                  (if evalSymId tbl₁ env condId != 0 then
                      execCfg cfg fuel thenBb (c₁.ownerReadLoc discr)
                    else execCfg cfg fuel elseBb (c₁.ownerReadLoc discr)) := by
              intro env cst c₁ hC₁ hR₁
              have hSpec := readSymScalar_spec env hSt₁ (loc := discr)
              rw [hDiscr] at hSpec
              dsimp only [execCfg]
              rw [hBlk]
              dsimp only
              rw [hC₁]
              dsimp only
              rw [hTerm]
              dsimp only
              rw [readConcreteScalar_refines hR₁ hSpec.2]
            have hSplitCase : combineSplit
                (symEvalCfgGvn cfg hints fuel thenBb (st₁.ownerReadLoc discr) tbl₁
                  (some (condId, true)))
                (fun tblT => symEvalCfgGvn cfg hints fuel elseBb (st₁.ownerReadLoc discr) tblT
                  (some (condId, false))) =
                  some (rets, tbl') →
                CfgResultSoundUnder cfg (fuel + 1) bb st tbl pc rets tbl' := by
              intro hComb
              rcases combineSplit_eq_some hComb with ⟨retsT, tblT, retsF, hT, hF, hRets⟩
              subst hRets
              rcases symEvalCfgGvn_under_sound cfg hints fuel thenBb (st₁.ownerReadLoc discr) tbl₁
                (some (condId, true)) retsT tblT hValid₁ hSt₂ hCondLt hT with
                ⟨hVT, hET, hLtT, hEvT⟩
              have hSt₂T : ValidSymCanonState tblT.nodes.length (st₁.ownerReadLoc discr) :=
                ValidSymSlots.mono hSt₂ hET.length_le
              have hCondLtT : PathCondValid tblT.nodes.length (some (condId, false)) :=
                Nat.lt_of_lt_of_le hCondLt hET.length_le
              rcases symEvalCfgGvn_under_sound cfg hints fuel elseBb (st₁.ownerReadLoc discr) tblT
                (some (condId, false)) retsF tbl' hVT hSt₂T hCondLtT hF with
                ⟨hVF, hEF, hLtF, hEvF⟩
              refine ⟨hVF, (hExt₁.trans hET).trans hEF, ?_, ?_⟩
              · intro r hr
                rcases List.mem_append.1 hr with hr | hr
                · exact Nat.lt_of_lt_of_le (hLtT r hr) hEF.length_le
                · exact hLtF r hr
              · intro env cst hPc hR
                rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, _⟩
                rw [hStepC env cst c₁ hC₁ hR₁]
                cases hB : (evalSymId tbl₁ env condId != 0) with
                | true =>
                  rcases hEvT env (c₁.ownerReadLoc discr) hB (hR₂ env c₁ hR₁) with ⟨r, hr, hExec⟩
                  refine ⟨r, List.mem_append_left _ hr, ?_⟩
                  rw [ite_eq_left rfl, hExec, evalSymId_mono hVT hEF env (hLtT r hr)]
                | false =>
                  have hR₂T : StateRefines (evalSymCanonState tblT env (st₁.ownerReadLoc discr))
                      (c₁.ownerReadLoc discr) := by
                    rw [← evalSymCanonState_mono hValid₁ hET env hSt₂]
                    exact hR₂ env c₁ hR₁
                  have hPcF : PathCondHolds tblT env (some (condId, false)) := by
                    dsimp [PathCondHolds]
                    rw [← evalSymId_mono hValid₁ hET env hCondLt]
                    exact hB
                  rcases hEvF env (c₁.ownerReadLoc discr) hPcF hR₂T with ⟨r, hr, hExec⟩
                  refine ⟨r, List.mem_append_right _ hr, ?_⟩
                  rw [ite_eq_right Bool.false_ne_true, hExec]
            cases hC : constCond? tbl₁ condId with
            | some b =>
              rw [hC] at hEval
              dsimp only at hEval
              have hB := constCond?_sound hValid₁ hC
              cases b with
              | true =>
                rw [ite_eq_left rfl] at hEval
                rcases symEvalCfgGvn_under_sound cfg hints fuel thenBb (st₁.ownerReadLoc discr) tbl₁
                  pc rets tbl' hValid₁ hSt₂ hPcValid₁ hEval with ⟨hV', hE', hLt', hEv'⟩
                refine ⟨hV', hExt₁.trans hE', hLt', ?_⟩
                intro env cst hPc hR
                rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                rcases hEv' env (c₁.ownerReadLoc discr) hPc₁ (hR₂ env c₁ hR₁) with ⟨r, hr, hExec⟩
                refine ⟨r, hr, ?_⟩
                rw [hStepC env cst c₁ hC₁ hR₁, hB env, ite_eq_left rfl]
                exact hExec
              | false =>
                rw [ite_eq_right Bool.false_ne_true] at hEval
                rcases symEvalCfgGvn_under_sound cfg hints fuel elseBb (st₁.ownerReadLoc discr) tbl₁
                  pc rets tbl' hValid₁ hSt₂ hPcValid₁ hEval with ⟨hV', hE', hLt', hEv'⟩
                refine ⟨hV', hExt₁.trans hE', hLt', ?_⟩
                intro env cst hPc hR
                rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                rcases hEv' env (c₁.ownerReadLoc discr) hPc₁ (hR₂ env c₁ hR₁) with ⟨r, hr, hExec⟩
                refine ⟨r, hr, ?_⟩
                rw [hStepC env cst c₁ hC₁ hR₁, hB env, ite_eq_right Bool.false_ne_true]
                exact hExec
            | none =>
              rw [hC] at hEval
              dsimp only at hEval
              cases hPlan : diamondMergePlan cfg hints thenBb elseBb with
              | none =>
                rw [hPlan] at hEval
                exact hSplitCase hEval
              | some plan =>
                rcases plan with ⟨thenStmts, elseStmts, joinBb, mask⟩
                rw [hPlan] at hEval
                cases fuel with
                | zero => cases hEval
                | succ f =>
                  dsimp only at hEval
                  cases hJoin : symExecDiamondJoin (st₁.ownerReadLoc discr) tbl₁ condId thenStmts
                      elseStmts mask with
                  | none => rw [hJoin] at hEval; cases hEval
                  | some pM =>
                    rcases pM with ⟨stM, tblM⟩
                    rw [hJoin] at hEval
                    dsimp only at hEval
                    rcases wpJoinBlock_sound hValid₁ hSt₂ hCondLt hJoin with
                      ⟨hVM, hEM, hStM, hJoinC⟩
                    have hPcValidM : PathCondValid tblM.nodes.length pc :=
                      hPcValid₁.mono hEM.length_le
                    rcases symEvalCfgGvn_under_sound cfg hints f joinBb stM tblM pc rets tbl'
                      hVM hStM hPcValidM hEval with ⟨hV', hE', hLt', hEv'⟩
                    rcases matchDiamond_spec (diamondMergePlan_spec hPlan) with
                      ⟨tBlk, eBlk, hTB, hEB, hTS, hES, hTT, hET⟩
                    refine ⟨hV', (hExt₁.trans hEM).trans hE', hLt', ?_⟩
                    intro env cst hPc hR
                    rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, hPc₁⟩
                    rcases hJoinC env (c₁.ownerReadLoc discr) (hR₂ env c₁ hR₁) with
                      ⟨c₂, hC₂, hR₂'⟩
                    have hPcM : PathCondHolds tblM env pc :=
                      PathCondHolds.mono hValid₁ hEM hPcValid₁ hPc₁
                    rcases hEv' env c₂ hPcM hR₂' with ⟨r, hr, hExec⟩
                    refine ⟨r, hr, ?_⟩
                    rw [hStepC env cst c₁ hC₁ hR₁]
                    cases hB : (evalSymId tbl₁ env condId != 0) with
                    | true =>
                      rw [hB, ite_eq_left rfl] at hC₂
                      rw [ite_eq_left rfl]
                      dsimp only [execCfg]
                      rw [hTB]
                      dsimp only
                      rw [hTS, hC₂]
                      dsimp only
                      rw [hTT]
                      exact hExec
                    | false =>
                      rw [hB, ite_eq_right Bool.false_ne_true] at hC₂
                      rw [ite_eq_right Bool.false_ne_true]
                      dsimp only [execCfg]
                      rw [hEB]
                      dsimp only
                      rw [hES, hC₂]
                      dsimp only
                      rw [hET]
                      exact hExec
        | ret retLoc =>
          rw [hTerm] at hEval
          dsimp only at hEval
          cases hRet : readSymScalar st₁ retLoc with
          | none => rw [hRet] at hEval; cases hEval
          | some rId =>
            rw [hRet] at hEval
            dsimp only at hEval
            injection hEval with hPair
            injection hPair with hR hT
            subst hR hT
            have hSpec0 := readSymScalar_spec (fun _ => 0) hSt₁ (loc := retLoc)
            rw [hRet] at hSpec0
            refine ⟨hValid₁, hExt₁, ?_, ?_⟩
            · intro r hr
              rw [List.mem_singleton] at hr
              subst hr
              exact hSpec0.1
            · intro env cst hPc hR
              rcases hPrefix env cst hPc hR with ⟨c₁, hC₁, hR₁, _⟩
              have hSpec := readSymScalar_spec env hSt₁ (loc := retLoc)
              rw [hRet] at hSpec
              refine ⟨rId, List.mem_singleton.2 rfl, ?_⟩
              dsimp only [execCfg]
              rw [hBlk]
              dsimp only
              rw [hC₁]
              dsimp only
              rw [hTerm]
              dsimp only
              rw [readConcreteScalar_refines hR₁ hSpec.2]
        | unreachable =>
          rw [hTerm] at hEval
          cases hEval

/-- **End-to-End Symbolic CFG Soundness (`symEvalCfgGvn_sound`)**, for every (untrusted)
    `hints` (`pc = none`). -/
theorem symEvalCfgGvn_sound (cfg : MirCfg) (hints : JoinHints)
    (fuel : Nat) (bb : BlockId) (st : CanonState SymId) (tbl : SymTable)
    (rets : List SymId) (tbl' : SymTable)
    (hValid : ValidTable tbl)
    (hSt : ValidSymCanonState tbl.nodes.length st)
    (hEval : symEvalCfgGvn cfg hints fuel bb st tbl = some (rets, tbl')) :
    CfgResultSound cfg fuel bb st tbl rets tbl' := by
  rcases symEvalCfgGvn_under_sound cfg hints fuel bb st tbl none rets tbl' hValid hSt trivial hEval
    with ⟨hV, hE, hLt, hEv⟩
  exact ⟨hV, hE, hLt, fun env cst hR => hEv env cst trivial hR⟩

/-- Symbolic GVN + Canonical-Join Weakest Precondition (`wpCfgSymGvn`): evaluates `cfg`
    symbolically once and requires `post` of every returned `SymId` for all `env`. -/
def wpCfgSymGvn (cfg : MirCfg) (hints : JoinHints) (fuel : Nat) (bb : BlockId)
    (st : CanonState SymId) (tbl : SymTable) (post : SymEnv → Nat → Prop) : Prop :=
  match symEvalCfgGvn cfg hints fuel bb st tbl with
  | none => False
  | some (rets, tbl') => ∀ env : SymEnv, ∀ r ∈ rets, post env (evalSymId tbl' env r)

/-- **End-to-End WP Soundness (`wpCfgSymGvn_sound`)**: for every (untrusted) join hint map, if
    `wpCfgSymGvn` holds then, for every `env` and every concrete state refined by the evaluated
    symbolic entry state, the **mask-free** concrete execution never faults (no assertion
    failure, no read/write of a dead or uninitialized local, no stale-generation loan), never
    runs out of fuel, and returns a value satisfying `post`. -/
theorem wpCfgSymGvn_sound {cfg : MirCfg} {hints : JoinHints} {fuel : Nat} {bb : BlockId}
    {st : CanonState SymId} {tbl : SymTable} {post : SymEnv → Nat → Prop}
    (hValid : ValidTable tbl) (hSt : ValidSymCanonState tbl.nodes.length st)
    (hWp : wpCfgSymGvn cfg hints fuel bb st tbl post) :
    ∀ (env : SymEnv) (cst : CanonState Nat), StateRefines (evalSymCanonState tbl env st) cst →
      ∃ retVal : Nat, execCfg cfg fuel bb cst = .ret retVal ∧ post env retVal := by
  unfold wpCfgSymGvn at hWp
  cases hSym : symEvalCfgGvn cfg hints fuel bb st tbl with
  | none =>
    rw [hSym] at hWp
    exact False.elim hWp
  | some pair =>
    rcases pair with ⟨rets, tbl'⟩
    rw [hSym] at hWp
    rcases symEvalCfgGvn_sound cfg hints fuel bb st tbl rets tbl' hValid hSt hSym with
      ⟨_, _, _, hExec⟩
    intro env cst hR
    rcases hExec env cst hR with ⟨r, hr, hRet⟩
    exact ⟨_, hRet, hWp env r hr⟩

/-- `wpCfgSymGvn_sound` specialized to the exact evaluated symbolic entry state. -/
theorem wpCfgSymGvn_sound_init {cfg : MirCfg} {hints : JoinHints} {fuel : Nat} {bb : BlockId}
    {st : CanonState SymId} {tbl : SymTable} {post : SymEnv → Nat → Prop}
    (hValid : ValidTable tbl) (hSt : ValidSymCanonState tbl.nodes.length st)
    (hWp : wpCfgSymGvn cfg hints fuel bb st tbl post) (env : SymEnv) :
    ∃ retVal : Nat, execCfg cfg fuel bb (evalSymCanonState tbl env st) = .ret retVal ∧
      post env retVal :=
  wpCfgSymGvn_sound hValid hSt hWp env _ (StateRefines.refl _)

/-- Executable verification checker: run `symEvalCfgGvn`, GVN-intern the functional spec tree
    into the final table, and accept iff every returned `SymId` is GVN-identical to the spec's
    `SymId` (sound, incomplete syntactic equivalence check). -/
def checkCfgAgainstTree (cfg : MirCfg) (hints : JoinHints) (fuel : Nat) (bb : BlockId)
    (st : CanonState SymId) (tbl : SymTable) (spec : ExprTree) : Bool :=
  match symEvalCfgGvn cfg hints fuel bb st tbl with
  | none => false
  | some (rets, tbl') => rets.all (fun r => r == (internTree tbl' spec).1)

/-- **Checker Soundness (`checkCfgAgainstTree_sound`)**: an accepted check proves that the
    mask-free concrete execution returns exactly `spec.eval env` for every `env` and every
    refined concrete state. -/
theorem checkCfgAgainstTree_sound {cfg : MirCfg} {hints : JoinHints} {fuel : Nat} {bb : BlockId}
    {st : CanonState SymId} {tbl : SymTable} {spec : ExprTree}
    (hCheck : checkCfgAgainstTree cfg hints fuel bb st tbl spec = true)
    (hValid : ValidTable tbl) (hSt : ValidSymCanonState tbl.nodes.length st) :
    ∀ (env : SymEnv) (cst : CanonState Nat), StateRefines (evalSymCanonState tbl env st) cst →
      execCfg cfg fuel bb cst = .ret (spec.eval env) := by
  unfold checkCfgAgainstTree at hCheck
  cases hSym : symEvalCfgGvn cfg hints fuel bb st tbl with
  | none => rw [hSym] at hCheck; cases hCheck
  | some pair =>
    rcases pair with ⟨rets, tbl'⟩
    rw [hSym] at hCheck
    dsimp only at hCheck
    rcases symEvalCfgGvn_sound cfg hints fuel bb st tbl rets tbl' hValid hSt hSym with
      ⟨hV', _, hLt', hExec⟩
    rcases internTree_spec spec tbl' hV' with ⟨_, hExtS, _, hEvalS⟩
    intro env cst hR
    rcases hExec env cst hR with ⟨r, hr, hRet⟩
    have hrEq : r = (internTree tbl' spec).1 := beq_iff_eq.1 (List.all_eq_true.1 hCheck r hr)
    rw [hRet, evalSymId_mono hV' hExtS env (hLt' r hr), hrEq, hEvalS env]

/-!
### 3.6 Kernel-Checked `k`-Diamond Multi-Block CFG Benchmarks & Fault Witnesses (`by rfl`)
-/

/-- Diamond `i` of the benchmark CFG (blocks `3i`, `3i+1`, `3i+2`, joining at `3i+3`):
    - head `3i`: `switchInt _1 → 3i+1 | 3i+2` (symbolic discriminant `_1`),
    - then-arm `3i+1`: `StorageLive(_2); _2 := xor(_0, i+1); _0 := _2 + _2; goto 3i+3` — the
      branch-local temporary `_2` is left **live**, so the two arm states differ at the join
      (`_2` live vs. dead) and only join-point pruning (`_2 ∉` live mask) lets them merge,
    - else-arm `3i+2`: `_0 := xor(_0, i+1); _0 := _0 + _0; goto 3i+3` (never touches `_2`). -/
def mkDiamondBlocks (i : Nat) : List MirBlock :=
  [ { stmts := [], term := .switchInt 1 (3 * i + 1) (3 * i + 2) },
    { stmts := [ .storageLive 2, .assign 2 (.op1 (.xorConst (i + 1)) 0),
        .assign 0 (.op2 .add 2 2) ]
      term := .goto (3 * i + 3) },
    { stmts := [ .assign 0 (.op1 (.xorConst (i + 1)) 0), .assign 0 (.op2 .add 0 0) ]
      term := .goto (3 * i + 3) } ]

/-- `count` diamonds starting at diamond index `i`, followed by a return block that checks a
    GVN-recognizable reflexive assertion (`_2 := _0 == _0; assert _2`) and returns `_0`. -/
def mkDiamondBlocksAux : Nat → Nat → List MirBlock
  | _, 0 =>
    [ { stmts := [ .storageLive 2, .assign 2 (.op2 .eq 0 0), .assert 2, .storageDead 2 ]
        term := .ret 0 } ]
  | i, count + 1 => mkDiamondBlocks i ++ mkDiamondBlocksAux (i + 1) count

/-- The `k`-diamond MIR CFG (`3k + 1` blocks, `2^k` concrete paths). -/
def mkDiamondCfg (k : Nat) : MirCfg :=
  { blocks := mkDiamondBlocksAux 0 k }

/-- Untrusted join hints for `mkDiamondCfg`: every join block `3(i+1)` gets live mask
    `[true, true, false]` (`_0`, `_1` live; `_2` dead). -/
def diamondJoinHints : JoinHints := fun bb =>
  if bb % 3 == 0 && bb != 0 then some [true, true, false] else none

/-- No hints at all: the evaluator path-splits every diamond (`2^k` paths, GVN still shared). -/
def noJoinHints : JoinHints := fun _ => none

/-- Hints that keep every local live (no pruning): merging fails on the `_2` shape mismatch. -/
def noPruneJoinHints : JoinHints := fun bb =>
  if bb % 3 == 0 && bb != 0 then some [true, true, true] else none

/-- Initial symbolic state: `_0 ↦ SymId 0 (.var 0)`, `_1 ↦ SymId 1 (.var 1)`, `_2` dead. -/
def diamondInitSymState : CanonState SymId :=
  { slots := [.live 0 0 false none, .live 1 0 false none, .dead 0] }

def diamondInitSymTable : SymTable :=
  { nodes := [.var 0, .var 1] }

theorem diamondInitSymTable_valid : ValidTable diamondInitSymTable := by
  intro idx node hGet
  cases idx with
  | zero =>
    dsimp [diamondInitSymTable] at hGet
    injection hGet with hEq
    subst hEq
    trivial
  | succ i =>
    cases i with
    | zero =>
      dsimp [diamondInitSymTable] at hGet
      injection hGet with hEq
      subst hEq
      trivial
    | succ j =>
      dsimp [diamondInitSymTable] at hGet
      cases hGet

theorem diamondInitSymState_valid :
    ValidSymCanonState diamondInitSymTable.nodes.length diamondInitSymState :=
  ⟨Nat.zero_lt_succ 1, Nat.lt_succ_self 1, trivial, trivial⟩

/-- **5-Diamond Verification Benchmark (`diamond5_verified_rfl`)**: one symbolic pass
    (`2 * 5 + 1 = 11` blocks of fuel) proves the 5-diamond CFG (`2^5 = 32` concrete paths)
    returns exactly `(buildDiamondTree 5).eval env`. -/
theorem diamond5_verified_rfl :
    checkCfgAgainstTree (mkDiamondCfg 5) diamondJoinHints 11 0 diamondInitSymState
      diamondInitSymTable (buildDiamondTree 5) = true := by
  decide +kernel

/-- **6-Diamond Verification Benchmark (`diamond6_verified_rfl`)**: one symbolic pass verifies
    the 6-diamond CFG (`2^6 = 64` concrete paths) against `buildDiamondTree 6`. -/
theorem diamond6_verified_rfl :
    checkCfgAgainstTree (mkDiamondCfg 6) diamondJoinHints 13 0 diamondInitSymState
      diamondInitSymTable (buildDiamondTree 6) = true := by
  decide +kernel

/-- Single-continuation vs. path-splitting shape witness at `k = 6`: with join hints the
    evaluator returns **1** path and a `15`-node table; without hints it explores all **64**
    paths (GVN keeps the table at `15` nodes); with non-pruning hints the merge is rejected
    (`_2` is live in one arm and dead in the other), so join-point pruning is load-bearing. -/
theorem diamond6_join_vs_split_witness :
    (symEvalCfgGvn (mkDiamondCfg 6) diamondJoinHints 13 0 diamondInitSymState
        diamondInitSymTable).map (fun res => (res.1.length, res.2.nodes.length)) = some (1, 15) ∧
      (symEvalCfgGvn (mkDiamondCfg 6) noJoinHints 13 0 diamondInitSymState
        diamondInitSymTable).map (fun res => (res.1.length, res.2.nodes.length)) = some (64, 15) ∧
      symEvalCfgGvn (mkDiamondCfg 6) noPruneJoinHints 13 0 diamondInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- **End-to-End Concrete Corollary (`diamond6_cfg_concrete_sound`)**: for every `env`, the
    mask-free concrete execution of the 6-diamond CFG returns `(buildDiamondTree 6).eval env`. -/
theorem diamond6_cfg_concrete_sound (env : SymEnv) :
    execCfg (mkDiamondCfg 6) 13 0 (evalSymCanonState diamondInitSymTable env diamondInitSymState) =
      .ret ((buildDiamondTree 6).eval env) :=
  checkCfgAgainstTree_sound diamond6_verified_rfl diamondInitSymTable_valid
    diamondInitSymState_valid env _ (StateRefines.refl _)

/-- Diamond whose arms compute the same sum with swapped operands:
    then-arm `_0 := _0 + _1`, else-arm `_0 := _1 + _0`. -/
def commDiamondCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchInt 1 1 2 },
        { stmts := [ .assign 0 (.op2 .add 0 1) ], term := .goto 3 },
        { stmts := [ .assign 0 (.op2 .add 1 0) ], term := .goto 3 },
        { stmts := [], term := .ret 0 } ] }

/-- **Commutative GVN at a Join (`commDiamond_shared_join_witness`)**: thanks to canonical
    operand order both arms intern the *same* `SymId` for `_0`, so the merge allocates no `ite`
    node (table stays at `3` nodes) and the program verifies against `x₁ + x₀`. -/
theorem commDiamond_shared_join_witness :
    (symEvalCfgGvn commDiamondCfg (fun _ => some [true, true, false]) 3 0 diamondInitSymState
        diamondInitSymTable).map (fun res => (res.1, res.2.nodes.length)) = some ([2], 3) ∧
      checkCfgAgainstTree commDiamondCfg (fun _ => some [true, true, false]) 3 0
        diamondInitSymState diamondInitSymTable (.op2 .add (.var 1) (.var 0)) = true := by
  decide +kernel

/-- 4-local initial state for the fault / borrow witnesses: `_0`, `_1` live inputs, `_2`, `_3`
    declared but uninitialized. -/
def borrowInitSymState : CanonState SymId :=
  { slots := [.live 0 0 false none, .live 1 0 false none, .uninit 0, .uninit 0] }

theorem borrowInitSymState_valid :
    ValidSymCanonState diamondInitSymTable.nodes.length borrowInitSymState :=
  ⟨Nat.zero_lt_succ 1, Nat.lt_succ_self 1, trivial, trivial, trivial⟩

/-- Writes `_1` after `StorageDead(_1)` (use-after-dead write). -/
def deadWriteCfg : MirCfg :=
  { blocks := [ { stmts := [.storageDead 1, .assign 1 (.const 7)], term := .ret 0 } ] }

/-- Takes `_2 := &_1`, recycles `_1`'s storage (`StorageDead`/`StorageLive`), re-borrows the
    new incarnation (`_3 := &_1`), then dereferences the **stale** loan `_2`. -/
def staleLoanCfg : MirCfg :=
  { blocks := [ { stmts := [ .retagBorrow 2 1, .storageDead 1, .storageLive 1,
      .assign 1 (.const 5), .retagBorrow 3 1, .assign 0 (.derefRef 2) ], term := .ret 0 } ] }

/-- Fresh-loan dereference: `_2 := &_1; _0 := *_2; return _0`. -/
def freshLoanCfg : MirCfg :=
  { blocks := [ { stmts := [ .retagBorrow 2 1, .assign 0 (.derefRef 2) ], term := .ret 0 } ] }

/-- **Fault Non-Vacuity Witnesses**: the concrete semantics genuinely faults on a dead-local
    write and on a stale-generation dereference (even after the target is re-borrowed, so the
    borrow flag alone would not catch it), the symbolic evaluator rejects both programs, and
    a fresh loan verifies (returns `_1`). -/
theorem fault_and_loan_witnesses :
    execCfg deadWriteCfg 1 0 (evalSymCanonState diamondInitSymTable (fun _ => 3)
        borrowInitSymState) = .fault ∧
      symEvalCfgGvn deadWriteCfg noJoinHints 1 0 borrowInitSymState diamondInitSymTable = none ∧
      execCfg staleLoanCfg 1 0 (evalSymCanonState diamondInitSymTable (fun _ => 3)
        borrowInitSymState) = .fault ∧
      symEvalCfgGvn staleLoanCfg noJoinHints 1 0 borrowInitSymState diamondInitSymTable = none ∧
      checkCfgAgainstTree freshLoanCfg noJoinHints 1 0 borrowInitSymState diamondInitSymTable
        (.var 1) = true := by
  decide +kernel

/-- Diamond whose then-arm borrows the branch-local `_2` and kills it (bumping its
    borrow-dirtied generation to `1`), while the else-arm leaves `_2` dead at generation `0`. -/
def borrowGenDiamondCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchInt 1 1 2 },
        { stmts := [ .storageLive 2, .assign 2 (.use 0), .retagBorrow 3 2, .storageDead 2 ]
          term := .goto 3 },
        { stmts := [], term := .goto 3 },
        { stmts := [], term := .ret 0 } ] }

/-- **Borrow-Generation Join Witness**: the generation mismatch on dead `_2` (`1` vs. `0`) makes
    the canonical merge fail — the join never conflates distinct storage incarnations — while
    path-splitting still verifies the program returns `_0`. -/
theorem borrowGen_join_rejected_split_verified :
    symEvalCfgGvn borrowGenDiamondCfg (fun _ => some [true, true, false, false]) 3 0
        borrowInitSymState diamondInitSymTable = none ∧
      checkCfgAgainstTree borrowGenDiamondCfg noJoinHints 3 0 borrowInitSymState
        diamondInitSymTable (.var 0) = true := by
  decide +kernel

/-- Write **and** read through the same fresh loan: `_2 := &_1; *_2 := _0 + 10; _0 := *_2`. -/
def freshStoreRefCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .storeRef 2 (.op1 (.addConst 10) 0),
              .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- Co-aliased loans, write through the older one, read through the newer one:
    `_2 := &_1; _3 := &_1; *_2 := _0 + 10; _0 := *_3`. Under the model's unique-loan (Stacked
    Borrows `&mut`) discipline the retag of `_3` already invalidates `_2`, so the write through
    `_2` faults. (Tree Borrows would allow that write — `_2` is still `Reserved` — but it is a
    foreign write that disables `_3`, so the final read is UB there too.) -/
def freshStoreRefAliasCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .retagBorrow 3 1,
              .storeRef 2 (.op1 (.addConst 10) 0),
              .assign 0 (.derefRef 3) ]
          term := .ret 0 } ] }

/-- An owner write invalidates outstanding loans: `_2 := &_1; _1 := 5; _0 := *_2`. -/
def ownerWriteInvalidatesCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .assign 1 (.const 5), .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- Indirect write through a **stale** loan (`_2 := &_1`, recycle `_1` via `StorageDead`/
    `StorageLive`, re-borrow `_3 := &_1`, then attempt `*_2 := _0`). -/
def staleStoreRefCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .storageDead 1,
              .storageLive 1,
              .assign 1 (.const 5),
              .retagBorrow 3 1,
              .storeRef 2 (.use 0) ]
          term := .ret 1 } ] }

/-- **Write-Through-Reference (`storeRef`) Aliasing Discipline Witness**:
    1. writing `*_2 := _0 + 10` and reading back through the same loan verifies
       (`= _0 + 10` for every input);
    2. with co-aliased loans `_2`, `_3` to `_1`, the program faults concretely and is rejected
       symbolically (the re-borrow `_3 := &_1` invalidates `_2`, so `*_2 := …` faults);
    3. an owner write (`_1 := 5`) invalidates the outstanding loan `_2` likewise;
    4. a write through a loan whose target storage was recycled faults and is rejected. -/
theorem storeRef_mutation_and_stale_fault_witness :
    checkCfgAgainstTree freshStoreRefCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable (.op1 (.addConst 10) (.var 0)) = true ∧
      execCfg freshStoreRefAliasCfg 1 0 (evalSymCanonState diamondInitSymTable (fun _ => 3)
        borrowInitSymState) = .fault ∧
      symEvalCfgGvn freshStoreRefAliasCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg ownerWriteInvalidatesCfg 1 0 (evalSymCanonState diamondInitSymTable (fun _ => 3)
        borrowInitSymState) = .fault ∧
      symEvalCfgGvn ownerWriteInvalidatesCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg staleStoreRefCfg 1 0 (evalSymCanonState diamondInitSymTable (fun _ => 3)
        borrowInitSymState) = .fault ∧
      symEvalCfgGvn staleStoreRefCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- Legal owner read after loan use is finished: `_2 := &_1; *_2 := _0 + 10; _0 := _1`. -/
def ownerReadAfterStoreRefValidCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .storeRef 2 (.op1 (.addConst 10) 0),
              .assign 0 (.use 1) ]
          term := .ret 0 } ] }

/-- Owner read of a borrowed local invalidates the loan (`_2 := &_1; _0 := _1; _0 := *_2`). -/
def ownerReadInvalidatesLoanDerefCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .assign 0 (.use 1), .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- Owner read of a borrowed local invalidates a subsequent indirect write
    (`_2 := &_1; _0 := _1; *_2 := 9`). -/
def ownerReadInvalidatesLoanStoreCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .assign 0 (.use 1), .storeRef 2 (.const 9) ]
          term := .ret 1 } ] }

/-- **Owner-Read Loan Invalidation Witness (`owner_read_invalidation_witness`)**:
    1. Writing through `_2 = &_1` and then reading `_1` through its owner (without using `_2`
       afterward) is legal and verifies (`= _0 + 10` for all inputs);
    2. Reading `_1` through its owner bumps `_1`'s borrow generation (`Slot.ownerRead`), so
       either reading (`*_2`) or writing (`*_2 := 9`) through `_2` afterward faults in
       `execCfg` and is rejected (`none`) by `symEvalCfgGvn`. -/
theorem owner_read_invalidation_witness :
    checkCfgAgainstTree ownerReadAfterStoreRefValidCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable (.op1 (.addConst 10) (.var 0)) = true ∧
      execCfg ownerReadInvalidatesLoanDerefCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn ownerReadInvalidatesLoanDerefCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg ownerReadInvalidatesLoanStoreCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn ownerReadInvalidatesLoanStoreCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- Owner read through a `switchInt` discriminant while a loan is live:
    `_2 := &_1; switchInt _1 → bb1 | bb2`, and both arms then read through `_2` (`_0 := *_2`). -/
def switchOwnerReadDerefCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1 ], term := .switchInt 1 1 2 },
        { stmts := [ .assign 0 (.derefRef 2) ], term := .ret 0 },
        { stmts := [ .assign 0 (.derefRef 2) ], term := .ret 0 } ] }

/-- The loan is finished before the `switchInt` reads its target (legal):
    `_2 := &_1; *_2 := _0 + 10; switchInt _1 → bb1 | bb2`, both arms `return _1`. -/
def switchOwnerReadValidCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .storeRef 2 (.op1 (.addConst 10) 0) ],
          term := .switchInt 1 1 2 },
        { stmts := [], term := .ret 1 },
        { stmts := [], term := .ret 1 } ] }

/-- Write through a loan, re-borrow the target, then write through the **old** loan:
    `_2 := &_1; *_2 := 5; _3 := &_1; *_2 := 6`. UB under Stacked Borrows (the retag of `_3`
    pops `_2`) and under Tree Borrows (the retag's read access freezes the `Active` `_2`). -/
def reborrowInvalidatesOldLoanCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .storeRef 2 (.const 5), .retagBorrow 3 1,
            .storeRef 2 (.const 6) ]
          term := .ret 1 } ] }

/-- The newest loan stays usable after a re-borrow:
    `_2 := &_1; _3 := &_1; *_3 := _0 + 1; _0 := *_3`. -/
def reborrowNewLoanValidCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .retagBorrow 3 1, .storeRef 3 (.op1 (.addConst 1) 0),
            .assign 0 (.derefRef 3) ]
          term := .ret 0 } ] }

/-- **Discriminant-Read & Re-Borrow Loan Invalidation Witness
    (`switch_and_reborrow_loan_invalidation_witness`)**:
    1. a `switchInt` on a borrowed local is an owner read: using the loan in either arm faults
       concretely (for a non-zero and a zero discriminant) and is rejected symbolically, while
       finishing the loan before the `switchInt` verifies (`= _0 + 10` on both paths);
    2. re-borrowing a target invalidates every earlier loan to it (`_2` after `_3 := &_1`
       faults and is rejected), while the newest loan verifies (`= _0 + 1`). -/
theorem switch_and_reborrow_loan_invalidation_witness :
    checkCfgAgainstTree switchOwnerReadValidCfg noJoinHints 2 0 borrowInitSymState
        diamondInitSymTable (.op1 (.addConst 10) (.var 0)) = true ∧
      execCfg switchOwnerReadDerefCfg 2 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      execCfg switchOwnerReadDerefCfg 2 0
        (evalSymCanonState diamondInitSymTable (fun _ => 0) borrowInitSymState) = .fault ∧
      symEvalCfgGvn switchOwnerReadDerefCfg noJoinHints 2 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg reborrowInvalidatesOldLoanCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn reborrowInvalidatesOldLoanCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      checkCfgAgainstTree reborrowNewLoanValidCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable (.op1 (.addConst 1) (.var 0)) = true := by
  decide +kernel

/-- Borrowing the pointer local `_2` itself (`_3 := &_2`) and then writing through `*_2`
    (`storeRef 2 (.const 9)`) performs an owner read on `_2`, invalidating `_3`'s loan to `_2`
    so a subsequent `_0 := *_3` faults. -/
def storeRefPtrOwnerReadInvalidatesLoanCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .retagBorrow 3 2,
              .storeRef 2 (.const 9),
              .assign 0 (.derefRef 3) ]
          term := .ret 0 } ] }

/-- Borrowing `_2` (`_3 := &_2`), writing through `*_2 := _0 + 9`, and reading back through `_2`
    itself (`_0 := *_2`, without touching the invalidated `_3`) succeeds and returns `_0 + 9`. -/
def storeRefPtrOwnerReadValidSelfCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .retagBorrow 2 1,
              .retagBorrow 3 2,
              .storeRef 2 (.op1 (.addConst 9) 0),
              .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- **Pointer-Local Owner-Read Invalidation in `storeRef`
    (`storeRef_ptr_owner_read_invalidation_witness`)**:
    1. When `_2 := &_1` and `_3 := &_2` (so `_3` borrows the pointer slot `_2`), executing
       `*_2 := 9` (`storeRef 2 (.const 9)`) directly reads `_2` by its owner (`storeThrough`
       applies `ownerReadLoc 2`), bumping `_2`'s generation and invalidating `_3` so a subsequent
       `_0 := *_3` faults in `execCfg` and returns `none` in `symEvalCfgGvn`.
    2. Meanwhile, `_2`'s own loan to `_1` is re-validated at `_1`'s bumped generation, so reading
       back through `*_2` (`storeRefPtrOwnerReadValidSelfCfg`) verifies `= _0 + 9`. -/
theorem storeRef_ptr_owner_read_invalidation_witness :
    execCfg storeRefPtrOwnerReadInvalidatesLoanCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn storeRefPtrOwnerReadInvalidatesLoanCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      checkCfgAgainstTree storeRefPtrOwnerReadValidSelfCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable (.op1 (.addConst 9) (.var 0)) = true := by
  decide +kernel

/-- Reading a reference local as a scalar: `_2 := &_1; *_2 := 7; _0 := _2` (ill-typed MIR — a
    `&mut u64` is not a `u64`). -/
def pointerAsScalarCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .storeRef 2 (.const 7), .assign 0 (.use 2) ]
          term := .ret 0 } ] }

/-- Returning a reference local as the scalar result: `_2 := &_1; return _2`. -/
def pointerReturnCfg : MirCfg :=
  { blocks := [ { stmts := [ .retagBorrow 2 1 ], term := .ret 2 } ] }

/-- Reading back through the reference instead: `_2 := &_1; *_2 := 7; _0 := *_2`. -/
def pointerDerefCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .storeRef 2 (.const 7), .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- **Pointer Locals Are Not Scalars (`pointer_scalar_read_rejected_witness`)**: a slot holding a
    loan cannot be read as a scalar, so the untyped model no longer exposes the stale snapshot of
    the referent taken at borrow time. Before B4, `pointerAsScalarCfg` *verified* against the
    **old** `_1` (`.var 1`) although `_1` had been overwritten with `7`. Both ill-typed programs
    now fault concretely, the first is rejected symbolically, and the deref reads the current
    referent (`= 7`). -/
theorem pointer_scalar_read_rejected_witness :
    execCfg pointerAsScalarCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn pointerAsScalarCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg pointerReturnCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      checkCfgAgainstTree pointerDerefCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable (.const 7) = true := by
  decide +kernel

/-- Two-level stale-snapshot read via `derefRef` on a reference-to-reference (`_2 := &_1;
    _3 := &_2; _1 := 7; _0 := *_3; return _0`): in B4 (`9f2fc8f8`), `_1 := 7` invalidated `_2`'s
    loan to `_1` without touching `_2`'s own generation, and `derefRef 3` matched `st.getSlot 2`
    against `.live targetVal curGen true _` (ignoring `targetLoan = some (1, 0)`), so B4 verified
    `_0 := *_3` against the stale borrow-time snapshot `.var 1` (`3`, even though `_1` had been
    overwritten with `7`!). Requiring `targetLoan = none` in `derefRef` rejects this both
    concretely and symbolically. -/
def refToRefDerefCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .retagBorrow 3 2, .assign 1 (.const 7),
            .assign 0 (.derefRef 3) ]
          term := .ret 0 } ] }

/-- Two-level scalar overwrite of a reference slot via `storeRef` (`_2 := &_1; _3 := &_2;
    *_3 := 7; _0 := *_2`): in B4, `storeRef 3 (.const 7)` overwrote `_2`'s snapshot with `7`
    while keeping `_2`'s `loanTarget = some (1, 0)`. Requiring `targetLoan = none` in `storeRef`
    rejects scalar writes into reference slots. -/
def refToRefStoreCfg : MirCfg :=
  { blocks :=
      [ { stmts := [ .retagBorrow 2 1, .retagBorrow 3 2, .storeRef 3 (.const 7),
            .assign 0 (.derefRef 2) ]
          term := .ret 0 } ] }

/-- **Reference-to-Reference Scalar Deref/Store Rejection (`ref_to_ref_deref_and_store_rejected_witness`)**:
    neither `derefRef` nor `storeRef` may treat a reference slot (`targetLoan = some _`) as a
    scalar referent, closing B4's residual two-level stale-snapshot soundness hole (`PROTOTYPE_REPORT.md`
    §2.7, §3.2). -/
theorem ref_to_ref_deref_and_store_rejected_witness :
    execCfg refToRefDerefCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn refToRefDerefCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none ∧
      execCfg refToRefStoreCfg 1 0
        (evalSymCanonState diamondInitSymTable (fun _ => 3) borrowInitSymState) = .fault ∧
      symEvalCfgGvn refToRefStoreCfg noJoinHints 1 0 borrowInitSymState
        diamondInitSymTable = none := by
  decide +kernel

/-- Diamond with branch-condition-dependent `MirStmt.assert`s in both arms:
    - `then` arm (`bb 1`, where `_1 != 0`) asserts `_1` directly and computes `_0 := _0 + 7`,
    - `else` arm (`bb 2`, where `_1 == 0`) computes `_2 := boolNot(_1)`, asserts `_2`, kills
      `_2`, and computes `_0 := _0 + 7`. -/
def branchCondAssertDiamondCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchInt 1 1 2 },
        { stmts := [ .assert 1, .assign 0 (.op1 (.addConst 7) 0) ], term := .goto 3 },
        { stmts :=
            [ .storageLive 2,
              .assign 2 (.op1 .boolNot 1),
              .assert 2,
              .storageDead 2,
              .assign 0 (.op1 (.addConst 7) 0) ]
          term := .goto 3 },
        { stmts := [], term := .ret 0 } ] }

/-- Non-diamond `switchInt` where both arms assert their branch condition and return directly
    (`.ret 0`, so `diamondMergePlan = none` and `combineSplit` path-splits). -/
def branchCondEarlyReturnCfg : MirCfg :=
  { blocks :=
      [ { stmts := [], term := .switchInt 1 1 2 },
        { stmts := [ .assert 1, .assign 0 (.op1 (.addConst 7) 0) ], term := .ret 0 },
        { stmts :=
            [ .storageLive 2,
              .assign 2 (.op1 .boolNot 1),
              .assert 2,
              .storageDead 2,
              .assign 0 (.op1 (.addConst 7) 0) ]
          term := .ret 0 } ] }

/-- **Path-Sensitive Branch-Assertion Diamond & Split Witness (`branch_cond_assert_diamond_verified`)**:
    `symEvalCfgGvn` discharges branch-dependent assertions (`assert _1` in the `then` arm and
    `assert (boolNot _1)` in the `else` arm) both when merging at a join (`diamondJoinHints`,
    `1` path) AND when path-splitting without join hints (`noJoinHints`, `2` paths) or on
    early-return arms (`branchCondEarlyReturnCfg`). -/
theorem branch_cond_assert_diamond_verified :
    (symEvalCfgGvn branchCondAssertDiamondCfg diamondJoinHints 3 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 1 ∧
      checkCfgAgainstTree branchCondAssertDiamondCfg diamondJoinHints 3 0 diamondInitSymState
        diamondInitSymTable (.op1 (.addConst 7) (.var 0)) = true ∧
      (symEvalCfgGvn branchCondAssertDiamondCfg noJoinHints 3 0 diamondInitSymState
        diamondInitSymTable).map (fun res => res.1.length) = some 2 ∧
      checkCfgAgainstTree branchCondAssertDiamondCfg noJoinHints 3 0 diamondInitSymState
        diamondInitSymTable (.op1 (.addConst 7) (.var 0)) = true ∧
      checkCfgAgainstTree branchCondEarlyReturnCfg noJoinHints 2 0 diamondInitSymState
        diamondInitSymTable (.op1 (.addConst 7) (.var 0)) = true := by
  decide +kernel

/-- Asserts `!(x < x)` and `!(x - x)` (folded by `peepholeOp2` to `.const 0`, then negated by
    `.op1 .boolNot` and discharged by `isProvablyNonZero`). -/
def assertNotLtIrreflCfg : MirCfg :=
  { blocks :=
      [ { stmts :=
            [ .storageLive 2,
              .assign 2 (.op2 .lt 0 0),
              .assign 2 (.op1 .boolNot 2),
              .assert 2,
              .assign 2 (.op2 .sub 0 0),
              .assign 2 (.op1 .boolNot 2),
              .assert 2,
              .storageDead 2 ]
          term := .ret 0 } ] }

/-- **Negated Zero-Constant Assertion Witness (`assert_not_lt_irrefl_verified`)**:
    `peepholeOp2` folds `_0 < _0` and `_0 - _0` to `.const 0`, and `isProvablyNonZero`
    recognizes `boolNot (.const 0)` as provably non-zero. -/
theorem assert_not_lt_irrefl_verified :
    checkCfgAgainstTree assertNotLtIrreflCfg noJoinHints 1 0 diamondInitSymState
      diamondInitSymTable (.var 0) = true := by
  decide +kernel



/-!
## Trusted `MirSemantics` Operator Bridges & Production `DWLP mirDefaultWP` Diamond Join-Cut Combinators
-/

/-- Bridge adapter converting a concrete evaluated `SymId` into a trusted `MirSemantics.Value`
    (`8`-byte `u64` scalar). -/
def evalSymIdToMirValue (tbl : SymTable) (env : SymEnv) (id : SymId) :
    Trusted.Rustc.V2026_06_01.MirSemantics.Value :=
  .scalar { bits := evalSymId tbl env id, sizeBytes := 8 }

/-- Monotonicity of `evalSymIdToMirValue` under append-only `SymTable.Extends`. -/
theorem evalSymIdToMirValue_mono {tbl₁ tbl₂ : SymTable}
    (hValid : ValidTable tbl₁) (hExt : tbl₁.Extends tbl₂)
    (env : SymEnv) {id : SymId} (hlt : id < tbl₁.nodes.length) :
    evalSymIdToMirValue tbl₁ env id = evalSymIdToMirValue tbl₂ env id := by
  dsimp [evalSymIdToMirValue]
  rw [evalSymId_mono hValid hExt env hlt]

/-- `evalSymIdToMirValue` after `internTree` produces the exact 8-byte `MirSemantics.Value`
    of `ExprTree.eval`. -/
theorem evalSymIdToMirValue_internTree (tbl : SymTable) (hValid : ValidTable tbl)
    (t : ExprTree) (env : SymEnv) :
    evalSymIdToMirValue (internTree tbl t).2 env (internTree tbl t).1 =
      .scalar { bits := t.eval env, sizeBytes := 8 } := by
  dsimp [evalSymIdToMirValue]
  rw [(internTree_spec t tbl hValid).2.2.2 env]

/-- Universal `u64` range invariant for `evalSymIdToMirValue`: every `SymId` evaluates to a
    canonical 8-byte `MirSemantics.Value` whose scalar bits are `< word64Modulus`. -/
theorem evalSymIdToMirValue_lt_word64 (tbl : SymTable) (env : SymEnv) (id : SymId) :
    ∃ bits : Nat,
      evalSymIdToMirValue tbl env id = .scalar { bits := bits, sizeBytes := 8 } ∧
        bits < word64Modulus :=
  ⟨evalSymId tbl env id, rfl, evalSymId_lt_word64 tbl env id⟩

/-- `evalSymIdToMirValue` after `internNode` agrees with the single-step node evaluation. -/
theorem evalSymIdToMirValue_internNode {tbl : SymTable} {n : SymNode}
    (hValid : ValidTable tbl) (hNode : ValidNode tbl.nodes.length n) (env : SymEnv) :
    evalSymIdToMirValue (internNode tbl n).2 env (internNode tbl n).1 =
      .scalar { bits := evalSymNodeWith (evalSymId tbl env) env n, sizeBytes := 8 } := by
  dsimp [evalSymIdToMirValue]
  rw [internNode_eval hValid hNode env]

/-- `evalSymIdToMirValue` after `internOp2` (including peephole canonicalization) agrees with
    `evalSymOp2` on the operand `SymId`s. -/
theorem evalSymIdToMirValue_internOp2 {tbl : SymTable} {op : SymOp2} {a b : SymId}
    (hValid : ValidTable tbl) (ha : a < tbl.nodes.length) (hb : b < tbl.nodes.length)
    (env : SymEnv) :
    evalSymIdToMirValue (internOp2 tbl op a b).2 env (internOp2 tbl op a b).1 =
      .scalar { bits := evalSymOp2 op (evalSymId tbl env a) (evalSymId tbl env b), sizeBytes := 8 } := by
  dsimp [evalSymIdToMirValue]
  rw [internOp2_eval hValid ⟨ha, hb⟩ env]

theorem bridge_coexistence_rfl :
    evalSymIdToMirValue (buildDiamondGvn 4).2 (fun _ => 7) (buildDiamondGvn 4).1 =
      .scalar { bits := (buildDiamondTree 4).eval (fun _ => 7), sizeBytes := 8 } :=
  rfl

/-- Does `evalSymOp2` on `u64` arithmetic/bitwise/shift operations agree with the trusted
    `MirSemantics.evalScalarBinOp` on 8-byte scalars `a`, `b`? -/
def protoOpAgrees (op : SymOp2) (mop : Trusted.Rustc.V2026_06_01.MirAst.BinOp) (a b : Nat) : Bool :=
  match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp mop ⟨a, 8⟩ ⟨b, 8⟩ [] with
  | .ok (.scalar s) _ _ => s.bits == evalSymOp2 op a b && s.sizeBytes == 8
  | _ => false

/-- Does `evalSymOp2` on `u64` comparison operations agree with the trusted
    `MirSemantics.evalScalarBinOp` (which returns a 1-byte `bool` scalar via `boolToScalar`)
    on 8-byte inputs `a`, `b`? -/
def protoCmpAgrees (op : SymOp2) (mop : Trusted.Rustc.V2026_06_01.MirAst.BinOp) (a b : Nat) : Bool :=
  match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp mop ⟨a, 8⟩ ⟨b, 8⟩ [] with
  | .ok (.scalar s) _ _ => s.bits == evalSymOp2 op a b && s.sizeBytes == 1
  | _ => false

/-- Does every `SymOp1` unary operator (`id`, `boolNot`, `wrappingNeg64`, `maskLow32`, `xorConst`,
    `addConst`) agree with its trusted `MirSemantics` binary-operator encoding on 8-byte scalar
    `a` and constant `b`? -/
def protoOp1Agrees (a b : Nat) : Bool :=
  let m8 := Trusted.Rustc.V2026_06_01.MirSemantics.scalarModulus 8
  let idOk := Trusted.Rustc.V2026_06_01.MirSemantics.wrapScalarBits a m8 == evalSymOp1 .id a
  let boolNotOk :=
    match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp .eq ⟨a, 8⟩ ⟨0, 8⟩ [] with
    | .ok (.scalar s) _ _ => s.bits == evalSymOp1 .boolNot a && s.sizeBytes == 1
    | _ => false
  let negOk :=
    match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp .sub ⟨0, 8⟩ ⟨a, 8⟩ [] with
    | .ok (.scalar s) _ _ => s.bits == evalSymOp1 .wrappingNeg64 a && s.sizeBytes == 8
    | _ => false
  let maskOk :=
    match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨0xFFFFFFFF, 8⟩ [] with
    | .ok (.scalar s) _ _ => s.bits == evalSymOp1 .maskLow32 a && s.sizeBytes == 8
    | _ => false
  let xorOk :=
    match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨wrap64 b, 8⟩ [] with
    | .ok (.scalar s) _ _ => s.bits == evalSymOp1 (.xorConst b) a && s.sizeBytes == 8
    | _ => false
  let addOk :=
    match Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp .add ⟨a, 8⟩ ⟨wrap64 b, 8⟩ [] with
    | .ok (.scalar s) _ _ => s.bits == evalSymOp1 (.addConst b) a && s.sizeBytes == 8
    | _ => false
  idOk && boolNotOk && negOk && maskOk && xorOk && addOk

def bridgeSamples : List (Nat × Nat) :=
  [(0, 0), (3, 5), (5, 3), (1, 65), (18446744073709551615, 1),
   (18446744073709551615, 18446744073709551615), (9223372036854775808, 2), (123456789, 987654321)]

/-- MIR `bool` operand type used by the typed `UnOp::Not` bridge (`evalUnaryNot`'s `ty.kind = .bool`
    branch). -/
def bridgeBoolTy : Ty := { kind := .bool, layoutIdx := 0 }

/-- MIR `u64` operand type used by the typed `UnOp::Not` bridge (`evalUnaryNot`'s `ty.kind = .uint _`
    branch). -/
def bridgeU64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }

/-- MIR `u8` operand type: a `1`-byte **integer**, whose `!0u8 = 255` must not be confused with
    `bool`'s `!false = true` although both operands are `1`-byte scalars with bits `0`. -/
def bridgeU8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }

/-- MIR `UnOp::Not` as evaluated by the trusted `evalUnaryNot` on a `width`-byte scalar `a` whose
    operand type `ty` is **known** (`some ty`), exactly as the MIR lowering supplies it. The typed
    branches are the ones a lowering exercises; `evalUnaryNot`'s untyped (`none`) fallback guesses
    `bool` for every `1`-byte `0`/`1` operand and is deliberately *not* what this bridge checks. -/
def mirNot (ty : Ty) (a width : Nat) : Option Nat :=
  match Trusted.Rustc.V2026_06_01.MirSemantics.evalUnaryNot ⟨a, width⟩ (some ty) [] emptyMemory with
  | .ok (.scalar s) _ _ => if s.sizeBytes == width then some s.bits else none
  | _ => none

/-- **Trusted `MirSemantics.evalUnaryNot` Bridge (`bridge_unary_not_mapping`)**, on **typed**
    operands (`bool` / `u64` / `u8`):
    1. `boolNot` agrees with MIR `UnOp::Not` on `bool` operands `0`/`1`;
    2. `xorConst (2^64 - 1)` agrees with MIR `UnOp::Not` on `u64` samples (bitwise complement);
    3. `boolNot 5 ≠ MIR Not 5` on `u64`, so lowering integer `!x` to `boolNot` would be unsound;
    4. MIR `!` on an invalid `bool` (bits `5`) is UB (`none`), whereas `boolNot 5 = 0`: `boolNot` is
       only a faithful encoding on valid `0`/`1` booleans;
    5. on `1`-byte operands with bits `0`, `u8` and `bool` disagree (`255` vs `1`): the encoding must
       be chosen from the operand **type**, never from the operand width or value. -/
theorem bridge_unary_not_mapping :
    [0, 1].all (fun b => mirNot bridgeBoolTy b 1 == some (evalSymOp1 .boolNot b)) = true ∧
      bridgeSamples.all (fun p =>
        mirNot bridgeU64Ty p.1 8 == some (evalSymOp1 (.xorConst 18446744073709551615) p.1)) = true ∧
      mirNot bridgeU64Ty 5 8 ≠ some (evalSymOp1 .boolNot 5) ∧
      mirNot bridgeBoolTy 5 1 = none ∧
      mirNot bridgeU8Ty 0 1 = some 255 ∧ mirNot bridgeBoolTy 0 1 = some 1 := by
  decide +kernel

/-- Universal typed-`bool` `UnOp::Not` bridge: on every valid `bool` (`b ≤ 1`), MIR `!b` is
    `boolNot b`. -/
theorem evalUnaryNot_bool_eq_boolNot {b : Nat} (hb : b ≤ 1)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨b, 1⟩ (some bridgeBoolTy) locals mem =
      .ok (.scalar ⟨evalSymOp1 .boolNot b, 1⟩) locals mem := by
  match b, hb with
  | 0, _ => rfl
  | 1, _ => rfl

/-- Universal typed-`bool` negative bridge: MIR `!b` on an invalid `bool` (`2 ≤ b`) is UB, although
    `evalSymOp1 .boolNot b = 0` is defined. -/
theorem evalUnaryNot_bool_invalid_ub {b : Nat} (hb : 2 ≤ b)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨b, 1⟩ (some bridgeBoolTy) locals mem = .ub := by
  match b, hb with
  | _ + 2, _ => rfl

/-- Universal typed-`u64` `UnOp::Not` bridge: on every `u64` word `a`, MIR `!a` is
    `u64::MAX.wrapping_sub(a)` (`evalSymOp2 .sub (2^64 - 1) a`), i.e. the bitwise complement. -/
theorem evalUnaryNot_u64_eq_wrappingSubMax {a : Nat} (ha : a < word64Modulus)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨a, 8⟩ (some bridgeU64Ty) locals mem =
      .ok (.scalar ⟨evalSymOp2 .sub 18446744073709551615 a, 8⟩) locals mem := by
  have ha' : a < 18446744073709551616 := ha
  have hle : a ≤ 18446744073709551615 := Nat.le_of_lt_succ ha'
  have hLt : 18446744073709551615 - a < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  show RvalueEvalResult.ok (.scalar ⟨Nat.sub (Nat.sub (scalarModulus 8) 1)
      (wrapScalarBits a (scalarModulus 8)), 8⟩) locals mem = _
  rw [scalarModulus_eight, wrapScalarBits_of_lt ha']
  have hSub : evalSymOp2 .sub 18446744073709551615 a = 18446744073709551615 - a := by
    show (18446744073709551615 + (18446744073709551616 - a % 18446744073709551616)) %
        18446744073709551616 = _
    rw [Nat.mod_eq_of_lt ha', ← Nat.add_sub_assoc (Nat.le_of_lt ha'),
      Nat.sub_add_comm hle, Nat.add_mod_right, Nat.mod_eq_of_lt hLt]
  rw [hSub]
  rfl

/-- **Trusted `MirSemantics.evalScalarBinOp` Bridge (`bridge_u64_semantics_agree`)**:
    Kernel-checked agreement with the trusted MIR semantics on boundary, shift-wrap (`65 % 64`),
    and generic `u64` samples across all 11 `SymOp2` binary operators and all 6 `SymOp1` unary
    operators (their binary-operator encodings). The universal counterparts for **every** operand
    pair are `bridge_u64_semantics_agree_universal` (binary) and the `evalUnaryNot_*` lemmas. -/
theorem bridge_u64_semantics_agree :
    bridgeSamples.all (fun p =>
      protoOp1Agrees p.1 p.2 &&
        protoOpAgrees .add .add p.1 p.2 && protoOpAgrees .sub .sub p.1 p.2 &&
        protoOpAgrees .mul .mul p.1 p.2 && protoOpAgrees .bitXor .bitXor p.1 p.2 &&
        protoOpAgrees .bitAnd .bitAnd p.1 p.2 && protoOpAgrees .bitOr .bitOr p.1 p.2 &&
        protoOpAgrees .shl .shl p.1 p.2 && protoOpAgrees .shr .shr p.1 p.2 &&
        protoCmpAgrees .eq .eq p.1 p.2 && protoCmpAgrees .lt .lt p.1 p.2 &&
        protoCmpAgrees .le .le p.1 p.2) = true := by
  decide +kernel

/-- Universal `u64` addition bridge: `evalSymOp2 .add a b` matches `MirSemantics.evalScalarBinOp .add`
    for **all** `a b : Nat`. -/
theorem evalSymOp2_add_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .add ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .add a b, 8⟩) locals mem := by
  dsimp [evalScalarBinOp, evalSymOp2, wrap64, word64Modulus]
  rw [wrapScalarBits_eq_mod]

/-- Universal `u64` multiplication bridge: `evalSymOp2 .mul a b` matches
    `MirSemantics.evalScalarBinOp .mul` for **all** `a b : Nat`. -/
theorem evalSymOp2_mul_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .mul ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .mul a b, 8⟩) locals mem := by
  dsimp [evalScalarBinOp, evalSymOp2, wrap64, word64Modulus]
  rw [wrapScalarBits_eq_mod]

/-- Universal `u64` wrapping subtraction bridge: `evalSymOp2 .sub a b` matches
    `MirSemantics.evalScalarBinOp .sub` for **all** `u64` words `a, b < word64Modulus`
    (proved without `omega`). -/
theorem evalSymOp2_sub_eq_evalScalarBinOp
    {a b : Nat} (ha : a < word64Modulus) (hb : b < word64Modulus)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .sub ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .sub a b, 8⟩) locals mem := by
  dsimp [evalScalarBinOp, evalSymOp2, wrap64, word64Modulus] at ha hb ⊢
  have hModB : b % 18446744073709551616 = b := Nat.mod_eq_of_lt hb
  rw [hModB]
  cases hBle : Nat.ble b a with
  | true =>
    have hLe : b ≤ a := (nat_ble_eq_true_iff b a).1 hBle
    rw [wrapScalarBits_eq_mod]
    congr 2
    have hSubLt : a - b < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
    have hAddEq : a + (18446744073709551616 - b) = (a - b) + 18446744073709551616 := by
      rw [← Nat.add_sub_assoc (Nat.le_of_lt hb), Nat.sub_add_comm hLe]
    rw [hAddEq, Nat.add_mod_right, Nat.mod_eq_of_lt hSubLt]
  | false =>
    dsimp only
    rw [wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb, wrapScalarBits_eq_mod]
    have hEq : 18446744073709551616 + a - b = a + (18446744073709551616 - b) := by
      rw [Nat.add_comm 18446744073709551616 a, Nat.add_sub_assoc (Nat.le_of_lt hb)]
    rw [hEq]

/-- Universal `u64` equality comparison bridge: `evalSymOp2 .eq a b` matches
    `MirSemantics.evalScalarBinOp .eq` for **all** `a b : Nat`. -/
theorem evalSymOp2_eq_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .eq ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .eq a b, 1⟩) locals mem := by
  dsimp [evalScalarBinOp, evalSymOp2, boolToScalar]
  by_cases h : a = b
  · subst h
    have hBeq : Nat.beq a a = true := (nat_beq_eq_true_iff a a).2 rfl
    have hBne : (a == a) = true := decide_eq_true rfl
    rw [hBeq, hBne]
    rfl
  · have hBeq : Nat.beq a b = false := (nat_beq_eq_false_iff a b).2 h
    have hBne : (a == b) = false := decide_eq_false h
    rw [hBeq, hBne]
    rfl

/-- Universal unsigned `u64` `<` bridge: `evalSymOp2 .lt a b` matches `MirSemantics.evalScalarBinOp .lt`
    (a `1`-byte `bool`) for **all** `a b : Nat`. -/
theorem evalSymOp2_lt_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .lt ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .lt a b, 1⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar (boolToScalar (Bool.not (Nat.ble b a)))) locals mem = _
  cases h : Nat.ble b a with
  | true =>
    have hn : decide (a < b) = false := decide_eq_false (Nat.not_lt.2 ((nat_ble_eq_true_iff b a).1 h))
    simp only [evalSymOp2, hn]
    rfl
  | false =>
    have hy : decide (a < b) = true := decide_eq_true ((nat_ble_eq_false_iff b a).1 h)
    simp only [evalSymOp2, hy]
    rfl

/-- Universal unsigned `u64` `≤` bridge: `evalSymOp2 .le a b` matches `MirSemantics.evalScalarBinOp .le`
    (a `1`-byte `bool`) for **all** `a b : Nat`. -/
theorem evalSymOp2_le_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .le ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .le a b, 1⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar (boolToScalar (Nat.ble a b))) locals mem = _
  cases h : Nat.ble a b with
  | true =>
    have hy : decide (a ≤ b) = true := decide_eq_true ((nat_ble_eq_true_iff a b).1 h)
    simp only [evalSymOp2, hy]
    rfl
  | false =>
    have hn : decide (a ≤ b) = false := decide_eq_false (Nat.not_le.2 ((nat_ble_eq_false_iff a b).1 h))
    simp only [evalSymOp2, hn]
    rfl

/-- Universal `u64` `<<` bridge: `evalSymOp2 .shl a b` (shift amount masked to `b % 64`) matches
    `MirSemantics.evalScalarBinOp .shl` for **all** `a b : Nat`. -/
theorem evalSymOp2_shl_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shl ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .shl a b, 8⟩) locals mem := by
  show RvalueEvalResult.ok
    (.scalar ⟨shiftLeftBits a (Nat.mod b (Nat.mul 8 8)) (scalarModulus 8), 8⟩) locals mem = _
  simp only [shiftLeftBits, evalSymOp2, wrap64, word64Modulus, scalarModulus_eight,
    wrapScalarBits_eq_mod, scalarPow2_eq_two_pow, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  rfl

/-- Universal unsigned `u64` `>>` bridge: `evalSymOp2 .shr a b` (shift amount masked to `b % 64`)
    matches `MirSemantics.evalScalarBinOp .shr` for **all** `a b : Nat`. -/
theorem evalSymOp2_shr_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shr ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .shr a b, 8⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar ⟨wrapScalarBits
    (shiftRightUnsignedBits a (Nat.mod b (Nat.mul 8 8))) (scalarModulus 8), 8⟩) locals mem = _
  have hShr : Nat.shiftRight a (b % 64) = a / 2 ^ (b % 64) := Nat.shiftRight_eq_div_pow a (b % 64)
  simp only [shiftRightUnsignedBits, evalSymOp2, wrap64, word64Modulus, scalarModulus_eight,
    wrapScalarBits_eq_mod, scalarPow2_eq_two_pow, hShr]
  rfl

/-- `testBit` of a trusted bit-recursion step `bit + 2 * rest` (`bit < 2`) at bit `0`. -/
theorem testBit_bitStep_zero {bit rest : Nat} (hb : bit < 2) :
    (Nat.add bit (Nat.mul 2 rest)).testBit 0 = decide (bit = 1) := by
  rw [Nat.testBit_zero]
  have h : (Nat.add bit (Nat.mul 2 rest)) % 2 = bit := by
    show (bit + 2 * rest) % 2 = bit
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  rw [h]

/-- `testBit` of a trusted bit-recursion step `bit + 2 * rest` (`bit < 2`) at bit `j + 1`. -/
theorem testBit_bitStep_succ {bit rest : Nat} (hb : bit < 2) (j : Nat) :
    (Nat.add bit (Nat.mul 2 rest)).testBit (j + 1) = rest.testBit j := by
  rw [Nat.testBit_succ]
  have h : (Nat.add bit (Nat.mul 2 rest)) / 2 = rest := by
    show (bit + 2 * rest) / 2 = rest
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt hb, Nat.zero_add]
  rw [h]

theorem decide_succ_lt_succ (j k : Nat) : decide (j + 1 < k + 1) = decide (j < k) :=
  decide_eq_decide.mpr Nat.succ_lt_succ_iff

/-- Bitwise characterization of the trusted `bitwiseAndBits` recursion. -/
theorem testBit_bitwiseAndBits :
    ∀ (k a b i : Nat),
      (bitwiseAndBits k a b).testBit i = (decide (i < k) && (a.testBit i && b.testBit i))
  | 0, a, b, i => by
    show (0 : Nat).testBit i = _
    rw [Nat.zero_testBit]
    rfl
  | k + 1, a, b, 0 => by
    refine (testBit_bitStep_zero ?_).trans ?_
    · split <;> decide
    · rw [Nat.testBit_zero a, Nat.testBit_zero b]
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        · have ha' : Nat.mod a 2 = _ := ha
          have hb' : Nat.mod b 2 = _ := hb
          simp only [ha, hb, ha', hb']
          all_goals rfl
  | k + 1, a, b, j + 1 => by
    refine (testBit_bitStep_succ ?_ j).trans ((testBit_bitwiseAndBits k (a / 2) (b / 2) j).trans ?_)
    · split <;> decide
    · rw [Nat.testBit_succ a j, Nat.testBit_succ b j, decide_succ_lt_succ]

/-- Bitwise characterization of the trusted `bitwiseOrBits` recursion. -/
theorem testBit_bitwiseOrBits :
    ∀ (k a b i : Nat),
      (bitwiseOrBits k a b).testBit i = (decide (i < k) && (a.testBit i || b.testBit i))
  | 0, a, b, i => by
    show (0 : Nat).testBit i = _
    rw [Nat.zero_testBit]
    rfl
  | k + 1, a, b, 0 => by
    refine (testBit_bitStep_zero ?_).trans ?_
    · split <;> decide
    · rw [Nat.testBit_zero a, Nat.testBit_zero b]
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        · have ha' : Nat.mod a 2 = _ := ha
          have hb' : Nat.mod b 2 = _ := hb
          simp only [ha, hb, ha', hb']
          all_goals rfl
  | k + 1, a, b, j + 1 => by
    refine (testBit_bitStep_succ ?_ j).trans ((testBit_bitwiseOrBits k (a / 2) (b / 2) j).trans ?_)
    · split <;> decide
    · rw [Nat.testBit_succ a j, Nat.testBit_succ b j, decide_succ_lt_succ]

/-- Bitwise characterization of the trusted `bitwiseXorBits` recursion. -/
theorem testBit_bitwiseXorBits :
    ∀ (k a b i : Nat),
      (bitwiseXorBits k a b).testBit i = (decide (i < k) && (a.testBit i ^^ b.testBit i))
  | 0, a, b, i => by
    show (0 : Nat).testBit i = _
    rw [Nat.zero_testBit]
    rfl
  | k + 1, a, b, 0 => by
    refine (testBit_bitStep_zero ?_).trans ?_
    · split <;> decide
    · rw [Nat.testBit_zero a, Nat.testBit_zero b]
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        · have ha' : Nat.mod a 2 = _ := ha
          have hb' : Nat.mod b 2 = _ := hb
          simp only [ha, hb, ha', hb']
          all_goals rfl
  | k + 1, a, b, j + 1 => by
    refine (testBit_bitStep_succ ?_ j).trans ((testBit_bitwiseXorBits k (a / 2) (b / 2) j).trans ?_)
    · split <;> decide
    · rw [Nat.testBit_succ a j, Nat.testBit_succ b j, decide_succ_lt_succ]

theorem bitwiseAndBits_eq (k a b : Nat) : bitwiseAndBits k a b = (a &&& b) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitwiseAndBits, Nat.testBit_mod_two_pow, Nat.testBit_and]

theorem bitwiseOrBits_eq (k a b : Nat) : bitwiseOrBits k a b = (a ||| b) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitwiseOrBits, Nat.testBit_mod_two_pow, Nat.testBit_or]

theorem bitwiseXorBits_eq (k a b : Nat) : bitwiseXorBits k a b = (a ^^^ b) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitwiseXorBits, Nat.testBit_mod_two_pow, Nat.testBit_xor]

/-- Universal `u64` `&` bridge (trusted `bitwiseAndBits` recursion) for **all** `a b : Nat`. -/
theorem evalSymOp2_bitAnd_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .bitAnd a b, 8⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar ⟨bitwiseAndBits (Nat.mul 8 8) a b, 8⟩) locals mem = _
  rw [bitwiseAndBits_eq]
  rfl

/-- Universal `u64` `|` bridge (trusted `bitwiseOrBits` recursion) for **all** `a b : Nat`. -/
theorem evalSymOp2_bitOr_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .bitOr ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .bitOr a b, 8⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar ⟨bitwiseOrBits (Nat.mul 8 8) a b, 8⟩) locals mem = _
  rw [bitwiseOrBits_eq]
  rfl

/-- Universal `u64` `^` bridge (trusted `bitwiseXorBits` recursion) for **all** `a b : Nat`. -/
theorem evalSymOp2_bitXor_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp2 .bitXor a b, 8⟩) locals mem := by
  show RvalueEvalResult.ok (.scalar ⟨bitwiseXorBits (Nat.mul 8 8) a b, 8⟩) locals mem = _
  rw [bitwiseXorBits_eq]
  rfl

/-- `k`-bit all-ones mask (`2 ^ k - 1`), defined structurally so `testBit`, low-masking, and
    bitwise-complement identities can be proved by elementary bit recursion without
    `Classical.choice` (`Nat.testBit_two_pow_sub_succ` in Lean core depends on `Classical.choice`). -/
def onesBits : Nat → Nat
  | 0 => 0
  | k + 1 => 1 + 2 * onesBits k

theorem testBit_onesBits : ∀ (k i : Nat), (onesBits k).testBit i = decide (i < k)
  | 0, i => by
    show (0 : Nat).testBit i = _
    rw [Nat.zero_testBit]
    rfl
  | k + 1, 0 => by
    refine (testBit_bitStep_zero (by decide : 1 < 2)).trans ?_
    rfl
  | k + 1, j + 1 => by
    refine (testBit_bitStep_succ (by decide : 1 < 2) j).trans ?_
    rw [testBit_onesBits k j, decide_succ_lt_succ]

theorem and_onesBits_eq_mod (k a : Nat) : (a &&& onesBits k) = a % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_onesBits, Nat.testBit_mod_two_pow, Bool.and_comm]

/-- `k`-bit bitwise complement of `a`, defined by the same bit-step recursion as `bitwiseXorBits`. -/
def bitwiseComplementBits : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, a => (1 - a % 2) + 2 * bitwiseComplementBits k (a / 2)

theorem testBit_bitwiseComplementBits :
    ∀ (k a i : Nat),
      (bitwiseComplementBits k a).testBit i = (decide (i < k) && !a.testBit i)
  | 0, a, i => by
    show (0 : Nat).testBit i = _
    rw [Nat.zero_testBit]
    rfl
  | k + 1, a, 0 => by
    have hb : 1 - a % 2 < 2 := Nat.lt_of_le_of_lt (Nat.sub_le 1 (a % 2)) (by decide)
    refine (testBit_bitStep_zero hb).trans ?_
    rw [Nat.testBit_zero a]
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> simp [ha]
  | k + 1, a, j + 1 => by
    have hb : 1 - a % 2 < 2 := Nat.lt_of_le_of_lt (Nat.sub_le 1 (a % 2)) (by decide)
    refine (testBit_bitStep_succ hb j).trans ?_
    rw [testBit_bitwiseComplementBits k (a / 2) j, Nat.testBit_succ a j, decide_succ_lt_succ]

theorem bitwiseComplementBits_eq_xor_onesBits (k a : Nat) :
    bitwiseComplementBits k a = (a ^^^ onesBits k) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitwiseComplementBits, Nat.testBit_mod_two_pow, Nat.testBit_xor, testBit_onesBits]
  cases decide (i < k) <;> cases a.testBit i <;> rfl

private theorem bitStep_add_compl (r c q : Nat) (hr : r = 0 ∨ r = 1) :
    ((1 - r) + 2 * c) + (r + 2 * q) = 1 + 2 * (c + q) := by
  rcases hr with rfl | rfl
  · show (1 + 2 * c) + (0 + 2 * q) = 1 + 2 * (c + q)
    rw [Nat.zero_add, Nat.add_assoc, ← Nat.left_distrib]
  · show (0 + 2 * c) + (1 + 2 * q) = 1 + 2 * (c + q)
    rw [Nat.zero_add, ← Nat.add_assoc, Nat.add_comm (2 * c) 1, Nat.add_assoc, ← Nat.left_distrib]

theorem bitwiseComplementBits_add_eq_onesBits :
    ∀ (k a : Nat), a < 2 ^ k → bitwiseComplementBits k a + a = onesBits k
  | 0, a, ha => by
    match a, ha with
    | 0, _ => rfl
  | k + 1, a, ha => by
    have hDivLt : a / 2 < 2 ^ k :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2 (by rw [← Nat.pow_succ]; exact ha)
    have ih := bitwiseComplementBits_add_eq_onesBits k (a / 2) hDivLt
    have hDecomp : a % 2 + 2 * (a / 2) = a := by
      rw [Nat.add_comm]
      exact Nat.div_add_mod a 2
    show ((1 - a % 2) + 2 * bitwiseComplementBits k (a / 2)) + a = 1 + 2 * onesBits k
    conv => lhs; rhs; rw [← hDecomp]
    rw [bitStep_add_compl (a % 2) (bitwiseComplementBits k (a / 2)) (a / 2)
      (Nat.mod_two_eq_zero_or_one a), ih]

/-- Constructive (`Classical.choice`-free) equivalence between `(2 ^ k - 1) - a` and
    `(a ^^^ (2 ^ k - 1)) % 2 ^ k` for all `a < 2 ^ k`. -/
theorem onesBits_sub_eq_xor {k a : Nat} (ha : a < 2 ^ k) :
    onesBits k - a = (a ^^^ onesBits k) % 2 ^ k := by
  have hSub : onesBits k - a = bitwiseComplementBits k a := by
    rw [← bitwiseComplementBits_add_eq_onesBits k a ha, Nat.add_sub_cancel]
  rw [hSub, bitwiseComplementBits_eq_xor_onesBits]

/-- Equivalence between `evalSymOp2 .sub (2^64 - 1) a` (`u64::MAX.wrapping_sub(a)`) and
    `evalSymOp1 (.xorConst (2^64 - 1)) a` (`a ^ u64::MAX`) for all `a < word64Modulus`
    (proved without `Classical.choice`). -/
theorem evalSymOp2_sub_max_eq_xorConst_max {a : Nat} (ha : a < word64Modulus) :
    evalSymOp2 .sub 18446744073709551615 a = evalSymOp1 (.xorConst 18446744073709551615) a := by
  have ha' : a < 18446744073709551616 := ha
  have hle : a ≤ 18446744073709551615 := Nat.le_of_lt_succ ha'
  have hLt : 18446744073709551615 - a < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  have hSub : evalSymOp2 .sub 18446744073709551615 a = 18446744073709551615 - a := by
    show (18446744073709551615 + (18446744073709551616 - a % 18446744073709551616)) %
        18446744073709551616 = _
    rw [Nat.mod_eq_of_lt ha', ← Nat.add_sub_assoc (Nat.le_of_lt ha'),
      Nat.sub_add_comm hle, Nat.add_mod_right, Nat.mod_eq_of_lt hLt]
  rw [hSub]
  exact onesBits_sub_eq_xor (k := 64) ha

/-- **Universal typed-`u64` `UnOp::Not` ↔ `xorConst (2^64 - 1)` bridge
    (`evalUnaryNot_u64_eq_xorConst_max`)**: on **every** `u64` word `a < word64Modulus`,
    trusted `MirSemantics.evalUnaryNot` on `u64` equals `evalSymOp1 (.xorConst (2^64 - 1)) a`
    (proved without `Classical.choice`). -/
theorem evalUnaryNot_u64_eq_xorConst_max {a : Nat} (ha : a < word64Modulus)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨a, 8⟩ (some bridgeU64Ty) locals mem =
      .ok (.scalar ⟨evalSymOp1 (.xorConst 18446744073709551615) a, 8⟩) locals mem := by
  rw [evalUnaryNot_u64_eq_wrappingSubMax ha, evalSymOp2_sub_max_eq_xorConst_max ha]

/-- Universal typed-`u8` `UnOp::Not` bridge (`evalUnaryNot_u8_eq_xor_255`): on every `u8` byte
    `a < 256`, trusted `MirSemantics.evalUnaryNot` on `u8` computes `(a ^^^ 255) % 256` (`1` byte),
    which disagrees with `boolNot 0 = 1` on `a = 0`. -/
theorem evalUnaryNot_u8_eq_xor_255 {a : Nat} (ha : a < 256)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨a, 1⟩ (some bridgeU8Ty) locals mem =
      .ok (.scalar ⟨(a ^^^ 255) % 256, 1⟩) locals mem := by
  have hSubXor : 255 - a = (a ^^^ 255) % 256 := onesBits_sub_eq_xor (k := 8) ha
  show RvalueEvalResult.ok (.scalar ⟨Nat.sub 255 (wrapScalarBits a 256), 1⟩) locals mem = _
  rw [wrapScalarBits_of_lt ha]
  change RvalueEvalResult.ok (.scalar ⟨255 - a, 1⟩) locals mem = _
  rw [hSubXor]

/-- Universal `SymOp1.id` bridge: `wrapScalarBits a (scalarModulus 8)` equals `evalSymOp1 .id a`
    for **all** `a < word64Modulus`. -/
theorem evalSymOp1_id_eq_wrapScalarBits {a : Nat} (ha : a < word64Modulus) :
    wrapScalarBits a (scalarModulus 8) = evalSymOp1 .id a := by
  have ha' : a < 18446744073709551616 := ha
  show wrapScalarBits a 18446744073709551616 = a
  exact wrapScalarBits_of_lt ha'

/-- Universal `SymOp1.boolNot` bridge: `evalScalarBinOp .eq ⟨a, 8⟩ ⟨0, 8⟩` produces
    `evalSymOp1 .boolNot a` (`1`-byte `bool`) for **all** `a : Nat`. -/
theorem evalSymOp1_boolNot_eq_evalScalarBinOp
    (a : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .eq ⟨a, 8⟩ ⟨0, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp1 .boolNot a, 1⟩) locals mem :=
  evalSymOp2_eq_eq_evalScalarBinOp a 0 locals mem

/-- Universal `SymOp1.wrappingNeg64` bridge: `evalScalarBinOp .sub ⟨0, 8⟩ ⟨a, 8⟩` produces
    `evalSymOp1 .wrappingNeg64 a` (`8`-byte `u64`) for **all** `a < word64Modulus`. -/
theorem evalSymOp1_wrappingNeg64_eq_evalScalarBinOp
    {a : Nat} (ha : a < word64Modulus) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .sub ⟨0, 8⟩ ⟨a, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp1 .wrappingNeg64 a, 8⟩) locals mem := by
  have h0 : (0 : Nat) < word64Modulus := by decide
  have hSub := evalSymOp2_sub_eq_evalScalarBinOp h0 ha locals mem
  have hEq : evalSymOp2 .sub 0 a = evalSymOp1 .wrappingNeg64 a := by
    dsimp [evalSymOp2, evalSymOp1, wrap64]
    rw [Nat.zero_add]
  rw [hEq] at hSub
  exact hSub

/-- Universal `SymOp1.maskLow32` bridge: `evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨0xFFFFFFFF, 8⟩` produces
    `evalSymOp1 .maskLow32 a` (`a % 2^32`, `8` bytes) for **all** `a : Nat` (closing the sampled-only
    gap for `maskLow32` without `Classical.choice`). -/
theorem evalSymOp1_maskLow32_eq_evalScalarBinOp
    (a : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨0xFFFFFFFF, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp1 .maskLow32 a, 8⟩) locals mem := by
  rw [evalSymOp2_bitAnd_eq_evalScalarBinOp]
  have hMask : (a &&& 0xFFFFFFFF) % 18446744073709551616 = a % 4294967296 := by
    change (a &&& onesBits 32) % 2 ^ 64 = a % 2 ^ 32
    rw [and_onesBits_eq_mod 32 a]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt a (by decide)) (by decide))
  dsimp [evalSymOp2, evalSymOp1, wrap64, word64Modulus]
  rw [hMask]

/-- Universal `SymOp1.xorConst` bridge: `evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨wrap64 b, 8⟩` produces
    `evalSymOp1 (.xorConst b) a` for **all** `a b : Nat`. -/
theorem evalSymOp1_xorConst_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨wrap64 b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp1 (.xorConst b) a, 8⟩) locals mem := by
  rw [evalSymOp2_bitXor_eq_evalScalarBinOp]
  have hXor : (a ^^^ (b % 2 ^ 64)) % 2 ^ 64 = (a ^^^ b) % 2 ^ 64 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_mod_two_pow,
      Nat.testBit_mod_two_pow, Nat.testBit_xor]
    cases decide (i < 64) <;> cases a.testBit i <;> cases b.testBit i <;> rfl
  dsimp [evalSymOp2, evalSymOp1, wrap64, word64Modulus]
  exact congrArg (fun v => RvalueEvalResult.ok (.scalar ⟨v, 8⟩) locals mem) hXor

/-- Universal `SymOp1.addConst` bridge: `evalScalarBinOp .add ⟨a, 8⟩ ⟨wrap64 b, 8⟩` produces
    `evalSymOp1 (.addConst b) a` for **all** `a b : Nat`. -/
theorem evalSymOp1_addConst_eq_evalScalarBinOp
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .add ⟨a, 8⟩ ⟨wrap64 b, 8⟩ locals mem false =
      .ok (.scalar ⟨evalSymOp1 (.addConst b) a, 8⟩) locals mem := by
  rw [evalSymOp2_add_eq_evalScalarBinOp]
  dsimp [evalSymOp2, evalSymOp1, wrap64, word64Modulus]
  rw [Nat.add_mod_mod]

/-- **Universal `SymOp1` unary operator bridge (`bridge_symOp1_semantics_agree_universal`)**:
    for **every** `u64` word `a < word64Modulus` and constant `b : Nat`, all 6 `SymOp1` unary
    operators (`id`, `boolNot`, `wrappingNeg64`, `maskLow32`, `xorConst`, `addConst`) agree with
    their trusted `MirSemantics` encodings, and `xorConst (2^64 - 1)` agrees with typed `u64`
    `MirSemantics.evalUnaryNot`. -/
theorem bridge_symOp1_semantics_agree_universal
    {a : Nat} (ha : a < word64Modulus) (b : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    wrapScalarBits a (scalarModulus 8) = evalSymOp1 .id a ∧
      evalScalarBinOp .eq ⟨a, 8⟩ ⟨0, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp1 .boolNot a, 1⟩) locals mem ∧
      evalScalarBinOp .sub ⟨0, 8⟩ ⟨a, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp1 .wrappingNeg64 a, 8⟩) locals mem ∧
      evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨0xFFFFFFFF, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp1 .maskLow32 a, 8⟩) locals mem ∧
      evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨wrap64 b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp1 (.xorConst b) a, 8⟩) locals mem ∧
      evalScalarBinOp .add ⟨a, 8⟩ ⟨wrap64 b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp1 (.addConst b) a, 8⟩) locals mem ∧
      evalUnaryNot ⟨a, 8⟩ (some bridgeU64Ty) locals mem =
        .ok (.scalar ⟨evalSymOp1 (.xorConst 18446744073709551615) a, 8⟩) locals mem :=
  ⟨evalSymOp1_id_eq_wrapScalarBits ha,
   evalSymOp1_boolNot_eq_evalScalarBinOp a locals mem,
   evalSymOp1_wrappingNeg64_eq_evalScalarBinOp ha locals mem,
   evalSymOp1_maskLow32_eq_evalScalarBinOp a locals mem,
   evalSymOp1_xorConst_eq_evalScalarBinOp a b locals mem,
   evalSymOp1_addConst_eq_evalScalarBinOp a b locals mem,
   evalUnaryNot_u64_eq_xorConst_max ha locals mem⟩

/-- **Universal `u64` operator bridge (`bridge_u64_semantics_agree_universal`)**: for **every** pair
    of `u64` words `a, b` (the canonical-range hypotheses are needed only by `sub`), all 11 `SymOp2`
    operators agree with the trusted `MirSemantics.evalScalarBinOp` (`8`-byte results for
    arithmetic/bitwise/shift operators, `1`-byte `bool` results for comparisons). This upgrades the
    sampled `bridge_u64_semantics_agree` regression test to a theorem over the whole `u64` domain. -/
theorem bridge_u64_semantics_agree_universal
    {a b : Nat} (ha : a < word64Modulus) (hb : b < word64Modulus)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .add ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .add a b, 8⟩) locals mem ∧
      evalScalarBinOp .sub ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .sub a b, 8⟩) locals mem ∧
      evalScalarBinOp .mul ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .mul a b, 8⟩) locals mem ∧
      evalScalarBinOp .bitAnd ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .bitAnd a b, 8⟩) locals mem ∧
      evalScalarBinOp .bitOr ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .bitOr a b, 8⟩) locals mem ∧
      evalScalarBinOp .bitXor ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .bitXor a b, 8⟩) locals mem ∧
      evalScalarBinOp .shl ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .shl a b, 8⟩) locals mem ∧
      evalScalarBinOp .shr ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .shr a b, 8⟩) locals mem ∧
      evalScalarBinOp .eq ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .eq a b, 1⟩) locals mem ∧
      evalScalarBinOp .lt ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .lt a b, 1⟩) locals mem ∧
      evalScalarBinOp .le ⟨a, 8⟩ ⟨b, 8⟩ locals mem false =
        .ok (.scalar ⟨evalSymOp2 .le a b, 1⟩) locals mem :=
  ⟨evalSymOp2_add_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_sub_eq_evalScalarBinOp ha hb locals mem,
   evalSymOp2_mul_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_bitAnd_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_bitOr_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_bitXor_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_shl_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_shr_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_eq_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_lt_eq_evalScalarBinOp a b locals mem,
   evalSymOp2_le_eq_evalScalarBinOp a b locals mem⟩

/-!
### Compositional `DWLP mirDefaultWP` / `MirSemantics` Diamond Join-Cut Combinator (`evalJoinDiamondWP`, `wpMirJoinDiamond_sound`)
-/

/-- Check whether `st : MirExecState` is at the entry (`stmtIdx == 0`) of top-level basic block
    `joinBb` (`activeCallee == none`). -/
def isAtJoinBlockEntry (joinBb : BasicBlockIdx) : MirExecState → Option MachineState
  | .running s =>
    if s.memory.activeCallee.isNone && s.frame.blockIdx == joinBb && s.frame.stmtIdx == 0 then
      some s
    else
      none
  | _ => none

theorem isAtJoinBlockEntry_eq_some
    {joinBb : BasicBlockIdx} {st : MirExecState} {sJoin : MachineState}
    (h : isAtJoinBlockEntry joinBb st = some sJoin) :
    st = .running sJoin ∧
      sJoin.memory.activeCallee = none ∧
      sJoin.frame.blockIdx = joinBb ∧
      sJoin.frame.stmtIdx = 0 := by
  cases st with
  | halted _ => cases h
  | faulted _ => cases h
  | running s =>
    dsimp [isAtJoinBlockEntry] at h
    split at h
    · rename_i hCond
      injection h with hEq
      subst hEq
      simp [Bool.and_eq_true, Option.isNone_iff_eq_none] at hCond
      exact ⟨rfl, hCond.1.1, hCond.1.2, hCond.2⟩
    · cases h

/-- Single-pass fuel-bounded symbolic WP with a compositional join-block cut at basic block
    `joinBb`: steps from `st` through prefix statements and branch terminators (`SwitchInt`
    arms), and whenever a transition lands at the entry (`stmtIdx = 0`, `activeCallee = none`)
    of `joinBb`, discharges `cut sJoin` instead of duplicating `joinBb`'s continuation across
    every incoming path. -/
def wpMirUntilJoinSym
    (fuel : Nat) (body : CapturedMir) (joinBb : BasicBlockIdx) (st : MirExecState)
    (cut : MachineState → Prop) (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTree
      (fun st' =>
        match isAtJoinBlockEntry joinBb st' with
        | some sJoin => cut sJoin
        | none => wpMirUntilJoinSym fuel' body joinBb st' cut post)
      post
      (stepMirExecSymTree body st)

/-- Fuel monotonicity of `wpMirExecSym` (`omega`-free, so it stays within `{propext, Quot.sound}`). -/
theorem wpMirExecSym_mono_fuel
    {f₁ f₂ : Nat} (hle : f₁ ≤ f₂)
    {body : CapturedMir} {st : MirExecState} {post : MirOutcome → Prop}
    (h : wpMirExecSym f₁ body st post) :
    wpMirExecSym f₂ body st post := by
  induction f₁ generalizing f₂ st with
  | zero => exact False.elim h
  | succ f₁' ih =>
    cases f₂ with
    | zero => exact absurd hle (Nat.not_succ_le_zero f₁')
    | succ f₂' =>
      have hle' : f₁' ≤ f₂' := Nat.le_of_succ_le_succ hle
      unfold wpMirExecSym at h ⊢
      rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h ⊢
      cases h_step : stepMirState body st with
      | ret _ =>
        rw [h_step] at h
        exact h
      | tau st' =>
        rw [h_step] at h
        exact ih hle' h
      | vis i k =>
        rw [h_step] at h
        exact mirDefaultWP.mono (fun _ _ hw => ih hle' hw) h

theorem wpMirSym_mono_fuel
    {f₁ f₂ : Nat} (hle : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : wpMirSym f₁ body s post) :
    wpMirSym f₂ body s post :=
  wpMirExecSym_mono_fuel hle h

/-- Compositional cut-elimination theorem for `wpMirUntilJoinSym`: combining a prefix execution
    `wpMirUntilJoinSym prefixFuel body joinBb st cut post` with a single suffix proof
    `∀ sJoin, cut sJoin → wpMirSym suffixFuel body sJoin post` yields
    `wpMirExecSym (prefixFuel + suffixFuel) body st post`. -/
theorem wpMirUntilJoinSym_to_wpMirExecSym
    {prefixFuel suffixFuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {st : MirExecState}
    {cut : MachineState → Prop}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb st cut post)
    (hJoin : ∀ sJoin : MachineState, cut sJoin → wpMirSym suffixFuel body sJoin post) :
    wpMirExecSym (prefixFuel + suffixFuel) body st post := by
  induction prefixFuel generalizing st with
  | zero => exact False.elim hPrefix
  | succ fuel' ih =>
    rw [Nat.add_right_comm fuel' 1 suffixFuel]
    unfold wpMirUntilJoinSym at hPrefix
    unfold wpMirExecSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at hPrefix ⊢
    have hStepJoin :
        ∀ st' : MirExecState,
          (match isAtJoinBlockEntry joinBb st' with
           | some sJoin => cut sJoin
           | none => wpMirUntilJoinSym fuel' body joinBb st' cut post) →
          wpMirExecSym (fuel' + suffixFuel) body st' post := by
      intro st' hCont
      cases hAt : isAtJoinBlockEntry joinBb st' with
      | some sJoin =>
        rw [hAt] at hCont
        rcases isAtJoinBlockEntry_eq_some hAt with ⟨rfl, _, _, _⟩
        exact wpMirExecSym_mono_fuel (Nat.le_add_left suffixFuel fuel') (hJoin sJoin hCont)
      | none =>
        rw [hAt] at hCont
        exact ih hCont
    cases h_step : stepMirState body st with
    | ret _ =>
      rw [h_step] at hPrefix
      exact hPrefix
    | tau st' =>
      rw [h_step] at hPrefix
      exact hStepJoin st' hPrefix
    | vis i k =>
      rw [h_step] at hPrefix
      exact mirDefaultWP.mono (fun o _ hw => hStepJoin (k o) hw) hPrefix

/-- Coinductive `DWLP mirDefaultWP` soundness of `wpMirUntilJoinSym`: if `wpMirUntilJoinSym`
    holds up to `joinBb` with cut predicate `cut`, and every `sJoin` satisfying `cut` satisfies
    `DWLP mirDefaultWP (mirTree body sJoin)`, then `DWLP mirDefaultWP` holds from `st`. -/
theorem dwlp_of_wpMirUntilJoinSym
    {fuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {st : MirExecState}
    {cut : MachineState → Prop}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym fuel body joinBb st cut post)
    (hJoin :
      ∀ sJoin : MachineState,
        cut sJoin →
        DWLP mirDefaultWP (mirTree body sJoin) (fun out _ => post out) PUnit.unit) :
    DWLP mirDefaultWP (ITree.cofix (stepMirState body) st) (fun out _ => post out) PUnit.unit := by
  induction fuel generalizing st with
  | zero => exact False.elim hPrefix
  | succ fuel' ih =>
    unfold wpMirUntilJoinSym at hPrefix
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at hPrefix
    have hStepJoin :
        ∀ st' : MirExecState,
          (match isAtJoinBlockEntry joinBb st' with
           | some sJoin => cut sJoin
           | none => wpMirUntilJoinSym fuel' body joinBb st' cut post) →
          DWLP mirDefaultWP (ITree.cofix (stepMirState body) st')
            (fun out _ => post out) PUnit.unit := by
      intro st' hCont
      cases hAt : isAtJoinBlockEntry joinBb st' with
      | some sJoin =>
        rw [hAt] at hCont
        rcases isAtJoinBlockEntry_eq_some hAt with ⟨rfl, _, _, _⟩
        exact hJoin sJoin hCont
      | none =>
        rw [hAt] at hCont
        exact ih hCont
    rw [DWLP.unfold_eq, ITree.observe_cofix]
    cases h_step : stepMirState body st with
    | ret out =>
      rw [h_step] at hPrefix
      dsimp only [ITreeF.map]
      exact hPrefix
    | tau st' =>
      rw [h_step] at hPrefix
      dsimp only [ITreeF.map]
      exact hStepJoin st' hPrefix
    | vis i k =>
      rw [h_step] at hPrefix
      dsimp only [ITreeF.map]
      exact mirDefaultWP.mono (fun o _ hw => hStepJoin (k o) hw) hPrefix

/-- Merge two `MirSemantics.LocalSlot`s reaching a join block from the two `SwitchInt` arms, under an
    **untrusted** per-slot hint `differs` (the production-semantics analogue of `JoinHints`):
    - `differs = false`: the arms are expected to agree on this slot, which is kept **verbatim** from
      the `then` arm (no `ite`, so the join continuation sees exactly the shared value);
    - `differs = true`:
      1. when both arms hold initialized scalars of the same width (`Nat.beq scT.sizeBytes scF.sizeBytes`),
         the merged slot pushes `if cond` **inside** `ScalarInt.bits`, so `evalOperand` / `evalRvalue` in
         the join block see a single `.init (.scalar ⟨_, sz⟩)` constructor and never re-split on `cond`;
      2. when the arms differ in slot kind or width (e.g., a branch-local scratch temporary `_3` left
         `.init` or `.uninit` in one arm and `.dead` in the other), the merged slot places
         `if cond then sT else sF` at that slot index — allowing a join block that either never reads
         the dead scratch slot or cleans it up via `StorageDead`/`StorageLive` to step once by `rfl`,
         while still faulting if the join block attempts to read a dead/uninitialized scratch slot!
    The hint is never trusted: `mergeMirJoinState_eq_ite` only fires under `MirArmsAgree`, and the
    join cut (`evalJoinDiamondWP`) independently checks that each arm reaches the merged state. -/
def mergeMirScalarSlot (cond differs : Bool) (sT sF : LocalSlot) : LocalSlot :=
  match differs, sT, sF with
  | false, _, _ => sT
  | true, .init (.scalar scT), .init (.scalar scF) =>
    if Nat.beq scT.sizeBytes scF.sizeBytes then
      .init (.scalar { bits := if cond then scT.bits else scF.bits, sizeBytes := scT.sizeBytes })
    else
      if cond then sT else sF
  | true, _, _ => if cond then sT else sF

/-- Pointwise hint-driven merge of two `List LocalSlot` local stores; slots beyond the hint list
    are kept verbatim from the `then` arm. -/
def mergeMirLocalSlots (cond : Bool) : List Bool → List LocalSlot → List LocalSlot → List LocalSlot
  | d :: ds, sT :: restT, sF :: restF =>
    mergeMirScalarSlot cond d sT sF :: mergeMirLocalSlots cond ds restT restF
  | _, lT, _ => lT

/-- Merge two `MachineState`s `(sT, sF)` arriving at the same join block entry under `cond`. The
    control point (`blockIdx`, `stmtIdx`) and the `Memory` are taken from `sT` **without** an `ite`:
    an `if cond then 3 else 3` block index or an `ite` over memories would block every later
    `stepMirState` reduction on a symbolic `cond`. `MirArmsAgree` is exactly the side condition
    under which the merge is the state-level `if cond then sT else sF` (`mergeMirJoinState_eq_ite`). -/
def mergeMirJoinState (cond : Bool) (differs : List Bool) (sT sF : MachineState) : MachineState :=
  { frame :=
      { blockIdx := sT.frame.blockIdx
        stmtIdx := sT.frame.stmtIdx
        locals := mergeMirLocalSlots cond differs sT.frame.locals sF.frame.locals }
    memory := sT.memory }

/-- Per-slot arm agreement demanded by the `differs` hint: equal slots when `differs = false`,
    unrestricted when `differs = true` (equal-width scalars fold `if cond` into `ScalarInt.bits`;
    diverging dead/scratch slots fold `if cond` into that single `LocalSlot`). -/
def MirArmSlotAgree (differs : Bool) (sT sF : LocalSlot) : Prop :=
  match differs with
  | false => sT = sF
  | true => True

/-- Pointwise `MirArmSlotAgree`; slots beyond the hint list must be equal. -/
def MirArmSlotsAgree : List Bool → List LocalSlot → List LocalSlot → Prop
  | d :: ds, sT :: restT, sF :: restF => MirArmSlotAgree d sT sF ∧ MirArmSlotsAgree ds restT restF
  | _, lT, lF => lT = lF

/-- The two arm states agree on the control point, on the whole `Memory`, and on every local
    outside the hinted `differs` slots. -/
structure MirArmsAgree (differs : List Bool) (sT sF : MachineState) : Prop where
  blockIdx : sT.frame.blockIdx = sF.frame.blockIdx
  stmtIdx : sT.frame.stmtIdx = sF.frame.stmtIdx
  memory : sT.memory = sF.memory
  locals : MirArmSlotsAgree differs sT.frame.locals sF.frame.locals

theorem mergeMirScalarSlot_true (d : Bool) (sT sF : LocalSlot) :
    mergeMirScalarSlot true d sT sF = sT := by
  cases d with
  | false => rfl
  | true =>
    cases sT with
    | dead => rfl
    | uninit => rfl
    | init vT =>
      cases vT with
      | scalar scT =>
        cases sF with
        | dead => rfl
        | uninit => rfl
        | init vF =>
          cases vF with
          | scalar scF =>
            dsimp [mergeMirScalarSlot]
            cases Nat.beq scT.sizeBytes scF.sizeBytes <;> rfl
          | _ => rfl
      | _ => rfl

theorem mergeMirScalarSlot_false {d : Bool} {sT sF : LocalSlot} (h : MirArmSlotAgree d sT sF) :
    mergeMirScalarSlot false d sT sF = sF := by
  cases d with
  | false => exact h
  | true =>
    cases sT with
    | dead => rfl
    | uninit => rfl
    | init vT =>
      cases vT with
      | scalar scT =>
        cases sF with
        | dead => rfl
        | uninit => rfl
        | init vF =>
          cases vF with
          | scalar scF =>
            dsimp [mergeMirScalarSlot]
            cases hSz : Nat.beq scT.sizeBytes scF.sizeBytes with
            | false => rfl
            | true =>
              rcases scF with ⟨bitsF, szF⟩
              have hEq : scT.sizeBytes = szF := (nat_beq_eq_true_iff _ _).1 hSz
              rw [hEq]
              rfl
          | _ => rfl
      | _ => rfl

theorem mergeMirScalarSlot_self (cond d : Bool) (s : LocalSlot) :
    mergeMirScalarSlot cond d s s = s := by
  cases cond with
  | false =>
    cases d with
    | false => rfl
    | true => exact mergeMirScalarSlot_false (d := true) trivial
  | true => exact mergeMirScalarSlot_true d s s

theorem mergeMirLocalSlots_true :
    ∀ (ds : List Bool) (lT lF : List LocalSlot), mergeMirLocalSlots true ds lT lF = lT
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | d :: ds, sT :: restT, sF :: restF => by
    show mergeMirScalarSlot true d sT sF :: mergeMirLocalSlots true ds restT restF = sT :: restT
    rw [mergeMirScalarSlot_true, mergeMirLocalSlots_true ds restT restF]

theorem mergeMirLocalSlots_false :
    ∀ {ds : List Bool} {lT lF : List LocalSlot}, MirArmSlotsAgree ds lT lF →
      mergeMirLocalSlots false ds lT lF = lF
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | _ :: _, _ :: _, [], h => h
  | _ :: _, _ :: _, _ :: _, h => by
    show mergeMirScalarSlot false _ _ _ :: mergeMirLocalSlots false _ _ _ = _ :: _
    rw [mergeMirScalarSlot_false h.1, mergeMirLocalSlots_false h.2]

theorem mergeMirLocalSlots_self (cond : Bool) :
    ∀ (ds : List Bool) (ls : List LocalSlot), mergeMirLocalSlots cond ds ls ls = ls
  | [], _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, s :: rest => by
    show mergeMirScalarSlot cond d s s :: mergeMirLocalSlots cond ds rest rest = s :: rest
    rw [mergeMirScalarSlot_self, mergeMirLocalSlots_self cond ds rest]

theorem mergeMirJoinState_true (ds : List Bool) (sT sF : MachineState) :
    mergeMirJoinState true ds sT sF = sT := by
  rcases sT with ⟨⟨bbT, stT, locT⟩, memT⟩
  show MachineState.mk ⟨bbT, stT, mergeMirLocalSlots true ds locT sF.frame.locals⟩ memT = _
  rw [mergeMirLocalSlots_true]

theorem mergeMirJoinState_false {ds : List Bool} {sT sF : MachineState}
    (h : MirArmsAgree ds sT sF) :
    mergeMirJoinState false ds sT sF = sF := by
  rcases sT with ⟨⟨bbT, stT, locT⟩, memT⟩
  rcases sF with ⟨⟨bbF, stF, locF⟩, memF⟩
  rcases h with ⟨hBb, hSt, hMem, hLoc⟩
  dsimp only at hBb hSt hMem hLoc
  subst hBb hSt hMem
  show MachineState.mk ⟨bbT, stT, mergeMirLocalSlots false ds locT locF⟩ memT = _
  rw [mergeMirLocalSlots_false hLoc]

/-- Under `MirArmsAgree`, the hint-driven merge **is** the state-level `if cond then sT else sF`
    (for both values of `cond`), yet, unlike that `ite`, it reduces structurally for a symbolic
    `cond`, so a join continuation can be evaluated once on it. -/
theorem mergeMirJoinState_eq_ite {cond : Bool} {ds : List Bool} {sT sF : MachineState}
    (h : MirArmsAgree ds sT sF) :
    mergeMirJoinState cond ds sT sF = if cond then sT else sF := by
  cases cond with
  | false => exact mergeMirJoinState_false h
  | true => exact mergeMirJoinState_true ds sT sF

theorem mergeMirJoinState_self (cond : Bool) (ds : List Bool) (s : MachineState) :
    mergeMirJoinState cond ds s s = s := by
  rcases s with ⟨⟨bb, st, loc⟩, mem⟩
  show MachineState.mk ⟨bb, st, mergeMirLocalSlots cond ds loc loc⟩ mem = _
  rw [mergeMirLocalSlots_self]

/-- Production `MirSemantics` / `DWLP mirDefaultWP` diamond join-cut combinator
    (`evalJoinDiamondWP`):
    1. Steps `body` from `s` up to the join basic block entry `(joinBb, 0)` via
       `wpMirUntilJoinSym prefixFuel body joinBb (.running s) (fun s' => s' = sJoin) post`,
       verifying that both `SwitchInt` branches reach the single merged join state `sJoin`
       (e.g., via canonicalized dead temporaries or `mergeMirJoinState`), and
    2. Proves the continuation from `joinBb` **once** on `sJoin` via
       `wpMirSym suffixFuel body sJoin post`. -/
def evalJoinDiamondWP
    (prefixFuel suffixFuel : Nat)
    (body : CapturedMir)
    (joinBb : BasicBlockIdx)
    (s sJoin : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpMirUntilJoinSym prefixFuel body joinBb (.running s) (fun s' => s' = sJoin) post ∧
    wpMirSym suffixFuel body sJoin post

/-- `evalJoinDiamondWP` implies `wpMirSym (prefixFuel + suffixFuel) body s post`. -/
theorem wpMirSym_of_evalJoinDiamondWP
    {prefixFuel suffixFuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {s sJoin : MachineState}
    {post : MirOutcome → Prop}
    (h : evalJoinDiamondWP prefixFuel suffixFuel body joinBb s sJoin post) :
    wpMirSym (prefixFuel + suffixFuel) body s post :=
  wpMirUntilJoinSym_to_wpMirExecSym h.1 (fun _ hEq => hEq ▸ h.2)

/-- Total-correctness (`DWP mirDefaultWP`) soundness of `evalJoinDiamondWP`. -/
theorem dwpMirJoinDiamond_sound
    {prefixFuel suffixFuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {s sJoin : MachineState}
    {post : MirOutcome → Prop}
    (h : evalJoinDiamondWP prefixFuel suffixFuel body joinBb s sJoin post) :
    DWP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  dwp_of_wpMirSym (wpMirSym_of_evalJoinDiamondWP h)

/-- **Compositional `DWLP mirDefaultWP` Diamond Join-Cut Soundness (`wpMirJoinDiamond_sound`)**:
    When both `SwitchInt` arms step to the join block `joinBb` with states matching `sJoin`,
    proving the suffix `wpMirSym suffixFuel body sJoin post` **once** on `sJoin` discharges
    `DWLP mirDefaultWP (mirTree body s)` without duplicating `joinBb` across branches. -/
theorem wpMirJoinDiamond_sound
    {prefixFuel suffixFuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {s sJoin : MachineState}
    {post : MirOutcome → Prop}
    (h : evalJoinDiamondWP prefixFuel suffixFuel body joinBb s sJoin post) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  (dwpMirJoinDiamond_sound h).toDWLP

/-- Coinductive `DWLP mirDefaultWP` variant of `wpMirJoinDiamond_sound` taking a direct
    `DWLP mirDefaultWP (mirTree body sJoin)` continuation hypothesis at `joinBb`. -/
theorem wpMirJoinDiamond_dwlp_sound
    {prefixFuel : Nat}
    {body : CapturedMir}
    {joinBb : BasicBlockIdx}
    {s sJoin : MachineState}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s) (fun s' => s' = sJoin) post)
    (hJoin : DWLP mirDefaultWP (mirTree body sJoin) (fun out _ => post out) PUnit.unit) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  dwlp_of_wpMirUntilJoinSym hPrefix (fun _ hEq => hEq ▸ hJoin)

/-- **Hint-driven merged diamond join cut (`wpMirJoinDiamond_merge_sound`)**: if the prefix from `s`
    reaches the join entry in the state-level `if cond then sT else sF` (each `SwitchInt` arm reaches
    its own natural arm state), the arms agree outside the untrusted `differs` hint
    (`MirArmsAgree`), and the join continuation holds **once** on the structurally merged state
    `mergeMirJoinState cond differs sT sF` (in which hinted equal-width scalar slots carry
    `if cond then _ else _` bits and hinted dead/scratch slots carry `if cond then sT[i] else sF[i]`),
    then `evalJoinDiamondWP` holds for that merged state; hence
    (`wpMirSym_of_evalJoinDiamondWP` / `wpMirJoinDiamond_sound`) the whole diamond is verified
    without evaluating the join block twice. A wrong hint can only make `MirArmsAgree` or `hJoin`
    unprovable (`mirJoinDiamond_unhinted_merge_rejected`,
    `mirJoinAsymmetricScratch_read_dead_slot3_rejected`), never unsound. -/
theorem wpMirJoinDiamond_merge_sound
    {prefixFuel suffixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {differs : List Bool} {sT sF : MachineState}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then sT else sF) post)
    (hAgree : MirArmsAgree differs sT sF)
    (hJoin : wpMirSym suffixFuel body (mergeMirJoinState cond differs sT sF) post) :
    evalJoinDiamondWP prefixFuel suffixFuel body joinBb s
      (mergeMirJoinState cond differs sT sF) post := by
  rw [mergeMirJoinState_eq_ite hAgree] at hJoin ⊢
  exact ⟨hPrefix, hJoin⟩

/-- Coinductive `DWLP mirDefaultWP` form of `wpMirJoinDiamond_merge_sound`. -/
theorem wpMirJoinDiamond_merge_dwlp_sound
    {prefixFuel : Nat} {body : CapturedMir} {joinBb : BasicBlockIdx}
    {s : MachineState} {cond : Bool} {differs : List Bool} {sT sF : MachineState}
    {post : MirOutcome → Prop}
    (hPrefix : wpMirUntilJoinSym prefixFuel body joinBb (.running s)
      (fun s' => s' = if cond then sT else sF) post)
    (hAgree : MirArmsAgree differs sT sF)
    (hJoin : DWLP mirDefaultWP (mirTree body (mergeMirJoinState cond differs sT sF))
      (fun out _ => post out) PUnit.unit) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit := by
  rw [mergeMirJoinState_eq_ite hAgree] at hJoin
  exact wpMirJoinDiamond_dwlp_sound hPrefix hJoin

section MirJoinDiamondWitness

private def u64JoinMirTy : Ty := { kind := .uint .u64, layoutIdx := 0 }

private def u64JoinConstOp (n : Nat) : Operand :=
  .constant { ty := u64JoinMirTy, val := .scalar (.int { bits := n, sizeBytes := 8 }) }

private def defaultU64JoinLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 8 }
    backendRepr := .scalar (.initialized (.int 64 false) ⟨0, 18446744073709551615⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

private def defaultU64JoinFnAbi : FnAbi :=
  { args := []
    ret := { layout := defaultU64JoinLayout, mode := .direct }
    conv := .rust
    canUnwind := true }

/-- Production `CapturedMir` diamond body (`mirJoinDiamondBody`):
    - `_0`: `u64` return slot,
    - `_1`: `u64` input `x`,
    - `_2`: `u64` branch selector `flag`,
    - `_3`: branch-local `u64` temporary used only in the `then` arm (`bb1`), killed via
      `StorageDead(3)` before jumping to `bb3`.
    - `bb0`: `SwitchInt(_2)` (`0 -> bb2`, `otherwise -> bb1`),
    - `bb1` (`then` arm): `StorageLive(_3); _3 := _1 + 10; _0 := _3; StorageDead(_3); goto bb3`,
    - `bb2` (`else` arm): `_0 := _1 + 20; goto bb3`,
    - `bb3` (join block): `_0 := _0 + _1; return`. -/
def mirJoinDiamondBody : CapturedMir :=
  { defPath := "sym_eval::mir_join_diamond_witness"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 2
    localDecls :=
      [ { mutability := .mut, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .mut, ty := u64JoinMirTy, debugName := none } ]
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 2, projection := [] })
                { branches := [(0, 2)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .storageLive 3, span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 3, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 0, projection := [] }
                  (.use (.copy { local_ := 3, projection := [] }))
                span := "SymbolicEval.lean" }
            , { kind := .storageDead 3, span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 20))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 1, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ]
    fnAbi := defaultU64JoinFnAbi
    layouts := emptyLayoutTable
    allocations := [] }

/-- Join-entry state of `mirJoinDiamondBody` at `bb3` (`stmtIdx = 0`) after an arm that stored
    `armVal` into `_0`: `_1 = x`, `_2 = flag`, and `_3` dead (killed by `StorageDead(3)` in `bb1`,
    never made live in `bb2`); the memory is the untouched initial memory. -/
def mirJoinDiamondArmState (x flag armVal : Nat) : MachineState :=
  let sInit := initMachineState mirJoinDiamondBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩]
  { sInit with
    frame :=
      { blockIdx := 3
        stmtIdx := 0
        locals :=
          [ .init (.scalar ⟨armVal, 8⟩)
          , .init (.scalar ⟨x, 8⟩)
          , .init (.scalar ⟨flag, 8⟩)
          , .dead ] } }

/-- Value stored into `_0` by the `else` arm `bb2` (`_0 := _1 + 20`, taken when `flag = 0`). -/
def mirJoinDiamondElseVal (x : Nat) : Nat := wrapScalarBits (Nat.add x 20) (scalarModulus 8)

/-- Value stored into `_0` by the `then` arm `bb1` (`_3 := _1 + 10; _0 := _3`, taken when
    `flag ≠ 0`). -/
def mirJoinDiamondThenVal (x : Nat) : Nat := wrapScalarBits (Nat.add x 10) (scalarModulus 8)

/-- Untrusted merge hint for `mirJoinDiamondBody`: only `_0` differs between the arms. -/
def mirJoinDiamondDiffers : List Bool := [true, false, false, false]

/-- State-level `ite` over the two arm states: what the prefix of `mirJoinDiamondBody` reaches. -/
def mirJoinDiamondArmResult (x flag : Nat) : MachineState :=
  if Nat.beq flag 0 then mirJoinDiamondArmState x flag (mirJoinDiamondElseVal x)
  else mirJoinDiamondArmState x flag (mirJoinDiamondThenVal x)

/-- Merged join state at `bb3`, built by the hint-driven `mergeMirJoinState` over the branch
    condition `Nat.beq flag 0`: `_0` carries `if Nat.beq flag 0 then x + 20 else x + 10` (wrapped)
    **inside** its scalar bits, while `_1`, `_2`, `_3`, the control point and the memory are shared
    verbatim. -/
def mirJoinDiamondMergedState (x flag : Nat) : MachineState :=
  mergeMirJoinState (Nat.beq flag 0) mirJoinDiamondDiffers
    (mirJoinDiamondArmState x flag (mirJoinDiamondElseVal x))
    (mirJoinDiamondArmState x flag (mirJoinDiamondThenVal x))

theorem mirJoinDiamond_arms_agree (x flag : Nat) :
    MirArmsAgree mirJoinDiamondDiffers
      (mirJoinDiamondArmState x flag (mirJoinDiamondElseVal x))
      (mirJoinDiamondArmState x flag (mirJoinDiamondThenVal x)) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, rfl, rfl⟩⟩

/-- **Non-Vacuity Witness for `evalJoinDiamondWP` / `wpMirJoinDiamond_merge_sound`
    (`mirJoinDiamond_evalJoinDiamondWP`)**: for all `x, flag : Nat`,
    1. each arm of `mirJoinDiamondBody` (`bb1` with the `StorageLive`/`StorageDead` temporary `_3`,
       `bb2` without it) steps via `wpMirUntilJoinSym` to its own arm state at `bb3`,
    2. the arms agree outside the hinted slot `_0` (`mirJoinDiamond_arms_agree`), and
    3. `bb3` is symbolically evaluated **once** on `mirJoinDiamondMergedState x flag` (built by
       `mergeMirJoinState`, without re-splitting on `Nat.beq flag 0`). -/
theorem mirJoinDiamond_evalJoinDiamondWP (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then
        wrapScalarBits (Nat.add x 20) (scalarModulus 8)
      else
        wrapScalarBits (Nat.add x 10) (scalarModulus 8)
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    evalJoinDiamondWP 6 3 mirJoinDiamondBody 3
      (initMachineState mirJoinDiamondBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirJoinDiamondMergedState x flag)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) := by
  intro armVal expectedRet
  refine wpMirJoinDiamond_merge_sound ?_ (mirJoinDiamond_arms_agree x flag) ?_
  · -- Prefix cut up to join block `bb3`: each arm reaches its own arm state.
    show wpMirUntilJoinSym 6 mirJoinDiamondBody 3 _
      (fun s' => s' = mirJoinDiamondArmResult x flag) _
    (repeat' ((conv => whnf); split)); all_goals
      (rename_i hCond; change Nat.beq flag 0 = _ at hCond;
       dsimp only [mirJoinDiamondArmResult]; rw [hCond]; rfl)
  · -- Suffix from `bb3` evaluated ONCE on the merged state:
    rfl

/-- Fuel-level (`wpMirSym`) end-to-end witness of the merged diamond join cut. It stays within
    `{propext, Quot.sound}`, unlike the `DWLP`/`DWP` corollaries, whose *statements* mention the
    `coinductive_fixpoint`/`inductive_fixpoint`-built `Anneal.ITreeWP.DWLP`/`DWP` (which themselves
    depend on `Classical.choice`). -/
theorem mirJoinDiamond_wpMirSym_witness (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then
        wrapScalarBits (Nat.add x 20) (scalarModulus 8)
      else
        wrapScalarBits (Nat.add x 10) (scalarModulus 8)
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    wpMirSym 9 mirJoinDiamondBody
      (initMachineState mirJoinDiamondBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) :=
  wpMirSym_of_evalJoinDiamondWP (mirJoinDiamond_evalJoinDiamondWP x flag)

/-- `DWLP mirDefaultWP` witness on `mirCallTree mirJoinDiamondBody` via `wpMirJoinDiamond_sound`. -/
theorem mirJoinDiamond_verified_witness (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then
        wrapScalarBits (Nat.add x 20) (scalarModulus 8)
      else
        wrapScalarBits (Nat.add x 10) (scalarModulus 8)
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    DWLP mirDefaultWP
      (mirCallTree mirJoinDiamondBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (fun out _ =>
        mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩) out)
      PUnit.unit :=
  wpMirJoinDiamond_sound (mirJoinDiamond_evalJoinDiamondWP x flag)

/-- **Negative control: the join cut is discriminating.** With `flag = 0` the `else` arm runs, so a
    cut demanding the `then` arm's state at `bb3` is refuted (the prefix check is not vacuous). -/
theorem mirJoinDiamond_cut_rejects_wrong_arm :
    ¬ wpMirUntilJoinSym 6 mirJoinDiamondBody 3
      (.running (initMachineState mirJoinDiamondBody [.scalar ⟨1, 8⟩, .scalar ⟨0, 8⟩]))
      (fun s' => s' = mirJoinDiamondArmState 1 0 (mirJoinDiamondThenVal 1)) (fun _ => True) := by
  intro h
  change mirJoinDiamondArmState 1 0 (mirJoinDiamondElseVal 1) =
    mirJoinDiamondArmState 1 0 (mirJoinDiamondThenVal 1) at h
  have hBits := congrArg (fun s : MachineState => match s.frame.locals with
    | .init (.scalar sc) :: _ => sc.bits
    | _ => 0) h
  exact absurd hBits (by decide)

/-- **Negative control: the merge hint is untrusted.** Without the `differs` hint on `_0`, the arms
    do not agree, so `mergeMirJoinState_eq_ite` / `wpMirJoinDiamond_merge_sound` cannot fire: a wrong
    hint makes verification fail, never unsound. -/
theorem mirJoinDiamond_unhinted_merge_rejected :
    ¬ MirArmsAgree [false, false, false, false]
      (mirJoinDiamondArmState 0 0 (mirJoinDiamondElseVal 0))
      (mirJoinDiamondArmState 0 0 (mirJoinDiamondThenVal 0)) := by
  intro h
  have hBits := congrArg (fun s : LocalSlot => match s with
    | .init (.scalar sc) => sc.bits
    | _ => 0) h.locals.1
  exact absurd hBits (by decide)

/-- **Asymmetric Dead/Scratch Slot Diamond (`mirJoinAsymmetricScratchBody`)**:
    Unlike `mirJoinDiamondBody`, `bb1` (`then` arm) allocates and initializes scratch local `_3`
    (`StorageLive(3); _3 := _1 + 10; _0 := _3; goto bb3`) **without** executing `StorageDead(3)`
    before jumping to `bb3`, while `bb2` (`else` arm) never touches `_3` (leaving `_3 = .dead`).
    At `bb3` entry, `_3` is `.dead` on `bb2` (`flag = 0`) and `.init (.scalar ⟨x + 10, 8⟩)` on
    `bb1` (`flag ≠ 0`). Because `_3` is dead (unused) in `bb3`, `mergeMirJoinState` with
    `differs = [true, false, false, true]` merges both arms and evaluates `bb3` **once** by `rfl`. -/
def mirJoinAsymmetricScratchBody : CapturedMir :=
  { mirJoinDiamondBody with
    defPath := "sym_eval::mir_join_asymmetric_scratch_witness"
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 2, projection := [] })
                { branches := [(0, 2)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .storageLive 3, span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 3, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 0, projection := [] }
                  (.use (.copy { local_ := 3, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 20))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 1, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ] }

/-- Join-entry state of `mirJoinAsymmetricScratchBody` at `bb3` with explicit slot `_3` state. -/
def mirJoinAsymmetricArmState (x flag armVal : Nat) (slot3 : LocalSlot) : MachineState :=
  let sInit := initMachineState mirJoinAsymmetricScratchBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩]
  { sInit with
    frame :=
      { blockIdx := 3
        stmtIdx := 0
        locals :=
          [ .init (.scalar ⟨armVal, 8⟩)
          , .init (.scalar ⟨x, 8⟩)
          , .init (.scalar ⟨flag, 8⟩)
          , slot3 ] } }

def mirJoinAsymmetricDiffers : List Bool := [true, false, false, true]

def mirJoinAsymmetricArmResult (x flag : Nat) : MachineState :=
  if Nat.beq flag 0 then
    mirJoinAsymmetricArmState x flag (mirJoinDiamondElseVal x) .dead
  else
    mirJoinAsymmetricArmState x flag (mirJoinDiamondThenVal x)
      (.init (.scalar ⟨mirJoinDiamondThenVal x, 8⟩))

def mirJoinAsymmetricMergedState (x flag : Nat) : MachineState :=
  mergeMirJoinState (Nat.beq flag 0) mirJoinAsymmetricDiffers
    (mirJoinAsymmetricArmState x flag (mirJoinDiamondElseVal x) .dead)
    (mirJoinAsymmetricArmState x flag (mirJoinDiamondThenVal x)
      (.init (.scalar ⟨mirJoinDiamondThenVal x, 8⟩)))

theorem mirJoinAsymmetric_arms_agree (x flag : Nat) :
    MirArmsAgree mirJoinAsymmetricDiffers
      (mirJoinAsymmetricArmState x flag (mirJoinDiamondElseVal x) .dead)
      (mirJoinAsymmetricArmState x flag (mirJoinDiamondThenVal x)
        (.init (.scalar ⟨mirJoinDiamondThenVal x, 8⟩))) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, trivial, rfl⟩⟩

/-- **Non-Vacuity Witness for Asymmetric Dead/Scratch Slots at Join
    (`mirJoinAsymmetricScratch_evalJoinDiamondWP`)**: even though `_3` is `.dead` on `bb2` and
    `.init (.scalar ⟨x + 10, 8⟩)` on `bb1` at `bb3` entry, `wpMirJoinDiamond_merge_sound` merges
    both arms and evaluates `bb3` **once** by `rfl`. -/
theorem mirJoinAsymmetricScratch_evalJoinDiamondWP (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then
        wrapScalarBits (Nat.add x 20) (scalarModulus 8)
      else
        wrapScalarBits (Nat.add x 10) (scalarModulus 8)
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    evalJoinDiamondWP 5 3 mirJoinAsymmetricScratchBody 3
      (initMachineState mirJoinAsymmetricScratchBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirJoinAsymmetricMergedState x flag)
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) := by
  intro armVal expectedRet
  refine wpMirJoinDiamond_merge_sound ?_ (mirJoinAsymmetric_arms_agree x flag) ?_
  · show wpMirUntilJoinSym 5 mirJoinAsymmetricScratchBody 3 _
      (fun s' => s' = mirJoinAsymmetricArmResult x flag) _
    (repeat' ((conv => whnf); split)); all_goals
      (rename_i hCond; change Nat.beq flag 0 = _ at hCond;
       dsimp only [mirJoinAsymmetricArmResult]; rw [hCond]; rfl)
  · rfl

theorem mirJoinAsymmetricScratch_wpMirSym_witness (x flag : Nat) :
    let armVal :=
      if Nat.beq flag 0 then
        wrapScalarBits (Nat.add x 20) (scalarModulus 8)
      else
        wrapScalarBits (Nat.add x 10) (scalarModulus 8)
    let expectedRet := wrapScalarBits (Nat.add armVal x) (scalarModulus 8)
    wpMirSym 8 mirJoinAsymmetricScratchBody
      (initMachineState mirJoinAsymmetricScratchBody [.scalar ⟨x, 8⟩, .scalar ⟨flag, 8⟩])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) :=
  wpMirSym_of_evalJoinDiamondWP (mirJoinAsymmetricScratch_evalJoinDiamondWP x flag)

/-- **Negative control on asymmetric scratch slot `_3` (`mirJoinAsymmetricScratch_unhinted_slot3_rejected`)**:
    if the hint `[true, false, false, false]` omits `differs[3] = true`, `MirArmsAgree` is refuted
    because `.dead ≠ .init (.scalar ...)`. -/
theorem mirJoinAsymmetricScratch_unhinted_slot3_rejected :
    ¬ MirArmsAgree [true, false, false, false]
      (mirJoinAsymmetricArmState 0 0 (mirJoinDiamondElseVal 0) .dead)
      (mirJoinAsymmetricArmState 0 0 (mirJoinDiamondThenVal 0)
        (.init (.scalar ⟨mirJoinDiamondThenVal 0, 8⟩))) := by
  intro h
  exact LocalSlot.noConfusion h.locals.2.2.2.1

/-- **Negative control on reading an asymmetric dead scratch slot in the join block
    (`mirJoinAsymmetricScratch_read_dead_slot3_rejected`)**: if a join block tries to read `_3`
    (`_0 := _0 + _3; return`) on `mirJoinAsymmetricMergedState 0 0` (where `_3 = .dead` because
    `flag = 0` took `bb2`), `wpMirSym` on the merged state is **refuted** (reading `.dead` faults
    with `.ub`). -/
def mirJoinReadScratchInJoinBody : CapturedMir :=
  { mirJoinAsymmetricScratchBody with
    defPath := "sym_eval::mir_join_read_scratch_in_join_neg"
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 2, projection := [] })
                { branches := [(0, 2)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .storageLive 3, span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 3, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 0, projection := [] }
                  (.use (.copy { local_ := 3, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 20))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 3, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ] }

theorem mirJoinAsymmetricScratch_read_dead_slot3_rejected :
    ¬ wpMirSym 3 mirJoinReadScratchInJoinBody
      (mirJoinAsymmetricMergedState 0 0)
      (fun _ => True) := by
  intro h
  exact h

/-- **Sequential Two-Diamond `CapturedMir` Witness (`mirSeqTwoDiamondBody`)**:
    Chains two `SwitchInt` diamonds (`bb0 -> {bb1, bb2} -> bb3 (join 1) -> {bb4, bb5} -> bb6 (join 2)`)
    by composing two `wpMirJoinDiamond_merge_sound` cuts back-to-back, evaluating `bb3` **once** on
    the first merged state and `bb6` **once** on the second merged state ($O(k)$ block evaluations
    instead of $2^k$ path unfoldings):
    - `_0`: `u64` return slot, `_1`: `x`, `_2`: `flag1`, `_3`: `flag2`, `_4`: scratch slot in `bb1`.
    - `bb0`: `SwitchInt(_2)` (`0 -> bb2`, `otherwise -> bb1`),
      - `bb1`: `StorageLive(_4); _4 := _1 + 1; _0 := _4; StorageDead(_4); goto bb3`,
      - `bb2`: `_0 := _1 + 2; goto bb3`,
    - `bb3` (Join 1): `SwitchInt(_3)` (`0 -> bb5`, `otherwise -> bb4`),
      - `bb4`: `_0 := _0 + 10; goto bb6`,
      - `bb5`: `_0 := _0 + 20; goto bb6`,
    - `bb6` (Join 2): `_0 := _0 + _1; return`. -/
def mirSeqTwoDiamondBody : CapturedMir :=
  { defPath := "sym_eval::mir_seq_two_diamond_witness"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 3
    localDecls :=
      [ { mutability := .mut, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .not, ty := u64JoinMirTy, debugName := none }
      , { mutability := .mut, ty := u64JoinMirTy, debugName := none } ]
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 2, projection := [] })
                { branches := [(0, 2)], otherwise := 1 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .storageLive 4, span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 4, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 1))
                span := "SymbolicEval.lean" }
            , { kind := .assign { local_ := 0, projection := [] }
                  (.use (.copy { local_ := 4, projection := [] }))
                span := "SymbolicEval.lean" }
            , { kind := .storageDead 4, span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 1, projection := [] })
                    (u64JoinConstOp 2))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 3, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements := []
          terminator :=
            { kind := .switchInt (.copy { local_ := 3, projection := [] })
                { branches := [(0, 5)], otherwise := 4 }
              span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (u64JoinConstOp 10))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 6, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (u64JoinConstOp 20))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .goto 6, span := "SymbolicEval.lean" }
          isCleanup := false }
      , { statements :=
            [ { kind := .assign { local_ := 0, projection := [] }
                  (.binaryOp .add
                    (.copy { local_ := 0, projection := [] })
                    (.copy { local_ := 1, projection := [] }))
                span := "SymbolicEval.lean" } ]
          terminator := { kind := .return_, span := "SymbolicEval.lean" }
          isCleanup := false } ]
    fnAbi := defaultU64JoinFnAbi
    layouts := emptyLayoutTable
    allocations := [] }

def mirSeqTwoDiamondDiffers : List Bool := [true, false, false, false, false]

def mirSeqTwoDiamondStateAt (bb : BasicBlockIdx) (x flag1 flag2 val0 : Nat) : MachineState :=
  let sInit :=
    initMachineState mirSeqTwoDiamondBody
      [.scalar ⟨x, 8⟩, .scalar ⟨flag1, 8⟩, .scalar ⟨flag2, 8⟩]
  { sInit with
    frame :=
      { blockIdx := bb
        stmtIdx := 0
        locals :=
          [ .init (.scalar ⟨val0, 8⟩)
          , .init (.scalar ⟨x, 8⟩)
          , .init (.scalar ⟨flag1, 8⟩)
          , .init (.scalar ⟨flag2, 8⟩)
          , .dead ] } }

def mirSeqDiamond1Val (x flag1 : Nat) : Nat :=
  if Nat.beq flag1 0 then
    wrapScalarBits (Nat.add x 2) (scalarModulus 8)
  else
    wrapScalarBits (Nat.add x 1) (scalarModulus 8)

def mirSeqDiamond2Val (x flag1 flag2 : Nat) : Nat :=
  let v1 := mirSeqDiamond1Val x flag1
  if Nat.beq flag2 0 then
    wrapScalarBits (Nat.add v1 20) (scalarModulus 8)
  else
    wrapScalarBits (Nat.add v1 10) (scalarModulus 8)

def mirSeqDiamond1ArmResult (x flag1 flag2 : Nat) : MachineState :=
  if Nat.beq flag1 0 then
    mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 2) (scalarModulus 8))
  else
    mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 1) (scalarModulus 8))

def mirSeqDiamond2ArmResult (x flag1 flag2 : Nat) : MachineState :=
  let v1 := mirSeqDiamond1Val x flag1
  if Nat.beq flag2 0 then
    mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 20) (scalarModulus 8))
  else
    mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 10) (scalarModulus 8))

def mirSeqDiamond1MergedState (x flag1 flag2 : Nat) : MachineState :=
  mergeMirJoinState (Nat.beq flag1 0) mirSeqTwoDiamondDiffers
    (mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 2) (scalarModulus 8)))
    (mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 1) (scalarModulus 8)))

def mirSeqDiamond2MergedState (x flag1 flag2 : Nat) : MachineState :=
  let v1 := mirSeqDiamond1Val x flag1
  mergeMirJoinState (Nat.beq flag2 0) mirSeqTwoDiamondDiffers
    (mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 20) (scalarModulus 8)))
    (mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 10) (scalarModulus 8)))

theorem mirSeqDiamond1_arms_agree (x flag1 flag2 : Nat) :
    MirArmsAgree mirSeqTwoDiamondDiffers
      (mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 2) (scalarModulus 8)))
      (mirSeqTwoDiamondStateAt 3 x flag1 flag2 (wrapScalarBits (Nat.add x 1) (scalarModulus 8))) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem mirSeqDiamond2_arms_agree (x flag1 flag2 : Nat) :
    let v1 := mirSeqDiamond1Val x flag1
    MirArmsAgree mirSeqTwoDiamondDiffers
      (mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 20) (scalarModulus 8)))
      (mirSeqTwoDiamondStateAt 6 x flag1 flag2 (wrapScalarBits (Nat.add v1 10) (scalarModulus 8))) :=
  ⟨rfl, rfl, rfl, ⟨trivial, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **Sequential Two-Diamond Compositional Join-Cut Witness (`mirSeqTwoDiamond_wpMirSym_witness`)**:
    Chains two `wpMirJoinDiamond_merge_sound` cuts across `bb3` and `bb6`, proving `wpMirSym` for
    all `x, flag1, flag2 : Nat` without exponential path splitting (`Classical.choice`-free). -/
theorem mirSeqTwoDiamond_wpMirSym_witness (x flag1 flag2 : Nat) :
    let expectedRet := wrapScalarBits (Nat.add (mirSeqDiamond2Val x flag1 flag2) x) (scalarModulus 8)
    wpMirSym 12 mirSeqTwoDiamondBody
      (initMachineState mirSeqTwoDiamondBody
        [.scalar ⟨x, 8⟩, .scalar ⟨flag1, 8⟩, .scalar ⟨flag2, 8⟩])
      (mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩)) := by
  intro expectedRet
  refine wpMirSym_of_evalJoinDiamondWP (prefixFuel := 6) (suffixFuel := 6) (joinBb := 3)
    (sJoin := mirSeqDiamond1MergedState x flag1 flag2) ?_
  refine wpMirJoinDiamond_merge_sound ?_ (mirSeqDiamond1_arms_agree x flag1 flag2) ?_
  · -- Diamond 1 (`bb0 -> {bb1, bb2} -> bb3`):
    show wpMirUntilJoinSym 6 mirSeqTwoDiamondBody 3 _
      (fun s' => s' = mirSeqDiamond1ArmResult x flag1 flag2) _
    (repeat' ((conv => whnf); split)); all_goals
      (rename_i hCond; change Nat.beq flag1 0 = _ at hCond;
       dsimp only [mirSeqDiamond1ArmResult]; rw [hCond]; rfl)
  · -- From `mirSeqDiamond1MergedState x flag1 flag2` at `bb3`, cut again at `bb6`:
    refine wpMirSym_of_evalJoinDiamondWP (prefixFuel := 3) (suffixFuel := 3) (joinBb := 6)
      (sJoin := mirSeqDiamond2MergedState x flag1 flag2) ?_
    refine wpMirJoinDiamond_merge_sound ?_ (mirSeqDiamond2_arms_agree x flag1 flag2) ?_
    · -- Diamond 2 (`bb3 -> {bb4, bb5} -> bb6`) evaluated ONCE from `mirSeqDiamond1MergedState`:
      show wpMirUntilJoinSym 3 mirSeqTwoDiamondBody 6 _
        (fun s' => s' = mirSeqDiamond2ArmResult x flag1 flag2) _
      ((conv => whnf); split); all_goals
        (rename_i hCond; change Nat.beq flag2 0 = _ at hCond;
         dsimp only [mirSeqDiamond2ArmResult]; rw [hCond]; rfl)
    · -- Join 2 (`bb6 -> return`) evaluated ONCE on `mirSeqDiamond2MergedState`:
      rfl

/-- `DWLP mirDefaultWP` witness for `mirSeqTwoDiamondBody`. -/
theorem mirSeqTwoDiamond_verified_witness (x flag1 flag2 : Nat) :
    let expectedRet := wrapScalarBits (Nat.add (mirSeqDiamond2Val x flag1 flag2) x) (scalarModulus 8)
    DWLP mirDefaultWP
      (mirCallTree mirSeqTwoDiamondBody
        [.scalar ⟨x, 8⟩, .scalar ⟨flag1, 8⟩, .scalar ⟨flag2, 8⟩])
      (fun out _ =>
        mirNormalPost (fun retVal _ => retVal = .scalar ⟨expectedRet, 8⟩) out)
      PUnit.unit :=
  (dwp_of_wpMirSym (mirSeqTwoDiamond_wpMirSym_witness x flag1 flag2)).toDWLP

end MirJoinDiamondWitness

/-!
## Axiom Policy

Every GVN, canonical-state, join-cut, aliasing, witness, operator-bridge and fuel-level
`MirSemantics` join-cut theorem in this file depends on at most `{propext, Quot.sound}`: no
`sorryAx`, no `Lean.ofReduceBool` (closed witnesses use `decide +kernel`), and no
`Classical.choice` (the fuel-monotonicity, subtraction, low-mask, and bitwise-complement lemmas
avoid `omega` and `Nat.testBit_two_pow_sub_succ`, which can introduce it). The only exceptions are
the corollaries whose *statements* mention `Anneal.ITreeWP.DWLP`/`DWP`
(`dwlp_of_wpMirUntilJoinSym`, `dwpMirJoinDiamond_sound`, `wpMirJoinDiamond_sound`,
`wpMirJoinDiamond_dwlp_sound`, `wpMirJoinDiamond_merge_dwlp_sound`,
`mirJoinDiamond_verified_witness`, `mirSeqTwoDiamond_verified_witness`): `DWLP`/`DWP` are built
with `coinductive_fixpoint`/`inductive_fixpoint` and themselves depend on `Classical.choice`, so no
proof of such a statement can avoid it, while their fuel-level premises (`wpMirSym_of_evalJoinDiamondWP`,
`wpMirJoinDiamond_merge_sound`, `mirJoinDiamond_wpMirSym_witness`,
`mirJoinAsymmetricScratch_wpMirSym_witness`, `mirSeqTwoDiamond_wpMirSym_witness`) stay
`Classical.choice`-free.
`trusted/audit/TrustedBoundary.lean` admits no `#guard_msgs`/`#print` commands in audited modules,
so this inventory is checked out-of-file by `#print axioms` over the declarations above.
-/

end Anneal.Rustc.V2026_06_01.SymbolicEval
