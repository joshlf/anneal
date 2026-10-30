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
  rw [MirContractHolds, mirContractHoldsWithSafety_iff_dwlp]
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

/-- Exact `DWLP mirDefaultWP` characterization of `MirBoolPredicateHolds`. -/
theorem mirBoolPredicateHolds_iff_dwlp
    (specBody : CapturedMir) (args : List Value) :
    MirBoolPredicateHolds specBody args ↔
      DWLP mirDefaultWP (mirCallTree specBody args)
        (fun out _ =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 })
        PUnit.unit := by
  rw [MirBoolPredicateHolds, mirContractHolds_iff_dwlp]
  exact ⟨fun h => h args rfl, fun h _ h_eq => h_eq ▸ h⟩

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
  rw [MirStatefulContractHolds, mirStatefulContractHoldsWithSafety_iff_dwlp]
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

/-- Decision-tree symbolic `evalRvalue`. -/
def evalRvalueSymTree
    (locals : List LocalSlot)
    (rv : Rvalue)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) : SymTree RvalueEvalResult :=
  match rv with
  | .binaryOp op lhsOp rhsOp =>
    match evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals with
    | .ok lhsVal locals₁ =>
      match evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          let isSigned := operandIsSigned localDecls lhsOp layouts
          evalScalarBinOpSymTree op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            .leaf (.ok
              (.ptr
                { ptrVal with
                  offsetBytes := Nat.add ptrVal.offsetBytes offsetSc.bits }
                sz)
              locals₂
              mem)
          | _ => .leaf .unsupported
        | _, _ => .leaf .unsupported
      | .ub => .leaf .ub
      | .unsupported => .leaf .unsupported
    | .ub => .leaf .ub
    | .unsupported => .leaf .unsupported
  | .unaryOp .not op =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
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
    cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok lhsVal locals₁ =>
      dsimp only
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals with
      | ub => rfl
      | unsupported => rfl
      | ok rhsVal locals₂ =>
        dsimp only
        cases lhsVal with
        | scalar lhs =>
          cases rhsVal with
          | scalar rhs =>
            dsimp only
            exact evalScalarBinOpSymTree_eval op lhs rhs locals₂ mem _
          | _ => rfl
        | ptr ptrVal sz =>
          cases rhsVal with
          | scalar _ =>
            dsimp only
            cases op <;> rfl
          | _ => rfl
        | _ => rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalueSymTree, evalRvalue]
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
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
    (dst : Place) :
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
              invalidateConflictingBorrows mem₁.borrows dst.local_ .none
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
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrows mem₁.borrows dst.local_ .none
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | .deref :: restProj =>
      match
        evalPlaceWrite locals₁ mem₁.borrows dst val mem₁.activeProtectors
      with
      | .ok locals₂ =>
        let borrows' :=
          invalidateDerefWriteBorrows locals₁ mem₁.borrows dst restProj
        MirStepNode.step
          (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .ub =>
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
            let borrows' :=
              invalidateDerefWriteBorrows locals₁ mem₁.borrows dst restProj
            MirStepNode.step
              (advanceStmt
                s
                locals₁
                { mem₁ with
                  borrows := borrows'
                  callerLocals := callerLocals' })
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
      | .unsupported => MirStepNode.unsupported
    | proj :: rest =>
      match get? locals₁ dst.local_ with
      | .some (.init rootVal) =>
        match writeProjectedValue locals₁ rootVal (proj :: rest) val with
        | .ok rootVal' =>
          match set? locals₁ dst.local_ (.init rootVal') with
          | .some locals₂ =>
            match mem₁.activeProtectors with
            | .nil =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  mem₁.borrows
                  dst.local_
                  .none
                  (proj :: rest)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
            | protHead :: protTail =>
              match
                hasProtectedWriteConflict
                  mem₁.borrows
                  (protHead :: protTail)
                  dst.local_
                  .none
                  (proj :: rest)
              with
              | true => MirStepNode.fail .ub
              | false =>
                let borrows' :=
                  invalidateConflictingBorrowsAtProj
                    mem₁.borrows
                    dst.local_
                    .none
                    (proj :: rest)
                MirStepNode.step
                  (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | .none => MirStepNode.fail .ub
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
      | .some .uninit => MirStepNode.fail .ub
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
      (fun res => .leaf (finishAssignStmtNode s dst res))
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
    cases evalOperand s.frame.locals discr s.memory.borrows s.memory.globals currentBody.layouts s.memory.callerLocals with
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
    cases evalOperand s.frame.locals cond s.memory.borrows s.memory.globals currentBody.layouts s.memory.callerLocals with
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

/-- Computable bounded boolean checker for `MirBoolPredicateHolds specBody args`. -/
def checkMirBoolBounded
    (fuel : Nat) (specBody : CapturedMir) (args : List Value) : Bool :=
  checkMirBoolExecBounded fuel specBody (.running (initMachineState specBody args))

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
Discharge `MirBoolPredicateHolds specBody args` on concrete inputs by kernel
`rfl` (`checkMirBoolBounded fuel specBody args = true`).
-/
theorem mirBoolPredicateHolds_of_checkBounded
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h : checkMirBoolBounded fuel specBody args = true := by rfl) :
    MirBoolPredicateHolds specBody args :=
  mirBoolPredicateHolds_of_bounded fuel specBody args
    (wpCoalBounded_of_checkMirBoolExecBounded fuel specBody _ h)

/-- Compatibility alias used by Tutor proof modules (`rfl`-discharged). -/
abbrev mirBoolPredicateHolds_of_wp_bounded :=
  @mirBoolPredicateHolds_of_checkBounded

/--
Single-pass symbolic sufficiency proposition for `MirBoolPredicateHolds`:
`specBody` executes within `fuel` steps without UB and returns `true`
(`.scalar ⟨1, 1⟩`) on every normal return path.
-/
def wpMirBoolSym
    (fuel : Nat) (specBody : CapturedMir) (args : List Value) : Prop :=
  wpMirSym fuel specBody (initMachineState specBody args)
    (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))

/--
Single-pass symbolic necessity / inversion proposition for `MirBoolPredicateHolds`:
at any finite `fuel`, `MirBoolPredicateHolds specBody args` unfolds into a pure
`Prop` formula over `args`.
-/
def holdBoolMirSym
    (fuel : Nat) (specBody : CapturedMir) (args : List Value) : Prop :=
  wpMirOrExhaustedSym fuel specBody (initMachineState specBody args)
    (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))

/-- Prove `MirBoolPredicateHolds specBody args` from symbolic `wpMirBoolSym`. -/
theorem mirBoolPredicateHolds_of_wpMirSym
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h : wpMirBoolSym fuel specBody args) :
    MirBoolPredicateHolds specBody args := by
  have h' :
      wpMirSym fuel specBody (initMachineState specBody args)
        (fun out =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 }) :=
    wpMirSym_mono (fun out ho => (mirSafePost_iff_forall_normal _ out).1 ho) h
  rw [wpMirSym_eq_wpMirBounded] at h'
  exact mirBoolPredicateHolds_of_bounded fuel specBody args h'

/--
Invert a `MirBoolPredicateHolds specBody args` hypothesis (such as a `#[spec]`
`requires` clause) into a single-pass symbolic `holdBoolMirSym` formula.
-/
theorem holdBoolMirSym_of_mirBoolPredicateHolds
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h : MirBoolPredicateHolds specBody args) :
    holdBoolMirSym fuel specBody args := by
  have h_dwlp := (mirBoolPredicateHolds_iff_dwlp specBody args).1 h
  have h_safe :
      DWLP mirDefaultWP (mirCallTree specBody args)
        (fun out _ =>
          mirSafePost
            (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }) out)
        PUnit.unit :=
    DWLP.mono
      (fun out _ ho => (mirSafePost_iff_forall_normal _ out).2 ho)
      h_dwlp
  exact wpMirOrExhaustedSym_of_dwlp fuel specBody
    (initMachineState specBody args) _ h_safe

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
  ⟨fun h =>
    wpMirSym_of_wpMirOrExhaustedSym h_term
      (holdBoolMirSym_of_mirBoolPredicateHolds fuel specBody args h),
   mirBoolPredicateHolds_of_wpMirSym fuel specBody args⟩

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
        wpMirSym fuel c.body (initMachineState c.body args)
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
        wpMirSym fuel c.body (initMachineState c.body args)
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
      wpMirSym fuel c.body (initMachineState c.body expectedArgs)
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
        wpMirSym fuel c.body (initMachineStateWithMemory c.body args mem)
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
        wpMirSym fuel c.body (initMachineStateWithMemory c.body args mem)
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
        wpMirSym fuel c.body (initMachineStateWithMemory c.body args mem)
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
        (initMachineStateWithMemory c.body expectedArgs expectedMem)
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
          (initMachineState c.body [.scalar { bits := b, sizeBytes := width }])
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
          (initMachineState c.body [.scalar { bits := b, sizeBytes := width }])
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
          (initMachineState c.body
            [ .scalar { bits := b1, sizeBytes := w1 }
            , .scalar { bits := b2, sizeBytes := w2 } ])
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
Computable check that `body` evaluates on `args` within `fuel` steps to a normal
return value `retVal` for which `checkMirBoolBounded specFuel ensBody (args ++ [retVal])`
holds.
-/
def checkMirRustPinnedSpec
    (subjectFuel specFuel : Nat)
    (subjectBody ensBody : CapturedMir)
    (args : List Value) : Bool :=
  let rec loop (fuel : Nat) (st : MirExecState) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match stepMirState subjectBody st with
      | .ret (.normal (retVal, _)) =>
        checkMirBoolBounded specFuel ensBody (args ++ [retVal])
      | .ret .panic => false
      | .ret .abort => false
      | .tau st' => loop fuel' st'
      | .vis (.inl _) _ => false
      | .vis (.inr (.inl _)) k => loop fuel' (k PUnit.unit)
      | .vis (.inr (.inr _)) _ => false
  loop subjectFuel (.running (initMachineState subjectBody args))

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
          MirBoolPredicateHolds ensBody (args ++ [retVal])) := by
  unfold checkMirRustPinnedSpec at h_ok
  unfold wpMirBounded
  suffices ∀ (fuel : Nat) (st : MirExecState),
      checkMirRustPinnedSpec.loop specFuel subjectBody ensBody args fuel st = true →
      wpCoalBounded fuel mirDefaultWP (stepMirState subjectBody)
        (fun out _ =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            MirBoolPredicateHolds ensBody (args ++ [retVal]))
        st PUnit.unit from
    this subjectFuel _ h_ok
  intro fuel
  induction fuel with
  | zero => intro _ h; nomatch h
  | succ fuel' ih =>
    intro st h
    unfold checkMirRustPinnedSpec.loop at h
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
        exact mirBoolPredicateHolds_of_checkBounded specFuel ensBody
          (args ++ [rv]) h
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
    ¬ MirContractHoldsWithSafety body safetyPre pre post := by
  intro h_holds
  rcases h_holds args h_safe_pre with ⟨h_tree_safe, _⟩
  exact reachesFaultBounded_not_treeSafe fuel body
    (initMachineState body args) h_ub h_tree_safe

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
      reachesFaultBounded fuel c.body (initMachineState c.body args) = true := by
      rfl) :
    ¬ c.holds :=
  refuteMirContractWithSafetyByBoundedUB fuel args h_pre h_ub

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
        (initMachineStateWithMemory c.body args mem) = true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  rcases h_holds args mem h_pre with ⟨h_tree_safe, _⟩
  exact reachesFaultBounded_not_treeSafe fuel c.body
    (initMachineStateWithMemory c.body args mem) h_ub h_tree_safe

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
        (initMachineStateWithMemory c.body args mem) = true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  have h_tree_safe := (h_holds args mem h_pre).1
  exact reachesFaultBounded_not_treeSafe fuel c.body
    (initMachineStateWithMemory c.body args mem) h_ub h_tree_safe

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
          (initMachineStateWithMemory c.implBody args mem)
          (fun out =>
            out = .normal (model args mem) ∧
            c.post args mem (model args mem).1 (model args mem).2))
    (h_spec :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirNoCallSym specFuel c.specBody
          (initMachineStateWithMemory c.specBody args mem)
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
          (initMachineStateWithMemory c.body args mem)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') →
              c.post args mem retVal mem'))
    (h_waived :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        wpMirUbWaivedSym fuel c.body
          (initMachineStateWithMemory c.body args mem)
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
        post := post } := by
  refine verifyModularContractMirBounded contract body pre post fuel
    (fun args mem h_pre => ?_)
  rw [wpMirModularBounded, ← wpMirExecModularSym_eq_wpCoalBounded]
  exact h_wp args mem h_pre

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

/-- Project a `MirDiffVerdict` to its decidable `MirDiffTag`. -/
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
  (evalMirDiffBounded fuel body s).toTag

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
      reachesStrictUBBounded fuel c.body (initMachineState c.body args) = true := by
      rfl) :
    ¬ c.holds :=
  refuteClaimByBoundedUB c fuel args h_pre
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded
      fuel c.body (.running (initMachineState c.body args)) h_ub)

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
        (initMachineStateWithMemory c.body args mem) = true := by
      rfl) :
    ¬ c.holds :=
  refuteStatefulClaimByBoundedUB c fuel args mem h_pre
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded
      fuel c.body (.running (initMachineStateWithMemory c.body args mem)) h_ub)

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
        (initMachineStateWithMemory c.body args mem) = true := by
      rfl) :
    ¬ c.holds :=
  refuteTotalClaimByBoundedUB c fuel args mem h_pre
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded
      fuel c.body (.running (initMachineStateWithMemory c.body args mem)) h_ub)

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
        (initMachineStateWithMemory c.body args mem) = true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  rcases reachesPanicBounded_reachesRet fuel c.body
    (initMachineStateWithMemory c.body args mem) h_panic with ⟨tr, h_ret⟩
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
    fuel body (.running (initMachineStateWithMemory body a m)) h_ok

/--
Certify a Miri `pass` test returning `.scalar ⟨bits, sizeBytes⟩` at `(args, mem)`:
proves `TotalVerificationResult` via
`evalMirDiffTagBounded ... = .normalScalar bits sizeBytes`.
-/
theorem verifyTotalMirScalarPointBounded
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
          retVal = .scalar { bits := bits, sizeBytes := sizeBytes } } := by
  refine verifyTotalMirBounded _ fuel ?_
  rintro a m ⟨rfl, rfl⟩
  exact wpCoalBounded_of_evalMirDiffExecBounded_normalScalar
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

end Anneal.Rustc.V2026_06_01.SymbolicEval

