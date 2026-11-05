import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.Pass
import Anneal.EffectWP
import Anneal.ITreeWP
import Anneal.Memory
import Anneal.UnsafeObligations
import Anneal.SepLogic

namespace Anneal.Rustc.V2026_06_01.Lower

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.Pass
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic

/-!
Version-scoped MIR verification bridge connecting `Trusted.Rustc.V2026_06_01`
(`CapturedMir`, `mirTree`, `mirStatefulTree`, `mirHandledTree`, and the five
trusted certificate gates in `Trusted.VerificationResult`) to the
toolchain-independent open effect predicate-transformer logics (`StateEffectWP`,
`DWLP`, `DWP`, `wpCoalBounded`, and horizontal `ITree.interp` handler linking)
(`#100`, `#102`, `#103`).

1. **Open Effect Predicate Transformers for MIR**:
   `mirClosedWP`, `mirNoCallWP`, `mirDefaultWP`, `mirTraceWP`, `mirModularWP C`,
   and fuel-bounded coalgebra evaluators `wpMirBounded`, `wpMirNoCallBounded`,
   `wpMirTraceBounded`, and `wpMirModularBounded`.
2. **Adequacy Bridges for All Five Trusted Certificates**:
   `verifyByDWLP`, `verifyMirBounded`, `mirBoolPredicateHolds_of_dwp`,
   `mirBoolPredicateHolds_of_bounded`, `verifyStatefulByDWLP`,
   `verifyStatefulMirBounded`, `verifyTraceByDWLP`, `verifyTraceMirBounded`,
   `verifyTotalByDWP`, `verifyTotalMirBounded`, `verifyModularByDWLP`, and
   `verifyModularMirBounded`.
3. **Horizontal Caller–Callee Linking via `ITree.interp`**:
   `linkCalleeHandler`, `envSatisfiesContract_linkCalleeHandler`, and
   `linkVerifiedMirCallee`.
-/

/-! ## 1. Compositional Open Effect Predicate Transformers for MIR -/

/--
Call-forbidding transformer for `CallE Req Resp`: rejects every unresolved
external call (`wp _ _ _ := False`), certifying that a closed callee body does
not invoke unlinked external functions.
-/
def forbidCallWP
    (S : Type u) (Req : Type u) (Resp : Req → Type u) :
    StateEffectWP S (CallE Req Resp) where
  wp _ _ _ := False
  mono _ h := False.elim h

instance (S Req : Type u) (Resp : Req → Type u) :
    StateEffectWP.Conjunctive (forbidCallWP S Req Resp) where
  conj h _ := False.elim h

instance (S Req : Type u) (Resp : Req → Type u) :
    StateEffectWP.ExcludedMiracle (forbidCallWP S Req Resp) where
  no_miracle h := h

instance (Req : Type u) (Resp : Req → Type u) :
    PureSoundWP (forbidCallWP PUnit.{u + 1} Req Resp) where
  sound h := False.elim h

/-- Silent effect transformer for `ObsE Obs`: rejects observable event emissions. -/
def forbidObsWP (S : Type u) (Obs : Type u) : StateEffectWP S (ObsE Obs) where
  wp _ _ _ := False
  mono _ h := False.elim h

instance (S Obs : Type u) : StateEffectWP.Conjunctive (forbidObsWP S Obs) where
  conj h _ := False.elim h

instance (S Obs : Type u) : StateEffectWP.ExcludedMiracle (forbidObsWP S Obs) where
  no_miracle h := h

instance (Obs : Type u) : PureSoundWP (forbidObsWP PUnit.{u + 1} Obs) where
  sound h := False.elim h

/--
Silent (pure/memory-only) predicate transformer for `MirEffect`: forbids faults,
observable I/O events, and unlinked external calls (`wp _ _ _ := False` on all
three branches). Any `ITree MirEffect MirOutcome` satisfying `DWP mirSilentWP`
deterministically terminates in a unique `.ret out` after finitely many `.tau`
steps with trace `[]`.
-/
abbrev mirSilentWP : EffectWP MirEffect :=
  (failWP PUnit FailureKind).sum
    ((forbidObsWP PUnit MirObs).sum
      (forbidCallWP PUnit MirCallReq (fun _ => MirCallAns)))

/-- Predicate transformer for `MirClosedEffect` (`SumE MirFailE MirObsE`). -/
abbrev mirClosedWP : EffectWP MirClosedEffect :=
  (failWP PUnit FailureKind).sum (obsIgnoreWP PUnit MirObs)

/-- Predicate transformer for closed (call-free) `MirEffect` bodies. -/
abbrev mirNoCallWP : EffectWP MirEffect :=
  (failWP PUnit FailureKind).sum
    ((obsIgnoreWP PUnit MirObs).sum
      (forbidCallWP PUnit MirCallReq (fun _ => MirCallAns)))

/--
Default impure-call predicate transformer for `MirEffect`: faults evaluate to
`False`, `MirObs` emissions step cleanly, and unresolved `MirCallE` requests
quantify demonically over all `MirCallAns` responses and post-call memories.
-/
abbrev mirDefaultWP : EffectWP MirEffect :=
  (failWP PUnit FailureKind).sum
    ((obsIgnoreWP PUnit MirObs).sum
      (unconstrainedCallWP PUnit MirCallReq (fun _ => MirCallAns)))

/-- Trace-recording predicate transformer for `MirEffect`. -/
abbrev mirTraceWP : StateEffectWP (List (Event MirEffect)) MirEffect :=
  eventTraceWP MirEffect

/-- Contract-guided modular predicate transformer for `MirEffect`. -/
abbrev mirModularWP
    (C : CallContract MirCallReq (fun _ => MirCallAns)) :
    EffectWP MirEffect :=
  (failWP PUnit FailureKind).sum
    ((obsIgnoreWP PUnit MirObs).sum (contractCallWP PUnit C))

/-- Proposition holding iff a `FailReq FailureKind` is a waived `.ub` fault. -/
def isWaivedUbFailReq : FailReq FailureKind → Prop
  | .fail .ub => True
  | .fail .unsupported => False
  | .fail .outOfFuel => False

/--
Fault transformer for `MirFailE` that waives `.fail .ub` (`wp _ _ _ := True`)
while still rejecting `.fail .unsupported` (`wp _ _ _ := False`).
Used by `UbExceptionVerificationResult` to verify that every non-faulting
normal return path of a UB-exempted item satisfies its postcondition across all
`pre` inputs, even on inputs where another execution path triggers `.fail .ub`.
-/
def waiveUbFailWP (S : Type) : StateEffectWP S MirFailE where
  wp i _ _ := isWaivedUbFailReq i
  mono _ h := h

instance (S : Type) : StateEffectWP.Conjunctive (waiveUbFailWP S) where
  conj h₁ _ := h₁

/--
UB-waiving predicate transformer for `MirEffect`: `.fail .ub` evaluates to
`True`, `.fail .unsupported` evaluates to `False`, `MirObs` emissions step
cleanly, and unresolved `MirCallE` requests quantify demonically over all
`MirCallAns` responses.
-/
abbrev mirUbWaivedWP : EffectWP MirEffect :=
  (waiveUbFailWP PUnit).sum
    ((obsIgnoreWP PUnit MirObs).sum
      (unconstrainedCallWP PUnit MirCallReq (fun _ => MirCallAns)))

/-- Convert a `MirCallContract` (`Trusted.VerificationResult`) into an `EffectWP.CallContract`. -/
def _root_.Trusted.VerificationResult.MirCallContract.toCallContract
    (C : MirCallContract) : CallContract MirCallReq (fun _ => MirCallAns) where
  pre := C.pre
  post := C.post

/-- Fuel-bounded coalgebra stepping on `stepMirState body` under `mirDefaultWP`. -/
def wpMirBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpCoalBounded fuel mirDefaultWP (stepMirState body)
    (fun out _ => post out) (.running s) PUnit.unit

/-- Fuel-bounded coalgebra stepping on `stepMirState body` under `mirUbWaivedWP`. -/
def wpMirUbWaivedBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpCoalBounded fuel mirUbWaivedWP (stepMirState body)
    (fun out _ => post out) (.running s) PUnit.unit

/-- Fuel-bounded coalgebra stepping on `stepMirState body` under `mirNoCallWP`. -/
def wpMirNoCallBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpCoalBounded fuel mirNoCallWP (stepMirState body)
    (fun out _ => post out) (.running s) PUnit.unit

/-- Fuel-bounded coalgebra stepping on `stepMirState body` under `mirSilentWP`. -/
def wpMirSilentBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpCoalBounded fuel mirSilentWP (stepMirState body)
    (fun out _ => post out) (.running s) PUnit.unit

/-- Fuel-bounded coalgebra stepping on `stepMirState body` under `mirTraceWP`. -/
def wpMirTraceBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : List (Event MirEffect) → MirOutcome → Prop) : Prop :=
  wpCoalBounded fuel mirTraceWP (stepMirState body)
    (fun out tr => post tr out) (.running s) []

/-- Fuel-bounded coalgebra stepping on `stepMirState body` under `mirModularWP C`. -/
def wpMirModularBounded
    (fuel : Nat) (C : CallContract MirCallReq (fun _ => MirCallAns))
    (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpCoalBounded fuel (mirModularWP C) (stepMirState body)
    (fun out _ => post out) (.running s) PUnit.unit

/-! ## 2. Adequacy Bridges for All Five Trusted Certificates -/

/-- Prove a stateless `VerificationResult c` from `DWLP mirDefaultWP`. -/
theorem verifyByDWLP
    (c : Claim)
    (h_dwlp :
      ∀ args : List Value,
        c.pre args →
        DWLP mirDefaultWP (mirCallTreeWithCallees c.body args c.callees)
          (fun out _ =>
            ∀ retVal mem', out = .normal (retVal, mem') → c.post args retVal)
          PUnit.unit) :
    VerificationResult c := by
  refine ⟨fun args h_pre => ?_⟩
  have h_adeq := dwlp_pure_adequacy (h_dwlp args h_pre)
  exact ⟨h_adeq.1, fun outPair h_ret _ retVal mem' h_out =>
    h_adeq.2 outPair.1 outPair.2 h_ret retVal mem' h_out⟩

/-- Prove a stateless `VerificationResult c` from `wpMirBounded`. -/
theorem verifyMirBounded
    (c : Claim) (fuel : Nat)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        wpMirBounded fuel c.body
          (initMachineStateWithCallees c.body args c.callees)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') → c.post args retVal)) :
    VerificationResult c :=
  verifyByDWLP c (fun args h_pre => dwlp_cofix_of_wpCoalBounded (h_wp args h_pre))

/-- Prove `MirBoolPredicateHoldsWithCallees specBody callees args` from `DWP mirDefaultWP`. -/
theorem mirBoolPredicateHoldsWithCallees_of_dwp
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (h_dwp :
      DWP mirDefaultWP (mirCallTreeWithCallees specBody args callees)
        (fun out _ =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 })
        PUnit.unit) :
    MirBoolPredicateHoldsWithCallees specBody callees args :=
  (verifyByDWLP
    { body := specBody
      pre := (· = args)
      post := fun _ ret => ret = .scalar { bits := 1, sizeBytes := 1 }
      callees := callees }
    (fun _ h_eq => h_eq ▸ h_dwp.toDWLP)).proof

/-- Prove `MirBoolPredicateHolds specBody args` from `DWP mirDefaultWP`. -/
theorem mirBoolPredicateHolds_of_dwp
    (specBody : CapturedMir) (args : List Value)
    (h_dwp :
      DWP mirDefaultWP (mirCallTree specBody args)
        (fun out _ =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 })
        PUnit.unit) :
    MirBoolPredicateHolds specBody args :=
  mirBoolPredicateHoldsWithCallees_of_dwp specBody .nil args h_dwp

/-- Prove `MirBoolPredicateHoldsWithCallees specBody callees args` from `wpMirBounded`. -/
theorem mirBoolPredicateHoldsWithCallees_of_bounded
    (fuel : Nat)
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value)
    (h_wp :
      wpMirBounded fuel specBody
        (initMachineStateWithCallees specBody args callees)
        (fun out =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 })) :
    MirBoolPredicateHoldsWithCallees specBody callees args :=
  mirBoolPredicateHoldsWithCallees_of_dwp
    specBody callees args (dwp_cofix_of_wpCoalBounded fuel h_wp)

/-- Prove `MirBoolPredicateHolds specBody args` from `wpMirBounded`. -/
theorem mirBoolPredicateHolds_of_bounded
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h_wp :
      wpMirBounded fuel specBody (initMachineState specBody args)
        (fun out =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 })) :
    MirBoolPredicateHolds specBody args :=
  mirBoolPredicateHoldsWithCallees_of_bounded fuel specBody .nil args h_wp

/-- Prove a stateful `StatefulVerificationResult c` from `DWLP mirDefaultWP`. -/
theorem verifyStatefulByDWLP
    (c : StatefulClaim)
    (h_dwlp :
      ∀ args mem,
        c.pre args mem →
        DWLP mirDefaultWP (mirStatefulTreeWithCallees c.body args mem c.callees)
          (fun out _ =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → c.post args mem retVal mem')
          PUnit.unit) :
    StatefulVerificationResult c := by
  refine ⟨fun args mem h_pre => ?_⟩
  have h_adeq := dwlp_pure_adequacy (h_dwlp args mem h_pre)
  exact ⟨h_adeq.1, fun outPair h_ret _ retVal mem' h_out =>
    h_adeq.2 outPair.1 outPair.2 h_ret retVal mem' h_out⟩

/-- Prove a stateful `StatefulVerificationResult c` from `wpMirBounded`. -/
theorem verifyStatefulMirBounded
    (c : StatefulClaim) (fuel : Nat)
    (h_wp :
      ∀ args mem,
        c.pre args mem →
        wpMirBounded fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (fun out =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → c.post args mem retVal mem')) :
    StatefulVerificationResult c :=
  verifyStatefulByDWLP c
    (fun args mem h_pre => dwlp_cofix_of_wpCoalBounded (h_wp args mem h_pre))

/-- Prove a trace-aware `TraceVerificationResult c` from `DWLP mirTraceWP`. -/
theorem verifyTraceByDWLP
    (c : TraceClaim)
    (h_dwlp :
      ∀ args mem,
        c.pre args mem →
        DWLP mirTraceWP (mirStatefulTreeWithCallees c.body args mem c.callees)
          (fun out tr => c.post args mem tr out) []) :
    TraceVerificationResult c := by
  refine ⟨fun args mem h_pre => ?_⟩
  have h_adeq := dwlp_trace_adequacy (h_dwlp args mem h_pre)
  exact ⟨h_adeq.1, fun outPair h_ret => h_adeq.2 outPair.1 outPair.2 h_ret⟩

/-- Prove a trace-aware `TraceVerificationResult c` from `wpMirTraceBounded`. -/
theorem verifyTraceMirBounded
    (c : TraceClaim) (fuel : Nat)
    (h_wp :
      ∀ args mem,
        c.pre args mem →
        wpMirTraceBounded fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (fun tr out => c.post args mem tr out)) :
    TraceVerificationResult c :=
  verifyTraceByDWLP c
    (fun args mem h_pre => dwlp_cofix_of_wpCoalBounded (h_wp args mem h_pre))

/-- Prove a total-correctness `TotalVerificationResult c` from `DWP mirDefaultWP`. -/
theorem verifyTotalByDWP
    (c : TotalClaim)
    (h_dwp :
      ∀ args mem,
        c.pre args mem →
        DWP mirDefaultWP (mirStatefulTreeWithCallees c.body args mem c.callees)
          (fun out _ =>
            ∃ retVal mem',
              out = .normal (retVal, mem') ∧ c.post args mem retVal mem')
          PUnit.unit) :
    TotalVerificationResult c :=
  ⟨fun args mem h_pre => dwp_pure_adequacy (h_dwp args mem h_pre)⟩

/-- Prove a total-correctness `TotalVerificationResult c` from `wpMirBounded`. -/
theorem verifyTotalMirBounded
    (c : TotalClaim) (fuel : Nat)
    (h_wp :
      ∀ args mem,
        c.pre args mem →
        wpMirBounded fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (fun out =>
            ∃ retVal mem',
              out = .normal (retVal, mem') ∧ c.post args mem retVal mem')) :
    TotalVerificationResult c :=
  verifyTotalByDWP c
    (fun args mem h_pre => dwp_cofix_of_wpCoalBounded fuel (h_wp args mem h_pre))

/--
Semantic rely predicate stating that an `ExternalCallHandler` `h` implements
`C : CallContract MirCallReq (fun _ => MirCallAns)` under `DWLP mirClosedWP`.
-/
def envSatisfiesContract
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (h : ExternalCallHandler) : Prop :=
  ∀ (req : MirCallReq) (Q : MirCallAns → PUnit → Prop),
    C.pre req →
    (∀ ans : MirCallAns, C.post req ans → Q ans PUnit.unit) →
    DWLP mirClosedWP (h req) Q PUnit.unit

private theorem handleMirExternalCalls_links_modularWP
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (h : ExternalCallHandler) (h_env : envSatisfiesContract C h) :
    ∀ (i : MirEffect.I) (Q : MirEffect.O i → PUnit → Prop) (u : PUnit),
      (mirModularWP C).wp i Q u →
      DWLP mirClosedWP (handleMirExternalCalls h i) Q u
  | .inl (.fail _), _, .unit, h_wp => False.elim h_wp
  | .inr (.inl (.emit _)), _, .unit, h_wp => DWLP.vis (DWLP.ret h_wp)
  | .inr (.inr (.call req)), Q, .unit, h_wp => h_env req Q h_wp.1 h_wp.2

/--
Prove a `ModularVerificationResult` with linked `callees` against
`envSatisfiesContract C` from `DWLP (mirModularWP C)` by linking
`handleMirExternalCalls` via `dwlp_interp`.
-/
theorem verifyModularWithCalleesByDWLP
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (h_dwlp :
      ∀ args mem,
        pre args mem →
        DWLP (mirModularWP C)
          (mirStatefulTreeWithCallees body args mem callees)
          (fun out _ =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → post args mem retVal mem')
          PUnit.unit) :
    ModularVerificationResult
      { body, envAssumed := envSatisfiesContract C, pre, post, callees } := by
  refine ⟨fun h h_env args mem h_pre => ?_⟩
  have h_interp :=
    dwlp_interp
      (handleMirExternalCalls h)
      (handleMirExternalCalls_links_modularWP C h h_env)
      (h_dwlp args mem h_pre)
  have h_adeq := dwlp_pure_adequacy h_interp
  exact ⟨h_adeq.1, fun outPair h_ret _ retVal mem' h_out =>
    h_adeq.2 outPair.1 outPair.2 h_ret retVal mem' h_out⟩

/--
Prove a `ModularVerificationResult` against `envSatisfiesContract C` from
`DWLP (mirModularWP C)` by linking `handleMirExternalCalls` via `dwlp_interp`.
-/
theorem verifyModularByDWLP
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (h_dwlp :
      ∀ args mem,
        pre args mem →
        DWLP (mirModularWP C) (mirStatefulTree body args mem)
          (fun out _ =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → post args mem retVal mem')
          PUnit.unit) :
    ModularVerificationResult
      { body, envAssumed := envSatisfiesContract C, pre, post } :=
  verifyModularWithCalleesByDWLP C body .nil pre post h_dwlp

/-- Prove a `ModularVerificationResult` with linked `callees` from `wpMirModularBounded`. -/
theorem verifyModularWithCalleesMirBounded
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ args mem,
        pre args mem →
        wpMirModularBounded fuel C body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → post args mem retVal mem')) :
    ModularVerificationResult
      { body, envAssumed := envSatisfiesContract C, pre, post, callees } :=
  verifyModularWithCalleesByDWLP C body callees pre post
    (fun args mem h_pre => dwlp_cofix_of_wpCoalBounded (h_wp args mem h_pre))

/-- Prove a `ModularVerificationResult` from `wpMirModularBounded`. -/
theorem verifyModularMirBounded
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ args mem,
        pre args mem →
        wpMirModularBounded fuel C body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → post args mem retVal mem')) :
    ModularVerificationResult
      { body, envAssumed := envSatisfiesContract C, pre, post } :=
  verifyModularWithCalleesMirBounded C body .nil pre post fuel h_wp

private theorem dwlp_ubWaived_reaches
    {t u : ITree MirEffect MirOutcome} {tr : List (Event MirEffect)}
    {Q : MirOutcome → PUnit → Prop}
    (h_reach : Reaches t tr u)
    (h_dwlp : DWLP mirUbWaivedWP t Q PUnit.unit) :
    DWLP mirUbWaivedWP u Q PUnit.unit := by
  induction h_reach with
  | refl => exact h_dwlp
  | tau ht _ ih =>
    rw [DWLP.unfold_eq, ht] at h_dwlp; exact ih h_dwlp
  | @vis _ _ i k _ hv _ o _ ih =>
    rw [DWLP.unfold_eq, hv] at h_dwlp
    cases i with
    | inl f => cases f; nomatch o
    | inr rest =>
      cases rest with
      | inl obs => cases obs; cases o; exact ih h_dwlp
      | inr call => cases call; exact ih (h_dwlp o)

/--
Adequacy of `DWLP mirUbWaivedWP` on normal/returning paths: even when `.fail .ub`
branches are waived (`wp _ _ _ := True`), any completed `ReachesRet t tr out`
path cannot pass through a fault node (`MirFailE.O _ = PEmpty`), so `post out`
holds on every return `out`.
-/
theorem dwlp_ubWaived_reachesRet
    {t : ITree MirEffect MirOutcome} {post : MirOutcome → Prop}
    (h_dwlp : DWLP mirUbWaivedWP t (fun out _ => post out) PUnit.unit) :
    ∀ tr out, ReachesRet t tr out → post out := by
  intro tr out ⟨u, h_reach, h_ret⟩
  have hu := dwlp_ubWaived_reaches h_reach h_dwlp
  rw [DWLP.unfold_eq, h_ret] at hu
  exact hu

/--
Prove a scoped `UbExceptionVerificationResult c` constructively (with zero
axioms) from:
1. `DWLP mirDefaultWP` on the strict-safety subdomain
   `c.pre args mem ∧ c.strictSafetyPre args mem`
2. `DWLP mirUbWaivedWP` across the full caller domain `c.pre args mem`.
-/
theorem verifyUbExceptionByDWLP
    (c : UbExceptionClaim)
    (h_strict :
      ∀ args mem,
        c.pre args mem →
        c.strictSafetyPre args mem →
        DWLP mirDefaultWP (mirStatefulTreeWithCallees c.body args mem c.callees)
          (fun out _ =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → c.post args mem retVal mem')
          PUnit.unit)
    (h_waived :
      ∀ args mem,
        c.pre args mem →
        DWLP mirUbWaivedWP (mirStatefulTreeWithCallees c.body args mem c.callees)
          (fun out _ =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → c.post args mem retVal mem')
          PUnit.unit) :
    UbExceptionVerificationResult c := by
  refine ⟨⟨?_, ?_⟩⟩
  · intro args mem ⟨h_pre, h_s⟩
    have h_adeq := dwlp_pure_adequacy (h_strict args mem h_pre h_s)
    exact ⟨h_adeq.1, fun outPair h_ret _ retVal mem' h_out =>
      h_adeq.2 outPair.1 outPair.2 h_ret retVal mem' h_out⟩
  · intro args mem h_pre tr retVal mem' h_ret
    exact dwlp_ubWaived_reachesRet (h_waived args mem h_pre)
      tr (.normal (retVal, mem')) h_ret retVal mem' rfl

/--
Prove a scoped `UbExceptionVerificationResult c` from fuel-bounded
`wpMirBounded` (on `c.pre ∧ c.strictSafetyPre`) and `wpMirUbWaivedBounded`
(on `c.pre`).
-/
theorem verifyUbExceptionMirBounded
    (c : UbExceptionClaim) (fuel : Nat)
    (h_strict :
      ∀ args mem,
        c.pre args mem →
        c.strictSafetyPre args mem →
        wpMirBounded fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (fun out =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → c.post args mem retVal mem'))
    (h_waived :
      ∀ args mem,
        c.pre args mem →
        wpMirUbWaivedBounded fuel c.body
          (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
          (fun out =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → c.post args mem retVal mem')) :
    UbExceptionVerificationResult c :=
  verifyUbExceptionByDWLP c
    (fun args mem h_pre h_s =>
      dwlp_cofix_of_wpCoalBounded (h_strict args mem h_pre h_s))
    (fun args mem h_pre =>
      dwlp_cofix_of_wpCoalBounded (h_waived args mem h_pre))

/--
Completeness of `DWLP mirClosedWP` with respect to `TreeSafe` and `ReachesRet`:
any `t : ITree MirClosedEffect R` that is `TreeSafe` and satisfies `Q r .unit`
on all `ReachesRet` returns satisfies `DWLP mirClosedWP t Q PUnit.unit`.
-/
theorem dwlp_mirClosedWP_of_treeSafe_reachesRet
    {R : Type} {t : ITree MirClosedEffect R} {Q : R → PUnit → Prop}
    (h_safe : TreeSafe t)
    (h_ret : ∀ tr r, ReachesRet t tr r → Q r PUnit.unit) :
    DWLP mirClosedWP t Q PUnit.unit := by
  refine DWLP.coinduct
    (fun u _ => TreeSafe u ∧ ∀ tr r, ReachesRet u tr r → Q r PUnit.unit)
    ?_ ⟨h_safe, h_ret⟩
  intro u _ ⟨hu_safe, hu_ret⟩
  cases h_obs : u.observe with
  | ret r =>
    exact hu_ret [] r ⟨u, .refl u, h_obs⟩
  | tau u' =>
    refine ⟨?_, ?_⟩
    · intro tr w hw
      exact hu_safe tr w (.tau h_obs hw)
    · intro tr r ⟨w, hw, hw_ret⟩
      exact hu_ret tr r ⟨w, .tau h_obs hw, hw_ret⟩
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail fk =>
        exact False.elim
          (hu_safe [] u (.refl u) ⟨u, .inl (.fail fk), k, .refl u, h_obs, trivial⟩)
    | inr obs =>
      cases obs with
      | emit ev =>
        have h_nf : ¬ FaultEffect.isFault (E := MirClosedEffect) (.inr (.emit ev)) :=
          not_false
        refine ⟨?_, ?_⟩
        · intro tr w hw
          exact hu_safe (⟨.inr (.emit ev), .unit⟩ :: tr) w
            (.vis h_obs h_nf .unit hw)
        · intro tr r ⟨w, hw, hw_ret⟩
          exact hu_ret (⟨.inr (.emit ev), .unit⟩ :: tr) r
            ⟨w, .vis h_obs h_nf .unit hw, hw_ret⟩

/--
Convert a trusted `MirCallContract.holdsOn C h` rely hypothesis into
`envSatisfiesContract C.toCallContract h`.
-/
theorem envSatisfiesContract_of_holdsOn
    (C : MirCallContract) (h : ExternalCallHandler)
    (h_on : C.holdsOn h) :
    envSatisfiesContract C.toCallContract h := by
  intro req Q h_pre h_post_imp
  rcases h_on req h_pre with ⟨h_safe, h_ret⟩
  exact dwlp_mirClosedWP_of_treeSafe_reachesRet h_safe
    (fun tr ans h_r => h_post_imp ans (h_ret tr ans h_r))

/--
Convert `envSatisfiesContract C.toCallContract h` into the trusted rely
predicate `C.holdsOn h`.
-/
theorem holdsOn_of_envSatisfiesContract
    (C : MirCallContract) (h : ExternalCallHandler)
    (h_env : envSatisfiesContract C.toCallContract h) :
    C.holdsOn h := by
  intro req h_pre
  have h_dwlp :
      DWLP mirClosedWP (h req) (fun ans _ => C.post req ans) PUnit.unit :=
    h_env req (fun ans _ => C.post req ans) h_pre (fun _ hp => hp)
  exact dwlp_pure_adequacy h_dwlp

/--
Exact equivalence between `C.holdsOn h` and
`envSatisfiesContract C.toCallContract h`.
-/
theorem holdsOn_iff_envSatisfiesContract
    (C : MirCallContract) (h : ExternalCallHandler) :
    C.holdsOn h ↔ envSatisfiesContract C.toCallContract h :=
  ⟨envSatisfiesContract_of_holdsOn C h, holdsOn_of_envSatisfiesContract C h⟩

/--
Prove a `ModularVerificationResult` with linked `callees` against `C.holdsOn`
(`MirCallContract`) from `DWLP (mirModularWP C.toCallContract)`.
-/
theorem verifyModularContractWithCalleesByDWLP
    (C : MirCallContract)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (h_dwlp :
      ∀ args mem,
        pre args mem →
        DWLP (mirModularWP C.toCallContract)
          (mirStatefulTreeWithCallees body args mem callees)
          (fun out _ =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → post args mem retVal mem')
          PUnit.unit) :
    ModularVerificationResult
      { body, envAssumed := C.holdsOn, pre, post, callees } :=
  ⟨fun h h_on =>
    (verifyModularWithCalleesByDWLP C.toCallContract body callees pre post h_dwlp).proof
      h (envSatisfiesContract_of_holdsOn C h h_on)⟩

/--
Prove a `ModularVerificationResult` against `C.holdsOn` (`MirCallContract`) from
`DWLP (mirModularWP C.toCallContract)`.
-/
theorem verifyModularContractByDWLP
    (C : MirCallContract)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (h_dwlp :
      ∀ args mem,
        pre args mem →
        DWLP (mirModularWP C.toCallContract) (mirStatefulTree body args mem)
          (fun out _ =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → post args mem retVal mem')
          PUnit.unit) :
    ModularVerificationResult
      { body, envAssumed := C.holdsOn, pre, post } :=
  verifyModularContractWithCalleesByDWLP C body .nil pre post h_dwlp

/--
Prove a `ModularVerificationResult` with linked `callees` against `C.holdsOn`
(`MirCallContract`) from fuel-bounded `wpMirModularBounded`.
-/
theorem verifyModularContractWithCalleesMirBounded
    (C : MirCallContract)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ args mem,
        pre args mem →
        wpMirModularBounded fuel C.toCallContract body
          (initMachineStateWithMemoryAndCallees body args mem callees)
          (fun out =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → post args mem retVal mem')) :
    ModularVerificationResult
      { body, envAssumed := C.holdsOn, pre, post, callees } :=
  verifyModularContractWithCalleesByDWLP C body callees pre post
    (fun args mem h_pre => dwlp_cofix_of_wpCoalBounded (h_wp args mem h_pre))

/--
Prove a `ModularVerificationResult` against `C.holdsOn` (`MirCallContract`) from
fuel-bounded `wpMirModularBounded`.
-/
theorem verifyModularContractMirBounded
    (C : MirCallContract)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (fuel : Nat)
    (h_wp :
      ∀ args mem,
        pre args mem →
        wpMirModularBounded fuel C.toCallContract body
          (initMachineStateWithMemory body args mem)
          (fun out =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → post args mem retVal mem')) :
    ModularVerificationResult
      { body, envAssumed := C.holdsOn, pre, post } :=
  verifyModularContractWithCalleesMirBounded C body .nil pre post fuel h_wp

/-! ## 3. Horizontal Caller–Callee Linking via `ITree.interp` -/

/--
Fail-closed effect projection closing `MirEffect` into `MirClosedEffect` by
routing any unexpected nested `MirCallE` request to `.fail .unsupported`.
-/
def failUnlinkedCalls :
    (i : MirEffect.I) → ITree MirClosedEffect (MirEffect.O i)
  | .inl (.fail fk) => ITree.fail (E := MirClosedEffect) fk
  | .inr (.inl (.emit obs)) => ITree.emit (E := MirClosedEffect) obs
  | .inr (.inr (.call _)) => ITree.fail (E := MirClosedEffect) FailureKind.unsupported

/-- Convert a root callee `MirOutcome` into the `MirCallAns` returned to callers. -/
def outcomeToCallAns (memFallback : Memory) : MirOutcome → MirCallAns
  | .normal (retVal, mem') => .returned retVal mem'
  | .panic => .panicked memFallback
  | .abort => .aborted

/-- Wrap a call-free callee tree `t` as an `ITree MirClosedEffect MirCallAns`. -/
def closeMirTreeAsCallAns
    (memFallback : Memory) (t : ITree MirEffect MirOutcome) :
    ITree MirClosedEffect MirCallAns :=
  ITree.interp failUnlinkedCalls t >>= fun out =>
    pure (outcomeToCallAns memFallback out)

/--
Extend a fallback `ExternalCallHandler` by linking calls targeting
`calleeBody.defPath` directly to `calleeBody`'s `mirStatefulTree`.
-/
def linkCalleeHandler
    (calleeBody : CapturedMir) (fallback : ExternalCallHandler) :
    ExternalCallHandler :=
  fun req =>
    if req.defPath = calleeBody.defPath then
      closeMirTreeAsCallAns req.memory
        (mirStatefulTree calleeBody req.args req.memory)
    else
      fallback req

private theorem failUnlinkedCalls_links_noCallWP :
    ∀ (i : MirEffect.I) (Q : MirEffect.O i → PUnit → Prop) (u : PUnit),
      mirNoCallWP.wp i Q u →
      DWLP mirClosedWP (failUnlinkedCalls i) Q u
  | .inl (.fail _), _, .unit, h_wp => False.elim h_wp
  | .inr (.inl (.emit _)), _, .unit, h_wp => DWLP.vis (DWLP.ret h_wp)
  | .inr (.inr (.call _)), _, .unit, h_wp => False.elim h_wp

/-- Lift `DWLP mirNoCallWP` on a call-free callee tree to `closeMirTreeAsCallAns`. -/
theorem dwlp_closeMirTreeAsCallAns
    {memFallback : Memory} {t : ITree MirEffect MirOutcome}
    {Q : MirCallAns → PUnit → Prop}
    (h_dwlp :
      DWLP mirNoCallWP t
        (fun out _ => Q (outcomeToCallAns memFallback out) PUnit.unit)
        PUnit.unit) :
    DWLP mirClosedWP (closeMirTreeAsCallAns memFallback t) Q PUnit.unit := by
  unfold closeMirTreeAsCallAns
  apply DWLP.bind
  exact DWLP.mono (fun _ _ hq => DWLP.ret hq)
    (dwlp_interp failUnlinkedCalls failUnlinkedCalls_links_noCallWP h_dwlp)

/--
Horizontal handler-discharge lemma establishing `envSatisfiesContract C` for
`linkCalleeHandler calleeBody fallback`.
-/
theorem envSatisfiesContract_linkCalleeHandler
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (calleeBody : CapturedMir) (fallback : ExternalCallHandler)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        DWLP mirNoCallWP (mirStatefulTree calleeBody req.args req.memory)
          (fun out _ => C.post req (outcomeToCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ (req : MirCallReq) (Q : MirCallAns → PUnit → Prop),
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        (∀ ans : MirCallAns, C.post req ans → Q ans PUnit.unit) →
        DWLP mirClosedWP (fallback req) Q PUnit.unit) :
    envSatisfiesContract C (linkCalleeHandler calleeBody fallback) := by
  intro req Q h_pre h_post_imp
  unfold linkCalleeHandler
  split
  · next h_eq =>
    apply dwlp_closeMirTreeAsCallAns
    exact DWLP.mono
      (fun out _ h_cpost => h_post_imp (outcomeToCallAns req.memory out) h_cpost)
      (h_callee req h_eq h_pre)
  · next h_ne =>
    exact h_fallback req Q h_ne h_pre h_post_imp

/--
Horizontal caller–callee linking theorem: combines a modularly verified caller
`ModularVerificationResult` with a verified call-free callee `calleeBody` to
obtain closed-effect partial refinement on `mirHandledTree`.
-/
theorem linkVerifiedMirCallee
    {C : CallContract MirCallReq (fun _ => MirCallAns)}
    {callerBody : CapturedMir}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (h_caller :
      ModularVerificationResult
        { body := callerBody
          envAssumed := envSatisfiesContract C
          pre := pre
          post := post })
    (calleeBody : CapturedMir) (fallback : ExternalCallHandler)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        DWLP mirNoCallWP (mirStatefulTree calleeBody req.args req.memory)
          (fun out _ => C.post req (outcomeToCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ (req : MirCallReq) (Q : MirCallAns → PUnit → Prop),
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        (∀ ans : MirCallAns, C.post req ans → Q ans PUnit.unit) →
        DWLP mirClosedWP (fallback req) Q PUnit.unit) :
    (fun args mem =>
      (mirHandledTree callerBody args mem
        (linkCalleeHandler calleeBody fallback)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  h_caller.proof
    (linkCalleeHandler calleeBody fallback)
    (envSatisfiesContract_linkCalleeHandler
      C calleeBody fallback h_callee h_fallback)

/--
Initial `MachineState` for executing `calleeBody` inside an isolated
`ExternalCallHandler` frame (`MirCallE`), populating `callees := calleeCallees`
and `traitImpls := calleeBody.traitImpls ++ callerMem.traitImpls` (so generic
callees can dispatch trait methods registered in either the callee or the caller
crate, deduplicated by `upsertMatchingTraitImpl`) while resetting
`callStack := .nil`, `activeCallee := .none`, and `activeProtectors := .nil` so
`calleeBody` executes as the root of its own interaction tree even when
`callerMem` is symbolic or inside a nested caller stack frame.
-/
@[reducible, simp]
def enterExternalCalleeState
    (calleeBody : CapturedMir)
    (args : List Value)
    (callerMem : Memory)
    (calleeCallees : List CapturedMir := .nil) : MachineState :=
  initMachineStateWithMemory calleeBody args
    { callerMem with
      callees := calleeCallees
      traitImpls := calleeBody.traitImpls ++ callerMem.traitImpls
      callStack := .nil
      activeCallee := .none
      activeProtectors := .nil }

/--
Coinductive interaction tree for executing `calleeBody` inside an isolated
`ExternalCallHandler` frame (`enterExternalCalleeState`).
-/
def mirExternalCalleeTree
    (calleeBody : CapturedMir)
    (args : List Value)
    (callerMem : Memory)
    (calleeCallees : List CapturedMir := .nil) :
    ITree MirEffect MirOutcome :=
  mirTree calleeBody
    (enterExternalCalleeState calleeBody args callerMem calleeCallees)

/--
Restore the caller's call-frame and trait-table fields (`callees`, `traitImpls`,
`callStack`, `activeCallee`, `activeProtectors`) onto the post-call memory
`after` returned by an external callee, while preserving all heap, borrow,
global, and `fnPtrs` updates produced by the callee.
-/
@[reducible, simp]
def restoreCallerMemoryFrame (before after : Memory) : Memory :=
  { after with
    callees := before.callees
    traitImpls := before.traitImpls
    callStack := before.callStack
    activeCallee := before.activeCallee
    activeProtectors := before.activeProtectors }

/--
Stronger call-frame preservation predicate that preserves both
`callFramePreserved` (`callees`, `callStack`, `activeCallee`,
`activeProtectors`, and `fnPtrs` suffix) and `traitImpls`.
-/
@[reducible, simp]
def callFrameAndTraitsPreserved (before after : Memory) : Prop :=
  And (callFramePreserved before after) (after.traitImpls = before.traitImpls)

theorem callFramePreserved_restoreCallerMemoryFrame
    (before after : Memory)
    (fresh : List FnPtrEntry)
    (h_fnPtrs : after.fnPtrs = List.append fresh before.fnPtrs) :
    callFramePreserved before (restoreCallerMemoryFrame before after) :=
  ⟨rfl, rfl, rfl, rfl, fresh, h_fnPtrs⟩

@[simp]
theorem callFramePreserved_restoreCallerMemoryFrame_same_fnPtrs
    (before after : Memory)
    (h_fnPtrs : after.fnPtrs = before.fnPtrs) :
    callFramePreserved before (restoreCallerMemoryFrame before after) :=
  callFramePreserved_restoreCallerMemoryFrame before after .nil h_fnPtrs

theorem callFrameAndTraitsPreserved_restoreCallerMemoryFrame
    (before after : Memory)
    (fresh : List FnPtrEntry)
    (h_fnPtrs : after.fnPtrs = List.append fresh before.fnPtrs) :
    callFrameAndTraitsPreserved before (restoreCallerMemoryFrame before after) :=
  ⟨callFramePreserved_restoreCallerMemoryFrame before after fresh h_fnPtrs, rfl⟩

@[simp]
theorem callFrameAndTraitsPreserved_restoreCallerMemoryFrame_same_fnPtrs
    (before after : Memory)
    (h_fnPtrs : after.fnPtrs = before.fnPtrs) :
    callFrameAndTraitsPreserved before (restoreCallerMemoryFrame before after) :=
  callFrameAndTraitsPreserved_restoreCallerMemoryFrame before after .nil h_fnPtrs

/--
Polymorphic and trait-preserving extension of `externalSpecCallContract` that
additionally constrains `req.typeArgs = expectedTypeArgs` in `pre` and
preserves `memAfter.traitImpls = req.memory.traitImpls` (`callFrameAndTraitsPreserved`)
in `post`, enabling post-call polymorphic and trait-method calls in `c.callees`
to reduce by WHNF without manual rewrites.
-/
def polyExternalSpecCallContract
    (targetDefPath : DefPath)
    (expectedTypeArgs : List RigidTy)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True) :
    MirCallContract where
  pre req :=
    And (req.defPath = targetDefPath)
      (And (req.typeArgs = expectedTypeArgs)
        (And (Trusted.Sequence.length req.args = sidecarBody.argCount)
          (And (argsMatchCalleeParamTys sidecarBody req.args)
            (extraPre req.args))))
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      And (callFrameAndTraitsPreserved req.memory memAfter)
        (And (retMatchesCalleeReturnTy sidecarBody retVal)
          (extraPost req.args retVal))
    | .panicked memAfter =>
      match sidecarTargetCanUnwind sidecarBody with
      | true => callFrameAndTraitsPreserved req.memory memAfter
      | false => False
    | .aborted => True

/--
Convert a linked callee `MirOutcome` into a `MirCallAns` that restores the
caller's `callees`, `traitImpls`, `callStack`, `activeCallee`, and
`activeProtectors` from `callerMem`.
-/
@[reducible, simp]
def outcomeToRestoredCallAns (callerMem : Memory) : MirOutcome → MirCallAns
  | .normal (retVal, mem') =>
    .returned retVal (restoreCallerMemoryFrame callerMem mem')
  | .panic => .panicked callerMem
  | .abort => .aborted

/--
Wrap a call-free callee tree `t` as an `ITree MirClosedEffect MirCallAns`
that restores the caller's frame fields from `callerMem` via
`outcomeToRestoredCallAns`.
-/
def closeMirTreeRestoringFrame
    (callerMem : Memory) (t : ITree MirEffect MirOutcome) :
    ITree MirClosedEffect MirCallAns :=
  ITree.interp failUnlinkedCalls t >>= fun out =>
    pure (outcomeToRestoredCallAns callerMem out)

/-- Lift `DWLP mirNoCallWP` on a call-free callee tree to `closeMirTreeRestoringFrame`. -/
theorem dwlp_closeMirTreeRestoringFrame
    {callerMem : Memory} {t : ITree MirEffect MirOutcome}
    {Q : MirCallAns → PUnit → Prop}
    (h_dwlp :
      DWLP mirNoCallWP t
        (fun out _ => Q (outcomeToRestoredCallAns callerMem out) PUnit.unit)
        PUnit.unit) :
    DWLP mirClosedWP (closeMirTreeRestoringFrame callerMem t) Q PUnit.unit := by
  unfold closeMirTreeRestoringFrame
  apply DWLP.bind
  exact DWLP.mono (fun _ _ hq => DWLP.ret hq)
    (dwlp_interp failUnlinkedCalls failUnlinkedCalls_links_noCallWP h_dwlp)

/--
Extend a fallback `ExternalCallHandler` by linking calls targeting
`calleeBody.defPath` to `calleeBody`'s isolated `mirExternalCalleeTree` with its
own linked helper table `calleeCallees`, restoring the caller's frame fields
upon return via `closeMirTreeRestoringFrame`.
-/
def linkCalleeWithCalleesHandler
    (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler) :
    ExternalCallHandler :=
  fun req =>
    if req.defPath = calleeBody.defPath then
      closeMirTreeRestoringFrame req.memory
        (mirExternalCalleeTree calleeBody req.args req.memory calleeCallees)
    else
      fallback req

/--
Resolve and instantiate `calleeBody` for an external call request `req` using
the caller's `callerLayouts : LayoutTable` and optional `extraTraitImpls` via
`lookupCallee`, falling back to `calleeBody` when uninstantiated.
-/
def instantiateCalleeForReq
    (calleeBody : CapturedMir)
    (callerLayouts : LayoutTable)
    (req : MirCallReq)
    (extraTraitImpls : List TraitImplEntry := .nil) : CapturedMir :=
  (lookupCallee [calleeBody] callerLayouts req.defPath req.typeArgs extraTraitImpls).getD calleeBody

/--
Extend a fallback `ExternalCallHandler` by linking calls targeting
`calleeBody.defPath` to the monomorphized instance
`instantiateCalleeForReq calleeBody callerLayouts req extraTraitImpls` in an
isolated `mirExternalCalleeTree` with linked helper table `calleeCallees`,
restoring the caller's frame fields upon return.
-/
def linkPolyCalleeWithCalleesHandler
    (calleeBody : CapturedMir)
    (callerLayouts : LayoutTable)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (extraTraitImpls : List TraitImplEntry := .nil) :
    ExternalCallHandler :=
  fun req =>
    if req.defPath = calleeBody.defPath then
      closeMirTreeRestoringFrame req.memory
        (mirExternalCalleeTree
          (instantiateCalleeForReq calleeBody callerLayouts req extraTraitImpls)
          req.args
          req.memory
          calleeCallees)
    else
      fallback req

/--
Extend a fallback `ExternalCallHandler` by linking any call request `req`
(direct generic or trait-method dispatch) that resolves via
`lookupCallee [calleeBody] callerLayouts req.defPath req.typeArgs extraTraitImpls`
to `.some instBody`, executing `instBody` in an isolated `mirExternalCalleeTree`
with `calleeCallees` and restoring the caller's frame fields upon return.
-/
def linkTraitOrPolyCalleeWithCalleesHandler
    (calleeBody : CapturedMir)
    (callerLayouts : LayoutTable)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (extraTraitImpls : List TraitImplEntry := .nil) :
    ExternalCallHandler :=
  fun req =>
    match lookupCallee [calleeBody] callerLayouts req.defPath req.typeArgs extraTraitImpls with
    | .some instBody =>
      closeMirTreeRestoringFrame req.memory
        (mirExternalCalleeTree instBody req.args req.memory calleeCallees)
    | .none =>
      fallback req

/--
Horizontal handler-discharge lemma establishing `envSatisfiesContract C` for
`linkCalleeWithCalleesHandler calleeBody calleeCallees fallback`.
-/
theorem envSatisfiesContract_linkCalleeWithCalleesHandler
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree calleeBody req.args req.memory calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ (req : MirCallReq) (Q : MirCallAns → PUnit → Prop),
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        (∀ ans : MirCallAns, C.post req ans → Q ans PUnit.unit) →
        DWLP mirClosedWP (fallback req) Q PUnit.unit) :
    envSatisfiesContract C
      (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback) := by
  intro req Q h_pre h_post_imp
  unfold linkCalleeWithCalleesHandler
  split
  · next h_eq =>
    apply dwlp_closeMirTreeRestoringFrame
    exact DWLP.mono
      (fun out _ h_cpost => h_post_imp (outcomeToRestoredCallAns req.memory out) h_cpost)
      (h_callee req h_eq h_pre)
  · next h_ne =>
    exact h_fallback req Q h_ne h_pre h_post_imp

/--
Horizontal handler-discharge lemma establishing `envSatisfiesContract C` for
polymorphic `linkPolyCalleeWithCalleesHandler`.
-/
theorem envSatisfiesContract_linkPolyCalleeWithCalleesHandler
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (calleeBody : CapturedMir)
    (callerLayouts : LayoutTable)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (extraTraitImpls : List TraitImplEntry := .nil)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree
            (instantiateCalleeForReq calleeBody callerLayouts req extraTraitImpls)
            req.args
            req.memory
            calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ (req : MirCallReq) (Q : MirCallAns → PUnit → Prop),
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        (∀ ans : MirCallAns, C.post req ans → Q ans PUnit.unit) →
        DWLP mirClosedWP (fallback req) Q PUnit.unit) :
    envSatisfiesContract C
      (linkPolyCalleeWithCalleesHandler
        calleeBody callerLayouts calleeCallees fallback extraTraitImpls) := by
  intro req Q h_pre h_post_imp
  unfold linkPolyCalleeWithCalleesHandler
  split
  · next h_eq =>
    apply dwlp_closeMirTreeRestoringFrame
    exact DWLP.mono
      (fun out _ h_cpost => h_post_imp (outcomeToRestoredCallAns req.memory out) h_cpost)
      (h_callee req h_eq h_pre)
  · next h_ne =>
    exact h_fallback req Q h_ne h_pre h_post_imp

/--
Horizontal handler-discharge lemma establishing `envSatisfiesContract C` for
trait-or-polymorphic `linkTraitOrPolyCalleeWithCalleesHandler`.
-/
theorem envSatisfiesContract_linkTraitOrPolyCalleeWithCalleesHandler
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (calleeBody : CapturedMir)
    (callerLayouts : LayoutTable)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (extraTraitImpls : List TraitImplEntry := .nil)
    (h_callee :
      ∀ (req : MirCallReq) (instBody : CapturedMir),
        lookupCallee [calleeBody] callerLayouts req.defPath req.typeArgs extraTraitImpls =
          .some instBody →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree instBody req.args req.memory calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ (req : MirCallReq) (Q : MirCallAns → PUnit → Prop),
        lookupCallee [calleeBody] callerLayouts req.defPath req.typeArgs extraTraitImpls =
          .none →
        C.pre req →
        (∀ ans : MirCallAns, C.post req ans → Q ans PUnit.unit) →
        DWLP mirClosedWP (fallback req) Q PUnit.unit) :
    envSatisfiesContract C
      (linkTraitOrPolyCalleeWithCalleesHandler
        calleeBody callerLayouts calleeCallees fallback extraTraitImpls) := by
  intro req Q h_pre h_post_imp
  unfold linkTraitOrPolyCalleeWithCalleesHandler
  cases h_lk : lookupCallee [calleeBody] callerLayouts req.defPath req.typeArgs extraTraitImpls with
  | some instBody =>
    apply dwlp_closeMirTreeRestoringFrame
    exact DWLP.mono
      (fun out _ h_cpost => h_post_imp (outcomeToRestoredCallAns req.memory out) h_cpost)
      (h_callee req instBody h_lk h_pre)
  | none =>
    exact h_fallback req Q h_lk h_pre h_post_imp

/--
Establish `C.holdsOn (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback)`
from `DWLP mirNoCallWP` on `calleeBody` with `calleeCallees` and `C.holdsOn fallback`
on other paths.
-/
theorem holdsOn_linkCalleeWithCalleesHandler
    (C : MirCallContract)
    (calleeBody : CapturedMir)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree calleeBody req.args req.memory calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ req : MirCallReq,
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    C.holdsOn
      (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback) := by
  apply holdsOn_of_envSatisfiesContract
  refine envSatisfiesContract_linkCalleeWithCalleesHandler
    C.toCallContract calleeBody calleeCallees fallback h_callee ?_
  intro req Q h_ne h_pre h_post_imp
  rcases h_fallback req h_ne h_pre with ⟨h_safe, h_ret⟩
  exact dwlp_mirClosedWP_of_treeSafe_reachesRet h_safe
    (fun tr ans h_r => h_post_imp ans (h_ret tr ans h_r))

/--
Establish `C.holdsOn (linkPolyCalleeWithCalleesHandler ...)` from `DWLP mirNoCallWP`
on `instantiateCalleeForReq` with `calleeCallees` and `C.holdsOn fallback` on
other paths.
-/
theorem holdsOn_linkPolyCalleeWithCalleesHandler
    (C : MirCallContract)
    (calleeBody : CapturedMir)
    (callerLayouts : LayoutTable)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (extraTraitImpls : List TraitImplEntry := .nil)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree
            (instantiateCalleeForReq calleeBody callerLayouts req extraTraitImpls)
            req.args
            req.memory
            calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ req : MirCallReq,
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    C.holdsOn
      (linkPolyCalleeWithCalleesHandler
        calleeBody callerLayouts calleeCallees fallback extraTraitImpls) := by
  apply holdsOn_of_envSatisfiesContract
  refine envSatisfiesContract_linkPolyCalleeWithCalleesHandler
    C.toCallContract calleeBody callerLayouts calleeCallees fallback extraTraitImpls h_callee ?_
  intro req Q h_ne h_pre h_post_imp
  rcases h_fallback req h_ne h_pre with ⟨h_safe, h_ret⟩
  exact dwlp_mirClosedWP_of_treeSafe_reachesRet h_safe
    (fun tr ans h_r => h_post_imp ans (h_ret tr ans h_r))

/--
Establish `C.holdsOn (linkTraitOrPolyCalleeWithCalleesHandler ...)` from
`DWLP mirNoCallWP` on resolved `instBody` instances and `C.holdsOn fallback`
when `lookupCallee` returns `.none`.
-/
theorem holdsOn_linkTraitOrPolyCalleeWithCalleesHandler
    (C : MirCallContract)
    (calleeBody : CapturedMir)
    (callerLayouts : LayoutTable)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (extraTraitImpls : List TraitImplEntry := .nil)
    (h_callee :
      ∀ (req : MirCallReq) (instBody : CapturedMir),
        lookupCallee [calleeBody] callerLayouts req.defPath req.typeArgs extraTraitImpls =
          .some instBody →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree instBody req.args req.memory calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ req : MirCallReq,
        lookupCallee [calleeBody] callerLayouts req.defPath req.typeArgs extraTraitImpls =
          .none →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    C.holdsOn
      (linkTraitOrPolyCalleeWithCalleesHandler
        calleeBody callerLayouts calleeCallees fallback extraTraitImpls) := by
  apply holdsOn_of_envSatisfiesContract
  refine envSatisfiesContract_linkTraitOrPolyCalleeWithCalleesHandler
    C.toCallContract calleeBody callerLayouts calleeCallees fallback extraTraitImpls h_callee ?_
  intro req Q h_none h_pre h_post_imp
  rcases h_fallback req h_none h_pre with ⟨h_safe, h_ret⟩
  exact dwlp_mirClosedWP_of_treeSafe_reachesRet h_safe
    (fun tr ans h_r => h_post_imp ans (h_ret tr ans h_r))

/--
Horizontal caller–callee linking theorem with non-empty `callerCallees` and
`calleeCallees` under `C.holdsOn`: combines a modularly verified caller
`ModularVerificationResult` with a verified callee `calleeBody` (stepping
through `calleeCallees` in an isolated frame and restoring the caller's frame
fields upon return) to obtain closed-effect partial refinement on
`mirHandledTreeWithCallees`.
-/
theorem linkVerifiedContractMirCalleeWithCallees
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
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree calleeBody req.args req.memory calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
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
  h_caller.proof
    (linkCalleeWithCalleesHandler calleeBody calleeCallees fallback)
    (holdsOn_linkCalleeWithCalleesHandler
      C calleeBody calleeCallees fallback h_callee h_fallback)

/--
Polymorphic horizontal caller–callee linking theorem with `callerCallees` and
`calleeCallees` under `C.holdsOn`: links each call request `req` targeting
`calleeBody.defPath` to the monomorphized body
`instantiateCalleeForReq calleeBody callerBody.layouts req callerBody.traitImpls`.
-/
theorem linkVerifiedPolyContractMirCalleeWithCallees
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
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ req : MirCallReq,
        req.defPath = calleeBody.defPath →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree
            (instantiateCalleeForReq calleeBody callerBody.layouts req callerBody.traitImpls)
            req.args
            req.memory
            calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ req : MirCallReq,
        req.defPath ≠ calleeBody.defPath →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkPolyCalleeWithCalleesHandler
          calleeBody callerBody.layouts calleeCallees fallback callerBody.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  h_caller.proof
    (linkPolyCalleeWithCalleesHandler
      calleeBody callerBody.layouts calleeCallees fallback callerBody.traitImpls)
    (holdsOn_linkPolyCalleeWithCalleesHandler
      C calleeBody callerBody.layouts calleeCallees fallback callerBody.traitImpls
      h_callee h_fallback)

/--
Trait-or-polymorphic horizontal caller–callee linking theorem with
`callerCallees` and `calleeCallees` under `C.holdsOn`.
-/
theorem linkVerifiedTraitOrPolyContractMirCalleeWithCallees
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
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ (req : MirCallReq) (instBody : CapturedMir),
        lookupCallee [calleeBody] callerBody.layouts req.defPath req.typeArgs callerBody.traitImpls =
          .some instBody →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree instBody req.args req.memory calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ req : MirCallReq,
        lookupCallee [calleeBody] callerBody.layouts req.defPath req.typeArgs callerBody.traitImpls =
          .none →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkTraitOrPolyCalleeWithCalleesHandler
          calleeBody callerBody.layouts calleeCallees fallback callerBody.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  h_caller.proof
    (linkTraitOrPolyCalleeWithCalleesHandler
      calleeBody callerBody.layouts calleeCallees fallback callerBody.traitImpls)
    (holdsOn_linkTraitOrPolyCalleeWithCalleesHandler
      C calleeBody callerBody.layouts calleeCallees fallback callerBody.traitImpls
      h_callee h_fallback)

/--
Fuel-bounded specialization of `linkVerifiedContractMirCalleeWithCallees` via
`wpMirNoCallBounded`.
-/
theorem linkVerifiedContractMirCalleeWithCalleesBounded
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
        wpMirNoCallBounded calleeFuel calleeBody
          (enterExternalCalleeState
            calleeBody req.args req.memory calleeCallees)
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
  linkVerifiedContractMirCalleeWithCallees
    h_caller calleeBody calleeCallees fallback
    (fun req h_eq h_pre =>
      dwlp_cofix_of_wpCoalBounded (h_callee req h_eq h_pre))
    h_fallback

/--
Fuel-bounded specialization of `linkVerifiedPolyContractMirCalleeWithCallees`
via `wpMirNoCallBounded`.
-/
theorem linkVerifiedPolyContractMirCalleeWithCalleesBounded
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
        wpMirNoCallBounded calleeFuel
          (instantiateCalleeForReq calleeBody callerBody.layouts req callerBody.traitImpls)
          (enterExternalCalleeState
            (instantiateCalleeForReq calleeBody callerBody.layouts req callerBody.traitImpls)
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
          calleeBody callerBody.layouts calleeCallees fallback callerBody.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  linkVerifiedPolyContractMirCalleeWithCallees
    h_caller calleeBody calleeCallees fallback
    (fun req h_eq h_pre =>
      dwlp_cofix_of_wpCoalBounded (h_callee req h_eq h_pre))
    h_fallback

/--
Fuel-bounded specialization of `linkVerifiedTraitOrPolyContractMirCalleeWithCallees`
via `wpMirNoCallBounded`.
-/
theorem linkVerifiedTraitOrPolyContractMirCalleeWithCalleesBounded
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
        lookupCallee [calleeBody] callerBody.layouts req.defPath req.typeArgs callerBody.traitImpls =
          .some instBody →
        C.pre req →
        wpMirNoCallBounded calleeFuel
          instBody
          (enterExternalCalleeState instBody req.args req.memory calleeCallees)
          (fun out => C.post req (outcomeToRestoredCallAns req.memory out)))
    (h_fallback :
      ∀ req : MirCallReq,
        lookupCallee [calleeBody] callerBody.layouts req.defPath req.typeArgs callerBody.traitImpls =
          .none →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkTraitOrPolyCalleeWithCalleesHandler
          calleeBody callerBody.layouts calleeCallees fallback callerBody.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  linkVerifiedTraitOrPolyContractMirCalleeWithCallees
    h_caller calleeBody calleeCallees fallback
    (fun req instBody h_lk h_pre =>
      dwlp_cofix_of_wpCoalBounded (h_callee req instBody h_lk h_pre))
    h_fallback

/--
Extend a fallback `ExternalCallHandler` by linking any call request `req`
(direct generic or trait-method dispatch) that resolves via
`lookupCallee calleeTable callerLayouts req.defPath req.typeArgs extraTraitImpls`
across a multi-callee table `calleeTable : List CapturedMir` to `.some instBody`,
executing `instBody` in an isolated `mirExternalCalleeTree` with `calleeCallees`
and restoring the caller's frame fields upon return.
-/
def linkCalleeTableWithCalleesHandler
    (calleeTable : List CapturedMir)
    (callerLayouts : LayoutTable)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (extraTraitImpls : List TraitImplEntry := .nil) :
    ExternalCallHandler :=
  fun req =>
    match lookupCallee calleeTable callerLayouts req.defPath req.typeArgs extraTraitImpls with
    | .some instBody =>
      closeMirTreeRestoringFrame req.memory
        (mirExternalCalleeTree instBody req.args req.memory calleeCallees)
    | .none =>
      fallback req

/--
Horizontal handler-discharge lemma establishing `envSatisfiesContract C` for
multi-callee `linkCalleeTableWithCalleesHandler`.
-/
theorem envSatisfiesContract_linkCalleeTableWithCalleesHandler
    (C : CallContract MirCallReq (fun _ => MirCallAns))
    (calleeTable : List CapturedMir)
    (callerLayouts : LayoutTable)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (extraTraitImpls : List TraitImplEntry := .nil)
    (h_callee :
      ∀ (req : MirCallReq) (instBody : CapturedMir),
        lookupCallee calleeTable callerLayouts req.defPath req.typeArgs extraTraitImpls =
          .some instBody →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree instBody req.args req.memory calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ (req : MirCallReq) (Q : MirCallAns → PUnit → Prop),
        lookupCallee calleeTable callerLayouts req.defPath req.typeArgs extraTraitImpls =
          .none →
        C.pre req →
        (∀ ans : MirCallAns, C.post req ans → Q ans PUnit.unit) →
        DWLP mirClosedWP (fallback req) Q PUnit.unit) :
    envSatisfiesContract C
      (linkCalleeTableWithCalleesHandler
        calleeTable callerLayouts calleeCallees fallback extraTraitImpls) := by
  intro req Q h_pre h_post_imp
  unfold linkCalleeTableWithCalleesHandler
  cases h_lk : lookupCallee calleeTable callerLayouts req.defPath req.typeArgs extraTraitImpls with
  | some instBody =>
    apply dwlp_closeMirTreeRestoringFrame
    exact DWLP.mono
      (fun out _ h_cpost => h_post_imp (outcomeToRestoredCallAns req.memory out) h_cpost)
      (h_callee req instBody h_lk h_pre)
  | none =>
    exact h_fallback req Q h_lk h_pre h_post_imp

/--
Establish `C.holdsOn (linkCalleeTableWithCalleesHandler ...)` from
`DWLP mirNoCallWP` on resolved `instBody` instances in `calleeTable` and
`C.holdsOn fallback` when `lookupCallee` returns `.none`.
-/
theorem holdsOn_linkCalleeTableWithCalleesHandler
    (C : MirCallContract)
    (calleeTable : List CapturedMir)
    (callerLayouts : LayoutTable)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (extraTraitImpls : List TraitImplEntry := .nil)
    (h_callee :
      ∀ (req : MirCallReq) (instBody : CapturedMir),
        lookupCallee calleeTable callerLayouts req.defPath req.typeArgs extraTraitImpls =
          .some instBody →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree instBody req.args req.memory calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ req : MirCallReq,
        lookupCallee calleeTable callerLayouts req.defPath req.typeArgs extraTraitImpls =
          .none →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    C.holdsOn
      (linkCalleeTableWithCalleesHandler
        calleeTable callerLayouts calleeCallees fallback extraTraitImpls) := by
  apply holdsOn_of_envSatisfiesContract
  refine envSatisfiesContract_linkCalleeTableWithCalleesHandler
    C.toCallContract calleeTable callerLayouts calleeCallees fallback extraTraitImpls h_callee ?_
  intro req Q h_none h_pre h_post_imp
  rcases h_fallback req h_none h_pre with ⟨h_safe, h_ret⟩
  exact dwlp_mirClosedWP_of_treeSafe_reachesRet h_safe
    (fun tr ans h_r => h_post_imp ans (h_ret tr ans h_r))

/--
Multi-callee horizontal caller–callee linking theorem with `callerCallees`,
`calleeTable`, and `calleeCallees` under `C.holdsOn`.
-/
theorem linkVerifiedCalleeTableWithCallees
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
    (calleeTable : List CapturedMir)
    (calleeCallees : List CapturedMir)
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ (req : MirCallReq) (instBody : CapturedMir),
        lookupCallee calleeTable callerBody.layouts req.defPath req.typeArgs callerBody.traitImpls =
          .some instBody →
        C.pre req →
        DWLP mirNoCallWP
          (mirExternalCalleeTree instBody req.args req.memory calleeCallees)
          (fun out _ => C.post req (outcomeToRestoredCallAns req.memory out))
          PUnit.unit)
    (h_fallback :
      ∀ req : MirCallReq,
        lookupCallee calleeTable callerBody.layouts req.defPath req.typeArgs callerBody.traitImpls =
          .none →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkCalleeTableWithCalleesHandler
          calleeTable callerBody.layouts calleeCallees fallback callerBody.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  h_caller.proof
    (linkCalleeTableWithCalleesHandler
      calleeTable callerBody.layouts calleeCallees fallback callerBody.traitImpls)
    (holdsOn_linkCalleeTableWithCalleesHandler
      C calleeTable callerBody.layouts calleeCallees fallback callerBody.traitImpls
      h_callee h_fallback)

/--
Fuel-bounded specialization of `linkVerifiedCalleeTableWithCallees` via
`wpMirNoCallBounded`.
-/
theorem linkVerifiedCalleeTableWithCalleesBounded
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
    (calleeTable : List CapturedMir)
    (calleeCallees : List CapturedMir)
    (calleeFuel : Nat)
    (fallback : ExternalCallHandler)
    (h_callee :
      ∀ (req : MirCallReq) (instBody : CapturedMir),
        lookupCallee calleeTable callerBody.layouts req.defPath req.typeArgs callerBody.traitImpls =
          .some instBody →
        C.pre req →
        wpMirNoCallBounded calleeFuel
          instBody
          (enterExternalCalleeState instBody req.args req.memory calleeCallees)
          (fun out => C.post req (outcomeToRestoredCallAns req.memory out)))
    (h_fallback :
      ∀ req : MirCallReq,
        lookupCallee calleeTable callerBody.layouts req.defPath req.typeArgs callerBody.traitImpls =
          .none →
        C.pre req →
        TreeSafe (fallback req) ∧
        ∀ tr ans, ReachesRet (fallback req) tr ans → C.post req ans) :
    (fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (linkCalleeTableWithCalleesHandler
          calleeTable callerBody.layouts calleeCallees fallback callerBody.traitImpls)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post :=
  linkVerifiedCalleeTableWithCallees
    h_caller calleeTable calleeCallees fallback
    (fun req instBody h_lk h_pre =>
      dwlp_cofix_of_wpCoalBounded (h_callee req instBody h_lk h_pre))
    h_fallback

/--
Idealized UB-exception call handler for a scoped `c : UbExceptionClaim`:
routes calls matching `c.body.defPath` to a deterministic specification witness
`excModel req.args req.memory` (isolating callers from the exempted callee's
internal `.fail .ub` outside `c.strictSafetyPre` while preserving the callee's
normal-return postcondition `c.post`).
-/
def ubExceptionModelHandler
    (c : UbExceptionClaim)
    (excModel : List Value → Memory → Value × Memory)
    (fallback : ExternalCallHandler) : ExternalCallHandler :=
  fun req =>
    if req.defPath = c.body.defPath then
      let out := excModel req.args req.memory
      .ret (.returned out.1 out.2)
    else
      fallback req

/--
Establish `c.callContract.holdsOn (ubExceptionModelHandler c excModel fallback)`
from a verified `UbExceptionVerificationResult c` and a postcondition-compliant
model witness `excModel`.
-/
theorem holdsOn_ubExceptionModelHandler
    {c : UbExceptionClaim}
    (h_callee : UbExceptionVerificationResult c)
    (excModel : List Value → Memory → Value × Memory)
    (fallback : ExternalCallHandler)
    (h_model :
      ∀ args mem,
        c.pre args mem →
        (∀ tr retVal mem',
          ReachesRet
            (mirStatefulTreeWithCallees c.body args mem c.callees)
            tr
            (.normal (retVal, mem')) →
          c.post args mem retVal mem') →
        c.post args mem (excModel args mem).1 (excModel args mem).2) :
    c.callContract.holdsOn (ubExceptionModelHandler c excModel fallback) := by
  intro req ⟨h_path, h_pre⟩
  simp only [ubExceptionModelHandler, h_path, ↓reduceIte]
  have h_dwlp :
      DWLP mirClosedWP
        (.ret (.returned (excModel req.args req.memory).1 (excModel req.args req.memory).2))
        (fun ans _ => c.callContract.post req ans)
        PUnit.unit :=
    DWLP.ret ⟨(excModel req.args req.memory).1, (excModel req.args req.memory).2,
      rfl, h_model req.args req.memory h_pre (h_callee.proof.2 req.args req.memory h_pre)⟩
  exact dwlp_pure_adequacy h_dwlp

/--
Horizontal caller–callee linking theorem with `callerCallees` for a scoped
UB-exception callee: links a caller verified via `ModularVerificationResult`
(with `callerCallees`) against `c.callContract.holdsOn` with a callee verified
via `UbExceptionVerificationResult c`.
-/
theorem linkUbExceptionCalleeWithCallees
    {c : UbExceptionClaim}
    {callerBody : CapturedMir}
    {callerCallees : List CapturedMir}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (h_caller :
      ModularVerificationResult
        { body := callerBody
          envAssumed := c.callContract.holdsOn
          pre := pre
          post := post
          callees := callerCallees })
    (h_callee : UbExceptionVerificationResult c)
    (excModel : List Value → Memory → Value × Memory)
    (fallback : ExternalCallHandler)
    (h_model :
      ∀ args mem,
        c.pre args mem →
        (∀ tr retVal mem',
          ReachesRet
            (mirStatefulTreeWithCallees c.body args mem c.callees)
            tr
            (.normal (retVal, mem')) →
          c.post args mem retVal mem') →
        c.post args mem (excModel args mem).1 (excModel args mem).2) :
    ((fun args mem =>
      (mirHandledTreeWithCallees callerBody args mem callerCallees
        (ubExceptionModelHandler c excModel fallback)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post) ∧
    MirStatefulContractHoldsWithSafetyAndCallees
      c.body
      c.callees
      (fun args mem => c.pre args mem ∧ c.strictSafetyPre args mem)
      c.pre
      c.post :=
  ⟨h_caller.proof
    (ubExceptionModelHandler c excModel fallback)
    (holdsOn_ubExceptionModelHandler h_callee excModel fallback h_model),
   h_callee.proof.1⟩

/--
Horizontal caller–callee linking theorem for a scoped UB-exception callee:
links a caller verified via `ModularVerificationResult` against
`c.callContract.holdsOn` with a callee verified via
`UbExceptionVerificationResult c`, certifying that:
1. The caller is `TreeSafe` and satisfies `post` across all `pre` under
   `ubExceptionModelHandler c excModel fallback`, and
2. The exempted callee itself is strictly `TreeSafe` on `c.pre ∧ c.strictSafetyPre`.
-/
theorem linkUbExceptionCallee
    {c : UbExceptionClaim}
    {callerBody : CapturedMir}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (h_caller :
      ModularVerificationResult
        { body := callerBody
          envAssumed := c.callContract.holdsOn
          pre := pre
          post := post })
    (h_callee : UbExceptionVerificationResult c)
    (excModel : List Value → Memory → Value × Memory)
    (fallback : ExternalCallHandler)
    (h_model :
      ∀ args mem,
        c.pre args mem →
        (∀ tr retVal mem',
          ReachesRet
            (mirStatefulTreeWithCallees c.body args mem c.callees)
            tr
            (.normal (retVal, mem')) →
          c.post args mem retVal mem') →
        c.post args mem (excModel args mem).1 (excModel args mem).2) :
    ((fun args mem =>
      (mirHandledTree callerBody args mem
        (ubExceptionModelHandler c excModel fallback)).toPartial) ≤
      MirClosedStatefulContractSpec pre pre post) ∧
    MirStatefulContractHoldsWithSafetyAndCallees
      c.body
      c.callees
      (fun args mem => c.pre args mem ∧ c.strictSafetyPre args mem)
      c.pre
      c.post :=
  linkUbExceptionCalleeWithCallees h_caller h_callee excModel fallback h_model

/-! ## 4. Program-to-Program Behavioral Equivalence & Whole-Crate Rollup -/

private theorem mirSilentWP_false
    (i : MirEffect.I) (Q : MirEffect.O i → PUnit → Prop) (u : PUnit) :
    ¬ mirSilentWP.wp i Q u := by
  cases i with
  | inl f => cases f; intro h; exact h
  | inr rest =>
    cases rest with
    | inl obs => cases obs; intro h; exact h
    | inr call => cases call; intro h; exact h

/--
Existence and uniqueness of deterministic silent evaluation under `DWP mirSilentWP`:
if `DWP mirSilentWP t (fun out _ => post out) PUnit.unit` holds, then `t` reaches
some unique `out₀` along empty trace `[]` satisfying `post out₀`, and every
`(tr, out)` with `ReachesRet t tr out` equals `([], out₀)`.
-/
theorem dwp_mirSilent_reachesRet
    {t : ITree MirEffect MirOutcome} {post : MirOutcome → Prop}
    (h_dwp : DWP mirSilentWP t (fun out _ => post out) PUnit.unit) :
    ∃ out₀,
      post out₀ ∧
      ReachesRet t [] out₀ ∧
      ∀ tr out, ReachesRet t tr out → tr = [] ∧ out = out₀ := by
  refine DWP.induct
    (fun x _ =>
      ∃ out₀,
        post out₀ ∧
        ReachesRet x [] out₀ ∧
        ∀ tr out, ReachesRet x tr out → tr = [] ∧ out = out₀)
    ?_ h_dwp
  intro x _ hx
  cases h_obs : x.observe with
  | ret out₀ =>
    simp only [h_obs] at hx
    refine ⟨out₀, hx, ⟨x, .refl x, h_obs⟩, ?_⟩
    rintro tr out ⟨u, h_reach, h_u⟩
    cases h_reach with
    | refl =>
      rw [h_obs] at h_u; injection h_u with h_eq; exact ⟨rfl, h_eq.symm⟩
    | tau ht => rw [h_obs] at ht; nomatch ht
    | vis hv => rw [h_obs] at hv; nomatch hv
  | tau x' =>
    simp only [h_obs] at hx
    rcases hx with ⟨out₀, h_post, ⟨u₀, h_r₀, h_u₀⟩, h_uniq⟩
    refine ⟨out₀, h_post, ⟨u₀, .tau h_obs h_r₀, h_u₀⟩, ?_⟩
    rintro tr out ⟨u, h_reach, h_u⟩
    cases h_reach with
    | refl => rw [h_obs] at h_u; nomatch h_u
    | tau ht hr' =>
      rw [h_obs] at ht; injection ht with h_x'
      subst h_x'
      exact h_uniq tr out ⟨u, hr', h_u⟩
    | vis hv => rw [h_obs] at hv; nomatch hv
  | vis i _ =>
    simp only [h_obs] at hx
    exact False.elim (mirSilentWP_false i _ _ hx)

/--
Lift `DWP mirNoCallWP` on a call-free interaction tree `t` (which may emit
internal `MirObsE` branch-tag observations) to `DWP mirSilentWP` on
`ITree.interp silenceMirObs t`.
-/
theorem dwp_mirSilent_silenceMirObs_of_dwp_noCall
    {t : ITree MirEffect MirOutcome} {post : MirOutcome → Prop}
    (h_dwp : DWP mirNoCallWP t (fun out _ => post out) PUnit.unit) :
    DWP mirSilentWP (ITree.interp silenceMirObs t)
      (fun out _ => post out) PUnit.unit := by
  refine DWP.induct
    (fun y _ =>
      DWP mirSilentWP (ITree.interp silenceMirObs y)
        (fun out _ => post out) PUnit.unit)
    ?_ h_dwp
  intro y _ hy
  cases h_obs : y.observe with
  | ret out =>
    simp only [h_obs] at hy
    have hEq : y = .ret out := by rw [← ITree.fold_observe y, h_obs]; rfl
    rw [hEq, interp_ret]
    exact DWP.ret hy
  | tau y' =>
    simp only [h_obs] at hy
    have hEq : y = .tau y' := by rw [← ITree.fold_observe y, h_obs]; rfl
    rw [hEq, interp_tau]
    exact DWP.tau hy
  | vis i k =>
    simp only [h_obs] at hy
    have hEq : y = .vis i k := by rw [← ITree.fold_observe y, h_obs]; rfl
    rw [hEq, interp_vis]
    cases i with
    | inl _ => exact False.elim hy
    | inr rest =>
      cases rest with
      | inr _ => exact False.elim hy
      | inl obsReq =>
        have h_bind :
            (silenceMirObs (.inr (.inl obsReq)) >>=
              fun o => (ITree.interp silenceMirObs (k o)).tau) =
            (ITree.interp silenceMirObs (k PUnit.unit)).tau :=
          ret_bind PUnit.unit (fun o => (ITree.interp silenceMirObs (k o)).tau)
        exact h_bind.symm ▸ DWP.tau (by cases obsReq; exact hy)

/--
Prove a `StatefulEquivVerificationResult c` from explicit `WeakRef` behavioral
refinement over `mirObsErasedStatefulTree` and `DWP mirDefaultWP` total
correctness on `c.implBody`.
-/
theorem verifyStatefulEquivByWeakRefAndTotal
    (c : StatefulEquivClaim)
    (h_ref :
      ∀ args mem,
        c.pre args mem →
        WeakRef
          (mirObsErasedStatefulTreeWithCallees c.implBody args mem c.implCallees)
          (mirObsErasedStatefulTreeWithCallees c.specBody args mem c.specCallees))
    (h_total :
      ∀ args mem,
        c.pre args mem →
        DWP mirDefaultWP
          (mirStatefulTreeWithCallees c.implBody args mem c.implCallees)
          (fun out _ =>
            ∃ retVal mem',
              out = .normal (retVal, mem') ∧ c.post args mem retVal mem')
          PUnit.unit) :
    StatefulEquivVerificationResult c :=
  ⟨⟨fun args mem h_pre => WeakRef.toPartial_le (h_ref args mem h_pre),
    (verifyTotalByDWP
      { body := c.implBody
        pre := c.pre
        post := c.post
        callees := c.implCallees }
      h_total).proof⟩⟩

/--
Relational pure-model equivalence bridge (`verifyStatefulEquivViaPureModel`):
if under `c.pre args mem` both candidate `c.implBody` (e.g., an `unsafe` fast
path) and reference specification `c.specBody` (e.g., a safe Rust baseline)
evaluate via `DWP mirNoCallWP` to the same deterministic `(retVal, mem') = model args mem`
and `c.post` holds on `(retVal, mem')`, then `c.implBody` both refines
`c.specBody` in the Smyth `Partial` order (`RefinesStatefulMir` across
CFG-changing optimizations) and satisfies total correctness (`TotalClaim.holds`),
yielding `StatefulEquivVerificationResult c`.
-/
theorem verifyStatefulEquivViaPureModel
    (c : StatefulEquivClaim)
    (model : List Value → Memory → Value × Memory)
    (h_impl :
      ∀ args mem,
        c.pre args mem →
        DWP mirNoCallWP
          (mirStatefulTreeWithCallees c.implBody args mem c.implCallees)
          (fun out _ =>
            out = .normal (model args mem) ∧
            c.post args mem (model args mem).1 (model args mem).2)
          PUnit.unit)
    (h_spec :
      ∀ args mem,
        c.pre args mem →
        DWP mirNoCallWP
          (mirStatefulTreeWithCallees c.specBody args mem c.specCallees)
          (fun out _ => out = .normal (model args mem))
          PUnit.unit) :
    StatefulEquivVerificationResult c := by
  refine ⟨⟨?_, ?_⟩⟩
  · intro args mem h_pre _h_spec_safe
    have hs_impl := dwp_mirSilent_silenceMirObs_of_dwp_noCall (h_impl args mem h_pre)
    have hs_spec := dwp_mirSilent_silenceMirObs_of_dwp_noCall (h_spec args mem h_pre)
    have h_adeq_impl := dwp_pure_adequacy hs_impl
    rcases dwp_mirSilent_reachesRet hs_impl with
      ⟨out_i, ⟨h_out_i, _⟩, _, h_uniq_i⟩
    rcases dwp_mirSilent_reachesRet hs_spec with
      ⟨out_s, h_out_s, h_reach_s, _⟩
    refine ⟨h_adeq_impl.1, ?_⟩
    rintro ⟨tr, out⟩ h_ret_i
    rcases h_uniq_i tr out h_ret_i with ⟨rfl, rfl⟩
    rw [h_out_i, ← h_out_s]
    exact h_reach_s
  · intro args mem h_pre
    have h_adeq := dwp_pure_adequacy (h_impl args mem h_pre)
    refine ⟨h_adeq.1, h_adeq.2.1, h_adeq.2.2.1, ?_⟩
    intro tr out h_ret
    rcases h_adeq.2.2.2 tr out h_ret with ⟨h_eq, h_post⟩
    exact ⟨(model args mem).1, (model args mem).2, h_eq, h_post⟩

/--
Fuel-bounded specialization of `verifyStatefulEquivViaPureModel` via
`wpMirNoCallBounded`.
-/
theorem verifyStatefulEquivMirBounded
    (c : StatefulEquivClaim)
    (implFuel specFuel : Nat)
    (model : List Value → Memory → Value × Memory)
    (h_impl :
      ∀ args mem,
        c.pre args mem →
        wpMirNoCallBounded implFuel c.implBody
          (initMachineStateWithMemoryAndCallees c.implBody args mem c.implCallees)
          (fun out =>
            out = .normal (model args mem) ∧
            c.post args mem (model args mem).1 (model args mem).2))
    (h_spec :
      ∀ args mem,
        c.pre args mem →
        wpMirNoCallBounded specFuel c.specBody
          (initMachineStateWithMemoryAndCallees c.specBody args mem c.specCallees)
          (fun out => out = .normal (model args mem))) :
    StatefulEquivVerificationResult c :=
  verifyStatefulEquivViaPureModel c model
    (fun args mem h_pre => dwp_cofix_of_wpCoalBounded implFuel (h_impl args mem h_pre))
    (fun args mem h_pre => dwp_cofix_of_wpCoalBounded specFuel (h_spec args mem h_pre))

/-- Assemble a whole-crate `CrateVerificationResult` rollup from its item proofs. -/
theorem verifyCrateRollup
    (c : CrateClaim)
    (h_nonempty : c.items ≠ [])
    (h_all : AllCrateItemsHold c.items) :
    CrateVerificationResult c :=
  ⟨⟨h_nonempty, h_all⟩⟩

end Anneal.Rustc.V2026_06_01.Lower
