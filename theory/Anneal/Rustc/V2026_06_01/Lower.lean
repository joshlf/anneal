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

/-- Fuel-bounded coalgebra stepping on `stepMirState body` under `mirDefaultWP`. -/
def wpMirBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpCoalBounded fuel mirDefaultWP (stepMirState body)
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
        DWLP mirDefaultWP (mirCallTree c.body args)
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
        wpMirBounded fuel c.body (initMachineState c.body args)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') → c.post args retVal)) :
    VerificationResult c :=
  verifyByDWLP c (fun args h_pre => dwlp_cofix_of_wpCoalBounded (h_wp args h_pre))

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
  (verifyByDWLP
    { body := specBody
      pre := (· = args)
      post := fun _ ret => ret = .scalar { bits := 1, sizeBytes := 1 } }
    (fun _ h_eq => h_eq ▸ h_dwp.toDWLP)).proof

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
  mirBoolPredicateHolds_of_dwp specBody args (dwp_cofix_of_wpCoalBounded fuel h_wp)

/-- Prove a stateful `StatefulVerificationResult c` from `DWLP mirDefaultWP`. -/
theorem verifyStatefulByDWLP
    (c : StatefulClaim)
    (h_dwlp :
      ∀ args mem,
        c.pre args mem →
        DWLP mirDefaultWP (mirStatefulTree c.body args mem)
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
        wpMirBounded fuel c.body (initMachineStateWithMemory c.body args mem)
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
        DWLP mirTraceWP (mirStatefulTree c.body args mem)
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
        wpMirTraceBounded fuel c.body (initMachineStateWithMemory c.body args mem)
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
        DWP mirDefaultWP (mirStatefulTree c.body args mem)
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
        wpMirBounded fuel c.body (initMachineStateWithMemory c.body args mem)
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
      { body, envAssumed := envSatisfiesContract C, pre, post } := by
  refine ⟨fun h h_env args mem h_pre => ?_⟩
  have h_interp :=
    dwlp_interp
      (handleMirExternalCalls h)
      (handleMirExternalCalls_links_modularWP C h h_env)
      (h_dwlp args mem h_pre)
  have h_adeq := dwlp_pure_adequacy h_interp
  exact ⟨h_adeq.1, fun outPair h_ret _ retVal mem' h_out =>
    h_adeq.2 outPair.1 outPair.2 h_ret retVal mem' h_out⟩

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
  verifyModularByDWLP C body pre post
    (fun args mem h_pre => dwlp_cofix_of_wpCoalBounded (h_wp args mem h_pre))

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
          (mirObsErasedStatefulTree c.implBody args mem)
          (mirObsErasedStatefulTree c.specBody args mem))
    (h_total :
      ∀ args mem,
        c.pre args mem →
        DWP mirDefaultWP (mirStatefulTree c.implBody args mem)
          (fun out _ =>
            ∃ retVal mem',
              out = .normal (retVal, mem') ∧ c.post args mem retVal mem')
          PUnit.unit) :
    StatefulEquivVerificationResult c :=
  ⟨⟨fun args mem h_pre => WeakRef.toPartial_le (h_ref args mem h_pre),
    (verifyTotalByDWP { body := c.implBody, pre := c.pre, post := c.post } h_total).proof⟩⟩

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
        DWP mirNoCallWP (mirStatefulTree c.implBody args mem)
          (fun out _ =>
            out = .normal (model args mem) ∧
            c.post args mem (model args mem).1 (model args mem).2)
          PUnit.unit)
    (h_spec :
      ∀ args mem,
        c.pre args mem →
        DWP mirNoCallWP (mirStatefulTree c.specBody args mem)
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
          (initMachineStateWithMemory c.implBody args mem)
          (fun out =>
            out = .normal (model args mem) ∧
            c.post args mem (model args mem).1 (model args mem).2))
    (h_spec :
      ∀ args mem,
        c.pre args mem →
        wpMirNoCallBounded specFuel c.specBody
          (initMachineStateWithMemory c.specBody args mem)
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
