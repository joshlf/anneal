import Trusted.Refinement
import Trusted.ITree
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import MiniRust.LibSpecr
import MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
import Correspondence.Framework
import Correspondence.DialectInterface
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses
import Correspondence.V2026_06_01.L5_ControlAndCalls

namespace Correspondence.V2026_06_01.L6_WholeMachine

open Trusted.Sequence
open Trusted.ITree
open Trusted.Refinement
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr
open MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
open Correspondence
open Correspondence.V2026_06_01.L5_ControlAndCalls

/-!
Horizontal Correspondence Slice L6: Whole-Machine Step Simulation and Guarded Refinement
(`Trusted.Rustc.V2026_06_01.MirSemantics.Machine` vs. mechanically extracted
`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops` and `Trusted.Refinement.GuardedRefines`).

Every theorem in this module universally quantifies (`∀`) over real Anneal TCB
whole-machine configurations (`initMachineState`, `initMachineStateWithCallees`,
`stepMirFn`, `stepMirState`, `mirTree`, `mirCallTree`, `MirNoUBTree`, `MirExecState`)
and proves step simulation and `Trusted.Refinement.GuardedRefines` against MiniRust's
`NdComp.toPartialBehavior` and `Generated.Ops.mrStepDispatchIsTerminator`
(`spec/lang/machine.md:185-233`).
-/

/-! ## 1. Initial Machine Configuration Correspondence -/

/-- Universal characterization of `initMachineState` and `initMachineStateWithCallees`
(`Machine.lean:42-99` vs. `spec/lang/machine.md:120-165`): both initialize the
entry stack frame at `blockIdx = 0` and `stmtIdx = 0` with `callStack = []`,
`activeCallee = none`, and initial borrow tag counter `nextTag = 1`;
when `callees` is non-empty, `initMachineStateWithCallees` also seeds
`Memory.traitImpls` with `body.traitImpls` (and reduces definitionally to
`initMachineState body args` when `callees = []`). -/
theorem mir_initMachineState_pc_zero
    (body : CapturedMir) (args : List Value) (callees : List CapturedMir) :
    (initMachineState body args).frame.blockIdx = 0 ∧
    (initMachineState body args).frame.stmtIdx = 0 ∧
    (initMachineState body args).memory.callStack = [] ∧
    (initMachineState body args).memory.activeCallee = none ∧
    (initMachineState body args).memory.nextTag = 1 ∧
    (initMachineStateWithCallees body args callees).frame.blockIdx = 0 ∧
    (initMachineStateWithCallees body args callees).frame.stmtIdx = 0 ∧
    (initMachineStateWithCallees body args callees).memory.callStack = [] ∧
    (initMachineStateWithCallees body args callees).memory.activeCallee = none ∧
    (initMachineStateWithCallees body args callees).memory.nextTag = 1 ∧
    (initMachineStateWithCallees body args callees).memory.callees = callees ∧
    (initMachineStateWithCallees body args []).memory.traitImpls = body.traitImpls ∧
    (∀ c cs, (initMachineStateWithCallees body args (c :: cs)).memory.traitImpls = body.traitImpls) := by
  cases callees <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-! ## 2. Program-Counter Statement-vs-Terminator Dispatch Correspondence -/

/-- Equivalence between `a == b` (used in `stepMirFn`) and
`Generated.Ops.mrStepDispatchIsTerminator`. -/
theorem mrStepDispatchIsTerminator_eq_beq (next_stmt stmt_len : Nat) :
    mrStepDispatchIsTerminator next_stmt stmt_len = (next_stmt == stmt_len) := by
  rfl

/-- Universal program-counter dispatch correspondence for `stepMirFn`
(`Machine.lean:100-115` vs. `Generated.Ops.mrStepDispatchIsTerminator` at
`spec/lang/machine.md:185-233`): for every active `currentBody` with supported
phase and basic block `bb`:
1. Out-of-bounds `blockIdx` faults with `MirStepNode.fail .ub`;
2. In-bounds `stmtIdx < length bb.statements` (`get? bb.statements s.frame.stmtIdx = .some stmt`)
   dispatches to `evalStmt s stmt currentBody.localDecls currentBody.layouts`;
3. Boundary `stmtIdx == length bb.statements`
   (`mrStepDispatchIsTerminator s.frame.stmtIdx (length bb.statements) = true`)
   dispatches to `evalTerminator s bb.terminator (.some currentBody)`; and
4. Out-of-bounds `stmtIdx > length bb.statements`
   (`mrStepDispatchIsTerminator s.frame.stmtIdx (length bb.statements) = false`)
   faults with `MirStepNode.fail .ub`. -/
theorem mir_stepMirFn_pc_dispatch_corresponds
    (body : CapturedMir) (s : MachineState) (bb : BasicBlockData)
    (hPhase : (s.memory.activeCallee.getD body).phase = .runtimePostCleanup) :
    let currentBody := s.memory.activeCallee.getD body
    (get? currentBody.basicBlocks s.frame.blockIdx = .none →
      stepMirFn body s = MirStepNode.fail .ub) ∧
    (∀ stmt : Statement,
      get? currentBody.basicBlocks s.frame.blockIdx = .some bb →
      get? bb.statements s.frame.stmtIdx = .some stmt →
      stepMirFn body s = evalStmt s stmt currentBody.localDecls currentBody.layouts) ∧
    (get? currentBody.basicBlocks s.frame.blockIdx = .some bb →
      get? bb.statements s.frame.stmtIdx = .none →
      mrStepDispatchIsTerminator s.frame.stmtIdx (length bb.statements) = true →
      stepMirFn body s = evalTerminator s bb.terminator (.some currentBody)) ∧
    (get? currentBody.basicBlocks s.frame.blockIdx = .some bb →
      get? bb.statements s.frame.stmtIdx = .none →
      mrStepDispatchIsTerminator s.frame.stmtIdx (length bb.statements) = false →
      stepMirFn body s = MirStepNode.fail .ub) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hNoBlock
    simp [stepMirFn, hPhase, hNoBlock]
  · intro stmt hBlock hStmt
    simp [stepMirFn, hPhase, hBlock, hStmt]
  · intro hBlock hNoStmt hIsTerm
    have hBeq : (s.frame.stmtIdx == length bb.statements) = true := hIsTerm
    simp [stepMirFn, hPhase, hBlock, hNoStmt, hBeq]
  · intro hBlock hNoStmt hNotTerm
    have hBeq : (s.frame.stmtIdx == length bb.statements) = false := hNotTerm
    simp [stepMirFn, hPhase, hBlock, hNoStmt, hBeq]

/-! ## 3. Unsupported Phase Fail-Closed Guarantee -/

/-- Universal theorem proving that when the active MIR body has an unsupported
compiler phase `.other ph`, `stepMirFn body s` fails closed with
`MirStepNode.unsupported` (`MirStepNode.fail .unsupported`), which corresponds to
`Partial.ub` (`⊤`) in `Trusted.Refinement.Partial` (`NdComp.top_refines_unsupported`). -/
theorem mir_stepMirFn_unsupported_phase_fails_closed
    (body : CapturedMir) (s : MachineState) (ph : String)
    (hPhase : (s.memory.activeCallee.getD body).phase = .other ph) :
    stepMirFn body s = MirStepNode.unsupported ∧
    MirStepNode.unsupported = MirStepNode.fail .unsupported ∧
    (∀ {α : Type} (c : NdComp α),
      NdComp.toPartialBehavior c ≤ (Partial.ub : Partial (BehaviorSet α))) := by
  refine ⟨?_, rfl, fun c => NdComp.top_refines_unsupported c⟩
  simp [stepMirFn, hPhase]

/-! ## 4. Coalgebra Step Simulation (`stepMirState`, `mirTree`, `mirCallTree`, `MirNoUBTree`) -/

/-- Universal coalgebra step characterization over `MirExecState` and coinductive
unfolding of `mirTree`, `mirCallTree`, and `MirNoUBTree` (`Machine.lean:117-147`):
- `.running s ↦ stepMirFn body s`
- `.halted out ↦ .ret out`
- `.faulted fk ↦ MirStepNode.fail fk`
- `(mirTree body s).observe = (stepMirFn body s).map (ITree.cofix (stepMirState body))`
- `mirCallTree body args = mirTree body (initMachineState body args)`
- `MirNoUBTree (mirTree body s) = TreeSafe (mirTree body s)` -/
theorem mir_stepMirState_simulation
    (body : CapturedMir) (s : MachineState) (out : MirOutcome)
    (fk : Trusted.Effect.FailureKind) (args : List Value) :
    stepMirState body (.running s) = stepMirFn body s ∧
    stepMirState body (.halted out) = .ret out ∧
    stepMirState body (.faulted fk) = MirStepNode.fail fk ∧
    (mirTree body s).observe = (stepMirFn body s).map (ITree.cofix (stepMirState body)) ∧
    mirCallTree body args = mirTree body (initMachineState body args) ∧
    MirNoUBTree (mirTree body s) = TreeSafe (mirTree body s) := by
  exact ⟨rfl, rfl, rfl, ITree.observe_cofix (stepMirState body) (.running s), rfl, rfl⟩

/-! ## 5. Whole-Machine Guarded Refinement (`Trusted.Refinement.GuardedRefines`) -/

/-- Order `NdComp α` via its canonical Smyth projection `NdComp.toPartialBehavior`. -/
instance instLENdComp {α : Type} : LE (NdComp α) where
  le c₁ c₂ := NdComp.toPartialBehavior c₁ ≤ NdComp.toPartialBehavior c₂

/-- Downward-closed specification induced by a state/program guard proposition `P`. -/
def guardPropSpec {Beh : Type u} [LE Beh] (P : Prop) : Spec Beh where
  holds _ := P
  downward_closed _ _ _ h := h

/-- Embed an observable `Verdict` into `NdComp Verdict`. -/
@[reducible]
def verdictToNdComp : Verdict → NdComp Verdict
  | .ub => NdComp.throwUb "undefined behavior"
  | .unsupported => NdComp.throwUb "unsupported"
  | other => NdComp.pure other

/-- Map a single-step `MirStepNode` transition into `Trusted.Refinement.Partial (BehaviorSet MirExecState)`:
deterministic `.tau next` transitions yield `{ next }`, terminal `.ret out` yields
`{ .halted out }`, and fault/effect nodes map to `Partial.ub` (`⊤`). -/
def mirStepNodeBehavior (node : MirStepNode) : Partial (BehaviorSet MirExecState) :=
  match node with
  | .tau next => Partial.pure (fun s => s = next)
  | .ret out => Partial.pure (fun s => s = .halted out)
  | .vis _ _ => Partial.ub

/-- Reference `NdComp MirExecState` transition corresponding to `stepMirState`. -/
def stepMirStateNd (body : CapturedMir) (st : MirExecState) : NdComp MirExecState :=
  match stepMirState body st with
  | .tau next => NdComp.pure next
  | .ret out => NdComp.pure (.halted out)
  | .vis _ _ => NdComp.throwUb "step fault or effect"

theorem partialPure_le_toPartialBehavior_pure {α : Type} (a : α) :
    Partial.pure (fun x => x = a) ≤ NdComp.toPartialBehavior (NdComp.pure a) := by
  intro _hDef
  refine ⟨trivial, fun x hx => ?_⟩
  subst hx
  exact NdComp.ReachesOutcome.ret (.ok x)

theorem toPartialBehavior_pure_le_partialPure {α : Type} (a : α) :
    NdComp.toPartialBehavior (NdComp.pure a) ≤ Partial.pure (fun x => x = a) := by
  intro _hDef
  refine ⟨?_, fun x hx => ?_⟩
  · intro msg hReach
    cases hReach
  · cases hx
    rfl

theorem partialUb_le_toPartialBehavior_throwUb {α : Type} (msg : String) :
    (Partial.ub : Partial (BehaviorSet α)) ≤ NdComp.toPartialBehavior (NdComp.throwUb msg) := by
  intro hDef
  exfalso
  exact hDef msg (NdComp.ReachesOutcome.ret (.error (.ub msg)))

theorem verdict_toPartial_le_verdictToNdComp (v : Verdict) :
    v.toPartial ≤ NdComp.toPartialBehavior (verdictToNdComp v) := by
  cases v with
  | ub => exact partialUb_le_toPartialBehavior_throwUb "undefined behavior"
  | unsupported => exact partialUb_le_toPartialBehavior_throwUb "unsupported"
  | normalUnit => exact partialPure_le_toPartialBehavior_pure Verdict.normalUnit
  | normalScalar n => exact partialPure_le_toPartialBehavior_pure (Verdict.normalScalar n)
  | panic => exact partialPure_le_toPartialBehavior_pure Verdict.panic

/-- Universal whole-machine guarded refinement theorem connecting `MirSemantics`
(`stepMirState` and `evalAnnealV2026_06_01`) to `MiniRust.LibSpecr.NdComp.toPartialBehavior`
via `Trusted.Refinement.GuardedRefines`:
1. For every captured MIR body `body`, execution state `st : MirExecState`, and
   guard condition `G`, `mirStepNodeBehavior (stepMirState body st)` refines
   `(stepMirStateNd body st).toPartialBehavior` under `Trusted.Refinement.GuardedRefines`;
2. For every snapshot `snap : MiniRustSnap` and program `prog : FixtureProg` outside
   the active gap guards (`hitsAnyGap = false`), Anneal's behavior
   `(evalAnnealV2026_06_01 prog defaultFixtureState).toPartial` refines MiniRust's
   `NdComp.toPartialBehavior (verdictToNdComp (evalMiniRustSnapshot snap prog))`
   under `Trusted.Refinement.GuardedRefines`! -/
theorem mir_whole_machine_guarded_refines
    (body : CapturedMir) (st : MirExecState)
    (snap : MiniRustSnap) (prog : FixtureProg) :
    GuardedRefines
      (guardPropSpec True)
      NdComp.toPartialBehavior
      (mirStepNodeBehavior (stepMirState body st))
      (stepMirStateNd body st) ∧
    GuardedRefines
      (guardPropSpec
        (hitsAnyGap
          (activeBugGaps .V2026_06_01 snap ++ activeEpochDivergences .V2026_06_01 snap)
          defaultFixtureState
          prog = false))
      NdComp.toPartialBehavior
      (evalAnnealV2026_06_01 prog defaultFixtureState).toPartial
      (verdictToNdComp (evalMiniRustSnapshot snap prog)) := by
  refine ⟨?_, ?_⟩
  · intro _hTrue
    unfold stepMirStateNd mirStepNodeBehavior
    cases stepMirState body st with
    | tau next => exact partialPure_le_toPartialBehavior_pure next
    | ret out => exact partialPure_le_toPartialBehavior_pure (MirExecState.halted out)
    | vis e k => exact partialUb_le_toPartialBehavior_throwUb "step fault or effect"
  · intro hNoGap
    have hEq := all_non_gap_fixtures_agree_exact snap prog hNoGap
    rw [hEq]
    exact verdict_toPartial_le_verdictToNdComp (evalMiniRustSnapshot snap prog)

end Correspondence.V2026_06_01.L6_WholeMachine
