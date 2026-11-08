import Trusted
import Anneal.MirLiftCore
import Mir.FxfsPlatformPager.layer_pager_read_unfixed
import Obligations.FxfsPlatformPager.layer_pager_read_unfixed
import Specs.FxfsPlatformPager.layer_pager_read_unfixed
import Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

namespace Proof.FxfsPlatformPager.layer_pager_read_unfixed

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-- Fuel-free modular step that may cross an external call. `h_step` shows that
the step meets the call contract and that every admitted call answer transitions
to `s'`, so convergence from `s'` yields convergence from `s`. -/
private theorem modularWpConverges_step_to {contract : MirCallContract}
    {body : CapturedMir} {s s' : MachineState} {post : MirOutcome → Prop}
    (h_step : ∀ {cont : MirExecState → Prop}, cont (.running s') →
      evalSymNodeTreeModular contract cont post (stepMirSymTree body s))
    (h_next : MirModularWpConverges contract body s' post) :
    MirModularWpConverges contract body s post :=
  let ⟨n, hn⟩ := h_next
  ⟨n + 1, h_step hn⟩

private def forceNat? : Nat → Option Nat
  | 0 => some 0
  | n + 1 => match forceNat? n with | some k => some (k + 1) | none => none

private theorem forceNat?_eq_some : ∀ n, forceNat? n = some n
  | 0 => rfl
  | n + 1 => by rw [forceNat?, forceNat?_eq_some n]

/-- Call-free step that normalizes `blockIdx`, `stmtIdx`, and `locals` so nested
`advanceStmt` and `List.set` terms do not accumulate across symbolic steps.
Forcing `blockIdx` and `stmtIdx` via `forceNat?` prevents `switchInt` from
unifying `?bb` with an unreduced `lookupSwitchTarget` term that retains the
prior frame. -/
private theorem modularStepNorm {contract : MirCallContract} {body : CapturedMir}
    {s : MachineState} {bb stmt : Nat} {locals : List LocalSlot}
    {post : MirOutcome → Prop}
    (h_step : evalSymNodeTreeNoCall
      (fun
        | .running s' =>
          s'.memory = emptyMemory ∧
          forceNat? s'.frame.blockIdx = some bb ∧
          forceNat? s'.frame.stmtIdx = some stmt ∧
          forcePureEnv? s'.frame.locals = some locals
        | _ => False) post (stepMirSymTree body s))
    (h_next : MirModularWpConverges contract body
      { frame := { blockIdx := bb, stmtIdx := stmt, locals := locals }
        memory := emptyMemory } post) :
    MirModularWpConverges contract body s post := by
  refine MirModularWpConverges.step
    (evalSymNodeTreeNoCall_mono ?_ (fun _ h => h) h_step)
  rintro ⟨⟨_, _, _⟩, _⟩ ⟨rfl, hb, hst, hloc⟩
  rw [forceNat?_eq_some] at hb hst
  rw [forcePureEnv?_eq_some] at hloc
  cases hb; cases hst; cases hloc
  exact h_next

theorem verified : ModularVerificationResult Obligations.FxfsPlatformPager.layer_pager_read_unfixed.modularClaim := by
  refine verifyModularContractMir_of_wpConverges _ _ _ _ ?_
  rintro _ _ ⟨ml, _, pb, ro, rl, h_ml, -, -, rfl | rfl, h_pb, rfl, rfl⟩
  · refine .of_noCall
      (mirNoCallWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, rfl, ?_⟩)
    rintro _ _ _ _ _ ⟨⟩
    simp
  · refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩
      (modularStepNorm ⟨rfl, rfl, rfl, rfl⟩ ?_)
    refine modularWpConverges_step_to (s' := ?s')
      (fun hc => ⟨⟨rfl, ml, pb, h_ml, h_pb, rfl, rfl⟩, ?h_ans⟩) ?h_next
    case h_ans =>
      rintro _ ⟨_, _, rfl, rfl, h_ret⟩
      obtain rfl := h_ret ml pb rfl
      exact hc
    case h_next =>
      refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩ (MirModularWpConverges.step ?_)
      show (match Nat.ble ro ml with | true => _ | false => _)
      cases h_le1 : Nat.ble ro ml
      · refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩
          (.of_noCall (mirNoCallWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, rfl, ?_⟩))
        rintro _ _ _ _ _ ⟨⟩
        simp [Nat.not_le.mpr (by simpa using h_le1)]
      · have h1 := Nat.le_of_ble_eq_true h_le1
        repeat refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩ ?_
        refine MirModularWpConverges.step ?_
        show (match Nat.ble ro ml with | true => _ | false => _)
        rw [h_le1]
        refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩ (MirModularWpConverges.step ?_)
        show (match Nat.ble rl (wrapScalarBits (ml - ro) 18446744073709551616) with
          | true => _ | false => _)
        rw [wrapScalarBits_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_ml)]
        cases h_le2 : Nat.ble rl (ml - ro) <;>
          (refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩
             (.of_noCall (mirNoCallWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, rfl, ?_⟩))
           rintro _ _ _ _ _ ⟨⟩)
        · simp [Nat.not_le.mpr (by simpa using h_le2)]
        · have h2 := Nat.le_of_ble_eq_true h_le2
          rw [ite_eq_left ⟨rfl, h1, h2⟩]
          change Value.aggregate 1 [.scalar ⟨wrapScalarBits (ro + rl) 18446744073709551616, 8⟩] = _
          rw [wrapScalarBits_of_lt
            (Nat.lt_of_le_of_lt (Nat.add_comm rl ro ▸ Nat.add_le_of_le_sub h1 h2) h_ml)]

/-- Model witness for `mapped_vmo_as_slice_unfixed` returning `mapped_len`. -/
def mappedVmoLenModel (args : List Value) (mem : Memory) : Value × Memory :=
  match args with
  | .scalar { bits := mapped_len, .. } :: _ =>
    (.scalar { bits := mapped_len, sizeBytes := 8 }, mem)
  | _ => (.scalar { bits := 0, sizeBytes := 8 }, mem)

/-- End-to-end horizontal linking theorem combining the modular proof of
    `layer_pager_read_unfixed` with the scoped UB-exception proof of
    `mapped_vmo_as_slice_unfixed`. -/
theorem linked_with_ub_exception (fallback : ExternalCallHandler) :
    ((fun args mem =>
      (mirHandledTree
        Mir.FxfsPlatformPager.layer_pager_read_unfixed.body
        args mem
        (ubExceptionModelHandler
          Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim
          mappedVmoLenModel
          fallback)).toPartial) ≤
      MirClosedStatefulContractSpec
        Specs.FxfsPlatformPager.layer_pager_read_unfixed.pre
        Specs.FxfsPlatformPager.layer_pager_read_unfixed.pre
        Specs.FxfsPlatformPager.layer_pager_read_unfixed.post) ∧
    MirStatefulContractHoldsWithSafety
      Mir.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.body
      (fun args mem =>
        Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.pre args mem ∧
        Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.strictSafetyPre args mem)
      Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.pre
      Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.post := by
  refine linkUbExceptionCallee
    verified
    Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.verified
    mappedVmoLenModel
    fallback
    ?_
  rintro _ _ ⟨_, _, _, _, rfl, rfl⟩ -
  exact ⟨rfl, by rintro _ _ ⟨⟩; rfl⟩

end Proof.FxfsPlatformPager.layer_pager_read_unfixed
