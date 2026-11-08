import Trusted
import Anneal.MirLiftCore
import Mir.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Obligations.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

namespace Proof.FxfsStorageBoundary.data_object_handle_verify_data_unfixed

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.FunctionalTranslation
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
  | n + 1 => (forceNat? n).map (· + 1)

private theorem forceNat?_eq_some : ∀ n, forceNat? n = some n
  | 0 => rfl
  | n + 1 => by simp [forceNat?, forceNat?_eq_some n]

/-- Call-free step that normalizes `blockIdx`, `stmtIdx`, and `locals` so nested
`advanceStmt` and `List.set` terms do not accumulate across symbolic steps. -/
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
  rintro (⟨⟨b, st, loc⟩, mem⟩ | _ | _)
  · rintro ⟨rfl, hb, hst, hloc⟩
    rw [forceNat?_eq_some] at hb hst
    rw [forcePureEnv?_eq_some] at hloc
    cases hb; cases hst; cases hloc
    exact h_next
  · exact False.elim
  · exact False.elim

theorem verified : ModularVerificationResult Obligations.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.modularClaim := by
  refine verifyModularContractMir_of_wpConverges _ _ _ _ ?_
  rintro _ _ ⟨vs, off, len, t, h_vs, -, -, h_t, rfl, rfl⟩
  repeat refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩ ?_
  refine MirModularWpConverges.step ?_
  show (match Nat.ble off vs with | true => _ | false => _)
  cases h_le1 : Nat.ble off vs
  · refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩ ?_
    refine MirModularWpConverges.of_noCall
      (mirNoCallWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, rfl, ?_⟩)
    rintro _ _ _ _ ⟨⟩
    rw [ite_eq_right fun h => by simp [Nat.ble_eq_true_of_le h.1] at h_le1]
  · have h1 := Nat.le_of_ble_eq_true h_le1
    repeat refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩ ?_
    refine MirModularWpConverges.step ?_
    show (match Nat.ble off vs with | true => _ | false => _)
    rw [h_le1]
    repeat refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩ ?_
    refine MirModularWpConverges.step ?_
    show (match Nat.ble len (wrapScalarBits (vs - off) 18446744073709551616) with
      | true => _ | false => _)
    rw [show wrapScalarBits (vs - off) 18446744073709551616 = vs - off by
      simp [wrapScalarBits,
        nat_ble_eq_false_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_vs)]]
    cases h_le2 : Nat.ble len (vs - off)
    · refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩ ?_
      refine MirModularWpConverges.of_noCall
        (mirNoCallWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, rfl, ?_⟩)
      rintro _ _ _ _ ⟨⟩
      rw [ite_eq_right fun h => by simp [Nat.ble_eq_true_of_le h.2] at h_le2]
    · have h2 := Nat.le_of_ble_eq_true h_le2
      repeat refine modularStepNorm ⟨rfl, rfl, rfl, rfl⟩ ?_
      refine modularWpConverges_step_to (s' := ?s')
        (fun hc => ⟨⟨rfl, vs, off, len, t, h1, h2, h_vs, h_t, rfl, rfl⟩, ?h_ans⟩) ?h_next
      case h_ans =>
        rintro _ ⟨_, _, rfl, rfl, h_ret⟩
        obtain rfl := h_ret vs off len t rfl
        exact hc
      case h_next =>
        refine MirModularWpConverges.of_noCall
          (mirNoCallWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, rfl, ?_⟩)
        rintro _ _ _ _ ⟨⟩
        rw [ite_eq_left ⟨h1, h2⟩]

/-- Model witness for `vmo_buffer_as_ref_unchecked` returning `offset + len`. -/
def vmoSliceEndModel (args : List Value) (mem : Memory) : Value × Memory :=
  match args with
  | [ _, .scalar { bits := offset, .. }, .scalar { bits := len, .. }, _ ] =>
    (.scalar { bits := offset + len, sizeBytes := 8 }, mem)
  | _ => (.scalar { bits := 0, sizeBytes := 8 }, mem)

/-- End-to-end horizontal linking theorem combining the modular proof of
    `data_object_handle_verify_data_unfixed` with the scoped UB-exception
    proof of `vmo_buffer_as_ref_unchecked`. -/
theorem linked_with_ub_exception (fallback : ExternalCallHandler) :
    ((fun args mem =>
      (mirHandledTree
        Mir.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.body
        args mem
        (ubExceptionModelHandler
          Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim
          vmoSliceEndModel
          fallback)).toPartial) ≤
      MirClosedStatefulContractSpec
        Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.pre
        Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.pre
        Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.post) ∧
    MirStatefulContractHoldsWithSafety
      Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
      (fun args mem =>
        Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.pre args mem ∧
        Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.strictSafetyPre args mem)
      Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.pre
      Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.post := by
  refine linkUbExceptionCallee
    verified
    Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.verified
    vmoSliceEndModel
    fallback
    ?_
  rintro _ _ ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩ -
  exact ⟨rfl, by rintro _ _ _ _ ⟨⟩; rfl⟩

end Proof.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
