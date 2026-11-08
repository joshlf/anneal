import Trusted
import Anneal
import Mir.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Obligations.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

namespace Proof.FxfsStorageBoundary.data_object_handle_verify_data_unfixed

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-- Fuel-free modular step that may cross an external call. `h_step` says
that the step from `s` satisfies every continuation that holds of `s'`: the
step meets the call contract, and its only successor (for every call answer
the contract admits) is `s'`. Convergence from `s'` then gives convergence from
`s`. -/
private theorem modularWpConverges_step_to {contract : MirCallContract}
    {body : CapturedMir} {s s' : MachineState} {post : MirOutcome → Prop}
    (h_step : ∀ {cont : MirExecState → Prop}, cont (.running s') →
      evalSymNodeTreeModular contract cont post (stepMirSymTree body s))
    (h_next : MirModularWpConverges contract body s' post) :
    MirModularWpConverges contract body s post :=
  let ⟨n, hn⟩ := h_next
  ⟨n + 1, h_step hn⟩

/-- Machine state at statement `stmt` of block `bb` with memory untouched.
Stepping symbolically from one of these explicit states keeps each proof term
small. -/
private def stateAt (bb stmt : Nat) (locals : List LocalSlot) : MachineState :=
  { frame := { blockIdx := bb, stmtIdx := stmt, locals := locals }
    memory := emptyMemory }

/-- Arguments `(vmo_size, offset, len, trusted)`. -/
private abbrev argVals (vs off len t : Nat) : List Value :=
  [.scalar ⟨vs, 8⟩, .scalar ⟨off, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨t, 1⟩]

/-- From bb4's call `_8 = vmo_buffer_as_ref_unchecked(move _1, move _2,
move _3, move _4)` with the range in bounds: the call meets the callee's
contract, every answer the contract admits returns `offset + len` with memory
untouched, and bb5 returns `Some(offset + len)`. -/
private theorem call_converges (vs off len t : Nat) (s6 : LocalSlot)
    (h_vs : vs < 18446744073709551616) (h_t : t = 0 ∨ t = 1)
    (h1 : off ≤ vs) (h2 : len ≤ vs - off) :
    MirModularWpConverges
      Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim.callContract
      Mir.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.body
      (stateAt 4 2
        [.uninit, .init (.scalar ⟨vs, 8⟩), .init (.scalar ⟨off, 8⟩),
         .init (.scalar ⟨len, 8⟩), .init (.scalar ⟨t, 1⟩), .dead, s6, .dead, .uninit])
      (mirSafePost (Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.post
        (argVals vs off len t) emptyMemory)) := by
  refine modularWpConverges_step_to (s' := ?s')
    (fun hc => ⟨⟨rfl, vs, off, len, t, h1, h2, h_vs, h_t, rfl, rfl⟩, ?h_ans⟩) ?h_next
  case h_ans =>
    rintro _ ⟨_, _, rfl, rfl, h_ret⟩
    obtain rfl := h_ret vs off len t rfl
    exact hc
  case h_next =>
    -- bb5: `_0 = Option::<usize>::Some(copy _8); goto -> bb6`; bb6: `return`
    repeat refine MirModularWpConverges.step ?_
    refine ⟨rfl, ?_⟩
    rintro _ _ _ _ ⟨⟩
    rw [ite_eq_left ⟨h1, h2⟩]

/-- From bb2's `_6 = Sub(copy _1, copy _2)` with `offset ≤ vmo_size`. -/
private theorem bb2_converges (vs off len t : Nat)
    (h_vs : vs < 18446744073709551616) (h_t : t = 0 ∨ t = 1) (h1 : off ≤ vs) :
    MirModularWpConverges
      Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim.callContract
      Mir.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.body
      (stateAt 2 2
        [.uninit, .init (.scalar ⟨vs, 8⟩), .init (.scalar ⟨off, 8⟩),
         .init (.scalar ⟨len, 8⟩), .init (.scalar ⟨t, 1⟩), .dead, .uninit, .dead, .dead])
      (mirSafePost (Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.post
        (argVals vs off len t) emptyMemory)) := by
  -- `offset ≤ vmo_size` selects the non-wrapping arm of the subtraction.
  refine MirModularWpConverges.step ?_
  show (match Nat.ble off vs with | true => _ | false => _)
  rw [Nat.ble_eq_true_of_le h1]
  -- `StorageLive(_7); _7 = Gt(copy _3, copy _6)` branches on
  -- `len ≤ vmo_size - offset`.
  repeat refine MirModularWpConverges.step ?_
  show (match Nat.ble len (wrapScalarBits (vs - off) 18446744073709551616) with
    | true => _ | false => _)
  rw [wrapScalarBits_eq_of_lt (by omega)]
  cases h_le2 : Nat.ble len (vs - off)
  · -- `len > vmo_size - offset`: bb3 returns `None`.
    repeat refine MirModularWpConverges.step ?_
    refine ⟨rfl, ?_⟩
    rintro _ _ _ _ ⟨⟩
    have h_gt := Nat.not_le_of_not_ble_eq_true (Bool.ne_true_of_eq_false h_le2)
    rw [ite_eq_right (by omega)]
  · -- bb4: `StorageDead(_7); StorageLive(_8)`, then the call. Step only
    -- while the next state is running, which stops at the call.
    repeat (refine MirModularWpConverges.step ?_; change MirModularWpConverges _ _ _ _)
    exact call_converges vs off len t _ h_vs h_t h1 (Nat.le_of_ble_eq_true h_le2)

theorem verified : ModularVerificationResult Obligations.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.modularClaim := by
  refine verifyModularContractMir_of_wpConverges _ _ _ _ ?_
  rintro _ _ ⟨vs, off, len, t, h_vs, -, -, h_t, rfl, rfl⟩
  -- bb0: `StorageLive(_5); _5 = Gt(copy _2, copy _1)` branches on
  -- `offset ≤ vmo_size`.
  repeat refine MirModularWpConverges.step ?_
  show (match Nat.ble off vs with | true => _ | false => _)
  cases h_le1 : Nat.ble off vs
  · -- `offset > vmo_size`: bb1 returns `None`.
    repeat refine MirModularWpConverges.step ?_
    refine ⟨rfl, ?_⟩
    rintro _ _ _ _ ⟨⟩
    have h_gt := Nat.not_le_of_not_ble_eq_true (Bool.ne_true_of_eq_false h_le1)
    rw [ite_eq_right (by omega)]
  · -- `switchInt(move _5)` jumps to bb2: `StorageDead(_5); StorageLive(_6)`.
    repeat (refine MirModularWpConverges.step ?_; change MirModularWpConverges _ _ _ _)
    exact bb2_converges vs off len t h_vs h_t (Nat.le_of_ble_eq_true h_le1)

/-- Model witness for `vmo_buffer_as_ref_unchecked` returning `offset + len`. -/
def vmoSliceEndModel (args : List Value) (mem : Memory) : Value × Memory :=
  match args with
  | [ _, .scalar { bits := offset, .. }, .scalar { bits := len, .. }, _ ] =>
    (.scalar { bits := offset + len, sizeBytes := 8 }, mem)
  | _ => (.scalar { bits := 0, sizeBytes := 8 }, mem)

/-- End-to-end horizontal linking theorem combining the modular proof of
    `data_object_handle_verify_data_unfixed` with the scoped UB-exception proof of
    `vmo_buffer_as_ref_unchecked`. -/
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
  intro args mem h_pre _
  rcases h_pre with ⟨vmo_size, offset, len, t, _, _, _, _, rfl, rfl⟩
  refine ⟨rfl, ?_⟩
  intro vs' off' l' t' h_args
  injection h_args with h1 ht1
  injection ht1 with h2 ht2
  injection ht2 with h3 _
  injection h2 with hs2
  injection h3 with hs3
  cases hs2; cases hs3
  rfl

end Proof.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
