import Trusted
import Anneal
import Mir.FxfsPlatformPager.layer_pager_read_unfixed
import Obligations.FxfsPlatformPager.layer_pager_read_unfixed
import Specs.FxfsPlatformPager.layer_pager_read_unfixed
import Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

namespace Proof.FxfsPlatformPager.layer_pager_read_unfixed

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

/-- Arguments `(mapped_len, ptr_non_null, pager_backed, read_offset,
read_len)`. -/
private abbrev argVals (ml pnn pb ro rl : Nat) : List Value :=
  [.scalar ⟨ml, 8⟩, .scalar ⟨pnn, 1⟩, .scalar ⟨pb, 1⟩, .scalar ⟨ro, 8⟩, .scalar ⟨rl, 8⟩]

/-- From bb5's `_8 = Sub(copy _6, copy _4)` with
`read_offset ≤ mapped_len`: the function returns
`Some(read_offset + read_len)` exactly when
`read_len ≤ mapped_len - read_offset`. -/
private theorem bb5_converges (ml pb ro rl : Nat) (h_ml : ml < 18446744073709551616)
    (h1 : ro ≤ ml) :
    MirModularWpConverges
      Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim.callContract
      Mir.FxfsPlatformPager.layer_pager_read_unfixed.body
      (stateAt 5 2
        [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨ro, 8⟩),
         .init (.scalar ⟨rl, 8⟩), .init (.scalar ⟨ml, 8⟩), .dead, .uninit, .dead, .dead])
      (mirSafePost (Specs.FxfsPlatformPager.layer_pager_read_unfixed.post
        (argVals ml 1 pb ro rl) emptyMemory)) := by
  -- `read_offset ≤ mapped_len` selects the non-wrapping arm of the
  -- subtraction.
  refine MirModularWpConverges.step ?_
  show (match Nat.ble ro ml with | true => _ | false => _)
  rw [Nat.ble_eq_true_of_le h1]
  -- `StorageLive(_9); _9 = Gt(copy _5, copy _8)` branches on
  -- `read_len ≤ mapped_len - read_offset`.
  repeat refine MirModularWpConverges.step ?_
  show (match Nat.ble rl (wrapScalarBits (ml - ro) 18446744073709551616) with
    | true => _ | false => _)
  rw [wrapScalarBits_eq_of_lt (by omega)]
  cases h_le2 : Nat.ble rl (ml - ro)
  · -- `read_len > mapped_len - read_offset`: bb6 returns `None` through bb8.
    repeat refine MirModularWpConverges.step ?_
    refine ⟨rfl, ?_⟩
    rintro _ _ _ _ _ ⟨⟩
    have h_gt := Nat.not_le_of_not_ble_eq_true (Bool.ne_true_of_eq_false h_le2)
    rw [ite_eq_right (by omega)]
  · -- bb7: `_10 = Add(copy _4, copy _5); _0 = Option::<usize>::Some(copy _10)`;
    -- bb9: `return`.
    have h2 := Nat.le_of_ble_eq_true h_le2
    repeat refine MirModularWpConverges.step ?_
    refine ⟨rfl, ?_⟩
    rintro _ _ _ _ _ ⟨⟩
    rw [ite_eq_left ⟨rfl, h1, h2⟩]
    -- `read_offset + read_len ≤ mapped_len < 2^64`, so `Add` does not wrap.
    show Value.aggregate 1 [.scalar ⟨wrapScalarBits (ro + rl) 18446744073709551616, 8⟩] = _
    rw [wrapScalarBits_eq_of_lt (by omega)]

/-- From bb3's entry, after the call returned `mapped_len` in `_6`. -/
private theorem bb3_converges (ml pb ro rl : Nat) (h_ml : ml < 18446744073709551616) :
    MirModularWpConverges
      Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim.callContract
      Mir.FxfsPlatformPager.layer_pager_read_unfixed.body
      (stateAt 3 0
        [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨ro, 8⟩),
         .init (.scalar ⟨rl, 8⟩), .init (.scalar ⟨ml, 8⟩), .dead, .dead, .dead, .dead])
      (mirSafePost (Specs.FxfsPlatformPager.layer_pager_read_unfixed.post
        (argVals ml 1 pb ro rl) emptyMemory)) := by
  -- bb3: `StorageLive(_7); _7 = Gt(copy _4, copy _6)` branches on
  -- `read_offset ≤ mapped_len`.
  repeat refine MirModularWpConverges.step ?_
  show (match Nat.ble ro ml with | true => _ | false => _)
  cases h_le1 : Nat.ble ro ml
  · -- `read_offset > mapped_len`: bb4 returns `None` through bb8.
    repeat refine MirModularWpConverges.step ?_
    refine ⟨rfl, ?_⟩
    rintro _ _ _ _ _ ⟨⟩
    have h_gt := Nat.not_le_of_not_ble_eq_true (Bool.ne_true_of_eq_false h_le1)
    rw [ite_eq_right (by omega)]
  · -- `switchInt(move _7)` jumps to bb5: `StorageDead(_7); StorageLive(_8)`.
    repeat (refine MirModularWpConverges.step ?_; change MirModularWpConverges _ _ _ _)
    exact bb5_converges ml pb ro rl h_ml (Nat.le_of_ble_eq_true h_le1)

theorem verified : ModularVerificationResult Obligations.FxfsPlatformPager.layer_pager_read_unfixed.modularClaim := by
  refine verifyModularContractMir_of_wpConverges _ _ _ _ ?_
  rintro _ _ ⟨ml, pnn, pb, ro, rl, h_ml, -, -, h_pnn, h_pb, rfl, rfl⟩
  rcases h_pnn with rfl | rfl
  · -- `ptr_non_null = false`: bb0 jumps to bb1, which returns `None`.
    repeat refine MirModularWpConverges.step ?_
    refine ⟨rfl, ?_⟩
    rintro _ _ _ _ _ ⟨⟩
    rw [ite_eq_right (by omega)]
  · -- bb0 jumps to bb2: `StorageLive(_6)`, then the call
    -- `_6 = mapped_vmo_as_slice_unfixed(move _1, move _2, move _3)`. Step only
    -- while the next state is running, which stops at the call.
    repeat (refine MirModularWpConverges.step ?_; change MirModularWpConverges _ _ _ _)
    -- The call meets the callee's contract, and every answer the contract
    -- admits returns `mapped_len` with memory untouched.
    refine modularWpConverges_step_to (s' := ?s')
      (fun hc => ⟨⟨rfl, ml, pb, h_ml, h_pb, rfl, rfl⟩, ?h_ans⟩) ?h_next
    case h_ans =>
      rintro _ ⟨_, _, rfl, rfl, h_ret⟩
      obtain rfl := h_ret ml pb rfl
      exact hc
    case h_next => exact bb3_converges ml pb ro rl h_ml

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
  intro args mem h_pre _
  rcases h_pre with ⟨mapped_len, pb, _, _, rfl, rfl⟩
  refine ⟨rfl, ?_⟩
  intro ml' pb' h_args
  injection h_args with h1 _

end Proof.FxfsPlatformPager.layer_pager_read_unfixed
