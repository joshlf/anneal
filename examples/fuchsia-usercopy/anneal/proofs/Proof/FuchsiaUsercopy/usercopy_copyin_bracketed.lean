import Trusted
import Anneal
import Mir.FuchsiaUsercopy.usercopy_copyin_bracketed
import Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed
import Specs.FuchsiaUsercopy.usercopy_copyin_bracketed
import Proof.FuchsiaUsercopy.hermetic_copy_stub

namespace Proof.FuchsiaUsercopy.usercopy_copyin_bracketed

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-- `evalSymNodeTreeModular` is monotone in its continuation. -/
private theorem evalSymNodeTreeModular_mono {contract : MirCallContract}
    {c₁ c₂ : MirExecState → Prop} {post : MirOutcome → Prop}
    (h : ∀ st, c₁ st → c₂ st) :
    ∀ t, evalSymNodeTreeModular contract c₁ post t →
      evalSymNodeTreeModular contract c₂ post t
  | .leaf (.ret _), hp => hp
  | .leaf (.tau _), hp => h _ hp
  | .leaf (.vis (.inl _) _), hp => hp
  | .leaf (.vis (.inr (.inl _)) _), hp => h _ hp
  | .leaf (.vis (.inr (.inr (.call _))) _), hp => ⟨hp.1, fun ans ha => h _ (hp.2 ans ha)⟩
  | .branch true t _, hp => evalSymNodeTreeModular_mono h t hp
  | .branch false _ t, hp => evalSymNodeTreeModular_mono h t hp

/-- Fuel-free modular step that may cross an external call: when the step
from `s` satisfies the call contract and every successor it admits (including
every contract-admitted call answer) is `s'`, convergence from `s'` gives
convergence from `s`. -/
private theorem modularWpConverges_step_to {contract : MirCallContract}
    {body : CapturedMir} {s s' : MachineState} {post : MirOutcome → Prop}
    (h_step : evalSymNodeTreeModular contract (fun st => st = .running s') post
      (stepMirSymTree body s))
    (h_next : MirModularWpConverges contract body s' post) :
    MirModularWpConverges contract body s post := by
  obtain ⟨n, hn⟩ := h_next
  exact ⟨n + 1, evalSymNodeTreeModular_mono (fun _ h => h ▸ hn) _ h_step⟩

/-- Machine state on entry to bb3, once `_5` holds the byte count `r` that bb1
or the `hermetic_copy_stub` call produced. -/
private def bb3Entry (in_range dest_len fo v r : Nat) : MachineState :=
  { frame :=
      { blockIdx := 3, stmtIdx := 0,
        locals :=
          [.uninit, .init (.scalar ⟨in_range, 1⟩), .init (.scalar ⟨dest_len, 8⟩),
           .init (.scalar ⟨fo, 8⟩), .init (.scalar ⟨v, 1⟩), .init (.scalar ⟨r, 8⟩),
           .uninit, .uninit, .uninit, .uninit] }
    memory := emptyMemory }

/-- bb3 checks `dest_len - r` for overflow and bb4 returns `(r, dest_len - r)`
with memory untouched. -/
private theorem bb3_converges (in_range dest_len fo v r : Nat)
    (h_r : r ≤ dest_len) (h_dl : dest_len < 18446744073709551616) :
    MirModularWpConverges
      Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.callContract
      Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
      (bb3Entry in_range dest_len fo v r)
      (mirSafePost fun ret mem' =>
        mem' = emptyMemory ∧
        ret = .aggregate 0 [.scalar ⟨r, 8⟩, .scalar ⟨dest_len - r, 8⟩]) := by
  -- bb3: `_7 = copy _5`
  refine MirModularWpConverges.step ?_
  show MirModularWpConverges _ _ _ _
  -- bb3: `_8 = SubWithOverflow(copy _2, copy _7)`; `r ≤ dest_len` selects the
  -- non-overflow arm of the checked subtraction.
  refine MirModularWpConverges.step ?_
  show (match Nat.ble r dest_len with | true => _ | false => _)
  rw [Nat.ble_eq_true_of_le h_r]
  show MirModularWpConverges _ _ _ _
  -- bb3: `assert(!move (_8.1)) -> bb4`
  refine MirModularWpConverges.step ?_
  show MirModularWpConverges _ _ _ _
  -- bb4: `_6 = move (_8.0); _9 = copy _5; _0 = (move _9, copy _6)`
  refine MirModularWpConverges.step ?_
  show MirModularWpConverges _ _ _ _
  refine MirModularWpConverges.step ?_
  show MirModularWpConverges _ _ _ _
  refine MirModularWpConverges.step ?_
  show MirModularWpConverges _ _ _ _
  -- bb4: `return`
  refine MirModularWpConverges.step ⟨rfl, ?_⟩
  show Value.aggregate 0
    [_, .scalar ⟨wrapScalarBits (dest_len - r) 18446744073709551616, 8⟩] = _
  rw [wrapScalarBits_eq_of_lt (by omega)]

theorem verified : ModularVerificationResult Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed.modularClaim := by
  refine verifyModularContractMir_of_wpConverges _ _ _ _ ?_
  rintro _ _ ⟨in_range, dest_len, fo, v, h_ir, h_fo, h_dl, h_v, rfl, rfl⟩
  rcases h_ir with rfl | rfl
  · -- `source_in_restricted_range = false`: bb0 jumps to bb1
    -- (`_5 = const 0_usize; goto -> bb3`).
    refine MirModularWpConverges.bind (mid := (· = bb3Entry 0 dest_len fo v 0))
      (mirStepsConverges_of_runCfgToBlock _ _ _ rfl 3 _ ⟨rfl, rfl⟩) ?_
    rintro _ rfl
    refine MirModularWpConverges.mono ?_ (bb3_converges 0 dest_len fo v 0 (Nat.zero_le _) h_dl)
    rintro (⟨ret, mem'⟩ | _ | _) h
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, by rintro _ _ _ _ ⟨⟩; rfl⟩
    all_goals trivial
  · -- `source_in_restricted_range = true`: bb0 jumps to bb2.
    refine MirModularWpConverges.bind
      (mirStepsConverges_of_runCfgToBlock _ _ _ rfl 2 _ (And.intro rfl ?_)) (fun _ h => h)
    -- bb2: `_5 = hermetic_copy_stub(copy _2, copy _3, copy _4) -> [return: bb3]`.
    -- The call meets the stub's contract, and every answer the contract admits
    -- returns `fault_offset` with memory untouched.
    refine modularWpConverges_step_to (s' := bb3Entry 1 dest_len fo v fo)
      ⟨⟨rfl, dest_len, fo, v, h_fo, h_dl, h_v, rfl, rfl⟩, ?_⟩
      (MirModularWpConverges.mono ?_ (bb3_converges 1 dest_len fo v fo h_fo h_dl))
    · rintro _ ⟨_, _, rfl, rfl, h_ret⟩
      obtain ⟨rfl, -⟩ := h_ret dest_len fo v rfl
      rfl
    · rintro (⟨ret, mem'⟩ | _ | _) h
      · obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, by rintro _ _ _ _ ⟨⟩; rfl⟩
      all_goals trivial

/-- Model witness for `hermetic_copy_stub` returning `fault_offset`. -/
def hermeticCopyStubModel (args : List Value) (mem : Memory) : Value × Memory :=
  match args with
  | [ _, .scalar { bits := fo, .. }, _ ] =>
    (.scalar { bits := fo, sizeBytes := 8 }, mem)
  | _ => (.scalar { bits := 0, sizeBytes := 8 }, mem)

/-- End-to-end horizontal linking theorem combining the modular proof of
    `usercopy_copyin_bracketed` with the scoped UB-exception proof of
    `hermetic_copy_stub`. -/
theorem linked_with_ub_exception (fallback : ExternalCallHandler) :
    ((fun args mem =>
      (mirHandledTree
        Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
        args mem
        (ubExceptionModelHandler
          Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim
          hermeticCopyStubModel
          fallback)).toPartial) ≤
      MirClosedStatefulContractSpec
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post) ∧
    MirStatefulContractHoldsWithSafety
      Mir.FuchsiaUsercopy.hermetic_copy_stub.body
      (fun args mem =>
        Specs.FuchsiaUsercopy.hermetic_copy_stub.pre args mem ∧
        Specs.FuchsiaUsercopy.hermetic_copy_stub.strictSafetyPre args mem)
      Specs.FuchsiaUsercopy.hermetic_copy_stub.pre
      Specs.FuchsiaUsercopy.hermetic_copy_stub.post := by
  refine linkUbExceptionCallee
    verified
    Proof.FuchsiaUsercopy.hermetic_copy_stub.verified
    hermeticCopyStubModel
    fallback
    ?_
  rintro _ _ ⟨count, fo, v, h_fo, -, -, rfl, rfl⟩ -
  exact ⟨rfl, by rintro _ _ _ ⟨⟩; exact ⟨rfl, h_fo⟩⟩

end Proof.FuchsiaUsercopy.usercopy_copyin_bracketed
