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

/-- Machine state on entry to block `bb` after bb0's `StorageLive`s, with `_5`
in slot `s5`. -/
private def entryState (bb in_range dest_len fo v : Nat) (s5 : LocalSlot) :
    MachineState :=
  { frame :=
      { blockIdx := bb, stmtIdx := 0,
        locals :=
          [.uninit, .init (.scalar ⟨in_range, 1⟩), .init (.scalar ⟨dest_len, 8⟩),
           .init (.scalar ⟨fo, 8⟩), .init (.scalar ⟨v, 1⟩), s5,
           .uninit, .uninit, .uninit, .uninit] }
    memory := emptyMemory }

/-- From bb3's entry with a byte count `r ≤ dest_len` in `_5`, bb3 checks
`dest_len - r` for overflow and bb4 returns `(r, dest_len - r)` with memory
untouched; `h_Q` discharges the caller's postcondition for that outcome. -/
private theorem bb3_converges {Q : Value → Memory → Prop}
    {in_range dest_len fo v r : Nat}
    (h_r : r ≤ dest_len) (h_dl : dest_len < 18446744073709551616)
    (h_Q : Q (.aggregate 0 [.scalar ⟨r, 8⟩, .scalar ⟨dest_len - r, 8⟩]) emptyMemory) :
    MirModularWpConverges
      Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.callContract
      Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
      (entryState 3 in_range dest_len fo v (.init (.scalar ⟨r, 8⟩)))
      (mirSafePost Q) := by
  -- bb3: `_7 = copy _5`, then `_8 = SubWithOverflow(copy _2, copy _7)`, whose
  -- overflow test is the first step that does not reduce on its own.
  repeat refine MirModularWpConverges.step ?_
  -- `r ≤ dest_len` selects the non-overflow arm of the checked subtraction.
  show (match Nat.ble r dest_len with | true => _ | false => _)
  rw [Nat.ble_eq_true_of_le h_r]
  -- bb3: `assert(!move (_8.1)) -> bb4`; bb4: `_6 = move (_8.0); _9 = copy _5;
  -- _0 = (move _9, copy _6)`; the final `return` leaves the step tree at `Q`.
  repeat refine MirModularWpConverges.step ?_
  show Q (.aggregate 0
    [_, .scalar ⟨wrapScalarBits (dest_len - r) 18446744073709551616, 8⟩]) _
  rw [wrapScalarBits_eq_of_lt (by omega)]
  exact h_Q

theorem verified : ModularVerificationResult Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed.modularClaim := by
  refine verifyModularContractMir_of_wpConverges _ _ _ _ ?_
  rintro _ _ ⟨in_range, dest_len, fo, v, h_ir, h_fo, h_dl, h_v, rfl, rfl⟩
  rcases h_ir with rfl | rfl
  · -- `source_in_restricted_range = false`: bb0 jumps to bb1
    -- (`_5 = const 0_usize; goto -> bb3`).
    refine MirModularWpConverges.bind
      (mid := (· = entryState 3 0 dest_len fo v (.init (.scalar ⟨0, 8⟩))))
      (mirStepsConverges_of_runCfgToBlock _ _ _ rfl 3 _ ⟨rfl, rfl⟩) ?_
    rintro _ rfl
    exact bb3_converges (Nat.zero_le _) h_dl ⟨rfl, by rintro _ _ _ _ ⟨⟩; rfl⟩
  · -- `source_in_restricted_range = true`: bb0 jumps to bb2.
    refine MirModularWpConverges.bind (mid := (· = entryState 2 1 dest_len fo v .uninit))
      (mirStepsConverges_of_runCfgToBlock _ _ _ rfl 2 _ ⟨rfl, rfl⟩) ?_
    rintro _ rfl
    -- bb2: `_5 = hermetic_copy_stub(copy _2, copy _3, copy _4) -> [return: bb3]`.
    -- The call meets the stub's contract, and every answer the contract admits
    -- returns `fault_offset` with memory untouched.
    refine modularWpConverges_step_to
      (s' := entryState 3 1 dest_len fo v (.init (.scalar ⟨fo, 8⟩)))
      (fun hc => ⟨⟨rfl, dest_len, fo, v, h_fo, h_dl, h_v, rfl, rfl⟩, ?_⟩)
      (bb3_converges h_fo h_dl ⟨rfl, by rintro _ _ _ _ ⟨⟩; rfl⟩)
    rintro _ ⟨_, _, rfl, rfl, h_ret⟩
    obtain ⟨rfl, -⟩ := h_ret dest_len fo v rfl
    exact hc

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
