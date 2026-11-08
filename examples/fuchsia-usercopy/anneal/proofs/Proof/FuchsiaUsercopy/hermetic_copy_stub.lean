import Trusted
import Anneal
import Mir.FuchsiaUsercopy.hermetic_copy_stub
import Obligations.FuchsiaUsercopy.hermetic_copy_stub
import Specs.FuchsiaUsercopy.hermetic_copy_stub

namespace Proof.FuchsiaUsercopy.hermetic_copy_stub

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-- A step from `s` that has no successor state (it returns or raises a waived
UB) converges under the UB-waived semantics on its own: the one step consumes
the only unit of the witness, since no leaf of the step tree consults the
continuation. This is the UB-waived analogue of `MirExecWpConverges.halted`;
`MirUbWaivedWpConverges.step` cannot express it because its call-free
evaluator rejects UB nodes. -/
private theorem ubWaivedWpConverges_of_halt
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : evalSymNodeTreeUbWaived (fun _ => False) post (stepMirSymTree body s)) :
    MirUbWaivedWpConverges body s post :=
  ⟨1, h⟩

/-- With `normal_mode_dest_valid = true`, bb0 `switchInt(copy _3)` jumps to bb2
(`_0 = copy _2; return`), returning `fault_offset` with memory untouched. -/
private theorem valid_dest_converges (count fo : Nat) (h_fo : fo ≤ count) :
    MirWpConverges Mir.FuchsiaUsercopy.hermetic_copy_stub.body
      (initMachineStateWithMemory Mir.FuchsiaUsercopy.hermetic_copy_stub.body
        [.scalar ⟨count, 8⟩, .scalar ⟨fo, 8⟩, .scalar ⟨1, 1⟩] emptyMemory)
      (mirSafePost (Specs.FuchsiaUsercopy.hermetic_copy_stub.post
        [.scalar ⟨count, 8⟩, .scalar ⟨fo, 8⟩, .scalar ⟨1, 1⟩] emptyMemory)) :=
  -- The run halts before it re-enters bb0.
  mirWpConverges_of_runCfgToBlock _ _ rfl 0 _
    ⟨rfl, rfl, by rintro _ _ _ ⟨⟩; exact ⟨rfl, h_fo⟩⟩

theorem verified : UbExceptionVerificationResult Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim := by
  refine verifyUbExceptionMir_of_wpConverges _ ?_ ?_
  · -- Strict-safety domain: `normal_mode_dest_valid = true`.
    rintro _ _ ⟨count, fo, v, h_fo, -, -, rfl, rfl⟩ ⟨_, _, ⟨⟩⟩
    exact valid_dest_converges count fo h_fo
  · rintro _ _ ⟨count, fo, v, h_fo, -, h_v, rfl, rfl⟩
    rcases h_v with rfl | rfl
    · -- `normal_mode_dest_valid = false`: bb0 jumps to bb1, whose call to
      -- `core::hint::unreachable_unchecked` raises a waived UB.
      exact MirUbWaivedWpConverges.bind
        (mirStepsConverges_of_runCfgToBlock _ _ _ rfl 1 _ (And.intro rfl trivial))
        (fun _ h => ubWaivedWpConverges_of_halt h)
    · exact .of_mirWpConverges (valid_dest_converges count fo h_fo)

end Proof.FuchsiaUsercopy.hermetic_copy_stub
