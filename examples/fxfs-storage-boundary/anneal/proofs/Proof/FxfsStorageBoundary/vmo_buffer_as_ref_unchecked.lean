import Trusted
import Anneal.MirLiftCore
import Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
import Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
import Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

namespace Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-- Closes a step that halts immediately (such as a violated `assume` raising a
waived UB): `MirUbWaivedWpConverges.step` requires `evalSymNodeTreeExec`, which
rejects `.ub`, whereas `evalSymNodeTreeUbWaived` accepts `.halt .ub` at depth
`1` without consulting the continuation. -/
private theorem ubWaivedWpConverges_of_halt
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : evalSymNodeTreeUbWaived (fun _ => False) post (stepMirSymTree body s)) :
    MirUbWaivedWpConverges body s post :=
  ⟨1, h⟩

theorem verified : UbExceptionVerificationResult Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim := by
  refine (fun h => verifyUbExceptionMir_of_wpConverges _ h ?waived) ?strict
  case strict =>
    rintro _ _ ⟨_, off, len, _, h_off, h_len, h_vs, -, rfl, rfl⟩ ⟨_, _, _, ⟨⟩⟩
    refine mirWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, rfl, ?_⟩
    rintro _ _ _ _ ⟨⟩
    change Value.scalar ⟨wrapScalarBits (off + len) 18446744073709551616, 8⟩ = _
    rw [wrapScalarBits_of_lt
      (Nat.lt_of_le_of_lt (Nat.add_comm len off ▸ Nat.add_le_of_le_sub h_off h_len) h_vs)]
  case waived =>
    intro _ _ h_pre
    have h := h _ _ h_pre
    rcases h_pre with ⟨_, _, _, _, -, -, -, rfl | rfl, rfl, rfl⟩
    · -- When `trusted = false`, the `assume` (`copy _4 != false`) fails and
      -- halts with a waived UB.
      repeat
        first
        | exact ubWaivedWpConverges_of_halt trivial
        | refine MirUbWaivedWpConverges.step ?_
    · exact .of_mirWpConverges (h ⟨_, _, _, rfl⟩)

end Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
