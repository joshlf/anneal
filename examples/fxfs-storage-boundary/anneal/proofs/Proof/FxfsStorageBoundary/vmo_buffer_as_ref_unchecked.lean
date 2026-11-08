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
open Anneal.FunctionalTranslation
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

private theorem trusted_converges (vs off len : Nat)
    (h_off : off ≤ vs) (h_len : len ≤ vs - off) (h_vs : vs < 18446744073709551616) :
    MirWpConverges Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
      (initMachineStateWithMemory Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
        [.scalar ⟨vs, 8⟩, .scalar ⟨off, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨1, 1⟩] emptyMemory)
      (mirSafePost (Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.post
        [.scalar ⟨vs, 8⟩, .scalar ⟨off, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨1, 1⟩]
        emptyMemory)) :=
  mirWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, rfl, by
    rintro _ _ _ _ ⟨⟩
    change Value.scalar ⟨wrapScalarBits (off + len) 18446744073709551616, 8⟩ = _
    simp [wrapScalarBits, nat_ble_eq_false_of_lt
      (Nat.lt_of_le_of_lt (Nat.add_comm len off ▸ Nat.add_le_of_le_sub h_off h_len) h_vs)]⟩

theorem verified : UbExceptionVerificationResult Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim := by
  refine verifyUbExceptionMir_of_wpConverges _ ?_ ?_
  · rintro _ _ ⟨vs, off, len, _, h_off, h_len, h_vs, -, rfl, rfl⟩ ⟨_, _, _, ⟨⟩⟩
    exact trusted_converges vs off len h_off h_len h_vs
  · rintro _ _ ⟨vs, off, len, _, h_off, h_len, h_vs, rfl | rfl, rfl, rfl⟩
    · -- When `trusted = false`, the `assume` (`copy _4 != false`) fails and
      -- halts with a waived UB.
      repeat
        first
        | exact ubWaivedWpConverges_of_halt trivial
        | refine MirUbWaivedWpConverges.step ?_
    · exact .of_mirWpConverges (trusted_converges vs off len h_off h_len h_vs)

end Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
