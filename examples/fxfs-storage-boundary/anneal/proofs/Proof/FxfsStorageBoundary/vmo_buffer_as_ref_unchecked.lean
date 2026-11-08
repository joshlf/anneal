import Trusted
import Anneal
import Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
import Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
import Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

namespace Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-- A step from `s` that has no successor state (it returns or raises a waived
UB) converges under the UB-waived semantics with a one-step witness, because
no leaf of its step tree consults the continuation. -/
private theorem ubWaivedWpConverges_of_halt
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : evalSymNodeTreeUbWaived (fun _ => False) post (stepMirSymTree body s)) :
    MirUbWaivedWpConverges body s post :=
  ⟨1, h⟩

/-- With `trusted = true`, bb0's `assume` holds, and bb0 returns
`offset + len` with memory untouched. -/
private theorem trusted_converges (vs off len : Nat)
    (h_off : off ≤ vs) (h_len : len ≤ vs - off) (h_vs : vs < 18446744073709551616) :
    MirWpConverges Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
      (initMachineStateWithMemory Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
        [.scalar ⟨vs, 8⟩, .scalar ⟨off, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨1, 1⟩] emptyMemory)
      (mirSafePost (Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.post
        [.scalar ⟨vs, 8⟩, .scalar ⟨off, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨1, 1⟩]
        emptyMemory)) := by
  refine MirWpConverges.step ?_
  repeat refine MirExecWpConverges.step ?_
  refine ⟨rfl, ?_⟩
  rintro _ _ _ _ ⟨⟩
  -- `offset + len ≤ vmo_size < 2^64`, so the wrapping `Add` does not wrap.
  show Value.scalar ⟨wrapScalarBits (off + len) 18446744073709551616, 8⟩ = _
  rw [wrapScalarBits_eq_of_lt (by omega)]

theorem verified : UbExceptionVerificationResult Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim := by
  refine verifyUbExceptionMir_of_wpConverges _ ?_ ?_
  · -- Strict-safety domain: `trusted = true`.
    rintro _ _ ⟨vs, off, len, t, h_off, h_len, h_vs, -, rfl, rfl⟩ ⟨_, _, _, ⟨⟩⟩
    exact trusted_converges vs off len h_off h_len h_vs
  · rintro _ _ ⟨vs, off, len, t, h_off, h_len, h_vs, h_t, rfl, rfl⟩
    rcases h_t with rfl | rfl
    · -- `trusted = false`: bb0's `assume` (`copy _4 != false`) fails, which
      -- raises a waived UB.
      repeat
        first
        | exact ubWaivedWpConverges_of_halt trivial
        | refine MirUbWaivedWpConverges.step ?_
    · exact .of_mirWpConverges (trusted_converges vs off len h_off h_len h_vs)

end Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
