import Trusted
import Anneal
import Mir.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
import Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
import Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

namespace Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

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

/-- With `pager_backed = false`, both `assume`s in bb0 hold, and bb0 returns
`mapped_len` with memory untouched. -/
private theorem not_pager_backed_converges (ml : Nat) :
    MirWpConverges Mir.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.body
      (initMachineStateWithMemory Mir.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.body
        [.scalar ⟨ml, 8⟩, .scalar ⟨1, 1⟩, .scalar ⟨0, 1⟩] emptyMemory)
      (mirSafePost (Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.post
        [.scalar ⟨ml, 8⟩, .scalar ⟨1, 1⟩, .scalar ⟨0, 1⟩] emptyMemory)) := by
  refine MirWpConverges.step ?_
  repeat refine MirExecWpConverges.step ?_
  exact ⟨rfl, by rintro _ _ ⟨⟩; rfl⟩

theorem verified : UbExceptionVerificationResult Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim := by
  refine verifyUbExceptionMir_of_wpConverges _ ?_ ?_
  · -- Strict-safety domain: `pager_backed = false`.
    rintro _ _ ⟨ml, pb, -, -, rfl, rfl⟩ ⟨_, ⟨⟩⟩
    exact not_pager_backed_converges ml
  · rintro _ _ ⟨ml, pb, -, h_pb, rfl, rfl⟩
    rcases h_pb with rfl | rfl
    · exact .of_mirWpConverges (not_pager_backed_converges ml)
    · -- `pager_backed = true`: bb0's second `assume` (`copy _3 == false`)
      -- fails, which raises a waived UB.
      repeat
        first
        | exact ubWaivedWpConverges_of_halt trivial
        | refine MirUbWaivedWpConverges.step ?_

end Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
