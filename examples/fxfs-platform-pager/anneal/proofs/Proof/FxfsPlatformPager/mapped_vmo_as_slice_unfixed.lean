import Trusted
import Anneal.MirLiftCore
import Mir.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
import Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
import Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

namespace Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

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

theorem verified : UbExceptionVerificationResult Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim := by
  refine (fun h => verifyUbExceptionMir_of_wpConverges _ h ?waived) ?strict
  case strict =>
    rintro _ _ ⟨_, _, -, -, rfl, rfl⟩ ⟨_, ⟨⟩⟩
    exact mirWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, rfl, by rintro _ _ ⟨⟩; rfl⟩
  case waived =>
    intro _ _ h_pre
    have h := h _ _ h_pre
    rcases h_pre with ⟨_, _, -, rfl | rfl, rfl, rfl⟩
    · exact .of_mirWpConverges (h ⟨_, rfl⟩)
    · -- When `pager_backed = true`, the second `assume` (`copy _3 == false`)
      -- fails and halts with a waived UB.
      repeat
        first
        | exact ubWaivedWpConverges_of_halt trivial
        | refine MirUbWaivedWpConverges.step ?_

end Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed
