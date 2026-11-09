import Trusted.Rustc.V2026_06_01.MirSemantics.StateRel
open MirSemantics
theorem test_hsrc (s : MachineState) (srcIdx : Local) (srcPtr srcPtr' : ProvenancePtr)
  (hsrcPtr : get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)))
  (h1 : get? s.frame.locals srcIdx = some (.init (.ptr srcPtr' 8))) :
  srcPtr' = srcPtr := by
  rw [hsrcPtr] at h1
  injection h1 with h1_inner
  injection h1_inner with h1_ptr
  injection h1_ptr with h1_eq
  exact h1_eq.symm
