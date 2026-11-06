import LeanMiriSpec.Correspondence.SimLM1_4
open Miri
open LeanMiriSpec

lemma write_memory_no_validate_impossible {T : Type}
  {s : AnnealState} {m : MachineState} {localId : Nat}
  (h_rel : StateRel s m) (size : Size) (val_sc : Scalar) (prov_none : val_sc.provenance = none)
  {m' : MachineState}
  (h_alloc : Miri.Interpreter.allocateStack localId size 0 = .ok m')
  {m'' : MachineState}
  (h_write : (do
    let basePtr ← .ok (Miri.Memory.Pointer.mk (Miri.Memory.Provenance.none) (Size.mk 0))
    let mplace ← .ok (Miri.Interpreter.MemPlace.mk (Miri.Interpreter.MemPlaceMeta.none) (Miri.Interpreter.MPlace.mk basePtr (Miri.Memory.Align.mk 1) none))
    let sc_val := Miri.Interpreter.Immediate.scalar val_sc
    Miri.Interpreter.writeMemoryNoValidate mplace sc_val m' LeanMiriSpec.Correspondence.annealPlaceHooks) = .ok m'') :
  False := by
  dsimp [bind, Except.bind, pure, Except.pure] at h_write
  unfold Miri.Interpreter.writeMemoryNoValidate at h_write
  dsimp at h_write
  sorry

