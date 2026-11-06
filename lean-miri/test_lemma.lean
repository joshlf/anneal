import Miri
open Miri.Memory

lemma tryNew_byteSize_eq {Prov Extra} (size : Nat) (align : Align) (mask : InitMaskMaterialized) (meta : Nat → Nat → Option Extra) (alloc : Allocation Prov Extra) :
  Allocation.tryNew size align mask meta = Except.ok alloc → alloc.byteSize = size := by
  intro h
  unfold Allocation.tryNew at h
  split at h
  · injection h with heq; rw [←heq]
  · contradiction

