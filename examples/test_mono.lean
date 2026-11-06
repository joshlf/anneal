import LeanMiriSpec
open Miri.Interpreter
open LeanMiriSpec
open LeanMiriSpec.Correspondence

theorem MemPlaceRel_mono_live {mach mach' : AnnealMachine} {ty layouts optVal mp}
  (h : MemPlaceRel mach ty layouts optVal mp)
  (hlive : ∀ id alloc, (id, alloc) ∈ mach.memory.live.toList → (id, alloc) ∈ mach'.memory.live.toList)
  (hbase : mach'.lookupBaseAddr = mach.lookupBaseAddr) :
  MemPlaceRel mach' ty layouts optVal mp := by
  cases h with | mk allocId tag baseAddr relOffset localAlloc ptr_prov no_misalign thin_meta live_lookup base_lookup addr_no_overflow ptr_addr_eq mut_alloc aligned_ptr in_bounds uninit_consistent val_consistent scalar_consistent =>
  apply MemPlaceRel.mk allocId tag baseAddr relOffset localAlloc
  · exact ptr_prov
  · exact no_misalign
  · exact thin_meta
  · exact hlive _ _ live_lookup
  · rw [hbase]; exact base_lookup
  · exact addr_no_overflow
  · exact ptr_addr_eq
  · exact mut_alloc
  · exact aligned_ptr
  · exact in_bounds
  · exact uninit_consistent
  · exact val_consistent
  · exact scalar_consistent

