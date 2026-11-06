import LeanMiriSpec
open Miri.Interpreter
open LeanMiriSpec
open LeanMiriSpec.Correspondence

theorem MemPlaceRel_mono_live {mach mach' : AnnealMachine} {ty layouts optVal mp}
  (h : MemPlaceRel mach ty layouts optVal mp)
  (hlive : ∀ id alloc, (id, alloc) ∈ mach.memory.live.toList → (id, alloc) ∈ mach'.memory.live.toList)
  (hbase : mach'.lookupBaseAddr = mach.lookupBaseAddr) :
  MemPlaceRel mach' ty layouts optVal mp := by
  cases h with | mk allocId tag baseAddr relOffset localAlloc ptr_prov no_misalign thin_meta live_lookup base_lookup mem_offset val_rel =>
  apply MemPlaceRel.mk allocId tag baseAddr relOffset localAlloc ptr_prov no_misalign thin_meta
  · apply hlive; exact live_lookup
  · rw [hbase]; exact base_lookup
  · exact mem_offset
  · exact val_rel

