import re

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "r") as f:
    content = f.read()

mono_lemmas = """
theorem MemPlaceRel_mono_live {mach mach' : AnnealMachine} {ty layouts optVal mp}
  (h : MemPlaceRel mach ty layouts optVal mp)
  (hlive : ∀ id alloc, (id, alloc) ∈ mach.memory.live.toList → (id, alloc) ∈ mach'.memory.live.toList)
  (hbase : mach'.lookupBaseAddr = mach.lookupBaseAddr) :
  MemPlaceRel mach' ty layouts optVal mp := by
  cases h with | mk allocId tag baseAddr relOffset localAlloc ptr_prov no_misalign thin_meta live_lookup base_lookup mem_offset val_rel =>
  apply MemPlaceRel.mk allocId tag baseAddr relOffset localAlloc ptr_prov no_misalign thin_meta
  · apply hlive _ _ live_lookup
  · rw [hbase]; exact base_lookup
  · exact mem_offset
  · exact val_rel

theorem LocalRel_mono_live {mach mach' : AnnealMachine} {decl layouts slot mls}
  (h : LocalRel mach decl layouts slot mls)
  (hlive : ∀ id alloc, (id, alloc) ∈ mach.memory.live.toList → (id, alloc) ∈ mach'.memory.live.toList)
  (hbase : mach'.lookupBaseAddr = mach.lookupBaseAddr) :
  LocalRel mach' decl layouts slot mls := by
  cases h
  · apply LocalRel.dead; assumption
  · apply LocalRel.immediate <;> assumption
  · apply LocalRel.indirect
    · assumption
    · assumption
    · apply MemPlaceRel_mono_live <;> assumption

theorem FrameRel_mono_live {body mach mach' af mf}
  (h : FrameRel body mach af mf)
  (hlive : ∀ id alloc, (id, alloc) ∈ mach.memory.live.toList → (id, alloc) ∈ mach'.memory.live.toList)
  (hbase : mach'.lookupBaseAddr = mach.lookupBaseAddr) :
  FrameRel body mach' af mf := by
  cases h with | mk body_eq loc_eq af_len mf_size h_locs =>
  apply FrameRel.mk body_eq loc_eq af_len mf_size
  intro i decl slot mls hi hslot hmls
  apply LocalRel_mono_live (h_locs i decl slot mls hi hslot hmls) hlive hbase

theorem MemoryAllocDisjoint_mono_live {mach mach' : AnnealMachine} {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
  (h : MemoryAllocDisjoint tf) : MemoryAllocDisjoint tf := h

"""

target = "theorem StateRel_allocateStack"
if mono_lemmas not in content:
    content = content.replace(target, mono_lemmas + target)

with open("lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean", "w") as f:
    f.write(content)
